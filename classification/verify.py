"""Unbounded necessary condition for simultaneous rotations. Requires Z3 CLI."""

from itertools import combinations, product
from argparse import ArgumentParser
import subprocess


def validate(rows):
    if len(rows) != 3 or len(set(rows)) != 3:
        raise ValueError("three distinct rows required")
    if len(set(map(len, rows))) != 1 or not all(
        row and set(row) <= set("01") for row in rows
    ):
        raise ValueError("nonempty binary rows of equal length required")
    if len({row.count("1") for row in rows}) != 1:
        raise ValueError("equal Hamming weights required")


def formula(rows):
    validate(rows)
    n = len(rows[0])
    lines = ["(set-logic QF_LRA)"]

    def declare(x):
        lines.extend(
            [f"(declare-const {x} Real)", f"(assert (and (<= 0 {x}) (< {x} 1)))"]
        )

    for x in ["a", "b"] + [f"p{i}" for i in range(n)]:
        declare(x)
    lines.append("(assert (= p0 0))")
    for i in range(1, n):
        lines.append(f"(assert (< p{i - 1} p{i}))")
    signs = [[], []]
    for i, bits in enumerate(zip(*rows)):
        u, v, w = map(int, bits)
        for shift, coeff in [("b", v - u), ("a", u - w), ("0", w - v)]:
            if coeff:
                point = f"(+ p{i} {shift})"
                signs[int(coeff > 0)].append(
                    f"(ite (< {point} 1) {point} (- {point} 1))"
                )
    # Within each fixed shift and sign the positions are distinct.
    # Equality of multisets via a Boolean permutation matrix.
    m = len(signs[0])
    for i, j in product(range(m), repeat=2):
        lines.extend(
            [
                f"(declare-const e{i}_{j} Bool)",
                f"(assert (=> e{i}_{j} (= {signs[0][i]} {signs[1][j]})))",
            ]
        )
    for i in range(m):
        for group in [[f"e{i}_{j}" for j in range(m)], [f"e{j}_{i}" for j in range(m)]]:
            lines.append("(assert (or " + " ".join(group) + "))")
            for x, y in combinations(group, 2):
                lines.append(f"(assert (or (not {x}) (not {y})))")
    # Distinct rows require distinct rotations.
    lines.append("(assert (distinct a b 0))")
    return "\n".join(lines + ["(check-sat)"])


def solve(rows, timeout=30):
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    try:
        run = subprocess.run(
            ["z3", "-in"],
            input=formula(rows),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=True,
        )
    except subprocess.TimeoutExpired:
        return "timeout"
    answer = run.stdout.strip()
    if answer not in {"sat", "unsat", "unknown"}:
        raise RuntimeError("Unexpected Z3 output: " + answer)
    return answer


def direct_search(rows, limit):
    """Enumerate completed first words and both rotations, independently of SMT."""
    for length in range(len(rows[0]), limit + 1):
        for bits in product("01", repeat=length):
            word = "".join(bits)
            rotations = [word[k:] + word[:k] for k in range(length)]
            for second, third in product(rotations, repeat=2):
                # DP consumes either one original column or a common insertion.
                indices = {0}
                for column in zip(word, second, third):
                    consumed = {
                        i + 1
                        for i in indices
                        if i < len(rows[0]) and column == tuple(row[i] for row in rows)
                    }
                    if len(set(column)) == 1:
                        consumed.update(indices)
                    indices = consumed
                    if not indices:
                        break
                if len(rows[0]) in indices:
                    return word, second, third
    return None


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("rows", nargs="*", default=["0110", "0101", "1001"])
    parser.add_argument("--limit", type=int, default=10)
    from pathlib import Path

    parser.add_argument("--export", type=Path, help="write standalone SMT-LIB")
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    rows = args.rows
    try:
        validate(rows)
        if args.timeout <= 0:
            raise ValueError("timeout must be positive")
    except ValueError as err:
        parser.error(str(err))
    if args.export:
        args.export.write_text(formula(rows) + "\n")
    answer = solve(rows, args.timeout)
    print("Unbounded necessary condition:", answer)
    if answer in {"unknown", "timeout"}:
        print("Solver inconclusive.")
    print(
        "Direct witness through length",
        args.limit,
        ":",
        direct_search(rows, args.limit),
    )
