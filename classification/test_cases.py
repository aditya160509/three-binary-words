"""Replay the 20 cases independently of the symmetry argument."""

from itertools import combinations, product
from pathlib import Path
import unittest
from unittest.mock import patch
import subprocess
from verify import direct_search, formula, solve, validate

WORDS = ["".join(w) for w in product("01", repeat=4) if w.count("1") == 2]
BAD = {
    ("0011", "0101", "1100"),
    ("0011", "1010", "1100"),
    ("0101", "0110", "1001"),
    ("0110", "1001", "1010"),
}


def embeds(rows, out):
    n = len(out[0])
    for kept in combinations(range(n), len(rows[0])):
        if all("".join(w[i] for i in kept) == v for v, w in zip(rows, out)) and all(
            len({w[i] for w in out}) == 1 for i in set(range(n)) - set(kept)
        ):
            return True
    return False


class Cases(unittest.TestCase):
    def test_classification(self):
        lengths = []
        for rows in combinations(WORDS, 3):
            with self.subTest(rows=rows):
                self.assertEqual(solve(rows), "unsat" if rows in BAD else "sat")
                out = direct_search(rows, 6)
                if rows in BAD:
                    self.assertIsNone(out)
                else:
                    self.assertIsNotNone(out)
                    lengths.append(len(out[0]))
                    self.assertTrue(embeds(rows, out))
                    self.assertTrue(
                        all(w in out[0] * 2 and len(w) == len(out[0]) for w in out)
                    )
                path = Path(__file__).parent / "smt" / ("_".join(rows) + ".smt2")
                self.assertEqual(path.read_text(), formula(rows) + "\n")

        self.assertEqual(sorted(lengths), [4] * 4 + [5] * 4 + [6] * 8)

    def test_input_and_inconclusive_results(self):
        with self.assertRaises(ValueError):
            validate(("00", "01", "10"))
        rows = next(combinations(WORDS, 3))
        with patch(
            "verify.subprocess.run", side_effect=subprocess.TimeoutExpired("z3", 1)
        ):
            self.assertEqual(solve(rows), "timeout")
        with patch(
            "verify.subprocess.run",
            return_value=subprocess.CompletedProcess([], 0, "unknown\n", ""),
        ):
            self.assertEqual(solve(rows), "unknown")


if __name__ == "__main__":
    unittest.main()
