# Classification of the shortest counterexamples

Start with the [research manuscript](manuscript.pdf). The [LaTeX source](manuscript.tex) includes the proofs, the bibliography, and the contribution disclosure.

Exactly four of the twenty distinct length-four, weight-two triples fail. They consist of a row with alternating bits and two rows whose ones occupy opposite edges of a four-cycle. Among the successes, the minimum completed length is four for four triples, five for four, and six for eight. Section 3 studies arbitrary lengths and shows when signed differences reconstruct a binary word for prescribed offsets and original positions.

## Formal proof

[Cyclic.lean](Cyclic.lean) requires Lean 4.33.0 and its standard library. The [verification log](lean-check.txt) includes a kernel replay of the compiled module. To repeat from this directory:

```sh
lean --version
lean -o Cyclic.olean Cyclic.lean
LEAN_PATH=. leanchecker -v Cyclic
```

The four audited theorems are:

- `Cyclic.noCompletion` proves the signed obstruction for all finite lengths, including cyclic choices of origin.
- `Cyclic.classify` proves the unrestricted positive/negative classification for all twenty sorted distinct weight-two triples. Positive cases carry explicit completions, and the four exclusions quantify over all common binary fillers.
- `Cyclic.components` proves existence of a Boolean labeling exactly when no connected component has conflicting prescriptions.
- `Cyclic.primitiveScan` proves the equivalence between a prefix-sum range of width at most one and periodic binary reconstruction from two commuting differences in generator coordinates.

No `sorry`, project axioms, native decision oracle, or external solver enters the Lean proofs. The kernel reports `propext`, `Classical.choice`, and `Quot.sound`. The manuscript identifies the paper-only arguments, including the arbitrary-orbit integration theorem, the denominator bound, the symmetry reductions, and the sharp lower bounds for the positive cases.

## Computational reproduction

Python 3 and a Z3 executable on PATH are required. From this directory:

```sh
python3 -m unittest -v
python3 verify.py --limit 12 --timeout 30
python3 verify.py 1001 1010 0101 --export control.smt2
z3 smt/0101_0110_1001.smt2
```

The [SMT directory](smt/) contains all twenty standalone formulas. UNSAT excludes every finite completion. SAT accepts the translation identity. The direct enumerator checks completed words. The tests check the twenty classifications, minimum positive lengths, solver status handling, and all signed column assignments at every fixed pair of offsets through completed length four.

## Research status

A November 23 preprint uses a closely related mod-two elimination for a four-row obstruction. See Lemma 2, equations (5) and (6). The signed three-row argument and the twenty-case classification were not found in the searched literature. External expert review and absolute priority remain unverified. [Nuida, Shinagawa and Numata](https://eprint.iacr.org/2026/2960)
