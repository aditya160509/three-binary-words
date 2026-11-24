# Three binary words that cannot be cyclically equalized

[![lean](https://github.com/aditya160509/three-binary-words/actions/workflows/lean.yml/badge.svg)](https://github.com/aditya160509/three-binary-words/actions/workflows/lean.yml)

**Can three binary words with the same number of 1s always be made into rotations of one another by inserting the same letters at the same positions?** No. The words `0110`, `0101`, `1001` can never be equalized, at any completion length.

This answers, negatively, the three-word question posed by Shinagawa and Nuida ([FCT 2025](https://arxiv.org/abs/2507.04916)) and by Fici at [WORDS 2025](https://words2025.loria.fr/files/2025/07/webpage-open-problems.pdf).

## Contents

- [**Manuscript (PDF)**](classification/manuscript.pdf): the obstruction, the classification of all 20 length-four weight-two triples (exactly four fail, one symmetry class), minimality of length four, criteria at prescribed geometry, and a denominator bound.
- [**Lean 4 proof**](classification/Cyclic.lean): checked by Lean 4.33.0 on every push (badge above). No `sorry`; only `propext`, `Classical.choice`, `Quot.sound`. See [classification/README.md](classification/README.md).
- [**Computational checks**](classification/): Z3 SMT-LIB files for all twenty cases, Python tests, exhaustive search.
- [Original short proof](counterexample.md) and its [verification script](verify.py).

## Reproduce

```sh
cd classification
lean Cyclic.lean                 # Lean 4.33.0
python3 -m unittest -v           # needs z3 on PATH
for f in smt/*.smt2; do echo "$f $(z3 $f)"; done
```

## Authorship and AI disclosure

**Aditya Balaji** identified the problem and confirmed it was still open, designed the research protocol (unbounded impossibility proof, independent cross-checks, Lean formalization), proposed the extension to all twenty length-four triples and conjectured that the four failures form one symmetry class, set the verification requirements, and audited and re-verified the results, including compiling the Lean proof. The original [research prompts](prompts.md) are included.

The written proofs, formalization, code and manuscript text were produced by the AI system **Astra 6.2** under that direction. The results have not yet been peer reviewed, and novelty is not established.
