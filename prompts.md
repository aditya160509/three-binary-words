# Research prompts given to Astra 6.2 (Aditya Balaji, 24 November 2026)

## 1. Initial research prompt

You are acting as a research mathematician specializing in combinatorics on words, finite automata, and computational mathematics.

Investigate the following open problem, posed at WORDS 2025 and still listed as open in the October 19, 2026 revision of arXiv:2604.19504.

**Problem.** Let u, v, w be three binary strings of equal length with the same number of 1s. Can we always insert exactly the same strings at exactly the same positions in all three original strings so that the resulting three strings are cyclic rotations of one another?

Formally, determine whether, for every triple u, v, w ∈ {0,1}ⁿ with equal Hamming weight, there exist insertion strings s₀, ..., sₙ ∈ {0,1}* such that U = s₀u₁s₁…uₙsₙ, V = s₀v₁s₁…vₙsₙ, W = s₀w₁s₁…wₙsₙ are all cyclic rotations of a common word.

**References.** WORDS 2025 open problems; arXiv:2604.19504; Shinagawa and Nuida, FCT 2025 (arXiv:2507.04916).

**Instructions.**
1. Read the references and check subsequent literature for any existing solution.
2. Derive necessary conditions and useful invariants. Carefully separate pairwise cyclic equalizability from simultaneous cyclic equalizability.
3. Explore constructive proofs and search for counterexamples using independent methods, including exhaustive enumeration, SAT/SMT, and combinatorial reasoning.
4. If you find a counterexample, prove that no insertion strings of any finite length can work. Failure to find insertions below a finite bound is insufficient unless that bound is proved complete.
5. If you claim a universal positive result, provide the complete construction and prove termination and correctness for arbitrary n.
6. If the universal problem remains unresolved, seek a nontrivial infinite family of positive instances, a proved sufficient condition, or a finite-case classification with a rigorous completeness bound.
7. Independently audit every significant lemma, every quantifier, and every claimed reduction.
8. Where feasible, create a Lean 4 formalization of the actual theorem statement and proof. Report exactly which declarations were checked and whether there are any `sorry` terms or additional axioms.
9. Compare any result against the literature. Distinguish an original theorem from a known result or computational observation.

Do not assume the conjecture is true. Do not claim a breakthrough merely because a proof looks convincing. Deliverables: a research-style write-up, reproducible verification code, a complete proof or explicit unresolved gap, and a bibliographic novelty assessment. Prioritize correctness over producing a positive result.

## 2. Follow-up research prompt

**Preliminary computational results.** A cross-check using Z3 4.13.3 and bounded exhaustive search reported: 0110, 0101, 1001 — UNSAT, no witness through length 10; 1001, 1010, 0101 — SAT, valid witness found. The Z3 formulation relaxes integer positions into real-valued coordinates on a unit circle; unsatisfiability of this relaxation rules out insertions of any finite length.

**Preliminary classification.** Of the 20 unordered triples of distinct length-four weight-two words, four were impossible — {0011, 0101, 1100}, {0011, 1010, 1100}, {0101, 0110, 1001}, {0110, 1001, 1010} — and sixteen had explicit completions of length at most six. The four impossible triples appear related by common cyclic shifts, bit complementation and row permutations.

**Extended objectives.**
1. Independently reproduce the computational results.
2. Extend the original result into a complete classification of minimal counterexamples.
3. Prove the relevant symmetry reductions.
4. Investigate whether the translation identity yields a general characterization of simultaneous cyclic equalizability.
5. Seek the strongest possible new structural theorem beyond the original counterexample.
6. Formalize the established results in Lean 4.
7. Investigate bibliographic novelty.

**Verification requirements.** Validate equal Hamming weights; add regression tests for all twenty triples; export SMT-LIB formulas; handle solver timeouts and `unknown` explicitly; distinguish bounded searches from unbounded impossibility proofs.

**Deliverables.** A publication-quality manuscript with rigorous proofs, reproducible verification, Lean 4 formalization and a novelty assessment. Disclose AI involvement accurately, and clearly identify unresolved questions, unverified claims and formalization limits. Prioritize correctness over unsupported generalizations.
