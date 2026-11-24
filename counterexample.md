# A shortest counterexample to simultaneous cyclic equalizability

**Theorem.** The three binary words $0110,0101,1001$ have length four and weight two. No simultaneous insertion of identical strings into corresponding gaps makes them rotations of a common word. Four is the least possible input length.

## Proof

Suppose a completion exists. Write its three rows as $U,V,W$ and its length as $N$. In the cyclic group of positions $G=\mathbb Z/N\mathbb Z$, let $T_c f(x)=f(x-c)$. Regard each row as an integer-valued function on $G$. There are $a,b\in G$ such that $V=T_aU$ and $W=T_bU$. The original columns distinguish all three rows, so $0,a,b$ are pairwise distinct, even if the completed words have a shorter period.

Write $0\le p<q<r<s<N$ for the four original positions, using their representatives in the completed linear word. Let $e_t$ be one at $t$ and zero elsewhere. At every inserted position the three row values agree. Subtracting the bits in the four original columns gives

| Position | $p$ | $q$ | $r$ | $s$ |
|---|---:|---:|---:|---:|
| $U$ | 0 | 1 | 1 | 0 |
| $V$ | 0 | 1 | 0 | 1 |
| $W$ | 1 | 0 | 0 | 1 |
| $V-U$ | 0 | 0 | −1 | 1 |
| $W-V$ | 1 | −1 | 0 | 0 |

Put $D=V-U=e_s-e_r$ and $F=W-V=e_p-e_q$. Since $D=(T_a-I)U$ and $F=(T_b-T_a)U$, commutativity of translations gives

$$
(T_b-T_a)D=(T_a-I)F.
$$

Use $T_c e_t=e_{t+c}$, expand, and collect the positive terms on opposite sides. Equality of integer-valued functions is precisely the following equality of **multisets**, including multiplicities, in $G$.

$$
\{p,\ q+a,\ r+a,\ s+b\}
=
\{p+a,\ q,\ r+b,\ s+a\}.
$$

The occurrence of $q+a$ on the left cannot match $p+a$ or $s+a$, since $q$ differs from both $p$ and $s$. It cannot match $q$, since $a\ne0$. Hence $q+a=r+b$. Cancel one occurrence on each side.

The occurrence of $r+a$ now has only $p+a,q,s+a$ available. The first and third are excluded because $r\ne p,s$, so $r+a=q$. Cancel this pair as well. Of the remaining right-hand entries $p+a,s+a$, only $s+a$ can match $p$. Thus $p=s+a$.

It follows that $r-q\equiv s-p\pmod N$. Yet
$$
0<r-q<s-p<N,
$$
since $s-p=(q-p)+(r-q)+(s-r)$. This contradiction proves the assertion for every finite $N$. Cancelling occurrences is legitimate even if some of the four entries on one side coincide.

For minimality, at lengths at most three every binary weight class is a single rotation orbit. Indeed the constant cases are immediate, and every other word has either a unique one or a unique zero. Thus every equal-weight triple of shorter words already works with empty insertions. ∎

## Consequences and scope

Each pair of the counterexample is cyclically equalizable by the binary two-word theorem. The obstruction uses both shifts acting on one completed word. Adding any common columns anywhere in the displayed triple gives further negative instances, since a successful completion would also complete the original four columns. In particular the counterexamples have unbounded input length.

The convention for rotations is immaterial because all shifts are allowed. The original positions can lie anywhere in the linear representative, including after a nonempty prefix and before a nonempty suffix. Their cyclic spacing is otherwise unrestricted. No assumption on the inserted symbols beyond agreement across the three rows enters the subtraction argument.

## Reproduction and cross-checks

Run the following commands with Python 3 and the Z3 executable on PATH.

```sh
python3 verify.py
python3 verify.py 1001 1010 0101
```

For three distinct rows, the SMT test constructs the signed identity
$T_b(V-U)-T_a(W-U)+(W-V)=0$ directly from the supplied bits. It divides all positions and shifts by $N$, fixes the first position at zero by translation, and lets the coordinates range over the real unit circle. Since both summands of a translated position lie in $[0,1)$, one conditional subtraction implements wraparound. A Boolean perfect matching enforces multiplicities. Any finite witness supplies a model of this relaxation. Z3 5.1.0 returned `unsat` for the counterexample and `sat` for the control. A satisfiable relaxation alone need not give a completion.

A second test enumerates every possible completed first word through length ten and every pair of rotations. A subsequence dynamic program accepts precisely when every column is consumed either as the next original column or as a common insertion. It found no witness for the counterexample and returned $01001,01010,00101$ for the control (prepend zero to each row). Only the unbounded argument establishes impossibility.

## Literature and priority

Shinagawa and Nuida proved the binary two-word theorem, asked the unrestricted three-word question, and gave a counterexample when insertions are restricted to zeros. Gabriele Fici also posed the three-word question at WORDS 2025. [FCT paper](https://arxiv.org/abs/2507.04916) · [WORDS problem collection, final slide](https://words2025.loria.fr/files/2025/07/webpage-open-problems.pdf)

Thongjarast, Pasiphol and Ruangwises characterized the two-word problem over every finite alphabet. Thongjarast separately proved the two-binary-word result with zero-only insertions. The literature search through November 24, 2026 located no earlier unrestricted three-word counterexample. The derivation here was independent. Bibliographic priority and peer review remain unverified. [Parikh-vector characterization](https://arxiv.org/abs/2604.19504) · [Zero-only insertion theorem](https://arxiv.org/abs/2607.18452)

**Formal verification status.** Z3 checked the real-linear relaxation. No Lean declarations were kernel-checked. There is no Lean axiom or placeholder audit for this result.
