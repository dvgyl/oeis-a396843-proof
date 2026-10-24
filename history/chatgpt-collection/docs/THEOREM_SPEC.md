# Mathematical specification and formalization boundaries

This file specifies the mathematical statements proved in the accompanying manuscript. It is a specification, not evidence that a Lean implementation has compiled. The final coverage report must identify which declarations were checked by Lean, against which definitions, and with which transitive axioms.

## 1. The canonical series

Let `R` be any commutative ring with identity. A formal power series `U : R[[X]]` is normalized when its constant coefficient is zero and its coefficient of `X` is one. Composition means substitution, with the outer series first. Set

\[
U^{\circ0}=X,\qquad U^{\circ(k+1)}=U\circ U^{\circ k}.
\]

For every natural number `r >= 1`, define

\[
\Phi_r(U)=X+U^{\circ r}U^{\circ(r+1)}.
\]

The existence-and-uniqueness theorem must prove that exactly one normalized series satisfies `U = Phi_r(U)`. The series `F_(R,r)` is that solution. Over the integers write `F_r`, and set

\[
a_r(n)=[X^n]F_r\quad(n\in\mathbb N).
\]

The coefficient at index zero is zero; every parity claim below starts at index one. The equation uses ordinary multiplication between the two composed series.

The canonical construction must be proved to satisfy the equation. A result about an arbitrary series with the desired congruence as a premise, or about an independently defined periodic coefficient function, does not establish the conjectures.

### Structural endpoints

1. **Existence and uniqueness:** the exact arbitrary-ring statement above, without adding field, characteristic-zero, or integral-domain hypotheses.
2. **Coefficient-map compatibility:** a ring homomorphism sends `F_(R,r)` to the canonical solution over the target ring. In particular, reduction modulo `2*r` commutes with the defining construction and with legitimate compositions.
3. **Normalized inverse:** a normalized formal series has a unique normalized inverse under composition, with both inverse identities.

## 2. Central congruence and every iterate

For integers `k`, put

\[
T_k(X)=\frac{X}{1-kX},\qquad H(X)=\frac{X^4}{(1-X)^3}.
\]

All fractions denote formal inverses of series with constant term one. Define the correction coefficient

\[
\epsilon(r,k)=\begin{cases}1,&r\text{ even and }k\text{ odd},\\0,&\text{otherwise}.\end{cases}
\]

For every `r >= 1` and every integer `k`, the manuscript proves

\[
F_r^{\circ k}(X)\equiv T_k(X)+r\epsilon(r,k)H(X)\pmod{2r}.
\]

For negative `k`, `F_r^(circ k)` means iteration of the actual compositional inverse of `F_r`; for `k=0` it is `X`. The current package includes this extension for both parities of `r` in `Consecutive.IntegerIterates`, with the series endpoint `map_ziter_solution_mod` and the coefficient endpoint `integerIterateCoeff_mod`. The natural-iterate theorem alone would not establish the negative cases.

The coefficient version is: degree zero is zero, degree one is one, and for every `n >= 2`,

\[
[X^n]F_r^{\circ k}\equiv k^{n-1}+r\epsilon(r,k)h_n\pmod{2r},
\]

where `h_n = 0` for `n < 4` and `h_n = binom(n-2,2)` for `n >= 4`. This avoids an unexplained `0^0` at `k=0,n=1`.

An acceptable formal endpoint can state equality after mapping to `ZMod (2*r)`, or equivalent divisibility of every integer coefficient difference. It must connect to the actual canonical solution.

The proof uses two exact integer-series identities:

\[
H(X)T_1'(T_1(X))+H(T_1(X))=\frac{2X^4}{(1-2X)^3},
\]

\[
(1-X)H(X)-X^2T_1(X)-X^3T_1'(X)=-\frac{2X^3}{1-X}.
\]

When `r` is even, `r*r=0` in `ZMod (2*r)`, so first-order substitution is valid by the binomial theorem. There is no division by `r`, two, or a factorial inside this ring.

## 3. The four A396099 endpoints

Set `A = F_2` and `a(n) = a_2(n)`.

1. **Odd coefficients:** for every `n >= 1`, `Odd (a(n))`.
2. **Residue cycle:** for every `j >= 0`,
   \[
   a(4j+3)\equiv1,\quad a(4j+4)\equiv3,\quad
   a(4j+5)\equiv3,\quad a(4j+6)\equiv1\pmod4.
   \]
   In addition `a(1)=a(2)=1`. An equivalent complete case split for every `n >= 3` is acceptable.
3. **Second iterate:**
   \[
   A^{\circ2}\equiv X+2X^2\pmod4.
   \]
   This implies the required zero coefficients in every degree `n > 2`.
4. **Cancellation:**
   \[
   A-XA^{\circ3}\equiv X+\frac{2X^3}{1-X}\pmod4.
   \]
   This implies coefficient two in every degree `n > 2`. The initial `X` must be retained in a full-series identity.

The stronger formula `A = T_1 + 2*H (mod 4)` may be used to derive these endpoints, but the four public endpoints should explicitly expose the original assertions.

## 4. A396798 and its phase correction

Set `B = F_4`. The following seven iterate statements are true:

| Iterate | Required statement modulo eight |
| --- | --- |
| `B^(circ 2)` | `X + 2*X^2 + 4*X^3`; hence zero coefficients for `n > 3` |
| `B^(circ 3)` | At `n = 4j+2,4j+3,4j+4,4j+5`, residues `3,1,7,5` |
| `B^(circ 4)` | `X + 4*X^2`; hence zero coefficients for `n > 2` |
| `B^(circ 5)` | At the same four index classes starting at two, residues `5,1,1,5` |
| `B^(circ 6)` | `X + 6*X^2 + 4*X^3`; hence zero coefficients for `n > 3` |
| `B^(circ 7)` | At the same four index classes starting at two, residues `7,1,3,5` |
| `B^(circ 8)` | `X`; hence zero coefficients for `n > 1` |

The coefficient period for `B` is `1,1,5,5` **starting at index two**, namely

\[
a_4(4j+2)\equiv1,\quad a_4(4j+3)\equiv1,\quad
a_4(4j+4)\equiv5,\quad a_4(4j+5)\equiv5\pmod8.
\]

The source entry starts that block at index one. That version is false: `a_4(3)=9`, which has residue one, whereas the stated phase would require residue five. The Lean endpoint `a396798_counterexample` establishes that the actual canonical coefficient has residue one and is not congruent to five. This is sufficient to refute the source phase. The exact integer value nine is derived in the manuscript and checked independently in Python; it is not asserted as the type of that Lean endpoint. A copied numeric literal would not establish a fact about the canonical sequence.

## 5. A396807

Set `C = F_5`.

1. For every `n >= 1`, `[X^n]C = 1 (mod 10)`.
2. For every integer `k`,
   \[
   C^{\circ k}\equiv\frac{X}{1-kX}\pmod{10}.
   \]
   Equivalently, degree one has coefficient one, and for `n >= 2` the coefficient is `k^(n-1)` modulo ten. Include negative `k` and zero as specified above.

## 6. Additional consequences and attribution

The manuscript also proves that the reduction of `F_r` has exact compositional order `2*r`: for every integer `k`,

\[
F_r^{\circ k}\equiv X\pmod{2r}\quad\Longleftrightarrow\quad 2r\mid k.
\]

The `r=3` case recovers Sundaram's September 2026 result for A396797. It is credited as prior work and must not be counted as a newly solved conjecture.

The existing `dvgyl/oeis-a396843-proof` project concerns the distinct equation `A_m(X*A_m-m*X*A_m^2)=X^2`. Its proofs do not by themselves certify any endpoint in this file.

## 7. The scaled inverse family A393856--A393859

This is a distinct second family. For a normalized series `U`, define the coefficientwise operator

\[
L_q(U)=\sum_{n\ge1}q^{n-1}[X^n]U\,X^n.
\]

It equals `U(qX)/q` for a nonzero integer parameter, but the definition uses no division and remains valid over arbitrary commutative rings. Let `G_(R,q)` be the unique normalized solution of

\[
G\bigl(X-X L_q(G)\bigr)=X.
\]

The structural endpoints must prove existence, uniqueness, normalization, the original composition equation, and compatibility with coefficient maps. The coefficients in every arithmetic endpoint must be coefficients of that canonical solution. The corresponding source is `lean/Hanna/Related/ScaledInverse.lean`.

For a natural parameter `q` and `n >= 1`, the uniform congruence is

\[
[X^n]G_{\mathbb Z,q}\equiv1\pmod{q+1}.
\]

The manuscript uses positive parameters. The implementation can validly include `q=0`, where the modulus is one.

The four public sequence endpoints specialize to:

| Entry | Parameter | Modulus | Expected declaration suffix |
| --- | --- | --- | --- |
| A393856 | 4 | 5 | `a393856_mod_five` |
| A393857 | 5 | 6 | `a393857_mod_six` |
| A393858 | 6 | 7 | `a393858_mod_seven` |
| A393859 | 7 | 8 | `a393859_mod_eight` |

For an even integer parameter `q`, the parity theorem is

\[
\operatorname{Odd}([X^n]G_{\mathbb Z,q})
\quad\Longleftrightarrow\quad
\exists j\in\mathbb N,\ n=2^j\qquad(n\in\mathbb N).
\]

The degree-zero coefficient is even, consistently with the right side being false. The public specializations at four and six are `a393856_parity` and `a393858_parity` in `lean/Hanna/Related/ScaledParity.lean`. These two parity results complete the six original assertions in this family. A successful build of the four congruence endpoints does not by itself certify the parity file.

## 8. Evidence required before using the word “formalized”

For every claimed endpoint, record its explicit Lean type, the definitions used in that type, a fresh successful build, and transitive axiom output. Check for `sorryAx`, unsupported custom axioms, and weakened or circular hypotheses. Keep finite computations separate from all-index proofs.

Written proofs in the manuscript, a roadmap in this document, a successful source scan, and old-project build logs are not substitutes for checking the new declarations. A release coverage table should mark any remaining gaps explicitly. Novelty, source status, authorship declarations, and independent human review are outside Lean's certification.
