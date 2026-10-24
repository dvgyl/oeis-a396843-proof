# Related conjectures and source status

Primary sources were checked on 24 October 2026. “Listed as conjectural” below describes the retrieved entry, not a proof that no earlier solution exists elsewhere. Exact-identifier searches did not locate earlier proofs for A396099, A396798 or A396807. This limited search does not establish priority.

## Family and results

Let `F_r` be the normalized solution of

\[
F_r=X+F_r^{\circ r}F_r^{\circ(r+1)}.
\]

| Parameter | Primary source | Result in this package | Source status when checked |
| --- | --- | --- | --- |
| `r=2` | [A396099](https://oeis.org/A396099) | All four recorded congruence assertions follow from `F_2 = X/(1-X) + 2*X^4/(1-X)^3 (mod 4)` | All four labelled conjectures; no proof linked in the entry |
| `r=3` | [A396797](https://oeis.org/A396797) | Recovered by the general theorem | Already credited to Sundaram (September 2026); prior work |
| `r=4` | [A396798](https://oeis.org/A396798) | Seven iterate assertions proved; the coefficient period is corrected to begin at index two | Eight assertions labelled conjectures; the first has an incorrect starting phase |
| `r=5` | [A396807](https://oeis.org/A396807) | Constant residue one modulo ten and the formula for every integer iterate | Both labelled conjectures; no proof linked in the entry |

The general theorem treats every positive integer `r`, but this document does not claim a one-to-one mapping to further OEIS entries without checking their definitions.

## A396099: exact correspondence

With `A=F_2`, the proved series identities are

\[
A\equiv\frac{X}{1-X}+\frac{2X^4}{(1-X)^3},\qquad
A^{\circ2}\equiv X+2X^2,\qquad
A-XA^{\circ3}\equiv X+\frac{2X^3}{1-X}\pmod4.
\]

They give odd positive-index coefficients, the residue block `1,3,3,1` starting at index three, vanishing second-iterate coefficients above degree two, and residue two for the final expression above degree two. The first two original coefficients equal one.

## A396798: the phase matters

The source assigns the coefficient block `1,1,5,5` to indices starting at one. Its own third term is nine, which contradicts that phase. The correct start is **index two**:

| Index | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Coefficient modulo eight | 1 | 1 | 1 | 5 | 5 | 1 | 1 | 5 | 5 |

This correction follows from the full formula `F_4 = X/(1-X) + 4*X^4/(1-X)^3 (mod 8)`. It is not an additional assumption fitted to the displayed data.

The seven iterate claims agree with the following consequences of the general theorem. All odd-iterate blocks in this table start at degree two.

| Iterate | Proved reduction modulo eight |
| --- | --- |
| 2 | `X + 2*X^2 + 4*X^3` |
| 3 | Coefficient block `3,1,7,5` |
| 4 | `X + 4*X^2` |
| 5 | Coefficient block `5,1,1,5` |
| 6 | `X + 6*X^2 + 4*X^3` |
| 7 | Coefficient block `7,1,3,5` |
| 8 | `X` |

## A396807: integer iterates

For `r=5`, the general formula is

\[
F_5^{\circ k}\equiv\frac{X}{1-kX}\pmod{10}\qquad(k\in\mathbb Z).
\]

Negative iterates mean compositions of the inverse series. Thus the statement covers the full integer range in the source. The case `k=1` supplies residue one for every positive-index coefficient. The package proves the signed cases in `Consecutive.IntegerIterates`, including the endpoint `a396807_integer_iterate_congruence`; its definition uses the actual inverse, and coefficient reduction is proved to commute with it.

## Prior work

Shiva Priyan Shanmuga Sundaram, [*A Proof of the Congruence Conjectures for OEIS A396797*](https://oeis.org/A396797/a396797.pdf), September 2026, proves the `r=3` formula, including integer iterates. Its method compares the solution with `X/(1-X)` and uses uniqueness. The odd-parameter argument here extends that calculation; the correction for even parameters is the extra step used for A396099 and A396798.

Paul D. Hanna receives credit for recording the sequence equations and conjectures. The mathematical note does not claim that the definition of the family, the `r=3` theorem, or the general method of comparison modulo an integer is new.

The earlier [A396843 repository](https://github.com/dvgyl/oeis-a396843-proof) studies a different defining equation and is not evidence of formal verification of this new family. Its author metadata supplies the name Dev Goyal. The new work does not inherit the earlier repository's declaration of completed human verification.

## A second family: A393856--A393859

The normalized solution of

\[
G_q\left(X-\frac{XG_q(qX)}q\right)=X
\]

has every positive-index coefficient congruent to one modulo `q+1`. The quotient is defined coefficientwise, so the proof does not divide by a nonunit in a residue ring. For even `q`, the odd coefficients occur exactly at power-of-two indices.

| Parameter | Official source | Assertions supplied by the manuscript |
| --- | --- | --- |
| 4 | [A393856](https://oeis.org/A393856) | Residue one modulo five; odd exactly at powers of two |
| 5 | [A393857](https://oeis.org/A393857) | Residue one modulo six |
| 6 | [A393858](https://oeis.org/A393858) | Residue one modulo seven; odd exactly at powers of two |
| 7 | [A393859](https://oeis.org/A393859) | Residue one modulo eight |

All four official pages, attributed to Paul D. Hanna on 11 March 2026, were read on 24 October 2026 and still labelled these six assertions as conjectures. This is a statement about the retrieved pages, not a priority claim. The manuscript includes the arbitrary-ring uniqueness proof and both modular arguments; the formal coverage of each endpoint must be assessed separately from the written proof.

## Release wording

Safe description before independent priority review: “Proofs of four assertions currently listed as conjectures for A396099, related results for A396798 and A396807, six assertions for A393856--A393859, and congruence theorems for the two families.”

Do not describe this as a major longstanding open problem, count the already-proved A396797 case as new, claim global priority from the search alone, or claim that Lean certifies the historical or authorship statements. Formal coverage must be reported from the new package's own build evidence.
