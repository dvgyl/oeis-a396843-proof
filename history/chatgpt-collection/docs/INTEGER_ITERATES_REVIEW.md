# Review of integer iterates and the scaled inverse family

## Scope and reviewer status

This is an adversarial self-review by the AI agent that implemented the signed-iterate module and the scaled inverse modules. It is **not independent human review**, and it is not independent of those implementations. The separate `FORMAL_REVIEW.md` records the broader review. Lean's kernel checks and this semantic review serve different purposes: the former checks proof terms against their types; the latter checks that the types describe the intended mathematical objects and ranges.

The primary files examined were:

- `lean/Consecutive/IntegerIterates.lean`;
- `lean/Hanna/Related/ScaledInverse.lean`;
- `lean/Hanna/Related/ScaledParity.lean`;
- the shared composition, inverse, construction, modular-formula and coefficient modules on which they depend;
- `docs/THEOREM_SPEC.md`, the related-conjecture ledger and the corresponding manuscript sections.

No mathematical defect was found in the reviewed definitions or theorem statements. The qualifications below specify what the formal results actually establish and what they leave outside their scope.

## 1. The underlying series are constructed from the source equations

### Consecutive-iterate family

`Consecutive.iter F 0` is the identity series `X`. The successor definition is `compose F (iter F n)`, with the outer series first. `Consecutive.step r F` is exactly

\[
X+F^{\circ r}F^{\circ(r+1)},
\]

where juxtaposition between the two iterates is ordinary multiplication of formal series.

`Consecutive.solution` is chosen from a proved existence-and-uniqueness theorem for the normalized fixed point of this operation. Normalization means constant coefficient zero and linear coefficient one. The modular representatives are subsequently identified with the reduction of that solution by uniqueness. Thus the arithmetic statements do not assume the requested residue formula, and they are not statements about an unrelated periodic sequence.

The shared substitution operation is Mathlib formal power-series substitution. Its auxiliary identities are applied with zero-constant-coefficient hypotheses, which are provided by normalization. The use of arbitrary commutative rings includes the composite residue rings needed here; no field or integral-domain assumption has been inserted.

### Scaled inverse family

`scaleTail q A` has coefficient

\[
[X^n]\operatorname{scaleTail}(q,A)=q^{n-1}[X^n]A.
\]

Lean uses natural subtraction in the exponent. At degree zero, this gives the constant coefficient of `A`; every source solution is normalized, so that coefficient is zero. For positive indices the exponent is exactly the intended one. Consequently, for a normalized integer series and nonzero integer `q`, this is the coefficientwise meaning of `A(qX)/q`. No division by a nonunit is performed in a residue ring.

`SourceEquation q A` is the exact equation

\[
A\bigl(X-X\operatorname{scaleTail}(q,A)\bigr)=X.
\]

The auxiliary expression `core q A = A - A * compose (scaleTail q A) A` is used to expose a triangular recursion. It is not substituted for the source equation without justification. `source_iff_core` proves their equivalence by the two-sided compositional inverse theorem, using the proved normalization of both the series and the inner argument. Existence, uniqueness, the original source equation and coefficient-map compatibility are all proved before the congruence endpoints.

## 2. Negative exponents are actual compositional inverses

`Consecutive.ziter F hF` is defined by the sign of its integer exponent:

\[
F^{\circ n}=\operatorname{iter}(F,n),\qquad
F^{\circ(-n)}=\operatorname{iter}(F^{-1},n)
\]

for natural `n`. The inverse used here is `Hanna.Series.inverse`, chosen from a proved existence-and-uniqueness theorem that includes both composition identities. Negative iterates are therefore defined over the integers before coefficient reduction, rather than being defined to equal a desired modular formula.

The following semantic links were checked:

- `ziter_nat` agrees with the existing natural-iterate definition.
- `ziter_neg_nat` includes the case `n=0`; both sides are `X`.
- `iter_inverse_right`, `iter_inverse_left` and `ziter_negative_is_inverse` prove both inverse identities for repeated compositions.
- `map_ziter` proves that coefficient maps commute with integer iterates. Its negative branch uses the already proved `map_inverse`, rather than assuming that modular inversion agrees with integer inversion.

The normalization proof is a proposition parameter. Equal series with different proofs of normalization have the same iterate; `ziter_congr` makes this explicit. Proof irrelevance is used only for proof parameters, not to identify unequal series.

## 3. The full signed formula is proved for both parameter parities

For every natural `r>0` and every integer `k`, `ziter_solution_mod` proves

\[
F_r^{\circ k}(X)
=\frac{X}{1-kX}
+\begin{cases}
r\,X^4/(1-X)^3,&r\text{ even and }k\text{ odd},\\
0,&\text{otherwise}
\end{cases}
\]

as an equality of actual formal series over `ZMod (2*r)`. `map_ziter_solution_mod` applies precisely that identity to coefficient reduction of the canonical integer series and its actual integer iterates.

For negative exponents the proof uses the established natural period `2*r`:

\[
F_r^{-1}=F_r^{\circ(2r-1)},\qquad
F_r^{\circ(-m)}=F_r^{\circ((2r-1)m)}.
\]

The inverse identity is proved from the compositional inverse theorem and the period, not inferred from coefficient samples. The requirement `r>0` ensures that `2*r-1` is the predecessor of a positive period. Its cast is `-1` in `ZMod (2*r)`, and it is an odd natural number. These two facts give both the signed Möbius parameter and the correct parity of the correction term. The odd-parameter subfamily also has a separate direct proof using the inverse of the Möbius series.

`integerIterateCoeff_mod` gives the coefficient form for every positive index. It explicitly sets the correction to zero below degree four and uses `choose (n-2) 2` only in the guarded range. In degree one, Lean uses the usual algebraic convention `k^0=1`, including `k=0`; this matches the separately stated linear coefficient in the manuscript. Degree zero is zero by normalization.

`a396807_integer_iterate_congruence` specializes to `r=5`, every `k : ℤ` and every `n≥1`. It therefore includes negative exponents, zero and positive exponents, not just the natural-iterate subset.

## 4. Exact composition order is not merely an upper bound

`ziter_solution_mod_eq_X_iff` proves, for every `r>0` and integer `k`,

\[
F_r^{\circ k}=X\quad\Longleftrightarrow\quad (2r)\mid k.
\]

The forward direction reads the coefficient of degree two in the full signed formula. The correction begins at degree four, so that coefficient is exactly the residue of `k`; equality with `X` forces divisibility by `2*r`. The reverse direction uses that a multiple of `2*r` is even, so the correction term vanishes, and the Möbius parameter is zero. This proves the exact signed order and excludes smaller positive periods.

## 5. All six scaled-family assertions are covered

The universal congruence `integer_mod_parameter_add_one` states that every positive-index coefficient of the canonical integer series is one modulo `q+1`. It is proved for natural `q`, including the harmless modulus-one case `q=0`; the four OEIS applications have positive parameters.

The public residue endpoints are:

| Entry | Parameter | Endpoint |
| --- | --- | --- |
| A393856 | 4 | `a393856_mod_five` |
| A393857 | 5 | `a393857_mod_six` |
| A393858 | 6 | `a393858_mod_seven` |
| A393859 | 7 | `a393859_mod_eight` |

The parity file is a separate compiled dependency. It proves an all-index coefficient identity for squaring formal series over `ZMod 2` by reducing each coefficient to a finite polynomial truncation and applying polynomial Frobenius. The ensuing strong induction derives the power-of-two support of the solution of `A-A^2=X`. It does not infer the support from a finite computation or assume a previously desired parity sequence.

`a393856_parity` and `a393858_parity` state exactly that the integer coefficient is odd if and only if its index is a power of two. They include degree zero correctly: the coefficient is zero, and zero is not a power of two. These two endpoints complete the six source assertions in this family.

## 6. A396798 phase correction and numerical precision

The related-family module proves the corrected period starting at index two. Its formal counterexample establishes

\[
a_4(3)\equiv1\pmod8,\qquad a_4(3)\not\equiv5\pmod8
\]

from the canonical solution and the general theorem. This is a sufficient formal disproof of the literal starting-at-one phase, and it does not depend on copying a displayed sequence term into a definition.

At the time of this review, that endpoint is a residue statement, not a declaration asserting the exact integer equality `a_4(3)=9`. The exact value nine appears in the written low-degree calculation and the separate coefficient computation. These two descriptions should not be conflated in a coverage table.

## 7. Build and axiom evidence examined

The module targets `Hanna.Related` and `Consecutive.IntegerIterates` compiled successfully with Lean 4.19.0 against the package's pinned Mathlib dependency. The completed module builds emitted no warnings from the newly implemented modules. The release-wide fresh build and complete contract checks are recorded separately by the release workflow.

The following transitive dependency inspections were run with `#print axioms`:

- `ziter_negative_is_inverse`, `map_ziter`;
- `ziter_solution_mod`, `map_ziter_solution_mod`;
- `integerIterateCoeff_mod`, `ziter_solution_mod_eq_X_iff`;
- `a396807_integer_iterate_congruence`;
- scaled-family `existence_uniqueness`, `source_iff_core`;
- `integer_mod_parameter_add_one` and all six scaled-family sequence endpoints.

Every inspected declaration depended only on `propext`, `Classical.choice` and `Quot.sound`, the standard Lean foundations used here. No `sorryAx`, custom conjecture axiom or native evaluation axiom appeared. A source scan of the implemented modules also found no `axiom`, `sorry`, `admit` or `native_decide` commands. This source scan is supplementary evidence; the transitive dependency output is the relevant check on the actual proof terms.

## Remaining boundaries

The formal results establish the stated universal mathematical claims for the declared formal series. They do not establish global novelty, priority, completeness of a literature search, acceptance by OEIS, journal suitability or independent human validation. The correspondence of sequence identifiers and source wording remains a source-review task. The separate source ledger and manuscript provide that provenance, and an external human review remains desirable before making publication or priority claims.
