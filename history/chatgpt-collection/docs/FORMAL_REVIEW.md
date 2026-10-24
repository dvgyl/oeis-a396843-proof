# AI semantic review of the formalization

**Review date:** 24 October 2026.  
**Scope:** the two new series families, their advertised OEIS consequences, the inherited series infrastructure on which they depend, and the independent finite coefficient program.

**Finding:** no mathematical mismatch, circular construction, vacuous target hypothesis, reversed composition, or omitted negative-iterate case was found in the reviewed definitions and theorem statements. The four A396099 assertions, the general signed formula and exact order, the seven valid A396798 iterate assertions and its phase correction, both A396807 assertions, and all six scaled-family assertions refer to solutions of the original equations.

This is an AI development review. The reviewing agent prepared the manuscript and Python verifier, shared the mathematical development context, and read the Lean implementations without editing them. It is therefore not an independent human review or an independent replication of the entire project. Independent human review remains pending. Compilation and axiom-dependency evidence are recorded separately in the final validation artifacts; this document explains the correspondence between the formal types and the mathematical claims.

## 1. What was inspected

The review read the complete new modules `Consecutive.Basic`, `Construction`, `Modular`, `Arithmetic`, `Coefficients`, `Acceptance`, `Related`, and `IntegerIterates`, and `Hanna.Related.ScaledInverse` and `ScaledParity`. It also read the inherited `Hanna.Series.Basic`, `Filtration`, `Triangular`, `Construction`, and `Inverse` modules that provide substitution, coefficient agreement, triangular recursion, and inverse construction. The new explicit examples in `lean/ContractChecks.lean` were checked against the advertised theorem types, including their unbounded quantifiers and definition expansions.

These were compared with `manuscript/compositional_congruences.tex`, `docs/THEOREM_SPEC.md`, and the original OEIS equations and index ranges. The relevant official pages were reopened during the final review: [A396099](https://oeis.org/A396099), [A396798](https://oeis.org/A396798), [A396807](https://oeis.org/A396807), [A393856](https://oeis.org/A393856), [A393857](https://oeis.org/A393857), [A393858](https://oeis.org/A393858), and [A393859](https://oeis.org/A393859). The prior-work status of [A396797](https://oeis.org/A396797) was also checked. The source-status claim is bounded to these pages on the review date.

The reviewed source-file hashes are recorded in `reproducibility/semantic_review_sources.json`. That manifest identifies the inspected snapshot; it is not itself proof of compilation or correctness. The final package manifest and validation records determine the released snapshot.

## 2. Actual formal series and composition

`Hanna.Series.Normalized A` means exactly

```lean
PowerSeries.coeff R 0 A = 0 ∧ PowerSeries.coeff R 1 A = 1
```

`Hanna.Series.compose outer inner` is Mathlib's formal multivariate substitution specialized to one variable. The outer argument comes first. It is not a custom operation that merely mimics the desired coefficient pattern. The coefficient theorem expresses substitution as the finite sum

\[
[X^n](A\circ B)=\sum_{j=0}^{n}[X^j]A\,[X^n]B^j
\]

when the constant coefficient of `B` is zero. Every use needed for the advertised results has the appropriate zero-constant or normalization proof. The associative and coefficient-map lemmas retain those conditions. No analytic convergence assumption is introduced.

The consecutive-iterate definition is

```lean
iter F 0 = X
iter F (n + 1) = compose F (iter F n)
step r F = X + iter F r * iter F (r + 1)
```

Thus `step 2 F` is exactly `X + compose F F * compose F (compose F F)`. The middle operation is multiplication of two composed series. The OEIS pages explicitly use iteration in their superscripts, so the formal reading matches the source.

`geom c` has coefficient `c^n`, `mobius c = X * geom c`, and `correction = X^4 * geom 1^3`. The identity `(1-C c*X)*geom c=1` is proved. Consequently the displayed rational notation means the actual formal series `X/(1-cX)` and `X^4/(1-X)^3`. No division by a possibly noninvertible ring element is hidden in these definitions.

## 3. Canonical construction and nonvacuity

`Consecutive.solution r` is selected from a proved existence-and-uniqueness result over every commutative ring. It is not defined to be the rational comparison candidate. The proof first establishes that `step r` improves agreement of normalized series by one coefficient. It then uses the inherited well-founded triangular coefficient recursion to construct an exact solution.

The inherited `triangularCoeffs` is a recursion on the natural index. Its specification is proved from the triangular property; the latter is established for the new equation using the coefficient filtration. Uniqueness is a separate strong induction on coefficient indices. Using `Classical.choose` after this existence proof does not assume the existence theorem or a target congruence.

The public equations and map bridge are substantive:

```lean
solution_normalized r
solution_equation r
map_solution f r
```

They prove normalization, `solution r = step r (solution r)`, and compatibility with any coefficient-ring homomorphism. The arithmetic sequences `a r n`, `iterateCoeff r k n`, and `integerIterateCoeff r k n` are coefficients of the canonical **integer** series and its actual iterates. They are not separate modular sequences.

Existence over the integers shows that the normalized-equation hypotheses used in the acceptance theorem are satisfiable. Generic lemmas sometimes assume properties of a comparison parameter, such as `c*c=0` and `2*c=0`; the applications prove those properties in the relevant residue ring. No endpoint assumes the residue formula it concludes.

## 4. The four A396099 claims

The endpoint `Consecutive.a396099_all_four` takes an arbitrary normalized integer series and the literal original equation as its only mathematical premises:

```lean
{F : PowerSeries ℤ}
(hF : Normalized F)
(hEq : F = X + compose F F * compose F (compose F F))
```

It concludes the conjunction of all four universal assertions. Its proof identifies `F` with the canonical solution by uniqueness, then applies the individual endpoints. This is a useful additional safeguard against proving theorems about the wrong named sequence.

| Source assertion | Public endpoint | Boundary and semantic check |
| --- | --- | --- |
| Every term is odd | `a396099_odd` | Quantifies over every natural `n` with `0<n`; the zero coefficient is correctly excluded. |
| Repeating residues `1,3,3,1` | `a396099_residue`, `a396099_period` | Starts at `n=3`; the four-index statement uses `4j+3` through `4j+6` for every `j`. |
| Second-iterate tail vanishes modulo four | `a396099_second_iterate`, `a396099_second_iterate_series` | Uses actual `iter F 2`; the full series is `X+2X^2`, and the source range is `n>2`. |
| Cancellation tail is two modulo four | `a396099_difference`, `a396099_difference_series` | Uses `F-X*iter F 3`, with `n>2`; the full-series statement retains the initial `X`. |

`cast_a` and `cast_iterateCoeff` explicitly connect the integer coefficients to the canonical series over `ZMod`. The cancellation proof has its own explicit map-of-series identity. Consequently a theorem about a solution constructed directly in a residue ring is not being silently substituted for a theorem about the integer sequence.

The periodic arithmetic is proved for all indices by induction and a binomial-coefficient identity. The small `decide` and `norm_num` calls settle fixed arithmetic facts and base cases; they do not stand in for testing an unbounded claim over a finite range.

## 5. General natural and signed iterates

`iter_solution_mod` proves the complete formula for all natural `r,k`. `map_iter_solution_mod` applies it to the actual integer series after coefficient reduction. Written with the manuscript's notation, it is

\[
F_r^{\circ k}=T_k+
\begin{cases}rH,&r\text{ even and }k\text{ odd},\\0,&\text{otherwise},\end{cases}
\quad\text{in }(\mathbb Z/(2r)\mathbb Z)[[X]].
\]

The odd-parameter proof verifies the comparison series in the defining equation. For even parameters the proof establishes `r*r=0` and `2*r=0` in the coefficient ring, proves the candidate's composition square and fixed-point identity, and invokes uniqueness. The weighted-composition argument justifies retaining `H(X)` in odd iterates. It does not replace `H(T_k)` with `H(X)` without a reason.

The manuscript uses a square-zero substitution calculation involving formal derivatives. The Lean proof instead supplies exact ring-identity certificates and inverse identities. This proves the same target statements; it does not claim to formalize each intermediate derivative lemma verbatim.

The signed definition `ziter F hF k` uses `iter F n` when `k` is nonnegative and `iter (inverse F hF) (n+1)` when `k = -(n+1)`. The inherited inverse is constructed by a triangular recursion and has both composition identities. `ziter_negative_is_inverse` proves that repeated inverse composition really inverts repeated forward composition. `map_ziter` uses the proved fact that coefficient reduction commutes with the actual inverse.

For every `r>0` and every integer `k`, the full signed formula appears in `ziter_solution_mod` and `map_ziter_solution_mod`; `integerIterateCoeff_mod` gives its coefficient form. In the even case, the proof identifies the inverse with the natural iterate `2*r-1`, then applies the natural formula and verifies both the cast and parity of the exponent. Negative iterates are not defined by the desired modular formula, nor are they merely an unproved extrapolation from the positive cases.

`iter_solution_mod_eq_X_iff` and `ziter_solution_mod_eq_X_iff` prove that the identity occurs exactly when the exponent is divisible by `2*r`. Necessity uses the coefficient of `X^2`, which is the exponent modulo `2*r`; the correction starts only in degree four. Sufficiency observes that a multiple of `2*r` is even and has zero residue. This establishes exact order, not merely a period dividing `2*r`.

Boundary checks:

- The mathematical finite-order statement uses `r>0`. The natural Lean theorem additionally allows `r=0`, where `ZMod 0` is the integer ring and zero divides the exponent only when the exponent is zero. That extension is not advertised as finite order zero.
- At `k=0`, the iterate is `X` and the correction is absent.
- At coefficient indices zero and one, normalization gives zero and one. The signed coefficient endpoint starts at `n>=1`; Lean's `k^0=1` handles `k=0,n=1`. The exposition states that linear coefficient separately.
- The correction coefficient has the explicit guard `4<=n`, so natural subtraction cannot create a spurious low-degree term.

## 6. A396798 and A396807

The A396798 equation is the case `r=4`. `a396798_iterate_residue` is an all-index coefficient formula from which the seven named iterate endpoints follow. The even-iterate tails use the correct cutoffs: degrees above three for iterates two and six, above two for iterate four, and above one for iterate eight. The three odd-iterate period statements begin at degree two and quantify over every four-term block.

The first period in the source is false when started at degree one. `a396798_corrected_period` proves the corrected start at degree two. `a396798_counterexample` proves that the **canonical** third coefficient has residue one modulo eight and is not congruent to five; `a396798_literal_period_false` explicitly negates the corresponding universal residue assertion.

There is a deliberate precision distinction: the named Lean counterexample proves the residue, not the exact integer equality `a_4(3)=9`. The manuscript derives the exact value from the defining equation, and the independent integer recursion reproduces it. The formally proved residue alone is sufficient to refute the source phase. Neither the manuscript nor the release should describe the false phase as a proved conjecture.

For A396807, `a396807_residue` covers all positive coefficient indices. `a396807_integer_iterate_congruence` quantifies over **all integers** `k` and all positive `n`, matching the source's negative-iterate requirement. The natural-only endpoint is retained as a separate consequence. The already-proved `r=3` instance A396797 is attributed to Sundaram and is not counted as a new resolution.

## 7. Scaled inverse family and the apparent division

The formal operator is

```lean
scaleTail q A = PowerSeries.mk (fun n => q^(n-1) * coeff R n A)
argument q A = X - X * scaleTail q A
SourceEquation q A = (compose A (argument q A) = X)
```

For a normalized series and positive integer `q`, the coefficient in degree `n>=1` of `scaleTail q A` is exactly the coefficient of `A(qX)/q`. At index zero, natural subtraction makes the exponent zero, but the coefficient of `A` is zero; hence the constant coefficient is still zero. This matches the manuscript's `L_q` on every series used here. No assertion about a series with arbitrary nonzero constant coefficient is needed.

The division-free equation therefore matches the source equation. Reduction to `q=-1` modulo `q+1` is legitimate even when the modulus is composite. The implementation never divides by `q`, and it proves the equation over an arbitrary commutative ring.

The construction uses a reversed equation `core q A = X`. This is not an unproved replacement of the original. `compose_argument` identifies `core` with `(argument q A) composed with A`, and `source_iff_core` proves both directions using the normalized two-sided inverse theorem. Existence, uniqueness, and `scaledSolution_equation` then establish the original source equation for the chosen canonical solution. `map_scaledSolution` connects that solution over the integers with its reduction.

`integer_mod_parameter_add_one` proves the uniform congruence for every natural parameter and every positive index. The four specializations use parameters four, five, six, and seven, with moduli five, six, seven, and eight respectively. The generic statement includes `q=0` modulo one; the manuscript's positive-parameter cases are nontrivial and are directly covered.

For even parameters, `scaledSolution_zero_quadratic` proves the equation `G-G^2=X` over `ZMod 2` after reduction. The square-coefficient identity is an all-degree Frobenius result. A strong induction distinguishes zero, one, odd indices greater than one, and even indices reduced to `n/2`. Thus `integer_coeff_odd_iff` proves the equivalence with `∃j, n=2^j` for every natural index. The named parity endpoints at four and six correctly include index one and exclude index zero. Together with the four congruence endpoints, these cover all six listed assertions.

## 8. Independent finite computation

The Python verifier was inspected for circular construction. `generate_r` computes each next integer coefficient directly from the original product of iterates. Because both factors have zero constant term, the degree-`n` product coefficient uses only indices below `n`. Computing iterates only through degree `n-1` at that stage is sufficient.

`generate_q` computes the residual of the original forward equation with the next coefficient temporarily zero. That coefficient first enters the inner argument in degree `n+1` and enters the outer series in degree `n` with multiplier one, so negating the residual determines it. The constructor does not use the reversed quadratic congruence, the geometric comparison series, or the claimed parity support.

The residue formulas appear only after construction, in the comparison checks. Arithmetic uses Python arbitrary-precision integers. Horner substitution has the correct outer/inner order, with an asymmetric unit test distinguishing the two orders. The verifier also checks exact defining equations, the reverse inverse identity for the scaled family, and eight source-prefix values for each of eight mapped entries.

The recorded run in `reproducibility/coefficients_40.json` passed **6,416 individual coefficient checks** through degree 40 for `r=1,...,8` and `q=1,...,8`. The current verifier hash matches the hash in that report. For each `r`, natural iterate indices zero through `2*r+2` are checked. The seven verifier unit tests passed during development. `docs/FINITE_VERIFICATION.md` gives the commands and the exact finite scope.

These computations are independent of the modular candidates as a method of constructing coefficients. They are not independent human verification, a formal proof of the Python program, an all-index proof, or a numerical test of negative iterates. The main and signed Lean theorems supply the all-index conclusions.

## 9. Trust boundary and remaining review

A source scan of the first-party Lean files found no `sorry`, `admit`, custom `axiom` declaration, `unsafe`, `implemented_by`, or `native_decide` use. This check is useful but is not a replacement for the final transitive axiom audit or a successful build. The release's `validation/final_theorems.json` names the required endpoints, and the explicit contract checks and audit output establish the formal evidence for those declarations.

The retained `Hanna.Acceptance` results are regression checks for the earlier A396843 project. This review does not treat their presence as proof of the new families, nor does it claim a new independent semantic audit of every old number-theoretic theorem. The relevant inherited series infrastructure was inspected because the new constructions use it.

No unresolved mathematical or specification defect was found in the new advertised endpoints. The limits remain explicit: Lean checks formal statements against its foundations and the pinned library; it does not verify historical priority, bibliographic accuracy, authorship, or whether the source pages will later be edited. The manuscript's proofs and the AI review should still receive independent human scrutiny before an author-approved public release.
