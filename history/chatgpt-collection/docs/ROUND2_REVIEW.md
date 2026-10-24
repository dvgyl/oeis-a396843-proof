# Round 2 semantic review and endpoint coverage

Prepared for Dev Goyal on 24 October 2026.

## Review scope and independence

This is an AI-assisted semantic review of `More.InverseIterate`,
`More.PowerPeriodicity`, `More.TailPeriodicity`, `More.Contracts`, and the fixed
validation manifest. The reviewing AI agent did not implement the three mathematical
modules or the initial contracts; it added five contract examples in response to
this review. It did implement the Stirling-transform portion and its numerical
checker, so the present manifest review is not an independent replication of that
entire development. The agents shared the same project and mathematical context.
No independent human review is asserted.

The separate [A396093 review](RATIONAL_PARITY_REVIEW.md) records the source and
definition audit of `More.RationalParity`. The cubic modules receive their own
review; this document checks their manifest presence and contract statements, not
the details of their construction proof.

**Result:** no unresolved mismatch in the reviewed mathematical definitions,
index ranges, modulus assumptions, inverse identities, or period meanings was
found. The boundaries and coverage qualifications below are part of that result.

## A396102: literal equation and sequence identification

The [OEIS A396102 entry](https://oeis.org/A396102), read on 24 October 2026, has
offset one. Its generating function starts with `x`, satisfies

\[
 A(A(A(x)))=(1+x)A(A(x)),
\]

and the conjecture is `a(n) == 1 mod 3` for every `n>=1`.

The formal sequence is `InverseIterate.A396102 = F 3` over the integers. The file
proves normalization, the displayed source equation, and uniqueness among
normalized solutions. Thus the endpoint does not assume that a separately
constructed sequence happens to be the OEIS sequence. The coefficient theorem
uses the exact range `1 <= n`. It does not incorrectly include the zero constant
coefficient in the congruence.

Normalization is material. The raw functional equation also admits the zero
series, while the source's series has zero constant term and linear coefficient
one. The existence and uniqueness declarations, and the corresponding contracts,
retain precisely those normalization conditions.

### Construction and equivalence

For a natural parameter `r`, the code first constructs a normalized series `R`
satisfying

\[
 R=x-R\,R^{\circ r}.
\]

The triangular existence argument is proved, not assumed. Inspection of the
inherited `Triangular`, `triangularCoeffs`, and inverse infrastructure shows that
the construction uses integer ring operations and coefficient recursion. Choosing
the resulting unique series uses ordinary classical choice after existence has
been established; it does not introduce a mathematical axiom asserting a solution.

The series `F` is its genuine compositional inverse, with both `R(F(x))=x` and
`F(R(x))=x` proved. For each positive parameter, the literal family equation is
then derived:

\[
 F^{\circ r}=(1+x)F^{\circ(r-1)}.
\]

Lean expresses the positive parameter as `r+1`, so the theorem type uses natural
indices without a truncated subtraction. The converse is also proved: the inverse
of any normalized solution of this original equation satisfies the auxiliary
fixed-point equation. Auxiliary uniqueness therefore yields uniqueness for the
original equation. This closes the possible gap between a convenient recursive
construction and the source definition.

### Modular conclusion and boundary cases

The coefficient reduction is transported through the actual integer construction
using `map_F`. Over `ZMod r`, the auxiliary solution is the formal series
`x/(1+x)`, whose inverse is `x/(1-x)`. This proves the entire positive-index
coefficient congruence. The modulus is not assumed prime, and the proof never
cancels a possibly nonunit coefficient in a composite residue ring.

The stronger iterate result has every natural iterate index `k`, including zero:

\[
 [x^n]F^{\circ k}\equiv k^{n-1}\pmod r\qquad(n\ge1).
\]

When `k=0`, the iterate is `x`; the right side is one at `n=1` under the standard
power convention and zero for `n>1`. This matches the identity iterate exactly.

The formal modular theorem also permits `r=0`, because Lean's `ZMod 0` is the
integer ring. In that extra case it asserts an exact equality for the auxiliary
parameter-zero construction. The usual modular-family interpretation should be
advertised for positive `r`. For `r=1`, reduction is into the one-element ring,
so the congruence is valid and uninformative. These cases cause no gap in the
parameter-three OEIS statement.

## Scalar-power periodicity

`More.PowerPeriodicity` has the explicit assumptions `0 < m` and `m <= n`, with
an arbitrary natural base. The zero-base case is handled separately; positivity
of `n` follows from those hypotheses, so no accidental `0^0` assertion occurs.

For nonzero bases the proof reduces divisibility to prime-power divisors of the
modulus. If the prime divides the base, both powers vanish at the stated onset.
If it does not, coprimality and Euler's theorem apply at that prime power, and
totient divisibility gives the requested exponent. The proof includes modulus
one and all composite moduli. It assumes neither that the base is a unit modulo
the whole modulus nor that the modulus is prime.

The onset `n>=m` is a sufficient uniform bound. No claim that it is optimal is
contained in the theorem. Its natural-number congruence and `ZMod` equality
versions are connected by the standard cast-congruence equivalence.

## What the exact period theorem means

`More.TailPeriodicity.shift` maps a sequence `f` to `n |-> f(n+1)`.
`iterate_shift` proves that its `k`th iterate is the shift by `k`. Therefore the
periodic-point definition used by Mathlib is exactly the ordinary statement
`f(n+p)=f(n)` for all natural `n`; it is not a period of one sampled residue or a
finite prefix.

`leastPeriod_spec` assumes a positive period and proves four facts: positivity of
the least period, divisibility into the given period, its own universal period
property, and comparison with every positive period. For the Stirling application,
`f(n)` is explicitly the residue of the coefficient with index `m+n`. Thus the
formal object is the least positive period of the whole tail beginning at `m`.
The definition is not applied directly to a sequence that might still contain a
transient prefix.

This is sufficient for the OEIS eventual-period conclusion. It does not identify
the smallest possible onset. The generic shift lemma does not silently assume a
finite codomain; it is valid for any codomain once a positive period is supplied.

## Typed contracts

`More.Contracts` restates the unbounded conclusions with their intended domains,
normalizations, defining equations, and residue conditions. In particular:

- A396093's exact third composition and both source parity clauses are explicit.
- The selected cubic statements include their original defining equations,
  normalizations, uniqueness, and the claimed coefficient ranges.
- The Stirling contracts specify the recursive numbers, the finite integer-weighted
  transform, every positive modulus, the onset `n>=m`, and all four least-tail-period
  properties.
- The inverse-iterate contracts include both inverse identities, positive-parameter
  original-equation existence and uniqueness, A396102's exact equation, and all
  positive coefficient indices.

The actual square-partition definition and Pell weight initial values were also
inspected and match the source formulas. This review prompted five additional
contract examples: the full square-partition filter, both Pell initial values,
and the two literal cubic existence-and-uniqueness statements. The strengthened
`More.Contracts` module compiled successfully with no warnings. These were
strengthenings of the review gate; no existing mathematical definition or theorem
statement needed correction.

`More.lean` imports `More.Contracts`, and the top-level `ContractChecks.lean`
also imports it. Consequently the complete project build and the separately
compiled contract file both reach the new contracts.

## Fixed manifest coverage

The reviewed `validation/final_theorems.json` contains **130** explicit endpoints:

| Group | Endpoint count |
|---|---:|
| Previous release, retained in original order | 67 |
| A396093 parity and source-identity endpoints | 8 |
| Cubic construction and selected A389474/A389475 claims | 19 |
| Known Stirling periodicity theorem, arithmetic helpers, and seven applications | 21 |
| A396102 and the inverse-iterate family | 15 |

A read-only check confirmed that the flattened group lists equal the required
endpoint list and that this list exactly matches `FINAL_NAMES` fixed in the
validator. The prior-release check confirms all 67 earlier endpoints, 30 previous
Lean sources, and byte-for-byte preservation of the earlier ZIP. The old contract
content is retained while new contracts are imported.

The advertised new theorem types reviewed here are covered. In particular, the
manifest includes all seven Stirling period results **and** all seven least-period
divisibility results, the generic least-period theorem, the literal A396102
definition and uniqueness result, and the stronger arbitrary-iterate congruence.
Intermediate helpers used by these declarations are included transitively in the
axiom audit. Not every intermediate lemma needs a separate endpoint entry.

This coverage does not mean that every conjecture appearing anywhere on every
referenced OEIS page is proved. The cubic group advertises selected clauses; the
Stirling group addresses periodicity. Any separate integrality, sign, continued
fraction, or other clause needs its own result before being claimed solved.

## Evidence and historical limits

The source correspondence above is a semantic review, distinct from a successful
Lean build and its transitive axiom audit. The validator separately checks the
pinned toolchain, dependency revision, full theorem types, contracts, and allowed
axiom dependencies. Finite numerical checks provide additional indexing and
formula corroboration, not substitutes for the universal proofs.

Publication priority remains unresolved for the newly investigated source clauses.
Current conjecture wording and a search that finds no earlier proof cannot prove
that a result was globally open. For the Stirling block, an earlier general proof
was positively identified: Danesh's Theorem 4.1 is stronger than the totient-bound
formalization here. Those seven specializations are known-result formalizations
and contribute zero newly solved open problems. See
[the Stirling source and attribution document](STIRLING_PERIODICITY.md).
