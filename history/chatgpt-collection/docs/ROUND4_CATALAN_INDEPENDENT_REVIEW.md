# Independent AI semantic review: Catalan composition and nested binomial series

Reviewed on 24 October 2026 by a separate ChatGPT agent from the agent that
implemented these proofs, for Dev Goyal. This is an AI review; independent
human review remains pending.

**Result: no semantic discrepancy found in the reviewed scope.** The two
Catalan-sequence conjectures and the elementary odd-index observation are
stated with the source's exact index ranges. The modulo-eight argument uses
an exact integer decomposition before reducing coefficients. No change to
the implementation was requested by this review.

## Official source comparison

The reviewer independently retrieved the official entries on 2026-10-24:

| Entry | Source equation used | Source index restriction | Formal conclusion |
|---|---|---|---|
| [A393172](https://oeis.org/A393172) | `F(x−x²)=x+F(x)²`, `F=x+O(x²)` | `n>1` | Residue two modulo four exactly at powers of two, residue zero otherwise. |
| [A393171](https://oeis.org/A393171) | Named definition `G=x+G(C)²`, with `C=x+C²`; equivalent source Formula (1) is `G(x−x²)=x−x²+G(x)²` | `n>2`, powers `2^k` with `k≥1` | Residue four modulo eight exactly at `2^k` or `2^k+1`, residue zero otherwise. |
| [A392210](https://oeis.org/A392210) | Source Formula (1), `H=x+H(x/(1−x))²` | `a(2n−1)` for `n>1` | Every stated odd-index coefficient is even. |

The respective raw OFFSET fields are `1,2`, `1,3`, and `1,3`; all three
displayed sequences begin at index one. The auxiliary constant terms in
Lean are zero. The Catalan function begins with `x`, so it is the shifted
Catalan series defined by the source's own equation, not a constant-one
Catalan generating function.

A393172 and A393171 explicitly label the target assertions as conjectures.
A392210 describes its observation with “It appears”. Its proof is an
elementary consequence of squaring in characteristic two, and the files
correctly identify this limited mathematical contribution.

## Construction and source identification

`Round4/SquareComposition.lean` constructs the normalized solution of
`F=T+(F∘P)²` for normalized `P,T` over any commutative ring. The construction
uses triangular coefficient recursion. Squaring the normalized composition
improves coefficient agreement by one, giving uniqueness. Existence is
proved before any source coefficient conjecture is used.

For the two Catalan sequences, `N=x−x²` and the constructed Catalan series
`C` are proved to be genuine two-sided compositional inverses. The source
equations are transported by these inverse substitutions in both
directions. The first sequence `F` is therefore the actual normalized
solution of `F(N)=x+F²`.

The second sequence is defined as `G=x+F²`. Its source equation,
normalization, uniqueness, and the named equation `G=x+G(C)²` are all
proved. The additional identity `G(C)=F` correctly relates the two source
entries. No unsupported identification of the two different sequences is
used.

For A392210, the inner `geometric` series has the explicit identity
`geometric*(1−x)=x`, so it denotes the source's `x/(1−x)` formal quotient.
The module uses the source's stated finite functional equation. It does
not claim a separate analytic interpretation of an infinite nested
expression.

## Modulo-four argument

The candidate `2C−x` is normalized and satisfies the first source equation
over `ZMod 4`. Uniqueness identifies it with `F`. For `n>1`, its coefficient
is `2C_n`, so the standard binary support of `C mod2` gives exactly the
powers of two. Both exceptional and complementary residue clauses are
formalized, as is divisibility by four for the complementary indices.

## Modulo-eight lift

This is the point requiring care. The proof does not square an arbitrary
representative of a congruence without justification. It first proves the
coefficientwise integral identity

\[
 F=2C-x+4K
\]

for its explicitly defined `remainderQuarter`. Every numerator defining
`K` is proved divisible by four using the complete modulo-four equality.
Exact integer division is then used to obtain the identity.

The integral relation gives

\[
 G=x+F^2\equiv x+(2C-x)^2
   =x+x^2+4(C-x-xC)\pmod8,
\]

where the last step uses `C²=C−x`. Terms involving `K` are multiples of
eight. The map to `ZMod 8` is applied only after this justified integral
decomposition. There is no cancellation of a nonunit in `ZMod 8`.

For `n>2`, the residue is four times `C_n−C_{n−1}` modulo two. The proof
explicitly excludes simultaneous power-of-two indices `n` and `n−1` in
this range. The excluded small adjacent powers are exactly why the range
condition matters. It then proves the equivalence with
`∃k≥1, n=2^k or n=2^k+1`. At `n=3`, the shifted case with `k=1` is correctly
included; `n=2` remains outside the theorem. Both source clauses and the
complementary divisibility-by-eight statement are established.

## A392210 observation

Reduction of its literal source equation modulo two makes the nontrivial
part a square. A square over characteristic two has no odd-degree
coefficients. The remaining `x` term only contributes at index one;
`n>1` guarantees that the target index `2n−1` is at least three. This proves
exactly the source observation and does not classify the even indices.

## Acceptance contracts and numerical checks

`Round4/CatalanContracts.lean` independently restates both source equations,
normalizations, existence and uniqueness, and exact residue ranges. It
also has theorems applying the conclusions to arbitrary normalized
integer series satisfying the stated source equations. Those contracts
eliminate reliance on an unexplained canonical-series name.

The reviewer inspected `scripts/verify_catalan_composition.py` and its
generated numerical report. The two Catalan sequences are generated by
signed source-equation recurrences and independently by the positive
nested-square recurrences. The script checks their agreement through
degree 520, the square relation between the sequences, all 24 displayed
terms for each of the three entries, the complete stated modular patterns,
and literal polynomial compositions through degree 80. The latter checks
use generic polynomial multiplication separately from the binomial
coefficient formulas. These are finite corroboration checks, not the basis
of the infinite claims.

The reviewed proof sources contain no `sorry`, `admit`, custom `axiom`,
`unsafe`, or `native_decide` declaration. Package-wide fresh Lean
compilation and transitive axiom auditing remain the authoritative
mechanical verification gates; this review addresses mathematical meaning
and source correspondence.

## Review limits

No assertion of historical priority or global openness follows from this
review. It does not establish all other formulas in the three entries or
analytic convergence/asymptotic statements. The named source conclusions
above are the complete reviewed mathematical scope.

## Reviewed file hashes

The SHA-256 list below identifies the exact files read for this review.

- `lean/Round4/SquareComposition.lean`: `94af591b99ba599888ef8800d31b196390657e3336bba51f85a3fd2982fe2b0a`
- `lean/Round4/CatalanComposition.lean`: `1c3e724f94ee7d46c9a5573634ad1dd950819bf52a3945eacfccfb24abc1f2f4`
- `lean/Round4/NestedBinomial.lean`: `9b6a2cf04f32fc55e725db19cd00ff94cc0a0d21a579381442a02cc28b1ec0eb`
- `lean/Round4/CatalanContracts.lean`: `6be71cb602506435b014b7e49fe06fccd642e1635c26f209c30f1b95a7ff1e00`
- `scripts/verify_catalan_composition.py`: `334b68315bc2102c1611240c9d2a0277facd13c094baeee904f69da48964b9fc`
- `validation/round4_catalan_endpoints.json`: `e8f3e2fd5c47bf378e8d760ae2e372ccc2f4d98b39b23c41990f6506d177e9c7`
- `validation/catalan_composition_numeric.json`: `ed79298634367918d06dc2e156cdab29f2bdacd159cb1d1ea67373486882b602`
