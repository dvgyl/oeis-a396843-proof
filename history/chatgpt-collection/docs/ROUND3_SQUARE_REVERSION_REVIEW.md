# A389542: independent AI semantic review

Prepared for Dev Goyal on 24 October 2026 by an AI agent other than the agent
that implemented `Round3/SquareReversion.lean`. The agents share the project
and mathematical context. This is an additional AI review, not independent
human review, a publication endorsement, or a priority determination.

## Source correspondence

The reviewer reopened the official [OEIS A389542 page](https://oeis.org/A389542)
and compared the formal definitions and endpoint types with it. The source has
offset one and generating function

\[
 A=x+2x^2+10x^3+\cdots,\qquad A(A^2-x^2)=4A^3.
\]

Its conjectured positive-index pattern starts at \(n>1\): the coefficient is
two modulo four when \(n=2^k+1\) for a nonnegative integer \(k\), and otherwise
is divisible by four. The current entry still labeled this a conjecture when
read. Establishing historical priority is outside this review.

The formal constant coefficient zero and linear coefficient one match this
indexing. `SourceEquation` uses actual power-series substitution with the
outer series as the first argument. The displayed theorem `a389542_equation`
is the literal source equation over `PowerSeries ℤ`, and `SquareContracts`
restates it directly. The final residue and divisibility endpoints retain
`1 < n`, so the exceptional linear coefficient is not accidentally included.

## Construction and uniqueness

The reviewed construction begins with the unique normalized solution

\[
 L=x+L^2-2xL(4x^3).
\]

Every next coefficient is determined from earlier coefficients with leading
coefficient one. The formal construction uses a proved contraction in powers
of \(X\) and the project's well-founded triangular recursion. It does not
assume that dividing arbitrary integers by two preserves integrality.

The definition \(R=x-2xL\) gives

\[
 R^2+R(4x^3)=x^2.
\]

The factorization in `R_equation` was checked algebraically: the excess over
\(x^2\) is \(4x^2(-L+L^2+x-2xL(4x^3))\), which vanishes by the constructed
equation. `A389542` is then the genuine compositional inverse of \(R\).
Both inverse identities are proved explicitly before use.

`source_of_inverse` and `inverse_of_source` give the two directions of the
conversion between the source and inverse equations. In particular, a
normalized source solution \(A\) has a compositional inverse \(B\); substituting
\(x=B(t)\) and applying \(B\) gives \(B(t)^2+B(4t^3)=t^2\).
All substitution arguments have constant coefficient zero.

The proof of uniqueness for this inverse equation is intentionally over the
integers. If two normalized solutions first differ in degree \(r\ge2\), their
squares first differ by twice that coefficient in degree \(r+1\), while the
substituted difference starts in degree \(3r\). The formal proof cancels the
factor two only in \(\mathbb Z\). It does not assert this argument works in a
ring with two-torsion. The resulting uniqueness identifies every normalized
integer solution of the original source equation with the canonical inverse.

## Reduction and residue argument

The auxiliary construction works over every commutative ring, and `map_L`
is proved from its actual equation and uniqueness. `map_R` follows from the
polynomial definition, while `map_A389542` uses the previously proved theorem
that coefficient maps commute with genuine normalized compositional inverses.
This ties the finite-ring calculation to the canonical integer sequence.

Modulo two, the auxiliary equation becomes \(L-L^2=x\). The imported
power-series theorem applied to this equation identifies its nonzero
coefficients exactly at \(2^k\), including \(k=0\), and correctly excludes
degree zero. It is not a hypothesis based on initial data.

Modulo four, \(R\equiv x\pmod2\), so reducing a composition gives
\(L(R)\equiv L\pmod2\). The `ModFour` lemma turns this into
\(2L(R)=2L\) in the modulus-four ring. The proof of `R_involution_mod_four`
uses this equality and the vanishing of four; it does not cancel two or
assume the modulus-four ring is a domain. Thus \(R\circ R=x\), and uniqueness
of compositional inverses gives \(A=R\pmod4\).

The final coefficient shift is \(a(n)\equiv-2\ell_{n-1}\pmod4\). Combining
the exact parity support with \(n>1\) gives precisely \(n=2^k+1\).
`a389542_four_dvd_iff` converts residue zero to divisibility in the integers
using Mathlib's integer-to-`ZMod` theorem, rather than changing the meaning
of divisibility inside the finite ring.

## Finite corroboration and review outcome

The reviewer inspected `scripts/verify_square_reversion.py` and
`validation/square_reversion_numeric.json`. The direct source recursion checks
the required divisions by two, separately constructs and reverts the auxiliary
series, and compares their coefficients through degree 80. The recorded
prefix matches all 22 terms displayed in the official entry. Literal source
and inverse equations are checked through degree 81, with both inverse
directions checked through degree 80. These are corroborative translation
checks; the unrestricted index claims come from the formal proofs.

No source-definition mismatch, omitted normalization, index-range error,
unjustified modular cancellation, or unconstructed source-solution assumption
was found. The reviewer did not modify the implementation. The final package
build and transitive axiom audit remain separate checks of Lean acceptance;
this review addresses the mathematical meaning and source alignment of the
statements being checked.
