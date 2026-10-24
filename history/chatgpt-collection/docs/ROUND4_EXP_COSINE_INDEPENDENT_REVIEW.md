# Independent semantic review: A380056

**AI-assisted review for Dev Goyal, 24 October 2026. Independent human review is pending.**

The primary agent reviewed the mathematical definitions and proof terms supplied by the separate elementary-proof agent against the official source <https://oeis.org/A380056>. The entry has offset `1,3`, is credited to Paul D. Hanna on 28 January 2025, and contains two selected conjectures: all positive coefficients are one modulo four, and the coefficients at positive multiples of four are divisible by five.

## Finding

No mismatch was found between the formalized statements and these source claims. The implementation proves a stronger result: `5 | a(n)` if and only if `4 | n`, including the auxiliary index zero where `a(0)=0`.

## Mathematical checks

`Round4.ExpCosine.a` is defined by an integer recursion with no divisibility assumption. Its binomial convolution with `cosineCoeff`, whose even-index values are `(-4)^(n/2)` and odd-index values are zero, is zero at index zero and one at every positive index. The coefficient of the newly determined `a(n)` in this convolution is one, proving uniqueness.

The rational series `egf a` has coefficients `a(n)/n!`. The proof `egf_mul` establishes the binomial-convolution/product relation with factorial denominators justified in the rational coefficient field. `cosine_egf_eq` identifies the other factor with Mathlib's formal cosine rescaled by two. The actual equation is therefore `A*cos(2x)=exp(x)-1`; the constant coefficient of the cosine is proved to be one, and the formal quotient and uniqueness are proved using its multiplicative inverse.

The modular arguments are performed on integer divided-power coefficients. They do not reduce a rational power series with factorial denominators directly into characteristic five. Modulo four, the cosine coefficient sequence is the convolution identity. Modulo five, writing `E_s(n)=s^n` gives `E_s*E_t=E_(s+t)` under binomial convolution, including the index-zero convention. The candidate `2E_2+3E_4` multiplies `3(E_1+E_4)` to `E_1-E_0`. Uniqueness then proves the candidate formula for every index. The four residue cases are checked in the kernel over `ZMod 5`.

## Scope and validation

Both source conjectures are present in explicit typed contracts. The stronger modulo-five formula, period, residue classification, and integer divisibility iff are also required endpoints. The associated numerical program independently divides the rational formal exponential by the cosine, checks factorial coefficient conversion, and matches all 22 displayed source terms. The universal proof does not depend on the finite checks.

No result about the compositional inverse entry A380555, analytic asymptotics, or convergence is claimed. A current conjecture label and a bounded unsuccessful prior-art search do not establish global originality. The proof source and exposition explicitly disclose AI generation and retain the source contributor's credit.

This semantic review complements the cumulative clean compilation, separately compiled source contracts, full theorem-type output, and transitive axiom audit.
