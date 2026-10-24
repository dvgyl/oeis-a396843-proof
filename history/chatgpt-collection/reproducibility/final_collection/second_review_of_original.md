# Independent AI semantic review of the original-group manuscripts

Reviewer: a separate ChatGPT agent from the one that prepared these ten entry presentations. This is an AI-assisted review, not independent human peer review. Human review remains pending.

## Outcome

No mathematical blocker was found. The ten manuscripts and their explicit Lean interfaces preserve the completed statements and the distinctions between proved source assertions, corrected false assertions, and the known A396797 result. The review examined the definitions and proof arguments, not merely compilation success. The final collection's central compiler and axiom audit remain the authoritative mechanical checks.

## Reviewed files and comparisons

Reviewed all ten standalone manuscript sources and all ten dedicated Lean entry files. Repeated general sections were checked in full in a representative manuscript and compared line by line across the other copies. Compared the results with the preserved `prior_work/hanna_congruences.tex`, `manuscript/compositional_congruences.tex`, `docs/COVERAGE.md`, the source-specific names in `validation/final_theorems.json`, and the shared Hanna, Consecutive, and scaled-inverse definitions and endpoints. The catalogue was also checked for source URLs, status, theorem names, and index descriptions.

### A396843 and A396844: the original parameter family

The normalized source is A_m(x A_m-m x A_m²)=x². The integer coefficients and inverse coefficients are the actual canonical objects `Hanna.a` and `Hanna.b`, not arbitrary sequences assumed to have the desired residues. Existence over every commutative ring follows from a triangular perturbation whose leading multiplier is one. The inverse proof establishes both composition directions.

The parity argument tests the unique reduced solution x/(1+x) for odd m and x for even m. The modulus-square proof first obtains an exact integral decomposition A_m=x+mC and then derives xC+C(x²)=x³ modulo m. Cancelling m in this step is integer divisibility, not cancellation of a zero divisor in ZMod(m²). Its lacunary solution has alternating signs at 2^j+1.

The binary-divisibility proof uses the shifted index r=n-1. The two actual inverse identities give F=G(x²)+mxF² and the inverse coefficient recursion. The simultaneous induction first establishes divisibility of f_r and then of g_r, so it is not circular. Every product uses only previously available g-coefficients. Binary subadditivity and s₂(2r)=s₂(r) yield the stated exponent. The same operations apply over Z[t], justifying the polynomial versions. The power-of-two index includes k=0 correctly.

For prime p dividing m, the lower bound is e s₂(n-1), with e the exact exponent of p in m. At n=2^j+1 the factor (-1)^j+mq is prime to p, giving exactly e. All other positive shifted indices have at least two binary ones. The formal `ExactExponent` predicate explicitly means p^e divides z and p^(e+1) does not; zero has no finite exact exponent. This agrees with the manuscript convention v_p(0)=infinity.

The m=3 exceptional residue classes are 3 at n=4^k+1 and 6 at n=2*4^k+1 modulo9. The m=4 classes are4 and12 modulo16. Both exclude n=1 from the classification. A396843 credits Danial Asaria's prior counterexample a_5(3)=975. A396844 correctly diagnoses the missing first class in the earlier n>8 clause; n=17 has residue4. Neither false source claim is presented as proved.

The A396844 formal map now explicitly names the shared Hanna.Acceptance endpoints for inverse binary divisibility and the minimum prime-exponent criterion. It also identifies the n=17 example as the k=2 specialization of the checked residue classification. The reviewer's navigation clarification was resolved; no new negation endpoint is claimed and no original proof was changed. This clarification was re-read against the shared endpoint types.

### A396099, A396797, A396798, and A396807

The family is F_r=x+F_r^(composition r) F_r^(composition(r+1)), with a normalized solution. The contraction raises the agreement order by one degree. Reduction therefore commutes with its canonical construction.

The comparison formula uses T_k=x/(1-kx) and H=x^4/(1-x)^3. For odd r the product denominator reduces to1-x modulo2r. For even r, r²=0 modulo2r and the displayed square-zero substitution calculation gives (T+rH) composed twice equal to T_2. Both rational identities used in the residual calculation are algebraically correct. Even iterate indices have no correction; odd indices receive rH. The low-degree coefficient guards are retained.

The degree-two coefficient is k modulo2r, proving the exact order. The extension to signed iterates uses the genuine two-sided inverse and composition-group reduction modulo2r, not an unsupported extension of a natural-index formula. Degree one is handled by k^0=1, including k=0.

For A396099, the four original conclusions retain their bounds: positive-index oddness; the 1,3,3,1 block starting at degree3; the second iterate vanishing above degree2; and residue2 for F-XF^(composition3) above degree2. The difference's full-series formula retains the initial X term. The direct typed contract starts from the literal source equation and does not assume a desired congruence.

For A396798, the false coefficient phase beginning at degree1 is refuted by degree3. The corrected block1,1,5,5 starts at degree2. Even iterates2 and6 vanish above degree3, iterate4 above degree2, and iterate8 above degree1. Odd iterates3,5,7 have the stated blocks beginning at degree2. All seven true source assertions remain present.

For A396807, all integer iterate indices are included modulo10. For A396797, the same statement modulo6 is correctly identified as a known result credited to Shiva Priyan Shanmuga Sundaram, with no new-discovery claim.

### A393856, A393857, A393858, and A393859

The source is G_q(x-xG_q(qx)/q)=x for q=4,5,6,7 respectively. The quotient is interpreted coefficientwise by q^(n-1)[x^n]G_q for n>0, and the normalized constant coefficient is zero. This agrees with the actual `scaleTail` definition on the stated domain. No inversion of q in a residue ring is used.

The degree-n source equation determines the coefficient g_n from earlier coefficients with leading multiplier one. This gives integral existence, uniqueness, and transport under ring homomorphisms. At q=-1 the geometric comparison series satisfies the source equation exactly, proving residue1 modulo q+1 even for the composite moduli6 and8.

For even q, characteristic two reduces the equation to G_q(x+x²)=x. The series sum_j x^(2^j) satisfies it by coefficientwise cancellation, and uniqueness identifies its support. The all-index parity statements include n=0 and n=1 correctly. The odd-q parity observation follows from the even modulus q+1. All six selected source assertions are present in their specialized interfaces.

## Scope and review limits

Historical sequence and conjecture credits are retained. The original repository's statement of prior human review is not attributed to the new editorial consolidation. The new papers explicitly disclose AI generation and pending independent human review. No analytic convergence theorem or worldwide priority assertion was inferred from formal algebra or compiler success.

This review is semantic. It does not duplicate the final centralized fresh compilation or axiom audit, and it does not establish novelty. The author's PDF rendering/visual review is recorded separately.

## Reviewed source hashes

Recorded UTC: 2026-10-24T18:36:53.931840+00:00

| File | SHA-256 |
|---|---|
| `manuscripts/A396843.tex` | `c8e56137d7d49425c626810c92984abd5d2b7b64c2b2e898d982226b9bb8b090` |
| `lean/Entries/A396843.lean` | `4e4866f66eff18aea56a291f7bdaa344a5f1d131db2f577b740847ee0b47d96d` |
| `manuscripts/A396844.tex` | `c509709500b3a6fa4cea33561b27bfec5b8cabaa24b1173193ec88bd7137623e` |
| `lean/Entries/A396844.lean` | `5bdbcfdf7aaa759e26271e5f54181c2fe1c6bae301bc39c3a9c68fdd04f7d9ca` |
| `manuscripts/A396797.tex` | `34172dbb87577c6e4042c58fc040ba48b5676d8319fdb59ac8b03987e1f88b6f` |
| `lean/Entries/A396797.lean` | `f39b4bb2669e5b6c6bdd3ff40283fb300d99e3e68fad42f54d72282778e05999` |
| `manuscripts/A396099.tex` | `daa6ddfd7cdec7303f9cd88f348525b6631f6347d3366918a6a28ef8397a2cdb` |
| `lean/Entries/A396099.lean` | `eed565e3dca898a9dc230bf9d9963b81a76d42de6edf9d6d981a9200c9de5166` |
| `manuscripts/A396798.tex` | `33cf6ce859242b74869d7887b242fc203429cd640daf55a2672d13ff4f1fed70` |
| `lean/Entries/A396798.lean` | `c13014b9a86cff6f252ef0a5c0b2db9e0e733e85cb4f76d6431431d0f6478979` |
| `manuscripts/A396807.tex` | `0a12f474e2be5f6b4778795905b3fb05f64b9b24653d7dbaba3c3140e16c49f9` |
| `lean/Entries/A396807.lean` | `325ffd1994cb5801265fec81f09e500a7b559eab999aea0649b767d0673d234c` |
| `manuscripts/A393856.tex` | `4a33ebf81a31f4638f75bacfc4f8ef60743c901fade392ed34d79f4660ef26bf` |
| `lean/Entries/A393856.lean` | `59bb4384976307072aa8ccf89cb6f9eb08936a2f08f03bd032e65bbf1e3b2722` |
| `manuscripts/A393857.tex` | `ecc800c20d25b05fdbfe84023f1aaf53218d5ef1f6d070d82c470997abc7b175` |
| `lean/Entries/A393857.lean` | `950c180286bd92d3ae64b34cd7b4da977b976a64da98077e6554753ff0a0efaf` |
| `manuscripts/A393858.tex` | `835848b5338b18374fc17a803f450117f4d68e603a72edb8e70fca21bd7beb4e` |
| `lean/Entries/A393858.lean` | `3e498a821d1a2583368dc57379d47cb24e5344c46ecd8c5d59a7da7079f6fbce` |
| `manuscripts/A393859.tex` | `333e276000287d7ed83a96ec49e6a405051e43cb2c5d8a6ac950554999fd17f6` |
| `lean/Entries/A393859.lean` | `60b315566033503d3d82c0303d6928a69a0b62344a7588ab7f657dba7074da3a` |

A396844 map clarification rechecked UTC: 2026-10-24T18:38:08.205326+00:00.
