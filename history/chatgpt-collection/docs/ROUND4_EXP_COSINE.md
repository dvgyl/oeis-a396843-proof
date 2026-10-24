# A380056: two coefficient conjectures for an exponential generating function

Prepared for **Dev Goyal**, 24 October 2026.

**AI disclosure.** OpenAI ChatGPT generated the mathematics, Lean proofs,
verification program, and this exposition at Dev Goyal's request. OEIS credits
Paul D. Hanna with the sequence entry and its two conjectures. Independent
human review remains pending. No OEIS submission or claim of exclusive
historical priority is implied.

## Source and exact scope

The official entry [OEIS A380056](https://oeis.org/A380056), retrieved on
2026-10-24, defines the integers by

\[
 A(x)=\sum_{n\ge1}a(n)\frac{x^n}{n!}
     =\frac{e^x-1}{\cos(2x)}.
\]

The entry's author line is Paul D. Hanna, 2025-01-28; its raw OFFSET field is
`1,3`. The first component specifies that the displayed sequence begins at
index one. We set the auxiliary value `a(0)=0`, which is the EGF's constant
coefficient. The entry's COMMENTS section explicitly labels both following
statements as conjectures:

1. `a(n) ≡ 1 (mod 4)` for every `n≥1`.
2. `5` divides `a(4n)` for every `n≥1`.

Both are proved for all indices in the specified ranges. The second follows
from the stronger complete classification

\[
 a(n)\equiv2\,2^n+3\,4^n\pmod5
 \quad(n\ge0),
\]

whose residue at `n mod 4 = 0,1,2,3` is respectively `0,1,1,3`. In particular,
`5 | a(n)` if and only if `4 | n`, including the auxiliary index zero.

## Source construction over the integers

Write the cosine in divided-power notation:

\[
 \cos(2x)=\sum_{n\ge0}c_n\frac{x^n}{n!},\qquad
 c_{2j}=(-4)^j,\quad c_{2j+1}=0.
\]

For two sequences define their binomial convolution by

\[
 (f\star g)_n=\sum_{k=0}^n\binom nk f_k g_{n-k}.
\]

Since `c₀=1`, the equation `a⋆c=d`, with `d₀=0` and `dₙ=1` for `n>0`,
has a unique integer solution. Explicitly,

\[
 a_0=0,\qquad
 a_n=1-\sum_{k=0}^{n-1}\binom nk a_k c_{n-k}\quad(n>0).
\]

This triangular recursion is the actual formal definition; it does not use
either conjectural congruence. Its binomial-convolution identity is proved
by isolating the last summand, and uniqueness follows by induction.

Over the rational numbers, the formal proof establishes that the EGF map
takes binomial convolution to ordinary power-series multiplication. The
factorial identity `binomial(n,k) k! (n−k)! = n!` supplies the coefficient
calculation. It also proves that the EGF of `c` is Mathlib's cosine power
series rescaled by two. Consequently the constructed series satisfies the
literal identity

\[
 A(x)\cos(2x)=e^x-1.
\]

The cosine's constant coefficient is one, so its multiplicative inverse
exists. The proof obtains the literal quotient and uniqueness among all
rational formal power series. It additionally checks
`n! [xⁿ]A = a(n)`. This connects the integer congruence theorems to the
specific EGF in the source.

## Proof modulo four

All positive-degree coefficients `cₙ` vanish modulo four: odd coefficients
are zero, and `c₂ⱼ=(-4)^j` is a multiple of four for `j≥1`. Thus `c` reduces
to the convolution identity sequence `(1,0,0,...)`. Reducing `a⋆c=d`
modulo four gives `a=d`, and hence `a(n)≡1 mod4` for every positive `n`.

## Proof modulo five

Work with sequences valued in `Z/5Z`, using binomial convolution. For a
residue `s`, define `E_s(n)=s^n`, with `0^0=1`. The binomial theorem gives

\[
 E_s\star E_t=E_{s+t}.
\]

These are divided-power coefficient sequences. We do not introduce
factorial denominators or an ordinary exponential series over `Z/5Z`.

Because `−4≡1 mod5`, the cosine coefficients reduce to one at even indices
and zero at odd indices. Therefore

\[
 c=3(E_1+E_4).
\]

Consider `b=2E₂+3E₄`. Direct binomial convolution yields

\[
\begin{aligned}
 b\star c
 &=6E_3+6E_1+9E_0+9E_3\\
 &=E_1-E_0=d\qquad\text{in }\mathbf F_5.
\end{aligned}
\]

The same triangular uniqueness argument applies over `Z/5Z` because
`c₀=1`. Thus the reduction of the canonical integer sequence is `b`, proving
the formula. Both `2⁴` and `4⁴` are one modulo five, so the resulting sequence
has the displayed four-term residue pattern. Only its zero residue class
is `n≡0 mod4`, which proves the exact divisibility statement and the second
source conjecture.

## Lean theorem endpoints

The implementation is `lean/Round4/ExpCosine.lean`, with explicit acceptance
types in `lean/Round4/ExpCosineContracts.lean`. All implementation names
below have namespace `Round4.ExpCosine`.

| Content | Principal endpoint |
|---|---|
| Integer coefficient equation and uniqueness | `a_conv`, `a_convolution_unique` |
| Correct interpretation of cosine | `cosine_egf_eq` |
| Integer coefficients of the rational EGF | `A_coeff`, `A_integral_coefficients` |
| Literal cleared source equation | `a380056_source_equation` |
| Literal quotient | `a380056_source_quotient` |
| Source existence and uniqueness | `a380056_source_existence_uniqueness` |
| First source conjecture | `a380056_mod_four` |
| Stronger modulo-five formula | `a380056_mod_five_formula` |
| Entire modulo-five pattern | `a380056_mod_five_residue` |
| Period four | `a380056_mod_five_period` |
| Second source conjecture | `a380056_five_dvd` |
| Exact divisibility by five | `a380056_five_dvd_iff` |

The explicit endpoint manifest is `validation/round4_exp_cosine_endpoints.json`.
These are universally quantified proofs, not finite verifications.

## Independent numerical corroboration

`scripts/verify_exp_cosine.py` constructs the integers by binomial recursion
through index 400. A separate ordinary power-series division over exact
Python rational numbers computes `(exp(x)−1)/cos(2x)` through degree 80;
multiplication by the factorial recovers the same integers. The program
also multiplies the literal rational denominator and quotient to check the
source identity, matches all 22 displayed OEIS terms, and checks both
conjectures and the stronger complete modulo-five classification. Its
report is `validation/exp_cosine_numeric.json`. These finite checks provide
source and implementation corroboration; the infinite results are proved
in Lean.

## Prior-art and scope limits

At retrieval, the official entry still marked both target statements as
conjectures and linked no proof. Exact-ID searches using proof, conjecture,
and OEIS Open terms, together with a search for the defining EGF, found no
relevant earlier proof. The parent agent also searched the public
[Awesome AI Proofs catalogue](https://github.com/subroy13/awesome-ai-proofs)
and the full primary
[DeepMind OEIS theorem mapping](https://github.com/google-deepmind/formal-conjectures/blob/auto_oeis/FormalConjectures/OEIS/Auto/THEOREM_MAPPING.txt)
and found no entry for A380056. This bounded search does not establish worldwide
openness or historical priority. The proofs themselves are elementary
once the binomial-convolution reduction is recognized.

No asymptotic formula, analytic convergence theorem, or claim about the
different reversion sequence A380555 is proved by this module.
