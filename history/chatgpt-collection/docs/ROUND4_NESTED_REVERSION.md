# A195194: parity of infinite nested reversion

Prepared for **Dev Goyal**, 24 October 2026.

**AI disclosure.** ChatGPT (OpenAI) generated the mathematical proof, Lean implementation,
verification program, and this exposition at Dev Goyal's request. Paul D. Hanna is
credited for the OEIS sequence and conjecture. Independent human review is pending.
No claim of publication, OEIS acceptance, or exclusive priority is made.

## Source and exact result

The official entry [OEIS A195194](https://oeis.org/A195194), retrieved on 24 October
2026, defines the ordinary generating function by infinite nested **compositional
reversion**:

\[
 A(x)=\operatorname{Rev}\bigl(x-x\operatorname{Rev}(x-2x\operatorname{Rev}
 (x-3x\operatorname{Rev}(\cdots)))\bigr).
\]

The entry author is **Paul D. Hanna**, dated **11 September 2011**. Its comments
attribute the parity conjecture to Hanna, dated **7 April 2026**. The OFFSET field
is `1,3`, so the displayed sequence begins at index one. The statement proved here is

\[
 \boxed{a(n)\text{ is odd}\quad\Longleftrightarrow\quad
        n=2^k\text{ for some }k\ge0.}
\]

The Lean theorem includes every natural index, including zero: the constant
coefficient is zero and zero is not a power of two. The source's range `n≥1` is
therefore included. This is one conjectural source statement, regardless of the
number of supporting construction and verification theorems.

At retrieval the official entry still called this statement a conjecture and
linked a coefficient table, but did not link a proof. Searches for the exact
identifier with `proof`, `parity`, and `conjecture`, including a separate stronger
search, did not identify an earlier proof. Search results were largely the entry
itself and irrelevant identifier collisions. This is a bounded prior-art check;
it does not establish that no prior or unpublished proof exists.

## 1. Giving the infinite expression a precise meaning

We prove a general construction over any commutative ring and any weight sequence
`w₀,w₁,…`. Let `F_j=x+O(x²)` be the tail at level `j`. The desired equations are

\[
 F_j=\operatorname{Rev}(x-w_jxF_{j+1}). \tag{1}
\]

Composing the proposed inverse on the right gives the equivalent equation

\[
 F_j=x+w_jF_j\,F_{j+1}(F_j). \tag{2}
\]

In degree `n≥2`, the nontrivial term on the right depends only on coefficients of
the two tails of degrees strictly below `n`. Both factors have zero constant
coefficient, and each starts with `x`. Thus all coefficients in degree `n` can be
defined simultaneously, after all lower degrees have been defined. This constructs
an integral family when the weights are integers and proves its uniqueness. No
unspecified boundary condition at infinity is assumed, and no division is needed
for the construction.

The implementation packages all tails as coefficients in the commutative ring
`ℕ → R`. Shifting that coefficient function replaces tail `j` by tail `j+1`.
The already verified triangular-recursion theorem then constructs the family.
Evaluation at each `j` recovers the ordinary formal power series in (2).

The expression `x−w_jxF_{j+1}` is normalized, hence has a unique normalized
compositional inverse. Equation (2) proves one inverse direction; the general
inverse theorem proves the other. The endpoint `source_existence_uniqueness`
states uniqueness using **both literal inverse identities**, not merely the
coefficient recursion.

### Finite nests really converge coefficientwise

Let `F_j^[0]=x`, and define the finite nests recursively by

\[
 F_j^{[d+1]}=\operatorname{Rev}(x-w_jxF_{j+1}^{[d]}).
\]

The formal proof establishes the exact bound

\[
 F_j^{[d]}-F_j\in x^{d+2}R[[x]]. \tag{3}
\]

Indeed, multiplication by `x` improves agreement by one degree, and normalized
compositional inversion preserves agreement. Both the finite approximation and
the true tail start with `x`, giving agreement modulo `x²` at depth zero. Induction
proves (3). Consequently depth `d` already determines coefficients through degree
`d+1`. This identifies the constructed family with the source's finite nesting
algorithm and its infinite formal expression.

The OEIS sequence is the specialization `w_j=j+1`, `A=F₀`. Thus the first two
levels are exactly

\[
 A=\operatorname{Rev}(x-xF_1),\qquad
 F_1=\operatorname{Rev}(x-2xF_2).
\]

## 2. Reduction modulo two

The construction commutes with coefficient ring homomorphisms. This follows
either from the coefficient recursion or by mapping the source equations and
using uniqueness. In particular, the integral family may be reduced modulo two.

At the second level the weight `2` vanishes. Equation (2) immediately gives

\[
 \overline F_1=x.
\]

At the first level the weight is `1`, so

\[
 \overline A=x+\overline A\,\overline F_1(\overline A)
             =x+\overline A^2. \tag{4}
\]

In characteristic two, squaring a series doubles its exponents. If
`b_n=[xⁿ] Ā`, equation (4) gives `b₁=1`, every odd-index coefficient beyond index
one is zero, and `b_{2m}=b_m` for `m≥1`. Repeatedly removing factors of two proves

\[
 \overline A(x)=x+x^2+x^4+x^8+\cdots,
\]

and therefore the claimed parity criterion for every coefficient. The formal
proof invokes the existing verified coefficient characterization of the unique
normalized solution of `U−U²=x` over `ZMod 2`.

The general mechanism is also proved: if `w_j=1` and `w_{j+1}=0` in a coefficient
ring, then the corresponding tail satisfies `F_j−F_j²=x`. This is a supporting
general theorem, not an additional OEIS conjecture count.

## 3. Formal files and endpoints

The main module is `lean/Round4/NestedReversion.lean`, with namespace
`Round4.NestedReversion`. The independently typed contracts are in
`lean/Round4/NestedContracts.lean`. The fixed endpoint fragment is
`validation/round4_nested_endpoints.json`.

| Endpoint | Mathematical content |
|---|---|
| `source_existence_uniqueness` | A unique normalized infinite family with both inverse identities, for arbitrary weights over any commutative ring. |
| `tail_is_inverse` | Each tail is the genuine formal inverse in (1). |
| `approximation_agrees` | The uniform finite-depth stabilization bound (3). |
| `map_tail` | Coefficient homomorphisms commute with the canonical construction. |
| `tail_quadratic_of_next_zero` | The general two-weight mechanism behind (4). |
| `A_source`, `A_source_left` | The literal first-level inverse identities of A195194. |
| `A_mod_two_quadratic` | The complete reduction `Ā−Ā²=x`. |
| `a195194_parity` | The exact unbounded parity conjecture. |

The typed contract `finite_nest_coefficients` states that for every `n<d+2`, the
degree-`n` coefficient computed by a finite nest of depth `d` equals the canonical
sequence coefficient.

## 4. Independent finite corroboration

`scripts/verify_nested_reversion.py` performs exact integer calculations; its
default output is `validation/nested_reversion_numeric.json`. The default degree
is 64. It checks all 20 displayed terms of A195194 and all 42 displayed
coefficients in the seven auxiliary tails `B,…,H` in the source examples.

One implementation computes finite nests by exact Lagrange coefficient
extraction. Every division is checked for zero remainder. A second implementation
solves `f(g)=x` coefficient by coefficient and agrees through degree 32. Neither
algorithm uses the predicted parity to produce the coefficients.

The program also checks both inverse directions and the equivalent fixed-point
equation for each of the first eight tails through degree 64, verifies the
stabilization bound at depths 0 through 12, and checks the complete binary
quadratic identity and all parities through degree 64. These finite checks
corroborate the interpretation and implementation; the Lean theorem proves the
infinite claim.

## Scope limits

This proof treats formal power series, not analytic convergence of the nested
expression at nonzero real or complex arguments. It does not establish an
asymptotic formula. It neither reclassifies the previously formalized geometric
weight families as new discoveries nor claims other observations in adjacent
OEIS entries without a named theorem endpoint.
