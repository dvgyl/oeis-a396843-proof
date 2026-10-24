# A397588 and A389536: two coefficient conjectures

**AI disclosure.** ChatGPT (OpenAI) generated these mathematical proofs, Lean formalizations, verification code, and explanatory notes autonomously at the request of Dev Goyal. Dev Goyal supplied the reference project and requested the work. Independent human review is pending. No OEIS acceptance, publication, or exclusive priority is claimed. See `AI_DISCLOSURE.md` for the package-wide statement.

## Source status and exact scope

The official entries [A397588](https://oeis.org/A397588) and [A389536](https://oeis.org/A389536), both attributed to Paul D. Hanna, were checked on **24 October 2026**. Each still explicitly called the coefficient statement below a conjecture. The retrieved entries linked numerical tables but no proof of the target assertion. Searches for the exact identifiers with “proof” and “conjecture” located no separate proof. This is a bounded source check, not an exhaustive priority search.

Both series have integer coefficients and normalization `A(x)=x+O(x²)`. The proofs construct these source-defined series and prove their uniqueness before deriving congruences.

| Entry | Defining equation | Proved source conjecture |
|---|---|---|
| A397588 | `A=x+(xA²)'` | `a(n)` is odd exactly when `n` is a power of two. |
| A389536 | `A(x²+2x³)=xA(x)` | For `n>1`, the residue modulo four is `2` exactly when `n=2^k+1`; the residue is `0` otherwise. |

The A397588 entry also states divisibility by three for `n>1` without labeling it a conjecture. We formally verify that additional assertion as a related source claim. It is not counted as another newly solved conjecture.

## 1. A397588: construction and uniqueness

Let `R` be any commutative ring and define the formal-series operator

\[
 T(G)=x+\frac{d}{dx}(xG^2).
\]

If `G=x+O(x²)`, then `xG²` has order at least three, and its derivative has order at least two. Hence `T(G)` is again normalized.

Suppose normalized series `G,H` agree below degree `r`. Their difference is divisible by `x^r`, while `G+H` is divisible by `x`. Therefore

\[
 G^2-H^2=(G-H)(G+H)=O(x^{r+1}),
\]

so

\[
 T(G)-T(H)=\frac{d}{dx}\bigl(x(G^2-H^2)\bigr)=O(x^{r+1}).
\tag{1}
\]

Formal differentiation lowers order by at most one, including in positive characteristic. Thus each coefficient of `G=T(G)` depends only on earlier coefficients. Explicitly, with `a₀=0` and `a₁=1`,

\[
 a_n=(n+1)\sum_{j=1}^{n-1}a_ja_{n-j}\qquad(n>1).
\tag{2}
\]

This recursively constructs the normalized solution over `R`, and in particular over the integers. No division is needed. If two solutions agree below degree `r`, equation (1) forces agreement in degree `r` as well; strong induction proves uniqueness.

The formal implementation uses the project's triangular-coefficient construction applied to `G−T(G)`. It proves actual existence and uniqueness over every commutative ring, not a statement conditional on an unproved solution hypothesis. The canonical series `Round3.DifferentialParity.A` is chosen from this existence theorem. Its defining equation is proved literally with Mathlib's formal derivative.

Coefficientwise ring homomorphisms commute with formal differentiation: the coefficient of degree `n` in a derivative is `(n+1)` times the original coefficient of degree `n+1`. Uniqueness therefore shows that reducing the integer solution modulo any integer gives the canonical solution in the reduced coefficient ring.

## 2. A397588: parity at every index

Reduce the actual integer series modulo two and write it as `A` over `𝔽₂`. The Leibniz rule gives

\[
 (A^2)'=2AA'=0.
\]

Consequently

\[
 (xA^2)'=A^2,
 \qquad A-A^2=x.
\tag{3}
\]

In characteristic two, formal-series Frobenius gives

\[
 A(x)^2=A(x^2).
\]

Equation (3) therefore recursively identifies the support. The coefficient of `x` is one. At any odd degree greater than one it is zero, and at an even degree `2m` it equals the coefficient of degree `m`. Repeatedly removing factors of two proves

\[
 [x^n]A=1
 \quad\Longleftrightarrow\quad
 n=2^k\text{ for some }k\ge0.
\]

The project already contained the fully proved all-index support theorem for normalized solutions of `H−H²=x` over `𝔽₂`. This proof applies it to the newly constructed differential solution. It does not define the sequence using the claimed support pattern.

The final theorem includes `n=0`: the constant coefficient is zero and zero is not a power of two.

### Additional divisibility by three

In characteristic three the normalized series `x` itself satisfies the differential equation because

\[
 x+(x\,x^2)'=x+(x^3)'=x.
\]

Uniqueness proves the stronger whole-series statement

\[
 A(x)\equiv x\pmod3.
\]

It follows that every coefficient of degree greater than one is divisible by three, as separately asserted in the source entry.

## 3. A389536: construction and uniqueness

Put `B=x²+2x³`. We seek the normalized series satisfying

\[
 A(B)=xA.
\tag{4}
\]

For `n≥2`, the coefficient of degree `n+1` in (4) determines `a_n` using only earlier coefficients:

\[
 a_n=
 \sum_{\substack{j\ge1\\0\le n+1-2j\le j}}
 a_j\binom{j}{n+1-2j}2^{n+1-2j}.
\tag{5}
\]

Indeed, `B^j=x^{2j}(1+2x)^j`, and every contributing index satisfies `j≤(n+1)/2<n`. Thus the recurrence constructs the series over any commutative ring, with no division, and determines it uniquely once `a₀=0,a₁=1` are fixed.

The Lean proof uses the same fact in a form convenient for formal-series reasoning. Define

\[
 E(G)=xG-G(B).
\]

For normalized `G`, this residual is divisible by `x³`. If `G−H` is divisible by `x^r`, where `r≥2`, then

\[
 E(G)-E(H)-x(G-H)=-(G-H)(B)
\]

is divisible by `x^{2r}` and hence by `x^{r+2}`. Thus the coefficient of degree `r+1` in the residual difference is exactly the coefficient of degree `r` in `G−H`. This supplies a triangular recursion with leading coefficient one, proves existence, and gives uniqueness by strong induction.

The canonical series `Round3.MahlerParity.A` is obtained from this source equation. Its reduction under a coefficient ring homomorphism is identified with the canonical reduced solution by uniqueness.

## 4. A389536: the full series modulo four

Work over `ℤ/4ℤ`. Let `H=x+O(x²)` be the canonical solution of

\[
 H-H^2=x.
\tag{6}
\]

Existence, uniqueness, and the reduction properties of this series were proved in the previous project. Its integer lift is `x` times the Catalan generating function, although the formal proof only uses equation (6) and the already proved power-of-two support of its reduction modulo two.

We prove the stronger comparison identity

\[
 A=x+2xH\pmod4.
\tag{7}
\]

To do so, define `C=x+2xH` over `ℤ/4ℤ`. It is normalized because `H` has constant coefficient zero. Reducing modulo two gives `B=x²`; Frobenius then yields

\[
 H(B)\equiv H(x^2)=H^2\pmod2.
\]

Multiplying an equality modulo two by two produces an equality modulo four. Coefficientwise, this is the elementary implication that `u−v` even implies `2u−2v` divisible by four. Therefore

\[
 2H(B)=2H^2\quad\text{in }(\mathbb Z/4\mathbb Z)[[x]].
\tag{8}
\]

Now compute, entirely in that ring:

\[
\begin{aligned}
 C(B)
 &=B+2BH(B)\\
 &=x^2+2x^3+2x^2H(B)\\
 &=x^2+2x^3+2x^2H^2\\
 &=x^2+2x^2H\\
 &=xC.
\end{aligned}
\]

The second line discards a multiple of four, the third uses (8), and the fourth uses `H²=H−x`. Hence `C` satisfies the actual source equation (4). Uniqueness over `ℤ/4ℤ` identifies it with the reduction of the integer source series and proves (7). No cancellation by two in `ℤ/4ℤ` is used.

For `n>1`, equation (7) gives

\[
 a_n\equiv 2[x^{n-1}]H\pmod4.
\]

The right side is two precisely when the indicated coefficient of `H` is odd. By (6) modulo two, that happens precisely when `n−1=2^k`. In every other case it is zero. This proves both branches of the source conjecture for every permitted index.

## Formal coverage

The proof files are `lean/Round3/DifferentialParity.lean` and `lean/Round3/MahlerParity.lean`. Explicit typed acceptance contracts in `lean/Round3/ElementaryContracts.lean` spell out normalization, the literal source equations, existence, uniqueness, whole-series reductions, and the exact coefficient conclusions.

The main theorem names are:

| Name, within the indicated namespace | Meaning |
|---|---|
| `Round3.DifferentialParity.existence_uniqueness` | Unique normalized solution of the differential equation over any commutative ring. |
| `Round3.DifferentialParity.A_equation` | The actual canonical solution satisfies that equation. |
| `Round3.DifferentialParity.a397588_parity` | Exact odd-index characterization, for every natural index. |
| `Round3.DifferentialParity.A_mod_three` | Full canonical series modulo three is `x`. |
| `Round3.DifferentialParity.a397588_divisible_by_three` | The separate source assertion for every `n>1`. |
| `Round3.MahlerParity.existence_uniqueness` | Unique normalized solution of the substitution equation over any commutative ring. |
| `Round3.MahlerParity.A_equation` | The actual canonical solution satisfies that equation. |
| `Round3.MahlerParity.A_mod_four` | Full comparison `A=x+2xH` modulo four. |
| `Round3.MahlerParity.a389536_residue` | Both residue cases, for every `n>1`. |
| `Round3.MahlerParity.a389536_four_dvd_iff` | The complementary case explicitly as integer divisibility by four. |

All index quantifiers are unbounded. The use of finite `decide` checks for identities among the four elements of `ℤ/4ℤ` supplies ordinary kernel-checked proof terms; it does not replace the infinite coefficient argument.

## Independent numerical corroboration

Run:

```sh
python scripts/verify_differential_mahler.py --output validation/differential_mahler_numeric.json
```

This separate exact-integer program reconstructs the coefficients from equations (2) and (5), without using the claimed parity or residue pattern. It matches all 20 displayed source coefficients of A397588 and all 34 displayed source coefficients of A389536. It checks the differential identity and parity through degree 500, divisibility by three from degree two through 500, and both modulo-four cases for A389536 through degree 2050. It independently evaluates the literal Mahler substitution by generic polynomial multiplication through degree 81, and checks the stronger Catalan comparison through degree 2050.

These computations corroborate indexing and source identification. The proof for every index is supplied by Lean, not inferred from this finite range.

## Local formal verification record

The three elementary modules build with Lean 4.19.0 against the pinned Mathlib revision without warnings. The 27 explicit proof and source-contract endpoints in `validation/round3_elementary_endpoints.json` pass the strict transitive axiom audit. Their dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`. The raw report and parsed audit are saved in `validation/round3_elementary_axioms.log` and `validation/round3_elementary_axioms.json`. These are dependency checks; the separate typed source contracts and semantic review address the meaning of the propositions.
