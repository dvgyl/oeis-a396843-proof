# Round 2: exact result coverage and preservation of the previous package

Prepared for **Dev Goyal**, 24 October 2026.

**AI disclosure.** ChatGPT (OpenAI) generated the additional proofs, Lean code, verification programs, and this coverage document in response to Dev Goyal's request. The review performed during preparation was AI-assisted. Independent human review is pending. See `AI_DISCLOSURE.md` for the complete attribution.

## What this release adds

This release proves **seven explicitly identified conjectural statements across four OEIS entries that were not included in version 1**: two in A396093, two in A389474, two in A389475, and one in A396102. The official entries still labeled these statements as conjectures when checked on 24 October 2026. This description records source status and package coverage; it does not assert worldwide novelty, exclusive priority, publication, or OEIS acceptance.

**Two of the seven assertions are direct applications of the standard Frobenius identity:** A389474 (4) and A389475 (4.a). They are counted as two covered source assertions, not as two new general mathematical principles. The other five assertions use the particular source series or defining equations. The construction and uniqueness theorems, stronger conclusions, and general families are also included, without inflating the count of separately identified OEIS conjectures.

The release additionally formalizes **seven named factorial Stirling-transform corollaries**. These are already covered by Payam Danesh's 2026 theorem and are **not counted as newly solved open problems**. They are catalogued separately below.

The fixed manifest in `validation/final_theorems.json` lists **130 required Lean endpoints**, including **all 67 endpoints from version 1**. An endpoint may express construction, uniqueness, source correspondence, a general theorem, a stronger corollary, or a regression check. Consequently, 130 is an audit count, not a count of distinct conjectures or mathematical discoveries.

## Conventions and source definitions

All power-series calculations are formal. A normalized series has constant coefficient zero and coefficient of `x` equal to one. Ordinary multiplication and ordinary powers are distinct from compositional iteration, denoted below by `G^{∘r}`. The identity iterate is `G^{∘0}(x)=x`.

| Entry | Exact source definition and indexing | Canonical Lean definition and source checks |
|---|---|---|
| [A396093](https://oeis.org/A396093) | `B(x)=x/(1−x)²`, `A(x)=B(B(B(x)))`, `a(n)=[xⁿ]A(x)`; source offset 0 and `a(0)=0` | `RationalParity.B = X * geom 1 ^ 2`; `RationalParity.A = iter B 3`; `RationalParity.a n = coeff ℤ n A`. `B_denominator` proves the exact denominator identity, and `A_definition` displays the three compositions. |
| [A389474](https://oeis.org/A389474) | Unique normalized integer series satisfying `A(x²+2x³+2A(x)²)=3A(x)²`; source offset 1 | `More.CubicReversion.a389474`, the genuine compositional inverse of `cubicSolution 1`. The literal source equation, normalization, existence, and uniqueness are proved by `a389474_equation`, `a389474_normalized`, `a389474_existence_uniqueness`, and `a389474_unique`. |
| [A389475](https://oeis.org/A389475) | Unique normalized integer series satisfying `A(3x²)=2x²+A(x)²−2A(x)³`; source offset 1 | `More.CubicReversion.a389475 = cubicSolution (−1)`. The literal source equation, normalization, existence, and uniqueness are proved by the corresponding `a389475_equation`, `a389475_normalized`, `a389475_existence_uniqueness`, and `a389475_unique` endpoints. |
| [A396102](https://oeis.org/A396102) | Unique normalized integer series satisfying `A(A(A(x)))=(1+x)A(A(x))`; source offset 1 | `InverseIterate.A396102 = F 3`. `F` is the genuine compositional inverse of the uniquely constructed auxiliary series `R`. `a396102_definition` proves the literal source equation, `a396102_unique` proves uniqueness, and `F_original_existence_uniqueness 2` supplies existence and uniqueness for precisely the threefold-composition equation. |

For A389474 and A389475, `cubicSolution s` is constructed over the integers from

\[
R_s(3x^2)=2x^2+R_s(x)^2+2sR_s(x)^3.
\]

Every division by two in its coefficient recursion is proved exact, using the evenness of the residual. The modular assertions therefore apply to actual integer series whose existence has been proved.

For A396102, the auxiliary series is constructed over the integers from

\[
R_r=x-R_rR_r^{\circ r},\qquad F_r=R_r^{-1}.
\]

The original-equation theorem uses a natural parameter `r+1` to express positivity without truncated subtraction: `F_original_existence_uniqueness r` proves uniqueness of a normalized solution of `G^{∘(r+1)}=(1+x)G^{∘r}`. Thus the source equation for A396102 uses this theorem at `r=2`, while the canonical series is `F 3`.

## The seven new-to-package source assertions

Every coefficient and parameter range in the following table is universally quantified in Lean. No finite coefficient table is an assumption of any endpoint.

| No. | Source assertion and exact range | Fully qualified Lean endpoint | File and proof classification |
|---|---|---|---|
| 1 | **A396093, first conjecture:** `a(2n)` is even for `n ≥ 1`. The formal theorem additionally includes `n=0`. | `RationalParity.a396093_even_indices` | `lean/More/RationalParity.lean`; deduction from the exact reduced rational series. |
| 2 | **A396093, second conjecture:** for every `n ≥ 1`, `a(2n−1)` is even if and only if there is an integer `k ≥ 1` with `n=5k−2`. | `RationalParity.a396093_odd_indices_original` | `lean/More/RationalParity.lean`; exact source formulation, with both positivity conditions preserved. Lean uses natural `n,k`, equivalent to positive integer `n,k` here. |
| 3 | **A389474 (3):** `[xⁿ]A(x)² ≡ 0 (mod 9)` for every `n > 3`. | `More.CubicReversion.a389474_conjecture_3` | `lean/More/CubicConsequences.lean`; deduction from the source equation by compositional inversion at a square-zero argument modulo nine. |
| 4 | **A389474 (4):** `[xⁿ](A(x)^(3k)−A(x³)^k) ≡ 0 (mod 3)` for `n ≥ 1`, `k ≥ 1`. The formal theorem proves it for every `n,k ≥ 0`. | `More.CubicReversion.a389474_conjecture_4` | `lean/More/CubicConsequences.lean`; **standard universal Frobenius consequence**, valid for any integer formal series. |
| 5 | **A389475 (4.a):** `A(x)³ ≡ A(x³) (mod 3)` as an entire series, equivalently at every coefficient index `n ≥ 0`. | `More.CubicReversion.a389475_conjecture_4a`; whole-series endpoint `More.CubicReversion.a389475_cube_mod_three` | `lean/More/CubicConsequences.lean`; **standard universal Frobenius consequence**, valid for any integer formal series. |
| 6 | **A389475 (4.b):** `A(x)² ≡ x²+2A(x³) (mod 3)` as an entire series, equivalently at every coefficient index `n ≥ 0`. | `More.CubicReversion.a389475_conjecture_4b`; whole-series endpoint `More.CubicReversion.a389475_square_mod_three` | `lean/More/CubicConsequences.lean`; deduction from this series' source equation in characteristic three, followed by Frobenius. |
| 7 | **A396102, displayed conjecture:** `a(n) ≡ 1 (mod 3)` for every `n ≥ 1`. | `InverseIterate.a396102_congruence` | `lean/More/InverseIterate.lean`; deduction from the canonical inverse family and its exact reduction to `x/(1−x)` modulo the family parameter. |

These endpoints correspond to the assertions in the comments of A396093 and A396102 and the numbered formulas of A389474 and A389475. The source URLs in the preceding table provide the precise definitions and conjecture statements. Targeted prior-art searches are documented in the individual review files; their scope does not justify a global priority claim.

### Stronger conclusions and general theorems

The package also proves the following statements. They are not counted again as additional independently identified OEIS conjectures.

- **Complete A396093 parity pattern:** `RationalParity.a396093_residue` proves that `a(n)` is odd exactly for `n ≡ 1,3,7,9 (mod 10)`, for every `n ≥ 0`. The underlying entire-series identity is `A(x)(1+x¹⁰)=x+x³+x⁷+x⁹` over `𝔽₂`, proved by `third_period_denominator`.
- **Complete A389474 square identity:** `More.CubicReversion.a389474_square_mod_nine` proves `A(x)² ≡ x²+2x³ (mod 9)`, including the exact low-degree terms.
- **Prime-characteristic Frobenius:** `More.CubicReversion.frobenius_substitution`, in `lean/More/CubicFrobenius.lean`, proves `U(x)^p=U(x^p)` for every prime `p` and every series over `ZMod p`. This formalizes a standard theorem.
- **Integral cubic family:** `More.CubicReversion.existence_uniqueness`, in `lean/More/CubicReversion.lean`, constructs the unique normalized integer solution for every integer parameter `s`, with no existence or integrality assumptions left unproved.
- **Inverse-iterate family:** `InverseIterate.F_original_existence_uniqueness` proves the source-family construction for every positive parameter. `coefficient_congruence` proves `[xⁿ]F_r ≡ 1 (mod r)`, and `iterate_coefficient_congruence` proves `[xⁿ]F_r^{∘k} ≡ k^(n−1) (mod r)` for every positive coefficient index and every natural iterate `k`. The meaningful modulus formulation uses `r ≥ 1`; the formal auxiliary construction also allows `r=0` under Mathlib's `ZMod 0` convention.

## Seven Stirling corollaries: formalized prior results

These results are separated from the seven source assertions above because their mathematical content is already covered by prior work.

Payam Danesh, *Eventual periodicity of weighted Stirling transforms and two conjectures of Bala*, version 1, **26 August 2026**, proves the general integral-substitution result in Theorem 4.1 and Corollary 4.2. The paper gives the stronger universal eventual **Carmichael period** `λ(m)` for integral substitutions `G(eˣ−1)`. The source is [Cambridge Open Engage](https://www.cambridge.org/engage/coe/article-details/6a883d7ed1922e37d58bbed1), DOI [10.33774/coe-2026-4d6jr](https://doi.org/10.33774/coe-2026-4d6jr). The totient-period conclusions for all seven specializations below follow from that existing theorem. Retained conjecture wording in an OEIS entry does not override this prior proof.

The present Lean development proves the explicit finite-transform theorem

\[
T_c(n)=\sum_{k=0}^{n}c_k k!S(n,k),\qquad
T_c(n+\varphi(m))\equiv T_c(n)\pmod m
\quad(m\ge1,\ n\ge m),
\]

for every integer weight sequence `c : ℕ → ℤ`, without sign or growth restrictions. It proves that the least positive period of the tail beginning at `m` exists, is a period, is minimal among positive tail periods, and divides `φ(m)`. The starting index `m` is a sufficient bound; optimality is not claimed. The Lean theorem proves the totient bound, not Danesh's stronger Carmichael bound.

Definitions are in `lean/More/StirlingTransform.lean`. All period and least-period endpoints below are in `lean/More/StirlingPeriodicity.lean`. All seven source sequences have offset zero.

| OEIS entry | Exact integer weight `c_k` in the finite transform | Named period endpoint | Named least-period endpoint |
|---|---|---|---|
| [A052895](https://oeis.org/A052895) | Catalan number `C_k` | `More.Stirling.A052895_period` | `More.Stirling.A052895_leastPeriod_dvd` |
| [A064618](https://oeis.org/A064618) | `k!`, giving summands `(k!)²S(n,k)` | `More.Stirling.A064618_period` | `More.Stirling.A064618_leastPeriod_dvd` |
| [A354242](https://oeis.org/A354242) | Central binomial coefficient `binomial(2k,k)` | `More.Stirling.A354242_period` | `More.Stirling.A354242_leastPeriod_dvd` |
| [A167137](https://oeis.org/A167137) | Number of integer partitions of `k` | `More.Stirling.A167137_period` | `More.Stirling.A167137_leastPeriod_dvd` |
| [A305550](https://oeis.org/A305550) | Number of partitions of `k` into distinct positive parts | `More.Stirling.A305550_period` | `More.Stirling.A305550_leastPeriod_dvd` |
| [A306082](https://oeis.org/A306082) | Number of partitions of `k` into positive square parts | `More.Stirling.A306082_period` | `More.Stirling.A306082_leastPeriod_dvd` |
| [A080253](https://oeis.org/A080253) | `A001333(k+1)`, defined by `c₀=1`, `c₁=3`, `c_(k+2)=2c_(k+1)+c_k` | `More.Stirling.A080253_period` | `More.Stirling.A080253_leastPeriod_dvd` |

Each `Axxxxxx_period` endpoint has the range `m ≥ 1`, `n ≥ m`. Each `Axxxxxx_leastPeriod_dvd` endpoint concerns the least period of `t ↦ a(m+t) mod m`, for `m ≥ 1`. These are unbounded theorems, not assertions restricted to the finite moduli checked by Python.

The universal endpoints are `More.Stirling.transform_totient_period`, `More.Stirling.transform_eventually_periodic`, and `More.Stirling.transform_exact_tail_period`. Supporting proofs are in `lean/More/PowerPeriodicity.lean`, `lean/More/StirlingNumbers.lean`, `lean/More/StirlingTransform.lean`, and `lean/More/TailPeriodicity.lean`. Attribution for adapted upstream Stirling-number code is preserved in `third_party/mathlib/NOTICE.md`.

### Exact boundary of the generating-function formalization

The standard formal identity

\[
(e^x-1)^k=k!\sum_{n\ge k}S(n,k)\frac{x^n}{n!}
\]

identifies the finite transform with the exponential generating coefficients of `G(eˣ−1)` when `G(t)=Σ c_k t^k`. This identity and its use in identifying exponential generating functions are explained in prose in `docs/STIRLING_PERIODICITY.md`.

**The formal-exponential-series substitution identity is not separately formalized in this release.** The Lean universal theorem is about the explicitly defined finite sum `More.Stirling.transform`. The seven named applications use the source entries' finite Stirling formulas directly, so they do not take an unproved EGF-identification proposition as a Lean assumption. This distinction is part of the formal coverage and must remain visible when reporting the result.

## Retention of version 1 and the fixed 130-endpoint manifest

The current manifest explicitly retains every one of version 1's 67 required endpoint names. The old and new groups are:

| Manifest group | Required endpoints | Status in this release |
|---|---:|---|
| `construction_and_natural_iterates` | 9 | Retained from version 1 |
| `integer_iterates` | 7 | Retained from version 1 |
| `a396099_all_four` | 8 | Retained from version 1 |
| `a396798` | 12 | Retained from version 1, including the source counterexample and corrected period |
| `a396807` | 3 | Retained from version 1 |
| `scaled_inverse_family` | 12 | Retained from version 1 |
| `hanna_regression` | 16 | Retained original A396843-family regression checks |
| **Version 1 subtotal** | **67** | **All retained** |
| `a396093_rational_parity` | 8 | Added in version 2 |
| `cubic_reversion` | 19 | Added in version 2 |
| `known_stirling_periodicity_formalization` | 21 | Added formalization of already covered mathematical results |
| `a396102_inverse_iterate` | 15 | Added in version 2 |
| **Version 2 additions** | **63** | **Explicitly listed, including supporting endpoints** |
| **Current required total** | **130** | **Fixed manifest audit target** |

This total was checked directly against `validation/final_theorems.json`, and the old 67-name set was read from the original archive's own manifest. The set difference of old names minus current names is empty. Fresh build, semantic-contract, and transitive-axiom evidence is generated by the package's complete validator; the required list is fixed before inspecting its audit output.

The previous ZIP is preserved **verbatim**, as an archive inside this release:

```text
prior_work/oeis_congruence_proofs_Dev_Goyal_v1.zip
```

Its verified SHA-256 is

```text
04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c
```

The preserved file is 509,323 bytes. Its path and digest are recorded in the current manifest under `previous_archive`. Keeping the entire original ZIP preserves the earlier sources, manuscript, evidence, disclosures, and packaging exactly as delivered; the retained old endpoint names are also included in the current compilation and audit target.

## Verification evidence and limits

`lean/More/Contracts.lean` states separate typed checks for the intended definitions, original functional equations, index ranges, and unbounded conclusions. The whole-project `ContractChecks.lean` includes the earlier and added contracts. Compilation validates proof terms against those types; the transitive axiom audit separately excludes proof placeholders and additional axioms. Neither operation certifies historical priority or completed human review.

The independent arithmetic evidence is recorded in:

| Family | Checker | Evidence |
|---|---|---|
| A396093 | `scripts/verify_rational_parity.py` | `validation/rational_parity_numeric.json` |
| A389474 and A389475 | `scripts/verify_cubic_reversion.py` | `validation/cubic_reversion_numeric.json` |
| A396102 and its general family | `tests/check_inverse_iterate.py` | `validation/inverse_iterate_checks.json` |
| Seven Stirling specializations | `scripts/verify_stirling_periodicity.py` | `validation/stirling_numeric.json` |

These checks compare source prefixes, independently computed definitions, functional equations, and bounded sets of congruences. They support the correspondence between source statements and code; the universal assertions are established by the Lean proofs.

Detailed arguments and source reviews are in `docs/RATIONAL_PARITY_REVIEW.md`, `docs/CUBIC_REVERSION.md`, `docs/INVERSE_ITERATE.md`, and `docs/STIRLING_PERIODICITY.md`. This coverage ledger does not claim results for other conjectures on the cited pages, such as separate integrality or continued-fraction questions, nor for analytical values or coefficient nonnegativity beyond what is explicitly proved. No OEIS submission or publication action is represented as having been performed.
