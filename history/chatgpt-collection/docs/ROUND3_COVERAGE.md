# Round 3: exact scope and source ledger

Prepared for **Dev Goyal**, 24 October 2026.

**AI disclosure.** ChatGPT (OpenAI) generated the proofs, Lean implementations, verification programs, and explanatory documents in this round at Dev Goyal's request. Paul D. Hanna is credited by OEIS for the six sequence entries and their conjectures. Separate AI agents reviewed mathematical meaning and source identification. Independent human review remains pending. This ledger does not assert publication, OEIS acceptance, or exclusive priority.

## The six added source claims

Every source below was retrieved from the official OEIS website on **2026-10-24**. Each target residue or parity assertion was explicitly labeled a conjecture in the entry's **COMMENTS** section at that retrieval. The dates in the second column are the entry author dates shown by OEIS, not dates assigned to this proof work.

Write `a(n)=[xⁿ]A(x)` for each entry separately, and set

\[
 \Theta(x)=1+2\sum_{j\ge1}x^{j^2}.
\]

| Official entry | Credited source author and entry date | OEIS OFFSET field | Normalization | Literal source equation |
|---|---|---|---|---|
| [A397588](https://oeis.org/A397588) | Paul D. Hanna; 2026-07-03 | `1,2` | `A=x+O(x²)` | `A=x+(xA²)'` |
| [A389536](https://oeis.org/A389536) | Paul D. Hanna; 2025-10-28 | `1,2` | `A=x+O(x²)` | `A(x²+2x³)=xA(x)` |
| [A389537](https://oeis.org/A389537) | Paul D. Hanna; 2025-11-03 | `1,3` | `A=x+O(x²)` | `A(A(x)−x)=A(x)²` |
| [A389542](https://oeis.org/A389542) | Paul D. Hanna; 2025-11-01 | `1,2` | `A=x+O(x²)` | `A(A(x)²−x²)=4A(x)³` |
| [A378580](https://oeis.org/A378580) | Paul D. Hanna; 2025-01-08 | `0,2` | `A(0)=1` | `A(x/A(x))=Θ(x)` |
| [A378581](https://oeis.org/A378581) | Paul D. Hanna; 2025-01-08 | `0,2` | `A(0)=1` | `A(xA(x))=Θ(x)` |

The first component of each OFFSET field is the initial sequence index. The first four sequences begin at index one; the formal definitions also include their zero constant coefficient. The theta sequences begin at index zero, where their coefficient is one. The quotient in A389536's entry title is cleared by multiplication by `x`; the same division-free equation appears explicitly in the entry's example. In A378580, division by `A` means its multiplicative unit inverse, justified by `A(0)=1`.

| Entry | Exact source range | Proved conclusion |
|---|---|---|
| A397588 | `n≥1` | `a(n)` is odd if and only if `n=2^k` for some integer `k≥0`. The formal theorem additionally includes `n=0`, where both sides are false. |
| A389536 | `n>1` | `a(n)≡2 (mod 4)` exactly when `n=2^k+1`, `k≥0`; otherwise `a(n)≡0 (mod 4)`. The complementary clause is also proved as integer divisibility by four. |
| A389537 | `n>2` | `a(n)≡2 (mod 4)` when `n=3·2^k`, `k≥0`, and `a(n)≡0 (mod 4)` otherwise. |
| A389542 | `n>1` | `a(n)≡2 (mod 4)` exactly when `n=2^k+1`, `k≥0`; otherwise `a(n)≡0 (mod 4)`. Integer divisibility by four is proved equivalent to the complementary index condition. |
| A378580 | `n>0` | `a(n)≡2 (mod 4)` exactly at square indices; at every positive nonsquare index, `4` divides `a(n)`. |
| A378581 | `n>0` | The same square-index residue and nonsquare divisibility pattern, for this different source sequence. |

Every index range in this table is unbounded. The square condition is written in Lean as `∃ k : ℕ, n=k^2`; under `n>0`, its witness is automatically positive. In all power-of-two conditions, `k` ranges over the natural numbers and includes zero.

## Source identification and canonical construction

Every sequence is constructed over the integers, proved to satisfy the literal source equation, and proved unique with the displayed normalization. None of the coefficient conclusions assumes the existence of an unidentified solution or defines the sequence by its desired residue pattern.

| Entry | Construction and source bridge | Source existence and uniqueness endpoint |
|---|---|---|
| A397588 | The differential operator `G ↦ x+(xG²)'` improves coefficient agreement; triangular recursion constructs its unique normalized fixed point. | `Round3.DifferentialParity.existence_uniqueness` |
| A389536 | Triangular recursion solves `xG−G(x²+2x³)=0`, with leading coefficient one at each step. | `Round3.MahlerParity.existence_uniqueness` |
| A389537 | Construct `R+R(x²)=x`, then take the genuine normalized compositional inverse. The converse bridge proves uniqueness for the original equation. | `Round3.LacunaryInverse.source_existence_uniqueness` |
| A389542 | Construct `L=x+L²−2xL(4x³)`, set `R=x−2xL`, and revert `R`. The integer inverse equation `R²+R(4x³)=x²` is equivalent to the source equation and has a unique normalized integer solution. | `Round3.SquareReversion.a389542_existence_uniqueness` |
| A378580 | Construct the general constant-one solution of `U(xU)=T`; apply it to `T=Θ⁻¹` and invert multiplicatively. The unit quotient is proved explicitly. | `ThetaSubstitution.a378580_source_existence_uniqueness` |
| A378581 | Construct normalized `G` from `G(G)=GΘ` by triangular recursion, then write `G=xA`. | `ThetaSubstitution.a378581_source_existence_uniqueness` |

The A389542 source uniqueness theorem is over the integers. Its modulo-four argument transports the integral construction and uses uniqueness of genuine compositional inverses; it does not assume uniqueness of the original source equation over `ZMod 4`.

The two theta series use actual multiplicative unit inversion (`PowerSeries.invOfUnit A 1`). The other reversion constructions use actual compositional inverses, with both inverse identities proved. These operations are kept mathematically distinct.

## Principal theorem endpoints and stronger statements

The endpoint names below occur in the corresponding explicit manifest fragments. The typed contract modules restate the source equations, normalizations, uniqueness claims, and exact unbounded conclusions with independently written proposition types.

### A397588

- Canonical source equation: `Round3.DifferentialParity.A_equation`.
- Exact parity conjecture: `Round3.DifferentialParity.a397588_parity`.
- Stronger characteristic-two equation: `Round3.DifferentialParity.A_mod_two_quadratic`, proving `A−A²=x` after reduction.
- Related source assertion: `Round3.DifferentialParity.A_mod_three` and `Round3.DifferentialParity.a397588_divisible_by_three`.
- Contracts: `Round3.ElementaryContracts`, including `differential_definition`, `differential_source_unique`, and `differential_parity`.

The entry separately states that `3` divides `a(n)` for `n>1`; it does **not** label that sentence a conjecture. We verify it through the stronger identity `A≡x (mod 3)`. It is an additional verified source assertion, not another newly solved conjecture.

### A389536

- Canonical source equation: `Round3.MahlerParity.A_equation`.
- Complete residue theorem: `Round3.MahlerParity.a389536_residue`.
- Explicit complementary divisibility: `Round3.MahlerParity.a389536_four_dvd_iff`.
- Whole-series comparison: `Round3.MahlerParity.A_mod_four`, proving `A=x+2xH` over `ZMod 4`, where `H−H²=x` and `H=x+O(x²)`.
- Contracts: `Round3.ElementaryContracts`, including `mahler_definition`, `mahler_source_unique`, `mahler_residue`, and `mahler_four_dvd_iff`.

The binary support of `H` modulo two gives the exact exceptional indices. The comparison series is proved equal to the canonical source solution by uniqueness.

### A389537

- Canonical source equation: `Round3.LacunaryInverse.A_equation`.
- Original-source uniqueness: `Round3.LacunaryInverse.A_unique`.
- Complete residue theorem: `Round3.LacunaryInverse.a389537_residue`.
- Initial reduction: `Round3.LacunaryInverse.A_mod_two`, proving `A≡x+x² (mod 2)`.
- Exact integer correction and its support: `Round3.LacunaryInverse.A_decomposition`, `H_mod_two_equation`, `H_mod_two`, and `H_mod_two_coeff`.
- Contracts: `Round3.LacunaryContracts`.

The correction is defined over the integers by the exact identity `A=x+x²+2H`. Its reduction modulo two has support precisely `3·2^k`. The proof establishes exact halving over the integers before passing to residue rings.

### A389542

- Canonical source equation: `Round3.SquareReversion.a389542_equation`.
- Original-source uniqueness: `Round3.SquareReversion.a389542_unique`.
- Complete residue theorem: `Round3.SquareReversion.a389542_residue`.
- Exact exceptional and complementary clauses: `Round3.SquareReversion.a389542_two_mod_four_iff` and `a389542_four_dvd_iff`.
- Whole-series comparison: `Round3.SquareReversion.a389542_series_mod_four` and `A_eq_R_mod_four`.
- Contracts: `Round3.SquareContracts`.

The auxiliary `R=x−2xL` is its own compositional inverse modulo four. Its coefficients follow from the power-of-two support of `L` modulo two.

### A378580 and A378581

All names in this paragraph have namespace `ThetaSubstitution`.

- Literal equations: `a378580_source_equation` and `a378581_source_equation`.
- Genuine quotient identity for A378580: `a378580_quotient_identity`.
- Whole-series reductions: `a378580_series_mod_four` and `a378581_series_mod_four`, each proving `A≡Θ (mod 4)`.
- Complete residue statements: `a378580_congruence` and `a378581_congruence`.
- Both source clauses: `a378580_square_iff`, `a378581_square_iff`, `a378580_four_dvd_iff`, and `a378581_four_dvd_iff`.
- Contracts: `Round3.ThetaContracts`.

The modulo-four substitution calculation is valid for any series `1+2S`; the final use of positive-square support identifies the coefficients of the particular theta series.

### Manifest and explanation files

The explicit endpoint fragments are:

- `validation/round3_elementary_endpoints.json` for A397588 and A389536.
- `validation/round3_lacunary_endpoints.json` for A389537 and the shared modulo-four transfer lemmas.
- `validation/round3_square_endpoints.json` for A389542.
- `validation/round3_theta_endpoints.json` for A378580 and A378581.

Full mathematical arguments appear in `docs/DIFFERENTIAL_AND_MAHLER_PARITY.md`, `docs/ROUND3_LACUNARY_INVERSE.md`, `docs/ROUND3_SQUARE_REVERSION.md`, and `docs/THETA_SUBSTITUTION.md`. Separate AI semantic review notes accompany the modules. The package-wide manifest and validation report determine the final integrated audit scope; this ledger does not infer proof coverage from an endpoint count.

## Bounded prior-art status

At retrieval, all six target coefficient statements were still explicitly called conjectures on their official entry pages. The pages linked coefficient tables; none linked a proof of these target assertions. Exact-identifier searches with “proof” or related terms, supplemented by defining-equation searches, did not identify a separate earlier proof. These observations document the search performed. They do not establish global openness, first discovery, absence of unpublished work, or priority.

The neighboring iterated-series claims in A378575 and A378576 were excluded from these additions. The proof comment by Amol Bhave, dated 2026-10-13, in [A196523](https://oeis.org/A196523) treats the family `A=x+xA^[l]` and congruences modulo `l−1` using `x/(1−x)`. The displayed theorem has different source equations from the theta substitution results here and does not directly state those results. This particular coverage check does not replace broader literature research.

The previously proved weighted Stirling periodicity results retained from the earlier package are not reclassified as newly solved conjectures in this round. No OEIS edit or submission was made as part of producing these files.

## Verification evidence and its limits

The infinite claims are Lean theorems with universally quantified natural indices. Canonical source construction, literal equation checks, and explicit acceptance contracts connect those theorems to the official entries. The axiom audits check transitive dependencies against the project's permitted standard axioms. Kernel verification of a formal proposition is distinct from source interpretation and historical-priority research.

Independent Python programs use exact integers to corroborate source coefficients and literal functional equations. Their finite ranges are not substitutes for the all-index theorems.

| Entry | Displayed source terms matched | Finite corroboration range |
|---|---:|---|
| A397588 | 20 | Differential identity and parity through degree 500; divisibility by three for `2≤n≤500`. |
| A389536 | 34 | Residues and Catalan comparison for `2≤n≤2050`; independently evaluated literal substitution through degree 81. |
| A389537 | 30 | Independent source recursion and inverse-series construction agree through degree 80; literal equations and residues checked in that range. |
| A389542 | 22 | Independent source and auxiliary-reversion constructions agree through degree 80; source and inverse equations checked through degree 81. |
| A378580 | 24 | Independent direct source and normalized constructions, literal equation, unit quotient, and residues checked through degree 64. |
| A378581 | 22 | Independent direct source and normalized constructions, literal equation, and residues checked through degree 64. |

The machine-readable numerical records are `validation/differential_mahler_numeric.json`, `validation/lacunary_inverse_numeric.json`, `validation/square_reversion_numeric.json`, and `validation/theta_substitution_numeric.json`.

## Nearby statements outside the proved scope

The results address the displayed coefficient conjectures and the expressly identified supporting or bonus theorems. Other observations in the source entries remain separate:

- **A389537 sign runs.** The entry observes that, after index seven, sign runs appear to have length nine or ten. No general theorem about that sign pattern is proved here.
- **A378580 convergence radius.** The entry asks for the radius of convergence. The formal-series construction and residue theorem do not answer that analytic question.
- **Analytic values and asymptotics.** The convergence-radius and real-evaluation claims in A389536, real-evaluation claims in A389542 and the theta entries, and the asymptotic formula in A397588 are not established by these formal proofs.
- **Other formulas in the entries.** Higher composition identities, infinite-product formulas, and every additional displayed transformation are covered only when explicitly stated in a theorem endpoint above. They are not included merely because they appear on the same OEIS page.

The formal work therefore proves six specific coefficient conjectures attached to six source sequences, together with their constructions and stated supporting results. It leaves the separate analytic and sign-pattern questions identified above unresolved.
