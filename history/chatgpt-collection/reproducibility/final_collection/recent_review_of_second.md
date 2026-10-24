# Independent AI review of the second-group separate entries

**Status: passed after two exposition clarifications.**

Reviewer: ChatGPT agent `final_recent_entries`, separate from the agent who prepared these eleven manuscripts and entry files. This is an AI-assisted semantic review, not independent human peer review. Human review remains pending.

## Material reviewed

The eleven complete standalone TeX manuscripts, their complete explicit Lean entry files, and `catalogue/second_entries.json` were read and compared with the retained `manuscript/further_oeis_proofs.tex`, `docs/ROUND2_COVERAGE.md`, the relevant implementation theorem types, and `third_party/mathlib/NOTICE.md`. The reviewed definitions are those in the supplied project; this review does not represent a new internet search or establish current worldwide openness.

All 70 declared entry theorems occur in the catalogue in their source-file order. Each has an explicit proposition type and a proof term. The combined checker, rather than this prose review, is responsible for fresh source compilation and transitive axiom audits.

## Findings by entry

| Entry | Checked mathematical correspondence | Finding |
|---|---|---|
| A396093 | Actual third iterate of `x/(1-x)^2`; characteristic-two denominator `1+x^10`; odd residues 1,3,7,9 modulo 10; even-index result including zero; positive `n,k` in the `2n-1`/`5k-2` statement | Exact agreement. The denominator is a unit; no invalid ring cancellation is used. |
| A389474 | Integral cubic family with exact division by two; reversion at parameter 1; literal source equation; square identity modulo 9; full coefficient range and ordinary powers in the Frobenius consequence | Exact agreement. The modulus-nine proof uses a square-zero argument and no division by three. |
| A389475 | Parameter -1 of the constructed cubic family; literal source equation; full cubic and quadratic identities modulo 3 | Exact agreement. The universal Frobenius identity is labeled standard; the quadratic identity separately uses the source equation. |
| A396102 | Unique normalized triple-composition source; inverse-family construction; both inverse directions; positive-index coefficients; zeroth natural iterate; source parameter `r+1` versus canonical family index `r` | Exact agreement. The prose now includes the normalized inverse construction and its two-sidedness argument. The mathematical modulus theorem is stated for positive parameters; the `ZMod 0` extension is clearly a formal convention. |
| A052895 | Catalan weight, starting at `C_0=1`; complete finite sum; period onset and least-period statement | Exact agreement. The generating series is now defined at its first occurrence. |
| A064618 | Factorial weight, so the summand contains `(k!)^2`; offset zero | Exact agreement. No analytic convergence of the factorial series is assumed. |
| A354242 | Central binomial weight; offset zero; separate continued-fraction question excluded | Exact agreement. |
| A167137 | All integer partitions into positive parts; empty partition at zero; unrelated power/logarithm integrality excluded | Exact agreement. |
| A305550 | Distinct positive parts; empty partition at zero | Exact agreement. |
| A306082 | Positive square parts; the Lean filter `sqrt j * sqrt j = j` is explicitly exposed in the entry | Exact agreement. |
| A080253 | Weight recurrence `1,3,7,17,...`; essential `A001333(k+1)` shift; numerator `(1+t)` in the weight generating series | Exact agreement. Weight boundary values and recurrence are explicit Lean theorems. |

## Shared Stirling argument

The universal proof, EGF explanation, and attribution sections are repeated verbatim in all seven Stirling manuscripts. Their respective SHA-256 values, independently compared across the seven files, are:

- Universal proof: `4bbc69b21c409a516c138eb3e7be4153eaf15a9c9db6bd9e16945971f2bf3432`.
- EGF explanation: `a96668a7e0b21a8938579313cc41a32daaeaab34493d592593c59d69852fffc2`.
- Attribution: `ea802c0bb819f81f24bb5bf3f5a55b1f2c305ba9573baf067361dabb006793c0`.

The power congruence is justified prime power by prime power. The bound `n >= m` kills nonunit powers; Euler's theorem handles units. The triangular falling-factorial expansion then transfers the congruence to `k! S(n,k)` for `k < m`. All terms with `k >= m` vanish modulo `m`. There is no cancellation of factorials in a residue ring. The case `m=1` and positivity of the least period are explicitly handled. The Euclidean-division argument proves that the least positive period of the tail beginning at `m` divides Euler's totient.

The finite weights in all seven entry files match the manuscript definitions and the retained source ledger. The EGF substitution identity is mathematically explained in prose and **explicitly excluded from the separately formalized Lean coverage**. No Lean theorem assumes an unspecified OEIS sequence agrees with a postulated residue pattern.

## Attribution and scope

All seven Stirling applications are classified as formalizations of known results. Danesh's Theorem 4.1 and Corollary 4.2, DOI `10.33774/coe-2026-4d6jr`, receive credit. The stronger Carmichael-period conclusion is distinguished from the totient theorem actually formalized. The sufficient onset `n >= m` is not called optimal. Earlier Schreyer work and the adapted Apache-2.0 Mathlib source, authors, revision, and retained license are identified consistently with the project notice.

The four non-Stirling papers retain their precise source status and distinguish direct standard Frobenius consequences from sequence-specific reasoning. All manuscripts identify Dev Goyal as the sole human author, disclose ChatGPT's contribution, state that independent human review is pending, and avoid publication, acceptance, or global-priority claims.

## Resolved review comments

1. A396102 originally invoked the standard normalized compositional inverse directly. A short coefficient recursion and associativity proof has now been added, making the standalone paper more self-contained. The Lean source and results did not change.
2. A052895 now defines `G(t) = sum C_k t^k` at its first occurrence. This was a notation clarification, not a mathematical change.

No remaining mathematical or source-to-formal mismatch was found. This review does not reclassify the seven known-result formalizations as newly solved open problems and does not substitute for the final compiler report.

## Reviewed source hashes

The hashes below fix the reviewed final TeX and Lean sources. PDF rendering/visual review is recorded independently in `second_pdf_qa.json` by the preparing agent.

| Entry | TeX SHA-256 | Lean SHA-256 |
|---|---|---|
| A396093 | `5a9a932c2d18c4fd0d0d8e248cc4d53b3719f16a232298501e6248070e58c65d` | `b254fcf7b82422e10401f0ed7288e439e3f6a8a8229f1568b0d4f245486460b9` |
| A389474 | `7fd0bff203c335a520d1170fc0c614a621105e0687853e1e69486fbef0010290` | `c12ebaed1d27c8a020472141a6ad041fddb0823e3ccb792e2db97e8a433182ec` |
| A389475 | `ff3ebf8100f226599a2a0a555055df94e9fc3708df4e0602a73721128c2ea540` | `bb03dc2f8127c2f863b935818a883fe3355a334eedcdc4e01a51c822ac6097c1` |
| A396102 | `f77606a4ed9da98d59c10c77bf1071c1894fa8fcfaa7d2d7da6c63e79d7748ed` | `7c0c813ab08f848f164464a174c150769753a43bc673b0093a0e775def38ae48` |
| A052895 | `a2684aca3b25846df25d94489aa1f47348476aa62110f10064cb800dd98ae7c3` | `198ae74be1aec15f138bf97a10634dcdc2b3e48097f428fcdfc0168018283693` |
| A064618 | `62b3fcfccc44572c0a667e3f4fbdfe60c9b29a1310ea5337f8528651026346be` | `bda6a09cf77677bccee98fe345573262f10152f2a331f182157ea3096106659f` |
| A354242 | `7a6690b81bde039217ed4850a7650e4665dcb874ce4116ff2647a4ee632c44d6` | `4cf255356753d9cefd072d42f4c4bd325265564e71390010f8305ce7cd92b596` |
| A167137 | `f00470562de489ae8dc566cd399f79ceab374ae6ffd127783d69ad9e82ee13dc` | `1ebd85691c84b6721f97beb74f946d992c917d9723b82f013a78a69d9a664b27` |
| A305550 | `0280d2ba222423efff8935ea80ec213e5c855e85d151f783cd376f31621c0d39` | `d034e67b064c8c47eda44ed63334328da0ecd66f8725aeef3914632e18e4be48` |
| A306082 | `4b3bf653fe71711bcc1690e0c1d0ced30bbb0143cbc3aa87c1ef8294f92f0e1c` | `96f4d19a0b01c418562f53f8767e2287ba0170a770bd136c41728341ed9347a7` |
| A080253 | `01618cebf3f67b435d7ec73b6599005638eb3a3e156e46e7567597a8e8402c08` | `b6e010f9fd4e61873e08e3f68705868febae235f3cc1c76c0d236746b148f03a` |

Completed UTC: 2026-10-24T18:41:34.600086+00:00.
