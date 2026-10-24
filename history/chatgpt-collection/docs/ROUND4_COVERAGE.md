# Round 4: exact source and theorem coverage

**Dev Goyal; prepared 24 October 2026. AI-generated proofs and reviews. Independent human review is pending.**

This round proves six explicit conjecture statements in five source entries. It also refutes a false conjecture comment and supplies a corrected theorem, and formalizes one elementary observation. These categories are separate from the 113 additional formal endpoints and the cumulative 339-endpoint audit.

## Source ledger

All sources below are official OEIS pages retrieved on 24 October 2026, credited to Paul D. Hanna. The raw offset retains both components printed by OEIS; the first is the starting index.

| Entry | Source author date | Raw offset | Selected assertion and status |
|---|---|---|---|
| [A195194](https://oeis.org/A195194) | 11 September 2011; parity comment 7 April 2026 | `1,3` | Explicit conjecture: odd exactly at powers of two. |
| [A393172](https://oeis.org/A393172) | 4 February 2026 | `1,2` | Explicit conjecture: for n>1, residue two modulo four exactly at powers of two, otherwise divisible by four. |
| [A393171](https://oeis.org/A393171) | 4 February 2026 | `1,3` | Explicit conjecture: for n>2, residue four modulo eight at n=2^k or 2^k+1, k≥1, otherwise divisible by eight. |
| [A380056](https://oeis.org/A380056) | 28 January 2025 | `1,3` | Two explicit conjectures: a(n)=1 modulo four for n≥1; five divides a(4n) for n≥1. |
| [A380060](https://oeis.org/A380060) | 6 February 2025 | `0,2` | Explicit conjecture: for n>0, residue two modulo four exactly at squares, otherwise divisible by four. |
| [A380680](https://oeis.org/A380680) | 6 February 2025 | `0,2` | False explicit square-support conjecture. Exact counterexamples a(1)=4 and a(2)=6. Corrected support is twice a positive square. |
| [A392210](https://oeis.org/A392210) | 2 February 2026 | `1,3` | Source says it appears that a(2n−1) is even for n>1. Proved as an elementary square consequence, outside the six-conjecture count. |

## Definitions and formal endpoints

### A195194: actual infinite nested reversion

`Round4.NestedReversion` constructs, for every commutative ring and weight function, the unique family of normalized series whose j-th tail is the genuine compositional inverse of `X−w(j) X F_(j+1)`. Both inverse identities are included. The specialization uses `w(j)=j+1` and tail zero, so the first weight is one. `approximation_agrees` proves depth d agrees through degree d+1. `a195194_parity` quantifies over all natural indices and includes the source range n≥1.

Fixed fragment: `validation/round4_nested_endpoints.json` (18 endpoints). Explicit contracts: `lean/Round4/NestedContracts.lean`.

### A393172 and A393171: exact source equivalences and lifting

Let `C=X+C²` be the canonical normalized series and `N=X−X²`. Their two-sided inverse relation is proved. `Round4.SquareComposition` constructs the unique normalized `G=T+(G∘P)²` over every commutative ring.

`Round4.CatalanComposition` proves the literal A393172 equation `A∘N=X+A²` and its equivalent contraction. It proves `A=2C−X` modulo four and the exact coefficient classification for n>1. For A393171 it proves both `B=X+(B∘C)²` and `B∘N=N+B²`, together with `B=X+A²` and `B∘C=A`. Exact integer divisibility of `A−(2C−X)` by four precedes the modulus-eight expansion. The classification retains n>2 and k≥1. Neither sequence is introduced by assuming a conjectural congruence.

### A392210: separate elementary observation

`Round4.NestedBinomial` uses the genuine quotient `X/(1−X)` and constructs the unique normalized solution `D=X+(D∘(X/(1−X)))²`. It proves every odd-index coefficient after one is even. The formal source is formula (1); no analytic interpretation of the nested title is required. This is an elementary characteristic-two consequence, not a new principle about squaring.

These three entries share `validation/round4_catalan_endpoints.json` (39 endpoints) and `lean/Round4/CatalanContracts.lean`.

### A380056: exponential coefficient semantics

`Round4.ExpCosine.a` is an integer sequence with the auxiliary value a(0)=0. Its binomial-convolution recursion is uniquely solvable. `A=egf a` has rational coefficient a(n)/n!; the proof identifies its cosine factor with Mathlib's cosine rescaled by two and establishes the literal quotient `(exp−1)/cos(2X)`, uniqueness, and factorial recovery.

The modulus-four result covers n>0. The modulus-five result proves `a(n)=2·2^n+3·4^n` in ZMod5 for all n≥0, the complete period-four pattern, and `5 | a(n)` iff `4 | n`. These concern exponential coefficients, not ordinary rational coefficients. Factorials are not inverted in characteristic five.

Fixed fragment: `validation/round4_exp_cosine_endpoints.json` (25 endpoints). Explicit contracts: `lean/Round4/ExpCosineContracts.lean`. A380555 reversion, analytic asymptotics, and convergence are not claimed.

### A380060 and A380680: locally finite positive source sums

`Round4.ThetaRational` defines `Q_j(U)=(U−X^j)/(1−X^j U)` for j≥1 using a proven constant-one unit. `Sigma(U)=sum_(j≥1) X^(j²) Q_j(U)^j` is locally finite. The finite coefficient expression is proved equal to the corresponding coefficientwise infinite sum.

The formal source is **formula (2)** of each entry: `A=1+2Sigma(A)` for A380060 and `B=1+2Sigma(2)` for A380680. The unique implicit solution is constructed over every commutative ring. The explicit solution is defined by the actual rational-sum formula. Source equations, quotient identities, full coefficient formulas, all-index congruences, and complementary integer-divisibility statements are endpoints.

For A380680, `a380680_literal_conjecture_false` negates the square-support iff and `a380680_nonsquare_clause_false` negates the nonsquare-divisibility clause. `a380680_coeff_one` and `a380680_coeff_two` prove 4 and 6 exactly. `a380680_corrected_congruence` has support twice a positive square. The false original claim is not counted as proved.

Fixed fragment: `validation/round4_theta_rational_endpoints.json` (31 endpoints). Explicit contracts: `lean/Round4/ThetaRationalContracts.lean`. A separate formal Laurent-series equivalence to the bilateral titles, special real values, and analytic convergence are outside the claimed coverage.

## Prior-art checks and limits

Current official pages displayed the statuses above. Exact identifier and defining-equation searches with proof/congruence/parity terms were made with both search engines. Relevant retrieved neighboring entries were inspected. No applicable earlier proof of the six selected conjecture statements was identified. Absence of a search result does not establish absence of prior work.

Checks also covered the available [awesome-ai-proofs catalogue](https://github.com/subroy13/awesome-ai-proofs) and the primary [OEIS theorem mapping](https://github.com/google-deepmind/formal-conjectures/blob/auto_oeis/FormalConjectures/OEIS/Auto/THEOREM_MAPPING.txt) linked from [AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results). None of the seven identifiers matched the inspected pages. The mapping includes attempted formalizations, not just successful proofs, and is not a complete literature catalogue. It was used only as a bounded cross-check.

A282779 was excluded after identifying prior AlphaProof Nexus work. Earlier exclusions and known-result credits remain: Amol Bhave's positive-iterate proof in A196523, Payam Danesh's Stirling-periodicity results, and standard Frobenius consequences. No old result is counted again as a round-four solution. No worldwide openness, first discovery, or priority is asserted.

## Verification and preservation

The cumulative manifest contains all earlier 226 endpoints followed by 113 new endpoints. There are 65 first-party Lean modules plus the separately compiled root contract. The release checker forces source compilation into a new isolated directory, prints complete theorem types, and accepts only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. It reruns 13 numerical suites and 41 gate tests.

All 177 displayed main-sequence terms and 42 auxiliary-tail terms from this round are reproduced by exact checks. Each numerical report states its finite ranges and algorithms. These calculations support source correspondence; the formal statements have no finite upper index bound.

Every earlier proof module is retained byte-for-byte, the old root contracts remain a literal suffix after new imports, and all three prior ZIPs retain their delivered hashes. Four mathematical manuscripts are supplied with editable sources. The final verification report is authoritative for the actual execution outcome, source hashes, and theorem list.
