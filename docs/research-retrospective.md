# OEIS proof project: methods, outcomes, and unfinished questions

> **Editor's note (October 2026).** This report was written by **ChatGPT** (OpenAI, GPT-6 with Pro reasoning) on 24 October 2026, at the end of the research, from the project's own records. It is the main source for the story told in the [README](../README.md). It is reproduced here with only these changes: the author's name is given in full (Dev D. Goyal); links point to where the files now sit in this repository (mostly [`history/chatgpt-collection/`](../history/chatgpt-collection/)); and one sentence about link locations was adjusted to match.
>
> Two statements in it have since been overtaken by events:
>
> - It says that independent human review is pending. Dev D. Goyal has since verified the results. **No independent peer review has taken place.**
> - Section 9 says that no new Lean build was run while the report was written. Claude Opus 5.5, used with Claude Code, has since rebuilt the Lean project from source, re-run the axiom audit, and recomputed every sequence independently; see [verification/README.md](../verification/README.md).
>
> The counts in this report (for example "100 first-party modules", "601 audited declarations", "141 manuscript pages") describe ChatGPT's archive. The current repository rearranges the same material (101 Lean files including the contract file; 262 entry theorems plus 6 cited general theorems audited; rewritten papers), as described in the [README](../README.md).

**Prepared for:** Dev D. Goyal  
**Prepared:** 24 October 2026  
**Companion archive:** `OEIS_Final_Collection_Dev_Goyal.zip`  
**Report scope:** A retrospective of the completed collection and surviving exploration records.

**AI disclosure.** ChatGPT (OpenAI) generated this report from the saved manuscripts, Lean sources, coverage ledgers, research notes, and verification records. The proof developments and their final organization were also AI-generated in response to Dev D. Goyal’s prompts, subject to the historical, conjecture-author, prior-result, and upstream-code credits retained in the collection. Dev D. Goyal is the sole human author identified in the collection. Independent human review of the expanded collection remains pending.

## 1. What was achieved

The final collection contains **34 OEIS entry treatments**, each with a separate manuscript and Lean proof interface. Across the four expansion rounds, the coverage ledgers record **38 affirmative proofs of selected source conjecture statements and two refutations accompanied by corrected theorems**. These 40 selected statements or comments belong to **23 distinct OEIS entries**. The remaining delivered entries are inherited original work, formalizations of known results, or an elementary observation. [E1] [E2] [E3] [E4] [E5]

The surviving records also identify **seven additional entries that were screened and not included**. Thus, **at least 41 distinct entries have a documented completed-or-screened disposition**: 34 delivered and seven screened out. This is a lower bound on recorded exploration, not a count of 41 sustained proof attempts. Four exclusions appear in the final archive; three more appear in a retained scout note reproduced in Section 10.

No complete chronological log of every candidate, speculative approach, abandoned calculation, and failed Lean tactic is available in the records used for this report. Consequently, **the total number of proof-search attempts and the overall research success rate cannot be reconstructed reliably**. The completed collection is a selected set of successful mathematical outcomes, not a benchmark against a predefined sample of open problems.

### The principal counts

| Quantity | Recorded result | What it means |
|---|---:|---|
| Delivered OEIS entry treatments | **34** | Distinct OEIS identifiers with individual papers and Lean interfaces. |
| Selected expansion-round conjecture statements proved affirmatively | **38** | Counted using the source ledgers’ statement/comment units. |
| Selected expansion-round conjecture comments refuted and corrected | **2** | A396798’s starting phase and A380680’s square-support claim. |
| Distinct expansion-round target entries receiving either outcome | **23** | Several entries contain multiple statements; related entries share general proofs. |
| Formalizations explicitly classified as known results | **8 entries** | Seven Stirling-transform entries and A396797. |
| Additional elementary observation | **1 entry** | A392210. |
| Inherited original entry treatments | **2 entries** | A396843 and A396844. |
| Additional documented screening exclusions | **7 entries** | Prior work, source ambiguity, or no explicit conjecture in the retrieved entry. |
| Minimum documented delivery-or-screening inventory | **41 entries** | A lower bound, not an attempt denominator. |
| Required advertised final formal goals left unfinished | **0** | The final fixed verification requirements all passed. |
| Total sustained unsuccessful proof attempts | **Unknown** | No complete attempt log survives. |
| Independent human review of the expanded collection | **Pending** | AI review and Lean checking do not establish human peer review. |

Sources for the delivered counts are the catalogue, four coverage ledgers, and final verification reports. The screening evidence is itemized in Sections 6 and 10. [E1]–[E7]

**These figures do not mean “34 newly solved open problems” or “38 independent discoveries.”** Two of the 38 source statements are direct applications of the standard Frobenius identity. Eight delivered entries formalize known results. Several target statements are consequences of one shared theorem. A conjecture label on a retrieved OEIS page is evidence of that page’s wording, not proof of worldwide openness or priority.

## 2. How the successful outcomes are counted

### A disjoint partition of the 34 delivered entries

| Category | Count | Entries |
|---|---:|---|
| Entries with affirmative proofs of selected conjecture statements during the expansion rounds | **22** | A195194, A378580, A378581, A380056, A380060, A389474, A389475, A389536, A389537, A389542, A393171, A393172, A393856, A393857, A393858, A393859, A396093, A396099, A396102, A396798, A396807, A397588 |
| Additional entry whose selected conjecture was false, with a corrected theorem proved | **1** | A380680 |
| Formalizations of known results | **8** | A052895, A064618, A080253, A167137, A305550, A306082, A354242, A396797 |
| Elementary observation formally proved | **1** | A392210 |
| Original repository work preserved and separately organized | **2** | A396843, A396844 |
| **Total** | **34** | Each entry appears exactly once in this table. |

A396798 belongs in the first row because seven of its selected statements were proved; it also contains a refutation and correction. The inherited A396843 and A396844 work also contains corrected residue assertions. Therefore the one “correction-only” entry does not imply that the collection contains only one correction. [E1] [E2] [E6]

### The expansion rounds, by source statement

| Round | Affirmative proofs | Refuted comments | Exact breakdown |
|---|---:|---:|---|
| First expansion | **19** | **1** | A396099: 4; A396798: 7 plus 1 correction; A396807: 2; A393856: 2; A393857: 1; A393858: 2; A393859: 1. |
| Second expansion | **7** | **0** | A396093: 2; A389474: 2; A389475: 2; A396102: 1. |
| Third expansion | **6** | **0** | One selected coefficient conjecture each for A397588, A389536, A389537, A389542, A378580, and A378581. |
| Fourth expansion | **6** | **1** | A195194: 1; A393172: 1; A393171: 1; A380056: 2; A380060: 1; A380680: 1 refuted comment. |
| **Total** | **38** | **2** | **40 selected source statements/comments across 23 entries.** |

This accounting excludes inherited A396843/A396844 results, known-result formalizations, A392210’s elementary observation, construction and uniqueness lemmas, and additional stronger consequences. A397588’s divisibility-by-three property was already stated without a conjecture label, so it is not added to the six third-round conjectures. A380680 has two separately formalized negations of false clauses, but its source comment is counted once. [E2]–[E5]

## 3. The common mathematical approach

The work concentrated on **formal power-series congruences**, especially compositional equations whose coefficients are determined recursively. This was a tractable direction because substantial machinery from the original A396843 project could be reused.

The recurring proof structure was:

1. **Fix the exact sequence definition.** Record the generating function, normalization, coefficient convention, and starting index. Ordinary powers, compositional iterates, multiplicative inverses, and compositional inverses must remain distinct.
2. **Construct the actual source series.** Show that the coefficient of degree \(n\) is determined by earlier coefficients, or that the defining operation improves coefficient agreement. Prove existence and uniqueness.
3. **Reduce modulo the relevant integer.** Prove that reduction respects the construction, composition, and inverses being used.
4. **Identify a simpler reduced series.** Verify a rational, quadratic, or sparse comparison series in the reduced equation. Uniqueness identifies it with the reduced source series.
5. **Read off the coefficients.** Translate the reduced identity into the conjectured parity, residue classes, or divisibility statement, including exceptional low indices.
6. **Formalize and check the correspondence.** Lean proves the universally quantified statements. Separate exact computations check source terms and help expose indexing mistakes. Reviews compare the formal definitions with the mathematical papers.

This explains why one general argument could produce results for several entries. It also explains the limits: formal congruences generally do not determine coefficient signs, analytic convergence radii, or special values. The following summaries describe reproducible mathematical proof methods, rather than a reconstructed diary of unrecorded exploratory reasoning. [E2]–[E6]

## 4. How the proofs work, by family

The 34 entries are grouped into **14 explanatory families** below. This grouping is editorial; it is not a count of independent discoveries.

### 4.1. Original Hanna parameter family — A396843 and A396844

The normalized source equation is

\[
A_m\!\left(xA_m-mxA_m^2\right)=x^2,\qquad A_m=x+O(x^2).
\]

A triangular coefficient argument constructs the series and proves uniqueness. Reduction modulo two gives the parity classification for odd and even parameters.

For integers \(m\ge2\), the stronger residue theorem starts with an exact integer decomposition \(A_m=x+mC\). The source equation then gives

\[
xC+C(x^2)\equiv x^3\pmod m.
\]

The solution is sparse:

\[
C\equiv \sum_{j\ge0}(-1)^j x^{2^j+1}\pmod m.
\]

This yields the complete classification modulo \(m^2\), including the corrected modulo-nine and modulo-sixteen cases.

For binary divisibility, write \(A_m=xF\) and its compositional inverse as \(B_m=xG\). The source and inverse identities imply

\[
F=G(x^2)+mxF^2.
\]

Simultaneous induction, using binary digit-sum inequalities, proves divisibility by \(m^{s_2(n-1)}\) for the degree-\(n\) coefficients of both normalized series, for \(n\ge1\). The residue classification also identifies where the minimum prime exponent occurs. Zero coefficients are handled through divisibility and exact-exponent predicates, without pretending that zero has a finite valuation.

**Outcome:** the original parity theorem, parameter generalizations, inverse-coefficient divisibility, exact residues, and valuation consequences. These are inherited results, preserved and rechecked. [E8]

### 4.2. Consecutive compositional iterates — A396099, A396797, A396798, A396807

The family satisfies

\[
F_r=x+F_r^{\circ r}F_r^{\circ(r+1)},\qquad r\ge1.
\]

The central comparison uses

\[
T_k=\frac{x}{1-kx},\qquad T_a\circ T_b=T_{a+b}.
\]

After proving the source construction and uniqueness, the reduced iterates are identified modulo \(2r\). For odd \(r\), they are \(T_k\). For even \(r\), an additional term is necessary:

\[
F_r^{\circ k}\equiv
T_k+r\epsilon(r,k)\frac{x^4}{(1-x)^3}\pmod{2r},
\]

where \(\epsilon(r,k)=1\) precisely when \(r\) is even and \(k\) is odd. The calculation works because the correction coefficient is square-zero in the relevant even-parameter residue ring. The proof also constructs genuine inverse iterates, establishing the formula for negative as well as nonnegative \(k\).

**Outcome:** all four selected A396099 assertions; the known A396797 specialization; seven valid A396798 iterate assertions and a corrected phase; both A396807 assertions, including all integer iterates. A396797’s earlier proof is credited to Shiva Priyan Shanmuga Sundaram. [E2] [E9]

### 4.3. Scaled inverse family — A393856, A393857, A393858, A393859

For a positive integer \(q\), define the division-free scaling operator

\[
L_q(U)=\sum_{n\ge1}q^{n-1}[x^n]U\,x^n.
\]

The source equation is

\[
G_q(x-xL_q(G_q))=x.
\]

This gives a valid interpretation of the source’s apparent \(G_q(qx)/q\), even when division by \(q\) would be illegal in a residue ring.

Modulo \(q+1\), the parameter satisfies \(q=-1\), and \(x/(1-x)\) is the comparison solution. For even \(q\), reduction modulo two gives \(L_q(G_q)=x\), making \(G_q\) the inverse of \(x-x^2\). Its quadratic equation has coefficient support at powers of two.

**Outcome:** every positive coefficient is one modulo \(q+1\); for even \(q\), odd coefficients occur exactly at powers of two. The specializations \(q=4,5,6,7\) prove six source assertions. [E2] [E9]

### 4.4. Rational third iterate — A396093

Let

\[
B=\frac{x}{(1-x)^2},\qquad A=B^{\circ3}.
\]

Direct rational-series calculation in characteristic two gives

\[
A(x)(1+x^{10})=x+x^3+x^7+x^9.
\]

The denominator has constant term one, so it has a formal inverse. Expanding that inverse shows that the odd coefficients occur exactly when

\[
n\equiv1,3,7,9\pmod{10}.
\]

**Outcome:** both source parity conjectures, with their original index conditions, follow from one complete classification. The proof concerns the actual threefold composition, not a sequence defined by the desired parity pattern. [E3] [E10]

### 4.5. Cubic reversion — A389474 and A389475

An auxiliary integer family satisfies

\[
R_s(3x^2)=2x^2+R_s(x)^2+2sR_s(x)^3.
\]

Its recursion appears to divide by two. The construction first proves that the relevant residual is even, so this division is exact over the integers. A389475 is the \(s=-1\) solution; A389474 is the compositional inverse of the \(s=1\) solution. Both source identifications are proved.

For A389474, write \(S=A^2\). Modulo nine, the argument \(3S\) is square-zero. Applying the genuine normalized compositional inverse to the source equation therefore gives

\[
S=x^2+2x^3\pmod9.
\]

Modulo three, Frobenius gives the cube identities; reducing A389475’s source equation supplies its square identity.

**Outcome:** four selected statements. **Two are standard Frobenius consequences**, not new general principles. Nonnegativity and analytic questions are outside these results. [E3] [E11]

### 4.6. Inverse-iterate family — A396102

The general source equation is

\[
F_r^{\circ r}=(1+x)F_r^{\circ(r-1)},\qquad r\ge1.
\]

The useful construction is for the genuine compositional inverse \(R_r\):

\[
R_r=x-R_rR_r^{\circ r}.
\]

This equation determines successive coefficients. The inverse identities prove its equivalence to the original equation.

Modulo \(r\), the comparison \(x/(1+x)\) has \(r\)-fold composition equal to \(x\). Uniqueness then gives

\[
F_r\equiv\frac{x}{1-x}\pmod r.
\]

**Outcome:** all positive A396102 coefficients are one modulo three, together with a parameter-family theorem and natural-iterate congruences. The different positive-iterate family already treated by Amol Bhave is credited separately. [E12]

### 4.7. Weighted Stirling transforms — seven entries

The entries are **A052895, A064618, A080253, A167137, A305550, A306082, and A354242**. Their common finite transform is

\[
B_c(n)=\sum_{k=0}^{n}c_k\,k!\,S(n,k),
\]

for arbitrary integer weights \(c_k\).

First prove eventual periodicity of scalar powers modulo a positive integer \(m\). A triangular power-expansion identity transfers the period to \(k!S(n,k)\). Terms with \(k\ge m\) vanish modulo \(m\), since \(m\mid k!\), so arbitrary integer weights preserve the period.

The result is

\[
B_c(n+\varphi(m))\equiv B_c(n)\pmod m
\quad(m\ge1,\ n\ge m).
\]

A separate minimal-period argument proves that the least positive period of that tail exists, is a period, and divides \(\varphi(m)\).

**Outcome:** seven precise formalizations of known results. Payam Danesh’s prior theorem, including its stronger Carmichael-period bound, is credited. The current Lean development proves the totient bound and sufficient onset, not the stronger bound or optimal onset. The EGF interpretation is proved in the manuscripts; its substitution identity is not separately formalized in Lean. [E13]

### 4.8. Differential and Mahler equations — A397588 and A389536

For A397588,

\[
A=x+(xA^2)'.
\]

Modulo two, the derivative of a square vanishes, reducing the equation to \(A=x+A^2\). Frobenius then gives a coefficient recurrence that halves the index. The odd coefficients occur exactly at powers of two. Modulo three, \(x\) itself solves the source equation, so uniqueness proves \(A\equiv x\).

For A389536,

\[
A(x^2+2x^3)=xA.
\]

Let \(C=x+C^2\). A comparison calculation and source uniqueness prove

\[
A\equiv x+2xC\pmod4.
\]

The power-of-two support of \(C\bmod2\) gives residue two exactly at \(n=2^k+1\), for \(n>1\).

**Outcome:** two coefficient conjectures. A397588’s additional divisibility-by-three statement is verified but was already stated nonconjecturally in the source. [E4] [E14]

### 4.9. Sparse inverse and square reversion — A389537 and A389542

For A389537, construct

\[
R+R(x^2)=x,\qquad A=R^{-1}
\]

with \(R^{-1}\) denoting compositional inversion. This is proved equivalent to the original source equation. After obtaining \(A=x+x^2\pmod2\), define the exact integer correction

\[
A=x+x^2+2H.
\]

The source equation gives \(\bar H+\bar H^2=x^3\) in characteristic two. Therefore \(\bar H\) has support \(3\cdot2^k\), yielding the modulo-four result for \(n>2\).

For A389542, construct

\[
L=x+L^2-2xL(4x^3),\qquad R=x-2xL,\qquad A=R^{-1}.
\]

These definitions imply the required integer source equation. Modulo two, \(L=x+L^2\). Modulo four, \(R\) is its own compositional inverse, so \(A\equiv R\), giving residue two exactly at \(2^k+1\), for \(n>1\).

**Outcome:** both complete modulo-four classifications. A389537’s observed coefficient sign runs remain unproved. [E15]

### 4.10. Theta quotient and product substitutions — A378580 and A378581

With

\[
\Theta=1+2\sum_{j\ge1}x^{j^2},
\]

the sources are

\[
A_-(x/A_-)=\Theta,\qquad A_+(xA_+)=\Theta.
\]

The formal construction establishes the source equations and uniqueness. The quotient uses the multiplicative inverse of a constant-one series, an operation distinct from compositional inversion.

Modulo four, substituting an argument congruent to \(x\) modulo two into an expression multiplied by two leaves that expression unchanged. This observation, together with \((1+2S)^2=1\pmod4\), identifies both reduced solutions with \(\Theta\).

**Outcome:** residue two exactly at positive square indices, and divisibility by four at positive nonsquares. The radius-of-convergence question for A378580 is not answered by this argument. [E16]

### 4.11. Infinite nested reversion — A195194

The displayed infinite nesting is made precise through a family of tails:

\[
F_j=\operatorname{Rev}(x-w_jxF_{j+1}),\qquad w_j=j+1.
\]

Equivalently,

\[
F_j=x+w_jF_jF_{j+1}(F_j).
\]

A simultaneous coefficient construction works because each degree depends on smaller degrees, even across different tails. It proves existence, uniqueness, both inverse identities, and a stabilization bound: a finite nest of depth \(d\) agrees through degree \(d+1\).

Modulo two, the second weight vanishes, giving \(F_1=x\). The first tail then satisfies \(F_0=x+F_0^2\).

**Outcome:** odd coefficients exactly at powers of two, with a more general construction for arbitrary weights. “Convergence” here means stabilization of each coefficient, not analytic convergence at a nonzero argument. [E17]

### 4.12. Catalan composition and an elementary square observation — A393172, A393171, A392210

Let \(C=x+C^2\), with compositional inverse \(N=x-x^2\).

For A393172, transform the source \(A(N)=x+A^2\) into a coefficient-determining equation and verify

\[
A\equiv2C-x\pmod4.
\]

For A393171, prove the source identities \(B=x+B(C)^2\) and \(B=x+A^2\). The modulo-eight proof needs the **exact integer lift** \(A=2C-x+4K\), after which squaring gives

\[
B\equiv x+x^2+4(C-x-xC)\pmod8.
\]

The binary support of \(C\) gives the exceptional indices \(2^k\) and \(2^k+1\), with the stated restrictions \(n>2\), \(k\ge1\).

For A392210,

\[
D=x+D\!\left(\frac{x}{1-x}\right)^2.
\]

A square in characteristic two has no odd-degree terms. Hence every odd-index coefficient after the first is even.

**Outcome:** two source conjectures and one separately labeled elementary observation. [E18]

### 4.13. Exponential/cosine coefficients — A380056

The source uses exponential coefficients:

\[
\sum_{n\ge0}a(n)\frac{x^n}{n!}
=\frac{e^x-1}{\cos(2x)}.
\]

The proof works with integer sequences under **binomial convolution**, rather than trying to invert factorials modulo five. It also formally identifies the constructed rational EGF with the literal quotient.

Modulo four, the positive-degree cosine coefficient sequence vanishes. Modulo five, the sequences \(E_s(n)=s^n\) satisfy

\[
E_s\star E_t=E_{s+t}.
\]

Verifying \(2E_2+3E_4\) in the convolution equation and using uniqueness gives

\[
a(n)\equiv1\pmod4\quad(n\ge1),\qquad
a(n)\equiv2\cdot2^n+3\cdot4^n\pmod5.
\]

**Outcome:** both selected conjectures, strengthened to \(5\mid a(n)\) exactly when \(4\mid n\). No result for the separate reversion sequence A380555 is claimed. [E19]

### 4.14. Rational theta sums — A380060 and A380680

Define

\[
\Phi(U)=1+2\sum_{j\ge1}x^{j^2}
\left(\frac{U-x^j}{1-x^jU}\right)^j.
\]

The source definitions are \(A=\Phi(A)\) for A380060 and \(B=\Phi(2)\) for A380680. The denominators are formal units, and every coefficient receives contributions from only finitely many \(j\). A coefficient-agreement argument constructs the implicit solution.

The outside factor two reduces the required calculation to characteristic two:

- For the implicit source, \(A\equiv1\), so the quotient becomes one. The support is \(j^2\).
- For the constant-two source, the quotient becomes \(x^j\). Its \(j\)-th power contributes a second factor \(x^{j^2}\), giving support \(2j^2\).

**Outcome:** A380060’s square-support conjecture is proved. A380680’s square-support conjecture is refuted and replaced by a twice-square theorem. The source bridge treats the positive-index formula (2); it does not include a separate formal equivalence to the bilateral Laurent-series title. [E20]

## 5. False statements and corrections

A false conjecture cannot be proved. A counterexample and a correct replacement constitute a different, useful mathematical outcome.

| Entry | What was false or incomplete | Established correction | Historical status |
|---|---|---|---|
| **A396843** | An older modulo-nine residue assertion. | \(a_5(3)=975\equiv3\pmod9\); the complete alternating sparse residue classification replaces the false clause. | Danial Asaria’s counterexample is credited. It was not newly discovered in the final consolidation. |
| **A396844** | A source clause omitted a residue-four class modulo sixteen. | \(n=17=4^2+1\) has residue four; the full classes are \(4^k+1\) and \(2\cdot4^k+1\), with residues four and twelve. | Already covered by the original parameter-family work. |
| **A396798** | The block \(1,1,5,5\pmod8\) was assigned the wrong starting phase. | It begins at degree two. The third coefficient is \(9\equiv1\pmod8\), contradicting the literal degree-one phase. | One of the two expansion-round refutations. Lean proves the sufficient residue counterexample directly. |
| **A380680** | Residue two modulo four was claimed at square indices. | \(a(1)=4\), \(a(2)=6\); the actual support is twice a positive square. | One of the two expansion-round refutations, with exact counterexamples and corrected all-index theorem. |

Thus **four delivered entries contain corrections**, while **two refuted source comments** belong to the expansion-round statement count. These are different scopes, not competing totals. [E2] [E5] [E8] [E20]

## 6. Candidates screened out

These records show why the entries were not included. They do not show seven sustained mathematical proof failures.

| Entry | Recorded stopping reason | Classification |
|---|---|---|
| **A004123** | Retrieved offset-one data and some offset-zero formulas required additional source clarification. | Source/specification ambiguity. |
| **A378575** | Amol Bhave’s general positive-iterate theorem already covered the relevant claim. | Prior-work exclusion. |
| **A378576** | Covered by the same prior theorem. | Prior-work exclusion. |
| **A282779** | Prior AlphaProof Nexus work was identified. | Prior-work exclusion. |
| **A396094** | The related fourth-iterate entry had no explicit conjecture in the scout’s retrieval. | Screened as a related entry, not adopted as an open target. |
| **A396209** | The related third-iterate entry had no explicit conjecture in the scout’s retrieval. | Same. |
| **A396210** | The related third-iterate entry had no explicit conjecture in the scout’s retrieval. | Same. |

The first four appear in the final archive’s Stirling, inverse-iterate, and coverage documents. The last three appear in the retained scout note. These are historical observations from the research; this retrospective did not conduct a new check of current OEIS wording. [E4] [E5] [E12] [E13]; Section 10.

A196523 and A091713 were prior-work comparators, not additional failed targets in this count. A001333, A001156, and A088311 supplied weights or background definitions. A265940, A271958, and A396845 were parameter-family references. Merely appearing in a source list does not make an entry a separately attempted or solved problem.

## 7. Where the work remained incomplete

### Mathematical questions outside the proved scope

| Question or extension | What was proved instead | Status at the end of the project |
|---|---|---|
| **A389537 sign runs** of length nine or ten after index seven | Its exact modulo-four coefficient classification and source construction. | No sign-run theorem. |
| **A378580 radius of convergence** | Formal existence and square-support congruence. | Radius not determined. |
| **A167137 power/logarithm integrality conjecture** | Known weighted-Stirling periodicity. | Separate conjecture not proved. |
| **A354242 continued-fraction conjecture** | Known weighted-Stirling periodicity. | Separate conjecture not proved. |
| **Analytic values, radii, or asymptotics** for the differential, Mahler, cubic, square-reversion, and theta families | Specified formal algebra and coefficient congruences. | No general analytic result delivered. |
| **Cubic-family nonnegativity** | Integer constructions and selected congruences. | Nonnegativity not established. |
| **A380555 reversion** | A380056’s exponential-coefficient results. | No theorem claimed for this distinct sequence. |

These are genuine remaining questions or limits of coverage. The surviving records do **not** establish that each received a long unsuccessful proof attempt. It would be inaccurate to invent a “got stuck after trying…” narrative for them. The obstacle visible from the completed methods is that congruence information alone does not control signs or analytic growth. [E4] [E11] [E13] [E19]

### Formalization extensions not included

| Extension | Delivered scope |
|---|---|
| Separate Lean proof of the Stirling EGF substitution bridge \(G(e^x-1)\) | Lean starts from the exact finite Stirling sums; the generating-function derivation is proved in prose. |
| Stronger Carmichael-period bound | The totient-period theorem is formalized; Danesh’s stronger known result is credited. |
| Optimal periodicity onset | The sufficient onset \(n\ge m\) is proved; optimality is not claimed. |
| Bilateral Laurent-series equivalence for A380060/A380680 | Positive-index formula (2), its construction, and its congruences are formalized. |

These limits do not leave a hidden assumption in the advertised Lean statements: the formal claims are explicitly stated at the scope that was actually proved. [E13] [E20]

### A recorded early formalization failure that was resolved

The original A396843 handoff contained supporting theorems but lacked the complete main formalization. Its historical completion criteria state that baseline mode passed and complete mode failed because the main theorem module and contract file were absent.

That was a real incomplete stage. The later original-project progress record states that all **16 required endpoints** were proved for the actual canonical formal power series and its normalized two-sided inverse. Those results were preserved and rechecked in the final collection. The final outcome therefore supersedes the early partial status; the earlier 23 supporting theorems alone were not sufficient evidence of completion. Section 10 records the historical sources.

## 8. Difficulties that were solved

Several issues required explicit mathematical or verification work even when the final congruence looked simple.

| Difficulty | Resolution in the delivered work |
|---|---|
| **Proving the right sequence** | Construct the source-defined series, prove its literal equation and uniqueness, and then identify its reduction. |
| **Division by nonunits** | Use coefficientwise scaling, prove exact integer halving or quartering before reduction, and use binomial convolution for EGF coefficients. |
| **Different notions of inverse** | Keep unit inversion and compositional inversion separate; prove both compositional inverse identities where needed. |
| **Negative iterates** | Build signed iteration from a genuine inverse and prove the formula for every integer iterate. |
| **Infinite nests and sums** | Prove coefficient stabilization for nests and finite contribution to each coefficient for theta sums. |
| **Low-degree exceptions** | Retain bounds such as \(n>1\), \(n>2\), and \(k\ge1\); explicitly check the phase that failed in A396798. |
| **Possibly reused compiled objects** | Strengthen verification to compile first-party sources directly into a fresh isolated object directory. |
| **Release integrity** | Bind manuscript/Lean reviews to the reviewed file hashes and check archived payloads against fixed checksum values. |

The compiled-object concern and two final packaging/review-binding issues were documented and repaired. They were verification-process defects or risks, not counterexamples to the mathematics. The successful final reports were produced after those corrections. [E6] [E21]

## 9. What “verified in Lean” means for this collection

The final stored reports record:

| Verification item | Result |
|---|---:|
| First-party modules freshly compiled from source | **100** |
| Preserved root contract file | **Separately compiled** |
| Original required endpoints audited | **339** |
| Additional per-entry theorem statements audited | **262** |
| Combined audited declarations | **601** |
| Numerical corroboration suites | **13** |
| Validation regression tests | **41** |
| Individual manuscript PDFs | **34** |
| Individual manuscript pages | **141** |
| Lean version | **4.19.0** |
| Mathlib revision | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |

The transitive axiom audits accepted only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No admitted proof or custom mathematical axiom was accepted. The source snapshots before and after the final verification matched. [E6] [E7]

**The number 601 is not a problem count.** It includes construction and uniqueness results, source-equation bridges, supporting statements, generalizations, and per-entry restatements of earlier theorems.

A successful Lean check establishes the formal propositions under the pinned system and its accepted foundations. It does not establish historical novelty, publication priority, authorship, or the correctness of every prose sentence. Definition reviews and typed contracts help assess whether the propositions express the intended OEIS questions. The finite computations are corroboration, not the justification for all-index conclusions.

This retrospective reads the existing final evidence. **It does not claim that a new complete Lean build was run while writing this report.** No proof source or final archive was changed for this retrospective.

### Archive identity

This report refers to the already delivered archive:

- **Filename:** `OEIS_Final_Collection_Dev_Goyal.zip`
- **Payload files:** 587
- **Size:** 17,367,520 bytes
- **SHA-256:** `a45b3ef924f316c384b4cdbac9c632526801e25cd6d1bc5da7e0fc283914f40c`

The final collection report has status `final_collection_verified`; the complete mathematical report has status `mechanical_checks_passed`. Those reports, the manuscript records, and the source ledgers are the evidence behind this retrospective.

## 10. Evidence and reconstruction limits

### Retained scout note

The file `new_series_scout/research_notes.txt`, dated 24 October 2026, records A396093 as selected, A396102 as a second target handed onward, and the positive-iterate family as excluded because of prior work. Its additional screening passage reads:

> RELATED ENTRIES NOT CLAIMED AS OPEN CONJECTURES:  
> https://oeis.org/A396094 (fourth iterate of the same B) has no conjecture.  
> https://oeis.org/A396209 and https://oeis.org/A396210 (third iterates of  
> x/(1-x)^3 and x/(1-x)^4) have no explicit conjectures.

This excerpt is included so that the extra three entries in the minimum-41 screening inventory are visible in this standalone report. It records what the scout found then; it is not a fresh assertion about the entries’ present status. The scout note is a separate retained workspace record, not a file claimed to be inside the final ZIP.

### Historical completion records

The earlier repository copy contains:

- [`history/original-release/docs/COMPLETION_CRITERIA.md`](../history/original-release/docs/COMPLETION_CRITERIA.md): records the initial complete-mode failure caused by absent main theorem and contract files.
- [`history/original-release/docs/PROGRESS.md`](../history/original-release/docs/PROGRESS.md): records subsequent completion of all 16 required endpoints while retaining the 23 supporting theorems.

The original repository is [dvgyl/oeis-a396843-proof](https://github.com/dvgyl/oeis-a396843-proof), inspected at revision `995e55adcbe06b2a913e24f12ff73a7faf362f06`. Its historical human-review statement applies to that earlier work; it does not establish completed human review of the expanded collection.

### Source map for the final archive

The links below point to the archive's files in this repository's `history/chatgpt-collection/` folder. Each individual manuscript and Lean interface is linked from the archive’s [INDEX.md](../history/chatgpt-collection/INDEX.md). The full list of 34 entries is accounted for in Sections 2 and 4.

| Reference | Evidence in the final collection |
|---|---|
| **E1** | [Entry catalogue](../history/chatgpt-collection/catalogue/entries.json) and [index](../history/chatgpt-collection/INDEX.md). |
| **E2** | [First-expansion coverage](../history/chatgpt-collection/docs/COVERAGE.md). |
| **E3** | [Second-round coverage](../history/chatgpt-collection/docs/ROUND2_COVERAGE.md). |
| **E4** | [Third-round coverage and unproved questions](../history/chatgpt-collection/docs/ROUND3_COVERAGE.md). |
| **E5** | [Fourth-round coverage and source status](../history/chatgpt-collection/docs/ROUND4_COVERAGE.md). |
| **E6** | [Final collection review](../history/chatgpt-collection/docs/FINAL_COLLECTION_REVIEW.md) and [AI disclosure](../history/chatgpt-collection/AI_DISCLOSURE.md). |
| **E7** | [Final verification report](../history/chatgpt-collection/reproducibility/final_collection/report.json), [complete mathematical report](../history/chatgpt-collection/reproducibility/lean_complete/report.json), and [manuscript checks](../history/chatgpt-collection/validation/manuscript_checks.json). |
| **E8** | [A396843 manuscript source](../history/chatgpt-collection/manuscripts/A396843.tex), [A396844 manuscript source](../history/chatgpt-collection/manuscripts/A396844.tex), and [original-family semantic review](../history/chatgpt-collection/reproducibility/final_collection/second_review_of_original.md). |
| **E9** | [Related conjectures and prior work](../history/chatgpt-collection/docs/RELATED_CONJECTURES.md), [formal review](../history/chatgpt-collection/docs/FORMAL_REVIEW.md), and [signed-iterate review](../history/chatgpt-collection/docs/INTEGER_ITERATES_REVIEW.md). |
| **E10** | [Rational-parity review](../history/chatgpt-collection/docs/RATIONAL_PARITY_REVIEW.md). |
| **E11** | [Cubic-reversion proof and scope](../history/chatgpt-collection/docs/CUBIC_REVERSION.md). |
| **E12** | [Inverse-iterate proof and prior work](../history/chatgpt-collection/docs/INVERSE_ITERATE.md). |
| **E13** | [Stirling-periodicity proof, credits, exclusions, and scope](../history/chatgpt-collection/docs/STIRLING_PERIODICITY.md). |
| **E14** | [Differential and Mahler proofs](../history/chatgpt-collection/docs/DIFFERENTIAL_AND_MAHLER_PARITY.md). |
| **E15** | [Sparse inverse proof](../history/chatgpt-collection/docs/ROUND3_LACUNARY_INVERSE.md) and [square-reversion proof](../history/chatgpt-collection/docs/ROUND3_SQUARE_REVERSION.md). |
| **E16** | [Theta-substitution proofs](../history/chatgpt-collection/docs/THETA_SUBSTITUTION.md). |
| **E17** | [Infinite nested-reversion proof](../history/chatgpt-collection/docs/ROUND4_NESTED_REVERSION.md). |
| **E18** | [Catalan-composition and square proofs](../history/chatgpt-collection/docs/ROUND4_CATALAN_COMPOSITION.md). |
| **E19** | [Exponential/cosine proof and source bridge](../history/chatgpt-collection/docs/ROUND4_EXP_COSINE.md). |
| **E20** | [Rational-theta proofs and correction](../history/chatgpt-collection/docs/ROUND4_THETA_RATIONAL.md). |
| **E21** | [Third-round integration review](../history/chatgpt-collection/docs/ROUND3_INTEGRATION_REVIEW.md) and [final integration review](../history/chatgpt-collection/reproducibility/final_collection/second_integration_review.md). |

[E1]: ../history/chatgpt-collection/catalogue/entries.json
[E2]: ../history/chatgpt-collection/docs/COVERAGE.md
[E3]: ../history/chatgpt-collection/docs/ROUND2_COVERAGE.md
[E4]: ../history/chatgpt-collection/docs/ROUND3_COVERAGE.md
[E5]: ../history/chatgpt-collection/docs/ROUND4_COVERAGE.md
[E6]: ../history/chatgpt-collection/docs/FINAL_COLLECTION_REVIEW.md
[E7]: ../history/chatgpt-collection/reproducibility/final_collection/report.json
[E8]: ../history/chatgpt-collection/manuscripts/A396843.tex
[E9]: ../history/chatgpt-collection/docs/RELATED_CONJECTURES.md
[E10]: ../history/chatgpt-collection/docs/RATIONAL_PARITY_REVIEW.md
[E11]: ../history/chatgpt-collection/docs/CUBIC_REVERSION.md
[E12]: ../history/chatgpt-collection/docs/INVERSE_ITERATE.md
[E13]: ../history/chatgpt-collection/docs/STIRLING_PERIODICITY.md
[E14]: ../history/chatgpt-collection/docs/DIFFERENTIAL_AND_MAHLER_PARITY.md
[E15]: ../history/chatgpt-collection/docs/ROUND3_LACUNARY_INVERSE.md
[E16]: ../history/chatgpt-collection/docs/THETA_SUBSTITUTION.md
[E17]: ../history/chatgpt-collection/docs/ROUND4_NESTED_REVERSION.md
[E18]: ../history/chatgpt-collection/docs/ROUND4_CATALAN_COMPOSITION.md
[E19]: ../history/chatgpt-collection/docs/ROUND4_EXP_COSINE.md
[E20]: ../history/chatgpt-collection/docs/ROUND4_THETA_RATIONAL.md
[E21]: ../history/chatgpt-collection/reproducibility/final_collection/second_integration_review.md

