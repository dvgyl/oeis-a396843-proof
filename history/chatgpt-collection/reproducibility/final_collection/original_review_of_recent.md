# Independent AI review of the thirteen recent-entry manuscripts

**Result: no mathematical or source-to-formal mismatch found.** This review was performed by a separate AI agent from the author of these thirteen entry manuscripts. It is not independent human peer review. The review does not establish historical priority or worldwide openness.

## Method and material

Read all thirteen final LaTeX manuscripts and their separate, explicit Lean entry statements. Compared their defining equations, offsets, conclusion ranges, source qualifications, and proof mechanisms with the retained round-three and round-four manuscripts and source ledgers. The review covered the mathematical arguments, not only theorem names or build success. The complete Lean kernel check and transitive axiom audit are separate collection-level mechanical gates.

The following retained records were consulted: `manuscript/six_more_oeis_proofs.tex`, `manuscript/more_oeis_proofs_and_corrections.tex`, `docs/ROUND3_COVERAGE.md`, and `docs/ROUND4_COVERAGE.md`. The primary source pages were not re-retrieved during this consolidation review; source identifications and historical labels are those in the retained evidence.

## Findings by entry

| Entry | Mathematical and formal scope checked |
|---|---|
| A397588 | The derivative operator improves agreement by one degree; the integral recurrence has multiplier n+1 and the correct coefficient index. Modulo two the square derivative vanishes, giving binary support including n=0. Modulo three x satisfies the same source equation; divisibility is restricted to n>1. The latter is correctly marked an existing nonconjectural source assertion. |
| A389536 | Coefficient recursion from A(x²+2x³)=xA is triangular with j≤(n+1)/2<n. The candidate x+2xC solves the literal equation modulo four. Doubling uses parity transport rather than cancellation in Z/4Z. Exceptional indices are 2^k+1 for n>1. |
| A389537 | Alternating lacunary R satisfies R+R(x²)=x. Both inverse directions and the converse source bridge give the literal equation A(A−x)=A² and uniqueness. The halved series is constructed over the integers before reduction. Its mod-two equation H+H²=x³ gives exactly 3·2^k support for n>2. No sign-run claim is added. |
| A389542 | The auxiliary L construction is contractive over arbitrary commutative rings. R=x−2xL gives R²+R(4x³)=x²; reversion supplies the source equation. Source uniqueness correctly uses torsion-free integer coefficients, not Z/4Z. The involution calculation and residue class 2^k+1 for n>1 are correct. |
| A378580 | The literal multiplicative quotient x/A is distinguished from compositional inversion. The normal-root residual has next-coefficient multiplier 2−1=1, giving a division-free construction. Minus(T)=Plus(T⁻¹)⁻¹ is justified by unit inversion. The square-support classification excludes the constant term. |
| A378581 | The companion positive product substitution A(xA)=Theta has the same canonical construction. Theta=1+2S is itself the reduced solution modulo four; square support is for n>0. The paper includes the necessary shared construction rather than relying on an unavailable companion proof. |
| A195194 | The nested family is constructed simultaneously by degree, without an assumed boundary value at infinity. The two inverse equations match the source. Finite depth d agrees below degree d+2. Weights 1,2 force the second reduced tail to x and the first to x+A²; the parity statement includes n=0 consistently. |
| A393172 | Composing with the genuine Catalan inverse converts the literal source to a contractive square equation. The candidate 2C−x is normalized and solves that source modulo four. The support theorem is restricted to n>1 and its complement matches integer divisibility. |
| A393171 | Both source formulations are checked, together with B=x+A², B=A composed with x−x², and B composed with C=A. The modulus-eight lift first uses the exact integral decomposition A=2C−x+4K. For n>2, the two adjacent binary supports do not overlap; k≥1 is retained. |
| A392210 | The rational argument x/(1−x) is an actual constant-one-unit quotient. The canonical square equation is constructed uniquely. Frobenius eliminates all odd-index coefficients except the first, giving a(2n−1) even for n>1. The elementary-observation status is correctly stated. |
| A380056 | Integer binomial convolution is solved without division; the rational EGF bridge uses the factorial identity and the literal rescaled cosine. The finite-characteristic argument never divides by factorials. The mod-five exponential convolution calculation, residue classes 0,1,1,3, and equivalence 5 divides a(n) iff4 divides n are correct including n=0. |
| A380060 | The denominator is a constant-one unit for every input series. Local finiteness follows from degree j². The implicit operator improves agreement from degree zero, gives constant term one, and has a unique solution. Reduction modulo two turns each rational factor into1 and doubling gives square support modulo four. Formal coverage is explicitly limited to source formula(2), not an unproved bilateral Laurent equivalence. |
| A380680 | The explicit constant input2 is correctly distinguished from the implicit sequence argument. Its reduced rational factor is x^j, producing twice-square exponents 2j². The exact coefficients4 and6 come from the j=1 term. Both universal false claims are explicitly negated in Lean; the corrected result is not represented as a proof of the original claim. |

## Clarifications requested and resolved

Two small exposition clarifications were requested, without changing any mathematical conclusion or Lean proof. The abstract contraction lemma's comment about ring operations now explicitly refers to the algebraic operators used in the paper, rather than arbitrary contractive operators. The A380060 construction now says that the fixed point is over K and is integral when K=Z. Both changes are present in the reviewed source hashes below.

All papers retain explicit ChatGPT contribution disclosure and pending independent human review. No analytic convergence radius, real special value, asymptotic formula, extra sign-run theorem, or global novelty claim is inferred from the congruence proofs.

## Reviewed source hashes

The entries below bind this review to the mathematical TeX and explicit Lean interfaces. PDF appearance and PDF hashes are covered by the authoring agent's separate visual-QA record.

| File | SHA-256 |
|---|---|
| `manuscripts/A397588.tex` | `c5b3cb6a3133d8b7a60138247ece67b4d4bc0017c1446537885d50af946f6d87` |
| `lean/Entries/A397588.lean` | `608f4e395ea2a9a3659840c90100fa54713d68216332988c44a3248a33d1db49` |
| `manuscripts/A389536.tex` | `c37af2630243cd75bea4c1f7fc2a0964a31caaef103b4e03130567d8ba292c11` |
| `lean/Entries/A389536.lean` | `067abbf08d42fa75fa369c82bdcce8df26e45c2d67b62ca59a67218096b654fc` |
| `manuscripts/A389537.tex` | `64eb5bbc2a5bb12f2dd6ba10f9e3163aaf27f0a5e3efc5beabb19b9f3979352e` |
| `lean/Entries/A389537.lean` | `22cb1472f872939b899ad081c62e168351cb97a2ddd1f44ad2f5bd12703fca0a` |
| `manuscripts/A389542.tex` | `9cffa337f48f72606c483f713045a496ebcbeeaf5a113415e5f350afe612a573` |
| `lean/Entries/A389542.lean` | `8ea3c1df57ca873e8d865486d17b03ebc5798c71f4a5e6eaa6b07ebb01a38f6c` |
| `manuscripts/A378580.tex` | `070855e0488efbfe3c4eeb89f3ecc49b3b1311018982f18a7f0108b504cf335b` |
| `lean/Entries/A378580.lean` | `b03358b5da36e1b2ff69b9445045dc8c0f2a0bcc5aa83d2ba5ac05bd16c60776` |
| `manuscripts/A378581.tex` | `052a77db6ca48254b5165c23f8d315c8ca15885b05c706bbdf1b35bc7dbc28f4` |
| `lean/Entries/A378581.lean` | `39a9eb55b1a3bd75d6a4293ed0fa963f13f6c028f04bb69f82ee27e193975dbf` |
| `manuscripts/A195194.tex` | `89d1519da0eb49b896cc9fa3139d7742c289004e456c3d366e8301da78027ea2` |
| `lean/Entries/A195194.lean` | `f23490bb505d15eb78cfc032745702e50daf23e344d24e5af8f2f3754a6ede08` |
| `manuscripts/A393172.tex` | `1515c59c0fda13fc3f5140965c6eaf8e3230e96963142304860c5e0f60d12663` |
| `lean/Entries/A393172.lean` | `9f0d3ac32fac13ebb5c2ba5339ea585cab32812972ec740631b718eec5e95f88` |
| `manuscripts/A393171.tex` | `658cfbbdd262f16f2e5b06a48a65f8c64b7f715345c22765dcf01d52003fc596` |
| `lean/Entries/A393171.lean` | `e3de6cec3429ac796fb86deafa75c34c90b39d37f1340d169654ab7c0c81779e` |
| `manuscripts/A392210.tex` | `30c83c601acd3959e0397ce16c6dda69d0f756c81fe1ae487a95c3cb1e03f0de` |
| `lean/Entries/A392210.lean` | `5c4ec242be4735bf49df2debb250e1a4440aa0117c334230bec37a8a1763894f` |
| `manuscripts/A380056.tex` | `721d5f76a7dd2fee9f6fc4c40db72f79b1cbf9cc5157480a2132d38bbd99df9d` |
| `lean/Entries/A380056.lean` | `96809d90d447a83f694c5cb80072f307c42d0b21172c324eb11f0bedede9ac07` |
| `manuscripts/A380060.tex` | `75e81d30ce0371ea9d1d753ec577db2dd89318edb26d3680bd5646f4d8a41861` |
| `lean/Entries/A380060.lean` | `be0300c1be8025012f384f68beae13e609148367e312e436de078ca6bc68701f` |
| `manuscripts/A380680.tex` | `a801f19440268806a0f97a59a8a8c84554e0b5b02d3ecac9a9bb2d526f2e39dc` |
| `lean/Entries/A380680.lean` | `f158be4f03bd12ddbad0ab47784bcbff03acd173f3ab813a6225cfc4b539a5e9` |

Review completed 2026-10-24T18:38:41.123805+00:00.
