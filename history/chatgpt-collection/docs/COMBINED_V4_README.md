# Combined OEIS proof package — version 4

**Author: Dev Goyal. Prepared 24 October 2026.**

This cumulative release adds complete Lean proofs of **six statements labeled conjectures in five retrieved OEIS entries**, proves one additional elementary parity observation, and **refutes and corrects a false conjecture in A380680**. All coefficient conclusions cover every index in the stated range. All earlier proofs, manuscripts, and the three previously delivered ZIPs are retained.

Start with **`manuscript/more_oeis_proofs_and_corrections.pdf`** for this round. Three earlier papers and all four editable LaTeX sources are included. The complete verification set has **339 fixed endpoints: all 226 from version 3 plus 113 additions**. These include source equations, constructions, uniqueness, and supporting results; they are not counts of solved open problems.

> **AI disclosure:** ChatGPT (OpenAI) generated the new mathematical arguments, Lean proofs, manuscripts, verification programs, and AI-assisted reviews in response to Dev Goyal's prompts. Dev Goyal is the sole human author. **Independent human review is pending.** Source conjectures, known results, and adapted upstream code retain separate credits. See `AI_DISCLOSURE.md`.

## New results

Unless specified otherwise, `a(n)=[x^n]A(x)`. Normalized series have `A=x+O(x²)`. Let `C=x+C²` be the normalized Catalan series. Exponents k are nonnegative integers unless k≥1 is stated.

| Entry | Source specification | Proved result |
|---|---|---|
| [A195194](https://oeis.org/A195194) | Infinite tails `F_j=Rev(x−(j+1)xF_(j+1))`, with `A=F_0` | `a(n)` is odd exactly when `n=2^k`. The formal theorem includes n=0; the source starts at 1. |
| [A393172](https://oeis.org/A393172) | `A(x−x²)=x+A(x)²` | For n>1, residue 2 modulo 4 exactly at powers of two, and 0 otherwise. |
| [A393171](https://oeis.org/A393171) | `B=x+B(C)²` | For n>2, residue 4 modulo 8 exactly when `n=2^k` or `2^k+1`, k≥1, and 0 otherwise. |
| [A380056](https://oeis.org/A380056) | Exponential generating function `(exp(x)−1)/cos(2x)`; `a(n)=n![x^n]A` | Both conjectures: `a(n)≡1 mod 4` for n≥1, and five divides `a(4n)`. More strongly, five divides `a(n)` iff four divides n. Residues modulo five by n modulo four = 0,1,2,3 are 0,1,1,3. |
| [A380060](https://oeis.org/A380060) | `A=1+2 Σ_(j≥1) x^(j²)((A−x^j)/(1−x^j A))^j` | For n>0, residue 2 modulo 4 exactly at square indices, and 0 elsewhere. |
| [A380680](https://oeis.org/A380680) | `B=1+2 Σ_(j≥1) x^(j²)((2−x^j)/(1−2x^j))^j` | **Correction:** residue 2 modulo 4 exactly when `n=2j²`, j≥1, and 0 elsewhere. The original square-index conjecture is false: `a(1)=4`, `a(2)=6`. |
| [A392210](https://oeis.org/A392210) | `D=x+D(x/(1−x))²` | `a(2n−1)` is even for n>1. This is an elementary characteristic-two square consequence, included as a separate source observation. |

The first five rows contain six explicit conjectures because A380056 has two. A380680 is a **refutation with a corrected all-index theorem**. A392210 is not counted among those six; the source describes it as an apparent pattern.

All seven sequences and their selected conjectures or observations are credited to **Paul D. Hanna**. Official pages were checked on 24 October 2026. Exact-identifier and equation searches, an available AI-proof catalogue, and the primary DeepMind OEIS attempted-theorem mapping did not identify an earlier proof of these selected statements. This bounded search does not establish worldwide novelty, exclusive priority, publication, or OEIS acceptance. See `docs/ROUND4_COVERAGE.md`.

## Connection to the actual sequences

The proofs construct each sequence and establish its source formula before deriving the congruences.

- **Nested reversion:** a unique infinite family is constructed for arbitrary weights over any commutative ring, with both inverse identities. A nest of depth d matches the canonical family through degree d+1. Modulo two, the second weight vanishes and the first tail satisfies `A=x+A²`.
- **Catalan substitution:** `G=T+(G∘P)²` is constructed by coefficient recursion. The A393172 source is equivalent to such an equation, and `2C−x` solves it modulo four. An exact integral remainder gives the A393171 modulus-eight lift.
- **Exponential coefficients:** an integer binomial-convolution recursion is connected to the literal rational exponential/cosine quotient. Factorial conversion and uniqueness are proved. Modular reasoning uses the integer divided-power coefficients, with no division by factorials in characteristic five.
- **Rational theta sums:** each coefficient sum is finite because the j-th summand starts at degree j², and every denominator is a constant-one unit. A contraction constructs the implicit series uniquely. Modulo two its rational factor is one for A380060 and x^j for A380680, yielding square and twice-square support after doubling modulo four.

For the theta entries, the formal source is the **positive-index formula (2)** displayed by OEIS. A separate formal Laurent-series equivalence to the bilateral titles is not claimed. Analytic asymptotics, convergence radii, and real special values are outside this release's scope.

## Previous work retained

| Release | Retained scope |
|---|---|
| Version 3 | A397588, A389536, A389537, A389542, A378580, A378581; six conjecture statements and the existing A397588 divisibility-by-three assertion. |
| Version 2 | A396093, A389474, A389475, A396102; inverse-iterate generalization; seven credited known Stirling-periodicity applications. |
| Version 1 | A396099, A396798, A396807, A393856–A393859; consecutive-iterate and scaled-inverse families; original A396843 work. |
| Original repository | All 16 Hanna.Acceptance endpoints, supporting source, manuscript source, author metadata, and provenance records. |

All **54 previous Lean source files** are accounted for. Every previous proof module is byte-for-byte unchanged, and the root contract text is retained literally after an added import. Earlier endpoints remain in their original order. The three previous complete ZIPs are embedded verbatim:

| Archive in prior_work/ | Unchanged SHA-256 |
|---|---|
| oeis_congruence_proofs_Dev_Goyal_v1.zip | `04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c` |
| oeis_proofs_complete_Dev_Goyal_v2.zip | `b28c6de12f53e862b670d37d79d8b5f11333ce3d7acd44e61cb27eb2b99dbc10` |
| oeis_proofs_complete_Dev_Goyal_v3.zip | `6a0cbeb94076a90e8938627a156ed4152f6cc3fd88546d0d2e29cd9331744d41` |

Earlier qualifications remain in force. The Stirling results are known mathematics credited to Payam Danesh's [26 August 2026 preprint](https://doi.org/10.33774/coe-2026-4d6jr) and earlier Fubini-periodicity work. Standard Frobenius consequences remain identified as such. The earlier consecutive-iterate case is credited to Shiva Priyan Shanmuga Sundaram, and Bhave's positive-iterate proof in A196523 is separately credited. A396798's false literal phase and its correction remain distinct. No A389537 sign-run or A378580 convergence-radius result has been added.

The reference repository is [dvgyl/oeis-a396843-proof](https://github.com/dvgyl/oeis-a396843-proof), revision `995e55adcbe06b2a913e24f12ff73a7faf362f06`. No original DOI is reassigned to this expanded release. This workflow has not submitted to OEIS or published to GitHub.

## Contents

- `manuscript/more_oeis_proofs_and_corrections.pdf` and `.tex`: this round's self-contained mathematics.
- `manuscript/six_more_oeis_proofs.*`, `further_oeis_proofs.*`, and `compositional_congruences.*`: three unchanged earlier papers and editable sources.
- `lean/Round4/`: new proof modules and explicit typed contracts; all earlier libraries remain.
- `docs/ROUND4_COVERAGE.md`: exact source statements, metadata, index ranges, theorem map, and prior-art limits.
- `docs/ROUND4_NESTED_REVERSION.md`, `ROUND4_CATALAN_COMPOSITION.md`, `ROUND4_EXP_COSINE.md`, and `ROUND4_THETA_RATIONAL.md`: detailed proof notes.
- `docs/ROUND4_*REVIEW.md`: separate AI-assisted semantic and integration reviews, not human peer review.
- `validation/final_theorems.json`: all 339 required endpoints, independently fixed in the checker.
- `reproducibility/lean_complete/`: fresh build, direct source compilation, contracts, full types, transitive axiom audit, and numerical evidence.
- `prior_work/`: all three earlier complete ZIPs and original provenance; `third_party/mathlib/` retains upstream attribution and licensing.

## Reproduce verification

The project pins **Lean 4.19.0** and **Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b**. Python 3.11 or later is required. Compiler binaries and downloaded dependency caches are omitted; pinned source configuration and the lockfile are included.

```sh
cd lean
lake exe cache get
lake build
cd ..
python3 scripts/check_formalization.py
```

The checker clears this project's build cache and builds all **six libraries**. It then invokes the actual Lean compiler directly on all **65 first-party modules** in dependency order into a new empty object directory. That directory is first on the import path, and the old project-object directory is excluded. This forces source re-elaboration. The root contract file, complete theorem-type output, and all 339 transitive axiom audits use those same isolated objects.

The checker rejects warnings, errors, missing/duplicate audits, weakened manifests, altered pins or previous proofs, and source changes during verification. Only the standard axioms **propext, Classical.choice, and Quot.sound** are accepted. There are no admitted proofs, native-decision certificates, or custom mathematical axioms. The validation gate has **41 regression tests**.

### Independent numerical corroboration

All **13 numerical suites** are rerun, including the nine from version 3. The additions can also run separately:

```sh
python3 scripts/verify_nested_reversion.py --output validation/nested_reversion_numeric.json
python3 scripts/verify_catalan_composition.py --output validation/catalan_composition_numeric.json
python3 scripts/verify_exp_cosine.py --output validation/exp_cosine_numeric.json
python3 scripts/verify_theta_rational.py --output validation/theta_rational_numeric.json
```

They match **all 177 displayed main-sequence terms** across seven entries, plus **42 displayed auxiliary-tail terms** for A195194. Default bounds:

| Check | Bound |
|---|---|
| A195194 family, source, parity | Degree 64; independent direct reversion 32; stabilization depths 0–12. |
| A393172/A393171 independent recursions and residues | Degree 520; literal compositions and links 80. |
| A392210 | Odd indices through 519; literal source through 80. |
| A380056 | Integer convolution/residues through 400; separate rational EGF division through 80. |
| A380060 | Source, independent binomial expansion, and residues through 80. |
| A380680 | Direct formula/corrected residues through 1030; independent rational sum through 80. |

These are corroborating computations. The Lean conclusions have no upper index bound.

## Archive

The manuscripts are compiled with pdfLaTeX and rendered for visual inspection. After complete validation succeeds:

```sh
python3 scripts/package_release.py
```

The packager requires matching validated source hashes, logs, numerical evidence, and fresh-compilation records. It creates **oeis_proofs_complete_Dev_Goyal_v4.zip** and verifies every payload hash and ZIP CRC. SHA256SUMS covers the entire payload, including the three earlier archives; after extraction, run `sha256sum -c SHA256SUMS`.
