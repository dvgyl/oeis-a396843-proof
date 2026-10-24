# Review of the final consolidated collection

## Scope and outcome

This collection organizes the completed work into **34 individually readable manuscripts and 34 named Lean entry files**. It contains no additional search for new conjectures. The two identifiers added to the former headline inventory are A396844, already covered by the original parameter-four endpoints, and A396797, the credited known consecutive-iterate case. References to source-weight sequences, prior-art comparisons, and explicitly excluded candidates are not incorrectly counted as additional results.

The per-entry interfaces contain **262 explicitly typed theorems**. They restate or specialize completed results and make the relation between a manuscript and its formal proof easy to inspect. All **339 original audited endpoints** remain mandatory, and all **66 original Lean source files from the fourth release are preserved byte for byte**. The final project has 100 first-party modules for direct source re-elaboration, plus the separate preserved root contract file. These are counts of declarations and files, not counts of newly solved open problems.

The final mechanical outcome is recorded in [the collection report](../reproducibility/final_collection/report.json) and [the complete mathematical report](../reproducibility/lean_complete/report.json). The packager requires both successful reports and matching source hashes before producing the deliverable.

## Individual-paper coverage

Each entry has its own complete PDF, standalone LaTeX source, and Lean file. The paper supplies its defining formula and coefficient conventions, precise claims and index bounds, mathematical proofs, source references, AI disclosure, and a map to the formal statements. Necessary general arguments are repeated so the mathematical exposition does not require opening another manuscript.

The formal proofs use a shared library in the same archive. Each separate entry file has explicit proposition types and actual proof terms, importing the preserved proof implementations. Shared constructions and lemmas are proved in those implementations, rather than introduced as assumptions. The entry files are intended to be checked inside the pinned Lean project, not in isolation from their imports.

[The catalogue](../catalogue/entries.json) maps papers to original endpoints and new entry statements. [The dependency map](../catalogue/dependency_map.json) lists the entire local source closure of each entry. [The theorem inventory](../catalogue/theorem_inventory.json) retains every original endpoint, including generic transport and iteration results without a unique single-entry assignment. No generic result is dropped merely because it is shared by several papers.

The four original combined manuscripts and their editable sources remain unchanged in `manuscript/`. The separately organized papers are in `manuscripts/`. Earlier archives are retained only as provenance; the current source and papers are directly accessible without opening them.

## Mathematical and source-to-formal reviews

The agents who prepared the three groups separately reviewed another group's complete mathematical exposition and typed Lean statements. These are AI-assisted reviews, not independent human peer review. They compared source definitions, offsets, exceptional low indices, coefficient domains, moduli, and every substantive proof mechanism with the preserved manuscripts and proof sources.

- [Review of the ten original-family papers](../reproducibility/final_collection/second_review_of_original.md) covers binary divisibility, inverse coefficients, exact-exponent conventions, corrected parameter-three and parameter-four residues, natural and signed composition iterates, and scaled-inverse substitution without illicit division.
- [Review of the eleven second-round papers](../reproducibility/final_collection/recent_review_of_second.md) covers the rational third iterate, cubic reversion and characteristic-three consequences, inverse-iterate construction, finite Stirling transforms, exact tail periods, and the boundary of the EGF formalization.
- [Review of the thirteen recent papers](../reproducibility/final_collection/original_review_of_recent.md) covers all differential, Mahler, lacunary, square-reversion, theta, nested-reversion, Catalan, exponential-cosine, and corrected rational-theta arguments.

The reviews found no mathematical result requiring revision. Small exposition improvements were incorporated: the general contraction discussion limits its ring-operation claim to the actual operators being used; a construction over an arbitrary coefficient ring is distinguished from its integral specialization; the inverse-series construction is supplied where needed for a standalone paper; and A396844's shared theorem map explicitly explains how its counterexample follows from a checked residue classification. Final hashes accompany the review records.

The historical source ledgers were reused during consolidation. This editorial stage does not claim that a new exhaustive prior-art search was performed. It preserves the previous bounded-search qualifications and known-result credits.

## Document checks

All individual manuscripts were compiled with pdfLaTeX, rendered, and visually inspected on every final page. Text-bound checks and the final LaTeX logs supplement that visual review. The group records are:

- [Original-family PDF QA](../reproducibility/final_collection/original_pdf_qa.json).
- [Second-round PDF QA](../reproducibility/final_collection/second_pdf_qa.json).
- [Recent-paper PDF QA](../reproducibility/final_collection/recent_pdf_qa.json).

[The consolidated manuscript record](../validation/manuscript_checks.json) gives the final PDF/TeX hashes, page counts, identity/disclosure checks, page-bound results, and the hashes of those group reports. The final verifier checks that the delivered papers still match that record. Temporary PDF build copies and page-render images are excluded from the archive; final papers and verification logs are retained.

## Mechanical release gates

The final checker performs the following substantive checks:

1. It requires the exact 34-entry set and the fixed ordered list of 262 new interface names. It rejects missing or duplicate entries and theorem names, mismatched file paths, incomplete manuscripts, and absent explicit theorem declarations.
2. It checks the fixed preservation manifest for all 66 earlier Lean files and invokes the unchanged complete mathematical checker, whose 339 original requirements remain independent of the editable endpoint manifest.
3. It reruns all 13 numerical suites and the existing validation regression tests. The numerical calculations remain finite corroboration; the mathematical conclusions are unbounded in the stated ranges.
4. It clears this project's build cache, rebuilds the original libraries, and directly elaborates every first-party module into a new empty object directory. The old project-object directory is excluded from the verification import path. Each module's newly created object and source hash is recorded.
5. It compiles the preserved typed contracts and prints the full types and transitive axiom dependencies of all 339 original endpoints. It separately builds the named `Entries` library, prints all 262 entry types, and audits those entries using the same freshly elaborated objects.
6. It permits only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Missing or duplicate audits, errors, warnings, additional axioms, and source changes during verification cause failure.
7. Before packaging, it rechecks source hashes, the manuscript records, reports, command logs, numerical evidence, and forced-compilation records. The ZIP contains a checksum for every payload file; ZIP CRCs and payload hashes are checked after creation.

The independent integration review is recorded in [the integration review](../reproducibility/final_collection/second_integration_review.md). A compiler check validates the formal propositions against their actual definitions. It does not by itself establish a historical priority claim, validate every sentence of prose, or replace the mathematical source-correspondence reviews above.

## Qualifications retained

A396797 is credited as known. The seven Stirling applications are credited to prior periodicity work, including Danesh's stronger theorem; they are not newly solved open problems. Their EGF interpretation is explained mathematically, but the formalization starts from the explicit finite Stirling sums. The characteristic-prime consequences and A392210 observation are marked as elementary applications of standard algebra.

False source assertions remain distinct from their corrected theorems. The parameter-family residue corrections, A396798's starting-phase correction, and A380680's twice-square correction are presented accurately. In particular, the original A380680 square-index conjecture is not claimed to be proved. Rational-theta source correspondence is the displayed positive-index formula, without an additional claim of formally proved bilateral Laurent equivalence. Analytic convergence, real special values, unproved sign-run patterns, and unrelated source conjectures remain outside the stated scope.

Dev Goyal is the sole human author. ChatGPT generated the new developments and final organization in response to his prompts, subject to the preserved source, prior-result, and upstream-code credits. **Independent human review is pending.** No OEIS submission, GitHub publication, new DOI, journal acceptance, or worldwide novelty claim follows from this collection.
