# Independent AI integration review: version 3

**Review date:** 24 October 2026.

**Reviewer disclosure:** a separate ChatGPT agent reviewed the release integration written by the coordinating agent. This is an AI review, not independent human peer review. The reviewer made no changes to the files under review; this document is the review deliverable.

## Conclusion and timing

**No blocking integration defect was found in the reviewed final code snapshot.** The combined requirements contain exactly the 130 previous endpoints followed by the 96 specified Round 3 additions, with no omissions, substitutions, or duplicates. The preservation checks for both delivered archives and the old Lean files pass. Comparison with the actual version-two archive found no weakening of the axiom parser, source snapshot checks, pin checks, fresh-build requirement, or existing regression tests.

The initial review took place before final validation and packaging, with the third manuscript/PDF still being completed. A subsequent ordinary complete run passed its endpoint audit, but the coordinator observed that Lake had apparently restored earlier project objects after cleaning. The checker was therefore strengthened to invoke Lean directly on every first-party source in an isolated object directory. This follow-up review inspects that strengthened implementation; its completed isolated compilation run and final ZIP integrity checks remain subsequent release evidence. Finished PDF layout is outside this review's scope.

## Files inspected

The review read `README.md`, `AI_DISCLOSURE.md`, `CITATION.cff`, `validation/final_theorems.json`, `scripts/check_formalization.py`, `scripts/package_release.py`, `tests/test_validation_requirements.py`, `lean/ContractChecks.lean`, `lean/Round3.lean`, `lean/Round3/Contracts.lean`, and `lean/lakefile.toml`.

Supporting inspection covered the four Round 3 endpoint fragments, the new numerical JSON records, the unchanged axiom-audit implementation and tests, and the corresponding files extracted in memory from the embedded version-two ZIP. The previous manuscripts were compared directly against that archive. All review computations were read-only with respect to release source; the unit tests use temporary directories for their mutation checks.

## 1. Fixed endpoint accounting

An independent Python check imported the validator without running its build pipeline and established all of the following:

- The ordered manifest list is exactly `check_formalization.FINAL_NAMES`.
- The manifest's group dictionary is exactly the independently fixed `ENDPOINT_GROUPS` dictionary in the checker.
- The combined list contains 226 distinct fully qualified names.
- The first 130 names are byte-for-byte the ordered requirement list in the delivered version-two archive's manifest.
- The remaining names are exactly the concatenation of the four reviewed Round 3 fragments in the integration order.
- Every fragment group and its ordered contents agree with both the root manifest and the fixed checker dictionary.

| Requirement source | Endpoints | Mapping result |
|---|---:|---|
| Delivered version-two manifest | 130 | Exact prefix retained |
| `round3_elementary_endpoints.json` | 27 | Exact ordered groups retained |
| `round3_lacunary_endpoints.json` | 24 | Exact ordered groups retained, including four shared transfer lemmas |
| `round3_square_endpoints.json` | 26 | Exact ordered group retained |
| `round3_theta_endpoints.json` | 19 | Exact ordered group retained |

Thus the advertised arithmetic is correct:

\[
 27+24+26+19=96,\qquad 130+96=226.
\]

The root documents correctly distinguish endpoint counts from conjecture counts. Construction, uniqueness, source-equation, reduction, and contract endpoints are included in the former. The six new selected OEIS coefficient claims are not described as 96 or 226 open problems.

## 2. Preservation of both delivered releases

The reviewer called the active `validate_baseline` function for each archive and independently compared the root contract text as a literal suffix. Both checks succeeded.

| Embedded archive | Expected and observed SHA-256 | Earlier endpoints |
|---|---|---:|
| `prior_work/oeis_congruence_proofs_Dev_Goyal_v1.zip` | `04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c` | 67 |
| `prior_work/oeis_proofs_complete_Dev_Goyal_v2.zip` | `b28c6de12f53e862b670d37d79d8b5f11333ce3d7acd44e61cb27eb2b99dbc10` | 130 |

The checks account for 30 earlier `.lean` files in version one and 42 in version two. In each case, every file other than the intentionally extended root `ContractChecks.lean` is byte-for-byte unchanged. The old root contract text is actually present as an unchanged literal suffix after the new import lines. The archive CRC checks also pass.

The validator invokes both preservation checks during complete validation. Both ZIP files are included in the source snapshot and are explicitly allowed into the release payload. The packager's default output is the new version-three ZIP outside the payload directory, so it does not overwrite an embedded prior archive.

The following previous manuscript files were also independently verified byte-identical to the delivered version-two archive:

- `manuscript/compositional_congruences.tex` and `.pdf`.
- `manuscript/further_oeis_proofs.tex` and `.pdf`.

## 3. Validator and axiom-audit continuity

The review compared the current checker and packager with their versions inside the delivered version-two archive, rather than relying on a reconstructed description of the old safeguards.

The checker changes add the fixed Round 3 names, import and default target; a second immutable archive; four new numerical suites; and a direct isolated compilation pass for every first-party module. The previous ordered endpoints and verification gates remain in place. In particular:

- Only the complete mode is accepted. Removing or replacing a required theorem, weakening imports, substituting another contract file, or changing the reviewed pins is rejected.
- The actual executing Lean version must be 4.19.0. The Mathlib source configuration, lockfile, installed commit, and absence of tracked Mathlib changes are checked.
- The reviewed Mathlib revision remains `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- The checker runs the regression tests and all numerical suites, removes this project's build cache, and performs the ordinary complete build. It then explicitly re-elaborates every first-party source into a newly created object directory, using the isolated import path detailed below. Dependency objects are retained; project objects used by the final audit must come from the direct compilation pass.
- It compiles the root typed contracts, prints full theorem types, and requests transitive axiom reports for every fixed endpoint.
- Nonzero command exits and warning/error diagnostics remain failures.
- The complete first-party source snapshot is compared before and after validation. Root documentation, manuscript PDFs, endpoint fragments, code, tests, and both previous ZIPs are included. First-party symlinks are rejected.

`scripts/audit_axioms.py` is byte-identical to version two. Its allowed set remains exactly `propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx`, custom mathematical axioms, unlisted dependencies, duplicate or missing theorem reports, unexpected extra reports, malformed/truncated output, and warning text. The existing axiom-audit test file is also byte-identical.

The source snapshot implementation has only the required extension allowing the second retained ZIP to be hashed. The packager retains its existing requirements for a successful report, equal before/after source snapshots, unchanged recorded source hashes, successful command records, matching evidence-log hashes, and matching numerical-evidence hashes. It additionally requires an exact, duplicate-free set of direct first-party compilation records and verifies their source hashes and newly-created-object flags. It then creates `SHA256SUMS`, checks every archived payload hash, and checks ZIP CRCs. The payload change admits the second previous ZIP; the output filename changes to version three.

These checks are reproducibility and consistency controls for the reviewed release. They are not a signed provenance system or an independent mathematical assessment of theorem meanings.

## 4. Imports and acceptance contracts

The import chain is explicit:

1. `Round3.lean` imports `Round3.Contracts`.
2. `Round3.Contracts` imports `Round3.ElementaryContracts`, `Round3.LacunaryContracts`, `Round3.SquareContracts`, and `Round3.ThetaContracts`.
3. Each contract module imports its corresponding proof module or modules.
4. The root `ContractChecks.lean` adds `Round3.Contracts` before the unchanged old contract text.

The Lake configuration and `validate_pins` both require the five default targets `Hanna`, `Consecutive`, `Related`, `More`, and `Round3`. The generated full-type and axiom-audit files import `Round3` along with every prior root import. This connects every new family and contract to the default build and the fixed endpoint audit.

No old contract was replaced by a finite check, a mere theorem-name lookup, or a weaker proposition. The detailed mathematical meaning of the new source contracts was reviewed in the separate family review documents. This integration review checks that those contracts are actually included in the combined build.

## 5. Regression tests independently rerun

The reviewer ran:

```sh
python -B -m unittest discover -s tests -v
```

**Result after the strengthening: 39 tests passed.** The suite includes malformed and forbidden axiom-report cases, fixed-manifest mutation cases, root-document/PDF snapshot coverage, symlink rejection, and mutation of an old proof in each previous release. Two added tests verify inclusion of isolated first-party modules, dependency ordering, exclusion of dependency-cache sources and the separately compiled root contract, and rejection of local import cycles. The new tests are additions; existing tests were not removed or weakened. `tests/test_audit_axioms.py` and `tests/test_verify_coefficients.py` are unchanged from version two.

This test execution does not stand in for the later fresh Lean build and all-endpoint axiom report.

## 6. Numerical accounting and publication wording

The README's six displayed-prefix counts agree with the actual numerical JSON records:

\[
 20+34+30+22+24+22=152.
\]

| Entry | Displayed terms matched | Advertised corroboration bound checked against JSON |
|---|---:|---|
| A397588 | 20 | Degree 500 for parity and the differential equation; divisibility by three for indices 2 through 500 |
| A389536 | 34 | Degree 2050 for residues and the Catalan comparison; direct substitution through degree 81 |
| A389537 | 30 | Degree 80 |
| A389542 | 22 | Coefficients and residues through degree 80; source and inverse equations through degree 81 |
| A378580 | 24 | Degree 64 |
| A378581 | 22 | Degree 64 |

The root checker preserves its five previous numerical suites and adds these four new programs, giving nine suites in total. It writes fresh numerical evidence inside the validation-output directory rather than silently treating old JSON files as rerun results. The documentation accurately separates these finite corroborations from the universal Lean propositions.

The reviewed root metadata clearly discloses AI generation and pending independent human review. `CITATION.cff` names Dev Goyal as the human author, gives release version 3.0.0, and does not assign a new DOI, affiliation, credential, or ORCID. The source conjectures remain credited to Paul D. Hanna.

Known-results labels remain accurate and explicit:

- The seven weighted Stirling applications remain credited formalizations of known results, with Payam Danesh's earlier theorem and stronger Carmichael bound identified.
- The two relevant version-two assertions remain identified as standard Frobenius consequences.
- The previously proved consecutive-iterate case remains credited to Shiva Priyan Shanmuga Sundaram.
- Bhave's positive-iterate result remains excluded from the new claim count; its prior credit was confirmed in the version-two archive's `docs/INVERSE_ITERATE.md`.
- A397588's divisibility by three remains labeled an existing source assertion, not another newly solved conjecture.
- The source sign-run observation for A389537 and the analytic radius question for A378580 remain outside the proved scope.

The six new statements are described as conjectures in the retrieved source entries, with bounded prior-art checks and no claim of exhaustive novelty or accepted priority. That qualification is consistent across README, disclosure, citation metadata, and the source ledger.

## Follow-up: forced source re-elaboration and import isolation

The cache-restoration observation exposed a limitation of relying on `lake clean`, directory removal, and a subsequent `lake build` alone to establish that every local source had just been elaborated. It did not change the mathematical statements. The revised checker adds an explicit direct-source pass, and this section supersedes any earlier assumption that the ordinary Lake build alone established that freshness guarantee.

The reviewer inspected the actual Lake compiler environment in this workspace. It identifies the absolute Lean 4.19.0 executable and eleven import-path entries: nine external dependency object directories, the project's own object directory, and Lean's runtime library directory. The revised code resolves each path against the Lean project directory before comparison. The comparison removes exactly the resolved project path `lean/.lake/build/lib/lean`; dependency paths such as `lean/.lake/packages/mathlib/.lake/build/lib/lean` are different resolved paths and remain available. The newly created unique `/tmp/oeis-lean-recheck-...` directory is prepended to the resulting `LEAN_PATH`.

The new `first_party_compile_order` function visits every first-party `.lean` file outside `.lake`, including files not reachable from a root library import. It excludes only the root `ContractChecks.lean`, which is compiled separately afterward. An independent inspection of the actual module graph found **53 modules**, with every local import preceding its importer. The temporary `lean/SquareAudit.lean` file is absent. The first-party modules use the ordinary one-line imports supported by the dependency scanner.

For each source, the checker invokes the resolved Lean executable directly with the project root and an explicit output filename under the fresh object tree. It rejects a pre-existing output object, requires the command to succeed without diagnostics, requires a newly created nonsymlink object file, and checks that the object's modification time is not earlier than the invocation's start. It records the source hash and generated object hash. No Lake command mediates these individual compilation calls.

The root contract compilation, generated full-type checks, and generated transitive axiom audit all use the **same direct Lean executable and same isolated environment**. Previously built project objects are absent from that effective import path. Local dependencies are found first in the new tree because their source modules have already been compiled in dependency order. The pinned external dependency caches and Lean runtime objects remain available.

The packager computes the expected first-party source set independently from the current tree. It rejects absent, extra, or duplicate compilation source records, a mismatching reported module count, a false new-object flag, or a recorded source hash that differs from the release source. Its existing command-log and source-snapshot checks remain active.

The follow-up independently reran all 39 regression tests successfully and inspected the current 53-module ordering and actual compiler environment. It did not itself run the entire 53-module direct compilation pipeline; the coordinator's final run must record that result, followed by the contract and 226-endpoint audit. No mathematical proof file was changed as part of this strengthening.

## Reviewed integration snapshot

These SHA-256 values identify the principal files read in this review. Subsequent changes to these files require an updated assessment; the final validation source snapshot separately records the actual release state.

| File | SHA-256 |
|---|---|
| `README.md` | `a37c3239f869e6cef7181b75510cce25a0bf9d5c2d0a1d555326a5247aacb607` |
| `AI_DISCLOSURE.md` | `ef2445a85ab1e74dc5a34e9462e1bdfdee9ecd36daaa14e7160e8288c8e641ae` |
| `CITATION.cff` | `ebc457f62d0e48d4125448f1f910cad400af6c8186543828973590f79a7a162a` |
| `validation/final_theorems.json` | `42780f8c5b03f02aa8b32445f966ea8a50e8e708f244065daa4cd059dc9d05fb` |
| `scripts/check_formalization.py` | `9ae6edec0676c64f343d57883bfc62e481bbca58a47b1325338260bd597fcb17` |
| `scripts/package_release.py` | `a0e6c6a6babc7de14d4c63a725ea48efad93a614c5be022a3e42bdd790be876c` |
| `tests/test_validation_requirements.py` | `3dff2d2651b4c677a29541ad4a99a682733774d31ec067dd47881df8ba05fd35` |
| `lean/ContractChecks.lean` | `d0b95748303cf3cc9377d0d6919d3fd433a726d1836d1985c6968e5db5593469` |
| `lean/Round3.lean` | `170ab473cf50d40957099a2aa02717e9afdf0e5a2a99da51054e082edf1c3a88` |
| `lean/Round3/Contracts.lean` | `f19a1691ae0ffe7228c767aa69bd0b3dd4e4d13d0f7e97c48b1cab0683aea2d4` |
| `lean/lakefile.toml` | `a9132700fe4a5806e35051434983f128280cd7dad40e3d5b2456d822f4b478dd` |

## Limits and remaining release gates

This review does not declare the strengthened isolated compilation and final 226-endpoint audit completed. It does not review the third PDF's finished layout or inspect the final version-three ZIP. The coordinating agent remains responsible for visual manuscript review, freezing all source including this updated review, running the complete strengthened validator, and packaging against the resulting successful report. The final report and archive verification must provide the evidence for those later actions.

No edits to the reviewed integration files were needed or made during this review.
