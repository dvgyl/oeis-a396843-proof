# Independent AI integration review of the final collection

Reviewer: the separate ChatGPT agent that prepared the second group of entries, not the agent that wrote the final integration scripts. This is an AI-assisted source review; independent human review remains pending.

## Outcome and limits

No outstanding integration blocker was found in the reviewed versions. Two concrete integrity gaps were reported and fixed during this review, as recorded below. This review did not run the complete Lean checker, numerical suites, final interface axiom audit, or release packager. The root agent started the full verification separately after the sources were frozen. This report does not claim that run has passed; its result must be read from the subsequently generated verification reports.

The checks here were limited to reading the integration code, comparing immutable archived bytes, recomputing catalogue/import inventories and hashes, and invoking the read-only manuscript validation function on its final manifest. They are not a proof of correctness of the Python tools, a new mathematical peer review of all 34 entries, or a novelty assessment.

## Inventory, preservation, and imports

- The exact fixed set contains 34 distinct OEIS IDs. The three group catalogues merge exactly into the sorted final catalogue. Each entry has its canonical separate PDF, TeX, and Lean path.
- The 262 catalogue theorem names are unique, match every explicit theorem declaration in the 34 entry files in order, and have the fixed newline-terminated SHA-256 `b905776e3639174bfa54a1fca9df0181f4ea37a5166b3e0d85d8fee812e01031`. The verifier rejects a changed count or ordered name hash.
- All 339 original endpoint names remain identical to the fixed core list and the retained original manifest. The theorem inventory preserves all of them; 13 general/supporting endpoints are explicitly listed without a single-entry assignment rather than silently dropped.
- Compared the baseline with the actual v4 ZIP, whose SHA-256 is `d3ed94896bf191334a61efe6befb0af2a361162877f4ddf8198b4c4e9cda2b2a`. The baseline lists exactly all 66 old Lean files, and every current file matches its archived bytes. The core checker, strict axiom auditor, and original theorem manifest are also byte-identical to v4.
- `lean/Entries.lean` imports all 34 entry modules exactly once in catalogue order. Every entry's direct imports agree with its metadata. An independent local import traversal matches every recorded dependency closure and shared-file list; no local import is missing. There are 101 current first-party Lean source files: 100 modules in the core compile order plus the separately checked `ContractChecks.lean`.
- The pinned Lean/Mathlib settings and six original default library targets remain intact. The added `Entries` library is separately built by the final verifier.

## Manuscript and semantic-review binding

The manifest generator requires the three completed visual reports, checks each final PDF/TeX digest and page count, checks the entry identity and AI disclosure in extracted text, and rejects words beyond the page rectangle. It recognizes both actual semantic-review table formats, verifies the corresponding source digests, and stores an exact 68-path map for the reviewed TeX and Lean entry sources.

The final validator now requires all 34 reviewed paper pairs, all six exact visual/semantic review-record paths and their hashes, and the exact 68 reviewed source paths with their current hashes. A read-only call to the final validator succeeded for the current manifest: 34 papers, 141 pages, and 68 bound semantic source files. This verifies the manifest coupling; visual inspection itself is supplied by the three recorded page reviews, not inferred from a PDF header or invented by the generator.

## Fresh compilation and axiom-audit path

The unchanged core checker forces source elaboration of every first-party module in dependency order into a newly created empty temporary object directory. It excludes the ordinary project object directory from the effective Lean path, checks that each new object was actually created, and records source/object hashes. The temporary directory remains available after the core subprocess exits. The root contract file is then separately elaborated with that same path.

The final verifier reads the recorded exact compiler and isolated Lean path and uses them for the 262 full-type checks and transitive axiom reports. The intervening ordinary `lake build Entries` therefore does not switch the final audit back to cached project objects. The strict retained auditor requires exact named coverage and rejects duplicate, missing, unexpected, malformed, or truncated reports, as well as dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.

Both core and final stages require unchanged first-party source snapshots, and the final stage requires the core snapshot to be identical to its own. These controls are appropriate for the inspected frozen source tree; this review did not execute or independently reproduce the long compiler run.

## Packaging and resolved findings

1. The first packaging version wrote `SHA256SUMS` from one set of reads but compared archive payloads with fresh live-file digests. A file changing between those steps could have left embedded checksums stale while the readback check passed. The final version retains the original path-to-digest map, writes sums from it, checks the archived checksum text, and compares every archived payload to those fixed digests. It also verifies captured first-party hashes against the successful validation snapshot and checks the snapshot again after archive creation.
2. The first manuscript manifest bound reviewed Lean entry files only when the manifest was generated, retaining their paths without digests. The final version stores the exact path-to-reviewed-digest map, and `validate_manuscripts` rechecks all 68 current TeX/Lean hashes. An entry edit between manuscript-manifest generation and verification is now rejected.

The final packager also requires the successful final/core report statuses, exact entry-theorem list, matching catalogue and manuscript manifests, stable source snapshots, command-log hashes, numerical evidence hashes, and complete nonduplicated forced-compilation source records. It retains the three required earlier release ZIPs and rejects unexpected symlinks. ZIP CRC and fixed payload hash checks are explicit. Actual release creation and its final archive digest remain for the root agent to execute after verification.

## Reviewed file hashes

Recorded UTC: 2026-10-24T18:45:11+00:00

| File | SHA-256 |
|---|---|
| `scripts/verify_final_collection.py` | `aeabee3dd5fccf3933636300dc06c1501d2b62e694532442fc217e3ad664af47` |
| `scripts/build_collection_index.py` | `716980f2f52914780505e5a680827510c07b854e98c433869ba72d147a08f427` |
| `scripts/package_release.py` | `0b991aac999e1e568c1e418a43849fe47b714a98f152fe267f2df495ea6fc798` |
| `scripts/check_manuscript_files.py` | `2cef5c3787fd8008d98a03e3a022ec03da0107676591b0d059a4d9dbb9a62ad8` |
| `scripts/check_formalization.py` | `7c6bf5dd92c9518ca2a304165806e37c4aa3b14829fbf781286ee185e995e1ce` |
| `scripts/audit_axioms.py` | `b01372d4ffa07cc3236ef641cc3beef90d0667ed755103fcee4cc2927d6ee89f` |
| `validation/final_theorems.json` | `c6f4d4c4d3427e74dbdb578202a88a0afbe137872137b9febbea0669c427865f` |
| `validation/consolidation_baseline.json` | `18f002efa5f66a8283e3dcb2309fd457575c94830a2bc4408ff4ba2dfefc9a4c` |
| `validation/manuscript_checks.json` | `53ed8ce5b35c432c3ee9eac2e191ea30f14bee752189741b21d59bee7c21e075` |
| `lean/lakefile.toml` | `3b4e6cfbf03806fbd1999d129085e447d83871a12565bcefc0c97a361194fc6f` |
| `lean/Entries.lean` | `867ee7a520eaecc9203a0bb78445260b67ef1bddbc1a702a8df4530f0dda6b3e` |
| `catalogue/entries.json` | `d21b915437389b10d4dadfd52e9af5d716026756fbeb82283a62f85744d6bae5` |
| `catalogue/dependency_map.json` | `c883e4f4c4561f6ad9c8b949206a62a94e601ddc5586d7896d0a8e730ca6141d` |
| `catalogue/theorem_inventory.json` | `775dcdbf31917d4a3d13df612cae2273bcc4be513e213c888c56fa84351d22f3` |
