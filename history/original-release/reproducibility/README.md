# Current verification evidence

The reports in `lean_baseline/` and `lean_complete/` come from fresh local runs on this public source tree. Each report records command exit codes, log hashes, theorem types, axiom dependencies, and source hashes. The `sources_before` and `sources_after` maps in each report must match. The complete report also records the compiled contract object's hash. The object file itself is excluded from the source ZIP.

`parser_tests.log` records the unit-test result. `verification_100.json` records the exact finite check for 100 coefficients at each parameter from 2 through 9. `manuscript/inspection.json` records the PDF source hash, PDF hash, page count, and inspection method. See the [review summary](../docs/PUBLIC_REVIEW.md) for limits on the research and earlier transcript reviews.

The ZIP inventory is `delivery_manifest.json`. The ZIP checksum and byte verification report are in `dist/` outside the ZIP, so the ZIP does not include its own checksum.
