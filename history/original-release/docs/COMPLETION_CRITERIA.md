# What counts as a completed formalization

Completion has two parts: Lean must check the proof terms, and review must establish that their types and definitions express the intended mathematics.

## Mechanical checks

From the repository root, after dependency setup:

```sh
python3 -m unittest discover -s tests -p 'test_*.py'
python3 scripts/check_formalization.py --mode baseline
python3 scripts/check_formalization.py --mode complete
```

The initial handoff passed baseline mode and failed complete mode because its main theorem module and contract file were absent. The completed package must pass both modes.

Complete mode requires:

- The fixed 16 endpoint names in `validation/final_theorems.json`.
- The pinned Lean release and a matching executing compiler.
- A successful `lake clean hanna` followed by `lake build`. This rebuilds the first-party proof package while preserving pinned dependency caches.
- A nonempty `lean/ContractChecks.lean`, compiled to a fresh object.
- Fresh type output for every required endpoint.
- Fresh transitive axiom output for every required endpoint.
- No compiler error or warning diagnostic in those commands.
- No axiom dependency outside `propext`, `Classical.choice`, and `Quot.sound`.
- Stable first-party source hashes throughout the run.

The runner generates its own audit commands. The parser rejects absent, extra, duplicate, malformed, and truncated records, including `sorryAx` and custom mathematical axioms. The endpoint list is fixed in both the script and manifest so an accidental omission from the JSON does not silently reduce coverage.

Reports, logs, generated audit source, and source hashes are written to `reproducibility/lean_baseline/` or `reproducibility/lean_complete/`. The JSON status `mechanical_checks_passed` means exactly that. It does not claim that a reviewer has approved the mathematical interpretation.

The harness assumes an ordinary trusted Lean compiler, standard audit commands, and reviewed source files. It is not a security system against deliberately forged compiler output. Review changes to the checker and manifest as well as proof-source changes.

## Review of mathematical meaning

Compare each printed endpoint type and each typed contract with `THEOREM_SPEC.md`. Inspect the shared definitions and the dependency chain that connects them to the original functional equation.

In particular, verify:

1. The coefficient function extracts coefficients of the actual normalized canonical solution. A recurrence-based construction has a proved functional-equation and uniqueness bridge.
2. Every required hypothesis is discharged where the result is applied. Neither a desired coefficient statement nor an equivalent recurrence bridge is simply assumed.
3. The inverse is the actual normalized two-sided compositional inverse.
4. The ring and parameter quantifiers are preserved, including rings with zero divisors, all odd integer parameters, and composite \(m\ge2\).
5. Both polynomial coefficient families specialize correctly and satisfy their divisibility statements.
6. The valuation representation handles zero correctly and the exact-exponent hypotheses have proved witnesses for nonzero inputs.
7. The typed contracts explicitly restate the expected propositions. They do not infer an expected type from the endpoint itself or refer to a different sequence with the same name.

A theorem of type `True` or \(P\to P\) can have a clean axiom report. This is why the type and definition review is required.

## Manuscript and reproducibility

If the manuscript changes, build it twice with `make paper`, inspect the resulting PDF, and replace the distributed PDF only with the synchronized result. Resolve mathematical inconsistencies and apply the small editorial corrections in `MANUSCRIPT_REVIEW.md`.

Keep theorem numbers and the Lean coverage map synchronized. Update the AI-contribution disclosure accurately while preserving the human author's responsibility. Do not label an unfinished result as proved by Lean.

Rerun the Python verifier if its source, the coefficient definition, or a mathematical claim it tests changes. Preserve exact arithmetic and independent construction from the original equation. Finite checks remain supplementary.

Record exact dependency commits, the toolchain, and final source hashes. Preserve old records as explicitly historical evidence or replace them with clearly labelled current records. A hash proves identity of source bytes, not correctness or novelty.

## Final delivery checklist

Return:

- Source, dependency lockfile, and reproducible setup/build instructions.
- All required endpoint proofs and reviewed typed contracts.
- Fresh complete-mode build, type, and axiom evidence.
- A coverage table and honest status report.
- A synchronized, self-contained manuscript if revised.
- A ZIP excluding dependency caches and toolchain binaries.

Do not convert a failed completion check into a successful status by skipping it, switching it to baseline mode, deleting endpoints, or relaxing the dependency checks. If any required proof remains unfinished, deliver the valid partial work with that boundary stated explicitly.
