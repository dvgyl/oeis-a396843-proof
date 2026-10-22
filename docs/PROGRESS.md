# Formalization status

All 16 endpoints in the fixed [theorem specification](THEOREM_SPEC.md) are proved for the actual canonical Mathlib formal power series and its normalized two-sided compositional inverse. The original 23 supporting theorems remain. No required mathematical goal remains unresolved.

The [coverage table](COVERAGE.md) maps the report to the Lean declarations. The [complete-check report](../reproducibility/lean_complete/report.json) records the clean build, explicit typed contracts, theorem types, transitive axioms, and source hashes. The user has confirmed that human verification is complete. The [public review summary](PUBLIC_REVIEW.md) states the scope and limits of the other reviews.

The written proof is in the report. The Python verifier checks finite examples for parameters 2 through 9 and the first 100 positive-degree coefficients. These computations are separate from the Lean proofs for all indices.

The complete Lean check verifies the stated propositions under Lean's kernel and the permitted standard axioms. It does not establish global novelty, historical priority, or the status of any external sequence entry. The bounded literature search found no earlier proof of the full stated results. The report makes no claim of a first proof or peer review.
