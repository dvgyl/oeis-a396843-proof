# Manuscript proof audit and revision

The audit found no genuine gap that required a theorem change. The formal proof preserves all required hypotheses, ranges, coefficient rings, and conclusions. A separate AI source review found that the final types match the specification. The user has since confirmed that human verification is complete. The confirmation preceded the citation edits described below. No further details of that verification were supplied.

## Changes made

1. The inverse proof now says “addition, subtraction, and multiplication.” The recursive step uses negation, such as the identity `b₂ = -a₂`.
2. Remark 6.2 now says “sums, products, and negatives.” The inverse recurrence contains minus signs.
3. The existence proof now states finite dependence explicitly. For degree `d ≥ 2`, the defining expression uses only coefficients through index `d - 1`. Later recursive choices therefore preserve every fixed coefficient identity.
4. The AI disclosure records the subsequent proof audit and revisions. Dev Goyal's authorship and responsibility statement remain in place.
5. The follow-up citation review adds local credit for Hanna's recorded inverse identity. It adds the five source author dates and Asaria's exact counterexample and correction date.
6. The abstract states the parity result without the word “settling”. The disclosure records the citation checks, literature search, and confirmation of human verification.

The theorem statements and their numbering are unchanged. The paper retains its written proof modulo the parameter squared. Lean proves the same conclusion from the actual coefficient recurrences. [COVERAGE.md](COVERAGE.md) explains this alternate proof and the shared series definitions.

## Matters checked during formalization

- Substitution is actual Mathlib substitution. Each use of its identities has the required zero constant coefficient.
- Existence and uniqueness hold over every commutative ring with identity, including rings with zero divisors.
- The compositional inverse is normalized, unique, and two-sided.
- The coefficient recurrences follow from the defining equation and the proved inverse identities.
- The simultaneous binary induction uses the full Cauchy product. Every previously used coefficient has a smaller index, except the solution coefficient proved immediately before the inverse coefficient at the same index.
- Both polynomial coefficient families specialize to the actual integer coefficients.
- Exact prime exponents exist uniquely for nonzero integers. Zero has no finite exact exponent. The lower bound is expressed by divisibility and therefore includes zero coefficients.

## PDF and attribution

The public manuscript was built twice after its contribution statement changed. The distributed PDF was copied from that output. All pages were rendered and inspected. [The manuscript evidence](../reproducibility/manuscript/inspection.json) records the source and PDF hashes, page count, and inspection scope.

Paul D. Hanna's OEIS attribution and Danial Asaria's prior counterexample attribution are preserved. The [public review summary](PUBLIC_REVIEW.md) states the citation, novelty-search, and audit limits. No journal review is claimed. No license grant is included.
