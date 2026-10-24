# Independent AI semantic review: rational theta sums

Reviewed on 24 October 2026 for Dev Goyal by an AI review agent separate from the authoring agent. This is an independent check within the AI workflow, not independent human peer review. Human review remains pending.

## Result

No semantic defect was found in the reviewed version of `Round4.ThetaRational` or its explicit acceptance contracts. The definitions correspond to **formula (2)** in the official A380060 and A380680 entries, and the unbounded results have the intended coefficient ranges. The A380680 result is a refutation and correction of the retrieved conjecture, not a proof of that conjecture as written.

## Source correspondence

The reviewer independently retrieved [A380060](https://oeis.org/A380060) and [A380680](https://oeis.org/A380680). Both source entries have offset `0,2`. Their formula (2) is the positive-index rational sum used in the formalization. The index `k` in Lean corresponds to the source's positive index `j=k+1`; there is no omitted first summand or duplicated zero-index contribution. The separate constant `1` is included.

The source's bilateral expressions involve negative exponents and rational simplification. The present formalization works directly from the independently listed positive-index formula (2). It does **not** separately formalize the equivalence to a bilateral Laurent-series expression, and should not be described as doing so. This is sufficient source identification because formula (2) is itself stated in each official entry.

## Inversion and finite support

For every series `A` and every `k≥0`, the denominator is `1−X^(k+1) A`, whose constant coefficient is exactly one. The inherited `unitInv` is Mathlib's `PowerSeries.invOfUnit A 1`; its multiplication identities are only applied with the constant-coefficient-one hypotheses established. In particular, `ratio_quotient` proves the literal numerator-denominator identity.

Each summand contains `X^((k+1)^2)`, so a coefficient of degree `n` vanishes whenever `n<(k+1)^2`. The chosen finite range `k<n+1` contains every possible nonzero summand. The theorem `sigma_coeff_finsum` also proves the equality to the coefficientwise finitely supported sum; a finite cutoff is not simply assumed to approximate the source sum. No analytic convergence claim is used.

## Existence, uniqueness, and coefficient reduction

The ratio's difference preserves `X^n` divisibility because both denominators are genuine units. Ordinary powering preserves this divisibility, and the positive prefactor `X^((k+1)^2)` raises it by at least one. Consequently `step(A)−step(B)` is divisible by `X^(n+1)` whenever `A−B` is divisible by `X^n`.

The triangular recursion includes the constant coefficient, so it constructs the entire implicit A380060 solution and forces that coefficient to one. The uniqueness theorem ranges over all formal series satisfying the equation, without assuming the target parity or a favorable coefficient table. The construction and the locally finite sum commute with arbitrary coefficient ring homomorphisms.

## Residue calculations

For A380060, reduction of the defining equation modulo two immediately gives `A=1`. At that value the rational ratio equals one identically, so the reduced sum contains precisely one monomial at every positive square index. The existing verified modulus-four helper transfers equality modulo two into equality of doubled series modulo four. This yields the complete series reduction `1+2 Σ X^(j²)` and the two coefficient cases for every positive `n`.

For A380680, the parameter is the constant series two. It reduces to zero modulo two. The ratio then equals `X^j` in characteristic two, and the whole summand is `X^(2j²)`. The same doubled-series transfer gives `1+2 Σ X^(2j²)` modulo four. The single-support proof uses uniqueness of the positive square root to exclude duplicate contributions; the conclusion is an indicator at twice-square indices, not a count with an unexamined multiplicity.

The condition `n>0` removes the constant coefficient, and the source's square predicate is equivalent to the positive-square predicate on this range. The source equations and coefficient conclusions are exposed again in `ThetaRationalContracts`; the canonical functions are not substituted into an unrelated auxiliary statement.

## Refutations

The formal proof derives `a(1)=4` and `a(2)=6` from the actual explicit source formula. Thus the proposed square-index residue condition fails at index one, and the proposed nonsquare divisibility condition fails at index two. The two negated universal statements are separately proved. These are exact mathematical counterexamples, not failures of a finite test or a shifted indexing convention.

## Verification scope

This review examined the mathematical meaning of the source, the actual Lean definitions and theorem statements, and the main proof dependencies. It did not substitute for the release's fresh compiler and transitive-axiom audit; the final integrated verification report records those mechanical results. It also does not establish exhaustive novelty, asymptotic behavior, or analytic convergence.

## Reviewed file hashes

The following SHA-256 hashes identify the reviewed source snapshot.

| File | SHA-256 |
|---|---|
| `lean/Round4/ThetaRational.lean` | `3888b23af84152036a02ac4b9a39a21354480b4398576a121cc695393c4c2f7d` |
| `lean/Round4/ThetaRationalContracts.lean` | `b869d0ea7ac540d7c58842d3db838869ba8e8699835270acf8ac6ab29d96d49d` |
