# Contributing

This package contains a mathematical manuscript, finite computations, and a Lean development. A change should identify which of those it affects.

## Mathematical changes

State the exact claim being changed, all hypotheses, and the coefficient indexing convention. Give an argument that addresses every permitted parameter, including composite values when the claim covers them. Explain any appeal to formal composition, inversion, or reduction modulo an integer.

A finite search can suggest a theorem or find a counterexample. It cannot establish an assertion about all coefficients. If a theorem is strengthened, include its proof and update the examples and related corollaries consistently.

For a correction to a source attribution or priority statement, provide an identifiable primary source and explain the relationship to the claim here.

## Computational changes

Keep coefficient construction independent of the formulas being tested. Preserve exact integer arithmetic. Run:

```bash
python3 scripts/verify_hanna_congruences.py --terms 100
```

Explain changes to the output or checked scope. Regenerate `reproducibility/verification_100.json` and its environment record if the verifier changes. State the Python version and the command actually run.

## Manuscript changes

Run `make paper` and inspect the generated PDF. Check equations, definitions, cross-references, page breaks, and the bibliography. Keep the text self-contained: the reader should not need the code or the project history to understand a proof.

## Lean changes

Follow the pinned toolchain and build instructions in `lean/README.md`. Include a successful build for any declaration described as checked. Do not add `sorry`, `admit`, an extra axiom, or an unsafe computational shortcut to close a mathematical proof.

If a theorem assumes an intermediate mathematical property, describe it as conditional until that property is proved and connected to the intended series. A compiled conditional theorem is not a formalization of the full unconditional result.

Update the Lean status document whenever the boundary between checked results and remaining work changes. Report the actual axioms on which the key declarations depend.

## Attribution and licensing

Identify substantial AI assistance or external contributions accurately. Do not attribute independent human verification unless it occurred. The human author remains responsible for submitted claims and attribution.

No license grant is included in this package. Contact the author before you submit material that needs a license agreement.
