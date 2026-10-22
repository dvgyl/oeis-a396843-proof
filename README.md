# An AI-developed proof for OEIS A396843 and related series

This package contains a mathematical report, Lean proofs, and exact finite checks for a family of formal power series. ChatGPT (OpenAI) developed the mathematical arguments and Lean formalization autonomously from prompts by Dev Goyal. Dev initiated the investigation and requested checks and revisions. He did not supply the proof strategy or intermediate mathematical arguments. Dev has confirmed that human verification is complete. He is the sole human author and accepts responsibility for this release.

The public source repository is [dvgyl/oeis-a396843-proof](https://github.com/dvgyl/oeis-a396843-proof). The [Zenodo record](https://zenodo.org/records/23567463) has DOI [10.5281/zenodo.23567463](https://doi.org/10.5281/zenodo.23567463).

Paul D. Hanna recorded the series for parameters 1 through 5 in the On-Line Encyclopedia of Integer Sequences (OEIS). Danial Asaria identified a prior counterexample to a residue conjecture. The [report](manuscript/hanna_congruences.pdf) gives the full credit and references.

The series is the unique normalized solution of

```text
A_m(x A_m(x) - m x A_m(x)^2) = x^2,   A_m(x) = x + O(x^2).
```

The report proves parity, a complete residue formula modulo `m²`, and divisibility controlled by the number of ones in the binary expansion of an index. It also treats the compositional inverse. The Lean project proves all 16 specified endpoints for the actual canonical series. See the [theorem specification](docs/THEOREM_SPEC.md) and [coverage table](docs/COVERAGE.md).

## Read and check the result

- [Report PDF](manuscript/hanna_congruences.pdf) and [LaTeX source](manuscript/hanna_congruences.tex) contain the written proof.
- [Lean README](lean/README.md) gives the module map and build instructions.
- [Current verification evidence](reproducibility/README.md) gives the build, type, axiom, parser, and finite-check records.
- [Public review summary](docs/PUBLIC_REVIEW.md) states the contribution record and review limits.

Install Python 3.10 or later, Git, and Elan. From this directory, run:

```sh
python3 scripts/setup_lean.py
python3 -m unittest discover -s tests -p 'test_*.py'
python3 scripts/check_formalization.py --mode baseline
python3 scripts/check_formalization.py --mode complete
python3 scripts/verify_hanna_congruences.py --terms 100
```

Elan selects Lean 4.19.0 from `lean/lean-toolchain`. The lockfile fixes the Mathlib revision and its dependencies. The setup command downloads required sources and caches. The complete check cleans and builds the first-party Lean library. It compiles the explicit contracts and records types and transitive axioms for all 16 endpoints. The finite Python check tests examples; it does not prove an all-index statement.

Run `make paper` to rebuild the PDF. Run `python3 scripts/package_public.py` to create and verify the source ZIP. The ZIP excludes dependency caches and compiled objects. No license grant is included in this package.
