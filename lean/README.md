# Lean formalization

All 16 endpoints in `Hanna.Acceptance` are proved against Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The exact transitive dependency commits are in `lake-manifest.json`.

The proofs use actual Mathlib `PowerSeries` objects and `MvPowerSeries.subst`. They construct the unique normalized solution before choosing it. They also construct its unique normalized two-sided compositional inverse. The coefficient recurrences are conclusions of these series identities.

See [the coverage table](../docs/COVERAGE.md), [explicit contracts](ContractChecks.lean), and [the complete-check report](../reproducibility/lean_complete/report.json).

## Build and validate

Install Python 3.10 or later, Git, and Elan. From the repository root, run:

```sh
python3 scripts/setup_lean.py
python3 scripts/check_formalization.py --mode baseline
python3 scripts/check_formalization.py --mode complete
```

Each script accepts `--lake /absolute/path/to/lake`. The setup script fetches locked dependencies and runs the Mathlib cache tool through the Lean interpreter.

For an incremental proof build, run `lake build` from `lean/`. Use complete mode for final evidence. It runs `lake clean hanna`, rebuilds the library, compiles `ContractChecks.lean` to a fresh object, prints all required types, and audits all required proof dependencies.

## Modules

| Module | Content |
| --- | --- |
| `Hanna.BinaryWeight` | Original 15 binary digit-count theorems |
| `Hanna.Divisibility` | Original eight integer divisibility theorems |
| `Hanna.Series.Basic` | Normalization, actual substitution, finite coefficient formula, composition laws, coefficient maps |
| `Hanna.Series.Triangular` | Coefficient recursion for a triangular operator |
| `Hanna.Series.Filtration` | Coefficient agreement and the defining equation's perturbation bound |
| `Hanna.Series.Construction` | Existence, uniqueness, the canonical solution, and coefficient maps |
| `Hanna.Series.Inverse` | Existence and uniqueness of both compositional inverse identities |
| `Hanna.Canonical` | Actual solution, inverse, integer coefficients, polynomial coefficients, specialization |
| `Hanna.Recurrences` | Shifted series and both coefficient recurrences |
| `Hanna.Parity` | Odd and even integer parameters |
| `Hanna.BinaryDivisibility` | Simultaneous solution and inverse divisibility over every commutative ring |
| `Hanna.ModSquare` | Full residue classification and the parameter-three and parameter-four cases |
| `Hanna.PrimeExponent` | Exact prime exponent, nonzero existence and uniqueness, and the zero case |
| `Hanna.Corollaries` | Prime lower bound and exact minimum-exponent classification |
| `Hanna.Acceptance` | All 16 fixed public theorem endpoints |

## Verification scope

`ContractChecks.lean` independently states the expected propositions. It also checks the definitions of composition, normalization, coefficients, and exact prime exponent. It checks that the chosen series satisfies the defining equation and both inverse identities.

The accepted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are no proof admissions, custom mathematical axioms, `unsafe` proofs, or `native_decide` proofs. The axiom audit and the separate type review support these claims.

The original two arithmetic modules are unchanged. The validation scripts and both theorem manifests are unchanged. The final package excludes `.lake/` and all compiled objects. Reports retain the hashes of the fresh contract objects as records of their compilation.
