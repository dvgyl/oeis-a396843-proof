# Lean 4 formalization

This folder is a single Lean 4 project. It proves every theorem of the 34 papers in [`../papers/`](../papers/).

Lean is a *proof assistant*: a program in which mathematical statements and their proofs are written in a precise formal language, and every step is checked by the computer down to the basic rules of logic. You do not need to read Lean to use the papers; this folder is for readers who want to inspect or rerun the formal proofs.

- **Toolchain:** Lean 4.19.0 ([`lean-toolchain`](lean-toolchain)).
- **Library:** Mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All dependency versions are pinned in [`lake-manifest.json`](lake-manifest.json).
- **Size:** 101 Lean files.
- **Trust:** no `sorry`, no added axioms, no `native_decide`, no `implemented_by`. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (see [`../verification/`](../verification/)).

The Lean code was written by ChatGPT (OpenAI, GPT-6 with Pro reasoning). The exception is `More/StirlingNumbers.lean`, which is adapted from Mathlib (see [`../third_party/mathlib/NOTICE.md`](../third_party/mathlib/NOTICE.md)). Claude Opus 5.5, used with Claude Code, rebuilt and audited it, and changed only comments (attribution text); see [`../AUTHORSHIP.md`](../AUTHORSHIP.md).

## Where to look

**Start with [`Entries/`](Entries/).** There is one file per OEIS entry, for example [`Entries/A396093.lean`](Entries/A396093.lean). Each file:

- states that entry's theorems with explicit types, in the namespace `FinalCollection.Axxxxxx`,
- proves them by calling the shared modules below.

The section "Checking the results" of each paper has a table that maps every statement in the paper to these theorem names. [`Entries.lean`](Entries.lean) imports all 34 files.

Every entry file also states the definition of its sequence. That is either the defining equation of the OEIS entry, together with the uniqueness of its solution, or the finite formula in the entry. So a reader can check that the theorems are about the right sequence without reading the shared modules. The papers explain the few places where the OEIS title differs from the formula used in Lean. These are: the e.g.f. versus the Stirling sum for the seven periodicity entries, the two-sided versus the one-sided sum for A380060 and A380680, and the nested title versus the functional equation for A392210.

## Build

You need [elan](https://github.com/leanprover/elan), which installs the pinned Lean version. Then, from this folder:

```sh
lake exe cache get   # downloads prebuilt Mathlib files; skip it to compile Mathlib from source (several hours)
lake build           # builds the libraries Hanna, Consecutive, Related, More, Round3, Round4
lake build Entries   # builds the 34 entry files
```

To check one entry, run `lake env lean Entries/A396843.lean`. To print the axioms of all 262 entry theorems (and of 6 general theorems that the papers cite), run `lake env lean ../verification/AxiomAudit.lean`.

[`ContractChecks.lean`](ContractChecks.lean) contains 92 `example`s kept from the research. They restate, with explicit types, the key definitions (for instance, that `compose` *is* `MvPowerSeries.subst`) and the main results, and check them against the implementations. It compiles with `lake env lean ContractChecks.lean`.

## Shared modules

| Folder | What it proves | Used by |
|---|---|---|
| `Hanna/Series/` | Formal power series foundations. Composition is Mathlib's `MvPowerSeries.subst`, and its coefficient formula is proved here. Also: unique normalized solutions built coefficient by coefficient, and compositional inverses | everything |
| `Hanna/` | The family A_m(xA_m − m·xA_m²) = x²: existence, parity, residues mod m², binary-digit divisibility, prime exponents | A396843, A396844 |
| `Hanna/Related/` | The scaled inverse family A(x − x·A(qx)/q) = x | A393856–A393859 |
| `Consecutive/` | F = x + F^∘r·F^∘(r+1) modulo 2r, including integer (negative) iterates | A396099, A396797, A396798, A396807 |
| `More/` | Stirling numbers and transforms, power and tail periodicity (`StirlingNumbers`, `StirlingTransform`, `PowerPeriodicity`, `TailPeriodicity`, `StirlingPeriodicity`) | the seven periodicity entries |
| `More/` | `RationalParity` (A396093), `CubicReversion`/`CubicFrobenius`/`CubicConsequences` (A389474, A389475), `InverseIterate` (A396102) | as named |
| `Round3/` | `ThetaSubstitution` (A378580, A378581), `DifferentialParity` (A397588), `MahlerParity` (A389536), `LacunaryInverse` (A389537), `SquareReversion` (A389542), `ModFour` (helper) | as named |
| `Round4/` | `NestedReversion` (A195194), `CatalanComposition` and `SquareComposition` (A393171, A393172), `NestedBinomial` (A392210), `ExpCosine` (A380056), `ThetaRational` (A380060, A380680) | as named |
| `*Contracts.lean` | Restatements of the main results with explicit types, kept from the research rounds | `ContractChecks.lean` |

The folder names `More`, `Round3` and `Round4` reflect the order in which the research was done. They do not mark any difference in status.

## Key definitions

- `Hanna.Series.compose A B` is the composition A(B(x)), defined as `MvPowerSeries.subst`. It is used only when B has constant term 0.
- `Hanna.Series.Normalized A` means A = x + O(x²).
- `Consecutive.iter F k` is the k-th compositional iterate. `Consecutive.ziter F hF k` extends it to integer k, using the genuine compositional inverse.
- `PowerSeries.map (Int.castRingHom (ZMod m)) A` is the reduction of A modulo m.
- `PowerSeries.invOfUnit A 1` (also called `unitInv`) is the multiplicative inverse of a series with constant term 1.
