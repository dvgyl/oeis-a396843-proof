# Lean formalizations

This directory is a single Lean 4 project containing formal proofs of every theorem stated in the papers in [`../preprints/`](../preprints/).

- **Toolchain:** Lean 4.19.0 ([`lean-toolchain`](lean-toolchain)).
- **Library:** Mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all dependency versions are pinned in [`lake-manifest.json`](lake-manifest.json).
- **Catalogue:** [`formalization.yaml`](formalization.yaml) lists the papers, the main declarations and the scope of the formalization.
- **Per-paper notes:** [`docs/`](docs/) has one file per paper, mapping each statement in the paper to its Lean declarations.

The formalization was written by ChatGPT (OpenAI, GPT-6 with Pro reasoning).

## Layout

| Path | Contents |
|---|---|
| [`Entries/`](Entries/) | One file per OEIS entry, in the namespace `OEIS.Axxxxxx`. Each file states the defining equation of the sequence, the uniqueness of its solution, and every result of the paper with explicit types. |
| [`Hanna/Series/`](Hanna/Series/) | Foundations: composition of formal power series (Mathlib's `MvPowerSeries.subst`) and its coefficient formula, normalized series, coefficient-by-coefficient constructions, and compositional inverses. |
| [`Hanna/`](Hanna/) | The family $`A_m(xA_m-mxA_m^2)=x^2`$: parity, residues modulo $`m^2`$, binary-digit divisibility and prime exponents (A396843, A396844). |
| [`Hanna/Related/`](Hanna/Related/) | Scaled inverses $`A(x-x\,A(qx)/q)=x`$ (A393856–A393859). |
| [`Consecutive/`](Consecutive/) | Consecutive iterates $`F=x+F^{\circ r}F^{\circ(r+1)}`$ modulo $`2r`$, including negative iterates (A396099, A396798, A396807). |
| [`Families/`](Families/) | The remaining families: theta substitutions and rational theta sums (A378580, A378581, A380060, A380680), Catalan-type equations (A393171, A393172, A392210, A389536, A397588, A195194), reversions with an exact halving step (A389474, A389475, A389537, A389542), and A396093, A396102, A380056. |

## Building

Install [elan](https://github.com/leanprover/elan), which selects the pinned Lean version. Then, from this directory:

```sh
lake exe cache get   # optional: download prebuilt Mathlib instead of compiling it
lake build           # the libraries Hanna, Consecutive, Related and Families
lake build Entries   # the 26 entry files
```

To check a single entry, run `lake env lean Entries/A396843.lean`.

## Axiom audit

[`../verification/AxiomAudit.lean`](../verification/AxiomAudit.lean) asks Lean for the axioms behind each of the 224 theorems in `Entries/` and 5 general theorems cited in the papers:

```sh
lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt
```

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The sources contain no `sorry`, no added axioms, and no `native_decide` or `implemented_by`.

## Key definitions

- `Hanna.Series.compose A B` is the composition $`A(B(x))`$, defined as `MvPowerSeries.subst`; it is used only when $`B`$ has constant term 0.
- `Hanna.Series.Normalized A` means $`A=x+O(x^2)`$.
- `Consecutive.iter F k` is the $`k`$-th compositional iterate; `Consecutive.ziter F hF k` extends it to integers $`k`$ using the compositional inverse.
- `PowerSeries.map (Int.castRingHom (ZMod m)) A` is the reduction of $`A`$ modulo $`m`$.
- `PowerSeries.invOfUnit A 1` is the multiplicative inverse of a series with constant term 1.
