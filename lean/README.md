# Lean formalizations

This directory is a single Lean 4 project containing formal proofs of the theorems stated in the papers in [`../preprints/`](../preprints/). The few steps that are proved only on paper are listed under `fidelity` in [`formalization.yaml`](formalization.yaml).

- **Toolchain:** Lean 4.35.0 ([`lean-toolchain`](lean-toolchain)). Every source file uses Lean's module system.
- **Library:** Mathlib v4.35.0 (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`); all dependency versions are pinned in [`lake-manifest.json`](lake-manifest.json).
- **Metadata:** [`formalization.yaml`](formalization.yaml), in the formalization.yaml v0.4 format used by the Palomar registry, records the sources, the scope, the authorship and, for each theorem compared by Comparator, the OEIS statement it corresponds to.
- **Per-paper notes:** [`docs/`](docs/) has one file per paper, mapping each statement in the paper to its Lean declarations.

The library was written by ChatGPT (OpenAI, GPT-6 with Pro reasoning). Claude Opus 5.5 later edited its module names, namespaces, comments and imports, ported it to Lean 4.35.0 and the module system, and wrote the Challenge and Solution modules and [`Families/ExpEquation.lean`](Families/ExpEquation.lean); see [`../AUTHORSHIP.md`](../AUTHORSHIP.md).

## Layout

| Path | Contents |
|---|---|
| [`Challenges/`](Challenges/) | One file per family of results. Each states the principal theorems using Mathlib's definitions only, with a docstring explaining each statement and its OEIS entry, and leaves the proofs as `sorry`. These are the statements a reader needs to audit. |
| [`Solutions/`](Solutions/) | The same theorems, word for word, proved from the library. |
| [`comparator/`](comparator/) | One Comparator configuration per family, naming the theorems that must match. |
| [`Entries/`](Entries/) | One file per OEIS entry, in the namespace `OEIS.Axxxxxx`, restating the results covered by the formalization in the notation of the library. |
| [`Hanna/Series/`](Hanna/Series/) | Foundations: composition of formal power series (Mathlib's substitution) and its coefficient formula, normalized series, coefficient-by-coefficient constructions, and compositional inverses. |
| [`Hanna/`](Hanna/) | The family $`A_m(xA_m-mxA_m^2)=x^2`$: parity, residues modulo $`m^2`$, binary-digit divisibility and prime exponents (A396843, A396844). |
| [`Hanna/Related/`](Hanna/Related/) | Scaled inverses $`A(x-x\,A(qx)/q)=x`$ (A393856–A393859). These files form the library `Related` (root file [`Related.lean`](Related.lean)). |
| [`Consecutive/`](Consecutive/) | Consecutive iterates $`F=x+F^{\circ r}F^{\circ(r+1)}`$ modulo $`2r`$, including negative iterates (A396099, A396798, A396807). |
| [`Families/`](Families/) | The remaining families: theta substitutions, rational theta sums and the bilateral theta-type equation (A378580, A378581, A380060, A380680, A355872), Catalan-type equations (A393171, A393172, A389536, A195194), equations with an exact halving step (A389474, A389475, A389537, A389542), and A396093, A392210, A396102, A380056, A397346, A394576. |
| [`scripts/`](scripts/) | [`verify-comparator.sh`](scripts/verify-comparator.sh), which runs Comparator on the configurations. |

## The statements checked by Comparator

[Comparator](https://github.com/leanprover/comparator), shipped with Lean as `lake comparator`, builds a Challenge module and its Solution module in a sandbox. It checks that every listed theorem of the Solution has exactly the statement of the Challenge, that it uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and that Lean's kernel accepts the proofs. The script below also replays the proofs through the independent NanoDa and con-ron kernels.

| Family | Configuration | Entries | Theorems |
|---|---|---|---|
| The family $`A(xA-mxA^2)=x^2`$ | [`hanna-family.json`](comparator/hanna-family.json) | A396843, A396844 | 8 |
| Consecutive iterates | [`consecutive-iterates.json`](comparator/consecutive-iterates.json) | A396099, A396798, A396807 | 5 |
| Scaled inverses | [`scaled-inverses.json`](comparator/scaled-inverses.json) | A393856–A393859 | 3 |
| Theta series and theta-type equations | [`theta.json`](comparator/theta.json) | A378580, A378581, A380060, A380680, A355872 | 9 |
| Catalan-type equations | [`catalan.json`](comparator/catalan.json) | A393172, A393171, A389536, A195194 | 9 |
| Equations with an exact halving step | [`halving.json`](comparator/halving.json) | A389537, A389542, A389474, A389475 | 9 |
| Further results | [`further-results.json`](comparator/further-results.json) | A396102, A397346, A394576 | 7 |
| Results with short proofs | [`short-results.json`](comparator/short-results.json) | A396093, A392210, A380056 | 6 |

All eight configurations are accepted by Lean's kernel, NanoDa and con-ron; the output is in [`../verification/results/comparator.log`](../verification/results/comparator.log).

## Building

Install [elan](https://github.com/leanprover/elan), which selects the pinned Lean version. Then, from this directory:

```sh
lake exe cache get   # optional: download prebuilt Mathlib instead of compiling it
lake build           # the libraries, Entries, Challenges and Solutions
```

To check a single entry, run `lake env lean Entries/A396843.lean`.

## Running Comparator

On Linux with [bubblewrap](https://github.com/containers/bubblewrap) installed, from this directory:

```sh
scripts/verify-comparator.sh                          # all eight configurations
scripts/verify-comparator.sh comparator/theta.json    # a single one
```

## Axiom audit

[`../verification/AxiomAudit.lean`](../verification/AxiomAudit.lean) asks Lean for the axioms behind each of the 240 theorems in `Entries/`, 5 general theorems cited in the papers, and the 56 theorems in `Solutions/`:

```sh
lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt
```

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Apart from the deliberate placeholders in `Challenges/`, the sources contain no `sorry`, no added axioms, and no `native_decide` or `implemented_by`.

## Key definitions

- `Hanna.Series.compose A B` is the composition $`A(B(x))`$. It is definitionally equal to Mathlib's `PowerSeries.subst B A`, which the Challenges use, and it is used only when $`B`$ has constant term 0.
- `Hanna.Series.Normalized A` means $`A=x+O(x^2)`$.
- `Consecutive.iter F k` is the $`k`$-th compositional iterate, written `(fun G => F.subst G)^[k] X` in the Challenges; `Consecutive.ziter F hF k` extends it to integers $`k`$ using the compositional inverse.
- `PowerSeries.map (Int.castRingHom (ZMod m)) A` is the reduction of $`A`$ modulo $`m`$.
- `PowerSeries.invOfUnit A 1` is the multiplicative inverse of a series with constant term 1.
