# History: earlier material, kept for the record

This folder keeps earlier versions of the work exactly as they were produced. Nothing here is needed to read or check the current results; those are in [`../papers/`](../papers/), [`../lean/`](../lean/) and [`../verification/`](../verification/). The files are kept so that anyone can see what the AI system originally produced, and how the current versions differ from it.

Some of these older files call the author "Dev Goyal". The author's full name is **Dev D. Goyal**. The old files were left unchanged on purpose, so that they remain an accurate record.

## `original-release/`: the first result (A396843)

This is the first public release of this repository. It covered only the original problem: the OEIS entry [A396843](https://oeis.org/A396843) and the family of series A_m with A_m(x·A_m − m·x·A_m²) = x². It contains:

- the report `manuscript/hanna_congruences.pdf` with its LaTeX source;
- the Lean project's configuration files as they were at the time (`lean/`). Its Lean proofs, the folder `Hanna/` and the file `Hanna.lean`, were carried over byte for byte into the current project and are not duplicated here: see [`../lean/Hanna/`](../lean/Hanna/);
- the scripts, tests and verification logs used then.

This release is archived on Zenodo with DOI [10.5281/zenodo.23567463](https://doi.org/10.5281/zenodo.23567463). It was produced by ChatGPT (OpenAI) from prompts by Dev D. Goyal; see its own [README](original-release/README.md). Its results are included, and re-proved, in the current [`../lean/`](../lean/) project and in the papers [A396843](../papers/A396843.pdf) and [A396844](../papers/A396844.pdf).

## `chatgpt-collection/`: ChatGPT's final collection of 34 entries

This is the archive `OEIS_Final_Collection_Dev_Goyal.zip`, which ChatGPT (OpenAI, GPT-6 with Pro reasoning) produced at the end of the research. It is kept as delivered, with three exceptions:

| In the archive | Where it is now | Why |
|---|---|---|
| `lean/` | [`../lean/`](../lean/) | This is the current Lean project. Only comments were changed: the author's name, and outdated "review pending" notes. |
| `third_party/` | [`../third_party/`](../third_party/) | License notice for the adapted Mathlib code. |
| `manuscript/` (four combined papers) | `combined-manuscripts/` | Renamed, so that it is not confused with `manuscripts/`. |

As a result, links inside this folder that point to `lean/`, `third_party/` or `manuscript/` no longer resolve; use the locations above instead.

What the folder contains:

| Path | Contents |
|---|---|
| `README.md`, `INDEX.md` | ChatGPT's own overview and index of the 34 entries |
| `AI_DISCLOSURE.md` | ChatGPT's own AI disclosure |
| `manuscripts/` | ChatGPT's original 34 papers (PDF and LaTeX). The papers in [`../papers/`](../papers/) are rewritten versions of these, with the same theorems and proof strategies |
| `combined-manuscripts/` | Four earlier combined papers, one per research round |
| `docs/` | ChatGPT's coverage ledgers, proof notes and internal reviews for each round |
| `catalogue/` | Machine-readable maps from papers to Lean theorems |
| `validation/`, `reproducibility/`, `scripts/`, `tests/` | ChatGPT's own verification tools and reports |
| `prior_work/` | Earlier archives from the same research (versions 1 to 3) |
| `SHA256SUMS` | ChatGPT's checksums for the delivered archive (they cover the original layout) |

The account of how the research unfolded, which ChatGPT wrote at the end of the project, is in [`../docs/research-retrospective.md`](../docs/research-retrospective.md).
