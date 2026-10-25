# Proofs and corrections of OEIS conjectures

A collection of proofs, disproofs and corrections of conjectures recorded in the [On-Line Encyclopedia of Integer Sequences](https://oeis.org) (OEIS), each with a self-contained paper and a Lean 4 formalization of its main theorems. The collection currently contains 29 papers.

## Background

This project is an AI research effort that I directed. ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning, worked autonomously from my prompts: it searched the OEIS for suitable conjectures, found the proofs and counterexamples, and wrote the Lean formalization. I chose which problems to pursue and asked for proofs, formal verification and revisions, but I did not supply proof ideas. I then used Claude Opus 5.5 with Claude Code to check the work independently and to write the papers in their present form.

I have personally reviewed the AI-generated proofs to the best of my mathematical ability. The accompanying Lean formalizations have been machine-checked, but my review should not be considered independent expert validation. I make no claims regarding the novelty of these results and welcome further scrutiny, corrections, and feedback from the mathematical community. They have NOT been peer reviewed. An OEIS entry that labels a statement as a conjecture shows only that its contributor did not know a proof. The searches for earlier work were limited, and I claim no priority. Results that turned out to be known were removed from the collection, and earlier work that bears on the remaining entries is credited in the papers. The precise attribution of each contribution is in [AUTHORSHIP.md](AUTHORSHIP.md).

— Dev D. Goyal

## Results

Most of the sequences are coefficients of formal power series defined by functional equations, and most of the conjectures concern their residues modulo small integers. In 24 entries the conjectures treated are proved, and in A392210 an observation recorded in the entry is proved. In four entries (A380680, A396798, A396843 and A396844) a conjectured statement is false; the papers give counterexamples and prove the correct statements, and in A396798 and A396843 the other conjectured statements are proved. Where an entry records further conjectures that are not treated, the paper says so.

The papers form six families of related results and a group of other results:

| Family | Papers |
|---|---|
| The family $`A_m(xA_m-mxA_m^2)=x^2`$ | A396843, A396844 |
| Consecutive iterates $`F=x+F^{\circ r}F^{\circ(r+1)}`$ | A396099, A396798, A396807 |
| Scaled inverses $`A(x-x\,A(qx)/q)=x`$ | A393856, A393857, A393858, A393859 |
| Theta series and theta-type equations | A378580, A378581, A380060, A380680, A355872 |
| Catalan-type equations | A393172, A393171, A389536, A397588, A195194 |
| Equations with an exact halving step | A389537, A389542, A389474, A389475 |
| Other results | A396093, A392210, A396102, A380056, A397346, A394576 |

## Navigating the collection

- The [overview](overview.pdf) describes every result.
- The [manuscript map](CONTENTS.md) lists the papers by family, with the result, status and abstract of each.
- The [`preprints/`](preprints/) directory contains, for each paper, the PDF, the LaTeX source and a BibTeX citation.
- The [Lean library](lean/README.md), the [formalization catalogue](lean/formalization.yaml) and the [per-paper notes](lean/docs/) describe the formal proofs and the declarations corresponding to each paper.
- The [`verification/`](verification/README.md) directory contains the axiom audit of the formal proofs and the numerical checks against the published OEIS data.

## Verification

- **Formal proofs.** The Lean project builds from source with Lean 4.19.0 and Mathlib (commit `c44e0c8`). The 244 theorems stated in [`lean/Entries/`](lean/Entries/), and 5 general theorems cited in the papers, depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The sources contain no `sorry`.
- **Definitions.** For each entry, the Lean definition of the sequence has been compared with the definition in the OEIS entry. Where the formal statement uses an equivalent form, the paper proves the equivalence; these cases are listed in the [formalization catalogue](lean/formalization.yaml).
- **Numerical checks.** Each sequence is recomputed from its OEIS definition and compared with the published terms, and each theorem and each observation in the Discussion sections is tested over a range of indices. All 363 checks pass; see [`verification/`](verification/README.md).

## Citations

Each paper's directory under [`preprints/`](preprints/) contains a BibTeX entry. The sequences and conjectures were contributed to the OEIS by Paul D. Hanna, except A394576, which was contributed by Hoang Xuan Thanh; when citing a result, please also cite the corresponding OEIS entry.

OEIS text quoted in the papers is © The OEIS Foundation Inc. and is used under CC BY-SA 4.0.
