# Proofs and corrections of OEIS conjectures

This repository contains 26 papers on conjectures recorded in the [On-Line Encyclopedia of Integer Sequences](https://oeis.org) (OEIS), together with Lean 4 formalizations of all their theorems.

Most of the sequences are coefficients of formal power series defined by functional equations, and most of the conjectures concern their residues modulo small integers. In most entries the conjectured statements are proved. In four entries (A380680, A396798, A396843 and A396844) a conjectured statement is false; the papers give counterexamples and prove the correct statements.

The results were obtained in an autonomous AI research effort directed by Dev D. Goyal (see [How the results were produced](#how-the-results-were-produced)). They have not been peer reviewed.

## Navigating the collection

The 26 papers are organized into 7 families of related results.

- Start with the [overview](overview.pdf) for a description of every result.
- Use the [manuscript map](CONTENTS.md) to find individual papers, their abstracts and their status.
- The [`preprints/`](preprints/) directory contains, for each paper, the PDF, the LaTeX source and a BibTeX citation.
- The [Lean library](lean/README.md), the [formalization catalogue](lean/formalization.yaml) and the [per-paper notes](lean/docs/) describe the formal proofs and the declarations corresponding to each paper.
- The [`verification/`](verification/README.md) directory contains independent numerical checks against the published OEIS data and the axiom audit of the formal proofs.

| Family | Papers |
|---|---|
| The family $`A_m(xA_m-mxA_m^2)=x^2`$ | A396843, A396844 |
| Consecutive iterates $`F=x+F^{\circ r}F^{\circ(r+1)}`$ | A396099, A396798, A396807 |
| Scaled inverses $`A(x-x\,A(qx)/q)=x`$ | A393856, A393857, A393858, A393859 |
| Theta series modulo 4 | A378580, A378581, A380060, A380680 |
| Catalan-type equations | A393172, A393171, A392210, A389536, A397588, A195194 |
| Reversions with an exact halving step | A389537, A389542, A389474, A389475 |
| Other results | A396093, A396102, A380056 |

## How the results were produced

- **ChatGPT** (OpenAI), using the GPT-6 model with Pro reasoning, worked autonomously from prompts by Dev D. Goyal. It selected the conjectures, found the proofs and counterexamples, and wrote the Lean formalization.
- **Claude Opus 5.5**, used with Claude Code, checked the work independently. It rebuilt the Lean project from source and audited its axioms, compared the Lean definitions with the OEIS definitions, recomputed every sequence in separately written PARI/GP code, and read every proof. It then wrote the papers in their present form, including the remarks in their Discussion sections.
- **Dev D. Goyal** chose the problems, directed the work and has verified the results. Dev D. Goyal did not supply proof ideas.

An OEIS entry that labels a statement as a conjecture shows only that its contributor did not know a proof. Only limited searches for earlier work were made, and no priority is claimed. Earlier results that bear on these entries are credited in the papers.

## Verification

- **Formal proofs.** The Lean project builds from source with Lean 4.19.0 and Mathlib (commit `c44e0c8`). The 224 theorems stated in [`lean/Entries/`](lean/Entries/), and 5 general theorems that the papers cite by name, depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The sources contain no `sorry`.
- **Definitions.** For each entry, the Lean definition of the sequence was compared with the definition in the OEIS entry. Where the formal statement uses an equivalent form, the paper proves the equivalence; these cases are listed in the [formalization catalogue](lean/formalization.yaml).
- **Numerical checks.** Every sequence is recomputed from its OEIS definition and compared with the published terms, and every theorem and every observation in the Discussion sections is tested over a range of indices. All checks pass; see [`verification/`](verification/README.md).

## Citations

To cite an individual paper, use the BibTeX block in its directory under [`preprints/`](preprints/). All 26 sequences and the conjectures treated here were contributed to the OEIS by Paul D. Hanna; when citing a result, please also cite the corresponding OEIS entry.

OEIS text quoted in the papers is © The OEIS Foundation Inc. and is used under CC BY-SA 4.0.
