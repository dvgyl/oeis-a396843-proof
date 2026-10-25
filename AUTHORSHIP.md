# Authorship and AI disclosure

**Author:** Dev D. Goyal.

The results in this repository were obtained in an AI research effort directed by Dev D. Goyal, in which ChatGPT worked autonomously. This page records the contribution of each participant.

## Contributions

**Dev D. Goyal** initiated and directed the project, choosing which of the proposed problems to pursue, requesting proofs, formal verification and revisions, reviewing the results and deciding what to publish, but did not supply proof strategies or intermediate mathematical arguments. Dev D. Goyal is responsible for the contents of this repository.

**ChatGPT** (OpenAI), using the GPT-6 model with Pro reasoning, worked autonomously from Dev D. Goyal's prompts. It:

- searched the OEIS and proposed candidate conjectures, and searched for earlier work on them;
- found the proofs, the counterexamples and the corrected statements;
- wrote the Lean 4 formalization in [`lean/`](lean/);
- wrote the first drafts of the papers.

The theorems stated in Section 3 ("Results") of each paper, and their proof strategies, are ChatGPT's.

**Claude Opus 5.5**, used with Claude Code, checked the work independently and prepared the papers and the repository. It:

- rebuilt the Lean project from source and audited the axioms of every theorem stated in [`lean/Entries/`](lean/Entries/), of the general theorems that the papers cite, and of the theorems in [`lean/Solutions/`](lean/Solutions/);
- compared the Lean definition of each sequence with the definition in its OEIS entry;
- wrote the numerical checks in [`verification/`](verification/), which recompute every sequence from its OEIS definition, compare it with the published terms, and test the results and the observations stated in the papers;
- read every proof;
- wrote the papers in their present form, expanding the exposition and, in places, writing out an argument in more detail or by a more elementary route;
- wrote the Discussion section of each paper, including the short arguments given there; these are checked numerically and are not part of the Lean formalization;
- renamed Lean modules and namespaces and edited comments;
- ported the formalization from Lean 4.19.0 to Lean 4.35.0 and Lean's module system, adapting proofs where Mathlib's names or lemmas had changed; the mathematical arguments of the proofs are unchanged;
- wrote the Challenge and Solution modules in [`lean/Challenges/`](lean/Challenges/) and [`lean/Solutions/`](lean/Solutions/), which restate the principal theorems using Mathlib's definitions only and derive them from the library, and checked them with Comparator;
- wrote [`lean/Families/ExpEquation.lean`](lean/Families/ExpEquation.lean), which proves that the exponential equation defining A397346 has exactly one solution, the generating function of the recurrence used in the paper; this step had been proved only on paper.

## Review status

Dev D. Goyal has reviewed the AI-generated proofs; this review is not an independent expert validation. No claim of novelty is made. The papers have not been peer reviewed, and they have not been submitted to a journal or to the OEIS.

## Scope of the checks

A Lean proof certifies the statement that Lean checks; whether that statement matches the OEIS entry was checked by comparing the definitions, and each paper explains the correspondence. The few steps that are proved only on paper are listed under `fidelity` in [`lean/formalization.yaml`](lean/formalization.yaml). The numerical checks test finitely many cases; they are evidence about definitions, indexing and statements, not proofs.

## Credits and priority

The sequences and the conjectures treated here were contributed to the OEIS by Paul D. Hanna, except A394576, which was contributed by Hoang Xuan Thanh. Some of the formulas in the entries that the papers use or mention were contributed by Vaclav Kotesovec and Seiichi Manyama, and the related entry A067145 (used in the paper on A396102) by Christian G. Bower. Earlier work credited in the papers:

- Danial Asaria recorded a counterexample to the conjecture modulo 9 in A396843.
- Shiva Priyan Shanmuga Sundaram proved the conjectures of A396797, the member $`r=3`$ of the family treated in the papers on A396099, A396798 and A396807.
- Amol Bhave's comment in A196523 proves congruences for a different family by a comparison of the same kind as in the paper on A396102.
- Hoang Xuan Thanh deposited software that computes A394576 and related sequences.

An OEIS entry that labels a statement as a conjecture shows only that its contributor did not know a proof. The searches for earlier work were limited, and no priority is claimed.

## Corrections

Errors in a proof, a definition or an attribution can be reported in the repository's issue tracker.
