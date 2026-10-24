# Authorship and AI disclosure

**Author:** Dev D. Goyal.

The results in this repository were obtained in an autonomous AI research effort directed by Dev D. Goyal. This page records the contribution of each participant.

## Contributions

**Dev D. Goyal** initiated and directed the project. Dev D. Goyal chose which of the proposed problems to pursue, requested proofs, formal verification and revisions, verified the results, and decided what to publish. Dev D. Goyal did not supply proof strategies or intermediate mathematical arguments, and is responsible for the contents of this repository.

**ChatGPT** (OpenAI), using the GPT-6 model with Pro reasoning, worked autonomously from Dev D. Goyal's prompts. It:

- searched the OEIS and proposed candidate conjectures;
- found the proofs, the counterexamples and the corrected statements;
- wrote the Lean 4 formalization in [`lean/`](lean/);
- wrote the first drafts of the papers.

The theorems and the proof strategies in the papers are ChatGPT's.

**Claude Opus 5.5**, used with Claude Code, checked the work independently and prepared the papers and the repository. It:

- rebuilt the Lean project from source and audited the axioms of every theorem stated in [`lean/Entries/`](lean/Entries/), and of the general theorems that the papers cite;
- compared the Lean definition of each sequence with the definition in its OEIS entry;
- wrote the numerical checks in [`verification/`](verification/), which recompute every sequence from its OEIS definition, compare it with the published terms, and test every stated result;
- read every proof;
- wrote the papers in their present form, expanding the exposition and, in places, writing out an argument in more detail or by a more elementary route;
- wrote the Discussion section of each paper. The further observations there were checked numerically and are not part of the Lean formalization;
- renamed Lean modules and namespaces, edited comments, and replaced `import Mathlib` by the specific Mathlib modules needed in two files. The proofs themselves are unchanged.

## Review status

Dev D. Goyal has verified the results. The papers have not been peer reviewed, and they have not been submitted to a journal or to the OEIS.

## Scope of the checks

A Lean proof certifies the statement that Lean checks; whether that statement matches the OEIS entry was checked by comparing the definitions, and each paper explains the correspondence. The numerical checks test finitely many cases; they are evidence about definitions, indexing and statements, not proofs.

## Credits and priority

The sequences and the conjectures treated here were contributed to the OEIS by Paul D. Hanna, except A394576, which was contributed by Hoang Xuan Thanh. Earlier work credited in the papers:

- Danial Asaria recorded a counterexample to the conjecture modulo 9 in A396843.
- Shiva Priyan Shanmuga Sundaram proved the conjectures of A396797, the member $`r=3`$ of the family treated in the papers on A396099, A396798 and A396807.
- Amol Bhave's comment in A196523 proves congruences for a related family by a comparison of the same kind as in the paper on A396102.
- Hoang Xuan Thanh deposited software that computes A394576 and related sequences.

An OEIS entry that labels a statement as a conjecture shows only that its contributor did not know a proof. Only limited searches for earlier work were made, and no priority is claimed.

## Corrections

Errors in a proof, a definition or an attribution can be reported in the repository's issue tracker.
