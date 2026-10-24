# Authorship and AI disclosure

**Author:** Dev D. Goyal, the only human author.

**This repository is the output of an autonomous AI research effort.** One AI system did the research: it found the proofs, the counterexamples and the corrected statements, wrote the formal proofs, and drafted the papers. A second AI system then checked the work independently and prepared this repository. Dev D. Goyal directed both. This page explains who did what, what was checked, and what the checks do and do not show.

## Who did what

### Dev D. Goyal

- Started the project with the A396843 problem, then asked for more OEIS conjectures to be found, proved and formally verified.
- Chose and approved the problems, asked for checks and revisions, and decided what to publish.
- Did **not** supply proof strategies or intermediate mathematical arguments.
- Has verified the results and is responsible for this repository.

### ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning: the research

ChatGPT worked autonomously from Dev D. Goyal's prompts, in a series of long conversations. It:

- screened candidate OEIS entries, and excluded some because earlier work already covered them or their sources were unclear (see [docs/research-retrospective.md](docs/research-retrospective.md));
- found the proofs, the counterexamples, and the corrected statements;
- wrote the whole Lean 4 development in [`lean/`](lean/), except the Stirling-number code adapted from Mathlib (see [CREDITS.md](CREDITS.md));
- wrote the original 34 papers, the coverage ledgers, its own verification scripts and reports, and the research retrospective.

ChatGPT's original records are kept unchanged in [`history/chatgpt-collection/`](history/chatgpt-collection/).

### Claude Opus 5.5, used with Claude Code: independent checking and editing

Claude Opus 5.5 is an AI model. It was used with Claude Code, a coding assistant that can read files, run programs, and edit a code repository. It worked in October 2026, after the research was finished, and it shares no code with ChatGPT's tools. Its tasks were to check the work independently and to prepare this repository. It did the following.

1. **Rebuilt the formal proofs from source.** It compiled the Lean project with Lean 4.19.0 and the pinned version of Mathlib. Then it asked Lean to list the basic assumptions (axioms) behind each of the 262 theorems stated in [`lean/Entries/`](lean/Entries/), and behind 6 general theorems that the papers cite. Every theorem depends only on Lean's three standard axioms, so no step is left unproved ([verification/README.md](verification/README.md)).
2. **Compared the Lean definitions with the OEIS definitions,** side by side for all 34 entries. This check matters because a formal proof is only as good as its statement.
3. **Wrote an independent numerical check** in PARI/GP ([`verification/independent_checks.gp`](verification/independent_checks.gp)). The script recomputes every sequence from its OEIS definition. It compares the results with the terms published in the OEIS (fetched in October 2026), and it tests every stated congruence and counterexample on hundreds of terms. All 156 checks pass.
4. **Read every proof** in the 34 papers and found no errors.
5. **Rewrote the 34 papers** so that a non-specialist can follow them. Each paper now explains its background from scratch. It says what was known, what is new, and why it matters, and it maps each statement to its Lean theorem. The theorems and the proof strategies are ChatGPT's. Claude Opus 5.5's changes are expository, plus three short connecting arguments, written out on paper, that are **not** part of the Lean development:
   - the reduction of the two-sided sums in A380060 and A380680 to the one-sided formula used in Lean;
   - the derivation of the nested-square title of A392210 from its defining equation;
   - a short lemma, in the A195194 paper, saying that inversion preserves agreement of series up to a given degree.

   The Discussion section of each paper was written during the rewrite. Some contain further observations, such as generalizations or congruences modulo higher powers. Some of these are proved in the text and others are only observed numerically, and the text says which. All were checked by computer (224 checks, in [`verification/discussion_checks.gp`](verification/discussion_checks.gp)), and none is part of the Lean formalization.
6. **Corrected the attribution text.** It replaced "Dev Goyal" with "Dev D. Goyal", and outdated "review pending" notes with the current status. This was done in documentation and in Lean *comments* only; a check confirmed that the Lean code itself is unchanged.
7. **Organized this repository** and wrote the README, this page, CREDITS, CITATION and the other guides.

Claude Opus 5.5 did not produce the original proofs, and it did not change any Lean proof.

## Review status

- Dev D. Goyal has verified the results.
- The independent checks by Claude Opus 5.5 are described above; their logs are in [`verification/results/`](verification/results/).
- **No independent peer review has taken place.** The work has not been submitted to a journal or to the OEIS.

## What the checks do and do not show

- **A Lean proof certifies the Lean statement.** Whether the Lean definitions match the OEIS definitions was checked by reading them side by side. Each paper explains this correspondence, including the few places where it is proved on paper but not in Lean.
- **The numerical checks test finitely many cases.** They catch mistakes in definitions and indexing. They are not proofs of statements about all n.
- **No priority or novelty is claimed.** An OEIS entry that labels a statement as a conjecture shows only that its contributor did not know a proof. During the research only limited searches for earlier proofs were made. Eight of the 34 entries are **known results**. Seven are periodicity statements proved earlier, in greater generality, by Payam Danesh, and A396797 was proved earlier by Shiva Priyan Shanmuga Sundaram. For these, the contribution here is a self-contained proof and a formal proof.
- **Some results are elementary or standard.** A392210 is a one-line observation. One statement in A389474 and one in A389475 follow directly from the classical Frobenius identity. The papers say so.

## Reporting problems

If you find an error in a proof, a definition or an attribution, please open an issue on the repository.
