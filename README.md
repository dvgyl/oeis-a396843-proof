# Proofs and corrections for 34 OEIS entries, with Lean 4 formalizations

**Dev D. Goyal** · October 2026 · *an autonomous AI research effort*

This repository contains proofs, and in a few cases corrections, of conjectures recorded in 34 entries of the [On-Line Encyclopedia of Integer Sequences](https://oeis.org) (OEIS). For each entry there is:

- a **short, self-contained paper** that a reader with no specialist background can follow ([`papers/`](papers/));
- a **formal proof** in the Lean proof assistant, which a computer has checked step by step ([`lean/`](lean/));
- an **independent computer check** against the data published in the OEIS ([`verification/`](verification/)).

> **How this work was produced.** This is the output of an **autonomous AI research effort** directed by Dev D. Goyal.
>
> - **ChatGPT** (OpenAI), using the **GPT-6** model with **Pro reasoning**, did the research. Working from Dev D. Goyal's prompts, it searched the OEIS for suitable conjectures, found the proofs and the counterexamples, wrote the Lean formalization, and wrote the first drafts of the papers.
> - **Claude Opus 5.5**, an AI model used with **Claude Code** (a coding assistant that can run programs), then checked the work independently. It rebuilt the Lean proofs from source and confirmed that they rely on no unproved assumptions. It recomputed every sequence with separately written code and compared the results with the OEIS data. It read every proof. Finally, it rewrote the papers for readability and organized this repository.
> - **Dev D. Goyal** chose the problems, directed the work, asked for checks and revisions, and decided what to publish. Dev D. Goyal did not supply proof ideas, but has verified the results and is responsible for them.
>
> **Nothing here has been peer reviewed.** [AUTHORSHIP.md](AUTHORSHIP.md) gives the full details.

## What this is about

**The OEIS** is a public database of more than 390,000 integer sequences, such as 1, 1, 2, 5, 14, 42, … (the Catalan numbers). Mathematicians and scientists use it to identify the sequences they meet and to look up what is known about them. Many entries also record **conjectures**: patterns that a contributor noticed in the data but could not prove. Most of the conjectures treated here were contributed by Paul D. Hanna, and the periodicity conjectures by Peter Bala.

**The sequences** here are mostly the coefficients of a *power series*: an expression a(0) + a(1)x + a(2)x² + ⋯ that stores a whole sequence in one object. The series is defined by an equation, for example "substitute the series into itself three times" or "A(x·A(x) − 3x·A(x)²) = x²". The numbers a(n) grow quickly and look irregular.

**The conjectures** are about *remainders*. Examples: "a(n) is odd exactly when n is a power of 2", or "a(n) always leaves remainder 1 on division by 5". Remainders are often the first place where hidden structure in a sequence becomes visible. Explaining such a pattern is a standard way of understanding a sequence, and the explanation often shows *why* the pattern holds.

**Why it matters.** Each result settles a question that the OEIS recorded as open, or corrects a pattern that turned out to be false. Taken together, the collection is a case study of autonomous AI research in mathematics. The proofs are not only written up but also machine-checked, and they were independently verified by a second AI system. The papers also show one simple, reusable method (described below) that settles many questions of this kind.

## Results at a glance

| | Entries | What was done |
|---|---:|---|
| New proofs | 22 | 38 conjectured statements proved. One of these entries, A396798, also contains a conjecture that is false as stated; it is corrected. |
| New disproof | 1 | A380680: the conjecture is false; the correct statement is proved. |
| The original problem | 2 | A396843 and A396844, where the project began: one conjecture proved; two residue conjectures shown false (one had already been refuted on the OEIS) and replaced by complete, proved classifications. |
| Known results | 8 | Proved earlier by others; here they get a short self-contained proof and a formal proof. |
| Elementary observation | 1 | A392210: a one-line observation, proved formally. |

**No priority is claimed.** An OEIS entry that calls a statement a conjecture shows only that its contributor did not know a proof. Only limited searches for earlier work were made. Earlier results that were found are credited in [CREDITS.md](CREDITS.md) and in the papers.

## The 34 entries

Status: **proved** means the conjectures are proved. **corrected** means a conjecture is false as stated, and the correct statement is proved. **known** means the result had already been proved by someone else; a self-contained proof and a formal proof are given.

Notation: "a(n) ≡ r (mod m)" means that a(n) leaves remainder r on division by m. "4 | a(n)" means that 4 divides a(n).

| OEIS | What is proved | Status | Paper | Lean |
|---|---|---|---|---|
| [A052895](https://oeis.org/A052895) | the remainders of a(n) modulo any m repeat with period φ(m) from n = m on (Bala's conjecture) | known | [PDF](papers/A052895.pdf) | [Lean](lean/Entries/A052895.lean) |
| [A064618](https://oeis.org/A064618) | the same periodicity, for the Stirling transform of (n!)² | known | [PDF](papers/A064618.pdf) | [Lean](lean/Entries/A064618.lean) |
| [A080253](https://oeis.org/A080253) | the same periodicity, for the Coxeter complexes of type Bₙ | known | [PDF](papers/A080253.pdf) | [Lean](lean/Entries/A080253.lean) |
| [A167137](https://oeis.org/A167137) | the same periodicity, for the e.g.f. P(eˣ−1) | known | [PDF](papers/A167137.pdf) | [Lean](lean/Entries/A167137.lean) |
| [A195194](https://oeis.org/A195194) | the infinitely nested reversion is well defined, and a(n) is odd exactly when n is a power of 2 | proved | [PDF](papers/A195194.pdf) | [Lean](lean/Entries/A195194.lean) |
| [A305550](https://oeis.org/A305550) | the same periodicity, for the e.g.f. ∏(1+(eˣ−1)ᵏ) | known | [PDF](papers/A305550.pdf) | [Lean](lean/Entries/A305550.lean) |
| [A306082](https://oeis.org/A306082) | the same periodicity, for the e.g.f. ∏ 1/(1−(eˣ−1)^(k²)) | known | [PDF](papers/A306082.pdf) | [Lean](lean/Entries/A306082.lean) |
| [A354242](https://oeis.org/A354242) | the same periodicity, for the e.g.f. 1/√(5−4eˣ) | known | [PDF](papers/A354242.pdf) | [Lean](lean/Entries/A354242.lean) |
| [A378580](https://oeis.org/A378580) | A(x/A(x)) = θ₃: for n > 0, a(n) ≡ 2 (mod 4) if n is a perfect square, and 4 \| a(n) otherwise | proved | [PDF](papers/A378580.pdf) | [Lean](lean/Entries/A378580.lean) |
| [A378581](https://oeis.org/A378581) | A(x·A(x)) = θ₃: the same square pattern | proved | [PDF](papers/A378581.pdf) | [Lean](lean/Entries/A378581.lean) |
| [A380056](https://oeis.org/A380056) | a(n) ≡ 1 (mod 4) for n ≥ 1, and a(n) ≡ 2·2ⁿ + 3·4ⁿ (mod 5); so 5 divides a(n) exactly when 4 divides n | proved | [PDF](papers/A380056.pdf) | [Lean](lean/Entries/A380056.lean) |
| [A380060](https://oeis.org/A380060) | for n > 0, a(n) ≡ 2 (mod 4) if n is a perfect square, and 4 \| a(n) otherwise | proved | [PDF](papers/A380060.pdf) | [Lean](lean/Entries/A380060.lean) |
| [A380680](https://oeis.org/A380680) | the square conjecture is **false** (a(1) = 4, a(2) = 6); in fact a(n) ≡ 2 (mod 4) exactly when n = 2k² | corrected | [PDF](papers/A380680.pdf) | [Lean](lean/Entries/A380680.lean) |
| [A389474](https://oeis.org/A389474) | A² ≡ x² + 2x³ (mod 9), and A^(3k) ≡ A(x³)ᵏ (mod 3) | proved | [PDF](papers/A389474.pdf) | [Lean](lean/Entries/A389474.lean) |
| [A389475](https://oeis.org/A389475) | A³ ≡ A(x³) and A² ≡ x² + 2A(x³) (mod 3) | proved | [PDF](papers/A389475.pdf) | [Lean](lean/Entries/A389475.lean) |
| [A389536](https://oeis.org/A389536) | for n > 1, a(n) ≡ 2 (mod 4) if n = 2ᵏ + 1, and 4 \| a(n) otherwise | proved | [PDF](papers/A389536.pdf) | [Lean](lean/Entries/A389536.lean) |
| [A389537](https://oeis.org/A389537) | for n > 2, a(n) ≡ 2 (mod 4) if n = 3·2ᵏ, and 4 \| a(n) otherwise | proved | [PDF](papers/A389537.pdf) | [Lean](lean/Entries/A389537.lean) |
| [A389542](https://oeis.org/A389542) | for n > 1, a(n) ≡ 2 (mod 4) if n = 2ᵏ + 1, and 4 \| a(n) otherwise | proved | [PDF](papers/A389542.pdf) | [Lean](lean/Entries/A389542.lean) |
| [A392210](https://oeis.org/A392210) | a(2n−1) is even for n > 1 (an elementary observation) | proved | [PDF](papers/A392210.pdf) | [Lean](lean/Entries/A392210.lean) |
| [A393171](https://oeis.org/A393171) | for n > 2, a(n) ≡ 4 (mod 8) if n = 2ᵏ or 2ᵏ + 1, and 8 \| a(n) otherwise | proved | [PDF](papers/A393171.pdf) | [Lean](lean/Entries/A393171.lean) |
| [A393172](https://oeis.org/A393172) | for n > 1, a(n) ≡ 2 (mod 4) if n = 2ᵏ, and 4 \| a(n) otherwise | proved | [PDF](papers/A393172.pdf) | [Lean](lean/Entries/A393172.lean) |
| [A393856](https://oeis.org/A393856) | a(n) ≡ 1 (mod 5), and a(n) is odd exactly when n is a power of 2 | proved | [PDF](papers/A393856.pdf) | [Lean](lean/Entries/A393856.lean) |
| [A393857](https://oeis.org/A393857) | a(n) ≡ 1 (mod 6) | proved | [PDF](papers/A393857.pdf) | [Lean](lean/Entries/A393857.lean) |
| [A393858](https://oeis.org/A393858) | a(n) ≡ 1 (mod 7), and a(n) is odd exactly when n is a power of 2 | proved | [PDF](papers/A393858.pdf) | [Lean](lean/Entries/A393858.lean) |
| [A393859](https://oeis.org/A393859) | a(n) ≡ 1 (mod 8) | proved | [PDF](papers/A393859.pdf) | [Lean](lean/Entries/A393859.lean) |
| [A396093](https://oeis.org/A396093) | a(n) is odd exactly when n ≡ 1, 3, 7 or 9 (mod 10) | proved | [PDF](papers/A396093.pdf) | [Lean](lean/Entries/A396093.lean) |
| [A396099](https://oeis.org/A396099) | all four mod-4 conjectures, for A and its iterates | proved | [PDF](papers/A396099.pdf) | [Lean](lean/Entries/A396099.lean) |
| [A396102](https://oeis.org/A396102) | a(n) ≡ 1 (mod 3), and a theorem for the whole family of such equations | proved | [PDF](papers/A396102.pdf) | [Lean](lean/Entries/A396102.lean) |
| [A396797](https://oeis.org/A396797) | for every integer k, the coefficients of the k-th iterate satisfy [xⁿ] ≡ k^(n−1) (mod 6) | known | [PDF](papers/A396797.pdf) | [Lean](lean/Entries/A396797.lean) |
| [A396798](https://oeis.org/A396798) | 7 of the 8 mod-8 conjectures; the remaining one holds from n = 2, not from n = 1 as stated | proved, corrected | [PDF](papers/A396798.pdf) | [Lean](lean/Entries/A396798.lean) |
| [A396807](https://oeis.org/A396807) | for every integer k, the coefficients of the k-th iterate satisfy [xⁿ] ≡ k^(n−1) (mod 10) | proved | [PDF](papers/A396807.pdf) | [Lean](lean/Entries/A396807.lean) |
| [A396843](https://oeis.org/A396843) | **the original problem**: every term is odd; exact remainders modulo 9; and 3^(s₂(n−1)) divides a(n), where s₂ is the binary digit sum | proved, corrected | [PDF](papers/A396843.pdf) | [Lean](lean/Entries/A396843.lean) |
| [A396844](https://oeis.org/A396844) | exact remainders modulo 16; the conjecture fails at n = 17 | corrected | [PDF](papers/A396844.pdf) | [Lean](lean/Entries/A396844.lean) |
| [A397588](https://oeis.org/A397588) | a(n) is odd exactly when n is a power of 2, and 3 \| a(n) for n > 1 | proved | [PDF](papers/A397588.pdf) | [Lean](lean/Entries/A397588.lean) |

Each paper's LaTeX source sits next to its PDF in [`papers/`](papers/). [papers/README.md](papers/README.md) groups the papers by method and explains how each one is organized.

## The common idea, in plain words

Most of the sequences are defined by an equation between power series. Such an equation usually pins down the numbers a(1), a(2), a(3), … one at a time, using only addition, subtraction and multiplication. Because no division is needed, the same equation also has exactly one solution in "clock arithmetic" modulo m, where only remainders are kept.

That gives a simple strategy for proving a statement about the remainders of a(n) modulo m:

1. guess a simple series that might describe the remainders;
2. check that it satisfies the defining equation modulo m;
3. conclude that it *is* the sequence modulo m, because there is only one solution.

The guesses are things like a simple fraction, a series with only a few nonzero terms, or the Catalan numbers. The hard part is usually finding the right guess, and handling cases where the equation seems to require dividing by 2 or 3, which clock arithmetic does not allow. Each paper explains this method from scratch.

## How the results were checked

| Check | What it shows | Result |
|---|---|---|
| Lean build from source (Lean 4.19.0, Mathlib `c44e0c8`) | every formal proof is complete and correct | all 101 Lean files compile |
| Axiom audit of the 262 theorems in `lean/Entries/`, plus 6 general theorems the papers cite | no step is left unproved and nothing extra is assumed | only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) |
| Lean definitions compared with the OEIS definitions | the formal theorems are about the right sequences | checked side by side for all 34 entries; see each paper's first section |
| Independent recomputation in PARI/GP | the definitions, indexing and claims match the published data | all published OEIS terms reproduced; 156 of 156 checks pass |
| Every proof read in full | the human-readable arguments are correct | no errors found |

The last four checks were done by Claude Opus 5.5 with Claude Code, in code that shares nothing with the original research. A formal proof certifies the statement that Lean checks. A computer check tests only finitely many cases, so it is evidence, not proof. [verification/README.md](verification/README.md) explains each check and how to rerun it.

## The story of the project

The project began with a single problem. In July 2026 Paul D. Hanna contributed [A396843](https://oeis.org/A396843) to the OEIS: the coefficients of the series A with A(x·A − 3x·A²) = x², together with the conjecture that all of them are odd. Dev D. Goyal asked ChatGPT (GPT-6, Pro reasoning) to solve it. ChatGPT proved the conjecture for the whole family A(x·A − m·x·A²) = x². It also found the exact remainders modulo m² and a divisibility law governed by binary digits, and it formalized everything in Lean. Two residue conjectures for this family turned out to be false. For A396843, Danial Asaria had already recorded a counterexample in the OEIS. For the companion entry A396844, the failure at n = 17 follows from the new classification. Both are replaced by complete, proved classifications. That first result was released on its own (Zenodo DOI [10.5281/zenodo.23567463](https://doi.org/10.5281/zenodo.23567463)); its files are kept in [`history/original-release/`](history/original-release/).

Dev D. Goyal then asked ChatGPT to find more OEIS conjectures of the same kind and to prove them. In four further rounds, ChatGPT screened candidate entries and proved 38 conjectured statements in 22 entries. It refuted two (in A396798 and A380680), and it wrote self-contained proofs of eight results that it found had already been proved by others. At least seven candidate entries were screened out, mostly because earlier work already covered them. Several questions in the treated entries remain open, for example the sign pattern in A389537 and the radius of convergence in A378580.

A detailed account, written by ChatGPT at the end of the research, is in [docs/research-retrospective.md](docs/research-retrospective.md). ChatGPT's complete final collection, including its original manuscripts and review records, is kept unchanged in [`history/chatgpt-collection/`](history/chatgpt-collection/).

## Repository layout

| Path | Contents |
|---|---|
| [`papers/`](papers/) | The 34 papers, as PDF and standalone LaTeX, one per OEIS entry |
| [`lean/`](lean/) | The Lean 4 project. `Entries/` has one file per entry; the other folders hold the shared proofs |
| [`verification/`](verification/) | The independent checks: the PARI/GP script, a snapshot of the OEIS data, the axiom audit, and their logs |
| [`docs/research-retrospective.md`](docs/research-retrospective.md) | How the research unfolded: methods, counts, screened-out entries, open questions |
| [`history/`](history/) | Earlier material, kept unchanged: the original A396843 release and ChatGPT's final collection |
| [`third_party/`](third_party/) | License notice for the adapted Mathlib code (Apache 2.0) |
| [AUTHORSHIP.md](AUTHORSHIP.md) | Who did what, the AI disclosure, and the review status |
| [CREDITS.md](CREDITS.md) | Who contributed each sequence and conjecture, and earlier results |
| [CITATION.cff](CITATION.cff) | How to cite this repository |

## Reproducing the checks

```sh
# Formal proofs (needs elan, the Lean version manager; downloads Mathlib, about 5 GB)
cd lean
lake exe cache get        # optional: download prebuilt Mathlib instead of compiling it (hours)
lake build                # the shared libraries
lake build Entries        # the 34 entry files
lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt

# Numerical checks (needs PARI/GP 2.15 or later; about 20 minutes)
cd ../verification
gp -q independent_checks.gp < /dev/null
```

## Citing

Please cite this repository using [CITATION.cff](CITATION.cff); GitHub shows a "Cite this repository" button. The first release, which covered A396843 only, is archived on Zenodo: [10.5281/zenodo.23567463](https://doi.org/10.5281/zenodo.23567463). When citing a specific result, please also cite the OEIS entry and the author of its conjecture (see [CREDITS.md](CREDITS.md)).

## License

No license is granted for the original material in this repository. The adapted Mathlib file `lean/More/StirlingNumbers.lean` remains under the Apache License 2.0 (see [`third_party/mathlib/`](third_party/mathlib/)). OEIS text quoted in the papers is © The OEIS Foundation and is used under CC BY-SA 4.0.
