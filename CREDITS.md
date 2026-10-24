# Credits

The problems come from the On-Line Encyclopedia of Integer Sequences (OEIS). The people below contributed the sequences and conjectures, or earlier results that this work builds on. The authorship of the work in this repository is described in [AUTHORSHIP.md](AUTHORSHIP.md).

## Sequences and conjectures

All attributions follow the OEIS entries as read in October 2026 (OEIS data is available under CC BY-SA 4.0 from the OEIS Foundation, <https://oeis.org>).

| Entry | Sequence contributed by | Statement(s) treated here, by | Notes |
|---|---|---|---|
| [A052895](https://oeis.org/A052895) | INRIA Encyclopedia of Combinatorial Structures (name by Vaclav Kotesovec) | Peter Bala (periodicity) | Stirling-sum formula by Vladimir Kruchinin |
| [A064618](https://oeis.org/A064618) | Karol A. Penson | Peter Bala (periodicity) | |
| [A080253](https://oeis.org/A080253) | Paul Boddington and Tim Honeywill | Peter Bala (periodicity) | e.g.f. by Antonio G. Astudillo; Stirling-sum formula by Vladeta Jovovic |
| [A167137](https://oeis.org/A167137) | Paul D. Hanna | Peter Bala (periodicity) | Hanna's separate integrality conjecture is not treated |
| [A195194](https://oeis.org/A195194) | Paul D. Hanna | Paul D. Hanna | |
| [A305550](https://oeis.org/A305550) | Ilya Gutkovskiy | Peter Bala (periodicity) | |
| [A306082](https://oeis.org/A306082) | Vaclav Kotesovec | Peter Bala (periodicity) | |
| [A354242](https://oeis.org/A354242) | Seiichi Manyama | Peter Bala (periodicity) | Bala's continued-fraction conjecture is not treated |
| [A378580](https://oeis.org/A378580) | Paul D. Hanna | Paul D. Hanna | the radius-of-convergence question is not treated |
| [A378581](https://oeis.org/A378581) | Paul D. Hanna | Paul D. Hanna | |
| [A380056](https://oeis.org/A380056) | Paul D. Hanna | Paul D. Hanna | |
| [A380060](https://oeis.org/A380060) | Paul D. Hanna | Paul D. Hanna | |
| [A380680](https://oeis.org/A380680) | Paul D. Hanna | Paul D. Hanna | conjecture refuted here |
| [A389474](https://oeis.org/A389474) | Paul D. Hanna | Paul D. Hanna | |
| [A389475](https://oeis.org/A389475) | Paul D. Hanna | Paul D. Hanna | |
| [A389536](https://oeis.org/A389536) | Paul D. Hanna | Paul D. Hanna | analytic statements not treated |
| [A389537](https://oeis.org/A389537) | Paul D. Hanna | Paul D. Hanna | the sign-run observation is not treated |
| [A389542](https://oeis.org/A389542) | Paul D. Hanna | Paul D. Hanna | |
| [A392210](https://oeis.org/A392210) | Paul D. Hanna | Paul D. Hanna (observation) | |
| [A393171](https://oeis.org/A393171) | Paul D. Hanna | Paul D. Hanna | |
| [A393172](https://oeis.org/A393172) | Paul D. Hanna | Paul D. Hanna | |
| [A393856](https://oeis.org/A393856) | Paul D. Hanna | Paul D. Hanna | |
| [A393857](https://oeis.org/A393857) | Paul D. Hanna | Paul D. Hanna | |
| [A393858](https://oeis.org/A393858) | Paul D. Hanna | Paul D. Hanna | |
| [A393859](https://oeis.org/A393859) | Paul D. Hanna | Paul D. Hanna | |
| [A396093](https://oeis.org/A396093) | Paul D. Hanna | Paul D. Hanna | closed form by Vaclav Kotesovec (mentioned, not used) |
| [A396099](https://oeis.org/A396099) | Paul D. Hanna | Paul D. Hanna | |
| [A396102](https://oeis.org/A396102) | Paul D. Hanna | Paul D. Hanna | |
| [A396797](https://oeis.org/A396797) | Paul D. Hanna | Paul D. Hanna | **proved earlier by Shiva Priyan Shanmuga Sundaram** |
| [A396798](https://oeis.org/A396798) | Paul D. Hanna | Paul D. Hanna | first conjecture corrected here |
| [A396807](https://oeis.org/A396807) | Paul D. Hanna | Paul D. Hanna | |
| [A396843](https://oeis.org/A396843) | Paul D. Hanna | Paul D. Hanna | **mod-9 conjecture refuted earlier by Danial Asaria** |
| [A396844](https://oeis.org/A396844) | Paul D. Hanna | Paul D. Hanna | conjecture corrected here |
| [A397588](https://oeis.org/A397588) | Paul D. Hanna | Paul D. Hanna | |

The papers also refer to the related entries A265940, A271958 and A396845 (Paul D. Hanna), A001333, A001156 and A088311 (weights), and A196523 (see below).

## Earlier results

- **Payam Danesh**, *Eventual periodicity of weighted Stirling transforms and two conjectures of Bala*, preprint, 26 August 2026, <https://doi.org/10.33774/coe-2026-4d6jr> (Theorem 4.1, Corollary 4.2). This proves the periodicity statements of the seven Stirling-transform entries in greater generality, with the Carmichael function λ(m). Our papers for A052895, A064618, A080253, A167137, A305550, A306082 and A354242 present **known results**.
- **B. Schreyer**, *Rigged horse numbers and their modular periodicity*, arXiv:2409.03799 (2024): earlier periodicity results for Fubini-type numbers.
- **Shiva Priyan Shanmuga Sundaram**, *A proof of the congruence conjectures for OEIS A396797*, September 2026, <https://oeis.org/A396797/a396797.pdf>. Our A396797 paper presents a **known result**. The method used here for the whole family A396099, A396797, A396798, A396807 extends the same comparison idea.
- **Danial Asaria** found the counterexample a(5) = 975 to the mod-9 conjecture in A396843 (recorded in the entry, July 2026).
- **Amol Bhave**'s comment in [A196523](https://oeis.org/A196523) (October 2026) proves congruences for the related family A = x + x·A^{∘l} by a comparison of the same kind. It is cited in the A396102 paper, which treats a different equation.

## Software

- **Lean 4** (version 4.19.0) and **Mathlib** (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`), by the Lean developers and the mathlib community.
- `lean/More/StirlingNumbers.lean` adapts the Stirling-number definitions and the power-expansion proof from the Mathlib module `Mathlib.Combinatorics.Enumerative.Stirling` (commit `4ed598f443601d8b5abccc2a14e3ba408ae47056`; copyright 2025 Beibei Xiong; authors Beibei Xiong, Yu Shao, Weijie Jiang, Zhengfeng Yang). That file stays under the Apache License 2.0. See [third_party/mathlib/NOTICE.md](third_party/mathlib/NOTICE.md) and [third_party/mathlib/Apache-2.0.txt](third_party/mathlib/Apache-2.0.txt).
- **PARI/GP** (The PARI Group) was used for the independent numerical checks.

## AI systems

- **ChatGPT** (OpenAI), using the GPT-6 model with Pro reasoning, did the research: the proofs, the formalization, and the first drafts of the papers.
- **Claude Opus 5.5**, used with Claude Code, did the independent verification, rewrote the papers for readability, and organized this repository.

See [AUTHORSHIP.md](AUTHORSHIP.md) for details.
