# Independent verification

This folder contains the independent checks of the results in this repository. They were written and run by **Claude Opus 5.5, used with Claude Code**, in October 2026, after the research was finished. They share no code with the tools that ChatGPT wrote during the research. (See [../AUTHORSHIP.md](../AUTHORSHIP.md) for who did what.)

A mathematical result can go wrong in three ways: the proof can contain a mistake; the proof can be correct but about a slightly different sequence than the one in the OEIS (for example, shifted by one index); or the statement can be mistyped. The three checks below target these three risks.

| Check | Risk it addresses | Files | Result |
|---|---|---|---|
| 1. Formal proofs rebuilt and audited | a mistake in a proof | [`AxiomAudit.lean`](AxiomAudit.lean), [`check_axioms.py`](check_axioms.py), [`results/`](results/) | all 262 entry theorems fully proved |
| 2. Lean definitions compared with the OEIS | a proof about the wrong sequence | each paper, Sections 1 and "Checking the results" | all 34 entries match |
| 3. Independent numerical recomputation | a wrong definition, index or statement | [`independent_checks.gp`](independent_checks.gp), [`oeis_terms.gp`](oeis_terms.gp), [`results/independent_checks.log`](results/independent_checks.log) | 156 of 156 checks pass |

## 1. Formal proofs

**What Lean is.** Lean is a *proof assistant*: a program in which mathematical statements and proofs are written in a precise formal language, and every step is checked mechanically down to the basic rules of logic. Mathlib is Lean's large library of formalized mathematics. If Lean accepts a proof, the only remaining questions are whether the *statement* says what was intended (check 2) and whether the basic rules (axioms) are acceptable.

**What was checked.** The Lean project in [`../lean/`](../lean/) was rebuilt from source with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Then Lean was asked, for each of the 262 theorems stated in [`../lean/Entries/`](../lean/Entries/), which axioms the theorem ultimately depends on (the command `#print axioms`, collected in [`AxiomAudit.lean`](AxiomAudit.lean)). The answer must contain only Lean's three standard axioms:

- `propext`: two statements that imply each other are equal;
- `Classical.choice`: one may pick an element from any nonempty collection;
- `Quot.sound`: the basic rule for working with equivalence classes.

These are the foundations that all of Mathlib uses. An unfinished proof would show up as the axiom `sorryAx`, and an extra assumption would show up under its own name. Neither occurs. The script [`check_axioms.py`](check_axioms.py) confirms this automatically: it checks that every theorem listed in `AxiomAudit.lean` appears in Lean's output and uses no other axiom.

**Logs:** [`results/lean_build.log`](results/lean_build.log) (the build) and [`results/axiom_audit.txt`](results/axiom_audit.txt) (Lean's answers).

## 2. Definitions

A formal proof certifies exactly the statement that Lean checks. So for each of the 34 entries, the Lean definition of the sequence was read side by side with the definition printed in the OEIS entry: the same equation, the same starting index, and the same meaning of notation such as A^k (a power or an iterate). In most entries the Lean file defines the sequence by the OEIS equation itself and proves that this equation has exactly one solution. In a few entries the OEIS title is first turned into an equivalent formula; each paper explains such steps in its first section and says which steps are proved on paper only:

- the exponential generating function versus the Stirling-number sum, for the seven periodicity entries;
- the two-sided versus the one-sided theta sum, for A380060 and A380680;
- the nested title versus the functional equation, for A392210.

## 3. Numerical recomputation

The PARI/GP script [`independent_checks.gp`](independent_checks.gp) does four things for each entry:

1. it computes the sequence from the definition printed in the OEIS entry;
2. it compares the result with the terms published in the OEIS, which are stored in [`oeis_terms.gp`](oeis_terms.gp);
3. it checks that the computed series satisfies its defining equation;
4. it tests every congruence, residue pattern and counterexample stated in the papers, on all indices in a range.

The OEIS terms in `oeis_terms.gp` were taken from the OEIS data repository (<https://github.com/oeis/oeisdata>) on 24 October 2026. OEIS data is © The OEIS Foundation Inc. and is licensed under CC BY-SA 4.0.

| Entries | Indices tested |
|---|---|
| seven periodicity entries (A052895, A064618, A080253, A167137, A305550, A306082, A354242) | every m ≤ 60 and m ≤ n < 160 |
| A195194 | n < 140 |
| A378580, A378581 | 0 < n < 200 |
| A380056 | n < 400 |
| A380060, A380680 | 0 < n < 220 |
| A389474, A389475 | n < 90 |
| A389536, A389537, A389542 | n < 130 |
| A392210 | odd indices below 200 |
| A393171, A393172 | n < 200 |
| A393856 to A393859 | n < 300 |
| A396093 | n < 600 |
| A396099, A396797, A396798, A396807 | n < 160; the general formula for r = 1, …, 8, iterates k = −4, …, 9, and n < 90 |
| A396102 | n < 70; the family r = 2, …, 7 for n < 40 |
| A396843, A396844 | m = 3, 4 for n < 260; m = 2, …, 12 for n < 70 |
| A397588 | n < 299 |

In every entry, all published OEIS terms were reproduced. The full output is in [`results/independent_checks.log`](results/independent_checks.log).

A computer check can only test finitely many cases, so it is not a proof. Its job is to catch mistakes in definitions, indexing and statements, which a formal proof cannot catch on its own.

## Rerunning the checks

```sh
# Formal proofs: from the lean/ folder (needs elan; see ../lean/README.md)
cd ../lean
lake build && lake build Entries
lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt

# Numerical checks: from this folder (needs PARI/GP 2.15 or later; about 20 minutes)
cd ../verification
gp -q independent_checks.gp < /dev/null
```

Both `check_axioms.py` and `independent_checks.gp` exit with a nonzero status if any check fails.
