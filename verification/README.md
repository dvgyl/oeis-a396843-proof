# Verification

This directory contains the independent checks of the results: an axiom audit of the Lean formalization, and numerical checks against the data published in the OEIS. The PARI/GP checks were written independently of the Lean development.

| Check | Files | Result |
|---|---|---|
| Axiom audit of the formal proofs | [`AxiomAudit.lean`](AxiomAudit.lean), [`check_axioms.py`](check_axioms.py) | 249 of 249 theorems use only the standard axioms |
| Main results against the OEIS data | [`independent_checks.gp`](independent_checks.gp), [`oeis_terms.gp`](oeis_terms.gp) | 156 of 156 checks pass |
| Observations in the Discussion sections | [`discussion_checks.gp`](discussion_checks.gp), [`discussion_terms.gp`](discussion_terms.gp) | 207 of 207 checks pass |

The outputs are in [`results/`](results/).

## Axiom audit

The Lean project in [`../lean/`](../lean/) was built from source with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` ([`results/lean_build.log`](results/lean_build.log)). [`AxiomAudit.lean`](AxiomAudit.lean) runs `#print axioms` on the 244 theorems stated in [`../lean/Entries/`](../lean/Entries/) and on 5 general theorems that the papers cite by name. [`check_axioms.py`](check_axioms.py) confirms that every listed theorem is reported and depends only on `propext`, `Classical.choice` and `Quot.sound`; an unfinished proof would appear as `sorryAx`. The output is in [`results/axiom_audit.txt`](results/axiom_audit.txt) and the verdict in [`results/axiom_audit_check.txt`](results/axiom_audit_check.txt).

A formal proof certifies the statement that Lean checks. For each entry, the Lean definition of the sequence was also compared with the definition in the OEIS entry. Where Lean uses an equivalent form of the definition, the paper proves the equivalence; these cases are listed under `fidelity` in [`../lean/formalization.yaml`](../lean/formalization.yaml).

## Numerical checks

[`independent_checks.gp`](independent_checks.gp) does the following for each entry:

1. it computes the sequence from the definition printed in the OEIS entry;
2. it compares the result with the published terms in [`oeis_terms.gp`](oeis_terms.gp);
3. it checks that the computed series satisfies its defining equation;
4. it tests every congruence, residue pattern and counterexample stated in the paper, over a range of indices.

[`discussion_checks.gp`](discussion_checks.gp) tests every concrete claim in the papers' Discussion sections, over at least the range stated in the paper. These claims include generalizations, congruences modulo higher powers, periods, agreement with related OEIS entries, and sign patterns; none of them is part of the Lean formalization. Published terms of the related entries are in [`discussion_terms.gp`](discussion_terms.gp).

The published terms were taken from the [OEIS data repository](https://github.com/oeis/oeisdata) on 24 October 2026. OEIS data is © The OEIS Foundation Inc. and is licensed under CC BY-SA 4.0.

| Entries | Indices tested for the main results |
|---|---|
| A195194 | $`n<140`$ |
| A378580, A378581 | $`0<n<200`$ |
| A380056 | $`n<400`$ |
| A380060, A380680 | $`0<n<220`$ |
| A389474, A389475 | $`n<90`$ |
| A389536, A389537, A389542 | $`n<130`$ |
| A392210 | odd indices below 200 |
| A393171, A393172 | $`n<200`$ |
| A393856–A393859 | $`n<300`$ |
| A396093 | $`n<600`$ |
| A396099, A396798, A396807 | $`n<160`$; the general theorem for $`r\le8`$, $`-4\le k\le9`$, $`n<90`$ |
| A396102 | $`n<70`$; the family $`r=2,\dots,7`$ for $`n<40`$ |
| A396843, A396844 | $`m=3,4`$ for $`n<260`$; $`m=2,\dots,12`$ for $`n<70`$ |
| A397588 | $`n<299`$ |
| A355872 | exactly for $`n\le30`$; modulo 16 for $`n\le300`$ |
| A394576 | $`n\le100000`$ |
| A397346 | from the definition for $`n<61`$; from the recurrence in the entry for $`n\le400`$ |

A finite computation is evidence, not a proof; its purpose is to catch errors in definitions, indexing and statements.

## Running the checks

```sh
# from lean/, after building the project
lake env lean ../verification/AxiomAudit.lean > ../verification/results/axiom_audit.txt
python3 ../verification/check_axioms.py ../verification/results/axiom_audit.txt

# from verification/ (PARI/GP 2.15 or later)
gp -q independent_checks.gp < /dev/null    # about 20 minutes
gp -q discussion_checks.gp < /dev/null     # about 8 minutes
```

Each command exits with a nonzero status if a check fails.
