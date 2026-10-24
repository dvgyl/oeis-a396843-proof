# Formal coverage

All declarations below are universal theorems about actual Mathlib formal power series and the canonical integer solutions of the original equations. The delivered `reproducibility/lean_complete/report.json` records the final clean build, explicit type-contract compilation, theorem-type output, source hashes, and transitive axiom checks. This table describes mathematical coverage; the fixed manifest lists the exact declarations included in the audit.

**Source assertions:** 19 original conjectures proved; one false starting-phase assertion refuted and replaced by a proved correction. This covers all 20 conjecture statements in the seven targeted entries, with additional general structural theorems. The previously proved A396797 case is credited, not counted as a new conjecture resolution.

## A396099: all four original assertions

Namespace: `Consecutive`. Files: `Coefficients.lean`, `Acceptance.lean`.

| Original assertion | Exact declaration | Index range |
|---|---|---|
| All terms odd | `a396099_odd` | Every n > 0 |
| Period 1,3,3,1 modulo four from index three | `a396099_period`; equivalent residue classifier `a396099_residue` | Every block j ≥ 0; every n ≥ 3 |
| Second-iterate coefficients vanish modulo four above degree two | `a396099_second_iterate` | Every n > 2 |
| Coefficients of F − X F^(circ 3) equal two modulo four above degree two | `a396099_difference` | Every n > 2 |

The stronger full-series identities are `solution_two_mod_four`, `a396099_second_iterate_series`, and `a396099_difference_series`.

**Direct original-equation contract:** `a396099_all_four` starts with any normalized integer series F and the literal equation

```
F = X + compose F F * compose F (compose F F)
```

and concludes all four universally quantified coefficient statements. None of the desired congruences is a hypothesis. The proof uses the proved uniqueness theorem to identify that F with the canonical solution.

## General consecutive-iterate theorem

Namespace: `Consecutive`. Files: `Construction.lean`, `Modular.lean`, `IntegerIterates.lean`.

| Result | Declaration |
|---|---|
| Existence and uniqueness over every commutative ring | `existence_uniqueness` |
| Canonical solution satisfies the defining equation | `solution_equation` |
| Coefficient reduction preserves the canonical solution | `map_solution` |
| Complete rational representative for all natural iterates | `iter_solution_mod` |
| Natural-iterate formula applied explicitly to the integer series | `map_iter_solution_mod` |
| Exact order modulo 2r for natural iterates | `iter_solution_mod_eq_X_iff` |
| Negative iterates are genuine two-sided compositional inverses | `ziter_negative_is_inverse` |
| Coefficient reduction preserves signed iterates | `map_ziter` |
| Complete representative for every integer k, for r > 0 | `ziter_solution_mod` |
| Signed formula applied explicitly to the integer series | `map_ziter_solution_mod` |
| Signed coefficient formula, including low-degree guards | `integerIterateCoeff_mod` |
| Exact order for all integer k, for r > 0 | `ziter_solution_mod_eq_X_iff` |

The formula is `mobius k` plus `r * correction` precisely when r is even and k is odd. `mobius k` is defined as X times the geometric series with coefficients k^n. `correction` is X^4 times the cube of the geometric series at one. The coefficient statement explicitly guards n ≥ 4, so no negative binomial index or missing low-degree case is hidden. It assumes n ≥ 1, as does the source coefficient formula.

## A396798: seven true statements and one phase correction

Namespace: `Consecutive`. File: `Related.lean`.

| Source assertion or correction | Declaration | Range |
|---|---|---|
| Second iterate vanishes modulo eight | `a396798_second_iterate` | n > 3 |
| Third iterate has period 3,1,7,5 | `a396798_third_iterate_period` | Blocks from n = 2 |
| Fourth iterate vanishes modulo eight | `a396798_fourth_iterate` | n > 2 |
| Fifth iterate has period 5,1,1,5 | `a396798_fifth_iterate_period` | Blocks from n = 2 |
| Sixth iterate vanishes modulo eight | `a396798_sixth_iterate` | n > 3 |
| Seventh iterate has period 7,1,3,5 | `a396798_seventh_iterate_period` | Blocks from n = 2 |
| Eighth iterate vanishes modulo eight | `a396798_eighth_iterate` | n > 1 |
| Corrected coefficient period 1,1,5,5 | `a396798_corrected_period` | Blocks from n = 2 |
| The coefficient at n = 3 is one, not five, modulo eight | `a396798_counterexample` | n = 3 |
| The literal period starting at n = 1 is false | `a396798_literal_period_false` | Negation of the universal source phase |

The exact integer value a(3) = 9 is derived in the manuscript and checked by the independent Python recursion. The Lean counterexample proves the sufficient residue inequality directly for the canonical coefficient; it does not need a separate exact-value theorem.

## A396807: both assertions, including all integer iterates

Namespace: `Consecutive`. Files: `Related.lean`, `IntegerIterates.lean`.

| Assertion | Declaration | Range |
|---|---|---|
| Coefficients equal one modulo ten | `a396807_residue` | n > 0 |
| Iterate coefficient equals k^(n−1) modulo ten | `a396807_integer_iterate_congruence` | All k in Z; n ≥ 1 |

`a396807_iterate_residue` additionally supplies the natural-iterate version. The signed theorem is not restricted to nonnegative k or to an auxiliary series chosen to have the expected residues.

## A393856–A393859: all six assertions

Namespace: `Hanna.Related.ScaledInverse`. Files: `Hanna/Related/ScaledInverse.lean`, `Hanna/Related/ScaledParity.lean`.

| Entry and assertion | Declaration | Range |
|---|---|---|
| A393856: one modulo five | `a393856_mod_five` | n ≥ 1 |
| A393856: odd exactly at power-of-two indices | `a393856_parity` | All natural n, including zero |
| A393857: one modulo six | `a393857_mod_six` | n ≥ 1 |
| A393858: one modulo seven | `a393858_mod_seven` | n ≥ 1 |
| A393858: odd exactly at power-of-two indices | `a393858_parity` | All natural n, including zero |
| A393859: one modulo eight | `a393859_mod_eight` | n ≥ 1 |

The formal source equation is `compose A (X-X*scaleTail q A)=X`. For the normalized series A used here, the degree-n coefficient of `scaleTail q A` equals q^(n−1) times the degree-n coefficient of A for n > 0, and its constant coefficient is zero. Thus it is exactly the division-free interpretation of A(X−X A(qX)/q)=X. `source_iff_core` proves equivalence to the reversed equation used in the recursion.

`existence_uniqueness`, `scaledSolution_equation`, and `map_scaledSolution` establish the canonical series and its reduction behavior. `integer_mod_parameter_add_one` proves the uniform modulus-q+1 theorem. `integer_coeff_odd_iff` proves the uniform parity statement whenever the parameter reduces to zero modulo two.

## Retained original repository results

The 16 declarations in `Hanna.Acceptance` are retained and included in the fresh regression audit. They concern the original A396843 family, not the new consecutive-iterate or scaled families. Their source and reference manuscript remain available for provenance; they are not included in the count of 19 newly targeted conjectures.

## What the checks establish

The clean build validates proof terms. The fixed manifest prevents silent omission of a required endpoint. Typed contracts check the intended quantified statements, while the semantic reviews examine definitions and correspondence with the equations. The transitive axiom audit accepts only `propext`, `Classical.choice`, and `Quot.sound` and rejects `sorryAx` and additional mathematical assumptions.

The finite Python computations and manuscript rendering are separately recorded. Mathematical novelty, source authorship, and the absence of all possible earlier proofs are not kernel-checkable claims. All reviews in this package were AI-assisted; independent human review is pending.
