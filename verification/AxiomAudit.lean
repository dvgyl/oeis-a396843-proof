/-
Axiom audit for the 34 entry files (written by Claude Opus 5.5, used with Claude Code, for the independent check).

Run from the `lean/` folder after `lake build Entries`:

    lake env lean ../verification/AxiomAudit.lean

For every theorem stated in `lean/Entries/*.lean`, Lean prints the axioms it
depends on, transitively. The expected answer for each is a subset of
`[propext, Classical.choice, Quot.sound]`; anything else (in particular
`sorryAx`) would be a failure. `verification/check_axioms.py` checks the output.
-/
import Entries

-- A052895
#print axioms FinalCollection.A052895.source_formula
#print axioms FinalCollection.A052895.period
#print axioms FinalCollection.A052895.least_period_divides
#print axioms FinalCollection.A052895.least_period_specification

-- A064618
#print axioms FinalCollection.A064618.source_formula
#print axioms FinalCollection.A064618.period
#print axioms FinalCollection.A064618.least_period_divides
#print axioms FinalCollection.A064618.least_period_specification

-- A080253
#print axioms FinalCollection.A080253.source_formula
#print axioms FinalCollection.A080253.period
#print axioms FinalCollection.A080253.least_period_divides
#print axioms FinalCollection.A080253.least_period_specification
#print axioms FinalCollection.A080253.weight_zero
#print axioms FinalCollection.A080253.weight_one
#print axioms FinalCollection.A080253.weight_recursion

-- A167137
#print axioms FinalCollection.A167137.source_formula
#print axioms FinalCollection.A167137.period
#print axioms FinalCollection.A167137.least_period_divides
#print axioms FinalCollection.A167137.least_period_specification

-- A195194
#print axioms FinalCollection.A195194.normalized_source
#print axioms FinalCollection.A195194.all_tails_normalized
#print axioms FinalCollection.A195194.all_tails_source
#print axioms FinalCollection.A195194.nested_definition_unique
#print axioms FinalCollection.A195194.first_tail_reversion
#print axioms FinalCollection.A195194.finite_nest_coefficients
#print axioms FinalCollection.A195194.binary_equation
#print axioms FinalCollection.A195194.exact_parity
#print axioms FinalCollection.A195194.arbitrary_weights_unique
#print axioms FinalCollection.A195194.arbitrary_finite_depth

-- A305550
#print axioms FinalCollection.A305550.source_formula
#print axioms FinalCollection.A305550.period
#print axioms FinalCollection.A305550.least_period_divides
#print axioms FinalCollection.A305550.least_period_specification

-- A306082
#print axioms FinalCollection.A306082.source_formula
#print axioms FinalCollection.A306082.period
#print axioms FinalCollection.A306082.least_period_divides
#print axioms FinalCollection.A306082.least_period_specification
#print axioms FinalCollection.A306082.square_weight_definition

-- A354242
#print axioms FinalCollection.A354242.source_formula
#print axioms FinalCollection.A354242.period
#print axioms FinalCollection.A354242.least_period_divides
#print axioms FinalCollection.A354242.least_period_specification

-- A378580
#print axioms FinalCollection.A378580.theta_constant_term
#print axioms FinalCollection.A378580.theta_coefficient_formula
#print axioms FinalCollection.A378580.minus_constant
#print axioms FinalCollection.A378580.quotient_identity
#print axioms FinalCollection.A378580.minus_source
#print axioms FinalCollection.A378580.minus_exists_unique
#print axioms FinalCollection.A378580.minus_unique
#print axioms FinalCollection.A378580.minus_series_mod_four
#print axioms FinalCollection.A378580.minus_congruence
#print axioms FinalCollection.A378580.minus_square_iff
#print axioms FinalCollection.A378580.minus_four_dvd_iff

-- A378581
#print axioms FinalCollection.A378581.theta_constant_term
#print axioms FinalCollection.A378581.theta_coefficient_formula
#print axioms FinalCollection.A378581.plus_constant
#print axioms FinalCollection.A378581.plus_source
#print axioms FinalCollection.A378581.plus_exists_unique
#print axioms FinalCollection.A378581.plus_unique
#print axioms FinalCollection.A378581.plus_series_mod_four
#print axioms FinalCollection.A378581.plus_congruence
#print axioms FinalCollection.A378581.plus_square_iff
#print axioms FinalCollection.A378581.plus_four_dvd_iff

-- A380056
#print axioms FinalCollection.A380056.integer_egf_definition
#print axioms FinalCollection.A380056.source_egf
#print axioms FinalCollection.A380056.literal_source_equation
#print axioms FinalCollection.A380056.literal_source_unique
#print axioms FinalCollection.A380056.integer_coefficients
#print axioms FinalCollection.A380056.first_source_conjecture
#print axioms FinalCollection.A380056.second_source_conjecture
#print axioms FinalCollection.A380056.exact_mod_five_pattern
#print axioms FinalCollection.A380056.exact_divisibility_by_five
#print axioms FinalCollection.A380056.mod_five_exponential_formula
#print axioms FinalCollection.A380056.mod_five_period

-- A380060
#print axioms FinalCollection.A380060.implicit_source_exists_unique
#print axioms FinalCollection.A380060.implicit_actual_source
#print axioms FinalCollection.A380060.a380060_statement
#print axioms FinalCollection.A380060.complete_series_mod_four

-- A380680
#print axioms FinalCollection.A380680.explicit_actual_source
#print axioms FinalCollection.A380680.a380680_corrected_statement
#print axioms FinalCollection.A380680.a380680_counterexamples
#print axioms FinalCollection.A380680.a380680_literal_statement_is_false
#print axioms FinalCollection.A380680.a380680_complement_is_false
#print axioms FinalCollection.A380680.complete_series_mod_four

-- A389474
#print axioms FinalCollection.A389474.normalized
#print axioms FinalCollection.A389474.source_equation
#print axioms FinalCollection.A389474.source_unique
#print axioms FinalCollection.A389474.source_existence_uniqueness
#print axioms FinalCollection.A389474.integral_family_existence
#print axioms FinalCollection.A389474.square_mod_nine
#print axioms FinalCollection.A389474.square_coefficients
#print axioms FinalCollection.A389474.power_coefficients

-- A389475
#print axioms FinalCollection.A389475.normalized
#print axioms FinalCollection.A389475.source_equation
#print axioms FinalCollection.A389475.source_unique
#print axioms FinalCollection.A389475.source_existence_uniqueness
#print axioms FinalCollection.A389475.integral_family_existence
#print axioms FinalCollection.A389475.cube_mod_three
#print axioms FinalCollection.A389475.square_mod_three
#print axioms FinalCollection.A389475.cube_coefficients
#print axioms FinalCollection.A389475.square_coefficients

-- A389536
#print axioms FinalCollection.A389536.mahler_existence
#print axioms FinalCollection.A389536.mahler_definition
#print axioms FinalCollection.A389536.mahler_source_unique
#print axioms FinalCollection.A389536.mahler_mod_four
#print axioms FinalCollection.A389536.mahler_residue
#print axioms FinalCollection.A389536.mahler_four_dvd_iff

-- A389537
#print axioms FinalCollection.A389537.auxiliary_exists_unique
#print axioms FinalCollection.A389537.auxiliary_equation
#print axioms FinalCollection.A389537.inverse_right
#print axioms FinalCollection.A389537.inverse_left
#print axioms FinalCollection.A389537.normalized
#print axioms FinalCollection.A389537.source_equation
#print axioms FinalCollection.A389537.source_exists_unique
#print axioms FinalCollection.A389537.source_unique
#print axioms FinalCollection.A389537.series_mod_two
#print axioms FinalCollection.A389537.integer_decomposition
#print axioms FinalCollection.A389537.half_equation_mod_two
#print axioms FinalCollection.A389537.half_binary_support
#print axioms FinalCollection.A389537.residue_mod_four

-- A389542
#print axioms FinalCollection.A389542.auxiliary_exists_unique
#print axioms FinalCollection.A389542.normalized
#print axioms FinalCollection.A389542.auxiliary_definition
#print axioms FinalCollection.A389542.inverse_equation
#print axioms FinalCollection.A389542.inverse_right
#print axioms FinalCollection.A389542.inverse_left
#print axioms FinalCollection.A389542.source_equation
#print axioms FinalCollection.A389542.source_exists_unique
#print axioms FinalCollection.A389542.source_unique
#print axioms FinalCollection.A389542.auxiliary_parity
#print axioms FinalCollection.A389542.inverse_involution
#print axioms FinalCollection.A389542.inverse_mod_four
#print axioms FinalCollection.A389542.series_mod_four
#print axioms FinalCollection.A389542.residue_mod_four
#print axioms FinalCollection.A389542.exceptional_iff
#print axioms FinalCollection.A389542.four_dvd_iff

-- A392210
#print axioms FinalCollection.A392210.third_existence
#print axioms FinalCollection.A392210.third_definition
#print axioms FinalCollection.A392210.third_evenness
#print axioms FinalCollection.A392210.third_arbitrary_source

-- A393171
#print axioms FinalCollection.A393171.second_existence
#print axioms FinalCollection.A393171.second_named_existence
#print axioms FinalCollection.A393171.second_definition
#print axioms FinalCollection.A393171.second_residue
#print axioms FinalCollection.A393171.second_arbitrary_source
#print axioms FinalCollection.A393171.link_to_first_sequence
#print axioms FinalCollection.A393171.link_composed_catalan
#print axioms FinalCollection.A393171.complete_series_mod_eight
#print axioms FinalCollection.A393171.divisibility_complement

-- A393172
#print axioms FinalCollection.A393172.first_existence
#print axioms FinalCollection.A393172.first_definition
#print axioms FinalCollection.A393172.first_residue
#print axioms FinalCollection.A393172.first_arbitrary_source
#print axioms FinalCollection.A393172.complete_series_mod_four
#print axioms FinalCollection.A393172.divisibility_complement

-- A393856
#print axioms FinalCollection.A393856.source_existence_uniqueness
#print axioms FinalCollection.A393856.source_normalized
#print axioms FinalCollection.A393856.source_equation
#print axioms FinalCollection.A393856.a393856_mod_five
#print axioms FinalCollection.A393856.a393856_parity

-- A393857
#print axioms FinalCollection.A393857.source_existence_uniqueness
#print axioms FinalCollection.A393857.source_normalized
#print axioms FinalCollection.A393857.source_equation
#print axioms FinalCollection.A393857.a393857_mod_six

-- A393858
#print axioms FinalCollection.A393858.source_existence_uniqueness
#print axioms FinalCollection.A393858.source_normalized
#print axioms FinalCollection.A393858.source_equation
#print axioms FinalCollection.A393858.a393858_mod_seven
#print axioms FinalCollection.A393858.a393858_parity

-- A393859
#print axioms FinalCollection.A393859.source_existence_uniqueness
#print axioms FinalCollection.A393859.source_normalized
#print axioms FinalCollection.A393859.source_equation
#print axioms FinalCollection.A393859.a393859_mod_eight

-- A396093
#print axioms FinalCollection.A396093.source_denominator
#print axioms FinalCollection.A396093.source_composition
#print axioms FinalCollection.A396093.coefficient_definition
#print axioms FinalCollection.A396093.reduced_denominator
#print axioms FinalCollection.A396093.complete_parity
#print axioms FinalCollection.A396093.even_iff
#print axioms FinalCollection.A396093.even_indices
#print axioms FinalCollection.A396093.odd_indices

-- A396099
#print axioms FinalCollection.A396099.source_existence_uniqueness
#print axioms FinalCollection.A396099.source_normalized
#print axioms FinalCollection.A396099.source_equation
#print axioms FinalCollection.A396099.exact_composition_order
#print axioms FinalCollection.A396099.a396099_all_four
#print axioms FinalCollection.A396099.a396099_odd
#print axioms FinalCollection.A396099.a396099_residue
#print axioms FinalCollection.A396099.a396099_period
#print axioms FinalCollection.A396099.a396099_second_iterate_series
#print axioms FinalCollection.A396099.a396099_second_iterate
#print axioms FinalCollection.A396099.a396099_difference_series
#print axioms FinalCollection.A396099.a396099_difference

-- A396102
#print axioms FinalCollection.A396102.normalized
#print axioms FinalCollection.A396102.source_equation
#print axioms FinalCollection.A396102.source_unique
#print axioms FinalCollection.A396102.source_existence_uniqueness
#print axioms FinalCollection.A396102.coefficient_congruence
#print axioms FinalCollection.A396102.iterate_congruence
#print axioms FinalCollection.A396102.family_source_existence
#print axioms FinalCollection.A396102.family_source_equation
#print axioms FinalCollection.A396102.auxiliary_source_equation
#print axioms FinalCollection.A396102.inverse_right
#print axioms FinalCollection.A396102.inverse_left
#print axioms FinalCollection.A396102.family_coefficient_congruence
#print axioms FinalCollection.A396102.family_iterate_congruence

-- A396797
#print axioms FinalCollection.A396797.source_existence_uniqueness
#print axioms FinalCollection.A396797.source_normalized
#print axioms FinalCollection.A396797.source_equation
#print axioms FinalCollection.A396797.integer_iterate_congruence
#print axioms FinalCollection.A396797.positive_coefficients
#print axioms FinalCollection.A396797.exact_composition_order

-- A396798
#print axioms FinalCollection.A396798.source_existence_uniqueness
#print axioms FinalCollection.A396798.source_normalized
#print axioms FinalCollection.A396798.source_equation
#print axioms FinalCollection.A396798.exact_composition_order
#print axioms FinalCollection.A396798.a396798_iterate_residue
#print axioms FinalCollection.A396798.a396798_corrected_residue
#print axioms FinalCollection.A396798.a396798_corrected_period
#print axioms FinalCollection.A396798.a396798_counterexample
#print axioms FinalCollection.A396798.a396798_literal_period_false
#print axioms FinalCollection.A396798.a396798_second_iterate
#print axioms FinalCollection.A396798.a396798_fourth_iterate
#print axioms FinalCollection.A396798.a396798_sixth_iterate
#print axioms FinalCollection.A396798.a396798_eighth_iterate
#print axioms FinalCollection.A396798.a396798_third_iterate_period
#print axioms FinalCollection.A396798.a396798_fifth_iterate_period
#print axioms FinalCollection.A396798.a396798_seventh_iterate_period

-- A396807
#print axioms FinalCollection.A396807.source_existence_uniqueness
#print axioms FinalCollection.A396807.source_normalized
#print axioms FinalCollection.A396807.source_equation
#print axioms FinalCollection.A396807.exact_composition_order
#print axioms FinalCollection.A396807.a396807_residue
#print axioms FinalCollection.A396807.a396807_iterate_residue
#print axioms FinalCollection.A396807.a396807_integer_iterate_congruence

-- A396843
#print axioms FinalCollection.A396843.existence_uniqueness
#print axioms FinalCollection.A396843.compositional_inverse
#print axioms FinalCollection.A396843.coefficient_polynomial_specialization
#print axioms FinalCollection.A396843.parity_odd
#print axioms FinalCollection.A396843.parity_even
#print axioms FinalCollection.A396843.mod_parameter_squared
#print axioms FinalCollection.A396843.binary_divisibility_polynomial
#print axioms FinalCollection.A396843.inverse_binary_divisibility_polynomial
#print axioms FinalCollection.A396843.binary_divisibility_integer
#print axioms FinalCollection.A396843.inverse_binary_divisibility_integer
#print axioms FinalCollection.A396843.power_of_two_index
#print axioms FinalCollection.A396843.prime_divisibility_lower_bound
#print axioms FinalCollection.A396843.prime_exponent_exists_unique
#print axioms FinalCollection.A396843.minimum_prime_exponent_iff
#print axioms FinalCollection.A396843.residues_parameter_three
#print axioms FinalCollection.A396843.residues_parameter_four
#print axioms FinalCollection.A396843.a396843_parity

-- A396844
#print axioms FinalCollection.A396844.source_existence_uniqueness
#print axioms FinalCollection.A396844.even_positive_tail
#print axioms FinalCollection.A396844.binary_divisibility
#print axioms FinalCollection.A396844.residues_parameter_four

-- A397588
#print axioms FinalCollection.A397588.differential_existence
#print axioms FinalCollection.A397588.differential_definition
#print axioms FinalCollection.A397588.differential_source_unique
#print axioms FinalCollection.A397588.differential_parity
#print axioms FinalCollection.A397588.differential_mod_three
#print axioms FinalCollection.A397588.differential_divisible_by_three

-- General theorems from the shared modules that the papers cite directly
-- (the entry theorems above depend on them, so they are also covered indirectly)
#print axioms Consecutive.existence_uniqueness
#print axioms Consecutive.ziter_solution_mod
#print axioms Consecutive.ziter_solution_mod_eq_X_iff
#print axioms Hanna.Related.ScaledInverse.integer_mod_parameter_add_one
#print axioms Hanna.Related.ScaledInverse.integer_coeff_odd_iff
#print axioms More.Stirling.transform_totient_period
