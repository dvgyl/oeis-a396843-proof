import Hanna

/-!
Print the transitive axiom dependencies of the main proved results.
The expected dependencies are Lean's standard logical axioms only;
there must be no `sorryAx` or user-declared mathematical axioms.
Run with `lake env lean Audit.lean` after `lake build`.
-/

#print axioms Hanna.binaryWeight_add_le
#print axioms Hanna.binaryWeight_sum_le
#print axioms Hanna.binaryWeight_mul_two_pow
#print axioms Hanna.binaryWeight_two_pow_sub_one
#print axioms Hanna.binaryWeight_eq_one_iff
#print axioms Hanna.two_le_binaryWeight_of_not_power
#print axioms Hanna.binaryWeight_power_dvd_product
#print axioms Hanna.binaryWeight_power_dvd_sum_products
#print axioms Hanna.binaryWeight_power_dvd_quadratic_term

-- Small specializations of the general theorems.
example : Hanna.binaryWeight 7 = 3 := Hanna.binaryWeight_two_pow_sub_one 3
example : Hanna.binaryWeight 8 = 1 := Hanna.binaryWeight_two_pow 3
example : Hanna.binaryWeight 31 = 5 := Hanna.binaryWeight_two_pow_sub_one 5
example : Hanna.binaryWeight 63 = 6 := Hanna.binaryWeight_two_pow_sub_one 6
