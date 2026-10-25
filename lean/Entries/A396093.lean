module

public import Families.RationalParity

/-!
# OEIS A396093

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A396093

open PowerSeries Hanna.Series

noncomputable section

abbrev B : PowerSeries ℤ := RationalParity.B
abbrev A : PowerSeries ℤ := RationalParity.A
def a (n : ℕ) : ℤ := coeff (R := ℤ) n A

theorem source_denominator : B * (1-X)^2 = X :=
  RationalParity.B_denominator

theorem source_composition : A = compose B (compose B B) :=
  RationalParity.A_definition

theorem coefficient_definition (n : ℕ) : a n = coeff (R := ℤ) n A := rfl

theorem reduced_denominator :
    (RationalParity.A : PowerSeries (ZMod 2)) * (1+X^10) = X+X^3+X^7+X^9 :=
  RationalParity.third_period_denominator

theorem complete_parity (n : ℕ) :
    (a n : ZMod 2) =
      if n%10=1 ∨ n%10=3 ∨ n%10=7 ∨ n%10=9 then 1 else 0 :=
  RationalParity.a396093_residue n

theorem even_iff (n : ℕ) :
    Even (a n) ↔ ¬(n%10=1 ∨ n%10=3 ∨ n%10=7 ∨ n%10=9) :=
  RationalParity.a396093_even_iff n

theorem even_indices (n : ℕ) : Even (a (2*n)) :=
  RationalParity.a396093_even_indices n

theorem odd_indices (n : ℕ) (hn : 1 ≤ n) :
    Even (a (2*n-1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5*k-2 :=
  RationalParity.a396093_odd_indices_original n hn

end
end OEIS.A396093
