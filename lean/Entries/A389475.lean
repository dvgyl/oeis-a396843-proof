import Families.CubicConsequences

/-!
# OEIS A389475

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A389475

open PowerSeries Hanna.Series


noncomputable section

abbrev A : PowerSeries ℤ := Families.CubicReversion.a389475

theorem normalized : coeff ℤ 0 A = 0 ∧ coeff ℤ 1 A = 1 :=
  Families.CubicReversion.a389475_normalized

theorem source_equation : compose A (3*X^2) = 2*X^2+A^2-2*A^3 :=
  Families.CubicReversion.a389475_equation

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (3*X^2) = 2*X^2+U^2-2*U^3) : U = A :=
  Families.CubicReversion.a389475_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2-2*U^3 :=
  Families.CubicReversion.a389475_existence_uniqueness

theorem integral_family_existence (s : ℤ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2+2*C ℤ s*U^3 :=
  Families.CubicReversion.existence_uniqueness s

theorem cube_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (A^3) =
      PowerSeries.map (Int.castRingHom (ZMod 3)) (compose A (X^3)) :=
  Families.CubicReversion.a389475_cube_mod_three

theorem square_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (A^2) =
      X^2+2*PowerSeries.map (Int.castRingHom (ZMod 3)) (compose A (X^3)) :=
  Families.CubicReversion.a389475_square_mod_three

theorem cube_coefficients (n : ℕ) :
    (coeff ℤ n (A^3-compose A (X^3)) : ZMod 3) = 0 :=
  Families.CubicReversion.a389475_conjecture_4a n

theorem square_coefficients (n : ℕ) :
    (coeff ℤ n (A^2-X^2-2*compose A (X^3)) : ZMod 3) = 0 :=
  Families.CubicReversion.a389475_conjecture_4b n

end
end OEIS.A389475
