module

public import Families.CubicConsequences

/-!
# OEIS A389474

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A389474

open PowerSeries Hanna.Series

noncomputable section

abbrev A : PowerSeries ℤ := Families.CubicReversion.a389474

theorem normalized : coeff (R := ℤ) 0 A = 0 ∧ coeff (R := ℤ) 1 A = 1 :=
  Families.CubicReversion.a389474_normalized

theorem source_equation : compose A (X^2+2*X^3+2*A^2) = 3*A^2 :=
  Families.CubicReversion.a389474_equation

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (X^2+2*X^3+2*U^2) = 3*U^2) : U = A :=
  Families.CubicReversion.a389474_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (X^2+2*X^3+2*U^2) = 3*U^2 :=
  Families.CubicReversion.a389474_existence_uniqueness

theorem integral_family_existence (s : ℤ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2+2*C (R := ℤ) s*U^3 :=
  Families.CubicReversion.existence_uniqueness s

theorem square_mod_nine :
    PowerSeries.map (Int.castRingHom (ZMod 9)) (A^2) = X^2+2*X^3 :=
  Families.CubicReversion.a389474_square_mod_nine

theorem square_coefficients (n : ℕ) (hn : 3 < n) :
    (coeff (R := ℤ) n (A^2) : ZMod 9) = 0 :=
  Families.CubicReversion.a389474_conjecture_3 n hn

theorem power_coefficients (n k : ℕ) :
    (coeff (R := ℤ) n (A^(3*k)-(compose A (X^3))^k) : ZMod 3) = 0 :=
  Families.CubicReversion.a389474_conjecture_4 n k

end
end OEIS.A389474
