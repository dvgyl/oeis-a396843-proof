import Related

/-!
# OEIS A393859

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

namespace OEIS.A393859

open PowerSeries Hanna.Series Hanna.Related.ScaledInverse

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧
      compose F (X - X * scaleTail (7 : R) F) = X := by
  exact Hanna.Related.ScaledInverse.existence_uniqueness (7 : R)

theorem source_normalized : Normalized (scaledSolution (7 : ℤ)) := by
  exact scaledSolution_normalized 7

theorem source_equation :
    compose (scaledSolution (7 : ℤ))
      (X - X * scaleTail (7 : ℤ) (scaledSolution (7 : ℤ))) = X := by
  exact scaledSolution_equation 7

theorem a393859_mod_eight (n : ℕ) (hn : 1 ≤ n) :
    ((coeff ℤ n (scaledSolution (7 : ℤ)) : ℤ) : ZMod 8) = 1 := by
  exact Hanna.Related.ScaledInverse.a393859_mod_eight n hn

end OEIS.A393859
