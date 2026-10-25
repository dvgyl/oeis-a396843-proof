module

public import Related

/-!
# OEIS A393858

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A393858

open PowerSeries Hanna.Series Hanna.Related.ScaledInverse

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧
      compose F (X - X * scaleTail (6 : R) F) = X := by
  exact Hanna.Related.ScaledInverse.existence_uniqueness (6 : R)

theorem source_normalized : Normalized (scaledSolution (6 : ℤ)) := by
  exact scaledSolution_normalized 6

theorem source_equation :
    compose (scaledSolution (6 : ℤ))
      (X - X * scaleTail (6 : ℤ) (scaledSolution (6 : ℤ))) = X := by
  exact scaledSolution_equation 6

theorem a393858_mod_seven (n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (6 : ℤ)) : ℤ) : ZMod 7) = 1 := by
  exact Hanna.Related.ScaledInverse.a393858_mod_seven n hn

theorem a393858_parity (n : ℕ) :
    Odd (coeff (R := ℤ) n (scaledSolution (6 : ℤ))) ↔ ∃ k : ℕ, n = 2^k := by
  exact Hanna.Related.ScaledInverse.a393858_parity n

end OEIS.A393858
