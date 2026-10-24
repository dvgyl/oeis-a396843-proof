import Related

/-!
Separate typed proof interface for OEIS A393858.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A393858

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
    ((coeff ℤ n (scaledSolution (6 : ℤ)) : ℤ) : ZMod 7) = 1 := by
  exact Hanna.Related.ScaledInverse.a393858_mod_seven n hn

theorem a393858_parity (n : ℕ) :
    Odd (coeff ℤ n (scaledSolution (6 : ℤ))) ↔ ∃ k : ℕ, n = 2^k := by
  exact Hanna.Related.ScaledInverse.a393858_parity n

end FinalCollection.A393858
