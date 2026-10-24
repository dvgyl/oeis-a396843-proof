import Related

/-!
Separate typed proof interface for OEIS A393857.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A393857

open PowerSeries Hanna.Series Hanna.Related.ScaledInverse

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧
      compose F (X - X * scaleTail (5 : R) F) = X := by
  exact Hanna.Related.ScaledInverse.existence_uniqueness (5 : R)

theorem source_normalized : Normalized (scaledSolution (5 : ℤ)) := by
  exact scaledSolution_normalized 5

theorem source_equation :
    compose (scaledSolution (5 : ℤ))
      (X - X * scaleTail (5 : ℤ) (scaledSolution (5 : ℤ))) = X := by
  exact scaledSolution_equation 5

theorem a393857_mod_six (n : ℕ) (hn : 1 ≤ n) :
    ((coeff ℤ n (scaledSolution (5 : ℤ)) : ℤ) : ZMod 6) = 1 := by
  exact Hanna.Related.ScaledInverse.a393857_mod_six n hn

end FinalCollection.A393857
