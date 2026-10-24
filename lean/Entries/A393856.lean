import Related

/-!
Separate typed proof interface for OEIS A393856.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A393856

open PowerSeries Hanna.Series Hanna.Related.ScaledInverse

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧
      compose F (X - X * scaleTail (4 : R) F) = X := by
  exact Hanna.Related.ScaledInverse.existence_uniqueness (4 : R)

theorem source_normalized : Normalized (scaledSolution (4 : ℤ)) := by
  exact scaledSolution_normalized 4

theorem source_equation :
    compose (scaledSolution (4 : ℤ))
      (X - X * scaleTail (4 : ℤ) (scaledSolution (4 : ℤ))) = X := by
  exact scaledSolution_equation 4

theorem a393856_mod_five (n : ℕ) (hn : 1 ≤ n) :
    ((coeff ℤ n (scaledSolution (4 : ℤ)) : ℤ) : ZMod 5) = 1 := by
  exact Hanna.Related.ScaledInverse.a393856_mod_five n hn

theorem a393856_parity (n : ℕ) :
    Odd (coeff ℤ n (scaledSolution (4 : ℤ))) ↔ ∃ k : ℕ, n = 2^k := by
  exact Hanna.Related.ScaledInverse.a393856_parity n

end FinalCollection.A393856
