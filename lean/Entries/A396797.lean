import Consecutive

/-!
Separate typed proof interface for OEIS A396797.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A396797

open PowerSeries Consecutive
open Hanna.Series (Normalized compose compose_X_right)

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧ F = X + iter F 3 * iter F 4 := by
  exact Consecutive.existence_uniqueness 3

theorem source_normalized : Normalized (solution (R:=ℤ) 3) := by
  exact Consecutive.solution_normalized 3

theorem source_equation :
    solution (R:=ℤ) 3 = X + iter (solution (R:=ℤ) 3) 3 *
      iter (solution (R:=ℤ) 3) 4 := by
  exact Consecutive.solution_equation 3

theorem integer_iterate_congruence (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    (integerIterateCoeff 3 k n : ZMod 6) = (k : ZMod 6)^(n-1) := by
  exact Consecutive.integerIterateCoeff_mod_odd 3 (by decide) k n hn

theorem positive_coefficients (n : ℕ) (hn : 1 ≤ n) :
    (a 3 n : ZMod 6) = 1 := by
  have h := Consecutive.integerIterateCoeff_mod_odd 3 (by decide) 1 n hn
  simpa [integerIterateCoeff, ziter, a, iter_succ, iter_zero, compose_X_right] using h

theorem exact_composition_order (k : ℤ) :
    ziter (solution (R:=ZMod 6) 3) (solution_normalized 3) k = X ↔
      (6 : ℤ) ∣ k := by
  exact Consecutive.ziter_solution_mod_eq_X_iff 3 (by decide) k

end FinalCollection.A396797
