import Consecutive

/-!
Separate typed proof interface for OEIS A396807.
The complete implementation is in the imported, preserved libraries.
AI disclosure: ChatGPT (OpenAI) generated this presentation for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace FinalCollection.A396807

open PowerSeries Consecutive
open Hanna.Series (Normalized compose compose_X_right)

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧ F = X + iter F 5 * iter F 6 := by
  exact Consecutive.existence_uniqueness 5

theorem source_normalized : Normalized (solution (R:=ℤ) 5) := by
  exact Consecutive.solution_normalized 5

theorem source_equation :
    solution (R:=ℤ) 5 = X + iter (solution (R:=ℤ) 5) 5 *
      iter (solution (R:=ℤ) 5) 6 := by
  exact Consecutive.solution_equation 5

theorem exact_composition_order (k : ℤ) :
    ziter (solution (R:=ZMod 10) 5) (solution_normalized 5) k = X ↔
      (10 : ℤ) ∣ k := by
  exact Consecutive.ziter_solution_mod_eq_X_iff 5 (by decide) k

theorem a396807_residue (n : ℕ) (hn : 0<n) : (a 5 n:ZMod 10)=1 := by
  exact Consecutive.a396807_residue n hn

theorem a396807_iterate_residue (k n : ℕ) (hn : 0<n) :
    (iterateCoeff 5 k n:ZMod 10)=(k:ZMod 10)^(n-1) := by
  exact Consecutive.a396807_iterate_residue k n hn

theorem a396807_integer_iterate_congruence (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    (integerIterateCoeff 5 k n : ZMod 10) = (k : ZMod 10)^(n-1) := by
  exact Consecutive.a396807_integer_iterate_congruence k n hn

end FinalCollection.A396807
