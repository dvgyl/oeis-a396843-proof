module

public import Consecutive

/-!
# OEIS A396798

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A396798

open PowerSeries Consecutive
open Hanna.Series (Normalized compose compose_X_right)

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧ F = X + iter F 4 * iter F 5 := by
  exact Consecutive.existence_uniqueness 4

theorem source_normalized : Normalized (solution (R:=ℤ) 4) := by
  exact Consecutive.solution_normalized 4

theorem source_equation :
    solution (R:=ℤ) 4 = X + iter (solution (R:=ℤ) 4) 4 *
      iter (solution (R:=ℤ) 4) 5 := by
  exact Consecutive.solution_equation 4

theorem exact_composition_order (k : ℤ) :
    ziter (solution (R:=ZMod 8) 4) (solution_normalized 4) k = X ↔
      (8 : ℤ) ∣ k := by
  exact Consecutive.ziter_solution_mod_eq_X_iff 4 (by decide) k

theorem a396798_iterate_residue (k n : ℕ) (hn : 2≤n) :
    (iterateCoeff 4 k n : ZMod 8) = (k:ZMod 8)^(n-1) +
      if Odd k then (if n%4=0 ∨ n%4=1 then 4 else 0) else 0 := by
  exact Consecutive.a396798_iterate_residue k n hn

theorem a396798_corrected_residue (n : ℕ) (hn : 2≤n) :
    (a 4 n:ZMod 8) = if n%4=0 ∨ n%4=1 then 5 else 1 := by
  exact Consecutive.a396798_corrected_residue n hn

theorem a396798_corrected_period (j : ℕ) :
    (a 4 (4*j+2):ZMod 8)=1 ∧
    (a 4 (4*j+3):ZMod 8)=1 ∧
    (a 4 (4*j+4):ZMod 8)=5 ∧
    (a 4 (4*j+5):ZMod 8)=5 := by
  exact Consecutive.a396798_corrected_period j

theorem a396798_counterexample : (a 4 3:ZMod 8)=1 ∧ (a 4 3:ZMod 8)≠5 := by
  exact Consecutive.a396798_counterexample

theorem a396798_literal_period_false :
    ¬(∀ j : ℕ, (a 4 (4*j+3):ZMod 8)=5) := by
  exact Consecutive.a396798_literal_period_false

theorem a396798_second_iterate (n : ℕ) (hn : 3<n) :
    (iterateCoeff 4 2 n:ZMod 8)=0 := by
  exact Consecutive.a396798_second_iterate n hn

theorem a396798_fourth_iterate (n : ℕ) (hn : 2<n) :
    (iterateCoeff 4 4 n:ZMod 8)=0 := by
  exact Consecutive.a396798_fourth_iterate n hn

theorem a396798_sixth_iterate (n : ℕ) (hn : 3<n) :
    (iterateCoeff 4 6 n:ZMod 8)=0 := by
  exact Consecutive.a396798_sixth_iterate n hn

theorem a396798_eighth_iterate (n : ℕ) (hn : 1<n) :
    (iterateCoeff 4 8 n:ZMod 8)=0 := by
  exact Consecutive.a396798_eighth_iterate n hn

theorem a396798_third_iterate_period (j : ℕ) :
    (iterateCoeff 4 3 (4*j+2):ZMod 8)=3 ∧
    (iterateCoeff 4 3 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 3 (4*j+4):ZMod 8)=7 ∧
    (iterateCoeff 4 3 (4*j+5):ZMod 8)=5 := by
  exact Consecutive.a396798_third_iterate_period j

theorem a396798_fifth_iterate_period (j : ℕ) :
    (iterateCoeff 4 5 (4*j+2):ZMod 8)=5 ∧
    (iterateCoeff 4 5 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 5 (4*j+4):ZMod 8)=1 ∧
    (iterateCoeff 4 5 (4*j+5):ZMod 8)=5 := by
  exact Consecutive.a396798_fifth_iterate_period j

theorem a396798_seventh_iterate_period (j : ℕ) :
    (iterateCoeff 4 7 (4*j+2):ZMod 8)=7 ∧
    (iterateCoeff 4 7 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 7 (4*j+4):ZMod 8)=3 ∧
    (iterateCoeff 4 7 (4*j+5):ZMod 8)=5 := by
  exact Consecutive.a396798_seventh_iterate_period j

end OEIS.A396798
