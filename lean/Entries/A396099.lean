module

public import Consecutive

/-!
# OEIS A396099

Statements of the results in the accompanying paper (listed in `CONTENTS.md` at the
repository root), proved using the shared libraries of this project.
Formalization written by ChatGPT (OpenAI) for Dev D. Goyal.
-/

@[expose] public section

namespace OEIS.A396099

open PowerSeries Consecutive
open Hanna.Series (Normalized compose compose_X_right)

theorem source_existence_uniqueness (R : Type*) [CommRing R] :
    ∃! F : PowerSeries R, Normalized F ∧ F = X + iter F 2 * iter F 3 := by
  exact Consecutive.existence_uniqueness 2

theorem source_normalized : Normalized (solution (R:=ℤ) 2) := by
  exact Consecutive.solution_normalized 2

theorem source_equation :
    solution (R:=ℤ) 2 = X + iter (solution (R:=ℤ) 2) 2 *
      iter (solution (R:=ℤ) 2) 3 := by
  exact Consecutive.solution_equation 2

theorem exact_composition_order (k : ℤ) :
    ziter (solution (R:=ZMod 4) 2) (solution_normalized 2) k = X ↔
      (4 : ℤ) ∣ k := by
  exact Consecutive.ziter_solution_mod_eq_X_iff 2 (by decide) k

theorem a396099_all_four {F : PowerSeries ℤ} (hF : Normalized F)
    (hEq : F=X+compose F F*compose F (compose F F)) :
    (∀ n : ℕ, 0<n → Odd (coeff (R := ℤ) n F)) ∧
    (∀ n : ℕ, 3≤n →
      (coeff (R := ℤ) n F:ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1) ∧
    (∀ n : ℕ, 2<n → (coeff (R := ℤ) n (compose F F):ZMod 4)=0) ∧
    (∀ n : ℕ, 2<n →
      (coeff (R := ℤ) n (F-X*compose F (compose F F)):ZMod 4)=2) := by
  exact Consecutive.a396099_all_four (F := F) hF hEq

theorem a396099_odd (n : ℕ) (hn : 0<n) : Odd (a 2 n) := by
  exact Consecutive.a396099_odd n hn

theorem a396099_residue (n : ℕ) (hn : 3≤n) :
    (a 2 n : ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1 := by
  exact Consecutive.a396099_residue n hn

theorem a396099_period (j : ℕ) :
    (a 2 (4*j+3):ZMod 4)=1 ∧
    (a 2 (4*j+4):ZMod 4)=3 ∧
    (a 2 (4*j+5):ZMod 4)=3 ∧
    (a 2 (4*j+6):ZMod 4)=1 := by
  exact Consecutive.a396099_period j

theorem a396099_second_iterate_series :
    iter (solution (R:=ZMod 4) 2) 2=X+C (R := (ZMod 4)) 2*X^2 := by
  exact Consecutive.a396099_second_iterate_series

theorem a396099_second_iterate (n : ℕ) (hn : 2<n) :
    (iterateCoeff 2 2 n:ZMod 4)=0 := by
  exact Consecutive.a396099_second_iterate n hn

theorem a396099_difference_series :
    solution (R:=ZMod 4) 2-X*iter (solution (R:=ZMod 4) 2) 3=
      X+C (R := (ZMod 4)) 2*X^3*geom 1 := by
  exact Consecutive.a396099_difference_series

theorem a396099_difference (n : ℕ) (hn : 2<n) :
    (coeff (R := ℤ) n (solution (R:=ℤ) 2-X*iter (solution (R:=ℤ) 2) 3):ZMod 4)=2 := by
  exact Consecutive.a396099_difference n hn

end OEIS.A396099
