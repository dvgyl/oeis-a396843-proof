import Consecutive.Coefficients

/-! The four statements of OEIS A396099, for every integer series satisfying
its defining equation. No congruence is assumed. -/

namespace Consecutive

open PowerSeries Hanna.Series

theorem a396099_all_four {F : PowerSeries ℤ} (hF : Normalized F)
    (hEq : F=X+compose F F*compose F (compose F F)) :
    (∀ n : ℕ, 0<n → Odd (coeff ℤ n F)) ∧
    (∀ n : ℕ, 3≤n →
      (coeff ℤ n F:ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1) ∧
    (∀ n : ℕ, 2<n → (coeff ℤ n (compose F F):ZMod 4)=0) ∧
    (∀ n : ℕ, 2<n →
      (coeff ℤ n (F-X*compose F (compose F F)):ZMod 4)=2) := by
  have hcanon : F=solution (R:=ℤ) 2 := by
    apply solution_unique 2 hF (solution_normalized 2) _ (solution_equation 2)
    simpa only [step, iter_succ, iter_zero, compose_X_right] using hEq
  subst F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    exact a396099_odd n hn
  · intro n hn
    exact a396099_residue n hn
  · intro n hn
    simpa only [iterateCoeff, iter_succ, iter_zero, compose_X_right] using
      a396099_second_iterate n hn
  · intro n hn
    simpa only [iter_succ, iter_zero, compose_X_right] using a396099_difference n hn

end Consecutive
