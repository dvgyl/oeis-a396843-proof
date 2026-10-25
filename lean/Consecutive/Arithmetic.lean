module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-! Elementary coefficient arithmetic, proved for every index. -/

@[expose] public section

namespace Consecutive

theorem choose_two_add_four (n : ℕ) :
    (n+4).choose 2 = n.choose 2 + 4*n + 6 := by
  have h (m : ℕ) : (m+1).choose 2 = m + m.choose 2 := by
    simpa using Nat.choose_succ_succ m 1
  rw [show n+4=(n+3)+1 by omega, h, show n+3=(n+2)+1 by omega, h,
    show n+2=(n+1)+1 by omega, h, h]
  omega

theorem weighted_choose_two_periodic {R : Type*} [CommRing R]
    (c : R) (hc : 2*c=0) (n : ℕ) :
    c*((n+4).choose 2:R) = c*(n.choose 2:R) := by
  rw [choose_two_add_four]
  push_cast
  linear_combination (2*(n:R)+3)*hc

theorem weighted_choose_two {R : Type*} [CommRing R]
    (c : R) (hc : 2*c=0) (n : ℕ) :
    c*(n.choose 2:R) = if n%4=0 ∨ n%4=1 then 0 else c := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> norm_num
      linear_combination hc
    · have hn4 : n-4+4=n := by omega
      have he := weighted_choose_two_periodic c hc (n-4)
      rw [hn4, ih (n-4) (by omega)] at he
      have hm : (n-4)%4=n%4 := by omega
      simpa only [hm] using he

end Consecutive
