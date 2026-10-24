import Consecutive.Coefficients

/-!
# Related OEIS conjectures

This file proves the seven correctly stated iterate conjectures in A396798,
corrects the starting phase of its first coefficient pattern, and proves the
natural-iterate assertions for A396807.  Every endpoint refers to the canonical
integer solution of the original functional equation.
-/

namespace Consecutive

open PowerSeries Hanna.Series

noncomputable section

private theorem weighted_correction_eight (n : ℕ) (hn : 2≤n) :
    coeff (ZMod 8) n (C (ZMod 8) 4*correction) =
      if n%4=0 ∨ n%4=1 then 4 else 0 := by
  rw [coeff_C_mul, coeff_correction]
  by_cases hn4 : 4≤n
  · rw [if_pos hn4, weighted_choose_two (4:ZMod 8) (by decide)]
    have hm : (n-2)%4=0 ∨ (n-2)%4=1 ↔ ¬(n%4=0 ∨ n%4=1) := by omega
    by_cases hh : n%4=0 ∨ n%4=1
    · simp [hh, hm]
    · simp [hh, hm]
  · have he : n=2 ∨ n=3 := by omega
    rcases he with rfl | rfl <;> norm_num

/-- A coefficient formula from which all A396798 patterns follow. -/
theorem a396798_iterate_residue (k n : ℕ) (hn : 2≤n) :
    (iterateCoeff 4 k n : ZMod 8) = (k:ZMod 8)^(n-1) +
      if Odd k then (if n%4=0 ∨ n%4=1 then 4 else 0) else 0 := by
  rw [show (iterateCoeff 4 k n:ZMod 8)=
    (Int.castRingHom (ZMod 8)) (iterateCoeff 4 k n) from rfl, cast_iterateCoeff]
  have hi := iter_solution_mod 4 k
  change iter (solution (R:=ZMod 8) 4) k =
    mobius (k:ZMod 8)+if Even 4 ∧ Odd k then C (ZMod 8) 4*correction else 0 at hi
  rw [hi, map_add]
  have hm : coeff (ZMod 8) n (mobius (k:ZMod 8)) = (k:ZMod 8)^(n-1) := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp
  rw [hm]
  by_cases hk : Odd k
  · simp only [show Even 4 by decide, hk, and_self, if_true]
    rw [weighted_correction_eight n hn]
  · simp only [hk, and_false, if_false, map_zero]

theorem a396798_corrected_residue (n : ℕ) (hn : 2≤n) :
    (a 4 n:ZMod 8) = if n%4=0 ∨ n%4=1 then 5 else 1 := by
  have ha : a 4 n = iterateCoeff 4 1 n := by simp [a, iterateCoeff]
  rw [ha, a396798_iterate_residue 1 n hn]
  norm_num
  split_ifs <;> norm_num

/-- The period `[1,1,5,5]` is valid from index TWO. -/
theorem a396798_corrected_period (j : ℕ) :
    (a 4 (4*j+2):ZMod 8)=1 ∧
    (a 4 (4*j+3):ZMod 8)=1 ∧
    (a 4 (4*j+4):ZMod 8)=5 ∧
    (a 4 (4*j+5):ZMod 8)=5 := by
  repeat' constructor
  all_goals rw [a396798_corrected_residue _ (by omega)]
  all_goals norm_num [Nat.add_mod, Nat.mul_mod]

/-- At index three the entry's literal starting-at-one pattern is false. -/
theorem a396798_counterexample : (a 4 3:ZMod 8)=1 ∧ (a 4 3:ZMod 8)≠5 := by
  have h : (a 4 3:ZMod 8)=1 := by
    rw [a396798_corrected_residue 3 (by omega)]
    norm_num
  constructor
  · exact h
  · rw [h]; decide

theorem a396798_literal_period_false :
    ¬(∀ j : ℕ, (a 4 (4*j+3):ZMod 8)=5) := by
  intro h
  exact a396798_counterexample.2 (by simpa using h 0)

/-- Second iterate: all coefficients above degree three vanish modulo eight. -/
theorem a396798_second_iterate (n : ℕ) (hn : 3<n) :
    (iterateCoeff 4 2 n:ZMod 8)=0 := by
  rw [a396798_iterate_residue 2 n (by omega)]
  simp only [show ¬Odd 2 by decide, if_false, add_zero]
  exact pow_eq_zero_of_le (by omega : 3≤n-1) (by decide : (2:ZMod 8)^3=0)

/-- Fourth iterate: all coefficients above degree two vanish modulo eight. -/
theorem a396798_fourth_iterate (n : ℕ) (hn : 2<n) :
    (iterateCoeff 4 4 n:ZMod 8)=0 := by
  rw [a396798_iterate_residue 4 n (by omega)]
  simp only [show ¬Odd 4 by decide, if_false, add_zero]
  exact pow_eq_zero_of_le (by omega : 2≤n-1) (by decide : (4:ZMod 8)^2=0)

/-- Sixth iterate: all coefficients above degree three vanish modulo eight. -/
theorem a396798_sixth_iterate (n : ℕ) (hn : 3<n) :
    (iterateCoeff 4 6 n:ZMod 8)=0 := by
  rw [a396798_iterate_residue 6 n (by omega)]
  simp only [show ¬Odd 6 by decide, if_false, add_zero]
  exact pow_eq_zero_of_le (by omega : 3≤n-1) (by decide : (6:ZMod 8)^3=0)

/-- Eighth iterate: all coefficients above degree one vanish modulo eight. -/
theorem a396798_eighth_iterate (n : ℕ) (hn : 1<n) :
    (iterateCoeff 4 8 n:ZMod 8)=0 := by
  rw [a396798_iterate_residue 8 n (by omega)]
  simp only [show ¬Odd 8 by decide, if_false, add_zero]
  exact pow_eq_zero_of_le (by omega : 1≤n-1) (by decide : (8:ZMod 8)^1=0)

private theorem pow_reduce_four {T : Type*} [Monoid T] (b : T) (hb : b^4=1) (n : ℕ) :
    b^n=b^(n%4) := by
  calc
    b^n = b^(4*(n/4)+n%4) := by congr 1; omega
    _ = _ := by rw [pow_add, pow_mul, hb, one_pow, one_mul]

private theorem a396798_odd_blocks (k j : ℕ) (hk : Odd k) (hp : (k:ZMod 8)^2=1) :
    (iterateCoeff 4 k (4*j+2):ZMod 8)=(k:ZMod 8) ∧
    (iterateCoeff 4 k (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 k (4*j+4):ZMod 8)=(k:ZMod 8)^3+4 ∧
    (iterateCoeff 4 k (4*j+5):ZMod 8)=5 := by
  have hfour : (k:ZMod 8)^4=1 := by
    calc
      _ = ((k:ZMod 8)^2)^2 := by ring
      _ = 1 := by rw [hp]; simp
  repeat' constructor
  all_goals rw [a396798_iterate_residue k _ (by omega), pow_reduce_four _ hfour]
  all_goals simp only [hk, if_true]
  · rw [show (4*j+2-1)%4=1 by omega]
    norm_num [Nat.add_mod, Nat.mul_mod]
  · rw [show (4*j+3-1)%4=2 by omega]
    norm_num [Nat.add_mod, Nat.mul_mod]
    exact hp
  · rw [show (4*j+4-1)%4=3 by omega]
    norm_num [Nat.add_mod, Nat.mul_mod]
  · rw [show (4*j+5-1)%4=0 by omega]
    norm_num [Nat.add_mod, Nat.mul_mod]

/-- Third iterate has the stated period `[3,1,7,5]` from index two. -/
theorem a396798_third_iterate_period (j : ℕ) :
    (iterateCoeff 4 3 (4*j+2):ZMod 8)=3 ∧
    (iterateCoeff 4 3 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 3 (4*j+4):ZMod 8)=7 ∧
    (iterateCoeff 4 3 (4*j+5):ZMod 8)=5 := by
  have h := a396798_odd_blocks 3 j (by decide) (by decide)
  norm_num at h
  exact h

/-- Fifth iterate has the stated period `[5,1,1,5]` from index two. -/
theorem a396798_fifth_iterate_period (j : ℕ) :
    (iterateCoeff 4 5 (4*j+2):ZMod 8)=5 ∧
    (iterateCoeff 4 5 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 5 (4*j+4):ZMod 8)=1 ∧
    (iterateCoeff 4 5 (4*j+5):ZMod 8)=5 := by
  have h := a396798_odd_blocks 5 j (by decide) (by decide)
  norm_num at h
  exact h

/-- Seventh iterate has the stated period `[7,1,3,5]` from index two. -/
theorem a396798_seventh_iterate_period (j : ℕ) :
    (iterateCoeff 4 7 (4*j+2):ZMod 8)=7 ∧
    (iterateCoeff 4 7 (4*j+3):ZMod 8)=1 ∧
    (iterateCoeff 4 7 (4*j+4):ZMod 8)=3 ∧
    (iterateCoeff 4 7 (4*j+5):ZMod 8)=5 := by
  have h := a396798_odd_blocks 7 j (by decide) (by decide)
  norm_num at h
  exact h

/-- A396807: every positive coefficient is one modulo ten. -/
theorem a396807_residue (n : ℕ) (hn : 0<n) : (a 5 n:ZMod 10)=1 := by
  rw [show (a 5 n:ZMod 10)=(Int.castRingHom (ZMod 10)) (a 5 n) from rfl, cast_a]
  have h := solution_mod_odd 5 (by decide)
  change solution (R:=ZMod 10) 5=mobius 1 at h
  rw [h]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp

/-- A396807: the natural-iterate formula. Integer iterates are proved separately. -/
theorem a396807_iterate_residue (k n : ℕ) (hn : 0<n) :
    (iterateCoeff 5 k n:ZMod 10)=(k:ZMod 10)^(n-1) := by
  rw [show (iterateCoeff 5 k n:ZMod 10)=
    (Int.castRingHom (ZMod 10)) (iterateCoeff 5 k n) from rfl, cast_iterateCoeff]
  have h := solution_mod_odd 5 (by decide)
  change solution (R:=ZMod 10) 5=mobius 1 at h
  rw [h, iter_mobius, mul_one]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp

end
end Consecutive
