import Consecutive.Construction
import Consecutive.Modular
import Consecutive.Arithmetic

/-!
# Coefficient consequences for the canonical integer solutions

The endpoints below refer to `solution`, constructed from the defining
functional equation in `Construction`, rather than to an assumed sequence
of coefficients satisfying the desired congruences.
-/

namespace Consecutive

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

@[simp] theorem coeff_mobius_succ (c : R) (n : ℕ) :
    coeff R (n+1) (mobius c)=c^n := by
  simp [mobius]

theorem coeff_correction (n : ℕ) :
    coeff R n (correction : PowerSeries R) =
      if 4≤n then ((n-2).choose 2:R) else 0 := by
  rw [correction, coeff_X_pow_mul', geom_one,
    show (3:ℕ)=2+1 by rfl, mk_one_pow_eq_mk_choose_add]
  split_ifs with hn
  · rw [coeff_mk]
    congr 2
    omega
  · rfl

theorem coeff_candidate (c : R) (n : ℕ) (hn : 0<n) :
    coeff R n (candidate c)=1+c*(if 4≤n then ((n-2).choose 2:R) else 0) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [candidate, map_add, coeff_mobius_succ, one_pow,
    coeff_C_mul, coeff_correction]

theorem coeff_candidate_periodic (c : R) (hc : 2*c=0) (n : ℕ) (hn : 3≤n) :
    coeff R n (candidate c)=
      if n%4=0 ∨ n%4=1 then 1+c else 1 := by
  rw [coeff_candidate c n (by omega)]
  by_cases hn4 : 4≤n
  · rw [if_pos hn4, weighted_choose_two c hc]
    have hm : (n-2)%4=0 ∨ (n-2)%4=1 ↔ ¬(n%4=0 ∨ n%4=1) := by omega
    by_cases hh : n%4=0 ∨ n%4=1
    · simp [hh, hm]
    · simp [hh, hm]
  · have he : n=3 := by omega
    subst n
    norm_num

theorem cast_a (r n : ℕ) (f : ℤ →+* R) :
    f (a r n) = coeff R n (solution (R:=R) r) := by
  rw [← map_solution f r]
  simp [a]

theorem cast_iterateCoeff (r k n : ℕ) (f : ℤ →+* R) :
    f (iterateCoeff r k n)=coeff R n (iter (solution (R:=R) r) k) := by
  rw [← map_solution f r, ← map_iter f (solution_normalized r)]
  simp [iterateCoeff]

theorem solution_two_mod_four :
    solution (R:=ZMod 4) 2=candidate 2 := by
  apply solution_unique 2 (solution_normalized 2) (candidate_normalized 2)
    (solution_equation 2)
  exact (candidate_fixedpoint_even 2 (by decide) (by decide) (by decide)).symm

theorem a396099_residue (n : ℕ) (hn : 3≤n) :
    (a 2 n : ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1 := by
  rw [show (a 2 n:ZMod 4)=(Int.castRingHom (ZMod 4)) (a 2 n) from rfl,
    cast_a, solution_two_mod_four]
  simpa using coeff_candidate_periodic (2:ZMod 4) (by decide) n hn

/-- The OEIS period `[1,3,3,1]`, with its stated starting index three. -/
theorem a396099_period (j : ℕ) :
    (a 2 (4*j+3):ZMod 4)=1 ∧
    (a 2 (4*j+4):ZMod 4)=3 ∧
    (a 2 (4*j+5):ZMod 4)=3 ∧
    (a 2 (4*j+6):ZMod 4)=1 := by
  repeat' constructor
  all_goals rw [a396099_residue _ (by omega)]
  all_goals norm_num [Nat.add_mod, Nat.mul_mod]

theorem solution_two_mod_two :
    solution (R:=ZMod 2) 2=mobius 1 := by
  apply solution_unique 2 (solution_normalized 2) (mobius_normalized 1)
    (solution_equation 2)
  exact (mobius_fixedpoint 2 (by decide) (by decide)).symm

/-- Every positive-index coefficient in A396099 is odd. -/
theorem a396099_odd (n : ℕ) (hn : 0<n) : Odd (a 2 n) := by
  have hcast : (a 2 n:ZMod 2)=1 := by
    rw [show (a 2 n:ZMod 2)=(Int.castRingHom (ZMod 2)) (a 2 n) from rfl,
      cast_a, solution_two_mod_two]
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp
  by_contra hodd
  have heven := Int.not_odd_iff_even.mp hodd
  have hzero : (a 2 n:ZMod 2)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a 2 n) 2).mpr (even_iff_two_dvd.mp heven)
  exact zero_ne_one (hzero.symm.trans hcast)

theorem a396099_second_iterate_series :
    iter (solution (R:=ZMod 4) 2) 2=X+C (ZMod 4) 2*X^2 := by
  rw [solution_two_mod_four]
  have h : iter (candidate (2:ZMod 4)) 2=mobius 2 := by
    simpa only [mul_one, Nat.cast_one] using
      iter_candidate_even (2:ZMod 4) (by decide) (by decide) 1
  rw [h, mobius_of_square_zero (2:ZMod 4) (by decide)]

/-- Coefficients beyond degree two in the second iterate vanish modulo four. -/
theorem a396099_second_iterate (n : ℕ) (hn : 2<n) :
    (iterateCoeff 2 2 n:ZMod 4)=0 := by
  rw [show (iterateCoeff 2 2 n:ZMod 4)=
    (Int.castRingHom (ZMod 4)) (iterateCoeff 2 2 n) from rfl,
    cast_iterateCoeff, a396099_second_iterate_series]
  simp [coeff_X, coeff_X_pow, Nat.ne_of_gt hn, show n≠1 by omega]

theorem a396099_difference_series :
    solution (R:=ZMod 4) 2-X*iter (solution (R:=ZMod 4) 2) 3=
      X+C (ZMod 4) 2*X^3*geom 1 := by
  rw [show (3:ℕ)=2+1 from rfl, iter_succ, a396099_second_iterate_series,
    solution_two_mod_four, candidate_residual (2:ZMod 4) (by decide)]
  have hneg : -(C (ZMod 4) 2)=C (ZMod 4) 2 := by
    rw [← map_neg]
    congr 1
  calc
    X-C (ZMod 4) 2*X^3*geom 1=
        X+(-(C (ZMod 4) 2))*X^3*geom 1 := by ring
    _ = _ := by rw [hneg]

/-- The coefficients of `F-X(F composed three times)` are two mod four above degree two. -/
theorem a396099_difference (n : ℕ) (hn : 2<n) :
    (coeff ℤ n (solution (R:=ℤ) 2-X*iter (solution (R:=ℤ) 2) 3):ZMod 4)=2 := by
  have hmap : PowerSeries.map (Int.castRingHom (ZMod 4))
      (solution (R:=ℤ) 2-X*iter (solution (R:=ℤ) 2) 3)=
      solution (R:=ZMod 4) 2-X*iter (solution (R:=ZMod 4) 2) 3 := by
    simp only [map_sub, map_mul, PowerSeries.map_X, map_solution,
      map_iter _ (solution_normalized 2)]
  have he := congrArg (coeff (ZMod 4) n) hmap
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at he
  rw [he, a396099_difference_series]
  rw [map_add, coeff_X]
  rw [if_neg (by omega)]
  have hr : C (ZMod 4) 2*X^3*geom 1=
      C (ZMod 4) 2*(X^3*geom 1) := by ring
  rw [hr, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), coeff_geom]
  simp

end
end Consecutive
