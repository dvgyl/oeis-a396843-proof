import Consecutive.Coefficients
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Integer composition iterates

Negative iterates are repeated composition of the unique actual formal-series
inverse.  They are not defined by a modular coefficient formula.  Coefficient
reduction commutes with these inverses and iterates.
-/

namespace Consecutive

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

/-- Integer composition powers, using genuine compositional inversion for
negative exponents. -/
def ziter (F : PowerSeries R) (hF : Normalized F) : ℤ → PowerSeries R
  | .ofNat n => iter F n
  | .negSucc n => iter (inverse F hF) (n+1)

@[simp] theorem ziter_nat (F : PowerSeries R) (hF : Normalized F) (n : ℕ) :
    ziter F hF (n : ℤ) = iter F n := rfl

@[simp] theorem ziter_neg_nat (F : PowerSeries R) (hF : Normalized F) (n : ℕ) :
    ziter F hF (-(n : ℤ)) = iter (inverse F hF) n := by
  cases n <;> rfl

theorem ziter_normalized (F : PowerSeries R) (hF : Normalized F) (k : ℤ) :
    Normalized (ziter F hF k) := by
  cases k with
  | ofNat n => exact iter_normalized hF n
  | negSucc n => exact iter_normalized (inverse_normalized F hF) (n+1)

theorem ziter_congr {A B : PowerSeries R} (hA : Normalized A) (hB : Normalized B)
    (h : A=B) (k : ℤ) : ziter A hA k = ziter B hB k := by
  subst B
  rfl

/-- Repeated inverse composition really inverts repeated forward composition. -/
theorem iter_inverse_right (F : PowerSeries R) (hF : Normalized F) (n : ℕ) :
    compose (iter F n) (iter (inverse F hF) n) = X := by
  have hi := inverse_normalized F hF
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iter_add hF n 1, iter_one, iter_succ,
      compose_assoc _ F (compose (inverse F hF) (iter (inverse F hF) n))
        hF.constantCoeff (hi.compose (iter_normalized hi n)).constantCoeff,
      ← compose_assoc F (inverse F hF) (iter (inverse F hF) n)
        hi.constantCoeff (iter_constantCoeff hi n),
      compose_inverse_right F hF,
      compose_X_left _ (iter_constantCoeff hi n), ih]

theorem iter_inverse_left (F : PowerSeries R) (hF : Normalized F) (n : ℕ) :
    compose (iter (inverse F hF) n) (iter F n) = X :=
  left_inverse_of_right_inverse (iter_normalized (inverse_normalized F hF) n)
    (iter_inverse_right F hF n)

theorem ziter_negative_is_inverse (F : PowerSeries R) (hF : Normalized F) (n : ℕ) :
    compose (ziter F hF (n : ℤ)) (ziter F hF (-(n : ℤ))) = X ∧
    compose (ziter F hF (-(n : ℤ))) (ziter F hF (n : ℤ)) = X := by
  simp only [ziter_nat, ziter_neg_nat]
  exact ⟨iter_inverse_right F hF n, iter_inverse_left F hF n⟩

variable {S : Type*} [CommRing S]

theorem map_ziter (f : R →+* S) (F : PowerSeries R) (hF : Normalized F) (k : ℤ) :
    PowerSeries.map f (ziter F hF k) =
      ziter (PowerSeries.map f F) (hF.map f) k := by
  cases k with
  | ofNat n => exact map_iter f hF n
  | negSucc n =>
    simp only [ziter, map_iter f (inverse_normalized F hF), map_inverse]

theorem inverse_mobius (a : R) (ha : Normalized (mobius a)) :
    inverse (mobius a) ha = mobius (-a) := by
  apply Hanna.Series.inverse_unique ha (mobius_normalized (-a))
    (compose_inverse_left (mobius a) ha)
  rw [mobius_compose, add_neg_cancel, mobius_zero]

theorem ziter_mobius (a : R) (ha : Normalized (mobius a)) (k : ℤ) :
    ziter (mobius a) ha k = mobius ((k : R)*a) := by
  cases k with
  | ofNat n =>
    simpa only [ziter, Int.ofNat_eq_natCast, Int.cast_natCast] using iter_mobius a n
  | negSucc n =>
    rw [ziter, inverse_mobius, iter_mobius]
    push_cast
    ring_nf

/-- Every integer iterate for odd `r`, modulo `2*r`. -/
theorem ziter_solution_mod_odd (r : ℕ) (hr : Odd r) (k : ℤ) :
    ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k =
      mobius (k : ZMod (2*r)) := by
  calc
    _ = ziter (mobius (1 : ZMod (2*r))) (mobius_normalized 1) k :=
      ziter_congr (solution_normalized r) (mobius_normalized 1)
        (solution_mod_odd r hr) k
    _ = mobius ((k : ZMod (2*r))*1) := ziter_mobius 1 (mobius_normalized 1) k
    _ = _ := by rw [mul_one]

theorem map_ziter_solution_mod_odd (r : ℕ) (hr : Odd r) (k : ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod (2*r)))
      (ziter (solution (R:=ℤ) r) (solution_normalized r) k) =
        mobius (k : ZMod (2*r)) := by
  rw [map_ziter]
  calc
    _ = ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k :=
      ziter_congr _ _ (map_solution (Int.castRingHom (ZMod (2*r))) r) k
    _ = _ := ziter_solution_mod_odd r hr k

def integerIterateCoeff (r : ℕ) (k : ℤ) (n : ℕ) : ℤ :=
  coeff ℤ n (ziter (solution (R:=ℤ) r) (solution_normalized r) k)

theorem coeff_mobius_of_pos (a : R) (n : ℕ) (hn : 1 ≤ n) :
    coeff R n (mobius a) = a^(n-1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [mobius]

theorem integerIterateCoeff_mod_odd (r : ℕ) (hr : Odd r) (k : ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    (integerIterateCoeff r k n : ZMod (2*r)) = (k : ZMod (2*r))^(n-1) := by
  have h := congrArg (coeff (ZMod (2*r)) n) (map_ziter_solution_mod_odd r hr k)
  simpa only [integerIterateCoeff, coeff_map, Int.coe_castRingHom,
    coeff_mobius_of_pos _ n hn] using h

/-- A396807's iterate conjecture for every integer exponent, including negative
exponents, and every positive coefficient index. -/
theorem a396807_integer_iterate_congruence (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    (integerIterateCoeff 5 k n : ZMod 10) = (k : ZMod 10)^(n-1) := by
  exact integerIterateCoeff_mod_odd 5 (by decide) k n hn

theorem mobius_eq_X_iff (a : R) : mobius a = X ↔ a=0 := by
  constructor
  · intro h
    have hc := congrArg (coeff R 2) h
    simpa [mobius, coeff_X] using hc
  · intro h
    rw [h, mobius_zero]

/-- The exact signed composition order for odd parameters. -/
theorem ziter_solution_mod_odd_eq_X_iff (r : ℕ) (hr : Odd r) (k : ℤ) :
    ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k = X ↔
      (2*r : ℤ) ∣ k := by
  rw [ziter_solution_mod_odd r hr, mobius_eq_X_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_cast

/-- A finite compositional period identifies the inverse as its preceding
natural iterate. -/
theorem inverse_eq_iter_pred_of_period (F : PowerSeries R) (hF : Normalized F)
    (N : ℕ) (hN : 1 ≤ N) (hperiod : iter F N=X) :
    inverse F hF = iter F (N-1) := by
  apply Hanna.Series.inverse_unique hF (iter_normalized hF (N-1))
    (compose_inverse_left F hF)
  rw [← iter_succ, Nat.sub_add_cancel hN, hperiod]

theorem inverse_solution_mod (r : ℕ) (hr : 0<r) :
    inverse (solution (R:=ZMod (2*r)) r) (solution_normalized r) =
      iter (solution (R:=ZMod (2*r)) r) (2*r-1) :=
  inverse_eq_iter_pred_of_period _ (solution_normalized r) (2*r) (by omega)
    (iter_solution_mod_period r)

theorem ziter_solution_mod_neg_nat (r : ℕ) (hr : 0<r) (m : ℕ) :
    ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) (-(m : ℤ)) =
      iter (solution (R:=ZMod (2*r)) r) ((2*r-1)*m) := by
  rw [ziter_neg_nat, inverse_solution_mod r hr,
    ← iter_mul (solution_normalized r)]

/-- The complete rational-series formula for every signed iterate and every
positive parameter.  This includes both the even and odd families. -/
theorem ziter_solution_mod (r : ℕ) (hr : 0<r) (k : ℤ) :
    ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k =
      mobius (k : ZMod (2*r)) +
        if Even r ∧ Odd k then C (ZMod (2*r)) (r : ZMod (2*r))*correction else 0 := by
  cases k with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, ziter_nat, Int.cast_natCast, Int.odd_coe_nat]
      using iter_solution_mod r n
  | negSucc n =>
    have hp : Odd (2*r-1) := Nat.odd_iff.mpr (by omega)
    have hcast : ((2*r-1 : ℕ) : ZMod (2*r)) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2*r), ZMod.natCast_self]
      simp
    have hz := ziter_solution_mod_neg_nat r hr (n+1)
    have hf := iter_solution_mod r ((2*r-1)*(n+1))
    rw [hf] at hz
    have hparity : Odd (Int.negSucc n) ↔ Odd (n+1) := by
      rw [Int.negSucc_eq, odd_neg]
      simpa only [Nat.cast_add, Nat.cast_one] using Int.odd_coe_nat (n+1)
    simp only [hparity]
    simpa [Int.negSucc_eq, Nat.cast_mul, hcast, Nat.odd_mul, hp] using hz

theorem map_ziter_solution_mod (r : ℕ) (hr : 0<r) (k : ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod (2*r)))
      (ziter (solution (R:=ℤ) r) (solution_normalized r) k) =
        mobius (k : ZMod (2*r)) +
          if Even r ∧ Odd k then C (ZMod (2*r)) (r : ZMod (2*r))*correction else 0 := by
  rw [map_ziter]
  calc
    _ = ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k :=
      ziter_congr _ _ (map_solution (Int.castRingHom (ZMod (2*r))) r) k
    _ = _ := ziter_solution_mod r hr k

/-- Coefficient form of the complete signed-iterate congruence.  The explicit
`4 ≤ n` guard includes all the low-index boundary cases. -/
theorem integerIterateCoeff_mod (r : ℕ) (hr : 0<r) (k : ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    (integerIterateCoeff r k n : ZMod (2*r)) =
      (k : ZMod (2*r))^(n-1) +
        if Even r ∧ Odd k then
          (r : ZMod (2*r)) * (if 4≤n then ((n-2).choose 2 : ZMod (2*r)) else 0)
        else 0 := by
  have h := congrArg (coeff (ZMod (2*r)) n) (map_ziter_solution_mod r hr k)
  by_cases hh : Even r ∧ Odd k
  · simpa only [integerIterateCoeff, coeff_map, Int.coe_castRingHom,
      if_pos hh, map_add, coeff_mobius_of_pos _ n hn, coeff_C_mul, coeff_correction] using h
  · simpa only [integerIterateCoeff, coeff_map, Int.coe_castRingHom,
      if_neg hh, add_zero, coeff_mobius_of_pos _ n hn] using h

/-- Exact signed composition order: a positive parameter `r` has order `2*r`
after coefficient reduction modulo `2*r`. -/
theorem ziter_solution_mod_eq_X_iff (r : ℕ) (hr : 0<r) (k : ℤ) :
    ziter (solution (R:=ZMod (2*r)) r) (solution_normalized r) k = X ↔
      (2*r : ℤ) ∣ k := by
  constructor
  · intro h
    rw [ziter_solution_mod r hr k] at h
    have hc := congrArg (coeff (ZMod (2*r)) 2) h
    have hk : (k : ZMod (2*r))=0 := by
      by_cases hh : Even r ∧ Odd k
      · simp only [if_pos hh, map_add, coeff_mobius_of_pos _ 2 (by omega),
          coeff_C_mul, coeff_correction] at hc
        simpa [coeff_X] using hc
      · simpa [hh, coeff_mobius_of_pos _ 2 (by omega), coeff_X] using hc
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd k (2*r)).mp hk
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
  · intro hk
    have hcast : (k : ZMod (2*r))=0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd k (2*r)).mpr
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk
    have heven : Even k := even_iff_two_dvd.mpr
      ((dvd_mul_right (2 : ℤ) (r : ℤ)).trans hk)
    have hodd : ¬Odd k := Int.not_odd_iff_even.mpr heven
    rw [ziter_solution_mod r hr k, hcast]
    simp [hodd, mobius_zero]

end
end Consecutive
