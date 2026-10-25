module

public import Hanna.Series.Inverse

/-!
Composition and the consecutive-iterate equation.  All objects are actual
Mathlib power series; no coefficient identities are assumed.
-/

@[expose] public section

namespace Consecutive

open PowerSeries Hanna.Series

variable {R : Type*} [CommRing R]

noncomputable def iter (F : PowerSeries R) : ℕ → PowerSeries R
  | 0 => X
  | n + 1 => compose F (iter F n)

@[simp] theorem iter_zero (F : PowerSeries R) : iter F 0 = X := rfl

@[simp] theorem iter_succ (F : PowerSeries R) (n : ℕ) :
    iter F (n+1) = compose F (iter F n) := rfl

@[simp] theorem iter_one (F : PowerSeries R) : iter F 1 = F := by
  simp [iter]

theorem iter_normalized {F : PowerSeries R} (hF : Normalized F) (n : ℕ) :
    Normalized (iter F n) := by
  induction n with
  | zero => exact normalized_X
  | succ n ih => exact hF.compose ih

theorem iter_constantCoeff {F : PowerSeries R} (hF : Normalized F) (n : ℕ) :
    constantCoeff (iter F n) = 0 := (iter_normalized hF n).constantCoeff

theorem iter_add {F : PowerSeries R} (hF : Normalized F) (m n : ℕ) :
    iter F (m+n) = compose (iter F m) (iter F n) := by
  induction m with
  | zero => simpa using (compose_X_left (iter F n) (iter_constantCoeff hF n)).symm
  | succ m ih =>
    rw [Nat.succ_add, iter_succ, ih, iter_succ]
    exact (compose_assoc F (iter F m) (iter F n)
      (iter_constantCoeff hF m) (iter_constantCoeff hF n)).symm

theorem iter_mul {F : PowerSeries R} (hF : Normalized F) (m n : ℕ) :
    iter F (m*n) = iter (iter F m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (m*n) m, iter_add hF, ih, iter_succ]

noncomputable def step (r : ℕ) (F : PowerSeries R) : PowerSeries R :=
  X + iter F r * iter F (r+1)

theorem step_normalized (r : ℕ) {F : PowerSeries R} (hF : Normalized F) :
    Normalized (step r F) := by
  have ha := iter_normalized hF r
  have hb := iter_normalized hF (r+1)
  constructor
  · simp [step, coeff_zero_eq_constantCoeff_apply, ha.constantCoeff, hb.constantCoeff]
  · rw [step, map_add]
    have hd : (X : PowerSeries R)^2 ∣ iter F r * iter F (r+1) := by
      simpa using X_pow_dvd_product
        (show (X : PowerSeries R)^1 ∣ iter F r by simpa using ha.X_dvd)
        (show (X : PowerSeries R)^1 ∣ iter F (r+1) by simpa using hb.X_dvd)
    rw [X_pow_dvd_iff.mp hd 1 (by omega)]
    simp

theorem iter_congr {A B : PowerSeries R} (hA : Normalized A) (hB : Normalized B)
    (n k : ℕ) (hAB : (X : PowerSeries R)^n ∣ A-B) :
    (X : PowerSeries R)^n ∣ iter A k - iter B k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha := iter_normalized hA k
    have hb := iter_normalized hB k
    have ho : (X : PowerSeries R)^n ∣ compose (A-B) (iter A k) := by
      simpa using compose_outer_vanish (A-B) (iter A k) n 1 ha.constantCoeff hAB
        (show (X : PowerSeries R)^1 ∣ iter A k by simpa using ha.X_dvd)
    have hi := compose_inner_congr B (iter A k) (iter B k) n
      ha.constantCoeff hb.constantCoeff ih
    rw [compose_sub _ _ _ ha.constantCoeff] at ho
    simpa only [iter_succ, sub_add_sub_cancel] using dvd_add ho hi

theorem step_contraction (r n : ℕ) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (hAB : (X : PowerSeries R)^n ∣ A-B) :
    (X : PowerSeries R)^(n+1) ∣ step r A-step r B := by
  have h1 := iter_congr hA hB n r hAB
  have h2 := iter_congr hA hB n (r+1) hAB
  have hp1 := X_pow_dvd_product h1
    (show (X : PowerSeries R)^1 ∣ iter A (r+1) by
      simpa using (iter_normalized hA (r+1)).X_dvd)
  have hp2 := X_pow_dvd_product h2
    (show (X : PowerSeries R)^1 ∣ iter B r by
      simpa using (iter_normalized hB r).X_dvd)
  convert dvd_add hp1 hp2 using 1
  simp only [step]
  ring

variable {S : Type*} [CommRing S]

theorem map_iter (f : R →+* S) {F : PowerSeries R} (hF : Normalized F) (n : ℕ) :
    PowerSeries.map f (iter F n) = iter (PowerSeries.map f F) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iter_succ, map_compose f F (iter F n) (iter_constantCoeff hF n), ih, iter_succ]

theorem map_step (f : R →+* S) (r : ℕ) {F : PowerSeries R} (hF : Normalized F) :
    PowerSeries.map f (step r F) = step r (PowerSeries.map f F) := by
  simp only [step, map_add, map_mul, PowerSeries.map_X, map_iter f hF]

end Consecutive
