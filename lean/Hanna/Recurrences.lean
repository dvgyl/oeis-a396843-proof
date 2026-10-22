import Hanna.Canonical
import Mathlib.Tactic.Ring

namespace Hanna
open PowerSeries
variable {R : Type*} [CommRing R]

noncomputable def shift (U : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun r => coeff R (r+1) U)

@[simp] lemma coeff_shift (U : PowerSeries R) (r : ℕ) :
    coeff R r (shift U) = coeff R (r+1) U := coeff_mk _ _

lemma eq_X_mul_shift (U : PowerSeries R) (hU : constantCoeff R U = 0) :
    U = X * shift U := by
  simpa only [hU, map_zero, add_zero, shift] using eq_X_mul_shift_add_const U

lemma coeff_compose_X_sq_even (U : PowerSeries R) (k : ℕ) :
    coeff R (2*k) (Series.compose U (X^2)) = coeff R k U := by
  rw [Series.coeff_compose U (X^2) (by simp)]
  rw [Finset.sum_eq_single k]
  · simp [← pow_mul]
  · intro j hj hjk
    have hne : 2*k ≠ 2*j := by omega
    simp [← pow_mul, coeff_X_pow, hne]
  · intro hk
    exfalso
    exact hk (Finset.mem_range.mpr (by omega))

lemma coeff_compose_X_sq_odd (U : PowerSeries R) (r : ℕ) (hr : ¬Even r) :
    coeff R r (Series.compose U (X^2)) = 0 := by
  rw [Series.coeff_compose U (X^2) (by simp)]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : r ≠ 2*j := by
    intro h
    apply hr
    exact ⟨j, by omega⟩
  simp [← pow_mul, coeff_X_pow, hne]

lemma coeff_compose_X_sq (U : PowerSeries R) (r : ℕ) :
    coeff R r (Series.compose U (X^2)) = if Even r then coeff R (r/2) U else 0 := by
  split_ifs with hr
  · obtain ⟨k, hk⟩ := hr
    have h : r = 2*k := by omega
    rw [h]
    simpa using coeff_compose_X_sq_even U k
  · exact coeff_compose_X_sq_odd U r hr

lemma coeff_compose_shift (U V : PowerSeries R) (hU : constantCoeff R U = 0)
    (hV : constantCoeff R V = 0) (r : ℕ) :
    coeff R (r+1) (Series.compose U V) =
      ∑ j ∈ Finset.range (r+1), coeff R j (shift U) *
        coeff R (r-j) ((shift V)^(j+1)) := by
  rw [Series.coeff_compose U V hV, Finset.sum_range_succ']
  simp only [coeff_zero_eq_constantCoeff_apply, hU, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hvpow : V^(j+1) = X^(j+1) * (shift V)^(j+1) := by
    conv_lhs => rw [eq_X_mul_shift V hV, mul_pow]
  rw [coeff_shift, hvpow, coeff_X_pow_mul', if_pos (by omega)]
  simp

noncomputable def F (m : R) : PowerSeries R := shift (A m)
noncomputable def G (m : R) : PowerSeries R := shift (B m)
noncomputable def f (m : R) (r : ℕ) : R := coeff R r (F m)
noncomputable def g (m : R) (r : ℕ) : R := coeff R r (G m)

lemma A_eq_X_mul_F (m : R) : A m = X * F m :=
  eq_X_mul_shift (A m) (A_normalized m).constantCoeff

lemma B_eq_X_mul_G (m : R) : B m = X * G m :=
  eq_X_mul_shift (B m) (B_normalized m).constantCoeff

@[simp] lemma f_zero (m : R) : f m 0 = 1 := by
  simpa only [f, F, coeff_shift, zero_add] using (A_normalized m).2

@[simp] lemma g_zero (m : R) : g m 0 = 1 := by
  simpa only [g, G, coeff_shift, zero_add] using (B_normalized m).2

@[simp] lemma constantCoeff_F (m : R) : constantCoeff R (F m) = 1 := by
  simpa only [f, coeff_zero_eq_constantCoeff_apply] using f_zero m

@[simp] lemma constantCoeff_G (m : R) : constantCoeff R (G m) = 1 := by
  simpa only [g, coeff_zero_eq_constantCoeff_apply] using g_zero m

lemma f_eq_coeff_A (m : R) (r : ℕ) : f m r = coeff R (r+1) (A m) := coeff_shift (A m) r
lemma g_eq_coeff_B (m : R) (r : ℕ) : g m r = coeff R (r+1) (B m) := coeff_shift (B m) r

lemma T_A_eq_compose_B (m : R) :
    Series.T m (A m) = Series.compose (B m) (X^2) := by
  calc
    Series.T m (A m) = Series.compose X (Series.T m (A m)) :=
      (Series.compose_X_left _ (Series.constantCoeff_T _ _)).symm
    _ = Series.compose (Series.compose (B m) (A m)) (Series.T m (A m)) := by
      rw [B_comp_A]
    _ = Series.compose (B m) (Series.compose (A m) (Series.T m (A m))) :=
      Series.compose_assoc _ _ _ (A_normalized m).constantCoeff (Series.constantCoeff_T _ _)
    _ = Series.compose (B m) (X^2) := congrArg (Series.compose (B m)) (A_equation m)

lemma F_equation (m : R) :
    F m = Series.compose (G m) (X^2) + C R m * X * (F m)^2 := by
  have h := T_A_eq_compose_B m
  rw [Series.T, A_eq_X_mul_F, B_eq_X_mul_G,
    Series.compose_mul _ _ _ (by simp), Series.compose_X_left _ (by simp)] at h
  have h' : X * (X * (F m - C R m * X * (F m)^2)) =
      X * (X * Series.compose (G m) (X^2)) := by
    calc
      _ = X * (X * F m) - C R m * X * (X * F m)^2 := by ring
      _ = X^2 * Series.compose (G m) (X^2) := h
      _ = _ := by ring
  have h'' := PowerSeries.X_mul_cancel (PowerSeries.X_mul_cancel h')
  exact sub_eq_iff_eq_add.mp h''

lemma f_recurrence (m : R) (r : ℕ) (hr : 1 ≤ r) :
    f m r = (if Even r then g m (r/2) else 0) +
      m * ∑ ij ∈ Finset.antidiagonal (r-1), f m ij.1 * f m ij.2 := by
  have h := congrArg (coeff R r) (F_equation m)
  rw [map_add, coeff_compose_X_sq] at h
  change f m r = (if Even r then g m (r/2) else 0) + _ at h
  rw [mul_assoc, coeff_C_mul] at h
  have heq : r = (r-1)+1 := by omega
  have hs : coeff R r (X * (F m)^2) =
      ∑ ij ∈ Finset.antidiagonal (r-1), f m ij.1 * f m ij.2 := by
    conv_lhs => rw [heq, coeff_succ_X_mul, pow_two, coeff_mul]
    rfl
  simpa only [hs] using h

lemma inverse_coefficient_sum (m : R) (r : ℕ) (hr : 1 ≤ r) :
    (∑ j ∈ Finset.range (r+1), f m j * coeff R (r-j) ((G m)^(j+1))) = 0 := by
  have h := coeff_compose_shift (A m) (B m)
    (A_normalized m).constantCoeff (B_normalized m).constantCoeff r
  rw [A_comp_B, coeff_X, if_neg (by omega)] at h
  exact h.symm

lemma g_recurrence (m : R) (r : ℕ) (hr : 1 ≤ r) :
    g m r = -f m r -
      ∑ j ∈ Finset.Ico 1 r, f m j * coeff R (r-j) ((G m)^(j+1)) := by
  have h := inverse_coefficient_sum m r hr
  rw [Finset.sum_range_succ] at h
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => f m j * coeff R (r-j) ((G m)^(j+1))) hr
  rw [← hsplit] at h
  simp only [Finset.sum_range_one, f_zero, Nat.sub_zero, zero_add, pow_one, one_mul,
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_G,
    one_pow, mul_one] at h
  change g m r + _ + f m r = 0 at h
  linear_combination h

end Hanna
