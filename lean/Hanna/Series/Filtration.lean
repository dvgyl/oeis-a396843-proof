import Hanna.Series.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Hanna.Series

open PowerSeries

variable {R : Type*} [CommRing R]

lemma agree_iff_X_pow_dvd_sub (n : ℕ) (A B : PowerSeries R) :
    Agree n A B ↔ (X : PowerSeries R)^n ∣ A-B := by
  simp only [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

lemma normalized_iff_X_sq_dvd (A : PowerSeries R) :
    Normalized A ↔ (X : PowerSeries R)^2 ∣ A-X := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h n hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · simp [h.constantCoeff]
    · simp [h.2]
  · intro h
    constructor
    · simpa using h 0 (by omega)
    · simpa [sub_eq_zero] using h 1 (by omega)

lemma Normalized.decompose {A : PowerSeries R} (hA : Normalized A) :
    ∃ D, A = X + X^2*D := by
  obtain ⟨D, hD⟩ := (normalized_iff_X_sq_dvd A).mp hA
  exact ⟨D, by linear_combination hD⟩

lemma Normalized.X_dvd {A : PowerSeries R} (hA : Normalized A) : X ∣ A :=
  X_dvd_iff.mpr hA.constantCoeff

lemma X_pow_dvd_product {A B : PowerSeries R} {r s : ℕ}
    (hA : (X : PowerSeries R)^r ∣ A) (hB : (X : PowerSeries R)^s ∣ B) :
    (X : PowerSeries R)^(r+s) ∣ A*B := by
  rw [pow_add]
  exact mul_dvd_mul hA hB

lemma compose_inner_congr (A B D : PowerSeries R) (n : ℕ)
    (hB : constantCoeff R B = 0) (hD : constantCoeff R D = 0)
    (hBD : (X : PowerSeries R)^n ∣ B-D) :
    (X : PowerSeries R)^n ∣ compose A B-compose A D := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  rw [map_sub, coeff_compose A B hB, coeff_compose A D hD,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [← mul_sub, ← map_sub]
  have hpow : (X : PowerSeries R)^n ∣ B^j-D^j :=
    hBD.trans (sub_dvd_pow_sub_pow B D j)
  rw [X_pow_dvd_iff.mp hpow k hk, mul_zero]

lemma compose_outer_vanish (A B : PowerSeries R) (r s : ℕ)
    (hB : constantCoeff R B = 0)
    (hA : (X : PowerSeries R)^r ∣ A) (hBs : (X : PowerSeries R)^s ∣ B) :
    (X : PowerSeries R)^(s*r) ∣ compose A B := by
  obtain ⟨D, rfl⟩ := hA
  rw [compose_mul _ _ _ hB, compose_pow _ _ _ hB, compose_X_left _ hB, pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hBs r) _

lemma compose_normalized_inner_error (A B D : PowerSeries R) (n : ℕ)
    (hA : Normalized A) (hB : constantCoeff R B = 0) (hD : constantCoeff R D = 0)
    (hBD : (X : PowerSeries R)^n ∣ B-D) :
    (X : PowerSeries R)^(n+1) ∣ compose A B-compose A D-(B-D) := by
  obtain ⟨F, rfl⟩ := hA.decompose
  rw [compose_add _ _ _ hB, compose_add _ _ _ hD,
    compose_mul _ _ _ hB, compose_mul _ _ _ hD,
    compose_pow _ _ _ hB, compose_pow _ _ _ hD,
    compose_X_left _ hB, compose_X_left _ hD]
  have hsum : (X : PowerSeries R)^1 ∣ B+D := by
    rw [pow_one]
    exact dvd_add (X_dvd_iff.mpr hB) (X_dvd_iff.mpr hD)
  have hfirst : (X : PowerSeries R)^(n+1) ∣
      (B-D)*(B+D)*compose F B :=
    dvd_mul_of_dvd_left (X_pow_dvd_product hBD hsum) _
  have hdiff := compose_inner_congr F B D n hB hD hBD
  have hDsq : (X : PowerSeries R)^1 ∣ D^2 := by
    rw [pow_one]
    exact (X_dvd_iff.mpr hD).trans (dvd_pow_self D (by omega : 2 ≠ 0))
  have hsecond : (X : PowerSeries R)^(n+1) ∣
      (compose F B-compose F D)*D^2 := X_pow_dvd_product hdiff hDsq
  convert dvd_add hfirst hsecond using 1; ring

lemma T_sub (m : R) (A B : PowerSeries R) :
    T m B-T m A = X*(B-A)*(1-C R m*(A+B)) := by
  unfold T
  ring

lemma T_dvd_X_sq (m : R) (A : PowerSeries R) (hA : Normalized A) :
    (X : PowerSeries R)^2 ∣ T m A := by
  have hx : (X : PowerSeries R)^1 ∣ A := by simpa using hA.X_dvd
  have h1 : (X : PowerSeries R)^2 ∣ X*A := by
    simpa using X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1)) hx
  have h2 : (X : PowerSeries R)^2 ∣ C R m*X*A^2 := by
    convert dvd_mul_of_dvd_left h1 (C R m*A) using 1; ring
  exact dvd_sub h1 h2

lemma psi_perturbation (m : R) (A B : PowerSeries R) (r : ℕ) (hr : 2 ≤ r)
    (hA : Normalized A) (hB : Normalized B)
    (hAB : (X : PowerSeries R)^r ∣ B-A) :
    (X : PowerSeries R)^(r+2) ∣ Psi m B-Psi m A-X*(B-A) := by
  have hTdiff : (X : PowerSeries R)^(r+1) ∣ T m B-T m A := by
    rw [T_sub]
    have hx : (X : PowerSeries R)^1 ∣ X := by simp
    have hprod := X_pow_dvd_product hx hAB
    rw [Nat.add_comm 1 r] at hprod
    exact dvd_mul_of_dvd_left hprod _
  have hinner := compose_normalized_inner_error A (T m B) (T m A) (r+1)
    hA (constantCoeff_T m B) (constantCoeff_T m A) hTdiff
  have houter : (X : PowerSeries R)^(r+2) ∣ compose (B-A) (T m B) := by
    have h := compose_outer_vanish (B-A) (T m B) r 2
      (constantCoeff_T m B) hAB (T_dvd_X_sq m B hB)
    exact (pow_dvd_pow X (by omega : r+2 ≤ 2*r)).trans h
  have hlinear : (X : PowerSeries R)^(r+2) ∣ T m B-T m A-X*(B-A) := by
    have hsum : (X : PowerSeries R)^1 ∣ A+B := by
      simpa using dvd_add hA.X_dvd hB.X_dvd
    have hx : (X : PowerSeries R)^1 ∣ X := by simp
    have hprod : (X : PowerSeries R)^(r+2) ∣ X*(B-A)*(A+B) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        X_pow_dvd_product (X_pow_dvd_product hx hAB) hsum
    have hmul := dvd_mul_of_dvd_left hprod (-C R m)
    convert hmul using 1; unfold T; ring
  have hsum := dvd_add (dvd_add houter hinner) hlinear
  rw [compose_sub _ _ _ (constantCoeff_T m B)] at hsum
  convert hsum using 1; unfold Psi; ring

end Hanna.Series
