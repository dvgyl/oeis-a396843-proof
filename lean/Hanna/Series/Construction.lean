import Hanna.Series.Filtration
import Hanna.Series.Triangular

namespace Hanna.Series

open PowerSeries

variable {R : Type*} [CommRing R]

noncomputable def ofTail (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else if n = 1 then 1 else a (n-2)

@[simp] lemma coeff_ofTail (a : ℕ → R) (n : ℕ) :
    coeff R (n+2) (ofTail a) = a n := by
  simp [ofTail]

lemma normalized_ofTail (a : ℕ → R) : Normalized (ofTail a) := by
  simp [Normalized, ofTail]

lemma ofTail_coeff {A : PowerSeries R} (hA : Normalized A) :
    ofTail (fun n => coeff R (n+2) A) = A := by
  ext n
  rcases n with _ | (_ | n)
  · simpa [ofTail] using hA.1.symm
  · simpa [ofTail] using hA.2.symm
  · simp [Nat.succ_eq_add_one, Nat.add_assoc]

lemma ofTail_agree (a b : ℕ → R) (n : ℕ) (h : ∀ k < n, a k = b k) :
    Agree (n+2) (ofTail a) (ofTail b) := by
  intro k hk
  rcases k with _ | (_ | k)
  · simp [ofTail]
  · simp [ofTail]
  · simp only [Nat.succ_eq_add_one, Nat.add_assoc, coeff_ofTail]
    exact h k (by omega)

lemma psi_triangular (m : R) :
    Triangular (fun a n => coeff R (n+3) (Psi m (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := psi_perturbation m (ofTail b) (ofTail a) (n+2) (by omega)
    (normalized_ofTail b) (normalized_ofTail a) hd
  have hc := X_pow_dvd_iff.mp hp (n+2+1) (by omega)
  simp only [map_sub, coeff_succ_X_mul, coeff_ofTail] at hc
  have heq : n+2+1 = n+3 := by omega
  rw [heq] at hc
  exact sub_eq_zero.mp hc

lemma psi_normalized_low (m : R) (A : PowerSeries R) (hA : Normalized A) :
    (X : PowerSeries R)^3 ∣ Psi m A-X^2 := by
  obtain ⟨D, hD⟩ := hA.decompose
  have hT := T_dvd_X_sq m A hA
  have hA2 : (X : PowerSeries R)^2 ∣ A^2 := by
    simpa using pow_dvd_pow_of_dvd hA.X_dvd 2
  have hlin : (X : PowerSeries R)^3 ∣ T m A-X^2 := by
    have h1 : (X : PowerSeries R)^3 ∣ X*(A-X) := by
      simpa using X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1))
        ((normalized_iff_X_sq_dvd A).mp hA)
    have h2 : (X : PowerSeries R)^3 ∣ C R m*X*A^2 := by
      have hh := X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1)) hA2
      convert dvd_mul_of_dvd_left hh (C R m) using 1; ring
    convert dvd_sub h1 h2 using 1; unfold T; ring
  have hnonlin : (X : PowerSeries R)^3 ∣ Psi m A-T m A := by
    have h4 : (X : PowerSeries R)^4 ∣ (T m A)^2 := by
      simpa only [← pow_mul, Nat.reduceMul] using pow_dvd_pow_of_dvd hT 2
    have h3 := (pow_dvd_pow (X : PowerSeries R) (by omega : 3 ≤ 4)).trans h4
    have hh := dvd_mul_of_dvd_left h3 (compose D (T m A))
    unfold Psi
    nth_rw 1 [hD]
    rw [compose_add _ _ _ (constantCoeff_T m A),
      compose_mul _ _ _ (constantCoeff_T m A),
      compose_pow _ _ _ (constantCoeff_T m A), compose_X_left _ (constantCoeff_T m A)]
    convert hh using 1; ring
  convert dvd_add hnonlin hlin using 1; ring

lemma solution_exists (m : R) :
    ∃ A : PowerSeries R, Normalized A ∧ Psi m A = X^2 := by
  let a := triangularCoeffs (fun a n => coeff R (n+3) (Psi m (ofTail a))) (fun _ => 0)
  have ha := triangularCoeffs_spec _ (psi_triangular m) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  ext n
  by_cases hn : n < 3
  · have hc := X_pow_dvd_iff.mp (psi_normalized_low m (ofTail a) (normalized_ofTail a)) n hn
    simpa only [map_sub, sub_eq_zero] using hc
  · have heq : n-3+3 = n := by omega
    have hc := congrFun ha (n-3)
    change coeff R (n-3+3) (Psi m (ofTail a)) = 0 at hc
    rw [heq] at hc
    rw [hc, coeff_X_pow, if_neg (by omega : n ≠ 2)]

lemma solution_unique (m : R) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (hPA : Psi m A = X^2) (hPB : Psi m B = X^2) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · have : n=0 ∨ n=1 := by omega
      rcases this with rfl | rfl
      · exact hA.1.trans hB.1.symm
      · exact hA.2.trans hB.2.symm
    · have hd : (X : PowerSeries R)^n ∣ A-B :=
        (agree_iff_X_pow_dvd_sub n A B).mp ih
      have hp := psi_perturbation m B A n (by omega) hB hA hd
      have hc := X_pow_dvd_iff.mp hp (n+1) (by omega)
      rw [hPA, hPB, sub_self] at hc
      simp only [zero_sub, map_neg, coeff_succ_X_mul, map_sub, neg_eq_zero, sub_eq_zero] at hc
      exact hc

theorem existence_uniqueness (m : R) :
    ∃! A : PowerSeries R, Normalized A ∧ Psi m A = X^2 := by
  obtain ⟨A, hA, hPA⟩ := solution_exists m
  exact ⟨A, ⟨hA, hPA⟩, fun B hB => solution_unique m hB.1 hA hB.2 hPA⟩

noncomputable def solution (m : R) : PowerSeries R :=
  (existence_uniqueness m).exists.choose

lemma solution_normalized (m : R) : Normalized (solution m) :=
  (existence_uniqueness m).exists.choose_spec.1

lemma solution_equation (m : R) : Psi m (solution m) = X^2 :=
  (existence_uniqueness m).exists.choose_spec.2

variable {S : Type*} [CommRing S]

lemma map_solution (f : R →+* S) (m : R) :
    PowerSeries.map f (solution m) = solution (f m) := by
  apply solution_unique (f m) ((solution_normalized m).map f) (solution_normalized (f m))
  · rw [← map_Psi, solution_equation, map_pow, PowerSeries.map_X]
  · exact solution_equation (f m)

end Hanna.Series
