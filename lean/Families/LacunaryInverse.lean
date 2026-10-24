import Families.ModFour
import Families.CubicFrobenius
import Hanna.Related.ScaledParity

/-!
# OEIS A389537: reversion of an alternating binary lacunary series

The canonical inverse series is constructed from `R + R(X²) = X`.
The original equation `A(A-X)=A²`, its uniqueness, and the full modulus-four
coefficient pattern are proved for actual formal power series.

AI-generated for Dev D. Goyal.
-/

namespace Families.LacunaryInverse

open PowerSeries Hanna.Series Families.CubicReversion

noncomputable section

variable {S T : Type*} [CommRing S] [CommRing T]

def step (U : PowerSeries S) : PowerSeries S := X-compose U (X^2)

theorem step_normalized {U : PowerSeries S} (hU : Normalized U) :
    Normalized (step U) := by
  constructor
  · simp [step, coeff_compose_X_power _ 2 0 (by omega), hU.constantCoeff]
  · simp [step, coeff_compose_X_power _ 2 1 (by omega)]

theorem step_contraction (n : ℕ) (hn : 1≤n) (U V : PowerSeries S)
    (hd : (X : PowerSeries S)^n ∣ U-V) : X^(n+1) ∣ step U-step V := by
  have h := compose_outer_vanish (U-V) (X^2) n 2 (by simp) hd (dvd_refl _)
  have hp : (X : PowerSeries S)^(n+1) ∣ compose (U-V) (X^2) :=
    (pow_dvd_pow X (by omega : n+1≤2*n)).trans h
  rw [compose_sub _ _ _ (by simp)] at hp
  convert dvd_neg.mpr hp using 1; simp only [step]; ring

theorem recursion_triangular :
    Triangular (fun a n => coeff S (n+2) (ofTail a-step (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := step_contraction (n+2) (by omega) (ofTail a) (ofTail b) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simp only [map_sub, coeff_ofTail] at hc ⊢
  linear_combination -hc

theorem auxiliary_exists : ∃ U : PowerSeries S, Normalized U ∧ U=step U := by
  let op := fun a n => coeff S (n+2) (ofTail a-step (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op recursion_triangular (fun _ => 0)
  refine ⟨ofTail a,normalized_ofTail a,?_⟩
  have hs := step_normalized (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · exact (normalized_ofTail a).1.trans hs.1.symm
  · exact (normalized_ofTail a).2.trans hs.2.symm
  · have hc := congrFun ha n
    change coeff S (n+2) (ofTail a-step (ofTail a))=0 at hc
    simpa only [map_sub, sub_eq_zero, Nat.succ_eq_add_one, Nat.add_assoc] using hc

theorem auxiliary_unique {U V : PowerSeries S} (hU : Normalized U)
    (hV : Normalized V) (heU : U=step U) (heV : V=step V) : U=V := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; exact hU.1.trans hV.1.symm
    · have hd := (agree_iff_X_pow_dvd_sub n U V).mp ih
      have hp := step_contraction n (by omega) U V hd
      have hc := X_pow_dvd_iff.mp hp n (by omega)
      rw [← heU, ← heV, map_sub, sub_eq_zero] at hc
      exact hc

theorem auxiliary_existence_uniqueness :
    ∃! U : PowerSeries S, Normalized U ∧ U=step U := by
  obtain ⟨U,hU,heU⟩ := auxiliary_exists (S:=S)
  exact ⟨U,⟨hU,heU⟩,fun V hV => auxiliary_unique hV.1 hU hV.2 heU⟩

def R : PowerSeries S := auxiliary_existence_uniqueness.exists.choose

theorem R_normalized : Normalized (R : PowerSeries S) :=
  auxiliary_existence_uniqueness.exists.choose_spec.1

theorem R_fixed : (R : PowerSeries S)=step R :=
  auxiliary_existence_uniqueness.exists.choose_spec.2

theorem R_equation : (R : PowerSeries S)+compose R (X^2)=X := by
  have h := R_fixed (S:=S)
  unfold step at h
  linear_combination h

def A : PowerSeries S := inverse R R_normalized

theorem A_normalized : Normalized (A : PowerSeries S) := inverse_normalized R R_normalized

theorem R_A : compose (R : PowerSeries S) A=X := compose_inverse_right R R_normalized

theorem A_R : compose (A : PowerSeries S) R=X := compose_inverse_left R R_normalized

theorem map_R (f : S →+* T) : PowerSeries.map f (R : PowerSeries S)=(R : PowerSeries T) := by
  apply auxiliary_unique (R_normalized.map f) R_normalized _ R_fixed
  have h := congrArg (PowerSeries.map f) (R_fixed (S:=S))
  change PowerSeries.map f R=PowerSeries.map f (X-compose R (X^2)) at h
  rw [map_sub, map_compose f R (X^2) (by simp), map_pow, PowerSeries.map_X] at h
  exact h

theorem map_A (f : S →+* T) : PowerSeries.map f (A : PowerSeries S)=(A : PowerSeries T) := by
  apply inverse_unique R_normalized A_normalized
  · rw [← map_R f, ← map_compose f A R R_normalized.constantCoeff, A_R, PowerSeries.map_X]
  · exact R_A

theorem A_equation : compose (A : PowerSeries S) (A-X)=A^2 := by
  have hA := A_normalized (S:=S)
  have hsq : constantCoeff S (A^2 : PowerSeries S)=0 := by simp [hA.constantCoeff]
  have hsub : constantCoeff S (A-X : PowerSeries S)=0 := by simp [hA.constantCoeff]
  have he := congrArg (fun U : PowerSeries S => compose U A) (R_equation (S:=S))
  dsimp only at he
  rw [compose_add _ _ _ hA.constantCoeff, compose_assoc _ _ _ (by simp) hA.constantCoeff,
    compose_pow _ _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff, R_A] at he
  have hRA : compose (R : PowerSeries S) (A^2)=A-X := by linear_combination he
  calc
    compose (A : PowerSeries S) (A-X)=compose A (compose R (A^2)) := by rw [hRA]
    _=compose (compose A R) (A^2) :=
      (compose_assoc A R _ R_normalized.constantCoeff hsq).symm
    _=A^2 := by rw [A_R, compose_X_left _ hsq]

theorem inverse_source (U : PowerSeries S) (hU : Normalized U)
    (he : compose U (U-X)=U^2) :
    inverse U hU=step (inverse U hU) := by
  let V := inverse U hU
  have hV : Normalized V := inverse_normalized U hU
  have hsub : constantCoeff S (U-X)=0 := by simp [hU.constantCoeff]
  have hUV : compose U V=X := compose_inverse_right U hU
  have hVU : compose V U=X := compose_inverse_left U hU
  have h := congrArg (fun E => compose V E) he
  dsimp only at h
  rw [← compose_assoc _ _ _ hU.constantCoeff hsub, hVU, compose_X_left _ hsub] at h
  have h' := congrArg (fun E => compose E V) h
  dsimp only at h'
  rw [compose_sub _ _ _ hV.constantCoeff, hUV, compose_X_left _ hV.constantCoeff,
    compose_assoc _ _ _ (by simp [hU.constantCoeff]) hV.constantCoeff,
    compose_pow _ _ _ hV.constantCoeff, hUV] at h'
  change V=X-compose V (X^2)
  linear_combination -h'

theorem A_unique (U : PowerSeries S) (hU : Normalized U)
    (he : compose U (U-X)=U^2) : U=A := by
  have hi : inverse U hU=(R : PowerSeries S) :=
    auxiliary_unique (inverse_normalized U hU) R_normalized (inverse_source U hU he) R_fixed
  apply inverse_unique (inverse_normalized U hU) A_normalized (compose_inverse_right U hU)
  rw [hi]
  exact R_A

theorem source_existence_uniqueness :
    ∃! U : PowerSeries S, Normalized U ∧ compose U (U-X)=U^2 :=
  ⟨A,⟨A_normalized,A_equation⟩,fun U hU => A_unique U hU.1 hU.2⟩

theorem A_mod_two : (A : PowerSeries (ZMod 2))=X+X^2 := by
  have hR := R_normalized (S:=ZMod 2)
  have h := R_equation (S:=ZMod 2)
  rw [← square_substitution] at h
  have hcomp : compose ((X : PowerSeries (ZMod 2))+X^2) R=X := by
    simpa only [compose_add _ _ _ hR.constantCoeff, compose_pow _ _ _ hR.constantCoeff,
      compose_X_left _ hR.constantCoeff] using h
  exact (inverse_unique hR A_normalized hcomp R_A).symm

def a (n : ℕ) : ℤ := coeff ℤ n A

def H : PowerSeries ℤ := Families.ModFour.half ((A : PowerSeries ℤ)-X-X^2)

theorem H_constantCoeff : constantCoeff ℤ H=0 := by
  apply Families.ModFour.half_constantCoeff
  simp [A_normalized.constantCoeff]

theorem A_decomposition : (A : PowerSeries ℤ)=X+X^2+2*H := by
  have hm : PowerSeries.map (Int.castRingHom (ZMod 2)) ((A : PowerSeries ℤ)-X-X^2)=0 := by
    simp only [map_sub, map_pow, PowerSeries.map_X, map_A, A_mod_two]
    ring
  have h := Families.ModFour.two_mul_half _ hm
  change 2*H=A-X-X^2 at h
  linear_combination -h


theorem A_mod_four_decomposition :
    (A : PowerSeries (ZMod 4))=X+X^2+2*PowerSeries.map (Int.castRingHom (ZMod 4)) H := by
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 4))) A_decomposition
  simpa only [map_add, map_mul, map_pow, map_ofNat, PowerSeries.map_X, map_A] using h

theorem H_mod_two_equation :
    let U := PowerSeries.map (Int.castRingHom (ZMod 2)) H
    U+U^2=(X : PowerSeries (ZMod 2))^3 := by
  let U := PowerSeries.map (Int.castRingHom (ZMod 4)) H
  have hU : constantCoeff (ZMod 4) U=0 := by
    simp only [U, constantCoeff_map, H_constantCoeff, map_zero]
  have hD : constantCoeff (ZMod 4) (X^2+2*U)=0 := by simp [hU]
  have ht : (2 : PowerSeries (ZMod 2))=0 := by
    have h : (2 : ZMod 2)=0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 2)) h
  have hf : (4 : PowerSeries (ZMod 4))=0 := by
    have h : (4 : ZMod 4)=0 := by decide
    simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 4)) h
  have hD2 : PowerSeries.map Families.ModFour.reduce (X^2+2*U)=
      (X : PowerSeries (ZMod 2))^2 := by
    simp only [map_add, map_pow, map_mul, map_ofNat, PowerSeries.map_X, ht,
      zero_mul, add_zero]
  have hc : 2*compose U (X^2+2*U)=2*compose U (X^2) := by
    apply Families.ModFour.series_double_eq_of_mod_two
    rw [map_compose _ _ _ hD, map_compose _ _ _ (by simp), hD2,
      map_pow, PowerSeries.map_X]
  have hc2 : compose (2*U) (X^2+2*U)=2*compose U (X^2+2*U) := by
    calc
      compose (2*U) (X^2+2*U)=compose (U+U) (X^2+2*U) := by rw [two_mul U]
      _=compose U (X^2+2*U)+compose U (X^2+2*U) := compose_add U U _ hD
      _=2*compose U (X^2+2*U) := by ring
  have he := A_equation (S:=ZMod 4)
  rw [A_mod_four_decomposition] at he
  change compose (X+X^2+2*U) (X+X^2+2*U-X)=(X+X^2+2*U)^2 at he
  have hsub : (X : PowerSeries (ZMod 4))+X^2+2*U-X=X^2+2*U := by ring
  rw [hsub, compose_add _ _ _ hD, compose_add _ _ _ hD,
    compose_pow _ _ _ hD, compose_X_left _ hD, hc2, hc] at he
  have hg : 2*(U+compose U (X^2))=2*(X^3) := by
    linear_combination he + X*U*hf
  have hg2 := (Families.ModFour.series_double_eq_iff _ _).1 hg
  rw [map_add, map_compose _ U (X^2) (by simp), map_pow, PowerSeries.map_X,
    map_pow, PowerSeries.map_X] at hg2
  simp only [U, Families.ModFour.reduce_int_map] at hg2
  rw [← square_substitution] at hg2
  exact hg2

theorem square_equation_unique (U V W : PowerSeries (ZMod 2))
    (hU0 : constantCoeff (ZMod 2) U=0) (hV0 : constantCoeff (ZMod 2) V=0)
    (hU : U+U^2=W) (hV : V+V^2=W) : U=V := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff] using hU0.trans hV0.symm
    · have hu := congrArg (coeff (ZMod 2) n) hU
      have hv := congrArg (coeff (ZMod 2) n) hV
      simp only [map_add, Hanna.Related.ScaledInverse.coeff_square_mod_two] at hu hv
      by_cases he : 2∣n
      · rw [if_pos he] at hu hv
        have hi := ih (n/2) (Nat.div_lt_self (by omega) (by omega))
        rw [hi] at hu
        exact add_right_cancel (hu.trans hv.symm)
      · rw [if_neg he, add_zero] at hu hv
        exact hu.trans hv.symm

def binary : PowerSeries (ZMod 2) :=
  Hanna.Related.ScaledInverse.scaledSolution (0 : ZMod 2)

theorem binary_constantCoeff : constantCoeff (ZMod 2) binary=0 :=
  (Hanna.Related.ScaledInverse.scaledSolution_normalized (0 : ZMod 2)).constantCoeff

theorem binary_equation : binary+binary^2=(X : PowerSeries (ZMod 2)) := by
  have h := Hanna.Related.ScaledInverse.scaledSolution_zero_quadratic (R:=ZMod 2)
  have hneg : -(binary^2)=binary^2 := by
    rw [neg_eq_iff_add_eq_zero]
    rw [← two_mul]
    have ht : (2 : PowerSeries (ZMod 2))=0 := by
      have hc : (2 : ZMod 2)=0 := by decide
      simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 2)) hc
    rw [ht, zero_mul]
  change binary-binary^2=X at h
  simpa only [sub_eq_add_neg, hneg] using h

theorem H_mod_two : PowerSeries.map (Int.castRingHom (ZMod 2)) H=
    compose binary ((X : PowerSeries (ZMod 2))^3) := by
  apply square_equation_unique _ _ (X^3)
  · simp only [constantCoeff_map, H_constantCoeff, map_zero]
  · rw [constantCoeff_compose _ _ (by simp), binary_constantCoeff]
  · exact H_mod_two_equation
  · have h := congrArg (fun E : PowerSeries (ZMod 2) => compose E (X^3)) binary_equation
    dsimp only at h
    rw [compose_add _ _ _ (by simp), compose_pow _ _ _ (by simp),
      compose_X_left _ (by simp)] at h
    exact h

theorem H_mod_two_coeff (n : ℕ) :
    coeff (ZMod 2) n (PowerSeries.map (Int.castRingHom (ZMod 2)) H)=1 ↔
      ∃ k : ℕ, n=3*2^k := by
  rw [H_mod_two, coeff_compose_X_power _ 3 n (by omega)]
  by_cases hd : 3∣n
  · rw [if_pos hd]
    change coeff (ZMod 2) (n/3) (Hanna.Related.ScaledInverse.scaledSolution 0)=1 ↔ _
    rw [Hanna.Related.ScaledInverse.scaledSolution_zero_coeff_one_iff]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,by rw [← hk, Nat.mul_div_cancel' hd]⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by omega⟩
  · rw [if_neg hd]
    constructor
    · intro h; exact False.elim (zero_ne_one h)
    · rintro ⟨k,hk⟩
      exact False.elim (hd ⟨2^k,hk⟩)

open scoped Classical in
theorem a389537_residue (n : ℕ) (hn : 2<n) :
    (a n : ZMod 4)=if ∃ k : ℕ, n=3*2^k then 2 else 0 := by
  have h := congrArg (coeff (ZMod 4) n) A_mod_four_decomposition
  have hX : coeff (ZMod 4) n X=0 := by
    rw [coeff_X, if_neg (by omega : n≠1)]
  have hX2 : coeff (ZMod 4) n (X^2)=0 := by
    rw [coeff_X_pow, if_neg (by omega : n≠2)]
  simp only [map_add, two_mul, hX, hX2, zero_add] at h
  have ha : (a n : ZMod 4)=coeff (ZMod 4) n (A : PowerSeries (ZMod 4)) := by
    rw [← map_A (Int.castRingHom (ZMod 4)), coeff_map]
    rfl
  rw [ha, h, ← two_mul]
  let u : ZMod 4 := coeff (ZMod 4) n (PowerSeries.map (Int.castRingHom (ZMod 4)) H)
  have hu : Families.ModFour.reduce u=1 ↔ ∃ k : ℕ, n=3*2^k := by
    simpa only [u, ← coeff_map, Families.ModFour.reduce_int_map] using H_mod_two_coeff n
  change 2*u=if ∃ k : ℕ, n=3*2^k then 2 else 0
  have hf : ∀ u : ZMod 4, 2*u=if Families.ModFour.reduce u=1 then 2 else 0 := by decide
  rw [hf u]
  simp only [hu]

end
end Families.LacunaryInverse
