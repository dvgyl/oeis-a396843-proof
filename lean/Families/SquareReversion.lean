import Families.CubicConsequences
import Hanna.Related.ScaledParity
import Mathlib.Tactic.FinCases
import Families.ModFour

/-!
# The modulus-four conjecture for OEIS A389542

We construct a normalized integral auxiliary series `L`, set `R = X - 2*X*L`,
and define the actual source series as the genuine compositional inverse of R.
The literal source equation and uniqueness are proved before the congruence.

AI-generated mathematical proof and formalization prepared for Dev D. Goyal.
-/

namespace Families.SquareReversion

open PowerSeries Hanna.Series

noncomputable section

variable {S T : Type*} [CommRing S] [CommRing T]

def step (G : PowerSeries S) : PowerSeries S :=
  X + G^2 - 2*X*compose G (4*X^3)

theorem step_normalized {G : PowerSeries S} (hG : Normalized G) :
    Normalized (step G) := by
  have hi : constantCoeff S (compose G (4*X^3)) = 0 := by
    rw [constantCoeff_compose _ _ (by simp)]
    exact hG.constantCoeff
  constructor
  · simp [step, hG.constantCoeff, hi]
  · have hsq : (X : PowerSeries S)^2 ∣ G^2 := by
      simpa [pow_two] using X_pow_dvd_product
        (show (X : PowerSeries S)^1 ∣ G by simpa using hG.X_dvd)
        (show (X : PowerSeries S)^1 ∣ G by simpa using hG.X_dvd)
    have hp : (X : PowerSeries S)^2 ∣ 2*X*compose G (4*X^3) := by
      have hc : (X : PowerSeries S)^1 ∣ compose G (4*X^3) := by
        simpa using X_dvd_iff.mpr hi
      have h := X_pow_dvd_product (dvd_refl ((X : PowerSeries S)^1)) hc
      convert dvd_mul_of_dvd_left h (2 : PowerSeries S) using 1; ring
    rw [step, map_sub, map_add, X_pow_dvd_iff.mp hsq 1 (by omega),
      X_pow_dvd_iff.mp hp 1 (by omega)]
    simp

theorem step_contraction (n : ℕ) {G H : PowerSeries S}
    (hG : Normalized G) (hH : Normalized H)
    (hGH : (X : PowerSeries S)^n ∣ G-H) :
    (X : PowerSeries S)^(n+1) ∣ step G-step H := by
  have hsum : (X : PowerSeries S)^1 ∣ G+H := by
    simpa using dvd_add hG.X_dvd hH.X_dvd
  have hsq := X_pow_dvd_product hGH hsum
  have hinner : (X : PowerSeries S)^1 ∣ 4*X^3 := by
    rw [pow_one]
    exact dvd_mul_of_dvd_right (dvd_pow_self X (by decide)) _
  have hcomp : (X : PowerSeries S)^n ∣ compose (G-H) (4*X^3) := by
    simpa using compose_outer_vanish (G-H) (4*X^3) n 1 (by simp) hGH hinner
  have hprod := X_pow_dvd_product hcomp (dvd_refl ((X : PowerSeries S)^1))
  have hmul := dvd_mul_of_dvd_left hprod (2 : PowerSeries S)
  rw [compose_sub _ _ _ (by simp)] at hmul
  convert dvd_sub hsq hmul using 1; unfold step; ring

theorem equation_triangular :
    Triangular (fun a n => coeff S (n+2) (ofTail a-step (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := step_contraction (n+2) (normalized_ofTail a) (normalized_ofTail b) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simp only [map_sub, coeff_ofTail] at hc ⊢
  linear_combination -hc

theorem L_exists : ∃ G : PowerSeries S, Normalized G ∧ G=step G := by
  let op := fun a n => coeff S (n+2) (ofTail a-step (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op equation_triangular (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have hs := step_normalized (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · exact (normalized_ofTail a).1.trans hs.1.symm
  · exact (normalized_ofTail a).2.trans hs.2.symm
  · have hc := congrFun ha n
    change coeff S (n+2) (ofTail a-step (ofTail a))=0 at hc
    simpa only [map_sub, sub_eq_zero, Nat.succ_eq_add_one, Nat.add_assoc] using hc

theorem L_unique {G H : PowerSeries S} (hG : Normalized G) (hH : Normalized H)
    (hEG : G=step G) (hEH : H=step H) : G=H := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := (agree_iff_X_pow_dvd_sub n G H).mp ih
    have hp := step_contraction n hG hH hd
    have hc := X_pow_dvd_iff.mp hp n (by omega)
    rw [← hEG, ← hEH, map_sub, sub_eq_zero] at hc
    exact hc

theorem L_existence_uniqueness : ∃! G : PowerSeries S, Normalized G ∧ G=step G := by
  obtain ⟨G,hG,hE⟩ := L_exists (S:=S)
  exact ⟨G,⟨hG,hE⟩,fun H hH => L_unique hH.1 hG hH.2 hE⟩

def L : PowerSeries S := (L_existence_uniqueness (S:=S)).exists.choose

theorem L_normalized : Normalized (L : PowerSeries S) :=
  (L_existence_uniqueness (S:=S)).exists.choose_spec.1

theorem L_equation : (L : PowerSeries S)=step L :=
  (L_existence_uniqueness (S:=S)).exists.choose_spec.2

def R : PowerSeries S := X-2*X*L

theorem R_normalized : Normalized (R : PowerSeries S) := by
  constructor
  · simp [R]
  · simp [R, two_mul, add_mul, L_normalized.constantCoeff]

def InverseEquation (G : PowerSeries S) : Prop := G^2+compose G (4*X^3)=X^2

theorem R_equation : InverseEquation (R : PowerSeries S) := by
  have hz : constantCoeff S (4*X^3 : PowerSeries S)=0 := by simp
  have he := L_equation (S:=S)
  unfold step at he
  have htwo : compose (2 : PowerSeries S) (4*X^3)=2 := by
    simpa using Families.CubicReversion.compose_natCast 2 (4*X^3 : PowerSeries S) hz
  unfold InverseEquation R
  rw [compose_sub _ _ _ hz, compose_mul _ _ _ hz, compose_mul _ _ _ hz,
    compose_X_left _ hz, htwo]
  linear_combination -4*(X : PowerSeries S)^2*he

def A389542 : PowerSeries S := inverse R R_normalized

theorem A389542_normalized : Normalized (A389542 : PowerSeries S) :=
  inverse_normalized R R_normalized

theorem compose_R_A : compose (R : PowerSeries S) A389542=X :=
  compose_inverse_right R R_normalized

theorem compose_A_R : compose (A389542 : PowerSeries S) R=X :=
  compose_inverse_left R R_normalized

def SourceEquation (G : PowerSeries S) : Prop := compose G (G^2-X^2)=4*G^3

theorem source_of_inverse {A B : PowerSeries S} (hA : Normalized A)
    (hB : Normalized B) (hAB : compose A B=X) (hBA : compose B A=X)
    (he : InverseEquation B) : SourceEquation A := by
  have hz : constantCoeff S (4*X^3 : PowerSeries S)=0 := by simp
  have h4A : constantCoeff S (4*A^3)=0 := by simp [hA.constantCoeff]
  have hfour : compose (4 : PowerSeries S) A=4 := by
    simpa using Families.CubicReversion.compose_natCast 4 A hA.constantCoeff
  have h := congrArg (fun F : PowerSeries S => compose F A) he
  change compose (B^2+compose B (4*X^3)) A=compose (X^2) A at h
  rw [compose_add _ _ _ hA.constantCoeff, compose_pow _ _ _ hA.constantCoeff,
    compose_assoc B _ A hz hA.constantCoeff, compose_mul _ _ _ hA.constantCoeff,
    hfour,
    compose_pow _ _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff, hBA] at h
  simp only [compose_pow _ _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff] at h
  have hBAeq : compose B (4*A^3)=A^2-X^2 := by linear_combination h
  unfold SourceEquation
  rw [← hBAeq, ← compose_assoc A B _ hB.constantCoeff h4A, hAB,
    compose_X_left _ h4A]

theorem inverse_of_source {A B : PowerSeries S} (hA : Normalized A)
    (hB : Normalized B) (hAB : compose A B=X) (hBA : compose B A=X)
    (he : SourceEquation A) : InverseEquation B := by
  have hV : constantCoeff S (A^2-X^2)=0 := by simp [hA.constantCoeff]
  have hW : constantCoeff S (X^2-B^2)=0 := by simp [hB.constantCoeff]
  have hfour : compose (4 : PowerSeries S) B=4 := by
    simpa using Families.CubicReversion.compose_natCast 4 B hB.constantCoeff
  have h := congrArg (fun F : PowerSeries S => compose F B) he
  change compose (compose A (A^2-X^2)) B=compose (4*A^3) B at h
  rw [compose_assoc A _ B hV hB.constantCoeff,
    compose_sub _ _ _ hB.constantCoeff, compose_pow _ _ _ hB.constantCoeff,
    compose_pow _ _ _ hB.constantCoeff, compose_X_left _ hB.constantCoeff,
    compose_mul _ _ _ hB.constantCoeff,
    hfour,
    compose_pow _ _ _ hB.constantCoeff, hAB] at h
  have h' := congrArg (compose B) h
  rw [← compose_assoc B A _ hA.constantCoeff hW, hBA, compose_X_left _ hW] at h'
  unfold InverseEquation
  linear_combination -h'

theorem a389542_equation :
    compose (A389542 : PowerSeries ℤ) (A389542^2-X^2)=4*A389542^3 :=
  source_of_inverse A389542_normalized R_normalized compose_A_R compose_R_A R_equation

theorem inverse_residual_perturbation (G H : PowerSeries S) (r : ℕ) (hr : 2≤r)
    (hG : Normalized G) (hH : Normalized H) (hd : X^r∣G-H) :
    X^(r+2)∣(G^2+compose G (4*X^3))-(H^2+compose H (4*X^3))-2*X*(G-H) := by
  have hsum : (X : PowerSeries S)^2∣G+H-2*X := by
    have h1 := (normalized_iff_X_sq_dvd G).mp hG
    have h2 := (normalized_iff_X_sq_dvd H).mp hH
    convert dvd_add h1 h2 using 1; ring
  have hsq := X_pow_dvd_product hd hsum
  have hc : (X : PowerSeries S)^(r+2)∣compose (G-H) (4*X^3) := by
    have h := compose_outer_vanish (G-H) (4*X^3) r 3 (by simp) hd
      (dvd_mul_left (X^3) 4)
    exact (pow_dvd_pow X (by omega : r+2≤3*r)).trans h
  rw [compose_sub _ _ _ (by simp)] at hc
  convert dvd_add hsq hc using 1; ring

theorem inverse_equation_unique {G H : PowerSeries ℤ} (hG : Normalized G)
    (hH : Normalized H) (heG : InverseEquation G) (heH : InverseEquation H) : G=H := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<2
    · rcases (by omega : n=0 ∨ n=1) with rfl | rfl
      · exact hG.1.trans hH.1.symm
      · exact hG.2.trans hH.2.symm
    · have hd := (agree_iff_X_pow_dvd_sub n G H).mp ih
      have hp := inverse_residual_perturbation G H n (by omega) hG hH hd
      have hc := X_pow_dvd_iff.mp hp (n+1) (by omega)
      rw [heG, heH] at hc
      have hx : coeff ℤ (n+1) (2*X*(G-H))=2*(coeff ℤ n G-coeff ℤ n H) := by
        simp [two_mul, add_mul]
      simp only [sub_self, zero_sub, map_neg, hx] at hc
      omega

theorem a389542_unique (G : PowerSeries ℤ) (hG : Normalized G)
    (he : compose G (G^2-X^2)=4*G^3) : G=A389542 := by
  let H := inverse G hG
  have hH : Normalized H := inverse_normalized G hG
  have hGH : compose G H=X := compose_inverse_right G hG
  have hHG : compose H G=X := compose_inverse_left G hG
  have hHe : InverseEquation H := inverse_of_source hG hH hGH hHG he
  have hR : H=R := inverse_equation_unique hH R_normalized hHe R_equation
  apply Hanna.Series.inverse_unique (R_normalized (S:=ℤ)) (A389542_normalized (S:=ℤ))
  · rw [← hR]; exact hGH
  · exact compose_R_A (S:=ℤ)

theorem a389542_existence_uniqueness :
    ∃! G : PowerSeries ℤ, Normalized G ∧ compose G (G^2-X^2)=4*G^3 := by
  exact ⟨A389542,⟨A389542_normalized,a389542_equation⟩,
    fun G hG => a389542_unique G hG.1 hG.2⟩

theorem map_step (f : S →+* T) (G : PowerSeries S) :
    PowerSeries.map f (step G)=step (PowerSeries.map f G) := by
  have hz : constantCoeff S (4*X^3 : PowerSeries S)=0 := by simp
  simp only [step, map_sub, map_add, map_pow, map_mul, map_ofNat,
    PowerSeries.map_X, map_compose f G _ hz]

theorem map_L (f : S →+* T) : PowerSeries.map f (L : PowerSeries S)=L := by
  apply L_unique (L_normalized.map f) L_normalized
  · rw [← map_step f L, ← L_equation]
  · exact L_equation

theorem map_R (f : S →+* T) : PowerSeries.map f (R : PowerSeries S)=R := by
  simp only [R, map_sub, map_mul, map_ofNat, PowerSeries.map_X, map_L]

private theorem inverse_congr {G H : PowerSeries S}
    (hG : Normalized G) (hH : Normalized H) (he : G=H) :
    inverse G hG=inverse H hH := by
  subst H
  rfl

theorem map_A389542 (f : S →+* T) :
    PowerSeries.map f (A389542 : PowerSeries S)=A389542 := by
  change PowerSeries.map f (inverse R R_normalized)=inverse R R_normalized
  rw [map_inverse]
  exact inverse_congr (R_normalized.map f) R_normalized (map_R f)

private theorem two_zero : (2 : PowerSeries (ZMod 2))=0 := by
  have h : (2 : ZMod 2)=0 := by decide
  simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 2)) h

private theorem four_zero : (4 : PowerSeries (ZMod 4))=0 := by
  have h : (4 : ZMod 4)=0 := by decide
  simpa only [map_ofNat, map_zero] using congrArg (C (ZMod 4)) h

theorem L_quadratic_mod_two :
    (L : PowerSeries (ZMod 2))-L^2=X := by
  have he := L_equation (S:=ZMod 2)
  unfold step at he
  rw [two_zero, zero_mul, zero_mul, sub_zero] at he
  linear_combination he

theorem L_coeff_one_iff (n : ℕ) :
    coeff (ZMod 2) n L=1 ↔ ∃ k : ℕ, n=2^k :=
  Hanna.Related.ScaledInverse.quadratic_coeff_one_iff_power_two L L_normalized
    L_quadratic_mod_two n

theorem R_reduce_mod_two :
    PowerSeries.map Families.ModFour.reduce (R : PowerSeries (ZMod 4))=X := by
  rw [map_R, R, two_zero, zero_mul, zero_mul, sub_zero]

theorem R_involution_mod_four :
    compose (R : PowerSeries (ZMod 4)) R=X := by
  have hmap : PowerSeries.map Families.ModFour.reduce
      (compose (L : PowerSeries (ZMod 4)) R)=PowerSeries.map Families.ModFour.reduce L := by
    rw [map_compose _ _ _ R_normalized.constantCoeff, R_reduce_mod_two, compose_X_right]
  have hdouble := Families.ModFour.series_double_eq_of_mod_two _ _ hmap
  have htwo : compose (2 : PowerSeries (ZMod 4)) R=2 := by
    simpa using Families.CubicReversion.compose_natCast 2
      (R : PowerSeries (ZMod 4)) R_normalized.constantCoeff
  change compose ((X : PowerSeries (ZMod 4))-2*X*L) R=X
  rw [compose_sub _ _ _ R_normalized.constantCoeff,
    compose_mul _ _ _ R_normalized.constantCoeff,
    compose_mul _ _ _ R_normalized.constantCoeff,
    compose_X_left _ R_normalized.constantCoeff, htwo]
  have hmul : (2 : PowerSeries (ZMod 4))*R*compose L R=R*(2*L) := by
    calc
      (2 : PowerSeries (ZMod 4))*R*compose L R=R*(2*compose L R) := by ring
      _=R*(2*L) := congrArg (fun U : PowerSeries (ZMod 4) => R*U) hdouble
  rw [hmul]
  unfold R
  linear_combination (X : PowerSeries (ZMod 4))*(L^2-L)*four_zero

theorem A_eq_R_mod_four : (A389542 : PowerSeries (ZMod 4))=R :=
  Hanna.Series.inverse_unique R_normalized R_normalized compose_A_R R_involution_mod_four

theorem a389542_series_mod_four :
    PowerSeries.map (Int.castRingHom (ZMod 4)) (A389542 : PowerSeries ℤ)=
      X-2*X*(L : PowerSeries (ZMod 4)) := by
  rw [map_A389542, A_eq_R_mod_four]
  rfl

theorem a389542_coeff_mod_four (n : ℕ) (hn : 1<n) :
    (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=
      -2*coeff (ZMod 4) (n-1) L := by
  have h := congrArg (coeff (ZMod 4) n) a389542_series_mod_four
  rw [coeff_map] at h
  have hn1 : n=(n-1)+1 := by omega
  have hx : coeff (ZMod 4) n (2*X*L)=2*coeff (ZMod 4) (n-1) L := by
    conv_lhs => rw [hn1]
    simp [two_mul, add_mul]
  simpa only [Int.coe_castRingHom, map_sub, coeff_X, if_neg (by omega : n≠1),
    zero_sub, hx, neg_mul] using h

private theorem neg_double_residue (z : ZMod 4) :
    -2*z=if Families.ModFour.reduce z=1 then 2 else 0 := by
  exact (by decide : ∀ z : ZMod 4,
    -2*z=if Families.ModFour.reduce z=1 then 2 else 0) z

open scoped Classical in
/-- The precise conjectured residue pattern for the actual source series. -/
theorem a389542_residue (n : ℕ) (hn : 1<n) :
    (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=
      if ∃ k : ℕ, n=2^k+1 then 2 else 0 := by
  classical
  rw [a389542_coeff_mod_four n hn, neg_double_residue]
  have hmap := congrArg (coeff (ZMod 2) (n-1)) (map_L Families.ModFour.reduce)
  rw [coeff_map] at hmap
  rw [hmap]
  have hp : coeff (ZMod 2) (n-1) L=1 ↔ ∃ k : ℕ, n=2^k+1 := by
    rw [L_coeff_one_iff]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k,by omega⟩
    · rintro ⟨k,hk⟩
      exact ⟨k,by omega⟩
  simp only [hp]

/-- Coefficients in degrees one more than powers of two are two modulo four. -/
theorem a389542_two_mod_four_iff (n : ℕ) (hn : 1<n) :
    (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=2 ↔
      ∃ k : ℕ, n=2^k+1 := by
  classical
  rw [a389542_residue n hn]
  split_ifs <;> simp_all [show (0 : ZMod 4) ≠ 2 by decide,
    show (2 : ZMod 4) ≠ 0 by decide]

/-- All other coefficients in degrees greater than one are divisible by four. -/
theorem a389542_four_dvd_iff (n : ℕ) (hn : 1<n) :
    (4 : ℤ) ∣ coeff ℤ n (A389542 : PowerSeries ℤ) ↔
      ¬ ∃ k : ℕ, n=2^k+1 := by
  classical
  have hd : (coeff ℤ n (A389542 : PowerSeries ℤ) : ZMod 4)=0 ↔
      (4 : ℤ) ∣ coeff ℤ n (A389542 : PowerSeries ℤ) :=
    ZMod.intCast_zmod_eq_zero_iff_dvd _ 4
  rw [← hd, a389542_residue n hn]
  split_ifs <;> simp_all [show (0 : ZMod 4) ≠ 2 by decide,
    show (2 : ZMod 4) ≠ 0 by decide]

end
end Families.SquareReversion
