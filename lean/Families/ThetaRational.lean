module

public import Families.ThetaSubstitution
public import Families.ModFour

/-!
# Rational theta sums: OEIS A380060 and a correction to A380680

The positive-index source formula is interpreted coefficientwise, so each
coefficient is a finite sum. Multiplicative inverses have constant term one.
The implicit A380060 equation is constructed and proved uniquely solvable.

AI-generated mathematical arguments and Lean formalization for Dev D. Goyal.
The source sequences and conjectures are credited to Paul D. Hanna.
-/

@[expose] public section

namespace Families.ThetaRational

open PowerSeries Hanna.Series ThetaSubstitution

noncomputable section

attribute [local instance] Classical.propDecidable

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The denominator in the j-th positive summand, with j=k+1. -/
def denominator (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  1-X^(k+1)*A

@[simp] theorem denominator_constant (A : PowerSeries R) (k : ℕ) :
    constantCoeff (denominator A k)=1 := by simp [denominator]

/-- `(A-X^j)/(1-X^j*A)` uses genuine multiplicative inversion. -/
def ratio (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  (A-X^(k+1))*unitInv (denominator A k)

theorem ratio_quotient (A : PowerSeries R) (k : ℕ) :
    denominator A k*ratio A k=A-X^(k+1) := by
  rw [ratio, mul_left_comm, mul_unitInv (denominator_constant A k), mul_one]

/-- The summand with positive index k+1. -/
def summand (A : PowerSeries R) (k : ℕ) : PowerSeries R :=
  X^((k+1)^2)*(ratio A k)^(k+1)

theorem summand_vanish (A : PowerSeries R) (k n : ℕ) (hn : n<(k+1)^2) :
    coeff n (summand A k)=0 := by
  exact X_pow_dvd_iff.mp (dvd_mul_right ((X : PowerSeries R)^((k+1)^2)) _) n hn

/-- The locally finite positive theta sum. -/
def sigma (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n+1), coeff n (summand A k)

@[simp] theorem sigma_coeff (A : PowerSeries R) (n : ℕ) :
    coeff n (sigma A)=∑ k ∈ Finset.range (n+1), coeff n (summand A k) := by
  simp [sigma]

/-- The finite definition equals the literal coefficientwise infinite sum. -/
theorem sigma_coeff_finsum (A : PowerSeries R) (n : ℕ) :
    coeff n (sigma A)=∑ᶠ k : ℕ, coeff n (summand A k) := by
  rw [sigma_coeff]
  symm
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  have hn : n<(k+1)^2 := by nlinarith
  exact hk (summand_vanish A k n hn)

@[simp] theorem sigma_constant (A : PowerSeries R) :
    constantCoeff (sigma A)=0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, sigma_coeff]
  simp [summand, ratio]

/-- The right-hand side in source formula (2) of both entries. -/
def step (A : PowerSeries R) : PowerSeries R := 1+2*sigma A

@[simp] theorem step_constant (A : PowerSeries R) :
    constantCoeff (step A)=1 := by simp [step]

theorem unitInv_sub_identity {U V : PowerSeries R}
    (hU : constantCoeff U=1) (hV : constantCoeff V=1) :
    unitInv U-unitInv V=unitInv U*(V-U)*unitInv V := by
  rw [mul_sub, sub_mul]
  have hu := unitInv_mul hU
  have hv := unitInv_mul hV
  calc
    unitInv U-unitInv V = unitInv U*(unitInv V*V)-(unitInv U*U)*unitInv V := by
      rw [hu,hv,mul_one,one_mul]
    _ = unitInv U*V*unitInv V-unitInv U*U*unitInv V := by ring

theorem unitInv_dvd_sub (n : ℕ) {U V : PowerSeries R}
    (hU : constantCoeff U=1) (hV : constantCoeff V=1)
    (hd : (X : PowerSeries R)^n ∣ U-V) : X^n ∣ unitInv U-unitInv V := by
  rw [unitInv_sub_identity hU hV]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by simpa only [neg_sub] using dvd_neg.mpr hd) _) _

theorem ratio_dvd_sub (n k : ℕ) (A B : PowerSeries R)
    (hd : (X : PowerSeries R)^n ∣ A-B) : X^n ∣ ratio A k-ratio B k := by
  have hD : (X : PowerSeries R)^n ∣ denominator A k-denominator B k := by
    have hh := dvd_mul_of_dvd_right (dvd_neg.mpr hd) ((X : PowerSeries R)^(k+1))
    convert hh using 1
    simp only [denominator]
    ring
  have hi := unitInv_dvd_sub n (denominator_constant A k) (denominator_constant B k) hD
  have he : ratio A k-ratio B k =
      (A-B)*unitInv (denominator A k)+
        (B-X^(k+1))*(unitInv (denominator A k)-unitInv (denominator B k)) := by
    simp only [ratio]; ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_left hd _) (dvd_mul_of_dvd_right hi _)

theorem summand_dvd_sub (n k : ℕ) (A B : PowerSeries R)
    (hd : (X : PowerSeries R)^n ∣ A-B) :
    X^(n+1) ∣ summand A k-summand B k := by
  have hp := (ratio_dvd_sub n k A B hd).trans
    (sub_dvd_pow_sub_pow (ratio A k) (ratio B k) (k+1))
  have he : (X : PowerSeries R)^1 ∣ X^((k+1)^2) :=
    pow_dvd_pow X (Nat.succ_le_of_lt (by positivity))
  have hh := mul_dvd_mul he hp
  rw [← pow_add] at hh
  simpa only [summand, ← mul_sub, Nat.add_comm] using hh

theorem step_contraction (n : ℕ) (A B : PowerSeries R)
    (hd : (X : PowerSeries R)^n ∣ A-B) : X^(n+1) ∣ step A-step B := by
  apply (agree_iff_X_pow_dvd_sub (n+1) (step A) (step B)).mp
  intro m hm
  have hs : coeff m (sigma A)=coeff m (sigma B) := by
    simp only [sigma_coeff]
    apply Finset.sum_congr rfl
    intro k _
    have h := X_pow_dvd_iff.mp (summand_dvd_sub n k A B hd) m hm
    simpa only [map_sub, sub_eq_zero] using h
  simp only [step, two_mul, map_add, hs]

theorem recursion_triangular :
    Triangular (fun (a : ℕ → R) n => coeff n (PowerSeries.mk a-step (PowerSeries.mk a))) := by
  intro n a b hab
  have hd : (X : PowerSeries R)^n ∣ PowerSeries.mk a-PowerSeries.mk b := by
    apply (agree_iff_X_pow_dvd_sub n _ _).mp
    intro k hk
    simpa only [coeff_mk] using hab k hk
  have hp := X_pow_dvd_iff.mp (step_contraction n _ _ hd) n (by omega)
  simp only [map_sub, coeff_mk] at hp ⊢
  linear_combination -hp

theorem existence_uniqueness : ∃! A : PowerSeries R, A=step A := by
  let op := fun (a : ℕ → R) n => coeff n (PowerSeries.mk a-step (PowerSeries.mk a))
  obtain ⟨a,ha,hu⟩ := triangular_existsUnique op recursion_triangular (fun _ => 0)
  have he : PowerSeries.mk a=step (PowerSeries.mk a) := by
    ext n
    have h := congrFun ha n
    change coeff n (PowerSeries.mk a-step (PowerSeries.mk a))=0 at h
    simpa only [map_sub, sub_eq_zero] using h
  refine ⟨PowerSeries.mk a,he,?_⟩
  intro B hB
  have hb : (fun n => coeff n B)=a := by
    apply hu
    funext n
    change coeff n (PowerSeries.mk (fun n => coeff n B)-
      step (PowerSeries.mk (fun n => coeff n B)))=0
    have hm : PowerSeries.mk (fun n => coeff n B)=B := by ext; simp
    rw [hm, ← hB, sub_self, map_zero]
  ext n
  simpa only [coeff_mk] using congrFun hb n

/-- Canonical solution of the implicit source equation, over any commutative ring. -/
def solution : PowerSeries R := existence_uniqueness.exists.choose

theorem solution_equation : (solution : PowerSeries R)=step solution :=
  existence_uniqueness.exists.choose_spec

theorem solution_unique {A : PowerSeries R} (he : A=step A) : A=solution :=
  existence_uniqueness.unique he solution_equation

@[simp] theorem solution_constant : constantCoeff (solution : PowerSeries R)=1 := by
  rw [solution_equation, step_constant]

theorem map_denominator (f : R →+* S) (A : PowerSeries R) (k : ℕ) :
    PowerSeries.map f (denominator A k)=denominator (PowerSeries.map f A) k := by
  simp only [denominator, map_sub, map_one, map_mul, map_pow, PowerSeries.map_X]

theorem map_ratio (f : R →+* S) (A : PowerSeries R) (k : ℕ) :
    PowerSeries.map f (ratio A k)=ratio (PowerSeries.map f A) k := by
  simp only [ratio, map_mul, map_sub, map_pow, PowerSeries.map_X,
    map_unitInv f (denominator_constant A k), map_denominator]

theorem map_summand (f : R →+* S) (A : PowerSeries R) (k : ℕ) :
    PowerSeries.map f (summand A k)=summand (PowerSeries.map f A) k := by
  simp only [summand, map_mul, map_pow, PowerSeries.map_X, map_ratio]

theorem map_sigma (f : R →+* S) (A : PowerSeries R) :
    PowerSeries.map f (sigma A)=sigma (PowerSeries.map f A) := by
  ext n
  simp only [coeff_map, sigma_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (coeff_map f n (summand A k)).symm.trans
    (congrArg (coeff n) (map_summand f A k))

theorem map_step (f : R →+* S) (A : PowerSeries R) :
    PowerSeries.map f (step A)=step (PowerSeries.map f A) := by
  simp only [step, map_add, map_one, map_mul, map_ofNat, map_sigma]

theorem map_solution (f : R →+* S) :
    PowerSeries.map f (solution : PowerSeries R)=(solution : PowerSeries S) := by
  apply solution_unique
  rw [← map_step, ← solution_equation]

/-- Positive squares multiplied by d, expressed without any analytic series. -/
def scaledSquare (d n : ℕ) : Prop := ∃ j : ℕ, 0<j ∧ n=d*j^2

def squareSeries (d : ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => if scaledSquare d n then 1 else 0

@[simp] theorem squareSeries_coeff (d n : ℕ) :
    coeff n (squareSeries (R := R) d)=if scaledSquare d n then 1 else 0 := by
  simp [squareSeries]

theorem squareSeries_constant (d : ℕ) (hd : 0<d) :
    constantCoeff (squareSeries d : PowerSeries R)=0 := by
  have hn : ¬scaledSquare d 0 := by
    rintro ⟨j,hj,he⟩
    have : 0<d*j^2 := by positivity
    omega
  simp [squareSeries,hn]

theorem map_squareSeries (f : R →+* S) (d : ℕ) :
    PowerSeries.map f (squareSeries d : PowerSeries R)=squareSeries d := by
  ext n
  simp only [coeff_map,squareSeries_coeff]
  split_ifs <;> simp

theorem sigma_of_monomials (A : PowerSeries R) (d : ℕ) (hd : 0<d)
    (he : ∀ k : ℕ, summand A k=X^(d*(k+1)^2)) : sigma A=squareSeries d := by
  ext n
  simp only [sigma_coeff,squareSeries_coeff,he]
  by_cases hn : scaledSquare d n
  · rw [if_pos hn]
    obtain ⟨j,hj,rfl⟩ := hn
    have hj1 : j-1+1=j := by omega
    have hmem : j-1 ∈ Finset.range (d*j^2+1) := by
      apply Finset.mem_range.mpr
      have hsq : j≤j^2 := by nlinarith
      have hm : j^2≤d*j^2 := Nat.le_mul_of_pos_left _ hd
      omega
    rw [Finset.sum_eq_single (j-1)]
    · simp [hj1]
    · intro k _ hkj
      have hh : d*(k+1)^2≠d*j^2 := by
        intro heq
        have heq' : (k+1)^2=j^2 := Nat.eq_of_mul_eq_mul_left hd heq
        have : k+1=j := by nlinarith
        omega
      simp [PowerSeries.coeff_X_pow, hh, Ne.symm hh]
    · exact fun h => (h hmem).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro k _
    have hh : n≠d*(k+1)^2 := by
      intro h
      exact hn ⟨k+1,by omega,h⟩
    simp [PowerSeries.coeff_X_pow,hh,Ne.symm hh]

theorem ratio_one (k : ℕ) : ratio (1 : PowerSeries R) k=1 := by
  have hd : denominator (1 : PowerSeries R) k=1-X^(k+1) := by simp [denominator]
  rw [ratio, ← hd, mul_unitInv (denominator_constant 1 k)]

theorem sigma_one : sigma (1 : PowerSeries R)=squareSeries 1 := by
  apply sigma_of_monomials _ 1 (by omega)
  intro k
  simp [summand,ratio_one]

theorem ratio_zero_mod_two (k : ℕ) :
    ratio (0 : PowerSeries (ZMod 2)) k=X^(k+1) := by
  have hu : unitInv (1 : PowerSeries (ZMod 2))=1 := by
    exact (unitInv_unique (by simp) (by simp)).symm
  simp only [ratio,denominator,mul_zero,sub_zero,hu,mul_one,zero_sub]
  ext n
  simpa only [map_neg] using (by decide : ∀ u : ZMod 2, -u=u)
    (coeff (R := (ZMod 2)) n ((X : PowerSeries (ZMod 2))^(k+1)))

theorem sigma_zero_mod_two :
    sigma (0 : PowerSeries (ZMod 2))=squareSeries 2 := by
  apply sigma_of_monomials _ 2 (by omega)
  intro k
  rw [summand,ratio_zero_mod_two, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem solution_mod_two : (solution : PowerSeries (ZMod 2))=1 := by
  rw [solution_equation,step]
  have hz : (2 : PowerSeries (ZMod 2))=0 := by
    simpa only [map_ofNat,map_zero] using
      congrArg (C (R := (ZMod 2))) (show (2 : ZMod 2)=0 by decide)
  rw [hz,zero_mul,add_zero]

theorem solution_mod_four :
    (solution : PowerSeries (ZMod 4))=1+2*squareSeries 1 := by
  rw [solution_equation,step]
  congr 1
  apply Families.ModFour.series_double_eq_of_mod_two
  rw [map_sigma,map_solution,solution_mod_two,sigma_one,map_squareSeries]

/-- OEIS A380060, defined by its unique source equation. -/
def A380060 : PowerSeries ℤ := solution

/-- OEIS A380680, using its explicit positive-index source formula (2). -/
def A380680 : PowerSeries ℤ := step 2

theorem a380060_source_equation : A380060=1+2*sigma A380060 := solution_equation

theorem a380060_existence_uniqueness :
    ∃! A : PowerSeries ℤ, A=1+2*sigma A := existence_uniqueness

theorem a380060_source_uniqueness {A : PowerSeries ℤ}
    (he : A=1+2*sigma A) : A=A380060 := solution_unique he

theorem a380680_source_formula : A380680=1+2*sigma 2 := rfl

theorem a380060_series_mod_four :
    PowerSeries.map (Int.castRingHom (ZMod 4)) A380060=1+2*squareSeries 1 := by
  rw [A380060,map_solution,solution_mod_four]

theorem a380680_series_mod_four :
    PowerSeries.map (Int.castRingHom (ZMod 4)) A380680=1+2*squareSeries 2 := by
  rw [A380680,map_step,map_ofNat,step]
  congr 1
  apply Families.ModFour.series_double_eq_of_mod_two
  rw [map_sigma,map_ofNat,map_squareSeries]
  have hz : (2 : PowerSeries (ZMod 2))=0 := by
    simpa only [map_ofNat,map_zero] using
      congrArg (C (R := (ZMod 2))) (show (2 : ZMod 2)=0 by decide)
  rw [hz,sigma_zero_mod_two]

theorem step_coefficient (A : PowerSeries R) (n : ℕ) :
    coeff n (step A)=coeff n (1 : PowerSeries R)+
      2*∑ k ∈ Finset.range (n+1), coeff n
        (X^((k+1)^2)*((A-X^(k+1))*unitInv (1-X^(k+1)*A))^(k+1)) := by
  simp only [step,two_mul,map_add,sigma_coeff,summand,ratio,denominator]

theorem a380060_coefficient_formula (n : ℕ) :
    coeff (R := ℤ) n A380060=coeff (R := ℤ) n (1 : PowerSeries ℤ)+
      2*∑ k ∈ Finset.range (n+1), coeff (R := ℤ) n
        (X^((k+1)^2)*((A380060-X^(k+1))*unitInv (1-X^(k+1)*A380060))^(k+1)) := by
  conv_lhs => rw [A380060,solution_equation]
  exact step_coefficient _ n

theorem a380680_coefficient_formula (n : ℕ) :
    coeff (R := ℤ) n A380680=coeff (R := ℤ) n (1 : PowerSeries ℤ)+
      2*∑ k ∈ Finset.range (n+1), coeff (R := ℤ) n
        (X^((k+1)^2)*((2-X^(k+1))*unitInv (1-X^(k+1)*2))^(k+1)) :=
  step_coefficient 2 n

theorem scaledSquare_iff (d n : ℕ) (hn : 0<n) :
    scaledSquare d n ↔ ∃ j : ℕ, n=d*j^2 := by
  constructor
  · rintro ⟨j,_,he⟩; exact ⟨j,he⟩
  · rintro ⟨j,he⟩
    refine ⟨j,?_,he⟩
    by_contra h
    have hj : j=0 := by omega
    simp [hj] at he
    omega

theorem theta_residue (d n : ℕ) (hn : 0<n) :
    coeff (R := (ZMod 4)) n (1+2*squareSeries d)=
      if ∃ j : ℕ, n=d*j^2 then 2 else 0 := by
  simp only [two_mul,map_add,squareSeries_coeff,scaledSquare_iff d n hn]
  rw [coeff_one n,if_neg (by omega : n≠0)]
  split_ifs <;> norm_num

theorem a380060_congruence (n : ℕ) (hn : 0<n) :
    (coeff (R := ℤ) n A380060 : ZMod 4)=if ∃ j : ℕ, n=j^2 then 2 else 0 := by
  have h := congrArg (coeff (R := (ZMod 4)) n) a380060_series_mod_four
  simpa only [coeff_map,Int.coe_castRingHom,theta_residue 1 n hn,one_mul] using h

theorem a380680_corrected_congruence (n : ℕ) (hn : 0<n) :
    (coeff (R := ℤ) n A380680 : ZMod 4)=if ∃ j : ℕ, n=2*j^2 then 2 else 0 := by
  have h := congrArg (coeff (R := (ZMod 4)) n) a380680_series_mod_four
  simpa only [coeff_map,Int.coe_castRingHom,theta_residue 2 n hn] using h

theorem a380060_square_iff (n : ℕ) (hn : 0<n) :
    (coeff (R := ℤ) n A380060 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2 := by
  rw [a380060_congruence n hn]
  split_ifs with h <;> simp [h,show (0 : ZMod 4)≠2 by decide]

theorem a380680_twice_square_iff (n : ℕ) (hn : 0<n) :
    (coeff (R := ℤ) n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=2*j^2 := by
  rw [a380680_corrected_congruence n hn]
  split_ifs with h <;> simp [h,show (0 : ZMod 4)≠2 by decide]

theorem a380060_four_dvd_iff (n : ℕ) (hn : 0<n) :
    (4 : ℤ) ∣ coeff (R := ℤ) n A380060 ↔ ¬∃ j : ℕ, n=j^2 := by
  have hd : (coeff (R := ℤ) n A380060 : ZMod 4)=0 ↔ (4 : ℤ) ∣ coeff (R := ℤ) n A380060 :=
    ZMod.intCast_zmod_eq_zero_iff_dvd _ 4
  rw [← hd, a380060_congruence n hn]
  split_ifs with h <;> simp [h,show (2 : ZMod 4)≠0 by decide]

theorem a380680_four_dvd_iff (n : ℕ) (hn : 0<n) :
    (4 : ℤ) ∣ coeff (R := ℤ) n A380680 ↔ ¬∃ j : ℕ, n=2*j^2 := by
  have hd : (coeff (R := ℤ) n A380680 : ZMod 4)=0 ↔ (4 : ℤ) ∣ coeff (R := ℤ) n A380680 :=
    ZMod.intCast_zmod_eq_zero_iff_dvd _ 4
  rw [← hd, a380680_corrected_congruence n hn]
  split_ifs with h <;> simp [h,show (2 : ZMod 4)≠0 by decide]

theorem a380680_coeff_one : coeff (R := ℤ) 1 A380680=4 := by
  rw [A380680,step]
  simp only [two_mul,map_add,sigma_coeff,Finset.sum_range_succ,Finset.sum_range_zero]
  rw [summand_vanish 2 1 1 (by norm_num)]
  norm_num [summand,ratio,denominator,coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply,unitInv_constant,map_ofNat]

theorem a380680_coeff_two : coeff (R := ℤ) 2 A380680=6 := by
  have hq := congrArg (coeff (R := ℤ) 1) (ratio_quotient (2 : PowerSeries ℤ) 0)
  have h0 : constantCoeff (R := ℤ) (ratio (2 : PowerSeries ℤ) 0)=2 := by
    simp [ratio,denominator,unitInv_constant,map_ofNat]
  simp only [coeff_one_mul,denominator_constant,h0] at hq
  have hden : coeff (R := ℤ) 1 (denominator (2 : PowerSeries ℤ) 0)= -2 := by
    norm_num [denominator,coeff_succ_X_mul,map_ofNat]
  rw [hden] at hq
  have hc2 : coeff (R := ℤ) 1 (2 : PowerSeries ℤ)=0 := by
    calc
      coeff (R := ℤ) 1 (2 : PowerSeries ℤ)=coeff (R := ℤ) 1 (1+1 : PowerSeries ℤ) := by congr 1; ring
      _=0 := by rw [map_add]; norm_num
  have hq1 : coeff (R := ℤ) 1 (ratio (2 : PowerSeries ℤ) 0)=3 := by
    norm_num [hc2] at hq
    omega
  rw [A380680,step]
  simp only [two_mul,map_add,sigma_coeff,Finset.sum_range_succ,Finset.sum_range_zero]
  rw [summand_vanish 2 1 2 (by norm_num),summand_vanish 2 2 2 (by norm_num)]
  norm_num [summand,coeff_succ_X_mul,hq1]

/-- Refutes the square-index iff stated in the retrieved A380680 comment. -/
theorem a380680_literal_conjecture_false :
    ¬(∀ n : ℕ, 0<n → ((coeff (R := ℤ) n A380680 : ZMod 4)=2 ↔ ∃ j : ℕ, n=j^2)) := by
  intro h
  have hh := (h 1 (by omega)).2 ⟨1,by norm_num⟩
  rw [a380680_coeff_one] at hh
  exact (by decide : (4 : ZMod 4)≠2) hh

/-- The nonsquare divisibility clause also fails: a(2)=6. -/
theorem a380680_nonsquare_clause_false :
    ¬(∀ n : ℕ, 0<n → (¬∃ j : ℕ, n=j^2) → (4 : ℤ) ∣ coeff (R := ℤ) n A380680) := by
  intro h
  have hn : ¬∃ j : ℕ, 2=j^2 := by
    rintro ⟨j,hj⟩
    have : j≤1 := by nlinarith
    interval_cases j <;> norm_num at hj
  have hh := h 2 (by omega) hn
  rw [a380680_coeff_two] at hh
  norm_num at hh

end

end Families.ThetaRational
