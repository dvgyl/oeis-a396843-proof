module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

/-!
# OEIS A380056: two conjectures about `(exp(x)-1)/cos(2*x)`

The integer sequence is defined by coefficient recursion, proved to have
the literal rational exponential generating function, and reduced modulo
four and five. No divisibility of rational denominators is used modulo a
prime: all modular arguments take place in the integral binomial convolution.

AI disclosure: OpenAI ChatGPT generated these proofs for Dev D. Goyal.
-/

@[expose] public section

namespace Families.ExpCosine

open Finset PowerSeries

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Binomial convolution is multiplication of exponential generating functions. -/
def conv (f g : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ range (n+1), (n.choose k : R) * f k * g (n-k)

/-- The divided-power coefficients of `cos(2*x)`. -/
def cosineCoeff (n : ℕ) : ℤ := if Even n then (-4)^(n/2) else 0

@[simp] theorem cosineCoeff_zero : cosineCoeff 0=1 := by simp [cosineCoeff]

/-- The canonical integral coefficients obtained by division by the constant-one cosine. -/
def a (n : ℕ) : ℤ :=
  if hn : n=0 then 0 else
  1-∑ k : Fin n, (n.choose k : ℤ) * a k * cosineCoeff (n-k)
termination_by n
decreasing_by exact k.isLt

@[simp] theorem a_zero : a 0=0 := by rw [a]; simp

theorem a_rec (n : ℕ) (hn : n≠0) :
    a n=1-∑ k ∈ range n, (n.choose k : ℤ)*a k*cosineCoeff (n-k) := by
  rw [a, dif_neg hn]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : ℤ)*a k*cosineCoeff (n-k)) n

theorem conv_last (f g : ℕ → R) (n : ℕ) (hg : g 0=1) :
    conv f g n=(∑ k ∈ range n, (n.choose k : R)*f k*g (n-k))+f n := by
  simp [conv, sum_range_succ, hg]

theorem a_conv (n : ℕ) :
    conv a cosineCoeff n=if n=0 then 0 else 1 := by
  by_cases hn : n=0
  · subst n; simp [conv]
  · rw [if_neg hn, conv_last a cosineCoeff n cosineCoeff_zero, a_rec n hn]
    ring

theorem conv_unique {c f g : ℕ → R} (hc : c 0=1)
    (h : ∀ n, conv f c n=conv g c n) : f=g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs : (∑ k ∈ range n, (n.choose k : R)*f k*c (n-k))=
        ∑ k ∈ range n, (n.choose k : R)*g k*c (n-k) := by
      apply sum_congr rfl
      intro k hk
      rw [ih k (mem_range.mp hk)]
    have hh := h n
    rw [conv_last f c n hc, conv_last g c n hc, hs] at hh
    exact add_left_cancel hh

theorem map_conv (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (conv f g n)=conv (fun k => φ (f k)) (fun k => φ (g k)) n := by
  simp [conv]

theorem a_convolution_unique (f : ℕ → ℤ)
    (hf : ∀ n, conv f cosineCoeff n=if n=0 then 0 else 1) : f=a := by
  apply conv_unique cosineCoeff_zero
  intro n
  rw [hf n, a_conv n]

theorem cosine_mod_four (n : ℕ) :
    (cosineCoeff n : ZMod 4)=if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n; simp
  · rw [if_neg hn]
    by_cases he : Even n
    · obtain ⟨k,hk⟩ := he
      subst n
      have hk0 : k≠0 := by intro hk; apply hn; simp [hk]
      simp [cosineCoeff, show Even (k+k) from ⟨k,rfl⟩,
        show (k+k)/2=k by omega, show (-4:ZMod 4)=0 by decide, hk0]
    · simp [cosineCoeff, he]

theorem a380056_mod_four (n : ℕ) (hn : 0<n) : (a n : ZMod 4)=1 := by
  have h := congrArg (Int.castRingHom (ZMod 4)) (a_conv n)
  rw [map_conv] at h
  simp only [show n≠0 by omega, if_false, map_one] at h
  rw [conv_last] at h
  · have hs : (∑ k ∈ range n, (n.choose k : ZMod 4) * (a k : ZMod 4) *
        (cosineCoeff (n-k) : ZMod 4))=0 := by
      apply sum_eq_zero
      intro k hk
      have hkn : n-k≠0 := by have := mem_range.mp hk; omega
      rw [cosine_mod_four, if_neg hkn, mul_zero]
    change (∑ k ∈ range n, (n.choose k : ZMod 4) * (a k : ZMod 4) *
      (cosineCoeff (n-k) : ZMod 4))+(a n : ZMod 4)=1 at h
    simpa [hs] using h
  · simp

theorem cosine_mod_five (n : ℕ) :
    (cosineCoeff n : ZMod 5)=3*(1+4^n) := by
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨k,hk⟩ := he
    subst n
    rw [show k+k=2*k by omega]
    simp [cosineCoeff, Even.mul_left, pow_mul, show (4:ZMod 5)^2=1 by decide,
      show (-4:ZMod 5)=1 by decide]
    decide
  · obtain ⟨k,hk⟩ := ho
    subst n
    simp [cosineCoeff, pow_add, pow_mul, show (4:ZMod 5)^2=1 by decide]
    decide

theorem conv_exp (s t : R) (n : ℕ) :
    conv (fun k => s^k) (fun k => t^k) n=(s+t)^n := by
  rw [conv, add_pow]
  apply sum_congr rfl
  intro k hk
  ring

def modFiveCandidate (n : ℕ) : ZMod 5 := 2*2^n+3*4^n

theorem modFiveCandidate_conv (n : ℕ) :
    conv modFiveCandidate (fun k => (cosineCoeff k : ZMod 5)) n=
      if n=0 then 0 else 1 := by
  have hc : (fun k => (cosineCoeff k : ZMod 5))=
      (fun k => 3*((1:ZMod 5)^k+4^k)) := by
    funext k; simp [cosine_mod_five]
  rw [hc]
  have hh : conv modFiveCandidate (fun k => 3*((1:ZMod 5)^k+4^k)) n=
      6*conv (fun k => (2:ZMod 5)^k) (fun k => (1:ZMod 5)^k) n+
      6*conv (fun k => (2:ZMod 5)^k) (fun k => (4:ZMod 5)^k) n+
      9*conv (fun k => (4:ZMod 5)^k) (fun k => (1:ZMod 5)^k) n+
      9*conv (fun k => (4:ZMod 5)^k) (fun k => (4:ZMod 5)^k) n := by
    simp only [conv, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [modFiveCandidate]
    ring
  rw [hh]
  simp only [conv_exp]
  rw [show (2+1:ZMod 5)=3 by decide, show (2+4:ZMod 5)=1 by decide,
    show (4+1:ZMod 5)=0 by decide, show (4+4:ZMod 5)=3 by decide,
    show (6:ZMod 5)=1 by decide, show (9:ZMod 5)=4 by decide]
  simp only [one_mul, one_pow]
  calc
    3^n+1+4*0^n+4*3^n=(5:ZMod 5)*3^n+1+4*0^n := by ring
    _=1+4*(0:ZMod 5)^n := by rw [show (5:ZMod 5)=0 by decide]; ring
    _=if n=0 then 0 else 1 := by
      by_cases hn : n=0
      · simp only [hn, pow_zero, mul_one, if_pos rfl]
        decide
      · simp [hn, zero_pow hn]

theorem a380056_mod_five_formula (n : ℕ) :
    (a n : ZMod 5)=2*2^n+3*4^n := by
  have he : (fun k => (a k : ZMod 5))=modFiveCandidate := by
    apply conv_unique (c:=fun k => (cosineCoeff k : ZMod 5)) (by simp)
    intro k
    have hh := congrArg (Int.castRingHom (ZMod 5)) (a_conv k)
    rw [map_conv] at hh
    rw [modFiveCandidate_conv]
    by_cases hk : k=0
    · simpa [hk] using hh
    · simpa [hk] using hh
  exact congrFun he n

theorem a380056_mod_five_period (n : ℕ) :
    (a (n+4) : ZMod 5)=(a n : ZMod 5) := by
  simp [a380056_mod_five_formula, pow_add,
    show (2:ZMod 5)^4=1 by decide, show (4:ZMod 5)^4=1 by decide]

theorem a380056_mod_five_four_mul (n : ℕ) : (a (4*n) : ZMod 5)=0 := by
  rw [a380056_mod_five_formula]
  simp only [pow_mul, show (2:ZMod 5)^4=1 by decide,
    show (4:ZMod 5)^4=1 by decide, one_pow, mul_one]
  decide

theorem a380056_five_dvd (n : ℕ) : (5:ℤ) ∣ a (4*n) := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (a380056_mod_five_four_mul n)

theorem pow_mod_four {b : ZMod 5} (hb : b^4=1) (n : ℕ) : b^n=b^(n%4) := by
  calc
    b^n=b^(n%4+4*(n/4)) := by rw [Nat.mod_add_div]
    _=b^(n%4) := by simp [pow_add, pow_mul, hb]

theorem a380056_mod_five_residue (n : ℕ) :
    (a n : ZMod 5)=if n%4=0 then 0 else if n%4=3 then 3 else 1 := by
  rw [a380056_mod_five_formula,
    pow_mod_four (by decide : (2:ZMod 5)^4=1),
    pow_mod_four (by decide : (4:ZMod 5)^4=1)]
  have hr := Nat.mod_lt n (by decide : 0<4)
  have cases : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases cases with h|h|h|h <;> rw [h] <;> decide

theorem a380056_five_dvd_iff (n : ℕ) : (5:ℤ) ∣ a n ↔ 4 ∣ n := by
  have hi : (a n : ZMod 5)=0 ↔ (5:ℤ) ∣ a n := by
    simpa using ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 5
  rw [← hi, a380056_mod_five_residue,
    Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> simp_all [show (3:ZMod 5)≠0 by decide, show (1:ZMod 5)≠0 by decide]

/-- The rational exponential generating function of an integer sequence. -/
def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ)/(n.factorial : ℚ)

theorem egf_mul (f g : ℕ → ℤ) : egf f * egf g=egf (conv f g) := by
  ext n
  simp only [egf, coeff_mul, coeff_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, conv]
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hk' : k≤n := by exact Nat.le_of_lt_succ (mem_range.mp hk)
  have hf : (n.choose k : ℚ)*(k.factorial : ℚ)*((n-k).factorial : ℚ)=
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have h0 : (n.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h1 : (k.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((n-k).factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
  field_simp
  linear_combination -(f k : ℚ)*(g (n-k) : ℚ)*hf

theorem cosine_egf_eq : egf cosineCoeff=PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ) := by
  ext n
  simp only [egf, coeff_mk, coeff_rescale, PowerSeries.cos, coeff_mk]
  by_cases he : Even n
  · obtain ⟨k,hk⟩ := he
    subst n
    simp only [cosineCoeff, show Even (k+k) from ⟨k,rfl⟩, if_true,
      show (k+k)/2=k by omega, Int.cast_pow, Int.cast_neg, Int.cast_ofNat]
    change (-4:ℚ)^k / ((k+k).factorial:ℚ)=
      2^(k+k)*((-1:ℚ)^k/((k+k).factorial:ℚ))
    rw [show k+k=2*k by omega, pow_mul, ← mul_div_assoc, ← mul_pow]
    norm_num
  · simp [cosineCoeff, he]

/-- The actual series, with integral divided-power coefficients. -/
def A : PowerSeries ℚ := egf a

theorem A_coeff (n : ℕ) : coeff (R := ℚ) n A=(a n : ℚ)/(n.factorial : ℚ) := by
  simp [A, egf]

theorem A_integral_coefficients (n : ℕ) :
    (n.factorial : ℚ)*coeff (R := ℚ) n A=(a n : ℚ) := by
  rw [A_coeff]
  have hn : (n.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem cosine_constantCoeff :
    constantCoeff (R := ℚ) (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ))=1 := by
  rw [← cosine_egf_eq, ← coeff_zero_eq_constantCoeff_apply]
  simp [egf]

/-- The literal source equation, with the denominator cleared by a proven unit. -/
theorem a380056_source_equation :
    A * PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)=PowerSeries.exp ℚ-1 := by
  rw [A, ← cosine_egf_eq, egf_mul]
  ext n
  by_cases hn : n=0
  · subst n; simp [egf, a_conv]
  · simp [egf, a_conv, hn]

/-- The literal quotient using the multiplicative inverse of `cos(2*x)`. -/
theorem a380056_source_quotient :
    A=(PowerSeries.exp ℚ-1)*
      (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ))⁻¹ := by
  have hi := PowerSeries.mul_invOfUnit
    (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)) 1 cosine_constantCoeff
  rw [PowerSeries.invOfUnit_eq' _ 1 cosine_constantCoeff] at hi
  calc
    A=A*(PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)*
      (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ))⁻¹) := by rw [hi, mul_one]
    _=(PowerSeries.exp ℚ-1)*
      (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ))⁻¹ := by
        rw [← mul_assoc, a380056_source_equation]

theorem a380056_source_unique (F : PowerSeries ℚ)
    (hF : F*PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)=PowerSeries.exp ℚ-1) : F=A := by
  have h := congrArg (fun G => G *
    PowerSeries.invOfUnit (PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)) 1)
    (hF.trans a380056_source_equation.symm)
  simpa only [mul_assoc, PowerSeries.mul_invOfUnit _ 1 cosine_constantCoeff,
    mul_one] using h

theorem a380056_source_existence_uniqueness :
    ∃! F : PowerSeries ℚ,
      F*PowerSeries.rescale (2:ℚ) (PowerSeries.cos ℚ)=PowerSeries.exp ℚ-1 := by
  exact ⟨A,a380056_source_equation,fun F hF => a380056_source_unique F hF⟩

end

end Families.ExpCosine
