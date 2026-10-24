import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# A397346: an exponential recurrence modulo eight

AI-generated mathematical proof and formalization for Dev D. Goyal.
The canonical integer sequence is constructed from the source recurrence,
with exact division and all index restrictions made explicit.
-/

namespace Families.ExpRecurrence

open scoped BigOperators

/-- `u n` is the integral quotient `a(n+2)/(n+2)`. -/
def u : ℕ → ℤ
  | 0 => 2
  | n + 1 => (2 * (n+3 : ℤ) * (n+2) - 1) * u n +
      ∑ i : Fin n, (2 * (i.val+2 : ℤ)^2 - 1) * (n+1-i.val : ℤ) *
        u i.val * u (n-1-i.val)
termination_by n => n
decreasing_by all_goals omega

@[simp] theorem u_zero : u 0 = 2 := by rw [u]

theorem u_succ (n : ℕ) :
    u (n+1) = (2 * (n+3 : ℤ) * (n+2) - 1) * u n +
      ∑ i : Fin n, (2 * (i.val+2 : ℤ)^2 - 1) * (n+1-i.val : ℤ) *
        u i.val * u (n-1-i.val) := by rw [u]

def residue (n : ℕ) : ZMod 8 := if n % 4 = 1 then 6 else 2

theorem residue_product (n m : ℕ) : residue n * residue m = 4 := by
  unfold residue
  split_ifs <;> decide

theorem four_sum (n : ℕ) :
    (∑ i : Fin n, (4 : ZMod 8) * ((n : ZMod 8)+1-(i.val : ZMod 8))) =
      2*(n : ZMod 8)*((n : ZMod 8)+3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    have he (i : Fin n) : (4 : ZMod 8) * ((n : ZMod 8)+1+1-(i.val : ZMod 8)) =
        4*((n : ZMod 8)+1-(i.val : ZMod 8))+4 := by ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf

theorem residue_step (n : ℕ) :
    (2*((n : ZMod 8)+3)*((n : ZMod 8)+2)-1)*residue n +
      2*(n : ZMod 8)*((n : ZMod 8)+3) = residue (n+1) := by
  have hlt := Nat.mod_lt n (by decide : 0<4)
  have he : n = n % 4 + 4 * (n / 4) := by omega
  generalize h : n % 4 = r at hlt he
  interval_cases r <;> rw [he] <;>
    norm_num [residue, Nat.add_mod, Nat.mul_mod] <;> ring_nf <;> reduce_mod_char

theorem u_mod_eight (n : ℕ) : (u n : ZMod 8) = residue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [residue]
    | succ n =>
      rw [u_succ]
      push_cast
      rw [ih n (by omega)]
      have hs :
          (∑ i : Fin n, (2*((i.val : ZMod 8)+2)^2-1)*
            ((n : ZMod 8)+1-(i.val : ZMod 8))*(u i.val : ZMod 8)*
              (u (n-1-i.val) : ZMod 8)) =
            ∑ i : Fin n, (4 : ZMod 8)*((n : ZMod 8)+1-(i.val : ZMod 8)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i.val (by omega), ih (n-1-i.val) (by omega)]
        calc
          _ = (2*((i.val : ZMod 8)+2)^2-1)*((n : ZMod 8)+1-(i.val : ZMod 8))*
              (residue i.val * residue (n-1-i.val)) := by ring
          _ = _ := by rw [residue_product]; ring_nf; reduce_mod_char; ring_nf; reduce_mod_char
      rw [hs, four_sum]
      exact residue_step n

/-- Integral quotients, with the auxiliary zero value excluded from source ranges. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => u n

/-- The canonical integer sequence, including the source's constant coefficient. -/
def a (n : ℕ) : ℤ := if n=0 then 1 else n*b n

@[simp] theorem b_zero : b 0 = 0 := rfl
@[simp] theorem b_one : b 1 = 1 := rfl
@[simp] theorem b_add_two (n : ℕ) : b (n+2) = u n := rfl
@[simp] theorem a_zero : a 0 = 1 := by simp [a]
@[simp] theorem a_one : a 1 = 1 := by simp [a]

theorem a_positive (n : ℕ) (hn : 0<n) : a n = (n : ℤ)*b n := by
  simp [a, Nat.ne_of_gt hn]

theorem a_add_two (n : ℕ) : a (n+2) = (n+2 : ℤ)*u n := by
  simp [a]

theorem index_dvd_a (n : ℕ) (hn : 0<n) : (n : ℤ) ∣ a n := by
  rw [a_positive n hn]
  exact dvd_mul_right _ _

theorem b_recurrence (n : ℕ) :
    b (n+2) = 2*(n+1 : ℤ)*b (n+1) +
      ∑ i : Fin n, (2*(i.val+2 : ℤ)^2-1)*(n-i.val : ℤ)*b (i.val+2)*b (n-i.val) := by
  cases n with
  | zero => norm_num [b, u]
  | succ n =>
    rw [show n+1+2=(n+1)+2 by omega, b_add_two, u_succ, Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    have hs :
        (∑ i : Fin n, (2*(i.val+2 : ℤ)^2-1)*(n+1-i.val : ℤ)*
          b (i.val+2)*b (n+1-i.val)) =
        ∑ i : Fin n, (2*(i.val+2 : ℤ)^2-1)*(n+1-i.val : ℤ)*
          u i.val*u (n-1-i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : n+1-i.val=(n-1-i.val)+2 := by omega
      rw [he, b_add_two, b_add_two]
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [hs]
    simp only [show n+1-n=1 by omega, b_one, b_add_two]
    ring

/-- The finite rational recurrence printed as formula (7) in OEIS A397346. -/
def Source (s : ℕ → ℚ) : Prop :=
  s 0=1 ∧ s 1=1 ∧ ∀ n : ℕ,
    s (n+2) = 2*(n+2 : ℚ)*s (n+1) +
      (n+2 : ℚ) * ∑ i : Fin n,
        (2*(i.val+2 : ℚ)^2-1)/(i.val+2 : ℚ)*s (i.val+2)*s (n-i.val)

theorem a_source : Source (fun n => (a n : ℚ)) := by
  refine ⟨by simp, by simp, ?_⟩
  intro n
  dsimp only
  rw [a_positive (n+2) (by omega), a_positive (n+1) (by omega)]
  have hb := congrArg (fun z : ℤ => (z : ℚ)) (b_recurrence n)
  push_cast at hb ⊢
  rw [hb]
  have hs :
      (∑ i : Fin n, (2*((i.val : ℚ)+2)^2-1)*((n : ℚ)-(i.val : ℚ))*
        (b (i.val+2) : ℚ)*(b (n-i.val) : ℚ)) =
      ∑ i : Fin n, (2*((i.val : ℚ)+2)^2-1)/((i.val : ℚ)+2)*
        (a (i.val+2) : ℚ)*(a (n-i.val) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [a_positive (i.val+2) (by omega), a_positive (n-i.val) (by omega)]
    push_cast
    rw [Nat.cast_sub (by omega : i.val≤n)]
    have hz : (i.val : ℚ)+2≠0 := by positivity
    field_simp
    ring
  rw [hs]
  ring

theorem source_unique {s t : ℕ → ℚ} (hs : Source s) (ht : Source t) : s=t := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | (_ | n)
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · rw [hs.2.2 n, ht.2.2 n, ih (n+1) (by omega)]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      rw [ih (i.val+2) (by omega), ih (n-i.val) (by omega)]

theorem source_existence_uniqueness : ∃! s : ℕ → ℚ, Source s :=
  ⟨(fun n => (a n : ℚ)), a_source, fun _ hs => source_unique hs a_source⟩

/-- Complete residue classification of the integral quotient. -/
theorem b_mod_eight (n : ℕ) (hn : 2≤n) :
    (b n : ZMod 8) = if n%4=3 then 6 else 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2+k=k+2 by omega, b_add_two, u_mod_eight]
  unfold residue
  have he : (k+2)%4=3 ↔ k%4=1 := by omega
  simp only [he]

/-- The original periodic block is indexed from degree two. -/
theorem a397346_block (k : ℕ) :
    (a (4*k+2) : ZMod 8)=4 ∧
    (a (4*k+3) : ZMod 8)=2 ∧
    (a (4*k+4) : ZMod 8)=0 ∧
    (a (4*k+5) : ZMod 8)=2 := by
  have h (r : ℕ) (hr : 2≤r) :
      (a (4*k+r) : ZMod 8) = (4*k+r : ZMod 8)*
        (if (4*k+r)%4=3 then 6 else 2) := by
    rw [a_positive _ (by omega)]
    push_cast
    rw [b_mod_eight _ (by omega)]
  rw [h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega)]
  norm_num [Nat.add_mod, Nat.mul_mod]
  ring_nf
  reduce_mod_char
  trivial

/-- Complete all-index residue classification, with the source lower bound. -/
theorem a397346_residue (n : ℕ) (hn : 2≤n) :
    (a n : ZMod 8) = if n%4=0 then 0 else if n%4=2 then 4 else 2 := by
  rw [a_positive _ (by omega)]
  push_cast
  rw [b_mod_eight _ hn]
  have hlt := Nat.mod_lt n (by decide : 0<4)
  have he : n=n%4+4*(n/4) := by omega
  generalize hr : n%4=r at hlt he ⊢
  interval_cases r <;> norm_num <;> rw [he] <;> push_cast <;>
    ring_nf <;> reduce_mod_char

theorem a_initial_values :
    a 0=1 ∧ a 1=1 ∧ a 2=4 ∧ a 3=66 ∧ a 4=2248 := by
  norm_num [a, b, u, Fin.sum_univ_succ]

/-- The ordinary generating function of the constructed sequence. -/
noncomputable def generatingFunction : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ)

/-- The series occurring inside the exponential in the OEIS definition. -/
noncomputable def exponentSeries : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n=0 then 0 else if n=1 then 1 else
    (2*(n : ℚ)^2-1)/(2*(n : ℚ)^2)*(a n : ℚ)

theorem exponent_derivative_zero :
    PowerSeries.coeff ℚ 0 (PowerSeries.derivative ℚ exponentSeries)=1 := by
  simp [PowerSeries.coeff_derivative, exponentSeries, PowerSeries.coeff_mk]

theorem exponent_derivative_succ (n : ℕ) :
    PowerSeries.coeff ℚ (n+1) (PowerSeries.derivative ℚ exponentSeries) =
      (2*(n+2 : ℚ)^2-1)/(2*(n+2 : ℚ))*(a (n+2) : ℚ) := by
  rw [PowerSeries.coeff_derivative]
  simp only [exponentSeries, PowerSeries.coeff_mk]
  norm_num only [show n+1+1=n+2 by omega, show n+2≠0 by omega,
    show n+2≠1 by omega, if_false, Nat.cast_add, Nat.cast_ofNat]
  have hz : (n : ℚ)+2≠0 := by positivity
  field_simp
  ring

/-- The actual formal differential identity obtained by differentiating the
source exponential equation. No analytic convergence is used. -/
theorem a_differential_equation :
    PowerSeries.derivative ℚ generatingFunction =
      generatingFunction * PowerSeries.derivative ℚ exponentSeries := by
  rw [mul_comm]
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  simp only [generatingFunction, PowerSeries.coeff_mk]
  cases n with
  | zero => simp [exponent_derivative_zero]
  | succ n =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, Nat.sub_zero, exponent_derivative_zero, one_mul,
      Fin.val_succ, Fin.coe_castSucc, Fin.val_last, exponent_derivative_succ,
      Nat.sub_self, a_zero, Int.cast_one, mul_one]
    have hs :
        (∑ i : Fin n,
          (2*(i.val+2 : ℚ)^2-1)/(2*(i.val+2 : ℚ))*(a (i.val+2) : ℚ)*
            (a (n+1-(i.val+1)) : ℚ)) =
        (1/2 : ℚ)*∑ i : Fin n,
          (2*(i.val+2 : ℚ)^2-1)/(i.val+2 : ℚ)*(a (i.val+2) : ℚ)*
            (a (n-i.val) : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show n+1-(i.val+1)=n-i.val by omega]
      have hz : (i.val : ℚ)+2≠0 := by positivity
      field_simp
    rw [hs]
    have hr := a_source.2.2 n
    dsimp only at hr
    rw [show n+1+1=n+2 by omega]
    push_cast at hr ⊢
    generalize hsum : (∑ i : Fin n,
      (2*((i.val : ℚ)+2)^2-1)/((i.val : ℚ)+2)*(a (i.val+2) : ℚ)*
        (a (n-i.val) : ℚ)) = s at hr ⊢
    have hz : (n : ℚ)+2≠0 := by positivity
    field_simp
    nlinarith [hr]

end Families.ExpRecurrence
