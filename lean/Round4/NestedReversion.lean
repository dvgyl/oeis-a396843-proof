import Hanna.Related.ScaledParity

/-!
# OEIS A195194: parity of infinite nested reversion

The nested expression is defined by its unique normalized family of tails.
Every inverse is a genuine formal compositional inverse.

AI disclosure: OpenAI ChatGPT generated this proof for Dev D. Goyal.
Review status: see AUTHORSHIP.md.
-/

namespace Round4.NestedReversion

open PowerSeries Hanna.Series

noncomputable section

variable {R : Type*} [CommRing R]

/-- The polynomial expression equivalent to the nested inverse equation. -/
def branch (w : R) (A B : PowerSeries R) : PowerSeries R :=
  X + C R w * A * compose B A

theorem branch_normalized (w : R) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B) : Normalized (branch w A B) := by
  apply (normalized_iff_X_sq_dvd _).mpr
  have hc := hB.compose hA
  have hp : (X : PowerSeries R)^2 ∣ A * compose B A := by
    simpa using X_pow_dvd_product
      (show (X : PowerSeries R)^1 ∣ A by simpa using hA.X_dvd)
      (show (X : PowerSeries R)^1 ∣ compose B A by simpa using hc.X_dvd)
  simpa [branch, mul_assoc] using dvd_mul_of_dvd_right hp (C R w)

theorem compose_congr (n : ℕ) {A A' B B' : PowerSeries R}
    (hA : Normalized A) (hA' : Normalized A')
    (hAA : (X : PowerSeries R)^n ∣ A-A')
    (hBB : (X : PowerSeries R)^n ∣ B-B') :
    (X : PowerSeries R)^n ∣ compose B A-compose B' A' := by
  have hi := compose_inner_congr B A A' n hA.constantCoeff hA'.constantCoeff hAA
  have ho := compose_outer_vanish (B-B') A' n 1 hA'.constantCoeff hBB
    (by simpa using hA'.X_dvd)
  rw [one_mul, compose_sub _ _ _ hA'.constantCoeff] at ho
  convert dvd_add hi ho using 1
  ring

theorem branch_contraction (w : R) (n : ℕ) {A A' B B' : PowerSeries R}
    (hA : Normalized A) (hA' : Normalized A') (hB : Normalized B)
    (hAA : (X : PowerSeries R)^n ∣ A-A')
    (hBB : (X : PowerSeries R)^n ∣ B-B') :
    (X : PowerSeries R)^(n+1) ∣ branch w A B-branch w A' B' := by
  have hc : (X : PowerSeries R)^1 ∣ compose B A := by
    simpa using (hB.compose hA).X_dvd
  have hp := X_pow_dvd_product hAA hc
  have hq := X_pow_dvd_product
    (compose_congr n hA hA' hAA hBB)
    (show (X : PowerSeries R)^1 ∣ A' by simpa using hA'.X_dvd)
  have hs := dvd_mul_of_dvd_right (dvd_add hp hq) (C R w)
  convert hs using 1
  unfold branch
  ring

def step (w : R) (s : R →+* R) (A : PowerSeries R) : PowerSeries R :=
  branch w A (PowerSeries.map s A)

theorem step_normalized (w : R) (s : R →+* R) {A : PowerSeries R}
    (hA : Normalized A) : Normalized (step w s A) :=
  branch_normalized w hA (hA.map s)

theorem step_contraction (w : R) (s : R →+* R) (n : ℕ)
    {A B : PowerSeries R} (hA : Normalized A) (hB : Normalized B)
    (hAB : (X : PowerSeries R)^n ∣ A-B) :
    (X : PowerSeries R)^(n+1) ∣ step w s A-step w s B := by
  apply branch_contraction w n hA hB (hA.map s) hAB
  obtain ⟨D, hD⟩ := hAB
  refine ⟨PowerSeries.map s D, ?_⟩
  simpa only [map_sub, map_mul, map_pow, PowerSeries.map_X] using
    congrArg (PowerSeries.map s) hD

theorem equation_triangular (w : R) (s : R →+* R) :
    Triangular (fun a n => coeff R (n+2) (ofTail a-step w s (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := step_contraction w s (n+2) (normalized_ofTail a) (normalized_ofTail b) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simp only [map_sub, coeff_ofTail] at hc ⊢
  linear_combination -hc

theorem fixed_exists (w : R) (s : R →+* R) :
    ∃ A : PowerSeries R, Normalized A ∧ A=step w s A := by
  let op := fun a n => coeff R (n+2) (ofTail a-step w s (ofTail a))
  let a := triangularCoeffs op (fun _ => 0)
  have ha := triangularCoeffs_spec op (equation_triangular w s) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  have hs := step_normalized w s (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · exact (normalized_ofTail a).1.trans hs.1.symm
  · exact (normalized_ofTail a).2.trans hs.2.symm
  · have hc := congrFun ha n
    change coeff R (n+2) (ofTail a-step w s (ofTail a))=0 at hc
    simpa only [map_sub, sub_eq_zero, Nat.succ_eq_add_one, Nat.add_assoc] using hc

theorem fixed_unique (w : R) (s : R →+* R) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (heA : A=step w s A) (heB : B=step w s B) : A=B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := (agree_iff_X_pow_dvd_sub n A B).mp ih
    have hp := step_contraction w s n hA hB hd
    have hc := X_pow_dvd_iff.mp hp n (by omega)
    rw [← heA, ← heB, map_sub, sub_eq_zero] at hc
    exact hc

def fixed (w : R) (s : R →+* R) : PowerSeries R :=
  (fixed_exists w s).choose

theorem fixed_normalized (w : R) (s : R →+* R) : Normalized (fixed w s) :=
  (fixed_exists w s).choose_spec.1

theorem fixed_equation (w : R) (s : R →+* R) : fixed w s=step w s (fixed w s) :=
  (fixed_exists w s).choose_spec.2

def shift : (ℕ → R) →+* (ℕ → R) where
  toFun a j := a (j+1)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def evaluate (j : ℕ) : (ℕ → R) →+* R where
  toFun a := a j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Arbitrary weights give a canonical infinite family of normalized tails. -/
def tail (w : ℕ → R) (j : ℕ) : PowerSeries R :=
  PowerSeries.map (evaluate j) (fixed w shift)

theorem tail_normalized (w : ℕ → R) (j : ℕ) : Normalized (tail w j) :=
  (fixed_normalized w shift).map (evaluate j)

theorem tail_equation (w : ℕ → R) (j : ℕ) :
    tail w j=branch (w j) (tail w j) (tail w (j+1)) := by
  have he := congrArg (PowerSeries.map (evaluate (R:=R) j)) (fixed_equation w shift)
  have hshift : PowerSeries.map (evaluate (R:=R) j)
      (PowerSeries.map shift (fixed w shift))=tail w (j+1) := by
    ext n
    simp only [tail, coeff_map]
    rfl
  simpa only [step, branch, map_add, map_mul, PowerSeries.map_X, PowerSeries.map_C,
    map_compose _ _ _ (fixed_normalized w shift).constantCoeff, hshift,
    show evaluate (R:=R) j w=w j from rfl] using he

/-- The family is uniquely determined, with no unspecified boundary at infinity. -/
theorem family_unique (w : ℕ → R) {F G : ℕ → PowerSeries R}
    (hF : ∀ j, Normalized (F j)) (hG : ∀ j, Normalized (G j))
    (heF : ∀ j, F j=branch (w j) (F j) (F (j+1)))
    (heG : ∀ j, G j=branch (w j) (G j) (G (j+1))) : F=G := by
  have hc : ∀ n j, coeff R n (F j)=coeff R n (G j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j
      have h1 : (X : PowerSeries R)^n ∣ F j-G j :=
        (agree_iff_X_pow_dvd_sub _ _ _).mp (fun k hk => ih k hk j)
      have h2 : (X : PowerSeries R)^n ∣ F (j+1)-G (j+1) :=
        (agree_iff_X_pow_dvd_sub _ _ _).mp (fun k hk => ih k hk (j+1))
      have hp := branch_contraction (w j) n (hF j) (hG j) (hF (j+1)) h1 h2
      rw [← heF j, ← heG j] at hp
      exact sub_eq_zero.mp (by simpa only [map_sub] using X_pow_dvd_iff.mp hp n (by omega))
  funext j
  ext n
  exact hc n j

theorem family_existence_uniqueness (w : ℕ → R) :
    ∃! F : ℕ → PowerSeries R,
      (∀ j, Normalized (F j)) ∧ (∀ j, F j=branch (w j) (F j) (F (j+1))) := by
  exact ⟨tail w, ⟨tail_normalized w, tail_equation w⟩,
    fun F hF => family_unique w hF.1 (tail_normalized w) hF.2 (tail_equation w)⟩

/-- The expression to be reverted at one level of the nesting. -/
def pre (w : R) (B : PowerSeries R) : PowerSeries R := X-C R w*X*B

theorem pre_normalized (w : R) {B : PowerSeries R} (hB : Normalized B) :
    Normalized (pre w B) := by
  apply (normalized_iff_X_sq_dvd _).mpr
  have hp : (X : PowerSeries R)^2 ∣ X*B := by
    simpa using X_pow_dvd_product (dvd_refl ((X : PowerSeries R)^1))
      (show (X : PowerSeries R)^1 ∣ B by simpa using hB.X_dvd)
  have hm := dvd_neg.mpr (dvd_mul_of_dvd_right hp (C R w))
  simpa [pre, mul_assoc] using hm

theorem branch_iff_inverse_equation (w : R) {A B : PowerSeries R}
    (hA : Normalized A) :
    A=branch w A B ↔ compose (pre w B) A=X := by
  rw [pre, compose_sub _ _ _ hA.constantCoeff,
    compose_mul _ _ _ hA.constantCoeff, compose_mul _ _ _ hA.constantCoeff,
    compose_C _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff]
  unfold branch
  constructor <;> intro h <;> linear_combination h

theorem tail_right_inverse (w : ℕ → R) (j : ℕ) :
    compose (pre (w j) (tail w (j+1))) (tail w j)=X :=
  (branch_iff_inverse_equation (w j) (tail_normalized w j)).mp (tail_equation w j)

theorem tail_left_inverse (w : ℕ → R) (j : ℕ) :
    compose (tail w j) (pre (w j) (tail w (j+1)))=X :=
  left_inverse_of_right_inverse (tail_normalized w j) (tail_right_inverse w j)

theorem tail_is_inverse (w : ℕ → R) (j : ℕ) :
    tail w j=inverse (pre (w j) (tail w (j+1)))
      (pre_normalized (w j) (tail_normalized w (j+1))) := by
  apply inverse_unique (pre_normalized (w j) (tail_normalized w (j+1)))
    (inverse_normalized _ _) (tail_left_inverse w j) (compose_inverse_right _ _)

/-- Existence and uniqueness stated in terms of the actual two-sided inverses. -/
theorem source_existence_uniqueness (w : ℕ → R) :
    ∃! F : ℕ → PowerSeries R,
      (∀ j, Normalized (F j)) ∧ (∀ j,
        compose (pre (w j) (F (j+1))) (F j)=X ∧
        compose (F j) (pre (w j) (F (j+1)))=X) := by
  refine ⟨tail w, ⟨tail_normalized w, fun j => ⟨tail_right_inverse w j,
    tail_left_inverse w j⟩⟩, ?_⟩
  intro F hF
  apply family_unique w hF.1 (tail_normalized w) _ (tail_equation w)
  intro j
  exact (branch_iff_inverse_equation (w j) (hF.1 j)).mpr (hF.2 j).1

theorem inverse_congr (n : ℕ) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (hAB : (X : PowerSeries R)^n ∣ A-B) :
    (X : PowerSeries R)^n ∣ inverse A hA-inverse B hB := by
  let BI := inverse B hB
  have hBI : Normalized BI := inverse_normalized B hB
  have houter := compose_outer_vanish (A-B) BI n 1 hBI.constantCoeff hAB
    (show (X : PowerSeries R)^1 ∣ BI by simpa using hBI.X_dvd)
  rw [one_mul, compose_sub _ _ _ hBI.constantCoeff] at houter
  have hBInv : compose B BI=X := compose_inverse_right B hB
  rw [hBInv] at houter
  have hinner := compose_inner_congr (inverse A hA) (compose A BI) X n
    (hA.compose hBI).constantCoeff (by simp) houter
  rw [← compose_assoc _ _ _ hA.constantCoeff hBI.constantCoeff,
    compose_inverse_left, compose_X_left _ hBI.constantCoeff, compose_X_right] at hinner
  simpa only [neg_sub] using dvd_neg.mpr hinner

theorem pre_contraction (w : R) (n : ℕ) {A B : PowerSeries R}
    (hAB : (X : PowerSeries R)^n ∣ A-B) :
    (X : PowerSeries R)^(n+1) ∣ pre w A-pre w B := by
  have hp := X_pow_dvd_product hAB (dvd_refl ((X : PowerSeries R)^1))
  have hm := dvd_mul_of_dvd_right hp (-C R w)
  convert hm using 1
  unfold pre
  ring

/-- Finite nests terminated by `X`; the accompanying proof guarantees reversion. -/
def approximationPair (w : ℕ → R) : ℕ → ℕ → {A : PowerSeries R // Normalized A}
  | 0, _ => ⟨X, normalized_X⟩
  | d+1, j =>
    let B := approximationPair w d (j+1)
    ⟨inverse (pre (w j) B.val) (pre_normalized (w j) B.property),
      inverse_normalized _ _⟩

def approximation (w : ℕ → R) (d j : ℕ) : PowerSeries R :=
  (approximationPair w d j).val

theorem approximation_normalized (w : ℕ → R) (d j : ℕ) :
    Normalized (approximation w d j) := (approximationPair w d j).property

@[simp] theorem approximation_zero (w : ℕ → R) (j : ℕ) : approximation w 0 j=X := rfl

theorem approximation_succ (w : ℕ → R) (d j : ℕ) :
    approximation w (d+1) j=inverse (pre (w j) (approximation w d (j+1)))
      (pre_normalized (w j) (approximation_normalized w d (j+1))) := rfl

/-- Each further inverse fixes one more coefficient, independently of later tails. -/
theorem approximation_agrees (w : ℕ → R) (d j : ℕ) :
    (X : PowerSeries R)^(d+2) ∣ approximation w d j-tail w j := by
  induction d generalizing j with
  | zero =>
    have ht := (normalized_iff_X_sq_dvd _).mp (tail_normalized w j)
    simpa only [approximation_zero, Nat.zero_add, neg_sub] using dvd_neg.mpr ht
  | succ d ih =>
    have hp := pre_contraction (w j) (d+2) (ih (j+1))
    have hi := inverse_congr (d+2+1)
      (pre_normalized (w j) (approximation_normalized w d (j+1)))
      (pre_normalized (w j) (tail_normalized w (j+1))) hp
    rw [← approximation_succ, ← tail_is_inverse] at hi
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
      show 1+2=2+1 from rfl] using hi

variable {S : Type*} [CommRing S]

theorem map_tail (f : R →+* S) (w : ℕ → R) (j : ℕ) :
    PowerSeries.map f (tail w j)=tail (fun k => f (w k)) j := by
  have he : (fun k => PowerSeries.map f (tail w k))=tail (fun k => f (w k)) := by
    apply family_unique (fun k => f (w k))
      (fun k => (tail_normalized w k).map f) (tail_normalized _) _ (tail_equation _)
    intro k
    have h := congrArg (PowerSeries.map f) (tail_equation w k)
    simpa only [branch, map_add, map_mul, PowerSeries.map_X, PowerSeries.map_C,
      map_compose _ _ _ (tail_normalized w k).constantCoeff] using h
  exact congrFun he j

theorem tail_of_zero_weight (w : ℕ → R) (j : ℕ) (hw : w j=0) : tail w j=X := by
  simpa only [branch, hw, map_zero, zero_mul, add_zero] using tail_equation w j

theorem tail_quadratic_of_next_zero (w : ℕ → R) (j : ℕ)
    (hw : w j=1) (hn : w (j+1)=0) : tail w j-(tail w j)^2=X := by
  have he := tail_equation w j
  rw [branch, hw, map_one, one_mul, tail_of_zero_weight w (j+1) hn,
    compose_X_left _ (tail_normalized w j).constantCoeff] at he
  linear_combination he

/-- The weight at tail `j` is `j+1`, exactly as in the source's nesting. -/
def weights (R : Type*) [CommRing R] : ℕ → R := fun j => (j+1 : ℕ)

def A : PowerSeries ℤ := tail (weights ℤ) 0

def a (n : ℕ) : ℤ := coeff ℤ n A

theorem A_normalized : Normalized A := tail_normalized (weights ℤ) 0

theorem A_source :
    compose (X-X*tail (weights ℤ) 1) A=X := by
  have he := tail_right_inverse (weights ℤ) 0
  change compose (X-C ℤ 1*X*tail (weights ℤ) 1) A=X at he
  simpa only [map_one, one_mul] using he

theorem A_source_left :
    compose A (X-X*tail (weights ℤ) 1)=X := by
  exact left_inverse_of_right_inverse A_normalized A_source

theorem A_mod_two_quadratic :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A-
      (PowerSeries.map (Int.castRingHom (ZMod 2)) A)^2=X := by
  unfold A
  rw [map_tail]
  apply tail_quadratic_of_next_zero _ 0
  · norm_num [weights]
  · change (2 : ZMod 2)=0
    decide

/-- The all-index parity conjecture for OEIS A195194, including the zero index. -/
theorem a195194_parity (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n=2^k := by
  have hc : ((a n : ZMod 2)=1) ↔ Odd (a n) := by
    simpa [Int.odd_iff] using ZMod.intCast_eq_intCast_iff' (a n) 1 2
  rw [← hc]
  change (Int.castRingHom (ZMod 2)) (coeff ℤ n A)=1 ↔ _
  rw [← coeff_map]
  exact Hanna.Related.ScaledInverse.quadratic_coeff_one_iff_power_two _
    (A_normalized.map _) A_mod_two_quadratic n

end
end Round4.NestedReversion
