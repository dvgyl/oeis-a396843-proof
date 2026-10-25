module

public import Hanna.Series.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# The scaled inverse family A393856--A393859

The source equation is `A(X - X * (A(qX)/q)) = X`.  The quotient is
defined coefficientwise, so no invertibility assumption on `q` occurs.
The construction and its uniqueness hold over every commutative ring.
-/

@[expose] public section

namespace Hanna.Related.ScaledInverse

open PowerSeries Hanna.Series

variable {R : Type*} [CommRing R]

/-- Coefficientwise interpretation of `A(qX)/q`, for a series with zero
constant coefficient.  Its definition makes sense even when `q = 0`. -/
noncomputable def scaleTail (q : R) (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => q ^ (n - 1) * coeff n A)

@[simp] theorem coeff_scaleTail (q : R) (A : PowerSeries R) (n : ℕ) :
    coeff n (scaleTail q A) = q ^ (n - 1) * coeff n A := by
  simp [scaleTail]

theorem scaleTail_normalized (q : R) {A : PowerSeries R} (hA : Normalized A) :
    Normalized (scaleTail q A) := by
  simp [Normalized, hA.1, hA.2]

noncomputable def argument (q : R) (A : PowerSeries R) : PowerSeries R :=
  X - X * scaleTail q A

@[simp] theorem argument_constant (q : R) (A : PowerSeries R) :
    constantCoeff (argument q A) = 0 := by
  simp [argument]

theorem argument_normalized (q : R) {A : PowerSeries R} (hA : Normalized A) :
    Normalized (argument q A) := by
  constructor
  · simp [argument]
  · simp [argument, scaleTail, hA.1]

/-- The exact formal power series equation used in the OEIS entries. -/
def SourceEquation (q : R) (A : PowerSeries R) : Prop :=
  compose A (argument q A) = X

/-- Reversing the compositional inverse equation exposes its triangular
coefficient recursion. -/
noncomputable def core (q : R) (A : PowerSeries R) : PowerSeries R :=
  A - A * compose (scaleTail q A) A

theorem compose_argument (q : R) {A : PowerSeries R} (hA : Normalized A) :
    compose (argument q A) A = core q A := by
  rw [argument, compose_sub _ _ _ hA.constantCoeff,
    compose_mul _ _ _ hA.constantCoeff, compose_X_left _ hA.constantCoeff]
  rfl

theorem source_iff_core (q : R) {A : PowerSeries R} (hA : Normalized A) :
    SourceEquation q A ↔ core q A = X := by
  constructor
  · intro h
    rw [← compose_argument q hA]
    exact left_inverse_of_right_inverse (argument_normalized q hA) h
  · intro h
    apply left_inverse_of_right_inverse hA
    rw [compose_argument q hA]
    exact h

theorem scaleTail_dvd_sub (q : R) (A B : PowerSeries R) (n : ℕ)
    (h : (X : PowerSeries R)^n ∣ B-A) :
    (X : PowerSeries R)^n ∣ scaleTail q B-scaleTail q A := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  have heq := X_pow_dvd_iff.mp h k hk
  simp only [map_sub, sub_eq_zero] at heq
  simp [heq]

theorem core_normalized (q : R) {A : PowerSeries R} (hA : Normalized A) :
    Normalized (core q A) := by
  apply (normalized_iff_X_sq_dvd _).mpr
  have hc := (scaleTail_normalized q hA).compose hA
  have h1 : (X : PowerSeries R)^1 ∣ A := by simpa using hA.X_dvd
  have h2 : (X : PowerSeries R)^1 ∣ compose (scaleTail q A) A := by
    simpa using hc.X_dvd
  have hp : (X : PowerSeries R)^2 ∣ A * compose (scaleTail q A) A := by
    simpa using X_pow_dvd_product h1 h2
  have hh := dvd_sub ((normalized_iff_X_sq_dvd _).mp hA) hp
  convert hh using 1
  unfold core
  ring

theorem core_perturbation (q : R) (A B : PowerSeries R) (n : ℕ)
    (hA : Normalized A) (hB : Normalized B)
    (hAB : (X : PowerSeries R)^n ∣ B-A) :
    (X : PowerSeries R)^(n+1) ∣ core q B-core q A-(B-A) := by
  have hscale := scaleTail_dvd_sub q A B n hAB
  have houter : (X : PowerSeries R)^n ∣
      compose (scaleTail q B) B-compose (scaleTail q A) B := by
    rw [← compose_sub _ _ _ hB.constantCoeff]
    have hb : (X : PowerSeries R)^1 ∣ B := by simpa using hB.X_dvd
    simpa using compose_outer_vanish (scaleTail q B-scaleTail q A) B n 1
      hB.constantCoeff hscale hb
  have hinner := compose_inner_congr (scaleTail q A) B A n
    hB.constantCoeff hA.constantCoeff hAB
  have hcomp : (X : PowerSeries R)^n ∣
      compose (scaleTail q B) B-compose (scaleTail q A) A := by
    convert dvd_add houter hinner using 1
    ring
  have hc := (scaleTail_normalized q hB).compose hB
  have hc1 : (X : PowerSeries R)^1 ∣ compose (scaleTail q B) B := by
    simpa using hc.X_dvd
  have ha1 : (X : PowerSeries R)^1 ∣ A := by simpa using hA.X_dvd
  have hp1 := X_pow_dvd_product hAB hc1
  have hp2 := X_pow_dvd_product hcomp ha1
  have hh := dvd_neg.mpr (dvd_add hp1 hp2)
  convert hh using 1
  unfold core
  ring

theorem core_triangular (q : R) :
    Triangular (fun (a : ℕ → R) n => coeff (n+2) (core q (ofTail a))) := by
  intro n a b hab
  have hd := (agree_iff_X_pow_dvd_sub (n+2) (ofTail a) (ofTail b)).mp
    (ofTail_agree a b n hab)
  have hp := core_perturbation q (ofTail b) (ofTail a) (n+2)
    (normalized_ofTail b) (normalized_ofTail a) hd
  have hc := X_pow_dvd_iff.mp hp (n+2) (by omega)
  simpa only [map_sub, coeff_ofTail, sub_eq_zero] using hc

theorem solution_exists (q : R) :
    ∃ A : PowerSeries R, Normalized A ∧ SourceEquation q A := by
  obtain ⟨a, ha, _⟩ := triangular_existsUnique
    (fun (a : ℕ → R) n => coeff (n+2) (core q (ofTail a))) (core_triangular q) (fun _ => 0)
  refine ⟨ofTail a, normalized_ofTail a, ?_⟩
  apply (source_iff_core q (normalized_ofTail a)).mpr
  have hn := core_normalized q (normalized_ofTail a)
  ext n
  rcases n with _ | (_ | n)
  · simpa using hn.1
  · simpa using hn.2
  · have hc := congrFun ha n
    change coeff (n+2) (core q (ofTail a)) = 0 at hc
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, coeff_X] using hc

theorem solution_unique (q : R) {A B : PowerSeries R}
    (hA : Normalized A) (hB : Normalized B)
    (hEA : SourceEquation q A) (hEB : SourceEquation q B) : A = B := by
  have hCA := (source_iff_core q hA).mp hEA
  have hCB := (source_iff_core q hB).mp hEB
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := (agree_iff_X_pow_dvd_sub n A B).mp ih
    have hp := core_perturbation q B A n hB hA hd
    have hc := X_pow_dvd_iff.mp hp n (by omega)
    rw [hCA, hCB, sub_self] at hc
    simpa only [zero_sub, map_neg, map_sub, neg_eq_zero, sub_eq_zero] using hc

theorem existence_uniqueness (q : R) :
    ∃! A : PowerSeries R, Normalized A ∧ SourceEquation q A := by
  obtain ⟨A, hA, he⟩ := solution_exists q
  exact ⟨A, ⟨hA, he⟩, fun B hB => solution_unique q hB.1 hA hB.2 he⟩

noncomputable def scaledSolution (q : R) : PowerSeries R :=
  (existence_uniqueness q).exists.choose

theorem scaledSolution_normalized (q : R) : Normalized (scaledSolution q) :=
  (existence_uniqueness q).exists.choose_spec.1

theorem scaledSolution_equation (q : R) : SourceEquation q (scaledSolution q) :=
  (existence_uniqueness q).exists.choose_spec.2

variable {S : Type*} [CommRing S]

theorem map_scaleTail (f : R →+* S) (q : R) (A : PowerSeries R) :
    PowerSeries.map f (scaleTail q A) = scaleTail (f q) (PowerSeries.map f A) := by
  ext n
  simp [PowerSeries.coeff_map]

theorem map_argument (f : R →+* S) (q : R) (A : PowerSeries R) :
    PowerSeries.map f (argument q A) = argument (f q) (PowerSeries.map f A) := by
  simp [argument, map_scaleTail]

theorem map_sourceEquation (f : R →+* S) (q : R) (A : PowerSeries R)
    (h : SourceEquation q A) : SourceEquation (f q) (PowerSeries.map f A) := by
  unfold SourceEquation at *
  rw [← map_argument, ← map_compose f A (argument q A) (argument_constant q A), h,
    PowerSeries.map_X]

theorem map_scaledSolution (f : R →+* S) (q : R) :
    PowerSeries.map f (scaledSolution q) = scaledSolution (f q) := by
  apply solution_unique (f q) ((scaledSolution_normalized q).map f)
    (scaledSolution_normalized (f q))
  · exact map_sourceEquation f q _ (scaledSolution_equation q)
  · exact scaledSolution_equation (f q)

/-- The series `X/(1-X)`, defined without any rational-function coercions. -/
noncomputable def geometric : PowerSeries R := X * PowerSeries.mk 1

theorem geometric_normalized : Normalized (geometric : PowerSeries R) := by
  constructor
  · simp [geometric]
  · rw [show (1 : ℕ) = 0+1 by omega, geometric, coeff_succ_X_mul]
    simp

theorem geometric_coeff (n : ℕ) (hn : 1 ≤ n) :
    coeff n (geometric : PowerSeries R) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [geometric, coeff_succ_X_mul]
  simp

theorem geometric_mul_one_sub :
    (geometric : PowerSeries R) * (1-X) = X := by
  rw [geometric, mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]

theorem scale_neg_one_geometric_mul :
    scaleTail (-1 : R) geometric * (1+X) = X := by
  rw [mul_add, mul_one, mul_comm (scaleTail (-1 : R) geometric) X]
  ext n
  rcases n with _ | (_ | n)
  · simp [scaleTail, geometric]
  · simp [scaleTail, geometric]
  · simp [scaleTail, geometric, pow_succ, coeff_X, show n+1+1 ≠ 1 by omega]

theorem geometric_sourceEquation :
    SourceEquation (-1 : R) (geometric : PowerSeries R) := by
  apply (source_iff_core (-1) geometric_normalized).mpr
  have hA := geometric_normalized (R := R)
  have hone : compose (1 : PowerSeries R) geometric = 1 := by
    change compose (C 1) geometric = 1
    rw [compose_C 1 geometric hA.constantCoeff]
    rfl
  have hcomp : compose (scaleTail (-1 : R) geometric) geometric * (1+geometric) =
      geometric := by
    calc
      _ = compose (scaleTail (-1 : R) geometric * (1+X)) geometric := by
        rw [compose_mul _ _ _ hA.constantCoeff, compose_add _ _ _ hA.constantCoeff,
          hone, compose_X_left _ hA.constantCoeff]
      _ = geometric := by
        rw [scale_neg_one_geometric_mul, compose_X_left _ hA.constantCoeff]
  have hunit : (1+(geometric : PowerSeries R)) * (1-X) = 1 := by
    have hg := geometric_mul_one_sub (R := R)
    linear_combination hg
  have hc : compose (scaleTail (-1 : R) geometric) geometric = X := by
    calc
      _ = compose (scaleTail (-1 : R) geometric) geometric *
          ((1+geometric)*(1-X)) := by rw [hunit, mul_one]
      _ = geometric*(1-X) := by rw [← mul_assoc, hcomp]
      _ = X := geometric_mul_one_sub
  rw [core, hc]
  have hg := geometric_mul_one_sub (R := R)
  linear_combination hg

theorem scaledSolution_neg_one :
    scaledSolution (-1 : R) = (geometric : PowerSeries R) :=
  solution_unique (-1) (scaledSolution_normalized (-1)) geometric_normalized
    (scaledSolution_equation (-1)) geometric_sourceEquation

theorem mapped_coeff_eq_one (f : R →+* S) (q : R) (hq : f q = -1)
    (n : ℕ) (hn : 1 ≤ n) : f (coeff n (scaledSolution q)) = 1 := by
  have h := congrArg (coeff n) (map_scaledSolution f q)
  rw [PowerSeries.coeff_map, hq, scaledSolution_neg_one, geometric_coeff n hn] at h
  exact h

/-- The uniform congruence for the entire family, with its natural modulus. -/
theorem integer_mod_parameter_add_one (q n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (q : ℤ)) : ℤ) : ZMod (q+1)) = 1 := by
  apply mapped_coeff_eq_one (Int.castRingHom (ZMod (q+1))) (q : ℤ) _ n hn
  change (q : ZMod (q+1)) = -1
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (q+1)

/-- A393856: the all-index congruence modulo 5. -/
theorem a393856_mod_five (n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (4 : ℤ)) : ℤ) : ZMod 5) = 1 := by
  exact mapped_coeff_eq_one (Int.castRingHom (ZMod 5)) 4 (by decide) n hn

/-- A393857: the all-index congruence modulo 6, a composite modulus. -/
theorem a393857_mod_six (n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (5 : ℤ)) : ℤ) : ZMod 6) = 1 := by
  exact mapped_coeff_eq_one (Int.castRingHom (ZMod 6)) 5 (by decide) n hn

/-- A393858: the all-index congruence modulo 7. -/
theorem a393858_mod_seven (n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (6 : ℤ)) : ℤ) : ZMod 7) = 1 := by
  exact mapped_coeff_eq_one (Int.castRingHom (ZMod 7)) 6 (by decide) n hn

/-- A393859: the all-index congruence modulo 8, a composite modulus. -/
theorem a393859_mod_eight (n : ℕ) (hn : 1 ≤ n) :
    ((coeff (R := ℤ) n (scaledSolution (7 : ℤ)) : ℤ) : ZMod 8) = 1 := by
  exact mapped_coeff_eq_one (Int.castRingHom (ZMod 8)) 7 (by decide) n hn

end Hanna.Related.ScaledInverse
