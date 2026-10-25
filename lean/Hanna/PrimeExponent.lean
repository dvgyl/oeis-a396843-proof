module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Algebra.Prime.Lemmas
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

namespace Hanna

def ExactExponent (p e : ℕ) (z : ℤ) : Prop :=
  (p : ℤ) ^ e ∣ z ∧ ¬ (p : ℤ) ^ (e + 1) ∣ z

theorem prime_power_lower_bound (p e s : ℕ) (m a : ℤ)
    (hpm : (p : ℤ) ^ e ∣ m) (hma : m ^ s ∣ a) :
    (p : ℤ) ^ (e * s) ∣ a := by
  rw [pow_mul]
  exact (pow_dvd_pow_of_dvd hpm s).trans hma

theorem exactExponent_mul_of_not_dvd (p e : ℕ) (hp : Nat.Prime p)
    {a u : ℤ} (ha : ExactExponent p e a) (hu : ¬(p : ℤ) ∣ u) :
    ExactExponent p e (a * u) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact ⟨dvd_mul_of_dvd_left ha.1 u,
    fun h => ha.2 (hp'.pow_dvd_of_dvd_mul_right (e + 1) hu h)⟩

theorem exactExponent_mul_sign_add_multiple (p e j : ℕ) (hp : Nat.Prime p)
    (m q : ℤ) (hpm : (p : ℤ) ∣ m) (hm : ExactExponent p e m) :
    ExactExponent p e (m * ((-1 : ℤ) ^ j + m * q)) := by
  apply exactExponent_mul_of_not_dvd p e hp hm
  intro hsum
  have hsign : (p : ℤ) ∣ (-1 : ℤ) ^ j := by
    simpa using dvd_sub hsum (dvd_mul_of_dvd_left hpm q)
  have hsignUnit : IsUnit ((-1 : ℤ) ^ j) := isUnit_neg_one.pow j
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact hp'.not_dvd_one (hsign.trans (isUnit_iff_dvd_one.mp hsignUnit))

theorem prime_exponent_exists_unique (p : ℕ) (hp : Nat.Prime p) :
    (∀ z : ℤ, z ≠ 0 → ∃! e : ℕ, ExactExponent p e z) ∧
      (¬∃ e : ℕ, ExactExponent p e 0) := by
  constructor
  · intro z hz
    have hf : FiniteMultiplicity (p : ℤ) z :=
      Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp.ne_one, hz⟩
    refine ⟨multiplicity (p : ℤ) z, ?_, ?_⟩
    · exact ⟨pow_multiplicity_dvd (p : ℤ) z,
        hf.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
    · intro e he
      exact (multiplicity_eq_of_dvd_of_not_dvd he.1 he.2).symm
  · rintro ⟨e, he⟩
    exact he.2 (dvd_zero _)

end Hanna
