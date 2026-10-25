module

public import Hanna.Corollaries
public import Hanna.Parity

@[expose] public section

namespace Hanna.Statements

open PowerSeries

theorem existence_uniqueness (R : Type*) [CommRing R] (m : R) :
    ∃! U : PowerSeries R, Series.Normalized U ∧ Series.Psi m U = X^2 :=
  Series.existence_uniqueness m

theorem compositional_inverse (R : Type*) [CommRing R]
    (U : PowerSeries R) (hU : Series.Normalized U) :
    ∃! V : PowerSeries R,
      Series.Normalized V ∧ Series.compose U V = X ∧ Series.compose V U = X :=
  Series.compositional_inverse U hU

theorem coefficient_polynomial_specialization (m : ℤ) (n : ℕ) :
    Polynomial.eval m (P n) = a m n ∧ Polynomial.eval m (Q n) = b m n :=
  Hanna.coefficient_polynomial_specialization m n

theorem parity_odd (m : ℤ) (hm : Odd m) (n : ℕ) (hn : 1 ≤ n) :
    Odd (a m n) := Parity.odd_coeff m hm n hn

theorem parity_even (m : ℤ) (hm : Even m) :
    a m 1 = 1 ∧ ∀ n ≥ 2, (2 : ℤ) ∣ a m n := Parity.even_coeff m hm

theorem mod_parameter_squared (m : ℤ) (hm : 2 ≤ m) :
    (∀ j : ℕ, m^2 ∣ a m (2^j+1) - m*(-1)^j) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n = 2^j+1) → m^2 ∣ a m n) :=
  Hanna.mod_parameter_squared m hm

theorem binary_divisibility_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ)^binaryWeight (n-1) ∣ P n :=
  Hanna.binary_divisibility_polynomial n hn

theorem inverse_binary_divisibility_polynomial (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ)^binaryWeight (n-1) ∣ Q n :=
  Hanna.inverse_binary_divisibility_polynomial n hn

theorem binary_divisibility_integer (m : ℤ) (_hm : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    m^binaryWeight (n-1) ∣ a m n := Hanna.binary_divisibility_integer m n hn

theorem inverse_binary_divisibility_integer (m : ℤ) (_hm : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    m^binaryWeight (n-1) ∣ b m n := Hanna.inverse_binary_divisibility_integer m n hn

theorem power_of_two_index (m : ℤ) (_hm : 2 ≤ m) (k : ℕ) :
    m^k ∣ a m (2^k) := Hanna.power_of_two_index m k

theorem prime_divisibility_lower_bound (m : ℤ) (hm : 2 ≤ m)
    (p : ℕ) (hp : Nat.Prime p) (hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : ExactExponent p e m) (n : ℕ) (hn : 1 ≤ n) :
    (p : ℤ)^(e*binaryWeight (n-1)) ∣ a m n :=
  Hanna.prime_divisibility_lower_bound m hm p hp hpm e he n hn

theorem prime_exponent_exists_unique (p : ℕ) (hp : Nat.Prime p) :
    (∀ z : ℤ, z ≠ 0 → ∃! e : ℕ, ExactExponent p e z) ∧
      (¬∃ e : ℕ, ExactExponent p e 0) :=
  Hanna.prime_exponent_exists_unique p hp

theorem minimum_prime_exponent_iff (m : ℤ) (hm : 2 ≤ m)
    (p : ℕ) (hp : Nat.Prime p) (hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : ExactExponent p e m) (n : ℕ) (hn : 2 ≤ n) :
    ExactExponent p e (a m n) ↔ ∃ j : ℕ, n = 2^j+1 :=
  Hanna.minimum_prime_exponent_iff m hm p hp hpm e he n hn

theorem residues_parameter_three :
    (∀ k : ℕ, (9:ℤ) ∣ a 3 (4^k+1) - 3) ∧
    (∀ k : ℕ, (9:ℤ) ∣ a 3 (2*4^k+1) - 6) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (9:ℤ) ∣ a 3 n) :=
  Hanna.residues_parameter_three

theorem residues_parameter_four :
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (4^k+1) - 4) ∧
    (∀ k : ℕ, (16:ℤ) ∣ a 4 (2*4^k+1) - 12) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n = 4^k+1) →
      (¬∃ k : ℕ, n = 2*4^k+1) → (16:ℤ) ∣ a 4 n) :=
  Hanna.residues_parameter_four

end Hanna.Statements
