import Hanna.BinaryDivisibility
import Hanna.ModSquare
import Hanna.PrimeExponent

namespace Hanna

lemma not_exactExponent_of_square_dvd (p e : ℕ) (m z : ℤ)
    (hpm : (p : ℤ) ∣ m) (hm : ExactExponent p e m) (hz : m^2 ∣ z) :
    ¬ExactExponent p e z := by
  have he : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    subst e
    exact hm.2 (by simpa using hpm)
  intro hex
  have hpow : (p : ℤ)^(e+1) ∣ (p : ℤ)^(e*2) :=
    pow_dvd_pow _ (by omega)
  have hm2 : (p : ℤ)^(e*2) ∣ m^2 := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd hm.1 2
  exact hex.2 (hpow.trans (hm2.trans hz))

lemma prime_divisibility_lower_bound (m : ℤ) (_hm : 2 ≤ m)
    (p : ℕ) (_hp : Nat.Prime p) (_hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : ExactExponent p e m) (n : ℕ) (hn : 1 ≤ n) :
    (p : ℤ)^(e * binaryWeight (n-1)) ∣ a m n :=
  prime_power_lower_bound p e (binaryWeight (n-1)) m (a m n) he.1
    (binary_divisibility_integer m n hn)

lemma minimum_prime_exponent_iff (m : ℤ) (hm : 2 ≤ m)
    (p : ℕ) (hp : Nat.Prime p) (hpm : (p : ℤ) ∣ m)
    (e : ℕ) (he : ExactExponent p e m) (n : ℕ) (hn : 2 ≤ n) :
    ExactExponent p e (a m n) ↔ ∃ j : ℕ, n = 2^j+1 := by
  constructor
  · intro hex
    by_contra hnone
    exact not_exactExponent_of_square_dvd p e m (a m n) hpm he
      ((mod_parameter_squared m hm).2 n hn hnone) hex
  · rintro ⟨j, rfl⟩
    obtain ⟨q, hq⟩ := (mod_parameter_squared m hm).1 j
    have ha : a m (2^j+1) = m*((-1 : ℤ)^j+m*q) := by
      linear_combination hq
    rw [ha]
    exact exactExponent_mul_sign_add_multiple p e j hp m q hpm he

end Hanna
