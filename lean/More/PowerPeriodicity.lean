import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A uniform period for powers modulo an arbitrary positive integer

For every positive modulus `m` and every natural base `a`, the powers of `a`
have period `Nat.totient m` from exponent `m` onward.  The proof treats the
prime powers dividing `m` separately, using vanishing for nonunits and
Euler's theorem for units.

AI-generated formal proof prepared for Dev D. Goyal; see `AUTHORSHIP.md`.
-/

namespace More.PowerPeriodicity

theorem nat_pow_totient_add_modEq (m : ℕ) (hm : 0 < m) (a n : ℕ)
    (hn : m ≤ n) : a ^ (n + m.totient) ≡ a ^ n [MOD m] := by
  by_cases ha : a = 0
  · subst a
    have hn0 : n ≠ 0 := by omega
    have hnp : n + m.totient ≠ 0 := by omega
    simpa only [zero_pow hn0, zero_pow hnp] using (Nat.ModEq.refl (n := m) 0)
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha
  have hle : a ^ n ≤ a ^ (n + m.totient) :=
    Nat.pow_le_pow_right ha0 (Nat.le_add_right n m.totient)
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' hle).2
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ m).2
  intro p k hp hpk
  apply (Nat.modEq_iff_dvd' hle).1
  by_cases hpa : p ∣ a
  · have hk : k ≤ n := by
      have hpow : k < p ^ k :=
        lt_of_lt_of_le (Nat.lt_two_pow_self (n := k)) (Nat.pow_le_pow_left hp.two_le k)
      have hpm : p ^ k ≤ m := Nat.le_of_dvd hm hpk
      omega
    have hd : p ^ k ∣ a ^ k := pow_dvd_pow_of_dvd hpa k
    have hn_dvd : p ^ k ∣ a ^ n := hd.trans (pow_dvd_pow a hk)
    have hnp_dvd : p ^ k ∣ a ^ (n + m.totient) :=
      hn_dvd.trans (pow_dvd_pow a (Nat.le_add_right n m.totient))
    exact (Nat.modEq_zero_iff_dvd.2 hn_dvd).trans
      (Nat.modEq_zero_iff_dvd.2 hnp_dvd).symm
  · have hcop : Nat.Coprime a (p ^ k) :=
      Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hpa).symm
    obtain ⟨q, hq⟩ := Nat.totient_dvd_of_dvd hpk
    have hEuler : a ^ m.totient ≡ 1 [MOD p ^ k] := by
      rw [hq, pow_mul]
      simpa using (Nat.ModEq.pow_totient hcop).pow q
    have hmul := hEuler.mul_left (a ^ n)
    simpa [pow_add] using hmul.symm

theorem pow_totient_add_eq (m : ℕ) (hm : 0 < m) (a n : ℕ)
    (hn : m ≤ n) : (a : ZMod m) ^ (n + m.totient) = (a : ZMod m) ^ n := by
  have h := (ZMod.natCast_eq_natCast_iff (a ^ (n + m.totient)) (a ^ n) m).2
    (nat_pow_totient_add_modEq m hm a n hn)
  simpa only [Nat.cast_pow] using h

end More.PowerPeriodicity
