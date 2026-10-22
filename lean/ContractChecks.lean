import Hanna.Acceptance

open PowerSeries

section Definitions
variable (R : Type*) [CommRing R]

example (U : PowerSeries R) :
    Hanna.Series.Normalized U ↔ coeff R 0 U = 0 ∧ coeff R 1 U = 1 := Iff.rfl

example (U V : PowerSeries R) :
    Hanna.Series.compose U V = MvPowerSeries.subst (fun (_ : Unit) => V) U := rfl

example (m : R) (U : PowerSeries R) :
    Hanna.Series.Psi m U =
      MvPowerSeries.subst (fun (_ : Unit) => X*U-C R m*X*U^2) U := rfl

example (m : R) : coeff R 0 (Hanna.A m) = 0 ∧ coeff R 1 (Hanna.A m) = 1 :=
  Hanna.A_normalized m

example (m : R) :
    MvPowerSeries.subst
      (fun (_ : Unit) => X*Hanna.A m-C R m*X*(Hanna.A m)^2) (Hanna.A m) = X^2 :=
  Hanna.A_equation m

example (m : R) : coeff R 0 (Hanna.B m) = 0 ∧ coeff R 1 (Hanna.B m) = 1 :=
  Hanna.B_normalized m

example (m : R) :
    MvPowerSeries.subst (fun (_ : Unit) => Hanna.B m) (Hanna.A m) = X :=
  Hanna.A_comp_B m

example (m : R) :
    MvPowerSeries.subst (fun (_ : Unit) => Hanna.A m) (Hanna.B m) = X :=
  Hanna.B_comp_A m
end Definitions

example (p e : ℕ) (z : ℤ) : Hanna.ExactExponent p e z ↔
    (p:ℤ)^e ∣ z ∧ ¬(p:ℤ)^(e+1) ∣ z := Iff.rfl

example (m : ℤ) (n : ℕ) : Hanna.a m n = coeff ℤ n (Hanna.A m) := rfl
example (m : ℤ) (n : ℕ) : Hanna.b m n = coeff ℤ n (Hanna.B m) := rfl
example (n : ℕ) : Hanna.P n = coeff (Polynomial ℤ) n (Hanna.A Polynomial.X) := rfl
example (n : ℕ) : Hanna.Q n = coeff (Polynomial ℤ) n (Hanna.B Polynomial.X) := rfl

example (R : Type*) [CommRing R] (m : R) :
    ∃! U : PowerSeries R, Hanna.Series.Normalized U ∧ Hanna.Series.Psi m U = X^2 :=
  Hanna.Acceptance.existence_uniqueness R m

example (R : Type*) [CommRing R] (U : PowerSeries R) (hU : Hanna.Series.Normalized U) :
    ∃! V : PowerSeries R, Hanna.Series.Normalized V ∧
      Hanna.Series.compose U V = X ∧ Hanna.Series.compose V U = X :=
  Hanna.Acceptance.compositional_inverse R U hU

example (m : ℤ) (n : ℕ) :
    Polynomial.eval m (coeff (Polynomial ℤ) n (Hanna.A Polynomial.X)) = coeff ℤ n (Hanna.A m) ∧
    Polynomial.eval m (coeff (Polynomial ℤ) n (Hanna.B Polynomial.X)) = coeff ℤ n (Hanna.B m) :=
  Hanna.Acceptance.coefficient_polynomial_specialization m n

example (m : ℤ) (hm : Odd m) (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff ℤ n (Hanna.A m)) := Hanna.Acceptance.parity_odd m hm n hn

example (m : ℤ) (hm : Even m) :
    coeff ℤ 1 (Hanna.A m) = 1 ∧ ∀ n ≥ 2, (2:ℤ) ∣ coeff ℤ n (Hanna.A m) :=
  Hanna.Acceptance.parity_even m hm

example (m : ℤ) (hm : 2 ≤ m) :
    (∀ j : ℕ, m^2 ∣ coeff ℤ (2^j+1) (Hanna.A m)-m*(-1:ℤ)^j) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n=2^j+1) → m^2 ∣ coeff ℤ n (Hanna.A m)) :=
  Hanna.Acceptance.mod_parameter_squared m hm

example (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ)^Hanna.binaryWeight (n-1) ∣
      coeff (Polynomial ℤ) n (Hanna.A Polynomial.X) :=
  Hanna.Acceptance.binary_divisibility_polynomial n hn

example (n : ℕ) (hn : 1 ≤ n) :
    (Polynomial.X : Polynomial ℤ)^Hanna.binaryWeight (n-1) ∣
      coeff (Polynomial ℤ) n (Hanna.B Polynomial.X) :=
  Hanna.Acceptance.inverse_binary_divisibility_polynomial n hn

example (m : ℤ) (hm : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    m^Hanna.binaryWeight (n-1) ∣ coeff ℤ n (Hanna.A m) :=
  Hanna.Acceptance.binary_divisibility_integer m hm n hn

example (m : ℤ) (hm : 2 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    m^Hanna.binaryWeight (n-1) ∣ coeff ℤ n (Hanna.B m) :=
  Hanna.Acceptance.inverse_binary_divisibility_integer m hm n hn

example (m : ℤ) (hm : 2 ≤ m) (k : ℕ) :
    m^k ∣ coeff ℤ (2^k) (Hanna.A m) := Hanna.Acceptance.power_of_two_index m hm k

example (m : ℤ) (hm : 2 ≤ m) (p : ℕ) (hp : Nat.Prime p) (hpm : (p:ℤ) ∣ m)
    (e : ℕ) (he : (p:ℤ)^e ∣ m ∧ ¬(p:ℤ)^(e+1) ∣ m) (n : ℕ) (hn : 1 ≤ n) :
    (p:ℤ)^(e*Hanna.binaryWeight (n-1)) ∣ coeff ℤ n (Hanna.A m) :=
  Hanna.Acceptance.prime_divisibility_lower_bound m hm p hp hpm e he n hn

example (p : ℕ) (hp : Nat.Prime p) :
    (∀ z : ℤ, z ≠ 0 → ∃! e : ℕ, (p:ℤ)^e ∣ z ∧ ¬(p:ℤ)^(e+1) ∣ z) ∧
    (¬∃ e : ℕ, (p:ℤ)^e ∣ (0:ℤ) ∧ ¬(p:ℤ)^(e+1) ∣ (0:ℤ)) :=
  Hanna.Acceptance.prime_exponent_exists_unique p hp

example (m : ℤ) (hm : 2 ≤ m) (p : ℕ) (hp : Nat.Prime p) (hpm : (p:ℤ) ∣ m)
    (e : ℕ) (he : (p:ℤ)^e ∣ m ∧ ¬(p:ℤ)^(e+1) ∣ m) (n : ℕ) (hn : 2 ≤ n) :
    ((p:ℤ)^e ∣ coeff ℤ n (Hanna.A m) ∧ ¬(p:ℤ)^(e+1) ∣ coeff ℤ n (Hanna.A m)) ↔
      ∃ j : ℕ, n=2^j+1 :=
  Hanna.Acceptance.minimum_prime_exponent_iff m hm p hp hpm e he n hn

example :
    (∀ k : ℕ, (9:ℤ) ∣ coeff ℤ (4^k+1) (Hanna.A 3)-3) ∧
    (∀ k : ℕ, (9:ℤ) ∣ coeff ℤ (2*4^k+1) (Hanna.A 3)-6) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n=4^k+1) →
      (¬∃ k : ℕ, n=2*4^k+1) → (9:ℤ) ∣ coeff ℤ n (Hanna.A 3)) :=
  Hanna.Acceptance.residues_parameter_three

example :
    (∀ k : ℕ, (16:ℤ) ∣ coeff ℤ (4^k+1) (Hanna.A 4)-4) ∧
    (∀ k : ℕ, (16:ℤ) ∣ coeff ℤ (2*4^k+1) (Hanna.A 4)-12) ∧
    (∀ n : ℕ, 2 ≤ n → (¬∃ k : ℕ, n=4^k+1) →
      (¬∃ k : ℕ, n=2*4^k+1) → (16:ℤ) ∣ coeff ℤ n (Hanna.A 4)) :=
  Hanna.Acceptance.residues_parameter_four
