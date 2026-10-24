import Round4.Contracts
import Round3.Contracts
import More.Contracts
import Hanna.Acceptance
import Consecutive
import Related

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

/-!
The sixteen retained Hanna contracts above are unchanged.  The contracts below
anchor the new definitions to actual Mathlib power series and restate every
advertised family of conclusions with explicit hypotheses and unbounded index
quantifiers.  None is a `#check` alias or a finite truncation test.
-/

section ConsecutiveDefinitions
variable (R : Type*) [CommRing R]

example (F : PowerSeries R) : Consecutive.iter F 0 = X := rfl

example (F : PowerSeries R) (n : ℕ) :
    Consecutive.iter F (n+1) =
      MvPowerSeries.subst (fun (_ : Unit) => Consecutive.iter F n) F := rfl

example (r : ℕ) (F : PowerSeries R) :
    Consecutive.step r F = X+Consecutive.iter F r*Consecutive.iter F (r+1) := rfl

example (a : R) :
    Consecutive.geom a = PowerSeries.mk (fun n => a^n) := rfl

example (a : R) :
    Consecutive.mobius a = X*PowerSeries.mk (fun n => a^n) := rfl

example : (Consecutive.correction : PowerSeries R) = X^4*(PowerSeries.mk 1)^3 := by
  rw [Consecutive.correction, Consecutive.geom_one]

example (r : ℕ) :
    ∃! F : PowerSeries R,
      (coeff R 0 F=0 ∧ coeff R 1 F=1) ∧
      F=X+Consecutive.iter F r*Consecutive.iter F (r+1) :=
  Consecutive.existence_uniqueness r

example (r : ℕ) :
    coeff R 0 (Consecutive.solution (R:=R) r)=0 ∧
    coeff R 1 (Consecutive.solution (R:=R) r)=1 :=
  Consecutive.solution_normalized r

example (r : ℕ) :
    Consecutive.solution (R:=R) r = X+
      Consecutive.iter (Consecutive.solution (R:=R) r) r*
      Consecutive.iter (Consecutive.solution (R:=R) r) (r+1) :=
  Consecutive.solution_equation r

example (S : Type*) [CommRing S] (f : R →+* S) (r : ℕ) :
    PowerSeries.map f (Consecutive.solution (R:=R) r)=
      Consecutive.solution (R:=S) r := Consecutive.map_solution f r

example (S : Type*) [CommRing S] (f : R →+* S) (F : PowerSeries R)
    (hF : coeff R 0 F=0 ∧ coeff R 1 F=1) (k : ℕ) :
    PowerSeries.map f (Consecutive.iter F k)=Consecutive.iter (PowerSeries.map f F) k :=
  Consecutive.map_iter f hF k

example (F : PowerSeries R) (hF : Hanna.Series.Normalized F) (n : ℕ) :
    Consecutive.ziter F hF (-(n:ℤ))=
      Consecutive.iter (Hanna.Series.inverse F hF) n :=
  Consecutive.ziter_neg_nat F hF n

example (F : PowerSeries R) (hF : Hanna.Series.Normalized F) (k : ℤ) :
    coeff R 0 (Consecutive.ziter F hF k)=0 ∧
    coeff R 1 (Consecutive.ziter F hF k)=1 :=
  Consecutive.ziter_normalized F hF k

example (F : PowerSeries R) (hF : Hanna.Series.Normalized F) (n : ℕ) :
    Hanna.Series.compose (Consecutive.ziter F hF (n:ℤ))
      (Consecutive.ziter F hF (-(n:ℤ)))=X ∧
    Hanna.Series.compose (Consecutive.ziter F hF (-(n:ℤ)))
      (Consecutive.ziter F hF (n:ℤ))=X :=
  Consecutive.ziter_negative_is_inverse F hF n

example (S : Type*) [CommRing S] (f : R →+* S) (F : PowerSeries R)
    (hF : Hanna.Series.Normalized F) (k : ℤ) :
    PowerSeries.map f (Consecutive.ziter F hF k)=
      Consecutive.ziter (PowerSeries.map f F) (hF.map f) k :=
  Consecutive.map_ziter f F hF k
end ConsecutiveDefinitions

example (r n : ℕ) :
    Consecutive.a r n=coeff ℤ n (Consecutive.solution (R:=ℤ) r) := rfl

example (r k n : ℕ) :
    Consecutive.iterateCoeff r k n=
      coeff ℤ n (Consecutive.iter (Consecutive.solution (R:=ℤ) r) k) := rfl

example (r : ℕ) (k : ℤ) (n : ℕ) :
    Consecutive.integerIterateCoeff r k n=
      coeff ℤ n (Consecutive.ziter (Consecutive.solution (R:=ℤ) r)
        (Consecutive.solution_normalized r) k) := rfl

example (r k : ℕ) :
    Consecutive.iter (Consecutive.solution (R:=ZMod (2*r)) r) k =
      X*Consecutive.geom (k : ZMod (2*r)) +
        if Even r ∧ Odd k then C (ZMod (2*r)) (r:ZMod (2*r))*
          (X^4*Consecutive.geom (1:ZMod (2*r))^3) else 0 :=
  Consecutive.iter_solution_mod r k

example (r k : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod (2*r)))
      (Consecutive.iter (Consecutive.solution (R:=ℤ) r) k) =
        X*Consecutive.geom (k:ZMod (2*r)) +
          if Even r ∧ Odd k then C (ZMod (2*r)) (r:ZMod (2*r))*
            (X^4*Consecutive.geom (1:ZMod (2*r))^3) else 0 :=
  Consecutive.map_iter_solution_mod r k

example (r k : ℕ) :
    Consecutive.iter (Consecutive.solution (R:=ZMod (2*r)) r) k=X ↔ 2*r ∣ k :=
  Consecutive.iter_solution_mod_eq_X_iff r k

example (r : ℕ) :
    Consecutive.iter (Consecutive.solution (R:=ZMod (2*r)) r) (2*r)=X :=
  Consecutive.iter_solution_mod_period r

example (r : ℕ) (hr : 0<r) (k : ℤ) :
    Consecutive.ziter (Consecutive.solution (R:=ZMod (2*r)) r)
      (Consecutive.solution_normalized r) k =
        X*Consecutive.geom (k:ZMod (2*r)) +
          if Even r ∧ Odd k then C (ZMod (2*r)) (r:ZMod (2*r))*
            (X^4*Consecutive.geom (1:ZMod (2*r))^3) else 0 :=
  Consecutive.ziter_solution_mod r hr k

example (r : ℕ) (hr : 0<r) (k : ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod (2*r)))
      (Consecutive.ziter (Consecutive.solution (R:=ℤ) r)
        (Consecutive.solution_normalized r) k) =
        X*Consecutive.geom (k:ZMod (2*r)) +
          if Even r ∧ Odd k then C (ZMod (2*r)) (r:ZMod (2*r))*
            (X^4*Consecutive.geom (1:ZMod (2*r))^3) else 0 :=
  Consecutive.map_ziter_solution_mod r hr k

example (r : ℕ) (hr : 0<r) (k : ℤ) (n : ℕ) (hn : 1≤n) :
    (Consecutive.integerIterateCoeff r k n:ZMod (2*r)) =
      (k:ZMod (2*r))^(n-1) +
        if Even r ∧ Odd k then (r:ZMod (2*r))*
          (if 4≤n then ((n-2).choose 2:ZMod (2*r)) else 0) else 0 :=
  Consecutive.integerIterateCoeff_mod r hr k n hn

example (r : ℕ) (hr : 0<r) (k : ℤ) :
    Consecutive.ziter (Consecutive.solution (R:=ZMod (2*r)) r)
      (Consecutive.solution_normalized r) k=X ↔ (2*r:ℤ) ∣ k :=
  Consecutive.ziter_solution_mod_eq_X_iff r hr k

/- All four original assertions, with only the defining equation as a hypothesis. -/
example (F : PowerSeries ℤ) (hF : coeff ℤ 0 F=0 ∧ coeff ℤ 1 F=1)
    (hEq : F=X+Hanna.Series.compose F F*
      Hanna.Series.compose F (Hanna.Series.compose F F)) :
    (∀ n : ℕ, 0<n → Odd (coeff ℤ n F)) ∧
    (∀ n : ℕ, 3≤n →
      (coeff ℤ n F:ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1) ∧
    (∀ n : ℕ, 2<n → (coeff ℤ n (Hanna.Series.compose F F):ZMod 4)=0) ∧
    (∀ n : ℕ, 2<n →
      (coeff ℤ n (F-X*Hanna.Series.compose F (Hanna.Series.compose F F)):ZMod 4)=2) :=
  Consecutive.a396099_all_four hF hEq

example (n : ℕ) (hn : 0<n) : Odd (Consecutive.a 2 n) :=
  Consecutive.a396099_odd n hn

example (n : ℕ) (hn : 3≤n) :
    (Consecutive.a 2 n:ZMod 4)=if n%4=0 ∨ n%4=1 then 3 else 1 :=
  Consecutive.a396099_residue n hn

example (j : ℕ) :
    (Consecutive.a 2 (4*j+3):ZMod 4)=1 ∧
    (Consecutive.a 2 (4*j+4):ZMod 4)=3 ∧
    (Consecutive.a 2 (4*j+5):ZMod 4)=3 ∧
    (Consecutive.a 2 (4*j+6):ZMod 4)=1 := Consecutive.a396099_period j

example : Consecutive.iter (Consecutive.solution (R:=ZMod 4) 2) 2=
    X+C (ZMod 4) 2*X^2 := Consecutive.a396099_second_iterate_series

example (n : ℕ) (hn : 2<n) : (Consecutive.iterateCoeff 2 2 n:ZMod 4)=0 :=
  Consecutive.a396099_second_iterate n hn

example : Consecutive.solution (R:=ZMod 4) 2-
    X*Consecutive.iter (Consecutive.solution (R:=ZMod 4) 2) 3=
      X+C (ZMod 4) 2*X^3*Consecutive.geom 1 := Consecutive.a396099_difference_series

example (n : ℕ) (hn : 2<n) :
    (coeff ℤ n (Consecutive.solution (R:=ℤ) 2-
      X*Consecutive.iter (Consecutive.solution (R:=ℤ) 2) 3):ZMod 4)=2 :=
  Consecutive.a396099_difference n hn

example (k n : ℕ) (hn : 2≤n) :
    (Consecutive.iterateCoeff 4 k n:ZMod 8)=(k:ZMod 8)^(n-1)+
      if Odd k then (if n%4=0 ∨ n%4=1 then 4 else 0) else 0 :=
  Consecutive.a396798_iterate_residue k n hn

example (n : ℕ) (hn : 2≤n) :
    (Consecutive.a 4 n:ZMod 8)=if n%4=0 ∨ n%4=1 then 5 else 1 :=
  Consecutive.a396798_corrected_residue n hn

example (j : ℕ) :
    (Consecutive.a 4 (4*j+2):ZMod 8)=1 ∧
    (Consecutive.a 4 (4*j+3):ZMod 8)=1 ∧
    (Consecutive.a 4 (4*j+4):ZMod 8)=5 ∧
    (Consecutive.a 4 (4*j+5):ZMod 8)=5 := Consecutive.a396798_corrected_period j

example : (Consecutive.a 4 3:ZMod 8)=1 ∧ (Consecutive.a 4 3:ZMod 8)≠5 :=
  Consecutive.a396798_counterexample

example : ¬(∀ j : ℕ, (Consecutive.a 4 (4*j+3):ZMod 8)=5) :=
  Consecutive.a396798_literal_period_false

example (n : ℕ) (hn : 3<n) : (Consecutive.iterateCoeff 4 2 n:ZMod 8)=0 :=
  Consecutive.a396798_second_iterate n hn

example (n : ℕ) (hn : 2<n) : (Consecutive.iterateCoeff 4 4 n:ZMod 8)=0 :=
  Consecutive.a396798_fourth_iterate n hn

example (n : ℕ) (hn : 3<n) : (Consecutive.iterateCoeff 4 6 n:ZMod 8)=0 :=
  Consecutive.a396798_sixth_iterate n hn

example (n : ℕ) (hn : 1<n) : (Consecutive.iterateCoeff 4 8 n:ZMod 8)=0 :=
  Consecutive.a396798_eighth_iterate n hn

example (j : ℕ) :
    (Consecutive.iterateCoeff 4 3 (4*j+2):ZMod 8)=3 ∧
    (Consecutive.iterateCoeff 4 3 (4*j+3):ZMod 8)=1 ∧
    (Consecutive.iterateCoeff 4 3 (4*j+4):ZMod 8)=7 ∧
    (Consecutive.iterateCoeff 4 3 (4*j+5):ZMod 8)=5 :=
  Consecutive.a396798_third_iterate_period j

example (j : ℕ) :
    (Consecutive.iterateCoeff 4 5 (4*j+2):ZMod 8)=5 ∧
    (Consecutive.iterateCoeff 4 5 (4*j+3):ZMod 8)=1 ∧
    (Consecutive.iterateCoeff 4 5 (4*j+4):ZMod 8)=1 ∧
    (Consecutive.iterateCoeff 4 5 (4*j+5):ZMod 8)=5 :=
  Consecutive.a396798_fifth_iterate_period j

example (j : ℕ) :
    (Consecutive.iterateCoeff 4 7 (4*j+2):ZMod 8)=7 ∧
    (Consecutive.iterateCoeff 4 7 (4*j+3):ZMod 8)=1 ∧
    (Consecutive.iterateCoeff 4 7 (4*j+4):ZMod 8)=3 ∧
    (Consecutive.iterateCoeff 4 7 (4*j+5):ZMod 8)=5 :=
  Consecutive.a396798_seventh_iterate_period j

example (n : ℕ) (hn : 0<n) : (Consecutive.a 5 n:ZMod 10)=1 :=
  Consecutive.a396807_residue n hn

example (k n : ℕ) (hn : 0<n) :
    (Consecutive.iterateCoeff 5 k n:ZMod 10)=(k:ZMod 10)^(n-1) :=
  Consecutive.a396807_iterate_residue k n hn

example (k : ℤ) (n : ℕ) (hn : 1≤n) :
    (Consecutive.integerIterateCoeff 5 k n:ZMod 10)=(k:ZMod 10)^(n-1) :=
  Consecutive.a396807_integer_iterate_congruence k n hn

section ScaledInverseDefinitions
open Hanna.Related.ScaledInverse
variable (R : Type*) [CommRing R]

example (q : R) (F : PowerSeries R) (n : ℕ) :
    coeff R n (scaleTail q F)=q^(n-1)*coeff R n F := coeff_scaleTail q F n

example (q : R) (F : PowerSeries R) :
    SourceEquation q F ↔
      MvPowerSeries.subst
        (fun (_ : Unit) => X-X*PowerSeries.mk (fun n => q^(n-1)*coeff R n F)) F=X :=
  Iff.rfl

example (q : R) : ∃! F : PowerSeries R,
    (coeff R 0 F=0 ∧ coeff R 1 F=1) ∧
      Hanna.Series.compose F
        (X-X*PowerSeries.mk (fun n => q^(n-1)*coeff R n F))=X :=
  Hanna.Related.ScaledInverse.existence_uniqueness q

example (q : R) :
    coeff R 0 (scaledSolution q)=0 ∧ coeff R 1 (scaledSolution q)=1 :=
  scaledSolution_normalized q

example (q : R) :
    Hanna.Series.compose (scaledSolution q)
      (X-X*PowerSeries.mk (fun n => q^(n-1)*coeff R n (scaledSolution q)))=X :=
  scaledSolution_equation q

example (S : Type*) [CommRing S] (f : R →+* S) (q : R) :
    PowerSeries.map f (scaledSolution q)=scaledSolution (f q) :=
  map_scaledSolution f q
end ScaledInverseDefinitions

example (q n : ℕ) (hn : 1≤n) :
    (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (q:ℤ)):ZMod (q+1))=1 :=
  Hanna.Related.ScaledInverse.integer_mod_parameter_add_one q n hn

example (q : ℤ) (hq : (q:ZMod 2)=0) (n : ℕ) :
    Odd (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution q)) ↔
      ∃ k : ℕ, n=2^k := Hanna.Related.ScaledInverse.integer_coeff_odd_iff q hq n

example (n : ℕ) (hn : 1≤n) :
    (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (4:ℤ)):ZMod 5)=1 :=
  Hanna.Related.ScaledInverse.a393856_mod_five n hn

example (n : ℕ) :
    Odd (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (4:ℤ))) ↔
      ∃ k : ℕ, n=2^k := Hanna.Related.ScaledInverse.a393856_parity n

example (n : ℕ) (hn : 1≤n) :
    (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (5:ℤ)):ZMod 6)=1 :=
  Hanna.Related.ScaledInverse.a393857_mod_six n hn

example (n : ℕ) (hn : 1≤n) :
    (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (6:ℤ)):ZMod 7)=1 :=
  Hanna.Related.ScaledInverse.a393858_mod_seven n hn

example (n : ℕ) :
    Odd (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (6:ℤ))) ↔
      ∃ k : ℕ, n=2^k := Hanna.Related.ScaledInverse.a393858_parity n

example (n : ℕ) (hn : 1≤n) :
    (coeff ℤ n (Hanna.Related.ScaledInverse.scaledSolution (7:ℤ)):ZMod 8)=1 :=
  Hanna.Related.ScaledInverse.a393859_mod_eight n hn
