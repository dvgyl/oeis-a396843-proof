import More.RationalParity
import More.CubicConsequences
import More.StirlingPeriodicity
import More.InverseIterate

/-!
# Explicit semantic contracts for the additional OEIS results

These examples state the intended definitions, domains, functional equations,
and unbounded conclusions independently of the exported theorem types.
They are compiled in every complete validation run.

AI-generated review contracts prepared for Dev D. Goyal.
-/

open PowerSeries Hanna.Series

set_option maxHeartbeats 1000000

section RationalParityContracts

example : (RationalParity.B : PowerSeries ℤ) * (1 - X)^2 = X :=
  RationalParity.B_denominator

example : (RationalParity.A : PowerSeries ℤ) =
    compose RationalParity.B (compose RationalParity.B RationalParity.B) :=
  RationalParity.A_definition

example (n : ℕ) : RationalParity.a n = coeff ℤ n RationalParity.A := rfl

example (n : ℕ) :
    (RationalParity.a n : ZMod 2) =
      if n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9 then 1 else 0 :=
  RationalParity.a396093_residue n

example (n : ℕ) : Even (RationalParity.a (2*n)) :=
  RationalParity.a396093_even_indices n

example (n : ℕ) (hn : 1 ≤ n) :
    Even (RationalParity.a (2*n-1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5*k-2 :=
  RationalParity.a396093_odd_indices_original n hn

end RationalParityContracts

section CubicContracts

open More.CubicReversion

example (s : ℤ) : ∃! U : PowerSeries ℤ, Normalized U ∧
    compose U (3*X^2) = 2*X^2 + U^2 + 2*C ℤ s*U^3 := by
  simpa only [Equation] using More.CubicReversion.existence_uniqueness s

example : coeff ℤ 0 a389474 = 0 ∧ coeff ℤ 1 a389474 = 1 :=
  a389474_normalized

example : compose a389474 (X^2+2*X^3+2*a389474^2) = 3*a389474^2 :=
  a389474_equation

example (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (X^2+2*X^3+2*U^2) = 3*U^2) : U = a389474 :=
  a389474_unique U hU he

example : ∃! U : PowerSeries ℤ, Normalized U ∧
    compose U (X^2+2*X^3+2*U^2) = 3*U^2 :=
  More.CubicReversion.a389474_existence_uniqueness

example : PowerSeries.map (Int.castRingHom (ZMod 9)) (a389474^2) = X^2+2*X^3 :=
  a389474_square_mod_nine

example (n : ℕ) (hn : 3 < n) :
    (coeff ℤ n (a389474^2) : ZMod 9) = 0 := a389474_conjecture_3 n hn

example (n k : ℕ) :
    (coeff ℤ n (a389474^(3*k) - (compose a389474 (X^3))^k) : ZMod 3) = 0 :=
  a389474_conjecture_4 n k

example : coeff ℤ 0 a389475 = 0 ∧ coeff ℤ 1 a389475 = 1 :=
  a389475_normalized

example : compose a389475 (3*X^2) = 2*X^2+a389475^2-2*a389475^3 :=
  a389475_equation

example (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (3*X^2) = 2*X^2+U^2-2*U^3) : U = a389475 :=
  a389475_unique U hU he

example : ∃! U : PowerSeries ℤ, Normalized U ∧
    compose U (3*X^2) = 2*X^2+U^2-2*U^3 :=
  More.CubicReversion.a389475_existence_uniqueness

example : PowerSeries.map (Int.castRingHom (ZMod 3)) (a389475^3) =
    PowerSeries.map (Int.castRingHom (ZMod 3)) (compose a389475 (X^3)) :=
  a389475_cube_mod_three

example : PowerSeries.map (Int.castRingHom (ZMod 3)) (a389475^2) =
    X^2 + 2*PowerSeries.map (Int.castRingHom (ZMod 3)) (compose a389475 (X^3)) :=
  a389475_square_mod_three

example (n : ℕ) :
    (coeff ℤ n (a389475^3 - compose a389475 (X^3)) : ZMod 3) = 0 :=
  a389475_conjecture_4a n

example (n : ℕ) :
    (coeff ℤ n (a389475^2-X^2-2*compose a389475 (X^3)) : ZMod 3) = 0 :=
  a389475_conjecture_4b n

end CubicContracts

section StirlingContracts

open More.Stirling Finset

example : second 0 0 = 1 := rfl
example (n k : ℕ) : second (n+1) (k+1) = (k+1)*second n (k+1)+second n k := rfl
example (c : ℕ → ℤ) (n : ℕ) :
    transform c n = ∑ k ∈ range (n+1), c k*(k.factorial : ℤ)*(second n k : ℤ) := rfl

example (c : ℕ → ℤ) (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : m ≤ n) :
    (transform c (n+m.totient) : ZMod m) = (transform c n : ZMod m) :=
  transform_totient_period c m hm n hn

example (c : ℕ → ℤ) (m : ℕ) (hm : 0 < m) :
    let f := fun n : ℕ => (transform c (m+n) : ZMod m)
    0 < More.TailPeriodicity.leastPeriod f ∧
      More.TailPeriodicity.leastPeriod f ∣ m.totient ∧
      (∀ n, f (n+More.TailPeriodicity.leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n+q) = f n) → More.TailPeriodicity.leastPeriod f ≤ q) :=
  transform_exact_tail_period c m hm

example (n : ℕ) : A052895 n = transform (fun k => (catalan k : ℤ)) n := rfl
example (n : ℕ) : A064618 n = transform (fun k => (k.factorial : ℤ)) n := rfl
example (n : ℕ) : A354242 n = transform (fun k => ((2*k).choose k : ℤ)) n := rfl
example (n : ℕ) : A167137 n = transform (fun k => (Fintype.card (Nat.Partition k) : ℤ)) n := rfl
example (n : ℕ) : A305550 n = transform (fun k => ((Nat.Partition.distincts k).card : ℤ)) n := rfl
example (n : ℕ) : squarePartitionWeight n =
    ((Finset.univ.filter fun p : Nat.Partition n =>
      ∀ a ∈ p.parts, Nat.sqrt a * Nat.sqrt a = a).card : ℤ) := by
  classical
  rfl
example (n : ℕ) : A306082 n = transform squarePartitionWeight n := rfl
example (n : ℕ) : A080253 n = transform pellWeight n := rfl
example : pellWeight 0 = 1 := rfl
example : pellWeight 1 = 3 := rfl
example (k : ℕ) : pellWeight (k+2) = 2*pellWeight (k+1)+pellWeight k := rfl

example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A052895 (n+m.totient) : ZMod m) = (A052895 n : ZMod m) := A052895_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A064618 (n+m.totient) : ZMod m) = (A064618 n : ZMod m) := A064618_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A354242 (n+m.totient) : ZMod m) = (A354242 n : ZMod m) := A354242_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A167137 (n+m.totient) : ZMod m) = (A167137 n : ZMod m) := A167137_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A305550 (n+m.totient) : ZMod m) = (A305550 n : ZMod m) := A305550_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A306082 (n+m.totient) : ZMod m) = (A306082 n : ZMod m) := A306082_period m hm n hn
example (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (A080253 (n+m.totient) : ZMod m) = (A080253 n : ZMod m) := A080253_period m hm n hn

end StirlingContracts

section InverseIterateContracts

open InverseIterate Consecutive

example (r : ℕ) : ∃! U : PowerSeries ℤ, Normalized U ∧
    iter U (r+1) = (1+X)*iter U r := F_original_existence_uniqueness r

example (r : ℕ) : compose (R (S:=ℤ) r) (F r) = X := compose_R_F r
example (r : ℕ) : compose (F (S:=ℤ) r) (R r) = X := compose_F_R r

example (r n : ℕ) (hn : 1 ≤ n) : (coeff ℤ n (F r) : ZMod r) = 1 :=
  coefficient_congruence r n hn

example (r k n : ℕ) (hn : 1 ≤ n) :
    (coeff ℤ n (iter (F r) k) : ZMod r) = (k : ZMod r)^(n-1) :=
  iterate_coefficient_congruence r k n hn

example : A396102 = (F (S:=ℤ) 3) := rfl
example : Normalized A396102 := F_normalized 3
example : compose A396102 (compose A396102 A396102) =
    (1+X)*compose A396102 A396102 := a396102_definition
example (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (compose U U) = (1+X)*compose U U) : U = A396102 :=
  a396102_unique U hU he
example (n : ℕ) (hn : 1 ≤ n) : (coeff ℤ n A396102 : ZMod 3) = 1 :=
  a396102_congruence n hn

end InverseIterateContracts
