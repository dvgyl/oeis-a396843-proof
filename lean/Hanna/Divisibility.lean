module

public import Hanna.BinaryWeight

/-!
# Binary-weight divisibility for finite expressions

These lemmas prove the integer-arithmetic part of the paper's simultaneous
induction. A factor is a pair consisting of an index and an integer value.
If the value at each index `i` is divisible by `m ^ binaryWeight i`, the
product is divisible by the same power indexed by the sum of all indices.
The hypotheses are individual factor divisibilities, not the desired
product conclusion. All results allow negative integer values.
-/

@[expose] public section

namespace Hanna

theorem int_pow_add (m : Int) (a b : Nat) :
    m ^ (a + b) = m ^ a * m ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Int.pow_succ, Int.pow_succ, ih, Int.mul_assoc]

theorem int_pow_dvd_pow_of_le (m : Int) {a b : Nat} (h : a ≤ b) :
    m ^ a ∣ m ^ b := by
  refine ⟨m ^ (b - a), ?_⟩
  rw [← int_pow_add]
  have hindex : a + (b - a) = b := by omega
  rw [hindex]

theorem int_mul_dvd_mul {a b c d : Int} (hab : a ∣ b) (hcd : c ∣ d) :
    a * c ∣ b * d := by
  rcases hab with ⟨u, rfl⟩
  rcases hcd with ⟨v, rfl⟩
  refine ⟨u * v, ?_⟩
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- The total degree contributed by a finite list of indexed factors. -/
def totalIndex (factors : List (Nat × Int)) : Nat :=
  (factors.map Prod.fst).sum

/-- The product of the integer values in a finite list of indexed factors. -/
def factorProduct : List (Nat × Int) → Int
  | [] => 1
  | factor :: tail => factor.2 * factorProduct tail

/-- First retain the stronger exponent equal to the sum of the weights. -/
theorem sum_weights_power_dvd_product (m : Int) (factors : List (Nat × Int))
    (h : ∀ factor ∈ factors, m ^ binaryWeight factor.1 ∣ factor.2) :
    m ^ (factors.map (fun factor => binaryWeight factor.1)).sum ∣
      factorProduct factors := by
  induction factors with
  | nil => simp [factorProduct]
  | cons factor tail ih =>
    simp only [List.map_cons, List.sum_cons, factorProduct]
    rw [int_pow_add]
    apply int_mul_dvd_mul
    · exact h factor (by simp)
    · apply ih
      intro other hother
      exact h other (by simp [hother])

/-- Finite products preserve binary-weight divisibility at the total index. -/
theorem binaryWeight_power_dvd_product (m : Int) (factors : List (Nat × Int))
    (h : ∀ factor ∈ factors, m ^ binaryWeight factor.1 ∣ factor.2) :
    m ^ binaryWeight (totalIndex factors) ∣ factorProduct factors := by
  have hweight : binaryWeight (totalIndex factors) ≤
      (factors.map (fun factor => binaryWeight factor.1)).sum := by
    simpa [totalIndex, List.map_map, Function.comp_def] using binaryWeight_sum_le (factors.map Prod.fst)
  exact Int.dvd_trans (int_pow_dvd_pow_of_le m hweight)
    (sum_weights_power_dvd_product m factors h)

/-- A fixed integer divisor is preserved under finite sums. -/
theorem int_dvd_sum (d : Int) (values : List Int)
    (h : ∀ value ∈ values, d ∣ value) : d ∣ values.sum := by
  induction values with
  | nil => simp
  | cons value tail ih =>
    rw [List.sum_cons]
    apply Int.dvd_add (h value (by simp))
    apply ih
    intro other hother
    exact h other (by simp [hother])

/-- A finite sum of monomials with the same total index has the required divisor. -/
theorem binaryWeight_power_dvd_sum_products (m : Int) (r : Nat)
    (terms : List (List (Nat × Int)))
    (hindex : ∀ factors ∈ terms, totalIndex factors = r)
    (hfactor : ∀ factors ∈ terms, ∀ factor ∈ factors,
      m ^ binaryWeight factor.1 ∣ factor.2) :
    m ^ binaryWeight r ∣ (terms.map factorProduct).sum := by
  apply int_dvd_sum
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨factors, hmem, rfl⟩
  rw [← hindex factors hmem]
  exact binaryWeight_power_dvd_product m factors (hfactor factors hmem)

/-- The quadratic term in `F = G(x^2) + m*x*F^2` has the required divisor. -/
theorem binaryWeight_power_dvd_quadratic_term (m : Int) (i j : Nat)
    (u v : Int) (hu : m ^ binaryWeight i ∣ u)
    (hv : m ^ binaryWeight j ∣ v) :
    m ^ binaryWeight (i + j + 1) ∣ m * u * v := by
  have hfactor : ∀ factor ∈ [(1, m), (i, u), (j, v)],
      m ^ binaryWeight factor.1 ∣ factor.2 := by
    intro factor hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · simp [Int.pow_succ]
    · exact hu
    · exact hv
  have h := binaryWeight_power_dvd_product m [(1, m), (i, u), (j, v)] hfactor
  simpa [totalIndex, factorProduct, Int.mul_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

end Hanna
