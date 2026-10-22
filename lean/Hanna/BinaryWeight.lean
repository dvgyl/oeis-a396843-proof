import Std

/-!
# Binary digit weight

The function `binaryWeight` is the number of ones in the binary expansion:
at each step it adds the remainder modulo two and divides the input by two.
No digit-sum inequality is assumed. The inequalities below are proved from
this definition and elementary natural-number arithmetic.
-/

namespace Hanna

/-- The number of ones in the binary expansion of a natural number. -/
def binaryWeight (n : Nat) : Nat :=
  if n = 0 then 0 else n % 2 + binaryWeight (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem binaryWeight_zero : binaryWeight 0 = 0 := by
  rw [binaryWeight]
  simp

theorem binaryWeight_step (n : Nat) :
    binaryWeight n = n % 2 + binaryWeight (n / 2) := by
  by_cases h : n = 0
  · subst n
    simp
  · rw [binaryWeight, if_neg h]

@[simp] theorem binaryWeight_double (n : Nat) :
    binaryWeight (2 * n) = binaryWeight n := by
  rw [binaryWeight_step]
  simp

@[simp] theorem binaryWeight_double_add_one (n : Nat) :
    binaryWeight (2 * n + 1) = binaryWeight n + 1 := by
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [binaryWeight_step, hmod, hdiv]
  omega

@[simp] theorem binaryWeight_one : binaryWeight 1 = 1 := by
  have h := binaryWeight_double_add_one 0
  simpa using h

/-- Incrementing an integer can add at most one binary one. -/
theorem binaryWeight_succ_le (n : Nat) :
    binaryWeight (n + 1) ≤ binaryWeight n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases heven : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      rw [hn, binaryWeight_double_add_one, binaryWeight_double]
      exact Nat.le_refl _
    · have hn : n = 2 * (n / 2) + 1 := by omega
      have hnext : n + 1 = 2 * (n / 2 + 1) := by omega
      have hsmall : n / 2 < n := by omega
      have hbound := ih (n / 2) hsmall
      rw [hnext, binaryWeight_double]
      calc
        binaryWeight (n / 2 + 1) ≤ binaryWeight (n / 2) + 1 := hbound
        _ ≤ binaryWeight n + 1 := by
          conv => rhs; rw [hn, binaryWeight_double_add_one]
          omega

/-- Binary carrying cannot increase the total number of ones. -/
theorem binaryWeight_add_le (a b : Nat) :
    binaryWeight (a + b) ≤ binaryWeight a + binaryWeight b := by
  have aux : ∀ k a b : Nat, a + b = k →
      binaryWeight (a + b) ≤ binaryWeight a + binaryWeight b := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro a b hsum
      by_cases ha : a = 0
      · subst a
        simp
      by_cases hb : b = 0
      · subst b
        simp
      have hsmall : a / 2 + b / 2 < k := by omega
      have hhalf := ih (a / 2 + b / 2) hsmall (a / 2) (b / 2) rfl
      by_cases hcarry : a % 2 + b % 2 < 2
      · have hdiv : (a + b) / 2 = a / 2 + b / 2 := by omega
        have hmod : (a + b) % 2 = a % 2 + b % 2 := by omega
        rw [binaryWeight_step (a + b), hdiv, hmod,
          binaryWeight_step a, binaryWeight_step b]
        omega
      · have hdiv : (a + b) / 2 = a / 2 + b / 2 + 1 := by omega
        have hmod : (a + b) % 2 = 0 := by omega
        have hparts : a % 2 + b % 2 = 2 := by omega
        have hnext := binaryWeight_succ_le (a / 2 + b / 2)
        rw [binaryWeight_step (a + b), hdiv, hmod,
          binaryWeight_step a, binaryWeight_step b]
        omega
  exact aux (a + b) a b rfl

/-- The addition inequality for an arbitrary finite list of indices. -/
theorem binaryWeight_sum_le (indices : List Nat) :
    binaryWeight indices.sum ≤ (indices.map binaryWeight).sum := by
  induction indices with
  | nil => simp
  | cons a tail ih =>
    simp only [List.sum_cons, List.map_cons]
    have h := binaryWeight_add_le a tail.sum
    omega

/-- Multiplication by a power of two appends zero binary digits. -/
theorem binaryWeight_mul_two_pow (n k : Nat) :
    binaryWeight (n * 2 ^ k) = binaryWeight n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h : n * (2 ^ k * 2) = 2 * (n * 2 ^ k) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [h, binaryWeight_double, ih]

/-- A power of two has exactly one binary one. -/
@[simp] theorem binaryWeight_two_pow (k : Nat) :
    binaryWeight (2 ^ k) = 1 := by
  have h := binaryWeight_mul_two_pow 1 k
  simpa using h

/-- The number immediately below `2^k` consists of `k` binary ones. -/
theorem binaryWeight_two_pow_sub_one (k : Nat) :
    binaryWeight (2 ^ k - 1) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpositive : 0 < 2 ^ k := Nat.two_pow_pos k
    have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [h, binaryWeight_double_add_one, ih]

/-- A positive integer has at least one binary one. -/
theorem binaryWeight_pos {n : Nat} (hn : 0 < n) : 0 < binaryWeight n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases heven : n % 2 = 0
    · have hhalf : 0 < n / 2 := by omega
      have hsmall : n / 2 < n := by omega
      rw [binaryWeight_step, heven, Nat.zero_add]
      exact ih (n / 2) hsmall hhalf
    · have hodd : n % 2 = 1 := by omega
      rw [binaryWeight_step, hodd]
      omega

@[simp] theorem binaryWeight_eq_zero_iff (n : Nat) :
    binaryWeight n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · have hpositive := binaryWeight_pos (n := n) (by omega)
      omega
  · intro h
    subst n
    exact binaryWeight_zero

/-- Exactly the powers of two have binary weight one. -/
theorem binaryWeight_eq_one_iff (n : Nat) :
    binaryWeight n = 1 ↔ ∃ k : Nat, n = 2 ^ k := by
  constructor
  · intro hweight
    induction n using Nat.strongRecOn with
    | ind n ih =>
      have hn : 0 < n := by
        by_cases hz : n = 0
        · subst n
          simp at hweight
        · omega
      by_cases heven : n % 2 = 0
      · have hhalf : binaryWeight (n / 2) = 1 := by
          rw [binaryWeight_step, heven, Nat.zero_add] at hweight
          exact hweight
        have hsmall : n / 2 < n := by omega
        rcases ih (n / 2) hsmall hhalf with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        have hdouble : n = 2 * (n / 2) := by omega
        rw [hdouble, hk, Nat.pow_succ, Nat.mul_comm]
      · have hodd : n % 2 = 1 := by omega
        have hhalf : binaryWeight (n / 2) = 0 := by
          rw [binaryWeight_step, hodd] at hweight
          omega
        have hzero : n / 2 = 0 := (binaryWeight_eq_zero_iff _).mp hhalf
        refine ⟨0, ?_⟩
        simp
        omega
  · rintro ⟨k, rfl⟩
    exact binaryWeight_two_pow k

/-- Other positive indices have at least two binary ones. -/
theorem two_le_binaryWeight_of_not_power {n : Nat} (hn : 0 < n)
    (hnot : ¬ ∃ k : Nat, n = 2 ^ k) : 2 ≤ binaryWeight n := by
  have hpositive := binaryWeight_pos hn
  have hne : binaryWeight n ≠ 1 := by
    intro h
    exact hnot ((binaryWeight_eq_one_iff n).mp h)
  omega

end Hanna
