module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The greedy sequence avoiding sums of three consecutive terms (A394576)

AI-generated formalization by ChatGPT (OpenAI), prompted by Dev D. Goyal.
The source sequence and conjectures are due to Hoang Xuan Thanh.

`sequence` is indexed from zero; its `n`th value is OEIS a(n+1).
We construct it in blocks, prove the literal greedy-minimum specification,
prove uniqueness for that specification, and then deduce all-index bounds.
-/

@[expose] public section

namespace Families.GreedyTriple

/-- A blockwise construction, subsequently proved to be the source greedy sequence. -/
def sequence (n : ℕ) : ℕ :=
  if h : n < 3 then n + 1 else
    let k := n / 3
    let s := sequence (k - 1) + sequence k + sequence (k + 1)
    4 * k + n % 3 + if s ≤ 4 * k + n % 3 then 1 else 0
termination_by n
decreasing_by all_goals omega

/-- The forbidden consecutive triple centered at the zero-based index `k`. -/
def skipped (f : ℕ → ℕ) (k : ℕ) : ℕ := f (k - 1) + f k + f (k + 1)

theorem initial (n : ℕ) (hn : n < 3) : sequence n = n + 1 := by
  rw [sequence]
  simp [hn]

theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    sequence n = 4 * (n / 3) + n % 3 +
      if skipped sequence (n / 3) ≤ 4 * (n / 3) + n % 3 then 1 else 0 := by
  rw [sequence]
  simp only [show ¬n < 3 by omega, if_false, skipped]
  exact if_congr Iff.rfl rfl rfl

theorem upper_sum (k : ℕ) (hk : 1 ≤ k) :
    (4 * (k - 1) + 3) / 3 + (4 * k + 3) / 3 +
      (4 * (k + 1) + 3) / 3 = 4 * k + 2 := by
  have hm : (k - 1) % 3 = 0 ∨ (k - 1) % 3 = 1 ∨ (k - 1) % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> omega

theorem lower_sum (k : ℕ) (hk : 1 ≤ k) :
    (4 * (k - 1) + 1) / 3 + (4 * k + 1) / 3 +
      (4 * (k + 1) + 1) / 3 = 4 * k := by
  have hm : (k - 1) % 3 = 0 ∨ (k - 1) % 3 = 1 ∨ (k - 1) % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> omega

theorem bounds (n : ℕ) :
    (4 * n + 1) / 3 ≤ sequence n ∧ sequence n ≤ (4 * n + 3) / 3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · rw [initial n hn]
      omega
    · have hk : 1 ≤ n / 3 := by omega
      have h₀ := (ih (n / 3 - 1) (by omega)).2
      have h₁ := (ih (n / 3) (by omega)).2
      have h₂ := (ih (n / 3 + 1) (by omega)).2
      have hs : skipped sequence (n / 3) ≤ 4 * (n / 3) + 2 := by
        have ht := upper_sum (n / 3) hk
        unfold skipped
        omega
      rw [recurrence n (by omega)]
      split_ifs <;> omega

theorem skipped_bounds (k : ℕ) (hk : 1 ≤ k) :
    4 * k ≤ skipped sequence k ∧ skipped sequence k ≤ 4 * k + 2 := by
  have h₀ := bounds (k - 1)
  have h₁ := bounds k
  have h₂ := bounds (k + 1)
  have hlo := lower_sum k hk
  have hhi := upper_sum k hk
  unfold skipped
  omega

theorem block_formula (k r : ℕ) (hk : 1 ≤ k) (hr : r < 3) :
    sequence (3 * k + r) = 4 * k + r +
      if skipped sequence k ≤ 4 * k + r then 1 else 0 := by
  rw [recurrence (3 * k + r) (by omega)]
  have hq : (3 * k + r) / 3 = k := by omega
  have hm : (3 * k + r) % 3 = r := by omega
  rw [hq, hm]

theorem strictMono_sequence : StrictMono sequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n < 3
  · interval_cases n
    · norm_num [initial]
    · norm_num [initial]
    · have hb := (bounds 3).1
      rw [initial 2 (by decide)]
      norm_num at hb ⊢
      omega
  · have hb := bounds n
    have hc := bounds (n + 1)
    by_cases hq : n / 3 = (n + 1) / 3
    · rw [recurrence n (by omega), recurrence (n + 1) (by omega), ← hq]
      split_ifs <;> omega
    · omega

theorem positive (n : ℕ) : 0 < sequence n := by
  have h := strictMono_sequence.monotone (Nat.zero_le n)
  rw [initial 0 (by decide)] at h
  omega

theorem avoids_skipped (n k : ℕ) (hk : 1 ≤ k) :
    sequence n ≠ skipped sequence k := by
  have hs := skipped_bounds k hk
  by_cases hn : n < 3
  · rw [initial n hn]
    omega
  · have hb := bounds n
    intro he
    have hq : n / 3 = k := by omega
    rw [recurrence n (by omega), hq] at he
    split_ifs at he <;> omega

theorem complement (t : ℕ) (ht : 0 < t) :
    (∃ n, sequence n = t) ∨ ∃ k, 1 ≤ k ∧ skipped sequence k = t := by
  by_cases hs : t < 4
  · left
    refine ⟨t - 1, ?_⟩
    rw [initial (t - 1) (by omega)]
    omega
  · have hk : 1 ≤ t / 4 := by omega
    have hb := skipped_bounds (t / 4) hk
    by_cases he : skipped sequence (t / 4) = t
    · exact Or.inr ⟨t / 4, hk, he⟩
    · left
      by_cases hl : t < skipped sequence (t / 4)
      · have hr : t % 4 < 3 := by omega
        refine ⟨3 * (t / 4) + t % 4, ?_⟩
        rw [block_formula (t / 4) (t % 4) hk hr]
        split_ifs <;> omega
      · have hr : t % 4 - 1 < 3 := by omega
        refine ⟨3 * (t / 4) + (t % 4 - 1), ?_⟩
        rw [block_formula (t / 4) (t % 4 - 1) hk hr]
        split_ifs <;> omega

/-- The literal least-admissible-next-term rule, with zero-based indexing. -/
def IsGreedy (f : ℕ → ℕ) : Prop :=
  f 0 = 1 ∧ ∀ n,
    f n < f (n + 1) ∧
    (∀ k, 1 ≤ k → k + 1 ≤ n → f (n + 1) ≠ skipped f k) ∧
    ∀ t, f n < t → (∀ k, 1 ≤ k → k + 1 ≤ n → t ≠ skipped f k) → f (n + 1) ≤ t

theorem greedy_specification : IsGreedy sequence := by
  refine ⟨initial 0 (by decide), ?_⟩
  intro n
  refine ⟨strictMono_sequence (by omega), ?_, ?_⟩
  · intro k hk _
    exact avoids_skipped (n + 1) k hk
  · intro t ht ha
    by_contra hnot
    have hlt : t < sequence (n + 1) := by omega
    have htpos : 0 < t := by have h := positive n; omega
    rcases complement t htpos with ⟨j, hj⟩ | ⟨k, hk, he⟩
    · have hn : n < j := by
        apply (strictMono_sequence.lt_iff_lt).mp
        omega
      have hn' : j < n + 1 := by
        apply (strictMono_sequence.lt_iff_lt).mp
        omega
      omega
    · have hpos := positive (k - 1)
      have hbelow : sequence (k + 1) < t := by
        unfold skipped at he
        omega
      have hkn : k + 1 ≤ n := by
        have h : k + 1 < n + 1 := (strictMono_sequence.lt_iff_lt).mp (by omega)
        omega
      exact ha k hk hkn he.symm

theorem greedy_unique {f g : ℕ → ℕ} (hf : IsGreedy f) (hg : IsGreedy g) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hf.1.trans hg.1.symm
    | succ n =>
      have he : f n = g n := ih n (by omega)
      have hs : ∀ k, 1 ≤ k → k + 1 ≤ n → skipped f k = skipped g k := by
        intro k hk hkn
        unfold skipped
        rw [ih (k - 1) (by omega), ih k (by omega), ih (k + 1) (by omega)]
      apply Nat.le_antisymm
      · apply (hf.2 n).2.2 (g (n + 1))
        · rw [he]
          exact (hg.2 n).1
        · intro k hk hkn
          rw [hs k hk hkn]
          exact (hg.2 n).2.1 k hk hkn
      · apply (hg.2 n).2.2 (f (n + 1))
        · rw [← he]
          exact (hf.2 n).1
        · intro k hk hkn
          rw [← hs k hk hkn]
          exact (hf.2 n).2.1 k hk hkn

theorem existence_uniqueness : ∃! f : ℕ → ℕ, IsGreedy f :=
  ⟨sequence, greedy_specification, fun _ h => greedy_unique h greedy_specification⟩

/-- One-based OEIS convention, with auxiliary value a(0)=0. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else sequence (n - 1)

theorem a394576_bounds (n : ℕ) (hn : 1 ≤ n) :
    (4 * n - 3) / 3 ≤ a n ∧ a n ≤ (4 * n - 1) / 3 := by
  have h := bounds (n - 1)
  unfold a
  rw [if_neg (by omega)]
  omega

/-- OEIS A394576, Conjecture 1. -/
theorem a394576_conjecture_one (n : ℕ) (hn : 1 ≤ n) :
    a n ≤ (4 * n - 1) / 3 := (a394576_bounds n hn).2

theorem a394576_error_zero_or_one (n : ℕ) (hn : 1 ≤ n) :
    (4 * n - 1) / 3 - a n = 0 ∨ (4 * n - 1) / 3 - a n = 1 := by
  have h := a394576_bounds n hn
  omega

theorem a394576_every_third (k : ℕ) (hk : 1 ≤ k) : a (3 * k) = 4 * k - 1 := by
  have h := a394576_bounds (3 * k) (by omega)
  omega

theorem original_source_bound {f : ℕ → ℕ} (hf : IsGreedy f) (n : ℕ) :
    f n ≤ (4 * n + 3) / 3 := by
  rw [greedy_unique hf greedy_specification]
  exact (bounds n).2

end Families.GreedyTriple
