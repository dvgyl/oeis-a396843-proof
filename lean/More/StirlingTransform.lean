import More.StirlingNumbers
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Combinatorics.Enumerative.Partition

/-!
# Weighted factorial Stirling transforms

AI disclosure: OpenAI ChatGPT generated the proof development for Dev D. Goyal.
The theorem below transfers any common period of powers to every integer-weighted
factorial Stirling transform.  The named sequences use the explicit formulas in
the OEIS entries, with actual partition types for the three partition weights.
-/

namespace More.Stirling

open Finset

/-- The coefficient of `x^n/n!` in `G(exp(x)-1)` when `G(t)=Σ c(k)t^k`. -/
def transform (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), c k * (k.factorial : ℤ) * (second n k : ℤ)

theorem power_expansion_mod (m a n : ℕ) (h : a ≤ n) :
    (a : ZMod m) ^ n =
      ∑ k ∈ range (a + 1),
        (a.choose k : ZMod m) * ((k.factorial : ZMod m) * (second n k : ZMod m)) := by
  have hc := congrArg (fun v : ℕ => (v : ZMod m)) (power_expansion_choose a n h)
  simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using hc

/-- Invert the triangular power expansion without dividing by a factorial. -/
theorem column_periodic_of_powers (m p n : ℕ) (hn : m ≤ n)
    (hp : ∀ a : ℕ, (a : ZMod m) ^ (n + p) = (a : ZMod m) ^ n) :
    ∀ k, k < m →
      (k.factorial : ZMod m) * (second (n + p) k : ZMod m) =
      (k.factorial : ZMod m) * (second n k : ZMod m) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hnew := power_expansion_mod m k (n + p) (by omega)
      have hold := power_expansion_mod m k n (by omega)
      rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hnew hold
      have lower :
          (∑ j ∈ range k, (k.choose j : ZMod m) *
            ((j.factorial : ZMod m) * (second (n + p) j : ZMod m))) =
          ∑ j ∈ range k, (k.choose j : ZMod m) *
            ((j.factorial : ZMod m) * (second n j : ZMod m)) := by
        apply sum_congr rfl
        intro j hj
        have hjk : j < k := mem_range.mp hj
        rw [ih j hjk (by omega)]
      have he := hp k
      rw [hnew, hold, lower] at he
      exact add_left_cancel he

theorem factorial_zero_mod (m k : ℕ) (hm : 0 < m) (hk : m ≤ k) :
    (k.factorial : ZMod m) = 0 :=
  (ZMod.natCast_zmod_eq_zero_iff_dvd k.factorial m).mpr (Nat.dvd_factorial hm hk)

/-- Modulo `m`, all factorial-transform terms with index at least `m` vanish. -/
theorem transform_truncate_mod (c : ℕ → ℤ) (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (transform c n : ZMod m) =
      ∑ k ∈ range m, (c k : ZMod m) * (k.factorial : ZMod m) * (second n k : ZMod m) := by
  simp only [transform, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  symm
  apply sum_subset (range_mono (show m ≤ n + 1 by omega))
  intro k hk hknot
  have hmk : m ≤ k := by simpa only [mem_range, not_lt] using hknot
  rw [factorial_zero_mod m k hm hmk]
  simp

theorem transform_periodic_of_powers (c : ℕ → ℤ) (m p n : ℕ)
    (hm : 0 < m) (hn : m ≤ n)
    (hp : ∀ a : ℕ, (a : ZMod m) ^ (n + p) = (a : ZMod m) ^ n) :
    (transform c (n + p) : ZMod m) = (transform c n : ZMod m) := by
  rw [transform_truncate_mod c m (n + p) hm (by omega),
    transform_truncate_mod c m n hm hn]
  apply sum_congr rfl
  intro k hk
  rw [mul_assoc, mul_assoc, column_periodic_of_powers m p n hn hp k (mem_range.mp hk)]

/-! ## Exact source-formula specializations -/

def A052895 (n : ℕ) : ℤ := transform (fun k => (catalan k : ℤ)) n

def A064618 (n : ℕ) : ℤ := transform (fun k => (k.factorial : ℤ)) n

def A354242 (n : ℕ) : ℤ := transform (fun k => ((2 * k).choose k : ℤ)) n

noncomputable section

/-- Ordinary integer partitions, with no undefined external sequence parameter. -/
def partitionWeight (n : ℕ) : ℤ := (Fintype.card (Nat.Partition n) : ℤ)

/-- Integer partitions in which each positive part is used at most once. -/
def distinctPartitionWeight (n : ℕ) : ℤ := ((Nat.Partition.distincts n).card : ℤ)

/-- Integer partitions whose positive parts are all perfect squares. -/
def squarePartitionWeight (n : ℕ) : ℤ := by
  classical
  exact ((Finset.univ.filter fun p : Nat.Partition n =>
    ∀ a ∈ p.parts, Nat.sqrt a * Nat.sqrt a = a).card : ℤ)

def A167137 (n : ℕ) : ℤ := transform partitionWeight n

def A305550 (n : ℕ) : ℤ := transform distinctPartitionWeight n

def A306082 (n : ℕ) : ℤ := transform squarePartitionWeight n

end

/-- `A001333(k+1)`, the shifted Pell-Lucas numerators `1,3,7,17,...`. -/
def pellWeight : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | k + 2 => 2 * pellWeight (k + 1) + pellWeight k

def A080253 (n : ℕ) : ℤ := transform pellWeight n

end More.Stirling
