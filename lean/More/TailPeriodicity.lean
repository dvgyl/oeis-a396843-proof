import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Exact periods of sequence tails

Every positive period of a sequence is divisible by its least positive period.
This supplies the exact-period clause in the OEIS periodicity statements.

AI-generated formal proof prepared for Dev D. Goyal; see `AUTHORSHIP.md`.
-/

namespace More.TailPeriodicity

def shift {α : Type*} (f : ℕ → α) : ℕ → α := fun n => f (n + 1)

theorem iterate_shift {α : Type*} (f : ℕ → α) (k n : ℕ) :
    (shift^[k] f) n = f (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega

/-- The least positive period of the whole sequence, or zero if none exists. -/
noncomputable def leastPeriod {α : Type*} (f : ℕ → α) : ℕ :=
  Function.minimalPeriod shift f

theorem isPeriodicPt_shift_iff {α : Type*} (f : ℕ → α) (p : ℕ) :
    Function.IsPeriodicPt shift p f ↔ ∀ n, f (n + p) = f n := by
  constructor
  · intro h n
    have he := congrFun h n
    simpa only [iterate_shift] using he
  · intro h
    apply funext
    intro n
    simpa only [iterate_shift] using h n

theorem leastPeriod_spec {α : Type*} (f : ℕ → α) (p : ℕ)
    (hp : 0 < p) (h : ∀ n, f (n + p) = f n) :
    0 < leastPeriod f ∧ leastPeriod f ∣ p ∧
      (∀ n, f (n + leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n + q) = f n) → leastPeriod f ≤ q) := by
  have hf := (isPeriodicPt_shift_iff f p).2 h
  refine ⟨hf.minimalPeriod_pos hp, hf.minimalPeriod_dvd, ?_, ?_⟩
  · exact (isPeriodicPt_shift_iff f (leastPeriod f)).1
      (Function.isPeriodicPt_minimalPeriod shift f)
  · intro q hq hperiod
    exact (isPeriodicPt_shift_iff f q).2 hperiod |>.minimalPeriod_le hq

end More.TailPeriodicity
