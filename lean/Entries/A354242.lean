import More.StirlingPeriodicity

/-!
# A354242: separate formal entry in the final collection

AI disclosure: ChatGPT (OpenAI) generated this explicitly typed presentation
for Dev D. Goyal. Review status: see AUTHORSHIP.md. Complete mathematical
implementations are preserved in the imported modules. Source and historical
scope are documented in papers/A354242.tex (ChatGPT's original draft:
history/chatgpt-collection/manuscripts/A354242.tex).
-/

namespace FinalCollection.A354242



noncomputable section

open Finset

abbrev a (n : ℕ) : ℤ := More.Stirling.A354242 n

theorem source_formula (n : ℕ) :
    a n = ∑ k ∈ range (n+1),
      ((2*k).choose k : ℤ) * (k.factorial : ℤ) * (More.Stirling.second n k : ℤ) := rfl

theorem period (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (a (n+m.totient) : ZMod m) = (a n : ZMod m) :=
  More.Stirling.A354242_period m hm n hn

theorem least_period_divides (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (a (m+n) : ZMod m)) ∣ m.totient :=
  More.Stirling.A354242_leastPeriod_dvd m hm

theorem least_period_specification (m : ℕ) (hm : 0 < m) :
    let f := fun n : ℕ => (a (m+n) : ZMod m)
    0 < More.TailPeriodicity.leastPeriod f ∧
      More.TailPeriodicity.leastPeriod f ∣ m.totient ∧
      (∀ n, f (n+More.TailPeriodicity.leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n+q) = f n) →
        More.TailPeriodicity.leastPeriod f ≤ q) :=
  More.Stirling.transform_exact_tail_period (fun k => ((2*k).choose k : ℤ)) m hm

end
end FinalCollection.A354242
