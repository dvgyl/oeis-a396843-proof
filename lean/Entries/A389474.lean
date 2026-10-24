import More.CubicConsequences

/-!
# A389474: separate formal entry in the final collection

AI disclosure: ChatGPT (OpenAI) generated this explicitly typed presentation
for Dev D. Goyal. Review status: see AUTHORSHIP.md. Complete mathematical
implementations are preserved in the imported modules. Source and historical
scope are documented in papers/A389474.tex (ChatGPT's original draft:
history/chatgpt-collection/manuscripts/A389474.tex).
-/

namespace FinalCollection.A389474

open PowerSeries Hanna.Series


noncomputable section

abbrev A : PowerSeries ℤ := More.CubicReversion.a389474

theorem normalized : coeff ℤ 0 A = 0 ∧ coeff ℤ 1 A = 1 :=
  More.CubicReversion.a389474_normalized

theorem source_equation : compose A (X^2+2*X^3+2*A^2) = 3*A^2 :=
  More.CubicReversion.a389474_equation

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (X^2+2*X^3+2*U^2) = 3*U^2) : U = A :=
  More.CubicReversion.a389474_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (X^2+2*X^3+2*U^2) = 3*U^2 :=
  More.CubicReversion.a389474_existence_uniqueness

theorem integral_family_existence (s : ℤ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2+2*C ℤ s*U^3 :=
  More.CubicReversion.existence_uniqueness s

theorem square_mod_nine :
    PowerSeries.map (Int.castRingHom (ZMod 9)) (A^2) = X^2+2*X^3 :=
  More.CubicReversion.a389474_square_mod_nine

theorem square_coefficients (n : ℕ) (hn : 3 < n) :
    (coeff ℤ n (A^2) : ZMod 9) = 0 :=
  More.CubicReversion.a389474_conjecture_3 n hn

theorem power_coefficients (n k : ℕ) :
    (coeff ℤ n (A^(3*k)-(compose A (X^3))^k) : ZMod 3) = 0 :=
  More.CubicReversion.a389474_conjecture_4 n k

end
end FinalCollection.A389474
