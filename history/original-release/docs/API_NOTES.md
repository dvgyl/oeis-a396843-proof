# Mathlib API and implementation notes

## Evidence and dependency pin

The original API notes below came from the **Mathlib v4.19.0 source**. The completed implementation now compiles against the pinned revision. The current wrappers are in `lean/Hanna/Series/Basic.lean`. The construction, filtration, and inverse modules contain their checked uses. See [COVERAGE.md](COVERAGE.md) for the current proof map.

Use Lean `leanprover/lean4:v4.19.0` with Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The official
[GitHub tag API](https://api.github.com/repos/leanprover-community/mathlib4/git/ref/tags/v4.19.0)
returned that commit for `v4.19.0`; the release's
[lean-toolchain](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/lean-toolchain)
contains `leanprover/lean4:v4.19.0`.

The inspected archive came from
`https://github.com/leanprover-community/mathlib4/archive/refs/tags/v4.19.0.tar.gz`.
Its SHA-256 was
`fd6bd32a498dcf50a28df78270838ae7b995f25cbd03beec4b3b79f31c3df550`.
The local research copy was `tmp/mathlib4-4.19.0`; it is not bundled or required
by this package. The completed package includes the exact Lake dependency manifest and a fresh build of the original foundations. No toolchain upgrade was needed.

Relevant verified import paths:

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Multiplicity
```

## Composition: use substitution, with its hypotheses

In this release `PowerSeries R` is an abbreviation for `MvPowerSeries Unit R`.
There is no univariate `PowerSeries.comp` declaration in the inspected power-series
modules. The implemented local wrapper over a commutative ring is:

```lean
-- Project definition in Hanna.Series.Basic.
noncomputable def compose (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun (_ : Unit) => g) f
```

Its argument order is **outer first, inner second**: `compose f g` means `f(g(x))`.

[MvPowerSeries/Substitution.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/MvPowerSeries/Substitution.lean)
provides:

- `MvPowerSeries.HasSubst`: constant coefficients must be nilpotent, with a
  finiteness condition on the substituted family.
- `MvPowerSeries.hasSubst_of_constantCoeff_zero`: for finite variable types,
  zero constant coefficients suffice. Apply this to `Unit`.
- `substAlgHom`, `substAlgHom_apply`, `subst_self`, `subst_X`.
- `subst_add`, `subst_mul`, `subst_pow`, `subst_monomial`.
- `coeff_subst_finite`, `coeff_subst`, `HasSubst.comp`.
- `subst_comp_subst_apply`, whose conclusion is
  `subst b (subst a f) = subst (fun s => subst b (a s)) f`.

**Pitfall:** substitution has a dummy value of zero when the outer series is not
a polynomial and admissibility does not hold. Prove the zero constant term and
obtain `HasSubst` before using substitution identities. For the defining inner
series `X*A - C m*X*A^2`, the factor `X` supplies this condition directly.

The first useful new lemma is the finite coefficient formula, assuming the inner
series has constant coefficient zero:

```text
coeff n (compose f g) = sum (k = 0,...,n) (coeff k f * coeff n (g^k)).
```

Derive it from `MvPowerSeries.coeff_subst`, which uses a `finsum` over
`Unit →₀ ℕ`. Available conversion names include `PowerSeries.coeff_def`,
`Finsupp.unique_single`, `AddEquiv.finsuppUnique`, and
`AddEquiv.finsuppUnique_symm`. Prove terms with `k > n` vanish using
`X^k | g^k`. Confirm generated `finsum` helper names with `#check`; do not assume
an unverified `PowerSeries.coeff_comp` exists.

## Coefficients, shifts, and finite products

[PowerSeries/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/PowerSeries/Basic.lean)
contains the following verified declarations:

| Declaration | Purpose |
| --- | --- |
| `PowerSeries.mk`, `coeff_mk` | Construct a series from a coefficient function and read its coefficients |
| `PowerSeries.ext`, `ext_iff` | Equality from equality of every coefficient |
| `constantCoeff`, `coeff_zero_eq_constantCoeff_apply` | Constant coefficient |
| `C`, `X`, `coeff_X`, `coeff_X_pow` | Constants and variable powers |
| `coeff_mul` | Cauchy product over `Finset.antidiagonal n` |
| `coeff_pow`, `coeff_prod` | Finite products indexed by `finsuppAntidiag` |
| `coeff_succ_X_mul`, `eq_X_mul_shift_add_const` | Shift coefficients and split off the constant |
| `X_dvd_iff`, `X_pow_dvd_iff` | Translate powers of `X` dividing a series into vanishing coefficients |
| `X_mul_cancel`, `X_pow_mul_injective` | Cancel powers of `X` without a domain assumption |

Argument order matters in `PowerSeries.coeff_pow (k n : ℕ) (φ : R⟦X⟧)`:
`k` is the power exponent; `n` is the coefficient index. Its formula is

```text
coeff R n (φ^k) =
  ∑ l ∈ finsuppAntidiag (Finset.range k) n,
    ∏ i ∈ Finset.range k, coeff R (l i) φ.
```

Prefer vanishing-coefficient bounds over exact order identities. The paper works
over rings with zero divisors; do not introduce a domain assumption merely to use
`PowerSeries.order_mul`.

## Recommended coefficientwise construction

The following construction plan is implemented in `Series/Triangular.lean`, `Series/Filtration.lean`, and `Series/Construction.lean`. The complete check compiles it.

1. Define normalization explicitly: coefficient zero is zero and coefficient one
   is one. Define `T_m(A)` and `Psi_m(A) = compose A (T_m(A))` using actual series.
2. Define agreement below an index. Prove that normalized `A,B` agreeing below
   `r >= 2` have images agreeing below `r+1`, and that
   `coeff (r+1) (Psi_m(B)-Psi_m(A)) = coeff r (B-A)`.
3. Construct coefficients by strong recursion: `a_0=0`, `a_1=1`, and
   `a_r = -coeff (r+1) (Psi_m(A_<r))`, where the truncated series uses only
   previously constructed coefficients. Use `PowerSeries.mk` for the final series.
4. Prove prefix stability, the defining equation by coefficient extensionality,
   and uniqueness by coefficient induction. No coefficient division is needed.

The perturbation proof uses
`T_m(B)-T_m(A)=X*(B-A)*(1-C m*(A+B))` and differences of powers.
`sub_dvd_pow_sub_pow` exists in `Mathlib.Algebra.GeomSum`, but the stronger degree
bound required by the proof must still be established.

A custom finite coefficient implementation of composition is also possible, but
it must be proved equal to Mathlib substitution under the zero-constant-term
hypothesis. A theorem about a disconnected recurrence is not a completed proof.

## Reduction, parity, and compositional inversion

Verified coefficient-map APIs are `PowerSeries.map`, `coeff_map`, `map_C`,
`map_X`, and `map_comp`. **`map_comp` concerns composition of coefficient ring
homomorphisms, not power-series composition.** Prove the latter compatibility
using the finite coefficient formula. Reduction uses
`Int.castRingHom (ZMod p)` and `PowerSeries.map`.

[ZMod/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/ZMod/Basic.lean)
provides `ZMod.intCast_eq_intCast_iff`, `intCast_zmod_eq_zero_iff_dvd`, and
`intCast_eq_intCast_iff_dvd_sub`.

For parity, define `G = PowerSeries.mk (fun _ => 1)` and `H=X*G` over `ZMod 2`.
`PowerSeries.mk_one_mul_one_sub_eq_one` in
[PowerSeries/WellKnown.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/PowerSeries/WellKnown.lean)
gives `G*(1-X)=1`. Characteristic two gives the needed denominator identity.
Use substitution and cancellation by a unit; the power-series ring is not a field.

[PowerSeries/Inverse.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/PowerSeries/Inverse.lean)
provides **multiplicative** inversion: `invOfUnit`, `mul_invOfUnit`,
`invOfUnit_mul`, and `isUnit_iff_constantCoeff`. These do not construct reversion.
Construct the compositional inverse from `A(B)=X` coefficient by coefficient.
The implementation proves `B(A)=X` by constructing a right inverse of `B` and applying associativity. Derive the actual `F,G` recurrences before applying the existing
checked binary-weight product and sum lemmas in simultaneous induction.

## Congruences and valuation convention

Cancel the parameter in **integer divisibility statements**, not by inventing an
inverse of `m` in `ZMod (m^2)`.

Mathlib's `padicValInt p 0` equals zero, whereas the manuscript assigns infinity.
The exact-divisibility predicate in the handoff therefore needs the required
existence-and-uniqueness theorem for prime `p` and nonzero integer input; do not
leave a valuation statement vacuous. An alternative faithful representation is
`emultiplicity (p : ℤ) a : ℕ∞`.

[Multiplicity.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/Multiplicity.lean)
contains `emultiplicity_zero`, `pow_dvd_iff_le_emultiplicity`,
`emultiplicity_eq_of_dvd_of_not_dvd`, `emultiplicity_mul`, and `emultiplicity_pow`.
Its value at zero is `⊤`, matching the manuscript. Complete the adapter to the
handoff's specified target statements rather than silently changing their meaning.
