# Manuscript and Lean coverage

All 16 required endpoints are proved. Their public names have the prefix `Hanna.Acceptance.`. They are defined in [Acceptance.lean](../lean/Hanna/Acceptance.lean). [ContractChecks.lean](../lean/ContractChecks.lean) independently restates each expected type against the actual canonical series.

The [complete-check report](../reproducibility/lean_complete/report.json) records compilation, theorem types, transitive axioms, and source hashes. A separate AI source review checked the meanings of these types. The user has confirmed that human verification is complete. See the [public review summary](PUBLIC_REVIEW.md) for the scope and limits of the reviews.

## Required results

| Manuscript result | Endpoint suffix | Main internal proof | Scope and interpretation |
| --- | --- | --- | --- |
| Lemma 3.1 | `existence_uniqueness` | `Hanna.Series.existence_uniqueness` in `Series/Construction.lean` | Every commutative ring with identity and every parameter. Exactly one normalized solution of the original equation. |
| Lemma 2.1 | `compositional_inverse` | `Hanna.Series.compositional_inverse` in `Series/Inverse.lean` | Every normalized series has exactly one normalized inverse with both composition identities. |
| Paragraph after Lemma 3.1; Remark 6.2 | `coefficient_polynomial_specialization` | `Hanna.coefficient_polynomial_specialization` in `Canonical.lean` | Actual evaluation of both polynomial coefficient families at every integer parameter and natural index. |
| Theorem 4.1, odd case | `parity_odd` | `Hanna.Parity.odd_coeff` in `Parity.lean` | All odd integers, including negative values; every index at least one. |
| Theorem 4.1, even case | `parity_even` | `Hanna.Parity.even_coeff` in `Parity.lean` | All even integers, including zero and negative values; first coefficient one and all later coefficients even. |
| Theorem 5.1 | `mod_parameter_squared` | `Hanna.mod_parameter_squared` in `ModSquare.lean` | Every integer parameter at least two. Both the exceptional powers-of-two branch and all other indices. |
| Remark 6.2, solution | `binary_divisibility_polynomial` | `Hanna.binary_divisibility_polynomial` in `BinaryDivisibility.lean` | Divisibility in `Polynomial ℤ` by `Polynomial.X ^ binaryWeight (n-1)`, for every positive index. |
| Remark 6.2, inverse | `inverse_binary_divisibility_polynomial` | `Hanna.inverse_binary_divisibility_polynomial` in `BinaryDivisibility.lean` | The same polynomial statement for coefficients of the actual compositional inverse. |
| Theorem 6.1, solution | `binary_divisibility_integer` | `Hanna.binary_divisibility_integer` in `BinaryDivisibility.lean` | Required range: parameter at least two and index at least one. The internal result allows every integer parameter. |
| Theorem 6.1, inverse | `inverse_binary_divisibility_integer` | `Hanna.inverse_binary_divisibility_integer` in `BinaryDivisibility.lean` | The same required range for inverse coefficients. The internal result also allows every integer parameter. |
| Consequence after Remark 6.2 | `power_of_two_index` | `Hanna.power_of_two_index` in `BinaryDivisibility.lean` | `m^k` divides the coefficient at index `2^k`, including `k = 0`. |
| Corollary 6.3, lower bound | `prime_divisibility_lower_bound` | `Hanna.prime_divisibility_lower_bound` in `Corollaries.lean` | Divisibility by the prime power with exponent `e * binaryWeight (n-1)`. Includes zero coefficients. |
| Valuation convention before Corollary 6.3 | `prime_exponent_exists_unique` | `Hanna.prime_exponent_exists_unique` in `PrimeExponent.lean` | Every nonzero integer has a unique finite exact exponent for a prime. Zero has none. |
| Corollary 6.3, equivalence | `minimum_prime_exponent_iff` | `Hanna.minimum_prime_exponent_iff` in `Corollaries.lean` | Exact exponent equals the parameter's exponent if and only if `n = 2^j + 1`. Includes the required hypothesis that the prime divides the parameter. |
| Section 7, parameter three | `residues_parameter_three` | `Hanna.residues_parameter_three` in `ModSquare.lean` | Residues 3, 6, and 0 modulo 9, with both exceptional classes and their complement. |
| Section 7, parameter four | `residues_parameter_four` | `Hanna.residues_parameter_four` in `ModSquare.lean` | Residues 4, 12, and 0 modulo 16, with both exceptional classes and their complement. |

## Connection to the actual series

`Hanna.Series.Normalized U` means that coefficients zero and one are zero and one. `Hanna.Series.compose U V` is `MvPowerSeries.subst (fun (_ : Unit) => V) U`. The outer series is first. The proof supplies a zero constant coefficient for the inner series whenever it uses a substitution identity.

`Hanna.Series.T m U` is `X * U - C R m * X * U^2`. `Hanna.Series.Psi m U` is `compose U (T m U)`. `coeff_compose` proves the finite coefficient formula from Mathlib substitution. Associativity and coefficient-map compatibility are also proved.

`Series/Filtration.lean` expresses coefficient agreement as divisibility by a power of the series variable. Its `psi_perturbation` lemma proves the coefficient change used in Lemma 3.1. `Series/Triangular.lean` constructs successive coefficients by well-founded recursion. `solution_exists` and `solution_unique` prove the equation and uniqueness before `solution` chooses a witness.

`Hanna.A m` is this solution. `Hanna.B m` is the inverse obtained from the proved inverse existence theorem. `A_normalized`, `A_equation`, `B_normalized`, `A_comp_B`, and `B_comp_A` state their required properties. The integer coefficients `a` and `b` are actual `PowerSeries.coeff` values. The polynomial coefficients `P` and `Q` are the same values over `Polynomial ℤ`, with parameter `Polynomial.X`.

## Recurrence and induction connections

| Written proof step | Lean declaration | Connection |
| --- | --- | --- |
| Factor the initial variable from the solution and inverse | `Hanna.A_eq_X_mul_F`, `Hanna.B_eq_X_mul_G` | `F` and `G` are coefficient shifts of the actual series. |
| Translate shifted indices | `Hanna.f_eq_coeff_A`, `Hanna.g_eq_coeff_B` | Shifted index `r` is coefficient index `r + 1`. |
| Apply the left inverse to the defining equation | `Hanna.T_A_eq_compose_B` | Proves `T m (A m) = compose (B m) (X^2)`. |
| Identity before the first recurrence in Section 6 | `Hanna.F_equation` | Proves `F m = compose (G m) (X^2) + C R m * X * (F m)^2`. Cancellation by a power of `X` is valid over arbitrary rings. |
| First coefficient recurrence | `Hanna.f_recurrence` | For `r ≥ 1`, the even-index term is `g m (r/2)`. The other term is `m` times the full Cauchy product at index `r-1`. |
| Second coefficient recurrence | `Hanna.g_recurrence` | Derived from `A(B) = X` and the finite composition formula. It includes the coefficient `-f m r` and all intermediate terms. |
| Coefficients of powers | `Hanna.binary_coeff_pow_dvd` | Proved by induction using the actual Cauchy product and binary addition inequality. Multiplicities are retained. |
| Simultaneous induction | `Hanna.binary_divisibility_shifted` | Proves divisibility of both `f m r` and `g m r`. The current `f` result is proved before the current `g` result. |

The binary proof works over every commutative ring. Its polynomial and integer versions are direct instances. The specialization theorem is proved separately by coefficient maps and uniqueness. Thus neither polynomial endpoint relies on an integer-only divisibility assertion.

## Equivalent proof choices

The manuscript proves Theorem 5.1 with an auxiliary sparse series. Lean uses the proved recurrences. `parameter_dvd_fg` first proves that all positive shifted coefficients are divisible by `m`. `square_dvd_g_add_f` then gives `g_r ≡ -f_r` modulo `m²`. The first recurrence gives `f_1 = m`, `f_(2r) ≡ -f_r`, and zero for odd shifted indices greater than one. Induction gives the alternating residue at powers of two and zero elsewhere. The index bridges convert this to exactly the two specified branches for `a_n(m)`.

`Hanna.ExactExponent p e z` is the specified conjunction: `p^e` divides `z`, and `p^(e+1)` does not. This is the finite meaning of the manuscript's prime valuation. `prime_exponent_exists_unique` supplies witnesses for nonzero integers and excludes zero. The lower-bound endpoint is divisibility, so it remains true at zero. The minimum-exponent proof uses the residue theorem and `p ∣ m` to obtain `e ≥ 1`; it does not assume coefficients are nonzero.

`power_two_index_split` proves the even/odd exponent split used in the two concrete residue classifications. It supplies coverage of both exceptional classes.

## Scope outside the endpoints

The original binary-digit and integer-divisibility modules contain 23 supporting theorems and remain unchanged. The Python verifier checks finite examples and identities independently from the defining equation. Printed numerical examples are not all separate Lean declarations. The bibliography, novelty, historical priority, and current OEIS status are outside this formalization claim.
