# Rational theta sums: A380060 and the correction to A380680

**Prepared for Dev Goyal, 24 October 2026. AI-generated mathematics, Lean source, and exposition; independent human review is pending.**

The source sequences and original conjectures are due to Paul D. Hanna. Both entries are dated 6 February 2025 and have raw OEIS offset `0,2`. The sources were inspected on 24 October 2026:

- <https://oeis.org/A380060>
- <https://oeis.org/A380680>

## Results and the false source statement

Write

\[
\Phi(U)=1+2\sum_{j\ge1}x^{j^2}
\left(\frac{U-x^j}{1-x^jU}\right)^j.
\]

Source formula (2) defines A380060 by `A = Phi(A)` and A380680 by `B = Phi(2)`. These are the actual formulas formalized in `lean/Round4/ThetaRational.lean`, using the formal multiplicative inverse of each denominator. The sum is locally finite: its j-th summand is divisible by `x^(j^2)`.

For every positive n, the proofs give

\[
[x^n]A\equiv
\begin{cases}2\pmod4&n=j^2\text{ for some }j\ge1,\\0\pmod4&\text{otherwise},\end{cases}
\]

and

\[
[x^n]B\equiv
\begin{cases}2\pmod4&n=2j^2\text{ for some }j\ge1,\\0\pmod4&\text{otherwise}.\end{cases}
\]

The A380060 statement proves its retrieved conjecture. The retrieved A380680 comment instead claims square support; that claim is false. Lean proves the exact coefficients `[x]B=4` and `[x^2]B=6`, and separately proves the negation of each universal clause of the source comment. The first coefficient refutes residue two at all square indices. The second refutes divisibility by four at all nonsquare indices. The complete twice-square classification is a corrected replacement, not a proof of the original assertion.

## The actual implicit series exists uniquely

The construction works over any commutative coefficient ring. Every denominator `1-x^j U` has constant coefficient one, so its multiplicative inverse exists even when the coefficient ring has zero divisors.

If `U-V` is divisible by `x^n`, then the differences of the corresponding inverses are also divisible by `x^n`. This follows from the exact identity

\[
D^{-1}-E^{-1}=D^{-1}(E-D)E^{-1}.
\]

Consequently, the difference between the two rational powers in the j-th summand is divisible by `x^n`. Multiplication by `x^(j^2)` increases the known vanishing by at least one, because `j>=1`. Thus

\[
U\equiv V\pmod{x^n}\quad\Longrightarrow\quad
\Phi(U)\equiv\Phi(V)\pmod{x^{n+1}}.
\]

This gives an integral triangular coefficient recursion for a unique fixed point. The Lean proof constructs that fixed point over every commutative ring, proves its source equation and uniqueness, and proves compatibility with every coefficient-ring homomorphism. Its constant coefficient is automatically one; no unproved boundary assumption is supplied.

The finite definition of the coefficient sum uses indices `0<=k<=n`, with source index `j=k+1`. The theorem `sigma_coeff_finsum` proves equality with the literal coefficientwise infinite sum. All omitted terms vanish by the proved support bound.

## Reduction modulo four

The factor two allows each summand to be computed modulo two before lifting its doubled value modulo four. This uses the proved finite-ring equivalence

\[
2u=2v\text{ in }\mathbb Z/4\mathbb Z
\quad\Longleftrightarrow\quad
u=v\text{ after reduction to }\mathbb Z/2\mathbb Z.
\]

There is no cancellation of two in a ring where it is a zero divisor.

For the implicit series, `A=Phi(A)` first gives `A=1` modulo two. Hence

\[
\frac{A-x^j}{1-x^jA}\equiv
\frac{1-x^j}{1-x^j}=1\pmod2.
\]

Each summand therefore reduces to `x^(j^2)`, and

\[
A\equiv1+2\sum_{j\ge1}x^{j^2}\pmod4.
\]

For the explicit series, the constant parameter two reduces to zero. In characteristic two,

\[
\frac{2-x^j}{1-2x^j}\equiv x^j.
\]

Its j-th power contributes another factor `x^(j^2)`, so

\[
B\equiv1+2\sum_{j\ge1}x^{2j^2}\pmod4.
\]

Positive squares have distinct exponents. The formal proof establishes that fact when extracting coefficients, and handles the positive-index restriction explicitly.

## Source coverage and limits

Both OEIS entries also give a bilateral expression involving negative powers. The checked formal source is their positive-index formula (2). The usual bilateral pairing is justified informally by replacing j with -j in the rational summand and cancelling powers; a formal Laurent-series equivalence is not asserted by this package. No analytic convergence, asymptotic formula, or numerical special-value statement is claimed.

Exact-identifier and equation searches on both search engines found no relevant earlier proof of the selected statements. No matching identifier appeared in the inspected `awesome-ai-proofs` catalogue or in the primary DeepMind OEIS theorem mapping linked from the AlphaProof Nexus results repository. These are bounded retrieval checks, not a proof of global novelty or priority.

## Formal acceptance endpoints

The complete fixed list is `validation/round4_theta_rational_endpoints.json` (31 endpoints). It includes the inverse identity, locally finite sum, generic existence and uniqueness, homomorphism transport, exact source coefficient formulas, both entire-series congruences, the all-index classifications, the integer divisibility iff statements, the exact counterexamples, and both refutations.

The independent typed contracts in `lean/Round4/ThetaRationalContracts.lean` spell out the sums and rational factors, including the shift `j=k+1`, rather than accepting an arbitrary sequence with an assumed congruence.

## Independent numerical corroboration

`scripts/verify_theta_rational.py` uses exact integers and the Python standard library. At its defaults it:

- Matches all 27 displayed A380060 terms and all 36 displayed A380680 terms.
- Constructs the implicit A380060 series directly from the source equation through degree 80.
- Checks all relevant denominator/quotient identities through degree 80.
- Checks the implicit source equation through degree 80 again using a separate binomial expansion that does not call the inverse routine.
- Computes A380680 directly from a binomial coefficient formula through degree 1030 and independently compares it with the literal rational sum through degree 80.
- Checks both complete residue classifications over those respective ranges and records both exact counterexamples.

The evidence is `validation/theta_rational_numeric.json`; the complete release checker reruns the program. These finite computations corroborate the definitions and exposition. Lean provides the universal proofs.
