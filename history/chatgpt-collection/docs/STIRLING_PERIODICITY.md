# Verified factorial Stirling transforms: seven OEIS specializations

**Prepared for Dev Goyal, 24 October 2026.**

**AI disclosure.** OpenAI ChatGPT generated this proof development, Lean formalization,
computational checker, and accompanying explanation. The proof uses established
mathematics and Mathlib. The present review is AI-assisted; independent human review
has not been represented as completed.

The Stirling recurrence and power-expansion helper adapt later upstream Mathlib
code by Beibei Xiong, Yu Shao, Weijie Jiang, and Zhengfeng Yang. Its copyright and
Apache-2.0 license are preserved; see `third_party/mathlib/NOTICE.md` for the exact
source revision and the division between reused and AI-generated work.

## Status and attribution

**These seven results are formalizations of an already proved theorem. They must not
be counted as seven newly solved open problems.**

Payam Danesh, *Eventual periodicity of weighted Stirling transforms and two conjectures
of Bala*, version 1 dated 26 August 2026, proves the general integral-substitution
statement in Theorem 4.1 and Corollary 4.2, with the stronger Carmichael period
`lambda(m)`. That theorem covers every specialization below. The relevant source is
the author's eight-page preprint, DOI
[10.33774/coe-2026-4d6jr](https://doi.org/10.33774/coe-2026-4d6jr),
available through [Cambridge Open Engage](https://www.cambridge.org/engage/coe/article-details/6a883d7ed1922e37d58bbed1).
The current OEIS entries still contain conjecture wording; that wording does not
establish that the mathematics remains open. Our contribution here is a checked
Lean development with explicit onset `n >= m` and concrete sequence definitions.
No priority claim is made for this onset or for the formalization.

An earlier antecedent is Benjamin Schreyer, *Rigged Horse Numbers and their Modular
Periodicity*, Journal of Integer Sequences 28 (2025), Article 25.4.1;
[arXiv:2409.03799v2](https://arxiv.org/html/2409.03799v2).
Its Fubini-number results use finite exponential sums and Carmichael periods. The
present Lean proof uses a triangular power expansion in place of an explicit
inclusion-exclusion sum. It proves the totient bound, not the stronger Carmichael
bound established in the cited literature.

## The precise universal result

Let `c : N -> Z` be any integer sequence, with no restriction on signs or growth.
Let `S(n,k)` denote the Stirling number of the second kind, and put

\[
 B_c(n)=\sum_{k=0}^{n}c_k\,k!\,S(n,k).
\]

For every positive integer `m`, the Lean theorem proves

\[
 \boxed{B_c(n+\varphi(m))\equiv B_c(n)\pmod m
 \quad\text{for all }n\ge m.}
\]

Thus `m` is a uniform sufficient transient bound, independent of the weights.
It is not asserted to be the smallest possible starting index. Define the tail
`f(t) = B_c(m+t) mod m`. Its least positive period exists, is a period of the whole
tail, is no larger than any other positive period, and divides `phi(m)`. All four
properties are present in `transform_exact_tail_period`.

The convention at `m=1` is harmless: `phi(1)=1`, and reduction modulo one is
constant. Zero modulus is excluded.

## Seven exact OEIS specializations

All seven entries have offset **zero**. The table gives the weight `c_k` in the
same universal finite sum. Every named Lean definition fixes the weight completely;
the endpoint theorems have no unproved hypothesis identifying an external sequence.

| Entry | Integer weight `c_k` | Lean definition of the weight |
|---|---|---|
| [A052895](https://oeis.org/A052895) | Catalan number `C_k` | Mathlib's recursive `catalan k` |
| [A064618](https://oeis.org/A064618) | `k!` | `Nat.factorial k`; the summand becomes `(k!)^2 S(n,k)` |
| [A354242](https://oeis.org/A354242) | `binomial(2k,k)` | `Nat.choose (2*k) k` |
| [A167137](https://oeis.org/A167137) | Number of integer partitions of `k` | `Fintype.card (Nat.Partition k)` |
| [A305550](https://oeis.org/A305550) | Number of partitions of `k` into distinct parts | Cardinality of `Nat.Partition.distincts k` |
| [A306082](https://oeis.org/A306082) | Number of partitions of `k` into positive squares | Filter of `Nat.Partition k` requiring every part `a` to satisfy `sqrt(a)^2=a` |
| [A080253](https://oeis.org/A080253) | `A001333(k+1)` | `c_0=1`, `c_1=3`, `c_(k+2)=2c_(k+1)+c_k` |

The source pages were inspected on 24 October 2026. Each contains a conjecture that
the sequence eventually has period dividing the totient modulo each positive
integer. A167137, A305550, and A354242 also state the general integral-substitution
conjecture covered by the universal result.

Source identification details:

- A052895 explicitly gives the factorial Stirling transform of Catalan numbers.
- A064618 explicitly gives `sum S(n,k) (k!)^2`.
- A354242 gives `sum (2k)! S(n,k)/k!` and also identifies the coefficients of
  `(exp(x)-1)^k` as the central binomial coefficients. Multiplication of
  `binomial(2k,k)` by `k!` is exactly the same integer weight.
- A167137 explicitly gives the transform with ordinary partition numbers.
- A305550 identifies the Stirling transform of A088311, and its displayed
  Mathematica formula is `sum S(n,k) PartitionsQ(k) k!`.
- A306082 explicitly gives the transform using A001156, whose defining count is
  partitions into squares. Positive parts are already required by
  `Nat.Partition`; zero is therefore not accidentally allowed as a part.
- A080253 explicitly gives the transform with A001333 at index `k+1`.
  [A001333](https://oeis.org/A001333) begins `1,1,3,7,17,...`; shifting by one
  gives precisely the initial data `1,3` and the recurrence used in Lean.

The paper and code do not claim to resolve other conjectures appearing on these
pages, such as A167137's separate integrality question or A354242's continued
fraction question. A004123 was not included: its current entry mixes offset-one
data with some offset-zero formulas, and no additional result from that entry is
needed for this package.

## Proof corresponding to the Lean development

### 1. A common period for scalar powers

Fix `m>0`, `n>=m`, and a natural base `a`. We claim

\[
 a^{n+\varphi(m)}\equiv a^n\pmod m.
\]

For each prime power `p^e` dividing `m`, split into two cases. If `p` divides `a`,
both powers vanish modulo `p^e`: the inequalities `e <= p^e <= m <= n` ensure
enough factors of `p`. If `p` does not divide `a`, Euler's theorem applies modulo
`p^e`. Since `phi(p^e)` divides `phi(m)`, multiplication by `a^phi(m)` leaves the
residue unchanged. Divisibility by every relevant prime power gives the congruence
modulo `m`. The zero-base case is included because `n` is positive.

This is checked in `More.PowerPeriodicity.pow_totient_add_eq`; a corresponding
natural-number modular-congruence theorem is also provided.

### 2. Powers determine the factorial Stirling columns

Set `T(n,k)=k! S(n,k)`. For `a<=n`, the power expansion gives

\[
 a^n=\sum_{k=0}^{a}\binom{a}{k}T(n,k).
\]

To see this identity algebraically, first write powers in the descending-factorial
basis:

\[
 a^n=\sum_{k=0}^{n}S(n,k)\,a(a-1)\cdots(a-k+1).
\]

The descending-factorial recurrence and the Stirling recurrence prove this by
induction on `n`. Terms with `k>a` vanish, and the remaining descending factorial is
`binomial(a,k) k!`. Both the identity and its truncation are proved in
`More.StirlingNumbers`.

Now fix `k<m`. Subtract the power expansions for exponents `n+phi(m)` and `n`, using
base `a=k`. The scalar power congruence makes their left sides equal modulo `m`.
By strong induction on `k`, all columns with index below `k` already agree.
The last coefficient is `binomial(k,k)=1`, so it follows that

\[
 T(n+\varphi(m),k)\equiv T(n,k)\pmod m.
\]

This argument only cancels an additive term in the ring `ZMod m`. In particular,
it never divides by `k!`, which could be a zero divisor modulo a composite modulus.
The precise helper is `column_periodic_of_powers`.

### 3. Truncation makes the result uniform in the weights

If `k>=m`, then `m` divides `k!`. Consequently, for `n>=m`,

\[
 B_c(n)\equiv\sum_{k=0}^{m-1}c_kT(n,k)\pmod m.
\]

The summation range is now fixed. Every surviving factorial Stirling column has
the period just proved, and arbitrary integer linear combinations preserve that
period. This proves the boxed assertion for every integer weight sequence.

### 4. The exact least period

The auxiliary file `More.TailPeriodicity` treats any sequence `f : N -> alpha`.
It realizes a period as a periodic point of the shift operation and uses Mathlib's
minimal-period results. Applied to the tail beginning at `m`, it proves positivity,
divisibility by `phi(m)`, the period property itself, and minimality. The named
`Axxxxxx_leastPeriod_dvd` corollaries are explicit instances.

## Relation to exponential generating functions

For an integral formal series `G(t)=sum c_k t^k`, the standard coefficient identity

\[
 (e^x-1)^k=k!\sum_{n\ge k}S(n,k)\frac{x^n}{n!}
\]

identifies `B_c(n)` as the coefficient of `x^n/n!` in `G(e^x-1)`. The substitution
is formal: the inner series has zero constant term, so each coefficient receives
only finitely many contributions. No analytic convergence hypothesis is needed.

**Formalization scope:** the Lean universal theorem is stated for the explicit
finite coefficient transform. Its typed definition is exact and unrestricted in
the integer weights. This development does not separately formalize the formal
exponential-series substitution identity above. The seven OEIS applications use
their displayed finite Stirling formulas directly, so they have no such identity
as an unproved Lean assumption. The broader generating-function interpretation is
the mathematical explanation of the finite transform.

## Formal files and endpoints

| File | Role |
|---|---|
| `lean/More/PowerPeriodicity.lean` | Scalar powers modulo arbitrary positive moduli |
| `lean/More/StirlingNumbers.lean` | Recursive Stirling numbers; power expansion |
| `lean/More/StirlingTransform.lean` | Generic transfer and all seven exact definitions |
| `lean/More/TailPeriodicity.lean` | Least positive periods of sequence tails |
| `lean/More/StirlingPeriodicity.lean` | Universal totient theorem and named corollaries |

All Stirling endpoints are in the namespace `More.Stirling`:

- `transform_totient_period`
- `transform_eventually_periodic`
- `transform_exact_tail_period`
- `A052895_period`, `A064618_period`, `A354242_period`, `A167137_period`,
  `A305550_period`, `A306082_period`, `A080253_period`
- The corresponding seven `Axxxxxx_leastPeriod_dvd` declarations.

## Independent finite corroboration

Run `python3 scripts/verify_stirling_periodicity.py`. The script uses integer
arithmetic, a recurrence for `k! S(n,k)`, and separate partition dynamic programs.
It checks the recurrence against the alternating inclusion-exclusion formula for
surjections through degree 18. The recorded run in
`validation/stirling_numeric.json` reports:

- 69 initial OEIS terms matched across the seven offset-zero sequences.
- 190 separate inclusion-exclusion identities checked.
- 81,376 period comparisons over moduli 1 through 128, for the seven named weights
  and an additional signed weight sequence.
- 49,920 scalar-power period comparisons.

These finite computations corroborate the source mapping and help detect indexing
errors. The proofs for all indices and all positive moduli are the Lean theorems.
The package's build and axiom audit provide their verification evidence.
