# Independent AI review: the differential and Mahler coefficient proofs

**Disclosure.** A separate OpenAI ChatGPT agent reviewed the mathematical
meaning of these implementations and their source identification. This is an
independent AI review within the same project, not human peer review. Prepared
for Dev Goyal on 2026-10-24. No claim of exclusive priority is made.

## Result and scope

**No mathematical or source-identification gap was found.** The implementations
prove the exact parity conjecture for A397588 and the complete modulus-four
conjecture for A389536. They construct the actual normalized integral source
series, prove their literal defining equations, and prove uniqueness before
using coefficient reduction.

The additional A397588 divisibility-by-three statement is correctly presented
as a verification of a separate assertion already in the OEIS entry. It is
not counted as an additional newly solved conjecture.

The reviewer read:

- [`lean/Round3/DifferentialParity.lean`](../lean/Round3/DifferentialParity.lean);
- [`lean/Round3/MahlerParity.lean`](../lean/Round3/MahlerParity.lean);
- [`lean/Round3/ElementaryContracts.lean`](../lean/Round3/ElementaryContracts.lean);
- [`docs/DIFFERENTIAL_AND_MAHLER_PARITY.md`](DIFFERENTIAL_AND_MAHLER_PARITY.md);
- [`scripts/verify_differential_mahler.py`](../scripts/verify_differential_mahler.py)
  and its numerical evidence;
- the reused definitions of normalization, genuine formal composition,
  coefficientwise triangular recursion, and the previously proved
  characteristic-two power-of-two support theorem.

The review found no reason to change either implementation.

## 1. Official sources and exact index ranges

The reviewer independently reopened both official OEIS entries on 2026-10-24.

| Entry | Official source equation | Official target | Formal match |
|---|---|---|---|
| [A397588](https://oeis.org/A397588) | \(A=x+(xA^2)'\) | For \(n\ge1\), \(a(n)\) is odd exactly at powers of two. | Same normalized differential solution, with the harmless extension \(a(0)=0\). |
| [A389536](https://oeis.org/A389536) | \(A(x)=A(x^2+2x^3)/x\) | For \(n>1\), residue two modulo four occurs exactly at \(n=2^k+1\); other coefficients are divisible by four. | Same normalized series with the explicitly equivalent equation \(A(x^2+2x^3)=xA(x)\). |

Both entries have offset 1. The A389536 entry itself also displays the
multiplied equation used by Lean, so there is no ambiguity about formal
division by \(x\). The normalization in the acceptance contracts is written
explicitly as coefficient zero equal to zero and coefficient one equal to one.

The reviewed source pages still label these two coefficient patterns as
conjectures. A397588 lists divisibility by three for \(n>1\) separately, without
the conjecture label. Both entries credit Paul D. Hanna. The current source
label does not prove global openness or historical priority.

## 2. Differential-series existence and uniqueness

For a commutative coefficient ring, define

\[
T(G)=x+\frac{d}{dx}(xG^2).
\]

The formal implementation uses Mathlib's actual formal derivative. If
\(G=x+O(x^2)\), then \(xG^2\) is divisible by \(x^3\), so its derivative is
divisible by \(x^2\). Thus \(T\) preserves normalization.

If normalized \(G,H\) agree below degree \(r\), then

\[
(G-H)(G+H)=G^2-H^2
\]

is divisible by \(x^{r+1}\). Multiplication by \(x\) raises this to
\(x^{r+2}\), and formal differentiation leaves a result divisible by
\(x^{r+1}\). The order estimate is an inequality: differentiation can
annihilate terms in positive characteristic, but can never lower their order
by more than one. This is exactly the statement proved by `derivative_vanish`.

Consequently, the coefficient in degree \(r\) of a fixed point depends only
on earlier coefficients. The triangular construction has leading coefficient
one and requires no division. The canonical `A` is chosen only after
existence is proved, and strong induction proves uniqueness over every
commutative ring. In particular, there is an actual unique normalized integral
series satisfying the source equation.

The resulting coefficient recurrence is

\[
a_0=0,\quad a_1=1,\qquad
a_n=(n+1)\sum_{j=1}^{n-1}a_ja_{n-j}\quad(n>1).
\]

This matches the recurrence printed in the official entry. The implementation
does not define coefficients by their predicted parity.

## 3. Differential parity and reduction of the derivative

The coefficient of degree \(n\) in a formal derivative is \((n+1)\) times
the coefficient of degree \(n+1\). Therefore coefficientwise ring
homomorphisms commute with differentiation. The implementation proves this
fact coefficientwise and uses uniqueness to identify the reduced integral
series with the canonical solution over the residue ring.

Over \(\mathbb F_2\), the formal Leibniz rule gives

\[
(A^2)'=A A'+A A'=2AA'=0,
\]

and hence \((xA^2)'=A^2\). The reduced source equation becomes

\[
A-A^2=x.
\]

There is no use of analytic differentiation, convergence, division by two, or
a converse inference from a vanishing derivative. The result is obtained
directly from the source equation and the Leibniz rule.

The previously proved formal-series Frobenius coefficient identity identifies
the odd-degree coefficients above degree one as zero and relates the
coefficient of degree \(2m\) to that of degree \(m\). Normalization supplies the
coefficient in degree one. The resulting support is exactly
\(\{2^k:k\ge0\}\), and the integer oddness conversion is made through
`ZMod 2`. At degree zero, both sides of the final equivalence are false.

## 4. The separately stated divisibility by three

Over \(\mathbb F_3\), the normalized series \(x\) satisfies the same source
equation because

\[
x+(x^3)'=x+3x^2=x.
\]

The implementation proves this formal derivative calculation, then applies
the already established uniqueness theorem. It obtains the full series
reduction \(A\equiv x\pmod3\), from which divisibility of every coefficient in
degree greater than one follows.

The theorem comment, proof notes, and endpoint manifest all distinguish this
assertion from the two target conjectures. The source range \(n>1\) is retained.

## 5. Mahler-series construction and uniqueness

Let \(B=x^2+2x^3\) and define the residual

\[
E(G)=xG-G(B).
\]

For a normalized \(G=x+x^2D\), direct expansion gives

\[
E(G)=x^3(D-2)-B^2D(B),
\]

which is divisible by \(x^3\). If \(G-H\) is divisible by \(x^r\) with
\(r\ge2\), then

\[
E(G)-E(H)-x(G-H)=-(G-H)(B)
\]

is divisible by \(x^{2r}\), and therefore by \(x^{r+2}\). Thus the coefficient
in degree \(r+1\) of the residual difference is exactly the coefficient in
degree \(r\) of \(G-H\). This is a coefficient-one triangular relation over an
arbitrary commutative ring, with no invertibility assumption.

The low-degree residual is proved zero separately, the triangular recursion
constructs all remaining coefficients, and strong induction proves uniqueness.
The formal theorem explicitly gives existence and uniqueness of a normalized
series satisfying \(A(B)=xA\). Reduction maps preserve this equation and its
normalization, so reduced integer solutions are correctly identified by
uniqueness.

## 6. The modulus-four comparison and index shift

The comparison series \(H\) used by the proof is an actual previously
constructed normalized solution of

\[
H-H^2=x
\]

over \(\mathbb Z/4\mathbb Z\). Define \(C=x+2xH\). Since
\(B\equiv x^2\pmod2\), formal-series Frobenius gives

\[
H(B)\equiv H^2\pmod2.
\]

The correctly proved `ModFour` transport lemma therefore yields
\(2H(B)=2H^2\) modulo four. The candidate calculation is

\[
\begin{aligned}
C(B)
&=B+2BH(B)\\
&=x^2+2x^3+2x^2H(B)\\
&=x^2+2x^3+2x^2H^2\\
&=x^2+2x^2H=xC.
\end{aligned}
\]

Terms with a factor four vanish, and the penultimate equality uses the
quadratic equation for \(H\). There is no cancellation by two in
\(\mathbb Z/4\mathbb Z\). The candidate is normalized and satisfies the
literal source equation, so uniqueness identifies it with the canonical
reduced source solution.

For \(n>1\), the coefficient of the initial \(x\) term vanishes, leaving

\[
a_n\equiv2[x^{n-1}]H\pmod4.
\]

The reduction of \(H\) modulo two has support at \(2^k\). The formal argument
therefore uses \(n-1=2^k\), then explicitly proves its equivalence to
\(n=2^k+1\) under the source range hypothesis. The endpoint proves both
residue-two and residue-zero equivalences; a separate corollary expresses the
second case as integer divisibility by four.

## 7. Acceptance contracts and finite evidence

The acceptance contracts independently spell out the integer coefficient
domain, both normalizations, both source equations, unconditional existence
and uniqueness, and the exact unbounded index predicates. They do not add
unproved parity assumptions or replace the source-defined sequences with
comparison series.

The reviewer inspected and independently reran the exact-integer numerical
checker. Its newly produced JSON matched
[`validation/differential_mahler_numeric.json`](../validation/differential_mahler_numeric.json)
exactly. This reproduced:

- all 20 displayed A397588 source terms and all 34 displayed A389536 terms;
- the differential equation and parity through degree 500, together with
  divisibility by three for degrees 2 through 500;
- the Mahler source equation through degree 81 using generic polynomial
  composition, independently of the binomial coefficient recurrence;
- the complete A389536 residue pattern and the stronger Catalan comparison
  through degree 2050.

The numerical routines reconstruct coefficients from source recurrences, not
from the conjectured residue patterns. In the Mahler recurrence, contributing
indices satisfy \(\lceil(n+1)/3\rceil\le j\le\lfloor(n+1)/2\rfloor<n\),
matching the code's summation bounds. The Catalan comparison uses coefficient
\(C_{n-2}\), consistent with the two shifts in \(2xH=2x^2C(x)\).

The reviewer also reran the strict parser on the existing 27-endpoint
transitive axiom report. It passed with only `propext`, `Classical.choice`, and
`Quot.sound`. The finite scalar `decide` calls are kernel-checked finite proofs;
the unbounded coefficient conclusions come from the proved recursion and
formal-series arguments. No `sorry`, `admit`, custom axiom, or `native_decide`
was found in the reviewed implementation.

These checks support the source identification and the meaning of the formal
statements. They do not establish historical novelty, OEIS acceptance, human
endorsement, or the unrelated analytic and numerical claims on the source
pages.
