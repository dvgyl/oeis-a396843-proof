# A389537: residues from an alternating binary-power inverse

Prepared for Dev Goyal, 24 October 2026. **AI disclosure:** ChatGPT (OpenAI)
generated the arguments, Lean code, and verification program. Independent
human review is pending. The sequence and conjecture are due to Paul D. Hanna.

## Source and exact theorem

[OEIS A389537](https://oeis.org/A389537) defines the normalized integral series
by

\[
 A(A(x)-x)=A(x)^2,\qquad A(x)=x+O(x^2).
\]

The all-index result is

\[
 [x^n]A(x)\equiv
 \begin{cases}2\pmod4,&n=3\cdot2^k\ (k\ge0),\\
 0\pmod4,&\text{otherwise},\end{cases}\qquad n>2.
\]

The initial coefficients are a(1)=a(2)=1. The offset is one. The independent
observation about sign-run lengths on the OEIS page is **not** proved here.
The residue statement remained explicitly conjectural on the retrieved page.
Exact-identifier and formula searches did not locate an earlier proof; this
bounded search is not an assertion of worldwide novelty or exclusive priority.

## Canonical integral construction and source equivalence

Construct the normalized series R by the equation

\[
 R(x)+R(x^2)=x.
\]

Its solution is the formal lacunary series
\(R(x)=x-x^2+x^4-x^8+\cdots\). Existence and uniqueness hold over any
commutative ring: the map \(U\mapsto x-U(x^2)\) improves the order of a
difference from n to 2n, so its coefficients are determined recursively.
Lean implements this through the existing triangular-recursion theorem.
It then constructs the genuine compositional inverse \(A=R^{\langle-1\rangle}\).
Both inverse identities are proved.

Substitution of A into the R equation gives
\(R(A^2)=A-x\). Composing with A proves the literal OEIS equation
\(A(A-x)=A^2\). Conversely, suppose a normalized U satisfies that literal
equation and let V be its genuine compositional inverse. Composing on the
left with V and then on the right with V gives
\(x-V=V(x^2)\). Uniqueness of R implies V=R and hence U=A. Thus both
existence and uniqueness are proved for the original source equation; the
final theorem does not assume an unconstructed solution.

## Modulo two, followed by exact halving

In characteristic two every series satisfies \(R(x^2)=R(x)^2\). The inverse
equation becomes \(R+R^2=x\), which shows that \(x+x^2\) is R's inverse.
Consequently

\[
 A(x)\equiv x+x^2\pmod2.
\]

Every coefficient of \(A-x-x^2\) is therefore even over the integers.
Define the **integer** correction series

\[
 H=(A-x-x^2)/2.
\]

Lean's coefficientwise division by two is accompanied by an exactness
proof, using the proved parity statement. No division by the zero divisor
two is performed in the residue ring.

## Modulo-four expansion

Work modulo four and write \(A=x+x^2+2H\). Then \(D=A-x=x^2+2H\) has
zero constant coefficient, and valid formal substitution gives

\[
 A(D)=D+D^2+2H(D).
\]

Because D reduces to x squared modulo two,
\(2H(D)=2H(x^2)\) modulo four. Substituting the decomposition into
\(A(D)=A^2\), expanding, and discarding multiples of four yields

\[
 2\bigl(H+H(x^2)\bigr)=2x^3\pmod4.
\]

For coefficients in Z/4, equality after multiplication by two is equivalent
to equality after reduction modulo two. This elementary equivalence is
proved in `Round3.ModFour`, including its coefficientwise series version.
The last identity therefore becomes

\[
 \overline H+\overline H(x^2)=x^3
 \quad\text{or equivalently}\quad
 \overline H+\overline H^2=x^3\quad\text{in }\mathbb F_2[[x]].
\]

The unique zero-constant solution is

\[
 \overline H=\sum_{k\ge0}x^{3\cdot2^k}.
\]

Uniqueness follows coefficient by coefficient: an odd index is determined
immediately and an even index reduces to half that index. In Lean this is
formalized by strong induction and identified with the existing binary
quadratic solution after substitution x cubed. The displayed support then
gives the desired residue theorem for all n>2.

## Formal and numerical evidence

`lean/Round3/LacunaryInverse.lean` contains the construction, source equations,
uniqueness, reductions, and endpoint `Round3.LacunaryInverse.a389537_residue`.
`lean/Round3/LacunaryContracts.lean` checks independently written types against
the literal equation and the exact unbounded coefficient statement.

`scripts/verify_lacunary_inverse.py` computes coefficients directly from
\(A(A-x)-A^2=0\), separately reverses the alternating lacunary series, and
checks equality of the results through degree 80. It checks both inverse
directions, the original functional equation, all residues in that range,
and all 30 displayed OEIS terms. The JSON evidence is
`validation/lacunary_inverse_numeric.json`. These finite computations
corroborate source identification; the all-index proof is the Lean theorem.
