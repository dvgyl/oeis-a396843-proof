# Independent AI review of the cubic formalization

**Outcome:** no mismatch with the checked OEIS statements, missing integral-existence argument, or hidden mathematical assumption was found in the reviewed modules. The explicit source-statement contracts and axiom audits compiled successfully.

This review was performed on 24 October 2026 by a separate ChatGPT agent from the agent that authored the cubic modules. It is an AI peer review, not an independent human review. Both the proofs and this review are AI generated for Dev Goyal; see `AI_DISCLOSURE.md`.

## Files and source statements checked

The review covered `lean/More/CubicFrobenius.lean`, `lean/More/CubicReversion.lean`, and `lean/More/CubicConsequences.lean`. The original OEIS pages were independently retrieved and compared with the formal declarations.

| Source | Original generating-function equation | Formal identification |
|---|---|---|
| [A389474](https://oeis.org/A389474) | \(A(x^2+2x^3+2A(x)^2)=3A(x)^2\) | `a389474_equation`, `a389474_existence_uniqueness` |
| [A389475](https://oeis.org/A389475) | \(A(3x^2)=2x^2+A(x)^2-2A(x)^3\) | `a389475_equation`, `a389475_existence_uniqueness` |

The normalized condition is explicit: zero constant coefficient and linear coefficient one. It matches the displayed OEIS series and their offset-one coefficients. Uniqueness is correctly stated within this normalized class.

All four listed conjectures have the correct operation and index conventions. In particular, the exponent \(3k\) in A389474 formula (4) is an ordinary power, while \(A(x^3)\) is substitution; the formalization does not confuse either with repeated composition. The condition \(n>3\) in A389474 formula (3) is retained. The Frobenius endpoints additionally cover degree zero and exponent zero, which are valid extensions of the source statements.

## Canonical integral construction

The auxiliary family uses the residual

\[
E_s(A)=A^2+2sA^3-A(3x^2)+2x^2.
\]

The construction divides a residual coefficient by two. The needed divisibility is proved before that quotient is used to establish existence. Modulo two, the residual is \(A(x)^2-A(x^2)\), which is zero by the separately proved characteristic-two Frobenius theorem. Therefore every integral residual coefficient is even.

The perturbation lemma proves that changing a normalized series first in degree \(r\ge2\) changes its residual, through degree \(r+1\), by exactly \(2x\) times that change. Consequently, the half-residual recursion is triangular with coefficient one on the next unknown coefficient. Solving the recursion makes the half-residual zero; evenness then makes the residual itself zero. The proof does not infer residual zero merely from a quotient zero without establishing divisibility.

Uniqueness is proved over the integers by the first differing coefficient and cancellation of multiplication by two. The code does not assert that this uniqueness argument works over coefficient rings with two-torsion. The subsequent modular consequences map the already constructed integral solutions into the relevant residue rings.

For A389474, the auxiliary parameter is \(s=1\), followed by actual compositional reversion. Both directions of the equivalence between the auxiliary equation and the original source equation are proved. The canonical source series therefore has a formal existence and uniqueness theorem. A389475 is the directly constructed auxiliary solution at \(s=-1\).

## Congruence arguments checked

The Frobenius file proves its statement for actual formal power series by passing to a finite polynomial truncation for each coefficient. The truncation bound is proved sufficient for the selected coefficient. Polynomial Frobenius and the prime-field identity then give the full series identity. No finite coefficient table is used as a premise.

For A389474 modulo nine, the inner series \(3A^2\) has square zero. A normalized series, including a normalized inverse, acts as the identity on such an inner argument. Applying the true inverse to the original defining equation consequently gives

\[
A^2=x^2+2x^3\pmod9.
\]

This establishes the whole square identity, including the low-degree coefficients, and therefore implies the stated divisibility for \(n>3\). The use of square-zero substitution is valid over \(\mathbb Z/9\mathbb Z\); it does not assume a field.

For A389475 modulo three, the original equation reduces to \(A^2=x^2+2A^3\), and Frobenius replaces \(A^3\) by \(A(x^3)\). This gives the source's square identity. The two cube-related conjectures are applications of the classical Frobenius identity valid for every integral power series. They should be described as verified resolutions of statements labeled conjectures in the entries, rather than as new general Frobenius theorems.

## Compiler and axiom audit

Independent Lean contracts were checked for both literal source-equation existence-and-uniqueness statements and all four conjecture endpoints. Axiom inspection was run for the general integral construction, both source-equation existence-and-uniqueness theorems, and each conjecture. Every inspected declaration reported exactly:

```text
propext, Classical.choice, Quot.sound
```

A source scan found no admitted proofs, added axioms, `native_decide`, or unsafe or external proof implementation in the three reviewed files. These checks support the formal claims as stated. Historical priority and independent human review remain separate from kernel verification.
