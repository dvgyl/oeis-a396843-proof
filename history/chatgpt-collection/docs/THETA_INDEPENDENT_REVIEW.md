# Independent AI semantic review: A378580 and A378581

**Reviewer disclosure.** This review was performed on 24 October 2026 by a separate ChatGPT agent from the agent that wrote `Round3/ThetaSubstitution.lean`. It is an AI review, not independent human review. It does not establish historical priority or OEIS acceptance.

## Scope and conclusion

The reviewer read all of `lean/Round3/ThetaSubstitution.lean`, all of `lean/Round3/ThetaContracts.lean`, the accompanying mathematical explanation, and the current official entries [A378580](https://oeis.org/A378580) and [A378581](https://oeis.org/A378581). The review checked the correspondence between the source definitions and the formal objects, the construction and uniqueness arguments, boundary indices, and the meaning of the final claims.

**Result: the formal statements faithfully cover both source coefficient conjectures.** No mismatch of source equation, normalization, index offset, multiplication versus composition, or conditional existence was found.

## Source definitions and constants

A378580 uses the equation `A(x/A(x))=theta₃(x)`, and A378581 uses `A(xA(x))=theta₃(x)`. Both have offset zero and constant coefficient one. The module assigns A378580 to its `minus` construction and A378581 to its `plus` construction, with these exact respective equations.

The function `unitInv` is defined using Mathlib's `PowerSeries.invOfUnit A 1`. The file proves that it is the multiplicative inverse whenever `A(0)=1`, proves its uniqueness and involutivity, and proves that it commutes with valid substitution and coefficient maps. The theorem `a378580_quotient_identity` explicitly establishes `A*(X*unitInv A)=X`. Thus the inner argument represents the formal quotient by the unit `A`; it is not being confused with compositional reversion.

The theta series is defined coefficientwise as `1+2S`, where `S` is one at positive square indices and zero at every other index. In particular, `S(0)=0` and `theta(0)=1`. The coefficient contract states exactly that the positive-index coefficient is two if `n=k²` for some natural `k`, and zero otherwise. Since the theorem assumes `n>0`, the square `0²` introduces no exceptional case.

## Construction and uniqueness

The proof first constructs the unique normalized series `G=x+O(x²)` satisfying `G(G(x))=G(x)T(x)` whenever `T(0)=1`. At an arbitrary first differing degree `r`, changing the outer and inner copies of `G` contributes the coefficient difference twice, while changing `GT` contributes it once. The residual therefore has leading coefficient exactly the coefficient difference. The triangular construction consequently needs no division and works over every commutative ring, including the integers and `ZMod 4`.

The transition from `G=xU` to `U(xU)=T` uses cancellation by `G`. The code justifies this cancellation by separating the injective factor `x` and the invertible factor `U`, rather than assuming every nonzero formal series can be cancelled over arbitrary rings. This is sufficient even in rings with zero divisors.

The quotient construction is `Minus(T)=Plus(T⁻¹)⁻¹`. Its proof uses genuine multiplicative inverses and derives both the source equation and uniqueness. The final named integer series are canonical constructions, not placeholders whose existence is assumed.

## Reduction and residue assertions

The reduction argument is valid in `ZMod 4`: multiplying a substitution perturbation by two eliminates its multiple-of-two change. It proves that `theta` itself solves the plus equation. Since `(1+2S)²=1`, the same series solves the minus construction. Uniqueness and the separately proved compatibility with coefficient maps then identify the reductions of the actual integer sequences.

The final whole-series equalities imply the exact coefficient statements for every positive natural index. The source's two clauses are represented both as the residue equality and as explicit equivalences:

- Residue two modulo four holds exactly at square indices.
- Integer divisibility by four holds exactly at nonsquare indices.

The constant terms are excluded by the positive-index hypothesis, as required by the source. There is no bound on the index in any of these conclusions.

## Bounded prior-art check

The reviewer also inspected [A196523](https://oeis.org/A196523), including Amol Bhave's proof comment dated 13 October 2026. That comment treats the family `A=x+xA^[l]`, with congruences modulo `l−1` proved by comparison with `x/(1−x)`. The entry links neighboring A378575 and A378576. The statement in that comment does not assert the theta substitution theorem formalized here; its hypotheses and source equations differ. This observation rules out direct coverage by that particular displayed result. It is not a claim that all relevant literature has been searched.

The reviewed A378580 and A378581 pages still label the target coefficient patterns conjectures. Neither this label nor the absence of a linked proof proves global novelty. The package's bounded status language and pending human-review disclosure should be retained.

## Limits of this review

This review addresses mathematical meaning and proof structure. The project-wide Lean build and axiom audit separately check proof terms and transitive dependencies. The independent exact-integer checker separately corroborates source prefixes and literal equations for finite ranges. None of those checks establishes publication priority or resolves the analytic radius-of-convergence question also appearing in A378580.
