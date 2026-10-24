# A393172, A393171, and an elementary A392210 consequence

Prepared for **Dev Goyal**, 24 October 2026.

**AI disclosure.** OpenAI ChatGPT generated the proofs, Lean source, checking program, and this exposition in response to Dev Goyal's request. Review during preparation was AI-assisted; independent human review is pending. This document does not claim publication, OEIS acceptance, exclusive priority, or an exhaustive exclusion of prior proofs.

## Source statements and exact scope

The official entries were inspected on 24 October 2026. Paul D. Hanna submitted A393171 and A393172 on 4 February 2026 and A392210 on 2 February 2026. The two Catalan-related entries still labeled the targeted assertions as conjectures. A392210 used tentative wording for its parity observation.

| Entry | Raw offset | Exact source series used | Proved assertion |
|---|---|---|---|
| [A393172](https://oeis.org/A393172) | `1,2` | The normalized series `A` satisfying `A(x−x²)=x+A(x)²` | For every `n>1`, `a(n)≡2 (mod4)` exactly when `n=2^k`, `k≥0`; all other terms in this range are divisible by four. |
| [A393171](https://oeis.org/A393171) | `1,3` | The normalized series `B` satisfying `B=x+B(C(x))²`, where `C=x+C²`; equivalently `B(x−x²)=x−x²+B(x)²` | For every `n>2`, `b(n)≡4 (mod8)` exactly when `n=2^k` or `n=2^k+1`, `k≥1`; all other terms in this range are divisible by eight. |
| [A392210](https://oeis.org/A392210) | `1,3` | The normalized series `D=x+D(x/(1−x))²`, the entry's formula (1) | `d(2n−1)` is even for every `n>1`. This is an elementary consequence of the standard characteristic-two square identity, not a new general mathematical principle. |

Here “normalized” means constant coefficient zero and coefficient of `x` equal to one. All multiplication and displayed squares are ordinary series multiplication; `F(G(x))` denotes composition. The source's second offset component is preserved as metadata, not treated as the mathematical starting index.

The A393172 integer recurrence used in the independent verifier is also credited in its OEIS entry to Seiichi Manyama, 15 July 2026. The formal proof constructs the series directly and does not assume that recurrence or any checked table of coefficients.

## 1. An actual series construction

Let `P,T` be any normalized formal power series over a commutative ring. Define

\[
\Phi(G)=T+G(P)^2.
\]

If `G,H` are normalized and `G−H` is divisible by `x^r`, then

\[
\Phi(G)-\Phi(H)
=(G(P)-H(P))(G(P)+H(P))
\]

is divisible by `x^(r+1)`. Composition with normalized `P` preserves the first divisibility, and the second factor has constant coefficient zero. Thus each next coefficient is determined by preceding coefficients, with coefficient one on the unknown. A triangular recursion constructs the solution over every commutative ring, with no divisions or completeness assumptions left informal. The same order improvement proves uniqueness by induction on coefficient degree.

`Round4.SquareComposition.existence_uniqueness` proves this construction. `map_solution` proves compatibility with coefficient-ring maps. These results are used for the actual source series below; the desired residues are never hypotheses of the construction or of the explicit source contracts.

## 2. A393172 modulo four

Let `C` be the normalized Catalan series satisfying

\[
C-C^2=x,
\qquad N=x-x^2.
\]

The identity `N(C)=x` and the normalized inverse theorem yield `C(N)=x`. Composing the A393172 source equation with `C` gives

\[
A=C+A(C)^2.
\]

The reverse implication follows by composing with `N`; both directions are checked in `source_iff_fixed`. The generic construction with `P=T=C` therefore gives the unique normalized solution of the literal source equation over every commutative ring.

Now work over `Z/4Z` and put `Q=2C−x`. It is normalized and

\[
Q(N)=2x-(x-x^2)=x+x^2,
\qquad
x+Q^2=x+x^2,
\]

because every other term in the square is a multiple of four. Source uniqueness gives the entire-series identity

\[
\boxed{A\equiv2C-x\pmod4.}
\]

Over the field with two elements, `C−C²=x` implies that its coefficient at degree `n` is one exactly when `n` is a power of two. This standard binary-support fact is proved in the earlier `ScaledParity` module and reused here. At every `n>1`, the `−x` correction vanishes, yielding exactly the claimed two residue cases.

Principal endpoints in namespace `Round4.CatalanComposition` are `a393172_existence_uniqueness`, `A_equation`, `A_unique`, `map_A`, `A_mod_four`, `a393172_residue`, and `a393172_four_dvd_iff`.

## 3. A393171 modulo eight

Define `B=x+A²` over the integers, using the actual A393172 series. Its source equation follows by substitution:

\[
B(N)=N+A(N)^2=N+(x+A^2)^2=N+B^2.
\]

Also `B(C)=A`, so `B=x+B(C)²`. Conversely, composing the source equation with `C` gives this same fixed-point equation. The generic construction with `P=C,T=x` proves uniqueness, identifying `B` with both source formulations in A393171.

The proof must retain enough information for reduction modulo eight. The already proved congruence modulo four implies an **exact integral** decomposition

\[
A=2C-x+4K.
\]

In Lean, `K` is defined coefficientwise by dividing `A−(2C−x)` by four. The preceding congruence proves that each division is exact; no cancellation by a nonunit in a residue ring is used. Squaring and reducing modulo eight then gives

\[
\begin{aligned}
B&\equiv x+(2C-x)^2\\
 &=x+x^2+4(C^2-xC)\\
 &=x+x^2+4(C-x-xC)\pmod8.
\end{aligned}
\]

For `n>2`, the relevant residue is therefore four times

\[
[x^n]C-[x^{n-1}]C\pmod2.
\]

The two summands are nonzero exactly when `n` and `n−1`, respectively, are powers of two. They cannot both be powers of two when `n>2`: both powers would have positive exponent and hence be even, whereas their difference is one. The coefficient is consequently one modulo two exactly when either condition holds. The positivity of the exponent follows from `n>2`, giving precisely `k≥1` in the source assertion.

Principal endpoints are `a393171_existence_uniqueness`, `a393171_named_existence_uniqueness`, `B_equation`, `B_fixed`, `B_composed_catalan`, `B_unique`, `map_B`, `A_integer_decomposition`, `B_mod_eight`, `a393171_residue`, and `a393171_eight_dvd_iff`.

## 4. The A392210 observation

The generic construction with `P=x/(1−x)` and `T=x` gives the actual normalized series `D`. The rational argument is represented by the formal geometric series and is certified by `P(1−x)=x`.

Reducing `D=x+D(P)²` modulo two, the square has support only in even degrees. Hence all odd-degree coefficients above degree one vanish modulo two. In the source's indexing, this is `d(2n−1)` even for all `n>1`. This short deduction is included as coverage of a source observation and is expressly classified as elementary.

The endpoints in `Round4.NestedBinomial` are `existence_uniqueness`, `A_equation`, `rational_argument`, and `a392210_odd_indices`.

## Formal contracts and checks

The four new Lean files are:

- `lean/Round4/SquareComposition.lean`
- `lean/Round4/CatalanComposition.lean`
- `lean/Round4/NestedBinomial.lean`
- `lean/Round4/CatalanContracts.lean`

`CatalanContracts` restates the original equations and coefficient normalizations explicitly. Its `first_arbitrary_source`, `second_arbitrary_source`, and `third_arbitrary_source` theorems start from **any** normalized integer series satisfying the respective literal source equation and conclude the all-index assertions. This prevents a correct theorem about a conveniently chosen unrelated series from passing as a solution of an OEIS problem.

`validation/round4_catalan_endpoints.json` contains 39 fixed endpoints, including construction, mapping, source identification, residue theorems, and typed contracts. This is an audit count, not a count of conjectures. No proof uses `sorry`, `native_decide`, an added mathematical axiom, or a numerical table as a premise. Small finite computations over `ZMod 4` and `ZMod 8` use kernel-checked `decide`.

The independent exact-integer script `scripts/verify_catalan_composition.py` checks:

- all 24 displayed terms in each of the three official entries, for 72 source terms total;
- two independently derived recursions for both Catalan-related series through degree 520: direct source-coefficient extraction and a positive recursion using exact coefficients of powers of `C`;
- the relation `B=x+A²`, both full-series reductions, and both residue classifications through degree 520;
- each literal source equation and the compositional identities through degree 80, using direct polynomial multiplication;
- the A392210 odd-index evenness observation through index 519 and its literal source equation through degree 80.

The recorded result is `validation/catalan_composition_numeric.json`. These finite checks are corroboration; the universal proofs are in Lean. The integrated release checker supplies the final fresh-compilation and transitive-axiom records.

## Bounded prior-art search

Exact-identifier searches for `A393172`, `A393171`, and `A392210`, combined with “proof”, “conjecture”, or the targeted residue wording, returned the official OEIS entries and unrelated identifier collisions. A search for the A393172 defining equation and modulus also found no relevant earlier proof. The package's broader round-four search additionally inspected the AI-proof catalog and the DeepMind OEIS theorem mapping for the entry identifiers. None of these bounded searches establishes global novelty or excludes an unpublished or differently indexed proof. The source conjecture labels and the proof coverage in this package are the claims made here.
