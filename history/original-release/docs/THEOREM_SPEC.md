# Mathematical contract for the completed formalization

This is the required meaning of the 16 public declarations in namespace `Hanna.Acceptance`. Internal module and helper names are flexible. Equivalent formulations are acceptable only with proved equivalence and an explanation in the coverage report. Merely declaring these names is insufficient.

All statements concern actual Mathlib `PowerSeries` objects. A sequence defined by a recurrence may be used during construction, but its series must be proved to solve the original equation and identified with the canonical solution.

## Shared definitions and conventions

For any commutative ring \(R\) with identity, write \(R[[x]]\) for formal power series, \(X\) for the series variable, and \(C(u)\) for the constant series with value \(u\in R\). Write \(c_n(U)\) for the coefficient of degree \(n\).

Define
$$
\operatorname{Normalized}(U)\ \Longleftrightarrow\
c_0(U)=0\ \land\ c_1(U)=1.
$$

Use the convention \(\operatorname{compose}(U,V)=U(V(x))\): outer series first. The inner series must have zero constant coefficient whenever that is the side condition used to justify substitution.

For \(m\in R\), set
$$
T_m(U)=XU-C(m)XU^2,\qquad
\Psi_m(U)=\operatorname{compose}(U,T_m(U)).
$$

After proving existence and uniqueness, let \(A_{R,m}\) be that unique normalized solution of \(\Psi_m(A)=X^2\). Define \(B_{R,m}\) as its unique normalized two-sided compositional inverse. For \(R=\mathbb Z\), abbreviate
$$
a_n(m)=c_n(A_{\mathbb Z,m}),\qquad
b_n(m)=c_n(B_{\mathbb Z,m}).
$$

Both coefficient functions are defined for every \(n\in\mathbb N\), including \(a_0=b_0=0\) and \(a_1=b_1=1\). Do not include \(n=0\) in a statement that every coefficient is odd.

For the polynomial parameter ring \(R=\mathbb Z[t]\), take \(t=\texttt{Polynomial.X}\). This is distinct from \(X=\texttt{PowerSeries.X}\). Set
$$
P_n(t)=c_n(A_{\mathbb Z[t],t}),\qquad
Q_n(t)=c_n(B_{\mathbb Z[t],t}).
$$

Write \(s_2(r)=\texttt{Hanna.binaryWeight}(r)\). If an alternative library binary-digit count is used, prove its equality to this function.

For \(p,e\in\mathbb N\) and \(z\in\mathbb Z\), define
$$
E(p,e,z)\ \Longleftrightarrow\
(p:\mathbb Z)^e\mid z\ \land\
\neg\bigl((p:\mathbb Z)^{e+1}\mid z\bigr).
$$

This exact-divisibility predicate gives the finite valuation statements without assigning a false finite value to \(v_p(0)\). Zero has no finite exact exponent. An extended valuation can be used internally, but the endpoints below still require the stated divisibility facts or proved equivalent statements.

## Required endpoints

### 1. `existence_uniqueness`

For every commutative ring \(R\) with identity and every \(m\in R\),
$$
\exists!\, A\in R[[x]],\
\operatorname{Normalized}(A)\ \land\ \Psi_m(A)=X^2.
$$

Do not add field, characteristic-zero, integral-domain, or non-zero-divisor hypotheses. Prove the canonical construction satisfies this property and that every normalized solution equals it. The corresponding manuscript statement is Lemma 3.1.

### 2. `compositional_inverse`

For every such \(R\) and every normalized \(A\in R[[x]]\), there is exactly one normalized \(B\in R[[x]]\) such that
$$
\operatorname{compose}(A,B)=X
\quad\text{and}\quad
\operatorname{compose}(B,A)=X.
$$

Apply this proved theorem to define \(B_{R,m}\). Proving only a multiplicative inverse, or only one composition identity, does not satisfy this endpoint. This is Lemma 2.1.

### 3. `coefficient_polynomial_specialization`

For every \(m\in\mathbb Z\) and \(n\in\mathbb N\),
$$
P_n(m)=a_n(m)\quad\text{and}\quad Q_n(m)=b_n(m).
$$

Here evaluation is the actual ring homomorphism \(\mathbb Z[t]\to\mathbb Z\). Prove compatibility of coefficient maps with legitimate composition and use uniqueness for both the defining series and its inverse. This supports the paragraph after Lemma 3.1 and Remark 6.2.

### 4. `parity_odd`

For every odd integer \(m\), and every \(n\ge1\), \(a_n(m)\) is odd.

The parameter ranges over all integers, including negative odd integers. This is the odd case of Theorem 4.1.

### 5. `parity_even`

For every even integer \(m\),
$$
a_1(m)=1,\qquad
\forall n\ge2,\quad 2\mid a_n(m).
$$

Include \(m=0\) and negative even integers. This is the even case of Theorem 4.1.

### 6. `mod_parameter_squared`

For every integer \(m\ge2\), prove both:
$$
\forall j\in\mathbb N,\quad
m^2\mid a_{2^j+1}(m)-m(-1)^j;
$$
$$
\forall n\ge2,\quad
\bigl(\neg\exists j\in\mathbb N,\ n=2^j+1\bigr)
\ \Longrightarrow\ m^2\mid a_n(m).
$$

Exponentiation of \(-1\) takes place in \(\mathbb Z\). The endpoint covers composite \(m\) as well as prime \(m\). It must include both the exceptional and ordinary indices. This is Theorem 5.1.

### 7–8. `binary_divisibility_polynomial` and `inverse_binary_divisibility_polynomial`

For every \(n\ge1\), respectively,
$$
t^{s_2(n-1)}\mid P_n(t)
\quad\text{and}\quad
t^{s_2(n-1)}\mid Q_n(t)
\quad\text{in }\mathbb Z[t].
$$

The inverse coefficient statement is part of the contract. This is Remark 6.2. Integer-only arithmetic lemmas do not by themselves establish the polynomial version; generalize the relevant divisibility algebra or prove polynomial analogues.

### 9–10. `binary_divisibility_integer` and `inverse_binary_divisibility_integer`

For every integer \(m\ge2\) and every \(n\ge1\), respectively,
$$
m^{s_2(n-1)}\mid a_n(m)
\quad\text{and}\quad
m^{s_2(n-1)}\mid b_n(m).
$$

These are the two parts of Theorem 6.1. They can be obtained by evaluating the polynomial statements. If an integer proof comes first, the polynomial endpoints still remain required.

### 11. `power_of_two_index`

For every integer \(m\ge2\) and every \(k\in\mathbb N\),
$$
m^k\mid a_{2^k}(m).
$$

Include \(k=0\). Use \(s_2(2^k-1)=k\). This is the consequence following Remark 6.2.

### 12. `prime_divisibility_lower_bound`

For every integer \(m\ge2\), natural prime \(p\) with \((p:\mathbb Z)\mid m\), natural \(e\) with \(E(p,e,m)\), and \(n\ge1\),
$$
(p:\mathbb Z)^{\,e\,s_2(n-1)}\mid a_n(m).
$$

Together with the valuation conventions and endpoint 13, this states the lower bound in Corollary 6.3, including zero coefficients. If an extended-valuation inequality is exported instead, explicitly prove the equivalence with this divisibility conclusion.

### 13. `prime_exponent_exists_unique`

For every natural prime \(p\) and every nonzero integer \(z\), there exists exactly one natural \(e\) such that \(E(p,e,z)\). Also prove that there is no natural \(e\) with \(E(p,e,0)\).

Package these facts in this endpoint, or export their conjunction here. This auxiliary result ensures the exact-exponent hypotheses in the valuation endpoints have actual witnesses for the intended parameters; it is not permission to leave those hypotheses unsupported.

### 14. `minimum_prime_exponent_iff`

For every integer \(m\ge2\), natural prime \(p\) with \((p:\mathbb Z)\mid m\), natural \(e\) satisfying \(E(p,e,m)\), and \(n\ge2\),
$$
E(p,e,a_n(m))
\quad\Longleftrightarrow\quad
\exists j\in\mathbb N,\ n=2^j+1.
$$

The hypothesis \(p\mid m\) matters: it forces \(e\ge1\). Do not omit it or silently replace the theorem by a weaker implication. This is the exact classification in Corollary 6.3.

### 15. `residues_parameter_three`

Prove the complete classification for \(n\ge2\):
$$
a_n(3)\equiv
\begin{cases}
3\pmod9,&n=4^k+1\text{ for some }k\ge0,\\
6\pmod9,&n=2\cdot4^k+1\text{ for some }k\ge0,\\
0\pmod9,&\text{otherwise}.
\end{cases}
$$

A conjunction of the two all-\(k\) divisibility assertions and the all-\(n\) assertion outside both classes is a suitable precise formulation. Prove coverage and the even/odd split of \(j\) in \(2^j+1\).

### 16. `residues_parameter_four`

For every $n\ge2$, with $k\in\mathbb N$ in the two exceptional cases,
$$
a_n(4)\equiv
\begin{cases}
4\pmod{16},&n=4^k+1,\\
12\pmod{16},&n=2\cdot4^k+1,\\
0\pmod{16},&\text{otherwise}.
\end{cases}
$$

These last two endpoints correspond to Section 7.

## Typed contract checks

The completed `lean/ContractChecks.lean` must import `Hanna.Acceptance` and typecheck every exported theorem against an explicit mathematical type using the canonical definitions above.

For example, once the real coefficient definition `Hanna.a` exists, the parity contract should have the shape

```lean
-- Illustrative shape, not a currently implemented declaration:
example (m : ℤ) (hm : Odd m) (n : ℕ) (hn : 1 ≤ n) :
    Odd (Hanna.a m n) :=
  Hanna.Acceptance.parity_odd m hm n hn
```

Adapt names and argument order to the actual definitions, while preserving the type's meaning. Do this for every endpoint. Do not use `#check` alone, infer the expected type directly from the exported theorem, assume a target as an extra premise, or substitute a shadow coefficient function.

Also check that the chosen canonical definitions themselves are normalized and satisfy the defining equation and both inverse identities. A polymorphic existence theorem alone does not connect an independently defined coefficient function to its unique solution.

The arbitrary-ring statements must remain polymorphic in the contract file. The polynomial checks must use `Polynomial ℤ` and actual evaluation. The inverse checks must refer to the inverse already connected to the canonical solution.

These contracts are ordinary proof source and require semantic review: a program cannot determine from a declaration's name whether the definitions express this mathematical specification.

## Scope of “complete”

Completion of these endpoints covers the paper's principal theorems, the polynomial strengthening, and its stated arithmetic corollaries. It does not by itself certify every printed numerical example, the bibliography, historical priority, or the claim that an OEIS question remains open. Track those separately. Finite examples can be certified as extra Lean results, but they cannot replace any required endpoint.
