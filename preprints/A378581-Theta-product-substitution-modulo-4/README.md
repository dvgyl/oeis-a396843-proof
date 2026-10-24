# [Remainders modulo $`4`$ for the series with $`A\bigl(x\,A(x)\bigr)=\theta_3(x)`$](paper.pdf)

*A proof of a conjecture in OEIS A378581*

Dev D. Goyal  
October 2026

OEIS entry: [A378581](https://oeis.org/A378581) · Lean: [`lean/Entries/A378581.lean`](../../lean/Entries/A378581.lean) · Formalization notes: [`lean/docs/A378581.md`](../../lean/docs/A378581.md)

## Abstract

Let $`\theta(x)=1+2x+2x^4+2x^9+2x^{16}+\cdots`$ be the Jacobi theta series $`\theta_3`$, whose coefficient of $`x^n`$ is $`2`$ when $`n`$ is a positive perfect square and $`0`$ otherwise. Entry A378581 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=1+2x-4x^2+24x^3-206x^4+\cdots`$ determined by $`A\bigl(x\,A(x)\bigr)=\theta(x)`$. The entry conjectures that for $`n>0`$ the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We prove this conjecture. In fact, modulo $`4`$ the whole series $`A(x)`$ agrees with $`\theta(x)`$, and the same is true for the companion equation $`A\bigl(x/A(x)\bigr)=\theta(x)`$ of entry A378580. The proof rests on one observation: modulo $`4`$, twice a series does not change when its argument is changed by a multiple of $`2`$. The results were checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A378581,
  author = {Goyal, Dev D.},
  title = {{Remainders modulo $4$ for the series with $A\bigl(x\,A(x)\bigr)=\theta_3(x)$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A378581-Theta-product-substitution-modulo-4/paper.pdf}},
  year = {2026}
}
```
