# [The odd-indexed terms of a nested square are even after the first term](paper.pdf)

*A proof of an observation in OEIS A392210*

Dev D. Goyal  
October 2026

OEIS entry: [A392210](https://oeis.org/A392210) · Lean: [`lean/Entries/A392210.lean`](../../lean/Entries/A392210.lean) · Formalization notes: [`lean/docs/A392210.md`](../../lean/docs/A392210.md)

## Abstract

The sequence A392210 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, is defined by an “infinitely nested square” $`x+\mathrm{sq}\Bigl(\frac{x}{1-x}+\mathrm{sq}\Bigl(\frac{x}{1-2x}+\mathrm{sq}\Bigl(\frac{x}{1-3x}+\cdots\Bigr)\Bigr)\Bigr), \qquad \mathrm{sq}(y)=y^2`$. Its terms are $`1,1,4,18,96,579,\dots`$, and the entry observes that the terms $`a(2n-1)`$ with $`n>1`$ appear to be even. We first make the nested expression precise: cutting it off after $`d`$ levels gives the correct coefficients up to degree $`d+1`$, and the resulting series is the unique solution of the simpler equation $`A(x)=x+A\bigl(x/(1-x)\bigr)^2`$. We then prove the observation: once all coefficients are reduced modulo $`2`$, the square of any power series contains only even powers of $`x`$. The same idea also gives a recursive rule for the parity of the even-indexed terms. The main results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A392210,
  author = {Goyal, Dev D.},
  title = {{The odd-indexed terms of a nested square are even after the first term}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A392210-Odd-indexed-terms-of-a-nested-square/paper.pdf}},
  year = {2026}
}
```
