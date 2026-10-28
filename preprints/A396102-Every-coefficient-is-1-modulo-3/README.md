# [Congruences modulo $`3`$ for the series with $`A(A(A(x)))=(1+x)\,A(A(x))`$](paper.pdf)

*A proof of the conjecture in OEIS A396102, and of a family of similar statements*

Dev D. Goyal  
October 2026

OEIS entry: [A396102](https://oeis.org/A396102) · Lean: [`lean/Entries/A396102.lean`](../../lean/Entries/A396102.lean) · Formalization notes: [`lean/docs/A396102.md`](../../lean/docs/A396102.md)

## Abstract

The OEIS entry A396102, contributed by Paul D. Hanna, concerns the power series $`A(x)=x+x^2-2x^3+10x^4-71x^5+616x^6-\cdots`$ determined by the equation $`A(A(A(x)))=(1+x)\cdot A(A(x))`$, which relates the second and third iterates of $`A`$ (the series obtained by substituting $`A`$ into itself). Hanna conjectured that every coefficient of positive degree leaves remainder $`1`$ on division by $`3`$. We prove this, as one case of a family of results: for every $`r\ge1`$, the solution of $`F^{\circ r}=(1+x)\cdot F^{\circ(r-1)}`$ agrees modulo $`r`$ with $`x/(1-x)=x+x^2+x^3+\cdots`$; the case $`r=3`$ is Hanna's conjecture. The key step is to pass to the compositional inverse of the solution, which satisfies a simpler equation, and to observe that $`x/(1+x)`$ solves that equation modulo $`r`$. As by-products, every term of OEIS A140094 is $`1`$ modulo $`3`$, and every term of OEIS A067145 is odd. The main results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396102,
  author = {Goyal, Dev D.},
  title = {{Congruences modulo $3$ for the series with $A(A(A(x)))=(1+x)\,A(A(x))$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A396102-Every-coefficient-is-1-modulo-3/paper.pdf}},
  year = {2026}
}
```
