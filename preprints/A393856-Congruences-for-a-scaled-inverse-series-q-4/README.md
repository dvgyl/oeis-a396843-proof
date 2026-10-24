# [Congruences for the series $`A`$ with $`A\bigl(x-x\,A(4x)/4\bigr)=x`$](paper.pdf)

*A proof of two conjectures in OEIS A393856*

Dev D. Goyal  
October 2026

OEIS entry: [A393856](https://oeis.org/A393856) · Lean: [`lean/Entries/A393856.lean`](../../lean/Entries/A393856.lean) · Formalization notes: [`lean/docs/A393856.md`](../../lean/docs/A393856.md)

## Abstract

The sequence A393856 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+6x^3+121x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(4x)/4\bigr)=x`$. The unknown series $`A`$ appears on both sides of this equation, and its coefficients grow very fast. Paul D. Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`5`$, and that a coefficient is odd exactly when its index is a power of $`2`$. We prove both conjectures. In fact we prove two statements that hold with $`4`$ replaced by any positive integer $`q`$: modulo $`q+1`$ the series becomes $`x+x^2+x^3+\cdots`$, and, when $`q`$ is even, modulo $`2`$ it agrees with the generating series of the Catalan numbers, whose odd coefficients sit exactly at the powers of $`2`$. The key observation is that in arithmetic modulo $`q+1`$ the number $`q`$ behaves like $`-1`$, and for $`q=-1`$ the equation can be solved by hand. The results have also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A393856,
  author = {Goyal, Dev D.},
  title = {{Congruences for the series $A$ with $A\bigl(x-x\,A(4x)/4\bigr)=x$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A393856-Congruences-for-a-scaled-inverse-series-q-4/paper.pdf}},
  year = {2026}
}
```
