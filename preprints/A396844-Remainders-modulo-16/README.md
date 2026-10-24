# [Remainders modulo $`16`$ for the series $`A(xA-4xA^2)=x^2`$](paper.pdf)

*The correct form of a conjecture in OEIS A396844*

Dev D. Goyal  
October 2026

OEIS entry: [A396844](https://oeis.org/A396844) · Lean: [`lean/Entries/A396844.lean`](../../lean/Entries/A396844.lean) · Formalization notes: [`lean/docs/A396844.md`](../../lean/docs/A396844.md)

## Abstract

Entry A396844 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=x+4x^2+28x^3+288x^4+\cdots`$ determined by the equation $`A\bigl(xA(x)-4xA(x)^2\bigr)=x^2`$. The entry conjectures that, for $`n>8`$, the remainder of $`a(n)`$ on division by $`16`$ is $`12`$ when $`n=2\cdot4^k+1`$, and $`0`$ otherwise. We show that the first half of this statement is true and the second half is not: for every $`n=4^k+1`$ the remainder is $`4`$, the first exception after $`n=8`$ being $`n=17`$. The complete rule, which we prove, is: for $`n\ge2`$, the remainder is $`4`$ if $`n=4^k+1`$, it is $`12`$ if $`n=2\cdot4^k+1`$, and it is $`0`$ otherwise. We also show that $`a(n)`$ is divisible by $`4^s`$, where $`s`$ is the number of ones in the binary expansion of $`n-1`$. Both results hold, in a form that depends on $`m`$, for the whole family of equations $`A\bigl(xA-mxA^2\bigr)=x^2`$. The results were checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396844,
  author = {Goyal, Dev D.},
  title = {{Remainders modulo $16$ for the series $A(xA-4xA^2)=x^2$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A396844-Remainders-modulo-16/paper.pdf}},
  year = {2026}
}
```
