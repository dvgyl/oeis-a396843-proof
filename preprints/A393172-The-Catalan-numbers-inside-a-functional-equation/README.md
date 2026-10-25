# [The Catalan numbers inside the equation $`A(x-x^2)=x+A(x)^2`$](paper.pdf)

*A proof of a conjecture in OEIS A393172*

Dev D. Goyal  
October 2026

OEIS entry: [A393172](https://oeis.org/A393172) · Lean: [`lean/Entries/A393172.lean`](../../lean/Entries/A393172.lean) · Formalization notes: [`lean/docs/A393172.md`](../../lean/docs/A393172.md)

## Abstract

There is exactly one power series $`A(x)=x+2x^2+8x^3+42x^4+\cdots`$ that satisfies the equation $`A(x-x^2)=x+A(x)^2`$. Its coefficients $`a(n)`$ form the sequence A393172 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this conjecture. The key observation is that, once every coefficient is replaced by its remainder modulo $`4`$, the series $`A(x)`$ becomes $`2C(x)-x`$, where $`C(x)=x+x^2+2x^3+5x^4+\cdots`$ is the generating function of the Catalan numbers. The conjecture then follows from the classical fact that the coefficient of $`x^n`$ in $`C(x)`$ is odd exactly when $`n`$ is a power of $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A393172,
  author = {Goyal, Dev D.},
  title = {{The Catalan numbers inside the equation $A(x-x^2)=x+A(x)^2$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A393172-The-Catalan-numbers-inside-a-functional-equation/paper.pdf}},
  year = {2026}
}
```
