# [Remainders modulo $`4`$ for the equation $`A(x^2+2x^3)=x\,A(x)`$](paper.pdf)

*A proof of a conjecture in OEIS A389536*

Dev D. Goyal  
October 2026

OEIS entry: [A389536](https://oeis.org/A389536) · Lean: [`lean/Entries/A389536.lean`](../../lean/Entries/A389536.lean) · Formalization notes: [`lean/docs/A389536.md`](../../lean/docs/A389536.md)

## Abstract

There is exactly one power series $`A(x)=x+2x^2+2x^3+8x^4+10x^5+\cdots`$ that satisfies the equation $`A(x^2+2x^3)=x\,A(x)`$. Its coefficients $`a(n)`$ form the sequence A389536 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n-1`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this conjecture. The key observation is that, once every coefficient is replaced by its remainder modulo $`4`$, the series $`A(x)`$ becomes $`x+2x\,C(x)`$, where $`C(x)=x+x^2+2x^3+5x^4+\cdots`$ is the generating function of the Catalan numbers. The conjecture then follows from the classical fact that the coefficient of $`x^n`$ in $`C(x)`$ is odd exactly when $`n`$ is a power of $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A389536,
  author = {Goyal, Dev D.},
  title = {{Remainders modulo $4$ for the equation $A(x^2+2x^3)=x\,A(x)$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A389536-Remainders-modulo-4-for-a-Mahler-type-equation/paper.pdf}},
  year = {2026}
}
```
