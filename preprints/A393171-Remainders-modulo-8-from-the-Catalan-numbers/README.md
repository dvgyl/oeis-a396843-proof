# [Remainders modulo $`8`$ of a series built from the Catalan numbers](paper.pdf)

*A proof of a conjecture in OEIS A393171*

Dev D. Goyal  
October 2026

OEIS entry: [A393171](https://oeis.org/A393171) · Lean: [`lean/Entries/A393171.lean`](../../lean/Entries/A393171.lean) · Formalization notes: [`lean/docs/A393171.md`](../../lean/docs/A393171.md)

## Abstract

The sequence A393171 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, consists of the coefficients $`a(n)`$ of the power series $`B(x)=x+x^2+4x^3+20x^4+116x^5+\cdots`$ defined by the equation $`B(x)=x+B(C(x))^2`$, where $`C(x)`$ is the generating function of the Catalan numbers. Hanna conjectured that, for $`n>2`$, the coefficient $`a(n)`$ leaves remainder $`4`$ on division by $`8`$ when $`n`$ or $`n-1`$ is a power of $`2`$, and is divisible by $`8`$ otherwise. We prove this conjecture. The proof goes through the companion sequence A393172, whose series $`A(x)`$ satisfies $`A(x-x^2)=x+A(x)^2`$: we show that $`B=x+A^2`$, and that $`A=2C-x+4K`$ for a series $`K`$ with integer coefficients. Squaring then gives $`B`$ modulo $`8`$ in closed form, $`B\equiv x+x^2+4(C-x-xC)`$, from which the conjecture can be read off. The result has also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A393171,
  author = {Goyal, Dev D.},
  title = {{Remainders modulo $8$ of a series built from the Catalan numbers}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A393171-Remainders-modulo-8-from-the-Catalan-numbers/paper.pdf}},
  year = {2026}
}
```
