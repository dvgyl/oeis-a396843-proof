# [Two congruences modulo $`3`$ for the series with $`A(3x^2)=2x^2+A^2-2A^3`$](paper.pdf)

*A proof of two conjectures in OEIS A389475*

Dev D. Goyal  
October 2026

OEIS entry: [A389475](https://oeis.org/A389475) · Lean: [`lean/Entries/A389475.lean`](../../lean/Entries/A389475.lean) · Formalization notes: [`lean/docs/A389475.md`](../../lean/docs/A389475.md)

## Abstract

The sequence A389475 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+7x^3+17x^4+\cdots`$ that satisfies $`A(3x^2)=2x^2+A(x)^2-2A(x)^3`$. Paul D. Hanna conjectured two congruences modulo $`3`$: $`A(x)^3\equiv A(x^3)`$ and $`A(x)^2\equiv x^2+2A(x^3)`$. We prove both. We also prove that the equation has exactly one normalized solution with integer coefficients; this is not immediate, because computing the coefficients from the equation involves a division by $`2`$ at every step. The first congruence is an instance of a classical identity that holds for every power series with integer coefficients. The second follows from the first, because modulo $`3`$ the left side $`A(3x^2)`$ of the equation vanishes. The results have been checked by computer and proved formally in the Lean proof assistant. A short further argument, not part of the formal verification, shows that modulo $`9`$ the equation determines $`A`$ completely, as the inverse of an explicit series.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A389475,
  author = {Goyal, Dev D.},
  title = {{Two congruences modulo $3$ for the series with $A(3x^2)=2x^2+A^2-2A^3$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A389475-Two-congruences-modulo-3/paper.pdf}},
  year = {2026}
}
```
