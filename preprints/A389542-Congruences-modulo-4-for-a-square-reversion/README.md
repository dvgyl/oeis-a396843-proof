# [Congruences modulo $`4`$ for the series with $`A\bigl(A(x)^2-x^2\bigr)=4A(x)^3`$](paper.pdf)

*A proof of a conjecture in OEIS A389542*

Dev D. Goyal  
October 2026

OEIS entry: [A389542](https://oeis.org/A389542) · Lean: [`lean/Entries/A389542.lean`](../../lean/Entries/A389542.lean) · Formalization notes: [`lean/docs/A389542.md`](../../lean/docs/A389542.md)

## Abstract

The sequence A389542 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+2x^2+10x^3+64x^4+\cdots`$ that satisfies $`A\bigl(A(x)^2-x^2\bigr)=4A(x)^3`$. Paul D. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n-1`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this. We also prove that the equation has exactly one normalized solution with integer coefficients; this is not immediate, because computing the coefficients from the equation involves a division by $`2`$ at every step. The proof works with the inverse series $`R`$, which has the form $`R=x-2xL`$ for a series $`L`$ that agrees with the generating series of the Catalan numbers modulo $`2`$. Modulo $`4`$, the series $`R`$ undoes its own substitution, so $`A`$ agrees with $`R`$, and the pattern comes from the parity of the Catalan numbers. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A389542,
  author = {Goyal, Dev D.},
  title = {{Congruences modulo $4$ for the series with $A\bigl(A(x)^2-x^2\bigr)=4A(x)^3$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A389542-Congruences-modulo-4-for-a-square-reversion/paper.pdf}},
  year = {2026}
}
```
