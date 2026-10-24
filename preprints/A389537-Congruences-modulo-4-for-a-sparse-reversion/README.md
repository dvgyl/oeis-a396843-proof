# [Congruences modulo $`4`$ for the series with $`A\bigl(A(x)-x\bigr)=A(x)^2`$](paper.pdf)

*A proof of a conjecture in OEIS A389537*

Dev D. Goyal  
October 2026

OEIS entry: [A389537](https://oeis.org/A389537) · Lean: [`lean/Entries/A389537.lean`](../../lean/Entries/A389537.lean) · Formalization notes: [`lean/docs/A389537.md`](../../lean/docs/A389537.md)

## Abstract

The sequence A389537 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+2x^3+4x^4+8x^5+14x^6+\cdots`$ that satisfies $`A\bigl(A(x)-x\bigr)=A(x)^2`$. Paul D. Hanna conjectured that, for $`n>2`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is $`3`$ times a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this. As the entry records, $`A`$ undoes the substitution of the sparse series $`R(x)=x-x^2+x^4-x^8+\cdots`$. Modulo $`2`$ this gives $`A\equiv x+x^2`$. Writing $`A=x+x^2+2H`$ and working modulo $`4`$ leads to the equation $`H+H^2=x^3`$ modulo $`2`$, whose solution is $`x^3+x^6+x^{12}+x^{24}+\cdots`$. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A389537,
  author = {Goyal, Dev D.},
  title = {{Congruences modulo $4$ for the series with $A\bigl(A(x)-x\bigr)=A(x)^2$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A389537-Congruences-modulo-4-for-a-sparse-reversion/paper.pdf}},
  year = {2026}
}
```
