# [Congruences for the series $`A`$ with $`A\bigl(x-x\,A(5x)/5\bigr)=x`$](paper.pdf)

*A proof of a conjecture in OEIS A393857*

Dev D. Goyal  
October 2026

OEIS entry: [A393857](https://oeis.org/A393857) · Lean: [`lean/Entries/A393857.lean`](../../lean/Entries/A393857.lean) · Formalization notes: [`lean/docs/A393857.md`](../../lean/docs/A393857.md)

## Abstract

The sequence A393857 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+7x^3+205x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(5x)/5\bigr)=x`$. The unknown series $`A`$ occurs both as the outer function and inside its own argument, and its coefficients grow rapidly. Paul D. Hanna conjectured that every coefficient of positive degree leaves remainder $`1`$ on division by $`6`$. We prove this. In fact we prove that, with $`5`$ replaced by any positive integer $`q`$, the series becomes $`x+x^2+x^3+\cdots`$ once its coefficients are reduced modulo $`q+1`$. The proof rests on the congruence $`q\equiv-1\pmod{q+1}`$: for $`q=-1`$ the equation has an explicit solution. The results have also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A393857,
  author = {Goyal, Dev D.},
  title = {{Congruences for the series $A$ with $A\bigl(x-x\,A(5x)/5\bigr)=x$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A393857-Congruences-for-a-scaled-inverse-series-q-5/paper.pdf}},
  year = {2026}
}
```
