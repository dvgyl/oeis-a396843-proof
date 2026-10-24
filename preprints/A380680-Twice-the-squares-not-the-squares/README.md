# [Twice the squares, not the squares: remainders modulo 4 in a theta-type series](paper.pdf)

*A disproof of the conjecture in OEIS A380680, and the corrected statement*

Dev D. Goyal  
October 2026

OEIS entry: [A380680](https://oeis.org/A380680) · Lean: [`lean/Entries/A380680.lean`](../../lean/Entries/A380680.lean) · Formalization notes: [`lean/docs/A380680.md`](../../lean/docs/A380680.md)

## Abstract

The OEIS entry A380680, contributed by Paul D. Hanna, lists the coefficients of the power series $`A(x)=\sum_{n=-\infty}^{\infty}x^{n^2}\bigl((2-x^n)/(1-2x^n)\bigr)^n=1+4x+6x^2+12x^3+32x^4+\cdots`$, a variant of the classical theta series $`\theta(x)=\sum_nx^{n^2}`$. The entry conjectures that, for $`n>0`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ exactly when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. The published terms $`a(1)=4`$ and $`a(2)=6`$ already contradict the conjecture. We prove the correct statement: for $`n>0`$, $`a(n)`$ leaves remainder $`2`$ exactly when $`n`$ is twice a perfect square ($`n=2,8,18,32,\dots`$), and $`a(n)`$ is divisible by $`4`$ otherwise. Equivalently, $`A(x)\equiv\theta(x^2)\pmod 4`$. The results have also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A380680,
  author = {Goyal, Dev D.},
  title = {{Twice the squares, not the squares: remainders modulo 4 in a theta-type series}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A380680-Twice-the-squares-not-the-squares/paper.pdf}},
  year = {2026}
}
```
