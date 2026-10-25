# [The numbers with exponential generating function $`(e^x-1)/\cos 2x`$, modulo 4 and 5](paper.pdf)

*A proof of two conjectures in OEIS A380056*

Dev D. Goyal  
October 2026

OEIS entry: [A380056](https://oeis.org/A380056) · Lean: [`lean/Entries/A380056.lean`](../../lean/Entries/A380056.lean) · Formalization notes: [`lean/docs/A380056.md`](../../lean/docs/A380056.md)

## Abstract

The OEIS entry A380056, contributed by Paul D. Hanna, lists the numbers $`a(n)`$ defined by the exponential generating function $`(e^x-1)/\cos 2x`$; that is, $`a(n)/n!`$ is the coefficient of $`x^n`$ in the power series of this function. The first terms are $`1,1,13,25,441,1261,\dots`$. Hanna conjectured that $`a(n)`$ leaves remainder $`1`$ on division by $`4`$ for every $`n\ge1`$, and that $`a(4n)`$ is divisible by $`5`$. We prove both, and more: modulo $`5`$, $`a(n)\equiv2\cdot2^n+3\cdot4^n`$, so the remainders repeat in the cycle $`1,1,3,0`$, and $`a(n)`$ is divisible by $`5`$ exactly when $`n`$ is a multiple of $`4`$. The proof first rewrites the definition as a recurrence that uses only integers, and then solves this recurrence modulo $`4`$ and modulo $`5`$. Modulo $`5`$ the solution is a combination of two geometric sequences, because modulo $`5`$ the coefficients of $`\cos 2x`$ agree with those of $`(e^x+e^{-x})/2`$. The results have also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A380056,
  author = {Goyal, Dev D.},
  title = {{The numbers with exponential generating function $(e^x-1)/\cos 2x$, modulo 4 and 5}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A380056-Exponential-over-cosine-modulo-4-and-5/paper.pdf}},
  year = {2026}
}
```
