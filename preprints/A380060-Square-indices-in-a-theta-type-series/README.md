# [Square indices and remainders modulo 4 in a theta-type series](paper.pdf)

*A proof of the conjecture in OEIS A380060*

Dev D. Goyal  
October 2026

OEIS entry: [A380060](https://oeis.org/A380060) · Lean: [`lean/Entries/A380060.lean`](../../lean/Entries/A380060.lean) · Formalization notes: [`lean/docs/A380060.md`](../../lean/docs/A380060.md)

## Abstract

The OEIS entry A380060, contributed by Paul D. Hanna, defines a power series $`A(x)=1+2x+4x^2+16x^3+66x^4+\cdots`$ by an implicit equation: $`A`$ equals a sum over all integers $`n`$ whose $`n`$-th term is $`x^{n^2}\bigl((A-x^n)/(1-x^nA)\bigr)^n`$, so $`A`$ appears on both sides. The sum resembles the classical theta series $`\theta(x)=\sum_nx^{n^2}=1+2x+2x^4+2x^9+\cdots`$. Hanna conjectured that, for $`n>0`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We prove this. In fact $`A(x)\equiv\theta(x)\pmod 4`$: every coefficient of $`A`$ has the same remainder modulo $`4`$ as the corresponding coefficient of the theta series. The proof rests on two simple observations: modulo $`2`$ the series $`A`$ is $`1`$, and twice a number is known modulo $`4`$ once the number is known modulo $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A380060,
  author = {Goyal, Dev D.},
  title = {{Square indices and remainders modulo 4 in a theta-type series}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A380060-Square-indices-in-a-theta-type-series/paper.pdf}},
  year = {2026}
}
```
