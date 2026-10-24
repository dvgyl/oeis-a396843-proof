# [Residues modulo $`16`$ for a series defined by a bilateral theta-type equation](paper.pdf)

*A proof of three conjectures in OEIS A355872*

Dev D. Goyal  
October 2026

OEIS entry: [A355872](https://oeis.org/A355872) · Lean: [`lean/Entries/A355872.lean`](../../lean/Entries/A355872.lean) · Formalization notes: [`lean/docs/A355872.md`](../../lean/docs/A355872.md)

## Abstract

The sequence A355872 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=\sum_{n\ge1}a(n)x^{4n-3}=2x+14x^5+434x^9+\cdots`$ determined by the equation $`x=\sum_{j\in\mathbb{Z}}(-x)^{j^2}A(x)^{(j-1)^2}`$, a sum over all integers $`j`$. The entry conjectures that every $`a(n)`$ is $`2`$ modulo $`4`$, and that $`a(n)`$ is $`2`$ or $`6`$ modulo $`8`$ according as $`n`$ is odd or even. We prove the stronger statement $`a(n)\equiv2(-1)^{n-1}\pmod{16}`$ for every $`n\ge1`$. The proof first shows that the equation has exactly one solution over every commutative ring and that only the degrees $`4n-3`$ occur. Modulo $`16`$ the series $`2x/(1+x^4)`$ satisfies the equation, because its fourth power vanishes and only three terms of the infinite sum survive. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A355872,
  author = {Goyal, Dev D.},
  title = {{Residues modulo $16$ for a series defined by a bilateral theta-type equation}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A355872-Residues-modulo-16-for-a-bilateral-theta-type-equation/paper.pdf}},
  year = {2026}
}
```
