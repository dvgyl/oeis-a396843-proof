# [The iterates of a self-referential power series modulo $`4`$](paper.pdf)

*A proof of four conjectures in OEIS A396099*

Dev D. Goyal  
October 2026

OEIS entry: [A396099](https://oeis.org/A396099) · Lean: [`lean/Entries/A396099.lean`](../../lean/Entries/A396099.lean) · Formalization notes: [`lean/docs/A396099.md`](../../lean/docs/A396099.md)

## Abstract

Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ2}(x)\cdot A^{\circ3}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396099 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that every $`a(n)`$ is odd, that from $`n=3`$ on the remainders of $`a(n)`$ on division by $`4`$ repeat the block $`1,3,3,1`$, and two similar statements about the iterates $`A(A(x))`$ and $`A(A(A(x)))`$. We prove all four. The key fact is that, modulo $`4`$, the series $`A`$ equals the explicit fraction $`\frac{x}{1-x}+\frac{2x^4}{(1-x)^3}`$, and $`A(A(x))`$ equals $`x+2x^2`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the simple fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396099,
  author = {Goyal, Dev D.},
  title = {{The iterates of a self-referential power series modulo $4$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A396099-Iterates-of-a-self-referential-series-modulo-4/paper.pdf}},
  year = {2026}
}
```
