# [The iterates of a self-referential power series modulo $`10`$](paper.pdf)

*A proof of two conjectures in OEIS A396807*

Dev D. Goyal  
October 2026

OEIS entry: [A396807](https://oeis.org/A396807) · Lean: [`lean/Entries/A396807.lean`](../../lean/Entries/A396807.lean) · Formalization notes: [`lean/docs/A396807.md`](../../lean/docs/A396807.md)

## Abstract

Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ5}(x)\cdot A^{\circ6}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396807 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that $`a(n)`$ leaves remainder $`1`$ on division by $`10`$ for every $`n\ge1`$, and more generally that the coefficient of $`x^n`$ in the $`k`$-th iterate $`A^{\circ k}`$ leaves the same remainder as $`k^{n-1}`$, for every integer $`k`$. We prove both: modulo $`10`$, the iterate $`A^{\circ k}`$ equals the fraction $`x/(1-kx)`$, for every integer $`k`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396807,
  author = {Goyal, Dev D.},
  title = {{The iterates of a self-referential power series modulo $10$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A396807-Iterates-of-a-self-referential-series-modulo-10/paper.pdf}},
  year = {2026}
}
```
