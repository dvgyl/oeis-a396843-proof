# [The iterates of a self-referential power series modulo $`8`$](paper.pdf)

*Proofs of seven conjectures in OEIS A396798, and a correction to an eighth*

Dev D. Goyal  
October 2026

OEIS entry: [A396798](https://oeis.org/A396798) · Lean: [`lean/Entries/A396798.lean`](../../lean/Entries/A396798.lean) · Formalization notes: [`lean/docs/A396798.md`](../../lean/docs/A396798.md)

## Abstract

Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ4}(x)\cdot A^{\circ5}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396798 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna made eight conjectures about the remainders on division by $`8`$ of the coefficients of $`A`$ and of its iterates $`A^{\circ2},\dots,A^{\circ8}`$. Seven of them are true as stated, and we prove them. The first, about $`a(n)`$ itself, is false as stated: $`a(3)=9`$ leaves remainder $`1`$, not $`5`$, on division by $`8`$. We prove the corrected statement, in which the repeating block $`1,1,5,5`$ of remainders starts at $`n=2`$ instead of $`n=1`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the simple fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396798,
  author = {Goyal, Dev D.},
  title = {{The iterates of a self-referential power series modulo $8$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A396798-Iterates-of-a-self-referential-series-modulo-8/paper.pdf}},
  year = {2026}
}
```
