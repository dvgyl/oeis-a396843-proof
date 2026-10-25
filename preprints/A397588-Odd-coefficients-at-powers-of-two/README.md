# [Odd coefficients at powers of two for $`A=x+(xA^2)'`$](paper.pdf)

*A proof of a conjecture in OEIS A397588*

Dev D. Goyal  
October 2026

OEIS entry: [A397588](https://oeis.org/A397588) · Lean: [`lean/Entries/A397588.lean`](../../lean/Entries/A397588.lean) · Formalization notes: [`lean/docs/A397588.md`](../../lean/docs/A397588.md)

## Abstract

The sequence A397588 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, consists of the coefficients $`a(n)`$ of the power series $`A(x)=x+3x^2+24x^3+285x^4+\cdots`$ determined by the differential equation $`A=x+(x\,A^2)'`$, where the prime denotes the derivative. Hanna conjectured that $`a(n)`$ is odd exactly when $`n`$ is a power of $`2`$. The entry also states that $`a(n)`$ is divisible by $`3`$ for every $`n>1`$. We prove both statements. Modulo $`2`$ the derivative term simplifies, and the equation becomes the Catalan equation $`A=x+A^2`$, whose solution modulo $`2`$ is $`x+x^2+x^4+x^8+\cdots`$. Modulo $`3`$, the series $`x`$ itself is a solution. The results have also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A397588,
  author = {Goyal, Dev D.},
  title = {{Odd coefficients at powers of two for $A=x+(xA^2)'$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A397588-Odd-coefficients-at-powers-of-two/paper.pdf}},
  year = {2026}
}
```
