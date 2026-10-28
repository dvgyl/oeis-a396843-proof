# [Odd coefficients, remainders modulo $`9`$, and binary digits for the series $`A(xA-3xA^2)=x^2`$](paper.pdf)

*A proof of one conjecture in OEIS A396843, and the correct form of another*

Dev D. Goyal  
October 2026

OEIS entry: [A396843](https://oeis.org/A396843) · Lean: [`lean/Entries/A396843.lean`](../../lean/Entries/A396843.lean) · Formalization notes: [`lean/docs/A396843.md`](../../lean/docs/A396843.md)

## Abstract

Entry A396843 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=x+3x^2+15x^3+117x^4+\cdots`$ determined by the equation $`A\bigl(xA(x)-3xA(x)^2\bigr)=x^2`$. The entry conjectures that all coefficients of positive degree are odd, and states a rule for their remainders modulo $`9`$ that has since been found to be false. We prove that all coefficients of positive degree are odd, and we determine the remainders modulo $`9`$ exactly: for $`n\ge2`$, the remainder is $`3`$ if $`n=4^k+1`$, it is $`6`$ if $`n=2\cdot4^k+1`$, and it is $`0`$ otherwise. We also show that $`a(n)`$ is divisible by $`3^s`$, where $`s`$ is the number of ones in the binary expansion of $`n-1`$. All three results hold, in a form that depends on $`m`$, for the whole family of equations $`A\bigl(xA-mxA^2\bigr)=x^2`$. The results were checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396843,
  author = {Goyal, Dev D.},
  title = {{Odd coefficients, remainders modulo $9$, and binary digits for the series $A(xA-3xA^2)=x^2$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A396843-Odd-coefficients-remainders-modulo-9-and-binary-digits/paper.pdf}},
  year = {2026}
}
```
