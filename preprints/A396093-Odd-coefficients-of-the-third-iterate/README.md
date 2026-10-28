# [When are the coefficients of $`B(B(B(x)))`$ odd?](paper.pdf)

*A reference proof for OEIS A396093*

This is reference material. The [earlier proof](https://github.com/umaia1234/agentic-conjectures/blob/c66cca68e85af87d46a7f3431b2602f3c9ebfcf0/problems/oeis-a396093/README.md) is present in a commit dated 11 August 2026. This paper is excluded from the active contribution set.

Dev D. Goyal  
October 2026

OEIS entry: [A396093](https://oeis.org/A396093) · Lean: [`lean/Entries/A396093.lean`](../../lean/Entries/A396093.lean) · Formalization notes: [`lean/docs/A396093.md`](../../lean/docs/A396093.md)

## Abstract

Substituting the power series $`B(x)=x/(1-x)^2=x+2x^2+3x^3+\cdots`$ into itself twice gives the series $`A(x)=B(B(B(x)))=x+6x^2+33x^3+174x^4+\cdots`$, whose coefficients form the sequence A396093 of the On-Line Encyclopedia of Integer Sequences (OEIS). The parity classification is proved in the agentic-conjectures repository in a commit dated 11 August 2026. We give another proof. The coefficient of $`x^n`$ is odd if and only if $`n`$ leaves remainder $`1`$, $`3`$, $`7`$ or $`9`$ on division by $`10`$. This classification implies both of Paul D. Hanna's parity conjectures. The proof works with coefficients modulo $`2`$, where the triple substitution reduces to the fraction $`(x+x^3+x^7+x^9)/(1+x^{10})`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A396093,
  author = {Goyal, Dev D.},
  title = {{When are the coefficients of $B(B(B(x)))$ odd?}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A396093-Odd-coefficients-of-the-third-iterate/paper.pdf}},
  year = {2026}
}
```
