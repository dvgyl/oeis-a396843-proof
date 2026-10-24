# [A power series whose square is $`x^2+2x^3`$ modulo $`9`$](paper.pdf)

*A proof of two conjectures in OEIS A389474*

Dev D. Goyal  
October 2026

OEIS entry: [A389474](https://oeis.org/A389474) · Lean: [`lean/Entries/A389474.lean`](../../lean/Entries/A389474.lean) · Formalization notes: [`lean/docs/A389474.md`](../../lean/docs/A389474.md)

## Abstract

The sequence A389474 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+4x^3+14x^4+\cdots`$ that satisfies $`A\bigl(x^2+2x^3+2A(x)^2\bigr)=3A(x)^2`$. Paul D. Hanna conjectured that all coefficients of the square $`A(x)^2`$ beyond $`x^3`$ are divisible by $`9`$, and that every coefficient of $`A(x)^{3k}-A(x^3)^k`$ is divisible by $`3`$. We prove both. The main result is that $`A(x)^2\equiv x^2+2x^3\pmod 9`$. We also prove that the equation has exactly one solution with integer coefficients; this requires an argument, because computing the coefficients from the equation involves a division by $`2`$ at every step. The proof works with the inverse series of $`A`$, which satisfies a simpler equation. The second conjecture is an instance of a classical identity. The results have been checked by computer and proved formally in the Lean proof assistant. A short further argument, not part of the formal verification, shows that $`A(x)^2`$ is congruent to a polynomial modulo every power of $`3`$.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A389474,
  author = {Goyal, Dev D.},
  title = {{A power series whose square is $x^2+2x^3$ modulo $9$}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A389474-A-series-whose-square-is-a-polynomial-modulo-9/paper.pdf}},
  year = {2026}
}
```
