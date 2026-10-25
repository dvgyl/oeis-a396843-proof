# [Residues modulo $`8`$ for a series defined by a self-referential exponential](paper.pdf)

*A proof of the conjecture in OEIS A397346*

Dev D. Goyal  
October 2026

OEIS entry: [A397346](https://oeis.org/A397346) · Lean: [`lean/Entries/A397346.lean`](../../lean/Entries/A397346.lean) · Formalization notes: [`lean/docs/A397346.md`](../../lean/docs/A397346.md)

## Abstract

The sequence A397346 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients of the power series $`A(x)=\sum_{n\ge0}a(n)x^n=1+x+4x^2+66x^3+2248x^4+\cdots`$ determined by $`A(x)=\exp\bigl(x+\sum_{n\ge2}\frac{2n^2-1}{2n^2}a(n)x^n\bigr)`$. The entry conjectures that, from $`n=2`$ on, the remainders of $`a(n)`$ on division by $`8`$ repeat the block $`4,2,0,2`$. We prove this. We first show that the equation is equivalent to a recurrence recorded in the entry, and deduce from it that $`a(n)`$ is an integer divisible by $`n`$. For the quotients $`b(n)=a(n)/n`$ we prove the stronger statement that $`b(n)\equiv6\pmod8`$ when $`n\equiv3\pmod4`$ and $`b(n)\equiv2\pmod8`$ otherwise, for $`n\ge2`$. The results have been checked by computer, and the recurrence and the congruences are proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A397346,
  author = {Goyal, Dev D.},
  title = {{Residues modulo $8$ for a series defined by a self-referential exponential}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A397346-Residues-modulo-8-for-a-self-referential-exponential/paper.pdf}},
  year = {2026}
}
```
