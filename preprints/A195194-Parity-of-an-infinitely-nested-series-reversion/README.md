# [Parity of an infinitely nested series reversion](paper.pdf)

*A proof of a conjecture in OEIS A195194*

Dev D. Goyal  
October 2026

OEIS entry: [A195194](https://oeis.org/A195194) · Lean: [`lean/Entries/A195194.lean`](../../lean/Entries/A195194.lean) · Formalization notes: [`lean/docs/A195194.md`](../../lean/docs/A195194.md)

## Abstract

The sequence A195194 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, is defined by an infinitely nested expression, $`A(x)=\mathrm{INV}\Bigl(x-x\,\mathrm{INV}\bigl(x-2x\,\mathrm{INV}(x-3x\,\mathrm{INV}(x-\cdots))\bigr)\Bigr)`$, where $`\mathrm{INV}`$ denotes series reversion, the operation that undoes a substitution of power series. Its terms are $`1,1,4,29,312,4528,\dots`$. In 2026 Hanna conjectured that $`a(n)`$ is odd exactly when $`n`$ is a power of $`2`$. We first give the infinite nesting a precise meaning: it defines a unique sequence of power series, one for each level, and in particular a unique series $`A`$; cutting it off after $`d`$ levels gives the correct coefficients up to degree $`d+1`$. This holds for arbitrary weights in place of $`1,2,3,\dots`$. We then prove the conjecture. Modulo $`2`$ the weight $`2`$ at the second level vanishes, the whole nest collapses, and $`A`$ satisfies the Catalan equation $`A=x+A^2`$, whose solution modulo $`2`$ is $`x+x^2+x^4+x^8+\cdots`$. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A195194,
  author = {Goyal, Dev D.},
  title = {{Parity of an infinitely nested series reversion}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A195194-Parity-of-an-infinitely-nested-series-reversion/paper.pdf}},
  year = {2026}
}
```
