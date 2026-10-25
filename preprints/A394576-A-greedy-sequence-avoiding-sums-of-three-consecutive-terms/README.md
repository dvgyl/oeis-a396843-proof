# [A greedy sequence that avoids sums of three consecutive terms](paper.pdf)

*A proof of the first conjecture in OEIS A394576*

Dev D. Goyal  
October 2026

OEIS entry: [A394576](https://oeis.org/A394576) · Lean: [`lean/Entries/A394576.lean`](../../lean/Entries/A394576.lean) · Formalization notes: [`lean/docs/A394576.md`](../../lean/docs/A394576.md)

## Abstract

The sequence A394576 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Hoang Xuan Thanh, starts with $`a(1)=1`$ and then always takes the smallest integer larger than the previous term that is not a sum $`a(k)+a(k+1)+a(k+2)`$ of three consecutive earlier terms. Its first conjecture is the bound $`a(n)\le\lfloor(4n-1)/3\rfloor`$. We prove this bound, together with the lower bound $`a(n)\ge\lfloor(4n-3)/3\rfloor`$, for every $`n\ge1`$. The two bounds differ by at most one and coincide when $`3\mid n`$, so $`a(n)`$ is always the upper bound or one less than it, and $`a(3k)=4k-1`$. The proof rests on an explicit construction: for each $`k\ge1`$, exactly one of the four integers $`4k,4k+1,4k+2,4k+3`$ is a sum of three consecutive terms, and the other three are the terms $`a(3k+1)`$, $`a(3k+2)`$, $`a(3k+3)`$. We prove that the sequence so constructed obeys the greedy rule; since the rule determines the sequence uniquely, it is the sequence of the entry. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A394576,
  author = {Goyal, Dev D.},
  title = {{A greedy sequence that avoids sums of three consecutive terms}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-proofs/blob/main/preprints/A394576-A-greedy-sequence-avoiding-sums-of-three-consecutive-terms/paper.pdf}},
  year = {2026}
}
```
