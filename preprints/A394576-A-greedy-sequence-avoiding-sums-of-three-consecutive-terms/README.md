# [A greedy sequence that avoids sums of three consecutive terms](paper.pdf)

*A proof of the first conjecture in OEIS A394576*

Dev D. Goyal  
October 2026

OEIS entry: [A394576](https://oeis.org/A394576) · Lean: [`lean/Entries/A394576.lean`](../../lean/Entries/A394576.lean) · Formalization notes: [`lean/docs/A394576.md`](../../lean/docs/A394576.md)

## Abstract

The sequence A394576 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Hoang Xuan Thanh, starts with $`a(1)=1`$ and then always takes the smallest integer larger than the previous term that is not a sum $`a(k)+a(k+1)+a(k+2)`$ of three consecutive earlier terms. Its first conjecture is the bound $`a(n)\le\lfloor(4n-1)/3\rfloor`$. We prove the two-sided bound $`\lfloor(4n-3)/3\rfloor\le a(n)\le\lfloor(4n-1)/3\rfloor`$ for every $`n\ge1`$. Since the two bounds differ by at most one, $`a(n)`$ is always within $`1`$ of the upper bound, and $`a(3k)=4k-1`$ exactly. The proof constructs the sequence in blocks of three: each interval $`\{4k,4k+1,4k+2,4k+3\}`$ contains exactly one forbidden sum, and the other three numbers are the next three terms. We then prove that this construction satisfies the greedy rule, and that the rule has only one solution. The results have been checked by computer and proved formally in the Lean proof assistant.

## Source

The LaTeX source is [`source/paper.tex`](source/paper.tex). It compiles on its own with `pdflatex` (run twice).

## Citation

```bibtex
@misc{Goyal:A394576,
  author = {Goyal, Dev D.},
  title = {{A greedy sequence that avoids sums of three consecutive terms}},
  howpublished = {Preprint, \url{https://github.com/dvgyl/oeis-a396843-proof/blob/main/preprints/A394576-A-greedy-sequence-avoiding-sums-of-three-consecutive-terms/paper.pdf}},
  year = {2026}
}
```
