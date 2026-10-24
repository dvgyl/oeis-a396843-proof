# Papers

There is one short paper for each of the 34 OEIS entries, as a PDF with its LaTeX source. Each paper is self-contained: it defines every notion it uses, so that a reader without specialist training can follow it, and it does not depend on the other papers. Papers in the same group below share their key ideas, so the background sections repeat from paper to paper. Read any one paper first; the others will then go faster.

## How each paper is organized

1. **Abstract and a note on how the paper was produced.** The note below the abstract says that this is an autonomous AI research effort and who did what.
2. **Introduction.** It has six parts:
   - *the sequence*, with the OEIS entry quoted word for word and its first terms;
   - *the question*, with a table of remainders that shows the conjectured pattern;
   - *what this paper proves*;
   - *what was known before*;
   - *why it is interesting*;
   - *how to read the paper*.
3. **Background.** Power series, substitution, remainders, and the other tools the proof needs, explained from scratch with short proofs.
4. **Results.** The precise theorems.
5. **Proofs.** They begin with "the idea in brief": a few sentences that explain the whole argument before the details.
6. **Checking the results.** It describes the independent computer check, and has a table that gives the Lean theorem for every statement in the paper.
7. **Discussion.** It covers what the result does and does not cover, open questions, and connections to other work.
8. **About this paper.** The roles of Dev D. Goyal, ChatGPT (GPT-6 with Pro reasoning), and Claude Opus 5.5 used with Claude Code; the review status; and the priority statement.
9. **Acknowledgements and references.**

ChatGPT's original drafts are kept in [`../history/chatgpt-collection/manuscripts/`](../history/chatgpt-collection/manuscripts/). The theorems and proof strategies here are the same; the text was rewritten for clarity.

## Papers grouped by method

**The original problem: A(x·A − m·x·A²) = x²**
- [A396843](A396843.pdf): every term is odd; exact remainders modulo 9; divisibility governed by binary digits. This is where the project started.
- [A396844](A396844.pdf): exact remainders modulo 16, correcting the conjecture.

**Consecutive iterates: A = x + A^∘r · A^∘(r+1), modulo 2r**
- [A396099](A396099.pdf) (r = 2)
- [A396797](A396797.pdf) (r = 3; known result)
- [A396798](A396798.pdf) (r = 4; one conjecture corrected)
- [A396807](A396807.pdf) (r = 5)

**Scaled inverses: A(x − x·A(qx)/q) = x**
- [A393856](A393856.pdf) (q = 4)
- [A393857](A393857.pdf) (q = 5)
- [A393858](A393858.pdf) (q = 6)
- [A393859](A393859.pdf) (q = 7)

**Periodicity of Stirling transforms modulo m (known results; Danesh 2026)**
- [A052895](A052895.pdf) · [A064618](A064618.pdf) · [A080253](A080253.pdf) · [A167137](A167137.pdf) · [A305550](A305550.pdf) · [A306082](A306082.pdf) · [A354242](A354242.pdf)

**Theta series and squares modulo 4**
- [A378580](A378580.pdf): A(x/A) = θ₃
- [A378581](A378581.pdf): A(x·A) = θ₃
- [A380060](A380060.pdf): an implicit theta-type sum
- [A380680](A380680.pdf): the explicit variant, where the conjecture is false

**Catalan-type equations modulo 4 and 8**
- [A393172](A393172.pdf): A(x − x²) = x + A²
- [A393171](A393171.pdf): B = x + B(C(x))²
- [A392210](A392210.pdf): nested squares
- [A389536](A389536.pdf): A(x² + 2x³) = x·A
- [A397588](A397588.pdf): A = x + (x·A²)′
- [A195194](A195194.pdf): an infinitely nested reversion

**Reversions with an exact halving step**
- [A389537](A389537.pdf): A(A − x) = A²
- [A389542](A389542.pdf): A(A² − x²) = 4A³
- [A389474](A389474.pdf) and [A389475](A389475.pdf): cubic equations modulo 9 and 3

**Single papers**
- [A396093](A396093.pdf): the third iterate of x/(1−x)², modulo 2
- [A396102](A396102.pdf): A(A(A(x))) = (1+x)·A(A(x)), modulo 3
- [A380056](A380056.pdf): the exponential generating function (eˣ−1)/cos 2x, modulo 4 and 5

## Rebuilding the PDFs

Each `.tex` file compiles on its own with `pdflatex` (run it twice, so that the cross-references resolve). It needs only standard TeX Live packages.

```sh
cd papers
for f in A*.tex; do pdflatex -interaction=nonstopmode "$f" && pdflatex -interaction=nonstopmode "$f"; done
```
