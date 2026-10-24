# Manuscript collection

**26 papers on conjectures from the OEIS, in 7 families.**

[**Read the overview PDF**](overview.pdf).

## Manuscript map

Each family is followed by its papers. For each paper: the OEIS entry, the result, the status (proved, corrected, or disproved and corrected), and the abstract. Paper titles link to the PDFs.

## 1. The family $`A_m(xA_m-mxA_m^2)=x^2`$

Parity, residues modulo $`m^2`$ and binary-digit divisibility for the unique normalized solution of $`A_m(xA_m-mxA_m^2)=x^2`$, with corrected residue classifications for the two entries.

&emsp;**[Odd coefficients, remainders modulo $`9`$, and binary digits for the series $`A(xA-3xA^2)=x^2`$](preprints/A396843-Odd-coefficients-remainders-modulo-9-and-binary-digits/paper.pdf)** ([A396843](https://oeis.org/A396843), proved, corrected)

&emsp;Every coefficient is odd; the exact residues modulo 9 (correcting the entry's second conjecture); $`3^{s_2(n-1)}`$ divides $`a(n)`$, where $`s_2`$ is the binary digit sum.

> Entry A396843 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=x+3x^2+15x^3+117x^4+\cdots`$ determined by the equation $`A\bigl(xA(x)-3xA(x)^2\bigr)=x^2`$. The entry conjectures that all coefficients are odd, and states a rule for their remainders modulo $`9`$ that has since been found to be false. We prove that all coefficients are odd, and we determine the remainders modulo $`9`$ exactly: for $`n\ge2`$, the remainder is $`3`$ if $`n=4^k+1`$, it is $`6`$ if $`n=2\cdot4^k+1`$, and it is $`0`$ otherwise. We also show that $`a(n)`$ is divisible by $`3^s`$, where $`s`$ is the number of ones in the binary expansion of $`n-1`$. All three results hold, in a form that depends on $`m`$, for the whole family of equations $`A\bigl(xA-mxA^2\bigr)=x^2`$. The results were checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Remainders modulo $`16`$ for the series $`A(xA-4xA^2)=x^2`$](preprints/A396844-Remainders-modulo-16/paper.pdf)** ([A396844](https://oeis.org/A396844), corrected)

&emsp;The exact residues modulo 16; the conjecture fails first at $`n=17`$.

> Entry A396844 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=x+4x^2+28x^3+288x^4+\cdots`$ determined by the equation $`A\bigl(xA(x)-4xA(x)^2\bigr)=x^2`$. The entry conjectures that, for $`n>8`$, the remainder of $`a(n)`$ on division by $`16`$ is $`12`$ when $`n=2\cdot4^k+1`$, and $`0`$ otherwise. We show that the first half of this statement is true and the second half is not: for every $`n=4^k+1`$ the remainder is $`4`$, the first exception after $`n=8`$ being $`n=17`$. The complete rule, which we prove, is: for $`n\ge2`$, the remainder is $`4`$ if $`n=4^k+1`$, it is $`12`$ if $`n=2\cdot4^k+1`$, and it is $`0`$ otherwise. We also show that $`a(n)`$ is divisible by $`4^s`$, where $`s`$ is the number of ones in the binary expansion of $`n-1`$. Both results hold, in a form that depends on $`m`$, for the whole family of equations $`A\bigl(xA-mxA^2\bigr)=x^2`$. The results were checked by computer and proved formally in the Lean proof assistant.

## 2. Consecutive iterates $`F=x+F^{\circ r}\,F^{\circ(r+1)}`$

For every integer $`k`$, the $`k`$-th iterate of $`F_r`$ modulo $`2r`$ is $`x/(1-kx)`$ when $`r`$ is odd, with an explicit correction term when $`r`$ is even.

&emsp;**[The iterates of a self-referential power series modulo $`4`$](preprints/A396099-Iterates-of-a-self-referential-series-modulo-4/paper.pdf)** ([A396099](https://oeis.org/A396099), proved)

&emsp;All four conjectured congruences modulo 4 for the series and its iterates.

> Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ2}(x)\cdot A^{\circ3}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396099 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that every $`a(n)`$ is odd, that from $`n=3`$ on the remainders of $`a(n)`$ on division by $`4`$ repeat the block $`1,3,3,1`$, and two similar statements about the iterates $`A(A(x))`$ and $`A(A(A(x)))`$. We prove all four. The key fact is that, modulo $`4`$, the series $`A`$ equals the explicit fraction $`\frac{x}{1-x}+\frac{2x^4}{(1-x)^3}`$, and $`A(A(x))`$ equals $`x+2x^2`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the simple fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[The iterates of a self-referential power series modulo $`8`$](preprints/A396798-Iterates-of-a-self-referential-series-modulo-8/paper.pdf)** ([A396798](https://oeis.org/A396798), proved, corrected)

&emsp;Seven of the eight conjectured congruences modulo 8; the remaining one holds from $`n=2`$, not from $`n=1`$ as stated.

> Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ4}(x)\cdot A^{\circ5}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396798 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna made eight conjectures about the remainders on division by $`8`$ of the coefficients of $`A`$ and of its iterates $`A^{\circ2},\dots,A^{\circ8}`$. Seven of them are true as stated, and we prove them. The first, about $`a(n)`$ itself, is false as stated: $`a(3)=9`$ leaves remainder $`1`$, not $`5`$, on division by $`8`$. We prove the corrected statement, in which the repeating block $`1,1,5,5`$ of remainders starts at $`n=2`$ instead of $`n=1`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the simple fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[The iterates of a self-referential power series modulo $`10`$](preprints/A396807-Iterates-of-a-self-referential-series-modulo-10/paper.pdf)** ([A396807](https://oeis.org/A396807), proved)

&emsp;For every integer $`k`$, the coefficients of the $`k`$-th iterate satisfy $`[x^n]\,A^{\circ k}\equiv k^{n-1}\pmod{10}`$.

> Let $`A(x)=x+x^2+\cdots`$ be the power series defined by the equation $`A(x)=x+A^{\circ5}(x)\cdot A^{\circ6}(x)`$, where $`A^{\circ k}`$ means $`A`$ substituted into itself $`k`$ times. Its coefficients form the sequence A396807 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that $`a(n)`$ leaves remainder $`1`$ on division by $`10`$ for every $`n\ge1`$, and more generally that the coefficient of $`x^n`$ in the $`k`$-th iterate $`A^{\circ k}`$ leaves the same remainder as $`k^{n-1}`$, for every integer $`k`$. We prove both: modulo $`10`$, the iterate $`A^{\circ k}`$ equals the fraction $`x/(1-kx)`$, for every integer $`k`$. The proof covers the whole family of equations $`F=x+F^{\circ r}\cdot F^{\circ(r+1)}`$, $`r\ge1`$. Modulo $`2r`$, every iterate $`F^{\circ k}`$ (including those with $`k<0`$, built from the inverse series) equals the simple fraction $`x/(1-kx)`$, plus an explicit correction $`r\,x^4/(1-x)^3`$ when $`r`$ is even and $`k`$ is odd. All results have been checked by computer and proved formally in the Lean proof assistant.

## 3. Scaled inverses $`A(x-x\,A(qx)/q)=x`$

Every coefficient is $`1`$ modulo $`q+1`$; for even $`q`$, the odd coefficients sit exactly at the powers of $`2`$.

&emsp;**[Congruences for the series $`A`$ with $`A\bigl(x-x\,A(4x)/4\bigr)=x`$](preprints/A393856-Congruences-for-a-scaled-inverse-series-q-4/paper.pdf)** ([A393856](https://oeis.org/A393856), proved)

&emsp;$`a(n)\equiv1\pmod 5`$, and $`a(n)`$ is odd exactly when $`n`$ is a power of 2.

> The sequence A393856 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+6x^3+121x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(4x)/4\bigr)=x`$. The unknown series $`A`$ appears on both sides of this equation, and its coefficients grow very fast. Paul D. Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`5`$, and that a coefficient is odd exactly when its index is a power of $`2`$. We prove both conjectures. In fact we prove two statements that hold with $`4`$ replaced by any positive integer $`q`$: modulo $`q+1`$ the series becomes $`x+x^2+x^3+\cdots`$, and, when $`q`$ is even, modulo $`2`$ it agrees with the generating series of the Catalan numbers, whose odd coefficients sit exactly at the powers of $`2`$. The key observation is that in arithmetic modulo $`q+1`$ the number $`q`$ behaves like $`-1`$, and for $`q=-1`$ the equation can be solved by hand. The results have also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Congruences for the series $`A`$ with $`A\bigl(x-x\,A(5x)/5\bigr)=x`$](preprints/A393857-Congruences-for-a-scaled-inverse-series-q-5/paper.pdf)** ([A393857](https://oeis.org/A393857), proved)

&emsp;$`a(n)\equiv1\pmod 6`$.

> The sequence A393857 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+7x^3+205x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(5x)/5\bigr)=x`$. The unknown series $`A`$ appears on both sides of this equation, and its coefficients grow very fast. Paul D. Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`6`$. We prove this. In fact we prove that, with $`5`$ replaced by any positive integer $`q`$, the series becomes $`x+x^2+x^3+\cdots`$ once its coefficients are reduced modulo $`q+1`$. The key observation is that in arithmetic modulo $`q+1`$ the number $`q`$ behaves like $`-1`$, and for $`q=-1`$ the equation can be solved by hand. The results have also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Congruences for the series $`A`$ with $`A\bigl(x-x\,A(6x)/6\bigr)=x`$](preprints/A393858-Congruences-for-a-scaled-inverse-series-q-6/paper.pdf)** ([A393858](https://oeis.org/A393858), proved)

&emsp;$`a(n)\equiv1\pmod 7`$, and $`a(n)`$ is odd exactly when $`n`$ is a power of 2.

> The sequence A393858 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+8x^3+323x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(6x)/6\bigr)=x`$. The unknown series $`A`$ appears on both sides of this equation, and its coefficients grow very fast. Paul D. Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`7`$, and that a coefficient is odd exactly when its index is a power of $`2`$. We prove both conjectures. In fact we prove two statements that hold with $`6`$ replaced by any positive integer $`q`$: modulo $`q+1`$ the series becomes $`x+x^2+x^3+\cdots`$, and, when $`q`$ is even, modulo $`2`$ it agrees with the generating series of the Catalan numbers, whose odd coefficients sit exactly at the powers of $`2`$. The key observation is that in arithmetic modulo $`q+1`$ the number $`q`$ behaves like $`-1`$, and for $`q=-1`$ the equation can be solved by hand. The results have also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Congruences for the series $`A`$ with $`A\bigl(x-x\,A(7x)/7\bigr)=x`$](preprints/A393859-Congruences-for-a-scaled-inverse-series-q-7/paper.pdf)** ([A393859](https://oeis.org/A393859), proved)

&emsp;$`a(n)\equiv1\pmod 8`$.

> The sequence A393859 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+9x^3+481x^4+\cdots`$ defined by the equation $`A\bigl(x-x\,A(7x)/7\bigr)=x`$. The unknown series $`A`$ appears on both sides of this equation, and its coefficients grow very fast. Paul D. Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`8`$. We prove this. In fact we prove that, with $`7`$ replaced by any positive integer $`q`$, the series becomes $`x+x^2+x^3+\cdots`$ once its coefficients are reduced modulo $`q+1`$. The key observation is that in arithmetic modulo $`q+1`$ the number $`q`$ behaves like $`-1`$, and for $`q=-1`$ the equation can be solved by hand. The results have also been checked by computer and proved formally in the Lean proof assistant.

## 4. Theta series modulo 4

Series built from the Jacobi theta series $`\theta_3`$ whose coefficients are $`2`$ modulo $`4`$ exactly at squares (or twice squares) and divisible by $`4`$ elsewhere.

&emsp;**[Remainders modulo $`4`$ for the series with $`A\bigl(x/A(x)\bigr)=\theta_3(x)`$](preprints/A378580-Theta-quotient-substitution-modulo-4/paper.pdf)** ([A378580](https://oeis.org/A378580), proved)

&emsp;$`A(x/A(x))=\theta_3`$: for $`n>0`$, $`a(n)\equiv2\pmod4`$ if $`n`$ is a square, and $`4\mid a(n)`$ otherwise.

> Let $`\theta(x)=1+2x+2x^4+2x^9+2x^{16}+\cdots`$ be the theta series, whose coefficient of $`x^n`$ is $`2`$ when $`n`$ is a positive perfect square and $`0`$ otherwise. Entry A378580 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=1+2x+4x^2+16x^3+98x^4+\cdots`$ determined by $`A\bigl(x/A(x)\bigr)=\theta(x)`$. The entry conjectures that for $`n>0`$ the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We prove this conjecture. In fact, modulo $`4`$ the whole series $`A(x)`$ agrees with $`\theta(x)`$, and the same is true for the companion equation $`A\bigl(x\,A(x)\bigr)=\theta(x)`$ of entry A378581. The proof rests on one observation: modulo $`4`$, twice a series does not change when its argument is changed by a multiple of $`2`$. The results were checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Remainders modulo $`4`$ for the series with $`A\bigl(x\,A(x)\bigr)=\theta_3(x)`$](preprints/A378581-Theta-product-substitution-modulo-4/paper.pdf)** ([A378581](https://oeis.org/A378581), proved)

&emsp;$`A(x\,A(x))=\theta_3`$: the same square pattern.

> Let $`\theta(x)=1+2x+2x^4+2x^9+2x^{16}+\cdots`$ be the theta series, whose coefficient of $`x^n`$ is $`2`$ when $`n`$ is a positive perfect square and $`0`$ otherwise. Entry A378581 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, lists the coefficients $`a(n)`$ of the power series $`A(x)=1+2x-4x^2+24x^3-206x^4+\cdots`$ determined by $`A\bigl(x\,A(x)\bigr)=\theta(x)`$. The entry conjectures that for $`n>0`$ the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We prove this conjecture. In fact, modulo $`4`$ the whole series $`A(x)`$ agrees with $`\theta(x)`$, and the same is true for the companion equation $`A\bigl(x/A(x)\bigr)=\theta(x)`$ of entry A378580. The proof rests on one observation: modulo $`4`$, twice a series does not change when its argument is changed by a multiple of $`2`$. The results were checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Square indices and remainders modulo 4 in a theta-type series](preprints/A380060-Square-indices-in-a-theta-type-series/paper.pdf)** ([A380060](https://oeis.org/A380060), proved)

&emsp;For $`n>0`$, $`a(n)\equiv2\pmod4`$ if $`n`$ is a square, and $`4\mid a(n)`$ otherwise.

> The OEIS entry A380060, contributed by Paul D. Hanna, defines a power series $`A(x)=1+2x+4x^2+16x^3+66x^4+\cdots`$ by an implicit equation: $`A`$ equals a sum over all integers $`n`$ whose $`n`$-th term is $`x^{n^2}\bigl((A-x^n)/(1-x^nA)\bigr)^n`$, so $`A`$ appears on both sides. The sum resembles the classical theta series $`\theta(x)=\sum_nx^{n^2}=1+2x+2x^4+2x^9+\cdots`$. Hanna conjectured that, for $`n>0`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We prove this. In fact $`A(x)\equiv\theta(x)\pmod 4`$: every coefficient of $`A`$ has the same remainder modulo $`4`$ as the corresponding coefficient of the theta series. The proof rests on two simple observations: modulo $`2`$ the series $`A`$ is just $`1`$, and twice a number is known modulo $`4`$ once the number is known modulo $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Twice the squares, not the squares: remainders modulo 4 in a theta-type series](preprints/A380680-Twice-the-squares-not-the-squares/paper.pdf)** ([A380680](https://oeis.org/A380680), disproved, corrected)

&emsp;The square conjecture is false ($`a(1)=4`$, $`a(2)=6`$); in fact $`a(n)\equiv2\pmod4`$ exactly when $`n=2k^2`$.

> The OEIS entry A380680, contributed by Paul D. Hanna, is the power series $`A(x)=\sum_{n=-\infty}^{\infty}x^{n^2}\bigl((2-x^n)/(1-2x^n)\bigr)^n=1+4x+6x^2+12x^3+32x^4+\cdots`$, a variant of the classical theta series $`\theta(x)=\sum_nx^{n^2}`$. The entry conjectures that, for $`n>0`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ exactly when $`n`$ is a perfect square, and is divisible by $`4`$ otherwise. We show that this conjecture is false: $`a(1)=4`$ and $`a(2)=6`$, as the published terms already show. We then prove the correct statement: for $`n>0`$, $`a(n)`$ leaves remainder $`2`$ exactly when $`n`$ is twice a perfect square ($`n=2,8,18,32,\dots`$), and $`a(n)`$ is divisible by $`4`$ otherwise. Equivalently, $`A(x)\equiv\theta(x^2)\pmod 4`$. The proof takes a few lines. The results have also been checked by computer and proved formally in the Lean proof assistant.

## 5. Catalan-type equations

Equations whose solutions reduce, modulo 4 or 8, to expressions in the Catalan series, whose coefficients are odd exactly at powers of 2.

&emsp;**[The Catalan numbers inside the equation $`A(x-x^2)=x+A(x)^2`$](preprints/A393172-The-Catalan-numbers-inside-a-functional-equation/paper.pdf)** ([A393172](https://oeis.org/A393172), proved)

&emsp;For $`n>1`$, $`a(n)\equiv2\pmod4`$ if $`n=2^k`$, and $`4\mid a(n)`$ otherwise.

> There is exactly one power series $`A(x)=x+2x^2+8x^3+42x^4+\cdots`$ that satisfies the equation $`A(x-x^2)=x+A(x)^2`$. Its coefficients $`a(n)`$ form the sequence A393172 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this conjecture. The key observation is that, once every coefficient is replaced by its remainder modulo $`4`$, the series $`A(x)`$ becomes $`2C(x)-x`$, where $`C(x)=x+x^2+2x^3+5x^4+\cdots`$ is the generating function of the Catalan numbers. The conjecture then follows from the classical fact that a Catalan number is odd only at positions given by powers of $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Remainders modulo $`8`$ of a series built from the Catalan numbers](preprints/A393171-Remainders-modulo-8-from-the-Catalan-numbers/paper.pdf)** ([A393171](https://oeis.org/A393171), proved)

&emsp;For $`n>2`$, $`a(n)\equiv4\pmod8`$ if $`n=2^k`$ or $`2^k+1`$, and $`8\mid a(n)`$ otherwise.

> The sequence A393171 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, consists of the coefficients of the power series $`B(x)=x+x^2+4x^3+20x^4+116x^5+\cdots`$ defined by the equation $`B(x)=x+B(C(x))^2`$, where $`C(x)`$ is the generating function of the Catalan numbers. Hanna conjectured that, for $`n>2`$, the coefficient $`a(n)`$ leaves remainder $`4`$ on division by $`8`$ when $`n`$ or $`n-1`$ is a power of $`2`$, and is divisible by $`8`$ otherwise. We prove this conjecture. The proof goes through the companion sequence A393172, whose series $`A(x)`$ satisfies $`A(x-x^2)=x+A(x)^2`$: we show that $`B=x+A^2`$, and that $`A=2C-x+4K`$ for a series $`K`$ with integer coefficients. Squaring then gives $`B`$ modulo $`8`$ in closed form, $`B\equiv x+x^2+4(C-x-xC)`$, from which the conjecture can be read off. The result has also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[The odd-indexed terms of a nested square are even](preprints/A392210-Odd-indexed-terms-of-a-nested-square/paper.pdf)** ([A392210](https://oeis.org/A392210), proved)

&emsp;$`a(2n-1)`$ is even for $`n>1`$ (an elementary observation recorded in the entry).

> The sequence A392210 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, is defined by an “infinitely nested square” $`x+\mathrm{sq}\Bigl(\frac{x}{1-x}+\mathrm{sq}\Bigl(\frac{x}{1-2x}+\mathrm{sq}\Bigl(\frac{x}{1-3x}+\cdots\Bigr)\Bigr)\Bigr), \qquad \mathrm{sq}(y)=y^2`$. Its terms are $`1,1,4,18,96,579,\dots`$, and the entry observes that the terms $`a(2n-1)`$ with $`n>1`$ appear to be even. We first make the nested expression precise: cutting it off after $`d`$ levels gives the correct coefficients up to degree $`d+1`$, and the resulting series is the unique solution of the simpler equation $`A(x)=x+A\bigl(x/(1-x)\bigr)^2`$. We then prove the observation. The proof is short: once all coefficients are reduced modulo $`2`$, the square of any power series contains only even powers of $`x`$. The same idea also gives a recursive rule for the parity of the even-indexed terms. The main results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Remainders modulo $`4`$ for the equation $`A(x^2+2x^3)=x\,A(x)`$](preprints/A389536-Remainders-modulo-4-for-a-Mahler-type-equation/paper.pdf)** ([A389536](https://oeis.org/A389536), proved)

&emsp;For $`n>1`$, $`a(n)\equiv2\pmod4`$ if $`n=2^k+1`$, and $`4\mid a(n)`$ otherwise.

> There is exactly one power series $`A(x)=x+2x^2+2x^3+8x^4+10x^5+\cdots`$ that satisfies the equation $`A(x^2+2x^3)=x\,A(x)`$. Its coefficients $`a(n)`$ form the sequence A389536 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n-1`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this conjecture. The key observation is that, once every coefficient is replaced by its remainder modulo $`4`$, the series $`A(x)`$ becomes $`x+2x\,C(x)`$, where $`C(x)=x+x^2+2x^3+5x^4+\cdots`$ is the generating function of the Catalan numbers. The conjecture then follows from the classical fact that a Catalan number is odd only at positions given by powers of $`2`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Odd coefficients at powers of two for $`A=x+(xA^2)'`$](preprints/A397588-Odd-coefficients-at-powers-of-two/paper.pdf)** ([A397588](https://oeis.org/A397588), proved)

&emsp;$`a(n)`$ is odd exactly when $`n`$ is a power of 2, and $`3\mid a(n)`$ for $`n>1`$.

> The sequence A397588 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, consists of the coefficients of the power series $`A(x)=x+3x^2+24x^3+285x^4+\cdots`$ determined by the differential equation $`A=x+(x\,A^2)'`$, where the prime denotes the derivative. Hanna conjectured that $`a(n)`$ is odd exactly when $`n`$ is a power of $`2`$. The entry also states that $`a(n)`$ is divisible by $`3`$ for every $`n>1`$. We prove both statements. Modulo $`2`$ the derivative term simplifies, and the equation becomes the Catalan equation $`A=x+A^2`$, whose solution modulo $`2`$ is $`x+x^2+x^4+x^8+\cdots`$. Modulo $`3`$, the series $`x`$ itself is a solution. The results have also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Parity of an infinitely nested series reversion](preprints/A195194-Parity-of-an-infinitely-nested-series-reversion/paper.pdf)** ([A195194](https://oeis.org/A195194), proved)

&emsp;The infinitely nested reversion is well defined, and $`a(n)`$ is odd exactly when $`n`$ is a power of 2.

> The sequence A195194 of the On-Line Encyclopedia of Integer Sequences (OEIS), contributed by Paul D. Hanna, is defined by an infinitely nested expression, $`A(x)=\mathrm{INV}\Bigl(x-x\,\mathrm{INV}\bigl(x-2x\,\mathrm{INV}(x-3x\,\mathrm{INV}(x-\cdots))\bigr)\Bigr)`$, where $`\mathrm{INV}`$ denotes series reversion, the operation that undoes a substitution of power series. Its terms are $`1,1,4,29,312,4528,\dots`$. In 2026 Hanna conjectured that $`a(n)`$ is odd exactly when $`n`$ is a power of $`2`$. We first give the infinite nesting a precise meaning: it defines exactly one power series, and cutting it off after $`d`$ levels gives the correct coefficients up to degree $`d+1`$. This holds for arbitrary weights in place of $`1,2,3,\dots`$. We then prove the conjecture. Modulo $`2`$ the weight $`2`$ at the second level vanishes, the whole nest collapses, and $`A`$ satisfies the Catalan equation $`A=x+A^2`$, whose solution modulo $`2`$ is $`x+x^2+x^4+x^8+\cdots`$. The results have been checked by computer and proved formally in the Lean proof assistant.

## 6. Reversions with an exact halving step

Equations whose coefficient recursion appears to divide by 2; the division is shown to be exact before reducing.

&emsp;**[Congruences modulo $`4`$ for the series with $`A\bigl(A(x)-x\bigr)=A(x)^2`$](preprints/A389537-Congruences-modulo-4-for-a-sparse-reversion/paper.pdf)** ([A389537](https://oeis.org/A389537), proved)

&emsp;For $`n>2`$, $`a(n)\equiv2\pmod4`$ if $`n=3\cdot2^k`$, and $`4\mid a(n)`$ otherwise.

> The sequence A389537 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+2x^3+4x^4+8x^5+14x^6+\cdots`$ that satisfies $`A\bigl(A(x)-x\bigr)=A(x)^2`$. Paul D. Hanna conjectured that, for $`n>2`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n`$ is $`3`$ times a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this. As the entry records, $`A`$ undoes the substitution of the sparse series $`R(x)=x-x^2+x^4-x^8+\cdots`$. Modulo $`2`$ this makes $`A`$ simply $`x+x^2`$. Writing $`A=x+x^2+2H`$ and working modulo $`4`$ leads to the equation $`H+H^2=x^3`$ modulo $`2`$, whose solution is $`x^3+x^6+x^{12}+x^{24}+\cdots`$. The results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Congruences modulo $`4`$ for the series with $`A\bigl(A(x)^2-x^2\bigr)=4A(x)^3`$](preprints/A389542-Congruences-modulo-4-for-a-square-reversion/paper.pdf)** ([A389542](https://oeis.org/A389542), proved)

&emsp;For $`n>1`$, $`a(n)\equiv2\pmod4`$ if $`n=2^k+1`$, and $`4\mid a(n)`$ otherwise.

> The sequence A389542 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+2x^2+10x^3+64x^4+\cdots`$ that satisfies $`A\bigl(A(x)^2-x^2\bigr)=4A(x)^3`$. Paul D. Hanna conjectured that, for $`n>1`$, the coefficient $`a(n)`$ leaves remainder $`2`$ on division by $`4`$ when $`n-1`$ is a power of $`2`$, and is divisible by $`4`$ otherwise. We prove this. We also prove that the equation has exactly one solution with integer coefficients, which is not obvious, because computing the coefficients from the equation requires a division by $`2`$ at every step. The proof works with the inverse series $`R`$, which has the form $`R=x-2xL`$ for a series $`L`$ that agrees with the generating series of the Catalan numbers modulo $`2`$. Modulo $`4`$, the series $`R`$ undoes its own substitution, so $`A`$ agrees with $`R`$, and the pattern comes from the parity of the Catalan numbers. The results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[A power series whose square is $`x^2+2x^3`$ modulo $`9`$](preprints/A389474-A-series-whose-square-is-a-polynomial-modulo-9/paper.pdf)** ([A389474](https://oeis.org/A389474), proved)

&emsp;$`A^2\equiv x^2+2x^3\pmod 9`$, and $`A^{3k}\equiv A(x^3)^k\pmod 3`$.

> The sequence A389474 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+4x^3+14x^4+\cdots`$ that satisfies $`A\bigl(x^2+2x^3+2A(x)^2\bigr)=3A(x)^2`$. Paul D. Hanna conjectured that all coefficients of the square $`A(x)^2`$ beyond $`x^3`$ are divisible by $`9`$, and that every coefficient of $`A(x)^{3k}-A(x^3)^k`$ is divisible by $`3`$. We prove both. The main result is that $`A(x)^2`$ leaves exactly $`x^2+2x^3`$ when its coefficients are reduced modulo $`9`$. We also prove that the equation has exactly one solution with integer coefficients, which is not obvious, because computing the coefficients from the equation requires a division by $`2`$ at every step. The proof works with the inverse series of $`A`$, which satisfies a simpler equation. The second conjecture is an instance of a classical identity. The results have been checked by computer and proved formally in the Lean proof assistant. Finally, by a short argument that is not part of the formal verification, we show that $`A(x)^2`$ is congruent to a polynomial modulo every power of $`3`$.

&emsp;**[Two congruences modulo $`3`$ for the series with $`A(3x^2)=2x^2+A^2-2A^3`$](preprints/A389475-Two-congruences-modulo-3/paper.pdf)** ([A389475](https://oeis.org/A389475), proved)

&emsp;$`A^3\equiv A(x^3)`$ and $`A^2\equiv x^2+2A(x^3)\pmod 3`$.

> The sequence A389475 of the On-Line Encyclopedia of Integer Sequences (OEIS) lists the coefficients of the power series $`A(x)=x+x^2+7x^3+17x^4+\cdots`$ that satisfies $`A(3x^2)=2x^2+A(x)^2-2A(x)^3`$. Paul D. Hanna conjectured two congruences modulo $`3`$: $`A(x)^3\equiv A(x^3)`$ and $`A(x)^2\equiv x^2+2A(x^3)`$. We prove both. We also prove that the equation has exactly one solution with integer coefficients, which is not obvious, because computing the coefficients from the equation requires a division by $`2`$ at every step. The first congruence is an instance of a classical identity that holds for every power series with integer coefficients. The second follows from the first, because modulo $`3`$ the left side $`A(3x^2)`$ of the equation vanishes. The results have been checked by computer and proved formally in the Lean proof assistant. Finally, by a short argument that is not part of the formal verification, we note that modulo $`9`$ the equation determines $`A`$ completely, as the inverse of an explicit series.

## 7. Other results

Three further entries, each with its own method.

&emsp;**[When are the coefficients of $`B(B(B(x)))`$ odd?](preprints/A396093-Odd-coefficients-of-the-third-iterate/paper.pdf)** ([A396093](https://oeis.org/A396093), proved)

&emsp;$`a(n)`$ is odd exactly when $`n\equiv1,3,7,9\pmod{10}`$.

> Substituting the power series $`B(x)=x/(1-x)^2=x+2x^2+3x^3+\cdots`$ into itself twice gives the series $`A(x)=B(B(B(x)))=x+6x^2+33x^3+174x^4+\cdots`$, whose coefficients form the sequence A396093 of the On-Line Encyclopedia of Integer Sequences (OEIS). Paul D. Hanna conjectured two rules for when these coefficients are even. We prove both, and more: the coefficient of $`x^n`$ is odd if and only if $`n`$ leaves remainder $`1`$, $`3`$, $`7`$ or $`9`$ on division by $`10`$. The proof works with coefficients modulo $`2`$, where the triple substitution collapses to the simple fraction $`(x+x^3+x^7+x^9)/(1+x^{10})`$. The result has also been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[Every coefficient is $`1`$ modulo $`3`$: the series with $`A(A(A(x)))=(1+x)\,A(A(x))`$](preprints/A396102-Every-coefficient-is-1-modulo-3/paper.pdf)** ([A396102](https://oeis.org/A396102), proved)

&emsp;$`a(n)\equiv1\pmod 3`$, together with a theorem for the whole family $`F^{\circ r}=(1+x)F^{\circ(r-1)}`$.

> The OEIS entry A396102, contributed by Paul D. Hanna, concerns the power series $`A(x)=x+x^2-2x^3+10x^4-71x^5+616x^6-\cdots`$ determined by the equation $`A(A(A(x)))=(1+x)\cdot A(A(x))`$, which relates the second and third iterates of $`A`$ (the series obtained by substituting $`A`$ into itself). Hanna conjectured that every coefficient leaves remainder $`1`$ on division by $`3`$. We prove this, as one case of a family of results: for every $`r\ge1`$, the solution of $`F^{\circ r}=(1+x)\cdot F^{\circ(r-1)}`$ agrees modulo $`r`$ with $`x/(1-x)=x+x^2+x^3+\cdots`$; the case $`r=3`$ is Hanna's conjecture. The key step is to pass to the compositional inverse of the solution, which satisfies a simpler equation, and to observe that $`x/(1+x)`$ solves that equation modulo $`r`$. As by-products, every term of OEIS A140094 is $`1`$ modulo $`3`$, and every term of OEIS A067145 is odd. The main results have been checked by computer and proved formally in the Lean proof assistant.

&emsp;**[The coefficients of $`(e^x-1)/\cos 2x`$ modulo 4 and 5](preprints/A380056-Exponential-over-cosine-modulo-4-and-5/paper.pdf)** ([A380056](https://oeis.org/A380056), proved)

&emsp;$`a(n)\equiv1\pmod4`$, and $`a(n)\equiv2\cdot2^n+3\cdot4^n\pmod5`$, so $`5\mid a(n)`$ exactly when $`4\mid n`$.

> The OEIS entry A380056, contributed by Paul D. Hanna, lists the numbers $`a(n)`$ defined by the exponential generating function $`(e^x-1)/\cos 2x`$; that is, $`a(n)/n!`$ is the coefficient of $`x^n`$ in the power series of this function. The first terms are $`1,1,13,25,441,1261,\dots`$. Hanna conjectured that $`a(n)`$ leaves remainder $`1`$ on division by $`4`$ for every $`n\ge1`$, and that $`a(4n)`$ is divisible by $`5`$. We prove both, and more: modulo $`5`$, $`a(n)\equiv2\cdot2^n+3\cdot4^n`$, so the remainders repeat in the cycle $`1,1,3,0`$, and $`a(n)`$ is divisible by $`5`$ exactly when $`n`$ is a multiple of $`4`$. The proof first rewrites the definition as a recurrence that uses only whole numbers, and then solves this recurrence modulo $`4`$ and modulo $`5`$. Modulo $`5`$ the solution is a combination of two geometric sequences, because there $`\cos 2x`$ behaves like $`(e^x+e^{-x})/2`$. The results have also been checked by computer and proved formally in the Lean proof assistant.
