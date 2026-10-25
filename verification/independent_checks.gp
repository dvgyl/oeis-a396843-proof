\\ Independent numerical checks for the OEIS proof collection.
\\
\\ An independent cross-check that shares no code with the Lean development.
\\ For each of the 28 entries this script
\\   1. recomputes the sequence from the definition printed in its OEIS entry,
\\   2. compares the first terms with the published OEIS terms (oeis_terms.gp),
\\   3. re-verifies the defining equation to the working precision, and
\\   4. tests every claimed congruence, residue pattern, and counterexample on
\\      all indices in the computed range.
\\
\\ A finite check is evidence, not a proof: the all-index statements are proved
\\ in the papers and in Lean.  Run from this directory with
\\     gp -q independent_checks.gp
\\ (PARI/GP 2.15 or later).  The exit status is nonzero if any check fails.
\\
\\ Conventions.  "c(S, n)" is the coefficient of x^n.  A series "to precision
\\ N" carries the coefficients of degrees 0..N-1.  Iterates A^k are k-fold
\\ compositions, as in the OEIS entries.  Multi-line statements are wrapped in
\\ braces, as GP requires when reading a file.

default(parisizemax, 8*10^9);
read("oeis_terms.gp");

NFAIL = 0; NPASS = 0;
ok(name, cond) = if(cond, NPASS++, NFAIL++; print("  FAIL: ", name));
c(S, n) = polcoef(S, n);
ispow2(n) = n >= 1 && n == 2^valuation(n, 2);
s2(n) = hammingweight(n);

\\ vanish(S, k): S is known to precision at least k and its coefficients of
\\ degree < k are all zero.  (In GP, "S == O(x^k)" only compares up to the
\\ smaller of the two precisions, so it is not used.)
vanish(S, k) = serprec(S, x) >= k && prod(i = 0, k - 1, c(S, i) == 0);

\\ Compare computed terms with the published OEIS terms.
\\ D = [offset, terms]; f(n) returns the computed a(n).
{
oeis(id, D, f) =
  my(off = D[1], t = D[2], good = 1);
  for(i = 1, #t, if(f(off + i - 1) != t[i], good = 0; print("  mismatch ", id, " at n=", off + i - 1); break));
  ok(Str(id, " matches OEIS"), good);
  printf("  %s: all %d published terms reproduced from the OEIS definition\n", id, #t);
}

\\ Compositional inverse of a normalized series.  Over Z/MZ, GP's serreverse
\\ may try to invert non-units, so a Newton iteration
\\ R <- R - (F(R) - x)/F'(R) is used there; it divides only by a series with
\\ constant term 1.
{
rev(F, P) =
  my(R = x + O(x^P), D = deriv(F));
  if(type(polcoef(F, 1)) != "t_INTMOD", return(serreverse(F)));
  for(i = 1, 2 + logint(P, 2), R = R - (subst(F, x, R) - x) / subst(D, x, R));
  R;
}

\\ k-fold compositional iterate of a normalized series F (k may be negative).
{
iter(F, k, P) =
  my(G = x + O(x^P), H = if(k >= 0, F, rev(F, P)));
  for(i = 1, abs(k), G = subst(H, x, G));
  G;
}

\\ Coefficient-by-coefficient solver for eqf(A, P) = 0.  Once a_0..a_{n-1} are
\\ fixed, the residual coefficient of degree n+s must be an affine function of
\\ a_n with nonzero slope; this is checked at every step.
{
solvecoef(eqf, A0, n0, N, s) =
  my(A = A0, r0, r1, r2, sl, P);
  for(n = n0, N - 1,
    P = n + s + 1;
    r0 = c(eqf(A + O(x^P), P), n + s);
    r1 = c(eqf(A + x^n + O(x^P), P), n + s);
    r2 = c(eqf(A + 2*x^n + O(x^P), P), n + s);
    sl = r1 - r0;
    if(sl == 0 || r2 - r1 != sl, error("solvecoef: degenerate step at n=", n));
    A += (-r0 / sl) * x^n);
  A;
}
isintpoly(A) = prod(i = 0, poldegree(A), type(c(A, i)) == "t_INT");
\\ The equation holds through degree N-1+s.
holds(eqf, A, N, s) = vanish(eqf(A + O(x^(N + s)), N + s), N + s);

\\ ===========================================================================
print("== A195194: nested reversion; a(n) odd iff n is a power of 2");
N = 140;
nest(D, P) = my(F = x + O(x^P)); forstep(j = D, 0, -1, F = serreverse(x - (j + 1)*x*F)); F;
A = nest(N + 2, N); A2 = nest(N + 12, N);
ok("A195194 nest stabilized", vanish(A - A2, N));
oeis("A195194", OEIS_A195194, n -> c(A, n));
ok("A195194 parity", prod(n = 1, N - 1, (c(A, n) % 2 == 1) == ispow2(n)));
print("  parity pattern verified for n < ", N);

\\ ===========================================================================
print("== A378580 / A378581: theta substitutions modulo 4");
N = 200;
TH = 1 + 2*sum(j = 1, sqrtint(N), x^(j^2)) + O(x^N);
thetares(S, N) = prod(n = 1, N - 1, c(S, n) % 4 == if(issquare(n), 2, 0));
A = 1 + O(x^N); for(i = 1, N, A = A + TH - subst(A, x, x/A));
ok("A378580 equation", vanish(TH - subst(A, x, x/A), N));
oeis("A378580", OEIS_A378580, n -> c(A, n)); ok("A378580 residues", thetares(A, N));
A = 1 + O(x^N); for(i = 1, N, A = A + TH - subst(A, x, x*A));
ok("A378581 equation", vanish(TH - subst(A, x, x*A), N));
oeis("A378581", OEIS_A378581, n -> c(A, n)); ok("A378581 residues", thetares(A, N));
print("  residue 2 at squares and 0 elsewhere verified for 0 < n < ", N);

\\ ===========================================================================
print("== A380056: e.g.f. (exp(x)-1)/cos(2x)");
N = 400;
S = (exp(x + O(x^N)) - 1) / cos(2*x + O(x^N)); a = vector(N, i, (i - 1)! * c(S, i - 1));
oeis("A380056", OEIS_A380056, n -> a[n + 1]);
ok("A380056 integral", prod(n = 0, N - 1, type(a[n + 1]) == "t_INT"));
ok("A380056 a(n) == 1 mod 4 for n >= 1", prod(n = 1, N - 1, a[n + 1] % 4 == 1));
ok("A380056 a(n) == 2*2^n + 3*4^n mod 5", prod(n = 0, N - 1, (a[n + 1] - 2*2^n - 3*4^n) % 5 == 0));
ok("A380056 5 | a(n) iff 4 | n", prod(n = 0, N - 1, (a[n + 1] % 5 == 0) == (n % 4 == 0)));
print("  verified for n < ", N);

\\ ===========================================================================
print("== A380060 / A380680: rational theta sums");
N = 220;
\\ The bilateral sums in the OEIS names, with both signs of j summed explicitly.
bil(U, P) = sum(j = -sqrtint(P), sqrtint(P), if(j == 0, 1, x^(j^2) * ((U - x^j) / (1 - x^j*U))^j)) + O(x^P);
A = 1 + O(x^N); for(i = 1, N, A = 1 + 2*sum(j = 1, sqrtint(N), x^(j^2) * ((A - x^j) / (1 - x^j*A))^j) + O(x^N));
ok("A380060 bilateral equation", vanish(bil(A, N) - A, N));
oeis("A380060", OEIS_A380060, n -> c(A, n)); ok("A380060 residues", thetares(A, N));
B = bil(2, N);
oeis("A380680", OEIS_A380680, n -> c(B, n));
ok("A380680 counterexamples a(1)=4, a(2)=6", c(B, 1) == 4 && c(B, 2) == 6);
ok("A380680 corrected: residue 2 iff n = 2k^2", prod(n = 1, N - 1, c(B, n) % 4 == if(n % 2 == 0 && issquare(n / 2), 2, 0)));
print("  verified for 0 < n < ", N);

\\ ===========================================================================
print("== A389474 / A389475: cubic equations modulo 9 and 3");
N = 90;
e474(A, P) = subst(A, x, x^2 + 2*x^3 + 2*A^2) - 3*A^2;
A = solvecoef(e474, x, 2, N, 1);
ok("A389474 integral", isintpoly(A)); ok("A389474 equation", holds(e474, A, N, 1));
oeis("A389474", OEIS_A389474, n -> c(A, n));
A = A + O(x^N);
ok("A389474 A^2 == x^2 + 2x^3 mod 9", prod(n = 0, N - 1, (c(A^2, n) - (n == 2) - 2*(n == 3)) % 9 == 0));
ok("A389474 [x^n](A^(3k) - A(x^3)^k) == 0 mod 3, k <= 6", prod(k = 1, 6, my(D = A^(3*k) - subst(A, x, x^3)^k); prod(n = 0, N - 1, c(D, n) % 3 == 0)));
e475(A, P) = subst(A, x, 3*x^2) - (2*x^2 + A^2 - 2*A^3);
A = solvecoef(e475, x, 2, N, 1);
ok("A389475 integral", isintpoly(A)); ok("A389475 equation", holds(e475, A, N, 1));
oeis("A389475", OEIS_A389475, n -> c(A, n));
A = A + O(x^N); A3 = subst(A, x, x^3);
ok("A389475 A^3 == A(x^3) mod 3", prod(n = 0, N - 1, c(A^3 - A3, n) % 3 == 0));
ok("A389475 A^2 == x^2 + 2A(x^3) mod 3", prod(n = 0, N - 1, c(A^2 - x^2 - 2*A3, n) % 3 == 0));
print("  verified for n < ", N);

\\ ===========================================================================
print("== A389536 / A389537 / A389542: residues modulo 4");
N = 130;
e536(A, P) = x*A - subst(A, x, x^2 + 2*x^3);
A = solvecoef(e536, x, 2, N, 1);
ok("A389536 equation", holds(e536, A, N, 1)); oeis("A389536", OEIS_A389536, n -> c(A, n));
ok("A389536 residues", prod(n = 2, N - 1, c(A, n) % 4 == if(ispow2(n - 1), 2, 0)));
e537(A, P) = subst(A, x, A - x) - A^2;
A = solvecoef(e537, x, 2, N, 0);
ok("A389537 equation", holds(e537, A, N, 0)); oeis("A389537", OEIS_A389537, n -> c(A, n));
ok("A389537 residues", prod(n = 3, N - 1, c(A, n) % 4 == if(n % 3 == 0 && ispow2(n / 3), 2, 0)));
e542(A, P) = subst(A, x, A^2 - x^2) - 4*A^3;
A = solvecoef(e542, x, 2, N, 1);
ok("A389542 integral", isintpoly(A)); ok("A389542 equation", holds(e542, A, N, 1));
oeis("A389542", OEIS_A389542, n -> c(A, n));
ok("A389542 residues", prod(n = 2, N - 1, c(A, n) % 4 == if(ispow2(n - 1), 2, 0)));
print("  verified for n < ", N);

\\ ===========================================================================
print("== A392210: nested squares; a(2n-1) even for n > 1");
N = 200;
A = x + O(x^N); for(i = 1, N, A = x + subst(A, x, x/(1 - x))^2);
ok("A392210 equation", vanish(A - x - subst(A, x, x/(1 - x))^2, N));
\\ The nested title x + sq(x/(1-x) + sq(x/(1-2x) + ...)), truncated deep enough.
H = 0; forstep(j = N + 2, 1, -1, H = x/(1 - j*x) + H^2 + O(x^N));
ok("A392210 nested title agrees with A = x + A(x/(1-x))^2", vanish(x + H^2 - A, N));
oeis("A392210", OEIS_A392210, n -> c(A, n));
ok("A392210 odd indices > 1 even", prod(n = 2, N / 2, c(A, 2*n - 1) % 2 == 0));
print("  verified for 2n-1 < ", N);

\\ ===========================================================================
print("== A393171 / A393172: Catalan substitutions");
N = 200;
C = (1 - sqrt(1 - 4*x + O(x^(N + 1)))) / 2 + O(x^N);
e172(A, P) = subst(A, x, x - x^2) - x - A^2;
A72p = solvecoef(e172, x, 2, N, 0); A72 = A72p + O(x^N);
ok("A393172 equation", holds(e172, A72p, N, 0)); oeis("A393172", OEIS_A393172, n -> c(A72, n));
ok("A393172 residues", prod(n = 2, N - 1, c(A72, n) % 4 == if(ispow2(n), 2, 0)));
ok("A393172 series == 2C - x mod 4", prod(n = 0, N - 1, c(A72 - 2*C + x, n) % 4 == 0));
B = x + O(x^N); for(i = 1, N, B = x + subst(B, x, C)^2);
ok("A393171 equation", vanish(B - x - subst(B, x, C)^2, N)); oeis("A393171", OEIS_A393171, n -> c(B, n));
ok("A393171 link B = x + A393172^2", vanish(B - x - A72^2, N));
ok("A393171 residues", prod(n = 3, N - 1, c(B, n) % 8 == if(ispow2(n) || ispow2(n - 1), 4, 0)));
print("  verified for n < ", N);

\\ ===========================================================================
print("== A393856..A393859: A(x - x*A(q*x)/q) = x");
\\ A(qx)/q is the integral series sum_k a_k q^(k-1) x^k.
sc(A, q, P) = sum(k = 1, P - 1, c(A, k) * q^(k - 1) * x^k) + O(x^P);
{
scaled(q, N, M) =
  my(one = if(M, Mod(1, M), 1), A = one*x + O(x^N));
  for(i = 1, N, A = A + one*x - subst(A, x, x - x*sc(A, q, N)));
  A;
}
ids = ["A393856", "A393857", "A393858", "A393859"];
{
for(q = 4, 7,
  my(id = ids[q - 3], A = scaled(q, 26, 0), Am, NM = 300);
  ok(Str(id, " equation"), vanish(subst(A, x, x - x*sc(A, q, 26)) - x, 26));
  oeis(id, eval(Str("OEIS_", id)), n -> c(A, n));
  \\ A longer range modulo 2(q+1): the construction uses only ring operations,
  \\ so running it over Z/2(q+1)Z gives the reductions of the integer terms.
  Am = scaled(q, NM, 2*(q + 1));
  ok(Str(id, " modular run agrees with exact"), prod(n = 1, 25, c(Am, n) == Mod(c(A, n), 2*(q + 1))));
  ok(Str(id, " a(n) == 1 mod q+1"), prod(n = 1, NM - 1, lift(c(Am, n)) % (q + 1) == 1));
  if(q % 2 == 0, ok(Str(id, " a(n) odd iff n is a power of 2"), prod(n = 1, NM - 1, (lift(c(Am, n)) % 2 == 1) == ispow2(n))));
  printf("  %s: verified for n < %d (q = %d)\n", id, NM, q));
}

\\ ===========================================================================
print("== A396093: third iterate of x/(1-x)^2");
N = 600;
Bx = x/(1 - x)^2 + O(x^N); A = subst(Bx, x, subst(Bx, x, Bx));
oeis("A396093", OEIS_A396093, n -> c(A, n));
ok("A396093 parity classification", prod(n = 0, N - 1, (c(A, n) % 2 == 1) == (n % 10 == 1 || n % 10 == 3 || n % 10 == 7 || n % 10 == 9)));
print("  verified for n < ", N);

\\ ===========================================================================
print("== Consecutive iterates: A(x) = x + A^r(x) A^(r+1)(x)");
{
consec(r, N, M) =
  my(one = if(M, Mod(1, M), 1), A = one*x + O(x^N));
  for(i = 1, N, A = one*x + iter(A, r, N) * iter(A, r + 1, N));
  A;
}
idr = [[2, "A396099"], [4, "A396798"], [5, "A396807"]];
{
foreach(idr, t,
  my(r = t[1], id = t[2], A = consec(r, 24, 0));
  ok(Str(id, " equation"), vanish(A - x - iter(A, r, 24)*iter(A, r + 1, 24), 24));
  oeis(id, eval(Str("OEIS_", id)), n -> c(A, n)));
}
\\ General theorem: modulo 2r, A^k == x/(1-kx) + r*[r even and k odd]*x^4/(1-x)^3.
N = 90;
{
for(r = 1, 8,
  my(M = 2*r, A = consec(r, N, M), good = 1, G, Tk);
  for(k = -4, 9,
    G = iter(A, k, N);
    Tk = x/(1 - k*x) + if(r % 2 == 0 && k % 2, r*x^4/(1 - x)^3, 0) + O(x^N);
    for(n = 0, N - 1, if(c(G, n) != Mod(c(Tk, n), M), good = 0)));
  ok(Str("iterate formula mod 2r, r=", r), good));
}
print("  iterate formula verified for r = 1..8, k = -4..9, n < ", N);
\\ The literal source statements.
N = 160;
A = consec(2, N, 8); A2 = iter(A, 2, N); A3 = iter(A, 3, N);
ok("A396099 all odd", prod(n = 1, N - 1, lift(c(A, n)) % 2 == 1));
ok("A396099 [1,3,3,1] mod 4 for n > 2", prod(n = 3, N - 1, lift(c(A, n)) % 4 == [1, 3, 3, 1][(n - 3) % 4 + 1]));
ok("A396099 [x^n]A(A(x)) == 0 mod 4, n > 2", prod(n = 3, N - 1, lift(c(A2, n)) % 4 == 0));
ok("A396099 [x^n](A - x A^3) == 2 mod 4, n > 2", prod(n = 3, N - 1, lift(c(A - x*A3, n)) % 4 == 2));
A = consec(5, N, 10);
ok("A396807 a(n) == 1 mod 10", prod(n = 1, N - 1, lift(c(A, n)) == 1));
ok("A396807 iterates: [x^n]A^k == k^(n-1) mod 10, -6 <= k <= 12", prod(k = -6, 12, my(G = iter(A, k, N)); prod(n = 1, N - 1, c(G, n) == Mod(k, 10)^(n - 1))));
A = consec(4, N, 8); res = vector(N - 1, n, lift(c(A, n)));
print("  A396798 residues mod 8 for n = 1..16: ", res[1..16]);
ok("A396798 literal claim (block 1,1,5,5 starting at n=1) is false", res[1..4] != [1, 1, 5, 5]);
ok("A396798 corrected: block 1,1,5,5 starting at n=2", prod(n = 2, N - 1, res[n] == [1, 1, 5, 5][(n - 2) % 4 + 1]));
it(k) = iter(A, k, N);
ok("A396798 A^2: 0 mod 8 for n > 3", prod(n = 4, N - 1, c(it(2), n) == 0));
ok("A396798 A^3: [3,1,7,5] for n > 1", prod(n = 2, N - 1, lift(c(it(3), n)) == [3, 1, 7, 5][(n - 2) % 4 + 1]));
ok("A396798 A^4: 0 mod 8 for n > 2", prod(n = 3, N - 1, c(it(4), n) == 0));
ok("A396798 A^5: [5,1,1,5] for n > 1", prod(n = 2, N - 1, lift(c(it(5), n)) == [5, 1, 1, 5][(n - 2) % 4 + 1]));
ok("A396798 A^6: 0 mod 8 for n > 3", prod(n = 4, N - 1, c(it(6), n) == 0));
ok("A396798 A^7: [7,1,3,5] for n > 1", prod(n = 2, N - 1, lift(c(it(7), n)) == [7, 1, 3, 5][(n - 2) % 4 + 1]));
ok("A396798 A^8: 0 mod 8 for n > 1", prod(n = 2, N - 1, c(it(8), n) == 0));
print("  A396099/A396798/A396807 source statements verified for n < ", N);

\\ ===========================================================================
print("== A396102 and its family F^r = (1+x) F^(r-1)");
N = 70;
fam(r) = (A, P) -> iter(A, r, P) - (1 + x)*iter(A, r - 1, P);
A = solvecoef(fam(3), x, 2, N, 0);
ok("A396102 integral", isintpoly(A)); ok("A396102 equation", holds(fam(3), A, N, 0));
oeis("A396102", OEIS_A396102, n -> c(A, n));
A = A + O(x^N);
ok("A396102 a(n) == 1 mod 3", prod(n = 1, N - 1, c(A, n) % 3 == 1));
ok("A396102 natural iterates k^(n-1) mod 3", prod(k = 0, 8, my(G = iter(A, k, N)); prod(n = 1, N - 1, (c(G, n) - k^(n - 1)) % 3 == 0)));
{
for(r = 2, 7,
  my(Ar = solvecoef(fam(r), x, 2, 40, 0));
  ok(Str("family r=", r, ": integral and == x/(1-x) mod r"), isintpoly(Ar) && prod(n = 1, 39, (c(Ar, n) - 1) % r == 0)));
}
print("  verified for n < ", N, "; family r = 2..7 for n < 40");

\\ ===========================================================================
print("== A396843 / A396844 and the family A_m(x A_m - m x A_m^2) = x^2");
\\ Hanna's construction from the OEIS entry: A = (1 - sqrt(1 - 4m B(x^2)/x))/(2m),
\\ where B is the compositional inverse of the previous A.
{
hanna(m, N) =
  my(A = x + O(x^N), B);
  for(i = 1, 2 + logint(N, 2), B = serreverse(A); A = (1 - sqrt(1 - 4*m*subst(B, x, x^2)/x + O(x^N))) / (2*m));
  A;
}
modsq(A, m, n) = (c(A, n) - if(ispow2(n - 1), m*(-1)^valuation(n - 1, 2), 0)) % m^2 == 0;
N = 260;
{
for(m = 3, 4,
  my(A = hanna(m, N), B = serreverse(A), id = if(m == 3, "A396843", "A396844"));
  ok(Str(id, " equation"), vanish(subst(A, x, x*A - m*x*A^2) - x^2, N + 1));
  oeis(id, eval(Str("OEIS_", id)), n -> c(A, n));
  ok(Str(id, " residues mod m^2"), prod(n = 2, N - 1, modsq(A, m, n)));
  ok(Str(id, " binary divisibility of series and inverse"), prod(n = 1, N - 1, c(A, n) % m^s2(n - 1) == 0 && c(B, n) % m^s2(n - 1) == 0));
  if(m == 3, ok("A396843 all odd", prod(n = 1, N - 1, c(A, n) % 2 == 1)));
  if(m == 4,
    ok("A396844 even for n >= 2", prod(n = 2, N - 1, c(A, n) % 2 == 0));
    print("  A396844: a(17) mod 16 = ", c(A, 17) % 16, " although 17 > 8 is not of the form 2*4^k+1");
    ok("A396844 literal OEIS clause fails at n = 17", c(A, 17) % 16 == 4)));
}
{
for(m = 2, 12,
  my(A = hanna(m, 70), B = serreverse(A), good = 1, e);
  if(!vanish(subst(A, x, x*A - m*x*A^2) - x^2, 71), good = 0);
  for(n = 2, 69,
    if(!modsq(A, m, n), good = 0);
    if(c(A, n) % m^s2(n - 1) || c(B, n) % m^s2(n - 1), good = 0);
    if(c(A, n) % 2 != m % 2, good = 0);
    \\ the smallest possible p-exponent occurs exactly at n = 2^j + 1
    foreach(factor(m)[, 1], p, e = valuation(m, p); if((c(A, n) != 0 && valuation(c(A, n), p) == e) != ispow2(n - 1), good = 0)));
  ok(Str("parameter family m=", m), good));
}
print("  m = 3, 4 verified for n < ", N, "; m = 2..12 for n < 70");

\\ ===========================================================================
print("== A355872: x = Sum_{j in Z} (-x)^(j^2) A(x)^((j-1)^2)");
\\ Each coefficient involves only finitely many j: the factor (-x)^(j^2) has degree j^2.
\\ The j = 0 term is A itself, so A = x - Sum_{j != 0} (...), solved by fixed-point iteration.
{
bil(M, N) =
  my(one = if(M, Mod(1, M), 1), A = O(x^N), R, J = sqrtint(N) + 1);
  for(it = 1, N,
    R = one*x + O(x^N);
    for(j = -J, J, if(j != 0 && j^2 < N, R -= (-x)^(j^2) * A^((j - 1)^2)));
    A = R);
  A;
}
N = 121; A = bil(0, N);
ok("A355872 equation", vanish(sum(j = -12, 12, if(j^2 < N, (-x)^(j^2) * A^((j - 1)^2), 0)) - x, N));
ok("A355872 only degrees 4n-3 occur", prod(d = 0, N - 1, d % 4 == 1 || c(A, d) == 0));
oeis("A355872", OEIS_A355872, n -> c(A, 4*n - 3));
ok("A355872 a(n) == 2*(-1)^(n-1) mod 16, n <= 30", prod(n = 1, 30, (c(A, 4*n - 3) - 2*(-1)^(n - 1)) % 16 == 0));
ok("A355872 conjectures: a(n) == 2 mod 4; a(2n-1) == 2, a(2n) == 6 mod 8", prod(n = 1, 30, my(t = c(A, 4*n - 3)); t % 4 == 2 && t % 8 == if(n % 2, 2, 6)));
N = 1201; Am = bil(16, N);
ok("A355872 modular run agrees with exact", prod(d = 0, 120, c(Am, d) == Mod(c(A, d), 16)));
ok("A355872 reduction mod 16 equals 2x/(1+x^4), degree < 1201", vanish(Am - Mod(2, 16)*x/(1 + x^4), N));
print("  verified exactly for n <= 30 and modulo 16 for n <= 300");

\\ ===========================================================================
print("== A394576: greedy, avoiding sums of three consecutive terms");
{
greedy(M) =
  my(a = vector(M), forb = vector(4*M + 10), t);
  a[1] = 1;
  for(n = 1, M - 1,
    t = a[n] + 1; while(forb[t], t++);
    a[n + 1] = t;
    if(n >= 2, my(s = a[n - 1] + a[n] + a[n + 1]); if(s <= #forb, forb[s] = 1)));
  a;
}
M = 100000; a = greedy(M);
oeis("A394576", OEIS_A394576, n -> a[n]);
ok("A394576 floor((4n-3)/3) <= a(n) <= floor((4n-1)/3), n <= 100000", prod(n = 1, M, (4*n - 3)\3 <= a[n] && a[n] <= (4*n - 1)\3));
ok("A394576 a(3k) = 4k-1, 3k <= 100000", prod(k = 1, M\3, a[3*k] == 4*k - 1));
SA = Set(a);
ok("A394576 no term is a sum of three consecutive terms", prod(k = 1, M - 2, !setsearch(SA, a[k] + a[k + 1] + a[k + 2])));
print("  verified for n <= ", M);

\\ ===========================================================================
print("== A397346: A(x) = exp(x + Sum_{n>=2} (2n^2-1)/(2n^2) a(n) x^n)");
\\ From the definition: [x^n] log A = (2n^2-1)/(2n^2) a(n) for n >= 2.  With
\\ a(n) unknown, [x^n] log A = a(n) + q, where q is computed from a(0..n-1);
\\ hence a(n) = -2 n^2 q.
{
expdef(N) =
  my(A = 1 + x + O(x^2), q);
  for(n = 2, N - 1,
    q = c(log(truncate(A) + O(x^(n + 1))), n);
    A = truncate(A) - 2*n^2*q*x^n + O(x^(n + 1)));
  A;
}
N = 61; A = expdef(N);
ok("A397346 coefficients are integers", prod(n = 0, N - 1, type(c(A, n)) == "t_INT"));
ok("A397346 definition holds", vanish(A - exp(x + sum(n = 2, N - 1, (2*n^2 - 1)/(2*n^2)*c(A, n)*x^n) + O(x^N)), N));
oeis("A397346", OEIS_A397346, n -> c(A, n));
\\ The printed recurrence (7), run further.
{
rec7(N) =
  my(a = vector(N + 1)); a[1] = 1; a[2] = 1;
  for(n = 2, N, a[n + 1] = 2*n*a[n] + n*sum(k = 1, n - 2, (2*(k + 1)^2 - 1)/(k + 1) * a[k + 2] * a[n - k]));
  a;
}
NR = 400; r = rec7(NR);
ok("A397346 recurrence (7) agrees with the definition, n < 61", prod(n = 0, N - 1, r[n + 1] == c(A, n)));
ok("A397346 n divides a(n), n <= 400", prod(n = 1, NR, type(r[n + 1]) == "t_INT" && r[n + 1] % n == 0));
ok("A397346 a(n) mod 8 repeats [4,2,0,2] from n = 2, n <= 400", prod(n = 2, NR, r[n + 1] % 8 == [4, 2, 0, 2][(n - 2) % 4 + 1]));
ok("A397346 a(n)/n mod 8 is 6 if n == 3 mod 4, else 2 (2 <= n <= 400)", prod(n = 2, NR, (r[n + 1]/n) % 8 == if(n % 4 == 3, 6, 2)));
print("  definition verified for n < 61; residues for n <= ", NR);

\\ ===========================================================================
print("");
printf("RESULT: %d checks passed, %d failed\n", NPASS, NFAIL);
quit(NFAIL > 0);
