\\ Numerical checks of the claims made in the Discussion sections of the 29 papers.
\\
\\ A companion to independent_checks.gp.  That script tests the main theorems; this one tests
\\ the further observations in each paper's Discussion section (the text between
\\ \section{Discussion} and \section*{About this paper}): generalizations,
\\ congruences modulo higher powers, periods found by computer, agreement with
\\ other OEIS entries, sign patterns, and the side remarks that the papers prove
\\ in the text.  Claims that only restate a main theorem are left to
\\ independent_checks.gp.  Every sequence is recomputed here from its OEIS
\\ definition; the published terms of the other OEIS entries cited in the
\\ Discussions are in discussion_terms.gp.
\\
\\ Each check prints "ok" or "FAIL" with a short description of the claim and
\\ of the range tested.  Lines starting with "info" report values that are
\\ printed for the reader but are not claims of the papers.  A finite check is
\\ evidence, not a proof; several of these claims are stated in the papers as
\\ computer observations only.  Run from this directory with
\\     gp -q discussion_checks.gp < /dev/null
\\ (PARI/GP 2.15 or later).  The exit status is nonzero if any check fails.
\\
\\ Conventions.  "c(S, n)" is the coefficient of x^n.  A series "to precision
\\ N" carries the coefficients of degrees 0..N-1.  Iterates F^k are k-fold
\\ compositions.  For a sequence stored in a vector v, v[n+1] is the term of
\\ index n.  Random tests use fixed seeds, so the output is reproducible.
\\ Multi-line statements are wrapped in braces, as GP requires when reading a
\\ file.

default(parisizemax, 8*10^9);
read("oeis_terms.gp");
read("discussion_terms.gp");

NFAIL = 0; NPASS = 0;
ok(name, cond) = if(cond, NPASS++; print("  ok    ", name), NFAIL++; print("  FAIL  ", name));
info(s) = print("  info  ", s);
c(S, n) = polcoef(S, n);
ispow2(n) = n >= 1 && n == 2^valuation(n, 2);
s2(n) = hammingweight(n);
\\ coefficient vector [c(S,0), ..., c(S,N-1)], with residues lifted to integers
coefs(S, N) = vector(N, i, lift(c(S, i - 1)));

\\ vanish(S, k): S is known to precision at least k and its coefficients of
\\ degree < k are all zero.  (In GP, "S == O(x^k)" only compares up to the
\\ smaller of the two precisions, so it is not used.)
vanish(S, k) = serprec(S, x) >= k && prod(i = 0, k - 1, c(S, i) == 0);
\\ congruent(S, T, m, k): the coefficients of degree < k of S and T agree
\\ modulo m.  S, T may be series, polynomials or rational functions; series
\\ over Z/MZ are allowed when m divides M.
congruent(S, T, m, k) = my(D = lift(S - T + O(x^k))); prod(i = 0, k - 1, c(D, i) % m == 0);
\\ agree(S, T, k): the coefficients of degree < k are equal.
agree(S, T, k) = prod(i = 0, k - 1, c(S, i) == c(T, i));

\\ Compare computed terms with published OEIS terms.
\\ D = [offset, terms]; f(n) returns the computed a(n).
{
oeis(id, D, f) =
  my(off = D[1], t = D[2], good = 1);
  for(i = 1, #t, if(f(off + i - 1) != t[i], good = 0; print("  mismatch ", id, " at n=", off + i - 1); break));
  ok(Str(id, ": all ", #t, " published terms reproduced"), good);
}

\\ perfrom(v, m, P, s): the residues modulo m of v repeat with period P from
\\ index s on, for every index in the computed range.
perfrom(v, m, P, s) = prod(n = s, #v - 1 - P, (v[n + P + 1] - v[n + 1]) % m == 0);
\\ evper(v, m): the smallest period P that holds on the second half of the
\\ data, and the earliest index s from which P holds on the whole range.  It
\\ is used only for the "info" lines that report the exact period and start.
{
evper(v, m) =
  my(L = #v, P = 0, s);
  for(p = 1, L \ 3, if(perfrom(v[L \ 2 + 1 .. L], m, p, 0), P = p; break));
  if(!P, return([0, -1]));
  s = L \ 2; while(s > 0 && (v[s + P] - v[s]) % m == 0, s--);
  [P, s];
}
{
perclaim(id, v, m, P, s, rng) =
  my(e = evper(v, m), Pc = if(P, P, e[1]));
  ok(Str(id, ": residues mod ", m, " periodic with period ", Pc, " from n = ", s, " (n < ", rng, ")"), perfrom(v[1 .. rng], m, Pc, s));
  info(Str(id, " mod ", m, ": smallest period ", e[1], ", earliest start n = ", e[2], " (computed for n < ", #v, ")"));
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

\\ Fixed-point solver with growing precision.  step(A, P) must return a series
\\ whose coefficient of degree P-1 is correct as soon as those of lower degree
\\ are.  Starting from A0 (correct below degree n0), the result is correct to
\\ precision N.
{
fixpt(step, A0, n0, N) =
  my(A = A0);
  for(P = n0 + 1, N, A = truncate(A) + O(x^P); A = step(A, P));
  A;
}

\\ Random integer series with coefficients in [-B, B] in degrees lo..hi.
rser(lo, hi, B) = sum(k = lo, hi, (random(2*B + 1) - B) * x^k);

\\ ===========================================================================
print("== A195194: Discussion (the tower modulo a prime p)");
N = 140;
nest(D, P) = my(F = x + O(x^P)); forstep(j = D, 0, -1, F = serreverse(x - (j + 1)*x*F)); F;
A = nest(N + 2, N);
oeis("A195194", OEIS_A195194, n -> c(A, n));
\\ The finite tower modulo p: F_{p-1} = x, F_j = INV(x - (j+1) x F_{j+1}).
tower(p, P) = my(F = Mod(1, p)*x + O(x^P)); forstep(j = p - 2, 0, -1, F = rev(Mod(1, p)*x - Mod(j + 1, p)*x*F, P)); F;
{
foreach([2, 3, 5, 7, 11, 13], p,
  my(T = tower(p, N));
  ok(Str("p = ", p, ": F_0 mod p equals the finite tower INV(x - x INV(x - 2x ... INV(x - (p-1)x^2))) (n < ", N, ")"),
     prod(n = 0, N - 1, c(T, n) == Mod(c(A, n), p))));
}
\\ Algebraicity, following the argument in the text: Q(x,y) = y - (p-1)y^2 - x
\\ annihilates INV(x - (p-1)x^2); if Q_F annihilates F, then
\\ Q_U(x,u) = Q_F(x, (x-u)/(w x)) (w x)^deg annihilates U = x - w x F, and
\\ Q_V(x,y) = Q_U(y,x) annihilates V = INV(U).
{
algrel(p) =
  my(Q = y - (p - 1)*y^2 - x, dy);
  forstep(j = p - 3, 0, -1,
    dy = poldegree(Q, y);
    Q = subst(Q, y, (x - y)/((j + 1)*x)) * ((j + 1)*x)^dy;
    Q = substvec(Q, [x, y], [y, x]));
  Q;
}
\\ The test Q(x, F_0 + x^20) != 0 shows that the check can tell F_0 from a
\\ nearby series; it needs a precision above 20 + v, where v is the valuation of
\\ dQ/dy(x, F_0).  For p = 11, v = 221, so the relation is tested on the finite
\\ tower (equal to F_0 mod p by the identity above) to precision 300.
{
foreach([3, 5, 7, 11], p,
  my(NA = if(p < 11, N, 300), Q = algrel(p), T = lift(tower(p, NA)), Qm, v1, v2, dv);
  Qm = Q * Mod(1, p);
  v1 = subst(Q, y, T + O(x^NA)) * Mod(1, p);
  v2 = subst(Q, y, T + x^20 + O(x^NA)) * Mod(1, p);
  dv = valuation(lift(subst(deriv(Q, y), y, T + O(x^NA)) * Mod(1, p)), x);
  ok(Str("p = ", p, ": the constructed Q(x,y) is a nonzero polynomial mod p, Q(x, F_0) == 0 (n < ", NA, "), and Q(x, F_0 + x^20) != 0"),
     type(Q) == "t_POL" && Qm != 0 && vanish(v1, NA) && !vanish(v2, NA));
  info(Str("p = ", p, ": deg_x Q = ", poldegree(Q, x), ", deg_y Q = ", poldegree(Q, y), ", valuation of dQ/dy(x, F_0) = ", dv)));
}
info("p-automaticity of a(n) mod p (Christol's theorem) is a qualitative statement; not tested");

\\ ===========================================================================
print("== A378580: Discussion (generalization; the two entries agree modulo 8)");
\\ Solutions of U(x/U) = T and U(xU) = T with constant term 1.  In degree n
\\ the left side is u_n plus terms in u_0..u_{n-1}, so each step fixes one
\\ more coefficient.
solq(T, N) = fixpt((U, P) -> U + T - subst(U, x, x/U), 1 + O(x), 0, N);
solp(T, N) = fixpt((U, P) -> U + T - subst(U, x, x*U), 1 + O(x), 0, N);
N = 160;
TH = 1 + 2*sum(j = 1, sqrtint(N), x^(j^2)) + O(x^N);
A80 = solq(TH, N); A81 = solp(TH, N);
ok("A378580 and A378581: defining equations hold", vanish(subst(A80, x, x/A80) - TH, N) && vanish(subst(A81, x, x*A81) - TH, N));
oeis("A378580", OEIS_A378580, n -> c(A80, n)); oeis("A378581", OEIS_A378581, n -> c(A81, n));
ok("a(2) = 4 (A378580) and a(2) = -4 (A378581), while [x^2] theta = 0: neither is == theta mod 8", c(A80, 2) == 4 && c(A81, 2) == -4 && c(TH, 2) == 0);
ok(Str("A378580 == A378581 mod 8 for every n < ", N), congruent(A80, A81, 8, N));
ok("A378580 and A378581 are not congruent mod 16: a(2) differ by 8", (c(A80, 2) - c(A81, 2)) % 16 == 8);
\\ 20 random targets T = 1 + 2S with integer S, S(0) = 0, up to degree 59.
setrand(378580);
{
my(g4 = 1, g8 = 1, geq = 1, T, U1, U2);
for(t = 1, 20,
  T = 1 + 2*rser(1, 59, 10) + O(x^60);
  U1 = solp(T, 60); U2 = solq(T, 60);
  if(!vanish(subst(U1, x, x*U1) - T, 60) || !vanish(subst(U2, x, x/U2) - T, 60), geq = 0);
  if(!isintpoly(truncate(U1)) || !isintpoly(truncate(U2)), geq = 0);
  if(!congruent(U1, T, 4, 60) || !congruent(U2, T, 4, 60), g4 = 0);
  if(!congruent(U1, U2, 8, 60), g8 = 0));
ok("20 random targets T = 1 + 2S: both solutions exist with integer coefficients (degree <= 59)", geq);
ok("20 random targets T = 1 + 2S: both solutions == T mod 4 (degree <= 59)", g4);
ok("20 random targets T = 1 + 2S: the two solutions agree mod 8 (degree <= 59)", g8);
}

\\ ===========================================================================
print("== A378581: Discussion");
info("the Discussion is the same as for A378580; all its claims are checked in that section");

\\ ===========================================================================
print("== A380056: Discussion (other moduli)");
N = 400;
S = (exp(x + O(x^N)) - 1) / cos(2*x + O(x^N)); a = vector(N, i, (i - 1)! * c(S, i - 1));
oeis("A380056", OEIS_A380056, n -> a[n + 1]);
perclaim("A380056", a, 3, 8, 1, N);
perclaim("A380056", a, 7, 48, 1, N);
perclaim("A380056", a, 8, 4, 3, N);
ok(Str("A380056: a(n) mod 8 = 5, 1, 1, 5 for n == 3, 0, 1, 2 mod 4, n >= 3 (n < ", N, ")"), prod(n = 3, N - 1, a[n + 1] % 8 == [1, 1, 5, 5][n % 4 + 1]));
perclaim("A380056", a, 16, 8, 3, N);
ok("-4 is a square mod 5 (-4 == 1 = 1^2), but not mod 3 or mod 7", Mod(-4, 5) == Mod(1, 5)^2 && !issquare(Mod(-4, 3)) && !issquare(Mod(-4, 7)));
ok("8 = 3^2 - 1 and 48 = 7^2 - 1", 3^2 - 1 == 8 && 7^2 - 1 == 48);

\\ ===========================================================================
print("== A380060: Discussion (mod 8; the general principle for 1 + 2 Sigma(U))");
N = 100;
Qj(U, j) = (U - x^j)/(1 - x^j*U);
Sig(U, P) = sum(j = 1, sqrtint(P), x^(j^2) * Qj(U + O(x^P), j)^j) + O(x^P);
TH1 = 1 + 2*sum(j = 1, sqrtint(N), x^(j^2)) + O(x^N);
TH2 = subst(TH1, x, x^2) + O(x^N);
A = fixpt((U, P) -> 1 + 2*Sig(U, P), 1 + O(x), 0, N);
ok("A380060: A = 1 + 2 Sigma(A) holds", vanish(A - 1 - 2*Sig(A, N), N));
oeis("A380060", OEIS_A380060, n -> c(A, n));
ok("A380060: a(2) = 4 while [x^2] theta = 0, so the theorem does not extend to mod 8", c(A, 2) == 4 && c(TH1, 2) == 0);
ok("Q_j(1) = 1 and Q_j(0) = -x^j for j <= 10", prod(j = 1, 10, Qj(1, j) == 1 && Qj(0, j) == -x^j));
ok(Str("U = A (A380060) is == 1 mod 2 and 1 + 2 Sigma(A) == theta(x) mod 4 (n < ", N, ")"), c(A, 0) % 2 == 1 && prod(n = 1, N - 1, c(A, n) % 2 == 0) && congruent(1 + 2*Sig(A, N), TH1, 4, N));
ok(Str("U = 2 (A380680) gives 1 + 2 Sigma(2) == theta(x^2) mod 4 (n < ", N, ")"), congruent(1 + 2*Sig(2, N), TH2, 4, N));
setrand(380060);
{
my(g1 = 1, g0 = 1, gm = 1, U, V);
for(t = 1, 10,
  U = (2*random(10) + 1) + 2*rser(1, N - 1, 5);
  if(!congruent(1 + 2*Sig(U, N), TH1, 4, N), g1 = 0);
  U = 2*rser(0, N - 1, 5);
  if(!congruent(1 + 2*Sig(U, N), TH2, 4, N), g0 = 0);
  U = rser(0, N - 1, 5); V = U + 2*rser(0, N - 1, 5);
  if(!congruent(1 + 2*Sig(U, N), 1 + 2*Sig(V, N), 4, N), gm = 0));
ok(Str("10 random U == 1 mod 2: 1 + 2 Sigma(U) == theta(x) mod 4 (n < ", N, ")"), g1);
ok(Str("10 random U == 0 mod 2: 1 + 2 Sigma(U) == theta(x^2) mod 4 (n < ", N, ")"), g0);
ok(Str("10 random pairs U == V mod 2: 1 + 2 Sigma(U) == 1 + 2 Sigma(V) mod 4 (n < ", N, ")"), gm);
}

\\ ===========================================================================
print("== A380680: Discussion");
{
my(t = OEIS_A380680[2], off = OEIS_A380680[1], bad = []);
for(i = 1, #t, my(n = off + i - 1); if(n >= 1 && t[i] % 4 != if(issquare(n), 2, 0), bad = concat(bad, n)));
ok(Str("published terms contradict the conjecture, first at n = 1 (a(1) = ", t[2 - off], ")"), #bad && bad[1] == 1 && t[2 - off] == 4);
info(Str("published indices contradicting the residue-2-at-squares conjecture: ", bad));
}
info("the general principle for 1 + 2 Sigma(U) is checked in the A380060 section");

\\ ===========================================================================
print("== A389474: Discussion (A modulo 9; A^2 modulo powers of 3)");
N = 90;
e474(A, P) = subst(A, x, x^2 + 2*x^3 + 2*A^2) - 3*A^2;
A74p = solvecoef(e474, x, 2, N, 1); A74 = A74p + O(x^N);
ok("A389474: integral solution of the defining equation", isintpoly(A74p) && holds(e474, A74p, N, 1));
oeis("A389474", OEIS_A389474, n -> c(A74, n));
setrand(389474);
{
my(good = 1, W);
for(t = 1, 5, W = rser(0, N - 1, 20) + O(x^N);
  for(k = 1, 6, if(!congruent(W^(3*k), subst(W, x, x^3)^k, 3, N), good = 0)));
ok(Str("statement (4) for 5 random integer series W: [x^n](W^(3k) - W(x^3)^k) == 0 mod 3, k <= 6, n < ", N), good);
}
Wb = x*sqrt(1 + 2*x + O(x^N));
ok("x (1+2x)^(1/2) = x + x^2 - x^3/2 + x^4/2 - 5x^5/8 + ...", vector(5, n, c(Wb, n)) == [1, 1, -1/2, 1/2, -5/8]);
ok("2*5 = 10 == 1 mod 9; -1/2 == 4 == a(3) and 1/2 == 5 == a(4) = 14 mod 9", Mod(2*5, 9) == 1 && Mod(-1/2, 9) == 4 && c(A74, 3) % 9 == 4 && Mod(1/2, 9) == 5 && c(A74, 4) == 14 && 14 % 9 == 5);
ok(Str("A == x (1+2x)^(1/2) mod 9 (degree < ", N, ")"), prod(n = 0, N - 1, Mod(c(A74, n), 9) == Mod(c(Wb, n), 9)));
S74 = A74^2; Q74 = x^2 + 2*x^3;
ok(Str("A^2 == x^2 + 2x^3 + 9x^4 + 9x^5 + 9x^6 mod 27 (degree < ", N, ")"), congruent(S74, Q74 + 9*(x^4 + x^5 + x^6), 27, N));
ok(Str("A^2 is == mod 3^k to a polynomial of degree <= 3k-3, for 2 <= k <= 7 (degree < ", N, ")"), prod(k = 2, 7, prod(n = 3*k - 2, N - 1, c(S74, n) % 3^k == 0)));
R1 = serreverse(A74); K = 3*R1 - 2*x; Kinv = serreverse(K);
ok("Q + 2S = R(3S) exactly, with S = A^2, Q = x^2 + 2x^3, R the inverse of A", vanish(Q74 + 2*S74 - subst(R1, x, 3*S74), N));
ok("K(u) = 3R(u) - 2u has integer coefficients, K(3S) = 3Q, and K^(-1)(v) == v mod 3 with integer coefficients", isintpoly(truncate(K)) && vanish(subst(K, x, 3*S74) - 3*Q74, N) && isintpoly(truncate(Kinv)) && congruent(Kinv, x, 3, N));
kj = vector(N - 1, j, c(Kinv, j) / 3);
ok("k_2 = 1", kj[2] == 1);
info(Str("k_2..k_8 = ", kj[2 .. 8]));
ok(Str("A^2 = Q + sum_{j>=2} 3^j k_j Q^j exactly (degree < ", N, ")"), vanish(S74 - Q74 - sum(j = 2, N \ 2, 3^j * kj[j] * Q74^j), N));

\\ ===========================================================================
print("== A389475: Discussion (A modulo 9; the family R(3x^2) = 2x^2 + R^2 + 2sR^3)");
e475(A, P) = subst(A, x, 3*x^2) - (2*x^2 + A^2 - 2*A^3);
A75p = solvecoef(e475, x, 2, N, 1); A75 = A75p + O(x^N);
ok("A389475: integral solution of the defining equation", isintpoly(A75p) && holds(e475, A75p, N, 1));
oeis("A389475", OEIS_A389475, n -> c(A75, n));
setrand(389475);
{
my(good = 1, W);
for(t = 1, 5, W = rser(0, N - 1, 20) + O(x^N); if(!congruent(W^3, subst(W, x, x^3), 3, N), good = 0));
ok(Str("statement (a) for 5 random integer series W: W^3 == W(x^3) mod 3 (n < ", N, ")"), good);
}
ok(Str("A(3x^2) == 3x^2 mod 9 (degree < ", N, ")"), congruent(subst(A75, x, 3*x^2), 3*x^2, 9, N));
ok(Str("A^2 - 2A^3 == x^2 mod 9 (degree < ", N, ")"), congruent(A75^2 - 2*A75^3, x^2, 9, N));
ok(Str("a(2) = 1 and A^2 - 2A^3 == x^2 + 9x^4 mod 27 (degree < ", N, ")"), c(A75, 2) == 1 && congruent(A75^2 - 2*A75^3, x^2 + 9*x^4, 27, N));
V = x*sqrt(1 - 2*x + O(x^N));
ok("V = x (1-2x)^(1/2) satisfies V^2 = x^2 - 2x^3", vanish(V^2 - x^2 + 2*x^3, N + 1));
Vinv = serreverse(V);
ok(Str("A == compositional inverse of x (1-2x)^(1/2) mod 9 (degree < ", N, ")"), prod(n = 0, N - 1, Mod(c(A75, n), 9) == Mod(c(Vinv, n), 9)));
efam(s) = (R, P) -> subst(R, x, 3*x^2) - (2*x^2 + R^2 + 2*s*R^3);
{
my(good = 1, Rs, NF = 40);
for(s = -6, 6, Rs = solvecoef(efam(s), x, 2, NF, 1);
  if(!isintpoly(Rs) || !holds(efam(s), Rs, NF, 1), good = 0);
  if(s == -1 && !agree(Rs, A75, NF), good = 0);
  if(s == 1 && !agree(Rs, R1, NF), good = 0));
ok("family: integer solution R_s for every s in [-6, 6]; R_{-1} = A389475 and R_1 = inverse of A389474 (degree < 40)", good);
}

\\ ===========================================================================
print("== A389536: Discussion (modulo 8)");
N = 130;
e536(A, P) = x*A - subst(A, x, x^2 + 2*x^3);
A = solvecoef(e536, x, 2, N, 1);
ok("A389536: defining equation holds", holds(e536, A, N, 1)); oeis("A389536", OEIS_A389536, n -> c(A, n));
{
r536(n) = my(m = n - 1, i, j);
  if(ispow2(m), return(2));
  if(s2(m) == 2, j = valuation(m, 2); i = logint(m, 2); if(i >= j + 2, return(4)));
  0;
}
ok("a(n) mod 8 = 2 if n-1 = 2^k, 4 if n-1 = 2^i + 2^j with i >= j+2, else 0 (1 < n < 129)", prod(n = 2, 128, c(A, n) % 8 == r536(n)));
ok("the residue-4 indices begin 6, 10, 11, 18, 19, 21, 34", select(n -> r536(n) == 4, [2 .. 34]) == [6, 10, 11, 18, 19, 21, 34]);

\\ ===========================================================================
print("== A389537: Discussion (signs; A == x + x^2 mod 2)");
N = 300;
\\ A(A(x) - x) = A(x)^2: in degree n the left side is a(n) plus terms in a(1..n-1).
A = fixpt((A, P) -> A + A^2 - subst(A, x, A - x), x + x^2 + O(x^3), 2, N);
ok("A389537: defining equation holds", vanish(subst(A, x, A - x) - A^2, N)); oeis("A389537", OEIS_A389537, n -> c(A, n));
ok(Str("A == x + x^2 mod 2 (n < ", N, ")"), congruent(A, x + x^2, 2, N));
{
my(sg = vector(N - 1, n, sign(c(A, n))), runs = [], st = 8);
for(n = 9, N - 1, if(sg[n] != sg[n - 1], runs = concat(runs, n - st); st = n));
ok(Str("entry's observation: for n > 7 the signs come in runs of length 9 or 10 (", #runs, " complete runs, n < ", N, ")"), prod(n = 8, N - 1, sg[n] != 0) && prod(i = 1, #runs, runs[i] == 9 || runs[i] == 10));
info(Str("run lengths from n = 8: ", runs));
}

\\ ===========================================================================
print("== A389542: Discussion (modulo 8)");
N = 130;
e542(A, P) = subst(A, x, A^2 - x^2) - 4*A^3;
A = solvecoef(e542, x, 2, N, 1);
ok("A389542: integral solution of the defining equation", isintpoly(A) && holds(e542, A, N, 1)); oeis("A389542", OEIS_A389542, n -> c(A, n));
{
r542(n) = my(m = n - 1);
  if(m == 1 || m == 2, return(2));
  if(ispow2(m), return(6));
  if(m % 2 == 0 && s2(m) == 2, return(4));
  0;
}
ok("a(n) mod 8 = 2 if n-1 in {1,2}, 6 if n-1 = 2^k (k >= 2), 4 if n-1 = 2^j + 2^k (1 <= j < k), else 0 (2 <= n < 130)", prod(n = 2, N - 1, c(A, n) % 8 == r542(n)));

\\ ===========================================================================
print("== A392210: Discussion (even-indexed terms; identities of the same shape)");
N = 200;
A = fixpt((A, P) -> x + subst(A, x, x/(1 - x))^2, x + O(x^2), 1, N);
ok("A392210: A = x + A(x/(1-x))^2 holds", vanish(A - x - subst(A, x, x/(1 - x))^2, N)); oeis("A392210", OEIS_A392210, n -> c(A, n));
ok(Str("A == x + A(x^2/(1-x^2)) mod 2 (n < ", N, ")"), congruent(A, x + subst(A, x, x^2/(1 - x^2)), 2, N));
ok("a(2m) == sum_{k=1}^m binomial(m-1,k-1) a(k) mod 2 for 2m < 130", prod(m = 1, 64, (c(A, 2*m) - sum(k = 1, m, binomial(m - 1, k - 1) * c(A, k))) % 2 == 0));
info(Str("the same parity rule also holds for 2m < ", N, ": ", prod(m = 1, (N - 1) \ 2, (c(A, 2*m) - sum(k = 1, m, binomial(m - 1, k - 1) * c(A, k))) % 2 == 0)));
setrand(392210);
{
my(good = 1, g, NG = 100, Ag = A + O(x^NG));
for(t = 1, 5, g = 1 + rser(1, NG, 5) + O(x^NG);
  if(!vanish(subst(Ag, x, x/g) - x/g - subst(Ag, x, x/(g - x))^2, NG), good = 0));
ok("A(x/g) = x/g + A(x/(g-x))^2 for 5 random integer series g with g(0) = 1 (degree < 100)", good);
good = 1;
for(n = -3, 6, g = 1 - n*x;
  if(!vanish(subst(Ag, x, x/g) - x/g - subst(Ag, x, x/(g - x))^2, NG), good = 0));
ok("entry formula (5), A(x/(1-nx)) = x/(1-nx) + A(x/(1-(n+1)x))^2, for -3 <= n <= 6 (degree < 100)", good);
}

\\ ===========================================================================
print("== A393172: Discussion (modulo 8)");
N = 200;
C = (1 - sqrt(1 - 4*x + O(x^(N + 1)))) / 2 + O(x^N);
e172(A, P) = subst(A, x, x - x^2) - x - A^2;
A72p = solvecoef(e172, x, 2, N, 0); A72 = A72p + O(x^N);
ok("A393172: defining equation holds", holds(e172, A72p, N, 0)); oeis("A393172", OEIS_A393172, n -> c(A72, n));
\\ n = 2^k (4^j + 1) with j >= 1, k >= 0
is4j1(n) = my(m = n >> valuation(n, 2)); m > 1 && issquare(m - 1) && ispow2(m - 1) && valuation(m - 1, 2) >= 2;
r172(n) = if(ispow2(n), 2, if(is4j1(n), 4, 0));
ok(Str("a(n) mod 8 = 2 if n = 2^k, 4 if n = 2^k (4^j+1) with j >= 1, else 0 (1 < n < ", N, ")"), prod(n = 2, N - 1, c(A72, n) % 8 == r172(n)));
ok("the residue-4 indices begin 5, 10, 17, 20, 34, 40, 65, 68, 80", select(n -> r172(n) == 4, [2 .. 80]) == [5, 10, 17, 20, 34, 40, 65, 68, 80]);
info("the consequence for A393171 modulo 16 is checked in the next section");

\\ ===========================================================================
print("== A393171: Discussion (squaring gains a power of 2; B modulo 16)");
B = fixpt((B, P) -> x + subst(B, x, C + O(x^P))^2, x + O(x^2), 1, N);
ok("A393171: B = x + B(C)^2 holds", vanish(B - x - subst(B, x, C)^2, N)); oeis("A393171", OEIS_A393171, n -> c(B, n));
setrand(393171);
{
my(good = 1, D, K, A2);
for(t = 1, 5, for(k = 1, 4,
  D = rser(0, 60, 50); K = rser(0, 60, 50); A2 = (D + 2^k*K)^2;
  if(!congruent(A2, D^2, 2^(k + 1), 121), good = 0)));
ok("A = D + 2^k K implies A^2 == D^2 mod 2^(k+1): 5 random D, K and k <= 4", good);
}
ok(Str("B == x + (A393172 reduced mod 8)^2 mod 16 (n < ", N, ")"), congruent(B, x + Ser(coefs(A72, N) % 8, x)^2, 16, N));
D8 = x + sum(n = 2, N - 1, r172(n) * x^n) + O(x^N);
ok(Str("the conjectured mod-8 rule for A393172 gives B mod 16: B == x + D^2 mod 16 (n < ", N, ")"), congruent(B, x + D8^2, 16, N));

\\ ===========================================================================
\\ A(x - x A(qx)/q) = x.  A(qx)/q is the integral series sum_k a_k q^(k-1) x^k.
\\ The construction uses only ring operations, so running it over Z/MZ gives
\\ the reductions of the integer terms.
sc(A, q, P) = sum(k = 1, P - 1, c(A, k) * q^(k - 1) * x^k) + O(x^P);
scaled(q, N, M) = my(one = if(M, Mod(1, M), 1)); fixpt((A, P) -> A + one*x - subst(A, x, x - x*sc(A, q, P)), one*x + O(x^2), 1, N);
cat(n) = binomial(2*n - 2, n - 1) / n;
NQ = 300;
{
qcheck(q, NM) =
  my(M = q*(q + 1), Am = scaled(q, NM, M), Ae = scaled(q, 16, 0));
  ok(Str("q = ", q, ": modular run agrees with the exact series for n < 16"), prod(n = 1, 15, c(Am, n) == Mod(c(Ae, n), M)));
  if(q > 1, ok(Str("q = ", q, ": [x^n] G_q == Catalan C(n-1) = binomial(2n-2,n-1)/n mod q (1 <= n < ", NM, ")"), prod(n = 1, NM - 1, Mod(lift(c(Am, n)), q) == Mod(cat(n), q))));
  ok(Str("q = ", q, ": [x^n] G_q == 1 mod q+1 (1 <= n < ", NM, ")"), prod(n = 1, NM - 1, Mod(lift(c(Am, n)), q + 1) == 1));
  if(q > 1, ok(Str("q = ", q, ": G_q mod q(q+1) = ", M, " is CRT(Catalan mod q, 1 mod q+1) (1 <= n < ", NM, ")"), prod(n = 1, NM - 1, c(Am, n) == chinese(Mod(cat(n), q), Mod(1, q + 1)))));
  if(q % 2 == 0, ok(Str("q = ", q, ": [x^n] G_q odd iff n is a power of 2 (1 <= n < ", NM, ")"), prod(n = 1, NM - 1, (lift(c(Am, n)) % 2 == 1) == ispow2(n))));
  Am;
}
{
q5ex(q, id, a5, r) =
  my(t = eval(Str("OEIS_", id))[2]);
  ok(Str("example q = ", q, ", n = 5: a(5) = ", a5, " and Catalan 14 both leave remainder ", r, " mod ", q), t[5] == a5 && a5 % q == r && cat(5) == 14 && 14 % q == r);
}

\\ ===========================================================================
print("== A393856: Discussion (G_q modulo q; the rest of the family)");
ok(Str("Catalan C(n-1) odd iff n is a power of 2 (1 <= n < ", NQ, ")"), prod(n = 1, NQ - 1, (cat(n) % 2 == 1) == ispow2(n)));
qcheck(4, NQ); G = scaled(4, 16, 0); oeis("A393856", OEIS_A393856, n -> c(G, n));
q5ex(4, "A393856", 8466, 2);
qcheck(2, NQ); qcheck(3, NQ);
\\ The members q = 1, 2, 3 listed in the OEIS.
G1 = scaled(1, 23, 0); G2 = scaled(2, 19, 0); G3 = scaled(3, 17, 0);
oeis("A088714 (= G_1 shifted by one)", OEIS_A088714, n -> c(G1, n + 1));
oeis("A195195 (= G_2)", OEIS_A195195, n -> c(G2, n));
oeis("A195196 (= G_3)", OEIS_A195196, n -> c(G3, n));
{
my(t = OEIS_A195195[2]);
ok("A195195: every published term == 1 mod 3, and odd iff its index is a power of 2", prod(n = 1, #t, t[n] % 3 == 1 && (t[n] % 2 == 1) == ispow2(n)));
}
qcheck(1, NQ);
info("q = 2 and q = 3 above cover A195195 and A195196 for n < 300");
for(q = 8, 12, qcheck(q, 100));

\\ ===========================================================================
print("== A393857: Discussion (q = 5)");
qcheck(5, NQ); G = scaled(5, 16, 0); oeis("A393857", OEIS_A393857, n -> c(G, n)); q5ex(5, "A393857", 26869, 4);
info("the family members q = 1, 2, 3 and q = 8..12 are checked in the A393856 section");

\\ ===========================================================================
print("== A393858: Discussion (q = 6)");
qcheck(6, NQ); G = scaled(6, 16, 0); oeis("A393858", OEIS_A393858, n -> c(G, n)); q5ex(6, "A393858", 71744, 2);
info("the family members q = 1, 2, 3 and q = 8..12 are checked in the A393856 section");

\\ ===========================================================================
print("== A393859: Discussion (q = 7)");
qcheck(7, NQ); G = scaled(7, 16, 0); oeis("A393859", OEIS_A393859, n -> c(G, n)); q5ex(7, "A393859", 167937, 0);
info("the family members q = 1, 2, 3 and q = 8..12 are checked in the A393856 section");

\\ ===========================================================================
print("== A396093: Discussion (other iterates; modulo 4)");
N = 600;
Bx = x/(1 - x)^2 + O(x^N); B2 = subst(Bx, x, Bx); B3 = subst(Bx, x, B2); B4 = subst(Bx, x, B3);
oeis("A396093", OEIS_A396093, n -> c(B3, n));
ok(Str("B == x/(1+x^2) mod 2 (n < ", N, ")"), congruent(Bx, x/(1 + x^2), 2, N));
ok(Str("B(B(x)) == (x+x^5)/(1+x^6) mod 2 (n < ", N, ")"), congruent(B2, (x + x^5)/(1 + x^6), 2, N));
oeis("A030267 (= B(B(x)))", OEIS_A030267, n -> c(B2, n));
ok(Str("[x^n] B(B(x)) odd iff n == 1 or 5 mod 6 (n < ", N, ", and all published terms of A030267)"), prod(n = 0, N - 1, (c(B2, n) % 2 == 1) == (n % 6 == 1 || n % 6 == 5)) && prod(i = 1, #OEIS_A030267[2], (OEIS_A030267[2][i] % 2 == 1) == (i % 6 == 1 || i % 6 == 5)));
perclaim("B(B(B(B(x))))", coefs(B4, N), 2, 34, 0, N);
perclaim("A396093", coefs(B3, N), 4, 20, 1, N);

\\ ===========================================================================
\\ Solution of F = x + F^r * F^s over Z/MZ (or Z if M = 0); F^k = k-th iterate.
{
gstep(F, r, s, one) =
  my(its = vector(max(r, s)));
  its[1] = F; for(k = 2, #its, its[k] = subst(F, x, its[k - 1]));
  one*x + its[r]*its[s];
}
gensol(r, s, N, M) = my(one = if(M, Mod(1, M), 1)); fixpt((F, P) -> gstep(F, r, s, one), one*x + O(x^2), 1, N);
N = 130;
Fr = vector(5, r, gensol(r, r + 1, N, 4*r));
{
print("== A396099: Discussion (all coefficients odd; modulo 4r; the equation F = x + F^r F^s)");
my(good = 1, F);
for(r = 1, 8, F = if(r <= 5, Fr[r], gensol(r, r + 1, N, 2*r)); if(!prod(n = 1, N - 1, lift(c(F, n)) % 2 == 1), good = 0));
ok(Str("every coefficient of F_r is odd, r = 1..8 (n < ", N, ")"), good);
}
idr = [[2, "A396099"], [4, "A396798"], [5, "A396807"]];
ok("the runs modulo 4r agree with the published terms (r = 2, 4, 5)", prod(i = 1, #idr, my(r = idr[i][1], t = eval(Str("OEIS_", idr[i][2]))[2]); prod(n = 1, #t, c(Fr[r], n) == Mod(t[n], 4*r))));
perclaim("F_1 (r = 1)", coefs(Fr[1], N), 4, 3, 1, N);
perclaim("A396099 (r = 2)", coefs(Fr[2], N), 8, 4, 4, N);
{
my(pairs = [], good = 1, m, F, G, NG = 50);
for(r = 1, 7, for(s = 1, 8, m = gcd(r + s - 1, r*s); if(m > 1, pairs = concat(pairs, [[r, s, m]]))));
ok("pairs r <= 7, s <= 8 with m = gcd(r+s-1, rs) > 1: there are 38", #pairs == 38);
foreach(pairs, p,
  r = p[1]; s = p[2]; m = p[3]; F = gensol(r, s, NG, m);
  for(k = -3, 6, G = iter(F, k, NG); if(!congruent(lift(G), x/(1 - k*x), m, NG), good = 0; print("  fails for r=", r, " s=", s, " k=", k))));
ok("F = x + F^r F^s: every iterate F^k == x/(1-kx) mod gcd(r+s-1, rs), 38 pairs, -3 <= k <= 6, n < 50", good);
good = 1;
for(r = 1, 8, F = gensol(r, r + 1, 60, 2*r); G = x + O(x^60);
  for(k = 1, 2*r, G = subst(F, x, G); if(vanish(G - x, 60) != (k == 2*r), good = 0)));
ok("F_r has order exactly 2r under composition modulo 2r, r = 1..8 (n < 60)", good);
}

\\ ===========================================================================
print("== The member r = 3 of the family (Discussion of A396099, A396798, A396807)");
perclaim("F_3 (r = 3)", coefs(Fr[3], N), 12, 6, 1, N);

\\ ===========================================================================
print("== A396798: Discussion (r = 4)");
perclaim("A396798 (r = 4)", coefs(Fr[4], N), 16, 8, 2, N);
info("the claims shared with A396099 (odd coefficients, F = x + F^r F^s, order 2r) are checked in that section");

\\ ===========================================================================
print("== A396807: Discussion (r = 5)");
perclaim("A396807 (r = 5)", coefs(Fr[5], N), 20, 3, 1, N);
info("the claims shared with A396099 (odd coefficients, F = x + F^r F^s, order 2r) are checked in that section");

\\ ===========================================================================
print("== A396102: Discussion (signs; A140094 and A067145; iterates of x/(1-x))");
N = 60;
fam(r) = (A, P) -> iter(A, r, P) - (1 + x)*iter(A, r - 1, P);
A = solvecoef(fam(3), x, 2, N, 0);
ok("A396102: integral solution of F^3 = (1+x) F^2", isintpoly(A) && holds(fam(3), A, N, 0)); oeis("A396102", OEIS_A396102, n -> c(A, n));
ok(Str("the terms alternate in sign from n = 2 on (2 <= n < ", N, ")"), prod(n = 2, N - 2, c(A, n) * c(A, n + 1) < 0));
\\ A140094: S = x/(1 - S^3), computed from its own definition.
S140 = fixpt((S, P) -> x/(1 - iter(S, 3, P)), x + O(x^2), 1, N);
R = serreverse(A + O(x^N)); S = -subst(R, x, -x);
ok(Str("S(x) = -R(-x), R the inverse of A396102, satisfies S = x + S S^3 and S = x/(1 - S^3) (n < ", N, ")"), vanish(S - x - S*iter(S, 3, N), N) && vanish(S - x/(1 - iter(S, 3, N)), N));
ok(Str("S equals the series defined by A140094 (n < ", N, ")"), vanish(S - S140, N));
oeis("A140094", OEIS_A140094, n -> c(S140, n));
ok("A140094: the entry prints 23 terms and every one is == 1 mod 3", #OEIS_A140094[2] == 23 && prod(i = 1, 23, OEIS_A140094[2][i] % 3 == 1));
ok(Str("S == x/(1-x) mod 3 (n < ", N, ")"), congruent(S, x/(1 - x), 3, N));
ok("for r = 2..8, the solution of S = x/(1 - S^r) is == x/(1-x) mod r (n < 60)", prod(r = 2, 8, congruent(lift(fixpt((S, P) -> Mod(1, r)*x/(1 - iter(S, r, P)), Mod(1, r)*x + O(x^2), 1, N)), x/(1 - x), r, N)));
\\ A067145: F(F(x)) = (1+x) F(x) is the family equation with r = 2.
F2 = solvecoef(fam(2), x, 2, 40, 0); F2s = F2 + O(x^40);
ok("A067145: F_2 is integral and F(F(x)) = (1+x) F(x)", isintpoly(F2) && holds(fam(2), F2, 40, 0));
oeis("A067145 (= F_2)", OEIS_A067145, n -> c(F2s, n));
ok("A067145 shifts left under reversion: INV(F) = F/x - 1 (n < 39)", vanish(serreverse(F2s) - (F2s/x - 1), 39));
ok("A067145: the entry prints 23 terms and every one is odd; F_2 is odd for n < 40", #OEIS_A067145[2] == 23 && prod(i = 1, 23, OEIS_A067145[2][i] % 2 != 0) && prod(n = 1, 39, c(F2s, n) % 2 != 0));
{
my(good = 1, M1 = x/(1 - x), G = x);
for(k = 1, 10, G = subst(M1, x, G); if(G != x/(1 - k*x), good = 0));
G = x; for(k = 1, 5, G = subst(x/(1 + x), x, G); if(G != x/(1 + k*x), good = 0));
ok("iterates of x/(1-x): M_1^k = x/(1-kx) for -5 <= k <= 10, so M_1^r == x mod r", good);
}

\\ ===========================================================================
\\ Hanna's construction from the OEIS entries: A = (1 - sqrt(1 - 4m B(x^2)/x))/(2m),
\\ where B is the compositional inverse of the previous A.
{
hanna(m, N) =
  my(A = x + O(x^N), B);
  for(i = 1, 2 + logint(N, 2), B = serreverse(A); A = (1 - sqrt(1 - 4*m*subst(B, x, x^2)/x + O(x^N))) / (2*m));
  A;
}
heq(A, m, N) = vanish(subst(A, x, x*A - m*x*A^2) - x^2, N + 1);
N = 260;
Hm = vector(5, m, hanna(m, N));
print("== A396843: Discussion (modulo m^3; the members m = 1, 2, 5)");
ok(Str("the series for m = 1..5 satisfy A(xA - mxA^2) = x^2 (n < ", N, ")"), prod(m = 1, 5, heq(Hm[m], m, N)));
oeis("A396843", OEIS_A396843, n -> c(Hm[3], n));
{
my(good = 1, A);
for(m = 3, 4, for(n = 1, N - 1, if(c(Hm[m], n) % m^3 && s2(n - 1) > 2, good = 0)));
for(m = 2, 12, A = hanna(m, 70); for(n = 1, 69, if(c(A, n) % m^3 && s2(n - 1) > 2, good = 0)));
ok("mod m^3 the nonzero residues occur only at n = 1, 2^i+1, 2^i+2^j+1 (m = 3, 4: n < 260; m = 2..12: n < 70)", good);
}
oeis("A265940 (m = 1)", OEIS_A265940, n -> c(Hm[1], n));
ok(Str("m = 1: every coefficient is odd (n < ", N, ", and all published terms)"), prod(n = 1, N - 1, c(Hm[1], n) % 2 == 1) && prod(i = 1, #OEIS_A265940[2], OEIS_A265940[2][i] % 2 == 1));
oeis("A271958 (m = 2)", OEIS_A271958, n -> c(Hm[2], n));
ok(Str("m = 2: a(n) == +-2 mod 4 for n = 2^j+1, == 0 mod 4 for the other n >= 2 (n < ", N, ", and all published terms)"), prod(n = 2, N - 1, if(ispow2(n - 1), c(Hm[2], n) % 4 == 2, c(Hm[2], n) % 4 == 0)) && prod(n = 2, #OEIS_A271958[2], if(ispow2(n - 1), OEIS_A271958[2][n] % 4 == 2, OEIS_A271958[2][n] % 4 == 0)));
oeis("A396845 (m = 5)", OEIS_A396845, n -> c(Hm[5], n));
r845(n) = my(e = valuation(n - 1, 2)); if(ispow2(n - 1), if(e % 2 == 0, 5, 20), 0);
ok(Str("m = 5: a(n) mod 25 is 5 at n = 4^k+1, 20 at n = 2*4^k+1, 0 elsewhere (2 <= n < ", N, ", and all published terms)"), prod(n = 2, N - 1, c(Hm[5], n) % 25 == r845(n)) && prod(n = 2, #OEIS_A396845[2], OEIS_A396845[2][n] % 25 == r845(n)));

\\ ===========================================================================
print("== A396844: Discussion (where the conjecture fails)");
oeis("A396844", OEIS_A396844, n -> c(Hm[4], n));
is24k1(n) = my(m = n - 1); m >= 2 && ispow2(m) && valuation(m, 2) % 2 == 1;
{
my(fails = select(n -> c(Hm[4], n) % 16 != if(is24k1(n), 12, 0), [9 .. N - 1]));
ok(Str("the literal conjecture (n > 8) fails exactly at n = 17, 65, 257 for n < ", N, " (first 17, next 65; none for 8 < n < 17)"), fails == [17, 65, 257]);
}
info("the claims shared with A396843 (modulo m^3; m = 1, 2, 5) are checked in that section");

\\ ===========================================================================
print("== A397588: Discussion (higher powers of 3)");
N = 300;
A = x + O(x^N); for(i = 1, N, A = x + deriv(x*A^2));
ok("A397588: A = x + (x A^2)' holds", vanish(A - x - deriv(x*A^2), N - 1)); oeis("A397588", OEIS_A397588, n -> c(A, n));
A2 = A^2;
sn(n) = c(A2, n);
ok(Str("a(n) = (n+1) s(n) with s(n) = sum_k a(k) a(n-k), so n+1 divides a(n) (2 <= n < ", N - 1, ")"), prod(n = 2, N - 2, c(A, n) == (n + 1)*sn(n) && c(A, n) % (n + 1) == 0));
ok(Str("s(n) = 2 a(n-1) + sum_{k=2}^{n-2} a(k) a(n-k) (3 <= n < ", N - 1, ")"), prod(n = 3, N - 2, sn(n) == 2*c(A, n - 1) + sum(k = 2, n - 2, c(A, k)*c(A, n - k))));
ok("a(5) = 4284 = 9*476", c(A, 5) == 4284 && 4284 == 9*476);
ok(Str("9 divides a(n) for 5 <= n < ", N - 1), prod(n = 5, N - 2, c(A, n) % 9 == 0));
ok(Str("3^12 divides a(n) for 35 <= n < ", N - 1), prod(n = 35, N - 2, c(A, n) % 3^12 == 0));
{
my(st = vector(12, e, my(n0 = N - 2); while(n0 > 1 && c(A, n0 - 1) % 3^e == 0, n0--); n0));
info(Str("smallest n0 with 3^e | a(n) for all n0 <= n < ", N - 1, ", e = 1..12: ", st));
}

\\ ===========================================================================
\\ ===========================================================================
print("== A355872: Discussion (modulo 32 and 64)");
{
bil2(M, N) =
  my(one = Mod(1, M), A = O(x^N), R, J = sqrtint(N) + 1);
  for(it = 1, N,
    R = one*x + O(x^N);
    for(j = -J, J, if(j != 0 && j^2 < N, R -= (-x)^(j^2) * A^((j - 1)^2)));
    A = R);
  A;
}
A32 = bil2(32, 4*200); A64 = bil2(64, 4*200);
ok("A355872: a(n) mod 32 repeats 2,14,18,30 from n = 1 (n < 200)", prod(n = 1, 199, lift(c(A32, 4*n - 3)) == [2, 14, 18, 30][(n - 1) % 4 + 1]));
ok("A355872: a(n) mod 64 repeats 2,14,50,62 from n = 1 (n < 200)", prod(n = 1, 199, lift(c(A64, 4*n - 3)) == [2, 14, 50, 62][(n - 1) % 4 + 1]));

\\ ===========================================================================
print("== A394576: Discussion (the skipped numbers; the blocks)");
{
greedy2(M) =
  my(a = vector(M), forb = vector(4*M + 10), t);
  a[1] = 1;
  for(n = 1, M - 1,
    t = a[n] + 1; while(forb[t], t++);
    a[n + 1] = t;
    if(n >= 2, forb[a[n - 1] + a[n] + a[n + 1]] = 1));
  a;
}
M = 30000; g = greedy2(M); bs = vector(M - 2, k, g[k] + g[k + 1] + g[k + 2]);
ok("A394576: the first sums b(k) are 6, 9, 12, 16, 20", bs[1..5] == [6, 9, 12, 16, 20]);
ok("A394576: b(k) lies in {4k, 4k+1, 4k+2} (k <= 9998)", prod(k = 1, (M - 3)\3, bs[k] >= 4*k && bs[k] <= 4*k + 2));
Tg = Set(g); Tb = Set(bs);
ok("A394576: the terms and the b(k) partition {1, ..., a(30000)}", #setintersect(Tg, Tb) == 0 && prod(m = 1, g[M], setsearch(Tg, m) || setsearch(Tb, m)));
{
my(good = 1, s, d);
for(k = 1, (M - 3)\3,
  s = bs[k] - 4*k;
  d = vector(3, r, (4*(3*k + r) - 1)\3 - g[3*k + r]);
  if(d != [[0, 0, 0], [1, 0, 0], [1, 1, 0]][s + 1], good = 0));
ok("A394576: U(n) - a(n) on block k is (0,0,0), (1,0,0), (1,1,0) for s = 0, 1, 2 (3k+3 <= 30000)", good);
}

\\ ===========================================================================
print("== A397346: Discussion (modulo 16)");
{
rec7b(N) = my(a = vector(N + 1)); a[1] = 1; a[2] = 1;
  for(n = 2, N, a[n + 1] = 2*n*a[n] + n*sum(k = 1, n - 2, (2*(k + 1)^2 - 1)/(k + 1) * a[k + 2] * a[n - k])); a;
}
r = rec7b(200);
ok("A397346: a(n) mod 16 repeats 4,2,8,10,12,2,0,2 from n = 2 (n < 200)", prod(n = 2, 199, r[n + 1] % 16 == [4, 2, 8, 10, 12, 2, 0, 2][(n - 2) % 8 + 1]));
ok("A397346: a(n)/n mod 16 repeats 2,6,2,2,10,14,2,2 from n = 2 (n < 200)", prod(n = 2, 199, (r[n + 1]/n) % 16 == [2, 6, 2, 2, 10, 14, 2, 2][(n - 2) % 8 + 1]));

print("");
printf("RESULT: %d checks passed, %d failed\n", NPASS, NFAIL);
quit(NFAIL > 0);
