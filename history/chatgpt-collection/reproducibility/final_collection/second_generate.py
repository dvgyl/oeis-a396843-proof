#!/usr/bin/env python3
"""Create independent per-entry presentations of the preserved round-two proofs."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[2]
OLD = (ROOT / 'manuscript/further_oeis_proofs.tex').read_text()
MANIFEST = json.loads((ROOT / 'validation/final_theorems.json').read_text())['endpoint_groups']

PREAMBLE = r'''\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage[margin=26mm]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage{enumitem}
\usepackage[hidelinks]{hyperref}
\setlength{\parskip}{3pt}
\setlength{\emergencystretch}{3em}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newcommand{\Z}{\mathbb Z}
\newcommand{\N}{\mathbb N}
\newcommand{\Q}{\mathbb Q}
\newcommand{\F}{\mathbb F}
\newcommand{\ps}[1]{#1[[x]]}
'''

DISCLOSURE = r'''\begin{center}
\fbox{\begin{minipage}{0.91\linewidth}\small
\textbf{AI contribution and review status.}
ChatGPT (OpenAI) generated the mathematical exposition, proof development,
Lean interfaces, and checks for this collection in response to Dev Goyal's
prompts. Dev Goyal is the sole human author. Independent human review is
pending. Original sequence authors, known mathematical results, and adapted
upstream code retain their separate credits. This document makes no claim
of publication, OEIS acceptance, or worldwide priority.
\end{minipage}}
\end{center}
'''

COMMON_FORMAL = r'''
The companion is a separate, explicitly typed Lean entry file. Its proofs
invoke the preserved implementation modules; the complete dependency source
is included in the same archive. Shared lemmas are reused rather than
assumed. The entry file is not a self-contained replacement for Mathlib or
the supplied common library.

The project pins Lean 4.19.0 and Mathlib revision
\begin{center}\small\ttfamily
c44e0c8ee63ca166450922a373c7409c5d26b00b.
\end{center}
The collection checker recompiles the proof sources and audits the
theorems' transitive axiom dependencies. Only \texttt{propext},
\texttt{Classical.choice}, and \texttt{Quot.sound} are permitted.
The delivered verification reports record the actual successful runs.
Finite numerical checks are corroboration; the displayed conclusions are
unbounded theorems. An AI review of source correspondence does not replace
independent human review.
'''

def between(start, end):
    return OLD[OLD.index(start):OLD.index(end)]

def render_doc(oid, title, abstract, body, names, modules, qualification, stirling=False):
    formal = '\\section{Lean proof and exact scope}\n'
    formal += 'The dedicated entry file is \\path{lean/Entries/'+oid+'.lean}. '
    formal += 'Its declarations lie in namespace \\texttt{FinalCollection.'+oid+'}. '
    formal += 'The principal checked endpoints are:\n\\begin{itemize}[nosep]\n'
    for name, meaning in names:
        formal += '\\item \\texttt{'+name.replace('_',r'\_')+'}: '+meaning+'\n'
    formal += '\\end{itemize}\nThe full implementations are in '
    formal += ', '.join('\\path{lean/'+m.replace('.','/')+'.lean}' for m in modules)+'.\n'
    formal += qualification + '\n' + COMMON_FORMAL
    bib = r'''\begin{thebibliography}{9}
\raggedright
\bibitem{oeis} OEIS Foundation, entry '''+oid+r''',
\url{https://oeis.org/'''+oid+r'''}. Source checked 24 October 2026.
'''
    if not stirling:
        bib += 'The source sequence and selected conjectures are credited to Paul D. Hanna.\n'
    if stirling:
        bib += r'''\bibitem{danesh} P. Danesh, \emph{Eventual periodicity of weighted
Stirling transforms and two conjectures of Bala}, version 1,
26 August 2026, Theorem 4.1 and Corollary 4.2.
\url{https://doi.org/10.33774/coe-2026-4d6jr}.
\bibitem{schreyer} B. Schreyer, \emph{Rigged Horse Numbers and their
Modular Periodicity}, arXiv:2409.03799v2, 3 December 2024.
\url{https://arxiv.org/abs/2409.03799}.
\bibitem{mathlib} Mathlib contributors. The adapted Stirling source is
\texttt{Mathlib.Combinatorics.Enumerative.Stirling} at revision
\path{4ed598f443601d8b5abccc2a14e3ba408ae47056}, copyright 2025 Beibei Xiong;
authors Beibei Xiong, Yu Shao, Weijie Jiang, and Zhengfeng Yang.
Apache-2.0 attribution and license are preserved in
\path{third_party/mathlib/NOTICE.md} and the accompanying license file.
'''
    bib += r'''\bibitem{repo} D. Goyal, supplied reference repository,
\url{https://github.com/dvgyl/oeis-a396843-proof}.
This separate presentation belongs to the final collected proof package;
no earlier DOI is reassigned to it.
\end{thebibliography}
\end{document}
'''
    # References retained from the original extracted mathematical sections.
    body = re.sub(r'\\cite\{oeis(?:093|474|475|102)\}',r'\\cite{oeis}',body)
    tex = PREAMBLE + '\\hypersetup{pdftitle={'+oid+': '+title+'},pdfauthor={Dev Goyal}}\n'
    tex += '\\title{'+oid+'\\\\[3pt]'+title+'}\n\\author{Dev Goyal}\n\\date{24 October 2026}\n\\begin{document}\n\\maketitle\n'
    tex += DISCLOSURE + '\\begin{abstract}\n'+abstract+'\n\\end{abstract}\n'
    tex += body + formal + bib
    (ROOT/'manuscripts'/f'{oid}.tex').write_text(tex)

def lean_header(oid, modules):
    opens = '' if modules == ['More.StirlingPeriodicity'] else 'open PowerSeries Hanna.Series\n'
    return '\n'.join('import '+m for m in modules)+f'''\n
/-!
# {oid}: separate formal entry in the final collection

AI disclosure: ChatGPT (OpenAI) generated this explicitly typed presentation
for Dev Goyal. Independent human review is pending. Complete mathematical
implementations are preserved in the imported modules. Source and historical
scope are documented in manuscripts/{oid}.tex.
-/

namespace FinalCollection.{oid}

{opens}

noncomputable section

'''

CATALOGUE=[]
def save_entry(oid,title,status,abstract,body,names,modules,qualification,code,original,summary,stirling=False):
    text=lean_header(oid,modules)+code+f'\nend\nend FinalCollection.{oid}\n'
    (ROOT/'lean/Entries'/f'{oid}.lean').write_text(text)
    render_doc(oid,title,abstract,body,names,modules,qualification,stirling)
    new=['FinalCollection.'+oid+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)]
    CATALOGUE.append(dict(oeis_id=oid,title=title,status=status,source_url='https://oeis.org/'+oid,
        manuscript_tex=f'manuscripts/{oid}.tex',manuscript_pdf=f'manuscripts/{oid}.pdf',
        lean_file=f'lean/Entries/{oid}.lean',imported_modules=modules,original_endpoints=original,
        new_endpoints=new,summary=summary,qualifications=qualification.replace('\\','')))

code093=r'''abbrev B : PowerSeries ℤ := RationalParity.B
abbrev A : PowerSeries ℤ := RationalParity.A
def a (n : ℕ) : ℤ := coeff ℤ n A

theorem source_denominator : B * (1-X)^2 = X :=
  RationalParity.B_denominator

theorem source_composition : A = compose B (compose B B) :=
  RationalParity.A_definition

theorem coefficient_definition (n : ℕ) : a n = coeff ℤ n A := rfl

theorem reduced_denominator :
    (RationalParity.A : PowerSeries (ZMod 2)) * (1+X^10) = X+X^3+X^7+X^9 :=
  RationalParity.third_period_denominator

theorem complete_parity (n : ℕ) :
    (a n : ZMod 2) =
      if n%10=1 ∨ n%10=3 ∨ n%10=7 ∨ n%10=9 then 1 else 0 :=
  RationalParity.a396093_residue n

theorem even_iff (n : ℕ) :
    Even (a n) ↔ ¬(n%10=1 ∨ n%10=3 ∨ n%10=7 ∨ n%10=9) :=
  RationalParity.a396093_even_iff n

theorem even_indices (n : ℕ) : Even (a (2*n)) :=
  RationalParity.a396093_even_indices n

theorem odd_indices (n : ℕ) (hn : 1 ≤ n) :
    Even (a (2*n-1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5*k-2 :=
  RationalParity.a396093_odd_indices_original n hn
'''
body093=between(r'\section{A396093:',r'\section{The two cubic series:')
save_entry('A396093','A complete parity classification','proved_source_conjectures',
    r'The third compositional iterate of $x/(1-x)^2$ has odd coefficients exactly at indices congruent to $1,3,7,9$ modulo ten. We prove this full classification and both parity assertions recorded in the source entry. The proof reduces an actual integral rational composition to a characteristic-two denominator identity.',
    body093,[('source_denominator','the literal rational denominator identity.'),('source_composition','the threefold composition defining the sequence.'),('reduced_denominator','the characteristic-two period identity.'),('complete_parity','the all-index residue classification.'),('even_iff','the equivalent integer-evenness characterization.'),('even_indices','the first source assertion, including index zero.'),('odd_indices','the exact positive-index source formulation.')],
    ['More.RationalParity'],r'The source offset is zero. The coefficient statement concerns the actual third iterate, not a separately postulated periodic sequence. The two source assertions were labeled conjectures in the retrieved entry; the full result here includes every $n\ge0$.',
    code093,MANIFEST['a396093_rational_parity'],'For every n≥0, a(n) mod2 is1 exactly when n mod10 is1,3,7,9. In particular a(2n) is even; for n≥1, a(2n−1) is even iff n=5k−2 for some k≥1.')

canonical=between(r'\subsection{A canonical integral family}',r'\subsection{A389474 and a square-zero substitution}')
canonical=canonical.replace(r'\subsection{A canonical integral family}',r'\section{Integral construction and uniqueness}')
frobenius=r'''\section{The standard Frobenius identity}
For any integer formal series $W$ and prime $p$, coefficient reduction gives
\[
\overline W(x)^p=\overline W(x^p)\qquad\text{in }\F_p[[x]].
\]
For each fixed coefficient one may truncate $W$ at that degree. The
polynomial identity $(u+v)^p=u^p+v^p$ in characteristic $p$, together
with $a^p=a$ in $\F_p$, proves the displayed identity coefficient by
coefficient. Thus it holds for every formal series, without a convergence
assumption. This is standard algebra; its application below is not a new
general principle.
'''

code474=r'''abbrev A : PowerSeries ℤ := More.CubicReversion.a389474

theorem normalized : coeff ℤ 0 A = 0 ∧ coeff ℤ 1 A = 1 :=
  More.CubicReversion.a389474_normalized

theorem source_equation : compose A (X^2+2*X^3+2*A^2) = 3*A^2 :=
  More.CubicReversion.a389474_equation

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (X^2+2*X^3+2*U^2) = 3*U^2) : U = A :=
  More.CubicReversion.a389474_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (X^2+2*X^3+2*U^2) = 3*U^2 :=
  More.CubicReversion.a389474_existence_uniqueness

theorem integral_family_existence (s : ℤ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2+2*C ℤ s*U^3 :=
  More.CubicReversion.existence_uniqueness s

theorem square_mod_nine :
    PowerSeries.map (Int.castRingHom (ZMod 9)) (A^2) = X^2+2*X^3 :=
  More.CubicReversion.a389474_square_mod_nine

theorem square_coefficients (n : ℕ) (hn : 3 < n) :
    (coeff ℤ n (A^2) : ZMod 9) = 0 :=
  More.CubicReversion.a389474_conjecture_3 n hn

theorem power_coefficients (n k : ℕ) :
    (coeff ℤ n (A^(3*k)-(compose A (X^3))^k) : ZMod 3) = 0 :=
  More.CubicReversion.a389474_conjecture_4 n k
'''
body474=r'''\section{Source and conclusions}
Let $U=x+O(x^2)\in\Z[[x]]$ be specified by
\[
U\bigl(x^2+2x^3+2U(x)^2\bigr)=3U(x)^2.
\]
This is the A389474 source equation \cite{oeis}, with offset one.
We first construct its unique integral solution. We then prove
$U^2\equiv x^2+2x^3\pmod9$ and, for every $k\ge0$,
$U^{3k}\equiv U(x^3)^k\pmod3$. Powers without the composition symbol
mean ordinary multiplication.
'''+canonical+between(r'\subsection{A389474 and a square-zero substitution}',r'\subsection{Frobenius and A389475}').replace(r'\subsection{A389474 and a square-zero substitution}',r'\section{The source bridge and the modulus-nine proof}')+frobenius+r'''
Apply the identity at $p=3$ to $W=U$ and raise both sides to the
ordinary $k$th power. For every $n,k\ge0$ this yields
\[
[x^n]\bigl(U(x)^{3k}-U(x^3)^k\bigr)\equiv0\pmod3.
\]
This proves the second selected source assertion, including the boundary
cases $n=0$ and $k=0$. It requires no special equation for $U$.
'''
save_entry('A389474','Cubic reversion modulo nine and three','proved_source_conjectures',r'We construct the normalized integer solution of the defining equation, prove that its square is $x^2+2x^3$ modulo nine, and formalize the associated cubic-power assertion modulo three. The second assertion is a direct application of the classical Frobenius identity.',body474,
 [('source_equation','the exact source equation.'),('source_existence_uniqueness','existence and uniqueness over the integers.'),('integral_family_existence','the entire integer-parameter auxiliary family.'),('square_mod_nine','the full modulus-nine identity.'),('square_coefficients','the source range $n>3$.'),('power_coefficients',r'the standard Frobenius consequence for all $n,k\ge0$.')],
 ['More.CubicConsequences'],r'The full integral construction, exact division by two, genuine compositional inversion, and both source-uniqueness directions are present in the shared implementation. No division by three is used modulo nine. Normalization and source uniqueness are explicit endpoints in the separate entry file.',code474,
 [n for n in MANIFEST['cubic_reversion'] if 'a389475' not in n],
 'Unique normalized integer source solution. Its square is x²+2x³ modulo9; for all n,k≥0, the coefficient of A(x)^(3k)−A(x³)^k is0 modulo3.')

code475=r'''abbrev A : PowerSeries ℤ := More.CubicReversion.a389475

theorem normalized : coeff ℤ 0 A = 0 ∧ coeff ℤ 1 A = 1 :=
  More.CubicReversion.a389475_normalized

theorem source_equation : compose A (3*X^2) = 2*X^2+A^2-2*A^3 :=
  More.CubicReversion.a389475_equation

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (3*X^2) = 2*X^2+U^2-2*U^3) : U = A :=
  More.CubicReversion.a389475_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2-2*U^3 :=
  More.CubicReversion.a389475_existence_uniqueness

theorem integral_family_existence (s : ℤ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (3*X^2) = 2*X^2+U^2+2*C ℤ s*U^3 :=
  More.CubicReversion.existence_uniqueness s

theorem cube_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (A^3) =
      PowerSeries.map (Int.castRingHom (ZMod 3)) (compose A (X^3)) :=
  More.CubicReversion.a389475_cube_mod_three

theorem square_mod_three :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (A^2) =
      X^2+2*PowerSeries.map (Int.castRingHom (ZMod 3)) (compose A (X^3)) :=
  More.CubicReversion.a389475_square_mod_three

theorem cube_coefficients (n : ℕ) :
    (coeff ℤ n (A^3-compose A (X^3)) : ZMod 3) = 0 :=
  More.CubicReversion.a389475_conjecture_4a n

theorem square_coefficients (n : ℕ) :
    (coeff ℤ n (A^2-X^2-2*compose A (X^3)) : ZMod 3) = 0 :=
  More.CubicReversion.a389475_conjecture_4b n
'''
body475=r'''\section{Source and conclusions}
The A389475 series \cite{oeis} is the normalized integer solution
\[
V(3x^2)=2x^2+V(x)^2-2V(x)^3,\qquad V=x+O(x^2).
\]
The offset is one. We prove the two coefficientwise identities
\[
V(x)^3\equiv V(x^3)\pmod3,\qquad
V(x)^2\equiv x^2+2V(x^3)\pmod3.
\]
The first is standard Frobenius; the second uses this source equation.
'''+canonical+r'''
Taking $s=-1$ in Theorem~\ref{thm:cubicexist} constructs the desired
series $V=R_{-1}$ and proves uniqueness for its literal source equation.
'''+frobenius+r'''
\section{The two modulus-three identities}
\begin{theorem}
For every coefficient index $n\ge0$,
\begin{align*}
[x^n]\bigl(V(x)^3-V(x^3)\bigr)&\equiv0\pmod3,\\
[x^n]\bigl(V(x)^2-x^2-2V(x^3)\bigr)&\equiv0\pmod3.
\end{align*}
\end{theorem}
\begin{proof}
Apply Frobenius with $p=3$ and $W=V$ for the first identity.
For the second reduce the source equation coefficientwise to $\F_3$.
Since $V(0)=0$, its left side reduces to $V(0)=0$. Hence
\[
0=2x^2+V^2-2V^3,\qquad V^2=x^2+2V^3.
\]
Substitute the first identity to obtain $V^2=x^2+2V(x^3)$.
Equality of series gives every stated coefficient congruence.
\end{proof}
This proves the assertions labeled (4.a) and (4.b) in the retrieved
entry. Both hold for the full series, including degree zero.
'''
save_entry('A389475','Two cubic congruences in characteristic three','proved_source_conjectures',r'For the unique normalized integer solution of $V(3x^2)=2x^2+V^2-2V^3$, we prove both recorded modulus-three identities. The construction is integral and unique; the congruence argument is a reduction of the source equation followed by standard Frobenius.',body475,
 [('source_equation','the literal defining equation.'),('source_existence_uniqueness','the integral source construction and uniqueness.'),('integral_family_existence','the integer-parameter family used in the construction.'),('cube_mod_three','the full Frobenius identity.'),('square_mod_three','the full square identity derived from the source.'),('cube_coefficients','the first assertion at every coefficient.'),('square_coefficients','the second assertion at every coefficient.')],
 ['More.CubicConsequences'],r'Every index is universally quantified. The first congruence is a standard identity valid for every integral formal power series; the second is a consequence of this particular source equation. The companion also separately states normalization and source uniqueness.',code475,
 [n for n in MANIFEST['cubic_reversion'] if 'a389474' not in n],
 'Unique normalized integer source solution. A(x)^3≡A(x³) and A(x)^2≡x²+2A(x³) modulo3 as full series.')

code102=r'''open Consecutive

abbrev A : PowerSeries ℤ := InverseIterate.A396102

theorem normalized : Normalized A := InverseIterate.F_normalized 3

theorem source_equation : compose A (compose A A) = (1+X)*compose A A :=
  InverseIterate.a396102_definition

theorem source_unique (U : PowerSeries ℤ) (hU : Normalized U)
    (he : compose U (compose U U) = (1+X)*compose U U) : U = A :=
  InverseIterate.a396102_unique U hU he

theorem source_existence_uniqueness :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      compose U (compose U U) = (1+X)*compose U U := by
  refine ⟨A, ⟨normalized, source_equation⟩, ?_⟩
  intro U hU
  exact source_unique U hU.1 hU.2

theorem coefficient_congruence (n : ℕ) (hn : 1 ≤ n) :
    (coeff ℤ n A : ZMod 3) = 1 :=
  InverseIterate.a396102_congruence n hn

theorem iterate_congruence (k n : ℕ) (hn : 1 ≤ n) :
    (coeff ℤ n (iter A k) : ZMod 3) = (k : ZMod 3)^(n-1) :=
  InverseIterate.iterate_coefficient_congruence 3 k n hn

theorem family_source_existence (r : ℕ) :
    ∃! U : PowerSeries ℤ, Normalized U ∧
      iter U (r+1) = (1+X)*iter U r :=
  InverseIterate.F_original_existence_uniqueness r

theorem family_source_equation (r : ℕ) :
    iter (InverseIterate.F (S:=ℤ) (r+1)) (r+1) =
      (1+X)*iter (InverseIterate.F (r+1)) r :=
  InverseIterate.F_original_equation r

theorem auxiliary_source_equation (r : ℕ) :
    InverseIterate.R (S:=ℤ) r =
      X-InverseIterate.R r*iter (InverseIterate.R r) r :=
  InverseIterate.R_equation r

theorem inverse_right (r : ℕ) :
    compose (InverseIterate.R (S:=ℤ) r) (InverseIterate.F r) = X :=
  InverseIterate.compose_R_F r

theorem inverse_left (r : ℕ) :
    compose (InverseIterate.F (S:=ℤ) r) (InverseIterate.R r) = X :=
  InverseIterate.compose_F_R r

theorem family_coefficient_congruence (r n : ℕ) (hn : 1 ≤ n) :
    (coeff ℤ n (InverseIterate.F r) : ZMod r) = 1 :=
  InverseIterate.coefficient_congruence r n hn

theorem family_iterate_congruence (r k n : ℕ) (hn : 1 ≤ n) :
    (coeff ℤ n (iter (InverseIterate.F r) k) : ZMod r) =
      (k : ZMod r)^(n-1) :=
  InverseIterate.iterate_coefficient_congruence r k n hn
'''
body102=between(r'\section{A396102 and the inverse-iterate family}',r'\section{Known Stirling periodicity, now formalized}')
body102=body102.replace(r'Take the genuine compositional inverse $F_r$ of $R_r$.',r'''Every normalized series $U$ has a unique normalized compositional inverse.
Indeed, in $U(V)=x$ the coefficient of degree $n\ge2$ is $v_n$ plus
an expression in earlier coefficients of $V$, so it determines $v_n$
with multiplier one and no division. This constructs a right inverse
$V$. Construct a right inverse $W$ of $V$ in the same way; associativity
gives $U=U\circ(V\circ W)=(U\circ V)\circ W=W$, hence $V\circ U=x$
as well. The coefficient recursion proves uniqueness.

Take the genuine compositional inverse $F_r$ of $R_r$.''')
save_entry('A396102','Congruences for an inverse-iterate family','proved_source_conjecture_and_generalization',r'We construct the unique normalized integer solution of $A(A(A(x)))=(1+x)A(A(x))$ and prove that every positive-index coefficient is one modulo three. A parameter theorem determines every natural compositional iterate modulo the parameter, with an explicit source-equation and inverse bridge.',body102,
 [('source_equation','the exact triple-composition equation.'),('source_existence_uniqueness','existence and uniqueness of its normalized solution.'),('coefficient_congruence',r'the source assertion for every $n\ge1$.'),('iterate_congruence','every natural iterate modulo three.'),('family_source_existence','the entire family of original equations.'),('family_source_equation','the canonical family solves that equation.'),('auxiliary_source_equation','the fixed-point equation constructing the inverse.'),('inverse_right, inverse_left','both genuine inverse identities.'),('family_coefficient_congruence','every coefficient modulo the parameter.'),('family_iterate_congruence','the general iterate formula.')],
 ['More.InverseIterate'],r'The source offset is one. The formal original-family statement uses parameter $r+1$, while $A396102=F_3$. Thus $r=2$ in the original-family existence theorem gives the required triple equation. The congruence statements also allow the formal convention \texttt{ZMod 0}, but the mathematical modulus assertions here use positive parameters.',code102,MANIFEST['a396102_inverse_iterate'],
 'A^(composition3)=(1+x)A^(composition2) has a unique normalized integer solution. Every a(n), n≥1, is1 modulo3; every natural iterate has coefficient k^(n−1) modulo3. The full parameter family is included.')

STIRLING_PROOF=r'''\section{The universal finite-transform theorem}
For an arbitrary sequence of integers $(c_k)_{k\ge0}$, write
\[
T_c(n)=\sum_{k=0}^n c_k k!S(n,k).
\]
No growth, sign, positivity, or recurrence hypothesis is needed.
\begin{theorem}\label{thm:period}
For every $m\ge1$ and $n\ge m$,
\[
T_c(n+\varphi(m))\equiv T_c(n)\pmod m.
\]
The tail $t\mapsto T_c(m+t)\bmod m$ has a least positive period $d$;
this $d$ is itself a period and divides $\varphi(m)$.
\end{theorem}
\begin{proof}
If $m=1$ every residue is zero, so the assertions hold with $d=1$.
Suppose $m>1$. First, for every natural number $a$ and $n\ge m$,
\begin{equation}\label{eq:powers}
a^{n+\varphi(m)}\equiv a^n\pmod m.
\end{equation}
Check each maximal prime-power factor $p^e$ of $m$. If $p\mid a$,
then $e\le p^e\le m\le n$, so $p^e$ divides both powers. If
$p\nmid a$, Euler's theorem gives period $\varphi(p^e)$ for powers
of $a$ modulo $p^e$. The prime-power product formula for $\varphi$
shows that $\varphi(p^e)\mid\varphi(m)$. Thus the congruence holds
modulo every prime-power factor, and hence modulo $m$.

The Stirling recurrence gives the falling-factorial expansion
\begin{equation}\label{eq:triangular-power}
a^n=\sum_{k=0}^{a}\binom ak k!S(n,k)\qquad(a\le n).
\end{equation}
For completeness, it follows by counting all functions from an
$n$-element set to an $a$-element set: their $k$ nonempty fibers
partition the domain in $S(n,k)$ ways, and the fibers may be assigned
distinct target values in $a(a-1)\cdots(a-k+1)=\binom ak k!$ ways.
Equivalently, both sides satisfy the induction obtained from the
Stirling recurrence, including $n=0$.

Fix $n\ge m$. Strong induction on $k<m$ now proves
\[
k!S(n+\varphi(m),k)\equiv k!S(n,k)\pmod m.
\]
Apply \eqref{eq:triangular-power} with $a=k$ to the two exponents.
Their left sides are congruent by \eqref{eq:powers}. Each term with
index below $k$ cancels by induction; the remaining multiplier is
$\binom kk=1$. No division by $k!$ modulo $m$ is involved.

For every $k\ge m$, the factor $k!$ is divisible by $m$. The two
transforms therefore reduce to the same fixed finite range $k<m$;
the columnwise congruence just proved gives their equality modulo $m$.

Since $\varphi(m)>0$, at least one positive tail period exists.
Let $d$ be the least such period and let $p$ be any other period.
Write $p=qd+r$ with $0\le r<d$. If $f(t)=T_c(m+t)\bmod m$, then
$f(t+r)=f(t+r+qd)=f(t+p)=f(t)$ for all $t\ge0$.
Thus $r$ is a period, and minimality forces $r=0$.
Taking $p=\varphi(m)$ proves $d\mid\varphi(m)$.
\end{proof}

\section{Generating functions and the application}
The preceding theorem directly applies to the finite formula defining
the sequence in this document. It proves both its totient period and
the existence and divisibility property of its least tail period.

The usual exponential-generating-function interpretation is also
mathematically valid. In $\Q[[x]]$ one has
\[
(e^x-1)^k=k!\sum_{n\ge k}S(n,k)\frac{x^n}{n!}.
\]
Indeed, expanding $(e^x-1)^k$ coefficientwise counts ways to distribute
$n$ labeled elements among $k$ labeled nonempty boxes. These are
surjections, whose number is $k!S(n,k)$. At any fixed degree all
coefficient operations are finite. Consequently, for
$G(t)=\sum_{k\ge0}c_kt^k$,
\[
G(e^x-1)=\sum_{n\ge0}T_c(n)\frac{x^n}{n!}.
\]
This explanation identifies the source's generating-function description
with its finite transform. \textbf{The formal-exponential substitution
identity itself is not separately formalized in this collection.}
The Lean theorems instead start from the explicit finite Stirling sum,
with the exact integer weight specified above. No unproved EGF bridge is
used as a Lean axiom or hypothesis.

\section{Prior result and attribution}
The periodicity is known mathematics, not a newly solved open problem.
Danesh's Theorem 4.1 and Corollary 4.2 \cite{danesh} already give a
stronger universal eventual Carmichael period $\lambda(m)$ for integral
substitutions $G(e^x-1)$. This covers the present totient-period
conclusion as an eventual-period statement. The explicit threshold
$n\ge m$ used here is sufficient; optimality or priority for that
threshold is not asserted. Earlier Fubini and $r$-Fubini work by
Schreyer is also relevant \cite{schreyer}. The formal result here
proves the totient bound; it does not assert a Lean proof of the
stronger Carmichael bound.

The Stirling recurrence and part of the power-expansion implementation
were adapted from Apache-2.0 Mathlib source \cite{mathlib}.
The original copyright, authors, license, and change notice are retained.
The modular transfer and named specialization proofs were generated
for this project. This AI disclosure does not claim authorship of
the adapted upstream code.
'''

STIRLING_ENTRIES=[
 ('A052895','Catalan-weighted Stirling periodicity',r'c_k=C_k=\frac{1}{k+1}\binom{2k}{k}',r'The weight $C_k$ is the $k$th Catalan number, with $C_0=1$. Thus $G(t)=\sum_{k\ge0}C_kt^k$ is the integral Catalan generating series.',r'(fun k => (catalan k : ℤ))',r'(catalan k : ℤ)',None),
 ('A064618','Factorial-weighted Stirling periodicity',r'c_k=k!',r'The weight is the integer factorial, with $0!=1$. The sum is therefore $a_n=\sum_{k=0}^n(k!)^2S(n,k)$. The series $G(t)=\sum_{k\ge0}k!t^k$ is used formally; analytic convergence is not needed.',r'(fun k => (k.factorial : ℤ))',r'(k.factorial : ℤ)',None),
 ('A354242','Central-binomial Stirling periodicity',r'c_k=\binom{2k}{k}',r'The weight is the central binomial coefficient, with $c_0=1$. Equivalently $G(t)=(1-4t)^{-1/2}$ in $\Q[[t]]$; its coefficients are integers.',r'(fun k => ((2*k).choose k : ℤ))',r'((2*k).choose k : ℤ)',r'The separate continued-fraction conjecture in this entry is outside the completed result set.'),
 ('A167137','Partition-weighted Stirling periodicity',r'c_k=p(k)',r'Here $p(k)$ is the number of integer partitions of $k$ into positive parts, with the empty partition counted once at $k=0$. The generating series is $G(t)=\prod_{j\ge1}(1-t^j)^{-1}$; every coefficient receives contributions from finitely many factors.',r'More.Stirling.partitionWeight',r'(Fintype.card (Nat.Partition k) : ℤ)',r'The separate power/logarithm integrality conjecture in this entry is outside the completed result set.'),
 ('A305550','Distinct-partition Stirling periodicity',r'c_k=p_{\mathrm{dist}}(k)',r'Here $p_{\mathrm{dist}}(k)$ counts partitions of $k$ into distinct positive parts, with the empty partition counted once. The corresponding integral series is $G(t)=\prod_{j\ge1}(1+t^j)$.',r'More.Stirling.distinctPartitionWeight',r'((Nat.Partition.distincts k).card : ℤ)',None),
 ('A306082','Square-partition Stirling periodicity',r'c_k=p_{\mathrm{sq}}(k)',r'Here $p_{\mathrm{sq}}(k)$ counts partitions of $k$ whose positive parts are all perfect squares; the empty partition has count one. The integral generating series is $G(t)=\prod_{j\ge1}(1-t^{j^2})^{-1}$.',r'More.Stirling.squarePartitionWeight',r'More.Stirling.squarePartitionWeight k',None),
 ('A080253','Pell-weighted Stirling periodicity',r'c_0=1,\quad c_1=3,\quad c_{k+2}=2c_{k+1}+c_k',r'The weight begins $1,3,7,17,\ldots$ and equals A001333$(k+1)$ in the source notation. The shift is essential. Its generating series is $G(t)=(1+t)/(1-2t-t^2)$.',r'More.Stirling.pellWeight',r'More.Stirling.pellWeight k',None),
]

for oid,title,weight,description,leanweight,leansummand,excluded in STIRLING_ENTRIES:
    source=r'''\section{Exact sequence and result}
Let $S(n,k)$ be the Stirling numbers of the second kind. Their initial
values are $S(0,0)=1$, $S(0,k)=0$ for $k>0$, and $S(n,0)=0$ for
$n>0$; their recurrence is
\[
S(n+1,k+1)=(k+1)S(n,k+1)+S(n,k).
\]
The finite source formula for '''+oid+r''' \cite{oeis} is
\[
a_n=\sum_{k=0}^n c_k k!S(n,k),\qquad '''+weight+r'''.
\]
The source offset is zero. '''+description+r'''

For every $m\ge1$ and $n\ge m$, we prove
$a_{n+\varphi(m)}\equiv a_n\pmod m$. We also prove that the least
positive period of $t\mapsto a_{m+t}\bmod m$ exists, is itself a
period, and divides $\varphi(m)$.
'''
    if excluded: source+='\n'+excluded+'\n'
    source+=STIRLING_PROOF
    sourceproof='by\n  classical\n  rfl' if oid=='A306082' else 'rfl'
    code=f'''open Finset

abbrev a (n : ℕ) : ℤ := More.Stirling.{oid} n

theorem source_formula (n : ℕ) :
    a n = ∑ k ∈ range (n+1),
      {leansummand} * (k.factorial : ℤ) * (More.Stirling.second n k : ℤ) := {sourceproof}

theorem period (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (a (n+m.totient) : ZMod m) = (a n : ZMod m) :=
  More.Stirling.{oid}_period m hm n hn

theorem least_period_divides (m : ℕ) (hm : 0 < m) :
    More.TailPeriodicity.leastPeriod (fun n => (a (m+n) : ZMod m)) ∣ m.totient :=
  More.Stirling.{oid}_leastPeriod_dvd m hm

theorem least_period_specification (m : ℕ) (hm : 0 < m) :
    let f := fun n : ℕ => (a (m+n) : ZMod m)
    0 < More.TailPeriodicity.leastPeriod f ∧
      More.TailPeriodicity.leastPeriod f ∣ m.totient ∧
      (∀ n, f (n+More.TailPeriodicity.leastPeriod f) = f n) ∧
      (∀ q, 0 < q → (∀ n, f (n+q) = f n) →
        More.TailPeriodicity.leastPeriod f ≤ q) :=
  More.Stirling.transform_exact_tail_period {leanweight} m hm
'''
    if oid=='A306082':
        code+=r'''
theorem square_weight_definition (k : ℕ) :
    More.Stirling.squarePartitionWeight k =
      ((Finset.univ.filter fun p : Nat.Partition k =>
        ∀ j ∈ p.parts, Nat.sqrt j * Nat.sqrt j = j).card : ℤ) := by
  classical
  rfl
'''
    if oid=='A080253':
        code+=r'''
theorem weight_zero : More.Stirling.pellWeight 0 = 1 := rfl
theorem weight_one : More.Stirling.pellWeight 1 = 3 := rfl
theorem weight_recursion (k : ℕ) :
    More.Stirling.pellWeight (k+2) =
      2*More.Stirling.pellWeight (k+1)+More.Stirling.pellWeight k := rfl
'''
    qual=r'This entry formalizes a known periodicity result with an explicit sufficient onset. The actual finite integer weight and sum are included in the source formula; no undefined external sequence is assumed to agree with the OEIS entry. The EGF identity is proved in prose above but is not a separate Lean endpoint. '
    if excluded: qual+=excluded+' '
    names=[('source_formula','the actual finite sum with the stated weight.'),('period',r'the unbounded congruence for every $m\ge1$ and $n\ge m$.'),('least_period_divides','divisibility of the least positive tail period.'),('least_period_specification','positivity, periodicity, divisibility, and minimality together.')]
    if oid=='A306082': names.append(('square_weight_definition','the finite cardinality of partitions with square parts.'))
    if oid=='A080253': names.append(('weight_zero, weight_one, weight_recursion','the exact shifted Pell-weight sequence.'))
    original=[n for n in MANIFEST['known_stirling_periodicity_formalization'] if not re.search(r'\.A\d{6}_',n) or oid in n]
    save_entry(oid,title,'formalization_of_known_result',r'For the explicitly defined factorial Stirling transform corresponding to '+oid+r''', we give a self-contained proof of eventual periodicity modulo every positive integer. The tail beginning at the modulus has period dividing Euler's totient. This is a formalization and specialization of known mathematics, credited to the prior work below.''',
      source,names,['More.StirlingPeriodicity'],qual,code,original,
      'For every m≥1 and n≥m, a(n+φ(m))≡a(n) mod m. The least positive period of the tail beginning at m exists and divides φ(m); positivity, minimality, and periodicity are all formalized.',True)

plain_qualifications = {
 'A396093': 'Source offset zero. The proof concerns the actual third composition and gives every n >= 0. Both source assertions and the stronger complete parity pattern are included.',
 'A389474': 'Source offset one. Integral construction, source uniqueness, and genuine compositional inversion are proved. The modulo-three power assertion is a standard Frobenius consequence, not a new general mathematical principle.',
 'A389475': 'Source offset one. Integral construction and source uniqueness are proved. The cube identity is standard Frobenius; the square identity additionally uses the defining equation. Both identities hold at every coefficient index.',
 'A396102': 'Source offset one. A396102 is F_3; the original-family existence theorem uses parameter r+1, so r=2 gives its triple equation. All natural iterates and the general positive-parameter family are included. Formal ZMod 0 extensions are not needed for the stated positive-modulus result.',
}
plain_summaries = {
 'A396093': 'For every n >= 0, a(n) is odd exactly when n modulo 10 is 1, 3, 7, or 9. Every a(2n) is even. For n >= 1, a(2n-1) is even if and only if n=5k-2 for some k >= 1.',
 'A389474': 'The normalized integral source solution is unique. Its square is congruent to x^2+2x^3 modulo 9. For all n,k >= 0, the coefficient of A(x)^(3k)-A(x^3)^k is zero modulo 3.',
 'A389475': 'The normalized integral source solution is unique. As full formal series, A(x)^3 is congruent to A(x^3), and A(x)^2 is congruent to x^2+2A(x^3), modulo 3.',
 'A396102': 'The equation A(A(A(x)))=(1+x)A(A(x)) has a unique normalized integral solution. Every positive-index coefficient is 1 modulo 3. The coefficient at index n of the kth natural iterate is k^(n-1) modulo 3. The full parameter family is included.',
}
for entry in CATALOGUE:
    oid = entry['oeis_id']
    if oid in plain_qualifications:
        entry['qualifications'] = plain_qualifications[oid]
        entry['summary'] = plain_summaries[oid]
    else:
        entry['summary'] = 'For every m >= 1 and n >= m, a(n+φ(m)) is congruent to a(n) modulo m. The least positive period of the tail beginning at m exists and divides φ(m); positivity, minimality, and periodicity are all formalized.'
        entry['qualifications'] = ('Known result, credited to Payam Danesh and earlier related Fubini-periodicity work. Source offset zero. Lean proves the explicit finite Stirling sum with the exact integer weight, the totient period, and the least-tail-period properties. The EGF substitution identity is explained and proved in the manuscript but is not separately a Lean theorem. The onset n >= m is sufficient; optimality is not asserted. The stronger Carmichael-period bound is not formalized here.')
        if oid == 'A354242':
            entry['qualifications'] += ' The separate continued-fraction conjecture remains outside this result set.'
        if oid == 'A167137':
            entry['qualifications'] += ' The separate power/logarithm integrality conjecture remains outside this result set.'

(ROOT/'catalogue/second_entries.json').write_text(json.dumps(CATALOGUE,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'entries':len(CATALOGUE),'new_endpoints':sum(len(e['new_endpoints']) for e in CATALOGUE),'ids':[e['oeis_id'] for e in CATALOGUE]}))
