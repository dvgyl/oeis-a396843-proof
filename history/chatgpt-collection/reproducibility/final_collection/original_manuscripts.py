from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[2]
CAT=json.loads((ROOT/'catalogue/original_entries.json').read_text())
old=(ROOT/'manuscript/compositional_congruences.tex').read_text()
hanna=(ROOT/'prior_work/hanna_congruences.tex').read_text()

def between(s,a,b):return s[s.index(a):s.index(b)]

def preamble(id,title):return r'''\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage[margin=25mm]{geometry}
\usepackage{amsmath,amssymb,amsthm,booktabs,microtype,enumitem}
\usepackage[hidelinks]{hyperref}
\hypersetup{pdftitle={'''+title+r'''},pdfauthor={Dev Goyal},pdfsubject={'''+id+r'''; formal power series and Lean proofs}}
\setlength{\parskip}{3pt}
\setlength{\emergencystretch}{3em}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{remark}\newtheorem{remark}[theorem]{Remark}
\newcommand{\Z}{\mathbb Z}
\newcommand{\N}{\mathbb N}
\newcommand{\F}{\mathbb F}
\newcommand{\coeff}[2]{[x^{#1}]#2}
\title{'''+title+r'''}
\author{Dev Goyal}
\date{24 October 2026}
\begin{document}
\maketitle
\begin{center}\fbox{\begin{minipage}{0.91\linewidth}
\textbf{AI disclosure and review status.}
ChatGPT (OpenAI) generated the mathematical arguments, formal proof code,
and this manuscript from Dev Goyal's prompts. Dev Goyal is the sole human
author and initiated the investigation. This consolidated presentation is
AI-generated; independent human review of this presentation is pending.
Source conjectures and prior results retain the credits given below.
\end{minipage}}\end{center}
'''

def formal(c,extra=''):
 ids=c['new_endpoints']
 return r'''
\section{Formal proof and scope}
The accompanying entry file is \path{'''+c['lean_file']+r'''}.
It states the results with explicit Lean types and supplies proof terms
using the complete shared implementation included in the collection.
The manuscript is self-contained mathematically; the Lean entry file uses
those ordinary library imports rather than duplicating the full foundation.
'''+extra+r'''
The entry's named theorem interfaces are listed below. The namespace of
each is \path{FinalCollection.'''+c['oeis_id']+r'''}.
\begin{itemize}[leftmargin=1.5em,itemsep=1pt]
'''+''.join(r'\item \path{'+n.split('.')[-1]+'}\n' for n in ids)+r'''\end{itemize}
The preserved dependencies also contain all supporting constructions,
coefficient identities, map-compatibility results, and inverse proofs.
The collection pins Lean 4.19.0 and Mathlib revision
\path{c44e0c8ee63ca166450922a373c7409c5d26b00b}.
The verification report records fresh compilation and the transitive axiom
audit. Finite numerical checks corroborate the definitions and indexing;
the universally quantified Lean theorems establish the all-index claims.
No assertion of worldwide novelty, OEIS acceptance, publication, or completed
human review follows from these checks. The prose may use elementary
identities that the formal proof establishes by a different algebraic route.
'''

def bib(id,additional=''):
 return r'''
\begin{thebibliography}{9}\raggedright
\bibitem{oeis} P. D. Hanna, \emph{'''+id+r'''}, The On-Line Encyclopedia of Integer
Sequences. \url{https://oeis.org/'''+id+r'''}. Source recorded in the retained
proof collection, 24 October 2026.
\bibitem{repo} D. Goyal, \emph{OEIS A396843 proof repository}.
\url{https://github.com/dvgyl/oeis-a396843-proof}.
Reference revision \path{995e55adcbe06b2a913e24f12ff73a7faf362f06}.
'''+additional+r'''\end{thebibliography}
\end{document}
'''

# Shared mathematical arguments are repeated so each paper stands alone.
consecutive_core=between(old,r'\section{Formal power series and uniqueness}',r'\section{The four assertions for A396099}')
integer_core=between(old,r'\section{Integer iterates and exact composition order}',r'\section{Related OEIS assertions}')
integer_core=integer_core.replace('The statements for A396797 and A396807 include negative iterate\nindices. We give the extension explicitly.','We also prove the integer-iterate extension explicitly, with negative\nindices defined through the normalized compositional inverse.')
scaled_core=between(old,r'\subsection{Removing the apparent division}',r'The four congruence applications and two parity applications are')
hanna_core=between(hanna,r'\section{Formal power series and notation}',r'\section{Residue formulas for the original examples}')

for c in CAT:
 id=c['oeis_id'];s=preamble(id,c['title'])
 if id in ['A396843','A396844']:
  m=3 if id=='A396843' else 4
  s+=r'''
\begin{abstract}
We give a separate complete manuscript for '''+id+r''', including the
parameter-family proof on which its conclusions depend. For the unique
normalized solution of $A_m(xA_m-mxA_m^2)=x^2$, we prove parity,
exact residues modulo $m^2$, binary-digit divisibility for both the series
and its compositional inverse, and the minimum prime-exponent criterion.
The entry under consideration is $m='''+str(m)+r'''$.
\end{abstract}
\section{The entry and the claims}
Let $a_n(m)=[x^n]A_m(x)$, where
\begin{equation}\label{eq:general}
 A_m\bigl(xA_m(x)-mxA_m(x)^2\bigr)=x^2,
 \qquad A_m=x+O(x^2).
\end{equation}
The sequence '''+id+r''' is the case $m='''+str(m)+r'''$; the constant
coefficient is zero, and the OEIS sequence is indexed from one.
The defining series and source questions are due to Paul D. Hanna
\cite{oeis'''+str(m)+r'''}.
We write $s_2(n)$ for the number of ones in the binary expansion of $n$.
The general results below give, in particular,
\[
 m^{s_2(n-1)}\mid a_n(m)\quad(n\ge1),
 \qquad
 a_{2^j+1}(m)\equiv m(-1)^j\pmod{m^2}.
\]
All other coefficients of degree at least two vanish modulo $m^2$.
The binary bound also holds for the coefficients of the inverse series.
'''
  if m==3:
   s+=r'''
Every positive-index coefficient of A396843 is odd. For $n\ge2$,
its residues modulo nine are three when $n=4^k+1$, six when
$n=2\cdot4^k+1$, and zero otherwise. The classification is a correction
to the older false residue claim. Danial Asaria's prior counterexample,
recorded in the source, used $a_5(3)=975\equiv3\pmod9$.
'''
  else:
   s+=r'''
The corrected residue theorem is, for $n\ge2$,
\[
a_n(4)\equiv
\begin{cases}
4\pmod{16},&n=4^k+1,\ k\ge0,\\
12\pmod{16},&n=2\cdot4^k+1,\ k\ge0,\\
0\pmod{16},&\text{otherwise}.
\end{cases}
\]
The first exceptional class is essential. The earlier source assertion
specified residue twelve in the second class and divisibility by sixteen
otherwise for $n>8$. At $n=17=4^2+1$ the correct residue is four,
so that other clause is false. We prove the corrected theorem, not the
false original clause. All coefficients after the first are even.
'''
  s+=r'''
\paragraph{Provenance.}
These arguments are adapted from the original A396843 repository supplied
by Dev Goyal. Its historical declaration of human verification concerns
that earlier report. It is not a declaration that this new editorial
consolidation has received independent human review.
The parameter-family results are retained mathematical work, not new
problems introduced by this final packaging.
'''+hanna_core
  s+=r'''
\section{Specialization to '''+id+r'''}
Substitute $m='''+str(m)+r'''$ in Theorems~\ref{thm:parity},
\ref{thm:modsquare}, and \ref{thm:binary}, and in
Corollary~\ref{cor:valuation}. In the residue formula, write
$j=2k$ or $j=2k+1$. Then $2^j=4^k$ or $2\cdot4^k$ respectively,
and $(-1)^j=1$ or $-1$. This proves precisely the two exceptional
classes stated at the start, with every other index handled by the
second case of Theorem~\ref{thm:modsquare}. The powers of two are
strictly increasing, so these exceptional classes are disjoint.
'''
  s+=formal(c,'The complete original acceptance layer is retained in '+r'\path{lean/Hanna/Acceptance.lean}'+'. Its sixteen audited endpoints include the general parameter results and both the parameter-three and parameter-four residue specializations.\n')
  s+=hanna[hanna.index(r'\begin{thebibliography}'):]
 elif id in ['A396099','A396798','A396807','A396797']:
  r={'A396099':2,'A396798':4,'A396807':5,'A396797':3}[id]
  s+=r'''
\begin{abstract}
This paper gives the defining construction and all completed congruence
results for '''+id+r'''. It includes the full elementary argument for the
consecutive-iterate family, so no companion paper is needed to follow the
proof. The entry is the parameter $r='''+str(r)+r'''$.
'''
  if id=='A396798':s+='The false starting phase of the original coefficient block is explicitly refuted and corrected.\n'
  if id=='A396797':s+='This is a formalization of a known result credited to Shiva Priyan Shanmuga Sundaram, not a new solution claim.\n'
  s+=r'''\end{abstract}
\section{Definition, result, and attribution}
For an integer $r\ge1$, let $F_r$ be the normalized series determined by
\begin{equation}\label{eq:family}
 F_r=x+F_r^{\circ r}F_r^{\circ(r+1)},\qquad F_r=x+O(x^2).
\end{equation}
A superscript $\circ k$ means repeated composition; an ordinary power
means multiplication. Set $a_n=[x^n]F_{'''+str(r)+r'''}$.
The sequence '''+id+r''' is this case $r='''+str(r)+r'''$, with source
indices $n\ge1$ and an additional zero constant coefficient \cite{oeis}.
All congruences below are coefficientwise.

We prove the formula, for every integer $k$,
\[
F_r^{\circ k}\equiv
\frac{x}{1-kx}+
\begin{cases}
\displaystyle\frac{rx^4}{(1-x)^3},&r\text{ even and }k\text{ odd},\\[5pt]
0,&\text{otherwise}
\end{cases}
\pmod{2r}.
\]
The reduced series has exact order $2r$ under composition. Existence,
uniqueness, and the meaning of negative iterates are proved below.

Hanna recorded the source sequences. Sundaram proved the $r=3$ case,
including integer iterates, in September 2026 \cite{sundaram}. The
odd-parameter argument extends that comparison-series method.
The even-parameter argument needs the displayed correction. The source
conjecture labels in the retained collection do not establish exclusive
priority or worldwide openness.
'''
  s+=consecutive_core+integer_core
  if r==2:
   s+=r'''
\section{All four A396099 assertions}
Take $A=F_2$ and put $T=x/(1-x)$, $H=x^4/(1-x)^3$.
The general theorem gives
\begin{align*}
A&\equiv T+2H\pmod4,\\
A^{\circ2}&\equiv x+2x^2\pmod4.
\end{align*}
Every positive-index coefficient of the first expression is odd. Since
$[x^n]H=\binom{n-2}{2}$ for $n\ge4$ and is zero below degree four,
the residue of $a_n$ for $n\ge3$ is three if $n\equiv0,1\pmod4$
and one otherwise. Indeed,
$\binom{n+2}{2}-\binom{n-2}{2}=4n-2$ is even, and the values at
$n=2,3,4,5$ are $0,0,1,3$. Thus the residue block is
$1,3,3,1$ beginning at degree three. The second displayed identity
shows that every coefficient of the second iterate above degree two
is divisible by four.

For the remaining assertion work modulo four and write $f=T+2H$.
From $f^{\circ2}=x+2x^2$ and the square-zero substitution rule,
$f^{\circ3}=f+2x^2f'$. Therefore
\begin{align*}
f-xf^{\circ3}
&=(1-x)f-2x^3f'\\
&=x+2\bigl((1-x)H-x^3T'\bigr)\\
&=x+2\frac{x^4-x^3}{(1-x)^2}
=x+\frac{2x^3}{1-x}\pmod4.
\end{align*}
Every coefficient above degree two in $A-xA^{\circ3}$ is consequently
two modulo four. This proves all four source assertions, including
their exact starting indices. The separate source contract also proves
them for any normalized integral series satisfying the original equation,
by the uniqueness already established.
'''
  elif r==4:
   part=between(old,r'\subsection{A396798: seven iterate assertions and a phase correction}',r'\subsection{A396807 and the previously proved A396797 case}')
   part=part.replace(r'\subsection{',r'\section{',1).replace(r'\cite{oeis798}',r'\cite{oeis}')
   s+=part
  else:
   modulus=2*r
   s+=r'''
\section{The '''+id+r''' specialization}
Since $r='''+str(r)+r'''$ is odd, the correction term is absent. For
every integer $k$,
\[
F_{'''+str(r)+r'''}^{\circ k}(x)\equiv\frac{x}{1-kx}
\pmod{'''+str(modulus)+r'''}.
\]
The coefficient of $x$ is one. For every $n\ge2$, expansion of the
geometric series gives
\[
[x^n]F_{'''+str(r)+r'''}^{\circ k}\equiv k^{n-1}
\pmod{'''+str(modulus)+r'''}.
\]
Taking $k=1$ proves that every positive-index coefficient of the source
series is one modulo '''+str(modulus)+r'''. Taking $k=0$ gives the
identity series $x$; the degree-one coefficient is stated separately
to make this boundary case explicit. The Lean theorem also includes
$n=1$ using the ordinary convention $k^0=1$.

Reduction commutes with the genuine two-sided compositional inverse,
as proved above, so the formula applies to negative $k$ as well.
The reduced series equals $x$ exactly when '''+str(modulus)+r''' divides
$k$, by its degree-two coefficient and the displayed formula. This
establishes the exact composition order, including signed iterate indices.
'''
   if r==3:s+=r'''
This $r=3$ result was already proved by Sundaram. Its separate entry here
is included because the previous collection explicitly recovered it from
the general theorem. It is a credited formalized specialization and is
not counted as a newly solved open conjecture.
'''
  s+=formal(c)
  s+=bib(id,r'''\bibitem{sundaram} Shiva Priyan Shanmuga Sundaram,
\emph{A Proof of the Congruence Conjectures for OEIS A396797}, September 2026.
\url{https://oeis.org/A396797/a396797.pdf}.
''')
 else:
  q={'A393856':4,'A393857':5,'A393858':6,'A393859':7}[id]
  s+=r'''
\begin{abstract}
For the scaled inverse series '''+id+r''' we prove that every
positive-index coefficient is one modulo '''+str(q+1)+r'''.
'''
  if q%2==0:s+=r'We also prove that a coefficient is odd exactly when its index is a power of two.'+'\n'
  s+=r'''The source equation, coefficientwise interpretation of its quotient,
existence, uniqueness, and the all-index proof are given explicitly.
\end{abstract}
\section{Source equation and theorem}
For a positive integer $q$, consider the normalized series $G_q$ satisfying
\begin{equation}\label{eq:scaled-source}
 G_q\left(x-\frac{xG_q(qx)}q\right)=x,
 \qquad G_q=x+O(x^2).
\end{equation}
The source '''+id+r''' of Paul D. Hanna is the case $q='''+str(q)+r'''$
\cite{oeis}. Put $a_n=[x^n]G_{'''+str(q)+r'''}$. Its source indices
start at one and $a_0=0$. We prove
\[
 a_n\equiv1\pmod{'''+str(q+1)+r'''}\qquad(n\ge1).
\]
'''
  if q%2==0:s+=r'''
For every $n\ge0$ we also prove
\[
 a_n\text{ is odd}\quad\Longleftrightarrow\quad
 n=2^j\text{ for some }j\ge0.
\]
Thus the parity statement includes $n=0$ and the initial term $n=1$.
'''
  s+=r'''
All series are formal: equality and congruence are coefficientwise, and
composition $U(V)=\sum_{j\ge0}u_jV^j$ is used only when $V(0)=0$.
Every coefficient then receives finitely many contributions.
A series with constant coefficient one is a multiplicative unit:
if $W(0)=0$, its inverse is $\sum_{j\ge0}(-W)^j$.
This justifies the rational comparison series below without analytic
convergence or division in a residue ring.
'''+scaled_core
  s+=r'''
\section{Application to '''+id+r'''}
Take $q='''+str(q)+r'''$ in Theorem~\ref{thm:scaled-congruence}.
Its modulus is $q+1='''+str(q+1)+r'''$, so every positive-index
coefficient has the asserted residue. '''
  if q%2==0:s+=r'''The parameter is even, so Theorem~\ref{thm:scaled-parity}
gives the precise power-of-two support modulo two. These are both
source assertions, with no upper index bound.
'''
  else:s+=r'''Since this modulus is even, the same formula also implies
that every positive-index coefficient is odd. The source congruence
is valid at composite modulus '''+str(q+1)+r'''; the proof used units
with constant coefficient one and did not cancel a nonunit parameter.
'''
  s+=formal(c)+bib(id)
 if id=='A396844':
  s=s.replace('Its sixteen audited endpoints include the general parameter results and both the parameter-three and parameter-four residue specializations.','The shared endpoints \\path{Hanna.Acceptance.inverse_binary_divisibility_integer}\nand \\path{Hanna.Acceptance.minimum_prime_exponent_iff} give the general\ninverse-divisibility and minimum-exponent assertions used in this paper.\nThe counterexample at $n=17$ follows by taking $k=2$ in the checked\n\\path{residues_parameter_four} classification.')
 if id=='A396844':
  s=s.replace(r'\begin{thebibliography}{9}',r'\begin{thebibliography}{9}\setlength{\itemsep}{2pt}\setlength{\parsep}{0pt}')
 (ROOT/c['manuscript_tex']).write_text(s)
print('Wrote',len(CAT),'standalone LaTeX manuscripts')
