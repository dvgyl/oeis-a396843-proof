from pathlib import Path
import re,json
ROOT=Path(__file__).resolve().parents[2]
V3=(ROOT/'manuscript/six_more_oeis_proofs.tex').read_text()
V4=(ROOT/'manuscript/more_oeis_proofs_and_corrections.tex').read_text()
ROWS=json.loads((ROOT/'catalogue/recent_entries.json').read_text())

def between(s,a,b): return s[s.index(a):s.index(b,s.index(a))]
def lemmablock(s,label):
 i=s.index('\\label{'+label+'}');start=s.rfind('\\begin{lemma}',0,i)
 stop=s.index('\\end{proof}',i)+len('\\end{proof}')
 return s[start:stop]+'\n\n'
def toolsection(v,labels):return '\\section{Formal algebra used in the proof}\n\n'+''.join(lemmablock(v,k) for k in labels)
def trimend(s,start):return s[:s.index(start)] if start in s else s

def tools3(labels):return toolsection(V3,labels)
def tools4(labels):
 s=toolsection(V4,labels)
 if 'lem:construction' in labels:
  s=s.replace('The recurrence requires\nonly ring operations,', 'The same induction applies with only the constant coefficient prescribed,\nprovided agreement is improved starting at degree one. It also applies to\nan operator on all series when agreement is improved starting at degree zero.\nFor the operators used in this paper, the recurrence requires\nonly ring operations,')
 return s

BODY={}
BODY['A397588']=tools3(['lem:contraction','lem:binary'])+between(V3,'\\section{A397588:', '\\section{A389536:')
BODY['A389536']=tools3(['lem:contraction','lem:binary','lem:double'])+between(V3,'\\section{A389536:', '\\section{A389537:')
BODY['A389537']=tools3(['lem:contraction','lem:inverse','lem:binary','lem:double'])+between(V3,'\\section{A389537:', '\\section{A389542:')
BODY['A389542']=tools3(['lem:contraction','lem:inverse','lem:binary','lem:double'])+between(V3,'\\section{A389542:', '\\section{A378580 and A378581:')
sharedtheta=between(V3,'\\section{A378580 and A378581:', '\\section{Formal coverage,')
sharedtheta=sharedtheta.replace('The two source equations are','To treat the selected source, we construct a pair of auxiliary substitution\nequations. For a constant-one target, these equations are')
sharedtheta=sharedtheta.replace('This proves one original coefficient conjecture in each of A378580\nand A378581 \\cite{oeis580,oeis581}.', 'This proves the coefficient conjecture for the selected source, with the\nother substitution sign supplied by the same general construction\n\\cite{oeis580,oeis581}.')
sharedtheta=sharedtheta.replace('No additional specializations\nare counted as new problems in this paper.','The shared mechanism is included to make this manuscript self-contained.')
for id in ['A378580','A378581']:
 BODY[id]=tools3(['lem:contraction','lem:inverse','lem:double'])+sharedtheta.replace('\\section{A378580 and A378581: theta substitution}',r'\section{Construction and square support for '+id+'}')
BODY['A195194']=tools4(['lem:construction','lem:inverse','lem:binary'])+between(V4,'\\section{A195194:', '\\section{A393172 and A393171:')
catalan=between(V4,'\\section{A393172 and A393171:', '\\section{A380056:')
first=trimend(catalan,'\\begin{theorem}[A393171 modulo eight]')
BODY['A393172']=tools4(['lem:construction','lem:inverse','lem:binary'])+first.replace('\\section{A393172 and A393171: Catalan substitution}',r'\section{Source construction and the modulus-four theorem}')
BODY['A393172']=BODY['A393172'].replace('\\tag{3}','\\tag{1}').replace('(3)','(1)')
BODY['A393171']=tools4(['lem:construction','lem:inverse','lem:binary'])+catalan.replace('\\section{A393172 and A393171: Catalan substitution}',r'\section{A prerequisite congruence and the modulus-eight lift}')
BODY['A393171']=BODY['A393171'].replace('\\tag{3}','\\tag{1}').replace('\\tag{4}','\\tag{2}').replace('(3)','(1)').replace('(4)','(2)')
BODY['A380056']=between(V4,'\\section{A380056:', '\\section{Rational theta sums:')
BODY['A380056']=BODY['A380056'].replace('\\tag{5}','\\tag{1}').replace('\\tag{6}','\\tag{2}').replace('(5)','(1)').replace('(6)','(2)')
ratiointro=r'''\section{The literal positive-index source}

For a formal series $U$ over a commutative ring, put
\[
 Q_j(U)=\frac{U-x^j}{1-x^jU}\quad(j\ge1),\qquad
 \Sigma(U)=\sum_{j\ge1}x^{j^2}Q_j(U)^j. \tag{1}
\]
The denominator is a constant-one unit, so the quotient denotes a genuine
multiplicative inverse. The $j$th summand has order at least $j^2$.
Each coefficient is therefore a finite sum, and no analytic convergence
assumption is required. This is the positive-index formula (2) given by OEIS.
A separate formal Laurent-series equivalence with the bilateral title is
outside the claimed Lean coverage.

'''
implicit=r'''The selected implicit series is the solution of
\[
 A=1+2\Sigma(A). \tag{2}
\]
'''
explicit=r'''The selected explicit series is
\[
 B=1+2\Sigma(2). \tag{2}
\]
Here $2$ denotes the constant series. This distinction from inserting
$B$ in the argument of $\Sigma$ determines the different residue support.
'''
imp_proof=between(V4,'\\begin{lemma}[Existence for the implicit theta equation]','\\begin{theorem}[The corrected A380680 statement]')
imp_proof=imp_proof.replace('(7)','(1)').replace('(8)','(2)')
BODY['A380060']=tools4(['lem:construction','lem:inverse','lem:binary'])+ratiointro+implicit+imp_proof
exp_proof=between(V4,'\\begin{theorem}[The corrected A380680 statement]','The source\'s displayed coefficients already expose')
exp_proof=exp_proof.replace('(9)','(2)')
BODY['A380680']=tools4(['lem:construction','lem:inverse','lem:binary'])+ratiointro+explicit+exp_proof
BODY['A380680']+='\nThe displayed source coefficients already expose both failures. The\nnewly presented theorem supplies the complete corrected twice-square pattern;\nit is a correction, not a proof of the false square-index statement.\n'
odd=between(V4,'\\section{An elementary additional observation: A392210}', '\\section{Formal verification,')
odd=trimend(odd,'The module \\texttt{Round4.NestedBinomial}')
BODY['A392210']=tools4(['lem:construction','lem:inverse'])+'\\section{A square-substitution construction}\n\n'+lemmablock(V4,'lem:square')+odd
BODY['A392210']=BODY['A392210'].replace('\\tag{10}','\\tag{1}').replace('(10)','(1)')

compact_theta_tools=r"""\section{Units, coefficient maps, and doubling}

A constant-one series $U=1+\sum_{n>0}u_nx^n$ has a unique multiplicative
inverse $V=1+\sum_{n>0}v_nx^n$: the coefficient equation for $UV=1$ is
\[
 v_n=-\sum_{k=1}^n u_kv_{n-k}\qquad(n>0).
\]
Thus inversion uses only ring operations, is defined integrally, and commutes
with coefficient homomorphisms. If two constant-one series agree modulo
$x^r$, the recurrence shows that their inverses agree modulo $x^r$ as well.
Locally finite coefficient sums, products, and integral powers also commute
with coefficient maps.

\begin{lemma}[Doubling]\label{lem:binary}
For formal series $U,V$ over $\Z/4\Z$, $2U=2V$ if and only if their
reductions modulo two agree.
\end{lemma}
\begin{proof}
For integers $u,v$, $4\mid2(u-v)$ is equivalent to $2\mid u-v$. Apply
this equivalence to every coefficient. No cancellation by two inside
$\Z/4\Z$ is used.
\end{proof}

"""
old_theta_end=r"""The
degree-by-degree construction and uniqueness argument of
Lemma~\ref{lem:construction} therefore apply starting with the constant
coefficient. Mapping the locally finite sums, unit inverses, and the
equation gives transport by uniqueness."""
new_theta_end=r"""Set its constant coefficient to one. Once the coefficients below
$n$ have been chosen, the improvement of agreement shows that the degree-$n$
coefficient on the right depends only on those earlier choices. Choose the
next coefficient to equal it. Induction gives a fixed point over $K$, integral when $K=\Z$, and
the same coefficient comparison proves uniqueness. Mapping the locally finite
sums, unit inverses, and the equation gives transport by uniqueness."""
for _id in ['A380060','A380680']:
 BODY[_id]=BODY[_id].replace(tools4(['lem:construction','lem:inverse','lem:binary']),compact_theta_tools)
 BODY[_id]=BODY[_id].replace(old_theta_end,new_theta_end)
BODY['A393172']=BODY['A393172'].replace('We use $A$ for A393172\nand $B$ for A393171 throughout this section, to keep the two source\nseries distinct \\cite{oeis172,oeis171}.','We use $A$ for the source sequence A393172 \\cite{oeis172}.')

META={
'A397588':('Binary parity for a differential power series','1','oeis588','3 July 2026',r'The unique normalized solution of $A=x+(xA^2)\prime$ has an odd coefficient precisely at powers of two. We give the integral construction, the complete parity proof, and the additional identity $A\equiv x\pmod3$. The latter verifies a source assertion already stated without a conjecture label.'),
'A389536':('Sparse residues in a Mahler substitution equation','1','oeis536','28 October 2025',r'The normalized solution of $A(x^2+2x^3)=xA(x)$ satisfies $A\equiv x+2xC\pmod4$, where $C=x+C^2$. Its coefficients above degree one are two modulo four exactly at indices $2^k+1$, and zero otherwise. The source equation is solved integrally before reduction.'),
'A389537':('Residues of an alternating lacunary inverse','1','oeis537','3 November 2025',r'The unique normalized integer solution of $A(A-x)=A^2$ has residue two modulo four exactly at indices $3\cdot2^k$ above degree two. We identify it as a genuine compositional inverse and prove the complete pattern by exact integral halving followed by a characteristic-two recursion.'),
'A389542':('A reversion that becomes an involution modulo four','1','oeis542','1 November 2025',r'We construct the unique normalized integer solution of $A(A^2-x^2)=4A^3$. Above degree one, its residue modulo four is two exactly at indices $2^k+1$ and zero otherwise. An auxiliary inverse becomes an involution after reduction; no cancellation of two in a residue ring is used.'),
'A378580':('Square-index residues for theta quotient substitution','0','oeis580','8 January 2025',r'Let $\Theta=1+2\sum_{j\ge1}x^{j^2}$. The unique constant-one integral solution of $A(x/A)=\Theta$ satisfies $A\equiv\Theta\pmod4$. We construct the literal unit quotient and prove that the positive-index residue is two precisely at squares and zero elsewhere.'),
'A378581':('Square-index residues for theta product substitution','0','oeis581','8 January 2025',r'Let $\Theta=1+2\sum_{j\ge1}x^{j^2}$. The unique constant-one integral solution of $A(xA)=\Theta$ satisfies $A\equiv\Theta\pmod4$. A division-free construction and a square-zero perturbation argument prove the full positive-index classification.'),
'A195194':('Parity of an infinite nested reversion','1','oeis194','11 September 2011',r'For arbitrary weights in a commutative ring, we construct a unique infinite family of normalized nested reversions and prove finite-depth coefficient stabilization. For weights $1,2,3,\ldots$, the first tail has odd coefficients exactly at powers of two. This is a statement about formal series, independent of analytic convergence.'),
'A393172':('A Catalan substitution congruence modulo four','1','oeis172','4 February 2026',r'The unique normalized integral solution of $A(x-x^2)=x+A^2$ satisfies $A\equiv2C-x\pmod4$, where $C=x+C^2$. Hence its coefficients above degree one have residue two precisely at powers of two, and zero otherwise. The comparison satisfies the literal source equation.'),
'A393171':('A Catalan substitution congruence modulo eight','1','oeis171','4 February 2026',r'For $C=x+C^2$, the unique normalized integral solution of $B=x+B(C)^2$ has residue four modulo eight precisely at indices $2^k$ or $2^k+1$, $k\ge1$, above degree two. We prove the prerequisite modulus-four result and an exact integral lift, so this manuscript is independent of the companion paper.'),
'A380056':('Exponential coefficients and congruences modulo four and five','1','oeis056','28 January 2025',r'If $\sum a_nx^n/n!=(e^x-1)/\cos(2x)$, then $a_n\equiv1\pmod4$ for $n\ge1$ and $a_n\equiv2\cdot2^n+3\cdot4^n\pmod5$ for all $n\ge0$. Thus $5\mid a_n$ exactly when $4\mid n$. Integer binomial convolution constructs the sequence and proves its literal rational exponential-generating-function identity.'),
'A380060':('Square support in an implicit rational theta equation','0','oeis060','6 February 2025',r'We construct the unique integral solution of the positive-index rational theta equation $A=1+2\Sigma(A)$ and prove $A\equiv1+2\sum_{j\ge1}x^{j^2}\pmod4$. Its coefficient at a positive index is two modulo four exactly at squares and is divisible by four otherwise.'),
'A380680':('A false square-index conjecture and its twice-square correction','0','oeis680','6 February 2025',r'The retrieved square-index conjecture fails already at $a_1=4$ and $a_2=6$. For the explicit positive-index rational theta sum, we prove the corrected identity $B\equiv1+2\sum_{j\ge1}x^{2j^2}\pmod4$. The full exceptional support is therefore twice a square, and both clauses of the false statement are explicitly refuted.'),
'A392210':('Odd-index evenness in a nested binomial equation','1','oeis210','2 February 2026',r'The normalized equation $D=x+(D(x/(1-x)))^2$ has a unique integral solution. Every odd-index coefficient beyond the first is even. We prove the source construction and the elementary characteristic-two square argument; the result formalizes an observed pattern, not a new general principle.')
}

COMMON_PREAMBLE=r'''\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage[margin=26mm]{geometry}
\usepackage{amsmath,amssymb,amsthm,booktabs,array,longtable}
\usepackage{microtype,multicol}
\usepackage[hidelinks]{hyperref}
\setlength{\parskip}{3pt}
\setlength{\emergencystretch}{2em}
\raggedbottom
\allowdisplaybreaks[1]
\clubpenalty=10000
\widowpenalty=10000
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newcommand{\Z}{\mathbb Z}
\newcommand{\Q}{\mathbb Q}
\newcommand{\N}{\mathbb N}
\newcommand{\F}{\mathbb F}
\newcommand{\ps}[1]{#1[[x]]}
\newcommand{\Rev}{\operatorname{Rev}}
\newcommand{\rev}{^{\langle-1\rangle}}
\newcommand{\Plus}{\operatorname{Plus}}
\newcommand{\Minus}{\operatorname{Minus}}
\newcommand{\coeff}[2]{[x^{#1}]#2}
\newcommand{\E}{\mathcal E}
\Urlmuskip=0mu plus 1mu
'''
DISCLOSURE=r'''\begin{center}
\fbox{\begin{minipage}{0.9\linewidth}\small
\textbf{AI disclosure.} ChatGPT (OpenAI) generated the mathematical arguments,
Lean proofs, and this manuscript in response to Dev Goyal's requests.
Dev Goyal is the sole human author. The source sequence and conjecture or
observation are credited to Paul D. Hanna.
\textbf{Independent human review is pending.}
\end{minipage}}
\end{center}
'''
NOTATION=r'''All series are formal. The set $\N$ includes zero, and $[x^n]U$ denotes a
coefficient. A normalized series is $x+O(x^2)$; $O(x^r)$ means divisibility
by $x^r$, over any coefficient ring used below. We write $U\circ V=U(V(x))$
only when $V(0)=0$. Compositional inversion, denoted $\Rev(U)$ or $U\rev$,
is distinct from multiplicative inversion of a unit. Congruences are
coefficientwise; ordinary products and compositional iterates are distinct.
'''

def texescape(s):return s.replace('&',r'\&').replace('_',r'\_').replace('%',r'\%').replace('#',r'\#')

for row in ROWS:
 id=row['oeis_id'];title,offset,key,date,abstract=META[id]
 # Correct a derivative typography shorthand only in the abstract.
 abstract=abstract.replace(r'(xA^2)\prime',r'(xA^2)\!\,{}\prime') if False else abstract.replace(r'A=x+(xA^2)\prime',r'A=x+(xA^2)\!\,{}^{\prime}')
 out=COMMON_PREAMBLE+'\\hypersetup{pdftitle={'+id+': '+title+'},pdfauthor={Dev Goyal},pdfsubject={Separate manuscript with AI disclosure and Lean proof map}}\n'
 out+='\\title{'+id+'\\\\[4pt]\\large '+title+'}\n\\author{Dev Goyal}\n\\date{24 October 2026}\n\\begin{document}\n\\maketitle\n'+DISCLOSURE
 out+='\\begin{abstract}\n'+abstract+'\n\\end{abstract}\n\n\\section{Source, notation, and scope}\n\n'
 out+='The source is Paul D. Hanna\'s OEIS entry '+id+' \\cite{'+key+'},\nretrieved on 24 October 2026. Its initial sequence index is '+offset+'.\n'
 if id=='A380056':out+='We use the auxiliary value $a_0=0$ and distinguish the exponential\ncoefficients $a_n=n![x^n]A$ from ordinary rational coefficients.\n'
 elif offset=='1':out+='We also retain the formal zero constant coefficient at index zero.\n'
 else:out+='The constant coefficient is one; the residue classification below\nis restricted to positive indices.\n'
 out+='\n'+NOTATION
 if id in ['A378580','A378581']:out+='\nIn this manuscript $\\Theta(x)=1+2\\sum_{j\\ge1}x^{j^2}$. The chosen source is\n'+(r'$A(x/A)=\Theta$.' if id=='A378580' else r'$A(xA)=\Theta$.')+' The auxiliary construction treats both signs.\n'
 out+='\n'+BODY[id]
 out+='\n\\section{Separate Lean proof and checked scope}\n\n'
 out+='The entry file is \\nolinkurl{lean/Entries/'+id+'.lean}. Its explicit\ntheorem statements and proof terms use the namespace\n\\nolinkurl{FinalCollection.'+id+'}. The complete imported implementations\nand their shared mathematical dependencies are included in the collection.\nThe following local theorem names give the proof map:\n\n'
 out+='\\begin{multicols}{2}\\raggedright\\begin{itemize}\\setlength{\\itemsep}{2pt}\\setlength{\\parsep}{0pt}\n'
 for name in row['new_endpoints']:out+='\\item \\nolinkurl{'+name.split('.')[-1]+'}.\n'
 out+='\\end{itemize}\\end{multicols}\n\n'
 if len(row['implementation_modules'])>1:
  out+='The main implementation modules are\n\\begin{quote}\\raggedright\n'
  for module in row['implementation_modules']:out+=r'\noindent\nolinkurl{'+module+r'}\par'+'\n'
  out+='\\end{quote}\n'
 else:out+='The main implementation module is '+r'\nolinkurl{'+row['implementation_modules'][0]+'}.\n'
 if id in ['A389536','A378580','A378581','A393172']:
  out+='The project pins Lean 4.19.0 and Mathlib\n\\nolinkurl{c44e0c8ee63ca166450922a373c7409c5d26b00b}.\nThe supplied collection report records fresh source compilation and\ntransitive axiom audits. All coefficient conclusions are unbounded.\n\n'
 else:
  out+='The catalogue records the full original endpoint names and the new entry\ntheorems. The project pins Lean 4.19.0 and Mathlib revision\n\\nolinkurl{c44e0c8ee63ca166450922a373c7409c5d26b00b}. The collection\nreport records source recompilation and transitive axiom checks. Accepted\naxioms are propositional extensionality, classical choice, and quotient\nsoundness. All index conclusions above are unbounded; exact finite\ncoefficient checks in the package provide separate corroboration.\n\n'
 out+='\\paragraph{Limits and status.}\n'
 for q in row['qualifications']:
  if id=='A393172':q=q.replace('A(x-x^2)=x+A(x)^2', '$A(x-x^2)=x+A(x)^2$')
  if id=='A393171':q=q.replace('A=2C-x+4K', '$A=2C-x+4K$')
  if id=='A380056':q=q.replace('n![x^n]A', '$n![x^n]A$')
  out+=texescape(q)+'\n'
 if id in ['A389536','A378580','A378581','A393172']:
  out+='No global novelty, exclusive priority, peer review, or OEIS acceptance is asserted.\n\n'
 else:
  out+='The manuscript consolidates completed results; it does not assert global\nnovelty, exclusive priority, peer review, OEIS acceptance, or a new submission.\nStandard algebraic ingredients are not claimed as new discoveries.\n\n'
 cites=set(re.findall(r'\\cite\{([^}]+)\}',out));keys=set(k for x in cites for k in x.split(','))
 out+='\\begin{thebibliography}{9}\n\\raggedright\n'
 for other in sorted(META):
  _,_,otherkey,otherdate,_=META[other]
  if otherkey not in keys: continue
  out+='\\bibitem{'+otherkey+'}\nPaul D. Hanna, \\emph{OEIS '+other+'}, '+otherdate+'.\n\\url{https://oeis.org/'+other+'}. Retrieved 24 October 2026.\n'
 out+='\\end{thebibliography}\n\\end{document}\n'
 # Extraction must not retain references to a removed combined-paper table.
 assert 'tab:results' not in out and 'tab:scope' not in out,id
 labels=set(re.findall(r'\\label\{([^}]+)\}',out));refs=set(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',out))
 assert refs<=labels,(id,refs-labels)
 (ROOT/'manuscripts'/f'{id}.tex').write_text(out)
 print(id,len(out))
