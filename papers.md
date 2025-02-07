# Papers

## Semantics-Based Execution and the LLVM Backend of the K Framework Version 1.0

**Authors:** Pi Squared Inc.

**Date:** February 2025

### LaTeX Source

```latex
\documentclass{article}
\usepackage{url}
\usepackage{graphicx} 
\usepackage{listings,color,xcolor, nameref}
\usepackage{todonotes}
\usepackage{array}
\usepackage{booktabs}
\usepackage{hyperref}



\definecolor{kterminalred}{RGB}{188,46,47}
\definecolor{ksyntaxgreen}{RGB}{63,131,21}
\definecolor{ksyntaxblack}{RGB}{2,15,41}
\definecolor{kcomments}{RGB}{78,137,136}
\definecolor{verylightgray}{gray}{0.98}


\lstdefinelanguage{K}{
	keywords=[1]{ensures, priorities, require, requires, rule, claim, sort, syntax}, 
	keywordstyle=[1]\color{ksyntaxgreen}\bfseries,
	keywords=[2]{configuration, context, endmodule, imports, left, module, non-assoc, right, when}, 
	keywordstyle=[2]\color{ksyntaxblack}\bfseries,
	keywords=[3]{alias,alias-rec,anywhere,bracket,concrete,context,cool,freshGenerator,function,functional,heat,hook,hybrid,klabel,left,macro,macro-rec,memo,owise,priority,result,right,seqstrict,simplification,smtlib,strict,symbol,token,unboundVariables},	
	keywordstyle=[3]\color{ksyntaxblack}\bfseries,
	sensitive=false,
	comment=[l][\color{kcomments}]{//}, 
    morecomment=[s][\color{ksyntaxgreen}]{<}{>}, 
    identifierstyle=\color{blue}, 
	stringstyle=\color{kterminalred}\ttfamily, 
	morestring=[b]', 
	morestring=[b]"
}

\lstset{
	language=K,
	backgroundcolor=\color{white},
	extendedchars=true,
	basicstyle=\footnotesize\ttfamily,
	showstringspaces=false,
	showspaces=false,
	numbers=left,
	numberstyle=\footnotesize,
	numbersep=9pt,
	tabsize=2,
	breaklines=true,
	showtabs=false,
        linewidth=12cm,
	frame=single,
	frameround=tttt,
        literate={~} {$\sim$}{1}
}
\let\Bbbk\relax 
\usepackage{amsmath,amsthm,amssymb}
\allowdisplaybreaks
\usepackage{booktabs}
\usepackage{cleveref}
\usepackage{color}
\usepackage{mathtools}
\usepackage{natbib}
\setcitestyle{square, comma, numbers,sort&compress}
\usepackage{prftree}
\usepackage{subcaption}
\usepackage{scalerel}
\usepackage[normalem]{ulem} 
\usepackage{xspace}
\usepackage{multirow}
\usepackage[cache=false]{minted}
\usepackage[altpo,epsilon]{backnaur}
\usepackage{algorithm}
\usepackage{algpseudocode}
\usepackage{caption}
\usepackage{subcaption}
\usepackage{comment}
\usepackage{listings}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\newtheorem{remark}{Remark}[section]
\newtheorem{assumption}{Assumption}[section]

\newcommand{\xc}[1]{{\color{blue}XC: #1}}
\newcommand{\bc}[1]{{\color{orange}BC: #1}}
\newcommand{\gr}[1]{{\color{red}GR: #1}}
\newcommand{\zl}[1]{{\color{green}ZL: #1}}



\newcommand{\imp}{\to}
\newcommand{\K}{$\mathbb{K}$\xspace}
\newcommand{\KH}{Haskell-\K}
\newcommand{\KL}{LLVM-\K}
\newcommand{\KO}{OCaml-\K}
\newcommand{\as}{\textbf{ as }}
\newcommand{\mto}{\mapsto}
\newcommand{\requires}{\mathbin{\vartriangleleft}}
\newcommand{\oor}{\textbf{ or }}
\newcommand{\sd}{\cdot}
\newcommand{\mtc}{\preceq}
\newcommand{\nmtc}{\npreceq}
\newcommand{\vvp}{\vec{p}}
\newcommand{\vvv}{\vec{v}}
\newcommand{\vvrho}{\vec{\rho}}
\newcommand{\vvo}{\vec{o}}
\newcommand{\vvx}{\vec{x}}
\newcommand{\defeq}{=_{\text{def}}}
\newcommand{\rhobar}{\bar{\rho}}
\newcommand{\cS}{\mathcal{S}}
\newcommand{\cD}{\mathcal{D}}
\newcommand{\MatchingRow}{\mathsf{MatchingRow}}
\newcommand{\SortCategory}{\mathbf{SortCategory}}
\newcommand{\NormalSort}{\mathbf{NormalSort}}
\newcommand{\ListSort}{\mathbf{ListSort}}
\newcommand{\SetSort}{\mathbf{SetSort}}
\newcommand{\MapSort}{\mathbf{MapSort}}
\newcommand{\cln}{{:}}
\newcommand{\NN}{\mathbb{N}}
\newcommand{\eventually}{\diamond}
\newcommand{\cl}[2]{\left\langle #1 \right\rangle_{\texttt{#2}}}
\newcommand{\tts}{\texttt{s}}
\newcommand{\ttn}{\texttt{n}}
\newcommand{\ldot}{\ld}
\newcommand{\ld}{.\,}
\newcommand{\snext}{\bullet}
\newcommand{\inh}[1]{[\![#1]\!]}
\newcommand{\prule}[1]{(\textsc{#1})}
\newcommand{\CC}{\mathcal{C}}
\newcommand{\vs}{\mathit{sort}}
\newcommand{\FV}{\mathit{FV}}
\DeclarePairedDelimiter{\ceil}{\lceil}{\rceil}
\newcommand{\Unifier}{\mathit{Unif}}
\newcommand{\code}[1]{{\small \ttfamily #1}}
\newcommand{\kcode}[1]{\texttt{#1}}
\newcommand{\df}[1]{{\uline{#1}}}
\newcommand{\scat}[1]{$\langle$\textnormal{\textit{#1}}$\rangle$}
\newcommand{\vphl}{\varphi_{\mathit{left}}}
\newcommand{\vphr}{\varphi_{\mathit{right}}}
\newcommand{\To}{\Rightarrow}
\newcommand{\Cfg}{\mathit{Cfg}}
\newcommand{\wcln}{\,\cln\,}
\newcommand{\vph}{\varphi}
\newcommand{\OneStep}{\mathit{OneStep}}
\newcommand{\Sbt}{S_\mathrm{builtin}}
\newcommand{\Sur}{S_\mathrm{user}}
\newcommand{\st}[1]{\textit{#1}}
\newcommand{\ind}[1]{\textit{is}_{#1}}
\newcommand{\true}{\mathit{true}}
\newcommand{\false}{\textit{false}}
\newcommand{\Sreg}{S_\regrm}
\newcommand{\Slist}{S_\listrm}
\newcommand{\Sset}{S_\setrm}
\newcommand{\Smap}{S_\maprm}
\newcommand{\Pat}{\textsc{Pat}}
\newcommand{\LPat}{\textsc{LPat}}
\newcommand{\Val}{\textsc{Val}}
\newcommand{\CPat}{\textsc{CPat}}
\newcommand{\Occ}{\textsc{Occ}}
\newcommand{\sslash}{/\!/\ }
\newcommand{\vrho}{\varrho}
\newcommand{\act}{\mathit{act}}
\newcommand{\rl}{\mathit{rule}}
\newcommand{\Rules}{\textsc{Rules}}
\newcommand{\tbd}{\mathsf{tbd}}
\newcommand{\Act}{\textsc{Act}}
\newcommand{\CT}{C}
\newcommand{\ct}{c}
\newcommand{\tmax}{t_\text{max}}
\newcommand{\kmax}{k_\text{max}}
\newcommand{\lenmax}{\ftlenmax}
\newcommand{\ftlenmax}{\mathit{ftlen}_\text{max}}
\newcommand{\col}{\mathit{col}}
\newcommand{\vmap}{\mathit{vmap}}
\newcommand{\regrm}{\mathrm{regular}}
\newcommand{\listrm}{\mathrm{list}}
\newcommand{\setrm}{\mathrm{set}}
\newcommand{\maprm}{\mathrm{map}}
\newcommand{\Creg}{C_\regrm}
\newcommand{\Clist}{C_\listrm}
\newcommand{\rle}{\prec}
\newcommand{\vvpa}{\vvp_{<j}}
\newcommand{\vvpb}{\vvp_{>j}}
\newcommand{\IMP}{\textsf{IMP}\xspace}
\newcommand{\impk}{\code{imp.k}}
\newcommand{\LAMBDA}{\textsf{LAMBDA}\xspace}
\newcommand{\cell}[1]{\kcode{<#1/>}}
\newcommand{\phil}{\varphi_\mathit{lhs}}
\newcommand{\phir}{\varphi_\mathit{rhs}}
\newcommand{\phicfg}{\varphi_\mathit{cfg}}
\newcommand{\listcst}{\mathsf{Len}}
\newcommand{\emptymap}{\mathsf{Empty}}
\newcommand{\mapkey}{\mathsf{Key}}
\newcommand{\mapchoice}{\mathsf{Choice}}
\newcommand{\pr}[1]{\left\langle #1 \right\rangle}
\newcommand{\sol}{\mathsf{sol}}
\newcommand{\actb}{\mathsf{act}}
\newcommand{\condb}{\mathsf{cond}}
\newcommand{\lslen}{\mathsf{ranges}}
\newcommand{\PP}{\mathbb{P}}
\newcommand{\pp}[2]{\PP[#1,#2]}
\newcommand{\pprow}[1]{\PP[#1,*]}
\newcommand{\ppcol}[1]{\PP[*,#1]}
\newcommand{\prio}{\mathsf{priority}}
\newcommand{\front}{\mathsf{front}}
\newcommand{\tail}{\mathsf{tail}}
\newcommand{\mapp}{\vec{p_s} \mapsto \vec{q_s}}
\newcommand{\mappPrime}{\vec{p'_s} \mapsto \vec{q'_s}}
\newcommand{\bestkey}{\mathsf{BestKey}}
\newcommand{\block}{\texttt{block}\xspace}
\newcommand{\children}{\texttt{children}\xspace}
\newcommand{\blockheader}{\texttt{blockheader}\xspace}


\newcommand{\suc}{\mathit{succ}}
\newcommand{\Nat}{\mathit{Nat}}
\newcommand{\plus}{\mathit{plus}}
\newcommand{\mult}{\mathit{mult}}
\newcommand{\zero}{\mathit{zero}}
\newcommand{\one}{\mathit{one}}
\newcommand{\Sort}{\mathit{Sort}}
\newcommand{\Int}{\mathit{Int}}
\newcommand{\AExp}{\mathit{AExp}}
\newcommand{\BExp}{\mathit{BExp}}
\newcommand{\Stmt}{\mathit{Stmt}}
\newcommand{\Block}{\mathit{Block}}
\newcommand{\Id}{\mathit{Id}}
\newcommand{\Ids}{\mathit{Ids}}
\newcommand{\AExps}{\mathit{AExps}}
\newcommand{\Stmts}{\mathit{Stmts}}
\newcommand{\List}{\mathit{List}}
\newcommand{\iif}{\mathit{if}}
\newcommand{\while}{\mathit{while}}
\newcommand{\plusAExp}{\mathit{+_\AExp}}
\newcommand\scslash{\stretchrel*{$/$}{\textsc{e}}}
\newcommand{\divAExp}{\mathit{\scslash_\AExp}}
\newcommand{\cat}{\mathit{cat}}
\newcommand{\KVar}{\mathit{V}}
\newcommand{\DT}{\mathit{DT}}
\newcommand{\iswildcard}{\mathsf{isWildcard}}
\newcommand{\frontlen}{\mathit{frontlen}}
\newcommand{\taillen}{\mathit{taillen}}
\newcommand{\ot}{\mathit{ot}}
\newcommand{\cond}{\mathit{cond}}
\newcommand{\listsize}{\mathit{listsize}}
\newcommand{\cfg}{\mathit{cfg}}
\newcommand{\asp}[2]{#1 \; \mathtt{as} \; #2}

\newcommand{\ListItem}{\mathsf{ListItem}}
\newcommand{\SetItem}{\mathsf{SetItem}}
\newcommand{\MapItem}{\mathsf{MapItem}}
\newcommand{\sortList}{\mathsf{List}}
\newcommand{\sortMap}{\mathsf{Map}}
\newcommand{\sortSet}{\mathsf{Set}}
\newcommand{\siz}{\mathsf{size}}
\newcommand{\rem}{\mathsf{rem}}
\newcommand{\val}{\mathsf{val}}
\newcommand{\key}{\mathsf{key}}
\newcommand{\fsh}{\mathsf{fresh}}
\newcommand{\iter}{\mathsf{iter}}
\newcommand{\pat}{\mathsf{pat}}
\newcommand{\fail}{\mathsf{fail}}
\newcommand{\Match}{\mathsf{Match}}
\newcommand{\Compile}{\mathsf{Compile}}
\newcommand{\Leaf}{\mathsf{Leaf}}
\newcommand{\Success}{\mathsf{Success}}
\newcommand{\CheckNull}{\mathsf{CheckNull}}
\newcommand{\IterHasNext}{\mathsf{IterHasNext}}
\newcommand{\Fail}{\mathsf{Fail}}
\newcommand{\Switch}{\mathsf{Switch}}
\newcommand{\FunctionDT}{\mathsf{Function}}
\newcommand{\Pattern}{\mathsf{Pattern}}
\newcommand{\Eval}{\mathsf{Eval}}
\newcommand{\sfsum}{\mathsf{sum}}
\newcommand{\IMPPP}{\mathsf{IMP++}}
\newcommand{\llen}{\mathsf{length}}
\newcommand{\patsig}{\mathsf{patsig}}
\newcommand{\CompileRow}{\mathsf{CompileRow}}
\newcommand{\listlen}{\mathsf{listlen}}
\newcommand{\lhs}{\varphi_\textit{lhs}}
\newcommand{\rhs}{\varphi_\textit{rhs}}

\newcommand{\None}{None}

\algblockdefx{Case}{EndCase}
  [1]{\textbf{case} #1}
  {\textbf{end case}}
\newcommand{\CaseItem}[2]{\State #1 $ \to $ #2}
\newcommand{\ret}{\textbf{return}\xspace}

\algdef{SE}[SUBALG]{Indent}{EndIndent}{}{\algorithmicend\ }
\algtext*{Indent}
\algtext*{EndIndent}

\bibliographystyle{ACM-Reference-Format}
\setcitestyle{numbers}

\title{Semantics-Based Execution and the LLVM Backend of the \K Framework\\\Large Version 1.0}
\author{Pi Squared Inc.}
\date{February 2025}


\begin{document}

\maketitle

{\parbox{0.86\textwidth}{\small\em 
It is suggested that the reader first read ``The Pi Squared Whitepaper''~\cite{pi2paper}.
}}



\begin{abstract}
The \K framework is a semantics-based approach to language design and implementation. From a single definition of a language's syntax and operational semantics, a full set of tools can be extracted automatically, including a \emph{concrete interpreter} for programs in that language. In this paper, we identify the most critical performance bottleneck for such interpreters: compiling fast decision trees for a subset of associative-commutative pattern-matching problems. We demonstrate a decision tree-based compilation algorithm that substantially extends existing methods with support for fast runtime collection data structures. We show that LLVM-based interpreters generated by \K perform comparably to ones written by hand for interpreted languages such as EVM and are practical for real-world adoption.  Moreover, we show that optimizations that are only possible in the presence of a formal language semantics make Compositional Symbolic Execution (CSE), in fact, outperform manually-written language implementations.  Automatically generating efficient and correct-by-construction language implementations from formal semantics is the holy grail of the programming language field; after more than two decades of sustained innovation and engineering, \K is proudly almost there.
\end{abstract}

\newpage 

\renewcommand{\contentsname}{Table of Contents}
\tableofcontents

\newpage

\section{Introduction}
\begin{figure}[t]
  \centering
  \includegraphics[width=\columnwidth]{figs/k-vision-v3.png}
  \caption{
    The central vision of the \K Framework: from one formal definition of
    a language's semantics, a full suite of important tooling can be derived
    automatically.
  }
  \label{fig:k-vision}
\end{figure}

The \K framework~\cite{RS10} is a semantic framework that allows language
designers to automatically and generically derive a full suite of tools from a
single formal specification of their language. For example, \K can generate a
parser, interpreter and symbolic deductive verifier~\cite{SPY+16} from this
specification.
The
language-generic approach used by \K is scalable; many real-world programming
languages have been formalized in \K, including C~\cite{ECR12},
Java~\cite{BR15}, JavaScript~\cite{Park2015}, Python~\cite{Guth2013},
Rust~\cite{Wang2018}, x86-64~\cite{Dasgupta2019}, the Ethereum virtual
machine~\cite{HSZ+18}, and LLVM IR~\cite{Li2020}. The implementations obtained
are suitable for commercial applications \cite{GHSR16, firefly}. 


For a programming language $L$, the \K definition of $L$ consists of (1) the
concrete syntax of $L$, as a conventional BNF grammar; (2) the state maintained
by each program in $L$ during execution (its \emph{configuration}); and (3) the
operational semantics of $L$ given as a set of rewrite rules. A rewrite rule
$\lhs \To \rhs$ specifies a transition relation over configurations; any
configuration that matches the pattern $\lhs$ can be rewritten into the
configuration $\rhs$. The \K compiler transforms rules that act on local
fragments of a configuration into efficient top-level rewrites of the entire
configuration.

A language-agnostic concrete interpreter is one of the most important tools that
\K provides. From a \K definition of a language $L$, the \K compiler generates
an interpreter for programs in $L$. It takes as input any configuration $\gamma$
of $L$, and looks for a rewrite rule whose left-hand side is matched by
$\gamma$. If such a rewrite rule exists, the interpreter applies it to $\gamma$
and obtains a new configuration $\gamma'$ as specified by the right-hand side of
the rule. Execution proceeds by repeatedly applying this process until no
rewrite rules apply, in which case the execution terminates.



In this paper we present \KL: a language-agnostic implementation strategy for \K
concrete interpreters, where the pattern matching and rule application
components of a \K language definition are compiled to efficient native code via
LLVM IR~\cite{Lattner2004}.

Much of the work done by a \K concrete interpreter is \emph{pattern matching},
where terms in \K's internal term representation (KORE\cite{kore-github}) are matched against
patterns in order to bind variables in rewrite rules. This is a well-studied
problem, with solutions implemented by every mainstream functional programming
language.

An initial version of the \K compiler (\KO) generated OCaml code for
each \K pattern, and relied on the OCaml compiler to provide efficient pattern
matching. However, this approach failed to scale: the terms generated by \K
triggered pessimal behavior in the OCaml compiler, leading to either impractical
compilation times, or slow execution. A specialized
pattern matching compiler for \K was therefore required.


The primary contribution of this paper is an algorithm for compiling \K pattern
matching problems to efficient native code. This algorithm originates in the
canonical work of \citet{Maranget2008}, but is substantially extended with
features specific to \K; we define pattern matching for collection data types
(lists, maps, and sets) and pattern matching for conditional rewrite rules.
The algorithms presented in this paper are instantiated in our implementation of
\KL \cite{anonymous_2022_7298780}, which significantly outperformed \KO.



We evaluated the performance of \KL interpreters in two contexts: Comparing the \K implementation of EVM, {\K}EVM, with the Go implementation of EVM, Geth, using the Ethereum test suite \cite{ethereum-tests} and evaluating both EVM implementations against the Solidity interpreter generated by \KL with and without CSE optimization in a program that executes a thousand swap operations from the UniSwap V2 contract \cite{Adams2020UniswapVC}. The first evaluation shows that we have some room to outperform Geth, but that {\K}EVM without any CSE is already performance-wise comparable with the most used EVM implementation around. The second experiment proved that a language-specific interpreter generated by \KL can outperform Geth, being 57\
.   
The structure of this paper is as follows. First, in \Cref{sec:related}, we
review relevant related work in pattern matching compilation and term rewriting
engines. Then, to contextualize the rest of the paper,  \Cref{sec:imp} gives a
brief overview of a \K semantics.
\Cref{sec:overview} gives a high-level overview of \KL. \Cref{sec:k-llvm,sec:decomp,sec:compile,sec:heuristics} detail the algorithms
and technical contributions of \KL, which are evaluated in \Cref{sec:eval}.










\begin{comment}
\subsection{PL Design \& Implementation: State of the Art}

\bc{
  I'd rephrase the use of SotA here - we're arguing that our approach is SotA;
  things like GCC etc. are rather the accepted hegemony that we can improve on.

  Perhaps ``informal'' is better phrased as non-mechanised?
}

The state of the art in programming language design is to develop the 
implementations, tools, and documentations for each individual language, 
\emph{separately}. 
For example, the C programming language has well-known compilers like
gcc \cite{gcc} and clang \cite{clang},
but there are many other C tools.
For example, there are C interpreters such as TrustInSoft \cite{trustinsoft}
that target at detecting undefined behaviors of C programs,
C model checkers such as CBMC \cite{KT14} that aim at 
exploring the state space of C programs, and
C verifiers such as VCC \cite{CDH+09a} that use symbolic reasoning
to formally prove properties of C programs.
C also has informal documentations such as C99, C11, and C18, which are 
manually reviewed by a language committee. 
We summarize the above scenario in \Cref{fig:C-tools}. 

\bc{
  We don't need all of these figures. I'd keep the standard K octopus and drop
  the other two.
}

\begin{figure}
\includegraphics[width=0.6\columnwidth]{figs/C-tools.png}
\caption{C tools are developed separately.}
\label{fig:C-tools}
\end{figure}

Regarding \Cref{fig:C-tools}, several concerns arise naturally:
\begin{enumerate}
\item Language tools are developed in an ad-hoc way. Language developers and 
program analysis experts rely on their informal understanding of the
language to develop the tools, which may not be consistent across different 
tools or different versions of the same tool. 
\item Languages standards are informal. Therefore, there is no means to 
formally prove a tool is consistent with the standards. In fact, many are not 
\citep{todo}. 
\item Language tools are often developed from scratch and share very little code
or functionality with each other, which cause a waste of resource and duplicate 
efforts in ``re-inventing the wheels''.
\item Language tools need be updated when a new language standard is published. 
In other words, they are inclined to become deprecated.
\end{enumerate}


\begin{figure}[t]
\centering
\includegraphics[width=0.6\columnwidth]{figs/LT.png}
\caption{State of the art in programming language design.}
\label{fig:PL-design}
\end{figure}

The above scenario unfolded for various programming languages over and over
again for more than 50 years.
And it is still going on, as shown in \Cref{fig:PL-design}.
If we have $L$ programming languages and $T$ tools, then we need
to develop and maintain at least $L \times T$ systems that share little code
or functionality.
This costs a waste of talent and resources in doing essentially
the same thing in developing the same tools but for different languages.

In conclusion, the state-of-the-art programming language design
generates language implementations and tools,
some of which we use to ensure the correctness, reliability, and security of 
programs and software systems written in that language,
which may be unreliable themselves.
\end{comment}

\begin{comment}
\subsection{An Ideal Language Framework}
\label{sec:ideal}

\bc{
  I think given the space available we could tone down this section - we aren't
  trying to sell the grand unified vision of K; rather, we have a tool for
  which previous implementations suffered from performance issues. We can still
  say what K does and why that's important
}

We hold a vision of an ideal language framework that makes programming language 
design a more organized and scientifically principled process,
reduces duplicated work in tool development, 
increases the reusability and reliability of analysis tools,
and increases the reliability and security of
the execution, verification, and testing environments of computer programs.

In an ideal language semantic framework, all languages must be rigorously 
designed using formal methods, and implementations of language tools must be 
provably correct with respect to the formal language semantics. 
As shown in \Cref{fig:k-vision},
once the formal language definition of a given (but arbitrary) programming 
language is given, the ideal framework generates all the tools for that language
including parsers, interpreters, compilers, state-space explorers, model 
checkers, deductive program verifiers, etc..
All language tools are directly derived from the reference formal language 
definition by the ideal framework.

The ideal framework has the following characteristics:
\begin{itemize}
\item The framework is \emph{language-independent}, in the sense that
it uses the same generic method to generate language tools from the formal
language definitions, for all programming languages.
\item The framework should be \emph{expressive}, to define the formal syntax
and
semantics of any programming language, with an intuitive and user-friendly
\emph{frontend interface}, so the formal definitions can be understood not only
by experts but also by non-semanticists.
\item The framework should support \emph{modular development}, where formal
definitions of large languages can be divided into smaller and more primitive
modules. Language features should be loosely coupled, and language designers
can easily add new features without revisiting existing definitions.
\item The framework should support \emph{testing-driven development}, where
basic language tools such as the parser and the interpreter and/or compiler
are automatically generated from language definitions
for language designers to execute and test the semantics while they are
defining it, by running lots of test programs and see if they get the intended
results.
\item \bc{We don't talk about proving or the Haskell backend, so these items
  should get cut or be de-emphasised}. The framework should have a mathematically solid logical foundation, in
the sense that every semantic definition yields a \emph{logical theory} of
a foundational logic (see Section~\ref{sec:MmL}) and all language tools are
best-effort implementations of logical reasoning of the foundational logic
within the given logical theory.
\item The framework should have a \emph{minimal trustbase} that is fully
comprehensible and accessible to users.
The framework should provide \emph{proof objects} as correctness certificates
for all tasks it does. Proof objects can be mechanically and quickly checked
by third-party proof checkers, so their correctness can not be compromised.
\end{itemize}
\end{comment}

\begin{comment}

\subsection{\K Framework}

{\K framework} (\url{http://kframework.org}) is an effort in pursuing and
realizing the ideal language framework. 
\K is a rewrite-based executable semantic framework where programming 
languages, type systems and formal analysis tools can be defined using 
configurations, computations and rules. Configurations organize the state in 
units called cells, which are labeled and can be nested. Computations carry 
computational meaning as special nested list structures sequentializing 
computational tasks, such as fragments of program. Computations extend the 
original language abstract syntax. K (rewrite) rules make it explicit which 
parts of the term they read-only, write-only, read-write, or do not care about. 
This makes K suitable for defining truly concurrent languages even in the 
presence of sharing. Computations are like any other terms in a rewriting 
environment: they can be matched, moved from one place to another, modified, or 
deleted. This makes K suitable for defining control-intensive features such as 
abrupt termination, exceptions or call/cc.

\bc{
  This can be shrunk down to one paragraph, I think. It's impressive that we can
  do all this but we probably don't need a full page of it (and there are some
  claims like Rust being blazingly fast that are a bit unsubstantial for our
  purposes).

  Also, similarly to my point above, I think that it might be worth explaining
  how the other backends worked wrt. pattern-matching, and why those
  implementations ran into performance issues.
}

The first \K backend was implemented in Maude \cite{todo}. 
Since then, it has been re-implemented in Coq, OCaml, and Java, with new 
features constantly added. 
In the following, we list a few important milestones of \K's practical 
application:
\begin{enumerate}
\item \textbf{C}. A complete formal semantics of C was defined 
in \cite{undefinedness-c}
that aims at capturing all the undefined behaviors.
This semantics powers the commercial RV-Match tool \cite{rv-match},
developed and maintained by Runtime Verification Inc. (RV) 
founded by the second author,
aiming at mathematically rigorous 
dynamic checking of C programs in compliance with the ISO C11 Standard. 
\item \textbf{Java}. A complete formal semantics of Java was defined 
in \cite{java-semantics}
that covers all language features and is
extensively tested on a test suite developed
in parallel with the semantics
in a test-driven manner;
the test suite itself was an important outcome 
because at the time Java appeared to have no publicly 
 conformance test suite.
\item \textbf{JavaScript}. A complete formal semantics of JavaScript was 
defined in \cite{kjs} and 
thoroughly tested on the ECMAScript~5.1 conformance test 
suite \cite{ecma2011262}.
Among the existing JavaScript
implementations at that time, only Chrome V8's passed all the 
tests. In addition to a reference implementation of JavaScript, the 
formal semantics also yields 
a coverage metric for test suites,
that is the set of \emph{semantic rules} it exercises
(see Section~\ref{sec:imp++_semantics}). 
It turned out that the ECMAScript 5.1 test suite was incomplete because it 
missed some semantic rules. 
By writing new tests to exercise those rules,
we found bugs in production JavaScript engines like 
Chrome V8, Safari WebKit, and Firefox SpiderMonkey. 
\item \textbf{Python}.
Defining the formal semantics of Python~3.2 is one of the first efforts
to demonstrate \K's scalability \cite{python-semantics}.
The semantics yields an interpreter and 
tools for state space exploration, static reasoning,
and formal verification. 
The semantics was thoroughly tested and was 
shown to perform as efficiently as CPython \cite{cpython}, which is the 
reference implementation of Python.
\item \textbf{Rust} .
As an emerging system programming language, Rust runs blazingly fast, prevents 
segfaults, and guarantees thread safety,
by providing a set of safe constructors and an ownership 
mechanism \cite{rust}. Nevertheless, a formal semantics is still needed 
in order to formally verify Rust programs. 
There are two parallel efforts to define the formal semantics of Rust in 
\K \cite{krust-shanghai,krust-singapore}, both of which have completely 
formalized the safe constructs and carried out experiments
on symbolic execution and formal verification.
\item \textbf{x86-64}.
Low-level languages such as assembly languages can also be formalized in \K. 
A formal semantics of x86-64 is defined in \cite{DPK+19},
 which formalizes all the non-deprecated, sequential 
user-level instructions of the x86-64 Haswell instruction set architecture,
including 3,155 instruction variants that correspond to 774 mnemonics. 
The semantics is fully executable and has been experimented on more than 7,000 
instruction-level test cases and the GCC torture test suite.
The experiment revealed bugs in the x86-64 reference manual and also other 
existing semantics. 
The formal semantics can be used for formal analysis such as processor 
verification.
\item \textbf{Ethereum Virtual Machine (EVM)}.
EVM is a bytecode stack-based language which
all smart contracts on the Ethereum blockchain are compiled to and then 
executed by EVM interpreters \cite{wood2014ethereum}.
A complete formal semantics of EVM, called KEVM, is defined in \cite{kevm},
whose correctness and performance 
are tests on over 40,000 EVM programs
in the the official Ethereum test suite.
\item \textbf{IELE}. 
As an alternative to EVM,  
IELE \cite{iele} is a \emph{verification friendly} virtual machine language
that has significantly different language features from EVM
such as a {register-based} architecture, 
unbounded, arbitrarily-large integer arithmetic, 
a simplified gas model design. 
IELE was designed and implemented in a \emph{semantic-driven} manner,  
whose virtual machine  was automatically generated from its formal semantics,
making it the first virtual machine whose development and implementation
were completely powered by formal methods.
\end{enumerate}
\end{comment}

\begin{comment}
\subsection{Challenges and Contributions}

\bc{
  This needs reworking to not mention the Haskell backend, or to mention and
  then immediately discharge it.
}

There have been two main challenges with the existing \K implementations:
performance and the ability to carry out complex symbolic analysis based on 
formal semantics. 
In terms of performance, the \K-generated language interpreters were much 
slower than the interpreters written by humans. 
In terms of the ability to carry out symbolic analysis, the previous \K 
implementations \cite{oopsla16} only considered deductive program verification,
but not other types of formal analysis. 

In this work, we solve the first challenge by implementing a new backend based 
on LLVM, denoted \KL. 
\KL uses innovative algorithms for pattern matching and substitution and 
improve the performance of program execution by several orders of magnitude. 
Our experiments show that \KL generates interpreters that are \emph{faster}
than hand-written interpreters for real languages, marking one of the most 
important milestone.

The second challenge is a small foundation for symbolic reasoning of language 
properties. 
Previously, symbolic reasoning in \K backends is implemented in an ad-hoc way. 
In this work, we propose a new \K backend, \KH, that provides a set of symbolic 
reasoning APIs and use them to implement all formal analysis, including 
deductive program verifiers and bounded model checkers. 
content...
\end{comment}


\section{Related Work} \label{sec:related}
\subsection{Semantic Frameworks}

There exist many semantic frameworks that allow the extraction of semantic tools
from a formal definition of a programming language. Early work on
\textsc{Centaur} \cite{BCD+88} compiled a \textsc{typol} \cite{Despeyroux1988}
definition of a language's natural semantics to Prolog rules; these rules could
then be queried by interactive tools such as a pretty-printer or interpreter.
Even in this early work, the authors identify the performance of the underlying
rule engine as a limitation of their approach, and suggest a specialized
compiler for their Prolog rules as a potential solution.

The \textsc{Spoofax} workbench collects a set of domain-specific languages and
tools for designing and implementing programming languages: SDF \cite{Vis97} for
syntax descriptions and parser generation, Stratego \cite{VBT98} for dynamic
semantics and execution strategies, and FlowSpec \cite{SV17} for data-flow
analysis. 

Similarly, tools developed in other workbenches such as PLT Redex \cite{FFF09}
also rely on the performance of an underlying language or runtime environment
(here, Racket). This points to performant concrete execution and interpretation
as a shared point of difficulty for language workbenches.


















\subsection{Rewrite Engines}

The concrete execution strategy used by \KL has its roots in the \emph{term rewriting} literature. 
\textsc{Maude} \cite{Clavel2007} is a rewrite engine based on order-sorted
membership equational logic \cite{membership-algebra}.
It is a high-performance system for specifying formal and computational systems, especially concurrent applications.  
A key feature of \textsc{Maude} is its built-in unification algorithms that apply modulo
ACUI axioms\footnote{Associativity, Commutativity, Unit and Idempotence.}.
This ACUI reasoning capability is further improved by variant-based unification
\cite{variant-based-narrowing}. 

\textsc{ASF+SDF} \cite{asf-sdf} is a general-purpose specification framework
based on algebraic specifications. 
It has been used to define the syntax and formal semantics of programming languages, program transformations, and language transformations. 
An ASF+SDF definition consists of two parts. The ASF (algebraic specification formalism)
part specifies the formal semantics in terms of conditional rewrite rules.
The SDF (syntax definition formalism) defines the concrete syntax of the target language. 
ASF+SDF supports both interpretation and compilation of the rewrite rules. 
The ASF2C compiler generates efficient C code that implements pattern matching and term traversal. 

As part of its suite of tools, \textsc{Spoofax} \cite{spoofax} provides a
term rewriting module that
allows programmable rewriting strategies, permitting context-sensitive transformations. 
Interpreters generated from a Spoofax definition rely on the Truffle
\cite{Wurthinger2017} infrastructure to perform just-in-time specialization and
compilation; this approach is more complex than \K's pure term-rewriting
approach, and relies on a Java virtual machine rather than compiling to native
code.


\subsection{Pattern Matching Compilation}

Much of the work in this paper deals with the compilation of pattern matching,
one of the first accounts of which is given by \citet{Cardelli1984} in the
context of an ML compiler; the subsequent work discussed in this section deals
exclusively with similar ML-style patterns. The fundamental problem of
\emph{ordering} is introduced here: how should the compiler decide the order in
which to address the sub-components of a pattern matching problem to produce
efficient code?

As well as the ordering of sub-problems, generating efficient code from these
structures is addressed by \citet{Augustsson1985}, who demonstrates an approach
based on backtracking automata. That is, it is possible for the code they
generate to proceed down an infeasible path, then be forced to re-examine part
of the term being scrutinized. While doing so is clearly suboptimal, it is
possible to ameliorate the performance impact of doing so through carefully
chosen optimizations \cite{LeFessant2001}.

The potential for backtracking can be avoided entirely by compiling pattern
matching to decision trees (DAG-like structures with internal sharing)
\cite{Maranget2008}; doing so can potentially produce larger code, but in
practice performs comparably to the backtracking approach. In this paper, the \K
compiler compiles to decision trees, and so much of the notation and terminology
used is shared with \citet{Maranget2008}. Almost all pattern matching compilers
perform some variant of decision tree compilation; the underlying approach is
flexible enough to be adapted to contexts such as extensible languages
\cite{Tobin-Hochstadt2011}, analysis of complex functional programming features
\cite{Karachalias2015}, and dependently-typed languages \cite{Cockx2016}.

\section{A Running Example of \K} \label{sec:imp}
In this section, to provide context for the rest of the paper, we show a \K
definition of \IMP; a minimal, prototypical imperative language. \IMP has
arithmetic and boolean expressions, assignment statements, conditional
statements, loops, and sequential composition of statements.
\lstinputlisting[language=K,
    numbers=none,
    frame=none,
    basicstyle=\footnotesize,
    label={fig:k-imp-syntax},
    caption={ Syntax module of the \K definition of \IMP, a simple imperative programming language. Syntax is defined as a familiar BNF grammar.}
    ]{code/imp-syntax.k}


\lstinputlisting[language=K,numbers=none,frame=none,basicstyle=\footnotesize, label={fig:k-imp-defintion}, caption={\K definition of the semantics of \IMP. These semantics are defined by a set of rewrite rules that transform \IMP syntax,  and eventually lower it into \K's standard library domains.}]{code/imp.k}


\subsection{\IMP Syntax Definition}

The \K definition of \IMP is shown in \Cref{fig:k-imp-syntax} and \Cref{fig:k-imp-defintion}. It consists of two
modules: \kcode{IMP-SYNTAX} that defines the formal syntax of \IMP, and
\kcode{IMP} that defines the operational semantics of \IMP using \K rewrite
rules. \K syntax definitions are BNF grammars, with terminals represented by
double-quoted strings (e.g.\ \kcode{"if"}, \kcode{"while"}), and non-terminals by
capitalized words (e.g.\ \kcode{AExp}, \kcode{Int}, \kcode{Id}). Each syntax
definition can be associated with attributes in square brackets; these
attributes encode additional syntactic and semantic information. For example,
\kcode{[left]} denotes left-associativity, while \kcode{[strict]} means that the
production has a strict evaluation order: \kcode{E1 + E2} is evaluated by first
evaluating \kcode{E1} and \kcode{E2}, and only then evaluating the addition
operation. \kcode{if (B) S1 else S2} has attribute \kcode{[strict(1)]}, so only
the condition \kcode{B} is evaluated before the top-level term. As you can see, strict attribute uses a 1-based indexing approach.

\subsection{\IMP Semantics Definition}


The module \kcode{IMP} defines the configurations and formal semantics
of \IMP.

\subsubsection{Configurations}

A configuration is a snapshot of a complete state of a machine that runs \IMP,
including the program being executed and any additional information required. We
organize this information into XML-like cells, which can be nested. An \IMP
configuration has two important cells: the \cell{k} cell contains the current
computation, and the \cell{state} cell contains a mapping from \IMP variables to
their values.\footnote{For clarity, we nest both of these inside a \cell{T} cell
  explicitly; this top-level cell is usually inserted implicitly by the
compiler.} Complex languages have many more cells than this; for example, \K
configurations for C \cite{ECR12} have more than 120 cells.

\subsubsection{Rewrite Rules}

\K uses rewrite rules to define the formal operational semantics of \IMP; in
\Cref{fig:k-imp-defintion}, rules are declared by the keyword \code{rule}. The most basic
\K rules have the form \kcode{LHS => RHS}, meaning that for any term matching
the \K pattern \kcode{LHS}, we can rewrite it to \kcode{RHS}.

For example, the semantics of the while loop in \IMP is defined by rewriting:
\begin{lstlisting}[language=K,numbers=none,frame=none,basicstyle=\footnotesize]
while B { S } => if B { S while B { S } } else { }
\end{lstlisting}
That is, the rewrite rule unfolds a single iteration of the loop.


\subsubsection{The \K Frontend}

As well as matching and rewriting a single term in the current computation
(i.e.\ the \cell{k} cell), \K supports more advanced rules that locally rewrite
the configuration. For example, consider the rule for variable lookup in an \IMP
program (where \kcode{X |-> I} means ``\kcode{X} maps to \kcode{I}'' in the
\cell{state} cell):
\begin{lstlisting}[language=K,numbers=none,frame=none,basicstyle=\footnotesize]
<k>     X:Id => I ...</k>
<state> X |-> I   ...</state>
\end{lstlisting}

Here, the rewrite arrow occurs \emph{inside} the \cell{k} cell. The \K compiler
frontend performs a series of de-sugaring transformations to lift this rule into
a more consistent (but less convenient to read and write) top-level rewrite. The
ellipses at the end of cell patterns are replaced by explicit patterns, and the
top-level \cell{T} cell is made explicit. Additionally, the entire configuration
is repeated:
\begin{lstlisting}[language=K,numbers=none,frame=none,basicstyle=\footnotesize]
<T>                                        
  <k> X:Id ~> REST-K </k>
  <state> X |-> I REST-STATE </state>
</T>                                       
                    =>
<T>                                        
  <k> I ~> REST-K </k>
  <state> X |-> I REST-STATE </state>
</T>                                       
\end{lstlisting}

These transformations make it convenient to write \K code, while also inducing a
conceptually simple internal structure for \K definitions. Internally to \K,
configuration cells are themselves just terms in an extended language syntax.
This means that a top-level configuration rewriting rule as above is simply a
single large pattern-matching and rewriting problem; it is therefore intuitive
why pattern matching must be made as efficient as possible in a \KL interpreter.
Further discussion of the user-level \K language is out of the scope of this
paper, which is concerned only with the internal details of how a \K
pattern-matching problem should be compiled and the efficiency of our approach in real-world applications.  The readers interested in learning \K are encouraged to start with the \href{https://kframework.org}{\K Tutorial}.




















\section{\KL Backend: A High-Level Overview} \label{sec:overview}
In this section, we give a high-level overview of \KL. We will detail its various subsystems and the ways in which they interact to create the semantic-based compiler that is \KL.

\KL does not operate directly on K definitions. Rather, it operates on KORE~\cite{kore-github}, a simplified internal representation of \K. This KORE definition is produced by the \K frontend and can be compiled by the \KL backend into a native interpreter binary that efficiently implements the rewrite system specified by that definition. Alternatively, the KORE definition can be compiled into a dynamic or static library that provides similar rewriting functionalities. 

\KL comprises the following subsystems and data structures:

\begin{itemize}
    \item \textbf{KORE AST data structures:} Data structures that represent the KORE AST in memory.
    \item \textbf{Decision tree data structures and generator:} Data structures representing decision trees used for pattern matching purposes and a generator that converts KORE ASTs to decision trees.
    \item \textbf{Runtime terms:} Data structures representing KORE terms during execution.
    \item \textbf{Code generator:} The main compiler that translates decision trees into an interpreter that can rewrite KORE terms according to the given KORE definition.
    \item \textbf{Runtime library:} Libraries and hooks implemented in C/C++ and LLVM IR that are linked with the generated interpreter to provide perfor-mance-focused runtime utilities.
    \item \textbf{Memory management and garbage collector:} Memory allocator and garbage collector for runtime terms.
\end{itemize}

In the following subsections, we give more details on each of the above items.


\subsection{KORE ASTs}
The input to the \KL backend is a KORE definition~\cite{kore-github}, which is an internal representation of a \K semantic definition, produced by the \K frontend. A KORE definition (similarly to a \K definition) contains sort and symbol declarations, as well as various axioms on terms constructed by said symbols, including axioms that specify rewriting a term that matches a specific pattern to another term. For a formal definition of the syntax of a KORE definition, see~\cite{kore-syntax}.

The KORE AST is represented internally in the backend by a collection of C++ data structures that include classes for KORE definitions, axioms, patterns, sorts, symbols, etc.

The KORE data structures guide the compilation of the KORE definition into a decision tree that implements pattern matching to select which rewrite rule to apply to a given term. They also guide the code generation that implements the said rewrites, i.e. the generation of code that rewrites a given term to a new one according to a rewrite rule that matched. As such, they provide the following important functionalities:
\begin{itemize}
    \item The data structures form an abstract syntax tree (AST) that can be traversed for the purposes of decision tree and code generation. For example, a KORE definition data structure points to the various sort and symbol declarations it contains, as well as the various axioms that represent top-level and function rewrite rules. A KORE pattern data structure points to the KORE symbol data structure for the constructor of the pattern, as well as to other KORE pattern data structures for the arguments of the constructor symbol.
    \item Parsing from textual KORE and outputting as textual KORE.
    \item Serialization and deserialization into two different binary formats, one that focuses on optimizing storage size for large KORE terms, and another that focuses on optimizing serialization/deserialization times.
    \item A mapping between KORE symbols and arithmetic tags, that will be useful for translating said symbols into the more efficient runtime term representation.
    \item Various utilities such as hashing, applying a substitution into a term, expanding macros, etc.
\end{itemize}

The \KL backend compiler walks a given KORE definition and generates a decision tree that can be used to pattern-match any given term of said definition and choose a corresponding rewrite rule from that definition to apply. The compiler does that for the top-level KORE definition as well as for all functions in that definition. Note that both K top-level rules and function rules correspond to KORE axioms.


\subsection{Decision Trees and Pattern Matching}
The compiler of the \KL backend needs to generate code that, for any given term that is well-formed according to a KORE definition, selects a rewrite rule from said definition that matches the term. Rewrite rules comprise a pattern (also known as the left-hand side of the rule) and a rewrite term (also known as the right-hand side of the rule). The pattern is a KORE term that contains variables and can be matched against a given concrete KORE term. The rewrite term is also a KORE term that contains the same variables found in the pattern. In the process of matching, the variables of the pattern are given concrete values according to the sub-terms of the concrete term that they matched. This mapping from pattern variables to concrete terms is called a substitution. After the pattern has been matched and we have a substitution, we can rewrite the given concrete term into the rewrite term of the matched rule by applying the substitution to the rewrite terms to get a new concrete term.

The pattern matching code generated by the compiler needs to handle large KORE definitions with potentially thousands of rewrite rules to select from. The code should do that in the most efficient way possible in terms of both code size and number of branches. Pattern matching is a common and well-studied problem for compilers of functional languages. In the \KL backend, we employ a modified version of an existing published algorithm for code generation of efficient pattern matching, described in~\cite{Maranget2008}. The algorithm represents the patterns of the left-hand side of rewrite rules as matrices, and processes these matrices into a decision tree data structure: Starting from the root of the tree, each node is a check on a specific position of the given term and the children of the node represent how to continue checking given the result of the parent’s check. A leaf node corresponds to a specific rewrite rule that matches when the leaf node is reached through a series of checks on the given term. The algorithm is designed to be customized with various heuristics in order to lead to generation of decision trees that minimize the number of checks needed to match a given term.

As mentioned, the \KL backend uses a modified version of the algorithm. There are two main modifications in our pattern matching algorithm:
\begin{itemize}
    \item New heuristics that we have found lead to better decision trees for the kinds of patterns found in KORE definitions.
    \item New types of internal decision tree nodes to represent functionality specifically found in KORE term patterns that are not covered by the patterns considered by the original algorithm, e.g. patterns that match an element of a set, or the i-th element of a list.
\end{itemize}
Our modifications to the pattern matching algorithm are documented in detail in \Cref{sec:k-llvm,sec:decomp,sec:compile,sec:heuristics}.



\subsection{Runtime Term Representation}
The KORE AST terms contain a lot of information that is not needed during execution and are therefore not ideal to use at runtime. Rather, the \KL backend uses \block as the common data structure to represent KORE symbol terms at runtime. The \block datatype is defined as:

\begin{lstlisting}[language=C++, numbers=none,frame=none]
using block = struct block {
  blockheader h;
  uint64_t *children[];
};
\end{lstlisting}

The \children field contains data that points to children of this block, i.e. the arguments of the KORE symbol that corresponds to this block. These can be other block pointers or any of the native runtime types described below.


The \blockheader is a struct containing only one 64-bit value that we use to encode all metadata related to the block. That includes its size, layout, and tag:
\begin{itemize}
    \item The size metadata contains the size of the block, in words.
    \item The layout metadata is an index to the layout table (generated by the code generator). The layout table contains information about the layout of the block, such as the number of children for this block, the offset in bytes from the start of the block where we can find the data related to each child, as well as whether each child is another block or one of the native runtime types.
    \item The tag metadata is a unique identifier for the symbol that is used instead of the symbol name during runtime, because comparing integers is more efficient than comparing strings.
    \item There are also a number of bits in the blockheader that provide metadata related to the memory management system and the garbage collector.
\end{itemize}

The \KL backend implements some KORE sorts as native types rather than regular blocks in order to be able to hook builtin functionality that should be available for these sorts into native C++ libraries that give significant performance benefits. The following sorts have their own implementation on the backend: machine integers, arbitrary precision integers, floating point numbers, strings and bytestrings, and collection sorts (maps, sets, lists, and rangemaps).


\subsection{Code Generation and Rewriting} \label{sec:codegen-overview}
The code generator is responsible for generating code that implements the pattern matching as directed by the decision tree, as well as the rewriting that should occur when a leaf node is reached in the tree, which corresponds to a rewrite rule. The main loop of execution is as follows:
\begin{enumerate}
    \item Given a KORE term, walk the decision tree to reach a leaf node.
    \item Apply the rewrite rule that corresponds to the reached node to the KORE term.
    \item Repeat for the new KORE term we get after applying the rewrite rule.
\end{enumerate}
The execution terminates if, in step 1, we fail to find a match, i.e. we end up in a special node of the decision tree that represents a pattern matching failure.

Before we start the execution loop, we need code that converts the input KORE term, which was parsed as a KORE data structure, into a Runtime Term. The code generator generates a variety of utility functions and tables to that end, including:
\begin{itemize}
    \item Functions that convert between tags and symbol names. Tags are used by runtime terms because they can be compared more efficiently than strings.
    \item A table that describes the layout of a runtime term that corresponds to a certain tag.
    \item A table that provides the sort of the for a runtime term that corresponds to a certain tag.
    \item A table that provides the argument sorts (if any) for a runtime term that corresponds to a certain tag.
    \item A visitor function that recursively calls a given lambda on the children of a given runtime term.
\end{itemize}

Using these utilities, the backend runtime provides a function that constructs the initial runtime term from a given KORE pattern data structure. These utilities are also useful for various other runtime functions, such as serializers of runtime terms and conversion from runtime terms back to KORE AST data structures.

Beyond emitting utility code for converting and handling runtime terms, the code generator is responsible for generating code that performs steps 1 and 2 of the main execution loop, as described above. Specifically, for step 1, the code generator implements the decision tree as a nested switch statement that switches on the tags of the constructor symbol as well as the various tags of the symbols found in argument positions in the runtime term. The order of nesting is dictated by the decision tree and is optimized for minimizing the number of checks, as discussed in the decision tree section.

The case blocks for the final switch correspond to leaf nodes of the decision tree and thus, the code generator needs to fill them with code that implements the rewrite of the rule for said leaf node. For rules with side conditions, the side condition function also needs to be evaluated before we can confirm that the rule matched. The code generator produces code that creates a new runtime term as dictated by the right-hand side of the matching rule, applying all the necessary substitutions using subterms of the original runtime term that matched. This is how step 2 of the main execution loop is code-generated by the compiler.

Note that each function (including functions for side conditions) needs to be processed in the same way by the code generator. In other words, for each function, we need to create a decision tree according to the rewrite rules of the function and code-generate a similar execution loop as the top-level execution loop that rewrites top-level terms.


\subsection{Runtime Library}
The \KL backend comes with a runtime library written in C/C++ (and some parts in LLVM IR) that contains initialization and termination code, utilities that operate on runtime terms, and hooked implementations for \K functions that provide standard APIs for KORE sorts with native implementations. All this functionality is linked with the generated code to create the interpreter binary (or the static/dynamic library) for the input KORE definition.

The runtime library contains the main function that parses the various input flags and arguments to the interpreter, parses the initial KORE term into a runtime term, initiates the execution rewrite loop, and finally outputs the final runtime term as a KORE term.

It also contains utilities that operate on runtime terms, such as traversing the children of a term, serializing/deserializing a KORE term, pretty-printing a KORE term, etc.

Finally, the runtime library contains the implementation for various functions that come as builtin support with specific KORE sorts, e.g. appending elements to a list, checking membership in a set, inserting a key/value pair in a map, etc. All of these operations are implemented natively, in C/C++, using optimized libraries and algorithms. The native implementations are hooked to the corresponding KORE function symbols: The code generator knows to call the native function for such a KORE symbol application instead of code generating of the function body from rewrite rules which happens normally for function symbols.

Memory management and garbage collection are also part of the runtime library. However, they are treated as a separate subsystem due to their complexity.


\subsection{Memory Management and Garbage Collection}
During execution, there is a need to allocate and keep in memory various runtime terms. In addition, after every rewrite step it is likely that some subterms of the old runtime term are not needed for the new term (due to rewrites), and thus it would be desirable to deallocate such terms to reduce memory usage. Both the allocation of new terms and the garbage collection of useless terms are handled by the memory management subsystem of the \KL backend’s runtime.

The allocator of the memory management subsystem offers convenient allocation APIs for runtime terms that correspond to KORE symbols, as well as to builtin types such as integers, floating-point numbers, maps, lists, sets, etc. The allocator is a bump allocator: it keeps a pointer to the next available memory location and every time memory of certain size is requested, the current pointer is returned and then bumped by the requested size to get the next available location. Bump allocators are extremely fast but provide limited support for manual deallocation. For this reason, all runtime terms that are allocated through the allocator APIs are tracked and automatically deallocated at a later time by the backend's garbage collector.

It is important to note that subterms that correspond to constant values (known at compile time) are not allocated by the memory management subsystem’s allocators. They are rather being code-generated as LLVM IR constant structs that follow the same layout as normal runtime terms.

The memory management subsystem utilizes 3 different address spaces for memory allocation in order to enable a generational garbage collection strategy~\cite{Ungar1984}. These address spaces are called arenas, and they are: the young generation arena, the old generation arena, and the always collected arena. The main difference between these arenas is the frequency of garbage collection cycles:
\begin{itemize}
    \item \textbf{Young generation arena:} Collected at every garbage collection cycle.
    \item \textbf{Old generation arena:} Collected every 50 garbage collection cycles (the number is configurable, and it is possible to implement more complex logic for deciding the frequency of collection for this arena).
    \item \textbf{Always collected arena:} Collected at every garbage collection cycle and everything contained in the arena is collected as garbage.
\end{itemize}
A garbage collection cycle is initiated between rewrites (between steps 2 and 3 of the execution loop shown in \Cref{sec:codegen-overview}). It is only initiated when the arena in question is approaching full capacity of allocated memory.

Unless explicitly asked, the allocator APIs allocate memory in the young generation arena. Terms that survive a configurable number of garbage collections (currently, this number is just 1 collection) are transferred to the old generation arena, where they will be collected more infrequently. This is done to improve the performance of the garbage collector: Terms that survive a collection cycle are more likely to remain relevant for many rewrite cycles, and it is beneficial if they are not scanned by the garbage collector at every collection cycle. Finally, the always collected arena is intended for terms that will not be used after the next rewrite.

The garbage collector uses a copying strategy following Cheney's algorithm for list compaction~\cite{Cheney1970}. The arena being collected is divided into 2 halves, and at every point in time only one half is used for allocations. When garbage collection begins, the collector scans the active half and copies to the inactive half terms that are either pointed by some global term that is always live (such as the term corresponding to the top cell of a KORE configuration), or by some already copied term. After the whole active half has been scanned, only the terms that are reachable by a known live term have been copied. The rest of the terms are garbage to be collected. Collecting them is as simple as reversing the roles of active and inactive halves of the arena, and continuing allocations in the new active half.

\section{\KL Backend: Pattern Matching} \label{sec:k-llvm}
In this section, we extend the decision tree-based pattern matching compilation
algorithm presented by \citet{Maranget2008} with three substantial features.

First, we define a restricted subset of associative-commutative (AC) pattern
matching \cite{Hvllot1979} for the collection data types natively supported by
\K: \emph{lists}, \emph{maps} and \emph{sets}. Maps and sets entail AC pattern
matching, while lists are only associative (A). Secondly, we describe the
implementation of pattern matching for conditional rules (those that have
boolean side conditions). This extension permits a simple implementation of
non-linear pattern matching.

Once a decision tree has been generated for a \K rule, \KL then compiles that
tree to native code via LLVM intermediate code \cite{Lattner2004}. The result of
matching a term against a pattern is a set of substitutions mapping variables to
subterms.
\KL uses a compact runtime representation for \K terms that allows rewrite
rules to be applied efficiently. Additionally, it backs lists, maps, and sets by
immutable native data structures \cite{Bolivar2017}; doing so is substantially
more efficient than implementing them directly as terms to be rewritten.

We additionally demonstrate a generalization of the \texttt{qbaL} heuristic
\cite{Maranget2008,Scott2000} that strikes a balance between compilation time
and decision tree quality for the \KL-specific algorithm.


The remainder of this section describes the pattern-matching compilation and the
\KL interpreter runtime in more detail.

\subsection{Pattern Matching}

In this subsection, we introduce the basic concepts in the \KL pattern matching
algorithm. Following the terminology of \citet{Maranget2008}, we define sorts,
constructors, patterns, occurrences, and pattern matrices as they pertain to the
\K-specific context of this paper.

\paragraph{Terms:}

\K terms are abstract syntax trees of variable arity with a constructor symbol
at each node.

\paragraph{Sorts:}

In the \K frontend's parsing phase, terms are sorted according to the
productions in a definition's grammar. \KL receives well-sorted terms from the
frontend, and must only distinguish between \K constructors and the three
collection sorts (sets, maps, and lists). In all other respects the
pattern-matching algorithm we present is unsorted.

\paragraph{Constructors:}

We categorize \K constructors into \emph{regular} and \emph{collection}
constructors. Regular constructors correspond to user-defined programming
language constructs, and resemble ML terms. Additionally, \K defines built-in
regular sorts with an infinite family of zero-arity constructors (for example,
the integer literal \mintinline{c}{0} is a constructor for the
\mintinline{c}{Int} sort).

Collection constructors represent partial collection structure against which we
can pattern-match. The constructor $ \listcst(l) $ matches lists of
length $ l $, while $ \emptymap $ matches an empty map or set. Maps and sets also
permit two additional constructors: $ \mapkey(k) $ matches a map or set
containing precisely the key $ k $, and $ \mapchoice $ matches an arbitrary
element of a map or set. The Set sort can be understood as a degenerate Map,
where every key maps to the unit value; they permit the same constructors and,
unless specified, are treated identically throughout.


\paragraph{Patterns:} \label{sec:pattern-grammar}

Patterns are defined inductively over a set of unsorted variables, regular
constructors, and collections. We write $p$, $q$ for patterns, $ c $ for regular
constructors, and $ X $, $ Y $ for variables. The grammar for patterns over
\emph{regular} sorts is as follows:
\begin{align*}
  p \Coloneqq & \: X                        && \text{variable} \\
    \mid      & \: c(p_1, \dots, p_n)       && \text{regular constructor} \\
    \mid      & \: p \; \mathtt{as} \; X    && \text{as-binding} \\
    \mid      & \: p \lor q                 && \text{disjunction}
\end{align*}


We extend this grammar of patterns to collection sorts as follows:
\begin{align*}
  p \Coloneqq & \: p_1 ; \dots ; p_n                            && \text{list pattern ($n \geq 0$)} \\
    \mid      & \: p_1 ; \dots ; p_n ; L ; q_1 ; \dots ; q_m
              && \text{binding list pattern ($m + n \geq 1$)} \\
    \mid      & \: p_1 \; \dots \; p_n                          && \text{set pattern ($n \geq 0$)} \\
    \mid      & \: p_1 \; \dots \; p_n \; S                   
              && \text{binding set pattern ($n \geq 1$)} \\
    \mid      & \: p_1 \mapsto q_1 \; \dots \; p_n \mapsto q_n  && \text{map pattern ($n \geq 0$)} \\
    \mid      & \: p_1 \mapsto q_1 \; \dots \; p_n \mapsto q_n \; M
              && \text{binding map pattern ($n \geq 1$)}
\end{align*}

For each collection sort, we define a ``binding'' and ``non-binding'' pattern
production. The binding productions contain variables $ L $, $ S $ and $ M $
(for lists, sets and maps, respectively), which represent the \emph{remainder}
of the collection after the explicit pattern components have matched. For
example, the pattern $ p ; L ; q $ matches a list whose prefix matches $ p $ and
suffix matches $ q $, binding the variable $ L $ to the ``middle'' of the list
after removing those first and last elements. Sets and maps are commutative, and
so their patterns are not explicitly ordered.

This grammar does not express full AC matching, as binding patterns must contain
exactly one collection variable. This restriction allows our matching algorithm
to be more efficient than a classical rewriting engine with full AC matching
(such as Maude \cite{Clavel2007}). In practice, the
semantics of many real-world languages can be defined easily without full AC
matching, and so this restriction is not critical. Additionally, we restrict
binding patterns to contain at least one pattern other than the collection
variable; if this restriction was relaxed, such patterns would simply be
sort-categorized variable patterns.

\paragraph{Conditional patterns:}

Let $p$ be a pattern and $b$ be a boolean expression whose variables all occur
in $p$. We write conditional patterns as $p \land b$. From now on, we assume
that all patterns $p$ are linear; a nonlinear pattern can be easily desugared to
a linear conditional pattern. For example, $c(x,x,y,y)$ desugars to
$c(x,x',y,y') \land x=x' \land y=y'$. We therefore suffer no loss of generality.

\paragraph{Actions:}

We identify a set of actions, each representing the result of a successful
pattern match. These actions are simply distinct integers identifying a
particular \K rewrite rule to be applied.

\paragraph{Occurrences:}

Occurrences represent either subterms of a run-time term being matched, or
another run-time value relevant to the evaluation of a pattern match; we define
them as finite sequences of tokens, where each token is:
\begin{align*}
  ot \Coloneqq n \in \mathbb{N} \mid \siz \mid \key \mid \val \mid \rem \mid \iter \mid \fsh(\act) \mid \pat(p)
\end{align*}

The precise semantics of each of these tokens with respect to a particular term
is explained later in this section, when the compilation of pattern matching
over collections is defined. For now, a rough intuition is sufficient: an
integer $ n $ is the $ n $th
child of a regular or list constructor,
$\siz$ represents the size of a collection at run-time; $ \key $ and $ \val $
are the key and value stored in maps (c.f.\ sets), and $ \rem $ is the remainder
of a collection after a matched element is removed. $ \iter $ is a run-time
iterator into a collection; $ \fsh(\act) $ is the result of a rule's side
condition, and $ \pat(p) $ tracks the original element of a map or set to which
another token refers.

\paragraph{Pattern matrices:}

We maintain pattern-matching state in a $ m \times n $ matrix of patterns. We
additionally track the occurrence against which each pattern matrix entry is
currently being matched, the (partial) matching solutions, the corresponding
actions, side conditions (if any), and auxiliary information for collection
sorts such as lists, maps, and sets. The pattern matrix $ \PP $ has the
following basic form:
$$
\PP =
\begin{pmatrix}
\PP[1,1] & \PP[1,2] & \cdots & \PP[1,n]  \\
\PP[2,1] & \PP[2,2] & \cdots & \PP[2,n]  \\
         &          & \vdots \\
\PP[m,1] & \PP[m,2] & \cdots & \PP[m,n] 
\end{pmatrix}
\ \ 
\begin{matrix}
\leftarrow \pprow{1} \\
\leftarrow \pprow{2} \\
\vdots \\
\leftarrow \pprow{m}
\end{matrix}
$$
\vspace{-0.5\baselineskip}
$$
\begin{matrix}
\uparrow & \uparrow & \cdots & \uparrow \\
\ppcol{1}\ & \ppcol{2}\ & \cdots & \ppcol{n}
\end{matrix}
\kern7ex
$$
Individual patterns in $\PP$ are written $\pp{i}{j}$. We write $\pprow{i}$ to
denote the $i$th row vector and $\ppcol{j}$ the $j$th column vector in $\PP$.
Along with the current matrix of patterns, we maintain a tuple of additional
information $ \pr{\PP, \succeq, [o_j], [s_j], \sol, \actb, \condb, \lslen}$, where
\begin{enumerate}

  \item $\succeq$ is a partial ordering on the rows of $\PP$, corresponding to
    the priorities of the rewrite rules. If $i_1 \succeq i_2$, row $i_1$ has
    higher priority than row $i_2$.  If both rows can be matched, row $i_1$ will
    be applied because it has higher priority. 

    Typically, in functional languages such as ML, exactly one rule is matched,
    and textual priority is used to enforce the order in which matching is
    attempted. However, in \K, it is often the case that multiple rules can
    match a term with equal priority; it is possible to extend our algorithm to
    generate the set of all possible matches rather than choosing exactly one.

  \item $ \{ o_j \}^n_{j=1} $ and $ \{ s_j \}^n_{j=1} $ are lists of $n$
    occurrences and sorts, respectively, corresponding to the $n$ columns of
    $\PP$.

  \item For the $i$-th row of $\PP$ ($1 \le i \le m$):
  \begin{enumerate}
    \item $\sol[i]$ is a (partial) solution, which is a mapping from
      variables to occurrences.

    \item $\actb[i] \in \Act$ is an action, which is the action to take if row
      $i$ is matched.

    \item $\condb[i]$ is a boolean side condition.

    \item $\lslen[i]$ is a list of tuples, each of the form $ \pr{o, s, n_1,
      n_2} $ with $ n_1, n_2 \in \NN $ and $ n_1 \leq n_2 $. These represent the
      sections of a list that are bound by a particular row.
  \end{enumerate}
\end{enumerate}

\paragraph{Column signatures:}

We define the \emph{signature} of a column $ \ppcol{j} $ as the set of
constructors that must be considered when pattern matching the term
corresponding to $ o_j $. First, we define the function $ \patsig $ over
regular patterns:
\begin{align*}
  \patsig(X) & = \emptyset \\
  \patsig(c(p_1, \dots, p_a)) & = \{ c \} \\
  \patsig(p \; \mathtt{as} \; X) & = \patsig(p)
\end{align*}

This definition is extended for collection patterns:
\begin{align*}
  \patsig(p_1 ; \dots ; p_n) & = \{\listcst(0), \dots, \listcst(n)\} \\
  \patsig(p_1 ; \dots ; p_n; L; q_1 \dots q_m) & = \{\listcst(0), \dots, \listcst(m+n)\} \\
  \patsig(p_1 \mapsto q_1 \dots p_n \mapsto q_n) & = \{\emptymap\} && \text{ if } n = 0 \\
  \patsig(p_1 \mapsto q_1 \dots p_n \mapsto q_n) & = \{\mapkey(p_1), \dots, \mapkey(p_n)\} && \text{ if } n > 0 \\
  \patsig(p_1 \mapsto q_1 \dots p_n \mapsto q_n \; M) & = \{\mapkey(p_1), \dots, \mapkey(p_n)\} \\
  \patsig(p_1 \; \dots \; p_n) & = \{\emptymap\} && \text{ if } n = 0 \\
  \patsig(p_1 \; \dots \; p_n) & = \{\mapkey(p_1), \dots, \mapkey(p_n)\} && \text{ if } n > 0 \\
  \patsig(p_1 \; \dots \; p_n \; S) & = \{\mapkey(p_1), \dots, \mapkey(p_n)\}
\end{align*}

We can then define the pattern signature for a column $ j $ with sort $ s $ in
terms of the signature of the individual patterns in that column:
\begin{align*}
  \patsig'(s, j) & = \bigcup_{1 \leq i \leq m} \patsig(\PP[i, j]) \\
  \patsig(s, j)  & = \{ \emptymap \}
                 && \text{if $ s $ is a map or set sort, and $ \emptymap \in \patsig'(s, j)$} \\
  \patsig(s, j)  & = \{ \bestkey(j) \}
                 && \text{if $ s $ is a map or set sort, and $ \emptymap \notin \patsig'(s, j)$} \\
  \patsig(s, j)  & = \patsig'(s, j)
                 && \text{otherwise}
\end{align*}

The function $ \bestkey(j) $ is a customization point for heuristics; it returns
either $ \mapchoice $ or some $ \mapkey(k) \in \patsig(s, j) $, specifying how
the map should be decomposed. A precise definition will be given later.

\paragraph{Canonical variables:}

Typically, we identify pattern variables as names. However, in some contexts, we
need to refer to the actual occurrences bound by those variables. For a given
row of the clause matrix, the substitution $ \sol[i] $ maps variables to
occurrences. To \emph{canonicalize} a pattern $ p $, we replace all named
variables with their bindings in $ \sol[i] $. A pattern is \emph{bound} if its
named variables have a binding in $ \sol[i] $.

We additionally adopt the standard definition of unification for patterns with
named variables; two patterns \emph{unify} if there exists a binding for all
their named variables such that substituting that binding into both patterns
produces the same pattern.

\paragraph{Initialization:} \label{sec:matrix-init}

Given a set of rewrite rules, we initialize $ \PP $ to a one-column,
$m$-row matrix:
\begin{align*}
  \PP =
  \begin{pmatrix}
    LHS[1] \\
    \vdots \\
    LHS[m]
  \end{pmatrix}
\end{align*}
where each pattern $ LHS[i] $ is the left-hand side of the $i$-th
rewrite rule. The rows of $ \PP $ are sorted according to the partial ordering $
\succeq $ induced by the original \K definition. For this single column matrix,
$ o_1 = \epsilon $ and $ s_1 = s $, where $ s $ is the sort of the term being
matched.

The lists $ \actb $ and $ \condb $ are initialized straightforwardly from the
right-hand side and side condition of the underlying \K rules. Then, $ \sol[i] $
and $ \lslen[i] $ are initialized to the empty set and empty list respectively.


\section{Pattern Decomposition} \label{sec:decomp}

To compile a pattern matrix into efficient code, we decompose the patterns in
each row into smaller components, while keeping track of the variable bindings
produced by doing so, and the subterm currently being scrutinized by each
pattern. Following \citet{Maranget2008}, we do so by defining two operations on
pattern matrices: \emph{specialization} and \emph{default decomposition}.

Specialization transforms a pattern matrix under the assumption that the subterm
being scrutinized has a particular head constructor. We write $ \cS(\PP, c, j) $
for the matrix obtained by discarding any rows of $ \PP $ that are known not to
have a pattern with constructor $ c $ in column $ j $, and reducing rows that do
to their sub-patterns. Conversely, the default decomposition (written $ \cD(\PP,
j) $) transforms $ \PP $ under the assumption that the current subterm will not
match any constructor patterns in column $ j $ (i.e.\ its head constructor does
not match any of the constructors in the column). Formal definitions of these
operations are given later in this section.

This subsection is divided into several parts for clarity. First, in
\Cref{sec:decomp:reg}, we define our instantiation of pattern matrix
decomposition for \emph{regular} constructors only, largely following the
terminology of \citet{Maranget2008}. Then, in
\Cref{sec:decomp:list,sec:decomp:map,sec:decomp:set}, we extend these
definitions substantially to account for collection sorts.

Disjunction patterns ($p \lor q$) are expanded into a row with the same action
and priority group for each disjoint pattern in the disjunction. By doing so
pairwise across all components of the disjunction, we eliminate these
patterns with no loss of generality and do not consider them further in this
section.

\subsection{Regular Patterns} \label{sec:decomp:reg}


\begin{definition}{Specialization on regular patterns}.

Our specialization procedure for regular patterns follows \citet{Maranget2008}:
at a high level, the specialized matrix $ \cS(\PP, c, j) $ is obtained by either
expanding or removing rows of $ \PP $ based on the head constructor of $ \PP[i,
j] $ and the constructor $ c $. If the head constructor is $ c $, then $ \PP[i,
j] $ is replaced by its arguments (expanding the row); if it is not $ c $, then
the row is removed.

Additionally, we extend this procedure with an accumulated variable binding
environment. If $ \PP[i, j] $ is a variable $ x $, then we update the binding
state:
\begin{align*}
  \sol[i]   & := \sol[i] \cup \{x \mapsto (o_j, s_j) \}
    && \text{(bind $x$ to the occurrence being matched)}
\end{align*}

If $ \PP[i, j] $ is $ p \; \mathtt{as} \; X $, then we proceed by specializing on $
p $, and similarly binding $ X $ to the current occurrence and sort.








After applying this process to each row, the pattern matrix has $n-1+a$ columns;
it may also have fewer rows if any did not match the constructor $ c $. To
account for the new structure, we must also update the lists $ [o_j] $ and $
[s_j] $ so that they remain consistent. The following elementwise updates to the
lists are performed, replacing the elements $ o_j $ and $ s_j $ with vectors:
\begin{align*}
  o_j & \to (1 \cdot o_j, \dots, a \cdot o_j) \\
  s_j & \to (s^c_1, \dots, s^c_a)
\end{align*}
where each $ s^c_i $ is the sort of the $ i^{\text{th}} $ argument of
constructor $ c $.

\end{definition}


\begin{definition}{Default decomposition on regular patterns.}

The default decomposition is dual to the specialization matrix; rather than
assuming that the term $ o_j $ has precisely constructor $ c $, we assume that
it has a constructor \emph{not contained} in $ \patsig(s_j, j) $. This
means that any constructor patterns in column $ j $ will not match the current
term, and that any variable patterns will match the term without needing to
match any further subterms. We define row-wise rewrites similar to the
specialization matrix, including variable bindings.






The resulting pattern matrix will have $ n - 1 $ columns, and may also have
fewer rows. We update $ [o_j] $ and $ [s_j] $ to account for the change in
structure by simply deleting the elements $ o_j $ and $ s_j $ from their
respective vectors.

\end{definition}



\subsection{List Patterns} \label{sec:decomp:list}


\begin{definition}{Specialization on list patterns.}

List collections permit one constructor: $\listcst(l)$, representing the family
of all lists of length $ l $. Specializing the pattern matrix against this
constructor amounts to ensuring that the pattern $ \PP[i, j] $ being scrutinized
can match a list with $ l $ elements, and that if the pattern binds a
list-sorted variable $ L $, the correct middle slice of the object term is
bound. We define $ \PP[i, \front] $ to be the sequence $ \PP[i, 1], \dots,
\PP[i, j-1] $, and $ \PP[i, \tail] $ to be (analogously) $ \PP[i, j + 1], \dots,
\PP[i, n] $, and proceed:
\begin{enumerate}

  \item If $ \PP[i, j] $ is the non-binding list pattern $ p_1; \dots; p_l $,
    then rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p_1, \dots, p_l, \PP[i, \tail])
    \end{align*}

  \item If $ \PP[i, j] $ is the non-binding list pattern $ p_1; \dots; p_k $
    where $ k \neq l $, then delete the current row (a list of exactly $ l $
    elements cannot match a pattern with $ k $ elements).

  \item If $ \PP[i, j] $ is $ p_1; \dots; p_h; L, q_1; \dots; q_t $, and $ l > h
    + t $, then there are excess list elements to bind to the variable $ L $. We
    therefore introduce new fresh variables $ y_1, \dots, y_{l-(h+t)} $ to bind
    each of these elements, and rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p_1, \dots, p_h, y_1, \dots, y_{l-(h+t)}, q_1, \dots, q_t, \PP[i, \tail])
    \end{align*}
    We additionally update the state as follows:
    \begin{align*}
      \sol[i]   & := \sol[i] \cup \{ L \mapsto (l + 1 \cdot o_j, s_j) \} \\
      \lslen[i] & := \lslen[i] :: (l + 1 \cdot o_j, s_j, h, t)
    \end{align*}
    where $ :: $ is list concatenation. The contents of the $ \lslen[i] $ list
    are used later to ensure that the variable $ L $ binds the correct subterms.

  \item If $ \PP[i, j] $ is $ p_1; \dots; p_h; L, q_1; \dots; q_t $, and $ l = h
    + t $, then there are no excess list elements to be bound to $ L $, and so
    we rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p_1, \dots, p_h, q_1, \dots, q_t, \PP[i, \tail])
    \end{align*}
    and perform the same state update as above:
    \begin{align*}
      \sol[i]   & := \sol[i] \cup \{ L \mapsto (l + 1 \cdot o_j, s_j) \} \\
      \lslen[i] & := \lslen[i] :: (l + 1 \cdot o_j, s_j, h, t)
    \end{align*}

  \item Finally, if $ \PP[i, j] $ is $ p_1; \dots; p_h; L, q_1; \dots; q_t $,
    and $ l < h + t $, then the pattern has too many elements to match the list
    constructor being scrutinized. We therefore delete the current row.

\end{enumerate}

As for regular constructors, specializing on a list constructor entails updates
to the occurrence and sort vectors $ [o_j] $ and $ [s_j] $. The individual
elements $ o_j $ and $ s_j $ are replaced by vectors:
\begin{align*}
  o_j & \to (1 \cdot o_j, \dots, l \cdot o_j) \\
  s_j & \to (s_e, \dots, s_e)
\end{align*}
where $ s_e $ is the element sort of $ s_j $.

\end{definition}


\begin{definition}{Default decomposition on list patterns.}

For list constructors, the default decomposition can be defined conveniently in
terms of specialization. Recall that the default decomposition transforms the
pattern matrix under the assumption that \emph{none} of the patterns in the
current column match the constructor currently being scrutinized. Let $ l_{head}
$ and $ l_{tail} $ be the lengths of the longest list pattern head and tail in $
\PP $. We know that the list being scrutinized must be longer than any pattern
in the column being decomposed, and so specializing on $ \listcst(l_{head} +
l_{tail}) $ guarantees that no elements in between can be referenced by any
submatrix. This produces the default decomposition in terms of specialization.

\end{definition}



\subsection{Map Patterns} \label{sec:decomp:map}


In order to maximize efficiency, \K does not implement fully general AC pattern matching for maps or sets.
Instead, the grammar of map and set patterns (see \Cref{sec:pattern-grammar}) is restricted
to two specific cases that can be compiled efficiently and suffice in practice.
The first, when the key
of the map element being matched is bound, is called a \emph{lookup}. The
second, when the key is not bound, is called a \emph{choice}. Additionally,
patterns may match the empty map or set.

\begin{definition}{Specialization on map patterns.}

To define specialization for maps and sets, we must therefore
define it separately for each of their constructors. First, let us
consider the empty map (i.e. the constructor $ \emptymap $), retaining the
definitions used previously for $ \PP[i, \front] $ etc.:

\begin{enumerate}

  \item If $ \PP[i, j] $ is the map pattern with $ n = 0 $, then rewrite the
    current row to:
    \begin{align*}
      (\PP[i, \front], \PP[i, \tail])
    \end{align*}
    This is intuitive: the map pattern with no sub-patterns should only match
    the empty map constructor, and so we are free to discard the pattern $
    \PP[i, j] $.

  \item If $ \PP[i, j] $ is a non-binding map pattern with $ n \geq 1 $ (i.e.\ $
    p_1 \mapsto q_1 \dots p_n \mapsto q_n $), then we delete the current row.

  \item Similarly, for any binding map pattern, we delete the current row
    (recall from \Cref{sec:pattern-grammar} that the grammar for map patterns
    enforces $ n \geq 1 $ for binding patterns, to distinguish them from
    ordinary variable patterns).

\end{enumerate}

Now, consider the $ \mapkey(k) $ constructor, which represents a known-key
lookup in a map. The specialization procedure here is somewhat more complex
than for $ \emptymap $. Intuitively, three new columns are created to replace
the pattern $ \PP[i, j] $ being scrutinized. These correspond to, in order, the
value bound to key $ k $, the map pattern after removing $ k $ from the map, and
the original map. We retain the original map as the third column because the set
of keys may differ across rows, and for rows that may not contain $ k $, we
should do no work and must specialize on the entire remaining map.

In this section, we write $ \mapp $ as shorthand for the
pattern syntax $ p_1 \mapsto q_1 \dots p_n \mapsto q_n $. With that in
mind, the specialization procedure for $ \mapkey(k) $ is as follows:

\begin{enumerate}

  \item If $ \PP[i, j] $ is a non-binding map pattern $ \mapp $, then we rewrite
    the current row to:
    \begin{align*}
      (\PP[i, \front], q_x, \mappPrime , Y, \PP[i, \tail])
    \end{align*}
    if there exists a pattern $ p_x $ in $ \vec{p_s} $ such that $ p_x $ is
    bound, and the canonicalized $ p_x = k $, where $ Y $ is a fresh anonymous
    variable that does not appear in the current substitution, and $ \mappPrime
    $ is $ \mapp $ with $ p_x \mapsto q_x $ removed. When this case applies, we
    must further scrutinize the value bound by $ k $, and the reduced remaining
    map, but will do no further examination of the rest of the map because of
    the anonymous variable $ Y $.

  \item Similarly, if $ \PP[i, j] $ is the binding map pattern $ \mapp \; M $,
    then we rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], q_x, \mappPrime \; M , Y, \PP[i, \tail])
    \end{align*}
    under the same side condition and fresh variable introductions as above.

  \item If $ \PP[i, j] $ is a non-binding map pattern $ \mapp $, then we rewrite
    the current row to:
    \begin{align*}
      (\PP[i, \front], Y, Z, \PP[i, j], \PP[i, \tail])
    \end{align*}
    if there is a $ p_x $ in $ \vec{p_s} $ such that the canonicalized $ p_x $
    unifies with $ k $, but $ k $ is not in the canonicalized $ p_x $.

  \item Similarly, if $ \PP[i, j] $ is a non-binding map pattern $ \mapp \; M $,
    then we rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], Y, Z, \PP[i, j], \PP[i, \tail])
    \end{align*}
    if $ k $ is not in the canonicalized $ p_x $.

  \item Finally, if none of the cases above apply to $ \PP[i, j] $ (i.e.\ for
    all $ p_x $, either $ p_x $ is not bound, or its canonicalized form does not
    unify with $ k $), we remove the current row.

\end{enumerate}

Finally, we can consider the $ \mapchoice $ constructor, corresponding to the
case where the map key being scrutinized is not known. Once again, specializing
on this constructor generates three new columns in the pattern matrix,
corresponding to the key pattern and value pattern that are matched, as well as
the remainder of the map after they are removed.

\begin{enumerate}

  \item If $ \PP[i, j] $ is a binding map pattern $ p \mapsto q \; M $, then we
    rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p, q, M, \PP[i, \tail])
    \end{align*}

  \item If $ \PP[i, j] $ is a binding map pattern $ p_1 \mapsto q_1 \dots p_n
    \mapsto q_n \; M $ with $ n \geq 2 $, then we rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p_1, q_1, \vec{p'_n} \mapsto \vec{q'_n} \; M, \PP[i, \tail])
    \end{align*}
    where $ \vec{p'_n} \mapsto \vec{q'_n} $ is all the remaining map pattern
    elements with $ n > 1 $.

  \item If $ \PP[i, j] $ is a non-binding map pattern $ p_1 \mapsto q_1 \dots p_n
    \mapsto q_n $ with $ n \geq 1 $ then we rewrite the current row to:
    \begin{align*}
      (\PP[i, \front], p_1, q_1, \vec{p'_n} \mapsto \vec{q'_n} , \PP[i, \tail])
    \end{align*}
    only if the current row is in the \emph{topmost} priority group. This
    restriction prevents us from failing to match the first key tried, then
    immediately dropping down to lower-priority groups (i.e.\ the \emph{pattern}
    could still match, even if a particular key failed to). Details of the
    compilation algorithm presented later ensure that lower-priority groups are
    actually tried in practice.

  \item If $ \PP[i, j] $ is an empty map pattern, we delete the current row (it
    is impossible to choose an element from an empty map).

  \item For any row $ i $  not in the topmost priority group, we delete that
    row. As above, this action is safe because of properties of the later
    compilation step.

\end{enumerate}

As for regular and list patterns, we update the sort and occurrence vectors $
[s_j] $ and $ [o_j] $ when specializing over map constructors. For the $
\emptymap $ constructor, we simply erase $ s_j $ and $ o_j $ respectively. For $
\mapkey(k) $, we replace those elements with vectors:
\begin{align*}
  o_j & \to (\val \cdot \pat(k) \cdot o_j, \rem \cdot \pat(k) \cdot o_j, o_j) \\
  s_j & \to (s^v_j, s_j, s_j)
\end{align*}
where $ s^v_j $ is the value sort of the map sort $ s_j $.
Similarly, for $ \mapchoice $, we rewrite as follows:
\begin{align*}
  o_j & \to (\key \cdot o_j, \val \cdot o_j, \rem \cdot o_j) \\
  s_j & \to (s^k_j, s^v_j, s_j)
\end{align*}

\end{definition}

\begin{definition}{Default decomposition on map patterns.}

We define the default decomposition for columns with a map sort as follows:

\begin{enumerate}

  \item If $ \PP[i, j] $ is a non-binding map pattern with $ n = 0 $, and $
    \emptymap \in \patsig(s_j, j) $, we delete the current row.

  \item If $ \PP[i, j] $ is a non-binding map pattern with $ n > 0 $, or a
    binding map pattern with $ n \geq 0 $, and $ \emptymap \in \patsig(s_j, j)
    $, we do not rewrite the current row.

  \item If $ \PP[i, j] $ is a non-binding map pattern $ \mapp $, or a binding
    map pattern with $ n \geq 0 $, and $ \mapkey(k) \in \patsig(s_j, j) $, but
    the canonicalized $ \vec{p_s} $ does not contain $ k $, we do not rewrite
    the current row.

  \item If $ \PP[i, j] $ is not an empty pattern (i.e.\ it is binding, or is
    non-binding with $ n > 0 $), $ \mapchoice \in \patsig(s_j, j) $, and row $ i
    $ is not in the topmost priority group, then we do not rewrite the current
    row.

  \item In all other cases, we delete the current row.

\end{enumerate}

\end{definition}

\subsection{Set Patterns} \label{sec:decomp:set}

\begin{definition}{Specialization and default decomposition on set patterns.}

The specialization and default decompositions for set sorts are almost identical
to those for map sorts, and so for brevity we avoid a full definition. The only
substantive change is that wherever a column corresponding to a mapped value
is generated for map decompositions, no column is generated for sets. For
example, the occurrence vectors that replace $ o_j $ for $ \mapkey(k) $ and $
\mapchoice $ respectively for set sorts are:
\begin{align*}
  o_j & \to (\rem \cdot \pat(k) \cdot o_j, o_j)
      && \mapkey(k) \\
  o_j & \to (\key \cdot o_j, \rem \cdot o_j)
      && \mapchoice
\end{align*}

\end{definition}

\section{Compiling to Decision Trees} \label{sec:compile}

We have now defined specialization and default decompositions for collection
sorts. Again following the style of \citet{Maranget2008}, we now define a
\emph{decision tree} structure that represents the actual runtime decisions made
when decomposing a pattern matrix. A decision tree can be interpreted
to produce an action identifier and a set of variable bindings (if the
corresponding pattern matching problem is successful); the actual implementation
used by \KL generates equivalent machine code from a tree structure for
efficiency.


\subsection{Decision Trees} \label{sec:dt-adt}

Decision trees are specified by the following term grammar:
\begin{align*}
  \DT \Coloneqq & \: \Fail \\
      \mid      & \: \Success(a, [(o, s)]) \\
      \mid      & \: \Switch(o, s, [(c, \DT)], DT?) \\
      \mid      & \: \CheckNull(o, s, \DT, \DT) \\
      \mid      & \: \FunctionDT(o, f, [(o, s)], s, \DT) \\
      \mid      & \: \Pattern(o, s, p, \DT) \\
      \mid      & \: \IterHasNext(o, s, \DT, \DT)
\end{align*}
where $ a $ is an action identifier (i.e.\ an integer), $ o $ is an occurrence,
$ s $ is a sort, $ c $ is a constructor, $ p $ is a pattern, and $ f $ is a
function. $ [...] $ represents lists, and $ ? $ is an optional argument to a term.

\subsection{Evaluation}

\begin{algorithm*}
  
  \caption{
    Evaluation semantics for our decision tree structure. The
    type Subst is a mapping from occurrences to either concrete patterns or
    iterators into maps and sets. Any occurrences not explicitly set in the
    substitution map to None. The initial substitution $ S $ maps the empty
    occurrence $ \epsilon $ to the top-level pattern. The \textsc{Parent}
    function returns the parent node of a decision tree node; for the $
    \IterHasNext $ case, this will be a $ \FunctionDT $ node that retries the
    matching process with the next element in the collection.
  }
  \label{alg:tree-evaluate}

  \footnotesize
  \begin{algorithmic}[1]
    \Function{Evaluate}{DT $dt$, Subst $S$, [(DT, Subst)] $choices$} $\to$ (Action, Subst)?
      \Case{$dt$}

        \CaseItem{$\Success(A, \_)$}{\ret $ (A, S) $}

        \CaseItem{$\Fail$}{}
        \Indent
          \Case{$choices$}
            \CaseItem{$[]$}{\ret None}
            \CaseItem{$(dt', S') :: tail$}{\ret $\textsc{Evaluate}(dt', S', tail)$}
          \EndCase
        \EndIndent

        \CaseItem{$\Switch(o, s, cases, default)$}{}
        \Indent
          \State $ c \gets $ the constructor of $ S[o] $
          \If{$ c \in cases $}
            \For{$ i = 1 $ to $ \textsc{Arity}(a) $}
              \State $ S[i \cdot o] \gets i^{\text{th}} $ child of $ S[o] $
            \EndFor
            \State \ret $ \textsc{Evaluate}(\text{decision tree for } c, S, choices )$
          \Else
            \State \ret $ \textsc{Evaluate}(default, S, choices) $
          \EndIf
        \EndIndent

        \CaseItem{$\CheckNull(o, s, case_{true}, case_{false})$}{}
        \Indent
          \State $ dt' \gets S[o] \text{ is None} \: ? \: case_{true} : case_{false} $
          \State \ret $ \textsc{Evaluate}(dt', S, choices) $
        \EndIndent

        \CaseItem{$\FunctionDT(o, f, args, s, dt')$}{}
        \Indent
          \State $ S[o] \gets f([S[a] \mid a \in args]) $
          \State \ret $ \textsc{Evaluate}(dt, S, choices) $
        \EndIndent

        \CaseItem{$\Pattern(o, s, pat, dt')$}{}
        \Indent
          \State $ S[o] \gets pat $ substituted using $ S $
          \State \ret $ \textsc{Evaluate}(dt, S, choices) $
        \EndIndent

        \CaseItem{$\IterHasNext(o, s, case_{true}, case_{false})$}{}
        \Indent
          \If{$ S[o] $ is None}
            \State \ret $ \textsc{Evaluate}(case_{false}, S, \textsc{Parent}(dt) :: choices) $
          \Else
            \State \ret $ \textsc{Evaluate}(case_{true}, S, choices) $
          \EndIf
        \EndIndent
      \EndCase
    \EndFunction
  \end{algorithmic}

\end{algorithm*}

The exact semantics of decision trees is given in
\Cref{alg:tree-evaluate}, but a brief summary is as follows: $ \Fail $ and $
\Success $ are leaf nodes, where a pattern
has either failed to match a term, or has succeeded and produces an action to be
taken (here, an integer representing a \K rewrite rule to be applied to the term
being scrutinized). $ \Switch $ is the basic unit of control flow for regular
sorts in decision trees, representing an $n$-ary case split across a set of
constructors.

$ \CheckNull $ dispatches to one of two sub-trees depending on whether an
occurrence bound to an optional value is None. $ \FunctionDT $ is used to
capture a particular function to be evaluated when the decision tree itself is
(e.g.\ to return the length of a list argument), and bind the result into the
substitution. $ \Pattern $, similarly, binds a particular pattern to an
occurrence. Finally $ \IterHasNext $ is used to implement backtracking through
map and set collections.


The \textsc{Evaluate} algorithm is largely responsible (at a high level) for
ensuring that occurrences are bound to the correct concrete patterns or
iterators before case splits are performed on the top-level term. Backtracking
is implemented by maintaining a stack of resumption points from which evaluation
can continue should matching fail. This backtracking is used when choosing
elements from maps and sets: if the chosen element causes matching to fail, then
prepending the parent node means that the match can be resumed with the next
element in the collection.  This algorithm is abstract; for efficiency, our
implementation of \KL instead transforms a decision tree into native code.

\subsection{Compilation}

With this definition of decision trees in hand, we can now define a compilation
algorithm from the initial pattern matrix (given in \Cref{sec:matrix-init}) to a
decision tree. This algorithm follows the structure suggested by
\citet{Maranget2008}; if there is a topmost-priority row with only variable
patterns (i.e.\ one that will always match), we compile that row and remove it.
Otherwise, we heuristically select a column and decompose it. The extensions
described in \Cref{sec:decomp} require additional state for variable binding and
runtime collections be maintained while doing so. This section provides a
high-level overview of this procedure.



\paragraph{Lists\\} Lists in \KL behave similarly to regular constructors in the
\textsc{CC} function described by Maranget, but require a run-time check to
establish their length before they can be matched. Additionally, we must ensure
that sufficient elements are available at their head and tail to bind the
relevant variables. These run-time checks correspond to \textsc{Function} nodes
in a decision tree that retrieve those elements at run-time.


\paragraph{Maps and sets\\}

The main difficulty in decomposing a map is that we may need to \emph{backtrack}
through the collection if the constructor $ \mapchoice $ appears in the current
column signature. To do so, we construct an $ \iter $ occurrence and bind it to
the correct run-time part of the collection. Additionally, we bind occurrences
for the key and value selected, along with the remainder of the collection after
removing that key. If there is no $ \mapchoice $ in the column signature, but
there is a $ \mapkey(k) $, no backtracking (and therefore binding of iterators)
is required, but we must check whether that key is present at run time (this
check is analogous to determining whether a list has sufficient elements at
run-time to match a pattern).


The decomposition procedure for sets is very similar; it does not require that
values are bound to occurrences (only keys, remainders and iterators), and
instead of extracting values from a map, membership tests for a key are
sufficient.














 

















































































\section{Heuristics\\} \label{sec:heuristics}

Two important heuristic choices remain in our decision tree compilation
procedure. \citet{Maranget2008} details several methods by which the
decomposition column $ j $ should be chosen first; for \KL, we adapt the
\texttt{qbaL} heuristic from that work. While we have not evaluated it formally,
our experience of implementing \KL suggests that this choice strikes an
appropriate balance between ease of implementation, compilation time and
performance of generated code.

One small modification to the \texttt{q} (constructor prefix) heuristic was
required. Because row priority in \KL is not a total ordering, our definition of
\texttt{q} does not stop counting after the first non-constructor row. Rather,
we also count any constructor patterns in the same group as that row
(effectively stopping after the first \emph{group} with a wildcard entry). The
\texttt{b}, \texttt{a} and \texttt{L} heuristics could be used unmodified.


\paragraph{Key selection\\}

In \Cref{sec:decomp:map}, our definition of $ \patsig $ relied on the $
\bestkey $ function to compute the signature of a map- or set-sorted column.
Before we can identify the best column $ j $ to decompose on, we must identify
the best key $ k $ to form the column signature for maps and sets.
The high-level principle by which we select keys is that we want to avoid set
and map \emph{choices}; these operations can cause the decision tree to
backtrack, which can be potentially very slow. Instead, we prefer to specialize
on bound key lookups where possible.

We therefore define $ \bestkey $ as follows:
\begin{align*}
  \bestkey(j) & = \mapchoice && \text{if no bound keys in column } j \\
  \bestkey(j) & = \mathsf{argmin}_j \; c(j) && \text{otherwise}
\end{align*}
where $ c(j) $ is the \texttt{qbaL} heuristic cost function described in the
next section, and $ \mathsf{argmin}_j $ will return the value of $ j $ for which
$ c(j) $ is lowest.











\paragraph{Priority inversion\\}

Consider the following partial pattern matrix, with the second row giving the
hypothetical heuristic scores for the remainder of each column:
\begin{align*}
  \begin{pmatrix}
    a(X) & X \mapsto Y & b \mapsto d \\
    c(1) = 1 & c(2) = 9 & c(3) = 6 \\
    \dots & \dots & \dots
  \end{pmatrix}
\end{align*}
Here, column 2 has $ \{ \mapchoice \} $ as its pattern signature, because it
does not have any map keys that are bound, and so will not be selected for
decomposition ahead of columns 1 and 3.  However, it has the best heuristic
score, and so would produce the smallest compiled tree.

We can see that while decomposing on column 1 has the lowest heuristic score,
doing so would produce a binding for $ X $ that would allow column 2 to be
selected. This is an instance of \emph{priority inversion}: column 2 is waiting
for column 1 to be decomposed. To address this, we set the score of each column
to be the highest score of any column that depends on it. A column $ j $ depends
on a column $ k $ if there exists a row $ i $ and variable $ X $ such that $ X $
occurs in $ \PP[i, k] $, and $ X $ occurs in a key position in $ \PP[i, j] $.














\section{Evaluation} \label{sec:eval}
Our goal when designing and implementing \KL was to produce a fast
term-rewriting backend for \K's core language. In this section, we evaluate our
success by benchmarking interpreters for specific programming languages generated by \K using \KL in two benchmarks: the Blockchain Tests from the Ethereum test suite \cite{ethereum-tests} and a synthetic benchmark with 1,000 swap operations on an ERC20 token~\cite{1kswapscode}. Our results are surprisingly positive; we find that:

\begin{enumerate}
    \item The \K implementation of EVM~\cite{HSZ+18} currently can reach only 1.35x slower execution than Geth, the Go official implementation of EVM~\cite{geth} which is the most adopted Ethereum client, widely used by the community~\cite{ethernodes}.
    \item The language interpreters generated through \KL have the potential to be as good as the top and widely used Ethereum clients. By using Compositional Symbolic Execution (CSE) it is possible to outperform Geth by 1.575x.
\end{enumerate}




All experiments were conducted on a machine with a 13th Gen Intel\textsuperscript{\tiny\textregistered} Core™ i9-13900K 24-Core CPU (32 threads), with Intel\textsuperscript{\tiny\textregistered} UHD Graphics 770 (Integrated with CPU) and 64 GB RAM.

\subsection{Evaluation of {\K}EVM against Geth}

To evaluate the performance of \KL as the primary tool for implementing programming languages, we first considered the Ethereum Virtual Machine (EVM) bytecode language. The Ethereum Virtual Machine is a stack-based virtual machine used as the execution layer for the Ethereum blockchain.

We used \KL to generate an EVM interpreter from a state-of-the-art \K definition of the language: KEVM~\cite{HSZ+18}. We compared the performance of the generated {\K}EVM interpreter against the most used EVM client: Geth -- the official Go implementation of EVM.

Each interpreter ran a selected set of tests from the official Ethereum test suite. The official test suite features three test primary categories:
\begin{itemize}
    \item \textbf{Blockchain tests} for testing the verification of a sequence of blocks.
    \item \textbf{State transition tests} for testing the verification of a single transaction.
    \item \textbf{VM tests} for testing the functionality of the EVM in isolation.
\end{itemize}

The official blockchain category groups general state tests into 58 subcategories.
We took 58 of these tests to evaluate the performance of each interpreter, comparing the overall wall time and VM time, the actual time spent executing EVM opcodes. We only dropped the `vmPerformance` tests from `VMTests` for the sake of reproducibility.


We also evaluated the implementations on a performance-focused subset of the
Blockchain test, for which the results are shown in \Cref{tab:geth-performance} and \Cref{tab:kevm-performance}. Each
of the implementations provides a different interface for testing; we
used the default test runner for each implementation to produce these results.
 \begin{itemize}
     \item For {\K}EVM, we used the \code{poetry pytest} implementation to execute the 58 \code{GeneralStateTests} from the Blockchain directory.

     \item For Go Ethereum, we used an instrumented version of the `go test` command to execute the same set of tests from the Blockchain directory in a single thread.
\end{itemize}



We used an instrumented version of {\K}EVM v1.0.675 with K v7.1.99 and Geth v1.13.14 to execute all tests.

\begin{table}[!ht]
    \centering
    \begin{tabular}{l|l|l}
        \textbf{Benchmark} & \textbf{Wall time} & \textbf{VM time} \\ \hline
        GeneralStateTests & 1072.95s & 531.40 \\
    \end{tabular}
    \caption{Performance of the {\K}EVM interpreter generated with \KL on Ethereum BlockchainTests} 
    \label{tab:kevm-performance}
\end{table}

The Go implementation of EVM has more than one execute mode, we decided to execute all and present all results here for the same of transparency.

\begin{table}[!ht]
    \centering
    \begin{tabular}{l|l|l|l|l}
        \multicolumn{1}{c}{} & &\textbf{Wall time} & \textbf{VM time} \\ \hline
        \textbf{Hash Mode} & \textbf{Snapshotter} & 415.348s & 199.015s \\
        ~ & \textbf{No Snapshotter} & 460.063s & 201.575s \\  \hline
        \textbf{Path Mode} & \textbf{Snapshotter} & 406.074s & 197.926s \\ 
        ~ & \textbf{No Snapshotter} & 446.882s & 392.253s \\ 
    \end{tabular}
    \caption{Performance of the Geth interpreter on Ethereum GeneralStateTests from BlockchainTests}
    \label{tab:geth-performance}
\end{table}

In the best case of Geth, {\K}EVM performs 2.68x slower, whereas in the worst case, {\K}EVM is only 1.35x slower than the most used EVM client considering the VM time of execution for both interpreters.


\subsection{Evaluation of 1K Swaps in Different Programming Language Interpreters}

The second benchmark we used to evaluate the performance of \KL generated interpreters uses an implementation of the UniSwap V2 \cite{Adams2020UniswapVC} contract. In particular, we measure the performance of 4 different executions of the swap operation between 2 different ERC20 tokens using this contract.

\clearpage





\lstdefinelanguage{Solidity}{
	keywords=[1]{anonymous, assembly, assert, balance, break, call, callcode, case, catch, class, constant, continue, constructor, contract, debugger, default, delegatecall, delete, do, else, emit, event, experimental, export, external, false, finally, for, function, gas, if, implements, import, in, indexed, instanceof, interface, internal, is, length, library, log0, log1, log2, log3, log4, memory, modifier, new, payable, pragma, private, protected, public, pure, push, require, return, returns, revert, selfdestruct, send, solidity, storage, struct, suicide, super, switch, then, this, throw, transfer, true, try, typeof, using, value, view, while, with, addmod, ecrecover, keccak256, mulmod, ripemd160, sha256, sha3}, 
	keywordstyle=[1]\color{blue}\bfseries,
	keywords=[2]{address, bool, byte, bytes, bytes1, bytes2, bytes3, bytes4, bytes5, bytes6, bytes7, bytes8, bytes9, bytes10, bytes11, bytes12, bytes13, bytes14, bytes15, bytes16, bytes17, bytes18, bytes19, bytes20, bytes21, bytes22, bytes23, bytes24, bytes25, bytes26, bytes27, bytes28, bytes29, bytes30, bytes31, bytes32, enum, int, int8, int16, int24, int32, int40, int48, int56, int64, int72, int80, int88, int96, int104, int112, int120, int128, int136, int144, int152, int160, int168, int176, int184, int192, int200, int208, int216, int224, int232, int240, int248, int256, mapping, string, uint, uint8, uint16, uint24, uint32, uint40, uint48, uint56, uint64, uint72, uint80, uint88, uint96, uint104, uint112, uint120, uint128, uint136, uint144, uint152, uint160, uint168, uint176, uint184, uint192, uint200, uint208, uint216, uint224, uint232, uint240, uint248, uint256, var, void, ether, finney, szabo, wei, days, hours, minutes, seconds, weeks, years},	
	keywordstyle=[2]\color{teal}\bfseries,
	keywords=[3]{block, blockhash, coinbase, difficulty, gaslimit, number, timestamp, msg, data, gas, sender, sig, value, now, tx, gasprice, origin},	
	keywordstyle=[3]\color{violet}\bfseries,
	identifierstyle=\color{black},
	sensitive=true,
	comment=[l]{//},
	morecomment=[s]{/*}{*/},
	commentstyle=\color{gray}\ttfamily,
	stringstyle=\color{red}\ttfamily,
	morestring=[b]',
	morestring=[b]"
}

\lstset{
	language=Solidity,
	backgroundcolor=\color{white},
	extendedchars=true,
	basicstyle=\footnotesize\ttfamily,
	showstringspaces=false,
	showspaces=false,
	numbers=left,
	numberstyle=\footnotesize,
	numbersep=9pt,
	tabsize=2,
	breaklines=true,
	showtabs=false,
	captionpos=b,
        linewidth=12cm,
	frame=single,
	frameround=tttt
}
\begin{lstlisting}[language=Solidity, label={lst:uniswapV2swap}, caption={UniswapV2SwapTest Solidity Code}, captionpos=b]
contract UniswapV2SwapTest {

    UniswapV2Swap private _uni;
    WETHMock private _weth;
    DAIMock private _dai;
    USDCMock private _usdc;

    function testSwapLoop() public {
        _weth = new WETHMock();
        _dai = new DAIMock();
        _usdc = new USDCMock();
        _uni = new UniswapV2Swap(address(_weth), address(_dai), address(_usdc));
        for (uint i = 0; i < 1000; i++) {
          testSwapSingleHopExactAmountIn();
	    }
    }

    function testSwapSingleHopExactAmountIn() public {
        uint256 wethAmount = 1e18;

        _weth.deposit{value: 2*wethAmount}();
        _weth.approve(address(_uni), 2*wethAmount);
        _dai.mint(address(this), wethAmount);
        _dai.approve(address(_uni), wethAmount);
        
        _weth.transfer(_uni.router().get_local_pair(address(_weth), address(_dai)), wethAmount);
        _dai.transfer(_uni.router().get_local_pair(address(_weth), address(_dai)), wethAmount);

        _uni.router().sync_local_pair(address(_weth), address(_dai));

        uint256 daiAmountMin = 1;
        uint256 daiAmountOut = _uni.swapSingleHopExactAmountIn(wethAmount, daiAmountMin);

        assert(daiAmountOut >= daiAmountMin);
    }
}
\end{lstlisting}

The \nameref{lst:uniswapV2swap} uses 3 ERC20 tokens and the Uni-swapV2Swap contract and implements 2 tests: 
\begin{itemize}
    \item \code{testSwapSingleHopExactAmountIn} responsible for testing a single swap operation between the ERC20 tokens \code{weth} and \code{dai}.
    \item \code{testSwapLoop} responsible for instantiating 3 ERC20 tokens and the Uni-swapV2Swap contract with them to call the test above 1,000 times.
\end{itemize}
The \code{testSwapLoop} is the main test we use for measuring performance in this benchmark.

As mentioned, in this experiment we are measuring 4 approaches:
\begin{itemize}
    \item Geth: The Go Official implementation of EVM 
    \item {\K}EVM: The \K official implementation of EVM.
    \item {\K}-Solidity without CSE: The \K implementation of the solidity semantics, \K-Solidity, without the CSE optimization.
    \item {\K}-Solidity with CSE: The same \K-Solidity semantics, but with the CSE optimization.
\end{itemize}

\paragraph{The CSE — Compositional Symbolic Execution\\} Optimization Technique in \K is originally used by Kontrol in its Symbolic Summarizer to identify common paths taken multiple times that can be saved as an axiom to be proved only once and then used to compose other proofs, saving several execution steps. 

In the context of concrete semantic-based execution, we use this idea in a bottom-up approach to compose multiple small execution steps, or “rewrite rules”, into a single step, that always performs the same operations as the underlying small steps would, regardless of the input. This single step becomes a new rewrite rule in the programming language semantics. Including these rules in the semantics results in fewer steps needed during program execution when these rules match, and thus to increased performance.

For this experiment, we manually searched for opportunities to apply this technique to compose semantics rules that correspond to multiple steps of the original semantics rules. All opportunities that were able to compose at least 30 execution steps into one single rule were taken. This can and will be automated.

Using CSE, we will show that we can now outperform Geth execution for the benchmark of 1,000 swaps by more than 1.57x. One of the most amazing characteristics of this technique is that it is language-agnostic, so all future semantics developed using the \K Framework and executed within the \KL can use it for optimizing its execution.


\begin{table}[!ht]
    \centering
    \label{tab:semantics-performance}
    \begin{tabular}{l | c | c | c}
    
        \textbf{Implementation} & \textbf{Time to run 1K swaps} & \textbf{Overhead} & \textbf{Speed} \\ \hline
        Geth & 0.241s & 1x & 100\
        K[Solidity] with CSE & 0.153s & 0.63x & 157.5\
        K[Solidity] & 0.266s & 1.10x & 90.6\
        KEVM & 8.787s & 36.5x & 0.03\
    \end{tabular}
    \caption{Performance of different approaches to execute 1K Swaps}
\end{table}

\Cref{tab:semantics-performance} shows the performance of the four different approaches to running \code{testSwapLoop}. We considered Geth as the baseline, and we can see that in this test {\K}EVM doesn't deliver the same performance we observed in the Ethereum test suite; we considered this an outlier example. The Solidity semantics, on the other hand, reaches a comparable performance with Geth even without the CSE optimization. Finally, the Solidity semantics with CSE show us the outstanding potential that only the semantics-based execution through the \KL is able to deliver to the users by outperforming the most used Ethereum client, being 57.5\

These tests were executed in the same machine with a 13th Gen Intel\textsuperscript{\tiny\textregistered} Core™ i9-13900K 24-Core CPU (32 threads), with Intel\textsuperscript{\tiny\textregistered} UHD Graphics 770 (Integrated with CPU) and 64 GB RAM.

Geth experiments were conducted using its \code{1.13.14} version and Go \code{v1.22.0}.

Solidity and KEVM experiments were conducted using \K \code{v7.1.166}. KEVM used its version \code{1.0.678}. 

\section{Conclusion}
The \K framework is a powerful method for semantics-based language development; a full suite of specialized tools can be extracted automatically by \K from a single definition of a language's formal operational semantics. One of these tools is a concrete interpreter, for which execution performance is an important goal for \K.

This paper has provided a high-level overview of \KL, the backend for compiling \K language definitions into fast concrete interpreters. It has also motivated and presented our innovations towards addressing one of the costliest bottlenecks for the generated interpreters' performance: compilation of pattern matching problems to native code. The compilation method presented in this paper extends the state-of-the-art method for decision tree-based compilation with support for a practical subset of ACUI pattern matching, supporting the use of fast runtime collection data structures by \K language definitions. Additionally, it supports conditional patterns and variable bindings.

Our bespoke decision tree-based compilation algorithm is shown to result in exceptionally performant interpreters for \K definitions. The generated interpreter from a \K definition of EVM is between 1.35x to 2.68x slower than GEth, the most widely used interpreter for EVM in production settings. Moreover, using CSE, a technique uniquely available to semantic-based execution, our generated interpreter outperforms GEth: GEth is 1.57x slower than our CSE interpreter.

This paper does not cover the full technical depth of \KL that has accrued over the course of our work on it. Some aspects of the tool that have not been described in detail in this paper include the efficient unsorted term rewriting engine used to execute programs, and a novel pattern-matching optimization that takes advantage of \K-specific knowledge to trade off space and time during the compilation process.

\clearpage
\bibliography{refs}

\end{document}
```

## The Pi Squared (π²) White Paper Version 1.0

**Authors:** Pi Squared Inc.

**Date:** February 2025

### LaTeX Source

```latex
\documentclass{article}

\usepackage{amsmath,amssymb,amsthm}
\usepackage{booktabs}
\usepackage{graphicx}
\usepackage{hyperref,cleveref}
\usepackage{tikz}
\usepackage{url}
\usepackage{xspace}


\newcommand{\code}[1]{\texttt{#1}}

\title{The Pi Squared ($\pi^2$) White Paper\\\Large Version 1.0}
\author{Pi Squared Inc.}
\date{February 2025}


\newcommand{\K}{\ensuremath{\mathbb{K}}\xspace}
\newcommand{\ld}{.\,}
\newcommand{\To}{\Rightarrow}
\newcommand{\init}{{\textit{init}}}
\newcommand{\final}{{\textit{final}}}
\newcommand{\KL}{LLVM-\K}
\newcommand{\ulm}{ULM}

\begin{document}
\maketitle

\abstract{
Pi Squared is set to massively disrupt the state-of-the-art and revolutionize Web3 by making the following features mainstream:
\begin{enumerate}
    \item {\textbf{Universality}:} Programs will be written in any programming languages, virtual machines (VMs), or instruction sets that applications choose.  Developers will no longer need to learn poorly designed languages only because that's the only way to write Web3 programs.  Program executions will be proved using any mathematical or cryptographic proof systems that the applications choose.  They will no longer need to take the risk of introducing bugs and increasing complexity by translating their code to restricted or obscure low-level languages, only because that is the only way to use existing zero-knowledge virtual machines (zkVMs) to prove their executions.  And finally, applications will choose which consensus fits them best: can be a total-order consensus, like in blockchains, rollups, appchains, etc., or a partial-order or even no order at all, like in voting, auction, or trading applications.  Applications will no longer need to squeeze their transactions in a global total order across all the applications in the universe, through a narrow pipe.
    \item {\textbf{Correctness}:} All the above will be \textit{correct by construction}.  Specifically, once a formal semantics of the language is provided\footnote{A formal semantics is a fundamental requirement in any setting where correctness matters.  Without a formal semantics we cannot even define what correctness means.}, all the execution and proving tools for that language are automatically derived and everything they do is provably and verifiably correct at no additional effort.  No formal verification of translators, compilers, interpreters,
    VMs, zkVMs, etc., will be required.  
    \item {\textbf{Performance}:} No, universality and correctness should not and will not come at the cost of performance.  Quite the contrary.  After more than fifty (50) years of sustained research and engineering, the formal semantics domain has reached a level of maturity and tooling that allows semantics-based execution to match and even outperform the traditional, ad-hoc manual implementations of compilers and interpreters/VMs.  
    The future is even brighter because formal semantics enables a series of optimizations that are simply not possible using traditional approaches, such as symbolic semantic summarization of basic blocks or using formal verification to non-asymptotically compress or even eliminate computation.
\end{enumerate}

This paper gives a high-level overview of Pi Squared and of its three major technical components, namely the K Framework, Proof of Proof, and the Universality Stack, focusing on {\em what} and {\em why}.  For {\em how}, the reader is encouraged to dive deeper into our three component-specific white papers as well as our research and peer-reviewed publications at 
\href{https://pi2.network/papers}{\texttt{pi2.network/papers}}.
}

\renewcommand{\contentsname}{Table of Contents}
\setcounter{tocdepth}{3}
\tableofcontents

\newpage

\section{Introduction}

Web3 infrastructure yearns for more universality and trustworthiness.
Current solutions are constrained by technological limitations 
such as specificity to particular computing models (e.g., programming languages, virtual machines, or instruction sets), reliance on error-prone translations among languages, lack of provable correctness, and slow performance.
In this paper, we present Pi Squared and its three core technological innovations
that address the above technological limitations:
\begin{itemize}
\item \textbf{\K Framework}: A universal programming language framework that enables fast and correct-by-construction computation for programs written in any programming language or virtual machine.
\item \textbf{Proof of Proof}: A universal verifiable computing framework designed to generate complete, rigorous, and machine-checkable proofs for the execution of programs in any programming language.
\item \textbf{Universality Stack}: The Pi Squared universality stack that
consists of the following three components: the universal settlement layer (USL),
the universal language machine (ULM), and the universal consensus protocol (UCP). 
\end{itemize}

\subsection{\K Framework}

Traditional programming and computing space are plagued by (programming) 
language barriers. 
On the one hand, we have a large and increasing number of programming languages as new
domains, new applications, and new demands arise,
such as the Ethereum virtual machine's bytecode language for the Ethereum network. 
On the other hand, the development of the tool support of programming languages
is still managed the same way as half a century ago: 
People develop specific tools 
(compilers, interpreters, formal verifiers, and ZK provers) 
for specific programming languages, 
virtual machines, and/or architecture set instructions. 

Language-specific tools lead to language-specific tech stacks and infrastructure,
which lead to language-specific ecosystems,
and eventually, result in a huge programming language barrier
in the current programming and computing space. 
Web2 programmers must first learn how to write code in Solidity.
Game developers must first translate their application to a specific zkVM implementing hundreds of thousands or lines of code that is blindly trusted, for which compilers may not even exist. 
Otherwise, they are effectively excluded by the emerging Web3 community. 
Language barriers make learning, development, deployment, and maintenance
more expensive,
increasing fragmentation and decreasing interoperability. 

The \href{https://kframework.org}{\K framework} breaks language barriers in the programming space using 
\emph{formal semantics}. 
\K allows anyone to define the formal semantics
of any programming language, virtual machine, or architecture set in it.
Furthermore, from the formal semantics, \K automatically generates all the language tools in a correct-by-construction manner. 
This way, \K fundamentally changes how the tool support of programming languages
is developed. 
Instead of working on all the language-tool combinations, 
\K separates language design and tool implementation.

\K was invented at University of Illinois at Urbana-Champaign in 2003
by Prof. Grigore Rosu, the founder of Pi Squared,
and has been continuously improved since then.
As of today, 
\K has been successfully applied to define the formal semantics of 
C~\cite{c-semantics}, 
Java~\cite{java-semantics}, 
JavaScript~\cite{kjs}, 
Python~\cite{python-semantics}, 
Rust~\cite{krust-shanghai,krust-singapore},
EVM~\cite{kevm}, 
WASM~\cite{kwasm}, 
x86-64~\cite{DPK+19}, 
and more.
\K constitutes the infrastructural foundation of a unique approach 
to verifiable computing,
initiated and developed at Pi Squared, called Proof of Proof.



\subsection{Proof of Proof}

Verifiable computing is poised to become the cornerstone of trust and correctness in decentralized Web3 infrastructure. 
Pi Squared's Proof of Proof is an approach to verifiable computing that puts
special emphasis on \emph{universality} and \emph{correct-by-construction}, 
which we term ``Verifiable Computing 2.0.''
Universality means that Proof of Proof is a framework that works for all programming
languages, virtual machines, and instruction set architectures. 
Correct-by-construction means that Proof of Proof directly uses the mathematical models
of the systems-being-verified to construct the correctness certificates, so there is
no modeling gap between the systems and their certificates. 
Both universality and correct-by-construction are a natural consequence of the semantics-based approach of Proof of Proof,
which is directly built on top of the \K framework
and the formal semantics of various programming languages and virtual machines in it. 

Proof of Proof stands for zero-knowledge (ZK) proofs of math proofs. 
As its name suggests, Proof of Proof involves two types of proofs:
math proofs and ZK proofs. 
Given a program in a programming language,
we first generate a math proof 
that is fast to generate, easy to check, but large to store on-chain. 
Then, we generate a ZK proof for the said math proof 
as a much smaller cryptographic artifact that is more suitable for
being checked and stored on-chain. 
Both the math proof and the ZK proof are directly based on a mathematical model of
the program and the underlying language, known as their formal semantics. 

The key idea of Proof of Proof is to separate three underlying concerns: \textit{computation}, \textit{verification}, and \textit{cryptography}.
Firstly, recent developments in executable formal semantics and \K 
allow us to efficiently and completely automatically reduce computation to math proofs.  Proof of Proof only needs one language for encoding math proofs in order to 
support computations done with any programs in any programming languages (PLs) or virtual machines (VMs).
Secondly, the math proofs are checked, not trusted, with a disarmingly simple and small proof checker of only a few hundred lines of code.  
No (usually complex and error-prone) compilers, interpreters, or even formal verifiers
need to be trusted, either.
All become just instruments to assist the generation of math proofs.
The math proofs, and not the tools that generate them,
are the ultimate correctness arguments for the computations from which they were derived.
Finally, recent developments in cryptography and ZK (e.g., SNARK and STARK) allow us to implement the math proof checker 
as a cryptographic circuit, which effectively allows us to produce ZK proofs 
for the integrity of the math proofs,
and thus, (ZK) Proofs of (math) Proofs. 

\subsection{Pi Squared's Universality Stack}

Building on top of \K and Proof of Proof,
Pi Squared proposes the following universality tech stack that consists of
the following three components:
\begin{itemize}
    \item \textbf{Universal Settlement Layer (USL)}, a common layer for any applications and blockchains to submit, verify, settle, store, and use claims
    across platforms and ecosystems, compatible with various proof mechanisms and systems; 
    \item \textbf{Universal Language Machine (ULM)}, a truly universal execution layer
    that allows developers to write and deploy smart contracts in all programming languages, including Bring Your Own Language (BYOL), and enables interactions
    among the smart contracts;
    \item \textbf{Universal Consensus Protocol (UCP)}, a fast and novel 
    consensus protocol that enables nodes to agree on a set of independent values without imposing a global total order, 
    thereby facilitating massively parallel processing and validation.
\end{itemize}

\subsubsection{Universal Settlement Layer (USL)} 

Pi Squared's USL aims to address the issue of fragmentation and interoperability 
in Web3.
The current monolithic design of blockchains means that a blockchain handles
all the core tasks on the same layer, including
providing consensus and security, 
guaranteeing data availability, and executing transactions.
It makes communication \emph{within} the blockchain easy and convenient,
but communication \emph{across} various blockchains difficult and expensive. 
Each blockchain becomes an isolated information island. 

USL is a common layer that brings together various applications running on different blockchains and ecosystems,
using \emph{claims}. 
Claims are a core mathematical concept.
They refer to anything provable or verifiable. 
Transaction execution is captured by computation claims. 
State queries are captured by state query claims. 
Consensus validation is captured by consensus claims. 
Vetted information (e.g., knowledge or data) is captured by information claims. 
In short, all statements are formally represented as claims, and they are submitted to the USL
together with their corresponding proofs for verification, settlement, storage, and usage. 

Different types of claims have different types of proofs, and the USL is compatible
with any proof mechanisms. 
Computation claims can be verified against their math and/or ZK proofs, generated by any zkVMs at the choice of the users, or by re-executing the code 
using a trusted software configuration and hardware setup. 
State query claims can also be verified against their math proofs, ZK proofs, or by re-executing the corresponding pure/view functions.
Consensus claims can be verified by validating the blockchain's block headers. 
Information claims can be verified using digital signatures. 
The USL nodes are thus configurable and compatible with any of the above proof mechanisms. 

A remarkable and unique characteristic of the USL claims 
is that they are self-contained and can be verified independently. 
Neither the verification process nor the verification result of a USL claim depends on
any data, information, or state that is not given within the claim itself. 
Claims are the minimal self-contained and self-dependent verification unit. 
Therefore, once a claim is verified and settled by a USL node, it is added
to the ``valid claim set'' maintained by the USL node, which constitutes the node's runtime state. 
The valid claim set is a monotonic set that only increases as time passes by,
which gives birth to a faster consensus protocol which we term as the Universal Consensus Protocol (UCP). 

Any application running on any blockchain 
can query the USL about the claims 
about any other application on any other blockchain.
If a claim has been verified, settled, and stored on the USL, the USL returns a corresponding
\emph{membership proof}, which proves that the said claim indeed belongs to the valid claim set maintained by the USL node. 
No computation or complex consensus mechanism matters here, because the membership proof is simply a verifiable certificate for the simplest mathematical structure---a set---and the simplest mathematical relation---whether an object (claim) belongs to a set. 
Membership proofs are one of the simplest and most succinct verifiable certificates to verify and store on-chain. 

USL addresses the issue of Web3 fragmentation and interoperability by proposing a novel
topological structure among blockchain ecosystems.
Instead of building ad-hoc bridging-like solutions for any two blockchains and/or applications, 
the USL imposes a spoke–hub distribution paradigm that connects and interconnects various blockchains and ecosystems
via claims and membership proofs, in a uniform and universal way. 



\subsubsection{Universal Language Machine (ULM)} 

Pi Squared's ULM aims to leverage the universality of \K and Proof of Proof and bring this universality to Web3, to engage with a much larger community of Web2 developers who are not necessarily familiar with particular Web3 programming languages and technology stacks.

The ULM is an open-source execution layer that enables developers to create, deploy, and interact with smart contracts written in any programming language.
Unlike existing blockchain systems that require all contracts to be written in a single prescribed language, the ULM natively supports multiple languages.
Furthermore, the \ulm{} can be dynamically extended and allows adding new programming languages on-the-fly. 
This way, the ULM enables diverse language ecosystems to coexist and interoperate on a single platform.
This not only empowers developers to use the most suitable language for their projects; it also makes smart contract development more accessible to the millions of developers who are unfamiliar with existing Web3 languages.

Pi Squared is building the \ulm{} platform because we are convinced that its universal, formally grounded approach represents a significant advancement in the blockchain space that improves flexibility, developer experience, and security. At the same time, it paves the way for future innovation in decentralized applications, fostering a more universal approach to blockchain programming.

\subsubsection{Universal Consensus Protocol (UCP)} 

Pi Squared's UCP is a natural innovation in consensus mechanisms 
based on the unique characteristics of the USL, especially its self-contained
and independently-verifiable claims. 
Traditional counterparts in the current blockchain systems have focused 
on ordering transactions or blocks, 
introducing complexity and constraints that are often unnecessary for many decentralized applications.
The UCP, on the other hand, enables nodes to agree on a set of independent values (i.e., claims)
without imposing an order, thereby facilitating massively parallel processing and validation, which are critical for scalability and efficiency. 

Pi Squared's UCP decouples core consensus from application-specific requirements, particularly application-specific safety properties. These include the absence of forks in blockchain histories, prevention of double-spending in payment systems, ensuring only valid bids in auctions, or counting valid votes in voting systems. Such properties are the responsibility of the application to prove and are independent of the core consensus mechanism. This separation enables the design of a universally generic consensus protocol that serves as a unifying framework for diverse applications, including blockchain-based smart contracts, distributed databases, scientific computation validations, and multi-agent coordination systems. Furthermore, it facilitates the creation of scalable systems unbounded by any constraints imposed by the underlying protocol.

\subsubsection{Putting It All Together}

Pi Squared aims to empower Web3 developers to build interoperable and trust-minimized applications across 
all blockchain environments and ecosystems. 
By leveraging the \K framework,
Proof of Proof, and the Universality Stack,
dApp builders can unlock new possibilities for decentralized applications, move beyond the current silos of blockchain networks, and embrace an emerging new paradigm for trustless computing in crypto applications and beyond.
Through Verifiable Computing 2.0, Pi Squared is paving the way for a more unified, secure, and scalable future for Web3 infrastructure, and will continue playing
a pivotal role in shaping the next generation of decentralized computing.




\begin{center}
\noindent\fbox{\parbox{0.8\textwidth}{
Due to space limits, more technical details, experiments, analyses, and discussions 
are given in our technical whitepapers (see \Cref{sec:further}). 
}}
\end{center}

\section{\K Framework}
\label{sec:k}

\href{https://kframework.org}{\K framework} is a formal programming language semantics framework
that lies at the core infrastructure of Pi Squared.
It enables two things.
Firstly, \K allows to define, in a uniform and executable way,
the \emph{formal semantics} of any programming language.
Secondly, from the formal semantics of a language, \K automatically generates fast execution tools
for that language.

The formal semantics of a programming language is a mathematical definition of that language
and of all the behaviors of all the programs in that language.
Therefore, if one has the formal semantics of a programming language, then one has, in theory,
all the information needed to execute any program written in that language.
A formal semantics is similar to a language specification in that both describe
the expected behaviors of the programs.
The difference is that formal semantics is also mathematically rigorous and unambiguous,
and thus can be directly used for formal reasoning and proving.

\begin{figure}
\centering
\includegraphics[width=0.6\textwidth]{figs/k.png}
\caption{\K Framework}
\label{fig:K}
\end{figure}

Using their formal semantics, \K unifies programming languages.
As shown in \Cref{fig:K},
the center bubble
represents the formal semantics of an arbitrary programming language,
and the bubbles around represent the language tools that are automatically generated
directly from the formal semantics by \K.
This way, 
\K enables a \emph{separation of concerns} between
programming language design and programming language tool implementation.
Language designers can laser focus on designing and defining their languages (and tools) rigorously,
and let \K automatically generate all the tools needed to execute and reason about programs.

\subsection{\K Specifications}
\label{sec:kspec}

The primary input into the entire \K framework is a formal semantics of a programming language,
represented as a \K specification.
At the highest level, \K defines a programming language using three different pieces:
\begin{itemize}
\item \textbf{System primitives}: The base datatypes used during system operation, such as numbers, lists, maps, and so on.
\item \textbf{System configuration}: A nested tuple or record over the system primitives that gives a complete snapshot of the running system at any given runtime moment; can be seen as a semantic core dump.
\item \textbf{System behavior}: A set of rules that modularly specify all possible evolutions and behaviors of the system.
\end{itemize}
As a result, the \K specification of a programming language
is organized by a collection of \emph{declarations}
that correspond to the three pieces above:
\begin{itemize}
\item \emph{Syntax declarations} encode the system primitives.
\item \emph{Configuration declarations} encode the system configurations.
\item \emph{Context and rule declarations} encode the system behavior.
\end{itemize}

\K has been successfully applied to define the formal semantics of 
C~\cite{c-semantics}, 
Java~\cite{java-semantics}, 
JavaScript~\cite{kjs}, 
Python~\cite{python-semantics}, 
Rust~\cite{krust-shanghai,krust-singapore},
EVM (the bytecode language of Ethereum VM)~\cite{kevm}, 
WASM~\cite{kwasm}, 
x86-64~\cite{DPK+19}, 
and many others.

\subsection{\K Process}
\label{sec:kprocess}

Once we obtain the \K specification of the formal semantics of a programming language,
we pass it to \K as the primary input to generate all the language tools.
For efficiency, the \K spec is first desugared into an intermediate representation called Kore.
The Kore spec is used to do:
\begin{itemize}
\item Parsing and pretty-printing.
\item Concrete and symbolic program execution using the \K specification.
\item Symbolic reasoning, theorem proving and formal verification, i.e., proving claims about programs against the \K specification.
\end{itemize}
The above \K process is shown in \Cref{fig:kprocess}.

\begin{figure}
\centering
\includegraphics[width=0.7\textwidth]{figs/kprocess.png}
\caption{\K Framework Process}
\label{fig:kprocess}
\end{figure}

\subsection{\K Backend}
\label{sec:kbackend}

LLVM-\K is a backend of \K that powers the \K execution process in \Cref{fig:kprocess},
specialized for concrete (non-symbolic) program execution.
It enables fast and correct-by-construction program execution for all languages, by
using their formal semantics.

As shown in \Cref{fig:kllvm},
the LLVM-\K backend generates fast, native interpreter binaries in LLVM IR for programming languages
from their formal semantics in \K.
The input to the LLVM-\K backend
is the Kore specification of a programming language, obtained by compiling the
\K specification of the language,
where Kore is the internal intermediate representation format of \K.
The output of the LLVM-\K backend is an efficient interpreter for the programming language
as an LLVM IR.

\begin{figure}
\centering
\includegraphics[width=0.7\textwidth]{figs/kllvm.png}
\caption{LLVM-\K Architecture}
\label{fig:kllvm}
\end{figure}

\K is a rewrite-based system.
Formal semantics are given in terms of \emph{rewrite rules}, which specify how to go from
the current configuration to the next configuration.
This process is called \emph{rewriting}, and is driven by \emph{pattern matching}.
For any given configuration, a rewrite rule is selected that matches the said configuration.
During pattern matching,
the variables of the rewrite rules are given concrete values
according to the configuration that they are matched against.
This mapping from variables to concrete terms is called a \emph{substitution}.
After the pattern has been matched and we have a substitution,
we can rewrite the current configuration to the next one by
applying the substitution to the rewrite rule.

The LLVM-\K backend implements a high-performance pattern matching algorithm that is specialized to
handle large formal semantics of programming languages with
potentially thousands of rewrite rules to select from.
The core algorithm is based on a modified version of an
existing algorithm for code generation of efficient pattern matching, described in~\cite{Maranget2008}.
The algorithm represents the left-hand sides of the rewrite rules as matrices,
and processes these matrices into a decision tree.
Starting from the root of the tree, each node is a check on a specific position of the given term and the children of the node represent how to continue checking given the result of the parent’s check.
A leaf node corresponds to a specific rewrite rule that matches when the leaf node is reached through a series of checks on the given term.
The algorithm is designed to be customized with various heuristics in order to lead to generation of decision trees that minimize the number of checks needed to match a given term.

\subsection{\K Performance}

Semantics-based execution is fast. 
The interpreters that are automatically generated by \KL can reach comparable performance against
hand-written interpreters. 
Furthermore, semantics-based execution enables a number of optimization technologies
that are simply not possible in a traditional compiler-based approach. 

A typical example is \emph{compositional symbolic execution} (CSE). 
Given a formal semantics of a programming language $L$ and a program $P$,
the CSE automatically derives a new semantics $L[P]$, which is the partial evaluation 
of $P$ using the semantics of $L$. 
In other words, $L[P]$ is a new language and a new semantics that is specialized, and thus optimized, with respect to
the program $P$. 
All the basic blocks of $P$ that require multiple rewrite rules to execute using the semantics $L$
will be automatically summarized into their corresponding rewrite rules in $L[P]$, and thus each basic block is executed in one step, using the new CSE-ed version of the semantics. 

We have evaluated the performance of \KL on two benchmark set:
the blockchain tests in the Ethereum test suite~\cite{ethereum-tests}
and the execution of 1,000 swap operations on an ERC20 token~\cite{1kswapscode}. Our results are 
preliminary but positive.
We find that on EVM, \K without CSE is merely 1.35x slower than \code{geth}, 
the official implementation of EVM~\cite{geth} in Go and the most adopted Ethereum client.
Furthermore, if we enable the CSE, 
the language interpreters generated by \K outperform \code{geth} by 1.58x.


\section{Proof of Proof}
\label{sec:pop}

Proof of Proof is a universal verifiable computing framework for all programming languages.
Its universality comes from \K and formal semantics,
and the usage of mathematics and proofs
in specifying and reasoning about programs and languages.
In other words,
computation \emph{is} proof:
\begin{equation*}
\boxed{\text{Computation}} = \boxed{\text{Proof\vphantom{Cp}}}
\end{equation*}


\subsection{Main Workflow}

\begin{figure}
\centering
\includegraphics[width=1\textwidth]{figs/pop.png}
\caption{Proof of Proof Workflow}
\label{fig:pop}
\end{figure}

\Cref{fig:pop} shows the entire Proof of Proof workflow. It has two phases.
In the first phase, we generate a mathematical proof that verifies that
a given execution trace of a program is indeed correct with respect to the formal semantics of the programming language.
Formally,
\begin{equation}
\Pi \colon \Gamma^L \vdash \varphi_P \qquad\text{where}
\label{eq:mathproof}
\end{equation}
\begin{itemize}
    \item $\Pi$ is the mathematical proof
    \item $\Gamma^L$ is the formal semantics of some programming language $L$
    \item $\varphi_P$ is the logical formula that specifies the correctness (w.r.t. $L$) of an execution trace
of a program $P$.
\end{itemize}
 
The symbol ``$\vdash$'' is called the entailment relation.
\Cref{eq:mathproof}
thus states that the mathematical proof $\Pi$ verifies the execution trace of program $P$
as specified by $\varphi_P$ with respect to the underlying formal semantics $\Gamma^L$.
The process of generating the mathematical proof $\Pi$
is called Math Proof Generation, and is depicted at the bottom left of \Cref{fig:pop}.

In the second phase of Proof of Proof, we generate a zero-knowledge proof (ZKP) that verifies the
(constructive) existence of a mathematical proof, for a given program execution claim.
Formally,
\begin{equation}
\pi \colon \text{ there exists $\Pi$ such that } \Pi \colon \Gamma^L \vdash \varphi_P
\label{eq:zkproof}
\end{equation}
In other words, we regard \Cref{eq:mathproof}
as a ternary relation among $\Pi$, $\Gamma^L$, and $\varphi_P$, and regard $\Pi$ is a private argument.
The zero-knowledge proof $\pi$ verifies the \emph{existence} of a mathematical proof for a given
execution trace of a given program, and thus forms an indirect certificate to computation.

Proof of Proof is thus an approach to verifiable computing
via two phases and two different types of proofs: mathematical proofs first, followed by zero-knowledge proofs.
In this order, not mixed.
Mathematical proofs are generated for the target execution traces based on formal semantics,
and zero-knowledge proofs are generated to show the existence of the mathematical proofs.
Hence, we name the approach ``Proof of Proof'':
\begin{equation*}
\boxed{\text{Proof of Proof}} = \boxed{\text{ZK Proof of Math Proof}}
\end{equation*}

\subsection{Math Proof Generation}

Math Proof Generation is the process of generating the mathematical proofs
for a given execution trace of a program using directly
the formal semantics of the underlying programming language.
The execution of the program is carried out by \K and the LLVM-\K backend,
as explained in \Cref{sec:k}.
Math Proof Generation consists of four main components:
\begin{enumerate}
\item  A universal logical foundation.
\item Proof hints.
\item Proof generation procedures.
\item Math proof checkers.
\end{enumerate}

The universal logical foundation that powers Proof of Proof is \emph{matching logic}
\cite{matchinglogichomepage}. 
All \K specifications correspond to logical theories of matching logic
and all \K tools, including the LLVM-\K backend,
are formally specified by matching logic formulas --- and this process is automatic.

Proof hints are the necessary information that \K generates on-the-fly
to facilitate the generation of the mathematical proofs,
including
the complete execution trace with all the intermediate configuration snapshots
as well as the information about how the rewrite rules have been matched and applied.
Proof hints are logs of the execution of the \K-generated interpreters.
Once generated, proof hints are passed into the proof generation procedures to generate the corresponding mathematical proofs.

Suppose the execution trace has the form $\varphi_1, \varphi_2,\dots,\varphi_n$.
Here, we write $\varphi_1,\varphi_2,\dots,\varphi_n$ to mean the intermediate configurations
that constitute the entire execution trace.
The corresponding mathematical proof
$\Pi \colon \Gamma^L \vdash \varphi_1 \To \varphi_n$ consists of four components:
\begin{enumerate}
\item The formalization of matching logic and its entailment relation ``$\vdash$''.
\item The formalization of the formal semantics $\Gamma^L$.
\item The proofs of all one-step executions, i.e.,
$\Gamma^L \vdash \varphi_i \To \varphi_{i+1}$ for all $i$.
\item The proof of the target trace
$\Pi \colon \Gamma^L \vdash \varphi_1 \To \varphi_n$.
\end{enumerate}
It should be noted that the mathematical proof as shown above has a linear structure
that enables proof checking in parallel.
Indeed, the formalization of matching logic and its entailment relation is
general, and is not specific to a programming language or a program,
so it can be proved once and for all.
The formalization of the formal semantics $\Gamma^L$ can be reused for all programs written
in the language $L$.

A math proof checker is a program that checks whether a mathematical proof
indeed verifies a mathematical claim.
As shown in \Cref{fig:pop}, we support two proof checkers for two proof formats.
The first is a math proof checker based on \href{https://metamath.org}{Metamath}, which has only 200 lines of code and thus forms a minimal trust base of Proof of Proof.
The second is a custom math proof checker based on our recent block model format, which is specialized
for the most efficient generation of ZK proofs.

\subsection{Zero-Knowledge Proof Generation}

Recall that zero-knowledge proof (ZKP) generation is the process of generating
a ZKP $\pi$ as shown below:
\begin{equation*}
\pi \colon \text{ there exists $\Pi$ such that } \Pi \colon \Gamma^L \vdash \varphi_P
\end{equation*}
In other words, we are generating ZKPs for the existence of a mathematical proof of a given, public
mathematical claim.

A generic ZK proof system designed to verify a particular computation
typically requires that the computation be specified via \textit{arithmetization}.
This reduces the computation into some ZK primitives, such as a system of algebraic equations or polynomials
over a finite field.
On the other hand, a zero-knowledge virtual machine (zkVM) verifies computations described by a program that runs on a virtual machine, and thus allows programs written in higher-level languages,
even programs not initially designed with verifiable computing in mind,
to be used in ZKP systems.

Pi Squared pursues both approaches at the same time and enables ZKP generation
via both existing zkVMs for best compatibility and via our own block model
for best arithmetization efficiency.
We discuss both.

\subsubsection{ZKP Generation via Existing zkVMs}

zkVMs are a type of software that supports producing ZKPs
of execution for some target language, for example,
RISC-V or the Ethereum VM instruction set.
By implementing the math proof checkers (see \Cref{fig:pop})
in a zkVM, we obtain an instance of Proof of Proof whose output verifiable certificates can be
directly produced and checked by the zkVM.

We have implemented
the same Metamath-based math proof checker
in seven different zkVMs: Cairo, Jolt, Lurk, Nexus, RISC Zero, SP1, and zkWASM.
Each consists of a guest program that runs on a specific virtual machine
and a host program, which is our interface to run the guest,
providing input for it and processing its output.

Among the seven zkVMs, five of them, namely Jolt, Nexus, RISC Zero, SP1 and zkWASM provides a Rust compiler.
For these Rust-based systems, we have developed and used a shared library.
Cairo and Lurk use domain-specific languages, namely the Cairo language and LISP.
We have implemented the same Metamath-based math proof checker in Cairo and Lurk,
but their code base was developed independently of the Rust code base and independent of each other.

Among the seven zkVMs, four of them have dedicated GPU support,
namely RISC Zero, zkWASM, SP1, and Cairo.
At the time of writing, January 2025, we were able to enable the GPU support on RISC Zero, SP1 and zkWASM.
GPU support on Cairo is a work in progress.

Our implementation and experiments are based on the following versions of the zkVMs:
\begin{itemize}
\item \textbf{Cairo} (the lambdaworks prover): Main branch, commit \href{https://github.com/lambdaclass/lambdaworks/commit/a591186e6c4dd53301b03b4ddd69369abe99f960}{a591186}
\item \textbf{Jolt}: Main branch, commit \href{https://github.com/a16z/jolt/commit/3b142426d9648299d9c6912e7e1b4698cf91491b}{3b14242}
\item \textbf{Lurk}: Main branch, commit \href{https://github.com/lurk-lab/lurk/commit/57c48b987a94ba1f9752408a0990882c9f4f506b}{57c48b9}
\item \textbf{Nexus}: Version \href{https://github.com/nexus-xyz/nexus-zkVM/releases/tag/v0.2.3}{0.2.3}
\item \textbf{RISC Zero}: Version 1.0.5
\item \textbf{SP1}: Dev branch, commit \href{https://github.com/succinctlabs/sp1/commit/2c7868364cb832531e8cafd258aa06fbab079459}{2c78683}
\item \textbf{zkWASM}: Main branch, commit \href{https://github.com/DelphinusLab/zkWasm/commit/f5acf8c58c32ac8c6426298be69958a6bea2b89a}{f5acf8c}
\end{itemize}

\subsubsection{ZKP Generation via Pi Squared's Block Model}

Generating ZKPs via zkVMs inevitably introduces extra complexity and overhead, due to encoding,
translation, and compilation.
A theoretically more efficient approach is to develop a ZK front-end that is specialized in math proof checking.
Pi Squared's block model is an approach for more efficiently ZK-proving math proofs.
The block model design is documented in
the ``\href{https://pi2.network/papers/proof-of-proof-whitepaper}{Proof of Proof white paper}'' while its related tool support
is a work in progress.


Pi Squared's block model is an intermediate computation model that is suitable for expressing
mathematical proof systems and can be implemented in an AIR/Plonkish arithmetization.
It also targets at connections with R1CS-native backends, and recursive SNARKs, and folding schemes.
The key observation of the block model
is that lookup arguments can more directly
support the task of checking that the hypotheses of math proof steps are conclusions of other steps, without building up a full RAM (or ROM) abstraction as for a zkVM.
Initial estimates based on theoretical and practical modeling of our math custom ZK circuit put it at about $1000\times$ faster than the off-the-shelf zkVM approach.



\section{Pi Squared's Universality Stack}

On top of \K and Proof of Proof,
Pi Squared proposes the universality tech stack that consists of 
Universal Settlement Layer (USL),
Universal Language Machine (ULM),
and Universal Consensus Protocol (UCP). 

\subsection{Universal Settlement Layer (USL)}

\begin{figure}
\centering
\includegraphics[width=1\textwidth]{figs/usl.png}
\caption{Universal Settlement Layer (USL) Architecture}
\label{fig:usl}
\end{figure}

Pi Squared's USL is a distributed service that allows users to submit, verify, store, settle, and use claims,
as shown in \Cref{fig:usl}.
The central component of the USL is that of \emph{claims}. 
Claims can be anything mathematically provable and can be proved by any type of proof.
Users submit a claim and 
its corresponding proof to the USL, and the nodes of the USL validate the claim by checking its proof.
The USL is compatible with any proof mechanism. 
It allows validation-by-re-execution, which is the canonical computation validation approach in most of the state-of-the-art layer-1 blockchains. 
It allows validation-by-proof-certificates, where the certificates
can be the math/ZK proofs generated by Proof of Proof or any zkVMs. 
This way, the USL enables verifiable computing, 
open or secure, for the whole Web3 world through a versatile set of proofs.

At runtime, a node in the USL network maintains a set of claims that have been validated and settled. 
Because claims are self-contained statements that can be validated independently of each other, 
the USL node only needs to maintain all the validated claims as a set and not as an ordered sequence or list. 
There are two important characteristics of the claim sets within the USL nodes:
\begin{itemize}
    \item \textbf{Atomicity}. Claims are the smallest verifiable atom in the USL. 
     Each claim is self-contained and includes all the information for it to be 
     verified independently from the other claims. 
    \item \textbf{Timelessness}. Claims, once verified, continue staying valid regardless of time.  
     Timelessness is a natural corollary of atomicity. A time-sensitive or state-sensitive claim can be turned into
     a timeless/stateless claim by incorporating the time and/or the state as an argument of the claim. 
    \item \textbf{Monotonicity}. The set of claims maintained by a USL node only increases, and never decreases, as time passes. Monotonicity is a natural corollary of timelessness. Since valid claims continue staying valid, the USL node does not need to bother re-verifying claims and removing those that are no longer valid. 
\end{itemize}
This way, the USL opens the door to a more generalized and efficient Universal Consensus protocol
because unlike traditional blockchains, the USL network does not enforce the total ordering of its claims
(the USL ``transactions'').

Any applications or users can submit claims to the USL for verification and settlement. 
Depending on their use cases and the needs, these claims can have various types,
such as transaction claims (i.e., computation claims), 
state query claims, consensus claims, and/or vetted information claims. 
Every claim must be associated with a corresponding proof, and thus forms
a pair $\langle c, \pi \rangle$, where $c$ is the mathematical representation of the claim
and $\pi$ is a proof that can be verified by the USL node. 

\subsection{Universal Language Machine (ULM)}

\begin{figure}
\centering
\includegraphics[width=1\textwidth]{figs/ulm.png}
\caption{Universal Language Machine (ULM) Architecture}
\label{fig:ulm}
\end{figure}

The Universal Language Machine (ULM) is an open-source execution layer
platform that enables developers to create, deploy, and interact with smart contracts written in any programming language.
Unlike existing blockchain systems that require all contracts to be written in a single prescribed language, the ULM natively supports multiple languages.
This way,
the ULM enables diverse language ecosystems to coexist and interoperate on a single platform,
which not only empowers developers to use the most suitable language for their projects
but also makes smart contract development accessible to a much larger developer base.

Pi Squared's ULM is based on \K and formal semantics and thus adopts a mathematically grounded approach to
language support.
It uses \K and the formal semantics of programming languages to execute smart contracts written
in any programming language in a correct-by-construction manner.
The ULM is a significant advancement in flexibility, developer experience, and security,
and it paves the way for future innovation in decentralized applications,
fostering a more universal approach to Web3 development.


The overview architecture of the ULM is depicted in \Cref{fig:ulm}.
The core component is a semantics-based execution layer, powered by the \K framework and the formal semantics.
This semantics-based execution layer is loosely connected to and
actively interacting with an external consensus layer.
The modular design of the ULM enables it to interact with a variety of consensus algorithms and schemes, including BFT protocols.
In the future, we expect and look forward to making the ULM compatible with more consensus protocols.
At present, we are collaborating with the \href{https://www.commonprefix.com/}{Common Prefix} team
to connect the ULM to a POD-like weak/generalized consensus protocol for faster finality of the ULM transactions.

The ULM allows smart contracts written in different programming languages to coexist.
When a contract is deployed or called, ULM determines the correct semantics module 
to execute the contract code.
All smart contracts are able to modify the same blockchain state thanks to
a single universal API that provides access control and allows each semantics to update the storage of its own namespace only.
A language semantics can only modify the contract storage under its own namespace.
This namespace access control policy prevents malicious semantics from harming the storage of contracts written in other languages.

The LM is a \emph{truly universal} framework
because all smart contracts written in any programming languages
are directly and natively executed using the formal semantics, without compilation, thus avoiding compiler bugs.
Furthermore, the ULM architecture, as shown in \Cref{fig:ulm}, is extensible and enables dynamic addition of new programming languages.
Smart contracts written in various programming languages are connected to the \K framework
as modules.
Users are able to plug and play their programming languages, even their own customized languages,
as long as the formal semantics have been defined in \K.
This way, the ULM fosters continuous innovation in smart contract development.





\subsection{Universal Consensus Protocol (UCP)}

In the ULM and the USL, claims are the core of validation and consensus.
A claim can represent various types of assertions and is independently evaluated for correctness without relying on the order of processing.
This contrasts with traditional blockchain consensus, which requires agreement on a globally ordered sequence of transactions to prevent conflicts and maintain consistency.

Pi Squared's UCP is a novel distributed consensus algorithm specifically designed to operate on claims.
The UCP enables achieving agreement on the validity of claims in a permissionless, decentralized network.
At its core is the concept of set consensus, where the focus shifts from ordering values to achieving agreement on a set of independent claims.
Instead of requiring a strict sequence, users propose claims in parallel,
and the goal of the network is to agree on the valid subset of those claims by verifying their proofs.
This enables concurrent validation, reducing the complexity and overhead associated with traditional blockchain systems.

Clients are nodes responsible for: (1) providing claims that require validation and (2) maintaining an up-to-date view of the network’s state. Validators, on the other hand, are nodes tasked with individually verifying these claims to ensure that only claims that are verified as correct (i.e., their provided proofs check) are maintained by the protocol.

\begin{figure}
\centering
\includegraphics[width=0.8\textwidth]{figs/connection_graph.png}
\caption{Universal Consensus Protocol (UCP) Connection Topology}
\label{fig:uc}
\end{figure}

Inspired by POD~\cite{AlposADZ:2025}, the UCP uses a broadcast model that is based on a communication topology of a complete bipartite graph of clients and validators, as illustrated in Figure~\ref{fig:uc}. Importantly, validators do not need to communicate with one another as they maintain local logs of verified claims. Clients maintain streaming and stateful connections to all validators.
Validators are identified by public keys registered in a public key infrastructure (PKI). They sign all outgoing messages with digital signatures, providing cryptographic assurance of message authenticity and integrity since signatures cannot be forged.

The UCP is designed to tolerate Byzantine nodes that act arbitrarily or deviate from the protocol rules. As in POD~\cite{AlposADZ:2025}, we assume a limit on the resilience threshold $\beta$, which is the number of malicious validators (typically $(n-1)/3$ where $n$ is the total number of validators). There is no inherent assumption about the honesty of clients.


The UCP has the following key advantages:
\begin{itemize}
\item \textbf{Order independence}: Set consensus does not enforce an ordering of values, not even partial, allowing for parallel validation and processing.
\item \textbf{Scalability}: By eliminating the need for ordering, set consensus supports higher throughput and lower latency, unlike blockchain systems that sacrifice scalability for order and consistency.
\item \textbf{Separation of concerns}: The validity of claims is evaluated independently from application-specific safety properties, such as transaction order or state transition requirements. This flexibility allows the consensus protocol to support diverse use cases, from decentralized exchanges requiring strict ordering to voting systems where order does not matter.
\end{itemize}

The security of the UCP is established through key theorems. The \textbf{correctness} theorem ensures that invalid claims are never finalized in the view of an honest client, though they may temporarily appear as pending. The \textbf{view consistency} theorem guarantees that during partial synchrony with a network delay $\delta$, if a claim is observed as finalized by one honest client, it will be observed as finalized by all honest clients within $u = 2\delta$, ensuring consistent views. Finally, the \textbf{finalization} theorem ensures that valid claims are finalized within $w = 2\delta + \tau$ during partial synchrony, where $\tau$ is an upper bound on claim verification time, ensuring the progression of finalized claims in honest client views.

\section{Conclusion and Further Readings}
\label{sec:further}

We have introduced Pi Squared and its three major technological innovations:
the \K framework, Proof of Proof, and the 3-component Universality Stack 
that consits of
the Universal Settlement Layer (USL),
the Universal Language Machine (ULM),
and the Universal Consensus Protocol (UCP). 
By leveraging these core technologies, Pi Squared will empower Web3 developers to build interoperable and trust-minimized applications across multiple blockchain environments
and paving the way for a more unified, secure, and scalable future for Web3 infrastructure.

We have outlined the major technology building blocks in this umbrella white paper.
Deeper technical white papers, as well as several research and peer-reviewed papers, are available on 
\href{https://pi2.network/papers}{\texttt{pi2.network}}, in particular:
\begin{itemize}
\item \href{https://pi2.network/papers/llvm-k-whitepaper}{K Framework}
\item \href{https://pi2.network/papers/proof-of-proof-whitepaper}{Proof of Proof}
\item \href{https://pi2.network/papers/universality-whitepaper}{Pi Squared's Universality Stack (USL + ULM + UCP)}
\end{itemize}

\bibliographystyle{plain}
\bibliography{refs}

\end{document}
```

## Proof of Proof:A Universal Verifiable Computing Framework Version 1.0

**Authors:** Pi Squared Inc.

**Date:** February 2025

### LaTeX Source

```latex
\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{alltt}
\usepackage{appendix}
\usepackage{adjustbox}
\usepackage{tikz}
\usetikzlibrary{graphs}



\usepackage{amsmath, amssymb, amsthm}
\usepackage{booktabs}
\usepackage{breqn}
\usepackage{graphicx}
\usepackage{hyperref}
  \usepackage[capitalize]{cleveref} 
\usepackage{listings}
\usepackage{mathbbol}
\usepackage{multirow}
\usepackage{subcaption}
\usepackage{tabularx}
\usepackage{todonotes}
\usepackage{url}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{listings}
\usepackage{prftree}


\theoremstyle{plain}
  \newtheorem{theorem}{Theorem}[section]
  \newtheorem{lemma}{Lemma}[section]
  \newtheorem{proposition}{Proposition}[section]
  \newtheorem*{theorem*}{Theorem}

\theoremstyle{definition}
  \newtheorem{definition}{Definition}[section]
  \newtheorem{remark}{Remark}[section]

\crefname{theorem}{Theorem}{Theorems}
\crefname{theorem*}{Theorem}{Theorems}
\crefname{lemma}{Lemma}{Lemmas}
\crefname{proposition}{Proposition}{Propositions}
\crefname{definition}{Definition}{Definitions}
\crefname{remark}{Remark}{Remarks}

\newcolumntype{Y}{>{\raggedright\arraybackslash}X}


\newcommand{\cln}{{\kern0.2ex:\kern0.2ex}}
\newcommand{\ld}{\mathord{.\,}}
\newcommand{\To}{\Rightarrow}
\newcommand{\imp}{\to}
\newcommand{\eventually}{\diamond}
\newcommand{\K}{$\mathbb{K}$\xspace}
\newcommand{\ML}{$\mathbb{ML}$\xspace}
\newcommand{\code}[1]{\texttt{#1}\xspace}
\newcommand{\codel}[1]{\\\phantom{aaa}\code{#1}\\}
\newcommand{\pr}[1]{\langle #1 \rangle}
\newcommand{\SV}{SV}
\newcommand{\EV}{EV}
\newcommand{\PAT}[1]{\textsc{Pattern}(#1)}
\newcommand{\Pattern}{\textsc{Pattern}}
\newcommand{\dimp}{\leftrightarrow}
\newcommand{\ev}[2]{|#1|_{#2}}
\newcommand{\pset}[1]{\mathcal{P}(#1)}
\newcommand{\FV}{\textsc{fv}}
\newcommand{\bflfp}{\mathbf{lfp}}
\newcommand{\uapdu}{\_{\apd}\_}
\newcommand{\apd}{\mathbin{\scalebox{0.7}{$\bullet$}}}
\newcommand{\apde}{\mathbin{\overline{\apd}}}
\newcommand{\celli}[2]{\code{<#1>\,#2\,</#1>}}
\newcommand{\celln}[1]{\code{</#1>}}
\newcommand{\inh}[1]{\top_{#1}}
\newcommand{\Sort}{\mathit{Sort}}
\newcommand{\tb}{\textbackslash}
\newcommand{\prule}[1]{\scalebox{.85}[1]{\textnormal{{(#1)}}}}
\newcommand{\Slash}{/\!/ }
\newcommand{\hole}{\square}
\newcommand{\smallurl}[1]{{\small\url{#1}}}
\newcommand{\oto}{\mathbin{\scalebox{0.8}{\textnormal{\textcircled{\scriptsize$\to$}}}}}
\newcommand{\init}{{\textit{init}}}
\newcommand{\final}{{\textit{final}}}

\newcommand{\INT}{\ensuremath{\mathit{INT}}}
\newcommand{\MAP}{\ensuremath{\mathit{MAP}}}
\newcommand{\ID}{\ensuremath{\mathit{ID}}}
\newcommand{\IDS}{\ensuremath{\mathit{IDS}}}
\newcommand{\Int}{\ensuremath{\mathit{Int}}}
\newcommand{\String}{\ensuremath{\mathit{String}}}
\newcommand{\Id}{\ensuremath{\mathit{Id}}}
\newcommand{\Ids}{\ensuremath{\mathit{Ids}}}
\newcommand{\dotIds}{\ensuremath{._\mathit{Ids}}}
\newcommand{\PlusInt}{\ensuremath{\mathbin{{\texttt{+}}_\Int}}}
\newcommand{\MinusInt}{\ensuremath{\mathbin{{\texttt{-}}_\Int}}}
\newcommand{\DiffInt}{\ensuremath{\mathbin{\texttt{=/=}_\Int}}}
\newcommand{\dotMap}{\ensuremath{._\mathit{Map}}}
\newcommand{\Exp}{\ensuremath{\mathit{Exp}}}
\newcommand{\Plus}{\ensuremath{Plus}}
\newcommand{\Minus}{\ensuremath{Minus}}
\newcommand{\WfTerm}{\ensuremath{\mathit{WfTerm}}}
\newcommand{\WfSubst}{\ensuremath{\mathit{WfSubst}}}
\newcommand{\WfPred}{\ensuremath{\mathit{WfPred}}}
\newcommand{\eqbynot}{\mathbin{{:}{\leftrightarrow}}}
\newcommand{\lequiv}{\leftrightarrow}
\newcommand{\limplies}{\rightarrow}
\newcommand{\ceil}[1]{\lceil #1 \rceil}
\newcommand{\floor}[1]{\lfloor #1 \rfloor}
\newcommand{\elOfSort}{\mathop{\cdot{:}}}
\newcommand{\SortIt}{\ensuremath{\mathit{Sort}}}
\newcommand{\Sorts}{\ensuremath{\mathit{Sorts}}}
\newcommand{\SortVariable}{\ensuremath{\mathit{SortVariable}}}
\newcommand{\SortVariables}{\ensuremath{\mathit{SortVariables}}}
\newcommand{\SortId}{\ensuremath{\mathit{SortId}}}
\newcommand{\ElementVariable}{\ensuremath{\mathit{ElementVariable}}}
\newcommand{\SetVariable}{\ensuremath{\mathit{SetVariable}}}
\newcommand{\ElementVariableId}{\ensuremath{\mathit{ElementVariableId}}}
\newcommand{\SetVariableId}{\ensuremath{\mathit{SetVariableId}}}
\newcommand{\SymbolId}{\ensuremath{\mathit{Symbol}}}
\newcommand{\PatternIt}{\ensuremath{\mathit{Pattern}}}
\newcommand{\Patterns}{\ensuremath{\mathit{Patterns}}}
\newcommand{\Sentence}{\ensuremath{\mathit{Sentence}}}
\newcommand{\Attributes}{\ensuremath{\mathit{Attributes}}}

\newcommand{\Com}{\operatorname{Com}} 
\newcommand{\Hash}{\operatorname{Hash}} 

\lstset{
    basicstyle=\ttfamily\scriptsize,
    numberstyle=\ttfamily,
    breaklines=true,
    tabsize=4,
    frame=tb,
    framerule=0pt,
    framesep=1pt,
    escapeinside={(*}{*)},
}

\lstdefinelanguage{K}{
    basicstyle=\ttfamily\scriptsize,
    commentstyle=\selectfont\color{gray},
    alsoletter={=,>},
    morekeywords={module,endmodule,imports,rule,claim,syntax,requires,configuration,=>},
    morecomment=[l]{//},
    keywordstyle=\color{blue}, 
}

\lstdefinelanguage{Kore}{
    commentstyle=\selectfont\color{gray},
    alsoletter={\textbackslash},
    morekeywords={module,endmodule,axiom,symbol,sort,\textbackslash and,\textbackslash or,\textbackslash not,\textbackslash top,\textbackslash bottom,\textbackslash rewrites,\textbackslash next,\textbackslash forall,\textbackslash exists},
    morecomment=[l]{//},
}

\lstdefinelanguage{Metamath}{
    commentstyle=\selectfont\color{gray},
    alsodigit={-},
    alsoletter={.,\{,\},=,?},
    morekeywords={\$c,\$v,\$f,\$d,\$e,\$a,\$p,\$=,\$==,\$.,\$\{,\$\},\$?},
    morecomment=[s]{\$(}{\$)},
}

\lstdefinelanguage{Tactic}{
    morekeywords={apply,let,notation,tautology},
    morecomment=[l]{\#},
}

\lstdefinelanguage{IMP}{
    morekeywords={while,int},
    morecomment=[l]{//},
}





\title{Proof of Proof:\\A Universal Verifiable Computing Framework\\\Large Version 1.0}
\author{Pi Squared Inc.}
\date{February 2025}



\begin{document}

\maketitle

{\parbox{0.86\textwidth}{\small\em 
It is suggested that the reader first read ``The Pi Squared Whitepaper''~\cite{pi2paper}.
}}

\begin{abstract}
This paper gives an overview of the Proof of Proof approach to universal and correct-by-construction verifiable computing proposed by the Pi Squared team.  The idea of Proof of Proof is to separate the three underlying concerns: \textit{computation}, \textit{verification}, and \textit{cryptography}.

First, recent developments in executable formal semantics allow us to efficiently and completely automatically reduce computation to mathematical proof.  The universality of Proof of Proof comes from the fact that there is only one language for mathematical proofs, which works with math proofs corresponding to any computations done with any programs in any programming languages (PLs) or virtual machines (VMs).

Second, the generated math proofs are verified, not trusted, with a disarmingly simple and small proof checker of only a few hundred lines of code.  The correctness of Proof of Proof comes from the fact that no (usually complex and error-prone) compilers, interpreters, or even formal provers or language frameworks need to be trusted or formally verified: all these become only instruments to assist the generation of math proofs; the math proofs, and not the tools that produced them, are the ultimate correctness arguments for the computations from which they were derived.

Finally, recent developments in cryptography, e.g., SNARKS, STARKS and zero-knowledge (ZK), allow us to implement the math proof checker as a cryptographic circuit, which effectively allows us to produce ZK proofs for the integrity of the math proofs, that is, (ZK) Proofs of (math) Proofs. 
\end{abstract}

\ \ \framebox{\parbox{0.86\textwidth}{This paper does not discuss semantics-based execution in-depth, nor recent developments in the context of the \K framework that make semantics-based execution comparable in performance with manual, adhoc language implementations.  If the reader is interested in how a formal reasoning engine like \K can execute programs as fast as or faster than dedicated interpreters, e.g., EVM programs as fast as or faster than Geth, they should refer to our white paper dedicated to that topic: \textit{``Semantics-based execution and the LLVM backend of the \K Framework''}.  This paper only focuses on how to extract the math proofs from \K, verify them, and generate ZK proofs from them.}}

\newpage

\renewcommand{\contentsname}{Table of Contents}
\tableofcontents


\newpage

\section{Introduction}

Proof of Proof is a universal, verifiable computing framework for all programming languages,
virtual machines (VMs), and instruction set architectures (ISAs). 
Its universality comes from a semantics-based approach.
In this approach, any programming language has a formal semantics, 
which is a rigorous, complete, and executable mathematical definition
that specifies all behaviors of all programs in that language. 
This formal semantics is passed as an input to the Proof of Proof framework for two purposes:
to execute programs in that language and to generate verifiable proofs for program execution. 
Because Proof of Proof is directly based on the formal semantics of programming languages,
it is universal and language-agnostic (also known as language-independent and language-parametric). 


\Cref{fig:workflow} shows the Proof of Proof workflow.
To obtain a proof for the execution of a program $P$ in a programming language $L$
within certain execution environment,
one should first prepare a formal semantics of $L$. 
This formal semantics, denoted by $\Gamma^L$, is written in an open-source universal language framework
called the \href{https://kframework.org}{\K framework}. 
The formal semantics $\Gamma^L$ then serves two purposes. 
Firstly, it is used by \K to automatically derive an interpreter for $L$. 
Secondly, it is used as a basis for formal reasoning, for constructing formal proofs
for the execution of programs in $L$.  

Proof of Proof reduces arbitrary computation of any program in any programming language 
into a unifying and universal domain: mathematics. 
More specifically, mathematical logic. 
Proof of Proof is based on \href{https://matching-logic.org}{matching logic}
as its underlying logical foundation. 
A formal semantics $\Gamma^L$ of a programming language $L$ is a logical theory in matching logic
that consists of mathematical axioms that specify the behaviors of all programs in the language. 
A concrete execution trace of a program $P$ within a certain execution environment $E$
is represented as a logical claim to be proved. 
Intuitively, the claim has the form
$\gamma_\init \To \gamma_\final$,
where $\gamma_\init$ and $\gamma_\final$ represent the 
initial and final configurations at the beginning and at the end of the execution of $P$, respectively. 
Then, Proof of Proof generates a mathematical proof $\Pi$ for the claim.
We denote it as
\begin{equation}
\label{eq:claim}
  \Pi \ \colon\  \Gamma^L \vdash \gamma_\init \To \gamma_\final
\end{equation}
The mathematical proof $\Pi$ shows how to construct the claim $\gamma_\init \To \gamma_\final$
from the axioms in $\Gamma^L$ using the proof system of matching logic. 
The proof system of matching logic consists of a fixed number of proof rules. 
The mathematical proof $\Pi$ is effectively
a transcript that tells how to apply the proof rules in the proof system
to construct the claim from the axioms. 
As a result, $\Pi$ is often a much larger artifact than $P$ or the configurations
$\gamma_\init$ and $\gamma_\final$. 
The process of generating $\Pi$ from $P$ and its initial and final configurations
is called Math Proof Generation, abbreviated as MPG. 

Since the mathematical proof $\Pi$ is large and its usage could be unpractical, Proof of Proof further uses Zero-Knowledge (ZK) Proof technology to reduce its size. While the mathematical proof demonstrates the correctness of a program's execution trace, the corresponding ZK proof $\pi$ only shows that such a mathematical proof exists. Still, from the user's point of view, the ZK proof is enough. Proof of Proof is compatible with many ZK technologies. In particular, any existing zkVM can be used to generate ZK proofs from mathematical proofs.

Following this introduction, Section \ref{sec:prelim} provides the prerequisites for understanding Proof of Proof such as the \K framework, matching logic, and zero-knowledge cryptography basics. Section \ref{sec:mpg} discusses how machine-verifiable mathematical proofs can be generated from a given program execution using its programming language's formal semantics. Section \ref{sec:zkVMs} elaborates on a series of experiments conducted to verify different mathematical proofs of existing zkVMs and the lessons we learned. Section \ref{sec:block_model} outlines our novel block model, an alternative to using zkVMs that allows us to represent and verify mathematical proofs directly and efficiently in ZK without translating to any VM or ISA.  


\begin{figure}
\includegraphics[width=\textwidth]{figures/pop.png}
\caption{Proof of Proof Workflow}
\label{fig:workflow}
\end{figure}



\section{Preliminaries} \label{sec:prelim}

Here, we recall what formal semantics is, how the formal semantics framework \K introduced in 2003 works, the logical foundation underlying \K that allows us to universally reduce computation to mathematical proof, and finally, what zkVMs are and their role in our Proof of Proof approach.

\subsection{Formal Semantics and \texorpdfstring{\K}{\K} Framework}

An easy way to understand \K is to look at it as a meta-language, that can implement, or better say, define, other programming languages. 
In \Cref{fig:imp}, we show an example \K language definition
of an imperative language IMP. 
In the 40-line definition, 
we \emph{completely} define the formal syntax and
the (executable) formal semantics of IMP using a user-friendly front end language (part of \K).



\begin{figure}[t]
\begin{subfigure}[t]{0.45\textwidth}
\begin{lstlisting}[language=K,numbers=left,frame=single,framexleftmargin=1em]
module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= 
      Int | Id
    | Exp "+" Exp [left, strict]
    | Exp "-" Exp [left, strict]
    | "(" Exp ")" [bracket]
  syntax Stmt  ::=
      Id "=" Exp ";" [strict(2)]
    | "if" "(" Exp ")"
        Stmt Stmt [strict(1)]
    | "while" "(" Exp ")" Stmt
    | "{" Stmt "}" [bracket]
    | "{" "}"
    > Stmt Stmt [left]
  syntax Pgm ::= 
    "int" Ids ";" Stmt 
  syntax Ids ::= List{Id,","}
endmodule
\end{lstlisting}
\end{subfigure}
\begin{subfigure}[t]{0.57\textwidth}
\begin{lstlisting}[language=K,numbers=left,firstnumber=20,xleftmargin=1em,frame=single,framexleftmargin=1em]
module IMP 
  imports IMP-SYNTAX DOMAINS
  syntax KResult ::= Int
  configuration 
    <T> <k> $PGM:Pgm </k>
        <state> .Map </state>  </T>
  rule <k> X:Id => I ...</k> 
       <state>... X |-> I ...</state>
  rule I1 + I2 => I1 +Int I2
  rule I1 - I2 => I1 -Int I2
  rule <k> X = I:Int; => .K ...</k> 
    <state>... X |-> (_ => I) ...</state>
  rule {} => .K
  rule if(I) S _ => S requires I =/=Int 0
  rule if(0) _ S => S
  rule while(B)S => if(B) {S while(B)S}{}
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule <k> int (X,Xs => Xs);_ </k> 
       <state> _ (.Map => X|->0) </state>
  rule int .Ids; S => S
endmodule
\end{lstlisting}
\end{subfigure}
\caption{Complete \K Semantics of  an Imperative Language}
\label{fig:imp}
\end{figure}



We use IMP as an example to illustrate the main \K features.
There are two \emph{modules}:
\code{IMP-SYNTAX} defines the syntax, and \code{IMP}
defines the semantics using rewrite rules. 
Syntax is defined as BNF grammar.
The keyword \code{syntax} leads to production rules
that can have {attributes} that specify the additional 
syntactic and/or semantic information.
For example, the syntax of \code{if}-statements is defined in lines~10--11
and has the attribute \code{[strict(1)]}, meaning that the evaluation order 
is strict in the first argument, i.e., the condition of an \code{if}-statement.

In the module \code{IMP}, we define the \emph{configurations} of IMP
and its formal semantics.
A configuration (lines~23-25) is a constructor term
that has all semantic information needed to execute programs.
IMP configurations are simple, consisting of 
the IMP code and a program state that maps variables to values.
We organize configurations using \emph{(semantic) cells}: 
\celln{\K} is the cell of IMP code and \celln{state} is the cell of 
program states. 
In the initial configuration (lines~24-25),
\celln{state} is empty
and \celln{\K} contains the IMP program that we pass to 
\K for execution (represented by the special \K variable \code{\$PGM}). 

We define formal semantics using \emph{rewrite rules}. 
In lines~26--27, we define the semantics of variable lookup,
where we match on a variable \code{X} in the \celln{\K} cell and 
look up its value \code{I} in the \celln{state} cell by matching on the binding
$\code{X} \,{\mapsto}\, \code{I}$. 
Then, we rewrite \code{X} to \code{I},
denoted by $\code{X} \,{\To}\, \code{I}$ 
in the \celln{\K} cell in line~26. 
Rewrite rules in \K generalize those in other rewrite engines, such as Maude \cite{maude}, in the sense that they also mention the partial context in which the rewrites happen.
That is, they are rewrites within a term called {\em local rewrites} in \K, and there can be more than one in the term -- see, for example, the rewrite rule giving the semantics of assignment in lines 30--31.


\subsection{Matching Logic} \label{sec:matching_logic}


Matching logic \cite{Ros17,CR19,CLR21a} provides a unifying framework for defining and reasoning about the semantics of programming languages. 
A programming language is defined in matching logic as a \emph{logical theory}, i.e., a set of axioms.

Thanks to the \href{https://kframework.org}{\K framework}, 
many real-world programming languages have been \emph{completely defined}
as matching logic theories: C~\cite{HER15}, 
Java~\cite{BR15},
JavaScript~\cite{PSR15},
Python~\cite{python-semantics}, 
Rust~\cite{krust-singapore,krust-shanghai},
Ethereum Virtual Machine (EVM) opcodes~\cite{HSZ+18},
x86-64~\cite{DPK+19}, 
and LLVM~\cite{K-llvm},
among others. 
\K provides a suite of tools to
generate implementations and formal analysis tools for any programming language
from its formal semantics. 
These implementations and tools include parsers, interpreters, model checkers, symbolic execution engines, and even deductive and inductive program verifiers~\cite{RS10,SPY+16}.
Some language tools, such as \textsc{RV-Match},
\textsc{RV-Monitor}, and \textsc{RV-Predict}
based on the C semantics in matching logic,
have commercialized applications. 

On the other hand, matching logic was purposely crafted not only to be expressive enough to support all programming languages and computational models and paradigms, but also to admit the \textit{smallest proof checker} known: it has only 200 lines of code \cite{CLTR21}.  That is, 200 lines of code that can verify the integrity of any execution of any program in any programming language.  It can in fact do significantly more than that, but that is enough for our purpose here.

The syntax of matching logic is quite compact:
\begin{equation}\label{eq:mlsyntax1}
\varphi ::=
x 
\mid X 
\mid \sigma
\mid \varphi_1 \  \varphi_2
\mid \bot
\mid \varphi_1 \imp \varphi_2
\mid \exists x \ld \varphi
\mid \mu X \ld \varphi \ \text{if $\varphi$ is positive in $X$}
\end{equation}
These 8 syntax constructs\footnote{Actually there are only 7 core constructs, since $\bot$ can be defined as a notation for $\mu X\ld X$.} build
matching logic formulas, called \emph{patterns},
which, semantically speaking, can be \emph{matched} by a set of elements. 
Patterns can match structures that are of certain shapes,
satisfy certain dynamic properties, or meet certain logical constraints,
usually all of these together.

\emph{Element variables} $x$ are FOL-style variables that are
necessary for ranging over individual elements, which can then be quantified (i.e., “abstracted”)
by the $\exists$ binder. \emph{Set variables} $X$ are like propositional variables in modal logic that are necessary
for ranging over sets (i.e., predicates), which can then be quantified by $\mu$ to create least fixpoints.
\emph{Constant symbols} $\sigma$ are used to represent functions, predicates, constructors, and modal operators in a
uniform way. Together with \emph{application}, constant symbols build complex patterns from simpler ones (i.e.,
$\sigma\,\varphi_1\ldots \varphi_n$), which can represent terms (e.g., $\sigma \equiv f$ for function $f$), FOL-style formulas (e.g., $\sigma \equiv p$
for predicate p), program configurations (e.g., $\sigma$ being the \verb|<\K/>| cell), and modal formulas such
as temporal and reachability properties (e.g., $\sigma$ being the “next” operator $\circ$ in LTL~\cite{CR19}).

\subsubsection{Notations} \label{sec:notations}

The expressivity of matching logic (\ML) can be extended on two dimensions:
\begin{enumerate}
\item Many logical frameworks can be subsumed to \ML as theories~\cite{CR19a}
\item   A domain-specific logic can be defined as an \ML theory using a simple and powerful notation mechanism.
\end{enumerate}
The \emph{notation mechanism} can be expressed as a chain of theories. Unlike the classical approach, we represent a theory as a triple $(\Sigma, \Phi, \vdash)$, where $\Sigma$ is the alphabet of the constant symbols, $\Phi$ a set of formulas (patterns), and $\vdash$ an entailment relation (more on the entailment/provability relation and the proof system of matching logic in Section \ref{sec:proof_system}). A notation-based specification is given as an inclusion theory morphism $(\Sigma, \Phi, \vdash) \allowbreak \to (\Sigma, \Phi', \vdash')$ such that each \emph{new formula} $\varphi'\in \Phi'\setminus \Phi$ is a \emph{notation} of a formula $\varphi\in\Phi$, written as $\varphi' \eqbynot \varphi$ and expressed by two new axioms: $\vdash' \varphi' \rightarrow \varphi$ and $\vdash' \varphi \rightarrow \varphi'$. $\Phi'$ may also include other axioms that constrain the use of notations.

\paragraph{Derived operators as notations}
\begin{enumerate}
\item \textbf{New formulas (patterns): }
\[
\varphi ::= \neg\varphi \mid \varphi_1 \lor \varphi_2 \mid \varphi_1 \land \varphi_2 \mid \varphi_1 \lequiv \varphi_2 \mid \forall x \ld \varphi \mid \nu X \ld \varphi
\]
\item \textbf{New axioms:}
\begin{align*}
\neg \varphi & \eqbynot \varphi \limplies \bot
&& \textrm{// negation}\\
\varphi_1 \lor \varphi_2 & \eqbynot (\varphi_1 \limplies \bot) \limplies \varphi_2 
&& \textrm{// disjunction}\\
\varphi_1 \land \varphi_2 & \eqbynot \neg(\neg \varphi_1 \lor \neg\varphi_2)
&& \textrm{// conjunction}\\
\varphi_1 \lequiv \varphi_2 & \eqbynot (\varphi_1 \limplies \varphi_2) \land (\varphi_2 \limplies \varphi_1)  
&& \textrm{\!// equivalence}\\
\forall x \ld \varphi & \eqbynot \neg \exists x \ld \neg \varphi 
&& \textrm{// universal quantification}\\
\nu X \ld \varphi &\eqbynot \neg\, \mu X \ld \neg\varphi [\neg X/ X]
&& \textrm{// greatest fixpoint}
\end{align*}
\end{enumerate}
Note that the above grammar extends the one over which the notation is defined (here, the original grammar).

\paragraph{Equality and membership as notations\\}
Although the syntax of patterns does not have equality, 
we can define it as a notation (see~\cite{CLR21a}).
An equality of two patterns $\varphi_1$ and $\varphi_2$, 
written $\varphi_1 = \varphi_2$,
is equivalent to $\top$ if the same elements match the
two patterns.
Otherwise, it is equivalent to $\bot$. 

Assume that $(\Sigma, \Phi, \vdash)$ includes a symbol $\mathit{def} \in \Sigma$, called the \emph{definedness} symbol,
and define the following axiom:
\[
\textsc{Definedness}\qquad \vdash\forall x \ld \mathit{def}\ x
\]
Intuitively, \textsc{Definedness} states that each individual element is \emph{defined} (i.e., not $\bot$). 
Thus, for any pattern $\psi$ that is matched by 
some elements, $\mathit{def}\ \psi$ is $\top$.  
\begin{enumerate}
\item \textbf{New formulas (patterns): }
\[
\varphi ::=  \ceil{\varphi} \mid \floor{\varphi} \mid \varphi_1 = \varphi_2 \mid \varphi_1 \subseteq \varphi_2 \mid x \in \varphi
\]
\item \textbf{New axioms:}
\begin{align*}
\ceil{\varphi} & \eqbynot (\mathit{def}\ x)
&& \textrm{// definedness}\\
\floor{\varphi} & \eqbynot \neg \ceil{\neg \varphi}
&& \textrm{// totality}\\
\varphi_1 = \varphi_2 & \eqbynot \floor{\varphi_1 \dimp \varphi_2}
&& \textrm{// equality}\\
\varphi_1 \subseteq \varphi_2 & \eqbynot \floor{\varphi_1 \imp \varphi_2}
&& \textrm{// set inclusion}\\
x \in \varphi & \eqbynot x \subseteq \varphi
&& \textrm{// membership}
\end{align*}
\end{enumerate}

\paragraph{Sorts as notations\\}
A \emph{sort} has a name and 
is associated with a set of its \emph{inhabitants}. 
In matching logic, we use a symbol $s \in \Sigma$ to represent the sort name
and use $(\mathsf{inh} \ s)$ to represent all its inhabitants,
where $\mathit{inh} \in \Sigma$ is an ordinary symbol.
\begin{enumerate}
\item \textbf{New formulas (patterns)}: 
\[\hspace{-5ex}
\varphi ::= \inh{s} \mid \neg_s \varphi \mid \forall x \cln s \ld \varphi \mid
\exists x \cln s \ld \varphi \mid \varphi \cln s \mid \forall x_1,\dots,x_n \cln s \ld \varphi \mid \exists x_1,\dots,x_n \cln s \ld \varphi
\]
\item \textbf{New axioms}:
\begin{align*}
\inh{s} & \eqbynot \mathit{inh} \  s
&& \textrm{// inhabitants of $s$}\\
\neg_s \varphi & \eqbynot (\neg \varphi) \wedge \inh{s}
&& \textrm{// negation within sort $s$}\\
\forall x \cln s \ld \varphi & \eqbynot \forall x \ld x \in \inh{s} \imp \varphi
&& \textrm{// $\forall$ within sort $s$}\\
\exists x \cln s \ld \varphi & \eqbynot \exists x \ld x \in \inh{s} \land \varphi
&& \textrm{// $\exists$ within sort $s$}\\
\varphi \elOfSort s & \eqbynot \exists z \cln s \ld \varphi = z
&& \textrm{// $\varphi$ is an element of sort $s$}\\
\forall x_1,\dots,x_n \cln s \ld \varphi & \eqbynot  \forall x_1 \cln s \ld \dots \forall x_n \cln s \ld \varphi
&& \textrm{// nested $\forall$ within sort $s$}\\
\exists x_1,\dots,x_n \cln s \ld \varphi & \eqbynot \exists x_1 \cln s \ld \dots \exists x_n \cln s \ld \varphi
&& \textrm{// nested $\exists$ within sort $s$}
\end{align*}
\end{enumerate}

\paragraph{Many-sorted functional symbols as notations\\}
A many-sorted function symbol $f:s_1\times\cdots s_n\to s$ is represented as a notation as follows:
\begin{enumerate}
\item \textbf{New formulas (patterns)}: 
\[
\varphi ::= f(\varphi_1,\ldots,\varphi_n)
\]
\item \textbf{New axioms}:
\begin{align*}
f(\varphi_1,\ldots,\varphi_n) & \eqbynot f\ \varphi_1\ \ldots\ \varphi_n\qquad\qquad\qquad
& \textrm{// functional notation}\\
\omit\rlap{$\vdash \forall x_1 \cln s_1 \ld \dots \forall x_n \cln s_n \ld \exists y \cln s \ld f(x_1,\ldots,x_n) = y$}
&&\omit\rlap{\textrm{// function}}
\end{align*}
\end{enumerate}


\paragraph{Rewrite rules as notations\\}
A binary relation $R\subseteq S\times S$ can be specified in \ML as a symbol $R$ together with an axiom $R\ S\subseteq S$.
For specifying rewrite rules $\varphi_{\it lhs}\Rightarrow_{\it rew}\varphi_{\it rhs}$, we consider a sort $\it Cfg$ for \emph{configurations} and a
\emph{one-path next} symbol $\bullet$ representing the one-step transitions over configurations, i.e., $\bullet {\it Cfg}\subseteq {\it Cfg}$. 
Since $\varphi_{\it lhs}\Rightarrow_{\it rew}\varphi_{\it rhs}$ means that any configuration $\gamma\in \varphi_{\it lhs}$ has a next configuration $\gamma'$ in $\varphi_{\it rhs}$, it can be specified by
$\varphi_{\it lhs}\rightarrow \bullet \varphi_{\it rhs}$. Summarizing:

\begin{enumerate}
\item \textbf{New formulas (patterns)}: 
\[
\varphi ::= \varphi_{\it lhs}\Rightarrow_{\it rew} \varphi_{\it rhs}
\]
\item \textbf{New axioms}:
\begin{align*}
\hspace{-5ex}\varphi_{\it lhs}\Rightarrow_{\it rew} \varphi_{\it rhs} & \eqbynot \varphi_{\it lhs}\rightarrow {}\bullet{} \varphi_{\it rhs}
& \textrm{// rewrite rule}\\
\omit\rlap{\hspace{-5ex}$\vdash {}\bullet{} \inh{\it Cfg}\subseteq \inh{\it Cfg}$}
&&\omit\rlap{\textrm{// one-step transition}}\\
\omit\rlap{\hspace{-5ex}$\varphi_1 \rightarrow {}\bullet \varphi_2, \varphi_2 \rightarrow {}\bullet \varphi_3\vdash \varphi_1 \rightarrow {}\bullet {} \bullet{} \varphi_3$}
&&\omit\rlap{\textrm{// transition transitivity}}
\end{align*}
\end{enumerate}

\paragraph{Kore as notations\\}
\label{sec:kore}

A \K language definition (such as imp.k in
Figure~\ref{fig:imp}) is compiled into an intermediate representation, called the \emph{Kore format}, by the \K tool \emph{kompile}.
The Kore format~\cite{kore-github} is based on many-sorted \ML~\cite{CR19}, which is itself just \ML extended with a series of notations -- i.e., not a new logic.
The main syntactic categories of Kore include:\footnote{See~\cite{kore-github} for a complete definition of Kore syntax.}\\

\noindent
\textbf{Sorts}:
\begin{alltt}
  \(\SortIt\)  ::= \(\SortVariable\) | \(\SortId\) "\{" \(\Sorts\) "\}"
  \(\Sorts\) ::= "" | \(\SortIt\) \{"," \(\SortIt\)\}\(^*\)
  \(\SortVariables\) ::= "" | \(\SortVariable\) \{"," \(\SortVariable\)\}\(^*\)
\end{alltt}

\noindent
\textbf{Variables}:
\begin{alltt}
  \(\ElementVariable\) ::= \(\ElementVariableId\) ":" \(\SortIt\)
  \(\SetVariable\) ::= \(\SetVariableId\) ":" \(\SortIt\)
\end{alltt}

\noindent
\textbf{Patterns}:
\begin{alltt}
  \(\PatternIt\)
    ::= \(\ElementVariable\)
      | \(\SetVariable\)
      | "\textbackslash{}bottom" "\{" \(\SortIt\) "\}" "(" ")"
      | "\textbackslash{}top" "\{" \(\SortIt\) "\}" "(" ")"
      | \(\SymbolId\) "\{" \(\Sorts\) "\}" "(" \(\Patterns\) ")"
      | "\textbackslash{}not" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) ")"
      | "\textbackslash{}and" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}or" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}implies" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}iff" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}exists" "\{" \(\SortIt\) "\}" "(" \(\ElementVariable\) "," \(\PatternIt\) ")"
      | "\textbackslash{}forall" "\{" \(\SortIt\) "\}" "(" \(\ElementVariable\) "," \(\PatternIt\) ")"
      | "\textbackslash{}mu" "\{" "\}" "(" \(\SetVariable\) "," \(\PatternIt\) ")"
      | "\textbackslash{}nu" "\{" "\}" "(" \(\SetVariable\) "," \(\PatternIt\) ")"
      | "\textbackslash{}ceil" "\{" \(\SortIt\) "," \(\SortIt\) "\}" "(" \(\PatternIt\) ")"
      | "\textbackslash{}floor" "\{" \(\SortIt\) "," \(\SortIt\) "\}" "(" \(\PatternIt\) ")"
      | "\textbackslash{}equals" "\{" \(\SortIt\) "," \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}in" "\{" \(\SortIt\) "," \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}next" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) ")"
      | "\textbackslash{}rewrites" "\{" \(\SortIt\) "\}" "(" \(\PatternIt\) "," \(\PatternIt\) ")"
      | "\textbackslash{}dv" "\{" \(\SortIt\) "\}" "(" \(\String\) ")"
  \(\Patterns\) ::= "" | \(\PatternIt\) \{"," \(\PatternIt\)\}\(^*\)
\end{alltt}

The definition of Kore as an \ML notation is given on top of theories defining sorts, many-sorted functions, and rewrite rules in a similar way to that given by the Metamath specification~\cite{kore-mm-github} (see also~\Cref{sec:ml_mm}).
\begin{enumerate}
\item \textbf{New formulas (patterns)}: 
\begin{align*}
\varphi ::={} & \texttt{\textbackslash{}bottom}\{s\}()\\
\mid{} & \texttt{\textbackslash{}top}\{s\}()\\
\mid{} & \sigma \{s_1,\ldots, s_n\}(\varphi_1,\ldots,\varphi_n)\\
\mid{} & \texttt{\textbackslash{}not}\{s\}(\varphi)\\
\mid{} & \texttt{\textbackslash{}and}\{s\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}or}\{s\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}implies}\{s\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}iff}\{s\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}exists}\{s\}(x{:}s', \varphi)\\
\mid{} & \texttt{\textbackslash{}forall}\{s\}(x{:}s', \varphi)\\
\mid{} & \texttt{\textbackslash{}mu}\{\,\}(X{:}s, \varphi)\\
\mid{} & \texttt{\textbackslash{}nu}\{\,\}(X{:}s, \varphi)\\
\mid{} & \texttt{\textbackslash{}ceil}\{s_1, s_2\}(\varphi)\\
\mid{} & \texttt{\textbackslash{}floor}\{s_1, s_2\}(\varphi)\\
\mid{} & \texttt{\textbackslash{}equals}\{s_1, s_2\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}in}\{s_1, s_2\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}next}\{s\}(\varphi)\\
\mid{} & \texttt{\textbackslash{}rewrites}\{s\}(\varphi_1, \varphi_2)\\
\mid{} & \texttt{\textbackslash{}dv}\{s\}("v")
\end{align*}

The above new patterns are sorted, where the sort is computed as follows:
\begin{center}    
\begin{tabular}{ll}
$\texttt{\textbackslash{}bottom}\{s\}():s$ & $\texttt{\textbackslash{}top}\{s\}():s$\\
$\sigma \{s_1,\ldots, s_n\}(s_1,\ldots,s_n): \textrm{sort of }\sigma$\qquad{} & $\texttt{\textbackslash{}not}\{s\}(s) :s$ \\
$\texttt{\textbackslash{}and}\{s\}(s, s):s$ & $\texttt{\textbackslash{}or}\{s\}(s, s):s$\\
$\texttt{\textbackslash{}implies}\{s\}(s, s):s$ & $\texttt{\textbackslash{}iff}\{s\}(s, s):s$\\
$\texttt{\textbackslash{}exists}\{s\}(\_, s):s$ & $\texttt{\textbackslash{}forall}\{s\}(\_, s):s$\\
$\texttt{\textbackslash{}mu}\{\,\}(s, s):s$ & $\texttt{\textbackslash{}nu}\{\,\}(s, s):s$\\
$\texttt{\textbackslash{}ceil}\{s_1, s_2\}(s_1):s_2$ & $\texttt{\textbackslash{}floor}\{s_1, s_2\}(s_1):s_2$\\
$\texttt{\textbackslash{}equals}\{s_1, s_2\}(s_1, s_1):s_2$ & $\texttt{\textbackslash{}in}\{s_1, s_2\}(s_1, s_1):s_2$\\
$\texttt{\textbackslash{}next}\{s\}(s):s$ & $\texttt{\textbackslash{}rewrites}\{s\}(s, s):s$\\
$\texttt{\textbackslash{}dv}\{s\}("v"):s$
\end{tabular}
\end{center}

\item \textbf{New axioms}:
\begin{align*}
\texttt{\textbackslash{}bottom}\{s\}() & \eqbynot \bot\\
\texttt{\textbackslash{}top}\{s\}() & \eqbynot \top_s\\
\sigma \{s_1,\ldots, s_n\}(\varphi_1,\ldots,\varphi_n) & \eqbynot \sigma(\varphi_1,\ldots,\varphi_n) \land \varphi_1\elOfSort s_1\land\cdots\land \varphi_n\elOfSort s_n\\
\texttt{\textbackslash{}not}\{s\}(\varphi) & \eqbynot \neg_s\varphi\displaybreak[0]\\
\texttt{\textbackslash{}and}\{s\}(\varphi_1, \varphi_2) & \eqbynot \varphi_1 \land \varphi_2 \displaybreak[0]\\
\texttt{\textbackslash{}or}\{s\}(\varphi_1, \varphi_2) & \eqbynot \varphi_1 \lor \varphi_2 \displaybreak[0]\\
\texttt{\textbackslash{}implies}\{s\}(\varphi_1, \varphi_2) & \eqbynot \texttt{\textbackslash{}or}\{s\}(\texttt{\textbackslash{}not}\{s\}(\varphi_1), \varphi_2)\displaybreak[0]\\
\texttt{\textbackslash{}iff}\{s\}(\varphi_1, \varphi_2) & \eqbynot \texttt{\textbackslash{}and}\{s\}(\texttt{\textbackslash{}implies}\{s\}(\varphi_1, \varphi_2),\\
& {}\qquad\qquad\quad~~\texttt{\textbackslash{}implies}\{s\}(\varphi_2, \varphi_1))\displaybreak[0]\\
\texttt{\textbackslash{}exists}\{s\}(x\cln s', \varphi) & \eqbynot \exists x\cln s'\ld \varphi \land \inh{s}\displaybreak[0]\\  
\texttt{\textbackslash{}forall}\{s\}(x\cln s', \varphi) & \eqbynot \texttt{\textbackslash{}not}\{s\}(\texttt{\textbackslash{}exists}\{s\}(x\cln s', \texttt{\textbackslash{}not}\{s\}(\varphi)))\displaybreak[0]\\ 
\texttt{\textbackslash{}mu}\{\,\}(X\cln s, \varphi) & \eqbynot (\mu X\ld \varphi) \land \inh{s} \displaybreak[0]\\
\texttt{\textbackslash{}nu}\{\,\}(X\cln s, \varphi) & \eqbynot 
\texttt{\textbackslash{}not}\{s\}(\texttt{\textbackslash{}mu}\{\,\}(X\cln s, \texttt{\textbackslash{}not}\{s\}(\varphi)))
\displaybreak[0]\\
\texttt{\textbackslash{}ceil}\{s_1, s_2\}(\varphi) & \eqbynot \ceil{\varphi}\land \inh{s_2}\displaybreak[0]\\
\texttt{\textbackslash{}floor}\{s_1, s_2\}(\varphi) & \eqbynot \texttt{\textbackslash{}not}\{s_2\}(\texttt{\textbackslash{}ceil}\{s_1, s_2\}(\texttt{\textbackslash{}not}\{s_1\}(\varphi)))\displaybreak[0]\\
\texttt{\textbackslash{}equals}\{s_1, s_2\}(\varphi_1, \varphi_2) & \eqbynot \texttt{\textbackslash{}floor}\{s_1, s_2\}(\texttt{\textbackslash{}iff}\{s_1\}(\varphi_1, \varphi_2))\displaybreak[0]\\
\texttt{\textbackslash{}in}\{s_1, s_2\}(\varphi_1, \varphi_2) & \eqbynot \texttt{\textbackslash{}floor}\{s_1, s_2\}(\texttt{\textbackslash{}implies}\{s_1\}(\varphi_1, \varphi_2))\displaybreak[0]\\
\texttt{\textbackslash{}next}\{s\}(\varphi) & \eqbynot \bullet{}\varphi\displaybreak[0]\\
\texttt{\textbackslash{}rewrites}\{s\}(\varphi_1, \varphi_2) & \eqbynot \texttt{\textbackslash{}implies}\{s\}(\varphi_1,\texttt{\textbackslash{}next}\{s\}(\varphi_2))\\
&\omit\rlap{$\vdash{}$\textbackslash{}dv$\{s\}("v")\elOfSort s$}  \\
&\omit\rlap{$\vdash{} (\varphi\subseteq \inh{s}) \limplies (\texttt{\textbackslash{}next}\{s\}(\varphi) \subseteq \inh{s})$}
\end{align*}
\end{enumerate}


\subsubsection{Proof System} \label{sec:proof_system}
With the basic matching logic syntax and its derived notations defined above in place, we also need a proof system that defines the provability relation $\vdash$ between theories and formulas. This is required so that we can write $\Gamma \vdash \varphi$, which represents $\varphi$ can be proved using the proof system, with patterns in $\Gamma$ added as additional axioms. 

Figure \ref{fig:hilbert-proof-system} shows the Hilbert-like proof system used for matching logic~\cite{CR19,CLR21a}. The proof rules are sound and can be divided into four categories: FOL reasoning, frame reasoning, fixpoint reasoning, and some technical rules.
$C,C_1,\text{and } C_2$ denote patterns that have a single placeholder variable $\hole$ that appears 
only within nested symbol applications (and not logical connectives). The notation $C[\varphi]$  is equivalent to $C[\varphi/\hole]$.
The FOL reasoning rules provide (complete) FOL reasoning (see, e.g., \cite{Sho67}). The frame reasoning rules state that application contexts are commutative with disjunctive connectives such as $\lor$ and $\exists$. The fixpoint reasoning rules support the standard fixpoint reasoning as in modal $\mu$-calculus \cite{Koz83}. The technical proof rules are needed for some completeness results (see \cite{CR19} for details). Since matching logic is the logical foundation of \K, the correctness of \K conducting one language task is reduced to the existence of a formal proof in matching logic, using the proof system in Figure~ \ref{fig:hilbert-proof-system}.

\begin{figure}[hbt]
    \centering
$
\begin{array}{l}
  \begin{array}{l}
  \rotatebox[origin=c]{90}{\textrm{FOL}}
  \end{array}
  \hspace*{-1.5ex}
  \begin{array}{l}
  \rotatebox[origin=c]{90}{\textrm{Reasoning}}
  \end{array}
  \left \{ \begin{array}{l} \\[24ex] \end{array} \right.
\\[-0.4ex]
  \begin{array}{l}
  \rotatebox[origin=c]{90}{\textrm{Technical}} \end{array}
  \hspace*{-1.1ex}
  \begin{array}{l}
  \rotatebox[origin=c]{90}{\textrm{Rules}}
  \end{array}
  \hspace*{-2ex}
  \left. \begin{array}{l} \\[6ex] \end{array} \right\{
\\[-0.4ex]
  \begin{array}{l} \\[13ex] \end{array}
  \hspace*{-2ex}
  \begin{array}{l} \rotatebox[origin=c]{90}{\textrm{Reasoning}}
  \end{array}
  \hspace*{-1.3ex}
  \begin{array}{l} \rotatebox[origin=c]{90}{\textrm{Frame}}
  \end{array}
  \hspace*{-2ex}
  \left. \begin{array}{l} \\[16ex] \end{array} \right\{
\\
  \begin{array}{l} \rotatebox[origin=c]{90}{\textrm{Reasoning}}
  \end{array}
  \hspace*{-1.5ex}
  \begin{array}{l} \rotatebox[origin=c]{90}{\textrm{Fixpoint}}
  \end{array}
  \hspace*{-2ex}
  \left. \begin{array}{l} \\[17ex] \end{array} \right\{
\end{array}
$
\hspace{-3ex}
\begin{tabular}{ll}
\hline\\[-1ex]
\prule{Tautology} &
$\varphi$ \quad
if $\varphi$ is a propositional
\\&\qquad tautology over patterns
\\[0.4ex]
\prule{Modus Ponens} &
$
\begin{prftree}
{\varphi_1}{\varphi_1 \imp \varphi_2}
{\varphi_2}
\end{prftree}$
\\[0.4ex]
\prule{$\exists$-Quantifier} &
$\varphi[y/x] \imp \exists x \ld \varphi$
\\[0.4ex]
\prule{$\exists$-Generalization} &
$
\begin{prftree}[r]{if $x \not\in \FV(\varphi_2)$}
{\varphi_1 \imp \varphi_2}
{(\exists x . \varphi_1) \imp \varphi_2}
\end{prftree}
$
\\[-1ex]
\\\hline
\\[-1ex]
\prule{Existence} &
$\exists x \ld x$
\\[0.4ex]
\prule{Singleton} &
$\neg \, (C_1[x \wedge \varphi] \wedge C_2[x \wedge \neg \varphi])$
\\[1.5ex]
\hline\\[-1ex]
\prule{Propagation$_\bot$} &
$C[\bot] \imp \bot$
\\[0.4ex]
\prule{Propagation$_\vee$} &
$C[\varphi_1 \vee \varphi_2] \imp
C[\varphi_1] \vee C[\varphi_2]$
\\[0.4ex]
\prule{Propagation$_\exists$} &
$C[\exists x \ld \varphi]
 \imp \exists x \ld C[\varphi]$ \ \
if $x \not\in \FV(C)$
\\[0.4ex]
\prule{Framing} &
$
\prftree{\varphi_1 \imp \varphi_2}
{C[\varphi_1]  \imp C[\varphi_2]}
$
\\[-1ex]
\\\hline\\[-1ex]
\prule{Substitution} &
$\prftree{\varphi}{\varphi[\psi/X]}$
\\[0.5ex]
\prule{Pre-Fixpoint} &
$\varphi [  \mu X \ld \, \varphi / X ] \imp \mu X \ld \, \varphi$
\\[0.5ex]
\prule{Knaster-Tarski} &
$\begin{prftree}
{ \varphi[\psi/X] \imp \psi }
{\mu X \ld \, \varphi \imp \psi}
\end{prftree}$
\\[-1ex]
\\\hline
\end{tabular}
    \caption{Hilbert proof System}
    \label{fig:hilbert-proof-system}
\end{figure}



\subsection{Zero-Knowledge Basics}

Highly related to our work are the concepts of \textit{Zero-Knowledge Cryptography} and, more specifically, \textit{Zero-Knowledge Virtual Machine}, or zkVM.

A generic zero-knowledge proof system designed to verify a particular computation typically requires that the computation be specified using some \textit{arithmetization}.  An arithmetization is a way to represent the computation as a system of equations, typically over a finite field or over a ring of polynomials over a finite field. This representation depends on the proof system being used and the cryptographic constructions on which the proof system is based.

A zkVM, by contrast, is a zero-knowledge proof system that verifies computations described by a program that runs on a virtual machine. Rather than requiring the computation to be arithmetized to start with, a zkVM system handles the conversion of the program to arithmetic form, allowing programs written in high-level languages, even programs not initially designed with verifiable computing in mind, to be used in zero-knowledge proof systems.

The zkVM abstraction is relevant to our work for two reasons. First, we are dealing with formal systems which, up to now, have not been designed with zero-knowledge in mind and which have been implemented in high-level programming languages. It is, therefore, an obvious possibility that existing zkVM systems could be used to construct our Proof of Proof system. Indeed, as shown in Section \ref{sec:zkVMs}, we have carried out implementations of our Proof of Proof system within a number of zkVM systems -- that section describes our experiments and results.

Second, because our Proof of Proof system is designed to handle verifiable computation for arbitrary programming languages, any implementation of the system is bound to share features in common with zkVM systems. In Section
\ref{sec:block_model}, we present our research into the design of a Proof of Proof system that is not based on existing zkVMs but rather is designed from first principles to best leverage zero-knowledge techniques for maximal efficiency.

\section{Math Proof Generation} \label{sec:mpg}

As the name suggests, the Math Proof Generation (MPG) process generates mathematical proofs from the execution steps of programs.
From the Curry-Howard correspondence \cite{howard1980formulae}, we know that there is a direct relationship between computer programs and mathematical proofs, and thus we can convert from programs to proofs and vice versa.
MPG refines this correspondence and pushes it one step further, automatically generating machine-checkable mathematical proofs from \textit{program executions}.
That is, the execution of any program in any programming language that has a formal semantics in \K is \textit{automatically} substantiated with a formal mathematical proof.  Moreover, that formal proof is verifiable independently of \K or other frameworks, implementations, or systems.

The general flow of how a mathematical proof, $Proof$, is generated from a program, $Program$, of a given language, $Lang$, can be seen in Figure \ref{fig:workflow} and it goes like this:

\begin{enumerate}
    \item Given the semantics of $Lang$ written in \K framework, it will be compiled into its Kore format as the $Lang$ Math Theory.
    \item \K's LLVM instrumented execution backend will take in a) the $Lang$ Math Theory and b) the $Prog$, together with c) the other execution environment inputs to generate proof hints. Proof hints are execution traces that the program has taken based on the defined semantics $Lang$ (more on proof hints later).
    \item The MPG process will take in a) the proof hints generated from the $Prog$ and b) the $Lang$ Math Theory, together with c) additional rules from some pre-defined proof calculus, to generate an internal representation of a Math Proof.
    \item This internal representation of the Math Proof is then serialized to a proof checker format such as Metamath or a specialized block model, which is machine-verifiable either directly via the designated proof checker or via a zkVM.
\end{enumerate}

To provide more in-depth details of the points mentioned above, this section is broken into the following parts:

\begin{itemize}
    \item Section \ref{sec:langdef_as_ml} provides basic knowledge of how language definitions are defined as Matching Logic (\ML) theories. As the underlying logic behind \K is \ML, it is important to understand how the language definitions defined in \K can be viewed as \ML theories. This in turn can help us understand how a program can be broken down into execution steps, proof hints, and lastly, generated to a mathematical proof in later subsections.
    \item Section \ref{sec:proof_calculus} mentions the additional relations, predicates, and rules needed for our MPG process. Other than the matching logic proof system mentioned in Section \ref{sec:proof_system}, these new relations, predicates, and rules better facilitate the generation of mathematical proofs in the MPG process.
    \item Section \ref{sec:proof_hints} shares more details on the types of proof hints and how they are generated before passing them to the MPG process. These proof hints are essential in generating the mathematical proof of a given program as these are steps taken by the program that goes from an initial state to a final state. These hints will in turn guide us on how we should build the proof for the program.
    \item Section \ref{sec:proof_generation} details how the MPG process reads proof hints one at a time, processes every type of them, and eventually generates the proof of the program. This is the crux of the MPG, as this process generates the machine-verifiable proof of the correctness of the program.
    \item Section \ref{sec:proof_checker} enumerates the two main proof checker formats that the MPG can serialize to. Note that the MPG process will first generate an internal representation of a mathematical proof, which needs to be generic and reusable in the sense that it should be versatile to be serialized to any proof checker formats that we chose.
\end{itemize}


\subsection{Language Definitions as Matching Logic (\ML) Theories} \label{sec:langdef_as_ml}

A programming language definition $L$ specifies, via \emph{notation}, a \ML theory $\Gamma^L$ consisting of:
\begin{enumerate}
\item 
A theory $\Gamma^T$ for each builtin datatype $T$
\item 
A theory $\Gamma^{\it Syn(L)}$ specifying the syntax of $L$
\item 
A theory $\Gamma^{\it Sem(L)}$ specifying the semantics of $L$
\item 
A theory $\Gamma^{\it Simpl(L)}$ specifying the simplification rules of $L$
\end{enumerate}
We exemplify these theories for the imperative language defined in Fig.~\ref{fig:imp}.

\paragraph{Builtin theories $\Gamma^T$\\} The theories specifying the imported builtin datatypes $T$ include:
\begin{enumerate}
\item A theory $\Gamma^{\INT}$ specifying the integers. This consists of a sort $\it Int$, functional symbols \PlusInt\ and \MinusInt, a predicate symbol \DiffInt, and all axioms of the form $\PlusInt(1, 2) = 3$ and $\DiffInt(1, 0)$.
\item A theory $\Gamma^{\MAP}$ of maps. This includes the empty map \dotMap, the map element constructor $\_{\mapsto}\_$, the associative\&commutative concatenation constructor $\_\,\_$, and the operations $\it lookup$ and $\it update$.
\item A theory $\Gamma^\ID$ of identifiers.
\item A theory $\Gamma^\IDS$ of identifier lists, with the empty lists constructor \dotIds, and the associative concatenation $\_,\_$.
\item A theory $\Gamma^K$, which specifies a program's computational units and the order in which they are computed.
\end{enumerate}
A complete specification of these theories is impractical. Therefore they are only partially specified and can be (conservatively) extended at runtime with trusted evaluations given from outside. We will denote by $\mathcal{B}$ the theory that extends the theories $\Gamma^T$, and will explain its construction in~\cref{sec:proof_gen_alg}.

\paragraph{The theory $\Gamma\sp{\it Syn(L)}$\\} Each non-terminal, e.g., \Exp, specifies a sort, and each syntax rule defines a symbol together with the axioms specifying its functional type and the fact that is a constructor. For instance, the syntax rule \verb|Exp ::= Exp "+" Exp| specifies a symbol, say \Plus, together with the following axioms:
\begin{align}
&\forall x:\Exp.\forall y:\Exp. \exists z:\Exp. \Plus(x,y) = z\label{eq:plus1}\\
&\forall x_1,x_2:\Exp.\forall y_1,y_2:\Exp. \Plus(x_1,y_1) = \Plus(x_2,y_2) \rightarrow x_1 = x_2 \land y_1 = y_2\label{eq:plus2}\\
&\forall x_1,x_2:\Exp.\forall y_1,y_2:\Exp. \neg(\Plus(x_1,y_1) = \Minus(x_2,y_2))\label{eq:plus3}
\end{align}
The carrier set of a non-terminal sort is inductively defined, e.g.,
\[
\Exp = \mu X.\Int \lor \Id \lor \Plus(X, X) \lor \Minus(X,X)
\]

\paragraph{The theory $\Gamma^{\it Sem(L)}$\\}Specifies the transition steps that give the operational semantics of a program. For example, the semantic rule that evaluates a program variable
\begin{alltt}
    rule <k> \(X\):Id => \(I\) ...</k>
         <state>... \(X\) |-> \(I\) ...</state>
\end{alltt}
is a notation for the configuration rewrite rule
\begin{center}
\begin{tabular}{lcl}
\begin{minipage}{.4\textwidth}\footnotesize
\begin{alltt}
<T>
  <k> \(X\) \(\sim\)>\(\it VarK\) </k>
  <state>... \(X\) |-> \(I\) ...</state>
</T>
\end{alltt}
\end{minipage}
&
$\Rightarrow$
&
\begin{minipage}{.4\textwidth}\footnotesize
\begin{alltt}
<T>
  <k> \(I\) \(\sim\)>\(\it VarK\) </k>
  <state>... \(X\) |-> \(I\) ...</state>
</T>
\end{alltt}
\end{minipage}
\end{tabular}
\end{center}
and specified as an \ML axiom
\begin{align*}\it
&TCell(kCell(kseq(X, VarK)),stateCell(M))\\
&{}\rightarrow{}\\
&\bullet TCell(kCell(kseq(lookup(M, X), VarK)),stateCell(M))   
\end{align*}
We can also see that the conditional semantic rule
\begin{alltt}
    rule if (\(I\)) \(S\) _ => \(S\) requires \(I\) =/=Int \(0\) 
\end{alltt}
is specified by an \ML axiom as follows:
\begin{align*}\it
&\DiffInt(I, 0) \land TCell(kCell(kseq(If(I, S, S_2), VarK)),stateCell(M))\\
&{}\rightarrow{}\\
&\bullet TCell(kCell(kseq(S, VarK)),stateCell(M))   
\end{align*}
We conventionally write a conditional semantic rule as 
\[
(\phi \land \ell) \Rightarrow_{\it semrew} r
\]
where $\phi$ is the predicate pattern specifying the condition, $\ell$ is the configuration pattern specifying the left-hand side of the rewrite rule, and $r$ is the configuration pattern specifying the right-hand side of the rewrite rule. It is just a notation for the \ML pattern is $(\phi \land\ell) \rightarrow\bullet r$.
If $\phi$ is $\top$, then rule is written as $\ell \Rightarrow_{\it semrew} r$.

\paragraph{The theory $\Gamma^{\it Simpl(L)}$\\} Specifies how the builtin or user-defined functions are computed. 
For example, the rule defining an update of a map
\begin{verbatim}
 rule (K |-> _ M:Map) [ K <- V ] => (K |-> V M) [simplification]
\end{verbatim}
is specified by an \ML axiom of the form
\[
\texttt{Map:update}(\_\,\_(\_{\mapsto}\_(K, X), M), V) = (\_\,\_(\_{\mapsto}\_(K, V), M))
\]
A conditional simplification rule is written as
\[
(\phi \land \ell) =_{\it simpl} r
\]
and it can be seen as a notation for $(\phi \land \ell) = r$. If $\phi$ is $\top$, then rule is written as 
$\ell =_{\it simpl} r$.

\subsubsection{Language Definitions as Kore Theories}
\label{sec:kore-definition}

The current version of \K translates a programming language definition into a Kore theory (see~\Cref{sec:kore}), using the following syntax:
\begin{alltt}
  \(\Sentence\)
    ::= "sort" \(\SortId\) "{" \(\SortVariables\) "}" "[" \(\Attributes\) "]"
      | "symbol" \(\SymbolId\) "\{" \(\SortVariables\) "\}" "(" \(\Sorts\) ")" ":" \(\Sort\) 
                                                 "[" \(\Attributes\) "]"
      | "axiom" "\{" \(\SortVariables\) "\}" \(\PatternIt\) "[" \(\Attributes\) "]"
      | "claim" "\{" \(\SortVariables\) "\}" \(\PatternIt\) "[" \(\Attributes\) "]" 
\end{alltt}
For example, for the syntax rule \verb|Exp ::= Exp "+" Exp|, the next theory fragment is generated:
\begin{verbatim}
symbol Plus {}(SortAExp{}, SortAExp{}) : SortAExp{} 
                    [constructor{}(), functional{}()]

axiom{R} \exists{R}(
     Val:SortAExp{}, 
     \equals{SortAExp{}, R} (Val:SortAExp{}, 
                             Plus{}(K0:SortAExp{}, K1:SortAExp{})
                            )
) [functional{}()] // functional

axiom{} \implies{SortAExp{}}( 
    \and{SortAExp{}}(
        Plus{}(X0:SortAExp{}, X1:SortAExp{}), 
        Plus{}(Y0:SortAExp{}, Y1:SortAExp{})
    ), 
    Plus{}(
        \and{SortAExp{}} (X0:SortAExp{}, Y0:SortAExp{}), 
        \and{SortAExp{}} (X1:SortAExp{}, Y1:SortAExp{})
    )
) [constructor{}()] // no confusion same constructor

axiom{} \not{SortAExp{}} (
    \and{SortAExp{}} (
        Plus{}(X0:SortAExp{}, X1:SortAExp{}), 
        Minus{}(Y0:SortAExp{}, Y1:SortAExp{})
    )
) [constructor{}()] // no confusion different constructors
\end{verbatim}
The three axioms are equivalent to \eqref{eq:plus1}-\eqref{eq:plus3} on page \pageref{eq:plus1}.

The rule
\begin{verbatim}
rule <k> X = I:Int; => .K ...</k> 
     <state>... X |-> (_ => I) ...</state>
\end{verbatim}
is translated into a Kore axiom as follows:
\begin{verbatim}
axiom{} \rewrites{TCell} (
    \and{TCell} (
        <T>(
          <k>(kseq(assign(VarX:Id, VarI:Int), DVar2:K)),
          <state>(concMap(mapItem(VarX:Id, Gen0:KItem), DotVar3:Map))
        ),
        \top{TCell}
    ),
    \and{TCell} (
        <T>(
          <k>(DotVar2:K),
          <state>(concMap(mapItem(VarX:Id, VarI:Int), DotVar3:Map))
        ), 
        \top{TCell}
    )
)
\end{verbatim}
where \verb'<T>' is the topmost configuration cell.

\subsubsection{Running Programs using the Language Definition} \label{sec:running-programs}
\label{sec:run_lang_def}

An execution 
$t_0 \Rightarrow^1 t_1 \Rightarrow^1 \cdots \Rightarrow^1 t_n$
is obtained using the theory $\Gamma^L$ defining $L$.
An execution step $t_i  \Rightarrow^1 t_{i+1}$ is broken down into two substeps:
\begin{enumerate}
\item 
$t_i \Rightarrow_{\it sem} tt_{i+1}$ consisting of the application of a semantic (rewrite) rule $\phi \land \ell\Rightarrow_{\it semrew} r$;
\item 
$tt_ {i+1} =^!_ {\it simpl} t_ {i+1}$ consisting of the application of the simplification rules such as function evaluation rules as much as possible (marked by $=^!_ {\it simpl}$).
\end{enumerate}

Intuitively, the fact that $t_i  \Rightarrow_{\it sem} tt_{i+1}$ is obtained using the semantic rule $\ell \land \phi \Rightarrow_{\it semrew} r$ means that 
\begin{enumerate}
\item 
$t_i$ matches the left-hand side $\ell$ of the rule via a substitution $\theta$, i.e., $t_i=\ell\theta$
\item 
The substitution $\theta$ satisfies the condition $\phi$, i.e., $\Gamma^L\vdash \phi\theta$
\item 
$tt_ {i+1}$ is obtained by applying $\theta$ to $r$, i.e., $tt_ {i+1}=r\theta$.
\end{enumerate}
  
A rewrite rule can be applied only when the current configuration is in a normal form. 
The theory $\Gamma^L$ may include \emph{simplification rules} $\phi \land \ell =_ {\it simpl} r$ that transform a pattern into an equivalent one. A configuration is in a \emph{normal form} if no simplifications can be applied. A simplification step $tt_{i+1} =^!_ {simpl} t_ {i+1}$ computes the normal form $t_ {i+1}$ of $tt_ {i+1}$.

We write $t \Rightarrow t'$ if there is an execution from $t$ to $t'$:
\[
\dfrac{t\Rightarrow^1 t'}{t\Rightarrow t'}
\qquad
\dfrac{t\Rightarrow^1 t'\quad t'\Rightarrow t''}{t\Rightarrow t''}
\]

\subsection{Proof Calculus}
\label{sec:proof_calculus}

The proof calculus consists of the matching logic proof system, well-formedness (type-checking) rules, variable substitutions, rule instantiation and derived rules. The reason for extending the proof system by incorporating these additional relations, predicates, and derived rules is that they aim to improve coverage and streamline the proof generation process. As a result, it enables a more comprehensive and efficient reasoning framework.




\subsubsection{Relations/Predicates}

\paragraph{Well-formedness}


\begin{description}
\item[$\WfTerm(t,s)$] denotes the fact that $t$ is a well-formed term pattern of sorts $s$.
\item[$\WfSubst(\mbox{$\theta$})$] denotes the fact that the substitution $\theta$ is well-formed, i.e., for each $x\mapsto u \in \theta$, $\WfTerm(u,s)$ and $\WfTerm(x,s)$ for certain sort $s$.
\item[$\WfPred(\mbox{$\phi$})$] denotes the fact that $\phi$ is a well-formed predicate pattern.
\end{description}

\paragraph{Element variables substitution\\}

A substitution $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$ can be seen as a notation for the \ML pattern $\theta^= \equiv x_1=u_1\land\cdots\land x_k=u_k$, where the element variables $x_i$ and the term patterns $u_i$ are of the same sort. The result $\varphi\theta$ of applying $\theta$ to a pattern $\varphi$ can be seen as a notation for $\varphi\land \theta^=$, assuming that variables $x_i$ are fresh. We also write $\varphi[\overline{u}/
\overline{x}]$ for $\varphi\theta$.

\paragraph{Set variable substitution\\}
If $X$ is a set variable and $\varphi, \psi$ are patterns, then $\varphi[\psi/X]$ denotes the capture-avoid substitution, obtained by replacing the free occurrences of $X$ in $\varphi$ by $\psi$.

\paragraph{Rule instantiation\\} The (derived) inference rules are in fact rule schemes, i.e., they are written using meta-variables. For instance, in the \textsc{Modus Ponens} rule
\[
\dfrac{\varphi_1\quad \varphi_1\rightarrow \varphi_2}
{\varphi2}
\]
$\varphi_1$ and $\varphi_2$ are meta-variables. An \emph{instantiation} of the rule is obtained by replacing the meta-variables with well-formed patterns.


\subsubsection{Derived Rules}

As our proof generation process is heavily influenced by the proof hints generated from the \K's LLVM backend, having specialized derived rules is beneficial in facilitating the process of generating the mathematical proofs. Each of the derived rules stated in this subsection will be applied in the proof generation process depending on the type of proof hint received at a given point in time. Further elaboration on which derived rules should be applied for which type of proof hint will be discussed in Section \ref{sec:proof_gen_alg}.



\paragraph{Application of a semantic rewrite rule}


\[
\dfrac
{
(\phi \land \ell \rightarrow {}\bullet{} r) \in \Gamma^{\it Sem(L)}\quad  \phi[\overline{u}/\overline{x}] \quad t = \ell[\overline{u}/\overline{x}]\quad t' = r[\overline{u}/\overline{x}]
}
{t \rightarrow {}\bullet{} t'} \tag{RewRl}\label{eq:RewRl}
\]

\paragraph{Application of a simplification rewrite rule}

\[
\dfrac{
(\phi \land \ell = r) \in \Gamma^{\it Simpl(L)}\quad \phi[\overline{u}/\overline{x}] \quad t = \ell[\overline{u}/\overline{x}]\quad t' = r[\overline{u}/\overline{x}] \tag{SimplRl}\label{eq:SimplRl}
}
{t = t'}
\]

\paragraph{Congruence}

\[
\dfrac
{u_1=v_1\quad \ldots\quad u_n=v_n\quad t'=t[\overline{u}/\overline{x}]\quad t''=t[\overline{v}/\overline{x}]}
{t' = t''} \tag{Congr}\label{eq:Congr}
\]

\paragraph{Equality transitivity}

\[
\dfrac
{t_1 = t_{2}\quad t_{2}  = t_{3}}{t_1 = t_{3}} \tag{EqTrans}\label{eq:EqTrans}
\]

\paragraph{Transition relation step}
\[
\dfrac
{t \rightarrow {}\bullet{} t'\quad t' = t''}
{t \rightarrow \Diamond t''} \tag{TrRelStep}\label{eq:TrRelStep}
\]
where $\Diamond t'' \equiv \mu X. t'' \lor \bullet X$~\cite{CR19}.


\paragraph{Transition relation transitivity}

\[
\dfrac
{t_1  \rightarrow \Diamond t_{2}\quad t_{2}  \rightarrow \Diamond t_{3}}
{t_1  \rightarrow \Diamond t_{3}} \tag{TrRelTrans}\label{eq:TrRelTrans}
\]

\paragraph{Semantic rewrite rules are well-formed}

\[
\dfrac
{(\phi \land \ell \rightarrow {}\bullet{}  r) \in \Gamma^{\it Sem(L)}}
{\WfPred(\phi) \quad \WfTerm(\ell, s) \quad \WfTerm(r, s)} \tag{WfRewRl}\label{eq:WfRewRl}
\]
where $s$ is the sort for program configurations.

\paragraph{Simplification rewrite rules are well-formed}

\[
\dfrac
{(\phi \land \ell =  r) \in \Gamma^{\it Simpl(L)}}
{\WfPred(\phi) \quad \WfTerm(\ell, s) \quad \WfTerm(r, s)} \tag{WfSimplRl}\label{eq:WfSimplRl}
\]
for certain sort $s$.

\paragraph{Well-formedness/Type preservation}

\[
\dfrac
{\WfPred(\phi) \quad \WfSubst(\overline{x}\mapsto \overline{u})}
{\WfPred(\phi[\overline{u}/\overline{x}])}
\qquad
\dfrac
{\WfTerm(t, s) \quad \WfSubst(\overline{x}\mapsto \overline{u})}
{\WfTerm(t[\overline{u}/\overline{x}], s)} \tag{WfPres}\label{eq:WfPres}
\]

\subsection{Proof Hints} \label{sec:proof_hints}


The LLVM backend of the \K Framework has been enhanced with the capability to instrument the generated code to produce proof hints. The role of these proof hints is to allow communication between the interpreter and the proof generation engine, providing information such as the specific axioms that should be applied, their order, their respective substitutions, and the part of the final proof that they contribute to. The purpose of hints is, thus, twofold. First, their sequence corresponds to an execution trace of the program being interpreted. Second, and most crucially, they enrich this execution trace with the mathematical information necessary to guide proof generation. These proof hints are categorized into different types, depending on the events occurring at the point of execution and follow a grammar defined in the BNF style that can be found in \cite{proof-hints-doc}. The section below describes the types of proof hints.


\subsubsection{Types of Proof Hints} \label{subsec:types_proof_hints}

Each kind of hint event contains specific information describing the execution of a proof-related piece of code. A common feature between different hint types is the presence of a \textit{rule ordinal}, which is a number corresponding to the nth axiom in a Kore definition (see~\Cref{sec:kore-definition}). These numbers are assigned during the axiom preprocessing phase by the LLVM Backend. The purpose of ordinals is to refer to an axiom in the Kore definition (which corresponds to a rule in theory $\Gamma^L$), from within the proof hints which emit them.

Currently, the backend can emit the following 8 types of proof hints during a program execution:

\begin{itemize}
    \item \textbf{Function event:} This hint event is produced as soon as the interpreter starts the evaluation of a function. It contains the name and arguments of the function being evaluated and its relative position on the stack of evaluations. The arguments of the functions are Kore terms themselves.
    \item \textbf{Function exit event:} This hint event is produced when the interpreter finishes the evaluation of a function. It contains the ordinal of the rule used to simplify the last-open function context,
    and whether the function exited via a tail call or a conventional return statement. This event is mainly useful for computing the call stack of the various simplifications in a proof hint trace.
    \item \textbf{Rule event:} This hint event is produced when the interpreter starts to evaluate a rewrite rule and its arguments. It provides the ordinal of the rule being applied along with a substitution to instantiate it, $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$.
    \item \textbf{Pattern matching failure event:} This hint event is produced when no axiom matches the subterm referred to by the most recent function event. That is, it tells the MPG process (\cref{sec:proof_generation}) that no rule should be applied to simplify a function further. As \K implements subsort overloading (see ~\cite{K-user-manual}), these events are often emitted when dealing with overloaded constructors, which are constructors-modulo-axioms. As information, they provide the name of the function that could not match any rule.

    \item \textbf{Side condition entry event:} This hint event is produced when the interpreter starts evaluating the side condition of a rule. It provides the rule ordinal and the substitution $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$ to be applied to the side condition term.
    \item \textbf{Side condition exit event:} This hint event is emitted once side condition evaluation finishes. It provides the rule ordinal, as well as the final result of evaluation (e.g., “true”).
    \item \textbf{Hook event:} This hint event is emitted when a hook function occurring at a certain relative position is called. These are special kinds of built-in functions for which the simplification rules in $\Gamma^T$ (see \cref{sec:langdef_as_ml}) are bypassed (or not defined at all) without a high-level evaluation. Instead, their evaluation is done by directly computing the result in the machine code level, which is also transmitted at the end of the hook event output on the trace. This is useful for, e.g., arithmetic computation, where evaluation can potentially lead to a large number of events being emitted.
    \item \textbf{Configuration pattern event:} This event contains the Kore representation of a \K configuration. Usually, it happens as an initial or final configuration, but it can also appear as an intermediate configuration, between rewrites, if the user sets the corresponding flag in the program execution command.
\end{itemize}

\subsubsection{Proof Hints Generation}

The generation of proof hints is achieved through instrumentation of the generated code by the LLVM backend, with additional instructions that are responsible for outputting a proof hint event. Each language definition compiled by the \K Framework, using the LLVM backend with the appropriate flags, will have this instrumented code that will output the proof trace of executions.

The code generator of the LLVM backend is responsible for generating code that implements pattern matching as directed by a Maranget-like decision tree as shown in ~\cite{maranget2008,llvm-backend-2025},
as well as the rewriting that should happen when a leaf node is reached in the tree, which corresponds to a rewrite rule. The main loop of execution implements the idea from  \Cref{sec:run_lang_def} as follows:
\begin{enumerate}
    \item Given a Kore term, walk the decision tree to reach a leaf node.
    \item Apply the rewrite rule that corresponds to the reached node to the Kore term.
    \item Repeat for the new Kore term we get after applying the rewrite rule.
\end{enumerate}

The execution terminates if, in Step 1, we fail to find a match, i.e., we end up in a special node of the decision tree that represents a pattern matching failure. Otherwise, the execution will eventually terminate if all Kore terms have been correctly evaluated.

The additional instrumented code is generated between Steps 1 and 2, and it is guarded by some conditions that can be controlled by flags passed to the language semantics's binary interpreter. So, the interpreter can be used to only execute a program, execute and output the proof trace, or even execute and output the proof trace with intermediate configuration events that can be used for debugging purposes. The two last modes are set when invoking the interpreter with the appropriate flags.


\subsection{Proof Generation} \label{sec:proof_generation}

\subsubsection{Main Idea} \label{sec:proof_generation_main_idea}

The MPG problem can be stated as follows:\\

\noindent \fbox{
\begin{minipage}{\textwidth}
\begin{description}
\item[Input:] A language definition $L$ and a claim of the form $t \Rightarrow^* t'$, where $t$ and $t'$ are two program configurations in $L$.
\item[Output:] A proof of the fact that there exists an execution 
   $t_0 \Rightarrow^1 t_1 \Rightarrow^1 \cdots \Rightarrow^1 t_n$ 
   in $L$ with $t=t_0$ and $t_n=t'$, if any. 
\end{description}
\end{minipage}
}\\

In terms of \ML, the above problem is stated as follows:\\

\noindent \fbox{
\begin{minipage}{\textwidth}
\begin{description}
\item[Input:] An \ML theory $\Gamma^L$ specifying $L$, and a claim represented as an \ML pattern $t \rightarrow \Diamond t'$ with $t,t'$ terms of sort $Cfg$ (= the sort for configurations). 
\item[Output:]  A proof of $\Gamma^L \vdash t \rightarrow \Diamond t'$, if any.  
\end{description}
\end{minipage}
}\\

A proof for $\Gamma^L \vdash t \rightarrow \Diamond t'$ can be obtained using the execution $t_0 \Rightarrow^1 t_1 \Rightarrow^1 \cdots \Rightarrow^1 t_n$, where $t=t_0$ and $t_n=t'$. The general idea of how the proof can be generated is as follows:

\noindent \fbox{
\begin{minipage}{\textwidth}
\textbf{Sketch of MPG algorithm:}

\begin{enumerate}
\item \label{mpg-main-1}
For each step $t_i  \Rightarrow^1 t_ {i+1}$ a proof for $\Gamma^L \vdash t_i  \rightarrow {}\Diamond t_ {i+1}$ is built. Recall that such a step is obtained by applying a rule $\phi \land \ell\Rightarrow_{\it semrew} r$. The main idea of the proof generation process is as follows:
\begin{enumerate}
\item \label{mpg-main-1a}
$t_i \Rightarrow_{\it sem} tt_{i+1}$ is just a notation for $t_i  \rightarrow{}\bullet tt_{i+1}$ and its proof consists of
\begin{enumerate}
\item \label{mpg-main-1ai}
generating proof for the side condition, if any;
\item \label{mpg-main-1aii}
generating proof for the equality between the current configuration $t_i$ and the instance of the left-hand side of the rule;
\item \label{mpg-main-1aiii}
$tt_{i+1}$ is the instance of the right-hand side of the rule;
\item \label{mpg-main-1aiv}
instantiating \eqref{eq:RewRl};
\end{enumerate}
\item \label{mpg-main-1b}
the proof for the substep
$tt_ {i+1} =^!_ {\it simpl} t_ {i+1}$ consists of:
\begin{enumerate}
\item \label{mpg-main-1bi}
generating proof for each simplification rule applied;
\item \label{mpg-main-1bii}
instantiating \eqref{eq:EqTrans}, whenever it is needed;
\item \label{mpg-main-1biii}
instantiating \eqref{eq:Congr}, whenever it is needed.
\end{enumerate}
\item \label{mpg-main-1c}
apply \eqref{eq:TrRelStep}.
\end{enumerate}
\item \label{mpg-main-2}
Using the following instantiations of the transitivity rule \eqref{eq:TrRelTrans}
$$
\dfrac{t_0  \rightarrow{}\Diamond t_{i}\quad t_{i}  \rightarrow{}\Diamond t_{i+1}}{t_0  \rightarrow{}\Diamond t_{i+1}} 
$$
for $i=1,\ldots, n-1$, we obtain a proof for $t_0  \rightarrow{}\Diamond t_{n}$.
\end{enumerate}
\end{minipage}
}

\subsubsection{Proof Generation Guided by Proof Hints}
\label{sec:proof_gen_alg}

While the foregoing serves as a general outline, the specific manner in which proof generation proceeds will be dependent on the program being executed. As mentioned in Section \ref{sec:proof_hints}, proof hints provide critical information, including the axioms to be used, the substitutions to instantiate them by, the subterms that they rewrite, and the order to apply them. This information is necessary as it helps to guide the proof generation process.

\paragraph{Builtin theory $\mathcal{B}$\\}
As mentioned in~\Cref{sec:langdef_as_ml}, the builtin theories $\Gamma^T$ are incomplete. Here we describe how they are conservatively extended with a dynamically built theory $\mathcal{B}$.
Consequently, the generated proof is modulo builtin theory $\mathcal{B}$, which includes all the claims describing computations given by the builtin functions/operations. This theory is trusted or it is checked by an external tool. This theory is built using the \textit{Hook events}. Such a hint includes the name of the builtin function/operation, its arguments $\overline{a}$ (if any), and the result $v$. Then a claim of the form $f(\overline{a})=v$ is included in $\mathcal{B}$. A simple example is $\PlusInt(1, 2) = 3$.

\paragraph{Simplification/Evaluation strategy\\} 
The evaluation of the side conditions and the simplification substeps are based on the same operations, application of simplification rules, and/or hook functions. Therefore the proof generation is based on a sequence of hints consisting of \textit{Function events}, \textit{Rule events}, and \textit{Hook events}. \textit{Pattern Matching Failure events} also belong to this category, but they do not mutate the evaluated term in any way, as their meaning is that no simplification could be applied (see \cref{sec:proof_hints}). Here we describe a strategy for generating a
proof chunk for such a sequence. It is the most challenging part since some hint events could be nested. Therefore, the sequence of hints is organized into a hierarchy of \emph{regions}, such that a proof chunk corresponds to each region. After the proof chunks of a region are generated, these are aggregated:
\begin{itemize}
\item Using instantiations of the equality transitivity rule~\eqref{eq:EqTrans}, to contract chains of equalities.
\item Using instantiations of the congruence rule~\eqref{eq:Congr}, to propagate the equalities to the parent region. The idea is that the hierarchy of regions reflects the subterm structure, where the simplifications hold.
\end{itemize}
This building process of the region hierarchy is guided by the \textit{Function Exit events} and the relative positions.
The final proof chunk of the hint sequence is that corresponding to the top region. An advantage of this strategy is that the regions can be generated in parallel.

Now we describe how the hints are used to generate the proof chunks for the main steps of the algorithm sketched in~\Cref{sec:proof_generation_main_idea}.

\begin{description}
\item[\cref{mpg-main-1ai}] 
The proof chunk for the evaluation of a side condition $\phi[\overline{u}/\overline{x}]$ is built using the hints emitted during a side condition evaluation, which are marked by a \textit{Side Condition entry event} and its corresponding \textit{Side Condition Exit event}. 
The substitution $\overline{u}/\overline{x}$ is given by the corresponding hint events. The proof chunk is built using the \textit{Simplification/Evaluation strategy}. 
\item[\cref{mpg-main-1aii}] 
The proof chunk can be built by a simultaneous traversal of the configurations and applying in a bottom-up manner the congruence rule ~\eqref{eq:Congr}. Note that this chunk must be constructed modulo the associative-commutative axioms of certain constructors, which adds additional complexity.
\item[\cref{mpg-main-1b}]
The proof chunk is built using the \textit{Simplification/Evaluation strategy}. 
\item[\cref{mpg-main-1c}]
This step aggregates the proof chunks generated at \cref{mpg-main-1a} and \cref{mpg-main-1b}.
\item[\cref{mpg-main-2}] 
The region approach is extended to be applied to the entire proof of the execution. The hints for each step $t_i\Rightarrow^1 t_{i+1}$ form a subregion of the top region, and the transitivity aggregates the proof chunks of these regions.
\end{description}


\iffalse
\todo[author=DL,inline]{STOP proposal.}

\begin{figure}
    \centering
    \includegraphics[width=0.65\linewidth]{figures/trace regions compressed.png}
    \caption{Example hint trace, with regions highlighted}
    \label{fig:hint_trace}
\end{figure}

If we were to log proof hints to some textual format, we would see an output similar to the one provided in Figure \ref{fig:hint_trace}. The key observation we make is that hint traces exhibit a highly regular structure, which allows a direct correspondence between \textit{portions of execution} to \textit{portions of the final proof}. Figure \ref{fig:hint_trace} highlights each of the regions we are interested in, their precise sense being explained below.

The goal is to compile each hint trace region to a \textit{derived proof rule}. For each of these derived proof rules, we will state the \textit{premise/s} it requires, the \textit{statement} it proves, and how its proof will be constructed. In turn, the premises of a region become the statements of its corresponding sub-regions.

The following subsections serve as a specification of the algorithm to compile hints down to mathematical proofs. It is beyond the scope of this whitepaper to provide exact implementation details, being the purpose of ongoing engineering effort to find the best performing implementation of the following specification.

We begin by specifying the interpretation of individual hints. We will then move on to see how their sequences should be treated, each of which we will subsequently call \textit{hint regions}.

\subsubsection*{Rule event}
As explained in section \ref{sec:proof_hints}, a rule event contains a pointer to an axiom in $\Gamma^{\it Sem(L)} \cup \Gamma^{\it Simpl(L)}$ (a so-called "rule ordinal"), and a substitution. Let $\phi$ and $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$ be the axiom and substitution, respectively.

It proves the following rule with no premises:
\[
\dfrac{}{\phi[\overline{u}/\overline{x}]}
\tag{RULE EVENT}\label{rule:rule_event}
\]

This is a simple instantiation, as obtained by applying rule ???.

\subsubsection*{ALL region}

\todo[author=DL,inline]{"ALL" is not a very good name. What about "MAIN"? od "EXECUTION"?}

This is the largest region occuring in a hints trace, spanning from the \textit{initial configuration event}, to the \textit{end of the trace}. In the example of Figure \ref{fig:hint_trace}, it is marked by an orange bounding box. In general, its structure is the following:

\begin{verbatim}
    Configuration Pattern event     \t_1
    <REWRITE REGION>  -- repeated n times
    Configuration Pattern event     \t_n
\end{verbatim}

The rule corresponding to this part of the hint trace is:
\[
\dfrac{t_1 \rightarrow{} \Diamond t_2 \quad ... \quad t_{n-1} \rightarrow \Diamond t_n}{t_1 \rightarrow{} \Diamond t_n}
\tag{ALL}\label{rule:all}
\]

It is proved by repeated application of Rule \eqref{eq:TrRelTrans} to the premises. Note that each of the premises, which have the shape $t_i \rightarrow{} \Diamond t_{i+1}$, are going in turn to be the \textit{conclusions} of the rules corresponding to the $n$ rewrite sub-regions, as described below.

Thus, assuming that all rewrite regions are also processed, we would have at our disposal proofs of $t_1 \rightarrow{} \Diamond t_2$ through $t_{n-1} \rightarrow \Diamond t_n$. Applying rule \eqref{rule:all} to them yields a proof of:
\[
\dfrac{}{t_1 \rightarrow{} \Diamond t_n}
\]
which is exactly the goal of proof generation, as per Section \ref{sec:proof_generation_main_idea}.
\subsubsection*{REWRITE region}
A single REWRITE region covers a single semantic rewrite rule. The conclusion it should prove, then, will be one of the form $t_i \rightarrow{} \Diamond t_{i+1}$. In Figure \ref{fig:hint_trace}, rewrite regions are marked with red bounding boxes. In a hints trace, these regions have the following structure:

\begin{verbatim}
     <SIDECONDITION REGION>
     Rule event
     <SIMPLIFICATION REGION>
\end{verbatim}

Assuming the inner Rule event points to rule $(\phi \land \ell) \rightarrow {}\bullet{} r$ and contains substitution $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$, the corresponding derived rule is:
\[
\dfrac
{
(\phi \land \ell) \rightarrow {}\bullet{} r \quad  \phi[\overline{u}/\overline{x}] \quad t_i = \ell[\overline{u}/\overline{x}] \quad t' = r[\overline{u}/\overline{x}] \quad t_{i+1} = t'
}
{t_i \rightarrow {}\Diamond t_{i+1}}
\tag{REWRITE}\label{rule:rewrite}
\]

This is proved by Rule \eqref{eq:RewRl} and \eqref{eq:TrRelStep}.

Each of the premises that this derived rule expects are guaranteed to be eventually be accounted for, in the following way:
\begin{itemize}
    \item The $(\phi \land \ell) \rightarrow {}\bullet{} r$ premise is proved when the proof generation reaches the inner Rule event. Its proof is trivial, as $(\phi \land \ell) \rightarrow {}\bullet{} r \in \Gamma^{\it Sem(L)}$.
    \item The $\phi[\overline{u}/\overline{x}]$ premise assumes the truth of the applied rule's sidecondition. It will be proved as the conclusion of the inner SIDECONDITION sub-region (see below).
    \item The $t_{i+1} = t'$ premise is the conclusion of the inner SIMPLIFICATION sub-region (see below). It is responsible for bringing the instantiated right-hand side of the rule to normal form (see Section \ref{sec:running-programs}).
    \item $t_i = \ell[\overline{u}/\overline{x}]$ and $ t' = r[\overline{u}/\overline{x}]$ are proofs of substitution. They are independent of the hints trace and may be handled by a specialized procedure.

Once all premises are discharged, we are left with a proof of:
\[
\dfrac{}{t_i \rightarrow{} \Diamond t_{i+1}}
\]
which states that configuration $t_{i+1}$ is reachable from configuration $t_i$, as expected.

\end{itemize}

\subsubsection*{SIDECONDITION region}
These are marked with blue bounding boxes in Figure \ref{fig:hint_trace}. Their grammar is as follows:

\begin{verbatim}
    Side Condition Entry event
    <SIMPLIFICATION REGION>
    Side Condition Exit event
\end{verbatim}

As can be seen, these regions are wrappers around simplification regions. This is not unexpected, as proving a sidecondition amounts to a special case of simplifying a pattern. That is, they are simplifications whose conclusion \textit{must} always have the shape $\phi = True$.

All work in these regions is thus delegated to the inner SIMPLIFICATION sub-region.

\subsubsection*{SIMPLIFICATION region}

The purpose of a simplification region is to successively apply simplification rewrite rules, until the resulting pattern reaches normal form. They are marked with green bounding boxes in Figure \ref{fig:hint_trace}. In a hints trace, they appear as a \textbf{batch} of:

\begin{verbatim}
    Function event <location>
    <EQUALITY REGION> | Pattern Matching Failure event
    Function Exit event
\end{verbatim}

or:
\begin{verbatim}
    Hook event <location> <result>
\end{verbatim}

The semantics of simplification batches is slightly more complex and is treated separately below.\todo[author=AO, inline]{One thing we recently learned is that it's impossible to determine the claims proved in a simplification batch \textit{without actually proving them}. Because we don't have a-priori knowledge of what patterns will be found at each location. We therefore don't have the luxury of knowing what the premises should be just by looking at the hints, and our dynamic-programming-like approach kind of breaks here.

Should we simply specify the old algorithm? That might end up being a large-ish section of its own -- though having the specification written down will certainly help \textit{us} in the future. How should we deal with this?}

\subsubsection*{EQUALITY REGION}
This is an application of a single simplification rewrite rule (not a batch of them). There is, however, added complexity due to the fact rule may have a sidecondition. They are highlighted in teal color in Figure \ref{fig:hint_trace}. In general, their grammar is:

\begin{verbatim}
    <SIDECONDITION REGION>
          Rule event
\end{verbatim}

Assuming the inner Rule event points to rule $\phi \rightarrow (\ell = r)$ and contains substitution $\theta = \{x_1\mapsto u_1,\ldots,x_k\mapsto u_k\}$, the corresponding derived rule is:
\[
\dfrac
{
\phi \rightarrow (\ell = r) \quad  \phi[\overline{u}/\overline{x}] \quad t = \ell[\overline{u}/\overline{x}] \quad t' = r[\overline{u}/\overline{x}]
}
{t = t'}
\tag{EQUALITY}\label{rule:equality}
\]
Which is proved using rule \eqref{eq:SimplRl}.

The considerations about discharging the premises are analogous to the ones made with respect to REWRITE regions.
\fi

\subsection{Proof Checker} \label{sec:proof_checker}

The MPG process will generate an internal representation of a mathematical proof of a given program before being serialized to a proof format that is machine verifiable. Even though the design of how the internal representation of a mathematical proof is still in progress, there are a few key properties that hold:

\begin{enumerate}
    \item \textbf{Generic and easy to serialize:} The internal representation of any mathematical proof should be generic in the sense that it can be easily serialized to any proof format that we wish to serialize to, e.g., Metamath, Coq, Lean, etc.
    \item \textbf{Modular and reusable:} The internal representation of components of a proof such as patterns, axioms, (sub-)proofs and theories, should be modular so that they can be easily reused (without reproving) while building the overall proof for a given program.
\end{enumerate}

With these key properties, the internal representation of any mathematical proof of a given program can be easily serialized to a target proof format which allows fast and efficient verification. For the remaining of this subsection, we will discuss the two main proof checker formats that we aim to serialize to: a) Metamath and b) proposed block model. We will give a brief description of how matching logic, Kore notations and the proof generated can be represented in these two proof checker languages.

\subsubsection{Metamath}
\label{sec:ml_mm}

Metamath \cite{metamath} is a simple language for representing formal proofs. Originally developed by Norman Megill in 1990, it was designed to be a language capable of representing proofs in user-specified formal systems. The largest repository of Metamath proofs is \texttt{set.mm}, which contains theorems in ZFC set theory and has grown to over 23000 theorems.

A key feature of Metamath is its simple design. Metamath uses only 15 keywords, each denoted by an initial \texttt{\$} character, and does not allow for extensibility of this basic syntax. This makes it straightforward to implement checkers for Metamath: Over 22 implementations exist in a variety of languages, most running to only a few hundred lines of code \footnote{\url{https://us.metamath.org/other.html\#verifiers}}. This simplicity makes it well-suited to the purpose of use in a ZK proof system, as it becomes possible to adapt and compile existing implementations to zkVMs, or replicate the semantics of the language in an arithmetic constraint system.

To demonstrate the simplicity of Metamath, the rest of this subsection provides a brief illustration of how matching logic can be formalized in Metamath. We will see how we can formalize the syntax, formulas/patterns, axioms and proofs that were defined in Section \ref{sec:matching_logic} in Metamath.

At high level, any Metamath source file will contain a list of \textit{statements} and the main ones are:

\begin{itemize}
    \item \textit{Constant statements} (\lstinline{$c}) that declare Metamath constants.
    \item \textit{Variable statements} (\lstinline{$v}) that declare Metamath variables, and \textit{Floating statements} (\lstinline{$f}) that declare their intended ranges.
    \item \textit{Axiomatic statements} (\lstinline{$a}) that declare Metamath axioms, which can be associated with some \textit{essential statements} (\lstinline{$e}) that declare the premises.
    \item \textit{Provable statements} (\lstinline{$p}) that state Metamath theorems and their proofs.
\end{itemize}

Figure \ref{fig:mm_ml_syntax} shows how the 8 matching logic syntax constructs (\ref{eq:mlsyntax1}) can be formalized in Metamath. 

\begin{figure}[!h]
\begin{subfigure}[t]{0.5\textwidth}
\begin{lstlisting}[language=Metamath]
$c #Pattern         $.
$c #ElementVariable $.
$c #SetVariable     $.
$c #Variable        $.
$c #Symbol          $.

$v ph0 ph1 $.
$v x y     $.
$v X Y     $.
$v xX yY   $.
$v sg0     $.

ph0-is-pattern $f #Pattern ph0 $.
ph1-is-pattern $f #Pattern ph1 $.

x-is-element-var 
   $f #ElementVariable x $.
y-is-element-var 
   $f #ElementVariable y $.

X-is-element-var $f #SetVariable X $.
Y-is-element-var $f #SetVariable Y $.

xX-is-var $f #Variable xX $.
yY-is-var $f #Variable yY $.

sg0-is-symbol $f #Symbol sg0 $.
\end{lstlisting}
\end{subfigure}
\begin{subfigure}[t]{0.7\textwidth}
\begin{lstlisting}[language=Metamath]
$c #Positive $.
$c \bot      $.
$c \imp      $.
$c \app      $.
$c \exists   $.
$c \mu       $.
$c ( )       $.

$( Matching Logic Syntax $)

element-var-is-var $a #Variable x $.
set-var-is-var     $a #Variable X $.
var-is-pattern     $a #Pattern xX $.
symbol-is-pattern  $a #Pattern sg0 $.
app-is-pattern 
  $a #Pattern ( \app ph0 ph1 ) $.
bot-is-pattern $a #Pattern \bot $.
imp-is-pattern 
  $a #Pattern ( \imp ph0 ph1 ) $.
exists-is-pattern 
  $a #Pattern ( \exists x ph0 ) $.
${ 
    mu-is-pattern.0 
      $e #Positive X ph0 $.
    mu-is-pattern   
      $a #Pattern ( \mu X ph0 ) $.
$}
\end{lstlisting}
\end{subfigure}
\caption{Formalization of matching logic syntax (\ref{eq:mlsyntax1}) in Metamath}
\label{fig:mm_ml_syntax}
\end{figure}

Notations derived from the 8 syntax constructs as seen in Section \ref{sec:matching_logic} can also be formalized in Metamath. A new constant statement \lstinline{#Notation} needs to be declared first before using it to capture the \textit{congruence relation of sugaring/desugaring}, i.e., notation. Figure \ref{fig:mm_not_as_notation} shows how the notation $\neg \varphi \equiv \varphi \imp \bot$ can be formalized in Metamath.

\begin{figure}[!h]
\begin{lstlisting}[language=Metamath]
$c #Notation$.

$c \not $.

not-is-pattern $a #Pattern ( \not ph0 ) $.
not-is-sugar $a #Notation ( \not ph0 ) ( \imp ph0 \bot ) $.
\end{lstlisting}
\caption{Formalization of $\neg$ as notation in Metamath}
\label{fig:mm_not_as_notation}
\end{figure}

Lastly, axiom/proof rules can also be formalized in Metamath so to provide us with a proof system to prove and verify theorems with. Figure \ref{fig:mm_fol} illustrates how proof rules can be added in order to prove theorem, $\varphi_1 \imp \varphi_1$ in Metamath.

\begin{figure}[!h]
\begin{lstlisting}[language=Metamath]
$c |- $. $( This declares the entailment relation. $)

proof-rule-prop-1 $a |- ( \imp ph0 ( \imp ph1 ph0 ) ) $.
proof-rule-prop-2 $a |- ( \imp ( \imp ph0 ( \imp ph1 ph2 ) ) ( \imp ( \imp ph0 ph1 ) ( \imp ph0 ph2 ) ) ) $.
${
    proof-rule-mp.0 $e |- ( \imp ph0 ph1 ) $.
    proof-rule-mp.1 $e |- ph0 $.
    proof-rule-mp   $a |- ph1 $.
$}

imp-refl $p |- ( \imp ph1 ph1 )
$=
  ($ Proof of the ph1 => ph1 goes here. $)
$.
\end{lstlisting}
\caption{Formalization of part of FOL and the proof of $\varphi\sb 1 \imp \varphi\sb 1$ in Metamath}
\label{fig:mm_fol}
\end{figure}

More on how matching logic can be formalized in Metamath can be found in \cite{LCT23}. Recall that language definitions written in \K are compiled into the Kore format instead of directly to matching logic primitives. Thus, it is also necessary to have these Kore notations to be formalized in Metamath in order for theorems, which are expressed in Kore format, to be proven. Full formalization of matching logic and Kore notations can be found in this directory of the GitHub repository\footnote{\url{https://github.com/runtimeverification/proof-generation/tree/main/theory}}. We have also experimented with verifying the mathematical proofs generated from the programs through zkVMs, which will be covered in Section~\ref{sec:mm_experiment}.









\subsubsection{Proposed Block Model}

The Block Model is a proof format that we specifically designed for efficient ZK verification of mathematical proofs. The Block Model organizes proofs into a series of blocks, each of which requires a set of premises and produces a set of conclusions. We hard code the rules of inference for the proof system into the construction of these blocks, and the prover can then construct a proof by providing a series of blocks.

The structure of the blocks allows for a more efficient verification process, as the only connection between blocks is checking that all premises of a block were produced somewhere as a conclusion.
This can be checked with the same techniques zkVMs use to check that a memory read instruction produces a value matching an earlier write, simplified further because blocks are unordered.
The order independence also makes it easy to divide checking a large proof across many copies of a fixed size circuit.
A succinct ZK proof for a formal proof can be produced more efficiently than separately producing a
SNARK for each instance of the circuit by taking advantage of this ``data parallel'' structure.
As this Block Model is specifically designed to fit our Proof-of-Proof pipeline, we will postpone the discussion to Section \ref{sec:block_model}, which is dedicated to provide more details on the Block Model.

\section{Implementing Math Proof Checker in zkVMs}
\label{sec:zkVMs}


The math proof generator and the proof checker described in \Cref{sec:mpg} effectively eliminate \K and its gory implementation details from the trust base.  Indeed, the role of \K is reduced to searching for and generating a mathematical proof for the computational claim that was made.  That is, the claim is a theorem and its actual computation, or execution produced by \K, is turned by the MPG module into its mathematical proof.  The proof checker then verifies the produced math proof and if that is correct, then the claim is correct. \K's correctness is therefore irrelevant, as far as it produces a math proof that checks.

In other words, the proof checker is the centerpiece that supports and enables the universal correctness of computing: it can verify any computation done with any program in any PL/VM, directly against the definition of the PL/VM, enforcing correctness-by-construction; additionally, it does it at no additional runtime overhead, as it verifies the proof as it is being generated.  Because of the above we can argue that, from some perspective, the math proof checker, which is itself a program which totals only a few hundred lines of code, is one of if not the most important program ever written.  But it is a program nevertheless, so it can be compiled and executed on off-the-shelf zkVMs. This is the fastest and cheapest way to obtain a PoC implementation of our Proof of Proof paradigm.

\subsection{Background}

Zero-knowledge virtual machines (zkVMs) are a type of software that supports producing zero-knowledge proofs of execution for some target language, for example, RISC-V or the Ethereum VM instruction set. Since the proofs are ideally much faster to check than it would be to execute the original program, this enables trustless computing, where one untrusted party (the prover) can perform a computation on behalf of another party (the verifier), and then quickly convince the verifier that the result produced was the result of a correct program execution, without tampering or errors. These computations can be fairly arbitrary. Any program that can be defined in the target language can be proven, within resource constraints. zkVMs can also support additional privacy-preserving features limited only by the expressiveness of the target language: the prover may provide their own inputs to the program, which are not revealed to the verifier. In this way, the prover can prove to the verifier that they know a piece of data satisfying some criteria without revealing the data. 

Zero-knowledge proofs in general, and zkVMs in particular, have been seen as a way to address scalability problems with blockchains. In traditional models, smart contract code must be independently re-executed by many parties. If ZK is used instead, only one party needs to execute the program, while simultaneously producing the small zero-knowledge proof, and then instead of re-executing the whole program, other parties can simply run a short verification procedure on the proof.

\subsection{Experiments and Benchmarks} \label{sec:mm_experiment}

Metamath (MM) is a minimalistic format for specifying mathematical proofs. In Metamath, proofs are defined by specifying variable and constant symbols, axioms with or without hypotheses over strings of those symbols, and then finally giving the proof itself, which is a list of labels of previously declared statements, which can be applied mechanically to gradually build up a string of symbols culminating in the proved theorem. More information on Metamath can be found in Subsection \ref{sec:ml_mm}. Metamath was chosen as the format we would check proofs in for this experiment because it is a well-established, widely-known format, it is expressive enough to be used to represent our proofs of execution, and provide flexibility in how we do so, and because it is simple to understand and to write checker programs for.

The checking procedure, which we implemented in several languages to be compatible across all zkVMs we tried, is to first load all of the symbols and axioms into memory, and then read each given proof step in order. At each step, a new string of symbols is added to a stack. Depending on which rule is invoked, some stack entries are also consumed. For axioms with hypotheses, variable substitutions must be done on stack entries to ensure all the hypotheses are satisfied. The appropriate substitution is then made to the rule conclusion which is then placed on the stack. At the very end, it is verified that the stack contains exactly one entry, and that this matches the theorem that was originally claimed. 

We implemented our Metamath proof checker in seven different zkVM's: Cairo, Jolt, Lurk, Nexus, Risc Zero, SP1 and zkWASM. Each implementation consists of a guest program which runs on the specific virtual machine and a host program which is our interface to actually running the guest, providing input for it and processing its output. 

Five  out of the seven tested zkVMs (Jolt, Nexus, Risc Zero, SP1 and zkWASM) provide a Rust compiler. Therefore, for them we have been able to develop and use a shared library for checking Metamath proofs, and thus the comparison among these five zkVMs should be considered more precise, as they share most of the code. Both Cairo and Lurk use domain specific languages (Cairo, respectively, LISP). While in Cairo and Lurk we implemented the same program (a Metamath checker), they were implemented independently of the rust code base and independent of each-other, so the comparison between them and the the Rust-based zkVM's should be taken with a grain of salt. 

Only Risc Zero, zkWASM, SP1 and Cairo provide GPU support among the zkVMs that we have considered. Still, we were only able to run Risc Zero and zkWASM with GPU support due to internal setup issues for SP1 and evolving code base for Cairo.

For each of the zkVMs we've been using the default type of certificate offered by that particular zkVM. For example, the default means composite certificates for Risc Zero and SP1 and succinct certificates for zkWASM. We've experimented with generating succinct certificates for Risc Zero and compressed certificates for SP1; the elapsed times to generate the shorter certificates seemed to be ~1.6 times larger than that for composite certificates.

The zkVM space is evolving rapidly, with frequent releases of new zkVM versions and the provers they rely on. For our benchmarking, we used the following versions: 
\begin{itemize}
\item \textbf{Cairo} (the Lambdaworks prover): Main branch, commit \href{https://github.com/lambdaclass/lambdaworks/commit/a591186e6c4dd53301b03b4ddd69369abe99f960}{a591186}, authored 2024-09-25 (the current version, while faster, does not yet support Cairo).
\item \textbf{Jolt}: Main branch, commit \href{https://github.com/a16z/jolt/commit/3b142426d9648299d9c6912e7e1b4698cf91491b}{3b14242}, authored 2024-11-04.
\item \textbf{Lurk}: Main branch, commit \href{https://github.com/lurk-lab/lurk/commit/57c48b987a94ba1f9752408a0990882c9f4f506b}{57c48b9}, authored 2024-11-05.
\item \textbf{Nexus}: Version \href{https://github.com/nexus-xyz/nexus-zkVM/releases/tag/v0.2.3}{0.2.3}, authored 2024-08-21
\item \textbf{Risc Zero CPU}: Version \href{https://github.com/risc0/risc0/releases/tag/v1.0.5}{1.0.5}, authored 2024-06-30.
\item \textbf{Risc Zero GPU}: Version \href{https://github.com/risc0/risc0/releases/tag/v1.0.5}{1.2.2}, authored 2025-01-27.
\item \textbf{SP1 CPU}: Dev branch, commit \href{https://github.com/succinctlabs/sp1/commit/2c7868364cb832531e8cafd258aa06fbab079459}{2c78683}, authored 2024-11-05.
\item \textbf{SP1 GPU}: Version \href{https://github.com/succinctlabs/sp1/releases/tag/v4.0.1}{4.0.1}, authored 2025-01-17.
\item \textbf{zkWASM}: Main branch, commit \href{https://github.com/DelphinusLab/zkWasm/commit/f5acf8c58c32ac8c6426298be69958a6bea2b89a}{f5acf8c}, authored 2024-10-19.
\end{itemize}
\subsubsection{How we Generated the Files}
Our full benchmark suite consists of $1225$ Metamath files split into two classes:
\begin{itemize}
\item A class generated from standard Metamath databases \href{https://github.com/metamath/set.mm/blob/develop/demo0.mm}{[1]} and \href{https://github.com/metamath/set.mm/blob/develop/hol.mm}{[2]} by dividing them into small lemmas. These tests can be found under\\
\centerline{checker/mm/common/metamath-files/benchmark_mm/small}\\ 
in the Docker image that can be pulled from \href{https://github.com/pi-squared-inc/zk-benchmark/pkgs/container/pi2-zk-mm-checkers}{here}; The instructions to run the Docker image can be found \href{https://github.com/pi-squared-inc/zk-benchmark/pkgs/container/pi2-zk-mm-checkers#instructions}{here}.
\item A class of Pi Squared proofs of execution of various lengths, which prove the correctness of an ERC20-like program written in the \href{https://en.wikipedia.org/wiki/IMP_(programming_language)}{IMP} programming language. These tests can be found under\\
\centerline{checker/mm/common/metamath-files/benchmark_mm/imp.}

If you want to find more on how we generate mathematical proofs of program executions, check out our \href{https://github.com/Pi-Squared-Inc/devcon-2024/tree/main/demos#generating-metamath-proofs-for-arbitrary-programs}{proof generation demos} and \href{https://docs.pi2.network/}{our documentation}.
\end{itemize}
\subsubsection{Optimizations}

In the course of our examination, we made a few optimizations to the original Rust implementation of Metamath we started with for the matching logic use case. These included:

\begin{itemize}
    \item Deduplication of strings stored in memory by managing using references to a single copy of each string.
    \item We reorganized the framestack to be a vector of frames, rather than a BTreeMap. This allowed us to avoid the overhead of maintaining the BTreeMap, and allowed us to use a more efficient data structure for the framestack.
    \item Circumvented derserialization of the proof by directly reading the proof file preparsed into a proof object into the zkVM.
\end{itemize}

Ultimately, the most significant single contribution to the runtime of the checker was the substitution of strings used in Metamath's core consistency checking step. Activity in this method ultimately amounted to around 15\

\subsection{Results}
These checkers implemented on each of the zkVMs presented here were all tested on the same machine, with a AMD EPYC 9354 32-Core CPU, 4x NVIDIA GeForce RTX 4090 24GB GPU's, and 248GB RAM.



\begin{figure}
\includegraphics[width=\textwidth]{figures/zkvm.pdf}
\includegraphics[width=\textwidth]{figures/zkvm_gpu.pdf}
\caption{zkVM Comparison Table}
\label{zkVM comparison}
\end{figure}

In order to save time, for each zkVM we run only some of the 1225 files, which makes the lines from Figure \ref{zkVM comparison} to be rather approximations of the points corresponding to the measured files. This is the reason for which, for some particular files, one particular zkVM could behave better than other one, even if the figure doesn't show this. For a more precise comparison, we encourage you to check our \href{https://github.com/Pi-Squared-Inc/zk-benchmark}{GitHub repository}.

\subsubsection{How Different zkVMs Behave}

The eight Metamath files referenced in Tables 1 through 7 were chosen to be representative of a wide range of input sizes. Times are measured in seconds, and input size is measured in number of Metamath tokens. A 900 second time limit was imposed, and where the result is "TO / OOM", either the time limit was exceeded or the checker used up all the system's memory. The Nexus checker took 512 seconds on hol\_idi.mm, so a table was not included here.

\begin{table}[htp]
    \centering
    \caption{Cairo}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 0.913 & 0.029 \\
         \hline
         hol\_wov.mm & 147 & 5.975 & 0.229 \\
         \hline
         hol\_ax13.mm & 508 & 25.623 & 0.993 \\
         \hline
         hol\_cbvf.mm & 1786 & 110.230 & 4.321 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 228.487 & 9.102 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & TO/OOM & TO/OOM \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & TO/OOM & TO / OOM \\
         \hline
         9.erc20transfer\_success.mm & 258135 & TO/OOM & TO/OOM \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{Jolt}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 2.04 & 0.08246\\
         \hline
         hol\_wov.mm & 147 & 2.89 &  0.06515\\
         \hline
         hol\_ax13.mm & 508 & 5.25 &  0.08273\\
         \hline
         hol\_cbvf.mm & 1786 & 12.09 &  0.08691\\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 21.15 & 0.0848\\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 65.51 &  0.09053\\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & TO/OOM & TO/OOM \\
         \hline
         9.erc20transfer\_success.mm & 258135 & TO/OOM & TO/OOM \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{Lurk}
    \begin{tabular}{|l|r|r|}
         \hline
         Benchmark & Input Size & Proving time \\
         \hline
         hol\_idi.mm & 39 & 0.924 \\
         \hline
         hol\_wov.mm & 147 & 5.588 \\
         \hline
         hol\_ax13.mm & 508 & 18.167 \\
         \hline
         hol\_cbvf.mm & 1786 & 195.757 \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{RISC0 (GPU), Succinct proof mode}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 1.47 & 0.01526 \\
         \hline
         hol\_wov.mm & 147 & 1.44 & 0.01527 \\
         \hline
         hol\_ax13.mm & 508 & 1.44 & 0.01525 \\
         \hline
         hol\_cbvf.mm & 1786 & 1.61 & 0.01528 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 1.58 & 0.01521 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 1.96 & 0.01526 \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & 10.93 & 0.01529 \\
         \hline
         9.erc20transfer\_success.mm & 258135 & 40.78 & 0.01525 \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{RISC Zero (CPU), Composite proof mode}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 3.140 & 0.016 \\
         \hline
         hol\_wov.mm & 147 & 5.770 & 0.017 \\
         \hline
         hol\_ax13.mm & 508 & 11.220 & 0.018 \\
         \hline
         hol\_cbvf.mm & 1786 & 33.900 & 0.035 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 33.480 & 0.035 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 66.280 & 0.053 \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & 276.440 & 0.225 \\
         \hline
         9.erc20transfer\_success.mm & 258135 & TO/OOM & TO/OOM \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{SP1 (CPU), Core proof mode}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 7.260 & 0.203 \\
         \hline
         hol\_wov.mm & 147 & 12.220 & 0.199 \\
         \hline
         hol\_ax13.mm & 508 & 17.450 & 0.199 \\
         \hline
         hol\_cbvf.mm & 1786 & 34.860 & 0.208 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 4334.790 & 0.207 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 43.340 & 0.338 \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & 133.150 & 0.731 \\
         \hline
         9.erc20transfer\_success.mm & 258135 & 456.790 & 2.490 \\
         \hline
    \end{tabular}
\end{table}

\begin{table}[htp]
    \centering
    \caption{SP1 (GPU), Compressed proof mode}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 0.6914 & 0.09137 \\
         \hline
         hol\_wov.mm & 147 & 0.7096 & 0.09151 \\
         \hline
         hol\_ax13.mm & 508 & 0.6942 & 0.09091 \\
         \hline
         hol\_cbvf.mm & 1786 & 0.7601 & 0.09168 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 0.7447 & 0.09047 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 1.19 & 0.09091 \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & 3.47 & 0.09065 \\
         \hline
         9.erc20transfer\_success.mm & 258135 & 10.15 & 0.0907 \\
         \hline
    \end{tabular}
\end{table}


\begin{table}[htp]
    \centering
    \caption{zkWASM (GPU)}
    \begin{tabular}{|l|r|r|r|}
         \hline
         Benchmark & \hspace{-2ex}\begin{tabular}{c}Input\\ Size\end{tabular} & \hspace{-3ex}\begin{tabular}{c}Proving\\ time\end{tabular} & \hspace{-2ex}\begin{tabular}{c}Verification\\ time\end{tabular} \\
         \hline
         hol\_idi.mm & 39 & 33.080 & 4.059 \\
         \hline
         hol\_wov.mm & 147 & 33.020 & 4.045 \\
         \hline
         hol\_ax13.mm & 508 & 34.090 & 4.063 \\
         \hline
         hol\_cbvf.mm & 1786 & 76.550 & 4.092 \\
         \hline
         45.erc20transfer\_success\_tm\_0\_6.mm & 6249 & 79.030 & 5.063 \\
         \hline
         25.erc20transfer\_success\_tm\_0\_9.mm & 21332 & 120.720 & 5.072 \\
         \hline
         3.erc20transfer\_success\_tm\_0.mm & 73862 & 351.660 & 8.034 \\
         \hline
         9.erc20transfer\_success.mm & 258135 & TO/OOM & TO/OOM \\
         \hline
    \end{tabular}
\end{table}

\subsection{Lessons Learned}



The Rust implementation of the checker got the best results, specifically on the SP1 and RISCZero VMs, both in terms of speed and maximum memory usage. However, even in these best cases, producing a ZK proof of a math proof of a simple ERC20-style transfer would take many minutes. This execution proof is generated using the semantics of a toy imperative language, but the proof sizes with a real-life language like Solidity could be significantly larger.

Checking large proofs (proofs of program execution are necessarily going to large) seemed to pose a problem for several of the zkVMs. In these cases the memory required to check a proof typically grew monotonically in the size of that proof. Some zkVMs, like RISCZero and SP1 use techniques to avoid excessive memory use which involve splitting up the execution transcript into chunks (These are referred to as shards in SP1 and segments in RISCZero) and recursively combining these.  

We believe that a ZK circuit built to check math proofs in a specific format has the potential to be significantly faster, up to $1400 \times$ times. This is in part because there is no need to check memory consistency, and additionally because it would avoid the overhead of an intermediate step to make the proof logic compatible with Metamath and a VM architecture; see Subsection \ref{estimating-performance-folding} for more details.

We would like to thank all the mentioned zkVM providers for having provided us feedback on these benchmarks and suggestions to improve our existing proof checking algorithm. We know that the field is continuously evolving and they are getting better and better with any release. We are happy to receive any further news on the improvements that they are going to make and to update our benchmarks accordingly.


\section{Block Computation Model} \label{sec:block_model}
In this section we propose a customized approach for checking proofs.
The design was inspired by considering how techniques used to implement instructions in zkVMs
could be applied more directly to proof checking, avoiding
overhead inherent to using any zkVM for proof checking.
When checking a proof, the only condition which needs to consider more than one proof step is checking that the hypotheses of one step are all conclusions of other steps.
This can be implemented directly with a \emph{lookup argument}(eg \cite{logup,Lasso}).
Each hypothesis becomes a single entry in the \emph{lookups} list, each conclusion a single entry in the \emph{table} list.
In comparison a zkVM implements memory operations using a \emph{memory checking argument}(\cite{BCGT13-ram}).
Each read or write lists the current and previous access times and values for the memory address as two entries in a \emph{permutation argument}.
A proof checking program will need several memory accesses to handle each hypothesis of a proof step.

The second simplification is to have no execution model.
Expressing the task to be proved in zkVM as ``run this code on this input'' allows a short description of the computation, but the ZK proving process requires materializing an entire transcript of the computation before the heavy cryptographic work.
So the input to computation that dominates prover time is still large, and a more complicated constraint system is needed to enforce that the transcript sticks to the control flow of the execution model.
Instead we allow locally well-formed proof steps to be checked in any order, and any desired ``execution model'' such as Prolog-style resolution is handled before ZK by choosing what blocks to generate.

\subsection{ZK Computational Model Assumptions}\label{zk-computational-model-assumptions}

\todo[inline]{\emph{Most of this section and its subsections are probably unnecessary}}

There is a common intermediate-level computational model that is
supported by the cryptography behind many zkSNARK protocols, not just
those of zkVMs, but also systems aimed at scalably supporting arbitrary
circuits. This section describes the functionality that seem useful for
proof checking.

In this lower-level model the basic unit of data is an element of a
large finite field, probably 256 bits or so. The prover's witness is a
fixed-size table of field elements. The system designer defines the
width and well-formedness constraints over a table, and where the public
data should be embedded in the table. A prover can then generate
certificates establishing that they knew a well-formed table for certain
public data.

The constraints consist of an arbitrary local transition relation that
is checked between each pair of neighboring rows, global constraints
relating the lists of values in different columns, and boundary
conditions setting exact values for some cells at absolute locations,
especially the first and last rows.

The local transition relation is given as a set of low degree
polynomials over the elements of the two rows. To be well-formed all
these constraint polynomials must evaluate to zero. The highest degree
appearing in any of the constraints is a significant factor in protocol
costs, but so is adding more columns to have room for intermediate
values to lower the degree of constraints. The local constraints can
also mention global values, which can be Fiat-Shamir random values
chosen by hashing a subset of earlier columns.

The global constraints are limited to specific constructions backed by
security arguments rather than a general language, but known
constructions are sufficient for our needs. Two important constraints
are permutation constraints which enforce that one column is a
permutation of another, and lookup or subset constraints which check
that the set of values in one column is a subset of the set of values in
another. This can also be extended to operate over tuples of values
rather than just individual column entries, or to operate on the
multisets of all values in groups of columns instead of just between two
individual columns.

For recursive zkSNARK schemes we might need some kind of cryptographic
commitments instead, but within a single VM-ish witness these
constraints actually reduce to local constraints using Fiat-Shamir
values (to accumulate the evaluation of certain polynomials over the
column entries at ``random'' points). In particular, the extension to
tuples simply computes a polynomial fingerprint across the tuple using a
Fiat-Shamir constant independent of those used in the permutation/subset
constraint, and applies the permutation/subset construction over these
fingerprint values.

\subsubsection{AIR Design Patterns}\label{air-design-patterns}

\todo[author=DL,inline]{"AIR" (Algebraic Intermediate Representation) occurs first time here. I think we should have an introductory paragraph here.}

In a zkVM constraints are designed so that a portion of the witness must
be a valid execution trace of the machine. Some columns will represent
the machine registers, some will represent inputs or outputs such as
memory access whose correctness is not apparent locally. These non-local
relations are supported by using permutation or lookup constraints to
link to auxiliary columns with the data sorted in an order where
correctness can be checked locally - and the desired ordering can also
be enforced locally. For example, if a list of memory accesses is sorted
first by address and then by access time, checking that reads return the
correct value becomes a local constraint, and checking that the list is
sorted in this way is also local.

We are not strictly sticking to a deterministic machine design, but the
point of view can be useful.

Two subcomputations can be combined side-by-side by combining the local
constraints implementing the transitions relations independently to the
two blocks of columns.

Different transition relations can be combined sequentially by adding
``control columns'' encoding the operating mode, modifying the
constraints for the transitions relations to only be applied in the
appropriate mode, and adding any desired constraints about how the
control columns can change.

For a modest number of modes a straightforward way to do this uses
``selector columns'' that are always constrained to be 0 or 1 by a
constraint $s(1-s)=0$. Have a selector column $s\_i$ for
each mode, and multiply the constraints for that operating mode by a
factor of $s\_i$ so it only applies when that selector is set to
1, and then new constraints among the selector columns and control
column to ensure the selectors are set appropriately for the new
control.

\subsubsection{Other AIR Features}\label{other-common-features}

There are some modest generalizations of the above features that seem to
be pretty broadly supported, but not so obviously useful for proof
checking.

It can be possible to suppress constraints, so they don't apply on a
specific row, or periodically on every $n$th-row. The fact that the
next-row constraint doesn't apply in a ``wrapping'' way between the last
row and the first is generally an instance of this mechanism.

Especially in systems that use interpolating univariate polynomials over
powers of $n$th-roots, it would be possible to have local constraints
not just between a row and the next row, but also between the row and
another row at a fixed offset.
As a special case, the contents of a column may be forced to be periodic.

\subsubsection{Verification Costs}\label{verification-costs}

For STARK, the costs depend on the number of columns k, the row length
N, and the constraint degree d.

For each column the prover needs to compute a polynomial whose
evaluations on one domain of size N interpolate the values of that
column, and then evaluate that polynomial on a disjoint domain of size
O(dN). Using the NTT each column takes O(dN log(dN)) work. A Merkle tree
is formed with leaves being rows of these evaluations.

Some auxiliary functions need to be computed for each row. The per-row
work is mostly evaluating (a linear combination of) the constraint
polynomials over the tabulated column polynomial evaluations. This is
linear as a function of sN, but the scaling factor depends on the
complexity of the constraints.

The domain size must be a multiple of dN because a security is based on
using the (DEEP)-FRI protocol to check that the auxiliary functions are
actually polynomials of bounded degree, the size of the evaluation
domain must a multiple of the degree bound for security, and one factor
in the bound is related to the degree of the composition of the degree-d
constraints with the degree-N column polynomials.

In the FRI protocol the Merkle trees are opened at logarithmic number of
rows, this is the main component of certificate size. log(dN)*(log(dN)
hashes + k field elements).

Overall it seems we should keep the constraint degree quite modest for
the benefit of the prover, only going to (s+1) if we can save a factor
of at least (s+1)/s in total table area. Trading off rows vs.~columns if
we keep the same total area is less clear, with different impacts on
prover and verifier costs. Probably prefer narrower transcripts at equal
area, however the STARK paper did claim that a major advantage of the
design was allowing for the use of k separate degree N interpolating
polynomials and a single (by linear combination) degree O(N) test rather
than degree kN interpolations and a degree O(kN) test, so don't go too
far.

What are the asymptotics for Groth16, or PlonK?

Spartan or other things that sound more like a direct R1CS argument?

\subsubsection{Proof Structure}\label{proof-structure}

This section is initial musings on how to organize a proof onto a
zkVM-ish transcript. It's largely obsoleted by other documents.
\todo[author=DL,inline]{We have to decide whether we keep (and remove the above statement) or we remove it.}

The overall structure of the witness will have blocks checking each
proof rule application, and connect the hypotheses and conclusions these
blocks with a subset constraint. Each block will use local constraints
to check that the proof rule application is well-formed, and put any
necessary hypotheses in the hypothesis column and the conclusion(s) of
the rule in the conclusion column. Besides the main judgment that a
pattern holds, claims communicated through the lookup mechanism will
include other side conditions like checking freshness, and also
auxiliary computations like substitution. These include things that
would be simply executed in an ordinary proof checking program, but need
transcript space in a ZK witness. As they need witness space either way,
we won't hesitate to represent them also as auxiliary judgments defined
by clauses of their own, but it might also be possible to have a more
direct zkVM encoding of executions for some.

To be able to communicate claims through a lookup constraint, we must
assign single-field-element names to terms and any other values that
appear as parameters of claims, so that the claims are all represented
by fixed-size tuples. Our proof system has no rules with variable
numbers of hypotheses, so the description of a proof rule is also fixed
size if all the parameters are assigned succinct names. The size of the
transcript block for checking a rule instance is also fixed size, so
some columns of the witness can be a direct transcription of the proof.

\paragraph{Uniqueness constraints}\label{uniqueness-constraints}

For implementing term definitions we want to enforce that some table
entries are emitted only once, ones which mean something like ``I'm
defining a term named by field element X''.

In the literature there are ``bounded lookup'' arguments which control
how many times a value can occur in the lookup column f, with special
interest in multiplicity one for RAM applications. That sounds like it
might be what we need, but unfortunately do not work. They do not
enforce the absence of repeated entries in the table, allowing
more lookups when the entry is repeated (or have uniqueness of table
entries as a precondition).

So, it seems we must just do the obvious thing of having a dedicated
permutation argument and auxiliary columns dedicated to uniquenes
enforcement, rather than trying to build it into the main hypothesis
lookup argument.

\subsubsection{Selectable Sets of Constraints}\label{selectable-sets-of-constraints}

Sometimes we would like to have several sets of constraints and be able
to choose at most one on a row. This shows up in the ``register''
routing in the Block zkVM design, and potentially could even apply to
picking among possible block types. But it seems a bit hard to support
many sets without also using many selector columns.

A common idea is binary selector columns. We can force the value to be
zero or one with the constraint s(1-s), and then change a constraint
P(X) to only be enabled when s is set or unset by changing to sP(X) or
(1-s)P(X), increasing the degree by one. This only gives two options.

If we want a choice among many different sets of constraints, a single
selector doesn't work so nicely. Forcing the selector value to be in a
set of size N takes a degree N constraint, like \texttt{(x-0)(x-1)(x-2)}
to allow x to be only 0,1,2. To enable a constraint on only 1 out of N
possible values we need a leading term that is zero on the other values,
which will have degree N-1 as in \texttt{(x-1)(x-2)P(X)} to apply
constraint P(X) only when x is 0.

For lower degree at the cost of columns, if we have K binary selectors
there are 2\^{}K settings, and set can make a constraint conditional on
1 out of 2\^{}K settings at a cost of K degree by multiplying by a term
like s1(1-s2)s3.

Perhaps the idea of multiple and multi-valued selectors could be
combined, but even just two ternary selectors increases degree by four.
It seems unlikely the column savings could make up for the degree. Even
combining multiple binary selectors pushes the degree a fair bit, if we
are trying to keep the maximum to a modest 5 or 6, and some of the
constraints to be controlled have degree two or three.

Is there anything besides a ``one hot'' encoding that works if we are
strictly restricted to degree 2 for R1CS/Groth?
\subsection{Block Model}\label{block-model}
The block model gives a language for defining \emph{rules}, a format
for writing \emph{transcripts}, and a condition for a transcript to
be valid according to a set of rules, designed so that validity of
a transcript can be efficiently checked in ZK, but also so that
that the problem of checking a mathematical proof in a conventional
logic can be translated to checking a transcript against a set of
rules (which depend only on the logic).
The ``public data'' of a ZK instance is a prefix of a transcript,
which may also leave some values in those blocks unspecified.
The full transcript must extend this specification.
We will see that a goal of proving a specific formula can be
specified in this way, so that any valid transcript extending
the given prefix must include a proof of that goal.

To conveniently support the recursive structure of proof steps
in a conventional logic, and also recursively defined auxiliary functions
such as substitution which are also common in such logics,
the transcript is organized as a loosely coupled
collection of \emph{block instances}, which interact only by
emitting and demanding \emph{claims}, which can represent the
logical judgments that appear in hypotheses and conclusions of proof rules,
or claims that some application of an auxiliary function
returns a particular result.
Each of a proof rule, a clause of a recursive function definition, or
production of a syntax definition generally corresponds to a single
block rule.

To suit the lower ZK layers, claims are represented by tuples of field elements.
Each \emph{relation} (kind of claim) has a fixed arity, and takes
only field elements rather than structured data as arguments,
such as \texttt{is\_impl(T,TA,TB)} or
\texttt{proved(T,k)}.
By giving code numbers to the relations and padding with trailing
zeros, all kinds of claims are uniformly represented.
Structured data such as syntax trees or a set of
substitutions must be translated into this representation.
This is a standard technique when applying Datalog to program analysis.
Families of relations are set up to describe tree nodes and immediate-child
relationships, and data is represented by assigning each subterm a
name, which is just any arbitrary field element, and
emitting claims describing the relationships.
To support declaring such data we also have a notion of \emph{unique claims},
where a transcript is not allowed to have multiple blocks emitting identical
unique claims.
This is used to avoid any value having multiple incompatible
definitions as a term name.
Some relations may also be given primitive semantics, where some
claims in that relation will be considered satisfied even if no block
emits them.
In the ZK implementation, this corresponds to using specialized
accelerator circuits rather than the general purpose block claims
to generate facts about e.g. cryptographic primitives, and adding
these extra facts into the lookup argument.

The body of a block rule definition is the list of
emitted and demanded claims, where the arguments can be variables
or constants. The list of hypotheses can also include some
primitive constraints that must hold between variables, such
as inequality. In pseudocode, we allow arbitrary mathematical
expressions as primitive constraints.
The block rule also has a name, declares an order of the variables
for writing down the local variables, and indicates which of the
variables are included in the public data if the block appears
in the public part of a transcript.
Some block rules, such as those that emit axioms as part of
a programming language definition, might only be allowed in the public part
of the transcript.

A transcript is valid if every block instance follows the form of
some block rule (while satisfying the primitive constraints),
no unique claims are duplicated, and every demanded claim is
satisfied.

\subsubsection{Block Model Notation}\label{block-model-notation}

We write rule definitions with concrete syntax inspired by Datalog.
We do, however, write \verb|-:| rather than \verb|:-|, because the
second looks too much like a turnstile $\vdash$ pointed in the
wrong direction, and the semantics are not close enough for
exact syntactic compatibility to be useful.
All ordinary claims are written as a name applied to variables.
Any other expressions among the hypotheses represent primitive
constraints or perhaps are pseudocode that could be elaborated
into additional claims.

If negation is derived syntax, we might have a block rule for decomposing
negation named \texttt{check\_not} with claims described by

\begin{verbatim}
check_not(TN,T):
  is_not(TN,T) -: is_impl(TN,T,TB), is_bot(TB)
\end{verbatim}

The arguments on the header line are used when listing blocks in
a transcript.
If only some of the arguments will be specified when the block is
used in the public portion of the transcript, the argument list
is divided with a semicolon (\texttt{;}).
When writing example transcripts informally we might leave out
trailing arguments that can be inferred from the rest of the transcript.

Unique claims will be tagged \texttt{UNIQUE}. To declare an implication
pattern we might have a block

\begin{verbatim}
def_pat_impl(T,TA,TB,k,ka,kb):
  UNIQUE wf_pat(T), wf_pat(T,k), is_impl(T,TA,TB)
   -: wf_pat(TA,kA), wf_pat(TB,kB), k > max(ka,kb)
\end{verbatim}

The unique claims are in a different namespace, so we can have
\texttt{UNIQUE wf\_pat} take one argument, and \texttt{wf\_pat} take two.
We don't want to allow a conflicting definition of a pattern named
\texttt{T} as a term with another depth so we can't include
\texttt{k} in the arguments of the unique claim, but we must
include the argument in the ordinary claim
to enforce that defined terms are acyclic.

Restricted blocks will be tagged \texttt{SETUP} on the header line. This
is used especially and perhaps only for emitting axioms when setting up
a program instance.

\begin{verbatim}
assumption(T): SETUP
  proved(T,0) -: wf_pat(T,_)
\end{verbatim}

\subsection{Using the Block Model}\label{using-the-block-model}

We will now describe a few patterns for applying the above block model
that are useful for implementing a proof system, especially how to
handle term syntax and functions.
This description should explain that the model is sufficiently expressive
to express mathematical proofs, and motivate the parts of the design such
as unique claims which are not similar to ideas found in Datalog.
For an extended example see the
propositional logic proof system in \cref{sec:prop-example-proof-blocks}.

\subsubsection{Term Representation}\label{term-representation}

Term construction and pattern matching can be handled through claims as
well. This might seem a bit inefficient compared to string-based or
pointer-based representations in conventional programs, but recall that
RAM itself is implemented in zkVMs by a permutation argument.
The zkVM essentially communicates claims like ``the result of reading address
\texttt{a} at cycle \texttt{t} is \texttt{v}'' between widely separated
instructions in the transcript (the successive instructions accessing
a memory location), by using the mathematical techniques that
can be applied directly to claims like ``term
\texttt{x} is constructor \texttt{C} applied to \texttt{x1} and
\texttt{x1}''.

We encode tree or DAG data by giving every node a name,
which are single field elements.
Every parameter of a proof rule or judgment has a known type, so it's
not a problem if a field value (such as a small number) is used as a
name in multiple types, as long as it has a unique interpretation in
each type.

For a type \texttt{T} we will have a relation for being a well-formed
\texttt{T} value, whose arguments are the name and a ``depth'', like
\texttt{wf\_T(x,d)}. For each constructor \texttt{TCk} we will also have
a relation saying that the value is formed by applying that constructor to
specified arguments, like \texttt{is\_T\_C1(x,x1,...,xk)}. (allowing
claims with many arguments would require the ZK implementation to
handle wider tuples, efficiency might motivate packing the argument lists
themselves as a sort of data, but applicative matching logic formulas
only need constructors with two arguments).

To ensure these claims are coherent, every block that emits a
\texttt{wf\_T(x,d)} claim will also emit a unique claim
\texttt{UNIQUE wf\_T(x)} to ensure there is only one interpretation of that
name as a value of type \texttt{T}.

For each constructor there will be an associated block rule that
will emit the general \texttt{wf\_T} claims along with the appropriate
constructor claim \texttt{is\_T\_Ci}, while consuming
well-formed value claims about all the arguments, and constraining the
depths. Any extra side conditions on the constructor could also be
checked here. There could also be a block for declaring opaque terms that
just emit the \texttt{wf\_T} claims without any specific constructor
claims.

Any logical rule that requires a specific shape of formulas in hypotheses
or conclusions, such as the expression $\varphi \rightarrow \psi$ in
the hypothesis $\vdash \varphi \rightarrow \psi$ of a Modus Ponens
rule, can be transformed by adding extra variables to
name the larger expressions and extra hypothesis about the syntactic
relationships between those variables, so the hypotheses and conclusions
that claim something has been proved will only talk about bare variables.
This leaves a logical rule that can be translated directly to a block
rule.
For example, rather than a Modus Ponens rule concluding $\vdash B$
from hypotheses $\vdash A \rightarrow B$ and $\vdash A$, it could
instead be written in terms of three variables $T$, $A$, $B$,
and conclude $\vdash B$ from $\vdash A$, $\vdash T$, and an
additional hypothesis $T = A \rightarrow B$ (which corresponds to the
\texttt{is_impl} relation).

\subsubsection{Function Representation}\label{function-representation}

Functions over the defined data types can be modeled with a relation
taking an extra parameter for the output, such as a relation
\texttt{subst(T,TB,X,TR)} to mean \texttt{T\ =\ TB{[}TR/x{]}}.
There will be a block rule for each clause of the function definition,
which will consume constructor claims to examine the arguments and
also enforce the shape of the result, and consume additional
claims corresponding to any function calls in the clause, recursive or
otherwise. Termination is usually ensured by structural recursion along
the already-acyclic data, but could be enforced by an extra argument if
needed.

Note that when using a block in this style, there must already be
term-defining blocks declaring a name and the structure of the result term.
For functions thought of as producing new terms, it would also be possible
to have variants of the function-defining block rules that also emit the
data-defining claims about the result value.
However, we would always need to keep the non-defining version of
every block rule available, to avoid a uniqueness error or preserve
sharing in case the result of the application had already been
independently produced elsewhere.

\subsubsection{Acyclicity}\label{acyclicity}

For both proofs and term declarations, we will be breaking up a DAG
structure into blocks and we want to enforce that it is acyclic. In Hilbert
proofs, this relies on ordering of the steps, but the standard
constructions for a lookup constraint in a zkSNARK are unordered.
It is easy to enforce acyclicity at the definition level by adding
an extra ``depth'' argument to relations and extra constraints in
the block rules that enforce that hypotheses have a smaller ``depth''.

To enforce that the ``depth'' is exactly the depth we would need not
only the inequalities \texttt{k\ \textgreater{}\ k\_i} for each
hypothesis depth \texttt{k\_i}, but also to enforce that
\texttt{k\ ==\ k\_i\ +\ 1} for at least one hypothesis (or to use a
different approach that accumulates the maximum across all \texttt{k\_i}).
But nothing is harmed by only checking the inequality constraints
because that is already sufficient to ensure derivations are acyclic,
and provers are still allowed to use the actual depth.
It does not seem useful to constrain the depth of proof trees, but
even if we did, the only natural constraint is imposing a maximum depth,
which can still be enforced by putting a maximum on the ``depth''.

A useful property of depths is that they are (or can be chosen to be)
relatively small numbers, and it is
more efficient to define inequality over a smaller domain than the
entire field. The actual depth is bounded by the number of blocks, so
supporting numbers up to $2^{40}$ or so would cover any possible
proof with a feasible transcript size, but \emph{any} size is still
sound. Rather than hard-coding the less-than relation up to a fixed size,
note that inequality reduces to a ``range check'' -
if there is a \texttt{smallPos} predicate that tests
$0 \le x < N$, then $0 \le a < b \le N$ if there
exists a $p$ with $a + p = b$, and
\texttt{smallPos(p)}, \texttt{smallPos(b)}.
If we just want a
well-founded relation and $(2^{40})^2$ doesn't overflow the size
of the finite field, we might even just check \texttt{a\ +\ p\ =\ b} and \texttt{smallPos(p)}.

The main sources of proof size in our applications are taking many
rewrite steps in an execution, and working over large program
configurations. In both cases by using balanced trees a logarithmic
depth suffices.
There are efficient ZK implementations of range checks, but
for writing self-contained block model examples,
spending $O(N)$ blocks to populate a \texttt{smallPos} table up to maximum
value $N$ can be affordable.

Note that acyclicity could be enforced with \emph{any} well-founded
relation, if another relation is cheaper than inequality.
Over the integers, term size looks like a simple option, with the size
of a new term defined by a simple equation $k = 1 + k_1 + \ldots + k_n$.
But that does not work in modular arithmetic; sharing makes it easy to
construct terms whose unshared size is exponentially large and induce
overflows.
\subsection{Block Model Example: Propositional Logic}\label{block-model-example-propositional-logic}

As a further example of the block model, we present an implementation of propositional logic.
Rules from this example will also be used later when discussing how the block model can be implemented.
We first introduce the main relation for claiming that a formula
has been proved and other relations that will be needed to state
the rules of propositional logic, then show the block rules
implementing the proof rules, and then show how to implement
the auxiliary relations, including block rules and additional
relations.

Because the point is to be a good example, we include metavariables and
an instantiation rule and a block for generically asserting a term
as an axiom, but also provide block rules that directly check axiom
schemes. Without instantiation we wouldn't have any auxiliary recursive
operations over terms, and the axiom schemes demonstrate how to
translate proof rules with complicated expressions.

\subsubsection{Main Claim}\label{main-claim}

The main claim is \texttt{proved(T,k)}, meaning that the term
represented by \texttt{T} has a proof of depth \texttt{k}.

For metavariable instantiation we have claim
\texttt{instantiation(T,TP,S)} meaning that term \texttt{T} is the
result of applying the metavariable substitution \texttt{S} to term
\texttt{TP}. This already implies the substitution is well formed, so
the proof rules don't need any claims about substitution syntax.

The most basic claim about terms is that \texttt{T} is the name of a
particular well-formed term. In proof rules we write
\texttt{wf\_term(T,\_)}, because term definitions need to include a depth
argument too, but proof rules never care.

The other relations that we will need in the proof rules are those
for applying a substitution, and for checking that a term has a particular shape.
The claim \texttt{instantiation(T,TP,S)} means that term \texttt{T} is
the result of applying substitution \texttt{S} to the term \texttt{TP}.
The only syntactic claims we need for the proof rules are
\texttt{is\_impl(T,T1,T2)} which means
\texttt{T} is the implication \texttt{T1-\textgreater{}T2}
and \texttt{is\_not(T,T1)} which means \texttt{T} is the negation of \texttt{T1}.
The block rules for defining these claims can only be produced when all of the term variables are
already well-formed expressions, so block rules can often avoid
separate \texttt{wf\_term} hypotheses.

Block rules and further relations for defining term data will be given
later, and consuming these claims in the proof rules does not require
that these are actually primitive constructors in the term representation.
Some presentations of propositional logic define implication in terms
of disjunction and negation, or negation in terms of implication and
a false term, or take both implication and negation as primitive and
define conjunction and disjunction.

\subsubsection{Proof Blocks}\label{sec:prop-example-proof-blocks}

The \texttt{assert} block is only allowed in the setup phase, and emits a
claim stating that a term has been proved.
If the term definition is not also included in the public part of the
transcript, the prover could choose any definition of the undefined 
(sub)term names.
The emitted claim takes a provided depth $k$ rather than just emitting
at depth zero, so this rule could be used to exactly replace a provable
lemma whose proof has a certain depth.

\begin{verbatim}
assert(T,k): SETUP
  proved(T,k) -: wf_term(T,_).
\end{verbatim}

The \texttt{demand} block just consumes a claim that a term has been proved.
This is meant to be used in the public part of an instance to force the
prover to come up with a proof of the specified formula.
It's useless but harmless in the private part of the transcript.

\begin{verbatim}
demand(T):
  -: proved(T,_).
\end{verbatim}

The basic derivation rule is \texttt{modus\_ponens}.

\begin{verbatim}
modus_ponens(T;TA,TB,k,k1,k2):
  proved(TB,k) -:
    is_impl(T,TA,TB), proved(T,k1), proved(TA,k2), k1 < k, k2 < k.
\end{verbatim}

The other derivation rule instantiates metavariables.

\begin{verbatim}
instantiate(T,TP,S; k1, k):
  proved(T,k1) -:
    proved(TP,k), instantiation(T,TP,S), k1 = k+1.
\end{verbatim}

The first axiom (K combinator) is
$\texttt{TA}\rightarrow\texttt{TB}\rightarrow\texttt{TA}$.

\begin{verbatim}
axiom1(T; TA,TB):
    proved(T,0) -:
      is_impl(TI,TB,TA), is_impl(T,TA,TI).
\end{verbatim}

The second axiom (S combinator) is
$(\texttt{TA}\rightarrow(\texttt{TB}\rightarrow\texttt{TC}))\rightarrow((\texttt{TA}\rightarrow\texttt{TB})\rightarrow(\texttt{TA}\rightarrow\texttt{TC}))$.
The variable name mnemonics are H for Hypothetical and I for Implication.

\begin{verbatim}
axiom2(T; TA,TB,TC,THB,THC,TI,THI,TIH):
  proved(T,0):
    is_impl(THB,TA,TB), is_impl(THC,TA,TC), is_impl(TI,TB,TC),
    is_impl(THI,TA,TI), is_impl(TIH,THB,THC),
    is_impl(T,THI,TIH).
\end{verbatim}

The third propositional axiom covers negation,
$(\neg\texttt{A}\rightarrow\neg\texttt{B})\rightarrow(\texttt{A}\rightarrow\texttt{B})$.

\begin{verbatim}
axiom3(T; TA,TB,TI,TNA,TNB,TIN):
  proved(T,0):
    is_impl(TI,TB,TA),
    is_not(TNA,TA), is_not(TNB,TB),
    is_impl(TIN,TNA,TNB),
    is_impl(T,TIN,TI).
\end{verbatim}

\subsubsection{Auxiliary Claims}\label{auxiliary-claims}

To define instantiation we need relations representing the term structure of
substitution, and we also need to be able to recognize metavariable terms.
The term syntax claim \texttt{is\_mvar(T,V)} means term \texttt{T}
consists of the metavariable \texttt{V}.
Metavariable names and term names are distinct namespaces, so there is
no necessary numerical relationship between the numbers.

A further auxiliary relation \texttt{subst\_lookup(V,T,S)}
gives the term resulting from looking up variable \texttt{V} in
substitution \texttt{S}, this is needed in the block rule for
defining substitution in the \texttt{is\_mvar} case.
To use the \texttt{instantiate} proof rule we need to be able to
derive \texttt{instantiation} claims about arbitrary well-formed
subterms, so if any terms are none of \texttt{is\_impl}, \texttt{is\_not},
nor \texttt{is\_mvar} additional block rules will be required.

We define substitutions as built up from a substitution for a single
variable \texttt{is\_single\_subst(S,V,T)} and unions of substitutions
\texttt{is\_union\_subst(S,S1,S2)}.
To have a sound proof system we will need to ensure we can't have both
\texttt{subst\_lookup(V,T1,S)} and \texttt{subst\_lookup(V,T2,S)} with
different \texttt{T1} and \texttt{T2}.

We could enforce at construction time that unions only join disjoint
substitutions, or enforce at lookup time that the substitution only
contains one definition for the replacement variable.
For both cases we need an auxiliary relation \texttt{not\_in\_subst(V,S)}
for checking that substitution \texttt{S} does not contain a replacement
for variable \texttt{V}.
We use the second option because the first would require another relation
for asserting that two substitutions were disjoint.
It is also efficient, unlike checking at each lookup in a conventional
program, because \texttt{not\_in\_subst} and \texttt{subst\_lookup} claims
are reusable.

A well-formed substitution claim is only needed in the substitution
constructor blocks themselves.
The rules defining the \texttt{not\_in\_subst} would actually work
correctly if cyclic terms were allowed, but we could derive false
\texttt{subst\_lookup} facts for cyclic terms
(\texttt{subst\_lookup(V,T,S)} for any \texttt{V} which does not actually
appear in \texttt{S}, by using the union rules along a cyclic path in
\texttt{S} and deriving true \texttt{not\_in\_subst(V,S')} claims for the
other arguments of those unions).

Metavariables are atomic, so we don't need any sort of
\texttt{wf\_mvar(V)} claim.

\subsubsection{Substitution Application}\label{substitution-blocks}

Substitution recurses over implication and negation

\begin{verbatim}
subst_impl(T,TI,S; TA,TB,TA2,TB2):
  instantiation(T,TI,S)
  -: is_impl(TI,TA,TB),
     instantiation(TA2,TA,S),
     instantiation(TB2,TB,S),
     is_impl(T,TA2,TB2).

subst_not(T,TN,S; TB,TB2):
  instantiation(T,TN,S)
  -: is_not(TN,TB),
     instantiation(TB2,TB,S),
     is_not(T,TB2).
\end{verbatim}

At a metavariable, we use the lookup

\begin{verbatim}
subst_mvar(T,TV,S):
  instantiation(T,TV,S)
  -: is_mvar(TV,V),
     subst_lookup(V,T,S).
\end{verbatim}

The above rules are already enough for a complete proof system,
if the prover always constructs substitutions giving a replacement
for all variables in the term, but we can give an additional block rule
saying a metavariable outside the domain of the substitution is left
unchanged, using the \texttt{not\_in\_subst} relation that we already
need for other reasons.

\begin{verbatim}
subst_mvar_missing(TV,S):
  instantiation(TV,TV,S)
  -: is_mvar(TV,V),
     not_in_subst(V,S).
\end{verbatim}

Now we define substitution lookup.
The three cases cover finding the target variable in a
single-variable substitution, or to the left or right of
a union.
To ensure lookup is deterministic as a function of \texttt{S}
and \texttt{V} the union cases also check that the variable
doesn't appear in the other side of the union.
With this design a valid transcript could declare a union
that has conflicting replacements for a variable

\begin{verbatim}
subst_here(S; V,T):
  subst_lookup(V,T,S)
  -: is_single_subst(S,V,T).

subst_left(S; V,T,SL,SR):
  subst_lookup(V,T,S)
  -: is_union_subst(S,SL,SR),
     not_in_subst(V,SR),
     subst_lookup(V,T,SL).

subst_right(S; V,T,SL,SR):
  subst_lookup(V,T,S)
  -: is_union_subst(S,SL,SR),
     not_in_subst(V,SL),
     subst_lookup(V,T,SR).
\end{verbatim}

Checking that a variable is not in a substitution only needs
two rules. The union case must recurse into both subterms.

\begin{verbatim}
subst_not_here(V,S; V1,T):
  not_in_subst(V,S)
  -: is_single_subst(S,V1,T),
     V != V1.

subst_not_union(V,S; SL,SR):
  not_in_subst(V,S)
  -: is_union_subst(S,SL,SR),
     not_in_subst(V,SL),
     not_in_subst(V,SR).
\end{verbatim}

\subsubsection{Substitution Definition}\label{substitution-definition}

\begin{verbatim}
def_subst_single(S,V,T):
  is_single_subst(S,V,T),
  UNIQUE wf_subst(S), wf_subst(S,0)
  -: wf_term(T,_).

def_subst_union(S,SL,SR; k,kl,kr):
  is_union_subst(S,SL,SR),
  UNIQUE wf_subst(S), wf_subst(S,k)
  -: wf_subst(SL,kl), wf_subst(SR,kr),
     kl < k, kr < k.
\end{verbatim}

\subsubsection{Term Definition}\label{sec:prop-example-term-definition}

Just to mix things up, we define terms so the primitive connective are
implication ($\rightarrow$) and false ($\bot$, aka bottom), and negation is notation for an
implication \(T\rightarrow\bot\).
For this we will have a claim \texttt{is\_bot(B)}.

We could potentially try to fix a reserved term code for \texttt{bot},
but then transcripts would probably need to anyway include a special
block to emit \texttt{UNIQUE wf\_term(\textless{}bot\textgreater{})}
to prevent that code from being reused.

The block rule emitting \texttt{is\_not} doesn't define a new term name.

\begin{verbatim}
check_not(T; TB,B):
  is_not(T,TB)
  -: is_impl(T,TB,B), is_bot(B).
\end{verbatim}

Here are the ones that actually declare terms

\begin{verbatim}
def_term_bot(B):
  is_bot(B),
  UNIQUE wf_term(B), wf_term(B,0) -: .

def_term_mvar(T,V):
  is_mvar(T,V),
  UNIQUE wf_term(T), wf_term(T,0) -: .

def_term_impl(T,TA,TB; k,ka,kb):
  is_impl(T,TA,TB),
  UNIQUE wf_term(T), wf_term(T,k)
  -: wf_term(TA,ka), wf_term(TB,kb),
     ka < k, kb < k.
\end{verbatim}

\subsubsection{Depth Handling}\label{depth-handling}

We define a \texttt{depthLt} relation that can replace the $<$ primitive
condition, to support later discussion of how to implement the block model in ZK\footnote{Addition is easily handled in arithmetic circuits or polynomial constraints, but inequality is not so primitive.}.
This is implemented in terms of a \texttt{smallPos} relation which will
also be explicitly populated with small positive numbers by block instances.

\begin{verbatim}
depthLtCheck(S,L; P):
  depthLt(S,L) -: L == S + P, smallPos(P).
\end{verbatim}

We don't impose a range check \texttt{smallPos(L)}, because we could only
hit an overflow if $N\cdot M$ exceeds the field size, where $N$ is the
number of \texttt{depthLtCheck} block instances and $M$ is the number
of \texttt{smallPos} instances, which would require a transcript length on the order of the square root of the field size.

\begin{verbatim}
smallPosOne():
  smallPos(1)
smallPosNext(k; k0):
  smallPos(k) -: smallPos(k0), k == k0 + 1.
\end{verbatim}

\subsubsection{Example Trace}\label{example-trace}

To prove \texttt{A-\textgreater{}A}, name \texttt{A-\textgreater{}A} by
\texttt{B}.
Then \texttt{(A-\textgreater{}(B-\textgreater{}A))-\textgreater{}((A-\textgreater{}B)-\textgreater{}(A-\textgreater{}A))}
is an instance of propositional axiom 2 (S combinator), and
both \texttt{A-\textgreater{}(B-\textgreater{}A)} and
\texttt{A-\textgreater{}B\ ==\ A-\textgreater{}(A-\textgreater{}A)} are
instances of propositional axiom 1 (K combinator), 
so the conclusion follows by modus ponens in two steps.

Numbering the terms, we assign the first codes to \texttt{A},
\texttt{B} and the axiom instances, and then have to name only
two further terms to have names for all subterms.

\begin{verbatim}
0 := v0 or A
1 := A->A (or B)
     0->0
2 := A->(A->A) or A->B
     0->1
3 := A->(B->A)
     0->6
4 := (A->(B->A)) -> ((A->B)->(A->A))
     3->5
5 := ((A->B)->(A->A))
     2->1
6 := (B->A)
     1->0
\end{verbatim}

These terms can be declared with blocks

\begin{verbatim}
def_term_mvar(0,0)
def_term_impl(1,0,0; 1,0,0)
def_term_impl(2,0,1; 2,0,1)
def_term_impl(3,0,6; 2,0,1)
def_term_impl(4,3,5; 4,2,3)
def_term_impl(5,2,1; 3,2,1)
def_term_impl(6,1,0; 2,1,0)
\end{verbatim}

The proof claims can be emitted with

\begin{verbatim}
axiom1(2; 0,1)
axiom1(3; 0,6)
axiom2(4; ...)
modus_ponens(4; 3,5, 1,0,0)
modus_ponens(5; 2,1, 2,1,0)
\end{verbatim}

\noindent
which would satisfy a block \texttt{demand(1)}. For the depth checking
these turn out to be enough inequalities and \texttt{smallPos} values.

\begin{verbatim}
depthLtCheck(0,1)
depthLtCheck(0,2)
depthLtCheck(0,3)
depthLtCheck(1,2)
depthLtCheck(1,3)
depthLtCheck(2,3)
depthLtCheck(3,4)
smallPosOne()
smallPosNext(2)
smallPosNext(3)
\end{verbatim}
\subsection{Implementation with Circuits and Folding}\label{block-implementation-folding}

To implement the block model with arithmetic circuits (or R1CS constraints),
one natural approach is to have specialized subcircuits corresponding to
each block rule.
A rule definition translates to a subcircuit with inputs corresponding to
the parameters of the rule and outputs corresponding to the hypotheses, conclusions,
and uniqueness tag (if needed) of the rule.
To check consistency of a block transcript, multiple copies of each rule circuit
will need to be connected to additional components that enforce that the hypotheses
are all contained in the conclusions and enforce that the unique claims are unique.
With additional Boolean inputs for disabling individual copies of the rule subcircuits,
a single fixed circuit can check block transcripts of any size up to a certain
maximum capacity.
To remove this limit, we will modify the circuit so multiple copies can be used
together to check arbitrarily large transcripts, and apply \emph{folding} \cite{Nova}
to efficiently check as many copies as needed with a fixed size SNARK.
This final circuit is called the \emph{segment} circuit.
An example rule subcircuit is shown in \cref{fig:modus_ponens_circom}.

Creating a specialized circuit for a set of block rules requires fixing the
set of rules in advance, but this is similar to fixing the set of proof
rules for a mathematical logic, like the Matching Logic used for all languages
in \cref{sec:mpg}.
In the mathematical proofs, a language semantics is given as a set of definitions,
which corresponds to a collection of block instances in a transcript, using
term-defining and axiom-declaring block rules in \cref{sec:prop-example-term-definition}
and \cref{sec:prop-example-proof-blocks} in the propositional logic example.

\begin{figure}
\begin{verbatim}
template modus_ponens() {
  signal input T,k, TA,k1, TB,k2;

  signal output conclusions[1][N()];
  conclusions[0] <== proved_claim(TB,k);

  signal output hypotheses[5][N()];
  hypotheses[0] <== is_impl_claim(T,TA,TB);
  hypotheses[1] <== proved_claim(T,k1);
  hypotheses[2] <== proved_claim(TA,k2);
  hypotheses[3] <== depthLt_claim(k1, k);
  hypotheses[4] <== depthLt_claim(k2, k);
}
\end{verbatim}
\caption{Modus Ponens Subcircuit, expressed in Circom}
\label{fig:modus_ponens_circom}
\end{figure}

\subsubsection{Claim Representation}

All claims can be represented uniformly as tuples of field elements.
Consider all the relations in the chosen set of block rules.
There is some maximum arity $k$.
Each relation will be assigned a distinct tag, which is a nonzero field element.
A claim will be represented as a tuple of $k+1$ field elements, with the
first element being the tag of the relation, followed by the arguments
of the claim, padded to length $k+1$ with trailing zeros.

In the propositional example, relations have at most three arguments,
so 4-tuples suffice. A claim like \texttt{is_impl(2,0,1)} would
be represented as a tuple $(\langle \texttt{is\_impl} \rangle, 2, 0 ,1)$
where $\langle \texttt{is\_impl} \rangle$ is the tag for the \texttt{is_impl}
relation, which could be a small value like 5 or 12.
A claim \texttt{proved(2,2)} would be represented by
$(\langle \texttt{proved} \rangle, 2, 2, 0)$.

For subset and permutation arguments, these tuples are represented as
single field elements using a Fiat-Shamir parameter $\alpha$.
The tuple $(x_0, \ldots, x_k)$ is represented by $\sum_{i=0}^k \alpha^ix_i$,
so $(\langle \texttt{proved} \rangle, 2, 2, 0)$ would be encoded as
$\langle \texttt{proved} \rangle + \alpha 2 + \alpha^2 2$.
Computing this representation of a \texttt{proved} claim in a specialized rule
circuit only requires two multiplication operators - the powers of
$\alpha$ are computed once and shared around the circuit, and no explicit
terms are required for the trailing zeros.
Tag values are nonzero so the representation zero (and the all-zero tuple)
is distinct from any valid claim, and can be used as a dummy value.

\subsubsection{Lookup Argument}

For checking the subset relation, we use the LogUp lookup argument \cite{logup}.
In primitive form, this checks that the set of values in a list
$l_1,\ldots,l_k$ of field elements is a subset of the set of values in a list
$t_1,\ldots,t_n$.
The argument is based on the equation
\[\sum_{i=1}^k \frac{1}{l_i - \beta} = \sum_{i=1}^n \frac{m_i}{t_i - \beta}\]
When considering the expressions as rational functions of $\beta$ and if
$k$ and $n$ are much smaller than the characteristic of the field,
this equality holds if and only if the $l$ are a subset of the $t$ and the $m$ 
correctly count the multiplicity, in the sense that for all values $f \in \mathbb{F}$
\[\sum_{i \mid l_i = f} 1 = \sum_{i \mid t_i = f} m_i\]

The concrete evaluation of a uniformly random $\beta$ is almost certainly equal
only if the rational functions are equal.
In an arithmetic circuit, quotients are not easy to compute purely in terms of addition and multiplication gates,
but it is easy to take an auxiliary input $q_i$ and force it to be the correct quotient
with a constraint like $q_i(v_i - \beta) = m_i$.
Consider rearranging the sum like
\[\sum_{i=1}^k \frac{1}{l_i - \beta} - \sum_{i=1}^n \frac{m_i}{t_i - \beta} = 0\]
Rearranging further, a rule circuit can output a single value which is the portion
of this difference corresponding to the hypotheses and conclusions from that rule instance,
and the overall circuit just needs to sum these contributions together.
The flag for disabling a rule circuit can be applied by changing this output to zero
without adding complexity to the internal circuitry.
Furthermore, the overall sum will be an output of the segment circuit, instead of
directly including a constraint that the sum is zero, allowing the lookup argument
to span across many copies of the segment circuit by adding these ``accumulator''
outputs together during the folding process, and only checking that the final
sum balances to zero.

\subsubsection{Uniqueness}

To enforce uniqueness of the unique claims emitted by the block rules
we construct a lexicographically sorted copy of that list of claims.
The copy is provided as additional circuit inputs.
That a sorted list has no duplicates can be checked with just
constraints between adjacent entries.
That a list is sorted can also be checked with constraints just
between adjacent entries.
Enforcing that a list is a permutation of another is a non-local
property, which can be checked with a \emph{permutation argument}.

One classic permutation argument uses the polynomial equation
\[\prod_{i=1}^n (a_i-\beta) = \prod_{i=1}^m (b_i-\beta)\]
or we can use the LogUp equation with multiplicities all set to 1,
so the accumulation operation is addition rather than multiplication.

When using multiple copies of the segment circuit to check a longer
transcript, the sorting and the sorted list needs to span across all
the circuits.
As with the subset check over hypotheses, the accumulated sum from
the permutation argument is an output of the segment circuit rather than
being constrained to balance within the segment circuit, so the
accumulator can be combined across all segments.
To handle the constraints between adjacent entries in the sorted list,
the segment circuit has an extra ``previous unique claim'' input treated
as preceding the first entry in the sorted list, and outputs a copy of
the last claim in the list.
When folding together multiple segment circuit instances, it will be checked
that the ``previous unique claim'' matches the last claim output from the
previous segment, or is set to the dummy claim for the first segment.

\subsubsection{Fiat-Shamir for Circuits and R1CS}

The Fiat-Shamir heuristic implements a ``random'' choice of parameters
such as $\alpha$ and $\beta$ by applying a hash to (commitments to)
``earlier data''.
This transforms an interactive protocol involving a true random choice
into a non-interactive protocol, while trying to make attacking the
resulting non-interactive proof take as many attempts as would be
required to attack a true random choice.

If not enough data is included in the hash, this can be insecure
even when the protocol would be secure for a true random choice,
if the attacker can compute the hash output but then adjust ``earlier''
values that are not covered by the hash to hit a false positive
condition that would be overwhelmingly unlikely to occur by chance.

Often the Fiat-Shamir heuristic is described with all values being
directly fed into the hash, but if we are already computing a vector commitment
$\bar{x}$ to a vector $\vec{x}$, then including the small commitment
$\bar{x}$ in the hash also works to make the result depend on all entries of $\vec{x}$.

For a circuit, the Fiat-Shamir parameters will be provided as circuit
inputs, and the data that might be included in the hash
are any other circuit inputs or intermediate values.
A sufficient condition for security is that the values included in the
hash combined with the Fiat-Shamir parameters uniquely determine the
remaining inputs and intermediate values, in the sense of leaving at
most one satisfying assignment to any inputs not included in the hash.

In the R1CS translation of a circuit, the circuit structure is encoded
into the R1CS matrices $A,B,C$, and each position of the witness vector
$x$ maps onto an input, output, or intermediate value in the circuit, such
that satisfying assignments to the circuit are equivalent to vectors $x$
such that the extended vector $z = (1,x)$ satisfies the R1CS equation
$Az \circ Bz = Cz$.

To correspond to a selection of circuit values to commit to, the
entries of $x$ can be ordered as $(\vec{d},\alpha,\beta,\vec{a})$
where the $d_i$ are the pre-Fiat-Shamir values and $a_i$ are the
remaining values.

Many folding schemes for R1CS only call for an additively
homomorphic vector commitment $\bar{x}$.
An example is the Pedersen vector commitment, defined by
$\Com(\vec{g};\vec{x}) = \prod_i {g_i}^{x_i}$
for some choice of group and list $\vec{g}$ of generators.
If there is no further requirement on the vector commitment scheme,
we can define the commitment to an overall vector to be a tuple of
commitments to subvectors such as $(\bar{d},\overline{(\alpha,\beta)},\bar{a})$,
with addition and scalar multiplication defined pointwise.

This makes the vector commitments $\bar{d}$ and $\overline{(\alpha,\beta)}$
directly available in the proof certificate for the modified SNARK or folding scheme,
so a verifier can also easily check that $\alpha$ and $\beta$ were derived
from a hash of $\bar{d}$.

\subsubsection{Folding Schemes}

A \emph{folding} or \emph{split accumulation} scheme for a relation
\(R \subseteq X \times W\) between instance descriptions \(X\) and
witnesses \(W\) provides a \emph{folding verifier} which is a partial
function $\operatorname{fold}$ that takes as input two instances $x_1$ and $x_2$ and a
\emph{folding proof} $\pi$ and either rejects or outputs another instance
$x_3$.
A prover knowing $(x_1,w_1), (x_2,w_2) \in R$ can efficiently compute
$\pi, x_3, w_3$ with $x_3 = \operatorname{fold}(x_1,x_2,\pi)$ and $(x_3,w_3) \in R$.
The security property is that a computationally bounded party can only
produce tuples $(x_1,x_2,\pi,x_3,w_3)$
with $x_3 = \operatorname{fold}(x_1,x_2,\pi)$ and $(x_3,w_3) \in R$ if they
also know $w_1$ and $w_2$ with $(x_1,w_1), (x_2,w_2) \in R$.

The size of an element of \(X\) should be much smaller than \(W\). These
schemes almost always have part of \(X\) consist of a vector commitment
to \(W\), particularly an additively homomorphic commitment.

Many papers about folding schemes, including the Nova paper \cite{Nova} itself,
discuss applying folding schemes as an ingredient in building the more
complicated constructions of Incrementally Verifiable Computation(IVC) or
Proof Carrying Data(PCD), which allow giving a SNARK for the claim that
a recursively defined predicate holds, with a linear or general graph
recursion structure, respectively.

But for handling the segment circuits in a block model proof, we just
need to combine many instances of the segment circuit as siblings,
rather than in a recursive structure.
A small number of public parameters of the segment circuit need special
handling while combining instances, such as accumulators for the
lookup arguments, and Merkle trees over commitments to the pre-Fiat-Shamir data,
but for the rest of the circuit we only need to fold multiple instances
of the circuit together.

\subsubsection{Relaxed Committed R1CS}
The folding scheme presented in the Nova paper is called Relaxed Committed R1CS.
Further work such as HyperNova and ProtoGalaxy potentially offer improvements
such as cheaper folding or being able to heterogeneously combine instances of different circuits
into a single folded instance, but Relaxed Committed R1CS is particularly simple and
sufficient to illustrate the folding-based implementation strategy.

As the name suggests, it is based on a relaxation of R1CS, and involves vector commitments.
The ``relaxed'' part is changing the notion of a witness for a set of R1CS matrics
$A,B,C$ to be a tuple $(u,\vec{x},\vec{e})$ of a scalar $u$ and vectors $\vec{x}$ and $\vec{e}$
such that the vector $\vec{z} = (u,\vec{x})$ satisfies the equation
\[A\vec{z} \circ B\vec{z} = uC\vec{z} + \vec{e}\]
The tuple $(1,\vec{x},\vec{0})$ with $u = 1$ and $\vec{e}$ the zero vector is a
relaxed R1CS witness for $A,B,C$ if and only if $x$ is an ordinary R1CS witness for $A,B,C$.
The ``committed'' part is modifying this to use vector commitments to fit the
structure of a split relation.
The instance part is a tuple $(u,\bar{x},\bar{e})$ of scalar $u$ and group elements
$\bar{x}$ and $\bar{e}$
(in the codomain of a vector commitment scheme).
The witness part is a pair of vectors $(\vec{x},\vec{e})$, where
$((u,\bar{x},\bar{e}),(\vec{x},\vec{e}))$ is in the Relaxed Committed R1CS
relation defined by matrices $A,B,C$ iff $\bar{x}$ is a vector commitment to $\vec{x}$,
$\bar{e}$ is a vector commitment to $\vec{e}$, and $(u,\vec{x},\vec{e})$ is in the
Relaxed R1CS relation defined by those matrices.

The folding operation only needs to consider the small instance description $(u,\bar{x},\bar{e})$.
To fold two instances $(u_1,\bar{x}_1,\bar{e}_1)$ and $(u_2,\bar{x}_2,\bar{e}_2)$ an
honest prover needs to know corresponding witnesses $(\vec{x}_1,\vec{e}_1)$ and
$(\vec{x}_2,\vec{e}_2)$, and use them to compute a certain cross-term vector $\vec{t}$,
and then a vector commitment $\bar{t}$, which is provided as the folding proof.
To fold two instances together with a folding witness, a scalar $r$
is computed by hashing all of
$u_1,\bar{x}_1,\bar{e}_1,u_2,\bar{x}_2,\bar{e}_2,\bar{t}$, and the updated instance is
computed as $u \leftarrow u_1 + r u_2$, $\bar{x} \leftarrow \bar{x}_1 + r \bar{x}_2$,
$\bar{e} \leftarrow \bar{e}_1 + r \bar{t} + r^2 \bar{e}_2$.

The security argument in the paper establishes that it is infeasible to find vectors
$\vec{x}$ and $\vec{e}$ such that $((u,\bar{x},\bar{e}),(\vec{x},\vec{e}))$ satisfy
the Relaxed Committed R1CS relation, unless $\bar{t}$ was honestly computed from
knowing satisfying witnesses for both input instances, or the adversary can break the
hash or vector commitment.

\subsubsection{Segment Folding}\label{segment-inputs}

Following the circuit design earlier in this section, the
segment circuit has a fixed interface independent of the number
of block rule subcircuits included in each segment.

These circuit inputs or outputs that need to be inspected to combine multiple
segments are
\begin{itemize}
\setlength\itemsep{0em}
\item The subset accumulator $A$
\item The uniqueness accumulator $B$
\item The used Fiat-Shamir parameters $\alpha, \beta$
\item The ``previous'' and ``last'' unique claim tuples $\vec{u}_{\mathrm{in}}, \vec{u}_{\mathrm{out}}$.
\end{itemize}

An honest prover begins transforming a valid block model transcript into a list of segment circuit
instances by distributing the block instances of the transcript among the segments,
setting the rule subcircuit arguments and enabling flags accordingly,
also setting the conclusion multiplicities, and the sorted list of unique claims.
This determines all the pre-Fiat-Shamir data, so the prover can then compute vector
commitments to the pre-Fiat-Shamir parts of the circuit witnesses, and hash up
the Merkle tree over those commitments to derive the $\alpha, \beta$.
With those parameters determined the rest of the circuit can be evaluated,
and vector commitments to the rest of the circuit witnesses computed,
and then the Relaxed Committed R1CS instances and witnesses folded together.

A list of satisfying assignments to the segment circuit is consistent if
they all use the same $\alpha$ and $\beta$, and the $\vec{u}_{\mathrm{in}}$ of
each segment equals the $\vec{u}_{\mathrm{out}}$ of the previous.
It additionally describes a consistent block model transcript if
the sum over all $A$ is zero, the sum over all $B$ is zero, the $\vec{u}_{\mathrm{in}}$ of
the first segment is the dummy zero tuple, and $\alpha$ and $\beta$ were properly derived from all
the pre-Fiat-Shamir values of all the circuit instances.

An individual segment description consists of the
six public parameters along with claimed vector commitments
$(\bar{d},\bar{a})$ to the pre-Fiat-Shamir and remaining parts of the vector.

A consistent collection of segment descriptions is described by the above six
parameters along with a hash $H^{\mathrm{FS}}$ committing to pre-Fiat-Shamir data,
and a Relaxed Committed R1CS instance $(u,\bar{x},\bar{e})$.

We recursively define a predicate $\varphi_{\mathrm{fold}}(A,B,\alpha,\beta,\vec{u}_{\mathrm{in}}, \vec{u}_{\mathrm{out}},H^{\mathrm{fs}},(u,\bar{x},\bar{e}))$.

This holds in the single-segment case if there exists $(\bar{d},\bar{a})$ such that
$H^{\mathrm{fs}} = \operatorname{Hash}(\vec{u}_{\mathrm{in}}, \vec{u}_{\mathrm{out}},\bar{d})$,
$u = 1$, $\bar{e} = \bar{0}$ and $\bar{x} = (\bar{d},\bar{a},\bar{v})$
and $\vec{v}$ is vector of public parameters $(A,B,\alpha,\beta,\vec{u}_{\mathrm{in}},\vec{u}_{\mathrm{out}})$.

This holds in the recursive case if there exist $$(A_1,A_2,B_1,B_2,\vec{u}_{\mathrm{mid}},H^{\mathrm{FS}}_1,H^{\mathrm{FS}}_2,(u_1,\bar{x}_1,\bar{e}_1),(u_2,\bar{x}_2,\bar{e}_2))$$ and folding proof $\bar{t}$
such that
\begin{itemize}
\item $\varphi_{\mathrm{fold}}(A_1,B_1,\alpha,\beta,\vec{u}_{\mathrm{in}}, \vec{u}_{\mathrm{mid}},H^{\mathrm{fs}}_1,(u_1,\bar{x}_1,\bar{e}_1))$
\item $\varphi_{\mathrm{fold}}(A_2,B_2,\alpha,\beta,\vec{u}_{\mathrm{mid}}, \vec{u}_{\mathrm{out}},H^{\mathrm{fs}}_2,(u_2,\bar{x}_2,\bar{e}_2))$
\item $A = A_1 + A_2$
\item $B = B_1 + B_2$
\item $H^{\mathrm{FS}} = \operatorname{Hash}_{\mathrm{Node}}(H^{\mathrm{FS}}_1,H^{\mathrm{FS}}_2)$
\item $(u,\bar{x},\bar{e})$ is the result of folding $(u_1,\bar{x}_1,\bar{e}_1)$ and
  $(u_2,\bar{x}_2,\bar{e}_2)$ using $\bar{t}$
\end{itemize}

An honest prover processing a valid block transcript ends up with a folded instance
$(u,\bar{x},\bar{e})$ and values $H^{\mathrm{FS}}, \alpha, \beta, \vec{u}_{\mathrm{out}}$
such that $\alpha,\beta$ were derived from $H^{\mathrm{FS}}$ and $\varphi_{\mathrm{fold}}(0,0,\alpha,\beta,\vec{0},\vec{u}_{\mathrm{out}},H^{\mathrm{FS}},(u,\bar{x},\bar{e}))$.
Giving a SNARK for knowing a witness to the folded instance and succinct proofs for the other claims constitutes a SNARK for knowing a valid block model transcript.

\subsubsection{Estimating the Performance of the Folding Approach}
\label{estimating-performance-folding}

To better understand the potential for performance of the block model, we model the components of the proof generation process. Suppose that we have $N$ computational steps to verify in a proof. Suppose further that the main components of the proof procedure take time which is linear in the size of their inputs: We assume that for a segment of $k$ steps, providing a proof for a relaxed committed R1CS of this size, either as a direct proof or in the form of some other succinct proof, takes $t_{R1CS} k$ time. We further assume that committing to the data in such a segment takes $t_{msm} k$, and that folding 2 such relaxed committed R1CS instances of this size takes $c_{fold} + t_{fold} k$ time. Then the total time to commit and fold $N$ steps in $s$ segments, and then prove the final instance, is

\[
t_{msm} s \frac{N}{s}  + (s-1) (c_{fold} + t_{fold} \frac{N}{s}) + t_{R1CS} \frac{N}{s}
\]

The first term and second half of the second term are constant in $s$, so we can ignore these when minimizing. Since $s$ is a free parameter, we can minimize the total time by minimizing $s \cdot c_{fold} + (t_{R1CS} - t_{fold}) N/s$, which is minimized at 

\[
s = \sqrt{\frac{(t_{R1CS} - t_{fold}) N}{c_{fold}}}
\]

The total time to prove is then approximately

\[
    t_{msm} N + t_{fold} N + 2 \sqrt{(t_{R1CS} - t_{fold}) N c_{fold}} 
\]

For large $N$, the last term is asymptotically smaller and $t_{fold}$ is expected to be relatively small, so the total time is dominated by the first term.


Investigating concrete times for this model: Looking at our benchmarks, we see that our largest Metamath file with 258135 tokens were processed by the fastest prover in 19.82 seconds. Let us assume each of these tokens corresponds to a proof rule application, and estimate that the block model requires approximately 10 field elements per proof rule:

\begin{itemize}
\item 2 Field elements per proof rule to encode the rule's output
\item 2-4 Field elements per proof rule to encode the rule's input(s)
\item 2 Field elements per proof rule accumulate the output in a product for uniqueness checking
\item 2-4 Field elements per proof rule to accumulate the input(s) in a product for subset checking
\end{itemize}


We can then estimate that the block model would require 2581350 $\approx 2^{21}$ field elements for the same proof. Using benchmarks from \cite{cuzk}, we see that for Pippenger operating on a typical curve with a single V100 GPU, the time to commit to a vector runs to approximately $90/2^{21} = 0.000043ms$ per field element, which equates to $\approx 110ms$ for a vector of $2581350$ size. Considering that our zkVM benchmarks were run on a more powerful machine with 4 NVIDIA GeForce RTX 4090 GPUs, it is reasonable to think that commitments of this size could be handled in $\approx 14 ms$ with our setup (note that the clock speed of the 4090 is about twice that of the V100). This is around a $1400\times$ speed-up over the zkVM approach, which is on the same order of magnitude as the $3330\times$ speed-up that ZKSMT found when comparing their custom zkSNARK to a generic approach \cite{zksmt}.


\subsection{Implementing the Block Model in AIR}\label{block-model-implementation-air}
In this section we describe how the block model can be implemented in the
type of constraints natively supported by STARK and Plonkish-style
SNARKs.
It was named AIR (Algebraic Intermediate Representation)
in the STARK paper~\cite{BBHR18}. This form of arithmetization is oriented much more towards implementing a virtual machine with multiple registers which update according to particular operations.
In this style, the ZK witness will be a rectangular array of field elements.
For $k$ columns, the constraints will be specified as polynomials on
$2k$ variables which will be evaluated on pairs of successive rows
of the transcript and must always evaluate to zero.
The polynomials may also take a few additional arguments for Fiat-Shamir
parameters.
The public data of an instance consists of specified cells of the
table, or entire columns.

When implementing the block model on this style of ZK backend each
block will map to a rectangular area of the transcript.
Additional columns can be used for auxiliary purposes such as
accumulations for lookup and permutation arguments.
The constraints, acting only on pairs of rows, must enforce that all
blocks respect a given set of block rules, in addition to checking the
validity of the transcript.

In principle a specific set of block rules might be hard-coded into
the set of constraint polynomials, but it seems that would require
prohibitively many constraints, and would be less flexible.

Instead we will describe a generic block implementation in a
semi-``software'' style, where the basic functionality of emitting and
demanding claims and routing arguments among claims (and public block
arguments) happen in a fairly generic way, controlled by constants in
some ``setting'' columns. The contents of these settings are a kind of
``instructions'' or ``microcode'' for the block.

This narrows the task of enforcing allowed block rules to controlling
these block settings columns. This is somewhat similar to the handling
of the program text in Harvard-architecture zkVMs, but even simpler
because we don't have general purpose instruction sets or even
nontrivial control flow.

In this design, the main components are 

\begin{itemize}
    \item Claim and constraint handling
    \item Argument routing
    \item Block rule enforcement
\end{itemize}

We first describe the main layout of the block, especially columns which
are involved in more than one component, and then how each component can
be implemented.

\subsubsection{Common Block Layout}\label{common-block-layout}

There will be \texttt{block\_control} column, whose value on the first
row of a block is the code for the block rule, and then as many public
arguments as the block expects will be recorded in the following rows.
If the block layout needs additional rows, these entries of the
\texttt{block\_control} column will be forced to $0$.

This is laid out so that the public input column corresponding to the
gamma/claim part of a proof can be in the same format as the control
column, and a simple constraint copying nonzero values from the
public input column into the actual control column will enforce that
the full transcript has the required public portion.

There will be a pool of selector columns that are considered part of the
block structure. To commit to these values as part of block rule
enforcement, they are first combined into a single
\texttt{compressed\_selectors} column with a constraint like
\texttt{compressed\_selectors\ ==\ s\_1\ +\ 2*s\_2\ +\ ..\ +\ 2\^{}\{k-1\}*s\_k},
and then only the \texttt{compressed\_selectors} column is included in
the block fingerprint.

To delimit the block instances there will be selector columns
\texttt{block\_start} and \texttt{block\_end}, set to 1 only on the
first and last rows of a block.

For the interaction of the claim enforcement and argument routing
components, there will a reserved tuple of columns for laying out
claims, with columns \texttt{claim\_code} and \texttt{arg1} \ldots{}
\texttt{argk} (for however many arguments the design supports). We could
perhaps have several such tuples per row, but one seems sufficient if we
have some selectors route whether it is emitted, demanded, or otherwise.
We will also implement primitive constraints that don't go through the
usual claim mechanism, such as addition or inequality, to expect the
arguments to be in these argument columns, because that is what argument
routing component can control.

The block ``microcode'' consists of the block code, which means
only the first entry of the control column within the block layout,
and all values from the \texttt{compressed\_selectors} and \texttt{claim\_code} columns.
For the ``permutation style'' argument routing, the columns holding the
``tags'' values are also part of the ``microcode''.

\subsubsection{Claim Handling}\label{claim-handling}

We will have selectors to control how the claim columns on a row are
used, whether that is as an emitted claim, a demanded claim, a unique
claim, or not at all. When working with claims of less than maximum
arity the remaining columns will just be set to zero.

There will also be selectors to enforce any primitive constraints. A
basic set is addition and inequality. The addition selector can simply
apply \texttt{arg1\ ==\ arg2\ +\ arg3}. To enforce
\texttt{arg1\ \textless{}\textgreater{}\ arg2} we can use \texttt{arg3}
for an advice value and enforce \texttt{1\ ==\ (arg1\ -\ arg2)*arg3}.

To support block definitions where arbitrary constants are used in
arguments we can also have a selector that enforces
\texttt{arg1\ ==\ claim\_code}. This takes advantage of the fact that
the block rule enforcement already allows fixing arbitrary values for
the claim code to avoid introducing a new mechanism. Argument routing
then can be used to copy the value to other places.

The standard construction for permutation or lookup arguments over a
tuple of columns already relies on encoding the tuple into a single
field element using a Fiat-Shamir constant, so there is a natural degree
of indirection here.

It might be possible to use selectors to control whether a value is
multiplied into a lookup or permutation argument at all without using
any auxiliary columns at all, but even if not then we can definitely use
a selector to control whether an auxiliary column is set to zero or the
encoded tuple value. In this way, the worse case is three auxiliary
columns for the three emit/demand/unique roles, rather than needing
three copies of the entire claim layout columns.

We might choose to have multiple sets of claim layout columns if we
would prefer to have a shorter fatter transcript, but our current
performance hypothesis doesn't call for that. If there are multiple sets
there could be design choices like only allowing a subset to be used to
emit claims.

The extra columns used for the lookup argument are the product
accumulation column, and two columns for the permuted witness. The input
and output are already accounted for.

\subsubsection{Unique Claims}\label{unique-claims}

To enforce uniqueness, we will have extra columns for the permuted
version of the unique claims, plus one columns for the product
accumulator for the permutation constraint.

\newcommand{\ucc}{\texttt{ucc}}
\newcommand{\uca}{\texttt{uca}}
For our planned applications it seems sufficient to only support unique
claims with a single argument, so two columns \ucc
(unique check code) and \uca (unique check argument)
could represent the table.

The dummy element will be \texttt{(0,0)}. To check uniqueness we need to
enforce the disjunction of the constraints
\begin{align*}
\ucc & < \operatorname{next}(\ucc) \wedge \operatorname{next}(\uca) = 0 \\
\ucc & = \operatorname{next}(\ucc) \wedge \uca < \operatorname{next}(\uca) \\
\ucc & = \operatorname{next}(\ucc) = \uca = \operatorname{next}(\uca) = 0
\end{align*}

To avoid a general inequality test we can impose stricter assumptions
on the code and argument values, which are still compatible with using
unique claims for term definitions. The restrictions are that the codes
which can appear in unique claims are assigned consecutive values
starting at 1, at least one claim for each code appears in the
transcript (this can be arranged by defining dummy data if needed), and
the set of arguments used with a given claim code are also consecutive
(possible for our use because the arguments are just arbitrary names).

In this case, we use $X+1 = \operatorname{next}(X)$ rather than
$X < \operatorname{next}(X)$, allowing the constraints to be expressed
with simpler polynomials.


\paragraph{Unique Claim Hack\\}\label{unique-claim-hack}

In term defining blocks, we emit some claims for later use and also check
uniqueness. The emitted claims must include a well-formed term claim
with depth like \texttt{wf\_term2(T,k)}, so we can maintain acyclicity
over further term definitions. But we need to enforce that the name is
also not reused at another depth, so the claim checked for uniqueness
must omit the depth, like \texttt{wf\_term1(T)}.

But it is not necessary to have a single-argument claim available for
ordinary lookup because other block definitions could always just demand
\texttt{wf\_term2(T,\_)}.

We can cover the unique claim and the ordinary emitted claim with a
single row if we reused the same code value
\texttt{\textless{}wf\_claim\textgreater{}} with one argument in the
uniqueness check, and two in the ordinary lookup. We are already
planning to cover fewer columns in the permutation argument for
uniqueness (or only one), so just put the argument \texttt{k} in column
not covered (such as \texttt{arg2}), and enable both the ``emit'' and
``unique'' selectors on the row.

\subsubsection{Block Rule Enforcement}\label{block-rule-enforcement}

The block rule enforcement is based on taking a polynomial fingerprint
of the ``microcode'', and looking it up in a table of allowed block rules.

There will be a public input column or columns defining the allowed
block rules, two columns used, respectively, to accumulate the fingerprint
of the actual block instances and of the block definitions, and extra
columns implementing a lookup argument. It might be possible to share
with the main claim lookup, but that would need an extra security
argument that a malformed block could not emit a claim justifying its own
definition.

There will be a Fiat-Shamir constant \(\alpha\) (or
\texttt{blockcode\_alpha}) used for computing the polynomial
fingerprint.

For the block instance accumulation, if \texttt{block\_fingerprint} is
the accumulator column and we only have to put selectors and claim codes
in the microcode, we will have the constraint
\begin{align*}
\texttt{block\_fingerprint} & = \texttt{block\_control} \cdot \alpha^2 \\
& \quad + \texttt{compressed\_selectors} \cdot \alpha \\
& \quad + \texttt{claim\_code}
\end{align*}
on rows where \texttt{block\_start} is 1, and
\begin{align*}
\texttt{\textbf{next}}(\texttt{\textbf{block\_fingerprint}}) &= \texttt{\textbf{block\_fingerprint}} \cdot \alpha^2 \\
&\quad + \texttt{\textbf{next}}(\texttt{\textbf{compressed\_selectors}}) \cdot \alpha \\
&\quad + \texttt{\textbf{next}}(\texttt{\textbf{claim\_code}}) \\
\end{align*}
on rows where \texttt{next(block\_start)} is 0.
At the end of the block the accumulated fingerprint will be added into
the lookup side of a lookup argument for allowed block rules.

Using powers of \(\alpha\) rather than unrelated values to combine the
columns allows the block definitions to be given in a different
arrangement. The public input column can be completely linearized like.

\begin{verbatim}
<block_name>
<compressed_selectors>1
<claim_code>1
<compressed_selectors>2
<claim_code>2
...
\end{verbatim}

The expected fingerprint for a block can be accumulated over this
representation by incorporating one new value per row rather than two,
resetting the accumulator at the start of a new block code and contributing
the accumulated fingerprint into the table side of the allowed block
fingerprint lookup argument at the end of the block definition.
It probably requires a selector column to delimit the block definitions.

The set of block rules will not vary, so maybe there are techniques for
handling a lookup with a fixed predetermined table that don't need to
make the table part of the transcript at all.

\subsubsection{Argument Routing}\label{argument-routing}

The job of the argument routing functionality is to enforce the
equalities that should exist among arguments of different claims, and
the public arguments of the block.

As the basic constraints of the zkVM style machine operate between
adjacent rows, the natural way to implement this is ``register style'',
with some auxiliary ``register'' columns that hold copies of values, and
selector columns that enable equalities between various argument and
register positions, and the control column for loading the argument
values.

In this style at a bare minimum there must be enough register columns to
hold all the live values which are not in argument (or control) columns
on that row.

There are many possible design choices for exactly what routing to
support, and also a single selector could enforce a collective operation
like shifting values along a set of registers.

Unlike hardware-based intuitions, preserving the value in a register
column from one row to the next is just as much an equality constraint
as any other. Also, value lifetimes in blocks probably don't look much
like register lifetimes in conventional register allocation, unless the
block definitions look less like derivation rules and more like

\begin{verbatim}
foo(X,Y,Z) -: A1==X+Y, A2==A1+Y, A3==A2+A1, Z==A3+A2
\end{verbatim}

Yet further, having a zero-one selector column is just as
expensive as a register column (the values will not be small after the
interpolation and evaluation on a disjoint domain that STARK uses), so
it is probably not worth trying to add selectors for fancy operations to
try to save registers.

All this suggests starting with a simple register design, and seeing how
expensive it is on realistic block sets.

\paragraph{Simple Register Design\\}\label{simple-register-design}

In this simple register design, we will just reserve enough register
columns that all the arguments that appear in more than one claim of the
block will be copied on every row, rather than needing more selectors to
modulate what is copied.

Most selectors will just control copies between the argument positions
and the register columns on the same row. If we are not restricted to
degree 2 constraints, we can select among \texttt{k} rows with
\texttt{lg\ k} selectors per argument, using terms like
\texttt{(arg\_i\ -\ reg\_j)*s\_a(1-s\_b)*s\_c}, which enforces that
argument \texttt{i} equal register \texttt{j} only if selector
\texttt{a} is set, \texttt{b} unset, and \texttt{c} set.

We also need to reserve some binary combinations for setting the
argument to zero and for leaving it unconstrained, so take \texttt{k} a
bit less than a power of two or have an extra selector.

For loading the block's public arguments into the registers the simple
design is to have an additional set of \texttt{lg\ k} selectors. A trick
that probably makes manual register allocation excessively confusing
reduces that to one selector. Just write the constraints that copy
register values into the next row (unless we are at the end of the
block) so that the values are copied with a cyclic shift. Then loading
arguments only needs a single selector for copying the control column
into the first register.

\paragraph{By Permutation\\}\label{by-permutation}

At least as early as PlonK, systems mapping gates of a circuit onto rows
or blocks of a table have used permutations to enforce non-local
equalities. The idea is to define a permutation over the cell locations
whose cycles are the desired equivalence classes, and check that the
list of cell values is unchanged by applying the permutation.

A specific permutation can be applied using a multi-column (arbitrary)
permutation constraint, by fixing the values in extra columns of
``tags'' on each side of the permutation. Often values are chosen so a
simple constraint like next(X) = X+1 or next(X) = wX suffices to fix the
output tag column.

To apply this for claim arguments, we will cost two index columns per
argument column, and a column for the permutation accumulator. The
permutation is block local, so there will also need to be a column
holding a block ID (this might have other applications).

We may need to consider each tag an independent value in the block
fingerprint.
If the indices could be constrained to small values we
could use a constraint like
\texttt{compressed\_indices\ ==\ index1\ +\ 16*index2\ +\ 16\^{}2*index3}
to summarize multiple 0..15 values in a single field,
but constraining the values would require either a range check or
an excessively high-degree constraint like
\texttt{(index1-0)*(index-1)*..*(index1-15)}.

\subsubsection{Example Block Tabulations}\label{example-block-tabulations}

This section shows how some block rules from the propositional logic example in
\cref{block-model-example-propositional-logic} would be laid out
in an AIR transcript according to the preceding implementation strategy.

We allocate columns for relations with up to three arguments, the
minimum to support the widest relations in the example such as
\texttt{instantiation} and \texttt{subst\_lookup}.
We use the simple register model, and write the tabulation of each
block rule using only as many register columns as that example needs,
in a fully concrete implementation this would leave unused columns.
We assume that the selectors for populating arguments allow setting
the argument to a fixed value 1, a fixed value 0, or leaving it
unconstrained, in addition to copying any register.

Nine register columns suffice for all blocks. The propositional axioms are
the most complicated, but other rules would still require seven register
columns even if the propositional axiom rules were removed (forcing the
axioms to be asserted in the public part of a transcript instead).

\begin{verbatim}
assert(T,k): SETUP
  proved(T,k) -: wf_term(T,_)
\end{verbatim}

\noindent
\begin{tabularx}{\textwidth}[]{@{}l l l l l l Y@{}}
\toprule
Control & R1 & R2 & Claim & Arg1 & Arg2 & Selectors \\
\midrule
\texttt{\textless{}assert\textgreater{}} & \texttt{T} & \texttt{k} &
\texttt{\textless{}proved\textgreater{}} & \texttt{T} & \texttt{k} &
Block\_Start, Setup, Arg1=R1, Arg2=R2, Emit \\
\texttt{T} & \texttt{T} & \texttt{k} &
\texttt{\textless{}wf\_term\textgreater{}} & \texttt{T} & X &
Control=R1, Demand, Arg1=R1, Arg2=Free \\
\texttt{k} & \texttt{T} & \texttt{k} & 0 & 0 & 0 & Block\_End,
Control=R2 \\
\bottomrule
\end{tabularx}
\smallskip

The value X corresponds to the \texttt{\_} in the block definition. It
does not have to equal any other claim arguments, so it is not in any
registers, but to construct a valid witness the prover will have to
choose a depth that lets the claim lookup succeed.

In \texttt{modus_ponens} we see a possible elaboration of depth checking.

\begin{verbatim}
modus_ponens(T):
  proved(TB,k) -:
    is_impl(T,TA,TB), proved(T,k1), proved(TA,k2),
    k == 1+max(k1,k2)
\end{verbatim}

\noindent
\begin{tabularx}{\linewidth}[]{@{}l l l l Y@{}}
\toprule
Control & R1-R6 & Claim & Arg1-3 &Selectors \\
\midrule
\texttt{modus\_ponens} & T, TA, TB, k, k1, k2 &
\texttt{\textless{}proved\textgreater{}} & TB, k, 0 & Block\_Start,
Arg1=R3, Arg2=R4, Emit \\
\texttt{T} & T, TA, TB, k, k1, k2 &
\texttt{\textless{}is\_impl\textgreater{}} & T, TA, TB & Arg1=R1,
Arg2=R2, Arg3=R3, Demand \\
& T, TA, TB, k, k1, k2 & \texttt{\textless{}proved\textgreater{}} &
T, k1, 0 & Arg1=R1, Arg2=R5, Demand \\
& T, TA, TB, k, k1, k2 & \texttt{\textless{}proved\textgreater{}} &
TA, k2, 0 & Arg1=R2, Arg2=R6, Demand \\
& T, TA, TB, k, k1, k2 & \texttt{\textless{}depthLt\textgreater{}}
& k1, k, 0 & Arg1=R5, Arg2=R4, Demand \\
& T, TA, TB, k, k1, k2 & \texttt{\textless{}depthLt\textgreater{}}
& k2, k, 0 & Block\_End, Arg1=R6, Arg2=R4, Demand \\
\bottomrule
\end{tabularx}
\smallskip

The \texttt{subst\_not\_here} block demonstrates the primitive
inequality constraint.

\begin{verbatim}
subst_not_here(V,S):
  not_in_subst(V,S)
  -: is_single_subst(S,V1,T),
     V != V1.
\end{verbatim}

Inequality takes an advice value. X should be set to \texttt{1/(V-V1)}
(the constraint checks \texttt{1\ ==\ (Arg1-Arg2)*Arg3}).

\noindent
\begin{tabularx}{\textwidth}[]{@{}l l l l Y@{}}
\toprule
Control & R1-R3 & Claim & Arg1-3 & Selectors \\
\midrule
\texttt{subst\_not\_here} & V, S, V1 & \texttt{not\_in\_subst} & V, S, 0 & Block\_Start, Arg1=R1, Arg2=R2, Emit \\
V & V, S, V1 & \texttt{is\_single\_subst} & S, V1, T & Arg1=R2,
Arg2=R3, Arg3=Free, Demand \\
S & V, S, V1 & 0 & V, V1, X & Block\_End, Arg1=R1, Arg2=R3,
Arg3=Free, NotEqual \\
\bottomrule
\end{tabularx}
\smallskip

The \texttt{def\_term\_impl} block demonstrates unique claims.

\begin{verbatim}
def_term_impl(T,TA,TB):
  is_impl(T,TA,TB),
  UNIQUE wf_term(T), wf_term(T,k)
  -: wf_term(TA,ka), wf_term(TB,kb),
     k == 1+max{ka,kb}.
\end{verbatim}

\noindent
\begin{tabularx}{\textwidth}[]{@{}l l l l Y@{}}
\toprule
Control & R1-R6 & Claim & Arg1-3 & Selectors \\
\midrule
\texttt{def\_term\_impl} & T, TA, TB, k, ka, kb &
\texttt{\textless{}is\_impl\textgreater{}} & T, TA, TB & Block\_Start,
Arg1=R1, Arg2=R2, Arg3=R3 Emit \\
\texttt{T} & T, TA, TB, k, ka, kb &
\texttt{\textless{}wf\_term\textgreater{}} & T, k, 0 & Control=R1,
Arg1=R1, Arg2=R4, Emit, Unique \\
\texttt{TA} & T, TA, TB, k, ka, kb &
\texttt{\textless{}wf\_term\textgreater{}} & TA, ka, 0 & Control=R2,
Arg1=R2, Arg2=R5, Demand \\
\texttt{TB} & T, TA, TB, k, ka, kb &
\texttt{\textless{}wf\_term\textgreater{}} & TB, kb, 0 & Control=R3,
Arg1=R3, Arg2=R6, Demand \\
& T, TA, TB, k, ka, kb & \texttt{\textless{}depthLt\textgreater{}}
& ka, k, 0 & Arg1=R5, Arg2=R4, Demand \\
& T, TA, TB, k, ka, kb & \texttt{\textless{}depthLt\textgreater{}}
& ka, k, 0 & Block\_End, Arg1=R6, Arg2=R4, Demand \\
\bottomrule
\end{tabularx}
\smallskip

The \texttt{smallPosNext} block uses addition and loading 1.
Alternatively the machine's register design might allow loading 1+Reg1
(or 1+Regi for a limited set of registers). If that was an additional
option for every register it would obviously cost an extra selector, but
picking among nine registers with binary selectors requires four bits
and we haven't used all 16 codes.

\begin{verbatim}
smallPosNext(k):
  smallPos(k) -: smallPos(k0), k == k0 + 1
\end{verbatim}

\noindent
\begin{tabularx}{\textwidth}[]{@{}l l l l Y@{}}
\toprule
Control & R1,R2 & Claim & Arg1-Arg3 & Selectors \\
\midrule
\texttt{smallPosNext} & k, k0 &
\texttt{\textless{}smallPos\textgreater{}} & k, 0, 0 & Block\_Start,
Arg1=R1, Emit \\
\texttt{k} & k, k0 & \texttt{\textless{}smallPos\textgreater{}} & k0, 0, 0
& Control=R1, Arg1=R2, Demand \\
& k, k0 & 0 & k, k0, 1 & Block\_End, Arg1=R1, Arg2=R2, Arg3=1,
Addition \\
\bottomrule
\end{tabularx}

\subsection{Related Work on Proof Checking in ZK}

In this section, we recall three recent proof checking approaches and compare them with our block model proposed solution.

ZKSMT \cite{zksmt} is a system for creating ZK proofs of Satisfiability Modulo Theories (SMT) validity proofs. It is based on existing zkVM design, but
specialized for checking proofs made up of a collection of proof steps instead of executing programs made up
of sequences of instructions, which enables performance optimizations that would not be available in a
general-purpose zkVM. This includes storing the list of referenced expressions and the list of proof steps in
read-only memory tables, which enables a more efficient memory consistency check.

zkPi \cite{zkpi} is a system for creating succinct zero-knowledge proofs of Lean proofs. zkPi works somewhat similarly to
ZKSMT, but supports a more expressive proof system based on dependent type theory.

Both of these systems make multiple ROM accesses per proof step, because it is necessary to load, e.g.,
premises of a proof step to check that the step is well-formed. This is limiting, and in the case of zkPi, prevents the system from completing 54\
require more memory to generate the ZK proof the longer the math proof is.
In our design we greatly reduce maximum memory usage by splitting proofs into 
segments and then folding these segments together as part of the final ZK proof.

The ZKSMT paper included results of an experiment which is roughly analogous to our experiment with implementing
Metamath proof checking in various off-the-shelf zkVMs. As a baseline to compare to ZKSMT, they implemented
the same algorithm in C++, converted it to ZK circuit using Cheesecloth
\cite{cuéllar2023cheeseclothzeroknowledgeproofsrealworld}, and used a system
called Diet Mac'N'Cheese as the ZK backend, which, like ZKSMT, uses a VOLE-based ZK system. They found an about 3000x
speedup for ZKSMT over this zkVM-like setup. This suggests that specialized ZK machinery for proof checking can be 
much more efficient than going through a zkVM.

In the direction of theories with less power, Luo et al. \cite{zkunsat} construct a system for proving unsatisfiability (UNSAT) in a zero-knowledge system. This system, which is a basic NP-Complete language, does not rise to the level of a fully featured formal system. Nevertheless, the ZK proof system constructed for it has some features in common with the above. For example, it also identifies a collection of possible proof steps, in this case, the logic of resolution proofs.

\section{Conclusion}

\emph{Proof of Proof} is a novel correctness approach proposed and implemented by \href{https://pi2.network}{Pi Squared}, which combines formal mathematical proofs and cryptography in a unique way.  The main idea, which also inspired its name, is to produce a \emph{ZK Proof} of a \emph{Math Proof}.  The ZK Proof acts as a succinct and independently verifiable certificate that attests for the integrity of the Math Proof, and thus for the Claim, or the Math Theorem, that was proved by the Math Proof.  Since every Claim that is provably true can (and should) be organized and presented as a Math Theorem with a Math Proof, Proof of Proof is therefore meant to serve as the ultimate approach to verifiable truth.

In this paper, we presented an instance of the general Proof of Proof approach, where the truths are program execution claims: the ZK proof represents a Math Proof that certifies that a given program executed correctly according to its programming language's or virtual machine's formal semantics.  Specifically, the presented Proof of Proof instance is based on the following key components:
\begin{itemize}
\item \K -- a \emph{universal framework for programming languages}, where the formal semantics of a programming language is defined as a Matching Logic theory and an Interpreter for that language can be automatically derived;
\item \emph{Math Proof Generation (MPG)}, a mechanism that generates Math Proofs for program executions, based on traces produced by the Interpreter; 
\item \emph{Proof Checker}, a simple and small program which ensures that the Math Proofs (and thus also \K and the Interpreter) are \textit{not trusted but verified}, providing the strongest correctness argument, with the smallest trust base ever reported or recorded, for the Math Proofs derived from computations;
\item \emph{ZK Proof Generation}, which utilizes Zero-Knowledge (ZK) proof technology to reduce the size of the mathematical proofs, showing only that such mathematical proofs exist, which is sufficient for many/most applications.
\end{itemize}
To summarize, the Proof of Proof instance presented in this paper is therefore:
\begin{itemize}
\item[\checkmark] \textbf{Universal}: There is a single language for the math proofs, which works with all programs written in all programming or virtual machine languages.
\item[\checkmark] \textbf{Verifiable}: The generated math proofs are verified by a simple proof checker.
\item[\checkmark] \textbf{Correct-by-construction}: The ZK proof generator acts as a massive compressor of math proofs in general, and is not specific to any programming or virtual machine language.  So we can ``plug and play'' new languages without any need to trust or formally verify anything language-specific.
\end{itemize}
We believe that Proof of Proof will naturally find applications in at least three domains: remote computing, blockchain, and AI.

Indeed, remote servers will be able to execute programs for their clients in any existing or future programming languages, and produce ZK proofs of correct execution along with the result produced by the program.  The clients verify the ZK proof and thus know that the result was correctly computed.  Once Proof of Proof matures as a technology, clients and remote computing providers will have no reason nor incentive to do things any other way.
Blockchains will not need to replicate program execution in thousands or even millions of nodes only because some of them may cheat on what the computation does. Finally, AI model inference will be verifiable as well, for our peace of mind.

Perhaps some of the most interesting applications of Proof of Proof will be those that go beyond what verifiable computing alone can do.  Specifically, applications in which we combine various methods to obtain mathematical proofs.  For example, a formally verified program provides mathematical guarantees that certain properties of interest hold.  Those properties can then be taken into account (as lemmas) to produce smaller and/or more comprehensive proofs of correct execution, and thus faster and more trusted verifiable computing end-to-end.  We experimented with this approach with a formally verified variant of the square root function in Uniswap, reducing its ZKP generation and verification to constant time --- indeed, the math proof resulting from the formal verification of \code{sqrt} that it implements the square root function is done once and for all, and then reused as a lemma when computing, eg, \code{sqrt(100) = 10}.

Even more interesting, the program that produced the computation is not even required to be public, provided that it is formally verified for compliance with publicly available specifications or requirements.  Indeed, from the math proof produced by the formal verification of the program and the math proof produced by the execution of the program, we can construct a math proof of the claim that ``there exists a program that is compliant, whose execution produced this result''.  This is sufficient in many / most cases for users, but it can be the difference between all or nothing for companies which are willing to prove compliance but cannot make their code public. 
























































\section{Polynomial fingerprinting} 
\label{sec:polynomial-fingerprinting}

\subsection{Motivation} 
\label{pf:motivation}

As we have seen in the section dedicated to the Block Model, this principle can be more easily applied if one transforms (encodes) formulas in numbers, or - more convenient in cryptography - in the elements of a finite field. It would be even better if this encoding would be homomorphic for usual proof steps, like modus ponens or substitution of variables. This way, one would apply the difficult (time-consuming) encoding only for initial steps, like invocation of axioms or of tautologies, while the encodings of other formulas present in proofs would be computed from already existing encodings via homomorphic rules. 
In general, formulas arising in proofs are very long, and a proof consists of a large number of formulas. This is another reason why it is better to encode proofs homomorphically in finite field elements or at least in finite sequences of such elements. Moreover, as we will see at the end of this section, a homomorphic encoding of formulas represents already a primitive method to create zero-knowledge certificates of correctness. Unfortunately, their length depends linearly on the length of the proof expressed in number of steps. For this reason, this method must be combined with other methods, like encoding the correctness in a one-variable polynomial which must be of relatively small degree and checking this fact using a folding algorithm. Also, the fact that a formula will not be encoded in just one element of a finite field, but in a finite sequence of field elements, implies that we possibly have to use Merkle trees to handle them. Solving these two challenges remain an open problem to be later investigated.

In this section, we present a first attempt to associate to any formula an element of a finite field  (or a vector of finite field elements), in such a way that the following properties hold:
\begin{enumerate}
    \item To each formula $\varphi$ corresponds a field element (or a vector consisting of field elements) $V(\varphi)$. Also, to every well-formed term $t$, corresponds a field element (or a vector consisting of field elements) $V(t)$. 
    \item The vector $V(\varphi)$, respectively $V(t)$, contains a sub-vector $[[\varphi]]$, respectively $[[t]]$, which directly encodes $\varphi$, respectively $t$. The other elements arising in this vector are useful for performing operations which homomorphically emulate logic proof steps, like modus ponens or substitution. These elements are also sub-vectors, and they correspond to variables arising in $\varphi$, respectively in $t$. So the fingerprint looks like:
    $$V(\varphi) = ([[\varphi]], [[\varphi]]_{x_1}, \dots , [[\varphi]]_{x_k}).$$
    \item There is an arithmetic term $MP(a, b)$ with the following property. If a formula $\varphi_3$ is the result of applying the rule modus ponens to formulas $\varphi_1$ and $\varphi_2$, then $V(\varphi_3) = MP(V(\varphi_1), V(\varphi_2))$. 
    \item There is an arithmetic term $Subst_y(a, b)$ with the following property. If a formula $\varphi_3$ is the result of the substitution of the variable $y$ occurring in the formula $\varphi_1$ with the formula $\varphi_2$, then $V(\varphi_3) = Subst_y(V(\varphi_1), V(\varphi_2))$. Also, if a formula $\varphi_3$ is the result of the substitution of the variable $y$ occurring in the formula $\varphi_1$ with the term $t$, then $V(\varphi_3) = Subst_y(V(\varphi_1), V(t))$.
\end{enumerate} 

We call the vactor $V(\varphi)$ the {\bf fingerprint} of $\varphi$. 

The definition above is for the time being just a declaration of intentions. This intentions must be completed with some other conditions, as follows:

\begin{itemize}
 \item The algorithm should not depend on the particular finite field $\mathbb F_p$ which is chosen.

 \item Different formulas must map on different elements, at least if the characteristic $p$ is sufficiently large. 

 \item  For axioms $\varphi$, the computation of $V(\varphi)$ is fast.

 \item  For given values of $V\varphi_1)$ and $V(\varphi_2)$, the computation of $$MP(V(\varphi_1), V(\varphi_2))$$ is fast.

 \item  For given values of $V(\varphi_1)$ and $V(\varphi_2)$, the computation of $$Subst_y(V(\varphi_1), V(\varphi_2))$$ is fast. 
\end{itemize}

We will follow the following strategy. We consider a non-commutative ring of $2 \times 2$ matrices over the ring $R = \mathbb Z[X_1, X_2, \dots]$, which is the ring of polynomials with infinitely many variables. We make a first correspondence between formula and terms:
$$\varphi \leadsto [\varphi] \in M_{2 \times 2}(R),$$
respectively
$$t \leadsto [t] \in M_{2 \times 2}(R),$$
satisfying the Unique Encoding Property, which says that some element $A \in M_{2 \times 2}(R)$ {\bf corresponds to at most one well-formed string, being a formula or a term}. 

For this encoding, we define the symbolic fingerprint $$F(\varphi) = ([\varphi], [\varphi]_{x_1}, \dots, [\varphi]_{x_1}),$$
and analogous for terms. The matrices $[\varphi]_{x_i}$ are necessary only for computing substitutions, but they must be updated also during the modus ponens steps.  Please remark that we use the notation $F(\varphi)$ for a finite sequence of matrices over polynomials, while $V(\varphi)$ is a finite sequence of matrices over a finite field $\mathbb F$. We obtain $V(\varphi)$ from $F(\varphi)$ by evaluating the polynomial variables in randomly chosen field elements, as it will be specified below. 

The arithmetic terms $MP(a, b)$, respectively $Subst_y(a, b)$, work already in the ring $M_{2 \times 2}(R)$. 

Now, for a random choice of values $X_1 = r_1, X_2 = r_2, \dots \in \mathbb F_p$, we evaluate the entries of the $2 \times 2$ matrices, and we get $2 \times 2$ matrices over $\mathbb F_p$. In conclusion, modulo evaluation of the entries, the non-injective encoding of the mathematical proof in a sequence of matrices is given by:
$$\varphi \leadsto [\varphi] \in M_{2 \times 2}(\mathbb Z[X_1, X_2, \dots]) \leadsto [[\varphi]] \in M_{2\times 2}(\mathbb F_p).$$
This leads to the following {\bf primitive Zero Knowledge Proof} procedure: 
\begin{itemize}
\item Consider a mathematical proof $P$, with conclusion $\psi$.

\item Choose values $X_1, X_2, \dots \in \mathbb F_p$.

\item Compute $\alpha_1 = [[\psi]]$ using the encoding rules.

\item For all axioms $a$ occurring in $P$, compute the corresponding fingerprints $V(a)$ using the encoding rules.

\item For all formulas $\varphi$ occurring in $P$, which are not axioms, compute $V(\varphi)$ by using the homomorphic properties $MP(a, b)$ respectively $Subst_y(a, b)$ for appropriated choices of $y, a, b$.

\item The last of these computations produces $\alpha_2=[[\psi]]$. Observe that the method to compute $\alpha_2$ differs from the method to compute $\alpha_1$. While $\alpha_1$ was computed by directly encoding $\psi$, $\alpha_2$ was computed starting from the axioms and following the homomorphic properties of the proof steps.

\item Check whether $\alpha_1 = \alpha_2$ and accept if this is true, respectively reject, if not. 
\end{itemize} 

This {\bf primitive Zero Knowledge procedure} works grace to the Theorem of Schwartz and Zippel:

\begin{theorem}
    Let $\mathbb F$ be a finite field and let $f \in \mathbb F[x_1, \dots, x_n]$ be a non-zero polynomial of degree $d \geq 0$. If $r_1, r_2, \dots, r_n$ are selected randomly and independent in $\mathbb F$, then:
    $$ Pr[f(r_1, r_2, \dots, r_n) = 0] \leq \frac{d}{|\mathbb F|}.$$
\end{theorem} 

The Schwartz and Zippel Theorem is applied as follows. The Theorem says that for a polynomial which is not identic zero, the probability that a random evaluation is zero in a big finite field is reasonably small. Let again $\varphi$ be the conclusion of the mathematical proof. Let $F_1 \in M_{2 \times 2} (\mathbb Z [X_1, X_2, \dots]) $ the polynomial matrix obtained by direct encoding. Let $F_2 \in  M_{2 \times 2} (\mathbb Z [X_1, X_2, \dots])$ be obtained from the encoding of the axioms using the proof steps and their homomorphic properties. We want to prove with high confidence that $F_1 = F_2$ as multivariate polynomials. To this sake, we just compute their evaluations $\alpha_1$ and $\alpha_2$, where $\alpha_2$ is computed from evaluations of the axioms and using homomorphic properties. If the field is sufficiently large, the equality $\alpha_1 = \alpha_2$ means that, with high probability, $F_1 = F_2$, so the formula resulted from the proof is indeed identical with the claimed conclusion, which has been directly encoded.

This primitive Zero Knowledge procedure has the disadvantage that its length is equal with the length of the proof. {\bf This procedure must be combined with zero-knowledge proof methods for arithmetic circuits, folding methods, etc}, in order to produce ZK-certificates of constant length. However, as it is an essential intermediate step toward arithmetization, we will describe a possibility to achieve such an encoding in the following subsections.


\subsection{Matrices of multivariate polynomials}\label{storysimp} 

The original observation which led to this subsection was that matrices consisting of different variables:
$$ A(k) = \begin{pmatrix}
    x_{4k+1} & x_{4k+2} \\ x_{4k+3} & x_{4k+4}
\end{pmatrix}$$
are non-commutative to such extent that if two products are equal: 
$$A(i_1)\dots A(i_n) = A(j_1) \dots A(j_m)$$
then $n = m$ and $i_1 = j_1$, $\dots$, $i_n = j_n$. This means that such a monomial (product of elementary matrices) contains information about the number of factors, their order, and their identity. All three elements of information are essential to encode a path inside a tree.

However, proceeding with such matrices would be expensive because one has to choose four field elements to evaluate every elementary matrix and to keep four elements for every matrix to be kept as part of a fingerprint. Instead, we present a system of elementary matrices that achieves the same goal, but needs just one field element to be evaluated and only three field elements for every matrix which is part of a fingerprint. 

\begin{definition}\label{defmatrixvar}
    Let $x_1$ be a variable, that is, some element which is transcendental over $\mathbb Q$. Let:
    $$A(x_1) = \begin{pmatrix}
        x_1 & 1 \\ 0 & 1
    \end{pmatrix}$$
    We consider that $A(x_1) \in M_{2 \times 2}(\mathbb Z[x_1, x_2, \dots])$. 
\end{definition} 

We show now that these elementary matrices fulfill the same property: a monomial contains enough information to uniquely determine the number of elementary matrices, their order and their identities.

\begin{lemma}\label{lemmamatrix}
    Consider a set of different variables $V = \{x_1, x_2, \dots, x_k\}$. Suppose that $0 \leq i_1, \dots, i_n, j_1, \dots, j_m \leq k$. If:
    $$A(x_{i_1}) A(x_{i_2}) \dots A(x_{i_n}) = A(x_{j_1}) A(x_{j_2}) \dots A(x_{j_m}).$$
    Then the following equalities take place: $n = m$, $i_1 = j_1$, $\dots$, $i_n = j_n$.
\end{lemma}

\begin{proof}
    If in this identity, we set $x_1 = \dots = x_k = 1$, as we observe that:
    $$\begin{pmatrix}
        1 & n-1 \\ 0 & 1
    \end{pmatrix}
    \begin{pmatrix}
         1 & 1 \\ 0 & 1
    \end{pmatrix} = 
    \begin{pmatrix}
        1 & n \\ 0 & 1
    \end{pmatrix},$$
    we get that $n = m$. 
    Let us denote with $S(n)$ the statement: {\it If
     $$A(x_{i_1}) A(x_{i_2}) \dots A(x_{i_n}) = A(x_{j_1}) A(x_{j_2}) \dots A(x_{j_n})$$
    then $i_1 = j_1$, $\dots$, $i_n = j_n$.}
    We observe that $S(1)$ is evident by identifying the entries. Suppose that we have proved $S(n)$. We look at the hypothesis of $S(n+1)$:
    $$A(x_{i_1}) A(x_{i_2}) \dots A(x_{i_{n+1}}) = A(x_{j_1}) A(x_{j_2}) \dots A(x_{j_{n+1}}).$$
    We observe by induction that:
    $$A(x_{i_1}) A(x_{i_2}) \dots A(x_{i_n}) = 
    \begin{pmatrix}
        x_{i_1}x_{i_2} \dots x_{i_n} & P(x_{i_1}, x_{i_2}, \dots, x_{i_{n-1}}) \\ 0 & 1
    \end{pmatrix},
    $$ where $P(z_1, \dots, z_{n-1}) \in \mathbb Z[z_1, \dots, z_{n-1}]$ is a fixed polynomial, {\it with the property that no variable $z_i$ divides $P$}. We write the hypothesis of induction in the form:
    $$
    \begin{pmatrix}
        x_{i_1} & 1 \\ 0 & 1
    \end{pmatrix}
    \begin{pmatrix}
        x_{i_2}x_{i_3} \dots x_{i_{n+1}} & P(x_{i_2}, x_{i_3}, \dots, x_{i_{n}}) \\ 0 & 1
    \end{pmatrix} = $$$$ =
    \begin{pmatrix}
        x_{j_1} & 1 \\ 0 & 1
    \end{pmatrix}
    \begin{pmatrix}
        x_{j_2}x_{j_3} \dots x_{j_{n+1}} & P(x_{j_2}, x_{j_3}, \dots, x_{j_{n}}) \\ 0 & 1
    \end{pmatrix},
    $$ 
     so:
     $$
      \begin{pmatrix}
        x_{i_1} x_{i_2}x_{i_3} \dots x_{i_{n+1}} & 1 + x_{i_1} P(x_{i_2}, x_{i_3}, \dots, x_{i_{n}}) \\ 0 & 1
    \end{pmatrix} = $$$$ =
      \begin{pmatrix}
        x_{j_1} x_{j_2}x_{j_3} \dots x_{j_{n+1}} & 1 + x_{j_1} P(x_{j_2}, x_{j_3}, \dots, x_{j_{n}}) \\ 0 & 1
    \end{pmatrix}.
     $$
     We identify the corresponding entries:
     \begin{eqnarray*}
          x_{i_1} x_{i_2}x_{i_3} \dots x_{i_{n+1}} &=& 
           x_{j_1} x_{j_2}x_{j_3} \dots x_{j_{n+1}}, \\
           1 + x_{i_1} P(x_{i_2}, x_{i_3}, \dots, x_{i_{n}}) &=&
           1 + x_{j_1} P(x_{j_2}, x_{j_3}, \dots, x_{j_{n}}).
     \end{eqnarray*} 
     We apply the property that no variable $z_i$ divides $P$. By variable identification we get $x_{i_1} = x_{j_1}$. We multiply the hypothesis with $A(x_{i_1})^{-1}$ from the left-hand side. We get an instance of $S(n)$ and we apply the induction hypothesis. Of course  $A(x_{i_1})^{-1}$ does not belong to the matrices over polynomials, but to the matrices over rational functions. It is just important that one can simplify with $A(x_i)$. 
\end{proof}

\subsection{Non-commutative edge variables in trees}\label{treesandpolynomials} 

 The goal of this section is to show how to further associate a matrix to a formula represented by a tree using the previous construction.

 Below, by {\bf edge variable} we understand an elementary matrix of the shape:
 $$X_i = \begin{pmatrix}
     x_i & 1 \\ 0 & 1
 \end{pmatrix}.$$
 To every edge of the tree, and to every vertex, we will associate such a matrix. 

In order to represent formulas by trees, both logical and term-building operations are represented as vertices of the tree. For every specific symbol $c$ of arity $d=d(c)$ a number of $d + 1$ different edge variables $C, C_1, \dots, C_d$ are associated. 

Suppose that a tree $T$ has root $c$ and the sub-trees connected with $c$ are $T_1, \dots, T_d$. Suppose that one already associated matrices $$[T_1], \dots, [T_d] \in M_{2 \times 2}(\mathbb Z[X_1, X_2, \dots])$$ with these sub-trees. Then we associate with $T$ the pair:
$$[T] = A(C) + A(C_1) [T_1] + \dots + A(C_d) [T_d].$$


\begin{definition}
    If $\varphi$ is a formula or a term, let $[\varphi]$ denote the matrix of polynomials associated with its tree. 
\end{definition}

\begin{theorem}
    A matrix represents at most one formula.
\end{theorem}

{\bf Proof}: We show this working out a simplistic example. Consider the following inductive definition:
\begin{enumerate}
    \item The letters $x$, $y$, $z$ are atomic propositional formulas.
    \item If $\varphi$ and $\psi$ are formulas, then:
    $$\neg\,\varphi,\,\, \varphi \rightarrow \psi, $$
    are formulas.
\end{enumerate}
 
The alphabet is $A = \{x, y, z, \neg, \rightarrow \}$. 

The variables $x, y, z$ are symbols of arity $0$ and will always be final nodes. We associate them with the matrices:
$$
[x] =  A(X) = \begin{pmatrix}
    X & 1 \\ 0 & 1
\end{pmatrix},\,\,\,\,
[y] = A(Y) = \begin{pmatrix}
    Y & 1 \\ 0 & 1
\end{pmatrix},\,\,\,\,
[z] = A(Z) = \begin{pmatrix}
    Z & 1 \\ 0 & 1
\end{pmatrix}.
$$

The symbols with positive arity are $\{\neg, \rightarrow\}$. We associate with $\neg$ the matrices:
$$
A(N) = \begin{pmatrix}
    N & 1 \\ 0 & 1
\end{pmatrix},\,\,\,\,
A(N_1) = \begin{pmatrix}
    N_1 & 1 \\ 0 & 1
\end{pmatrix}.
$$
We associate with $\rightarrow$ the matrices:
$$
A(I) = \begin{pmatrix}
    I & 1 \\ 0 & 1
\end{pmatrix},\,\,\,\,
A(I_1) = \begin{pmatrix}
    I_1 & 1 \\ 0 & 1
\end{pmatrix},\,\,\,\,
A(I_2) = \begin{pmatrix}
    I_2 & 1 \\ 0 & 1
\end{pmatrix}.
$$
The $7$ variables $X, Y, Z, N, N_1, I, I_1, I_2$ are pairwise different.

The inductive steps are given by:
    $$[\neg \,\alpha] = A( N) + A(N_1) [\alpha],$$
    $$[\alpha \rightarrow \beta] = A(I) + A(I_1) [\alpha] + A(I_2) [\beta], $$
The statement of the Theorem is proved by induction over the building rules for formulas. What we really prove is the equivalent statement: {\it Every formula is encoded by only one matrix of polynomials}.  If $\varphi$ is an atomic propositional symbol, then $[\varphi]$ is $[x]$,  $[y]$ or $[z]$ and so from $[\varphi] = [\varphi']$ follows immediately $\varphi = \varphi'$. Suppose that $\varphi = \neg \, \alpha$. Then:
$$[\varphi] = A(N) + A(N_1) [\alpha].$$
We observe that $A(N)$ is the only one monomial of degree one present here. So one can conclude that we are reading a negation. All other monomials start with $A(N_1)$ because, as shown in Lemma \ref{lemmamatrix}, all these non-commutative monomials can start only with $A(N_1)$. Now, by the induction hypothesis, the formula $\alpha$ is uniquely encoded by $[\alpha]$, and it follows that $\varphi$ is uniquely encoded by $[\varphi]$. 

Now we consider the case $\varphi = \alpha \rightarrow \beta$. We have seen that: 
$$[\varphi] = A(I) + A(I_1) [\alpha] + A(I_2) [\beta].$$
Again $A(I)$ is the only one monomial of degree one and its presence shows that we are reading an implication. All other monomials have the shape $A(I_1) B$ or $A(I_2)B$. By the unicity of products of elementary matrices (Lemma \ref{lemmamatrix}), this monomials can start only with $A(I_1)$ or with $A(I_2)$. By common factor, we get the expression $A(I_1) [\alpha] + A(I_2) [\beta]$. As by induction hypothesis the formulas $\alpha$ and $\beta$ are uniquely expressed by the polynomial matrices $[\alpha]$, respectively $[\beta]$, it follows that $\varphi$ is uniquely expressed by the matrix of polynomials $[\varphi]$. 
\qed

\subsection{Homomorphic properties} 

In this subsection we define the notion of fingerprint of a formula and we show that this notion enjoys homomorphic properties of the operations with formulas used in proofs: modus ponens and substitution. We show how the fingerprint of a formula produced by modus ponens can be computed from the fingerprints of the arguments of the operation modus ponens. Also we show how the fingerprint of a formula obtained by substitution can be computed from the fingerprints of the formula in which the variable has been substituted and the fingerprint of the formula (or term) which has substituted this variable. 

Suppose that three different lines of a proof read:
\begin{eqnarray*}
    \varphi \,\,\,\,\,\,\,\,\,\,\,\,\,\,\\
    \varphi \rightarrow \psi \\
    ---\\
    \psi
\end{eqnarray*}
such that the formula $\psi$ is deduced from the formulae $\varphi$ and $\varphi \rightarrow \psi$ by modus ponens. Suppose that we equip the implication symbol $\rightarrow$ with three matrices $A(I)$, $A(I_1)$ and $A(I_2)$ such that:
$$[\varphi \rightarrow \psi] = A(I) + A(I_1) [\varphi] + A(I_2)[\psi].$$
Then one can compute the conclusion as follows:
$$[\psi] = {A(I_2)}^{-1} \left ([\varphi \rightarrow \psi] - A(I) - A(I_1)[\varphi]\right ).  $$ 

Substitution also enjoys a homomorphic property. Suppose that one has a formula $\varphi(x)$ and substitutes $x$ with a tree $[\psi]$ corresponding to a formula or a term. We observe that:
$$[\varphi(x)] = \sum_{\text{nodes }c} A(X_{i_1})\dots A(X_{i_n}) \cdot A(X_c).$$
Here for every node $c$, the monomial $A(X_{i_1})\dots A(X_{i_n})$ consists of the edge-variables on the path from the root to the node $c$. If two such nodes are marked with $x$ and are to be substituted, one has:
$$[\varphi(x/\psi)] = [\varphi(x)] - A(X_{i_1})\dots A(X_{i_n})  [x] - A(X_{j_1})\dots A(X_{j_m}) [x] +$$ $$+ A(X_{i_1})\dots A(X_{i_n}) [\psi] + A(X_{j_1})\dots A(X_{j_m})[\psi].$$
In general, let $x \in A$ be a variable, and let $X$ be the polynomial variable associated to this symbol of arity $0$. Let $\varphi$ be a formula or a term. We denote by:
$$\sum _{c = x} A(X_{i_1})\dots A(X_{i_n}) \cdot A(X_c) := [\varphi]_x \cdot A(X_c).$$
It follows that in general for every formula or term $\psi$,
$$[\varphi(x/\psi)] = [\varphi] - [\varphi]_x \cdot A(X) + [\varphi]_x \cdot [\psi]. $$ 
Observe that the matrix $[\varphi]_x$ has been implicitly defined in the precedent formula. 

\begin{definition}\label{deffingerprint}
Let $\varphi$ be a well-formed expression over $A$, i.e. a term or a formula. Suppose that $x_1, \dots, x_k$ are the free variables in $\varphi$. We call the fingerprint of $\varphi$ the tuple:
$$([\varphi], [\varphi]_{x_1}, \dots, [\varphi]_{x_k}).$$
We denote the fingerprint of $\varphi$ with $F(\varphi)$.
\end{definition} 

Observe that, as we announced in Subsection \ref{pf:motivation}, we will deal with two kinds of fingerprints. To a string $\varphi$ which might be a formula or a term, we have defined the fingerprint consisting of a vector of matrices over the polynomial ring $\mathbb Z [X_1, X_2, \dots]$. Once we fix elements of the finite field for the variables, say $X_1 = r_1$, $\dots$, $X_k = r_k$, the fingerprint can be evaluated in these values, and becomes a vector of matrices over the finite field. Because of the homomorphic properties presented below, the algebraic relations between polynomial fingerprints are the same as the algebraic relations between evaluated fingerprints.  

 In the next two theorems we show that the fingerprints of the results of Modus Ponens and substitution can be computed using the fingerprints of the inputs. The proofs are simple computations and we omit them here.
 
\begin{theorem}
Suppose that formulas $\varphi$ and $\varphi \rightarrow \psi$ have fingerprints:
$$F(\varphi) = ([\varphi], [\varphi]_{x_1}, \dots, [\varphi]_{x_k}),$$
$$F(\varphi \rightarrow \psi) = ([\varphi \rightarrow \psi], [\varphi \rightarrow \psi]_{x_1}, \dots, [\varphi \rightarrow \psi]_{x_k}).$$
Then the fingerprint of $\psi$ is:
$$F(\psi) = ([\psi], [\psi]_{x_1}, \dots, [\psi]_{x_k}),$$
where:
$$[\psi] = {A(I_2)}^{-1} \left ([\varphi \rightarrow \psi] - A(I) - A(I_1)[\varphi]\right ),  $$
$$[\psi]_{x_i} = {A(I_2)}^{-1} \left ([\varphi \rightarrow \psi]_{x_i}  - A(I_1)[\varphi]_{x_i}\right ).$$
\end{theorem} 

\begin{theorem}
    Let $\varphi$ and $\psi$ be formulas or terms. Suppose that their fingerprints are: 
    $$F(\varphi) = ([\varphi], [\varphi]_{x_1}, \dots, [\varphi]_{x_k}),$$
    $$F(\psi) = ([\psi], [\psi]_{x_1}, \dots, [\psi]_{x_k}).$$
    Let $\varphi(x_i/\psi) $ be the result of the substitution of
    $x_i$ with $\psi$ and let $X_i$ be a polynomial variable such that $A(X_i)$ is associated with the $x_i$-nodes.  Then the expression:
    $$F(\varphi(x_i/\psi)) = ([\varphi(x_i/\psi)], [\varphi(x_i/\psi)]_{x_1}, \dots, [\varphi(x_i/\psi)]_{x_k})$$
    where
    $$[\varphi(x_i/\psi)] = [\varphi] - [\varphi]_{x_i} \cdot A(X_i) + [\varphi]_{x_i} \cdot [\psi], $$ 
    and, if $j \neq i$, then:
    $$[\varphi(x_i/\psi)]_{x_j} = [\varphi]_{x_j} + [\varphi]_{x_i} [\psi]_{x_j}$$
    while if $j = i$, then:
    $$[\varphi(x_i/\psi)]_{x_i} = [\varphi]_{x_i} [\psi]_{x_i}$$
\end{theorem} 

{\bf Example of a fingerprint}: Consider the formula
$$\varphi = (x \rightarrow y) \rightarrow (x \rightarrow z).$$
According to our definition, one has:
$$[\varphi] = [(x \rightarrow y) \rightarrow (x \rightarrow z)] = A(I) + A(I_1)[x \rightarrow y] + A(I_2) [x \rightarrow z] =$$
$$= A(I) + A(I_1)(A(I) + A(I_1)A(X) + A(I_2)A(Y)) +$$$$+ A(I_2)(A(I) + A(I_1)A(X)+A(I_2)A(Z)) = $$
$$= A(I) + A(I_1)A(I) + A(I_1)^2A(X) + $$$$+ A(I_1)A(I_2)A(Y) + A(I_2)A(I) + A(I_2)A(I_1)A(X) + A(I_2)^2 A(Z).$$
Also, one has:
$$[\varphi]_x = A(I_1)^2 + A(I_2)A(I_1),$$
$$[\varphi]_y = A(I_1)A(I_2),$$
$$[\varphi]_z = A(I_2)^2.$$
Finally, the fingerprint of $\varphi$ is:
$$F(\varphi) = ([\varphi], [\varphi]_x, [\varphi]_y, [\varphi]_z).$$
\begin{center}
\begin{tikzpicture}[level distance=20mm,
    level 1/.style={sibling distance=30mm},
    level 2/.style={sibling distance=20mm},
    level 3/.style={sibling distance=10mm}]
    \node {$I$}
      child {
        node {$I$}
          child {
            node {$X$}
            edge from parent
              node[left] {$I_1$}
          }
          child {
            node {$Y$}
            edge from parent
              node[right] {$I_2$}
          }
        edge from parent
          node[left] {$I_1$}
      }
      child {
        node {$I$}
          child {
            node {$X$}
            edge from parent
              node[left] {$I_1$}
          }
          child {
            node {$Z$}
            edge from parent
              node[right] {$I_2$}
          }
        edge from parent
          node[right] {$I_2$}
      };
  \end{tikzpicture}
\end{center}
\subsection{An algebra of pairs}

In this subsection we consider the possibility to encode a formula represented by a tree with just a pair of multivariate polynomials. The encoding introduced so far has the shape:
$$
\begin{pmatrix}
    P(\vec x) & Q(\vec x) \\ 0 & m
\end{pmatrix}
$$
which by random evaluation of the variables $\vec x$ in a finite field $\mathbb F$ comes to keep three field elements for any formula. We will see that we can reduce this number of field elements to two. Basically, we keep only the first row of the matrix used for the encoding method developed so far. This will change the structure of the non-commutative ring on which we are working. 

\begin{lemma}
    Let $R$ be some commutative ring with $1$. Consider the set of pairs $P(R) = R \times R$ with the following operations:
    $$(a,b) + (c,d) = (a+c, b+d),$$
    $$(a,b) \cdot (c,d) = (ac, ad+b).$$ 
    In the following lines, we often use the notation $\alpha = (a,b)$, $\beta = (c,d)$ and $\gamma = (e,f)$. 
    While $(P(R), +, -, 0)$ is a commutative group, the multiplication has the following properties: 
    \begin{enumerate}
        \item The multiplication with $0 = (0,0)$ acts as:
        $$\alpha \cdot 0 = (a,b) \cdot (0,0) = (0, b),$$
        $$0 \cdot \alpha = (0,0) \cdot (a,b) = (0,0),$$
        so the expected behavior takes place only when we multiply $0$ with some element from the right-hand side. Also, 
        $$\alpha \cdot 0 = 0 \,\,\,\,\longleftrightarrow \,\,\,\, \alpha = (a, 0). $$
        \item The element $1 = (1,0)$ is a two-sided unit:
        $$\alpha \cdot 1 = (a,b) \cdot (1,0) = (a, b) = \alpha,$$
        $$1 \cdot \alpha = (1,0) \cdot (a,b) = (a, b) = \alpha. $$
        \item The multiplication is associative. For all $\alpha$, $\beta$ and $\gamma$ one has:
        $$(\alpha \cdot \beta) \cdot \gamma = \alpha \cdot (\beta \cdot \gamma).$$  
        \item The multiplication is distributive from the right-hand side:
        $$(\beta + \gamma) \cdot \alpha = \beta \cdot \alpha + \gamma \cdot \alpha.$$
        \item The multiplication is not distributive from the left-hand side:
        $$\alpha(\beta + \gamma) = \alpha \cdot \beta + \alpha \cdot \gamma \,\,\,\, \longleftrightarrow \,\,\,\, \alpha = (a, 0). $$
        \item If $a \in R^\times$ is an invertible element, then the element $\alpha^{-1} = (a^{-1}, - a^{-1} b)$ is the two-sided inverse of $\alpha = (a, b)$. This means:
        $$\alpha \cdot \alpha^{-1} = (a,b) \cdot (a^{-1}, - a^{-1} b) = (1,0) = 1,$$
        $$\alpha^{-1} \cdot \alpha =  (a^{-1}, - a^{-1} b) \cdot (a,b) = (1,0) = 1.$$
        \end{enumerate}
        Consequently, $(P(R), +, -, \cdot,  0, 1)$ is a right hand-side ring. 
\end{lemma}

\begin{proof}
    The multiplications with $0$ and with $1$ were verified directly. For the associativity of the multiplication, observe that:
    $$\alpha \cdot \beta = (a, b) \cdot (c, d) = (ac, ad+b),$$
    $$(\alpha \cdot \beta) \cdot \gamma = (ac, ad+b) \cdot (e, f) = (ace, acf + ad + b),$$
    $$\beta \cdot \gamma = (c,d) \cdot (e,f) = (ce, cf + d),$$
    $$\alpha \cdot (\beta \cdot \gamma) = (a,b) \cdot (ce, cf + d) = (ace, acf + ad + b).$$
    For the right-hand side distributivity, we observe that:
    $$(\beta + \gamma)\cdot \alpha = (c+e, d+f) \cdot (a,b) = (ac + ae, bc + be + d + f),$$
    $$\beta \cdot \alpha + \gamma \cdot \alpha = (c,d)\cdot(a,b) +(e,f)\cdot(a,b) = (ac, bc+d) + (ae, be + f) = $$ $$ =(ac + ae, bc + be + d + f).$$
    The condition for left-hand side distributivity is given by the following computations: 
    $$\alpha \cdot (\beta + \gamma) = (a,b) \cdot (c+e, d+f) = (ac + ae, ad + af + b),$$
    $$\alpha \cdot \beta + \alpha \cdot \gamma = (a,b)\cdot(c,d) +(a,b) \cdot (e,f) = (ac, ad+b) + (ae, af+b) =$$ $$ =(ac+ae, ad + af + 2b).$$
    The two elements are equal if and only if $b=0$. 
    The multiplications with $\alpha^{-1}$ were checked directly. 
    
\end{proof} 


\begin{definition}\label{defpairvar}
    Let $x_1$ be a variable, that is, some element which is transcendental over $\mathbb Q$. Let:
    $$A(x_1) = (x_1, 1)$$
    We consider that $A(x_1) \in P(\mathbb Z[x_1, x_2, \dots])$. 
\end{definition} 

The following Lemma has almost the same proof as Lemma \ref{lemmamatrix}. The Lemma is important because again from the product of pairs, we have enough information to find out the number of pairs, their order and their identities. This is an essential step for proving that a polynomial pair encodes at most one formula. It works in the same way as for matrices. 

\begin{lemma}\label{lemmapair}
    Consider a set of different variables $V = \{x_1, x_2, \dots, x_k\}$. Suppose that $0 \leq i_1, \dots, i_n, j_1, \dots, j_m \leq k$. If:
    $$A(x_{i_1}) A(x_{i_2}) \dots A(x_{i_n}) = A(x_{j_1}) A(x_{j_2}) \dots A(x_{j_m}).$$
    Then the following equalities take place: $n = m$, $i_1 = j_1$, $\dots$, $i_n = j_n$.
\end{lemma} 

\subsection{Symbolic trees} 

In this section we show how one can associate to every formula or term represented as tree, an element of the algebra of pairs of multivariate polynomials. 

\begin{definition}\label{defsymbolictrees}
    A symbolic tree is an abstract unification of terms and formulas. A symbolic tree is a tree whose vertices are labeled with symbols of an alphabet $A$. Every symbol in $A$ has an own arity. If a node is labeled with $c \in A$, it has a number of children equal with the arity of $c$. Terminal nodes (leaves) are marked only with symbols of arity $0$. 
\end{definition} 

\begin{definition}\label{defembedding}
Let $A$ be a finite alphabet, containing both logical and non-logical constants. We suppose that $A$ contains at least one symbol of arity $d = 0$ and at least one symbol of arity $d \geq 1$. Let $T(A)$ the set of trees over $A$. Then there is an application $[\,\cdot \,] : T(A) \rightarrow P(\mathbb Z[X_1, X_2, \dots])$ defined as follows:
\begin{enumerate}
    \item To every symbol $c \in A$, of arity $d$, one associates $d+1$ new variables $C, C_1, \dots, C_d$. 
    \item If the tree $t$ consists of only one vertex (the root), which is marked with the symbol $r$ of arity $0$, then:
    $$[t] = A(R) = (R, 1) \in P(\mathbb Z[X_1, X_2, \dots]).$$
    \item If $t$ has a root $c$ of arity $d$, and the root is connected with the roots of the sub-trees $t_1, \dots, t_t$ whose values $[t_1], \dots, [t_d]$ are already defined, then:
    $$[t] = A(C) + [t_1] \cdot A(C_1) + \dots + [t_d] \cdot A(C_d).$$
\end{enumerate}
\end{definition}
We observe that, in order to make use of the right-hand side distributivity, we multiply sums with new variables $A(C_i)$ only from the right. 

The following Theorem can be proved by induction on trees:

\begin{theorem}\label{theopairsunicity}
    The application $[\,\cdot \,] : T(A) \rightarrow P(\mathbb Z[X_1, X_2, \dots])$ is one-to-one. There are no different trees $t_1 \neq t_2$ with $[t_1] = [t_2]$. 
\end{theorem} 

Now, one can follow the same recipes as for matrices, and define the finger-print of a formula, respectively the rules which allow the computation of the fingerprint of the formula obtained by Modus-Ponens, respectively by substitution. However, as we have only the right-hand side distributivity, {\bf the fingerprint contains a quantity for every occurrence of a variable in the formula, and not a quantity for every variable}. So, one has the advantage to save two field elements instead of three for every matrix, but one has the disadvantage to save a pair of elements to every occurrence of a variable instead of a pair of elements per variable. In most cases, one has to save more field elements working in this algebra. Also, after a substitution, the number of supplementary pairs to keep and walk with, is of the order of the product of the number of pairs contained in the ancestor formulas (the formula to substitute in and the substituted formula). The conclusion is that, despite the apparent advantage, this method is in general worse than the other one, and should be applied only in special cases.   

\bibliographystyle{plain}
\bibliography{refs}

\end{document}
```

## Pi Squared's Universality Stack Version 1.0

**Authors:** Pi Squared Inc.

**Date:** February 2025

### LaTeX Source

```latex
\documentclass{article}
\usepackage{graphicx} 
\usepackage{xargs} 
\usepackage[pdftex,dvipsnames]{xcolor}  
\usepackage[colorinlistoftodos,prependcaption,textsize=tiny]{todonotes} 
\usepackage{url}
\usepackage{amsmath, amssymb}
\usepackage{hyperref,cleveref}
\usepackage{tikz}           
\usetikzlibrary{graphs}
\usepackage{algorithm}      
\usepackage{algpseudocode}  

\newcommand{\spre}{s_\textit{pre}}
\newcommand{\spost}{s_\textit{post}}

\newcommandx{\fixme}[2][1=]{\todo[linecolor=OliveGreen,backgroundcolor=OliveGreen!25,bordercolor=OliveGreen,#1]{#2}}
\newcommand{\ulm}{{ULM}} 
\newcommand{\K}{\ensuremath{\mathbb{K}}}
\newcommand{\ps}{Pi Squared}
\newcommand{\paraheader}[1]{\vspace{1em}\noindent\textbf{#1}.}

\algrenewcommand\algorithmicwhile{\textbf{upon}}
\newcommand{\Upon}{\While}
\newcommand{\EndUpon}{\EndWhile}
\newtheorem{definition}{Definition}
\newtheorem{theorem}{Theorem}
\newcommand{\UniCon}{Universal Consensus Protocol}
\newcommand{\UC}{UCP}

\title{Pi Squared's Universality Stack\\\Large Version 1.0}
\author{Pi Squared Inc.}
\date{February 2025}

\begin{document}

\maketitle

{\parbox{0.86\textwidth}{\small\em 
It is suggested that the reader first read ``The Pi Squared Whitepaper''~\cite{pi2paper}.
}}

\begin{abstract}
Blockchain systems have faced persistent challenges related to fragmentation, inefficiency, and limited interoperability. The monolithic architecture of existing blockchains tightly couples execution, settlement, consensus, and data, leading to scalability bottlenecks and isolated ecosystems. Developers are restricted by language-specific environments, while cross-chain interactions rely on insecure and inefficient bridging mechanisms. These limitations stifle innovation, increase costs, and create security vulnerabilities, preventing the seamless development and deployment of decentralized applications across multiple blockchain networks.

To address these issues, Pi Squared introduces the \textit{Universality Stack}, a three-tiered architecture comprising the Universal Settlement Layer (USL), the Universal Language Machine (ULM), and the Universal Consensus Protocol (\UC{}). The USL provides a unified settlement layer based on verifiable claims, eliminating the need for traditional cross-chain bridges. The ULM enables smart contract development in any programming language, breaking the constraints of ecosystem-specific virtual machines. The \UC{} redefines consensus by allowing agreement on unordered, independent values, unlocking massive parallelism and improving scalability.

By integrating the USL, the ULM, and the \UC{}, Pi Squared’s Universality Stack creates a flexible, efficient, and secure foundation for next-generation blockchain applications. This framework enhances interoperability, empowers developers with efficient execution of smart contracts in any languages or VMs, and introduces a scalable consensus model that moves beyond traditional ordering constraints. As a result, it enables a more inclusive and adaptable Web3 ecosystem, fostering innovation and broadening access to decentralized applications across diverse platforms.
\end{abstract}

\newpage

\renewcommand{\contentsname}{Table of Contents}
\tableofcontents

\newpage

\section{Introduction}

Web3 has struggled with fragmentation and interoperability challenges for the past decade. These challenges arise from the monolithic architecture of blockchains, where execution, settlement, consensus and data are all tightly coupled within the same layer. Additionally, blockchain networks operate in isolated silos, relying on ad hoc or incomplete solutions for interoperability. Furthermore, blockchains enforce transaction serialization by design, which has consistently limited their scalability. While this traditional design may be adequate for a narrow range of applications, it presents several critical challenges:

\begin{itemize}
\item \textit{\textbf{Complexity and security}:}
Blockchains operate in isolation, requiring bridges or third-party solutions for interoperability. These introduce latency, high costs, and security vulnerabilities, as seen in bridge exploits. Cross-chain transactions demand complex infrastructure, increasing failure and attack risks.

\item \textit{\textbf{Inefficiency and cost}:}
Monolithic blockchain architectures force inter-chain operations through redundant consensus, execution, and verification layers, leading to excessive fees, slow finality, and inefficient transaction serialization.

\item \textit{\textbf{Fragmented state}:}
Assets and information remain siloed across chains, requiring cumbersome wrapping mechanisms and intermediary trust. This reduces capital efficiency, complicates multi-chain applications, and increases security risks.

\item \textit{\textbf{Siloed development}:}
Each blockchain has distinct rules, languages, and execution environments, making cross-chain interoperability difficult. Developers must build for specific ecosystems (e.g., Solidity for Ethereum, Rust for Solana), creating steep learning curves and limiting application portability.

\item \textit{\textbf{Language and VM inflexibility}:}
Developers are locked into ecosystem-specific technology stacks, restricting innovation and excluding those proficient in other languages like Python, JavaScript, or Haskell from smart contract development.

\item \textit{\textbf{Scalability bottleneck}:}
Traditional blockchains enforce global transaction ordering, even when unnecessary, leading to inefficient serialization. This limits scalability for applications that could process transactions in parallel, such as off-chain computation verification and multi-agent coordination.
\end{itemize}

To tackle these challenges, we introduce in this paper the Pi Squared \textbf{Universality Stack}, a three-tiered architecture comprising the Universal Settlement Layer (USL), the Universal Language Machine (ULM) and the \UniCon (\UC).

The \textbf{Universal Settlement Layer (USL)} introduces a unifying layer that connects applications across different blockchains using claims, which represent provable or verifiable statements. Various types of claims—such as computation, state queries, consensus validation, and vetted information—are submitted to the USL with corresponding proofs for verification and settlement. The system supports multiple proof mechanisms, including mathematical proofs, ZK proofs, re-execution, and digital signatures, making it flexible and universally compatible. Once verified, claims are added to the valid claim set, a monotonic structure that only grows over time.

Applications on any blockchain can query the USL for verified claims about other chains and receive membership proofs, verifiable certificates confirming claim inclusion in the valid claim set. This eliminates the need for complex consensus mechanisms, as membership proofs are succinct and efficiently stored on-chain. By replacing ad-hoc blockchain bridges with a spoke–hub model, the USL creates a standardized, universal framework for cross-chain interoperability, ensuring a more scalable and efficient Web3 ecosystem.

The \textbf{Universal Language Machine (ULM)} brings the universality of the \K{} framework and Proof of Proof to Web3, making blockchain development accessible to a broader community of Web2 developers unfamiliar with Web3-specific languages and stacks. As an open-source blockchain execution layer, the ULM enables smart contract development in any programming language, unlike traditional blockchains that enforce a single prescribed language. It also supports dynamic extensibility, allowing new languages to be added on-the-fly, fostering a diverse and interoperable language ecosystem. This flexibility empowers developers to use their preferred languages while lowering entry barriers for millions unfamiliar with existing Web3 languages. Pi Squared is building ULM because its formally grounded, universal approach enhances flexibility, security, and developer experience, paving the way for future innovation in decentralized applications and a more inclusive blockchain ecosystem.

The \textbf{\UniCon{} (\UC{})} is a breakthrough in consensus design, leveraging the self-contained and independently verifiable nature of the USL claims to redefine how decentralized systems achieve agreement. Unlike traditional consensus mechanisms that focus on ordering transactions or blocks—introducing unnecessary complexity — the \UC{} allows nodes to agree on unordered, independent values (claims), enabling massive parallelism for scalability and efficiency. By decoupling core consensus from application-specific safety properties, such as fork prevention in blockchains or double-spending prevention in payment systems, the \UC{} shifts the responsibility of proving these properties to the applications themselves. This separation results in a universal and flexible consensus framework, adaptable across diverse applications, from blockchain-based smart contracts to distributed databases, scientific computation verification, and multi-agent coordination. As a result, the \UC{} enables scalable, unconstrained systems that are no longer bottlenecked by traditional ordering-based consensus mechanisms.

In summary, the challenges of fragmentation and inefficiency that have long plagued Web3 can be overcome with the innovative approach introduced by Pi Squared's Universality Stack. By unifying cross-chain interoperability through the USL, enabling flexible development environments with the ULM, and providing scalable consensus with the \UC{}, Pi Squared is transforming the landscape of decentralized systems. This new framework empowers developers, improves scalability, and enhances security, fostering a more inclusive, efficient, and adaptable ecosystem.

The remainder of this paper is structured as follows. Section 2 introduces the USL claims and describes the USL architecture. This is followed in Section 3 by a description of the ULM, detailing its architecture and providing an overview of its mathematical foundations. After that, Section 4 presents the \UC{}, discussing the set consensus problem, protocol algorithms, and potential extensions. Finally, Section 5 concludes with a summary and a future outlook. 











\section{Universal Settlement Layer}
\label{usl}

The Universal Settlement Layer (USL) is a distributed network with configurable validation nodes to accept, verify, settle, and store \emph{claims}, submitted and used by all dApps and blockchains across ecosystems. 
The USL serves as a common layer that connects the computation and information islands in the current Web3 space following the spoke-hub distribution paradigm,
as a solution to the interoperability issue that is plaguing the blockchain space. 

\subsection{USL Claims}
\label{sec:usl:claims}

Claims are a mathematical concept that plays a vital role in the USL. 
In short, claims are anything provable. 
We give some typical examples of claims in the following. 
\begin{itemize}
    \item \textbf{Computation}: The execution of any program in any programming language and/or virtual machine (VM) forms a claim of the form $\langle \spre , P , \spost \rangle$,
    where $\spre,\spost$ are the runtime states before and after executing the program $P$. 
    \item \textbf{State queries}: State query functions, such as the \texttt{view} functions of the Ethereum network,
    returns the current state of a given blockchain, which forms a claim of the form $\texttt{viewFunc($s$)} = r$.
    \item \textbf{Consensus}: Given a block header, whether or not it belongs to the longest header chain
    is an important consensus problem and forms a consensus claim. 
    \item \textbf{Vetted knowledge}: Data that is available either on-chain or via a data availability layer can be vetted by their stakeholders, which form a claim of vetted knowledge and/or information.  
\end{itemize}

Different types of claims may be verified by different types of proof mechanisms
and the USL is compatible with all proof mechanisms. 
Computation claims and state query claims are related to the execution of 
some programs or functions, so their proofs can be generated using a verifiable computing framework
such as a zero-knowledge virtual machine (zkVM) or the Pi Squared's Proof of Proof framework. 
They can also be generated via the straightforward validation-by-reexecution scheme. 
Consensus claims can be verified by the cryptographic consensus proofs. 
Vetted knowledge and information can be verified by digital signature schemes. 
In short, the USL allows nodes to be configurable and to use the appropriate and desired proof mechanisms 
based on the types of the claims that are being verified and settled. 

\subsection{USL Architecture}

\begin{figure}
\centering
\includegraphics[width=1\linewidth]{USL.png}
\caption{Universal Settlement Layer (USL) Architecture}
\label{fig:usl}
\end{figure}

We present the USL architecture in \Cref{fig:usl}. 
The USL network is a distributed topological structure that consists of many USL nodes, connected among each
via the Pi Squared's Universal Consensus protocol. 

Any applications or users can submit claims to the USL for verification and settlement. 
Depending on their use cases and the needs, these claims can have various types,
such as transaction claims (i.e., computation claims), 
state query claims, consensus claims, and/or vetted information claims. 
Every claim must be associated with a corresponding proof, and thus forms
a pair $\langle c, \pi \rangle$, where $c$ is the mathematical representation of the claim
and $\pi$ is a proof that can be verified by the USL nodes. 

Internally, a USL node maintains its state as a \emph{set} of claims that have been verified and settled. 
This set forms the state of a USL node. 
There are two important characteristics of the claim sets within the USL nodes:
\begin{itemize}
    \item \textbf{Atomicity}: Claims are the smallest verifiable atom in the USL. 
     Each claim is self-contained and includes all the information for it to be 
     verified independently from the other claims. 
    \item \textbf{Timelessness}: Claims, once verified, continue staying valid regardless of time.  
     Timelessness is a natural corollary of atomicity. A time-sensitive or state-sensitive claim can be turned into
     a timeless/stateless claim by incorporating the time and/or the state as an argument of the claim. 
    \item \textbf{Monotonicity}: The set of claims maintained by a USL node only increases, and never decreases, as time passes. Monotonicity is a natural corollary of timelessness. Since valid claims continue staying valid, the USL node does not need to bother re-verifying claims and removing those that are no longer valid. 
\end{itemize}

The above characteristics of atomicity, timelessness, and monotonicity yield a new consensus protocol
for the USL network, which we call the \UniCon{} (\UC{}). 
\UC{} 
is a novel protocol designed to achieve agreement on the validity of independent claims in the USL. 
\UC{} generalizes the process of validation, enabling concurrent and unordered agreement on claims,
and makes it a foundational protocol capable of supporting diverse applications with varying requirements, from high-throughput transaction systems to domain-specific computations. 
The reader is recommended to read the dedicated technical report~\cite{uc} for more details.

Once claims are submitted to and verified by the USL node, they are added to the set of valid claims, ready to be used.
A user can query the USL about whether a given claim $c$ has been verified and settled,
and the USL should respond either yes or no. 
If the answer is yes, the USL should also output a special \emph{membership proof}
that is succinct and efficiently verifiable. 
The user verifies the claim against its membership proof and (a commitment to) the valid claim set
by a membership verifier that runs the membership proof verification algorithm
that is lightweight and fast to implement as a smart contract. 




\subsection{USL-Powered Applications}

We discuss three representative applications that can be powered or enhanced by the USL. 

\paragraph{USL and the \ulm{}.\\}
The first and foremost application that benefits from the USL is the \ulm{}. 
By connecting the \ulm{} to the USL, we increase its security and trustworthiness
by using the USL to verify and settle
claims for the block transitions carried out on the \ulm{} against their corresponding proofs. 
Furthermore, the USL enables communication and interactions between
the smart contracts on the \ulm{} and the smart contracts on the other blockchains. 
The \ulm{} states are incorporated into verifiable claims on the USL 
that can be directly queried and used by the applications on the other blockchains,
and thus improving the overall interoperability.

\paragraph{USL and Wormhole's Native Token Transfer Framework.\\}
The USL can be used to settle cross-chain messages. 
We have collaborated with the \href{https://wormhole.com/}{Wormhole}
and integrate the USL with the Wormhole’s Native Token Transfer (NTT) framework,
which is an open, flexible, and modular token transfer mechanism facilitating secure asset transfers across numerous blockchain environments, securing tens of billions of dollars in value across the blockchain sphere.
By integrating the USL as a custom Transceiver in the NTT framework that 
handles the sending and receiving of NTT messages with the USL's flexible approach to claim verification,
we obtain a new approach to cross-chain messaging with bleeding-edge innovations,
including better scalability via the independent claim verification and a more flexible trust model.
See the demo of the \href{https://pi2.network/videos/USL-Wormhole-Devcon-7}{USL-Wormhole integration}. 

\paragraph{USL and Light Clients.\\}

The USL can be used to replace the implementation of on-chain light clients for cross-chain applications. 
Currently, the one-way communication from a source blockchain to a target blockchain relies on the implementation
of a light client of the source chain as an online smart contract on the target chain. 
On-chain light clients have to be implemented for each combination of the blockchains and/or ecosystems, leading to
significant workload and duplicated work. 
The USL and its spoke–hub distribution paradigm provides a more economic solution, 
where the light client (for each source chain) only needs to be implemented once and for all on the USL,
which is available to be used by all target blockchains and/or applications. 

In the above, we give an overview of three representative and ongoing applications building on top of the USL:
the \ulm{}, the Wormhole's NTT framework, and on-chain light clients. 
We are looking forward to collaborating with the community and identifying and enabling more high-demanding 
applications that can directly benefit from the verifiability, security, and interoperability provided by the USL.


\section{Universal Language Machine}


The Universal Language Machine (\ulm{}) is an open-source blockchain execution layer that enables developers to create, deploy, and interact with smart contracts written in any programming language.
Unlike existing blockchain systems that require all contracts to be written in a single prescribed language, the \ulm{} natively supports multiple languages.
In this way, the \ulm{} enables diverse language ecosystems to coexist and interoperate on a single platform.
This not only empowers developers to use the most suitable language for their dApps; it also makes smart contract development more accessible to the millions of developers who are unfamiliar with existing Web3 languages.

At its core, the \ulm{} leverages the formal semantics of programming languages to securely execute smart contracts in a correct-by-construction manner.
This is all thanks to the \K{} framework, a proven system for formally defining programming languages backed by decades of research and extensive industry use.
As further discussed in the sequel, by submitting a \K{} specification of a programming language $L$, the \ulm{} can be dynamically extended to support \textit{any} language.
At launch, \ps{} will provide an initial set of prebuilt programming languages modules available for immediate use, with plans for additional modules to be made available at a later date.

\subsection{\ulm{} Architecture Overview}

\begin{figure}
\centering
\includegraphics[scale=0.25]{ULM.png}
\caption{Universal Language Machine (ULM) Blockchain Architecture}
\label{arch-figure}
\end{figure}

As mentioned in the introduction, an important facet of the \ulm{} design is its native multi-language support.
By plugging in new \emph{language modules}, developers can dynamically extend the \ulm{}'s set of on-chain programming languages.
This enables developers to build and interact with smart contracts written in \emph{any} programming language.
We provide an overview of a \ulm{}-based blockchain architecture, including language modules, in Figure \ref{arch-figure}.

A key design decision enabling \emph{correct} multi-language transaction execution is the \ulm{}'s \emph{semantics-based} execution.
By semantics-based, we mean that on-chain programming languages are executed \emph{directly}, without compilation, using \emph{correct-by-construction} interpreters \emph{derived} from their formal semantics.
By \emph{formal semantics} of some language $L$ (e.g., Rust), we mean a mathematical definition of $L$ that gives a precise meaning to all well-formed $L$ programs (e.g., all Rust programs).

Since designing a semantics-based execution platform from scratch is an enormous and error-prone undertaking,
the \ulm{} platform relies on the \K{} framework for specifying and executing formal language semantics.
This means that the \ulm{} language module for language $L$ (e.g. Rust) is just the formal semantics of $L$ specified in \K{}.
Aside from reinventing the wheel, another important reason why \ps{} chose to rely on \K{} is because the \K{} framework is mature, production-ready programming language development toolchain that has been in use for over a decade.
Lastly, one other benefit of working with \K{} is its expressive power.
Given a formal operational semantics of a language $L$, \K{} can generate a full suite of correct-by-construction $L$-specific tools including parsers, interpreters, debuggers, theorem provers, etc.\hspace{0.5em}all without additional tool-specific code.

\subsubsection{Language Modules}
\label{lang-mod}

A language module is a formal specification, defined using the \K{} framework, of a programming language's syntax and semantics.
Since \K{} can generate correct-by-construction language-specific parsers and interpreters, this means the \ulm{} can rely on \K{} to correctly validate and execute input programs.
In fact, the \ulm{} derives its \emph{universality} from \K{} language modules, since these modules permit developers to securely extend the \ulm's set of on-chain executable languages.
Furthermore, using \K{} provides a secondary benefit; by defining a language module for a language $L$ (e.g. Solidity), we can execute $L$ programs in \K{} directly, without intermediate compilation!
In this section, we describe in further detail how language modules operate in the \ulm{} platform.

From a smart contract developer's perspective, a language module $Mod(L)$ can be understood as a special kind of $L$ interpreter.
However, since arbitrary language modules can be added to the \ulm{} platform dynamically, the \ulm{} executes each language module instance in a secure sandbox.
This sandbox prevents the code in $Mod(L)$ from influencing the behavior of other system components, including other language module instances.

Now, we are ready to examine the structure of a language module.
Every language module contains:

\begin{enumerate}
    \item \textbf{Syntax}: Rules that define well-formed $L$ programs.
    \item \textbf{Configuration}: Definitions of internal, ephemeral state items managed by an $L$ interpreter.
    \item \textbf{Semantics}: Rules that describe how to execute $L$ programs.
    \item \textbf{\ulm{} primitives}: Definitions of the \ulm{}-specific interfaces.
\end{enumerate}

Recall that language modules are just a special kind of \K{} definition suitable for use by the \ulm{}.
By suitable, we mean that $Mod(L)$ provides all necessary \ulm{} primitives, i.e., satisfies the \ulm{} application programming interface (API).
The current set of primitives\footnotemark{} includes:

\footnotetext{In the future, \ps{} may develop and release additional primitives in order to provide new functionality to on-chain languages or improve performance.}

\begin{enumerate}
    \item \textbf{Initialization}: Deserialize and load an $L$ program plus its initial arguments.
    \item \textbf{Finalization}: Serialize and return a value (if one exists).
    \item \textbf{Invocation}$^*\!$: Serialize program arguments in order to call another contract.
    \item \textbf{Storage}$^*\!$: Read from/write to the \ulm{}'s persistent blockchain state.
\end{enumerate}

\noindent Where starred primitives are \emph{optional}.\footnote{A module without these optional primitives will have severely restricted functionality.}

Aside from providing a universal interface between language modules and the \ulm{}, the \ulm{} primitive API ensures blockchain security by mediating access control policy decisions.

We end this section with a few highlights:
\begin{enumerate}
  \item When a contract is deployed/invoked, the \ulm{} determines the correct \K{} language module to load based on the transaction's associated language ID; this allows contracts in different languages to coexist.
  \item Each language module is executed by the \ulm{} in a secure sandbox so that malicious actors cannot influence system behavior via custom language modules.
  \item Contracts deployed to the \ulm{} are executed by the \K{} framework, which ensures verifiable, correct-by-construction executions.
  \item All language modules must access/modify persistent blockchain state through the \ulm{} API, i.e., a tiny set of \ulm{} primitives; the API also mediates access control policy to ensure blockchain security (e.g., each language module can only directly update the storage under its own namespace).
\end{enumerate}

\subsection{\ulm{} Mathematical Overview}

Formally, we can view a blockchain as a transition system where states are blockchain states and transitions are transaction executions.
In other words, the execution layer defines the \emph{state transition function}.
In particular, the execution layer enables the blockchain state to \emph{evolve} over time, letting it represent dynamic quantities like a token balance, NFT ownership, earned interest, or even an online game status.

In this section, we will provide an overview of the \ulm{}'s execution layer state transition function.
For brevity, we let the Greek letter $\tau$ refer to this function, which has the following type:

$$\tau : State \times Transaction \rightarrow State$$

\noindent where we let $State$ and $Transaction$ denote local blockchain state and blockchain transactions, respectively.

In plain English, the \ulm{} state advances by executing transactions that produce successor states.
An important requirement of the function $\tau$ is that it is both \emph{total} and \emph{deterministic}, i.e., it produces a \emph{valid} and \emph{unique} result for all possible argument combinations.
The \textit{totality} requirement ensures liveness; in particular, this means malicious actors cannot execute a denial of service (DOS) attack by exhausting all resources or crashing the \ulm{} using ill-formed inputs (see Section \ref{gas} for important details about how this property depends on a suitably chosen gas model).
The \textit{determinism} requirement ensures that any \ulm{} node at state $N$, when executing transaction $N$, produces a unique successor state $N+1$, giving rise to the \ulm{} blockchain's eponymous chain-like structure\footnotemark{} shown in Figure \ref{blockchain}.

\footnotetext{More precisely, the determinism of the state transition function is sufficient to ensure \emph{locally} unique successor states; producing a \emph{globally} unique successor state among a distributed collection of blockchain nodes also requires a consensus protocol.}

\begin{figure}
    \centering
    \includegraphics[width=\linewidth]{ulm-state.png}
    \caption{Universal Language Machine (ULM) State Evolution}
    \label{blockchain}
\end{figure}

In the \ulm{}, all blockchain transactions share a common transaction envelope but come in three distinct classes: call transactions, contract deployment transactions, and language deployment transactions.
A BNF grammar describing this transaction structure is shown below.


\begin{align*}
Transaction ::=\ \ & Txn(Sig, Sender, FeeAmt, LangId, TxnType)\\
TxnType ::=\ \ & Call(SendAmt, Dest, ProgramArgs)\\
          |\ \ & DeployContract(SendAmt, ContractCode, ProgramArgs)\\
          |\ \ & DeployLang(LangModule)
\end{align*}
\noindent Regardless of transaction type, the outer transaction envelope contains several common elements:

\begin{enumerate}
    \itemsep0.25em
    \item A sender address with a corresponding public key.
    \item A declared amount of tokens to be used to pay transaction fees.
    \item A language ID that specifies the on-chain language to be used.
    \item A digital signature generated by the private key for the sender's public key.
\end{enumerate}

\noindent The \ulm{}'s call and contract deployment transactions largely follow standard conventions, which we briefly review here; we describe the language ID field and language deployment transaction in more detail below.

Contract deployment and call transactions contain two additional shared fields:

\begin{enumerate}
    \item A declared amount of tokens to be transferred to the destination address.
    \item  Zero or more program arguments.
\end{enumerate}

The key difference between the two transaction types lies in how the destination address is computed.
In contract deployment transactions, the destination address is \emph{generated} during the transaction execution, the embedded code is stored at the generated address, and finally, the code's initializer function, if it exists, is invoked with the given program arguments.
In call transactions, the destination address is specified directly; then, the program deployed at the specified address is loaded and invoked with the given program arguments.
Note that, like many blockchains, call transactions are overloaded to transfer currency when the recipient address is not a contract account.

Unlike other blockchains, transaction envelopes also contain a language ID field.
When a contract deployment or call transaction with language ID $L$ is executed, the \ulm{} loads a fresh instance of $Mod(L)$ to parse and execute any code.
The language ID field also appears in language deployment transactions. 
In response to a valid $Txn(..., L, DeployLang(Mod(L)))$ transaction, the \ulm{} uses \K{} to validate, compile, and store $Mod(L)$ under identifier $L$.

We can now fully specify the language-specific transaction execution requirements that we elided in our overview above.
When validating a transaction with language ID $L$ of the form $DeployContract(..., ContractCode, ProgramArgs)$ or $Call(..., Dest, ProgramArgs)$, the execution layer must verify:

\begin{enumerate}
    \item Language ID $L$ points to a language module $Mod(L)$.
    \item $ContractCode$, $ProgramArgs$ are well-formed w.r.t. $Mod(L)$.
    \item $Dest$ points to a program stored with language ID $Mod(L)$.
    \item $ProgramArgs$ are well-typed w.r.t. $ContractCode$.
\end{enumerate}

\noindent If any of the above assertions fail, the transaction will abort.


\subsection{Universal Interfaces}

As a blockchain executor, the \ulm{} requires an input transaction format and an on-chain programming language format.
Of course, in a blockchain context, we also require an account/address scheme, gas model, value serialization format, and storage layer interface.
Additionally, language universality requires a dynamically loadable representation of a programming language, which we refer to as a \emph{language module}.
Separately, universality imposes additional requirements.
Specifically, language-specific gas, address, and storage schemes (where they exist) must be mapped into a unified model that respects the security properties of the underlying language.
In particular, cross-language contract calls require additional interface support.


In this section, we fill in some omitted details regarding how language modules interact with the \ulm{} and interoperate with each other.
The descriptions here reflect how language modules' semantics must be mapped into the \ulm{}'s underlying blockchain model. 

\subsubsection{Unified Account Model}

\begin{figure}
    \centering
    \includegraphics[width=\linewidth]{account.png}
    \caption{Universal Language Machine (ULM) Account Model}
    \label{fig:ulm-account}
\end{figure}

Accounts in a blockchain serve multiple roles: as on-chain identities (facilitating access-control policies), digital wallets (storing and transferring digital currency), and storage regions (grouping data owned by their corresponding identity).
For this reason, when designing a new blockchain, its account model must be carefully considered.
However, due to the \ulm{}'s universality, we must also consider the case where a contract in language $L_1$ calls a contract in language $L_2$ in a single transaction.
Since the \ulm{} allows multiple languages to coexist and interoperate in the same transaction, we additionally require that the account model (if it exists) of each participating language be respected.
When designing the \ulm{}'s account model, our goal was to generalize existing popular models so that they could be easily embedded into our model.

In general, the \ulm{} partitions each account $A$ into one of three $AccountTypes$:

\begin{enumerate}
    \item Non-executable Accounts: these accounts have corresponding public/private key pairs which can be used to authorize transactions that spend money and use data owned by this account;
    \item Executable Accounts: these accounts have associated on-chain code in language $L$ that is authorized to spend money and use/modify data owned by this account;
    \item Idle Accounts: these accounts have neither associated on-chain code nor corresponding public/private key pairs; all accounts initially have this type.
\end{enumerate}

\noindent As a security precaution, the \ulm{} enforces the following restriction on account types:

\begin{enumerate}
    \item An idle account may transition to another account type;
    \item The type of a non-idle account can never change;
    \item If an executable account contains an $L_1$ program, it can never contain $L_2$ programs where $L_1 \neq L_2$. 
\end{enumerate}

These restrictions ensure that on-chain identities are consistent and malicious actors cannot confuse on-chain programs by arbitrarily updating account types.
Additionally, each account $A$ has an associated group of storage regions $Storage_A$ with the following structure:

$$ Storage_A : [ LangId \times Bytes \rightarrow Bytes ] $$

\noindent Then each storage region $Storage_A(L, K)$ represents data that is owned by account $A$ that:

\begin{enumerate}
    \item is associated with key $K$;
    \item is only readable by on-chain programs with language ID $L$.
\end{enumerate}

The \ulm{} does not prescribe the structure of storage keys $K$ or the the exact format of $Storage_A(L,K)$.
Instead, the \ulm{} account model enables each language module $Mod(L)$ to control the structure of its associated storage regions (up to a maximum storage key and region size limit) and their access control policies.



\subsubsection{Unified Invocation API}

In the \ulm{}, multiple language modules can interact in the same transaction via cross-language calls.
These kinds of calls are the blockchain equivalent of a foreign function interface.
To handle this situation, the \ulm{} defines a unified API for cross-language contract invocation.
For the remainder of this section, we assume that a contract in language $L_1$ is invoking an entry point $f(p_1,\ldots,p_n)$ on contract in language $L_2$ where $L_1 \neq L_2$ with arguments $a_1,\ldots,a_k$ and where each $p_1,\ldots,p_n$ are parameter types.
Our unified invocation API consists of several parts:

\begin{enumerate}
    \item \textbf{Function selector}: A byte string that identifies the $L_2$ contract entry point $f(p_1,\ldots,p_n)$ to be invoked; in some cases, the function selector must be qualified, i.e., prefixed by a non-empty list of module names starting from the destination address's root namespace. The structure of this selector is specified by the target language module (up to a \ulm{}-specified maximum size limit). 
    \item \textbf{Native types}: A set of datatypes\footnotemark{}, denoted by $NativeTypes$, that can be passed between language modules; currently, this set includes addresses, variable-length byte strings, and variable-width integers.
    \item \textbf{Parameter encoding}: A unified, typed serialization format defined for each supported language $L$ as a pair of partial, injective maps; let  $Ser_L: [Types(L) \rightarrow NativeTypes]$ and its inverse $Des_L$ denote the serialization and deserialization functions, respectively. The partiality of these maps means that $L$ types and native types may not fully correspond.
\end{enumerate}

\footnotetext{As the platform develops, \ps{} may extend the set of native types.}

From a high-level perspective, this interface may seem simple; however, in actuality, this design must navigate a number of subtle issues simultaneously, which we explore further below.

Firstly, if the set of native types included all datatypes, it would actually nullify capabilities-as-parameters access control policies, which are actively used in some languages, e.g., Move.
Secondly, to pass data between two languages, we actually interact with \emph{three} separate type systems: $Types(L_1)$, $NativeTypes$, and $Types(L_2)$;
this approach avoids bitcast-style type conversions, as these may unexpectedly change the meaning of call arguments, leading to unsound executions.
Thirdly, due to the fact that (a) language modules are user-defined and (b) contract call destinations and parameter types are not statically known, cross-language calls cannot, in general, be statically validated.
This means that, when a cross-language invocation occurs, the \ulm{} must perform a dynamic validation check.

One may wonder how the authors selected the limited set of native types for cross-language calls.
By a naive analysis, it seems that supporting as many native types as possible would improve the developer experience.
Unfortunately, letting native types encompass all datatypes fundamentally breaks capabilities-as-parameters access control policies.
When these policies are used, function parameters may represent \emph{unforgeable capability tokens}, i.e., by acquiring the capability token, the function is authorized to perform a restricted operation.
Thus, if native types included capability tokens, then other languages could arbitrarily forge them, nullifying all of their security guarantees.
For this reason, the authors elected to support a minimal set of native types that is obviously secure, as opposed to a maximal set that is not obviously insecure.

We now describe the cross-language contract invocation process including all dynamic validation checks performed by the \ulm{}.
The process proceeds as follows:

\begin{enumerate}
    \item Validate that the function selector $f(p_1,\ldots,p_n)$ resolves to a valid function at the destination address.
    \item Validate that all arguments can be translated from $L_1$ into $L_2$ types, i.e., the map $b_i = Des_{L_2}(Ser_{L_1}(a_i))$ is defined for $1\leq i\leq k$.
    \item Validate that the native parameter count $k$ matches the actual parameter count $n$ and that mapped native types match expected types, i.e., $Type(b_i) = p_i$ for all $1\leq i\leq k$. 
    \item Invoke the $L_2$ contract by calling $f(b_1,\ldots,b_n)$.
    \item If the preceding invocation produced a return value $v_2$, validate that $v_1=Des_{L_1}(Ser_{L_2}(v_2))$ is defined; return $v_1$ from the cross-language invocation.
\end{enumerate}

Note that if \emph{any} validation check fails, the entire transaction will abort.
Further, observe that there are many ways that a cross-language transaction may fail, and many checks are required to make them safe.
The extra expressive power of cross-language contract invocations necessarily increases their cost.
However, without these additional checks, cross-language contract invocations could become unsound.

Finally, there is one issue that we elided in our description above: what about non-local control flow constructs that cross language contexts?
For example, what happens if an $L_1$ program invokes an $L_2$ program which throws an exception but does not catch it?
Since $L_1$ may not implement exceptions itself, there is no way to safely throw exceptions across a language context.
Another popular non-local control flow construct, call-with-current-continuation, requires function pointers to work correctly.
However, sharing a function pointer that was created in an elevated security context is equivalent to sharing a capability token; any transitive callee that obtains the function pointer can escalate their privileges merely by invoking it.
For this reason, to remain sound, the \ulm{} aborts whenever non-local control flow passes between language contexts.

\subsubsection{Unified Gas Model}
\label{gas}


The primary purposes of a gas model are to ensure that all on-chain programs terminate and to calculate appropriate fees to be paid to blockchain validators.
However, due to the \ulm{}'s \emph{universality}, i.e., that \ulm{} language developers can add arbitrary language modules $Mod(L)$ to the \ulm{} platform, we cannot rely on any embedded gas model in $L$---and, in fact, $L$ may not have a gas model at all.
For this reason, the \ulm{} adopts a unified gas model across all language modules.
This unified model not only ensures fair gas cost comparisons between languages, it also prevents bad actors from injecting malicious gas models that consume gas tokens excessively.

To understand the unified gas model, recall that all language modules are just \K{} specifications which satisfy the \ulm{} API.
In particular, this means that language executions are performed by correct-by-construction interpreters generated by \K{}.
Therefore, to decouple our gas model from any programming language semantics $Mod(L)$, we charge gas based on the computational cost of executing single steps in \K{}-generated interpreters.


At a basic level, a \K{} specification consists of a definition of system state called a \emph{configuration} and a series of \emph{rules} describe how the configuration may evolve in response to an input program.
This means that each step executed in a \K{} interpreter is the result of applying some rule.
When the \K{} framework compiles a \K{} specification into executable code, it derives a semantics-specific deterministic algorithm that searches among all potentially applicable rules to quickly find one that applies.
Once it finds such a rule, it applies it and repeats the process.
Otherwise, if no rule applies, execution halts.

Finally, we can compute the cost of a single step as the sum of the following costs:

\begin{enumerate}
    \item The cost of a rule search.
    \item The cost of a rule application.
\end{enumerate}

\noindent For brevity, we will not further discuss the rule search and application algorithms here; for more detail, see our whitepaper on the LLVM backend \cite{llvm-backend}.

At this point, the astute reader may still wonder, if language $L$ has an embedded gas model, how will this gas model interact with the \ulm{} unified model?
The answer is simple: the \ulm{} unified gas model is ultimately used to ensure program termination and to charge gas fees; however, if $L$ has an embedded gas model, $L$ programs may abort earlier due to hitting an embedded gas limit.
As a matter of course, \ps{} recommends that language modules refrain from embedding gas models, because this may lead to confusion about how execution fees for $L$ programs should be paid.


\subsection{Putting It All Together}

\begin{figure}
    \centering
    \includegraphics[width=\linewidth]{transaction.png}
    \caption{Universal Language Machine (ULM) Transaction Workflow}
    \label{fig:ulm-tx}
\end{figure}

In this section, we examine a possible multi-language transaction workflow involving a Rust and EVM contract.
The overall scenario is shown in Figure \ref{fig:ulm-tx}.
The workflow begins when an incoming transaction, annotated with the Rust language ID, invokes a program at account $A$.
To start, the \ulm{} interface queries the blockchain database and loads the account state for account $A$.
It verifies that the type of account $A$ is executable and its language ID matches that of the transaction (in this example, Rust).
The \ulm{} now creates a sandboxed instance of the Rust language module $Mod(Rust)$ which it will use to initialize the Rust program $code_A$.
To initialize the program, the Rust module decodes the program arguments (or \emph{calldata}, in Ethereum parlance) as follows:

\begin{enumerate}
    \item The function selector $f_A$ is separated from the encoded function parameters $enc(args_A)$;
    \item The parameters are decoded with the module's parameter deserialization function, i.e., $args_A = Des_{Rust}(enc(args_A))$.
\end{enumerate}

After verifying that $f_A$ is a valid entrypoint selector for $code_A$, the Rust module invokes input program $code_A$ at entrypoint $f_A(args_A)$.
Now, suppose that, during the execution of the Rust semantics, an external function $f_B$ at account $B$ is invoked with parameters $args_B$.
To handle this inter-contract call, the \ulm{} encodes the function selector and arguments into a binary calldata string using the inverse of the process described above:

\begin{enumerate}
    \item The parameters $args_B$ are encoded with the module's parameter serialization function $enc(args_B) = Ser_{Rust}(args_B)$;
    \item The function selector $f_B$ and $enc(args_B)$ are concatenated into a single calldata byte string.
\end{enumerate}

At this point, the \ulm{} interface will repeat the contract loading and initialization process for account $B$ with program $code_B$.
In our example, we assume that account $B$ is executable and has the EVM language ID.
To handle this call, the \ulm{} will create a sandboxed instance of the EVM language module $Mod(EVM)$
which will decode the calldata and invoke the input program $code_B$ at entrypoint $f_B(args_B)$.
When the EVM semantics terminates and returns $value$, the \ulm{} will detect that an inter-contract return is required.
To handle the return, $value$ will be encoded using the module's serialization function $result = Ser_{EVM}(value)$.
Finally, the \ulm{} will return control to the Rust module which can decode the result via its deserialization function $Des_{Rust}(result)$.


\section{\UniCon}

The \textbf{\UniCon{}} (\UC{}) is a novel, Byzantine fault-tolerant (BFT) protocol designed to achieve agreement on the validity of independent claims in a permissionless, decentralized network. Unlike traditional consensus mechanisms that focus on ordered state transitions or linear transaction logs, \UC{} generalizes the process of validation, enabling generic, concurrent and unordered agreement on claims. 

The \UC{} is being designed and developed in collaboration with the team behind \textit{Pod}~\cite{AlposADZ:2025}. \UC{} leverages the primitives pioneered by Pod (in addition to earlier work on which Pod is based~\cite{BaudetBDS:2020,SliwinskiSW:2021,BrachaB:1987}). By building on these robust foundational elements, the \UC{} aims to deliver a protocol that is both highly scalable and adaptable.


\subsection{Set Consensus on Claims}
\label{sec:ucp:claim-consensus}

As described in Section~\ref{sec:usl:claims}, \textbf{claims} in the USL serve as the fundamental unit of validation and consensus. A claim represents an assertion submitted to the network for verification, such as the validity of a state transition induced by a transaction, a mathematical proof of a theorem, or the outcome of a computation. Claims are independent entities, meaning their validity does not inherently depend on the order in which they are processed. In the context of the \UC{}, we abstract claims as values that can be evaluated independently for their validity.

The \textbf{Set Consensus Problem} focuses on achieving agreement among distributed nodes on a set of independent values, rather than an ordered sequence of values. In this problem, nodes (concurrently) propose individual values (claims), and the goal is for the network to collectively decide on the subset of these values that are valid (according to claim verification rules). Importantly, the decision process does not require imposing a any order on the values, enabling concurrent validation and processing of values.

This approach contrasts with traditional \textbf{blockchain consensus}, which typically centers on achieving agreement on a linear sequence of (blocks of) transactions or, in some applications, a partially ordered set of transactions (like payment transactions). Blockchain consensus protocols ensure that all nodes agree on the exact order of transactions to prevent (application-specific) conflicts and maintain a consistent ledger state. This ordering requirement introduces additional complexity and resource overhead, as nodes must coordinate to resolve conflicts over which transactions or blocks should be appended to the chain.

We highlight below key differences between set consensus on claims and traditional blockchain consensus on transactions.

\paragraph{Order Independence\\}
Set consensus does not impose any ordering on values, enabling concurrent processing, while Blockchain consensus requires a strict, globally agreed-upon (total or partial) ordering of transactions. As a result, set consensus is a simpler, more robust and more general consensus protocol design.

\paragraph{Scalability\\}
By avoiding the need to order values, set consensus can achieve significantly higher throughput and lower latency for applications that do not require value ordering. Values can be produced and settled massively in parallel. On the other hand, blockchain consensus often sacrifices scalability to ensure order and consistency.

\paragraph{Separation of Concerns\\}
Set consensus on claims focuses exclusively on determining the validity of individual claims, separating this process from application-specific safety properties, such as maintaining a particular order of transactions to ensure a sequence of state transitions that satisfy absence of double-spending of a token. These properties are the application’s responsibility to prove correct, and are independent of the core consensus mechanism. This separation allows for the design of a universally generic consensus protocol that can be instantiated to support a wide variety of use cases with different requirements (see Section~\ref{sec:use-cases} for further details and some concrete use cases). In contrast, blockchain consensus enforces global transaction ordering, ensuring application-level safety but imposing unnecessary overhead on systems that do not require strict sequencing, leading to inefficiency and reduced scalability.







\subsection{Protocol Description}

In the following sections, we outline the design of the \UC{}, detailing its operational mechanics, underlying assumptions, and the adversarial model it is designed to withstand.

\subsubsection{Setup}

The protocol operates within a network of nodes classified as either validators or clients, each fulfilling distinct roles in the system.

Clients are nodes responsible for:

\begin{enumerate}
    \item Providing claims that require validation
    \item Maintaining a local, up-to-date view of the network’s state.
\end{enumerate}

Validators, on the other hand, are nodes tasked with individually verifying these claims to ensure that only claims that are verified correct are maintained by the protocol.

\begin{figure}
    \centering
    \includegraphics[width=\linewidth]{connection_graph.png}
    \caption{The connection topology of validators and clients in the \UC{} network. Bidirectional connections of validator V1 and client C1 are highlighted as examples.}
    \label{fig:uc_connections_graph}
\end{figure}

Similarly to pod, we assume a communication topology of a complete bi-partite graph of clients and validators, as illustrated by Figure~\ref{fig:uc_connections_graph}. Importantly, validators do not need to communicate with one another as they maintain local logs of claim verification results. Clients maintain streaming, stateful connections to all validators.

Validators are identified by public keys registered in a public key infrastructure (PKI). They sign all outgoing messages, providing cryptographic assurance of message authenticity and integrity since signatures cannot be forged.

We consider an asynchronous network model in which message delivery delays are finite but unpredictable (i.e., messages are only guaranteed to be delivered eventually). However, achieving liveness necessitates a (partially) synchronous network, where the delivery delay bound is both finite and known. Whenever this synchrony assumption is relied upon, it is explicitly stated.

The protocol is designed to tolerate Byzantine nodes that act arbitrarily or deviate from the protocol rules. As in pod, we assume a limit on the resilience threshold $\beta$, which is the number of malicious validators (typically $(n-1)/3$ where $n$ is the total number of validators). There is no inherent assumption about the honesty of clients.


\subsubsection{Construction}

In this section, as we abstract claims as values whose correctness can be checked deterministically by validators and independently by third parties according to a public verification procedure, $\textbf{verify}(m)$, where $m$ is a claim. We assume that $\textbf{verify}(m)$ is correctly implemented and that its execution takes at most $\tau$ time units.

\begin{definition}{\textbf{(claim)}\\}
A claim $m$ is a value that can be deterministically and independently verified correct using the public procedure $\textbf{verify}(m)$.
\end{definition}

In \UC{}, claims progress through four states: \textit{Unchecked}, when newly submitted and unevaluated; \textit{Pending}, after receiving an initial validation vote while awaiting consensus; \textit{Finalized}, upon securing a quorum of votes; and \textit{Invalid}, if it fails to gather sufficient votes within a given timeframe. The state transitions of a claim are depicted in Figure~\ref{fig:uc_claim_states}.

\begin{figure}
    \centering
    \includegraphics[width=\linewidth]{claim_states.png}
    \caption{The state transition of claims in the \UC{}. Note that ``Finalized'' and ``Invalid'' are terminal states.}
    \label{fig:uc_claim_states}
\end{figure}

Clients submit claims to validators, which verify and vote for them. A vote is an attestation by a validator that the claim has been verified correct.
\begin{definition}{\textbf{(Vote)}\\}
A vote is a tuple $(m, n, \sigma, R))$ consisting of:
\begin{itemize}
    \item $m$, the claim for which the vote is made
    \item $n$, the validator's sequence number for this vote
    \item $\sigma$, the validator's digital signature of $(m, n)$
    \item $R$, the validator's identifier (public key)
\end{itemize}
\end{definition}


\paragraph{Clients\\}
A client maintains in its local state three components:
\begin{enumerate}
    \item Public keys of all validators (replicas) $\mathcal{R}$ along with the expected next sequence number for each validator
    \item A map $\textsf{claim\_votes}$ that defines for each claim in the network the set of all validator votes received 
    \item The current view $D = (\mathcal{M}_f, \mathcal{M}_p)$, a pair of disjoint sets of finalized and pending claims
\end{enumerate}
By construction, the view $D$ is fully derivable from the $\textsf{claim\_votes}$ map. Specifically, each finalized claim in $\mathcal{M}_f$ corresponds to an entry in $\textsf{claim\_votes}$ that maps to a set of votes forming a quorum. Similarly, every pending claim in $\mathcal{M}_p$ maps to a set of votes that does not yet constitute a quorum. Note that clients do not maintain claims for which no vote was seen. The client's state and procedures are listed in Algorithm~\ref{alg:uc-client}. We say that a client $C$ observes that a claim $m$ is finalized if $m \in \mathcal{M}_f$ in the view of $C$.

\begin{algorithm}
\caption{\UC{} Client}
\begin{algorithmic}[1]
\State $\mathcal{R} : \{R_1, \ldots, R_n\}$ \Comment{Replicas public keys}
\State $\textsf{nextsn} : \mathcal{R} \rightarrow \mathbb{N}$ \Comment{next sequence number for each validator}
\State $\textsf{claim\_votes} : \mathcal{M} \rightarrow \mathcal{V}$ \Comment{votes observed for each claim}
\State $D : (\mathcal{M}_f, \mathcal{M}_p)$ \Comment{current view of finalized and pending claims}

\

\Upon{event $\textit{init}(R_1, \ldots, R_n)$}
    \State $\mathcal{R} \gets \{R_1, \ldots, R_n\}$
    \State $D \gets ( \emptyset, \emptyset )$
    \For{$R_i \in \mathcal{R}$}
        \State $\textsf{nextsn}[R_i] \gets -1$
        \State \textbf{send} $\langle \text{CONNECT} \rangle$ \textbf{to} $R_i$
    \EndFor
\EndUpon

\

\Upon{receive $\langle \text{VOTE} (m, n, \sigma, R) \rangle$}
    \If{$m = \textsf{nextsn}(R)$ and $\textbf{valid}(\sigma)$}
        \State $\textsf{claim\_votes}.\textbf{augment}(m, (m, n, \sigma, R))$
    \EndIf
\EndUpon

\

\Function{write}{$m$}
    \For{$R_i \in \mathcal{R}$}
        \State \textbf{send} $\langle \text{WRITE } m \rangle$ \textbf{to} $R_i$
    \EndFor
\EndFunction

\

\Function{read}{\,}
    \State $(\mathcal{M}_f, \mathcal{M}_p) \gets ( \emptyset, \emptyset )$
    \For{$m \in \textsf{claim\_votes}.keys()$}
        \If{$|\textsf{claim\_votes}[m]| \geq 1 - \beta$}
            \State $\mathcal{M}_f \gets \mathcal{M}_f \cup \{ m \}$
        \Else
            \State $\mathcal{M}_p \gets \mathcal{M}_p \cup \{ m \}$
        \EndIf
    \EndFor
    \State $D \gets (\mathcal{M}_f, \mathcal{M}_p)$
    \State \textbf{return} $D$
\EndFunction

\end{algorithmic}
\label{alg:uc-client}
\end{algorithm}

When a client first joins the network, it invokes its initialization procedure \textsc{init}, which initializes its set of validator public keys and sends out connection requests to all validators. Upon initialization, the client starts a fresh with an empty $\textsf{claim\_votes}$ map and an empty view. These structures are first populated when connections are established with validators (see Algorithm~\ref{alg:uc-validator}).

Clients receive votes from validators attesting to validity of claims. Upon receiving a vote $(m, sn,\sigma, R)$, the client first checks that the vote's sequence number is the expected value for $R$ and verifies the signature $\sigma$. Upon validation, it augments the set of votes for the claim $m$ with this vote. Note that if this is the first vote received for claim $m$, a new entry in the $\textsf{claim\_votes}$ map is created.  

Similarly to Pod, clients interact with the protocol through a write-read interface to submit new claims and update the current state of claim verification. To write a new claim, a client sends it to validators for verification. As the client continuously receives votes from validators, recorded in $\textsf{claim\_votes}$, it reads the state by scanning $\textsf{claim\_votes}$. Claims with a quorum of votes are added to the set of finalized claims $\mathcal{M}_f$, while the remaining claims—those with at least one vote but not yet a quorum—are added to the set of pending claims $\mathcal{M}_p$. This process ensures an up-to-date view of both finalized and pending claims.


\paragraph{Validators\\}
A validator maintains a local state consisting of the set of connected clients, the next sequence number to attach to a vote, and a log  of claim verification results for all claims it has encountered so far. Each verification result indicates the validator’s assessment of the claim: it is either a vote for correctness if the claim is valid or \textsf{False} if it is not. Recall that a vote is a tuple $(m, n, \sigma, R))$ that includes the validator's signature $\sigma$ of the claim. The local state and procedures of a validator are listed in Algorithm~\ref{alg:uc-validator}.

\begin{algorithm}
\caption{\UC{} Validator}
\begin{algorithmic}[1]
\State $\mathcal{C}: \{C_1, \ldots, C_n\}$ \Comment{all connected clients}
\State $\textsf{nextsn} : \mathbb{N}$ \Comment{next sequence number to use}
\State $\textsf{log} : \mathcal{M} \to \mathcal{V} \cup \{\textsf{False}\}$ \Comment{claim verification results}

\

\Upon{event $\textit{init}$}
    \State $\mathcal{M} \gets \emptyset, \textsf{nextsn} \gets 0, \textsf{log} \gets \emptyset$
\EndUpon

\

\Upon{receive $\langle \text{CONNECT} \rangle$ from $C$}
    \State $\mathcal{C} \gets \mathcal{C} \cup \{C\}$
    \For{$m \in \textsf{log}.keys()$}
        \If{$\textsf{log}[m] \neq \textsf{False}$}
            \State \textbf{send} $\textsf{log}[m]$ \textbf{to} $C$
        \EndIf
    \EndFor
\EndUpon

\

\Upon{receive $\langle \text{WRITE}\ m \rangle$}
    \If{$m \notin \textsf{log}.keys()$}
        \If{$\textbf{verify}(m)$}
            \State $\sigma \gets \textbf{sign}(m, \textsf{nextsn})$
            \State $\textsf{log}[m] \gets \textsf{log}[m] \cup (m, nextsn, \sigma)$
            \For{$C \in \mathcal{C}$}
                \State \textbf{send} $\langle \text{VOTE} (m, \textsf{nextsn}, \sigma, R) \rangle$ \textbf{to} $C$
            \EndFor
            \State \textbf{increment} $\textsf{nextsn}$
        \Else
            \State $\textsf{log}[m] \gets False$
        \EndIf
    \EndIf
\EndUpon

\end{algorithmic}
\label{alg:uc-validator}
\end{algorithm}

Upon initialization, a validator resets its state. When a validator establishes a connection with a new client, it adds the client to its set of connected clients and shares all the votes currently stored in its log with the client.

When a validator receives a new claim $m$ for verification, it executes the claim verification predicate $\textbf{verify}(m)$ to decide on the claim's validity. If the claim is valid, the validator creates a new signed vote attesting to the claim's validity, attaches to its log, forwards the vote to all connected clients and increments its $\textsf{nextsn}$ counter. Otherwise, it records the verification failure result in the log.

\subsubsection{Correctness}

The security of the \UC{} is defined by the following theorems. Recall that a claim $m$ is valid iff $\textbf{verify}(m) = 1$.

\begin{theorem}{(\textbf{Correctness})}:
    Invalid claims are never finalized in the view of an honest client.
\end{theorem}
Note that an invalid claim may appear as a pending claim in some views, but it is never finalized.

\begin{theorem}{(\textbf{View consistency within u})}:
During (partial) synchrony with network delay $\delta$, if an honest client observes that a claim m is finalized, then it will be observed as finalized by all other honest clients within $u = 2\delta$.
\end{theorem}
When the network is asynchronous, finalized claims are eventually observed by all honest clients. This is a fundamental (liveness) property that guarantees consistency of honest client views with respect to finalized claims. Note that this consistency requirement does not necessarily hold for pending claims. An important consequence of this property is that it is enough for an external user to read the state of one honest client to know with certainty whether a claim has been finalized.

In the following, recall that $\tau$ is an upper bound on the time needed to execute the claim verification procedure $\textbf{verify}(m)$.

\begin{theorem}{\textbf{(Finalization within w)}}:
During (partial) synchrony with network delay $\delta$, valid claims become finalized within $w = 2\delta + \tau$.
\end{theorem}
When the network is asynchronous, valid claims are eventually finalized. This is a liveness property that guarantees progression of the finalized claim set in honest client views as long as valid claims are being generated and submitted to validators.

\subsubsection{\UC{} vs. Pod}

Although the \UC{}'s design draws directly from the Pod framework, there are some fundamental distinctions between the two. The first major difference is time-stamping votes. In Pod, transaction votes are timestamped, enabling the specification of (potential) causal dependencies between transactions. Specifically, if the timestamp interval (minimum to maximum) of transaction  $T_1$  entirely precedes that of  $T_2$ ,  $T_2$  may be causally dependent on  $T_1$ . In contrast, the \UC{} does not use timestamps for claim votes, making all claims concurrent and eliminating the concept of causal dependency. Conceptually, one could view \UC{} claim votes as being timestamped with the unbounded interval  $(-\infty, \infty)$ , effectively rendering all claims concurrent, both with past and future claims.

Another key distinction is that the notion of past-perfection in Pod degenerates into the set of finalized claims in the \UC{}. In pod, the past-perfection safety property ensures that any transaction confirmed before a past-perfect round for an honest client must have already appeared in the view of that client. In other words, transactions with earlier (confirmed) timestamps cannot appear retroactively in the view of an honest client. This is an important property for causally dependent transactions. In \UC{}, there is no notion of causal dependency since claims are unordered. Instead of a monotonically increasing past-perfect round, we have a monotonically increasing set of finalized claims in the \UC{}. Furthermore, if a claim is finalized in an honest client view, it must eventually appear in the finalized set of other honest clients.

\subsection{Optimizations and Extensions}
\label{sec:optimizations}

In this section, we highlight some optimizations and extensions relevant to the \UC{} as a set consensus protocol.

\subsubsection{Fast Set Reconciliation} 

As the \UC{} is based on maintaining sets of validator votes, proposed claims and finalized claims, nodes  in the network will constantly have to process overlapping sets and will need to efficiently identify and synchronize the differences. For example, a client in the \UC{} needs to update its view periodically, which involves updating the set of validator votes it maintains for each claim in its state. Efficient ways for nodes to reconcile their sets without prior knowledge of the set differences’ size can significantly reduce computational and communication overhead and improve performance and scalability.

A recent fast set reconciliation algorithm, called Rateless Invertible Bloom Lookup Tables (Rateless IBLT)~\cite{YangYGA:2024}, efficiently addresses the set reconciliation problem. At its core, this problem involves two parties, each possessing distinct sets of fixed-length bit strings, aiming to identify and exchange the differing elements between their sets.

Rateless IBLT stands out by offering low computational overhead and near-optimal communication costs across a broad spectrum of scenarios. It effectively manages set differences ranging from a single element to millions, accommodates bit strings varying from a few bytes to megabytes, and remains robust even under workloads introduced by potential adversaries.

The core innovation of Rateless IBLT lies in its encoder, which incrementally encodes the set difference into an infinite stream of coded symbols, akin to rateless error-correcting codes. This design allows the protocol to adaptively adjust to varying set differences without prior knowledge of their size.

Therefore, in our context, instead of broadcasting or gossiping raw sets (e.g. votes and claims), nodes encode their state using Rateless IBLT and share these lightweight encodings. Receiving nodes decode the received encodings, extract missing elements, and update their local views without unnecessary data transfer.

\subsubsection{Coding for Full BFT Agreement} 

Coding theory offers a powerful set of tools to improve distributed protocols. In particular, modern rateless coding schemes designed for distributed storage~\cite{RawatRVBS:2011,NicolaouNCPTKML:2022} offer significant benefits spanning compression, resilience, storage efficiency, and network optimization. They can potentially enable an alternative design for the \UC{} where full BFT consensus can be efficiently achieved at a large scale. 

\paragraph{Compression:} 
Rateless encoding reduces redundancy by combining state data into coded symbols, compressing information and minimizing transmission overhead based on the data’s inherent redundancy.

\paragraph{Resilience:} 
Rateless encoding enhances resilience in unreliable or Byzantine environments by using coded symbols to correct errors and maintain data integrity despite adversarial interference.

\paragraph{Storage efficiency:} 
Rateless encoding enhances fault tolerance in distributed storage by enabling data reconstruction from encoded symbols, ensuring reliability despite node failures or churn, without requiring persistent storage.

\paragraph{Network optimization:}
Rateless encoding optimizes data propagation in peer-to-peer networks by replacing inefficient flooding with coded symbol exchange, reducing message overhead and enabling faster, more efficient dissemination.

This paper~\cite{ChoiCSHM:2019} demonstrates a practical application of coding techniques within a BFT consensus protocol. It leverages rateless coding to reduce the size of data that need to be exchanged in the different phases of the BFT protocol. This and similar work exemplify how coding-based techniques can address the dual challenges of efficiency and security in decentralized consensus, making it an inspiration for adopting similar approaches in the \UC{}.

\subsubsection{Efficient Decentralized Data Dissemination}

Nodes in the \UC{} and other decentralized systems must efficiently and reliably read and write state data when verifying claims or transactions. This ensures optimal performance and resilience across the network. Optimum~\cite{OptimumO:2024} is a protocol that addresses this particular challenge of efficient data access and manipulation. Systems may integrate with the Optimum Network via an API or establish private networks using Flexnode Clients. For validators, the FlexNode client handles data reads (e.g., reading account balances) and data writes (e.g., updating smart contract states) efficiently, decreasing the operational costs of validators.

The underlying technology of Optimum is a novel erasure code, named Random Linear Network Coding (RLNC). RLNC divides the original data into smaller segments. Multiple segments are encoded into a number of linear combinations or blocks. The encoded blocks are transmitted independently to a subset of the other nodes in the network. Upon receiving a sufficient number of encoded blocks, nodes can reconstruct the original data by solving a system of linear equations derived from the received blocks, even if some blocks were lost or damaged in transit.

RLNC offers key advantages over traditional coding: it enables data reconstruction from partial encoded blocks, ensuring reliability amid failures; reduces network bandwidth by avoiding full block transmission; allows independent, parallel reconstruction without consensus, enhancing throughput; and significantly lowers latency, especially in high-loss networks.

We anticipate that integrating Optimum with the \UC{} could potentially improve the consensus mechanism by ensuring faster and more reliable and robust data dissemination among validators.

\subsection{Key Challenges}

Below, we outline the key challenges we anticipate.

\subsubsection{Extreme Scalability}

Entities of various kinds, including blockchains, AI agents, centralized systems and humans, will be able to generate claims of varying complexities at very high rates. The USL validator network will potentially need to handle an unprecedented influx of claims—potentially millions or tens of millions per second—submitted simultaneously by diverse sources. This creates a multifaceted challenge, demanding a system that can deliver high throughput, maintain low latency, provide efficient storage, scale dynamically with load, and ensure robust security while processing claims of varying types and priorities.

\begin{itemize}
    \item \textbf{Network optimization}: Optimize the underlying network with efficient communication protocols (such as the optimizations highlighted in Section~\ref{sec:optimizations} above), routing algorithms, and redundancy measures to handle the high rate of claim submission and propagation.
    \item \textbf{Modular architecture}: Implement a modular validator architecture where different modules handle specific claim types. This specialization allows efficient processing tailored to the claim’s nature and complexity.
    \item \textbf{Parallelization and sharding}: As claims are independent, utilize parallel processing and sharding techniques to distribute the workload across multiple validators. Each shard or processing unit can handle a subset of claims, significantly improving throughput.
    \item \textbf{Zero-Knowledge proofs}: Leverage advanced cryptographic methods like Zero-Knowledge Proofs (ZKPs) to validate claims with minimal computational overhead while ensuring privacy and security.
    \item D\textbf{ecentralized reputation and incentive systems}: Introduce reputation and incentive mechanisms to encourage validators to process claims efficiently and penalize nodes that act maliciously or are consistently slow.
\end{itemize}


\subsubsection{Supporting Application-Specific Properties}
\label{sec:use-cases}

Claims are versatile structures representing various application-specific assertions, such as token transfers, computation results, or mathematical proofs. The \UC{} enables consensus on verifiably true claims while abstracting away their verification semantics. It focuses solely on claim validity, delegating application-specific safety properties—such as double-spending prevention in wallets—to the application layer.

Nevertheless, certain classes of safety properties are so critical and ubiquitous across applications that they warrant dedicated solutions built on top of the \UC{}. Examples include enforcing a total ordering of state transitions in a traditional blockchain system (to support swaps in a decentralized exchange, for instance), preventing double-spending in wallet applications (a partial order property), or ensuring that late votes arriving after a deadline are excluded in voting systems. These properties, while not directly handled by the \UC{}’s core consensus mechanism, are common enough that designing tailored solutions leveraging the \UC{} for their enforcement will be essential for many practical applications. To illustrate this concept, we elaborate on these three use cases below.

\paragraph{Chains (Total ordering)\\}
Consider an app-chain that aims to enforce a total ordering on its transactions to be able to support its decentralized exchange functionality. Such an app-chain might generate a claim asserting its current state at time $t$ as $s$, represented by the predicate $\textit{state}(s, t)$. The proof for this claim would rely on the validity of two prior claims:

\begin{enumerate}
    \item $\textit{state}(s_0, t_0)$, with $t_0 < t$: This claim states that the latest recorded application state was $s_o$ at time $t_o$, where $t_o$ is the greatest timestamp among all prior state claims.
    \item $\textit{transition}(s_0, \text{block}, s)$: This claim asserts the transactions in $\text{block}$ were executed to transition the app-chain from state $s_0$ to $s$, and there was no other transition claim that started at $s_0$.
\end{enumerate}

Using this methodology, attempts to double-spend or manipulate the exchange rates of pools, for example, can be prevented by ensuring that validators verify that, at any given time, the app-chain has a unique claim of the form $\text{state}(s, t)$ for a specific state $s$. This methodology effectively simulates the chain using claim primitives ensuring that violations of safety as proved by the app-chain are not possible. 

Note that this approach requires validators to access the complete states of the app-chains they are validating. This aligns with the responsibilities of validators in existing blockchain systems, which also maintain and verify state information. Consequently, it does not place any additional burden on validators beyond what is already expected in current blockchain frameworks. However, cryptographic techniques, such as zero-knowledge proofs, could be leveraged to develop more efficient validation methods.

\paragraph{Payments (Partial ordering)\\}
Consider a payment application, such as a digital wallet, where accounts can send and receive payments. To ensure proper functionality, the application must enforce a partial order on transactions, preventing any account from overspending. At the same time, it should allow different accounts to operate independently, enabling them to spend from their individual balances without interference.

The application may generate claims of the form $\textit{remitted}(A, \alpha, x, b, t)$, with $A$ the account making or receiving a payment, $\alpha \in \{ \text{pay}, \text{receive}\}$ the remittance type, $x \geq 0$ the remittance amount, $b \geq 0$ the new account balance, and $t$ the time of remittance. The claim states that, at time $t$, account $A$ paid or received an amount $x$ of tokens resulting in a new balance of $b$. Note that with this encoding, the application will be generating claims in pairs, one for each of the source and target accounts. We chose this form of encoding for its simplicity.

To prevent overspending, verifying a claim of the form $\textit{remitted}(A, \text{pay}, x, b, t)$ would require having a claim of the following form already finalized: 
$$\textit{remitted}(A, \alpha, y, x + b, t_0)$$
with $t_0 < t$ and $t_0$ greater than the timestamps of all remittance claims finalized for account $A$. That is, validators would need to ensure that the account most recently made or received a payment for some amount resulting in a new balance equal to $x + b$. Note that claims of payments for other accounts can be made in parallel and are independent of other claims for $A$, hence the partial order on payments.

\paragraph{Voting (No ordering)\\}
Consider a voting application in which users may submit votes for candidates up to a prescribed deadline. Votes that arrive after the deadline are not counted. The candidate who meets the vote threshold wins (we assume ties are not possible for simplicity). Note that the order in which votes arrive is immaterial.

The application may generate claims of the following forms:
\begin{itemize}
    \item $\textit{voting\_session}(S, \tau, \kappa)$: The voting session identified by $S$ with deadline $\tau$ and winning threshold $\kappa$ started.
    \item $\textit{voted}(S, A, C, t)$: In session $S$, user $A$ voted for candidate $C$ at time $t$.
    \item $won(S, C)$: In the voting session $S$, the candidate $C$ won.
\end{itemize}

To verify a winning candidate claim $won(S, C)$, we require the protocol to have already achieved consensus on the following claims:
\begin{enumerate}
    \item $\textit{voting\_session}(S, \tau, \kappa)$, that the voting session was started before with the given parameters
    \item $|\{ \textit{voted}(S, x, C, t) | x \text{ is a valid account } \land t \leq \tau\} ~|~ \geq \kappa$, that the number of valid votes for candidate $C$ received by the voting session's deadline has meet the required threshold.
\end{enumerate}
Note that the verification conditions do not require having the votes received in any particular order.



\section{Conclusion}

The Pi Squared Universality Stack introduces a novel approach to addressing the fundamental challenges of blockchain interoperability, scalability, and developer accessibility. By decoupling execution, settlement, and consensus through its three-tiered architecture—comprising the Universal Settlement Layer (USL), the Universal Language Machine (ULM), and the \UniCon{} (\UC{})—this framework overcomes the inefficiencies and limitations of traditional monolithic and severely siloed blockchains. The USL establishes a robust and verifiable foundation for cross-chain interaction, the ULM removes language restrictions in smart contract development, and the \UC{} unlocks massive parallelism by eliminating unnecessary ordering constraints in consensus.

With this modular and extensible design, Pi Squared’s approach fosters a more interconnected, scalable, and inclusive decentralized ecosystem. Developers are no longer constrained by ecosystem-specific languages or execution environments, and applications can seamlessly interact across blockchains without relying on insecure and inefficient bridging mechanisms. Furthermore, by redefining consensus beyond global transaction ordering, the \UC{} enables new classes of scalable and parallelizable decentralized applications, ranging from scientific computation verification to multi-agent coordination.

Future work on the Universality Stack will focus on further refining each of its components to maximize efficiency, security, and usability. In the USL, ongoing research aims to define additional classes of claims capturing a wider range of applications, and to optimize proof mechanisms for greater efficiency to minimize verification costs while maintaining security. Expanding the ULM’s language support will also be a priority, ensuring seamless integration for a wider range of programming languages and improving developer tooling to enhance adoption. Additionally, future research on the \UC{} will focus on formally analyzing its core properties and their relation to Pod, exploring its evolution into a full BFT consensus protocol without sacrificing efficiency or scalability, and developing optimized implementations, leveraging techniques like coding-based methods to enhance performance and scalability.


\section{Demo}
We presented the 2 demos about the USL and the ULM at ETH Denver 2025.
\begin{itemize}
   \item \href{https://pi2.network/videos/USL-Wormhole-Devcon-7}{Universal Settlement Layer (USL)} The video covers the demo of the USL integrating with the Wormhole's NTT framework to implmement a token bridge from Sepolia to Arbitrum Sepolia network.
  \item \href{https://pi2.network/videos/ULM-Devcon-7}{Universal Language Machine (ULM)} The video covers the demo about the ULM's functionality: deploying languages, deploying contracts and a simple swap that involves contracts written in multiple languages.
\end{itemize}

\bibliographystyle{plain}
\bibliography{refs}

\end{document}

```

