You are reviewing a complete first draft of a mathematics paper together with the formalisation it cites. The paper subsumes an earlier paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor") and is written for smooth data throughout; the Taylor-tree material of the earlier paper has been dropped by design.

Please review in four passes and be concrete (quote the sentence, say what is wrong, say what to write instead).

1. MATHEMATICAL FIDELITY. Every displayed formula and every claim in the prose: is it correct as stated, with the stated hypotheses? Pay particular attention to (a) constants and normalisations in the stratum measure / weighted logarithmic residue (factors of 2k_j, Γ(μ)/(c−1)!, 2^c for interior walls, the one-variable sanity check), (b) the three tiers in §7.9 and §9.4 (finite-part formula, the x²y² tie computation of c_{1/2,0} including signs, the x²y⁶ example numbers 1/6, 1/3, 1/2 and the claimed integrability of x^{-1/3}, x^{-2/3}), (c) the parity remark and the choice W=[0,1]² in Example 2.2 (are odd corrections really zero on symmetric domains? is the claim about the first nonzero correction being the one with the logarithm right?), (d) the blow-up example x²(x−y)² (data (k,h), which components meet, ratios), (e) the Gaussian average formula and the threshold v<2, (f) the two-site identity, (g) the quotient theorem remainder exponent (d−1)(J+1), (h) the statement that Weber's equation appears as stated (check the substitution S_μ(a)=e^{a²/8}f(a/√2) and the closed form via D_{−2μ}), (i) the claim that the leading empirical posterior expectation is independent of the sample when the leading stratum is a point.

2. FORMALISATION TABLE (§13). Below the paper you will find the Lean signatures of every declaration named in Table 1, extracted from the source. Check each row: does the named declaration state what the row says, with the hypotheses the row lists? Flag mismatches (wrong name, hypothesis omitted or misdescribed, statement stronger than the Lean). Also flag any statement in the body of the paper that is presented as a theorem but for which no formal counterpart is cited and which you believe is not proved in the literature either.

3. STRUCTURE AND EXPOSITION. The intended style is that of a conceptual primer: introduce machinery when it is needed, motivate every definition by the computation it enables, coordinate-free statements first with chart formulas as computations, three recurring actors (observable, strata, data). Where does the draft fail this? What is redundant between sections (e.g. §4.3 wall-crossing vs §7.10; §7.9 tiers vs §9.4)? What is missing that a reader would need (e.g. is the definition of the exact stratum before the graded formula clear; is the passage from moment tensors to stratum measures motivated)? Are the running examples used consistently? Is anything in Part IV out of place?

4. PRIORITISED FIX LIST. Ten items, most important first, each one sentence.

Do not rewrite the paper. Do not praise. Be specific.

============ THE PAPER (LaTeX; main.tex followed by the section files in order) ============
\documentclass[11pt]{article}
\usepackage[margin=1.1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{tikz}
\usetikzlibrary{arrows.meta,calc,positioning,decorations.pathreplacing,shapes.geometric}
\usepackage{booktabs}
\usepackage{array}
\usepackage[round]{natbib}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=blue!60!black,citecolor=blue!60!black,urlcolor=blue!60!black}
\usepackage[capitalise,noabbrev]{cleveref}
\crefname{thm}{Theorem}{Theorems}
\crefname{prop}{Proposition}{Propositions}
\crefname{lem}{Lemma}{Lemmas}
\crefname{cor}{Corollary}{Corollaries}
\crefname{defn}{Definition}{Definitions}
\crefname{remark}{Remark}{Remarks}
\crefname{example}{Example}{Examples}
\crefname{equation}{}{}

\newtheorem{thm}{Theorem}[section]
\newtheorem{prop}[thm]{Proposition}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{cor}[thm]{Corollary}
\newtheorem{defn}[thm]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[thm]{Remark}
\newtheorem{example}[thm]{Example}

\DeclareMathOperator{\Cov}{Cov}
\DeclareMathOperator{\Var}{Var}
\newcommand{\E}{\mathbb E}
\newcommand{\R}{\mathbb R}
\newcommand{\N}{\mathbb N}
\newcommand{\Zcal}{\mathcal Z}
\newcommand{\Dn}{\mathcal D_n}
\newcommand{\Rres}{\mathcal R}
\newcommand{\Ical}{\mathcal I}
\DeclareMathOperator{\res}{res}

\title{Expectations and the Exceptional Divisor}
\author{Daniel Murfet}
\date{September 2026}

\begin{document}
\maketitle

\begin{abstract}
The expectation of an observable $f$ under the Bayesian posterior of a singular statistical model is the ratio $Z_n[f]/Z_n[1]$ of two partition functions with insertion. We give the complete asymptotic expansion of $Z_n[f]$ in the sample size $n$, for the population divergence and for the empirical loss of a fixed sample, and describe its coefficients without coordinates. After resolution of singularities the zero locus of the divergence becomes a normal crossing divisor with a stratification, and every coefficient is a distribution on a stratum of the exceptional divisor paired with the observable: at leading order a measure, the weighted logarithmic residue of the resolved integrand along the deepest stratum of lowest exponent, and at higher orders the pairing of finitely many normal derivatives of the observable with residue data of higher order. The sample enters through Watanabe's standard form as a field on the resolution, and its whole effect is to replace the Gamma function in the stratum measures by the fluctuation function of the field along the stratum, with derivatives of the field entering the corrections through a ladder of indices. Posterior expectations are quotients of these expansions, and their coefficients are rational functions of the same data. The analysis is carried out for smooth priors and observables throughout, the running examples are worked in detail, and the statements have been formalised in the Lean theorem prover; a table records what is a theorem and under which hypotheses.
\end{abstract}

\tableofcontents

\part{The question and the geometry}
\input{sections/01_introduction}
\input{sections/02_setting}
\input{sections/03_resolution}
\input{sections/04_stratification}

\part{Population expectations, coordinate-free}
\input{sections/05_normal_geometry}
\input{sections/06_moment_tensors}
\input{sections/07_population}

\part{The data}
\input{sections/08_fluctuation}
\input{sections/09_empirical}
\input{sections/10_limit}

\part{Expectations}
\input{sections/11_posterior}
\input{sections/12_averaging}
\input{sections/13_formalisation}
\input{sections/14_conclusion}

\bibliographystyle{plainnat}
\bibliography{references}

\appendix
\input{sections/A_chart_proofs}
\input{sections/B_fluctuation_facts}
\input{sections/C_expansion_algebra}
\input{sections/D_resolution_facts}

\end{document}

%%%%%%%%%% FILE sections/01_introduction.tex %%%%%%%%%%
\section{Introduction}\label{sec:introduction}

A statistical model $p(x\mid w)$ with parameter $w\in W\subseteq\R^d$ fits a ground truth $q$ to the extent measured by the Kullback--Leibler divergence
\[
K(w)=\int q(x)\log\frac{q(x)}{p(x\mid w)}\,dx\,.
\]
Given $n$ samples $\Dn$ the Bayesian posterior concentrates near the zero locus $W_0=\{K=0\}$, and the point of view of singular learning theory \citep{watanabeAlgebraicGeometryStatistical2009,watanabe2018} is that the local geometry of $K$ along $W_0$ is where the information about what the model has learned resides. That geometry is not directly visible. What is visible, and what a growing body of empirical work actually measures, are posterior expectation values
\[
\E[f\mid\Dn]=\frac{Z_n[f]}{Z_n[1]},\qquad Z_n[f]=\int_W f(w)\,e^{-nL_n(w)}\,\varphi(w)\,dw ,
\]
of chosen observables $f$: the local learning coefficient estimator, susceptibilities of model components to perturbations of the data, per-sample influences. The question this paper answers is what a \emph{single} such expectation value sees.

The answer has a definite shape. As $n\to\infty$ the partition function with insertion has an asymptotic expansion
\begin{equation}\label{eq:intro_answer}
Z_n[f]\;\sim\;\sum_{\mu}\sum_{q}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q ,
\end{equation}
in which the exponents $\mu$ and the powers of the logarithm are read off a resolution of the singularities of $K$, and each coefficient $c_{\mu,q}$ is a \emph{distribution supported on a stratum of the exceptional divisor}, paired with $f$. Three actors appear in this formula, and the paper is organised around them.

\begin{itemize}
\item \textbf{The geometry.} Resolution of singularities replaces $W_0$ by a normal crossing divisor $E=E_1\cup\cdots\cup E_r$ on a manifold $U$ mapping onto $W$. Its components intersect along a stratification, and to each component are attached two integers: the order $2k_i$ to which $K$ vanishes along it and the order $h_i$ to which the prior measure does. The ratios $(h_i+1)/2k_i$ are the exponents; the strata along which several components meet with a common ratio are where the logarithms come from. Every coefficient in \eqref{eq:intro_answer} is a measure, or a distribution built from a measure and finitely many normal derivatives, living on one of these strata. This is the \emph{stratum measure} of the pair $(K,\varphi)$ at a given exponent and depth, and it is a coordinate-free object: the weighted logarithmic residue of the resolved integrand along the stratum.
\item \textbf{The observable.} The coefficients are linear in $f$. The leading coefficient pairs the stratum measure with the restriction of $f$ to the stratum; the corrections pair it with the normal derivatives of $f$ along the stratum, organised as sections of symmetric powers of the conormal bundle. An observable that vanishes along a stratum does not see it at the leading order and is instead seen at a shifted exponent, which is the mechanism by which different observables probe different parts of the singular locus.
\item \textbf{The data.} Replacing the population divergence $K$ by the empirical loss $L_n$ introduces a random field on the resolution, the standardised empirical process, and the whole effect of the sample on the expansion is that the Gamma function in the stratum measures is replaced by a \emph{fluctuation function} $S_\mu$ evaluated on that field along the stratum, with its derivatives entering the corrections in a rigid ladder. For a fixed sample the expansion is deterministic and the coefficients are functionals of finitely many jets of the field on the strata; as the sample grows the field converges to a Gaussian process and the coefficients converge with it.
\end{itemize}

Posterior expectations are quotients of two such expansions, for $f$ and for $1$, and therefore rational functions of the same coefficients. At leading order the posterior concentrates on the deepest strata of lowest exponent, weighted by the stratum measures and, in the empirical case, reweighted by the fluctuation function evaluated on the data. When several strata tie, the sample decides how the posterior mass is distributed between them.

None of this requires analyticity of the observable or of the prior, and the paper is written for smooth data throughout. The expansion, its coefficients, and the passage to the Gaussian limit have been formalised in the Lean theorem prover; a table of what is a theorem, with hypotheses, is given in \cref{sec:formalisation}, together with what is not.

\paragraph{Plan.} \cref{sec:setting} fixes the setting, the notion of asymptotic expansion in the scale $n^{-\mu}(\log n)^q$, and the running examples. \cref{sec:resolution,sec:stratification} introduce the resolution and the stratification of its exceptional divisor at a gentle pace. Part~II develops the population expansion without coordinates: the normal geometry of a stratum (\cref{sec:normal_geometry}), moment tensors and the conormal presentation of the coefficients (\cref{sec:moment_tensors}), and the stratum measures with the zeta function that organises all orders (\cref{sec:population}). Part~III introduces the data: the fluctuation function (\cref{sec:fluctuation}), the expansion for a fixed sample (\cref{sec:empirical}), and the Gaussian limit (\cref{sec:limit}). Part~IV treats expectations: the posterior quotient (\cref{sec:posterior}), averaging over the sample (\cref{sec:averaging}), and the formalisation (\cref{sec:formalisation}).

\paragraph{Notation.} $W\subseteq\R^d$ is the parameter space, $K$ the divergence, $L_n$ the empirical loss, $\varphi$ the prior density, $f$ an observable. $\Zcal_n[f]=\int f\,e^{-nK}\varphi\,dw$ is the population partition function with insertion and $Z_n[f]=\int f\,e^{-nL_n}\varphi\,dw$ the empirical one; $\pi\colon U\to W$ is the resolution, $E_i$ the components of the exceptional divisor with data $(k_i,h_i)$, $S_I=\bigcap_{i\in I}E_i\setminus\bigcup_{j\notin I}E_j$ the strata, $\lambda_I=\min_{i\in I}(h_i+1)/2k_i$ the exponent of a stratum and $m_I$ its multiplicity. Near a stratum $(v,u)$ are tangential and normal coordinates. $S_\mu$ is the fluctuation function and $\zeta$ the field on the resolution.

%%%%%%%%%% FILE sections/02_setting.tex %%%%%%%%%%
\section{Setting and the running examples}\label{sec:setting}

\subsection{Partition functions with insertion}

The parameter space $W\subseteq\R^d$ is compact with nonempty interior, cut out by finitely many real analytic inequalities. The model $p(x\mid w)$ and the truth $q(x)$ are probability densities with a common support, and the truth is realisable: $W_0=\{w\in W: K(w)=0\}$ is nonempty. We assume $K$ is real analytic on a neighbourhood of $W$ and nonnegative there, as a divergence is, and that the prior $\varphi\ge0$ is smooth with compact support and positive on a neighbourhood of $W_0$. The observables $f$ are smooth functions on a neighbourhood of $W$. Nothing in the paper requires $\varphi$ or $f$ to be analytic, and \cref{sec:resolution} explains why $K$ is the one function for which analyticity is used.

The population partition function with insertion and the corresponding expectation are
\[
\Zcal_n[f]=\int_W f(w)\,e^{-nK(w)}\varphi(w)\,dw,\qquad \E_\infty[f]=\frac{\Zcal_n[f]}{\Zcal_n[1]} .
\]
Given a sample $\Dn=\{x_1,\dots,x_n\}$ from $q$, the empirical loss $L_n(w)=-\frac1n\sum_i\log p(x_i\mid w)$ defines the empirical partition function with insertion and the Bayesian posterior expectation
\[
Z_n[f]=\int_W f(w)\,e^{-nL_n(w)}\varphi(w)\,dw,\qquad \E[f\mid\Dn]=\frac{Z_n[f]}{Z_n[1]} .
\]
Since $L_n(w)-L_n^{\min}$ is, up to the constant $\frac1n\sum_i\log q(x_i)$, the empirical divergence $K_n(w)=\frac1n\sum_i\log\frac{q(x_i)}{p(x_i\mid w)}$, the factor $e^{-nL_n^{\min}}$ cancels in the quotient and we may and do write $Z_n[f]=\int f\,e^{-nK_n}\varphi\,dw$. An inverse temperature $\beta$ in front of $nL_n$ changes nothing structurally and is absorbed into $n$ and into the field introduced below; we keep $\beta=1$.

\subsection{The standard form of the empirical divergence}

The difference between $K_n$ and $K$ is a fluctuation of order $n^{-1/2}$, but not uniformly: near $W_0$ the difference is itself small because the terms being summed are. Watanabe's standard form makes this precise. Define the empirical process
\[
\psi_n(w)=\frac1{\sqrt n}\sum_{i=1}^n\frac{K(w)-\log\big(q(x_i)/p(x_i\mid w)\big)}{\sqrt{K(w)}},\qquad w\notin W_0 ,
\]
so that, identically in $w\notin W_0$,
\begin{equation}\label{eq:standard_form}
K_n(w)=K(w)-\frac1{\sqrt n}\sqrt{K(w)}\,\psi_n(w) .
\end{equation}
The process $\psi_n$ has mean zero and is not defined on $W_0$ as written, but on the resolution of $K$ it extends to a smooth function \citep[Main Theorem~6.1]{greybook}, and this extended process converges in law to a Gaussian process as $n\to\infty$. Everything the sample does to the expansions of this paper is done through the exponent
\[
-nK_n=-nK+\sqrt n\,\sqrt K\,\psi_n ,
\]
and on the resolution, where $\sqrt{K\circ\pi}$ is a monomial, this is the exponent $-nu^{2k}+\sqrt n\,u^k\,\zeta(u)$ of a one-parameter family of integrals that we will analyse in complete generality. The field $\zeta$ is the sample; the rest is geometry.

\subsection{Asymptotic expansions in the scale \texorpdfstring{$n^{-\mu}(\log n)^q$}{n^-mu (log n)^q}}\label{sec:scale}

We follow \citet[Ch.~1]{paris2001asymptotics}. The functions $n^{-\mu}(\log n)^q$ with $\mu\in\mathbb Q_{>0}$ and $q\in\N$ are totally ordered by eventual domination: $n^{-\mu}(\log n)^q$ dominates $n^{-\mu'}(\log n)^{q'}$ when $\mu<\mu'$, or $\mu=\mu'$ and $q>q'$. We write $(\mu,q)\prec(\mu',q')$ in that case. For a discrete set $\mathcal A\subseteq\mathbb Q_{>0}$ and $D\in\N$,
\[
F(n)\sim\sum_{\mu\in\mathcal A}\sum_{q=0}^{D}c_{\mu,q}\,n^{-\mu}(\log n)^q
\]
means that for every $(\mu',q')$ the difference $F(n)-\sum_{(\mu,q)\prec(\mu',q')}c_{\mu,q}n^{-\mu}(\log n)^q$ is $O(n^{-\mu'}(\log n)^{q'})$. Such an expansion, if it exists, determines its coefficients uniquely, and adding a term $O(e^{-\varepsilon n})$ changes nothing. All expansions in this paper have the additional property that the exponents lie on a lattice $Q^{-1}\N$ for an integer $Q$ determined by the resolution, and the logarithmic degree is bounded by $d-1$. In that situation the expansion is equivalent to the family of \emph{cutoff estimates}
\begin{equation}\label{eq:cutoff}
F(n)=\sum_{\mu\in Q^{-1}\N,\ \mu<U}\ \sum_{q\le D}c_{\mu,q}\,n^{-\mu}(\log n)^q+O\big(n^{-U}(1+\log n)^{D}\big),\qquad U>0 ,
\end{equation}
one for each cutoff $U$, with coefficients independent of $U$. This is the form in which the theorems are stated and proved; it is also the form that the formalisation uses.

Two facts about expansions in this scale are used repeatedly and are recorded in \cref{app:expansion_algebra}: the product of two expansions is an expansion with the convolved coefficients, and the quotient of two expansions is an expansion provided the denominator's leading block, the polynomial in $\log n$ multiplying its lowest power of $n$, is nonzero. The quotient's coefficients are rational functions of $\log n$ whose numerators and denominators are built from the two coefficient systems by formal division in the variable $x=n^{-1/Q}$. Posterior expectations are such quotients.

\subsection{Comparability}

The divergence is analytic but rarely polynomial. Two nonnegative functions $g_1,g_2$ on an open set are \emph{comparable}, $g_1\asymp g_2$, if $c_1g_2\le g_1\le c_2g_2$ for positive constants. Comparable functions have the same vanishing orders along every component of a common resolution \citep[App.~B]{murfet2025programssingularities}, hence the same exponents and multiplicities in the expansions below, and in examples one routinely replaces $K$ by a comparable polynomial. The coefficients do change under such a replacement; the exponents and logarithms do not.

\subsection{The running examples}\label{sec:examples}

Two examples accompany the whole paper. Both have a divergence that is already a monomial, so that the resolution is the identity and the geometry can be seen without any machinery; \cref{sec:resolution} adds an example where a blow-up is genuinely needed.

\begin{example}[Two planes meeting along a line]\label{ex:planes}
Let $W=[-1,1]^3$ with coordinates $(x,y,z)$ and $K(x,y,z)=x^2y^2$, with a smooth positive prior $\varphi$. The zero locus is the union of the two planes $\{x=0\}$ and $\{y=0\}$, meeting along the $z$-axis. Along each plane $K$ vanishes to order $2$ and the prior measure to order $0$, so each carries the ratio $1/2$; along the axis both planes meet with the same ratio. We will see that $\Zcal_n[1]\sim C\,n^{-1/2}\log n$, that the logarithm is the signature of the axis, and that the leading coefficient is an integral of the prior along the axis: the posterior concentrates on the line $\{x=y=0\}$. An observable $f(x,y,z)$ is seen at leading order only through its restriction to the axis, $f(0,0,z)$; an observable vanishing on the axis, such as $f=x^2$, is seen at a higher exponent and only through its normal derivatives.
\end{example}

\begin{example}[Mixed exponents]\label{ex:mixed}
Let $W=[0,1]^2$, a model whose two parameters are constrained to be nonnegative, with $K(x,y)=x^2y^6$. The two lines $\{x=0\}$ and $\{y=0\}$ are now walls of the parameter space and carry the ratios $1/2$ and $1/6$. The line $\{y=0\}$ leads, alone, so $\Zcal_n[1]\sim C\,n^{-1/6}$ with no logarithm; the first correction sits at $n^{-1/3}$ and is again carried by $\{y=0\}$ alone, through the first normal derivative of the amplitude; the second correction, at $n^{-1/2}$, is where the line $\{x=0\}$ first resonates, and a logarithm appears there. This example exhibits the three tiers of \cref{sec:population} in sequence. The nonnegativity constraint is not decoration: on a symmetric domain such as $[-1,1]^2$ the odd normal moments cancel between the two sides of a wall, the first correction vanishes identically, and the first nonzero correction is the one with the logarithm (\cref{rem:parity}).
\end{example}

In both examples the same three actors are visible: the strata (the axis and the two planes, or the two lines and the origin), the observable through its restriction and normal derivatives, and, once the sample is introduced, the field through the fluctuation function on the leading stratum.

%%%%%%%%%% FILE sections/03_resolution.tex %%%%%%%%%%
\section{Resolution and the exceptional divisor}\label{sec:resolution}

The integrals $\Zcal_n[f]$ concentrate, as $n\to\infty$, on the zero locus $W_0$ of $K$, and their asymptotics are governed by how $K$ vanishes there. In general $W_0$ is a singular set and $K$ vanishes along it in an intricate way. Resolution of singularities is the device that replaces this situation by a standard one: after a proper change of variables $\pi\colon U\to W$, the function $K\circ\pi$ vanishes along a union of smooth hypersurfaces meeting transversally, and near every point it is a monomial in suitable coordinates. This section states the resolution theorem in the form we use and explains what the local picture looks like.

\subsection{The theorem}

We work with the complexification: $K$ is the restriction to $W$ of a holomorphic function $K_{\mathbb C}$ on an open set $W^{(\mathbb C)}\subseteq\mathbb C^d$ containing $W$ \citep[Fundamental Condition~I]{watanabe2018}. By Hironaka's theorem \citep{hironaka1964resolution1,bierstone1997canonical}, in the form given by \citet[\S11.3]{igusa2000introduction}, there exist a $d$-dimensional complex manifold $U_{\mathbb C}$, a proper holomorphic map $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$ which is an isomorphism over the complement of $\{K_{\mathbb C}=0\}$, and a finite set of smooth closed hypersurfaces $E_1,\dots,E_r$ of $U_{\mathbb C}$ with normal crossings, such that
\[
(K_{\mathbb C}\circ\pi)^{-1}(0)=E_1\cup\cdots\cup E_r
\]
and, at every point of this set through which exactly the components $E_1,\dots,E_p$ pass, there are local coordinates $(u_1,\dots,u_d)$ in which $E_i=\{u_i=0\}$ and
\begin{equation}\label{eq:local_normal_form}
K_{\mathbb C}\circ\pi=\varepsilon\,\prod_{i=1}^pu_i^{a_i},\qquad \pi^*(dw_1\cdots dw_d)=b\,\prod_{i=1}^pu_i^{h_i}\,du_1\cdots du_d ,
\end{equation}
with $\varepsilon,b$ nonvanishing holomorphic functions and integers $a_i>0$, $h_i\ge0$ attached to the components. The pair $(a_E,h_E)$ depends only on the component $E$: $a_E$ is the order to which $K\circ\pi$ vanishes along $E$ and $h_E$ the order to which the Jacobian of $\pi$ does.

Since $K$ has real coefficients the resolution can be built from blow-ups along real centres, and then $U_{\mathbb C}$ carries an anti-holomorphic involution lifting complex conjugation whose fixed locus $U=U_{\mathbb R}$ is a real manifold of dimension $d$ with $\pi\colon U\to W^{(\mathbb R)}$ a proper real analytic map. The components with real points are the $E_i$ that matter, and at real points the coordinates in \eqref{eq:local_normal_form} can be taken real. Nonnegativity of $K$ forces every exponent $a_i$ to be even, $a_i=2k_i$, and $\varepsilon>0$ near the real points; absorbing $\varepsilon^{1/2k_1}$ into $u_1$ we may take $\varepsilon=1$. So the local picture on the real resolution is
\begin{equation}\label{eq:real_normal_form}
K\circ\pi=\prod_{i=1}^pu_i^{2k_i},\qquad \pi^*(\varphi\,dw)=c(u)\prod_{i=1}^p|u_i|^{h_i}\,du ,
\end{equation}
with $c=b\,(\varphi\circ\pi)$ smooth, and nonnegative where $\varphi$ is. This is the only place where analyticity is used: it is needed for the resolution of $K$, and for nothing else. The prior enters through $c$, which is smooth, and so does the observable, through $f\circ\pi$.

\input{figures/resolution_schematic}

\subsection{The two divisors}

The formula \eqref{eq:real_normal_form} records two different divisors on $U$. The first is the divisor of $K\circ\pi$, with multiplicities $2k_i$: it says how fast the Boltzmann weight $e^{-nK\circ\pi}$ decays away from the components. The second is the divisor of the pulled-back measure $\pi^*(\varphi\,dw)$, with multiplicities $h_i$: it says how much volume the change of variables has compressed onto each component. The asymptotics of $\int e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ near a component is a competition between the two, and the outcome of the competition in one normal variable is the elementary integral
\begin{equation}\label{eq:one_variable}
\int_0^1u^{h}\,e^{-nu^{2k}}\,du=\frac{1}{2k}\,\Gamma\!\Big(\frac{h+1}{2k}\Big)\,n^{-\frac{h+1}{2k}}+O(e^{-n/2}) ,
\end{equation}
obtained by the substitution $t=nu^{2k}$. The exponent $(h+1)/2k$ is the number attached to a component of the divisor; the smaller it is, the slower the decay, and the more the component contributes. When several components pass through a point, the local integral is a product of such one-variable integrals in the normal coordinates, times an integral over the remaining coordinates, and the exponents add as poles of the Mellin transform rather than as numbers: this is where the logarithms come from, and it is the subject of \cref{sec:stratification}.

The vanishing orders $h_i$ are the reason the prior cannot be dropped from the picture. Changing the prior does not change the components or the $k_i$, but a prior vanishing along part of $W_0$ changes the $h_i$ there and hence the exponents. In the same way an observable $f$ vanishing to order $l_i$ along $E_i$ shifts the second divisor for the integral $\Zcal_n[f]$ to $h_i+l_i$, which is the mechanism of \cref{sec:wallcrossing}.

\subsection{Irreducible components as primes}

The components $E_i$ are canonical once the resolution is fixed: working with the Zariski topology on $U_{\mathbb C}$, the zero locus of $K_{\mathbb C}\circ\pi$ has a unique decomposition into irreducible components, and by the normal crossing property each is smooth. The analogy to keep in mind is the factorisation of an integer into primes: the components are the primes of the singularity, the multiplicities $2k_i$ are the exponents in the factorisation, and $h_i$ is a second numerical invariant of each prime. Different components represent independent ways in which the model attains zero divergence, and the intersection pattern records how these ways combine. We work over $\mathbb C$ for this decomposition because real analytic sets do not in general admit one \citep{fernando2016irreducible}; the real strata used in the integrals are the real points of the complex ones.

\subsection{An example with a blow-up}\label{ex:blowup}

The running examples of \cref{sec:examples} are already in the form \eqref{eq:real_normal_form}. To see what a resolution does, take $K(x,y)=x^2(x-y)^2$ on a neighbourhood of the origin in $\R^2$: two lines through the origin, each a component of $W_0$, meeting at a point where $K$ vanishes to order four. Blowing up the origin replaces it by a projective line $E_0$; in the chart $x=u,\ y=uv$ of the blow-up,
\[
K\circ\pi=u^2(u-uv)^2=u^4(1-v)^2,\qquad dx\,dy=u\,du\,dv ,
\]
so $E_0=\{u=0\}$ carries $(k_0,h_0)=(2,1)$ and the strict transform of the line $\{x=y\}$, which is $\{v=1\}$, carries $(1,0)$; the other chart shows the strict transform of $\{x=0\}$ with data $(1,0)$. The three components meet in two points, $E_0\cap\{v=1\}$ and $E_0\cap\{x=0\}$, and $K\circ\pi$ is a monomial near each: the singular point of $W_0$ has become a curve $E_0$ with two marked points. The ratios are $(h_0+1)/2k_0=1/2$ on $E_0$ and $(0+1)/2=1/2$ on each strict transform, so all three components tie at $1/2$, and the two marked points, where two components with the same ratio meet, will carry the logarithm: $\Zcal_n[1]\sim C\,n^{-1/2}\log n$. An observable vanishing at the origin of $W$ vanishes along all of $E_0$ after pull-back, and so shifts the exponent on $E_0$ and at both marked points; an observable vanishing only on the line $\{x=0\}$ shifts only the one strict transform, and hence only one of the two marked points. Already in this example the resolution separates contributions that are superimposed at the single singular point of $W_0$.

%%%%%%%%%% FILE sections/04_stratification.tex %%%%%%%%%%
\section{The stratification of the exceptional divisor}\label{sec:stratification}

The exceptional divisor $E=E_1\cup\cdots\cup E_r$ is not a manifold: it is a union of manifolds that cross. The natural way to organise it is by how many components pass through a point. This section introduces the resulting stratification, which is the index set of everything that follows, and explains which strata carry the leading behaviour and why.

\subsection{Depth and strata}

For a point $u\in E$ let $I(u)=\{i: u\in E_i\}$ be the set of components through $u$; its size is the \emph{depth} of $u$. For a nonempty $I\subseteq\{1,\dots,r\}$ set
\[
E_I=\bigcap_{i\in I}E_i,\qquad S_I=E_I\setminus\bigcup_{j\notin I}E_j ,
\]
so that $S_I$ is the set of points through which exactly the components indexed by $I$ pass. By the normal crossing property $E_I$ is a smooth submanifold of codimension $|I|$ (or empty) and $S_I$ is open in it. The $S_I$ are the \emph{strata}; they are disjoint, they cover $E$, and the closure of $S_I$ is the union of the $S_J$ with $J\supseteq I$. Ordering by depth gives the filtration
\[
E=Z_{d-1}\supseteq Z_{d-2}\supseteq\cdots\supseteq Z_0,\qquad Z_c=\bigcup_{|I|\ge d-c}E_I ,
\]
whose successive differences are the unions of strata of a fixed depth. This is a stratification in the sense of \citet{trotmanstrat}, and a particularly well-behaved one: in the local coordinates \eqref{eq:real_normal_form} a stratum of depth $p$ is a coordinate subspace $\{u_1=\cdots=u_p=0\}$ and its normal directions are the coordinate directions $u_1,\dots,u_p$, each labelled by a component and carrying that component's data $(k_i,h_i)$.

In \cref{ex:planes} the strata are the two planes with the axis removed, of depth one, and the axis, of depth two. In \cref{ex:mixed} they are the two lines with the origin removed and the origin. In \cref{ex:blowup} they are the three components with the two marked points removed and the two marked points. The picture to hold on to is a cell decomposition of $E$ in which cells of higher depth lie in the closures of cells of lower depth, and the deepest cells, where the most components meet, are the smallest.

\input{figures/stratification}
\input{figures/planes}

\subsection{Exponents and multiplicities of a stratum}

Near a point of $S_I$ with normal coordinates $u=(u_i)_{i\in I}$ and tangential coordinates $v$ along the stratum, the integrand of $\Zcal_n[f]$ is
\[
(f\circ\pi)(v,u)\;\prod_{i\in I}|u_i|^{h_i}\;e^{-n\prod_{i\in I}u_i^{2k_i}}\;c(v,u)\,du\,dv .
\]
Freezing $v$, the $u$-integral is a $|I|$-dimensional version of \eqref{eq:one_variable}. Its behaviour is governed by the ratios attached to the normal directions,
\[
\lambda_i=\frac{h_i+1}{2k_i}\quad(i\in I),\qquad \lambda_I=\min_{i\in I}\lambda_i,\qquad m_I=\#\{i\in I:\lambda_i=\lambda_I\} ,
\]
and the basic fact, proved in \cref{sec:population}, is that the $u$-integral is asymptotic to a constant times $n^{-\lambda_I}(\log n)^{m_I-1}$. The exponent of a stratum is the smallest ratio among its normal directions; the multiplicity is the number of normal directions attaining it, and it is the multiplicity, less one, that becomes the power of the logarithm. A stratum where all normal directions share the same ratio is called \emph{exact} at that exponent; the deepest exact strata at the smallest exponent are where the leading term of $\Zcal_n[1]$ lives.

The mechanism behind the logarithm is worth seeing once in coordinates. With two normal directions of equal ratio $\lambda$, the Mellin transform of the $u$-integral in the variable $s$ is a product of two factors each with a simple pole at $s=\lambda$, and a double pole corresponds to a term $n^{-\lambda}\log n$. With different ratios the poles are at different places and the smaller one wins with no logarithm. In \cref{ex:planes} the axis has two normal directions with ratio $1/2$, so $\lambda=1/2$, $m=2$ and $\Zcal_n\sim Cn^{-1/2}\log n$; each plane has a single normal direction with ratio $1/2$ and contributes $n^{-1/2}$ without a logarithm, which is dominated. In \cref{ex:mixed} the origin has normal directions with ratios $1/2$ and $1/6$, so $\lambda=1/6$ and $m=1$, while the line $\{y=0\}$ has the single ratio $1/6$: the leading term $n^{-1/6}$ is carried by the line, and the origin is not exact at $1/6$.

The global exponents of $\Zcal_n[1]$ are
\[
\lambda=\min_I\lambda_I,\qquad m=\max\{m_I:\lambda_I=\lambda\} ,
\]
the real log canonical threshold and its multiplicity \citep{watanabeAlgebraicGeometryStatistical2009}; all the strata with $\lambda_I=\lambda$ and $m_I=m$ contribute to the leading coefficient, and the coefficient is a sum of integrals over them. The whole expansion \eqref{eq:intro_answer} arises in the same way from all strata and all their normal directions: every exponent that occurs is of the form $(h_i+\alpha+1)/2k_i$ for some component $E_i$ and some $\alpha\in\N$, the shift $\alpha$ being the order of a normal derivative of the amplitude, and a stratum contributes at an exponent $\mu$ precisely when each of its normal directions resonates with $\mu$ in this sense. The exponents therefore lie on the lattice $Q^{-1}\N$ with $Q=2\prod_ik_i$, and the logarithmic degree at $\mu$ is bounded by the largest depth of a stratum all of whose normal directions resonate with $\mu$.

\input{figures/mixed}

\subsection{Wall-crossing}\label{sec:wallcrossing}

Now insert an observable. If $f\circ\pi$ vanishes to order $l_i$ along $E_i$, meaning that $f\circ\pi=\prod_{i\in I}|u_i|^{l_i}\tilde f$ near $S_I$ with $\tilde f$ not identically zero on $S_I$, then the integrand of $\Zcal_n[f]$ near $S_I$ has the form of the integrand of $\Zcal_n[1]$ with $h_i$ replaced by $h_i+l_i$. The exponents of the stratum shift:
\[
\lambda_I(f)=\min_{i\in I}\frac{h_i+l_i+1}{2k_i}\ \ge\ \lambda_I ,
\]
with equality if and only if $l_i=0$ for some $i$ attaining the minimum, and the multiplicity $m_I(f)$ is recomputed with the shifted ratios. An observable that vanishes along a component is blind to the strata whose leading behaviour that component carries, and sees them instead at a higher exponent, through its normal derivatives. Conversely the leading exponent of $\Zcal_n[f]$ is attained on the strata where $f$ does not vanish along a minimising component, and if $f$ vanishes on all of $W_0$ the exponent of $\Zcal_n[f]$ is strictly larger than that of $\Zcal_n[1]$, so that $\E_\infty[f]\to0$ at a rate that measures the order of vanishing.

This is the sense in which different observables probe different parts of the singular locus. In \cref{ex:planes}, $f=1$ and any $f$ with $f(0,0,z)\not\equiv0$ have exponent $1/2$ with a logarithm, carried by the axis; $f=x^2$ vanishes to order two on the plane $\{x=0\}$ and hence on the axis, and the shifted ratios on the axis are $(0+2+1)/2=3/2$ for the $x$-direction and $1/2$ for the $y$-direction, so the axis now has exponent $1/2$ with multiplicity one, while the plane $\{y=0\}$, on which $f=x^2$ does not vanish, still has exponent $1/2$ with multiplicity one: $\Zcal_n[x^2]\sim Cn^{-1/2}$ with no logarithm, and $\E_\infty[x^2]\sim C'/\log n$. The posterior concentrates on the axis, and this is the rate at which it does so. In \cref{ex:blowup}, an observable vanishing at the singular point of $W$ shifts $E_0$ and both marked points, while an observable vanishing along one line shifts one marked point only, which the resolution keeps apart.

\begin{remark}[Parity]\label{rem:parity}
A component $E_i$ either resolves a wall of the parameter space, in which case the normal coordinate $u_i$ runs over a one-sided interval $[0,\varepsilon)$, or lies in the interior of $U$, in which case $u_i$ runs over $(-\varepsilon,\varepsilon)$. In the second case the normal integral is a sum over the two sides, and the amplitude is replaced by its even part in $u_i$: all odd normal derivatives in an interior direction drop out of the expansion, and only the shifts $\alpha$ of the parity of the wall survive. \cref{ex:planes} has interior components, so its corrections proceed in steps of $2$ in each normal direction; \cref{ex:mixed} has boundary components, and all shifts occur. The chart-level statements of Parts~II and~III are formulated on the positive box, where both cases are covered by summing over the orthants.
\end{remark}

A remark on what is intrinsic. The exponents and multiplicities depend on the resolution only through the vanishing orders along its components, and are the same for any two resolutions; the coefficients we construct in Part~II are pairings of $f$ with measures on the strata, and \cref{sec:population} explains in what sense those measures are independent of the choices made in constructing them. The stratification is scaffolding of the same kind as the coordinates: canonical once $\pi$ is fixed, and used to organise a computation whose outcome is a distribution on $W_0$.

%%%%%%%%%% FILE sections/05_normal_geometry.tex %%%%%%%%%%
\section{The normal geometry of a stratum}\label{sec:normal_geometry}

The coefficients of the expansion will be integrals over strata of normal derivatives of the amplitude. To say this without coordinates we need three pieces of differential geometry: a canonical splitting of the conormal bundle of a stratum, which makes normal Taylor coefficients into global sections; tubular neighbourhoods, which identify a neighbourhood of the stratum with a neighbourhood of the zero section of its normal bundle; and the pushforward of densities along the bundle projection, which integrates out the normal variables without a metric. None of this is special to our situation, but the normal crossing structure makes each piece unusually clean.

\subsection{The conormal splitting}

Let $M$ be a smooth manifold and $X\subseteq M$ a submanifold. The normal bundle $NX$ is defined by the exact sequence
\begin{equation}\label{eq:conormal_sequence}
0\longrightarrow TX\longrightarrow TM|_X\longrightarrow NX\longrightarrow0
\end{equation}
of bundles on $X$, and its dual $N^*X\subseteq T^*M|_X$ is the conormal bundle, the covectors along $X$ that kill $TX$. In general there is no preferred way to split \eqref{eq:conormal_sequence}. When $X=Y_1\cap\cdots\cap Y_p$ is a transverse intersection of smooth hypersurfaces there is, however, a canonical decomposition of the conormal bundle. If $u_i$ is a local defining equation of $Y_i$ then $T_xX=\bigcap_i\ker(du_i)_x$, so $N^*_xX$ is spanned by $(du_1)_x,\dots,(du_p)_x$. A different defining equation $u_i'$ of the same hypersurface is a unit multiple of $u_i$, so $du_i'$ and $du_i$ span the same line along $X$. The line bundle $\mathcal L_i\subseteq N^*X$ spanned by the differentials of defining equations of $Y_i$ is therefore well defined, and
\begin{equation}\label{eq:conormal_splitting}
N^*X\;\cong\;\bigoplus_{i=1}^p\mathcal L_i,\qquad \operatorname{Sym}^r(N^*X)\;\cong\;\bigoplus_{|b|=r}\ \bigotimes_{i=1}^p\operatorname{Sym}^{b_i}(\mathcal L_i) .
\end{equation}
The right side of the second isomorphism is the bundle of polynomials in the $du_i$ of degree $b_i$ in the $i$-th variable, with coefficients smooth functions on $X$. In our application $M=U$ is the resolution, $X=S_I$ is a stratum, and the hypersurfaces are the components $E_i$, $i\in I$; the splitting says that a stratum knows which of its normal directions belongs to which component, and this is what allows the data $(k_i,h_i)$ of the components to be attached to normal directions of the stratum.

\subsection{Normal derivatives as global sections}

For a smooth function $F$ on $M$ the naive normal derivatives $\partial^b_uF|_X$ in local coordinates are not intrinsic: they depend on how the coordinates along $X$ are completed to coordinates on $M$, and a nonlinear change of defining equations mixes orders. The situation is different on the normal bundle itself, where the transition functions between local frames are linear on fibres.

\begin{lem}\label{lem:normal_deriv}
Let $X=Y_1\cap\cdots\cap Y_p$ be a transverse intersection of hypersurfaces in $M$ and let $\tilde F$ be a smooth function on a neighbourhood of the zero section in $NX$. Let $u_1,\dots,u_p$ be linear fibre coordinates on $NX$ dual to a local frame adapted to the splitting \eqref{eq:conormal_splitting}. For $b\in\N^p$ the section
\[
D_b(\tilde F)=\frac1{b!}\,\frac{\partial^{|b|}\tilde F}{\partial u^{b}}\Big|_{u=0}\;(du_1|_X)^{\otimes b_1}\otimes\cdots\otimes(du_p|_X)^{\otimes b_p}
\]
is independent of the choice of adapted linear fibre coordinates, and hence a global section of $\bigotimes_i\operatorname{Sym}^{b_i}(\mathcal L_i)$ over $X$.
\end{lem}

\begin{proof}
It suffices to treat one factor. An adapted change of frame is $u_i'=g_iu_i$ with $g_i$ a nonvanishing smooth function of the base point alone. Then $\partial_{u_i'}=g_i^{-1}\partial_{u_i}$ along the fibre and $du_i'|_X=g_i\,du_i|_X$, so the factors $g_i^{-b_i}$ and $g_i^{b_i}$ cancel; mixed derivatives are unaffected because $g_i$ does not depend on the fibre coordinates.
\end{proof}

To apply this to a function $F$ on $M$ one pulls it back to the normal bundle along a tubular neighbourhood $\Phi\colon NX\to M$, a diffeomorphism from a neighbourhood of the zero section onto a neighbourhood of $X$ that restricts to the identity on $X$, and sets
\begin{equation}\label{eq:normal_differential}
D^r_\perp(F)=\sum_{|b|=r}D_b(F\circ\Phi)\in\Gamma\big(X,\operatorname{Sym}^r(N^*X)\big) ,
\end{equation}
the \emph{normal $r$-th differential} of $F$ with respect to $\Phi$. Its dependence on $\Phi$ is exactly the dependence of a Taylor coefficient on the choice of coordinates transverse to $X$: the leading nonvanishing one is intrinsic, and the lower ones are intrinsic modulo the higher ones. This is made precise in \cref{sec:jets}, where the coefficients of the expansion are shown to depend on $F$ only through its class in a quotient of the ideal of functions vanishing on the stratum; the tubular neighbourhood is a device for computing that class.

\input{figures/tubular_nbhd}

\subsection{Tubular neighbourhoods and integration along fibres}

A tubular neighbourhood of $X$ separates tangential from normal variables without choosing a metric, and this separation is what reduces the per-stratum integral to an outer integral over the stratum and inner integrals over the normal fibres. We work with densities rather than forms to avoid orientations \citep[\S16]{lee2012smooth}.

Let $|\mu|$ be a smooth positive density on a neighbourhood $V$ of $X$ in $M$ and $\Phi\colon NX\to M$ a tubular neighbourhood with $\Phi^{-1}(V)$ a bounded disc bundle over $X$. Then for integrable $F$,
\[
\int_VF\,|\mu|=\int_{\Phi^{-1}(V)}(F\circ\Phi)\,\Phi^*|\mu| .
\]
The bundle projection $\tau\colon NX\to X$ is a surjective submersion, and for a density $|\omega|$ on $NX$ with fibrewise compact support there is a unique density $\tau_*|\omega|$ on $X$ with
\begin{equation}\label{eq:pushforward}
\int_Xg\,\tau_*|\omega|=\int_{NX}(g\circ\tau)\,|\omega|\qquad\text{for all }g\in C^\infty_c(X) .
\end{equation}
In local coordinates $x$ on $X$ and linear fibre coordinates $u$, a density on $NX$ has the form $g(x,u)|du|\,|dx|$ and its pushforward is $\big(\int_{D_x}g(x,u)\,du\big)|dx|$, with $D_x$ the fibre over $x$: the pushforward integrates out the normal variables.

Near a stratum $S_I$ of the resolution the integrand of $\Zcal_n[f]$ is, in the notation of \eqref{eq:real_normal_form},
\[
(f\circ\pi)\;e^{-n(K\circ\pi)}\;\pi^*(\varphi\,dw)=(f\circ\pi)(v,u)\;|u|^{h_I}\;e^{-nu^{2k_I}}\;c(v,u)\,|du\,dv| ,
\]
where $u^{2k_I}=\prod_{i\in I}u_i^{2k_i}$, $|u|^{h_I}=\prod_{i\in I}|u_i|^{h_i}$, and $c(v,u)$ is the smooth factor of \eqref{eq:real_normal_form}, the prior times the smooth part of the Jacobian. Pulling back along a tubular neighbourhood of $S_I$ and pushing forward along $\tau$, the contribution of a neighbourhood of the stratum becomes an integral over $S_I$ of fibre integrals
\begin{equation}\label{eq:fibre_integral}
\int_{D_v}(f\circ\pi)(v,u)\,|u|^{h_I}\,e^{-nu^{2k_I}}\,c(v,u)\,du ,
\end{equation}
in which $v$ is a parameter. The normal Taylor expansion of the amplitude,
\[
(f\circ\pi)(v,u)=\sum_{|\gamma|\le N}D^\gamma_\perp(f\circ\pi)(v)\,u^\gamma+R_N(v,u),\qquad c(v,u)=\sum_\delta\frac{c_\delta(v)}{\delta!}u^\delta ,
\]
with $D^\gamma_\perp$ the components of \eqref{eq:normal_differential} in the adapted frame, turns \eqref{eq:fibre_integral} into a sum of \emph{bare normal moments}
\begin{equation}\label{eq:bare_moment}
M_\alpha(n)=\int_{D}u^\alpha\,|u|^{h_I}\,e^{-nu^{2k_I}}\,du ,
\end{equation}
which are the objects whose asymptotics carry the exponents and logarithms, and a remainder whose treatment is the substance of \cref{sec:population} and \cref{app:chart_proofs}. Two features of this reduction deserve emphasis. The tangential variable $v$ is inert: it appears only as a parameter in the amplitude and the density factor, and the outer integral over $S_I$ is performed last. And the domain $D_v$ of the fibre is one-sided or two-sided in each normal direction according to whether the component resolves a wall of $W$ or lies in its interior, which is the source of the parity phenomenon of \cref{rem:parity}: over a symmetric interval the odd moments $M_\alpha$ vanish.

\begin{remark}[Cutoffs]\label{rem:cutoff}
Restricting the fibre to a bounded domain $D_v$ is harmless in one sense and not in another. Localising in the \emph{phase}, to the sublevel set $\{K\circ\pi<\varepsilon\}$, costs $O(e^{-n\varepsilon})$, which is invisible in the scale. Changing the \emph{normal} cutoff, say from $[0,b]^{|I|}$ to $[0,b']^{|I|}$, is not exponentially small, because $u^{2k_I}$ vanishes on the coordinate hyperplanes and the Boltzmann weight does not decay there. Such a change alters the coefficients of the expansion but not its exponents or logarithmic degrees. The coordinate-free formulation of \cref{sec:population} absorbs the cutoff into the partition of unity and makes the total coefficient, summed over strata, independent of these choices.
\end{remark}

%%%%%%%%%% FILE sections/06_moment_tensors.tex %%%%%%%%%%
\section{Moment tensors and the conormal presentation}\label{sec:moment_tensors}

The bare moments $M_\alpha(n)$ of \eqref{eq:bare_moment} depend on the linear fibre coordinates through the monomial $u^\alpha$: rescaling a defining equation of a component rescales the moment. The intrinsic object is a tensor, and pairing it with the normal differential of the amplitude, which rescales inversely, produces a scalar. This section defines the moment tensors, states the coordinate-free form of the per-stratum expansion, and records what in the resulting presentation is canonical.

\subsection{Moment tensors}

Fix a stratum $S=S_I$, a tubular neighbourhood $\Phi\colon NS\supseteq\mathcal N\to U$ with projection $\tau$, and a smooth cutoff $\chi$ with compact support in the tubular neighbourhood, constant along the fibres. Write the pulled-back phase and the smooth density factor as
\[
K_S=(K\circ\pi)\circ\Phi\in C^\infty(\mathcal N),\qquad |\mu_S|=\Phi^*\big(\chi\,(\varphi\circ\pi)\,b\,|dw|\big) ,
\]
where $|\det D\pi|=b\,\prod_{i\in I}|u_i|^{h_i}$ with $b>0$ smooth, so that the singular monomial weight $|u|^{h_I}$ is kept separate from the smooth positive density $|\mu_S|$. Disintegrating $|\mu_S|$ along $\tau$ writes it as a marginal density $\tau_*|\mu_S|$ on $S$ times conditional fibre densities $|\mu_S|_v$.

\begin{defn}[Moment tensor]\label{def:moment_tensor}
For $r\ge0$ the $r$-th \emph{moment tensor} $\mathsf M_{S,r}(n)\in\Gamma(S,\operatorname{Sym}^r(NS))$ is defined by requiring, for every $v\in S$ and every $\alpha\in\operatorname{Sym}^r(N_v^*S)$,
\begin{equation}\label{eq:moment_tensor}
\big\langle\alpha,\mathsf M_{S,r}(n)(v)\big\rangle=\int_{D_v}\alpha(\xi^{\otimes r})\,|u|^{h_I}\,e^{-nK_S(\xi)}\,|\mu_S|_v(\xi) ,
\end{equation}
where $D_v=\mathcal N\cap\tau^{-1}(v)$ and $\alpha(\xi^{\otimes r})$ evaluates the symmetric $r$-linear form on $r$ copies of the fibre vector $\xi$.
\end{defn}

In an adapted frame with fibre coordinates $\xi=\sum_iu_ie_i$ and with the tubular chart chosen so that $K_S=u^{2k_I}$, the pairing of $\mathsf M_{S,r}$ with $du^\gamma$, $|\gamma|=r$, is the \emph{dressed} moment
\begin{equation}\label{eq:dressed_moment}
\widetilde M_\gamma(v,n)=\int_{D_v}u^\gamma\,|u|^{h_I}\,e^{-nu^{2k_I}}\,g(v,u)\,du=\sum_\delta\frac{g_\delta(v)}{\delta!}\,M_{\gamma+\delta}(n) ,
\end{equation}
with $g$ the local density of $|\mu_S|_v$ and $g_\delta$ its normal Taylor coefficients: a convergent fibre integral, equal to any order to a finite combination of bare moments. The normal differential $D^r_\perp(f\circ\pi)$ is constant along fibres, so it can be pulled out of the fibre integral, and the contraction $\langle D^r_\perp(f\circ\pi),\mathsf M_{S,r}(n)\rangle$ is a function on $S$.

\begin{prop}[Coordinate-free per-stratum expansion]\label{prop:coordfree_expansion}
With the above data,
\begin{equation}\label{eq:coordfree_expansion}
\int_U\chi\,(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw)\;\sim\;\sum_{r\ge0}\frac1{r!}\int_S\big\langle D^r_\perp(f\circ\pi),\mathsf M_{S,r}(n)\big\rangle\,\tau_*|\mu_S| ,
\end{equation}
and in an adapted frame the integrand is $\sum_{|\gamma|=r}D^\gamma_\perp(f\circ\pi)(v)\,\widetilde M_\gamma(v,n)\,|dv|$.
\end{prop}

The proposition is the normal Taylor expansion of \cref{sec:normal_geometry} with the remainder estimated; the estimate is the same one that proves the expansion theorem of \cref{sec:population}, and is given in \cref{app:chart_proofs}. Both sides are independent of the frame: the left side manifestly, the right because the pairing of a section of $\operatorname{Sym}^r(N^*S)$ with a section of $\operatorname{Sym}^r(NS)$ is a scalar.

\subsection{What the moment tensors know}

The $n$-dependence of $\mathsf M_{S,r}(n)$ is governed by the bare moments. The normal directions of $S$ are labelled by the components $E_i$, $i\in I$, with data $(k_i,h_i)$, and \cref{sec:population} shows that
\[
M_\gamma(n)\sim\frac{\Gamma(\lambda)}{(m-1)!}\,a_\gamma\;n^{-\lambda}(\log n)^{m-1},\qquad \lambda=\min_{i\in I}\frac{h_i+\gamma_i+1}{2k_i},\quad m=\#\{i:\tfrac{h_i+\gamma_i+1}{2k_i}=\lambda\} ,
\]
with an explicit $a_\gamma>0$. The exponent of the $\gamma$-component of the moment tensor is therefore the minimum over the normal directions of the shifted ratios, and its logarithmic degree is the number of directions attaining the minimum. Increasing $\gamma_i$ in a direction attaining the minimum raises the exponent; increasing it in another direction leaves the exponent alone until that direction catches up. In the dressed moment \eqref{eq:dressed_moment} the density corrections $\delta\ne0$ are subleading in the minimising directions and can tie in the others, which is how the prior enters the corrections and not only the leading term.

Reading \eqref{eq:coordfree_expansion} with this information gives the shape of the whole expansion. The exponents of $\Zcal_n[f]$ near $S$ are the numbers $(h_i+\alpha+1)/2k_i$ with $\alpha\in\N$ ranging over the normal orders that occur, the leading one at $S$ is $\lambda_I(f)$ of \cref{sec:wallcrossing}, and the coefficient of $n^{-\mu}(\log n)^q$ collects the contractions $\langle D^r_\perp(f\circ\pi),\mathsf M_{S,r}\rangle$ whose exponent is $\mu$ and logarithmic degree at least $q$. Which strata contribute at a given $(\mu,q)$, and how the contributions of nested strata are to be shared, is the content of the stratum measures of the next section.

\subsection{The conormal presentation and what is intrinsic in it}\label{sec:conormal}

Collecting the terms of \eqref{eq:coordfree_expansion} at a fixed $(\mu,q)$ gives a functional of the form
\begin{equation}\label{eq:conormal_presentation}
F\;\longmapsto\;\sum_{\beta\le\alpha}\int_S\partial^\beta_NF\;\rho_\beta ,
\end{equation}
with $\alpha$ a multi-index of normal orders, $\partial_N^\beta$ normal derivatives in an adapted frame, and $\rho_\beta$ smooth densities on $S$. In the language of distributions this is a \emph{conormal distribution} along $S$ of order $|\alpha|$: a distribution supported on $S$ whose singular structure is transverse to $S$. The form \eqref{eq:conormal_presentation} is what any coefficient of the expansion looks like in coordinates, and it is worth being exact about what in it is canonical.

The total functional is canonical, being a coefficient of an expansion that does not know about coordinates. So is the class of amplitudes it sees, which is made precise in \cref{sec:jets}. The principal part, the term $\beta=\alpha$, is canonical as well: $\rho_\alpha$ is a density on $S$ with values in $\operatorname{Sym}^\alpha$ of the conormal bundle, the leading Laurent coefficient of a pole of higher order. The lower terms $\rho_\beta$, $\beta<\alpha$, are not canonical. Replacing a defining equation $u_j$ by a unit multiple of itself mixes the order-$\beta$ terms into the orders below, exactly as the residue of a pole of higher order is not a canonical Laurent coefficient. Coordinates are therefore needed to \emph{write} a coefficient of positive normal order, and the writing is not unique; what is unique is the functional, its principal symbol, and the finite jet of the amplitude on which it depends.

Two special cases make the whole functional canonical. When $\alpha=0$ the distribution is a measure on $S$: this is the stratum measure of \cref{sec:population}, the object through which the leading term and the top logarithmic coefficients are described. And when $S$ is a single point the conormal bundle has no base to vary along and every term of \eqref{eq:conormal_presentation} is a number times a normal derivative at the point; this is the situation in one variable and at the deepest strata of the running examples, where the coefficients are numbers built from derivatives of the amplitude at the crossing.

%%%%%%%%%% FILE sections/07_population.tex %%%%%%%%%%
\section{The stratum measures and the population expansion}\label{sec:population}

This section assembles the machinery into the expansion of $\Zcal_n[f]$ and describes its coefficients. The description proceeds from the coarse to the fine. First the exponents and logarithms, from the poles of a zeta function. Then the leading term at every exponent and depth, which is a measure on a stratum, canonical, and identified with a logarithmic residue of the resolved integrand. Then the corrections, organised as the Laurent data of one meromorphic function, with closed forms in the two situations that matter most. Throughout, $f$ and $\varphi$ are smooth; analyticity has been used once, for the resolution, and will not be used again.

\subsection{The per-stratum decomposition}

Pulling $\Zcal_n[f]$ back to the resolution is a change of variables, legitimate because $\pi$ is a diffeomorphism off a set of measure zero:
\[
\Zcal_n[f]=\int_U(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\]
Off the sublevel set $U_\varepsilon=\{K\circ\pi<\varepsilon\}$ the integrand is $O(e^{-n\varepsilon})$, invisible in the scale, so only a neighbourhood of $E$ matters. A partition of unity adapted to the stratification, $\sum_I\rho_I=1$ on $U_\varepsilon$ with $\rho_I$ supported in a fibre-saturated tubular neighbourhood of $S_I$ meeting no component $E_j$ with $j\notin I$, and constant along the normal fibres, gives
\begin{equation}\label{eq:strata_decomposition}
\Zcal_n[f]=\sum_I\Zcal_n[f;I]+O(e^{-n\varepsilon}),\qquad \Zcal_n[f;I]=\int\rho_I\,(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\end{equation}
Such partitions exist for the same reason tubular neighbourhoods do, and the cutoffs $\rho_I$ can be chosen to depend only on the tangential variable, so that they factor out of every fibre integral. Each $\Zcal_n[f;I]$ is then of the form treated in \cref{prop:coordfree_expansion}. The individual terms $\Zcal_n[f;I]$ depend on the partition of unity; the sum does not, and neither do the exponents and logarithmic degrees, which are read off the resolution data alone.

\subsection{The zeta function of a stratum and the shape of the expansion}

The asymptotics of a bare moment \eqref{eq:bare_moment} on the box $[0,b]^{|I|}$ are governed by the poles of
\[
\zeta_\gamma(z)=\int_{[0,b]^{|I|}}(u^{2k_I})^{z}\,u^{\gamma}\,|u|^{h_I}\,du=\prod_{i\in I}\frac{b^{2k_iz+h_i+\gamma_i+1}}{2k_iz+h_i+\gamma_i+1} ,
\]
a product of one-variable integrals because the integrand is a monomial. The $i$-th factor has a simple pole at $z=-(h_i+\gamma_i+1)/2k_i$, so $\zeta_\gamma$ has a pole at $z=-\lambda$ of order $m$ exactly when $m$ of the shifted ratios equal $\lambda$, and the Laplace transform relation $M_\gamma(n)=\int_0^\infty e^{-nt}\,d\nu_\gamma(t)$, with $\nu_\gamma$ the pushforward of $u^\gamma|u|^{h_I}du$ under $u\mapsto u^{2k_I}$, converts a pole of order $m$ at $-\lambda$ into a term $n^{-\lambda}(\log n)^{m-1}$ \citep[Ch.~4]{watanabeAlgebraicGeometryStatistical2009}. The leading Laurent coefficient is explicit: the factors with $i$ in the minimising set $J$ contribute $1/2k_i$ each and the others are evaluated at the pole,
\begin{equation}\label{eq:zeta_leading}
M_\gamma(n)\sim\frac{\Gamma(\lambda)}{(m-1)!}\ \prod_{i\in J}\frac1{2k_i}\ \prod_{i\in I\setminus J}\frac{b^{\,h_i+\gamma_i+1-2k_i\lambda}}{h_i+\gamma_i+1-2k_i\lambda}\ \ n^{-\lambda}(\log n)^{m-1} .
\end{equation}
The denominators in the second product are positive because $\lambda$ is the minimum; the factors of $1/2k_i$ are residues against $d\log u_i^{2k_i}$; and the factor $\Gamma(\lambda)/(m-1)!$ comes from the Laplace transform of $t^{\lambda-1}(\log t)^{m-1}$. All three ingredients reappear in the stratum measures below.

Combining \eqref{eq:zeta_leading} with the coordinate-free expansion \eqref{eq:coordfree_expansion} and summing over strata gives the shape of the expansion, which we state now and refine through the rest of the section.

\begin{thm}[The population expansion]\label{thm:population_expansion}
For smooth $f$ and $\varphi$ there is an asymptotic expansion
\[
\Zcal_n[f]\sim\sum_{\mu\in Q^{-1}\N}\ \sum_{q=0}^{d-1}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q,\qquad Q=2\prod_ik_i ,
\]
in the sense of \cref{sec:scale}, with the following properties. Each $c_{\mu,q}$ is a linear functional of $f$ of the conormal form \eqref{eq:conormal_presentation}, supported on the strata all of whose normal directions resonate with $\mu$, that is, satisfy $2k_i\mu-h_i-1\in\N$, and $c_{\mu,q}=0$ unless some such stratum has depth at least $q+1$. The exponents that occur are of the form $(h_i+\alpha+1)/2k_i$, $\alpha\in\N$. For $f\circ\pi$ not vanishing identically on a stratum $S_I$, that stratum first contributes at $\lambda_I$ with logarithmic degree $m_I-1$; if $f\circ\pi$ vanishes along $E_i$ to order $l_i$, its first contribution is at $\lambda_I(f)$ of \cref{sec:wallcrossing}. In particular
\[
\Zcal_n[1]\sim c\,n^{-\lambda}(\log n)^{m-1},\qquad c>0 ,
\]
with $(\lambda,m)$ the real log canonical threshold and its multiplicity of \cref{sec:stratification}.
\end{thm}

The theorem is proved for smooth data by an argument that never expands anything in a Taylor series in the tangential directions: in each chart the integral is reduced, by Fubini along the resonant normal directions, to one-dimensional integrals whose expansion is proved by scaling with an explicit remainder, and the remainder is estimated uniformly in the tangential variable. The argument is given in \cref{app:chart_proofs}, and it is the same argument that gives the empirical expansion of \cref{sec:empirical} once the field is put into the exponent. The rest of this section is about the coefficients.

\subsection{Depth, exact strata and admissible observables}\label{sec:exact_strata}

Fix an exponent $\mu$. At a point $P\in E$ of depth $c$, with normal directions labelled by the components through $P$, say that a wall $E_i$ \emph{resonates} with $\mu$ if $\alpha_i:=2k_i\mu-h_i-1\in\N$, and write $r_\mu(P)$ for the number of resonating walls through $P$. The \emph{exact stratum} at $(\mu,c)$ is
\[
S^\mu_c=\{P\in E:\ \operatorname{depth}(P)=c,\ r_\mu(P)=c\} ,
\]
the depth-$c$ points all of whose walls resonate; it is a union of strata $S_I$ with $|I|=c$, a locally closed submanifold of codimension $c$. Its closure lies in the closed set $D_c=\{\operatorname{depth}\ge c\}$ and its boundary in $D_{c+1}$, and on the open set $X_c=U\setminus D_{c+1}$ it is relatively closed. The coefficient $c_{\mu,q}$ is supported on the closed set $\{r_\mu\ge q+1\}$, a superlevel set of the resonance count rather than a stratum: a boundary point of the locus where $q+1$ walls resonate lies where more walls meet and belongs to the set automatically.

Call an observable \emph{admissible at depth $c$} if $f\circ\pi$ vanishes on a neighbourhood of $D_{c+1}$, and write $\Ical_{c+1}$ for the space of such pulled-back observables. The filtration $\Ical_1\subseteq\Ical_2\subseteq\cdots$ grades observables by how deep into the divisor they can see: an observable in $\Ical_{c+1}$ sees the strata of depth at most $c$ and is blind to the deeper crossings. Every statement about the depth-$c$ term below is made for admissible observables and on $X_c$. The reason is that at the boundary of an exact stratum a further wall arrives, the residue density of the stratum acquires a further pole, and it blows up whenever $\mu$ exceeds the exponent of the arriving wall; an admissible observable vanishes in a collar around that boundary, so the blow-up is met only where the observable is already zero. In \cref{ex:planes}, admissibility at depth one means vanishing near the axis, and admissibility at depth two is automatic since there are no points of depth three.

\input{figures/depth}

\subsection{The graded stratum formula}\label{sec:graded}

\begin{thm}[Graded stratum formula]\label{thm:graded}
Let $c\ge1$ and $f\circ\pi\in\Ical_{c+1}$. Then $c_{\mu,q}(f)=0$ for $q\ge c$, and $c_{\mu,c-1}(f)$ is a finite sum of absolutely convergent integrals over $S^\mu_c$. In a normal crossing chart with face coordinates $u_J=0$, $|J|=c$, the contribution of the face differentiates the whole localised amplitude $\eta=\rho\,c\,(f\circ\pi)$, the cutoff times the smooth density factor times the observable, in the $c$ normal directions to the resonant orders $\alpha_j=2k_j\mu-h_j-1$, integrates against the tangential weight, and multiplies by a constant:
\begin{equation}\label{eq:graded}
\frac{\Gamma(\mu)}{(c-1)!\prod_{j\in J}2k_j\,\alpha_j!}\int_{u_J=0}\partial^\alpha_J\eta\,(0_J,w)\;\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,dw .
\end{equation}
Only faces all of whose walls resonate contribute, and a face point with exactly the $J$-coordinates zero is a point of depth $|J|$, so these are integrals over $S^\mu_c$.
\end{thm}

The theorem says that the top logarithmic power at an exponent sees only the deepest exact stratum: a face of smaller depth produces a pole of lower order and cannot reach $(\log n)^{c-1}$. The summed coefficient is the invariant object and descends to a functional on $\Ical_{c+1}/\Ical_c$; the individual chart contributions are not asserted to be canonical, in accordance with \cref{sec:conormal}. The tangential weight $\prod w_i^{h_i-2k_i\mu}$ is integrable up to the boundary of the face exactly when $\mu$ is below the exponent of every non-resonant wall; admissibility removes the need for this, since the amplitude vanishes near the deeper faces. Where the condition does hold, the formula is valid for all smooth $f$, which is the situation of \cref{sec:tiers}.

\subsection{Jet dependence, without coordinates}\label{sec:jets}

For a locally closed submanifold $S\subseteq U$ let $\Ical_S^{\,n}$ be the $n$-th power of the ideal of smooth functions vanishing on $S$; the class of $F$ modulo $\Ical_S^{\,n+1}$ is its \emph{transverse $n$-jet} along $S$, a coordinate-free object whose identification with the normal Taylor coefficients through order $n$ is Hadamard's lemma. Define, for $P\in E$, the \emph{intrinsic jet order}
\[
n_\mu(P)=\sum_{\text{walls }E_i\text{ through }P}\big(\lfloor2k_i\mu\rfloor_\N-h_i-1\big) ,
\]
with $\lfloor x\rfloor_\N=\max(\lfloor x\rfloor,0)$; at a point of $S^\mu_c$ every wall resonates and $n_\mu(P)=|\alpha|$.

\begin{thm}[Jet dependence]\label{thm:jet}
Let $c\ge1$ and $F,F'\in\Ical_{c+1}$. If the germ of $F-F'$ at every $P\in S^\mu_c$ lies in $\Ical_{S^\mu_c,P}^{\,n_\mu(P)+1}$, then $c_{\mu,c-1}$ takes the same value on $F$ and $F'$. The functional therefore descends to the quotient of the admissible observables by those lying in $\Ical_{S^\mu_c}^{\,n_\mu(\cdot)+1}$ near every point of the stratum.
\end{thm}

The proof runs through \cref{thm:graded}: at an exactly resonant face the amplitude is a smooth multiple of $F$, a difference in $\Ical_S^{\,|\alpha|+1}$ is locally a sum of smooth multiples of products of $|\alpha|+1$ functions vanishing at the face, and a coordinate derivative of total order $|\alpha|$ of such a product vanishes there because the Leibniz rule leaves some factor undifferentiated. The order $n_\mu(P)$ is an upper bound: cancellations, or vanishing of the prior, can lower the true order at particular points. In the language of \cref{sec:conormal}, the coefficient depends on the observable only through its transverse $|\alpha|$-jet along the exact stratum. This is the precise form of the statement that the observable is seen through finitely many normal derivatives on a stratum, and it needs no choice of tubular neighbourhood.

\subsection{The stratum measure}\label{sec:stratum_measure}

Now impose the \emph{zero-order condition} on $S^\mu_c$: every wall through the exact stratum satisfies $2k_j\mu=h_j+1$, so that all $\alpha_j=0$ and the twisted density $(K\circ\pi)^{-\mu}\pi^*(\varphi\,dw)$ has simple poles along the $c$ walls. Then \cref{thm:graded} contains no derivatives, the functional $c_{\mu,c-1}$ is nonnegative on nonnegative admissible observables and depends only on their values on $S^\mu_c$, and a positive local linear functional is a measure.

\begin{thm}[The stratum measure]\label{thm:stratum_measure}
Let $c\ge1$ and assume the zero-order condition on $S^\mu_c$. There is a positive Radon measure $\nu^\mu_c$ on $X_c=U\setminus D_{c+1}$, carried by the exact stratum, such that for every $f$ with $f\circ\pi\in\Ical_{c+1}$ the restriction of $f\circ\pi$ to $X_c$ is $\nu^\mu_c$-integrable and
\begin{equation}\label{eq:stratum_measure}
c_{\mu,c-1}(f)=\int_{X_c}f\circ\pi\,d\nu^\mu_c .
\end{equation}
It is the unique positive Radon measure on $X_c$ with these integrals on smooth compactly supported tests, and for the fixed resolution and prior it does not depend on the tubular neighbourhoods, cutoffs or partitions of unity used to compute it.
\end{thm}

The construction is the Riesz--Markov--Kakutani theorem applied to $T[G]=c_{\mu,c-1}[G]$ on smooth compactly supported tests $G$ in $X_c$: $T$ is linear, positive and local to the stratum, and it satisfies the fixed-support bound $|T[G]|\le\|G\|_\infty T[\chi_L]$ for a cutoff $\chi_L$ equal to one on a compact $L$ containing the support of $G$, which gives continuity and hence extension to $C_c(X_c)$. Nothing is asserted about $\nu^\mu_c$ across $D_{c+1}$: it need not have finite mass, and it is not extended to $U$.

\subsection{The weighted logarithmic residue}\label{sec:residue}

The stratum measure has a name from complex geometry. In a normal crossing chart the twisted density near a face $u_J=0$ of the exact stratum is
\[
\prod_{j\in J}|u_j|^{h_j-2k_j\mu}\,\eta(u)\,|du|=\prod_{j\in J}\frac{|du_j|}{|u_j|}\cdot\eta\,|du_{J^c}| ,
\]
with every pole simple under the zero-order condition. Extracting the pole along $E_j$ against $d\log(u_j^{2k_j})=2k_j\,du_j/u_j$ contributes a factor $(2k_j)^{-1}$, and doing so for all $j\in J$ leaves on the face the density
\begin{equation}\label{eq:face_density}
\prod_{j\in J}(2k_j)^{-1}\,\eta(0,w)\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,|dw| ,
\end{equation}
which is exactly the tangential weight of \eqref{eq:graded} at zero order. Define
\begin{equation}\label{eq:residue_measure}
\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c .
\end{equation}

\begin{thm}[The residue formula]\label{thm:residue}
Under the zero-order condition, for every admissible $f$ the integral $\int f\circ\pi\,d\Rres^\mu_c$ is the sum over charts and over simple faces $J$ of the face integrals of $f\circ\pi$ against \eqref{eq:face_density}, with chart and face multiplicities retained, and
\[
c_{\mu,c-1}(f)=\frac{\Gamma(\mu)}{(c-1)!}\int_{S^\mu_c}f\circ\pi\,d\Rres^\mu_c .
\]
\end{thm}

Two coordinate-free descriptions of $\Rres^\mu_c$ follow, and their agreement is what licenses the name.

\paragraph{Through the asymptotics.} Nothing in \eqref{eq:residue_measure} uses a chart: the defining property is
\begin{equation}\label{eq:defA}
\int F\,d\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\lim_{n\to\infty}n^{\mu}(\log n)^{-(c-1)}\int_UF\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw)
\end{equation}
for $F$ vanishing near $D_{c+1}$, and $\Rres^\mu_c$ is the unique regular measure on $X_c$ with these integrals on tests. Equivalently, replacing the Laplace weight by sublevel sets of the phase,
\[
\int F\,d\Rres^\mu_c=\lim_{\delta\to0}\frac{c!}{(\log1/\delta)^c}\int_{\{K\circ\pi>\delta\}}F\,(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw) ,
\]
a truncated negative moment of the phase against the prior; in the logarithmic coordinates $t_j=2k_j\log(1/|u_j|)$ the region is the simplex $\sum t_j<\log(1/\delta)$, whose volume $(\log1/\delta)^c/c!$ is where the constant and the multiplicities $2k_j$ come from.

\paragraph{As an iterated density residue.} A positive density $\omega$ with a simple pole along a hypersurface $\{g=0\}$, meaning that $|g|\omega$ extends smoothly across it, has a residue $\operatorname{res}\omega=(|g|\omega)|_{\{g=0\}}/|dg|$, a positive density on the hypersurface independent of the choice of $g$, and characterised by the logarithmic divergence of the collar integral: $\int G\,\operatorname{res}\omega=\lim_{\varepsilon\to0}\frac1{2\log(1/\varepsilon)}\int_{\varepsilon<|g|<r}\tilde G\,\omega$. Along $c$ walls meeting transversally the residue is iterated, and for densities every step is unsigned and the result is symmetric in the walls. Summing over the normal sides of each wall and dividing by the multiplicity $2k_j$ of the divisor of $K\circ\pi$,
\begin{equation}\label{eq:defB}
\Rres^\mu_c=\frac{2^{c}}{\prod_{j\in J}2k_j}\,\operatorname{res}_{S^\mu_c}\big[(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw)\big]
\end{equation}
on each component of the stratum with walls $J$, where $2^c$ counts the sides for interior walls. Both the divisor and its multiplicities are intrinsic to $K\circ\pi$, so this is a coordinate-free density on the exact stratum.

\begin{thm}[Identity of the two descriptions]\label{thm:identity}
Under the zero-order condition, the iterated density residue \eqref{eq:defB}, computed in any resolved chart atlas as the sum of the face densities \eqref{eq:face_density} pushed into $U$ and restricted to $X_c$, is a regular measure on $X_c$ that integrates tests to the residue sums of \cref{thm:residue}. Hence it equals $\Rres^\mu_c$, and $\nu^\mu_c=\frac{\Gamma(\mu)}{(c-1)!}\Rres^\mu_c$.
\end{thm}

The classical Poincar\'e residue takes a meromorphic form with a simple pole to a form on the polar hypersurface and is signed; here the object with the pole is a positive density and the residue is a positive density on the stratum. The two agree up to sign and normalisation where both make sense. The sanity check in one variable: for $K=x^{2k}$ on $\R$ with $\mu=1/2k$ and $\varphi\,dx=dx$, the residue of $|x|^{-1}|dx|$ at the origin is $1$, the two sides give $2$, and $\Rres^\mu_1=\frac1k\delta_0$, which is the coefficient of $n^{-1/2k}$ in $\int e^{-nx^{2k}}dx=\Gamma(\frac1{2k})n^{-1/2k}/k$ divided by $\Gamma(\mu)$.

\subsection{The leading term with insertion}\label{sec:leading}

Let $\lambda$ be the minimum of the wall exponents $(h_i+1)/2k_i$ over the components with real points and $m$ the maximum number of walls of exponent $\lambda$ through a point of $E$. Extremality forces the zero-order condition on every exact $\lambda$-resonant stratum, since a resonant wall with $2k\lambda=h+1+\alpha$, $\alpha\ge1$, would have exponent below $\lambda$. So the stratum measures $\nu^\lambda_c$ exist for every $c$, and the deepest one describes the leading term.

\begin{thm}[Leading asymptotic with insertion]\label{thm:leading}
For every smooth $f$ whose pull-back vanishes on a neighbourhood of $D_{m+1}$,
\[
n^{\lambda}(\log n)^{-(m-1)}\,\Zcal_n[f]\longrightarrow\int_Xf\circ\pi\,d\nu^\lambda_m=\frac{\Gamma(\lambda)}{(m-1)!}\int_{S^\lambda_m}f\circ\pi\,d\Rres^\lambda_m .
\]
If $f\ge0$ is positive at the image of a point of $S^\lambda_m$ at which the prior is positive, the limit is positive and $\Zcal_n[f]\sim\big(\int f\circ\pi\,d\nu^\lambda_m\big)n^{-\lambda}(\log n)^{m-1}$. The leading stratum measure is finite, with $\nu^\lambda_m(X)\le c_{\lambda,m-1}(1)$, and with equality when $D_{m+1}=\varnothing$.
\end{thm}

The admissibility hypothesis is vacuous when $D_{m+1}$ is empty, which is the case whenever the deepest points of $E$ have depth $m$; in general it says that $f$ vanishes near the points where more than $m$ walls meet, and the general leading term for such $f$ is given by the chart formula of \cref{thm:graded}, whose contributions from the deeper points are not attributed to any single stratum.

\begin{example}[The running examples]\label{ex:population_examples}
For \cref{ex:planes} the components are the planes $E_1=\{x=0\}$, $E_2=\{y=0\}$ with $(k,h)=(1,0)$, $\lambda=1/2$, $m=2$, and $D_3=\varnothing$, so every observable is admissible at depth two. The twisted density is $\varphi\,dx\,dy\,dz/|xy|$, with simple poles along both planes. At depth two the exact stratum is the axis; each of the four quadrants around it contributes the iterated residue with a factor $1/2$ per wall, and
\[
\nu^{1/2}_2=\sqrt\pi\,\varphi(0,0,z)\,dz\quad\text{on the axis},\qquad \Zcal_n[f]\sim\sqrt\pi\Big(\int_{-1}^1f(0,0,z)\varphi(0,0,z)\,dz\Big)n^{-1/2}\log n .
\]
The posterior concentrates on the axis with density proportional to the prior along it, and the leading expectation of $f$ is its prior-weighted average along the axis. At depth one the exact stratum is the two planes minus the axis, $X_1=U\setminus\{x=y=0\}$, and
\[
\nu^{1/2}_1=\sqrt\pi\Big(\varphi(x,0,z)\frac{dx\,dz}{|x|}+\varphi(0,y,z)\frac{dy\,dz}{|y|}\Big) ,
\]
with infinite mass near the axis. For $f$ vanishing near the axis, $c_{1/2,0}(f)=\int f\,d\nu^{1/2}_1$ is the coefficient of $n^{-1/2}$ without a logarithm. For $f$ not vanishing on the axis the $n^{-1/2}$ coefficient is not this divergent integral but a finite part in which the axis and the planes share the constant non-canonically; what is canonical is the $n^{-1/2}\log n$ term, and the class of $c_{1/2,0}$ on observables modulo those vanishing near the axis. For \cref{ex:mixed}, $\lambda=1/6$ with $m=1$, the exact stratum at $(1/6,1)$ is the line $\{y=0\}$ minus the origin, and since the wall $\{x=0\}$ has exponent $1/2>1/6$ the weight $x^{0}(x^{2})^{-1/6}=x^{-1/3}$ is integrable up to the origin: the leading measure is $\frac{\Gamma(1/6)}{6}\,\varphi(x,0)\,x^{-1/3}dx$ on $[0,1]$, finite, and no admissibility is needed.
\end{example}

\input{figures/x2y2}

\subsection{The Laurent data and the three tiers}\label{sec:tiers}

The stratum measures describe the top logarithmic coefficient at each exponent under the zero-order condition. All the coefficients are described at once by a single meromorphic function. For $0<\operatorname{Re}s<\lambda$ the Mellin transform of the partition function in $n$ is, by Fubini,
\begin{equation}\label{eq:zeta_global}
\mathcal Z_f(s)=\int_0^\infty n^{s-1}\Zcal_n[f]\,dn=\Gamma(s)\int_Wf\,K^{-s}\,\varphi\,dw=\Gamma(s)\int_U(f\circ\pi)\,(K\circ\pi)^{-s}\,\pi^*(\varphi\,dw) ,
\end{equation}
Watanabe's zeta function of the pair $(K,\varphi)$ with the observable inserted. It continues meromorphically to $\mathbb C$ with poles on the lattice, and the expansion of \cref{thm:population_expansion} is equivalent to the statement
\begin{equation}\label{eq:laurent}
c_{\mu,q}(f)=\frac{(-1)^{q+1}}{q!}\,\big[(s-\mu)^{-(q+1)}\big]\,\mathcal Z_f(s) ,
\end{equation}
the coefficient of $n^{-\mu}(\log n)^q$ being the Laurent coefficient of order $q+1$ at $s=\mu$. Every coefficient is thus the pairing of the amplitude with a Laurent coefficient of the meromorphic distribution-valued function $s\mapsto(K\circ\pi)^{-s}\pi^*(\varphi\,dw)$, whose poles sit on the resonant strata. This is the definition from which the two closed forms below are evaluations, and it is the form in which the empirical coefficients of \cref{sec:empirical} will be obtained by replacing $\Gamma(s)$ with the fluctuation function.

\paragraph{One resonant coordinate.} Suppose that at $\mu$ only one wall $E_{i_0}$ resonates near the points in question, with $\alpha=2k_{i_0}\mu-h_{i_0}-1\in\N$. Then the pole of \eqref{eq:zeta_global} is simple, there is no logarithm, and in a chart with normal coordinate $u$ for $E_{i_0}$ and tangential coordinates $w$,
\begin{equation}\label{eq:tier2}
c_{\mu,0}(f)=\frac{\Gamma(\mu)}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\eta\,(0,w)\;\prod_{i\ne i_0}w_i^{h_i}\Big(\prod_{i\ne i_0}w_i^{2k_i}\Big)^{-\mu}\,dw ,
\end{equation}
where $\eta$ is the localised amplitude and FP is the Hadamard finite part in those $w_i$ with $(h_i+1)/2k_i<\mu$, namely the subtraction of the Taylor polynomial of $\partial^\alpha_u\eta$ in $w_i$ of degree below $2k_i\mu-h_i-1$; when $\mu$ is below every other exponent the integral converges and no finite part is needed. This is the pairing with $\delta^{(\alpha)}(u)\otimes\mathrm{FP}\,w^{h-2k\mu}$. In \cref{ex:mixed} the leading term is the case $\alpha=0$ and the first correction at $n^{-1/3}$ the case $\alpha=1$, both with convergent integrals since $1/3<1/2$:
\[
c_{1/3,0}(f)=\frac{\Gamma(1/3)}{6}\int_0^1\partial_y\eta(x,0)\,x^{-2/3}\,dx,\qquad \eta=\varphi\cdot f .
\]

\paragraph{Ties.} When $c$ walls resonate at $\mu$ the pole has order $c$. The coefficient of the top power $(\log n)^{c-1}$ is the graded formula \eqref{eq:graded}, a product of normal deltas against the residue density on the face. The lower powers are read off the Laurent expansion: Taylor-expanding the amplitude in the coordinates $u_J$ to order $\alpha$ and integrating $u_J^{h_J+\alpha-2k_Js}$ over the $J$-cube produces the factor $\prod_{j\in J}(2k_j(\mu-s))^{-1}$ times the tangential integral of $\partial^\alpha_J\eta(0_J,w)/\alpha!$ against $w^{h-2ks}$; expanding that tangential integral around $s=\mu$ contributes the powers of $\log w^{2k}$, and the expansion of $\Gamma(s)$ contributes derivatives of the Gamma function. A face $J'\supsetneq J$ resonating at the same $\mu$ makes the tangential integral itself singular, raising the pole order, and its finite part is what the lower coefficients compute. In the simplest tie, \cref{ex:planes} at $\mu=1/2$ with amplitude $\eta=\varphi f$ restricted to a slice $z=$ const, one finds, with $\eta_s=\Gamma(s)\eta$,
\[
c_{1/2,1}=\frac{\eta_{1/2}(0,0)}4,\qquad c_{1/2,0}=-\frac{\partial_s\eta_s(0,0)|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}{x}\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}{y}\,dy
\]
per quadrant and per $z$: the lower logarithm at a tie is the derivative in the exponent at the deepest stratum plus finite parts of the amplitude along the subfaces. The derivative in the exponent, here $\Gamma'(1/2)\eta(0,0)$, becomes in the empirical case the index derivative of the fluctuation function.

\subsection{Population posterior expectations}\label{sec:population_posterior}

The expectation $\E_\infty[f]=\Zcal_n[f]/\Zcal_n[1]$ is the quotient of two expansions in the same scale, and the leading block of the denominator is $c\,(\log n)^{m-1}$ with $c>0$, so the quotient is an expansion in the sense of \cref{sec:scale} with coefficients rational in $\log n$ (\cref{app:expansion_algebra}). Three cases arise at leading order, according to how $f$ meets the leading strata.

\begin{itemize}
\item \emph{Generic observable.} If $f\circ\pi$ does not vanish identically on some exact stratum $S^\lambda_m$, the exponents and logarithmic degrees of numerator and denominator agree and
\[
\E_\infty[f]\longrightarrow\frac{\int f\circ\pi\,d\nu^\lambda_m}{\nu^\lambda_m(X)} ,
\]
the average of $f$ against the normalised leading stratum measure. The posterior concentrates on the deepest exact strata of lowest exponent, with the density \eqref{eq:face_density}.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on all of $S^\lambda_m$ but not on all leading strata of smaller depth, the exponent is unchanged and the logarithmic degree drops: $\E_\infty[f]\sim D(\log n)^{-(m-m')}$ with $m'<m$ the largest depth of a leading stratum on which $f$ survives. This is \cref{ex:planes} with $f=x^2$: the expectation decays like $1/\log n$, the rate at which the posterior concentrates on the axis.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$, the exponent of $\Zcal_n[f]$ is strictly larger and $\E_\infty[f]\sim Dn^{-(\mu-\lambda)}(\log n)^{q-(m-1)}$ decays as a power. The observable $f=K$ is the canonical instance: $K\circ\pi$ vanishes to order $2k_i$ along every wall, shifting every exponent by exactly one, so $\E_\infty[K]\sim\lambda/n$, and indeed $\E_\infty[K]=-\frac{d}{dn}\log\Zcal_n[1]=\frac\lambda n-\frac{m-1}{n\log n}+\cdots$ exactly.
\end{itemize}

\input{figures/wall_crossing}

As the observable varies in a family, the vanishing orders along the walls are generically constant and change only at special values, where the exponent of $\E_\infty[f_\tau]$ jumps by a rational amount determined by $(k_i,h_i,l_i)$. This wall-crossing is the discrete signal by which expectation values report the structure of $W_0$. The full expansion of the quotient, to all orders, is deferred to \cref{sec:posterior}, where it is treated together with its empirical counterpart.

%%%%%%%%%% FILE sections/08_fluctuation.tex %%%%%%%%%%
\section{The fluctuation function}\label{sec:fluctuation}

The population expansion is built from one-variable integrals $\int u^he^{-nu^{2k}}du$, whose value is a Gamma function times a power of $n$. When the sample enters, the exponent acquires the term $\sqrt n\,u^k\zeta(u)$ of \cref{sec:setting}, and the same one-variable integral produces a different special function. This section introduces it, records the algebra it satisfies, and explains why that algebra is the whole mechanism by which the data enters the coefficients.

\subsection{The one-variable computation}

Take a single normal coordinate with data $(k,h)$ and freeze the field at a constant $a$. The substitution $t=nu^{2k}$ gives
\begin{equation}\label{eq:one_variable_field}
\int_0^\infty u^h\,e^{-nu^{2k}+\sqrt n\,u^ka}\,du=\frac{n^{-\mu}}{2k}\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}\,dt,\qquad \mu=\frac{h+1}{2k} ,
\end{equation}
because $\sqrt n\,u^k=\sqrt t$. The exponent is unchanged from the population case; the constant $\Gamma(\mu)$ has become a function of $a$.

\begin{defn}[Fluctuation function]\label{def:fluctuation}
For $\mu>0$ and $a\in\R$,
\begin{equation}\label{eq:fluctuation}
S_\mu(a)=\int_0^\infty t^{\mu-1}\,e^{-t+a\sqrt t}\,dt .
\end{equation}
\end{defn}

The integral converges for every $a$, since $-t+a\sqrt t=-(\sqrt t-a/2)^2+a^2/4$, and $S_\mu(0)=\Gamma(\mu)$. This is Watanabe's fluctuation function \citep[Def.~5.8]{watanabeAlgebraicGeometryStatistical2009} at unit temperature; a temperature $\beta$ is absorbed by $n\mapsto\beta n$ and $a\mapsto\sqrt\beta\,a$. Its probabilistic meaning is immediate from \eqref{eq:fluctuation}: $S_\mu(a)/\Gamma(\mu)=\E\,e^{a\sqrt T}$ for $T\sim\operatorname{Gamma}(\mu,1)$, the moment generating function of $\sqrt T$. The radial variable $t=nu^{2k}$ is the loss measured in units of $1/n$, its law under the population Gibbs weight is $\operatorname{Gamma}(\mu,1)$, and the sample tilts that law by $e^{a\sqrt t}$.

\subsection{The ladder}

\begin{lem}\label{lem:ladder}
For $\mu>0$: (i) $\partial_aS_\mu=S_{\mu+1/2}$; (ii) $S_{\mu+1}(a)=\frac a2S_{\mu+1/2}(a)+\mu S_\mu(a)$; (iii) $S_\mu''=\frac a2S_\mu'+\mu S_\mu$; (iv) $S_1(a)=\frac a2S_{1/2}(a)+1$; (v) $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}\big(1+\operatorname{erf}(a/2)\big)$.
\end{lem}

\begin{proof}
(i) is differentiation under the integral, since $\partial_ae^{a\sqrt t}=\sqrt t\,e^{a\sqrt t}$ raises the power of $t$ by one half. (ii) follows from $\int_0^\infty\frac{d}{dt}\big[t^\mu e^{-t+a\sqrt t}\big]dt=0$, whose integrand is $(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$; (iii) is (ii) rewritten with (i); (iv) is the same computation at $\mu=0$ on $[\varepsilon,T]$ with $\varepsilon\to0$; (v) is the substitution $u=\sqrt t$ and completion of the square.
\end{proof}

Property (i) is the \emph{ladder}: differentiating in the field variable raises the index by one half. Property (iii) is Weber's equation in disguise: under $S_\mu(a)=e^{a^2/8}f(a/\sqrt2)$ it becomes $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $-2\mu$, so that
\begin{equation}\label{eq:weber}
S_\mu(a)=2^{1-\mu}\Gamma(2\mu)\,e^{a^2/8}\,D_{-2\mu}\big(-a/\sqrt2\big)
\end{equation}
in terms of the standard parabolic cylinder function \citep[\S12.5]{NIST:DLMF}. The raising and lowering operators $b^\dagger=\partial_a$ and $b=2\partial_a-a$ satisfy $[b,b^\dagger]=1$ and $b^\dagger S_\mu=S_{\mu+1/2}$, $bS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>1/2$, the recurrence (ii) being the statement that $b$ lowers. The span of the $S_\mu$ along an orbit $\mu+\frac12\mathbb Z$ is a module over the Weyl algebra, and the orbit of $\mu=1/2$, which is the regular case, is distinguished: there $S_{(n+1)/2}=\partial_a^nS_{1/2}$ and every fluctuation function is a derivative of $e^{a^2/4}\operatorname{erf}(a/2)$, with the vacuum $S_{1/2}$ annihilated modulo constants by $b$. For a singular model with $\mu\notin\frac12\mathbb Z$ the orbit has no lowest weight and the parabolic cylinder function is genuinely needed. Weber's equation is also the source of Watanabe's equations of state relating Bayes and Gibbs generalisation and training errors \citep[Thm~5.11, \S1.5]{watanabeAlgebraicGeometryStatistical2009}; we will not need them.

The structural consequence for the expansions is this. Wherever the population theory produces a Gamma function $\Gamma(\mu)$ from a normal integral, the empirical theory produces $S_\mu$ evaluated on the field. Wherever the population theory differentiates the amplitude in a normal direction, the empirical theory also differentiates the factor $e^{\sqrt n u^k\zeta}$, and by the chain rule and \cref{lem:ladder}(i) every derivative of the field brings $S_{\mu+1/2}$, $S_{\mu+1}$, and so on. The corrections therefore involve a finite ladder of fluctuation functions of increasing index multiplied by derivatives of the field, in a pattern fixed by the Leibniz rule. In one variable it reads
\begin{equation}\label{eq:one_dim_coefficients}
\int_0^1\eta(u)u^he^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}du\sim\sum_{j\ge0}\frac{\partial_u^j\big[\eta\,S_{\mu_j}(\zeta)\big](0)}{j!\,2k}\,n^{-\mu_j},\qquad\mu_j=\frac{h+j+1}{2k} ,
\end{equation}
so that the $j$-th coefficient is the $j$-th derivative at the origin of the amplitude times the fluctuation function of the field at the $j$-th index: $\eta S_{\mu_0}(\zeta)/2k$, then $(\eta'S_{\mu_1}(\zeta)+\eta\zeta'S_{\mu_1+1/2}(\zeta))/2k$, then $(\eta''S_{\mu_2}+2\eta'\zeta'S_{\mu_2+1/2}+\eta\zeta''S_{\mu_2+1/2}+\eta\zeta'^2S_{\mu_2+1})/(2\cdot2k)$, and so on. This is the one-dimensional form of everything in \cref{sec:empirical}, and it is proved in \cref{app:chart_proofs} by scaling $u=n^{-1/2k}x$ and Taylor-expanding the smooth factor $\eta(u)e^{x^k\zeta(u)}$ in $u$ to finite order with a remainder.

\subsection{Index derivatives and logarithms}

The logarithms of the population expansion arise, in the Mellin picture, from higher-order poles, and in the coefficients they appear as derivatives of $\Gamma$ with respect to its argument. In the empirical theory they are derivatives of $S$ with respect to the index:
\begin{equation}\label{eq:index_derivative}
\partial_\nu^\ell S_\nu(a)=\int_0^\infty t^{\nu-1}(\log t)^\ell\,e^{-t+a\sqrt t}\,dt ,
\end{equation}
by differentiation under the integral, which is legitimate for $\nu>0$. A term $(c-\log t)^p$ in a radial integral thus becomes the operator $(c-\partial_\nu)^p$ applied to $S_\nu$, and $\sum_p\frac{z^p}{p!}(c-\partial_\nu)^pS_\nu=e^{zc}S_{\nu-z}$ is the translation in the index. In the smallest example with a logarithm, $K=x^2y^2$ with a constant field $a$ on the unit square, the radial density of $u=xy$ is $-\log u$ and
\[
\int_0^1\!\!\int_0^1e^{-nx^2y^2+a\sqrt n\,xy}\,dx\,dy=\frac1{4\sqrt n}\int_0^n t^{-1/2}e^{-t+a\sqrt t}(\log n-\log t)\,dt=\frac{n^{-1/2}}4\Big[S_{1/2}(a)\log n-\partial_\nu S_\nu(a)\big|_{1/2}\Big]+o(n^{-1/2}) ,
\]
which at $a=0$ is $\frac{n^{-1/2}}4[\Gamma(\tfrac12)\log n-\Gamma'(\tfrac12)]$. The coefficient below the top power of the logarithm is an index derivative of the fluctuation function, and this is the general pattern: the lower logarithmic orders at a tied exponent carry $\partial_\nu^\ell S_\nu(\zeta)$, and the passage from the population to the empirical theory replaces $\Gamma^{(\ell)}(\mu)$ by $\partial_\nu^\ell S_\nu(\zeta)|_{\nu=\mu}$ throughout. The higher index derivatives satisfy an inhomogeneous Weber equation obtained by differentiating (iii) in $\mu$, a triangular system that determines them recursively.

\subsection{The field in the exponent, and the incomplete function}

In the actual integrals the radial variable runs over a bounded range, $t\le nb^{2k}$, and the fluctuation function is replaced by its incomplete version $S_\mu(a;T)=\int_0^Tt^{\mu-1}e^{-t+a\sqrt t}dt$, which satisfies the same ladder in $a$ and the same index-derivative identity, and an inhomogeneous Weber equation whose right side $-T^\mu e^{-T+a\sqrt T}$ is exponentially small in $T=nb^{2k}$. Replacing the incomplete function by the complete one therefore costs $O(e^{-\varepsilon n})$, invisible in the scale, exactly as the localisation to a neighbourhood of the divisor did in the population case. The field itself is not constant, and the way its variation enters is through the normal derivatives in \eqref{eq:one_dim_coefficients}; what is constant is the structure, the finite ladder of indices and the Leibniz pattern of derivatives, and the next section makes it the statement of a theorem in every dimension.

%%%%%%%%%% FILE sections/09_empirical.tex %%%%%%%%%%
\section{The empirical expansion for a fixed sample}\label{sec:empirical}

Fix the sample. The empirical partition function is then a deterministic integral of the same kind as the population one, with the field of \cref{sec:setting} in the exponent, and everything in Part~II goes through with one substitution: the Gamma function in the stratum measures becomes the fluctuation function of the field along the stratum, and derivatives of the field enter the corrections through the ladder. This section states that theorem, describes the coefficients in the same three ways as before, and works out what enters at the first few orders.

\subsection{Root fields}

Pulling the standard form \eqref{eq:standard_form} back along the resolution, on a chart where $K\circ\pi=u^{2k}$ we have $\sqrt{K\circ\pi}=|u^k|$ and
\begin{equation}\label{eq:exponent_chart}
-nK_n\circ\pi=-nu^{2k}+\sqrt n\,|u^k|\,(\psi_n\circ\pi) .
\end{equation}
The standardised process $\psi_n$ extends smoothly to the resolution \citep[Main Theorem~6.1]{greybook}, but the function that enters the exponent is $|u^k|\psi_n\circ\pi$, and on a two-sided normal coordinate the absolute value means that the restriction of $\psi_n\circ\pi$ to the two sides of a wall enters with the sign of $u^k$ absorbed differently. The natural object is therefore a \emph{root field}: a bounded measurable function $\psi$ on $U$ together with, for every chart and every orthant of its normal coordinates, a smooth representative $\hat\psi$ on the closed box, agreeing with $\psi$ off the walls. Off the walls the representatives are determined; on the walls they record the one-sided limits, which need not agree, and it is the representatives that the coefficients see. Writing $\zeta=\hat\psi$ for the chart representative, the chart integral of $Z_n[f]$ is
\begin{equation}\label{eq:empirical_chart}
Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du ,
\end{equation}
with $\eta$ the localised amplitude of \cref{sec:population} and both $\eta$ and $\zeta$ smooth on the closed cube. For an analytic model $\zeta$ is analytic for each finite $n$; nothing below uses this.

\subsection{The expansion}

\begin{thm}[The empirical expansion, fixed sample]\label{thm:empirical_expansion}
Let $\eta,\zeta$ be smooth on a neighbourhood of the closed cube. Then $Z_n(\eta;\zeta)$ has a cutoff expansion in the sense of \cref{sec:scale},
\[
Z_n(\eta;\zeta)\sim\sum_{\mu\in Q^{-1}\N}\sum_{q=0}^{d-1}c_{\mu,q}(\eta;\zeta)\,n^{-\mu}(\log n)^q ,
\]
with coefficients independent of the cutoff, and with a remainder constant that is uniform over all $(\eta,\zeta)$ in a $C^R$ ball, $R=R(U)$. Assembled over the charts of the resolution with the partition of unity of \cref{sec:population}, the empirical partition function of a bounded smooth root field has a cutoff expansion on the common lattice with logarithmic degree at most $d-1$, whose coefficients at zero field are the population coefficients.
\end{thm}

The proof is the proof of \cref{thm:population_expansion} with the field carried along: Fubini along the resonant normal coordinates, the one-dimensional expansion \eqref{eq:one_dim_coefficients} with an explicit constant depending on the slice only through a bound on $\zeta$ and bounds on the normal jets of $\eta e^{\tau\zeta}$, and dominated convergence in the tangential variables (\cref{app:chart_proofs}). The uniformity in $C^R$ balls is what allows the sample to vary: for a family of samples whose fields lie in a fixed ball the remainder is bounded uniformly, which is the form the statement takes in probability in \cref{sec:limit}.

\subsection{The coefficients}

Three descriptions, each the empirical form of one in \cref{sec:population}.

\paragraph{Geometric: the top logarithmic order.} For an observable admissible at depth $c$, the coefficient of $n^{-\mu}(\log n)^{c-1}$ is the graded formula \eqref{eq:graded} with the amplitude $A$ replaced by $A\cdot S_\mu(\zeta)/\Gamma(\mu)$:
\begin{equation}\label{eq:empirical_graded}
c_{\mu,c-1}(\eta;\zeta)=\sum_{|J|=c}\frac{\prod_{j\in J}(2k_j)^{-1}}{(c-1)!\prod_{j\in J}\alpha_j!}\int_{u_J=0}\partial^\alpha_J\big[\eta\,S_\mu(\zeta)\big](0_J,w)\;w^{h}\big(w^{2k}\big)^{-\mu}\,dw .
\end{equation}
In resolved form: the normal jet of order $\alpha$ of $(f\circ\pi)\,S_\mu(\hat\psi)$ along the exact stratum $S^\mu_c$, integrated against the weighted logarithmic residue $\Rres^\mu_c$ of \cref{sec:residue}. The geometry is that of the population expansion; the sample enters as a pointwise reweighting of the residue density by the fluctuation function of the standardised field, together with its normal derivatives, which raise the index by halves. At the leading pair $(\lambda,m)$, for $f$ admissible at depth $m$,
\begin{equation}\label{eq:empirical_leading}
n^{\lambda}(\log n)^{-(m-1)}Z_n[f]\longrightarrow\frac1{(m-1)!}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi)\,d\Rres^\lambda_m ,
\end{equation}
which at $\psi=0$ is \cref{thm:leading}. Two things are worth noticing. The leading empirical coefficient depends on the field only through its values on the leading stratum: the posterior at leading order lives on the deepest exact stratum and is the population stratum measure reweighted by $S_\lambda(\hat\psi)$. And the reweighting is by a positive function, so the positivity and finiteness statements of \cref{thm:leading} survive, with $S_\lambda(\hat\psi)\le S_\lambda(\|\psi\|_\infty)$ giving domination by a multiple of the population measure.

\paragraph{Analytic: the fluctuation zeta function.} The Mellin transform of the frozen partition function in $n$ is, by \eqref{eq:one_variable_field} applied pointwise,
\begin{equation}\label{eq:fluctuation_zeta}
\mathcal Z_f(s;\psi)=\int_0^\infty n^{s-1}Z_n[f]\,dn=\int_W f\,K^{-s}\,S_s(\psi)\,\varphi\,dw ,
\end{equation}
Watanabe's zeta function with the Gamma factor replaced, inside the integral, by the fluctuation function of the standardised field, at a complex index. Every coefficient of \cref{thm:empirical_expansion}, at every logarithmic order, is a Laurent coefficient of this function exactly as in \eqref{eq:laurent}: $c_{\mu,q}=\frac{(-1)^{q+1}}{q!}[(s-\mu)^{-(q+1)}]\mathcal Z_f(s;\psi)$. This is the definition from which the geometric formula is an evaluation, and it is the description that covers the lower logarithmic orders at ties, where no closed geometric formula of the form \eqref{eq:empirical_graded} exists: there the index derivatives $\partial_\nu^\ell S_\nu(\zeta)$ of \cref{sec:fluctuation} carry the logarithms, in Taylor-subtracted chart expressions.

\paragraph{Algebraic: the generating identity.} Every empirical coefficient is a convergent series of population coefficients with powers of the field inserted into the observable:
\begin{equation}\label{eq:generating}
c_{\mu,q}(\eta;\zeta)=\sum_{r\ge0}\frac1{r!}\,c^{\mathrm{pop}}_{\mu+r/2,\,q}\big(\eta\,(u^k\zeta)^r\big) ,
\end{equation}
unconditionally convergent. The half-integer shift of the exponent is the bookkeeping for the $\sqrt n$ in front of the field: in the radial variable $t=nu^{2k}$ the term $(\sqrt t\,\zeta)^r/r!$ of the exponential is the insertion $(u^k\zeta)^r$ against the Gamma law at index $\mu+r/2$, and $S_\mu(a)=\sum_ra^r\Gamma(\mu+r/2)/r!$ is the same identity at a single point. The proof is by truncation of the exponential and never exchanges the series with the integral, and each term depends on the field only through its jet of a fixed order determined by $(h,k,\mu)$. The identity says that the population theory determines the empirical one: the sample enters through the population coefficients of the modified observables $f\,H^r$, $H=\sqrt K\,\psi$, with the exponent climbing by halves.

\subsection{What enters at the first orders}\label{sec:first_orders}

The abstract descriptions become concrete in the two situations of \cref{sec:tiers}.

\paragraph{One resonant coordinate.} If at $\mu$ only the wall $E_{i_0}$ resonates, with normal order $\alpha$, then with the amplitude $A=\eta$ and the slice notation of \cref{sec:tiers},
\begin{equation}\label{eq:empirical_tier2}
c_{\mu,0}(\eta;\zeta)=\frac{1}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\big[\eta\,S_\mu(\zeta)\big](0,w)\;w^{h_L}\big(w^{2k_L}\big)^{-\mu}\,dw ,
\end{equation}
with the finite part needed only past the exponents of the other walls. Under the generic hypothesis that $\mu_1=\lambda+1/2k_{i_0}$ is below every other exponent, the two leading coefficients are plain integrals over the face, valid for all smooth $\eta,\zeta$ with no admissibility hypothesis:
\begin{align}
c_{\lambda,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\lambda}\,\eta(0,w)\,S_\lambda\big(\zeta(0,w)\big)\,dw,\label{eq:c_lambda}\\
c_{\mu_1,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\mu_1}\Big[\partial_u\eta(0,w)\,S_{\mu_1}\big(\zeta(0,w)\big)+\eta(0,w)\,\partial_u\zeta(0,w)\,S_{\mu_1+1/2}\big(\zeta(0,w)\big)\Big]dw,\label{eq:c_mu1}
\end{align}
with $p(w)=w^{2k_L}$, and every other coefficient at a lattice exponent $\le\mu_1$ vanishes. The first correction is the one-dimensional coefficient $C_1$ of \eqref{eq:one_dim_coefficients} for the slice $(\eta(\cdot,w),\zeta(\cdot,w))$, integrated over the face against the residue density. Only the values and first normal derivatives of the amplitude and of the field on the face enter; the field's derivative comes with the raised index $\mu_1+\frac12$. In \cref{ex:mixed} this gives the leading term at $n^{-1/6}$ and the first correction at $n^{-1/3}$ as integrals over the wall $\{y=0\}$ against $x^{-1/3}dx$ and $x^{-2/3}dx$, and the second correction at $n^{-1/2}$ is the first place where a logarithm and the other wall appear.

\paragraph{Ties.} At a tie of $c$ walls the top logarithm is \eqref{eq:empirical_graded}, and the lower ones follow the Laurent computation of \cref{sec:tiers} with $\Gamma$ replaced by $S$. For \cref{ex:planes} at $\mu=1/2$, with $\eta_s=\eta\,S_s(\zeta)$ evaluated on a slice $z=$ const,
\[
c_{1/2,1}=\frac{\eta(0,0)S_{1/2}(\zeta(0,0))}4,\qquad c_{1/2,0}=-\frac{\eta(0,0)\,\partial_\nu S_\nu(\zeta(0,0))|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}x\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}y\,dy
\]
per quadrant and per $z$: the coefficient of $n^{-1/2}\log n$ is the fluctuation function of the field on the axis, and the coefficient of $n^{-1/2}$ is its index derivative there plus finite parts of $\eta S_{1/2}(\zeta)$ along the two planes. Integrating over $z$ against the prior gives the coefficients of $Z_n[f]$ for this example: the sample enters the leading term through the values of $\psi_n$ on the axis, and the first correction through its values on the planes as well.

\subsection{How much of the field is seen}

Each coefficient depends on the field only through finitely many of its normal jets on the resonant strata, of an order fixed by $\mu$: the values for the leading term, first derivatives for the first correction, and so on, exactly as for the observable in \cref{thm:jet}. This dependence is continuous, and locally Lipschitz on jet balls: if two fields have jets of the relevant order within $\delta$ of each other on the closed cube, the corresponding coefficients differ by at most a constant times $\delta$. Together with the uniformity of the remainder in \cref{thm:empirical_expansion} this is all that the passage to the Gaussian limit needs, and it is why the limit can be taken coefficient by coefficient.

%%%%%%%%%% FILE sections/10_limit.tex %%%%%%%%%%
\section{The limit field}\label{sec:limit}

For a fixed sample the expansion of $Z_n[f]$ is deterministic. Its coefficients are random through the field, and the question of how they behave as the sample grows is a question about the field alone, since the geometry does not move. This section records what is known: the field converges to a Gaussian process, the coefficients converge with it, and averaging over the sample can be carried out for the fluctuation function at a single point, with a threshold that is instructive.

\subsection{Convergence in law of the coefficients}

By Watanabe's theorem \citep[Thm~6.2]{greybook} the standardised empirical process on the resolution converges in law, as $n\to\infty$, to a centred Gaussian process $G$ whose covariance at two points of the resolution is the covariance of the log-likelihood ratio increments $\Cov_X\big(a(X,u),a(X,u')\big)$ in the notation of the standard form. This convergence is a statement about the process as a function on the resolved manifold.

The coefficients of \cref{thm:empirical_expansion} depend on the field only through finitely many normal jets on the faces of the chart cubes, continuously and locally Lipschitz (\cref{sec:empirical}). Hence, if for each chart the vector of jets of $\hat\psi_n$ of the relevant order converges in law, the coefficients converge in law to the same functionals evaluated on the jets of $G$, jointly for any finite set of exponents and logarithmic degrees, and the normalised remainders of the expansion converge accordingly. In particular
\[
n^{\lambda}(\log n)^{-(m-1)}Z_n[f]\ \Longrightarrow\ \frac1{(m-1)!}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat G)\,d\Rres^\lambda_m ,
\]
the leading coefficient evaluated on the Gaussian field along the leading stratum, and the analogous statements hold for every retained coefficient. The convergence of the face jets of the empirical process is a statement about the sample and the model, a functional central limit theorem for finitely many derivatives of $\psi_n$ on the resolution; it is the hypothesis under which the limit theorems are proved, and it is not derived from the geometry. For the leading coefficient only the values on the leading stratum are needed, and there the convergence is Watanabe's theorem itself.

\subsection{Averaging over the sample: the fluctuation function of a Gaussian}

For a single centred Gaussian value $a\sim N(0,v)$, Fubini gives
\begin{equation}\label{eq:gaussian_average}
\E\,S_\lambda(a)=\int_0^\infty t^{\lambda-1}e^{-t}\,\E e^{a\sqrt t}\,dt=\int_0^\infty t^{\lambda-1}e^{-(1-v/2)t}\,dt=\Gamma(\lambda)\Big(1-\frac v2\Big)^{-\lambda} ,
\end{equation}
finite exactly when $v<2$, and $+\infty$ otherwise. Two lessons follow. First, the expected leading coefficient of $Z_n[f]$ in the Gaussian limit is the population coefficient with the amplitude reweighted by $(1-v(x)/2)^{-\lambda}$ along the leading stratum, where $v(x)$ is the variance of the limit field at the point $x$: averaging and expanding do not commute, and $\E\,C(G)\ne C(0)$ even though $\E\,G=0$, because the coefficients are nonlinear in the field through the fluctuation function. Second, unnormalised averaging can fail: on the set of the stratum where the variance of the field exceeds $2$ the expected partition function is infinite, although every sample partition function is finite. In the generating identity \eqref{eq:generating} the same threshold appears as the radius of convergence of the Wick series $\sum_j(2^jj!)^{-1}c^{\mathrm{pop}}_{\mu+j,q}(\eta\,W^j)$, obtained by taking expectations term by term, with $W$ the variance profile of the scaled field: odd terms vanish, even ones contribute $(2j)!/(2^jj!)$ times the variance power, and the sum is $e^{W/2}$ distributed over the shifted exponents. The series converges under an exponential moment $\E\,e^{\delta\|J_R\zeta\|^2}<\infty$ with $\delta>\frac14$ on the relevant jets, which is the condition $W<2$ in jet form.

None of this affects the posterior. The posterior expectation is a ratio, bounded by $\|f\|_\infty$ for every sample, and its averaged behaviour is a different question, taken up in \cref{sec:averaging}. The threshold concerns the unnormalised evidence only.

\subsection{What is a hypothesis}

The picture of this section rests on three inputs of different standing. That the coefficients are continuous functionals of finitely many jets of the field, and that the remainder is uniform on jet balls, are theorems of the smooth theory. That the empirical process converges to a Gaussian field on the resolution is Watanabe's theorem, consumed as such. That the finitely many normal derivatives of the empirical process on the faces converge jointly in law, which is what the convergence of the subleading coefficients needs, is a hypothesis about the model, plausible under the moment conditions of the standard form but not derived here; for the leading coefficient it is not needed.

%%%%%%%%%% FILE sections/11_posterior.tex %%%%%%%%%%
\section{Posterior expectations}\label{sec:posterior}

The posterior expectation of an observable is the quotient $Z_n[f]/Z_n[1]$ of two expansions on the same lattice. This section says what the quotient looks like, for a fixed sample and to all orders; what its leading term is; and how the three actors interact in it. The organising fact is that nothing new enters: every coefficient of the posterior expectation is a rational function of the coefficients of $Z_n[f]$ and $Z_n[1]$, and all the geometry and all the data are already in those.

\subsection{Blocks and the quotient}

Write $\ell=\log n$ and $x=n^{-1/Q}$. Collecting the logarithmic powers at a fixed exponent $\mu=j/Q$ into one polynomial gives the \emph{block}
\[
B_j(\ell)=\sum_{q\le d-1}c_{j/Q,q}\,\ell^q,\qquad Z_n\sim\sum_jB_j(\log n)\,n^{-j/Q}=\sum_jB_j(\ell)\,x^j ,
\]
so that an expansion in our scale is a power series in $x$ with coefficients polynomial in $\ell$. Blocks rather than individual coefficients are the right unit for division: the inverse of the leading block $B_0(\ell)$ of the denominator is a rational function of $\ell$, not a polynomial. The quotient of two expansions is therefore a power series in $x$ over the field $\R(\ell)$ of rational functions in $\log n$, and its coefficients, the \emph{quotient blocks}
\begin{equation}\label{eq:quotient_blocks}
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) ,
\end{equation}
are computed by the ordinary recursion for the quotient of power series, with $A_j,B_j$ the blocks of numerator and denominator counted from the first exponent at which the denominator is nonzero.

\begin{thm}[Posterior expectation, fixed sample, all orders]\label{thm:posterior_quotient}
Let $A_j$ and $B_j$ be the blocks of the expansions of $Z_n[f]$ and $Z_n[1]$ from \cref{thm:empirical_expansion}, and suppose the leading block $B_0$ is a nonzero polynomial, as it is when the prior is positive somewhere on the leading stratum. Then for every $J\ge1$,
\[
\frac{Z_n[f]}{Z_n[1]}=\sum_{j<J}R_j(\log n)\,n^{-j/Q}+O\big(n^{-J/Q}(1+\log n)^{(d-1)(J+1)}\big) ,
\]
with $R_j$ the quotient blocks \eqref{eq:quotient_blocks}, kept exact as rational functions of $\log n$. Each $R_j$ may be expanded in inverse powers of $\log n$ to any order if a pure power-logarithm form is wanted.
\end{thm}

The remainder is $O$ and not $o$ at that scale: the omitted block survives at exactly the order of the bound. The theorem is deterministic algebra over the two expansions, and its content is the statement that nothing else is true at this level: the quotient of two asymptotic expansions is the formal quotient, and the terms obtained by expanding $1/Z_n[1]$ are exactly the terms of the recursion.

\subsection{The source and the connected coefficients}

The cleaner organisation of the higher posterior moments is through a source. For bounded smooth $f$,
\begin{equation}\label{eq:source}
\partial_\varepsilon\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f]}{Z_n[1]},\qquad \partial_\varepsilon^2\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f^2]}{Z_n[1]}-\Big(\frac{Z_n[f]}{Z_n[1]}\Big)^2 ,
\end{equation}
and in general the $r$-th derivative is the $r$-th posterior cumulant of $f$. Anchoring the logarithm at $Z_n[1]$ makes it a formal logarithm of a series with constant term one, computable by a finite formula, and fixing a source order $R$ makes only the finitely many expansions of $Z_n[f^r]$, $r\le R$, enter. Writing $m_r$ for the quotient-block series of $Z_n[f^r]/Z_n[1]$, the \emph{connected coefficients} $\kappa_r=[\varepsilon^r/r!]\log\sum_rm_r\varepsilon^r/r!$ satisfy
\[
\kappa_1=m_1,\qquad\kappa_{r+1}=m_{r+1}-\sum_{i=0}^{r-1}\binom ri\kappa_{i+1}m_{r-i} ,
\]
with Cauchy products in $x$; at the level of blocks, $\kappa_2(j)=q^{f^2}(j)-\sum_{i\le j}q^f(i)q^f(j-i)$ is the all-orders expansion of the posterior variance. Connected means connected in the source variable; the result is that every posterior cumulant is a universal polynomial in the quotient blocks, and the quotient blocks are the only new objects. The posterior variance is the susceptibility of \citet{baker2025structuralinferenceinterpretingsmall}: the response of $\E[f\mid\Dn]$ to a perturbation of the data enters through exactly these connected coefficients, by the fluctuation--dissipation relation, and this is where the present expansion connects to the measurements it was designed to explain.

\subsection{The leading term}

At leading order the quotient reduces to the ratio of leading blocks, and the three cases of \cref{sec:population_posterior} recur with the fluctuation function inserted. Let $(\lambda,m)$ be the leading pair and suppose $f$ is admissible at depth $m$.

\begin{itemize}
\item \emph{Generic observable.} If $f\circ\pi$ does not vanish identically on $S^\lambda_m$,
\begin{equation}\label{eq:leading_posterior}
\E[f\mid\Dn]\longrightarrow\langle f\rangle_{\hat\psi_n}:=\frac{\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m}{\int_{S^\lambda_m}S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m} ,
\end{equation}
where the limit is understood with the field frozen, that is, as the leading quotient block evaluated on the sample. The posterior at leading order is the residue measure on the leading stratum reweighted by the fluctuation function of the field at each point. When the leading stratum is a single point, the reweighting cancels and $\E[f\mid\Dn]\to f(\text{point})$ regardless of the sample: at a point-like singularity the data cannot move the leading posterior expectation. When the leading stratum has positive dimension the sample redistributes posterior mass along it according to $S_\lambda(\hat\psi_n)$, and since $S_\lambda$ is increasing this favours the parts of the stratum where the empirical loss dips below the population loss.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on $S^\lambda_m$ but not on all leading strata of smaller depth, $\E[f\mid\Dn]\sim D_n(\log n)^{-(m-m')}$ with $D_n$ the ratio of the corresponding reweighted residue integrals.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$ the expectation decays as a power, with a random constant given by the ratio of the first nonvanishing block of $Z_n[f]$ to the leading block of $Z_n[1]$; for $f=K$ the shift is by exactly one and $\E[K\mid\Dn]\sim\lambda/n$ with the fluctuation factors cancelling at this order.
\end{itemize}

\subsection{Tied strata and the two-site phenomenon}

When the leading stratum has several components of the same depth and exponent, the sample decides how the posterior mass is distributed between them, and the outcome has a definite sign. The simplest case is two points carrying population masses $p$ and $1-p$ and posterior weights $U=S_\lambda(a_1)$, $V=S_\lambda(a_2)$, so that the posterior mass of the first point is $Q_p=pU/(pU+(1-p)V)$. If the pair $(U,V)$ is exchangeable, which is the case when the two field values have the same variance,
\begin{equation}\label{eq:two_site}
\E\,Q_p-p=\frac{p(1-p)(1-2p)}2\,\E\Big[\frac{(U-V)^2}{(pU+(1-p)V)((1-p)U+pV)}\Big],\qquad \E\,Q_p\in\big[\min(p,\tfrac12),\max(p,\tfrac12)\big] .
\end{equation}
No moments of $U,V$ are needed, since the kernel is bounded by $1/\min(p,1-p)^2$. Exchangeable disorder moves the averaged posterior mass toward equal allocation: a minority component gains, a majority component loses, and the displacement is strict as soon as $p\ne\frac12$ and $U\ne V$ with positive probability. Two consequences are worth stating. Positivity of an observable does not make its averaged posterior expectation move in a fixed direction; the indicator of a majority component decreases. And $\E[Z_n[f]/Z_n[1]]\ne\E Z_n[f]/\E Z_n[1]$ already in the simplest case, which is the concrete reason the averaged posterior is treated separately in \cref{sec:averaging}.

\subsection{Wall-crossing with data}

The exponents and logarithmic degrees of the posterior expansion are determined by the vanishing orders of $f$ along the walls, exactly as in the population case, and they do not depend on the sample. What the sample changes is the coefficients, and at leading order only through the values of the field on the leading strata. As $f$ varies in a family the exponent of $\E[f\mid\Dn]$ jumps at the same walls as $\E_\infty[f]$, by the same rational amounts. The discrete signal of \cref{sec:population_posterior} survives averaging; the continuous part, the coefficients, acquires a random component with the structure described in the next section.

%%%%%%%%%% FILE sections/12_averaging.tex %%%%%%%%%%
\section{Averaging over the sample}\label{sec:averaging}

The results so far hold sample by sample. The average of a posterior expectation over the sample is a different object, and this short section records what is known about it at leading order, what its exact structure is, and where the theory currently stops.

\subsection{The limit posterior}

At leading order the posterior lives on the leading stratum $S=S^\lambda_m$, and by \eqref{eq:leading_posterior} the posterior expectation is the normalised $S_\lambda$-reweighting of the residue measure by the field along $S$. Passing to the Gaussian limit $G$ of the field, and keeping the radial variable $t=nK\circ\pi$ as a coordinate, the limit object is the random probability measure
\begin{equation}\label{eq:gibbs}
\mu_G(dx\,dt)=\frac{t^{\lambda-1}e^{-t+G(x)\sqrt t}}{D(G)}\,d\rho(x)\,dt,\qquad D(g)=\int_SS_\lambda(g(x))\,d\rho(x) ,
\end{equation}
on $S\times(0,\infty)$, with $\rho=\Rres^\lambda_m$ restricted to the stratum. Its $S$-marginal has the $S_\lambda(G)$-weights and gives $\langle f\rangle_G$ for observables seen through their values on $S$; the radial variable is what makes derivatives in the field precise, the tilt in direction $h$ being the observable $\sqrt t\,h(x)$. In this form the limit posterior is a Gibbs measure with a Gaussian random Hamiltonian, and the tools of that subject apply.

\subsection{Three exact identities}

Let $\mathcal C$ be the covariance kernel of $G$ on $S$ and $\langle\phi\sqrt t\rangle_g=\int\phi\,S_{\lambda+1/2}(g)\,d\rho/D(g)$ the radial-moment weighted integral.

\begin{enumerate}
\item \emph{Fr\'echet differentiability.} $g\mapsto\langle f\rangle_g$ is differentiable on $C(S,\R)$ with the sup norm, with derivative $D\langle f\rangle_g[h]=\langle f\,\sqrt t\,h\rangle_g-\langle f\rangle_g\langle\sqrt t\,h\rangle_g=\Cov_{\mu_g}(f,\sqrt t\,h)$, by the ladder $\partial_aS_\lambda=S_{\lambda+1/2}$.
\item \emph{Stein's identity.} For every $x_0\in S$,
\[
\E\big[G(x_0)\langle f\rangle_G\big]=\E\big[\langle f\,\mathcal C(x_0,\cdot)\sqrt t\rangle_G-\langle f\rangle_G\langle\mathcal C(x_0,\cdot)\sqrt t\rangle_G\big] ,
\]
Gaussian integration by parts on the field, which with two independent replicas of $\mu_G$ reads $\E\langle f(x_1)(\sqrt{t_1}\mathcal C(x_0,x_1)-\sqrt{t_2}\mathcal C(x_0,x_2))\rangle^{\otimes2}_G$.
\item \emph{Covariance interpolation.} With $G_s=\sqrt sG$,
\begin{equation}\label{eq:interpolation}
\E\langle f\rangle_G=\frac{\rho(f)}{\rho(S)}+\int_0^1\E\,H_f(\sqrt s\,G)\,ds,\qquad H_f(g)=\frac12\,\E^{\otimes3}_{\mu_g}\Big[(f(x_1)-f(x_2))\big(t_1\mathcal C(x_1,x_1)-2\sqrt{t_1t_3}\,\mathcal C(x_1,x_3)\big)\Big] ,
\end{equation}
with $|H_f(g)|\le5\|f\|_\infty c\,(2\lambda+\tfrac14)(1+\|g\|_\infty^2)$ when $\mathcal C\le c$ on the diagonal. The averaged posterior expectation differs from the zero-field value, the population posterior expectation on the leading stratum, by an integral over the covariance amplitude of a three-replica response, and only the second moment of $\|G\|_\infty$ enters.
\end{enumerate}

These identities are exact and hold at every temperature and every variance; the threshold $v<2$ of \cref{sec:limit} concerns the unnormalised evidence and does not appear, since the inverse evidence $D(G)^{-1}\le\lambda e^{2}(1+\|G\|_\infty)^{2\lambda}/\rho(S)$ has all moments. Iterating \eqref{eq:interpolation} produces finite-order expansions in the covariance amplitude with exact integral remainders, in which covariance lines between replicas are the bookkeeping. Two cautions: the interpolation to finite order does not give a convergent series in the covariance, and the amplitude $s$ is not the asymptotic parameter $n^{-1/Q}$, so these identities describe the random leading object and its dependence on the field, not the subleading $n$-expansion. The averaged posterior cumulants are packaged by the quenched source $\Psi(\varepsilon)=\E\log\langle e^{\varepsilon f}\rangle_G$, with $\Psi'(0)=\E\langle f\rangle_G$ and $\Psi''(0)=\E\operatorname{Var}_{\mu_G}(f)$, an expected conditional variance; for bounded $f$ its expansion in $\varepsilon$ converges on $|\varepsilon|<\log2/\|f\|_\infty$.

\subsection{Where the theory stops}

Two identifications separate the results of this section from a statement about the model. The first is that the restriction of the empirical process to the leading stratum converges in law to $G$ as a process on $S$, with $\rho$ the residue measure and $\mathcal C$ the covariance of the limit field; for the values on $S$ this is Watanabe's theorem, and it is what the leading term needs. The second is that the leading posterior expectation of the fixed-sample theory, which is a continuous functional of the field, is the functional $\langle f\rangle_G$ of that limit; this is a matter of matching the two constructions and, once done, gives $\lim_n\E[\E[f\mid\Dn]]=\E\langle f\rangle_G$ for every bounded $f$ with no further estimate, since $|E[f\mid\Dn]|\le\|f\|_\infty$ makes the posterior expectations uniformly integrable. The subleading averaged corrections are a further problem: they require rates for the fixed-sample remainders and for the law of the finite-$n$ field, the latter of Edgeworth type, and the exponent lattice rather than $n^{-1/2}$ decides which correction comes first. None of this is attempted here.

%%%%%%%%%% FILE sections/13_formalisation.tex %%%%%%%%%%
\section{What is a theorem}\label{sec:formalisation}

The statements of this paper have been formalised in the Lean theorem prover, in the library \texttt{timaeus-research/grammar} (namespace \texttt{Grammar}), with the resolution of singularities consumed from the library \texttt{hironaka} through its axiom-free exports and the statements about the sample proved in a bridge workspace on top of the formalisation of \citet{greybook}. Every declaration named below has been checked to depend on no axioms beyond \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}. \cref{tab:lean} lists the correspondence; the hypotheses stated in the table are the hypotheses of the formal statements, which in several places are weaker or more specific than the prose above, and the reader should take the table as the precise version.

\begin{table}[p]
\centering\scriptsize
\begin{tabular}{@{}>{\raggedright\arraybackslash}p{3.0cm}>{\raggedright\arraybackslash}p{6.6cm}>{\raggedright\arraybackslash}p{5.0cm}@{}}
\toprule
Statement & Hypotheses and content & Lean \\
\midrule
\multicolumn{3}{@{}l}{\emph{Population expansion (Part~II)}}\\
Chart expansion & smooth $\eta$ on the box, $k_i\ge1$: cutoff expansion on $Q^{-1}\N$, degree $\le d-1$, coefficients cutoff-independent & \texttt{smooth\_cutoffExpansion}, \texttt{smoothCoeff\_unique} \\
Resolved coefficients & atlas- and transport-independent; push-forward to $W$ intrinsic to $(K,\varphi)$ & \texttt{ResolvedData.coeff}, \texttt{coeff\_eq\_of\_transports}, \texttt{coeff\_comp\_gv} \\
Support & $c_{\mu,q}$ vanishes on observables vanishing near $\{r_\mu\ge q+1\}$ & \texttt{coeff\_eq\_zero\_of\_eventually\_zero\_resonant} \\
Graded stratum formula (\cref{thm:graded}) & $F$ vanishing near $D_{c+1}$: degrees $\ge c$ vanish; top coefficient as face integrals with constant $\Gamma(\mu)/((c-1)!\prod2k_j\alpha_j!)$ & \texttt{coeff\_eq\_stratumSum}, \texttt{smoothCoeff\_eq\_faceSum\_top}, \texttt{faceMonoCoeff\_top} \\
Jet dependence (\cref{thm:jet}) & kills $\Ical_S^{\,n_\mu(P)+1}$ near the stratum; descends to the jet quotient & \texttt{coeff\_eq\_of\_memIdealPow}, \texttt{descendedCoeff} \\
Stratum measure (\cref{thm:stratum_measure}) & zero-order condition: positive Radon measure on $X_c$, carried by $S^\mu_c$, unique, transport-independent, representing $c_{\mu,c-1}$ on $\Ical_{c+1}$ & \texttt{stratumMeasure}, \texttt{coeff\_withF\_eq\_integral\_stratumMeasure}, \texttt{eq\_stratumMeasure\_of\_tests} \\
Residue (\cref{thm:residue,thm:identity}) & $\Rres=\frac{(c-1)!}{\Gamma(\mu)}\nu$ equals the chart residue measure: face densities with $(2k_j)^{-1}$ per wall & \texttt{residueMeasure}, \texttt{chartResidueMeasure\_eq\_residueMeasure} \\
Leading term (\cref{thm:leading}) & extremal pair; $F$ vanishing near $D_{m+1}$: normalised limit $=\int F\,d\nu^\lambda_m$; positivity at a realiser; $\nu(X)\le c_{\lambda,m-1}(1)$, equality if $D_{m+1}=\varnothing$ & \texttt{tendsto\_normalised\_partitionObs\_extremal}, \texttt{observableCoeff\_pos\_of\_realised}, \texttt{extremalStratumMeasure\_univ\_le} \\
RLCT & $\Zcal_n[1]\sim c\,n^{-\lambda}(\log n)^{m-1}$, $c>0$ & \texttt{exists\_rlct\_asymptotic} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Fluctuation function and empirical expansion (Part~III)}}\\
Ladder, Weber & $\partial_aS_\mu=S_{\mu+1/2}$; recurrence; ODE; closed form at $\frac12$; index derivatives as log weights & \texttt{deriv\_fluctuation}, \texttt{fluctuation\_recurrence}, \texttt{fluctuation\_ode}, \texttt{mellinMom\_pow\_mul\_exp\_eq\_iteratedDeriv} \\
One-dimensional expansion & smooth $\eta,\xi$: $\sum_jC_jn^{-\mu_j}+O(n^{-L})$, $C_j=\partial^j[\eta S_{\mu_j}(\xi)](0)/(j!2k)$; explicit constant through $\xi\le M$ and jet bounds & \texttt{empOneDim\_expansion}, \texttt{empOneDim\_expansion\_of\_bounds}, \texttt{empOneDimCoeff\_one} \\
Chart expansion (\cref{thm:empirical_expansion}) & smooth $\eta,\zeta$: cutoff expansion, unique coefficients, remainder linear in a jet bound & \texttt{emp\_cutoffExpansion}, \texttt{empCoeff\_unique}, \texttt{emp\_cutoffExpansion\_uniform} \\
Resolved expansion & bounded smooth root field: expansion on the common lattice; zero field gives the population coefficients & \texttt{empZ\_cutoffExpansion}, \texttt{resolvedCoeff\_zero} \\
Graded empirical formula \eqref{eq:empirical_graded} & $\eta$ vanishing near the deep set: degrees $\ge c$ vanish; top coefficient $=$ population coefficient of $\eta S_\mu(\zeta)/\Gamma(\mu)$; branchwise stratum sum & \texttt{empCoeff\_eq\_faceSum\_top}, \texttt{empCoeff\_top\_eq\_smoothCoeff}, \texttt{resolvedCoeff\_eq\_empStratumSum} \\
Empirical leading term \eqref{eq:empirical_leading} & chart-leading transport, bounded root field, smooth $F$: normalised limit $=$ face formula with $S_\lambda(\hat\psi)$; $=\int F\,d\nu(\hat\psi)$ on $\Ical_{m+1}$ & \texttt{hasLeadingTerm\_empZ}, \texttt{hasLeadingTerm\_empZ\_eq\_integral} \\
Generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1} & one resonant coordinate, $\mu_1<$ other exponents: $c_{\lambda,0}$, $c_{\mu_1,0}$ as face integrals, all other coefficients $\le\mu_1$ vanish & \texttt{empCoeff\_generic}, \texttt{empCoeff\_firstCorrection}, \texttt{tendsto\_firstCorrection} \\
Two-dimensional tie & $x^2y^2$, constant field: $\frac{n^{-1/2}}4[S_{1/2}(a)\log n-\partial_\nu S_\nu(a)|_{1/2}]$ & \texttt{tendsto\_logExample} \\
Generating identity \eqref{eq:generating} & smooth chart field: unconditionally convergent series of population coefficients & \texttt{hasSum\_empCoeff\_population} \\
Mellin--Laurent characterisation & any cutoff expansion: coefficients are the unique polar data of the continued Mellin transform & \texttt{mellin\_eq\_mellin\_cutoffRemainderFun\_add\_principalParts}, \texttt{polarCoeff\_unique} \\
Coefficient continuity & locally Lipschitz in the face jets; convergence in law of the top coefficients under convergence in law of the jets & \texttt{exists\_resolvedCoeff\_top\_bound}, \texttt{tendstoInDistribution\_resolvedCoeff\_top} \\
Gaussian average & $E\,S_\lambda(N(0,v))=\Gamma(\lambda)(1-v/2)^{-\lambda}$ for $v<2$, infinite otherwise; Wick series under an exponential moment with $\delta>\frac14$ & \texttt{integral\_fluctuation\_gaussianReal'}, \texttt{integral\_empCoeff\_gaussian\_wick\_of\_exp\_moment} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Expectations (Part~IV)}}\\
Quotient to all orders (\cref{thm:posterior_quotient}) & two cutoff expansions, nonzero leading block: quotient blocks, remainder $O(n^{-J/Q}(1+\log n)^{D(J+1)})$; in probability at the diagonal for the grey book's data model & \texttt{cutoff\_div\_isBigO'}, \texttt{boundedInProbSeq\_posteriorMean\_allOrders} \\
Connected coefficients & $\kappa_2=\partial^2_\varepsilon\log(Z[e^{\varepsilon f}]/Z[1])|_0$ at the block level; posterior variance to all orders & \texttt{coeff\_two\_mul\_coeff\_two\_logOf\_blocks}, \texttt{emp\_variance\_isBigO} \\
Two-site balancing \eqref{eq:two_site} & exchangeable positive weights & \texttt{integral\_twoSitePosteriorMass\_sub}, \texttt{integral\_twoSitePosteriorMass\_mem} \\
Fr\'echet derivative, Stein & compact base, continuous PSD kernel, Gaussian field with second sup-norm moment & \texttt{hasFDerivAt\_compactAvg}, \texttt{GaussianField.integral\_eval\_mul\_compactAvg} \\
Interpolation \eqref{eq:interpolation} & same hypotheses & \texttt{GaussianField.integral\_compactAvg\_eq}, \texttt{compactMeanResponse\_eq\_replica}, \texttt{abs\_compactMeanResponse\_le} \\
Inverse evidence & all moments finite & \texttt{inv\_compactD\_le}, \texttt{integrable\_inv\_compactD\_rpow\_of\_isGaussian} \\
Quenched source & $|\log\langle e^{\varepsilon f}\rangle_g|\le|\varepsilon|\,\|f\|$; $\Psi'(0)$, $\Psi''(0)$ & \texttt{abs\_logTilt\_le}, \texttt{deriv\_quenchedSource}, \texttt{deriv\_deriv\_quenchedSource\_zero} \\
\bottomrule
\end{tabular}
\caption{Formal counterparts of the statements of this paper. Names are declarations of \texttt{timaeus-research/grammar} unless stated; the bridge statements about the sample live in the workspace on the grey book formalisation.}
\label{tab:lean}
\end{table}

\paragraph{What is not proved.} The list is short and specific.
\begin{itemize}
\item The finite-part form \eqref{eq:tier2} for one resonant coordinate at normal order $\alpha\ge2$ when the amplitude does not vanish at the corner and $\mu$ exceeds another wall's exponent; the formalised coefficient formula performs the Taylor subtraction but its closed evaluation is not written. Likewise the closed form of the lower logarithmic coefficients at ties for nonconstant data; the $x^2y^2$ formulas of \cref{sec:first_orders} are derivations from the Laurent characterisation, not formalised theorems.
\item The convergence in law of the normal derivatives of the empirical process on the faces, needed for the subleading coefficients; and the identification of the fixed-sample leading posterior functional with $\langle f\rangle_G$ of \cref{sec:averaging}. Both are statistical statements about the model, not about the geometry.
\item Watanabe's convergence of the zeta function on the strip $\operatorname{Re}s<\lambda$ is used as a hypothesis where the Mellin characterisation is applied to the assembled integral; it is not derived from the resolution.
\item The averaged subleading corrections of \cref{sec:averaging}.
\item A manifold-level residue calculus for densities: the residue is defined as a measure and identified with the face densities in charts; the operation on densities is not developed separately. For positive normal orders the conormal presentation is not a canonical decomposition, and only the total functional, its jet dependence and its principal part are asserted to be intrinsic.
\end{itemize}

%%%%%%%%%% FILE sections/14_conclusion.tex %%%%%%%%%%
\section{Related work and conclusion}\label{sec:conclusion}

\paragraph{Related work.} The asymptotic expansion of the population partition function and the identification of its exponents with the real log canonical threshold are the foundation of singular learning theory \citep{watanabeAlgebraicGeometryStatistical2009,watanabe2018}, and the standard form of the empirical divergence, the fluctuation function and the Gaussian limit of the empirical process are Watanabe's. The use of the strata of a normal crossing divisor to organise the asymptotics of integrals with a phase is classical in the theory of Igusa zeta functions and motivic integration \citep{igusa2000introduction,denef1998motivicigusazetafunctions,gusein2010integration}, and the analogy with the amplitude selecting the visible features of a caustic in geometric optics is in \citet{arnold2012singularities}. Products and quotients of expansions in the scale $n^{-\mu}(\log n)^q$ are treated in \citet{paris2001asymptotics}. The identification of the fluctuation function with a parabolic cylinder function is classical from the point of view of special functions \citep{NIST:DLMF}. Gaussian integration by parts, replica identities and covariance interpolation as used in \cref{sec:averaging} are the standard tools of mean field spin glasses \citep{talagrand2011meanfield,panchenko2013sk,guerra2002thermodynamic}. On the empirical side, the local learning coefficient estimator \citep{lau2023quantifying}, susceptibilities \citep{baker2025structuralinferenceinterpretingsmall,gordon2026lang3} and patterning \citep{wang2026patterning} are the measurements whose geometric meaning the paper describes; the hypothesis that structure is encoded in the singular geometry is set out in \citet{murfet2025programssingularities}.

\paragraph{Conclusion.} A posterior expectation is a ratio of two integrals of the same kind, and each has an expansion whose coefficients are distributions on the strata of the exceptional divisor paired with the observable. The strata are where the coefficients live; the observable enters through its restriction to a stratum and finitely many normal derivatives there; the data enters through the fluctuation function of the standardised empirical process evaluated on the same strata, with derivatives of the field climbing a ladder of indices. At leading order the posterior is the residue measure on the deepest stratum of lowest exponent, reweighted pointwise by the fluctuation function of the field, and a posterior expectation is the average of the observable against this random measure. The corrections follow the same pattern one stratum and one derivative at a time, and their algebra, the quotient and the connected coefficients, introduces nothing beyond the coefficients of the two integrals.

Three things are left open, and they are of different kinds. The closed forms of the coefficients past the first correction, where the residue densities need finite parts and the ties need the lower Laurent data, are computations within a theory that is complete. The convergence in law of the derivatives of the empirical process on the strata, and the identification of the leading posterior functional with the Gibbs measure of the limit field, are statistical inputs about the model that the geometry cannot supply. And the averaged subleading corrections require rates that the present limit theorems do not give. What is not open is the shape of the answer: for every observable, every sample, and every order, the coefficient is a stratum, a jet of the observable, and a fluctuation function of the data.

%%%%%%%%%% FILE sections/A_chart_proofs.tex %%%%%%%%%%
\section{Chart-level proofs}\label{app:chart_proofs}

This appendix gives the proofs behind \cref{thm:population_expansion,thm:empirical_expansion} and the generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1}, at the level of detail at which they are formalised. The population case is the empirical case at zero field, so only the latter is treated. Throughout, $\eta$ and $\zeta$ are smooth on a neighbourhood of the closed cube $[0,1]^d$, $k_i\ge1$, and
\[
Z(n)=Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du .
\]

\subsection{One variable}

Let $d=1$, so $Z(n)=\int_0^1\eta(u)u^he^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}du$. Substitute $u=\varepsilon x$ with $\varepsilon=n^{-1/2k}$, so that $nu^{2k}=x^{2k}$ and $\sqrt n\,u^k=x^k$:
\[
Z(n)=\varepsilon^{h+1}\int_0^{1/\varepsilon}\eta(\varepsilon x)\,e^{x^k\zeta(\varepsilon x)}\,x^h\,e^{-x^{2k}}\,dx .
\]
The factor $\eta(\varepsilon x)e^{x^k\zeta(\varepsilon x)}$ is a smooth function of $v=\varepsilon x$ for fixed $x$, and its $j$-th derivative in $v$ has the form $P_j(v,x^k)\,e^{x^k\zeta(v)}$ with $P_j(v,\tau)=\sum_{r\le j}p_{j,r}(v)\tau^r$ a polynomial in $\tau$ whose coefficients are built from derivatives of $\eta$ and $\zeta$ by the recursion $p_{0,0}=\eta$, $p_{j+1,r}=p_{j,r}'+\zeta'p_{j,r-1}$. Taylor's theorem in $v$ at $v=0$ to order $q$ gives
\[
\eta(\varepsilon x)e^{x^k\zeta(\varepsilon x)}=\sum_{j\le q}\frac{(\varepsilon x)^j}{j!}P_j(0,x^k)e^{x^k\zeta(0)}+R_q(\varepsilon x,x) ,
\]
with $|R_q(v,x)|\le\frac{|v|^{q+1}}{(q+1)!}\sup_{|v'|\le|v|}|P_{q+1}(v',x^k)|e^{x^k\zeta(v')}$. On $v\in[0,1]$ and $\tau\ge0$ one has $|P_j(v,\tau)|\le C_j(1+\tau)^j$ with $C_j$ a bound on the coefficient functions, and $\zeta\le M$; so the $j$-th term of the sum is integrable on $(0,\infty)$ against $x^he^{-x^{2k}}$, since $(1+x^k)^je^{Mx^k}x^he^{-x^{2k}}\le C\,e^{-x^{2k}/2}$, and the tail $\int_{1/\varepsilon}^\infty$ is $O(e^{-1/(2\varepsilon^{2k})})=O(e^{-n/2})$. The full integrals are
\[
\frac{\varepsilon^{h+1+j}}{j!}\int_0^\infty P_j(0,x^k)e^{x^k\zeta(0)}x^{h+j}e^{-x^{2k}}dx=\frac{n^{-\mu_j}}{j!\,2k}\int_0^\infty s^{\mu_j-1}e^{-s}P_j(0,\sqrt s)e^{\sqrt s\zeta(0)}ds=\frac{n^{-\mu_j}}{j!\,2k}\,\partial_v^j\big[\eta\,S_{\mu_j}(\zeta)\big](0) ,
\]
by $s=x^{2k}$ and the identity $\int s^{\mu-1}e^{-s}P_j(v,\sqrt s)e^{\sqrt s\zeta(v)}ds=\partial_v^j[\eta S_\mu(\zeta)](v)$, which is \eqref{eq:one_dim_coefficients} and follows by differentiating $\eta(v)S_\mu(\zeta(v))=\int s^{\mu-1}e^{-s}\eta(v)e^{\sqrt s\zeta(v)}ds$ under the integral $j$ times. The remainder contributes $\varepsilon^{h+1}\int_0^{1/\varepsilon}|R_q|\le\varepsilon^{h+1+q+1}\,C'$, which is $O(n^{-L})$ whenever $2kL\le q+1+h$. This proves the one-dimensional expansion with the constant
\[
K_{h,k,q,L}(M,C_\bullet)=\Big(\sum_{j\le q}\frac{2C_j\kappa_{h+2j}(M)}{j!}\Big)\,E_{k,L}+\frac{C_{q+1}}{q!}\,\kappa_{h+2q+2}(M)\int_0^\infty e^{-x^{2k}/2}dx ,
\]
where $\kappa_m(M)=m!\,e^{1+(M+1)^2/2}$ bounds $(1+y)^me^{My}e^{-y^2}$ against $e^{-y^2/2}$ and $E_{k,L}$ bounds the tail; the point is that $K$ depends on $(\eta,\zeta)$ only through $M$ and the finitely many $C_j$.

\subsection{Fubini along a resonant coordinate}

In dimension $d=n'+1$ fix the coordinate $i_0$ and write $u=(u_{i_0},w)$. On the box the monomials split, $u^h=u_{i_0}^{h_{i_0}}w^{h_L}$ and $u^{2k}=u_{i_0}^{2k_{i_0}}p(w)$ with $p=w^{2k_L}$, and $\sqrt n\,u^k=\sqrt{np(w)}\,u_{i_0}^{k_{i_0}}$ for $w$ in the open box. Hence, by Fubini,
\begin{equation}\label{eq:fubini}
Z(n)=\int_{(0,1]^{d-1}}w^{h_L}\,I\big(np(w),w\big)\,dw,\qquad I(T,w)=\int_0^1\eta(u,w)\,u^{h_{i_0}}\,e^{-Tu^{2k_{i_0}}+\sqrt T\,u^{k_{i_0}}\zeta(u,w)}\,du ,
\end{equation}
the one-dimensional integral of the slice $(\eta(\cdot,w),\zeta(\cdot,w))$ at the effective sample size $T=np(w)$. The slices are uniformly controlled: $\zeta\le M$ on the closed cube, and the coefficient functions $p_{j,r}$ of the slice are restrictions to the line $\{w=\text{const}\}$ of smooth functions on the cube, obtained by the same recursion with $\partial_{u_{i_0}}$ in place of $d/dv$, so their bounds $C_j$ can be taken uniform in $w$. The one-dimensional estimate therefore holds for every slice with the same constant.

\subsection{Dominated convergence and the generic first correction}

Let $\lambda=\mu_0$ and $\mu_1$ be the first two exponents of the coordinate $i_0$ and assume $\mu_1<(h_l+1)/2k_l$ for every $l\ne i_0$. Set $a_j(w)=\partial_u^j[\eta S_{\mu_j}(\zeta)](0,w)/(j!\,2k_{i_0})$, the one-dimensional coefficients of the slice, and
\[
B(T,w)=T^{\mu_1}\big(I(T,w)-a_0(w)T^{-\lambda}\big) .
\]
For $T\ge1$ the one-dimensional expansion with $q$ terms and cutoff $L>\mu_1$ gives $|B(T,w)-a_1(w)-\sum_{2\le j\le q}a_j(w)T^{\mu_1-\mu_j}|\le KT^{\mu_1-L}$, so $B$ is bounded on $T\ge1$ uniformly in $w$ and $B(T,w)\to a_1(w)$ as $T\to\infty$; for $T\le1$ the trivial bound $|I|\le C_0e^{\max(M,0)}$ and $T^{\mu_1-\lambda}\le1$ bound $B$ as well. The functions $a_j$ are continuous on the closed cube, since $a_j(w)=\sum_rp_{j,r}(0,w)S_{\mu_j+r/2}(\zeta(0,w))/(j!2k_{i_0})$ and $S_\nu$ is continuous. Now
\[
n^{\mu_1}\big(Z(n)-c_{\lambda,0}n^{-\lambda}\big)=\int w^{h_L}p(w)^{-\mu_1}\,B\big(np(w),w\big)\,dw,\qquad c_{\lambda,0}=\int w^{h_L}p(w)^{-\lambda}a_0(w)\,dw ,
\]
by \eqref{eq:fubini} and the identity $w^{h_L}p^{-\mu_1}B(np,w)=n^{\mu_1}w^{h_L}I(np,w)-n^{\mu_1-\lambda}w^{h_L}p^{-\lambda}a_0(w)$. The weight $w^{h_L}p(w)^{-\mu_1}=\prod_lw_l^{h_l-2k_l\mu_1}$ is integrable on the box because every exponent exceeds $-1$, which is the gap hypothesis; the integrand is dominated by a constant times this weight; and for every $w$ in the open box $np(w)\to\infty$, so the integrand converges pointwise to $w^{h_L}p^{-\mu_1}a_1(w)$. Dominated convergence gives
\[
n^{\mu_1}\big(Z(n)-c_{\lambda,0}n^{-\lambda}\big)\longrightarrow c_{\mu_1,0}=\int w^{h_L}p(w)^{-\mu_1}a_1(w)\,dw ,
\]
which is \eqref{eq:c_mu1} once $a_1$ is written out with the ladder.

\subsection{Reading off the coefficients}

A two-term asymptotic determines the coefficients of any cutoff expansion up to the second exponent. Precisely, if $Z$ has a cutoff expansion $c$ on $Q^{-1}\N$ with degree $\le D$, and $n^{\mu_1}(Z(n)-An^{-\lambda})\to B$ with $\lambda<\mu_1$ lattice points, then $c_{\lambda,0}=A$, $c_{\mu_1,0}=B$, and $c_{\mu,q}=0$ for every other lattice $\mu\le\mu_1$ and $q\le D$. The proof subtracts the two known terms, each of which has the obvious cutoff expansion, and uses the first-nonzero-term theorem: a cutoff expansion of a function that is $o(n^{-\mu_1})$ has no nonzero coefficient at any exponent $\le\mu_1$, because the first nonzero pair $(\mu,q)$ in the lexicographic order makes the function asymptotically equivalent to $c_{\mu,q}n^{-\mu}(\log n)^q$, which is not $o(n^{-\mu_1})$ when $\mu\le\mu_1$. Applied to the canonical expansion of \cref{thm:empirical_expansion}, this identifies $c_{\lambda,0}$ and $c_{\mu_1,0}$ with the face integrals and forces the vanishing of everything else at lattice exponents $\le\mu_1$: no logarithms at $\lambda$ or $\mu_1$, nothing between.

\subsection{The general chart expansion}

The general case, where several coordinates may resonate and every order is wanted, is organised by faces. For a face $J$ of the cube and a depth $p$ one Taylor-expands the field factor $\eta e^{\tau\zeta}$ in the $J$-normal directions to order $p$ and subtracts its Taylor polynomial in the complementary directions to the same order; the $J$-normal integrals of monomials are the one-dimensional integrals above, whose Laurent data at the resonant exponents are explicit, and the complementary integrals are integrals over the face of the Taylor-subtracted amplitude against $w^{h-2k\mu}$ with logarithmic weights $(\log w^{2k})^\ell$, convergent because the subtraction removes the terms that would diverge. The coefficient at $(\mu,q)$ is a finite sum over faces and Taylor orders of these face integrals, and the remainder of the truncation is estimated by the same one-dimensional bounds, with a constant linear in a bound on the normal jets of $\eta e^{\tau\zeta}$ of the depth. This is the construction that defines the coefficients in the formalisation; uniqueness of expansions then shows they agree with every other description, including the Laurent data of \cref{sec:tiers}, and the graded formula \eqref{eq:graded} is its evaluation at the top logarithmic order, where only the fully resonant faces of maximal depth survive and no Taylor subtraction is needed for admissible amplitudes.

%%%%%%%%%% FILE sections/B_fluctuation_facts.tex %%%%%%%%%%
\section{The fluctuation function and the Weber equation}\label{app:fluctuation_facts}

We collect the facts about $S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}dt$ used in the body, with proofs.

\paragraph{Ladder and recurrence.} Differentiation under the integral, justified by the bound $t^{\mu-1}\sqrt t\,e^{-t+a\sqrt t}\le t^{\mu-1/2}e^{-t/2+a^2}$, gives $\partial_aS_\mu=S_{\mu+1/2}$ and $\partial_a^2S_\mu=S_{\mu+1}$. Integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]=(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$ over $(0,\infty)$ gives $0=\mu S_\mu-S_{\mu+1}+\frac a2S_{\mu+1/2}$, the recurrence $S_{\mu+1}=\frac a2S_{\mu+1/2}+\mu S_\mu$; rewritten with the ladder it is $S_\mu''=\frac a2S_\mu'+\mu S_\mu$. At $\mu=0$ the same computation on $[\varepsilon,T]$ gives $S_1(a)=\frac a2S_{1/2}(a)+1$ in the limit.

\paragraph{Weber's equation.} Put $z=a/\sqrt2$ and $S_\mu(a)=e^{z^2/4}f(z)$. Then $S_\mu'=e^{z^2/4}\frac1{\sqrt2}(f'+\frac z2f)$, $S_\mu''=e^{z^2/4}\frac12(f''+zf'+\frac12f+\frac{z^2}4f)$, and substituting into the ODE and dividing by $\frac12e^{z^2/4}$ leaves $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $\nu=-2\mu$. Comparing the integral representation $D_{-\nu}(x)=\frac{e^{-x^2/4}}{\Gamma(\nu)}\int_0^\infty u^{\nu-1}e^{-u^2/2-xu}du$ \citep[\S12.5(i)]{NIST:DLMF} with the definition of $S_\mu$ after $u=\sqrt{2t}$ gives the closed form \eqref{eq:weber}. At $\mu=1/2$, $u=\sqrt t$ and completion of the square give $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}(1+\operatorname{erf}(a/2))$.

\paragraph{The Weyl algebra.} Let $b^\dagger=\partial_a$ and $b=2\partial_a-a$, so $[b,b^\dagger]=1$. Then $b^\dagger S_\mu=S_{\mu+1/2}$, and the recurrence at $\mu-\frac12$ gives $bS_\mu=2S_{\mu+1/2}-aS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>\frac12$, while $bS_{1/2}=2$. The number operator $b^\dagger b-(2\mu-1)$ acts on $S_{\mu+Q/2}$ by $Q$. The definition extends to $\mu\le0$ off the poles $\{0,-\frac12,-1,\dots\}$ by $S_\mu=\frac1{2\mu}bS_{\mu+1/2}$, consistently with the meromorphic continuation of \eqref{eq:weber} in $\mu$, and the ladder relations persist. The span of the $S_\mu$ along an orbit $\mu+\frac12\mathbb Z$ is a module over the Weyl algebra; the orbit of $\frac12$ contains the polynomials $\mathbb C[a]=\operatorname{span}\{b^m1\}$ as a submodule and its quotient is the Fock representation with vacuum $S_{1/2}$, while for $\mu\notin\frac12\mathbb Z$ the orbit is doubly infinite with no lowest weight.

\paragraph{Index derivatives.} For $\nu>0$ and every $\ell$, $\partial_\nu^\ell S_\nu(a)=\int_0^\infty t^{\nu-1}(\log t)^\ell e^{-t+a\sqrt t}dt$, again by differentiation under the integral, the derivative of $t^{\nu-1}$ in $\nu$ being $t^{\nu-1}\log t$ and the bound $|\log t|^\ell t^{\nu-1}e^{-t+a\sqrt t}$ integrable. Hence for a constant $c$, $\int_0^\infty t^{\nu-1}(c-\log t)^pe^{-t+a\sqrt t}dt=(c-\partial_\nu)^pS_\nu(a)$, and $\sum_p\frac{z^p}{p!}(c-\partial_\nu)^pS_\nu=e^{zc}S_{\nu-z}$ for small $z$, the translation in the index. Differentiating the ODE $\ell$ times in $\mu$ gives the inhomogeneous equation $(\partial_\mu^\ell S_\mu)''-\frac a2(\partial_\mu^\ell S_\mu)'-\mu\,\partial_\mu^\ell S_\mu=\ell\,\partial_\mu^{\ell-1}S_\mu$, a triangular system determining the index derivatives recursively.

\paragraph{The incomplete function.} For $T>0$ let $S_\mu(a;T)=\int_0^Tt^{\mu-1}e^{-t+a\sqrt t}dt$. It has the same ladder $\partial_a^qS_\mu(a;T)=S_{\mu+q/2}(a;T)$ and index derivatives, and integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]$ over $[0,T]$ gives the inhomogeneous Weber equation $S_\mu''(a;T)-\frac a2S_\mu'(a;T)-\mu S_\mu(a;T)=-T^\mu e^{-T+a\sqrt T}$. In the applications $T=nb^{2k}$, and $S_\mu(a)-S_\mu(a;T)=\int_T^\infty t^{\mu-1}e^{-t+a\sqrt t}dt\le C_\mu e^{-T/2}e^{a^2}$ is exponentially small in $n$.

\paragraph{Gaussian average.} For $a\sim N(0,v)$, $\E e^{a\sqrt t}=e^{vt/2}$, so by Tonelli $\E S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-(1-v/2)t}dt$, which is $\Gamma(\mu)(1-v/2)^{-\mu}$ for $v<2$ and $+\infty$ for $v\ge2$.

%%%%%%%%%% FILE sections/C_expansion_algebra.tex %%%%%%%%%%
\section{Multiplication and division of expansions}\label{app:expansion_algebra}

Expansions in the scale $n^{-\mu}(\log n)^q$ with exponents on a lattice $Q^{-1}\N$ and bounded logarithmic degree form an algebra, and quotients exist when the denominator's leading block is nonzero. We record the two facts in the cutoff form used throughout.

\paragraph{Blocks.} With $x=n^{-1/Q}$ and $\ell=\log n$, a cutoff expansion $F(n)=\sum_{j<JQ}B_j(\ell)x^j+O(x^{JQ}(1+\ell)^D)$, $B_j\in\R[\ell]$ of degree $\le D$, is a truncated power series in $x$ over $\R[\ell]$, and the remainder is smaller than every retained term because $x^{JQ}(1+\ell)^D=o(x^j\ell^q)$ for $j<JQ$: powers of $x$ beat powers of $\ell$.

\paragraph{Multiplication.} If $F$ and $G$ have cutoff expansions with blocks $A_j,B_j$ and degrees $D_1,D_2$, then $FG$ has the cutoff expansion with blocks $(A*B)_j=\sum_{i\le j}A_iB_{j-i}$ and degree $D_1+D_2$: the product of the two truncations is the truncation of the Cauchy product plus terms $x^{j}$ with $j\ge JQ$ whose coefficients are polynomials in $\ell$ of degree $\le D_1+D_2$, and the cross terms with a remainder are $O(x^{JQ}(1+\ell)^{D_1+D_2})$ since each truncation is $O((1+\ell)^{D_i})$.

\paragraph{Division.} Suppose $F$ and $G$ have cutoff expansions with blocks $A_j$ and $B_j$ counted from a common first exponent, and $B_0\in\R[\ell]$ is a nonzero polynomial. Define $R\in\R(\ell)[[x]]$ by $R=A/B$, that is,
\[
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) .
\]
Then for every $J\ge1$,
\[
\frac{F(n)}{G(n)}=\sum_{j<J}R_j(\ell)\,x^j+O\big(x^J(1+\ell)^{D(J+1)}\big) .
\]
The proof is the two-scale division lemma: write $G=B_0(\ell)x^{0}(1+g)$ with $g=\sum_{1\le j<J}(B_j/B_0)x^j+O(x^J(1+\ell)^D/|B_0|)$; since $B_0$ is a nonzero polynomial, $|B_0(\ell)|\ge c\,\ell^{\deg B_0}$ for large $\ell$, so $g\to0$ and $|g|\le Cx(1+\ell)^{D}$ for large $n$, and $(1+g)^{-1}=\sum_{i<J}(-g)^i+O(x^J(1+\ell)^{DJ})$. Multiplying the truncations of $F/B_0$ and $(1+g)^{-1}$ and collecting powers of $x$ gives the recursion, with the stated growth of the remainder: each division by $B_0$ costs a rational function of $\ell$ whose denominator is a power of $B_0$, and the bound $|1/B_0|\le C(1+\ell)^0$ is not available, only $|1/B_0|\le C$ for large $\ell$, which is why the blocks are kept as rational functions and the remainder exponent grows linearly in $J$. Each $R_j$ can be expanded in inverse powers of $\ell$ to any order by dividing the polynomials, at the cost of exactness in $\ell$.

\paragraph{The logarithm with a source.} For a formal series $U=1+\varepsilon U_1+\varepsilon^2U_2+\cdots$ over any commutative $\mathbb Q$-algebra, $[\varepsilon^r]\log U=\sum_{j=1}^r\frac{(-1)^{j+1}}j[\varepsilon^r](U-1)^j$, a finite formula, and $U\,\partial_\varepsilon\log U=\partial_\varepsilon U$. Applied to $U=\sum_r m_r\varepsilon^r/r!$ with $m_r\in\R(\ell)[[x]]$ the quotient-block series of $Z_n[f^r]/Z_n[1]$, this gives the recursion for the connected coefficients of \cref{sec:posterior}: $\kappa_1=m_1$ and $\kappa_{r+1}=m_{r+1}-\sum_{i<r}\binom ri\kappa_{i+1}m_{r-i}$, in particular $\kappa_2=m_2-m_1^2$ blockwise.

%%%%%%%%%% FILE sections/D_resolution_facts.tex %%%%%%%%%%
\section{Resolution facts used}\label{app:resolution_facts}

\paragraph{The resolution theorem.} We use Hironaka's theorem in the form of \citet[\S11.3, Thm~3.2.1]{igusa2000introduction}, applied to $K_{\mathbb C}$ together with the complexified boundary functions of $W$ and the complexification of an analytic positive factor of the prior where one is assumed: a proper holomorphic $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$, an isomorphism off $\{K_{\mathbb C}=0\}$, with $(K_{\mathbb C}\circ\pi)^{-1}(0)$ a normal crossing divisor along whose components $K_{\mathbb C}\circ\pi$ and the Jacobian vanish to constant orders. Since $K$ is real the centres of the blow-ups can be taken real \citep{bierstone1997canonical}, so that $U_{\mathbb C}$ carries an anti-holomorphic involution lifting conjugation, whose fixed locus is the real resolution $U$. At a real point through which exactly the components $E_1,\dots,E_p$ pass, the local coordinates can be chosen equivariant, hence real, and the normal form \eqref{eq:local_normal_form} holds with real units. Nonnegativity of $K$ forces the exponents $a_i$ to be even: an odd exponent would change the sign of $K\circ\pi$ across the wall while the unit does not vanish. Absorbing the unit into a normal coordinate uses only that it is positive and smooth, and changes the Jacobian factor by a smooth positive function without changing the $h_i$.

\paragraph{Where the analyticity of $K$ is used.} Only here. The prior, the observable, and the cutoffs of the partitions of unity are smooth, and the expansion theorems of the body are proved for smooth data on the resolution. If $K$ is merely smooth no resolution exists in general, and the theory does not apply; if $K$ is analytic but not polynomial one may replace it by a comparable polynomial without changing exponents or logarithmic degrees, though the coefficients change.

\paragraph{Change of variables.} The pull-back $\Zcal_n[f]=\int_U(f\circ\pi)e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ is the change of variables formula for $\pi$, which is not injective on $E$ but is a diffeomorphism off $E$, a set of measure zero whose image $W_0$ has measure zero; this suffices \citep[Thm~7.26]{rudin1987real}.

\paragraph{Tubular neighbourhoods on a manifold with corners.} The resolved space is a manifold with corners, the boundary of $U$ being cut out by the monomialised boundary functions of $W$. Each $E_I$ is a neat submanifold in the sense of \citet[\S4.6]{hirsch2012differential}: in normal crossing coordinates the components are coordinate hyperplanes and the boundary is cut out by monomial conditions on the same coordinates, so $E_I$ meets the boundary transversely. The tubular neighbourhood theorem then applies to $E_I$, and restricting to the open subset $S_I$ gives a tubular neighbourhood of the stratum whose fibres, by the normal crossing property, meet no component $E_j$ with $j\notin I$: the defining equation of such an $E_j$ is a unit near $S_I$.

\paragraph{The adapted partition of unity.} For $\varepsilon>0$ small there are open sets $V_I\subseteq U_\varepsilon=\{K\circ\pi<\varepsilon\}$, indexed by the nonempty $I$ with $S_I\ne\varnothing$, and smooth $\rho_I\ge0$ with $\sum_I\rho_I=1$ on $U_\varepsilon$, such that $V_I\cap E_I=S_I$, $V_I\cap E_j=\varnothing$ for $j\notin I$, the $V_I$ cover $U_\varepsilon$, each $V_I$ is saturated by the normal fibres over $S_I$, and each $\rho_I$ is constant along those fibres. Take $V_I$ to be the image of the normal fibres over $S_I$ inside the tubular neighbourhood of $E_I$, intersected with $U_\varepsilon$; the first two properties hold by construction and normal crossings, and the covering property holds for $\varepsilon$ small because $E=\bigsqcup S_I$ and $U_\varepsilon$ shrinks to $E$. For the functions, choose bump functions $\tilde f_I$ on $S_I$, pull them back along the fibre projection to get $f_I$ constant on fibres and supported in $V_I$, arrange $\sum f_I>0$ on $U_\varepsilon$ by shrinking $\varepsilon$, and normalise. Analytic partitions of unity do not exist, and this is harmless: $\rho_I$ depends only on the tangential variable, so it factors out of every normal integral and enters the coefficients only as part of the smooth amplitude on the stratum.

\paragraph{Comparability.} If $g_1\asymp g_2$ are comparable nonnegative functions monomialised by the same resolution, their vanishing orders along every component agree: near a point of a component with local equation $u$, $g_i\circ\pi=\varepsilon_iu^{N_i}\cdot(\text{other factors})$, and $c_1\le g_1/g_2\le c_2$ along a curve transverse to the wall forces $N_1=N_2$ \citep[App.~B]{murfet2025programssingularities}. Hence the exponents and multiplicities of the expansion are the same for $g_1$ and $g_2$, though the coefficients are not.

============ LEAN SIGNATURES OF THE DECLARATIONS CITED IN TABLE 1 (extracted from the repo at commit d56efc8) ============
== smooth_cutoffExpansion (Grammar/SmoothGeneral.lean)
theorem smooth_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) (smoothCoeff F h k β b) := by
== smoothCoeff_unique (Grammar/SmoothGeneral.lean)
theorem smoothCoeff_unique (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = smoothCoeff F h k β b μ j :=
== coeff_eq_of_transports (Grammar/SmoothBridgeConsumer.lean)
theorem BridgeInputs.coeff_eq_of_transports (T T' : NormalisedCoreTransport d K prior)
    (hK : Measurable K) (hprior : ContDiff ℝ ∞ prior) (hprior0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior) (hobs : ContDiff ℝ ∞ obs) (μ : ℝ) (q : ℕ) :
    (BridgeInputs.ofTransport T hK hprior hprior0 hpc hobs).decomp.coeff μ q =
      (BridgeInputs.ofTransport T' hK hprior hprior0 hpc hobs).decomp.coeff μ q :=
== coeff_comp_gv (Grammar/SmoothResolvedConsumer.lean)
theorem coeff_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y μ q =
      (Ξ.X Y).observableCoeff μ q f hf :=
== coeff_eq_zero_of_eventually_zero_resonant (Grammar/SmoothResolvedResonantSupport.lean)
theorem coeff_eq_zero_of_eventually_zero_resonant {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) : Ξ.coeff Y μ q = 0 := by
== coeff_eq_stratumSum (Grammar/SmoothResolvedStratumFormula.lean)
theorem coeff_eq_stratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (μ : ℝ) :
    Ξ.coeff Y μ (c - 1) = Ξ.stratumSum Y μ c := by
== smoothCoeff_eq_faceSum_top (Grammar/SmoothFaceSumCollapse.lean)
theorem smoothCoeff_eq_faceSum_top {A : (Fin d → ℝ) → ℝ} (hA : ContDiff ℝ ∞ A)
    (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) {c : ℕ}
    (hc : 1 ≤ c) (hdeep : JetsZeroOn A (deepSet d b c)) :
    smoothCoeff A h k β b μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (faceCoef k β b J (fun i => resOrder h k μ J i + h i) μ (c - 1) *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) b μ 0) := by
== faceMonoCoeff_top (Grammar/SmoothFaceMonoTop.lean)
theorem faceMonoCoeff_top (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b)
    {μ : ℝ} (hμ : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) :
    faceMonoCoeff k e β b μ (Fintype.card ι - 1) =
      Real.Gamma μ * β ^ (-μ) / (((Fintype.card ι - 1).factorial : ℝ) * ∏ i, 2 * (k i : ℝ)) := by
== coeff_eq_of_memIdealPow (Grammar/SmoothStratumJetDependence.lean)
theorem coeff_eq_of_memIdealPow {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0)
    (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.MemIdealPowNear (Ξ.exactStratum μ c)
      (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) :=
== descendedCoeff (Grammar/SmoothStratumJetDescent.lean)
noncomputable def descendedCoeff (μ : ℝ) (c : ℕ) (hc : 1 ≤ c) :
    (Ξ.admissible c ⧸ Ξ.jetKernelAdm μ c) →ₗ[ℝ] ℝ :=
== stratumMeasure (Grammar/MomentKernelData.lean)
noncomputable def stratumMeasure (I : Finset R.Component) : Measure (R.Stratum I) :=
== coeff_withF_eq_integral_stratumMeasure (Grammar/SmoothStratumMeasure.lean)
theorem coeff_withF_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) := by
== eq_stratumMeasure_of_tests (Grammar/SmoothStratumMeasure.lean)
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero := by
== residueMeasure (Grammar/SmoothStratumMeasure.lean)
noncomputable def residueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
== chartResidueMeasure_eq_residueMeasure (Grammar/SmoothChartResidueIdentity.lean)
theorem chartResidueMeasure_eq_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.residueMeasure Y hc hzero := by
== tendsto_normalised_partitionObs_extremal (Grammar/SmoothStratumMeasureExtremal.lean)
theorem tendsto_normalised_partitionObs_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm))) := by
== observableCoeff_pos_of_realised (Grammar/SmoothStratumMeasurePositive.lean)
theorem observableCoeff_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.X Y).observableCoeff lam (m - 1) f hf := by
== extremalStratumMeasure_univ_le (Grammar/SmoothStratumMeasureFinite.lean)
theorem extremalStratumMeasure_univ_le {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ ≤
      ENNReal.ofReal ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)) := by
== exists_rlct_asymptotic (Grammar/SmoothResolvedRLCTAsymptotic.lean)
theorem exists_rlct_asymptotic (hne : Ξ.zeroFibre.Nonempty)
    (hpos : ∀ y ∈ tsupport Ξ.prior, Ξ.K y = 0 → 0 < Ξ.prior y) :
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧
      ∃ c : ℝ, 0 < c ∧ (fun N => partitionObs Ξ.K Ξ.prior (fun _ => (1 : ℝ)) N) ~[atTop]
        fun N => c * (N ^ (-lam) * Real.log N ^ (m - 1)) := by
== deriv_fluctuation (Grammar/Fluctuation.lean)
theorem deriv_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    deriv (fun a => fluctuation β lam a) a = β * fluctuation β (lam + 1 / 2) a :=
== fluctuation_recurrence (Grammar/Fluctuation.lean)
theorem fluctuation_recurrence (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    fluctuation β (lam + 1) a
      = (a / 2) * fluctuation β (lam + 1 / 2) a + (lam / β) * fluctuation β lam a := by
== fluctuation_ode (Grammar/Fluctuation.lean)
theorem fluctuation_ode (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    β ^ 2 * fluctuation β (lam + 1) a
      = (a * β / 2) * (β * fluctuation β (lam + 1 / 2) a) + lam * β * fluctuation β lam a := by
== mellinMom_pow_mul_exp_eq_iteratedDeriv (Grammar/MellinLogWeights.lean)
theorem mellinMom_pow_mul_exp_eq_iteratedDeriv {μ a : ℝ} (hμ : 0 < μ) (r ℓ : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ ℓ =
      (-1) ^ ℓ * iteratedDeriv ℓ (fun ν => fluctuation 1 ν a) (μ + r / 2) := by
== empOneDim_expansion (Grammar/EmpiricalOneDim.lean)
theorem empOneDim_expansion (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) {b : ℝ} (hb : 0 < b) (q L : ℕ) (hqL : 2 * k * L ≤ q + 1 + h) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → 1 ≤ b * N ^ (1 / (2 * (k : ℝ))) →
      |empOneDim η ξ h k b N -
        ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h))| ≤
        C * N ^ (-(L : ℝ)) := by
== empOneDim_expansion_of_bounds (Grammar/EmpiricalOneDim.lean)
theorem empOneDim_expansion_of_bounds (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ)
    {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) (q L : ℕ) (hqL : 2 * k * L ≤ q + 1 + h) {M : ℝ}
    (hM' : ∀ t ∈ Icc 0 b, ξ t ≤ M) {Cj : ℕ → ℝ}
    (hCj : ∀ j, 0 ≤ Cj j ∧ ∀ v ∈ Icc 0 b, ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j v τ| ≤ Cj j * (1 + τ) ^ j)
    {N : ℝ} (hN : 1 ≤ N) (hX : 1 ≤ b * N ^ (1 / (2 * (k : ℝ)))) :
    |empOneDim η ξ h k b N -
        ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h))| ≤
        oneDimExpConst h k q L b M Cj * N ^ (-(L : ℝ)) := by
== empOneDimCoeff_one (Grammar/EmpiricalOneDim.lean)
theorem empOneDimCoeff_one (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    empOneDimCoeff η ξ h k 1 = (deriv η 0 * fluctuation 1 (lam k (1 + h)) (ξ 0) +
      η 0 * deriv ξ 0 * fluctuation 1 (lam k (1 + h) + 1 / 2) (ξ 0)) / (2 * k) := by
== emp_cutoffExpansion (Grammar/EmpiricalGeneral.lean)
theorem emp_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) := by
== empCoeff_unique (Grammar/EmpiricalGeneral.lean)
theorem empCoeff_unique (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = empCoeff η ζ h k μ j :=
== emp_cutoffExpansion_uniform (Grammar/EmpiricalUniform.lean)
theorem emp_cutoffExpansion_uniform (hk : ∀ i, 0 < k i) (L' M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ (depthOf h k (max ⌈L'⌉₊ (L₀ h))) 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1) (empCoeff η ζ h k) L' N| ≤
          C * K₀ * (N ^ (-L') * (1 + log N) ^ (d - 1)) := by
== empZ_cutoffExpansion (Grammar/EmpiricalResolvedExpansion.lean)
theorem empZ_cutoffExpansion {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD (Ξ.empZ Y ξ.toRootField)
      ξ.resolvedCoeff := by
== resolvedCoeff_zero (Grammar/EmpiricalResolvedExpansion.lean)
theorem resolvedCoeff_zero {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / (Ξ.decomp Y).commonQ) {j : ℕ}
    (hj : j ≤ (Ξ.decomp Y).commonD) : (zero Ξ Y).resolvedCoeff μ j = Ξ.coeff Y μ j := by
== empCoeff_eq_faceSum_top (Grammar/EmpiricalFaceSumCollapse.lean)
theorem empCoeff_eq_faceSum_top (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (resonantTop k J (fun i => resOrder h k μ J i + h i) μ *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J)
                (fun v => η v * fluctuation 1 μ (ζ v)) (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) 1 μ 0) := by
== empCoeff_top_eq_smoothCoeff (Grammar/EmpiricalFaceSumCollapse.lean)
theorem empCoeff_top_eq_smoothCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) h k 1 1 μ (c - 1) := by
== resolvedCoeff_eq_empStratumSum (Grammar/EmpiricalResolvedStratumFormula.lean)
theorem resolvedCoeff_eq_empStratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    ξ.resolvedCoeff μ (c - 1) = ξ.empStratumSum μ c := by
== hasLeadingTerm_empZ (Grammar/EmpiricalResolvedLeading.lean)
theorem hasLeadingTerm_empZ (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      (∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν) lam (m - 1) := by
== hasLeadingTerm_empZ_eq_integral (Grammar/EmpiricalResolvedLeading.lean)
theorem hasLeadingTerm_empZ_eq_integral (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam) {m : ℕ}
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M)
    (hFt : Ξ.IsTest m Ξ.F) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m)) lam
      (m - 1) := by
== empCoeff_generic (Grammar/FirstCorrection.lean)
theorem empCoeff_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ₁ : μ ≤ lam (k i₀) (1 + h i₀)) {q : ℕ}
    (hq : q ≤ n) :
    empCoeff η ζ h k μ q =
      (if μ = ratioExp h k i₀ ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 0 else 0) +
      (if μ = lam (k i₀) (1 + h i₀) ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 1 else 0) := by
== empCoeff_firstCorrection (Grammar/FirstCorrection.lean)
theorem empCoeff_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    empCoeff η ζ h k (ratioExp h k i₀ + 1 / (2 * (k i₀ : ℝ))) 0 =
      genericFaceCoeff η ζ h k i₀ 1 := by
== tendsto_firstCorrection (Grammar/FirstCorrection.lean)
theorem tendsto_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    Tendsto (fun N : ℝ => N ^ lam (k i₀) (1 + h i₀) *
        (empIntegral η ζ h k N - genericFaceCoeff η ζ h k i₀ 0 * N ^ (-lam (k i₀) (h i₀))))
      atTop (𝓝 (genericFaceCoeff η ζ h k i₀ 1)) := by
== tendsto_logExample (Grammar/LogExampleTwoDim.lean)
theorem tendsto_logExample (a : ℝ) :
    Tendsto (fun n : ℝ => 4 * Real.sqrt n * logExample a n -
      (Real.log n * fluctuation 1 (1 / 2) a - deriv (fun ν => fluctuation 1 ν a) (1 / 2)))
      atTop (𝓝 0) := by
== hasSum_empCoeff_population (Grammar/EmpiricalGeneratingIdentity.lean)
theorem hasSum_empCoeff_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q)
      (empCoeff η ζ h k μ q) := by
== mellin_eq_mellin_cutoffRemainderFun_add_principalParts (Grammar/MellinRegularization.lean)
theorem mellin_eq_mellin_cutoffRemainderFun_add_principalParts (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U a : ℝ} (haU : a ≤ U)
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → a ≤ μ) {s : ℂ}
    (hs0 : 0 < s.re) (hsa : s.re < a) :
    mellin (fun N => (E N : ℂ)) s =
      mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s := by
== polarCoeff_unique (Grammar/PrincipalPartUniqueness.lean)
theorem polarCoeff_unique (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) {a : ℕ → ℂ}
    (ha : (fun s => mellinContinuation Q D E c U s - polarPart D a (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = polarCoeff c μ₀ q := by
== exists_resolvedCoeff_top_bound (Grammar/EmpiricalResolvedContinuity.lean)
theorem exists_resolvedCoeff_top_bound {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ ξ₁ ξ₂ : Ξ.SmoothRootField Y,
      (∀ p, JetBoundOn (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₂.Lψ p) B) →
      ∀ ε, 0 ≤ ε → ε ≤ 1 →
      (∀ p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₁.Lψ p) (ξ₂.Lψ p) ε) →
      |ξ₁.resolvedCoeff μ (c - 1) - ξ₂.resolvedCoeff μ (c - 1)| ≤ K * ε := by
== tendstoInDistribution_resolvedCoeff_top (Grammar/EmpiricalCoeffDistribution.lean)
theorem tendstoInDistribution_resolvedCoeff_top {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : ℕ → Ω → Ξ.SmoothRootField Y) {G : Ω' → Ξ.RealizableJets Y μ}
    (hLG : TendstoInDistribution (fun n w => Ξ.realizableJet Y μ (ξ n w)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution (fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1)) atTop
      (fun w' => Ξ.coeffOnJets Y μ c (G w')) (fun _ => P) P' := by
== integral_empCoeff_gaussian_wick_of_exp_moment (Grammar/WickEnvelope.lean)
theorem integral_empCoeff_gaussian_wick_of_exp_moment [IsProbabilityMeasure P]
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {ζ : Ω → (Fin d → ℝ) → ℝ}
    (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hb : closedBox d 1 ⊆ U) (hG : IsGaussianProcess (fun (x : U) o => ζ o x) P)
    {W : (Fin d → ℝ) → ℝ} (hW : ContDiff ℝ ∞ W) (hW0 : ∀ x, 0 ≤ W x)
    (hlaw : ∀ x ∈ closedBox d 1,
      HasLaw (fun o => mono k x * ζ o x) (gaussianReal 0 ⟨W x, hW0 x⟩) P)
    (hJ : ∀ R : ℕ, AEMeasurable
      (fun o => cubeJet R 1 (fun v => mono k v * ζ o v) ((contDiff_mono k).mul (hζ o))) P)
    (hmeas : ∀ r R : ℕ, AEStronglyMeasurable
      (fun o => cubeJet R 1 (fun v => η v * (mono k v * ζ o v) ^ r)
        (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) P)
    {R₀ : ℕ} (hR₀ : ∑ i, depthOf h k (cutoffOf h (μ + 1 / 2)) i ≤ R₀) {δ : ℝ} (hδ : 1 / 4 < δ)
    (hexp : Integrable (fun o => Real.exp (δ * ‖cubeJet R₀ 1 (ζ o) (hζ o)‖ ^ 2)) P) :
    Integrable (fun o => empCoeff η (ζ o) h k μ q) P ∧
    ∫ o, empCoeff η (ζ o) h k μ q ∂P = ∑' j : ℕ, (1 / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q :=
== coeff_two_mul_coeff_two_logOf_blocks (Grammar/SourceLog.lean)
theorem coeff_two_mul_coeff_two_logOf_blocks (hb : b 0 ≠ 0) (hZ0 : constantCoeff Z = mk b)
    (hZ1 : coeff 1 Z = mk a) (hZ2 : 2 * coeff 2 Z = mk c) (j : ℕ) :
    coeff j (2 * coeff 2 (logOf (C (mk b)⁻¹ * Z))) = varianceBlocks a b c j := by
== emp_variance_isBigO (Grammar/PosteriorVarianceExpansion.lean)
theorem emp_variance_isBigO (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hf : ContDiff ℝ ∞ f)
    (hk : ∀ i, 0 < k i) {lam : ℝ} {m m₀ : ℕ} (hBL : BoxLeading h k lam m)
    (hm₀ : (m₀ : ℝ) / Qamb k ≤ lam) {J : ℕ} (hJ : 1 ≤ J)
    (hne : ∃ q ∈ range (d - 1 + 1), empCoeff η ζ h k ((m₀ : ℝ) / Qamb k) q ≠ 0) :
    (fun N : ℝ => empIntegral (fun v => η v * f v ^ 2) ζ h k N / empIntegral η ζ h k N -
        (empIntegral (fun v => η v * f v) ζ h k N / empIntegral η ζ h k N) ^ 2 -
        ∑ j ∈ range J, varianceBlocks
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff (fun v => η v * f v) ζ h k) m₀ i
            (Real.log N))
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff η ζ h k) m₀ i (Real.log N))
          (fun i => blockPoly (Qamb k) (d - 1) (empCoeff (fun v => η v * f v ^ 2) ζ h k) m₀ i
            (Real.log N)) j * (N ^ (-(1 / (Qamb k : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ =>
        (N ^ (-(1 / (Qamb k : ℝ)))) ^ J * ((1 + Real.log N) ^ (d - 1)) ^ (2 * J + 2) :=
== integral_twoSitePosteriorMass_sub (Grammar/TwoSiteExchange.lean)
theorem integral_twoSitePosteriorMass_sub :
    (∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ) - p =
      p * (1 - p) * (1 - 2 * p) / 2 * ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ := by
== integral_twoSitePosteriorMass_mem (Grammar/TwoSiteExchange.lean)
theorem integral_twoSitePosteriorMass_mem :
    min p (1 / 2) ≤ ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ∧
      ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ≤ max p (1 / 2) := by
== hasFDerivAt_compactAvg (Grammar/PosteriorFrechet.lean)
theorem hasFDerivAt_compactAvg (f g : C(K, ℝ)) :
    HasFDerivAt (fun g : C(K, ℝ) => compactAvg β lam ρ g f) (posteriorDeriv ρ hβ hlam f g) g := by
== integral_eval_mul_compactAvg (Grammar/CompactBaseStein.lean)
theorem integral_eval_mul_compactAvg (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P =
      β * ∫ ω, (compactSqrtTimeMoment β lam ρ (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam ρ (Γ.G ω) f *
          compactSqrtTimeMoment β lam ρ (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P := by
== integral_compactAvg_eq (Grammar/CompactBaseResponse.lean)
theorem integral_compactAvg_eq (f : C(K, ℝ)) :
    ∫ ω, compactAvg β lam ρ (Γ.G ω) f ∂P =
      (∫ x, f x ∂ρ) / ρ.real univ + ∫ s in (0 : ℝ)..1,
        ∫ ω, compactMeanResponse β lam ρ 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := by
== compactMeanResponse_eq_replica (Grammar/GibbsJointResponse.lean)
theorem compactMeanResponse_eq_replica :
    compactMeanResponse β lam ρ 𝒞 f g = β ^ 2 / 2 *
      ∫ z, (f z.2.1.1 - f z.1.1) * (z.2.1.2 * 𝒞.C z.2.1.1 z.2.1.1 -
        2 * (Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2 * 𝒞.C z.2.1.1 z.2.2.1))
        ∂(gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := by
== abs_compactMeanResponse_le (Grammar/CompactBaseResponse.lean)
theorem abs_compactMeanResponse_le (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, 𝒞.C x x ≤ c) (f : C(K, ℝ)) (g : C(K, ℝ)) :
    |compactMeanResponse β lam ρ 𝒞 f g| ≤
      5 * β ^ 2 * ‖f‖ * c * (2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2) := by
== inv_compactD_le (Grammar/InverseEvidence.lean)
theorem inv_compactD_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ‖g‖ ≤ R) :
    (compactD β lam ρ g)⁻¹ ≤ lam * Real.exp (2 * β) / ρ.real univ * (1 + R) ^ (2 * lam) := by
== integrable_inv_compactD_rpow_of_isGaussian (Grammar/InverseEvidence.lean)
theorem integrable_inv_compactD_rpow_of_isGaussian (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    {G : Ω → C(K, ℝ)} (hG : Measurable G) [IsGaussian (P.map G)] {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun ω => (compactD β lam ρ (G ω))⁻¹ ^ s) P :=
== abs_logTilt_le (Grammar/QuenchedSource.lean)
theorem abs_logTilt_le (hρ : ρ ≠ 0) (ε : ℝ) : |logTilt β lam ρ g f ε| ≤ |ε| * M := by
== deriv_quenchedSource (Grammar/QuenchedSource.lean)
theorem deriv_quenchedSource (hρ : ρ ≠ 0) :
    deriv (quenchedSource β lam ρ P G f) = fun ε => ∫ ω, compactAvgTilt β lam ρ (G ω) f ε ∂P :=
== deriv_deriv_quenchedSource_zero (Grammar/QuenchedSource.lean)
theorem deriv_deriv_quenchedSource_zero (hρ : ρ ≠ 0) :
    deriv (deriv (quenchedSource β lam ρ P G f)) 0 = ∫ ω, compactVar β lam ρ (G ω) f ∂P := by
== integral_fluctuation_gaussianReal' (Grammar/GaussianFluctuationScalar.lean)
105:theorem integral_fluctuation_gaussianReal' (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (v : ℝ≥0)
106-    (hδ : 0 < 1 - β * (v : ℝ) / 2) :
107-    Integrable (fluctuation β μ) (gaussianReal 0 v) ∧
108-    ∫ x, fluctuation β μ x ∂gaussianReal 0 v =
109-      Real.Gamma μ * (β * (1 - β * (v : ℝ) / 2)) ^ (-μ) := by
110-  have h := integral_mul_fluctuation_eq_of_measure (gaussianReal 0 v) β μ (fun x => x)
111-    measurable_id (fun _ => 1) measurable_const
112-    (fun θ => θ ^ 0 * Real.exp (θ ^ 2 * (v : ℝ) / 2))
113-    (fun θ => by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := v) θ)
== cutoff_div_isBigO' (Grammar/CutoffQuotientExpansion.lean)
238:theorem cutoff_div_isBigO' (hQ : 0 < Q) {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
239-    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂) {m₀ : ℕ}
240-    (hv₁ : VanishBelow Q c₁ m₀) (hv₂ : VanishBelow Q c₂ m₀) {J : ℕ} (hJ : 1 ≤ J)
241-    (hne : ∃ q ∈ range (D + 1), c₂ ((m₀ : ℝ) / Q) q ≠ 0) :
242-    (fun N : ℝ => Z₁ N / Z₂ N - ∑ j ∈ range J,
243-        quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
244-          (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) j * (N ^ (-(1 / (Q : ℝ)))) ^ j)
245-      =O[atTop] fun N : ℝ => (N ^ (-(1 / (Q : ℝ)))) ^ J * ((1 + Real.log N) ^ D) ^ (J + 1) := by
246-  have hne' : ∃ q ∈ range (D + 1), c₂ (((m₀ + 0 : ℕ) : ℝ) / Q) q ≠ 0 := by
