Design consult #167 for timaeus-research/grammar (Lean 4 / Mathlib, namespace Grammar, commit d56efc8). Your perspective review of the paper (reproduced below as (2)) recommended reorganising it around the meromorphic distribution T(s) = K^{-s} φ dw, the all-log coefficient formula (*), a global leading measure, and a branch space. The user has accepted this and asked to start: do the mathematics, formalise what needs to be formalised, then rewrite. Below: (1) the current paper (corrected today per your correctness review), (2) your perspective review, (3) my draft plan, (4) the Lean definitional closure of the paper's pinned declarations (section variables per module, proofs elided) so you can see what exists.

Please return, concretely and in this order:
A. The precise mathematical statements to prove, at chart level first ((0,1]^d, monomial phase u^{2k}, weight u^h, smooth amplitude G, smooth root field ζ, unit temperature), then resolved: (A1) meromorphic continuation of the chart zeta functional s ↦ ∫ G(u) u^{h−2ks} du with pole order bound and Laurent functionals A_{μ,r}; (A2) the holomorphic-amplitude-family lemma and the proof of (*) for the empirical chart integral, with the exact sign conventions ((μ−s)^r vs (s−μ)^r, the (−1) factors, the 1/q!) made consistent with the library's `polarCoeff`/`polarPart` conventions (Grammar/PrincipalPartUniqueness.lean: polarPart D a μ s = Σ_q a q / (s−μ)^{q+1}, polarCoeff c μ q = (−1)^q q! c μ q, if I recall; please state (*) in those terms); (A3) identification of A_{μ,M} with the library's residueMeasure/stratumMeasure and of A_{μ,1} at a simple pole with the finite-part face functional; (A4) the global leading measure at the extremal pair (integrability across nonminimal walls, assembly, leading limit for all smooth F). Give proofs or proof sketches at the level a formaliser needs, and flag any step that is not standard.
B. The formalisation route: an ordered list of units (each one Lean file, ≤ ~600 lines) with, for each, the statement (in Lean-like notation using the library's existing names where they apply: empIntegral, empCoeff, smoothCoeff, CutoffExpansion, polarCoeff, mellinContinuation, principalParts, fluctuation, mellinMom, faceCoeffInt, ResolvedData, ResolvedCoreTransport, stratumMeasure, residueMeasure, extremalStratumMeasure, tendsto_normalised_partitionObs_extremal, deepZeroFibre, exactStratum), the inputs it reuses, the new definitions it needs, the main proof steps, and a size estimate. Say which existing declarations should be generalised in place and which need new files. Identify the first unit precisely enough that I can start it now.
C. The mathematics that is NOT yet standard or is at risk (e.g. the two-variable (s,u) continuation; the sign/orthant bookkeeping on the branch space; the resolved assembly of distributions with orthantwise representatives; the compact branch space), with your recommendation of what to prove first to de-risk.
D. Any corrections to the draft plan (3) and to the paper as corrected today, if you see remaining errors.
Be concrete; do not repeat the review; cite Lean names exactly.

================ (1) THE PAPER (current)

%%%%%%%% sections/01_introduction.tex
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

As $n\to\infty$ the renormalised partition function with insertion has, for each sample, an asymptotic expansion
\begin{equation}\label{eq:intro_answer}
Z_n[f]\;\sim\;\sum_{\mu}\sum_{q}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q ,
\end{equation}
in which the candidate exponents $\mu$ and the powers of the logarithm are read off a resolution of the singularities of $K$ and do not depend on the sample, while each coefficient $c_{\mu,q}$ is a \emph{distribution supported on the strata of the exceptional divisor whose walls resonate with $\mu$}, paired with $f$; on observables that vanish near the deeper crossings it is represented by finitely many normal derivatives integrated over one stratum. Three actors appear in this formula, and the paper is organised around them.

\begin{itemize}
\item \textbf{The geometry.} Resolution of singularities replaces $W_0$ by a normal crossing divisor $E=E_1\cup\cdots\cup E_r$ on a manifold $U$ mapping onto $W$. Its components intersect along a stratification, and to each component are attached two integers: the order $2k_i$ to which $K$ vanishes along it and the order $h_i$ to which the prior measure does. The ratios $(h_i+1)/2k_i$ are the exponents; the strata along which several components meet with a common ratio are where the logarithms come from. Every coefficient in \eqref{eq:intro_answer} is a distribution supported on these strata; restricted to observables vanishing near the deeper crossings it is a measure, or a measure paired with finitely many normal derivatives, on one of them. This is the \emph{stratum measure} of the pair $(K,\varphi)$ at a given exponent and depth, and it is a coordinate-free object: the weighted logarithmic residue of the resolved integrand along the stratum.
\item \textbf{The observable.} The coefficients are linear in $f$. The leading coefficient pairs the stratum measure with the restriction of $f$ to the stratum; the corrections pair it with finitely many normal derivatives of $f$ along the stratum, of which the leading one is canonically a section of a symmetric power of the conormal bundle. An observable that vanishes along a stratum does not see it at the leading order and is instead seen at a shifted exponent, which is the mechanism by which different observables probe different parts of the singular locus.
\item \textbf{The data.} Replacing the population divergence $K$ by the empirical loss $L_n$ introduces a random field on the resolution, the standardised empirical process, and the whole effect of the sample on the expansion is that the Gamma function in the stratum measures is replaced by a \emph{fluctuation function} $S_\mu$ evaluated on that field along the stratum, with its derivatives entering the corrections in a rigid ladder. For a fixed sample the expansion is deterministic and the coefficients are functionals of finitely many jets of the field on the strata; as the sample grows the field converges to a Gaussian process and the coefficients converge with it.
\end{itemize}

Posterior expectations are quotients of two such expansions, for $f$ and for $1$, and therefore rational functions of the same coefficients. At leading order the posterior concentrates on the deepest strata of lowest exponent, weighted by the stratum measures and, in the empirical case, reweighted by the fluctuation function evaluated on the data. When several strata tie, the sample decides how the posterior mass is distributed between them.

None of this requires analyticity of the observable or of the prior, and the paper is written for smooth data throughout. The expansion, its coefficients, and the convergence of the top coefficients on admissible observables to their Gaussian limit, given that of the field's jets, have been formalised in the Lean theorem prover; a table of what is a theorem, with hypotheses, is given in \cref{sec:formalisation}, together with what is not.

\paragraph{Plan.} \cref{sec:setting} fixes the setting, the notion of asymptotic expansion in the scale $n^{-\mu}(\log n)^q$, and the running examples. \cref{sec:resolution,sec:stratification} introduce the resolution and the stratification of its exceptional divisor at a gentle pace. Part~II develops the population expansion: the normal geometry of a stratum and what in it is intrinsic (\cref{sec:normal_geometry}), and the stratum measures with the zeta function that organises all orders (\cref{sec:population}). Part~III introduces the data: the fluctuation function (\cref{sec:fluctuation}), the expansion for a fixed sample (\cref{sec:empirical}), and the Gaussian limit (\cref{sec:limit}). Part~IV treats expectations: the posterior quotient (\cref{sec:posterior}), averaging over the sample (\cref{sec:averaging}), and the formalisation (\cref{sec:formalisation}).

\paragraph{Notation.} $W\subseteq\R^d$ is the parameter space, $K$ the divergence, $L_n$ the empirical loss, $\varphi$ the prior density, $f$ an observable. $\Zcal_n[f]=\int f\,e^{-nK}\varphi\,dw$ is the population partition function with insertion and $Z_n[f]=\int f\,e^{-nL_n}\varphi\,dw$ the empirical one; $\pi\colon U\to W$ is the resolution, $E_i$ the components of the exceptional divisor with data $(k_i,h_i)$, $S_I=\bigcap_{i\in I}E_i\setminus\bigcup_{j\notin I}E_j$ the strata, $\lambda_I=\min_{i\in I}(h_i+1)/2k_i$ the exponent of a stratum and $m_I$ its multiplicity. Near a stratum $(v,u)$ are tangential and normal coordinates. $S_\mu$ is the fluctuation function and $\zeta$ the field on the resolution.

%%%%%%%% sections/02_setting.tex
\section{Setting and the running examples}\label{sec:setting}

\subsection{Partition functions with insertion}

The parameter space $W\subseteq\R^d$ is compact with nonempty interior, cut out by finitely many real analytic inequalities and equal to the closure of its interior (a zero of $K$ lying only in a lower-dimensional piece of $W$ would contribute nothing to the integrals). The model $p(x\mid w)$ and the truth $q(x)$ are probability densities with a common support, and the truth is realisable: $W_0=\{w\in W: K(w)=0\}$ is nonempty. We assume $K$ is real analytic on a neighbourhood of $W$ and nonnegative there, as a divergence is, not identically zero on any connected component of the interior of $W$, with $W_0$ meeting the support of the prior; and that the prior $\varphi\ge0$ is smooth with compact support and positive on a neighbourhood of $W_0$. Exponents are always minimised over the walls that meet the support of the prior. The observables $f$ are smooth functions on a neighbourhood of $W$. Nothing in the paper requires $\varphi$ or $f$ to be analytic, and \cref{sec:resolution} explains why $K$ is the one function for which analyticity is used.

The population partition function with insertion and the corresponding expectation are
\[
\Zcal_n[f]=\int_W f(w)\,e^{-nK(w)}\varphi(w)\,dw,\qquad \E_\infty[f]=\frac{\Zcal_n[f]}{\Zcal_n[1]} .
\]
Given a sample $\Dn=\{x_1,\dots,x_n\}$ from $q$, the empirical loss $L_n(w)=-\frac1n\sum_i\log p(x_i\mid w)$ defines the empirical partition function with insertion and the Bayesian posterior expectation
\[
Z_n[f]=\int_W f(w)\,e^{-nL_n(w)}\varphi(w)\,dw,\qquad \E[f\mid\Dn]=\frac{Z_n[f]}{Z_n[1]} .
\]
The empirical divergence $K_n(w)=\frac1n\sum_i\log\frac{q(x_i)}{p(x_i\mid w)}$ satisfies $K_n=L_n+\frac1n\sum_i\log q(x_i)$ exactly, so replacing $L_n$ by $K_n$ multiplies numerator and denominator by the same sample-dependent constant; from now on $Z_n[f]=\int f\,e^{-nK_n}\varphi\,dw$ denotes this renormalised partition function. An inverse temperature $\beta$ in front of $nL_n$ changes nothing structurally and is absorbed into $n$ and into the field introduced below; we keep $\beta=1$.

\subsection{The standard form of the empirical divergence}

The difference between $K_n$ and $K$ is a fluctuation of order $n^{-1/2}$, but not uniformly: near $W_0$ the difference is itself small because the terms being summed are. Watanabe's standard form makes this precise. Define the empirical process
\[
\psi_n(w)=\frac1{\sqrt n}\sum_{i=1}^n\frac{K(w)-\log\big(q(x_i)/p(x_i\mid w)\big)}{\sqrt{K(w)}},\qquad w\notin W_0 ,
\]
so that, identically in $w\notin W_0$,
\begin{equation}\label{eq:standard_form}
K_n(w)=K(w)-\frac1{\sqrt n}\sqrt{K(w)}\,\psi_n(w) .
\end{equation}
The process $\psi_n$ has mean zero and is not defined on $W_0$ as written. Watanabe's standard-form theorem \citep[Main Theorem~6.1]{greybook} supplies, on each chart of the resolution of $K$ where $K\circ\pi=u^{2k}$, a smooth \emph{signed-root} representative $\xi_n$ with $K_n\circ\pi=u^{2k}-n^{-1/2}u^k\xi_n$; the field obtained by dividing by $\sqrt{K\circ\pi}=|u^k|$ is then smooth on each orthant of the normal coordinates and may jump in sign across an interior wall, which is why \cref{sec:empirical} works with orthantwise representatives. The representatives converge in law to a Gaussian process as $n\to\infty$. For the empirical results we assume in addition the statistical hypotheses of that theorem: the log-likelihood ratio $\log(q(x)/p(x\mid w))$ is analytic in $w$ with a holomorphic extension on a complex neighbourhood of $W$ whose $L^s(q)$ norms are controlled, and the relative finite variance condition; the population results of Part~II need only the geometric hypotheses above. Convergence of the normal derivatives of the field is a separate hypothesis, discussed in \cref{sec:limit}. Everything the sample does to the expansions of this paper is done through the exponent
\[
-nK_n=-nK+\sqrt n\,\sqrt K\,\psi_n ,
\]
and on the resolution, where $\sqrt{K\circ\pi}$ is a monomial, this is the exponent $-nu^{2k}+\sqrt n\,u^k\,\zeta(u)$ of a one-parameter family of integrals that we will analyse in complete generality. The field $\zeta$ is the sample; the rest is geometry.

\subsection{Asymptotic expansions in the scale \texorpdfstring{$n^{-\mu}(\log n)^q$}{n^-mu (log n)^q}}\label{sec:scale}

We follow \citet[Ch.~1]{paris2001asymptotics}. The functions $n^{-\mu}(\log n)^q$ with $\mu\in\mathbb Q_{>0}$ and $q\in\N$ are totally ordered by eventual domination: $n^{-\mu}(\log n)^q$ dominates $n^{-\mu'}(\log n)^{q'}$ when $\mu<\mu'$, or $\mu=\mu'$ and $q>q'$. We write $(\mu,q)\prec(\mu',q')$ in that case. For a locally finite set $\mathcal A\subseteq\mathbb Q_{>0}$ and $D\in\N$,
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

The divergence is analytic but rarely polynomial. Two nonnegative functions $g_1,g_2$ on an open set are \emph{comparable}, $g_1\asymp g_2$, if $c_1g_2\le g_1\le c_2g_2$ for positive constants. Comparable functions have the same vanishing orders along every component of a common resolution \citep[App.~B]{murfet2025programssingularities}, hence the same candidate exponents and logarithmic degrees and the same leading pair $(\lambda,m)$ for positive amplitudes, and in examples one replaces $K$ by a comparable polynomial when one exists; it need not, since $(y-e^x)^2$ has none. The coefficients change under such a replacement, and a subleading candidate term that is present for one phase may be absent for a comparable one.

\subsection{The running examples}\label{sec:examples}

Two examples accompany the whole paper. Both have a divergence that is already a monomial, so that the resolution is the identity and the geometry can be seen without any machinery; \cref{sec:resolution} adds an example where a blow-up is genuinely needed.

\begin{example}[Two planes meeting along a line]\label{ex:planes}
Let $W=[-1,1]^3$ with coordinates $(x,y,z)$ and $K(x,y,z)=x^2y^2$, with a smooth positive prior $\varphi$. The zero locus is the union of the two planes $\{x=0\}$ and $\{y=0\}$, meeting along the $z$-axis. Along each plane $K$ vanishes to order $2$ and the prior measure to order $0$, so each carries the ratio $1/2$; along the axis both planes meet with the same ratio. We will see that $\Zcal_n[1]\sim C\,n^{-1/2}\log n$, that the logarithm is the signature of the axis, and that the leading coefficient is an integral of the prior along the axis: the posterior concentrates on the line $\{x=y=0\}$. An observable $f(x,y,z)$ is seen at leading order only through its restriction to the axis, $f(0,0,z)$; an observable vanishing on the axis, such as $f=x^2$, loses the logarithm without changing the exponent, and is seen on the plane $\{y=0\}$, where it does not vanish, through its restriction to that plane.
\end{example}

\begin{example}[Mixed exponents]\label{ex:mixed}
Let $W=[0,1]^2$, a model whose two parameters are constrained to be nonnegative, with $K(x,y)=x^2y^6$. The two lines $\{x=0\}$ and $\{y=0\}$ are now walls of the parameter space and carry the ratios $1/2$ and $1/6$. The line $\{y=0\}$ leads, alone, so $\Zcal_n[1]\sim C\,n^{-1/6}$ with no logarithm. The first candidate correction sits at $n^{-1/3}$, carried by $\{y=0\}$ alone through the first normal derivative of the amplitude; the next candidate exponent is $n^{-1/2}$, where the line $\{x=0\}$ first resonates and a logarithm is allowed, present when the second $y$-derivative of the amplitude at the origin is nonzero. Whether a candidate term is present depends on the amplitude: for a constant amplitude one has exactly $\Zcal_n[1]=\frac{\Gamma(1/6)}4n^{-1/6}-\frac{\Gamma(1/2)}4n^{-1/2}+O(e^{-\varepsilon n})$, with neither an $n^{-1/3}$ term nor a logarithm. This example exhibits the three tiers of \cref{sec:population} in sequence. The nonnegativity constraint matters: on a symmetric domain such as $[-1,1]^2$ the odd normal moments of the population integral cancel between the two sides of a wall and the $n^{-1/3}$ candidate vanishes for every amplitude (\cref{rem:parity}).
\end{example}

In both examples the strata are the axis and the two planes, or the two lines and the origin; the observable enters through its restriction to them and its normal derivatives; and once the sample is introduced, the field enters through the fluctuation function on the leading stratum.

%%%%%%%% sections/03_resolution.tex
\section{Resolution and the exceptional divisor}\label{sec:resolution}

The integrals $\Zcal_n[f]$ concentrate, as $n\to\infty$, on the zero locus $W_0$ of $K$, and their asymptotics are governed by how $K$ vanishes there. In general $W_0$ is a singular set and $K$ vanishes along it in an intricate way. Resolution of singularities is the device that replaces this situation by a standard one: after a proper change of variables $\pi\colon U\to W$, the function $K\circ\pi$ vanishes along a union of smooth hypersurfaces meeting transversally, and near every point it is a monomial in suitable coordinates. This section states the resolution theorem in the form we use and explains what the local picture looks like.

\subsection{The theorem}

We work with the complexification: $K$ is the restriction to $W$ of a holomorphic function $K_{\mathbb C}$ on an open set $W^{(\mathbb C)}\subseteq\mathbb C^d$ containing $W$ \citep[Fundamental Condition~I]{watanabe2018}. By Hironaka's theorem \citep{hironaka1964resolution1,bierstone1997canonical}, in the form given by \citet[\S11.3]{igusa2000introduction}, there exist a $d$-dimensional complex manifold $U_{\mathbb C}$, a proper holomorphic map $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$ which is an isomorphism over the complement of $\{K_{\mathbb C}=0\}$ (when the boundary functions of $W$ are resolved simultaneously, as in \cref{app:resolution_facts}, the exceptional locus also contains the singular locus of the boundary, and the Jacobian orders $h_i$ below include the effect of rectilinearising the domain), and a finite set of smooth closed hypersurfaces $E_1,\dots,E_r$ of $U_{\mathbb C}$ with normal crossings, such that
\[
(K_{\mathbb C}\circ\pi)^{-1}(0)=E_1\cup\cdots\cup E_r
\]
and, at every point of this set through which exactly the components $E_1,\dots,E_p$ pass, there are local coordinates $(u_1,\dots,u_d)$ in which $E_i=\{u_i=0\}$ and
\begin{equation}\label{eq:local_normal_form}
K_{\mathbb C}\circ\pi=\varepsilon\,\prod_{i=1}^pu_i^{a_i},\qquad \pi^*(dw_1\cdots dw_d)=b\,\prod_{i=1}^pu_i^{h_i}\,du_1\cdots du_d ,
\end{equation}
with $\varepsilon,b$ nonvanishing holomorphic functions and integers $a_i>0$, $h_i\ge0$ attached to the components. The pair $(a_E,h_E)$ depends only on the component $E$: $a_E$ is the order to which $K\circ\pi$ vanishes along $E$ and $h_E$ the order to which the Jacobian of $\pi$ does.

Since $K$ has real coefficients the resolution can be built from blow-ups along real centres, and then $U_{\mathbb C}$ carries an anti-holomorphic involution lifting complex conjugation whose fixed locus $U=U_{\mathbb R}$ is a real manifold of dimension $d$ with $\pi\colon U\to W^{(\mathbb R)}$ a proper real analytic map. The components that matter are those whose real points form real hypersurfaces; a pair of conjugate components meeting at a real point, as for $x^2+y^2$, is not yet of this form, and the real resolution continues with real blow-ups until every component through a real point is a real hypersurface, at which point the coordinates in \eqref{eq:local_normal_form} can be taken real \citep[Thm~2.3]{watanabeAlgebraicGeometryStatistical2009}. Nonnegativity of $K$ forces every exponent $a_i$ to be even, $a_i=2k_i$, and $\varepsilon>0$ near the real points; absorbing $\varepsilon^{1/2k_1}$ into $u_1$ we may take $\varepsilon=1$. So the local picture on the real resolution is
\begin{equation}\label{eq:real_normal_form}
K\circ\pi=\prod_{i=1}^pu_i^{2k_i},\qquad \pi^*(\varphi\,dw)=g(u)\prod_{i=1}^p|u_i|^{h_i}\,du ,
\end{equation}
with $g=|b|\,(\varphi\circ\pi)$ smooth, and nonnegative where $\varphi$ is. This is the only place where analyticity is used: it is needed for the resolution of $K$, and for nothing else. The prior enters through $g$, which is smooth, and so does the observable, through $f\circ\pi$.

\input{figures/resolution_schematic}

\subsection{The two divisors}

The formula \eqref{eq:real_normal_form} records two different divisors on $U$. The first is the divisor of $K\circ\pi$, with multiplicities $2k_i$: it says how fast the Boltzmann weight $e^{-nK\circ\pi}$ decays away from the components. The second is the divisor of the pulled-back measure $\pi^*(\varphi\,dw)$, with multiplicities $h_i$: it says how much volume the change of variables has compressed onto each component. The asymptotics of $\int e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ near a component is a competition between the two, and the outcome of the competition in one normal variable is the elementary integral
\begin{equation}\label{eq:one_variable}
\int_0^1u^{h}\,e^{-nu^{2k}}\,du=\frac{1}{2k}\,\Gamma\!\Big(\frac{h+1}{2k}\Big)\,n^{-\frac{h+1}{2k}}+O(e^{-n/2}) ,
\end{equation}
obtained by the substitution $t=nu^{2k}$. The exponent $(h+1)/2k$ is the number attached to a component of the divisor; the smaller it is, the slower the decay, and the more the component contributes. When several components pass through a point the phase is the product $\prod_iu_i^{2k_i}$ and the local integral no longer factors, but its Mellin transform in $n$ does, into $\Gamma(s)$ times one-variable factors $\int u_i^{h_i-2k_is}\,du_i$, so that the exponents combine as poles of the Mellin transform rather than as numbers: this is where the logarithms come from, and it is the subject of \cref{sec:stratification}.

The vanishing orders $h_i$ are the reason the prior cannot be dropped from the picture. Changing the prior does not change the components or the $k_i$, but a prior vanishing along part of $W_0$ changes the $h_i$ there and hence the exponents. In the same way an observable $f$ vanishing to order $l_i$ along $E_i$ shifts the second divisor for the integral $\Zcal_n[f]$ to $h_i+l_i$, which is the mechanism of \cref{sec:wallcrossing}.

\subsection{Irreducible components as primes}

The components $E_i$ are canonical once the resolution is fixed: working with the Zariski topology on $U_{\mathbb C}$, the zero locus of $K_{\mathbb C}\circ\pi$ has a unique decomposition into irreducible components, and by the normal crossing property each is smooth. The analogy to keep in mind is the factorisation of an integer into primes: the components are the primes of the singularity, the multiplicities $2k_i$ are the exponents in the factorisation, and $h_i$ is a second numerical invariant of each prime. Different components represent independent ways in which the model attains zero divergence, and the intersection pattern records how these ways combine. We work over $\mathbb C$ for this decomposition because real analytic sets do not in general admit one \citep{fernando2016irreducible}; the real strata used in the integrals are the real points of the complex ones.

\subsection{An example with a blow-up}\label{ex:blowup}

The running examples of \cref{sec:examples} are already in the form \eqref{eq:real_normal_form}. To see what a resolution does, take $K(x,y)=x^2(x^2+y^2)$ on a neighbourhood of the origin in $\R^2$. Its zero locus is the line $\{x=0\}$, along which $K$ vanishes to order two except at the origin, where it vanishes to order four; since $x^2+y^2$ is not a product of real linear forms, no change of coordinates makes $K$ a monomial near the origin, and a blow-up is genuinely needed. Blowing up the origin replaces it by a projective line $E_0$. In the chart $y=u,\ x=uv$,
\[
K\circ\pi=u^2v^2\big(u^2v^2+u^2\big)=u^4v^2(1+v^2),\qquad dx\,dy=|u|\,du\,dv ,
\]
so $E_0=\{u=0\}$ carries $(k_0,h_0)=(2,1)$ and the strict transform $E_1=\{v=0\}$ of the line $\{x=0\}$, the closure of the preimage of the line with the origin removed, carries $(k_1,h_1)=(1,0)$; the other chart $x=u,\ y=uv$ gives $K\circ\pi=u^4(1+v^2)$ and shows $E_0$ alone. The two components meet in the single point $(u,v)=(0,0)$ of the first chart, $K\circ\pi$ is a monomial times a unit near it, and the singular point of $W_0$ has become a curve $E_0$ with one marked point where it meets the rest of the line. The ratios are $(h_0+1)/2k_0=1/2$ on $E_0$ and $(h_1+1)/2k_1=1/2$ on $E_1$: they tie, and the marked point, where two components of the same ratio meet, carries a logarithm, $\Zcal_n[1]\sim C\,n^{-1/2}\log n$. Nothing in the picture of $W_0$, a smooth line, announces this; the resolution reveals that the origin is more singular than the rest of the line. An observable vanishing at the origin of $W$ vanishes along all of $E_0$ after pull-back, since $\pi(E_0)$ is the origin; for $f=x^2+y^2$ the order is two, $E_0$ moves to the ratio $(1+2+1)/4=1$, the tie is broken, and $\Zcal_n[x^2+y^2]\sim C'n^{-1/2}$ without a logarithm, so that $\E_\infty[x^2+y^2]\sim C''/\log n$. An observable vanishing along the line $\{x=0\}$ itself vanishes along both $E_1$ and $E_0$, and the minimum and its multiplicity must be recomputed at the marked point.

%%%%%%%% sections/04_stratification.tex
\section{The stratification of the exceptional divisor}\label{sec:stratification}

The exceptional divisor $E=E_1\cup\cdots\cup E_r$ is not a manifold: it is a union of manifolds that cross. The natural way to organise it is by how many components pass through a point. This section introduces the resulting stratification, which is the index set of everything that follows, and explains which strata carry the leading behaviour and why.

\subsection{Depth and strata}

For a point $u\in E$ let $I(u)=\{i: u\in E_i\}$ be the set of components through $u$; its size is the \emph{depth} of $u$. For a nonempty $I\subseteq\{1,\dots,r\}$ set
\[
E_I=\bigcap_{i\in I}E_i,\qquad S_I=E_I\setminus\bigcup_{j\notin I}E_j ,
\]
so that $S_I$ is the set of points through which exactly the components indexed by $I$ pass. By the normal crossing property $E_I$ is a smooth submanifold of codimension $|I|$ (or empty) and $S_I$ is open in it. The $S_I$ are the \emph{strata}; they are disjoint, they cover $E$, and the closure of $S_I$ is the union of the $S_J$ with $J\supseteq I$. Ordering by depth gives a filtration by closed sets
\[
E=D_1\supseteq D_2\supseteq\cdots\supseteq D_d,\qquad D_c=\{u\in E:\operatorname{depth}(u)\ge c\}=\bigcup_{|I|\ge c}E_I ,
\]
whose successive differences $D_c\setminus D_{c+1}$ are the unions of the strata of depth $c$. This is a stratification in the sense of \citet{trotmanstrat}, and a particularly well-behaved one: in the local coordinates \eqref{eq:real_normal_form} a stratum of depth $p$ is a coordinate subspace $\{u_1=\cdots=u_p=0\}$ and its normal directions are the coordinate directions $u_1,\dots,u_p$, each labelled by a component and carrying that component's data $(k_i,h_i)$.

In \cref{ex:planes} the strata are the two planes with the axis removed, of depth one, and the axis, of depth two. In \cref{ex:mixed} they are the two lines with the origin removed and the origin. In \cref{ex:blowup} they are the exceptional curve $E_0$ and the strict transform $E_1$ with their common point removed, and that point. The picture to hold on to is a cell decomposition of $E$ in which cells of higher depth lie in the closures of cells of lower depth, and the deepest cells, where the most components meet, are the smallest.

\input{figures/stratification}
\input{figures/planes}

\subsection{Exponents and multiplicities of a stratum}

Near a point of $S_I$ with normal coordinates $u=(u_i)_{i\in I}$ and tangential coordinates $v$ along the stratum, the integrand of $\Zcal_n[f]$ is
\[
(f\circ\pi)(v,u)\;\prod_{i\in I}|u_i|^{h_i}\;e^{-n\prod_{i\in I}u_i^{2k_i}}\;g(v,u)\,du\,dv .
\]
Freezing $v$, the $u$-integral is a $|I|$-dimensional version of \eqref{eq:one_variable}. Its behaviour is governed by the ratios attached to the normal directions,
\[
\lambda_i=\frac{h_i+1}{2k_i}\quad(i\in I),\qquad \lambda_I=\min_{i\in I}\lambda_i,\qquad m_I=\#\{i\in I:\lambda_i=\lambda_I\} ,
\]
and the basic fact, proved in \cref{sec:population}, is that the $u$-integral is asymptotic to a constant times $n^{-\lambda_I}(\log n)^{m_I-1}$. The exponent of a stratum is the smallest ratio among its normal directions; the multiplicity is the number of normal directions attaining it, and the multiplicity less one is the largest power of the logarithm that can occur; whether it does depends on the amplitude, and a positive amplitude guarantees it. A stratum where all normal directions share the same ratio is called \emph{tied} at that exponent; it is the zero-order case of the exact strata of \cref{sec:exact_strata}, and the deepest tied strata at the smallest exponent are where the leading term of $\Zcal_n[1]$ lives.

The mechanism behind the logarithm is worth seeing once in coordinates, and it rests on one classical fact. The Mellin transform of a function $F$ on $(0,\infty)$ is $\int_0^\infty n^{s-1}F(n)\,dn$. For $F(n)=\Zcal_n[1]$ it converges for $0<\operatorname{Re}s<\lambda$, equals $\Gamma(s)\int_WK^{-s}\varphi\,dw$ by Fubini, and continues meromorphically to the plane; a term $c\,n^{-\mu}(\log n)^q$ in the expansion of $F$ corresponds to a pole of order $q+1$ at $s=\mu$, and the poles of the continuation in $\operatorname{Re}s>0$, with their orders and Laurent coefficients, determine the expansion \citep[Ch.~4]{watanabeAlgebraicGeometryStatistical2009}; the poles of $\Gamma(s)$ at the nonpositive integers record the behaviour of $F$ at small $n$, not its asymptotics. The correspondence is made exact in \cref{sec:tiers}. With two normal directions of equal ratio $\lambda$, the Mellin transform of the $u$-integral is a product of two factors each with a simple pole at $s=\lambda$, and a double pole corresponds to a term $n^{-\lambda}\log n$. With different ratios the poles are at different places and the smaller one wins with no logarithm. In \cref{ex:planes} the axis has two normal directions with ratio $1/2$, so $\lambda=1/2$, $m=2$ and $\Zcal_n\sim Cn^{-1/2}\log n$; each plane has a single normal direction with ratio $1/2$ and contributes $n^{-1/2}$ without a logarithm, which is dominated. In \cref{ex:mixed} the origin has normal directions with ratios $1/2$ and $1/6$, so $\lambda=1/6$ and $m=1$, while the line $\{y=0\}$ has the single ratio $1/6$: the leading term $n^{-1/6}$ is carried by the line, and the origin is not exact at $1/6$.

The global exponents of $\Zcal_n[1]$ are
\[
\lambda=\min_I\lambda_I,\qquad m=\max\{m_I:\lambda_I=\lambda\} ,
\]
the real log canonical threshold and its multiplicity \citep{watanabeAlgebraicGeometryStatistical2009}; the exact strata at $(\lambda,m)$, those of depth $m$ all of whose walls have exponent $\lambda$, carry the leading coefficient, which is a sum of integrals over them; a deeper point on the closure of such a stratum, like the origin of \cref{ex:mixed}, has $\lambda_I=\lambda$ but contributes no atom of its own. The whole expansion \eqref{eq:intro_answer} arises in the same way from all strata and all their normal directions: every exponent that occurs is of the form $(h_i+\alpha+1)/2k_i$ for some component $E_i$ and some $\alpha\in\N$, the shift $\alpha$ being the order of a normal derivative of the amplitude, and a stratum contributes at an exponent $\mu$ precisely when each of its normal directions resonates with $\mu$ in this sense. The exponents therefore lie on the lattice $Q^{-1}\N$ with $Q=2\prod_ik_i$, and the logarithmic degree at $\mu$ is bounded by the largest depth of a stratum all of whose normal directions resonate with $\mu$.

\input{figures/mixed}

\subsection{Wall-crossing}\label{sec:wallcrossing}

Now insert an observable. Suppose $f\circ\pi$ vanishes to finite order $l_i$ along $E_i$, meaning that in signed normal coordinates $f\circ\pi=\prod_{i\in I}u_i^{l_i}\tilde f$ near $S_I$ with $\tilde f$ smooth and not identically zero on $S_I$ (a smooth observable may also vanish to infinite order, in which case the stratum contributes nothing at any algebraic order). Then the integrand of $\Zcal_n[f]$ near $S_I$ has the form of the integrand of $\Zcal_n[1]$ with $h_i$ replaced by $h_i+l_i$, up to the sign of $u_i^{l_i}$ on the two sides of an interior wall. The candidate exponents of the stratum shift:
\[
\lambda_I(f)=\min_{i\in I}\frac{h_i+l_i+1}{2k_i}\ \ge\ \lambda_I ,
\]
with equality if and only if $l_i=0$ for some $i$ attaining the minimum, and the multiplicity $m_I(f)$ is recomputed with the shifted ratios. These are candidate first terms: the coefficient at the shifted pair is an integral of $\tilde f$ against a density on the stratum, and it can vanish for a signed $\tilde f$, or by the parity cancellation of \cref{rem:parity}; a nonnegative $\tilde f$ positive somewhere on the stratum where the prior is positive makes it nonzero provided the orders $l_i$ are even in every interior direction, since otherwise the sign of $u_i^{l_i}$ cancels between the two sides ($f=x$ for $K=x^2$ on $[-1,1]$ has $\tilde f=1$ and $\Zcal_n[x]=0$). With this caveat, an observable that vanishes along a component is blind to the strata whose leading behaviour that component carries: it either loses the logarithm, if the component was one of several tied at the minimum, or moves to a higher exponent, if the component carried the minimum alone. If $f$ vanishes along every wall of exponent $\lambda$ the candidate exponent of $\Zcal_n[f]$ is strictly larger than that of $\Zcal_n[1]$, and $\E_\infty[f]\to0$ at a rate that measures the order of vanishing.

This is the sense in which different observables probe different parts of the singular locus. In \cref{ex:planes}, $f=1$ and any $f$ with $\int f(0,0,z)\varphi(0,0,z)\,dz\ne0$ have exponent $1/2$ with a logarithm, carried by the axis (for $f=z$ and a symmetric prior the axis average vanishes and the logarithm is lost); $f=x^2$ vanishes to order two on the plane $\{x=0\}$ and hence on the axis, and the shifted ratios on the axis are $(0+2+1)/2=3/2$ for the $x$-direction and $1/2$ for the $y$-direction, so the axis now has exponent $1/2$ with multiplicity one, while the plane $\{y=0\}$, on which $f=x^2$ does not vanish, still has exponent $1/2$ with multiplicity one: $\Zcal_n[x^2]\sim Cn^{-1/2}$ with no logarithm, and $\E_\infty[x^2]\sim C'/\log n$. The posterior concentrates on the axis, and this is the rate at which it does so. In \cref{ex:blowup}, an observable vanishing at the origin of $W$ shifts the exceptional curve $E_0$; whether this breaks the tie at the marked point depends on the orders ($f=x^2+y^2$ breaks it, while $f=K$ shifts both ratios to $3/2$ and does not), and an observable vanishing along the line $\{x=0\}$ shifts both $E_1$ and $E_0$.

\begin{remark}[Parity]\label{rem:parity}
A component $E_i$ either resolves a wall of the parameter space, in which case the normal coordinate $u_i$ runs over a one-sided interval $[0,\varepsilon)$, or lies in the interior of $U$, in which case $u_i$ runs over $(-\varepsilon,\varepsilon)$. In the second case the population normal integral is a sum over the two sides, and the amplitude is replaced by its even part in $u_i$: all odd normal derivatives in an interior direction drop out of the population expansion, and only even shifts $\alpha$ survive. \cref{ex:planes} has interior components, so its population corrections proceed in steps of $2$ in each normal direction; \cref{ex:mixed} has boundary components, and all shifts are candidates. In the empirical expansion of Part~III the cancellation requires in addition that the field's orthantwise representatives be compatible under the reflection, since an odd derivative of the amplitude can couple to the odd part of the field's exponential; without that symmetry odd candidates survive. The chart-level statements of Parts~II and~III are formulated on the positive box, where both cases are covered by summing over the orthants.
\end{remark}

A remark on what is intrinsic. The candidate exponents and multiplicities read off a resolution are not invariant: a further blow-up adds components and hence candidates (blowing up the axis of \cref{ex:planes} adds a component with $(k,h)=(2,1)$ and the candidates $(2+\alpha)/4$), which then cancel. What is invariant is the expansion itself, its nonzero coefficients and in particular the leading pair; the coefficients we construct in Part~II are pairings of $f$ with measures on the strata, and \cref{sec:population} explains in what sense those measures are independent of the choices made in constructing them. The stratification is scaffolding of the same kind as the coordinates: canonical once $\pi$ is fixed, and used to organise a computation whose outcome is a distribution on $W_0$.

%%%%%%%% sections/05_normal_geometry.tex
\section{The normal geometry of a stratum}\label{sec:normal_geometry}

The coefficients of the expansion will be integrals over strata of normal derivatives of the amplitude. This section fixes what normal means near a stratum of the exceptional divisor, reduces the integral near a stratum to fibre integrals whose asymptotics carry the exponents and logarithms, and states which parts of the resulting description are independent of coordinates. The tubular neighbourhoods and moment tensors of the earlier account of this material are not needed for the proofs and are recorded in \cref{app:moment_tensors}.

\subsection{Normal and tangential coordinates}

Let $S=S_I$ be a stratum. By the normal crossing property, near a point of $S$ there are coordinates $(v,u)$ with $u=(u_i)_{i\in I}$ in which $E_i=\{u_i=0\}$ for $i\in I$, $S=\{u=0\}$, and \eqref{eq:real_normal_form} holds: the normal coordinates are labelled by the components through the stratum, each carrying that component's data $(k_i,h_i)$, and $v$ are coordinates along $S$. Another choice of coordinates of this kind replaces each $u_i$ by a unit multiple $u_i'=g_iu_i$, with $g_i$ a nonvanishing smooth function of all the coordinates, and $v$ by other coordinates along $S$. This is the only freedom, and it is what the coordinate-free statements of \cref{sec:conormal} have to survive.

Along $S$ the differentials $du_i$ span the conormal bundle $N^*S\subseteq T^*U|_S$, the covectors that kill $TS$, and since $du_i'=g_i\,du_i$ on $S$ the line $\mathcal L_i$ spanned by $du_i$ depends only on the component $E_i$. Hence, canonically,
\begin{equation}\label{eq:conormal_splitting}
N^*S=\bigoplus_{i\in I}\mathcal L_i,\qquad \operatorname{Sym}^r(N^*S)=\bigoplus_{|b|=r}\ \bigotimes_{i\in I}\operatorname{Sym}^{b_i}(\mathcal L_i) :
\end{equation}
a stratum knows which of its normal directions belongs to which component, which is what allows the data $(k_i,h_i)$ of the components to be attached to normal directions of the stratum.

\subsection{The fibre integral and the bare moments}

Near $S$ the integrand of $\Zcal_n[f]$ is, in the notation of \eqref{eq:real_normal_form},
\[
(f\circ\pi)\;e^{-n(K\circ\pi)}\;\pi^*(\varphi\,dw)=(f\circ\pi)(v,u)\;|u|^{h_I}\;e^{-nu^{2k_I}}\;g(v,u)\,|du\,dv| ,
\]
where $u^{2k_I}=\prod_{i\in I}u_i^{2k_i}$, $|u|^{h_I}=\prod_{i\in I}|u_i|^{h_i}$, and $g$ is the smooth factor of \eqref{eq:real_normal_form}, the prior times the smooth part of the Jacobian. Freezing $v$, the contribution of a neighbourhood of the stratum is an integral over $S$ of the fibre integrals
\begin{equation}\label{eq:fibre_integral}
\int_{D_v}(f\circ\pi)(v,u)\,|u|^{h_I}\,e^{-nu^{2k_I}}\,g(v,u)\,du ,
\end{equation}
in which $v$ is a parameter and $D_v$ is a box in the normal variables, one-sided in each direction whose component resolves a wall of $W$ and two-sided in each interior direction. Expanding the amplitude $(f\circ\pi)\,g$ in a finite Taylor series in $u$ at $u=0$ turns \eqref{eq:fibre_integral} into a combination of \emph{bare normal moments}
\begin{equation}\label{eq:bare_moment}
M_\alpha(n)=\int_{D}u^\alpha\,|u|^{h_I}\,e^{-nu^{2k_I}}\,du ,
\end{equation}
which are the objects whose asymptotics carry the exponents and logarithms (\cref{sec:population}), plus a remainder. The tangential variable $v$ is inert: it appears only as a parameter in the amplitude, and the outer integral over $S$ is performed last. And over a two-sided direction the odd moments vanish, which is the source of the parity phenomenon of \cref{rem:parity}.

\begin{remark}[Why the crossing does not see everything]\label{rem:flat}
The remainder of the normal Taylor expansion is not negligible in general. It is small near $u=0$, but not along the adjacent walls $\{u_i=0\}$, where the phase $u^{2k_I}$ still vanishes and the Boltzmann weight does not decay. For $K=x^2y^2$ and $S$ the crossing, an amplitude flat at the origin but nonzero on the axis $\{y=0,\ x>0\}$ has every normal Taylor coefficient at the crossing equal to zero, yet contributes a nonzero $n^{-1/2}$ term from the axis. The contributions along the walls belong to the shallower strata, and the bookkeeping that does produce an asymptotic expansion expands the amplitude in the normal directions of each face of the chart cube and subtracts along the face what has already been counted at deeper faces. That is the face construction of \cref{sec:population} and \cref{app:chart_proofs}, from which every coefficient statement of this paper is derived.
\end{remark}

\begin{remark}[Cutoffs]\label{rem:cutoff}
Restricting the fibre to a bounded domain $D_v$ is harmless in one sense and not in another. Localising in the \emph{phase}, to the sublevel set $\{K\circ\pi<\varepsilon\}$, costs $O(e^{-n\varepsilon})$, which is invisible in the scale. Changing the \emph{normal} cutoff, say from $[0,b]^{|I|}$ to $[0,b']^{|I|}$, is not exponentially small, because $u^{2k_I}$ vanishes on the coordinate hyperplanes and the Boltzmann weight does not decay there. Such a change alters the coefficients of the expansion but not its exponents or logarithmic degrees. The coordinate-free formulation of \cref{sec:population} absorbs the cutoff into the partition of unity and makes the total coefficient, summed over strata, independent of these choices.
\end{remark}

\subsection{What is intrinsic}\label{sec:conormal}

Let $\Ical_S$ be the ideal of smooth functions vanishing on $S$. The class of a function $F$ modulo $\Ical_S^{\,r+1}$ is its \emph{transverse $r$-jet} along $S$; in coordinates of the kind above it is the collection of normal Taylor coefficients of $F$ through order $r$, by Hadamard's lemma, and the class itself does not depend on the coordinates. The associated graded is canonical and is the conormal bundle:
\[
\Ical_S^{\,r}/\Ical_S^{\,r+1}\;\cong\;\Gamma\big(S,\operatorname{Sym}^r(N^*S)\big) ,
\]
the leading normal Taylor coefficient of a function vanishing to order $r$ along $S$ being a symmetric $r$-form on the normal bundle, refined by \eqref{eq:conormal_splitting} according to how the order is distributed among the components. What is not canonical is the splitting of a jet into homogeneous pieces: under $u'=gu$ the normal derivatives of order $\beta$ of a function that does not vanish along $S$ pick up contributions from its lower-order derivatives.

The coefficients of the expansion have the following shape. In a normal crossing chart the coefficient at $(\mu,q)$ is a finite sum, over faces of the chart cube, of integrals over the face of normal derivatives of the localised amplitude against explicit densities (\cref{app:chart_proofs}); collecting the terms at a stratum $S$, for an amplitude vanishing near the deeper strata, gives a functional
\begin{equation}\label{eq:conormal_presentation}
F\;\longmapsto\;\sum_{|\beta|\le n}\int_S\partial^\beta_uF\;\rho_\beta ,
\end{equation}
with $\partial_u^\beta$ normal derivatives in the chart and $\rho_\beta$ densities on $S$: in the language of distributions, a \emph{conormal distribution} along $S$ of order $n$, supported on $S$ with singular structure transverse to it. Three things about this functional are proved in \cref{sec:population} and are independent of coordinates. Its support: the coefficient $c_{\mu,q}$ vanishes on observables that vanish near the set of points through which at least $q+1$ walls resonate with $\mu$. Its jet dependence: on observables vanishing near the deeper strata, the top coefficient at an exponent depends only on the transverse jet of a fixed order $n$ along the exact stratum (\cref{thm:jet}), so the functional descends to the quotient of such observables by the corresponding ideal power. And its principal symbol: restricted to observables that in addition vanish to order $n$ along the exact stratum, the functional factors through $\Ical_S^{\,n}/\Ical_S^{\,n+1}\cong\Gamma(S,\operatorname{Sym}^n(N^*S))$ by the previous point, and is therefore a coordinate-free pairing of the leading normal jet with a density on $S$ valued in $\operatorname{Sym}^n(NS)$, the top face density of \cref{thm:graded}. What is not canonical is the rest: the lower terms $\rho_\beta$, $|\beta|<n$, mix under a change of defining equations exactly as the lower Laurent coefficients of a pole of higher order do. Coordinates are therefore needed to \emph{write} a coefficient of positive normal order, and the writing is not unique; what is unique is the functional, the finite jet it depends on, and its principal symbol.

One special case makes the whole functional canonical: when $n=0$ the distribution is a measure on $S$, the stratum measure of \cref{sec:population}, the object through which the leading term and the top logarithmic coefficients are described. When $S$ is a single point the functional is a finite combination of derivatives of the delta function at that point; the combination is canonical as a distribution, while its individual coefficients depend on coordinates through the same mixing.

%%%%%%%% sections/07_population.tex
\section{The stratum measures and the population expansion}\label{sec:population}

This section assembles the machinery into the expansion of $\Zcal_n[f]$ and describes its coefficients. The description proceeds from the coarse to the fine. First the exponents and logarithms, from the poles of a zeta function. Then the leading term at every exponent and depth, which is a measure on a stratum, canonical, and identified with a logarithmic residue of the resolved integrand. Then the corrections, organised as the Laurent data of one meromorphic function, with closed forms in the two situations that matter most. Throughout, $f$ and $\varphi$ are smooth; analyticity has been used once, for the resolution, and will not be used again.

\subsection{The per-stratum decomposition}

Pulling $\Zcal_n[f]$ back to the resolution is a change of variables, legitimate because $\pi$ is a diffeomorphism off a set of measure zero:
\[
\Zcal_n[f]=\int_U(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\]
Off the sublevel set $U_\varepsilon=\{K\circ\pi<\varepsilon\}$ the integrand is $O(e^{-n\varepsilon})$, invisible in the scale, so only a neighbourhood of $E$ matters. A smooth partition of unity $\sum_I\rho_I=1$ on $U_\varepsilon$ subordinate to a cover by normal crossing charts, each chart meeting only the components $E_i$ of one index set $I$ and each $\rho_I$ compactly supported in its chart, gives
% Lean @ d56efc8: Grammar/SmoothResolvedConsumer.lean: Grammar.SmoothEngine.ResolvedData (structure), Grammar.SmoothEngine.ResolvedData.coeff (def), Grammar.SmoothEngine.ResolvedData.coeff_eq_of_transports, Grammar.SmoothEngine.ResolvedData.coeff_comp_gv
% Lean @ d56efc8: Grammar/SmoothResolvedResonantSupport.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_eventually_zero_resonant
\begin{equation}\label{eq:strata_decomposition}
\Zcal_n[f]=\sum_I\Zcal_n[f;I]+O(e^{-n\varepsilon}),\qquad \Zcal_n[f;I]=\int\rho_I\,(f\circ\pi)\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw) .
\end{equation}
The cutoffs depend on all chart coordinates and are simply part of the smooth amplitude that gets differentiated in the normal directions; no cutoff constant along fibres is needed or, in general, available. Each $\Zcal_n[f;I]$ is a chart integral of the form \eqref{eq:empirical_chart} at zero field. The individual terms $\Zcal_n[f;I]$ depend on the partition of unity; the sum does not, and neither do the candidate exponents and logarithmic degrees, which are read off the resolution data alone.

\subsection{The zeta function of a stratum and the shape of the expansion}

The asymptotics of a bare moment \eqref{eq:bare_moment} on the box $[0,b]^{|I|}$ are governed by the poles of
\[
\zeta_\gamma(z)=\int_{[0,b]^{|I|}}(u^{2k_I})^{z}\,u^{\gamma}\,|u|^{h_I}\,du=\prod_{i\in I}\frac{b^{2k_iz+h_i+\gamma_i+1}}{2k_iz+h_i+\gamma_i+1} ,
\]
a product of one-variable integrals because the integrand is a monomial. The $i$-th factor has a simple pole at $z=-(h_i+\gamma_i+1)/2k_i$, so $\zeta_\gamma$ has a pole at $z=-\lambda$ of order $m$ exactly when $m$ of the shifted ratios equal $\lambda$, and the Laplace transform relation $M_\gamma(n)=\int_0^\infty e^{-nt}\,d\nu_\gamma(t)$, with $\nu_\gamma$ the pushforward of $u^\gamma|u|^{h_I}du$ under $u\mapsto u^{2k_I}$, converts a pole of order $m$ at $-\lambda$ into a term $n^{-\lambda}(\log n)^{m-1}$ \citep[Ch.~4]{watanabeAlgebraicGeometryStatistical2009}. The leading Laurent coefficient is explicit: the factors with $i$ in the minimising set $J$ contribute $1/2k_i$ each and the others are evaluated at the pole,
% Lean @ d56efc8: Grammar/SmoothFaceMonoTop.lean: Grammar.SmoothEngine.faceMonoCoeff_top (equal-ratio case only: the constant Gamma(lam)/((m-1)! prod 2k_i); the complementary factors of the mixed-ratio display are a derivation)
\begin{equation}\label{eq:zeta_leading}
M_\gamma(n)\sim\frac{\Gamma(\lambda)}{(m-1)!}\ \prod_{i\in J}\frac1{2k_i}\ \prod_{i\in I\setminus J}\frac{b^{\,h_i+\gamma_i+1-2k_i\lambda}}{h_i+\gamma_i+1-2k_i\lambda}\ \ n^{-\lambda}(\log n)^{m-1} .
\end{equation}
The denominators in the second product are positive because $\lambda$ is the minimum; the factors of $1/2k_i$ are residues against $d\log u_i^{2k_i}$; and the factor $\Gamma(\lambda)/(m-1)!$ comes from the Laplace transform of $t^{\lambda-1}(\log t)^{m-1}$. All three ingredients reappear in the stratum measures below.

Combining \eqref{eq:zeta_leading} with the face construction of \cref{app:chart_proofs} and summing over strata gives the shape of the expansion, which we state now and refine through the rest of the section.

% Lean @ d56efc8: Grammar/SmoothGeneral.lean: Grammar.SmoothEngine.smooth_cutoffExpansion, Grammar.SmoothEngine.smoothCoeff_unique
% Lean @ d56efc8: Grammar/SmoothResolvedConsumer.lean: Grammar.SmoothEngine.ResolvedData.coeff, Grammar.SmoothEngine.ResolvedData.coeff_eq_of_transports, Grammar.SmoothEngine.ResolvedData.coeff_comp_gv
% Lean @ d56efc8: Grammar/SmoothResolvedResonantSupport.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_eventually_zero_resonant (support on {r_mu >= q+1})
% Lean @ d56efc8: Grammar/SmoothResolvedRLCTAsymptotic.lean: Grammar.SmoothEngine.ResolvedData.exists_rlct_asymptotic (Z_n[1] ~ c n^{-lam} (log n)^{m-1}, c>0)
% Lean @ d56efc8: Grammar/SmoothStratumMeasurePositive.lean: Grammar.SmoothEngine.ResolvedData.observableCoeff_pos_of_realised (positivity at the extremal pair)
% Lean: the chart shape of a general coefficient is the face construction defining smoothCoeff; no separate structure theorem is asserted.
\begin{thm}[The population expansion]\label{thm:population_expansion}
For smooth $f$ and $\varphi$ there is an asymptotic expansion
\[
\Zcal_n[f]\sim\sum_{\mu\in Q^{-1}\N}\ \sum_{q=0}^{d-1}c_{\mu,q}(f)\,n^{-\mu}(\log n)^q,\qquad Q=2\prod_ik_i ,
\]
in the sense of \cref{sec:scale}, with the following properties. Each $c_{\mu,q}$ is a linear functional of $f$ which vanishes on every $f$ whose pull-back vanishes near the set of points through which at least $q+1$ walls resonate with $\mu$, a wall $E_i$ resonating when $2k_i\mu-h_i-1\in\N$; in particular $c_{\mu,q}=0$ unless some stratum all of whose walls resonate with $\mu$ has depth at least $q+1$. In a chart each coefficient is a finite sum of normal derivatives of the localised amplitude integrated over faces of the chart cube (\cref{app:chart_proofs}), of the shape \eqref{eq:conormal_presentation}. The exponents that occur are of the form $(h_i+\alpha+1)/2k_i$, $\alpha\in\N$. The first candidate contribution of a stratum $S_I$ is at $\lambda_I(f)$ with logarithmic degree $m_I(f)-1$, with $l_i$ the vanishing orders of \cref{sec:wallcrossing}; its face term is an integral over the stratum of the leading normal jet of $f$ against a positive density, and at the extremal pair, where the normal orders are zero and no other term competes, it is nonzero for $f\ge0$ positive somewhere on the stratum where the prior is positive. In particular
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
the depth-$c$ points all of whose walls resonate; it is a union of strata $S_I$ with $|I|=c$, a locally closed submanifold of codimension $c$. Its closure lies in the closed set $D_c$ of \cref{sec:stratification} and its boundary in $D_{c+1}$, and on the open set $X_c=U\setminus D_{c+1}$ it is relatively closed. The coefficient $c_{\mu,q}$ is supported on the closed set $\{r_\mu\ge q+1\}$, a superlevel set of the resonance count rather than a stratum: a boundary point of the locus where $q+1$ walls resonate lies where more walls meet and belongs to the set automatically.

Call an observable \emph{admissible at depth $c$} if $f\circ\pi$ vanishes on a neighbourhood of $D_{c+1}$, and write $\Ical_{c+1}$ for the space of such pulled-back observables. The filtration $\Ical_1\subseteq\Ical_2\subseteq\cdots$ grades observables by how deep into the divisor they can see: an observable in $\Ical_{c+1}$ sees the strata of depth at most $c$ and is blind to the deeper crossings. Every statement about the depth-$c$ term below is made for admissible observables and on $X_c$. The reason is that at the boundary of an exact stratum a further wall arrives, the residue density of the stratum acquires a further pole, and it blows up whenever $\mu$ exceeds the exponent of the arriving wall; an admissible observable vanishes in a collar around that boundary, so the blow-up is met only where the observable is already zero. In \cref{ex:planes}, admissibility at depth one means vanishing near the axis, and admissibility at depth two is automatic since there are no points of depth three.

\input{figures/depth}

\subsection{The graded stratum formula}\label{sec:graded}

% Lean @ d56efc8: Grammar/SmoothResolvedStratumFormula.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_zero_of_deep, Grammar.SmoothEngine.ResolvedData.coeff_eq_stratumSum
% Lean @ d56efc8: Grammar/SmoothFaceSumCollapse.lean: Grammar.SmoothEngine.smoothCoeff_eq_faceSum_top (chart form, JetsZeroOn the deep set)
% Lean @ d56efc8: Grammar/SmoothFaceMonoTop.lean: Grammar.SmoothEngine.faceMonoCoeff_top (constant Gamma(mu)/((c-1)! prod 2k_j); the 1/alpha_j! is faceW)
\begin{thm}[Graded stratum formula]\label{thm:graded}
Let $c\ge1$ and $f\circ\pi\in\Ical_{c+1}$. Then $c_{\mu,q}(f)=0$ for $q\ge c$, and $c_{\mu,c-1}(f)$ is a finite sum of absolutely convergent integrals over $S^\mu_c$. In a normal crossing chart with face coordinates $u_J=0$, $|J|=c$, the contribution of the face differentiates the whole localised amplitude $\eta=\rho\,g\,(f\circ\pi)$, the cutoff times the smooth density factor $g$ of \eqref{eq:real_normal_form} times the observable, in the $c$ normal directions to the resonant orders $\alpha_j=2k_j\mu-h_j-1$, integrates against the tangential weight, and multiplies by a constant; here $0_J$ is the point of the face with all $J$-coordinates zero and $w$ collects the remaining coordinates:
\begin{equation}\label{eq:graded}
\frac{\Gamma(\mu)}{(c-1)!\prod_{j\in J}2k_j\,\alpha_j!}\int_{u_J=0}\partial^\alpha_J\eta\,(0_J,w)\;\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,dw .
\end{equation}
Only faces all of whose walls resonate contribute, and a face point with exactly the $J$-coordinates zero is a point of depth $|J|$, so these are integrals over $S^\mu_c$.
\end{thm}

The theorem says that the top logarithmic power at an exponent sees only the deepest exact stratum: a face of smaller depth produces a pole of lower order and cannot reach $(\log n)^{c-1}$. The vanishing of the degrees $q\ge c$ is a separate statement of the same construction. The summed coefficient is the invariant object and descends to a functional on $\Ical_{c+1}/\Ical_c$; the individual chart contributions are not asserted to be canonical, in accordance with \cref{sec:conormal}. The tangential weight $\prod_{i\notin J}w_i^{h_i-2k_i\mu}$ is integrable up to the boundary of the face exactly when $\mu<(h_i+1)/2k_i$ for every complementary wall $i$, resonant or not (for $K=x^2y^2$ at $\mu=1/2$ and $c=1$ the complementary wall is resonant and the weight $dx/|x|$ diverges); admissibility removes the need for this, since the amplitude vanishes near the deeper faces. Where the condition does hold, the formula is valid for all smooth $f$, which is the situation of \cref{sec:tiers}.

\subsection{Jet dependence, without coordinates}\label{sec:jets}

With the transverse jets of \cref{sec:conormal}, define, for $P\in E$, the \emph{intrinsic jet order}
\[
n_\mu(P)=\sum_{\text{walls }E_i\text{ through }P}\max\big(\lfloor2k_i\mu\rfloor-h_i-1,\,0\big) ,
\]
so that only walls whose resonant order is nonnegative count; at a point of $S^\mu_c$ every wall resonates and $n_\mu(P)=|\alpha|$.

% Lean @ d56efc8: Grammar/SmoothStratumJetDependence.lean: Grammar.SmoothEngine.ResolvedData.coeff_eq_of_memIdealPow, Grammar.SmoothEngine.ResolvedData.stratumJetOrder (= n_mu(P)), Grammar.SmoothEngine.ResolvedData.MemIdealPowNear
% Lean @ d56efc8: Grammar/SmoothStratumJetDescent.lean: Grammar.SmoothEngine.ResolvedData.descendedCoeff, Grammar.SmoothEngine.ResolvedData.admissible, Grammar.SmoothEngine.ResolvedData.jetKernelAdm
\begin{thm}[Jet dependence]\label{thm:jet}
Let $c\ge1$ and $F,F'\in\Ical_{c+1}$. If the germ of $F-F'$ at every $P\in S^\mu_c$ lies in $\Ical_{S^\mu_c,P}^{\,n_\mu(P)+1}$, then $c_{\mu,c-1}$ takes the same value on $F$ and $F'$. The functional therefore descends to the quotient of the admissible observables by those lying in $\Ical_{S^\mu_c}^{\,n_\mu(\cdot)+1}$ near every point of the stratum.
\end{thm}

The proof runs through \cref{thm:graded}: at an exactly resonant face the amplitude is a smooth multiple of $F$, a difference in $\Ical_S^{\,|\alpha|+1}$ is locally a sum of smooth multiples of products of $|\alpha|+1$ functions vanishing at the face, and a coordinate derivative of total order $|\alpha|$ of such a product vanishes there because the Leibniz rule leaves some factor undifferentiated. The order $n_\mu(P)$ is an upper bound: cancellations, or vanishing of the prior, can lower the true order at particular points. In the language of \cref{sec:conormal}, the coefficient depends on the observable only through its transverse $|\alpha|$-jet along the exact stratum. This is the precise form of the statement that the observable is seen through finitely many normal derivatives on a stratum, and it needs no choice of tubular neighbourhood.

\subsection{The stratum measure}\label{sec:stratum_measure}

Now impose the \emph{zero-order condition} on $S^\mu_c$: every wall through the exact stratum satisfies $2k_j\mu=h_j+1$, so that all $\alpha_j=0$ and the twisted density $(K\circ\pi)^{-\mu}\pi^*(\varphi\,dw)$ has simple poles along the $c$ walls. Then \cref{thm:graded} contains no derivatives, the functional $c_{\mu,c-1}$ is nonnegative on nonnegative admissible observables and depends only on their values on $S^\mu_c$, and a positive local linear functional is a measure.

% Lean @ d56efc8: Grammar/SmoothStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.stratumMeasure (def), Grammar.SmoothEngine.ResolvedData.coeff_withF_eq_integral_stratumMeasure, Grammar.SmoothEngine.ResolvedData.stratumMeasure_compl_exactStratum, Grammar.SmoothEngine.ResolvedData.eq_stratumMeasure_of_tests, Grammar.SmoothEngine.ResolvedData.stratumMeasure_eq_of_transports
% Lean @ d56efc8: Grammar/SmoothResolvedStratumPositive.lean: Grammar.SmoothEngine.ResolvedData.ZeroOrder, Grammar.SmoothEngine.ResolvedData.exactStratum
% Lean @ d56efc8: Grammar/SmoothStratumTest.lean: Grammar.SmoothEngine.ResolvedData.stratumOpen (= X_c), Grammar.SmoothEngine.ResolvedData.IsTest
\begin{thm}[The stratum measure]\label{thm:stratum_measure}
Let $c\ge1$ and assume the zero-order condition on $S^\mu_c$. There is a positive Radon measure $\nu^\mu_c$ on $X_c=U\setminus D_{c+1}$, carried by the exact stratum, such that for every $f$ with $f\circ\pi\in\Ical_{c+1}$ the restriction of $f\circ\pi$ to $X_c$ is $\nu^\mu_c$-integrable and
\begin{equation}\label{eq:stratum_measure}
c_{\mu,c-1}(f)=\int_{X_c}f\circ\pi\,d\nu^\mu_c .
\end{equation}
It is the unique positive Radon measure on $X_c$ with these integrals on smooth compactly supported tests, and for the fixed resolution and prior it does not depend on the tubular neighbourhoods, cutoffs or partitions of unity used to compute it.
\end{thm}

The construction is the Riesz--Markov--Kakutani theorem applied to $T[G]=c_{\mu,c-1}[G]$ on smooth compactly supported tests $G$ in $X_c$: $T$ is linear, positive and local to the stratum, and it satisfies the fixed-support bound $|T[G]|\le\|G\|_\infty T[\chi_L]$ for a cutoff $\chi_L$ equal to one on a compact $L$ containing the support of $G$, which gives continuity and hence extension to $C_c(X_c)$. Nothing is asserted about $\nu^\mu_c$ across $D_{c+1}$: it need not have finite mass, and it is not extended to $U$.

\subsection{The weighted logarithmic residue}\label{sec:residue}

The stratum measure has a name from complex geometry. Write $a=\rho\,g$ for the density amplitude without the observable, so that the localised amplitude of \cref{thm:graded} is $\eta=a\,(f\circ\pi)$. In a normal crossing chart the twisted density near a face $u_J=0$ of the exact stratum is
\[
\prod_{j\in J}|u_j|^{h_j-2k_j\mu}\,a(u)\,|du|=\prod_{j\in J}\frac{|du_j|}{|u_j|}\cdot a\,|du_{J^c}| ,
\]
with every pole simple under the zero-order condition. Extracting the pole along $E_j$ against $d\log(u_j^{2k_j})=2k_j\,du_j/u_j$ contributes a factor $(2k_j)^{-1}$, and doing so for all $j\in J$ leaves on the face the density
\begin{equation}\label{eq:face_density}
\prod_{j\in J}(2k_j)^{-1}\,a(0,w)\prod_{i\notin J}w_i^{h_i}\Big(\prod_{i\notin J}w_i^{2k_i}\Big)^{-\mu}\,|dw| ,
\end{equation}
which is exactly the tangential weight of \eqref{eq:graded} at zero order, before the observable is inserted. Define
% Lean @ d56efc8: Grammar/SmoothStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.residueMeasure (def: ((c-1)!/Gamma(mu)) * stratumMeasure), Grammar.SmoothEngine.ResolvedData.residueMeasure_compl_exactStratum
\begin{equation}\label{eq:residue_measure}
\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\,\nu^\mu_c .
\end{equation}

% Lean @ d56efc8: Grammar/SmoothChartResidueMeasure.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure (def: face densities with (2k_j)^{-1} per wall)
% Lean @ d56efc8: Grammar/SmoothChartResidueIdentity.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure_eq_residueMeasure
\begin{thm}[The residue formula]\label{thm:residue}
Under the zero-order condition, for every admissible $f$ the integral $\int f\circ\pi\,d\Rres^\mu_c$ is the sum over charts and over simple faces $J$ of the face integrals of $f\circ\pi$ against \eqref{eq:face_density}, with chart and face multiplicities retained, and
\[
c_{\mu,c-1}(f)=\frac{\Gamma(\mu)}{(c-1)!}\int_{S^\mu_c}f\circ\pi\,d\Rres^\mu_c .
\]
\end{thm}

The measure $\Rres^\mu_c$ has two coordinate-free descriptions, and their agreement is what licenses the name.

\paragraph{Through the asymptotics.} Nothing in \eqref{eq:residue_measure} uses a chart: $\Rres^\mu_c$ is defined by coefficient extraction, and when no term more dominant than $n^{-\mu}(\log n)^{c-1}$ is present, which is the case at the leading pair and, for an admissible test, whenever all the more dominant candidate coefficients vanish, it is given by the limit
% Lean @ d56efc8: Grammar/SmoothStratumMeasureExtremal.lean: Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal (the limit in the leading situation)
% Lean: the sublevel-set form below is a derivation, not formalised.
\begin{equation}\label{eq:defA}
\int F\,d\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\lim_{n\to\infty}n^{\mu}(\log n)^{-(c-1)}\int_UF\,e^{-nK\circ\pi}\,\pi^*(\varphi\,dw)
\end{equation}
for $F$ vanishing near $D_{c+1}$; in general the more dominant terms must be subtracted first. $\Rres^\mu_c$ is the unique regular measure on $X_c$ with the coefficient values on tests. In the same leading situation one may replace the Laplace weight by sublevel sets of the phase,
\[
\int F\,d\Rres^\mu_c=\lim_{\delta\to0}\frac{c!}{(\log1/\delta)^c}\int_{\{K\circ\pi>\delta\}}F\,(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw) ,
\]
a truncated negative moment of the phase against the prior; in the logarithmic coordinates $t_j=2k_j\log(1/|u_j|)$ the region is the simplex $\sum t_j<\log(1/\delta)$, whose volume $(\log1/\delta)^c/c!$ is where the constant and the multiplicities $2k_j$ come from.

\paragraph{As an iterated density residue.} A positive density $\omega$ with a simple pole along a hypersurface $\{g=0\}$, meaning that $|g|\omega$ extends smoothly across it, has a residue $\operatorname{res}\omega=(|g|\omega)|_{\{g=0\}}/|dg|$, a positive density on the hypersurface independent of the choice of $g$, and characterised by the logarithmic divergence of the collar integral: $\int G\,\operatorname{res}\omega=\lim_{\varepsilon\to0}\frac1{2\log(1/\varepsilon)}\int_{\varepsilon<|g|<r}\tilde G\,\omega$ for a two-sided wall, with $\log(1/\varepsilon)$ in place of $2\log(1/\varepsilon)$ for a one-sided one. Along $c$ walls meeting transversally the residue is iterated, and for densities every step is unsigned and the result is symmetric in the walls. Summing over the permitted normal sides of each wall and dividing by the multiplicity $2k_j$ of the divisor of $K\circ\pi$,
\begin{equation}\label{eq:defB}
\Rres^\mu_c=\frac{2^{c_{\mathrm{int}}}}{\prod_{j\in J}2k_j}\,\operatorname{res}_{S^\mu_c}\big[(K\circ\pi)^{-\mu}\,\pi^*(\varphi\,dw)\big]
\end{equation}
on each component of the stratum with walls $J$, where $c_{\mathrm{int}}$ is the number of interior (two-sided) walls among them and the density factor is assumed to match on the two sides; in general the residue measure is the sum over the permitted normal orthants of the one-sided residues, with $(2k_j)^{-1}$ per wall. Both the divisor and its multiplicities are intrinsic to $K\circ\pi$, so this is a coordinate-free density on the exact stratum.

% Lean @ d56efc8: Grammar/SmoothChartResidueIdentity.lean: Grammar.SmoothEngine.ResolvedData.chartResidueMeasure_eq_residueMeasure
% Lean: the manifold-level residue calculus for densities is not developed formally; the identity is with the chart face densities.
\begin{thm}[Identity of the two descriptions]\label{thm:identity}
Under the zero-order condition, the iterated density residue \eqref{eq:defB}, computed in any resolved chart atlas as the sum of the face densities \eqref{eq:face_density} pushed into $U$ and restricted to $X_c$, is a regular measure on $X_c$ that integrates tests to the residue sums of \cref{thm:residue}. Hence it equals $\Rres^\mu_c$, and $\nu^\mu_c=\frac{\Gamma(\mu)}{(c-1)!}\Rres^\mu_c$.
\end{thm}

The classical Poincar\'e residue takes a meromorphic form with a simple pole to a form on the polar hypersurface and is signed; here the object with the pole is a positive density and the residue is a positive density on the stratum. The two agree up to sign and normalisation where both make sense. The sanity check in one variable: for $K=x^{2k}$ on $\R$ with $\mu=1/2k$ and $\varphi\,dx=dx$, the residue of $|x|^{-1}|dx|$ at the origin is $1$, the two sides give $2$, and $\Rres^\mu_1=\frac1k\delta_0$, which is the coefficient of $n^{-1/2k}$ in $\int e^{-nx^{2k}}dx=\Gamma(\frac1{2k})n^{-1/2k}/k$ divided by $\Gamma(\mu)$.

\subsection{The leading term with insertion}\label{sec:leading}

Let $\lambda$ be the minimum of the wall exponents $(h_i+1)/2k_i$ over the components with real points and $m$ the maximum number of walls of exponent $\lambda$ through a point of $E$. Extremality forces the zero-order condition on every exact $\lambda$-resonant stratum, since a resonant wall with $2k\lambda=h+1+\alpha$, $\alpha\ge1$, would have exponent below $\lambda$. So the stratum measures $\nu^\lambda_c$ exist for every $c$, and the deepest one describes the leading term.

% Lean @ d56efc8: Grammar/SmoothStratumMeasureExtremal.lean: Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure (def), Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal
% Lean @ d56efc8: Grammar/SmoothStratumMeasurePositive.lean: Grammar.SmoothEngine.ResolvedData.observableCoeff_pos_of_realised
% Lean @ d56efc8: Grammar/SmoothStratumMeasureFinite.lean: Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure_univ_le, Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure_univ_eq_of_deep_empty
% Lean @ d56efc8: Grammar/SmoothResolvedRLCTIndex.lean: Grammar.SmoothEngine.ResolvedData.IsExtremalData
\begin{thm}[Leading asymptotic with insertion]\label{thm:leading}
For every smooth $f$ whose pull-back vanishes on a neighbourhood of $D_{m+1}$,
\[
n^{\lambda}(\log n)^{-(m-1)}\,\Zcal_n[f]\longrightarrow\int_Xf\circ\pi\,d\nu^\lambda_m=\frac{\Gamma(\lambda)}{(m-1)!}\int_{S^\lambda_m}f\circ\pi\,d\Rres^\lambda_m .
\]
If $f\ge0$ is positive at the image of a point of $S^\lambda_m$ at which the prior is positive, the limit is positive and $\Zcal_n[f]\sim\big(\int f\circ\pi\,d\nu^\lambda_m\big)n^{-\lambda}(\log n)^{m-1}$. The leading stratum measure is finite, with $\nu^\lambda_m(X)\le c_{\lambda,m-1}(1)$, and with equality when $D_{m+1}=\varnothing$.
\end{thm}

The admissibility hypothesis is vacuous when $D_{m+1}$ is empty, as in \cref{ex:planes}; in \cref{ex:mixed} the origin lies in $D_2$ while $m=1$. It is a restriction of the formal statement, not of the mathematics. At the extremal pair a further wall through a point of the closure of $S^\lambda_m$ has exponent strictly greater than $\lambda$, since equality would produce a point with $m+1$ walls of exponent $\lambda$; its tangential weight $w^{h-2k\lambda}$ therefore has exponent greater than $-1$ and is integrable, the leading residue density extends across $D_{m+1}$ with finite mass, as the bound $\nu^\lambda_m(X)\le c_{\lambda,m-1}(1)$ records, and the leading formula holds for every smooth $f$ with the extended measure (in \cref{ex:mixed} the weight $x^{-1/3}$ is integrable at the origin). This extension is a derivation and is not among the pinned declarations; wherever the normalised leading measure $\nu^\lambda_m/\nu^\lambda_m(X)$ is used below for the denominator $\Zcal_n[1]$, either $D_{m+1}=\varnothing$ or the extended measure is understood.

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample at a = 0 (x^2y^2 on the unit square, constant amplitude)
% Lean: the displayed measures for general prior are derivations from thm:residue.
\begin{example}[The running examples]\label{ex:population_examples}
For \cref{ex:planes} the components are the planes $E_1=\{x=0\}$, $E_2=\{y=0\}$ with $(k,h)=(1,0)$, $\lambda=1/2$, $m=2$, and $D_3=\varnothing$, so every observable is admissible at depth two. The twisted density is $\varphi\,dx\,dy\,dz/|xy|$, with simple poles along both planes. At depth two the exact stratum is the axis; each of the four quadrants around it contributes the iterated residue with a factor $1/2$ per wall, and
\[
\nu^{1/2}_2=\sqrt\pi\,\varphi(0,0,z)\,dz\quad\text{on the axis},\qquad \Zcal_n[f]\sim\sqrt\pi\Big(\int_{-1}^1f(0,0,z)\varphi(0,0,z)\,dz\Big)n^{-1/2}\log n\quad\text{when the axis average is nonzero}.
\]
The posterior concentrates on the axis with density proportional to the prior along it, and the leading expectation of $f$ is its prior-weighted average along the axis. At depth one the exact stratum is the two planes minus the axis, $X_1=U\setminus\{x=y=0\}$, and
\[
\nu^{1/2}_1=\sqrt\pi\Big(\varphi(x,0,z)\frac{dx\,dz}{|x|}+\varphi(0,y,z)\frac{dy\,dz}{|y|}\Big) ,
\]
with infinite mass near the axis. For $f$ vanishing near the axis, $c_{1/2,0}(f)=\int f\,d\nu^{1/2}_1$ is the coefficient of $n^{-1/2}$ without a logarithm. For $f$ not vanishing on the axis the $n^{-1/2}$ coefficient is not this divergent integral but a finite part in which the axis and the planes share the constant non-canonically. The complete functional $c_{1/2,0}$ is canonical, and its restriction to observables vanishing near the axis is the plane-measure integral; only its decomposition into plane finite parts and an axis term depends on conventions. For \cref{ex:mixed}, $\lambda=1/6$ with $m=1$, the exact stratum at $(1/6,1)$ is the line $\{y=0\}$ minus the origin, and since the wall $\{x=0\}$ has exponent $1/2>1/6$ the weight $x^{0}(x^{2})^{-1/6}=x^{-1/3}$ is integrable up to the origin: the leading measure is $\frac{\Gamma(1/6)}{6}\,\varphi(x,0)\,x^{-1/3}dx$ on $[0,1]$, finite, and no admissibility is needed.
\end{example}

\input{figures/x2y2}

\subsection{The Laurent data and the three tiers}\label{sec:tiers}

The stratum measures describe the top logarithmic coefficient at each exponent under the zero-order condition. All the coefficients are described at once by a single meromorphic function. For $0<\operatorname{Re}s<\lambda$ the Mellin transform of the partition function in $n$ is, by Fubini,
\begin{equation}\label{eq:zeta_global}
\mathcal Z_f(s)=\int_0^\infty n^{s-1}\Zcal_n[f]\,dn=\Gamma(s)\int_Wf\,K^{-s}\,\varphi\,dw=\Gamma(s)\int_U(f\circ\pi)\,(K\circ\pi)^{-s}\,\pi^*(\varphi\,dw) ,
\end{equation}
Watanabe's zeta function of the pair $(K,\varphi)$ with the observable inserted. It continues meromorphically to $\mathbb C$, with poles in $\operatorname{Re}s>0$ on the lattice and, from $\Gamma(s)$, at the nonpositive integers, and the expansion of \cref{thm:population_expansion} is equivalent to the statement
% Lean @ d56efc8: Grammar/MellinRegularization.lean: Grammar.mellin_eq_mellin_cutoffRemainderFun_add_principalParts
% Lean @ d56efc8: Grammar/PrincipalPartUniqueness.lean: Grammar.polarCoeff_unique, Grammar.mellinContinuation, Grammar.polarCoeff
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaPolar.lean: fluctuationZeta_eq_mellinContinuation, isFrozenCoeff_polarCoeff_unique (population case = zero field)
\begin{equation}\label{eq:laurent}
c_{\mu,q}(f)=\frac{(-1)^{q+1}}{q!}\,\big[(s-\mu)^{-(q+1)}\big]\,\mathcal Z_f(s) ,
\end{equation}
the coefficient of $n^{-\mu}(\log n)^q$ being the Laurent coefficient of order $q+1$ at $s=\mu$. Every coefficient is thus the pairing of the amplitude with a Laurent coefficient of the meromorphic distribution-valued function $s\mapsto(K\circ\pi)^{-s}\pi^*(\varphi\,dw)$, whose poles sit on the resonant strata. This is the definition from which the two closed forms below are evaluations, and it is the form in which the empirical coefficients of \cref{sec:empirical} will be obtained by replacing $\Gamma(s)$ with the fluctuation function.

\paragraph{One resonant coordinate.} Suppose that at $\mu$ only one wall $E_{i_0}$ resonates near the points in question, with $\alpha=2k_{i_0}\mu-h_{i_0}-1\in\N$. Then the pole of \eqref{eq:zeta_global} is simple, there is no logarithm, and in a chart with normal coordinate $u$ for $E_{i_0}$ and tangential coordinates $w$,
% Lean: not formalised; the closed finite-part form is a derivation; the formal coefficient at this pair is smoothCoeff (Taylor-subtracted face construction, Grammar/SmoothGeneral.lean), and for alpha <= 1 under the gap hypothesis it is empCoeff_generic at zero field (Grammar/FirstCorrection.lean).
\begin{equation}\label{eq:tier2}
c_{\mu,0}(f)=\frac{\Gamma(\mu)}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\eta\,(0,w)\;\prod_{i\ne i_0}w_i^{h_i}\Big(\prod_{i\ne i_0}w_i^{2k_i}\Big)^{-\mu}\,dw ,
\end{equation}
where $\eta$ is the localised amplitude and FP is the Hadamard finite part in those $w_i$ with $(h_i+1)/2k_i<\mu$: in one tangential variable with $a=h-2k\mu$ not a negative integer and $N$ large,
\[
\mathrm{FP}\!\int_0^1g(w)w^a\,dw=\int_0^1\Big(g(w)-\sum_{j\le N}\frac{g^{(j)}(0)}{j!}w^j\Big)w^a\,dw+\sum_{j\le N}\frac{g^{(j)}(0)}{j!\,(a+j+1)} ,
\]
the subtraction of the Taylor polynomial together with the compensating integrated monomials, iterated in the several variables and with the boundary cutoffs fixed; when $\mu$ is below every other exponent the integral converges and no finite part is needed. Up to the sign $(-1)^\alpha$ this is the pairing with $\delta^{(\alpha)}(u)\otimes\mathrm{FP}\,w^{h-2k\mu}$. In \cref{ex:mixed} the leading term is the case $\alpha=0$ and the first correction at $n^{-1/3}$ the case $\alpha=1$, both with convergent integrals since $1/3<1/2$:
\[
c_{1/3,0}(f)=\frac{\Gamma(1/3)}{6}\int_0^1\partial_y\eta(x,0)\,x^{-2/3}\,dx,\qquad \eta=\varphi\cdot f .
\]

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (x^2y^2, constant amplitude: n^{-1/2}/4 [Gamma(1/2) log n - Gamma'(1/2)] at a = 0)
% Lean: the x^2y^2 formulas for nonconstant amplitude are derivations.
\paragraph{Ties.} When $c$ walls resonate at $\mu$ the pole has order $c$. The coefficient of the top power $(\log n)^{c-1}$ is the graded formula \eqref{eq:graded}, a product of normal deltas against the residue density on the face. The lower powers are read off the Laurent expansion: Taylor-expanding the amplitude in the coordinates $u_J$ to order $\alpha$ and integrating $u_J^{h_J+\alpha-2k_Js}$ over the $J$-cube produces the factor $\prod_{j\in J}(2k_j(\mu-s))^{-1}$ times the tangential integral of $\partial^\alpha_J\eta(0_J,w)/\alpha!$ against $w^{h-2ks}$; expanding that tangential integral around $s=\mu$ contributes the powers of $\log w^{2k}$, and the expansion of $\Gamma(s)$ contributes derivatives of the Gamma function. A face $J'\supsetneq J$ resonating at the same $\mu$ makes the tangential integral itself singular, raising the pole order, and its finite part is what the lower coefficients compute. In the simplest tie, \cref{ex:planes} at $\mu=1/2$ with amplitude $\eta=\varphi f$ restricted to a slice $z=$ const, one finds, with $\eta_s=\Gamma(s)\eta$,
\[
c_{1/2,1}=\frac{\eta_{1/2}(0,0)}4,\qquad c_{1/2,0}=-\frac{\partial_s\eta_s(0,0)|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}{x}\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}{y}\,dy
\]
per quadrant and per $z$, each quadrant with its own pulled-back amplitude; the full coefficients are obtained by summing the four quadrants and integrating over $z$. The lower logarithm at a tie is the derivative in the exponent at the deepest stratum plus finite parts of the amplitude along the subfaces. The derivative in the exponent, here $\Gamma'(1/2)\eta(0,0)$, becomes in the empirical case the index derivative of the fluctuation function.

\subsection{Population posterior expectations}\label{sec:population_posterior}

The expectation $\E_\infty[f]=\Zcal_n[f]/\Zcal_n[1]$ is the quotient of two expansions in the same scale, and the leading block of the denominator has top term $c\,(\log n)^{m-1}$ with $c>0$, so the quotient is an expansion in the sense of \cref{sec:scale} with coefficients rational in $\log n$ (\cref{app:expansion_algebra}). Three cases arise at leading order, according to how $f$ meets the leading strata.

\begin{itemize}
% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO' (quotient of two cutoff expansions)
% Lean @ d56efc8: Grammar/MomentKernel.lean: HasLeadingTerm.div (ratio of leading terms)
\item \emph{Generic observable.} If $\int f\circ\pi\,d\nu^\lambda_m\ne0$, which holds when $f\circ\pi$ does not vanish identically on $S^\lambda_m$ and has a sign there, the exponents and logarithmic degrees of numerator and denominator agree and
\[
\E_\infty[f]\longrightarrow\frac{\int f\circ\pi\,d\nu^\lambda_m}{\nu^\lambda_m(X)} ,
\]
the average of $f$ against the normalised leading stratum measure. The posterior concentrates on the deepest exact strata of lowest exponent, with the density \eqref{eq:face_density}.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on all of $S^\lambda_m$ and $m'-1<m-1$ is the largest logarithmic degree at which its coefficient at $\lambda$ is nonzero, the exponent is unchanged and the logarithmic degree drops: $\E_\infty[f]\sim D(\log n)^{-(m-m')}$, $D\ne0$ (the largest degree matters: for $K=x^2y^2z^2$ on $[0,1]^3$ and $f=x^2$ the numerator has nonzero coefficients at degrees $1$ and $0$, and the rate is $2/\log n$). This is \cref{ex:planes} with $f=x^2$: the expectation decays like $1/\log n$, the rate at which the posterior concentrates on the axis.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$, the first candidate exponent of $\Zcal_n[f]$ is strictly larger and, if some coefficient of $\Zcal_n[f]$ is nonzero, $\E_\infty[f]=Dn^{-(\mu-\lambda)}(\log n)^{q-(m-1)}+o(\cdot)$ decays as a power, with $(\mu,q)$ the first such pair; an observable flat along the walls, such as $e^{-1/x^2}$ for $K=x^2$, has no nonzero coefficient and its expectation decays faster than every power. The observable $f=K$ is the canonical instance: $K\circ\pi$ vanishes to order $2k_i$ along every wall, shifting every exponent by exactly one, so $\E_\infty[K]\sim\lambda/n$, and indeed $\E_\infty[K]=-\frac{d}{dn}\log\Zcal_n[1]=\frac\lambda n-\frac{m-1}{n\log n}+\cdots$ exactly.
\end{itemize}

\input{figures/wall_crossing}

As the observable varies in a family, the vanishing orders along the walls are generically constant and change only at special values, where the candidate exponent of $\E_\infty[f_\tau]$ jumps by a rational amount determined by $(k_i,h_i,l_i)$; the actual exponent follows when the corresponding coefficient is nonzero. This wall-crossing is the discrete signal by which expectation values report the structure of $W_0$. In the running examples: for \cref{ex:planes}, $\E_\infty[f]\to\int f(0,0,z)\varphi(0,0,z)dz/\int\varphi(0,0,z)dz$ for $f$ with nonzero axis average and $\E_\infty[x^2]\sim C/\log n$; for \cref{ex:mixed}, $\E_\infty[f]\to\int_0^1f(x,0)\varphi(x,0)x^{-1/3}dx/\int_0^1\varphi(x,0)x^{-1/3}dx$. The full expansion of the quotient, to all orders, is deferred to \cref{sec:posterior}, where it is treated together with its empirical counterpart.

%%%%%%%% sections/08_fluctuation.tex
\section{The fluctuation function}\label{sec:fluctuation}

The population expansion is built from one-variable integrals $\int u^he^{-nu^{2k}}du$, whose value is a Gamma function times a power of $n$. When the sample enters, the exponent acquires the term $\sqrt n\,u^k\zeta(u)$ of \cref{sec:setting}, and the same one-variable integral produces a different special function. This section introduces it, records the algebra it satisfies, and explains why that algebra is the whole mechanism by which the data enters the coefficients.

\subsection{The one-variable computation}

Take a single normal coordinate with data $(k,h)$ and freeze the field at a constant $a$. The substitution $t=nu^{2k}$ gives
\begin{equation}\label{eq:one_variable_field}
\int_0^\infty u^h\,e^{-nu^{2k}+\sqrt n\,u^ka}\,du=\frac{n^{-\mu}}{2k}\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}\,dt,\qquad \mu=\frac{h+1}{2k} ,
\end{equation}
because $\sqrt n\,u^k=\sqrt t$. The exponent is unchanged from the population case; the constant $\Gamma(\mu)$ has become a function of $a$.

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.fluctuation (def; general beta, here beta = 1)
\begin{defn}[Fluctuation function]\label{def:fluctuation}
For $\mu>0$ and $a\in\R$,
\begin{equation}\label{eq:fluctuation}
S_\mu(a)=\int_0^\infty t^{\mu-1}\,e^{-t+a\sqrt t}\,dt .
\end{equation}
\end{defn}

The integral converges for every $a$, since $-t+a\sqrt t=-(\sqrt t-a/2)^2+a^2/4$, and $S_\mu(0)=\Gamma(\mu)$. The same integral defines $S_s(a)$ for complex $s$ with $\operatorname{Re}s>0$, holomorphic in $s$, which is the form used in \cref{sec:empirical}. This is Watanabe's fluctuation function \citep[Def.~5.8]{watanabeAlgebraicGeometryStatistical2009} at unit temperature; a temperature $\beta$ is absorbed by $n\mapsto\beta n$ and $a\mapsto\sqrt\beta\,a$. Its probabilistic meaning is immediate from \eqref{eq:fluctuation}: $S_\mu(a)/\Gamma(\mu)=\E\,e^{a\sqrt T}$ for $T\sim\operatorname{Gamma}(\mu,1)$, the moment generating function of $\sqrt T$. The radial variable $t=nu^{2k}$ is the loss measured in units of $1/n$, its law under the population Gibbs weight is $\operatorname{Gamma}(\mu,1)$, and the sample tilts that law by $e^{a\sqrt t}$.

\subsection{The ladder}

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.deriv_fluctuation (i), Grammar.fluctuation_recurrence (ii), Grammar.fluctuation_ode (iii), Grammar.fluctuation_one (iv)
% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_iteratedDeriv (S_{(n+1)/2} = d^n S_{1/2}, regular orbit), fluctuation_half_gaussian ((v) as a Gaussian integral, before the erf normalisation)
% Lean: the erf normalisation in (v) and the Weber form eq:weber are analytic derivations.
\begin{lem}\label{lem:ladder}
For $\mu>0$: (i) $\partial_aS_\mu=S_{\mu+1/2}$; (ii) $S_{\mu+1}(a)=\frac a2S_{\mu+1/2}(a)+\mu S_\mu(a)$; (iii) $S_\mu''=\frac a2S_\mu'+\mu S_\mu$; (iv) $S_1(a)=\frac a2S_{1/2}(a)+1$; (v) $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}\big(1+\operatorname{erf}(a/2)\big)$.
\end{lem}

\begin{proof}
(i) is differentiation under the integral, since $\partial_ae^{a\sqrt t}=\sqrt t\,e^{a\sqrt t}$ raises the power of $t$ by one half. (ii) follows from $\int_0^\infty\frac{d}{dt}\big[t^\mu e^{-t+a\sqrt t}\big]dt=0$, whose integrand is $(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$; (iii) is (ii) rewritten with (i); (iv) is the same computation at $\mu=0$ on $[\varepsilon,T]$ with $\varepsilon\to0$; (v) is the substitution $u=\sqrt t$ and completion of the square.
\end{proof}

Property (i) is the \emph{ladder}: differentiating in the field variable raises the index by one half. Property (iii) is Weber's equation in disguise: under $S_\mu(a)=e^{a^2/8}f(a/\sqrt2)$ it becomes $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $-2\mu$, so that
% Lean: not formalised; Weber substitution and parabolic-cylinder closed form.
\begin{equation}\label{eq:weber}
S_\mu(a)=2^{1-\mu}\Gamma(2\mu)\,e^{a^2/8}\,D_{-2\mu}\big(-a/\sqrt2\big)
\end{equation}
in terms of the standard parabolic cylinder function \citep[\S12.5]{NIST:DLMF}. The operators $b^\dagger=\partial_a$ and $b=2\partial_a-a$ satisfy $[b,b^\dagger]=1$, the defining relation of the Weyl algebra, and act on the fluctuation functions by raising and lowering the index: $b^\dagger S_\mu=S_{\mu+1/2}$ and $bS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>1/2$, the recurrence (ii) being the statement that $b$ lowers. The space $\mathbb C[a]+\operatorname{span}\{S_{(n+1)/2}:n\ge0\}$ is stable under $b$ and $b^\dagger$, and the orbit of $\mu=1/2$, which is the regular case, is distinguished: there $S_{(n+1)/2}=\partial_a^nS_{1/2}$, so every fluctuation function of half-integer index is a derivative of $\sqrt\pi e^{a^2/4}(1+\operatorname{erf}(a/2))$, and modulo the polynomial submodule $S_{1/2}$ is a lowest-weight vector, a vector killed by $b$, from which $b^\dagger$ generates the whole orbit: this is the Fock representation of the Weyl algebra, in which $b^\dagger$ creates and $b$ annihilates. For a singular model with $\mu\notin\frac12\mathbb Z$ there is no lowest weight and the parabolic cylinder function is genuinely needed; the module structure is recorded in \cref{app:fluctuation_facts}. The same recurrence underlies Watanabe's equations of state for the Bayes and Gibbs errors \citep[Thm~5.11]{watanabeAlgebraicGeometryStatistical2009}; we will not need them.

The structural consequence for the expansions is this. Wherever the population theory produces a Gamma function $\Gamma(\mu)$ from a normal integral, the empirical theory produces $S_\mu$ evaluated on the field. Wherever the population theory differentiates the amplitude in a normal direction, the empirical theory also differentiates the factor $e^{\sqrt n u^k\zeta}$, and by the chain rule and \cref{lem:ladder}(i) every derivative of the field brings $S_{\mu+1/2}$, $S_{\mu+1}$, and so on. The corrections therefore involve a finite ladder of fluctuation functions of increasing index multiplied by derivatives of the field, in a pattern fixed by the Leibniz rule. In one variable it reads
% Lean @ d56efc8: Grammar/EmpiricalOneDim.lean: Grammar.SmoothEngine.empOneDimCoeff (def: d^j[eta S_{mu_j}(xi)](0)/(j! 2k)), Grammar.SmoothEngine.empOneDim_expansion, Grammar.SmoothEngine.empOneDimCoeff_one
\begin{equation}\label{eq:one_dim_coefficients}
\int_0^1\eta(u)u^he^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}du\sim\sum_{j\ge0}\frac{\partial_u^j\big[\eta\,S_{\mu_j}(\zeta)\big](0)}{j!\,2k}\,n^{-\mu_j},\qquad\mu_j=\frac{h+j+1}{2k} ,
\end{equation}
so that the $j$-th coefficient is the $j$-th derivative at the origin of the amplitude times the fluctuation function of the field at the $j$-th index: $\eta S_{\mu_0}(\zeta)/2k$, then $(\eta'S_{\mu_1}(\zeta)+\eta\zeta'S_{\mu_1+1/2}(\zeta))/2k$, then $(\eta''S_{\mu_2}+2\eta'\zeta'S_{\mu_2+1/2}+\eta\zeta''S_{\mu_2+1/2}+\eta\zeta'^2S_{\mu_2+1})/(2\cdot2k)$, and so on. This is the one-dimensional form of everything in \cref{sec:empirical}, and it is proved in \cref{app:chart_proofs} by scaling $u=n^{-1/2k}x$ and Taylor-expanding the smooth factor $\eta(u)e^{x^k\zeta(u)}$ in $u$ to finite order with a remainder.

\subsection{Index derivatives and logarithms}

The logarithms of the population expansion arise, in the Mellin picture, from higher-order poles, and in the coefficients they appear as derivatives of $\Gamma$ with respect to its argument. In the empirical theory they are derivatives of $S$ with respect to the index:
% Lean @ d56efc8: Grammar/MellinLogWeights.lean: Grammar.SmoothEngine.mellinMom_pow_mul_exp_eq_iteratedDeriv (log weights as index derivatives)
% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (the x^2y^2 display below)
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

%%%%%%%% sections/09_empirical.tex
\section{The empirical expansion for a fixed sample}\label{sec:empirical}

We distinguish three objects. The \emph{frozen} partition function $Z_N(\eta;\zeta)$ is a deterministic integral with a fixed smooth field $\zeta$ in the exponent and an independent parameter $N\to\infty$; it is of the same kind as the population one, and everything in Part~II goes through with one substitution: the Gamma function in the stratum measures becomes the fluctuation function of the field along the stratum, and derivatives of the field enter the corrections through the ladder. The \emph{empirical diagonal} $Z_n(\eta;\hat\psi_n)$ is the frozen partition function evaluated at $N=n$ and at the chart representative $\hat\psi_n$ of the sample's own field, defined below, which itself depends on $n$; statements about it are obtained from the frozen theorem through the uniformity of its remainder in the field. The \emph{limit} is the same coefficient functional evaluated on the Gaussian field $G$, in \cref{sec:limit}. This section is about the first object, and states what carries over to the second.

\subsection{Root fields}

Pulling the standard form \eqref{eq:standard_form} back along the resolution, on a chart where $K\circ\pi=u^{2k}$ we have $\sqrt{K\circ\pi}=|u^k|$ and
\begin{equation}\label{eq:exponent_chart}
-nK_n\circ\pi=-nu^{2k}+\sqrt n\,|u^k|\,(\psi_n\circ\pi) .
\end{equation}
The standard form supplies a smooth signed-root representative $\xi_n$ with $K_n\circ\pi=u^{2k}-n^{-1/2}u^k\xi_n$ \citep[Main Theorem~6.1]{greybook}; the function multiplying $|u^k|$ in \eqref{eq:exponent_chart} is $\operatorname{sgn}(u^k)\xi_n$, smooth on each orthant of the normal coordinates and in general discontinuous across an interior wall. The natural object is therefore a \emph{root field}: a bounded measurable function $\psi$ on $U$ together with, for every chart and every orthant of its normal coordinates, a smooth representative $\hat\psi$ on the closed box, agreeing with $\psi$ off the walls. Off the walls the representatives are determined; on the walls they record the one-sided limits, which need not agree, and it is the representatives that the coefficients see. Writing $\zeta=\hat\psi$ for the chart representative, the chart integral of $Z_n[f]$ is
\begin{equation}\label{eq:empirical_chart}
Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du ,
\end{equation}
with $\eta$ the localised amplitude of \cref{sec:population} and both $\eta$ and $\zeta$ smooth on the closed cube. Summing the chart integrals of a root field $\psi$ over the charts and orthants with the partition of unity of \cref{sec:population} gives the resolved frozen partition function, written $Z_N[f;\psi]$. For an analytic model $\zeta$ is analytic for each finite $n$; nothing below uses this.

\subsection{The expansion}

% Lean @ d56efc8: Grammar/EmpiricalGeneral.lean: Grammar.SmoothEngine.empIntegral (def), Grammar.SmoothEngine.emp_cutoffExpansion, Grammar.SmoothEngine.empCoeff_unique
% Lean @ d56efc8: Grammar/EmpiricalUniform.lean: Grammar.SmoothEngine.emp_cutoffExpansion_uniform (remainder linear in the FieldJetBound constant)
% Lean @ d56efc8: Grammar/EmpiricalFieldFamilyJets.lean: Grammar.SmoothEngine.FieldJetBound
% Lean @ d56efc8: Grammar/EmpiricalResolvedExpansion.lean: Grammar.SmoothEngine.ResolvedData.SmoothRootField (structure), Grammar.SmoothEngine.ResolvedData.SmoothRootField.empZ_cutoffExpansion, Grammar.SmoothEngine.ResolvedData.SmoothRootField.resolvedCoeff_zero
\begin{thm}[The empirical expansion, fixed sample]\label{thm:empirical_expansion}
Let $\eta,\zeta$ be smooth on a neighbourhood of the closed cube. Then $Z_N(\eta;\zeta)$ has a cutoff expansion in $N$ in the sense of \cref{sec:scale},
\[
Z_N(\eta;\zeta)\sim\sum_{\mu\in Q^{-1}\N}\sum_{q=0}^{d-1}c_{\mu,q}(\eta;\zeta)\,N^{-\mu}(\log N)^q ,
\]
with coefficients independent of the cutoff, and with a remainder constant at cutoff $U$ that is linear in a bound on the normal jets of $\eta\,e^{\tau\zeta}$ up to an order $R(U)$ on the closed cube, with the bound on $\zeta$ fixed. Assembled over the charts of the resolution with the partition of unity of \cref{sec:population}, the empirical partition function of a bounded smooth root field has a cutoff expansion on the common lattice with logarithmic degree at most $d-1$, whose coefficients at zero field are the population coefficients.
\end{thm}

The proof is the proof of \cref{thm:population_expansion} with the field carried along: Fubini along the resonant normal coordinates, the one-dimensional expansion \eqref{eq:one_dim_coefficients} with an explicit constant depending on the slice only through a bound on $\zeta$ and bounds on the normal jets of $\eta e^{\tau\zeta}$, and dominated convergence in the tangential variables (\cref{app:chart_proofs}). The uniformity in the jets is what allows the sample to vary: on the empirical diagonal $N=n$, $\zeta=\hat\psi_n$, the remainder at cutoff $U$ is bounded by the jet bound of the sample's field times $n^{-U}(1+\log n)^{d-1}$, so it is $O_P(n^{-U}(\log n)^{d-1})$ as soon as the jet bounds of the fields are tight, which is the form the statement takes in \cref{sec:limit}.

\subsection{The coefficients}

Three descriptions, each the empirical form of one in \cref{sec:population}.

\paragraph{Geometric: the top logarithmic order.} For an observable admissible at depth $c$, the coefficient of $n^{-\mu}(\log n)^{c-1}$ is the graded formula \eqref{eq:graded} with the amplitude $\eta$ replaced by $\eta\,S_\mu(\zeta)/\Gamma(\mu)$:
% Lean @ d56efc8: Grammar/EmpiricalFaceSumCollapse.lean: Grammar.SmoothEngine.empCoeff_eq_zero_of_deep, Grammar.SmoothEngine.empCoeff_eq_faceSum_top, Grammar.SmoothEngine.empCoeff_top_eq_smoothCoeff
% Lean @ d56efc8: Grammar/EmpiricalResolvedStratumFormula.lean: Grammar.SmoothEngine.ResolvedData.SmoothRootField.resolvedCoeff_eq_empStratumSum
\begin{equation}\label{eq:empirical_graded}
c_{\mu,c-1}(\eta;\zeta)=\sum_{|J|=c}\frac{\prod_{j\in J}(2k_j)^{-1}}{(c-1)!\prod_{j\in J}\alpha_j!}\int_{u_J=0}\partial^\alpha_J\big[\eta\,S_\mu(\zeta)\big](0_J,w)\;w^{h}\big(w^{2k}\big)^{-\mu}\,dw .
\end{equation}
In resolved form: the normal jet of order $\alpha$ of $(f\circ\pi)\,S_\mu(\hat\psi)$ along the exact stratum $S^\mu_c$, integrated against the chart residue data of \cref{sec:residue}, which at zero order is the weighted logarithmic residue $\Rres^\mu_c$ and at positive orders is the differentiated face density of \eqref{eq:graded}; the sum is over the orthants, each with its own representative $\hat\psi$. The geometry is that of the population expansion; the sample enters as a pointwise reweighting of the residue density by the fluctuation function of the standardised field, together with its normal derivatives, which raise the index by halves. At the leading pair $(\lambda,m)$, for $f$ admissible at depth $m$,
% Lean @ d56efc8: Grammar/EmpiricalResolvedLeading.lean: Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ, Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ_eq_integral
% Lean @ d56efc8: Grammar/EmpiricalStratumMeasure.lean: Grammar.SmoothEngine.ResolvedData.RootField (structure), Grammar.SmoothEngine.ResolvedData.empiricalStratumMeasure
\begin{equation}\label{eq:empirical_leading}
N^{\lambda}(\log N)^{-(m-1)}Z_N[f;\psi]\longrightarrow\frac1{(m-1)!}\sum_{\text{orthants}}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi)\,d\Rres^{\lambda,\pm}_m ,
\end{equation}
where $\Rres^{\lambda,\pm}_m$ are the one-sided residue densities whose sum is $\Rres^\lambda_m$; when the representatives agree on the two sides of every wall this collapses to $\frac1{(m-1)!}\int(f\circ\pi)S_\lambda(\hat\psi)\,d\Rres^\lambda_m$, and at $\psi=0$ it is \cref{thm:leading}. The leading empirical coefficient depends on the field only through its values on the leading stratum: the posterior at leading order lives on the deepest exact stratum and is the population stratum measure reweighted, orthant by orthant, by $S_\lambda(\hat\psi)$. And the reweighting is by a positive function, so the positivity and finiteness statements of \cref{thm:leading} survive, with $S_\lambda(\hat\psi)\le S_\lambda(\|\psi\|_\infty)$ giving domination by a multiple of the population measure.

\paragraph{Analytic: the fluctuation zeta function.} The Mellin transform of the frozen partition function in $n$ is, by \eqref{eq:one_variable_field} applied pointwise,
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZeta.lean: mellin_frozenEvidenceObs_eq
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaPolar.lean: fluctuationZeta_eq_mellinContinuation, isFrozenCoeff_polarCoeff_unique
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/FluctuationZetaStrip.lean: mellin_frozenEvidenceObs_eq_of_bounded_std, fluctuationZeta_eq_mellinContinuation_of_bounded_std, isFrozenCoeff_polarCoeff_unique_of_bounded (strip hypotheses derived)
% Lean @ d56efc8: Grammar/MellinRegularization.lean: Grammar.mellin_eq_mellin_cutoffRemainderFun_add_principalParts
% Lean @ d56efc8: Grammar/PrincipalPartUniqueness.lean: Grammar.polarCoeff_unique
\begin{equation}\label{eq:fluctuation_zeta}
\mathcal Z_f(s;\psi)=\int_0^\infty N^{s-1}Z_N[f;\psi]\,dN=\int_W f\,K^{-s}\,S_s(\psi)\,\varphi\,dw ,
\end{equation}
Watanabe's zeta function with the Gamma factor replaced, inside the integral, by the fluctuation function of the standardised field, at a complex index. Every coefficient of \cref{thm:empirical_expansion}, at every logarithmic order, is a Laurent coefficient of this function at a pole in $\operatorname{Re}s>0$, exactly as in \eqref{eq:laurent} (the poles of $S_s$ at $0,-\tfrac12,-1,\dots$ record the small-$N$ behaviour): $c_{\mu,q}=\frac{(-1)^{q+1}}{q!}[(s-\mu)^{-(q+1)}]\mathcal Z_f(s;\psi)$. This is the definition from which the geometric formula is an evaluation, and it is the description that covers the lower logarithmic orders at ties, where no closed geometric formula of the form \eqref{eq:empirical_graded} exists: there the index derivatives $\partial_\nu^\ell S_\nu(\zeta)$ of \cref{sec:fluctuation} carry the logarithms, in Taylor-subtracted chart expressions.

\paragraph{Algebraic: the generating identity.} Every empirical coefficient is a convergent series of population coefficients with powers of the field inserted into the observable:
% Lean @ d56efc8: Grammar/EmpiricalGeneratingIdentity.lean: Grammar.SmoothEngine.hasSum_empCoeff_population
\begin{equation}\label{eq:generating}
c_{\mu,q}(\eta;\zeta)=\sum_{r\ge0}\frac1{r!}\,c^{\mathrm{pop}}_{\mu+r/2,\,q}\big(\eta\,(u^k\zeta)^r\big) ,
\end{equation}
unconditionally convergent. The half-integer shift of the exponent is the bookkeeping for the $\sqrt n$ in front of the field: in the radial variable $t=nu^{2k}$ the term $(\sqrt t\,\zeta)^r/r!$ of the exponential is the insertion $(u^k\zeta)^r$ against the Gamma law at index $\mu+r/2$, and $S_\mu(a)=\sum_ra^r\Gamma(\mu+r/2)/r!$ is the same identity at a single point. The proof is by truncation of the exponential and never exchanges the series with the integral, and each term depends on the field only through its jet of a fixed order determined by $(h,k,\mu)$. The identity says that the population theory determines the empirical one: the sample enters through the population coefficients of the modified observables $f\,H^r$, $H=\sqrt K\,\psi$, with the exponent climbing by halves.

\subsection{What enters at the first orders}\label{sec:first_orders}

The abstract descriptions become concrete in the two situations of \cref{sec:tiers}.

\paragraph{One resonant coordinate.} If at $\mu$ only the wall $E_{i_0}$ resonates, with normal order $\alpha$, then, writing $u$ for the normal coordinate of $E_{i_0}$, $w$ for the remaining coordinates, $w^{h_L}=\prod_{i\ne i_0}w_i^{h_i}$ and $p(w)=w^{2k_L}=\prod_{i\ne i_0}w_i^{2k_i}$ as in \cref{app:chart_proofs},
% Lean: not formalised; closed finite-part form for alpha >= 2 past another wall's exponent; see sec:formalisation, first bullet.
\begin{equation}\label{eq:empirical_tier2}
c_{\mu,0}(\eta;\zeta)=\frac{1}{2k_{i_0}\,\alpha!}\ \mathrm{FP}\!\int_{u=0}\partial_u^\alpha\big[\eta\,S_\mu(\zeta)\big](0,w)\;w^{h_L}\big(w^{2k_L}\big)^{-\mu}\,dw ,
\end{equation}
with the finite part needed only past the exponents of the other walls. Under the generic hypothesis that $\mu_1=\lambda+1/2k_{i_0}$ is below every other exponent, the two leading coefficients are plain integrals over the face, valid for all smooth $\eta,\zeta$ with no admissibility hypothesis:
% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.genericFaceCoeff (def), Grammar.SmoothEngine.empCoeff_generic, Grammar.SmoothEngine.empCoeff_firstCorrection, Grammar.SmoothEngine.tendsto_firstCorrection
\begin{align}
c_{\lambda,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\lambda}\,\eta(0,w)\,S_\lambda\big(\zeta(0,w)\big)\,dw,\label{eq:c_lambda}\\
c_{\mu_1,0}(\eta;\zeta)&=\frac1{2k_{i_0}}\int w^{h_L}p(w)^{-\mu_1}\Big[\partial_u\eta(0,w)\,S_{\mu_1}\big(\zeta(0,w)\big)+\eta(0,w)\,\partial_u\zeta(0,w)\,S_{\mu_1+1/2}\big(\zeta(0,w)\big)\Big]dw,\label{eq:c_mu1}
\end{align}
and every other coefficient at a lattice exponent $\le\mu_1$ vanishes. The first correction is the one-dimensional coefficient $C_1$ of \eqref{eq:one_dim_coefficients} for the slice $(\eta(\cdot,w),\zeta(\cdot,w))$, integrated over the face against the residue density. Only the values and first normal derivatives of the amplitude and of the field on the face enter; the field's derivative comes with the raised index $\mu_1+\frac12$. In \cref{ex:mixed} this gives the leading term at $n^{-1/6}$ and the first correction at $n^{-1/3}$ as integrals over the wall $\{y=0\}$ against $x^{-1/3}dx$ and $x^{-2/3}dx$, and the second correction at $n^{-1/2}$ is the first place where a logarithm and the other wall appear.

% Lean @ d56efc8: Grammar/LogExampleTwoDim.lean: Grammar.SmoothEngine.tendsto_logExample (constant amplitude and constant field a)
% Lean: the nonconstant-amplitude tie formulas are derivations.
\paragraph{Ties.} At a tie of $c$ walls the top logarithm is \eqref{eq:empirical_graded}, and the lower ones follow the Laurent computation of \cref{sec:tiers} with $\Gamma$ replaced by $S$. For \cref{ex:planes} at $\mu=1/2$, with $\eta_s=\eta\,S_s(\zeta)$ evaluated on a slice $z=$ const,
\[
c_{1/2,1}=\frac{\eta(0,0)S_{1/2}(\zeta(0,0))}4,\qquad c_{1/2,0}=-\frac{\eta(0,0)\,\partial_\nu S_\nu(\zeta(0,0))|_{1/2}}4+\frac12\int_0^1\frac{\eta_{1/2}(x,0)-\eta_{1/2}(0,0)}x\,dx+\frac12\int_0^1\frac{\eta_{1/2}(0,y)-\eta_{1/2}(0,0)}y\,dy
\]
per quadrant and per $z$: the coefficient of $n^{-1/2}\log n$ is the fluctuation function of the field on the axis, and the coefficient of $n^{-1/2}$ is its index derivative there plus finite parts of $\eta S_{1/2}(\zeta)$ along the two planes. Summing the four quadrants, each with its own representative of the field, and integrating over $z$ gives the coefficients for this example: the sample enters the leading term through the values of the field on the axis, and the first correction through its values on the planes as well.

% Lean @ d56efc8: Grammar/EmpiricalResolvedContinuity.lean: Grammar.SmoothEngine.ResolvedData.exists_resolvedCoeff_top_bound (locally Lipschitz in the chart jets)
\subsection{How much of the field is seen}

Each coefficient depends on the field only through finitely many of its normal jets on the closed cube, of an order fixed by $\mu$: the values on the resonant faces for the leading term, first derivatives for the first correction, and so on, exactly as for the observable in \cref{thm:jet}. For the top logarithmic coefficient at each exponent, on admissible observables, this dependence is continuous and locally Lipschitz on jet balls: if two fields have jets of the relevant order within $\delta$ of each other on the closed cube, the corresponding coefficients differ by at most a constant times $\delta$. Together with the uniformity of the remainder in \cref{thm:empirical_expansion} this is what the passage to the Gaussian limit needs for those coefficients.

%%%%%%%% sections/10_limit.tex
\section{The limit field}\label{sec:limit}

For a fixed sample the expansion of $Z_n[f]$ is deterministic. Its coefficients are random through the field, and the question of how they behave as the sample grows is a question about the field alone, since the geometry does not move. This section records what is known: the field converges to a Gaussian process, the coefficients converge with it, and averaging over the sample can be carried out for the fluctuation function at a single point, with a threshold.

% Lean @ d56efc8: Grammar/EmpiricalCoeffDistribution.lean: Grammar.SmoothEngine.ResolvedData.tendstoInDistribution_resolvedCoeff_top, Grammar.SmoothEngine.ResolvedData.realizableJet
% Lean @ d56efc8: Grammar/EmpiricalBranchJets.lean: Grammar.SmoothEngine.ResolvedData.coeffOnJets
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/ChartLaw.lean: tendstoInDistribution_chartField
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/DownstairsFidi.lean: tendstoInDistribution_empDeformation_fidi
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/LeadingLaw.lean: tendstoInDistribution_evidenceObs_div_leading
\subsection{Convergence in law of the coefficients}

By Watanabe's theorem \citep[Thm~6.2]{greybook} the signed-root process $\xi_n$ of \cref{sec:setting} converges in law, as $n\to\infty$, to a centred Gaussian process $G$ on the resolution with covariance $\Cov_X\big(a(X,u),a(X,u')\big)$, where $a$ is the function of the standard form: in a chart with $K\circ\pi=u^{2k}$ it is defined by $\log\big(q(x)/p(x\mid\pi(u))\big)=u^k\,a(x,u)$, so that $\E_X\,a(X,u)=u^k$ and $\psi_n\circ\pi=\pm n^{-1/2}\sum_i\big(u^k-a(x_i,u)\big)$ with the sign of $u^k$; the orthantwise representatives of $\psi_n$ and of its limit are $\pm\xi_n$ and $\pm G$ with that sign, so their covariance carries the factor $\operatorname{sgn}(u^k)\operatorname{sgn}(u'^k)$. This convergence is a statement about the process as a function on the resolved manifold.

The top coefficients of \cref{thm:empirical_expansion}, on admissible observables, depend on the field only through finitely many normal jets on the chart cubes, continuously and locally Lipschitz (\cref{sec:empirical}). Hence, if the vector of jets of $\hat\psi_n$ of the relevant order, taken jointly over all charts and orthants, converges in law, these coefficients converge in law to the same functionals evaluated on the jets of $G$, and by the same continuity jointly for any finite set of exponents (the formal statement is for one exponent and takes the limiting jets to be jets of smooth root fields, which is the case when $G$ has smooth orthantwise representatives); and since the remainder of the expansion at cutoff $U$ is $O_P(n^{-U}(\log n)^{d-1})$ under tightness of the jet bounds, the truncation of $Z_n[f]$ at any cutoff is accurate to that order in probability. In particular
\[
n^{\lambda}(\log n)^{-(m-1)}Z_n[f]\ \Longrightarrow\ \frac1{(m-1)!}\sum_{\text{orthants}}\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat G)\,d\Rres^{\lambda,\pm}_m ,
\]
the leading coefficient evaluated on the Gaussian field along the leading stratum, with $\hat G$ its one-sided limits on the walls, for $f$ admissible at depth $m$, and the analogous statements hold for the top coefficient at every retained exponent. The convergence of the face jets of the empirical process is a statement about the sample and the model, a functional central limit theorem for finitely many derivatives of $\psi_n$ on the resolution; it is the hypothesis under which the limit theorems are proved, and it is not derived from the geometry. For the leading coefficient only the values on the leading stratum are needed, and there the convergence is Watanabe's theorem itself.

\subsection{Averaging over the sample: the fluctuation function of a Gaussian}

For a single centred Gaussian value $a\sim N(0,v)$, Fubini gives
% Lean @ d56efc8: Grammar/GaussianFluctuationScalar.lean: Grammar.integral_fluctuation_gaussianReal'
% Lean @ d56efc8: Grammar/GaussianThreshold.lean: Grammar.lintegral_gaussMomentJ_lt_top_iff (finite iff beta v < 2)
% Lean @ d56efc8: Grammar/WickEnvelope.lean: Grammar.integral_empCoeff_gaussian_wick_of_exp_moment (the Wick series below)
\begin{equation}\label{eq:gaussian_average}
\E\,S_\lambda(a)=\int_0^\infty t^{\lambda-1}e^{-t}\,\E e^{a\sqrt t}\,dt=\int_0^\infty t^{\lambda-1}e^{-(1-v/2)t}\,dt=\Gamma(\lambda)\Big(1-\frac v2\Big)^{-\lambda} ,
\end{equation}
finite exactly when $v<2$, and $+\infty$ otherwise. First, the expected leading coefficient of $Z_n[f]$ in the Gaussian limit is the population coefficient with the amplitude reweighted by $(1-v(x)/2)^{-\lambda}$ along the leading stratum, where $v(x)$ is the variance of the limit field at the point $x$: averaging and expanding do not commute, and $\E\,C(G)\ne C(0)$ even though $\E\,G=0$, because the coefficients are nonlinear in the field through the fluctuation function. Second, the Gaussian limiting leading coefficient need not be integrable: if the variance of the limit field exceeds $2$ on a set of positive residue measure of the leading stratum, its expectation is infinite. This is a statement about the limit object and about the failure of uniform integrability, not about finite samples: for the renormalised $K_n$ of \cref{sec:setting} one has $\E\,e^{-nK_n(w)}=\prod_i\E_q[p(x_i\mid w)/q(x_i)]=1$, so $\E\,Z_n[1]=\int\varphi$ exactly, and the expectation of the finite-sample evidence cannot be exchanged with the asymptotic limit. In the generating identity \eqref{eq:generating} the same threshold appears as the radius of convergence of the Wick series $\sum_j(2^jj!)^{-1}c^{\mathrm{pop}}_{\mu+j,q}(\eta\,W^j)$, obtained by taking expectations term by term, with $W(u)$ the variance of the scaled field $u^k\zeta(u)$ at each point of the cube: odd terms vanish, even ones contribute $(2j)!/(2^jj!)$ times the variance power, and the sum is $e^{W/2}$ distributed over the shifted exponents. The series converges under an exponential moment $\E\,e^{\delta\|J_R\zeta\|^2}<\infty$ with $\delta>\frac14$, where $J_R\zeta$ is the vector of derivatives of $\zeta$ of order at most $R$ on the cube and $R$ is fixed by $\mu$, a sufficient uniform-integrability condition that is considerably stronger than the pointwise threshold $v<2$ on the variance $v$ of $\zeta$ itself: the averaged frozen integrand has phase $-nu^{2k}+nW(u)/2=-nu^{2k}(1-v(u)/2)$, so the threshold is on $v$, not on $W=u^{2k}v$, which vanishes on the walls.

None of this affects the posterior. The posterior expectation is a ratio, bounded by $\|f\|_\infty$ for every sample, and its averaged behaviour is a different question, taken up in \cref{sec:averaging}. The threshold concerns the unnormalised evidence only.

\subsection{What is a hypothesis}

The picture of this section rests on three inputs of different standing. That the top coefficients are continuous functionals of finitely many jets of the field on admissible observables, and that the remainder is uniform on jet balls, are theorems of the smooth theory. That the empirical process converges to a Gaussian field on the resolution is Watanabe's theorem, consumed as such. That the finitely many normal derivatives of the empirical process on the faces converge jointly in law, which is what the convergence of the subleading coefficients needs, is a hypothesis about the model, plausible under the moment conditions of the standard form but not derived here; for the leading coefficient it is not needed.

%%%%%%%% sections/11_posterior.tex
\section{Posterior expectations}\label{sec:posterior}

The posterior expectation of an observable is the quotient $Z_n[f]/Z_n[1]$ of two expansions on the same lattice. This section says what the quotient looks like, for a fixed sample and to all orders, and what its leading term is. The organising fact is that nothing new enters: every coefficient of the posterior expectation is a rational function of the coefficients of $Z_n[f]$ and $Z_n[1]$, and all the geometry and all the data are already in those.

\subsection{Blocks and the quotient}

Write $\ell=\log n$ and $x=n^{-1/Q}$. Collecting the logarithmic powers at a fixed exponent $\mu=j/Q$ into one polynomial gives the \emph{block}
\[
B_j(\ell)=\sum_{q\le d-1}c_{j/Q,q}\,\ell^q,\qquad Z_n\sim\sum_jB_j(\log n)\,n^{-j/Q}=\sum_jB_j(\ell)\,x^j ,
\]
so that an expansion in our scale is a power series in $x$ with coefficients polynomial in $\ell$. Blocks rather than individual coefficients are the right unit for division: the inverse of the leading block $B_0(\ell)$ of the denominator is a rational function of $\ell$, not a polynomial. The quotient of two expansions is therefore a power series in $x$ over the field $\R(\ell)$ of rational functions in $\log n$, an enlargement of the scale of \cref{sec:scale} in which the logarithmic factors need no longer be polynomial, and its coefficients, the \emph{quotient blocks}
\begin{equation}\label{eq:quotient_blocks}
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) ,
\end{equation}
are computed by the ordinary recursion for the quotient of power series, with $A_j,B_j$ the blocks of numerator and denominator counted from the first exponent at which the denominator is nonzero.

% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO'
% Lean @ d56efc8: Grammar/QuotientBlocks.lean: Grammar.quotientBlocks (def), Grammar.sum_mul_quotientBlocks
% Lean (bridge workspace lean/grammar-greybook-bridge @ 17c058b): Bridge/PosteriorAllOrders.lean: boundedInProbSeq_posteriorMean_allOrders (in probability at the diagonal)
\begin{thm}[Posterior expectation, fixed sample, all orders]\label{thm:posterior_quotient}
Let $A_j$ and $B_j$ be the blocks of the expansions of $Z_n[f]$ and $Z_n[1]$ from \cref{thm:empirical_expansion}, counted from the first exponent $\lambda$ of $Z_n[1]$ (both systems vanish below it, since $|Z_n[f]|\le\|f\|_\infty Z_n[1]$), and suppose the leading block $B_0$ is a nonzero polynomial, as it is when the prior is positive somewhere on the leading stratum. Then for every $J\ge1$,
\[
\frac{Z_n[f]}{Z_n[1]}=\sum_{j<J}R_j(\log n)\,n^{-j/Q}+O\big(n^{-J/Q}(1+\log n)^{(d-1)(J+1)}\big) ,
\]
with $R_j$ the quotient blocks \eqref{eq:quotient_blocks}, kept exact as rational functions of $\log n$. Each $R_j$ may be expanded in inverse powers of $\log n$ to any order if a pure power-logarithm form is wanted.
\end{thm}

The remainder is $O$ and not $o$ at that scale: the omitted block survives at exactly the order of the bound. The theorem is deterministic algebra over the two expansions, and its content is the statement that nothing else is true at this level: the quotient of two asymptotic expansions is the formal quotient, and the terms obtained by expanding $1/Z_n[1]$ are exactly the terms of the recursion.

\subsection{The source and the connected coefficients}

The cleaner organisation of the higher posterior moments is through a source. For bounded smooth $f$,
% Lean @ d56efc8: Grammar/SourceLog.lean: Grammar.logOf, Grammar.varianceBlocks, Grammar.coeff_two_mul_coeff_two_logOf_blocks
% Lean @ d56efc8: Grammar/PosteriorVarianceExpansion.lean: Grammar.emp_variance_isBigO (posterior variance to all orders)
\begin{equation}\label{eq:source}
\partial_\varepsilon\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f]}{Z_n[1]},\qquad \partial_\varepsilon^2\log\frac{Z_n[e^{\varepsilon f}]}{Z_n[1]}\Big|_{\varepsilon=0}=\frac{Z_n[f^2]}{Z_n[1]}-\Big(\frac{Z_n[f]}{Z_n[1]}\Big)^2 ,
\end{equation}
and in general the $r$-th derivative is the $r$-th posterior cumulant of $f$. Anchoring the logarithm at $Z_n[1]$ makes it a formal logarithm of a series with constant term one, computable by a finite formula, and fixing a source order $R$ makes only the finitely many expansions of $Z_n[f^r]$, $r\le R$, enter. Writing $m_r$ for the quotient-block series of $Z_n[f^r]/Z_n[1]$, the \emph{connected coefficients} $\kappa_r=[\varepsilon^r/r!]\log\sum_rm_r\varepsilon^r/r!$ satisfy
\[
\kappa_1=m_1,\qquad\kappa_{r+1}=m_{r+1}-\sum_{i=0}^{r-1}\binom ri\kappa_{i+1}m_{r-i} ,
\]
with Cauchy products in $x$; at the level of blocks, with $q^{f}(j)$ the quotient blocks $R_j$ of $Z_n[f]/Z_n[1]$, $\kappa_2(j)=q^{f^2}(j)-\sum_{i\le j}q^f(i)q^f(j-i)$ is the all-orders expansion of the posterior variance. Connected means connected in the source variable; the result is that every posterior cumulant is a universal polynomial in the quotient blocks, and the quotient blocks are the only new objects. The posterior variance is a susceptibility in the sense of \citet{baker2025structuralinferenceinterpretingsmall}: it is the response of $\E[f\mid\Dn]$ to the tilt of the posterior by $e^{\varepsilon f}$, and for a general perturbation of the data the response is the posterior covariance of $f$ with the perturbing score, again a connected coefficient of two observables. This is the point of contact between the expansion and those measurements.

\subsection{The leading term}

At leading order the quotient reduces to the ratio of leading blocks, and the three cases of \cref{sec:population_posterior} recur with the fluctuation function inserted. Let $(\lambda,m)$ be the leading pair, assume $D_{m+1}=\varnothing$ so that the denominator's leading block is the reweighted stratum measure of $1$, and write the field frozen and the orthantwise representatives agreeing across walls, so that the reweighting is by a single function on the stratum.

\begin{itemize}
\item \emph{Generic observable.} If $f\circ\pi$ does not vanish identically on $S^\lambda_m$,
% Lean @ d56efc8: Grammar/EmpiricalResolvedLeading.lean: Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ_eq_integral (numerator and denominator)
% Lean @ d56efc8: Grammar/MomentKernel.lean: HasLeadingTerm.div
% Lean: the E[K | D_n] display below is a derivation.
\begin{equation}\label{eq:leading_posterior}
\E[f\mid\Dn]\longrightarrow\langle f\rangle_{\hat\psi_n}:=\frac{\int_{S^\lambda_m}(f\circ\pi)\,S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m}{\int_{S^\lambda_m}S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m} ,
\end{equation}
to be read as three statements: for a frozen field $\psi$, $Z_N[f;\psi]/Z_N[1;\psi]\to\langle f\rangle_\psi$ as $N\to\infty$; on the empirical diagonal, $\E[f\mid\Dn]-\langle f\rangle_{\hat\psi_n}\to0$ in probability, by the uniform remainder, when the denominator's leading coefficient stays bounded away from zero; and in the Gaussian limit $\E[f\mid\Dn]\Rightarrow\langle f\rangle_G$ under the convergence of \cref{sec:limit}. The arrow in \eqref{eq:leading_posterior} is shorthand for these. The posterior at leading order is the residue measure on the leading stratum reweighted by the fluctuation function of the field at each point. When the leading measure is carried by a single point, or more generally when $f\circ\pi$ is constant on its support, the reweighting cancels and the leading value is $f$ at that point regardless of the field: at a point-like singularity the data cannot move the leading posterior expectation, though it can move the first correction. When the leading stratum has positive dimension the sample redistributes posterior mass along it according to $S_\lambda(\hat\psi_n)$, and since $S_\lambda$ is increasing this favours the parts of the stratum where the empirical loss dips below the population loss.
\item \emph{Partially vanishing.} If $f\circ\pi$ vanishes on $S^\lambda_m$ and $m'-1$ is the largest logarithmic degree at $\lambda$ with a nonzero coefficient, $\E[f\mid\Dn]\sim D_n(\log n)^{-(m-m')}$ with $D_n$ the ratio of the corresponding reweighted residue data.
\item \emph{Fully vanishing.} If $f\circ\pi$ vanishes along every wall of exponent $\lambda$ the expectation decays as a power when some block of $Z_n[f]$ is nonzero, with a random constant given by the ratio of the first nonvanishing block of $Z_n[f]$ to the leading block of $Z_n[1]$. For $f=K$ the shift is by exactly one, and the fluctuation factors do not cancel: since $K\circ\pi=u^{2k}$ is the radial variable $t/n$, the leading value is
\[
\E[K\mid\Dn]\sim\frac1n\,\frac{\int_{S^\lambda_m}S_{\lambda+1}(\hat\psi_n)\,d\Rres^\lambda_m}{\int_{S^\lambda_m}S_\lambda(\hat\psi_n)\,d\Rres^\lambda_m} ,
\]
which reduces to $\lambda/n$ at zero field by $S_{\lambda+1}(0)=\lambda\Gamma(\lambda)$; in the regular one-dimensional case $K=x^2$ on $[-1,1]$ with a constant signed-root field $a$, so that the two orthants carry $\pm a$, it is $(\frac12+\frac{a^2}4)/n$, the odd terms cancelling between the sides; on a single one-sided orthant the ratio $S_{3/2}(a)/S_{1/2}(a)$ is $\frac12+\frac{a^2}4+\frac a{2S_{1/2}(a)}$.
\end{itemize}

\subsection{Tied strata and the two-site phenomenon}

When the leading stratum has several components of the same depth and exponent, the sample decides how the posterior mass is distributed between them, and the outcome has a definite sign. The simplest case is two points carrying population masses $p$ and $1-p$ and posterior weights $U=S_\lambda(a_1)$, $V=S_\lambda(a_2)$, so that the posterior mass of the first point is $Q_p=pU/(pU+(1-p)V)$. If the pair $(U,V)$ is exchangeable, which is the case when the two field values form a jointly centred Gaussian pair with equal variances,
% Lean @ d56efc8: Grammar/TwoSiteExchange.lean: Grammar.twoSitePosteriorMass, Grammar.twoSiteKernel, Grammar.integral_twoSitePosteriorMass_sub, Grammar.integral_twoSitePosteriorMass_mem
\begin{equation}\label{eq:two_site}
\E\,Q_p-p=\frac{p(1-p)(1-2p)}2\,\E\Big[\frac{(U-V)^2}{(pU+(1-p)V)((1-p)U+pV)}\Big],\qquad \E\,Q_p\in\big[\min(p,\tfrac12),\max(p,\tfrac12)\big] .
\end{equation}
Here $0<p<1$, the weights are positive and measurable, and no moments of $U,V$ are needed, since the kernel is bounded by $1/\min(p,1-p)^2$. Exchangeable disorder moves the averaged posterior mass toward equal allocation: a minority component gains, a majority component loses, and the displacement is strict as soon as $p\ne\frac12$ and $U\ne V$ with positive probability. Positivity of an observable does not make its averaged posterior expectation move in a fixed direction; the indicator of a majority component decreases. And $\E[Z_n[f]/Z_n[1]]\ne\E Z_n[f]/\E Z_n[1]$ already in the simplest case, which is the concrete reason the averaged posterior is treated separately in \cref{sec:averaging}.

\subsection{Wall-crossing with data}

The candidate exponents and maximal logarithmic degrees of the posterior expansion are determined by the vanishing orders of $f$ along the walls, exactly as in the population case, and they do not depend on the sample. What the sample changes is the coefficients, at leading order only through the values of the field on the leading strata, and a sample-dependent cancellation can remove a candidate term for particular fields. As $f$ varies in a family the candidate exponent of $\E[f\mid\Dn]$ jumps at the same walls as that of $\E_\infty[f]$, by the same rational amounts. The discrete signal of \cref{sec:population_posterior} survives the passage to data; the continuous part, the coefficients, acquires a random component with the structure described in the next section.

%%%%%%%% sections/12_averaging.tex
\section{Averaging over the sample: a conditional compact-base Gaussian model}\label{sec:averaging}

The results so far hold sample by sample. The average of a posterior expectation over the sample is a different object, and this short section records what is known about it at leading order, what its exact structure is, and where the theory currently stops. Throughout the section the base is a compact metric space $S$ carrying a finite nonzero Borel measure $\rho$, the field $G$ is a centred Gaussian random element of $C(S,\R)$ with continuous positive semidefinite covariance kernel $\mathcal C$ and $\E\|G\|_\infty^2<\infty$, and the observables are continuous on $S$. The exact leading stratum of \cref{sec:population} is in general neither compact nor single-sheeted, so the identification of the geometric leading object with this model, described at the end of the section, is conditional.

\subsection{The limit posterior}

At leading order the posterior lives on the leading stratum $S=S^\lambda_m$, and by \eqref{eq:leading_posterior} the posterior expectation is the normalised $S_\lambda$-reweighting of the residue measure by the field along $S$. Passing to the Gaussian limit $G$ of the field, and keeping the radial variable $t=nK\circ\pi$ as a coordinate, the limit object is the random probability measure
% Lean @ d56efc8: Grammar/QuenchedSource.lean: Grammar.compactAvg (= <f>_g), Grammar.logTilt, Grammar.compactVar
% Lean @ d56efc8: Grammar/CompactBaseQuantise.lean: Grammar.compactD (= D(g))
% Lean @ d56efc8: Grammar/GibbsJoint.lean: Grammar.gibbsJoint (= mu_g)
\begin{equation}\label{eq:gibbs}
\mu_G(dx\,dt)=\frac{t^{\lambda-1}e^{-t+G(x)\sqrt t}}{D(G)}\,d\rho(x)\,dt,\qquad D(g)=\int_SS_\lambda(g(x))\,d\rho(x) ,
\end{equation}
on $S\times(0,\infty)$, where in the intended application $S$ is a compact, orthant-labelled version of the leading stratum and $\rho$ the corresponding residue density. Its $S$-marginal has the $S_\lambda(G)$-weights and gives $\langle f\rangle_G$ for observables seen through their values on $S$; the radial variable is what makes derivatives in the field precise, the tilt in direction $h$ being the observable $\sqrt t\,h(x)$. In this form the limit posterior is a Gibbs measure with a Gaussian random Hamiltonian, and the tools of that subject apply. In particular we use replicas: independent copies $(x_1,t_1),(x_2,t_2),\dots$ drawn from the same realisation $\mu_g$, so that a product of Gibbs averages becomes a single average $\E^{\otimes r}_{\mu_g}$ over the product measure.

\subsection{Three exact identities}

Let $\mathcal C$ be the covariance kernel of $G$ on $S$ and $\langle\phi\sqrt t\rangle_g=\int\phi\,S_{\lambda+1/2}(g)\,d\rho/D(g)$ the radial-moment weighted integral.

\begin{enumerate}
% Lean @ d56efc8: Grammar/PosteriorFrechet.lean: Grammar.posteriorDeriv, Grammar.hasFDerivAt_compactAvg
\item \emph{Fr\'echet differentiability.} $g\mapsto\langle f\rangle_g$ is differentiable on $C(S,\R)$ with the sup norm ($S$ compact), with derivative $D\langle f\rangle_g[h]=\langle f\,\sqrt t\,h\rangle_g-\langle f\rangle_g\langle\sqrt t\,h\rangle_g=\Cov_{\mu_g}(f,\sqrt t\,h)$, by the ladder $\partial_aS_\lambda=S_{\lambda+1/2}$.
% Lean @ d56efc8: Grammar/CompactBaseStein.lean: Grammar.compactSqrtTimeMoment, Grammar.GaussianField.integral_eval_mul_compactAvg
% Lean @ d56efc8: Grammar/CompactBaseFinite.lean: Grammar.GaussianField (structure: measurable evaluations, E||G||^2 < oo, Gaussian fidis with kernel matrix)
% Lean @ d56efc8: Grammar/CompactBaseKernel.lean: Grammar.PSDKernel
\item \emph{Stein's identity.} For every $x_0\in S$,
\[
\E\big[G(x_0)\langle f\rangle_G\big]=\E\big[\langle f\,\mathcal C(x_0,\cdot)\sqrt t\rangle_G-\langle f\rangle_G\langle\mathcal C(x_0,\cdot)\sqrt t\rangle_G\big] ,
\]
Gaussian integration by parts on the field, which with two independent replicas of $\mu_G$ reads $\E\langle f(x_1)(\sqrt{t_1}\mathcal C(x_0,x_1)-\sqrt{t_2}\mathcal C(x_0,x_2))\rangle^{\otimes2}_G$.
\item \emph{Covariance interpolation.} With $G_s=\sqrt sG$,
% Lean @ d56efc8: Grammar/CompactBaseResponse.lean: Grammar.compactMeanResponse (= H_f), Grammar.GaussianField.integral_compactAvg_eq, Grammar.abs_compactMeanResponse_le
% Lean @ d56efc8: Grammar/GibbsJointResponse.lean: Grammar.compactMeanResponse_eq_replica (three-replica form)
\begin{equation}\label{eq:interpolation}
\E\langle f\rangle_G=\frac{\rho(f)}{\rho(S)}+\int_0^1\E\,H_f(\sqrt s\,G)\,ds,\qquad H_f(g)=\frac12\,\E^{\otimes3}_{\mu_g}\Big[(f(x_1)-f(x_2))\big(t_1\mathcal C(x_1,x_1)-2\sqrt{t_1t_3}\,\mathcal C(x_1,x_3)\big)\Big] ,
\end{equation}
with $\rho(f)=\int_Sf\,d\rho$, and $|H_f(g)|\le5\|f\|_\infty c\,(2\lambda+\tfrac14)(1+\|g\|_\infty^2)$ when $\mathcal C\le c$ on the diagonal. The averaged posterior expectation differs from the zero-field value, the population posterior expectation on the leading stratum, by an integral over the covariance amplitude of a three-replica response, and only the second moment of $\|G\|_\infty$ enters.
\end{enumerate}

% Lean @ d56efc8: Grammar/InverseEvidence.lean: Grammar.inv_compactD_le, Grammar.integrable_inv_compactD_rpow_of_isGaussian
% Lean @ d56efc8: Grammar/QuenchedSource.lean: Grammar.quenchedSource (= Psi), Grammar.abs_logTilt_le, Grammar.deriv_quenchedSource, Grammar.deriv_deriv_quenchedSource_zero
% Lean: the convergence radius log 2/||f|| of Psi is an elementary derivation.
These identities are exact and hold at every temperature and every variance; the threshold $v<2$ of \cref{sec:limit} concerns the unnormalised evidence and does not appear, since the inverse evidence $D(G)^{-1}\le\lambda e^{2}(1+\|G\|_\infty)^{2\lambda}/\rho(S)$ has all moments. Iterating \eqref{eq:interpolation} produces finite-order expansions in the covariance amplitude with exact integral remainders, in which covariance lines between replicas are the bookkeeping. The interpolation to finite order does not give a convergent series in the covariance, and the amplitude $s$ is not the asymptotic parameter $n^{-1/Q}$, so these identities describe the random leading object and its dependence on the field, not the subleading $n$-expansion. The averaged posterior cumulants are packaged by the quenched source $\Psi(\varepsilon)=\E\log\langle e^{\varepsilon f}\rangle_G$, with $\Psi'(0)=\E\langle f\rangle_G$ and $\Psi''(0)=\E\operatorname{Var}_{\mu_G}(f)$, an expected conditional variance; for bounded $f$ the elementary bound $|\langle e^{zf}\rangle_g-1|\le e^{|z|\|f\|_\infty}-1$ makes $\log\langle e^{zf}\rangle_g$ analytic and uniformly bounded on $|z|<\log2/\|f\|_\infty$, so the expansion of $\Psi$ in $\varepsilon$ converges there.

\subsection{Where the theory stops}

Two identifications separate the results of this section from a statement about the model. The first is that the restriction of the empirical process to the leading stratum converges in law to $G$ as a process on $S$, with $\rho$ the residue measure and $\mathcal C$ the covariance of the limit field; for the values on $S$ this is Watanabe's theorem, and it is what the leading term needs. The second is that the leading posterior expectation of the fixed-sample theory, which is a continuous functional of the field, is the functional $\langle f\rangle_G$ of that limit; this is a matter of matching the two constructions and, once done, gives $\lim_n\E[\E[f\mid\Dn]]=\E\langle f\rangle_G$ for every bounded $f$ with no further estimate, since $|E[f\mid\Dn]|\le\|f\|_\infty$ makes the posterior expectations uniformly integrable. The subleading averaged corrections are a further problem: they require rates for the fixed-sample remainders and for the law of the finite-$n$ field, the latter of Edgeworth type, and the exponent lattice rather than $n^{-1/2}$ decides which correction comes first. None of this is attempted here.

%%%%%%%% sections/13_formalisation.tex
\section{What is a theorem}\label{sec:formalisation}

The chart expansions, the resolved coefficient constructions and stratum measures, the quotient algebra, and the compact-base Gaussian identities of this paper have formal counterparts in the Lean theorem prover, in the library \texttt{timaeus-research/grammar} (namespace \texttt{Grammar}, commit \texttt{d56efc8}), with the resolution of singularities consumed from the library \texttt{hironaka} through its axiom-free exports and the statements about the sample proved in a bridge workspace on top of the formalisation of \citet{greybook}. The declarations of the library named below depend on no axioms beyond \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}. \cref{tab:lean} lists the correspondence; the hypotheses stated in the table are those of the formal statements, which in several places are more specific than the prose above (the population chart statements allow a temperature $\beta>0$ and a box size $b>0$, the empirical ones are at unit temperature on the unit box, resolved statements are for a normalised core transport, and \texttt{ResolvedData} carries measurability of $K$, a smooth nonnegative compactly supported prior and smooth observables), and the reader should take the table as the precise version. Two features of the resolved statements deserve to be stated once. The resolved data consist of an \emph{open} set $W$ and a smooth prior with compact support inside it, and the partition function is the integral over all of $\R^d$; the assembled theorems therefore treat a prior supported in the interior of the parameter domain, and boundary walls of $W$, as in \cref{ex:mixed}, are covered only by the chart-level statements on the positive box. And the strata, the deep set and the open set $X_c$ of the formal statements are intersected with the pull-back of the closed support of the prior, so they are support-truncated versions of the sets of \cref{sec:population}. The geometric and statistical identifications not covered by these declarations are listed separately below.

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
Graded stratum formula (\cref{thm:graded}) & $c\ge1$, $\mu>0$, $F$ smooth vanishing near $D_{c+1}$ (chart form: jets vanishing on the deep set): degrees $\ge c$ vanish; top coefficient as face integrals with constant $\Gamma(\mu)/((c-1)!\prod2k_j\alpha_j!)$ & \texttt{coeff\_eq\_zero\_of\_deep}, \texttt{coeff\_eq\_stratumSum}, \texttt{smoothCoeff\_eq\_faceSum\_top}, \texttt{faceMonoCoeff\_top} \\
Jet dependence (\cref{thm:jet}) & $c\ge1$, both observables smooth and vanishing near $D_{c+1}$: kills $\Ical_S^{\,n_\mu(P)+1}$ near the stratum; descends to the jet quotient & \texttt{coeff\_eq\_of\_memIdealPow}, \texttt{descendedCoeff} \\
Stratum measure (\cref{thm:stratum_measure}) & $c\ge1$, zero-order condition: positive measure on $X_c$ integrating tests to the coefficient, carried by $S^\mu_c$, unique among regular measures, transport-independent, representing $c_{\mu,c-1}$ on $\Ical_{c+1}$ & \texttt{ResolvedData.stratumMeasure} (\texttt{SmoothStratumMeasure.lean}), \texttt{coeff\_withF\_eq\_integral\_stratumMeasure}, \texttt{eq\_stratumMeasure\_of\_tests}, \texttt{stratumMeasure\_eq\_of\_transports} \\
Residue (\cref{thm:residue,thm:identity}) & $\mu>0$: $\Rres=\frac{(c-1)!}{\Gamma(\mu)}\nu$ equals the chart residue measure, the sum over pieces and simple faces of the face densities with $(2k_j)^{-1}$ per wall; no separate density-residue calculus & \texttt{residueMeasure}, \texttt{chartResidueMeasure\_eq\_residueMeasure} \\
Leading term (\cref{thm:leading}) & a pair $(\lambda,m)$ with $\lambda$ at most every wall exponent and $m$ at least every resonance count (the true extremal pair is one instance; attainment is not required, and for a non-attained pair the limit is zero); $F$ vanishing near $D_{m+1}$: normalised limit $=\int F\,d\nu^\lambda_m$; for $F\ge0$ positive at a realiser where the prior is positive, positivity; $\nu(X)\le c_{\lambda,m-1}(1)$, with equality if $D_{m+1}=\varnothing$ & \texttt{tendsto\_normalised\_partitionObs\_extremal}, \texttt{observableCoeff\_pos\_of\_realised}, \texttt{extremalStratumMeasure\_univ\_le}, \texttt{extremalStratumMeasure\_univ\_eq\_of\_deep\_empty} \\
RLCT & nonempty zero fibre, prior positive at every zero of $K$ in its closed support (so, since a connected component of $\{K=0\}$ meeting the support is then contained in it, every such component must be compact; the hypothesis excludes a compactly supported prior meeting a noncompact component such as a plane of \cref{ex:planes} on $\R^3$, and holds for isolated or compact zero components inside the region where the prior is positive): $\Zcal_n[1]\sim c\,n^{-\lambda}(\log n)^{m-1}$, $c>0$ & \texttt{exists\_rlct\_asymptotic} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Fluctuation function and empirical expansion (Part~III)}}\\
Ladder & $\beta,\mu>0$: $\partial_aS_\mu=\beta S_{\mu+1/2}$; recurrence; ODE; index derivatives as log weights (the Weber substitution, the parabolic-cylinder closed form and the erf formula are analytic derivations, not formalised) & \texttt{deriv\_fluctuation}, \texttt{fluctuation\_recurrence}, \texttt{fluctuation\_ode}, \texttt{mellinMom\_pow\_mul\_exp\_eq\_iteratedDeriv} \\
One-dimensional expansion & smooth $\eta,\xi$, $k,b>0$, integers $q,L$ with $2kL\le q+1+h$, $N\ge1$, $bN^{1/2k}\ge1$: $\sum_{j\le q}C_jN^{-\mu_j}+O(N^{-L})$ with $C_j=\partial^j[\eta S_{\mu_j}(\xi)](0)/(j!2k)$ by definition; explicit constant through $\xi\le M$ and bounds on the jet polynomials & \texttt{empOneDim\_expansion}, \texttt{empOneDim\_expansion\_of\_bounds}, \texttt{empOneDimCoeff\_one} \\
Chart expansion (\cref{thm:empirical_expansion}) & smooth $\eta,\zeta$, $k_i>0$: cutoff expansion, unique coefficients; remainder linear in a \texttt{FieldJetBound} constant at fixed field bound $M'$ & \texttt{emp\_cutoffExpansion}, \texttt{empCoeff\_unique}, \texttt{emp\_cutoffExpansion\_uniform} \\
Resolved expansion & bounded smooth root field: expansion on the common lattice with degree bounded by the common degree; at zero field the coefficients agree with the population ones on that lattice and degree range & \texttt{empZ\_cutoffExpansion}, \texttt{resolvedCoeff\_zero} \\
Graded empirical formula \eqref{eq:empirical_graded} & $\mu>0$, $c\ge1$, $k_i>0$, amplitude vanishing near the deep set (chart form) or observable vanishing near $D_{c+1}$ (resolved form): degrees $\ge c$ vanish; top coefficient $=$ population coefficient of $\eta S_\mu(\zeta)/\Gamma(\mu)$; branchwise stratum sum & \texttt{empCoeff\_eq\_zero\_of\_deep}, \texttt{empCoeff\_eq\_faceSum\_top}, \texttt{empCoeff\_top\_eq\_smoothCoeff}, \texttt{resolvedCoeff\_eq\_empStratumSum} \\
Empirical leading term \eqref{eq:empirical_leading} & chart-leading transport at $(\lambda,m)$, $m\ge1$, bounded root field, smooth $F$: normalised limit $=$ branchwise face formula with $S_\lambda(\hat\psi)$; for $\lambda>0$ and $F$ a test in the sense of the development (smooth, compactly supported in $X_m$) it equals $\int F\,d\nu(\hat\psi)$ & \texttt{hasLeadingTerm\_empZ}, \texttt{hasLeadingTerm\_empZ\_eq\_integral} \\
Generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1} & $k_i>0$, one resonant coordinate with $\mu_1$ strictly below every other exponent: $c_{\lambda,0}$, $c_{\mu_1,0}$ as face integrals; every other coefficient at lattice exponents $\le\mu_1$ and log degree $\le d-1$ vanishes & \texttt{empCoeff\_generic}, \texttt{empCoeff\_firstCorrection}, \texttt{tendsto\_firstCorrection} \\
Two-dimensional tie & $x^2y^2$ on the positive unit square, constant amplitude and field: $\frac{n^{-1/2}}4[S_{1/2}(a)\log n-\partial_\nu S_\nu(a)|_{1/2}]+o(n^{-1/2})$ (the nonconstant-amplitude formulas of \cref{sec:tiers,sec:first_orders} are derivations) & \texttt{tendsto\_logExample} \\
Generating identity \eqref{eq:generating} & smooth $\eta,\zeta$, $k_i>0$, lattice $\mu$, $q\le d-1$: unconditionally convergent series of population coefficients (in the form $\eta\zeta^r$ at the monomial $h+rk$) & \texttt{hasSum\_empCoeff\_population} \\
Mellin--Laurent characterisation & a cutoff expansion locally integrable on $(0,\infty)$ and bounded near $0$, on a strip: the Mellin transform is the transform of the subtracted remainder plus the principal parts; polar data with bounded remainder are unique and equal the coefficients & \texttt{mellin\_eq\_mellin\_cutoffRemainderFun\_add\_principalParts}, \texttt{polarCoeff\_unique} \\
Coefficient continuity & top depth-graded coefficient, $\mu>0$, $c\ge1$, admissible observable: locally Lipschitz in the chart jets of the branch representatives; convergence in law, one exponent at a time, under convergence in law of the jets to a limit that is itself the jet of a smooth root field & \texttt{exists\_resolvedCoeff\_top\_bound}, \texttt{tendstoInDistribution\_resolvedCoeff\_top} \\
Gaussian average & $\E\,S_\lambda(N(0,v))=\Gamma(\lambda)(1-v/2)^{-\lambda}$ and integrability for $v<2$ (the divergence for $v\ge2$ is the extended-integral statement \texttt{lintegral\_gaussMomentJ\_lt\_top\_iff}); Wick series for a Gaussian random smooth chart field whose scaled field $u^k\zeta$ has a smooth variance profile $W$, measurable jet maps, jet order at the depth of $\mu+\frac12$, and an exponential jet-norm moment with $\delta>\frac14$ & \texttt{integral\_fluctuation\_gaussianReal'}, \texttt{integral\_empCoeff\_gaussian\_wick\_of\_exp\_moment} \\
\midrule
\multicolumn{3}{@{}l}{\emph{Expectations (Part~IV)}}\\
Quotient to all orders (\cref{thm:posterior_quotient}) & $Q>0$, two cutoff expansions vanishing below a common base exponent, nonzero leading block, $J\ge1$: quotient blocks, remainder $O(n^{-J/Q}(1+\log n)^{D(J+1)})$; in probability at the diagonal for the grey book's data model: i.i.d.\ sample, unit temperature, prior localised by a cutoff in $K$, bounded observable smooth in the charts, chart-leading atlas with a positive-weight chart realising $m$ (bridge workspace, \texttt{Bridge/PosteriorAllOrders.lean}) & \texttt{cutoff\_div\_isBigO'}, \texttt{boundedInProbSeq\_posteriorMean\_allOrders} \\
Connected coefficients & $\kappa_2=\partial^2_\varepsilon\log(Z[e^{\varepsilon f}]/Z[1])|_0$ at the block level; posterior variance to all orders under box-leading data with a nonzero denominator block, remainder $O(n^{-J/Q}(1+\log n)^{(d-1)(2J+2)})$; higher cumulants are algebra over the quotient blocks & \texttt{coeff\_two\_mul\_coeff\_two\_logOf\_blocks}, \texttt{emp\_variance\_isBigO} \\
Two-site balancing \eqref{eq:two_site} & probability space, $0<p<1$, measurable, everywhere positive weights with exchangeable joint law & \texttt{integral\_twoSitePosteriorMass\_sub}, \texttt{integral\_twoSitePosteriorMass\_mem} \\
Fr\'echet derivative, Stein & compact metric base with finite nonzero measure, $\beta,\lambda>0$, continuous observables; Stein additionally for a Gaussian field with continuous PSD kernel, measurable evaluations and second sup-norm moment & \texttt{hasFDerivAt\_compactAvg}, \texttt{GaussianField.integral\_eval\_mul\_compactAvg} \\
Interpolation \eqref{eq:interpolation} & same hypotheses, $\rho\ne0$, nonnegative diagonal bound $c$ on the kernel & \texttt{GaussianField.integral\_compactAvg\_eq}, \texttt{compactMeanResponse\_eq\_replica}, \texttt{abs\_compactMeanResponse\_le} \\
Inverse evidence & $\beta,\lambda>0$, $\rho\ne0$, Gaussian $C(K,\R)$-valued field: every nonnegative power of $D(G)^{-1}$ is integrable & \texttt{inv\_compactD\_le}, \texttt{integrable\_inv\_compactD\_rpow\_of\_isGaussian} \\
Quenched source & same hypotheses: $|\log\langle e^{\varepsilon f}\rangle_g|\le|\varepsilon|\,\|f\|$; $\Psi'(0)$, $\Psi''(0)$ (the convergence radius is an elementary derivation) & \texttt{abs\_logTilt\_le}, \texttt{deriv\_quenchedSource}, \texttt{deriv\_deriv\_quenchedSource\_zero} \\
\bottomrule
\end{tabular}
\caption{Formal counterparts of the statements of this paper. Names are declarations of \texttt{timaeus-research/grammar} at commit \texttt{d56efc8}, in the namespaces \texttt{Grammar}, \texttt{Grammar.SmoothEngine} and \texttt{Grammar.SmoothEngine.ResolvedData}, unless stated; the bridge statement about the sample lives in the workspace on the grey book formalisation.}
\label{tab:lean}
\end{table}

\paragraph{What is not proved.}
\begin{itemize}
\item The finite-part form \eqref{eq:tier2} for one resonant coordinate at normal order $\alpha\ge2$ when the amplitude does not vanish at the corner and $\mu$ exceeds another wall's exponent; the formalised coefficient formula performs the Taylor subtraction but its closed evaluation is not written. Likewise the closed form of the lower logarithmic coefficients at ties for nonconstant data; the $x^2y^2$ formulas of \cref{sec:first_orders}, the Weber reduction and the Gaussian integration identities are analytic derivations within established machinery, not formalised theorems and not open problems.
\item The convergence in law of the normal derivatives of the empirical process on the faces, needed for the subleading coefficients, together with the statistical hypotheses of \cref{sec:setting} that would imply it; the identification of the fixed-sample leading posterior functional, which lives on the noncompact orthant-labelled leading stratum, with $\langle f\rangle_G$ of the compact-base model of \cref{sec:averaging}; and the continuity and convergence in law of the lower logarithmic coefficients, for which only the top depth-graded coefficients are covered by the cited declarations. All are conditional statements in the present text.
\item Watanabe's convergence of the zeta function on the strip $\operatorname{Re}s<\lambda$ is used as a hypothesis where the Mellin characterisation is applied to the assembled integral; it is not derived from the resolution.
\item The averaged subleading corrections of \cref{sec:averaging}.
\item A manifold-level residue calculus for densities: the residue is defined as a measure and identified with the face densities in charts; the operation on densities is not developed separately. For positive normal orders the chart presentation \eqref{eq:conormal_presentation} as normal derivatives against face densities is not a canonical decomposition; what is intrinsic is the total functional, the finite jet it depends on (\texttt{coeff\_eq\_of\_memIdealPow}) and its descent to the jet quotient (\texttt{descendedCoeff}), from which the principal symbol of \cref{sec:conormal} follows. The moment tensors of \cref{app:moment_tensors} are not used.
\end{itemize}

%%%%%%%% sections/14_conclusion.tex
\section{Related work and conclusion}\label{sec:conclusion}

\paragraph{Related work.} The asymptotic expansion of the population partition function and the identification of its exponents with the real log canonical threshold are the foundation of singular learning theory \citep{watanabeAlgebraicGeometryStatistical2009,watanabe2018}, and the standard form of the empirical divergence, the fluctuation function and the Gaussian limit of the empirical process are Watanabe's. The use of the strata of a normal crossing divisor to organise the asymptotics of integrals with a phase is classical in the theory of Igusa zeta functions and motivic integration \citep{igusa2000introduction,denef1998motivicigusazetafunctions,gusein2010integration}, and the analogy with the amplitude selecting the visible features of a caustic in geometric optics is in \citet{arnold2012singularities}. Products and quotients of expansions in the scale $n^{-\mu}(\log n)^q$ are treated in \citet{paris2001asymptotics}. The identification of the fluctuation function with a parabolic cylinder function is classical from the point of view of special functions \citep{NIST:DLMF}. Gaussian integration by parts, replica identities and covariance interpolation as used in \cref{sec:averaging} are the standard tools of mean field spin glasses \citep{talagrand2011meanfield,panchenko2013sk,guerra2002thermodynamic}. On the empirical side, the local learning coefficient estimator \citep{lau2023quantifying}, susceptibilities \citep{baker2025structuralinferenceinterpretingsmall,gordon2026lang3} and patterning \citep{wang2026patterning} are the measurements whose geometric meaning the paper describes; the hypothesis that structure is encoded in the singular geometry is set out in \citet{murfet2025programssingularities}.

\paragraph{Relation to the earlier paper.} This paper subsumes the earlier account of the population expansion by Gerraty and Murfet, from which the geometric material of \cref{sec:resolution,sec:stratification,sec:normal_geometry} and \cref{app:moment_tensors} and the population wall-crossing picture are inherited, in places verbatim. The earlier paper described the coefficients through a Taylor tree, an absolutely convergent series over the Taylor coefficients of analytic data on a polydisc; that description has been dropped, because its analyticity hypotheses are not met by the smooth priors, cutoffs and limit fields of the application, and replaced by the smooth finite-jet and face-first description of Part~II. The stratum measures and the weighted logarithmic residue, the empirical expansion for smooth data with its three descriptions of the coefficients, the posterior quotient and connected coefficients, and the compact-base Gaussian identities are new here.

\paragraph{Conclusion.} A posterior expectation is a ratio of two integrals of the same kind, and each has an expansion whose coefficients are distributions supported on the resonant part of the exceptional divisor and paired with the observable; on the observables that vanish near the deeper crossings they are represented by finitely many normal derivatives integrated over one exact stratum. The strata are where the coefficients live; the observable enters through its restriction to a stratum and finitely many normal derivatives there; the data enters through the fluctuation function of the standardised empirical process evaluated on the same strata, with derivatives of the field climbing a ladder of indices. At leading order the posterior is the residue measure on the deepest stratum of lowest exponent, reweighted pointwise by the fluctuation function of the field, and a posterior expectation is the average of the observable against this random measure. The corrections follow the same pattern one stratum and one derivative at a time, and their algebra, the quotient and the connected coefficients, introduces nothing beyond the coefficients of the two integrals.

Three things are left open. The closed forms of the coefficients past the first correction, where the residue densities need finite parts and the ties need the lower Laurent data, are computations within a theory that is complete. The convergence in law of the derivatives of the empirical process on the strata is a statistical input about the model that the geometry cannot supply; the identification of the leading posterior functional with the Gibbs measure of the limit field is, by contrast, geometry, a compact branch space over the support of the prior on which the leading measure lives, and it has not been carried out. And the averaged subleading corrections require rates that the present limit theorems do not give. The shape of the answer is not open: at every order the coefficient is a canonical distribution on the resonant part of the divisor, of finite transverse order, whose associated-graded pieces pair a normal jet of the observable with a residue density and whose lower pieces carry the finite parts at the crossings; the data enters it by multiplication with the fluctuation function of the field.

%%%%%%%% sections/A_chart_proofs.tex
\section{Chart-level proofs}\label{app:chart_proofs}

This appendix gives the proofs behind \cref{thm:population_expansion,thm:empirical_expansion} and the generic first correction \eqref{eq:c_lambda}--\eqref{eq:c_mu1}, at the level of detail at which they are formalised. The population case is the empirical case at zero field, so only the latter is treated. Throughout, $\eta$ and $\zeta$ are smooth on a neighbourhood of the closed cube $[0,1]^d$, $k_i\ge1$, and
\[
Z(n)=Z_n(\eta;\zeta)=\int_{(0,1]^d}\eta(u)\,u^h\,e^{-nu^{2k}+\sqrt n\,u^k\zeta(u)}\,du .
\]

% Lean @ d56efc8: Grammar/EmpiricalOneDim.lean: Grammar.SmoothEngine.empOneDimCoeff, Grammar.SmoothEngine.oneDimExpConst (the constant K_{h,k,q,L}(M,C)), Grammar.SmoothEngine.empOneDim_expansion_of_bounds, Grammar.SmoothEngine.empOneDim_expansion
% Lean @ d56efc8: Grammar/EmpiricalFieldJets.lean: Grammar.SmoothEngine.jetPoly (= P_j)
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
by $s=x^{2k}$ and the identity $\int s^{\mu-1}e^{-s}P_j(v,\sqrt s)e^{\sqrt s\zeta(v)}ds=\partial_v^j[\eta S_\mu(\zeta)](v)$, which is \eqref{eq:one_dim_coefficients} and follows by differentiating $\eta(v)S_\mu(\zeta(v))=\int s^{\mu-1}e^{-s}\eta(v)e^{\sqrt s\zeta(v)}ds$ under the integral $j$ times. The remainder contributes $\varepsilon^{h+1}\int_0^{1/\varepsilon}|R_q(\varepsilon x,x)|\,x^he^{-x^{2k}}dx\le\varepsilon^{h+1+q+1}\,C'$, which is $O(n^{-L})$ whenever $2kL\le q+1+h$. This proves the one-dimensional expansion with the constant
\[
K_{h,k,q,L}(M,C_\bullet)=\Big(\sum_{j\le q}\frac{2C_j\kappa_{h+2j}(M)}{j!}\Big)\,E_{k,L}+\frac{C_{q+1}}{q!}\,\kappa_{h+2q+2}(M)\int_0^\infty e^{-x^{2k}/2}dx ,
\]
where $\kappa_m(M)=m!\,e^{1+(M+1)^2/2}$ bounds $(1+y)^me^{My}e^{-y^2}$ against $e^{-y^2/2}$ and $E_{k,L}$ bounds the tail; the point is that $K$ depends on $(\eta,\zeta)$ only through $M$ and the finitely many $C_j$.

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.sliceExp, Grammar.SmoothEngine.faceWt (the weight w^{h_L} p(w)^{-mu})
\subsection{Fubini along a resonant coordinate}

In dimension $d=n'+1$ fix the coordinate $i_0$ and write $u=(u_{i_0},w)$. On the box the monomials split, $u^h=u_{i_0}^{h_{i_0}}w^{h_L}$ and $u^{2k}=u_{i_0}^{2k_{i_0}}p(w)$ with $p=w^{2k_L}$, and $\sqrt n\,u^k=\sqrt{np(w)}\,u_{i_0}^{k_{i_0}}$ for $w$ in the open box. Hence, by Fubini,
\begin{equation}\label{eq:fubini}
Z(n)=\int_{(0,1]^{d-1}}w^{h_L}\,I\big(np(w),w\big)\,dw,\qquad I(T,w)=\int_0^1\eta(u,w)\,u^{h_{i_0}}\,e^{-Tu^{2k_{i_0}}+\sqrt T\,u^{k_{i_0}}\zeta(u,w)}\,du ,
\end{equation}
the one-dimensional integral of the slice $(\eta(\cdot,w),\zeta(\cdot,w))$ at the effective sample size $T=np(w)$. The slices are uniformly controlled: $\zeta\le M$ on the closed cube, and the coefficient functions $p_{j,r}$ of the slice are restrictions to the line $\{w=\text{const}\}$ of smooth functions on the cube, obtained by the same recursion with $\partial_{u_{i_0}}$ in place of $d/dv$, so their bounds $C_j$ can be taken uniform in $w$. The one-dimensional estimate therefore holds for every slice with the same constant.

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.SmoothEngine.genericFaceCoeff, Grammar.SmoothEngine.tendsto_firstCorrection
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

% Lean @ d56efc8: Grammar/FirstCorrection.lean: Grammar.CutoffExpansion.coeff_eq_of_twoTerm, Grammar.SmoothEngine.empCoeff_generic, Grammar.SmoothEngine.empCoeff_firstCorrection
\subsection{Reading off the coefficients}

A two-term asymptotic determines the coefficients of any cutoff expansion up to the second exponent. Precisely, if $Z$ has a cutoff expansion $c$ on $Q^{-1}\N$ with degree $\le D$, and $n^{\mu_1}(Z(n)-An^{-\lambda})\to B$ with $\lambda<\mu_1$ lattice points, then $c_{\lambda,0}=A$, $c_{\mu_1,0}=B$, and $c_{\mu,q}=0$ for every other lattice $\mu\le\mu_1$ and $q\le D$. The proof subtracts the two known terms, each of which has the obvious cutoff expansion, and uses the first-nonzero-term theorem: a cutoff expansion of a function that is $o(n^{-\mu_1})$ has no nonzero coefficient at any exponent $\le\mu_1$, because the first nonzero pair $(\mu,q)$ in the lexicographic order makes the function asymptotically equivalent to $c_{\mu,q}n^{-\mu}(\log n)^q$, which is not $o(n^{-\mu_1})$ when $\mu\le\mu_1$. Applied to the canonical expansion of \cref{thm:empirical_expansion}, this identifies $c_{\lambda,0}$ and $c_{\mu_1,0}$ with the face integrals and forces the vanishing of everything else at lattice exponents $\le\mu_1$: no logarithms at $\lambda$ or $\mu_1$, nothing between.

% Lean @ d56efc8: Grammar/EmpiricalGeneral.lean: Grammar.SmoothEngine.emp_cutoffExpansion (the face construction defining empCoeff)
% Lean @ d56efc8: Grammar/SmoothGeneral.lean: Grammar.SmoothEngine.smooth_cutoffExpansion, Grammar.SmoothEngine.smoothCoeff_unique
\subsection{The general chart expansion}

The general case, where several coordinates may resonate and every order is wanted, is organised by faces. For a face $J$ of the cube and a depth $p$ one Taylor-expands the field factor $\eta e^{\tau\zeta}$ in the $J$-normal directions to order $p$ and subtracts its Taylor polynomial in the complementary directions to the same order; the $J$-normal integrals of monomials are the one-dimensional integrals above, whose Laurent data at the resonant exponents are explicit, and the complementary integrals are integrals over the face of the Taylor-subtracted amplitude against $w^{h-2k\mu}$ with logarithmic weights $(\log w^{2k})^\ell$, convergent because the subtraction removes the terms that would diverge. The coefficient at $(\mu,q)$ is a finite sum over faces and Taylor orders of these face integrals, and the remainder of the truncation is estimated by the same one-dimensional bounds, with a constant linear in a bound on the normal jets of $\eta e^{\tau\zeta}$ of the depth. This is the construction that defines the coefficients in the formalisation; uniqueness of expansions then shows they agree with every other description, including the Laurent data of \cref{sec:tiers}, and the graded formula \eqref{eq:graded} is its evaluation at the top logarithmic order, where only the fully resonant faces of maximal depth survive and no Taylor subtraction is needed for admissible amplitudes.

%%%%%%%% sections/B_fluctuation_facts.tex
\section{The fluctuation function and the Weber equation}\label{app:fluctuation_facts}

We collect the facts about $S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-t+a\sqrt t}dt$ used in the body, with proofs.

% Lean @ d56efc8: Grammar/Fluctuation.lean: Grammar.deriv_fluctuation, Grammar.fluctuation_recurrence, Grammar.fluctuation_ode, Grammar.fluctuation_one
\paragraph{Ladder and recurrence.} Differentiation under the integral, justified by the bound $t^{\mu-1}\sqrt t\,e^{-t+a\sqrt t}\le t^{\mu-1/2}e^{-t/2+a^2}$, gives $\partial_aS_\mu=S_{\mu+1/2}$ and $\partial_a^2S_\mu=S_{\mu+1}$. Integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]=(\mu t^{\mu-1}-t^\mu+\frac a2t^{\mu-1/2})e^{-t+a\sqrt t}$ over $(0,\infty)$ gives $0=\mu S_\mu-S_{\mu+1}+\frac a2S_{\mu+1/2}$, the recurrence $S_{\mu+1}=\frac a2S_{\mu+1/2}+\mu S_\mu$; rewritten with the ladder it is $S_\mu''=\frac a2S_\mu'+\mu S_\mu$. At $\mu=0$ the same computation on $[\varepsilon,T]$ gives $S_1(a)=\frac a2S_{1/2}(a)+1$ in the limit.

% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_gaussian (S_{1/2} as a Gaussian integral)
% Lean: not formalised; the Weber substitution and parabolic-cylinder closed form are analytic derivations.
\paragraph{Weber's equation.} Put $z=a/\sqrt2$ and $S_\mu(a)=e^{z^2/4}f(z)$. Then $S_\mu'=e^{z^2/4}\frac1{\sqrt2}(f'+\frac z2f)$, $S_\mu''=e^{z^2/4}\frac12(f''+zf'+\frac12f+\frac{z^2}4f)$, and substituting into the ODE and dividing by $\frac12e^{z^2/4}$ leaves $f''+(\frac12-2\mu-\frac{z^2}4)f=0$, the parabolic cylinder equation with parameter $\nu=-2\mu$. Comparing the integral representation $D_{-\nu}(x)=\frac{e^{-x^2/4}}{\Gamma(\nu)}\int_0^\infty u^{\nu-1}e^{-u^2/2-xu}du$ \citep[\S12.5(i)]{NIST:DLMF} with the definition of $S_\mu$ after $u=\sqrt{2t}$ gives the closed form \eqref{eq:weber}. At $\mu=1/2$, $u=\sqrt t$ and completion of the square give $S_{1/2}(a)=\sqrt\pi\,e^{a^2/4}(1+\operatorname{erf}(a/2))$.

% Lean @ d56efc8: Grammar/RegularCase.lean: fluctuation_half_iteratedDeriv (the regular orbit)
% Lean: the module structure itself is not formalised.
\paragraph{The Weyl algebra.} Let $b^\dagger=\partial_a$ and $b=2\partial_a-a$, so $[b,b^\dagger]=1$. Then $b^\dagger S_\mu=S_{\mu+1/2}$, and the recurrence at $\mu-\frac12$ gives $bS_\mu=2S_{\mu+1/2}-aS_\mu=(2\mu-1)S_{\mu-1/2}$ for $\mu>\frac12$, while $bS_{1/2}=2$. The number operator $b^\dagger b-(2\mu-1)$ acts on $S_{\mu+Q/2}$ by $Q$. For $\mu\notin\frac12\mathbb Z$ the definition extends to $\mu\le0$ by $S_\mu=\frac1{2\mu}bS_{\mu+1/2}$, consistently with the meromorphic continuation of \eqref{eq:weber} in $\mu$, the ladder relations persist, and the span of the $S_\mu$ along the orbit $\mu+\frac12\mathbb Z$ is a module over the Weyl algebra, doubly infinite with no lowest weight. On the orbit of $\frac12$ the span of the positive-index functions alone is not stable, since $bS_{1/2}=2$; the module is $\mathbb C[a]+\operatorname{span}\{S_{(n+1)/2}:n\ge0\}$, which contains the polynomials $\mathbb C[a]=\operatorname{span}\{b^m1\}$ as a submodule, and its quotient is the Fock representation with vacuum $S_{1/2}$.

% Lean @ d56efc8: Grammar/MellinLogWeights.lean: Grammar.SmoothEngine.mellinMom_pow_mul_exp_eq_iteratedDeriv
% Lean: the inhomogeneous Weber system is a derivation.
\paragraph{Index derivatives.} For $\nu>0$ and every $\ell$, $\partial_\nu^\ell S_\nu(a)=\int_0^\infty t^{\nu-1}(\log t)^\ell e^{-t+a\sqrt t}dt$, again by differentiation under the integral, the derivative of $t^{\nu-1}$ in $\nu$ being $t^{\nu-1}\log t$ and the bound $|\log t|^\ell t^{\nu-1}e^{-t+a\sqrt t}$ integrable. Hence for a constant $c$, $\int_0^\infty t^{\nu-1}(c-\log t)^pe^{-t+a\sqrt t}dt=(c-\partial_\nu)^pS_\nu(a)$, and $\sum_p\frac{z^p}{p!}(c-\partial_\nu)^pS_\nu=e^{zc}S_{\nu-z}$ for small $z$, the translation in the index. Differentiating the ODE $\ell$ times in $\mu$ gives the inhomogeneous equation $(\partial_\mu^\ell S_\mu)''-\frac a2(\partial_\mu^\ell S_\mu)'-\mu\,\partial_\mu^\ell S_\mu=\ell\,\partial_\mu^{\ell-1}S_\mu$, a triangular system determining the index derivatives recursively.

\paragraph{The incomplete function.} For $T>0$ let $S_\mu(a;T)=\int_0^Tt^{\mu-1}e^{-t+a\sqrt t}dt$. It has the same ladder $\partial_a^qS_\mu(a;T)=S_{\mu+q/2}(a;T)$ and index derivatives, and integrating $\frac{d}{dt}[t^\mu e^{-t+a\sqrt t}]$ over $[0,T]$ gives the inhomogeneous Weber equation $S_\mu''(a;T)-\frac a2S_\mu'(a;T)-\mu S_\mu(a;T)=-T^\mu e^{-T+a\sqrt T}$. In the applications $T=nb^{2k}$, and $S_\mu(a)-S_\mu(a;T)=\int_T^\infty t^{\mu-1}e^{-t+a\sqrt t}dt\le C_\mu e^{-T/2}e^{a^2}$ is exponentially small in $n$.

% Lean @ d56efc8: Grammar/GaussianFluctuationScalar.lean: Grammar.integral_fluctuation_gaussianReal'
% Lean @ d56efc8: Grammar/GaussianThreshold.lean: Grammar.lintegral_gaussMomentJ_lt_top_iff
\paragraph{Gaussian average.} For $a\sim N(0,v)$, $\E e^{a\sqrt t}=e^{vt/2}$, so by Tonelli $\E S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-(1-v/2)t}dt$, which is $\Gamma(\mu)(1-v/2)^{-\mu}$ for $v<2$ and $+\infty$ for $v\ge2$.

%%%%%%%% sections/C_expansion_algebra.tex
\section{Multiplication and division of expansions}\label{app:expansion_algebra}

Expansions in the scale $n^{-\mu}(\log n)^q$ with exponents on a lattice $Q^{-1}\N$ and bounded logarithmic degree form an algebra, and quotients exist when the denominator's leading block is nonzero. We record the two facts in the cutoff form used throughout.

% Lean @ d56efc8: Grammar/AbstractExpansion.lean: Grammar.CutoffExpansion (def)
% Lean @ d56efc8: Grammar/CutoffExpansionUniqueness.lean: Grammar.CutoffExpansion.sub (uniqueness of coefficients)
\paragraph{Blocks.} With $x=n^{-1/Q}$ and $\ell=\log n$, a cutoff expansion $F(n)=\sum_{j<JQ}B_j(\ell)x^j+O(x^{JQ}(1+\ell)^D)$, $B_j\in\R[\ell]$ of degree $\le D$, is a truncated power series in $x$ over $\R[\ell]$, and the remainder is smaller than every retained term because $x^{JQ}(1+\ell)^D=o(x^j\ell^q)$ for $j<JQ$: powers of $x$ beat powers of $\ell$.

% Lean @ d56efc8: Grammar/PosteriorVarianceExpansion.lean: Grammar.sum_mul_sum_eq_cauchy_add_tail (Cauchy product of truncations)
% Lean: no standalone product theorem is cited; the product enters through the quotient and variance results.
\paragraph{Multiplication.} If $F$ and $G$ have cutoff expansions with blocks $A_j,B_j$ and degrees $D_1,D_2$, then $FG$ has the cutoff expansion with blocks $(A*B)_j=\sum_{i\le j}A_iB_{j-i}$ and degree $D_1+D_2$: the product of the two truncations is the truncation of the Cauchy product plus terms $x^{j}$ with $j\ge JQ$ whose coefficients are polynomials in $\ell$ of degree $\le D_1+D_2$, and the cross terms with a remainder are $O(x^{JQ}(1+\ell)^{D_1+D_2})$ since each truncation is $O((1+\ell)^{D_i})$.

% Lean @ d56efc8: Grammar/CutoffQuotientExpansion.lean: Grammar.cutoff_div_isBigO'
% Lean @ d56efc8: Grammar/QuotientBlocks.lean: Grammar.quotientBlocks, Grammar.sum_mul_quotientBlocks
\paragraph{Division.} Suppose $F$ and $G$ have cutoff expansions with blocks $A_j$ and $B_j$ counted from a common first exponent, and $B_0\in\R[\ell]$ is a nonzero polynomial. Define $R\in\R(\ell)[[x]]$ by $R=A/B$, that is,
\[
R_0=\frac{A_0}{B_0},\qquad R_{j+1}=\frac1{B_0}\Big(A_{j+1}-\sum_{i\le j}B_{i+1}R_{j-i}\Big) .
\]
Then for every $J\ge1$,
\[
\frac{F(n)}{G(n)}=\sum_{j<J}R_j(\ell)\,x^j+O\big(x^J(1+\ell)^{D(J+1)}\big) .
\]
The proof is the two-scale division lemma: write $G=B_0(\ell)x^{0}(1+g)$ with $g=\sum_{1\le j<J}(B_j/B_0)x^j+O(x^J(1+\ell)^D/|B_0|)$; since $B_0$ is a nonzero polynomial, $|B_0(\ell)|\ge c\,\ell^{\deg B_0}$ for large $\ell$, so $g\to0$ and $|g|\le Cx(1+\ell)^{D}$ for large $n$, and $(1+g)^{-1}=\sum_{i<J}(-g)^i+O(x^J(1+\ell)^{DJ})$. Multiplying the truncations of $F/B_0$ and $(1+g)^{-1}$ and collecting powers of $x$ gives the recursion, with the stated growth of the remainder: since $B_0$ is a nonzero polynomial, $1/B_0(\ell)=O(1)$ as $\ell\to\infty$, and the displayed logarithmic growth of the remainder is a coarse bound for the finite products that occur in the formal division; the blocks are kept as rational functions so that the bound is exact in $\ell$. Each $R_j$ can be expanded in inverse powers of $\ell$ to any order by dividing the polynomials, at the cost of exactness in $\ell$.

% Lean @ d56efc8: Grammar/SourceLog.lean: Grammar.logOf, Grammar.mul_derivative_logOf, Grammar.coeff_succ_mul_eq_sum_logOf, Grammar.two_mul_coeff_two_logOf, Grammar.coeff_two_mul_coeff_two_logOf_blocks
\paragraph{The logarithm with a source.} For a formal series $U=1+\varepsilon U_1+\varepsilon^2U_2+\cdots$ over any commutative $\mathbb Q$-algebra, $[\varepsilon^r]\log U=\sum_{j=1}^r\frac{(-1)^{j+1}}j[\varepsilon^r](U-1)^j$, a finite formula, and $U\,\partial_\varepsilon\log U=\partial_\varepsilon U$. Applied to $U=\sum_r m_r\varepsilon^r/r!$ with $m_r\in\R(\ell)[[x]]$ the quotient-block series of $Z_n[f^r]/Z_n[1]$, this gives the recursion for the connected coefficients of \cref{sec:posterior}: $\kappa_1=m_1$ and $\kappa_{r+1}=m_{r+1}-\sum_{i<r}\binom ri\kappa_{i+1}m_{r-i}$, in particular $\kappa_2=m_2-m_1^2$ blockwise.

%%%%%%%% sections/D_resolution_facts.tex
\section{Resolution facts used}\label{app:resolution_facts}

\paragraph{The resolution theorem.} We use Hironaka's theorem in the form of \citet[\S11.3, Thm~3.2.1]{igusa2000introduction}, applied to $K_{\mathbb C}$ together with the complexified boundary functions of $W$ and the complexification of an analytic positive factor of the prior where one is assumed: a proper holomorphic $\pi\colon U_{\mathbb C}\to W^{(\mathbb C)}$, an isomorphism off the union of $\{K_{\mathbb C}=0\}$ and the singular locus of the boundary, with $(K_{\mathbb C}\circ\pi)^{-1}(0)$ a normal crossing divisor along whose components $K_{\mathbb C}\circ\pi$ and the Jacobian vanish to constant orders. Since $K$ is real the centres of the blow-ups can be taken real \citep{bierstone1997canonical}, so that $U_{\mathbb C}$ carries an anti-holomorphic involution lifting conjugation, whose fixed locus is the real resolution $U$. At a real point through which exactly the components $E_1,\dots,E_p$ pass, the local coordinates can be chosen equivariant, hence real, and the normal form \eqref{eq:local_normal_form} holds with real units. Nonnegativity of $K$ forces the exponents $a_i$ to be even: an odd exponent would change the sign of $K\circ\pi$ across the wall while the unit does not vanish. Absorbing the unit into a normal coordinate uses only that it is positive and smooth, and changes the Jacobian factor by a smooth positive function without changing the $h_i$. The orders $h_i$ include the effect of rectilinearising the domain, which the phase alone does not see: for $W=\{0\le x\le1,\ 0\le y\le x^2\}$ and $K=x^2$ the integral is $\int_0^1x^2e^{-nx^2}dx\sim\tfrac12\Gamma(\tfrac32)n^{-3/2}$, not the $n^{-1/2}$ of the phase wall $(k,h)=(1,0)$, because the blow-up that straightens the cusp contributes to the Jacobian.

\paragraph{Where the analyticity of $K$ is used.} Only here. The prior, the observable, and the cutoffs of the partitions of unity are smooth, and the expansion theorems of the body are proved for smooth data on the resolution. If $K$ is merely smooth no resolution exists in general, and the theory does not apply; if $K$ is analytic but not polynomial and a comparable polynomial exists, one may replace it by that polynomial without changing exponents or logarithmic degrees, though the coefficients change; such a polynomial need not exist.

\paragraph{Change of variables.} The pull-back $\Zcal_n[f]=\int_U(f\circ\pi)e^{-nK\circ\pi}\pi^*(\varphi\,dw)$ is the change of variables formula for $\pi$, which is not injective on $E$ but is a diffeomorphism off $E$, a set of measure zero whose image $W_0$ has measure zero; this suffices \citep[Thm~7.26]{rudin1987real}.

\paragraph{Tubular neighbourhoods and boundary walls.} The integration domain is rectilinearised together with the phase: in each chart the coordinates are split into phase-active ones, with $k_i>0$, and the remaining ones, which include the coordinates cutting out the boundary of $W$ and are treated as parameters; the resolution is an isomorphism off $\{K=0\}$ but the domain may still need its own charts, and a boundary wall need not be a component of the divisor of $K$. On the ambient real resolution each $E_I$ is a submanifold and the tubular neighbourhood theorem applies to it, with fibres meeting no component $E_j$, $j\notin I$, because the defining equation of such an $E_j$ is a unit near $S_I$. Where a component of the divisor is itself a wall of the integration domain the admissible normal directions form an inward cone rather than a full fibre, and the statements are made orthantwise, in charts, which is how the formalisation proceeds; \cref{sec:normal_geometry} keeps the geometric discussion on the ambient resolution and imposes the domain restrictions chartwise.

\paragraph{The partition of unity.} Cover a neighbourhood $U_\varepsilon=\{K\circ\pi<\varepsilon\}$ of $E$ by normal crossing charts, each meeting only the components of one index set, and take a smooth partition of unity subordinate to this cover. The cutoffs depend on all chart coordinates and are treated as part of the smooth amplitude: they are differentiated in the normal directions along with the prior and the observable, and the face construction of \cref{app:chart_proofs} applies to the product. A cutoff constant along the normal fibres of a stratum would be convenient but is not in general available (normalising functions constant along different fibre projections destroys the constancy, and a fibre-constant function cannot be extended by zero smoothly across the normal boundary of its tube), and it is not needed: the sum over charts is independent of the choice, and only the sum is asserted to be canonical. Analytic partitions of unity do not exist, which is one of the reasons the theory is developed for smooth amplitudes.

\paragraph{Comparability.} If $g_1\asymp g_2$ are comparable nonnegative functions monomialised by the same resolution, their vanishing orders along every component agree: near a point of a component with local equation $u$, $g_i\circ\pi=\varepsilon_iu^{N_i}\cdot(\text{other factors})$, and $c_1\le g_1/g_2\le c_2$ along a curve transverse to the wall forces $N_1=N_2$ \citep[App.~B]{murfet2025programssingularities}. Hence the candidate exponents and logarithmic degrees, and the leading pair for positive amplitudes, are the same for $g_1$ and $g_2$; the coefficients are not, and a subleading candidate present for one may be absent for the other.

================ (2) THE PERSPECTIVE REVIEW
## Overall assessment

**The paper has the right underlying idea, but not yet the right hierarchy of ideas.** Its strongest statement is not that coefficients “live on strata.” It is this:

> Singular posterior asymptotics are obtained by applying a universal radial Mellin transform to a meromorphic distribution, then normalising. Resolution gives a computable, stratified description of that distribution’s polar coefficients.

That formulation retains everything valuable in the paper while distinguishing three things that the draft still sometimes conflates:

1. **The intrinsic object downstairs:** a meromorphic distribution associated with the phase and prior.
2. **Its resolved presentation:** polar distributions, supported on resonant faces, with finite transverse order and possibly singular tangential coefficients.
3. **Its associated-graded pieces:** residue measures and principal normal-jet pairings.

The empirical theory is then a remarkably clean **holomorphic-amplitude extension of the population Mellin theory**. The fluctuation function is its universal Mellin symbol, not a separate geometric mechanism.

I would recommend substantial revision, not because the central mathematics is unconvincing, but because the paper currently spends too much effort making a restricted stratum description appear fundamental, and too little exploiting the invariant statement it already possesses.

I take the formalisation claims and their stated scope as supplied. I have not independently inspected the repository. In particular, a stronger reformulation below should not be read as something already covered by a cited declaration merely because its ingredients are formalised.

# I. Is this the right deep perspective?

## 1. Yes to distributions and jets; no to “a coefficient is a stratum”

The distribution-and-jet perspective is correct and fundamental. But the last sentence of the conclusion—

> “at every order the coefficient is a stratum, a jet of the observable on it, and a fluctuation function of the data”

—is too simple, and is contradicted by some of the paper’s best examples.

A lower logarithmic coefficient can involve:

- normal derivatives supported on several faces;
- finite-part distributions along those faces;
- compatibility and subtraction at their intersections;
- derivatives in the Mellin parameter;
- a sum whose individual face allocations are not canonical.

It is **one distribution**, not necessarily one stratum with one density.

I would replace the sentence by:

> At every order, the coefficient is a canonical polar distribution. On a normal-crossing resolution it has finite transverse order along the resonant divisor; its associated-graded pieces are normal-jet pairings against residue densities, while its lower pieces incorporate the finite-part extensions required at crossings. The empirical field enters by multiplication with a universal holomorphic Mellin amplitude.

That is both stronger and more accurate.

There is also an important distinction between **finite-dimensional information** and **finite-order information**. A coefficient may require only finitely many normal derivatives, but those derivatives are functions along an entire stratum. The information is generally infinite-dimensional tangentially. “A finite jet” should not suggest finitely many numbers.

---

## 2. The meromorphic distribution should come first

### The primary object belongs downstairs

Start with
\[
\langle \mathscr T(s),f\rangle
=
\int_W f(w)K(w)^{-s}\varphi(w)\,dw,
\qquad \Re s<\lambda,
\]
initially in its domain of local integrability.

This is intrinsically defined without choosing a resolution. Its distribution-valued meromorphic continuation is the primary population object.

On a resolution,
\[
\widetilde{\mathscr T}(s)
=
(K\circ\pi)^{-s}\pi^*(\varphi\,dw),
\qquad
\pi_*\widetilde{\mathscr T}(s)=\mathscr T(s).
\]

This identity expresses precisely what is invariant:

- the distribution downstairs is intrinsic;
- the distribution upstairs is intrinsic **on that resolution**;
- distributions on different resolutions are related by proper pushforward;
- a decomposition into face terms is computational;
- individual exceptional components are not intrinsic “pieces of the model.”

The “primes of the singularity” discussion should therefore disappear. Exceptional components introduced by additional blow-ups need not represent independent statistical ways of attaining zero divergence. They can be artefacts of the chosen presentation.

### Candidate poles are not resolution-independent

The draft occasionally says that exponents and multiplicities read off the resolution are the same for any resolution. This needs a sharp distinction:

> The actual poles of the intrinsic meromorphic distribution, and hence the actual asymptotic coefficient system, are invariant. A resolution’s candidate pole set and candidate multiplicities need not be.

For example, blowing up the origin for \(K=x^2y^6\) introduces a divisor with phase order \(8\) and Jacobian order \(1\), hence candidates
\[
\frac{2+\alpha}{8}.
\]
The candidate \(1/4\) was not in the original monomial candidate set. It need not survive in the assembled integral.

This is not a minor qualification. It is one reason the Laurent object should precede the divisor combinatorics.

### Where the classical frameworks fit

The nearest frameworks are:

- distribution-valued analytic continuation in the Atiyah/Bernstein tradition;
- Mellin asymptotics of pushforward densities;
- normal-crossing residue and finite-part calculus.

The equivalent pushforward picture is
\[
K_*(f\varphi\,dw),
\]
whose asymptotics near \(t=0\) are converted into Laplace asymptotics. Gelfand–Leray language describes its density at regular values and helps connect it to singular fibre integrals.

Barlet’s currents provide an important conceptual neighbour, but I would not identify these real, unsigned, smooth-amplitude densities with complex residue currents without specifying the comparison. Likewise, Bernstein–Sato theory constrains continuation and possible poles; it does not by itself provide these amplitude-dependent coefficients.

**Recommendation:** define the coefficients through Laurent extraction, prove their existence and continuity with the smooth chart machinery, and present faces as their evaluation. There is no circularity if the proof of meromorphic continuation and the proof of the expansion are supplied together.

---

## 3. There is a clean general formula for *all* logarithmic coefficients

This is the most consequential missing statement.

Work on the resolution, or more cleanly on its real oriented blow-up along the divisor so that normal sides are separated. Write the Laurent expansion near a positive candidate exponent \(\mu\) as
\[
\widetilde{\mathscr T}(s)
=
\sum_{r=1}^{M_\mu}\frac{A_{\mu,r}}{(\mu-s)^r}
+H_\mu(s),
\]
where the \(A_{\mu,r}\) are distributions.

Let \(\psi\) be a smooth branchwise root field. Then
\[
\mathcal M_F(s;\psi)
=
\left\langle
\widetilde{\mathscr T}(s),\,F S_s(\psi)
\right\rangle.
\]

The complete coefficient formula is
\[
\boxed{
c_{\mu,q}(F;\psi)
=
\frac1{q!}
\sum_{r=q+1}^{M_\mu}
\frac{(-1)^{r-q-1}}{(r-q-1)!}
\left\langle
A_{\mu,r},
F\,
\left.\partial_s^{\,r-q-1}S_s(\psi)\right|_{s=\mu}
\right\rangle .
}
\tag{*}
\]

At zero field, replace \(S_s(\psi)\) by \(\Gamma(s)\).

This formula does several jobs at once:

- it states the population-to-empirical passage exactly;
- it covers every lower logarithmic coefficient;
- it separates geometric polar distributions from the universal radial kernel;
- it explains why index derivatives appear;
- it makes the top-log formula the case \(q=M_\mu-1\);
- it puts the finite-part formulas in their proper role as local expressions for \(A_{\mu,r}\).

For example, at a double pole,
\[
c_{\mu,1}(F;\psi)
=
\langle A_{\mu,2},F S_\mu(\psi)\rangle,
\]
and
\[
c_{\mu,0}(F;\psi)
=
\langle A_{\mu,1},F S_\mu(\psi)\rangle
-
\left\langle A_{\mu,2},
F\,\partial_sS_s(\psi)|_{s=\mu}\right\rangle.
\]
That is exactly the conceptual content of the \(x^2y^2\) calculation.

### What this says about the “three tiers”

Keep them only as **three useful evaluations**, not three levels of theory.

There is one theory: the polar distributions and formula \((*)\).

Its elementary manifestations are:

1. a zero-order highest polar coefficient is a residue measure;
2. a simple pole can be evaluated through one normal residue and tangential finite parts;
3. multiple poles require the complete Laurent jet.

The current repeated “three tiers” organisation partly reflects a genuine computational distinction, but partly reflects failure to state \((*)\).

### Are higher residues, \(b\)-functions, or mixed Hodge structures the better answer?

For this paper, **the polar filtration of the meromorphic distribution is the better answer**.

In coordinates, the polar distributions can indeed be computed by products of one-variable meromorphic distributions, delta derivatives, finite parts, and logarithmic weights. That is a satisfactory general lower-log statement.

A \(b\)-function will not determine the coefficients, and its root multiplicities should not be casually equated with the pole orders of every amplitude pairing. A mixed-Hodge interpretation may illuminate special complex-analytic situations, but it is not the missing organising principle for arbitrary smooth priors, real integration chains, nonisolated zero sets, and random smooth fields.

Do not add Hodge-theoretic vocabulary merely to make this look deeper. The distributional statement is already deep enough.

**Status:** \((*)\) is an immediate Laurent-product calculation once distribution-valued continuation and holomorphic multiplication are established. The substantive work is continuity and finite-order control of the \(A_{\mu,r}\). Mathematically standard; a coherent formalisation may require a nontrivial new interface.

---

## 4. The empirical theory is a base change—but not an ordinary fixed-amplitude substitution

The suggestion “population theory for a random amplitude” is correct only with care.

In the original integral the amplitude
\[
e^{\sqrt N\sqrt K\,\psi}
\]
depends on \(N\). Its derivatives are not uniformly bounded as \(N\to\infty\). One cannot simply apply a fixed-amplitude population theorem to it.

The clean statement is instead:

> After Mellin transformation in \(N\), the empirical theory is the population meromorphic distribution applied to the holomorphic amplitude \(F S_s(\psi)\).

This is a literal base change to amplitudes depending holomorphically on the Mellin parameter:
\[
\widetilde{\mathscr T}(s)
\quad\longmapsto\quad
S_s(\psi)\widetilde{\mathscr T}(s).
\]

The radial interpretation explains why:
\[
t=NK,\qquad
e^{-NK+\sqrt{NK}\psi}=e^{-t+\sqrt t\,\psi}.
\]

Thus both statements are useful:

- **probabilistically:** the sample produces a Gamma-radial exponential tilt;
- **analytically:** \(S_s\) is the Mellin transform of the universal tilted radial kernel.

I would not demote \(S_\mu\) to a mere curiosity. It is the right universal special function, just not the fundamental geometric object.

### The jet-bundle formulation

One can say precisely:

> For every retained asymptotic order, the coefficient map factors through finite transverse jets of the observable and root field along the resonant divisor, with compatibility at crossings. On an exact open stratum its associated-graded expression is a differential pairing with the corresponding residue density.

But one should not imply that a canonical splitting into homogeneous normal derivatives exists. A jet sheaf, or its finite-order quotients, is better than an arbitrarily split jet bundle.

The real oriented blow-up is especially useful here. It replaces “a measurable field with several chartwise representatives on its walls” by a smooth field on a space where those sides are genuinely different boundary points. That is a cleaner geometric object.

**Difficulty:** moderate geometric bookkeeping, not a new asymptotic theory. Formalising the manifold-with-corners and pushforward interfaces could be appreciably more work than the mathematics on paper.

---

## 5. The leading measure deserves a stronger theorem—and one paragraph needs correction

The restriction \(D_{m+1}=\varnothing\) is not an inherent limitation of the leading theory.

More seriously, the explanation following the leading theorem says that deeper points cause infinite mass of the leading residue density. At the **global extremal pair**, that is generally the wrong mechanism.

Suppose \(J\) consists of \(m\) minimal walls, with exponent \(\lambda\). Every additional wall meeting their intersection must have
\[
\lambda_i>\lambda;
\]
otherwise the maximal minimal-wall multiplicity would exceed \(m\). Consequently its tangential residue exponent satisfies
\[
h_i-2k_i\lambda>-1.
\]
The leading residue density is integrable there.

Your own \(x^2y^6\) example demonstrates this:
\[
x^{-1/3}\,dx
\]
extends integrably to the intersection with the nonminimal wall. Here \(m=1\) but \(D_2\neq\varnothing\). In particular, the assertion that both running examples have maximal divisor depth \(m\) is not correct.

The right leading theorem is stronger and simpler:

> **Leading polar measure.** Let \(\lambda\) be the first pole and \(m\) its order. On a compact resolved branch space, the coefficient
> \[
> A_{\lambda,m}
> =
> \lim_{s\uparrow\lambda}(\lambda-s)^m
> \widetilde{\mathscr T}(s)
> \]
> is a finite positive measure \(\rho_\lambda\). In each chart it is the sum of the residue densities on intersections of \(m\) minimal walls, extended integrably across intersections with nonminimal walls. For every smooth \(F\),
> \[
> N^\lambda(\log N)^{-(m-1)}
> Z_N[F;\psi]
> \longrightarrow
> \frac1{(m-1)!}
> \int F S_\lambda(\psi)\,d\rho_\lambda.
> \]

This needs no exclusion of all deeper divisor intersections.

Two distinctions are essential:

- non-extremal residue measures can genuinely diverge at deeper faces;
- the global leading measure is protected by extremality.

One can also obtain positivity downstairs directly: the leading coefficient is the limit of positive rescaled measures on a compact set. Positivity and a fixed-support bound make it a finite measure. Identifying its resolved density is the additional geometric step.

**Status:** this exceeds the stated formal leading-measure theorem. I would expect a standard chart argument plus careful assembly, not a major new result. It is a high-priority extension because it removes several artificial qualifications later.

---

## 6. The one theorem around which I would organise the paper

I would call it something like **“The polar-distribution theorem for tilted singular Laplace integrals.”**

Here is the statement I would write, modulo choosing the exact category of resolved spaces.

> **Theorem.** Let \(K\ge0\) be real analytic, let \(\omega=\varphi\,dw\) be a smooth nonnegative compactly supported density, and choose a rectilinearised resolution of the phase and integration domain. Separate the permitted normal sides, obtaining a resolved branch space \(X\), with proper map \(p:X\to W\). Assume the zero fibre meets the positive part of the density.
>
> For a smooth bounded root field \(\psi\) on \(X\), define
> \[
> Z_N[F;\psi]
> =
> \int_X F\,e^{-N K\circ p+\sqrt{N K\circ p}\,\psi}\,\omega_X.
> \]
> Then:
>
> **(i)** The family
> \[
> \mathscr T_X(s)=(K\circ p)^{-s}\omega_X
> \]
> has a distribution-valued meromorphic continuation. Its positive polar coefficients have finite transverse order and are supported on the corresponding resonant loci. Their pushforwards, when paired with compatible pulled-back data, are independent of the resolution.
>
> **(ii)** \(Z_N[F;\psi]\) has a power-logarithmic cutoff expansion. For every cutoff, its remainder is bounded uniformly when \(\psi\) ranges over an appropriate bounded finite-\(C^R\) set, with linear control by an appropriate \(C^R\) seminorm of \(F\).
>
> **(iii)** Every coefficient is given by formula \((*)\). Consequently each coefficient is continuous in sufficiently many jets of \(F\) and \(\psi\).
>
> **(iv)** At the first pole \((\lambda,m)\), the highest polar coefficient is a finite positive measure \(\rho_\lambda\), and the leading asymptotic is
> \[
> \frac{N^{-\lambda}(\log N)^{m-1}}{(m-1)!}
> \int_X F S_\lambda(\psi)\,d\rho_\lambda.
> \]
>
> **(v)** After normalisation, the posterior has a distribution-valued asymptotic expansion with rational logarithmic blocks. Its leading probability measure is
> \[
> \Pi_\psi
> =
> p_*\left(
> \frac{S_\lambda(\psi)\rho_\lambda}
> {\int_XS_\lambda(\psi)\,d\rho_\lambda}
> \right).
> \]

The sample theorem then becomes a corollary:

- evaluate at \(\psi_n\);
- use uniform remainders for the empirical diagonal;
- use a functional CLT in the required topology for convergence of coefficients;
- normalise.

This is the paper’s thesis in one theorem, rather than in a sequence of partly overlapping descriptions.

Parts (i)–(iii), stated at this level of distributional generality and for all lower logarithmic coefficients, require an explicit mathematical assembly beyond the current pins. Part (iv) is the leading extension just discussed. None looks conceptually speculative. The statistical derivative CLT is a separate, model-dependent problem.

---

## 7. Posterior quotients are correctly organised—but should be presented as normalisation of a distribution

The block algebra over \(\mathbb R(\log N)\) is exactly right.

Keeping a rational logarithmic block intact is important. An infinite sequence
\[
1,\quad(\log N)^{-1},\quad(\log N)^{-2},\ldots
\]
intervenes before the next positive power of \(N^{-1/Q}\). The block organisation avoids pretending that a finite inverse-log truncation resolves the next algebraic order.

But this algebra should occupy less space.

A more illuminating formulation is:
\[
\mathsf Z_N^\psi
\sim
N^{-\lambda}\sum_{j\ge0}
\mathsf B_j^\psi(\ell)x^j,
\qquad
x=N^{-1/Q},\quad \ell=\log N,
\]
where each \(\mathsf B_j^\psi\) is a **distribution-valued polynomial**. Then
\[
\mathsf P_N^\psi
=
\frac{\mathsf Z_N^\psi}{\mathsf Z_N^\psi(1)}
\]
is its formal normalisation.

This highlights a feature particularly relevant to the title:

> For a fixed field, every posterior coefficient remains linear in the observable. The correction distributions have total mass zero.

It also makes visible what a posterior expectation *does not* see. Any component common to numerator and denominator can cancel. The numerator’s first nonzero coefficient is not the whole story; normalisation centres successive coefficients.

The source and cumulant discussion is sound, useful, and classical. Keep the source identity and one variance formula; move the recursion and remainder bookkeeping to the algebra appendix.

### A limit statement should not have a moving object on the right

The displayed
\[
\E[f\mid D_n]\longrightarrow\langle f\rangle_{\hat\psi_n}
\]
mixes frozen and diagonal language.

Use instead:

- frozen field:
  \[
  \frac{Z_N[f;\psi]}{Z_N[1;\psi]}\to\Pi_\psi(f);
  \]
- empirical diagonal:
  \[
  \E[f\mid D_n]-\Pi_{\psi_n}(f)\to0
  \quad\text{in probability};
  \]
- Gaussian limit:
  \[
  \E[f\mid D_n]\Rightarrow\Pi_G(f).
  \]

This separation should be maintained everywhere.

---

## 8. The Gaussian model is useful; the spin-glass analogy should be modest

The compact-base Gibbs model is legitimate and well chosen for Gaussian differentiation. Stein’s identity, the radial variable, and replica notation make the calculations efficient.

But it is not a mean-field spin-glass limit in any substantive sense merely because it has Gaussian disorder and replicas. There is no automatically relevant thermodynamic limit, overlap hierarchy, or replica-symmetry-breaking problem here.

Call these **Gaussian Gibbs identities**, with spin-glass techniques as a source, rather than making the analogy part of the conceptual thesis.

### Compactification is geometry, not a further statistical input

The conclusion currently groups the compact-base identification with statistical inputs “that the geometry cannot supply.” That is not right.

- Convergence of the empirical process is statistical.
- Separating normal sides and extending the leading measure across integrable corners is geometric/analytic.
- Matching the two leading formulas is a compatibility theorem.

A compact resolved branch space over the prior support is a natural route to putting the leading object inside the compact-base model. This deserves a lemma, not treatment as a mysterious gap.

### The variance threshold has a sharper statistical interpretation

The \(v<2\) calculation is correct. But the paper should explain that, in the usual realizable standard form, the variance on the zero divisor is typically **exactly \(2\)** under the normalisation used here.

Formally, write
\[
\log(q/p)=u^k a(X,u),\qquad \E a(X,u)=u^k.
\]
Expanding likelihood normalisation
\[
\E e^{-u^k a(X,u)}=1
\]
under appropriate remainder control gives
\[
\E a(X,u)^2\to2
\]
as \(u^k\to0\). Thus the limiting root field has pointwise variance \(2\) on the divisor.

The precise derivation requires the relevant integrability hypotheses; it should be proved or cited rather than asserted from analyticity alone. But its consequence is important:

> Non-integrability of the limiting evidence is not an exotic high-variance possibility. In standard realizable models it occurs at the natural critical variance.

That makes the exact identity \(\E Z_n[1]=\int\varphi\) and the contrast with bounded posterior expectations much more illuminating.

Finally, boundedness proves convergence of averaged **leading posterior values**, not termwise averaging of subleading quotient coefficients. The draft knows this; the distinction should be prominent.

---

## 9. What is genuinely new?

I would insist on separating **new to this paper**, **newly formalised**, and **new to mathematics**.

### Classical, or substantially already present

The following are not new mathematical principles:

- smooth-amplitude power-log asymptotics after resolution;
- meromorphic distributional continuation and polar coefficients;
- delta derivatives and finite parts in normal-crossing coordinates;
- highest-pole residues and leading positive measures;
- observables annihilating leading coefficients;
- Watanabe’s standard form, fluctuation function, Gaussian field, and leading random radial object;
- formal division, source logarithms, and cumulants;
- Gaussian integration by parts and covariance interpolation;
- the special-function identities for \(S_\mu\).

The stratum measure construction is a valuable presentation, but “positive functional gives a measure, whose local density is a residue” is classical machinery, not a new kind of invariant.

Similarly, calling observable-dependent cancellation “wall-crossing” does not make it a new wall-crossing theory.

### Plausibly substantive contributions

The strongest claims available are:

1. **A unified all-orders empirical expansion for smooth observables and root fields**, with field-uniform remainder bounds.
2. **A coefficient-level formulation that makes the complete empirical theory a universal transformation of population polar data.**
3. **A systematic posterior-observable interpretation**, including normalisation, lower logarithms, and normal jets.
4. **A machine-checked development** connecting these layers.
5. Possibly useful particular Gaussian identities and examples, without suggesting that their underlying calculus is new.

I would not certify priority for the all-orders empirical theorem without a more specific literature comparison. It is a natural consequence of classical Mellin machinery once formulated correctly, but “natural consequence” and “already written down with the required uniformity and statistical interfaces” are different claims.

The related-work section must move forward and become more exact. It should say which aspects are being reproved constructively and formally, which extend Watanabe’s leading analysis, and which are a synthesis.

# II. What would make it beautiful?

## 10. The single change with the greatest effect

**Put the polar-distribution theorem and formula \((*)\) near the beginning, and make the rest of the paper explain them.**

This would change the reading experience from:

> many charts, strata, admissibility conditions, measures, exceptions, then finally a zeta function explaining them,

to:

> one invariant object, one universal empirical operation, and increasingly concrete ways to evaluate it.

That is the difference between an extensive account and a definitive one.

---

## 11. A concrete revised architecture

I would aim for the following.

### 1. What a posterior expectation sees

Give the thesis, the main theorem in an accessible version, and one complete \(x^2y^2\) calculation through the constant logarithmic term.

State immediately what is classical and what this paper contributes.

### 2. Meromorphic distributions and normal-crossing computation

Combine the essential parts of current §§2–5.

Include:

- the intrinsic family downstairs;
- its resolved pullback;
- actual versus candidate poles;
- distributional support and finite transverse order;
- why crossing jets alone do not suffice;
- the distinction between arbitrary tests upstairs and physical observables \(f\circ\pi\).

Move elementary resolution exposition to an appendix or a short preliminary box.

### 3. Polar coefficients, residues, and finite parts

This is the mathematical centre of current §6.

Organise it as:

1. all coefficients as Laurent data;
2. highest polar coefficient and leading positive measure;
3. exact-stratum associated-graded formulas;
4. finite-part evaluation of lower coefficients;
5. observable vanishing and cancellation.

Introduce admissibility immediately before the restricted stratum formulas, not as a late repair to broad claims.

### 4. Universal radial tilting

Merge most of current §§7–8.

Keep:

- \(S_\mu\);
- the field and index derivative identities;
- formula \((*)\);
- uniform expansion theorem;
- generating identity;
- two worked empirical calculations.

Move Weber/Weyl material out.

### 5. Posterior normalisation and the sample limit

Combine the essential parts of current §§9 and 10.

State frozen, diagonal, and Gaussian-limit assertions separately. Treat quotient blocks briefly. Include source cumulants as a corollary.

### 6. What averaging does and does not preserve

A short section:

- bounded posterior convergence;
- critical failure of evidence uniform integrability;
- the two-site illustration;
- a concise statement of the Gaussian Gibbs model.

Move the full Stein/replica development to an appendix or companion paper.

### Appendices

- smooth chart proofs and uniform estimates;
- finite-part computation details;
- expansion algebra;
- special functions;
- Gaussian Gibbs identities;
- formalisation coverage.

Delete the moment-tensor appendix. It is a historical record, not a necessary part of this paper.

---

## 12. Which current sections contain the deep content?

The deepest material is:

- the invariant content of §5;
- the Laurent, residue, and finite-part parts of §6;
- the empirical generating and Mellin identities of §8;
- uniformity needed for the empirical diagonal;
- the distinction between evidence and normalised posterior in §9.

The essential statistical application is the leading posterior law plus the conditions under which the field limit transfers to it.

The principal scaffolding is:

- much of §§3–4;
- the long elementary special-function discussion;
- repeated wall-crossing explanations;
- repeated “three tiers” explanations;
- detailed quotient recursions;
- the unused tubular-neighbourhood apparatus.

The formalisation table is valuable, but the paper should not tell readers that its late table is the precise version of earlier, broader theorems. **Each theorem must state its actual mathematical hypotheses where it appears.** The table should describe coverage, not retroactively revise the theorem.

---

## 13. The examples are good, but they need different jobs

### \(x^2y^2\) on \([-1,1]^3\): keep it as the main example

It shows:

- a leading positive-dimensional locus;
- a logarithm;
- divergent lower-stratum measures;
- finite-part correction;
- \(1/\log n\) posterior decay.

But correct the statement that \(f=x^2\) is seen on the surviving plane “through its normal derivatives.” Its \(n^{-1/2}\) contribution is seen through its **restriction to \(y=0\)**. That is precisely why a jet only at the crossing is insufficient.

More importantly, give this example an actual statistical model.

For instance, take
\[
q=N_2(0,I),\qquad
p(\,\cdot\mid x,y,z)
=
N_2\!\left(\sqrt2\,xy\,v(z),I\right),
\]
where
\[
v(z)=(\cos z,\sin z).
\]
Then \(K=x^2y^2\), and the signed root field is
\[
\xi_n(z)=\sqrt2\,v(z)\cdot Z_n,
\qquad Z_n\sim N_2(0,I).
\]

After summing the normal sides,
\[
S_{1/2}(a)+S_{1/2}(-a)
=
2\sqrt\pi\,e^{a^2/4}.
\]
Thus the leading axis posterior is reweighted by
\[
\exp\!\left(\frac{(v(z)\cdot Z_n)^2}{2}\right).
\]

This one example would demonstrate:

- realizability;
- the exact field;
- orthant signs;
- tangential random redistribution;
- pointwise variance \(2\);
- finite random posterior normalisation despite divergent mean evidence weight.

It would do more work than several pages of general commentary.

### \(x^2y^6\) on \([0,1]^2\): keep it as the boundary and finite-part example

Its role should be explicit:

- one-sided normal derivatives;
- distinct exponents;
- a higher-order tie;
- an integrable nonminimal corner at leading order;
- a finite part after crossing another wall’s threshold.

State that it is a boundary chart example unless the global boundary theory is actually included in the theorem being illustrated.

### \(x^2(x^2+y^2)\): keep it, but use it to expose observability limits

It is an excellent blow-up example. Its most important lesson is:

> An exceptional curve can carry nontrivial resolved information while every downstairs smooth observable restricts to the same constant on that curve.

A positive-dimensional exceptional stratum does **not** automatically imply that the sample can move the leading value of a downstairs observable.

The correct condition is that \(f\circ\pi\) varies on the support of the leading measure—not that the resolved support has positive dimension.

### Add a very short regular sanity check

Use \(K=x^2\) on the full line with signed root field \(a\). Both sides are essential. This also resolves the draft’s statement
\[
n\,\E[K]\sim\tfrac12+\tfrac{a^2}{4}.
\]
That formula is correct for the full-line signed-field Gaussian calculation, not for a single one-sided constant absolute-root field.

This is not merely a normalisation check: it tests whether the root-field geometry is being handled correctly.

---

## 14. Notation and terminology that obscure the perspective

I would change the following.

- Use \(\mathscr T(s)\) for the meromorphic distribution and \(\mathcal M_F(s;\psi)\) for its tilted Mellin pairing. Avoid using \(\zeta\) for both zeta-related objects and the field.
- Use \(N\) consistently for the frozen asymptotic parameter, \(n\) only on the empirical diagonal.
- Replace \(\E_\infty[f]\), which still depends on \(n\), by \(\E_N^{\mathrm{pop}}[f]\).
- Distinguish the **total zero divisor** from the genuinely exceptional divisor. In the identity-resolution examples the coordinate planes are not exceptional.
- Prefer “resonance multiplicity at a point” to “exponent of a stratum” when discussing neighbourhood asymptotics. A mixed crossing need not itself carry the leading measure.
- Call the global objects “stratified conormal distributions,” or simply polar distributions, rather than suggesting that every coefficient is conormal to one smooth stratum.
- Use a common denominator such as an appropriate least common multiple rather than \(2\prod_i k_i\), unless the product is retained explicitly for formal convenience.
- Replace most uses of “wall-crossing” by “changes in the visible leading order” or “observable vanishing filtration.” There is no developed chamber or wall-crossing structure here.

Also distinguish measures determined by **all smooth tests upstairs** from information determined only by tests \(f\circ\pi\). The latter cannot distinguish different measures along fibres collapsed by \(\pi\). This matters to both uniqueness claims and the interpretation of what observables see.

---

## 15. Does Part IV belong?

Not in its current proportions.

- **Posterior normalisation belongs centrally.**
- **The leading Gaussian posterior and bounded averaging belong.**
- **The full compact-base Gaussian calculus is optional.**

My preference is to keep the leading Gibbs law, the evidence/posterior contrast, and the two-site phenomenon in the main text. Move the Stein, three-replica, inverse-evidence, and quenched-source development to an appendix.

If the compact-base identification is completed and a substantial statistical consequence follows from the interpolation identity, there is a stronger case for retaining more. At present it is a second coherent mathematical project attached to the first, rather than the culmination of it.

---

## 16. Earlier recommendations: still endorsed, with a revised priority order

I still endorse the earlier suggestions, but would order them as follows.

1. **Put the invariant object first**, now specifically the meromorphic distribution and formula \((*)\).
2. **Repair and strengthen the global leading-measure statement.** This is newly urgent; the current deeper-stratum explanation is misleading.
3. **State admissibility and divergence before restricted per-stratum assertions.** Distinguish non-extremal divergence from extremal integrability.
4. **Make every example carry its actual domain, side, support, and field hypotheses.** Add one realizable empirical example.
5. **Consolidate the three wall-crossing passages and the two “three tiers” passages.**
6. **Move the Weyl-module discussion and most of §12 to appendices.**
7. **Delete the moment-tensor appendix rather than preserving superseded language.**
8. **Make the formalisation table a coverage document, not the source of hidden theorem hypotheses.**
9. **State the limits of observability.** Downstairs pullbacks, normalisation, and coefficient cancellation are not peripheral caveats; they are part of the answer to the title.

The main additional mathematics I would request is therefore:

| Addition | Mathematical difficulty | Present formal status |
|---|---|---|
| All-log formula \((*)\) | Easy once meromorphic distributions are available | Requires a distribution/Laurent interface beyond the stated pins |
| Continuity of every lower-log coefficient | Standard finite-part estimates; moderate bookkeeping | Not covered by the cited top-graded continuity statements |
| Global leading measure across nonminimal corners | Standard local integrability plus assembly | Stronger than the stated leading-measure theorem |
| Compact branch-space identification | Moderate geometric work | Not supplied |
| Jet-level empirical CLT | Model-dependent; potentially substantial | A genuine statistical hypothesis here |
| Averaged subleading posterior expansion | Substantial; requires rates and law corrections | Properly left open |

## Verdict

**This could become a definitive account of how fixed smooth posterior observables probe singular asymptotics. It is not yet that account.**

Its best contribution is not a new theory of residues, nor a new spin-glass interpretation. It is the synthesis of classical polar-distribution asymptotics with Watanabe’s random radial tilt, carried to smooth all-orders coefficients, posterior normalisation, and unusually explicit formal verification.

To become definitive, it should stop making strata bear more conceptual weight than they can. Put the meromorphic distribution first; state the universal all-log coefficient formula; make the leading measure genuinely global; and explain what normalisation and pullback prevent an observable from seeing.

Then the exceptional divisor becomes what it should be: **a powerful geometric instrument for computing an intrinsic answer, not the answer’s ultimate location.**
================ (3) DRAFT PLAN
# Plan: the polar-distribution reorganisation (opened 2026-09-26; consult #167)

Origin. The end-to-end review of the new paper (review-log 2026-09-26, `deep_review_perspective.md`)
judged the draft "the right idea, not yet the right hierarchy". The user (2026-09-26) asked to start
preparing the reorganisation in the proposed manner: do the mathematics, formalise what needs to be
formalised, rewrite the paper around one invariant object. This file is the standing plan; update it as
steps land. Lean content pinned at d56efc8 (897 modules) unless stated.

## 0. The target hierarchy

1. **The intrinsic object downstairs.** `⟨T(s), f⟩ = ∫_W f K^{-s} φ dw`, holomorphic for `Re s < λ`,
   with a distribution-valued meromorphic continuation. Its resolved presentation is
   `T̃(s) = (K∘π)^{-s} π^*(φ dw)` with `π_* T̃ = T`. Near a positive candidate `μ`:
   `T̃(s) = Σ_{r=1}^{M_μ} A_{μ,r}/(μ−s)^r + H_μ(s)`, the `A_{μ,r}` distributions of finite transverse
   order supported on the `μ`-resonant locus.
2. **The universal radial kernel.** Mellin in `N` of the frozen partition function is
   `⟨T̃(s), F S_s(ψ)⟩` (population: `Γ(s)⟨T̃(s),F⟩`). The empirical theory is the population
   meromorphic distribution applied to the holomorphic amplitude `F S_s(ψ)`.
3. **The all-log coefficient formula (*).** For every `μ` on the lattice and `q ≤ M_μ − 1`,
   ```
   c_{μ,q}(F;ψ) = (1/q!) Σ_{r=q+1}^{M_μ} ((−1)^{r−q−1}/(r−q−1)!) ⟨ A_{μ,r}, F ∂_s^{r−q−1} S_s(ψ)|_{s=μ} ⟩,
   ```
   population case with `Γ^{(r−q−1)}(μ)` in place of the index derivative. Top log `q = M_μ−1`:
   `c = ⟨A_{μ,M_μ}, F S_μ(ψ)⟩/(M_μ−1)!` (the graded formula); the tie case `M_μ=2` gives the paper's
   `x²y²` constants.
4. **The global leading measure.** At the first pole `(λ, m)`, `A_{λ,m}` is a finite positive measure
   `ρ_λ` (extends integrably across intersections with nonminimal walls, since those have exponent
   `> λ`); for every smooth `F`, `N^λ (log N)^{−(m−1)} Z_N[F;ψ] → (1/(m−1)!) ∫ F S_λ(ψ) dρ_λ`. No
   admissibility.
5. **Normalisation.** `Z_N^ψ ~ N^{−λ} Σ_j B_j^ψ(log N) x^j` with distribution-valued polynomial blocks;
   the posterior is its formal normalisation; leading probability measure
   `Π_ψ = p_*(S_λ(ψ)ρ_λ / ∫S_λ(ψ)dρ_λ)`. Frozen / diagonal / Gaussian limits stated separately.
6. **The branch space.** Work on the real oriented blow-up of the resolution along the divisor (sides
   separated), so that "measurable field with orthantwise smooth representatives" becomes one smooth
   field on a manifold with corners, and the leading measure lives on a compact space.

## 1. Mathematics to do (paper level)

M1. Distribution-valued meromorphic continuation of `T̃(s)` on a normal-crossing chart, with pole order
    `≤ #resonant coordinates ≤ d` and Laurent coefficients `A_{μ,r}` continuous in finitely many
    derivatives of the amplitude (Taylor subtraction in each coordinate: `∫_0^b g(u) u^{a−2ks} du =
    Σ_{i<M} g^{(i)}(0) b^{a−2ks+i+1}/(i!(a−2ks+i+1)) + ∫(g − T_M g) u^{a−2ks} du`). Assemble over charts.
M2. Holomorphic amplitude families: for `G(s,u)` holomorphic in `s` near `μ`, smooth in `u`, jointly
    controlled, `s ↦ ∫ G(s,u) u^{h−2ks} du` continues with pole order `≤ M_μ` and Laurent data obtained
    by Taylor-expanding `G` in `s` to order `M_μ` (the remainder `(s−μ)^{M_μ}·(pole order ≤ M_μ)` is
    holomorphic). Apply to `G = F S_s(ψ)`. This is the proof of (*).
M3. Identification of `A_{μ,r}` with the paper's objects: `A_{μ,1}` at a simple pole = the finite-part
    face functional (tier 2); `A_{μ,c}` under the zero-order condition = `(c−1)!·ν^μ_c/Γ(μ)`·... (fix
    the exact normalisation: with `Γ(s)` factored out, `A_{μ,M}` is the residue measure `R^μ_c` up to
    sign conventions `(μ−s)^r` vs `(s−μ)^r`); lower `A_{μ,r}` = finite parts + index-derivative
    weights (the `x²y²` computation as the worked case).
M4. The global leading measure (item 4): integrability across nonminimal walls at the extremal pair;
    assembly; positivity; identification with the branchwise face limit; the compact branch space.
M5. Support and transverse order of `A_{μ,r}`: support in `{r_μ ≥ r}` (resonance count), transverse
    order `≤ n_μ` (jet dependence); descent to jet quotients (already formal for the top coefficient).
M6. Invariance: `π_* A_{μ,r}` paired with `f∘π`-type amplitudes is resolution-independent (uniqueness
    of the expansion downstairs); candidate poles are not.
M7. Variance-2 lemma: in the realisable standard form `E a(X,u)² → 2` as `u^k → 0` from
    `E e^{−u^k a} = 1`; consequence for the evidence threshold. Realisable `x²y²` model
    `p = N₂(√2 xy v(z), I)`, field `√2 v(z)·Z_n`, leading axis reweighting `exp((v(z)·Z_n)²/2)`.

## 2. Formalisation to do (grammar library)

Existing pieces to reuse: `CutoffExpansion`, `emp_cutoffExpansion`/`smooth_cutoffExpansion` (the
Laplace side), `mellin_eq_mellin_cutoffRemainderFun_add_principalParts` + `polarCoeff_unique`
(Laurent data of the Laplace integral = coefficients), `fluctuation` at complex index and
`mellinMom_pow_mul_exp_eq_iteratedDeriv` (index derivatives), bridge `mellin_frozenEvidenceObs_eq`
(Mellin of the frozen evidence = `∫ f K^{-s} S_s(ψ) φ`), `SmoothStratumMeasure`/`residueMeasure`
(the top-log measure), `EmpiricalGeneratingIdentity`, `FirstCorrection` (tier 2 at `α ≤ 1`).

F1. **Chart zeta functionals.** `chartZeta G h k (s : ℂ) = ∫_{(0,1]^d} G u u^{h−2ks} du` for smooth
    `G`; strip convergence; meromorphic continuation by coordinatewise Taylor subtraction;
    definition of `polarFunctional h k μ r : (smooth amplitudes) →ₗ ℝ` (the `A_{μ,r}` in a chart);
    pole order bound `≤ resonantCount`; continuity in `C^R` jets.
F2. **Laurent data of the Laplace chart integral through Γ.** `Γ(s)·chartZeta` has Laurent data
    `c_{μ,q}`: relate `smoothCoeff G h k 1 1 μ q` to `polarFunctional` via the Taylor coefficients of
    `Γ` at `μ` (population (*)); this identifies the face-construction coefficients with polar data
    without going through `polarCoeff_unique`, or use uniqueness to identify.
F3. **Holomorphic amplitude families (M2) at chart level**, and the empirical (*):
    `empCoeff η ζ h k μ q = (1/q!) Σ_r ((−1)^{r−q−1}/(r−q−1)!) polarFunctional μ r (η · ∂^{r−q−1}_s S_s(ζ)|_μ)`.
    Uses the chart-level Mellin identity of the frozen integral (bridge-style, easy), the pole-order
    bound, and `polarCoeff_unique`.
F4. **Resolved polar functionals.** Assemble `A_{μ,r}` over a `ResolvedCoreTransport` as functionals
    on smooth functions on `U` (orthantwise); support in `{r_μ ≥ r}`; transverse order; jet descent
    (generalise `coeff_eq_of_memIdealPow`/`descendedCoeff` from the top coefficient to all `r`).
F5. **Global leading measure (M4).** Extend `extremalStratumMeasure` across `deepZeroFibre` at the
    extremal pair: integrability of the tangential weight when all complementary walls have exponent
    `> λ`; `tendsto_normalised_partitionObs_extremal` for all smooth `f` (drop `h0`).
F6. **Branch space** (later): the real oriented blow-up as a manifold with corners; probably a
    separate seabed or a `RootField`-level abstraction first.
F7. **Variance-2 lemma (M7)** on the greybook bridge side.

Order: F1 → F2 → F3 (the mathematical centre; chart level, ~6–10 units) → F5 (independent; ~3 units)
→ F4 (~4 units) → F7; F6 deferred.

## 3. Paper reorganisation (after F1–F3 and M4 are in hand)

New architecture (per the perspective review):
1. What a posterior expectation sees — thesis, main theorem (accessible form), one complete `x²y²`
   calculation through the constant log term, what is classical / newly formalised / new.
2. Meromorphic distributions and normal-crossing computation — `T(s)`, `T̃(s)`, actual vs candidate
   poles, support and transverse order, why crossing jets alone do not suffice, tests upstairs vs
   observables `f∘π`. (Absorbs §§2–5.)
3. Polar coefficients, residues and finite parts — all coefficients as Laurent data; the leading
   positive measure (global); associated-graded formulas; finite-part evaluation; observable
   vanishing and cancellation, with admissibility introduced before the restricted statements.
4. Universal radial tilting — `S_μ`, ladder, index derivatives, (*), the uniform expansion theorem,
   generating identity, two worked empirical calculations. (Weber/Weyl to an appendix.)
5. Posterior normalisation and the sample limit — distribution-valued blocks, formal normalisation,
   frozen / diagonal / Gaussian stated separately, source cumulants as a corollary.
6. What averaging does and does not preserve — bounded posterior convergence, critical failure of
   evidence uniform integrability (variance-2 lemma), two-site illustration, Gaussian Gibbs model in
   brief. Stein/replica/inverse-evidence/quenched-source to an appendix.
Appendices: chart proofs; finite-part computations; expansion algebra; special functions; Gaussian
Gibbs identities; formalisation coverage (a coverage document, not a source of hidden hypotheses).
Delete Appendix E. Examples: `x²y²` with the realisable model; `x²y⁶` as the boundary/finite-part
chart example; `x²(x²+y²)` for observability limits; a one-line regular two-sided sanity check.
Notation: `T(s)`, `M_F(s;ψ)`; `N` frozen, `n` diagonal; `E^pop_N`; "polar distributions"; drop
"wall-crossing" and "primes"; lattice denominator lcm.

## 4. Log
- 2026-09-26: plan drafted; consult #167 requested on the route (statements, proofs, F1–F5 design).

================ (4) LEAN DEFINITIONAL CLOSURE OF THE PINNED DECLARATIONS

==================== Grammar/AbstractExpansion.lean

/-!# Abstract finite-cutoff expansions: sums, lattice refinement, ordered remainders (Stage S12)

Unit 281 (Astra #34 / review v29, assembly prerequisites). A real function `Z` of the sample size
has a **finite-cutoff expansion** on the lattice `Q⁻¹ℕ` with log degrees `≤ D`
(`CutoffExpansion Q D Z c`) if for every cutoff `L > 0` there is a constant `K` with
`|Z N − ∑_{μ ∈ Λ^Q_L} N^{-μ} ∑_{j ≤ D} c μ j (log N)^j| ≤ K N^{-L} (1 + log N)^D` eventually in `N`.
The chart-level Taylor tree provides such expansions (unit 282). This unit develops the purely
spectral bookkeeping needed to assemble charts: expansions add (`CutoffExpansion.add`,
`CutoffExpansion.sum`), a coefficient system supported on a coarser lattice `Q⁻¹ℕ ⊂ Q'⁻¹ℕ`
(`Q ∣ Q'`) gives an expansion on the finer lattice (`CutoffExpansion.refine`), a coefficient system
vanishing above degree `D` gives an expansion with any larger degree -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
open scoped Classical
end Grammar

/-- The spectral sum of an abstract coefficient system below the cutoff `L`. -/
noncomputable def absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j

/-- **Finite-cutoff expansion** of `Z` on the lattice `Q⁻¹ℕ` with log degrees `≤ D` and
coefficients `c`. -/
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop,
    |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)


==================== Grammar/BoxPeel.lean

/-!# Peeling the first coordinate of a Bochner box integral

The `ℝ≥0∞` peel `lintegral_unitBox_succ` (unit 174) has a Bochner counterpart for an arbitrary
one-dimensional measurable factor `S` and an integrable integrand:

  `∫ x in S^{d+1}, F x = ∫ a in S, ∫ b in S^d, F (Fin.cons a b)`

(`integral_pi_box_succ`), via `measurePreserving_piFinSuccAbove` at `0` and Fubini. The symmetric
box `[-1,1]^d` (interior normal coordinates) and the unit box are both instances.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
end Grammar

/-- The box `S^d` in `Fin d → ℝ`. -/
def piBox (d : ℕ) (S : Set ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => S


==================== Grammar/BoxScaling.lean

/-!# Scaling to a general box side `b` (Stage 4h)

Unit 248 (Taylor-tree programme; Astra #28 candidate D). The paper's standard integral lives on
`[0,b]^d`; substituting `u = b v` gives the exact identity
```
Z_b(N; ξ, η) = b^{|h|+d} · Z_1(N b^{2|k|}; ξ(b·), η(b·)),
```
where `ξ(b·)` has the rescaled coefficient family `c_γ b^{|γ|}` (`CoeffFamily.scale`), absolutely
summable when `∑ |c_γ| b^{|γ|} < ∞` — the weighted mass at radius `b` (`familyPhaseIntegralBox_eq`,
via the Haar scaling `Measure.integral_comp_smul`). The Taylor tree on `(0,b]^d` therefore follows
from Headline XXVII at the rescaled sample size (unit 249). No `sorry` and no additional `axiom`
declarations.-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
open MonoRep CoeffFamily
namespace CoeffFamily
variable {d : ℕ}
end CoeffFamily
end Grammar

/-- The rescaled coefficient family `c_γ b^{|γ|}` of `u ↦ ξ(b u)`. -/
noncomputable def scale (c : CoeffFamily d) (b : ℝ) : CoeffFamily d := fun γ => c γ * b ^ (∑ i, γ i)


==================== Grammar/BoxTaylorTree.lean

/-!# The Taylor tree on a general box `(0,b]^d` (Stage 4i)

Unit 249 (Taylor-tree programme; Astra #28 candidate D, second half). Combining the scaling identity
`Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))` (unit 248) with Headline XXVII at the rescaled
sample size gives, for coefficient families with finite weighted mass `∑ |c_γ| b^{|γ|}` and every
`L > 0`:

**Headline XXVIII** (`boxTaylorTree_cutoff_bound`): for `N ≥ 1` with `N b^{2|k|} ≥ 1`,
```
|Z_b(N) − b^{|h|+d} ∑_{μ ∈ Λ_L} (N b^{2|k|})^{-μ} ∑_{j ≤ d-1} A^b_{μ,j} (log(N b^{2|k|}))^j|
  ≤ b^{|h|+d} · cutoffBound · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^{d-1},
```
with `A^b_{μ,j}` the family coefficients of the rescaled data. In the sample size `N` this is
`O(N^{-L}(1+log N)^{d-1})` (`boxTaylorTree_isBigO`), and the spectral sum is `∑_μ N^{-μ} P_μ(log N)`
with
`P_μ` a polynomial of degree `≤ d-1` whose coefficients are obtained by-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Asymptotics
namespace Grammar
open MonoRep CoeffFamily
end Grammar

/-- The box coefficients
`C^b_{μ,j'} = b^{|h|+d} c^{-μ} ∑_{q ≥ j'} A^b_{μ,q} C(q,j') (log c)^{q-j'}`,
`c = b^{2|k|}`. -/
noncomputable def boxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
    ∑ q ∈ Finset.Ico j (n + 1), familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ q *
      (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j)


==================== Grammar/CoeffFamily.lean

/-!# Coefficient families and their box truncations (Stage 4c)

Unit 243 (Taylor-tree programme, Stage 4; Astra #28 §2.1–2.2). Analytic data enter through their
Taylor coefficients: a **coefficient family** `c : (Fin d → ℕ) → ℝ` with `∑_γ |c_γ| < ∞`
(`AbsSummable`), of **mass** `∑_γ |c_γ|` and **evaluation** `∑_γ c_γ u^γ`, absolutely convergent on
the
closed unit cube with `|eval c u| ≤ mass c`. The **box truncation** at level `m` is the finite
monomial list of the coefficients with all `γᵢ ≤ m` (`truncList`), a genuine `MonoRep` to which all
of
Stage 3 applies; it keeps the constant term (`eval_truncList_zero`), has list mass at most `mass c`,
and successive truncations differ by an appended list (`truncList_perm`) whose mass is at most the
**tail mass** `∑_{γ ∉ box m} |c_γ|`, which tends to `0` (`tailMass_tendsto_zero`); the truncations
converge to the family uniformly on the cube (`abs_e-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
open scoped List
namespace Grammar
open MonoRep
namespace CoeffFamily
variable {d : ℕ}
end CoeffFamily
end Grammar

/-- Coefficient families: real coefficients indexed by multi-indices. -/
abbrev CoeffFamily (d : ℕ) := (Fin d → ℕ) → ℝ

/-- The box `{γ | ∀ i, γᵢ ≤ m}` of multi-indices. -/
def boxSet (d m : ℕ) : Finset (Fin d → ℕ) := Fintype.piFinset fun _ => Finset.range (m + 1)

/-- The box truncation as a monomial list. -/
noncomputable def truncList (c : CoeffFamily d) (m : ℕ) : MonoRep d :=
  (boxSet d m).toList.map fun γ => (γ, c γ)


==================== Grammar/CompactBaseFinite.lean

/-!# Compact base II (part 1): finite reduction and the Gaussian field record

A finite-range quantisation `q` of the compact base turns every compact-base quantity of
`ρ.map q` into a finite quartet quantity over the atoms of positive mass:

* `posAtoms ρ hfin` are the atoms `a ∈ range q` with `ρ(q⁻¹{a}) > 0`, enumerated by
  `atomPt : Fin m → K` with weights `atomWt : Fin m → ℝ` (positive, summing to `ρ(K)`);
* `∫ f(q x) dρ = ∑ᵢ wᵢ f(xᵢ)` (`integral_comp_finiteRange_atoms`), so `D, M₂, H, Diag, Q, V` of
  `ρ.map q` equal `quartetD, quartetM2, quartetH, quartetDiag, quartetQ, quartetVgen` of the
  evaluation vector `g ∘ atomPt` with the kernel matrix `kernelMatrix 𝒞 atomPt`
  (`compactD_map_eq`, …, `compactV_map_eq`).

A **Gaussian field** (`GaussianField 𝒞 P`) is a random continuous function `G : Ω → C(K,ℝ)`
with measurable evaluations, a finite second sup-norm moment, and finite-dimensio-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Atoms
variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K] (ρ : Measure K)
  [IsFiniteMeasure ρ] {q : K → K}
omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
end Atoms
section Reduce
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (𝒞 : PSDKernel K) (g : C(K, ℝ)) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hq
omit 𝒞 in
omit 𝒞 in
omit 𝒞 in
omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hq in
end Reduce
namespace GaussianField
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
variable {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (hρ : ρ ≠ 0) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hρ hq hfin
end GaussianField
end Grammar

/-- A **Gaussian field** on the compact base with covariance kernel `𝒞`: a random continuous
function with measurable evaluations, a finite second sup-norm moment, and finite-dimensional
laws given by the axiom-clean `gaussianVector` construction with covariance `kernelMatrix 𝒞 x`. -/
structure GaussianField {K : Type*} [TopologicalSpace K] [CompactSpace K] (𝒞 : PSDKernel K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The random continuous function. -/
  G : Ω → C(K, ℝ)
  measurable_eval : ∀ x, Measurable fun ω => G ω x
  integrable_sq_norm : Integrable (fun ω => ‖G ω‖ ^ 2) P
  law : ∀ (m : ℕ) (x : Fin m → K), ∃ (n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ),
    A * A.transpose = 𝒞.kernelMatrix x ∧
      P.map (fun ω => fun i => G ω (x i)) = gaussianVector A

  G : Ω → C(K, ℝ)
  measurable_eval : ∀ x, Measurable fun ω => G ω x
  integrable_sq_norm : Integrable (fun ω => ‖G ω‖ ^ 2) P
  law : ∀ (m : ℕ) (x : Fin m → K), ∃ (n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ),
    A * A.transpose = 𝒞.kernelMatrix x ∧
      P.map (fun ω => fun i => G ω (x i)) = gaussianVector A

namespace GaussianField

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)

omit [MeasurableSpace K] [BorelSpace K] in
theorem measurable_evalVec {m : ℕ} (x : Fin m → K) :
    Measurable fun ω => fun i => Γ.G ω (x i) :=
  measurable_pi_lambda _ fun i => Γ.measurable_eval (x i)


==================== Grammar/CompactBaseKernel.lean

/-!# Compact base I (continued): the covariance kernel, `Q`, `V`, and their bounds

For a continuous symmetric positive-semidefinite kernel `C` on the compact base `K`
(`PSDKernel`), the compact analogues of the finite quartet are

* `compactQnum = ∫∫ C(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ` and `compactQ = compactQnum / D²`
  (the bilocal quadratic form `⟨√(rs) C(x,y)⟩` over two replicas);
* `compactDiag = ∫ C(x,x) S_{λ+1}(g x) dρ / D` (the diagonal term `⟨r C(x,x)⟩`);
* `compactV = compactDiag − compactQ` (the connected two-point function).

Main results (all for `g ∈ C(K,ℝ)` with `‖g‖_∞ ≤ R`):

* **finite quantisation transfers positivity**: on a finitely supported pushforward `ρ.map q` the
  integral is a finite sum (`integral_comp_finiteRange`), so `compactQnum (ρ.map q) ≥ 0` is the
  finite PSD inequality (`compactQnum_map_nonneg`); `compactQnum` is continuous under quantisation
  -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
namespace PSDKernel
variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)
end PSDKernel
section Finite
variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K] (ρ : Measure K)
  [IsFiniteMeasure ρ]
end Finite
section Kernel
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ}
variable (ρ : Measure K) [IsFiniteMeasure ρ]
variable (hβ : 0 < β) (hlam : 0 < lam) (𝒞 : PSDKernel K) (g : C(K, ℝ))
include hβ hlam
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
omit hβ hlam in
omit 𝒞 in
omit 𝒞 in
end Kernel
end Grammar

/-- A continuous symmetric positive-semidefinite kernel. -/
structure PSDKernel (K : Type*) [TopologicalSpace K] where
  /-- The kernel. -/
  C : K → K → ℝ
  symm : ∀ x y, C x y = C y x
  psd : ∀ (m : ℕ) (x : Fin m → K) (v : Fin m → ℝ),
    0 ≤ ∑ i, ∑ j, C (x i) (x j) * v i * v j
  continuous : Continuous (Function.uncurry C)

  C : K → K → ℝ
  symm : ∀ x y, C x y = C y x
  psd : ∀ (m : ℕ) (x : Fin m → K) (v : Fin m → ℝ),
    0 ≤ ∑ i, ∑ j, C (x i) (x j) * v i * v j
  continuous : Continuous (Function.uncurry C)

namespace PSDKernel

variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)

theorem diag_nonneg (x : K) : 0 ≤ 𝒞.C x x := by
  have := 𝒞.psd 1 (fun _ => x) (fun _ => 1)
  simpa using this

  continuous : Continuous (Function.uncurry C)

namespace PSDKernel

variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)

theorem diag_nonneg (x : K) : 0 ≤ 𝒞.C x x := <proof>

theorem continuous_diag : Continuous fun x => 𝒞.C x x := <proof>


==================== Grammar/CompactBaseQuantise.lean

/-!# Compact base I: finite quantisation and the compact-base denominator

For a nonempty compact metric space `K` with a finite Borel measure `ρ`, the finite-resolution
quantities of the quartet have compact-base analogues: `D_ρ(g) = ∫_K S_λ(g(x)) dρ(x)`,
`M₂,ρ(g) = ∫ S_{λ+1}(g)/D`, `H_ρ(g) = ∫ g S_{λ+1/2}(g)/D`. This file provides

* **finite quantisation** (`exists_measurable_finiteRange_approx`): for every `ε > 0` a measurable
  map `q : K → K` with finite range and `dist x (q x) < ε` (Mathlib's nearest-point simple
  functions along a dense sequence, with a finite subcover to fix the depth); the pushforward
  `ρ.map q` is a mass-preserving finitely supported approximation of `ρ`;
* **partition-independent deterministic bounds** in terms of `R = ‖g‖_∞` and `M = ρ(K)`:
  `M e^{−2β} λ^{−1}(1+R)^{−2λ} ≤ D_ρ(g) ≤ M e^{βR²/2}(β/2)^{−λ}Γ(λ)` (`compactD_le`, `le_compactD`),
  hence `D_ρ(g) > 0-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Quantise
variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K]
omit [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K] in
omit [Nonempty K] in
omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] in
end Quantise
section CompactD
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ}
variable (ρ : Measure K) [IsFiniteMeasure ρ]
omit [CompactSpace K] [IsFiniteMeasure ρ] in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
end CompactD
end Grammar

/-- `D_ρ(g) = ∫_K S_λ(g(x)) dρ(x)`. -/
noncomputable def compactD (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  ∫ x, fluctuation β lam (g x) ∂ρ


==================== Grammar/CompactBaseResponse.lean

/-!# Covariance interpolation for the averaged posterior mean on the compact base (§20)

For a centred Gaussian field `G` with kernel `𝒞` on the compact base `K`, the averaged limit
posterior mean of a continuous observable `f` differs from the zero-field mean `ρ(f)/ρ(K)` by the
integral of the **mean response** along the covariance scale:

★★★ `GaussianField.integral_compactAvg_eq`:
`E⟨f⟩_G = ρ(f)/ρ(K) + ∫₀¹ E[H_f(√s G)] ds`,

`H_f(g) = (β²/2)[(T_g(f c_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞 f) − ⟨f⟩_g B_g(𝒞))]`
(`compactMeanResponse`), with the radial-moment–weighted integrals
`T_g(φ) = ∫ φ S_{λ+1}(g) dρ / D_ρ(g)` (`compactTimeMoment`, `= ⟨φ t⟩_g`), the bilocal
`B_g(h) = ∫∫ h(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ / D_ρ(g)²` (`compactBilocal`,
`= ⟨h(x₁,x₂)√t₁√t₂⟩^{⊗2}_g`), the diagonal `c_Δ(x) = 𝒞(x,x)` and `(𝒞f)(x,y) = 𝒞(x,y) f(y)`.
In replica language
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Defs
variable {K : Type*} [MeasurableSpace K]
end Defs
section Kernel
variable {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)
end Kernel
section Bounds
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
include hβ hlam
end Bounds
section Quantised
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (g : C(K, ℝ)) {q : K → K} (hq : Measurable q)
include hβ hlam hq
omit [CompactSpace K] [IsFiniteMeasure ρ] in
variable (hfin : (Set.range q).Finite)
include hfin
end Quantised
section Convergence
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ)) {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ}
  (hε : Tendsto ε atTop (𝓝 0)) (hqε : ∀ n x, dist x (q n x) < ε n)
include hβ hlam hρ hq hε hqε
end Convergence
namespace GaussianField
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ
section Quantised
variable {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hq hfin
omit [IsProbabilityMeasure P] in
omit [IsProbabilityMeasure P] in
omit [IsProbabilityMeasure P] in
omit [IsProbabilityMeasure P] in
end Quantised
section Limit
variable [Nonempty K]
end Limit
end GaussianField
end Grammar

/-- `T_g(φ) = ∫ φ S_{λ+1}(g) dρ / D_ρ(g)`, the radial-first-moment–weighted integral `⟨φ t⟩_g`. -/
noncomputable def compactTimeMoment (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β (lam + 1) ρ g φ / compactD β lam ρ g

/-- `B_g(h) = ∫∫ h(x,y) S_{λ+1/2}(g x) S_{λ+1/2}(g y) dρ dρ / D_ρ(g)²`, the bilocal
`⟨h(x₁,x₂)√t₁√t₂⟩^{⊗2}_g`. -/
noncomputable def compactBilocal (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) (h : K × K → ℝ) : ℝ :=
  (∫ z, h z * fluctuation β (lam + 1 / 2) (g z.1) * fluctuation β (lam + 1 / 2) (g z.2)
    ∂(ρ.prod ρ)) / compactD β lam ρ g ^ 2

/-- The diagonal `x ↦ 𝒞(x,x)` as a continuous map. -/
noncomputable def kernelDiag : C(K, ℝ) := ⟨fun x => 𝒞.C x x, 𝒞.continuous_diag⟩

/-- The kernel as a continuous map on `K × K`. -/
noncomputable def kernelFun : C(K × K, ℝ) := ⟨fun z => 𝒞.C z.1 z.2, 𝒞.continuous⟩

/-- `(x,y) ↦ 𝒞(x,y) f(y)` as a continuous map. -/
noncomputable def kernelObs (f : C(K, ℝ)) : C(K × K, ℝ) :=
  ⟨fun z => 𝒞.C z.1 z.2 * f z.2, 𝒞.continuous.mul (f.continuous.comp continuous_snd)⟩

/-- The **mean response** of a continuous observable:
`H_f(g) = (β²/2)[(T_g(f c_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞f) − ⟨f⟩_g B_g(𝒞))]`. -/
noncomputable def compactMeanResponse [MeasurableSpace K] (β lam : ℝ) (ρ : Measure K)
    (𝒞 : PSDKernel K) (f : C(K, ℝ)) (g : K → ℝ) : ℝ :=
  β ^ 2 / 2 * ((compactTimeMoment β lam ρ g (f * kernelDiag 𝒞 : C(K, ℝ)) -
      compactAvg β lam ρ g f * compactTimeMoment β lam ρ g (kernelDiag 𝒞)) -
    2 * (compactBilocal β lam ρ g (kernelObs 𝒞 f) -
      compactAvg β lam ρ g f * compactBilocal β lam ρ g (kernelFun 𝒞)))

/-- ★ **The mean response is quadratically dominated**:
`|H_f(g)| ≤ 5β² ‖f‖ c (2λ/β + 1/4)(1 + ‖g‖²)` when `𝒞(x,x) ≤ c`. -/
theorem abs_compactMeanResponse_le (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, 𝒞.C x x ≤ c) (f : C(K, ℝ)) (g : C(K, ℝ)) :
    |compactMeanResponse β lam ρ 𝒞 f g| ≤
      5 * β ^ 2 * ‖f‖ * c * (2 * lam / β + 1 / 4) * (1 + ‖g‖ ^ 2) := <proof>

/-- ★★★ **Covariance interpolation for the averaged posterior mean on the compact base**:
`E⟨f⟩_G = ρ(f)/ρ(K) + ∫₀¹ E[H_f(√s G)] ds` for every centred Gaussian field with kernel `𝒞`
and every continuous observable `f`. -/
theorem integral_compactAvg_eq (f : C(K, ℝ)) :
    ∫ ω, compactAvg β lam ρ (Γ.G ω) f ∂P =
      (∫ x, f x ∂ρ) / ρ.real univ + ∫ s in (0 : ℝ)..1,
        ∫ ω, compactMeanResponse β lam ρ 𝒞 f (Real.sqrt s • Γ.G ω : C(K, ℝ)) ∂P := <proof>


==================== Grammar/CompactBaseStein.lean

/-!# Stein's identity for posterior averages on the compact base (§20, replicas)

For a Gaussian field `G` on the compact base `K` with covariance kernel `𝒞` and the limit
posterior `⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)` (`compactAvg`), the Gaussian integration-by-parts
identity for the posterior average of a continuous observable `f` reads

★★★ `GaussianField.integral_eval_mul_compactAvg`:
`E[G(x₀) ⟨f⟩_G] = β E[⟨f · 𝒞(x₀,·)√t⟩_G − ⟨f⟩_G ⟨𝒞(x₀,·)√t⟩_G]`,

where `⟨φ√t⟩_g = ∫ φ S_{λ+1/2}(g) dρ / D_ρ(g)` (`compactSqrtTimeMoment`) is the posterior average of
`φ(x)√t` on the joint Gibbs measure `μ_g(dx dt) ∝ t^{λ−1} e^{−βt + βg(x)√t} dρ dt`.  This is
`E[G(x₀) F(G)] = E[DF(G)[𝒞(x₀,·)]]` with the Fréchet derivative
`DF_f(g)[h] = β(⟨f √t h⟩_g − ⟨f⟩_g ⟨√t h⟩_g)` of the posterior average (Astra #162 §5): the
one-covariance-line identity whose two-replica form is
`β E⟨f(x₁)(√t₁ 𝒞(x₀,x₁) − √t₂ 𝒞(x₀,x₂))⟩^{⊗2-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Defs
variable {K : Type*} [MeasurableSpace K]
end Defs
section Bounds
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
include hβ hlam
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hlam in
variable (g : C(K, ℝ)) {q : K → K} (hq : Measurable q)
include hq
omit [CompactSpace K] [IsFiniteMeasure ρ] hlam in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
omit [CompactSpace K] [IsFiniteMeasure ρ] in
variable (hfin : (Set.range q).Finite)
include hfin
omit hq hfin in
omit hq hfin in
end Bounds
section Aux
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
end Aux
namespace GaussianField
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ
omit [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
section Quantised
variable {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hq hfin
omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
omit [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ hq in
end Quantised
section Limit
variable [Nonempty K]
omit hρ [Nonempty K] in
omit hρ [Nonempty K] in
omit [Nonempty K] in
omit [Nonempty K] in
omit [IsFiniteMeasure ρ] hρ [Nonempty K] in
variable [IsProbabilityMeasure P] {q : ℕ → K → K} (hq : ∀ n, Measurable (q n))
  (hfin : ∀ n, (Set.range (q n)).Finite) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
  (hqε : ∀ n x, dist x (q n x) < ε n)
include hq hfin hε hqε
omit [Nonempty K] in
omit [Nonempty K] in
omit hq hfin hε hqε in
end Limit
end GaussianField
end Grammar

/-- The posterior average of `φ(x) √t`: `⟨φ√t⟩_g = ∫ φ S_{λ+1/2}(g) dρ / D_ρ(g)`. -/
noncomputable def compactSqrtTimeMoment (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β (lam + 1 / 2) ρ g φ / compactD β lam ρ g

/-- The kernel section `x ↦ 𝒞(x₀, x)` as a continuous map. -/
noncomputable def kernelSection (𝒞 : PSDKernel K) (x₀ : K) : C(K, ℝ) :=
  ⟨fun x => 𝒞.C x₀ x, 𝒞.continuous.comp (Continuous.prodMk_right x₀)⟩

/-- ★★★ **Stein's identity for posterior averages on the compact base**:
`E[G(x₀) ⟨f⟩_G] = β E[⟨f 𝒞(x₀,·)√t⟩_G − ⟨f⟩_G ⟨𝒞(x₀,·)√t⟩_G]`, i.e.
`E[G(x₀) F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]` with `DF_f(g)[h] = β(⟨f√t h⟩_g − ⟨f⟩_g⟨√t h⟩_g)`. -/
theorem integral_eval_mul_compactAvg (f : C(K, ℝ)) (x₀ : K) :
    ∫ ω, Γ.G ω x₀ * compactAvg β lam ρ (Γ.G ω) f ∂P =
      β * ∫ ω, (compactSqrtTimeMoment β lam ρ (Γ.G ω) (f * kernelSection 𝒞 x₀ : C(K, ℝ)) -
        compactAvg β lam ρ (Γ.G ω) f *
          compactSqrtTimeMoment β lam ρ (Γ.G ω) (kernelSection 𝒞 x₀)) ∂P := <proof>


==================== Grammar/CubeJets.lean

/-!# Jets on a cube and the top cube coefficient on the closed realizable jets

`CubeJetSpace d R b`: for every order `r ≤ R`, a continuous `r`-multilinear-map-valued function
on the closed box `[0,b]^d` (a `def` with one normed-group instance). `cubeJet R b ζ hζ` is the jet
of a smooth field; `cubeRealizable` its range. The top coefficient of the cube expansion is a
well-defined function of the realizable jets of order `R ≥ R₀ = ∑ depthOf h k (cutoffOf h μ)`,
Lipschitz on bounded parts (`exists_empCoeffRect_top_bound`), hence extends continuously to the
closed realizable jets (`cubeCoeffOnClosedJets`, via `closureExtend`), and convergence in
distribution of random closed cube jets transfers to the coefficient
(`tendstoInDistribution_cubeCoeff_top_closed`).

This is the single-cube analogue of `EmpiricalBranchJets`/`EmpiricalClosedJets`, the target of the
grey-book bridge (consult #151, M5)-/

-- section/variable skeleton:
open Filter Topology Set MeasureTheory
open scoped ContDiff
namespace Grammar
open SmoothEngine
variable {d : ℕ}
section Coeff
variable {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
open Classical in
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
end Coeff
end Grammar

/-- The jets of order `≤ R` on the closed cube `[0,b]^d`. -/
def CubeJetSpace (d R : ℕ) (b : ℝ) : Type :=
  ∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)

noncomputable instance instNormedAddCommGroupCubeJetSpace (R : ℕ) (b : ℝ) :
    NormedAddCommGroup (CubeJetSpace d R b) :=
  inferInstanceAs (NormedAddCommGroup (∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

noncomputable instance instMeasurableSpaceCubeJetSpace (R : ℕ) (b : ℝ) :
    MeasurableSpace (CubeJetSpace d R b) :=
  borel _

/-- The cube jet of a smooth field. -/
noncomputable def cubeJet (R : ℕ) (b : ℝ) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    CubeJetSpace d R b :=
  fun r => ⟨fun x => iteratedFDeriv ℝ r.1 ζ x.1,
    (hζ.continuous_iteratedFDeriv (natCast_le_infty _)).comp continuous_subtype_val⟩


==================== Grammar/CutoffQuotientExpansion.lean

/-!# The quotient of two cutoff expansions to all orders (§20, posterior expectations)

Two cutoff expansions `Z₁, Z₂` on the lattice `Q⁻¹ℕ` (log degree `≤ D`) whose coefficients vanish
below the common leading index `m₀` (`VanishBelow`), with the denominator's leading block
`b₀(log N) = Σ_q c₂(m₀/Q, q) (log N)^q` bounded away from zero, have

★★★ `cutoff_div_isBigO`:
`Z₁(N)/Z₂(N) = Σ_{j<J} R_j(log N) N^{−j/Q} + O(N^{−J/Q} (1 + log N)^{D(J+1)})`,

where `R_j(L) = quotientBlocks (a_·(L)) (b_·(L)) j` are the pointwise quotient blocks of the
block polynomials `a_j(L) = Σ_q c₁((m₀+j)/Q, q) L^q`, `b_j` likewise (`blockPoly`).  This is the
deterministic all-orders expansion of the posterior expectation `E_N[φ]/E_N[1]` as exact
rational-log blocks (consult #158 item 3, #159 B(ii)); the first correction and its probabilistic
form live in the bridge (`Bridge/PosteriorQuotient`).

Route: `absSpectral-/

-- section/variable skeleton:
open Filter Topology Asymptotics Finset
namespace Grammar
variable {Q D : ℕ} {c : ℝ → ℕ → ℝ} {Z : ℝ → ℝ}
end Grammar

/-- Vanishing below the leading lattice index `m₀`: `c (m/Q) q = 0` for `m < m₀`. -/
def VanishBelow (Q : ℕ) (c : ℝ → ℕ → ℝ) (m₀ : ℕ) : Prop :=
  ∀ m : ℕ, m < m₀ → ∀ q, c ((m : ℝ) / Q) q = 0

/-- The `j`-th block polynomial above the leading index:
`blockPoly Q D c m₀ j L = Σ_{q≤D} c((m₀+j)/Q, q) L^q`. -/
noncomputable def blockPoly (Q D : ℕ) (c : ℝ → ℕ → ℝ) (m₀ j : ℕ) (L : ℝ) : ℝ :=
  ∑ q ∈ range (D + 1), c (((m₀ + j : ℕ) : ℝ) / Q) q * L ^ q

/-- ★★★ **The quotient of two cutoff expansions to all orders, with the denominator's leading
block nonzero**: the eventual lower bound of `cutoff_div_isBigO` is automatic once some
coefficient `c₂(m₀/Q, q)` is nonzero. -/
theorem cutoff_div_isBigO' (hQ : 0 < Q) {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂) {m₀ : ℕ}
    (hv₁ : VanishBelow Q c₁ m₀) (hv₂ : VanishBelow Q c₂ m₀) {J : ℕ} (hJ : 1 ≤ J)
    (hne : ∃ q ∈ range (D + 1), c₂ ((m₀ : ℝ) / Q) q ≠ 0) :
    (fun N : ℝ => Z₁ N / Z₂ N - ∑ j ∈ range J,
        quotientBlocks (fun i => blockPoly Q D c₁ m₀ i (Real.log N))
          (fun i => blockPoly Q D c₂ m₀ i (Real.log N)) j * (N ^ (-(1 / (Q : ℝ)))) ^ j)
      =O[atTop] fun N : ℝ => (N ^ (-(1 / (Q : ℝ)))) ^ J * ((1 + Real.log N) ^ D) ^ (J + 1) := <proof>


==================== Grammar/DensityTransfer.lean

/-!# The finite density-transfer theorem (grammar §4.2, from state density to asymptotics)

An abstract, finite, quantitative version of "a power-log expansion of the state density transfers
to a power-log asymptotic expansion of the partition function". Let

  `Z(N) = ∫₀^R e^{-β(Nr)²} ρ(r, Nr) dr`

with a two-variable density `ρ(r, s)` (`r` the monomial radius, `s` the kernel parameter,
specialised to `s = Nr` only at transfer time). If for `0 < r ≤ R`, `s > 0`

  `ρ(r, s) = ∑ᵢ r^{αᵢ-1} (log(1/r))^{jᵢ} cᵢ(s) + E(r, s)`,
  `|E(r, s)| ≤ r^{a-1} (1+|log r|)^J H(s)`,

with `0 < αᵢ < a`, `jᵢ ≤ J` and finite weighted moments, then for `N ≥ 1`

  `Z(N) = ∑ᵢ N^{-αᵢ} ∑_{m ≤ jᵢ} C(jᵢ,m) (log N)^m (-1)^{jᵢ-m} M_{i, jᵢ-m} + O(N^{-a} (1 + log N)^J)`

with the log moments `M_{i,ℓ} = ∫₀^∞ s^{αᵢ-1} (log s)^ℓ e^{-βs²} cᵢ(s) ds` and an explicit constant
(`densityTransfer_bound`). Three elementary mechanisms-/

-- section/variable skeleton:
open Real MeasureTheory Set Filter Topology
namespace Grammar
end Grammar

/-- The log moments `M_ℓ = ∫₀^∞ s^{α-1} (log s)^ℓ e^{-βs²} c(s) ds`. -/
noncomputable def logMoment (β α : ℝ) (ℓ : ℕ) (c : ℝ → ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2) * c s)


==================== Grammar/EmpiricalBoxScaling.lean

/-!# The empirical expansion on a general rectangle: the exact scaling adapter
(§20 unit 5 of consult #142)

The empirical integral on a rectangle `∏ᵢ (0, bᵢ]` reduces EXACTLY to the unit box by the diagonal
scaling `v = (bᵢ uᵢ)`: with `A_b = ∏ bᵢ^{hᵢ+1}` and `B_b = ∏ bᵢ^{2kᵢ}`,
`Z_b(N; η, ζ) = A_b · Z_1(B_b N; η∘b, ζ∘b)` (★ `empIntegralRect_eq`) — the coupling transforms
correctly because `√N v^k = √(B_b N) u^k`, so NO rescaling of the field is needed. Consequently the
rectangle integral is a `CutoffExpansion` on the same lattice `(2∏kᵢ)⁻¹ℕ` with the same logarithmic
degree `d − 1` (★★ `empRect_cutoffExpansion`), with the explicit coefficients
`empCoeffRect = A_b · scaleCoeff (d−1) B_b (empCoeff (η∘b) (ζ∘b))`, i.e.
`c^b_{μq} = A_b B_b^{−μ} ∑_{j≥q} C(j,q) (log B_b)^{j−q} c^1_{μj}(η∘b, ζ∘b)` (the coefficient law of
consult #142), and they are canonical (`empCoeffRect_unique`). The cube `(0,b-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
end SmoothEngine
end Grammar

/-- The diagonal scaling `u ↦ (bᵢ uᵢ)` as a plain function. -/
def diag (b : Fin d → ℝ) (u : Fin d → ℝ) : Fin d → ℝ := fun i => b i * u i

/-- The rectangle coefficients: `A_b · scaleCoeff (d−1) B_b (empCoeff (η∘b) (ζ∘b))`. -/
noncomputable def empCoeffRect (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (b : Fin d → ℝ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  ((∏ i, b i) * mono h b) *
    scaleCoeff (d - 1) (mono (fun i => 2 * k i) b) (empCoeff (η ∘ diag b) (ζ ∘ diag b) h k) μ q


==================== Grammar/EmpiricalBranchJets.lean

/-!# The branch-jet topology and the coefficient map (§20, consult #145 interface)

The fixed-index topology on smooth root fields in which the resolved coefficient at `(μ, c − 1)` is
continuous: the **branch jets** `branchJet μ ξ` — for every piece `p` and every order `r ≤ R_p(μ)`
the continuous map `x ↦ D^r L_p(x)` on the compact chart image `K_p` — living in the finite product
`BranchJetSpace μ` of the Banach spaces `C(K_p, CMM_r)` (sup norms). Closeness of the jets is
exactly the `JetClose` hypothesis of the continuity theorem (`jetClose_of_norm_branchJet_sub_le`,
`norm_branchJet_sub_le`), and jet bounds are norm bounds (`jetBoundOn_of_norm_branchJet_le`). The
coefficient factors through the jets (`resolvedCoeff_eq_of_branchJet_eq`, from the local Lipschitz
bound with `ε = 0`), defining `coeffOnJets` on the REALIZABLE jets `range (branchJet μ)`; it is
continuous there (★★ `continuous_co-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The branch-jet space at index `μ`: for every piece and every order `r ≤ R_p(μ)`, a continuous
`r`-multilinear-map-valued function on the compact chart image. A `def` (not an abbreviation), so
that all its structure comes from the single normed-group instance below. -/
def BranchJetSpace (μ : ℝ) : Type :=
  ∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
    ContinuousMap (Ξ.chartImage Y p) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)

noncomputable instance instNormedAddCommGroupBranchJetSpace (μ : ℝ) :
    NormedAddCommGroup (Ξ.BranchJetSpace Y μ) :=
  inferInstanceAs (NormedAddCommGroup (∀ p : (Ξ.X Y).PIdx, ∀ r : Fin (Ξ.pieceOrder Y p μ + 1),
    ContinuousMap (Ξ.chartImage Y p) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

noncomputable instance instMeasurableSpaceBranchJetSpace (μ : ℝ) :
    MeasurableSpace (Ξ.BranchJetSpace Y μ) :=
  borel _

instance instBorelSpaceBranchJetSpace (μ : ℝ) : BorelSpace (Ξ.BranchJetSpace Y μ) := ⟨rfl⟩

/-- The restricted branch jets of a smooth root field. -/
noncomputable def branchJet (μ : ℝ) (ξ : Ξ.SmoothRootField Y) : Ξ.BranchJetSpace Y μ :=
  fun p r => ⟨fun x => iteratedFDeriv ℝ r.1 (ξ.Lψ p) x.1,
    ((ξ.Lψ_smooth p).continuous_iteratedFDeriv (natCast_le_infty _)).comp continuous_subtype_val⟩

/-- The resolved coefficient at `(μ, c − 1)` as a function on the realizable branch jets. -/
noncomputable def coeffOnJets (μ : ℝ) (c : ℕ) (x : Set.range (Ξ.branchJet Y μ)) : ℝ :=
  (Classical.choose x.2).resolvedCoeff μ (c - 1)


==================== Grammar/EmpiricalCoeffDistribution.lean

/-!# The conditional random-field theorem for the subleading coefficients (§20, consult #145 (3))

For random smooth root fields `ξₙ : Ω → SmoothRootField` whose realizable branch jets
`realizableJet μ (ξₙ ω)` converge in distribution, in the metric space of realizable jets
`RealizableJets μ ⊆ BranchJetSpace μ`, to a random realizable jet `G`, the resolved empirical
coefficients at the top pair `(μ, c − 1)` of an observable vanishing near `D_{c+1}` converge in
distribution to `coeffOnJets μ c ∘ G` (★★ `tendstoInDistribution_resolvedCoeff_top`) — the
continuous-mapping theorem applied to the continuous coefficient map on the realizable jets. The
statement is conditional: the substantive probabilistic input, convergence in distribution of the
branch jets of the empirical root fields in this finite-order topology (with joint convergence
across pieces), is a hypothesis, not a theorem of this de-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
end ResolvedData
end SmoothEngine
end Grammar

/-- The realizable branch jets at index `μ`, as a metric space. -/
abbrev RealizableJets (μ : ℝ) : Type := Set.range (Ξ.branchJet Y μ)

/-- The branch jets of a field as a realizable jet. -/
noncomputable def realizableJet (μ : ℝ) (ξ : Ξ.SmoothRootField Y) : Ξ.RealizableJets Y μ :=
  ⟨Ξ.branchJet Y μ ξ, ⟨ξ, rfl⟩⟩

/-- ★★ **The conditional random-field theorem**: if the realizable branch jets of random smooth
root fields converge in distribution to a random realizable jet `G`, the resolved coefficients
at `(μ, c − 1)` converge in distribution to `coeffOnJets μ c ∘ G`. -/
theorem tendstoInDistribution_resolvedCoeff_top {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ)
    (ξ : ℕ → Ω → Ξ.SmoothRootField Y) {G : Ω' → Ξ.RealizableJets Y μ}
    (hLG : TendstoInDistribution (fun n w => Ξ.realizableJet Y μ (ξ n w)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution (fun (n : ℕ) w => (ξ n w).resolvedCoeff μ (c - 1)) atTop
      (fun w' => Ξ.coeffOnJets Y μ c (G w')) (fun _ => P) P' := <proof>


==================== Grammar/EmpiricalFaceFunctional.lean

/-!# The empirical face functional and its identification with the spatial face functional

`faceFunctional h k l b ξ η = 1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J, w) S_l(ξ(0_J, w)) ·
∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−l} dw` is the limit of the empirical box integral on
`(0,b]^d` in the form of the empirical stratum measure (`J` the coordinates of ratio `l`,
`m = |J|`).
This module shows that the dilated spatial face functional of Headline XIX equals it
(`spatialFace_dilated_eq_faceFunctional`), by scaling the unit box to `(0,b]^d`, splitting the
coordinates into `J` and `Jᶜ`, and converting `phaseMoment` to the fluctuation function. Zero
`sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
open SmoothEngine in
section
variable {d : ℕ}
end
end Grammar

/-- The resonant coordinates `J_l = {i | (h_i+1)/(2k_i) = l}`. -/
noncomputable def resSet (h k : Fin d → ℕ) (l : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => ratioExp h k i = l

/-- The empirical face functional on the box `(0,b]^d` at temperature one:
`1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J,w) S_l(ξ(0_J,w)) residueWeight(w) dw`. -/
noncomputable def faceFunctional (h k : Fin d → ℕ) (l b : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i ∈ resSet h k l, (2 * (k i : ℝ)))) *
    ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
      η (glue (resSet h k l) 0 w) * fluctuation 1 l (ξ (glue (resSet h k l) 0 w)) *
        residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w


==================== Grammar/EmpiricalFaceInner.lean

/-!# The empirical inner kernel on a general finite index type (§20 Stage 5, part 1)

`empFaceInner k e G t = ∫_{(0,1]^ι} u^e G(√t u^k) e^{−t u^{2k}} du` on an arbitrary finite index
type `ι` — the inner integral of a face `J` of the box, `ι = {i // i ∈ J}`. On `Fin (n+1)` it is
`empUnitInner` (`empFaceInner_fin`), it is invariant under reindexing (`empFaceInner_reindex`,
transport along `piCongrLeft`), and on the EMPTY index type it is `G(√t) e^{−t}`
(`empFaceInner_isEmpty`). The two-regime estimate of `EmpiricalInnerTwoRegime` transports to every
nonempty `ι` (★ `empFaceInner_two_regime`) with spectrum `faceSpectrum k e L ⊆ (2∏kᵢ)⁻¹ℕ ∩ [0,L)`
and coefficients `faceInnerCoeff k e G` (linear in `G`, bounded by `A` times a constant, vanishing
off the spectrum); on the empty type the estimate holds with EMPTY spectrum
(`empFaceInner_isEmpty_two_regime`, from the master kernel bound `jet_kerne-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
namespace Grammar
namespace SmoothEngine
variable {ι : Type*} [Fintype ι]
end SmoothEngine
end Grammar

/-- The face coefficient system, through the reindexing `faceEquiv`. -/
noncomputable def faceInnerCoeff [Nonempty ι] (k e : ι → ℕ) (G : ℝ → ℝ) : ℝ → ℕ → ℝ :=
  empInnerCoeff (k ∘ (faceEquiv ι).symm) (e ∘ (faceEquiv ι).symm) G


==================== Grammar/EmpiricalFaceSumCollapse.lean

/-!# The empirical face-sum collapse at the top logarithmic power: the graded empirical Theorem E
in a box (§20 units 3–4 of consult #142)

**Top spectral coefficient.** On a face all of whose coordinates resonate exactly with `μ`
(`2kᵢμ = eᵢ + 1`), the empirical face coefficient at the top logarithmic power `|J| − 1` is
`(∏_{i∈J} 1/(2kᵢ)) / (|J|−1)! · mellinMom G μ 0` (`empInnerCoeff_top_of_exact`, from the top
coefficient `1/(m−1)!` of the state density), and it vanishes if some coordinate fails exact
resonance (`empInnerCoeff_top_eq_zero_of_not_exact`); at log degrees `≥ |J|` every face coefficient
vanishes (`empFaceCoef_eq_zero_of_card_le`). Packaged as `resonantTop`:
★ `empFaceCoef_top : empFaceCoef k J e G μ (DJ J) = resonantTop k J e μ * mellinMom G μ 0`.

**Depth flatness.** If `η` vanishes near the deep set `{≥ c+1 vanishing coordinates}` then so does
`η e^{τζ}` for every `τ`, its -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
section Inner
variable {n : ℕ} (k e : Fin (n + 1) → ℕ)
end Inner
variable {d : ℕ}
variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
end SmoothEngine
end Grammar

/-- The resonant top constant of a face `J`: `(∏_{i∈J} 1/(2kᵢ)) / (|J|−1)!` if every coordinate of
`J` resonates exactly with `μ` (`2kᵢμ = eᵢ + 1`), `0` otherwise. -/
noncomputable def resonantTop (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) (μ : ℝ) : ℝ :=
  if ∀ j ∈ J, 2 * (k j : ℝ) * μ = e j + 1 then
    (∏ i : {i // inJ J i}, 1 / (2 * (k i : ℝ))) / ((J.card - 1).factorial : ℝ)
  else 0

/-- **Deep vanishing within the box**: `η` vanishes near every point of the deep set
`{≥ c+1 vanishing coordinates}` of `[0,b]^d`, on the closed box. This is the form in which the
chart amplitudes vanish (they are arbitrary smooth extensions off the chart box). -/
def DeepVanishing (η : (Fin d → ℝ) → ℝ) (b : ℝ) (c : ℕ) : Prop :=
  ∀ v ∈ deepSet d b c, ∀ᶠ w in 𝓝 v, w ∈ closedBox d b → η w = 0

/-- ★★★ **The empirical face-sum collapse at the top logarithmic power**: for `η` vanishing near
the deep set `{≥ c+1 vanishing coordinates}` and `μ > 0`, the empirical coefficient at `(μ, c−1)`
is the sum over the faces of size `c` of
`faceW · resonantTop · ∫_{face} ∂_J^{α_J}[η · S_μ(ζ)](0_J, w) · (power weight)`. -/
theorem empCoeff_eq_faceSum_top (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (resonantTop k J (fun i => resOrder h k μ J i + h i) μ *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J)
                (fun v => η v * fluctuation 1 μ (ζ v)) (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) 1 μ 0) := <proof>

/-- ★★ **Vanishing above the depth**: for `η` vanishing near the deep set, the empirical
coefficients of log degree `≥ c` vanish. -/
theorem empCoeff_eq_zero_of_deep (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {μ : ℝ} {c : ℕ}
    (hdeep : DeepVanishing η 1 c) {q : ℕ} (hq : c ≤ q) :
    empCoeff η ζ h k μ q = 0 := <proof>

/-- ★★★ **The replacement rule**: the empirical top coefficient is the population top coefficient
of the amplitude `η · S_μ(ζ)/Γ(μ)` — exponent by exponent, the field enters through the
fluctuation function evaluated on the field. -/
theorem empCoeff_top_eq_smoothCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hdeep : DeepVanishing η 1 c) :
    empCoeff η ζ h k μ (c - 1) =
      smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Real.Gamma μ) h k 1 1 μ (c - 1) := <proof>


==================== Grammar/EmpiricalFieldFamilyJets.lean

/-!# Jets of the empirical field family `B_τ(v) = η(v) e^{τ ζ(v)}` (§20 Stage 4)

The empirical integrand is the population amplitude `η` times the exponential of the root field
`ζ` at the effective coupling `τ = √N v^k`. Its coordinate derivatives are JETS: polynomials in
`τ` with smooth coefficient functions times `e^{τ ζ}` (`IsJet`; `∂_i` raises the degree by one,
`IsJet.pd`, so `∂^m` has degree `|m|`, `IsJet.pdMulti`). On the closed box a jet of degree `R`
is bounded by `C (1+τ)^R e^{M'τ}` when `|ζ| ≤ M'` (`IsJet.bound`), uniformly over all
multi-indices `m ≤ p` (★ `exists_pdMulti_fieldFam_bound`). Consequently the face amplitudes
`G_{J,m}(τ; w) = (R_K^p ∂^m B_τ)(0_J, w)` satisfy the FLAT GROWTH bound
`|G_{J,m}(τ; w)| ≤ (∏_K 1/(pᵢ−1)!) · C · w^{p_K} · (1+τ)^{|p|} e^{M'τ}`
(★ `growthLE_faceAmp_fieldFam`, the hypothesis of the empirical face theorem) and are jointly
measurable in `(w, τ)`-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable {η ζ : (Fin d → ℝ) → ℝ}
end SmoothEngine
end Grammar

/-- The empirical field family `B_τ(v) = η(v) e^{τ ζ(v)}`. -/
noncomputable def fieldFam (η ζ : (Fin d → ℝ) → ℝ) (τ : ℝ) (v : Fin d → ℝ) : ℝ :=
  η v * exp (τ * ζ v)

/-- The rectangular jet bound of the field family: `|∂^m B_τ(v)| ≤ C (1+τ)^{|p|} e^{M'τ}` for all
`m ≤ p`, `τ ≥ 0` and `v` in the closed box. This is the only way `(η, ζ)` enter the constants of
the empirical expansion. -/
def FieldJetBound (η ζ : (Fin d → ℝ) → ℝ) (p : Fin d → ℕ) (b C M' : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
    |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤ C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ)


==================== Grammar/EmpiricalFieldJets.lean

/-!# The jets of `η e^{τξ}` and the fluctuation-function ladder

For smooth `η, ξ : ℝ → ℝ` and a parameter `τ`, the `j`-th derivative of `v ↦ η(v) e^{τ ξ(v)}` is
`P_j(v, τ) e^{τ ξ(v)}` with `P_j` a polynomial of degree `≤ j` in `τ` whose coefficients
`jetCoeff η ξ j r` are smooth functions of `v` defined by the recursion
`p_{0,0} = η`, `p_{j+1,r} = p_{j,r}' + ξ' p_{j,r−1}` (`iteratedDeriv_mul_exp_field`). On a compact
`v`-interval, `|P_j(v, τ)| ≤ C_j (1 + τ)^j` for `τ ≥ 0` (`exists_jetPoly_bound`).

Differentiating `η(v) S_μ(ξ(v)) = ∫ s^{μ−1} e^{−s} η(v) e^{√s ξ(v)} ds` under the integral gives
★★ `iteratedDeriv_mul_fluctuation`:
`∂_v^j [η · S_μ∘ξ] = ∫ s^{μ−1} e^{−s} P_j(v, √s) e^{√s ξ(v)} ds`, the exact form in which the
normal jets of the field enter the empirical coefficients: each power `τ^r = s^{r/2}` of the
field-derivative polynomial shifts the fluctuation index by `r/2` (the ladder -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable (η ξ : ℝ → ℝ)
variable {η ξ}
variable (η ξ) in
end SmoothEngine
end Grammar

/-- The coefficient functions `p_{j,r}` of `∂_v^j[η e^{τξ}] = (∑_r p_{j,r}(v) τ^r) e^{τξ(v)}`. -/
noncomputable def jetCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => η
  | 0, _ + 1 => fun _ => 0
  | j + 1, 0 => deriv (jetCoeff j 0)
  | j + 1, r + 1 => fun v => deriv (jetCoeff j (r + 1)) v + deriv ξ v * jetCoeff j r v

/-- The field-derivative polynomial `P_j(v, τ) = ∑_{r ≤ j} p_{j,r}(v) τ^r`. -/
noncomputable def jetPoly (j : ℕ) (v τ : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1), jetCoeff η ξ j r v * τ ^ r


==================== Grammar/EmpiricalGeneral.lean

/-!# The empirical expansion: canonical coefficients (§20 Stage 6)

The depth-`p` empirical expansions of `EmpiricalGeneralDepth` are made DEPTH-FREE exactly as for
the population engine (`SmoothGeneral`): for the cutoff `L ≥ L₀ = ∑hᵢ + 1` the depth
`pᵢ = 2kᵢL − hᵢ` is admissible, the bound `|ζ| ≤ M'` on the closed box exists by compactness, and
two admissible depths give the same coefficients below their common cutoff by finite uniqueness.
The canonical coefficient `empCoeff η ζ h k μ q` uses the deterministic cutoff
`max(⌊μ⌋+1, L₀)`, and ★★★ `emp_cutoffExpansion`: the EMPIRICAL integral
`∫_{(0,1]^d} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)} dv` is a `CutoffExpansion` on the lattice
`Q⁻¹ℕ`, `Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and coefficients `empCoeff` — the same
interface as the population engine, so ★★ `empCoeff_unique` (any cutoff expansion has these
coefficients). Only smoothness-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
end SmoothEngine
end Grammar

/-- The empirical integral `∫_{(0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`. -/
noncomputable def empIntegral (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
    exp (-N * mono (fun i => 2 * k i) v)

/-- ★★★ **The canonical empirical coefficients**: the depth-`2kL−h` coefficients at the
deterministic cutoff `L = max(⌊μ⌋₊ + 1, L₀)`. -/
noncomputable def empCoeff (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (μ : ℝ) (q : ℕ) : ℝ :=
  empCoeffAtDepth η ζ h k (depthOf h k (cutoffOf h μ)) μ q

/-- ★★★ **The empirical integral is a cutoff expansion** on the lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, with
logarithmic degree `≤ d − 1` and the canonical coefficients `empCoeff`: for every `L > 0` there is
`K` with
`|∫_{(0,1]^d} η v^h e^{−N v^{2k} + √N v^k ζ} dv`
`  − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} empCoeff μ q (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` eventually in `N`. -/
theorem emp_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) (empCoeff η ζ h k) := <proof>

/-- ★★ **Canonicity**: any cutoff expansion of the empirical integral on the lattice `Q⁻¹ℕ` with
logarithmic degree `≤ d − 1` has the coefficients `empCoeff`. -/
theorem empCoeff_unique (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (empIntegral η ζ h k) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = empCoeff η ζ h k μ j := <proof>


==================== Grammar/EmpiricalGeneralDepth.lean

/-!# The empirical expansion in general dimension at a fixed depth (§20 Stage 5)

For smooth `η, ζ` on the closed unit box with `|ζ| ≤ M'`, the EMPIRICAL integrand
`η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}}` is split by the subset formula applied to the field family
`B_τ = η e^{τζ}` at the pointwise coupling `τ = √N v^k` (`empFaceTerm_pointwise`); the `J`-face term
integrates, after the `u/w` split of the box and the identity `√N (uw)^k = √(N w^{2k_K}) u^{k_J}`,
to a finite sum of empirical face integrals
`∫_w w^{h_K} · empFaceInner k_J (m+h_J) (τ ↦ G_{J,m}(τ; w)) (N w^{2k_K}) dw`
(★ `empFaceTerm_integral`, `integral_eq_sum_empFaceIntegral`). Each is expanded by the
parametrised face theorem with the two-regime estimate of `EmpiricalFaceInner` and the flat growth
of `EmpiricalFieldFamilyJets` (★ `empFace_bound`), and `reorganise'` collects everything into ONE
coefficient system `empCoeffAtDept-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
section FaceData
variable (k : Fin d → ℕ) (L : ℝ) (J : Finset (Fin d))
end FaceData
variable (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ)
variable {η ζ}
end SmoothEngine
end Grammar

/-- The empirical face coefficients of a field factor `G` (zero for the empty face). -/
noncomputable def empFaceCoef (e : Fin d → ℕ) (G : ℝ → ℝ) : ℝ → ℕ → ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceInnerCoeff (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) G
  else fun _ _ => 0

/-- The pointwise coupling `τ = √N v^k`. -/
noncomputable def coupling (k : Fin d → ℕ) (N : ℝ) (v : Fin d → ℝ) : ℝ := Real.sqrt N * mono k v

/-- ★ **The empirical coefficient system at depth `p`** on the ambient lattice: for each face
`(J, m)`, the binomially reindexed face coefficient integrals of the empirical face coefficients of
the face amplitude family. -/
noncomputable def empCoeffAtDepth (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (μ : ℝ) (q : ℕ) :
    ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q) *
    faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)


==================== Grammar/EmpiricalGeneratingIdentity.lean

/-!# The all-orders generating identity, chart-wise (§20, coordinate-free programme)

For smooth `η, ζ` on the unit box the canonical empirical coefficients of the exponential field
family are the exponential generating series of *population* coefficients with the monomial
insertions `η ζ^r` at the half-integer shifted exponents:

★★★ `hasSum_empCoeff_population`:
`Σ_{r ≥ 0} (1/r!) · empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q = empCoeff η ζ h k μ q`
(unconditionally convergent), for every `μ ∈ Q⁻¹ℕ` and `q ≤ d − 1`; equivalently with the
insertion `η (u^k ζ)^r` and the unshifted monomial `h` (`hasSum_empCoeff_population_mono`).

Route (truncation, no series/integral interchange): `fieldFam = Σ_{r<R} (1/r!) expTermFam r +
tailFam R` pointwise; the family coefficients are linear (by uniqueness of cutoff expansions,
`empCoeffAtDepthFam_add/const_mul`) and `O(C)` for a family with jet bound `C`-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)
end SmoothEngine
end Grammar

/-- ★★★ **The all-orders generating identity, chart-wise on the unit box**: for every
`μ ∈ Q⁻¹ℕ` and `q ≤ d − 1`,
`Σ_{r ≥ 0} (1/r!) · empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q = empCoeff η ζ h k μ q`
(unconditionally convergent). -/
theorem hasSum_empCoeff_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q)
      (empCoeff η ζ h k μ q) := <proof>


==================== Grammar/EmpiricalInnerKernel.lean

/-!# The empirical inner kernel on the unit box, through the state density

For a measurable field factor `G : ℝ → ℝ` of at most polynomial-exponential growth
`|G(τ)| ≤ A (1+τ)^m e^{Mτ}` (`GrowthLE`), the **empirical inner kernel**
`I_G(t) = ∫_{(0,1]^{n+1}} u^e G(√t u^k) e^{−t u^{2k}} du`
is, by the exact state density `v` of the monomial `u^{2k}` under the weight `u^e`
(`integral_unitBox_monomial_eq_stateDensity`), the one-dimensional integral
`∏ 1/(2kᵢ) ∫₀¹ v(z) G(√(tz)) e^{−tz} dz`; and since `v(z) = ∑ c z^{μ−1} (−log z)^j` is an explicit
finite power–log sum, the substitution `z = s/t` turns every term into
`c t^{−μ} ∑_{q ≤ j} C(j,q) (log t)^q ∫₀^t s^{μ−1} (−log s)^{j−q} G(√s) e^{−s} ds`
(★★ `empUnitInner_eq_series`): the multivariate inner kernel is a finite combination of the
**log-weighted Mellin moments** `mellinMom G μ ℓ = ∫₀^∞ s^{μ−1}(−log s)^ℓ G(√s) e^{−s} ds` of the
field factor-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {n : ℕ}
end SmoothEngine
end Grammar

/-- The moment kernel `s^{μ−1} (−log s)^ℓ · G(√s) e^{−s}`. -/
noncomputable def momKernel (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) (s : ℝ) : ℝ :=
  s ^ (μ - 1) * (-log s) ^ ℓ * (G (Real.sqrt s) * exp (-s))

/-- The log-weighted Mellin moment `∫₀^∞ s^{μ−1} (−log s)^ℓ G(√s) e^{−s} ds`. -/
noncomputable def mellinMom (G : ℝ → ℝ) (μ : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), momKernel G μ ℓ s

/-- The state-density weights `(eᵢ+1)/(2kᵢ) − 1` of the monomial `u^{2k}` under `u^e`. -/
noncomputable def sdWeights (k e : Fin (n + 1) → ℕ) : Fin (n + 1) → ℝ :=
  fun i => ((e i : ℝ) + 1) / (2 * (k i : ℝ)) - 1


==================== Grammar/EmpiricalInnerTwoRegime.lean

/-!# The empirical inner kernel as a power–log system with a global two-regime estimate

The exact series of `EmpiricalInnerKernel` is regrouped by exponent into the coefficient system
`empInnerCoeff k e G μ q = ∏ 1/(2kᵢ) ∑_j coeffAt(rep) μ j · C(j,q) · mellinMom G μ (j−q)` on the
spectrum `exps = {(eᵢ+1)/(2kᵢ)}` (`empInnerSeries_eq_powLog`). Every moment is bounded by `A` times
a moment of the growth envelope (`abs_mellinMom_le`), so the coefficients are `O(A)`; and for every
cutoff `L > 0` the kernel satisfies the GLOBAL two-regime estimate
`|I_G(t) − powLog (exps ∩ {μ < L}) n (empInnerCoeff k e G) t| ≤ A · C · t^{−L} (1 + |log t|)^n`
for all `t > 0` (★★ `empUnitInner_two_regime`), with `C` depending only on `k, e, m, M, L` — exactly
the inner hypothesis `hZ2` of the generic face theorem `face_expansion`, linear in the growth
constant of the field factor. The kernel is measurable in `t` (-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {n : ℕ}
end SmoothEngine
end Grammar

/-- The coefficient system of the inner kernel:
`c μ q = ∏ 1/(2kᵢ) ∑_{j ≤ n} coeffAt(rep) μ j · C(j,q) · mellinMom G μ (j−q)`. -/
noncomputable def empInnerCoeff (k e : Fin (n + 1) → ℕ) (G : ℝ → ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * ∑ j ∈ Finset.range (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (sdWeights k e)) μ j * (j.choose q : ℝ) *
      mellinMom G μ (j - q)


==================== Grammar/EmpiricalMonomialFamily.lean

/-!# The monomial amplitude families and the shifted population coefficients (§20, generating identity)

The `r`-th term of the exponential series `η e^{τζ} = Σ_r τ^r η ζ^r / r!` is the monomial family
`A_r(τ, v) = τ^r η(v) ζ(v)^r` (`expTermFam`).  It is a jointly smooth amplitude family with the jet
bound `|∂^m A_r(τ, ·)| ≤ C r! (1+τ)^{|p|} e^{τ}` (`exists_famJetBound_expTermFam`), so the family
depth engine applies at the SAME depth `p` as the empirical coefficient.  Its integral is the
population integral with the monomial absorbed into the weight, times `N^{r/2}`
(`integral_expTermFam`), and by uniqueness of cutoff expansions its depth-`p` coefficient at
`(μ, q)`
is the canonical population coefficient at the shifted exponent `μ + r/2`
(★★ `empCoeffAtDepthFam_expTermFam_eq`):

  `empCoeffAtDepthFam (τ^r η ζ^r) h k p μ q = empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q`.

The half-integer sh-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} {h k p : Fin d → ℕ}
end SmoothEngine
end Grammar

/-- The monomial `v ↦ v^k` is smooth. -/
theorem contDiff_mono (k : Fin d → ℕ) : ContDiff ℝ ∞ (mono k) := <proof>


==================== Grammar/EmpiricalOneDim.lean

/-!# The one-dimensional empirical smooth engine

For smooth `η, ξ : ℝ → ℝ`, `k ≥ 1`, `h ≥ 0` and `b > 0`, the one-dimensional empirical integral
`Z(N) = ∫_0^b η(u) u^h e^{−N u^{2k} + √N u^k ξ(u)} du` has the full no-log cutoff expansion
`Z(N) = ∑_{j ≤ q} C_j N^{−μ_j} + O(N^{−L})`, `μ_j = (h+j+1)/(2k)`, with
`C_j = ∂_u^j [η(u) S_{μ_j}(ξ(u))]|_{u=0} / (j! · 2k)` (★★★ `empOneDim_expansion`): the
coefficients are the normal jets of `η · S_μ∘ξ`, so derivatives of the fluctuation function enter
through the chain rule (`iteratedDeriv_mul_fluctuation`). At `ξ = 0` these are the population
coefficients `η^{(j)}(0) Γ(μ_j)/(j!·2k)` of `oneDim_smooth`.

Proof: substitute `u = N^{−1/2k} x`, Taylor-expand `v ↦ η(v) e^{x^k ξ(v)}` at `v = 0` for fixed `x`
(the jets `P_j(0, x^k) e^{x^k ξ(0)}` of `EmpiricalFieldJets`), extend the coefficient integrals to
`(0, ∞)` (tails `O(e^{−bN^{1/2k}/2})`) and bound the -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology intervalIntegral
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable (η ξ : ℝ → ℝ)
variable {η ξ}
variable (η ξ) in
end SmoothEngine
end Grammar

/-- The one-dimensional empirical integral `∫_0^b η(u) u^h e^{−N u^{2k} + √N u^k ξ(u)} du`. -/
noncomputable def empOneDim (h k : ℕ) (b N : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..b, η u * u ^ h * exp (-N * u ^ (2 * k) + Real.sqrt N * u ^ k * ξ u)

/-- The coefficient at `N^{−μ_j}`, `μ_j = (h+j+1)/(2k)`: `∂_u^j[η · S_{μ_j}∘ξ](0)/(j!·2k)`. -/
noncomputable def empOneDimCoeff (h k j : ℕ) : ℝ :=
  iteratedDeriv j (fun v => η v * fluctuation 1 (lam k (j + h)) (ξ v)) 0 /
    ((j.factorial : ℝ) * (2 * k))

/-- The kernel constant `n! e^{1+(M+1)²/2}` of the master bound. -/
noncomputable def kernelConst (n : ℕ) (M : ℝ) : ℝ := (n.factorial : ℝ) * exp (1 + (M + 1) ^ 2 / 2)

/-- The explicit constant of the one-dimensional expansion: it depends on the field data only
through the bound `M ≥ ξ` and the jet bounds `C_j` (so it is uniform over families sharing
those bounds). -/
noncomputable def oneDimExpConst (h k q L : ℕ) (b M : ℝ) (Cj : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (q + 1), 2 * Cj j * kernelConst (h + 2 * j) M / (j.factorial : ℝ)) *
    (max 1 ((2 * k * L).factorial : ℝ) * (2 / b) ^ (2 * k * L)) +
  Cj (q + 1) / (q.factorial : ℝ) * kernelConst (h + 2 * q + 2) M *
    ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2)

/-- ★★★ **The one-dimensional empirical expansion with an explicit constant**: under the bound
`ξ ≤ M` on `[0, b]` and the jet bounds `|P_j(v, τ)| ≤ C_j (1+τ)^j` on `[0, b]`, for `N ≥ 1` with
`b N^{1/2k} ≥ 1` and `2kL ≤ q + 1 + h`,
`|Z(N) − Σ_{j ≤ q} C_j N^{−μ_j}| ≤ oneDimExpConst · N^{−L}`. -/
theorem empOneDim_expansion_of_bounds (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ)
    {k : ℕ} (hk : 0 < k) {b : ℝ} (hb : 0 < b) (q L : ℕ) (hqL : 2 * k * L ≤ q + 1 + h) {M : ℝ}
    (hM' : ∀ t ∈ Icc 0 b, ξ t ≤ M) {Cj : ℕ → ℝ}
    (hCj : ∀ j, 0 ≤ Cj j ∧ ∀ v ∈ Icc 0 b, ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j v τ| ≤ Cj j * (1 + τ) ^ j)
    {N : ℝ} (hN : 1 ≤ N) (hX : 1 ≤ b * N ^ (1 / (2 * (k : ℝ)))) :
    |empOneDim η ξ h k b N -
        ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h))| ≤
        oneDimExpConst h k q L b M Cj * N ^ (-(L : ℝ)) := <proof>

/-- ★★★ **The one-dimensional empirical smooth expansion**: for smooth `η, ξ`, `k ≥ 1`, `b > 0` and
`2kL ≤ q + 1 + h`, there is `C` with
`|∫_0^b η u^h e^{−Nu^{2k} + √N u^k ξ} du − ∑_{j ≤ q} empOneDimCoeff_j N^{−(h+j+1)/2k}| ≤ C N^{−L}`
for all `N ≥ 1` with `b N^{1/2k} ≥ 1`, where
`empOneDimCoeff_j = ∂_u^j[η(u) S_{(h+j+1)/2k}(ξ(u))]|_{u=0} / (j! · 2k)`. -/
theorem empOneDim_expansion (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) {b : ℝ} (hb : 0 < b) (q L : ℕ) (hqL : 2 * k * L ≤ q + 1 + h) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → 1 ≤ b * N ^ (1 / (2 * (k : ℝ))) →
      |empOneDim η ξ h k b N -
        ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h))| ≤
        C * N ^ (-(L : ℝ)) := <proof>

/-- The first correction exhibits the ladder: with `μ = μ_1 = (h+2)/2k`,
`C_1 = (η'(0) S_μ(ξ(0)) + η(0) ξ'(0) S_{μ+1/2}(ξ(0))) / 2k`. -/
theorem empOneDimCoeff_one (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    empOneDimCoeff η ξ h k 1 = (deriv η 0 * fluctuation 1 (lam k (1 + h)) (ξ 0) +
      η 0 * deriv ξ 0 * fluctuation 1 (lam k (1 + h) + 1 / 2) (ξ 0)) / (2 * k) := <proof>


==================== Grammar/EmpiricalPieceIntegral.lean

/-!# The empirical piece integral: transport, domination and leading term

For a piece `p` of the resolved chart transport and a root field `ξ`, the empirical core integral
`∫ F e^{−N K∘π + √N √(K∘π) ψ} dcoreMeasure_p` is transported to the box:
`∫_{Base} empBoxIntegral h k N b (loc_p(s,·)) (amp s) dν(s)` (`integral_coreMeasure_empIntegrand`).
The fibrewise integrals are dominated by `e^{M²/2} A · empBoxIntegral h k (N/2) b 0 1`
(`abs_empBoxIntegral_le`), whose normalisation is eventually bounded, so by dominated convergence
the empirical piece integral has the leading term `∫_{Base} boxFaceLimit(s) dν(s)` at a
chart-leading pair (`hasLeadingTerm_empPieceInt`). Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
variable {d : ℕ}
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The empirical integrand `e^{−N K∘π + √N √(K∘π) ψ} · F` on `U`. -/
noncomputable def empIntegrand (ξ : Ξ.RootField Y) (N : ℝ) (P : Ξ.R.U) : ℝ :=
  Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P) * Ξ.F P

/-- The face limit of a piece at the pair `(λ, m)`, at the base point `s`. -/
noncomputable def pieceFaceLimit (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m (Y.T.a p.1) (fun v => ξ.loc p (s, v))
    fun v => (Ξ.amp Y p).amp s v

/-- The chart-leading condition: every piece is chart-leading at `(λ, m)`. -/
def ChartLeading (lam : ℝ) (m : ℕ) : Prop :=
  ∀ p : (Ξ.X Y).PIdx, BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m


==================== Grammar/EmpiricalPieceLeading.lean

/-!# The empirical box integral on `(0,b]^d`: leading term at a chart-leading pair

`empBoxIntegral h k N b ξ η = ∫_{(0,b]^d} η u^h e^{−N u^{2k} + √N u^k ξ(u)} du` (temperature one,
any `d`, `ξ` continuous). At a pair `(λ, m)` which is **chart-leading** for the box (all ratios
`(h_i+1)/2k_i ≥ λ`, at most `m` of them equal to `λ`; `BoxLeading`), the normalised integral
converges to the **box face limit**: the empirical face functional if exactly `m` coordinates
have ratio `λ`, and `0` otherwise (`tendsto_empBoxIntegral_div_boxFaceLimit`). The case `d = 0`
(no active coordinate) is exponentially small. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
variable {d : ℕ}
end Grammar

/-- The chart-leading condition for a box at the pair `(λ, m)`. -/
def BoxLeading (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) : Prop :=
  (∀ i, lam ≤ ratioExp h k i) ∧ multCount (ratioExp h k) lam ≤ m

/-- The box face limit at `(λ, m)`: the empirical face functional when the box realises the
multiplicity `m`, and `0` otherwise. -/
noncomputable def boxFaceLimit (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) (b : ℝ)
    (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  if multCount (ratioExp h k) lam = m then faceFunctional h k lam b ξ η else 0


==================== Grammar/EmpiricalResolvedContinuity.lean

/-!# Continuity of the resolved empirical coefficients in the branch representatives
(§20, consult #144 unit C)

For smooth root fields `ξₙ → ξ` whose branch representatives converge on every piece in
`C^{R_p}` on the compact chart image `K_p` of the piece (`chartImage`: all chart points
`Tm p s v`, `s` in the base, `v` in the closed piece box; `R_p = pieceOrder`, the canonical depth
of the piece at `μ`), the resolved empirical coefficient at the top power `(μ, c − 1)` of an
observable vanishing near `D_{c+1}` converges (★★★ `tendsto_resolvedCoeff_top`). Route: the
affine chart map of a piece is `v ↦ T v + s'` with `‖T‖ ≤ 1` (`affineLin`, `affineMap_eq_lin_add`,
`norm_affineLin_le`), so jets transfer along it without loss (`iteratedFDeriv_comp_affineMap`,
`norm_iteratedFDeriv_comp_affineMap_le`, `jetBoundOn_comp_affineMap`, `jetClose_comp_affineMap`)
— uniformly in the base point; the repla-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
section Affine
variable {d da : ℕ} {J : Finset (Fin d)} (e : Fin da ≃ {i // inJ J i})
  (σ : WaterFilling.CoordSign d)
variable {L L₁ L₂ : (Fin d → ℝ) → ℝ}
end Affine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The chart image of a piece: all chart points `Tm p s v` with `s` in the base and `v` in the
closed piece box. -/
def chartImage (p : (Ξ.X Y).PIdx) : Set (Fin d → ℝ) :=
  (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
    (Ξ.X Y).Tm p z.1 z.2) '' (univ ×ˢ closedBox ((Ξ.X Y).da p) (Y.T.a p.1))

/-- The canonical order of a piece at `μ`: the total canonical depth
`Σ (2kᵢ·cutoffOf h μ − hᵢ)` of the piece exponents. -/
noncomputable def pieceOrder (p : (Ξ.X Y).PIdx) (μ : ℝ) : ℕ :=
  ∑ i, depthOf ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (cutoffOf ((Ξ.X Y).hA p) μ) i

/-- ★★ **Local Lipschitz control of the resolved coefficient on jet-bounded data**. -/
theorem exists_resolvedCoeff_top_bound {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ ξ₁ ξ₂ : Ξ.SmoothRootField Y,
      (∀ p, JetBoundOn (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₂.Lψ p) B) →
      ∀ ε, 0 ≤ ε → ε ≤ 1 →
      (∀ p, JetClose (Ξ.pieceOrder Y p μ) (Ξ.chartImage Y p) (ξ₁.Lψ p) (ξ₂.Lψ p) ε) →
      |ξ₁.resolvedCoeff μ (c - 1) - ξ₂.resolvedCoeff μ (c - 1)| ≤ K * ε := <proof>


==================== Grammar/EmpiricalResolvedExpansion.lean

/-!# The resolved empirical expansion: empirical Theorem E on the resolved manifold
(§20 Stage 7, part 3)

A **smooth root field** is a root field whose branch representative on every piece is the pull-back
of a smooth function on the chart coordinate space along the affine chart map of the piece
(`SmoothRootField`: `loc p (s, v) = Lψ p (Tm p s v)`, smooth up to the walls, sector sign absorbed
piece by piece). For a bounded smooth root field the empirical partition function
`Z^emp_N[F; ψ] = ∫_U F e^{−N K∘π + √N √(K∘π) ψ} dμ_U` decomposes into the empirical piece integrals
and an exponentially small tail (`empZ_eq_sum`, `abs_integral_tail_le`); each piece integral is the
base integral of the rectangle kernels of its piece field family and has the cutoff expansion of
`EmpiricalPieceExpansion` on its chart lattice (★ `empPieceInt_cutoffExpansion`); refined to the
common lattice and padded to t-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
namespace SmoothRootField
variable {Ξ Y} (ξ : Ξ.SmoothRootField Y)
end SmoothRootField
end ResolvedData
end SmoothEngine
end Grammar

/-- A **smooth root field**: a root field whose branch representatives are pull-backs of smooth
functions on the chart coordinate spaces along the affine chart maps of the pieces. -/
structure SmoothRootField extends Ξ.RootField Y where
  /-- the smooth chart representative of the field on the piece -/
  Lψ : (Ξ.X Y).PIdx → (Fin d → ℝ) → ℝ
  Lψ_smooth : ∀ p, ContDiff ℝ ∞ (Lψ p)
  loc_eq_Lψ : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    loc p z = Lψ p ((Ξ.X Y).Tm p z.1 z.2)

structure SmoothRootField extends Ξ.RootField Y where
  /-- the smooth chart representative of the field on the piece -/
  Lψ : (Ξ.X Y).PIdx → (Fin d → ℝ) → ℝ
  Lψ_smooth : ∀ p, ContDiff ℝ ∞ (Lψ p)
  loc_eq_Lψ : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    loc p z = Lψ p ((Ξ.X Y).Tm p z.1 z.2)

  Lψ : (Ξ.X Y).PIdx → (Fin d → ℝ) → ℝ
  Lψ_smooth : ∀ p, ContDiff ℝ ∞ (Lψ p)
  loc_eq_Lψ : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    loc p z = Lψ p ((Ξ.X Y).Tm p z.1 z.2)

namespace SmoothRootField

/-- The zero field is a smooth root field. -/
def zero : Ξ.SmoothRootField Y :=
  { RootField.zero Ξ Y with
    Lψ := fun _ _ => 0
    Lψ_smooth := fun _ => contDiff_const
    loc_eq_Lψ := fun _ _ => rfl }

/-- The zero field is a smooth root field. -/
def zero : Ξ.SmoothRootField Y :=
  { RootField.zero Ξ Y with
    Lψ := fun _ _ => 0
    Lψ_smooth := fun _ => contDiff_const
    loc_eq_Lψ := fun _ _ => rfl }

/-- The empirical piece coefficients: the base integrals of the rectangle coefficients. -/
noncomputable def pieceCoeff (p : (Ξ.X Y).PIdx) (μ : ℝ) (q : ℕ) : ℝ :=
  ∫ s, empCoeffRect (fun v => Ξ.G Y p.1 (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
    (fun v => ξ.Lψ p (affineMap ((Ξ.X Y).eqv p) p.2 ((Ξ.X Y).sc p s) v))
    ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) (fun _ => Y.T.a p.1) μ q ∂(Ξ.piecePresentation Y p).ν

/-- ★ **The resolved empirical coefficients**: the sum over the pieces of the base integrals of the
rectangle coefficients of the piece field families. -/
noncomputable def resolvedCoeff (μ : ℝ) (q : ℕ) : ℝ := ∑ p, ξ.pieceCoeff p μ q

/-- ★★★ **The resolved empirical expansion** (empirical Theorem E on the resolved manifold, for a
bounded smooth root field): `Z^emp_N[F; ψ]` is a cutoff expansion on the common lattice
`commonQ⁻¹ℕ` with logarithmic degree `≤ commonD`, with the coefficients `resolvedCoeff`. -/
theorem empZ_cutoffExpansion {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    CutoffExpansion (Ξ.decomp Y).commonQ (Ξ.decomp Y).commonD (Ξ.empZ Y ξ.toRootField)
      ξ.resolvedCoeff := <proof>

/-- ★★ **Zero-field compatibility**: the resolved empirical coefficients of the zero field are the
population resolved coefficients. -/
theorem resolvedCoeff_zero {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / (Ξ.decomp Y).commonQ) {j : ℕ}
    (hj : j ≤ (Ξ.decomp Y).commonD) : (zero Ξ Y).resolvedCoeff μ j = Ξ.coeff Y μ j := <proof>


==================== Grammar/EmpiricalResolvedLeading.lean

/-!# The empirical leading theorem on the resolved manifold

For a root field `ξ` (continuous branch representatives on the pieces, `|ψ| ≤ M`) and a
chart-leading pair `(λ, m)` of the resolved chart transport, the **empirical partition function**
`Z^{emp}_N[F; ξ] = ∫_U e^{−N K∘π + √N √(K∘π) ψ} F dμ_U` has the leading term
`N^{−λ}(log N)^{m−1} · Σ_{pieces} ∫_{Base} boxFaceLimit_p(s) dν_p(s)`
(`hasLeadingTerm_empZ`): the tail is exponentially small (`hasLeadingTerm_tail_zero`), the cores
are the empirical piece integrals. For a test `F` supported in `X = U ∖ D_{m+1}` the limit is the
integral of `F` against the **empirical stratum measure** `ν^λ_m(ξ)` of `EmpiricalStratumMeasure`
(`integral_empiricalStratumMeasure_eq_sum`, `hasLeadingTerm_empZ_eq_integral`): the leading term
of the empirical partition function is the population residue measure weighted by the fluctuation
density `S_λ(ξ̂)/Γ(λ)-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The empirical partition function `∫_U e^{−N K∘π + √N √(K∘π) ψ} F dμ_U`. -/
noncomputable def empZ (ξ : Ξ.RootField Y) (N : ℝ) : ℝ := ∫ P, Ξ.empIntegrand Y ξ N P ∂Ξ.μU

/-- ★★★ **The empirical leading theorem**: at a chart-leading pair `(λ, m)` and for a bounded root
field, `Z^{emp}_N[F; ξ] / (N^{−λ}(log N)^{m−1}) → Σ_p ∫_{Base} boxFaceLimit_p dν_p`. -/
theorem hasLeadingTerm_empZ (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      (∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν) lam (m - 1) := <proof>

/-- ★★★ **The empirical leading theorem, in the form of the empirical stratum measure**: for a
test `F` supported in `X = U ∖ D_{m+1}`, a bounded root field `ξ` and a chart-leading pair
`(λ, m)`, `N^{λ}(log N)^{−(m−1)} Z^{emp}_N[F; ξ] → ∫_X F dν^λ_m(ξ)`. -/
theorem hasLeadingTerm_empZ_eq_integral (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam) {m : ℕ}
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M)
    (hFt : Ξ.IsTest m Ξ.F) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m)) lam
      (m - 1) := <proof>


==================== Grammar/EmpiricalResolvedStratumFormula.lean

/-!# The resolved graded empirical formula (§20, consult #143 priority 2b)

For a smooth root field `ξ` and an observable `F` vanishing near the deep zero fibre `D_{c+1} = Z₀
∩ {depth ≥ c+1}`, the coefficient of the resolved empirical expansion at the top logarithmic power
`(μ, c − 1)` is the **branchwise weighted stratum sum** (★★★ `resolvedCoeff_eq_empStratumSum`):
over the pieces `p` and the base points `s`, the population stratum term of the piece with the
amplitude replaced by `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)` — the replacement rule `∂^α A ↦
∂^α[A S_μ(ζ)]/Γ(μ)` applied branch by branch (`pieceCoeff_top_eq_smoothCoeff`), where `ζ = Lψ_p ∘
Tm_{p,s}` is the smooth branch representative of the field on the piece. The inputs are the cube
replacement rule (`empCoeffRect_top_eq_smoothCoeff`) and the deep vanishing of the chart amplitudes
within the piece boxes (`deepVanishing_amp`, fr-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
namespace SmoothRootField
variable {Ξ Y} (ξ : Ξ.SmoothRootField Y)
end SmoothRootField
end ResolvedData
end SmoothEngine
end Grammar

/-- The replaced amplitude of a piece: `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s}) / Γ(μ)`. -/
noncomputable def replacedAmp (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) : (Fin ((Ξ.X Y).da p) → ℝ) → ℝ :=
  fun v => (Ξ.amp Y p).amp s v * fluctuation 1 μ (ξ.Lψ p ((Ξ.X Y).Tm p s v)) / Real.Gamma μ

/-- The empirical stratum term of a piece at a base point: the population stratum term
(`pieceStratumSum`) with the amplitude replaced by `amp · S_μ(ζ)/Γ(μ)`. -/
noncomputable def empPieceStratumSum (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter (fun J => J.card = c),
    faceW J (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) *
      (faceCoef ((Ξ.X Y).kA p) 1 (Y.T.a p.1) J
          (fun i => resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J i + (Ξ.X Y).hA p i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) μ J) (lJ J)
            (ξ.replacedAmp p s μ) (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => 2 * (Ξ.X Y).kA p i)
          (Y.T.a p.1) μ 0)

/-- The branchwise weighted stratum sum: the empirical stratum terms integrated over the bases
and summed over the pieces. -/
noncomputable def empStratumSum (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ p, ∫ s, ξ.empPieceStratumSum p s μ c ∂(Ξ.piecePresentation Y p).ν

/-- ★★★ **The resolved graded empirical formula**: for an observable vanishing near the deep zero
fibre `D_{c+1}`, the resolved empirical coefficient at `(μ, c − 1)` is the branchwise weighted
stratum sum with the amplitudes `amp_{p,s} · S_μ(Lψ_p ∘ Tm_{p,s})/Γ(μ)`. -/
theorem resolvedCoeff_eq_empStratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {μ : ℝ} (hμ : 0 < μ) :
    ξ.resolvedCoeff μ (c - 1) = ξ.empStratumSum μ c := <proof>


==================== Grammar/EmpiricalStratumMeasure.lean

/-!# The empirical stratum measure

The population stratum measure `ν^μ_c` (zero order) is, on `X = U ∖ D_{c+1}`, the sum over the
pieces of a resolved chart transport and their simple-pole faces of the pushforwards of the face
densities (`SmoothChartResidueIdentity`). With the empirical phase
`e^{−N K∘π + √N √(K∘π) ψ}` the radial Gamma factor `Γ(μ)` of every face is replaced by the
fluctuation function `S_μ(ψ̂)` of the **branch trace** `ψ̂` of the root field
`ψ = √n (K − K_n)/√K` on the normal side of the face carried by the piece. This module defines the
resulting **empirical stratum measure**

`ν^μ_c(ξ) = Γ(μ)/(c−1)! · Σ_{pieces, simple faces} (faceDensity · S_μ(trace ξ)/Γ(μ))_*`

for a `RootField` `ξ` (a function on `U` with a continuous branch representative on the closed box
of every piece) and proves its basic properties: it is the population measure at the zero field
(`empiricalStra-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
namespace RootField
variable {Ξ Y} (ξ : Ξ.RootField Y)
end RootField
section Face
variable (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p))) (ξ : Ξ.RootField Y)
end Face
variable (ξ : Ξ.RootField Y)
end ResolvedData
end SmoothEngine
end Grammar

/-- A **root field**: a function `ψ` on `U` (the pull-back of Watanabe's `√n(K − K_n)/√K`)
together with, for every piece, a continuous branch representative on `Base × ℝ^{da}` agreeing
with `ψ ∘ divPt` on the open box. Only the representatives' values on the closed boxes enter the
empirical stratum measure. -/
structure RootField where
  /-- the field on `U` -/
  ψ : Ξ.R.U → ℝ
  ψ_meas : Measurable ψ
  /-- the branch representative of the piece -/
  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

structure RootField where
  /-- the field on `U` -/
  ψ : Ξ.R.U → ℝ
  ψ_meas : Measurable ψ
  /-- the branch representative of the piece -/
  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

  ψ : Ξ.R.U → ℝ
  ψ_meas : Measurable ψ
  /-- the branch representative of the piece -/
  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

namespace RootField

/-- The zero field. -/
def zero : Ξ.RootField Y where
  ψ _ := 0
  ψ_meas := measurable_const
  loc _ _ := 0
  loc_cont _ := continuous_const
  loc_eq _ _ _ := rfl

  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

namespace RootField

/-- The zero field. -/
def zero : Ξ.RootField Y where
  ψ _ := 0
  ψ_meas := measurable_const
  loc _ _ := 0
  loc_cont _ := continuous_const
  loc_eq _ _ _ := rfl

/-- The zero field. -/
def zero : Ξ.RootField Y where
  ψ _ := 0
  ψ_meas := measurable_const
  loc _ _ := 0
  loc_cont _ := continuous_const
  loc_eq _ _ _ := rfl

/-- The branch trace of the field at the face point `(s, glue J 0 w)`. -/
noncomputable def faceTrace
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  ξ.loc p (z.1, glue J 0 z.2)

/-- The empirical face density: the face density times the fluctuation density of the trace. -/
noncomputable def empFaceDensity (μ : ℝ)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  Ξ.faceDensity Y p J μ z * fluctDensity μ (Ξ.faceTrace Y p J ξ z)

/-- The empirical face measure on `U`: the pushforward of the empirical face density along the
face map. -/
noncomputable def empFaceMeasureU (μ : ℝ) : Measure Ξ.R.U :=
  ((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p J ξ μ z)).map
    (Ξ.faceMap Y p J)

/-- The empirical face measure on `X = U ∖ D_{c+1}`. -/
noncomputable def empFaceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  Measure.comap Subtype.val (Ξ.empFaceMeasureU Y p J ξ μ)

/-- The empirical chart measure: the sum over the pieces and simple-pole faces of the empirical
face measures. -/
noncomputable def empiricalChartMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c, Ξ.empFaceMeasure Y ((Ξ.X Y).en I) J ξ μ c

/-- **The empirical stratum measure** `ν^μ_c(ξ) = Γ(μ)/(c−1)! · empiricalChartMeasure`, equal to
the population stratum measure at the zero field. -/
noncomputable def empiricalStratumMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal (residueConst μ c) • Ξ.empiricalChartMeasure Y ξ μ c


==================== Grammar/EmpiricalUniform.lean

/-!# The empirical expansion, uniformly in the field data (§20 unit 1 of consult #142)

The constants of the empirical box expansion depend on `(η, ζ)` only through the rectangular jet
bound `FieldJetBound η ζ p 1 C M'` (`|∂^m(η e^{τζ})| ≤ C (1+τ)^{|p|} e^{M'τ}`, `m ≤ p`), and
LINEARLY in `C`. This file records the consequences at the level of the canonical coefficients:
the coefficients themselves are `O(C)` (★ `exists_abs_empCoeffAtDepth_le`, via
`abs_faceCoeffInt_le`),
the expansion through every admissible cutoff is `C · K₀ N^{−L}(1+log N)^{d−1}` with `K₀`
depending only on `(h, k, L, M')` (`emp_expansion_cutoff_uniform`), and
★★★ `emp_cutoffExpansion_uniform`: for every real cutoff `L' > 0` there is `K₀ = K₀(h,k,L',M')`
with `|Z_{η,ζ}(N) − Σ_{μ<L'} N^{−μ} Σ_q empCoeff η ζ μ q (log N)^q| ≤ C K₀ N^{−L'}(1+log N)^{d−1}`
for ALL `N ≥ 1` and ALL smooth `(η, ζ)` satisfying the jet bound at t-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} (h k p : Fin d → ℕ)
variable {h k}
end SmoothEngine
end Grammar

/-- ★★★ **The canonical cutoff expansion, uniformly in the field data**: for every real cutoff
`L' > 0` there is `K₀ = K₀(h, k, L', M')` such that for every smooth `(η, ζ)` with the jet bound
of constant `C` at the depth of `L'`,
`|Z_{η,ζ}(N) − Σ_{μ ∈ Λ^Q_{L'}} N^{−μ} Σ_{q ≤ d−1} empCoeff η ζ h k μ q (log N)^q|`
`  ≤ C K₀ N^{−L'} (1 + log N)^{d−1}` for ALL `N ≥ 1`. -/
theorem emp_cutoffExpansion_uniform (hk : ∀ i, 0 < k i) (L' M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ (depthOf h k (max ⌈L'⌉₊ (L₀ h))) 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |empIntegral η ζ h k N - absSpectralSum (Qamb k) (d - 1) (empCoeff η ζ h k) L' N| ≤
          C * K₀ * (N ^ (-L') * (1 + log N) ^ (d - 1)) := <proof>


==================== Grammar/FamilySpectralCoeff.lean

/-!# Spectral coefficients of coefficient-family data (Stage 4f)

Unit 245 (Taylor-tree programme, Stage 4; Astra #28 §2.4 (II)). For absolutely summable coefficient
families `cξ, cη`, the spectral coefficients of the box truncations
`A_{μ,j}(truncList cξ m, truncList cη m)` form a Cauchy sequence: by the stability gate (unit 242)
consecutive differences are bounded by explicit constants times the tail masses of `cξ, cη`, which
tend to `0`. The **family spectral coefficient** `A_{μ,j}(cξ, cη)` is their limit
(`familySpectralCoeff`, `tendsto_truncCoeff`), it vanishes off the candidate set `Λ(h,k)`
(`familySpectralCoeff_eq_zero_of_not_candidate`), and the spectral sums below any cutoff converge
(`tendsto_spectralSum_truncList`). No `sorry` and no additional `axiom` declarations.-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
open scoped List
namespace Grammar
open MonoRep CoeffFamily
namespace CoeffFamily
variable {d : ℕ}
end CoeffFamily
end Grammar

/-- The spectral coefficient of the level-`m` truncations. -/
noncomputable def truncCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j : ℕ) (m : ℕ) : ℝ :=
  spectralCoeff n h k β (truncList cξ m) (truncList cη m) μ j

/-- **The family spectral coefficient** `A_{μ,j}(cξ, cη)`: the limit of the truncation
coefficients. -/
noncomputable def familySpectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ :=
  limUnder atTop (truncCoeff n h k β cξ cη μ j)


==================== Grammar/FirstCorrection.lean

/-!# The first correction of the empirical integral in the generic case

For the empirical integral `Z_N = ∫_{[0,1]^{n+1}} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv` with a
single resonant coordinate `i₀` whose first two exponents `λ = (h₀+1)/2k₀` and
`μ₁ = λ + 1/(2k₀)` both lie strictly below every other ratio `(h_l+1)/2k_l`, the two leading
coefficients of the canonical cutoff expansion are **readable face integrals**: writing
`w` for the complementary coordinates, `η_w(u) = η(u, w)`, `ζ_w(u) = ζ(u, w)` and
`p(w) = w^{2k_L}`,
```
c(λ, 0)  = ∫_{[0,1]^n} w^{h_L} p(w)^{−λ}  · η_w(0) S_λ(ζ_w(0)) / (2k₀) dw
c(μ₁, 0) = ∫_{[0,1]^n} w^{h_L} p(w)^{−μ₁} · [∂_{i₀}η(0,w) S_{μ₁}(ζ(0,w))
                                            + η(0,w) ∂_{i₀}ζ(0,w) S_{μ₁+1/2}(ζ(0,w))] / (2k₀) dw,
```
there are no logarithms at `λ` or `μ₁`, and every coefficient at a lattice exponent `< μ₁` other
than `c(λ,0)` vanis-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Asymptotics
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
section OneDim
variable {η ξ : ℝ → ℝ}
end OneDim
variable {n : ℕ}
variable (η ζ : (Fin (n + 1) → ℝ) → ℝ) (h k : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1))
end SmoothEngine
end Grammar

/-- The one-variable slice of `G` along the coordinate `i₀` through the complementary point
`w`: `u ↦ G(insertNth i₀ u w)`. -/
def coordSlice (i₀ : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ) (w : Fin n → ℝ) : ℝ → ℝ :=
  fun u => G (Fin.insertNth i₀ u w)

/-- The exponent data of the complementary coordinates. -/
def sliceExp (γ : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1)) : Fin n → ℕ := fun j => γ (i₀.succAbove j)

/-- The face weight `w^{h_L} (w^{2k_L})^{−μ}`. -/
noncomputable def faceWt (μ : ℝ) (w : Fin n → ℝ) : ℝ :=
  mono (sliceExp h i₀) w * mono (fun j => 2 * sliceExp k i₀ j) w ^ (-μ)

/-- The face coefficients `∫_{[0,1]^n} w^{h_L} (w^{2k_L})^{−μ_j} · C_j[η_w, ζ_w] dw`
of the resonant coordinate `i₀`, `μ_j = (h_{i₀} + j + 1)/(2k_{i₀})`. -/
noncomputable def genericFaceCoeff (j : ℕ) : ℝ :=
  ∫ w in box (Fin n) 1, faceWt h k i₀ (lam (k i₀) (j + h i₀)) w *
    empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) (h i₀) (k i₀) j

/-- ★★ **The first correction of the empirical integral (generic case)**: if the resonant
coordinate `i₀` has `μ₁ = (h_{i₀}+2)/(2k_{i₀})` strictly below every other ratio, then
`N^{μ₁} (Z_N − C_λ N^{−λ}) → C_{μ₁}` with `C_λ = genericFaceCoeff 0`,
`C_{μ₁} = genericFaceCoeff 1`. -/
theorem tendsto_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    Tendsto (fun N : ℝ => N ^ lam (k i₀) (1 + h i₀) *
        (empIntegral η ζ h k N - genericFaceCoeff η ζ h k i₀ 0 * N ^ (-lam (k i₀) (h i₀))))
      atTop (𝓝 (genericFaceCoeff η ζ h k i₀ 1)) := <proof>

/-- ★★★ **The two leading canonical coefficients in the generic case**: for every lattice exponent
`μ ≤ μ₁ = λ + 1/(2k_{i₀})` and every log degree `q ≤ n`,
`empCoeff η ζ h k μ q = [μ = λ, q = 0] · C_λ + [μ = μ₁, q = 0] · C_{μ₁}`
with the readable face integrals `C_λ = genericFaceCoeff 0`, `C_{μ₁} = genericFaceCoeff 1`. In
particular there are no logarithms at `λ` or `μ₁`, and no terms strictly between them. -/
theorem empCoeff_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ₁ : μ ≤ lam (k i₀) (1 + h i₀)) {q : ℕ}
    (hq : q ≤ n) :
    empCoeff η ζ h k μ q =
      (if μ = ratioExp h k i₀ ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 0 else 0) +
      (if μ = lam (k i₀) (1 + h i₀) ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 1 else 0) := <proof>

/-- ★★★ **The first correction coefficient is the face integral `C_{μ₁}`** at
`μ₁ = λ + 1/(2k_{i₀})`. -/
theorem empCoeff_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    empCoeff η ζ h k (ratioExp h k i₀ + 1 / (2 * (k i₀ : ℝ))) 0 =
      genericFaceCoeff η ζ h k i₀ 1 := <proof>


==================== Grammar/Fluctuation.lean

/-!# The fluctuation function (grammar paper §4)

Watanabe's *fluctuation function* (greybook, Definition 5.8), the building block
of the `Z_n[φ]` asymptotic expansion in *Expectations and the exceptional
divisor* (§4, `eq:fluctuation`):

  `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`,   `β, λ > 0`.

This module opens the §4 formalisation with the definition, its integrability
for every `a ∈ ℝ` (AM–GM domination `a√t ≤ t/2 + a²/2` against a Gamma
integrand), and the base value `S_λ(0) = β^{-λ} Γ(λ)`.

`lam` denotes the RLCT `λ` (`λ` is reserved syntax in Lean).-/

-- section/variable skeleton:
open Real MeasureTheory
namespace Grammar
end Grammar

/-- The **fluctuation function** `S_λ(a) = ∫₀^∞ t^{λ-1} e^{-β t + β a √t} dt`
(grammar §4 `eq:fluctuation`; Watanabe, Definition 5.8). -/
noncomputable def fluctuation (β lam a : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

/-- Property (i) in `deriv` form. -/
theorem deriv_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    deriv (fun a => fluctuation β lam a) a = β * fluctuation β (lam + 1 / 2) a := <proof>

/-- The integration-by-parts recurrence (grammar §4 `eq:fluctuation_recurrence`):
`S_{λ+1}(a) = (a/2)·S_{λ+1/2}(a) + (λ/β)·S_λ(a)`, from `∫₀^∞ d/dt[t^λ e^{phase}] = 0`. -/
theorem fluctuation_recurrence (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    fluctuation β (lam + 1) a
      = (a / 2) * fluctuation β (lam + 1 / 2) a + (lam / β) * fluctuation β lam a := <proof>

/-- Property (iii) (grammar §4 `lem:fluctuation_properties`): the second-order ODE
`S''_λ = (aβ/2)·S'_λ + λβ·S_λ`, i.e. `β²S_{λ+1} = (aβ/2)(βS_{λ+1/2}) + λβ S_λ`. -/
theorem fluctuation_ode (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    β ^ 2 * fluctuation β (lam + 1) a
      = (a * β / 2) * (β * fluctuation β (lam + 1 / 2) a) + lam * β * fluctuation β lam a := <proof>

/-- Property (iv) (grammar §4 `lem:fluctuation_properties`): `S_1(a) = (a/2)·S_{1/2}(a) + 1/β`,
the `λ = 0` boundary case of the recurrence (`∫₀^∞ d/dt[e^{phase}] = 0 − 1 = −1`). -/
theorem fluctuation_one (β : ℝ) (hβ : 0 < β) (a : ℝ) :
    fluctuation β 1 a = (a / 2) * fluctuation β (1 / 2) a + 1 / β := <proof>


==================== Grammar/FluctuationLipschitz.lean

/-!# Positivity, monotonicity and Lipschitz bounds of the fluctuation function

`S_λ(a) = ∫₀^∞ t^{λ−1} e^{−βt + βa√t} dt` (positive: `fluctuation_pos`) is increasing in `a` and
locally Lipschitz with constant `β S_{λ+1/2}(M)` on `[−M, M]` (`abs_fluctuation_sub_le`). The
normalised
**fluctuation density** `fluctDensity μ a = S_μ(a)/Γ(μ)` at temperature one equals `1` at `a = 0`
and is the density of the empirical stratum measure with respect to the population one
(`EmpiricalStratumMeasure`). Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open Real MeasureTheory Set
namespace Grammar
end Grammar

/-- The fluctuation density `S_μ(a)/Γ(μ)` (temperature one): the density of the empirical
stratum measure with respect to the population one; equals `1` at `a = 0`. -/
noncomputable def fluctDensity (μ a : ℝ) : ℝ := fluctuation 1 μ a / Real.Gamma μ


==================== Grammar/FluctuationSelfNormalised.lean

/-!# Self-normalisation of the fluctuation function

The Gaussian-averaging note works with ratios of fluctuation functions
`R₁(a) = S_{λ+1/2}(a)/S_λ(a)` and `R₂(a) = S_{λ+1}(a)/S_λ(a)` (posterior moments of the radial
variable).  This file proves the elementary facts that make every such ratio polynomially bounded,
hence integrable against any Gaussian law for every `β > 0`:

* `fluctuation_eq_two_mul_gaussMomentJ`: `S_μ = 2 J_{2μ}` (the two normalisations of the paper);
* `fluctuation_half_sq_le`: the posterior Cauchy–Schwarz inequality `S_{λ+1/2}² ≤ S_λ S_{λ+1}`,
  from `∫ t^{λ−1} e^{…} (√t − r)² dt ≥ 0`;
* `fluctuation_succ_le`, `fluctuation_half_le`: with the Weber recurrence `R₂ = λ/β + (a/2) R₁`,
  `R₂(a) ≤ 2λ/β + a₊²/4` and `R₁(a) ≤ √(2λ/β + a₊²/4)`;
* `fluctuation_ge_lower`: the polynomial lower bound `S_λ(a) ≥ e^{−2β} λ⁻¹ (1 + |a|)^{−2λ}`, from
  the initial segment `0 < t < (1+|a-/

-- section/variable skeleton:
variable).  This file proves the elementary facts that make every such ratio polynomially bounded,
open Real MeasureTheory Set
namespace Grammar
section Basic
variable {β lam : ℝ}
end Basic
section CauchySchwarz
variable {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ)
include hβ hlam
omit hβ hlam in
omit hβ hlam in
end CauchySchwarz
section Lower
variable {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ)
include hβ hlam
end Lower
end Grammar

/-- The fluctuation integrand. -/
noncomputable def fluctIntegrandFn (β lam a t : ℝ) : ℝ :=
  t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)


==================== Grammar/GaussianDichotomy.lean

/-!# The constant-Gaussian fluctuation model: expected leading moment (grammar §4.3, rem:pop_vs_emp)

The leading coefficient is `A_p = y₀₀/(k₁k₂) J_p(x₀₀)` with the positive Gaussian moment
`J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` (units 124, 154). If the constant fluctuation `x₀₀ = X`
is Gaussian `N(0, v)`, Tonelli and the Gaussian moment generating function give the identity
(in the extended nonnegative reals, so that `+∞` is a legitimate value)

`E₊[J_p(X)] = ∫₀^∞ s^{p−1} e^{−βs²} e^{v(βs)²/2} ds` (`lintegral_gaussMoment_eq`).

The right-hand side is finite iff `βv < 2` (next unit): the expected leading coefficient can be
infinite although every sample coefficient is finite, which is the content of the paper's remark
that "E[C(ξ_n)] ≠ C(0)" and of the temperature threshold. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory ProbabilityTheory Real Set Filter Topology
namespace Grammar
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
omit [IsProbabilityMeasure μ] in
end Grammar

/-- The Gaussian moment `J_p(x) = ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` as a function of `x`. -/
noncomputable def gaussMomentJ (β p x : ℝ) : ℝ :=
  logMoment β p 0 (fun s => Real.exp (β * s * x))


==================== Grammar/GaussianFluctuationScalar.lean

/-!# The Gaussian expectation of the fluctuation function, in one variable and in families

* `integral_mul_fluctuation_eq_of_measure`: Fubini for insertions against an arbitrary probability
  measure and an arbitrary real random variable `X` (the `gaussianVector` version is
  `integral_mul_fluctuation_eq`).
* `integral_fluctuation_gaussianReal'` ★★ (variance in `ℝ≥0`; the `toNNReal` form is
  `integral_fluctuation_gaussianReal` in `LeadingCoeffGaussianMoment`): for `G ~ N(0, v)`, `βv < 2`,
  `E S_λ(G) = Γ(λ) (β(1 − βv/2))^{−λ}`; at `β = 1` this is `Γ(λ)(1 − v/2)^{−λ}`.
* `integral_fluctuation_of_map_gaussianReal`: the same for a random variable whose law is
  `N(0, v)`.
* `integral_integral_fluctuation_of_gaussian_marginals` ★★: for a jointly measurable family
  `X(ω, z)` whose one-point laws are all `N(0, v)` and an integrable weight `a`,
  `E ∫ a(z) S_λ(X(ω, z)) dρ(z) = Γ(λ)(1 − v/2)^{−λ-/

-- section/variable skeleton:
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
namespace Grammar
variable {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
end Grammar

/-- ★★ **The Gaussian expectation of the fluctuation function**: for `G ~ N(0, v)` with
`βv < 2`, `S_μ(G)` is integrable and `E S_μ(G) = Γ(μ) (β(1 − βv/2))^{−μ}`. -/
theorem integral_fluctuation_gaussianReal' (β μ : ℝ) (hβ : 0 < β) (hμ : 0 < μ) (v : ℝ≥0)
    (hδ : 0 < 1 - β * (v : ℝ) / 2) :
    Integrable (fluctuation β μ) (gaussianReal 0 v) ∧
    ∫ x, fluctuation β μ x ∂gaussianReal 0 v =
      Real.Gamma μ * (β * (1 - β * (v : ℝ) / 2)) ^ (-μ) := <proof>


==================== Grammar/GaussianThreshold.lean

/-!# The constant-Gaussian fluctuation model: the finiteness threshold (rem:pop_vs_emp)

For `X ~ N(0, v)` the expected Gaussian moment `E₊[J_p(X)]` (unit 161) equals
`∫₀^∞ s^{p−1} e^{−(β − β²v/2)s²} ds`, hence

* if `βv < 2`: `E₊[J_p(X)] = J_p(0) (1 − βv/2)^{−p/2} < ∞` (`lintegral_gaussMomentJ_eq_of_lt`),
  and it strictly exceeds `J_p(0)` when `v > 0` (`lt_lintegral_gaussMomentJ`);
* if `βv ≥ 2`: `E₊[J_p(X)] = ∞` (`lintegral_gaussMomentJ_eq_top_of_ge`).

So the expected leading coefficient is finite iff `βv < 2` (`lintegral_gaussMomentJ_lt_top_iff`):
averaging the asymptotic coefficients over the fluctuation is not justified by the samplewise
expansion alone, and a temperature threshold appears. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory ProbabilityTheory Real Set Filter Topology
namespace Grammar
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
end Grammar

/-- **The finiteness threshold**: the expected leading moment is finite iff `βv < 2`. -/
theorem lintegral_gaussMomentJ_lt_top_iff (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (X : Ω → ℝ)
    (hX : Measurable X) (v : NNReal) (hXg : μ.map X = gaussianReal 0 v) :
    (∫⁻ ω, ENNReal.ofReal (gaussMomentJ β p (X ω)) ∂μ) < ⊤ ↔ β * v < 2 := <proof>


==================== Grammar/GibbsJoint.lean

/-!# The joint Gibbs measure on the base and the radial line (§20, replicas)

The limit posterior of a continuous field `g` on the compact base `K` is the probability measure
`μ_g(dx dt) ∝ t^{λ−1} e^{−βt + βg(x)√t} dρ(x) dt` on `K × (0,∞)` (`gibbsJoint`, a `withDensity`
of `ρ ⊗ Lebesgue|_(0,∞)` — Astra #163 §4).  Its reductions identify the moment brackets used so
far with genuine expectations:

* `integral_gibbsJoint_obs`: `∫ φ(x) dμ_g = ⟨φ⟩_g` (`compactAvg`);
* `integral_gibbsJoint_sqrt`: `∫ φ(x)√t dμ_g = ⟨φ√t⟩_g` (`compactSqrtTimeMoment`);
* `integral_gibbsJoint_radial`: `∫ φ(x) t dμ_g = T_g(φ)` (`compactTimeMoment`);
* `integral_gibbsJoint_prod_sqrt`: `∫∫ h(x₁,x₂)√t₁√t₂ dμ_g dμ_g = B_g(h)` (`compactBilocal`),

for bounded measurable `φ` and continuous `h`.  With them the Stein identity of `CompactBaseStein`
takes its **two-replica form**

★★★ `GaussianField.integral_eval_mul_compactAvg_-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Measure
variable {K : Type*} [MeasurableSpace K] (β lam : ℝ) (ρ : Measure K)
end Measure
section Norm
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
end Norm
section Reduction
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ))
omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
include hβ hlam hρ
end Reduction
section Replica
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0) [Nonempty K]
include hβ hlam hρ
omit [Nonempty K] in
end Replica
end Grammar

/-- The base measure `ρ ⊗ Lebesgue|_(0,∞)`. -/
noncomputable def gibbsBase : Measure (K × ℝ) := ρ.prod (volume.restrict (Ioi (0 : ℝ)))

/-- The normalised joint density `t^{λ−1} e^{−βt + βg(x)√t} / D_ρ(g)`. -/
noncomputable def gibbsDensity (g : K → ℝ) (z : K × ℝ) : ℝ :=
  fluctIntegrandFn β lam (g z.1) z.2 / compactD β lam ρ g

/-- The **joint Gibbs measure** `μ_g` on `K × ℝ` (supported on `t > 0`). -/
noncomputable def gibbsJoint (g : K → ℝ) : Measure (K × ℝ) :=
  (gibbsBase ρ).withDensity fun z => ENNReal.ofReal (gibbsDensity β lam ρ g z)


==================== Grammar/GibbsJointResponse.lean

/-!# The mean response as a three-replica expectation (§20, replicas)

With the joint Gibbs measure `μ_g` of `GibbsJoint`, the mean response of `CompactBaseResponse`,
`H_f(g) = (β²/2)[(T_g(fc_Δ) − ⟨f⟩_g T_g(c_Δ)) − 2(B_g(𝒞f) − ⟨f⟩_g B_g(𝒞))]`, is a genuine
expectation over three independent replicas of the limit posterior:

★★★ `compactMeanResponse_eq_replica`:
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁ 𝒞(x₁,x₁) − 2√t₁√t₃ 𝒞(x₁,x₃))]`,

so that the interpolation identity `GaussianField.integral_compactAvg_eq` reads
`E⟨f⟩_G − ρ(f)/ρ(K)
  = (β²/2)∫₀¹ E E^{⊗3}_{μ_{√sG}}[(f(x₁) − f(x₂))(t₁𝒞(x₁,x₁) − 2√t₁√t₃𝒞(x₁,x₃))] ds`
(compose `GaussianField.integral_compactAvg_eq` with this identity pointwise).  The replicas are
organised as
`z = ((x₂,t₂), ((x₁,t₁), (x₃,t₃)))` on `μ_g ⊗ (μ_g ⊗ μ_g)`, so that every term factorises into a
function of replica `2` and a function of the pair `(1,3)`.

Zero -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
section Swap
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ))
include hβ hlam
end Swap
section Replica
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
  (g : C(K, ℝ)) (𝒞 : PSDKernel K) (f : C(K, ℝ))
include hβ hlam hρ
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] hβ hlam hρ in
omit hρ in
end Replica
end Grammar

/-- ★★★ **The mean response is a three-replica expectation**:
`H_f(g) = (β²/2) E^{⊗3}_{μ_g}[(f(x₁) − f(x₂))(t₁ 𝒞(x₁,x₁) − 2√t₁√t₃ 𝒞(x₁,x₃))]`, with the replicas
organised as `z = ((x₂,t₂), ((x₁,t₁), (x₃,t₃)))`. -/
theorem compactMeanResponse_eq_replica :
    compactMeanResponse β lam ρ 𝒞 f g = β ^ 2 / 2 *
      ∫ z, (f z.2.1.1 - f z.1.1) * (z.2.1.2 * 𝒞.C z.2.1.1 z.2.1.1 -
        2 * (Real.sqrt z.2.1.2 * Real.sqrt z.2.2.2 * 𝒞.C z.2.1.1 z.2.2.1))
        ∂(gibbsJoint β lam ρ g).prod ((gibbsJoint β lam ρ g).prod (gibbsJoint β lam ρ g)) := <proof>


==================== Grammar/GlobalExponentBound.lean

/-!# The global exponent from local leading terms, conditional on a local cover (Astra #70, route D)

For a nonnegative observable the exponent pair of a region integral is determined by finitely many
local regions with identified leading terms, with **no ownership and no intersection expansions**:
if the regions `Ω_i ⊆ R` cover `R` up to a set on which the phase is a.e. at least `δ₀ > 0`, and
each local integral satisfies `∫_{Ω_i} F e^{−NK} ~ c_i N^{−λ_i}(log N)^{m_i−1}` with `c_i > 0`, then
`∫_R F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})` with `λ_* = min_i λ_i` and `m_* = max{m_i : λ_i = λ_*}`
(`isTheta_of_local_leading_terms`): the lower bound is one piece, the upper bound is the sum of
the pieces plus the exponentially small tail. In logarithmic form the free energy is
`−log ∫_R F e^{−NK} = λ_* log N − (m_*−1) log log N + O(1)` (`freeEnergy_asymptotic`).

The hypotheses are exactly what `Is-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
namespace Grammar
section Abstract
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {R : Set X} (hR : MeasurableSet R) {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x)
  (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x) (hKm : Measurable K)
include hFint hKm hK0 hR in
include hR hF0 hFint hK0 hKm in
include hR hF0 hFint hK0 hKm in
end Abstract
section Global
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {R : Set X} (hR : MeasurableSet R)
  {F K : X → ℝ} (hF0 : ∀ x ∈ R, 0 ≤ F x) (hFint : IntegrableOn F R μ) (hK0 : ∀ x ∈ R, 0 ≤ K x)
  (hKm : Measurable K) {ι : Type*} (Ω : ι → Set X)
  (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩR : ∀ i, Ω i ⊆ R) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
  (hgap : ∀ᵐ x ∂μ, x ∈ R → x ∉ ⋃ i, Ω i → δ₀ ≤ K x) (c lam : ι → ℝ) (m : ι → ℕ)
  (hc : ∀ i, 0 < c i)
  (hI : ∀ i, (fun N : ℝ => ∫ x in Ω i, F x * Real.exp (-N * K x) ∂μ) ~[atTop]
    fun N => c i * powLogScale (lam i) (m i - 1) N)
include hR hF0 hFint hK0 hKm hΩm hΩR hc hI in
include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hI in
include hR hF0 hFint hK0 hKm hΩm hΩR hδ₀ hgap hc hI in
end Global
end Grammar

/-- The power–log scale `N^{−λ}(log N)^{r}`. -/
noncomputable def powLogScale (l : ℝ) (r : ℕ) (N : ℝ) : ℝ := N ^ (-l) * Real.log N ^ r


==================== Grammar/InverseEvidence.lean

/-!# The inverse evidence has all moments (§20, posterior expectations)

The Gaussian threshold `βv < 2` governs the **unnormalised** evidence `E D_ρ(G)` only
(`lintegral_compactD_eq_top`).  Normalised posterior expectations are unaffected: on
`0 < t < (1 + ‖g‖)^{−2}` the fluctuation integrand is at least `t^{λ−1} e^{−2β}`, so

★ `inv_compactD_le`: `D_ρ(g)^{−1} ≤ λ e^{2β} ρ(K)^{−1} (1 + ‖g‖)^{2λ}`,

a polynomial bound in the sup norm at every temperature and every variance.  Consequently

★★ `integrable_inv_compactD_rpow`: `E[D_ρ(G)^{−s}] < ∞` for every `s ≥ 0` as soon as
`(1 + ‖G‖)^{2λs}` is integrable, and ★★ `integrable_inv_compactD_rpow_of_isGaussian`: for a
Gaussian Borel law on `C(K,ℝ)` every inverse moment of the evidence is finite (Fernique via
`IsGaussian.memLp_id`).

The normalised radial moments are polynomially bounded as well: with `⟨t^p⟩_g =
∫ S_{λ+p}(g) dρ / D_ρ(g)` (`compact-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology ProbabilityTheory Finset
namespace Grammar
section Pointwise
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
end Pointwise
section Gaussian
variable {K : Type*} [MetricSpace K] [CompactSpace K]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable [MeasurableSpace K] [BorelSpace K] {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ]
end Gaussian
section Radial
variable {β lam : ℝ}
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ρ : Measure K) [IsFiniteMeasure ρ]
omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] in
end Radial
end Grammar

/-- ★ **The inverse evidence is polynomially bounded**:
`D_ρ(g)^{−1} ≤ λ e^{2β} ρ(K)^{−1} (1 + R)^{2λ}` for `‖g‖ ≤ R`. -/
theorem inv_compactD_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ‖g‖ ≤ R) :
    (compactD β lam ρ g)⁻¹ ≤ lam * Real.exp (2 * β) / ρ.real univ * (1 + R) ^ (2 * lam) := <proof>

/-- The Borel σ-algebra of the sup-norm topology on `C(K,ℝ)`. -/
local instance instMeasurableSpaceContinuousMapInv : MeasurableSpace C(K, ℝ) := borel _

local instance instBorelSpaceContinuousMapInv : BorelSpace C(K, ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(1 + x)^r ≤ 2^r (1 + x^r)` for `x, r ≥ 0`. -/
theorem one_add_rpow_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  have h2 : (1 + x) ≤ 2 * max 1 x := by
    rcases le_total x 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  have hm : 0 ≤ max 1 x := le_max_of_le_left zero_le_one
  calc (1 + x) ^ r ≤ (2 * max 1 x) ^ r := Real.rpow_le_rpow (by linarith) h2 hr
    _ = 2 ^ r * (max 1 x) ^ r := Real.mul_rpow (by norm_num) hm
    _ ≤ 2 ^ r * (1 + x ^ r) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
        rcases le_total x 1 with h | h
        · rw [max_eq_left h, Real.one_rpow]
          linarith [Real.rpow_nonneg hx r]
        · rw [max_eq_right h]
          linarith

/-- ★★ **Every inverse moment of the evidence of a Gaussian field is finite**: for a Gaussian
Borel law on `C(K,ℝ)`, `E[D_ρ(G)^{−s}] < ∞` for all `s ≥ 0`, at every temperature and every
variance — the threshold `βv < 2` concerns the unnormalised evidence only. -/
theorem integrable_inv_compactD_rpow_of_isGaussian (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    {G : Ω → C(K, ℝ)} (hG : Measurable G) [IsGaussian (P.map G)] {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun ω => (compactD β lam ρ (G ω))⁻¹ ^ s) P := <proof>


==================== Grammar/JetCloseness.lean

/-!# Finite-order closeness of smooth maps and its stability (§20, consult #144 unit B, analytic core)

`JetClose R K f₁ f₂ ε`: the `iteratedFDeriv` of orders `≤ R` of `f₁` and `f₂` differ by at most
`ε` on `K` (closeness in `C^R(K)`); `JetBoundOn R K f B`: the jets of orders `≤ R` are bounded by
`B` on `K`. Stability: scalar multiples (`JetClose.const_smul`), products with a fixed smooth
factor (★ `JetClose.mul_left`, Leibniz `norm_iteratedFDeriv_mul_le`), and composition with a
fixed smooth outer map (★★ `exists_jetClose_comp`): for `g` smooth and a jet bound `B` of the
limit, there is `C` with `JetClose R K f₁ f₂ ε → JetClose R K (g ∘ f₁) (g ∘ f₂) (C·ε)` for
`ε ≤ 1`. The composition step is Mathlib's Faà di Bruno formula (`HasFTaylorSeriesUpToOn.comp`):
`D^r(g∘f)(x) = Σ_{c ∈ OrderedFinpartition r} c.comp (D^{|c|}g(f x)) (D^{cᵢ} f x)`, with the
difference bound `norm_compAlongOrderedFinpa-/

-- section/variable skeleton:
open Set Filter Topology Finset Metric
open scoped ContDiff
namespace Grammar
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace SmoothEngine
variable {d : ℕ}
end SmoothEngine
end Grammar

/-- Closeness of the jets of orders `≤ R` on `K`. -/
def JetClose (R : ℕ) (K : Set E) (f₁ f₂ : E → F) (ε : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x‖ ≤ ε

/-- A bound on the jets of orders `≤ R` on `K`. -/
def JetBoundOn (R : ℕ) (K : Set E) (f : E → F) (B : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f x‖ ≤ B


==================== Grammar/LeadingTermInterface.lean

/-!# The leading-coefficient interface over chart–stratum pairs

The seventh module of the resolved-space programme (`tide-log/gpt6_bigpicture_v74.md`): a
**leading-term certificate** `HasLeadingTerm Z c λ k` for a function of the inverse temperature
`N` is the statement `Z(N) / (N^{-λ} (log N)^k) → c` (the scale `powLogScale` of
`GlobalExponentBound`) — the identified-leading-term theorems of
`ChartLeadingTerm` (`∫ F e^{-NK} ~ c N^{-λ} (log N)^{m-1}` with `c > 0`) are certificates with
`k = m − 1` (`hasLeadingTerm_of_isEquivalent`), and a certificate with `c ≠ 0` is such an
equivalence (`HasLeadingTerm.isEquivalent`), while `c = 0` records that `Z` is `o` of the scale.
Certificates are linear, and a term whose pair `(λ', k')` is **dominated** by `(λ, k)` (larger
exponent, or the same exponent and smaller log degree) is a certificate with coefficient `0` at
`(λ, k)` (`HasLeadingTerm.of_domi-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal
namespace Grammar
section Certificates
variable {Z Z' : ℝ → ℝ} {c c' lam lam' : ℝ} {k k' : ℕ}
end Certificates
section Dominance
variable {lam lam' : ℝ} {k k' : ℕ}
end Dominance
section Sums
variable {α : Type*} (s : Finset α) (Z : α → ℝ → ℝ) (c lam : α → ℝ) (k : α → ℕ)
variable (hs : s.Nonempty)
end Sums
namespace ResolutionCover
variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)
end ResolutionCover
end Grammar

/-- **A leading-term certificate**: `Z(N) / (N^{-λ} (log N)^k) → c`. -/
def HasLeadingTerm (Z : ℝ → ℝ) (c lam : ℝ) (k : ℕ) : Prop :=
  Tendsto (fun N => Z N / powLogScale lam k N) atTop (𝓝 c)


==================== Grammar/Localisation.lean

/-!# Measured localisation of a Laplace-type integral

The measure-theoretic content of Steps 1–3 of the paper's expansion argument, separated from the
resolution geometry.  A `LocalisationData` packages a resolved measure `μ` (prior and Jacobian
absorbed), a nonnegative measurable phase `K` and an integrable observable `F`, so that the
population integral is `Z(N) = ∫ F e^{−NK} dμ`.

* `localisation_bound`: the integral over the complement of the sublevel set `{K < δ}` is
  `O(e^{−δN})`: `|Z(N) − Z_{<δ}(N)| ≤ (∫|F|) e^{−δN}` for `N ≥ 0`.
* `FiniteSublevelPartition`: finitely many measurable `ρ_i ≥ 0` with `∑ ρ_i = 1` a.e. on the
  sublevel set; `Zsublevel_eq_sum` splits `Z_{<δ}` into the per-piece integrals `∫ ρ_i F e^{−NK}`.
* `Z_eq_of_map`: the pullback to a resolved space is an equality of integrals given the measure
  transport certificate `Measure.map π μ_U = μ_X` — no injectivity of -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
namespace LocalisationData
variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
namespace FiniteSublevelPartition
variable {D} {ι : Type*} [Fintype ι] (P : D.FiniteSublevelPartition ι)
end FiniteSublevelPartition
end LocalisationData
end Grammar
namespace Grammar
namespace LocalisationData
variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
end LocalisationData
end Grammar

/-- A resolved Laplace-type integral: measure, phase, observable, and a localisation level. -/
structure LocalisationData (U : Type*) [MeasurableSpace U] where
  /-- the resolved measure (prior and Jacobian absorbed) -/
  μ : Measure U
  /-- the pulled-back phase `K ∘ π` -/
  phase : U → ℝ
  /-- the pulled-back observable -/
  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

structure LocalisationData (U : Type*) [MeasurableSpace U] where
  /-- the resolved measure (prior and Jacobian absorbed) -/
  μ : Measure U
  /-- the pulled-back phase `K ∘ π` -/
  phase : U → ℝ
  /-- the pulled-back observable -/
  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

  μ : Measure U
  /-- the pulled-back phase `K ∘ π` -/
  phase : U → ℝ
  /-- the pulled-back observable -/
  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- The sublevel set `U_δ = {K < δ}`. -/
def sublevel : Set U := {z | D.phase z < D.δ}

  phase : U → ℝ
  /-- the pulled-back observable -/
  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- The sublevel set `U_δ = {K < δ}`. -/
def sublevel : Set U := {z | D.phase z < D.δ}

  obs : U → ℝ
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  /-- the localisation level `δ` -/
  δ : ℝ
  δ_pos : 0 < δ

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U)

/-- The sublevel set `U_δ = {K < δ}`. -/
def sublevel : Set U := {z | D.phase z < D.δ}


==================== Grammar/LogExampleTwoDim.lean

/-!# A two-dimensional example with a logarithm and a `∂_ν S_ν` weight (§20, consult #146/#147)

`K = x²y²` on `(0,1]²`, `h = 0`, constant field `a`: the ratios `(hᵢ+1)/(2kᵢ) = 1/2` coincide, so
`λ = 1/2` with multiplicity `2` and the leading term carries `log n`. Exactly
(★ `logExample_eq`):
`∫_0^1∫_0^1 e^{−n x²y² + a√n xy} dx dy = (4√n)⁻¹ ∫_0^n t^{−1/2} e^{−t + a√t} (log n − log t) dt`
(the product `u = xy` has density `−log u`, then `t = n u²`), and asymptotically
(★★ `tendsto_logExample`):
`4√n · I(n) − (S_{1/2}(a) log n − ∂_ν S_ν(a)|_{ν=1/2}) → 0`, with `∂_ν S_ν(a)|_{1/2} =
∫_0^∞ t^{−1/2} (log t) e^{−t+a√t} dt` (`iteratedDeriv_fluctuation_eq`). The coefficient of
`n^{−1/2}` is a genuine index derivative of the fluctuation function: the lower logarithmic weight
of `MellinLogWeights` appears concretely. At `a = 0` the two constants are `Γ(1/2)` and `Γ'(1/2)`.
Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology intervalIntegral
namespace Grammar
namespace SmoothEngine
end SmoothEngine
end Grammar

/-- The two-dimensional example integral `∫_0^1∫_0^1 e^{−n(xy)² + a√n·xy} dy dx`. -/
noncomputable def logExample (a n : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, exp (-n * (x * y) ^ 2 + a * Real.sqrt n * (x * y))

/-- ★★ **The two-dimensional log asymptotics**:
`4√n · I(n) − (S_{1/2}(a) log n − ∂_ν S_ν(a)|_{ν=1/2}) → 0` as `n → ∞`. -/
theorem tendsto_logExample (a : ℝ) :
    Tendsto (fun n : ℝ => 4 * Real.sqrt n * logExample a n -
      (Real.log n * fluctuation 1 (1 / 2) a - deriv (fun ν => fluctuation 1 ν a) (1 / 2)))
      atTop (𝓝 0) := <proof>


==================== Grammar/MellinLogWeights.lean

/-!# The lower logarithmic Mellin weights are `ν`-derivatives of the fluctuation function
(§20, consult #145 (2))

The coefficients of the empirical expansion below the top logarithmic power involve the
log-weighted Mellin moments `mellinMom G μ ℓ = ∫₀^∞ s^{μ−1} (−log s)^ℓ G(√s) e^{−s} ds`. On the
jet families `G(τ) = τ^r e^{aτ}` these are derivatives of the fluctuation function in its index:
★★ `mellinMom_pow_mul_exp_eq_iteratedDeriv`:
`mellinMom (τ^r e^{aτ}) μ ℓ = (−1)^ℓ · ∂_ν^ℓ S_ν(a) |_{ν = μ + r/2}` (`S_ν = fluctuation 1 ν`).
Route: `fluctuationLog ν a ℓ = ∫ t^{ν−1} (log t)^ℓ e^{−t + a√t} dt` is integrable for `ν > 0`
(the envelope of `EmpiricalInnerTwoRegime`), differentiable in `ν` under the integral with
derivative `fluctuationLog ν a (ℓ+1)` (★ `hasDerivAt_fluctuationLog`, dominated on a ball by
`(t^{ν/2−1} + t^{3ν/2−1}) |log t|^{ℓ+1} e^{−t+a√t}`), hence `iteratedDeriv ℓ S_·(a) ν =
-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
namespace SmoothEngine
end SmoothEngine
end Grammar

/-- ★★ **The lower logarithmic Mellin weights are index derivatives of the fluctuation
function**: `mellinMom (τ^r e^{aτ}) μ ℓ = (−1)^ℓ ∂_ν^ℓ S_ν(a) |_{ν = μ + r/2}`. -/
theorem mellinMom_pow_mul_exp_eq_iteratedDeriv {μ a : ℝ} (hμ : 0 < μ) (r ℓ : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ ℓ =
      (-1) ^ ℓ * iteratedDeriv ℓ (fun ν => fluctuation 1 ν a) (μ + r / 2) := <proof>


==================== Grammar/MellinPowerLog.lean

/-!# The Mellin transform of `N^{−μ} (log N)^q` on `[1, ∞)` (§20, the fluctuation zeta function)

`hasMellin_powLogIci : HasMellin (𝟙_{[1,∞)} N^{−μ} (log N)^q) s (q! / (μ − s)^{q+1})` for
`Re s < μ` — the elementary Mellin lemma behind the principal parts of the zeta function of a
cutoff expansion.  Route: the `(0,1]` power `t^μ (log t)^q` has transform `(−1)^q q!/(s+μ)^{q+1}`
for `Re s > −μ` (Mathlib's `hasMellin_cpow_Ioc` at `q = 0`, then differentiation in `s`:
`d/ds mellin f = mellin (log · f)`, `mellin_hasDerivAt_of_isBigO_rpow`), and inversion
`t ↦ t⁻¹` (`mellin_comp_inv`) carries it to `[1, ∞)`.

Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
namespace Grammar
end Grammar

/-- `N^{−μ} (log N)^q` on `[1, ∞)`, as a complex-valued function on `ℝ`. -/
noncomputable def powLogIci (μ : ℝ) (q : ℕ) : ℝ → ℂ :=
  indicator (Ici (1 : ℝ)) fun N => (N : ℂ) ^ (-(μ : ℂ)) * (Real.log N : ℂ) ^ q


==================== Grammar/MellinRegularization.lean

/-!# The regularised Mellin transform of a cutoff expansion (§20, the fluctuation zeta function)

For `E : ℝ → ℝ` with a cutoff expansion `E(N) = Σ_{μ<U} Σ_{q≤D} c_{μ,q} N^{−μ} (log N)^q +
O(N^{−U}(1+log N)^D)` on the lattice `Q⁻¹ℕ`, subtract the principal polynomial on `[1,∞)`:
`R_U(N) = E(N) − 𝟙_{[1,∞)}(N) Σ_{μ<U} Σ_q c_{μ,q} N^{−μ} (log N)^q`.  Then

* `mellinConvergent_cutoffRemainderFun`, `differentiableAt_mellin_cutoffRemainderFun`: the Mellin
  transform of `R_U` converges and is complex-differentiable on the strip `0 < Re s < U`;
* `mellin_eq_mellin_cutoffRemainderFun_add_principalParts`: on the initial strip `0 < Re s < a`
  (where `E = O(N^{−a})` and every retained exponent is `≥ a`),
  `mellin E s = mellin R_U s + Σ_{μ<U} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`;
* `mellin_cutoffRemainderFun_compat`: for `U ≤ V`,
  `mellin R_U s = mellin R_V s + Σ_{U≤μ<V} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}` o-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics Real
namespace Grammar
variable {Q D : ℕ} {E : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
end Grammar

/-- The principal parts `Σ_{μ<U} Σ_{q≤D} c_{μ,q} · q!/(μ − s)^{q+1}`. -/
noncomputable def principalParts (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
    (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))

/-- The regularised function `E − 𝟙_{[1,∞)} P_U`, complexified. -/
noncomputable def cutoffRemainderFun (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (N : ℝ) :
    ℂ :=
  (E N : ℂ) - ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N

/-- ★★ **The Mellin transform of `E` with its principal parts on the initial strip**: for
`0 < Re s < a`, where `E = O(N^{−a})` at infinity and every retained exponent with a nonzero
coefficient is `≥ a`,
`mellin E s = mellin R_U s + Σ_{μ<U} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`. -/
theorem mellin_eq_mellin_cutoffRemainderFun_add_principalParts (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U a : ℝ} (haU : a ≤ U)
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → a ≤ μ) {s : ℂ}
    (hs0 : 0 < s.re) (hsa : s.re < a) :
    mellin (fun N => (E N : ℂ)) s =
      mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s := <proof>


==================== Grammar/MonomialMixedAsymptotic.lean

/-!# The mixed-ratio monomial asymptotic in general dimension

Assembly of the mixed-ratio general-`d` monomial programme (Astra #15). For exponents
`h k : Fin (m+1) → ℕ` with `kᵢ > 0`, Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`, minimum `λ = min ℓᵢ` attained
`|J|` times, the monomial box integral

  `M(N) = ∫_{(0,1]^{m+1}} ∏ xᵢ^{hᵢ} e^{-βN ∏ xᵢ^{2kᵢ}} dx`

satisfies

  `M(N) ~ Γ(λ) β^{-λ} / (|J|-1)! · ∏_{i∈J} 1/(2kᵢ) · ∏_{i∉J} 1/(hᵢ+1-2kᵢλ) · N^{-λ} (log N)^{|J|-1}`

(`monomialBoxReal_mixed_isEquivalent`), which is the paper's Laurent coefficient
`a_{-|J|}` (eq. `a_minus_m_explicit`, cutoff `b = 1`) times the Laplace–Tauberian factor
`Γ(λ)/(|J|-1)!` and the inverse-temperature factor `β^{-λ}` (the paper has `β = 1`). The exact relation `M(N) = ∏ 1/(2kᵢ) · W_ℓ(N)` (`monomialBoxReal_eq_mixed`) comes
from the coordinatewise substitution of unit 174; the weighted asymptotic is unit 180. A `min`
wrapper-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
namespace Grammar
end Grammar

/-- The Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`. -/
noncomputable def ratioExp {d : ℕ} (h k : Fin d → ℕ) (i : Fin d) : ℝ :=
  ((h i : ℝ) + 1) / (2 * (k i : ℝ))


==================== Grammar/MonomialPhaseIdentity.lean

/-!# Exact monomial moments with a constant phase (Stage 2a)

Unit 227 (Taylor-tree programme). The Taylor-tree terms are monomial integrals with a constant phase
`a = ξ(0)` and a phase power `p`:
```
T(N) = ∫_{(0,1]^d} u^h (√N u^k)^p exp(-βN u^{2k} + β√N u^k a) du,
```
`N` the sample size. In the state-density variable `τ = u^{2k}` the kernel is `g(Nτ)` with the
**phase kernel** `g(t) = (√t)^p e^{-βt + β√t a}`, so `T(N) = ∏ 1/(2kᵢ) ∫₀¹ v(τ) g(Nτ) dτ` with the
exact density `v` of unit 224. This file provides the two ingredients of the exact moment identity:
* `integral_unitBox_monomial_eq_stateDensity`: the real monomial bridge carrying the Jacobian;
* `basis_scaling`: for one basis term, the substitution `t = Nτ` and the binomial expansion of
  `(log N - log t)^j` give
  `∫₀¹ τ^{μ-1}(-log τ)^j g(Nτ) dτ =
     N^{-μ} ∑_{i≤j} C(j,i) (log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t) dt`
  (`truncMom-/

-- section/variable skeleton:
open MeasureTheory Set Real
namespace Grammar
end Grammar

/-- The phase kernel `g(t) = (√t)^p exp(-βt + β√t a)`. -/
noncomputable def phaseKernel (β a : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt t ^ p * Real.exp (-(β * t) + β * Real.sqrt t * a)


==================== Grammar/MonomialPhaseTail.lean

/-!# Exponentially small tails and the asymptotic form of the monomial moments (Stage 2c)

Unit 229 (Taylor-tree programme). The truncated moments `∫₀^N t^{ν-1}(-log t)^i g(t) dt` of unit 227
differ from the **full fluctuation moments**
`fluctMoment β a p ν i = ∫₀^∞ t^{ν-1}(-log t)^i g(t) dt`
by a tail that is exponentially small: the phase kernel satisfies
`g(t) ≤ (√t)^p e^{βa²/2} e^{-βt/2}` (`phaseKernel_le`, from `2√t a ≤ t + a²`), and for `t ≥ 1` the
power–log factor is at most `t^{⌈ν⌉+i+p}`, so the integrand is bounded by `C e^{-βt/4}`
(`tail_integrand_le`, using `t^m e^{-βt/4} ≤ m!(4/β)^m`), giving
`|∫_N^∞ …| ≤ C (4/β) e^{-βN/4}` (`tail_le`). Consequently the exact identity of Headline XXIII
becomes the **asymptotic form** (Headline XXIII′, `monomialPhase_isBigO`):
```
T(N) - ∏ 1/(2kᵢ) ∑_{(μ,j,c)} c N^{-μ} ∑_{i≤j} C(j,i) (log N)^{j-i} fluctMoment β a p μ i
  = O(e^{-βN/8})   as N → ∞,-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Asymptotics
namespace Grammar
end Grammar

/-- The full log-weighted fluctuation moment `∫₀^∞ t^{ν-1} (-log t)^i g(t) dt`. -/
noncomputable def fluctMoment (β a : ℝ) (p : ℕ) (ν : ℝ) (i : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t


==================== Grammar/MonomialRep.lean

/-!# Polynomial data as finite monomial lists, with the `ℓ¹` coefficient norm (Stage 3c)

Unit 233 (Taylor-tree programme; Astra #27). Polynomial amplitudes and phases enter Stage 3 only
through their monomial coefficients, so we represent a real polynomial on `ℝ^d` as a finite list of
`(exponent γ, coefficient c)` pairs (`MonoRep d`), evaluated by `eval P u = ∑ c · ∏ uᵢ^{γᵢ}`, with
the
coefficient norm `‖P‖₁ = ∑ |c|` (`l1`). Products are the list of pairwise products
(`MonoRep.mul`, `eval_mul`), so `‖PQ‖₁ ≤ ‖P‖₁ ‖Q‖₁` is an equality (`l1_mul`) and
`‖P^p‖₁ ≤ ‖P‖₁^p` (`l1_pow_le`); on the closed unit cube `|P(u)| ≤ ‖P‖₁` (`abs_eval_le_l1`). The
phase fluctuation `J = ξ − ξ(0)` is the sublist of terms with `γ ≠ 0` (`MonoRep.fluct`,
`eval_fluct`). Every `MvPolynomial (Fin d) ℝ` gives such a list (its support with coefficients), but
Stage 3 only needs the list form. No `sorry` and no additional-/

-- section/variable skeleton:
open Set
namespace Grammar
namespace MonoRep
variable {d : ℕ}
end MonoRep
end Grammar

/-- A polynomial in `d` variables as a finite list of monomials `(γ, c)`. -/
abbrev MonoRep (d : ℕ) := List ((Fin d → ℕ) × ℝ)

/-- The monomial `∏ uᵢ^{γᵢ}`. -/
def mono (γ : Fin d → ℕ) (u : Fin d → ℝ) : ℝ := ∏ i, u i ^ γ i

/-- Evaluation `∑ c · u^γ`. -/
def eval (P : MonoRep d) (u : Fin d → ℝ) : ℝ := (P.map fun t => t.2 * mono t.1 u).sum

/-- Product of representations: all pairwise products. -/
def mul (P Q : MonoRep d) : MonoRep d :=
  P.flatMap fun s => Q.map fun t => (s.1 + t.1, s.2 * t.2)

/-- Powers by iterated products (`pow P 0 = [(0, 1)]`, the constant `1`). -/
def pow (P : MonoRep d) : ℕ → MonoRep d
  | 0 => [(0, 1)]
  | p + 1 => mul P (pow P p)

/-- The fluctuation part `ξ − ξ(0)`: the terms with `γ ≠ 0`. -/
def fluct (P : MonoRep d) : MonoRep d := P.filter fun t => t.1 ≠ 0


==================== Grammar/OrthantReflection.lean

/-!# Orthant reflection as a weighted measure identity

A resolution chart is a cube in all orthants; grammar's standard box is the positive orthant
`(0, b]^d`.  The coordinate reflection `y ↦ (s_i y_i)` with signs `|s_i| = 1` preserves Lebesgue
measure (`map_signReflect_volume`), fixes every even monomial `y^e` (`mono_signReflect_of_even`) and
turns `y^h` on the positive box into `|y|^h` on the reflected box: the weighted measure identity
`map_signReflect_weightedPosBox`.  With `map_withDensity_comp` this is a one-line consequence of the
Lebesgue invariance.-/

-- section/variable skeleton:
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace Grammar
open MonoRep
variable {d : ℕ}
end Grammar

/-- The coordinate reflection by signs `s`. -/
def signReflect (s : Fin d → ℝ) (y : Fin d → ℝ) : Fin d → ℝ := fun i => s i * y i


==================== Grammar/PosteriorFrechet.lean

/-!# The Fréchet derivative of the posterior average on `C(K,ℝ)` (§20, Banach-form Stein)

The weighted functional `N_φ(g) = ∫ φ S_ν(g) dρ` (`weightedFunctional`) is Fréchet differentiable
on `C(K,ℝ)` with the sup norm, with derivative `h ↦ β ∫ φ S_{ν+1/2}(g) h dρ` (`weightedDeriv`,
★ `hasFDerivAt_weightedFunctional`): the pointwise mean value theorem for `S_ν` (derivative
`β S_{ν+1/2}`) and uniform continuity of `S_{ν+1/2}` on compact intervals give the little-o
uniformly in `x`.  By the quotient rule the posterior average `g ↦ ⟨f⟩_g = N_f(g)/D(g)` is Fréchet
differentiable with

★★ `hasFDerivAt_compactAvg`: `D⟨f⟩_g[h] = β(⟨f h√t⟩_g − ⟨f⟩_g ⟨h√t⟩_g)` (`posteriorDeriv`,
`posteriorDeriv_apply`),

and Stein's identity of `CompactBaseStein` takes its **Banach form**

★★★ `GaussianField.integral_eval_mul_compactAvg_fderiv`:
`E[G(x₀) F_f(G)] = E[DF_f(G)[𝒞(x₀,·)]]` for `F_f(g) = ⟨f⟩_g` (Astra #16-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
namespace Grammar
section Weighted
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (β ν : ℝ) (ρ : Measure K) [IsFiniteMeasure ρ]
variable (hβ : 0 < β) (hν : 0 < ν)
include hβ hν
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
end Weighted
section Posterior
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
include hβ hlam hρ
omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ in
omit [CompactSpace K] [BorelSpace K] [IsFiniteMeasure ρ] hβ hlam hρ in
end Posterior
section Banach
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (Γ : GaussianField 𝒞 P) {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β)
  (hlam : 0 < lam) (hρ : ρ ≠ 0) [Nonempty K]
include hβ hlam hρ
end Banach
end Grammar

/-- The derivative `h ↦ β ∫ φ S_{ν+1/2}(g) h dρ` as a linear map. -/
noncomputable def weightedDerivLM (φ g : C(K, ℝ)) : C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun h := β * ∫ x, φ x * fluctuation β (ν + 1 / 2) (g x) * h x ∂ρ
  map_add' h₁ h₂ := by
    have := integral_add (integrable_weightedDeriv_integrand β ν ρ hβ hν φ g h₁)
      (integrable_weightedDeriv_integrand β ν ρ hβ hν φ g h₂)
    simp only [ContinuousMap.add_apply, mul_add]
    rw [this]
    ring
  map_smul' c h := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : (fun x => φ x * fluctuation β (ν + 1 / 2) (g x) * (c * h x)) =
        fun x => c * (φ x * fluctuation β (ν + 1 / 2) (g x) * h x) := by
      funext x; ring
    rw [this, integral_const_mul]
    ring

/-- The uniform bound on `S_{ν+1/2}(g x)`. -/
noncomputable def fluctBound (g : C(K, ℝ)) : ℝ :=
  Real.exp (β * ‖g‖ ^ 2 / 2) * (β / 2) ^ (-(ν + 1 / 2)) * Real.Gamma (ν + 1 / 2)

/-- The derivative as a continuous linear map. -/
noncomputable def weightedDeriv (φ g : C(K, ℝ)) : C(K, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (weightedDerivLM β ν ρ hβ hν φ g)
    (β * (‖φ‖ * fluctBound β ν g * ρ.real univ)) fun h => by
    rw [weightedDerivLM_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hβ, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    have hb := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun x => φ x * fluctuation β (ν + 1 / 2) (g x) * h x)
      (C := ‖φ‖ * fluctBound β ν g * ‖h‖) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (fluctuation_pos β _ _ hβ (by linarith))]
        exact mul_le_mul (mul_le_mul (abs_coe_le_norm φ x)
          (fluctuation_le_fluctBound β ν hβ hν g x)
          (fluctuation_pos β _ _ hβ (by linarith)).le (norm_nonneg _)) (abs_coe_le_norm h x)
          (abs_nonneg _) (mul_nonneg (norm_nonneg _) (fluctBound_nonneg β ν hβ hν g)))
    exact hb.trans (le_of_eq (by ring))

/-- The Fréchet derivative of `g ↦ ⟨f⟩_g` at `g`, as a continuous linear map:
`(1/D) N_f' − (N_f/D²) D'`. -/
noncomputable def posteriorDeriv (f g : C(K, ℝ)) : C(K, ℝ) →L[ℝ] ℝ :=
  (compactD β lam ρ g)⁻¹ • weightedDeriv β lam ρ hβ hlam f g -
    (compactWeighted β lam ρ g f / compactD β lam ρ g ^ 2) • weightedDeriv β lam ρ hβ hlam 1 g

/-- ★★ **The posterior average is Fréchet differentiable on `C(K,ℝ)`.** -/
theorem hasFDerivAt_compactAvg (f g : C(K, ℝ)) :
    HasFDerivAt (fun g : C(K, ℝ) => compactAvg β lam ρ g f) (posteriorDeriv ρ hβ hlam f g) g := <proof>


==================== Grammar/PosteriorVarianceExpansion.lean

/-!# The posterior variance to all orders (§20, posterior cumulants)

The posterior variance of an observable for a fixed sample is the second connected coefficient
`Z₃/Z₂ − (Z₁/Z₂)²` (`Z₁ = Z_N[ηf]`, `Z₂ = Z_N[η]`, `Z₃ = Z_N[ηf²]`; `SourceLog`).  Given the
all-orders quotient expansions `cutoff_div_isBigO` of `Z₁/Z₂` and `Z₃/Z₂` with quotient blocks
`R₁, R₃`, the variance has the all-orders expansion with the **variance blocks**
`κ₂(j) = R₃(j) − Σ_{i ≤ j} R₁(i) R₁(j − i)` (`varianceBlocks`):

★★ `cutoff_variance_isBigO`:
`Z₃/Z₂ − (Z₁/Z₂)² − Σ_{j<J} κ₂,j(log N) N^{−j/Q} = O(N^{−J/Q} (1 + log N)^{D(2J+2)})`.

Route: `twoScale_variance_isBigO` is the abstract two-scale statement (`x = N^{−1/Q}`,
`g = (1 + log N)^D`): with `E₁ = P₁ − S₁`, `E₃ = P₃ − S₃` the two quotient remainders and
`S₁² = Σ_{k<J} (Σ_{i≤k} R₁ i R₁ (k−i)) x^k + T` (`sum_mul_sum_eq_cauchy_add_tail`, the tail `T`
carrying the d-/

-- section/variable skeleton:
open Filter Topology Asymptotics Finset
namespace Grammar
variable {Q D : ℕ}
section Empirical
open scoped ContDiff
open SmoothEngine
variable {d : ℕ} {η ζ f : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}
end Empirical
end Grammar

/-- ★★★ **The posterior variance of a smooth observable to all orders, fixed sample**: for
`C^∞` weights `η`, field `ζ` and observable `f`, with the box-leading index `λ ≥ m₀/Q` and a
nonzero leading denominator block,
`Z_N[ηf²]/Z_N[η] − (Z_N[ηf]/Z_N[η])² − Σ_{j<J} κ₂,j(log N) N^{−j/Q}
  = O(N^{−J/Q} (1 + log N)^{(d−1)(2J+2)})`,
where `κ₂,j = varianceBlocks` are the variance blocks of the intrinsic coefficients
`empCoeff (ηf)`, `empCoeff η`, `empCoeff (ηf²)`. -/
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
        (N ^ (-(1 / (Qamb k : ℝ)))) ^ J * ((1 + Real.log N) ^ (d - 1)) ^ (2 * J + 2) := <proof>


==================== Grammar/PowLogCalculus.lean

/-!# Power–log representations and the one-coordinate convolution calculus

Unit 223 (Taylor-tree programme, Stage 1a; Astra #26). The exact state density of a monomial on
the unit box is a finite combination of `τ^{μ-1} (-log τ)^j` (`powLogBasis μ j`). We represent such
combinations concretely as lists of triples `(μ, j, c)` (`PowLogRep`, evaluated by
`PowLogRep.eval`), and prove that peeling one coordinate (original weight `t^w`, kernel weight
`t^{w-1}`),
```
(powLogConv w v)(z) = ∫_{[z,1]} t^{w-1} v(z/t) dt,
```
acts on representations by an explicit linear map `PowLogRep.conv w` (`eval_conv`). The kernel
identity is `t^{w-1} (z/t)^{μ-1} (-log(z/t))^j = z^{μ-1} t^{α-1} (log t - log z)^j`,
`α = w - μ + 1`, and the one-dimensional integrals `G_j(z) = ∫_z^1 t^{α-1} (log t - log z)^j dt`
obey `G_0 = (1 - z^α)/α`, `G_{j+1} = (-log z)^{j+1}/α - ((j+1)/α) G_j` for `α ≠ 0` (partial
fractions: th-/

-- section/variable skeleton:
open MeasureTheory Set Real intervalIntegral
namespace Grammar
namespace PowLogRep
end PowLogRep
end Grammar

/-- A finite power–log combination: triples `(exponent, log degree, coefficient)`. -/
abbrev PowLogRep := List (ℝ × ℕ × ℝ)


==================== Grammar/PrincipalPartUniqueness.lean

/-!# Uniqueness of bounded principal parts and the polar coefficients of a cutoff expansion

`polarPart D a μ s = Σ_{q≤D} a_q/(s−μ)^{q+1}`.  If the difference of two polar parts is bounded
on a punctured neighbourhood of `μ` then the coefficients agree
(`polarPart_eq_of_sub_isBigO_one`; descending induction on the pole order: multiply by
`(s−μ)^{D+1}`, the product tends to `a_D − b_D` and to `0`).

Applied to the continuation expression `F_U = mellin R_U + principalParts U` of a cutoff
expansion (`MellinRegularization`): at a retained exponent `0 < μ₀ < U`,
`F_U − polarPart D (polarCoeff c μ₀) μ₀` is bounded near `μ₀`
(`mellinContinuation_sub_polarPart_isBigO_one`) with `polarCoeff c μ₀ q = (−1)^{q+1} q! c_{μ₀,q}`,
and ANY polar part with this property has these coefficients (`polarCoeff_unique`).  So the
coefficients `c_{μ₀,q}` of `N^{−μ₀}(log N)^q` are the unique local principal-part data-/

-- section/variable skeleton:
open Filter Topology Asymptotics Set MeasureTheory
namespace Grammar
variable {Q D : ℕ} {E : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
end Grammar

/-- The polar part `Σ_{q≤D} a_q/(s−μ)^{q+1}`. -/
noncomputable def polarPart (D : ℕ) (a : ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (D + 1), a q / (s - μ) ^ (q + 1)

/-- The continuation expression `F_U = mellin R_U + principalParts U` (`MellinRegularization`). -/
noncomputable def mellinContinuation (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) :
    ℂ :=
  mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s

/-- The polar coefficients at `μ₀` in the standard `(s−μ₀)^{−(q+1)}` convention:
`a_q = (−1)^{q+1} q! c_{μ₀,q}`. -/
noncomputable def polarCoeff (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) : ℂ :=
  (-1) ^ (q + 1) * (q.factorial : ℂ) * (c μ₀ q : ℂ)

/-- ★★★ **Uniqueness of the polar coefficients of a cutoff expansion**: any polar part `a` at a
retained exponent `0 < μ₀ < U` with `F_U − polarPart D a μ₀ = O(1)` near `μ₀` has
`a_q = (−1)^{q+1} q! c_{μ₀,q}` — the coefficients of `N^{−μ₀}(log N)^q` are the unique local
principal-part data of the continued Mellin transform. -/
theorem polarCoeff_unique (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) {a : ℕ → ℂ}
    (ha : (fun s => mellinContinuation Q D E c U s - polarPart D a (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = polarCoeff c μ₀ q := <proof>


==================== Grammar/QuenchedSource.lean

/-!# The anchored quenched source (§20, averaged posterior cumulants)

On the compact base the limit posterior of a random continuous field `g` has the normalised
weights `S_λ(g(x)) dρ(x) / D_ρ(g)`; the posterior average of an observable `φ` is
`⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)` (`compactAvg`).  For a bounded observable `f` the **anchored
source** is `log⟨e^{εf}⟩_g = log (D(g; ρ e^{εf}) / D(g; ρ))` (`logTilt`), whose `ε`-derivatives
are the posterior cumulants of `f`:

* ★ `abs_logTilt_le`: `|log⟨e^{εf}⟩_g| ≤ |ε| ‖f‖_∞` — the anchoring makes the source bounded
  without any evidence moment;
* ★★ `hasDerivAt_logTilt`: `∂_ε log⟨e^{εf}⟩_g = ⟨f⟩_{g,ε}` (the tilted average `compactAvgTilt`),
  so `deriv (logTilt) 0 = ⟨f⟩_g` and `deriv (deriv logTilt) 0 = ⟨f²⟩_g − ⟨f⟩_g²` (`compactVar`,
  `deriv_deriv_logTilt_zero`).

Averaged over the field, `Ψ(ε) = E log⟨e^{εf}⟩_G` (`quenchedSource`):

* ★★★ `has-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
namespace Grammar
section Defs
variable {K : Type*} [MeasurableSpace K]
end Defs
section Bounded
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (g : C(K, ℝ)) {f : K → ℝ} (hf : Measurable f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |f x| ≤ M)
include hβ hlam in
omit [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hM in
include hβ hlam hf hM in
include hβ hlam hf hM in
include hβ hlam hf hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM0 hM in
include hβ hlam hf hM in
end Bounded
section Quenched
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
  (G : Ω → C(K, ℝ)) (hG : Measurable fun q : Ω × K => G q.1 q.2)
  {f : K → ℝ} (hf : Measurable f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |f x| ≤ M)
include hβ hlam hG in
include hβ hlam hG hf in
include hβ hlam hG hf in
include hβ hlam hG hf in
include hβ hlam hG hf in
include hβ hlam hG hf hM0 hM in
include hβ hlam hG hf hM0 hM in
include hβ hlam hG hf hM0 hM in
include hβ hlam hG hf hM0 hM in
include hβ hlam hG hf hM0 hM in
end Quenched
end Grammar

/-- The weighted evidence `∫ φ S_λ(g) dρ`. -/
noncomputable def compactWeighted (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  ∫ x, φ x * fluctuation β lam (g x) ∂ρ

/-- The limit posterior average `⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)`. -/
noncomputable def compactAvg (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β lam ρ g φ / compactD β lam ρ g

/-- The tilted evidence `D(g; ρ e^{εf}) = ∫ e^{εf} S_λ(g) dρ`. -/
noncomputable def compactTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  compactWeighted β lam ρ g fun x => Real.exp (ε * f x)

/-- The tilted average `⟨f⟩_{g,ε} = ∫ f e^{εf} S_λ(g) dρ / D(g; ρ e^{εf})`. -/
noncomputable def compactAvgTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  compactWeighted β lam ρ g (fun x => f x * Real.exp (ε * f x)) / compactTilt β lam ρ g f ε

/-- The anchored source `log⟨e^{εf}⟩_g = log (D(g; ρ e^{εf}) / D(g; ρ))`. -/
noncomputable def logTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  Real.log (compactTilt β lam ρ g f ε / compactD β lam ρ g)

/-- The limit posterior variance `⟨f²⟩_g − ⟨f⟩_g²`. -/
noncomputable def compactVar (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) : ℝ :=
  compactAvg β lam ρ g (fun x => f x ^ 2) - compactAvg β lam ρ g f ^ 2

/-- ★ **The anchored source is bounded by the observable**: `|log⟨e^{εf}⟩_g| ≤ |ε| M`. -/
theorem abs_logTilt_le (hρ : ρ ≠ 0) (ε : ℝ) : |logTilt β lam ρ g f ε| ≤ |ε| * M := <proof>

/-- The **anchored quenched source** `Ψ(ε) = E log⟨e^{εf}⟩_G`. -/
noncomputable def quenchedSource (β lam : ℝ) (ρ : Measure K) (P : Measure Ω) (G : Ω → C(K, ℝ))
    (f : K → ℝ) (ε : ℝ) : ℝ :=
  ∫ ω, logTilt β lam ρ (G ω) f ε ∂P

theorem deriv_quenchedSource (hρ : ρ ≠ 0) :
    deriv (quenchedSource β lam ρ P G f) = fun ε => ∫ ω, compactAvgTilt β lam ρ (G ω) f ε ∂P := <proof>

/-- ★★★ `Ψ''(0) = E[⟨f²⟩_G − ⟨f⟩_G²]`: the second derivative of the quenched source at the origin
is the averaged posterior variance. -/
theorem deriv_deriv_quenchedSource_zero (hρ : ρ ≠ 0) :
    deriv (deriv (quenchedSource β lam ρ P G f)) 0 = ∫ ω, compactVar β lam ρ (G ω) f ∂P := <proof>


==================== Grammar/QuotientBlocks.lean

/-!# Quotient blocks (§20, posterior expectations beyond the first correction)

Formal division of two coefficient sequences `A, B : ℕ → K` over a field `K` with `B 0 ≠ 0`: the
**quotient blocks** `R = quotientBlocks A B` are the coefficients of the power series
`(Σ A_j x^j)/(Σ B_j x^j)`, so that `Σ_{i ≤ j} B_i R_{j−i} = A_j` for every `j`
(`sum_mul_quotientBlocks`) and `R` satisfies the recursion `R_0 = A_0/B_0`,
`R_{j+1} = (A_{j+1} − Σ_{i ≤ j} B_{i+1} R_{j−i})/B_0`
(`quotientBlocks_zero`, `quotientBlocks_succ`).

For the posterior expectation `E_N[φ]/E_N[1]` the field is the rational functions of `log N`, or
the reals pointwise in `N`: `x = N^{−1/Q}` and `A_j, B_j` are the polynomials in `log N` attached
to the `j`-th lattice exponent (consult #158, item 3: keep the rational-log blocks exact for
power accuracy; expand a block in `1/log N` separately).

Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open PowerSeries Finset
namespace Grammar
variable {K : Type*} [Field K]
end Grammar

/-- The quotient blocks of `A` by `B`: the coefficients of `(Σ A_j x^j) · (Σ B_j x^j)⁻¹`. -/
noncomputable def quotientBlocks (A B : ℕ → K) (j : ℕ) : K :=
  PowerSeries.coeff j (PowerSeries.mk A * (PowerSeries.mk B)⁻¹)


==================== Grammar/RegularCase.lean

/-!# The regular case: `S_{1/2}` and the half-integer ladder (grammar §4 `ex:fluctuation_half`)

For regular models the RLCT is `λ = 1/2` on every chart, and the grammar paper's Example
`ex:fluctuation_half` records two facts about the base fluctuation function `S_{1/2}`:

* **Gaussian form.** Completing the square (`u = √t`, then `-βu²+βau = -β(u-a/2)²+βa²/4`),
  `S_{1/2}(a) = √(2/β) · e^{βa²/4} · ∫₀^∞ e^{-(u - a√(β/2))²/2} du`. The paper evaluates the
  remaining Gaussian tail as an error function; Mathlib has no `erf`, so we stop at the tail integral.
* **Half-integer ladder.** Every `S_{(n+1)/2}` is an `a`-derivative of `S_{1/2}`:
  `∂ₐⁿ S_{1/2}(a) = βⁿ S_{(n+1)/2}(a)`, so for regular models all fluctuation functions reduce to
  derivatives of the single function `S_{1/2}`.-/

-- section/variable skeleton:
open Real MeasureTheory
namespace Grammar
end Grammar

/-- **Half-integer ladder** (grammar §4 `ex:fluctuation_half`): the `n`-th `a`-derivative of `S_{1/2}`
is `βⁿ S_{(n+1)/2}`, so `S_{(n+1)/2}(a) = β^{-n} ∂ₐⁿ S_{1/2}(a)`. Iterates the derivative ladder
`S'_λ = β S_{λ+1/2}`. -/
theorem fluctuation_half_iteratedDeriv (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    iteratedDeriv n (fun a => fluctuation β (1 / 2) a)
      = fun a => β ^ n * fluctuation β (((n : ℝ) + 1) / 2) a := <proof>

/-- **Gaussian form of `S_{1/2}`** (grammar §4 `ex:fluctuation_half`): completing the square gives
`S_{1/2}(a) = √(2/β) · e^{βa²/4} · ∫₀^∞ e^{-(u - a√(β/2))²/2} du`. (The paper writes the tail integral
as `(√π/2)(1 + erf(a√β/2))`; Mathlib has no error function.) -/
theorem fluctuation_half_gaussian (β a : ℝ) (hβ : 0 < β) :
    fluctuation β (1 / 2) a
      = Real.sqrt (2 / β) * Real.exp (β * a ^ 2 / 4)
        * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(u - a * Real.sqrt (β / 2)) ^ 2 / 2) := <proof>


==================== Grammar/ResolvedDepth.lean

/-!# Intrinsic depth and resonance data on the resolved manifold

Consult #127, Units D5a–D5b. At every point `P` of the exceptional divisor `D = {K ∘ π = 0}` of
a Watanabe modification `R`, hironaka supplies an even chart box centred at `P`
(`exists_evenChartBox`): a chart `φ` of the maximal analytic atlas with `φ P = 0`, in which the
phase is the even monomial `∏ u_j^{2 k_j}` and the Jacobian of the blow-down is
`b(u) ∏ u_j^{h_j}` with an analytic nonvanishing unit `b`. The **pair data** of the box is the
multiset of `(k_j, h_j)` over the active coordinates `k_j > 0`.

* `EvenChartBox.pairData_eq_of_centered` (**the atlas adapter, D5a**): two even chart boxes
  centred at the same point have the same pair data. The transition `H = φ' ∘ φ⁻¹` is analytic
  near `0` with analytic inverse (both charts lie in the maximal atlas), the two phases agree,
  and the two Jacobian laws are related by -/

-- section/variable skeleton:
open Set Filter Topology Function
open scoped Manifold ContDiff
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open IsManifold (maximalAtlas)
namespace Grammar
namespace NormalCrossing
variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {W : TopologicalSpace.Opens (Fin d → ℝ)}
  {R : WatanabeModificationOn K W}
namespace EvenChartBoxDepth
variable (E : EvenChartBox R)
end EvenChartBoxDepth
open EvenChartBoxDepth
section Intrinsic
variable (R)
open Classical in
variable (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
open Classical in
open Classical in
end Intrinsic
end NormalCrossing
end Grammar

/-- The active coordinates of an even chart box. -/
def active : Finset (Fin d) := Finset.univ.filter fun j => 0 < E.k j

/-- The pair data `{(k_j, h_j) : j active}` of an even chart box. -/
def pairData : Multiset (ℕ × ℕ) := (active E).val.map fun j => (E.k j, E.h j)

/-- The exceptional divisor `{K ∘ π = 0}`. -/
def divisor : Set R.U := {P | K (R.gv P) = 0}

theorem exists_centeredEvenChartBox (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x) {P : R.U}
    (hP : P ∈ divisor R) : ∃ E : EvenChartBox R, P ∈ E.φ.source ∧ E.φ P = 0 := <proof>

/-- ★ **The intrinsic pair data** of a point of the resolved manifold: the pair data of any even
chart box centred at the point (empty off the divisor). -/
noncomputable def pairs (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x) (P : R.U) :
    Multiset (ℕ × ℕ) :=
  if hP : P ∈ divisor R then pairData (Classical.choose (exists_centeredEvenChartBox R hK0 hP))
  else 0

/-- The intrinsic depth `d_D(P)`: the number of walls through `P`. -/
noncomputable def depth (P : R.U) : ℕ := (pairs R hK0 P).card

/-- Resonance of an exponent `μ` with a wall of data `(k, h)`: `2kμ ∈ h + 1 + ℕ`. -/
def Resonates (μ : ℝ) (p : ℕ × ℕ) : Prop := ∃ m : ℕ, 2 * (p.1 : ℝ) * μ = (p.2 : ℝ) + 1 + m

/-- The resonance count `r_μ(P)`: the number of walls through `P` resonant with `μ`. -/
noncomputable def resonanceCount (μ : ℝ) (P : R.U) : ℕ :=
  ((pairs R hK0 P).filter (Resonates μ)).card


==================== Grammar/ResolvedDepthLocal.lean

/-!# The local coordinate formula for the pair data; the closed depth and resonance filtrations

Consult #127, Unit D5c. In an even chart box `E` (centred anywhere), the intrinsic pair data of a
point `Q` of the chart source is read off from its chart coordinate `u₀ = φ Q`:

  `pairs Q = {(k_j, h_j) : j active, u₀_j = 0}`   (`pairs_eq_of_mem_source`).

Proof: translating the chart by `u₀`, the phase becomes `a(v) ∏_{j : u₀_j = 0} v_j^{2k_j}` with the
analytic nonvanishing unit `a(v) = ∏_{j : u₀_j ≠ 0} (v_j + u₀_j)^{2k_j}` (`translatedForm`), and the
Jacobian becomes `b_T(v) ∏_{j : u₀_j = 0} v_j^{h_j}` with the unit
`b_T(v) = b(v + u₀) ∏_{j : u₀_j ≠ 0} (v_j + u₀_j)^{h_j}` (the inactive exponents vanish, hironaka
`h_eq_zero_of_k_eq_zero`); comparing with any even chart box centred at `Q` through the
translated transition `H v = φ' (φ⁻¹ (v + u₀))` (analytic near `0` with analytic inverse), the-/

-- section/variable skeleton:
open Set Filter Topology Function
open scoped Manifold ContDiff
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open IsManifold (maximalAtlas)
namespace Grammar
namespace NormalCrossing
variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {W : TopologicalSpace.Opens (Fin d → ℝ)}
  {R : WatanabeModificationOn K W}
namespace EvenChartBoxDepth
variable (E : EvenChartBox R)
end EvenChartBoxDepth
open EvenChartBoxDepth
section Local
variable (R) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
open Classical in
end Local
end NormalCrossing
end Grammar

/-- The locus of depth at least `c`. -/
def depthGE (c : ℕ) : Set R.U := {P | c ≤ depth R hK0 P}

/-- The locus of resonance count at least `c`. -/
def resonanceGE (μ : ℝ) (c : ℕ) : Set R.U := {P | c ≤ resonanceCount R hK0 μ P}


==================== Grammar/SignedBoxPackets.lean

/-!# Signed boxes: sign patterns, reflections, the signed analytic packet (CCCXXXVI; phase G, G1)

Consult #100 §1, §5. The signed box `[−a,a]^d` is covered by the `2^d` reflected copies
`R_σ [0,a]^d` of the positive box, `R_σ(w)_i = σ_i w_i` (`refl σ`, built on `signReflect`). This
unit provides the sign patterns `CoordSign d = Fin d → Bool`, the real and complex reflections and
their basic identities (involution, measurability, Lebesgue invariance `map_refl_volume`,
evenness of the monomial phase `phase_refl`, `complexify_refl`), the orthant pieces
`orthantBox σ a = R_σ⁻¹ [0,a]^d` of the signed box, the reflection as a measurable equivalence, and
the set-integral change of variables `setIntegral_refl`, the **signed analytic packet**
`HolomorphicSignedBoxExtension a ϕ φ` (the packet of CCCXXX over the signed box) with its pullbacks
`A.pullback σ : HolomorphicBoxExtension a (ϕ ∘ R_σ) (φ ∘ R-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
namespace Grammar
namespace WaterFilling
open CoordModel
variable {d : ℕ}
variable (a : ℝ)
namespace HolomorphicSignedBoxExtension
variable {a} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension a ϕ φ)
end HolomorphicSignedBoxExtension
variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hd : 0 < d) (ha : 0 < a)
include hk hd ha in
variable {a} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)
  (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)
end WaterFilling
end Grammar

/-- A sign pattern on the coordinates. -/
abbrev CoordSign (d : ℕ) := Fin d → Bool

/-- The sign vector `±1` of a pattern. -/
def sgn (σ : CoordSign d) : Fin d → ℝ := fun i => if σ i then 1 else -1

/-- The reflection `R_σ (w)_i = σ_i w_i`. -/
def refl (σ : CoordSign d) : (Fin d → ℝ) → (Fin d → ℝ) := signReflect (sgn σ)

/-- The orthant piece `R_σ⁻¹ [0,a]^d` of the signed box. -/
def orthantBox (σ : CoordSign d) (a : ℝ) : Set (Fin d → ℝ) := refl σ ⁻¹' piBox d (Icc 0 a)


==================== Grammar/SmoothAffineFamily.lean

/-!# Smooth amplitude families from affine chart coordinates (consult #117 U6b.1)

The affine chart-coordinate map of a face of the box: given an enumeration
`e : Fin da ≃ {i // i ∈ J}` of the active coordinates, a sign pattern `σ` and fixed complementary
coordinates `s`, the map `affineMap e σ s : ℝ^{da} → ℝ^d` sends `v` to the point whose
`J`-coordinates are `σ_i · v_{e⁻¹ i}` and whose other coordinates are `s`. It is smooth
(`contDiff_affineMap`), jointly continuous in `(s, v)` (`continuous_affineMap_pair`), and the
coordinate derivatives of a pullback `G ∘ affineMap` are the reflected pushed-forward derivatives
(★ `pd_comp_affineMap`, `pdPow_comp_affineMap`, ★★ `pdMulti_comp_affineMap`:
`∂^m (G ∘ A) = (∏ σ_{e j}^{m_j}) · (∂^{extendIdx e m} G) ∘ A`). Consequently the pullback of a
smooth `G` along a continuous family of complementary coordinates is a `SmoothAmplitudeFamily`
(★★★ `SmoothA-/

-- section/variable skeleton:
open Set Filter Topology
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d da : ℕ} {J : Finset (Fin d)}
variable (e : Fin da ≃ {i // inJ J i}) (σ : WaterFilling.CoordSign d) (s : {i // ¬ inJ J i} → ℝ)
end SmoothEngine
end Grammar

/-- The affine chart-coordinate map: face coordinates `v ∘ e.symm` reflected by `σ`,
complementary coordinates fixed at `s`. -/
def affineMap (e : Fin da ≃ {i // inJ J i}) (σ : WaterFilling.CoordSign d)
    (s : {i // ¬ inJ J i} → ℝ) (v : Fin da → ℝ) : Fin d → ℝ :=
  glue J (fun i => WaterFilling.sgn σ i * v (e.symm i)) s

/-- The pullback of a smooth `G` along the affine chart maps of a continuous family
`s ↦ sc s` of complementary coordinates, as a smooth amplitude family on `ℝ^{da}`. -/
noncomputable def SmoothAmplitudeFamily.ofAffine {S : Type*} [TopologicalSpace S]
    {sc : S → {i // ¬ inJ J i} → ℝ} (hsc : Continuous sc) (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (b : ℝ) :
    SmoothAmplitudeFamily S da b where
  amp s v := G (affineMap e σ (sc s) v)
  smooth s := hG.comp (contDiff_affineMap e σ (sc s))
  deriv_cont m := by
    simp only [pdMulti_comp_affineMap]
    exact (continuous_const.mul ((contDiff_pdMulti hG _ _).continuous.comp
      ((continuous_affineMap_pair e σ).comp
        ((hsc.comp continuous_fst).prodMk continuous_snd)))).continuousOn


==================== Grammar/SmoothAmplitudeFamily.lean

/-!# Smooth amplitude families: uniform bounds and parameter continuity (consult #117 §2, U4b–U4c)

A `SmoothAmplitudeFamily S d b` is a family `s ↦ amp s` of smooth amplitudes on `ℝ^d` whose
mixed coordinate derivatives of every order are jointly continuous on `S × [0,b]^d`. On a compact
base this gives (i) a rectangular mixed-derivative bound uniform in `s` at every depth
(`exists_uniform_rect_bound`), hence (ii) the depth expansion with a constant uniform in `s`
(`uniform_depth`, from `smooth_expansion_at_depth_uniform`); (iii) joint continuity of the flat
face amplitudes `G_{J,m}(s, w) = (R_K^p ∂^m amp s)(0_J, w)` (`continuousOn_faceAmp_family`, by
list induction through the Taylor remainders, using only the derivative algebra `pdMulti_add`),
hence by dominated convergence (iv) continuity in `s` of every face coefficient integral and of
the canonical coefficients ★ `continuous_smoothCoe-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace SmoothAmplitudeFamily
variable {S : Type*} [TopologicalSpace S] {b : ℝ} (F : SmoothAmplitudeFamily S d b)
variable {h k p : Fin d → ℕ} {β : ℝ} {L : ℕ}
end SmoothAmplitudeFamily
end SmoothEngine
end Grammar

/-- The closed box `[0,b]^d`. -/
def closedBox (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc 0 b

/-- A family of smooth amplitudes with jointly continuous mixed derivatives on `S × [0,b]^d`. -/
structure SmoothAmplitudeFamily (S : Type*) [TopologicalSpace S] (d : ℕ) (b : ℝ) where
  /-- the amplitudes -/
  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  /-- joint continuity of every mixed coordinate derivative on `S × [0,b]^d` -/
  deriv_cont : ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (amp z.1) z.2)
    (Set.univ ×ˢ closedBox d b)

structure SmoothAmplitudeFamily (S : Type*) [TopologicalSpace S] (d : ℕ) (b : ℝ) where
  /-- the amplitudes -/
  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  /-- joint continuity of every mixed coordinate derivative on `S × [0,b]^d` -/
  deriv_cont : ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (amp z.1) z.2)
    (Set.univ ×ˢ closedBox d b)

  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  /-- joint continuity of every mixed coordinate derivative on `S × [0,b]^d` -/
  deriv_cont : ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (amp z.1) z.2)
    (Set.univ ×ˢ closedBox d b)

namespace SmoothAmplitudeFamily

variable {S : Type*} [TopologicalSpace S] {b : ℝ} (F : SmoothAmplitudeFamily S d b)

instance : CoeFun (SmoothAmplitudeFamily S d b) fun _ => S → (Fin d → ℝ) → ℝ := ⟨amp⟩


==================== Grammar/SmoothBridgeConsumer.lean

/-!# The grammar-side consumer of a normalised core transport (consult #119, Unit 3)

From hironaka's resolution-bridge output `NormalisedCoreTransport d K prior` — finitely many
charts `ψ_i` on the common box `[−a,a]^d`, analytic on open neighbourhoods `V_i`, with the phase
in exact normalised monomial form `K ∘ ψ_i = c_i ∏ u^{2k_i}`, Jacobian `b_i ∏ u^{h_i}`, smooth
weights `ω_i`, a tail measure with a phase gap and the exact transport
`∑_i (ψ_i)_*(core sources) + tail = vol·prior` — and a smooth compactly supported nonnegative
prior and a smooth observable, we build the `SmoothCoreDecomposition` of the localisation datum
`(vol·prior, K, obs)` on ALL of `ℝ^d`: one smooth core presentation per chart and orthant, with
the CONSTANT phase unit `c_i`, the transport density `ω_i |b_i| prior∘ψ_i` and the amplitude
`ω_i |b_i| prior∘ψ_i obs∘ψ_i`, both extended from `V_i` to globally smooth functio-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} (X : BridgeInputs d)
namespace BridgeInputs
end BridgeInputs
variable {K prior obs : (Fin d → ℝ) → ℝ}
end SmoothEngine
end Grammar

/-- **Bridge inputs**: a normalised core transport of a smooth compactly supported nonnegative
prior, a measurable phase and a smooth observable. -/
structure BridgeInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

structure BridgeInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

  K : (Fin d → ℝ) → ℝ
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

  obs : (Fin d → ℝ) → ℝ
  /-- the normalised core transport of the prior-weighted volume -/
  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

  T : NormalisedCoreTransport d K prior
  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

  K_m : Measurable K
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) := <proof>

  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) := <proof>

  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) := <proof>

  prior_compact : HasCompactSupport prior
  obs_smooth : ContDiff ℝ ∞ obs

variable {d : ℕ} (X : BridgeInputs d)

namespace BridgeInputs

/-! ### The localisation datum -/

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) := <proof>

/-- The prior measure `vol·prior` on all of `ℝ^d`. -/
noncomputable def priorMeasure : Measure (Fin d → ℝ) :=
  volume.withDensity fun y => ENNReal.ofReal (X.prior y)

theorem obs_int : Integrable X.obs X.priorMeasure := <proof>

/-- ★ **The phase is nonnegative a.e. for the prior measure**, from the transport alone: the
monomial on the cores, above the gap on the tail. -/
theorem K_nonneg : ∀ᵐ y ∂X.priorMeasure, 0 ≤ X.K y := <proof>

/-- The localisation datum `(vol·prior, K, obs)`. -/
noncomputable def D : LocalisationData (Fin d → ℝ) where
  μ := X.priorMeasure
  phase := X.K
  obs := X.obs
  phase_measurable := X.K_m
  phase_nonneg := X.K_nonneg
  obs_integrable := X.obs_int
  δ := X.T.δ
  δ_pos := X.T.δ_pos

/-- The local nonnegative density factor `ω · |b| · prior ∘ ψ` of chart `i`, smooth on `V i`. -/
noncomputable def ρloc (i : X.T.ι) (u : Fin d → ℝ) : ℝ :=
  X.T.ω i u * |X.T.jacUnit i u| * X.prior (X.T.ψ i u)

/-- The local amplitude `ω · |b| · prior ∘ ψ · obs ∘ ψ` of chart `i`, smooth on `V i`. -/
noncomputable def Gloc (i : X.T.ι) (u : Fin d → ℝ) : ℝ := X.ρloc i u * X.obs (X.T.ψ i u)

theorem exists_ρf (i : X.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (X.ρloc i) (centeredBox d (X.T.a i)) ∧ ∀ x, 0 ≤ g x := <proof>

/-- The globally smooth nonnegative transport density of chart `i`, equal to `ω · |b| · prior ∘ ψ`
on the box. -/
noncomputable def ρf (i : X.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (X.exists_ρf i)

theorem exists_G (i : X.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (X.Gloc i) (centeredBox d (X.T.a i)) := <proof>

/-- The globally smooth amplitude of chart `i`, equal to `ω · |b| · prior ∘ ψ · obs ∘ ψ` on the
box. -/
noncomputable def G (i : X.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (X.exists_G i)

/-- The active set of chart `i`. -/
def act (i : X.T.ι) : Finset (Fin d) := Finset.univ.filter fun j => 0 < X.T.k i j

/-- The pieces: a chart and an orthant (all orthants are selected). -/
abbrev PIdx : Type := Σ _ : X.T.ι, WaterFilling.CoordSign d

/-- The core measure of a piece: the weighted orthant-box measure pushed along the chart. -/
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (X.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (X.T.h p.1) w * X.ρf p.1 w)).map (X.T.ψ p.1)

/-- The number of active coordinates of a piece. -/
noncomputable def da (p : X.PIdx) : ℕ := Fintype.card {j // inJ (X.act p.1) j}

/-- The enumeration of the active coordinates. -/
noncomputable def eqv (p : X.PIdx) : Fin (X.da p) ≃ {j // inJ (X.act p.1) j} :=
  (Fintype.equivFin _).symm

/-- The reflected inactive coordinates of a base point. -/
def sc (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) : {j // ¬ inJ (X.act p.1) j} → ℝ :=
  fun j => WaterFilling.sgn p.2 j.1 * s.1 j

theorem continuous_sc (p : X.PIdx) : Continuous (X.sc p) := <proof>

/-- The chart coordinate of a piece: reflected active coordinates `v`, reflected inactive
coordinates `s`. -/
noncomputable def Tm (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    Fin d → ℝ :=
  affineMap (X.eqv p) p.2 (X.sc p s) v

/-- The amplitude family of a piece: the pull-back of the extended amplitude along the chart
coordinate. -/
noncomputable def amp (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) (X.T.a p.1)) (X.da p) (X.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2 (X.contDiff_G p.1) (X.T.a p.1)

/-- The active phase exponents of a piece. -/
noncomputable def kA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.T.k p.1 (X.eqv p j).1

/-- The active Jacobian exponents of a piece. -/
noncomputable def hA (p : X.PIdx) (j : Fin (X.da p)) : ℕ := X.T.h p.1 (X.eqv p j).1

theorem kA_pos (p : X.PIdx) (j : Fin (X.da p)) : 0 < X.kA p j := (X.mem_act).1 (X.eqv p j).2

/-- ★★ **The smooth core presentation of a piece**: constant phase unit `c_i`, transport density
`ρf`, amplitude `G`. -/
noncomputable def piecePresentation (p : X.PIdx) :
    SmoothCorePresentation X.D (X.coreMeasure p) (Base (X.act p.1) (X.T.a p.1)) (X.da p) where
  ν := baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)
  h := X.hA p
  k := X.kA p
  k_pos := X.kA_pos p
  b := (X.T.a p.1)
  b_pos := X.T.a_pos p.1
  βf _ := X.T.phaseConst p.1
  β_cont := continuous_const
  β_pos _ := X.T.phaseConst_pos p.1
  Φ z := X.T.ψ p.1 (X.Tm p z.1 z.2)
  measurable_Φ := (X.T.ψ_measurable p.1).comp (X.continuous_Tm p).measurable
  ρ z := X.ρf p.1 (X.Tm p z.1 z.2)
  measurable_ρ := ((X.contDiff_ρf p.1).continuous.comp (X.continuous_Tm p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => X.ρf_nonneg p.1 _
  amp := X.amp p
  amplitude_eq := by
    refine (ae_snd_mem_box' (X.act p.1) (X.T.a p.1)
      (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (X.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change X.G p.1 (X.Tm p z.1 z.2) = X.ρf p.1 (X.Tm p z.1 z.2) * X.obs (X.T.ψ p.1 (X.Tm p z.1 z.2))
    rw [X.G_eq p.1 (X.Tm_mem_box p z.1 hv), X.ρf_eq p.1 (X.Tm_mem_box p z.1 hv)]
    rfl
  phase_normal := by
    refine (ae_snd_mem_box' (X.act p.1) (X.T.a p.1)
      (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (X.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change X.K (X.T.ψ p.1 (X.Tm p z.1 z.2)) = _
    rw [X.T.phase_eq p.1 _ (X.Tm_mem_V p z.1 hv), X.prod_Tm_pow]
    rfl
  transport := by
    have hΦ : (fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) =>
        X.T.ψ p.1 (X.Tm p z.1 z.2)) =
        (X.T.ψ p.1 ∘ WaterFilling.refl p.2) ∘ glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [X.Tm_eq_refl_glueE]
    have hρ : (fun z : Base (X.act p.1) (X.T.a p.1) × (Fin (X.da p) → ℝ) =>
        ((mono (X.hA p) z.2 * X.ρf p.1 (X.Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => X.T.h p.1 (X.eqv p j).1) z.2 *
          X.ρf p.1 (WaterFilling.refl p.2 (glueE' (X.act p.1) (X.T.a p.1) (X.eqv p) z))) := by
      funext z
      rw [X.Tm_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((X.T.ψ_measurable p.1).comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (X.T.ψ_measurable p.1) (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ (X.measurable_ρf p.1), ChartCollar.map_refl_pieceMeasure]
    rfl

/-- The enumeration of the pieces. -/
noncomputable def en : Fin (Fintype.card X.PIdx) ≃ X.PIdx := (Fintype.equivFin _).symm

/-- ★★★ **The smooth core decomposition of the population integral**: one smooth core presentation
per chart and orthant, the transport's tail as the tail. -/
noncomputable def decomp : SmoothCoreDecomposition X.D (Fintype.card X.PIdx)
    (fun I => Base (X.act (X.en I).1) (X.T.a (X.en I).1)) (fun I => X.da (X.en I)) where
  core I := X.coreMeasure (X.en I)
  tail := X.T.tail
  measure_eq := by
    rw [X.D_μ, ← X.sum_coreMeasure]
    congr 1
    exact (Equiv.sum_comp X.en X.coreMeasure).symm
  δ₀ := X.T.δ
  δ₀_pos := X.T.δ_pos
  gap := X.T.tail_gap
  chart I := X.piecePresentation (X.en I)


==================== Grammar/SmoothChartResidueIdentity.lean

/-!# The chart residue measure is the weighted residue measure

Units 4 and 6 of the chart-pushforward identity (consult #135). Tests are integrable against the
face measures (`integrable_faceMeasure_test`), the face measures are finite on compact subsets of
`X` (`faceMeasure_lt_top_of_isCompact`: a cutoff equal to `1` on the compact dominates the
indicator, and the face-density integrand of a test is integrable by the collar), so the chart
residue measure is finite on compacts, locally finite, and REGULAR on the σ-compact metrisable
`X`. Its smooth-test integrals are the residue sums of CDLIII
(`integral_chartResidueMeasure_test`), hence `residueConst · ∫ G dchart = 𝒯^U_{μ,c−1}[G]`
(`residueConst_mul_integral_chartResidueMeasure`). Uniqueness of the stratum measure by smooth
tests (CDLVI) then gives the ★★★ identities
`ν^μ_c = Γ(μ)/(c−1)! · chartResidueMeasure` (`stratumMeasure_eq_smul_cha-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
  (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **THE CHART RESIDUE MEASURE IS THE WEIGHTED RESIDUE MEASURE**: on `X = U ∖ D_{c+1}`,
`ℛ^μ_c` is exactly the finite sum over the pieces of the resolved chart transport and their
simple-pole faces of the pushforwards of the multiplicity-normalised face densities. -/
theorem chartResidueMeasure_eq_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.residueMeasure Y hc hzero := <proof>


==================== Grammar/SmoothChartResidueMeasure.lean

/-!# The chart residue measure: the face densities as a measure on `X = U ∖ D_{c+1}`

Units 2–3 and 5 of the chart-pushforward identity (consult #135). For a piece `p` of the resolved
core transport and a face `J` of its box, the FACE PARAMETER SPACE is `Base_p × ℝ^{Jᶜ}` with the
reference measure `base ⊗ volume|box` (`faceRef`), the F-free FACE DENSITY is
`∏_{j∈J}(2k_j)⁻¹ · ρ(Tm(s, glue J 0 w)) · residueWeight(w)` (`faceDensity`: `ρ = ω·|b|·prior∘ψ`
is the transport density), and the FACE MAP sends `(s, w)` to the divisor point
`divPt p s (glue J 0 w)`
(`faceMap`). The face
measure on `U` is the pushforward of the density measure (`faceMeasureU`),
restricted to `X` along the measurable embedding `X ↪ U` (`faceMeasure`); the CHART RESIDUE
MEASURE is the finite sum over pieces and simple faces (`chartResidueMeasure`). The smooth-test
bridge (`integral_faceMeasure_test`, `integral_chartResidu-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
  (p : (Ξ.X Y).PIdx) (J : Finset (Fin ((Ξ.X Y).da p)))
end ResolvedData
end SmoothEngine
end Grammar

/-- The reference measure `base ⊗ volume|box` on the face parameter space `Base × ℝ^{Jᶜ}`. -/
noncomputable def faceRef :
    Measure (Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) :=
  (Ξ.piecePresentation Y p).ν.prod (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1)))

/-- The multiplicity normalisation `∏_{j∈J} (2k_j)⁻¹` of a face. -/
noncomputable def faceNorm' : ℝ := ∏ j : {i // inJ J i}, (2 * ((Ξ.X Y).kA p j : ℝ))⁻¹

/-- The F-free face density: normalisation × transport density at the face point × residue
weight of the complementary coordinates. -/
noncomputable def faceDensity (μ : ℝ)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ :=
  Ξ.faceNorm' Y p J * (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2)) *
    residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ z.2

/-- The face map: the divisor point of the face point `(s, glue J 0 w)` (through the measurable
chart inverse). -/
noncomputable def faceMap
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : Ξ.R.U :=
  Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 (glue J 0 z.2))

/-- The face measure on `U`: the pushforward of the face density along the face map. -/
noncomputable def faceMeasureU (μ : ℝ) : Measure Ξ.R.U :=
  ((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (Ξ.faceDensity Y p J μ z)).map
    (Ξ.faceMap Y p J)

/-- The face measure on `X = U ∖ D_{c+1}`: the restriction along the embedding `X ↪ U`. -/
noncomputable def faceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  Measure.comap Subtype.val (Ξ.faceMeasureU Y p J μ)

/-- ★★★ **The chart residue measure**: the sum over the pieces of the resolved core transport
and the simple-pole faces of size `c` of the face measures. -/
noncomputable def chartResidueMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c, Ξ.faceMeasure Y ((Ξ.X Y).en I) J μ c


==================== Grammar/SmoothCoordTaylor.lean

/-!# Coordinate Taylor subtraction for smooth amplitudes on a box (consult #114 U1)

The one-coordinate subtraction operators of the smooth-amplitude engine. For a smooth
`G : ℝ^d → ℝ`, the coordinate derivative `pd i G v = d/dt G(v with v_i := t)|_{t = v_i}`
(`pd`, iterated `pdPow`), which commute (`pd_comm`, `pdPow_comm`, from the symmetry of the second
derivative); the coordinate Taylor polynomial of order `p` at `v_i = 0` and its remainder
(`coordTaylor`, `coordRem`, `G = T_i G + R_i G`); the remainder bound along the coordinate line
(★ `coordRem_bound`: `|R_i^{p+1} G (v)| ≤ C v_i^{p+1}/p!` when `|∂_i^{p+1} G| ≤ C` on the line
through `v`), from Mathlib's Taylor theorem; the commutation of the subtraction operators with the
derivatives in the OTHER coordinates (`pdPow_coordRem`); and the iterated remainder over a list
of distinct coordinates (`remList`, ★ `remList_bound`:
`|(∏_{i∈l} R_i-/

-- section/variable skeleton:
open Set Filter Topology
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable (p : Fin d → ℕ)
end SmoothEngine
end Grammar

/-- The iterated coordinate remainder `R_{i₁}^{p_{i₁}} ⋯ R_{iₖ}^{p_{iₖ}} G` over a list of
coordinates. -/
noncomputable def remList : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => coordRem i (p i) (remList l G)


==================== Grammar/SmoothCoreDecomposition.lean

/-!# Smooth core presentations and decompositions (consult #117 §4–§5, U5)

The smooth analogue of `CorePresentation`/`AnalyticCoreDecomposition`: a `SmoothCorePresentation`
transports the weighted box `S × (0,b]^d` (compact base `S`, base measure `ν`) exactly onto a core
measure with a NONNEGATIVE transport density `ρ` (weight × prior × Jacobian unit), an exact
monomial phase with a continuous positive tangential unit `β(s)`, and a smooth amplitude family
equal a.e. to `ρ · obs ∘ Φ` — no tangential datum, no ℓ¹ coefficient family, no fluctuation
field. ★ `integral_eq`: the core integral of `F e^{−NK}` is the family integral of the smooth
engine. A `SmoothCoreDecomposition` is `μ = ∑ cores + tail` with a phase gap on the tail;
★★★ `SmoothCoreDecomposition.cutoffExpansion : CutoffExpansion commonQ commonD D.Z coeff` with
the integrated canonical coefficients summed over the charts (refined t-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff ENNReal NNReal
namespace Grammar
namespace SmoothEngine
attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν
namespace SmoothCorePresentation
variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)
end SmoothCorePresentation
namespace SmoothCoreDecomposition
variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  (A : SmoothCoreDecomposition D M S dim)
variable [∀ I, CompactSpace (S I)] [∀ I, FirstCountableTopology (S I)]
  [∀ I, OpensMeasurableSpace (S I)]
end SmoothCoreDecomposition
end SmoothEngine
end Grammar

/-- The chart measure `ν ⊗ vol|_{(0,b]^d}`. -/
noncomputable def smoothChartMeasure {S : Type*} [MeasurableSpace S] (ν : Measure S) (d : ℕ)
    (b : ℝ) : Measure (S × (Fin d → ℝ)) :=
  ν.prod (volume.restrict (box (Fin d) b))

/-- **A smooth core presentation**: the weighted box `S × (0,b]^d` transported exactly onto
`target`, with nonnegative transport density `ρ`, exact monomial phase with tangential unit
`β(s)`, and a smooth amplitude family equal to `ρ · obs ∘ Φ`. -/
structure SmoothCorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (S : Type*) [TopologicalSpace S] [MeasurableSpace S] (d : ℕ) where
  /-- the base measure -/
  ν : Measure S
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the Jacobian exponents -/
  h : Fin d → ℕ
  /-- the phase exponents, all positive -/
  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

structure SmoothCorePresentation {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (target : Measure U) (S : Type*) [TopologicalSpace S] [MeasurableSpace S] (d : ℕ) where
  /-- the base measure -/
  ν : Measure S
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the Jacobian exponents -/
  h : Fin d → ℕ
  /-- the phase exponents, all positive -/
  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

  ν : Measure S
  [isFiniteMeasure_ν : IsFiniteMeasure ν]
  /-- the Jacobian exponents -/
  h : Fin d → ℕ
  /-- the phase exponents, all positive -/
  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

  h : Fin d → ℕ
  /-- the phase exponents, all positive -/
  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

  k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the box side -/
  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

  b : ℝ
  b_pos : 0 < b
  /-- the tangential phase unit -/
  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

  βf : S → ℝ
  β_cont : Continuous βf
  β_pos : ∀ s, 0 < βf s
  /-- the chart map -/
  Φ : S × (Fin d → ℝ) → U
  measurable_Φ : Measurable Φ
  /-- the nonnegative transport density (weight × prior × Jacobian unit) -/
  ρ : S × (Fin d → ℝ) → ℝ
  measurable_ρ : Measurable ρ
  nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  /-- the smooth amplitude family -/
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b,
    D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z =>
    ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target

attribute [instance] SmoothCorePresentation.isFiniteMeasure_ν

namespace SmoothCorePresentation

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {target : Measure U}
  {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {d : ℕ}
  (C : SmoothCorePresentation D target S d)

theorem measurable_density : Measurable fun z : S × (Fin d → ℝ) => mono C.h z.2 * C.ρ z :=
  ((measurable_mono C.h).comp measurable_snd).mul C.measurable_ρ

/-- **A smooth core decomposition** of a localisation datum: `μ = ∑_I core_I + tail`, every core
carried exactly by a smooth core presentation, and a positive phase gap on the tail. -/
structure SmoothCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (S : Fin M → Type*) [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)]
    (dim : Fin M → ℕ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the smooth core presentations -/
  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)

structure SmoothCoreDecomposition {U : Type*} [MeasurableSpace U] (D : LocalisationData U)
    (M : ℕ) (S : Fin M → Type*) [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)]
    (dim : Fin M → ℕ) where
  /-- the core measures -/
  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the smooth core presentations -/
  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)

  core : Fin M → Measure U
  /-- the tail measure -/
  tail : Measure U
  measure_eq : D.μ = ∑ I, core I + tail
  /-- the phase gap on the tail -/
  δ₀ : ℝ
  δ₀_pos : 0 < δ₀
  gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  /-- the smooth core presentations -/
  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)

namespace SmoothCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  (A : SmoothCoreDecomposition D M S dim)

/-- The common lattice denominator `∏_I 2∏ᵢ k_{I,i}`. -/
def commonQ : ℕ := ∏ I, Qamb (A.chart I).k

  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)

namespace SmoothCoreDecomposition

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {S : Fin M → Type*}
  [∀ I, TopologicalSpace (S I)] [∀ I, MeasurableSpace (S I)] {dim : Fin M → ℕ}
  (A : SmoothCoreDecomposition D M S dim)

/-- The common lattice denominator `∏_I 2∏ᵢ k_{I,i}`. -/
def commonQ : ℕ := ∏ I, Qamb (A.chart I).k

/-- The common lattice denominator `∏_I 2∏ᵢ k_{I,i}`. -/
def commonQ : ℕ := ∏ I, Qamb (A.chart I).k

/-- The common logarithmic degree `max_I (dim I − 1)`. -/
def commonD (_A : SmoothCoreDecomposition D M S dim) : ℕ := Finset.univ.sup fun I => dim I - 1

/-- ★ **The global smooth coefficients**: the sum over the charts of the integrated canonical
coefficients. -/
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ I, familyCoeff (A.chart I).ν (A.chart I).amp (A.chart I).h (A.chart I).k (A.chart I).βf
    (A.chart I).b μ q


==================== Grammar/SmoothFaceMonoTop.lean

/-!# The top face-monomial coefficient

Consult #130, Unit E1b. For a face all of whose coordinates resonate exactly with `μ`
(`2k_iμ = e_i + 1` for every `i`), the face-monomial coefficient at the top logarithmic power
`|ι| − 1` is the explicit positive constant

  `faceMonoCoeff k e β b μ (|ι|−1) = Γ(μ) β^{−μ} / ((|ι|−1)! ∏_i 2k_i)`

(★★ `faceMonoCoeff_top`), independent of the box side `b`. Proof: the two-regime estimate of the
face monomial is a cutoff expansion with coefficients `faceMonoCoeff` (`faceMono_cutoffExpansion`),
all coefficients preceding `(μ, |ι|−1)` vanish (exact resonance, CDXLIV), so the normalised face
monomial converges to the top coefficient (`tendsto_normalised_faceMono`, via
`tendsto_normalised_of_leading`); the face monomial is the cutoff monomial box integral of the
analytic programme (`faceMono_eq_cutoff`), whose equal-ratio asymptotic is explicit
(`monomialBoxR-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset Asymptotics
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
open MonoRep CoeffFamily
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {d : ℕ}
end SmoothEngine
end Grammar

/-- ★★ **The top face-monomial coefficient**: `Γ(μ) β^{−μ} / ((|ι|−1)! ∏ 2k_i)`, independent of the
box side. -/
theorem faceMonoCoeff_top (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b)
    {μ : ℝ} (hμ : ∀ i, 2 * (k i : ℝ) * μ = e i + 1) :
    faceMonoCoeff k e β b μ (Fintype.card ι - 1) =
      Real.Gamma μ * β ^ (-μ) / (((Fintype.card ι - 1).factorial : ℝ) * ∏ i, 2 * (k i : ℝ)) := <proof>


==================== Grammar/SmoothFaceMonomial.lean

/-!# The two-regime estimate for face monomial box integrals (smooth engine, unit 3c)

The inner function of the facewise engine in several variables is the face monomial box integral
`Z_e(t) = ∫_{(0,b]^ι} u^e e^{−β t u^{2k}} du` (`faceMono`). It is continuous in `t`
(`continuous_faceMono`, hence `measurable_faceMono`), nonnegative, and bounded by
`∏ᵢ b^{eᵢ+1}/(eᵢ+1)` for `t ≥ 0` (`faceMono_le`). For `ι = Fin (n+1)` it is the box engine's
`familyPhaseIntegralBox` with `h = 0`, `cξ = 0` and the monomial coefficient family `monoFam e`
(`familyPhaseIntegralBox_monoFam`), so the Taylor tree on the box (`boxTaylorTree_cutoff_bound`)
gives the power–log estimate in the large regime `t b^{2|k|} ≥ 1`; in the small regime both the
integral and the power–log sum are bounded by constants times `t^{−L}(1 + |log t|)^n`. Together
this is the GLOBAL two-regime estimate `|Z_e(t) − powLog(t)| ≤ C t^{−L} (1 -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
namespace SmoothEngine
open CoeffFamily
variable {ι : Type*} [Fintype ι]
end SmoothEngine
end Grammar

/-- The coefficient family of the monomial `u^e`. -/
def monoFam {d : ℕ} (e : Fin d → ℕ) : CoeffFamily d := fun γ => if γ = e then 1 else 0

/-- The reindexing `ι ≃ Fin (|ι| − 1 + 1)` of a nonempty finite index type. -/
noncomputable def faceEquiv (ι : Type*) [Fintype ι] [Nonempty ι] :
    ι ≃ Fin (Fintype.card ι - 1 + 1) :=
  (Fintype.equivFin ι).trans
    (finCongr (Nat.sub_add_cancel (Nat.one_le_of_lt Fintype.card_pos)).symm)

/-- The face monomial power–log coefficients `C_{μ,j}` on a nonempty finite index type, defined
through the box engine after reindexing. -/
noncomputable def faceMonoCoeff [Nonempty ι] (k e : ι → ℕ) (β b : ℝ) (μ : ℝ) (j : ℕ) : ℝ :=
  boxCoeff (Fintype.card ι - 1) 0 (k ∘ (faceEquiv ι).symm) β b 0
    (monoFam (e ∘ (faceEquiv ι).symm)) μ j


==================== Grammar/SmoothFaceOperators.lean

/-!# Face operators of the smooth engine: the subset formula (consult #116 §3.4–3.5)

Over a list `l` of distinct coordinates, the face operator of a Taylor set `J` applies `T_i^{p_i}`
for `i ∈ J` and `R_i^{p_i}` for `i ∉ J` (`faceOp`). Since `T_i + R_i = 1` coordinatewise,
★ `sum_faceOp`: `G = ∑_{J ⊆ l} faceOp J l G` — the SUBSET FORMULA, proved by list induction
(`Finset.sum_powerset_insert`), with no linearity of the operators needed. Taylor operators and
remainders in different coordinates commute (`coordRem_tayList`, `coordTaylor_remList`), so
`faceOp J l G = T_{l∩J} R_{l∖J} G` (`faceOp_eq`), and the iterated Taylor polynomial is the
finite multi-index sum ★ `tayList_eq_sum`:
`T_l G (v) = ∑_{m ∈ idxL l} (∏_i v_i^{m_i}/m_i!) · ∂^m G (v with the `l`-coordinates zeroed)`,
`idxL l = {m : m_i < p_i for i ∈ l, m_i = 0 otherwise}`. Together: the face-`J` term of a smooth
amplitude is a finite-/

-- section/variable skeleton:
open Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} (p : Fin d → ℕ)
end SmoothEngine
end Grammar

/-- `∂^m = ∏_{i ∈ l} ∂_i^{m_i}` over a list. -/
noncomputable def pdMulti (m : Fin d → ℕ) : List (Fin d) → ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | [], G => G
  | i :: l, G => pdPow i (m i) (pdMulti m l G)

/-- The multi-indices of the list: `m_i < p_i` for `i ∈ l`, `m_i = 0` otherwise. -/
def idxL (l : List (Fin d)) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ l then Finset.range (p i) else {0}


==================== Grammar/SmoothFaceSplit.lean

/-!# The face split of the smooth engine (consult #116 §1.2, §3.3)

For a Taylor set `J ⊆ Fin d` with complement `K`, the box `(0,b]^d` splits as
`(0,b]^J × (0,b]^K` (`glue`, `integral_box_split`, Fubini with the `K`-variables outside), and
the face-`J` term of the subset formula integrates to a finite sum of ONE-FLAT-COMPLEMENT face
integrals ★ `faceTerm_integral`:
`∫ (T_J R_K F)(v) v^h e^{−Nβ v^{2k}} dv = ∑_{m ∈ idxL J} (∏_{i∈J} 1/m_i!) ·`
`  ∫_{(0,b]^K} G_{J,m}(w) w^{h_K} · Z^J_{m+h}(N w^{2k_K}) dw`,
with the flat face amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)` (`faceAmp`) and the inner face
monomial integral `Z^J_e(t) = ∫_{(0,b]^J} u^e e^{−βt u^{2k}} du`. The amplitude is flat of
order `p` in the `K`-variables (`faceAmp_bound`, from `remList_bound` and the rectangular
mixed-derivative bound, via permutation invariance of iterated coordinate derivatives
`pdMulti_perm`) — exactly the -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable (p : Fin d → ℕ)
variable (J : Finset (Fin d))
variable (F : (Fin d → ℝ) → ℝ)
variable {F}
end SmoothEngine
end Grammar

/-- The Taylor coordinates of the face, in the standard enumeration. -/
def lJ : List (Fin d) := (List.finRange d).filter (· ∈ J)

/-- The flat coordinates of the face, in the standard enumeration. -/
def lK : List (Fin d) := (List.finRange d).filter (· ∉ J)

/-- Membership in the Taylor set as a plain predicate, so that the subtypes `{i // inJ J i}` and
`{i // ¬ inJ J i}` carry the generic `Subtype.fintype` instance (no `Finset`-specific instance). -/
def inJ (J : Finset (Fin d)) (i : Fin d) : Prop := i ∈ J

instance (J : Finset (Fin d)) : DecidablePred (inJ J) :=
  fun i => inferInstanceAs (Decidable (i ∈ J))

/-- The point of `ℝ^d` with `J`-coordinates `u` and complementary coordinates `w`. -/
def glue (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) : Fin d → ℝ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm (u, w)

/-- The flat face amplitude `G_{J,m}(w) = (R_K^p ∂^m F)(0_J, w)`. -/
noncomputable def faceAmp (m : Fin d → ℕ) (w : {i // ¬ inJ J i} → ℝ) : ℝ :=
  remList p (lK J) (pdMulti m (lJ J) F) (glue J 0 w)


==================== Grammar/SmoothFaceSumCollapse.lean

/-!# The face-sum collapse at the top logarithmic power

Consult #130, Unit E1d. For an amplitude `A` whose jets vanish on the DEEP SET of the closed box
(the points with at least `c + 1` vanishing coordinates, `deepSet`), the engine coefficient at
`(μ, c − 1)` collapses to a sum over the faces `J` of size exactly `c`, each contributing ONE term:
the resonant Taylor order `α_J` (`resOrder`, `α_j = 2k_jμ − h_j − 1` on `J`), the top face
coefficient `faceCoef k β b J (α_J + h) μ (c−1)` (zero unless every coordinate of `J` resonates
exactly, CDXLIV), and the honest face integral of the normal derivative `∂_J^{α_J} A` on the face
`{u_J = 0}` against the power weight `∏_{i∉J} w_i^{h_i} (∏_{i∉J} w_i^{2k_i})^{−μ}` — no logarithmic
factor and no Taylor subtraction (★★★ `smoothCoeff_eq_faceSum_top`). Faces of size `< c` have an
empty top-log range or a pole of order below `c`; faces of size `> c` ha-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
open MonoRep CoeffFamily
variable {d : ℕ}
end SmoothEngine
end Grammar

/-- The deep set: points of the closed box with at least `c + 1` vanishing coordinates. -/
def deepSet (d : ℕ) (b : ℝ) (c : ℕ) : Set (Fin d → ℝ) :=
  {v ∈ closedBox d b | c + 1 ≤ (univ.filter fun i => v i = 0).card}

/-- The resonant Taylor order of a face: `α_j = 2k_jμ − h_j − 1` on `J`, `0` off `J`. -/
noncomputable def resOrder (h k : Fin d → ℕ) (μ : ℝ) (J : Finset (Fin d)) : Fin d → ℕ :=
  fun j => if j ∈ J then ⌊2 * (k j : ℝ) * μ⌋₊ - h j - 1 else 0

/-- ★★★ **The face-sum collapse at the top logarithmic power**: for an amplitude whose jets vanish
on the deep set `{≥ c+1 vanishing coordinates}`, the `(μ, c−1)` coefficient is the sum over the
faces of size `c` of `faceW · faceCoef · ∫_{face} ∂_J^{α_J} A · (power weight)`. -/
theorem smoothCoeff_eq_faceSum_top {A : (Fin d → ℝ) → ℝ} (hA : ContDiff ℝ ∞ A)
    (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) (μ : ℝ) {c : ℕ}
    (hc : 1 ≤ c) (hdeep : JetsZeroOn A (deepSet d b c)) :
    smoothCoeff A h k β b μ (c - 1) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))).filter (fun J => J.card = c),
        faceW J (resOrder h k μ J) *
          (faceCoef k β b J (fun i => resOrder h k μ J i + h i) μ (c - 1) *
            faceCoeffInt (fun w => pdMulti (resOrder h k μ J) (lJ J) A (glue J 0 w))
              (fun i : {i // ¬ inJ J i} => h i) (fun i => 2 * k i) b μ 0) := <proof>


==================== Grammar/SmoothFaceTheorem.lean

/-!# The generic face theorem of the smooth engine (consult #116 §1.3–1.4, second milestone)

An inner function `Z(t)` with a GLOBAL power–log estimate
`|Z(t) − ∑_{μ∈Λ} ∑_{j≤D} c_{μ,j} t^{−μ} (log t)^j| ≤ C t^{−L} (1 + |log t|)^D` for every `t > 0`
is integrated against an outer amplitude `G` on the box `(0,b]^ι` satisfying the product-flat
bound `|G(w)| ≤ M ∏ᵢ wᵢ^{pᵢ}`, with Jacobian exponents `h` and the effective parameter
`t = N ∏ᵢ wᵢ^{aᵢ}`:
`∫ G(w) w^h Z(N w^a) dw = ∑_{μ∈Λ} N^{−μ} ∑_{j≤D} ∑_{q≤j} c_{μ,j} C(j,q) (log N)^q`
`  · ∫ G(w) w^h (w^a)^{−μ} S(w)^{j−q} dw + Rem`,
`|Rem| ≤ C M (1 + log N)^D N^{−L} ∫ ∏ᵢ wᵢ^{pᵢ+hᵢ−aᵢL} (1 + |S(w)|)^D dw`, `S(w) = ∑ᵢ aᵢ log wᵢ`,
under the convergence condition `aᵢ L < pᵢ + hᵢ + 1` (★★ `face_expansion`). The logarithmic degree
is preserved (`(log N + S)^j = ∑_q C(j,q)(log N)^q S^{j−q}`), the remainder is bounded on the
WHOLE box (`1 + |log(N w^a)| ≤ -/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
namespace Grammar
namespace SmoothEngine
variable {ι : Type*} [Fintype ι]
end SmoothEngine
end Grammar

/-- The half-open box `(0,b]^ι`. -/
def box (ι : Type*) (b : ℝ) : Set (ι → ℝ) := Set.pi univ fun _ => Ioc 0 b

/-- The monomial `∏ᵢ wᵢ^{aᵢ}`. -/
def mono (a : ι → ℕ) (w : ι → ℝ) : ℝ := ∏ i, w i ^ a i

/-- The logarithmic sum `S(w) = ∑ᵢ aᵢ log wᵢ`. -/
noncomputable def logSum (a : ι → ℕ) (w : ι → ℝ) : ℝ := ∑ i, (a i : ℝ) * log (w i)

/-- The face coefficient integral `∫_{(0,b]^ι} G(w) w^h (w^a)^{−μ} S(w)^e dw`. -/
noncomputable def faceCoeffInt (G : (ι → ℝ) → ℝ) (h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : ℝ :=
  ∫ w in box ι b, G w * mono h w * mono a w ^ (-μ) * logSum a w ^ e


==================== Grammar/SmoothFamilyIntegral.lean

/-!# Integrating smooth amplitude families over a compact base (consult #117 §2.5, §3.2; U4d–U4e)

★ `cutoffExpansion_integral_of_uniform`: a family of cutoff expansions with constants uniform in
the parameter integrates, against a finite base measure, to a cutoff expansion with the
integrated coefficients (finite-sum/integral interchange and `|∫ E_s| ≤ ν(S) sup |E_s|`). Applied
to a `SmoothAmplitudeFamily` on a compact base this gives ★★ `cutoffExpansion_integral`:
`N ↦ ∫_S ∫_{(0,b]^d} F_s(v) v^h e^{−Nβ v^{2k}} dv dν(s)` is a `CutoffExpansion` on the lattice
`(2∏k)⁻¹ℕ` with degree `≤ d − 1` and coefficients `∫_S smoothCoeff (F_s) dν`, and with a
continuous positive TANGENTIAL PHASE UNIT `β(s)` (★★ `cutoffExpansion_integral_beta`): the unit is
absorbed by rescaling the Laplace parameter, `smoothIntegral F h k β b N = smoothIntegral F h k 1 b
(βN)`, and the coefficients transform by `scaleCo-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} {S : Type*} [TopologicalSpace S] [CompactSpace S] [FirstCountableTopology S]
  [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν] {b : ℝ}
  (F : SmoothAmplitudeFamily S d b)
omit [FirstCountableTopology S] in
variable {h k : Fin d → ℕ}
omit [MeasurableSpace S] [OpensMeasurableSpace S] in
end SmoothEngine
end Grammar

/-- The integrated canonical coefficients. -/
noncomputable def familyCoeff (h k : Fin d → ℕ) (βf : S → ℝ) (b : ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  ∫ s, smoothCoeff (F s) h k (βf s) b μ q ∂ν


==================== Grammar/SmoothGeneral.lean

/-!# The smooth-amplitude expansion: canonical coefficients (consult #116 §2, U3 closure)

The depth-`p` expansions of `SmoothGeneralDepth` are made DEPTH-FREE: for the cutoff `L` the
depth `pᵢ = 2kᵢL − hᵢ` is admissible once `L ≥ L₀ = ∑hᵢ + 1`, the rectangular mixed-derivative
bound exists by compactness (`exists_rect_bound`), and two admissible depths give the same
coefficients below their common cutoff by finite uniqueness (`smoothCoeffAtDepth_eq`). The
canonical coefficient `smoothCoeff F μ q` uses the deterministic cutoff `max(⌊μ⌋+1, L₀)`, and
★★★ `smooth_cutoffExpansion`: the smooth-amplitude integral `∫_{(0,b]^d} F v^h e^{−Nβ v^{2k}} dv`
is a `CutoffExpansion` on the lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and
coefficients `smoothCoeff` — the same interface as the analytic box engine, so the repo's
canonicity theorems (`CutoffExpansion.coeff_unique`) apply: ★★ `-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}
end SmoothEngine
end Grammar

/-- The smooth-amplitude integral as a function of the sample size. -/
noncomputable def smoothIntegral (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b N : ℝ) : ℝ :=
  ∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)

/-- The depth for the cutoff `L`: `pᵢ = 2kᵢL − hᵢ`. -/
def depthOf (h k : Fin d → ℕ) (L : ℕ) : Fin d → ℕ := fun i => 2 * k i * L - h i

/-- The first cutoff at which every depth is positive. -/
def L₀ (h : Fin d → ℕ) : ℕ := (∑ i, h i) + 1

/-- The cutoff used to define the coefficient at the exponent `μ`. -/
noncomputable def cutoffOf (h : Fin d → ℕ) (μ : ℝ) : ℕ := max (⌊μ⌋₊ + 1) (L₀ h)

/-- ★★★ **The canonical smooth coefficients**: the depth-`2kL−h` coefficients at the deterministic
cutoff `L = max(⌊μ⌋₊ + 1, L₀)`. -/
noncomputable def smoothCoeff (F : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (β b : ℝ) (μ : ℝ)
    (q : ℕ) : ℝ :=
  smoothCoeffAtDepth F h k (depthOf h k (cutoffOf h μ)) β b μ q

/-- ★★★ **The smooth-amplitude integral is a cutoff expansion** on the lattice `Q⁻¹ℕ`,
`Q = 2∏kᵢ`, with logarithmic degree `≤ d − 1` and the canonical coefficients `smoothCoeff`:
for every `L > 0` there is `K` with
`|∫_{(0,b]^d} F v^h e^{−Nβ v^{2k}} dv − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} smoothCoeff μ q (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` eventually in `N`. -/
theorem smooth_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β)
    (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) (smoothCoeff F h k β b) := <proof>

/-- ★★ **Canonicity**: any cutoff expansion of the smooth-amplitude integral on the lattice
`Q⁻¹ℕ` with logarithmic degree `≤ d − 1` has the coefficients `smoothCoeff`. -/
theorem smoothCoeff_unique (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    {c : ℝ → ℕ → ℝ} (hc : CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) c) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {j : ℕ} (hj : j ≤ d - 1) :
    c μ j = smoothCoeff F h k β b μ j := <proof>


==================== Grammar/SmoothGeneralDepth.lean

/-!# The smooth expansion in general dimension at a fixed depth (consult #116 U3)

For a smooth amplitude `F` on `[0,b]^d` with the rectangular mixed-derivative bound
`|∂^m F| ≤ M` (`m ≤ p`), Jacobian exponents `h`, phase `Nβ v^{2k}`, a natural cutoff `L` and
depths `pᵢ + hᵢ = 2kᵢL`, the subset formula splits the integral into the face terms
`T_J R_K F`; each is a finite sum of one-flat-complement face integrals (`faceTerm_integral`),
whose inner function is the face monomial integral `Z^J_e` with its global two-regime estimate
(`faceMono_two_regime`; for the empty face `Z^∅(t) = e^{−βt}`, `faceMono_empty_two_regime`) and
whose outer amplitude is the flat face amplitude (`faceAmp_bound`). The generic face theorem
(`face_expansion`) expands each, and `reorganise` collects everything into ONE coefficient system
`smoothCoeffAtDepth` on the ambient lattice `Q⁻¹ℕ`, `Q = 2∏kᵢ`, of logarithmic deg-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
section FaceData
variable (k : Fin d → ℕ) (β b : ℝ) (L : ℕ) (J : Finset (Fin d))
end FaceData
variable {F : (Fin d → ℝ) → ℝ} {h k p : Fin d → ℕ} {β b : ℝ} {L : ℕ}
end SmoothEngine
end Grammar

/-- The ambient lattice denominator `Q = 2 ∏ᵢ kᵢ`. -/
def Qamb : ℕ := 2 * ∏ i, k i

/-- The face logarithmic degree `|J| − 1`. -/
def DJ : ℕ := Fintype.card {i // inJ J i} - 1

theorem nonempty_subtype_inJ {J : Finset (Fin d)} (hJ : J.Nonempty) : Nonempty {i // inJ J i} := <proof>

/-- The face power–log coefficients (zero for the empty face). -/
noncomputable def faceCoef (e : Fin d → ℕ) : ℝ → ℕ → ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceMonoCoeff (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) β b
  else fun _ _ => 0

/-- The weight `∏_{i∈J} 1/m_i!` of a face multi-index. -/
noncomputable def faceW (J : Finset (Fin d)) (m : Fin d → ℕ) : ℝ :=
  ∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹

/-- The index set of the face sums: pairs `(J, m)` with `m ∈ idxL p (lJ J)`. -/
def faceIndex (p : Fin d → ℕ) : Finset (Σ _ : Finset (Fin d), Fin d → ℕ) :=
  (univ : Finset (Finset (Fin d))).sigma fun J => idxL p (lJ J)

/-- ★ **The smooth coefficient system at depth `p`** on the ambient lattice: for each face
`(J, m)`, the binomially reindexed face coefficients times the face coefficient integrals. -/
noncomputable def smoothCoeffAtDepth (F : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (β b : ℝ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1),
    faceCoef k β b x.1 (fun i => x.2 i + h i) μ j * (j.choose q) *
      faceCoeffInt (faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
        (fun i : {i // ¬ inJ x.1 i} => 2 * k i) b μ (j - q)


==================== Grammar/SmoothJetDetermination.lean

/-!# Finite-jet determination of the smooth coefficients (consult #122 U1–U2)

The canonical coefficients of the smooth-amplitude engine depend on the amplitude only through
finitely many coordinate derivatives on the chart-local divisor — the coordinate walls
`walls d = ⋃ᵢ {vᵢ = 0}` of the box. Two amplitudes with equal coordinate jets of orders `α ≤ p`
(`EqJetsOn`) on `walls ∩ [0,b]^d` have the same flat face amplitudes (★ `faceAmp_congr`: the
iterated Taylor remainder `R_K^p ∂^m F (0_J, w)` is a combination of derivatives at points with
`v_J = 0`, `J ≠ ∅`, by `remList_congr`), hence the same depth-`p` coefficient system
(★★ `smoothCoeffAtDepth_congr`; the empty face carries zero coefficients) and the same canonical
coefficients (★★ `smoothCoeff_congr`, with the explicit componentwise order
`depthOf h k (cutoffOf h μ)` and the total order `jetOrder h k μ`). Integrated over a chart base
an-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
open Monomialize.VolumeScaling
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable (p : Fin d → ℕ)
variable {V : Set (Fin d → ℝ)}
open neighbourhood `V` of the box) are determined by the jets of `f`. -/
namespace BridgeInputs
variable (X : BridgeInputs d)
end BridgeInputs
end SmoothEngine
end Grammar

/-- The bridge inputs with the observable replaced (same phase, prior and transport). -/
def withObs (obs' : (Fin d → ℝ) → ℝ) (hobs' : ContDiff ℝ ∞ obs') : BridgeInputs d :=
  { X with obs := obs', obs_smooth := hobs' }


==================== Grammar/SmoothLeadingTerm.lean

/-!# The leading term of a smooth coordinate-free expansion

Consult #127, Unit D8a (abstract half). For a function `Z` with a smooth coordinate-free
expansion `Z(N) ~ ∑ c_{μ,q} N^{−μ} (log N)^q` (`HasSmoothCoordFreeExpansion`) whose
coefficients vanish at every index PRECEDING `(μ₀, q₀)` in the asymptotic order — smaller
exponent, or the same exponent with a higher logarithmic power (`Precedes`) — the normalised
function `N^{μ₀} (log N)^{−q₀} Z(N)` converges to `c_{μ₀,q₀}`
(`tendsto_normalised_of_leading`). This is the analytic input for the positivity of the
leading coefficient functional of the resolved expansion (`SmoothResolvedLeading`).

Non-claims: no existence of a first nonzero index (conditional on the vanishing hypothesis);
the normalisation is stated for `N → ∞` along the reals.-/

-- section/variable skeleton:
open Filter Topology Asymptotics
namespace Grammar
namespace SmoothEngine
end SmoothEngine
end Grammar

/-- The normalised function `N^{μ₀} (log N)^{−q₀} Z(N)`. -/
noncomputable def normalised (μ₀ : ℝ) (q₀ : ℕ) (Z : ℝ → ℝ) (N : ℝ) : ℝ :=
  N ^ μ₀ / Real.log N ^ q₀ * Z N


==================== Grammar/SmoothObservableCoeff.lean

/-!# The observable coefficient functional of the resolution bridge (consult #123, units C0a–C0b, C3)

For fixed bridge inputs `X` (phase `K`, prior, normalised core transport) and a fixed index
`(μ, q)`, the intrinsic coefficient of `N^{−μ} (log N)^q` in the expansion of
`Z_N[f] = ∫ prior · f · e^{−N K}` is a function of the smooth observable `f` alone:

  `observableCoeff X μ q f hf := (X.withObs f hf).decomp.coeff μ q`.

This file establishes the algebraic and geometric facts that make this functional the
*coefficient distribution* of the next unit:

* **linearity** (`observableCoeff_add`, `observableCoeff_smul`, `observableCoeff_zero`), by the
  certificate calculus of `SmoothCoefficientLinearity` and the uniqueness theorem
  `SmoothExpansionCertificate.coeff_eq` — never by unfolding the engine;
* **intrinsicness** (`observableCoeff_eq_of_eq`): two bridge presentations of the same phase-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
open Monomialize.VolumeScaling
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace BridgeInputs
variable (X : BridgeInputs d)
end BridgeInputs
end SmoothEngine
end Grammar

/-- `Z_N[f] = ∫ prior · f · e^{−N K}`. -/
noncomputable def partitionObs (K prior f : (Fin d → ℝ) → ℝ) (N : ℝ) : ℝ :=
  ∫ y, prior y * f y * Real.exp (-N * K y)

/-- ★ **The observable coefficient functional**: the intrinsic coefficient of `N^{−μ}(log N)^q`
in the expansion of `∫ prior · f · e^{−NK}`, as a function of the smooth observable `f`. -/
noncomputable def observableCoeff (μ : ℝ) (q : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ℝ :=
  (X.withObs f hf).decomp.coeff μ q


==================== Grammar/SmoothOneDim.lean

/-!# The one-dimensional smooth expansion (consult #114/#116, first milestone)

For a smooth amplitude `F` on `[0,b]`, a Jacobian exponent `h` and the phase `N β v^{2k}`,
`∫_0^b F(v) v^h e^{−Nβ v^{2k}} dv = ∑_{m<p} F^{(m)}(0)/m! · Γ(λ_m)/(2k β^{λ_m}) · N^{−λ_m}`
`+ O(N^{−L})`,
`λ_m = (m+h+1)/(2k)`, for every natural cutoff `L` and Taylor depth `p` with `2kL ≤ p + h`
(★ `oneDim_smooth`). Ingredients, all reusable in the multivariate engine: the half-line monomial
integral through the fluctuation function (`integral_pow_mul_exp_Ioi`), its exponentially small
tail beyond `b` (`tail_le`), the elementary bound `e^{−x} ≤ max(1, L!) x^{−L}` (`exp_neg_le`),
the fully flat remainder bound (`flat_bound`: no logarithmic loss), and Taylor's theorem along the
line. The coefficients are the exact monomial coefficients of the analytic engine on the line
(compare `OneDim.expansionCoefficient_oneDim` for `k-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology intervalIntegral
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {β : ℝ} (hβ : 0 < β) {k : ℕ} (hk : 0 < k)
include hk in
include hβ hk in
include hβ hk in
omit hβ hk in
include hβ hk in
include hβ hk in
include hβ in
include hβ hk in
end SmoothEngine
end Grammar

/-- The exponent `λ_e = (e+1)/(2k)`. -/
noncomputable def lam (k e : ℕ) : ℝ := ((e : ℝ) + 1) / (2 * k)


==================== Grammar/SmoothResolvedCoefficient.lean

/-!# The resolved coefficient functional: linearity and locality along the zero fibre

Consult #126, Unit D3. The resolved coefficient functional `𝒯^U_{μ,q}[F] = coeff Ξ Y μ q` of
`SmoothResolvedConsumer` is

* **linear** in the smooth observable `F` on the resolved manifold (`coeff_add`, `coeff_smul`,
  `coeff_zero`) — by the linearity of `Z^U_N[F]` and the uniqueness of expansion coefficients;
* **local along the zero fibre** `C₀ = D ∩ π⁻¹(supp prior)` (a compact subset of `U`): if `F`
  vanishes on a neighbourhood of `C₀` then `Z^U_N[F]` is exponentially small (the phase `K ∘ π`
  is bounded below by a positive constant on the compact `π⁻¹(supp prior) ∖ O`), so every
  coefficient vanishes (`coeff_eq_zero_of_eventually_zero`); hence `𝒯^U_{μ,q}[F]` depends only
  on the germ of `F` along `C₀` (`coeff_congr_of_eventuallyEq`) — the support of the resolved
  functional lies in `D ∩ π⁻¹(supp -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The zero fibre over the prior support: `D ∩ π⁻¹(supp prior)`. -/
def zeroFibre : Set Ξ.R.U := Ξ.R.gv ⁻¹' tsupport Ξ.prior ∩ {P | Ξ.K (Ξ.R.gv P) = 0}


==================== Grammar/SmoothResolvedConsumer.lean

/-!# The resolved consumer: the expansion of `Z^U_N[F] = ∫_U F e^{−N K∘π} dμ_U`

Consult #126, Units D2–D3 (first half). The bridge consumer (`SmoothBridgeConsumer`) expands
`∫ prior · f · e^{−NK}` on `ℝ^d` from a normalised core transport. Here the same smooth engine
runs on the RESOLVED manifold `U` of a Watanabe modification `R : WatanabeModificationOn K W`:
the localisation datum is `(μ_U, K ∘ π, F)` with `μ_U = R.resolvedMeasure` the canonical
lift of `prior · vol` (hironaka `ResolvedMeasure`), `π = R.gv` the blow-down and
`F : U → ℝ` a smooth function on the manifold — NOT necessarily a pull-back along `π`. The
pieces are the lifted cores of a resolved core transport `Y` (hironaka
`ResolvedCoreTransport`), presented in the resolution charts `φ i` with amplitude
`ρ · (F ∘ φ_i⁻¹)`; the tail is the lifted tail with the same phase gap.

* `ResolvedData d`: the phase, the modification, the-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The resolved inputs: a phase with a Watanabe modification over `W`, a smooth compactly
supported nonnegative prior inside `W`, and a smooth observable `F` on the resolved manifold. -/
structure ResolvedData (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the open set carrying the modification -/
  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

structure ResolvedData (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the open set carrying the modification -/
  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

  K : (Fin d → ℝ) → ℝ
  /-- the open set carrying the modification -/
  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d := <proof>

  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

/-- The resolved measure `μ_U`. -/
noncomputable def μU : Measure Ξ.R.U := Ξ.R.resolvedMeasure Ξ.hKc Ξ.prior

/-- The pulled-back phase `K ∘ π`. -/
noncomputable def phaseU (P : Ξ.R.U) : ℝ := Ξ.K (Ξ.R.gv P)

theorem measurable_phaseU : Measurable Ξ.phaseU := Ξ.K_m.comp Ξ.R.measurable_gv

theorem F_int : Integrable Ξ.F Ξ.μU := Ξ.integrable_of_continuous Ξ.F_smooth.continuous

/-- The localisation datum `(μ_U, K ∘ π, F)` on the resolved manifold. -/
noncomputable def D : LocalisationData Ξ.R.U where
  μ := Ξ.μU
  phase := Ξ.phaseU
  obs := Ξ.F
  phase_measurable := Ξ.measurable_phaseU
  phase_nonneg := Eventually.of_forall Ξ.phaseU_nonneg
  obs_integrable := Ξ.F_int
  δ := Y.T.δ
  δ_pos := Y.T.δ_pos

/-- The Euclidean bridge input with zero observable: it carries the chart machinery (orthant
boxes, active coordinates, the affine chart coordinate, the extended transport density). -/
abbrev X : BridgeInputs d :=
  ⟨Ξ.K, Ξ.prior, fun _ => 0, Y.T, Ξ.K_m, Ξ.prior_smooth, Ξ.prior_nonneg, Ξ.prior_compact,
    contDiff_const⟩

/-- The local amplitude `ω · |b| · prior ∘ ψ · F ∘ φ⁻¹` of chart `i`, smooth on `V i`. -/
noncomputable def Gloc (i : Y.T.ι) (u : Fin d → ℝ) : ℝ :=
  (Ξ.X Y).ρloc i u * Ξ.F (Y.chartInv i u)

theorem exists_G (i : Y.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (Ξ.Gloc Y i) (centeredBox d (Y.T.a i)) := <proof>

/-- The globally smooth amplitude of chart `i`, equal to `ω · |b| · prior ∘ ψ · F ∘ φ⁻¹` on the
box. -/
noncomputable def G (i : Y.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (Ξ.exists_G Y i)

/-- The lifted core measure of a piece: the weighted orthant-box measure pushed into `U` along
the chart inverse. -/
noncomputable def coreMeasure (p : (Ξ.X Y).PIdx) : Measure Ξ.R.U :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (Y.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (Y.T.h p.1) w * (Ξ.X Y).ρf p.1 w)).map (Y.chartInv p.1)

/-- The amplitude family of a piece: the pull-back of the extended amplitude along the chart
coordinate. -/
noncomputable def amp (p : (Ξ.X Y).PIdx) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine ((Ξ.X Y).continuous_sc p) ((Ξ.X Y).eqv p) p.2 (Ξ.contDiff_G Y p.1)
    (Y.T.a p.1)

/-- ★★ **The smooth core presentation of a lifted piece**: constant phase unit, transport density
`ρf`, amplitude `G`, chart map `φ⁻¹ ∘ Tm` into `U`. -/
noncomputable def piecePresentation (p : (Ξ.X Y).PIdx) :
    SmoothCorePresentation (Ξ.D Y) (Ξ.coreMeasure Y p) (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
      ((Ξ.X Y).da p) where
  ν := baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1)
  h := (Ξ.X Y).hA p
  k := (Ξ.X Y).kA p
  k_pos := (Ξ.X Y).kA_pos p
  b := Y.T.a p.1
  b_pos := Y.T.a_pos p.1
  βf _ := Y.T.phaseConst p.1
  β_cont := continuous_const
  β_pos _ := Y.T.phaseConst_pos p.1
  Φ z := Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_Φ := (Y.measurable_chartInv p.1).comp ((Ξ.X Y).continuous_Tm p).measurable
  ρ z := (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_ρ := (((Ξ.X Y).contDiff_ρf p.1).continuous.comp ((Ξ.X Y).continuous_Tm p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => (Ξ.X Y).ρf_nonneg p.1 _
  amp := Ξ.amp Y p
  amplitude_eq := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change Ξ.G Y p.1 ((Ξ.X Y).Tm p z.1 z.2) =
      (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2) * Ξ.F (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))
    rw [Ξ.G_eq Y p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv), (Ξ.X Y).ρf_eq p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv)]
    rfl
  phase_normal := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    have hbox := (Ξ.X Y).Tm_mem_box p z.1 hv
    change Ξ.K (Ξ.R.gv (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))) = _
    rw [← Y.ψ_eq_gv_chartInv p.1 (Y.box_subset_target p.1 hbox),
      Y.T.phase_eq p.1 _ (Y.T.box_subset_V p.1 hbox)]
    congr 1
    exact (Ξ.X Y).prod_Tm_pow p z.1 z.2
  transport := by
    have hΦ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)) =
        (Y.chartInv p.1 ∘ WaterFilling.refl p.2) ∘
          glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
    have hρ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        ((mono ((Ξ.X Y).hA p) z.2 * (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => Y.T.h p.1 ((Ξ.X Y).eqv p j).1) z.2 *
          (Ξ.X Y).ρf p.1 (WaterFilling.refl p.2
            (glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) z))) := by
      funext z
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((Y.measurable_chartInv p.1).comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (Y.measurable_chartInv p.1) (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ ((Ξ.X Y).measurable_ρf p.1),
      ChartCollar.map_refl_pieceMeasure]
    rfl

/-- ★★★ **The smooth core decomposition of `Z^U_N[F]`**: one smooth core presentation per
resolution chart and orthant, the lifted tail as the tail. -/
noncomputable def decomp : SmoothCoreDecomposition (Ξ.D Y) (Fintype.card (Ξ.X Y).PIdx)
    (fun I => Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1))
    (fun I => (Ξ.X Y).da ((Ξ.X Y).en I)) where
  core I := Ξ.coreMeasure Y ((Ξ.X Y).en I)
  tail := Y.tailU
  measure_eq := by
    rw [Ξ.D_μ, ← Ξ.sum_coreMeasure Y]
    congr 1
    exact (Equiv.sum_comp (Ξ.X Y).en (Ξ.coreMeasure Y)).symm
  δ₀ := Y.T.δ
  δ₀_pos := Y.T.δ_pos
  gap := Y.ae_tailU_gap Ξ.hK0 Ξ.prior_compact Ξ.prior_W
  chart I := Ξ.piecePresentation Y ((Ξ.X Y).en I)

/-- ★ **The resolved coefficient functional** `𝒯^U_{μ,q}[F]`: the coefficient of
`N^{−μ}(log N)^q` in the expansion of `∫_U F e^{−N K∘π} dμ_U`. -/
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ := (Ξ.decomp Y).coeff μ q

/-- ★★ **Intrinsicness in the transport**: the resolved coefficients do not depend on the
resolved core transport. -/
theorem coeff_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) (μ : ℝ) (q : ℕ) :
    Ξ.coeff Y μ q = Ξ.coeff Y' μ q := <proof>

/-- A smooth function on `ℝ^d` pulled back along the blow-down is smooth on `U`. -/
theorem contMDiff_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => f (Ξ.R.gv P)) := <proof>

/-- ★★★ **The resolved functional restricts to Theorem C on pull-backs**: for `F = f ∘ π`, the
resolved coefficient equals the observable coefficient `C_{μ,q}(f)` of the Euclidean bridge
input built from the same transport. -/
theorem coeff_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y μ q =
      (Ξ.X Y).observableCoeff μ q f hf := <proof>


==================== Grammar/SmoothResolvedRLCTAsymptotic.lean

/-!# The RLCT asymptotic of the partition function at a positive realiser

Consult #129 packaging unit: the paper-facing statement of Theorem D in one theorem. At a point
`P₀` of the zero fibre realising the extremal data `(λ*, m*)` (CDXXXIX) where the prior is
positive (★★★ `rlct_asymptotic_of_realised`):

* every coefficient of every observable preceding `(λ*, m*−1)` vanishes,
* `N^{λ*}(log N)^{−(m*−1)} Z^U_N[G] → 𝒯^U_{λ*,m*−1}[G]` for every smooth observable `G`,
* `c := 𝒯^U_{λ*,m*−1}[1] > 0`, and
* the Euclidean partition function satisfies `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`
  (`Asymptotics.IsEquivalent`), with `λ* > 0`.

The automatic-existence form (`exists_rlct_asymptotic`): for a nonempty zero fibre and a prior
positive on the zero set of the phase inside its support, there are `λ* > 0`, `m* ≥ 1` and
`c > 0` with `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`, where `(λ*, -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
include Y in
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **The RLCT asymptotic without a leading-index hypothesis**: for a nonempty zero fibre and
a prior positive on the zero set of the phase inside its support, there are `λ* > 0`, `m* ≥ 1`
extremal for the wall data and `c > 0` with `∫ prior · e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}`. -/
theorem exists_rlct_asymptotic (hne : Ξ.zeroFibre.Nonempty)
    (hpos : ∀ y ∈ tsupport Ξ.prior, Ξ.K y = 0 → 0 < Ξ.prior y) :
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 1 ≤ m ∧ Ξ.IsExtremalData lam m ∧
      ∃ c : ℝ, 0 < c ∧ (fun N => partitionObs Ξ.K Ξ.prior (fun _ => (1 : ℝ)) N) ~[atTop]
        fun N => c * (N ^ (-lam) * Real.log N ^ (m - 1)) := <proof>


==================== Grammar/SmoothResolvedRLCTIndex.lean

/-!# The resolved expansion starts at the extremal pair of the zero fibre

Consult #128 follow-up (5), first half. Read the intrinsic wall data of Theorem D on the zero
fibre `Z₀ = π⁻¹(supp prior) ∩ {K ∘ π = 0}`: a pair `(λ*, m*)` is **extremal data** for the
resolved inputs (`IsExtremalData`) when every wall `(k, h)` through a point of `Z₀` has ratio
`(h+1)/(2k) ≥ λ*` and at most `m*` walls through any point of `Z₀` resonate with `λ*`. Then for
every index `(ν, p)` preceding `(λ*, m* − 1)` the resonant support set `Z₀ ∩ {r_ν ≥ p+1}` is
EMPTY (`resonantZeroFibre_eq_empty_of_precedes`: a wall resonating with `ν < λ*` would have
`2kν ≥ h+1 ≥ 2kλ*`, and at `ν = λ*` the count is at most `m* ≤ p`), so by the resonant support
theorem (CDXXXV) the coefficient `𝒯^U_{ν,p}[F]` vanishes for EVERY observable
(`coeff_eq_zero_of_precedes`): `(λ*, m* − 1)` is a leading index in the sense of CDXXXII
(`isLe-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
open Classical in
variable {lam : ℝ} {m : ℕ}
open Classical in
end ResolvedData
end SmoothEngine
end Grammar

/-- **Extremal data** `(λ*, m*)` of the zero fibre: every wall through a point of `Z₀` has
ratio `(h+1)/(2k) ≥ λ*`, and at most `m*` walls through any point of `Z₀` resonate with `λ*`. -/
def IsExtremalData (lam : ℝ) (m : ℕ) : Prop :=
  (∀ P ∈ Ξ.zeroFibre, ∀ p ∈ pairs Ξ.R Ξ.hK0 P, 2 * (p.1 : ℝ) * lam ≤ (p.2 : ℝ) + 1) ∧
    ∀ P ∈ Ξ.zeroFibre, resonanceCount Ξ.R Ξ.hK0 lam P ≤ m


==================== Grammar/SmoothResolvedResidue.lean

/-!# The graded stratum formula as a residue sum

The twisted prior density `(K∘π)^{−μ} μ_U` behaves along a wall `(k, h)` like `u^{h − 2kμ}`:
its POLE ORDER is `poleOrder k h μ = 2kμ − h`. A wall resonates with `μ` exactly when this pole
order is a positive integer (`resonates_iff_poleOrder`), the exact resonance count of CDXLIV counts
the SIMPLE poles (`exactCount_eq_card_simplePole`), and the resonant Taylor order is the pole order
minus one. On a face all of whose walls carry simple poles the face term of the stratum formula
(CDXLVI) is the residue term
`Γ(μ) β^{−μ}/(c−1)! · (∏_{j∈J} (2k_j)^{−1}) ∫_{face} A(0_J, w) · residueWeight(w) dw`
(★★ `faceTerm_eq_residue_of_simple`): the weight `∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−μ}` is the
coordinate expression of the iterated Poincaré residue of the twisted density along the face, and
the factors `(2k_j)^{−1}` normalise the residue agains-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The residue weight on a face: `∏_{i∉J} w_i^{h_i} (∏_{i∉J} w_i^{2k_i})^{−μ}`, the coordinate
expression of the iterated Poincaré residue of the twisted density along the face. -/
noncomputable def residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) (w : ι → ℝ) : ℝ :=
  mono h w * mono (fun i => 2 * k i) w ^ (-μ)

/-- The residue constant `Γ(μ)/(c−1)!`. -/
noncomputable def residueConst (μ : ℝ) (c : ℕ) : ℝ := Real.Gamma μ / ((c - 1).factorial : ℝ)

/-- The simple-pole faces of size `c` of a piece box. -/
noncomputable def simpleFaces (p : (Ξ.X Y).PIdx) (μ : ℝ) (c : ℕ) :
    Finset (Finset (Fin ((Ξ.X Y).da p))) :=
  (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter fun J =>
    J.card = c ∧ ∀ j ∈ J, 2 * ((Ξ.X Y).kA p j : ℝ) * μ = (Ξ.X Y).hA p j + 1


==================== Grammar/SmoothResolvedResonant.lean

/-!# Resonant faces of the resolved decomposition: the chart amplitudes vanish there

Consult #127, Unit D6b (geometric half). Fix resolved data `Ξ` and a resolved core transport `Y`.
The resolved expansion is assembled from the pieces `p` (a resolution chart and an orthant): the
engine expands the chart amplitude `G_p(T_p(s, v))` (`ρ · F ∘ φ_p⁻¹` extended smoothly off the
box) in the active coordinates `v ∈ [0, a]^{d_p}`. A **face** `J` of the active box is the
coordinate subspace `{v_i = 0 : i ∈ J}`; its points are carried by the chart to the divisor
points `Q = φ_p⁻¹(T_p(s, v))` whose intrinsic pair data contain the pairs `(k_i, h_i)`, `i ∈ J`
(the local coordinate formula of CDXXXI in the even chart box of the piece). Hence:

* `resonanceCount_ge_face`: the resonance count of such a `Q` is at least the number of
  resonant coordinates of the face;
* if the observable `F` vanishes on a n-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
open Classical in
open Classical in
end ResolvedData
end SmoothEngine
end Grammar

/-- The resonant zero fibre `Z₀ ∩ {r_μ ≥ q + 1}`. -/
def resonantZeroFibre (μ : ℝ) (q : ℕ) : Set Ξ.R.U :=
  Ξ.zeroFibre ∩ resonanceGE Ξ.R Ξ.hK0 μ (q + 1)

/-- The chart point of a piece face point. -/
noncomputable def facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Fin d → ℝ := (Ξ.X Y).Tm p s v

/-- The divisor point of a piece face point. -/
noncomputable def divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Ξ.R.U := (Y.φ p.1).symm (Ξ.facePt Y p s v)


==================== Grammar/SmoothResolvedResonantSupport.lean

/-!# The resonant support of the resolved coefficient functionals

Consult #127, Unit D6 (assembly). The resolved coefficient functional `𝒯^U_{μ,q}` vanishes on
every smooth observable that vanishes on a neighbourhood of the **resonant zero fibre**
`Z₀ ∩ {r_μ ≥ q + 1}` — the divisor points over the prior support at which at least `q + 1` of
the walls resonate with the exponent `μ` (`coeff_eq_zero_of_eventually_zero_resonant`). Hence
`𝒯^U_{μ,q}` depends only on the germ of the observable along `Z₀ ∩ {r_μ ≥ q+1}`
(`coeff_congr_of_eventuallyEq_resonant`), a fortiori along `Z₀ ∩ D_{≥ q+1}`
(`coeff_eq_zero_of_eventually_zero_depth`), and an observable supported in the shallow locus
`U_c = U ∖ D_{≥ c+1}` has vanishing coefficients at all logarithmic powers `q ≥ c`
(`coeff_eq_zero_of_tsupport_subset_shallowOpen`): the logarithmic power `q` requires `q + 1`
resonant walls through a point of the sup-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **Resonant support of the resolved coefficient functional**: an observable vanishing on a
neighbourhood of the resonant zero fibre `Z₀ ∩ {r_μ ≥ q + 1}` has vanishing `(μ, q)` coefficient. -/
theorem coeff_eq_zero_of_eventually_zero_resonant {μ : ℝ} {q : ℕ}
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) : Ξ.coeff Y μ q = 0 := <proof>


==================== Grammar/SmoothResolvedStratumExtremal.lean

/-!# The zero-order condition at the extremal exponent

Consult #131, optional corollary (1). At the extremal exponent `λ*` of Theorem D
(`IsExtremalData λ* m*`: every wall through the zero fibre has `2kλ* ≤ h + 1`), a wall
resonating with `λ*` has `2kλ* = h + 1 + n ≥ h + 1 ≥ 2kλ*`, so `n = 0`: the zero-order condition
of Theorem E holds on every exact stratum `S^{λ*}_c` (★★ `zeroOrder_of_extremalData`). Hence the
leading functional `𝒯^U_{λ*,c−1}`, restricted to observables vanishing near the zero fibre of
depth `≥ c+1`, is nonnegative on nonnegative observables and depends only on their values on
`S^{λ*}_c` (`coeff_nonneg_of_deep_extremal`, `coeff_eq_of_eqOn_exactStratum_extremal`). This links
Theorem E to Theorem D's leading functional without a global-minimum hypothesis on Theorem E
itself. Non-claims: the restriction to observables vanishing near the deeper fibre is not
vacuous (`m*` bo-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
open Classical in
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★ **The zero-order condition holds at the extremal exponent** on every exact stratum. -/
theorem zeroOrder_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (c : ℕ) :
    Ξ.ZeroOrder lam c := <proof>


==================== Grammar/SmoothResolvedStratumFormula.lean

/-!# The graded stratum formula on the resolved manifold

Consult #130, Unit E2. Let `D_{c+1} = Z₀ ∩ {depth ≥ c+1}` be the DEEP ZERO FIBRE
(`deepZeroFibre`, compact). For an observable `F` vanishing on a neighbourhood of `D_{c+1}`
(the class `𝓘_{c+1}`), the resolved coefficient at the top logarithmic power `(μ, c − 1)` is the
STRATUM SUM (★★★ `coeff_eq_stratumSum`): over the pieces of the resolved core transport and the
base points, the sum over the faces `J` of size `c` of the piece box of
`faceW · faceCoef · ∫_{face} ∂_J^{α_J}(amplitude) · (power weight)` (`pieceStratumSum`,
`stratumSum`) — the engine collapse (CDXLVI) applied piecewise, since the amplitude jets vanish on
the deep set of every piece box (`jetsZeroOn_amp_deep`: near a face point with `≥ c+1` vanishing
coordinates the divisor point has depth `≥ c+1`, so either `F` vanishes near it or it lies off the
prior support). The geom-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
open Classical in
end ResolvedData
end SmoothEngine
end Grammar

/-- The deep zero fibre `D_{c+1} = Z₀ ∩ {depth ≥ c + 1}`. -/
def deepZeroFibre (c : ℕ) : Set Ξ.R.U := Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (c + 1)

/-- Observables vanishing near the deep zero fibre have no coefficients of log power `≥ c`. -/
theorem coeff_eq_zero_of_deep {c : ℕ} (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) {q : ℕ}
    (hq : c ≤ q) (μ : ℝ) : Ξ.coeff Y μ q = 0 := <proof>

/-- The stratum term of a piece at a base point: the sum over the faces of size `c` of the piece
box of `faceW · faceCoef · ∫_{face} ∂_J^{α_J}(amplitude) · (power weight)`. -/
noncomputable def pieceStratumSum (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin ((Ξ.X Y).da ((Ξ.X Y).en I))))).filter (fun J => J.card = c),
    faceW J (resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k μ J) *
      (faceCoef ((Ξ.decomp Y).chart I).k (((Ξ.decomp Y).chart I).βf s) ((Ξ.decomp Y).chart I).b J
          (fun i => resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k μ J i +
            ((Ξ.decomp Y).chart I).h i) μ (c - 1) *
        faceCoeffInt (fun w => pdMulti (resOrder ((Ξ.decomp Y).chart I).h ((Ξ.decomp Y).chart I).k
            μ J) (lJ J) (((Ξ.decomp Y).chart I).amp.amp s) (glue J 0 w))
          (fun i : {i // ¬ inJ J i} => ((Ξ.decomp Y).chart I).h i)
          (fun i => 2 * ((Ξ.decomp Y).chart I).k i) ((Ξ.decomp Y).chart I).b μ 0)

/-- The stratum sum: the piece stratum terms integrated over the bases and summed over the
pieces. -/
noncomputable def stratumSum (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ I, ∫ s, Ξ.pieceStratumSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν

/-- ★★★ **The graded stratum formula**: for an observable vanishing near the deep zero fibre
`Z₀ ∩ {depth ≥ c+1}`, the coefficient at `(μ, c − 1)` is the stratum sum. -/
theorem coeff_eq_stratumSum {c : ℕ} (hc : 1 ≤ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) (μ : ℝ) :
    Ξ.coeff Y μ (c - 1) = Ξ.stratumSum Y μ c := <proof>


==================== Grammar/SmoothResolvedStratumPositive.lean

/-!# Positivity and values-only dependence of the graded stratum functional

Consult #130, Unit E3. On the EXACT STRATUM `S^μ_c = Z₀ ∩ {depth = c} ∩ {r_μ = c}`
(`exactStratum`) assume the ZERO-ORDER condition (`ZeroOrder`): every wall through a point of
`S^μ_c` has ratio exactly `μ`, `2kμ = h + 1`. Then for observables `F` vanishing near the deep
zero fibre `Z₀ ∩ {depth ≥ c+1}`:

* every face contributing to the stratum sum has resonant Taylor order `α_J = 0`, or its face
  point lies off the prior support and all amplitude jets vanish there (`stratum_or_jets_zero`:
  a face point with exactly the `J`-coordinates zero is a divisor point of the exact stratum,
  CDXLVIII, so the zero-order condition forces `α_J = 0`);
* hence `𝒯^U_{μ,c−1}[F] ≥ 0` for `F ≥ 0` (★★★ `coeff_nonneg_of_deep`: the face integrands are
  `amplitude · (positive power weight)` with `amplitude = ω|b|·prior∘π·F ≥ 0`, and -/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The exact stratum `S^μ_c = Z₀ ∩ {depth = c} ∩ {r_μ = c}`. -/
def exactStratum (μ : ℝ) (c : ℕ) : Set Ξ.R.U :=
  {P | P ∈ Ξ.zeroFibre ∧ depth Ξ.R Ξ.hK0 P = c ∧ resonanceCount Ξ.R Ξ.hK0 μ P = c}

/-- **The zero-order condition**: every wall through a point of the exact stratum has ratio
exactly `μ`. -/
def ZeroOrder (μ : ℝ) (c : ℕ) : Prop :=
  ∀ P ∈ Ξ.exactStratum μ c, ∀ q ∈ pairs Ξ.R Ξ.hK0 P, 2 * (q.1 : ℝ) * μ = q.2 + 1


==================== Grammar/SmoothResonantSupport.lean

/-!# Resonant support of the smooth expansion coefficients

Consult #127, Unit D6a. The smooth engine expands `∫_{(0,b]^d} F(v) v^h e^{−Nβ v^{2k}} dv` for a
smooth amplitude `F` as `∑_{μ,q} c_{μ,q} N^{−μ} (log N)^q`, with the coefficient system
`smoothCoeff F h k β b μ q` (`SmoothGeneral`, `SmoothGeneralDepth`). Each coefficient is a finite
sum over FACES `J ⊆ {1,…,d}` and Taylor multi-indices `m` supported on `J` of products

  `faceCoef k β b J (m + h) μ j · C(j, q) · ∫_{(0,b]^{Jᶜ}} G_{J,m}(w) w^h (w^{2k})^{−μ} S(w)^{j−q}`

where `faceCoef` collects the power–log coefficients of the monomial face integral
`∫_{(0,b]^J} ∏_{i∈J} u_i^{m_i+h_i} e^{−Nβ ∏_{i∈J} u_i^{2k_i}}` and `G_{J,m} = faceAmp p J F m` is
the `m`-th normal derivative of `F` along the face `{v_i = 0 : i ∈ J}`, with the complementary
Taylor remainders, evaluated at the face point with complementary coordinates `w`.

## Resonanc-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
open MonoRep CoeffFamily
open Classical in
variable {d : ℕ}
end SmoothEngine
end Grammar

/-- All coordinate jets of `G` vanish on `S`. -/
def JetsZeroOn (G : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) : Prop :=
  ∀ α : Fin d → ℕ, ∀ v ∈ S, pdMulti α (List.finRange d) G v = 0


==================== Grammar/SmoothSheetTransport.lean

/-!# Transport of a chart piece onto the smooth chart measure (consult #117 §7, U6b transport)

For a chart with active set `J` (enumerated by `e : Fin da ≃ J`), the positive box `[0,a]^d`
splits as the compact INACTIVE base `Base J a = [0,a]^{J^c}` times the active box `(0,a]^{da}`
(`glueE`), a measurable embedding carrying Lebesgue measure to Lebesgue measure
(`map_glueE_prod`), and the piece measure `(vol|_{[0,a]^d})·|w|^h ϕ(refl σ w)` is the transport of
the smooth chart measure `(vol_{base}·s^{h_{J^c}}) ⊗ (vol|_{(0,a]^{da}})` with density
`v^{h_J} · ϕ(refl σ (glue s v))` (★ `map_glueE_pieceMeasure`) — the shape of the `transport` field
of a `SmoothCorePresentation`. Also `MeasurableEmbedding.map_withDensity_comp`: densities transport
along measurable embeddings. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace Grammar
namespace SmoothEngine
variable {d : ℕ} (J : Finset (Fin d)) (a : ℝ)
variable {da : ℕ} (e : Fin da ≃ {i // inJ J i})
end SmoothEngine
end Grammar

/-- The closed inactive box `[0,a]^{J^c}`. -/
def baseBox : Set ({i // ¬ inJ J i} → ℝ) := Set.pi univ fun _ => Icc 0 a

/-- The base of a chart piece: the closed inactive box as a compact type. -/
abbrev Base : Type := ↥(baseBox J a)

/-- Lebesgue measure on the base. -/
noncomputable def baseVol : Measure (Base J a) :=
  Measure.comap (Subtype.val : Base J a → {i // ¬ inJ J i} → ℝ) volume

/-- The inactive Jacobian weight `∏_{j ∉ J} s_j^{h_j}` on the base. -/
noncomputable def baseWeight (h : Fin d → ℕ) (s : Base J a) : ℝ :=
  ∏ j : {i // ¬ inJ J i}, s.1 j ^ h j.1

/-- The base measure of a chart piece: Lebesgue measure with the inactive Jacobian weight. -/
noncomputable def baseMeasure (h : Fin d → ℕ) : Measure (Base J a) :=
  (baseVol J a).withDensity fun s => ENNReal.ofReal (baseWeight J a h s)


==================== Grammar/SmoothStratumApprox.lean

/-!# Extension of the stratum test functional to compactly supported continuous functions

Residue programme (consult #132), units 2–3. A compactly supported continuous function on
`X = U ∖ D_{c+1}` extends by zero to a compactly supported continuous function on `U`
(`ext`, `continuous_ext`, `hasCompactSupport_ext`), and is uniformly approximated by smooth test
functions with supports in ONE fixed compact `L ⊆ X` (`exists_approx`: a smooth uniform
approximant from the convex local-to-global gluing theorem, multiplied by a cutoff equal to `1`
on the support). The values `T[G_n]` along such an approximating sequence converge, by the local
bound `|T[G] − T[G']| ≤ ‖G − G'‖_∞ · T[χ_L]`, and the limit does not depend on the sequence
(`tendsto_T_of_approx`). The resulting functional `Λ` on `C_c(X, ℝ)` is linear and positive
(`Λ`, a `PositiveLinearMap`), and agrees with `T` on smooth test functions-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold CompactlySupported
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
open Classical in
end ResolvedData
end SmoothEngine
end Grammar

/-- Extension by zero of a function on `X = U ∖ D_{c+1}` to `U`. -/
noncomputable def ext (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.R.U → ℝ := fun P =>
  if h : P ∈ Ξ.stratumOpen c then f ⟨P, h⟩ else 0

/-- ★ **Uniform approximation by smooth tests with a common compact support**: for every
`f ∈ C_c(X, ℝ)` there is a compact `L ⊆ X` such that for every `ε > 0` some smooth test function
supported in `L` is uniformly `ε`-close to the extension by zero of `f`. -/
theorem exists_approx (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) :
    ∃ L : Set Ξ.R.U, IsCompact L ∧ L ⊆ Ξ.stratumOpen c ∧ ∀ ε > 0, ∃ G : Ξ.R.U → ℝ,
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ Ξ.IsTest c G ∧ tsupport G ⊆ L ∧
        ∀ P, |G P - Ξ.ext c f P| ≤ ε := <proof>

/-- The common support compact of the chosen approximants. -/
noncomputable def approxL (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : Set Ξ.R.U :=
  Classical.choose (Ξ.exists_approx c f)

/-- The `n`-th chosen approximant, uniformly `1/(n+1)`-close to the extension of `f`. -/
noncomputable def approx (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (n : ℕ) : Ξ.R.U → ℝ :=
  Classical.choose ((Ξ.approxL_spec c f).2.2 (1 / ((n : ℝ) + 1)) (one_div_succ_pos n))

theorem approx_smooth (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) (n : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (Ξ.approx c f n) := (Ξ.approx_spec c f n).1

/-- The limit of `T` along the chosen approximating sequence. -/
noncomputable def Λ₀ (μ : ℝ) (c : ℕ) (f : C_c(Ξ.stratumOpen c, ℝ)) : ℝ :=
  limUnder atTop fun n => Ξ.T Y μ c (Ξ.approx c f n) (Ξ.approx_smooth c f n)

theorem Λ₀_add {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (f g : C_c(Ξ.stratumOpen c, ℝ)) : Ξ.Λ₀ Y μ c (f + g) = Ξ.Λ₀ Y μ c f + Ξ.Λ₀ Y μ c g := <proof>

/-- ★★ **The positive linear functional on `C_c(X, ℝ)`** extending the stratum test functional. -/
noncomputable def Λ {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    C_c(Ξ.stratumOpen c, ℝ) →ₚ[ℝ] ℝ where
  toFun := Ξ.Λ₀ Y μ c
  map_add' := Ξ.Λ₀_add Y hc hzero
  map_smul' := fun r f => by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact Ξ.Λ₀_smul Y hc hzero r f
  monotone' := fun f g hfg => by
    have h := Ξ.Λ₀_nonneg Y hc hzero (g + (-1 : ℝ) • f) fun x => by
      have := CompactlySupportedContinuousMap.le_def.1 hfg x
      simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    rw [Ξ.Λ₀_add Y hc hzero, Ξ.Λ₀_smul Y hc hzero] at h
    change Ξ.Λ₀ Y μ c f ≤ Ξ.Λ₀ Y μ c g
    linarith


==================== Grammar/SmoothStratumJetDependence.lean

/-!# Jet dependence of the stratum coefficients (chart-free)

The `(μ, c−1)` coefficient of an observable `F` vanishing near the deep zero fibre depends on `F`
only through a finite transverse jet along the exact stratum `S^μ_c`, and the order of that jet
is intrinsic. Both halves of the statement are chart-free:

* `VanishesToOrderAt n H P`: near `P`, `H` is a finite sum of smooth multiples of products of `n`
  smooth functions each vanishing at `P` (equivalently, the `(n−1)`-jet of `H` at `P` is zero);
  `MemIdealPowNear S n H P` is the ideal-theoretic form `H ∈ 𝓘_S^n` near `P` (the factors vanish
  on `S`). Exponent `0` imposes nothing.
* `stratumJetOrder μ P = Σ_{(k,h)} (⌊2kμ⌋₊ − h − 1)` over the intrinsic wall pairs through `P`;
  at a point of the exact stratum it is the total resonant Taylor order `|α|` of the face formula
  (`stratumJetOrder_divPt_eq`), and it vanishes under the zer-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
variable {Ξ} in
variable {Ξ} in
end ResolvedData
end SmoothEngine
end Grammar

/-- **`H ∈ 𝓘_S^n` near `P`**: near `P`, `H` is a finite sum of smooth multiples of products of `n`
smooth functions each vanishing on `S`. For `n = 0` every smooth `H` qualifies. -/
def MemIdealPowNear (S : Set Ξ.R.U) (n : ℕ) (H : Ξ.R.U → ℝ) (P : Ξ.R.U) : Prop :=
  ∃ N ∈ 𝓝 P, ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ξ.R.U → ℝ) (g : ι → Fin n → Ξ.R.U → ℝ),
    (∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (a i)) ∧
    (∀ i l, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (g i l)) ∧ (∀ i l, ∀ Q ∈ S, g i l Q = 0) ∧
    ∀ Q ∈ N, H Q = ∑ i, a i Q * ∏ l, g i l Q

/-- The intrinsic transverse jet order at `P`: `Σ_{(k,h)} (⌊2kμ⌋₊ − h − 1)` over the wall pairs
through `P`. At a point of the exact stratum this is the total resonant Taylor order `|α|`. -/
noncomputable def stratumJetOrder (μ : ℝ) (P : Ξ.R.U) : ℕ :=
  ((pairs Ξ.R Ξ.hK0 P).map fun q => ⌊2 * (q.1 : ℝ) * μ⌋₊ - q.2 - 1).sum

/-- ★★★ **Ideal-power form**: if `G − G' ∈ 𝓘_{S^μ_c}^{stratumJetOrder μ P + 1}` near every point
`P` of the exact stratum, the two `(μ, c−1)` coefficients agree. -/
theorem coeff_eq_of_memIdealPow {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) {G G' : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG' : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G')
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0)
    (hG0' : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G' P = 0)
    (hjet : ∀ P ∈ Ξ.exactStratum μ c, Ξ.MemIdealPowNear (Ξ.exactStratum μ c)
      (Ξ.stratumJetOrder μ P + 1) (fun P => G P - G' P) P) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = (Ξ.withF G' hG').coeff Y μ (c - 1) := <proof>


==================== Grammar/SmoothStratumJetDescent.lean

/-!# Descent of the stratum coefficient to the transverse-jet quotient

The jet-dependence theorem of `SmoothStratumJetDependence` is packaged as a descent: the
admissible observables of depth `c` (smooth, vanishing near `D_{c+1}`) form a submodule
`admissible c` of `U → ℝ`; the observables lying in `𝓘_{S^μ_c}^{n(P)+1}` near every point `P` of the
exact stratum form a submodule `jetKernel μ c` (the ideal-power condition is closed under sums and
smooth multiples); the coefficient `G ↦ 𝒯^U_{μ,c−1}[G]` is a linear functional `coeffLin` on
`admissible c` that kills `admissible c ∩ jetKernel μ c` (`coeffLin_eq_zero_of_mem_jetKernel`), so
it descends to a linear functional `descendedCoeff` on the transverse-jet quotient
`admissible c ⧸ (admissible c ∩ jetKernel μ c)` with `descendedCoeff (mk G) = 𝒯^U_{μ,c−1}[G]`
(`descendedCoeff_mk`). No zero-order hypothesis; under it the kernel contains every a-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
variable {Ξ} in
variable {Ξ} in
end ResolvedData
end SmoothEngine
end Grammar

/-- The admissible observables of depth `c`: smooth and vanishing near the deep zero fibre
`D_{c+1}`. -/
def admissible (c : ℕ) : Submodule ℝ (Ξ.R.U → ℝ) where
  carrier := {G | ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G ∧ ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0}
  add_mem' {G G'} hG hG' := ⟨hG.1.add hG'.1, by
    filter_upwards [hG.2, hG'.2] with P h1 h2
    rw [Pi.add_apply, h1, h2, add_zero]⟩
  zero_mem' := ⟨contMDiff_const, Eventually.of_forall fun _ => rfl⟩
  smul_mem' r {G} hG := ⟨contMDiff_const.mul hG.1, by
    filter_upwards [hG.2] with P h1
    rw [Pi.smul_apply, h1, smul_zero]⟩

/-- The transverse-jet kernel: observables lying in `𝓘_{S^μ_c}^{n(P)+1}` near every point `P` of
the exact stratum, `n(P) = stratumJetOrder μ P`. -/
def jetKernel (μ : ℝ) (c : ℕ) : Submodule ℝ (Ξ.R.U → ℝ) where
  carrier := {H | ∀ P ∈ Ξ.exactStratum μ c,
    Ξ.MemIdealPowNear (Ξ.exactStratum μ c) (Ξ.stratumJetOrder μ P + 1) H P}
  add_mem' hH hH' P hP := (hH P hP).add (hH' P hP)
  zero_mem' P _ := Ξ.memIdealPowNear_zero_fun _ _ P
  smul_mem' r _ hH P hP := (hH P hP).smul r

/-- The `(μ, c−1)` coefficient on admissible observables, as a linear functional. -/
noncomputable def coeffLin (μ : ℝ) (c : ℕ) : Ξ.admissible c →ₗ[ℝ] ℝ where
  toFun G := (Ξ.withF G.1 G.2.1).coeff Y μ (c - 1)
  map_add' G G' := Ξ.coeff_add Y G.2.1 G'.2.1 μ (c - 1)
  map_smul' r G := Ξ.coeff_smul Y G.2.1 r μ (c - 1)

/-- The transverse-jet kernel inside the admissible observables. -/
def jetKernelAdm (μ : ℝ) (c : ℕ) : Submodule ℝ (Ξ.admissible c) :=
  (Ξ.jetKernel μ c).comap (Ξ.admissible c).subtype

theorem jetKernelAdm_le_ker {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) :
    Ξ.jetKernelAdm μ c ≤ LinearMap.ker (Ξ.coeffLin Y μ c) := fun G hG =>
  Ξ.coeffLin_eq_zero_of_mem_jetKernel Y hc G hG

/-- ★★★ **The descended coefficient functional** on the transverse-jet quotient of admissible
observables: `𝒯^U_{μ,c−1}` factors through `admissible c ⧸ (admissible c ∩ 𝓘_{S^μ_c}^{n(·)+1})`. -/
noncomputable def descendedCoeff (μ : ℝ) (c : ℕ) (hc : 1 ≤ c) :
    (Ξ.admissible c ⧸ Ξ.jetKernelAdm μ c) →ₗ[ℝ] ℝ :=
  (Ξ.jetKernelAdm μ c).liftQ (Ξ.coeffLin Y μ c) (Ξ.jetKernelAdm_le_ker Y hc)


==================== Grammar/SmoothStratumMeasure.lean

/-!# The stratum measure: an intrinsic positive Radon measure carried by the exact stratum

Units 4–10 of the residue programme (Astra #132). Under the zero-order condition, the positive
linear functional `Λ` on `C_c(X, ℝ)`, `X = U ∖ D_{c+1}` (`SmoothStratumApprox`), is represented
by the Riesz–Markov–Kakutani theorem as integration against a regular Borel measure `ν` on `X`,
the **stratum measure**. It integrates every smooth test function to the `(μ, c−1)` coefficient
(`integral_stratumMeasure_test`), it is carried by the exact stratum `S^μ_c`
(`stratumMeasure_compl_exactStratum`), it represents the coefficient of every observable
vanishing near the deep zero fibre, compactly supported or not (`coeff_eq_integral_stratumMeasure`,
`observableCoeff_eq_integral_stratumMeasure`), it is independent of the transport
(`stratumMeasure_eq_of_transports`), and it is the unique regular measure integr-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold CompactlySupported
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

instance (c : ℕ) : LocallyCompactSpace (Ξ.stratumOpen c) := <proof>

/-- ★★★ **The stratum measure** `ν^μ_c` on `X = U ∖ D_{c+1}`: the Riesz measure of the positive
linear functional `Λ`. -/
noncomputable def stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  RealRMK.rieszMeasure (Ξ.Λ Y hc hzero)

/-- ★★★ **The stratum measure is carried by the exact stratum**: the complement of `S^μ_c` in
`X` is a null set. -/
theorem stratumMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0 := <proof>

/-- ★★★ **Representation for observables vanishing near the deep zero fibre**, compactly supported
in `X` or not: the `(μ, c−1)` coefficient is the integral against the stratum measure. -/
theorem coeff_withF_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) := <proof>

/-- ★★★ **The weighted residue measure** `ℛ^μ_c = ((c−1)!/Γ(μ)) · ν^μ_c`. -/
noncomputable def residueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal ((c - 1).factorial / Real.Gamma μ) • Ξ.stratumMeasure Y hc hzero

/-- ★★ **Transport independence**: the stratum measure does not depend on the chosen resolved
core transport. -/
theorem stratumMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) {μ : ℝ}
    {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero = Ξ.stratumMeasure Y' hc hzero := <proof>

/-- ★★★ **Uniqueness**: a regular measure on `X` integrating every smooth test function to the
coefficient functional is the stratum measure. -/
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero := <proof>


==================== Grammar/SmoothStratumMeasureExtremal.lean

/-!# The extremal stratum measure and the leading asymptotic

At extremal data `(λ*, m*)` the zero-order condition holds on every stratum
(`zeroOrder_of_extremalData`), so the stratum measure `ν^{λ*}_{m*}` on `U ∖ D_{m*+1}` is defined
(`extremalStratumMeasure`). For an observable `F` vanishing near the deep zero fibre `D_{m*+1}`
the normalised partition function `N^{λ*} (log N)^{−(m*−1)} Z^U_N[F]` converges to `∫ F dν`
(`tendsto_normalised_Z_extremal`); for a base observable `f` with `f ∘ π ∈ 𝓘_{m*+1}` this reads
`N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → ∫ f ∘ π dν`
(`tendsto_normalised_partitionObs_extremal`), and when the limit is nonzero
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν) N^{−λ*} (log N)^{m*−1}`
(`partitionObs_isEquivalent_extremal`). Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **The extremal stratum measure** `ν^{λ*}_{m*}` on `U ∖ D_{m*+1}`. -/
noncomputable def extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure (Ξ.stratumOpen m) :=
  Ξ.stratumMeasure Y hm (Ξ.zeroOrder_of_extremalData h m)

/-- ★★★ **Euclidean leading-index characterisation**: for a base observable `f` with
`f ∘ π ∈ 𝓘_{m*+1}`, `N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → ∫ f ∘ π dν^{λ*}_{m*}`. -/
theorem tendsto_normalised_partitionObs_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm))) := <proof>


==================== Grammar/SmoothStratumMeasureFinite.lean

/-!# The extremal stratum measure is finite

At extremal data `(λ*, m*)` the leading functional is nonnegative on every nonnegative observable
(`coeff_nonneg_of_extremalData`), so a cutoff `0 ≤ χ ≤ 1` has `T[χ] ≤ 𝒯^U_{λ*,m*−1}[1]`. Inner
regularity then bounds the total mass of the extremal stratum measure `ν^{λ*}_{m*}` by the
unit-observable coefficient (`extremalStratumMeasure_univ_le`): the leading stratum measure is a
FINITE measure (`IsFiniteMeasure` instance). When the deeper zero fibre `D_{m*+1}` is empty the
unit observable is admissible and the mass equals the coefficient
(`extremalStratumMeasure_univ_eq_of_deep_empty`): the total mass of the leading residue measure is
then the RLCT constant. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **The extremal stratum measure is finite, with total mass at most the RLCT constant**
`𝒯^U_{λ*,m*−1}[1]`. -/
theorem extremalStratumMeasure_univ_le {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ ≤
      ENNReal.ofReal ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)) := <proof>

/-- ★★★ **Total mass when the deeper zero fibre is empty**: if `D_{m*+1} = ∅`, the unit observable
is admissible and the total mass of `ν^{λ*}_{m*}` is exactly the RLCT constant
`𝒯^U_{λ*,m*−1}[1]`. -/
theorem extremalStratumMeasure_univ_eq_of_deep_empty {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (hD : Ξ.deepZeroFibre m = ∅) :
    (Ξ.extremalStratumMeasure Y h hm).real univ =
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1) := <proof>


==================== Grammar/SmoothStratumMeasurePositive.lean

/-!# Positivity of the leading coefficient with insertion

The orthant lower bound of `SmoothResolvedRLCTPositive` (there for the unit observable) is
generalised to a nonnegative base observable `f`: if `f ∘ π` is positive at a point `P₀` of the
zero fibre where exactly `m*` walls resonate with `λ*` and the prior is positive, then the
`(λ*, m*−1)` coefficient of `f` is strictly positive (`observableCoeff_pos_of_realised`). When
moreover `f ∘ π` vanishes near `D_{m*+1}`, the integral of `f ∘ π` against the extremal stratum
measure is strictly positive (`integral_extremalStratumMeasure_pos`) and the partition function
with insertion has the genuine asymptotic equivalence
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν) N^{−λ*} (log N)^{m*−1}` with a positive constant
(`partitionObs_isEquivalent_of_pos`). Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth
namespace Grammar
namespace SmoothEngine
namespace ResolvedData
variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
section Chart
variable (E : EvenChartBox Ξ.R)
end Chart
end ResolvedData
end SmoothEngine
end Grammar

/-- ★★★ **Euclidean form**: `0 < C_{λ*,m*−1}(f)`. -/
theorem observableCoeff_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.X Y).observableCoeff lam (m - 1) f hf := <proof>


==================== Grammar/SmoothStratumTest.lean

/-!# The stratum test functional

Residue programme (consult #132), unit 1. Fix `(μ, c)` with the zero-order condition. On the open
set `X = U ∖ D_{c+1}` (`stratumOpen`) the TEST FUNCTIONS are the smooth observables with compact
support inside `X` (`IsTest`); every test vanishes near the deep zero fibre, so the resolved
coefficient functional `T[G] := 𝒯^U_{μ,c−1}[G]` (`T`) is defined on them and is linear
(`T_add`, `T_smul`), positive (`T_nonneg`), monotone (`T_mono`), local on the exact stratum
(`T_eq_zero_of_eqOn_zero`), and locally bounded: `|T[G]| ≤ M · T[χ]` whenever `|G| ≤ M` and the
cutoff `χ ≥ 1` on the support of `G` (`abs_T_le`). Cutoffs equal to `1` on a compact subset of
`X` exist (`exists_cutoff`, smooth bump functions on the σ-compact Hausdorff manifold `U`). These
are the inputs of the Riesz construction of the stratum measure. Zero `sorry`/`axiom`.-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
namespace ResolvedData
variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
end ResolvedData
end SmoothEngine
end Grammar

/-- The open set `X = U ∖ D_{c+1}` carrying the stratum measure. -/
def stratumOpen (c : ℕ) : Set Ξ.R.U := (Ξ.deepZeroFibre c)ᶜ

/-- **Test functions**: compactly supported inside `X = U ∖ D_{c+1}`. -/
def IsTest (c : ℕ) (G : Ξ.R.U → ℝ) : Prop :=
  HasCompactSupport G ∧ tsupport G ⊆ Ξ.stratumOpen c

/-- **The stratum test functional** `T[G] = 𝒯^U_{μ,c−1}[G]`. -/
noncomputable def T (μ : ℝ) (c : ℕ) (G : Ξ.R.U → ℝ)
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ℝ :=
  (Ξ.withF G hG).coeff Y μ (c - 1)


==================== Grammar/SmoothTimeRescale.lean

/-!# The smooth-amplitude expansion: rescaling the phase unit (consult #117 §3)

The phase scale `β` of the smooth-amplitude integral is a TIME rescaling: exactly
`smoothIntegral F h k β b N = smoothIntegral F h k 1 b (β N)` (`smoothIntegral_beta_eq`). On the
coefficient side, `(βN)^{−μ} log(βN)^j = β^{−μ} N^{−μ} (log β + log N)^j` expands by the binomial
theorem into the **coefficient rescaling operator**
`scaleCoeff D β c μ q = β^{−μ} ∑_{j=q}^{D} c μ j (j choose q) (log β)^{j−q}`, and
`absSpectralSum_mul_pos` shows the spectral sum of `c` at `βN` is the spectral sum of
`scaleCoeff D β c` at `N`. Hence ★ `CutoffExpansion.comp_mul_pos`: a cutoff expansion of `Z`
transports to one of `N ↦ Z (βN)` with coefficients `scaleCoeff D β c`, on the same lattice and
with the same logarithmic degree (the constant picks up `β^{−L} (1 + |log β|)^D`).

Combined with the zero-support of the canonical smoo-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
namespace Grammar
namespace SmoothEngine
variable {d : ℕ}
variable {F : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ} {β b : ℝ}
end SmoothEngine
end Grammar

/-- The coefficient rescaling operator:
`scaleCoeff D β c μ q = β^{−μ} ∑_{j=q}^{D} c μ j (j choose q) (log β)^{j−q}`. -/
noncomputable def scaleCoeff (D : ℕ) (β : ℝ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (q : ℕ) : ℝ :=
  β ^ (-μ) * ∑ j ∈ Finset.Ico q (D + 1), c μ j * (j.choose q) * Real.log β ^ (j - q)


==================== Grammar/SourceLog.lean

/-!# The formal source logarithm and the connected coefficients (§20, posterior cumulants)

For a fixed sample the posterior expectation `Z_N[ηf]/Z_N[η]` is the formal quotient of two
expansions (`quotientBlocks`).  The clean organisation is through a **source**: with
`Z(ε) = Z_N[η e^{εf}] = Σ_r (ε^r/r!) Z_N[η f^r]`, the posterior cumulants of `f` are the
`ε`-derivatives at `0` of `log (Z(ε)/Z(0))`.  Anchoring by `Z(0)` makes the constant term `0`,
so Mathlib's formal logarithm `PowerSeries.logOf` applies without choosing a logarithm of the
leading evidence coefficient (consult #162, §3).

Over a commutative `ℚ`-algebra `A` and `U : A⟦ε⟧` with constant coefficient `1`:

* ★ `mul_derivative_logOf`: `U · (log U)' = U'`, the formal identity behind
  `∂_ε log Z = Z⁻¹ ∂_ε Z`;
* `coeff_succ_mul_eq_sum_logOf`: its coefficientwise form, the moment–cumulant recurrence
  `(n+1) U_{n+1} = Σ_{i+l=n} U_-/

-- section/variable skeleton:
open PowerSeries Finset
namespace Grammar
section FormalLog
variable {A : Type*} [CommRing A] [Algebra ℚ A]
omit [Algebra ℚ A] in
end FormalLog
section Source
variable {A : Type*} [CommRing A] [Algebra ℚ A] {Z : A⟦X⟧} {Bi : A}
omit [Algebra ℚ A] in
end Source
section Blocks
variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
variable {a b c : ℕ → K} {Z : K⟦X⟧⟦X⟧}
omit [CharZero K] in
end Blocks
end Grammar

/-- The **variance blocks**: `κ₂(j) = (c/b)_j − Σ_{i ≤ j} (a/b)_i (a/b)_{j−i}`, the all-orders
blocks of the posterior variance when `a, b, c` are the blocks of `Z_N[ηf], Z_N[η], Z_N[ηf²]`. -/
noncomputable def varianceBlocks (a b c : ℕ → K) (j : ℕ) : K :=
  quotientBlocks c b j -
    ∑ i ∈ range (j + 1), quotientBlocks a b i * quotientBlocks a b (j - i)

/-- ★ **The variance blocks are the second connected coefficients**:
`κ₂(j) = quotientBlocks c b j − Σ_{i ≤ j} quotientBlocks a b i · quotientBlocks a b (j − i)`
for `Z = B + εA + ε²C/2 + …` with blocks `a, b, c`. -/
theorem coeff_two_mul_coeff_two_logOf_blocks (hb : b 0 ≠ 0) (hZ0 : constantCoeff Z = mk b)
    (hZ1 : coeff 1 Z = mk a) (hZ2 : 2 * coeff 2 Z = mk c) (j : ℕ) :
    coeff j (2 * coeff 2 (logOf (C (mk b)⁻¹ * Z))) = varianceBlocks a b c j := <proof>


==================== Grammar/SpectralCoefficients.lean

/-!# Spectral coefficients and regrouping (Stage 3g, Gate D)

Unit 237 (Taylor-tree programme; Astra #27). The low-spectrum part of the polynomial Taylor tree,
with truncated moments replaced by full fluctuation moments, is regrouped by spectral exponent
`μ ∈ latticeBelow Q L` and log power `j`:
```
mainPart_p = ∑_{μ ∈ Λ_L} ∑_{j ≤ n} N^{-μ} (log N)^j · coeffTerm_p(μ, j),
coeffTerm_p(μ, j)
  = K_k ∑_{(γ,c) ∈ P_p} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j) fluctMoment_p(μ, q-j)
```
(`mainPart_eq_sum`: aggregate the list entries with `coeffAt` — the coefficient is the aggregated
one, never that of a single list entry — and reflect the binomial sum). The **spectral
coefficient** `A_{μ,j} = ∑_p β^p/p! coeffTerm_p(μ,j)` (`spectralCoeff`) is defined independently of
the cutoff `L` and its series is absolutely convergent (`summable_coeffTerm_series`: the uniform
budget `|coeffAt| ≤ (n+1)! Q^n`, `C-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
open MonoRep
open Classical in
end Grammar

/-- The Stage 1 weights of the monomial `u^h` with exponents `2k`. -/
noncomputable def monoWeights {d : ℕ} (h k : Fin d → ℕ) : Fin d → ℝ :=
  fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1

/-- Per phase order: the coefficient of `N^{-μ} (log N)^j` (the paper's `A_{μ,j}` before the
sum over phase orders). -/
noncomputable def coeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (μ : ℝ) (j : ℕ)
    (P : MonoRep (n + 1)) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * (P.map fun s => s.2 * ∑ q ∈ Finset.Ico j (n + 1),
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + s.1) k)) μ q * (q.choose j : ℝ) *
      fluctMoment β a p μ (q - j)).sum

/-- **The spectral coefficient** `A_{μ,j}` — defined without reference to any cutoff; the paper's
`C_{μ,m}` is `A_{μ,m-1}` (`spectralCoeff_eq` in `CandidateSupport.lean` displays the formula). -/
noncomputable def spectralCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (ξ η : MonoRep (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
    coeffTerm n h k β (eval ξ 0) p μ j (mul η (pow (fluct ξ) p))


==================== Grammar/SpectralLattice.lean

/-!# The spectral lattice of a monomial family (Stage 3a)

Unit 230 (Taylor-tree programme; Astra #27). All exponents that can occur in the state densities of
the monomials `u^{h+γ}` (any shift `γ ∈ ℕ^d`) under `τ = u^{2k}` are of the form
`(hᵢ+γᵢ+1)/(2kᵢ)`; with `Q = 2 ∏ᵢ kᵢ` every such exponent is a positive multiple of `1/Q`
(`ratio_mem_lattice`), hence distinct exponents are at least `1/Q` apart
(`lattice_sub_ge`) and only finitely many lie below any cutoff `L` (`latticeBelow`,
`mem_latticeBelow`). These are the two facts Stage 3 needs: the spacing bounds the denominators
`1/|α|` produced by the convolution calculus uniformly in the monomial, and the finite cutoff set
turns every spectral sum into an ordinary `Finset` sum. No `sorry` and no additional `axiom`
declarations.-/

-- section/variable skeleton:
open Set
namespace Grammar
end Grammar

/-- The finite set of lattice points below the cutoff `L`. -/
noncomputable def latticeBelow (Q : ℕ) (L : ℝ) : Finset ℝ :=
  (Finset.range ⌈L * Q⌉₊).image fun m : ℕ => (m : ℝ) / Q


==================== Grammar/StateDensity.lean

/-!# The exact state density of a monomial on the unit box

Unit 224 (Taylor-tree programme, Stage 1b). For weights `w : Fin (n+1) → ℝ` the weighted box
integral `∫_{(0,1]^{n+1}} ∏ aᵢ^{wᵢ} g(∏ aᵢ) da` (`weightedBoxIntegral`) equals `∫₀¹ v(z) g(z) dz`
for an **explicit power–log density** `v = eval (stateDensityRep n w)`
(`weightedBoxIntegral_eq_stateDensity`), for every measurable `g : ℝ → ℝ≥0∞`. The representation is
built by the one-coordinate convolution calculus of unit 223: one coordinate has density `a^{w₀}`,
and each further coordinate acts by `PowLogRep.conv`. Consequently (`stateDensityRep_exponent_mem`,
`stateDensityRep_degree_lt`) every term `c · z^{μ-1} (-log z)^j` of the density has `μ = wᵢ + 1` for
some coordinate and `j` strictly less than the number of coordinates with that value: the exact
multivariate state density `v(τ) = ∑_{μ} ∑_{j < r(μ)} c_{μ,j} τ^{μ-1} (-log τ)^j` of -/

-- section/variable skeleton:
open MeasureTheory Set Real
namespace Grammar
end Grammar

/-- The state-density representation for weights `w` on `n+1` coordinates. -/
noncomputable def stateDensityRep : (n : ℕ) → (Fin (n + 1) → ℝ) → PowLogRep
  | 0, w => [(w 0 + 1, 0, 1)]
  | n + 1, w => PowLogRep.conv (w 0) (stateDensityRep n (Fin.tail w))


==================== Grammar/StateDensityLeadCoeff.lean

/-!# The leading coefficient of the state density

Unit 226 (Taylor-tree programme, Stage 1d). Let `l = min (wᵢ + 1)` with multiplicity `m`. The
state density `v = eval (stateDensityRep n w)` has terms `z^{μ-1} (-log z)^j` with `μ ≥ l` and, at
`μ = l`, `j ≤ m - 1` (unit 224). Its **top coefficient** (the coefficient of
`z^{l-1} (-log z)^{m-1}`, `PowLogRep.coeffAt`) is
```
c_{l,m-1} = (1/(m-1)!) · ∏_{i : wᵢ+1 ≠ l} 1/(wᵢ + 1 - l)
```
(`stateDensityRep_leadCoeff`). The proof is Abelian, as in Headline XXI: `(s+l)^m ∫₀¹ z^s v(z) dz`
is computed in two ways as `s → -l⁺` — from the product Mellin transform `∏ 1/(wᵢ+s+1)`
(unit 225) it tends to the product on the right; from the termwise transform
`∑ cₜ jₜ!/(s+μₜ)^{jₜ+1}` every term tends to `0` except the top one, which tends to
`(m-1)! · c_{l,m-1}`. In the monomial normalisation (`wᵢ = (hᵢ+1)/(2kᵢ) - 1`, Jacobian `∏ 1/(2kᵢ)`)
the top coefficient-/

-- section/variable skeleton:
open MeasureTheory Set Real Filter Topology
namespace Grammar
open Classical in
open Classical in
end Grammar

/-- The coefficient of `z^{μ-1} (-log z)^j` in a representation (sum over matching terms). -/
noncomputable def PowLogRep.coeffAt (c : PowLogRep) (μ : ℝ) (j : ℕ) : ℝ :=
  ((c.filter fun t => t.1 = μ ∧ t.2.1 = j).map fun t => t.2.2).sum


==================== Grammar/TwoSiteExchange.lean

/-!# Two-site exchangeable weights: averaging the quotient balances the posterior (§20, sanity anchor)

On a base with two sites of masses `p, 1−p` and positive random posterior weights `U, V`, the
posterior mass of the first site is `Q_p = pU/(pU + (1−p)V)` (`twoSitePosteriorMass`).  If `(U,V)`
is **exchangeable**, then

★★ `integral_twoSitePosteriorMass_sub`:
`E Q_p − p = (p(1−p)(1−2p)/2) · E[(U−V)² / ((pU+(1−p)V)((1−p)U+pV))]`

(the symmetrised algebraic identity `twoSitePosteriorMass_symm_sub` integrated against the
exchangeable law; the ratio is bounded by `1/min(p,1−p)²`, so no moments of `U, V` enter).
Consequently ★ `integral_twoSitePosteriorMass_mem`: `E Q_p ∈ [min(p,1/2), max(p,1/2)]` — random
exchangeable weights move the averaged posterior mass **toward equal allocation**, a minority site
gains and a majority site loses; in particular positivity of an observable does not make th-/

-- section/variable skeleton:
open MeasureTheory
namespace Grammar
section Algebra
variable {p u v : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hu : 0 < u) (hv : 0 < v)
include hp hp₁ hu hv
end Algebra
section Exchangeable
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (U V : Ω → ℝ)
  (hU : Measurable U) (hV : Measurable V) (hpos : ∀ ω, 0 < U ω ∧ 0 < V ω)
  (hexch : μ.map (fun ω => (U ω, V ω)) = μ.map (fun ω => (V ω, U ω))) {p : ℝ} (hp : 0 < p)
  (hp₁ : p < 1)
omit [IsProbabilityMeasure μ] in
include hU hV hexch in
include hU hV hpos hp hp₁
include hexch
end Exchangeable
section FiniteAtoms
variable {β lam : ℝ}
end FiniteAtoms
end Grammar

/-- The posterior mass of the first of two sites with base masses `p, 1−p` and weights `u, v`. -/
noncomputable def twoSitePosteriorMass (p u v : ℝ) : ℝ := p * u / (p * u + (1 - p) * v)

/-- The exchangeability kernel `(u−v)² / ((pu+(1−p)v)((1−p)u+pv))`. -/
noncomputable def twoSiteKernel (p u v : ℝ) : ℝ :=
  (u - v) ^ 2 / ((p * u + (1 - p) * v) * ((1 - p) * u + p * v))

/-- ★★ **Averaging the quotient over exchangeable weights**:
`E Q_p(U,V) − p = (p(1−p)(1−2p)/2) · E[(U−V)²/((pU+(1−p)V)((1−p)U+pV))]`. -/
theorem integral_twoSitePosteriorMass_sub :
    (∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ) - p =
      p * (1 - p) * (1 - 2 * p) / 2 * ∫ ω, twoSiteKernel p (U ω) (V ω) ∂μ := <proof>

/-- ★ **Balancing**: `E Q_p ∈ [min(p,1/2), max(p,1/2)]` — exchangeable random weights move the
averaged posterior mass toward equal allocation. -/
theorem integral_twoSitePosteriorMass_mem :
    min p (1 / 2) ≤ ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ∧
      ∫ ω, twoSitePosteriorMass p (U ω) (V ω) ∂μ ≤ max p (1 / 2) := <proof>


==================== Grammar/WeightedMixedAsymptotic.lean

/-!# The mixed-ratio weighted asymptotic

Fourth step of the mixed-ratio general-`d` monomial programme (Astra #15, route A): the leading
asymptotic of the real weighted box integral

  `W_ℓ(N) = ∫_{(0,1]^d} ∏ tᵢ^{ℓᵢ-1} e^{-βN ∏ tᵢ} dt`

for **arbitrary** positive exponents `ℓᵢ` with minimum `λ` attained `m` times:

  `W_ℓ(N) / (N^{-λ} (log N)^{m-1}) → Γ(λ) β^{-λ} / (m-1)! · ∏_{ℓᵢ > λ} 1/(ℓᵢ - λ)`

(`mixedBoxReal_tendsto`). The multiplicity is `multCount ℓ λ = ∑ᵢ [ℓᵢ = λ]` and the residue product
`resFactor ℓ λ = ∏ᵢ (if ℓᵢ = λ then 1 else 1/(ℓᵢ-λ))`, both stated as sums/products over all
coordinates so that they are manifestly permutation invariant and peel off the first coordinate by
`Fin.sum_univ_succ`/`Fin.prod_univ_succ`.

The proof is an induction on the number of coordinates. If every coordinate is minimal, this is the
equal-ratio theorem (units 172–173). Otherwise a nonminimal coordi-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology Asymptotics
namespace Grammar
end Grammar

/-- The multiplicity of the value `l` among the exponents. -/
noncomputable def multCount {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : ℕ :=
  ∑ i, if ℓ i = l then 1 else 0


==================== Grammar/WeightedNormalisedBoxCore.lean

/-!# The weighted normalised box core: Jacobian orders and a tangential unit (CCCXLV; phase E, unit E2)

Consult #102 §2, §5. The normalised box core of CCCXXI transports the prior-weighted Lebesgue
measure; a resolution chart carries in addition the **Jacobian weight** `∏_i |y_i|^{h_i}` and a
positive **tangential unit** in the phase, `K = u(y_tan) · ∏_i y_i^{2k_i}`. On the normal box
`y_i = λ_i(s) v_i` (`v_i > 0`) the weight factors as
`∏_{j∉I} |t_j|^{h_j} · ∏_{i∈I} λ_i(s)^{h_i} · ∏_i v_i^{h_i}` (`wgt_Φ`): the tangential factor
`H_I(s)` and the normal scaling `L_I(s)` go into the amplitude `c_h = J·H_I·L_I·fϕ` (`JW`, `cw`) and
the datum `x = (J H L · fϕ) ⋆ fφ` (`xDataW`), while `∏ v^{h}` is the chart density's own factor
(`chartDensity (hι h I σ) c_h`). The unit enters the normalisation `u(t)·t_I(t)·∏λ^{2k} = β`
(`WData.hnorm`). The core `wcore` records the orders `h` (`wcore.h = hι h I σ-/

-- section/variable skeleton:
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace Grammar
open CoeffFamily MonoRep
namespace NormalisedBox
variable {d : ℕ} (k h : Fin d → ℕ) (I : Finset (Fin d)) {n : ℕ} (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (lamT : (Tan I → ℝ) → (Nrm I → ℝ))
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
end NormalisedBox
namespace NormalisedBox
variable {d : ℕ} (k h : Fin d → ℕ) (I : Finset (Fin d)) {n : ℕ} (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (he : Continuous e) (he_inj : Function.Injective e)
  (lamT : (Tan I → ℝ) → (Nrm I → ℝ)) (hlamT : Measurable lamT)
  (hlam_cont : ContinuousOn lamT (range e)) (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j)
  (ϕ : (Fin d → ℝ) → ℝ) (b b' : ℝ) (hb : 0 < b) (hbb' : b < b')
  (Fϕ Fφ : UniformSeriesFamily K (n + 1) b')
  (hϕ_eq : ∀ s, ∀ v ∈ box (ι := Fin (n + 1)) b, ϕ (Φ I σ e lamT (s, v)) = evalF (Fϕ.f s) v)
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
omit [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
omit [MeasurableSpace K] [BorelSpace K] in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hϕ_eq in
include he he_inj hpos hϕ_eq in
end NormalisedBox
namespace NormalisedBox
variable {d : ℕ} {k h : Fin d → ℕ} {I : Finset (Fin d)} (hkI : ∀ j : Nrm I, 0 < k j.1) {n : ℕ}
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {W : Set (Fin d → ℝ)} (hWm : MeasurableSet W) {ϕ φ : (Fin d → ℝ) → ℝ} (hϕm : Measurable ϕ)
  (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w) (L : LocalisationData (Fin d → ℝ)) (D : WData k I n K W ϕ φ)
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (wgt h w * ϕ w))
  (hLphase : ∀ y, L.phase y = D.unit (WaterFilling.tan I y) * CoordModel.phase d k y)
  (hLobs : L.obs = φ)
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
end NormalisedBox
end Grammar

/-- The ambient Jacobian weight `∏_i |w_i|^{h_i}`. -/
noncomputable def wgt (w : Fin d → ℝ) : ℝ := ∏ i, |w i| ^ h i


==================== Grammar/WickEnvelope.lean

/-!# The absolute-moment envelope of the Wick series

The `r`-th term of the generating series of the empirical coefficient is the population
coefficient of `η (u^k ζ)^r` at exponent `μ + r/2`.  Writing `(u^k)^r = u^{2jk}` (`r = 2j` or
`2j+1`) and applying the iterated monomial shift (`abs_empCoeff_mono_pow_le`) at the FIXED depth
data of `μ` and `μ + 1/2`, then the jet bound of the population coefficient and the Leibniz bound
for jets of powers, gives the deterministic Gamma-growth estimate

`|C_{μ+r/2,q}[η (u^k ζ)^r]| ≤ K · Π_{i<⌊r/2⌋} (μ + 1/2 + i + d − 1) · C_η · (r+1)^R · ‖J_R ζ‖^r`

(`abs_empCoeff_wick_term_le`).  Against an exponential moment `E e^{δ‖J_R ζ‖²} < ∞` with
`δ > 1/4`, the weighted absolute moments `Σ_r (1/r!) E|C_{μ+r/2,q}[η (u^k ζ)^r]|` are summable
(`summable_wick_envelope`, ratio test with limit `1/(4δ)`): the envelope hypothesis of the Wick
series is discharged by a G-/

-- section/variable skeleton:
open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ContDiff Nat
namespace Grammar
open SmoothEngine
variable {d : ℕ} {h k : Fin d → ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
end Grammar

/-- ★★★ **The Wick series with every integrability hypothesis discharged**: for a smooth field
whose value process on an open `U ⊇ closedBox d 1` is Gaussian, with pointwise variance profile
`W` of the scaled field `u^k ζ`, measurable jets, and an exponential moment
`E e^{δ ‖J_{R₀} ζ‖²} < ∞` of the field's jet with `δ > 1/4` at the depth data of `μ + 1/2`,

`E[C_{μ,q}[ζ, η]] = Σ_j (1/(2^j j!)) · C^pop_{μ+j,q}[η W^j]`. -/
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
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q := <proof>

================ (5) KEY EXISTING DECLARATIONS (PrincipalPartUniqueness, MellinRegularization, MellinLogWeights)
noncomputable def polarPart (D : ℕ) (a : ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (D + 1), a q / (s - μ) ^ (q + 1)

noncomputable def mellinContinuation (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) :
    ℂ :=
  mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s

noncomputable def polarCoeff (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) : ℂ :=
  (-1) ^ (q + 1) * (q.factorial : ℂ) * (c μ₀ q : ℂ)

theorem polarCoeff_unique (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) {a : ℕ → ℂ}
    (ha : (fun s => mellinContinuation Q D E c U s - polarPart D a (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = polarCoeff c μ₀ q := by
noncomputable def principalParts (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
    (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))

noncomputable def cutoffRemainderFun (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (N : ℝ) :
    ℂ :=
  (E N : ℂ) - ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N

theorem mellin_eq_mellin_cutoffRemainderFun_add_principalParts (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U a : ℝ} (haU : a ≤ U)
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → a ≤ μ) {s : ℂ}
    (hs0 : 0 < s.re) (hsa : s.re < a) :
    mellin (fun N => (E N : ℂ)) s =
      mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s := by
theorem mellinMom_pow_mul_exp_eq_iteratedDeriv {μ a : ℝ} (hμ : 0 < μ) (r ℓ : ℕ) :
    mellinMom (fun τ => τ ^ r * exp (a * τ)) μ ℓ =
      (-1) ^ ℓ * iteratedDeriv ℓ (fun ν => fluctuation 1 ν a) (μ + r / 2) := by
