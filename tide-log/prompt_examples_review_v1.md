# Whole-document review: examples_slop.tex (companion to *Expectations and the Exceptional Divisor*)

You are an independent reviewer. Below is the full text of a working note developing complete, formalised examples of
the paper's machinery (six sections: candidates; monomial phases / deep linear network; the cone; the blow-up example
x²(x²+y²); rank-one matrix factorisation at a rank-one truth; the two-leaf naive Bayes model), followed by the
headline summaries of the Lean 4 theorems that back it (grammar library, units DLXXXII–DXCV). Every numerical claim in
the note has been checked by scripts (not reproduced here).

Please return, tersely and concretely:

**(A) Mathematical errors or misstatements** in the note — wrong constants, wrong signs, wrong exponents, claims that
contradict the stated theorems, misuse of the paper's notions (polar distributions, leading measure, tilt, fluctuation
functions, partially/fully vanishing observables). Quote the sentence and give the correction.

**(B) Fidelity between text and theorems**: any place where the note claims something is "a theorem" or "formal" but
the quoted Lean statement (as summarised in the headline) is weaker, differently normalised, or about a different object.

**(C) Exposition**: at most five concrete improvements (ordering, missing definitions, redundant material, what a
reader of the paper would want first).

**(D) What next**: rank the remaining gaps (listed in the "What is formal" subsections and below) by value for the
paper, and propose at most three new formal targets that are (i) genuinely about the paper's machinery (polar
distributions, leading measures, tilts, corrections), (ii) feasible in Lean 4/Mathlib in a day each, (iii) not
already done. Known remaining gaps: the tie formula A_{1/2,1}[η] for the blow-up with a nonconstant amplitude; the
Laplace evaluations for the deep linear network of depth ≥ 3 and for the Gaussian prior (Bessel K₀ is not in
Mathlib); the leading Laplace term of the naive Bayes partition function (log² amplitude); the rank-one Morse–Bott
Laplace expansion.

## The note (LaTeX body)

\begin{document}
\maketitle

\begin{abstract}
Working notes developing, in complete detail and with formal counterparts, examples of the core machinery of \emph{Expectations and the Exceptional Divisor}: models for which the whole asymptotic expansion of $\Zcal_N[f]=\int f\,e^{-NK}\varphi\,dw$, population and frozen-field, can be derived, with the polar distributions written out, the leading measure identified, the corrections evaluated, and the posterior expectations read off. This first section surveys the candidates across the formalised material (the grammar library and the sibling seabeds: deep linear networks, matrix factorisation, Markov trees, radial and monomial families) and ranks them by how completely the expansion can be derived and how much of it is already formal.
\end{abstract}

\tableofcontents

\section{Candidates}\label{sec:candidates}

\subsection{What ``complete'' means}

An example is complete when all of the following can be written down and, where the machinery of the paper is formalised, backed by a declaration:
\begin{enumerate}
\item the resolution $\pi\colon U\to W$ with its charts, the wall data $(k_i,h_i)$, the depth and resonance structure, the candidate lattice $Q^{-1}\N$ and the leading pair $(\lambda,m)$;
\item the chart zeta functionals $T_{h,k}(s)[G]$ and their polar coefficients $A_{\mu,r}[G]$ at every candidate exponent, hence every population coefficient $c_{\mu,q}(f)$ for a stated class of priors and observables (constant, polynomial, smooth), through the constant term at the leading exponent and at least one further exponent;
\item the leading measures $\rho^\lambda_m$, $\nu^\lambda_m$ and the tilted $\widehat\nu^\lambda_m(\xi)$ in closed form, and the posterior quotient at leading order with its three regimes (generic, partially vanishing, fully vanishing) exhibited on named observables;
\item the frozen-field coefficients through the coupling-average formula, with the fluctuation functions and index derivatives that appear evaluated as far as they close (for $\lambda=\tfrac12$ everything reduces to derivatives of $S_{1/2}$, which is an error function);
\item where a state density $V(\varepsilon)=\operatorname{vol}\{K<\varepsilon\}$ is known in closed form, the exact Laplace transform $\Zcal_N[1]=\int e^{-N\varepsilon}\,dV(\varepsilon)$ as an independent check of the whole expansion.
\end{enumerate}
The criterion excludes models whose real log canonical threshold is known only through comparability of the phase with a monomial ideal: comparability fixes the exponents and logarithmic degrees but not one coefficient, so such models give a leading pair and nothing more.

\subsection{The survey}

Three sources of exactly computable examples exist in the formalised material. The \emph{monomial phases} $K=\prod_iw_i^{2k_i}$ on a box, for which the resolution is the identity (the identity is a Watanabe modification of a monomial phase in the hironaka library, and the grammar library instantiates the whole resolved machinery on it), the chart zeta functional of a monomial amplitude is the product $\prod_i(h_i+\gamma_i+1-2k_is)^{-1}$, and every coefficient is an explicit finite sum. The \emph{radial reductions}, phases that become monomial in polar or bipolar coordinates, $K=|w|^{2k}$, $K=|x|^2|y|^2$, $K=y^2(x^2+y^2)$, for which the angular integral averages the amplitude over spheres and the radial integral is one-dimensional. And the \emph{regular models}, $K$ a nondegenerate quadratic form, where the population expansion is the Laplace expansion in Gaussian moments and the empirical one is the half-integer ladder of $S_{1/2}$. The models of the sibling seabeds fall into these classes exactly when they are complete: the scalar deep linear network with zero target is a monomial phase; rank-one matrix factorisation with zero truth is a bipolar radial reduction; the leap-complexity model at $M=1$ is a monomial phase; the Markov-tree and general NMF and DLN results are of the comparability kind and stop at the leading pair.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}>{\raggedright\arraybackslash}p{3.1cm}>{\raggedright\arraybackslash}p{2.4cm}>{\raggedright\arraybackslash}p{1.6cm}>{\raggedright\arraybackslash}p{4.6cm}>{\raggedright\arraybackslash}p{2.2cm}@{}}
\toprule
Model / phase & Resolution & $(\lambda,m)$ & What is exact & Formal status \\
\midrule
\multicolumn{5}{@{}l}{\emph{Tier 1: monomial phases (all orders exact, all formal machinery applies directly)}}\\
Scalar DLN, zero target: $K=(w_1\cdots w_L)^2$ & identity & $(\tfrac12,L)$ & every coefficient; state density $V(\varepsilon)$ closed; $S_{1/2}$ orbit (erf) & volume identity (qd), monomial regressions (grammar), zeta closed forms (watanabe-examples) \\
Crossing $x^2y^2$ & identity & $(\tfrac12,2)$ & through the constant term; polar data $\tfrac14$, $0$ & fully formal for constant data \\
Mixed exponents $x^2y^6$ & identity & $(\tfrac16,1)$ & three tiers in sequence; boundary walls & leading term and first correction formal (generic gap) \\
Triple crossing $x^2y^2z^2$ & identity & $(\tfrac12,3)$ & depressed polynomial $t^2+\pi^2$; rate $2/\log N$ for $x^2$ & leading measure formal (point mass) \\
Leap model $M=1$: $K=b^2\prod_ru_r^2$ & identity & $(\tfrac12,q)$ & as the DLN with $L=q$ & RLCT formal (leap-slt) \\
\midrule
\multicolumn{5}{@{}l}{\emph{Tier 2: radial reductions (all orders exact after polar coordinates; assembly to be written)}}\\
Rank-one MF, zero truth: $K=|x|^2|y|^2$, $x\in\R^M$, $y\in\R^N$ & bipolar, or blow-ups & $(\tfrac{\min(M,N)}2,\ 1\text{ or }2)$ & radial monomial with $h=(M-1,N-1)$; nonnegativity constraint changes the parity & rank-one true-target RLCT formal (nmf); zero-truth case new \\
Isotropic $K=|w|^{2k}$ & one blow-up & $(\tfrac d{2k},1)$ & radial Gamma times spherical means of the amplitude & radial families formal (watanabe-examples, RLCT level) \\
Weighted $K=y^2(x^2+y^2)$; blow-up example $x^2(x^2+y^2)$ (\cref{sec:blowup}) & one blow-up & $(\tfrac12,2)$ & zeta $2^{3w+1}\Gamma(w+\tfrac12)^2$ against the Gaussian prior; the tie with unequal $(k,h)$ & zeta factorisation and closed form formal (DLXXXIV, DXC) \\
\midrule
\multicolumn{5}{@{}l}{\emph{Tier 3: regular models}}\\
$K=x^2$ on $[-1,1]$, $K=|w|^2$ & identity & $(\tfrac d2,1)$ & Laplace expansion; empirical coefficients as erf & one-dimensional instance and $S_{1/2}$ orbit formal \\
\midrule
\multicolumn{5}{@{}l}{\emph{Tier 4: stretch (complete expansion not yet in reach)}}\\
Leap model $M\ge2$: $K=(\sum_jb_j\prod_ru_{j,r})^2$ & smooth hypersurface plus singular locus & $(\tfrac12,1)$ & regular-type off the singular locus of $\alpha=0$ & RLCT formal (leap-slt) \\
Two-leaf naive Bayes, independent truth (\cref{sec:nb}) & moment map; fibre volume exact & $(\tfrac32,3)$ & $\rho=2\log(M/|\mu|)\log(V/M|\mu|)$; complete, $N^{-2}$ from a sign jump & moment map, label symmetry, the exact fibre volume formal (DLXXXVI--VIII) \\
TMS $k$-gon, $k=3,4$ & Morse--Bott along the critical family & $(\tfrac{\dim-1}2,1)$ & Laplace along the family if the normal form is Morse--Bott & loss closed forms formal (tms) \\
General DLN, NMF, Markov trees & Aoyagi / Hayashi--Watanabe / Zwiernik & known & leading pair only & comparability arguments \\
\bottomrule
\end{tabular}
\caption{Candidates for complete examples. The formal status names the seabed in which the relevant identities are proved; ``new'' marks the assembly that the example would add.}
\label{tab:candidates}
\end{table}

\subsection{Tier 1: monomial phases}

\paragraph{The scalar deep linear network with zero target (\cref{sec:dln}).} The one-neuron-per-layer deep linear network $w\mapsto w_1w_2\cdots w_L$ with zero target has population divergence $K=\tfrac12(w_1\cdots w_L)^2$ (up to the normalisation of the Gaussian noise), the cross monomial of depth $L$. This is the flagship candidate, for four reasons. Every ingredient of the paper is exact: the walls are the $L$ coordinate hyperplanes with $(k_i,h_i)=(1,0)$, all of ratio $\tfrac12$, so $(\lambda,m)=(\tfrac12,L)$, the leading stratum is the origin and the leading measure is a point mass, and the depth-$c$ strata are the coordinate subspaces of codimension $c$; the chart zeta functional of a monomial amplitude $w^\gamma$ is $\prod_i(\gamma_i+1-2s)^{-1}$, with a pole of order $\#\{i:\gamma_i=0\}$ at $\tfrac12$ and poles of order $\#\{i:\gamma_i=2j\}$ at $\tfrac{2j+1}2$, so every population coefficient of a polynomial or Taylor-expanded amplitude is a finite sum of products of derivatives of $\Gamma$ at half-integers, and the state density is known in closed form,
\[
\operatorname{vol}\{w\in[-1,1]^L:(w_1\cdots w_L)^2<\varepsilon\}=2^L\sqrt\varepsilon\sum_{j<L}\frac{(-\tfrac12\log\varepsilon)^j}{j!}\qquad(0<\varepsilon\le1),
\]
a formal theorem of the qd seabed (\texttt{Qd.volume\_firstOctantL\_closed\_form}), whose Laplace transform gives $\Zcal_N[1]$ for the flat prior exactly, in incomplete Gamma functions, as an independent check of every coefficient. For the Gaussian-localised prior the zeta function is $\pi^{-L/2}(\ldots)^z\Gamma(z+\tfrac12)^L$ (\texttt{zeta\_mult\_pi} in watanabe-examples), and the expansion has the universal shape $A_{L-1}N^{-1/2}P_{L-1}(\log N+\kappa_L)$ with the depressed polynomials $P_1(t)=t$, $P_2(t)=t^2+\pi^2$, $P_3(t)=t^3+\tfrac72\pi^2t+6\zeta(3)$, whose coefficients are polygamma values at $\tfrac12$: this is the lower-order structure of the paper's Corollary on population coefficients as polar data, in its most transparent instance, and it has been checked numerically against SGLD estimates at $n\sim10^3$--$10^5$ where the corrections are $10$--$30\%$ of the value. The empirical theory is closed in elementary functions: $\lambda=\tfrac12$ puts every fluctuation function that appears on the regular orbit, $S_{(j+1)/2}=\partial_a^jS_{1/2}$ with $S_{1/2}(a)=\sqrt\pi e^{a^2/4}(1+\operatorname{erf}(a/2))$, and the index derivatives at $\tfrac12$ are the only transcendental input. The observables are the ones of the paper: $f=w_i^2$ vanishes on the wall $w_i=0$ and loses one logarithm, so $\E[w_i^2\mid\Dn]\sim C/\log n$; $f=w_1w_2$ is odd in each of two interior directions and its population coefficients vanish identically, while its frozen coefficients survive when the branch traces of the field are not reflection-compatible; $f=K$ shifts every exponent by one and gives $\E[K\mid\Dn]\sim\tfrac1{2n}(1+\ldots)$ with the ratio $S_{3/2}/S_{1/2}$ of the paper; and $f=\prod w_i^2$ is the model's own output. The example is also the $M=1$ case of the leap-complexity model and the depth-$L$ case of the qd cross-monomial family.

\paragraph{The crossing $x^2y^2$, the mixed exponents $x^2y^6$, the triple crossing $x^2y^2z^2$.} These are the running examples of the paper and should be developed to the same completeness as the DLN, in particular past constant data: the tie formulas for a smooth amplitude and a nonconstant field (the finite parts $A_{1/2,1}$ along the axes), the three tiers of $x^2y^6$ with its boundary walls (all shifts are candidates, no parity cancellation, and the exact identity $\Zcal_N[1]=\tfrac{\Gamma(1/6)}4N^{-1/6}-\tfrac{\Gamma(1/2)}4N^{-1/2}+O(e^{-\varepsilon N})$ for constant data), and the triple crossing, where the constant term of $N^{-1/2}$ carries $\pi^2$ and the observable $x^2$ decays at the rate $2/\log N$ because its numerator has nonzero coefficients at two logarithmic degrees. The mixed monomial $\prod x_i^{2k_i}$ with distinct exponents (the qd anisotropic family, $x^{2a}y^{2b}$ with closed-form volume $\tfrac{4b}{b-a}\varepsilon^{1/2b}-\tfrac{4a}{b-a}\varepsilon^{1/2a}$) is the general member: its leading measure is the weighted restriction of the prior to the subspace of the fastest-vanishing coordinates, formal in the grammar library (\texttt{monomial\_integral\_extremalStratumMeasure\_eq}).

\subsection{Tier 2: radial reductions}

\paragraph{Rank-one matrix factorisation with zero truth.} For $x\in\R^M$, $y\in\R^N$ and $K=\|xy^{\mathsf T}\|_F^2=|x|^2|y|^2$ the phase is a monomial in the two radii, and in bipolar coordinates the prior measure carries the Jacobian $r_x^{M-1}r_y^{N-1}$: the wall data are $(k,h)=(1,M-1)$ and $(1,N-1)$, the ratios $\tfrac M2$ and $\tfrac N2$, so $(\lambda,m)=(\tfrac{\min(M,N)}2,1)$ for $M\ne N$ and $(\tfrac M2,2)$ for $M=N$, and the angular integrals average the amplitude over the two spheres, so that every coefficient is a one-dimensional monomial coefficient of a spherically averaged amplitude. The resolution in the paper's sense is the pair of blow-ups of the two origins, whose charts the hironaka library constructs; the derivation through the resolved machinery is new, and the polar reduction is the check. The nonnegative version, NMF, restricts $x,y$ to the positive orthants: the walls become boundary walls, the odd corrections that cancel by parity in the unconstrained model survive, and the two models have the same leading pair with different first corrections, which is the parity remark of the paper made concrete. The nmf seabed proves the rank-one local RLCT $(M+N-1)/2$ at a nonzero truth, the regular-type regime; the zero-truth regime is the singular one and is not in the seabed.

\paragraph{Isotropic and weighted radial phases.} $K=|w|^{2k}$ on a ball, and more generally $K=q(w)^k$ for a positive definite quadratic form, reduces in polar coordinates to the one-dimensional monomial $r^{2k}$ with $h=d-1$, $(\lambda,m)=(\tfrac d{2k},1)$, and the population coefficients are the spherical means of the Taylor coefficients of the amplitude against Gamma values: an observable that is a harmonic polynomial of positive degree has zero spherical mean and vanishes at the leading order, seen instead at the shifted exponent through $|w|^2$-multiples. The weighted phase $y^2(x^2+y^2)$ and the paper's blow-up example $x^2(x^2+y^2)$ need one blow-up of the origin, after which the exceptional curve and the strict transform carry unequal data $(2,1)$ and $(1,0)$ with the same ratio $\tfrac12$: a tie of two walls with different $(k,h)$, whose lower coefficient is the paper's $A_{1/2,1}$ with the correct residue factors $\tfrac1{2k}$, and whose zeta function $2^{3z}\Gamma(z+\tfrac12)^2/\pi$ differs from that of $x^2y^2$ by the shift $\kappa$ that the leading pair cannot see. The blow-up chart constructors of the hironaka library (\texttt{blowUpResolution}, \texttt{CoordBlock.blowupResolution}) are the formal route; their applicability to these two phases is to be checked.

\subsection{Tier 3: regular models}

$K=x^2$ on $[-1,1]$, and $K=|w|^2$, are the sanity examples. The population expansion is the Laplace expansion, with coefficient $\Gamma(\tfrac{2j+1}2)\eta^{(2j)}(0)/(2j)!$ at $N^{-(2j+1)/2}$ and the odd terms cancelling between the two sides; the empirical coefficients are $\partial^j[\eta S_{\mu_j}(\zeta)](0)/j!$ with all fluctuation functions on the regular orbit; the leading posterior is the point mass at the origin, unmoved by the data, and the first correction is where the field first appears, through $\zeta'(0)S_1(\zeta(0))$. The one-dimensional coordinate-free instance $\int_0^\rho P(x)e^{-Nx^2}dx$ and the regular orbit are formal.

\subsection{Tier 4: stretch}

The leap model at $M\ge2$, $K=(\sum_jb_j\prod_ru_{j,r})^2$, has $\lambda=\tfrac12$ because $K=\alpha^2$ with $\alpha$ a polynomial whose zero set is a smooth hypersurface off its singular locus; off that locus the model is regular in the normal direction to $\{\alpha=0\}$ and the expansion is the one-dimensional regular expansion fibred over the hypersurface, but the singular locus, where several products vanish, needs a genuine resolution. The two-leaf naive Bayes model (the smallest Markov tree) was listed here as a stretch and turned out to be complete: pushed forward along the moment map its fibre volume is an explicit quadratic in $\log|\mu|$ (\cref{sec:nb}). The TMS $k$-gon at $k=3,4$ sits on a one-parameter critical family; if the loss is Morse--Bott along the family the expansion is the Laplace expansion in the normal directions integrated along the family, with $\lambda=(\dim-1)/2$ and no logarithm, which would be a clean instance of a positive-dimensional leading measure on a regular family. General DLNs, NMF at rank above one and general Markov trees stop at the leading pair.

\subsection{Recommended order}

Develop the examples in the order DLN (with the crossing $x^2y^2$ as its $L=2$ case and the triple crossing as $L=3$), then the mixed exponents $x^2y^6$, then rank-one matrix factorisation unconstrained and nonnegative, then the blow-up examples $x^2(x^2+y^2)$ and $y^2(x^2+y^2)$, then the regular sanity example; the stretch examples only if the first five leave the machinery wanting. Each example gets the same five headings: geometry, polar data and population coefficients, leading measures and the posterior at leading order, the frozen field, and the exact check.

\section{Monomial phases: the deep linear network with zero target}\label{sec:dln}

This section is deliberately short: for a monomial phase the resolution is the identity and every ingredient of the paper is a finite computation, so the value of the example lies in two exact identities that pin the whole expansion, one for the flat prior and one for the Gaussian prior, and in the reduction of the sample to a one-dimensional polar distribution.

\subsection{The model and the two exact identities}

The one-neuron-per-layer deep linear network $w\mapsto w_1w_2\cdots w_L$ with zero target and unit Gaussian noise has $K(w)=\tfrac12(w_1\cdots w_L)^2$: the walls are the $L$ coordinate hyperplanes with $(k_i,h_i)=(1,0)$, all of ratio $\tfrac12$, so $(\lambda,m)=(\tfrac12,L)$, the leading stratum is the origin and the leading measure is a point mass, and the depth-$c$ strata are the coordinate subspaces of codimension $c$. Everything is governed by the distribution of the single scalar $t=w_1\cdots w_L$ under the prior, since $K=t^2/2$ and the regression field couples to $t$ as well: $K_n(w)=\tfrac12t^2-n^{-1/2}\xi_n\,t$ exactly, with $\xi_n\sim N(0,1)$ as at the cone (\cref{sec:cone}). Two exact identities give this distribution.

\paragraph{The flat prior.} On $[-1,1]^L$ the volume function is a square root times a polynomial in the logarithm,
\begin{equation}\label{eq:dln_volume}
\operatorname{vol}\{w\in[-1,1]^L:(w_1\cdots w_L)^2<\varepsilon\}=2^L\sqrt\varepsilon\sum_{j<L}\frac{(-\tfrac12\log\varepsilon)^j}{j!}\qquad(0<\varepsilon\le1),
\end{equation}
a theorem of the qd seabed (\texttt{Qd.volume\_firstOctantL\_closed\_form}); its $\varepsilon$-derivative is $2^{L-1}\varepsilon^{-1/2}(-\tfrac12\log\varepsilon)^{L-1}/(L-1)!$, the law of $t^2$ under the prior, so the polar distribution of the model is exactly of the leading type $\varepsilon^{-1/2}\times(\log)^{L-1}$ with no lower terms at all, and its Laplace transform is
\begin{equation}\label{eq:dln_flat}
\Zcal_N[1]=\frac{2^{L-1}}{(L-1)!}\int_0^1e^{-N\varepsilon/2}\varepsilon^{-1/2}\Big(-\frac{\log\varepsilon}2\Big)^{L-1}d\varepsilon
=\frac{\sqrt{2\pi}}{(L-1)!}\,N^{-1/2}\,Q_{L-1}(\log N-\log2)+O(e^{-N/2}),
\end{equation}
where, with $\psi^{(j)}=\psi^{(j)}(\tfrac12)$ the polygamma values at one half,
\[
Q_{L-1}(t)=\sum_{j<L}\binom{L-1}j t^{L-1-j}(-1)^j\frac{\Gamma^{(j)}(\tfrac12)}{\Gamma(\tfrac12)},\qquad Q_1(t)=t-\psi,\quad Q_2(t)=(t-\psi)^2+\tfrac{\pi^2}2,\quad Q_3(t)=(t-\psi)^3+\tfrac{3\pi^2}2(t-\psi)+14\zeta(3),
\]
$\psi(\tfrac12)=-\gamma-2\log2$, $\psi'(\tfrac12)=\pi^2/2$, $\psi''(\tfrac12)=-14\zeta(3)$. The expansion is \emph{exact up to exponentially small terms}: a single pole of order $L$ at $\tfrac12$ and nothing else, the cleanest instance of the paper's statement that the population coefficients at an exponent are the polar data there. In the language of the paper the $\log N$-polynomial is the depressed polynomial in $t=\log N+\kappa_L^{\rm flat}$ with $\kappa_L^{\rm flat}=\gamma+\log2$ (for $L=2$: $\Zcal_N[1]=\sqrt{2\pi}N^{-1/2}(\log N+\gamma+\log2)+R_N$ with $0\le R_N\le4e^{-N/2}/N$, a theorem, see below).

\paragraph{The Gaussian prior.} For the normalised Gaussian prior the zeta function is a product of Gamma functions,
\[
\int\prod_i|w_i|^{2z}\,\varphi(w)\,dw=\pi^{-L/2}\,2^{(L-1)z}\,\Gamma(z+\tfrac12)^L
\]
(\texttt{zeta\_mult\_pi} in watanabe-examples, at $\gamma=0$), with a pole of order $L$ at $z=-\tfrac12$ and further poles at the negative half-integers, and the Mellin inversion at the first pole gives
\begin{equation}\label{eq:dln_gauss}
\Zcal_N[1]=A_{L-1}\,N^{-1/2}\,P_{L-1}(\log N+\kappa_L)+O(N^{-3/2}\log^{L-1}N),\qquad A_{L-1}=\frac1{(L-1)!(2\pi)^{(L-1)/2}},\quad \kappa_L=(L+1)\log2-(L-1)\gamma,
\end{equation}
with the depressed polynomials $P_1(t)=t$, $P_2(t)=t^2+\pi^2$, $P_3(t)=t^3+\tfrac72\pi^2t+6\zeta(3)$, whose coefficients are again polygamma values at $\tfrac12$ but now assembled from the $L$-fold product $\Gamma(z+\tfrac12)^L$ rather than from a single $\Gamma$: compare $\pi^2$ against $\pi^2/2$ and $6\zeta(3)$ against $14\zeta(3)$ in the two priors. The absence of a $t^{L-2}$ term is the defining property of the shift $\kappa_L$, and \cref{sec:dln_numerics} tests it directly.

\paragraph{The mixed exponents $x^2y^6$.} The same reduction handles the mixed monomial: under Lebesgue measure on $[-1,1]^2$ the law of $t=xy^3$ has density $|t|^{-2/3}-1$ on $0<|t|<1$ (no logarithm: the two walls have different ratios $\tfrac16$ and $\tfrac12$ and do not tie), so
\begin{equation}\label{eq:mixed_flat}
\int_{[-1,1]^2}e^{-Nx^2y^6}\,dx\,dy=2\int_0^1e^{-Nt^2}(t^{-2/3}-1)\,dt=\Gamma(\tfrac16)N^{-1/6}-\sqrt\pi\,N^{-1/2}+R_N,\qquad 0\le R_N\le\frac{e^{-N}}N ,
\end{equation}
the two exponents $\tfrac16$ and $\tfrac12$ with simple poles, nothing in between, and an exponentially small remainder: the three tiers of the paper's mixed-exponent example collapse to two terms because the amplitude is constant, and the exact identity is again a theorem (\texttt{Grammar/MixedMonomialFlat.lean}, \texttt{lintegral\_square\_cube} for the density, \texttt{mixed\_flat\_allOrders} and \texttt{mixed\_flat\_remainder\_le} for the expansion; the script \texttt{mixed\_check.py} confirms the density by Monte Carlo and the identity to $10^{-15}$ for $N\ge100$).

\subsection{The sample and the observables}

Since the field couples to $t$, the frozen partition function is the one-dimensional integral $Z_N[1;\xi]=\int e^{-Nt^2/2+\sqrt N\xi t}\rho_L(t)\,dt$ against the law $\rho_L$ of the product, which for the flat prior on $[-1,1]^2$ is $\rho_2(t)=\tfrac12\log(1/|t|)$ on $|t|<1$ (the product-of-uniforms density of \cref{sec:nb}) and for the Gaussian prior is $K_0(|t|)/\pi$; in the standardised variable $t=z/\sqrt N$ the flat-prior integral is
\begin{equation}\label{eq:dln_frozen}
Z_N[1;\xi]=N^{-1/2}\Big[\tfrac14\sqrt{2\pi}\,e^{\xi^2/2}\log N-\tfrac12m_1(\xi)\Big]+O(e^{-cN}),\qquad m_1(\xi)=\int e^{-z^2/2+\xi z}\log|z|\,dz ,
\end{equation}
the tilt $e^{\xi^2/2}$ at the leading logarithm and the shifted logarithmic moment in the constant term, exactly as in the naive Bayes model; at the chart level these are the paper's regression coefficients $S_{1/2}(a)/4$ and $-\partial_\nu S_\nu(a)|_{1/2}/4$ for the crossing $x^2y^2$ with a constant field (\texttt{empCoeff\_xy\_sq\_one}, \texttt{empCoeff\_xy\_sq\_zero}), written with the one-sided fluctuation functions of the paper. The posterior mean of the output, $\E[w_1w_2\mid\xi]=\E[t\mid\xi]$, is $\xi/\sqrt N$ at leading order with a $1/\log N$ relative correction, the partially vanishing regime; $\E[w_1^2]$ under the population loses one logarithm, $\E[w_1^2]\sim c/(\log N+\kappa_2)$, the fully vanishing regime on the wall $w_1=0$; and $\E[K]\sim\tfrac1{2N}$ is regular.

\subsection{Numerical checks}\label{sec:dln_numerics}

The script \texttt{projects/grammar/experiments/monomial/dln\_check.py} evaluates $\Zcal_N[1]$ for the flat prior by the one-dimensional integral \eqref{eq:dln_flat} (and by Monte Carlo in $L$ dimensions at $N=10$), for the Gaussian prior by nested quadrature over the product densities, and the frozen-field integrals by quadrature.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}rrrr@{}}
\toprule
$N$ & $L=2$: ratio to \eqref{eq:dln_gauss} & $L=3$ & $L=4$ \\
\midrule
$10^2$ & 1.0025050 & 0.9984308 & 1.0011272 \\
$10^3$ & 1.0002500 & 0.9998492 & 1.0001033 \\
$10^4$ & 1.0000250 & 0.9999854 & 1.0000096 \\
$10^5$ & 1.0000025 & 0.9999986 & 1.0000009 \\
\bottomrule
\end{tabular}
\qquad
\begin{tabular}{@{}rrr@{}}
\toprule
$N$ & $\E[w_1w_2\mid\xi]\sqrt N$, $\xi=0.7$ & $\E[w_1^2](\log N+\kappa_2)$ \\
\midrule
$10^2$ & 0.48015 & 1.969418 \\
$10^3$ & 0.54568 & 1.995794 \\
$10^4$ & 0.58111 & 1.999464 \\
$10^5$ & 0.60331 & 1.999935 \\
$10^6$ & --- & 1.999992 \\
\bottomrule
\end{tabular}
\caption{Left: the Gaussian prior, $\Zcal_N[1]$ by quadrature against $A_{L-1}N^{-1/2}P_{L-1}(\log N+\kappa_L)$; the ratio approaches $1$ with $N(\text{ratio}-1)\to0.25,\,-0.14,\,0.09$ for $L=2,3,4$, the next pole. For $L=3$ the fit $\sqrt N\Zcal_N=aL^2+bL+c$ over $N\in[10^3,3\cdot10^5]$ gives $a=0.07953$ ($A_2=1/4\pi=0.07958$), $b/2a=1.626$ ($\kappa_3=1.618$) and $c/a=12.41$ ($\kappa_3^2+\pi^2=12.49$), the depressed form. For the flat prior the one-dimensional integral \eqref{eq:dln_flat} and the closed form agree to $10^{-13}$ for $N\ge100$ and $L=2,3,4$ (at $N=10$ the difference is the $e^{-N/2}$ tail, $7\cdot10^{-5}$ relative), and Monte Carlo in $L$ dimensions agrees at $N=10$. Right: the frozen field, $L=2$, flat prior; $\sqrt N\,Z_N[1;\xi]$ agrees with \eqref{eq:dln_frozen} to seven digits at every $N\ge100$ and $\xi\in\{0,0.7,-1.3\}$, the posterior mean of the output approaches $\xi$ with a $1/\log N$ correction (the prediction from the same one-dimensional integral matches to five digits), and under the Gaussian prior $\E[w_1^2](\log N+\kappa_2)\to2$: $\E[w_1^2]=2/(\log N+3\log2-\gamma)$ to all shown digits.}
\label{tab:dln_numerics}
\end{table}

\subsection{What is formal}

The volume identity \eqref{eq:dln_volume} is a theorem of the qd seabed and the zeta function of the Gaussian prior a theorem of watanabe-examples; the crossing $x^2y^2$ with constant data is the formal regression of the paper (\texttt{SquareExample}, \texttt{empCoeff\_xy\_sq\_one}, \texttt{empCoeff\_xy\_sq\_zero}). In the grammar library the $L=2$ flat-prior reduction is a corollary of the product-of-uniforms density of \cref{sec:nb}: \texttt{lintegral\_crossing\_flat} (\texttt{Grammar/CrossingFlatPrior.lean}) states that for every measurable $\Psi\ge0$, $\int_{[-1,1]^2}\Psi(w_1w_2)\,dw=\int_{-1}^1\Psi(t)\,2\log(1/|t|)\,dt$, so that $Z_N[1;\xi]$ and every insertion $Z_N[f(w_1w_2);\xi]$ are one-dimensional integrals against the polar distribution $2\log(1/|t|)$, field included. For $L=2$ the flat-prior expansion \eqref{eq:dln_flat} is itself a theorem, with the remainder explicit (\texttt{Grammar/CrossingFlatAllOrders.lean}, \texttt{crossing\_flat\_allOrders}, \texttt{crossing\_flat\_remainder\_le}): for every $N>0$,
\[
\int_{[-1,1]^2}e^{-N(w_1w_2)^2/2}\,dw=\sqrt{\frac{2\pi}N}\,(\log N+\gamma+\log2)+R_N,\qquad R_N=4\int_1^\infty e^{-Nt^2/2}\log t\,dt\in\Big[0,\frac{4e^{-N/2}}N\Big],
\]
the constant term coming from the Gaussian logarithmic moment $\int_0^\infty e^{-u^2/2}\log u\,du=-\tfrac14\sqrt{2\pi}\,(\gamma+\log2)$, which is Mathlib's $\Gamma'(\tfrac12)=-\sqrt\pi(\gamma+2\log2)$ read through the derivative of the Gamma integral. This is the complete expansion of a partition function, exponent, both polar coefficients and remainder, as a single formal statement. The frozen-field formula \eqref{eq:dln_frozen} is a theorem in the same form (\texttt{crossing\_flat\_field}, \texttt{Grammar/CrossingFlatField.lean}): for every $N>0$ and every constant field $\xi$, with the Lebesgue normalisation of the prior,
\[
\int_{[-1,1]^2}e^{-N(w_1w_2)^2/2+\sqrt N\xi w_1w_2}\,dw=\frac1{\sqrt N}\Big[\sqrt{2\pi}\,e^{\xi^2/2}\log N-2m_1(\xi)-\int_{|z|\ge\sqrt N}e^{-z^2/2+\xi z}(\log N-2\log|z|)\,dz\Big],
\]
the tilt on the leading logarithm, the shifted logarithmic moment $m_1(\xi)$ in the constant term, and an explicit Gaussian tail as the remainder; and the same for the numerator of the output observable, $\int w_1w_2\,e^{-N(w_1w_2)^2/2+\sqrt N\xi w_1w_2}\,dw=N^{-1}[\sqrt{2\pi}\,\xi e^{\xi^2/2}\log N-2m_1^{(1)}(\xi)-\text{tail}]$ with $m_1^{(1)}(\xi)=\int ze^{-z^2/2+\xi z}\log|z|\,dz$ (\texttt{crossing\_flat\_field\_mean}), so that $\E[w_1w_2\mid\xi]$ is an exact ratio of two such expressions, $N^{-1/2}(\xi+O(1/\log N))$: the partially vanishing regime as a theorem. The Laplace-transform evaluations for $L\ge3$ and \eqref{eq:dln_gauss} are derivations here, checked numerically.

\section{The cone: a linear network with a width-two hidden layer}\label{sec:cone}

\subsection{The model and its geometry}

Take the bilinear regression model with parameters $(a,b)\in\R^2\times\R^2$, output $q(a,b)=a\cdot b=a_1b_1+a_2b_2$, unit Gaussian noise, and the zero truth: $p(y\mid a,b)=N(y;\,a\cdot b,\,1)$ and $q(y)=N(y;0,1)$. This is a linear network $x\mapsto b\cdot(a\,x)$ with a width-two hidden layer, evaluated at $x=1$, fitting the zero function. The divergence and the empirical divergence are
\[
K(a,b)=\tfrac12\,q(a,b)^2,\qquad K_n(a,b)=\frac1n\sum_{i=1}^n\log\frac{q(y_i)}{p(y_i\mid a,b)}=\tfrac12q^2-q\,\bar y_n=\tfrac12q^2-n^{-1/2}\,q\,\xi_n,\qquad \xi_n=n^{-1/2}\sum_iy_i\sim N(0,1) .
\]
So the standard form holds exactly, with the signed-root field $\xi_n$ a \emph{constant} on parameter space, exactly Gaussian for every $n$, and the standardised field $\psi_n=\sqrt2\operatorname{sgn}(q)\,\xi_n$ of variance exactly $2$. The frozen theory with a constant field is the sample theory; the empirical diagonal and the Gaussian limit are the same statement; and the average over the sample is the average over one standard Gaussian. The prior is a smooth $\varphi$ on $\R^4$; the running choices are the Gaussian $\varphi=e^{-|w|^2/2}$, for which everything is closed, and a compactly supported smooth prior, for which the machinery applies verbatim.

After the orthogonal change of coordinates $u_1=(a_1+b_1)/\sqrt2$, $u_3=(a_1-b_1)/\sqrt2$, $u_2=(a_2+b_2)/\sqrt2$, $u_4=(a_2-b_2)/\sqrt2$,
\[
q=\tfrac12\big(u_1^2+u_2^2-u_3^2-u_4^2\big) ,
\]
a nondegenerate quadratic form of signature $(2,2)$. Its zero set $C=\{q=0\}$ is a three-dimensional quadric cone with an isolated singular point at the origin, and off the origin $\nabla q\ne0$, so $C\setminus\{0\}$ is a smooth hypersurface along which $K=\tfrac12q^2$ vanishes to order two with $q$ itself a normal coordinate. The vertex is where a resolution is needed.

\subsection{The resolution and the wall data}

Blow up the origin of $\R^4$. In the chart in which $u_1$ is the leading coordinate, $u=x\cdot(1,y,z,t)$ with $x\in\R$ and $(y,z,t)\in\R^3$,
\[
q=\tfrac12x^2\big(1+y^2-z^2-t^2\big),\qquad du_1\,du_2\,du_3\,du_4=|x|^3\,dx\,dy\,dz\,dt ,
\]
and the factor $1+y^2-z^2-t^2$ vanishes on a smooth hypersurface (a two-sheeted hyperboloid in the $(y,z,t)$-space, the strict transform of the cone), along which it has a nonvanishing gradient; taking $v=\tfrac12(1+y^2-z^2-t^2)$ as a coordinate in place of one of $y,z,t$ near the strict transform gives the normal-crossing form
\[
K=\tfrac12q^2=\tfrac12\,x^4v^2,\qquad \pi^*(du)=|x|^3\,g\,dx\,dv\,dz'\,dt' ,
\]
with $g$ a smooth positive unit. In the paper's notation the active coordinates are $(x,v)$ with wall data
\[
(k_x,h_x)=(2,3),\qquad (k_v,h_v)=(1,0) ,
\]
the coordinates along the strict transform being inert; the four blow-up charts (one per leading coordinate) are related by the obvious changes of variables and cover the blow-up, with overlaps of measure zero on the divisor. The exceptional divisor $E=\{x=0\}\cong\mathbb{RP}^3$ carries the ratio $(h_x+1)/2k_x=1$; the strict transform $\widetilde C=\{v=0\}$ carries the ratio $(h_v+1)/2k_v=\tfrac12$; they meet along the conic $E\cap\widetilde C$, a smooth quadric surface in $\mathbb{RP}^3$, the depth-two stratum. The zero fibre over the support of the prior is $\widetilde C\cup E$ (for a prior positive at the origin), the leading pair is
\[
(\lambda,m)=(\tfrac12,1) ,
\]
realised on $\widetilde C\setminus E$, and the candidate lattice is $Q^{-1}\N$ with $Q=2k_xk_v=4$. The candidate structure at the first exponents: at $\mu=\tfrac12$ only the $v$-wall resonates, at order $0$; at $\mu=1$ the $x$-wall resonates at order $0$ and the $v$-wall at order $1$, so the candidate pole order along the conic is two and a term $N^{-1}\log N$ is allowed by the candidate count; at $\mu=\tfrac32$ both walls resonate again at order $2$. None of the logarithms is realised, for a reason the paper's machinery locates exactly (\cref{prop:cone_leray}): the resonant $v$-derivatives are derivatives of functions pulled back from $\R^4$, which are constant along $E$.

\subsection{The chart polar data and the coupling average}

The chart integral of the blow-up chart with a constant amplitude on the unit box, in the paper's normalisation $e^{-Nu^{2k}}$, is
\[
Z_N(c;a)=c\int_0^1\!\!\int_0^1x^{3}\,e^{-Nx^4v^2+\sqrt N\,x^2v\,a}\,dx\,dv ,
\]
the flat prior in blow-up coordinates with a constant field $a$. The paper's machinery on this chart is formal in every step.

% Lean @ grammar main after 1a04563 (Grammar/ConeExample.lean, DLXXXII; Grammar/ConeGaussian.lean, DLXXXIII): Grammar/ConeExample.lean: Grammar.coneH, Grammar.coneK, Grammar.chartZeta_const_cone, Grammar.chartPolarCoeff_const_cone_half, Grammar.chartPolarCoeff_const_cone_one
\begin{prop}[Polar data of the cone chart]\label{prop:cone_polar}
For the constant amplitude $c$ and the data $h=(3,0)$, $k=(2,1)$,
\[
T_{h,k}(s)[c]=\int_{(0,1]^2}c\,x^{3-4s}v^{-2s}\,dx\,dv=\frac{c}{(4-4s)(1-2s)} ,
\]
with simple poles at $s=\tfrac12$ and $s=1$ and polar coefficients, in the $(\mu-s)^{-r}$ convention,
\[
A_{1/2,1}[c]=\frac c4,\qquad A_{1,1}[c]=-\frac c4,\qquad A_{1/2,2}=A_{1,2}=0 .
\]
\end{prop}

The residue at $\tfrac12$ is the $v$-wall's $\tfrac1{2k_v}=\tfrac12$ times the $x$-integral $\int_0^1x^{3-2}dx=\tfrac12$ evaluated at the pole; the residue at $1$ is the $x$-wall's $\tfrac1{2k_x}=\tfrac14$ times the finite part of the divergent tangential integral $\int_0^1v^{-2}dv$, which is $\mathrm{FP}\int_0^1v^{-2}dv=-1$: the vertex contributes with a \emph{negative} sign, the sign of a Hadamard finite part. The candidate double pole at $1$ has coefficient zero because the amplitude has no $v$-derivative.

% Lean @ grammar main after 1a04563 (Grammar/ConeExample.lean, DLXXXII; Grammar/ConeGaussian.lean, DLXXXIII): Grammar/ConeExample.lean: Grammar.couplingPolarCoeff_cone, Grammar.empCoeff_cone_half, Grammar.empCoeff_cone_one, Grammar.empCoeff_cone_one_log, Grammar.empCoeff_cone_zero_field
\begin{prop}[Frozen coefficients of the cone chart]\label{prop:cone_chart_coeffs}
With the constant field $a$, the coupling-average formula gives
\[
Z_N(1;a)=\frac{S_{1/2}(a)}4\,N^{-1/2}-\frac{S_1(a)}4\,N^{-1}+O\big(N^{-5/4}\big),\qquad c_{1,1}(1;a)=0 ,
\]
with $S_{1/2}(a)=\sqrt\pi e^{a^2/4}(1+\operatorname{erf}(a/2))$ and $S_1(a)=\tfrac a2S_{1/2}(a)+1$; at zero field the coefficients are $\sqrt\pi/4$ and $-\tfrac14$.
\end{prop}

The two coefficients are the two polar coefficients of \cref{prop:cone_polar} applied to the tilted amplitude $e^{a\sqrt t}$ under the coupling integral: $c_{1/2,0}=-\int_0^\infty t^{-1/2}e^{-t}C_{1/2,1}[e^{a\sqrt t}]\,dt=\tfrac14S_{1/2}(a)$ and $c_{1,0}=-\int_0^\infty e^{-t}C_{1,1}[e^{a\sqrt t}]\,dt=-\tfrac14S_1(a)$, with $C_{\mu,r}=(-1)^rA_{\mu,r}$; the logarithmic term at $1$ is the coupling average of the vanishing double-pole coefficient. The next candidate exponent on the lattice is $\tfrac54$, from the $x$-wall at order one, and it is realised for a constant amplitude: the expansion continues in steps of $\tfrac14$.

\subsection{The Leray density and the complete population expansion}

Globally, and for a general smooth prior and observable, the whole expansion is read off one function of one variable. For $F$ smooth on $\R^4$ define the Leray density of $q$,
\[
\mathcal L_F(v)=\int_{\{q=v\}}F\,\frac{du}{dq}=\int_{\R^4}\delta(q(u)-v)\,F(u)\,du ,
\]
so that $\int_{\R^4}F\,e^{-Nq^2/2+\sqrt N\,q\,a}\,du=\int_\R e^{-Nv^2/2+\sqrt N\,v\,a}\,\mathcal L_F(v)\,dv$. In the bipolar coordinates $u_1+iu_2=re^{i\theta}$, $u_3+iu_4=se^{i\psi}$, with $p=r^2$ and $t=s^2$, $q=\tfrac12(p-t)$ and $du=\tfrac14dp\,dt\,d\theta\,d\psi$, so with $\bar F(p,t)$ the average of $F$ over the two circles,
\begin{equation}\label{eq:cone_leray}
\mathcal L_F(v)=\pi^2\int_0^\infty\!\!\int_0^\infty\delta\big(\tfrac{p-t}2-v\big)\bar F(p,t)\,dp\,dt=2\pi^2\int_{\max(0,2v)}^\infty\bar F(p,\,p-2v)\,dp .
\end{equation}

% Lean: the decomposition below is a derivation from eq:cone_leray; the smoothness of the circle averages in (p, t) is the standard fact that an even smooth function of r is smooth in r^2.
\begin{prop}[The Leray density of a signature $(2,2)$ form]\label{prop:cone_leray}
For $F$ smooth and integrable with its derivatives against the Leray form, $\mathcal L_F$ is piecewise smooth with a corner at $0$: $\mathcal L_F(v)=A_F(v)+B_F(v)|v|$ with $A_F$, $B_F$ smooth, and
\[
A_F(0)=\mathcal L_F(0)=\int_CF\,\frac{du}{dq},\qquad B_F(0)=\tfrac12\big(\mathcal L_F'(0^+)-\mathcal L_F'(0^-)\big)=-2\pi^2F(0) .
\]
In particular $\mathcal L_F$ has no logarithmic singularity at $0$, and the corner is proportional to the value of $F$ at the vertex.
\end{prop}

\begin{proof}
For $v>0$ the right side of \eqref{eq:cone_leray} is $2\pi^2\int_{2v}^\infty\bar F(p,p-2v)\,dp$ and for $v<0$ it is $2\pi^2\int_0^\infty\bar F(p,p-2v)\,dp$; $\bar F$ is smooth in $(p,t)$ on the closed quadrant because the circle average of a smooth function of $(u_1,u_2)$ is a smooth even function of $r$, hence a smooth function of $r^2$. Each one-sided expression extends smoothly across $v=0$, so $\mathcal L_F=G_+$ on $v\ge0$ and $G_-$ on $v\le0$ with $G_\pm$ smooth, $G_+(0)=G_-(0)$, and $A=\tfrac12(G_++G_-)$, $B=\tfrac12(G_+-G_-)/v$ are smooth. Differentiating, $G_+'(0)=2\pi^2\big(-2\bar F(0,0)-2\int_0^\infty\partial_2\bar F(p,p)\,dp\big)$ and $G_-'(0)=2\pi^2\big(-2\int_0^\infty\partial_2\bar F(p,p)\,dp\big)$, so the jump is $-4\pi^2\bar F(0,0)=-4\pi^2F(0)$.
\end{proof}

\begin{thm}[The complete population expansion of the cone model]\label{thm:cone_population}
For $\varphi$ and $f$ smooth with $F=f\varphi$ as above, writing $A_F(v)=\sum_ia_iv^i$ and $B_F(v)=\sum_ib_iv^i$ at $v=0$,
\begin{equation}\label{eq:cone_population}
\Zcal_N[f]\sim\sum_{j\ge0}\sqrt{2\pi}\,(2j-1)!!\,a_{2j}\,N^{-j-1/2}+\sum_{j\ge0}2^{j+1}j!\,b_{2j}\,N^{-j-1} ,
\end{equation}
an expansion on the lattice $\tfrac12\N$ with no logarithms. The exponents $j+\tfrac12$ are carried by the cone and their coefficients are the even normal moments of $F$ along it; the exponents $j+1$ are carried by the vertex, with
\[
c_{1,0}(f)=2b_0=-4\pi^2\,(f\varphi)(0) .
\]
\end{thm}

\begin{proof}
Insert $\mathcal L_F=A_F+B_F|v|$ into $\int e^{-Nv^2/2}\mathcal L_F(v)\,dv$ and use $\int_\R v^{2j}e^{-Nv^2/2}dv=\sqrt{2\pi}(2j-1)!!N^{-j-1/2}$, $\int_\R|v|^{2j+1}e^{-Nv^2/2}dv=2^{j+1}j!\,N^{-j-1}$, and the vanishing of the odd moments; the Taylor remainders of $A_F$ and $B_F$ contribute at the next order. Cutting the integral to $|v|\le\varepsilon$ costs $O(e^{-N\varepsilon^2/2})$.
\end{proof}

In the language of the paper: the Gamma-free zeta distribution pairs with $F$ as $\langle T(s),F\rangle=\int|q|^{-2s}F=\int|v|^{-2s}\mathcal L_F(v)\,dv$ (with the model's $K=q^2/2$ the Mellin variable is scaled by $2^{s}$, which we suppress), whose poles are simple, at $s=j+\tfrac12$ with residue data $a_{2j}$ from the even part of $A_F$ and at $s=j+1$ with residue data $b_{2j}$ from $B_F|v|$: $A_{1/2,1}[F]=\mathcal L_F(0)$ and $A_{1,1}[F]=b_0$. The candidate double poles at the integers and half-integers $\ge1$ are not realised because the two one-sided densities $G_\pm$ are smooth; in chart terms, the resonant $v$-derivatives at the conic are derivatives along $E$ of functions pulled back from $\R^4$, which vanish. The population leading measure is
\[
\nu^{1/2}_1=\sqrt{2\pi}\;\varphi\,\delta(q)\,du ,\qquad \int f\,d\nu^{1/2}_1=\sqrt{2\pi}\,\mathcal L_{f\varphi}(0) ,
\]
the Gelfand--Leray measure of the cone weighted by the prior: a finite measure on all of $\R^4$ giving the vertex measure zero, as in the paper's global leading-measure theorem, with the factor $\sqrt{2\pi}=\Gamma(\tfrac12)\sqrt2$ the radial constant of $e^{-Nv^2/2}$. The vertex is the exceptional divisor's leading measure at exponent $1$: a point mass at the origin of mass $-4\pi^2\varphi(0)$, negative, the finite part of the tangential integral across the conic.

\begin{cor}[The Gaussian prior]\label{cor:cone_gaussian}
For $\varphi=e^{-|u|^2/2}$, $\mathcal L_\varphi(v)=2\pi^2e^{-|v|}$ exactly, so
\[
\Zcal_N[1]=2\pi^2\int_\R e^{-Nv^2/2-|v|}\,dv=2\pi^2\sqrt{\tfrac{2\pi}N}\,e^{1/2N}\operatorname{erfc}\Big(\frac1{\sqrt{2N}}\Big)\sim2\pi^2\sum_{j\ge0}\frac{(-1)^j}{j!}\,m_j\,N^{-(j+1)/2},\qquad m_j=\int_\R|t|^je^{-t^2/2}dt ,
\]
that is $\Zcal_N[1]=2\pi^2\big[\sqrt{2\pi}N^{-1/2}-2N^{-1}+\tfrac{\sqrt{2\pi}}2N^{-3/2}-\tfrac23N^{-2}+\cdots\big]$. For $f=u_1^2$, $\mathcal L_{f\varphi}(v)=\pi^2e^{-|v|}(1+v+|v|)$, so $\Zcal_N[u_1^2]=\pi^2\int e^{-Nv^2/2-|v|}(1+|v|)\,dv$ has no $N^{-1}$ term, and
\[
\E_\infty[u_1^2]=\frac{\Zcal_N[u_1^2]}{\Zcal_N[1]}=\frac12+\frac1{\sqrt{2\pi}}N^{-1/2}+O(N^{-1}) .
\]
\end{cor}

The population posterior at leading order is the prior-weighted Leray measure on the cone, $\langle u_1^2\rangle_C=\tfrac12$; the vertex enters the expectation at order $N^{-1/2}$, with the universal shape
\[
\E_\infty[f]=\langle f\rangle_C+\frac{4\pi^2\varphi(0)}{\sqrt{2\pi}\,\mathcal L_\varphi(0)}\big(\langle f\rangle_C-f(0)\big)N^{-1/2}+O(N^{-1}) ,
\]
which \emph{repels} the expectation from its value at the singular point, because the vertex mass is negative. This is the first correction of the paper's leading posterior theorem for an observable that does not vanish near the deep stratum, and it is not an admissibility artefact: $f=u_1^2$ vanishes at the vertex and still sees it, through the denominator.

\subsection{The sample}

With the field the Leray reduction reads $Z_N[f;a]=\int_\R e^{-Nv^2/2+\sqrt N\,v\,a}\,\mathcal L_{f\varphi}(v)\,dv$, and the tilt $e^{\sqrt Nva}$ is odd in $v$: the odd Taylor coefficients of $A_F$ and $B_F$, invisible at zero field, are restored. With $t=\sqrt Nv$ and the tilted absolute moments $m_j(a)=\int_\R|t|^je^{-t^2/2+at}dt$, $m_j^\pm(a)=\int_\R t^{j}e^{-t^2/2+at}dt$,
\begin{equation}\label{eq:cone_frozen}
Z_N[f;a]\sim\sum_{i\ge0}a_i\,m^\pm_i(a)\,N^{-(i+1)/2}+\sum_{i\ge0}b_i\,m_{i+1}(a)\,N^{-(i+2)/2} ,
\end{equation}
every coefficient a tilted Gaussian moment of the jets of the two Leray functions at the vertex. The tilted moments are the fluctuation functions of the paper at the standardised field $\sqrt2a$: $\int_0^\infty t^ie^{-t^2/2+at}dt=2^{(i-1)/2}S_{(i+1)/2}(\sqrt2a)$, and the two half-lines carry $\pm\sqrt2a$, the two branch traces of the signed root on the two sides of the cone. The leading coefficient is $\mathcal L_{f\varphi}(0)\,[S_{1/2}(\sqrt2a)+S_{1/2}(-\sqrt2a)]/\sqrt2=\sqrt{2\pi}\,e^{a^2/2}\mathcal L_{f\varphi}(0)$: the tilted leading measure is the population one times $e^{a^2/2}$, a constant, so the leading posterior does not move with the data, as the paper's leading posterior theorem says for a field constant on the support of the leading measure. The data enter at the next order, through three terms: the vertex $b_0m_1(a)$, the odd cone term $a_1m_1^\pm(a)$, and nothing else. For the Gaussian prior and $f=u_1^2$ (where $a_1=\pi^2$, $b_0=0$ for the numerator and $a_1=0$, $b_0=-2\pi^2$ for the denominator),
\begin{equation}\label{eq:cone_posterior_field}
\E[u_1^2\mid\xi_n=a]=\frac12+\frac12\Big(a+\frac{m_1(a)}{m_0(a)}\Big)N^{-1/2}+O(N^{-1}),\qquad \frac{m_1(a)}{m_0(a)}=\frac{2e^{-a^2/2}}{\sqrt{2\pi}}+a\operatorname{erf}\Big(\frac a{\sqrt2}\Big) ,
\end{equation}
the first term of the correction being the restored odd part of the cone density and the second the vertex, each an explicit function of the single Gaussian $\xi_n$. The chart coefficients of \cref{prop:cone_chart_coeffs} are the same two mechanisms on the unit box with the flat prior in blow-up coordinates.

\paragraph{The average over the sample.} Since $\E\,e^{\sqrt N\,q\,\xi}=e^{Nq^2/2}$ for $\xi\sim N(0,1)$, the averaged evidence is exactly the prior mass, $\E_\xi Z_N[1;\xi]=\int\varphi\,du=(2\pi)^2$ for the Gaussian prior, for every $N$; but the leading coefficient $2\pi^2\sqrt{2\pi}e^{\xi^2/2}N^{-1/2}$ is not integrable against the law of $\xi$, the standardised field having variance exactly $2$. The average is carried by fields of size $|\xi|\sim\sqrt N$: truncating to $|\xi|<A$ gives $\E_\xi[Z_N[1;\xi]\mathbf 1_{|\xi|<A}]=2\pi^2\int_\R e^{-|v|}\big[\Phi(A-\sqrt Nv)-\Phi(-A-\sqrt Nv)\big]dv\to0$ as $N\to\infty$ for every fixed $A$. The posterior ratios are unaffected: \eqref{eq:cone_posterior_field} is bounded and its average over $\xi$ converges to $\tfrac12$ with the correction $\tfrac12\E[\xi+m_1(\xi)/m_0(\xi)]N^{-1/2}=\tfrac12\E[m_1(\xi)/m_0(\xi)]N^{-1/2}$.

\subsection{Numerical checks}\label{sec:cone_numerics}

The script \texttt{projects/grammar/experiments/cone/cone\_check.py} samples $u\sim N(0,I_4)$ and estimates $Z_N[f;a]=(2\pi)^2\,\E\big[f(u)\,e^{-Nq(u)^2/2+\sqrt N\,q(u)\,a}\big]$ by Monte Carlo (five batches of $4\cdot10^6$), against the one-dimensional Leray reduction and the expansion \eqref{eq:cone_population}--\eqref{eq:cone_frozen}.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}rrrrrr@{}}
\toprule
$N$ & MC & 1D exact & 1 term & 2 terms & 4 terms \\
\midrule
\multicolumn{6}{@{}l}{$Z_N[1]$, zero field}\\
10 & $12.3657\pm0.0022$ & 12.3667 & 15.6466 & 11.6987 & 12.3495 \\
100 & $4.5778\pm0.0015$ & 4.5766 & 4.9479 & 4.5531 & 4.5765 \\
1000 & $1.5233\pm0.0020$ & 1.5260 & 1.5647 & 1.5252 & 1.5260 \\
\multicolumn{6}{@{}l}{$Z_N[1;a]$, field $a=1$}\\
10 & $18.3831\pm0.0081$ & 18.3828 & 25.7969 & 16.2799 & 18.2909 \\
100 & $7.2819\pm0.0020$ & 7.2822 & 8.1577 & 7.2060 & 7.2819 \\
1000 & $2.4855\pm0.0025$ & 2.4870 & 2.5797 & 2.4845 & 2.4870 \\
\bottomrule
\end{tabular}
\qquad
\begin{tabular}{@{}rrr@{}}
\toprule
$N$ & $\E[u_1^2\mid a]$ MC & prediction \\
\midrule
\multicolumn{3}{@{}l}{$a=0$: slope $0.3989$}\\
100 & 0.5379 & 0.5399 \\
300 & 0.5227 & 0.5230 \\
1000 & 0.5129 & 0.5126 \\
\multicolumn{3}{@{}l}{$a=1$: slope $1.0833$}\\
100 & 0.6022 & 0.6083 \\
1000 & 0.5347 & 0.5343 \\
\multicolumn{3}{@{}l}{$a=2$: slope $2.0085$}\\
100 & 0.6910 & 0.7009 \\
1000 & 0.5653 & 0.5635 \\
\bottomrule
\end{tabular}
\caption{Left: the evidence of the cone model with the Gaussian prior against the Leray reduction and the truncated expansion of \cref{cor:cone_gaussian} (the two-term column includes the vertex). Right: the posterior expectation of $u_1^2$ at a frozen field against \eqref{eq:cone_posterior_field}; the residual is the $O(N^{-1})$ term, which the numbers at $N=100$ resolve.}
\label{tab:cone_numerics}
\end{table}

The averaged evidence checks the critical variance: with the field truncated to $|\xi|<1$ the exact truncated average is $9.53$, $3.61$, $1.21$ at $N=10,100,1000$ (Monte Carlo over $150$ fields: $9.54$, $3.67$, $1.22$), and with $|\xi|<3$ it is $23.4$, $10.1$, $3.56$ ($21.5$, $9.45$, $3.68$), against the exact untruncated value $(2\pi)^2=39.48$ at every $N$: the average is carried by fields the truncation removes, more so as $N$ grows.

\subsection{What is formal}

The chart polar data and the frozen chart coefficients (\cref{prop:cone_polar,prop:cone_chart_coeffs}) are theorems of the grammar library (\texttt{Grammar/ConeExample.lean}), obtained from the chart zeta functional of the blow-up chart through the paper's determination lemmas and the coupling-average formula, exactly as for the $x^2y^2$ regression. The Gaussian Leray density is a theorem as well (\texttt{Grammar/ConeGaussian.lean}): the pushforward of $e^{-|u|^2/2}du$ along $q$ is $2\pi^2e^{-|v|}dv$ (\texttt{map\_coneQ\_gaussian}), proved by bipolar coordinates and Tonelli with lower integrals and no integrability hypotheses, so that $\int_{\R^4}g(q(u))e^{-|u|^2/2}du=\int_\R g(v)\,2\pi^2e^{-|v|}dv$ for every measurable $g$ (\texttt{integral\_cone\_gaussian}) and in particular the frozen evidence with a constant field is the one-dimensional integral of \cref{cor:cone_gaussian} (\texttt{cone\_evidence\_eq}). For the Gaussian prior the frozen partition function is moreover in closed form (\texttt{Grammar/ConeClosedForm.lean}, \texttt{cone\_evidence\_closed}): for every $N>0$ and every constant field $a$, with the Gaussian tail $T(c)=\int_c^\infty e^{-s^2/2}ds$,
\[
Z_N[1;a]=\frac{2\pi^2}{\sqrt N}\Big[e^{(a-1/\sqrt N)^2/2}\,T\Big(\tfrac1{\sqrt N}-a\Big)+e^{(a+1/\sqrt N)^2/2}\,T\Big(\tfrac1{\sqrt N}+a\Big)\Big],
\]
by completing the square on each half-line of the Leray integral; every coefficient of the expansion in $N^{-1/2}$ is a Taylor coefficient of this expression, and at $a=0$ it reads $4\pi^2N^{-1/2}e^{1/(2N)}T(1/\sqrt N)=4\pi^2N^{-1/2}[\sqrt{\pi/2}-N^{-1/2}+\tfrac12\sqrt{\pi/2}\,N^{-1}-\cdots]$, the vertex term $-4\pi^2N^{-1}$ in its place (the script \texttt{cone\_closed\_check.py} confirms the closed form against quadrature to $10^{-16}$ and the three-term expansion). The Leray decomposition for a general prior (\cref{prop:cone_leray}), the global expansion \eqref{eq:cone_population}, the identification of the vertex mass, and the sample formulas are derivations in this note, checked numerically.
\section{The blow-up example: a two-output network and the oriented blow-up}\label{sec:blowup}

\subsection{The model and its geometry}

Take the model with two outputs $(x^2,\,xy)$ on the parameter $(x,y)\in\R^2$, unit Gaussian noise, and the zero truth: $p(y_1,y_2\mid x,y)=N\big((y_1,y_2);(x^2,xy),I_2\big)$ and $q=N(0,I_2)$. The divergence is
\[
K(x,y)=\tfrac12\big(x^4+x^2y^2\big)=\tfrac12\,x^2(x^2+y^2) ,
\]
the paper's blow-up example up to the factor $\tfrac12$, and the empirical divergence is $K_n=K-n^{-1/2}(x^2\xi_1+xy\,\xi_2)$ with $(\xi_1,\xi_2)=n^{-1/2}\sum_i(y_{i1},y_{i2})\sim N(0,I_2)$ exactly, so the field is again a constant Gaussian vector and the frozen theory is the sample theory. The standardised field is $\psi=\sqrt2\operatorname{sgn}(x)(x\xi_1+y\xi_2)/\sqrt{x^2+y^2}$, of variance $2$. The zero set is the line $\{x=0\}$, along which $K$ vanishes to order two except at the origin, where it vanishes to order four, and the origin is the singular point.

The paper's resolution is one blow-up of the origin. In the chart $y=u$, $x=uv$,
\[
K=\tfrac12u^4v^2(1+v^2),\qquad dx\,dy=|u|\,du\,dv ,
\]
so the exceptional curve $E_0=\{u=0\}$ carries $(k,h)=(2,1)$ and the strict transform $E_1=\{v=0\}$ of the line carries $(1,0)$; both have ratio $\tfrac12$, the leading pair is $(\lambda,m)=(\tfrac12,2)$, the leading stratum is the single point $E_0\cap E_1$, and the candidate lattice is $\tfrac14\N$ ($Q=2k_uk_v=4$). The unit $1+v^2$ is absorbed into $u$ near the crossing. Candidate resonances: $E_0$ at $(\alpha+2)/4$, $E_1$ at $(\alpha+1)/2$, so both walls resonate at every half-integer $\tfrac12+j$ (orders $(2j,\,2j)$, both even, both surviving parity), with candidate order two, and $E_0$ alone at the quarter-integers $\tfrac34+j$ with odd order, which parity removes. The expansion is therefore on $\tfrac12\N$ with a logarithm allowed at every half-integer, the exact opposite of the cone: there the candidate logarithms were all killed, here they are all realised.

\subsection{Polar coordinates are the oriented blow-up}

The polar coordinates $x=r\cos\theta$, $y=r\sin\theta$ give
\[
K=\tfrac12r^4\cos^2\theta,\qquad dx\,dy=r\,dr\,d\theta=\tfrac12\,ds\,d\theta\ \ (s=r^2) ,
\]
a normal-crossing form on the half-cylinder $\{s\ge0\}\times S^1$: the wall $s=0$ is the circle of directions, the oriented blow-up of the origin, which double covers the exceptional $\mathbb{RP}^1$ and separates the two sides of every direction; the walls $\cos\theta=0$ are the two points $\theta=\pm\tfrac\pi2$ of the circle, the two rays of the line $x=0$. Near $\theta=\tfrac\pi2$ put $w=\cos\theta$, so that $d\theta=-dw/\sqrt{1-w^2}$ and
\[
K=\tfrac12\,w^2s^2,\qquad dx\,dy=\tfrac12\,(1-w^2)^{-1/2}\,dw\,ds :
\]
the crossing $x^2y^2$ of the paper's running example, in the coordinates $(w,s)$ with $w$ two-sided, $s$ one-sided, Jacobian exponents $h=(0,0)$, and a smooth amplitude. The blow-up chart data $(2,1),(1,0)$ and the polar data $(1,0),(1,0)$ describe the same geometry because $s=r^2=u^2(1+v^2)$: the polar wall coordinate $s$ is the square of the blow-up wall coordinate $u$, which halves $k$ and $h+1$ together and leaves the ratio unchanged. This is the paper's oriented blow-up in its simplest instance, and it turns the example into $x^2y^2$ with a nonconstant amplitude, so that every coefficient statement of \cref{sec:candidates} for the crossing applies: in particular the leading logarithm is carried by the two points $\theta=\pm\tfrac\pi2$ of the circle, each with two sides in $w$.

\subsection{The zeta function and the complete population expansion}

For the Gaussian prior $\varphi=e^{-|w|^2/2}$ the zeta function factorises in polar coordinates into a radial Gamma integral and an angular Beta integral,
\begin{equation}\label{eq:blowup_zeta}
\zeta_1(z)=\int_{\R^2}K^z\,e^{-|w|^2/2}\,dw=2^{z}\,\Gamma(2z+1)\int_{-\pi}^{\pi}|\cos\theta|^{2z}\,d\theta=2^{z}\Gamma(2z+1)\cdot\frac{2\sqrt\pi\,\Gamma(z+\frac12)}{\Gamma(z+1)}=2^{3z+1}\,\Gamma\big(z+\tfrac12\big)^2 ,
\end{equation}
by the duplication formula. The two factors are the two walls: $\Gamma(2z+1)$ has its poles at $z=-\tfrac12,-1,-\tfrac32,\dots$, the candidate exponents of the radial wall $s=0$, and $\Gamma(z+\tfrac12)/\Gamma(z+1)$ has poles at $z=-\tfrac12,-\tfrac32,\dots$ and zeros at $z=-1,-2,\dots$, the angular wall's candidates and the cancellation of the radial wall's integer candidates by the flat angular weight; the product has double poles exactly at the half-integers. With $\mathcal M\Zcal_1(s)=\Gamma(s)\zeta_1(-s)$ and the residue formula,
\begin{equation}\label{eq:blowup_population}
\Zcal_N[1]=\sum_{j\ge0}N^{-\frac12-j}\big(\alpha_j\log N-\beta_j\big),\qquad \frac{G_j(\varepsilon)}{\varepsilon^2}:=\Gamma\big(\tfrac12+j+\varepsilon\big)\,2^{-\frac12-3j-3\varepsilon}\,\Gamma(-j-\varepsilon)^2,\quad \alpha_j=G_j(0)=\frac{\Gamma(\frac12+j)}{2^{\frac12+3j}(j!)^2},\ \beta_j=G_j'(0) ,
\end{equation}
so that $c_{\frac12+j,1}=\alpha_j$ and $c_{\frac12+j,0}=-\beta_j$; explicitly
\[
c_{1/2,1}=\sqrt{\tfrac\pi2},\qquad c_{1/2,0}=\sqrt{\tfrac\pi2}\,\big(5\log2-\gamma_E\big),\qquad c_{3/2,1}=\frac{\sqrt{\pi/2}}{16},\qquad\dots
\]
with $\psi(\tfrac12)=-\gamma_E-2\log2$, and every coefficient a rational combination of $\sqrt\pi$, powers of $2$, $\gamma_E$ and polygamma values. For an observable, $\zeta_f$ has the same shape with the angular weight replaced by the angular average of $f\varphi$ and the radial exponent shifted by the order of $f$ at the origin. Two observables show the regimes of the paper:
\[
\zeta_{y^2}(z)=2^{z+1}\Gamma(2z+2)\Big[\frac{2\sqrt\pi\,\Gamma(z+\frac12)}{\Gamma(z+1)}-\frac{2\sqrt\pi\,\Gamma(z+\frac32)}{\Gamma(z+2)}\Big],\qquad \zeta_{x^2}(z)=2^{z+1}\Gamma(2z+2)\,\frac{2\sqrt\pi\,\Gamma(z+\frac32)}{\Gamma(z+2)} .
\]
The observable $y^2$ vanishes to order two at the origin and nowhere else on the line: it shifts the radial wall to ratio $1$ and leaves the angular wall at $\tfrac12$, so its first pole is simple, $\Zcal_N[y^2]\sim cN^{-1/2}$ with no logarithm, and $\E_\infty[y^2]\sim c'/\log N$, the partially vanishing regime. The observable $x^2$ vanishes on the whole line: both walls shift, the first pole is at $s=1$ from the radial wall alone, $\Zcal_N[x^2]\sim cN^{-1}$, and $\E_\infty[x^2]\sim c''N^{-1/2}/\log N$, the fully vanishing regime with the denominator's logarithm surviving in the rate.

In the paper's normalisation the leading logarithm is the top polar coefficient at the crossing: in the coordinates $(w,s')$ with $s'=s/\sqrt2$ (so that $NK=Ns'^2w^2$) the amplitude of the flat prior at the crossing is $\eta(0)=\tfrac12\cdot\sqrt2\cdot\varphi(0)=\varphi(0)/\sqrt2$, each of the two points carries two $w$-sides, and
\[
c_{1/2,1}(f)=\Gamma(\tfrac12)\cdot 2\cdot2\cdot\tfrac14\,\eta(0)\,f(0)=\sqrt{\tfrac\pi2}\,(f\varphi)(0) ,
\]
the point mass at the origin; for $f=1$ this is the $\alpha_0$ of \eqref{eq:blowup_population}. The constant term $c_{1/2,0}$ is the tie formula of the paper, $\Gamma(\tfrac12)A_{1/2,1}[\eta]-\Gamma'(\tfrac12)A_{1/2,2}[\eta]$, the finite parts of the amplitude along the two walls (the circle of directions and the two rays of the line) plus the Gamma derivative at the crossing; for the Gaussian prior the finite parts sum to the $5\log2$ and the Gamma derivative to the $-\gamma_E$.

\subsection{The sample}

In the polar chart the standardised field is $\psi=\sqrt2\operatorname{sgn}(x)(\cos\theta\,\xi_1+\sin\theta\,\xi_2)$, and near $\theta=\pm\tfrac\pi2$, with $w=\cos\theta$ and $\sin\theta=\pm\sqrt{1-w^2}$,
\[
\zeta_\pm(w,s)=\sqrt2\operatorname{sgn}(w)\big(w\,\xi_1\pm\sqrt{1-w^2}\,\xi_2\big) :
\]
the branch traces at the crossing are $\pm\sqrt2\,\xi_2$ on the two sides of each point, four branches in all, and $\xi_1$ multiplies the vanishing coordinate $w$. By the coupling-average formula the frozen leading logarithm is
\[
c_{1/2,1}(1;\xi)=\frac{\eta(0)}4\sum_{\text{branches}}S_{1/2}(\zeta_{\mathrm{br}})=\frac{\varphi(0)}{4\sqrt2}\cdot2\big[S_{1/2}(\sqrt2\xi_2)+S_{1/2}(-\sqrt2\xi_2)\big]=\sqrt{\tfrac\pi2}\,\varphi(0)\,e^{\xi_2^2/2} ,
\]
using $S_{1/2}(a)+S_{1/2}(-a)=2\sqrt\pi e^{a^2/4}$: the output direction $xy$ is seen at leading order through $e^{\xi_2^2/2}$, and the output direction $x^2$ is invisible there, entering only at the constant term through the ladder, via $\partial_w\zeta=\pm\sqrt2\xi_1$ and $S_1(\pm\sqrt2\xi_2)$. The leading posterior is the point mass at the origin whatever the data, and the data first move the posterior expectation at order $1/\log N$, through the constant term. The averaged evidence is again exactly the prior mass, $\E_\xi Z_N[1;\xi]=2\pi$, with the leading coefficient $\propto e^{\xi_2^2/2}$ integrable against $N(0,1)$ only marginally (the density $e^{-\xi_2^2/2}$ cancels it): the same critical variance as for the cone.

\subsection{Numerical checks}\label{sec:blowup_numerics}

The script \texttt{projects/grammar/experiments/blowup/blowup\_check.py} evaluates $\Zcal_N[f]$ by two-dimensional quadrature and the Laurent data of $\Gamma(s)\zeta_f(-s)$ by contour integration around each pole, for $f\in\{1,y^2,x^2\}$.

The Laurent data at $s=\tfrac12$ of $\Gamma(s)\zeta_1(-s)$ come out as $c_{-2}=1.253314137$ and $c_{-1}=-3.62022325$, against $\sqrt{\pi/2}=1.253314137$ and $-\sqrt{\pi/2}(5\log2-\gamma_E)=-3.62022325$.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}rrrrrr@{}}
\toprule
$N$ & $\Zcal_N[1]$ quad & one pole & two poles & three poles & rel.\ error \\
\midrule
10 & 2.0703281 & 2.0574049 & 2.0702637 & 2.0703279 & $1.1\cdot10^{-7}$ \\
100 & 0.9397821 & 0.9391948 & 0.9397818 & 0.9397821 & $1.1\cdot10^{-10}$ \\
1000 & 0.3882827 & 0.3882585 & 0.3882827 & 0.3882827 & $8.0\cdot10^{-14}$ \\
\midrule
$N$ & $\Zcal_N[y^2]$ quad & $s=\tfrac12$ & $+\,s=1$ & $+\,s=\tfrac32,2$ & rel.\ error \\
\midrule
10 & 1.3326919 & 1.5853309 & 1.2711717 & 1.3325151 & $1.3\cdot10^{-4}$ \\
100 & 0.4725718 & 0.5013257 & 0.4699097 & 0.4725710 & $1.7\cdot10^{-6}$ \\
1000 & 0.1554985 & 0.1585331 & 0.1553915 & 0.1554985 & $2.1\cdot10^{-8}$ \\
\midrule
$N$ & $\Zcal_N[x^2]$ quad & $s=1$ & $+\,s=\tfrac32$ & $+\,s=2,\tfrac52$ & rel.\ error \\
\midrule
10 & 0.2106429 & 0.3141593 & 0.2112890 & 0.2106461 & $1.5\cdot10^{-5}$ \\
100 & 0.0267170 & 0.0314159 & 0.0267200 & 0.0267170 & $5.4\cdot10^{-8}$ \\
1000 & 0.0029475 & 0.0031416 & 0.0029475 & 0.0029475 & $2.0\cdot10^{-10}$ \\
\bottomrule
\end{tabular}
\qquad
\begin{tabular}{@{}lrrr@{}}
\toprule
$(\xi_1,\xi_2)$ & fitted $a$ & $\sqrt{\pi/2}\,e^{\xi_2^2/2}$ & fitted $b$ \\
\midrule
$(0,0)$ & 1.2530 & 1.2533 & 3.62 \\
$(1,0)$ & 1.2515 & 1.2533 & 8.89 \\
$(2,0)$ & 1.2378 & 1.2533 & 29.95 \\
$(0,1)$ & 2.0673 & 2.0664 & 2.43 \\
$(0,1.5)$ & 3.8665 & 3.8605 & $-1.35$ \\
$(1,1)$ & 2.0647 & 2.0664 & 11.12 \\
\bottomrule
\end{tabular}
\caption{Left: the population expansion of the blow-up model with the Gaussian prior, by quadrature against the residue sums at the first one, two and all listed poles; the first pole of $y^2$ is simple (no logarithm), the first pole of $x^2$ is at $s=1$. Right: the frozen field. Least-squares fit of $\sqrt N\,Z_N[1;\xi]=a\log N+b+(c\log N+d)/\sqrt N$ over $N\in\{250,\dots,8000\}$: the logarithm's coefficient $a$ follows $e^{\xi_2^2/2}$ and ignores $\xi_1$, which enters the constant $b$ through the ladder.}
\label{tab:blowup_numerics}
\end{table}

The posterior expectations follow the regimes: $\E_\infty[y^2]$ is $0.503$, $0.400$, $0.363$ at $N=100,1000,3000$ against the leading-pole ratio $0.534$, $0.408$, $0.367$ (decaying like $1/\log N$), and $\E_\infty[x^2]$ is $0.0284$, $0.0076$, $0.0040$ against $0.0335$, $0.0081$, $0.0042$ (decaying like $N^{-1/2}/\log N$).

\subsection{What is formal}

The radial--angular factorisation of the zeta function against the Gaussian prior, $\int_{\R^2}K^we^{-|w|^2/2}=2^w\Gamma(2w+1)\int_{-\pi}^\pi|\cos\theta|^{2w}d\theta$ for $w>-\tfrac12$, is a theorem (\texttt{Grammar/BlowUpPolar.lean}, \texttt{lintegral\_blowK\_gauss}), with the Tonelli form of polar coordinates (\texttt{lintegral\_polar}) and the radial Gamma integral; the angular Beta integral $\int_{-\pi}^\pi|\cos\theta|^{2w}d\theta=2\sqrt\pi\,\Gamma(w+\tfrac12)/\Gamma(w+1)$ and hence the closed form \eqref{eq:blowup_zeta}, $\zeta(w)=2^{3w+1}\Gamma(w+\tfrac12)^2$ for $w>-\tfrac12$, are theorems as well (\texttt{Grammar/BlowUpZeta.lean}, \texttt{lintegral\_abs\_cos\_rpow}, \texttt{lintegral\_blowK\_gauss\_closed}): the angular integral is evaluated by the Gaussian trick, computing $\int_{\R^2}|x|^{2w}e^{-|z|^2/2}$ once as a product of one-dimensional Gamma integrals and once in polar coordinates, and the duplication formula turns $\Gamma(2w+1)\Gamma(w+\tfrac12)/\Gamma(w+1)$ into $2^{2w}\Gamma(w+\tfrac12)^2/\sqrt\pi$. At the chart level, the crossing $x^2y^2$ with a constant amplitude and a constant field is the formal regression of the paper's first section; the top polar coefficient $A_{1/2,2}[\eta]=\eta(0)/4$ for a smooth amplitude is the graded formula of the paper (\texttt{smoothCoeff\_eq\_faceSum\_top}, \texttt{faceMonoCoeff\_top}, with the deep set empty at depth two), and the tie formula for $A_{1/2,1}[\eta]$ with a nonconstant amplitude is an evaluation of the chart polar coefficient not yet written as a named theorem. The identification of the polar chart with the blow-up chart and the assembly over the two crossing points are derivations in this note.

\section{Rank-one matrix factorisation at a rank-one truth: a regular family}\label{sec:rankone}

\subsection{The model and its geometry}

Take $x\in\R^M$, $y\in\R^N$, the output $xy^{\mathsf T}$ with unit Gaussian noise on each entry, and a rank-one truth $A=ab^{\mathsf T}$ with $a\ne0$, $b\ne0$:
\[
K(x,y)=\tfrac12\,\|xy^{\mathsf T}-ab^{\mathsf T}\|_F^2,\qquad K_n=K-n^{-1/2}\langle xy^{\mathsf T}-ab^{\mathsf T},\Xi_n\rangle,\quad \Xi_n\sim N(0,I_{M\times N})\ \text{exactly} .
\]
The zero set is the gauge orbit $\gamma(t)=(ta,\,b/t)$, $t\in\R\setminus\{0\}$, a smooth curve with two components. At a point of the orbit the residual vanishes, so $K=\tfrac12\|D(\xi,\eta)\|^2+O(3)$ with the Gauss--Newton differential $D(\xi,\eta)=ta\,\eta^{\mathsf T}+\xi\,b^{\mathsf T}/t$, whose kernel is the tangent line of the orbit and whose image is the tangent space $T_A=\{a\eta^{\mathsf T}+\xi b^{\mathsf T}\}$ of the rank-one variety at $A$, of dimension $M+N-1$ and independent of $t$. So $K$ is Morse--Bott along the orbit: in normal coordinates $u\in\R^{M+N-1}$ it is a nondegenerate quadratic form, and in polar coordinates $u=\rho\omega$ it is $\rho^2$ times a positive function of $\omega$, a single wall $\rho=0$ with $(k,h)=(1,M+N-2)$ and no logarithm:
\[
(\lambda,m)=\Big(\frac{M+N-1}2,\,1\Big) ,
\]
the local RLCT of the nmf seabed (\texttt{nmf\_rank1\_true\_local\_rlct}). The candidate exponents are $\lambda+\tfrac j2$, and the odd $j$ are removed by the vanishing of the odd angular moments on the sphere of normal directions, so the expansion is in integer steps: $\Zcal_N[f]=N^{-\lambda}(c_0(f)+c_1(f)N^{-1}+\cdots)$. This is the paper's leading-measure theorem with a positive-dimensional exact stratum whose walls are regular in the normal directions: the leading measure is the orbit measure weighted by the prior and by the normal determinant, and the posterior at leading order is spread along the orbit.

\subsection{The exact reduction: one Gaussian integral per column}

Since $\|xy^{\mathsf T}-A\|_F^2=\sum_j\|y_jx-A_{\cdot j}\|^2$ over the columns, the exponent is a sum of one-variable quadratics in the $y_j$, and with the Gaussian prior $e^{-(|x|^2+|y|^2)/2}$ the $y$-integral is exact, field included:
\begin{equation}\label{eq:rankone_reduction}
\int_{\R^N}e^{-NK+\sqrt N\langle xy^{\mathsf T}-A,\Xi\rangle-|y|^2/2}\,dy=\prod_{j=1}^N\sqrt{\frac{2\pi}{N|x|^2+1}}\,\exp\Big(\frac{(N\langle x,A_{\cdot j}\rangle+\sqrt N\langle x,\Xi_{\cdot j}\rangle)^2}{2(N|x|^2+1)}-\frac N2|A_{\cdot j}|^2-\sqrt N\langle A_{\cdot j},\Xi_{\cdot j}\rangle\Big) ,
\end{equation}
leaving an $M$-dimensional integral over $x$. At zero field, with $A_{\cdot j}=b_ja$ and $\langle x,a\rangle=|x||a|\cos\psi$, the exponent sums to
\[
-\frac{N|a|^2|b|^2}2\Big(\sin^2\psi+\frac{\cos^2\psi}{N|x|^2+1}\Big)-\frac{|x|^2}2 ,
\]
so the effective phase in $x$ is $c\sin^2\psi/2$ with $c=|a|^2|b|^2$, vanishing on the line $x\parallel a$ (the two rays $\psi=0,\pi$ are the two components of the orbit), Morse in the angle, and the second term is the truth's own cut-off $e^{-c/(2|x|^2)}$ near $x=0$, where the orbit runs to infinity in $y$. Laplace's method in the angle, $\int_{S^{M-1}}e^{-(Nc/2)\sin^2\psi}d\omega\sim2\,(2\pi/Nc)^{(M-1)/2}$, and the radial integral give
\begin{equation}\label{eq:rankone_C}
\Zcal_N[1]\sim C\,N^{-(M+N-1)/2},\qquad C=2\,(2\pi)^{\frac{M+N-1}2}c^{-\frac{M-1}2}\int_0^\infty r^{M-1-N}e^{-r^2/2-c/(2r^2)}\,dr=2\,(2\pi)^{\frac{M+N-1}2}c^{-\frac{M-1}2}c^{\frac{M-N}4}K_{\frac{M-N}2}(\sqrt c) ,
\end{equation}
with $K_\nu$ the modified Bessel function, from $\int_0^\infty r^{\nu-1}e^{-(r^2+\beta^2/r^2)/2}dr=\beta^{\nu/2}K_{\nu/2}(\beta)$; for $M=N=2$, $C=4\pi\sqrt{2\pi/c}\,K_0(\sqrt c)$. The same constant is the leading-measure integral of the paper, $C=(2\pi)^\lambda\int_{\text{orbit}}\varphi(\gamma)\det{}'\!H(\gamma)^{-1/2}\,d\ell$ with $\det'H$ the product of the nonzero Hessian eigenvalues, and the two agree numerically to six digits (\cref{sec:rankone_numerics}). The orbit average of an observable against this measure is the leading posterior expectation; for $f=|x|^2$ it is $\sqrt c\,K_1(\sqrt c)/K_0(\sqrt c)$ when $M=N=2$, and for the gauge-invariant $f=\langle x,a\rangle\langle y,b\rangle$, constant equal to $c$ on the orbit, it is $c$.

\subsection{The sample}

The field is linear in $y$, so \eqref{eq:rankone_reduction} handles it exactly. At leading order the paper's tilted measure is the orbit measure weighted, at each orbit point, by the normal Gaussian integral with the linear term $\sqrt N\langle Du,\Xi\rangle$: since $H=D^{\mathsf T}D$ at a zero of the residual,
\[
\int e^{-Nu^{\mathsf T}Hu/2+\sqrt N\,u^{\mathsf T}D^{\mathsf T}\Xi}\,du=\Big(\frac{2\pi}N\Big)^{\lambda}\det{}'\!H^{-1/2}\,e^{\frac12\Xi^{\mathsf T}D(D^{\mathsf T}D)^{-1}D^{\mathsf T}\Xi}=\Big(\frac{2\pi}N\Big)^{\lambda}\det{}'\!H^{-1/2}\,e^{\|P\Xi\|^2/2} ,
\]
with $P$ the orthogonal projector onto the tangent space $T_A$, which does not depend on the point of the orbit. Hence
\[
Z_N[1;\Xi]\sim C\,e^{\|P\Xi\|^2/2}\,N^{-\lambda},\qquad \|P\Xi\|^2\sim\chi^2_{M+N-1} ,
\]
the fluctuation function of the regular case, $\int_{S^{M+N-2}}S_\lambda(\psi(\omega))\,d\omega$ with $\psi$ linear in the direction, integrated in closed form; the tilt is constant along the orbit, so the leading posterior is not moved by the data, exactly as at the cone and at the crossing, and the data first enter the posterior expectation at order $1/N$. The averaged evidence is again the prior mass, $\E_\Xi Z_N[1;\Xi]=(2\pi)^{(M+N)/2}$, while $\E\,e^{\|P\Xi\|^2/2}=\E e^{\chi^2_{M+N-1}/2}=\infty$: the standardised field has variance $2$ and the leading coefficient is not integrable, the critical case of the paper in a regular model.

\subsection{Numerical checks}\label{sec:rankone_numerics}

The script \texttt{projects/grammar/experiments/rankone/rankone\_check.py} takes $M=N=2$, $a=(1,\tfrac12)$, $b=(\tfrac45,-\tfrac35)$, so $c=\tfrac54$, integrates the $y$-variables in closed form and the $x$-variables by quadrature in polar coordinates around the direction of $a$, and computes the orbit integral of \eqref{eq:rankone_C} from the numerical Hessian along the orbit.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}rrr@{}}
\toprule
$N$ & $N^{3/2}\Zcal_N[1]$ & ratio to $C$ \\
\midrule
100 & 10.2012 & 1.0155 \\
400 & 10.0835 & 1.0038 \\
1600 & 10.0547 & 1.0009 \\
6400 & 10.0475 & 1.0002 \\
\bottomrule
\end{tabular}
\qquad
\begin{tabular}{@{}lrrrr@{}}
\toprule
$\Xi$ & $\|P\Xi\|^2$ & ratio at $N=400$ & at $6400$ & $e^{\|P\Xi\|^2/2}$ \\
\midrule
\#1 & 0.3005 & 1.1834 & 1.1665 & 1.1621 \\
\#2 & 0.2337 & 1.1176 & 1.1215 & 1.1239 \\
\#3 & 0.7427 & 1.4052 & 1.4376 & 1.4497 \\
\bottomrule
\end{tabular}
\caption{Left: the orbit integral gives $C=10.04514$, the Bessel closed form $4\pi\sqrt{2\pi/c}K_0(\sqrt c)$ gives $10.04515$, and the fit $N^{3/2}\Zcal_N[1]=C_0+C_1/N+C_2/N^2$ over $N\in\{50,\dots,6400\}$ gives $C_0=10.04516$ with an $N^{-1/2}$ term fitted at $-0.1$ against $C_1=15.3$: the expansion is in integer powers. Right: the frozen field, $N^{3/2}Z_N[1;\Xi]/C$ against the tilt $e^{\|P\Xi\|^2/2}$ for three Gaussian matrices $\Xi$.}
\label{tab:rankone_numerics}
\end{table}

The posterior expectations follow the leading measure: $\E_\infty[|x|^2]=1.5377,\,1.5488,\,1.5515$ at $N=100,400,1600$ against the orbit average $1.5525$ ($=\sqrt cK_1(\sqrt c)/K_0(\sqrt c)=1.5528$), and $\E_\infty[\langle x,a\rangle\langle y,b\rangle]=1.2243,\,1.2436,\,1.2484$ against $c=1.25$.

\subsection{What is formal}

The column-wise Gaussian integration \eqref{eq:rankone_reduction}, with the field, is a theorem: \texttt{integral\_rankOne\_gauss} in \texttt{Grammar/RankOneGauss.lean} states, for every $M,N$, every $n\ge 0$, every $x$, truth $A$ and field $\Xi$,
\[
\int_{\R^N} e^{-n\sum_{j}\sum_i (x_iy_j-A_{ij})^2/2+\sqrt n\sum_j\sum_i (x_iy_j-A_{ij})\Xi_{ij}-|y|^2/2}\,dy
=\prod_j \sqrt{\frac{2\pi}{n|x|^2+1}}\,\exp\Big(\frac{(n\langle x,A_j\rangle+\sqrt n\langle x,\Xi_j\rangle)^2}{2(n|x|^2+1)}-\frac{n|A_j|^2}{2}-\sqrt n\langle A_j,\Xi_j\rangle\Big),
\]
proved by Fubini over the columns and the one-dimensional Gaussian integral with a linear term (\texttt{integral\_exp\_quadratic\_real}, from Mathlib's \texttt{integral\_cexp\_quadratic}). The local RLCT $(M+N-1)/2$ at a rank-one truth is the nmf seabed's theorem. The Morse--Bott Laplace expansion along the orbit, the Bessel closed forms and the tilt factor are derivations here, checked numerically.

\section{The two-leaf naive Bayes model at an independent truth: the moment map}\label{sec:nb}

\subsection{The model and its geometry}

A hidden binary class $H$ with $P(H=1)=t$ and two binary leaves $X_1,X_2$ conditionally independent given $H$, with $P(X_i=1\mid H=0)=a_i$ and $P(X_i=1\mid H=1)=b_i$: the parameter is $\theta=(t,a_1,b_1,a_2,b_2)\in[0,1]^5$ with the uniform prior, and the model is the two-component mixture of product distributions on $\{0,1\}^2$, the smallest Markov tree model (the star with two leaves). The observable distribution is determined by the \emph{moment coordinates}
\[
\lambda_i=\E X_i=(1-t)a_i+tb_i,\qquad \eta_i=b_i-a_i,\qquad \mu=\Cov(X_1,X_2)=t(1-t)\eta_1\eta_2 ,
\]
through the four cell probabilities
\begin{equation}\label{eq:nb_cells}
p(1,1)=\lambda_1\lambda_2+\mu,\quad p(1,0)=\lambda_1(1-\lambda_2)-\mu,\quad p(0,1)=(1-\lambda_1)\lambda_2-\mu,\quad p(0,0)=(1-\lambda_1)(1-\lambda_2)+\mu ,
\end{equation}
so the model saturates the three-dimensional simplex (every $2\times2$ table is such a mixture) and the fibres of the map $\theta\mapsto y=(\lambda_1,\lambda_2,\mu)$ are generically two-dimensional. The truth is a distribution with \emph{independent} leaves and interior means, $y^*=(\lambda_1^*,\lambda_2^*,0)$ with $0<\lambda_i^*<1$; write
\[
v_i=\lambda_i^*(1-\lambda_i^*),\qquad V=v_1v_2,\qquad u_i=\log\frac{\lambda_i^*}{1-\lambda_i^*} .
\]
The zero fibre is $\{\lambda=\lambda^*\}\cap(\{t=0\}\cup\{t=1\}\cup\{\eta_1=0\}\cup\{\eta_2=0\})$, four two-dimensional faces (at $t=0$ the class-one leaf parameters $b$ are free, on $\{\eta_1=0\}$ the parameters $t$ and $a_2$ are free), meeting pairwise along intervals and all together at the two points
\[
P_0=(t,a,b)=(0,\lambda^*,\lambda^*),\qquad P_1=(1,\lambda^*,\lambda^*),
\]
which are exchanged by the label involution $\sigma(t,a,b)=(1-t,b,a)$. The divergence is $K(\theta)=D(p^*\|p_\theta)=G(y(\theta))$ with $G(y)=\sum_xp^*(x)\log(p^*(x)/p_y(x))$ smooth on the open simplex and Morse at $y^*$: its Hessian is the Fisher information of the saturated model in moment coordinates, which at $\mu^*=0$ is diagonal,
\begin{equation}\label{eq:nb_fisher}
G(y)=\frac{(\lambda_1-\lambda_1^*)^2}{2v_1}+\frac{(\lambda_2-\lambda_2^*)^2}{2v_2}+\frac{\mu^2}{2V}+G_3(y)+O(|y-y^*|^4),
\end{equation}
since $\sum_x\partial_{\lambda_1}p\,\partial_\mu p/p^*=1/\lambda_1^*-1/\lambda_1^*+1/(1-\lambda_1^*)-1/(1-\lambda_1^*)=0$ and $\sum_x1/p^*(x)=1/V$. The cubic term will matter once: $G_3(\lambda^*,\mu)=-\tfrac13\mu^3\sum_x s_x/p^*(x)^2$ with $s=(+,-,-,+)$ the signs in \eqref{eq:nb_cells}, and $V^2\sum_xs_x/p^*(x)^2=(1-2\lambda_1^*)(1-2\lambda_2^*)$.

At $P_0$ the walls are $t$, $\eta_1$, $\eta_2$ (with $t=0$ a boundary wall of the parameter space) and the two directions $u_i=\lambda_i-\lambda_i^*$ are regular: $K\asymp u_1^2+u_2^2+t^2\eta_1^2\eta_2^2$, a triple crossing times a regular quadratic form, so $(\lambda,m)=(1+\tfrac12,3)=(\tfrac32,3)$; the same at $P_1$. In a chart of the blow-up of the ideal $(u_1,u_2,t\eta_1\eta_2)$, $u_j=t\eta_1\eta_2z_j$, one has $K=(t\eta_1\eta_2)^2(1+|z|^2)\cdot(\text{unit})$ with Jacobian $|t\eta_1\eta_2|^2$, so all three divisors carry $(k,h)=(1,2)$ and the ratio $\tfrac32$: the three tie, and the multiplicity three is the log-square. What makes the example complete is that the whole computation can be pushed forward along the moment map and done in three dimensions, where the multiplicity becomes the singularity of an explicit density.

\subsection{The pushforward of the prior along the moment map}

For fixed $t$ the leaf map $(a_i,b_i)\mapsto(\lambda_i,\eta_i)=((1-t)a_i+tb_i,\,b_i-a_i)$ is a shear of determinant $(1-t)+t=1$, so the map $\theta\mapsto(t,\lambda_1,\eta_1,\lambda_2,\eta_2)$ preserves Lebesgue measure and carries the uniform prior on the cube to Lebesgue measure on the region $\{0\le\lambda_i-t\eta_i\le1,\ 0\le\lambda_i+(1-t)\eta_i\le1\}$; for fixed $(t,\lambda)$ this is the rectangle $\eta\in[-\alpha_1,\beta_1]\times[-\alpha_2,\beta_2]$ with $\alpha_i=\min(\lambda_i/(1-t),(1-\lambda_i)/t)$ and $\beta_i=\min((1-\lambda_i)/(1-t),\lambda_i/t)$, which contains $0$ in its interior. The density of $\eta_1\eta_2$ under Lebesgue measure on the rectangle is elementary, $\log^+(\beta_1\beta_2/z)+\log^+(\alpha_1\alpha_2/z)$ at $z>0$ (one logarithm per sign quadrant) and $\log^+(\beta_1\alpha_2/|z|)+\log^+(\alpha_1\beta_2/|z|)$ at $z<0$, so the pushforward density of the prior under $y=(\lambda_1,\lambda_2,\mu)$ is the one-dimensional integral
\begin{equation}\label{eq:nb_rho_integral}
\rho(\lambda,\mu)=\int_0^1\frac{dt}{t(1-t)}\,h_t\Big(\frac{\mu}{t(1-t)}\Big),
\end{equation}
and this integral is exactly computable. In the variable $r=t/(1-t)$, $dt/(t(1-t))=dr/r$, and for the quadrant $\eta_1,\eta_2>0$ the product $t(1-t)\beta_1\beta_2=\min((1-\lambda_1)r,\lambda_1)\min((1-\lambda_2)r,\lambda_2)/r$ is $Ar$ for $r\le r_{\rm lo}$, the constant $M$ for $r_{\rm lo}\le r\le r_{\rm hi}$, and $D/r$ for $r\ge r_{\rm hi}$, with $A=(1-\lambda_1)(1-\lambda_2)$, $D=\lambda_1\lambda_2$, $r_{\rm lo},r_{\rm hi}$ the ordered pair $\lambda_i/(1-\lambda_i)$, and $M=\min(\lambda_1(1-\lambda_2),\lambda_2(1-\lambda_1))$; the three pieces integrate against $dr/r$ to $\tfrac12\log^2(M/\mu)+\log(r_{\rm hi}/r_{\rm lo})\log(M/\mu)+\tfrac12\log^2(M/\mu)$ for $0<\mu<M$, and $M^2r_{\rm hi}/r_{\rm lo}=AD=V$. The other quadrant with $\mu>0$ gives the same, and the two mixed quadrants give the same expression with $M_-=\min(\lambda_1\lambda_2,(1-\lambda_1)(1-\lambda_2))$ in place of $M_+=M$:
\begin{prop}[the exact pushforward density; formal, \texttt{nbFibreDensity\_closed\_pos/neg}]\label{prop:nb_rho}
For $0<|\mu|<M_\pm$ (the Fr\'echet bounds, $\pm=\operatorname{sgn}\mu$) and $\lambda\in(0,1)^2$,
\begin{equation}\label{eq:nb_rho}
\rho(\lambda,\mu)=2\log\frac{M_\pm}{|\mu|}\,\log\frac{V}{M_\pm|\mu|}
=2\log^2\frac{\sqrt V}{|\mu|}-\frac{u_1^2+u_2^2}2+u_1u_2\operatorname{sgn}\mu ,
\end{equation}
with $V=\lambda_1\lambda_2(1-\lambda_1)(1-\lambda_2)$ and $u_i=\log(\lambda_i/(1-\lambda_i))$ evaluated at $\lambda$; $\rho=0$ outside these intervals.
\end{prop}
The density is \emph{exactly} a quadratic polynomial in $\log|\mu|$ on each side of $\mu=0$, with no power corrections; it vanishes continuously at the Fr\'echet bounds; its $\log^2$ coefficient is the universal $2$ and its $\log$ coefficient $2\log V$ is the same on both sides, while the constant term jumps by $2u_1u_2$ across $\mu=0$. Its $\lambda$-marginal is $2M_+(2+\log(V/M_+^2))+2M_-(2+\log(V/M_-^2))$, the area of the $(t,\eta)$-region, which integrates to $1$ over the unit square.

This is the whole example in one formula. The multiplicity $m=3$ is the $\log^2|\mu|$ singularity of the fibre volume; the two deepest points $P_0,P_1$ are where the fibre volume near $\mu=0$ accumulates (the ends $t\to0,1$ of the $r$-integral, each contributing $\tfrac12\log^2$ per sign quadrant); the leading measure of the paper, pushed down to parameter space, is
\[
\nu_{\rm lead}=\frac{c_3}2\,(\delta_{P_0}+\delta_{P_1}),\qquad \Zcal_N[f]\sim N^{-3/2}\log^2N\int f\,d\nu_{\rm lead}=\frac{c_3}2\,(f(P_0)+f(P_1))\,N^{-3/2}\log^2N
\]
for continuous $f$, with $c_3$ the constant of \eqref{eq:nb_Z} below, and the label symmetry forces the two weights to agree. In the language of the paper, $T_f(s)=\int K^{-s}f\,d\theta=\int G^{-s}\rho_f\,dy$ with $\rho_f$ the pushforward of $f\,d\theta$, and $\Gamma(s)T_f(s)=\int_0^\infty N^{s-1}\Zcal_N[f]\,dN$ has its leading pole $2c_3[f]/(\Gamma(\tfrac32)(\tfrac32-s)^3)$: the polar distribution of order three at $\tfrac32$ is the Mellin image of the $\log^2$ term.

\subsection{The complete population expansion}

With $\rho$ exact, $\Zcal_N[1]=\int e^{-NG(y)}\rho(y)\,dy$ is a three-dimensional Laplace integral with a logarithmic amplitude. In the standardised coordinates $\lambda_i=\lambda_i^*+\sqrt{v_i/N}\,x_i$, $\mu=\sqrt{V/N}\,z$ the $\log V$ terms cancel, $2\log^2(\sqrt V/|\mu|)=2(\tfrac12L-\log|z|)^2$ with $L=\log N$, and the Gaussian logarithmic moments $\int e^{-z^2/2}\log|z|\,dz=-\sqrt{2\pi}\,g/2$, $\int e^{-z^2/2}\log^2|z|\,dz=\sqrt{2\pi}(g^2/4+\pi^2/8)$ with $g=\gamma+\log2$ give
\begin{equation}\label{eq:nb_Z}
\Zcal_N[1]=(2\pi)^{3/2}V\,N^{-3/2}\Big[\frac{L^2}2+gL+\frac{g^2}2+\frac{\pi^2}4-\frac{u_1^2+u_2^2}2\Big]+d\,N^{-2}+O(N^{-5/2}\log^2N),
\end{equation}
so $c_3=\pi\sqrt{2\pi}\,V$, $c_2=(2\pi)^{3/2}Vg$, $c_1=(2\pi)^{3/2}V(g^2/2+\pi^2/4-(u_1^2+u_2^2)/2)$. The three coefficients at the leading exponent are the paper's polar data of orders $3,2,1$ at $s=\tfrac32$: the top one universal, the middle one the Gamma-derivative shift $g$, the bottom one carrying the geometry of the truth through $u_1^2+u_2^2$, the constant term of the fibre volume.

The first correction is not what a generic example would suggest. Since $\rho$ has no $|\mu|^k$ terms, there is no $N^{-2}\log^jN$ with $j>0$; and the even part of $\rho$ against the odd cubic phase integrates to zero. What survives at $N^{-2}$ is the \emph{sign jump} $u_1u_2\operatorname{sgn}\mu$ paired with the cubic term of the phase: in standardised coordinates $G_3=-\tfrac13(\kappa_1x_1^3+\kappa_2x_2^3+\kappa_1\kappa_2z^3)-x_1x_2z-\kappa_1x_1z^2-\kappa_2x_2z^2$ with $\kappa_i=(1-2\lambda_i^*)/\sqrt{v_i}$, only $z^3$ survives the $x$-integrations, and $\int e^{-z^2/2}|z|^3dz=4$ gives
\begin{equation}\label{eq:nb_d}
d=\frac{8\pi}3\sqrt V\,(1-2\lambda_1^*)(1-2\lambda_2^*)\,u_1u_2 ,
\end{equation}
which vanishes when either mean is $\tfrac12$. The structure to all orders, for $f=1$, is $\sum_kN^{-3/2-k}P_k(\log N)+\sum_kN^{-2-k}d_k$ with $\deg P_k\le2$: the logarithmic amplitude feeds the first series, the jump the second. This is a case where the paper's finite parts at the \emph{same} exponent, the $\log N$ and constant coefficients at $\tfrac32$, are the informative corrections, and the next power is a parity effect.

\subsection{The sample}

The empirical loss is exact in the empirical table $\hat p$: $K_N(\theta)=D(\hat p\|p_\theta)-D(\hat p\|p^*)$, so
\[
Z_N[f;\text{sample}]=e^{ND(\hat p\|p^*)}\int e^{-ND(\hat p\|p_y)}\rho_f(y)\,dy ,
\]
a Laplace integral about the empirical moments $\hat y=y(\hat p)=y^*+\xi/\sqrt N$, where $\xi=\sqrt N(\hat y-y^*)$ is asymptotically $N(0,I^{-1})$ in the moment coordinates. The prefactor is the paper's tilt, $e^{ND(\hat p\|p^*)}=e^{\xi^{\mathsf T}I\xi/2}(1+O(N^{-1/2}))$, with the projector the identity on the three-dimensional observable tangent space because the model saturates. Behind the tilt, the $\lambda$-directions are regular and the $\mu$-Gaussian is centred at $\hat\mu=\xi_\mu/\sqrt N$, i.e.\ at $z=a:=\xi_\mu/\sqrt V$ in the standardised coordinate: the field enters through the shifted logarithmic moments
\[
m_j(a)=\int e^{-(z-a)^2/2}\log^j|z|\,dz,\qquad q(a)=\int e^{-(z-a)^2/2}\operatorname{sgn}z\,dz=\sqrt{2\pi}\,(2\Phi(a)-1),
\]
the fluctuation functions of this example, and
\begin{equation}\label{eq:nb_frozen}
e^{-ND(\hat p\|p^*)}\,N^{3/2}Z_N[1;\text{sample}]\to2\pi V\Big[\sqrt{2\pi}\Big(\frac{L^2}2-\frac{u_1^2+u_2^2}2\Big)-2L\,m_1(a)+2m_2(a)+u_1u_2\,q(a)\Big].
\end{equation}
The $\log^2N$ coefficient is field-independent once the tilt is divided out ($m_0(a)=\sqrt{2\pi}$ for every shift), the $\log N$ coefficient sees the field through $m_1(a)$, and the constant through $m_2(a)$ and, via the jump, through $q(a)$. For the posterior mean of the covariance parameter,
\begin{equation}\label{eq:nb_postmu}
\E[\mu\mid\text{sample}]=\hat\mu-\frac{4\sqrt V}{\sqrt N\log N}\,\frac{m_1'(a)}{\sqrt{2\pi}}+O\Big(\frac1{\sqrt N\log^2N}\Big),
\end{equation}
the posterior tracks the empirical covariance with a relative correction of order $1/\log N$, while at the population truth ($a=0$) the logarithmic terms are even and only the jump contributes, $\E_N[\mu]\sim4\sqrt V\,u_1u_2/(\sqrt{2\pi}\sqrt N\log^2N)$, a partially vanishing observable with a $1/\log^2N$ rate on top of $N^{-1/2}$. This last limit is approached slowly: the cubic term of the phase against the even part of the amplitude contributes to $\E_N[\mu]$ at relative order $(1-2\lambda_1^*)(1-2\lambda_2^*)\log^2N/\sqrt N$, which exceeds the jump term below $N\approx10^5$, and including it together with the full $\log N$ and constant terms of the denominator gives the posterior covariance to four digits (\cref{sec:nb_numerics}).

Finally an exact statement at every $N$ and for every sample: the label involution $\sigma$ fixes the cell probabilities \eqref{eq:nb_cells} and preserves the prior, so every label-antisymmetric observable has posterior mean zero, and in particular
\[
\E[t\mid\text{sample}]=\tfrac12 ,
\]
the posterior weight of $P_0$ and $P_1$ is equal, the leading measure is not moved by the data (the three regimes of the paper: $t-\tfrac12$ is exactly vanishing, $\mu$ partially vanishing, $t(1-t)$ generic).

\subsection{Numerical checks}\label{sec:nb_numerics}

The script \texttt{projects/grammar/experiments/naivebayes/nb\_check.py} takes $\lambda^*=(0.3,0.6)$ ($V=0.0504$, $u_1u_2=-0.3436$), checks \eqref{eq:nb_rho} against the $t$-integral \eqref{eq:nb_rho_integral} and its total mass, integrates $e^{-NG}\rho$ over the simplex by Gauss--Legendre in $\lambda$ and adaptive quadrature in $\mu$ split at zero, and compares with \eqref{eq:nb_Z}--\eqref{eq:nb_postmu}.

\begin{table}[h]
\centering\small
\begin{tabular}{@{}rrrr@{}}
\toprule
$N$ & $N^{3/2}\Zcal_N-c_3L^2-c_2L$ & $N^2(\Zcal_N-\text{lead})$ & $N^{3/2}Z_N[1;\text{s}]/\text{pred.}$, $a=1.11$ \\
\midrule
$10^3$ & 2.15887 & $-2.847$ & 0.99256 \\
$10^4$ & 2.23366 & $-1.524$ & 0.99829 \\
$10^5$ & 2.24665 & $-0.713$ & 0.99951 \\
$10^6$ & 2.24861 & $-0.293$ & 0.99985 \\
\midrule
limit & $c_1=2.24890$ & $d=0.0517$ (fit $0.0513$) & 1 \\
\bottomrule
\end{tabular}
\qquad
\begin{tabular}{@{}rrr@{}}
\toprule
$N$ & $\dfrac{\E[\mu\mid\text{s}]-\hat\mu}{\text{pred.}-\hat\mu}$ & $\dfrac{\E_N[\mu]}{\text{pred.}}$ \\
\midrule
$10^3$ & 1.0196 & 0.9885 (1.075) \\
$10^4$ & 1.0195 & 0.9987 (1.037) \\
$10^5$ & 1.0181 & 0.9999 (0.957) \\
$10^6$ & 1.0168 & 1.0000 (0.906) \\
\bottomrule
\end{tabular}
\caption{$\lambda^*=(0.3,0.6)$. The closed density \eqref{eq:nb_rho} agrees with the $t$-integral \eqref{eq:nb_rho_integral} to ten digits at every tested $(\lambda,\mu)$, its $\lambda$-marginal with the area of the $(t,\eta)$-region, and its total mass is $1.00000000$. Left: the constant coefficient at $N^{-3/2}$ converges to $c_1$ (the remainder is the $N^{-1/2}$ tail, $d\,N^{-1/2}$ plus the $N^{-5/2}\log^2N$ terms), the $N^{-2}$ residual is dominated by $N^{-5/2}\log^2N$ and a four-parameter fit $d+(aL^2+bL+c)/\sqrt N$ over $N\ge3000$ recovers $d$ to $0.7\%$ (at $\lambda^*=(\tfrac12,\tfrac12)$ the same residual tends to $0$); the frozen-field bracket \eqref{eq:nb_frozen} for the pure-covariance field $\xi_p=(1,-1,-1,1)/4$ ($a=1.114$), with the tilt $e^{ND(\hat p\|p^*)}=1.8592$ against $e^{\xi^{\mathsf T}I\xi/2}=1.8590$; a second field with $a=0.13$ gives $0.9938,0.9990,0.9998,0.99994$. Right: the posterior covariance with the field, \eqref{eq:nb_postmu}, and at the truth, where the column shows the ratio to the prediction including the cubic-phase term and, in brackets, to the leading $4\sqrt V u_1u_2/(\sqrt{2\pi}\sqrt N\log^2N)$ alone. A five-dimensional Monte Carlo at $N=30$ with $4\cdot10^6$ prior draws reproduces the three-dimensional quadrature of the pushforward ($Z_N$ ratio $0.9988$), gives $\E[t\mid\text{sample}]=0.49992$, and its histogram of $\mu$ follows the exact density.}
\label{tab:nb_numerics}
\end{table}

\subsection{What is formal}

The moment parametrisation and the two measure-theoretic facts behind \eqref{eq:nb_rho} and the exact symmetry are theorems in \texttt{Grammar/NaiveBayes.lean}: the cell probabilities as polynomials in $(\lambda_1,\lambda_2,\mu)$ \eqref{eq:nb_cells} (\texttt{nbCell\_true\_true} and its three companions, \texttt{sum\_nbCell}, \texttt{nbCov\_eq}); the moment map $\theta\mapsto(t,(\lambda_1,\eta_1),(\lambda_2,\eta_2))$ preserves Lebesgue measure on the parameter space (\texttt{measurePreserving\_nbMomentMap}, from the determinant-one shear \texttt{measurePreserving\_nbLeafMap} assembled by Mathlib's \texttt{skew\_product}), so the uniform prior pushes to Lebesgue measure on the explicit image region (\texttt{map\_nbMomentMap\_restrict\_nbBox}, \texttt{nbMomentMap\_image\_nbBox}); the label involution fixes the likelihood and preserves the prior, giving $\int_{[0,1]^5}t\,L_c\,d\theta=\tfrac12\int_{[0,1]^5}L_c\,d\theta$ for every count vector $c$ (\texttt{integral\_fst\_nbLik}, \texttt{integral\_nbLik\_antisymm} for antisymmetric observables); and the Fisher information of the saturated model in moment coordinates at an independent truth is $\operatorname{diag}(1/v_1,1/v_2,1/V)$ (\texttt{nbFisher\_mu\_mu}, \texttt{nbFisher\_l\textsubscript{1}\_mu} $=0$, and the other entries), with the cubic coefficient $V^2\sum_xs_x/p^*(x)^2=(1-2\lambda_1)(1-2\lambda_2)$ of \eqref{eq:nb_d} (\texttt{nbCubic\_mu}), the cells being derivable polynomials in the moments (\texttt{hasDerivAt\_nbCellY\_mu}, \ldots). The two pushforward steps behind \cref{prop:nb_rho} are theorems in \texttt{Grammar/NaiveBayesDensity.lean}: the product-of-uniforms density (\texttt{lintegral\_rect\_prod}: for Lebesgue measure on $[-\alpha,\beta]\times[-\gamma,\delta]$ and every measurable $\Psi\ge0$, $\int\Psi(\eta_1\eta_2)\,d\eta=\int\Psi(z)\,h(z)\,dz$ with $h$ the two-logarithm density, proved by Tonelli, the substitution $w=\eta_1\eta_2$ on each slice and the fibre $\{\eta_1\in[-\alpha,\beta]:z/\eta_1\in[-\gamma,\delta]\}$ computed as two intervals) and the fibre volume of $\mu=t(1-t)\eta_1\eta_2$ over the region of $(t,\eta)$ at fixed means as the $t$-integral \eqref{eq:nb_rho_integral} (\texttt{lintegral\_nbRegion}, with the density \texttt{nbFibreDensity}). The closed form itself is now a theorem as well (\texttt{Grammar/NaiveBayesClosedForm.lean}, \texttt{nbFibreDensity\_closed\_pos} and \texttt{\_neg}): for $0<|\mu|<M_\pm$ the fibre density is exactly $2\log(M_\pm/|\mu|)\log(V/(M_\pm|\mu|))$. The formal proof avoids the case analysis of the $r$-derivation above: it writes $\log^+(Q/z)=\int_z^\infty\mathbf 1[w\le Q]\,dw/w$, swaps the integrals, and uses that the superlevel set $\{t:w\le P(t)/(t(1-t))\}$ of the quadrant product $P(t)=\min((1-b_1)t,b_1(1-t))\min((1-b_2)t,b_2(1-t))$ is the single interval $[w/(A+w),D/(D+w)]$ for $w\le M$ and empty above (a product of two minima of positive numbers is the minimum of the four products), so that $\int dt/(t(1-t))$ over it is $\log(AD/w^2)$ and $\int_z^M\log(AD/w^2)\,dw/w=\log(M/z)\log(AD/(Mz))$ (\texttt{quadJ\_eq}); the two quadrants at each sign share $M_\pm$ and $AD=V$. The chain is closed end to end in \texttt{Grammar/NaiveBayesPushforward.lean}: \texttt{lintegral\_nbBox\_moments} states that for every measurable $\Psi\ge0$, $\int_{[0,1]^5}\Psi(\lambda_1(\theta),\lambda_2(\theta),\mu(\theta))\,d\theta=\int_{(0,1)^2}\int_{\R}\Psi(\lambda,z)\,\rho(\lambda,z)\,dz\,d\lambda$ with $\rho$ the $t$-integral \eqref{eq:nb_rho_integral}, hence the closed form \eqref{eq:nb_rho}: the uniform prior on the cube, pushed forward along the two means and the covariance, has exactly the density of \cref{prop:nb_rho} (the moment map, a measure-preserving reordering of the coordinates, Tonelli, and the slice of the image at fixed means identified with the region up to the null slices $t\in\{0,1\}$). The Laplace expansion and the frozen-field formulas are derivations here, checked numerically.

\end{document}


## The Lean headlines (units DLXXXII–DXCV)

| **DLXXXII** | ★★★ **THE CONE EXAMPLE: the blow-up chart of `K = q²` for a quadratic form of signature (2,2) — the linear network with a width-two hidden layer (u916; examples_slop §2)**: the blow-up of the vertex gives the chart data `h = (3, 0)`, `k = (2, 1)` (`coneH`, `coneK`; exceptional divisor of ratio 1, strict transform of the cone of ratio ½); `chartZeta_const_cone`: `T(s)[c] = c/((4−4s)(1−2s))`; ★ `chartPolarCoeff_const_cone_half`/`_one`: simple poles with `C_{½,1} = −c/4` (`A_{½,1} = c/4`) and `C_{1,1} = c/4` (`A_{1,1} = −c/4`, the vertex enters with a NEGATIVE finite part), the candidate double pole at 1 has coefficient zero; the coupling-average formula with a constant field `a` (`couplingPolarCoeff_cone`) gives ★★★ `empCoeff_cone_half`: `c_{½,0} = S_{½}(a)/4`, ★★★ `empCoeff_cone_one`: `c_{1,0} = −S_1(a)/4`, `empCoeff_cone_one_log`: `c_{1,1} = 0`, `empCoeff_cone_zero_field` (`√π/4`, `−1/4`); `integral_coupKernel_mul_ofReal`/`integral_coupKernel_exp_sqrt` (the coupling integral of `e^{a√t}` at index μ is `S_μ(a)`). Numerically checked (projects/grammar/experiments/cone): the global Leray reduction `Z_N[1] = 2π²∫e^{−Nv²/2−|v|}` for the Gaussian prior, the vertex term, the insertion `u₁²` and the field-restored odd term, and the critical averaged evidence. | ConeExample.lean |
| **DLXXXIII** | ★★★ **THE LERAY DENSITY OF THE CONE UNDER THE GAUSSIAN PRIOR (u917; examples_slop §2)**: for `q(u) = ((u₁²+u₂²) − (u₃²+u₄²))/2` on `(ℝ×ℝ)×(ℝ×ℝ)` (`coneQ`) and the Gaussian weight `gaussW = e^{−|u|²/2}`, bipolar coordinates (`lintegral_radial_sq`: `∫_{ℝ²} Ψ(|z|²) = π ∫_0^∞ Ψ`, from Mathlib's `lintegral_comp_polarCoord_symm` and the `r²` substitution `lintegral_Ioi_eq_two_mul_lintegral_sq`), the quadrant reduction `lintegral_cone_gauss` (`∫ G(q) e^{−|u|²/2} = π² ∫_0^∞∫_0^∞ G((p−t)/2) e^{−(p+t)/2}`), the substitution `t = p − 2v` and Tonelli over the triangle (`lintegral_quadrant`: `= 2 ∫_ℝ G(v) e^{−|v|}`), all with lower integrals and NO integrability hypotheses; ★★★ `map_coneQ_gaussian`: the pushforward of `e^{−|u|²/2} du` along `q` is `2π² e^{−|v|} dv` — the Leray density of the cone, with the corner `∓2π²` at the vertex; ★★ `integral_cone_gaussian` (Bochner form for every measurable observable) and ★★ `cone_evidence_eq`: `∫_{ℝ⁴} e^{−Nq²/2+√N q a} e^{−|u|²/2} = 2π² ∫_ℝ e^{−Nv²/2+√N v a−|v|} dv`, the exact one-dimensional reduction of the frozen partition function of the cone model for every constant field. | ConeGaussian.lean |
| **DLXXXIV** | ★★ **THE BLOW-UP EXAMPLE `K = x²(x²+y²)/2` — POLAR COORDINATES AND THE ZETA FACTORISATION (u918; examples_slop §3)**: the two-output model `(x², xy)` with zero target; `lintegral_polar` (Tonelli form of Mathlib's polar coordinates: `∫_{ℝ²} f = ∫_0^∞∫_{−π}^{π} r f(r cos θ, r sin θ)`), `blowK_polar` (`K = r⁴cos²θ/2`, the polar coordinates as the oriented blow-up), `blowK_rpow_gauss_polar`, `integral_radial_gamma` (`∫_0^∞ r^{4w+1}e^{−r²/2} = 2^{2w}Γ(2w+1)`), ★★ `lintegral_blowK_gauss`: for `w > −½`, `∫_{ℝ²} K^w e^{−|z|²/2} = 2^w Γ(2w+1) · ∫_{−π}^{π} |cos θ|^{2w} dθ` — the zeta function of the model against the Gaussian prior factorises into the radial wall's Gamma factor and the angular wall's Beta integral (whose evaluation `2√π Γ(w+½)/Γ(w+1)`, hence `ζ = 2^{3w+1}Γ(w+½)²` with double poles at every half-integer, is not in Mathlib and stays a derivation). Numerically checked (projects/grammar/experiments/blowup): the population expansion to three poles (14 digits), the partially/fully vanishing observables `y²`, `x²`, the frozen leading logarithm `√(π/2) e^{ξ₂²/2}`. | BlowUpPolar.lean |
| **DLXXXV** | ★★ **RANK-ONE MATRIX FACTORISATION AT A RANK-ONE TRUTH — THE COLUMN-WISE GAUSSIAN INTEGRATION (u919; examples_slop §4)**: `integral_exp_quadratic_real` (`∫ e^{−αy²+βy−γ} = √(π/α) e^{β²/4α−γ}`, from Mathlib's `integral_cexp_quadratic`), the column decompositions `sum_sq_column`/`sum_field_column`, and ★★ `integral_rankOne_gauss`: for the model `x yᵀ` with truth `A`, frozen field `Ξ` and the Gaussian prior, `∫_{ℝ^N} e^{−nK + √n⟨xyᵀ−A,Ξ⟩ − |y|²/2} dy = ∏_j √(2π/(n|x|²+1)) exp((n⟨x,A_j⟩+√n⟨x,Ξ_j⟩)²/(2(n|x|²+1)) − n|A_j|²/2 − √n⟨A_j,Ξ_j⟩)` (Fubini over the columns, `integral_fintype_prod_volume_eq_prod`), the exact reduction of the `M+N`-dimensional partition function to `M` dimensions for every field. Numerically checked (projects/grammar/experiments/rankone, M = N = 2): the Morse–Bott leading constant `C = 4π√(2π/c)K₀(√c)` (six digits), the pure `1/N` series, the orbit averages, the tilt `e^{|PΞ|²/2}`. | RankOneGauss.lean |
| **DLXXXVI** | ★★ **TWO-LEAF NAIVE BAYES — MOMENT COORDINATES AND THE EXACT LABEL SYMMETRY (u920; examples_slop §5)**: the cell probabilities of the hidden-class model `(t, (a₁,b₁), (a₂,b₂))` are polynomials in the means `λᵢ = (1−t)aᵢ + t bᵢ` and the covariance `μ = t(1−t)(b₁−a₁)(b₂−a₂)` (`nbCell_true_true` …, `sum_nbCell`, `nbCov_eq`), so the likelihood factors through the moment map `θ ↦ (t, (λ₁,η₁), (λ₂,η₂))`; ★★ `measurePreserving_nbMomentMap` (the fixed-`t` leaf map `(a,b) ↦ ((1−t)a + tb, b−a)` is a determinant-one shear, `measurePreserving_nbLeafMap`, assembled by `skew_product`), `map_nbMomentMap_restrict_nbBox` (the uniform prior pushes to Lebesgue measure on the image region `nbMomentMap_image_nbBox`), which is the first step of the exact pushforward density `ρ(λ, μ) = 2 log²(√V/|μ|) − (u₁²+u₂²)/2 + u₁u₂ sgn μ` (multiplicity 3 = the `log²` singularity); ★★ `integral_fst_nbLik` / `nbPosteriorMean_fst`: the label involution `(t,a,b) ↦ (1−t,b,a)` fixes every cell probability (`nbCell_nbSwap`) and preserves the prior (`measurePreserving_nbSwap`, `nbSwap_preimage_nbBox`), so for EVERY sample and sample size the posterior mean of the class probability is exactly `1/2`, and every label-antisymmetric observable has posterior mean zero (`integral_nbLik_antisymm`). The Fisher information in moment coordinates at an independent truth is `diag(1/v₁, 1/v₂, 1/V)` (`nbFisher_mu_mu`, `nbFisher_l₁_mu` = 0, …) and the cubic coefficient `V² Σ s_x/p*(x)² = (1−2λ₁)(1−2λ₂)` (`nbCubic_mu`), the data of the `N^{−2}` sign-jump correction `d = (8π/3)√V(1−2λ₁)(1−2λ₂)u₁u₂`. Numerically (projects/grammar/experiments/naivebayes): the exact density, `Z_N = (2π)^{3/2}V N^{−3/2}[½L² + gL + g²/2 + π²/4 − (u₁²+u₂²)/2] + dN^{−2} + …`, the tilt, the posterior covariance. | NaiveBayes.lean |
| **DLXXXVII** | ★★ **THE FIBRE VOLUME OF THE NAIVE BAYES MOMENT MAP — PRODUCT DENSITY AND THE `t`-INTEGRAL (u921; examples_slop §5, Prop. nb_rho)**: ★★ `lintegral_rect_prod`: for Lebesgue measure on `[−α,β]×[−γ,δ]` and every measurable `Ψ ≥ 0`, `∫_rect Ψ(η₁η₂) = ∫ Ψ(z)·prodDensity(z) dz` with `prodDensity(z) = log⁺(βδ/z) + log⁺(αγ/z)` (`z>0`), `log⁺(βγ/|z|) + log⁺(αδ/|z|)` (`z<0`) (Tonelli + `Real.map_volume_mul_left` on each slice + the fibre `{η₁ ∈ [−α,β] : z/η₁ ∈ [−γ,δ]}` = two intervals `prodFibre_pos/neg` + `∫ dη/|η| = log`, `lintegral_Icc_inv`); ★★ `lintegral_nbRegion`: over the region `nbRegion λ` of `(t,(η₁,η₂))` (rectangle `[−αᵢ(t), βᵢ(t)]` over each `t ∈ (0,1)`, the slice of the moment-map image at fixed means) the pushforward along `μ = t(1−t)η₁η₂` has density `nbFibreDensity λ z = ∫₀¹ dt/(t(1−t)) prodDensity(α(t),β(t))(z/(t(1−t)))`, the exact one-dimensional integral behind `ρ(λ,μ) = 2 log(M±/|μ|) log(V/(M±|μ|))` (its closed form is the remaining calculus). | NaiveBayesDensity.lean |
| **DLXXXVIII** | ★★★ **THE EXACT FIBRE VOLUME OF THE NAIVE BAYES MOMENT MAP — CLOSED FORM (u922; examples_slop §5, Prop. nb_rho now a theorem)**: `nbFibreDensity_closed_pos`/`_neg`: for `0 < |μ| < M±` the density of the pushforward of the prior along the covariance is EXACTLY `ρ(λ,μ) = 2 log(M±/|μ|)·log(V/(M±|μ|))`, `M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`, `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`, `V = λ₁(1−λ₁)λ₂(1−λ₂)` — a quadratic in `log|μ|` with no power corrections: multiplicity three as a formula. Proof WITHOUT case analysis on the order of the means: the quadrant integral `J(z) = ∫₀¹ dt/(t(1−t)) log⁺(P(t)/(t(1−t)z))` with `P = min((1−b₁)t, b₁(1−t))·min((1−b₂)t, b₂(1−t))` is computed by the LAYER CAKE `log⁺(Q/z) = ∫_{w>z} 1[w ≤ Q] dw/w` (`ofReal_logPlus_eq_lintegral`), Tonelli, and the superlevel set `{t : w ≤ P/(t(1−t))} = [w/(A+w), D/(D+w)]` for `w ≤ M` (`quad_superlevel`, via `min_mul_min_eq`: a product of minima is the minimum of the four products), empty above (`quad_superlevel_empty`); `∫ dt/(t(1−t))` over it is `log(AD/w²)` (`lintegral_Icc_inv_mul_one_sub`, antiderivative `log t − log(1−t)`), and `∫_z^M log(AD/w²) dw/w = log(M/z) log(AD/(Mz))` (`lintegral_log_div_sq`, antiderivative `log(AD) log w − log² w`): ★★ `quadJ_eq`. The two quadrants at each sign (`prodDensity_nb_pos/neg`, `nbFibreDensity_eq_quadJ_pos/neg`) share `M±` and `AD = V`. | NaiveBayesClosedForm.lean |
| **DLXXXIX** | ★★★ **THE NAIVE BAYES PRIOR PUSHED FORWARD ALONG THE MOMENTS — END TO END (u923; examples_slop §5)**: `lintegral_nbBox_moments`: for every measurable `Ψ ≥ 0`, `∫_{[0,1]⁵} Ψ(λ₁(θ), λ₂(θ), μ(θ)) dθ = ∫_{(0,1)²} ∫_ℝ Ψ(λ, z)·nbFibreDensity(λ, z) dz dλ` — the uniform prior on the cube of `(t, a, b)`, pushed forward along the two means and the covariance, has the density of DLXXXVII–VIII, i.e. EXACTLY `2 log(M±/|z|) log(V/(M±|z|))` on `0 < |z| < M±`. Assembly: the measure-preserving moment map (`restrict_image_emb` + `lintegral_comp`), a measure-preserving reordering `(t,(λ₁,η₁),(λ₂,η₂)) ↦ ((λ₁,λ₂),(t,(η₁,η₂)))` composed from `volume_preserving_prodAssoc`, `Measure.measurePreserving_swap` and `MeasurePreserving.prod` (`measurePreserving_interchange`, `measurePreserving_nbReorder`; the composite is `rfl`), Tonelli, and the slice of the image at fixed means = `nbRegion` up to the null slices `t ∈ {0,1}` (`nbSlice_inter_Ioo`, `nb_slice_iff`, `nbSlice_ae_eq`, `Measure.restrict_congr_set`); off `[0,1]²` the slice is empty (means are convex combinations). | NaiveBayesPushforward.lean |
| **DXC** | ★★★ **THE BLOW-UP ZETA FUNCTION IN CLOSED FORM: `ζ(w) = 2^{3w+1} Γ(w+½)²` (u924; examples_slop §3)**: `lintegral_blowK_gauss_closed`: for `w > −½`, `∫_{ℝ²} (x²(x²+y²)/2)^w e^{−|z|²/2} dz = 2^{3w+1} Γ(w+½)²` — the double poles of `Γ(w+½)²` at the negative half-integers ARE the tied walls of the blow-up. Via ★★ `lintegral_abs_cos_rpow`: the angular Beta integral `∫_{−π}^{π} |cos θ|^{2w} dθ = 2√π Γ(w+½)/Γ(w+1)`, evaluated by the GAUSSIAN TRICK rather than Mathlib's complex Beta function: `∫_{ℝ²} |x|^{2w} e^{−|z|²/2}` is `2^{w+½}Γ(w+½)·√(2π)` in Cartesian coordinates (`lintegral_abs_rpow_gauss` by reflection `Measure.measurePreserving_neg` + `integral_rpow_mul_exp_neg_mul_rpow`; `lintegral_gauss_half` from `integral_gaussian`) and `2^wΓ(w+1)·∫|cos|^{2w}` in polar coordinates (`lintegral_polar`, `integral_radial_gamma'`); then Legendre duplication `Real.Gamma_mul_Gamma_add_half (w+½)`. Closes the formal gap noted for §3 (the note said 'analytic derivation, not in Mathlib'). | BlowUpZeta.lean |
| **DXCI** | ★★ **THE CROSSING `x²y²` WITH THE FLAT PRIOR: THE ONE-DIMENSIONAL POLAR DISTRIBUTION `2 log(1/|t|)` (u925; examples_slop §2)**: `lintegral_crossing_flat`: for every measurable `Ψ ≥ 0`, `∫_{[−1,1]²} Ψ(w₁w₂) dw = ∫_{−1}^{1} Ψ(t)·2 log(1/|t|) dt` — the product-of-uniforms density of DLXXXVII at the unit square (`prodDensity_unit`); `lintegral_crossing_flat_field`: the depth-two DLN with zero target, flat prior and frozen regression field, with any insertion `f(w₁w₂)`, is the one-dimensional integral `∫ f(t) e^{−Nt²/2 + √N ξ t}·2 log(1/|t|) dt`. Numerically (projects/grammar/experiments/monomial): the flat-prior expansion `√(2π)/(L−1)! N^{−1/2} Q_{L−1}(log N − log 2)` is EXACT modulo `e^{−N/2}` (1e-13 at N ≥ 100, L = 2,3,4; `Q₂ = (t−ψ)² + π²/2`, `Q₃ = (t−ψ)³ + (3π²/2)(t−ψ) + 14ζ(3)`, ψ = ψ(½)), the Gaussian-prior `A_{L−1}N^{−1/2}P_{L−1}(log N + κ_L)` has O(1/N) relative corrections, the depressed-polynomial fit reproduces `κ₃` and `κ₃² + π²`, the frozen-field reduction is exact, and `E[w₁²](log N + κ₂) → 2.000000`. | CrossingFlatPrior.lean |
| **DXCII** | ★★★ **THE DEPTH-TWO DEEP LINEAR NETWORK WITH FLAT PRIOR, TO ALL ORDERS (u926; examples_slop §2)**: `crossing_flat_allOrders`: for every `N > 0`, `∫_{[−1,1]²} e^{−N(w₁w₂)²/2} dw = √(2π/N)(log N + γ + log 2) + 4∫_1^∞ e^{−Nt²/2} log t dt`, and `crossing_flat_remainder_le`: `0 ≤ ∫_1^∞ e^{−Nt²/2} log t ≤ e^{−N/2}/N` — a COMPLETE expansion of a partition function as one theorem: the exponent `½`, the polar coefficients `√(2π)` (log) and `√(2π)(γ + log 2)` (constant), and an exponentially small remainder. Ingredients: the polar distribution `2 log(1/|t|)` (DXCI); the Gaussian logarithmic moment `∫_0^∞ e^{−u²/2} log u = −(√(2π)/4)(γ + log 2)` (`integral_exp_neg_sq_half_log`) from `Γ'(½) = ∫_0^∞ t^{−1/2} log t e^{−t} = −√π(γ + 2 log 2)` (`integral_rpow_log_exp_half`: Mathlib's `Complex.hasDerivAt_GammaIntegral` + `Complex.hasDerivAt_Gamma_one_half` + `HasDerivAt.unique`, cast to reals with `integral_complex_ofReal`/`Complex.ofReal_cpow`), the substitution `integral_comp_rpow_Ioi_of_pos`, the scaling `integral_comp_mul_left_Ioi`, `integral_gaussian_Ioi`; integrability of `e^{−bx²} log x` via `|log x| ≤ 2x^{−1/2} + x` (`abs_log_le_rpow`); the improper FTC `integral_Ioi_of_hasDerivAt_of_tendsto` for the remainder. | CrossingFlatAllOrders.lean |
| **DXCIII** | ★★★ **THE CONE'S FROZEN PARTITION FUNCTION IN CLOSED FORM (u927; examples_slop §3)**: `cone_evidence_closed`: for `N > 0` and every constant field `a`, `∫_{ℝ⁴} e^{−N q²/2 + √N q a} e^{−|u|²/2} du = 2π² N^{−1/2}[e^{(a−1/√N)²/2} T(1/√N − a) + e^{(a+1/√N)²/2} T(1/√N + a)]` with the Gaussian tail `T(c) = ∫_c^∞ e^{−s²/2}` (`gaussTailStd`): the complete expansion in `N^{−1/2}` (every coefficient a Taylor coefficient of the closed form; at `a = 0`, `4π²N^{−1/2}e^{1/(2N)}T(1/√N) = 4π²N^{−1/2}[√(π/2) − N^{−1/2} + …]`, the vertex term). Via ★★ `integral_cone_leray_closed` (the Leray integral `∫ e^{−s²v²/2 + s a v − |v|}` by splitting at `0`, `integral_Iio_zero_eq_Ioi_neg`, completing the square `integral_Ioi_exp_quadratic` = translation `integral_Ioi_comp_add_right` + scaling `integral_comp_mul_left_Ioi`); integrability from `integrable_cexp_quadratic … |>.norm` + `Complex.norm_exp`; the substitution `N = s²` keeps every identity polynomial. | ConeClosedForm.lean |
| **DXCIV** | ★★★ **THE MIXED MONOMIAL `x²y⁶` WITH FLAT PRIOR, TO ALL ORDERS (u928; examples_slop §2)**: `mixed_flat_allOrders`: `∫_{[−1,1]²} e^{−N x²y⁶} = Γ(1/6) N^{−1/6} − √π N^{−1/2} + 2∫_1^∞ e^{−Nt²}(1 − t^{−2/3})`, `mixed_flat_remainder_le`: `0 ≤ ∫_1^∞ … ≤ e^{−N}/(2N)` — two simple poles at the two wall ratios `1/6`, `1/2`, nothing between, exponentially small remainder. Via ★★ `lintegral_square_cube`: the law of `t = x y³` under Lebesgue on the square has density `|t|^{−2/3} − 1` on `0 < |t| < 1` (`mixedDensity`): Tonelli with `y` outer (`lintegral_prod_symm`), the slice substitution `lintegral_Icc_mul_left` of DLXXXVII, swap, and the fibre `{y ∈ [−1,1] : |w| ≤ |y|³} = [−1, −|w|^{1/3}] ∪ [|w|^{1/3}, 1] ∪ {0}` (`cube_fibre` via `pow_le_pow_iff_left₀`, `Real.rpow_inv_natCast_pow`; empty above `|w| = 1`, `cube_fibre_empty`) with `∫ y^{−3} = (r^{−2} − 1)/2` (`lintegral_Icc_inv_cube`, `integral_rpow`). Integrability of the polar-distribution integrand is read off from the finiteness of the box integral (`hasFiniteIntegral_iff_enorm`, `Real.enorm_eq_ofReal`) rather than from rpow lemmas (Lean's `|t|^s` vs `t^s` for negative `t`). | MixedMonomialFlat.lean |
| **DXCV** | ★★★ **THE DEPTH-TWO DLN WITH FLAT PRIOR AND A FROZEN FIELD: TILT × log N MINUS TWICE THE SHIFTED LOG-MOMENT (u929; examples_slop §2)**: `crossing_flat_field`: for `N > 0` and every constant field `ξ`, `∫_{[−1,1]²} e^{−N(w₁w₂)²/2 + √N ξ w₁w₂} = N^{−1/2}[√(2π) e^{ξ²/2} log N − 2 m₁(ξ) − ∫_{|z| ≥ √N} e^{−z²/2 + ξz}(log N − 2 log|z|)]`, `m₁(ξ) = ∫ e^{−z²/2 + ξz} log|z|` (`logMomentShift`): the tilt multiplies the leading logarithm and the field enters the constant term only through the fluctuation function, with the remainder an explicit Gaussian tail. Proof: DXCI's polar distribution, the scaling `t = z/√N` (`intervalIntegral.integral_comp_mul_left`; `h t = H(√N t)` off the null point `t = 0`, where Lean's `log 0 = 0` breaks the pointwise identity), `integral_add_compl` for the tail, `integral_exp_quadratic_half` (= `integral_exp_quadratic_real` at `α = ½`), and the integrability `integrable_exp_quadratic_log` (dominate by `e^{ξ²}(2|z|^{−1/2} + |z|)e^{−z²/4}`, halves glued by `IntegrableOn.comp_neg` + `Set.neg_Ioi`). EXTENSION (same unit): the signed reduction `integral_crossing_flat` (Bochner form of DXCI for any integrable insertion `f(w₁w₂)`, via `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`), the Gaussian first moment `∫ z e^{−z²/2+ξz} = √(2π) ξ e^{ξ²/2}` (`integral_mul_exp_quadratic_half`, shift + oddness), and ★★ `crossing_flat_field_mean`: the posterior numerator of the OUTPUT `w₁w₂` is `N^{−1}[√(2π) ξ e^{ξ²/2} log N − 2 m₁⁽¹⁾(ξ) − tail]` (`logMomentShift₁`), so `E[w₁w₂ | ξ] = N^{−1/2}(ξ + O(1/log N))`, the partially vanishing regime as an exact ratio of two theorems. | CrossingFlatField.lean |
