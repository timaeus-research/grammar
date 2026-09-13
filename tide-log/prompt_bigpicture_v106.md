# Consult #106 — the companion note `averaging_dataset.tex`: claim-and-dependency survey

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 654 modules, zero sorry/axiom). Your consult #105 closed J-min and the paper's
Lean-facing programme (the wording pass is done: pin `32cdbf6`, audit 0 mismatches; the Overleaf push awaits the
user's authorisation), and asked for the companion note's first consult to be a **claim-and-dependency survey,
not implementation**, with the output a ledger: exact claim → exact hypotheses → existing declaration → missing
bridge → status → proposed unit/gate, distinguishing population vs empirical asymptotics, pathwise vs
in-probability/L¹ remainders, scalar vs joint/functional CLTs, concentration vs distributional convergence, fixed
vs dataset-dependent spectral structure, numerator vs normalised-ratio fluctuations.

Context. The note (Gerraty–Murfet, "dataset averaging"; §1–§6 + two appendices; 726 lines) is ALREADY heavily
annotated: 222 leanref dots on ~40 modules (inventory below). Its own §6.9 "What the expected error formulas still
need" says the remaining hypotheses (uniform integrability / uniform (1+ε)-moment bound and a predictive
Taylor-remainder estimate, plus the Gaussian-process existence and the CLT/tail certificates of the interface
table §6.10) are not discharged; its appendices are explicitly heuristic (no convergence/asymptotic-order
claims). The user's standing directive: formalise the note; we MAY edit the note's tex (move wrong or
unsupported material to appendices, shape it with you); paper edits go to staging; local commits only until the
user authorises an Overleaf push.

## What we ask for

1. The ledger, one row per substantive claim of §2–§6 (propositions/lemmas/theorems and the dotted prose),
   marking each as (a) fully certified by its dots, (b) certified with the stated qualification, (c) claimed
   beyond the dots (the "prose stronger than the formal statement" cases), (d) not formalised. Where a claim
   is (c), say how the tex should be reworded or whether it moves to an appendix.
2. The smallest missing bridges feeding CENTRAL claims, ranked, each with one explicit target theorem, the
   hypothesis list matching the note, the reusable dependencies (by declaration name from the inventory or
   the modules listed below), a success gate and a stopping rule. In particular assess: (i) the
   uniform-integrability input for the quartet algebra at finite resolution (§6.9); (ii) the predictive
   Taylor-remainder estimate; (iii) Gaussian-process existence from a kernel (the note's `GaussianField` is an
   adapter); (iv) the CLT/tail certificates for the ℓ¹ sample-data limit; (v) the normalised-ratio
   fluctuations vs the numerator (§5–§6 self-normalised quartet vs `GibbsJointRatio`).
3. Whether any material of §2–§6 should move to the appendices now (wrong, or heuristic), and whether the
   note's `rem:lean_convention` "levels" (exact / Gaussian-limit / conditional asymptotic) are the right
   scaffold for the ledger.
4. Do NOT pre-authorise a general empirical-process or functional-CLT programme; if a bridge needs that
   scale, say so and make the note conditional or narrower instead.

## Material

### A. The note (full tex, pinned at `\grammarLeanCommit` = 32cdbf6)

```latex
\documentclass[11pt]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{booktabs}
\usepackage[margin=1in]{geometry}
\usepackage{tikz}
\usetikzlibrary{decorations.pathmorphing,positioning}
\usepackage{hyperref}
\usepackage[capitalise,noabbrev]{cleveref}
\usepackage{natbib}

\newtheorem{thm}{Theorem}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{prop}[thm]{Proposition}
\crefname{prop}{Proposition}{Propositions}
\Crefname{prop}{Proposition}{Propositions}
\newtheorem{defn}[thm]{Definition}
\newtheorem{cor}[thm]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[thm]{Remark}
\newtheorem{example}[thm]{Example}

\newcommand{\norm}[1]{\|#1\|}

% Lean annotations. A blue dot in the margin links to the formal statement in
% timaeus-research/grammar (library Grammar), pinned at \grammarLeanCommit. The second argument
% of \leanrefL is documentation only and does not render. Requires two compile passes.
\newcommand{\grammarLeanCommit}{32cdbf6}
\newcommand{\leanrefmarker}{%
  \tikz[baseline=-0.3ex]%
    \shade[top color=white, bottom color=blue!75!black]
    (0,0) circle (0.66ex);%
}
\newcommand{\leanrefL}[2]{%
  \begin{tikzpicture}[remember picture, overlay]%
    \node[inner sep=0pt] (leanref anchor) at (0,0) {};%
    \node[inner sep=2pt, xshift=-40pt]
        at (current page.east |- leanref anchor) {%
      \begingroup
      \hypersetup{pdfborder={0 0 0}, colorlinks=false}%
      \href{https://github.com/timaeus-research/grammar/blob/\grammarLeanCommit/#1}{%
        \leanrefmarker}%
      \endgroup};%
  \end{tikzpicture}}

\title{Averaging over the dataset:\\ Gaussian averages and self-normalised Gaussian posterior identities\\ (working draft)}
\date{}

\begin{document}
\maketitle

\begin{abstract}
The Taylor tree expansion of the grammar paper writes the partition function $Z_n$ as a sum of leaf contributions in which the fluctuation function $S_\lambda$ is evaluated on the empirical process $\xi_n$, and Watanabe's averaged quantities are expectations of such expressions over the dataset. This note isolates what is rigorous in that programme. Once $\xi_n$ is replaced by its Gaussian limit $G$ we obtain exact one-point Gaussian averages with their finiteness threshold, bilocal integral and series formulas with formalised finiteness and divergence results in the strict regime and on the critical line, the covariance interpolation for the expected log-evidence, and---the main result---the \emph{self-normalised Gaussian posterior identities} at finite resolution: for finitely many base points and a centred Gaussian vector $G$, the Schwinger--Dyson identity and Gaussian integration by parts hold and every normalised quantity is integrable for \emph{every} $\beta>0$, giving the Bayes-quartet algebra $\lambda/\beta\pm\nu$, $(\lambda-\nu)/\beta\pm\nu$ with $\nu\ge0$. On the finite-sample side the sampling identity, including its sign, is certified at the sample datum before any limit. For i.i.d.\ chart observations satisfying an $\ell^1$ central-limit certificate and a uniform full-box sub-Gaussian bound, we derive the distributional limit of the scaled empirical core for one or finitely many charts, upgrade it to convergence of expectations after addition of a scaled $L^1$-negligible remainder, and identify the limiting expectation as a covariance-modified leading face integral: the temperature is replaced pointwise by $\beta(1-\beta\sigma^2/2)$, and by a single effective temperature when the evaluation variance is constant on the contributing face. These results are conditional on the certified chart-core representation and the stated remainder estimate; the geometric construction of the certified cores is a separate input. Blue dots in the margin identify the formalised statements. The diagrammatic reorganisation that motivated the note is kept as discussion and as an explicitly heuristic appendix, where formulas that were wrong or unsupported in earlier drafts are corrected.
\end{abstract}

\section{Introduction}\label{sec:scope}

The grammar paper expands the partition function
\[
Z_n(\beta)=\int\prod_{i=1}^ne^{-\beta f(X_i,u)}\,\pi(du)
\]
of a singular statistical model through a resolution of singularities. In a chart of the resolved space the exponent takes the standard form $-\beta nu^{2k}+\beta\sqrt n\,u^k\xi_n(u)$, where $\xi_n$ is the centred empirical process of the resolved coefficient (\cref{sec:sampling}), and the Taylor tree writes $Z_n$ as a sum of leaf contributions in which the fluctuation function $S_\lambda$ of \eqref{eq:S_defn} is evaluated on $\xi_n$. Watanabe's averaged quantities---the expected generalisation, training and Bayes errors---are expectations of such expressions over the dataset. This note isolates what is rigorous in that programme and records, statement by statement, what has been formalised.

The empirical process converges in law to a centred Gaussian field $G$ whose covariance is determined by the resolved coefficient (\cref{subsec:resolved_covariance}). Replacing $\xi_n$ by $G$ yields exact Gaussian averages: one-point averages with their finiteness threshold and bilocal two-point functions (\cref{sec:raw}), and---the main result---the self-normalised posterior identities of \cref{sec:quartet}, which hold for every temperature $\beta>0$ because extreme values of $S_\lambda(G_i)$ appear in numerator and denominator alike; \cref{sec:interpolation} gives the expected log-evidence by covariance interpolation and extends the identities to a compact base. The passage from the Gaussian limit back to finite samples is the subject of \cref{sec:grammar}: an exact annealed identity, a bridge from convergence in law to convergence of expectations, uniform moment bounds from sub-Gaussian control of the empirical phase, and the resulting annealed theorem whose limiting expectation is identified as a covariance-modified face integral. \Cref{sec:discussion} and the appendices record the diagrammatic reading that motivated the note, with its heuristic parts marked as such.

\paragraph{Three levels.} Everything below is one of the following, and the Lean remarks say which.
\begin{enumerate}
\item \emph{Exact finite-sample statements}: the algebraic sampling identity $N=n$ and the sign of the fluctuation (\cref{sec:sampling}), and the probabilistic annealed identity $\mathbb E Z_n(1)=\pi(W)$ under independence and likelihood normalisation (\cref{sec:grammar}).
\item \emph{Gaussian-limit theorems}: statements about the centred Gaussian field $G$ that is the limit in law of $\xi_n$ (\cref{sec:raw,sec:quartet,sec:interpolation}).
\item \emph{Conditional asymptotic consequences}: statements about the finite-sample Bayes errors, which need in addition the posterior transfer and uniform-integrability theorems (\cref{sec:grammar}).
\end{enumerate}
Convergence in distribution $\xi_n\Rightarrow G$ does not by itself give convergence of expectations: the expected leading coefficient can be infinite while every sample coefficient is finite (\cref{sec:raw}). Where the Lean library only proves a statement in level 2 the text says so.

\paragraph{The fluctuation function.} Throughout, with $\beta,\mu>0$,
\begin{equation}\label{eq:S_defn}
S_\mu(a)=\int_0^\infty y^{\mu-1}\,e^{-\beta y+\beta a\sqrt y}\,dy\leanrefL{Grammar/Fluctuation.lean\#L31}{fluctuation}
\end{equation}
(Watanabe's normalisation, the one used in the grammar paper and in Lean). Writing $y=T^2$ for the radial variable, $S_\mu(a)=2\int_0^\infty T^{2\mu-1}e^{-\beta T^2+\beta aT}\,dT$, so $S_\mu=2J_{2\mu}$ where $J_p(x)=\int_0^\infty s^{p-1}e^{-\beta s^2}e^{\beta sx}\,ds$ is the half-line quadratic integral of earlier drafts\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L56}{fluctuation\_eq\_two\_mul\_gaussMomentJ}; ratios are unaffected, raw $q$-point functions acquire a factor $2^q$. Expanding the source,
\begin{equation}\label{eq:S_series}
S_\mu(a)=\sum_{m\ge0}s^{(\mu)}_m a^m,\qquad s^{(\mu)}_m=\frac{\beta^{m/2-\mu}\,\Gamma(\mu+m/2)}{m!},\qquad S_\mu(0)=\frac{\Gamma(\mu)}{\beta^{\mu}}\leanrefL{Grammar/Fluctuation.lean\#L68}{fluctuation\_zero}.
\end{equation}
The derivative and the Weber recurrence are
\begin{equation}\label{eq:S_derivative_recurrence}
S_\mu'(a)=\beta S_{\mu+1/2}(a)\leanrefL{Grammar/Fluctuation.lean\#L83}{hasDerivAt\_fluctuation},\qquad
S_{\mu+1}(a)=\tfrac a2\,S_{\mu+1/2}(a)+\tfrac\mu\beta\,S_\mu(a)\leanrefL{Grammar/Fluctuation.lean\#L157}{fluctuation\_recurrence},
\end{equation}
and the raising operator of the Weber module acts by $b^\dagger S_\mu=\beta^{1/2}S_{\mu+1/2}$\leanrefL{Grammar/Ladder.lean\#L75}{raiseOp\_fluctuation}. The radial moments are
\[
\int_0^\infty T^{2\mu}e^{-\beta T^2+\beta aT}\,dT=\tfrac12S_{\mu+1/2}(a),\qquad
\int_0^\infty T^{2\mu+1}e^{-\beta T^2+\beta aT}\,dT=\tfrac12S_{\mu+1}(a).
\]

\begin{remark}[Lean conventions]\label{rem:lean_convention}
The fluctuation function, its derivatives, the recurrence and the ladder algebra are formalised in the grammar library (\S4 of the paper); the normalisation identity $S_\mu=2J_{2\mu}$ is new to this note. A blue dot in the margin links the sentence or formula it is attached to with the formal statement that certifies it, in the library \texttt{timaeus-research/grammar} pinned at commit \texttt{\grammarLeanCommit}. A dot certifies exactly the bounded statement next to it, under the hypotheses of the cited declaration; where the prose is stronger than the formal statement, the text says so. Where a Lean statement is only proved at the Gaussian-limit level (level 2 above) the text says so.
\end{remark}

\section{The sampling phase and the resolved covariance}\label{sec:sampling}

\subsection{The standard form and the sign of the fluctuation}

After resolution the log-likelihood ratio takes the standard form
\begin{equation}\label{eq:a_defn}
f(x,u):=\log q(x)-\log p(x\mid\pi(u))=\phi(u)\,a(x,u),\qquad \mathbb E_X\,a(X,u)=\phi(u),
\end{equation}
so that $K(\pi(u))=\mathbb E_Xf(X,u)=\phi(u)^2$; in normal-crossing coordinates $\phi(u)=u^k$ and $K=u^{2k}$ (Watanabe's ``standard form of the likelihood ratio function'', \cite[Main Theorem 6.1]{watanabeAlgebraicGeometryStatistical2009}). Define the centred empirical process of the coefficient and the standard-integral phase
\begin{equation}\label{eq:xi_n_defn}
\zeta_n(u)=\frac1{\sqrt n}\sum_{i=1}^n\big(a(X_i,u)-\phi(u)\big),\qquad
\xi_n(u):=-\zeta_n(u)=\frac1{\sqrt n}\sum_{i=1}^n\big(\phi(u)-a(X_i,u)\big).
\end{equation}

\begin{prop}[The sampling identity]\label{prop:sampling}
Identically for every dataset and every $u$,
\[
\frac1n\sum_{i=1}^nf(X_i,u)=\phi(u)^2+\frac{\phi(u)}{\sqrt n}\,\zeta_n(u)\leanrefL{Grammar/SamplingIdentity.lean\#L32}{sum\_mul\_eq},
\qquad
-\beta\sum_{i=1}^nf(X_i,u)=-\beta n\,\phi(u)^2+\beta\sqrt n\,\phi(u)\,\xi_n(u)\leanrefL{Grammar/SamplingIdentity.lean\#L46}{sampling\_exponent\_eq}.
\]
\end{prop}
Thus the sampling exponent is the exponent $-\beta Nu^{2k}+\beta\sqrt N u^k\xi(u)$ of the standard integral with $N=n$ and $\xi=\xi_n=-\zeta_n$: the phase of the standard integral is \emph{minus} the centred empirical process of the coefficient $a$. This is a purely algebraic statement about the sampling construction; it identifies the asymptotic scale in this construction, not an unconditional equality of two independently introduced parameters.

\begin{remark}[Sign audit against the Lean library]
In the Lean formalisation of the paper the empirical Taylor datum (with a zero-phase amplitude datum) has phase coefficients $n^{-1/2}\sum_i(c_\gamma(X_i)-\mathbb E c_\gamma)$\leanrefL{Grammar/SampleDatum.lean\#L142}{xiCoord\_sampleDatum}\leanrefL{Grammar/AnalyticCertificate.lean\#L165}{dataPhase\_sampleDatum}, entering the standard integral with the sign $+\beta\sqrt N u^k\xi$\leanrefL{Grammar/SamplingCompatibility.lean\#L161}{exp\_sampling\_exponent\_eq\_core\_factor}. By \cref{prop:sampling}, to instantiate this library construction for the likelihood convention \eqref{eq:a_defn} the coefficient family $c_\gamma(x)$ must be chosen as the Taylor coefficients of $-a(x,\cdot)$, equivalently of $\log p-\log q$; the algebra does not itself identify an abstract coefficient family with a model's coefficients. A centred Gaussian limit has the same law under global negation, so the limiting statements are unaffected, but the finite-sample identity is not.
\end{remark}

\begin{remark}[Centring and the certified sampling convention]\label{rem:centring}
The empirical phase is centred. Writing $\zeta_n$ for the normalised centred fluctuation of the coefficient $a$, the sampling convention is $\xi_n=-\zeta_n$. The population mean is retained in the deterministic population exponent $-\beta n\phi^2$, so that the empirical exponent splits exactly into the population exponent and the centred fluctuation term; the deterministic datum $A$ supplies the amplitude, has zero phase, and does not absorb an uncentred mean phase (a fixed datum cannot: $n^{-1/2}\sum_{i\le n}Y_i=n^{-1/2}\sum_{i\le n}(Y_i-\mathbb EY_0)+\sqrt n\,\mathbb EY_0$). In the Lean library this is certified at the sample datum itself, before any limit or expectation. For integrable phase observations the phase of the sample datum is the centred normalised sum $n^{-1/2}\sum_{i\le n}(\xi_{Y_i}(u)-\mathbb E\xi_{Y_0}(u))$\leanrefL{Grammar/SamplingCompatibility.lean\#L81}{phaseEval\_sampleDatum\_of\_integrable} (evaluation commutes with the Bochner mean\leanrefL{Grammar/SamplingCompatibility.lean\#L48}{phaseEvalCLM\_integral}) and its amplitude is that of $A$\leanrefL{Grammar/SamplingCompatibility.lean\#L71}{etaCoord\_sampleDatum\_of\_integrable}; when the coefficient family $c_\gamma(x)$ is the Taylor family of $-a(x,\cdot)$ at the box point $bu$ and $\mathbb Ea(X,bu)=\phi(bu)$, the phase is $\xi_n(u)=-\zeta_n(bu)$\leanrefL{Grammar/SamplingCompatibility.lean\#L102}{evalF\_xiCoord\_sampleDatum\_eq\_neg\_zetaEmp} and
\[
-\beta\sum_{i=1}^nf(X_i,bu)=-\beta n\,\phi(bu)^2+\beta\sqrt n\,\phi(bu)\,\xi_n(u)\leanrefL{Grammar/SamplingCompatibility.lean\#L123}{sampling\_exponent\_eq\_sampleDatum\_phase}.
\]
In the monomial chart $\phi(v)=v^k$ the sampling integrand $e^{-\beta\sum_if(X_i,v)}$ is the phase factor $e^{-\beta nv^{2k}+\beta\sqrt n\,v^k\xi(v)}$ of the box integrand at the sample datum with $N=n$\leanrefL{Grammar/SamplingCompatibility.lean\#L161}{exp\_sampling\_exponent\_eq\_core\_factor}, and the certified box core at the sample datum \emph{is} the sampling integral, $Z(n;D_n)=\int_{(0,b]^d}\eta_A(v)\,v^h\,e^{-\beta\sum_{i\le n}f(X_i,v)}\,dv$\leanrefL{Grammar/SamplingCompatibility.lean\#L188}{dataBoxIntegral\_sampleDatum\_eq\_sampling}. The remaining interface is the identification of the abstract coefficient family with the model's Taylor coefficients (the hypothesis of these statements), not the sign.
\end{remark}

\begin{example}[Normal location]\label{ex:normal_location}
For $X\sim N(0,1)$ and the negative log-likelihood ratio $g_a(x)=a^2/2-ax$ one has $K(a)=a^2/2$ and $\sum_{i=1}^ng_a(X_i)=na^2/2-a\sum_iX_i$\leanrefL{Grammar/EffectiveTemperature.lean\#L115}{sum\_normalLocation}. In the standard form with core coordinate $\rho=a/\sqrt2$, $g_a(x)=\rho\,(\rho-\sqrt2\,x)$\leanrefL{Grammar/EffectiveTemperature.lean\#L122}{normalLocation\_standard\_form}, so $a(x,\rho)=\rho-\sqrt2\,x$ has mean $\rho$ and the sampling phase is $\xi_n=-\zeta_n=\sqrt2\,n^{-1/2}\sum_iX_i$\leanrefL{Grammar/EffectiveTemperature.lean\#L131}{neg\_zetaEmp\_normalLocation}, of variance $2$, not $1$\leanrefL{Grammar/EffectiveTemperature.lean\#L140}{variance\_phase\_normalLocation}. This is a normalisation check of the sampling convention (the factor $\sqrt2$ comes from $\phi=\rho$ against $K=\rho^2$); it certifies neither the resolution presentation nor the remainder.
\end{example}

\begin{remark}[Well-definedness on the exceptional divisor]
Both $a(x,u)$ and $\xi_n(u)$ are defined on the whole chart, including the divisor $\{\phi=0\}$, where $\xi_n(u)=-n^{-1/2}\sum_ia(X_i,u)$. The na\"ive empirical process $\sqrt n(K_n-K)/\sqrt K$ in the original coordinates is not.
\end{remark}

\subsection{The resolved covariance and the variance normalisation}\label{subsec:resolved_covariance}

By the central limit theorem \cite[Theorem 6.2]{watanabeAlgebraicGeometryStatistical2009} (in the Lean library, the $\ell^1$ central limit theorem for the Taylor data\leanrefL{Grammar/L1SeqCLT.lean\#L64}{clt\_l1}) $\xi_n$ converges in law to a centred Gaussian process $G$ with covariance
\begin{equation}\label{eq:resolved_covariance}
C(u,u')=\mathbb E[G(u)G(u')]=\mathbb E_X[a(X,u)a(X,u')]-\phi(u)\phi(u').
\end{equation}
On the divisor the second term vanishes. The diagonal there is fixed by the likelihood normalisation $\mathbb E_Xe^{-f(X,u)}=\int p(x\mid\pi(u))\,dx=1$ (the identity $\mathbb E_qe^{-f(X,u)}=1$ requires $\int_{\{q>0\}}p(x\mid\pi(u))\,dx=1$, i.e.\ that the model place no mass outside the support of $q$; a finite real log-likelihood ratio $q$-almost surely additionally requires $p(\cdot\mid\pi(u))>0$ $q$-almost surely):

\begin{lem}[Variance normalisation]\label{lem:variance_normalisation}
Let $a$ be a real random variable and $\phi\neq0$, $h$ real numbers with $\mathbb E\,e^{-\phi a}=1$ and $\mathbb E\,a=\phi h$ (i.e.\ $\mathbb E[\phi a]=\phi^2h$), and suppose $a$, $a^2$, $e^{-\phi a}$ and $|a|^3e^{|\phi a|}$ are integrable. Then
\begin{equation}\label{eq:variance_bound}
\big|\mathbb E[a^2]-2h\big|\le 2|\phi|\;\mathbb E\big[|a|^3e^{|\phi a|}\big]\leanrefL{Grammar/DivisorVariance.lean\#L51}{abs\_integral\_sq\_sub\_le}.
\end{equation}
\end{lem}
\begin{proof}
From $|e^{-z}-(1-z+z^2/2)|\le|z|^3e^{|z|}$\leanrefL{Grammar/DivisorVariance.lean\#L31}{abs\_exp\_neg\_sub\_le} with $z=\phi a$: integrating, $\mathbb E[e^{-\phi a}-1+\phi a-\phi^2a^2/2]=\phi^2(h-\mathbb E[a^2]/2)$ in absolute value is at most $|\phi|^3\,\mathbb E[|a|^3e^{|\phi a|}]$. (With Taylor's theorem the constant $2$ improves to $1/3$.)
\end{proof}

\begin{cor}[The divisor variance]\label{cor:divisor_variance}
Along any approach to a divisor point through points with $\phi_t\neq0$ (at least eventually)---$\phi_t\to0$, $h_t\to h_0$, with a uniform cubic envelope $\mathbb E[|a_t|^3e^{|\phi_ta_t|}]\le M$---one has $\mathbb E[a_t^2]\to2h_0$\leanrefL{Grammar/DivisorVariance.lean\#L115}{tendsto\_integral\_sq}; if moreover the second moments converge to that of a limit coefficient $a_0$ (for instance $a_t\to a_0$ in $L^2$), then $\mathbb E[a_0^2]=2h_0$ exactly\leanrefL{Grammar/DivisorVariance.lean\#L142}{integral\_sq\_eq\_of\_tendsto}. In the normalised standard form $K=\phi^2$ ($h\equiv1$), under the stated envelope and second-moment continuity assumptions, the covariance diagonal on the divisor is
\begin{equation}\label{eq:variance_normalised}
C\big((0,w),(0,w)\big)=\mathbb E_X\big[a(X,(0,w))^2\big]=2.
\end{equation}
\end{cor}

\begin{remark}[Why the hypothesis $K=\phi^2h$ is needed]
The statement ``$\mathbb E e^{-\phi a}=1$ and $\phi\to0$ imply $\mathbb E a^2\to2$'' is false without control of $\mathbb E[\phi a]$: for $Z\sim N(0,1)$ and $a_\phi=\sigma Z+\phi\sigma^2/2$ one has $\mathbb E e^{-\phi a_\phi}=1$ and $\mathbb E a_\phi^2\to\sigma^2$. Pointwise real analyticity of $a(x,\cdot)$ does not by itself supply the integrable envelope or the $L^2$-continuity; in the Lean library these are hypotheses, to be discharged by the analytic coefficient envelopes of Hypothesis~I.
\end{remark}

\begin{remark}[Relation to the Fisher information]\label{rem:fisher}
For a one-dimensional regular model with true parameter $w_0$, $K(w)=\tfrac12I(w_0)(w-w_0)^2+O((w-w_0)^3)$; with $u=\sqrt{I/2}\,(w-w_0)+O((w-w_0)^2)$ one has $K=u^2$, $k=1$, and $a(x,u)=-s(x)/\sqrt{I/2}+O(u)$ where $s$ is the score, so that $C(0,0)=\mathbb E[s^2]/(I/2)=2$, confirming \eqref{eq:variance_normalised}. In several dimensions the resolved coefficient depends on the blow-up direction. At leading order in a regular model, normalised score directions do give a Fisher-matrix expression for the directional covariance; no coordinate-independent formula for arbitrary resolved charts is needed or claimed here.
\end{remark}

\paragraph{Jets.} At a leaf the coordinates split into dead ones $v$ (set to zero) and alive ones $w$. The Taylor tree produces derivatives $\partial_v^{(\alpha)}G(0,w)$ in the dead directions, and the pairings needed are the jet-covariances $C_{\alpha\beta}(w,w')=\partial_v^{(\alpha)}\partial_{v'}^{(\beta)}C((0,w),(0,w'))$; the special cases are $c(w)=C_{00}(w,w)=2$, $d_\alpha(w)=C_{\alpha0}(w,w)$, $e_{\alpha\beta}(w)=C_{\alpha\beta}(w,w)$, and the bilocal propagator $b(w,w')=C_{00}(w,w')$. That these derivatives are jointly Gaussian and that differentiation commutes with expectation is a statement about limits of Gaussian linear functionals; for the $\ell^1$ Gaussian Taylor data of the library the bounded linear coefficient and evaluation maps are the cleaner route than difference quotients, and the required integrability is a hypothesis (an analytic coefficient envelope), not a consequence of pointwise analyticity. No spatial decay of $b(w,w')$ in $|w-w'|$ is asserted: the covariance can be constant, oscillatory or negative.

\section{Raw Gaussian averages}\label{sec:raw}

Throughout this section $(Y,X_1,X_2)$ is a centred Gaussian vector with $c=\mathbb E Y^2$, $d_i=\mathbb E[X_iY]$, $e=\mathbb E[X_1X_2]$, and
\[
\delta:=1-\frac{\beta c}{2}.
\]

\subsection{The one-point function and its threshold}

\begin{prop}[$Q=0$]\label{prop:Q0}
If $\delta>0$ then $S_\mu(Y)$ is integrable and
\begin{equation}\label{eq:Q0}
\mathbb E\,S_\mu(Y)=\frac{\Gamma(\mu)}{(\beta\delta)^{\mu}}=S_\mu(0)\,\delta^{-\mu};
\end{equation}
if $\delta\le0$ then $\mathbb E_+S_\mu(Y)=+\infty$.
\end{prop}
\begin{proof}
Tonelli and the Gaussian moment generating function $\mathbb E e^{\beta\sqrt y\,Y}=e^{\beta^2cy/2}$ give $\mathbb E_+S_\mu(Y)=\int_0^\infty y^{\mu-1}e^{-\beta\delta y}\,dy$, finite exactly when $\delta>0$.
\end{proof}
In the half-normalisation $J_p$ this is the constant-Gaussian dichotomy formalised in the grammar library\leanrefL{Grammar/GaussianDichotomy.lean\#L67}{lintegral\_gaussMomentJ\_eq}: $\mathbb E_+J_p(X)=J_p(0)(1-\beta v/2)^{-p/2}$ for $\beta v<2$\leanrefL{Grammar/GaussianThreshold.lean\#L116}{lintegral\_gaussMomentJ\_eq\_of\_lt} and $=+\infty$ for $\beta v\ge2$\leanrefL{Grammar/GaussianThreshold.lean\#L124}{lintegral\_gaussMomentJ\_eq\_top\_of\_ge}, packaged as one theorem\leanrefL{Grammar/HeadlineGaussian.lean\#L30}{headline\_gaussian\_dichotomy}; with $S_\mu=2J_{2\mu}$ and $v=c$ this is \eqref{eq:Q0}. On the divisor $c=2$ and the threshold is $\beta<1$: at the physical temperature $\beta=1$ the expected leading coefficient of the Gaussian model is infinite although every sample coefficient is finite.

\begin{remark}[Lean]
The dichotomy is stated in the extended nonnegative reals, so that ``$=+\infty$'' is a genuine value; a Bochner integral of a non-integrable function is $0$ in Lean and must not be used to express divergence.
\end{remark}

\subsection{Insertions: $Q=1,2$}

\begin{prop}[$Q=1,2$]\label{prop:Q12}
If $\delta>0$ then $X_1S_\mu(Y)$ and $X_1X_2S_\mu(Y)$ are integrable and
\begin{align}
\mathbb E[X_1S_\mu(Y)]&=\frac{\beta d_1\,\Gamma(\mu+\frac12)}{(\beta\delta)^{\mu+1/2}},\label{eq:Q1}\\
\mathbb E[X_1X_2S_\mu(Y)]&=\frac{e\,\Gamma(\mu)}{(\beta\delta)^{\mu}}+\frac{\beta^2d_1d_2\,\Gamma(\mu+1)}{(\beta\delta)^{\mu+1}}.\label{eq:Q2}
\end{align}
In particular $\mathbb E[X_1S_{\lambda+1/2}(Y)]=d_1\Gamma(\lambda+1)\beta^{-\lambda}\delta^{-(\lambda+1)}$.
\end{prop}
\begin{proof}
Integrate the tilted Gaussian identities $\mathbb E[X_ie^{\theta Y}]=\theta d_ie^{c\theta^2/2}$\leanrefL{Grammar/GaussianTilted.lean\#L319}{integral\_mul\_exp\_gaussianVector} and $\mathbb E[X_1X_2e^{\theta Y}]=(e+\theta^2d_1d_2)e^{c\theta^2/2}$\leanrefL{Grammar/GaussianTilted.lean\#L342}{integral\_mul\_mul\_exp\_gaussianVector} against $y^{\mu-1}e^{-\beta y}dy$ with $\theta=\beta\sqrt y$; Isserlis' theorem is not needed. The exchange of the Gaussian expectation with the $y$-integral is Fubini\leanrefL{Grammar/GaussianInsertion.lean\#L108}{integral\_mul\_fluctuation\_eq}, whose integrability hypothesis is reduced to the tilted second moment by $|x|\le\frac{1+x^2}2$ and $|xy|\le\frac{x^2+y^2}2$, and the remaining $y$-integral is the Gamma integral $\int_0^\infty y^{\mu-1}e^{-\beta y}(\beta\sqrt y)^ke^{\beta^2cy/2}\,dy=\beta^k\Gamma(\mu+\tfrac k2)(\beta\delta)^{-(\mu+k/2)}$\leanrefL{Grammar/GaussianInsertion.lean\#L87}{integral\_radialKernel\_mul\_tilt}. This gives \eqref{eq:Q1}\leanrefL{Grammar/GaussianInsertion.lean\#L307}{integral\_coord\_mul\_fluctuation} and \eqref{eq:Q2}\leanrefL{Grammar/GaussianInsertion.lean\#L333}{integral\_coord\_mul\_coord\_mul\_fluctuation}, together with the integrability claims.
\end{proof}
The same argument with $k=0$ gives the Bochner form of \eqref{eq:Q0} for $\delta>0$, including integrability\leanrefL{Grammar/GaussianInsertion.lean\#L284}{integral\_fluctuation\_gaussianVector}. The polynomial-growth Stein identity of \cref{sec:quartet} does not apply directly to the exponentially growing $S_\mu$; the formal route is the tilted moment generating function, and the formalisation is for a Gaussian vector $G=AZ$ with $Z$ standard Gaussian, so that $(Y,X_1,X_2)$ are three coordinates of $G$ and $c,d_i,e$ are entries of $AA^{\mathsf T}$ (every centred Gaussian vector has this form).

\subsection{The bilocal two-point function}\label{subsec:bilocal}

Let $(X,Y)$ be centred Gaussian with variances $c,c'$ and covariance $b$, and put
\[
A=\beta\Big(1-\frac{\beta c}2\Big),\qquad B=\beta\Big(1-\frac{\beta c'}2\Big),\qquad H=\beta^2b.
\]

\begin{prop}[Bilocal integral and thresholds]\label{prop:bilocal}
In the extended nonnegative reals,
\begin{equation}\label{eq:bilocal_integral}
\mathbb E_+\big[S_\lambda(X)S_\lambda(Y)\big]=\int_0^\infty\!\!\int_0^\infty t^{\lambda-1}s^{\lambda-1}\,e^{-At-Bs+H\sqrt{ts}}\,dt\,ds.\leanrefL{Grammar/BilocalGaussian.lean\#L174}{lintegral\_fluctuation\_mul\_fluctuation}
\end{equation}
For $A>0$, $B>0$ it is finite if $H<2\sqrt{AB}$\leanrefL{Grammar/BilocalGaussian.lean\#L239}{lintegral\_bilocalIntegrand\_lt\_top}, and on the critical line $H=2\sqrt{AB}$ it is finite if and only if $\lambda<1/4$\leanrefL{Grammar/BilocalCriticalBoundary.lean\#L434}{bilocal\_lintegral\_lt\_top\_iff\_of\_critical} (on the critical line the exponent is the perfect square $-(\sqrt{At}-\sqrt{Bs})^2$, and the substitution $s=(A/B)tz$ followed by the Gamma integral in $t$ reduces the double integral to $(A/B)^\lambda\Gamma(2\lambda)A^{-2\lambda}\int_0^\infty z^{\lambda-1}|1-\sqrt z|^{-4\lambda}\,dz$\leanrefL{Grammar/BilocalCriticalBoundary.lean\#L345}{lintegral\_bilocalIntegrand\_critical\_eq}, whose only new condition is the integrability of $|z-1|^{-4\lambda}$ at $z=1$\leanrefL{Grammar/BilocalCriticalBoundary.lean\#L185}{lintegral\_criticalProfile\_lt\_top\_iff}; for the Gaussian two-point function this is \leanrefL{Grammar/BilocalCriticalBoundary.lean\#L451}{lintegral\_fluctuation\_mul\_fluctuation\_lt\_top\_iff\_of\_critical}); in particular it is infinite for $A,B>0$ and $H>2\sqrt{AB}$\leanrefL{Grammar/BilocalDivergence.lean\#L44}{lintegral\_bilocalIntegrand\_eq\_top}. When $A,B>0$ and $|H|<2\sqrt{AB}$ the cross-pairing series converges absolutely\leanrefL{Grammar/BilocalSeries.lean\#L182}{summable\_bilocalCoeff} and
\begin{equation}\label{eq:bilocal_series}
\mathbb E\big[S_\lambda(X)S_\lambda(Y)\big]=\sum_{r\ge0}\frac{H^r}{r!}\,\frac{\Gamma(\lambda+r/2)^2}{(AB)^{\lambda+r/2}}.\leanrefL{Grammar/BilocalSeries.lean\#L234}{integral\_fluctuation\_mul\_fluctuation\_eq\_tsum}
\end{equation}
\end{prop}
\begin{proof}
Tonelli and the joint moment generating function $\mathbb E\,e^{xX+yY}=e^{(cx^2+2bxy+c'y^2)/2}$ give \eqref{eq:bilocal_integral} with $x=\beta\sqrt t$, $y=\beta\sqrt s$. For $A,B>0$ and $H<2\sqrt{AB}$ the AM--GM bound $H\sqrt{ts}\le\rho(At+Bs)$ with $\rho=\max(H,0)/(2\sqrt{AB})<1$ dominates the integrand by a product of two Gamma integrands; for $H>2\sqrt{AB}$ the exponent is $t\,\psi(u)$ along the ray $s=ut$, with $\psi(A/B)=\sqrt{A/B}\,(H-2\sqrt{AB})>0$, and the integral over a cone around this ray is already infinite. For $|H|<2\sqrt{AB}$, expand $e^{H\sqrt{ts}}$ and integrate term by term: the absolute-convergence hypothesis is the Tonelli computation at $|H|$, finite by the first part, so signed convergence is a consequence of the integrability of the positive integrand at $|H|$ and not an input. At the endpoint $H=2\sqrt{AB}$ (finite iff $\lambda<1/4$, formalised in \cref{prop:bilocal}) the exponent is the perfect square $-(\sqrt{At}-\sqrt{Bs})^2$, vanishing along the interior ray $Bs=At$; the substitution $s=(A/B)tz$ and the Gamma integral in $t$ leave the one-dimensional profile $z^{\lambda-1}|1-\sqrt z|^{-4\lambda}$, whose only new condition is the integrability of $|z-1|^{-4\lambda}$ at $z=1$. If $A<0$ or $B<0$, fixing the other variable in a compact positive interval gives divergence; if $A=0$, $B\ge0$ and $H<0$, integration in $t$ gives a constant multiple of $\int_0^\infty s^{-1}e^{-Bs}\,ds$, which diverges, and the other zero-boundary cases are immediate or symmetric.
\end{proof}
The Lean results establish the integral identity, finiteness for $A,B>0$ and $H<2\sqrt{AB}$, divergence for $A,B>0$ and $H>2\sqrt{AB}$, the absolutely convergent series for $|H|<2\sqrt{AB}$, and the boundary classification at $H=2\sqrt{AB}$. For $c=c'=2$ the absolutely convergent series is valid when $0<\beta<(1+|b|/2)^{-1}$ and reads
\[
\mathbb E\big[S_\lambda(X)S_\lambda(Y)\big]=\frac1{\beta^{2\lambda}}\sum_{r\ge0}\frac{\Gamma(\lambda+r/2)^2}{r!}\,(\beta b)^r(1-\beta)^{-(2\lambda+r)},
\]
while the integral itself is finite throughout $0<\beta<1$ when $b\le0$ and throughout $0<\beta<(1+b/2)^{-1}$ when $b>0$, with the critical-line qualification above; at $b=2$ the critical value is $\beta=1/2$, where the integral is finite iff $\lambda<1/4$. Finiteness depends on the \emph{sign} of $b$ (a negative covariance helps), absolute convergence of the series on $|b|$. The $r=0$ term is the disconnected part $\mathbb ES_\lambda(X)\,\mathbb ES_\lambda(Y)$; the connected part is the sum over $r\ge1$, in integral form (for $\beta<1$ and $H<2\sqrt{AB}$, i.e.\ $\beta<(1+b/2)^{-1}$ when $b>0$, so that the individual means and the product are finite)
\[
\operatorname{Cov}\big(S_\lambda(X),S_\lambda(Y)\big)=\iint t^{\lambda-1}s^{\lambda-1}e^{-\beta(1-\beta)(t+s)}\big(e^{\beta^2b\sqrt{ts}}-1\big)\,dt\,ds\leanrefL{Grammar/BilocalSeries.lean\#L274}{cov\_fluctuation\_eq\_connected}
\]
The series form $\sum_{r\ge1}$ of the covariance\leanrefL{Grammar/BilocalSeries.lean\#L250}{cov\_fluctuation\_eq\_tsum} and the integrability of $S_\lambda(X)S_\lambda(Y)$ below threshold\leanrefL{Grammar/BilocalGaussian.lean\#L290}{integrable\_fluctuation\_mul\_fluctuation} are formalised as well (rescaling $t,s$ by $\beta$ gives the form $\beta^{-2\lambda}\iint\cdots e^{-(1-\beta)(t+s)}(e^{\beta b\sqrt{ts}}-1)$ of earlier drafts, up to the normalisation factor $4$). The simplest bilocal diagram is the $r=1$ term: two $S_\lambda$-vertices joined by one propagator $b$, each dressed by local tadpoles (\cref{fig:bilocal_diagrams}).

\IfFileExists{bilocal_diagram_figure.tex}{\input{bilocal_diagram_figure}}{}

\begin{prop}[Higher moments]\label{prop:moments}
For $Y\sim N(0,c)$, $c>0$, and real $p>0$: $\mathbb E[S_\lambda(Y)^p]<\infty$ if $\beta cp<2$\leanrefL{Grammar/GaussianPMoment.lean\#L148}{integrable\_fluctuation\_rpow\_gaussianReal}, $\mathbb E_+[S_\lambda(Y)^p]=+\infty$ if $\beta cp>2$\leanrefL{Grammar/GaussianPMoment.lean\#L178}{lintegral\_fluctuation\_rpow\_gaussianReal\_eq\_top}, and at $\beta cp=2$ it is finite if and only if $p(2\lambda-1)<-1$, i.e.\ $\lambda<\frac{p-1}{2p}$\leanrefL{Grammar/GaussianCriticalMoment.lean\#L44}{integrable\_fluctuation\_rpow\_gaussianReal\_iff\_of\_critical}. For the finite mixture $D(G)=\sum_i\rho_iS_\lambda(G_i)$ with $\rho_i>0$ and $G=AZ$, $B=AA^{\mathsf T}$: $\mathbb E[D(G)^p]<\infty$ for $p\ge1$ when $B_{ii}>0$ and $\beta pB_{ii}<2$ for every $i$\leanrefL{Grammar/GaussianPMoment.lean\#L336}{integrable\_quartetD\_rpow}, and $\mathbb E_+[D(G)^p]=+\infty$ when $\beta pB_{ii}>2$ for one $i$\leanrefL{Grammar/GaussianPMoment.lean\#L354}{lintegral\_quartetD\_rpow\_eq\_top}; correlations play no role and the threshold is $c^*=\max_iB_{ii}$.
\end{prop}
\begin{proof}[Proof sketch]
The strict regime uses two-sided Gaussian bounds in place of the asymptotic $S_\lambda(a)\sim2\sqrt{\pi/\beta}\,(a/2)^{2\lambda-1}e^{\beta a^2/4}$: for $0<\eta<1$ the weighted AM--GM inequality $a\sqrt t\le(1-\eta)t+a_+^2/(4(1-\eta))$ gives $S_\lambda(a)\le\Gamma(\lambda)(\beta\eta)^{-\lambda}e^{\beta a_+^2/(4(1-\eta))}$\leanrefL{Grammar/FluctuationSharpBounds.lean\#L59}{fluctuation\_le\_eta}, and restricting the integral to $t\in[a^2/4,(a/2+1)^2]$ gives $S_\lambda(a)\ge e^{-\beta}4^{-\max(\lambda-1,0)}a^{2\lambda-1}e^{\beta a^2/4}$ for $a\ge2$\leanrefL{Grammar/FluctuationSharpBounds.lean\#L92}{le\_fluctuation\_of\_two\_le}. With $\mathbb Ee^{\kappa Y^2}<\infty$ iff $2\kappa c<1$ these give the two strict statements (choose $\eta=(1-\beta cp/2)/2$ for the upper bound). For the critical line one needs the polynomially sharp upper bound $S_\lambda(a)\le Ca^{2\lambda-1}e^{\beta a^2/4}$ for $a\ge2$\leanrefL{Grammar/FluctuationSharpUpper.lean\#L47}{fluctuation\_le\_polynomial\_mul\_gaussian}: completing the square, $S_\lambda(a)=e^{\beta a^2/4}\int_0^\infty t^{\lambda-1}e^{-\beta(\sqrt t-a/2)^2}\,dt$\leanrefL{Grammar/FluctuationSharpUpper.lean\#L26}{fluctuation\_eq\_exp\_mul\_integral}, and the integral is split at the window $t\in[a^2/16,9a^2/16]$, where $t^{\lambda-1}\le c_\lambda a^{2\lambda-2}$ and $\beta(\sqrt t-a/2)^2\ge\frac{16\beta}{25a^2}(t-a^2/4)^2$ (a Gaussian of width $5a/4$), while off the window $(\sqrt t-a/2)^2\ge a^2/16$ and the $\eta=1/10$ bound at temperature $\beta/2$ leaves a factor $e^{-5\beta a^2/288}$. On the critical line the Gaussian factors cancel exactly against the density and the tail test is $\int_2^\infty a^{p(2\lambda-1)}\,da$; the half-line $a\le2$ is controlled by monotonicity of $S_\lambda$ in the phase\leanrefL{Grammar/GaussianCriticalMoment.lean\#L25}{fluctuation\_mono}. For the mixture, the coordinate $G_i$ has law $N(0,B_{ii})$\leanrefL{Grammar/GaussianPMoment.lean\#L271}{gaussianVector\_map\_eval}, Jensen gives $D^p\le(\sum_i\rho_i)^{p-1}\sum_i\rho_iS_\lambda(G_i)^p$\leanrefL{Grammar/GaussianPMoment.lean\#L292}{quartetD\_rpow\_le}, and $D\ge\rho_iS_\lambda(G_i)$ gives the divergence.
\end{proof}
For $c=2$, $\beta<1/p$ is the strict subcritical region of the pointwise $p$-th moment; the endpoint depends on $\lambda$. A finite $p$-th moment of the limiting $D(G)$ does not by itself give a uniform $p$-th moment bound for empirical approximants, and it does not classify moments of continuum spatial integrals: for $p\ge1$, sufficiency on a compact base with $C(x,x)\le c$ and $p\beta c<2$ holds, $\mathbb E[D_\rho(G)^p]\le[\rho(K)\Gamma(\lambda)(\beta(1-p\beta c/2))^{-\lambda}]^p$\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L198}{GaussianField.integrable\_compactD\_rpow} (\cref{prop:uniform_moment}), but necessity does not follow from infinite pointwise moments, and for $0<p<1$ the Jensen direction reverses. The Lean development proves the bilocal strict-regime results described above (for a Gaussian vector $G=AZ$ with $X=G_i$, $Y=G_j$ and $c,c',b$ the entries $B_{ii},B_{jj},B_{ij}$ of $AA^{\mathsf T}$) and the boundary classification on the critical line $H=2\sqrt{AB}$; the divergence when $A\le0$ or $B\le0$ (the necessity of $A,B>0$) is not formalised.

\subsection{Worked examples: the floor-rises leaf}\label{subsec:floor_rises}

Take the exponent data $d=7$, $k_i=1$, $h=(0,0,0,2,2,4,4)$ of the paper: the minimising set is $\{1,2,3\}$, $\lambda=1/2$, the alive coordinates are $w=(u_4,\dots,u_7)$ with weight $w^\mu$, $\mu=(1,1,3,3)$. The leading leaf integral is $\int_{[0,b]^4}w^\mu\eta(0,w)S_{1/2}(G(0,w))\,dw$, and by \cref{prop:Q0} with $c=2$, for $\beta<1$,
\begin{equation}\label{eq:floor_rises_averaged}
\mathbb E\int w^\mu\,\eta(0,w)\,S_{1/2}(G_w)\,dw=\frac{\Gamma(1/2)}{\sqrt{\beta(1-\beta)}}\int_{[0,b]^4}w_4w_5w_6^3w_7^3\,\eta(0,0,0,w)\,dw,
\end{equation}
where for nonnegative $\eta$ Tonelli permits the exchange of the dataset and base integrals and constant variance on the divisor then makes the one-point expectation independent of the base point (for signed $\eta$, assume the corresponding absolute integrability). For two copies of the leaf at $w\neq w'$ the connected two-point function is, by \cref{prop:bilocal} with $\lambda=1/2$,
\[
\operatorname{Cov}\big(S_{1/2}(G_w),S_{1/2}(G_{w'})\big)=\frac1\beta\sum_{r\ge1}\frac{\Gamma(\frac12+\frac r2)^2}{r!}(\beta b)^r(1-\beta)^{-(1+r)},
\qquad\text{$r=1$ term: }\ \frac{b(w,w')}{(1-\beta)^2},
\]
valid for $0<\beta<(1+|b(w,w')|/2)^{-1}$; a uniform sufficient condition for all covariance values with diagonal $2$ is $\beta<1/2$ (earlier drafts had a spurious factor $\pi$).

\section{Self-normalised finite Gaussian posteriors: the quartet}\label{sec:quartet}

The quantities of statistical interest are normalised, and the normalisation is what makes them finite at every temperature. Fix $m\ge1$ base points, weights $\rho_i>0$, and a centred Gaussian vector $G=(G_1,\dots,G_m)$ with covariance $b_{ij}$, $b_{ii}=c$; write $g$ for a value of $G$. Define
\begin{align}
D(g)&=\sum_i\rho_iS_\lambda(g_i)\leanrefL{Grammar/GaussianQuartetDet.lean\#L53}{quartetD},&
W_i(g)&=\frac{\rho_iS_{\lambda+1/2}(g_i)}{D(g)}\leanrefL{Grammar/GaussianQuartetDet.lean\#L60}{quartetW},\\
M_2(g)&=\frac{\sum_i\rho_iS_{\lambda+1}(g_i)}{D(g)}\leanrefL{Grammar/GaussianQuartetDet.lean\#L68}{quartetM2},&
H(g)&=\sum_ig_iW_i(g)\leanrefL{Grammar/GaussianQuartetDet.lean\#L71}{quartetH},\\
V(g)&=c\,M_2(g)-\sum_{i,j}b_{ij}W_i(g)W_j(g)\leanrefL{Grammar/GaussianQuartetDet.lean\#L78}{quartetV}.&&
\end{align}
Under the marked posterior $\pi_g(i,T)\propto\rho_i\,T^{2\lambda-1}e^{-\beta T^2+\beta g_iT}$ on base points and the radial variable, $W_i=\langle T\,\mathbb 1_i\rangle_g$ (the radial partition function in this convention is $D/2$, and the factors cancel in the ratio), $M_2=\langle T^2\rangle_g$, $H=\langle g_iT\rangle_g$ (the pairing of the field with the first moment), and $V$ is the connected two-point function: with $b_{ij}=\langle h_i,h_j\rangle$, $V=\mathbb E_{\pi_g}\|Th_i\|^2-\|\mathbb E_{\pi_g}[Th_i]\|^2$.

\subsection{Deterministic identities and bounds}

\begin{prop}\label{prop:det}
For every $\beta,\lambda>0$ and every $g$:
\begin{enumerate}
\item $D(g)>0$, and $S_\mu(a)>0$ for all $a$.
\item \emph{Schwinger--Dyson}: $M_2(g)=\dfrac\lambda\beta+\dfrac{H(g)}2$\leanrefL{Grammar/GaussianQuartetDet.lean\#L107}{quartetM2\_eq} (the recurrence \eqref{eq:S_derivative_recurrence} summed against $\rho_i$ and divided by $D$).
\item \emph{Self-normalisation bounds}: with $R_1=S_{\lambda+1/2}/S_\lambda$, $R_2=S_{\lambda+1}/S_\lambda$ and $a_+=\max(a,0)$,
\[
R_1(a)^2\le R_2(a)\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L130}{fluctuation\_half\_sq\_le},\qquad
R_2(a)\le\frac{2\lambda}\beta+\frac{a_+^2}4\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L147}{fluctuation\_succ\_le},\qquad
R_1(a)\le\sqrt{\frac{2\lambda}\beta+\frac{a_+^2}4}\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L187}{fluctuation\_half\_le},
\]
the first by Cauchy--Schwarz under the radial measure ($\int y^{\lambda-1}e^{\cdots}(\sqrt y-r)^2\,dy\ge0$), the others from it and the recurrence. Hence $0\le W_i(g)\le\sqrt{2\lambda/\beta}+|g_i|/2$\leanrefL{Grammar/GaussianQuartetDet.lean\#L98}{quartetW\_nonneg}\leanrefL{Grammar/GaussianQuartetDet.lean\#L126}{quartetW\_le}, $0\le M_2(g)\le\sum_i(2\lambda/\beta+g_i^2/4)$: the normalised quantities $W_i,M_2,H,Q,V$ are polynomially bounded in $g$\leanrefL{Grammar/GaussianQuartetDet.lean\#L171}{polyBoundedPi\_quartetW}, while $\log D$ has a quadratic bound (item 4); the raw denominator $D$ itself has exponential-quadratic growth.
\item \emph{Lower bound}: $S_\lambda(a)\ge e^{-2\beta}\lambda^{-1}(1+|a|)^{-2\lambda}$\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L215}{fluctuation\_ge\_lower} (restrict the integral to $0<y<(1+|a|)^{-2}$), so with the Gaussian upper bound $S_\lambda(a)\le e^{\beta a^2/2}(\beta/2)^{-\lambda}\Gamma(\lambda)$, $|\log S_\lambda(a)|\le C_1+C_2a^2$\leanrefL{Grammar/FluctuationSelfNormalised.lean\#L268}{abs\_log\_fluctuation\_le}, and $|\log D(g)|$ is quadratically bounded.
\item \emph{Derivatives}: $\partial_jW_i=\beta\,\delta_{ij}\,\dfrac{\rho_iS_{\lambda+1}(g_i)}{D(g)}-\beta\,W_iW_j$\leanrefL{Grammar/GaussianQuartetDet.lean\#L264}{hasFDerivAt\_quartetW}.
\item \emph{Positivity}: if $b=AA^{\mathsf T}$ with $\sum_kA_{ik}^2=c$, then $0\le V(g)\le c\,M_2(g)$\leanrefL{Grammar/GaussianQuartetDet.lean\#L403}{quartetV\_nonneg}: writing $\sum_{ij}b_{ij}W_iW_j=\sum_k(\sum_iA_{ik}W_i)^2$ and applying Cauchy--Schwarz with the weights $\rho_iS_\lambda(g_i)$ and $S_{\lambda+1/2}^2\le S_\lambda S_{\lambda+1}$ column by column.
\end{enumerate}
\end{prop}

\subsection{Gaussian integration by parts}

\begin{lem}[Stein's identity]\label{lem:stein}
\begin{enumerate}
\item For $Z\sim N(0,v)$, $v\neq0$, and $F\in C^1(\mathbb R)$ with $F,F'$ of polynomial growth, $\mathbb E[ZF(Z)]=v\,\mathbb E[F'(Z)]$\leanrefL{Grammar/GaussianStein.lean\#L165}{gaussianReal\_stein}.
\item For $Z=(Z_0,\dots,Z_n)$ independent standard Gaussians and $H\in C^1$ with $H,\partial_kH$ of polynomial growth, $\mathbb E[Z_kH(Z)]=\mathbb E[\partial_kH(Z)]$\leanrefL{Grammar/GaussianSteinVector.lean\#L192}{stdGaussianPi\_stein}.
\item For $G=AZ$ (covariance $b=AA^{\mathsf T}$, possibly degenerate) and $F\in C^1$ with $F,\partial_jF$ of polynomial growth, $\mathbb E[G_iF(G)]=\sum_jb_{ij}\,\mathbb E[\partial_jF(G)]$\leanrefL{Grammar/GaussianSteinVector.lean\#L286}{gaussianVector\_stein}.
\end{enumerate}
\end{lem}
\begin{proof}
(1) Against the density $\varphi_v$ one has $\varphi_v'(x)=-(x/v)\varphi_v(x)$ and integration by parts on $\mathbb R$, all integrands being integrable since a polynomial times $\varphi_v$ is. (2) Split off the $k$-th coordinate, Fubini, and (1) with the other coordinates frozen. (3) Chain rule for $H=F\circ A$.
\end{proof}
The growth hypothesis matters: the identity is applied to the \emph{normalised} weights $W_i$, which are polynomially bounded by \cref{prop:det}, never to the unnormalised $S_\mu$.

\subsection{The quartet}

\begin{thm}[The self-normalised Gaussian quartet at finite resolution]\label{thm:quartet}
Let $G=AZ$ with $b=AA^{\mathsf T}$ and $b_{ii}=c$ for all $i$, and $\rho_i>0$. For every $\beta,\lambda>0$ all of $W_i,M_2,H,V$ are integrable, and
\begin{equation}\label{eq:ibp_result}
\mathbb E[H(G)]=\beta\,\mathbb E[V(G)]\leanrefL{Grammar/GaussianQuartet.lean\#L110}{integral\_quartetH\_eq}.
\end{equation}
Defining the finite-resolution Gaussian fluctuation parameter $\nu:=\tfrac12\mathbb E[H(G)]$,
\begin{equation}\label{eq:quartet_identities}
\nu\ge0,\qquad \mathbb E[V(G)]=\frac{2\nu}\beta,\qquad \mathbb E[M_2(G)]=\frac\lambda\beta+\nu\leanrefL{Grammar/GaussianQuartet.lean\#L177}{quartet\_identities}.
\end{equation}
\end{thm}
\begin{proof}
Apply \cref{lem:stein}(3) to $F=W_i$ and sum over $i$, using the derivative formula of \cref{prop:det}(5): $\mathbb E[G_iW_i]=\beta b_{ii}\mathbb E[\rho_iS_{\lambda+1}(G_i)/D]-\beta\sum_jb_{ij}\mathbb E[W_iW_j]$, and $\sum_i$ of this is $\beta(c\,\mathbb E M_2-\mathbb E\sum_{ij}b_{ij}W_iW_j)=\beta\,\mathbb EV$. The identities follow from \eqref{eq:ibp_result}, $V\ge0$, and the Schwinger--Dyson identity integrated.
\end{proof}

\begin{cor}[The Bayes-quartet algebra]\label{cor:quartet_algebra}
With $\mathbb E V=2\nu/\beta$,
\[
\frac\lambda\beta+\nu-2\nu=\frac\lambda\beta-\nu,\qquad
\frac\lambda\beta+\nu-\frac{\mathbb EV}2=\frac{\lambda-\nu}\beta+\nu,\qquad
\frac\lambda\beta-\nu-\frac{\mathbb EV}2=\frac{\lambda-\nu}\beta-\nu\leanrefL{Grammar/GaussianQuartet.lean\#L205}{bayes\_quartet}.
\]
\end{cor}
These are the algebraic combinations appearing in Watanabe's four expected-error formulas (their identification with coefficients of a statistical model requires the transfer and remainder hypotheses of \cref{sec:grammar}): the two-leg amplitude $\mathbb E\langle T^2\rangle=\lambda/\beta+\nu$ (generalisation), the training correction $-2\nu$ from $\mathbb E\langle T^2-GT\rangle$, and the predictive-variance correction $-\tfrac12\mathbb EV=-\nu/\beta$ distinguishing Bayes from Gibbs. In the diagrammatic reading, $\lambda/\beta$ is the contact term (no propagator), $\pm\nu$ the one-propagator amplitude, and $-\nu/\beta$ the connected two-point bubble (local tadpole minus bilocal cross-pairing).

\begin{remark}[What is and is not claimed]
\Cref{thm:quartet} is a statement about Gaussian-limit posteriors at finite resolution, for every $\beta>0$: no restriction $\beta<1$, no analytic continuation, no Isserlis theorem, no Malliavin calculus. It does \emph{not} identify $\nu$ with the statistical singular fluctuation of a model, and it does not prove the four expected finite-sample error expansions; those require the posterior transfer theorems of the grammar library together with uniform-integrability and predictive Taylor-remainder hypotheses (\cref{sec:grammar}). The integrability for every $\beta$ is the self-normalisation phenomenon: extreme values of $S_\lambda(G_i)$ appear in numerator and denominator alike.
\end{remark}

\section{The expected log-evidence by covariance interpolation}\label{sec:interpolation}

For $s\in[0,1]$ let $D_s(g)=\sum_i\rho_iS_\lambda(\sqrt s\,g_i)$ and let $V_s(g)$ be the expression $V$ of \cref{sec:quartet} evaluated at $\sqrt s\,g$ with the original covariance $b$.

\begin{prop}[Covariance interpolation]\label{prop:interpolation}
$L(s)=\mathbb E\log D_s(G)$ is continuous on $[0,1]$\leanrefL{Grammar/CovarianceInterpolation.lean\#L338}{continuousOn\_interpL}, differentiable on $(0,1)$, with
\[
L'(s)=\frac{\beta^2}2\,\mathbb E[V_s(G)]\leanrefL{Grammar/CovarianceInterpolation.lean\#L293}{hasDerivAt\_interpL}\ge0,\leanrefL{Grammar/CovarianceInterpolation.lean\#L370}{interpV\_nonneg}
\qquad\text{hence}\qquad
\mathbb E\log D(G)=\log\Big(\Gamma(\lambda)\beta^{-\lambda}\sum_i\rho_i\Big)+\frac{\beta^2}2\int_0^1\mathbb E[V_s(G)]\,ds\leanrefL{Grammar/CovarianceInterpolation.lean\#L394}{integral\_log\_quartetD\_eq}\ \ge\ \log D_0.\leanrefL{Grammar/CovarianceInterpolation.lean\#L410}{log\_quartetD\_zero\_le\_integral}
\]
\end{prop}
\begin{proof}[Proof sketch]
The pathwise derivative $\partial_s\log D_s=\frac\beta{2\sqrt s}\sum_ig_iW_i(\sqrt sg)=\frac{\beta}{2s}H(\sqrt s g)$ contains $1/\sqrt s$; on $s>0$ Stein's identity (\cref{lem:stein}) converts $\mathbb E[g_iW_i(\sqrt sg)]$ into $\sqrt s\,\beta\,\mathbb E[V_s]$ by the same computation as \cref{thm:quartet}, and the quadratic bound on $|\log D|$ (\cref{prop:det}(4)) gives the domination needed to differentiate under the expectation and to extend continuously to $s=0$, where $D_0=\sum_i\rho_iS_\lambda(0)$ is deterministic. In the formalisation $\sqrt s\,G$ is the Gaussian vector with matrix $\sqrt s\,A$, whose covariance is $sb$, so the scale-$s$ Stein identity $\mathbb E H(\sqrt sG)=\beta s\,\mathbb E V_s(G)$\leanrefL{Grammar/CovarianceInterpolation.lean\#L237}{integral\_quartetH\_scaled} is \cref{thm:quartet} for that vector, and the derivative is taken under the integral on a neighbourhood $(s_0/2,2)$ of each $s_0\in(0,1)$ with a polynomial dominating function; the quadratic bound used is $|\log D(g)|\le|\log\sum_i\rho_i|+|\log\rho_j|+\sum_i|\log S_\lambda(g_i)|$\leanrefL{Grammar/CovarianceInterpolation.lean\#L92}{abs\_log\_quartetD\_le}. Pathwise differentiability at $s=0$ is never asserted.
\end{proof}
This is exact and holds for every $\beta>0$. It is not the formal cumulant expansion of $\mathbb E\log D$ around $\bar D=\mathbb ED$ (\cref{app:heuristic}): on the divisor model $\bar D=\infty$ for $\beta\ge1$, so that expansion is not even defined there, while the interpolation identity is.

\subsection{General diagonal and the compact base}\label{subsec:compact_base}

The constant-diagonal hypothesis $b_{ii}=c$ in \cref{thm:quartet,prop:interpolation} is a convenience, not a necessity. With
\[
V(g)=\sum_ib_{ii}\,\frac{\rho_iS_{\lambda+1}(g_i)}{D(g)}-\sum_{i,j}b_{ij}W_i(g)W_j(g)\leanrefL{Grammar/GaussianQuartetGeneral.lean\#L37}{quartetVgen}
\]
(which reduces to $cM_2-Q$ when the diagonal is constant), the column-wise Cauchy--Schwarz inequality gives $0\le V\le\sum_ib_{ii}\rho_iS_{\lambda+1}(g_i)/D$\leanrefL{Grammar/GaussianQuartetGeneral.lean\#L86}{quartetVgen\_nonneg}, Gaussian integration by parts gives $\mathbb E[H(G)]=\beta\,\mathbb E[V(G)]$ for every $G=AZ$\leanrefL{Grammar/GaussianQuartetGeneral.lean\#L132}{integral\_quartetH\_eq\_gen}, and the interpolation identity and the inequality $\mathbb E\log D(G)\ge\log D_0$ hold without any diagonal hypothesis\leanrefL{Grammar/GaussianQuartetGeneral.lean\#L287}{integral\_log\_quartetD\_eq\_gen}\leanrefL{Grammar/GaussianQuartetGeneral.lean\#L300}{log\_quartetD\_zero\_le\_integral\_gen}. This is the form needed on a compact base, where the variance $C(x,x)$ of the field is not constant.

Let $K$ be a nonempty compact metric space with a finite Borel measure $\rho\neq0$, $C$ a continuous symmetric positive-semidefinite kernel on $K$\leanrefL{Grammar/CompactBaseKernel.lean\#L39}{PSDKernel}, and for $g\in C(K)$ put
\[
D_\rho(g)=\int_KS_\lambda(g(x))\,d\rho(x)\leanrefL{Grammar/CompactBaseQuantise.lean\#L104}{compactD},\qquad
H_\rho(g)=\frac{\int_Kg\,S_{\lambda+1/2}(g)\,d\rho}{D_\rho(g)}\leanrefL{Grammar/CompactBaseQuantise.lean\#L112}{compactH},\qquad
V_\rho(g)=\frac{\int_KC(x,x)S_{\lambda+1}(g(x))\,d\rho(x)}{D_\rho(g)}-\frac{\iint C(x,y)S_{\lambda+1/2}(g(x))S_{\lambda+1/2}(g(y))\,d\rho\,d\rho}{D_\rho(g)^2}\leanrefL{Grammar/CompactBaseKernel.lean\#L159}{compactV}.
\]
A \emph{Gaussian field} with kernel $C$ is a random continuous function $G\colon\Omega\to C(K)$ with measurable evaluations, $\mathbb E\|G\|_\infty^2<\infty$, and, for every finite family of points $x_1,\dots,x_m$ (repetitions allowed), the law of $(G(x_i))_i$ equal to that of the centred Gaussian vector with covariance $(C(x_i,x_j))_{ij}$\leanrefL{Grammar/CompactBaseFinite.lean\#L209}{GaussianField}. The finite-dimensional laws are stated as evaluation pushforwards, so no Gaussian process is constructed and no common Gaussian source space is assumed.

\begin{prop}[The quartet on a compact base]\label{prop:compact_base}
For every $\beta,\lambda>0$ and $g\in C(K)$ with $\|g\|_\infty\le R$:
\begin{enumerate}
\item $D_\rho(g)>0$\leanrefL{Grammar/CompactBaseQuantise.lean\#L162}{compactD\_pos} and $|\log D_\rho(g)|\le|\log\rho(K)|+C_{\beta,\lambda}+\tfrac\beta2R^2+2\lambda R$\leanrefL{Grammar/CompactBaseQuantise.lean\#L173}{abs\_log\_compactD\_le}; $M_{2,\rho}(g)\le2\lambda/\beta+R^2/4$\leanrefL{Grammar/CompactBaseKernel.lean\#L330}{compactM2\_le} and $|H_\rho(g)|\le R(\sqrt{2\lambda/\beta}+R/2)$\leanrefL{Grammar/CompactBaseKernel.lean\#L351}{abs\_compactH\_le}; if $C(x,x)\le c$ then $0\le V_\rho(g)\le c\,(2\lambda/\beta+R^2/4)$\leanrefL{Grammar/CompactBaseKernel.lean\#L319}{compactV\_nonneg}\leanrefL{Grammar/CompactBaseKernel.lean\#L397}{compactV\_le}. The bounds do not depend on any partition of $K$.
\item (Mass-preserving atomic approximation.) For every $\varepsilon>0$ there is a measurable finite-range map $q\colon K\to K$ with $d(x,q(x))<\varepsilon$\leanrefL{Grammar/CompactBaseQuantise.lean\#L40}{exists\_measurable\_finiteRange\_approx}; the pushforwards $\rho_n=(q_n)_*\rho$ along a sequence with mesh $\to0$ have $\rho_n(K)=\rho(K)$, and for each fixed $g$ the quantities $D_{\rho_n}(g),\log D_{\rho_n}(g),H_{\rho_n}(g),V_{\rho_n}(g)$ converge to those of $\rho$\leanrefL{Grammar/CompactBaseQuantise.lean\#L245}{tendsto\_compactD\_map}\leanrefL{Grammar/CompactBaseQuantise.lean\#L252}{tendsto\_log\_compactD\_map}\leanrefL{Grammar/CompactBaseQuantise.lean\#L290}{tendsto\_compactH\_map}\leanrefL{Grammar/CompactBaseKernel.lean\#L424}{tendsto\_compactV\_map}. On each $\rho_n$ every quantity is the finite quartet quantity of the evaluation vector at the atoms of positive mass\leanrefL{Grammar/CompactBaseFinite.lean\#L188}{compactV\_map\_eq}. Positivity of the bilocal form passes to the limit, so $V_\rho\le\langle rC(x,x)\rangle$ for every positive-semidefinite kernel\leanrefL{Grammar/CompactBaseKernel.lean\#L255}{compactQ\_nonneg}; the lower bound $V_\rho\ge0$ is a pointwise AM--GM inequality using $C(x,y)^2\le C(x,x)C(y,y)$\leanrefL{Grammar/CompactBaseKernel.lean\#L259}{compactQnum\_le}\leanrefL{Grammar/CompactBaseKernel.lean\#L319}{compactV\_nonneg}.
\item For a Gaussian field $G$ with kernel $C$,
\[
\mathbb E[H_\rho(G)]=\beta\,\mathbb E[V_\rho(G)]\leanrefL{Grammar/CompactBaseGaussian.lean\#L212}{integral\_compactH\_eq},\qquad
\mathbb E\log D_\rho(G)=\log\big(\rho(K)\beta^{-\lambda}\Gamma(\lambda)\big)+\frac{\beta^2}2\int_0^1\mathbb E\big[V_\rho(\sqrt s\,G)\big]\,ds\leanrefL{Grammar/CompactBaseGaussian.lean\#L224}{integral\_log\_compactD\_eq}\ \ge\ \log D_\rho(0).\leanrefL{Grammar/CompactBaseGaussian.lean\#L294}{log\_compactD\_zero\_le\_integral}
\]
\end{enumerate}
\end{prop}
\begin{proof}[Proof sketch]
On each $\rho_n$ the identities are \cref{thm:quartet,prop:interpolation} in their general-diagonal form, applied to the Gaussian vector of evaluations at the atoms\leanrefL{Grammar/CompactBaseFinite.lean\#L251}{integral\_compactH\_map\_eq}\leanrefL{Grammar/CompactBaseFinite.lean\#L298}{integral\_log\_compactD\_map\_eq}. The passage to $\rho$ is dominated convergence in $\omega$: the bounds of (1), applied with $R=\|G(\omega)\|_\infty$, are all at most a constant times $1+\|G(\omega)\|_\infty^2$, which is integrable by hypothesis\leanrefL{Grammar/CompactBaseGaussian.lean\#L119}{tendsto\_integral\_compactH\_map}\leanrefL{Grammar/CompactBaseGaussian.lean\#L160}{tendsto\_integral\_log\_compactD\_map}; for the interpolation identity the $s$-integrals converge by a second dominated convergence with the constant bound $\tfrac{\beta^2}2c\,(2\lambda/\beta+\mathbb E\|G\|_\infty^2/4)$, continuity in $s$ on the quantised side coming from the finite theory. The integrated identity is used throughout; no derivative at $s=0$ and no uniformity over sup-norm balls of $C(K)$ is asserted, and finite-dimensional Gaussianity is not claimed to imply the second-moment hypothesis (a Gaussian Borel law on $C(K)$ does, by Fernique's theorem; see the paragraph on the Gaussian Banach law below).
\end{proof}

\section{Relation to the stochastic theorems of the grammar library}\label{sec:grammar}

This section connects the Gaussian-limit identities of \cref{sec:raw,sec:quartet,sec:interpolation} with the finite-sample theorems of the grammar library. The logical order is the following. An exact identity for the annealed evidence shows why the raw dataset average is not the object of interest (\cref{subsec:annealed}). Convergence in distribution of the scaled evidence upgrades to convergence of expectations only under a uniform moment bound (\cref{subsec:bridge}). That bound is supplied for finite-$n$ certified box cores by a deterministic-weight estimate whose only probabilistic input is a full-box exponential-moment bound on the empirical phase (\cref{subsec:uniform_moments}); for an i.i.d.\ sample the empirical phase inherits a sub-Gaussian proxy from a single observation (\cref{subsec:subgaussian}). The pieces assemble into the annealed sample-datum theorem, whose limiting expectation is identified as a covariance-modified face integral and, at constant face variance, as the population coefficient at an effective temperature (\cref{subsec:assembly}). Everything is conditional on a certified chart-core representation of the evidence; nothing geometric is asserted.

\subsection{The leading posterior is random}\label{subsec:random_posterior}

For a continuous spatial phase $\xi$ on the compact base the grammar library proves that the evidence has leading term $\mathcal F(\xi,\eta)$\leanrefL{Grammar/SpatialPhaseLeading.lean\#L63}{spatialPhase\_tendsto} and, for a continuous nonnegative amplitude with positive face functional and along $N_m\to\infty$, that the posterior law of the energy converges to the evidence-weighted face mixture $\int J_\lambda(\xi(v))\rho_{\xi(v)}\,d\nu(v)/M_\xi$\leanrefL{Grammar/SpatialEnergyLaw.lean\#L346}{spatialEnergyLaw\_tendsto} and that the posterior location concentrates with density $J_\lambda(\xi(v))/M_\xi$\leanrefL{Grammar/SpatialLocationLaw.lean\#L162}{phasePosterior\_tendsto\_faceLocation}. With $\xi=G$ the Gaussian field this is the continuum version of the ratio
\[
\frac{\int\rho(w)\,\phi(w)\,S_\lambda(G_w)\,dw}{\int\rho(w)\,S_\lambda(G_w)\,dw}.
\]
This ratio is \emph{random} already at order $1$ and depends on the covariance structure of $G$: even though $\mathbb ES_\lambda(G_w)$ is independent of $w$ when the variance is constant on the divisor, $\mathbb E[N(G)/D(G)]\neq\mathbb EN(G)/\mathbb ED(G)$ in general. Earlier drafts asserted that the leading ratio is the population ratio and that normalisation first matters at relative order $1/n$; both claims are withdrawn. For a spatially constant phase the common factor $S_\lambda$ cancels from location-only posterior ratios, but it need not cancel from energy observables, and no general statement about the order at which normalisation matters follows. An observable such as $K$ itself carries a $1/n$ scale, while the limiting spatial posterior weights fluctuate at order $1$.

\subsection{The exact annealed identity}\label{subsec:annealed}

For likelihood ratios the evidence is $Z_n(\beta)=\int\prod_{i=1}^ne^{-\beta f(X_i,u)}\,\pi(du)$, so independence and Tonelli give
\begin{equation}\label{eq:annealed}
\mathbb E_+Z_n(\beta)=\int\big(\mathbb E\,e^{-\beta f(X,u)}\big)^n\,\pi(du)\leanrefL{Grammar/AnnealedIdentity.lean\#L72}{lintegral\_annealedZ},\qquad\text{and}\qquad \mathbb E\,Z_n(1)=\pi(W)\leanrefL{Grammar/AnnealedIdentity.lean\#L91}{lintegral\_annealedZ\_one}
\end{equation}
under the likelihood normalisation $\mathbb E e^{-f(X,u)}=1$. The typical scale $n^{-\lambda}(\log n)^{m-1}$ of $Z_n$ therefore does not describe the raw annealed evidence at $\beta=1$: the annealed/quenched distinction is a sharp identity, not a cancellation of divergent factors. The same phenomenon appears in the Gaussian limit.

\begin{cor}[The Gaussian-limit denominator]\label{cor:denominator}
For the finite-resolution denominator $D(G)=\sum_i\rho_iS_\lambda(G_i)$ with positive weights $\rho_i>0$ and constant covariance diagonal $c$: if $\delta=1-\beta c/2>0$ then $D(G)$ is integrable and
\[
\mathbb ED(G)=\Gamma(\lambda)(\beta\delta)^{-\lambda}\sum_i\rho_i\leanrefL{Grammar/GaussianDenominator.lean\#L110}{integral\_quartetD};
\]
if $\beta c\ge2$ then $\mathbb E_+D(G)=+\infty$\leanrefL{Grammar/GaussianDenominator.lean\#L131}{lintegral\_quartetD\_eq\_top} and $D(G)$ is not integrable\leanrefL{Grammar/GaussianDenominator.lean\#L152}{not\_integrable\_quartetD}. On the divisor, $c=2$: $\mathbb ED(G)=\Gamma(\lambda)[\beta(1-\beta)]^{-\lambda}\sum_i\rho_i$ for $0<\beta<1$ and $+\infty$ for $\beta\ge1$.
\end{cor}
\begin{proof}
The one-point Tonelli identity $\mathbb E_+S_\lambda(G_j)=\int_0^\infty t^{\lambda-1}e^{-\beta(1-\beta B_{jj}/2)t}\,dt$\leanrefL{Grammar/GaussianDenominator.lean\#L44}{lintegral\_fluctuation\_gaussianVector}, summed over $j$.
\end{proof}

The continuum version holds for a Gaussian field on a compact base (\cref{subsec:compact_base}). The one-point laws give $\mathbb Ee^{tG(x)}=e^{C(x,x)t^2/2}$\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L45}{GaussianField.lintegral\_exp\_eval}, and Tonelli over $\Omega\times K$ gives, when $\beta C(x,x)<2$ everywhere on $K$,
\begin{equation}\label{eq:compact_first_moment}
\mathbb ED_\rho(G)=\Gamma(\lambda)\int_K\big[\beta(1-\tfrac\beta2C(x,x))\big]^{-\lambda}\,d\rho(x)\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L145}{GaussianField.integral\_compactD\_eq},
\end{equation}
which for a constant diagonal $C(x,x)=c$ reads
\[
\mathbb ED_\rho(G)=\rho(K)\Gamma(\lambda)(\beta\delta)^{-\lambda}=D_\rho(0)\,(1-\tfrac{\beta c}2)^{-\lambda}\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L179}{GaussianField.integral\_compactD\_eq\_of\_const\_diag}\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L188}{GaussianField.integral\_compactD\_eq\_compactD\_zero\_mul},
\]
while $\mathbb E_+D_\rho(G)=+\infty$ as soon as $\beta C(x,x)\ge2$ on a set of positive $\rho$-measure\leanrefL{Grammar/CompactBaseFirstMoment.lean\#L127}{GaussianField.lintegral\_compactD\_eq\_top} (an overcritical variance on a $\rho$-null set does not force this). Correlations do not enter the first moment; they enter $\mathbb E\log D$, $Q$ and $V$. The three quantities $\log D_\rho(0)$, $\mathbb E\log D_\rho(G)$ and $\log\mathbb ED_\rho(G)$ are distinct: the second is finite for every $\beta>0$ (\cref{prop:compact_base}), the third only below the exponential-moment threshold, where Jensen gives $\mathbb E\log D_\rho(G)\le\log\mathbb ED_\rho(G)$ and not an identification; neither identifies the mean limiting empirical coefficient with the population coefficient. The first-moment formula uses the compactness of $K$ and the continuity of $C$, through the continuity of $x\mapsto[\beta(1-\beta C(x,x)/2)]^{-\lambda}$; pointwise strictness of $\beta C(x,x)<2$ on an arbitrary measurable base would not by itself give integrability.

\subsection{From convergence in distribution to expectations}\label{subsec:bridge}

\begin{prop}[Expectation bridge]\label{prop:bridge}
Let $X_n$ and $Z$ be real random variables, on possibly different probability spaces, with $X_n\Rightarrow Z$.
\begin{enumerate}
\item If $\sup_n\mathbb E|X_n|^p\le M$ for some $p>1$, then $Z$ is integrable and $\mathbb EX_n\to\mathbb EZ$\leanrefL{Grammar/ExpectationBridge.lean\#L207}{tendsto\_integral\_of\_tendstoInDistribution\_of\_moment}.
\item Conversely, if $X_n\ge0$, $Z\ge0$ and $\mathbb E_+Z=+\infty$, then $\mathbb E_+X_n\to+\infty$\leanrefL{Grammar/ExpectationBridge.lean\#L253}{tendsto\_lintegral\_top\_of\_tendstoInDistribution}.
\end{enumerate}
\end{prop}
\begin{proof}[Proof sketch]
Clip at level $R$, use weak convergence for the clipped variables, and bound the clipping error by $|x-T_R(x)|\le|x|^p/R^{p-1}$\leanrefL{Grammar/ExpectationBridge.lean\#L52}{abs\_sub\_clipR\_le}; the moment bound passes to $Z$ through bounded truncations of $|x|^p$.
\end{proof}

Applied to \cref{cor:denominator}: if the scaled empirical denominators converge in distribution to $D(G)$ with a uniform $p$-th moment bound, their expectations converge to $\Gamma(\lambda)(\beta\delta)^{-\lambda}\sum_i\rho_i$ below threshold\leanrefL{Grammar/ExpectationBridge.lean\#L307}{tendsto\_integral\_quartetD\_of\_tendstoInDistribution}, while at $\beta c\ge2$ their $\mathbb E_+$ diverge\leanrefL{Grammar/ExpectationBridge.lean\#L321}{tendsto\_lintegral\_top\_of\_tendstoInDistribution\_quartetD}: no uniform integrability is possible there. This is a theorem about a raw leading coefficient, not the expected Bayes-error theorem, which uses the normalised quantities of \cref{thm:quartet}. Scalar convergence in distribution suffices for a scalar observable; a joint law is needed only earlier, to deduce convergence of a ratio or another multivariate functional from that of its components.

\subsection{Uniform moments from pointwise exponential moments}\label{subsec:uniform_moments}

The bridge needs a uniform $p$-th moment bound for the scaled finite-$n$ evidence. The following estimate produces one from a pointwise exponential-moment bound, with no Gaussian field, no supremum tail and no independence across base points.

\begin{prop}[Uniform moments of the leading coefficient from pointwise exponential moments]\label{prop:uniform_moment}
Let $(K,\rho)$ be a finite measure space, $X\colon\Omega\times K\to\mathbb R$ jointly measurable, and suppose only the pointwise bound $\mathbb Ee^{tX(x)}\le e^{ct^2/2}$ for $t\ge0$ and every $x$. Then for $p\ge1$ with $p\beta c<2$,
\[
\mathbb E\Big[\Big(\int_KS_\lambda(X(x))\,d\rho(x)\Big)^p\Big]\le\Big[\rho(K)\Gamma(\lambda)\big(\beta(1-p\beta c/2)\big)^{-\lambda}\Big]^p\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L125}{lintegral\_compactD\_rpow\_le\_of\_subgaussian}.
\]
In particular, for bounded independent observations $Z_i(x)\in[l,h]$ the normalised empirical field $\xi_n(x)=n^{-1/2}\sum_{i<n}(Z_i(x)-\mathbb EZ_i(x))$\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L244}{empiricalField} satisfies the hypothesis with $c=((h-l)/2)^2$ (Hoeffding), so $\mathbb E[D_\rho(\xi_n)^p]$ is bounded uniformly in $n$\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L260}{lintegral\_compactD\_rpow\_empirical\_le}.
\end{prop}
\begin{proof}[Proof sketch]
With $\alpha=\beta(1-p\beta c/2)$, write $S_\lambda(a)=\int e^{-(\beta-\alpha)t+\beta a\sqrt t}\,\gamma_{\lambda,\alpha}(dt)$ against the Gamma weight $\gamma_{\lambda,\alpha}(dt)=t^{\lambda-1}e^{-\alpha t}\,dt$\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L77}{ofReal\_fluctuation\_eq\_lintegral\_gammaWeight}, so that $D_\rho(X)$ is a single integral over the finite measure $\rho\otimes\gamma_{\lambda,\alpha}$ of mass $B=\rho(K)\Gamma(\lambda)\alpha^{-\lambda}$. H\"older gives $D^p\le B^{p-1}\int e^{-p(\beta-\alpha)t+p\beta\sqrt t\,X(x)}$, and Tonelli with the exponential-moment bound at $t'=p\beta\sqrt t$ makes the inner expectation exactly $1$, since $p(\beta-\alpha)=p^2\beta^2c/2$. For a random continuous function with measurable evaluations the joint measurability is Carath\'eodory's\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L103}{measurable\_uncurry\_eval}, $D_\rho(G)^p$ is integrable with the same bound\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L298}{integrable\_compactD\_rpow\_of\_subgaussian}, and a pointwise domination $|Y_n|\le K_0D_\rho(\xi_n)$ transfers the uniform moment to $Y_n$\leanrefL{Grammar/UniformMomentSubgaussian.lean\#L336}{moment\_bound\_of\_dominated}.
\end{proof}

The estimate yields uniform integrability whenever it is available for some $p>1$; with this sufficient bound such a choice requires $\beta c<2$, and the case $p=1$ alone does not supply uniform integrability. The input actually used for the finite-$n$ cores is not a domination by the compact-base coefficient but a direct moment bound in terms of the finite-$n$ population weight, obtained by the same H\"older--Tonelli argument on the chart integral itself.

\begin{prop}[Finite-$n$ moments from the deterministic weight]\label{prop:deterministic_weight}
\begin{enumerate}
\item For a finite measure $\nu$ on $U$ and a jointly measurable $H$ with $\mathbb Ee^{pH(\cdot,u)}\le1$ for $\nu$-almost every $u$,
\[
\mathbb E\Big[\Big(\int_Ue^{H(\cdot,u)}\,d\nu(u)\Big)^p\Big]\le\nu(U)^p\leanrefL{Grammar/FiniteWeightMoment.lean\#L40}{lintegral\_rpow\_lintegral\_exp\_le\_mass\_rpow}.
\]
\item For a chart integral $J_n(\omega)=\int_Uw(u)\,a(\omega,u)\,e^{-\beta r_n(u)^2+\beta r_n(u)\xi_n(\omega,u)}\,d\mu(u)$ with $w,r_n\ge0$, $|a|\le M$ and the \emph{full-domain} pointwise bound $\mathbb Ee^{t\xi_n(\cdot,u)}\le e^{ct^2/2}$,
\begin{equation}\label{eq:deterministic_weight}
\mathbb E|A_nJ_n|^p\le\Big(M\,A_n\int_Uw\,e^{-\alpha r_n^2}\,d\mu\Big)^p,\qquad\alpha=\beta\Big(1-\frac{p\beta c}2\Big),\leanrefL{Grammar/FiniteWeightMoment.lean\#L126}{moment\_scaled\_integral\_le\_population\_mass}
\end{equation}
because $-p(\beta-\alpha)r_n^2+\tfrac c2(p\beta r_n)^2=0$.
\item For the certified box model
\[
Z_n=\int_{(0,b]^d}\eta(u)\,u^h\,e^{-\beta nu^{2k}+\beta\sqrt n\,u^k\xi(u)}\,du
\]
with Borel-measurable data of norm $\le M$ (so $|\eta|\le M$ on the box) and the exponential-moment bound for the phase field $\xi$ at every point of the box,
\[
\mathbb E|A_nZ_n|^p\le\Big(M\,A_n\,b^{|h|+d}\,Z^{\mathrm{pop}}_\alpha(nb^{2|k|})\Big)^p,\qquad Z^{\mathrm{pop}}_\alpha(N')=\int_{(0,1]^d}u^he^{-\alpha N'u^{2k}}\,du\leanrefL{Grammar/BoxMomentBound.lean\#L121}{moment\_scaled\_dataBoxIntegral\_le},
\]
uniformly in $n$ under a certified bound $\sup_{n\ge n_0}A_nZ^{\mathrm{pop}}_\alpha(nb^{2|k|})\le C_\alpha$\leanrefL{Grammar/BoxMomentBound.lean\#L195}{uniform\_moment\_scaled\_dataBoxIntegral}.
\end{enumerate}
\end{prop}

The estimate bounds the $p$-th moment by the $p$-th power of a population mass at the reduced temperature $\alpha>0$. It is a sufficient estimate, not a sharp moment classification. The certified bound in (3) is itself a theorem of the library.

\begin{prop}[The population bound]\label{prop:population_bound}
$Z^{\mathrm{pop}}_\alpha$ is the grammar paper's monomial box integral, its standard integral with zero phase, at temperature $\alpha$\leanrefL{Grammar/PopulationBoundDischarge.lean\#L31}{popBoxMass\_eq\_monomialBoxReal}. Its exact leading asymptotics $Z^{\mathrm{pop}}_\alpha(N')\sim K\,N'^{-\lambda_0}(\log N')^{m_0-1}$, with $\lambda_0=\min_i(h_i+1)/(2k_i)$ and $m_0$ the multiplicity, give the bound at the scale $A_n=n^\lambda/(\log n)^{m-1}$ whenever the box exponent pair dominates the scale, that is $\lambda<\lambda_0$ or ($\lambda=\lambda_0$ and $m_0\le m$)\leanrefL{Grammar/PopulationBoundDischarge.lean\#L106}{exists\_population\_bound\_scaleA}\leanrefL{Grammar/PopulationBoundDischarge.lean\#L159}{uniform\_moment\_scaled\_dataBoxIntegral\_of\_dominated}. The joint measurability of the phase field is obtained by clipping to the closed cube\leanrefL{Grammar/BoxMomentBound.lean\#L75}{measurable\_uncurry\_xiField}.
\end{prop}

\begin{remark}
A pointwise exponential-moment bound for the \emph{limiting} face field is not, by itself, a bound for the finite-$n$ field throughout a chart, and a distributional remainder estimate does not supply an $L^p$ error bound. The full-box bound for the finite-$n$ empirical phase is the subject of the next subsection.
\end{remark}

\subsection{The empirical phase of an i.i.d.\ sample is sub-Gaussian}\label{subsec:subgaussian}

Recall the sample datum of \cref{rem:centring}: the phase observations $Y_i=\mathrm{phaseObs}(X_i)$ are elements of the $\ell^1$ data space, and $D_n=n^{-1/2}\sum_{i<n}(Y_i-\mathbb EY_0)+A$ with $A$ a zero-phase amplitude datum. The phase evaluation $x\mapsto\xi_x(u)$ is a continuous linear functional of norm at most one on the data space for $u\in[0,1]^d$\leanrefL{Grammar/SampleDatumMGF.lean\#L50}{phaseEvalCLM}, so the phase field of the sample datum at $u$ is the normalised centred sum of the i.i.d.\ real variables $\xi_{Y_i}(u)$\leanrefL{Grammar/SampleDatumMGF.lean\#L120}{phaseEval\_sampleDatum}. For bounded observations, $\|Y_i\|_{\ell^1}\le M_0$, Hoeffding's lemma gives
\begin{equation}\label{eq:hoeffding_phase}
\mathbb Ee^{t\xi_n(u)}\le e^{M_0^2t^2/2}\qquad\text{for every $n$, every $u\in[0,1]^d$ and every $t$}\leanrefL{Grammar/SampleDatumMGF.lean\#L142}{lintegral\_exp\_phase\_sampleDatum\_le}.
\end{equation}
Boundedness is a convenience, not a necessity. Write
\[
Q_u:=\xi_{Y_0}(u)-\mathbb E\,\xi_{Y_0}(u)
\]
for the centred phase evaluation of a single observation.

\begin{prop}[Inheritance of the sub-Gaussian proxy]\label{prop:subgaussian_phase}
Suppose that $Y_0$ is Bochner integrable (as the coordinate certificate guarantees) and that for some $\kappa\ge0$
\begin{equation}\label{eq:uniform_subgaussian}
\mathbb E\,e^{tQ_u}\le e^{\kappa t^2/2}\qquad\text{for all $t\in\mathbb R$ and all $u\in[0,1]^d$}\leanrefL{Grammar/SubgaussianPhase.lean\#L139}{UniformSubgaussianPhase}.
\end{equation}
Then:
\begin{enumerate}
\item the normalised empirical phase $n^{-1/2}\sum_{i<n}Q_u(X_i)$ is sub-Gaussian with the \emph{same} proxy $\kappa$, for every $n>0$ and $u$\leanrefL{Grammar/SubgaussianPhase.lean\#L167}{hasSubgaussianMGF\_empiricalPhase}, so that the full-box exponential-moment bound $\mathbb Ee^{t\xi_n(u)}\le e^{\kappa t^2/2}$ holds uniformly in $n$\leanrefL{Grammar/SubgaussianPhase.lean\#L201}{lintegral\_exp\_phase\_sampleDatum\_le\_of\_subgaussian};
\item the face variances satisfy $\sigma^2(u):=\operatorname{Var}[\xi_{Y_0}(u)]\le\kappa$\leanrefL{Grammar/SubgaussianPhase.lean\#L217}{phaseVar\_le\_of\_uniformSubgaussian}, because a sub-Gaussian variable with proxy $\kappa$ has variance at most $\kappa$\leanrefL{Grammar/SubgaussianPhase.lean\#L71}{variance\_le\_of\_hasSubgaussianMGF};
\item bounded observations satisfy \eqref{eq:uniform_subgaussian} with $\kappa=M_0^2$ (Hoeffding)\leanrefL{Grammar/SubgaussianPhase.lean\#L144}{uniformSubgaussianPhase\_of\_bounded}.
\end{enumerate}
\end{prop}
\begin{proof}[Proof sketch]
(1) is the additivity of the sub-Gaussian proxy under independent sums together with the scaling $((\sqrt n)^{-1})^2\cdot n\kappa=\kappa$. (2) uses $y^2\le e^{y}+e^{-y}-2$, the two-sided bound $\mathbb E e^{\pm tQ}\le e^{\kappa t^2/2}$, and $t\to0^+$. (3) is Hoeffding's lemma for variables in $[-M_0,M_0]$.
\end{proof}

The hypothesis \eqref{eq:uniform_subgaussian} is a substantive assumption on the sampling law: it is not implied by the Gaussian limit, by a scalar central limit theorem, or by square integrability. It is exactly the input that controls finite-sample exponential moments uniformly in $n$ over the whole box. The variance bound in (2) is sharp, so the thresholds $\beta\kappa<2$ below are the advertised ones; the annealed criterion itself is sufficient, and is not claimed to be necessary.

\subsection{The Gaussian Banach law and Fernique}\label{subsec:fernique}

If $G$ is Borel measurable for the sup-norm topology of $C(K)$ and its law is Gaussian in the sense that every continuous linear functional has a real Gaussian law, then Fernique's theorem (in Mathlib, the finiteness of all moments of a Gaussian measure on a separable Banach space) gives $\mathbb E\|G\|_\infty^2<\infty$\leanrefL{Grammar/GaussianFieldFernique.lean\#L38}{integrable\_sq\_norm\_of\_isGaussian}, discharging the second-moment hypothesis of \cref{prop:compact_base}\leanrefL{Grammar/GaussianFieldFernique.lean\#L61}{GaussianField.ofIsGaussian}. Gaussianity of the Banach law fixes neither the mean nor the covariance, so the constructor takes them as certificates. With $\mathbb EG(y)=0$ and $\mathbb E[G(y)G(z)]=C(y,z)$ for all $y,z\in K$, every finite linear combination has a Gaussian law,
\[
\sum_i\theta_iG(x_i)\sim N\Big(0,\sum_{i,j}\theta_i\theta_jC(x_i,x_j)\Big)\leanrefL{Grammar/GaussianLinearCombination.lean\#L246}{map\_evalCombination\_eq\_gaussianReal\_of\_certificates};
\]
Gaussian laws on $\mathbb R^m$ are determined by their first and second coordinate moments\leanrefL{Grammar/GaussianLinearCombination.lean\#L87}{isGaussian\_ext\_of\_moments}, and the kernel matrix is positive semidefinite\leanrefL{Grammar/GaussianLinearCombination.lean\#L160}{PSDKernel.kernelMatrix\_posSemidef} with the Gram factor $[\sqrt C\,|\,0]$\leanrefL{Grammar/GaussianLinearCombination.lean\#L140}{gramFactor\_mul\_transpose}. Hence the finite-dimensional evaluation laws are the centred Gaussian vectors with the kernel covariance\leanrefL{Grammar/GaussianLinearCombination.lean\#L279}{map\_evalVec\_eq\_gaussianVector}, and the \texttt{GaussianField} record is built from the Banach law and the two certificates alone\leanrefL{Grammar/GaussianLinearCombination.lean\#L307}{GaussianField.ofIsGaussianCertificates}. No Gaussian law on $C(K)$ is constructed from a kernel.

\subsection{Conditional assembly at the scale $A_n=n^\lambda/(\log n)^{m-1}$}\label{subsec:assembly}

Write $Z_n=Z_n^{\mathrm{core}}+\mathrm{Rem}_n$ for the certified-core decomposition of the evidence and
\[
A_n=\frac{n^\lambda}{(\log n)^{m-1}}\qquad(\text{set to $1$ for $n<2$})\leanrefL{Grammar/ScaledAssembly.lean\#L38}{scaleA}
\]
for the scale.

\begin{prop}[Scaled assembly]\label{prop:scaled_assembly}
\begin{enumerate}
\item If $A_nZ_n^{\mathrm{core}}\Rightarrow L$ and $A_n\mathrm{Rem}_n\to0$ in probability, then $A_nZ_n\Rightarrow L$ (Slutsky)\leanrefL{Grammar/ScaledAssembly.lean\#L97}{tendstoInDistribution\_scaled\_assembly}. The condition $\mathbb E|A_n\mathrm{Rem}_n|\to0$ suffices\leanrefL{Grammar/ScaledAssembly.lean\#L113}{tendstoInMeasure\_zero\_of\_tendsto\_integral\_abs}, and since $A_ne^{-cn}\to0$ for every $c>0$\leanrefL{Grammar/ScaledAssembly.lean\#L60}{tendsto\_scaleA\_mul\_exp\_neg}, the annealed remainder bound of the paper makes it automatic.
\item If moreover $\sup_n\mathbb E|A_nZ_n^{\mathrm{core}}|^p<\infty$ for some $p>1$, then $\mathbb E[A_nZ_n]\to\mathbb EL$\leanrefL{Grammar/ScaledAssembly.lean\#L127}{tendsto\_integral\_scaled\_assembly} and, when $\mathbb EL>0$,
\[
\mathbb EZ_n\sim\mathbb EL\;n^{-\lambda}(\log n)^{m-1}\leanrefL{Grammar/ScaledAssembly.lean\#L156}{isEquivalent\_integral\_scaled}.
\]
\item If $A_nZ_n\Rightarrow L$ with $L>0$ almost surely and $Z_n>0$, then $\log Z_n/\log n\to-\lambda$ in probability\leanrefL{Grammar/ScaledAssembly.lean\#L285}{tendstoInMeasure\_log\_div\_log}: the portmanteau inequality for the closed sets $[M,\infty)$ and $(-\infty,1/M]$ shows that $a_n\log X_n\to0$ in probability whenever $X_n\Rightarrow L>0$, $X_n>0$ and $a_n\to0$\leanrefL{Grammar/ScaledAssembly.lean\#L175}{tendsto\_measure\_log\_of\_tendstoInDistribution}.
\end{enumerate}
\end{prop}

The moment hypothesis of (2) is discharged for certified box cores by \cref{prop:deterministic_weight,prop:population_bound}.

\begin{thm}[Expectation assembly for certified sub-Gaussian cores]\label{thm:core_assembly}
Let $Z_n^{\mathrm{core}}=\sum_jZ_{j,n}$ be a finite sum of certified box cores with bounded Borel data, full-box exponential moments of the phase fields (constant $c$) and certified reduced-temperature population bounds. Then for $p>1$ with $p\beta c<2$ the uniform $p$-th moment bound holds (using $|\sum_jY_j|^p\le J^{p-1}\sum_j|Y_j|^p$\leanrefL{Grammar/CertifiedCoreAssembly.lean\#L33}{abs\_sum\_rpow\_le} and \cref{prop:deterministic_weight} at temperature $\alpha$\leanrefL{Grammar/CertifiedCoreAssembly.lean\#L101}{uniform\_moment\_coreSum}), and
\[
A_nZ^{\mathrm{core}}_n\Rightarrow L\ \text{ and }\ \mathbb E|A_n\mathrm{Rem}_n|\to0\qquad\Longrightarrow\qquad\mathbb E[A_nZ_n]\to\mathbb EL\leanrefL{Grammar/CertifiedCoreAssembly.lean\#L187}{tendsto\_integral\_scaled\_assembly\_of\_certified\_subgaussian\_cores}.
\]
When every box exponent pair dominates the scale $(\lambda,m)$, which is automatic at the assembled core's own leading scale, the population bounds are supplied by \cref{prop:population_bound}, and only the field limit, the bounded Borel data, the full-box exponential moments and $\mathbb E|A_n\mathrm{Rem}_n|\to0$ remain as hypotheses\leanrefL{Grammar/PopulationBoundDischarge.lean\#L201}{tendsto\_integral\_scaled\_assembly\_of\_dominated\_cores}. For the sample datum of an i.i.d.\ sample with bounded chart phase observations ($\|Y_i\|_{\ell^1}\le M_0$, $p\beta M_0^2<2$) and zero-phase amplitude data the exponential moments are \eqref{eq:hoeffding_phase}, so the assembly needs only the distributional limit of the scaled empirical core, the domination of the box exponent pairs and $\mathbb E|A_n\mathrm{Rem}_n|\to0$\leanrefL{Grammar/SampleDatumMGF.lean\#L182}{tendsto\_integral\_scaled\_assembly\_sampleDatum}; under the sub-Gaussian hypothesis \eqref{eq:uniform_subgaussian} the same holds with $p\beta\kappa<2$ in place of $p\beta M_0^2<2$\leanrefL{Grammar/SubgaussianAssembly.lean\#L60}{tendsto\_integral\_scaled\_assembly\_sampleDatum\_subgaussian}.
\end{thm}

The distributional limit of the scaled empirical core is itself a theorem of the library, for one chart and for finitely many charts read from one sample.

\begin{thm}[The annealed sample-datum theorem]\label{thm:annealed_sample}
Consider one certified box chart with exponent data $(h,k)$ and leading pair $(\lambda_0,m_0-1)$, i.i.d.\ samples whose chart phase observations satisfy the $\ell^1$ central-limit certificate $\sum_\gamma b^{|\gamma|}\|c_\gamma(X)\|_{L^2}<\infty$, a zero-phase amplitude datum $A$ of bounded amplitude mass, and a remainder with $\mathbb E|A_n\mathrm{Rem}_n|\to0$.
\begin{enumerate}
\item At the leading pair every predecessor coefficient of the ordered normalised remainder vanishes\leanrefL{Grammar/SampleDatumLimit.lean\#L56}{predSum\_leading}, so the ordered remainder is the scaled core itself\leanrefL{Grammar/SampleDatumLimit.lean\#L80}{scaleA\_mul\_dataBoxIntegral\_eq\_orderedRemainder}, and the stochastic Taylor tree (uniform control of the deterministic remainder on data balls together with tightness of the sample data in $\ell^1$; the $\sqrt n$ growth of the sample datum's norm is immaterial) gives
\[
A_nZ_n(D_n)\Rightarrow C_{\lambda_0,m_0-1}(Z+A),\qquad Z\sim\nu,\leanrefL{Grammar/SampleDatumLimit.lean\#L116}{tendstoInDistribution\_scaled\_dataBoxIntegral\_sampleDatum}
\]
with $\nu$ the $\ell^1$ Gaussian limit of the phase observations.
\item If the observations are bounded, $\|Y_i\|_{\ell^1}\le M_0$ with $p\beta M_0^2<2$ for some $p>1$, then
\[
\mathbb E\big[A_n(Z_n(D_n)+\mathrm{Rem}_n)\big]\to\mathbb E_\nu\big[C_{\lambda_0,m_0-1}(Z+A)\big],\leanrefL{Grammar/SampleDatumLimit.lean\#L158}{tendsto\_integral\_scaled\_sampleDatum\_single}
\]
the limiting coefficient being $\nu$-integrable; the same holds under the sub-Gaussian hypothesis \eqref{eq:uniform_subgaussian} with $p\beta\kappa<2$\leanrefL{Grammar/SubgaussianAssembly.lean\#L147}{tendsto\_integral\_scaled\_sampleDatum\_single\_subgaussian}.
\item For finitely many charts read from the same sample, the chart data are the components of the joint sample datum and converge jointly to the unpacked stacked $\ell^1$ Gaussian limit. At a global scale $(\lambda,m)$ dominated by every chart exponent pair, the leading charts contribute their leading coefficients and the strictly dominated charts vanish in probability (a deterministic scale ratio tending to zero times a remainder bounded uniformly on data balls), so
\[
A_nZ^{\mathrm{core}}_n\Rightarrow\sum_{I\ \mathrm{leading}}C_I(Z_I+A_I)\leanrefL{Grammar/JointSampleLimit.lean\#L176}{tendstoInDistribution\_scaled\_coreSum\_sampleDatum},\qquad
\mathbb E\big[A_n(Z^{\mathrm{core}}_n+\mathrm{Rem}_n)\big]\to\mathbb E_\nu\Big[\sum_{I\ \mathrm{leading}}C_I(Z_I+A_I)\Big]\leanrefL{Grammar/JointSampleLimit.lean\#L357}{tendsto\_integral\_scaled\_coreSum\_sampleDatum}
\]
for bounded observations with $p\beta M_0^2<2$, and likewise for sub-Gaussian observations with a common proxy and $p\beta\kappa<2$\leanrefL{Grammar/SubgaussianAssembly.lean\#L96}{tendsto\_integral\_scaled\_coreSum\_sampleDatum\_subgaussian}.
\end{enumerate}
\end{thm}

The limiting expectation is not left abstract: it is a Gaussian integral that can be evaluated.

\begin{thm}[Identification of the limiting expectation]\label{thm:EL_identified}
The $\ell^1$ central limit theorem determines its limit law $\nu$ through two certificates: centred Gaussian finite coordinate marginals with the covariance of the observation, and the tail bound $\int\|x-T_Fx\|\,d\nu\le\sum_{j\notin F}\sigma_j$.
\begin{enumerate}
\item For bounded observations these make every continuous linear functional $L$ of $\nu$ a centred Gaussian variable with variance $\operatorname{Var}[L(Y_0)]$\leanrefL{Grammar/L1GaussianFunctional.lean\#L174}{map\_eq\_gaussianReal\_of\_marginals}, and likewise for observations in $L^2(P;\ell^1)$, the dominating functions of the variance limit being $\|L\|\,\|Y_0\|$ and its square\leanrefL{Grammar/L1GaussianFunctionalL2.lean\#L87}{map\_eq\_gaussianReal\_of\_marginals\_of\_memLp}. The proof truncates, compares characteristic functions within $|t|\,\|L\|\sum_{j\notin F}\sigma_j$, and passes to the limit. In particular the phase evaluation $Z\mapsto\xi_Z(u)$ of the $\ell^1$ Gaussian limit is $N(0,\operatorname{Var}[\xi_{Y_0}(u)])$ for every $u\in[0,1]^d$\leanrefL{Grammar/L1GaussianFunctional.lean\#L211}{map\_phaseEvalCLM\_eq\_gaussianReal}.
\item The phase-dressed moment is half the fluctuation function, $J_{2\lambda}(a)=S_\lambda(a)/2$\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L42}{phaseMoment\_eq\_half\_fluctuation}, and $\mathbb ES_\lambda(N(0,v))=\Gamma(\lambda)(\beta(1-\beta v/2))^{-\lambda}$ for $\beta v<2$\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L56}{integral\_fluctuation\_gaussianReal}. The amplitude coordinates of $Z\sim\nu$ vanish almost surely\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L115}{ae\_etaCoord\_eq\_zero}, and the leading coefficient at box radius $b$ is the face functional of the represented phase and amplitude,
\[
C^b_{\lambda,m-1}(x)=b^{|h|+d}c^{-\lambda}\,\mathcal F(\xi_x,\eta_x)\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L163}{dataBoxCoeff\_leading\_eq\_spatialFace}.
\]
At each face point, with $\sigma^2(v)=\operatorname{Var}[\xi_{Y_0}(v)]\le M_0^2$ (respectively $\le\kappa$ by \cref{prop:subgaussian_phase}),
\[
\mathbb E_\nu J_{2\lambda}(\xi_Z(v))=\frac{\Gamma(\lambda)}2\big(\beta(1-\beta\sigma^2(v)/2)\big)^{-\lambda}\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L215}{integral\_phaseMoment\_evalF}.
\]
\item Fubini over the face gives, for $\beta M_0^2<2$,
\begin{equation}\label{eq:EL_identified}
\mathbb E_\nu\big[C^b_{\lambda,m-1}(Z+A)\big]=b^{|h|+d}c^{-\lambda}\,K_{\mathrm{face}}\,\frac{\Gamma(\lambda)}{2}\int_{(0,1]^d}\eta_A(\pi u)\,\big(\beta(1-\tfrac\beta2\sigma^2(\pi u))\big)^{-\lambda}w(u)\,du\Big/2^{m-1},\leanrefL{Grammar/LeadingCoeffGaussianMoment.lean\#L261}{integral\_dataBoxCoeff\_leading\_eq}
\end{equation}
with $\pi$ the face projection and $w$ the residual weight, and the identity holds verbatim for $L^2$ observations with a uniform sub-Gaussian proxy $\kappa$, $\beta\kappa<2$\leanrefL{Grammar/SubgaussianAssembly.lean\#L257}{integral\_dataBoxCoeff\_leading\_eq\_subgaussian}.
\end{enumerate}
\end{thm}

The right-hand side of \eqref{eq:EL_identified} is the population face integral with the temperature $\beta$ replaced \emph{pointwise} by $\beta(1-\beta\sigma^2(\pi u)/2)$. It is a single scalar temperature only when $\sigma^2$ is constant on the face.

\begin{cor}[The effective temperature]\label{cor:effective_temperature}
Under the hypotheses of \cref{thm:EL_identified}, suppose that the face variance is constant, $\sigma^2(\pi u)=v_0$ for almost every $u$ in the box, with $\beta v_0<2$. Then the limiting expectation is the zero-phase population coefficient with the same geometric data and amplitude at the effective temperature $\beta_{\mathrm{eff}}=\beta(1-\beta v_0/2)$:
\begin{equation}\label{eq:effective_temperature}
\mathbb E_\nu\big[C^b_{\lambda,m-1}(Z+A)\big]=C^b_{\lambda,m-1}(A;\beta_{\mathrm{eff}})\leanrefL{Grammar/EffectiveTemperature.lean\#L80}{integral\_dataBoxCoeff\_leading\_eq\_population\_of\_const\_faceVariance},
\end{equation}
where for zero-phase data
\[
C^b_{\lambda,m-1}(A;\beta)=b^{|h|+d}c^{-\lambda}K_{\mathrm{face}}\,\frac{\Gamma(\lambda)\beta^{-\lambda}}{2}\int_{(0,1]^d}\eta_A(\pi u)\,w(u)\,du\Big/2^{m-1}\leanrefL{Grammar/EffectiveTemperature.lean\#L51}{dataBoxCoeff\_leading\_zero\_phase}.
\]
\end{cor}

Almost-everywhere constancy suffices, and no converse is asserted: a signed amplitude can produce accidental equalities of integrals. With several charts, constant variance on each leading face gives chart-specific effective temperatures, and a single effective temperature needs a common variance. On the divisor model $v_0=2$ and $\beta_{\mathrm{eff}}=\beta(1-\beta)$, so the temperature condition reads $\beta<1$, matching \cref{cor:denominator}.

\begin{remark}[$\mathbb EL$ is not the population coefficient]\label{rem:EL_not_population}
$\mathbb EL$ is the expectation of the \emph{limiting empirical} coefficient. It is not in general the population Laplace coefficient at temperature $\beta$: \cref{cor:denominator} already exhibits the Gaussian inflation of $\mathbb ED(G)$ over $D(0)$, and \cref{cor:effective_temperature} shows that at constant face variance the limit is the population coefficient at $\beta(1-\beta v_0/2)<\beta$. Equality at the original temperature is in general false, not merely unproved.
\end{remark}

Three interface facts close the chain between \cref{thm:annealed_sample} and \cref{thm:EL_identified}.

\begin{prop}[Closure of the empirical chain]\label{prop:closure}
\begin{enumerate}
\item The Banach $L^2$ hypothesis of \cref{thm:EL_identified}(1) is implied by the coordinate certificate: finite-sum Minkowski on the truncations and Fatou along an exhaustion give
\[
\big\|\,\|Y_0\|_{\ell^1}\big\|_{L^2}\le\sum_\gamma\|Y_{0,\gamma}\|_{L^2}\leanrefL{Grammar/ClosureEndpoint.lean\#L78}{eLpNorm\_le\_tsum\_coordL2}\leanrefL{Grammar/ClosureEndpoint.lean\#L94}{memLp\_two\_of\_summableCoordL2}.
\]
\item The Gaussian limit delivered by \cref{thm:annealed_sample} carries the tail certificate used by \cref{thm:EL_identified}\leanrefL{Grammar/ClosureEndpoint.lean\#L133}{tendstoInDistribution\_scaled\_dataBoxIntegral\_sampleDatum\_tail}, so one and the same law $\nu$ appears in both.
\item (The endpoint.) Under the coordinate certificate, the sub-Gaussian hypothesis \eqref{eq:uniform_subgaussian} with $p\beta\kappa<2$, a zero-phase amplitude datum and $\mathbb E|A_n\mathrm{Rem}_n|\to0$, there is one law $\nu$ with Gaussian marginals and the tail certificate such that $\mathbb E[A_n(Z_n(D_n)+\mathrm{Rem}_n)]\to\mathbb E_\nu[C^b_{\lambda_0,m_0-1}(Z+A)]$ \emph{and} this limit equals the right-hand side of \eqref{eq:EL_identified}\leanrefL{Grammar/ClosureEndpoint.lean\#L180}{annealed\_sampleDatum\_single\_identified}; at constant face variance it equals $C^b_{\lambda_0,m_0-1}(A;\beta_{\mathrm{eff}})$\leanrefL{Grammar/ClosureEndpoint.lean\#L253}{annealed\_sampleDatum\_single\_effectiveTemperature}.
\item Since $\beta\kappa<2$ already yields a $p>1$ with $p\beta\kappa<2$\leanrefL{Grammar/ClosureEndpoint.lean\#L103}{exists\_p\_gt\_one\_of\_lt\_two}, the $p$-hypothesis is no extra numerical restriction\leanrefL{Grammar/ClosureEndpoint.lean\#L287}{annealed\_sampleDatum\_single\_identified\_of\_lt\_two}.
\end{enumerate}
\end{prop}

Finally, the exponent pair of the scale is identified by comparison with the deterministic theory.

\begin{prop}[Exponent identification]\label{prop:exponent}
Power--log orders along the integers are unique\leanrefL{Grammar/ExponentComparison.lean\#L126}{powerLogRate\_pair\_eq\_of\_isTheta\_nat}. Hence if the \emph{same} population integral $\int e^{-nK}\,d\mu$ has a certified core limit $A_nZ^{\mathrm{pop}}_n\to L_0>0$ and Hironaka's two-sided order $N^{-\lambda_H}(\log N)^{\theta_H-1}$, then $\lambda=\lambda_H$ and $m=\theta_H$ (for $m\ge1$; $m=0$ and $m=1$ define the same scale)\leanrefL{Grammar/ExponentComparison.lean\#L178}{exponentPair\_eq\_of\_population\_comparison}. By Bierstone--Milman's chart-form theorem, which the \texttt{hironaka} library now proves for every dimension (\texttt{Q\_all}), this holds unconditionally on every small closed cube centred at a zero $w$ of a real-analytic phase $K\ge0$ that is not identically zero near $w$, for the Lebesgue-measure integral $\int_{\|x-w\|_\infty\le r}e^{-nK}\,dx$\leanrefL{Grammar/ExponentComparison.lean\#L194}{exists\_exponentPair\_of\_Q}\leanrefL{Grammar/HironakaUnconditional.lean\#L45}{exists\_exponentPair}, and the empirical exponent statement then reads $\log Z_n/\log n\to-\lambda_H$ in probability\leanrefL{Grammar/ExponentComparison.lean\#L211}{tendstoInMeasure\_log\_div\_log\_of\_population\_comparison}.
\end{prop}

The pair is identified by comparing two order descriptions of the same population integral; two exponent theorems about unrelated integrals identify nothing, and the empirical logarithmic limit transports the power exponent $\lambda$ only (the log exponent $m$ comes from the deterministic comparison, with $m\ge1$).

\subsection{What the expected error formulas still need}\label{subsec:still_needed}

The library's stochastic expansion gives convergence in distribution of the normalised remainders and of the canonical coefficients at the Gaussian limit\leanrefL{Grammar/SampleExpansion.lean\#L54}{sample\_stochastic\_expansion}, and the random-phase posterior theorems give convergence of the posterior laws. For a finite-resolution limit, convergence of the relevant scaled observables together with uniform integrability (or a uniform $(1+\varepsilon)$-moment bound) and a predictive Taylor-remainder estimate permits the quartet algebra of \cref{cor:quartet_algebra} to determine the expected coefficients; for the continuum spatial posterior the Gaussian identities are available on a compact base by discretisation transfer (\cref{prop:compact_base}), so what remains is the uniform-integrability input and the remainder estimate. These hypotheses are not discharged here.

\subsection{Interfaces}\label{subsec:interfaces}

The following table records, for each formal interface, what is supplied as hypothesis, what is proved, and what is not supplied.
\begin{center}\small
\begin{tabular}{p{2.6cm}p{3.6cm}p{3.6cm}p{3.6cm}}
\toprule
Interface & Supplied hypotheses & Formal output & Not supplied\\
\midrule
Certified chart core & exact core certificate (measure and phase identities) & chart integral $=$ model integral & certificate existence; removal of positive units\\
Pathwise gap & positive gap, fluctuation bound on the good event & pathwise $e^{-\beta n\kappa/2}$ remainder & smallness on the exceptional event\\
Annealed gap & pointwise exponential moments, integrable envelope & expected $e^{-(1-\theta)\beta n\kappa}$ remainder & supremum concentration\\
Compact Gaussian base & continuous paths, Gaussian evaluation laws, $\mathbb E\|G\|_\infty^2<\infty$ & IBP, interpolation, $\mathbb E\log D\ge\log D(0)$, annealed first moment & Gaussian-process existence\\
Banach-law adapter & Gaussian Borel law on $C(K)$, centring and kernel covariance & the sup-norm moment (Fernique) and the finite-dimensional Gaussian evaluation laws; a \texttt{GaussianField} & a Gaussian law constructed from the kernel alone\\
Uniform moments & pointwise $\mathbb Ee^{tX(x)}\le e^{ct^2/2}$, $p\beta c<2$; bounded amplitude mass & $\sup_n\mathbb E[D_\rho(\xi_n)^p]<\infty$; uniform $p$-th moments for dominated certified box cores under a full-box sub-Gaussian MGF bound, with the population bounds derived; for bounded i.i.d.\ sample data the MGF bound is Hoeffding's & a uniform full-box sub-Gaussian proxy for the chart phase observations (Hoeffding supplies $\kappa=M_0^2$ for bounded observations); otherwise the full-box exponential moments of the finite-$n$ field\\
Empirical sampling & the standard form $f=\phi a$, $\mathbb Ea=\phi$; the coefficient family as the Taylor family of $-a$ & exact centred coefficient/evaluation identity including the sign: sample phase $\xi_n=-\zeta_n$, certified core at the sample datum $=$ sampling integral with $N=n$ & original-model-to-certified-core compatibility (the abstract coefficient family as the model's Taylor coefficients)\\
Scaled assembly & $A_nZ^{\mathrm{core}}_n\Rightarrow L$, negligible scaled remainder & $A_nZ_n\Rightarrow L$, $\log Z_n/\log n\to-\lambda$ & expectation convergence without UI\\
Distributional assembly & the joint $\ell^1$ sample-data limit (CLT and tail certificates, certified chart data) & single- and finite-chart scaled-core limits & CLT/tail certificates and certified chart data\\
Annealed assembly & the scaled-core limit, the sub-Gaussian proxy ($p\beta\kappa<2$) and vanishing scaled $L^1$ remainder & convergence of expectations $\mathbb E[A_nZ_n]\to\mathbb EL$, $\mathbb EZ_n\sim\mathbb EL\,n^{-\lambda}(\log n)^{m-1}$; the finite-$n$ moment inputs discharged & scaled $L^1$-negligibility of the external remainder\\
First-moment identification & the coordinate certificate (which gives $L^2$), $\beta\kappa<2$ & the covariance-modified face integral \eqref{eq:EL_identified}; the constant-variance corollary at the effective temperature & no general equality with the population coefficient at the original temperature $\beta$: it is generally a different quantity\\
Exponent comparison & same population integral, $L_0>0$, both order descriptions & $(\lambda,m)=(\lambda_H,\theta_H)$ & compatibility of unrelated theorems\\
\bottomrule
\end{tabular}
\end{center}

\section{Discussion}\label{sec:discussion}

\paragraph{The diagrammatic reading.} The computation of dataset-averaged quantities decomposes into resolution of singularities (which produces the vertices $S_\lambda(G_w)$ at points of the alive coordinate space, with the Weber recurrence as equation of motion) followed by Gaussian averaging with the resolved covariance as propagator. Raw one-point quantities involve local pairings (tadpoles dressing each vertex); raw multipoint quantities already involve bilocal cross-pairings mediated by $b(w,w')$; normalised observables couple base points through the common denominator and are handled here by exact self-normalised identities rather than by a denominator series, the linked-cluster structure appearing through logarithms and ratios rather than through geometric expansions of $1/Z$. Under the statistical transfer and remainder hypotheses, the leading expected-error coefficients have the two-parameter form determined by $\lambda$ and $\nu$: $\lambda$ packages the geometry of the resolution, $\nu$ the statistics of the Gaussian field on the divisor; the present finite-resolution Gaussian theorem establishes that algebra, not the finite-sample expansion itself. The analogy with a scalar field theory with one species and a generating-function vertex is genuine but limited: there are no selection rules, the combinatorics is trivial, and the complexity lives in the geometry of the resolution and in the analytic structure of $C_{\alpha\beta}(w,w')$.

\paragraph{The Weber module.} The annotation insertions of the Taylor tree raise the index of the fluctuation function by $1/2$ per insertion ($S_\lambda\to S_{\lambda+Q/2}$, the action of $b^\dagger$), but monomial insertions also shift the Mellin exponent: in one normal coordinate $n^{Q/2}\int u^{h+\gamma+kQ}e^{-\beta nu^{2k}+\beta\sqrt nu^ka}\,du$ has scale $n^{-\mu}S_{\mu+Q/2}(a)$ with $\mu=(h+\gamma+1)/(2k)$, up to deterministic factors, and logarithmic terms require the log-moment functions rather than bare $S_\mu$. The precise leaf-interface statement is the Taylor-tree theorem of the paper; the universal leaf-polynomial formula and the representation-theoretic reading of earlier drafts are recorded, with these qualifications, in \cref{app:heuristic}.

\paragraph{Relation to Watanabe.} The formulas $\mathbb E[V]=2\nu/\beta$ and $\mathbb E\langle T^2\rangle=\lambda/\beta+\nu$ are Watanabe's \cite[Chapter~6]{watanabeAlgebraicGeometryStatistical2009}; the Gaussian integration by parts is a repackaging of his partial-integration identity. What is new here is the finite-resolution formulation with explicit integrability for every $\beta>0$, its formalisation, and the separation of the exact and Gaussian-limit statements from the conditional asymptotic ones.

\paragraph{Deferred.} Multi-leaf contributions with distinct exponents; finite-$n$ non-Gaussian corrections (higher cumulants of $\xi_n$); the $O(1/n^2)$ theory; log-power cancellations across leaves; higher Ward identities from the Weber module; the diagrammatic phase-transition picture (\cref{app:phase}).

\appendix

\section{Heuristic diagrammatics (deferred)}\label{app:heuristic}

This appendix collects the diagrammatic material of earlier drafts that is not established at the level of the main text. Nothing here carries a convergence or asymptotic-order claim.

\paragraph{Isserlis pairings.} When the leaf polynomial is a product $\prod_{j=1}^Q\partial_v^{(\alpha_j)}G(0,w)\cdot S_\nu(G(0,w))$ (schematically; see the Weber-module paragraph of \cref{sec:discussion} for the index bookkeeping), its expectation can be organised by Isserlis' theorem: expand $S_\nu=\sum_ms^{(\nu)}_ma^m$ and sum over perfect pairings of the $Q+m$ Gaussian factors, each pairing contributing a jet-covariance $c$, $d_\alpha$ or $e_{\alpha\beta}$. For $Q=0$ the pairings are tadpoles and resum to the dressing $(1-\beta c/2)^{-\nu}$ of \cref{prop:Q0}; for $Q=1,2$ they reproduce \cref{prop:Q12}. For general $Q$ the enumeration is the standard one and is not needed for the main text. Termwise expectation of the source series requires a separate absolute-integrability argument; the pairing description alone does not justify exchanging the infinite sum and expectation.

\paragraph{The denominator expansion.} Writing $D=\bar D(1+\delta)$ with $\bar D=\mathbb ED$ and expanding $\log(1+\delta)$ gives, \emph{when justified},
\[
\mathbb E\log D=\log\bar D+\sum_{p\ge2}\frac{(-1)^{p+1}}p\,\mathbb E[\delta^p],
\]
in terms of \emph{moments} of $\delta$, not cumulants (e.g.\ $\mathbb E[\delta^4]=\kappa_4+3\kappa_2^2$); earlier drafts stated the sum with cumulants, which is incorrect. On the divisor model $\bar D=\infty$ for $\beta\ge1$ and $\delta$ is not defined; the covariance interpolation of \cref{sec:interpolation} is the rigorous replacement and is not term-by-term the same expansion. Finiteness of $\bar D$ alone is not sufficient: the Taylor series for $\log(1+\delta)$ and its termwise expectation require additional control, and higher moments of $\delta$ may fail even when $\bar D<\infty$ (\cref{prop:moments}). Likewise $1/D$ is not to be expanded as a geometric series in $\delta$ to compute posterior expectations; the ratio $N/D$ is handled by self-normalisation (\cref{thm:quartet}).

\paragraph{The marked-space representation.} With $G_w=W(h_w)$ an isonormal process on a Hilbert space $H$, $\|h_w\|^2=c$, $\langle h_w,h_{w'}\rangle=b(w,w')$, and the marked variable $\alpha=(w,y)$ with measure $\nu(d\alpha)=\rho(w)y^{\lambda-1}e^{-\beta y}\,dy\,dw$ and kernel element $V_\alpha=\sqrt y\,h_w$, the denominator is a superposition of exponential vertices,
\[
D(G)=\int e^{\beta W(V_\alpha)}\,\nu(d\alpha),
\]
which is correct in the normalisation \eqref{eq:S_defn}. This linearisation is useful and is the continuum shadow of the finite-resolution computations. The infinite-dimensional identities of earlier drafts are replaced by \cref{thm:quartet,prop:interpolation}: an isonormal $W$ is not an $H$-valued random vector, so $\langle W,\nabla\log D\rangle_H$ is not automatically meaningful; the Malliavin Hessian of $\log D_s$ carries a factor $s$, $\nabla^2_W\log D_s=\beta^2s\operatorname{Cov}_{\pi_s}(V,V)$; and the marked second moment obeys only $\operatorname{Tr}\operatorname{Cov}_\pi(V,V)\le\mathbb E_\pi\|V\|^2=c\,\mathbb E_\pi[y]$ for constant diagonal, not a factorisation. The compact-base extension by mass-preserving atomic approximation is \cref{prop:compact_base}: it requires the field to have measurable evaluations, the stated finite-dimensional Gaussian laws, and an integrable squared sup norm (which Fernique's theorem supplies under a Gaussian Borel law on $C(K)$, as formalised in \cref{sec:grammar}).

\paragraph{Loop order and the computation recipe.} The reading of $1/n$ as a loop-counting parameter, of the Gaussian approximation as the tree-level theory, and of the higher cumulants of $\xi_n$ as higher-valence vertices ($r=3$ at relative order $n^{-1/2}$, $r=4$ at $n^{-1}$) is heuristic. So is the recipe ``enumerate vertices by running the Taylor tree; compute the propagator $C_{\alpha\beta}$; draw connected diagrams at the desired order; evaluate the finite-dimensional integrals'': it is a plausible organisation of the calculation, whose first step (the resolution and the enumeration of complete movies) is the algebraic geometry and whose justification at order $1/n^2$ and beyond has not been given.

\paragraph{Finite-$n$ regularity.} A finite empirical average is not automatically sub-Gaussian and need not have all exponential moments; analyticity of $a(x,\cdot)$ in the parameter does not supply them. Pathwise finiteness of $Z_n$, finiteness of its dataset moments, and finiteness of moments of the Gaussian limit are three different statements. For the Gaussian-limit quantities of the quartet no Borel summation or analytic continuation to $\beta=1$ is needed.

\section{Phase transitions: the algebra, and what is speculative}\label{app:phase}

Suppose $Z_n=Z_n^{(1)}+Z_n^{(2)}$ with $Z_n^{(i)}\approx n^{-\lambda^{(i)}}(\log n)^{m^{(i)}-1}D^{(i)}(G)$, $D^{(i)}(G)=\int\rho^{(i)}(w)S_{\lambda^{(i)}}(G_w)\,dw$, both functionals of the same Gaussian process. The free energy obeys the exact identity $F_n=F_n^{(1)}-\log(1+e^{-\Delta F_n})$ with
\begin{equation}\label{eq:free_energy_diff}
\Delta F_n=F_n^{(2)}-F_n^{(1)}=(\lambda^{(2)}-\lambda^{(1)})\log n-(m^{(2)}-m^{(1)})\log\log n+\log\frac{D^{(1)}(G)}{D^{(2)}(G)}+\cdots,
\end{equation}
conditional on the leading-order approximations. The following corrections to earlier drafts apply. When $\lambda^{(1)}<\lambda^{(2)}$ the second phase is suppressed \emph{polynomially}, by $n^{-(\lambda^{(2)}-\lambda^{(1)})}$, not exponentially. At equal $\lambda$ but unequal multiplicities the selection is deterministic through $\log\log n$. The expectation $\mathbb E[\log D^{(1)}-\log D^{(2)}]$ depends only on the two marginal laws; the cross-covariance of the phases does \emph{not} enter it through cross-cumulants, but enters the variance of $\Delta F_n$, the phase-selection probabilities, and $\mathbb E\log(D^{(1)}+D^{(2)})$. A large inter-phase correlation does not by itself make a transition ``soft'' or the ratio close to its population value, and the stated incidence relation between strata does not supply an inclusion between their normal bundles. The narrative of resonating phases, wall-crossing diagnostics through observables with different vanishing orders, and universal sharpness statements is speculative and is recorded here as such. \IfFileExists{phase_transition_figure.tex}{\input{phase_transition_figure}}{}

\bibliographystyle{plainnat}
\bibliography{references_grammar}

\end{document}
```

### B. The leanref inventory (module : declaration), 220 distinct dots

```
AnalyticCertificate : dataPhase_sampleDatum
AnnealedIdentity : lintegral_annealedZ
AnnealedIdentity : lintegral_annealedZ_one
BilocalCriticalBoundary : bilocal_lintegral_lt_top_iff_of_critical
BilocalCriticalBoundary : lintegral_bilocalIntegrand_critical_eq
BilocalCriticalBoundary : lintegral_criticalProfile_lt_top_iff
BilocalCriticalBoundary : lintegral_fluctuation_mul_fluctuation_lt_top_iff_of_critical
BilocalDivergence : lintegral_bilocalIntegrand_eq_top
BilocalGaussian : integrable_fluctuation_mul_fluctuation
BilocalGaussian : lintegral_bilocalIntegrand_lt_top
BilocalGaussian : lintegral_fluctuation_mul_fluctuation
BilocalSeries : cov_fluctuation_eq_connected
BilocalSeries : cov_fluctuation_eq_tsum
BilocalSeries : integral_fluctuation_mul_fluctuation_eq_tsum
BilocalSeries : summable_bilocalCoeff
BoxMomentBound : measurable_uncurry_xiField
BoxMomentBound : moment_scaled_dataBoxIntegral_le
BoxMomentBound : uniform_moment_scaled_dataBoxIntegral
CertifiedCoreAssembly : abs_sum_rpow_le
CertifiedCoreAssembly : tendsto_integral_scaled_assembly_of_certified_subgaussian_cores
CertifiedCoreAssembly : uniform_moment_coreSum
ClosureEndpoint : annealed_sampleDatum_single_effectiveTemperature
ClosureEndpoint : annealed_sampleDatum_single_identified
ClosureEndpoint : annealed_sampleDatum_single_identified_of_lt_two
ClosureEndpoint : eLpNorm_le_tsum_coordL2
ClosureEndpoint : exists_p_gt_one_of_lt_two
ClosureEndpoint : memLp_two_of_summableCoordL2
ClosureEndpoint : tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail
CompactBaseFinite : GaussianField
CompactBaseFinite : compactV_map_eq
CompactBaseFinite : integral_compactH_map_eq
CompactBaseFinite : integral_log_compactD_map_eq
CompactBaseFirstMoment : GaussianField.integrable_compactD_rpow
CompactBaseFirstMoment : GaussianField.integral_compactD_eq
CompactBaseFirstMoment : GaussianField.integral_compactD_eq_compactD_zero_mul
CompactBaseFirstMoment : GaussianField.integral_compactD_eq_of_const_diag
CompactBaseFirstMoment : GaussianField.lintegral_compactD_eq_top
CompactBaseFirstMoment : GaussianField.lintegral_exp_eval
CompactBaseGaussian : integral_compactH_eq
CompactBaseGaussian : integral_log_compactD_eq
CompactBaseGaussian : log_compactD_zero_le_integral
CompactBaseGaussian : tendsto_integral_compactH_map
CompactBaseGaussian : tendsto_integral_log_compactD_map
CompactBaseKernel : PSDKernel
CompactBaseKernel : abs_compactH_le
CompactBaseKernel : compactM2_le
CompactBaseKernel : compactQ_nonneg
CompactBaseKernel : compactQnum_le
CompactBaseKernel : compactV
CompactBaseKernel : compactV_le
CompactBaseKernel : compactV_nonneg
CompactBaseKernel : tendsto_compactV_map
CompactBaseQuantise : abs_log_compactD_le
CompactBaseQuantise : compactD
CompactBaseQuantise : compactD_pos
CompactBaseQuantise : compactH
CompactBaseQuantise : exists_measurable_finiteRange_approx
CompactBaseQuantise : tendsto_compactD_map
CompactBaseQuantise : tendsto_compactH_map
CompactBaseQuantise : tendsto_log_compactD_map
CovarianceInterpolation : abs_log_quartetD_le
CovarianceInterpolation : continuousOn_interpL
CovarianceInterpolation : hasDerivAt_interpL
CovarianceInterpolation : integral_log_quartetD_eq
CovarianceInterpolation : integral_quartetH_scaled
CovarianceInterpolation : interpV_nonneg
CovarianceInterpolation : log_quartetD_zero_le_integral
DivisorVariance : abs_exp_neg_sub_le
DivisorVariance : abs_integral_sq_sub_le
DivisorVariance : integral_sq_eq_of_tendsto
DivisorVariance : tendsto_integral_sq
EffectiveTemperature : dataBoxCoeff_leading_zero_phase
EffectiveTemperature : integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance
EffectiveTemperature : neg_zetaEmp_normalLocation
EffectiveTemperature : normalLocation_standard_form
EffectiveTemperature : sum_normalLocation
EffectiveTemperature : variance_phase_normalLocation
ExpectationBridge : abs_sub_clipR_le
ExpectationBridge : tendsto_integral_of_tendstoInDistribution_of_moment
ExpectationBridge : tendsto_integral_quartetD_of_tendstoInDistribution
ExpectationBridge : tendsto_lintegral_top_of_tendstoInDistribution
ExpectationBridge : tendsto_lintegral_top_of_tendstoInDistribution_quartetD
ExponentComparison : exists_exponentPair_of_Q
ExponentComparison : exponentPair_eq_of_population_comparison
ExponentComparison : powerLogRate_pair_eq_of_isTheta_nat
ExponentComparison : tendstoInMeasure_log_div_log_of_population_comparison
FiniteWeightMoment : lintegral_rpow_lintegral_exp_le_mass_rpow
FiniteWeightMoment : moment_scaled_integral_le_population_mass
Fluctuation : fluctuation
Fluctuation : fluctuation_recurrence
Fluctuation : fluctuation_zero
Fluctuation : hasDerivAt_fluctuation
FluctuationSelfNormalised : abs_log_fluctuation_le
FluctuationSelfNormalised : fluctuation_eq_two_mul_gaussMomentJ
FluctuationSelfNormalised : fluctuation_ge_lower
FluctuationSelfNormalised : fluctuation_half_le
FluctuationSelfNormalised : fluctuation_half_sq_le
FluctuationSelfNormalised : fluctuation_succ_le
FluctuationSharpBounds : fluctuation_le_eta
FluctuationSharpBounds : le_fluctuation_of_two_le
FluctuationSharpUpper : fluctuation_eq_exp_mul_integral
FluctuationSharpUpper : fluctuation_le_polynomial_mul_gaussian
GaussianCriticalMoment : fluctuation_mono
GaussianCriticalMoment : integrable_fluctuation_rpow_gaussianReal_iff_of_critical
GaussianDenominator : integral_quartetD
GaussianDenominator : lintegral_fluctuation_gaussianVector
GaussianDenominator : lintegral_quartetD_eq_top
GaussianDenominator : not_integrable_quartetD
GaussianDichotomy : lintegral_gaussMomentJ_eq
GaussianFieldFernique : GaussianField.ofIsGaussian
GaussianFieldFernique : integrable_sq_norm_of_isGaussian
GaussianInsertion : integral_coord_mul_coord_mul_fluctuation
GaussianInsertion : integral_coord_mul_fluctuation
GaussianInsertion : integral_fluctuation_gaussianVector
GaussianInsertion : integral_mul_fluctuation_eq
GaussianInsertion : integral_radialKernel_mul_tilt
GaussianLinearCombination : GaussianField.ofIsGaussianCertificates
GaussianLinearCombination : PSDKernel.kernelMatrix_posSemidef
GaussianLinearCombination : gramFactor_mul_transpose
GaussianLinearCombination : isGaussian_ext_of_moments
GaussianLinearCombination : map_evalCombination_eq_gaussianReal_of_certificates
GaussianLinearCombination : map_evalVec_eq_gaussianVector
GaussianPMoment : gaussianVector_map_eval
GaussianPMoment : integrable_fluctuation_rpow_gaussianReal
GaussianPMoment : integrable_quartetD_rpow
GaussianPMoment : lintegral_fluctuation_rpow_gaussianReal_eq_top
GaussianPMoment : lintegral_quartetD_rpow_eq_top
GaussianPMoment : quartetD_rpow_le
GaussianQuartet : bayes_quartet
GaussianQuartet : integral_quartetH_eq
GaussianQuartet : quartet_identities
GaussianQuartetDet : hasFDerivAt_quartetW
GaussianQuartetDet : polyBoundedPi_quartetW
GaussianQuartetDet : quartetD
GaussianQuartetDet : quartetH
GaussianQuartetDet : quartetM2
GaussianQuartetDet : quartetM2_eq
GaussianQuartetDet : quartetV
GaussianQuartetDet : quartetV_nonneg
GaussianQuartetDet : quartetW
GaussianQuartetDet : quartetW_le
GaussianQuartetDet : quartetW_nonneg
GaussianQuartetGeneral : integral_log_quartetD_eq_gen
GaussianQuartetGeneral : integral_quartetH_eq_gen
GaussianQuartetGeneral : log_quartetD_zero_le_integral_gen
GaussianQuartetGeneral : quartetVgen
GaussianQuartetGeneral : quartetVgen_nonneg
GaussianStein : gaussianReal_stein
GaussianSteinVector : gaussianVector_stein
GaussianSteinVector : stdGaussianPi_stein
GaussianThreshold : lintegral_gaussMomentJ_eq_of_lt
GaussianThreshold : lintegral_gaussMomentJ_eq_top_of_ge
GaussianTilted : integral_mul_exp_gaussianVector
GaussianTilted : integral_mul_mul_exp_gaussianVector
HeadlineGaussian : headline_gaussian_dichotomy
HironakaUnconditional : exists_exponentPair
JointSampleLimit : tendstoInDistribution_scaled_coreSum_sampleDatum
JointSampleLimit : tendsto_integral_scaled_coreSum_sampleDatum
L1GaussianFunctional : map_eq_gaussianReal_of_marginals
L1GaussianFunctional : map_phaseEvalCLM_eq_gaussianReal
L1GaussianFunctionalL2 : map_eq_gaussianReal_of_marginals_of_memLp
L1SeqCLT : clt_l1
Ladder : raiseOp_fluctuation
LeadingCoeffGaussianMoment : ae_etaCoord_eq_zero
LeadingCoeffGaussianMoment : dataBoxCoeff_leading_eq_spatialFace
LeadingCoeffGaussianMoment : integral_dataBoxCoeff_leading_eq
LeadingCoeffGaussianMoment : integral_fluctuation_gaussianReal
LeadingCoeffGaussianMoment : integral_phaseMoment_evalF
LeadingCoeffGaussianMoment : phaseMoment_eq_half_fluctuation
PopulationBoundDischarge : exists_population_bound_scaleA
PopulationBoundDischarge : popBoxMass_eq_monomialBoxReal
PopulationBoundDischarge : tendsto_integral_scaled_assembly_of_dominated_cores
PopulationBoundDischarge : uniform_moment_scaled_dataBoxIntegral_of_dominated
SampleDatum : xiCoord_sampleDatum
SampleDatumLimit : predSum_leading
SampleDatumLimit : scaleA_mul_dataBoxIntegral_eq_orderedRemainder
SampleDatumLimit : tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum
SampleDatumLimit : tendsto_integral_scaled_sampleDatum_single
SampleDatumMGF : lintegral_exp_phase_sampleDatum_le
SampleDatumMGF : phaseEvalCLM
SampleDatumMGF : phaseEval_sampleDatum
SampleDatumMGF : tendsto_integral_scaled_assembly_sampleDatum
SampleExpansion : sample_stochastic_expansion
SamplingCompatibility : dataBoxIntegral_sampleDatum_eq_sampling
SamplingCompatibility : etaCoord_sampleDatum_of_integrable
SamplingCompatibility : evalF_xiCoord_sampleDatum_eq_neg_zetaEmp
SamplingCompatibility : exp_sampling_exponent_eq_core_factor
SamplingCompatibility : phaseEvalCLM_integral
SamplingCompatibility : phaseEval_sampleDatum_of_integrable
SamplingCompatibility : sampling_exponent_eq_sampleDatum_phase
SamplingIdentity : sampling_exponent_eq
SamplingIdentity : sum_mul_eq
ScaledAssembly : isEquivalent_integral_scaled
ScaledAssembly : scaleA
ScaledAssembly : tendstoInDistribution_scaled_assembly
ScaledAssembly : tendstoInMeasure_log_div_log
ScaledAssembly : tendstoInMeasure_zero_of_tendsto_integral_abs
ScaledAssembly : tendsto_integral_scaled_assembly
ScaledAssembly : tendsto_measure_log_of_tendstoInDistribution
ScaledAssembly : tendsto_scaleA_mul_exp_neg
SpatialEnergyLaw : spatialEnergyLaw_tendsto
SpatialLocationLaw : phasePosterior_tendsto_faceLocation
SpatialPhaseLeading : spatialPhase_tendsto
SubgaussianAssembly : integral_dataBoxCoeff_leading_eq_subgaussian
SubgaussianAssembly : tendsto_integral_scaled_assembly_sampleDatum_subgaussian
SubgaussianAssembly : tendsto_integral_scaled_coreSum_sampleDatum_subgaussian
SubgaussianAssembly : tendsto_integral_scaled_sampleDatum_single_subgaussian
SubgaussianPhase : UniformSubgaussianPhase
SubgaussianPhase : hasSubgaussianMGF_empiricalPhase
SubgaussianPhase : lintegral_exp_phase_sampleDatum_le_of_subgaussian
SubgaussianPhase : phaseVar_le_of_uniformSubgaussian
SubgaussianPhase : uniformSubgaussianPhase_of_bounded
SubgaussianPhase : variance_le_of_hasSubgaussianMGF
UniformMomentSubgaussian : empiricalField
UniformMomentSubgaussian : integrable_compactD_rpow_of_subgaussian
UniformMomentSubgaussian : lintegral_compactD_rpow_empirical_le
UniformMomentSubgaussian : lintegral_compactD_rpow_le_of_subgaussian
UniformMomentSubgaussian : measurable_uncurry_eval
UniformMomentSubgaussian : moment_bound_of_dominated
UniformMomentSubgaussian : ofReal_fluctuation_eq_lintegral_gammaWeight
```

### C. Reusable Lean modules — declaration lines

```lean
-- Grammar/EmpiricalConcentration.lean
54:noncomputable def normaliser (Kh : W → ℝ) (n : ℝ) : ℝ := ∫ w, Real.exp (-n * Kh w) ∂π
57:noncomputable def mass (Kh : W → ℝ) (n : ℝ) (E : Set W) : ℝ :=
61:noncomputable def expectation (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ :=
69:theorem integrable_exp {n : ℝ} (hn : 0 ≤ n) :
81:theorem setIntegral_exp_ge_le {κ n : ℝ} (hn : 0 ≤ n) :
99:theorem normaliser_ge {a n : ℝ} (hn : 0 ≤ n) :
120:theorem gibbsMass_ge_le {κ a n : ℝ} (hn : 0 ≤ n) (ha : 0 < π.real {w | K w < a}) :
155:theorem tendsto_gibbsMass_ge {κ : ℝ} (hκ : 0 < κ) :
183:theorem ae_tendsto_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
194:theorem tendsto_measure_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
235:theorem normaliser_le_normaliser {n : ℝ} (hn : 0 ≤ n) :
257:theorem abs_log_normaliser_sub_le [NeZero π] {n : ℝ} (hn : 0 ≤ n) :
288:theorem tendsto_log_normaliser_div
321:theorem exists_sublevel_of_eq_on_zeroSet {W : Type*} [TopologicalSpace W] [T2Space W]
357:theorem abs_expectation_sub_le {φ₀ ε B κ n : ℝ} (hn : 0 ≤ n) (hZ : 0 < normaliser π Kh n)
450:theorem tendsto_expectation_of_eq_on_zeroSet :
486:theorem exists_sublevel_subset_of_isOpen {U : Set W} (hU : IsOpen U)
507:theorem tendsto_mass_compl_of_isOpen {U : Set W} (hU : IsOpen U)
544:theorem tendsto_expectation_of_eq_on_zeroSet_population :
554:theorem coeff_eq_of_eq_on_zeroSet {a : ℕ → ℝ} {c₁ cφ : ℝ} (hc₁ : 0 < c₁)
580:theorem coeff_eq_of_hasLeadingTerm {c₁ cφ lam : ℝ} {k : ℕ} (hc₁ : 0 < c₁)

-- Grammar/GibbsJointRatio.lean
43:noncomputable def numerator (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ :=
46:theorem expectation_eq_div (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) :
49:theorem normaliser_nonneg (Kh : W → ℝ) (n : ℝ) : 0 ≤ normaliser π Kh n :=
53:theorem abs_numerator_le {Kh φ : W → ℝ} {n M : ℝ} (hM : ∀ w, |φ w| ≤ M)
64:theorem abs_expectation_le {Kh φ : W → ℝ} {n M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, |φ w| ≤ M)
79:theorem tendstoInDistribution_expectation (Kh : ι → Ω → W → ℝ) (n : ι → ℝ) (φ : W → ℝ)
103:theorem tendsto_integral_expectation {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ} {M : ℝ}
127:theorem ae_div_eq_of_ae_tendsto {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ}
167:theorem ae_tendsto_expectation_of_eq_on_zeroSet :
179:theorem ae_div_eq_of_eq_on_zeroSet (a : ℕ → ℝ) (ha : ∀ i, a i ≠ 0)

-- Grammar/PosteriorTransfer.lean
43:theorem HasLeadingTerm.eventually_pos (h : HasLeadingTerm Z c lam k) (hc : 0 < c) :
49:theorem HasLeadingTerm.eventually_ne_zero (h : HasLeadingTerm Z c lam k) (hc : c ≠ 0) :
56:theorem HasLeadingTerm.tendsto_div_same_pair (h₁ : HasLeadingTerm Z₁ c₁ lam k)
64:theorem HasLeadingTerm.tendsto_div_zero_of_dominated (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
71:theorem HasLeadingTerm.isLittleO_div_ratio (h₁ : HasLeadingTerm Z₁ 0 lam₁ k₁)
81:theorem HasLeadingTerm.div_isEquivalent (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
105:theorem boltzmannIntegral_eq (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
109:theorem boltzmannIntegral_const_mul (a : ℝ) (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
116:theorem boltzmannIntegral_const (a : ℝ) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
123:theorem boltzmannIntegral_add {F G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
136:theorem hasLeadingTerm_boltzmannIntegral_add {F G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
147:theorem hasLeadingTerm_boltzmannIntegral_const_mul {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
156:noncomputable def posteriorExpectation (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
160:theorem posteriorExpectation_const (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (a : ℝ) {N : ℝ}
169:theorem tendsto_posteriorExpectation_of_hasLeadingTerm {K φ : (Fin d → ℝ) → ℝ}
178:theorem tendsto_posteriorExpectation_zero_of_dominated {K φ : (Fin d → ℝ) → ℝ}

-- Grammar/L1Seq.lean
42:theorem L1Seq.summable_abs (x : L1Seq ι) : Summable fun j => |x j| := by
46:theorem L1Seq.norm_eq_tsum (x : L1Seq ι) : ‖x‖ = ∑' j, |x j| := by
51:noncomputable def coordCLM (j : ι) : L1Seq ι →L[ℝ] ℝ :=
60:theorem measurable_coord (j : ι) : Measurable fun x : L1Seq ι => x j :=
64:theorem exists_finset_exhaustion [Countable ι] :
74:noncomputable def finiteCoords (F : Finset ι) : L1Seq ι →L[ℝ] EuclideanSpace ℝ F :=
88:noncomputable def coordL2 (Y : Ω → L1Seq ι) (j : ι) : ℝ := Real.sqrt (∫ ω, (Y ω j) ^ 2 ∂P)
91:structure SummableCoordL2 (Y : Ω → L1Seq ι) : Prop where
96:theorem coordL2_nonneg (Y : Ω → L1Seq ι) (j : ι) : 0 ≤ coordL2 P Y j := Real.sqrt_nonneg _
98:theorem SummableCoordL2.coord_measurable {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (j : ι) :
103:theorem coord_integral {Y : Ω → L1Seq ι} (hY : Integrable Y P) (j : ι) :
111:theorem integral_abs_coord_le {Y : Ω → L1Seq ι} (hY : ∀ j, MemLp (fun ω => Y ω j) 2 P) (j : ι) :
122:theorem integrable_abs_coord {Y : Ω → L1Seq ι} (hY : ∀ j, MemLp (fun ω => Y ω j) 2 P) (j : ι) :
127:theorem integrable_of_summableCoordL2 [Countable ι] {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
153:noncomputable def singleCLM (j : ι) : ℝ →L[ℝ] L1Seq ι :=
162:noncomputable def truncate (F : Finset ι) : L1Seq ι →L[ℝ] L1Seq ι :=
165:theorem truncate_eq_sum (F : Finset ι) (x : L1Seq ι) :
169:theorem truncate_apply (F : Finset ι) (x : L1Seq ι) (i : ι) :
175:theorem sub_truncate_apply (F : Finset ι) (x : L1Seq ι) (i : ι) :
181:theorem norm_sub_truncate (F : Finset ι) (x : L1Seq ι) :
188:theorem norm_sub_truncate_le_tsum (F : Finset ι) (x : L1Seq ι) :
196:theorem norm_truncate_le (F : Finset ι) (x : L1Seq ι) : ‖truncate F x‖ ≤ ‖x‖ := by
204:theorem tendsto_truncate {F : ℕ → Finset ι} (hF : Monotone F) (hcov : ∀ j, ∃ k, j ∈ F k)
211:theorem measurable_truncate_comp [Countable ι] {Ω : Type*} [MeasurableSpace Ω] {f : Ω → L1Seq ι}
219:theorem measurable_of_coords [Countable ι] {Ω : Type*} [MeasurableSpace Ω] {f : Ω → L1Seq ι}

-- Grammar/ExpectationBridge.lean
38:noncomputable def clipR (R : ℝ) : BoundedContinuousFunction ℝ ℝ :=
45:theorem clipR_apply (R x : ℝ) : clipR R x = max (-R) (min x R) := rfl
47:theorem clipR_of_abs_le {R x : ℝ} (h : |x| ≤ R) : clipR R x = x := by
52:theorem abs_sub_clipR_le {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) (x : ℝ) :
82:noncomputable def truncPowBCF (p : ℝ) (hp : 0 ≤ p) (N : ℕ) : BoundedContinuousFunction ℝ ℝ :=
89:theorem truncPowBCF_apply (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (x : ℝ) :
93:noncomputable def truncPosBCF (N : ℕ) : BoundedContinuousFunction ℝ ℝ :=
99:theorem truncPosBCF_apply (N : ℕ) (x : ℝ) : truncPosBCF N x = min (max x 0) N := rfl
109:theorem tendsto_integral_bcf_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
119:theorem integrable_bcf_comp {α : Type*} [MeasurableSpace α] {ν : Measure α}
127:theorem integrable_of_integrable_rpow_abs {α : Type*} [MeasurableSpace α] {ν : Measure α}
141:theorem integrable_rpow_abs_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
191:theorem abs_integral_sub_clipR_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
207:theorem tendsto_integral_of_tendstoInDistribution_of_moment
253:theorem tendsto_lintegral_top_of_tendstoInDistribution (hX : TendstoInDistribution X atTop Z μ μ')
307:theorem tendsto_integral_quartetD_of_tendstoInDistribution (hβ : 0 < β) (hlam : 0 < lam)
321:theorem tendsto_lintegral_top_of_tendstoInDistribution_quartetD (hβ : 0 < β) (hlam : 0 < lam)

-- Grammar/ScaledAssembly.lean
38:noncomputable def scaleA (lam : ℝ) (m : ℕ) (n : ℕ) : ℝ :=
41:theorem scaleA_of_two_le (lam : ℝ) (m : ℕ) {n : ℕ} (hn : 2 ≤ n) :
44:theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n :=
47:theorem scaleA_pos (lam : ℝ) (m n : ℕ) : 0 < scaleA lam m n := by
54:theorem one_le_log_nat {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
60:theorem tendsto_scaleA_mul_exp_neg (lam : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
74:theorem tendsto_log_scaleA_div_log (lam : ℝ) (m : ℕ) :
97:theorem tendstoInDistribution_scaled_assembly {Zc R : ℕ → Ω → ℝ} {A : ℕ → ℝ} {L : Ω' → ℝ}
113:theorem tendstoInMeasure_zero_of_tendsto_integral_abs {Y : ℕ → Ω → ℝ}
127:theorem tendsto_integral_scaled_assembly {Zc R : ℕ → Ω → ℝ} {A : ℕ → ℝ} {L : Ω' → ℝ}
156:theorem isEquivalent_integral_scaled {Z : ℕ → Ω → ℝ} (lam : ℝ) (m : ℕ) {EL : ℝ} (hEL : 0 < EL)
175:theorem tendsto_measure_log_of_tendstoInDistribution {X : ℕ → Ω → ℝ} {L : Ω' → ℝ}
285:theorem tendstoInMeasure_log_div_log {Z : ℕ → Ω → ℝ} {L : Ω' → ℝ} (lam : ℝ) (m : ℕ)

-- Grammar/SubgaussianAssembly.lean
45:theorem measurable_sampleDatum_of_integrable {d : ℕ} (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
60:theorem tendsto_integral_scaled_assembly_sampleDatum_subgaussian (hk : ∀ j i, 0 < k j i)
96:theorem tendsto_integral_scaled_coreSum_sampleDatum_subgaussian (hb : ∀ I, 0 < bJ I)
147:theorem tendsto_integral_scaled_sampleDatum_single_subgaussian (hk : ∀ i, 0 < k i)
210:theorem integral_phaseMoment_evalF_subgaussian (hcm : ∀ γ, Measurable fun x => c x γ)
257:theorem integral_dataBoxCoeff_leading_eq_subgaussian (hcm : ∀ γ, Measurable fun x => c x γ)

-- Grammar/CertifiedCoreAssembly.lean
33:theorem abs_sum_rpow_le {J : ℕ} {p : ℝ} (hp : 1 ≤ p) (Y : Fin J → ℝ) :
62:theorem exists_uniform_bound_of_eventually {f : ℕ → ℝ} {n₀ : ℕ} {M₀ : ℝ}
77:theorem integral_rpow_abs_le_of_lintegral_le {Y : Ω → ℝ} (hY : Measurable Y) {p B : ℝ}
95:noncomputable def coreSum (β : ℝ) (Nn : ℕ → ℝ) (x : Fin J → ℕ → Ω → DataSpace (n + 1)) (m : ℕ)
101:theorem uniform_moment_coreSum {β c p M : ℝ} (hβ : 0 < β) (hp : 1 ≤ p) (hc : p * β * c < 2)
187:theorem tendsto_integral_scaled_assembly_of_certified_subgaussian_cores {β c p M : ℝ}

-- Grammar/SampleDatumLimit.lean
43:theorem dataBoxCoeff_eq_zero_of_multCount_lt (x : DataSpace (n + 1)) {j : ℕ}
56:theorem predSum_leading (x : DataSpace (n + 1)) (N : ℝ) :
71:theorem orderedRemainder_leading (x : DataSpace (n + 1)) (N : ℝ) :
80:theorem scaleA_mul_dataBoxIntegral_eq_orderedRemainder (x : DataSpace (n + 1)) {N : ℕ}
99:theorem tendstoInDistribution_congr_eventually {X X' : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
116:theorem tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum (hk : ∀ i, 0 < k i) {β : ℝ}
158:theorem tendsto_integral_scaled_sampleDatum_single (hk : ∀ i, 0 < k i) {β p M M₀ : ℝ}

-- Grammar/JointSampleLimit.lean
38:theorem tendstoInMeasure_congr_eventually {ι : Type*} {l : Filter ι} {f f' : ι → Ω → ℝ}
43:theorem tendstoInMeasure_zero_add {f g : ℕ → Ω → ℝ}
62:theorem tendstoInMeasure_zero_finset_sum {J : Type*} (s : Finset J) {f : J → ℕ → Ω → ℝ}
84:theorem tendsto_scaleA_div_scaleA {lam lam' : ℝ} {m m' : ℕ}
135:theorem jointSampleDatum_apply_eq_sampleDatum (hcm : ∀ I γ, Measurable fun x => c I x γ)
154:noncomputable def jointLeadingCoeff (β lam : ℝ) (mult : ℕ)
163:theorem continuous_jointLeadingCoeff (hk : ∀ I i, 0 < k I i) {β : ℝ} (hβ : 0 < β) (lam : ℝ)
176:theorem tendstoInDistribution_scaled_coreSum_sampleDatum (hk : ∀ I i, 0 < k I i) {β : ℝ}
357:theorem tendsto_integral_scaled_coreSum_sampleDatum (hk : ∀ I i, 0 < k I i) {β p M M₀ : ℝ}

-- Grammar/ClosureEndpoint.lean
51:theorem eLpNorm_coord_eq {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (j : ι) :
62:theorem eLpNorm_truncate_le {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (F : Finset ι) :
78:theorem eLpNorm_le_tsum_coordL2 {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
94:theorem memLp_two_of_summableCoordL2 {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
103:theorem exists_p_gt_one_of_lt_two {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2) :
123:theorem memLp_two_sampleObs_of_certificate (hcm : ∀ γ, Measurable fun x => c x γ)
133:theorem tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail (hk : ∀ i, 0 < k i)
180:theorem annealed_sampleDatum_single_identified (hk : ∀ i, 0 < k i)
253:theorem annealed_sampleDatum_single_effectiveTemperature (hk : ∀ i, 0 < k i)
287:theorem annealed_sampleDatum_single_identified_of_lt_two (hk : ∀ i, 0 < k i)

-- Grammar/CompactBaseGaussian.lean
37:theorem map_quantise_ne_zero {q : K → K} (hq : Measurable q) (hρ : ρ ≠ 0) : ρ.map q ≠ 0 := by
45:theorem map_quantise_real_univ {q : K → K} (hq : Measurable q) :
51:theorem PSDKernel.exists_diag_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, 𝒞.C x x ≤ c := by
58:theorem integrable_const_mul_one_add_sq (hsq : Integrable (fun ω => ‖g ω‖ ^ 2) P) (C : ℝ) :
65:theorem measurable_compactD_map (hβ : 0 < β) (hlam : 0 < lam)
76:theorem measurable_log_compactD_map (hβ : 0 < β) (hlam : 0 < lam)
83:theorem measurable_compactH_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
96:theorem measurable_compactV_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
119:theorem tendsto_integral_compactH_map :
135:theorem abs_compactV_map_le {c : ℝ} (hc : ∀ x, 𝒞.C x x ≤ c) (n : ℕ) (ω : Ω) :
142:theorem tendsto_integral_compactV_map :
160:theorem tendsto_integral_log_compactD_map :
195:theorem measurable_eval_smul (s : ℝ) (x : K) :
202:theorem integrable_sq_norm_smul (s : ℝ) :
212:theorem integral_compactH_eq :
224:theorem integral_log_compactD_eq :
294:theorem log_compactD_zero_le_integral :

-- Grammar/GaussianQuartetGeneral.lean
33:noncomputable def quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
37:noncomputable def quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
40:theorem quartetDiag_eq_of_const {b : Matrix (Fin m) (Fin m) ℝ} {c : ℝ} (hc : ∀ i, b i i = c)
46:theorem quartetVgen_eq_quartetV {b : Matrix (Fin m) (Fin m) ℝ} {c : ℝ} (hc : ∀ i, b i i = c)
51:theorem quartetDiag_smul (b : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (g : Fin m → ℝ) :
56:theorem quartetVgen_smul (b : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (g : Fin m → ℝ) :
66:theorem quartetQ_le_quartetDiag {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
81:theorem quartetDiag_nonneg (b : Matrix (Fin m) (Fin m) ℝ) (hb : ∀ i, 0 ≤ b i i)
86:theorem quartetVgen_nonneg {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
94:theorem continuous_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
98:theorem continuous_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
106:theorem polyBoundedPi_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
111:theorem polyBoundedPi_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
123:theorem integrable_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
127:theorem integrable_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
132:theorem integral_quartetH_eq_gen :
195:theorem integral_quartetH_scaled_gen {s : ℝ} (hs : 0 ≤ s) :
210:noncomputable def interpVgen (β lam : ℝ) (ρ : Fin m → ℝ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
218:theorem interpVgen_eq (s : ℝ) :
226:theorem hasDerivAt_interpL_gen {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
266:theorem continuousOn_interpVgen : ContinuousOn (interpVgen β lam ρ A) (Icc 0 1) := by
282:theorem interpVgen_nonneg (s : ℝ) : 0 ≤ interpVgen β lam ρ A s :=
287:theorem integral_log_quartetD_eq_gen :
300:theorem log_quartetD_zero_le_integral_gen :

-- Grammar/UniformMomentSubgaussian.lean
43:noncomputable def gammaWeight (lam α : ℝ) : Measure ℝ :=
46:theorem measurable_gammaDensity (lam α : ℝ) :
50:theorem gammaWeight_univ {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
67:theorem gammaWeight_Iic (lam α : ℝ) : gammaWeight lam α (Iic 0) = 0 := by
77:theorem ofReal_fluctuation_eq_lintegral_gammaWeight {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
103:theorem measurable_uncurry_eval (G : Ω → C(K, ℝ)) (hG : ∀ x, Measurable fun ω => G ω x) :
119:noncomputable def subgaussianBound (β lam c p M : ℝ) : ℝ :=
125:theorem lintegral_compactD_rpow_le_of_subgaussian {β lam c p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
244:noncomputable def empiricalField (Z : ℕ → Ω → K → ℝ) (n : ℕ) (ω : Ω) (x : K) : ℝ :=
247:theorem measurable_uncurry_empiricalField {Z : ℕ → Ω → K → ℝ}
260:theorem lintegral_compactD_rpow_empirical_le {β lam p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
277:theorem ofReal_compactD {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (g : C(K', ℝ)) :
282:theorem measurable_compactD_comp {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (G : Ω → C(K', ℝ))
298:theorem integrable_compactD_rpow_of_subgaussian {β lam c p : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
336:theorem moment_bound_of_dominated {Y D : ℕ → Ω → ℝ} {K₀ B p : ℝ} (hK : 0 ≤ K₀) (hB : 0 ≤ B)

```

### D. Notation and limits (as the note uses them)

* `n` = sample size = inverse temperature multiplier in `e^{−nK}`; `β` the fixed inverse temperature of the
  normal form; dataset `(x_i)` i.i.d. from the truth; the empirical phase `K_n = K + ξ_n/√n` with `ξ_n` the
  centred fluctuation; the Gaussian limit `G` of `ξ_n` (a Gaussian field on the resolved space / a compact base).
* Randomness: over the dataset (probability space `(Ω, P)`); the prior/model/resolution are fixed.
* `Z_n[φ] = ∫ φ ϕ e^{−nK_n}` (numerator), `E_n[φ] = Z_n[φ]/Z_n[1]` (normalised posterior expectation);
  "self-normalised" quantities are the ratios.
* Convergence modes used: pathwise (a.s.), in probability, in distribution (⇒), in `L¹`/expectation
  (annealed); limits are in `n → ∞` with `β` fixed, sometimes at the Gaussian limit first (level 2).
