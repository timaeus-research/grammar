# Direction consult #57 — after Astra #56 units 6, 7, 8, 10: what remains for the companion note, and what next for the paper

Setting unchanged: Lean 4 + Mathlib `v4.33.1`, repo `timaeus-research/grammar` (434 modules, zero `sorry`/`axiom`, Headlines I–CXXXIII), `timaeus-research/hironaka` a pinned dependency consumed only through axiom-clean declarations. Your #56 programme has been executed as follows (all axiom-clean, all checked against Monte Carlo):

## Landed since #56
- **Unit 4 (quartet, CXXVI–CXXVII)**: `quartet_identities` — for `G = AZ` with constant covariance diagonal `c`, `D, W_i, M₂, H, V` polynomially bounded, `M₂ = λ/β + H/2` pointwise, `0 ≤ V ≤ cM₂`, `E[H] = βE[V]`, `ν := E[H]/2 ≥ 0`, `E[V] = 2ν/β`, `E[M₂] = λ/β + ν`, every `β > 0`; scalar/coordinate/vector Stein identities (`gaussianReal_stein`, `stdGaussianPi_stein`, `gaussianVector_stein`).
- **Unit 1 (variance normalisation)**, **unit 3 (sampling identity `N = n`, `ξ_n = −ζ_n`)**.
- **Unit 10 (CXXVIII)**: `lintegral_annealedZ : E₊Z_n(β) = ∫(E e^{−βf(X,u)})^n dπ(u)` in `ℝ≥0∞`, `lintegral_annealedZ_one : E Z_n(1) = π(W)` under `E e^{−f} = 1`.
- **Unit 6 (CXXIX)**: tilted moments `E e^{θG_j} = e^{θ²B_jj/2}`, `E[G_i e^{θG_j}] = θB_ij e^{θ²B_jj/2}`, `E[G_iG_{i'}e^{θG_j}] = (B_{ii'} + θ²B_ijB_{i'j})e^{θ²B_jj/2}` (`GaussianTilted.lean`); Fubini on `(0,∞)×Ω` (`integral_mul_fluctuation_eq`) + tilted Gamma integral `∫₀^∞ t^{μ−1}e^{−βt}(β√t)^k e^{β²tB_jj/2}dt = β^kΓ(μ+k/2)(βδ)^{−(μ+k/2)}`; for `δ = 1 − βB_jj/2 > 0`: `E S_μ(G_j) = Γ(μ)(βδ)^{−μ}`, `E[G_iS_μ(G_j)] = βB_ijΓ(μ+½)(βδ)^{−(μ+½)}`, `E[G_iG_{i'}S_μ(G_j)] = B_{ii'}Γ(μ)(βδ)^{−μ} + β²B_ijB_{i'j}Γ(μ+1)(βδ)^{−(μ+1)}`, with integrability.
- **Unit 7 (CXXX–CXXXII)**: `E₊[S_λ(G_i)S_λ(G_j)] = ∫₀^∞∫₀^∞ t^{λ−1}s^{λ−1}e^{−at−bs+h√(ts)}` in `ℝ≥0∞` (`a = β(1−βB_ii/2)`, `b = β(1−βB_jj/2)`, `h = β²B_ij`); finite for `a,b > 0`, `h < 2√(ab)` (AM–GM `h√(ts) ≤ ρ(at+bs)`, `ρ = max(h,0)/(2√(ab))`); infinite for `h > 2√(ab)` (cone around the ray `s = (a/b)t`); for `|h| < 2√(ab)` the absolutely convergent series `E[S_λ(G_i)S_λ(G_j)] = ∑_r (h^r/r!)Γ(λ+r/2)²(ab)^{−(λ+r/2)}` (`integral_tsum` with absolute-convergence hypothesis = Tonelli at `|h|`), `Cov = ∑_{r≥1}` and `= ∬ t^{λ−1}s^{λ−1}e^{−at−bs}(e^{h√(ts)}−1)`. NOT formalised: the critical line `h = 2√(ab)` (finite iff `λ < 1/4`), the cases `a ≤ 0` or `b ≤ 0`, `prop:moments`.
- **Unit 8 (CXXXIII)**: `L(s) = E log D(√s G)` (the expectation of `log D` under `gaussianVector (√s • A)`, covariance `s AAᵀ`) is continuous on `[0,1]`, differentiable on `(0,1)` with `L'(s) = (β²/2)E[V_s(G)] ≥ 0` (differentiation under the integral on `(s₀/2, 2)` with polynomial domination, Gaussian IBP at scale `√s`: `E H(√sG) = βs E V(√sG)`), so `E log D(G) = log(β^{−λ}Γ(λ)∑ρᵢ) + (β²/2)∫₀¹E[V_s(G)]ds ≥ log D(0)`, every `β > 0`. Key input: `|log D(g)| ≤ |log∑ρ| + |log ρ_j| + ∑_i|log S_λ(g_i)|` with `|log S_λ(a)| ≤ K + βa²/2 + 2λ|a|`.
- The note `averaging_dataset.tex` (appended in its CURRENT form, 64 Lean dots, pinned to grammar `0560fb2`) has been restructured per your D-plan: heuristic diagrammatics and phase transitions are in appendices; every formalised statement carries a dot.

## Interfaces you may rely on
`fluctuation β lam a := ∫_{Ioi 0} t^{lam−1}e^{−βt+βa√t}`; `gaussianVector A := (stdGaussianPi (n+1)).map A.mulVec` for `A : Matrix (Fin m) (Fin (n+1)) ℝ` (so every centred Gaussian vector on `Fin m → ℝ` is covered); `quartetD/W/R/M2/H/Q/V`; `PolyBoundedPi` with closure lemmas (`const, coord, mul, add, const_mul, neg, sub, finset_sum, abs, of_abs_le, smul_bound`) and `integrable_of_polyBoundedPi`; `integral_gaussianVector`; `bilocalIntegrand`, `bilocalCoeff`; `interpL`, `interpV`. Mathlib: `IsGaussianProcess`, `HasGaussianLaw`, `IsGaussian`, Fernique `exists_integrable_exp_sq`, `ContinuousMap`, `BoundedContinuousFunction`, finite-measure integration, `tendsto_integral_of_dominated_convergence`, `MeasureTheory.tendsto_integral_of_tendsto_of_...` (UI-type results: `tendstoInMeasure`, `Integrable.tendsto_integral_of_uniformIntegrable`? — please name the right one), `ProbabilityTheory.tendsto_integral_of_forall_integral_le_of_...`.

## Questions
**Q1 (unit 9: compact base).** Is the discretisation transfer worth doing now? If yes, give the *minimal* formal set-up that avoids the trap you flagged: e.g. (i) hypothesis "`G : Ω → C(K,ℝ)` measurable and for every finite family `w_1..w_m` the vector `(G(w_1),…,G(w_m))` has law `gaussianVector A` for some `A` with `AAᵀ_{ii} = c`" (is this the right way to say "centred Gaussian process with continuous paths and constant diagonal" without `IsGaussianProcess`?), (ii) `ρ` a finite positive measure on `K`, `D(G) = ∫ S_λ(G(w))dρ(w)`, `M₂, H, V` analogously, (iii) the statements to transfer: `E[H] = βE[V]`, `E log D ≥ log D(0)`, the interpolation identity. What exactly needs Fernique (uniform-in-partition domination of `log D` and `V` by polynomials in `‖G‖_∞`), and is there a cheaper route via the *exact* finite statements (e.g. Riemann sums of `ρ` by atomic measures with `ρ_i = ρ(K_i)` and points `w_i ∈ K_i`, pathwise convergence by uniform continuity of `G` on compact `K`, expectations by dominated convergence with the bound `|log D| ≤ C(1+‖G‖_∞)²` and `E(1+‖G‖_∞)^k < ∞`)? Rank against the alternatives below; give a bound on the number of units.

**Q2 (p-th moment, `prop:moments`).** The `p`-fold Tonelli gives `E₊[S_λ(Y)^p] = ∫_{(0,∞)^p} ∏t_i^{λ−1} e^{−β∑t_i + (β²c/2)(∑√t_i)²}`; the quadratic form `∑x_i² − (βc/2)(∑x_i)²` on `ℝ^p` is positive definite iff `βcp/2 < 1`, so finiteness for `βcp < 2` follows from `(∑x_i)² ≤ p∑x_i²`, and divergence for `βcp > 2` along the diagonal ray, exactly as in the bilocal case (which is `p = 2`, `X = Y`, consistent: `h < 2√(ab)` ⟺ `βc < 1`). Is a `p`-dimensional version (on `Fin p → ℝ` with `Measure.pi`) worth a unit, or should the note simply cite the `p = 2` case and state the general criterion as established-not-formalised? The endpoint `βcp = 2` (finite iff `λ < (p−1)/(2p)`) we would leave unformalised.

**Q3 (dataset-facing).** Your unit 10 also asked for "finite-sample expectation asymptotics under an explicit UI/moment hypothesis on the scaled empirical quantities, using the existing stochastic expansion and posterior transfer". Grammar has: `sample_stochastic_expansion` (the coefficients and normalised remainders converge in distribution to those at the Gaussian limit `G`, via the ℓ¹ CLT), the finite-resolution quartet at `G`, and the annealed identity. Please state the *cleanest* theorem of the form "if the scaled empirical leading coefficients `C_n` are uniformly integrable (or `sup_n E|C_n|^{1+ε} < ∞`) then `E C_n → E C(G)` where `E C(G)` is given by `Q = 0` (finite iff `β < 1`, `c = 2`)", with the Mathlib names for the UI ⇒ convergence-of-expectations step (I believe `MeasureTheory.tendsto_integral_of_tendsto_of_...`/`ProbabilityTheory` has `tendsto_integral_of_...uniformIntegrable`; if not, the standard truncation argument). Is convergence in distribution enough, or does grammar need convergence of the *joint* law on a product space? Also: is `E D(G) = ∑ρ_iΓ(λ)(βδ)^{−λ}` (finite resolution) plus its ENNReal divergence at `β ≥ 1` worth recording as a one-line corollary?

**Q4 (paper side).** With the note's programme essentially complete, should the next campaign return to the paper? Candidates: A2 (tangential/normal weighted-box decomposition — please restate precisely, we lost the details), A3 (positive-gap remainder), the analytic-core decomposition modulo an exponentially small remainder for a `ResolutionCover` with analytic charts (from #55), or anything the hironaka dependency now makes provable. Rank ≤ 4 units with precise statements and non-claims.

**Q5 (note text).** Read the appended note critically: any remaining error, overclaim, or sentence that no longer matches what is formalised (in particular the sentences after `prop:moments`, in `sec:relation`, `sec:discussion`, `app:heuristic`)? Give exact replacement sentences. Anything that should now be *promoted* from appendix to main text, or demoted?

## Ask
Ranked, bounded programme (≤ 8 units) across Q1–Q4 with precise Lean-level statements, Mathlib inputs, traps, non-claims; plus the Q5 edit list. Stop rule as before.

---
## Appendix: the current note `averaging_dataset.tex`
\documentclass[11pt]{article}
\usepackage{amsmath,amssymb,amsthm}
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
\newcommand{\grammarLeanCommit}{0560fb2}
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
The Taylor tree expansion of the grammar paper writes the partition function $Z_n$ as a sum of leaf contributions in which the fluctuation function $S_\lambda$ is evaluated on the empirical process $\xi_n$; Watanabe's averaged quantities are expectations of such expressions over the dataset. This note isolates what is rigorous in that programme once $\xi_n$ is replaced by its Gaussian limit $G$: exact Gaussian averages of fluctuation functions with their exact domains of finiteness, and---the main result---the \emph{self-normalised Gaussian posterior identities} at finite resolution: for finitely many base points and a centred Gaussian vector $G$, the Schwinger--Dyson identity and Gaussian integration by parts hold and every normalised quantity is integrable for \emph{every} $\beta>0$, giving the Bayes-quartet algebra $\lambda/\beta\pm\nu$, $(\lambda-\nu)/\beta\pm\nu$ with $\nu\ge0$. These statements are formalised in Lean (blue dots). The diagrammatic reorganisation that motivated the note is kept as discussion and as an explicitly heuristic appendix; formulas that were wrong or unsupported in earlier drafts are corrected there.
\end{abstract}

\section{Scope and normalisation}\label{sec:scope}

\paragraph{Three levels.} Everything below is one of the following, and the Lean remarks say which.
\begin{enumerate}
\item \emph{Exact finite-sample identities} of the sampling model (no probability): the sampling identity $N=n$ and the sign of the fluctuation (\cref{sec:sampling}), the annealed identity $\mathbb E Z_n(1)=\pi(W)$ (\cref{sec:grammar}).
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

\begin{remark}[Lean]
The fluctuation function, its derivatives, the recurrence and the ladder algebra are formalised in the grammar library (\S4 of the paper); the normalisation identity $S_\mu=2J_{2\mu}$ is new to this note. Blue dots link to the formal statements, pinned at commit \texttt{\grammarLeanCommit}.
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
In the Lean formalisation of the paper the empirical Taylor datum has phase coefficients $n^{-1/2}\sum_i(c_\gamma(X_i)-\mathbb E c_\gamma)$ entering the standard integral with the sign $+\beta\sqrt N u^k\xi$\leanrefL{Grammar/AnalyticCertificate.lean\#L165}{dataPhase\_sampleDatum}. By \cref{prop:sampling} the coefficient family $c_\gamma(x)$ of the library is therefore that of $-a(x,\cdot)$ in the convention \eqref{eq:a_defn}, equivalently of the coefficient of $\log p-\log q$. A centred Gaussian limit has the same law under global negation, so the limiting statements are unaffected, but the finite-sample identity is not.
\end{remark}

\begin{remark}[Well-definedness on the exceptional divisor]
Both $a(x,u)$ and $\xi_n(u)$ are defined on the whole chart, including the divisor $\{\phi=0\}$, where $\xi_n(u)=-n^{-1/2}\sum_ia(X_i,u)$. The na\"ive empirical process $\sqrt n(K_n-K)/\sqrt K$ in the original coordinates is not.
\end{remark}

\subsection{The resolved covariance and the variance normalisation}\label{subsec:resolved_covariance}

By the central limit theorem \cite[Theorem 6.2]{watanabeAlgebraicGeometryStatistical2009} (in the Lean library, the $\ell^1$ central limit theorem for the Taylor data\leanrefL{Grammar/L1SeqCLT.lean\#L64}{clt\_l1}) $\xi_n$ converges in law to a centred Gaussian process $G$ with covariance
\begin{equation}\label{eq:resolved_covariance}
C(u,u')=\mathbb E[G(u)G(u')]=\mathbb E_X[a(X,u)a(X,u')]-\phi(u)\phi(u').
\end{equation}
On the divisor the second term vanishes. The diagonal there is fixed by the likelihood normalisation $\mathbb E_Xe^{-f(X,u)}=\int p(x\mid\pi(u))\,dx=1$ (which requires the support of $p(\cdot\mid w)$ to contain that of $q$):

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
Along any approach to a divisor point---$\phi_t\to0$, $h_t\to h_0$, with a uniform cubic envelope $\mathbb E[|a_t|^3e^{|\phi_ta_t|}]\le M$---one has $\mathbb E[a_t^2]\to2h_0$\leanrefL{Grammar/DivisorVariance.lean\#L115}{tendsto\_integral\_sq}; if moreover the second moments converge to that of a limit coefficient $a_0$ (for instance $a_t\to a_0$ in $L^2$), then $\mathbb E[a_0^2]=2h_0$ exactly\leanrefL{Grammar/DivisorVariance.lean\#L142}{integral\_sq\_eq\_of\_tendsto}. In the normalised standard form $K=\phi^2$ ($h\equiv1$), the covariance diagonal on the divisor is
\begin{equation}\label{eq:variance_normalised}
C\big((0,w),(0,w)\big)=\mathbb E_X\big[a(X,(0,w))^2\big]=2.
\end{equation}
\end{cor}

\begin{remark}[Why the hypothesis $K=\phi^2h$ is needed]
The statement ``$\mathbb E e^{-\phi a}=1$ and $\phi\to0$ imply $\mathbb E a^2\to2$'' is false without control of $\mathbb E[\phi a]$: for $Z\sim N(0,1)$ and $a_\phi=\sigma Z+\phi\sigma^2/2$ one has $\mathbb E e^{-\phi a_\phi}=1$ and $\mathbb E a_\phi^2\to\sigma^2$. Pointwise real analyticity of $a(x,\cdot)$ does not by itself supply the integrable envelope or the $L^2$-continuity; in the Lean library these are hypotheses, to be discharged by the analytic coefficient envelopes of Hypothesis~I.
\end{remark}

\begin{remark}[Relation to the Fisher information]\label{rem:fisher}
For a one-dimensional regular model with true parameter $w_0$, $K(w)=\tfrac12I(w_0)(w-w_0)^2+O((w-w_0)^3)$; with $u=\sqrt{I/2}\,(w-w_0)+O((w-w_0)^2)$ one has $K=u^2$, $k=1$, and $a(x,u)=-s(x)/\sqrt{I/2}+O(u)$ where $s$ is the score, so that $C(0,0)=\mathbb E[s^2]/(I/2)=2$, confirming \eqref{eq:variance_normalised}. In several dimensions a blow-up introduces directional variables and the resolved coefficient depends on them; there is no analogous closed formula in terms of the Fisher matrix, and none is claimed.
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
It is finite if and only if $A>0$, $B>0$ and either $H<2\sqrt{AB}$\leanrefL{Grammar/BilocalGaussian.lean\#L239}{lintegral\_bilocalIntegrand\_lt\_top}, or $H=2\sqrt{AB}$ and $\lambda<1/4$; in particular it is infinite for $A,B>0$ and $H>2\sqrt{AB}$\leanrefL{Grammar/BilocalDivergence.lean\#L44}{lintegral\_bilocalIntegrand\_eq\_top}. When $A,B>0$ and $|H|<2\sqrt{AB}$ the cross-pairing series converges absolutely\leanrefL{Grammar/BilocalSeries.lean\#L182}{summable\_bilocalCoeff} and
\begin{equation}\label{eq:bilocal_series}
\mathbb E\big[S_\lambda(X)S_\lambda(Y)\big]=\sum_{r\ge0}\frac{H^r}{r!}\,\frac{\Gamma(\lambda+r/2)^2}{(AB)^{\lambda+r/2}}.\leanrefL{Grammar/BilocalSeries.lean\#L234}{integral\_fluctuation\_mul\_fluctuation\_eq\_tsum}
\end{equation}
\end{prop}
\begin{proof}
Tonelli and the joint moment generating function $\mathbb E\,e^{xX+yY}=e^{(cx^2+2bxy+c'y^2)/2}$ give \eqref{eq:bilocal_integral} with $x=\beta\sqrt t$, $y=\beta\sqrt s$. For $A,B>0$ and $H<2\sqrt{AB}$ the AM--GM bound $H\sqrt{ts}\le\rho(At+Bs)$ with $\rho=\max(H,0)/(2\sqrt{AB})<1$ dominates the integrand by a product of two Gamma integrands; for $H>2\sqrt{AB}$ the exponent is $t\,\psi(u)$ along the ray $s=ut$, with $\psi(A/B)=\sqrt{A/B}\,(H-2\sqrt{AB})>0$, and the integral over a cone around this ray is already infinite. For $|H|<2\sqrt{AB}$, expand $e^{H\sqrt{ts}}$ and integrate term by term: the absolute-convergence hypothesis is the Tonelli computation at $|H|$, finite by the first part, so signed convergence is a consequence of the integrability of the positive integrand at $|H|$ and not an input. The endpoint $H=2\sqrt{AB}$ (finite iff $\lambda<1/4$) is not formalised: set $t=x^2$, $s=y^2$; at criticality the exponent vanishes along an interior ray, and integrating in the transverse Gaussian direction leaves a tail $\int^\infty R^{4\lambda-2}\,dR$.
\end{proof}
For $c=c'=2$ this reads
\[
\mathbb E\big[S_\lambda(X)S_\lambda(Y)\big]=\frac1{\beta^{2\lambda}}\sum_{r\ge0}\frac{\Gamma(\lambda+r/2)^2}{r!}\,(\beta b)^r(1-\beta)^{-(2\lambda+r)},
\]
finite for $0<\beta<1$ when $b\le0$ and for $\beta<(1+b/2)^{-1}$ when $b>0$; at $b=2$ the critical value is $\beta=1/2$, where the integral is finite iff $\lambda<1/4$. Finiteness depends on the \emph{sign} of $b$ (a negative covariance helps), absolute convergence of the series on $|b|$. The $r=0$ term is the disconnected part $\mathbb ES_\lambda(X)\,\mathbb ES_\lambda(Y)$; the connected part is the sum over $r\ge1$, in integral form
\[
\operatorname{Cov}\big(S_\lambda(X),S_\lambda(Y)\big)=\iint t^{\lambda-1}s^{\lambda-1}e^{-\beta(1-\beta)(t+s)}\big(e^{\beta^2b\sqrt{ts}}-1\big)\,dt\,ds\leanrefL{Grammar/BilocalSeries.lean\#L274}{cov\_fluctuation\_eq\_connected}
\]
(the series form $\sum_{r\ge1}$ of the covariance is \leanrefL{Grammar/BilocalSeries.lean\#L250}{cov\_fluctuation\_eq\_tsum}, and integrability of $S_\lambda(X)S_\lambda(Y)$ below threshold is \leanrefL{Grammar/BilocalGaussian.lean\#L290}{integrable\_fluctuation\_mul\_fluctuation})
(rescaling $t,s$ by $\beta$ gives the form $\beta^{-2\lambda}\iint\cdots e^{-(1-\beta)(t+s)}(e^{\beta b\sqrt{ts}}-1)$ of earlier drafts, up to the normalisation factor $4$). The simplest bilocal diagram is the $r=1$ term: two $S_\lambda$-vertices joined by one propagator $b$, each dressed by local tadpoles (\cref{fig:bilocal_diagrams}).

\IfFileExists{bilocal_diagram_figure.tex}{\input{bilocal_diagram_figure}}{}

\begin{prop}[Higher moments]\label{prop:moments}
For $Y\sim N(0,c)$ and an integer $p\ge1$, $\mathbb E[S_\lambda(Y)^p]<\infty$ if $\beta cp<2$, $=\infty$ if $\beta cp>2$, and at $\beta cp=2$ it is finite if and only if $\lambda<\frac{p-1}{2p}$. (This follows from $S_\lambda(a)\sim2\sqrt{\pi/\beta}\,(a/2)^{2\lambda-1}e^{\beta a^2/4}$ as $a\to+\infty$.)
\end{prop}
So $\beta<1/p$ (for $c=2$) is the strict subcritical domain of the $p$-th moment, not an exact threshold including its boundary, and it is not automatically the threshold for spatially integrated quantities. \Cref{prop:bilocal} is formalised for $A,B>0$ off the critical line $H=2\sqrt{AB}$, for a Gaussian vector $G=AZ$ with $X=G_i$, $Y=G_j$ and $c,c',b$ the entries $B_{ii},B_{jj},B_{ij}$ of $AA^{\mathsf T}$; the critical line, the cases $A\le0$ or $B\le0$, and \cref{prop:moments} are established but not formalised.

\subsection{Worked examples: the floor-rises leaf}\label{subsec:floor_rises}

Take the exponent data $d=7$, $k_i=1$, $h=(0,0,0,2,2,4,4)$ of the paper: the minimising set is $\{1,2,3\}$, $\lambda=1/2$, the alive coordinates are $w=(u_4,\dots,u_7)$ with weight $w^\mu$, $\mu=(1,1,3,3)$. The leading leaf integral is $\int_{[0,b]^4}w^\mu\eta(0,w)S_{1/2}(G(0,w))\,dw$, and by \cref{prop:Q0} with $c=2$, for $\beta<1$,
\begin{equation}\label{eq:floor_rises_averaged}
\mathbb E\int w^\mu\,\eta(0,w)\,S_{1/2}(G_w)\,dw=\frac{\Gamma(1/2)}{\sqrt{\beta(1-\beta)}}\int_{[0,b]^4}w_4w_5w_6^3w_7^3\,\eta(0,0,0,w)\,dw,
\end{equation}
the expectation passing through the $w$-integral because the Gaussian variance is constant on the divisor. For two copies of the leaf at $w\neq w'$ the connected two-point function is, by \cref{prop:bilocal} with $\lambda=1/2$,
\[
\operatorname{Cov}\big(S_{1/2}(G_w),S_{1/2}(G_{w'})\big)=\frac1\beta\sum_{r\ge1}\frac{\Gamma(\frac12+\frac r2)^2}{r!}(\beta b)^r(1-\beta)^{-(1+r)},
\qquad\text{$r=1$ term: }\ \frac{b(w,w')}{(1-\beta)^2},
\]
valid for $\beta<(1+b/2)^{-1}$ (earlier drafts had a spurious factor $\pi$).

\section{Self-normalised finite Gaussian posteriors: the quartet}\label{sec:quartet}

The quantities of statistical interest are normalised, and the normalisation is what makes them finite at every temperature. Fix $m\ge1$ base points, weights $\rho_i>0$, and a centred Gaussian vector $G=(G_1,\dots,G_m)$ with covariance $b_{ij}$, $b_{ii}=c$; write $g$ for a value of $G$. Define
\begin{align}
D(g)&=\sum_i\rho_iS_\lambda(g_i)\leanrefL{Grammar/GaussianQuartetDet.lean\#L53}{quartetD},&
W_i(g)&=\frac{\rho_iS_{\lambda+1/2}(g_i)}{D(g)}\leanrefL{Grammar/GaussianQuartetDet.lean\#L60}{quartetW},\\
M_2(g)&=\frac{\sum_i\rho_iS_{\lambda+1}(g_i)}{D(g)}\leanrefL{Grammar/GaussianQuartetDet.lean\#L68}{quartetM2},&
H(g)&=\sum_ig_iW_i(g)\leanrefL{Grammar/GaussianQuartetDet.lean\#L71}{quartetH},\\
V(g)&=c\,M_2(g)-\sum_{i,j}b_{ij}W_i(g)W_j(g)\leanrefL{Grammar/GaussianQuartetDet.lean\#L78}{quartetV}.&&
\end{align}
Under the marked posterior $\pi_g(i,T)\propto\rho_i\,T^{2\lambda-1}e^{-\beta T^2+\beta g_iT}$ on base points and the radial variable, $W_i=\frac12\langle T\,\mathbb 1_i\rangle_g$, $M_2=\langle T^2\rangle_g$, $H=\langle g_iT\rangle_g$ (the pairing of the field with the first moment), and $V$ is the connected two-point function: with $b_{ij}=\langle h_i,h_j\rangle$, $V=\mathbb E_{\pi_g}\|Th_i\|^2-\|\mathbb E_{\pi_g}[Th_i]\|^2$.

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
the first by Cauchy--Schwarz under the radial measure ($\int y^{\lambda-1}e^{\cdots}(\sqrt y-r)^2\,dy\ge0$), the others from it and the recurrence. Hence $0\le W_i(g)\le\sqrt{2\lambda/\beta}+|g_i|/2$\leanrefL{Grammar/GaussianQuartetDet.lean\#L171}{polyBoundedPi\_quartetW}, $0\le M_2(g)\le\sum_i(2\lambda/\beta+g_i^2/4)$: every quantity is polynomially bounded in $g$.
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
Defining the \emph{singular fluctuation} $\nu:=\tfrac12\mathbb E[H(G)]$,
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
These are the four coefficients of Watanabe's formulas: the two-leg amplitude $\mathbb E\langle T^2\rangle=\lambda/\beta+\nu$ (generalisation), the training correction $-2\nu$ from $\mathbb E\langle T^2-GT\rangle$, and the predictive-variance correction $-\tfrac12\mathbb EV=-\nu/\beta$ distinguishing Bayes from Gibbs. In the diagrammatic reading, $\lambda/\beta$ is the contact term (no propagator), $\pm\nu$ the one-propagator amplitude, and $-\nu/\beta$ the connected two-point bubble (local tadpole minus bilocal cross-pairing).

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

\section{Relation to the stochastic theorems of the grammar library}\label{sec:grammar}

\paragraph{The leading posterior is random.} For a continuous spatial phase $\xi$ on the compact base the grammar library proves that the posterior law of the energy converges to the evidence-weighted face mixture $\int J_\lambda(\xi(v))\rho_{\xi(v)}\,d\nu(v)/M_\xi$ and that the posterior location concentrates with density $J_\lambda(\xi(v))/M_\xi$\leanrefL{Grammar/SpatialPhaseLeading.lean\#L63}{spatialPhase\_tendsto}; with $\xi=G$ the Gaussian field this is the continuum version of the ratio $\int\rho\phi S_\lambda(G_w)\,dw/\int\rho S_\lambda(G_w)\,dw$. This ratio is \emph{random} already at order $1$ and depends on the covariance structure of $G$; even though $\mathbb ES_\lambda(G_w)$ is independent of $w$ when the variance is constant on the divisor, $\mathbb E[N(G)/D(G)]\neq\mathbb EN(G)/\mathbb ED(G)$ in general. Earlier drafts asserted that the leading ratio is the population ratio and that normalisation first matters at relative order $1/n$; that is true only for a spatially constant phase, where a common fluctuation factor cancels, and is withdrawn. An observable such as $K$ itself carries a $1/n$ scale, while the limiting spatial posterior weights fluctuate at order $1$.

\paragraph{The exact annealed identity.} For likelihood ratios, $Z_n(\beta)=\int\prod_{i=1}^ne^{-\beta f(X_i,u)}\,\pi(du)$, so by independence and Tonelli
\begin{equation}\label{eq:annealed}
\mathbb E_+Z_n(\beta)=\int\big(\mathbb E\,e^{-\beta f(X,u)}\big)^n\,\pi(du)\leanrefL{Grammar/AnnealedIdentity.lean\#L72}{lintegral\_annealedZ},\qquad\text{and}\qquad \mathbb E\,Z_n(1)=\pi(W)\leanrefL{Grammar/AnnealedIdentity.lean\#L91}{lintegral\_annealedZ\_one}
\end{equation}
under the likelihood normalisation $\mathbb E e^{-f(X,u)}=1$. The typical scale $n^{-\lambda}(\log n)^{m-1}$ of $Z_n$ therefore does not describe the raw annealed evidence at $\beta=1$: the annealed/quenched distinction is a sharp identity, not a cancellation of divergent factors. For the Gaussian-limit denominator with divisor variance $2$, $\mathbb ED(G)=\Gamma(\lambda)[\beta(1-\beta)]^{-\lambda}\rho(K)$ for $0<\beta<1$ and $+\infty$ for $\beta\ge1$ (\cref{prop:Q0}). The annealed identity is formalised (in the extended nonnegative reals); the Gaussian-limit denominator formula is \cref{prop:Q0}.

\paragraph{What the expected error formulas still need.} The library's stochastic expansion gives convergence in distribution of the normalised remainders and of the canonical coefficients at the Gaussian limit\leanrefL{Grammar/SampleExpansion.lean\#L54}{sample\_stochastic\_expansion}, and the random-phase posterior theorems give convergence of the posterior laws. To pass from these to expectations of the Bayes errors one needs uniform integrability of the scaled empirical quantities and a predictive Taylor-remainder estimate; with such hypotheses the algebra of \cref{cor:quartet_algebra} assembles the four coefficients. Neither hypothesis is discharged here.

\section{Discussion}\label{sec:discussion}

\paragraph{The diagrammatic reading.} The computation of dataset-averaged quantities decomposes into resolution of singularities (which produces the vertices $S_\lambda(G_w)$ at points of the alive coordinate space, with the Weber recurrence as equation of motion) followed by Gaussian averaging with the resolved covariance as propagator. For raw quantities the pairings are local (tadpoles dressing each vertex); normalisation forces bilocal pairings between vertices at different base points, mediated by $b(w,w')$, and the linked-cluster structure appears through logarithms and self-normalised ratios rather than through geometric expansions of $1/Z$. At order $1/n$ the theory collapses to two numbers, $\lambda$ and $\nu$: $\lambda$ packages the geometry of the resolution, $\nu$ the statistics of the Gaussian field on the divisor. The analogy with a scalar field theory with one species and a generating-function vertex is genuine but limited: there are no selection rules, the combinatorics is trivial, and the complexity lives in the geometry of the resolution and in the analytic structure of $C_{\alpha\beta}(w,w')$.

\paragraph{The Weber module.} The annotation insertions of the Taylor tree raise the index of the fluctuation function by $1/2$ per insertion ($S_\lambda\to S_{\lambda+Q/2}$, the action of $b^\dagger$), but monomial insertions also shift the Mellin exponent: in one normal coordinate $n^{Q/2}\int u^{h+\gamma+kQ}e^{-\beta nu^{2k}+\beta\sqrt nu^ka}\,du$ has scale $n^{-\mu}S_{\mu+Q/2}(a)$ with $\mu=(h+\gamma+1)/(2k)$, up to deterministic factors, and logarithmic terms require the log-moment functions rather than bare $S_\mu$. The precise leaf-interface statement is the Taylor-tree theorem of the paper; the universal leaf-polynomial formula and the representation-theoretic reading of earlier drafts are recorded, with these qualifications, in \cref{app:heuristic}.

\paragraph{Relation to Watanabe.} The formulas $\mathbb E[V]=2\nu/\beta$ and $\mathbb E\langle T^2\rangle=\lambda/\beta+\nu$ are Watanabe's \cite[Chapter~6]{watanabeAlgebraicGeometryStatistical2009}; the Gaussian integration by parts is a repackaging of his partial-integration identity. What is new here is the finite-resolution formulation with explicit integrability for every $\beta>0$, its formalisation, and the separation of the exact and Gaussian-limit statements from the conditional asymptotic ones.

\paragraph{Deferred.} Multi-leaf contributions with distinct exponents; finite-$n$ non-Gaussian corrections (higher cumulants of $\xi_n$); the $O(1/n^2)$ theory; log-power cancellations across leaves; higher Ward identities from the Weber module; the compact-base continuum version of \cref{thm:quartet} and \cref{prop:interpolation} by discretisation; the diagrammatic phase-transition picture (\cref{app:phase}).

\appendix

\section{Heuristic diagrammatics (deferred)}\label{app:heuristic}

This appendix collects the diagrammatic material of earlier drafts that is not established at the level of the main text. Nothing here carries a convergence or asymptotic-order claim.

\paragraph{Isserlis pairings.} When the leaf polynomial is a product $\prod_{j=1}^Q\partial_v^{(\alpha_j)}G(0,w)\cdot S_\nu(G(0,w))$ (schematically; see the Weber-module paragraph of \cref{sec:discussion} for the index bookkeeping), its expectation can be organised by Isserlis' theorem: expand $S_\nu=\sum_ms^{(\nu)}_ma^m$ and sum over perfect pairings of the $Q+m$ Gaussian factors, each pairing contributing a jet-covariance $c$, $d_\alpha$ or $e_{\alpha\beta}$. For $Q=0$ the pairings are tadpoles and resum to the dressing $(1-\beta c/2)^{-\nu}$ of \cref{prop:Q0}; for $Q=1,2$ they reproduce \cref{prop:Q12}. For general $Q$ the enumeration is the standard one and is not needed for the main text.

\paragraph{The denominator expansion.} Writing $D=\bar D(1+\delta)$ with $\bar D=\mathbb ED$ and expanding $\log(1+\delta)$ gives, \emph{when justified},
\[
\mathbb E\log D=\log\bar D+\sum_{p\ge2}\frac{(-1)^{p+1}}p\,\mathbb E[\delta^p],
\]
in terms of \emph{moments} of $\delta$, not cumulants (e.g.\ $\mathbb E[\delta^4]=\kappa_4+3\kappa_2^2$); earlier drafts stated the sum with cumulants, which is incorrect. On the divisor model $\bar D=\infty$ for $\beta\ge1$ and $\delta$ is not defined; the covariance interpolation of \cref{sec:interpolation} is the rigorous replacement and is not term-by-term the same expansion. Likewise $1/D$ is not to be expanded as a geometric series in $\delta$ to compute posterior expectations; the ratio $N/D$ is handled by self-normalisation (\cref{thm:quartet}).

\paragraph{The marked-space representation.} With $G_w=W(h_w)$ an isonormal process on a Hilbert space $H$, $\|h_w\|^2=c$, $\langle h_w,h_{w'}\rangle=b(w,w')$, and the marked variable $\alpha=(w,y)$ with measure $\nu(d\alpha)=\rho(w)y^{\lambda-1}e^{-\beta y}\,dy\,dw$ and kernel element $V_\alpha=\sqrt y\,h_w$, the denominator is a superposition of exponential vertices,
\[
D(G)=\int e^{\beta W(V_\alpha)}\,\nu(d\alpha),
\]
which is correct in the normalisation \eqref{eq:S_defn}. This linearisation is useful and is the continuum shadow of the finite-resolution computations. The infinite-dimensional identities of earlier drafts are replaced by \cref{thm:quartet,prop:interpolation}: an isonormal $W$ is not an $H$-valued random vector, so $\langle W,\nabla\log D\rangle_H$ is not automatically meaningful; the Malliavin Hessian of $\log D_s$ carries a factor $s$, $\nabla^2_W\log D_s=\beta^2s\operatorname{Cov}_{\pi_s}(V,V)$; and the marked second moment obeys only $\operatorname{Tr}\operatorname{Cov}_\pi(V,V)\le\mathbb E_\pi\|V\|^2=c\,\mathbb E_\pi[y]$ for constant diagonal, not a factorisation. The compact-base statements are expected to follow from the finite-resolution ones by discretisation under compactness, continuity of the covariance kernel and a Gaussian random-element hypothesis on $C(K)$ (Fernique's theorem supplying the moments); this has not been carried out.

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
