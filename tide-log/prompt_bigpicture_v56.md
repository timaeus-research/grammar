# Direction consult #56 — (A) is the grammar paper formalised as far as it can be? (B) the "Averaging over the dataset" companion note: what is true, what is provable, what must move to an appendix, and a Lean programme

Same setting: Lean 4 + Mathlib `v4.33.1`, repo `timaeus-research/grammar` (420 modules, zero `sorry`/`axiom`, Headlines I–CXXV), now with `timaeus-research/hironaka` as a pinned lake dependency consumed only through axiom-clean declarations (`Q n`, Bierstone–Milman Thm 3.2 in chart form, is an explicit hypothesis). Since consult #55 the following landed: the two-sided Laplace theorem (`SublevelTheta → LaplaceTheta`), the dominant pair, exact chart transport from `PartialResolution` + normalised-indicator partition, the localisation obstruction, the hironaka adapter (`laplaceTheta_of_analyticOnNhd_nonneg_of_Q`: population Laplace exponent pair of an analytic nonnegative phase on small cubes, conditional on `Q n`), orthant reflection. An analytic-unit witness has been requested from the hironaka campaign (not yet available).

## (A) The paper's remaining non-claims
Everything in `paper_grammar.tex` §3–§4 that is a theorem about the standard form is formalised (see the Lean remarks in the mirror). The remaining non-claims are: the exact bridge from hironaka's chart form to `AdaptedStrataData` (needs analytic units + a compatible localisation: chart-exact analytic partition, or an analytic-core decomposition modulo an exponentially small remainder); Hypothesis I's complexification (torus inclusion, analytic divisibility `f(x,π_ℂ w) = w^k a(x,w)`, joint product-polydisc Cauchy estimate); the identification `N = n`; the tangential/normal split of weighted boxes (bookkeeping, Astra #55 unit 5). **Question A:** is there any remaining theorem of the paper provable NOW without the analytic-unit witness or the complexification (e.g. the analytic-core decomposition modulo exponentially small remainder as a theorem about a `ResolutionCover` with analytic charts; the `N = n` identification as a statement about the sampling model; anything about Hypothesis I with only real-analytic data)? If yes, rank ≤ 3 units. If no, say so and move on to (B).

## (B) The companion note `averaging_dataset.tex`
The user's directive: formalise this material, developing new mathematics where necessary; the tex file MAY be edited — incorrect or merely heuristic material is to be pushed into appendices and the note reshaped in consultation with you. The full note is appended below. It is a working draft: the Wick resummations, the cumulant expansion, the Malliavin sketch and the phase-transition section are heuristic; there are visible inconsistencies (e.g. two normalisations of `S_λ`: `∫ t^{2μ−1} e^{−βt²+βat} dt` implied by `s_m^{(ν)} = β^{m/2−ν}Γ(ν+m/2)/(2 m!)` and `S_λ(0) = Γ(λ)/(2β^λ)`, versus `∫ t^{λ−1} e^{−βt + βa√t} dt` in §marked_space; the bilocal integral form has `e^{−(1−β)(t+s)}(e^{βb√(ts)}−1)` where the MGF gives `e^{−β(1−β)(t+s)} e^{β²b√(ts)}` in the second normalisation; the bilocal resummation eq:bilocal_resummed and its `β < 1/p` discussion need checking).

### What grammar already has (exact interfaces)
- `fluctuation β lam a := ∫_{Ioi 0} t^{lam−1} e^{−βt + βa√t} dt` (the paper's `S_λ`, Watanabe's normalisation; `fluctuation_integrableOn`, `fluctuation_le_gaussian : S_λ(a) ≤ e^{βa²/2}(β/2)^{−λ}Γ(λ)`), ladder operators `raiseOp/lowerOp` with `raiseOp_fluctuation : b† S_λ = β^{1/2} S_{λ+1/2}`, `lowerOp_fluctuation`, `number_operator_fluctuation : b†b S_μ = (2μ−1) S_μ`, Weber form `fluctuation_weber`, derivatives `S_λ' = β S_{λ+1/2}` (FluctuationDerivative), `fluctMoment β a p ν i := ∫ t^{ν−1}(log t)^i … `.
- The constant-Gaussian fluctuation model (Headline part III, rem:pop_vs_emp): `gaussMomentJ β p x := ∫₀^∞ s^{p−1} e^{−βs²} e^{βsx} ds` (the `t = s²` normalisation; `J_p(0) = Γ(p/2)/(2β^{p/2})`), `lintegral_gaussMomentJ_eq (X ~ N(0,v)) : E₊[J_p(X)] = ∫ s^{p−1} e^{−βs²} e^{v(βs)²/2}`, `lintegral_gaussMomentJ_eq_of_lt (βv < 2) : = J_p(0)(1 − βv/2)^{−p/2}`, `lintegral_gaussMomentJ_eq_top_of_ge (2 ≤ βv) : = ∞`, `headline_gaussian_dichotomy`, `headline_gaussian_jensen_gap`. So the note's eq:Q0_expansion (Q = 0 tadpole resummation) and its threshold `βc < 2` ARE formalised, in the ENNReal-valued form, for a Gaussian scalar.
- Posterior laws at chart level (constant phase `a`): `ρ_a ∝ y^{λ−1} e^{−βy + βa√y}` as the posterior law of `NK`, Laplace transform `T(a,t) = r^{−λ}A(a/√r)/A(a)`, the moment hierarchy `M_{q+1} = ((λ+q)M_q + (a/2)M_q')/β`, `μ(a) = (λ + (a/2)ℓ'(a))/β` (ℓ = log A) — i.e. the Schwinger–Dyson identity `⟨t²⟩ = λ/β + (a/2)⟨t⟩`-type relation is available in the form `S_{λ+1} = (a/2)S_{λ+1/2} + (λ/β)S_λ` (Weber ODE, `S'' = (βa/2)S' + λβS` with `S' = βS_{λ+1/2}`); arbitrary continuous spatial phase `ξ(v)`: posterior law converges to the evidence-weighted face mixture `∫ J_λ(ξ(v)) ρ_{ξ(v)} dν(v)/M_ξ`, evidence ratio `Z[η;ξ]/Z[η;a] → M_ξ/J_λ(a)`, moments `E[Y^r g(u)] → ∫ g J_{λ+r}(ξ) dν / M_ξ`, all uniform on compact phase sets; random phase fields `Ξ` (kernel-law transfer, quenched/stable convergence); joint random next-log posterior-observable theorem; the ℓ¹ CLT for the empirical Taylor data with the Gaussian limit `G` (finite marginals `gaussianTarget` = centred Gaussian with the sample covariance of the coefficients), `sample_stochastic_expansion` (coefficients and normalised remainders converge in distribution to those at the Gaussian limit), `phaseEval`/`dataPhase_sampleDatum` (the phase of the datum IS `ξ_n(u) = n^{−1/2}∑(a(X_i,u) − E a(X,u))` in unit-box coordinates), `TorusCertificate`, `TanCertificate`.
- Mathlib (v4.33.1) Gaussian toolkit: `gaussianReal`, `mgf`/`charFun`, `multivariateGaussian μ S` on `EuclideanSpace ℝ ι` (with `covariance_eval_multivariateGaussian`, `charFun_multivariateGaussian`), `IsGaussian`, `HasGaussianLaw`, `IsGaussianProcess`, Fernique (`exists_integrable_exp_sq`, all moments), `stdGaussian E`. NOT in Mathlib: Isserlis/Wick, Gaussian integration by parts (Stein) in any dimension, Malliavin calculus, Borell–TIS.

### Candidate targets (please correct, rank, and add)
1. **Variance normalisation on the divisor** (eq:variance_normalised): if `E_q[e^{−f(X,u)}] = 1` for all `u` and `f(x,u) = u^k a(x,u)` with `a` analytic in `u` and suitable integrability, then `E[a(X,u)²] = 2 + O(u^k)` and `E[a(X,(0,w))²] = 2` on `{u^k = 0}`. Statement-level: a lemma about a family `f_u` with `E e^{−f_u} = 1`, `E f_u = K(u)`, `f_u = φ(u) a_u`, `φ(u) → 0`: `E[a²] → 2` along `φ → 0`, plus the exact identity on the divisor. Is the claimed `E[a²] = 2` on the divisor actually a theorem (Watanabe Thm 6.3?), or only `E[a²]|_{divisor} = 2·(something)`? Check the sign conventions (`f = log q − log p`, `K = E f`, `E e^{−f} = ∫ p = 1`).
2. **Wick formulas Q = 0, 1, 2** for a Gaussian vector `(Y, X_1, …, X_Q)`: `E[X_1 S_{λ+1/2}(Y)] = d (Γ(λ+1)/(2β^λ))(1−βc/2)^{−(λ+1)}`-type closed forms — derivable by Gaussian regression `X_1 = (d/c)Y + Z`, `Z ⊥ Y`, and the derivative `S' = βS_{λ+1/2}` — WITHOUT Isserlis. Is the note's eq:Q1_expansion correct in its own normalisation? Give the correct closed forms in the `fluctuation` normalisation.
3. **The bilocal two-point function** `E[S_λ(X)S_λ(Y)]` for a bivariate centred Gaussian `(X,Y)` with variances `c, c'` and covariance `b`: exact double-integral representation via the joint MGF, the `r`-series by expanding `e^{β²b√(ts)}`, the correct convergence thresholds (in the `fluctuation` normalisation the joint exponent is `−β(1−βc/2)t − β(1−βc'/2)s + β²b√(ts)`; with `c = c' = 2`, `b ≤ 2`, finiteness iff `β < 1/2`?? — please derive the exact condition, e.g. positive-definiteness of the quadratic form `(1−β)t + (1−β)s − βb√(ts)` in `(√t, √s)`: finite iff `1−β > 0` and `(1−β)² > β²b²/4`, i.e. `β(1 + |b|/2) < 1`; at `b = 2` this is `β < 1/2`, at `b = 0` it is `β < 1`). The note's `β < 1/p` for the `p`-th moment: check.
4. **The Bayes-quartet algebra at finite resolution** (the mathematically clean core): for a centred Gaussian vector `G = (G_1,…,G_m)` with covariance `b_{ij}`, `b_{ii} = c`, positive weights `ρ_i`, define `D(G) = ∑ρ_i S_λ(G_i)`, `⟨t²⟩_G = ∑ρ_i S_{λ+1}(G_i)/D`, `⟨t⟩_G = ∑ρ_i S_{λ+1/2}(G_i)/D`, `⟨Gt⟩_G = ∑ρ_i G_i S_{λ+1/2}(G_i)/D`, `V(G) = c⟨t²⟩_G − ∑_{ij} ρ_iρ_j b_{ij} S_{λ+1/2}(G_i)S_{λ+1/2}(G_j)/D²`. Then (i) `⟨t²⟩_G = λ/β + ½⟨Gt⟩_G` pointwise (Weber ODE — check the factor: with `S_{λ+1} = (a/2)S_{λ+1/2} + (λ/β)S_λ` it is exactly this); (ii) `E[⟨Gt⟩_G] = β E[V(G)]` by the finite-dimensional Gaussian integration by parts `E[G_i F(G)] = ∑_j b_{ij} E[∂_j F(G)]`, whose proof in Lean needs: Stein's identity for `gaussianReal` in one variable (IBP against the Gaussian density), product structure for independent standard coordinates, and the linear change `G = A Z`; hence (iii) `E[V] = 2ν/β` with `ν := ½E[⟨Gt⟩]`, and `E[⟨t²⟩] = λ/β + ν`. Integrability: `S_{λ+1/2}(a)/S_λ(a)` grows like `a/2` and `S_{λ+1}/S_λ` like `a²/4` as `a → +∞` (bounded for `a → −∞`), so with Gaussian tails ALL these ratios are integrable for EVERY `β > 0`, including `β = 1` — the self-normalisation phenomenon of §finiteness made rigorous in finite dimension. Is this the right first theorem? What about the continuum version (weights `ρ(w)dw`, `G_w` a Gaussian process with continuous paths on a compact base — grammar has `C(K,ℝ)` random fields and `IsGaussianProcess` exists in Mathlib): can the finite-dimensional identity be passed to the limit by discretisation (Riemann sums in `w`, dominated convergence with the Fernique bound), avoiding Malliavin calculus entirely?
5. **The covariance-interpolation identity** for `E[log D_s]` (eq:interpolation_identity) in finite dimension: `d/ds E[log D_s(G)] = (β²/2) E[Tr Cov_{π_s}(V,V)]`-type identity with `D_s = ∑ρ_i S_λ(√s G_i)`: derivable from (4)'s IBP; gives `E[log D(G)] = log D_0 + (β²/2)∫_0^1 …` rigorously in finite dimension. Worth a unit?
6. **What is FALSE or unsupported** in the note and should move to an appendix ("heuristic/deferred"): the formal cumulant expansion of `E log D` (divergent), the bilocal resummation domain, the QFT analogies (keep as discussion), the phase-transition section (heuristic), the Malliavin section (replace by the finite-dimensional theorems + a remark), the claim `E[a²] = 2` if wrong, the `β < 1/p` thresholds if wrong, the leaf-polynomial form `P_ℓ` with `S_{λ+Q/2}` (is the `+Q/2` shift right given grammar's Taylor tree — in grammar the annotation of degree `Q` in the normal variable produces `S_{λ + Q/(2k)}`-type shifts? please check against the paper's `thm:TaylorTree`: the exponent shift for a monomial `u^γ` inserted is `γ·(something)/2k`).
7. Anything connecting to grammar's existing stochastic theorems: e.g. the constant-phase Gaussian mixture `∫ρ_a Law(X)(da)` already formalised; the leading-order triviality (`E[Z_n] ∼ n^{−λ}(log n)^{r−1}(1−β)^{−λ} × population coefficient`) — is it a theorem given `clt_l1` + `headline_gaussian_dichotomy`? (Careful: `E` of the limit vs limit of `E`; the note's own caveat.)

## Ask
(A) as above. (B) A ranked, bounded (≤ 10 units) Lean programme with precise statements (in grammar's `fluctuation` normalisation), Mathlib inputs (names where you know them), traps, and non-claims; and, separately, a concrete **editing plan for `averaging_dataset.tex`**: which paragraphs/equations are wrong (with the corrected formulas), which are heuristic and go to an appendix "Heuristic diagrammatics (deferred)", what the restructured main text should contain (the finite-dimensional theorems, the variance normalisation, the Wick closed forms with correct thresholds, the Bayes-quartet algebra and its Lean remarks), and which sections to keep as discussion. Stop rule: when the units are exhausted or a unit needs Malliavin calculus / Isserlis beyond what the regression trick gives.

---
## Appendix: the full note `averaging_dataset.tex`
\documentclass[11pt]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[margin=1in]{geometry}
\usepackage{tikz}
\usetikzlibrary{decorations.pathmorphing,positioning}
\usepackage[capitalise,noabbrev]{cleveref}
\usepackage{natbib}

\newtheorem{thm}{Theorem}
\newtheorem{lem}[thm]{Lemma}
\newtheorem{defn}[thm]{Definition}
\newtheorem{cor}[thm]{Corollary}
\theoremstyle{remark}
\newtheorem{remark}[thm]{Remark}
\newtheorem{example}[thm]{Example}

\newcommand{\norm}[1]{\|#1\|}

\title{Averaging over the dataset (working draft)}
\date{}

\begin{document}
\maketitle

\section{Averaging over the dataset}\label{sec:averaging}

The Taylor tree expansion gives the partition function $Z(\beta,n;\xi_n,\eta)$ as a sum over leaves, where each leaf polynomial $P_\ell$ depends on the empirical process $\xi_n$. In the application to singular learning theory, $\xi_n$ depends on the dataset $\mathcal{D}_n = \{X_1, \ldots, X_n\}$ drawn i.i.d.\ from the true distribution $q(x)$. To obtain Watanabe's averaged quantities (expected free energy, generalization error, etc.), one takes the expectation $\mathbb{E}_{\mathcal{D}_n}[\cdot]$ of the expansion. This section describes how these expectations are computed.

\begin{remark}[Relation to existing work]
The underlying asymptotic formulas in this section (the RLCT $\lambda$, the singular fluctuation $\nu$, the Bayes quartet, and the identity $\mathbb{E}[V] = 2\nu/\beta$) are due to \citet{watanabeAlgebraicGeometryStatistical2009}, particularly Chapter~6 and the equations-of-state framework. The Gaussian integration by parts argument is a repackaging of Watanabe's partial integration identity. What is new here is the \emph{diagrammatic reorganisation}: interpreting these computations as a Gaussian field theory on the exceptional divisor, with the Taylor tree producing the vertices and the covariance kernel providing the propagators. This perspective clarifies the structure of the expansion and suggests systematic extensions to higher orders.
\end{remark}

\subsection{Overview}\label{subsec:overview}

The conceptual structure has five layers, each building on the previous one.

\paragraph{Resolution creates the stage.} Resolution of singularities replaces the singular parameter space (where the KL divergence $K(w)$ vanishes to various orders along a complicated set) with a smooth manifold where $K = u^{2k}$ has normal crossing form. The exceptional divisor $E = \{u^k = 0\}$ is the locus where the model is exactly true: the singularity has been spread out into a smooth geometric object with strata, each carrying its own rational exponent $\lambda = \sum (h_i+1)/(2k_i)$.

\paragraph{The Taylor tree produces vertices on the divisor.} The partition function integral is decomposed by iterating: at each node of the Taylor tree, the current minimising coordinates (those contributing to the leading singularity at that frame) are Taylor-expanded and integrated out. A coordinate killed at any frame is called \emph{dead}; coordinates that are never in any minimising set are \emph{alive}. At the leaf, the dead coordinates are set to zero in $\xi$, producing a fluctuation function $S_\lambda(G(0,w))$ where $w$ ranges over the alive coordinates. The alive coordinates survive as integration variables. Each leaf is thus an $S_\lambda$-vertex at a point $w$ in the alive coordinate space, with the Gaussian process $G(0,w)$ as its argument. The annotation insertions (derivatives $\partial_v^{(\alpha)} G(0,w)$ with respect to dead coordinates) provide the external legs.

\paragraph{Weber's equation is the equation of motion.} The fluctuation functions satisfy Weber's ODE, which arises because $S_\lambda$ is defined by a Gaussian integral over a half-line with a quadratic potential and a linear source. The ODE constrains the vertex algebraically. The ladder operators $b, b^\dagger$ shift $\lambda$ by half-integers: $b^\dagger S_\lambda \propto S_{\lambda+1/2}$, $b\, S_\lambda \propto S_{\lambda-1/2}$. This shift is connected to the annotation insertions as follows: each annotation contributes one factor of $\partial_v G$ multiplying the fluctuation function, increasing the annotation count $Q$ by $1$ and hence the $S$-index $\lambda + Q/2$ by $1/2$. So $b^\dagger$ implements the algebraic effect of adding an insertion, even though the insertion factor $\partial_v G$ sits outside $S$ in the leaf polynomial. The Schwinger--Dyson equation ($M_2 = \frac{a}{2}M_1 + \lambda/\beta$) is the fundamental constraint relating $S$-vertices at consecutive levels of the Weber module.

This gives the Weber module a natural role in organising the asymptotic expansion. At a given power $n^{-\mu}$, all leaves with $\lambda_\ell = \mu$ contribute. Within a single movie, the $S$-function at the leaf has index $\nu_\ell = \lambda_{\mathrm{base}} + Q/2$, where $\lambda_{\mathrm{base}}$ comes from the density of states of the dead coordinates and $Q$ counts annotation insertions. As $Q$ increases by $1$, $\nu_\ell$ increases by $1/2$: one step up the ladder. So the annotation levels $Q = 0, 1, 2, \ldots$ of a single movie trace out consecutive elements of one irreducible representation of the Weyl algebra:
\begin{itemize}
\item $Q = 0$: the vacuum $S_{\lambda_{\mathrm{base}}}$ (the bare fluctuation function, dressed only by tadpoles).
\item $Q = 1$: a one-particle state $S_{\lambda_{\mathrm{base}}+1/2}$ (one external $\partial_v G$ leg, created by $b^\dagger$).
\item $Q = 2$: a two-particle state $S_{\lambda_{\mathrm{base}}+1}$ (two external legs, created by $(b^\dagger)^2$).
\end{itemize}
At each particle number $Q$, one sums over all choices of annotation multi-indices $\alpha_j$: this is the sum over input states at fixed particle count. The Wick contraction then determines how these input states couple to the $S$-vertex and to each other.

Since the exponent $\lambda_\ell$ determines the irreducible representation (up to $\mathbb{Z}/2$, reflecting the half-integer orbit structure of the Weber module), all leaves contributing at a given power $n^{-\mu}$ belong to the same irreducible representation of the Weyl algebra.

\paragraph{Dataset averaging is a Gaussian field theory on the divisor.} The empirical process $\xi_n \to G$ converges to a Gaussian random field on the resolved manifold. Its covariance kernel $C(u,u')$ is the resolved Fisher kernel (\S\ref{subsec:resolved_covariance}): it encodes how dataset fluctuations at different points of the resolution are correlated. Taking expectations over the dataset amounts to performing Wick contractions with this kernel. We therefore have a Gaussian field theory whose ``spacetime'' is the space of alive coordinates at each leaf (parametrising the disc over which the leaf integral runs), whose ``fields'' are the values $G(0,w)$, and whose ``propagator'' is the covariance kernel $C$. For the raw partition function $\mathbb{E}[Z_n]$, each $S_\lambda$-vertex self-contracts via tadpoles: the theory is free. But normalised quantities ($\mathbb{E}[Z_n[\phi]/Z_n]$, $\mathbb{E}[\log Z_n]$) force interaction: the denominator introduces additional $S_\lambda$-vertices at independent integration points, connected to the numerator vertices by bilocal propagators $b(w,w') = C_{00}(w,w')$ (\S\ref{subsec:bilocal}, \S\ref{subsec:normalised}).

\paragraph{The Bayes quartet as leading-order amplitudes.} At order $1/n$, only three diagrammatic amplitudes contribute (\S\ref{subsec:four_formulas}, \cref{fig:bayes_quartet}): the contact term $\lambda/\beta$ (from the Schwinger--Dyson identity, purely geometric), the one-propagator amplitude $\nu$ (one external $G$-leg on a normalised vertex, where the bilocal structure first enters), and the connected two-point bubble $V$ (local tadpole minus bilocal cross-pairing, related to $\nu$ by Gaussian IBP). All four of Watanabe's asymptotic formulas are assembled from just $\lambda$ and $\nu$: the geometry of the resolution is packaged into $\lambda$, the statistics of the Gaussian field on the divisor into $\nu$.

\medskip
In summary: the computation of dataset-averaged quantities in singular learning theory decomposes into \emph{resolution of singularities} (which produces the vertices and the geometry) followed by \emph{Gaussian field theory on the exceptional divisor} (which performs the Wick contractions and selects connected diagrams), with \emph{Weber's equation as the equation of motion} constraining the vertices.

\subsection{The empirical process in resolution coordinates}

We begin by recalling how the empirical process arises in the resolved integral. After resolution of singularities, the KL divergence takes the normal crossing form $K(\pi(u)) = u^{2k}$ in local coordinates $u = (u_1,\ldots,u_d)$ on a chart of the resolved manifold $U$. The key object is the function $a(x,u)$ defined by the identity
\begin{equation}\label{eq:a_defn}
\log q(x) - \log p(x|\pi(u)) = u^k\, a(x,u)\,,
\end{equation}
where $a(x,u)$ is real analytic in $u$ and satisfies $\mathbb{E}_X[a(X,u)] = u^k$, so that taking expectations recovers $K(\pi(u)) = u^{2k}$. This is the ``standard form of the likelihood ratio function'' of \cite[Main Theorem~6.1]{watanabeAlgebraicGeometryStatistical2009}.

The \emph{empirical process} in resolution coordinates is
\begin{equation}\label{eq:xi_n_defn}
\xi_n(u) = \frac{1}{\sqrt{n}} \sum_{i=1}^n \big\{u^k - a(X_i, u)\big\}\,.
\end{equation}
By construction $\mathbb{E}[\xi_n(u)] = 0$, and the empirical KL divergence becomes
\begin{equation}\label{eq:K_n_standard}
K_n(\pi(u)) = u^{2k} - \frac{u^k}{\sqrt{n}}\,\xi_n(u)\,,
\end{equation}
so that $e^{-\beta n K_n(\pi(u))} = e^{-\beta n u^{2k} + \beta\sqrt{n}\, u^k \xi_n(u)}$, recovering the integrand of the standard integral $Z(\beta,n;\xi_n,\eta)$.

\begin{remark}[Well-definedness on the exceptional divisor]
Both $a(x,u)$ and $\xi_n(u)$ are well-defined and real analytic \emph{everywhere} on $U$, including on the exceptional divisor $U_0 = \{u : u^k = 0\}$. On the divisor, $a(x,(0,w))$ is a well-defined random variable (not identically zero), and $\xi_n(0,w) = -\frac{1}{\sqrt{n}}\sum_i a(X_i, (0,w))$. In contrast, the na\"ive empirical process $\psi_n(w) = \sqrt{n}(K_n(w) - K(w))/\sqrt{K(w)}$ in the original coordinates is ill-defined where $K(w) = 0$. Resolution of singularities replaces the singular quotient by the analytic function $a(x,u)$.
\end{remark}

\subsection{The resolved covariance kernel}\label{subsec:resolved_covariance}

By the central limit theorem \cite[Theorem~6.2]{watanabeAlgebraicGeometryStatistical2009}, $\xi_n$ converges in law to a centred Gaussian process $G$ with covariance
\begin{equation}\label{eq:resolved_covariance}
C(u,u') = \mathbb{E}[G(u)\,G(u')] = \mathbb{E}_X[a(X,u)\,a(X,u')] - u^k (u')^k\,.
\end{equation}
The second term $-u^k(u')^k$ arises because $\mathbb{E}_X[a(X,u)] = u^k$; it vanishes whenever either $u$ or $u'$ lies on the exceptional divisor (where $u^k = 0$). Since the Taylor tree evaluates $\xi$ at points of the form $(0,w)$ (with dead coordinates set to zero), the relevant covariance simplifies to
\begin{equation}\label{eq:covariance_on_divisor}
C((0,w),(0,w')) = \mathbb{E}_X[a(X,(0,w))\,a(X,(0,w'))]\,.
\end{equation}
Moreover, Watanabe shows \cite[Theorem~6.3]{watanabeAlgebraicGeometryStatistical2009} that on the divisor, the variance is normalised:
\begin{equation}\label{eq:variance_normalised}
\mathbb{E}_X[|a(X,(0,w))|^2] = C((0,w),(0,w)) = 2\,.
\end{equation}
This normalisation plays a role in determining the convergence conditions for the Wick expansions below.

At a given leaf $\ell$ of the Taylor tree, the $d$ coordinates $u = (u_1,\ldots,u_d)$ are partitioned into $r$ \emph{dead} coordinates $v = (v_1,\ldots,v_r)$ and $s = d - r$ \emph{alive} coordinates $w = (w_1,\ldots,w_s)$, so that $u = (v,w)$. A coordinate is dead if it was in the minimising set at some frame of the movie and was subsequently killed (set to zero); alive if it never entered any minimising set. The distinction between ``dead'' and ``minimising'' matters: a coordinate may be dead (killed at an earlier frame) without being minimising at the final frame. At the leaf, the restricted empirical process is $\xi^{(T)}(w) = \xi(0,\ldots,0,w)$ with all dead coordinates set to zero.

The Taylor tree produces random variables of the form $\partial_v^{(\alpha)} G(0,w)$: derivatives of $G$ with respect to dead coordinates, evaluated at $v = 0$, where $\alpha = (\alpha_1,\ldots,\alpha_r) \in \mathbb{N}^r$ is a multi-index in the dead coordinates. These are Gaussian random variables because $G$ is a centered Gaussian process and each derivative $\partial_v^{(\alpha)} G(0,w)$ is a limit of linear combinations of the Gaussian variables $G(u)$ (via difference quotients), hence Gaussian. Differentiation and expectation commute (justified by the analyticity of $a(x,\cdot)$ in $u$, which ensures the required integrability):
\[
\mathbb{E}\!\left[\partial_v^{(\alpha)} G(0,w) \cdot \partial_{v'}^{(\beta)} G(0,w')\right] = \partial_v^{(\alpha)} \partial_{v'}^{(\beta)}\, C\big((0,w),(0,w')\big)\,,
\]
where $\alpha \in \mathbb{N}^r$ and $\beta \in \mathbb{N}^{r'}$ are multi-indices in the respective dead coordinates (which may differ between leaves; see below).
This motivates the definition of the \emph{jet-covariances} on the divisor:
\begin{equation}\label{eq:jet_covariance}
C_{\alpha\beta}(w,w') := \partial_v^{(\alpha)} \partial_{v'}^{(\beta)}\, C\big((0,w),(0,w')\big)\,.
\end{equation}
The term ``jet'' reflects the fact that these are Taylor coefficients of $C$ in the dead coordinate directions, evaluated on the divisor. The multi-indices $\alpha, \beta$ range over $\mathbb{N}^r$ (or $\mathbb{N}^{r'}$ for the second leaf), so the jet-covariances involve derivatives of \emph{arbitrary order} in the dead coordinates. The collection $\{C_{\alpha\beta}(w,w')\}_{\alpha,\beta}$ encodes the full normal-jet data of the covariance kernel along the divisor. These jet-covariances are the propagators of the Wick expansion: each Isserlis pairing of $\partial_v^{(\alpha)} G(0,w)$ with $\partial_{v'}^{(\beta)} G(0,w')$ contributes a factor $C_{\alpha\beta}(w,w')$.

\paragraph{Local pairings (single leaf).} At a single leaf $\ell$ with $r$ dead and $s$ alive coordinates, all Wick contractions occur at a single value of $w \in [0,b]^s$. Three cases arise:
\begin{itemize}
\item $c(w) := C_{00}(w,w) = \mathbb{E}[G(0,w)^2] = 2$: the variance of $G$ on the divisor (constant by \eqref{eq:variance_normalised}), where $0 \in \mathbb{N}^r$ is the zero multi-index. This appears when two copies of $Y = G(0,w)$ from the fluctuation function $S_\mu(Y)$ are paired with each other (a ``tadpole'').
\item $d_\alpha(w) := C_{\alpha 0}(w,w) = \mathbb{E}[\partial_v^{(\alpha)} G(0,w) \cdot G(0,w)]$, for $\alpha \in \mathbb{N}^r$ with $|\alpha| \ge 1$: the covariance between a normal derivative and $G$ itself. This appears when an annotation insertion $\partial_v^{(\alpha_j)} G$ is paired with a factor of $G$ from the fluctuation function.
\item $e_{\alpha\beta}(w) := C_{\alpha\beta}(w,w) = \mathbb{E}[\partial_v^{(\alpha)} G(0,w) \cdot \partial_v^{(\beta)} G(0,w)]$, for $\alpha, \beta \in \mathbb{N}^r$ with $|\alpha|, |\beta| \ge 1$: the covariance between two normal derivatives. This appears when two annotation insertions are paired with each other.
\end{itemize}

\paragraph{Bilocal pairings (two leaves).} For normalised quantities (\S\ref{subsec:normalised}), the denominator expansion produces products of leaf polynomials from two (or more) leaves. If the first leaf $\ell$ has $r$ dead and $s$ alive coordinates with integration variable $w \in [0,b]^s$, and the second leaf $\ell'$ has $r'$ dead and $s'$ alive coordinates with integration variable $w' \in [0,b]^{s'}$, then the bilocal Wick contractions involve
\[
C_{\alpha\beta}(w,w') = \partial_v^{(\alpha)} \partial_{v'}^{(\beta)}\, C\big((0,w),(0,w')\big)\,, \qquad \alpha \in \mathbb{N}^r,\ \beta \in \mathbb{N}^{r'}\,.
\]
In general $r \neq r'$ and $s \neq s'$, since different leaves may arise from different paths in the Taylor tree with different adapted partitions. The simplest bilocal propagator is
\[
b(w,w') := C_{00}(w,w') = \mathbb{E}[G(0,w) \cdot G(0,w')]\,,
\]
with $0 \in \mathbb{N}^r$ and $0 \in \mathbb{N}^{r'}$ respectively.

\begin{remark}[Relation to the Fisher information]\label{rem:fisher}
Consider the simplest case: a one-dimensional regular model with true parameter $w_0$, so that $K(w) = \frac{1}{2} I(w_0)(w - w_0)^2 + O((w-w_0)^3)$ where $I(w_0) = \mathbb{E}_X[(\partial_w \log p(X|w)|_{w_0})^2]$ is the Fisher information. No resolution is needed (one dead coordinate, no alive coordinates): we set $u = \sqrt{I/2}\,(w - w_0) + O((w-w_0)^2)$ so that $K = u^2$, giving $k = 1$. From the defining identity \eqref{eq:a_defn},
\[
\log q(x) - \log p(x|w(u)) = u\, a(x,u)\,.
\]
Since $\log q - \log p$ vanishes at $u = 0$ and has derivative $\partial_w(\log q - \log p)|_{w_0} \cdot dw/du = -s(x)/\sqrt{I/2}$ where $s(x) = \partial_w \log p(x|w)|_{w_0}$ is the score, we get $\log q - \log p = -u\, s(x)/\sqrt{I/2} + O(u^2)$, and therefore
\[
a(x,u) = \frac{\log q - \log p}{u} = -\frac{s(x)}{\sqrt{I/2}} + O(u)\,.
\]
On the divisor ($u = 0$): $a(x,0) = -s(x)/\sqrt{I/2}$, and the covariance is $C(0,0) = \mathbb{E}_X[a(X,0)^2] = \mathbb{E}_X[s(X)^2]/(I/2) = 2$, confirming \eqref{eq:variance_normalised}. In several dimensions with $r$ dead coordinates $v = (v_1,\ldots,v_r)$ and $s = 0$ alive coordinates (so all coordinates are dead), the same argument gives $a(x,0) = -\sum_i s_i(x)/\sqrt{I_{ii}/2}$ (after diagonalising), and the jet-covariances $C_{\alpha\beta}(0,0)$ for $|\alpha| = |\beta| = 1$ recover the Fisher information matrix (appropriately normalised). For higher-order multi-indices $|\alpha| \ge 2$, the jet-covariances $C_{\alpha\beta}$ involve higher derivatives of $a(x,u)$ in the normal directions, which correspond to higher-order interactions between the empirical process and the singular geometry: these have no classical Fisher information analogue.
\end{remark}

\subsection{Computing expectations via Isserlis' theorem}\label{subsec:wick_expansion}

\input{wick_diagrams_figure}

At a leaf $\ell$ of a complete movie of length $T$, the leaf polynomial has the form
\[
P_\ell(w) = \rho_\ell(w) \cdot \prod_{j=1}^Q \partial_{v_{\mathrm{dead}_j}}^{(\alpha_j)} \xi(0,w) \cdot S_{\lambda + Q/2}\big(\xi(0,w)\big)\,,
\]
where $\xi(0,w) := \xi(0,\ldots,0,w)$ is the empirical process with all dead coordinates set to zero, $w$ ranges over the alive coordinates, and $\rho_\ell(w)$ is a deterministic weight (from the Jacobian, prior, and log factors accumulated along the path). The product $\prod_{j=1}^Q$ runs over the $Q$ annotation insertions: each is a derivative of $\xi$ with respect to some dead coordinate $v_{\mathrm{dead}_j}$, evaluated at the same point $(0,w)$. The multi-indices $\alpha_j$ and the specific dead coordinates appearing are determined by the movie: at each frame, the Taylor expansion in the current minimising set produces annotation derivatives with respect to those coordinates. Although the annotations arise from nested Taylor expansions at successive frames, at the leaf they are all evaluated at the common point $(0,w)$, so they reduce to partial derivatives $\partial_v^{(\alpha_j)} \xi(0,w)$ in specific dead directions. Diagrammatically, these annotation factors play the role of \emph{external insertions}: they are determined by the movie (fixed by the ``kinematics'' of the Taylor tree path) and fed into the Wick contraction, which determines how they pair with each other (via $e_{\alpha\beta}$) or with legs from the $S$-vertex (via $d_\alpha$). The $S_\lambda$-vertex is the only true interaction vertex (generating legs of all orders through its power series); the annotations are inputs to it.

When $\xi = G$ is the Gaussian limit, the expectation of this product can be computed by Isserlis' theorem: the expectation of a product of centred Gaussian random variables equals the sum over all ways of partitioning them into pairs, with each pair replaced by its covariance.

Fix a leaf $\ell$ and a point $w$. Write $Y = G(0,w)$ and $X_j = \partial_v^{(\alpha_j)} G(0,w)$ for $j = 1,\ldots,Q$. The fluctuation function contributes additional powers of $Y$ through $S_\nu(a) = \sum_{m \ge 0} s_m^{(\nu)} a^m$, where
\[
s_m^{(\nu)} = \frac{\beta^{m/2-\nu}\,\Gamma(\nu + m/2)}{2\, m!}\,.
\]
We need
\[
\mathbb{E}\!\left[\prod_{j=1}^Q X_j \cdot S_\nu(Y)\right] = \sum_{m=0}^\infty s_m^{(\nu)}\, \mathbb{E}\!\left[X_1 \cdots X_Q \cdot Y^m\right].
\]
By Isserlis' theorem, $\mathbb{E}[X_1 \cdots X_Q \cdot Y^m]$ is nonzero only when $Q + m$ is even, and equals the sum over all perfect pairings.

\paragraph{$Q = 0$ (no annotations).} Since $Y$ is centred Gaussian with variance $c = c(w) = 2$ (by \eqref{eq:variance_normalised}), only even powers $m = 2r$ contribute:
\begin{equation}\label{eq:Q0_expansion}
\mathbb{E}[S_\lambda(Y)] = \frac{\Gamma(\lambda)}{2\beta^\lambda}\sum_{r=0}^\infty \frac{(\lambda)_r}{r!}\left(\frac{\beta c}{2}\right)^r = \frac{\Gamma(\lambda)}{2\beta^\lambda}\left(1 - \frac{\beta c}{2}\right)^{-\lambda},
\end{equation}
where $(\lambda)_r = \lambda(\lambda+1)\cdots(\lambda+r-1)$ is the Pochhammer symbol. With $c = 2$ this becomes
\begin{equation}\label{eq:Q0_c2}
\mathbb{E}[S_\lambda(G(0,w))] = \frac{\Gamma(\lambda)}{2\beta^\lambda}(1 - \beta)^{-\lambda} \qquad (\beta < 1)\,.
\end{equation}
The convergence condition $\beta c < 2$ reduces to $\beta < 1$ on the divisor.

\paragraph{$Q = 1$ (one annotation).} Writing $d_v = d_{\alpha_1}(w)$:
\begin{equation}\label{eq:Q1_expansion}
\mathbb{E}\!\left[X_1 \cdot S_{\lambda+1/2}(Y)\right] = \frac{\Gamma(\lambda+1)}{2\beta^\lambda}\, d_v \left(1 - \beta\right)^{-(\lambda+1)}.
\end{equation}

\paragraph{$Q = 2$ (two annotations).} Two types of pairing: (a) both $X_1, X_2$ pair with $Y$'s (contributing $d_{\alpha_1} d_{\alpha_2}$), or (b) $X_1$ pairs with $X_2$ (contributing $e_{\alpha_1\alpha_2}$) while the $Y$'s self-pair.

\subsection{Worked example: the floor-rises leaf}\label{subsec:floor_rises_example}

We illustrate the averaging computation for the simplest complete movie: the ``floor rises'' movie of length $T = 1$ with $\gamma = 0$, $q_0 = 0$ (no annotations, $Q = 0$). Using the exponent data $d = 7$, $k_i = 1$, $h = (0,0,0,2,2,4,4)$:
\begin{itemize}
\item The minimising set is $\{1,2,3\}$ with $\lambda = 1/2$, $r = 3$.
\item The alive non-minimising coordinates are $w = (u_4, u_5, u_6, u_7)$.
\item The restricted empirical process is $\xi^{(1)}(w) = \xi(0,0,0,w)$.
\item The weight is $\eta^{(1)}(w) = \eta(0,0,0,w)$ (no $\xi$-factors since $q_0 = 0$).
\end{itemize}
The leaf polynomial (at leading log order, $j = r - 1 = 2$) involves the integral
\[
\int_{[0,b]^4} w^\mu\, \eta(0,w) \cdot S_{1/2}\big(G(0,0,0,w)\big)\, dw\,,
\]
where $\mu = h' - 2k'\lambda = (2,2,4,4) - 2(1,1,1,1)(1/2) = (1,1,3,3)$. Taking the expectation over the dataset:
\begin{align}
\mathbb{E}\!\left[\int w^\mu\, \eta(0,w) \cdot S_{1/2}(G(0,w))\, dw\right] &= \int w^\mu\, \eta(0,w) \cdot \mathbb{E}[S_{1/2}(G(0,w))]\, dw \nonumber\\
&= \int w^\mu\, \eta(0,w) \cdot \frac{\Gamma(1/2)}{2\beta^{1/2}}(1-\beta)^{-1/2}\, dw \label{eq:floor_rises_averaged}\\
&= \frac{\sqrt{\pi}}{2\sqrt{\beta(1-\beta)}} \int_{[0,b]^4} w_4 w_5 w_6^3 w_7^3\, \eta(0,0,0,w)\, dw\,. \nonumber
\end{align}
The expectation passes through the $w$-integral because the Isserlis computation is performed at fixed $w$ (the Gaussian $G(0,w)$ has variance $c(w) = 2$ independent of $w$, by \eqref{eq:variance_normalised}).

Several features are visible:
\begin{itemize}
\item The factor $(1 - \beta c/2)^{-\lambda} = (1-\beta)^{-1/2}$ diverges as $\beta \to 1^-$. This is \emph{not} an error: the Wick series $\sum_r s_{2r}(2r-1)!! c^r$ has radius of convergence $\beta c/2 = 1$, which is reached at the physical inverse temperature $\beta = 1$. Term by term, each Wick coefficient is finite at $\beta = 1$; only the closed-form resummation diverges. The divergence arises because the Gaussian limit $G$ has unbounded tails, whereas the true empirical process $\xi_n$ (a finite average) is sub-Gaussian and gives a convergent integral for every $n$. In the quantities that actually matter (ratios like $\mathbb{E}[Z_n[\phi]/Z_n]$ and $\mathbb{E}[\log Z_n]$), the divergences cancel between numerator and denominator. See \S\ref{subsec:convergence_beta} for further discussion.
\item The averaged coefficient is a \emph{deterministic} integral of $\eta$ over the non-minimising coordinates, weighted by powers of $w$. In the population case ($c = 0$), the factor $(1-\beta c/2)^{-1/2}$ is replaced by $1$ and we recover $\Gamma(1/2)/(2\beta^{1/2})$ times the integral of $w^\mu \eta$.
\item The $Q = 0$ case involves no Wick contractions beyond the self-pairings that produce the $(1 - \beta c/2)^{-\lambda}$ factor. The first genuinely new diagrams appear at $Q = 1$.
\end{itemize}

\subsection{Bilocal pairings}\label{subsec:bilocal}

The computations above are \emph{local}: all pairings occur at a single point $w$. When computing normalised expectations $\mathbb{E}[Z_n[\phi]/Z_n]$, the denominator expansion introduces products of leaf polynomials at \emph{different} points, requiring \emph{bilocal} pairings.

The simplest bilocal computation is $\mathbb{E}[S_\lambda(G_w) \cdot S_\lambda(G_{w'})]$ for two distinct points $w, w'$. Write $X = G(0,w)$, $Y = G(0,w')$, with local variances $c = c(w) = c(w') = 2$ and bilocal covariance $b = b(w,w') = C((0,w),(0,w'))$. Organising by the number $r$ of cross-pairings (pairings between an $X$-factor and a $Y$-factor):
\begin{equation}\label{eq:bilocal_resummed}
\mathbb{E}[S_\lambda(X) S_\lambda(Y)] = \frac{1}{4\beta^{2\lambda}} \sum_{r=0}^\infty \frac{\Gamma(\lambda + r/2)^2}{r!}\, (\beta b)^r \left(1 - \beta\right)^{-(\lambda+r/2)} \left(1 - \beta\right)^{-(\lambda+r/2)},
\end{equation}
using $c = c' = 2$.

\paragraph{Disconnected and connected parts.} The $r = 0$ term is the disconnected part $\mathbb{E}[S_\lambda(X)] \cdot \mathbb{E}[S_\lambda(Y)]$. The connected part (the covariance) is the sum over $r \ge 1$:
\begin{equation}\label{eq:connected_covariance}
\operatorname{Cov}(S_\lambda(G_w), S_\lambda(G_{w'})) = \frac{1}{4\beta^{2\lambda}} \sum_{r=1}^\infty \frac{\Gamma(\lambda + r/2)^2}{r!}\, (\beta b)^r (1 - \beta)^{-(2\lambda+r)}.
\end{equation}
In integral form:
\[
\operatorname{Cov}(S_\lambda(G_w), S_\lambda(G_{w'})) = \frac{1}{4\beta^{2\lambda}} \int_0^\infty\!\!\int_0^\infty t^{\lambda-1} s^{\lambda-1}\, e^{-(1-\beta)(t+s)}\, \big(e^{\beta b\sqrt{ts}} - 1\big)\, dt\, ds\,.
\]
The factor $(e^{\beta b\sqrt{ts}} - 1)$ isolates the connected contribution.

\paragraph{Simplest bilocal diagram.} The $r = 1$ term (one cross-pairing, dressed by local tadpoles) gives
\[
\frac{\Gamma(\lambda+1/2)^2}{4\beta^{2\lambda-1}}\, b(w,w') \, (1 - \beta)^{-(2\lambda+1)}.
\]
Diagrammatically: two $S_\lambda$-vertices (one at $w$, one at $w'$) connected by a single bilocal propagator $b(w,w')$, each dressed by local tadpoles. See \cref{fig:bilocal_diagrams}.

\input{bilocal_diagram_figure}

\subsection{Consequences of the Weber ODE}\label{subsec:schwinger_dyson}

The Weber ODE constrains the expectations. Define
\[
M_1(a) = \frac{S_{\lambda+1/2}(a)}{S_\lambda(a)}\,, \qquad M_2(a) = \frac{S_{\lambda+1}(a)}{S_\lambda(a)}\,.
\]
The ODE gives
\begin{equation}\label{eq:schwinger_dyson}
M_2(a) = \frac{a}{2}\, M_1(a) + \frac{\lambda}{\beta}\,.
\end{equation}
This becomes relevant for \emph{normalised} expectations, where one divides by $Z_n \propto \int \rho\, S_\lambda(G_w)\, dw$.

\subsection{Watanabe's four formulas as diagrammatic amplitudes}\label{subsec:four_formulas}

We now derive Watanabe's four asymptotic formulas as the leading amplitudes of the bilocal diagrammatic expansion. Throughout, $\mathbb{E}$ denotes expectation over the dataset $\mathcal{D}_n$, while $\langle \cdot \rangle_G$ denotes expectation with respect to the random measure
\[
\mu_G(dw\, dt) \propto \rho(w)\, t^{2\lambda-1} e^{-\beta t^2 + \beta t G_w}\, dw\, dt
\]
on the non-minimising coordinates and the radial variable $t = \sqrt{n}\, u^k$. This measure is random through its dependence on the Gaussian process $G$.

\paragraph{The four quantities.} Write $D(G) := \int \rho(w)\, S_\lambda(G_w)\, dw$ for the denominator functional. The posterior expectations of $t$ and $t^2$ are
\[
\langle t \rangle_G = \frac{\int \rho(w)\, S_{\lambda+1/2}(G_w)\, dw}{D(G)}\,, \qquad
\langle t^2 \rangle_G = \frac{\int \rho(w)\, S_{\lambda+1}(G_w)\, dw}{D(G)}\,,
\]
using the identity $\int_0^\infty t^{2\mu+1} e^{-\beta t^2 + \beta a t}\, dt = S_{\mu+1/2}(a)$ (and similarly for $t^{2\mu+2}$). Also define
\[
\langle G t \rangle_G := \frac{\int \rho(w)\, G_w\, S_{\lambda+1/2}(G_w)\, dw}{D(G)}\,.
\]
At leading order in $1/n$, the four error quantities reduce to:
\begin{align}
\mathbb{E}[G_g] &= L_0 + \frac{1}{n}\, \mathbb{E}[\langle t^2 \rangle_G] + o(n^{-1})\,, \label{eq:Gg_raw} \\
\mathbb{E}[G_t] &= L_0 + \frac{1}{n}\, \mathbb{E}[\langle t^2 - G t \rangle_G] + o(n^{-1})\,, \label{eq:Gt_raw}
\end{align}
where $G_g$ is the Gibbs generalisation error and $G_t$ is the Gibbs training error. The $-Gt$ term in the training error arises because training data points contribute $K_n(w) = t^2/n - t\xi_n(w)/n$ rather than $K(w) = t^2/n$.

\input{bayes_quartet_figure}

\paragraph{Step 1: Schwinger--Dyson reduction.} The Weber ODE $S''_\lambda = (\beta a/2) S'_\lambda + \lambda \beta S_\lambda$, combined with $S'_\lambda = \beta S_{\lambda+1/2}$ and $S''_\lambda = \beta^2 S_{\lambda+1}$, gives
\begin{equation}\label{eq:SD_Sfunctions}
S_{\lambda+1}(a) = \frac{a}{2}\, S_{\lambda+1/2}(a) + \frac{\lambda}{\beta}\, S_\lambda(a)\,.
\end{equation}
Integrating against $\rho(w)\, dw$ and dividing by $D(G)$:
\begin{equation}\label{eq:SD_posterior}
\langle t^2 \rangle_G = \frac{\lambda}{\beta} + \frac{1}{2}\, \langle G t \rangle_G\,.
\end{equation}
This is the Schwinger--Dyson identity for the posterior, depicted in \cref{fig:bayes_quartet}(a): it reduces the two-leg amplitude $\langle t^2 \rangle_G$ (two $t$-legs emerging from the $S$-vertex) to a contact term $\lambda/\beta$ (a dressed vacuum diagram) plus half the one-leg amplitude $\langle Gt \rangle_G$ (one external $G$-leg). Taking $\mathbb{E}$ and defining the \emph{singular fluctuation}
\begin{equation}\label{eq:nu_defn}
\nu(\beta) := \frac{1}{2}\, \mathbb{E}[\langle G t \rangle_G] = \frac{1}{2}\, \mathbb{E}\!\left[\frac{\int \rho(w)\, G_w\, S_{\lambda+1/2}(G_w)\, dw}{D(G)}\right],
\end{equation}
we obtain
\begin{equation}\label{eq:Et2}
\mathbb{E}[\langle t^2 \rangle_G] = \frac{\lambda}{\beta} + \nu\,.
\end{equation}
Substituting into \eqref{eq:Gg_raw}--\eqref{eq:Gt_raw} gives the Gibbs formulas:
\begin{equation}\label{eq:gibbs_formulas}
\mathbb{E}[G_g] = L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} + \nu\right) + o(n^{-1})\,, \qquad
\mathbb{E}[G_t] = L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} - \nu\right) + o(n^{-1})\,.
\end{equation}
The diagrammatic content of $\nu$ is shown in \cref{fig:bayes_quartet}(b): a single external $G$-leg attached to a dressed $S_{\lambda+1/2}$-vertex (the one-propagator amplitude), normalised by the denominator $D(G)$.

\paragraph{Step 2: Bayes vs Gibbs and the predictive variance.} The Bayes quantities involve the predictive log-likelihood $-\log \langle e^{-f_X} \rangle$ rather than the Gibbs posterior mean $\langle f_X \rangle$. Since $f_X = O(n^{-1/2})$ under the posterior, expand:
\[
-\log \langle e^{-f_X} \rangle = \langle f_X \rangle - \frac{1}{2}\bigl(\langle f_X^2 \rangle - \langle f_X \rangle^2\bigr) + O(n^{-3/2})\,.
\]
The second term is (minus one half of) the posterior predictive variance. At leading order, define
\begin{equation}\label{eq:V_defn}
V(G) := c\, \langle t^2 \rangle_G - \Big\langle b(w_1,w_2)\, t_1\, t_2 \Big\rangle_G^{\otimes 2},
\end{equation}
where
\[
\Big\langle b(w_1,w_2)\, t_1\, t_2 \Big\rangle_G^{\otimes 2} := \frac{\displaystyle\iint \rho(w_1)\, \rho(w_2)\, b(w_1,w_2)\, S_{\lambda+1/2}(G_{w_1})\, S_{\lambda+1/2}(G_{w_2})\, dw_1\, dw_2}{D(G)^2}\,.
\]
These two terms are depicted in \cref{fig:bayes_quartet}(c). The first term $c\, \langle t^2 \rangle_G$ is the \textbf{local tadpole}: the test point $X$ (green vertex) contributes $\mathbb{E}_X[a(X,w)^2] = c = 2$ (the on-divisor variance), contracted back to the same $S$-vertex. The second term is the \textbf{bilocal two-point bubble}: two $S$-vertices at independent normal coordinates $w_1, w_2$, connected through the test point by the bilocal propagator $b(w_1, w_2) = \mathbb{E}_X[a(X,w_1)\, a(X,w_2)]$. This is the same bilocal structure as the $r = 1$ diagram in \cref{fig:bilocal_diagrams}, but now the cross-pairing passes through the test point rather than through the training data.

The Bayes errors are then
\begin{equation}\label{eq:bayes_gibbs_relation}
\mathbb{E}[B_g] = \mathbb{E}[G_g] - \frac{1}{2n}\, \mathbb{E}[V] + o(n^{-1})\,, \qquad
\mathbb{E}[B_t] = \mathbb{E}[G_t] - \frac{1}{2n}\, \mathbb{E}[V] + o(n^{-1})\,.
\end{equation}

\paragraph{Step 3: Gaussian integration by parts.} To compute $\mathbb{E}[V]$, we use Gaussian integration by parts (also called Stein's lemma or the Gaussian contraction identity). For readers unfamiliar with this technique: if $Z$ is a centered Gaussian random variable with variance $\sigma^2$, then for any differentiable $F$ with $\mathbb{E}[|Z F'(Z)|] < \infty$,
\begin{equation}\label{eq:stein_scalar}
\mathbb{E}[Z\, F(Z)] = \sigma^2\, \mathbb{E}[F'(Z)]\,.
\end{equation}
This follows from integration by parts on $\int z\, F(z)\, e^{-z^2/2\sigma^2}\, dz/(\sigma\sqrt{2\pi})$, using $z\, e^{-z^2/2\sigma^2} = -\sigma^2 \frac{d}{dz} e^{-z^2/2\sigma^2}$. The identity says: to evaluate $\mathbb{E}[Z \cdot F(Z)]$, differentiate $F$ and multiply by the variance. It replaces the explicit factor of $Z$ by the effect of an infinitesimal shift in $Z$, weighted by the covariance.

For a Gaussian random field $G$ with covariance $\mathbb{E}[G_{w_1} G_{w_2}] = b(w_1, w_2)$, the functional generalisation is
\begin{equation}\label{eq:stein_functional}
\mathbb{E}[G_{w_1}\, F(G)] = \int b(w_1, w_2)\, \mathbb{E}\!\left[\frac{\delta F}{\delta G_{w_2}}\right] dw_2\,.
\end{equation}
This is the infinite-dimensional version of \eqref{eq:stein_scalar}: the factor $G_{w_1}$ is traded for a functional derivative $\delta/\delta G_{w_2}$, integrated against the covariance kernel. When $F$ depends on $G$ only through finitely many values $G_{w_1}, \ldots, G_{w_m}$, this reduces to a sum $\sum_j b(w_1, w_j)\, \mathbb{E}[\partial F/\partial G_{w_j}]$.

\paragraph{Step 4: Applying Gaussian IBP to the singular fluctuation.} We apply \eqref{eq:stein_functional} to the normalised posterior density $\mu_G(w_1) := \rho(w_1)\, S_{\lambda+1/2}(G_{w_1}) / D(G)$, computing
\[
\mathbb{E}[\langle G t \rangle_G] = \mathbb{E}\!\left[\int G_{w_1}\, \mu_G(w_1)\, dw_1\right] = \int\!\!\int b(w_1, w_2)\, \mathbb{E}\!\left[\frac{\delta \mu_G(w_1)}{\delta G_{w_2}}\right] dw_1\, dw_2\,.
\]
The functional derivative of the normalised density has two terms (quotient rule):
\begin{align}
\frac{\delta}{\delta G_{w_2}} \frac{\rho(w_1)\, S_{\lambda+1/2}(G_{w_1})}{D(G)}
&= \delta(w_1 - w_2)\, \frac{\beta\, \rho(w_1)\, S_{\lambda+1}(G_{w_1})}{D(G)} \label{eq:ibp_numerator} \\
&\quad - \frac{\beta\, \rho(w_1)\, S_{\lambda+1/2}(G_{w_1}) \cdot \rho(w_2)\, S_{\lambda+1/2}(G_{w_2})}{D(G)^2}\,. \label{eq:ibp_denominator}
\end{align}
The first term \eqref{eq:ibp_numerator} comes from differentiating the numerator: $\partial_a S_{\lambda+1/2}(a) = \beta\, S_{\lambda+1}(a)$, and $\delta G_{w_1}/\delta G_{w_2} = \delta(w_1 - w_2)$. Diagrammatically, this is the \textbf{local} contribution: the IBP probe at $w_2$ hits the same vertex at $w_1 = w_2$, producing a self-contraction (the left diagram in \cref{fig:bayes_quartet}(c)). The second term \eqref{eq:ibp_denominator} comes from differentiating the denominator $D(G) = \int \rho\, S_\lambda(G_w)\, dw$ using $\partial_a S_\lambda(a) = \beta\, S_{\lambda+1/2}(a)$. This is the \textbf{bilocal} contribution: the IBP probe at $w_2$ hits the denominator, connecting two distinct vertices at $w_1$ and $w_2$ (the right diagram in \cref{fig:bayes_quartet}(c)).

Substituting back:
\begin{align*}
\mathbb{E}[\langle G t \rangle_G]
&= \beta \int b(w_1, w_1)\, \mathbb{E}\!\left[\frac{\rho(w_1)\, S_{\lambda+1}(G_{w_1})}{D(G)}\right] dw_1 \\
&\quad - \beta \iint b(w_1, w_2)\, \mathbb{E}\!\left[\frac{\rho(w_1)\, S_{\lambda+1/2}(G_{w_1}) \cdot \rho(w_2)\, S_{\lambda+1/2}(G_{w_2})}{D(G)^2}\right] dw_1\, dw_2\,.
\end{align*}
Using $b(w,w) = c = 2$, the first integral is $\beta\, c\, \mathbb{E}[\langle t^2 \rangle_G]$ and the second is $\beta\, \mathbb{E}[\langle b_{12}\, t_1 t_2 \rangle_G^{\otimes 2}]$, so
\begin{equation}\label{eq:ibp_result}
\mathbb{E}[\langle G t \rangle_G] = \beta\, \mathbb{E}[V(G)]\,,
\end{equation}
by the definition \eqref{eq:V_defn} of $V$. Since $\mathbb{E}[\langle Gt \rangle_G] = 2\nu$,
\begin{equation}\label{eq:EV}
\mathbb{E}[V] = \frac{2\nu}{\beta}\,.
\end{equation}

\paragraph{Step 5: Assembling the four formulas.} Substituting \eqref{eq:Et2} and \eqref{eq:EV} into \eqref{eq:bayes_gibbs_relation}:
\begin{align}
\mathbb{E}[B_g] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} + \nu - \frac{\nu}{\beta}\right) + o(n^{-1}) = L_0 + \frac{1}{n}\!\left(\frac{\lambda - \nu}{\beta} + \nu\right) + o(n^{-1})\,, \label{eq:Bg} \\
\mathbb{E}[B_t] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} - \nu - \frac{\nu}{\beta}\right) + o(n^{-1}) = L_0 + \frac{1}{n}\!\left(\frac{\lambda - \nu}{\beta} - \nu\right) + o(n^{-1})\,. \label{eq:Bt}
\end{align}

\paragraph{Summary.} The four formulas are:
\begin{align}
\mathbb{E}[G_g] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} + \nu\right) + o(n^{-1})\,, \label{eq:Gg}\\
\mathbb{E}[G_t] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda}{\beta} - \nu\right) + o(n^{-1})\,, \label{eq:Gt}\\
\mathbb{E}[B_g] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda - \nu}{\beta} + \nu\right) + o(n^{-1})\,, \label{eq:Bg2}\\
\mathbb{E}[B_t] &= L_0 + \frac{1}{n}\!\left(\frac{\lambda - \nu}{\beta} - \nu\right) + o(n^{-1})\,. \label{eq:Bt2}
\end{align}
Each term has a diagrammatic interpretation, as summarised in \cref{fig:bayes_quartet}:
\begin{itemize}
\item $\lambda/\beta$: the \textbf{contact term} (\cref{fig:bayes_quartet}(a)), arising from the Schwinger--Dyson reduction \eqref{eq:SD_Sfunctions}. It is purely geometric (determined by the resolution exponents) and involves no bilocal propagators. In the Wick diagram, it corresponds to a dressed vacuum $S$-vertex with no external legs.
\item $\pm\nu$: the \textbf{one-propagator amplitude} (\cref{fig:bayes_quartet}(b)). The factor $G_w$ in the definition of $\nu$ represents a single external leg attached to an $S_{\lambda+1/2}$-vertex, normalised by $D(G)$. The sign distinguishes generalisation ($+$, the test point sees the posterior mean) from training ($-$, the training points are correlated with the posterior).
\item $-\nu/\beta$: the \textbf{connected two-point bubble} (\cref{fig:bayes_quartet}(c)), which distinguishes Bayes from Gibbs. It arises from the Gaussian IBP identity \eqref{eq:ibp_result}, whose two terms correspond to the local tadpole (the test point self-contracts at one fibre, left diagram) minus the bilocal cross-pairing (the test point connects two fibres, right diagram). This is the same bilocal structure as in \cref{fig:bilocal_diagrams}, but mediated by the test point rather than the training data.
\end{itemize}
The bottom panel of \cref{fig:bayes_quartet} shows the relationships between the four formulas: horizontal arrows subtract the one-propagator amplitude $2\nu/n$ (the generalisation--training gap), vertical arrows subtract the connected bubble $\nu/(n\beta)$ (the Gibbs--Bayes correction).

At leading order in $1/n$, the entire $O(1/n)$ theory depends on just two quantities: $\lambda$ (from the Mellin exponent $t^{2\lambda-1}$, determined by the resolution geometry) and $\nu$ (which collects all nontrivial dependence on the bilocal structure of the covariance kernel, the prior density $\rho$, and the multiplicity). All further geometric data ($\rho$, $b$, $r$) is packaged into $\nu$.

\subsection{Normalised expectations and connected pairings}\label{subsec:normalised}

The quantities of physical interest are normalised: $\mathbb{E}[Z_n[\phi]/Z_n]$ for posterior expectations, and $\mathbb{E}[-\log Z_n]$ for the free energy. We now explain why bilocal diagrams are forced on us by the denominator.

\paragraph{Raw expectations are local.} For the unnormalised partition function $Z_n = \int e^{-\beta n K_n} \varphi(w)\, dw$, the Taylor tree produces a sum of leaf contributions $P_\ell(\xi_n, w)$, each integrated over a single copy of $w$:
\[
\mathbb{E}[Z_n] = \sum_\ell n^{-\lambda_\ell} (\log n)^{r_\ell} \int_{W_\ell} \rho_\ell(w)\, \mathbb{E}[P_\ell(\xi_n, w)]\, dw + \cdots
\]
At each fixed $w$, the leaf polynomial $P_\ell$ involves products of $\partial_v^{\alpha} G(0,w)$ and $S_\mu(G(0,w))$, all evaluated at the \emph{same} point. The Wick contractions are therefore \emph{local}: only the jet-covariances $C_{\alpha\beta}(w) := C_{\alpha\beta}(w,w)$ appear, and the $w$-integration is performed after contracting. This is the setting of \S\ref{subsec:wick_expansion}.

\paragraph{Normalisation forces bilocality.} For a normalised observable $\mathbb{E}[\phi] = \mathbb{E}[Z_n[\phi]/Z_n]$, the numerator and denominator both depend on the same Gaussian process $G$. At leading order, both are dominated by the minimal leaves (those with $\lambda_\ell = \lambda$):
\[
Z_n \approx n^{-\lambda} (\log n)^{r-1} D(G)\,, \qquad D(G) := \int \rho(w)\, S_\lambda(G_w)\, dw\,,
\]
where $G_w = G(0,w)$ is the limiting Gaussian process. The ratio $Z_n[\phi]/Z_n$ involves the quotient of two functionals of the \emph{same} random field $G$, and the correlations between them are mediated by the bilocal covariance $b(w,w') = C_{00}(w,w')$.

To see why bilocal pairings arise, consider the product $Z_n[\phi] \cdot Z_n$ (which appears in computing $\mathbb{E}[Z_n[\phi]/Z_n]$ via the cumulant expansion, or in $\mathbb{E}[\log Z_n]$ via the variance). This product involves $S$-vertices at integration points $w$ (from the numerator) and $w'$ (from the denominator), both evaluated on the same Gaussian process $G$. The Wick contractions therefore pair factors of $G$ from \emph{different leaf integrals}: each cross-contraction between $G_{w}$ and $G_{w'}$ contributes a factor $b(w, w') = C_{00}(w, w')$. These are the bilocal pairings of \S\ref{subsec:bilocal}. When annotation insertions $\partial_v^\alpha G$ are present, the bilocal jet-covariance $C_{\alpha\beta}(w, w')$ appears instead.

The source of correlation is the \emph{shared dataset}: the empirical process $\xi_n$ (and its Gaussian limit $G$) is the same random object in every leaf integral. At fixed $(w, w')$, the pair $(G_w, G_{w'})$ is a bivariate Gaussian whose covariance $b(w,w')$ measures how much the dataset fluctuation at one normal fibre correlates with the fluctuation at another.

\paragraph{Free energy and connected diagrams.} The expected free energy $\mathbb{E}[F_n] = -\mathbb{E}[\log Z_n]$ has a direct decomposition. Writing $Z_n \approx n^{-\lambda}(\log n)^{r-1} D(G)$ at leading order:
\[
-\mathbb{E}[\log Z_n] = \lambda \log n - (r-1)\log\log n - \mathbb{E}[\log D(G)] + \cdots
\]
The first two terms are deterministic (independent of the dataset). The dataset dependence is entirely in $\mathbb{E}[\log D(G)]$, where $D(G) = \int \rho(w) S_\lambda(G_w)\, dw$ is a positive functional of the Gaussian process.

To compute $\mathbb{E}[\log D(G)]$, one uses the cumulant expansion. Write $D(G) = \bar{D}(1 + \delta)$ where $\bar{D} = \mathbb{E}[D(G)]$. Then formally
\[
\mathbb{E}[\log D(G)] = \log \bar{D} - \frac{1}{2}\operatorname{Var}(\delta) + \frac{1}{3}\mathbb{E}[\delta^3] - \cdots = \log \bar{D} + \sum_{p=2}^{\infty} \frac{(-1)^{p}}{p}\, \kappa_p\,,
\]
where $\kappa_p$ are the cumulants of $\delta = (D - \bar{D})/\bar{D}$. The linked-cluster theorem identifies each cumulant $\kappa_p$ with a sum over \emph{connected} Wick diagrams involving $p$ copies of $S_\lambda$-vertices: those in which every pair of vertices is linked by a chain of bilocal propagators (\cref{fig:bilocal_diagrams}). The disconnected diagrams cancel between the cumulant terms.

\begin{remark}[Convergence caveat]
The cumulant expansion $\mathbb{E}[\log D] = \log \bar{D} + \sum \kappa_p/p$ is formal: convergence requires control of the tails of $D(G)$, particularly the probability that $D(G)$ is close to zero. For finite $n$, $Z_n > 0$ always and $\log Z_n$ is well-defined. In the Gaussian limit, $D(G)$ is a.s.\ positive (being an integral of $S_\lambda(G_w) > 0$), but the cumulants $\kappa_p$ may not decay fast enough for the series to converge. Watanabe's rigorous proofs of the free energy expansion \citep{watanabeAlgebraicGeometryStatistical2009} do not use this cumulant expansion; they work directly with $\log Z_n$ using different techniques. The cumulant expansion should be understood as identifying which diagrammatic contributions appear at each order, not as a convergent series.
\end{remark}

At leading order, $\log \bar{D} = \log\!\big(\frac{\Gamma(\lambda)}{2\beta^\lambda}(1-\beta)^{-\lambda} \int \rho\, dw\big)$ is the population value, independent of the dataset. The first correction is $-\frac{1}{2}\kappa_2 = -\frac{1}{2}\operatorname{Var}(D)/\bar{D}^2$, which involves the bilocal two-point function $\operatorname{Cov}(S_\lambda(G_w), S_\lambda(G_{w'}))$ integrated over $w$ and $w'$. This is the connected two-point bubble of \cref{fig:bilocal_diagrams}. Higher cumulants involve higher-point connected correlators of $S_\lambda(G_w)$, each built from more bilocal propagators.

\paragraph{Reduction to $\lambda$ and $\nu$.} As derived in \S\ref{subsec:four_formulas}, the Schwinger--Dyson equation and Gaussian integration by parts together collapse all connected amplitudes at order $1/n$ to two quantities: the contact term $\lambda/\beta$ and the singular fluctuation $\nu$. The connected two-point bubble (which distinguishes Bayes from Gibbs) is itself determined by $\nu$ via the Gaussian IBP identity $\mathbb{E}[V] = 2\nu/\beta$.

\subsection{Worked example: bilocal floor-rises diagram}\label{subsec:bilocal_floor_rises}

We illustrate the bilocal mechanism using two copies of the floor-rises leaf from \S\ref{subsec:floor_rises_example}. Suppose the numerator $Z_n[\phi]$ and denominator $Z_n$ are both dominated by the same leaf type (the floor-rises leaf with $\lambda = 1/2$, non-minimising coordinates $w = (u_4, u_5, u_6, u_7)$). At leading order,
\[
Z_n \approx n^{-1/2} (\log n)^{r-1} \int_{[0,b]^4} \rho(w)\, S_{1/2}(G_w)\, dw\,,
\]
and the ratio involves
\[
\frac{Z_n[\phi]}{Z_n} \approx \frac{\int \rho(w)\, \phi(w)\, S_{1/2}(G_w)\, dw}{\int \rho(w')\, S_{1/2}(G_{w'})\, dw'}\,.
\]
Expanding via $1/Z_n = \bar{Z}_n^{-1}(1 - \delta + \delta^2 - \cdots)$ and taking the dataset expectation, the first nontrivial term involves a double integral
\[
\iint_{[0,b]^4 \times [0,b]^4} \rho(w)\, \phi(w)\, \rho(w')\, \mathbb{E}\!\left[S_{1/2}(G_w)\, S_{1/2}(G_{w'})\right] dw\, dw'\,.
\]
Here $w$ and $w'$ are \emph{independent} copies of the normal coordinates $(u_4, u_5, u_6, u_7)$. The expectation is the bilocal two-point function computed in \S\ref{subsec:bilocal}. Decomposing into disconnected and connected parts:
\begin{align*}
\mathbb{E}[S_{1/2}(G_w)\, S_{1/2}(G_{w'})] &= \mathbb{E}[S_{1/2}(G_w)] \cdot \mathbb{E}[S_{1/2}(G_{w'})] + \operatorname{Cov}(S_{1/2}(G_w), S_{1/2}(G_{w'})).
\end{align*}
The disconnected part factors through the $w$- and $w'$-integrals independently and cancels in the cumulant expansion. The connected part, from \eqref{eq:connected_covariance} with $\lambda = 1/2$, is
\[
\operatorname{Cov}(S_{1/2}(G_w), S_{1/2}(G_{w'})) = \frac{1}{4\beta} \sum_{r=1}^\infty \frac{\Gamma(1/2 + r/2)^2}{r!}\, (\beta b)^r\, (1-\beta)^{-(1+r)}\,,
\]
where $b = b(w,w') = C_{00}(w,w')$ is the bilocal covariance of the empirical process at the two normal fibres. The $r = 1$ term is
\[
\frac{\pi}{4}\, b(w,w')\, (1-\beta)^{-2}\,,
\]
using $\Gamma(1)^2 = 1$ and $c = c' = 2$. This is the simplest bilocal diagram: two $S_{1/2}$-vertices (one from the numerator leaf at $w$, one from the denominator leaf at $w'$), each dressed by local tadpoles, connected by a single propagator $b(w,w')$. The amplitude is then integrated over $w$ and $w'$ against the leaf weights $\rho(w)\phi(w)$ and $\rho(w')$.

The bilocal covariance $b(w,w')$ encodes how the dataset noise at normal fibre $w$ correlates with the noise at normal fibre $w'$. When $w = w'$, $b = c = 2$ and we recover the local variance. As $w$ and $w'$ separate, $b$ decays: data points that produce large fluctuations in $G$ at one value of the non-minimising coordinates need not produce large fluctuations at another.

\subsection{Convergence of the Wick resummation}\label{subsec:convergence_beta}

The closed-form resummations throughout this section require careful attention to convergence. The situation is more delicate than it may first appear: different moments of $S_\lambda(G_w)$ have different convergence thresholds in $\beta$.

\paragraph{One-point function.} The expectation $\mathbb{E}[S_\lambda(G_w)]$ involves the integral
\[
\int_0^\infty t^{2\lambda-1}\, e^{-\beta t^2(1 - \beta c/2)}\, dt\,,
\]
obtained by computing the moment generating function $\mathbb{E}[e^{\beta t G_w}] = e^{\beta^2 c t^2/2}$. With $c = 2$, this converges when $\beta < 1$ and diverges at $\beta = 1$: the Gaussian enhancement exactly cancels the quadratic damping.

\paragraph{Higher moments and the $\beta < 1/p$ threshold.} The $p$-th moment $\mathbb{E}[S_\lambda(G_w)^p]$ has a \emph{stricter} convergence threshold. Using the integral representation with $p$ copies of $S_\lambda$ at the same point ($c = b = 2$), the exponent evaluated at $t_1 = \cdots = t_p = t$ is $tp(\beta p - 1)$. This diverges when $\beta p > 1$, giving the threshold
\[
\beta < \frac{1}{p}\,.
\]
In particular:
\begin{itemize}
\item $p = 1$: $\beta < 1$ (one-point function).
\item $p = 2$: $\beta < 1/2$ (second moment, relevant to the bilocal two-point function at $w = w'$).
\item $p = 3$: $\beta < 1/3$.
\end{itemize}
So the bilocal resummation \eqref{eq:bilocal_resummed} is not valid on the full range $\beta < 1$: at $w = w'$ (the worst case), it diverges at $\beta = 1/2$. For distinct $w \neq w'$ with $b(w,w') < c = 2$, the threshold is less severe but still stricter than $\beta < 1$.

\paragraph{Implications.} These convergence thresholds do not signal a pathology in the finite-$n$ objects:
\begin{enumerate}
\item For each finite $n$, the partition function $Z_n$ and all its moments are finite (the empirical process $\xi_n$ has bounded moment generating function under appropriate integrability assumptions on $a(x,u)$).
\item The divergence is an artefact of replacing $\xi_n$ by its Gaussian limit $G$ (which has unbounded tails) and resumming the entire Wick series.
\item The Wick expansion \emph{term by term} is well-defined at any $\beta$: each coefficient $s_{2r}(2r-1)!! c^r$ is finite for each $r$.
\end{enumerate}
The physically meaningful quantities are \emph{ratios}: posterior expectations $\mathbb{E}[Z_n[\phi]/Z_n]$ and the free energy $\mathbb{E}[\log Z_n]$. In these, the divergent factors from numerator and denominator may cancel. For instance, the singular fluctuation $\nu$ involves the ratio $S_{\lambda+1/2}/S_\lambda$, in which the tadpole dressing cancels to leading order. However, justifying this cancellation rigorously (particularly showing that the Gaussian limit can be exchanged with the nonlinear functional $\int S_{\lambda+1/2} / \int S_\lambda$) requires control beyond the bare CLT, including uniform integrability and control of the denominator $D(G)^{-1}$. Watanabe's proofs in \citep{watanabeAlgebraicGeometryStatistical2009} provide this control, but the arguments are not purely diagrammatic.

In practice, one either works with the formal Wick series at $\beta = 1$ (without resumming), or derives algebraic identities at general $\beta$ (treating the resummations as formal) and verifies that the ratios have finite limits as $\beta \to 1^-$. Watanabe's four formulas (\S\ref{subsec:four_formulas}) are valid at $\beta = 1$ because they express ratios, not individual resummed expectations. The next section describes a more systematic approach to making the diagrammatic expansion rigorous without requiring individual moments to be finite.

\subsection{Towards rigorous diagrammatics}\label{subsec:rigorous}

The formal diagrammatic expansion of \S\ref{subsec:normalised}--\S\ref{subsec:four_formulas} relies on expanding $1/Z_n$ as a geometric series in $\delta = (Z_n - \bar{Z}_n)/\bar{Z}_n$, which does not converge in general. We now sketch how the connected-diagram structure can be recovered rigorously, using techniques from Malliavin calculus and covariance interpolation. The key ideas are: (i)~rewrite the $S_\lambda$-vertex as a superposition of exponential Gaussian vertices on an enlarged (marked) space, (ii)~use Gaussian integration by parts (Malliavin derivatives) instead of geometric series to handle ratios, and (iii)~use covariance interpolation to compute $\mathbb{E}[\log D(G)]$ without a cumulant expansion.

\subsubsection{The marked-space representation}\label{subsec:marked_space}

The starting point is to ``linearise'' the fluctuation function. Recall that $S_\lambda(a) = \int_0^\infty t^{\lambda-1} e^{-\beta t + \beta a\sqrt{t}}\, dt$. Realise the Gaussian process $G$ as an isonormal process on a Hilbert space $H$: write $G_w = W(h_w)$ where $W$ is a white noise on $H$ and $h_w \in H$ satisfies $\|h_w\|_H^2 = \mathbb{E}[G_w^2] = 2$. The covariance is $\langle h_w, h_{w'}\rangle_H = C_{00}(w,w') = b(w,w')$.

Now introduce the \emph{marked variable} $\alpha = (w, t) \in [0,b]^s \times (0,\infty)$ with measure
\begin{equation}\label{eq:marked_measure}
\nu(d\alpha) = \rho(w)\, t^{\lambda-1} e^{-\beta t}\, dt\, dw
\end{equation}
and define the \emph{marked kernel element} $V_\alpha = \sqrt{t}\, h_w \in H$. Then the denominator functional becomes
\begin{equation}\label{eq:D_marked}
D(G) = \int \rho(w)\, S_\lambda(G_w)\, dw = \int e^{\beta\, W(V_\alpha)}\, \nu(d\alpha)\,.
\end{equation}
This is the crucial rewriting: the $S_\lambda$-vertex, which was a complicated nonlinear functional of $G_w$, becomes a \emph{superposition of exponential Gaussian vertices} $e^{\beta W(V_\alpha)}$ on the enlarged space parametrised by $\alpha = (w,t)$. The extra variable $t$ (from the integral defining $S_\lambda$) plays the role of a ``radial'' or ``energy'' variable that linearises the vertex. Each exponential $e^{\beta W(V_\alpha)}$ is a standard object in Gaussian analysis: its moments are controlled by $\|V_\alpha\|_H^2 = 2t$, which diverges as $t \to \infty$ but is tamed by the decay $e^{-\beta t}$ in the measure $\nu$.

The marked-space representation converts the problem from ``nonlinear functionals of a Gaussian process'' (the $S_\lambda$ framework) to ``linear exponentials of a Gaussian process on an enlarged space'' (the $e^{\beta W(V_\alpha)}$ framework). The latter is the natural setting for Malliavin calculus and cluster expansion techniques.

\subsubsection{Ratios via Gaussian integration by parts}\label{subsec:ratio_ibp}

With the marked-space representation, the ratio $N(G)/D(G)$ (where $N$ is the numerator of $\nu$, say $N = \int \rho\, G_w S_{\lambda+1/2}(G_w)\, dw$) can be handled by the Malliavin derivative. The key identity is:

Since $\partial_a S_\lambda(a) = \beta S_{\lambda+1/2}(a)$, the Malliavin derivative of $D$ in the direction $h_w$ is
\[
\langle \nabla D, h_w \rangle_H = \beta \int \rho(w')\, \langle h_w, \sqrt{t}\, h_{w'}\rangle_H\, e^{\beta W(V_{w',t})}\, \nu(dw'\, dt) = \beta N_w(G)\,,
\]
where $N_w$ involves the propagator $b(w,w')$. More generally, the full Malliavin gradient is
\[
\nabla D(W) = \beta \int V_\alpha\, e^{\beta W(V_\alpha)}\, \nu(d\alpha)\,.
\]
Therefore the ratio $N/D$ can be written as a \emph{logarithmic Malliavin derivative}:
\begin{equation}\label{eq:ratio_malliavin}
\frac{N(W)}{D(W)} = \frac{1}{\beta}\, \langle W, \nabla \log D(W) \rangle_H\,.
\end{equation}
This is exact and does not require expanding $1/D$ as a power series. Applying the Gaussian integration by parts formula $\mathbb{E}[W(h) F(W)] = \mathbb{E}[\langle h, \nabla F(W)\rangle_H]$ (the infinite-dimensional Stein lemma):
\begin{equation}\label{eq:ratio_ibp_exact}
\mathbb{E}\!\left[\frac{N}{D}\right] = \frac{1}{\beta}\, \mathbb{E}\!\left[\operatorname{Tr}(\nabla^2 \log D)\right] = \beta\, \mathbb{E}\!\left[\operatorname{Tr}\operatorname{Cov}_{\pi^W}(V, V)\right],
\end{equation}
where $\pi^W(d\alpha) = e^{\beta W(V_\alpha)} \nu(d\alpha) / D(W)$ is the \emph{random Gibbs measure} on the marked space and $\operatorname{Cov}_{\pi^W}(V,V)$ is the covariance of $V_\alpha$ under $\pi^W$. The second equality uses
\[
\nabla^2 \log D = \beta^2\!\left(\frac{\int V_\alpha V_\alpha^\top e^{\beta W(V_\alpha)}\nu(d\alpha)}{D} - \frac{\int V_\alpha e^{\beta W(V_\alpha)}\nu(d\alpha)}{D} \cdot \frac{\int V_\alpha^\top e^{\beta W(V_\alpha)}\nu(d\alpha)}{D}\right) = \beta^2 \operatorname{Cov}_{\pi^W}(V,V)\,.
\]

The identity \eqref{eq:ratio_ibp_exact} is the rigorous version of the singular fluctuation computation from \S\ref{subsec:four_formulas}. The object $\operatorname{Tr}\operatorname{Cov}_{\pi^W}(V,V)$ is the \emph{connected two-point function under the random Gibbs measure}: it is a single connected diagram (a bilocal propagator $b(w,w')$ weighted by the Gibbs measure $\pi^W$), and it is well-defined and finite under mild conditions on $G$ and $\rho$, even at $\beta = 1$ where individual moments $\mathbb{E}[S_\lambda(G_w)^p]$ diverge. The self-normalisation by $D(W)$ in the Gibbs measure $\pi^W$ is what makes the ratio finite: it is not a cancellation between divergent numerator and denominator, but a single well-defined object from the start.

\subsubsection{The covariance interpolation identity for the free energy}\label{subsec:covariance_interpolation}

For the expected free energy $\mathbb{E}[\log D(G)]$, the cumulant expansion $\log\bar{D} + \sum \kappa_p$ is formal and potentially divergent. The covariance interpolation method provides a rigorous alternative that still exhibits the connected-diagram structure.

Define the interpolated denominator
\begin{equation}\label{eq:interpolated_D}
D_s(W) := \int e^{\beta\sqrt{s}\, W(V_\alpha)}\, \nu(d\alpha)\,, \qquad s \in [0,1]\,,
\end{equation}
so that $D_0 = \nu([0,b]^s \times (0,\infty)) = \int \rho(w) S_\lambda(0)\, dw$ is a deterministic constant (the population value) and $D_1 = D(G)$. Write $\pi_s^W(d\alpha) = e^{\beta\sqrt{s}\, W(V_\alpha)} \nu(d\alpha) / D_s(W)$ for the interpolated Gibbs measure. A direct computation using Gaussian integration by parts gives
\begin{equation}\label{eq:interpolation_derivative}
\frac{d}{ds}\, \mathbb{E}[\log D_s] = \frac{\beta^2}{2}\, \mathbb{E}\!\left[\operatorname{Tr}\operatorname{Cov}_{\pi_s^W}(V, V)\right].
\end{equation}
To see this: $\frac{d}{ds} \log D_s = \frac{\beta}{2\sqrt{s}} \frac{\int W(V_\alpha) e^{\beta\sqrt{s} W(V_\alpha)} \nu(d\alpha)}{D_s}$, which after taking $\mathbb{E}$ and applying the IBP formula $\mathbb{E}[W(h) F] = \mathbb{E}[\langle h, \nabla F\rangle_H]$ to the numerator, yields the Hessian of $\log D_s$ contracted against the covariance kernel, which is $\beta^2 \operatorname{Cov}_{\pi_s}(V,V)$. Integrating \eqref{eq:interpolation_derivative} from $s = 0$ to $s = 1$:
\begin{equation}\label{eq:interpolation_identity}
\boxed{\mathbb{E}[\log D(G)] = \log D_0 + \frac{\beta^2}{2} \int_0^1 \mathbb{E}\!\left[\operatorname{Tr}\operatorname{Cov}_{\pi_s^W}(V,V)\right] ds\,.}
\end{equation}
This is exact and rigorous (assuming the integrand is integrable on $[0,1]$, which holds under mild conditions). The first term $\log D_0$ is the population free energy. The integral is the connected correction: at each interpolation parameter $s$, the integrand $\operatorname{Tr}\operatorname{Cov}_{\pi_s}(V,V)$ is a connected two-point function under the $s$-tilted Gibbs measure, and the integral ``turns on'' the Gaussian field from $s = 0$ (no field) to $s = 1$ (full field). Higher derivatives of \eqref{eq:interpolation_derivative} in $s$ produce higher connected cumulants, giving a systematic hierarchy of connected diagrams without a formal power series.

\begin{remark}[Comparison with the formal cumulant expansion]
The formal cumulant expansion $\mathbb{E}[\log D] = \log\bar{D} - \frac{1}{2}\kappa_2 + \frac{1}{3}\kappa_3 - \cdots$ corresponds to Taylor-expanding the integrand in \eqref{eq:interpolation_identity} around $s = 0$ and integrating term by term. The $p$-th order term reproduces the $p$-th cumulant. But the interpolation formula does not require this Taylor expansion to converge: the integral over $s$ is well-defined even when the individual cumulants $\kappa_p$ are infinite (which happens when $\beta$ exceeds the convergence threshold $1/p$). The interpolation ``resums'' the divergent cumulant series into a finite quantity.
\end{remark}

\begin{remark}[Source derivatives and the linked-cluster theorem]
The linked-cluster theorem (connected diagrams give the free energy) can also be obtained rigorously via source derivatives. Introduce a source $J$ and define
\[
D_J(W) = \int e^{J\, O(\alpha) + \beta W(V_\alpha)}\, \nu(d\alpha)\,.
\]
Then $\partial_J^k \log D_J(W)|_{J=0}$ is the $k$-th connected cumulant of $O$ under the random Gibbs measure $\pi^W$. This is a pathwise identity (no expectation over $W$ needed) and is the exact analogue of the linked-cluster theorem in statistical mechanics: connected objects are derivatives of a logarithm, not terms in a geometric series for $1/Z$. Taking $\mathbb{E}_W$ and applying Gaussian IBP to each derivative produces the averaged connected diagrams of \S\ref{subsec:normalised}.
\end{remark}

\subsubsection{Finiteness at $\beta = 1$}\label{subsec:finiteness}

The identity \eqref{eq:ratio_ibp_exact} expresses $\mathbb{E}[N/D]$ as the expectation of a \emph{self-normalised} quantity ($\operatorname{Cov}_{\pi^W}$), which can be finite even when individual moments of $S_\lambda(G_w)$ diverge. This is a self-normalisation phenomenon: the Gibbs measure $\pi^W$ divides by $D(W)$, so extreme values of $S_\lambda(G_w)$ (which cause the raw moments to diverge) are simultaneously in both the numerator and denominator and cancel in the ratio.

To make this rigorous at $\beta = 1$, one needs:
\begin{enumerate}
\item \textbf{Lower-tail control on $D(G)$}: show that $D(G)$ is bounded away from zero with sufficient integrability. Since $S_\lambda(a) > 0$ for all $a$ and $\rho(w)$ is a positive density on a set of positive measure, $D(G) > 0$ a.s. For integrability of $D(G)^{-q}$ (negative moments), one can use the bound $D(G) \ge \rho_{\min} \int_K S_\lambda(G_w)\, dw \ge \rho_{\min}\, e^{c \inf_{w \in K} G_w}$ for a compact $K$ with $\rho(K) > 0$, combined with Gaussian sup-tail estimates (Borell--TIS inequality) to control $\inf_K G_w$.
\item \textbf{Integrability of the Gibbs covariance}: show that $\mathbb{E}[\operatorname{Tr}\operatorname{Cov}_{\pi^W}(V,V)]$ is finite. Since $\operatorname{Cov}_{\pi^W}(V,V) \le \mathbb{E}_{\pi^W}[V V^\top] = \mathbb{E}_{\pi^W}[t]\, \mathbb{E}_{\pi^W}[h_w h_{w'}^\top]$ (by Cauchy--Schwarz on the marked space), this reduces to controlling the first moment of $t$ under $\pi^W$, which is a ratio of fluctuation functions.
\item \textbf{Regularity of the interpolation}: show that $s \mapsto \mathbb{E}[\operatorname{Tr}\operatorname{Cov}_{\pi_s}(V,V)]$ is integrable on $[0,1]$ for the free energy identity \eqref{eq:interpolation_identity}. At $s = 0$, the Gibbs measure is deterministic and the covariance is explicit; the potential singularity is at $s = 1$ (full field strength).
\end{enumerate}
These conditions are expected to hold under the standard SLT hypotheses (compact parameter space, analytic prior and model, realizable case), but verifying them in detail is deferred to future work. The point is that the Malliavin/interpolation framework provides a \emph{pathway} to rigorous diagrammatics at $\beta = 1$, whereas the naive geometric series / cumulant expansion approach does not.

\subsection{Leading-order triviality and where the diagrams matter}\label{subsec:leading_order}

At the leading power $n^{-\lambda}$ in the asymptotic expansion of $Z_n$, the Feynman calculus is trivial. Only the $Q = 0$ leaves (the vacuum level of the Weber module) contribute, because any annotation ($Q \ge 1$) shifts the exponent $\lambda_\ell$ upward (the extra power of $v$ from the Taylor expansion increases the Mellin exponent). At the vacuum level, the only Wick contractions are tadpoles (self-pairings of $G_w$ within the $S_\lambda$ power series), which produce the universal dressing factor $(1 - \beta c/2)^{-\lambda} = (1-\beta)^{-\lambda}$. Since $c = 2$ is constant on the divisor, this factor is independent of $w$ and pulls out of the $w$-integral:
\[
\mathbb{E}[Z_n] \sim n^{-\lambda}(\log n)^{r-1} \cdot (1-\beta)^{-\lambda} \cdot \frac{\Gamma(\lambda)}{2\beta^\lambda} \cdot \int \rho(w)\, dw\,.
\]
The $w$-integral $\int \rho(w)\, dw$ is exactly the population ($\xi = 0$) coefficient. So at leading order, dataset averaging multiplies the population coefficient by a universal constant: no bilocal diagrams, no connected amplitudes, nothing depending on the covariance kernel $C$.

\paragraph{The ratio $Z_n[\phi]/Z_n$ at leading order.} When forming the posterior expectation $\mathbb{E}_n[\phi] = Z_n[\phi]/Z_n$, both numerator and denominator have the same leading power $n^{-\lambda}(\log n)^{r-1}$, so the ratio is $O(1)$. The tadpole dressing $(1-\beta)^{-\lambda}$ cancels between numerator and denominator, and the leading term is simply the ratio of population coefficients: a purely geometric quantity depending on the resolution data $(h, k)$, the prior density $\rho$, and the observable $\phi$, but not on the dataset.

\paragraph{First nontrivial contribution at $O(1/n)$.} The Feynman calculus becomes genuinely nontrivial at $O(1/n)$. Write $Z_n = \bar{Z}_n(1 + \delta)$ where $\bar{Z}_n = \mathbb{E}[Z_n]$ and $\delta$ is the relative fluctuation. Expanding $1/Z_n = \bar{Z}_n^{-1}(1 - \delta + \delta^2 - \cdots)$, the first correction to the ratio $Z_n[\phi]/Z_n$ involves the covariance between the numerator and denominator fluctuations:
\[
\frac{Z_n[\phi]}{Z_n} = \frac{\bar{Z}_n[\phi]}{\bar{Z}_n}\Big(1 - \operatorname{Cov}\!\left(\frac{Z_n[\phi]}{\bar{Z}_n[\phi]}, \delta\right) + \cdots\Big).
\]
This covariance is the first bilocal diagram: it connects an $S$-vertex from the numerator (at $w$) to an $S$-vertex from the denominator (at $w'$) via the propagator $b(w,w') = C_{00}(w,w')$. The singular fluctuation $\nu$ is the amplitude of this diagram. The contact term $\lambda/\beta$ enters separately through the Schwinger--Dyson identity.

\paragraph{Where each order lives in the Weber module.} This hierarchy has a clean representation-theoretic interpretation:
\begin{itemize}
\item \textbf{Leading order} ($n^{-\lambda}$): only the vacuum $Q = 0$ contributes. The leading coefficient is the population quantity, independent of the dataset. The Feynman calculus is trivial (free theory, tadpoles only).
\item \textbf{$O(1/n)$ correction}: the denominator expansion introduces bilocal diagrams. Still at the vacuum level ($Q = 0$), but the normalisation creates interaction between $S$-vertices at different integration points. This is where $\nu$ appears.
\item \textbf{Subleading powers} ($n^{-\mu}$ with $\mu > \lambda$): the $Q \ge 1$ leaves (excited states in the Weber module) contribute. These bring annotation derivatives $\partial_v G$ as external legs, requiring the full Wick machinery with jet-covariances $C_{\alpha\beta}$.
\end{itemize}
So the Feynman calculus is a machine for computing corrections to the population ratio. The leading order is free; the interactions enter through the denominator expansion at $O(1/n)$ and through the excited states of the Weber module at subleading powers of $n$.

\section{Discussion}\label{sec:discussion}

\subsection{The Bayes quartet as a scattering amplitude}\label{subsec:scattering}

We have described the Bayes quartet as ``leading-order scattering amplitudes.'' This analogy deserves elaboration.

In quantum field theory, one computes transition amplitudes between asymptotic states (the S-matrix) by summing over Feynman diagrams: vertices contribute local factors from the Lagrangian, propagators connect them, and connected diagrams give physical scattering amplitudes. The result is organised by loop order (powers of $\hbar$), with tree-level diagrams giving the classical limit and loops giving quantum corrections.

The structure here is remarkably parallel:
\begin{itemize}
\item The \textbf{vertices} are fluctuation functions $S_\lambda(G_w)$, produced by the Taylor tree. Each vertex sits at a point $w$ in the normal bundle over the exceptional divisor. Since $S_\lambda(a) = \sum_m s_m a^m$, the vertex is a generating function for all valences $m$ (numbers of $G$-legs). The annotation insertions from the Taylor tree increase the $S$-index by $1/2$ per insertion ($\lambda \to \lambda + Q/2$ for $Q$ insertions), which is the algebraic effect of the raising operator $b^\dagger$.
\item The \textbf{propagator} is the resolved covariance kernel $C_{\alpha\beta}(w,w')$, encoding dataset correlations. Local contractions (tadpoles, $w = w'$) dress the vertices; bilocal contractions ($w \neq w'$) connect them.
\item The \textbf{equation of motion} is Weber's ODE, which acts as a Schwinger--Dyson identity: it relates vertices of different valence, reducing the two-leg amplitude $\langle t^2\rangle_G$ to a one-leg amplitude plus a contact term.
\item The \textbf{loop expansion parameter} is $1/n$ (the inverse sample size), playing the role of $\hbar$. The Gaussian approximation $\xi_n \approx G$ is the leading (``tree-level'') theory; non-Gaussian corrections from higher cumulants of $\xi_n$ are suppressed by powers of $n^{-1/2}$.
\item The \textbf{physical observables} (generalisation error, free energy) are normalised quantities, analogous to connected S-matrix elements. The linked-cluster theorem ensures only connected diagrams contribute, just as in QFT.
\end{itemize}

The Bayes quartet \eqref{eq:Gg}--\eqref{eq:Bt2} is the complete set of ``$2 \to 0$ scattering amplitudes'' at one-loop order: the asymptotic behaviour of the four error quantities, each expressed as a sum of the tree-level contact term $\lambda/\beta$ and one-loop corrections $\pm\nu$, $-\nu/\beta$. In this analogy:
\begin{itemize}
\item The \textbf{in-state} is the dataset $\mathcal{D}_n$ (or its Gaussian proxy $G$), which creates the fluctuations on the divisor.
\item The \textbf{out-state} is the error quantity being measured ($G_g$, $G_t$, $B_g$, or $B_t$).
\item The \textbf{scattering} is the interaction between dataset fluctuations and the singular geometry, mediated by the fluctuation functions and their bilocal correlations.
\end{itemize}
The contact term $\lambda/\beta$ is the tree-level amplitude: it depends only on the geometry of the singularity (the resolution exponents $h, k$) and involves no propagators. The singular fluctuation $\nu$ is the one-loop correction: it requires one bilocal propagator and depends on the full structure of the Gaussian field on the divisor (the covariance kernel $C$, the prior density $\rho$, and the vertex structure $S_\lambda$). The connected bubble $V$ is a second one-loop amplitude, related to $\nu$ by the Ward identity $\mathbb{E}[V] = 2\nu/\beta$ (the Gaussian IBP relation, analogous to a Ward identity in gauge theory).

\paragraph{Movies as Wilsonian RG flow.} The ``movies'' of the Taylor tree (sequences of accumulated multi-indices parametrising paths through the tree) and the Feynman diagrams of the Wick expansion operate at different stages of the computation. Movies determine \emph{what vertices exist}: each complete movie specifies a sequence of coordinate integrations (at each frame, a set of minimising coordinates is killed via the standard integral), producing a specific $S_\lambda$-vertex at the leaf with a specific $\lambda$, annotation count $Q$, insertion multi-indices $\alpha_j$, and weight function $\rho_\ell(w)$. The movie also determines which derivatives $\partial_v^{(\alpha)} G$ appear as external legs: these are derivatives with respect to the dead coordinates, determined by which coordinates were killed at which frame and what annotations were produced. The collection of all complete movies gives the full catalogue of vertices in the theory. The Wick contractions then happen \emph{after} the vertices are determined: given the vertices from the movies, dataset averaging contracts their legs using the propagator $C_{\alpha\beta}(w,w')$.

In this sense, the Taylor tree produces an \emph{effective theory}: at each frame, the current minimising coordinates are integrated out (the posterior concentrates sharply in those directions, with width $\sim n^{-1/(2k)}$), producing the fluctuation function vertices. The rescaling $t = \sqrt{n}\, v^k$ that produces $S_\lambda$ is the change of variables to the natural fluctuation scale, after which the $v$-integral becomes $n$-independent. The alive coordinates $w$, by contrast, are not rescaled: the posterior does not concentrate in those directions at leading order, and they remain as the degrees of freedom over which the Feynman calculus operates. We note the structural similarity to deriving an effective action by integrating out fast modes, though we do not claim a precise correspondence with Wilsonian renormalisation group flow.

\paragraph{Comparison with QFT: why the combinatorics is simpler.} While the parallel with quantum field theory is genuine, the diagrammatic theory here is considerably simpler than a typical QFT in two respects.

First, in QFT one typically has multiple particle species (photons, electrons, gluons, \ldots), each with its own propagator, and the interaction vertices specify which species can meet at a point (e.g.\ in QED, each vertex joins exactly one photon line, one electron line, and one positron line). This gives rise to selection rules: not every pair of legs can contract. In the SLT setting, there is only \emph{one} Gaussian field $G$, and \emph{any} two linear functionals of $G$ can pair. The propagator $C_{\alpha\beta}(w,w')$ varies depending on which derivatives and which points are involved, but there is no selection rule constraining which legs contract with which: everything pairs with everything. The theory is a ``scalar field theory with one species,'' not a gauge theory with multiple particle types.

Second, in QFT the vertices have fixed valence (e.g.\ a $\phi^4$ vertex has exactly four legs). Here the $S_\lambda$-vertex is a generating function $\sum_m s_m a^m$ that produces legs of all orders: the Wick contraction selects which terms in the power series contribute. This means one does not need to enumerate vertex types; the single function $S_\lambda$ encodes all of them.

The complexity in the SLT setting comes not from the combinatorics of the Wick contractions (which are straightforward) but from two other sources: the \emph{geometry} of the resolution (which determines the exponents $\lambda$, the strata, and the normal bundles) and the \emph{analytic structure} of the propagator $C_{\alpha\beta}(w,w')$ (which encodes the resolved Fisher information). The Weber ODE constrains the vertices algebraically, playing the role of the equations of motion, but the vertex structure itself is simpler than in typical QFT.

The fact that the entire $O(1/n)$ theory collapses to two numbers ($\lambda$ and $\nu$) is the SLT analogue of renormalisability: despite the infinite-dimensional structure of the Gaussian field on the divisor and the complicated geometry of the resolution, only two ``renormalised couplings'' survive at leading order.

\subsection{The field theory toolkit}\label{subsec:field_theory}

The setup of \S\ref{sec:averaging} places us in a standard Gaussian field theory framework: a Gaussian field $G$ on a smooth geometric space (the normal bundle over the divisor strata), vertices ($S_\lambda$) satisfying an ODE that acts as a Schwinger--Dyson constraint, a well-defined propagator ($C_{\alpha\beta}$) with a clean local/bilocal decomposition, a loop expansion parameter ($1/n$), and a linked-cluster theorem selecting connected diagrams. This is essentially the same starting position as a quantum field theorist after writing down a Lagrangian, and the standard toolkit becomes available.

\paragraph{Higher-order asymptotic coefficients.} The $O(1/n^2)$ terms in the error formulas come from two-loop connected diagrams (two bilocal propagators connecting normalised $S$-vertices) plus higher cumulant vertices (from the non-Gaussianity of $\xi_n$ at finite $n$). The Schwinger--Dyson hierarchy (iterating the Weber ODE to relate higher-valence amplitudes to lower ones) should constrain these the same way the one-loop answer is constrained by $M_2 = \frac{a}{2}M_1 + \lambda/\beta$, potentially reducing the number of independent amplitudes at each order.

\paragraph{Correlation functions on the divisor.} Quantities beyond the four error formulas are accessible: for instance, $\operatorname{Var}(G_g)$ or $\operatorname{Cov}(G_g, G_t)$ involve higher connected correlators of the $S$-vertices, computable by the same Wick machinery. These are the higher-point functions of the field theory, and they encode fluctuations of the error quantities across datasets.

\paragraph{Functional renormalisation in $\beta$.} The $\beta$-dependence of the theory has the structure of a renormalisation group flow. The tadpole dressing $(1-\beta c/2)^{-\lambda}$ diverges at $\beta = 1$, which is analogous to a critical point. The exponent $\lambda$ plays the role of a critical exponent, and $\beta = 1$ is the ``critical temperature.'' The ratios that appear in the physical quantities (the four formulas, $\nu$) are analogous to scaling functions that remain finite at criticality. A systematic study of the $\beta$-flow of $\nu(\beta)$ might yield non-trivial information about the approach to the physical point.

\paragraph{Multiple strata and inter-stratum propagators.} The expansion in this note is implicitly localised to a single stratum (or the set of leaves sharing the same leading exponent $\lambda$). But the true partition function is a sum over all leaves: $Z_n = \sum_\ell Z_n^{(\ell)}$, where different leaves may live on different strata of the exceptional divisor. When forming the normalised ratio $Z_n[\phi]/Z_n$, the denominator expansion produces cross-terms between leaves on \emph{different} strata. These give rise to \emph{inter-stratum} bilocal propagators (\cref{fig:inter_stratum}): if $w$ lives in the normal bundle of one stratum and $\tilde{w}$ in the normal bundle of another, the correlation $C_{00}(w, \tilde{w}) = \mathbb{E}[G(0,w) \cdot G(0,\tilde{w})]$ is still well-defined, because the Gaussian process $G$ is defined globally on the resolved manifold. The Wick/Isserlis machinery applies without modification: the random variables $\partial_v^{(\alpha)} G(0,w)$ from stratum 1 and $\partial_{v'}^{(\beta)} G(0,\tilde{w})$ from stratum 2 are jointly Gaussian (both being linear functionals of the same Gaussian process $G$), so Isserlis' theorem pairs them with covariance $C_{\alpha\beta}(w, \tilde{w})$. The Feynman expansion now involves two types of vertices ($S_{\lambda_1}$ and $S_{\lambda_2}$), each with its own Schwinger--Dyson constraint, connected by inter-stratum propagators.

\input{inter_stratum_figure}

Strata of the exceptional divisor are indexed by subsets $I$ of divisor components: stratum $S_I$ corresponds to $\{u_i = 0 : i \in I\} \setminus \bigcup_{j \notin I} \{u_j = 0\}$. Two strata ``meet'' when $J \subset I$, so that $S_I \subset \overline{S_J}$: the deeper stratum (more components vanishing) lies in the closure of the shallower one. In this case, the normal bundle of $S_J$ contains the normal directions of $S_I$ as a subset, and the Gaussian process $G$ is continuous across the boundary. The inter-stratum propagator $C_{00}(w, \tilde{w})$ therefore varies continuously as $\tilde{w}$ on $S_J$ approaches the intersection $S_I$. For strata that do not meet (disjoint components of the divisor), the propagator still exists but there is no such continuity constraint: the correlation between dataset fluctuations at the two singularities is a global property of the covariance kernel $C$.

At leading order, subleading strata ($\lambda_{\ell'} > \lambda$) are suppressed by $n^{-(\lambda_{\ell'} - \lambda)}$ and do not affect the Bayes quartet. But when two strata have nearby values of $\lambda$ (say $\lambda_1 < \lambda_2$ with $\lambda_2 - \lambda_1$ small), the crossover region where both strata contribute comparably to the partition function is controlled by the inter-stratum propagator. This is directly analogous to a phase transition in statistical mechanics, with $\lambda_2 - \lambda_1$ playing the role of the energy gap between competing phases. We develop this in the next subsection.

\subsection{Bayesian phase transitions}\label{subsec:phase_transitions}

In singular learning theory, Bayesian phase transitions arise when two regions of parameter space (two singularities, two components of $W_0$, or two competing models) have comparable contributions to the partition function. The transition between them is controlled by the difference of their free energies, and the diagrammatic framework gives a natural decomposition of this difference.

\paragraph{Setup.} Suppose the partition function decomposes as $Z_n = Z_n^{(1)} + Z_n^{(2)}$, where $Z_n^{(i)}$ is the contribution from region $i$ with RLCT $\lambda^{(i)}$ and multiplicity $m^{(i)}$. Each region has its own Taylor tree, its own vertices ($S_{\lambda^{(i)}}$-functions), and its own leaf weights $\rho^{(i)}(w)$. At leading order:
\[
Z_n^{(i)} \approx n^{-\lambda^{(i)}} (\log n)^{m^{(i)}-1}\, D^{(i)}(G)\,, \qquad D^{(i)}(G) = \int \rho^{(i)}(w)\, S_{\lambda^{(i)}}(G_w)\, dw\,.
\]
Crucially, both $D^{(1)}$ and $D^{(2)}$ are functionals of the \emph{same} Gaussian process $G$ (same dataset).

\paragraph{The free energy difference.} The total free energy is
\[
F_n = -\log Z_n = -\log Z_n^{(1)} - \log\!\left(1 + \frac{Z_n^{(2)}}{Z_n^{(1)}}\right) = F_n^{(1)} - \log\!\left(1 + e^{-(F_n^{(2)} - F_n^{(1)})}\right).
\]
The free energy difference between the two phases is
\begin{equation}\label{eq:free_energy_diff}
\Delta F_n := F_n^{(2)} - F_n^{(1)} = (\lambda^{(2)} - \lambda^{(1)})\log n - (m^{(2)} - m^{(1)})\log\log n + \log \frac{D^{(1)}(G)}{D^{(2)}(G)} + \cdots
\end{equation}
The first two terms are deterministic: they depend on the resolution geometry alone. The dataset-dependent part is entirely in the ratio $D^{(1)}(G)/D^{(2)}(G)$.

\paragraph{Away from criticality.} When $\lambda^{(1)} < \lambda^{(2)}$, the deterministic term $(\lambda^{(2)} - \lambda^{(1)})\log n \to +\infty$ dominates, so $\Delta F_n \to +\infty$ and region 1 wins (lower free energy) for large $n$. The ratio $Z_n^{(2)}/Z_n^{(1)} \sim n^{-(\lambda^{(2)}-\lambda^{(1)})} \to 0$, and the inter-phase diagrams are suppressed by this power. The Feynman calculus for $F_n$ reduces to the single-phase expansion around region 1, with exponentially small corrections from region 2.

\paragraph{At criticality.} When $\lambda^{(1)} = \lambda^{(2)} =: \lambda$, the leading $\log n$ terms cancel and the phase transition is controlled by the $O(1)$ term:
\begin{equation}\label{eq:critical_ratio}
\Delta F_n = -(m^{(2)} - m^{(1)})\log\log n + \log \frac{D^{(1)}(G)}{D^{(2)}(G)} + \cdots
\end{equation}
If the multiplicities also agree ($m^{(1)} = m^{(2)}$), the transition is controlled entirely by the ratio of leading coefficients $D^{(1)}(G)/D^{(2)}(G)$, which fluctuates with the dataset.

The expected free energy difference $\mathbb{E}[\Delta F_n]$ involves $\mathbb{E}[\log D^{(1)}(G) - \log D^{(2)}(G)]$. Each term has a cumulant expansion in connected diagrams, as in the single-phase case (\S\ref{subsec:normalised}). But now the two cumulant expansions are \emph{correlated}: $D^{(1)}(G)$ and $D^{(2)}(G)$ are functionals of the same Gaussian process, and their joint fluctuations are mediated by the inter-stratum propagator $C_{00}(w, \tilde{w})$ connecting the normal bundles of the two phases.

\paragraph{Three types of diagrams.} The diagrammatic expansion of $\mathbb{E}[\Delta F_n]$ at criticality involves three types of connected diagrams:
\begin{enumerate}
\item \textbf{Intra-phase diagrams} (within each region): $S_\lambda$-vertices at points $w$ in the normal bundle of region $i$, connected by intra-stratum propagators $b^{(i)}(w,w') = C_{00}^{(i)}(w,w')$. These give the individual cumulants of $D^{(i)}(G)$.
\item \textbf{Inter-phase diagrams} (connecting the two regions): $S_\lambda$-vertices from region 1 at $w$ connected to $S_\lambda$-vertices from region 2 at $\tilde{w}$ by the inter-stratum propagator $C_{00}(w, \tilde{w})$. These mediate the correlation between the two phases through the shared dataset.
\item \textbf{Cross-cumulant diagrams}: connected diagrams involving vertices from both regions simultaneously, arising from the joint cumulants of $D^{(1)}$ and $D^{(2)}$. These control the covariance $\operatorname{Cov}(\log D^{(1)}, \log D^{(2)})$ and hence the variance of $\Delta F_n$.
\end{enumerate}
At criticality ($\lambda^{(1)} = \lambda^{(2)} = \lambda$), both types of vertices are $S_\lambda$-functions in the same irreducible representation of the Weyl algebra, so the inter-phase diagrams are of the same order as the intra-phase ones: the two phases ``resonate.'' Away from criticality, the inter-phase diagrams are suppressed by $n^{-|\lambda^{(2)} - \lambda^{(1)}|}$.

\paragraph{The phase transition as a competition of singularities.} The inter-stratum propagator $C_{00}(w, \tilde{w}) = \mathbb{E}[G(0,w) \cdot G(0,\tilde{w})]$ (with $w$ and $\tilde{w}$ in different normal bundles) measures how strongly a dataset fluctuation that favours one singularity also favours the other. When the two singularities are ``similar'' (the inter-stratum propagator is large), the dataset fluctuations push them in the same direction: the phase transition is soft, with the ratio $D^{(1)}/D^{(2)}$ staying close to its population value. When the singularities are ``dissimilar'' (the propagator is small), the fluctuations are nearly independent: the phase transition is sharp, with large dataset-to-dataset variability in which phase dominates.

This gives a concrete diagrammatic characterisation of the Bayesian phase transitions studied in singular learning theory: the transition is controlled by the geometry of the two singularities (through $\lambda$, $m$, and the leaf weights $\rho$), the statistics of the Gaussian field on the resolved manifold (through the inter-stratum propagator), and their interaction (through the cross-cumulant diagrams). See \cref{fig:phase_transition} for a schematic.

\input{phase_transition_figure}

\paragraph{Localising the transition to the changed geometry.} In many cases of interest, the two competing phases share most of their exceptional divisor structure and differ only on a subset of components. For instance, two nearby local minima in the loss landscape may be related by a deformation that affects only part of the resolution. When both phases are resolved simultaneously by the same resolution $\pi: U \to W$, their leading coefficients decompose as sums over strata:
\[
D^{(i)}(G) = \sum_I D_I^{(i)}(G)\,.
\]
Write $\Delta$ for the set of strata where the two phases differ ($D_I^{(1)} \neq D_I^{(2)}$) and ``shared'' for the rest. Then
\[
\frac{D^{(1)}}{D^{(2)}} = \frac{D_{\mathrm{shared}} + D_\Delta^{(1)}}{D_{\mathrm{shared}} + D_\Delta^{(2)}}\,.
\]
When the shared part dominates ($D_{\mathrm{shared}} \gg D_\Delta^{(i)}$), the free energy difference at criticality reduces to
\[
\log \frac{D^{(1)}}{D^{(2)}} \approx \frac{D_\Delta^{(1)} - D_\Delta^{(2)}}{D_{\mathrm{shared}}} + O\!\left(\left(\frac{D_\Delta}{D_{\mathrm{shared}}}\right)^2\right).
\]
In the Feynman picture, the transition is localised: only diagrams touching the changed components $\Delta$ contribute to the perturbation $D_\Delta^{(1)} - D_\Delta^{(2)}$, while the shared components provide a ``background'' $D_{\mathrm{shared}}$ that sets the scale. The coupling between the changed and shared components is mediated by the cross-propagator $C_{00}(w_{\mathrm{shared}}, w_\Delta)$, which measures how strongly a dataset fluctuation on the unchanged part of the exceptional divisor correlates with a fluctuation on the changed part.

\paragraph{Probing the transition with expectation values.} The nature of a phase transition can be diagnosed by computing expectation values $\mathbb{E}_n[\phi] = Z_n[\phi]/Z_n$ for suitably chosen observables $\phi$. An observable $\phi$ that has different vanishing orders $l_i^{(\phi)}$ on the changed components $\Delta$ versus the shared components will be sensitive to the change in geometry. Specifically:
\begin{itemize}
\item If $\phi$ vanishes to different orders on the components that distinguish the two phases, then $Z_n[\phi]$ receives different contributions from the two phases, and the ratio $\mathbb{E}_n[\phi]$ will exhibit a discontinuity (in the asymptotic regime) as the dominant phase switches. This is exactly the wall-crossing phenomenon for observables.
\item By choosing a family of observables $\{\phi_\tau\}$ parametrised by $\tau$, one can ``scan'' the exceptional divisor and identify which components are affected by the transition: the components where the vanishing order $l_i^{(\phi_\tau)}$ changes as $\tau$ varies are the components participating in the phase transition.
\item The inter-stratum propagator $C_{00}(w_{\mathrm{shared}}, w_\Delta)$ determines how strongly these diagnostic observables couple the changed and unchanged geometry. A large cross-propagator means that observables supported on the shared components are still sensitive to the change (the bulk ``feels'' the defect); a small cross-propagator means the transition is invisible to observables that do not directly probe the changed components.
\end{itemize}
This perspective connects the abstract geometry of the exceptional divisor to concrete statistical quantities: the phase transition is characterised by which divisor components change, and expectation values of observables with appropriate vanishing profiles serve as order parameters that detect the transition.

\subsection{Missing elements}\label{subsec:missing}

Several aspects of this picture remain to be developed.

\paragraph{Multi-leaf contributions.} The derivation of the Bayes quartet assumes that the leading-order partition function is dominated by a single leaf type (or a sum of leaves with the same exponent $\lambda$). When multiple leaves with distinct exponents contribute, the subleading leaves give corrections at relative order $n^{-(\lambda_\ell - \lambda)}$. The diagrammatic framework extends straightforwardly: each leaf contributes its own $S_{\lambda_\ell}$-vertex, but the bilocal pairings between leaves with different $\lambda$-values involve products $\mathbb{E}[S_{\lambda_1}(G_w) S_{\lambda_2}(G_{w'})]$ with $\lambda_1 \neq \lambda_2$.

\paragraph{Finite-$n$ corrections.} For finite $n$, the empirical process $\xi_n$ is not exactly Gaussian: its higher cumulants $\operatorname{cum}_r(\xi_n(u_1), \ldots, \xi_n(u_r)) = n^{1-r/2}\, \kappa_r(u_1,\ldots,u_r)$ introduce higher-valence interaction vertices into the diagrammatic expansion ($r = 3$ at relative order $n^{-1/2}$, $r = 4$ at $n^{-1}$, etc.). At leading order ($O(1/n)$), only Gaussian pairings matter. Incorporating these corrections systematically would extend the Feynman calculus to a full perturbative expansion in $n^{-1/2}$.

\paragraph{Higher-order terms in $1/n$.} The $O(1/n^2)$ theory would involve: multi-loop connected diagrams (more bilocal propagators between normalised vertices), the $r = 4$ cumulant vertex, and cross-terms between the leading and subleading leaves of the Taylor tree. The Weber module structure should organise these systematically, since the ladder algebra prescribes how vertices of different valence are related, but the combinatorics has not been worked out.

\paragraph{Log-power cancellations.} The Taylor tree produces $(\log n)^j$ factors at each leaf, with $j$ ranging from $0$ to $r-1$ where $r$ is the corner multiplicity. After dataset averaging and summing over leaves, the coefficient of the top $(\log n)^{r-1}$ term may vanish by cancellation (between leaves, or by oddness of the Wick expectation). Determining which log powers actually survive requires understanding the global structure of the Taylor tree, not just individual leaves.

\paragraph{The role of the Weber module at higher orders.} The ladder algebra ($b, b^\dagger$, $N_\lambda$) and the Schwinger--Dyson identity were used here only to reduce $\langle t^2\rangle_G$ to $\lambda/\beta + \frac{1}{2}\langle Gt\rangle_G$. At higher orders, the full Weber module structure (including the action of $b$ as a lowering operator, and the doubly-infinite modules for non-half-integer $\lambda$) should constrain the higher-loop amplitudes. Whether this produces further ``Ward identities'' that reduce the number of independent amplitudes at each order is an open question.

\paragraph{Convergence at $\beta = 1$.} As discussed in \S\ref{subsec:convergence_beta}, the Wick resummation diverges at the physical inverse temperature $\beta = 1$. The ratios that appear in the Bayes quartet are well-defined, but a systematic treatment of the $\beta \to 1$ limit for higher-order amplitudes (where more complicated ratios appear) has not been given. The analytic continuation from $\beta < 1$ to $\beta = 1$ may require Borel summation or a non-perturbative completion of the Wick series.

\subsection{Computability}\label{subsec:computability}

Despite the open questions above, the diagrammatic framework provides a concrete recipe for computing dataset-averaged quantities to any desired order in $1/n$, for any model where the resolution of singularities is known:
\begin{enumerate}
\item \textbf{Enumerate vertices.} Run the Taylor tree to find all complete movies. Each movie produces a vertex: an $S_{\lambda_\ell}$-vertex with specific annotation count $Q_\ell$, insertion multi-indices, and leaf weight $\rho_\ell(w)$.
\item \textbf{Compute the propagator.} The covariance kernel $C(u,u') = \mathbb{E}_X[a(X,u)\, a(X,u')] - u^k(u')^k$ and its jet-derivatives $C_{\alpha\beta}(w,w')$ can be computed analytically (for tractable models) or numerically (by Monte Carlo sampling from the true distribution $q$).
\item \textbf{Draw diagrams.} For the desired observable and order in $1/n$, enumerate all connected Feynman diagrams at the appropriate loop order, including higher-cumulant vertices if needed.
\item \textbf{Evaluate.} Each diagram is an integral over the non-minimising coordinates of products of propagators and vertex factors, constrained by the Schwinger--Dyson identities. These integrals are finite-dimensional (over the $w$-variables of each participating leaf).
\end{enumerate}
At order $1/n$ (one loop), this procedure yields the Bayes quartet: only $\lambda$ and $\nu$ survive, which is why the result is universal (independent of the detailed structure of $C$ and $\rho$ beyond what $\nu$ captures). At order $1/n^2$, model-specific corrections appear: two-loop diagrams, the $r = 3$ cumulant vertex, and subleading leaves. These depend on finer structure of the propagator and the resolution geometry, but are computable in principle.

The bottleneck is step 1: finding the resolution of singularities and enumerating the complete movies. This is the algebraic geometry, not the field theory. For models where the resolution is known (e.g.\ normal crossing singularities, reduced rank regression, finite mixture models), the remaining steps are mechanical. The diagrammatic framework thus offers a systematic path from the algebraic geometry of the singularity to quantitative predictions about learning curves, generalisation, and model comparison.

\subsection{Related work}\label{subsec:related_work}

Feynman diagrammatic methods have been applied to deep learning theory and to Bayesian inference in other contexts, but the specific framework developed here (a Gaussian field theory on the resolved space, with Weber-function vertices and the resolved Fisher kernel as propagator) appears to be new. We briefly survey the closest related work.

\paragraph{Neural network field theory.} Roberts, Yaida, and Hanin \citep{roberts2022principles} develop a systematic effective theory for deep neural networks using $1/n$ perturbation theory, where $n$ is the network \emph{width}. At infinite width, the distribution of preactivations is exactly Gaussian (by the CLT); at finite width, non-Gaussianity creates interaction vertices (quartic coupling at $O(1/n)$, sextic at $O(1/n^2)$, etc.). The propagator is the neural network kernel $G^{(l)}_{\alpha_1\alpha_2}$ (the covariance of preactivations evaluated on two inputs), and the layer-to-layer recursion plays the role of a renormalisation group flow. Connected correlators (cumulants) are generated by the free energy $\log Z$, with the depth-to-width ratio $r = L/n$ controlling the effective model complexity. The Wick/Isserlis theorem is the computational workhorse throughout.

The structural parallel with our framework is striking: both have a Gaussian free theory, an expansion parameter ($1/n_{\text{width}}$ vs $1/n_{\text{samples}}$), interaction vertices from non-Gaussianity, and connected diagrams giving the free energy. However, the mathematical content is completely disjoint. Roberts--Yaida--Hanin work in the \emph{regular} regime (smooth parameter-to-function map, no singularities in the loss landscape), where the non-Gaussianity comes from finite width (a perturbation of the GP limit). Our framework works in the \emph{singular} regime, where the non-trivial structure comes from the geometry of the singularity (requiring resolution of singularities to define the expansion), the vertices are Weber/parabolic cylinder functions (not polynomial couplings), and the propagator is the resolved Fisher kernel (not the neural network kernel). The two frameworks are complementary: theirs probes the width direction, ours the sample-size direction near singularities.

See also Halverson, Maiti, and Stoner \citep{halverson2021neural} for the neural network / quantum field theory correspondence, and Dyer and Gur-Ari \citep{dyer2020asymptotics} for the large-$N$ (width) Feynman diagram expansion.

\paragraph{Information field theory.} Ensslin and collaborators \citep{ensslin2009information} formulate Bayesian signal reconstruction as a statistical field theory. The ``field'' is a spatially distributed signal $s(x)$, the propagator is the posterior covariance $D = [S^{-1} + R^\dagger N^{-1} R]^{-1}$ (where $S$ is the signal prior covariance and $R, N$ encode the response and noise), and interaction vertices arise from non-Gaussian or non-linear components of the likelihood. The free (Gaussian) theory reproduces the Wiener filter; loop corrections give non-linear signal reconstructions. This is a correct and useful observation (Bayesian inference with a Gaussian prior \emph{is} a Gaussian field theory), but the ``field'' lives on physical space (e.g.\ the sky for CMB reconstruction), not on a resolved parameter space, and there are no singularities or resolution of singularities involved. The mathematical content does not overlap with our framework.

\bibliographystyle{plainnat}
\bibliography{references_grammar}

\end{document}
