# Astra consult #33 — the grammar paper after the Taylor tree: what is the next autoformalisation programme?

Context: Lean 4 / Mathlib formalisation of the grammar paper (Gerraty–Murfet, "Grammar (Expectations and the Exceptional Divisor)"), now in its own repository `timaeus-research/grammar` (library/namespace `Grammar`, 261 modules, no sorry, pin `3a861ed`; factored out of `laplace` on 2026-09-07). Your consults #24–#32 steered the normal-block programme (Headlines I–XXI, frozen at #25) and the Taylor-tree programme (Headlines XXII–XXXIII, frozen at #32: `thm:TaylorTree`/`cor:standardintegralexp` in every positive dimension under the holomorphic-polydisc hypothesis with coefficient families `Re(∂^γ F(0)/γ!)` and the original integral; reviews v18–v26 no defect). Your #32 ranking of successors was: (1) posterior weak convergence for the normal-crossing model, (2) a second concrete Taylor-tree example, (3) boundary/Δ tail and non-box domains, (4) the resolution-based §3/§4.3 application.

**The user has now instructed: "continue on autoformalisation of the grammar paper as before".** That is authorisation for a new programme in this seabed. I need a roadmap of the same kind as #26 (staged, with gates, unit estimates, and explicit non-claims), aimed at *the paper's remaining statements*, not at adjacent mathematics.

## What the paper contains and what is formalised

Sections: 1 Introduction; 2 Background (resolution of singularities, irreducible decomposition, stratification, asymptotic expansions, comparability `defn:comparable`, empirical extension); 3 Expectation via resolution (normal crossing divisors and normal bundles `lem:normal_deriv`, `defn:normal_diff`; tubular neighbourhoods and integration along fibres; moment tensors; standard form and normal moment integrals; per-stratum decomposition `lem:adapted_pou`, **`thm:expectation_expansion`**; general expectation values `cor:expectation_expansion`); 4 Fluctuations (4.1 fluctuation function + ladder algebra/log insertions — fully formalised, ~40 dots; 4.2 standard integral `thm:TaylorTree`, `cor:standardintegralexp` — fully formalised; 4.3 Application to SLT: Hypothesis I, **`thm:strataempiricalexpansion`**, `cor:empirical_expectation`, `rem:pop_vs_emp`); 5 Related work; 6 Conclusion.

Lean dots: §4.1–4.2 dense; §4.3 has 4 dots (single-chart d=2 statements from the normal-block programme, see below); §3 has SIX dots into a *different* Lean repo (`StrucDual/Geometry/*`: chart-local tubular neighbourhoods, global tubular neighbourhood, tangent well-definedness — the shared differential-geometry layer) and none for `thm:expectation_expansion`; §2 has none. Note two dangling references in the paper: `\cref{prop:convergence}` (continuity of ξ ↦ C_μ,m(ξ) on C^ω([0,b]^d)) and `\cref{lemma:AsymInt}` (integrating an asymptotic expansion over the stratum) are cited in the §4.3 proof but no such labelled statements exist in the source — the paper relies on them without stating them.

### §3 main theorem (the paper's authors mark it in red: "The theorem is now out of date, and needs to be rewritten with the progress on fluctuations etc.")

```latex
\begin{thm}\label{thm:expectation_expansion}
Let $\phi: W \to \mathbb{R}$ be a real analytic observable, and write $l_i = \operatorname{ord}_{E_i}(\phi \circ \pi) \ge 0$ for the generic vanishing order of $\phi \circ \pi$ along $E_i$ (which is well-defined and constant on a dense open subset of $E_i$ by analyticity). Then
\begin{equation}\label{eq:thm_strata_decomp}
\mathcal{Z}_n[\phi] = \sum_I \mathcal{Z}_n[\phi;\, I] + O(e^{-n\varepsilon})
\end{equation}
where the sum is over all strata of $E$. Each contribution admits the asymptotic expansion
\begin{equation}\label{eq:thm_per_stratum}
\mathcal{Z}_n[\phi;\, I] \sim \sum_{k=1}^\infty \sum_{j=1}^{m_{I,k}} C_{I,k,j}(\phi)\, n^{-\lambda_{I,k}}(\log n)^{j-1}\,.
\end{equation}
Writing $l = (l_i)_{i \in I}$ for the multi-index of vanishing orders, if $D^l_\perp(\phi \circ \pi)|_{S_I} \not\equiv 0$ then the leading exponent is
\begin{equation}\label{eq:thm_leading_exponent}
\lambda_{I,1} = \min_{i \in I} \frac{h_i + l_i + 1}{2k_i}
\end{equation}
with multiplicity $m_{I,1} = \big|\big\{i \in I : (h_i + l_i + 1)/(2k_i) = \lambda_{I,1}\big\}\big|$; otherwise $\lambda_{I,1}$ is strictly larger, determined by the first $\gamma \ge l$ for which $D^\gamma_\perp(\phi \circ \pi)|_{S_I} \not\equiv 0$. The expansion \eqref{eq:thm_per_stratum} admits the coordinate-free expression
\begin{equation}\label{eq:thm_coordfree}
\mathcal{Z}_n[\phi;\, I] \sim \sum_{r \ge 0} \frac{1}{r!}\int_{S_I}
\big\langle D_\perp^r(\phi\circ\pi),\,\mathsf{M}_{I,r}(n)\big\rangle\;
\tau_*|\mu_I|
\end{equation}
where $D_\perp^r(\phi \circ \pi) \in \Gamma(S_I, \operatorname{Sym}^r(N^*S_I))$ is the $r$-th conormal derivative \textup{(\cref{defn:normal_diff})} and $\mathsf{M}_{I,r}(n) \in \Gamma(S_I, \operatorname{Sym}^r(NS_I))$ is the $r$-th moment tensor \eqref{eq:moment_tensor_defn}. In particular, if $l_i = 0$ for all $i \in I$ (so that $(\phi \circ \pi)|_{S_I} \not\equiv 0$), the leading coefficient is
\begin{equation}\label{eq:thm_leading_coeff}
C_{I,1,m_{I,1}}(\phi) = \frac{\Gamma(\lambda_{I,1})}{(m_{I,1}-1)!}\, a_{I}\,\int_{S_I} (\phi \circ \pi)|_{S_I}\; c_0\; |dv|
\end{equation}
where $c_0(v) = b(v,0)\,(\varphi \circ \pi)(v,0) > 0$ is the restriction of the smooth density factor, and $a_I > 0$ depends only on the numerical data $(k_i, h_i)_{i \in I}$ via \eqref{eq:a_minus_m_explicit}. When some $l_i > 0$, the leading coefficient instead involves the conormal derivative $D^l_\perp(\phi \circ \pi)|_{S_I}$ contracted against the moment tensor $\mathsf{M}_{I,|l|}(n)$ via \eqref{eq:thm_coordfree}.
\end{thm}
\begin{proof}
Steps 1--4 above establish each part: the pullback to the resolution \eqref{eq:pullback_integral}, localisation near the divisor \eqref{eq:localisation}, the strata decomposition via \cref{lem:adapted_pou}, and the tubular neighbourhood expansion of \cref{subsec:tubular_nbhd}. The asymptotic exponents and multiplicities follow from the zeta function analysis of \cref{subsec:standard_form}, and the leading coefficient is computed by combining the moment asymptotics with the dressed moment expansion \eqref{eq:dressed_moment} at $\gamma = 0$, $\delta = 0$.
\end{proof}
\begin{comment}
\begin{remark}[Two forms of the expansion]\label{rem:two_forms}
There are two natural ways to present the asymptotic expansion of $\mathcal{Z}_n[\phi]$. The \emph{per-stratum form} of \cref{thm:expectation_expansion} writes it as a sum over strata, with each stratum $S_I$ contributing its own sub-expansion \eqref{eq:thm_per_stratum}. This is the geometric presentation: it makes visible which components of the exceptional divisor are responsible for each asymptotic term, and is the natural setting for the coordinate-free machinery of \cref{subsec:moment_tensors}.
```

### §4.3 stochastic theorem and its currently formalised scope

```latex
\begin{thm} \label{thm:strataempiricalexpansion}\leanrefL{Grammar/Headline.lean\#L180}{headline\_coefficients\_in\_distribution}\leanrefL{Grammar/Headline.lean\#L201}{headline\_normalised\_remainders}
Assume the triple $(p,q,\varphi)$ satisfies hypothesis I with index $s=2$ and relative finite variance. Let $\phi : W \to \mathbb{R}$ be a real analytic function. The partition function for the tempered Bayesian posterior with observable decomposes 
\begin{equation}
    Z_n[\phi] = \int_W \phi(w) e^{-\beta n L_n(w)}\varphi(w) dw = e^{-\beta n L_n(w_0)}\cdot Z_n^0,
\end{equation}
where $Z_n^0$ has the following asymptotic expansion 
\begin{equation}
    Z^0_n[\phi] \sim \sum_{\mu \in \Lambda^*}\sum_{m=1}^d C_{\mu,m}(\xi_n) n^{-\mu}(\log n)^{m-1}.
\end{equation}
The coefficients $C_{\mu,m}(\xi_n)$ are random variables that converge in distribution $C_{\mu,m}(\xi_n) \to C_{\mu,m}(G)$ where $G$ is a Gaussian process as $n\to\infty$. For each $(\mu',m') \in \Lambda^* \times \{1,\ldots,d\}$, the following convergence in distribution holds 
    \[
     \frac{1}{n^{-\mu'}(\log n)^{m' - 1}} \bigg\{ Z^0_n[\phi] - \sum_{(\mu,m)<(\mu',m')} C_{\mu, m}(\xi_n)\, n^{-\mu} (\log n)^{m - 1} \bigg\}\, \to C_{\mu',m'}(G).
    \]
\end{thm}
```
Formalised-scope remark (what the normal-block programme proved, single chart, d = 2, conditional on convergence in distribution of the weighted Taylor data (ξ_n, η_n) in the coefficient Banach space ℓ¹_ρ):
```latex
\begin{remark}[Formalised scope of \cref{thm:strataempiricalexpansion}]\label{rem:strataempirical_lean}
The Lean formalisation proves the single-chart $d=2$ statements conditional on convergence in distribution of the weighted Taylor data $(\xi_n,\eta_n)$ in the coefficient Banach space $\ell^1_\rho$: every finite vector of canonical coefficients $(A_\alpha,B_\alpha)$ converges in distribution (\texttt{headline\_coefficients\_in\_distribution}; in the notation above $C_{\mu,2}=A_{2\mu}/2$, $C_{\mu,1}=B_{2\mu}$), the coefficient maps being locally Lipschitz in $\ell^1_\rho$ (\texttt{headline\_coefficient\_lipschitz}, \texttt{\_B}); and the ordered normalised remainders converge, first $\big(Z-\sum_{\gamma<\alpha}\big)/(N^{-\alpha}\log N)\Rightarrow A_\alpha$ and then, after subtracting the \emp
\end{remark}
```
```latex
\begin{cor}\label{cor:empirical_expectation}\leanrefL{Grammar/HeadlinePosterior.lean\#L82}{headline\_chart\_posterior\_limit}\leanrefL{Grammar/HeadlinePosterior.lean\#L46}{headline\_quotient\_in\_distribution}
Under the hypotheses of \cref{thm:strataempiricalexpansion}, the expectation $\mathbb{E}_{w|\mathcal{D}_n}[\phi] := Z_n[\phi]/Z_n$ admits the asymptotic expansion 
\begin{equation}\label{eq:empirical_expectation_full_expansion}
\mathbb{E}_{w|\mathcal{D}_n}[\phi]\sim \sum_{s \in \mathcal{S}} \sum_{q \in \mathcal{Q}} d_{s,q}(\phi,\xi_n)\, n^{-s}(\log n)^{q-1},
\end{equation}
where $\mathcal{S} \subset \mathbb{Q}_{\ge 0}$ and $\mathcal{Q} \subset \mathbb{Z}$ are discrete index sets and $\xi_n$ is the empirical process. The coefficients  converge in distribution  $d_{s,q}(\phi,\xi_n) \to d_{s,q}(\phi,G)$ as $n\to\infty$, and are determined recursively from the coefficients $A_{k,j}(\phi,\xi_n)$ of $Z_n[\phi]$ and the coefficients $B_{k,p}(\xi_n) := A_{k,p}(1,\xi_n)$ of $Z_n$ via the division formula \cref{lemma:division}. All the coefficients $A_{k,p}(1,\xi_n)$, $B_{k,p}(\xi_n)$ and $d_{s,q}(\phi,\xi_n)$ converge in distribution  to a random variable as $n\to\infty$. The leading term is
\begin{equation}
d_{s_0,q_0}(\phi,\xi_n) = \frac{A_{i_0,j_0}(\phi,\xi_n)}{B_{k_0,p_0}(\xi_n)},
\end{equation}
where $(i_0, j_0)$ and $(k_0, p_0)$ are the leading indices of the asymptotic expansions of $Z^0_n[\phi]$ and $Z^0_n$ respectively.
\end{cor}
\begin{proof}
```
```latex
Apply \cref{thm:strataempiricalexpansion} to the numerator $Z_n[\phi]$ and the denominator $Z_n[1]$. The term $e^{-\beta n L_n(w_0)}$ cancels and the proof follows from applying \cref{lemma:division} and $B_{k_0,p_0}(\xi_n) > 0$ for all $\xi_n$ by \cite[Main Theorem II]{greybook}. 
\end{proof}
\begin{remark}[Formalised scope of \cref{cor:empirical_expectation}]\label{rem:empirical_expectation_lean}
At chart level, for $d=2$ with equal starting exponents $p=(h_1+1)/k_1=(h_2+1)/k_2$, deterministic amplitudes $\eta_\phi,\eta_1$ (the pull-backs of $\phi\varphi$ and $\varphi$) with $\eta_1(0)>0$, and a common random phase whose Taylor data converge in distribution, the Lean formalisation proves the leading term of the quotient: $Z_n[\phi]/Z_n[1]\Rightarrow\eta_\phi(0)/\eta_1(0)$ (\texttt{headline\_chart\_posterior\_limit}). The random fluctuation factor $\int_0^\infty s^{p-1}e^{-\beta s^2+\beta s\xi(0)}ds$ common to numerator and denominator cancels, so the leading empirical posterior expectation converges to the deterministic corner ratio $\phi(0)$ when $\eta_\phi=\phi\eta_1$; fluctuations
\end{remark}
```
```latex
\begin{remark}[Population vs.\ empirical expectation values]\label{rem:pop_vs_emp}
The population partition function $\mathcal{Z}_n[\phi] = \int \phi\, e^{-nK}\varphi\, dw$ and the empirical partition function $Z_n[\phi] = \int \phi\, e^{-\beta n L_n}\varphi\, dw$ are related but distinct objects. After resolution and applying the standard form \citep[Main Theorem~6.1]{greybook}, the empirical partition function on each chart takes the form $Z(\beta,n;\xi_n,\eta)$ where $\xi_n$ is the empirical process; the population version is the specialisation $\xi = 0$. Several aspects of this relationship deserve comment.
\begin{itemize}
\item[\textup{(i)}] \emph{Exponents are shared.} The asymptotic exponents $\mu \in \Lambda^*$ and their multiplicities $m \in \mathbb{Z}_{\geq 1}$ are determined by the resolution data $(k_i, h_i)$ and are the same for both the population and empirical expansions. In particular, the per-stratum organisation (\cref{thm:expectation_expansion}), the shifted exponent $\mu_I(\phi)$ from the vanishing orders \cref{eq:mu_I_phi}, and the wall-crossing mechanism driven by changes in vanishing order all apply equally to the empirical case.
\item[\textup{(ii)}] \emph{Coefficients differ.} The population coefficients (e.g.\ \eqref{eq:thm_leading_coeff}) are deterministic integrals over the strata, while the empirical coefficients $C_{\mu,m}(\xi_n)$ are random variables depending on the empirical process. Although $\mathbb{E}_{\mathcal{D}_n}[\xi_n(u)] = 0$ \citep[Remark~6.3]{greybook}, the coefficients depend non-linearly on $\xi_n$ through the fluctuation function, so the expected empirical coefficient $\mathbb{E}_{\mathcal{D}_n}[C(\xi_n)]$ is not equal to the population coefficient $C(0)$.
\end{itemize}
Understanding the precise relationship between the population and empirical coefficients, in particular, whether the fluctuation tree structure of the empirical expansion (\cref{thm:TaylorTree}) can be used to express the empirical coefficients systematically in terms of the population ones and the empirical process, is left to future work.
For the simplest random fluctuation --- a Gaussian constant $\xi(0)=X\sim N(0,v)$ --- the Lean formalisation makes the non-commutation of expectation and expansion quantitative: with $J_p(x)=\int_0^\infty s^{p-1}e^{-\beta s^2+\beta sx}\,ds$ the positive factor of the leading coefficient, $\mathbb E_+[J_p(X)]=\int_0^\infty s^{p-1}e^{-(\beta-\beta^2v/2)s^2}\,ds$ in the extended reals (\texttt{lintegral\_gaussMomentJ\_eq}), which exceeds $J_p(0)$ and is finite only when $\beta v<2$; the expected leading coefficient can thus be infinite although every sample coefficient is finite.
\end{remark}
```

## What the Taylor-tree programme now makes available (relevant for §4.3 in general d)

- `thm_TaylorTree_coeffFamily` (every d): for coefficient families cξ, cη with Σ|c_γ| b^|γ| < ∞, `TaylorTreeConclusion`: support in Λ(h,k), cutoff-independent coefficients A_{μ,j}(cξ,cη) = explicit absolutely convergent series Σ_p β^p/p! T_{μ,j,p}(cη * J^{*p}) (J = constant-free part of cξ, * = Cauchy product), remainder bound |Z(N) − Σ_{μ<L} Σ_j A_{μ,j} N^{-μ} (log N)^j| ≤ C(L)·N^{-L}(1+log N)^{d-1} for N b^{2|k|} ≥ 1 with C(L) depending on the data only through ξ(0) = cξ 0 and the two weighted masses (`cutoffBound`, monotone in the masses).
- Stability of coefficients under perturbation of the family: `abs_spectralCoeff_sub_le` / `abs_truncCoeff_sub_le` (appended-perturbation stability with fixed constant phase; constants depend on masses and ξ(0)); the kernel functional T_{μ,j,p} is bounded by (mass) × M_{ν,r,p}(|a|) (`abs_kernelFunctional_le`); the phase-moment generating identity Σ_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B).
- Derivative dictionary: β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a) (`fluctMoment_eq_mixed_deriv`); ∂_a^p S_μ = β^p S_{μ+p/2}.
- Analytic bridge: holomorphic F on a polydisc of radius R > b ⇒ Cauchy families, |c_γ| ≤ M r^{-|γ|}, `polyCoeff_eq_coordDeriv_div`, `thm_TaylorTree_taylor`.
- From the normal-block programme (d = 2 single chart): coefficient Banach space ℓ¹_ρ of weighted Taylor data, locally Lipschitz coefficient maps (`headline_coefficient_lipschitz`), convergence in distribution of finite vectors of coefficients and of ordered normalised remainders (`headline_coefficients_in_distribution`, `headline_normalised_remainders`), chart posterior limit (`headline_chart_posterior_limit`), random-phase transfer (`PhaseRandomTransfer`: F_{N_n}(X_n) ⇒ F(Z) for random phases), stochastic chart assembly (Headline XVIII, conditional on an external chart decomposition), the 1/log N stochastic regime, `lintegral_gaussMomentJ_eq`.

## HEADLINES index (verbatim, for reference)

# Grammar §4 formalisation — headline index (general-dimensional normal block)

## Taylor-tree programme (opened 2026-09-07, after the freeze; Astra #26)
**Stage 1 — exact multivariate state density — COMPLETE (units 223–226).**
| Headline | Statement | File:line |
|---|---|---|
| XXII | exact state density: `∫_{(0,1]^{n+1}} ∏aᵢ^{wᵢ} g(∏aᵢ) = ∫₀¹ v g`, `v = eval (stateDensityRep n w)` a finite sum of `z^{μ-1}(-log z)^j`, `μ ∈ {wᵢ+1}`, `j < multiplicity` | StateDensity.lean (`weightedBoxIntegral_eq_stateDensity`, `stateDensityRep_exponent_mem`, `stateDensityRep_degree_lt`) |
| XXII′ | Mellin transform `∫₀¹ z^s v = ∏ 1/(wᵢ+s+1)`; basis `∫₀¹ τ^{c-1}(-log τ)^j = j!/c^{j+1}`; real identity for `f ≥ 0`; integrability | StateDensityAPI.lean (`mellin_stateDensity`, `integral_Ioc_rpow_mul_neg_log_pow`, `integral_unitBox_eq_stateDensity`) |
| XXII″ | top coefficient `c_{l,m-1} = (1/(m-1)!) ∏_{wᵢ+1≠l} 1/(wᵢ+1-l)`; monomial form `= a_{-m}/(m-1)!` (Headline XXI's `mellinCoeff h k l 1`) | StateDensityLeadCoeff.lean (`stateDensityRep_leadCoeff`, `monomial_leadCoeff`) |
Convolution calculus in `PowLogCalculus.lean` (`PowLogRep.eval_conv`, `conv_exponent_mem`, `conv_degree_lt`).
**Stage 2 — exact monomial moments with a constant phase — COMPLETE (units 227–229).**
| Headline | Statement | File:line |
|---|---|---|
| XXIII | exact identity: `∫_{(0,1]^{n+1}} u^h (√N u^k)^p e^{-βNu^{2k}+β√N u^k a} = ∏1/(2kᵢ) ∑_{(μ,j,c)∈v} c N^{-μ} ∑_{i≤j} C(j,i)(log N)^{j-i} ∫₀^N t^{μ-1}(-log t)^i g(t)`, `g(t) = (√t)^p e^{-βt+β√t a}`, every `N > 0` | MonomialPhaseExpansion.lean (`monomialPhase_eq`) |
| XXIII′ | asymptotic form: `T(N) − monomialMainSum(N) = O(e^{-βN/8})` with the full moments `fluctMoment β a p μ i = ∫₀^∞ t^{μ-1}(-log t)^i g` | MonomialPhaseTail.lean (`monomialPhase_isBigO`, `tail_le`) |
Tools: `phaseKernel`, `truncMoment`, `basis_scaling`, `integral_unitBox_monomial_eq_stateDensity` (MonomialPhaseIdentity.lean).
**Stage 3 — polynomial Taylor tree with spectral truncation — COMPLETE (units 230–239; Astra #27, Gates A–D passed).**
Scope: polynomial phase `ξ` and amplitude `η` (finite monomial lists `MonoRep`), box `(0,1]^{n+1}` (`d = n+1`), `β > 0`, `kᵢ > 0`, `N` = paper's `n`; `Z(N) = polyPhaseIntegral = ∫ η u^h e^{-βN u^{2k} + β√N u^k ξ(u)}`; `Λ_L = latticeBelow (2∏kᵢ) L` (the lattice `Q⁻¹ℕ` below the cutoff; coefficients vanish at exponents not carried by any density).
| Headline | Statement | File:line |
|---|---|---|
| XXIV | exact polynomial Taylor tree, every `N > 0`: `Z(N) = ∑_p β^p/p! ∑_{(γ,c)∈ηJ^p} c · monomialTruncSum(h+γ)` with `J = ξ − ξ(0)` (absolutely convergent; `HasSum` form at L159 / L286) | PhaseTaylorIdentity.lean:270 (`polyPhaseIntegral_eq_tsum_truncSum`) |
| XXV | quantitative cutoff: `|Z(N) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} A_{μ,j}(log N)^j| ≤ C · N^{-L}(1+log N)^n` for all `N ≥ 1`, `L > 0`, `C` explicit and `N`-free; exact form `= R_high − tail` at L444 | LowSpectrumTail.lean:457 (`taylorTree_cutoff_bound`) |
| XXVI | asymptotic expansion: `Z − spectralSum_L = O(N^{-L}(1+log N)^n)` (L41), `= O(N^{-L}(log N)^n)` (L64), `= o(N^{-L'})` for `L' < L` (L81) | TaylorTreeAsymptotic.lean:41 (`taylorTree_isBigO`) |
| — | spectral coefficient `A_{μ,j} = ∑_p β^p/p! K_k ∑_{(γ,c)} c ∑_{q=j}^{n} coeffAt(ρ_{h+γ},μ,q) C(q,j) fluctMoment_p(μ,q−j)`: cutoff-free, absolutely convergent (Gate D) | SpectralCoefficients.lean:371 (`spectralCoeff`), :343 (`summable_coeffTerm_series`), :384 (`mainSeries_eq_sum`) |
| — | Gate C: `|R_high(N)| ≤ K_k‖η‖₁(n+1)!Q^n M_{L,n}(ξ(0)+‖J‖₁) · N^{-L}(1+log N)^n` (τ-side estimate, constants independent of the monomial) | HighSpectrumBound.lean:376 (`abs_highRemainder_le`), :118 (`basis_integral_le`) |
| — | Gate B: log majorant `M_{ν,r,p}(b) = ∫₀^∞ t^{ν-1}(1+|log t|)^r(√t)^p e^{-βt+βb√t}` finite for all real `b`; Tonelli `∑_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B)` (no smallness on `B`) | PhaseMajorant.lean:146 (`integrableOn_logMajorant`), :246 (`tsum_phaseLogMoment_series`) |
| — | Gate A: uniform weighted budget `∑|c| j! Q^j ≤ (n+1)! Q^n` for every lattice-supported state density | DensityBudget.lean:204 (`budget_stateDensityRep_le`) |
| — | lattice `Q = 2∏kᵢ`, `(e+1)/(2kᵢ) ∈ Q⁻¹ℕ_{>0}`, spacing `1/Q`, finite `latticeBelow` | SpectralLattice.lean:37 (`ratio_mem_lattice`) |
| — | polynomial ℓ¹ algebra: `|P(u)| ≤ ‖P‖₁` on the cube, `‖PQ‖₁ = ‖P‖₁‖Q‖₁`, `‖P^p‖₁ ≤ ‖P‖₁^p`, `fluct` | MonomialRep.lean:85 (`abs_eval_le_l1`), :149 (`l1_pow_le`) |
| — | **spectral support (u240)**: `A_{μ,j} = 0` unless `μ ∈ Λ(h,k) = ⋃_i ((hᵢ+1)/(2kᵢ) + ℕ/(2kᵢ))` (paper's candidate set, `candidateExp`); expansion restated over `Λ(h,k) ∩ [0,L)`; explicit coefficient formula (`C_{μ,m} = A_{μ,m-1}`); summed exponential tail `|tailSeries| ≤ C(1+log N)^n e^{-βN/4}` | CandidateSupport.lean:87 (`spectralCoeff_eq_zero_of_not_candidate`), :131 (`taylorTree_isBigO_candidate`), :105 (`spectralCoeff_eq`), :142 (`abs_tailSeries_le_exp`) |
Low-spectrum tail replacement: `LowSpectrumTail.lean` (`tsum_logTailMoment_series` L48, `exp_le_rpow_const` L137, `abs_tailSeries_le` L396). Numerical checks: XXIV in d=1 to 2e-15; XXV in d=1 (L = 5/2): error × N^{5/2} ≈ 0.15 stable over N = 10…640.
**Stage 4 — analytic data by coefficient families — COMPLETE (units 241–247; Astra #28).**
Hypothesis: `ξ(u) = ∑_γ cξ_γ u^γ`, `η(u) = ∑_γ cη_γ u^γ` with `∑|c_γ| < ∞` (`CoeffFamily.AbsSummable`) — a *sufficient, strictly weaker* form of the paper's hypothesis: holomorphy on `D_R`, `R > 1`, implies it via Cauchy estimates `|c_γ| ≤ M_r r^{-|γ|}` (bridge NOT formalised; it would also identify `c_γ = ∂^γ f(0)/γ!`). Paper correspondence: `P_μ(X) = ∑_{j≤n} A_{μ,j} X^j`, `C_{μ,m} = A_{μ,m-1}`. The coefficients are cutoff-independent LIMITS of the polynomial coefficients; their identification with an explicit absolutely convergent series over `(p, γ)` (a convolution of families) is NOT formalised. Route: box truncations `truncList c m` (finite `MonoRep`), coefficient stability, pass to the limit at fixed `N`.
| Headline | Statement | File:line |
|---|---|---|
| XXVII | `|Z(N) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} A_{μ,j}(cξ,cη)(log N)^j| ≤ cutoffBound(ξ(0), mass η, mass ξ) · N^{-L}(1+log N)^n` for all `N ≥ 1`, `L > 0`; `O(N^{-L}(1+log N)^n)` (L54), `O(N^{-L}(log N)^n)` (L66), `o(N^{-L'})` for `L' < L` (L96), over `Λ(h,k)` (L122) | FamilyTaylorTree.lean:39 (`familyTaylorTree_cutoff_bound`) |
| — | **stability gate**: `|A_{μ,j}(ξ',η') − A_{μ,j}(ξ,η)| ≤ K_k D (E β M_{μ+1/2,n}(a+B) ‖Δ‖₁ + M_{μ,n}(a+B) ‖Δη‖₁)` for `η' ~ η ++ Δη`, `J' ~ J ++ Δ`, same constant phase | CoeffStability.lean:147 (`abs_spectralCoeff_sub_le`) |
| — | family coefficients `A_{μ,j}(cξ,cη) = lim_m A_{μ,j}(truncations)` (Cauchy via the gate), vanishing off `Λ(h,k)` | FamilySpectralCoeff.lean:130 (`familySpectralCoeff`), :135 (`tendsto_truncCoeff`), :142 |
| — | `Z_m(N) → Z(N)` at fixed `N` (dominated convergence) | FamilyPhaseIntegral.lean:45 (`tendsto_polyPhaseIntegral_truncList`) |
| — | uniform constant: `taylorCutoffConst ≤ cutoffBound a E B` from `ξ(0) = a`, `‖η‖₁ ≤ E`, `‖J‖₁ ≤ B` (`M` monotone in `b`, `tailConst` in `|b|`) | UniformCutoffConst.lean:61 (`taylorCutoffConst_le`) |
| — | coefficient families: mass, eval (`|eval| ≤ mass` on the cube), truncations with `truncList c m' ~ truncList c m ++ rest`, `‖rest‖₁ ≤ tailMass c m → 0`, uniform convergence | CoeffFamily.lean:189 (`truncList_perm`), :149 (`tailMass_tendsto_zero`), :221 (`abs_evalF_sub_truncList_le`) |
| — | list algebra: `pow (J ++ Δ) p ~ pow J p ++ R`, `‖R‖₁ ≤ p‖Δ‖₁(‖J‖₁+‖Δ‖₁)^{p-1}` | MonoRepPerm.lean:65 (`pow_append_perm`) |
| — | general box `(0,b]^d` (u248): `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))`, rescaled family `c_γ b^{|γ|}` summable iff the weighted mass at radius `b` is finite | BoxScaling.lean:80 (`familyPhaseIntegralBox_eq`) |
| XXVIII | Taylor tree on `(0,b]^d` (u249): for `∑|c_γ| b^{|γ|} < ∞`, `|Z_b(N) − boxSpectralSum(N)| ≤ b^{|h|+d} cutoffBound · (N b^{2|k|})^{-L}(1+log(N b^{2|k|}))^n`; `O(N^{-L}(1+log N)^n)` in the sample size (L82); paper's form `∑_μ N^{-μ} ∑_{j≤n} C^b_{μ,j}(log N)^j` by binomial re-expansion (L131, `boxCoeff`) | BoxTaylorTree.lean:45 (`boxTaylorTree_cutoff_bound`) |
| ★ | **end-to-end wrapper (u256)** `thm_TaylorTree_coeffFamily`: `∃ C, TaylorTreeConclusion …` — one coefficient system (= `familySpectralCoeff` of the rescaled data), vanishing off `Λ(h,k)`, equal to the paper's absolutely convergent series, remainder bound for every cutoff `L` (`N b^{2|k|} ≥ 1`), `IsBigO` in `N`, and the mixed derivative dictionary; quantifier order `∃ C ∀ L` | TaylorTreeWrapper.lean:68 |

**Stage 6 — the analytic bridge, one variable (units 257–258; Astra #30 C₁ pilot) — COMPLETE.**
| — | Cauchy coefficients of `f : ℂ → ℂ` holomorphic on `|z| ≤ r` (u257): `discCoeff f r n = (cauchyPowerSeries f 0 r).coeff n`; `∑ discCoeff z^n = f z` on `|z| < r` (L48); Cauchy estimate `‖discCoeff‖ ≤ M_r r^{-n}` (L40); weighted summability at every `b < r`; `discCoeff = f^{(n)}(0)/n!` (L75) | CauchyCoeff1D.lean |
| XXXI | **analytic Taylor tree in `d = 1` under the paper's own hypothesis (u258)**: for `fξ, fη` holomorphic on the closed disc of radius `r > b`, the real Cauchy-coefficient families represent `Re fξ, Re fη` on `(0,b]` (L50: `∑ Re(discCoeff) x^n = Re f(x)`) and `TaylorTreeConclusion` holds for them — no reality hypothesis needed | AnalyticBridge1D.lean:102 (`thm_TaylorTree_analytic_1d`) |
| XXXI′ | **paper-facing `d = 1` corollary (u259)**: real `ξ, η` on `(0,b]` with holomorphic extensions to `|z| < R`, `R > b`; for any `r ∈ (b,R)` the real Cauchy-coefficient families satisfy `TaylorTreeConclusion` and their family integral IS the original `Z(N) = ∫_{(0,b]} η u^h e^{-βN u^{2k} + β√N u^k ξ} du` (`familyPhaseIntegralBox_eq_orig_1d`) | AnalyticTaylorTree1D.lean:63 (`thm_TaylorTree_analytic_1d'`) |
Review v24 (u256–258): qualified pass, no defect; should-fixes done in u259 (paper-facing corollary, integral transport, `Re f` docstring, closed-disc/totalised-integral wording). Release scope: coefficient-family theorem in every dimension; analytic bridge complete in `d = 1` only.
**Stage 7 — the several-variable analytic bridge (units 260–264; Astra #31 route R2) — COMPLETE.**
| — | normalised circle operator `A_r g = (2πi)⁻¹ ∮ w⁻¹ g` (u260): `‖A_r g‖ ≤ sup‖g‖`, Cauchy formula `A_r((1−z/w)⁻¹ g) = g z`, coefficient `HasSum`, parametric continuity | CircleOperator.lean |
| — | iterated operator `A_r^{[d]}` along `Fin.cons`, torus bound, `SliceHolo`, **iterated Cauchy formula** `A_r^{[d]}(w ↦ F w ∏(1−zᵢ/wᵢ)⁻¹) = F z` (L160), supplied by joint differentiability on the open polydisc (L213) | PolydiscCauchy.lean |
| — | parametric continuity on sets, series interchange `A_r(Σ G_n) = Σ A_r(G_n)` (L91), product geometric series | CircleOpParam.lean |
| — | **Cauchy coefficients `c_γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ})`** (u263, the gate): `‖c_γ‖ ≤ M r^{-|γ|}` (L33), reconstruction `∑_γ c_γ z^γ = F z` as `HasSum` on the open polydisc (L87), `∑ ‖c_γ‖ b^{|γ|} < ∞` for `b < r` | PolydiscCoeff.lean |
| XXXII | **`thm:TaylorTree` under the paper's own hypothesis, every dimension (u264)**: real `ξ, η` on `(0,b]^d` with holomorphic extensions to the polydisc `{|zᵢ| < R}`, `R > b`; for `r ∈ (b,R)` the real Cauchy-coefficient families `polyRealCoeff` satisfy `TaylorTreeConclusion` and their family integral IS the original `Z(N)` (`familyPhaseIntegralBox_eq_orig`) | AnalyticTaylorTree.lean:112 (`thm_TaylorTree_analytic`) |
Not formalised: the multi-index derivative identification `c_γ = ∂^γ F(0)/γ!` (γ! = ∏ γᵢ!; Astra #31 units 9–10, coordinate-wise uniqueness) — the coefficients are the explicit iterated Cauchy integrals.
| XXXII′ | **paper-facing form (u265)**: the same from `0 < b < R` alone, `∃ cξ cη C` (radius `(b+R)/2` chosen inside) | AnalyticTaylorTree.lean:133 (`thm_TaylorTree_analytic'`) |
Review v25 (u260–264): qualified pass at statement level, no mathematical defect — "the analytic bridge is successfully closed"; should-fixes done in u265: headline reads "applies under the paper's hypothesis" (the formal matching assumption is real-part agreement `Re Fξ = ξ` on the box, weaker than a genuine extension), residual task stated with the complex/real distinction (`polyCoeff = ∂^γ F(0)/γ!`, `polyRealCoeff = Re(…)`, linkage to `ξ` needs the genuine extension), `∃ r` corollary XXXII′, torus-bound estimate vs closed-polydisc-bound reconstruction distinguished in the docstrings; the "duplicate declaration" remarks are statement-extractor artefacts (each source has one). Numerics: `polyCoeff` at `d = 2` vs Taylor coefficients `2e-16`, reconstruction `4e-15`.

**Analytic bridge — COMPLETE in every dimension (2026-09-07; pin see git; Headlines XXXI–XXXII′, units 257–265; reviews v24–v25).** `thm:TaylorTree`/`cor:standardintegralexp` now hold under the paper's own hypothesis (holomorphic `Fξ, Fη` on a polydisc of radius `R > b` with `Re Fξ = ξ`, `Re Fη = η` on `(0,b]^d`) with the original integral `Z(N)`. Only the derivative identification of the coefficients remains outside the formalisation.
Remaining for general `d` (superseded — done above): iterated one-variable Cauchy coefficient extraction with the product majorant `|c_γ| ≤ M r^{-|γ|}` (Astra #30: gate = quantitative two-coordinate lemma; 12–20 units).

**Stage 8 — derivative identification `c_γ = ∂^γ F(0)/γ!` (units 266–268; Astra #32: bounded sprint, cap 6 units, gate after unit 1) — COMPLETE in 3 units.**
| — | **identification (u267)**: `c_γ = A_r^{[d]}(F ∏ wᵢ^{-γᵢ}) = ∂^γ F(0)/γ!` for `F` holomorphic on the open polydisc of radius `R > r`, with `∂^γ` the fixed-order iterated coordinate derivative `coordDeriv` (L55: tail coordinates first, head last; ordinary `iteratedDeriv` at `0`) and `γ! = ∏ γᵢ!`; proof by induction with `polyCoeff_eq_discCoeff` + the one-variable identification, using the induction hypothesis as a local identity (no differentiation under the integral) | CoordDeriv.lean:99 (`polyCoeff_eq_coordDeriv_div`) |
| XXXIII | **`thm:TaylorTree` with Taylor-derivative coefficients, every positive dimension (u268)**: same hypotheses as XXXII′ (`0 < b < R`, `Fξ, Fη` holomorphic on the polydisc, `Re Fξ = ξ`, `Re Fη = η` on `(0,b]^d`); the Taylor-tree conclusion holds for the families `taylorFamily F γ = Re(∂^γ F(0)/γ!)` and the family integral is the original `Z(N)`; `taylorFamily F 0 = Re F(0)` | TaylorTreeDerivatives.lean:57 (`thm_TaylorTree_taylor`) |
Non-claims (Astra #32, review v26): no permutation invariance of `∂^γ` (fixed-order nested derivative); the families are the Taylor coefficients at `0` of the real restriction `u ↦ Re F(u)`, not derivatives of the supplied `ξ, η` (constrained only on the positive box); the holomorphic polydisc extensions are hypotheses (not constructed from real analyticity); cutoff independence = independence from the spectral threshold `L`; candidate support is containment, not nonvanishing. Corollary: `polyCoeff` is independent of the admissible radius (`polyCoeff_radius_indep`, CoordDeriv.lean:137).
Review v26 (u266–268): pass / pass / qualified pass, overall qualified pass — "the derivative identification is mathematically correct and closes the specific qualification left by v25"; wording fixes applied in u269 (holomorphic-polydisc setting named explicitly, "every positive dimension", real-restriction phrasing).

**★ TAYLOR-TREE PROGRAMME — COMPLETE AND FROZEN (2026-09-07; Headlines XXII–XXXIII, units 223–269; reviews v18–v26, no mathematical defect).** `thm:TaylorTree` / `cor:standardintegralexp` are formalised in the holomorphic-polydisc, normal-crossing-box setting in every positive dimension with the paper's coefficient data `Re(∂^γ F(0)/γ!)` and the original integral `Z(N)` (`thm_TaylorTree_taylor`), with exponent support `Λ(h,k)`, the paper's log indexing, cutoff-independent coefficients equal to the explicit absolutely convergent Cauchy-product series, the mixed derivative dictionary, and remainder `O(N^{-L}(1+log N)^{d-1})` for every `L`. Per Astra #32 no further theorems are added here; the preferred separately authorised successor is posterior weak convergence for the normal-crossing model.
| — | **gate passed (u266)**: `x ↦ polyCoeff d r (F ∘ Fin.cons x) γ'` is holomorphic on the disc of radius `ρ ∈ (r,R)` for `F` holomorphic on the open polydisc of radius `R` — no differentiation under the integral: slice Cauchy formula at radius `ρ`, Fubini `iterOp_circleOp_swap` (from `circleOp_eq_integral`: `A_r` is the circle average), then `hasFPowerSeriesOn_cauchy_integral` | ParamHolo.lean:137 (`differentiableOn_polyCoeff_param`) |
Astra #32 (`tide-log/gpt6_bigpicture_v32.md`): freeze `45b0943` as the qualified milestone; finish the identification with the fixed-order recursive `coordDeriv` target (tail coordinates first, head last; `γ! = ∏ γᵢ!`; ordinary `iteratedDeriv` at `0`), exploiting the induction hypothesis as a local identity instead of arbitrary-order differentiation under the integral; expose the identified families in the public theorem; the real-part family is `Re(coordDeriv F 0/γ!)`, i.e. the Taylor coefficients of the canonical analytic representative `Re F` — NOT derivatives of the supplied `ξ` (which is constrained only on the positive box); afterwards close the programme (posterior weak convergence = preferred separately authorised successor; §4.3/general domains are separate programmes).

**[historical — superseded by Stages 6–8 above] Taylor-tree programme — COMPLETE under the coefficient-summability hypothesis (2026-09-07; pin `ba849b3`; Headlines XXII–XXX, units 223–255; reviews v18–v23 all pass/qualified pass with no mathematical defect).** Formalised: `thm:TaylorTree`/`cor:standardintegralexp` on `(0,b]^d` for phase and amplitude given by coefficient families with `∑|c_γ| b^{|γ|} < ∞` — the paper's exponent set `Λ(h,k)`, log indexing, cutoff-independent coefficients equal to the paper's explicit absolutely convergent Cauchy-product series (XXIX), the mixed derivative dictionary `β^p fluctMoment = (−∂_μ)^i ∂_a^p S_μ(a)` (XXX), remainder `O(N^{-L}(1+log N)^{d-1})` for every `L`. **Not formalised (the single remaining gap to the paper's own hypotheses):** the Cauchy-estimate bridge from holomorphy on the polydisc `D_R`, `R > b`, to `∑|c_γ| b^{|γ|} < ∞` with `c_γ = ∂^γ f(0)/γ!` (Mathlib has no several-variable Cauchy estimates; Astra #29: 15–25 units, not budgeted). Review v23 (u255): qualified pass ("duplicate declaration" is a statement-extractor artefact; the source has one). Paper erratum: `∂_a^p S_μ = β^p S_{μ+p/2}`, the displayed formula omits `β^p`.

**Qualified release (Astra #29, 2026-09-07; pin `bb504c0`).** Principal theorem: Headline XXVIII (general box), core Headline XXVII (unit cube), corollary `boxSpectralSum_eq`. Hand-off wording (Astra #29): *We have formalised the Taylor-tree asymptotic expansion and its standard-integral corollary for general boxes, under the coefficient hypothesis `∑_γ |c_γ| b^{|γ|} < ∞` for phase and amplitude: the paper's exponent set `Λ(h,k)`, the paper's logarithmic indexing, a single coefficient system independent of the cutoff, and for every `L > 0` the remainder `O(N^{-L}(1+log N)^{d-1})`; no `sorry`, no additional axioms. This is a qualified formalisation of `thm:TaylorTree`: the coefficient hypothesis is sufficient and less restrictive than the polydisc hypothesis, but the implication from the paper's analytic hypothesis (incl. `c_γ = ∂^γ f(0)/γ!`) is not formalised; coefficients are explicit for polynomial inputs and defined for summable families as stable limits of truncations — their identification with the paper's explicit absolutely convergent series, and the special-function derivative notation, remain unformalised (the `∂_a` half of the dictionary is now a theorem, u250). Independent reviews v20/v21 found no mathematical defects.* Constants depend on `d, h, k, β, b, L` and the data through `ξ(0)` and the masses; the general-box quantitative bound needs `N b^{2|k|} ≥ 1`; "vanish off `Λ(h,k)`" is support containment, not nonvanishing.
Astra #29 plan: A (explicit coefficient series via `Finset.Iic` convolution, 8–12 units, gate = summable majorant of `∑_p β^p/p! |T_{μ,j,p}(c_η * J^{*p})|`), C scouting (Cauchy bridge, 2–3 scouting units then 15–25; gate = arbitrary `b < R`, closed cube), B derivative dictionary (5–8), then final review.

Review v21 (Stage 4): qualified pass, no mathematical defect (moment shift, appended-perturbation estimate, constant phase of truncations, fixed-N limit, `|a|+B` monotonicity all confirmed); should-fixes are documentation (done above: analytic bridge labelled, coefficient-series identification labelled, u242 described as appended-perturbation stability). The reviewer's "duplicate `pow_append_perm`" is a paste artefact of the statement extractor (source has one declaration).
**Stage 5 — explicit coefficient series (units 251–254; Astra #29 candidate A) — COMPLETE.**
| — | Cauchy product of families `(c*e)_γ = ∑_{α≤γ} c_α e_{γ-α}` (Finset.Iic, no antidiagonal instance): `evalF (c*e) = evalF c · evalF e` on the cube, `mass (c*e) ≤ mass c · mass e` | CoeffConv.lean:81 (`evalF_conv`), :116 (`mass_conv_le`) |
| — | collected coefficients of lists: `coeffFn (mul P Q) = conv`, `coeffFn (pow P p) = convPow`, `coeffFn (fluct P)`, `coeffFn (truncList c m) = truncFamily c m` | CoeffFnBridge.lean:154 (`coeffFn_mul`), :176 (`coeffFn_pow`) |
| — | kernel functional `T_p(f) = K_k ∑_γ f_γ S_p(μ,j;γ)`: `coeffTerm P = T_p (coeffFn P)`, `|T_p f| ≤ K_k D M_{μ,n,p}(a) mass f` | CoeffKernel.lean:81 (`coeffTerm_eq_kernelFunctional`), :100 (`abs_kernelFunctional_le`) |
| XXIX | **the paper's coefficient series**: `A_{μ,j}(cξ,cη) = ∑_p β^p/p! T_p(cη * J^{*p})`, `J = fluctFamily cξ`, absolutely convergent (`|term_p| ≤ K_k D M_{μ,n,p}(a) mass(cη) mass(J)^p`, Tonelli) and EQUAL to the limit-defined family coefficient (`familySpectralCoeff_eq_series`, μ > 0); `(cη * J^{*p})_γ` is the paper's `η_m/m! · ξ_{n,p}` (eq:flucttreeterms); power-difference estimate `mass(c^{*p} − c'^{*p}) ≤ p B^{p-1} mass(c − c')` (L95) | FamilyCoeffSeries.lean:306 (`familySpectralCoeff_eq_series`), :152 (`familyCoeffSeries`), :195 (`summable_familyCoeffSeries_terms`) |
Review v21's qualification (ii) is thereby closed in the coefficient-family setting: for `μ > 0` the family coefficients are the *collected* Cauchy-product series matching the paper's formula when the input families are normalised Taylor coefficients `c_γ = ∂^γ f(0)/γ!` (that normalisation is part of the unformalised analytic bridge). `summable_familyCoeffSeries_terms` is absolute convergence of the outer collected series in `p`; the fully expanded multi-index series is not exposed as a separate theorem. Review v22 (u250–254): qualified pass, no mathematical defect; hand-off wording: *the phase-parameter derivative dictionary is formalised including the factor `β^p` (the paper's displayed `∂^p S_μ = S_{μ+p/2}` omits it); spectral-parameter derivatives producing logarithmic moments remain to be formalised.*
| XXX | **the derivative dictionary (u255)**: `∂_μ fluctMoment = −fluctMoment` at the next log order; `fluctMoment β a p μ i = (−1)^i ∂_ν^i S_{ν+p/2}(a)|_{ν=μ}` (L169); `β^p fluctMoment β a p μ i = (−∂_μ)^i ∂_a^p S_μ(a)` (the paper's coefficient notation, sign `(−∂_μ)^i ↔ (−log t)^i` exact); shift identity `fluctMoment β a p ν 0 = S_{ν+p/2}(a)`; identification of the family coefficients with the paper's series for EVERY real `μ` (L210) | FluctuationDerivativeMu.lean:180 (`fluctMoment_eq_mixed_deriv`) |
| — | derivative dictionary, phase half (u250): `∂_a fluctMoment = β · fluctMoment` at the next phase order; `∂_a^p S_μ(a) = β^p fluctMoment β a p μ 0` | FluctuationDerivative.lean (`hasDerivAt_fluctMoment`, `iteratedDeriv_fluctuationFn`) |
Not formalised: the Cauchy-estimate bridge from holomorphy on a polydisc to `∑|c_γ| < ∞` (the only remaining gap to `thm:TaylorTree` under the paper's own hypotheses; Astra #29: 15–25 units, unbudgeted).

Review v20 (Stage 3): qualified pass, no mathematical defect; should-fix items 1 (candidate support), 2 (coefficient formula), 6 (exponential tail) done in u240; 3–5 are documentation (done). **Stage 3 frozen as reviewed milestone at u240.**
Not formalised (Stage 4, Astra #28 plan: coefficient families `(Fin d → ℕ) → ℝ` with `Summable |c|`, polynomial truncations, coefficient-stability gate first, then density): analytic (non-polynomial) `ξ, η`; `b ≠ 1` (scaling `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; ξ(b·), η(b·))`); the derivative dictionary `fluctMoment β a p μ i = (−∂_μ)^i S_{μ+p/2}(a) = β^{-p}(−∂_μ)^i ∂_a^p S_μ(a)` (interpretation only). Hypothesis audit: the paper assumes holomorphy on the origin-centred polydisc `D_R`, `R > b`, which gives `∑|c_γ| b^{|γ|} < ∞` by Cauchy estimates — so "absolutely summable coefficient family on the box" is implied by the paper's hypothesis (no localisation gap for the stated theorem; the Cauchy-estimate bridge itself is a separate Mathlib obligation).


## Completion statement (2026-09-07)
The scoped **§4 normal-block programme is complete** at the reviewed baseline `d65d48b` (Astra #24–#25; reviews
v1–v17): general machinery (Headlines VI–XIX), the assembled statistical example (XX–XX'' with the genuine-prior
lemmas), and the Abelian coefficient dictionary (XXI). Explicit non-claims: XX–XX'' are fixed-`θ` moment-generating-
function limits, not a formalised weak-convergence theorem for posterior laws; XXI is a real-axis Abelian coefficient
limit, not meromorphic continuation or an exact-pole-order theorem; the signed-weight statements are analytic, the
posterior interpretation needs `ρ ≥ 0`. The remaining paper material (full Taylor-tree expansion, complex Mellin
continuation, the boundary tail, `eq:flucttreeterms`, the resolution-based §4.3 application) is **outside the
completed work package**. Preferred separately authorised successor (Astra #25): posterior weak convergence of the
law of `√n x₀x₁` to `N(z,1)` for deterministic phases (reconnaissance first: Lévy/Curtiss route vs direct
test-function route); a cheap robustness variant is available via Mathlib's CLT (i.i.d. mean-0 variance-1 data).

Pinned commit for the mirror `grammar_lean.tex`: see `\laplaceLeanCommit` there. All statements
zero `sorry`/`axiom`; independent statement-level reviews v1–v15 in `tide-log/gpt6_fidelity_review_v*.md`.
Conventions: boxes `(0,1]^d` (`unitBox`), `(-1,1]^d` (`symBox`); `ratioExp h k i = (hᵢ+1)/(2kᵢ)`,
`λ = min`, `J` the minimisers, `m = multCount`; chart variable `N` (paper's `√n`), `p = 2λ`;
`phaseMoment β p a = ∫₀^∞ s^{p-1} e^{-βs²+βas} ds` is the paper's `J_p(a) = S_{p/2}(a)/2`.

| Headline | Statement | File:line |
|---|---|---|
| VI  | bare equal-ratio normal moment asymptotic | HeadlineMonomial.lean:73 |
| VII | bare mixed-ratio (face) asymptotic, `minRatio` wrapper | HeadlineMonomialMixed.lean:58 |
| VIII | continuous amplitude: face-supported functional | HeadlineAmplitude.lean:85 |
| IX  | tangential integration against a compact set | HeadlineTangential.lean:38 |
| X   | stochastic `1/log N` regime (d = 2) | HeadlineStochasticLog.lean:37 |
| XI  | signed reflections, zero phase (parity) | SymmetricAmplitudeAsymptotic.lean:89 |
| XII | zero-phase unequal-exponent dictionary, `noLogConst` closed form | QuadraticMixedBridge.lean:115 |
| XIII | phase-dressed leading term, general d (face integral of `η(πu) J_p(ξ(πu))`) | HeadlinePhase.lean:117 |
| XIII' | equal ratios: corner value `η(0) J_p(ξ(0)) / ((d-1)! ∏ kᵢ)` (= paper's `A_p` at d = 2) | HeadlinePhase.lean:138 |
| XIII'' | uniform cutoff `(0,b]^d` | PhaseCutoff.lean:117 |
| XIV | per-stratum posterior quotient (deterministic) | PhasePosterior.lean:148 |
| XV  | conditional finite chart assembly (deterministic) | HeadlineAssembly.lean:51 |
| XVI | random phases and amplitudes: `F_{N_n}(X_n) ⇒ F(Z)` | PhaseRandomTransfer.lean:222 |
| XVII | random per-stratum posterior quotient | PhaseRandomPosterior.lean:99 |
| XVIII | assembled stochastic posterior quotient over charts | HeadlineStochasticAssembly.lean:102 |
| XIX | symmetric box with phase (signed `x^h` / absolute `|x|^h`) | HeadlineSymmetricPhase.lean:102 / 127 |
| XX  | end-to-end example: model `N(x₀x₁,1)` on `(-1,1]²`, posterior MGF of `√n x₀x₁` → `e^{zθ+θ²/2}` (exact likelihood identity at L152) | NormalCrossingModel.lean:278 |
| XX' | Gaussian data `Yᵢ` iid `N(0,1)`: `E_post[e^{θ√n x₀x₁}] − e^{Zₙθ+θ²/2} → 0` in probability (uniform-in-phase MGF at L255, Chebyshev at L350) | NormalCrossingData.lean:361 |
| XX'' | Gaussian data: `E_post[e^{θ√n x₀x₁}] ⇒ e^{Zθ+θ²/2}`, `Z ~ N(0,1)` (exact law `Zₙ ~ N(0,1)` at L123) | NormalCrossingLaw.lean:178 |
| XXI | real-axis Abelian limit for the leading Mellin (zeta) coefficient: `s^m ∫ η u^{2k(-λ+s)+h} → ∏_J 1/(2kᵢ) ∫ η(πu) ∏_{∉J} u^{h-2kλ}` as `s → 0⁺` (`η` continuous on the closed cube; no continuation/pole-order claim); `η = 1` gives the paper's `a_{-m}` (L303); Γ-dictionary with Headline VIII (L338) | MellinCoefficient.lean:285 |
| — | genuine prior (`ρ ≥ 0`, `ρ(0) > 0`): evidence positive at every sample size; posterior mean of `1` is `1` | NormalCrossingPrior.lean:87 / 102 |
| — | formal face-vs-corner counterexample (`5√π/12 ≠ √π/4`) | MixedRatioCounterexample.lean:126 |
| — | abstract assembly (min exponent, max log multiplicity) | ChartAssembly.lean:142 |

Earlier headlines (I–V, d = 2 Taylor tree, coefficient CLT, chart posterior limit, `1/log N` regime)
are in `Headline.lean`, `HeadlinePosterior.lean` and their neighbours.

## What the theorems assume (hand-off)
See `projects/grammar/staging/normal-block-report-v3.pdf` §Assumptions: the chart decomposition is an
external input ("conditional" = assuming); densities are deterministic and strictly positive; no
remainders; joint convergence of the empirical phases is a hypothesis; the stochastic results are weak
limits, not expansions with rates; selection is at the normalised scale and signed numerators may cancel.
Headlines XX/XX'/XX'' concern one concrete statistical model with no chart-decomposition or likelihood-remainder
hypothesis (XX assumes `Zₙ → z`; XX'/XX'' assume i.i.d. `N(0,1)` data). They are fixed-`θ` moment-generating-function
limits, not weak convergence of the posterior law, with no rate; the weight `ρ` may be signed (`ρ(0) > 0` only), and for a
genuine prior (`ρ ≥ 0` on the box) the evidence is positive at every sample size (`NormalCrossingPrior.lean`). Reviews v16–v17.


## Questions

1. **What is the right next programme?** Candidates as I see them: (A) **the stochastic Taylor tree in general d** — upgrade `thm:strataempiricalexpansion` from the d = 2 single-chart normal-block version to the full Taylor-tree coefficient system: (A1) `prop:convergence` as a theorem — the coefficient map (cξ, cη) ↦ A_{μ,j}(cξ, cη) is continuous/locally Lipschitz on the weighted-ℓ¹ ball (we have the stability gates and the ℓ¹ kernel functional; the constant depends on ξ(0), so local Lipschitz on balls); (A2) convergence in distribution of every finite vector of coefficients and of the ordered normalised remainders, given convergence in distribution of the Taylor data in weighted ℓ¹ (continuous mapping + the uniform remainder bound with `cutoffBound` monotone in the masses — tightness of the masses gives o_p); (A3) chart assembly and the stratum integral (the dangling `lemma:AsymInt`: integrating over v ∈ S_I with a compactly supported ρ_I, uniformity of C(L) in v), conditional on an external chart decomposition as in Headline XV/XVIII; (A4) `cor:empirical_expectation` via division of asymptotic series (`lemma:division`) in general d. (B) The §3 population theorem `thm:expectation_expansion` in a conditional form (the authors say it must be rewritten; formalising a statement its authors consider out of date seems premature — but a conditional per-stratum decomposition given an external resolution atlas might be the honest target). (C) Your #32 successors (posterior weak convergence for the normal-crossing model; a second example). (D) The Δ boundary tail / general domains. Please rank, with unit estimates and go/no-go gates, and say which the user's instruction most plausibly points at.

2. **For (A), the formal shape.** What is the right Lean statement of `prop:convergence` (continuity vs local Lipschitz; in which norm — Σ|c_γ| b^|γ| with which b, the box radius or a larger r; role of ξ(0))? What is the right formal model of "ξ_n → G in distribution" for the coefficient data (a random variable in the weighted-ℓ¹ Banach space? measurability of the coefficient maps? Portmanteau/continuous mapping in Mathlib: `Tendsto (map …) … (𝓝 …)` in `ProbabilityMeasure` with `tendsto_iff_forall_integral_tendsto` / `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`?) — the d = 2 programme already did this in ℓ¹_ρ; should we generalise that infrastructure or restate it over `CoeffFamily d`? Gates?

3. **The dangling `prop:convergence` / `lemma:AsymInt`.** Should the formalisation supply these as named theorems (paper-facing value: they are cited but missing), and how should the hand-off report flag this to the authors?

4. **Non-claims and traps** you foresee (e.g. Hypothesis I / the greybook standard form is external input; the random phase ξ_n must be real-analytic on the box for the analytic bridge, but the empirical process's holomorphic extension radius is data-dependent — how should the hypothesis be phrased so it is honest and matches the greybook's fundamental conditions; measurability of ξ ↦ Cauchy coefficients).

5. **Order of work for the first 3 units**, so I can start immediately after this consult, with the gate that would make you say stop.
