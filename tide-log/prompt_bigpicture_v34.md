# Astra consult #34 — Programme S after tranche A1–A2: A3 (tangential integration and chart assembly) go/no-go and formal shape

Context: Lean 4 / Mathlib formalisation of the grammar paper's §4 in `timaeus-research/grammar` (main pin `46a7ac8`; 269 modules, no sorry). Your consult #33 opened Programme S (§4.3 stochastic Taylor tree in every positive dimension) with the tranche A1–A2 capped at 18 units and a hard review after unit 3. **Tranche A1–A2 is complete in 8 units (u270–277), reviews v27 and v28 PASS.** HEADLINES block:

**Programme S — the §4.3 stochastic Taylor tree in every positive dimension (Astra #33; `tide-log/gpt6_bigpicture_v33.md`) — tranche A1–A2 COMPLETE in 8 units (u270–277; cap was 18; reviews v27 after unit 3 and v28 after unit 7, both PASS).** Target: `thm:strataempiricalexpansion` at chart level for arbitrary normal dimension `d = n+1`: (A1) the canonical box coefficients `C_{μ,j}` are Lipschitz on balls, hence continuous and measurable, on the weighted-ℓ¹ data space `E_b × E_b` (this is the paper's dangling `prop:convergence`); (A2) under convergence in distribution of the data, every finite coefficient vector and every ordered normalised remainder converges in distribution. Later tranches: (A3) tangential integration (`lemma:AsymInt`, dominated) and finite chart assembly; (A4) posterior division after a statement gate. Non-claims: no derivation from Hypothesis I; no common analytic radius for random phases (data are `E_b`-valued by hypothesis); no Gaussian identification of the limit; `N` = paper sample size.
Review v28 (u273–276): PASS / PASS / PASS / PASS (conditional chart-level scope) — "no mathematical blocker … I would accept this tranche for the stated A1–A2 scope"; nonblocking exports requested (`mem_predSet_iff`, cutoff-independence of the predecessor set for every `L > μ`, the explicit majorant estimate `|R_N^{μ,j}(x) − C_{μ,j}(x)| ≤ remainderMajorant N` on the ball, joint convergence of several remainders) — done in u277. Non-claims for XXXV: conditional on data convergence in the weighted-ℓ¹ topology (not derived from Hypothesis I); fixed common radius `b`; one chart, no tangential integration / assembly; no Gaussianity; `N_n` deterministic sample sizes `≥ 0` (paper's `n`), the normalised quotient is meaningful above the thresholds `N ≥ e`, `N b^{2|k|} ≥ 1`.
| — | **S8 joint remainders + predecessor-set interface (u277)**: `mem_predSet_iff`, `mem_latticeBelow_iff`, cutoff independence `predSet_eq_filter` (L50); vector-valued uniform-on-balls lemma; **XXXV joint form** `tendstoInDistribution_orderedRemainderVec` (L127): finitely many ordered remainders converge jointly in distribution to the vector of limiting coefficients | StochasticTaylorTreeJoint.lean |
| XXXV | **The stochastic Taylor tree, one chart, every positive dimension (u276)**: for measurable random weighted Taylor data `X_n : Ω → E_b × E_b` with `X_n ⇒ Z` in distribution and sample sizes `N_n → ∞` (`N_n ≥ 0`): every finite vector of canonical coefficients converges in distribution, `(C_{μ_i,j_i}(X_n))_i ⇒ (C_{μ_i,j_i}(Z))_i` (L113); for every target `(μ,j)`, `μ ∈ Q⁻¹ℕ`, `j ≤ n`: `R_{N_n}^{μ,j}(X_n) − C_{μ,j}(X_n) → 0` in probability (L140) and `R_{N_n}^{μ,j}(X_n) ⇒ C_{μ,j}(Z)` (L165); ingredients: XXXIV (continuous mapping), S6 (uniform on balls), norm-boundedness in probability by portmanteau (L64), Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`). This is `thm:strataempiricalexpansion` at chart level in arbitrary normal dimension, conditional on convergence in distribution of the data | StochasticTaylorTree.lean |
| — | **S6 ordered normalised remainders converge uniformly on data balls (u275)**: ordering `(ν,q) ≺ (μ,j) ↔ ν < μ ∨ (ν = μ ∧ j < q)` (L38), `orderedRemainder R_N^{μ,j}(x) = (Z(N;x) − ∑_{≺} C_{ν,q}(x) N^{-ν} (log N)^q)/(N^{-μ}(log N)^j)` (L63); for `μ ∈ Q⁻¹ℕ`, `j ≤ n`: `TendstoUniformlyOn (R_N^{μ,j}) (C_{μ,j}) atTop (closedBall 0 R)` (L334; explicit majorant estimate `abs_orderedRemainder_sub_le` L238); cutoff `L = μ+1`, retained terms `ν > μ` are `O(N^{-(ν-μ)}(1+log N)^n)`, `ν = μ, q < j` are `O(1/log N)`, coefficients bounded on the ball by XXXIV; thresholds `N ≥ e`, `N b^{2|k|} ≥ 1` | OrderedRemainder.lean |
| — | **S5 the standard integral is continuous in the data (u274)**: for fixed `N ≥ 0`, `x ↦ Z(N; x) = dataBoxIntegral` is Lipschitz on data balls with constant `b^{|h|+d} e^{β√(Nb^{2|k|}) R}(1 + Rβ√(Nb^{2|k|}))` (L237), continuous (L249) and Borel measurable; `continuousOn_evalF` (Weierstrass M-test on the closed cube), `evalF_sub`, `integrableOn_boxIntegrand` | DataIntegralContinuity.lean |
| — | **S4 canonical cutoff theorem on data balls (u273)**: for `‖x‖ ≤ R`, `L > 0`, `N > 0`, `N b^{2|k|} ≥ 1`: `|Z(N;x) − ∑_{μ∈Λ_L} N^{-μ} ∑_{j≤n} C_{μ,j}(x)(log N)^j| ≤ b^{|h|+d} dataCutoffConst(R) (N b^{2|k|})^{-L} (1+log(N b^{2|k|}))^n` with `dataCutoffConst n k β L R = cutoffBound n k β L R R R` (L78); `cutoffBound_mono` (monotone in `|ξ(0)|`, both masses) | DataCutoff.lean |
| XXXIV | **Continuity of the canonical coefficient functionals (u272) — a weighted-ℓ¹ substitute for the paper's cited `prop:convergence`**: the coefficient `C_{μ,j}` of `N^{-μ}(log N)^j` in the expansion of the original box integral, as a function of the weighted-ℓ¹ data `(cξ, cη) ∈ E_b × E_b`, is Lipschitz on every closed ball (L103, constant `dataLipConst`), continuous (L116) and Borel measurable, for every real `μ` and `j`; finite coefficient vectors are continuous (L137). Topology: weighted ℓ¹ at the box radius `b`; no `C^ω` identification claimed | DataCoeffContinuity.lean |
Review v27 (u270–272): pass / pass / qualified pass — "no substantive correction to the displayed A1 Lipschitz mathematics"; proceed to A2 with: canonical cutoff interface stated with `dataBoxCoeff`; measurability of `x ↦ Z(N;x)` and of the remainders; finite predecessor set with the ordering `(ν,q) ≺ (μ,j) ↔ ν < μ ∨ (ν = μ ∧ q > j)` (larger log powers first); cutoff `L > μ`; uniform normalised-remainder convergence on data balls (thresholds `N b^{2|k|} ≥ 1`, `N > 1`); boundedness in probability of `‖X_n‖` + Slutsky.
| — | **S2 gate PASSED (u271) — ballwise Lipschitz continuity of the canonical coefficients with varying constant phase**: for absolutely summable families with all four masses `≤ R`, `|A_{μ,j}(cξ',cη') − A_{μ,j}(cξ,cη)| ≤ familyLipConst n k β μ R · (mass(cξ'−cξ) + mass(cη'−cη))`, every real `μ` (L318); the new ingredient is `|fluctMoment β a p μ i − fluctMoment β a' p μ i| ≤ β M_{μ,n,p+1}(R) |a−a'|` on `|a|,|a'| ≤ R` by the mean value theorem and `∂_a fluctMoment = β fluctMoment(p+1)` (L38); the three perturbation series (phase constant, amplitude, constant-free phase) are summed by the Tonelli identity and its shift; `familyLipConst = K_k D (2βR M_{μ+1/2,n,0}(2R) + M_{μ,n,0}(2R))` | FamilyCoeffLipschitz.lean |
| — | **S1 statement lock (u270)**: `DataSpace d = ℓ¹((Fin d → ℕ) ⊕ (Fin d → ℕ))` = `E_b × E_b` in rescaled coordinates; `xiCoord/etaCoord` are the rescaled unit-box families (`scale_toXi`), `toXi b/toEta b` the box families, `‖x‖ = mass ξ + mass η`, coordinates 1-Lipschitz, `ofFamilies` embeds weighted-summable pairs; canonical coefficient map `dataBoxCoeff` (L201) = `boxCoeff` of the box families, `= b^{|h|+d} (b^{2|k|})^{-μ} ∑_q familySpectralCoeff (xiCoord x) (etaCoord x) μ q C(q,j) log(b^{2|k|})^{q-j}` (L218); `taylorTree_data` | StochasticData.lean |



Review v28's guidance for A3 (verbatim): "A3 must add, rather than silently infer: measurable and sufficiently uniform control in the tangential variable; integrable domination or another justified mechanism for passing coefficient/remainder limits through tangential integration; a joint stochastic data model across charts when assembling random contributions; chart weights, coordinate-change factors, overlap handling, and the identity with the original global integral; appropriate summability or local-finiteness controls if chart assembly is not finite. The important boundary is that uniformity on fixed data balls does not by itself provide tangential domination or joint convergence across charts."

## The paper's §4.3 proof, the part A3 must formalise (verbatim from the source)

```latex
\begin{proof}
Starting with the integral,
\[
Z_n[\phi] = \int_W \phi(w)\, e^{-\beta n L_n(w)}\, \varphi(w)\, dw\,,
\]
We can factor out $e^{-\beta n L_n(w_0)}$, giving us 
\[
     Z_n[\phi]= e^{-\beta nL_n(w_0)}\int_W \phi(w)\, e^{-\beta n K_n(w)}\, \varphi(w)\, dw = e^{-\beta nL_n(w_0)}Z_n^0,
\]
where $Z_n^0$ is the normalised partition function. Decompose 
\[
    \int_W \phi(w)\, e^{-\beta n K_n(w)}\, \varphi(w)\, dw = Z^{(1)}_n[\phi] + Z^{(2)}_n[\phi],
\]
where
\begin{align*}
    Z^{(1)}_n[\phi] &:= \int_{K(w) < \varepsilon} \phi(w) e^{-\beta nK(w) + \beta\sqrt{n K(w)}\psi_n(w)} \varphi(w) dw, \\
     Z^{(2)}_n[\phi]&:=\int_{K(w) \geq \varepsilon} \phi(w) e^{-\beta nK(w) + \beta\sqrt{n K(w)}\psi_n(w)} \varphi(w) dw.
\end{align*}
First we treat $Z_n^{(2)}[\phi]$. If $K(w) \geq \varepsilon$, then 
\[
    \beta nK(w) - \beta\sqrt{n K(w)}\psi_n(w) \geq \frac{\beta}{2}\left(n\varepsilon -\sup_{K(w)\geq \varepsilon} |\psi_n(w)|^2\right).
\]
Since $\psi_n(w)$ is an empirical process which converges to a Gaussian process $G$ with supremum norm in distribution, then $\sup_{K(w)\geq \varepsilon} |\psi_n(w)|^2$ converges in distribution . Therefore for any $a' \in \mathbb{Q}_{>0}$ and $b' \in \mathbb{Z}$,
\[
    n^{a'}(\log n)^{1-b'}|Z^{(2)}_n[\phi]| \leq C n^{a'}(\log n)^{1-b'} e^{-\beta n \varepsilon /2} \exp\left(\frac{\beta}{2}\sup_{K(w)\geq \varepsilon} |\psi_n(w)|^2\right),
\]
for some $C >0$, which converges to zero in probability by \citep[Theorem 5.2]{greybook}. For $Z_n^{(1)}[\phi]$, we can pullback via the resolution $\pi$ giving us 
\[
     Z^0_n[\phi] = \sum_{I} Z_n[\beta;\xi_n,\eta;I] + R_n,
\]
where $R_n = o_p(e^{-\varepsilon' n})$ for some $\varepsilon' > 0$ is a random variable converging to zero in probability, and
\[
     Z_n[\beta;\xi_n,\eta; I] = \int_{S_I} \int_{[0,b]^{|I|}} \eta(v,u) u^{h_I} e^{-\beta nu^{2k_I}+\beta \sqrt{n}u^k\xi_n(u,v)}\,du\, \rho_I(v) dv.
\]
$\rho_I(v) \in C^\infty_0$ is a smooth partition of unity with compact support, $\xi_n$ is the empirical process (analytic function for each $n$) and $\eta(u,v) = \phi(u,v)c(u,v)$ incorporates the pullback of $\phi(w)$ and $\varphi(w)$. The multi-index $h_I$ collects the Jacobian exponents and observable vanishing orders, and $k_I$ records the resolution data of $K$. Now the integral 
\begin{align*}
    Z(\beta,n;\xi,\eta) := \int_{[0,b]^{|I|}} \eta(v,u) u^{h_I} e^{-\beta nu^{2k_I}+\beta \sqrt{n}u^{k_I}\xi(u,v)}\,du,
\end{align*}
where $\xi :[0,b]^d \to \mathbb{R}$ is a real analytic function, is a standard integral for fixed $v$. Applying \cref{cor:standardintegralexp} gives us the asymptotic expansion
\begin{align*}
    Z(\beta,n;\xi,\eta) &\sim \sum_{\mu \in \Lambda_I}\sum_{m=1}^d C_{\mu,m,I}(\xi,v) n^{-\mu}(\log n)^{m-1},
\end{align*}
where $\Lambda_I \subseteq \Lambda(h_I,k_I)$ as in \eqref{eq:candidateexponents}. The coefficients are 
\begin{align*}  
   C_{\mu,m,I}(\xi,v) &:=  \sum_{p\geq 0} \sum_{\substack{ \mathbf{m}\in \mathbb{N}^d, |\mathbf{n}|\geq p \,\\ \text{where }\mu\in\mathcal{P}_{\mathbf{m},\mathbf{n}}}}   \sum_{j=m}^{d}\binom{j-1}{m-1}\\
     &\quad \times \frac{\eta_{\mathbf{m}}(v)}{\mathbf{m}!} \frac{\xi_{\mathbf{n},p}(v)}{p!} c_{\mu,j}(-\partial_{\mu})^{j-m} \partial^p S_{\mu}(\xi(0,v)),
\end{align*}
where
\begin{align*}
    \xi_{\mathbf{n},p}(v) &:= \sum_{\substack{\gamma^{(1)}+\cdots+\gamma^{(p)} = \mathbf{n}\\|\gamma^{(j)}|\geq1}} \left(\prod_{i=1}^p  \frac{\partial_u^{(\gamma^{(i)})}\xi(u,v)|_{u=0}}{\gamma^{(i)}!}\right), \\
    \eta_{\mathbf{m}}(v) &:= \frac{\partial^{|\mathbf{m}|} \eta}{\partial u^{\mathbf{m}}}\bigg|_{u=0}.
\end{align*}
Applying to our per strata integral $Z_n[\beta,\xi_n,\eta;I]$ where $\xi:=\xi_n$ we have
\begin{align*}
    Z_n[\beta,\xi_n,\eta;I] &= \int_{S_I} Z(\beta,n;\xi_n,\eta) \rho_I(v)dv \\
    &\sim  \sum_{\mu \in \Lambda_I}\sum_{m=1}^{|I|} \left(\int_{S_I}C_{\mu,m,I}(\xi_n,v)dv\right)\, n^{-\mu}(\log n)^{m-1},\\
    &\sim \sum_{\mu \in \Lambda_I}\sum_{m=1} ^{|I|}\widetilde{C}_{\mu,m,I}(\xi_n) n^{-\mu}(\log n)^{m-1}.
\end{align*}
by \cref{lemma:AsymInt}. The integral over the strata $S_I$ converges since the partition of unity $\rho_I(v)$ has compact support and we defined 
\[
    \widetilde{C}_{\mu,m,I}(\xi_n) := \int_{S_I}C_{\mu,m,I}(\xi_n,v)dv.
\]
Therefore summing over the strata we have the asymptotic expansion 
\[
    Z^0_n[\phi] \sim \sum_I \sum_{\mu \in \Lambda_I}\sum_{m=1} ^{|I|}\widetilde{C}_{\mu,m,I}(\xi_n) n^{-\mu}(\log n)^{m-1}.
\]
Swapping the sums we have 
\[
    Z^0_n[\phi] \sim \sum_{\mu \in \Lambda^*}\sum_{m=1}^d C_{\mu,m} n^{-\mu}(\log n)^{m-1},
\]
where $\Lambda^* \subseteq \Lambda(h,k)$ and 
\[
    C_{\mu,m}(\xi_n)=\sum_{I} \widetilde{C}_{\mu,m,I}(\xi_n).
\]
Here the sum $\sum_I$ is taken over all the strata that achieve the exponent $\mu$ with multiplicity $m$. Now since $\xi_n, G \in C^\omega([0,b]^d)$, by \cref{prop:convergence}, $C_{\mu,m}(\xi)$ is a continuous function of $\xi$ and the convergence in distribution   $C_{\mu,m}(\xi_n) \to C_{\mu,m}(G)$ holds. For each fixed $(\mu',j')< (M,J)$, each coefficient is defined via 
\[
    C_{\mu',m'}(\xi_n) := \lim_{n\to\infty}\frac{1}{n^{-\mu'}(\log n)^{m' - 1}} \bigg\{ Z^0_n[\phi]  - \sum_{(\mu,m)<(\mu',m')} C_{\mu, m}(\xi_n)\, n^{-\mu} (\log n)^{m - 1} \bigg\}\,.
\]
Therefore
```

Note: `\cref{lemma:AsymInt}` is cited but has no statement in the source. The earlier normal-block programme has a **conditional finite chart assembly** for d = 2 (Headline XV deterministic, XVIII stochastic: an external chart decomposition `Z_n = ∑_I Z_n^{(I)} + o(...)` is a hypothesis; assembly takes min exponent / max log multiplicity; `ChartAssembly.lean`, `HeadlineAssembly.lean`, `HeadlineStochasticAssembly.lean`, `StochasticAssemblyInfra.lean`).

## What we have for A3
- Deterministic: `dataTaylorTree_cutoff_bound` (uniform on data balls, all `N` with `N b^{2|k|} ≥ 1`), `abs_orderedRemainder_sub_le` (explicit majorant `remainderMajorant n h k β b μ j R N`, independent of `x` on the ball, `→ 0`), `continuous_taylorTree_coeff` (Lipschitz on balls), `continuous_dataBoxIntegral` (Lipschitz on balls, fixed `N`).
- Probabilistic: Mathlib `TendstoInDistribution` (continuous mapping, Slutsky, portmanteau), `dataNormBounded_of_tendstoInDistribution`, `tendstoInMeasure_zero_of_uniform_on_balls'` (vector-valued).
- Mathlib: Bochner integral on finite measure spaces, `integral_finset_sum`, `norm_setIntegral_le_of_norm_le_const`, `ContinuousOn.integrableOn_compact`, `ContinuousMap` (`C(K, E)` with sup norm, compact `K`), `ContinuousMap.norm_le`, `Measurable` of `ContinuousMap.eval`.

## Questions

1. **Go/no-go on A3 now**, versus freezing Programme S at A1–A2 (a clean release: "the stochastic Taylor tree at chart level in every positive dimension, conditional on data convergence") and stopping. The user's standing instruction is to continue formalising the paper on auto, consulting you for direction. Give unit estimates and gates.

2. **Formal shape of `lemma:AsymInt` (deterministic).** Proposal: `K` a compact metric (or just a measurable) space with a finite measure `ν`; tangential data `x : K → DataSpace (n+1)` continuous (so `sup_v ‖x v‖ ≤ R` by compactness); then for each fixed `N`, `v ↦ Z(N; x v)` is continuous/measurable and bounded, `v ↦ C_{μ,j}(x v)` continuous; and `|∫_K Z(N; x v) dν − ∑_{Λ_L} N^{-μ} ∑_j (∫_K C_{μ,j}(x v) dν)(log N)^j| ≤ ν(K) · b^{|h|+d} dataCutoffConst(R) (N b^{2|k|})^{-L} (1+log(N b^{2|k|}))^n`, so the integrated integral has a Taylor-tree expansion with coefficients `∫_K C_{μ,j}(x v) dν` and the integrated ordered remainders converge to them. Is `C(K, DataSpace)` the right data type (sup-norm continuity in `v`), or should the hypothesis be weaker (measurable + uniformly bounded in `v`, with the coefficient integrability following from the ballwise bound)? How should the amplitude `η(u,v)` (deterministic, includes the partition of unity `ρ_I(v)`) and the phase `ξ_n(u,v)` enter — as one tangential data map `v ↦ (cξ(v), cη(v))`?

3. **Stochastic tangential version.** Hypothesis `X_n ⇒ X` in `C(K, DataSpace)` (a Polish space; the integrated coefficient map `x ↦ ∫_K C(x v) dν` is continuous on `C(K, DataSpace)` — Lipschitz on balls since `‖x v‖ ≤ ‖x‖_∞`), then continuous mapping + the uniform remainder argument on sup-norm balls give the analogue of XXXV for the stratum integral. Right shape? Pitfalls (measurability of `x ↦ ∫_K Z(N; x v) dν` on `C(K, DataSpace)`; Borel σ-algebra on `C(K, E)`; `TendstoInDistribution` in a non-locally-compact space is fine in Mathlib?).

4. **Finite chart assembly.** Charts `I ∈ Fin M` each with their own `(n_I, h_I, k_I, b_I)` and data spaces; the global `Z^0_n = ∑_I Z_I(n) + R_n` with `R_n = o_p(e^{-εn})` as an EXTERNAL hypothesis (as in Headlines XV/XVIII); the exponent set is the union of the lattices; coefficient of `n^{-μ}(log n)^j` is `∑_I C_{μ,j}^I` (zero where a chart's lattice does not contain `μ`); ordering across charts by the same `≺`. Should we (a) reuse the d=2 conditional assembly theorems (`ChartAssembly.lean`) generically, (b) write a new generic assembly over `Fin M` with heterogeneous chart types (dependent types: `Σ I, DataSpace (d I)`), or (c) fix a common ambient `d` and pad? What must the external decomposition hypothesis contain to make the ordered-remainder conclusion honest (quantified residual at every normalised scale)?

5. **A4 (posterior division) statement gate**: is there a small honest deliverable now (leading-order quotient `Z_n[φ]/Z_n[1] ⇒ C^φ_{μ₀,j₀}(Z)/C^1_{μ₀,j₀}(Z)` given the joint convergence of the two leading coefficients and a.s. nonvanishing of the limit denominator), and what exactly should be deferred?

6. **Order of the first 3 units of A3** and the stop criterion.
