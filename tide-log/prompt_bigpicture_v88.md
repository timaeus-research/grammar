# Consult #88 — programme C landed; audit and next direction

You are Astra, advising the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, Mathlib v4.33.1, 590 modules, no sorry/axioms) of the grammar paper (Gerraty–Murfet). Consult #87 designed programme C (statistical transfer). It has now landed in full: CCLXXXVII `PosteriorPerturbationTransfer` (C1), CCLXXXVIII `EmpiricalConcentration` (C2/C3 + coefficient consistency), CCLXXXIX `GibbsJointRatio` (C4). The abstract joint ratio theorem already existed in the library (`tendstoInDistribution_div` in `QuotientInDistribution.lean`, with the normal-crossing specialisation `tendstoInDistribution_posterior_scales`); CCLXXXIX specialises it to the Gibbs numerator/normaliser and adds the bounded-observable expectation corollary and the degenerate-ratio-law consequence. The semantic audit (E) of the paper mirror found no changes needed. Below are the exact Lean statements and the new mirror paragraph.

## Questions
1. Audit: are the statements below correct and honestly scoped? Point out any hypothesis that is silently stronger/weaker than the paper's intent, any misleading name, and any place where the mirror paragraph overclaims.
2. Programme D (exact constant-unit kernel log-polynomial) was marked optional. Given what has landed, is it worth one or two units? If yes, give the precise statement(s) and proof route; if not, say so.
3. Is there any remaining theorem of genuinely high value for the paper (resolved-space programme, statistical transfer, or elsewhere in §3/§4) that the library does not yet contain, given the full list of headline units I–CCLXXXIX? If the honest answer is that the formalisation should close at this point, say that plainly. Prefer at most three concrete candidates, ranked, each with a statement, a proof sketch against Mathlib, and an estimate of size.

## Lean statements (verbatim)
```lean
-- EmpiricalConcentration.lean (namespace Grammar.Gibbs)
-- ==== Grammar/EmpiricalConcentration.lean
variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]

variable {K Kh : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKhm : Measurable Kh)
  {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {K : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {K Kh : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKhm : Measurable Kh)
  {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π] [NeZero π]
  {K : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

variable {W : Type*} [MeasurableSpace W] (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hπS : ∀ᵐ w ∂π, w ∈ S) {K Kh φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
  (hKhm : Measurable Kh) (hφm : Measurable φ) {e : ℝ} (he : ∀ w, |Kh w - K w| ≤ e)

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)
  (Kh : ℕ → W → ℝ) (hKhm : ∀ n, Measurable (Kh n))
  (hunif : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n w - K w| ≤ ε)

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)

noncomputable def normaliser (Kh : W → ℝ) (n : ℝ) : ℝ := ∫ w, Real.exp (-n * Kh w) ∂π

/-- The Gibbs mass of a set `E`: `∫_E e^{−n K̂} dπ / Ẑ`. -/
noncomputable def mass (Kh : W → ℝ) (n : ℝ) (E : Set W) : ℝ

noncomputable def expectation (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ

theorem integrable_exp {n : ℝ} (hn : 0 ≤ n) :
    Integrable (fun w => Real.exp (-n * Kh w)) π

theorem setIntegral_exp_ge_le {κ n : ℝ} (hn : 0 ≤ n) :
    ∫ w in {w | κ ≤ K w}, Real.exp (-n * Kh w) ∂π ≤ π.real univ * Real.exp (-n * (κ - e))

theorem normaliser_ge {a n : ℝ} (hn : 0 ≤ n) :
    π.real {w | K w < a} * Real.exp (-n * (a + e)) ≤ normaliser π Kh n

theorem gibbsMass_ge_le {κ a n : ℝ} (hn : 0 ≤ n) (ha : 0 < π.real {w | K w < a}) :
    mass π Kh n {w | κ ≤ K w} ≤
      π.real univ / π.real {w | K w < a} * Real.exp (-n * (κ - a - 2 * e))

theorem tendsto_gibbsMass_ge {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => mass π (Kh n) n {w | κ ≤ K w}) atTop (𝓝 0)

theorem ae_tendsto_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
    (hunif : ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n ω w - K w| ≤ ε)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => mass π (Kh n ω) n {w | κ ≤ K w}) atTop (𝓝 0)

theorem tendsto_measure_gibbsMass_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
    (hunif : ∀ ε > 0,
      Tendsto (fun n : ℕ => P {ω | ¬ ∀ w, |Kh n ω w - K w| ≤ ε}) atTop (𝓝 0))
    {κ : ℝ} (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P {ω | δ ≤ mass π (Kh n ω) n {w | κ ≤ K w}}) atTop (𝓝 0)

theorem normaliser_le_normaliser {n : ℝ} (hn : 0 ≤ n) :
    Real.exp (-n * e) * normaliser π K n ≤ normaliser π Kh n ∧
      normaliser π Kh n ≤ Real.exp (n * e) * normaliser π K n

theorem abs_log_normaliser_sub_le [NeZero π] {n : ℝ} (hn : 0 ≤ n) :
    |Real.log (normaliser π Kh n) - Real.log (normaliser π K n)| ≤ n * e

theorem tendsto_log_normaliser_div
    (hZ : Tendsto (fun n : ℕ => Real.log (normaliser π K n) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (normaliser π (Kh n) n) / n) atTop (𝓝 0)

theorem exists_sublevel_of_eq_on_zeroSet {W : Type*} [TopologicalSpace W] [T2Space W]
    {S : Set W} (hS : IsCompact S) {K φ : W → ℝ} (hKc : ContinuousOn K S)
    (hφc : ContinuousOn φ S) (hK0 : ∀ w ∈ S, 0 ≤ K w) {φ₀ : ℝ}
    (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ > 0, ∀ w ∈ S, K w < κ → |φ w - φ₀| < ε

theorem abs_expectation_sub_le {φ₀ ε B κ n : ℝ} (hn : 0 ≤ n) (hZ : 0 < normaliser π Kh n)
    (hεS : ∀ w ∈ S, K w < κ → |φ w - φ₀| ≤ ε) (hBS : ∀ w ∈ S, |φ w - φ₀| ≤ B) (hε : 0 ≤ ε) :
    |expectation π Kh n φ - φ₀| ≤ ε + B * mass π Kh n {w | κ ≤ K w}

theorem tendsto_expectation_of_eq_on_zeroSet :
    Tendsto (fun n : ℕ => expectation π (Kh n) n φ) atTop (𝓝 φ₀)

theorem tendsto_expectation_of_eq_on_zeroSet_population :
    Tendsto (fun n : ℕ => expectation π K n φ) atTop (𝓝 φ₀)

theorem coeff_eq_of_eq_on_zeroSet {a : ℕ → ℝ} {c₁ cφ : ℝ} (hc₁ : 0 < c₁)
    (h₁ : Tendsto (fun n : ℕ => a n * normaliser π K n) atTop (𝓝 c₁))
    (hφ : Tendsto (fun n : ℕ => a n * ∫ w, φ w * Real.exp (-(n : ℝ) * K w) ∂π) atTop (𝓝 cφ)) :
    cφ = φ₀ * c₁

theorem coeff_eq_of_hasLeadingTerm {c₁ cφ lam : ℝ} {k : ℕ} (hc₁ : 0 < c₁)
    (h₁ : HasLeadingTerm (fun N => normaliser π K N) c₁ lam k)
    (hφ : HasLeadingTerm (fun N => ∫ w, φ w * Real.exp (-N * K w) ∂π) cφ lam k) :
    cφ = φ₀ * c₁

-- ==== Grammar/GibbsJointRatio.lean
variable {W : Type*} [MeasurableSpace W] (π : Measure W)

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
  [l.IsCountablyGenerated]

variable {W : Type*} [TopologicalSpace W] [T2Space W] [MeasurableSpace W]
  (π : Measure W) [IsFiniteMeasure π]
  {S : Set W} (hS : IsCompact S) (hπS : ∀ᵐ w ∂π, w ∈ S)
  {K φ : W → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K) (hKc : ContinuousOn K S)
  (hφm : Measurable φ) (hφc : ContinuousOn φ S)
  (hpos : ∀ a, 0 < a → 0 < π.real {w | K w < a})
  {φ₀ : ℝ} (hφ0 : ∀ w ∈ S, K w = 0 → φ w = φ₀)
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  (Kh : ℕ → Ω → W → ℝ) (hKhm : ∀ n ω, Measurable (Kh n ω))
  (hunif : ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ w, |Kh n ω w - K w| ≤ ε)

noncomputable def numerator (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) : ℝ

theorem expectation_eq_div (Kh : W → ℝ) (n : ℝ) (φ : W → ℝ) :
    expectation π Kh n φ = numerator π Kh n φ / normaliser π Kh n := rfl

theorem normaliser_nonneg (Kh : W → ℝ) (n : ℝ) : 0 ≤ normaliser π Kh n

theorem abs_numerator_le {Kh φ : W → ℝ} {n M : ℝ} (hM : ∀ w, |φ w| ≤ M)
    (hI : Integrable (fun w => Real.exp (-n * Kh w)) π) :
    |numerator π Kh n φ| ≤ M * normaliser π Kh n

theorem abs_expectation_le {Kh φ : W → ℝ} {n M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, |φ w| ≤ M)
    (hI : Integrable (fun w => Real.exp (-n * Kh w)) π) :
    |expectation π Kh n φ| ≤ M

theorem tendstoInDistribution_expectation (Kh : ι → Ω → W → ℝ) (n : ι → ℝ) (φ : W → ℝ)
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hNm : ∀ i, Measurable fun ω => numerator π (Kh i ω) (n i) φ)
    (hZm : ∀ i, Measurable fun ω => normaliser π (Kh i ω) (n i))
    (Lφ L1 : Ω' → ℝ) (hLφm : Measurable Lφ) (hL1m : Measurable L1)
    (hjoint : TendstoInDistribution
      (fun i ω => (a i * numerator π (Kh i ω) (n i) φ, a i * normaliser π (Kh i ω) (n i))) l
      (fun ω => (Lφ ω, L1 ω)) (fun _ => μ) μ')
    (hL1 : μ' {ω | L1 ω = 0} = 0) :
    TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) l
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ'

theorem tendsto_integral_expectation {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ w, |φ w| ≤ M)
    (hI : ∀ i ω, Integrable (fun w => Real.exp (-n i * Kh i ω w)) π)
    (hEm : ∀ i, Measurable fun ω => expectation π (Kh i ω) (n i) φ) {Lφ L1 : Ω' → ℝ}
    (h : TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) atTop
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ') :
    Integrable (fun ω => Lφ ω / L1 ω) μ' ∧
      Tendsto (fun i => ∫ ω, expectation π (Kh i ω) (n i) φ ∂μ) atTop
        (𝓝 (∫ ω, Lφ ω / L1 ω ∂μ'))

theorem ae_div_eq_of_ae_tendsto {Kh : ℕ → Ω → W → ℝ} {n : ℕ → ℝ} {φ : W → ℝ}
    (hEm : ∀ i, Measurable fun ω => expectation π (Kh i ω) (n i) φ) {Lφ L1 : Ω' → ℝ}
    (h : TendstoInDistribution (fun i ω => expectation π (Kh i ω) (n i) φ) atTop
      (fun ω => Lφ ω / L1 ω) (fun _ => μ) μ') {φ₀ : ℝ}
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun i => expectation π (Kh i ω) (n i) φ) atTop (𝓝 φ₀)) :
    ∀ᵐ ω ∂μ', Lφ ω / L1 ω = φ₀

theorem ae_tendsto_expectation_of_eq_on_zeroSet :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => expectation π (Kh n ω) n φ) atTop (𝓝 φ₀)

theorem ae_div_eq_of_eq_on_zeroSet (a : ℕ → ℝ) (ha : ∀ i, a i ≠ 0)
    (hNm : ∀ i, Measurable fun ω => numerator π (Kh i ω) i φ)
    (hZm : ∀ i, Measurable fun ω => normaliser π (Kh i ω) i)
    (Lφ L1 : Ω' → ℝ) (hLφm : Measurable Lφ) (hL1m : Measurable L1)
    (hjoint : TendstoInDistribution
      (fun i ω => (a i * numerator π (Kh i ω) i φ, a i * normaliser π (Kh i ω) i)) atTop
      (fun ω => (Lφ ω, L1 ω)) (fun _ => μ) μ')
    (hL1 : μ' {ω | L1 ω = 0} = 0) :
    ∀ᵐ ω ∂μ', Lφ ω / L1 ω = φ₀

```

## New mirror paragraph (grammar_lean.tex, remark rem:pop_vs_emp)

\emph{Lean (statistical transfer: what passes from the population posterior to the empirical one, and what does not).} Three statements about the empirical posterior $\hat\mu_n$ are formalised; each is a hypothesis-carrying transfer, none identifies the empirical coefficients with the population ones. (a) \emph{Perturbation.} For a reference probability measure $\mu$ (the population posterior), a nonnegative reweighting $R$ (the empirical-to-population density ratio) and a scalar $A>0$ with $\delta=\int|R/A-1|\,d\mu<1$, every observable with $|\phi|\le M$ has $|\hat\mu(\phi)-\mu(\phi)|\le 2M\delta/(1-\delta)$ for the tilted expectation $\hat\mu(\phi)=\int\phi R\,d\mu/\int R\,d\mu$ [dot: abs\_tiltedExpectation\_sub\_le]; the smallness of $\delta$ is the interface, and it is \emph{not} a consequence of a law of large numbers (the empirical fluctuation survives at order one on the shrinking neighbourhoods of $W_0$, so for general observables the empirical coefficient differs from the population one, as in (ii) above). (b) \emph{Concentration.} If the empirical phase $\hat K_n$ is uniformly within $e$ of $K\ge0$ on the support of a finite prior $\pi$, then for $0<a<\kappa$ the empirical posterior mass of $\{K\ge\kappa\}$ is at most $(\pi(W)/\pi\{K<a\})\,e^{-n(\kappa-a-2e)}$ [dot: Gibbs.gibbsMass\_ge\_le], so under a uniform law of large numbers (taken as a hypothesis, almost surely or in probability) the empirical posterior concentrates on every neighbourhood of $W_0$, and $\tfrac1n\log Z_n[1]\to0$ transfers from the population to the empirical normaliser [dot: Gibbs.tendsto\_log\_normaliser\_div]. For an observable continuous on a compact support and equal to a constant $\phi_0$ on $W_0$, the empirical posterior expectation converges to $\phi_0$ [dot: Gibbs.tendsto\_expectation\_of\_eq\_on\_zeroSet], and, by uniqueness of limits, population leading-term certificates for $\mathcal Z_n[\phi]$ and $\mathcal Z_n[1]$ at a common pair with $c_1>0$ have $c_\phi=\phi_0c_1$ [dot: Gibbs.coeff\_eq\_of\_hasLeadingTerm]. (c) \emph{Joint ratio.} If the pair $(a_nZ_n[\phi],a_nZ_n[1])$ converges jointly in distribution to $(L_\phi,L_1)$ with $\mathbb P(L_1=0)=0$, then $\hat\mu_n(\phi)=Z_n[\phi]/Z_n[1]$ converges in distribution to $L_\phi/L_1$ [dot: Gibbs.tendstoInDistribution\_expectation] (marginal convergence of numerator and normaliser is insufficient), with convergent expectations $\mathbb E[\hat\mu_n(\phi)]\to\mathbb E[L_\phi/L_1]$ for bounded $\phi$ [dot: Gibbs.tendsto\_integral\_expectation]; for a constant-on-minimisers observable under an almost-surely uniform law of large numbers every such joint limit has the degenerate ratio law $L_\phi/L_1=\phi_0$ almost surely [dot: Gibbs.ae\_div\_eq\_of\_eq\_on\_zeroSet]. The three quantities $\mathbb E[L_\phi/L_1]$, $\mathbb E L_\phi/\mathbb E L_1$ and the population ratio $c_\phi/c_1$ are distinct in general; the joint limit law itself (a field central limit theorem for the empirical process on the resolved space) is not derived here, and the uniform convergence of the empirical phase is a hypothesis throughout.

## Headline index (titles only)
CCXX | weighted tube densities — the fibre integration chain carries a density factor (u538; Astra #74 module 3, prerequisite for the resolved-space programme)
CCLXXXIX | ★★ THE JOINT RATIO THEOREM FOR EMPIRICAL GIBBS EXPECTATIONS (u607; consult #87, C4)
CCLXXXVIII | ★★ CONCENTRATION OF THE EMPIRICAL GIBBS POSTERIOR NEAR THE ZERO SET (u606; consult #87, C2/C3)
CCLXXXVII | ★ THE ABSTRACT PERTURBATION TRANSFER FOR REWEIGHTED POSTERIORS (u605; consult #86, C1)
CCLXXXVI | ★★ THE SEPARABLE-BALL REGRESSION (u604; consult #86, B3)
CCLXXXV | ★ COEFFICIENT LOCALITY AND SMALL-BALL RADIUS INDEPENDENCE (u603; consult #86, B)
CCLXXXIV | ★★★ THE BLOW-UP COEFFICIENT OF THE UNIT CUBE IS `π^{d/2}` (u602; consult #86, A4)
CCLXXXIII | ★★ ONE BLOW-UP SUFFICES: THE UNIT CUBE IN EVERY DIMENSION (u601; consult #86, A3)
CCLXXXII | ★★ BOUNDARY-COMPATIBLE BOX ASSEMBLIES: DERIVED CERTIFICATES (u600; consult #86, A2)
CCLXXXI | ★★ THE WHOLE-BOX SOURCE CERTIFICATE (u599; consult #86, A1)
CCLXXX | ★ THE BLOW-UP SQUARE REGRESSION (u598; consult #85 unit 7, checked in #86)
CCLXXIX | ★★ THE CERTIFIED RESOLUTION THEOREM FOR THE EXPLICIT COEFFICIENT (u597; consult #85 unit 6)
CCLXXVIII | ★★ ASSEMBLY OVER ALMOST-EVERYWHERE DISJOINT CHART IMAGES (u596; consult #85 unit 5)
CCLXXVII | ★ COMPACT SOURCE LOCALISATION ON A MONOMIAL CHART (u595; consult #85 unit 4)
CCLXXVI | ★★ CERTIFIED SOURCE DECOMPOSITIONS HAVE AN EXPLICIT POSITIVE LEADING COEFFICIENT (u594; consult #85 unit 3)
CCLXXV | ★ THE ZERO-COMPATIBLE EXPANSION OF A SOURCE-WEIGHTED ONE-CHART INTEGRAL (u593; consult #85 unit 2)
CCLXXIV | THE PIECE BRIDGE WITH A SOURCE AMPLITUDE (u592; consult #85 unit 2)
CCLXXIII | NEGLIGIBLE REMAINDERS (u591; consult #85 unit 1)
CCLXXII | TWO-CHART PARTITION REGRESSION (u590; consult #84 unit 5)
CCLXXI | ★★ THE EXPLICIT LEADING COEFFICIENT OF THE BOX INTEGRAL OF A MONOMIAL CHART AT A DIVISOR POINT (u589; consult #84 unit 4)
CCLXX | ★ the local product box of a monomial chart at a divisor point (u588; consult #84 units 2–3)
CCLXIX | ★★ partition assembly without the active-chart hypothesis (u587; consult #84 unit 1)
CCLXVIII | ★ the residual regression end to end with a nontrivial posterior (u586; consult #83 unit 5)
CCLXVII | ★ the residual face formula in chart data for variable-unit product charts (u585; consult #83 unit 4)
CCLXVI | consequences of a positive leading term: two-sided bounds and the free energy with its constant (u584; consult #83 unit 3)
CCLXV | ★★ ASSEMBLY ALONG A SUPPLIED PARTITION OF UNITY — R3 (u583; consult #83 unit 2)
CCLXIV | localisation by a supplied partition of unity (u582; consult #83 unit 1, R3 step 1)
CCLXIII | ★ compatibility: the variable-unit theorem specialises to the scalar one, coefficient included (u581; consult #82 Q3)
CCLXII | ★ end-to-end regression with a unit depending on all coordinates (u580; consult #82 "B-full")
CCLXI | ★ posterior limit and tied strata for product charts with normal-dependent units (u579; consult #82 unit 4C)
CCLX | ★★ PRODUCT CHARTS WITH NORMAL-DEPENDENT UNITS — `unit_indep` REMOVED FROM THE HEADLINE THEOREMS (u578; consult #82 unit 4B)
CCLIX | variable-unit piece atlases — the chart–stratum bridge WITHOUT normal-independence of the unit (u577; consult #82 unit 4A)
CCLVIII | the abstract leading atlas (u576; consult #82 prelude)
CCLVII | variable-unit cell regressions (u575; consult #82 "B-small")
CCLVI | variable-unit cells (u574; consult #81 unit 3)
CCLV | ★★ THE VARIABLE-UNIT CERTIFICATE — the phase unit may depend on the normal coordinates (u573; consult #81 unit 2b, Astra's range comparison)
CCLIV | the variable-unit box kernel (u572; consult #81 unit 2a)
CCLIII | range partitions of a positive unit and the approximate squeeze (u571; consult #81 unit 1 — the analytic helpers for removing the normal-independence of the phase unit)
CCLII | ★ the posterior expectation `E_N[y₀²] → 1/5` in the `x²y⁴` example (u570; consult #80 unit 2, posterior check)
CCLI | ★ the unequal-exponent regression example `∫_{[−1,1]²} e^{−N x²y⁴} dy ~ 2Γ(1/4) N^{−1/4}` (u569; consult #80 unit 2)
CCL | the residual-face coefficient of a scalar-unit cell (u568; consult #79 unit 4 in the form of consult #80)
CCXLIX | ★ one-chart covers and the regression example `∫_{[−1,1]²} e^{−N x²y²} dy ~ √π N^{−1/2} log N` (u567; consult #79 unit 5)
CCXLVIII | tied strata of a cover of product charts and the all-minimal coefficient formula (u566; consult #79 unit 3)
CCXLVII | ★★ THE LEADING-ORDER POSTERIOR EXPECTATION FOR A COVER OF PRODUCT CHARTS (u565; consult #79 unit 2)
CCXLVI | abstract posterior transfer (u564; consult #79 unit 1)
CCXLV | ★★ THE IDENTIFIED LEADING PAIR OF A COVER OF PRODUCT CHARTS — positivity of the total coefficient (u563; consult #78 unit 5b, completes the #78 plan)
CCXLIV | nonnegativity of every scalar-unit cell coefficient and the exposed cells of a product-chart piece (u562; consult #78 unit 5a)
CCXLIII | the extremal pair of a cover of product charts (u561; consult #78 unit 4)
CCXLII | the uniform piece atlases of a product chart and the END-TO-END leading-term theorem (u560; consult #78 units 2–3)
CCXLI | product chart geometry and the hypothesis package for the end-to-end theorem (u559; consult #78 unit 1)
CCXL | unrestricted certificate ratios and signed symmetric moments (u558; consult #77 unit 5 — completes the #77 plan)
CCXXXIX | positive leading coefficients (u557; consult #77 unit 4)
CCXXXVIII | the scalar-unit atlas of a chart–stratum piece from monomial-chart data (u556; consult #77 unit 3 — the first concrete constructor of the conditional theorems' hypotheses)
CCXXXVII | compact bases and product-domain allocations for adapted piece densities (u555; consult #77 unit 2)
CCXXXVI | the scalar normal form of a monomial phase on a stratum (u554; consult #77 unit 1)
CCXXXV | normal moments of the box kernel — exponent shift and certificate ratios (u553; consult #76 unit D)
CCXXXIV | the face coefficient and decomposition-independence (u552; consult #76 units 4–5)
CCXXXIII | the bridge from an adapted piece in scalar normal form to a scalar-unit atlas (u551; consult #76 unit 3 — the first concrete constructor of the conditional theorems' hypotheses)
CCXXXII | two-sided assembly and scalar-unit cells (u550; consult #76 unit B)
CCXXXI | the box kernel with a tangentially varying scalar phase unit (u549; consult #76 unit A)
CCXXX | finite constant-unit atlases and the conditional global leading coefficient (u548; Astra #75 modules 4–6 with the cells of CCXXIX)
CCXXIX | the constant-unit box kernel over a compact base — pointwise certificates, a uniform eventual bound, the integrated certificate (u547; Astra #75 module 2, constant-unit version)
CCXXVIII | adapted product densities on chart–stratum pieces (u546; Astra #75 module 1)
CCXXVII | integrating fibrewise leading terms over a base (u545; Astra #75 module 3)
CCXXVI | the divisor-free pieces are negligible at every power–log scale (u544; closes the `O(e^{−nε})` remainder of eq:localisation in chart form)
CCXXV | the leading-coefficient interface over chart–stratum pairs (u543; Astra #74 module 7)
CCXXIV | the global weighted expansion over resolution charts — the exact resolved-chart formula and the chart–stratum decomposition (u542; Astra #74 module 6)
CCXXIII | the coordinate-size stratification of a chart and the per chart–stratum formula (u541; Astra #74 modules 4–5)
CCXXII | coordinate planes as analytic LCI strata — the divisor strata of a chart (u540; Astra #74 module 2)
CCXXI | the model coordinate plane as an analytic LCI stratum with strucdual's tube of every radius (u539; Astra #74 module 2, model case)
CCXIX | the per-stratum formula on the whole tube of a compact stratum (u537; Astra #73 unit 3, genuine globalisation — assembly)
CCXVIII | `eq:per_stratum_expansion_coordfree` on strucdual's tube — the pushforward form (u536; Astra #73 unit 3)
CCXVII | `eq:tubular_expansion` coordinate-free on strucdual's tube (u535; Astra #73 unit 3, easy bridge)
CCXVI | the Taylor–moment expansion on the actual tube, and the zero-section Jacobian (u534; Astra #73 units 3-easy/4)
CCXV | integration along the fibres of the tube (u533; Astra #73 unit 2)
CCXIV | the tubular change of variables with its Jacobian density (u532; Astra #73 unit 1)
CCXIII | the global analytic tubular equivalence of a compact analytic LCI stratum (u531)
CCXII | the local tubular equivalence is real-analytic (u530)
CCXI | the lifted foot from strucdual's analytic tube — the local tubular equivalence is unconditional for compact analytic LCI strata (u529)
CCX | the local expansion is supported on the chart's candidate lattice (u528)
CCIX | THE SMALL-BALL LAPLACE EXPONENT PAIR IS THE RESOLUTION PAIR (u524; Astra #71 targets (ii)+(iii))
CCVIII | THE RESOLUTION FORMULA FOR THE EXPONENT, UNCONDITIONAL (u523; the support condition removed by tangential Jacobian weights, Astra #71 confirmed)
CCVII | THE EXPONENT OF A MONOMIAL RESOLUTION — the finite local cover exists (u521; discharges the cover hypothesis of CCVI for hironaka's partial resolutions with supported Jacobian exponents)
CCVI | the global exponent from local leading terms, conditional on a local cover (u520; Astra #70 route D)
CCV | THE IDENTIFIED LEADING TERM at a divisor point of a hironaka chart (u519; Astra #70 route C)
CCIV | THE LOCAL THEOREM AT A DIVISOR POINT OF A HIRONAKA CHART, unconditional (u518; the chart-level endpoint of the geometric bridge)
CCIII | the orthant charts of a centred hironaka chart are split box charts (u517; towards the chart-level theorem)
CCII | the centred split normal form of a hironaka chart at a divisor point (u516; towards the chart-level theorem)
CCI | reflections of the normal coordinates along a splitting (u515; towards the chart-level theorem)
CC | positive box charts along a splitting, and the abstract core tiling (u514; towards the chart-level theorem)
CXCIX | analytic units of a hironaka monomial chart (u512; towards the chart-level local theorem)
CXCVIII | the local unconditional single-chart expansion (u511; Astra #69 B1 completed)
CXCVII | the single-chart theorem with an analytic unit — the strip-normalised box (u510; Astra #69 B1)
CXCVI | the two-sided exact-monomial box — reflections as tiling pieces (u509; Astra #69 B0, orthants)
CXCV | the unconditional expansion of an exact-monomial box integral — first endpoint of the geometric bridge (u508; Astra #69 B0)
CXCIV | the exact-normal tiling interface and the conditional bridge (u507; Astra #68 unit 4b)
CXCIII | the core presentation of a positive-orthant exact box chart (u506; Astra #68 unit 7a)
CXCII | the tangential datum of a jointly analytic amplitude (u505; Astra #68 unit 6c)
CXCI | monomial coefficients of a real power series — the analytic amplitude as a point of the coefficient space (u504; Astra #68 unit 6a)
CXC | exact-monomial rectangular extraction — the tiling of a box into monomial cores (u503; Astra #68 unit 4a)
CLXXXIX | compact-strip normalisation of the unit-removal rescaling (u502; Astra #68 unit 3)
CLXXXVIII | parity and sign of a nonnegative monomial chart (u501; Astra #67 unit 2b, #68 unit 3)
CLXXXVII | exact unit removal — the local analytic normal form of a monomial chart (u500; Astra #67 unit 2)
CLXXXVI | analytic core presentations — the certificate the geometry can supply (u499; Astra #67 unit 1)
CLXXXV | the population Laplace exponent pair, unconditionally — hironaka's chart form is complete (u498; hironaka bumped `aa4087e` → `eb9b6ca`, 356/356 leaves, `Q_all` axiom-clean)
CLXXXIV | closure endpoints for the empirical chain (u497; Astra #66 units 3 and 5 — interface obligations from the closure audit)
CLXXXIII | the effective-temperature corollary and the normal-location check (u496; Astra #62 unit 5)
CLXXXII | the sub-Gaussian empirical programme — the boundedness of CLXII–CLXV replaced by the coordinate certificate plus a uniform full-box scalar sub-Gaussian hypothesis (u493–u495; Astra #62 units 2–4)
CLXXXI | sampling/core compatibility — the release gate of the companion note (u492; Astra #62 unit 1)
CLXXX | the conditional tubular equivalence (u491; Astra #65 unit 4 = Astra #64 unit 14 in conditional form)
CLXXIX | the labelled normal bundle as the Riesz image of the conormal splitting, and the geometric identification adapter (u490; Astra #65 units 2–3)
CLXXVIII | the normal bundle of a coordinate stratum and its tubular equivalence (u489; Astra #64 units 14–15, coordinate case)
CLXXVII | global normal sections — the "global section" clauses of `defn:normal_diff` and `lem:normal_deriv` (u488; Astra #64 unit 13)
CLXXVI | the normal bundle of labelled defining equations — `eq:decomp_nx` at bundle level (u487; Astra #64 units 11–12; claims tightened per Astra #65 unit 1)
CLXXV | frame atlases from frames and coframes (u486; Astra #64 unit 10)
CLXXIV | the normal bundle from local frames (u485; Astra #64 unit 9)
CLXXIII | the StrucDual realisation of the chosen normal family (u484; Astra #64 unit 8; strucdual bumped to Mathlib v4.33.1 and made a lake dependency)
CLXXII | certified finite box reduction and the grammar application — the coordinate-free expansion of the resolved integral (u483; Astra #63 unit 7)
CLXXI | the coordinate-free Taylor–moment expansion — corrected identity versions of `eq:per_stratum_expansion_coordfree` and `eq:tubular_expansion` (u482; Astra #63 unit 6)
CLXX | weighted fibre integration and dressed moments — measure forms of `eq:pushforward_char`, `eq:pushforward_local`, `eq:tubular_cov`, `eq:dressed_moment` (u481; Astra #63 unit 5)
CLXIX | normal-fibre moments and the invariant contraction — `eq:moment_tensor_defn` and the boxed bridge (u480; Astra #63 unit 4)
CLXVIII | symmetric weight decomposition and the factorial bridge — `eq:decomp_sym_nx` and the completion of `lem:normal_deriv` (u479; Astra #63 unit 3)
CLXVII | fibrewise conormal exactness and the labelled line splitting `eq:decomp_nx` (u478; Astra #63 unit 2)
CLXVI | chosen-normal Taylor forms and frame covariance — the coordinate-free normal differential (u477; Astra #63 unit 1, `defn:normal_diff` + full-form part of `lem:normal_deriv`)
CLXV | the Gaussian first moment of the leading coefficient at the `ℓ¹` Gaussian limit — `E L` identified (u476; Astra #61 unit 3, second deliverable)
CLXIV | continuous linear functionals of the `ℓ¹` Gaussian limit are Gaussian (u475; Astra #61 unit 3, first deliverable)
CLXIII | the joint field limit for the sample datum and the assembled annealed sample-datum theorem (u474; Astra #61 units 1–2, 4 — several charts)
CLXII | the field limit for the sample datum and the single-chart annealed sample-datum theorem (u473; Astra #61 units 1–2, 4 — single chart)
CLXI | the full-box exponential-moment bound for the sample datum — Hoeffding (u472)
CLX | the reduced-temperature population bound is a theorem (u471; Astra #60 'how to discharge the deterministic bound')
CLIX | the Gaussian adapter from mean/covariance certificates (u470; Astra #60 unit 4, beyond its cap)
CLVIII | the bilocal integral on the critical line (u469; Astra #60 unit 5)
CLVII | the expectation assembly for certified sub-Gaussian cores (u468; Astra #60 unit 3 — the campaign's objective)
CLVI | uniform moments of the certified box model from the population mass at a reduced temperature (u467; Astra #60 unit 2)
CLV | uniform moments of exponential integrals against deterministic finite-`n` weights (u466; Astra #60 unit 1)
CLIV | conditional identification of the exponent pair with the population Laplace order (u465; Astra #59 unit 4)
CLIII | the Gaussian Banach-law adapter — Fernique discharges the sup-norm moment (u464; Astra #59 unit 1A)
CL | the annealed compact-base denominator: exact first moment, divergence, uniform moments (u461; Astra #59 unit 2)
CXLIX | uniform `p`-th moments of the leading compact-base coefficient from pointwise exponential moments (u460; Astra #59 unit 3 — the campaign's central bridge)
CXLVIII | conditional empirical assembly at the scale `A_n = n^λ/(log n)^{m−1}` (u459; Astra #58 unit 6)
CXLVII | strict `p`-moment thresholds (u458; Astra #58 unit 5)
CXLVI | sharp Gaussian bounds on the fluctuation function (u457; Astra #58 unit 5, part 1)
CXLV | compact base II — the Gaussian identities on the compact base (u456; Astra #58 unit 4 complete)
CXLIV | compact base II — finite reduction and the Gaussian field record (u455; Astra #58 unit 4, part 2)
CXLIII | the Gaussian quartet with a general covariance diagonal (u454; Astra #58 unit 4, part 1)
CXLII | compact base I — the covariance kernel, `Q`, `V`, and partition-independent bounds (u453; Astra #58 unit 3, completed)
CXLI | compact base I — finite quantisation and partition-independent bounds (u452; Astra #58 unit 3)
CXL | the exact-core adapter (u451; Astra #58 unit 1)
CXXXIX | the expected positive-gap remainder from annealed exponential moments (u450; Astra #58 unit 2)
CXXXVIII | cover assembly modulo a positive-gap remainder (u449; Astra #57 unit 5)
CXXXVII | tangential certificates from a joint torus envelope, and the reconstructed amplitude is the chart function (u448; Astra #57 unit 4)
CXXXVI | tangential/normal splitting of the weighted box (u447; Astra #57 unit 3 = A2, Astra #55 unit 5)
CXXXV | the positive-gap remainder for the empirical phase (u446; Astra #57 unit 2 = A3)
CXXXIV | the Gaussian-limit denominator and the dataset expectation bridge (u444–445; Astra #57 unit 1)
CXXXIII | covariance interpolation for the expected log-evidence (u443; Astra #56 unit 8)
CXXXII | divergence of the bilocal integral above threshold (u442; Astra #56 unit 7, completed off the critical line)
CXXXI | the cross-pairing series of the bilocal two-point function (u441; Astra #56 unit 7, second half)
CXXX | the bilocal two-point function `E₊[S_λ(G_i) S_λ(G_j)]` (u440; Astra #56 unit 7, first half)
CXXIX | the `Q = 0, 1, 2` insertion formulas via the tilted moment generating function (u438–439; Astra #56 unit 6)
CXXVIII | the exact annealed identity (u437; Astra #56 unit 10)
CXXVII | the sampling identity and the variance normalisation on the divisor (u435–436; Astra #56 A1 and unit 5)
CXXVI | the self-normalised Gaussian quartet at finite resolution (u430–434; Astra #56 units 1–4)
CXXV | the hironaka adapter and the orthant reflection (u428–429; Astra #55 unit 4 and the integration layer)
CXXIV | exact chart transport from a partial resolution, the normalised-indicator partition, and the localisation obstruction (u426–427; Astra #55 units 6–8)
CXXIII | two-sided sublevel growth implies two-sided Laplace growth, and the dominant exponent pair (u424–425; Astra #55 units 1–3)
CXXII | the concrete tangential reconstruction and the tangential stochastic expansion (u422–423; Astra #54 §6)
CXXI | joint charts from one sample and the reconstruction interface (u421; Astra #54 units 5–6)
CXX | the Hypothesis-I division bridge and the empirical phase (u420; Astra #54 unit 3)
CXIX | the torus `L²` certificate gives the chart moment certificate (u419; Astra #54 unit 2)
CXVIII | the stochastic expansion at the sample datum (u417; Astra #53 unit 8)
CXVII | the sample datum and the stochastic expansion with the data premise discharged (u416; Astra #53 unit 7)
CXVI | the central limit theorem in `ℓ¹` (u415; Astra #53 unit 6)
CXV | existence of the Gaussian limit in `ℓ¹` by tightness (u414; Astra #53 unit 5b)
CXIV | the i.i.d. central limit theorem in finite dimension (u411; Astra #53 unit 3)
CXIII | the conditional geometric main theorem (u408; Astra #52 unit 6)
CXII | the chart integral as a Taylor–moment series (u407; Astra #52 unit 5b)
CXI | the Taylor–moment contraction and representation (u406; Astra #52 unit 5a)
CX | moment functionals, invariant pairing, and the fibre pushforward (u405; Astra #52 unit 4)
CIX | normal jets and fibre-linear covariance (u404; Astra #52 unit 3)
CVIII | weighted chart presentations and the conditional geometric main theorem (u403; Astra #52 unit 2 + unit 6 first-nonzero part)
CVII | measured localisation of a Laplace-type integral (u402; Astra #52 unit 1)
CVI | the joint random assembled law (u401; Astra #51 unit 5)
CV | first corrections to chart allocations and assembled quotients (u399–400; Astra #51 units 3–4)
CIV | uniform finite-chart assembly at the next logarithmic order (u397–398; Astra #51 units 1–2)
CIII | expectations under law-level uniform integrability (u396; Astra #50 unit 6)
CII | the joint random next-log posterior-observable theorem (u395; Astra #50 unit 5)
CI | evidence ratios under a joint random data law (u394; Astra #50 unit 4)
C | uniform logarithmic lemma and random next-log free energy (u393; Astra #50 unit 3)
XCIX | random next-log posterior Laplace transform (u392; Astra #50 unit 2)
XCVIII | the data space is Polish — tightness discharged (u390)
XCVII | random next-log posterior energy correction (u389; Astra #49 unit 5)
XCVI | random next-log evidence jointly with its data (u388; Astra #49 units 3–4)
XCV | the uniform spatial two-term theorem on coefficient balls (u386; Astra #49 unit 1)
XCIV | temperature scaling of the two-term coefficients (u385; Astra #48 unit 6)
XCIII | quenched and stable convergence (u384; Astra #48 unit 5)
XCII | independence iff essential face constancy (u383; Astra #48 unit 4)
XCI | the random field jointly with a posterior draw (u382; Astra #48 units 1–3)
XC | the random-field finite-observable transfer (u381; Astra #47 unit 5)
LXXXIX | the graph-law transfer (u380; Astra #47 unit 4)
LXXXVIII | moving-phase joint weak convergence and phase-continuity of the limit law (u377; Astra #47 unit 1)
LXXXVII | the next-log observable dictionary with spatial phase (u376; Astra #46 unit 5)
LXXXVI | independence forces a face-constant phase (u375; Astra #46 unit 3, converse)
LXXXV | product form of the limiting joint law for a face-constant phase (u374; Astra #46 unit 3, "if")
LXXXIV | two-dimensional regression and a strict transverse example (u373; Astra #46 unit 2)
LXXXIII | finite-chart assembly at the next logarithmic order (u372; Astra #46 unit 1)
LXXXII | joint weak convergence of energy and location under a spatial phase (u371; Astra #45 unit 5)
LXXXI | next-log correction of the posterior energy mean with spatial phase (u370; Astra #45 unit 3)
LXXX | face versus transverse phase sensitivity at order 1/L (u369; Astra #45 unit 4)
LXXIX | the explicit second coefficient of an analytic spatial phase (u368; Astra #45 unit 2 COMPLETE)
LXXVIII | the second coefficient functional is a finite-part face integral (u366; Astra #45 unit 2, step 6)
LXXVII | two-term asymptotics for an arbitrary analytic spatial phase (u360; Astra #45 unit 1)
LXXVI | moving continuous phases (u359; Astra #44 unit 5)
LXXV | spatial-phase energy moments and face selection (u358; Astra #44 unit 4)
LXXIV | posterior concentration on the dominant face (u357; Astra #44 unit 3, location part)
LXXIII | the posterior energy law under a fixed continuous phase (u356; Astra #44 units 2–3, energy part)
LXXII | leading asymptotics for an arbitrary continuous phase (u355; Astra #44 unit 1)
LXXI | stochastic ordering of the limiting family and moving constant phases (u354; Astra #43 units 3, 6)
LXX | polynomial-growth observables (u353; Astra #43 unit 2)
LXIX | perturbed posterior energy moments (u352; Astra #43 unit 1)
LXVIII | stability under vanishing spatial phase perturbations (u351; Astra #42 unit 2)
LXVII | assembled posterior energy law (u350; Astra #42 unit 1)
LXVI | structure of the limiting energy law `ρ_a` (u349; Astra #42 units 3–4)
LXV | posterior Laplace transform with a moving random phase (u348; Astra #41 unit 2)
LXIV | weak convergence of the posterior law of `NK` at constant phase (u346–347; Astra #41 unit 5)
LXIII | constant-phase free energy, deterministic and moving (u345; Astra #41 unit 8)
LXII | phase-dressed energy moment hierarchy (u344; Astra #41 unit 4)
LXI | posterior law of `NK` at constant phase (u342–343; Astra #41 units 1–3)
LX | moving random constant phase (u340–341; Astra #40 unit 5)
LIX | assembled Gamma Laplace-transform limit (u339; Astra #40 unit 6)
LVIII | random constant phase (u338; Astra #40 unit 4)
LVII | constant-phase energy correction (u337; Astra #40 units 1–3)
LVI | constant-phase leading coefficient and energy ratio (u336; open thread closed)
LV | phase derivative through the monomial sum (u335; open thread closed)
LIV | constant-phase coefficient transport (u334; deferred item, Astra #39 unit 10 at kernel level)
LIII | stochastic second-order quotient at multiplicity one (u332–333; deferred item)
LII | phase-dressed moment recurrence and phase derivative (u331; Astra #39 unit 9)
LI | noncancellation from face witnesses (u329; Astra #39 units 7–8)
L | stochastic second-order posterior quotient (u328; Astra #39 units 1–3)
XLIX | Gamma Laplace-transform limit (u327; Astra #39 unit 6)
XLVIII | population energy hierarchy (u326; Astra #39 units 4–5)
XLVII | population free energy with its first inverse-log correction (u325; Astra #39 unit 11)
XLVI | second-order expectation quotient after finite chart assembly (u323)
XLV | second-order expectation quotient (u322)
XLIV | assembled energy correction (u321)
