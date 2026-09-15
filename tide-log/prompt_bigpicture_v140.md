You are Astra, auditing a Lean 4 / Mathlib formalisation of the EMPIRICAL (sample) version of the leading asymptotics of the partition function with insertion in singular learning theory (Gerraty–Murfet "grammar" paper, Section 4). This is consult #140. In #138 you designed ranks 0–5 of the empirical programme and in #139 you audited rank 2 (deterministic leading theorem for a fixed bounded root field under `ChartLeading`) and designed ranks 3–5 in detail. Ranks 3, 4 and 5a have now been formalised exactly along your design. Please audit them and give direction.

## What landed (all axiom-clean, no sorry; repo main 58765f6, 797 modules)

Setting (from rank 2, unchanged): resolved data Ξ (K∘π, prior μ_U on U, observable F), a finite resolved chart transport Y with pieces p, each piece with a compact base Base_p, box (0,b_p]^{d_p}, exponents (h_{p,i}, k_{p,i}), phase constants 1, an amplitude amp_p(s,u) (smooth, bounded on Base×closed box), base measure ν_p (finite), and a tail complement on which K∘π ≥ δ. `ChartLeading λ m := ∀ p, (∀ i, λ ≤ (h_{p,i}+1)/(2k_{p,i})) ∧ #{i : ratio = λ} ≤ m`. Root fields: bounded measurable ψ on U with continuous branch representatives loc_p on Base_p × ℝ^{d_p} agreeing with ψ∘divPt on the open box. `empZ ξ N = ∫_U F e^{−N K∘π + √N √(K∘π) ψ} dμ_U`. `empBoxIntegral h k N b ξ η = ∫_{(0,b]^d} η u · u^h · exp(−N u^{2k} + √N u^k ξ(u)) du`. `boxFaceLimit h k λ m b ξ η = if multCount(ratio) λ = m then faceFunctional else 0`, where `faceFunctional = (1/((m−1)! ∏_{J} 2k_j)) ∫_{(0,b]^{Jᶜ}} η(glue J 0 w) · S_λ(ξ(glue J 0 w)) · ∏_{i∉J} w_i^{h_i − 2k_i λ} dw`, J = resSet = {i : ratio_i = λ}, S_λ(a) = ∫_0^∞ t^{λ−1} e^{−t + a√t} dt. Rank 2 theorem: `hasLeadingTerm_empZ : Tendsto (fun N => empZ ξ N / (N^{−λ} (log N)^{m−1})) atTop (𝓝 (Σ_p ∫_{Base_p} boxFaceLimit(loc_p(s,·), amp_p s) dν_p))`.

### Rank 3 (CDLXXIV): `EmpiricalFieldLipschitz`, `UniformCompactFamilies`, `EmpiricalBranchTuples`

```lean
theorem abs_exp_field_sub_le {σ M a b : ℝ} (hσ : 0 ≤ σ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |Real.exp (-σ ^ 2 + σ * a) - Real.exp (-σ ^ 2 + σ * b)| ≤
      Real.exp (M ^ 2) * |a - b| * Real.exp (-(σ ^ 2 / 2))
-- (mean value + σM ≤ σ²/4 + M² + σe^{−σ²/4} ≤ 1; constant e^{M²} instead of your √(2/e)e^{M²})

theorem abs_empBoxIntegral_sub_le (h k : Fin d → ℕ) (hN : 0 ≤ N) (hξc hζc hηc : Continuous …)
    (hM : ∀ u ∈ box, |ξ u| ≤ M) (hM' : ∀ u ∈ box, |ζ u| ≤ M) (hδ : ∀ u ∈ box, |ξ u - ζ u| ≤ δ)
    (hA : ∀ u ∈ box, |η u| ≤ A) :
    |empBoxIntegral h k N b ξ η - empBoxIntegral h k N b ζ η| ≤
      Real.exp (M ^ 2) * δ * A * empBoxIntegral h k (N / 2) b (fun _ => 0) fun _ => 1

-- abstract ε-net lemma, E any pseudo-metric space
theorem tendstoUniformlyOn_of_eventually_lipschitz (hC : IsCompact C)
    (hpt : ∀ f ∈ C, Tendsto (fun N => T N f) atTop (𝓝 (Tlim f)))
    (hlip : ∀ᶠ N in atTop, ∀ f ∈ C, ∀ g ∈ C, |T N f - T N g| ≤ L * dist f g) :
    TendstoUniformlyOn T Tlim atTop C
-- (the limit inherits the Lipschitz bound; no regularity of Tlim assumed)

-- continuous branch tuples: PieceDom p := Base_p × ↥(closedBox d_p b_p) (compact metric)
abbrev BranchTuple : Type := ∀ p : (Ξ.X Y).PIdx, C(Ξ.PieceDom Y p, ℝ)     -- Pi sup norm
-- tupleField f p (s,v) := f p (s, clampBox b v)  (coordinatewise clamp to [0,b]; identity on the closed box)
noncomputable def tupleZ (f : BranchTuple) (N : ℝ) : ℝ := ∑ p, ∫ s, empBoxIntegral (hA p) (kA p) N (a p) (fun v => tupleField f p (s, v)) (fun v => amp_p s v) ∂ν_p
noncomputable def tupleLimit (f : BranchTuple) (lam : ℝ) (m : ℕ) : ℝ := ∑ p, ∫ s, boxFaceLimit (hA p) (kA p) lam m (a p) (fun v => tupleField f p (s, v)) (fun v => amp_p s v) ∂ν_p

theorem hasLeadingTerm_tupleZ (f) (hm : 1 ≤ m) (hlead : ChartLeading lam m) :
    HasLeadingTerm (tupleZ f) (tupleLimit f lam m) lam (m - 1)
theorem abs_tupleZ_sub_le (f g) (hN : 0 ≤ N) (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) (hA : amp bounds A p) :
    |tupleZ f N - tupleZ g N| ≤ tupleLipConst A R N * ‖f - g‖
-- tupleLipConst A R N = e^{R²} Σ_p A_p · empBoxIntegral_p(N/2, 0, 1) · ν_p(Base_p)
theorem exists_eventually_lipschitz_tupleZ_div (hm) (hlead) (R : ℝ) :
    ∃ L, ∀ᶠ N in atTop, ∀ f g, ‖f‖ ≤ R → ‖g‖ ≤ R →
      |tupleZ f N / s_N - tupleZ g N / s_N| ≤ L * ‖f - g‖          -- s_N = powLogScale lam (m-1) N
theorem tendstoUniformlyOn_tupleZ (hm) (hlead) {C : Set BranchTuple} (hC : IsCompact C) :
    TendstoUniformlyOn (fun N f => tupleZ f N / s_N) (fun f => tupleLimit f lam m) atTop C
-- bridge to root fields
noncomputable def RootField.tuple (ξ : RootField) : BranchTuple := fun p => ⟨fun z => ξ.loc p (z.1, z.2.1), _⟩
theorem empZ_eq_tupleZ_add_tail (ξ) (hN : 0 ≤ N) (hM : ∀ P, |ξ.ψ P| ≤ M) :
    empZ ξ N = tupleZ ξ.tuple N + ∫ P, empIntegrand ξ N P ∂tailU
theorem tupleLimit_tuple_eq (ξ) (hm) (hlead) (hM) :
    tupleLimit ξ.tuple lam m = ∑ p, ∫ s, pieceFaceLimit p ξ lam m s ∂ν_p   -- (by uniqueness of limits)
```

### Rank 4 (CDLXXV): `UniformCompactTransfer`, `EmpiricalFieldLimit` (Mathlib's `TendstoInDistribution`, `IsTightMeasureSet`, Slutsky `add_of_tendstoInMeasure_const`)

```lean
-- E metric, Borel; P, P' probability measures
theorem tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts {L : ℕ → Ω → E} (hLm : ∀ n, Measurable (L n)) {G : Ω' → E}
    (hLG : TendstoInDistribution L atTop G (fun _ => P) P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (L n)))
    {T : ℕ → E → ℝ} {Tlim : E → ℝ} (hTc : ∀ n, Continuous (T n)) (hlimc : Continuous Tlim)
    (hunif : ∀ C : Set E, IsCompact C → TendstoUniformlyOn T Tlim atTop C) :
    TendstoInDistribution (fun n ω => T n (L n ω)) atTop (fun ω => Tlim (G ω)) (fun _ => P) P'
theorem tendstoInMeasure_zero_of_tight_bound {Y M : ℕ → Ω → ℝ} {r : ℕ → ℝ} {c : ℝ → ℝ} (hc : MonotoneOn c (Ici 0)) (hM0 : ∀ n ω, 0 ≤ M n ω)
    (hbound : ∀ n ω, |Y n ω| ≤ c (M n ω) * r n) (hr : Tendsto r atTop (𝓝 0)) (hr0 : ∀ n, 0 ≤ r n)
    (hM : ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, ∀ᶠ n in atTop, P {ω | R < M n ω} ≤ η) :
    TendstoInMeasure P Y atTop 0

instance : MeasurableSpace BranchTuple := borel _ ; instance : BorelSpace BranchTuple := ⟨rfl⟩
theorem continuous_tupleZ (hN : 0 ≤ N) : Continuous fun f => tupleZ f N          -- Lipschitz on balls
theorem continuous_tupleLimit (hm) (hlead) : Continuous fun f => tupleLimit f lam m
theorem tendstoInDistribution_tupleZ_div (hm) (hlead) {L : ℕ → Ω → BranchTuple} (hLm) {G} (hLG : TendstoInDistribution L atTop G _ P') (htight) :
    TendstoInDistribution (fun n ω => tupleZ (L n ω) n / s_n) atTop (fun ω' => tupleLimit (G ω') lam m) (fun _ => P) P'
theorem tendstoInMeasure_tail_div (ξ : ℕ → Ω → RootField) {M : ℕ → Ω → ℝ} (hM : ∀ n ω Q, |(ξ n ω).ψ Q| ≤ M n ω) (hM0 : ∀ n ω, 0 ≤ M n ω)
    (hMt : ∀ η > 0, ∃ R, ∀ᶠ n, P {ω | R < M n ω} ≤ η) (lam) (q) :
    TendstoInMeasure P (fun n ω => (∫ Q, empIntegrand (ξ n ω) n Q ∂tailU) / powLogScale lam q n) atTop 0

theorem tendstoInDistribution_empZ_div (hm : 1 ≤ m) (hlead : ChartLeading lam m) (ξ : ℕ → Ω → RootField)
    (hLm : ∀ n, Measurable fun ω => (ξ n ω).tuple)
    (hZm : ∀ n, AEMeasurable (fun ω => empZ (ξ n ω) n) P)
    {G : Ω' → BranchTuple} (hLG : TendstoInDistribution (fun n ω => (ξ n ω).tuple) atTop G (fun _ => P) P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map fun ω => (ξ n ω).tuple))
    {M : ℕ → Ω → ℝ} (hM : ∀ n ω Q, |(ξ n ω).ψ Q| ≤ M n ω) (hM0 : ∀ n ω, 0 ≤ M n ω)
    (hMt : ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, ∀ᶠ n in atTop, P {ω | R < M n ω} ≤ η) :
    TendstoInDistribution (fun (n : ℕ) ω => empZ (ξ n ω) n / powLogScale lam (m - 1) n) atTop
      (fun ω' => tupleLimit (G ω') lam m) (fun _ => P) P'
```

### Rank 5a (CDLXXVI): `GaussianFluctuationScalar`, `EmpiricalGaussianExpectation`

```lean
theorem integral_mul_fluctuation_eq_of_measure (ν : Measure α) [IsProbabilityMeasure ν] (β μ) (X : α → ℝ) (hX) (P : α → ℝ) (hP) (M : ℝ → ℝ)
    (hint : ∀ θ, Integrable (fun a => P a * exp (θ * X a)) ν) (hM : ∀ θ, ∫ |P a| exp(θ X a) ≤ M θ) (hK : IntegrableOn (fun t => radialKernel β μ t * M (β √t)) (Ioi 0)) :
    Integrable (fun a => P a * fluctuation β μ (X a)) ν ∧ ∫ P a * S_μ(X a) = ∫_{t>0} radialKernel β μ t * ∫ P a e^{β√t X a}
theorem integral_fluctuation_gaussianReal' (β μ) (hβ hμ) (v : ℝ≥0) (hδ : 0 < 1 - β v / 2) :
    Integrable (fluctuation β μ) (gaussianReal 0 v) ∧ ∫ S_μ d(gaussianReal 0 v) = Γ(μ) (β (1 − βv/2))^{−μ}
noncomputable def gaussianFluctConst (μ : ℝ) (v : ℝ≥0) : ℝ := Real.Gamma μ * (1 - v / 2) ^ (-μ)
theorem integral_integral_fluctuation_of_gaussian_marginals {ρ : Measure Z} [SFinite ρ] {a : Z → ℝ} (ha : Integrable a ρ) {X : Ω × Z → ℝ} (hX : Measurable X) {v : ℝ≥0}
    (hlaw : ∀ z, P.map (fun ω => X (ω, z)) = gaussianReal 0 v) (μ) (hμ : 0 < μ) (hv : v < 2) :
    Integrable (fun q => a q.2 * fluctuation 1 μ (X q)) (P.prod ρ) ∧
    ∫ ω, ∫ z, a z * fluctuation 1 μ (X (ω, z)) ∂ρ ∂P = gaussianFluctConst μ v * ∫ z, a z ∂ρ

theorem SmoothEngine.integrableOn_residueWeight_box (h k : ι → ℕ) (l) (hlt : ∀ i, 2 k_i l < h_i + 1) (hb : 0 ≤ b) :
    IntegrableOn (residueWeight h k l) (box ι b)       -- residueWeight h k l w = u^h · (u^{2k})^{−l} = ∏ w_i^{h_i − 2k_i l}
theorem integral_tupleFaceLimit_eq (f) (p) (hlam : 0 < lam) (hlead : BoxLeading (hA p) (kA p) lam m) :
    ∫ s, tupleFaceLimit f p lam m s ∂ν_p = if multCount = m then ∫ z, faceWeight p lam m z * S_λ(faceField f p lam z) ∂(ν_p ⊗ vol|box_{Jᶜ}) else 0
-- faceWeight z = c_p · amp_p(s, glue J 0 w) · residueWeight(w);  faceField f p lam (s,w) = tupleField f p (s, glue J 0 w)

theorem integral_tupleLimit_gaussian (hlam : 0 < lam) (hlead : ChartLeading lam m) {G : Ω' → BranchTuple} (hG : Measurable G) {v : ℝ≥0} (hv : (v:ℝ) < 2)
    (hlaw : ∀ (p : PIdx) (z : PieceDom p), P'.map (fun ω => G ω p z) = gaussianReal 0 v) :
    Integrable (fun ω => tupleLimit (G ω) lam m) P' ∧
    ∫ ω, tupleLimit (G ω) lam m ∂P' = (1 - (v:ℝ) / 2) ^ (-lam) * tupleLimit 0 lam m
```

## Paper-facing text now in the mirror (please audit the wording)

"Let $\psi_n$ be random root fields on a probability space with measurable tuples $\hat\psi_n$, suppose $\hat\psi_n\Rightarrow G$ in $E$ (weak convergence of the laws) with tight laws, and that nonnegative bounds $M_n\ge\sup_U|\psi_n|$ satisfy $M_n=O_p(1)$. Then $Z^{\mathrm{emp}}_n[F;\psi_n]/s_n\Rightarrow T(G)$. … Joint convergence of the tuple is the hypothesis; convergence of the piecewise marginals would not suffice. … If every one-point law of $G$ is $N(0,v)$ with $v<2$ (no independence across points or pieces is assumed), then $T(G)$ is integrable and $\mathbb E\,T(G)=(1-v/2)^{-\lambda}T(0)$, $T(0)$ the population face limit. Not asserted: that $\hat\psi_n\Rightarrow G$ or the tightness follow from a statistical model (… $E$-valued convergence would need a functional central limit theorem for the branch representatives); any annealed statement $\mathbb E[Z^{\mathrm{emp}}_n/s_n]\to\mathbb E\,T(G)$, which needs uniform integrability; and the facewise varying variance."

## Questions

(a) Audit the three main statements (`tendstoUniformlyOn_tupleZ`, `tendstoInDistribution_empZ_div`, `integral_tupleLimit_gaussian`) for correctness of hypotheses and for hidden gaps: (i) is measurability of ω ↦ empZ(ξ_n ω) n as a HYPOTHESIS acceptable (RootField carries no σ-algebra), or should it be derived (e.g. from a jointly measurable ψ)? (ii) is `IsTightMeasureSet` of the laws redundant given convergence in distribution in E = ∏ C(K_p) (Polish) — Mathlib may lack "convergent ⇒ tight"; is it worth proving? (iii) the `M_n ≥ 0` and `M_n = O_p(1)` phrasing; (iv) in 5a the hypothesis "every one-point law is N(0,v) with the SAME v" — how restrictive is this for the actual Gaussian process limit of ψ_n on the resolution (Watanabe's ξ has a covariance kernel; the one-point variance v(u) = Var of the normalised score direction varies over the divisor); would the natural next statement be the facewise varying variance with a uniform gap sup v ≤ 2 − ε, giving E T(G) = Σ_p c_p ∫∫ amp · Γ(λ)(1 − v(z)/2)^{−λ} · weight ?

(b) The 1/(1 − v/2)^λ factor: relate it to the paper's/Watanabe's annealed expectation of the empirical partition function and the β < 1 (or v < 2) threshold; is it right that on the divisor at β = 1 the natural variance is v = 2 exactly (the "critical" case, E S = ∞), so the finite-mean statement genuinely requires the tempered/β<1 or a variance gap? Please state precisely what is and is not implied about E[Z^emp_n/s_n].

(c) What is the honest status of the statistical input ξ̂_n ⇒ G in ∏_p C(K_p): what would a Lean proof need (Kolmogorov–Chentsov / tightness via modulus of continuity of the empirical process on the compact box; the paper's analytic-certificate route; the repo has an ℓ¹-sequence CLT `L1SeqCLT` and chart-level CLTs)? Rank it against (d).

(d) Direction: what should be built next, ranked, with sizes: 5b annealed (UI via uniform exponential moments of M_n²), the varying-variance 5a, the functional CLT input, the ChartLeading↔IsExtremalData bridge, the all-smooth-F stratum-integral identification, or declaring the empirical programme closed for the paper and returning to write-up. Say whether the empirical programme as it stands is a paper-worthy result and give the one-paragraph theorem statement you would put in the paper.
