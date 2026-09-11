# Astra consult #66 — both open programmes closed; what next?

You are Astra, direction-setting consultant for the Lean 4 (Mathlib v4.33.1) formalisation of Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*, repo `timaeus-research/grammar` (main `1513312`, 487 modules, axiom-clean, zero sorries) with the companion note `averaging_dataset.tex` (Gaussian averaging over the dataset). Your consult #65 (bounded fidelity pass on the bundle layer) and your consult #62 (companion-note programme: sampling gate, sub-Gaussian observations, effective temperature, paper closure) are now **both fully executed**. Summary of what landed since #65:

* **Astra #65 units 1–4**: claim ledger applied (CLXXVI "embedded base" → smooth map with no embedding hypothesis, "tangent field" → kernel field, `IsGlobalNormalSection` is `C^∞` not analytic and the Taylor-section theorem is over a normed-space base, CLXXVIII is a linear coordinate model, tubular-definition dots certify decomposition/uniqueness only); CLXXIX geometric identification adapter + labelled-splitting resolution (the gradient lines are the Riesz images of the paper's conormal lines `ℝ·du_l`); CLXXX conditional unit 14 (lifted foot). Unit 5 (independent closure review) NOT done.
* **Astra #62 units 1–6**: CLXXXI sampling/core compatibility (release gate passed: sample phase = `−ζ_n`, certified core at the sample datum = sampling integral with `N = n`); CLXXXII boundedness removed (L² functionals, uniform full-box sub-Gaussian proxy `κ` inherited by the empirical phase, sharp `Var ≤ κ`, annealed theorems for `pβκ < 2`, first moment for `βκ < 2`); CLXXXIII effective-temperature corollary (a.e. constant face variance `v₀` ⇒ `E_ν[C(Z+A)] = C(A; β(1−βv₀/2))`) and the normal-location check (phase variance 2); note abstract/centring remark/interface table and mirror updated as you specified.

## Headline rows landed (verbatim)

| **CLXXXIII** | **the effective-temperature corollary and the normal-location check (u496; Astra #62 unit 5)**: the zero-phase population leading coefficient is `C^b_{λ,m−1}(A; β) = b^{|h|+d} c^{−λ} K_face (Γ(λ) β^{−λ}/2) ∫ η_A(π u) w(u) du / 2^{m−1}` (`dataBoxCoeff_leading_zero_phase`, from `S_λ(0) = β^{−λ}Γ(λ)`), so when the face variance is almost-everywhere constant on the box, `σ²(π u) = v₀` with `βv₀ < 2`, **`E_ν[C^b_{λ,m−1}(Z + A)] = C^b_{λ,m−1}(A; β_eff)`, `β_eff = β(1 − βv₀/2)`** — the zero-phase population coefficient with the same geometric data and amplitude at the effective temperature (`integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance`); **the normal-location check**: for `g_a(x) = a²/2 − ax` (`X ~ N(0,1)`), `∑_{i<n} g_a(X_i) = na²/2 − a∑X_i`, the standard form with core coordinate `ρ = a/√2` is `g_a = ρ(ρ − √2 x)`, and the sampling phase is `ξ_n = −ζ_n = √2 n^{−1/2}∑X_i` with variance `2`, not `1` (`sum_normalLocation`, `normalLocation_standard_form`, `neg_zetaEmp_normalLocation`, `variance_phase_normalLocation`). Non-claims: no converse (a signed amplitude can produce accidental equalities of integrals); pointwise constancy is not required; finitely many charts have chart-specific effective temperatures (a single one needs a common variance); the check certifies neither the resolution presentation, nor the localisation, nor the remainder | EffectiveTemperature.lean |
| **CLXXXII** | **the sub-Gaussian empirical programme — boundedness removed from CLXII–CLXV (u493–u495; Astra #62 units 2–4)**: (unit 2) continuous linear functionals of the `ℓ¹` Gaussian limit are Gaussian for observations in `L²(P; ℓ¹)` — the dominated-convergence step `Var[L(T_F Y₀)] → Var[L(Y₀)]` uses the dominating functions `‖L‖‖Y₀‖`, `‖L‖²‖Y₀‖²` (`tendsto_variance_truncate_of_memLp`, `map_eq_gaussianReal_of_marginals_of_memLp`), hence `ν.map(ξ_·(u)) = N(0, Var ξ_{Y₀}(u))` and a.s. vanishing amplitude coordinates for `L²` phase observations (`map_phaseEvalCLM_eq_gaussianReal_of_memLp`, `ae_etaCoord_eq_zero_of_memLp`; bounded ⇒ `L²`, `memLp_two_sampleObs_of_bounded`); (unit 3) the **uniform full-box sub-Gaussian hypothesis** `E e^{tQ_u} ≤ e^{κt²/2}` on the centred phase evaluations `Q_u = ξ_{Y₀}(u) − E ξ_{Y₀}(u)` of one observation (`UniformSubgaussianPhase`) is inherited with the **same proxy** by the normalised empirical phase `n^{−1/2}∑_{i<n} Q_u(X_i)` (`hasSubgaussianMGF_empiricalPhase`, Mathlib's `sum_of_iIndepFun` and `const_mul`, `((√n)⁻¹)²·nκ = κ`), giving the full-box exponential-moment bound uniformly in `n` and `u` (`lintegral_exp_phase_sampleDatum_le_of_subgaussian`); **the sharp variance bound** `Var[X] ≤ κ` of a sub-Gaussian variable (`variance_le_of_hasSubgaussianMGF`: `y² ≤ e^y + e^{−y} − 2` from `|y/2| ≤ sinh|y/2|`, the two-sided MGF bound and `t → 0⁺`), so the face variances satisfy `σ²(v) ≤ κ` (`phaseVar_le_of_uniformSubgaussian`) and the advertised threshold `βκ < 2` stands; bounded observations have proxy `M₀²` (Hoeffding, `uniformSubgaussianPhase_of_bounded`); (unit 4) the expectation assembly, the single-chart and the several-chart annealed sample-datum theorems for sub-Gaussian observations (`tendsto_integral_scaled_assembly_sampleDatum_subgaussian`, `tendsto_integral_scaled_sampleDatum_single_subgaussian`, `tendsto_integral_scaled_coreSum_sampleDatum_subgaussian`: `p > 1`, `pβκ < 2`, integrability of the observations from the `ℓ¹` certificate), and the Gaussian first moment `E_ν[C^b_{λ,m−1}(Z + A)] = b^{|h|+d} c^{−λ} K_face (Γ(λ)/2) ∫ η_A(π u) (β(1 − βσ²(π u)/2))^{−λ} w(u) du / 2^{m−1}` for `L²` observations with `βκ < 2` (`integral_dataBoxCoeff_leading_eq_subgaussian`). The bounded theorems CLXII–CLXV are the case `κ = M₀²`. Non-claims: no sub-Gaussian bound for the `ℓ¹` norm of the observations; no `ℓ¹` CLT from the scalar evaluation bounds (the coordinate certificate stays); a common proxy across charts (chart-specific `κ_I` with a common `p` is the refinement); the Banach `L²` norm is a hypothesis, not derived from the coordinate certificate; the external remainder as before | L1GaussianFunctionalL2.lean, SubgaussianPhase.lean, SubgaussianAssembly.lean |
| **CLXXXI** | **sampling/core compatibility — the release gate of the companion note (u492; Astra #62 unit 1)**: evaluation commutes with the Bochner mean (`phaseEvalCLM_integral`); the exact centred evaluation `ξ_n(u) = n^{−1/2}∑_{i<n}(ξ_{Y_i}(u) − E ξ_{Y₀}(u))` and the amplitude invariance `η(sampleDatum) = η(A)` need only integrable observations (`phaseEval_sampleDatum_of_integrable`, `etaCoord_sampleDatum_of_integrable`); **the sign**: when the coefficient family is the Taylor family of `−a(x,·)` at the box point (`evalF (c x) (b•u) = −a x (b•u)`) and `E a(X, b·u) = φ(b·u)`, the phase of the sample datum is `−ζ_n(b·u)`, *minus* the centred empirical process of the coefficient (`evalF_xiCoord_sampleDatum_eq_neg_zetaEmp`), and the sampling exponent is the standard-integral exponent at the sample datum with `N = n`: `−β∑_{i<n} f(X_i, b·u) = −βnφ² + β√n φ ξ_n(u)` (`sampling_exponent_eq_sampleDatum_phase`, via CXXVII's `sampling_exponent_eq`); **the certified box core is the sampling integral**: in the monomial chart `φ(v) = v^k` the integrand `e^{−β∑_i f(X_i,v)}` is the phase factor `e^{−βn v^{2k} + β√n v^k ξ(v)}` of the box integrand at the sample datum (`exp_sampling_exponent_eq_core_factor`) and `Z(n; sampleDatum) = ∫_{(0,b]^d} η_A(v) v^h e^{−β∑_{i<n} f(X_i,v)} dv` (`dataBoxIntegral_sampleDatum_eq_sampling`), before any limit or expectation. Convention certified: `phaseObs` represents `−a` (equivalently `log p − log q`), the sample phase is the paper's `ξ_n = −ζ_n`, and the population mean is carried by the deterministic exponent `−βnφ²`, not by the zero-phase amplitude datum `A`. Non-claims: the identification of an abstract coefficient family with a model's Taylor coefficients is the hypothesis `hca`; nothing probabilistic is used beyond integrability | SamplingCompatibility.lean |
| **CLXXX** | **the conditional tubular equivalence (u491; Astra #65 unit 4 = Astra #64 unit 14 in conditional form)**: given a StrucDual normal tubular chart `T` of `S ⊆ ℝ^d`, an injective smooth map `emb : B → ℝ^d` onto `S`, a frame–coframe atlas of the normal field along `emb`, and a **lifted foot** `P` (smooth on the tube with `emb (P y) = proj y`; `LiftedFoot`), the map `Ψ(x,n) = emb x + n` on the certified domain `{‖n‖ < ε}` (`tubeMap`, `tubeDom`, open) lands in the tube with foot `emb x` and normal coordinate `n` (`tubeMap_mem_tube`, `proj_tubeMap`, `ncoord_tubeMap`), is inverted by `y ↦ (P y, ncoord y)` (`tubeInv`, `tubeInv_tubeMap`, `tubeMap_tubeInv`) with image the tube (`image_tubeMap`), is `C^∞` on the total space (`contMDiff_tubeMap`) and has a `C^∞` inverse on the tube — in frame `j` the fibre coordinate of the inverse is `coframe j (P y) (ncoord y)` (`snd_tubeInv_eq_coframe`, `contMDiffOn_tubeInv` via `Trivialization.contMDiffWithinAt_iff`) — packaged as an open partial homeomorphism from the domain onto the tube (`tubeHomeomorph`). Closes: *given* a certified tube and a smooth identification of its foot with the base, the frame-built bundle realises the tube diffeomorphically. Non-claims: existence of the lifted foot (a smooth left inverse of `emb` along the tube), an embedded level-set manifold, or a tubular neighbourhood from the labelled equations alone | TubularBridge.lean |
| **CLXXIX** | **the labelled normal bundle as the Riesz image of the conormal splitting, and the geometric identification adapter (u490; Astra #65 units 2–3)**: Astra's review asked which labelled splitting CLXXVI realises — the answer is the paper's: the Riesz map carries the gradient frame `c ↦ ∑ c_l ∇u_l` to the differential frame `c ↦ ∑ c_l du_l` (`toDual_frame_apply`), each gradient line to the labelled conormal line `ℝ·du_l` of CLXVII (`toDual_grad_mem_conormalLine`), the normal space `(T x)ᗮ` onto the pointwise conormal space `(T x)^⊥ ⊆ E*` (`mem_normal_iff_toDual_mem_conormalOf`), and the frame coordinates are exactly CLXVII's conormal coordinates `ℝ^k ≃ N*_pX` (`toDual_frame_eq_conormalCoordEquiv`) — so the labelled lines of CLXXVI are the Riesz images of `𝓛_i = ℝ·du_i` in `eq:decomp_nx`, not the lines dual to them under the canonical pairing; **geometric identification**: `LabelledDefiningEquations` is algebraic data along a smooth map, and `GeometricIdentification` records the hypotheses (equations vanish along the map, the map is injective, the image of `mfderiv emb` is the kernel field `⋂ ker du_l`) under which the kernel field is the image of the tangent spaces and the normal field is its orthogonal complement (`normal_eq_orthogonal_range_mfderiv`); the scalar overlap law follows from function-level unit changes on the zero set (`unit_of_mul`). Non-claims: the tangent-image equality is a hypothesis (no implicit-function construction of a level-set manifold); no direct-sum bundle isomorphism beyond the frame-level statements | LabelledConormalBridge.lean |

## Key statements (verbatim Lean)

### TubularBridge (CLXXX): LiftedFoot, tubeHomeomorph
```lean
structure LiftedFoot (T : NormalTubularChart N S) (emb : B → (Fin d → ℝ)) {ι : Type*}
    (D : FrameCoframeData IB V ∞ (fun x => N (emb x)) ι) (P : (Fin d → ℝ) → B) : Prop where
  contMDiff_emb : ContMDiff IB 𝓘(ℝ, Fin d → ℝ) ∞ emb
  emb_mem : ∀ x, emb x ∈ S
  emb_injective : Injective emb
  contMDiffOn_P : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) IB ∞ P T.U
  emb_P : ∀ y ∈ T.U, emb (P y) = T.proj y

variable (T : NormalTubularChart N S) (emb : B → (Fin d → ℝ)) {ι : Type*}
  (D : FrameCoframeData IB V ∞ (fun x => N (emb x)) ι) (P : (Fin d → ℝ) → B)

/-- **The tubular map** `Ψ (x, n) = emb x + n`. -/
noncomputable def tubeMap (p : TotalSpace V D.toAtlas.toCore.Fiber) : Fin d → ℝ :=
  emb p.1 + D.toAtlas.realise p

/-- **The certified domain** `{(x, n) : ‖n‖ < ε}`. -/
def tubeDom : Set (TotalSpace V D.toAtlas.toCore.Fiber) := {p | ‖D.toAtlas.realise p‖ < T.eps}

theorem isOpen_tubeDom : IsOpen (tubeDom T emb D) :=
...
noncomputable def tubeHomeomorph (h : LiftedFoot T emb D P) :
    OpenPartialHomeomorph (TotalSpace V D.toAtlas.toCore.Fiber) (Fin d → ℝ) where
  toFun := tubeMap emb D
  invFun := tubeInv T D P h
  source := tubeDom T emb D
  target := T.U
  map_source' := fun _ hp => tubeMap_mem_tube h hp
  map_target' := fun _ hy => tubeInv_mem_tubeDom h hy
  left_inv' := fun _ hp => tubeInv_tubeMap h hp
  right_inv' := fun _ hy => tubeMap_tubeInv h hy
```

### SamplingCompatibility (CLXXXI)
```lean
theorem evalF_xiCoord_sampleDatum_eq_neg_zetaEmp (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) (n : ℕ) (ω : Ω) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) (hca : ∀ x, evalF (c x) (b • u) = -a x (b • u))
    (hφ : ∫ ω', a (X 0 ω') (b • u) ∂P = φ (b • u)) :
    evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u =
      -zetaEmp n (fun i => a (X i ω) (b • u)) (φ (b • u)) := by
  rw [phaseEval_sampleDatum_of_integrable b hb c hc P X hint A hA n ω hu]
  unfold zetaEmp
  rw [← mul_neg, ← Finset.sum_neg_distrib]
...
theorem dataBoxIntegral_sampleDatum_eq_sampling (h k : Fin (n + 1) → ℕ)
    (hint : Integrable (sampleObs b hb c hc X 0) P) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    {m : ℕ} (hm : 0 < m) (ω : Ω)
    (hca : ∀ x, ∀ v ∈ piBox (n + 1) (Ioc 0 b), evalF (c x) v = -a x v)
    (hφ : ∀ v ∈ piBox (n + 1) (Ioc 0 b), ∫ ω', a (X 0 ω') v ∂P = ∏ i, v i ^ k i) (β : ℝ) :
    dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) =
      ∫ v in piBox (n + 1) (Ioc 0 b), evalF (toEta b A) v * (∏ i, v i ^ h i) *
        Real.exp (-β * ∑ i ∈ Finset.range m, (∏ i, v i ^ k i) * a (X i ω) v) := by
  unfold dataBoxIntegral familyPhaseIntegralBox
  rw [toEta_sampleDatum_of_integrable b hb c hc P X hint A m ω]
```

### SubgaussianPhase (CLXXXII)
```lean
  phaseEvalCLM u hu (sampleObs b hb c hc X i ω) -
    ∫ ω', phaseEvalCLM u hu (sampleObs b hb c hc X 0 ω') ∂P

/-- **The uniform full-box sub-Gaussian hypothesis**: `E e^{tQ_u} ≤ e^{κt²/2}` for every `t` and
every `u` in the closed unit cube. -/
def UniformSubgaussianPhase (κ : ℝ≥0) : Prop :=
  ∀ (u : Fin d → ℝ) (hu : u ∈ closedCube d),
    HasSubgaussianMGF (centredPhaseObs b hb c hc P X u hu 0) κ P

...
theorem hasSubgaussianMGF_empiricalPhase (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hint : Integrable (sampleObs b hb c hc X 0) P)
    (A : DataSpace d) (hA : xiCoord A = 0) {n : ℕ} (hn : 0 < n) (u : Fin d → ℝ)
    (hu : u ∈ closedCube d) :
    HasSubgaussianMGF (fun ω => evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u) κ P := by
  have e : (fun ω => evalF (xiCoord (sampleDatum b hb c hc P X A n ω)) u) =
      fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, centredPhaseObs b hb c hc P X u hu i ω := by
    funext ω
```

### SubgaussianAssembly (CLXXXII)
```lean
theorem tendsto_integral_scaled_sampleDatum_single_subgaussian (hk : ∀ i, 0 < k i)
    {β p M : ℝ} {κ : ℝ≥0} (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * κ < 2) (hM : 0 ≤ M)
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (A : DataSpace (n + 1)) (hA : xiCoord A = 0)
    (hAM : mass (etaCoord A) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω =>
      scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA (minRatio h k)
      (multCount (ratioExp h k) (minRatio h k)) m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      (∀ F : Finset (DataIdx (n + 1)),
        (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P) ∧
      Integrable (fun x => dataBoxCoeff n h k β b (x + A) (minRatio h k)
        (multCount (ratioExp h k) (minRatio h k) - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      Tendsto (fun m => ∫ ω, scaleA (minRatio h k) (multCount (ratioExp h k) (minRatio h k)) m *
          (dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) + R m ω) ∂P) atTop
        (𝓝 (∫ x, dataBoxCoeff n h k β b (x + A) (minRatio h k)
          (multCount (ratioExp h k) (minRatio h k) - 1)
            ∂(ν : Measure (L1Seq (DataIdx (n + 1)))))) := by
  obtain ⟨ν, hmarg, hcore⟩ := tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum b hb c hc P
    X h k hk hβ hcm hXm hXind hXid hc2 hsum A
  have hint : Integrable (sampleObs b hb c hc X 0) P :=
    integrable_of_summableCoordL2 P (summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum)
  have e : ∀ m ω, coreSum n (fun _ : Fin 1 => h) (fun _ => k) (fun _ => b) β (fun m => (m : ℝ))
      (fun _ m => sampleDatum b hb c hc P X A m) m ω =
      dataBoxIntegral n h k β m b (sampleDatum b hb c hc P X A m ω) := fun m ω => by
    simp [coreSum]
  have hcore' : TendstoInDistribution (fun m ω =>
```

### EffectiveTemperature (CLXXXIII)
```lean
theorem integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM2 : MemLp (sampleObs b hb c hc X 0) 2 P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hβκ : β * κ < 2)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    (A : DataSpace (n + 1)) (hA : xiCoord A = 0) {v₀ : ℝ} (hv₀ : β * v₀ < 2)
    (hconst : ∀ᵐ u ∂volume, u ∈ unitBox (n + 1) →
      phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) = v₀) :
    ∫ Z, dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)
        ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
      dataBoxCoeff n h k (β * (1 - β * v₀ / 2)) b A l (multCount (ratioExp h k) l - 1) := by
  have hβeff : 0 < β * (1 - β * v₀ / 2) := mul_pos hβ (by linarith)
  rw [(integral_dataBoxCoeff_leading_eq_subgaussian n h k hk hβ hb hmin hatt c hc P X hcm hXm hc2
    hsum hM2 hκ hβκ hmarg htail A hA).2,
    dataBoxCoeff_leading_zero_phase n h k hk hβeff hb hmin hatt A hA]
  congr 3
```


## What is NOT done / external
* Existence of the lifted foot `P` (a smooth left inverse of `emb` along a StrucDual tube); manifold structure on a level set (IFT); the exact geometric bridge (analytic units / compatible localisation for hironaka's chart form); nothing on the paper's resolved `U` beyond charts.
* Identification of the abstract coefficient family `c_γ(x)` with a model's Taylor coefficients (the hypothesis `hca` of CLXXXI); the external remainder `E|A_n Rem_n| → 0`; the Banach `L²` norm from the coordinate certificate (kept as a hypothesis); chart-specific sub-Gaussian proxies `κ_I` (a common `κ` is used).
* Astra #65 unit 5 (independent closure review of the geometry claims) and an analogous review of the empirical chain.
* The user's standing directive after the geometry: "finish the paper, then formalise `averaging_dataset.tex`" — the note's Gaussian-averaging sections (raw one-point/bilocal/quartet/interpolation/compact base) were formalised in CXXVI–CLXV; its Discussion/heuristic appendices are explicitly non-formal.

## Questions
1. **Closure audit.** Given the rows above, is there any statement in CLXXIX–CLXXXIII you would call an over-claim, or any hypothesis that silently supplies content (e.g. `hca` in CLXXXI, `UniformSubgaussianPhase` as a hypothesis on the sampling law, the a.e. constancy in CLXXXIII)? Name corrections to headline wording or paper dots.
2. **Next direction.** Candidates: (A) lifted-foot existence in a bounded form (e.g. `B` an embedded submanifold with a smooth retraction on the tube — a local IFT/graph argument — or via StrucDual's atlas `stratum_tube` data), making CLXXX unconditional for the paper's strata; (B) the exact geometric bridge; (C) companion-note extras: chart-specific proxies, the `ℓ¹`-norm `L²` bound from the coordinate certificate (Minkowski + Fatou), the next logarithmic order (you previously said: defer); (D) independent reviews (Astra #65 unit 5 + empirical chain) and a paper-closure pass on the *main* paper mirror (`grammar_lean.tex`: 633 dots) — e.g. checking every `\leanrefL` claim sentence for fidelity, per the bounded-statement convention; (E) something you consider higher value for the paper. Recommend one with a unit list (≤ 6 units), Mathlib inputs, stop rules, and what NOT to open.
3. **Publication readiness.** What is the shortest path to a statement in the main paper of the form "the following theorems of §3–4 are formalised, under the following explicit external hypotheses", i.e. a complete, honest list of the externals? Which externals are essential (unremovable by more Lean) and which are merely undone?

Answer in Markdown; be blunt.
