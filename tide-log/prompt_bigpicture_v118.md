# Consult #118 — AUDIT of the completed smooth-amplitude route (U1–U6c) and the stopping point

You are advising a Lean 4 (Mathlib) formalisation of the grammar paper (Gerraty–Murfet): asymptotic expansion of `Z(N) = ∫_W φ ϕ e^{−NK}` with insertions. Your consults #113–#117 designed the SMOOTH-AMPLITUDE facewise engine (route G5): coordinate Taylor/remainder splitting on chart boxes, monomial box integrals with their power–log expansions, canonical coefficients, parameter families over compact bases, time rescaling for tangential units, smooth core presentations, a scalar certificate with presentation independence, and a weighted-atlas producer with NO stratum-adapted weight hypotheses. Everything you asked for in #117 (landings 1–10 and the three optional refinements) is now landed, axiom-clean (`[propext, Classical.choice, Quot.sound]`), zero `sorry`, in `timaeus-research/grammar` main `1f35998` (711 modules; the two last optional regressions — cube blow-up with a radial smooth prior, d = 0 — are being landed as we speak). This consult is an AUDIT: tell us what is wrong, what is weaker than it looks, what is missing relative to the paper's claim, and where to stop.

## 1. What is landed (verbatim Lean; namespace `Grammar.SmoothEngine` unless noted)

### 1.1 The engine (CCCLXXXVIII–CCCXCII), unchanged since #117
```
theorem smooth_cutoffExpansion (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) :
    CutoffExpansion (Qamb k) (d - 1) (smoothIntegral F h k β b) (smoothCoeff F h k β b)
-- smoothIntegral F h k β b N := ∫ v in box (Fin d) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)
-- Qamb k := 2 * ∏ i, k i ; smoothCoeff = smoothCoeffAtDepth at the canonical cutoff max(⌊μ⌋₊+1, Σh+1)
theorem smoothCoeff_unique ... -- any CutoffExpansion of smoothIntegral on the lattice/degree agrees with smoothCoeff
```
### 1.2 Families, units, cores (CCCXCIII–CCCXCIV)
```
structure SmoothAmplitudeFamily (S : Type*) [TopologicalSpace S] (d : ℕ) (b : ℝ) where
  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  deriv_cont : ∀ m : Fin d → ℕ, ContinuousOn
    (fun z : S × (Fin d → ℝ) => pdMulti m (List.finRange d) (amp z.1) z.2) (Set.univ ×ˢ closedBox d b)

theorem smoothIntegral_beta_eq : smoothIntegral F h k β b N = smoothIntegral F h k 1 b (β * N)   -- time rescaling
theorem smoothCoeff_beta_eq_scaleCoeff ... -- log-degree mixing: c_β(μ,q) = Σ_{j≥q} C(j,q) β^{-μ} (−log β)^{j−q} c_1(μ,j)

theorem cutoffExpansion_integral_beta [CompactSpace S] [FirstCountableTopology S] [OpensMeasurableSpace S]
    (hk : ∀ i, 0 < k i) (hb : 0 < b) {βf : S → ℝ} (hβ : Continuous βf) (hβpos : ∀ s, 0 < βf s) :
    CutoffExpansion (Qamb k) (d - 1) (familyIntegral ν F h k βf b) (familyCoeff ν F h k βf b)
-- familyIntegral ν F h k βf b N := ∫ s, smoothIntegral (F.amp s) h k (βf s) b N ∂ν ; familyCoeff = ∫ s, smoothCoeff (F.amp s) h k (βf s) b μ q ∂ν

structure SmoothCorePresentation (D : LocalisationData U) (target : Measure U) (S : Type*) [TopologicalSpace S] [MeasurableSpace S] (d : ℕ) where
  ν : Measure S ; [isFiniteMeasure_ν : IsFiniteMeasure ν]
  h : Fin d → ℕ ; k : Fin d → ℕ ; k_pos : ∀ i, 0 < k i ; b : ℝ ; b_pos : 0 < b
  βf : S → ℝ ; β_cont : Continuous βf ; β_pos : ∀ s, 0 < βf s
  Φ : S × (Fin d → ℝ) → U ; measurable_Φ : Measurable Φ
  ρ : S × (Fin d → ℝ) → ℝ ; measurable_ρ : Measurable ρ ; nonneg_ρ : ∀ᵐ z ∂smoothChartMeasure ν d b, 0 ≤ ρ z
  amp : SmoothAmplitudeFamily S d b
  amplitude_eq : ∀ᵐ z ∂smoothChartMeasure ν d b, amp z.1 z.2 = ρ z * D.obs (Φ z)
  phase_normal : ∀ᵐ z ∂smoothChartMeasure ν d b, D.phase (Φ z) = βf z.1 * mono (fun i => 2 * k i) z.2
  transport : ((smoothChartMeasure ν d b).withDensity fun z => ((mono h z.2 * ρ z).toNNReal : ℝ≥0∞)).map Φ = target
-- smoothChartMeasure ν d b := ν.prod (volume.restrict (box (Fin d) b)) ; LocalisationData U = (μ, phase ≥ 0 a.e., obs integrable, δ>0)

structure SmoothCoreDecomposition (D : LocalisationData U) (M : ℕ) (S : Fin M → Type*) ... (dim : Fin M → ℕ) where
  core : Fin M → Measure U ; tail : Measure U ; measure_eq : D.μ = ∑ I, core I + tail
  δ₀ : ℝ ; δ₀_pos : 0 < δ₀ ; gap : ∀ᵐ z ∂tail, δ₀ ≤ D.phase z
  chart : ∀ I, SmoothCorePresentation D (core I) (S I) (dim I)
def commonQ : ℕ := ∏ I, Qamb (A.chart I).k        -- commonD := max over I of (dim I − 1)
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ := ∑ I, familyCoeff (A.chart I).ν (A.chart I).amp (A.chart I).h (A.chart I).k (A.chart I).βf (A.chart I).b μ q
theorem cutoffExpansion : CutoffExpansion A.commonQ A.commonD D.Z A.coeff     -- D.Z N := ∫ obs · e^{−N phase} dμ
```
### 1.3 The certificate (CCCXCV; namespace `Grammar`)
```
structure SmoothExpansionCertificate (Z : ℝ → ℝ) where
  Q : ℕ ; Q_pos : 0 < Q ; D : ℕ ; coeff : ℝ → ℕ → ℝ
  coeff_support : ∀ μ q, coeff μ q ≠ 0 → (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D
  expansion : CutoffExpansion Q D Z coeff
theorem SmoothExpansionCertificate.coeff_eq (C₁ C₂ : SmoothExpansionCertificate Z) (μ : ℝ) (q : ℕ) : C₁.coeff μ q = C₂.coeff μ q
def HasSmoothCoordFreeExpansion (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (Q D : ℕ) : Prop :=
  ∀ A : ℝ, (fun N : ℝ => Z N - ∑ q ∈ spectrumLe Q D A, c q.exponent q.logDegree * q.scale N) =o[atTop] fun N : ℝ => N ^ (-A)
theorem SmoothExpansionCertificate.coeff_eq_gCoeff ... -- analytic compatibility: agrees with the analytic engine's coefficients when both apply
```
### 1.4 The producer (CCCXCVI–CCCXCVII)
```
structure SmoothSheetInputs (d : ℕ) where
  K : (Fin d → ℝ) → ℝ ; K_m : Measurable K ; Ω : Set (Fin d → ℝ)
  A : WeightedDomainAtlas d K Ω          -- hironaka: finitely many charts φᵢ : box → ℝ^d, K∘φᵢ = uᵢ · y^{2kᵢ}, |det Dφᵢ| = |jᵢ| · y^{hᵢ},
                                          -- measurable weights ωᵢ ≥ 0 with the EXACT weighted transport Σᵢ (φᵢ)_*(ωᵢ |jᵢ| y^{hᵢ} · vol|boxᵢ∩selected orthants) = vol|_W
  a : ℝ ; ha : 0 < a ; lo_eq : ∀ i j, A.lo i j = -a ; hi_eq : ∀ i j, A.hi i j = a
  K_nonneg : ∀ w ∈ A.W, 0 ≤ K w
  prior obs : (Fin d → ℝ) → ℝ ; prior_nonneg : ∀ w, 0 ≤ prior w
  prior_smooth : ContDiff ℝ ∞ prior ; obs_smooth : ContDiff ℝ ∞ obs
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  φ_smooth : ∀ i, ContDiff ℝ ∞ (A.φ i) ; ω_smooth : ∀ i, ContDiff ℝ ∞ (A.ω i)
  jacAbs_smooth : ∀ i, ContDiff ℝ ∞ fun y => |A.jacUnit i y|
  hu_tan : ∀ i (w w' : Fin d → ℝ), (∀ j, ¬ 0 < A.k i j → w j = w' j) → A.phaseUnit i w = A.phaseUnit i w'

noncomputable def decomp : SmoothCoreDecomposition X.D (Fintype.card X.PIdx) (fun I => Base (X.act (X.en I).1) X.a) (fun I => X.da (X.en I))
-- one core per (chart, selected orthant); base = [0,a]^{inactive}; active box; T s v = refl σ (glue …); tail = 0 (the pieces exhaust vol|_W)
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) X.decomp.coeff X.decomp.commonQ X.decomp.commonD
theorem coeff_eq_of_inputs {Y : SmoothSheetInputs d} (hW : X.A.W = Y.A.W) (hK : X.K = Y.K) (hprior : X.prior = Y.prior) (hobs : X.obs = Y.obs) (μ : ℝ) (q : ℕ) :
    X.decomp.coeff μ q = Y.decomp.coeff μ q
```
### 1.5 The refinements (CCCXCVIII–CCCXCIX)
```
theorem exists_contDiff_zero_one_nhds {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :   -- E finite-dimensional
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ᶠ x in 𝓝ˢ s, χ x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1
theorem exists_contDiff_eqOn_of_contDiffOn {f : E → ℝ} {U C : Set E} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ EqOn g f C ∧ ((∀ x ∈ U, 0 ≤ f x) → ∀ x, 0 ≤ g x)
structure SmoothSheetNhdsInputs (d : ℕ)  -- as SmoothSheetInputs but: U open, W_closed : IsClosed A.W, W_sub : A.W ⊆ U,
  -- prior_nonneg : ∀ w ∈ U, 0 ≤ prior w ; prior_smooth : ContDiffOn ℝ ∞ prior U ; obs_smooth : ContDiffOn ℝ ∞ obs U
theorem SmoothSheetNhdsInputs.hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace X.A.W X.K fun w => X.prior w * X.obs w) X.toInputs.decomp.coeff X.toInputs.decomp.commonQ X.toInputs.decomp.commonD
theorem SmoothSheetNhdsInputs.coeff_eq_of_inputs {Y : SmoothSheetInputs d} (hW) (hK) (hprior : EqOn X.prior Y.prior X.A.W) (hobs : EqOn X.obs Y.obs X.A.W) (μ q) : X.toInputs.decomp.coeff μ q = Y.decomp.coeff μ q

noncomputable def SmoothExpansionCertificate.add (C₁ : SmoothExpansionCertificate Z₁) (C₂ : SmoothExpansionCertificate Z₂) : SmoothExpansionCertificate fun N => Z₁ N + Z₂ N  -- Q₁Q₂, max D
theorem SmoothSheetInputs.coeff_add {X Y Z : SmoothSheetInputs d} (hW : X.A.W = Z.A.W) (hW' : Y.A.W = Z.A.W) (hK : X.K = Z.K) (hK' : Y.K = Z.K)
    (hprior : X.prior = Z.prior) (hprior' : Y.prior = Z.prior) (hobs : Z.obs = fun w => X.obs w + Y.obs w) (μ : ℝ) (q : ℕ) :
    Z.decomp.coeff μ q = X.decomp.coeff μ q + Y.decomp.coeff μ q
theorem SmoothSheetInputs.coeff_smul ... (hobs : Z.obs = fun w => r * X.obs w) : Z.decomp.coeff μ q = r * X.decomp.coeff μ q
```
### 1.6 The regression (CD; hironaka fork `sector-atlas` 001c545b6)
```
-- hironaka: shiftedAtlasOf (i₀ i₁ : Fin n) (hne : i₀ ≠ i₁) {a} (ha : 0 < a) (s : ℝ) (τ : (Fin n → ℝ) → ℝ) (hτm : Measurable τ) (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1)
--   (h1 : ∀ x, x ∈ centeredBox n a → x ∉ shift i₁ s '' centeredBox n a → τ x = 1) (h2 : ∀ x, x ∈ shift i₁ s '' centeredBox n a → x ∉ centeredBox n a → τ x = 0) :
--   WeightedDomainAtlas n (monoPhase (Pi.single i₀ 1)) (shiftedSet i₁ a s)        -- weights τ∘φ₁, (1−τ)∘φ₂ ; the old ramp atlas is the special case τ x = ρ(x_{i₁})
structure SmoothRamp (i₁ : Fin n) (a s : ℝ)   -- τ smooth, 0 ≤ τ ≤ 1, the two boundary conditions
noncomputable def smoothOverlapInputs (hne : i₀ ≠ i₁) (ha : 0 < a) (ρ : SmoothRamp i₁ a s) (hP : ContDiff ℝ ∞ P) (hP0 : ∀ w, 0 ≤ P w) (hQ : ContDiff ℝ ∞ Q) : SmoothSheetInputs n
theorem smoothOverlap_hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion (globalLaplace (shiftedSet i₁ a s) (fun x => x i₀ ^ 2) fun w => P w * Q w) (smoothOverlapInputs …).decomp.coeff (…).commonQ (…).commonD
theorem coeff_eq_of_ramp (ρ' : SmoothRamp i₁ a s) : (smoothOverlapInputs hne ha ρ hP hP0 hQ).decomp.coeff = (smoothOverlapInputs hne ha ρ' hP hP0 hQ).decomp.coeff
-- activeRamp x := 1 − σ(2·overlapCoord x − 1 + σ(x_{i₀}²)), σ = Real.smoothTransition, overlapCoord x = (x_{i₁} − (s − a))/(2a − s)
theorem activeRamp_not_ω_indep (hne) (ha) (hs0 : 0 < s) (hs : s < 2 * a) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ¬ ∀ i j, 0 < ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).k i j → ∀ y, |y j| ≤ t₀ → (…).ω i (Function.update y j 0) = (…).ω i y
theorem coeff_active_eq_coeff_tangential ...   -- active-ramp coefficients = tangential-ramp coefficients
```

## 2. Recorded non-claims / hypotheses we know about
(a) The chart data (`φᵢ`, `ωᵢ`, `|jᵢ|`) are GLOBALLY `C^∞` on `ℝ^d` (only the prior/observable have the neighbourhood version). (b) `hu_tan`: the phase unit `uᵢ` does not depend on the ACTIVE coordinates of chart `i` (the exact chart form gives `K∘φᵢ = uᵢ·y^{2kᵢ}` with `uᵢ` a unit; we assume it is tangential). (c) `jacAbs_smooth`: `|jᵢ|` smooth (fine if `jᵢ` is a nonvanishing unit). (d) Symmetric boxes `[−a,a]^d` with a single `a` for all charts; selected orthants; `K ≥ 0` on `W` only. (e) Coefficients are scalars `c_{μ,q}` (intrinsic by `coeff_eq_of_inputs`/`coeff_eq`), linear in the observable, NOT a jet field (no finite-order dependence statement). (f) Existence of a smooth `WeightedDomainAtlas` for a given `(W, K)` is an INPUT (consult #112 stop: from Watanabe/Hironaka we have local chart form; a smooth partition of unity subordinate to the chart images is the missing constructor — Mathlib has smooth partitions of unity on finite-dimensional manifolds, and CCCXCVIII now has the smooth Urysohn lemma on `ℝ^d`). (g) `HasSmoothCoordFreeExpansion` is stated for `globalLaplace W K (prior·obs) N = ∫_W prior·obs·e^{−NK}` with the little-o remainder at every order `A`; the log-degree bound is `commonD = max_I (dim active_I − 1)`.

## 3. Questions — please answer concretely, in Lean-ready terms
1. **Audit.** Is anything above WRONG or weaker than it appears? In particular: (i) is `hu_tan` (tangential phase unit) a genuine restriction relative to the paper's normal-crossing form, or can every exact-chart-form atlas be refined to satisfy it (e.g. by absorbing the active-coordinate dependence of `uᵢ` via a further coordinate change `y_j ↦ u^{1/2k_j} y_j` — which is not available as a chart move here)? Is there a cheap Lean workaround (e.g. allow `uᵢ` smooth positive and treat `uᵢ(y)` as part of the amplitude at the cost of the time-rescaling step: `e^{−N u(y) y^{2k}}` with `u` non-tangential — what breaks in the facewise engine)? (ii) Are the a.e. formulations (`amplitude_eq`, `phase_normal`, `nonneg_ρ` a.e. on `ν ⊗ vol|box`) adequate for the transport identity, or is there a subtle measurability/null-set gap? (iii) Is `commonQ = ∏_I 2∏ᵢ k_{I,i}` the right lattice statement (the paper: exponents in `Q⁻¹ℕ`), or should we record the finer statement that the coefficients are supported on `⋃_I (2∏ᵢ k_{I,i})⁻¹ℕ`? (iv) Any concern with `coeff_support`-based uniqueness (`coeff_eq_of_lattices`) when the two lattices differ?
2. **Distance to the paper's statement.** What exactly separates `SmoothSheetInputs.hasSmoothCoordFreeExpansion` from the paper's theorem "for `K` analytic ≥ 0 on a compact semianalytic `W` with smooth prior and observable, `Z(N)` has the power–log expansion with intrinsic coefficients"? List the gaps in order and estimate their Lean cost: (a) existence of the smooth weighted atlas from hironaka's resolution (what constructor: partition of unity subordinate to chart images? how to get the EXACT weighted transport identity `Σᵢ (φᵢ)_*(ωᵢ|jᵢ|y^{hᵢ}·vol) = vol|_W` — is it just `ωᵢ∘φᵢ⁻¹` summing to 1 on `W` a.e. plus the change of variables per chart? does the frontier of `W` and the exceptional divisor (measure zero) cause trouble?); (b) global vs neighbourhood smoothness of chart data; (c) `hu_tan`; (d) anything else. Which of these would you do NEXT, and which should be recorded as the final stopping point of the Lean programme?
3. **The coefficient functional.** With linearity in the observable landed, is a "smooth jet" statement worth pursuing — e.g. `c_{μ,q}(obs)` depends only on the derivatives of `obs` of order `≤ ord(μ)` along the strata, or the analogue of the analytic `jetFunctional` (CCCL–CCCLIII)? If yes, state the target theorem precisely; if no, say why the scalar linear functional is the right final form.
4. **Wording for the paper mirror** (`grammar_lean.tex`, remark-level): give a 5–8 sentence paragraph we can adapt, stating precisely what is formalised (inputs, conclusion, intrinsic coefficients, no stratum-adapted weight hypotheses, regressions) and the non-claims.
5. **Stopping point.** Should the smooth programme now be CLOSED (with items from Q2 recorded as future work), or is there one more unit with a high value/cost ratio? Be decisive.
