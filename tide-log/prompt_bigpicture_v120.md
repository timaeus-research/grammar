# Consult #120 — AUDIT of Target A (landed) and DESIGN of Target B (compact semianalytic domains)

You are advising a Lean 4 (Mathlib) formalisation of the grammar paper (Gerraty–Murfet). Your consult #119 designed the project "a smooth weighted normalised atlas from resolution data" with Target A first. **Target A is now LANDED, axiom-clean** (grammar main `83d9986`, 716 modules; hironaka fork `sector-atlas` `26f92335d`), following your design with the deviations listed in §2. This consult asks for (1) an audit of what was proved, (2) the design of Target B, (3) small cleanups.

## 1. What is landed (verbatim Lean)

### 1.1 hironaka `Monomialize/Transport/` (namespace `Monomialize.VolumeScaling`)
```
-- SupportedTransport
theorem lintegral_supported (hD : MeasurableSet D) (hV : IsOpen V) (hDV : D ⊆ V) (hψ : ContDiffOn ℝ 1 ψ V) (hN : MeasurableSet N) (hN0 : volume N = 0)
    (hinj : InjOn ψ (D \ N)) {χ} (hsupp : ∀ y, χ y ≠ 0 → y ∈ ψ '' (D \ N)) {ω} (hω : ∀ᵐ x ∂(volume.restrict D), ω x = χ (ψ x)) (a : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ x in D, a (ψ x) * ENNReal.ofReal (ω x) * absDet ψ x = ∫⁻ y, a y * ENNReal.ofReal (χ y)      -- absDet ψ x := ofReal |det (fderiv ℝ ψ x)|
theorem map_supported … : ((volume.restrict D).withDensity fun x => a (ψ x) * ofReal (ω x) * absDet ψ x).map ψ = volume.withDensity fun y => a y * ofReal (χ y)
theorem sum_withDensity_add_residual (μ) (χ : ι → α → ℝ) (hχm) (hχ0 : ∀ i y, 0 ≤ χ i y) (hsum : ∀ y, ∑ i, χ i y ≤ 1) :
    ∑ i, μ.withDensity (fun y => ofReal (χ i y)) + μ.withDensity (fun y => ofReal (1 - ∑ i, χ i y)) = μ
-- ChartWeights
noncomputable def targetWeight (ψ) (D N : Set _) (ω) : (Fin n → ℝ) → ℝ := Function.extend ((D \ N).domRestrict ψ) (fun x : ↥(D \ N) => ω x) 0
theorem targetWeight_apply (hinj : InjOn ψ (D \ N)) (ω) (hu : u ∈ D \ N) : targetWeight ψ D N ω (ψ u) = ω u ;  targetWeight_eq_zero (hy : y ∉ ψ '' (D \ N)) : … = 0
theorem measurable_targetWeight (hD hV hDV hψ hN hinj hωm) : Measurable (targetWeight ψ D N ω)     -- via measurableEmbedding_of_fderivWithin
theorem map_targetWeight (hD hV hDV hψ hψm hN hN0 hinj hωm ha) : ((volume.restrict D).withDensity fun x => a (ψ x) * ofReal (ω x) * absDet ψ x).map ψ = volume.withDensity fun y => a y * ofReal (targetWeight ψ D N ω y)
theorem sum_targetWeight_le_one (hinj : ∀ i, InjOn (g ∘ σ i) (D i \ N i)) (hg : InjOn g (⋃ i, σ i '' (D i \ N i))) (hρ0) (hρ1 : ∀ P, ∑ i, ρ i P ≤ 1) (y) : ∑ i, targetWeight (g ∘ σ i) (D i) (N i) (fun u => ρ i (σ i u)) y ≤ 1
theorem sum_targetWeight_eq_one (hinj) (hg) (hP : g P = y) (hlift : ∀ i, ρ i P ≠ 0 → ∃ u ∈ D i \ N i, σ i u = P) (hsum : ∑ i, ρ i P = 1) : ∑ i, targetWeight … y = 1
-- NormalisedCoreTransport (the output interface; PER-CHART radii)
noncomputable def coreSource (ψ) (ω) (a : ℝ) (prior) : Measure _ := (volume.restrict (centeredBox d a)).withDensity fun u => ofReal (prior (ψ u) * ω u) * absDet ψ u
structure NormalisedCoreTransport (d : ℕ) (K prior : (Fin d → ℝ) → ℝ) where
  ι : Type ; [fin : Fintype ι] ; a : ι → ℝ ; a_pos : ∀ i, 0 < a i
  ψ : ι → (Fin d → ℝ) → (Fin d → ℝ) ; V : ι → Set _ ; V_open ; box_subset_V : ∀ i, centeredBox d (a i) ⊆ V i ; ψ_measurable ; ψ_analytic : ∀ i, AnalyticOnNhd ℝ (ψ i) (V i)
  k : ι → Fin d → ℕ ; k_active : ∀ i, ∃ j, 0 < k i j ; phaseConst : ι → ℝ ; phaseConst_pos ; phase_eq : ∀ i, ∀ u ∈ V i, K (ψ i u) = phaseConst i * ∏ j, u j ^ (2 * k i j)
  h : ι → Fin d → ℕ ; jacUnit ; jacUnit_analytic ; jacUnit_ne_zero : ∀ i, ∀ u ∈ V i, jacUnit i u ≠ 0 ; jac_eq : ∀ i, ∀ u ∈ V i, (fderiv ℝ (ψ i) u).det = jacUnit i u * ∏ j, u j ^ h i j
  ω : ι → (Fin d → ℝ) → ℝ ; ω_measurable ; ω_smoothOn : ∀ i, ContDiffOn ℝ ∞ (ω i) (V i) ; ω_nonneg ; ω_le_one
  tail : Measure _ ; δ : ℝ ; δ_pos ; tail_gap : ∀ᵐ y ∂tail, δ ≤ K y
  transport : ∑ i, (coreSource (ψ i) (ω i) (a i) prior).map (ψ i) + tail = volume.withDensity fun y => ofReal (prior y)
-- CoreTransportAssembly
def activeWalls (k : Fin d → ℕ) : Set _ := {u | ∃ j, 0 < k j ∧ u j = 0}        -- null, closed
structure ChartData (d) (K) -- one chart: a, ψ, V, analytic, k, k_active, phaseConst > 0, phase_eq, h, jacUnit, jac_eq, injOn : InjOn ψ (centeredBox d a \ activeWalls k), ω measurable/smoothOn V/[0,1]
noncomputable def ChartData.χ (C) := targetWeight C.ψ (centeredBox d C.a) (activeWalls C.k) C.ω
noncomputable def assemble (C : ι → ChartData d K) (hpm : Measurable prior) (hp0) (hsum : ∀ y, ∑ i, (C i).χ y ≤ 1) (hδ : 0 < δ)
    (hgap : ∀ᵐ y ∂volume, prior y ≠ 0 → ∑ i, (C i).χ y < 1 → δ ≤ K y) : NormalisedCoreTransport d K prior   -- tail := vol · ofReal (prior · (1 − ∑ χ))
-- ZeroChartExtraction (from WatanabeModificationOn; phase unit already 1 there)
structure EvenChartBox (R : WatanabeModificationOn K W) where
  φ : OpenPartialHomeomorph R.U (Fin d → ℝ) ; mem : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.U ; k h : Fin d → ℕ ; b ; b_analytic : AnalyticOnNhd ℝ b φ.target ; b_ne_zero
  phase_eq : ∀ u ∈ φ.target, K (watanabeRep R.g φ u) = ∏ j, u j ^ (2 * k j) ; jac_eq : ∀ u ∈ φ.target, (fderiv ℝ (watanabeRep R.g φ) u).det = b u * ∏ j, u j ^ h j
  r ρ : ℝ ; r_pos ; r_lt_ρ ; box_subset : centeredBox d ρ ⊆ φ.target ; zero_mem : 0 ∈ φ.target ∧ K (watanabeRep R.g φ 0) = 0
theorem EvenChartBox.injOn_offZero : InjOn (watanabeRep R.g E.φ) {u | u ∈ E.φ.target ∧ K (watanabeRep R.g E.φ u) ≠ 0}
theorem EvenChartBox.zeroSet_eq_walls (hu : u ∈ E.φ.target) : K (watanabeRep R.g E.φ u) = 0 ↔ ∃ j, 0 < E.k j ∧ u j = 0
theorem exists_finite_evenChartBoxes (R) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hC₀ : IsCompact C₀) (hzero : ∀ P ∈ C₀, K (inclusion W (R.g P)) = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (E : ι → EvenChartBox R), C₀ ⊆ ⋃ i, (E i).φ.source ∩ (E i).φ ⁻¹' Metric.ball 0 (E i).r
theorem isCompact_zeroFibre (R) (hKc : ContinuousOn K W) (hS : IsCompact S) (hSW : S ⊆ W) : IsCompact {P | inclusion W (R.g P) ∈ S ∧ K (inclusion W (R.g P)) = 0}
-- ChartCutoffs (M any T2 charted space over ℝ^d; NO IsManifold needed)
theorem exists_chartCutoffs (φ : ι → OpenPartialHomeomorph M (Fin d → ℝ)) (hφ : ∀ i, φ i ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M) (r ρ) (hr : ∀ i, 0 < r i) (hrρ : ∀ i, r i < ρ i) (hbox : ∀ i, centeredBox d (ρ i) ⊆ (φ i).target) :
    ∃ cut : ι → M → ℝ, (∀ i P, 0 ≤ cut i P) ∧ (∀ P, ∑ i, cut i P ≤ 1) ∧ (∃ O, IsOpen O ∧ (∀ i, (φ i).source ∩ (φ i) ⁻¹' centeredBox d (r i) ⊆ O) ∧ ∀ P ∈ O, ∑ i, cut i P = 1) ∧
      (∀ i P, cut i P ≠ 0 → P ∈ (φ i).source ∧ ∀ j, |φ i P j| < ρ i) ∧ (∀ i, Continuous (cut i)) ∧ (∀ i, ∃ Kc, IsCompact Kc ∧ ∀ P ∉ Kc, cut i P = 0) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun u => cut j ((φ i).symm u)) (φ i).target)
-- cut i := (β_i ∘ φ_i, zero off source) · q(∑ β_j ∘ φ_j), β = ∏ smoothTransition((ρ²−u_j²)/(ρ²−r²)), q(t) = smoothTransition(4t−1)/t (0 for t ≤ 1/8)
-- ResolutionBridge
theorem exists_normalisedCoreTransport_of_modification (R : WatanabeModificationOn K W) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hKc : ContinuousOn K W)
    (hpm : Measurable prior) (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) : Nonempty (NormalisedCoreTransport d K prior)
theorem exists_normalisedCoreTransport_of_analyticOnNhd (hU₀ : IsOpen U₀) (hK : AnalyticOnNhd ℝ K U₀) (h0 : K 0 = 0) (hne : ¬ ∀ᶠ x in 𝓝 0, K x = 0) (W : Opens _) (hW : IsConnected ↑W) (h0W : 0 ∈ W) (hWU : ↑W ⊆ U₀)
    (hK0 : ∀ x ∈ W, 0 ≤ K x) (hpm) (hp0) (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) : Nonempty (NormalisedCoreTransport d K prior)
```
Bridge proof (as in your §2): `C₀ := {P | g P ∈ tsupport prior ∧ K (g P) = 0}` compact; finite even chart boxes covering it; cutoffs; chart data with `ψ_i := watanabeRep` totalised by `0` off the target, `ω_i := cut_i ∘ φ_i.symm` totalised, `phaseConst := 1`; `∑ χ_i ≤ 1` by `sum_targetWeight_le_one` with `g` injective on `{K∘g ≠ 0}`; `vol (supp ∩ {K = 0}) = 0` by finitely many chart images of active walls (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`); a.e. gap: a point of the support with `K ≠ 0` and `∑ χ < 1` lifts (surjectivity) to `P ∉ O` (else `sum_targetWeight_eq_one` gives `1`), so `P ∈ g⁻¹(supp) ∖ O` compact where `K ∘ g > 0` (min `δ`); `assemble`.

### 1.2 grammar (namespace `Grammar.SmoothEngine`)
```
structure BridgeInputs (d) where K prior obs ; T : NormalisedCoreTransport d K prior ; K_m : Measurable K ; prior_smooth : ContDiff ℝ ∞ prior ; prior_nonneg ; prior_compact : HasCompactSupport prior ; obs_smooth
theorem BridgeInputs.K_nonneg : ∀ᵐ y ∂X.priorMeasure, 0 ≤ X.K y        -- derived from the transport
theorem NormalisedCoreTransport.hasSmoothCoordFreeExpansion (T) (hK : Measurable K) (hprior : ContDiff ℝ ∞ prior) (hprior0) (hpc : HasCompactSupport prior) (hobs : ContDiff ℝ ∞ obs) :
    HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)) (ofTransport …).decomp.coeff (…).decomp.commonQ (…).decomp.commonD   -- commonD ≤ d − 1
theorem BridgeInputs.coeff_eq_of_transports (T T' : NormalisedCoreTransport d K prior) … (μ q) : (ofTransport T …).decomp.coeff μ q = (ofTransport T' …).decomp.coeff μ q
theorem exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd (hU₀) (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K) (h0 : K 0 = 0) (hne) (W : Opens _) (hW : IsConnected ↑W) (h0W) (hWU) (hK0 : ∀ x ∈ W, 0 ≤ K x)
    (hprior : ContDiff ℝ ∞ prior) (hp0) (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ), HasSmoothCoordFreeExpansion (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)) c Q D
```
Regressions: identity chart no-tail (`ofMonomialNoTail`, through the consumer); in flight: `d = 1` genuine tail (`ofMonomialWithTail`, weight `boxBump r a`, tail `prior·(1−ω)`, gap `c r^{2k}`) and `ofEmptyCores`.

## 2. Deviations from #119 (please confirm they are harmless)
(a) per-chart box radii `a : ι → ℝ` instead of a common box (no diagonal rescaling); (b) `assemble` takes the gap hypothesis a.e. (the zero set inside the support is null, not empty); (c) `hu_tan` is free — Watanabe's chart form in hironaka has phase unit `S = 1` (even case) on the whole chart target, so the paper's unit normalisation is inside the resolution export; (d) cutoffs on `M` need only `T2Space` + `ChartedSpace` (maximal-atlas transition smoothness), not `IsManifold`; (e) the chart map and weight are totalised by `0` off the chart target (measurability), the atlas fields hold on `V := φ.target`; (f) `Measurable K` is an explicit hypothesis of the final theorem.

## 3. Questions
1. **Audit Target A.** Anything wrong or weaker than it looks? Does `exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd` capture the paper's Theorem for the case "prior compactly supported in the open set where `K` is analytic and `≥ 0`"? Is the `K 0 = 0 ∧ K ≢ 0 near 0 ∧ 0 ∈ W` normalisation (inherited from hironaka's `exists_watanabeModificationOn`) a real restriction (a phase with `K > 0` everywhere on `W` or with `K ≡ 0` on `W`: the first should be a pure tail — do we lose it? the second a constant)? How to remove `Measurable K` cleanly (extend `K` off `W` by a measurable representative — but the theorem's function `fun N => ∫ prior·obs·e^{−NK}` only sees `K` on `supp prior ⊆ W`, so we can replace `K` by `indicator W K` or by `K` where `AnalyticOnNhd` gives measurability on `U₀` — `Measurable K` follows from `ContinuousOn K U₀` + `IsOpen U₀` only for the restriction: state the theorem for `K' := fun x => if x ∈ U₀ then K x else 0`?). State the cleanest final form.
2. **Coefficient canonicity for Target A.** We have `∃ c Q D, …` plus presentation independence `coeff_eq_of_transports` for fixed `(K, prior, obs)`. Should the final theorem instead PRODUCE the certificate (`Nonempty (SmoothExpansionCertificate Z)`) so that uniqueness at every `(μ, q)` (`SmoothExpansionCertificate.coeff_eq`) is available downstream? Anything else worth stating now (e.g. `commonD ≤ d − 1` spectrum bound, the lattice `Q = ∏_i 2∏_j k_{ij}`; linearity in `obs` already exists)?
3. **Target B design** (compact semianalytic `W_dom = {π₁ ≥ 0, …, π_r ≥ 0} ∩ (ball)`, prior smooth up to the boundary, the paper's setting). hironaka has: `AnalyticQChartPacket (Δ : BMData n s)` (Bierstone–Milman style, `s` auxiliary functions, phase clause a disjunction), `DomainSectorAtlasBoundary.ofBoundaryMonomials` (selected orthants from sign rules of jointly monomial boundary functions), `WeightedDomainAtlas.domain_ae` (chart domain = selected orthants a.e.). What EXACT export should we ask hironaka for — e.g. a `WatanabeModificationOn` for the PRODUCT `K · ∏ π_j` (or for the tuple) whose even charts also give each `π_j ∘ rep = ε_j · unit_j · monomial_j` with constant sign on the chart target? Is the joint normal crossing form of `K` and all `π_j` obtainable from the existing resolution of a single function (resolve `K·∏π_j`; then each factor is a unit times a monomial locally — the "zero-set ⇒ monomial" lemma is FALSE over ℝ in general, but here the factors are analytic functions dividing a monomial in a local ring where the monomial's factorisation… please give the correct algebraic statement: in the local ring of real-analytic germs at a point of a normal-crossing divisor, an analytic `f` whose zero set is contained in the divisor need not be a unit times a monomial (e.g. `f = x² + y²`)? — so what hypothesis makes the boundary functions monomial in the same charts: resolve them jointly (Hironaka for the ideal/family) — which hironaka currently exports only in the BM89 `Q'` form). Given the exports, design Target B: the interface (`NormalisedCoreTransport` with SELECTED ORTHANTS per chart: `domain_ae`-style `centeredBox ∩ ψ⁻¹' W_dom =ᵐ centeredBox ∩ selectedOrthants signs`, and the transport of `vol|_{W_dom}·prior`), the bridge changes (cutoffs unchanged; the target measure becomes `vol|_{W_dom} · prior`; source measure restricted to selected orthants; the boundary walls are null), the consumer changes (the grammar `SmoothSheetPieces`-style per-(chart, selected orthant) presentations already exist), and the units in order with sizes. If the joint resolution export is the blocker, say precisely what hironaka theorem is needed and how hard it is (the repo has Bierstone–Milman monomialisation infrastructure for families: `BMData n s`, `IsAnalyticQChart` with the disjunction).
4. **Anything cheap and valuable to add now** before moving on (e.g. `prior` only continuous with compact support? — the consumer needs smoothness of `prior∘ψ`; the paper's prior is analytic; keep smooth), and the wording for the paper mirror (one paragraph).
