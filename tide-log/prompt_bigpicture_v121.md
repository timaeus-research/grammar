# Consult #121 — AUDIT of Target B (landed) and the stopping point of the "atlas from resolution data" project

You are advising a Lean 4 (Mathlib) formalisation of the grammar paper (Gerraty–Murfet). Consult #119 designed the project, #120 audited Target A (passed) and designed Target B. **Target B is now LANDED, axiom-clean** (grammar main `5e14080`, 719 modules; hironaka fork `sector-atlas` `9ca3ad986`). This consult asks for an audit and the stopping decision.

## 1. What is landed (verbatim Lean; hironaka namespace `Monomialize.VolumeScaling`, grammar `Grammar.SmoothEngine`)

### 1.1 The audit of the export (what we found in hironaka, then used)
No family monomialisation existed, but: `watanabe_thm_2_3_of_isConnected_of_bo` runs on an arbitrary single analytic `F` (instantiating the ideal-sheaf engine `resolveFamExt` at the principal ideal), so we applied it to the PRODUCT `F := K · ∏ π_ℓ`; and the factor-splitting lemma in the ring of convergent power series was already proved and certified (`exists_nhd_eq_unit_mul_monomial`, resting on `prime_convX` and `Conv` being a UFD). Ambient nonnegativity of `K` is the paper's hypothesis ("an open set `W^{(R)} ⊇ W` on which `K ≥ 0`"), so the even-chart interface stands.

### 1.2 hironaka units
```
-- FactorSplitting (delegated)
theorem exists_evenBox_factors (hV : IsOpen V) (h0 : 0 ∈ V) {K} (hK : AnalyticOnNhd ℝ K V) (hKnn : ∀ x ∈ V, 0 ≤ K x) {r} (π : Fin r → …) (hπ) {S} (hS : S ≠ 0) (θ)
    (hprod : ∀ x ∈ V, K x * ∏ ℓ, π ℓ x = S * ∏ j, x j ^ θ j) :
    ∃ a, 0 < a ∧ centeredBox d a ⊆ V ∧ ∃ V', IsOpen V' ∧ IsPreconnected V' ∧ centeredBox d a ⊆ V' ∧ V' ⊆ V ∧ ∃ (k : Fin d → ℕ) v₀, AnalyticOnNhd ℝ v₀ V' ∧ (∀ x ∈ V', 0 < v₀ x) ∧
      (∀ x ∈ V', K x = v₀ x * ∏ j, x j ^ (2 * k j)) ∧ ∃ m v (ε : Fin r → ℝ), (∀ j, 2 * k j + ∑ ℓ, m ℓ j = θ j) ∧ (∀ ℓ, AnalyticOnNhd ℝ (v ℓ) V') ∧ (∀ ℓ, ε ℓ = 1 ∨ ε ℓ = -1) ∧
      (∀ ℓ, ∀ x ∈ V', 0 < ε ℓ * v ℓ x) ∧ ∀ ℓ, ∀ x ∈ V', π ℓ x = v ℓ x * ∏ j, x j ^ m ℓ j
-- (the complementary factor is obtained by the identity theorem on the polydisc, not a second germ-lemma application; parity by evaluating at (ε/2)·1 and its sign flip; constant sign by IsPreconnected.intermediate_value)
-- UnitAbsorption (delegated): absorb v j₀ k u := Function.update u j₀ (unitRoot v (2 k j₀) u * u j₀), unitRoot := exp (n⁻¹ log v)
structure AbsorbingChange (v) (j₀) (k) (V) -- e : OpenPartialHomeomorph, coe_e : ⇑e = absorb v j₀ k, 0 ∈ e.source ⊆ V, v analytic positive on e.source, e.symm analytic, det D e.symm ≠ 0
theorem exists_absorbingChange (hV : IsOpen V) (h0V : 0 ∈ V) (hv : AnalyticOnNhd ℝ v V) (hv0 : ∀ u ∈ V, 0 < v u) (j₀) (k) : Nonempty (AbsorbingChange v j₀ k V)   -- via HasStrictFDerivAt.toOpenPartialHomeomorph (derivative at 0 diagonal)
theorem phase_comp_symm (hk : 0 < k j₀) (hu') : v (Φ.e.symm u') * ∏ j, Φ.e.symm u' j ^ (2*k j) = ∏ j, u' j ^ (2*k j)
theorem symm_apply_self : Φ.e.symm u' j₀ = Φ.w u' * u' j₀   -- w analytic positive; other coordinates unchanged
theorem unit_mul_monomial_comp_symm … -- any c·∏u^m on the source becomes unitComp c m · ∏u'^m on the target (same exponents); Jacobian likewise
def chart φ := (φ.restrOpen (φ.source ∩ φ⁻¹' Φ.e.source) _).trans Φ.e ; chart_mem_maximalAtlas ; watanabeRep_chart : watanabeRep g (Φ.chart φ) = watanabeRep g φ ∘ Φ.e.symm
theorem watanabeRep_chart_phase (hk) (hVt) (hK : ∀ u ∈ Φ.e.source, K (watanabeRep g φ u) = v u * ∏ u^(2k)) : ∀ u' ∈ (Φ.chart φ).target, K (watanabeRep g (Φ.chart φ) u') = ∏ u'^(2k)
-- ChartDomainReading (delegated)
def chartAdmissibleSigns (zero : Fin r → Prop) [DecidablePred zero] (ε) (m) : Finset (CoordSign d) := univ.filter fun σ => ∀ ℓ, ¬ zero ℓ → ε ℓ * ∏ j, sgn σ j ^ m ℓ j = 1
theorem chart_domain_ae (π) (zero) (ε) (m) (v) {ψ} {a} (hΩ : ∀ u ∈ centeredBox d a, ψ u ∈ Ω) (hzero) (hmono : ∀ ℓ, ¬ zero ℓ → ∀ u ∈ box, π ℓ (ψ u) = v ℓ u * ∏ u^{m ℓ}) (hε) (hv : … 0 < ε ℓ * v ℓ u) :
    (centeredBox d a ∩ ψ ⁻¹' boundaryDomain Ω π) =ᵐ[volume] (centeredBox d a ∩ selectedOrthants (chartAdmissibleSigns zero ε m))     -- boundaryDomain Ω π := Ω ∩ {w | ∀ j, 0 ≤ π j w}
-- DomainCoreTransport (mine)
structure NormalisedDomainCoreTransport (d) (K prior) (Wdom) -- chart fields as NormalisedCoreTransport (per-chart radii, exact even phase c_i ∏u^{2k}, analytic Jacobian unit, smooth weights) + sectors : ι → Finset (CoordSign d), tail, δ, tail_gap,
  transport : ∑ i, (sectorSource (ψ i) (ω i) (a i) (sectors i) prior).map (ψ i) + tail = (volume.restrict Wdom).withDensity fun y => ofReal (prior y)
  -- sectorSource ψ ω a S prior := (volume.restrict (centeredBox d a ∩ selectedOrthants S)).withDensity fun u => ofReal (prior (ψ u) * ω u) * absDet ψ u
structure ChartData (d) (K) -- … walls : Set _, walls_measurable, walls_null, injOn : InjOn ψ (centeredBox d a \ walls)   (generalised from the active walls)
structure DomainChartData (d) (K) (Wdom) extends ChartData d K where sectors ; domain_ae : (centeredBox d a ∩ ψ ⁻¹' Wdom) =ᵐ[volume] (centeredBox d a ∩ selectedOrthants sectors)
theorem DomainChartData.χ_eq_zero_ae : ∀ᵐ y, y ∉ Wdom → C.χ y = 0     -- χ := targetWeight ψ (box ∩ sel) walls ω; the sector minus the domain preimage is null, its chart image null
noncomputable def assembleDomain (C : ι → DomainChartData d K Wdom) (hW : MeasurableSet Wdom) (hpm) (hp0) (hsum : ∀ y, ∑ i, (C i).χ y ≤ 1) (hδ : 0 < δ)
    (hgap : ∀ᵐ y ∂volume, y ∈ Wdom → prior y ≠ 0 → ∑ i, (C i).χ y < 1 → δ ≤ K y) : NormalisedDomainCoreTransport d K prior Wdom   -- tail := (vol|_Wdom)·ofReal (prior·(1 − ∑χ))
-- DomainBridge (mine)
structure ProductChartBox (R : WatanabeModificationOn F W) (K) (π : Fin r → …) -- φ ∈ maximalAtlas, rIn < rOut, V open with centeredBox rOut ⊆ V ⊆ φ.target, k active, phase_eq : ∀ u ∈ V, K (rep u) = ∏ u^(2k) (EXACT),
  -- h b (analytic, ≠ 0 on V), jac_eq, zero ε m v with hzero/hmono/hε/hv on V, F_ne_zero : ∀ u ∈ V, u ∉ allWalls d → F (rep u) ≠ 0      (allWalls d := {u | ∃ j, u j = 0})
noncomputable def ProductChartBox.domainChartData (cut) … : DomainChartData d K (boundaryDomain W π)   -- walls := allWalls d; weights := cut ∘ φ.symm totalised
theorem exists_normalisedDomainCoreTransport_of_cover (R : WatanabeModificationOn F W) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hKc : ContinuousOn K W) (hpm) (hp0) (hpW : tsupport prior ⊆ W)
    (hWm : MeasurableSet (boundaryDomain W π)) (hSWc : IsCompact (tsupport prior ∩ boundaryDomain W π)) {ι} [Finite ι] (E : ι → ProductChartBox R K π)
    (hcover : {P | R.gv P ∈ tsupport prior ∩ boundaryDomain W π ∧ K (R.gv P) = 0} ⊆ ⋃ i, (E i).φ.source ∩ (E i).φ ⁻¹' Metric.ball 0 (E i).rIn)
    (hnull : volume (tsupport prior ∩ boundaryDomain W π ∩ {y | F y = 0}) = 0) : Nonempty (NormalisedDomainCoreTransport d K prior (boundaryDomain W π))
-- proof: cutoffs on the resolution space (unchanged), ∑χ ≤ 1 via g injective off {F ≠ 0} (sum_targetWeight_le_one), exceptional set = (supp ∩ Wdom ∩ {F = 0}) ∪ ⋃ ψ_i(box ∩ allWalls) (null), lifts of the rest: if in O then ∑χ = 1 (sum_targetWeight_eq_one with the pointwise domain reading mem_domain_iff), else K∘g ≥ δ on the compact g⁻¹(supp ∩ Wdom) ∖ O
theorem volume_zeroSet_inter_compact (R : WatanabeModificationOn F W) (hFc : ContinuousOn F W) (hT : IsCompact T) (hTW : T ⊆ W) : volume (T ∩ {y | F y = 0}) = 0   -- raw Watanabe charts at F-zeros
-- ProductChartExtraction (delegated)
theorem exists_productChartBox (R : WatanabeModificationOn F W) (hF : ∀ x ∈ W, F x = K x * ∏ ℓ, π ℓ x) (hK : AnalyticOnNhd ℝ K W) (hπ) (hK0 : ∀ x ∈ W, 0 ≤ K x) {P} (hP : K (inclusion W (R.g P)) = 0) : ∃ E : ProductChartBox R K π, P ∈ E.φ.source ∧ E.φ P = 0
theorem exists_finite_productChartBoxes … (hC₀ : IsCompact C₀) (hzero : ∀ P ∈ C₀, K (…) = 0) : ∃ ι (_ : Fintype ι) (E : ι → ProductChartBox R K π), C₀ ⊆ ⋃ i, (E i).φ.source ∩ (E i).φ ⁻¹' Metric.ball 0 (E i).rIn
-- DomainBridgeFinal (mine)
theorem exists_normalisedDomainCoreTransport_of_analyticOnNhd {U₀} (hU₀ : IsOpen U₀) (hK : AnalyticOnNhd ℝ K U₀) (hπ : ∀ ℓ, AnalyticOnNhd ℝ (π ℓ) U₀) (h0 : K 0 * ∏ ℓ, π ℓ 0 = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, K x * ∏ ℓ, π ℓ x = 0) (W : Opens _) (hW : IsConnected ↑W) (h0W : 0 ∈ W) (hWU : ↑W ⊆ U₀) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hWc : IsCompact (boundaryDomain W π))
    (hpm) (hp0) (hpW : tsupport prior ⊆ W) : Nonempty (NormalisedDomainCoreTransport d K prior (boundaryDomain W π))
```
### 1.3 grammar
```
-- SmoothDomainConsumer (delegated): DomainBridgeInputs (compact Wdom, T, Measurable K, smooth prior ≥ 0, smooth obs); pieces over Σ i, ↥(sectors i); decomp with tail := T.tail
theorem NormalisedDomainCoreTransport.hasSmoothCoordFreeExpansion (T) (hW : IsCompact Wdom) (hK : Measurable K) (hprior) (hprior0) (hobs) :
    HasSmoothCoordFreeExpansion (fun N => ∫ y in Wdom, prior y * obs y * Real.exp (-N * K y)) (ofTransport …).decomp.coeff … .commonQ … .commonD      -- commonD ≤ d − 1; certificate; coeff_eq_of_transports
-- regressions: identity chart on the half box with the positive orthant selected; the half line ∫_0^a prior·obs·e^{−N c y^{2k}} with log degree 0
-- SmoothTargetB (mine)
theorem exists_hasSmoothCoordFreeExpansion_domain_of_analyticOnNhd {U₀} (hU₀) {K} (hK : AnalyticOnNhd ℝ K U₀) (hKm : Measurable K) {π : Fin r → …} (hπ) (h0 : K 0 * ∏ ℓ, π ℓ 0 = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, K x * ∏ ℓ, π ℓ x = 0) (W : Opens _) (hW : IsConnected ↑W) (h0W : 0 ∈ W) (hWU) (hK0 : ∀ x ∈ W, 0 ≤ K x) (hWc : IsCompact (boundaryDomain W π))
    {prior obs} (hprior : ContDiff ℝ ∞ prior) (hp0) (hpW : tsupport prior ⊆ W) (hobs : ContDiff ℝ ∞ obs) :
    ∃ (c : ℝ → ℕ → ℝ) (Q D : ℕ), HasSmoothCoordFreeExpansion (fun N => ∫ y in boundaryDomain W π, prior y * obs y * Real.exp (-N * K y)) c Q D
theorem exists_smoothExpansionCertificate_domain_of_analyticOnNhd … : ∃ C : SmoothExpansionCertificate (globalLaplace (boundaryDomain W π) K fun y => prior y * obs y), C.D ≤ d - 1
```
Target A cleanups (CDV, delegated) exist: indicator representative removing `Measurable K`, translation to any zero, positive phase as a pure tail, certificate-facing statement, coefficient uniqueness.

## 2. Questions
1. **Audit Target B.** Anything wrong or weaker than it appears? Specifically: (i) the hypotheses `h0 : K 0 * ∏ π 0 = 0` and `hne` refer to the PRODUCT at the origin (inherited from `exists_watanabeModificationOn`) — is the intended hypothesis set for the paper "`0 ∈ Wdom ∩ {K = 0}`" or arbitrary? (ii) `IsCompact (boundaryDomain W π)` — is requiring the closed semianalytic domain to be compact and inside the OPEN `W` where `K ≥ 0` and everything is analytic the right reading of the paper (the paper's `W` compact, `K ≥ 0` on an open `W^{(R)} ⊇ W`)? It forces `Wdom` to stay away from `∂W`; the user of the theorem includes a ball inequality `R² − |x|²` among the `π_ℓ`. (iii) `tsupport prior ⊆ W` with the prior smooth on all of `ℝ^d`: the paper's prior is smooth (analytic) on a neighbourhood of `Wdom`; a compactly supported cutoff equal to `1` near `Wdom` makes `prior` compactly supported in `W` without changing `∫_{Wdom}` — should we add that wrapper (prior smooth on an open `U ⊇ Wdom`, `U ⊆ W`), and is `HasCompactSupport prior` then redundant? (iv) `Measurable K`: same indicator wrapper as Target A. (v) Boundary factors identically zero (`zero ℓ`) never arise in our extraction (the split lemma handles every factor since `F ≢ 0` near each zero); is that airtight — a boundary function identically zero on `W` makes `F ≡ 0` and is excluded by `hne`; a boundary function vanishing identically on a CHART but not on `W` cannot happen by the identity theorem on the connected `W`… but the chart image is connected? (the chart target is an open subset of `ℝ^d`; `π_ℓ∘rep ≡ 0` on it would give `π_ℓ ≡ 0` on the open set `rep(target) ∩ W`, hence on `W`) — confirm.
2. **Distance to the paper's Theorem.** With Targets A and B, what remains between the Lean statements and the paper's theorem for `Z_n[φ] = ∫_W φ e^{−nK} ϕ dw` (`W` compact semianalytic, `K` analytic ≥ 0 on a neighbourhood, prior analytic, observable smooth)? List remaining gaps (normalisation of the origin; positive-phase and zero-phase components; the prior only on a neighbourhood; anything about the domain such as `Wdom = W` exactly vs `W ∩ {π ≥ 0}` with an ambient open set) and their cost. Which would you do NOW (S-sized) before closing?
3. **Coefficient structure.** Same as Target A: intrinsic scalar coefficients, `D ≤ d − 1`, linear in the observable. Anything cheap worth adding (e.g. the leading exponent equals the RLCT of the pair `(K, Wdom)` when that is defined in the library — the repo has RLCT/`HasLLCExponentsOn` from hironaka's `E5` readout; is a bridge "leading exponent of the certificate = λ" a sensible S/M unit or a separate project)?
4. **Stopping decision and wording.** Should the project be CLOSED now (with a non-claims list), and what is the 6–8 sentence paper-mirror paragraph for Target B (to follow the Target A paragraph)? Give the acceptance statement in one sentence.
