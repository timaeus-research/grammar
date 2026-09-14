# Consult #127 — AUDIT of Theorem D level (1) (units D0–D4 landed) and DESIGN of level (2): the intrinsic depth/resonance stratification (D5–D8)

You designed Theorem D in #126 (three levels: (1) intrinsic coefficient functional on the FIXED measured resolution `(U, π, μ_U)`; (2) intrinsic depth/resonance filtration from a chart-invariance lemma; (3) smooth stratum-kernel presentations of RESTRICTIONS). Level (1) and the invariance lemma are LANDED, axiom-clean, in hironaka (fork `dmurfet/hironaka@sector-atlas`, rev `34cbdee3e`) and grammar (main `f4b5fb9`, 741 modules; rows CDXXVII–CDXXIX). Please (A) audit the landed statements against the design, (B) design level (2) in Lean-shaped units, (C) give the paper-facing paragraph for level (1).

## 1. Landed — hironaka (`Monomialize.Transport`), verbatim signatures
```
-- D0: ResolvedMeasure.lean. R : WatanabeModificationOn K W (resolved analytic manifold R.U, blow-down g : U → W, proper, surjective,
-- isoOff : IsAnalyticIsoOver g {x | K x ≠ 0}); R.gv : R.U → Fin d → ℝ the blow-down into ℝ^d; hKc : ContinuousOn K W.
instance : MeasurableSpace R.U := borel R.U ; instance : BorelSpace R.U
def priorDensityMeasure (prior) : Measure (Fin d → ℝ) := volume.withDensity fun y => ENNReal.ofReal (prior y)
def regularLocus K W : Set (Fin d → ℝ) := {y | y ∈ W ∧ K y ≠ 0}                     -- isOpen_regularLocus (hKc)
def offDivisor : Set R.U := {P | K (R.gv P) ≠ 0}                                        -- isOpen (hKc); compl = {K∘gv = 0}
theorem volume_inter_zeroSet_eq_zero (R) (hK0) (hKc) {S} (hSc : IsCompact S) (hSW : S ⊆ W) : volume (S ∩ {y | K y = 0}) = 0
def offDivisorHomeomorph (hKc) : R.offDivisor ≃ₜ regularLocus K W        -- from isoOff: BijOn + local diffeo ⇒ open map
def liftMeasure (hKc) (ν : Measure (Fin d → ℝ)) : Measure R.U :=              -- ν|regular, transported through the inverse, extended by 0
  ((ν.comap (Subtype.val : regularLocus K W → _)).map (R.offDivisorHomeomorph hKc).toMeasurableEquiv.symm).map (Subtype.val : R.offDivisor → R.U)
theorem liftMeasure_zeroSet : R.liftMeasure hKc ν {P | K (R.gv P) = 0} = 0
theorem map_gv_liftMeasure : (R.liftMeasure hKc ν).map R.gv = ν.restrict (regularLocus K W)
theorem eq_liftMeasure_of_map_gv (μ : Measure R.U) (hμD : μ {P | K (R.gv P) = 0} = 0) (hμg : μ.map R.gv = ν) : μ = R.liftMeasure hKc ν   -- UNCONDITIONAL uniqueness
def resolvedMeasure (hKc) (prior) : Measure R.U := R.liftMeasure hKc (priorDensityMeasure prior)
theorem map_gv_resolvedMeasure (hK0) (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ W) : (R.resolvedMeasure hKc prior).map R.gv = priorDensityMeasure prior
theorem isFiniteMeasure_resolvedMeasure … (hint : Integrable prior) ; theorem resolvedMeasure_compl_preimage_tsupport … : μ_U (R.gv ⁻¹' tsupport prior)ᶜ = 0
theorem isCompact_gv_preimage_tsupport (hpc) (hpW) : IsCompact (R.gv ⁻¹' tsupport prior)
theorem integral_boltzmann_resolvedMeasure … (hpm : Measurable prior) (hp0) (hf : Continuous f) (hKm : Measurable K) (t) :
  ∫ P, f (R.gv P) * exp (-t * K (R.gv P)) ∂(R.resolvedMeasure hKc prior) = ∫ y, f y * exp (-t * K y) * prior y
theorem contMDiff_gv : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω R.gv
-- D1: ResolvedCoreTransport.lean
structure ResolvedCoreTransport (R) (hKc) (prior) where
  T : NormalisedCoreTransport d K prior                       -- the Euclidean core transport of #119 (charts ψ i, boxes a i, weights ω i, phase ∏u^{2k}, Jacobian b·∏u^h, tail with gap δ, T.transport : ∑ (coreSource i).map (ψ i) + tail = prior·vol)
  φ : T.ι → OpenPartialHomeomorph R.U (Fin d → ℝ) ; φ_mem : ∀ i, φ i ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.U
  V_eq : ∀ i, T.V i = (φ i).target ; ψ_eq : ∀ i, ∀ u ∈ (φ i).target, T.ψ i u = R.gv ((φ i).symm u)
def coreU i := (coreSource i).map (φ i).symm ; def tailU := R.liftMeasure hKc T.tail
theorem transport (hK0) (hpc) (hpW) : ∑ i, X.coreU i + X.tailU = R.resolvedMeasure hKc prior     -- by uniqueness of divisor-null lifts
theorem integral_resolvedMeasure_eq … (hF : Integrable F μ_U) : ∫ F ∂μ_U = ∑ i, ∫ u, F ((φ i).symm u) ∂(core i) + ∫ F ∂tailU
theorem ae_tailU_gap … : ∀ᵐ P ∂X.tailU, X.T.δ ≤ K (R.gv P)
def chartInv i : (Fin d → ℝ) → R.U   -- (φ i).symm totalised measurably; coreU_eq_map_chartInv; ψ_eq_gv_chartInv
theorem contDiffOn_comp_symm {F : R.U → ℝ} (hF : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F) (i) : ContDiffOn ℝ ∞ (fun u => F ((φ i).symm u)) (φ i).target
theorem exists_resolvedCoreTransport_of_modification (R) (hK0) (hKc) (hpm) (hp0) (hpc) (hpW) : Nonempty (ResolvedCoreTransport R hKc prior)
```
## 2. Landed — grammar (`Grammar.SmoothEngine.ResolvedData`), rows CDXXVIII–CDXXIX
```
structure ResolvedData (d) where K; W : Opens; R : WatanabeModificationOn K W; hKc; hK0; K_m : Measurable K; prior; prior_smooth : ContDiff ℝ ∞ prior; prior_nonneg; prior_compact; prior_W : tsupport prior ⊆ W;
  F : R.U → ℝ ; F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F           -- F smooth on the MANIFOLD, not a pull-back
def withF (G) (hG) : ResolvedData d := { Ξ with F := G, F_smooth := hG }
def μU := R.resolvedMeasure hKc prior ; def Z (N) : ℝ := ∫ P, F P * exp (-N * K (R.gv P)) ∂μU
def D Y : LocalisationData R.U := ⟨μU, K ∘ gv, F, …, δ := Y.T.δ⟩                    -- Y : ResolvedCoreTransport R hKc prior
def decomp Y : SmoothCoreDecomposition (D Y) (card PIdx) (Base …) (da …)          -- one smooth core presentation per resolution chart × orthant: chart map (φ i)⁻¹ ∘ Tm INTO U, amplitude ρf · (F ∘ φ_i⁻¹), constant phase unit, lifted tail
theorem hasSmoothCoordFreeExpansion : HasSmoothCoordFreeExpansion Ξ.Z (decomp Y).coeff (decomp Y).commonQ (decomp Y).commonD ; commonD_le : ≤ d − 1
def coeff Y (μ : ℝ) (q : ℕ) : ℝ := (decomp Y).coeff μ q                                 -- 𝒯^U_{μ,q}[F]
theorem coeff_eq_of_transports (Y Y') : coeff Y μ q = coeff Y' μ q                         -- intrinsic in the transport (fixed R)
theorem coeff_comp_gv {f} (hf : ContDiff ℝ ∞ f) : (Ξ.withF (fun P => f (R.gv P)) _).coeff Y μ q = (Ξ.X Y).observableCoeff μ q f hf   -- = Theorem C's C_{μ,q}(f) (CDXVII), X Y the Euclidean bridge input of Y.T
-- D3: SmoothResolvedCoefficient.lean
theorem coeff_add (hG) (hG') : (withF (G + G')).coeff Y μ q = (withF G).coeff Y μ q + (withF G').coeff Y μ q ; coeff_smul ; coeff_zero
def zeroFibre : Set R.U := R.gv ⁻¹' tsupport prior ∩ {P | K (R.gv P) = 0}   -- compact
theorem coeff_eq_zero_of_eventually_zero (hF : ∀ᶠ P in 𝓝ˢ zeroFibre, F P = 0) : coeff Y μ q = 0     -- Z^U exponentially small: K∘π ≥ δ' > 0 on π⁻¹(supp prior) ∖ O
theorem coeff_congr_of_eventuallyEq (h : G =ᶠ[𝓝ˢ zeroFibre] G') : (withF G).coeff Y μ q = (withF G').coeff Y μ q   -- germ locality along D ∩ π⁻¹(supp prior)
```
## 3. Landed — D4 (grammar `Grammar.NormalCrossing`, Mathlib-only, row CDXXVII)
```
structure MonomialForm d where J : Finset (Fin d); k : Fin d → ℕ; a : (Fin d → ℝ) → ℝ; a_analytic : AnalyticAt ℝ a 0; a_ne : a 0 ≠ 0; k_pos : ∀ j ∈ J, 0 < k j
def MonomialForm.phase F x := F.a x * ∏ j ∈ F.J, x j ^ (2 * F.k j)
theorem exists_wall_equiv (F F') {H G} (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hH0 : H 0 = 0) (hGH : ∀ᶠ x in 𝓝 0, G (H x) = x) (hHG : ∀ᶠ y in 𝓝 0, H (G y) = y)
  (hphase : ∀ᶠ x in 𝓝 0, F.phase x = F'.phase (H x)) : ∃ σ : F.J ≃ F'.J, (∀ j, F.k j = F'.k (σ j)) ∧ ∀ j v, fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0
theorem exists_wall_equiv_jac_det … (hb : ∀ᶠ x, ContinuousAt b x) (hb0 : b 0 ≠ 0) (hb' …) (hb'0) (hjac : ∀ᶠ x in 𝓝 0, b x * ∏ j ∈ F.J, x j ^ h j = b' (H x) * (∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ) * (fderiv ℝ H x).det) :
  ∃ σ : F.J ≃ F'.J, (∀ j, F.k j = F'.k (σ j)) ∧ (∀ j, h j = h' (σ j)) ∧ ∀ j v, fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0
theorem card_eq_of_phase_eq … : F.J.card = F'.J.card ; theorem multiset_pairs_eq_of_phase_eq … : F.J.val.map (fun j => (F.k j, h j)) = F'.J.val.map (fun ℓ => (F'.k ℓ, h' ℓ))
theorem exponent_eq_of_unit_monomial_eq (σ : J ≃ J') (htan) (hwall : ∀ j, ∀ᶠ x, x j = 0 → ∃ ℓ ∈ J', H x ℓ = 0) (units c c' continuous near 0, nonzero at 0) (hid : ∀ᶠ x, c x * ∏_J x^e = c' x * ∏_{J'} (H x)^{e'}) : e j = e' (σ j)
```
Non-claims of D4: wall correspondence stated via tangent hyperplanes and exponents (not `H` mapping wall `j` onto wall `σ j`); units only continuous near 0; no inverse-function theorem (both directions `H, G` are hypotheses — an atlas supplies them).

## 4. Hironaka chart data available for level (2)
```
structure EvenChartBox (R) where φ : OpenPartialHomeomorph R.U (Fin d → ℝ); mem : φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.U; k h : Fin d → ℕ; b; b_analytic : AnalyticOnNhd ℝ b φ.target; b_ne_zero;
  phase_eq : ∀ u ∈ φ.target, K (watanabeRep R.g φ u) = ∏ j, u j ^ (2 * k j)  -- watanabeRep R.g φ u = R.gv (φ.symm u) (gv_symm_apply, rfl)
  jac_eq : ∀ u ∈ φ.target, (fderiv ℝ (watanabeRep R.g φ) u).det = b u * ∏ j, u j ^ h j ; r ρ; box_subset : centeredBox d ρ ⊆ φ.target; zero_mem : 0 ∈ φ.target ∧ K (watanabeRep R.g φ 0) = 0
theorem exists_evenChartBox (R) (hK0) {P} (hP : K (R.gv P) = 0) : ∃ E : EvenChartBox R, P ∈ E.φ.source ∧ E.φ P = 0     -- an even chart CENTRED at every divisor point
-- Mathlib: for e e' ∈ maximalAtlas (analytic groupoid, grade ω) the transition e.symm ≫ₕ e' is analytic on its source (StructureGroupoid.compatible_of_mem_maximalAtlas).
```
Observation: for two even chart boxes `E, E'` centred at `P`, `H := E'.φ ∘ E.φ.symm` is analytic near `0`, `H 0 = 0`, with analytic inverse `G`, and the two phases agree `∏ u^{2k} = ∏ (H u)^{2k'}` (both are `K(gv(·))`), the Jacobian law `b u ∏ u^h = b'(H u) ∏ (H u)^{h'} · det DH(u)` holds by the chain rule — so D4 gives `σ`, hence `|J| = |J'|` and equal multisets `{(k_j, h_j)}`. For a NON-centred point `Q = E.φ.symm u₀` near `P`, the translated chart `v ↦ E.φ(·) − u₀` has phase `∏_{j : u₀_j ≠ 0}(v_j+u₀_j)^{2k_j} · ∏_{j : u₀_j = 0} v_j^{2k_j}` = unit · monomial with `J(Q) = {j active : u₀_j = 0}`, i.e. a `MonomialForm` with a non-trivial unit `a` — D4 allows this.

## 5. Questions
**(A) Audit of level (1).** (i) Is `ResolvedData` (F smooth on all of U, `ContMDiff ∞`) the right domain, or should the functional be on compactly supported smooth functions / test functions on U (Mathlib has no `𝓓(U)` for manifolds; compact support is automatic-ish since μ_U is carried by the compact `π⁻¹(supp prior)`)? (ii) Is `coeff_congr_of_eventuallyEq` (germ locality along `zeroFibre = D ∩ π⁻¹(supp prior)`) the correct "support" statement for the paper, given there is no distribution structure on U yet? (iii) What is missing for the functional to be a genuine distribution on U — the chart-wise jet bound `|𝒯[F]| ≤ C · max_i ‖F ∘ φ_i⁻¹‖_{C^r(box_i)}` (Theorem C's `abs_observableCoeff_le` with `obs ∘ ψ` replaced by `F ∘ φ_i⁻¹`) — and is it worth doing now (M–L) or deferring? (iv) Anything WRONG or over-claimed in the statements above (e.g. `coeff_eq_of_transports` is for a fixed `R`; `coeff_comp_gv` uses the Euclidean bridge input `X Y` built from `Y.T`).

**(B) Design of level (2) — D5–D8 as Lean units.** Please give concrete definitions and statements, smallest-first, with proof routes and sizes (S/M/L/XL), using ONLY: the objects in §1–§4, Mathlib's manifold API (maximal atlas, analytic groupoid), and D4. Specifically:
 D5 (intrinsic depth and resonance data): how to define `depth P` for `P ∈ D` — via `exists_evenChartBox` centred at `P` + `Classical.choice`, well-definedness by D4 (`card_eq_of_phase_eq`) — and `pairs P : Multiset (ℕ × ℕ)` (the `(k_j,h_j)`), plus the resonance count `r_μ(P) = #{j : ∃ m, 2 k_j μ = h_j + 1 + m}`. Which properties are needed downstream and provable now: (a) upper semicontinuity / `D_{≥c} := {P | depth P ≥ c}` closed (via the translated-chart argument above — does that need D4 with the general unit, and what is the cleanest Lean route?), (b) `U_c := U ∖ D_{≥c+1}` open, (c) locally near `P` of depth `c`, `D_{≥c} ∩ chart = {u : u_j = 0 ∀ j ∈ J(P)}` (the stratum is a coordinate subspace in the centred chart), (d) do we need `S_c` as a submanifold at all for D6–D8, or do coordinate descriptions in the centred charts suffice?
 D6 (resonant support): `𝒯_{μ,q}[F] = 0` whenever `F` vanishes near `{P ∈ zeroFibre : r_μ(P) ≥ q + 1}`. Route: localise `F` by a partition of unity to centred even charts; in a centred chart the coefficient is a sum over the pieces of the engine's chart coefficients whose lattice/degree support is `{(μ, q) : q + 1 ≤ #{j : 2k_jμ ∈ h_j+1+ℕ}}` — do we have this in grammar (`coeff_eq_zero_of_degree_gt` is only `q ≤ D = d−1`; the finer per-piece degree bound by the number of resonant active coordinates — is it in the smooth engine's `familyCoeff` support lemmas, or would it need a new engine lemma?). What is the precise statement you want, and the cheapest proof?
 D7 (stratum kernels): skip for now or give the minimal statement worth doing.
 D8 (leading term): the globally first nonzero coefficient `(μ₀, q₀)` (smallest exponent, then highest log) is a positive functional: `F ≥ 0 ⇒ 𝒯_{μ₀,q₀}[F] ≥ 0`, hence (Riesz) a positive measure on the compact zero fibre; also `|𝒯_{μ₀,q₀}[F]| ≤ 𝒯_{μ₀,q₀}[1_U]·sup|F|`. Route: `Z_N[F] ≥ 0` for `F ≥ 0` and `Z_N[F] ~ c N^{−μ₀}(log N)^{q₀}` with the leading term dominating. Is this S/M given `hasSmoothCoordFreeExpansion`? What exactly is "globally first" in Lean (we have `coeff_support` on a lattice with `commonD`; the exponents with nonzero coefficients form a subset of `commonQ⁻¹ℕ` bounded below by 0 — existence of a minimum needs SOME nonzero coefficient, which we cannot prove in general (non-claim: no nonvanishing) — so state it conditionally on `(μ₀, q₀)` being minimal among nonzero?).
 Also: the regression `x²y²` on the quadrant (your #126): is a Lean regression feasible/valuable at level (2)?

**(C) Paper paragraph** for level (1) (8–10 sentences, `grammar_lean.tex` mirror style: what is proved, what is not), naming the theorems in prose.
