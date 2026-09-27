# Consult #169 — units 19–21 of the polar-distribution plan: the global leading measure (F5/M4)

You are Astra. Route B (consult #168) is complete: (B1), (B4) and the `x²y²` regression are formalised
(grammar main `319c892`, 912 modules; `couplingPolarCoeff`, `empCoeff_xy_sq_one/zero`). The next block of
the plan is F5 = M4, "the global leading measure": at the extremal pair `(λ*, m*)` the leading polar
functional is a finite positive measure `ρ_λ` on the resolved space (extending integrably across the
intersections with nonminimal walls, since those have exponent `> λ*`), and for every smooth observable
`F` and bounded root field `ξ`,

    N^{λ*} (log N)^{−(m*−1)} Z_N[F; ξ]  →  (1/(m*−1)!) ∫ F · S_{λ*}(ξ) dρ_λ            (M4)

with NO admissibility / test hypothesis on `F`. The plan's units are

19. `ResolvedLeadingMeasureChart` — under `ChartLeading`: a measure `leadingResidueMeasureU` on `U`, finite,
    zero on `deepZeroFibre m`, and `hasLeadingTerm_empZ_eq_integral_leading` for ALL smooth `F`.
20. `ResolvedExtremalLocalisation` — intrinsic `IsExtremalData` ⇒ the representation, via an adapted
    local cover certificate (flagged as the main size risk in #167).
21. `SmoothGlobalLeadingMeasure` — `globalExtremalStratumMeasure := (extremalStratumMeasure).map val`;
    coefficient = integral; `tendsto_normalised_partitionObs_extremal_all` (no `h0`); mass equality; then
    strengthen `tendsto_normalised_partitionObs_extremal` in place.

## What the library already has (verbatim statements in the appendix)

* Piece level (`EmpiricalPieceIntegral`, `EmpiricalPieceLeading`): each piece `p` of the resolved core
  transport has box data `(hA p, kA p)`, base measure `ν_p = (piecePresentation p).ν` on `Base`, the
  amplitude `(Ξ.amp Y p).amp s v` (which CONTAINS the observable `Ξ.F`: `amp` is the transported
  `prior · F · Jacobian` — please check its definition in the appendix), the piece kernel
  `empPieceKernel p ξ N s = empBoxIntegral hA kA N b (ξ.loc p (s,·)) (amp s ·)` and the piece face limit
  `pieceFaceLimit p ξ λ m s = boxFaceLimit hA kA λ m b (ξ.loc p (s,·)) (amp s ·)` (`= faceFunctional` if
  `multCount (ratioExp hA kA) λ = m`, else `0`). `hasLeadingTerm_empPieceInt` (for `BoxLeading` data):
  `empPieceInt p ξ ~ (∫_s pieceFaceLimit dν_p) N^{−λ}(log N)^{m−1}`, with NO hypothesis on `F`.
* Resolved level (`EmpiricalResolvedLeading`): `hasLeadingTerm_empZ`: under `ChartLeading λ m` (every piece
  `BoxLeading`) and a bounded field, `HasLeadingTerm (empZ Y ξ) (Σ_p ∫_s pieceFaceLimit … dν_p) λ (m−1)` —
  again for ALL `F`. The identification of `Σ_p ∫_s pieceFaceLimit` with `∫ F dν^λ_m(ξ)` against the
  EMPIRICAL STRATUM MEASURE on the OPEN stratum `X = U ∖ D_{m+1}` (`empiricalStratumMeasure`, built from
  `empFaceMeasure` on the open faces) needs `IsTest m F` (compact support in `X`):
  `integral_empiricalStratumMeasure_eq_sum`, `hasLeadingTerm_empZ_eq_integral`.
* Population level (`SmoothStratumMeasureExtremal`, `SmoothResolvedRLCTIndex`): `IsExtremalData λ m`
  (every wall through `Z₀` has ratio `≥ λ`, at most `m` resonate) gives `tendsto_normalised_Z_of_extremalData`
  for ALL smooth `G` with limit the coefficient `(withF G).coeff Y λ (m−1)`, and the stratum measure
  `extremalStratumMeasure` on the open stratum with `tendsto_normalised_partitionObs_extremal` under `h0`
  (`f∘π` vanishing near `deepZeroFibre m`).
* Unit 18 (`LeadingFaceMeasure`, DLXIV): on one box with `BoxLeading h k l m` and resonant set
  `J = resSet h k l`, the CLOSED-face leading measure `leadingFaceMeasure h k l b a = (glue J 0)_*
  ((vol|_{box'}).withDensity (∏_{J}(2kᵢ)⁻¹ · a(0_J,w) · ∏_{i∉J} wᵢ^{hᵢ−2kᵢ l}))` for a NONNEGATIVE continuous
  amplitude `a`; finite (exponents `> −1` on every complementary wall), carried by `{u_J = 0}`, deeper
  corners null, and ★★ `tendsto_empBoxIntegral_leadingFaceMeasure`: for every continuous `F` and `ξ`,
  `empBoxIntegral h k N b ξ (a·F) / (N^{−l} log^{m−1} N) → (1/(m−1)!) ∫ F · S_l(ξ) d(leadingFaceMeasure a)`
  (when `multCount = m`); `faceFunctional_eq_integral_leadingFaceMeasure`.

So the piece-level content of unit 19 is essentially there; what is missing is the ASSEMBLY of the closed
face measures over the base and over the pieces into one measure on `U`, and the resulting identification
of `Σ_p ∫_s pieceFaceLimit dν_p` with `(1/(m−1)!) ∫ F S_λ(ξ) dρ` for all `F`.

## Questions

1. **Construction of `ρ` on `U`.** For a piece `p` with `multCount (ratioExp hA kA) λ = m` and `J = resSet`,
   the natural candidate is the product-with-density pushforward
   `ρ_p := ((ν_p).prod (vol|_{box_{Jᶜ}})).withDensity (fun (s,w) ↦ ofReal (leadingFaceDensity (a_p s) w)) |>.map (fun (s,w) ↦ divPt p s (glue J 0 w))`
   (with `a_p s v := (Ξ.withF 1).amp p s v`, i.e. the amplitude with the observable removed — is that the
   right object? how does `Ξ.F` enter `Ξ.amp`?), and `ρ := Σ_{p : multCount = m} ρ_p`. This avoids
   `Measure.bind` and kernel measurability; integrals against `ρ_p` are `integral_map` + `integral_withDensity`
   + `integral_prod`. Is this the right construction, and is `ρ_p` independent of the base point structure in
   the way needed (the base measure `ν_p` and the transported box)? Alternatively, should the measure be
   defined directly as the pushforward of unit 18's `leadingFaceMeasure` fibrewise, or should we avoid the
   explicit measure and instead prove a Riesz-representation-free statement "the leading functional
   `F ↦ lim` is integration against a finite Borel measure on `U`" by uniqueness?
2. **Identification and the `if multCount = m` split.** `boxFaceLimit` is `0` for pieces with `multCount < m`
   (`ChartLeading` allows `≤ m`). Confirm that the global measure should be the sum over the pieces attaining
   `m` only, and that `Σ_p ∫_s pieceFaceLimit p ξ λ m s dν_p = (1/(m−1)!) Σ_{p attaining} ∫_s ∫ F(divPt) S_λ(ξ.loc) d(leadingFaceMeasure (a_p s)) dν_p`
   is exactly `faceFunctional_eq_integral_leadingFaceMeasure` under `integral_prod`. What are the
   measurability/integrability obligations (jointly in `(s,w)`) and which existing lemmas discharge them
   (`continuous_amp_uncurry`, `piecePresentation_Φ_eq_divPt`, the `RootField.loc` continuity)?
3. **The field on the face.** `ξ.loc p (s, glue J 0 w)` versus `ξ.ψ (divPt p s (glue J 0 w))`: the appendix
   has `RootField`; confirm the relation to be used so that the limit reads `∫ F(x) S_λ(ξ.ψ x) dρ(x)` on `U`.
4. **Unit 20: `IsExtremalData ⇒ ChartLeading`.** Every piece's box coordinates carry the wall data of a
   point of the resolved space; is `ChartLeading Y λ m` a consequence of `IsExtremalData λ m` for the
   given core transport `Y`, or only for an ADAPTED cover (pieces small enough that all their box walls
   pass through zero-fibre points)? If the latter, what is the minimal certificate and where does it live in
   the library (the `ResolvedCoreTransport` has a tube radius `a`; the pieces are `(chart, sector)` pairs)?
   Note `zeroOrder_of_extremalData` and `isLeadingIndex_of_extremalData` exist: the POPULATION coefficient
   at `(λ, m−1)` is known to be the leading one for every observable. Could unit 20 be avoided by proving
   the measure representation at the population level only through `coeff_withF_eq_integral_stratumMeasure`
   + a closed-stratum extension of `stratumMeasure` (Riesz on `U` rather than on `X`)? I.e. is there a
   cheaper route to (M4) for the population case that goes through uniqueness (`eq_stratumMeasure_of_tests`)
   instead of the piece construction?
5. **Unit 21 statements.** Give the precise Lean-level statements you would want: the global measure
   (name, type `Measure Ξ.R.U`), finiteness, `ρ (deepZeroFibre m) = 0`, `ρ.restrict (stratumOpen m) = map val (extremalStratumMeasure)`
   (mass equality), `tendsto_normalised_partitionObs_extremal_all` (no `h0`), and the empirical
   `hasLeadingTerm_empZ_eq_integral_leading`. Order them by dependency and estimate sizes.
6. **Paper.** Is (M4) in this form ("the leading polar functional is the Γ-weighted / `S_λ(ξ)`-weighted
   integral against a finite positive measure on the CLOSED extremal stratum, for every smooth
   observable") the right statement to print, and how should the relation to the open-stratum measure
   `ν^λ_m` (unique, transport-independent, `stratumMeasure_eq_of_transports`) be presented — as
   "`ρ` restricted to the open stratum is `ν^λ_m`, and `ρ` gives the deeper corners measure zero, so the
   two agree and `ρ` is the unique extension"?

Answer with precise mathematics and Lean-level statements in the library's names; flag anything in the
appendix that contradicts the plan.

## Appendix: verbatim Lean statements

### SmoothResolvedConsumer.lean

/-- The resolved inputs: a phase with a Watanabe modification over `W`, a smooth compactly
supported nonnegative prior inside `W`, and a smooth observable `F` on the resolved manifold. -/
structure ResolvedData (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the open set carrying the modification -/
  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

/-- The resolved measure `μ_U`. -/
noncomputable def μU : Measure Ξ.R.U := Ξ.R.resolvedMeasure Ξ.hKc Ξ.prior

/-- `Z^U_N[F] = ∫_U F e^{−N K∘π} dμ_U`. -/
noncomputable def Z (N : ℝ) : ℝ := ∫ P, Ξ.F P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU

/-- The amplitude family of a piece: the pull-back of the extended amplitude along the chart
coordinate. -/
noncomputable def amp (p : (Ξ.X Y).PIdx) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine ((Ξ.X Y).continuous_sc p) ((Ξ.X Y).eqv p) p.2 (Ξ.contDiff_G Y p.1)
    (Y.T.a p.1)

/-- ★★ **The smooth core presentation of a lifted piece**: constant phase unit, transport density
`ρf`, amplitude `G`, chart map `φ⁻¹ ∘ Tm` into `U`. -/
noncomputable def piecePresentation (p : (Ξ.X Y).PIdx) :
    SmoothCorePresentation (Ξ.D Y) (Ξ.coreMeasure Y p) (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
      ((Ξ.X Y).da p) where
  ν := baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1)
  h := (Ξ.X Y).hA p
  k := (Ξ.X Y).kA p
  k_pos := (Ξ.X Y).kA_pos p
  b := Y.T.a p.1
  b_pos := Y.T.a_pos p.1
  βf _ := Y.T.phaseConst p.1
  β_cont := continuous_const
  β_pos _ := Y.T.phaseConst_pos p.1
  Φ z := Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_Φ := (Y.measurable_chartInv p.1).comp ((Ξ.X Y).continuous_Tm p).measurable
  ρ z := (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_ρ := (((Ξ.X Y).contDiff_ρf p.1).continuous.comp ((Ξ.X Y).continuous_Tm p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => (Ξ.X Y).ρf_nonneg p.1 _
  amp := Ξ.amp Y p
  amplitude_eq := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change Ξ.G Y p.1 ((Ξ.X Y).Tm p z.1 z.2) =
      (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2) * Ξ.F (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))
    rw [Ξ.G_eq Y p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv), (Ξ.X Y).ρf_eq p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv)]
    rfl
  phase_normal := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    have hbox := (Ξ.X Y).Tm_mem_box p z.1 hv
    change Ξ.K (Ξ.R.gv (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))) = _
    rw [← Y.ψ_eq_gv_chartInv p.1 (Y.box_subset_target p.1 hbox),
      Y.T.phase_eq p.1 _ (Y.T.box_subset_V p.1 hbox)]
    congr 1
    exact (Ξ.X Y).prod_Tm_pow p z.1 z.2
  transport := by
    have hΦ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)) =
        (Y.chartInv p.1 ∘ WaterFilling.refl p.2) ∘
          glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
    have hρ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        ((mono ((Ξ.X Y).hA p) z.2 * (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => Y.T.h p.1 ((Ξ.X Y).eqv p j).1) z.2 *
          (Ξ.X Y).ρf p.1 (WaterFilling.refl p.2
            (glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) z))) := by
      funext z
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((Y.measurable_chartInv p.1).comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (Y.measurable_chartInv p.1) (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ ((Ξ.X Y).measurable_ρf p.1),
      ChartCollar.map_refl_pieceMeasure]
    rfl

/-- ★★★ **The smooth core decomposition of `Z^U_N[F]`**: one smooth core presentation per
resolution chart and orthant, the lifted tail as the tail. -/
noncomputable def decomp : SmoothCoreDecomposition (Ξ.D Y) (Fintype.card (Ξ.X Y).PIdx)
    (fun I => Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1))
    (fun I => (Ξ.X Y).da ((Ξ.X Y).en I)) where
  core I := Ξ.coreMeasure Y ((Ξ.X Y).en I)
  tail := Y.tailU
  measure_eq := by
    rw [Ξ.D_μ, ← Ξ.sum_coreMeasure Y]
    congr 1
    exact (Equiv.sum_comp (Ξ.X Y).en (Ξ.coreMeasure Y)).symm
  δ₀ := Y.T.δ
  δ₀_pos := Y.T.δ_pos
  gap := Y.ae_tailU_gap Ξ.hK0 Ξ.prior_compact Ξ.prior_W
  chart I := Ξ.piecePresentation Y ((Ξ.X Y).en I)

/-- ★ **The resolved coefficient functional** `𝒯^U_{μ,q}[F]`: the coefficient of
`N^{−μ}(log N)^q` in the expansion of `∫_U F e^{−N K∘π} dμ_U`. -/
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ := (Ξ.decomp Y).coeff μ q


### SmoothResolvedResonant.lean

/-- The chart point of a piece face point. -/
noncomputable def facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Fin d → ℝ := (Ξ.X Y).Tm p s v

/-- The divisor point of a piece face point. -/
noncomputable def divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Ξ.R.U := (Y.φ p.1).symm (Ξ.facePt Y p s v)

theorem facePt_mem_box (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.facePt Y p s v ∈ centeredBox d (Y.T.a p.1)


### EmpiricalPieceIntegral.lean

/-- The empirical integrand `e^{−N K∘π + √N √(K∘π) ψ} · F` on `U`. -/
noncomputable def empIntegrand (ξ : Ξ.RootField Y) (N : ℝ) (P : Ξ.R.U) : ℝ :=
  Real.exp (-N * Ξ.phaseU P + Real.sqrt N * Real.sqrt (Ξ.phaseU P) * ξ.ψ P) * Ξ.F P

/-- The empirical box kernel of a piece at the base point `s`. -/
noncomputable def empPieceKernel (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  empBoxIntegral ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) N (Y.T.a p.1) (fun v => ξ.loc p (s, v))
    fun v => (Ξ.amp Y p).amp s v

/-- The empirical piece integral: the kernel integrated over the base. -/
noncomputable def empPieceInt (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (N : ℝ) : ℝ :=
  ∫ s, Ξ.empPieceKernel Y p ξ N s ∂(Ξ.piecePresentation Y p).ν

/-- The face limit of a piece at the pair `(λ, m)`, at the base point `s`. -/
noncomputable def pieceFaceLimit (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) : ℝ :=
  boxFaceLimit ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m (Y.T.a p.1) (fun v => ξ.loc p (s, v))
    fun v => (Ξ.amp Y p).amp s v

/-- The chart-leading condition: every piece is chart-leading at `(λ, m)`. -/
def ChartLeading (lam : ℝ) (m : ℕ) : Prop :=
  ∀ p : (Ξ.X Y).PIdx, BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m

/-- The chart map of the piece presentation is the divisor point on the box. -/
theorem piecePresentation_Φ_eq_divPt (p : (Ξ.X Y).PIdx)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)}
    (hz : z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1)) :
    (Ξ.piecePresentation Y p).Φ z = Ξ.divPt Y p z.1 z.2

/-- ★★ **Transport of the empirical core integral to the box**:
`∫ e^{−NK∘π + √N√(K∘π)ψ} F dcore_p = ∫_{Base} empBoxIntegral h k N b (loc_p(s,·)) (amp s) dν`. -/
theorem integral_coreMeasure_empIntegrand (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {N : ℝ}
    (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    ∫ P, Ξ.empIntegrand Y ξ N P ∂(Ξ.coreMeasure Y p) = Ξ.empPieceInt Y p ξ N

/-- ★★★ **The leading term of the empirical piece integral** at a chart-leading pair: the base
integral of the piece face limit. -/
theorem hasLeadingTerm_empPieceInt (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    HasLeadingTerm (Ξ.empPieceInt Y p ξ) (∫ s, Ξ.pieceFaceLimit Y p ξ lam m s
      ∂(Ξ.piecePresentation Y p).ν) lam (m - 1)


### EmpiricalPieceLeading.lean

/-- The chart-leading condition for a box at the pair `(λ, m)`. -/
def BoxLeading (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) : Prop :=
  (∀ i, lam ≤ ratioExp h k i) ∧ multCount (ratioExp h k) lam ≤ m

/-- The box face limit at `(λ, m)`: the empirical face functional when the box realises the
multiplicity `m`, and `0` otherwise. -/
noncomputable def boxFaceLimit (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) (b : ℝ)
    (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  if multCount (ratioExp h k) lam = m then faceFunctional h k lam b ξ η else 0

/-- ★★ **The empirical box integral at a chart-leading pair** converges, normalised at `(λ, m−1)`,
to the box face limit. -/
theorem tendsto_empBoxIntegral_div_boxFaceLimit (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m)
    (ξ η : (Fin d → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    Tendsto (fun N => empBoxIntegral h k N b ξ η / (N ^ (-lam) * Real.log N ^ (m - 1))) atTop
      (𝓝 (boxFaceLimit h k lam m b ξ η))


### EmpiricalResolvedLeading.lean

/-- The empirical partition function `∫_U e^{−N K∘π + √N √(K∘π) ψ} F dμ_U`. -/
noncomputable def empZ (ξ : Ξ.RootField Y) (N : ℝ) : ℝ := ∫ P, Ξ.empIntegrand Y ξ N P ∂Ξ.μU

/-- **The core decomposition of the empirical partition function**. -/
theorem empZ_eq_sum (ξ : Ξ.RootField Y) {N : ℝ} (hN : 0 ≤ N) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    Ξ.empZ Y ξ N = ∑ p, Ξ.empPieceInt Y p ξ N + ∫ P, Ξ.empIntegrand Y ξ N P ∂Y.tailU

/-- ★★★ **The empirical leading theorem**: at a chart-leading pair `(λ, m)` and for a bounded root
field, `Z^{emp}_N[F; ξ] / (N^{−λ}(log N)^{m−1}) → Σ_p ∫_{Base} boxFaceLimit_p dν_p`. -/
theorem hasLeadingTerm_empZ (ξ : Ξ.RootField Y) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      (∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν) lam (m - 1)

/-- ★★ **The piece face limit is the empirical face integral**: for a test `F` and a chart-leading
piece, `∫_{Base} boxFaceLimit_p dν_p = Σ_{J simple} residueConst · ∫ F dempFaceMeasure_{p,J}`. -/
theorem integral_pieceFaceLimit_eq (p : (Ξ.X Y).PIdx) (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam)
    {m : ℕ} (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) (hFt : Ξ.IsTest m Ξ.F) :
    ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν =
      ∑ J ∈ Ξ.simpleFaces Y p lam m,
        residueConst lam m * ∫ x, Ξ.F x.1 ∂(Ξ.empFaceMeasure Y p J ξ lam m)

/-- ★★★ **The limit is the integral against the empirical stratum measure**: for a test `F`,
`Σ_p ∫_{Base} boxFaceLimit_p dν_p = ∫_X F dν^λ_m(ξ)`. -/
theorem integral_empiricalStratumMeasure_eq_sum (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam)
    {m : ℕ} (hlead : Ξ.ChartLeading Y lam m) (hFt : Ξ.IsTest m Ξ.F) :
    ∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m) =
      ∑ p, ∫ s, Ξ.pieceFaceLimit Y p ξ lam m s ∂(Ξ.piecePresentation Y p).ν

/-- ★★★ **The empirical leading theorem, in the form of the empirical stratum measure**: for a
test `F` supported in `X = U ∖ D_{m+1}`, a bounded root field `ξ` and a chart-leading pair
`(λ, m)`, `N^{λ}(log N)^{−(m−1)} Z^{emp}_N[F; ξ] → ∫_X F dν^λ_m(ξ)`. -/
theorem hasLeadingTerm_empZ_eq_integral (ξ : Ξ.RootField Y) {lam : ℝ} (hμ : 0 < lam) {m : ℕ}
    (hm : 1 ≤ m) (hlead : Ξ.ChartLeading Y lam m) {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M)
    (hFt : Ξ.IsTest m Ξ.F) :
    HasLeadingTerm (Ξ.empZ Y ξ) (∫ x, Ξ.F x.1 ∂(Ξ.empiricalStratumMeasure Y ξ lam m)) lam
      (m - 1)


### EmpiricalStratumMeasure.lean

/-- The empirical face measure on `X = U ∖ D_{c+1}`. -/
noncomputable def empFaceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  Measure.comap Subtype.val (Ξ.empFaceMeasureU Y p J ξ μ)

theorem integral_empFaceMeasure_eq {μ : ℝ} (hμ : 0 < μ) {c : ℕ} {G : Ξ.R.U → ℝ}
    (hGc : Continuous G) (hGt : tsupport G ⊆ Ξ.stratumOpen c) :
    ∫ x, G x.1 ∂(Ξ.empFaceMeasure Y p J ξ μ c) =
      ∫ z, Ξ.empFaceDensity Y p J ξ μ z * G (Ξ.faceMap Y p J z) ∂(Ξ.faceRef Y p J)

/-- The empirical chart measure: the sum over the pieces and simple-pole faces of the empirical
face measures. -/
noncomputable def empiricalChartMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ∑ I, ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c, Ξ.empFaceMeasure Y ((Ξ.X Y).en I) J ξ μ c

/-- **The empirical stratum measure** `ν^μ_c(ξ) = Γ(μ)/(c−1)! · empiricalChartMeasure`, equal to
the population stratum measure at the zero field. -/
noncomputable def empiricalStratumMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal (residueConst μ c) • Ξ.empiricalChartMeasure Y ξ μ c

theorem empiricalChartMeasure_zero {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    Ξ.empiricalChartMeasure Y (RootField.zero Ξ Y) μ c = Ξ.chartResidueMeasure Y μ c


### LeadingFaceMeasure.lean

/-- The residue weight on positive coordinates as a product of real powers. -/
theorem residueWeight_eq_prod {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    residueWeight h k μ w = ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * μ)

/-- The residue weight is integrable on the box when every exponent exceeds `−1`. -/
theorem integrableOn_residueWeight_box {ι : Type*} [Fintype ι] (h k : ι → ℕ) {μ : ℝ}
    (hμ : ∀ i, 2 * (k i : ℝ) * μ < h i + 1) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (residueWeight h k μ) (SmoothEngine.box ι b)

theorem measurable_residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) :
    Measurable (residueWeight h k μ)

/-- The leading face density with amplitude `a`:
`(∏_{i∈J} (2k_i)⁻¹) · a(0_J,w) · residueWeight(w)` on the complementary box. -/
noncomputable def leadingFaceDensity (a : (Fin d → ℝ) → ℝ)
    (w : {i // ¬ inJ (resSet h k l) i} → ℝ) : ℝ :=
  (∏ i ∈ resSet h k l, (2 * (k i : ℝ))⁻¹) * a (glue (resSet h k l) 0 w) *
    residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w

/-- The leading face measure on `ℝ^d`: the density pushed forward under the face inclusion. -/
noncomputable def leadingFaceMeasure (b : ℝ) (a : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  ((volume.restrict (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b)).withDensity
    fun w => ENNReal.ofReal (leadingFaceDensity h k l a w)).map (glue (resSet h k l) 0)

theorem measurable_glue_zero (J : Finset (Fin d)) :
    Measurable fun w : {i // ¬ inJ J i} → ℝ => glue J 0 w

theorem leadingFaceDensity_nonneg {a : (Fin d → ℝ) → ℝ} (ha : ∀ u, 0 ≤ a u) {b : ℝ}
    {w : {i // ¬ inJ (resSet h k l) i} → ℝ} (hw : w ∈ SmoothEngine.box _ b) :
    0 ≤ leadingFaceDensity h k l a w

theorem measurable_leadingFaceDensity {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    Measurable (leadingFaceDensity h k l a)

/-- Integrals against the leading face measure are box integrals of the face construction. -/
theorem integral_leadingFaceMeasure {b : ℝ} {a : (Fin d → ℝ) → ℝ} (ha : Continuous a)
    (ha0 : ∀ u, 0 ≤ a u) {F : (Fin d → ℝ) → ℝ} (hF : Measurable F) :
    ∫ u, F u ∂(leadingFaceMeasure h k l b a) =
      ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
        F (glue (resSet h k l) 0 w) * leadingFaceDensity h k l a w

/-- The complementary weight is integrable under `BoxLeading`, since every complementary wall has
exponent strictly greater than `l`. -/
theorem integrableOn_residueWeight_compl (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l)
      (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b)

/-- The leading face density is integrable on the complementary box for continuous `a`. -/
theorem integrableOn_leadingFaceDensity (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    IntegrableOn (leadingFaceDensity h k l a)
      (SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b)

/-- The leading face measure is finite. -/
theorem leadingFaceMeasure_univ_lt_top (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    leadingFaceMeasure h k l b a univ < ⊤

theorem isFiniteMeasure_leadingFaceMeasure (hk : ∀ i, 0 < k i) (hmin : ∀ i, l ≤ ratioExp h k i)
    {b : ℝ} (hb : 0 < b) {a : (Fin d → ℝ) → ℝ} (ha : Continuous a) :
    IsFiniteMeasure (leadingFaceMeasure h k l b a)

theorem measurableSet_coordZero (i : Fin d) : MeasurableSet {u : Fin d → ℝ | u i = 0}

/-- The measure is carried by the closed face `{u_J = 0}`. -/
theorem leadingFaceMeasure_face (b : ℝ) (a : (Fin d → ℝ) → ℝ) :
    leadingFaceMeasure h k l b a {u | ∃ i ∈ resSet h k l, u i ≠ 0} = 0

/-- The deeper corners `{∃ i ∉ J, u_i = 0}` carry no mass. -/
theorem leadingFaceMeasure_deep (b : ℝ) (a : (Fin d → ℝ) → ℝ) :
    leadingFaceMeasure h k l b a {u | ∃ i, i ∉ resSet h k l ∧ u i = 0} = 0

/-- The empirical face functional is `(1/(m−1)!) ∫ S_l(ξ) dρ^η` for a nonnegative continuous
amplitude `η`. -/
theorem faceFunctional_eq_integral_leadingFaceMeasure (hl : 0 < l) {b : ℝ}
    {ξ η : (Fin d → ℝ) → ℝ} (hξ : Continuous ξ) (hη : Continuous η) (hη0 : ∀ u, 0 ≤ η u) :
    faceFunctional h k l b ξ η =
      (1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ)) *
        ∫ u, fluctuation 1 l (ξ u) ∂(leadingFaceMeasure h k l b η)

/-- **The leading limit of the tilted box integral on the closed face.** Under `BoxLeading` with
the multiplicity attained, for every continuous field `ξ`, nonnegative continuous amplitude `a`
and continuous observable `F`,
`N^l (log N)^{−(m−1)} ∫_{(0,b]^d} a F u^h e^{−N u^{2k} + √N u^k ξ} → (1/(m−1)!) ∫ F S_l(ξ) dρ^a`.
No admissibility of `F` is needed. -/
theorem tendsto_empBoxIntegral_leadingFaceMeasure (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (hm : 1 ≤ m)
    (hlead : BoxLeading h k l m) (hatt : multCount (ratioExp h k) l = m)
    {ξ a F : (Fin d → ℝ) → ℝ} (hξ : Continuous ξ) (ha : Continuous a) (ha0 : ∀ u, 0 ≤ a u)
    (hF : Continuous F) :
    Tendsto (fun N => empBoxIntegral h k N b ξ (fun u => a u * F u) /
        (N ^ (-l) * Real.log N ^ (m - 1))) atTop
      (𝓝 ((1 / ((m - 1).factorial : ℝ)) *
        ∫ u, F u * fluctuation 1 l (ξ u) ∂(leadingFaceMeasure h k l b a)))


### SmoothStratumMeasureExtremal.lean

/-- ★★★ **The extremal stratum measure** `ν^{λ*}_{m*}` on `U ∖ D_{m*+1}`. -/
noncomputable def extremalStratumMeasure {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) : Measure (Ξ.stratumOpen m) :=
  Ξ.stratumMeasure Y hm (Ξ.zeroOrder_of_extremalData h m)

/-- ★★★ **Leading-index characterisation**: for `F ∈ 𝓘_{m*+1}`, the normalised resolved partition
function converges to the integral of `F` against the extremal stratum measure. -/
theorem tendsto_normalised_Z_extremal {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), G P = 0) :
    Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
      (𝓝 (∫ x, G x.1 ∂(Ξ.extremalStratumMeasure Y h hm)))

/-- ★★★ **Euclidean leading-index characterisation**: for a base observable `f` with
`f ∘ π ∈ 𝓘_{m*+1}`, `N^{λ*} (log N)^{−(m*−1)} ∫ prior · f · e^{−NK} → ∫ f ∘ π dν^{λ*}_{m*}`. -/
theorem tendsto_normalised_partitionObs_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    Tendsto (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f)) atTop
      (𝓝 (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)))

/-- ★★★ **The leading asymptotic with insertion**: when `∫ f ∘ π dν^{λ*}_{m*} ≠ 0`,
`∫ prior · f · e^{−NK} ∼ (∫ f ∘ π dν^{λ*}_{m*}) N^{−λ*} (log N)^{m*−1}`. -/
theorem partitionObs_isEquivalent_extremal {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0)
    (hne : ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) ≠ 0) :
    (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
      fun N => (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)) *
        (N ^ (-lam) * Real.log N ^ (m - 1))


### SmoothResolvedRLCTIndex.lean

/-- ★★★ **The extremal pair is a leading index** (in the sense of CDXXXII). -/
theorem isLeadingIndex_of_extremalData (h : Ξ.IsExtremalData lam m) :
    Ξ.IsLeadingIndex Y lam (m - 1)

/-- ★★ **The normalised limit at the extremal pair**, unconditionally:
`N^{λ*}(log N)^{−(m*−1)} Z^U_N[G] → 𝒯^U_{λ*,m*−1}[G]`. -/
theorem tendsto_normalised_Z_of_extremalData (h : Ξ.IsExtremalData lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    Tendsto (normalised lam (m - 1) (Ξ.withF G hG).Z) atTop
      (𝓝 ((Ξ.withF G hG).coeff Y lam (m - 1)))

/-- ★★ **Nonnegativity of the extremal functional** on observables nonnegative a.e. -/
theorem coeff_nonneg_of_extremalData (h : Ξ.IsExtremalData lam m) {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hG0 : ∀ᵐ P ∂Ξ.μU, 0 ≤ G P) :
    0 ≤ (Ξ.withF G hG).coeff Y lam (m - 1)


### SmoothStratumMeasure.lean

/-- ★★★ **The stratum measure** `ν^μ_c` on `X = U ∖ D_{c+1}`: the Riesz measure of the positive
linear functional `Λ`. -/
noncomputable def stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  RealRMK.rieszMeasure (Ξ.Λ Y hc hzero)

/-- ★★★ **Smooth integral representation**: the stratum measure integrates every smooth test
function to the `(μ, c−1)` coefficient of the corresponding observable. -/
theorem integral_stratumMeasure_test {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.T Y μ c G hG

/-- ★★★ **The stratum measure is carried by the exact stratum**: the complement of `S^μ_c` in
`X` is a null set. -/
theorem stratumMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0

/-- ★★★ **Representation for observables vanishing near the deep zero fibre**, compactly supported
in `X` or not: the `(μ, c−1)` coefficient is the integral against the stratum measure. -/
theorem coeff_withF_eq_integral_stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    (Ξ.withF G hG).coeff Y μ (c - 1) = ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero)

/-- ★★ **Transport independence**: the stratum measure does not depend on the chosen resolved
core transport. -/
theorem stratumMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) {μ : ℝ}
    {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero = Ξ.stratumMeasure Y' hc hzero

/-- ★★★ **Uniqueness**: a regular measure on `X` integrating every smooth test function to the
coefficient functional is the stratum measure. -/
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero


### SmoothResolvedStratumFormula.lean

/-- The deep zero fibre `D_{c+1} = Z₀ ∩ {depth ≥ c + 1}`. -/
def deepZeroFibre (c : ℕ) : Set Ξ.R.U := Ξ.zeroFibre ∩ depthGE Ξ.R Ξ.hK0 (c + 1)


### SmoothResolvedStratumPositive.lean

/-- **The zero-order condition**: every wall through a point of the exact stratum has ratio
exactly `μ`. -/
def ZeroOrder (μ : ℝ) (c : ℕ) : Prop :=
  ∀ P ∈ Ξ.exactStratum μ c, ∀ q ∈ pairs Ξ.R Ξ.hK0 P, 2 * (q.1 : ℝ) * μ = q.2 + 1


### SmoothResolvedCoefficient.lean

/-- The zero fibre over the prior support: `D ∩ π⁻¹(supp prior)`. -/
def zeroFibre : Set Ξ.R.U := Ξ.R.gv ⁻¹' tsupport Ξ.prior ∩ {P | Ξ.K (Ξ.R.gv P) = 0}


### ResolvedDepth.lean

/-- ★ **The intrinsic pair data** of a point of the resolved manifold: the pair data of any even
chart box centred at the point (empty off the divisor). -/
noncomputable def pairs (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x) (P : R.U) :
    Multiset (ℕ × ℕ) :=
  if hP : P ∈ divisor R then pairData (Classical.choose (exists_centeredEvenChartBox R hK0 hP))
  else 0

/-- The resonance count `r_μ(P)`: the number of walls through `P` resonant with `μ`. -/
noncomputable def resonanceCount (μ : ℝ) (P : R.U) : ℕ :=
  ((pairs R hK0 P).filter (Resonates μ)).card


### SmoothStratumTest.lean

/-- **Test functions**: compactly supported inside `X = U ∖ D_{c+1}`. -/
def IsTest (c : ℕ) (G : Ξ.R.U → ℝ) : Prop :=
  HasCompactSupport G ∧ tsupport G ⊆ Ξ.stratumOpen c


### EmpiricalFaceFunctional.lean

/-- The resonant coordinates `J_l = {i | (h_i+1)/(2k_i) = l}`. -/
noncomputable def resSet (h k : Fin d → ℕ) (l : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => ratioExp h k i = l

/-- The empirical face functional on the box `(0,b]^d` at temperature one:
`1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J,w) S_l(ξ(0_J,w)) residueWeight(w) dw`. -/
noncomputable def faceFunctional (h k : Fin d → ℕ) (l b : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i ∈ resSet h k l, (2 * (k i : ℝ)))) *
    ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
      η (glue (resSet h k l) 0 w) * fluctuation 1 l (ξ (glue (resSet h k l) 0 w)) *
        residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w


### EmpiricalStratumMeasure.lean

/-- A **root field**: a function `ψ` on `U` (the pull-back of Watanabe's `√n(K − K_n)/√K`)
together with, for every piece, a continuous branch representative on `Base × ℝ^{da}` agreeing
with `ψ ∘ divPt` on the open box. Only the representatives' values on the closed boxes enter the
empirical stratum measure. -/
structure RootField where
  /-- the field on `U` -/
  ψ : Ξ.R.U → ℝ
  ψ_meas : Measurable ψ
  /-- the branch representative of the piece -/
  loc : ∀ p : (Ξ.X Y).PIdx,
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) → ℝ
  loc_cont : ∀ p, Continuous (loc p)
  loc_eq : ∀ (p : (Ξ.X Y).PIdx)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)),
    z.2 ∈ SmoothEngine.box (Fin ((Ξ.X Y).da p)) (Y.T.a p.1) → loc p z = ψ (Ξ.divPt Y p z.1 z.2)

/-- The empirical face measure on `U`: the pushforward of the empirical face density along the
face map. -/
noncomputable def empFaceMeasureU (μ : ℝ) : Measure Ξ.R.U :=
  ((Ξ.faceRef Y p J).withDensity fun z => ENNReal.ofReal (Ξ.empFaceDensity Y p J ξ μ z)).map
    (Ξ.faceMap Y p J)


### SmoothBridgeConsumer.lean

/-- The pieces: a chart and an orthant (all orthants are selected). -/
abbrev PIdx : Type := Σ _ : X.T.ι, WaterFilling.CoordSign d

/-- The chart coordinate of a piece: reflected active coordinates `v`, reflected inactive
coordinates `s`. -/
noncomputable def Tm (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    Fin d → ℝ :=
  affineMap (X.eqv p) p.2 (X.sc p s) v


### SmoothStratumTest.lean

/-- The open set `X = U ∖ D_{c+1}` carrying the stratum measure. -/
def stratumOpen (c : ℕ) : Set Ξ.R.U := (Ξ.deepZeroFibre c)ᶜ


### SmoothResolvedResidue.lean

/-- The residue constant `Γ(μ)/(c−1)!`. -/
noncomputable def residueConst (μ : ℝ) (c : ℕ) : ℝ := Real.Gamma μ / ((c - 1).factorial : ℝ)

/-- The simple-pole faces of size `c` of a piece box. -/
noncomputable def simpleFaces (p : (Ξ.X Y).PIdx) (μ : ℝ) (c : ℕ) :
    Finset (Finset (Fin ((Ξ.X Y).da p))) :=
  (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter fun J =>
    J.card = c ∧ ∀ j ∈ J, 2 * ((Ξ.X Y).kA p j : ℝ) * μ = (Ξ.X Y).hA p j + 1


### EmpiricalFaceFunctional.lean

/-- The resonant coordinates `J_l = {i | (h_i+1)/(2k_i) = l}`. -/
noncomputable def resSet (h k : Fin d → ℕ) (l : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => ratioExp h k i = l

/-- The empirical face functional on the box `(0,b]^d` at temperature one:
`1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J,w) S_l(ξ(0_J,w)) residueWeight(w) dw`. -/
noncomputable def faceFunctional (h k : Fin d → ℕ) (l b : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i ∈ resSet h k l, (2 * (k i : ℝ)))) *
    ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
      η (glue (resSet h k l) 0 w) * fluctuation 1 l (ξ (glue (resSet h k l) 0 w)) *
        residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w


### MonomialMixedAsymptotic.lean

/-- The Mellin ratios `ℓᵢ = (hᵢ+1)/(2kᵢ)`. -/
noncomputable def ratioExp {d : ℕ} (h k : Fin d → ℕ) (i : Fin d) : ℝ :=
  ((h i : ℝ) + 1) / (2 * (k i : ℝ))


### WeightedMixedAsymptotic.lean

/-- The multiplicity of the value `l` among the exponents. -/
noncomputable def multCount {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : ℕ :=
  ∑ i, if ℓ i = l then 1 else 0


### ResolvedDepthLocal.lean

/-- The locus of depth at least `c`. -/
def depthGE (c : ℕ) : Set R.U := {P | c ≤ depth R hK0 P}

