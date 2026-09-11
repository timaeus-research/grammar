# Consult #79 — grammar Lean: the #78 plan (N1 end-to-end) is complete; what next?

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
546 modules, axiom-clean: every theorem below depends only on `propext, Classical.choice, Quot.sound`).
Your #78 five-unit programme is fully landed. This consult asks for the next programme.

## Landed since #78 (exact statements in the appendix)

* CCXLI `ProductChartHypotheses` (unit 1): `zeroOn J` (zero the active coordinates), centred product
  domain `productDom J T b = {y | P_J y ∈ T ∧ ∀ j ∈ J, |y_j| ≤ b}` (compact), foot set
  `footSet J T b I` (closed), fibre saturation `mem_productDom_iff_foot_mem_footSet` (ε ≤ b),
  `unit_indep_piece`, `weight_factor_piece`, `exists_zeroPoint`; the hypothesis package
  `structure ProductMonomialChart R i K` (fields e h W monomial u v T b dom_eq unit_indep r r_meas Cr
  r_bound **weight_eq : ∀ y ∈ dom, R.weight i (Φ y) = r (zeroOn e.support y)**), `ratio`,
  `pieceLam I = I.inf' ratio`, `pieceMult`.
* CCXLII `ProductChartPieceData` (units 2–3): `exists_pieceAtlas` (all CCXXXVIII hypotheses for every
  nonempty I ⊆ supp e with common ε ≤ b), `pieceAtlas'` (choice), `productAtlases`,
  **`hasLeadingTerm_boltzmannIntegral_of_productCharts`**: for a cover all of whose charts carry a
  `ProductMonomialChart`, `Z_N[F] := coverIntegral (F·p)(−N K)` has the certificate at any (λ₀,k₀)
  dominating every chart–stratum pair, coefficient = Σ over (i, I) of tied cell coefficients.
* CCXLIII `ProductChartExtremalPair` (unit 4): `ratioExp_normal_eq`, `minRatio_normal_eq`,
  `multCount_normal_eq` (cell pair = divisor pair `(min_{j∈I}(h_j+1)/e_j, #min − 1)`), `coverLam`
  (λ* = min over active (i, j)), `coverDeg` (k* = max over charts attaining λ* of #{λ*-ratios} − 1),
  **`hasLeadingTerm_boltzmannIntegral_of_productCharts_extremal`** at (λ*, k*);
  `hasLeadingTerm_boltzmannIntegral_of_no_active`.
* CCXLIV `ScalarCellNonneg` (unit 5a): `ScalarUnitCell.coeff_nonneg` (β ≥ 0 a.e., A ≥ 0 on
  base × closedBall ⇒ coeff ≥ 0), `reflected_coeff_nonneg`; and
  `exists_pieceAtlas_of_chart_data` now returns the CCXXXVIII atlas as an EQUALITY with the
  constructed one (q' = scalarPhase, A' = pieceAmp on the base) — cells exposed.
* CCXLV `ProductChartPositivity` (unit 5b): `pieceDensity`, `IsPieceAtlasData`, `pieceAtlasD`,
  `productAtlasesD`, `productCoeffD`, `hasLeadingTerm_boltzmannIntegral_of_productChartsD`;
  `cell_coeff_nonneg_of_data` (F, p, r ≥ 0 ⇒ every cell coefficient ≥ 0); `dominantFace` (foot points
  of the piece in dom with r, p∘φ, F∘φ > 0, Jacobian unit and tangential monomial ≠ 0);
  `exists_cell_coeff_pos_of_data` (all-minimal stratum + positive dominant-face measure ⇒ some cell
  coefficient > 0, via `coeff_pos_of_all_minimal`); `productCoeffD_pos`;
  **`boltzmannIntegral_isEquivalent_of_productCharts`** and **`_extremal`**:
  `0 < c ∧ Z_N[F] ~ c · N^{−λ*} (log N)^{k*}` (extremal stratum I₀ of chart i₀: all ratios = λ*,
  |I₀| − 1 = k*, positive dominant-face measure); `exists_extremal_stratum`.

## Where the paper's theorem (thm:expectation_expansion) stands
Exact chart–stratum decomposition (CCXXIV); divisor-free pieces negligible (CCXXVI); scalar-unit
atlases per piece (CCXXX–CCXXXIII); concrete atlas from monomial-chart data with product geometry
(CCXXXVIII); explicit face coefficient & positivity in the all-minimal case (CCXXXIV/CCXXXIX);
moments (CCXXXV/CCXL); END-TO-END for a cover of centred product charts at (λ*,k*) with c > 0 under
a dominant-face positive-mass hypothesis (CCXLII–CCXLV). Separately (earlier, via hironaka's
resolution `Q_all`): `IsMonomialChart.local_leading_term` (one chart, F(φ y₀) > 0 ⇒ ~ c N^{−λ} log^{m−1},
c > 0), `exponent_of_analytic` (unconditional Θ(N^{−λ*} log^{m*−1}) for analytic K ≥ 0, F > 0), and
`laplace_pair_eq_resolution_pair` (the RLCT formula).

## The honest gaps
(a) `ProductMonomialChart.weight_eq` requires the cover weight `R.weight i = coverWeight R.image i`
    (the COUNTING weight `1_{image i}(x) / #{j : x ∈ image j}`, see appendix) to factor through the
    inactive coordinates on dom. For a ONE-chart cover (ι = Unit) the weight is ≡ 1 on the image and
    r := 1 works; for genuine covers it is a strong hypothesis (the overlap pattern must be a product).
    The library fixes the weights as `coverWeight`; a `ResolutionCover` with user-supplied partition
    of unity does not exist.
(b) The coefficient `productCoeffD` is a sum of opaque tied cell coefficients (`ScalarUnitCell.coeff`
    is `q^{−λ}`-weighted face coefficient integrated against β); in the all-minimal case
    `coeff_of_all_minimal'` gives `faceConst · ∫_base β q^{−λ} A(·,0)` — the paper's
    eq:thm_leading_coeff shape — but this is not yet assembled into a formula for the total.
(c) Positivity hypotheses (F, p, r ≥ 0) are pointwise everywhere; the positive-mass hypothesis is
    stated in base coordinates z ↦ Ψ(z,0) of the stratum, not as a (d−|I|)-dimensional measure on
    the face inside ℝ^d.
(d) Not yet: statistical transfer — posterior expectation `E_N[φ] = Z_N[φ p]/Z_N[p]` (paper §4's
    object). With F = 1 also satisfying the package (continuous, ≥ 0, > 0), `Z_N[1] ~ c₁ N^{−λ*} log^{k*}`
    and `HasLeadingTerm.tendsto_div_ratio` (CCXL) give `E_N[φ] → c_φ / c₁` (same pair ⇒ scale ratio 1),
    including c_φ = 0 when φ vanishes on the dominant faces. This looks CHEAP now.
(e) Not yet: a phase unit depending on the normal coordinates (N3); identification of the model-cell
    moments with the tube fibre measures (N4); all orders (N5); a fidelity review of CCXLI–CCXLV (N7).

## Candidates for the next 3–5 units
(P1) Posterior expectations: `posteriorExpectation N φ := Z_N[φ p] / Z_N[p]`; `tendsto E_N[φ] → c_φ/c₁`
     for a cover of product charts (F = 1 satisfies the package); `c₁ > 0` needs only p, r ≥ 0 and one
     dominant face of positive measure (F = 1 drops out of the positivity condition); moments of the
     normal coordinates via CCXXXV/CCXL (`symMomentKernel`) — the paper's expectation expansion at leading
     order. Also: the ratio when φ has a DIFFERENT pair (`tendsto_div_mul_log` — φ subleading ⇒ E_N[φ] → 0
     at rate).
(P2) One-chart corollaries (N2): `ι = Unit`, `r = 1`, `weight_eq` automatic; the whole-box theorem
     for a single centred product box; connect to `chartIntegral`/`coverIntegral`. A concrete example
     (K = y₁² y₂², F = 1 on [−1,1]²: λ* = 1/2, k* = 1, c explicit?) as a regression test.
(P3) Coefficient formula (gap b): `productCoeffD` at (λ*,k*) = Σ_{tied (i,I)} 2^{|I|} · faceConst ·
     ∫_{base} β q^{−λ*} A(·,0) when every tied stratum is all-minimal (is every EXTREMAL tied piece
     automatically all-minimal? A tied piece has pieceLam = λ* and pieceMult − 1 = k*; not all its ratios
     need equal λ* unless |I| − 1 = k* — so no; but the extremal strata I₀ = {j : r_ij = λ*} are, and a
     tied non-all-minimal piece has coefficient given by the general `coeff` with a residual product).
(P4) Partition-of-unity covers (gap a): generalise `ResolutionCover` weights to a supplied measurable
     partition of unity subordinate to the images (`∑ w_i = 1 on ⋃ images`), keeping CCXXIV–CCXLV
     (which only use measurability/boundedness/sum-to-one of the weights?) — how much of the chain
     depends on `coverWeight`'s specific form?
(P5) N3 normal-dependent phase unit; (P6) N4 tube-measure identification; (P7) N7 fidelity review of
     CCXLI–CCXLV statements vs the paper.

Q1. Rank P1–P7 for the next 3–5 units, with reasons. My prior: P1 (cheap, paper-facing) → P3 → P2 → P7.
Q2. For the top two: module contracts — statements, hypotheses, reuse of existing declarations
    (appendix), pitfalls (e.g. for P1: Z_N[p] > 0 for all large N follows from `~` with c₁ > 0; the
    definition of the posterior expectation when Z_N[p] = 0; do we need p > 0 somewhere or is the
    dominant-face hypothesis with F = 1 enough; the log-degree bookkeeping when φ's pair differs).
Q3. Any mis-statement or vacuity in CCXLI–CCXLV (appendix)? In particular: is `weight_eq` consistent
    with `coverWeight` for a non-trivial cover (give a two-chart example where it holds), and is the
    dominant-face hypothesis correctly located (footCondition ∧ dom ∧ positivity)?

## Appendix — exact Lean statements

```lean
-- Grammar/ProductChartHypotheses.lean
structure ProductMonomialChart {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
    (K : (Fin d → ℝ) → ℝ) where
  /-- The phase exponents. -/
  e : Fin d →₀ ℕ
  /-- The Jacobian exponents. -/
  h : Fin d →₀ ℕ
  /-- The open monomial neighbourhood of the domain. -/
  W : Set (Fin d → ℝ)
  W_open : IsOpen W
  dom_subset : (R.chart i).dom ⊆ W
  /-- hironaka's monomial-chart certificate (its existential units are not the ones below). -/
  monomial : IsMonomialChart K (R.chart i).φ (R.chart i).dom e h W
  /-- The phase unit (a specific witness, carrying the independence hypothesis below). -/
  u : (Fin d → ℝ) → ℝ
  u_cont : ContinuousOn u W
  u_ne : ∀ y ∈ W, u y ≠ 0
  phase_eq : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e
  /-- The Jacobian unit. -/
  v : (Fin d → ℝ) → ℝ
  v_cont : ContinuousOn v W
  det_eq : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h
  /-- The compact inactive base. -/
  T : Set (Fin d → ℝ)
  T_compact : IsCompact T
  T_nonempty : T.Nonempty
  T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0
  /-- The normal radius. -/
  b : ℝ
  b_pos : 0 < b
  dom_eq : (R.chart i).dom = productDom e.support T b
  unit_indep : ∀ y ∈ (R.chart i).dom, u y = u (zeroOn e.support y)
  /-- The inactive factor of the cover weight. -/
  r : (Fin d → ℝ) → ℝ
  r_meas : Measurable r
  /-- A bound of the weight factor. -/
  Cr : ℝ
  r_bound : ∀ x, |r x| ≤ Cr
  weight_eq : ∀ y ∈ (R.chart i).dom, R.weight i ((R.chart i).Φ y) = r (zeroOn e.support y)

```

```lean
-- Grammar/ResolutionTransport.lean
noncomputable def coverWeight (A : ι → Set X) (i : ι) (x : X) : ℝ :=
```

```lean
-- Grammar/ResolutionTransport.lean
noncomputable def weight (i : ι) : (Fin d → ℝ) → ℝ := coverWeight R.image i

theorem measurable_weight (i : ι) : Measurable (R.weight i) :=
```

```lean
-- Grammar/LeadingTermInterface.lean
def HasLeadingTerm (Z : ℝ → ℝ) (c lam : ℝ) (k : ℕ) : Prop :=
```

```lean
-- Grammar/LeadingTermInterface.lean
noncomputable def boltzmannIntegral (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
```

```lean
-- Grammar/LeadingTermInterface.lean
noncomputable def pieceIntegral (D : ι → Finset (Fin d)) (ε : ℝ) (i : ι) (I : Finset (Fin d))
    (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
```

```lean
-- Grammar/SymmetricScalarUnitCells.lean
structure ScalarUnitCell (t : ℕ) where
  /-- The normal dimension is `n + 1`. -/
  n : ℕ
  /-- The density exponents. -/
  h : Fin (n + 1) → ℕ
  /-- The half phase exponents. -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- The box side. -/
  b : ℝ
  b_pos : 0 < b
  /-- The amplitude. -/
  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  A_cont : Continuous (Function.uncurry A)
  /-- The tangential base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The tangential weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_int : IntegrableOn βw base
  /-- The scalar phase unit. -/
  q : (Fin t → ℝ) → ℝ
  q_cont : Continuous q
  q_pos : ∀ z ∈ base, 0 < q z

```

```lean
-- Grammar/SymmetricScalarUnitCells.lean
structure FiniteScalarUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where
  /-- The cell index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The cells. -/
  cell : ι → ScalarUnitCell t
  /-- The exact decomposition. -/
  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N

```

```lean
-- Grammar/AdaptedPieceAtlas.lean
noncomputable def scalarAtlasPieceCoeff' {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    {tdim : ι → Finset (Fin d) → ℕ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas (tdim i I) (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ (e i).support ∧ I.Nonempty then
    ∑ j ∈ (At i I hI.1 hI.2).tied lam₀ k₀, ((At i I hI.1 hI.2).cell j).coeff
  else 0
```

```lean
-- Grammar/ProductChartPieceData.lean
theorem hasLeadingTerm_boltzmannIntegral_of_productCharts (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' (R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK) lam₀ k₀ i I)
      lam₀ k₀ :=
```

```lean
-- Grammar/ProductChartExtremalPair.lean
noncomputable def coverLam (hact : (R.activeCoords Ps).Nonempty) : ℝ :=
```

```lean
-- Grammar/ProductChartExtremalPair.lean
noncomputable def coverDeg (hact : (R.activeCoords Ps).Nonempty) : ℕ :=
```

```lean
-- Grammar/ProductChartExtremalPair.lean
theorem hasLeadingTerm_boltzmannIntegral_of_productCharts_extremal
    (hact : (R.activeCoords Ps).Nonempty) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (Ps i).e.support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff' (R.productAtlases Ps hK0 hε hεb hFc hpc hFm hF hK)
          (R.coverLam Ps hact) (R.coverDeg Ps hact) i I)
      (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
```

```lean
-- Grammar/ScalarCellNonneg.lean
theorem coeff_nonneg (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ z ∈ c.base, ∀ u ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 ≤ c.A z u) :
    0 ≤ c.coeff := by
```

```lean
-- Grammar/SingleChartScalarAtlas.lean
theorem exists_pieceAtlas_of_chart_data :
    ∃ At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
      (∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
        (minRatio (normalExp I hne h) (normalHalfExp I hne e))) ∧
      ∃ (q' : (Fin (d - (I.card - 1 + 1)) → ℝ) → ℝ)
        (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
        (hq'c : Continuous q')
        (hq'pos : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          0 < q' z)
        (hA'c : Continuous (Function.uncurry A'))
        (hk : ∀ a, 0 < normalHalfExp I hne e a)
        (hbase : IsCompact (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hβ : IntegrableOn (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).beta
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hamp' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).amp z n *
              F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
              A' z n * ∏ a, |n a| ^ normalExp I hne h a)
        (hphase' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
              q' z * ∏ a, n a ^ (2 * normalHalfExp I hne e a)),
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          q' z = scalarPhase I hne u e z) ∧
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            A' z n = R.pieceAmp i I hne h v (F := F) (p := p) z n) ∧
        At = R.pieceAtlas i D hε I hne
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ) hbase hβ rfl
          (normalExp I hne h) (normalHalfExp I hne e) hk q' hq'c hq'pos A' hA'c hamp' hphase' hFm
          hF hK hK0 := by
```

```lean
-- Grammar/ProductChartPositivity.lean
def dominantFace (F : (Fin d → ℝ) → ℝ) (p : TubeWeight d) :
    Set (Fin (d - (I.card - 1 + 1)) → ℝ) :=
```

```lean
-- Grammar/ProductChartPositivity.lean
def IsPieceAtlasData
    (At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)) : Prop :=
```

```lean
-- Grammar/ProductChartPositivity.lean
theorem cell_coeff_nonneg_of_data (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x)
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) (σ : At.ι) :
    0 ≤ (At.cell σ).coeff := by
```

```lean
-- Grammar/ProductChartPositivity.lean
theorem exists_cell_coeff_pos_of_data (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x) (hall : ∀ j ∈ I, P.ratio j = P.pieceLam I hne)
    (hpos : 0 < volume (P.dominantFace D ε I hne F p))
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∃ σ, 0 < (At.cell σ).coeff := by
```

```lean
-- Grammar/ProductChartPositivity.lean
noncomputable def productCoeffD (lam₀ : ℝ) (k₀ : ℕ) : ℝ :=
```

```lean
-- Grammar/ProductChartPositivity.lean
theorem boltzmannIntegral_isEquivalent_of_productCharts (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀)
    (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι)
    (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = lam₀) (hdeg : I₀.card - 1 = k₀)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ * powLogScale lam₀ k₀ N :=
```

```lean
-- Grammar/ProductChartPositivity.lean
theorem boltzmannIntegral_isEquivalent_of_productCharts_extremal
    (hact : (R.activeCoords Ps).Nonempty) (hF0 : ∀ x, 0 ≤ F x) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀ F p)) :
    0 < R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) ∧
      R.boltzmannIntegral F K p ~[atTop] fun N =>
        R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) *
          powLogScale (R.coverLam Ps hact) (R.coverDeg Ps hact) N :=
```

```lean
-- Grammar/ProductChartPositivity.lean
theorem exists_extremal_stratum (hact : (R.activeCoords Ps).Nonempty) :
    ∃ (i₀ : ι) (I₀ : Finset (Fin d)), I₀ ⊆ (Ps i₀).e.support ∧ I₀.Nonempty ∧
      (∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact) ∧ I₀.card - 1 = R.coverDeg Ps hact := by
```

```lean
-- Grammar/PositiveScalarCoefficient.lean
theorem coeff_of_all_minimal' (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
    c.coeff = c.faceConst * ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
  rw [c.coeff_of_all_minimal hall, box_prefactor_of_all_minimal c.h c.k c.k_pos hall c.b_pos,
    one_mul]
```

```lean
-- Grammar/LogRatioSymmetricMoments.lean
theorem HasLeadingTerm.tendsto_div_ratio (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) :
    Tendsto (fun N => (Z₁ N / Z₂ N) / (powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N)) atTop
      (𝓝 (c₁ / c₂)) := by
```

```lean
-- Grammar/PositiveScalarCoefficient.lean
noncomputable def faceConst : ℝ := Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k
  i : ℝ))

theorem faceConst_pos : 0 < c.faceConst := by
```