/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartVar

/-!
# The piece bridge with a source amplitude (CCLXXIV)

The chart–stratum piece machinery consumes the observable only through its pull-back `F ∘ φ_i` on
the chart domain. This file generalises the piece integral to an arbitrary **source amplitude**
`G : (Fin d → ℝ) → ℝ` — measurable, continuous on the chart domain — in place of `F ∘ φ_i`
(consult #85 unit 2, first half):

* `sourcePieceIntegral R i D ε I G K p N = ∫_{piece} boltzmannChartDensity_i(N) · G`, with
  `pieceIntegral … F … = sourcePieceIntegral … (F ∘ φ_i) …` definitionally;
* the adapted form, the identification with the symmetric integral of the variable-unit cell
  (`sourcePieceIntegral_eq_varSymIntegral`), the orthant atlas `sourceVarPieceAtlas`;
* ★ `exists_sourceVarPieceAtlas_of_chart_data`: the atlas with exposed cells from monomial-chart
  data, amplitude `sourcePieceAmp = |v| · |y_tang^h| · (p ∘ φ) · G`;
* for a variable-unit product package: the data certificate `IsSourceVarPieceAtlasData`, the chosen
  atlas `sourcePieceAtlasV`, nonnegativity of the cell coefficients for `G, p, r ≥ 0`, the
  **source dominant face** (`0 < G` at the foot in place of `0 < F ∘ φ`) and positivity of some cell
  coefficient of an all-minimal stratum whose source dominant face has positive measure.

A source amplitude is not in general the pull-back of a target function continuous across the
exceptional locus (the blow-up wedge), which is why the localisation of the resolved-space programme
is phrased on the source.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- **The source-weighted chart–stratum piece integral** `∫_{piece} w_i(N) · G`. -/
noncomputable def sourcePieceIntegral (D : ι → Finset (Fin d)) (ε : ℝ) (i : ι)
    (I : Finset (Fin d)) (G K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) : ℝ :=
  ∫ y in sizePiece (D i) ε I, R.boltzmannChartDensity i N K p y * G y

theorem pieceIntegral_eq_sourcePieceIntegral (D : ι → Finset (Fin d)) (ε : ℝ) (i : ι)
    (I : Finset (Fin d)) (F K : (Fin d → ℝ) → ℝ) (p : TubeWeight d) (N : ℝ) :
    R.pieceIntegral D ε i I F K p N =
      R.sourcePieceIntegral D ε i I (fun y => F ((R.chart i).φ y)) K p N := rfl

variable (i : ι) {K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- The static chart density is integrable. -/
theorem integrable_boltzmannChartDensity_zero (p : TubeWeight d) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) : Integrable (R.boltzmannChartDensity i 0 K p) := by
  have h := R.integrable_boltzmannChartDensity_zero_mul i (F := fun _ => (1 : ℝ)) (p := p)
    measurable_const ?_ hK hK0
  · simpa using h
  · refine Measure.integrableOn_of_bounded (M := p.bound)
      (isCompact_iUnion fun i => R.isCompact_image i).measure_lt_top.ne
      (measurable_const.mul p.measurable).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (p.nonneg x)]
    exact p.le_bound x

variable {G : (Fin d → ℝ) → ℝ}

/-- The static density times a source amplitude bounded on the domain is integrable. -/
theorem integrable_boltzmannChartDensity_zero_mul_source (hGm : Measurable G) {C : ℝ}
    (hGb : ∀ y ∈ (R.chart i).dom, |G y| ≤ C) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) :
    Integrable fun y => R.boltzmannChartDensity i 0 K p y * G y := by
  have h := (R.integrable_boltzmannChartDensity_zero i p hK hK0).bdd_mul (c := max C 0)
    (f := (R.chart i).dom.indicator G)
    (hGm.indicator (R.chart i).measurableSet_dom).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      by_cases hy : y ∈ (R.chart i).dom
      · rw [indicator_of_mem hy]
        exact (hGb y hy).trans (le_max_left _ _)
      · rw [indicator_of_notMem hy, abs_zero]
        exact le_max_right _ _)
  refine h.congr (Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : y ∈ (R.chart i).dom
  · rw [indicator_of_mem hy, mul_comm]
  · have h0 : R.boltzmannChartDensity i 0 K p y = 0 := by
      unfold boltzmannChartDensity
      rw [indicator_of_notMem hy]
    rw [h0, mul_zero, zero_mul]

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d))

/-- The static density times the Boltzmann factor times a source amplitude, on a piece. -/
theorem integrable_indicator_static_mul_source (hGm : Measurable G)
    (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ}
    (hN : 0 ≤ N) :
    Integrable fun y => (sizePiece (D i) ε I).indicator (R.boltzmannChartDensity i 0 K p) y *
      (Real.exp (-N * K ((R.chart i).Φ y)) * G y) := by
  obtain ⟨C, hC⟩ := (R.chart i).dom_compact.exists_bound_of_continuousOn hGc
  have h := ((R.integrable_boltzmannChartDensity_zero_mul_source i (p := p) hGm
    (fun y hy => (Real.norm_eq_abs _).symm.trans_le (hC y hy)) hK hK0).bdd_mul (c := 1)
    (f := fun y => Real.exp (-N * K ((R.chart i).Φ y)))
    (Real.measurable_exp.comp (measurable_const.mul
      (hK.comp (R.measurable_chart_Φ i)))).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hN (hK0 _)))).indicator (measurableSet_sizePiece (D i) ε I)
  refine h.congr (Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : y ∈ sizePiece (D i) ε I
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

/-- **The source-weighted piece integral in adapted form.** -/
theorem sourcePieceIntegral_eq_adapted (hne : I.Nonempty)
    (A : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I))
    (hGm : Measurable G) (hGc : ContinuousOn G (R.chart i).dom) (hK : Measurable K)
    (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    R.sourcePieceIntegral D ε i I G K p N =
      ∫ z in A.base, A.beta z * ∫ n in A.normalBox, A.amp z n *
        (Real.exp (-N * K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))) *
          G (planeSplit (stratumSplit I hne) (z, n))) := by
  rw [← A.integral_piece_eq _ (measurableSet_sizePiece (D i) ε I)
    (fun y => Real.exp (-N * K ((R.chart i).Φ y)) * G y)
    (R.integrable_indicator_static_mul_source i D ε I hGm hGc hK hK0 hN)]
  unfold sourcePieceIntegral
  refine setIntegral_congr_fun (measurableSet_sizePiece (D i) ε I) fun y _ => ?_
  rw [R.boltzmannChartDensity_eq_exp_mul]
  ring

end ResolutionCover

/-! ### The variable-unit cell and atlas of a source-weighted piece -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  {G K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (Ad : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
    (sizePiece (D i) ε I))
  (hbase : IsCompact Ad.base) (hβ : IntegrableOn Ad.beta Ad.base)
  (hbox : Ad.normalBox = Metric.ball 0 ε)
  (h k : Fin (I.card - 1 + 1) → ℕ) (hk : ∀ j, 0 < k j)
  (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hqv : Continuous (Function.uncurry qv))
  (hqv_pos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
  (A : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))
  (hamp : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    Ad.amp z n * G (planeSplit (stratumSplit I hne) (z, n)) = A z n * ∏ j, |n j| ^ h j)
  (hphase : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
    K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) = qv z n * ∏ j, n j ^ (2 * k j))
  (hGm : Measurable G) (hGc : ContinuousOn G (R.chart i).dom)
  (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)

include hbox hamp hphase hGm hGc hK hK0 in
/-- **The source-weighted piece integral is the symmetric integral of its variable-unit cell.** -/
theorem sourcePieceIntegral_eq_varSymIntegral {N : ℝ} (hN : 0 ≤ N) :
    R.sourcePieceIntegral D ε i I G K p N =
      (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).symIntegral N := by
  rw [R.sourcePieceIntegral_eq_adapted i D ε I hne Ad hGm hGc hK hK0 hN]
  unfold VarUnitCell.symIntegral
  refine setIntegral_congr_fun hbase.isClosed.measurableSet fun z hz => ?_
  congr 1
  change _ = symVarKernel (I.card - 1) h k ε qv A z N
  unfold symVarKernel
  rw [hbox]
  have hinner : ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * (Real.exp (-N * K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))) *
        G (planeSplit (stratumSplit I hne) (z, n))) =
      ∫ n in Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A z n * (∏ j, |n j| ^ h j) * Real.exp (-(qv z n * N * ∏ j, n j ^ (2 * k j))) := by
    refine setIntegral_congr_fun measurableSet_ball fun n hn => ?_
    rw [hphase z hz n hn, ← hamp z hz n hn]
    ring_nf
  rw [hinner, ball_eq_piBox_Ioo hε]
  exact setIntegral_congr_set (piBox_Ioo_ae_eq_Ioc ε)

include hbox hamp hphase hGm hGc hK hK0 in
/-- **The orthant atlas of a source-weighted piece in variable normal form.** -/
noncomputable def sourceVarPieceAtlas :
    FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p) where
  ι := Fin (I.card - 1 + 1) → Bool
  cell := (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).reflected
  eq := fun N hN => by
    rw [R.sourcePieceIntegral_eq_varSymIntegral i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos
      A hA hamp hphase hGm hGc hK hK0 hN]
    exact (R.varPieceCell i D hε I hne Ad hbase hβ h k hk qv hqv hqv_pos A hA).symIntegral_eq_sum hN

include hbox hamp hphase hGm hGc hK hK0 in
theorem sourceVarPieceAtlas_cell_lam (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.sourceVarPieceAtlas i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos A hA hamp hphase
      hGm hGc hK hK0).cell σ).lam = minRatio h k := rfl

include hbox hamp hphase hGm hGc hK hK0 in
theorem sourceVarPieceAtlas_cell_mult (σ : Fin (I.card - 1 + 1) → Bool) :
    ((R.sourceVarPieceAtlas i D hε I hne Ad hbase hβ hbox h k hk qv hqv hqv_pos A hA hamp hphase
      hGm hGc hK hK0).cell σ).mult = multCount (ratioExp h k) (minRatio h k) := rfl

end ResolutionCover

/-! ### The source-weighted atlas from chart data -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (I : Finset (Fin d)) (hne : I.Nonempty) (h : Fin d →₀ ℕ) (v : (Fin d → ℝ) → ℝ)
  {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- **The source piece amplitude** `|v(Ψ(z,n))| · |y_tang^h(z)| · p(φ(Ψ(z,n))) · G(Ψ(z,n))`. -/
noncomputable def sourcePieceAmp (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (n : Fin (I.card - 1 + 1) → ℝ) : ℝ :=
  |v (planeSplit (stratumSplit I hne) (z, n))| * |tangentialMonomial I hne h z| *
    p.w ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) *
      G (planeSplit (stratumSplit I hne) (z, n))

theorem sourcePieceAmp_nonneg (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ) :
    0 ≤ R.sourcePieceAmp i I hne h v (G := G) (p := p) z n :=
  mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hp0 _)) (hG0 _)

variable (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (e : Fin d →₀ ℕ) (hD : D i = e.support)
  (hI : I ⊆ e.support) {K : (Fin d → ℝ) → ℝ} (hK0 : ∀ x, 0 ≤ K x) {W : Set (Fin d → ℝ)}
  (hW : IsOpen W) (hsub : (R.chart i).dom ⊆ W) (u : (Fin d → ℝ) → ℝ) (hu : ContinuousOn u W)
  (hu0 : ∀ y ∈ W, u y ≠ 0) (hKu : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e)
  (hv : ContinuousOn v W)
  (hdet : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h)
  (T' : Set (Fin d → ℝ)) (hT' : IsClosed T') (ρT : (Fin d → ℝ) → ℝ) (hρm : Measurable ρT)
  {Cρ : ℝ} (hρb : ∀ x, |ρT x| ≤ Cρ)
  (hdom : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
  (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y))
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) W)
  (hGm : Measurable G) (hGc : ContinuousOn G (R.chart i).dom)
  (hK : Measurable K) (hy₀ : ∃ y₀ ∈ W, ∀ j ∈ I, y₀ j = 0)

include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hT' hρm hρb hdom hρ hpc hGm hGc hK hy₀ in
/-- **The variable-unit atlas of a source-weighted chart–stratum piece from monomial-chart data,
with its cells exposed**: the orthant atlas of the variable-unit cell on the compact-base piece
density, unit the variable phase, amplitude `sourcePieceAmp`; all cells at the pair
`(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`. -/
theorem exists_sourceVarPieceAtlas_of_chart_data :
    ∃ At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
      (∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
        (minRatio (normalExp I hne h) (normalHalfExp I hne e))) ∧
      ∃ (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
        (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
        (hqv : Continuous (Function.uncurry qv))
        (hqv_pos : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
        (hA'c : Continuous (Function.uncurry A'))
        (hk : ∀ a, 0 < normalHalfExp I hne e a)
        (hbase : IsCompact (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hβ : IntegrableOn (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).beta
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
        (hamp' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).amp z n *
              G (planeSplit (stratumSplit I hne) (z, n)) =
              A' z n * ∏ a, |n a| ^ normalExp I hne h a)
        (hphase' : ∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
              qv z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a)),
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            qv z n = varPhase I hne u e z n) ∧
        (∀ z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base,
          ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
            A' z n = R.sourcePieceAmp i I hne h v (G := G) (p := p) z n) ∧
        At = R.sourceVarPieceAtlas i D hε I hne
          (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ) hbase hβ rfl
          (normalExp I hne h) (normalHalfExp I hne e) hk qv hqv hqv_pos A' hA'c hamp' hphase' hGm
          hGc hK hK0 := by
  -- the adapted density with compact base
  set Ad := R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ with hAd
  have hbase : IsCompact Ad.base :=
    R.chartPieceDensity_base_compact i D hε I hne e hD hI K p T' hT' ρT hdom hρ
  have hmemdom : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := fun z hz n hn =>
    R.mem_dom_of_mem_base i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn
  have hmemdomc : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := fun z hz n hn =>
    R.mem_dom_of_mem_base_closedBall i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn
  -- the base weight is integrable
  have hβ : IntegrableOn Ad.beta Ad.base := by
    have hβeq : Ad.beta = fun z => T'.indicator ρT (planeSplit (stratumSplit I hne) (z, 0)) := rfl
    rw [hβeq]
    refine Measure.integrableOn_of_bounded hbase.measure_lt_top.ne ?_ (M := Cρ) ?_
    · exact ((hρm.indicator hT'.measurableSet).comp
        ((planeSplit (stratumSplit I hne)).continuous.comp
          (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs]
      by_cases hx : planeSplit (stratumSplit I hne) (z, 0) ∈ T'
      · rw [indicator_of_mem hx]
        exact hρb _
      · rw [indicator_of_notMem hx, abs_zero]
        exact (abs_nonneg _).trans (hρb 0)
  -- parity of the normal exponents
  obtain ⟨y₀, hy₀W, hy₀I⟩ := hy₀
  have hK0' : ∀ y ∈ W, 0 ≤ K ((R.chart i).φ y) := fun y _ => hK0 _
  have hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a := fun a =>
    normalExp_eq_two_mul_halfExp I hne e hW (K := fun y => K ((R.chart i).φ y)) hKu hK0' hy₀W
      (hu.continuousAt (hW.mem_nhds hy₀W)) (hu0 y₀ hy₀W) hy₀I a
  have he : ∀ j ∈ I, 0 < e j := fun j hj =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (hI hj))
  have hk : ∀ a, 0 < normalHalfExp I hne e a := normalHalfExp_pos I hne e he hpar
  -- the variable phase on the base × ball
  have hphase0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        varPhase I hne u e z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [(R.chart i).Φ_eqOn (hmemdom z hz n hn)]
    exact phase_varNormalForm I hne u e (K := fun y => K ((R.chart i).φ y))
      (hKu _ (hsub (hmemdom z hz n hn))) hpar
  have hfootOf : ∀ z ∈ Ad.base,
      planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I := fun z hz => by
    rw [hAd, chartPieceDensity_base] at hz
    exact hz.1.1
  have hΨz : ∀ z : Fin (d - (I.card - 1 + 1)) → ℝ, Continuous fun n : Fin (I.card - 1 + 1) → ℝ =>
      planeSplit (stratumSplit I hne) (z, n) := fun z =>
    (planeSplit (stratumSplit I hne)).continuous.comp (continuous_const.prodMk continuous_id)
  have hqpos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      0 < varPhase I hne u e z n := fun z hz n hn => by
    refine varPhase_pos_closedBall I hne u e (K := fun y => K ((R.chart i).φ y)) hε
      (fun n hn => hKu _ (hsub (hmemdom z hz n hn))) hpar (fun n _ => hK0 _)
      (fun n hn => hu0 _ (hsub (hmemdomc z hz n hn)))
      (hu.comp (hΨz z).continuousOn fun n hn => hsub (hmemdomc z hz n hn)) ?_ hn
    intro j hj hjI h0
    have := hfootOf z hz j (by rw [hD]; exact hj) hjI
    apply this
    rw [h0, abs_zero]
    exact hε
  -- continuous representatives on the compact base × closed ball
  have hΨ : Continuous fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q := (planeSplit (stratumSplit I hne)).continuous
  have hmapsD : MapsTo (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q) (Ad.base ×ˢ Metric.closedBall 0 ε) (R.chart i).dom :=
    fun q hq => hmemdomc q.1 hq.1 q.2 hq.2
  have hmaps : MapsTo (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q) (Ad.base ×ˢ Metric.closedBall 0 ε) W :=
    fun q hq => hsub (hmapsD hq)
  have hqcont : ContinuousOn (Function.uncurry (varPhase I hne u e))
      (Ad.base ×ˢ Metric.closedBall 0 ε) :=
    (hu.comp hΨ.continuousOn hmaps).mul
      ((continuous_tangentialMonomial I hne e).comp continuous_fst).continuousOn
  obtain ⟨qv'', hqv''c, hqv''eq⟩ := exists_continuous_extension_of_isClosed
    (hbase.isClosed.prod Metric.isClosed_closedBall) hqcont
  have hqv : Continuous (Function.uncurry (Function.curry qv'')) := by
    rwa [Function.uncurry_curry]
  have hqv_pos : ∀ z ∈ Ad.base, ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      0 < Function.curry qv'' z n := fun z hz n hn => by
    change 0 < qv'' (z, n)
    rw [hqv''eq (z, n) ⟨hz, hn⟩]
    exact hqpos z hz n hn
  have hphase' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        Function.curry qv'' z n * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [hphase0 z hz n hn]
    congr 1
    exact (hqv''eq (z, n) ⟨hz, Metric.ball_subset_closedBall hn⟩).symm
  -- the amplitude identity on the base and the open ball
  have hamp0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * G (planeSplit (stratumSplit I hne) (z, n)) =
        R.sourcePieceAmp i I hne h v (G := G) (p := p) z n *
          ∏ a, |n a| ^ normalExp I hne h a :=
    fun z hz n hn => by
      have hdomzn := hmemdom z hz n hn
      have hampeq : Ad.amp z n = (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
          p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) := rfl
      rw [hampeq, (R.chart i).Φ_eqOn hdomzn]
      unfold ResolutionChart.jac sourcePieceAmp
      rw [hdet _ (hsub hdomzn), abs_mul, abs_monomialEval_planeSplit]
      ring
  have hAcont : ContinuousOn (Function.uncurry (R.sourcePieceAmp i I hne h v (G := G) (p := p)))
      (Ad.base ×ˢ Metric.closedBall 0 ε) := by
    have h1 := (hv.comp hΨ.continuousOn hmaps).abs
    have h2 : ContinuousOn (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)
        => |tangentialMonomial I hne h q.1|) (Ad.base ×ˢ Metric.closedBall 0 ε) :=
      ((continuous_tangentialMonomial I hne h).comp continuous_fst).continuousOn.abs
    have h3 := hpc.comp hΨ.continuousOn hmaps
    have h4 := hGc.comp hΨ.continuousOn hmapsD
    exact ((h1.mul h2).mul h3).mul h4
  obtain ⟨A'', hA''c, hA''eq⟩ := exists_continuous_extension_of_isClosed
    (hbase.isClosed.prod Metric.isClosed_closedBall) hAcont
  have hA'c : Continuous (Function.uncurry (Function.curry A'')) := by
    rwa [Function.uncurry_curry]
  have hamp' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * G (planeSplit (stratumSplit I hne) (z, n)) =
        Function.curry A'' z n * ∏ a, |n a| ^ normalExp I hne h a := fun z hz n hn => by
    rw [hamp0 z hz n hn]
    congr 1
    exact (hA''eq (z, n) ⟨hz, Metric.ball_subset_closedBall hn⟩).symm
  exact ⟨R.sourceVarPieceAtlas i D hε I hne Ad hbase hβ rfl (normalExp I hne h)
    (normalHalfExp I hne e) hk (Function.curry qv'') hqv hqv_pos (Function.curry A'') hA'c hamp'
    hphase' hGm hGc hK hK0,
    fun _ => rfl, fun _ => rfl, Function.curry qv'', Function.curry A'', hqv, hqv_pos, hA'c, hk,
    hbase, hβ, hamp', hphase', fun z hz n hn => hqv''eq (z, n) ⟨hz, hn⟩,
    fun z hz n hn => hA''eq (z, n) ⟨hz, hn⟩, rfl⟩

end ResolutionCover

/-! ### Source-weighted piece atlases of a variable-unit product package -/

namespace ProductMonomialChartVar

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} {i : ι} {K : (Fin d → ℝ) → ℝ}
  (P : ProductMonomialChartVar R i K)

section Face

variable (D : ι → Finset (Fin d)) (ε : ℝ) (I : Finset (Fin d)) (hne : I.Nonempty)

/-- **The source dominant face of the stratum piece `I`**: the foot points of the piece in the chart
domain at which the cover-weight factor, the pulled-back prior and the SOURCE amplitude are positive
and the Jacobian unit and the tangential Jacobian monomial are nonzero. -/
def sourceDominantFace (G : (Fin d → ℝ) → ℝ) (p : TubeWeight d) :
    Set (Fin (d - (I.card - 1 + 1)) → ℝ) :=
  {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I ∧
    planeSplit (stratumSplit I hne) (z, 0) ∈ (R.chart i).dom ∧
    0 < P.pieceWeight (planeSplit (stratumSplit I hne) (z, 0)) ∧
    0 < p.w ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, 0))) ∧
    0 < G (planeSplit (stratumSplit I hne) (z, 0)) ∧
    P.v (planeSplit (stratumSplit I hne) (z, 0)) ≠ 0 ∧
    tangentialMonomial I hne P.h z ≠ 0}

end Face

section Density

variable {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b) {D : ι → Finset (Fin d)} (hD : D i = P.e.support)
  (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

include hεb hD hI in
/-- Source dominant-face points lie in the base of the piece density. -/
theorem mem_pieceDensity_base_of_mem_sourceDominantFace {G : (Fin d → ℝ) → ℝ} (p : TubeWeight d)
    {z : Fin (d - (I.card - 1 + 1)) → ℝ} (hz : z ∈ P.sourceDominantFace D ε I hne G p) :
    z ∈ (P.pieceDensity hε hεb hD I hI hne p).base := by
  obtain ⟨hfoot, hdom, -, -, -, -, -⟩ := hz
  have hpiece : planeSplit (stratumSplit I hne) (z, 0) ∈ sizePiece (D i) ε I := by
    have htube : planeSplit (stratumSplit I hne) (z, 0) ∈
        (coordPlaneTube (stratumSplit I hne) ε hε).U := by
      change ‖planeSplit (stratumSplit I hne) (z, 0) -
        planeFoot (stratumSplit I hne) (planeSplit (stratumSplit I hne) (z, 0))‖ < ε
      rw [norm_planeSplit_sub_foot, norm_zero]
      exact hε
    refine (mem_sizePiece_iff_of_mem_tube (D i) hε I hne htube).2 ?_
    rwa [planeFoot_planeSplit]
  have hT' := (P.piece_dom_iff hεb hD I hI hne _ hpiece).1 hdom
  rw [planeFoot_planeSplit] at hT'
  unfold pieceDensity
  rw [ResolutionCover.chartPieceDensity_base]
  exact ⟨⟨hfoot, mem_tangentialCarrier_of_mem (stratumSplit I hne) hdom⟩, hT'⟩

end Density

section Atlas

variable (hK0 : ∀ x, 0 ≤ K x) {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ P.b)
  {D : ι → Finset (Fin d)} (hD : D i = P.e.support) {G : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) P.W)
  (hGm : Measurable G) (hGc : ContinuousOn G (R.chart i).dom)
  (hK : Measurable K) (I : Finset (Fin d)) (hI : I ⊆ P.e.support) (hne : I.Nonempty)

/-- **The data certificate of a source-weighted piece atlas**: the orthant atlas over the piece
density, unit the variable phase, amplitude `sourcePieceAmp` on the base times the closed ball. -/
def IsSourceVarPieceAtlasData
    (At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p)) :
    Prop :=
  ∃ (qv : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
    (A' : (Fin (d - (I.card - 1 + 1)) → ℝ) → (Fin (I.card - 1 + 1) → ℝ) → ℝ)
    (hqv : Continuous (Function.uncurry qv))
    (hqv_pos : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε, 0 < qv z n)
    (hA'c : Continuous (Function.uncurry A'))
    (hk : ∀ a, 0 < normalHalfExp I hne P.e a)
    (hbase : IsCompact (P.pieceDensity hε hεb hD I hI hne p).base)
    (hβ : IntegrableOn (P.pieceDensity hε hεb hD I hI hne p).beta
      (P.pieceDensity hε hεb hD I hI hne p).base)
    (hamp' : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        (P.pieceDensity hε hεb hD I hI hne p).amp z n *
          G (planeSplit (stratumSplit I hne) (z, n)) =
          A' z n * ∏ a, |n a| ^ normalExp I hne P.h a)
    (hphase' : ∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
          qv z n * ∏ a, n a ^ (2 * normalHalfExp I hne P.e a)),
    (∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        qv z n = varPhase I hne P.u P.e z n) ∧
    (∀ z ∈ (P.pieceDensity hε hεb hD I hI hne p).base,
      ∀ n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε,
        A' z n = R.sourcePieceAmp i I hne P.h P.v (G := G) (p := p) z n) ∧
    At = R.sourceVarPieceAtlas i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ rfl
      (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c hamp' hphase' hGm
      hGc hK hK0

include hpc in
/-- **Every stratum piece of a variable-unit product chart has a source-weighted piece atlas with
exposed cells**, all at the divisor pair of the stratum. -/
theorem exists_sourceVarPieceAtlas_data :
    ∃ At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p),
      (∀ σ, (At.cell σ).lam = P.pieceLam I hne) ∧ (∀ σ, (At.cell σ).mult = P.pieceMult I hne) ∧
      P.IsSourceVarPieceAtlasData hK0 hε hεb hD hGm hGc hK I hI hne At := by
  have hy₀ : ∃ y₀ ∈ P.W, ∀ j ∈ I, y₀ j = 0 := by
    obtain ⟨y₀, hy₀, hz⟩ := exists_zeroPoint P.e.support P.T P.b P.T_nonempty P.T_zero P.b_pos.le
    exact ⟨y₀, P.dom_subset (P.mem_dom_of_mem_productDom hy₀), fun j hj => hz j (hI hj)⟩
  obtain ⟨At, hlam, hmult, qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA',
      hAt⟩ :=
    R.exists_sourceVarPieceAtlas_of_chart_data i I hne P.h P.v D hε P.e hD hI hK0 P.W_open
      P.dom_subset P.u P.u_cont P.u_ne P.phase_eq P.v_cont P.det_eq (P.pieceFootSet I)
      (P.isClosed_pieceFootSet I) P.pieceWeight
      (P.r_meas.comp (continuous_zeroOn _).measurable) (fun x => P.r_bound _)
      (P.piece_dom_iff hεb hD I hI hne) (P.piece_weight_eq I hI hne) hpc hGm hGc hK hy₀
  exact ⟨At, fun σ => (hlam σ).trans (P.pieceLam_eq hK0 I hI hne),
    fun σ => (hmult σ).trans (P.pieceMult_eq hK0 I hI hne),
    qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', hq', hA', hAt⟩

/-- **The chosen source-weighted piece atlas with exposed cells** (classical choice, once). -/
noncomputable def sourcePieceAtlasV :
    FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p) :=
  Classical.choose (P.exists_sourceVarPieceAtlas_data hK0 hε hεb hD hpc hGm hGc hK I hI hne)

theorem sourcePieceAtlasV_cell_lam (σ) :
    ((P.sourcePieceAtlasV hK0 hε hεb hD hpc hGm hGc hK I hI hne).cell σ).lam =
      P.pieceLam I hne :=
  (Classical.choose_spec
    (P.exists_sourceVarPieceAtlas_data hK0 hε hεb hD hpc hGm hGc hK I hI hne)).1 σ

theorem sourcePieceAtlasV_cell_mult (σ) :
    ((P.sourcePieceAtlasV hK0 hε hεb hD hpc hGm hGc hK I hI hne).cell σ).mult =
      P.pieceMult I hne :=
  (Classical.choose_spec
    (P.exists_sourceVarPieceAtlas_data hK0 hε hεb hD hpc hGm hGc hK I hI hne)).2.1 σ

theorem sourcePieceAtlasV_data :
    P.IsSourceVarPieceAtlasData hK0 hε hεb hD hGm hGc hK I hI hne
      (P.sourcePieceAtlasV hK0 hε hεb hD hpc hGm hGc hK I hI hne) :=
  (Classical.choose_spec
    (P.exists_sourceVarPieceAtlas_data hK0 hε hεb hD hpc hGm hGc hK I hI hne)).2.2

/-- **Every cell coefficient of a certified source-weighted piece atlas is nonnegative** when the
source amplitude, the prior and the cover-weight factor are nonnegative. -/
theorem sourceCell_coeff_nonneg_of_data (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x)
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p)}
    (hAt : P.IsSourceVarPieceAtlasData hK0 hε hεb hD hGm hGc hK I hI hne At) (σ : At.ι) :
    0 ≤ (At.cell σ).coeff := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', -, hA', rfl⟩ := hAt
  exact VarUnitCell.reflected_coeff_nonneg
    (R.varPieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
      (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c)
    (Eventually.of_forall fun z => P.pieceDensity_beta_nonneg hε hεb hD I hI hne p hr0 z)
    (fun z hz u hu => by
      change 0 ≤ A' z u
      rw [hA' z hz u hu]
      exact R.sourcePieceAmp_nonneg i I hne P.h P.v hG0 hp0 z u) σ

/-- **Some cell coefficient of a certified source-weighted piece atlas is positive** for an
all-minimal stratum whose source dominant face has positive measure. -/
theorem exists_sourceCell_coeff_pos_of_data (hG0 : ∀ y, 0 ≤ G y) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ x, 0 ≤ P.r x) (hall : ∀ j ∈ I, P.ratio j = P.pieceLam I hne)
    (hpos : 0 < volume (P.sourceDominantFace D ε I hne G p))
    {At : FiniteVarUnitAtlas (d - (I.card - 1 + 1)) (R.sourcePieceIntegral D ε i I G K p)}
    (hAt : P.IsSourceVarPieceAtlasData hK0 hε hεb hD hGm hGc hK I hI hne At) :
    ∃ σ, 0 < (At.cell σ).coeff := by
  obtain ⟨qv, A', hqv, hqv_pos, hA'c, hk, hbase, hβ, hamp', hphase', -, hA', rfl⟩ := hAt
  have hallc : ∀ a, ratioExp (normalExp I hne P.h) (normalHalfExp I hne P.e) a =
      minRatio (normalExp I hne P.h) (normalHalfExp I hne P.e) := fun a => by
    rw [ratioExp_normal_eq I hne P.e P.h (P.normalExp_eq_two_mul hK0 I hI hne) a,
      P.pieceLam_eq hK0 I hI hne]
    exact hall _ (stratumSplit_symm_inr_mem I hne a)
  have hbaseM : MeasurableSet (P.pieceDensity hε hεb hD I hI hne p).base :=
    hbase.isClosed.measurableSet
  refine ⟨(fun _ => false : Fin (I.card - 1 + 1) → Bool), lt_of_lt_of_eq
    (VarUnitCell.coeff_pos_of_all_minimal
      (R.varPieceCell i D hε I hne (P.pieceDensity hε hεb hD I hI hne p) hbase hβ
        (normalExp I hne P.h) (normalHalfExp I hne P.e) hk qv hqv hqv_pos A' hA'c) hallc
      (Eventually.of_forall fun z => P.pieceDensity_beta_nonneg hε hεb hD I hI hne p hr0 z) ?_ ?_)
    (VarUnitCell.reflected_coeff_of_all_minimal _ hallc _).symm⟩
  · refine (ae_restrict_iff' hbaseM).2 (Eventually.of_forall fun z hz => ?_)
    change 0 ≤ A' z 0
    rw [hA' z hz 0 (Metric.mem_closedBall_self hε.le)]
    exact R.sourcePieceAmp_nonneg i I hne P.h P.v hG0 hp0 z 0
  · refine lt_of_lt_of_le hpos (measure_mono fun z hz => ?_)
    have hzb := P.mem_pieceDensity_base_of_mem_sourceDominantFace hε hεb hD I hI hne p hz
    obtain ⟨-, -, hr, hp, hGz, hv, ht⟩ := hz
    refine ⟨hzb, ?_, ?_⟩
    · change 0 < (P.pieceFootSet I).indicator P.pieceWeight (planeSplit (stratumSplit I hne) (z, 0))
      rw [Set.indicator_of_mem (P.foot_mem_pieceFootSet_of_mem_base hε hεb hD I hI hne p hzb)]
      exact hr
    · change 0 < A' z 0
      rw [hA' z hzb 0 (Metric.mem_closedBall_self hε.le)]
      exact mul_pos (mul_pos (mul_pos (abs_pos.2 hv) (abs_pos.2 ht)) hp) hGz

end Atlas

end ProductMonomialChartVar

end Grammar
