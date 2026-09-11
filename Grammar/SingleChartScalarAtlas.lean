/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CompactProductChartDensity

/-!
# The scalar-unit atlas of a chart–stratum piece from monomial-chart data

Unit 3 of consult #77 (`tide-log/gpt6_bigpicture_v77.md`): the **first concrete constructor** of
the hypotheses of the conditional global theorems, from the data of a monomial chart. For a chart
`φ_i` with `K∘φ_i = u · y^e`, `det Dφ_i = v · y^h` on an open `W ⊇ dom_i` (`K ≥ 0`), a nonempty
stratum `I ⊆ supp e`, and

* **product geometry** on the piece (`y ∈ dom_i ↔ foot y ∈ T'` with `T'` closed, and a
  fibre-constant cover weight `ρ_i∘Φ_i = ρ_T∘foot`, `ρ_T` measurable and bounded),
* a unit **independent of the normal coordinates** on the domain (`u y = u (foot y)`),
* `v`, `p∘φ_i`, `F∘φ_i` continuous on `W`, and a point of `W` vanishing on `I` (for parity),

the piece integral `Z_{N;i,I}` admits a finite scalar-unit atlas all of whose cells sit at the pair
`(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`
(`exists_pieceAtlas_of_chart`).
The construction: the compact-base fibre-constant density (CCXXXVII) restricted further to the
fibres over `T'` (`chartPieceDensity`), on whose base × ball every point lies in the domain
(`mem_dom_of_mem_base`, and on the closed ball by closure), the scalar normal form of CCXXXVI for
the phase and the Jacobian (`pieceAmp`), continuous representatives of the `ContinuousOn` chart
data on the compact base × closed ball by the **Tietze extension theorem**
(`exists_continuous_extension_of_isClosed`), and the bridge CCXXXIII.

Non-claims: product geometry and normal-independence of the unit are hypotheses (constant chart
unit = basic case); the per-piece pair is not asserted to be the actual leading pair (coefficient
may vanish); the all-strata assembly of a whole chart is a corollary left to the global theorem
with per-piece base dimension.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic
open scoped ENNReal

namespace Grammar

/-- **Tietze extension** of a function continuous on a closed set. -/
theorem exists_continuous_extension_of_isClosed {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} (hs : IsClosed s) {f : X → ℝ} (hf : ContinuousOn f s) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ x ∈ s, g x = f x := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hs ⟨s.domRestrict f, hf.domRestrict⟩
  refine ⟨g, g.continuous, fun x hx => ?_⟩
  have h := ContinuousMap.congr_fun hg ⟨x, hx⟩
  rw [ContinuousMap.restrict_apply] at h
  exact h

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  (e : Fin d →₀ ℕ) (hD : D i = e.support) (hI : I ⊆ e.support)
  (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
  (T' : Set (Fin d → ℝ)) (hT' : IsClosed T') (ρT : (Fin d → ℝ) → ℝ)
  (hdom : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
  (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y))

theorem compactFibreConstantDensity_base (hI' : I ⊆ D i) (β : (Fin d → ℝ) → ℝ) (hfc) :
    (R.compactFibreConstantDensity i D hε I hI' hne K p β hfc).base =
      {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I} ∩
        tangentialCarrier (stratumSplit I hne) (R.chart i).dom := rfl

include hdom in
/-- Off the fibres over `T'` the static piece density vanishes (product geometry). -/
theorem piece_density_eq_zero_of_foot_notMem
    (q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ))
    (hq : q.1 ∉ {z | planeSplit (stratumSplit I hne) (z, 0) ∈ T'}) :
    (sizePiece (D i) ε I).indicator (R.boltzmannChartDensity i 0 K p)
      (planeSplit (stratumSplit I hne) q) = 0 := by
  by_cases hpiece : planeSplit (stratumSplit I hne) q ∈ sizePiece (D i) ε I
  · rw [indicator_of_mem hpiece]
    unfold boltzmannChartDensity
    apply Set.indicator_of_notMem (s := (R.chart i).dom)
    intro hdom'
    apply hq
    have := (hdom _ hpiece).1 hdom'
    obtain ⟨z, n⟩ := q
    rwa [planeFoot_planeSplit] at this
  · exact Set.indicator_of_notMem (f := R.boltzmannChartDensity i 0 K p) hpiece

include hε hD hI hT' hdom hρ in
/-- **The adapted density of the chart piece**: fibre-constant, compact base, restricted to the
fibres over `T'`. -/
noncomputable def chartPieceDensity :
    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I) :=
  (R.compactFibreConstantDensity i D hε I (hD ▸ hI) hne K p (T'.indicator ρT)
    (R.fibreConstant_of_product i D I hne T' ρT hdom hρ)).restrictBase
    {z | planeSplit (stratumSplit I hne) (z, 0) ∈ T'}
    (hT'.measurableSet.preimage ((planeSplit (stratumSplit I hne)).continuous.comp
      (continuous_id.prodMk continuous_const)).measurable)
    (fun q hq => R.piece_density_eq_zero_of_foot_notMem i D I hne K p T' hdom q hq)

include hε hD hI hT' hdom hρ in
theorem chartPieceDensity_base :
    (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base =
      ({z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I} ∩
        tangentialCarrier (stratumSplit I hne) (R.chart i).dom) ∩
        {z | planeSplit (stratumSplit I hne) (z, 0) ∈ T'} := rfl

include hε hD hI hT' hdom hρ in
theorem chartPieceDensity_beta :
    (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).beta =
      fun z => T'.indicator ρT (planeSplit (stratumSplit I hne) (z, 0)) := rfl

include hε hD hI hT' hdom hρ in
theorem chartPieceDensity_amp :
    (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).amp = fun z n =>
      (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
        p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) := rfl

include hε hD hI hT' hdom hρ in
theorem chartPieceDensity_normalBox :
    (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).normalBox =
      Metric.ball 0 ε := rfl

include hε hD hI hT' hdom hρ in
theorem chartPieceDensity_base_compact :
    IsCompact (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base := by
  rw [chartPieceDensity_base]
  refine IsCompact.inter_right ?_ (hT'.preimage ((planeSplit (stratumSplit I hne)).continuous.comp
    (continuous_id.prodMk continuous_const)))
  exact R.compactFibreConstantDensity_base_compact i D hε I (hD ▸ hI) hne K p (T'.indicator ρT)
    (R.fibreConstant_of_product i D I hne T' ρT hdom hρ)

include hε hD hI hT' hdom hρ in
/-- Points over the base and the open ball lie in the piece. -/
theorem mem_piece_of_mem_base {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
    {n : Fin (I.card - 1 + 1) → ℝ} (hn : n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    planeSplit (stratumSplit I hne) (z, n) ∈ sizePiece (D i) ε I := by
  rw [chartPieceDensity_base] at hz
  have hfoot : planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I := hz.1.1
  have htube : planeSplit (stratumSplit I hne) (z, n) ∈
      (coordPlaneTube (stratumSplit I hne) ε hε).U := by
    change ‖planeSplit (stratumSplit I hne) (z, n) -
      planeFoot (stratumSplit I hne) (planeSplit (stratumSplit I hne) (z, n))‖ < ε
    rw [norm_planeSplit_sub_foot]
    exact mem_ball_zero_iff.1 hn
  refine (mem_sizePiece_iff_of_mem_tube (D i) hε I hne htube).2 ?_
  rwa [planeFoot_planeSplit]

include hε hD hI hT' hdom hρ in
/-- Points over the base and the open ball lie in the chart domain (product geometry). -/
theorem mem_dom_of_mem_base {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
    {n : Fin (I.card - 1 + 1) → ℝ} (hn : n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := by
  have hpiece := R.mem_piece_of_mem_base i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn
  rw [chartPieceDensity_base] at hz
  refine (hdom _ hpiece).2 ?_
  rw [planeFoot_planeSplit]
  exact hz.2

include hε hD hI hT' hdom hρ in
/-- Points over the base and the CLOSED ball lie in the compact chart domain (closure). -/
theorem mem_dom_of_mem_base_closedBall {z : Fin (d - (I.card - 1 + 1)) → ℝ}
    (hz : z ∈ (R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ).base)
    {n : Fin (I.card - 1 + 1) → ℝ} (hn : n ∈ Metric.closedBall (0 : Fin (I.card - 1 + 1) → ℝ) ε) :
    planeSplit (stratumSplit I hne) (z, n) ∈ (R.chart i).dom := by
  have hcl : n ∈ closure (Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε) := by
    rwa [closure_ball 0 hε.ne']
  have himg : (fun n => planeSplit (stratumSplit I hne) (z, n)) ''
      Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε ⊆ (R.chart i).dom := by
    rintro _ ⟨n', hn', rfl⟩
    exact R.mem_dom_of_mem_base i D hε I hne e hD hI K p T' hT' ρT hdom hρ hz hn'
  have hcont : Continuous fun n : Fin (I.card - 1 + 1) → ℝ =>
      planeSplit (stratumSplit I hne) (z, n) :=
    (planeSplit (stratumSplit I hne)).continuous.comp (continuous_const.prodMk continuous_id)
  have hmem := mem_closure_image hcont.continuousAt hcl
  exact ((closure_mono himg).trans_eq (R.chart i).dom_compact.isClosed.closure_eq) hmem

end ResolutionCover

/-! ### The atlas from chart data -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hne : I.Nonempty)
  (e h : Fin d →₀ ℕ) (hD : D i = e.support) (hI : I ⊆ e.support)
  {K : (Fin d → ℝ) → ℝ} (hK0 : ∀ x, 0 ≤ K x) {W : Set (Fin d → ℝ)} (hW : IsOpen W)
  (hsub : (R.chart i).dom ⊆ W) (u v : (Fin d → ℝ) → ℝ) (hu : ContinuousOn u W)
  (hu0 : ∀ y ∈ W, u y ≠ 0) (hKu : ∀ y ∈ W, K ((R.chart i).φ y) = u y * monomialEval y e)
  (hv : ContinuousOn v W)
  (hdet : ∀ y ∈ W, (fderiv ℝ (R.chart i).φ y).det = v y * monomialEval y h)
  (hind : ∀ y ∈ (R.chart i).dom, u y = u (planeFoot (stratumSplit I hne) y))
  (T' : Set (Fin d → ℝ)) (hT' : IsClosed T') (ρT : (Fin d → ℝ) → ℝ) (hρm : Measurable ρT)
  {Cρ : ℝ} (hρb : ∀ x, |ρT x| ≤ Cρ)
  (hdom : ∀ y ∈ sizePiece (D i) ε I,
    y ∈ (R.chart i).dom ↔ planeFoot (stratumSplit I hne) y ∈ T')
  (hρ : ∀ y ∈ sizePiece (D i) ε I, y ∈ (R.chart i).dom →
    R.weight i ((R.chart i).Φ y) = ρT (planeFoot (stratumSplit I hne) y))
  {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d}
  (hFc : ContinuousOn (fun y => F ((R.chart i).φ y)) W)
  (hpc : ContinuousOn (fun y => p.w ((R.chart i).φ y)) W)
  (hFm : Measurable F)
  (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
  (hK : Measurable K) (hy₀ : ∃ y₀ ∈ W, ∀ j ∈ I, y₀ j = 0)

/-- The scalar amplitude of the piece: `|v(Ψ)| · |tangential Jacobian monomial| · p(φΨ) · F(φΨ)`. -/
noncomputable def pieceAmp (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ) :
    ℝ :=
  |v (planeSplit (stratumSplit I hne) (z, n))| * |tangentialMonomial I hne h z| *
    p.w ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) *
      F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))

include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hind hT' hρm hρb hdom hρ hFc hpc hFm hF hK hy₀ in
/-- **The scalar-unit atlas of a chart–stratum piece from monomial-chart data, with its cells
exposed**: the atlas is the orthant atlas of the cell built on the compact-base piece density
`chartPieceDensity`, with a continuous phase unit `q'` equal to the scalar phase on the base and a
continuous amplitude `A'` equal to `pieceAmp` on base × closed ball; all cells at the pair
`(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`. -/
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
  -- the adapted density with compact base
  set Ad := R.chartPieceDensity i D hε I hne e hD hI K p T' hT' ρT hdom hρ with hAd
  have hbase : IsCompact Ad.base :=
    R.chartPieceDensity_base_compact i D hε I hne e hD hI K p T' hT' ρT hdom hρ
  have hbaseM : MeasurableSet Ad.base := hbase.isClosed.measurableSet
  have hbox : Ad.normalBox = Metric.ball 0 ε := rfl
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
  -- the scalar phase on the base
  set S : Set ((Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)) :=
    {q | q.1 ∈ Ad.base ∧ q.2 ∈ Metric.ball 0 ε} with hS
  have hSdom : ∀ q ∈ S, planeSplit (stratumSplit I hne) q ∈ (R.chart i).dom :=
    fun q hq => hmemdom q.1 hq.1 q.2 hq.2
  have hKS : ∀ q ∈ S, K ((R.chart i).φ (planeSplit (stratumSplit I hne) q)) =
      u (planeSplit (stratumSplit I hne) q) * monomialEval (planeSplit (stratumSplit I hne) q) e :=
    fun q hq => hKu _ (hsub (hSdom q hq))
  have hindS : ∀ q ∈ S, u (planeSplit (stratumSplit I hne) q) = tangentialUnit I hne u q.1 :=
    fun q hq => by
      obtain ⟨z, n⟩ := q
      have := hind _ (hSdom (z, n) hq)
      rwa [planeFoot_planeSplit] at this
  have hphase0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        scalarPhase I hne u e z * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [(R.chart i).Φ_eqOn (hmemdom z hz n hn)]
    exact phase_scalarNormalForm I hne u e (K := fun y => K ((R.chart i).φ y)) hKS hindS hpar
      (show (z, n) ∈ S from ⟨hz, hn⟩)
  have hfootOf : ∀ z ∈ Ad.base,
      planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I := fun z hz => by
    rw [hAd, chartPieceDensity_base] at hz
    exact hz.1.1
  have hqpos : ∀ z ∈ Ad.base, 0 < scalarPhase I hne u e z := fun z hz => by
    have hnstar : (fun _ : Fin (I.card - 1 + 1) => ε / 2) ∈
        Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro a
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    refine scalarPhase_pos I hne u e (K := fun y => K ((R.chart i).φ y)) hKS hindS hpar
      (fun q _ => hK0 _) (fun q hq => hu0 _ (hsub (hSdom q hq)))
      (show (z, fun _ => ε / 2) ∈ S from ⟨hz, hnstar⟩) (fun _ => (half_pos hε).ne') ?_
    intro j hj hjI h0
    have := hfootOf z hz j (by rw [hD]; exact hj) hjI
    apply this
    rw [h0, abs_zero]
    exact hε
  have hqcont : ContinuousOn (scalarPhase I hne u e) Ad.base :=
    continuousOn_scalarPhase I hne u e hu fun z hz =>
      hsub (hmemdom z hz 0 (Metric.mem_ball_self hε))
  obtain ⟨q', hq'c, hq'eq⟩ := exists_continuous_extension_of_isClosed hbase.isClosed hqcont
  -- the amplitude identity on the base and the open ball
  have hamp0 : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
        R.pieceAmp i I hne h v (F := F) (p := p) z n * ∏ a, |n a| ^ normalExp I hne h a :=
    fun z hz n hn => by
      have hdomzn := hmemdom z hz n hn
      have hampeq : Ad.amp z n = (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
          p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) := rfl
      rw [hampeq, (R.chart i).Φ_eqOn hdomzn]
      unfold ResolutionChart.jac pieceAmp
      rw [hdet _ (hsub hdomzn), abs_mul, abs_monomialEval_planeSplit]
      ring
  -- continuous representatives on the compact base × closed ball
  have hΨ : Continuous fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q := (planeSplit (stratumSplit I hne)).continuous
  have hmaps : MapsTo (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ) =>
      planeSplit (stratumSplit I hne) q) (Ad.base ×ˢ Metric.closedBall 0 ε) W :=
    fun q hq => hsub (hmemdomc q.1 hq.1 q.2 hq.2)
  have hAcont : ContinuousOn (Function.uncurry (R.pieceAmp i I hne h v (F := F) (p := p)))
      (Ad.base ×ˢ Metric.closedBall 0 ε) := by
    have h1 := (hv.comp hΨ.continuousOn hmaps).abs
    have h2 : ContinuousOn (fun q : (Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ)
        => |tangentialMonomial I hne h q.1|) (Ad.base ×ˢ Metric.closedBall 0 ε) :=
      ((continuous_tangentialMonomial I hne h).comp continuous_fst).continuousOn.abs
    have h3 := hpc.comp hΨ.continuousOn hmaps
    have h4 := hFc.comp hΨ.continuousOn hmaps
    exact ((h1.mul h2).mul h3).mul h4
  obtain ⟨A'', hA''c, hA''eq⟩ := exists_continuous_extension_of_isClosed
    (hbase.isClosed.prod Metric.isClosed_closedBall) hAcont
  have hA'c : Continuous (Function.uncurry (Function.curry A'')) := by
    rwa [Function.uncurry_curry]
  have hamp' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      Ad.amp z n * F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n))) =
        Function.curry A'' z n * ∏ a, |n a| ^ normalExp I hne h a := fun z hz n hn => by
    rw [hamp0 z hz n hn]
    congr 1
    exact (hA''eq (z, n) ⟨hz, Metric.ball_subset_closedBall hn⟩).symm
  have hphase' : ∀ z ∈ Ad.base, ∀ n ∈ Metric.ball (0 : Fin (I.card - 1 + 1) → ℝ) ε,
      K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n))) =
        q' z * ∏ a, n a ^ (2 * normalHalfExp I hne e a) := fun z hz n hn => by
    rw [hphase0 z hz n hn, hq'eq z hz]
  have hq'pos : ∀ z ∈ Ad.base, 0 < q' z := fun z hz => by
    rw [hq'eq z hz]
    exact hqpos z hz
  exact ⟨R.pieceAtlas i D hε I hne Ad hbase hβ hbox (normalExp I hne h) (normalHalfExp I hne e) hk
    q' hq'c hq'pos (Function.curry A'') hA'c hamp' hphase' hFm hF hK hK0, fun _ => rfl,
    fun _ => rfl, q', Function.curry A'', hq'c, hq'pos, hA'c, hk, hbase, hβ, hamp', hphase', hq'eq,
    fun z hz n hn => hA''eq (z, n) ⟨hz, hn⟩, rfl⟩

include hε hD hI hK0 hW hsub hu hu0 hKu hv hdet hind hT' hρm hρb hdom hρ hFc hpc hFm hF hK hy₀ in
/-- **The scalar-unit atlas of a chart–stratum piece from monomial-chart data**: all cells at the
pair `(min_a (h_{ν(a)}+1)/(2k_a), #minimisers − 1)` with `2k_a = e_{ν(a)}`. -/
theorem exists_pieceAtlas_of_chart :
    ∃ At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p),
      (∀ σ, (At.cell σ).lam = minRatio (normalExp I hne h) (normalHalfExp I hne e)) ∧
      ∀ σ, (At.cell σ).mult = multCount (ratioExp (normalExp I hne h) (normalHalfExp I hne e))
        (minRatio (normalExp I hne h) (normalHalfExp I hne e)) := by
  obtain ⟨At, h1, h2, -⟩ := R.exists_pieceAtlas_of_chart_data i D hε I hne e h hD hI hK0 hW hsub u v
    hu hu0 hKu hv hdet hind T' hT' ρT hρm hρb hdom hρ hFc hpc hFm hF hK hy₀
  exact ⟨At, h1, h2⟩

end ResolutionCover

end Grammar
