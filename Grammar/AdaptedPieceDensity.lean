/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.IntegratedLeadingTerm

/-!
# Adapted product densities on chart–stratum pieces

Module 1 of the adapted-density programme (`tide-log/gpt6_bigpicture_v75.md`). An **adapted product
density** for a static density `w` on a piece, relative to the coordinate splitting `planeSplit τ`
of a stratum, is an a.e. factorisation
`1_piece · w ∘ planeSplit τ = 1_base(z) β(z) · 1_normalBox(n) a(z, n)`
into a tangential weight `β` on a measurable base and a normal amplitude `a` (their regularity
is imposed by the downstream integration theorems)
(`AdaptedProductDensity`). Against it any weighted piece integral is the iterated integral
`∫_base β(z) ∫_normalBox a(z,n) G(planeSplit(z,n)) dn dz`
(`AdaptedProductDensity.integral_piece_eq`),
and for the chart–stratum piece integrals of CCXXV this gives
`Z_{N;i,I} = ∫_base β(z) ∫_normalBox a(z,n) e^{-N K(φ_i(z,n))} F(φ_i(z,n)) dn dz`
(`pieceIntegral_eq_adapted`) — the form to which the fibrewise Mellin kernel asymptotics and the
integration step of CCXXVII apply.

The first geometric specialisation is the **fibre-constant case**
(`adaptedProductDensity_of_fibreConstant`): if, a.e. on the piece, the geometric allocation factor
`1_{dom_i} · (ρ_i ∘ Φ_i)` is a function of the foot on the stratum (the paper's adapted partition of
unity is constant on normal fibres, Lemma adapted_pou (iv)), then the piece's static density is an
adapted product density with base the foot condition of the piece, normal box the `ε`-ball, and
amplitude the Jacobian times the pulled-back prior — the fibre saturation of the pieces (CCXXIII)
does the rest.

Non-claims: the fibre-constancy is a HYPOTHESIS — neither hironaka's `PartialResolution` nor the
normalised indicator cover weights supply it (Astra #75: unrestricted per-piece certificates are
false); no asymptotics are produced here.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Adapted product densities -/

section Adapted

variable {d m r : ℕ} (τ : Fin d ≃ Fin m ⊕ Fin r)

/-- **An adapted product density** for the static density `w` on `piece`, relative to the
coordinate splitting `planeSplit τ`: a.e. on the product,
`1_piece · w ∘ planeSplit τ = 1_base(z) β(z) · 1_normalBox(n) a(z, n)`. -/
structure AdaptedProductDensity (w : (Fin d → ℝ) → ℝ) (piece : Set (Fin d → ℝ)) where
  /-- The tangential base. -/
  base : Set (Fin (d - r) → ℝ)
  measurableSet_base : MeasurableSet base
  /-- The normal box. -/
  normalBox : Set (Fin r → ℝ)
  measurableSet_normalBox : MeasurableSet normalBox
  /-- The tangential weight (its regularity is imposed by the downstream integration theorems). -/
  beta : (Fin (d - r) → ℝ) → ℝ
  /-- The normal amplitude. -/
  amp : (Fin (d - r) → ℝ) → (Fin r → ℝ) → ℝ
  density_ae : (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) => piece.indicator w (planeSplit τ q))
    =ᵐ[volume] fun q => base.indicator beta q.1 * normalBox.indicator (amp q.1) q.2

theorem measurableEmbedding_planeSplit : MeasurableEmbedding (planeSplit τ) :=
  (planeSplit τ).toHomeomorph.measurableEmbedding

/-- **Weighted piece integrals against an adapted product density** are iterated integrals over the
base and the normal box. -/
theorem AdaptedProductDensity.integral_piece_eq {w : (Fin d → ℝ) → ℝ} {piece : Set (Fin d → ℝ)}
    (A : AdaptedProductDensity τ w piece) (hpiece : MeasurableSet piece) (G : (Fin d → ℝ) → ℝ)
    (hint : Integrable fun y => piece.indicator w y * G y) :
    ∫ y in piece, w y * G y =
      ∫ z in A.base, A.beta z * ∫ n in A.normalBox, A.amp z n * G (planeSplit τ (z, n)) := by
  have hmp := measurePreserving_planeSplit τ
  have hemb := measurableEmbedding_planeSplit τ
  have hae : (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      piece.indicator w (planeSplit τ q) * G (planeSplit τ q)) =ᵐ[volume] fun q =>
        A.base.indicator A.beta q.1 * A.normalBox.indicator (A.amp q.1) q.2 * G (planeSplit τ q) :=
    A.density_ae.mul (EventuallyEq.refl _ fun q => G (planeSplit τ q))
  have hint' : Integrable (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      A.base.indicator A.beta q.1 * A.normalBox.indicator (A.amp q.1) q.2 * G (planeSplit τ q))
      volume :=
    ((hmp.integrable_comp_emb hemb).2 hint).congr hae
  calc ∫ y in piece, w y * G y = ∫ y, piece.indicator w y * G y := by
        rw [← integral_indicator hpiece]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        beta_reduce
        exact indicator_mul_left _ _ _
    _ = ∫ q, piece.indicator w (planeSplit τ q) * G (planeSplit τ q) :=
        (hmp.integral_comp hemb _).symm
    _ = ∫ q, A.base.indicator A.beta q.1 * A.normalBox.indicator (A.amp q.1) q.2 *
          G (planeSplit τ q) := integral_congr_ae hae
    _ = ∫ z, ∫ n, A.base.indicator A.beta z * A.normalBox.indicator (A.amp z) n *
          G (planeSplit τ (z, n)) := by
        rw [Measure.volume_eq_prod] at hint' ⊢
        exact integral_prod _ hint'
    _ = ∫ z in A.base, A.beta z * ∫ n in A.normalBox, A.amp z n * G (planeSplit τ (z, n)) := by
        rw [← integral_indicator A.measurableSet_base]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        beta_reduce
        by_cases hz : z ∈ A.base
        · rw [indicator_of_mem hz, indicator_of_mem hz,
            ← integral_indicator A.measurableSet_normalBox, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun n => ?_)
          beta_reduce
          rw [indicator_mul_left, mul_assoc]
        · simp only [indicator_of_notMem hz, zero_mul, integral_zero]

end Adapted

/-! ### The chart–stratum piece integrals in adapted form -/

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (I : Finset (Fin d)) (hne : I.Nonempty)
  {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- The static density (the Boltzmann chart density at `N = 0`) times the Boltzmann factor is the
chart density at `N`, as an integrable function on the piece. -/
theorem integrable_indicator_static_mul (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun y => (sizePiece (D i) ε I).indicator (R.boltzmannChartDensity i 0 K p) y *
      (Real.exp (-N * K ((R.chart i).Φ y)) * F ((R.chart i).φ y)) := by
  have h := (R.integrable_chartWeight_mul i (TubeWeight.boltzmann N hN K hK hK0 p) hFm
    ((R.integrable_boltzmann hF hK hK0 hN).congr (Eventually.of_forall fun x => by
      simp only [TubeWeight.boltzmann_w]
      ring))).indicator (measurableSet_sizePiece (D i) ε I)
  refine h.congr (Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : y ∈ sizePiece (D i) ε I
  · rw [indicator_of_mem hy, indicator_of_mem hy, R.chartWeight_boltzmann_w,
      R.boltzmannChartDensity_eq_exp_mul]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

/-- **The chart–stratum piece integral in adapted form**: against an adapted product density for the
piece's static density,
`Z_{N;i,I} = ∫_base β(z) ∫_normalBox a(z,n) e^{-N K(φ_i(z,n))} F(φ_i(z,n))`. -/
theorem pieceIntegral_eq_adapted
    (A : AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I))
    (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ} (hN : 0 ≤ N) :
    R.pieceIntegral D ε i I F K p N =
      ∫ z in A.base, A.beta z * ∫ n in A.normalBox, A.amp z n *
        (Real.exp (-N * K ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))) *
          F ((R.chart i).φ (planeSplit (stratumSplit I hne) (z, n)))) := by
  rw [← A.integral_piece_eq _ (measurableSet_sizePiece (D i) ε I)
    (fun y => Real.exp (-N * K ((R.chart i).Φ y)) * F ((R.chart i).φ y))
    (R.integrable_indicator_static_mul i D I hFm hF hK hK0 hN)]
  unfold pieceIntegral
  refine setIntegral_congr_fun (measurableSet_sizePiece (D i) ε I) fun y _ => ?_
  rw [R.boltzmannChartDensity_eq_exp_mul]
  ring

end ResolutionCover

/-! ### The fibre-constant case -/

section FibreConstant

variable {d : ℕ} (D : Finset (Fin d)) {ε : ℝ} (I : Finset (Fin d))

theorem measurableSet_footCondition : MeasurableSet (footCondition D (ε := ε) I) := by
  have h : footCondition D (ε := ε) I =
      ⋂ j ∈ D, {v : Fin d → ℝ | j ∉ I → ¬ |v j| < ε} := by
    ext v
    simp only [footCondition, mem_ofPred_eq, mem_iInter]
  rw [h]
  refine Finset.measurableSet_biInter D fun j _ => ?_
  by_cases hj : j ∈ I
  · simp only [hj, not_true_eq_false, false_implies, ofPred_true, MeasurableSet.univ]
  · simp only [hj, not_false_eq_true, true_implies]
    exact (measurableSet_lt (measurable_abs.comp (measurable_pi_apply j)) measurable_const).compl

variable {m r : ℕ} (τ : Fin d ≃ Fin m ⊕ Fin r)

theorem planeFoot_planeSplit (z : Fin (d - r) → ℝ) (n : Fin r → ℝ) :
    planeFoot τ (planeSplit τ (z, n)) = planeSplit τ (z, 0) := by
  rw [planeFoot_apply, planeSplit_apply, planeSplit_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem norm_planeSplit_sub_foot (z : Fin (d - r) → ℝ) (n : Fin r → ℝ) :
    ‖planeSplit τ (z, n) - planeFoot τ (planeSplit τ (z, n))‖ = ‖n‖ := by
  rw [planeFoot_planeSplit, ← map_sub, planeSplit_apply, norm_coordCLE]
  simp only [Prod.mk_sub_mk, sub_self, sub_zero, map_zero, Prod.norm_def, norm_zero]
  exact max_eq_right (norm_nonneg _)

end FibreConstant

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) (i : ι)
  (D : ι → Finset (Fin d)) {ε : ℝ} (hε : 0 < ε) (I : Finset (Fin d)) (hI : I ⊆ D i)
  (hne : I.Nonempty) (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)

/-- The geometric allocation factor of chart `i`: `1_{dom_i} · (ρ_i ∘ Φ_i)`. -/
noncomputable def allocation (y : Fin d → ℝ) : ℝ :=
  (R.chart i).dom.indicator (fun y => R.weight i ((R.chart i).Φ y)) y

theorem boltzmannChartDensity_zero_eq (y : Fin d → ℝ) :
    R.boltzmannChartDensity i 0 K p y =
      R.allocation i y * ((R.chart i).jac y * p.w ((R.chart i).Φ y)) := by
  unfold boltzmannChartDensity allocation
  by_cases hy : y ∈ (R.chart i).dom
  · rw [indicator_of_mem hy, indicator_of_mem hy, neg_zero, zero_mul, Real.exp_zero, one_mul]
    ring
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

include hε hI in
/-- **The fibre-constant case**: if a.e. on the piece the allocation factor `1_{dom_i} (ρ_i ∘ Φ_i)`
is a function `β` of the foot on the stratum, the piece's static density is an adapted product
density with base the foot condition, normal box the `ε`-ball and amplitude `|det Dφ_i| · (p ∘
Φ_i)`. -/
noncomputable def adaptedProductDensity_of_fibreConstant (β : (Fin d → ℝ) → ℝ)
    (hfc : (fun y => (sizePiece (D i) ε I).indicator (R.allocation i) y) =ᵐ[volume]
      fun y => (sizePiece (D i) ε I).indicator (fun y => β (planeFoot (stratumSplit I hne) y)) y) :
    AdaptedProductDensity (stratumSplit I hne) (R.boltzmannChartDensity i 0 K p)
      (sizePiece (D i) ε I) where
  base := {z | planeSplit (stratumSplit I hne) (z, 0) ∈ footCondition (D i) (ε := ε) I}
  measurableSet_base := (measurableSet_footCondition (D i) I).preimage
    ((planeSplit (stratumSplit I hne)).continuous.comp
      (continuous_id.prodMk continuous_const)).measurable
  normalBox := Metric.ball 0 ε
  measurableSet_normalBox := measurableSet_ball
  beta z := β (planeSplit (stratumSplit I hne) (z, 0))
  amp z n := (R.chart i).jac (planeSplit (stratumSplit I hne) (z, n)) *
    p.w ((R.chart i).Φ (planeSplit (stratumSplit I hne) (z, n)))
  density_ae := by
    set τ := stratumSplit I hne with hτ
    have hmp := measurePreserving_planeSplit τ
    have hfc' := hmp.quasiMeasurePreserving.ae_eq_comp hfc
    refine hfc'.mono fun q hq => ?_
    obtain ⟨z, n⟩ := q
    simp only [Function.comp_apply] at hq
    dsimp only
    have htube : planeSplit τ (z, n) ∈ (coordPlaneTube τ ε hε).U ↔
        n ∈ Metric.ball (0 : Fin _ → ℝ) ε := by
      change ‖planeSplit τ (z, n) - planeFoot τ (planeSplit τ (z, n))‖ < ε ↔ _
      rw [norm_planeSplit_sub_foot, Metric.mem_ball, dist_zero_right]
    by_cases hy : planeSplit τ (z, n) ∈ sizePiece (D i) ε I
    · have hn : n ∈ Metric.ball (0 : Fin _ → ℝ) ε :=
        htube.1 (sizePiece_subset_tube (D i) hε I hI hne hy)
      have hz : planeSplit τ (z, 0) ∈ footCondition (D i) (ε := ε) I := by
        have := (mem_sizePiece_iff_of_mem_tube (D i) hε I hne (htube.2 hn)).1 hy
        rwa [planeFoot_planeSplit] at this
      have hz' : z ∈ {z | planeSplit τ (z, 0) ∈ footCondition (D i) (ε := ε) I} := hz
      rw [indicator_of_mem hy, indicator_of_mem hy, planeFoot_planeSplit] at hq
      rw [indicator_of_mem hy, indicator_of_mem hz', indicator_of_mem hn,
        R.boltzmannChartDensity_zero_eq, hq]
    · rw [indicator_of_notMem hy]
      by_cases hn : n ∈ Metric.ball (0 : Fin _ → ℝ) ε
      · have hz : planeSplit τ (z, 0) ∉ footCondition (D i) (ε := ε) I := by
          intro hz
          refine hy ((mem_sizePiece_iff_of_mem_tube (D i) hε I hne (htube.2 hn)).2 ?_)
          rwa [planeFoot_planeSplit]
        have hz' : z ∉ {z | planeSplit τ (z, 0) ∈ footCondition (D i) (ε := ε) I} := hz
        rw [indicator_of_notMem hz', zero_mul]
      · rw [indicator_of_notMem hn, mul_zero]

end ResolutionCover

end Grammar
