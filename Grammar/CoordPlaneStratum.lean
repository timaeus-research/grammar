/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularGlobalExpansion

/-!
# Coordinate planes as analytic LCI strata (resolved-space programme, module 2)

In a hironaka chart the exceptional-divisor strata are coordinate planes. For an index splitting
`τ : Fin d ≃ Fin m ⊕ Fin r` (the `r` normal coordinates `τ⁻¹(inr j)`), this file provides:

* the plane `coordPlane τ = {y : y(τ⁻¹(inr j)) = 0 ∀ j}`, its normal-coordinate projection
  `planeProj` (a continuous linear map) and Jacobian rows `planeJ` (`planeJ_mulVec`,
  `planeJ_transpose_mulVec`, `fullRowRank_planeJ`);
* the single-chart atlas `coordPlaneAtlas τ : CompatibleAnalyticLCIAtlas r (coordPlane τ)` with
  normal field `range planeJᵀ = coordCLE τ (0, ·)` (`mem_coordPlaneAtlas_normal`);
* **the analytic tube of every radius** `coordPlaneTube τ ε` (foot `planeFoot` = zeroing the normal
  coordinates; built directly, `U = {‖y − foot y‖ < ε}`);
* **the global graph chart** `coordPlaneChart τ hs` (one piece: `W = ⊤`, `V' = univ`, `emb` the
  coordinate insertion, `ft` the tangential read-out);
* the tube chart is the linear coordinate splitting (`tubeChart_coordPlaneChart`), the certified
  domain is `{‖n‖ < ε}` (`tubeChartDom_coordPlaneChart`) and **the Jacobian density is `1`**
  (`tubeJac_coordPlaneChart`, from `abs_det_eq_one_of_measurePreserving`);
* **the per-stratum formula on the ε-tube of a coordinate plane** with a tube weight
  (`integral_coordPlaneTube_eq_integral_condContraction`): `∫_{‖y − foot y‖<ε} w F dy =
  ∫ w · (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(foot y) dy`.

Non-claims: the plane is the whole coordinate plane of `ℝ^d` (the stratum of a chart is an open
subset of it, cut down by the measurable pieces of module 4); the weight carries the chart's
Jacobian unit, prior and cutoffs.
-/

open scoped Manifold ContDiff Matrix ENNReal
open Set Function StrucDual.Geometry TopologicalSpace MeasureTheory

namespace Grammar

section Det

/-- **A measure-preserving linear automorphism has `|det| = 1`.** -/
theorem abs_det_eq_one_of_measurePreserving {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : E ≃L[ℝ] E) (h : MeasurePreserving L μ μ) :
    |LinearMap.det (L : E →ₗ[ℝ] E)| = 1 := by
  have hball := Measure.addHaar_image_continuousLinearEquiv μ L (Metric.ball (0 : E) 1)
  have himg : ⇑L '' Metric.ball (0 : E) 1 = ⇑L.symm ⁻¹' Metric.ball (0 : E) 1 := by
    have := ContinuousLinearEquiv.image_symm_eq_preimage L.symm (Metric.ball (0 : E) 1)
    rwa [ContinuousLinearEquiv.symm_symm] at this
  have hpre : μ (⇑L.symm ⁻¹' Metric.ball (0 : E) 1) = μ (Metric.ball (0 : E) 1) :=
    (h.symm L.toHomeomorph.toMeasurableEquiv).measure_preimage
      measurableSet_ball.nullMeasurableSet
  rw [himg, hpre] at hball
  have hpos : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ 0 one_pos).ne'
  have hfin : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  exact ENNReal.ofReal_eq_one.1 ((ENNReal.mul_eq_right hpos hfin).1 hball.symm)

end Det

section Plane

variable {d m r : ℕ} (τ : Fin d ≃ Fin m ⊕ Fin r)

/-- **The coordinate plane** along `τ`: the normal coordinates `τ⁻¹(inr j)` vanish. -/
def coordPlane : Set (Fin d → ℝ) := {y | ∀ j : Fin r, y (τ.symm (Sum.inr j)) = 0}

/-- The normal-coordinate projection. -/
noncomputable def planeProj : (Fin d → ℝ) →L[ℝ] (Fin r → ℝ) :=
  (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin r → ℝ)).comp
    ((coordCLE τ).symm : (Fin d → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin r → ℝ))

theorem planeProj_apply (y : Fin d → ℝ) (j : Fin r) :
    planeProj τ y j = y (τ.symm (Sum.inr j)) :=
  coordCLE_symm_apply_snd τ y j

theorem mem_coordPlane_iff (y : Fin d → ℝ) : y ∈ coordPlane τ ↔ planeProj τ y = 0 := by
  simp only [coordPlane, Set.mem_ofPred_eq, funext_iff, planeProj_apply, Pi.zero_apply]

/-- The Jacobian rows: the normal coordinate functionals. -/
def planeJ : Matrix (Fin r) (Fin d) ℝ :=
  Matrix.of fun j k => if k = τ.symm (Sum.inr j) then 1 else 0

theorem planeJ_mulVec (y : Fin d → ℝ) : (planeJ τ).mulVec y = planeProj τ y := by
  funext j
  simp only [Matrix.mulVec, dotProduct, planeJ, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, planeProj_apply]

theorem planeJ_transpose_mulVec (c : Fin r → ℝ) :
    (planeJ τ)ᵀ.mulVec c = coordCLE τ (0, c) := by
  funext k
  rw [coordCLE_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, planeJ, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  have hk : ∀ j : Fin r, (k = τ.symm (Sum.inr j)) ↔ (τ k = Sum.inr j) := fun j =>
    Equiv.eq_symm_apply τ
  simp only [hk]
  rcases hτ : τ k with i | j
  · simp
  · simp

theorem fullRowRank_planeJ : FullRowRank (planeJ τ) := by
  intro c₁ c₂ h
  rw [planeJ_transpose_mulVec, planeJ_transpose_mulVec] at h
  exact (Prod.mk.inj ((coordCLE τ).injective h)).2

/-- **The coordinate plane as an analytic LCI stratum** (one chart, `G = planeProj`,
`J = planeJ`). -/
noncomputable def coordPlaneAtlas : CompatibleAnalyticLCIAtlas r (coordPlane τ) where
  ι := Unit
  V _ := univ
  isOpen_V _ := isOpen_univ
  G _ := planeProj τ
  J _ _ := planeJ τ
  analyticAt_G _ p := (planeProj τ).analyticAt p
  hJG _ p := by
    refine (planeProj τ).hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
    exact (planeJ_mulVec τ y).symm
  cover _ := ⟨(), mem_univ _⟩
  zero_iff := fun _ {y} _ => mem_coordPlane_iff τ y
  fullRank := fun _ {_} _ _ => fullRowRank_planeJ τ
  tangent _ := tangentSpaceOf (planeJ τ)
  tangent_eq := fun _ {_} _ _ => rfl

theorem coordPlaneAtlas_normal (x : Fin d → ℝ) :
    (coordPlaneAtlas τ).normal x = normalSpaceOf (planeJ τ) :=
  (normalSpaceOf_eq_orthogonalSubmodule_tangent (fullRowRank_planeJ τ)).symm

/-- The normal space is the image of the normal coordinates. -/
theorem mem_coordPlaneAtlas_normal (x n : Fin d → ℝ) :
    n ∈ (coordPlaneAtlas τ).normal x ↔ ∃ c : Fin r → ℝ, n = coordCLE τ (0, c) := by
  rw [coordPlaneAtlas_normal, mem_normalSpaceOf]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, planeJ_transpose_mulVec]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, planeJ_transpose_mulVec τ c⟩

/-- **The foot**: zero the normal coordinates. -/
noncomputable def planeFoot : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ((coordCLE τ : (Fin m → ℝ) × (Fin r → ℝ) →L[ℝ] (Fin d → ℝ)).comp
    (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin r → ℝ))).comp
      ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin r → ℝ)).comp
        ((coordCLE τ).symm : (Fin d → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin r → ℝ)))

theorem planeFoot_apply (y : Fin d → ℝ) :
    planeFoot τ y = coordCLE τ (((coordCLE τ).symm y).1, 0) := rfl

theorem planeFoot_mem (y : Fin d → ℝ) : planeFoot τ y ∈ coordPlane τ := by
  intro j
  rw [planeFoot_apply, coordCLE_apply_inr]
  rfl

theorem planeFoot_of_mem {y : Fin d → ℝ} (hy : y ∈ coordPlane τ) : planeFoot τ y = y := by
  rw [planeFoot_apply]
  have h2 : ((coordCLE τ).symm y).2 = 0 := by
    funext j
    rw [coordCLE_symm_apply_snd]
    exact hy j
  conv_rhs => rw [← (coordCLE τ).apply_symm_apply y]
  rw [← h2]

theorem planeFoot_normal (c : Fin r → ℝ) : planeFoot τ (coordCLE τ (0, c)) = 0 := by
  rw [planeFoot_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact map_zero _

theorem sub_planeFoot (y : Fin d → ℝ) :
    y - planeFoot τ y = coordCLE τ (0, ((coordCLE τ).symm y).2) := by
  rw [planeFoot_apply]
  conv_lhs => rw [← (coordCLE τ).apply_symm_apply y]
  rw [← map_sub]
  congr 1
  ext <;> simp

/-- **strucdual's analytic tube of every radius, for the coordinate plane**, built directly: the
foot zeroes the normal coordinates and the tube is `{‖y − foot y‖ < ε}`. -/
noncomputable def coordPlaneTube (ε : ℝ) (hε : 0 < ε) :
    AnalyticNormalTubularChart (coordPlaneAtlas τ).normal (coordPlane τ) where
  eps := ε
  eps_pos := hε
  U := {y | ‖y - planeFoot τ y‖ < ε}
  mem_U_iff := fun y => by
    constructor
    · intro hy
      refine ⟨planeFoot τ y, planeFoot_mem τ y, y - planeFoot τ y, ?_, hy, by abel⟩
      rw [sub_planeFoot]
      exact (mem_coordPlaneAtlas_normal τ _ _).2 ⟨_, rfl⟩
    · rintro ⟨s, hs, n, hn, hlt, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_coordPlaneAtlas_normal τ s n).1 hn
      change ‖s + coordCLE τ (0, c) - planeFoot τ (s + coordCLE τ (0, c))‖ < ε
      rw [map_add, planeFoot_of_mem τ hs, planeFoot_normal, add_zero, add_sub_cancel_left]
      exact hlt
  isOpen_U := isOpen_lt (continuous_id.sub (planeFoot τ).continuous).norm continuous_const
  proj := planeFoot τ
  proj_mem := fun _ => planeFoot_mem τ _
  ncoord_mem := fun {y} _ => by
    rw [sub_planeFoot]
    exact (mem_coordPlaneAtlas_normal τ _ _).2 ⟨_, rfl⟩
  ncoord_norm_lt := fun hy => hy
  unique := by
    intro s₁ s₂ n₁ n₂ hs₁ hs₂ hn₁ hn₂ _ _ heq
    obtain ⟨c₁, rfl⟩ := (mem_coordPlaneAtlas_normal τ _ _).1 hn₁
    obtain ⟨c₂, rfl⟩ := (mem_coordPlaneAtlas_normal τ _ _).1 hn₂
    have h := congrArg (planeFoot τ) heq
    rw [map_add, map_add, planeFoot_of_mem τ hs₁, planeFoot_of_mem τ hs₂, planeFoot_normal,
      planeFoot_normal, add_zero, add_zero] at h
    subst h
    exact ⟨rfl, add_left_cancel heq⟩
  contDiffAt_proj := fun _ => (planeFoot τ).contDiff.contDiffAt
  analyticAt_proj := fun _ => (planeFoot τ).analyticAt _

@[simp] theorem coordPlaneTube_proj (ε : ℝ) (hε : 0 < ε) :
    (coordPlaneTube τ ε hε).proj = planeFoot τ := rfl

@[simp] theorem coordPlaneTube_U (ε : ℝ) (hε : 0 < ε) :
    (coordPlaneTube τ ε hε).U = {y | ‖y - planeFoot τ y‖ < ε} := rfl

end Plane

section GraphChart

variable {d m r : ℕ} (τ : Fin d ≃ Fin m ⊕ Fin r)

include τ in
theorem coordPlane_card : m + r = d := by
  have h := Fintype.card_congr τ
  simp only [Fintype.card_fin, Fintype.card_sum] at h
  exact h.symm

/-- Reindexing of the model coordinates `ℝ^{d−r} ≃L ℝ^m`. -/
noncomputable def planeReindex (τ : Fin d ≃ Fin m ⊕ Fin r) :
    (Fin (d - r) → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (finCongr (by have := coordPlane_card τ; omega) :
    Fin m ≃ Fin (d - r))).toContinuousLinearEquiv

/-- **The global graph chart of the coordinate plane**: `emb z = coordCLE τ (z, 0)`,
`ft y = ` the tangential coordinates. -/
noncomputable def coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ) :
    ModelGraphChart (coordPlaneAtlas τ) s where
  i := ()
  W := ⊤
  V' := univ
  isOpen_V' := isOpen_univ
  V'_subset := subset_univ _
  s_mem := ⟨hs, mem_univ _⟩
  emb z := coordCLE τ (planeReindex τ z, 0)
  contDiffOn_emb :=
    ((coordCLE τ : (Fin m → ℝ) × (Fin r → ℝ) →L[ℝ] (Fin d → ℝ)).contDiff.comp
      ((planeReindex τ).contDiff.prodMk contDiff_const)).contDiffOn
  emb_mem z _ := ⟨fun j => by rw [coordCLE_apply_inr]; rfl, mem_univ _⟩
  ft y := (planeReindex τ).symm ((coordCLE τ).symm y).1
  contDiff_ft := (planeReindex τ).symm.contDiff.comp
    ((ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin r → ℝ)).contDiff.comp (coordCLE τ).symm.contDiff)
  ft_mem _ _ := by simp
  emb_ft x hx := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have h2 : ((coordCLE τ).symm x).2 = 0 := by
      funext j
      rw [coordCLE_symm_apply_snd]
      exact hx.1 j
    conv_rhs => rw [← (coordCLE τ).apply_symm_apply x]
    rw [← h2]
  ft_emb z _ := by
    rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The linear tube chart of the coordinate plane: `(z, n) ↦ coordCLE τ (reindex z, n)`. -/
noncomputable def planeSplit : ((Fin (d - r) → ℝ) × (Fin r → ℝ)) ≃L[ℝ] (Fin d → ℝ) :=
  ((planeReindex τ).prodCongr (ContinuousLinearEquiv.refl ℝ (Fin r → ℝ))).trans (coordCLE τ)

theorem planeSplit_apply (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    planeSplit τ p = coordCLE τ (planeReindex τ p.1, p.2) := rfl

/-- **The tube chart is the linear coordinate splitting.** -/
theorem tubeChart_coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ)
    (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : tubeChart (coordPlaneChart τ hs) p = planeSplit τ p :=
      by
  unfold tubeChart
  rw [rowFrame_eq, planeSplit_apply]
  change coordCLE τ (planeReindex τ p.1, 0) + (planeJ τ)ᵀ.mulVec p.2 = _
  rw [planeJ_transpose_mulVec, ← map_add]
  congr 1
  ext <;> simp

/-- **The certified domain is the normal ball**: `{(z, n) : ‖n‖ < ε}`. -/
theorem tubeChartDom_coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ) (ε : ℝ) (hε : 0 < ε) :
    tubeChartDom (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs) =
      {p : (Fin (d - r) → ℝ) × (Fin r → ℝ) | ‖p.2‖ < ε} := by
  ext p
  simp only [tubeChartDom, Set.mem_ofPred_eq]
  have hW : p.1 ∈ (coordPlaneChart τ hs).W := Set.mem_univ _
  have hR : rowFrame (coordPlaneAtlas τ) (coordPlaneChart τ hs).i ((coordPlaneChart τ hs).emb p.1)
      p.2 = coordCLE τ (0, p.2) := by
    rw [rowFrame_eq]
    exact planeJ_transpose_mulVec τ p.2
  rw [hR, norm_coordCLE, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  exact ⟨fun h => h.2, fun h => ⟨hW, h⟩⟩

/-- The flattened chart is the linear automorphism `planeSplit ∘ concat⁻¹`. -/
theorem flatChart_coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ) :
    flatChart (coordPlaneChart τ hs) =
      ⇑((coordPlaneChart τ hs).concat.symm.trans (planeSplit τ)) := by
  funext w
  rw [flatChart, tubeChart_coordPlaneChart]
  rfl

theorem measurePreserving_planeSplit :
    MeasurePreserving (planeSplit τ) volume volume := by
  have h1 : MeasurePreserving (planeReindex τ) volume volume := by
    have := volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ)
      (finCongr (by have := coordPlane_card τ; omega) : Fin (d - r) ≃ Fin m)
    refine this.congr (planeReindex τ).continuous.measurable (Filter.Eventually.of_forall fun z =>
      ?_)
    funext i
    obtain ⟨i', rfl⟩ : ∃ i', i = (finCongr (by have := coordPlane_card τ; omega) :
      Fin (d - r) ≃ Fin m) i' := ⟨_, (Equiv.apply_symm_apply _ i).symm⟩
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  have h2 : MeasurePreserving (Prod.map (planeReindex τ) (id : (Fin r → ℝ) → Fin r → ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact h1.prod (MeasurePreserving.id _)
  exact (measurePreserving_coordCLE τ).comp h2

/-- **The Jacobian density of the coordinate plane is `1`.** -/
theorem tubeJac_coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ)
    (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : tubeJac (coordPlaneChart τ hs) p = 1 := by
  unfold tubeJac
  rw [flatChart_coordPlaneChart, ContinuousLinearEquiv.fderiv]
  have hmp : MeasurePreserving ((coordPlaneChart τ hs).concat.symm.trans (planeSplit τ)) volume
      volume :=
    (measurePreserving_planeSplit τ).comp
      (((coordPlaneChart τ hs).measurePreserving_concat).symm
        (coordPlaneChart τ hs).concat.toHomeomorph.toMeasurableEquiv)
  exact abs_det_eq_one_of_measurePreserving volume _ hmp

/-- **The weighted density of the coordinate plane**: `1_{‖n‖<ε} · w(split p)`. -/
theorem tubeDensity_coordPlaneChart {s : Fin d → ℝ} (hs : s ∈ coordPlane τ) (ε : ℝ) (hε : 0 < ε)
    (wt : TubeWeight d) (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    tubeDensity (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs) wt p =
      if ‖p.2‖ < ε then wt.w (planeSplit τ p) else 0 := by
  by_cases hp : ‖p.2‖ < ε
  · have hp' : p ∈ tubeChartDom (coordPlaneTube τ ε hε).toNormalTubularChart
        (coordPlaneChart τ hs) := by
      rw [tubeChartDom_coordPlaneChart]
      exact hp
    rw [if_pos hp, tubeDensity_of_mem _ _ _ hp', tubeJac_coordPlaneChart, one_mul,
      tubeChart_coordPlaneChart]
  · have hp' : p ∉ tubeChartDom (coordPlaneTube τ ε hε).toNormalTubularChart
        (coordPlaneChart τ hs) := by
      rw [tubeChartDom_coordPlaneChart]
      exact hp
    rw [if_neg hp, tubeDensity_of_notMem _ _ _ hp']

/-- **The per-stratum formula on the ε-tube of a coordinate plane** with a tube weight:
`∫_{‖y − foot y‖<ε} w F dy = ∫_{‖y − foot y‖<ε} w · (∑_k ⟨D^k_⊥F, 𝖬^κ_k⟩)(foot y) dy`. -/
theorem integral_coordPlaneTube_eq_integral_condContraction {s : Fin d → ℝ}
    (hs : s ∈ coordPlane τ) (ε : ℝ) (hε : 0 < ε) (wt : TubeWeight d) {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn (fun y => wt.w y * F y) {y | ‖y - planeFoot τ y‖ < ε})
    {q : (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ z, HasFPowerSeriesOnBall (fun n => F (planeSplit τ (z, n))) (q z) 0 (Rad z))
    (hη : ∀ z, ∀ᵐ n ∂fibreMeasure volume
      (tubeDensity (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs) wt) z,
      n ∈ Metric.eball (0 : Fin r → ℝ) (Rad z))
    (hdom : ∀ z, Summable fun k => ‖q z k‖ * ∫ n, ‖n‖ ^ k ∂fibreMeasure volume
      (tubeDensity (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs) wt) z) :
    ∫ y in {y | ‖y - planeFoot τ y‖ < ε}, wt.w y * F y =
      ∫ y in {y | ‖y - planeFoot τ y‖ < ε}, wt.w y *
        condContractionSeries (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs)
          wt F (planeFoot τ y) := by
  have hU : (coordPlaneTube τ ε hε).toNormalTubularChart.U ∩
      (coordPlaneTube τ ε hε).toNormalTubularChart.proj ⁻¹' (coordPlaneChart τ hs).V' =
      {y | ‖y - planeFoot τ y‖ < ε} := by
    change {y | ‖y - planeFoot τ y‖ < ε} ∩ planeFoot τ ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
  have h := integral_tube_piece_eq_integral_condContraction
    (coordPlaneTube τ ε hε).toNormalTubularChart (coordPlaneChart τ hs) wt (hU ▸ hF)
    (fun z _ => by
      have := hq z
      simp_rw [← tubeChart_coordPlaneChart τ hs] at this
      exact this)
    (fun z _ => hη z) (fun z _ => hdom z)
  rw [hU] at h
  exact h

end GraphChart

end Grammar
