/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeCharts
import Grammar.ChartModelGeometry
import Grammar.OrthantDecomposition

/-!
# The cube blow-up as a chart model: the obligation fixture (CCCXLIV; phase E, unit E0a)

Consult #102 §1, §7. For chart `β` of the blow-up cover of the unit cube (CCLXXXIII) with the
quadratic phase, the data of the chart model of CCCXLIII are: active set `{β}`, `k_β = 1`,
`h_β = d − 1`, the unit `1 + ∑_{γ≠β} y_γ²` depending only on the inactive coordinates
(`unit_indep`), and `K ∘ φ_β` is exactly the chart phase (`phase_singleton`), which the chart
geometry resolves (`isResolutionOf_singleton`). The absolute Jacobian is `|y_β|^{d−1}`, even under
every coordinate reflection for every `d` (`abs_det_φ`, `abs_det_φ_refl`; the determinant itself
is not). The deepest stratum `{y_β = 0}` has `d − 1` free coordinates (`singleton_ne_univ` with
CCCXLIII). The **exact chart integral adapter**: for every integrand,
`∫_{wedge β} g = ∫_{cube} |y_β|^{d−1} g(φ_β y) dy` (★ `wedge_integral_eq`, by the change of
variables
off the null hyperplane), and the cube integral is the sum of the wedge integrals for integrable
integrands (★ `cube_integral_eq_sum`, a.e.-unique wedge). No producer assumptions are made.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling

namespace Grammar

namespace BlowUpCube

variable {d : ℕ} (β : Fin d)

/-! ### The singleton active data -/

/-- The unit depends only on the inactive coordinates. -/
theorem unit_indep {y y' : Fin d → ℝ} (h : ∀ γ, γ ≠ β → y γ = y' γ) : unit β y = unit β y' := by
  unfold unit
  congr 1
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [h γ (Finset.ne_of_mem_erase hγ)]

/-- `K ∘ φ_β` is the chart phase with active set `{β}`, `k_β = 1` and the unit. -/
theorem phase_singleton :
    ChartModel.phase d {β} (fun _ => 1) (unit β) = K ∘ φ β := by
  funext y
  simp only [Function.comp, ChartModel.phase, ChartModel.monoPhase, Finset.prod_singleton, K_φ,
    mul_one]

/-- The chart geometry (active `{β}`, orders `(1, d − 1)`) resolves `K ∘ φ_β`. -/
theorem isResolutionOf_singleton :
    (ChartModel.geometry d {β} (fun _ => 1) (fun _ => d - 1) fun _ _ => one_pos).IsResolutionOf
      (K ∘ φ β) := by
  rw [← phase_singleton]
  exact ChartModel.isResolutionOf d {β} _ _ _ (unit β) (unit_pos β)

theorem singleton_ne_univ (hd : 1 < d) : ({β} : Finset (Fin d)) ≠ Finset.univ := by
  intro h
  have := congrArg Finset.card h
  rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The absolute Jacobian `|y_β|^{d−1}`. -/
theorem abs_det_φ (y : Fin d → ℝ) : |(fderiv ℝ (φ β) y).det| = |y β| ^ (d - 1) := by
  rw [det_φ, abs_pow]

/-- The absolute Jacobian is even under every coordinate reflection (for every `d`). -/
theorem abs_det_φ_refl (σ : WaterFilling.CoordSign d) (y : Fin d → ℝ) :
    |(fderiv ℝ (φ β) (WaterFilling.refl σ y)).det| = |(fderiv ℝ (φ β) y).det| := by
  rw [abs_det_φ, abs_det_φ, WaterFilling.refl_apply, abs_mul, WaterFilling.abs_sgn, one_mul]

/-! ### The exact chart integral adapter -/

theorem ae_ne_zero_coord : ∀ᵐ y : Fin d → ℝ ∂volume, y β ≠ 0 :=
  WaterFilling.ae_coord_ne_zero.mono fun _ hy => hy β

theorem ae_eq_ne_zero : ({x : Fin d → ℝ | x β ≠ 0} : Set (Fin d → ℝ)) =ᵐ[volume] univ := by
  rw [ae_eq_univ]
  have h := ae_ne_zero_coord β
  rw [ae_iff] at h
  convert h using 2
  exact Set.compl_ofPred _

theorem measurableSet_ne_zero : MeasurableSet {y : Fin d → ℝ | y β ≠ 0} :=
  (measurableSet_singleton (0 : ℝ)).compl.preimage (measurable_pi_apply β)

theorem image_cube_inter :
    φ β '' (cube d ∩ {y | y β ≠ 0}) = wedge β ∩ {x | x β ≠ 0} := by
  rw [← image_eq β, ← Set.image_inter_preimage]
  congr 1
  ext y
  simp [φ_self]

/-- ★ **The exact chart integral adapter**: `∫_{wedge β} g = ∫_{cube} |y_β|^{d−1} g(φ_β y) dy`. -/
theorem wedge_integral_eq (g : (Fin d → ℝ) → ℝ) :
    ∫ x in wedge β, g x = ∫ y in cube d, |y β| ^ (d - 1) * g (φ β y) := by
  have hs : MeasurableSet (cube d ∩ {y | y β ≠ 0}) :=
    isCompact_cube.isClosed.measurableSet.inter (measurableSet_ne_zero β)
  have hf' : ∀ y ∈ cube d ∩ {y | y β ≠ 0},
      HasFDerivWithinAt (φ β) (fderiv ℝ (φ β) y) (cube d ∩ {y | y β ≠ 0}) y := fun y _ =>
    ((analyticOnNhd_φ β y (mem_univ _)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ β) (cube d ∩ {y | y β ≠ 0}) :=
    (blowUpChart_injOn_compl_pivotHyperplane (B d) β).mono fun y hy => hy.2
  have h1 := integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' hinj g
  rw [image_cube_inter, setIntegral_congr_set (inter_ae_eq_left_of_ae_eq_univ (ae_eq_ne_zero β)),
    setIntegral_congr_set (inter_ae_eq_left_of_ae_eq_univ (ae_eq_ne_zero β))] at h1
  rw [h1]
  simp only [abs_det_φ, smul_eq_mul]

/-! ### The cube integral is the sum of the wedge integrals -/

theorem isClosed_wedge : IsClosed (wedge β) := by
  have : wedge β = {x : Fin d → ℝ | |x β| ≤ 1} ∩ ⋂ γ, {x | |x γ| ≤ |x β|} := by
    ext x
    simp [wedge]
  rw [this]
  exact (isClosed_le (continuous_abs.comp (continuous_apply β)) continuous_const).inter
    (isClosed_iInter fun γ => isClosed_le (continuous_abs.comp (continuous_apply γ))
      (continuous_abs.comp (continuous_apply β)))

theorem measurableSet_wedge : MeasurableSet (wedge β) := (isClosed_wedge β).measurableSet

omit β in
/-- Almost every point lies in at most one wedge. -/
theorem ae_wedge_unique :
    ∀ᵐ x : Fin d → ℝ ∂volume, ∀ β γ : Fin d, β ≠ γ → ¬ (x ∈ wedge β ∧ x ∈ wedge γ) := by
  rw [ae_all_iff]
  intro β
  rw [ae_all_iff]
  intro γ
  by_cases hβγ : β = γ
  · exact Eventually.of_forall fun x h => absurd hβγ h
  · have h0 : volume (wedge β ∩ wedge γ) = 0 := volume_wedge_inter hβγ
    have h0' : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∉ wedge β ∩ wedge γ := by
      rw [ae_iff]
      simpa using h0
    exact h0'.mono fun x hx _ hxm => hx hxm

omit β in
/-- ★ **The cube integral is the sum of the wedge integrals** (integrable integrands). -/
theorem cube_integral_eq_sum [NeZero d] (g : (Fin d → ℝ) → ℝ) (hg : IntegrableOn g (cube d)) :
    ∫ x in cube d, g x = ∑ β : Fin d, ∫ x in wedge β, g x := by
  have hae : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
      (cube d).indicator g x = ∑ β : Fin d, (wedge β).indicator g x := by
    filter_upwards [ae_wedge_unique (d := d)] with x hx
    by_cases hS : x ∈ cube d
    · obtain ⟨β, hβ⟩ := mem_iUnion.1 ((iUnion_wedge (d := d)).symm ▸ hS)
      rw [indicator_of_mem hS, Finset.sum_eq_single β]
      · rw [indicator_of_mem hβ]
      · intro γ _ hγ
        rw [indicator_of_notMem]
        intro hγm
        exact hx γ β hγ ⟨hγm, hβ⟩
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [indicator_of_notMem hS]
      symm
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [indicator_of_notMem]
      intro h'
      exact hS (wedge_subset_cube β h')
  calc ∫ x in cube d, g x
      = ∫ x, (cube d).indicator g x :=
        (integral_indicator isCompact_cube.isClosed.measurableSet).symm
    _ = ∫ x, ∑ β : Fin d, (wedge β).indicator g x := integral_congr_ae hae
    _ = ∑ β : Fin d, ∫ x, (wedge β).indicator g x :=
        integral_finsetSum _ fun β _ =>
          (hg.mono_set (wedge_subset_cube β)).integrable_indicator (measurableSet_wedge β)
    _ = ∑ β : Fin d, ∫ x in wedge β, g x :=
        Finset.sum_congr rfl fun β _ => integral_indicator (measurableSet_wedge β)

/-- The original cube integral through the charts, with the Jacobian weight and the unit phase. -/
theorem cube_integral_eq_sum_chart [NeZero d] (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (cube d)) :
    ∫ x in cube d, g x = ∑ β : Fin d, ∫ y in cube d, |y β| ^ (d - 1) * g (φ β y) := by
  rw [cube_integral_eq_sum g hg]
  exact Finset.sum_congr rfl fun β _ => wedge_integral_eq β g

end BlowUpCube

end Grammar
