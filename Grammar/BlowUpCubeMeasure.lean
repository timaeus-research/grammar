/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeExpansion

/-!
# The cube prior measure as the sum of the piece measures (B4a)

The `d · 2^d` pieces of the cube blow-up (CCCXLVII) carry the weighted prior measures
`μ_{βσ} = 1_{[0,1]^d}(z) |z_β|^{d−1} p⁺_{βσ}(z) dz` on the chart boxes. Pushed forward along the
piece charts `φ_β ∘ R_σ` they add up EXACTLY to the prior measure `1_{[−1,1]^d}(x) p(x) dx` on
the cube (`sum_map_pieceMeasure`): the measure-level form of the exact chart decomposition
`cube_integral_eq_sum_pieces`. This is the `transport` field of the genuine blow-up certificate.

Also here: the piece packets' representatives agree with `p ∘ φ_β ∘ R_σ`, `F ∘ φ_β ∘ R_σ` on the
whole signed cube `[−1,1]^d`, not only on the positive box (`priorRep_eq_of_mem_cube`,
`obsRep_eq_of_mem_cube`), because the piece packet's complex domain is the preimage of the
packet's domain under the complexified chart — this is what lets the fibre balls of the chart
cores (which leave the positive box) see the original observable.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox CoordModel

variable {d : ℕ} (β : Fin d) {p F : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension 1 p F)
  (σ : CoordSign d)

/-! ### The representatives on the signed cube -/

theorem cube_eq_piBox : cube d = piBox d (Icc (-1) 1) := rfl

theorem refl_mem_cube {y : Fin d → ℝ} (hy : y ∈ cube d) : refl σ y ∈ cube d := by
  rw [mem_cube] at hy ⊢
  intro j
  rw [refl_apply, abs_mul, abs_sgn, one_mul]
  exact hy j

/-- Points of the signed cube lie in the real domain of the piece packet. -/
theorem mem_realDomain_pieceExt {y : Fin d → ℝ} (hy : y ∈ cube d) :
    y ∈ (pieceExt β A σ).realDomain := by
  change complexify y ∈ reflC σ ⁻¹' (φℂ β ⁻¹' A.Ω)
  rw [mem_preimage, mem_preimage, ← complexify_refl, ← complexify_φ]
  exact A.box_subset _ (φ_mem_cube β (refl_mem_cube σ hy))

theorem obsRep_eq_of_mem_cube {y : Fin d → ℝ} (hy : y ∈ cube d) :
    (pieceExt β A σ).obsRep y = F (φ β (refl σ y)) :=
  (pieceExt β A σ).obsRep_eq_of_mem (mem_realDomain_pieceExt β A σ hy)

theorem priorRep_eq_of_mem_cube {y : Fin d → ℝ} (hy : y ∈ cube d) :
    (pieceExt β A σ).priorRep y = p (φ β (refl σ y)) :=
  (pieceExt β A σ).priorRep_eq_of_mem (mem_realDomain_pieceExt β A σ hy)

theorem piBox_subset_cube : piBox d (Icc 0 1) ⊆ cube d := fun z hz => by
  rw [mem_cube]
  intro j
  have := hz j (mem_univ j)
  rw [mem_Icc] at this
  exact abs_le.2 ⟨by linarith [this.1], this.2⟩

/-! ### A measurable representative of the prior on the cube -/

omit β σ in
open scoped Classical in
/-- The prior, made measurable by cutting off outside the cube. -/
noncomputable def pM (_A : HolomorphicSignedBoxExtension 1 p F) : (Fin d → ℝ) → ℝ :=
  (cube d).piecewise p 0

omit β σ in
open scoped Classical in
theorem measurable_pM : Measurable (pM A) :=
  A.continuousOn_prior.measurable_piecewise continuousOn_const isCompact_cube.isClosed.measurableSet

omit β σ in
open scoped Classical in
theorem pM_of_mem {x : Fin d → ℝ} (hx : x ∈ cube d) : pM A x = p x := by
  unfold pM
  exact piecewise_eq_of_mem _ _ _ hx

omit β σ in
open scoped Classical in
theorem pM_of_notMem {x : Fin d → ℝ} (hx : x ∉ cube d) : pM A x = 0 := by
  unfold pM
  exact piecewise_eq_of_notMem _ _ _ hx

omit β σ in
theorem pM_nonneg (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x) (x : Fin d → ℝ) : 0 ≤ pM A x := by
  by_cases hx : x ∈ cube d
  · rw [pM_of_mem A hx]
    exact hp0 x hx
  · rw [pM_of_notMem A hx]

omit β σ in
theorem exists_bound_pM : ∃ M, 0 ≤ M ∧ ∀ x, |pM A x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_cube.exists_bound_of_continuousOn A.continuousOn_prior
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ cube d
  · rw [pM_of_mem A hx]
    exact (hM x hx).trans (le_max_left _ _)
  · rw [pM_of_notMem A hx, abs_zero]
    exact le_max_right _ _

/-! ### The piece measures -/

/-- The piece density `|z_β|^{d−1} p⁺_{βσ}(z)` on the chart box. -/
noncomputable def pieceDensity (z : Fin d → ℝ) : ℝ :=
  wgt (hS β (d - 1)) z * WaterFilling.posPart (pieceExt β A σ).priorRep z

theorem measurable_pieceDensity : Measurable (pieceDensity β A σ) := by
  unfold pieceDensity
  have h1 : Measurable (wgt (hS β (d - 1))) := by
    have : wgt (hS β (d - 1)) = fun z : Fin d → ℝ => |z β| ^ (d - 1) := funext fun z => wgt_hS β _ z
    rw [this]
    exact (measurable_pi_apply β).abs.pow_const _
  exact h1.mul (measurable_posPart (pieceExt β A σ).measurable_priorRep)

theorem pieceDensity_nonneg (z : Fin d → ℝ) : 0 ≤ pieceDensity β A σ z :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _)
    (WaterFilling.posPart_nonneg _ _)

/-- The weighted prior measure of a piece on its chart box. -/
noncomputable def pieceMeasure : Measure (Fin d → ℝ) :=
  (volume.restrict (piBox d (Icc 0 1))).withDensity fun z => ENNReal.ofReal (pieceDensity β A σ z)

theorem pieceCert_L_μ (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x) :
    (pieceCert β A σ hp0).L.μ = pieceMeasure β A σ := rfl

instance : IsFiniteMeasure (volume.restrict (cube d)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_cube.measure_lt_top⟩

instance : IsFiniteMeasure (volume.restrict (piBox d (Icc (-1) 1))) :=
  inferInstanceAs (IsFiniteMeasure (volume.restrict (cube d)))

instance : IsFiniteMeasure (volume.restrict (piBox d (Icc 0 1))) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top⟩

/-- The pulled-back cube integrand equals the piece density on the box. -/
theorem piece_integrand_eq (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)
    {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 1)) :
    |refl σ z β| ^ (d - 1) * pM A (φ β (refl σ z)) = pieceDensity β A σ z := by
  unfold pieceDensity
  rw [posPart_priorRep_piece β A σ hp0 hz, pM_of_mem A (φ_mem_cube β (refl_mem_cube σ
    (piBox_subset_cube hz))), ← wgt_hS β (d - 1), wgt_refl]

/-- The piece density is bounded on the box by the bound of the prior. -/
theorem pieceDensity_le (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x) {M : ℝ}
    (hM : ∀ x, |pM A x| ≤ M) {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 1)) :
    pieceDensity β A σ z ≤ M := by
  rw [← piece_integrand_eq β A σ hp0 hz]
  have h1 : |refl σ z β| ^ (d - 1) ≤ 1 := by
    have := (mem_cube.1 (refl_mem_cube σ (piBox_subset_cube hz))) β
    exact pow_le_one₀ (abs_nonneg _) this
  have h2 : 0 ≤ pM A (φ β (refl σ z)) := pM_nonneg A hp0 _
  calc |refl σ z β| ^ (d - 1) * pM A (φ β (refl σ z)) ≤ 1 * pM A (φ β (refl σ z)) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ ≤ M := by rw [one_mul]; exact (le_abs_self _).trans (hM _)

omit β σ in
/-- ★ **The prior measure on the cube is the sum of the pushed piece measures**: the exact chart
decomposition of the cube integral, at the level of measures. -/
theorem sum_map_pieceMeasure [NeZero d] (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x) :
    ∑ β : Fin d, ∑ σ : CoordSign d, (pieceMeasure β A σ).map (φ β ∘ refl σ) =
      (volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (pM A x) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_pM A
  ext s hs
  set g : (Fin d → ℝ) → ℝ := s.indicator (pM A) with hg
  have hgm : Measurable g := (measurable_pM A).indicator hs
  have hgb : ∀ x, |g x| ≤ M := fun x => by
    rw [hg]
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      exact hM x
    · rw [indicator_of_notMem hx, abs_zero]
      exact hM0
  have hgi : IntegrableOn g (cube d) :=
    (integrable_const M).mono' hgm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x)
  -- the right-hand side
  have hR : ((volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (pM A x)) s =
      ENNReal.ofReal (∫ x in cube d, g x) := by
    rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_const M).mono' (measurable_pM A).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x))
      (Eventually.of_forall (pM_nonneg A hp0)), ← integral_indicator hs]
  -- the pieces
  have hL : ∀ β σ, ((pieceMeasure β A σ).map (φ β ∘ refl σ)) s = ENNReal.ofReal
      (∫ z in piBox d (Icc 0 1), ((φ β ∘ refl σ) ⁻¹' s).indicator (pieceDensity β A σ) z) := by
    intro β σ
    have hΨm : Measurable (φ β ∘ refl σ) :=
      (continuous_φ β).measurable.comp (continuous_refl σ).measurable
    rw [Measure.map_apply hΨm hs, pieceMeasure, withDensity_apply _ (hΨm hs),
      ← ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall (pieceDensity_nonneg β A σ)),
      ← integral_indicator (hΨm hs)]
    refine (integrable_const M).mono' (measurable_pieceDensity β A σ).aestronglyMeasurable ?_
    rw [Measure.restrict_restrict (hΨm hs)]
    filter_upwards [ae_restrict_mem ((hΨm hs).inter (measurableSet_W 1))] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pieceDensity_nonneg β A σ z)]
    exact pieceDensity_le β A σ hp0 hM hz.2
  have hI0 : ∀ β σ, 0 ≤ ∫ z in piBox d (Icc 0 1),
      ((φ β ∘ refl σ) ⁻¹' s).indicator (pieceDensity β A σ) z := fun β σ =>
    integral_nonneg fun z => indicator_nonneg (fun z _ => pieceDensity_nonneg β A σ z) z
  rw [Measure.finsetSum_apply, hR]
  simp_rw [Measure.finsetSum_apply, hL]
  have h1 : ∀ β : Fin d, ∑ σ : CoordSign d, ENNReal.ofReal (∫ z in piBox d (Icc 0 1),
      ((φ β ∘ refl σ) ⁻¹' s).indicator (pieceDensity β A σ) z) =
      ENNReal.ofReal (∑ σ : CoordSign d, ∫ z in piBox d (Icc 0 1),
        ((φ β ∘ refl σ) ⁻¹' s).indicator (pieceDensity β A σ) z) := fun β =>
    (ENNReal.ofReal_sum_of_nonneg fun σ _ => hI0 β σ).symm
  simp_rw [h1]
  rw [← ENNReal.ofReal_sum_of_nonneg fun β _ => Finset.sum_nonneg fun σ _ => hI0 β σ]
  congr 1
  -- the real identity
  rw [cube_integral_eq_sum_chart g hgi]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hint : IntegrableOn (fun y => |y β| ^ (d - 1) * g (φ β y)) (piBox d (Icc (-1) 1)) := by
    have hm : Measurable fun y : Fin d → ℝ => |y β| ^ (d - 1) * g (φ β y) :=
      ((measurable_pi_apply β).abs.pow_const _).mul (hgm.comp (continuous_φ β).measurable)
    refine (integrable_const M).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem
      (isCompact_univ_pi fun _ => isCompact_Icc).isClosed.measurableSet] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs]
    have h1 : |y β| ^ (d - 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) ((mem_cube.1 hy) β)
    calc |y β| ^ (d - 1) * |g (φ β y)| ≤ 1 * M :=
          mul_le_mul h1 (hgb _) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  rw [cube_eq_piBox, setIntegral_signedBox_eq_sum 1 _ hint]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [setIntegral_orthantBox 1 σ]
  refine setIntegral_congr_fun (measurableSet_W 1) fun z hz => ?_
  by_cases hmem : φ β (refl σ z) ∈ s
  · rw [indicator_of_mem (show z ∈ (φ β ∘ refl σ) ⁻¹' s from hmem), hg, indicator_of_mem hmem]
    exact (piece_integrand_eq β A σ hp0 hz).symm
  · rw [indicator_of_notMem (show z ∉ (φ β ∘ refl σ) ⁻¹' s from hmem), hg,
      indicator_of_notMem hmem, mul_zero]

end BlowUpCube

end Grammar
