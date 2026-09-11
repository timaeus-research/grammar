/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StripBoxExpansion

/-!
# The local unconditional single-chart expansion (Astra #69 B1, completed)

The series hypothesis of `strip_cutoffExpansion` is discharged locally. The Jacobian of the
inverse strip normalisation is the reciprocal of the positive Jacobian of the rescaling
(`StripData.det_fderiv_inv`, by `HasFDerivAt.of_local_left_inverse` and `det_rescaleDerivAt`), so
the normal-form amplitude `normalAmp = |det D(T⁻¹)| · F∘T⁻¹` is **jointly analytic** on the image
of the strip for an analytic observable (`analyticAt_normalAmp`, `analyticAt_normalAmp_joint`).
Its power series at the tangential origin has some radius `R > 0`; shrinking the tangential base
to a small ball and the normal box to a side below `R / (t + n + 3)` gives the dimension margin, and
the strip-normalised expansion holds **with no hypothesis beyond analyticity**
(`strip_cutoffExpansion_local`): for the phase `unit · ∏ y_{n_j}^{2k_j}` with an analytic positive
unit and an analytic observable, some adapted region around every strip point over the tangential
origin has the full power–log cutoff expansion.

Non-claims (Astra #69): the region is small and chosen by the proof; the outer region, several
normalisation charts, and their ownership are not treated; the tangential origin is a
normalisation (translate the coordinates first).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

/-! ### The Jacobian of the inverse strip normalisation -/

section Inverse

variable {d : ℕ} {i : Fin d} {V : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {Q₀ : Set (Fin d → ℝ)}
  (SD : StripData i V ρ Q₀)

/-- **The derivative of the inverse** is the inverse of the derivative of the rescaling. -/
theorem StripData.det_fderiv_inv (hρ : AnalyticOnNhd ℝ ρ V) {z : Fin d → ℝ}
    (hz : z ∈ rescale i ρ '' SD.S) :
    (fderiv ℝ SD.inv z).det =
      (ρ (SD.inv z) + SD.inv z i * fderiv ℝ ρ (SD.inv z) (Pi.single i 1))⁻¹ := by
  set y := SD.inv z with hy
  have hyS : y ∈ SD.S := SD.inv_mem hz
  have hyV : y ∈ V := SD.S_sub hyS
  have hdet : ρ y + (y i • fderiv ℝ ρ y) (Pi.single i 1) ≠ 0 := by
    have := SD.jac_pos y hyS
    change ρ y + y i • fderiv ℝ ρ y (Pi.single i 1) ≠ 0
    rw [smul_eq_mul]
    exact this.ne'
  have hT : HasFDerivAt (rescale i ρ)
      (rescaleDerivEquiv i (ρ y) (y i • fderiv ℝ ρ y) hdet : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) y := by
    rw [coe_rescaleDerivEquiv]
    exact hasFDerivAt_rescale i (hρ y hyV).differentiableAt.hasFDerivAt
  have hcont : ContinuousAt SD.inv z := (SD.inv_analytic z hz).continuousAt
  have hev : ∀ᶠ w in 𝓝 z, rescale i ρ (SD.inv w) = w :=
    Filter.eventually_of_mem (SD.image_open.mem_nhds hz) fun w hw => SD.apply_inv hw
  have hinv := HasFDerivAt.of_local_left_inverse hcont hT hev
  rw [hinv.fderiv, ContinuousLinearEquiv.det_coe_symm, coe_rescaleDerivEquiv, det_rescaleDerivAt]
  rfl

theorem StripData.det_fderiv_inv_pos (hρ : AnalyticOnNhd ℝ ρ V) {z : Fin d → ℝ}
    (hz : z ∈ rescale i ρ '' SD.S) : 0 < (fderiv ℝ SD.inv z).det := by
  rw [SD.det_fderiv_inv hρ hz]
  exact inv_pos.2 (SD.jac_pos _ (SD.inv_mem hz))

/-- The Jacobian factor of the inverse as an analytic function on the image. -/
theorem StripData.analyticAt_det_fderiv_inv (hρ : AnalyticOnNhd ℝ ρ V)
    {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) :
    AnalyticAt ℝ (fun w => |(fderiv ℝ SD.inv w).det|) z := by
  have hyV : SD.inv z ∈ V := SD.S_sub (SD.inv_mem hz)
  have hinv := SD.inv_analytic z hz
  -- the explicit reciprocal Jacobian
  have hjac : AnalyticAt ℝ (fun y => ρ y + y i * fderiv ℝ ρ y (Pi.single i 1)) (SD.inv z) := by
    refine (hρ _ hyV).add (((ContinuousLinearMap.proj i :
      (Fin d → ℝ) →L[ℝ] ℝ).analyticAt _).mul ?_)
    exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin d → ℝ)).analyticAt _).comp
      (hρ _ hyV).fderiv
  have hne : ρ (SD.inv z) + SD.inv z i * fderiv ℝ ρ (SD.inv z) (Pi.single i 1) ≠ 0 :=
    (SD.jac_pos _ (SD.inv_mem hz)).ne'
  have h := ((hjac.inv hne).comp hinv)
  refine h.congr ?_
  filter_upwards [SD.image_open.mem_nhds hz] with w hw
  simp only [Function.comp, Pi.inv_apply]
  rw [abs_of_pos (SD.det_fderiv_inv_pos hρ hw), SD.det_fderiv_inv hρ hw]

end Inverse

/-! ### Joint analyticity of the normal-form amplitude -/

variable {t n : ℕ}

theorem analyticAt_prodToPi (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :
    AnalyticAt ℝ (prodToPi t n) p := by
  rw [analyticAt_pi_iff]
  intro x
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective x
  rcases s with i | j
  · have h : (fun q : (Fin t → ℝ) × (Fin (n + 1) → ℝ) =>
        prodToPi t n q (finSumFinEquiv (Sum.inl i))) = fun q => q.1 i :=
      funext fun q => prodToPi_apply_tIdx q i
    rw [h]
    exact ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)).analyticAt p
  · have h : (fun q : (Fin t → ℝ) × (Fin (n + 1) → ℝ) =>
        prodToPi t n q (finSumFinEquiv (Sum.inr j))) = fun q => q.2 j :=
      funext fun q => prodToPi_apply_nIdx q j
    rw [h]
    exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ _ _)).analyticAt p

section Main

variable {k : Fin (n + 1) → ℕ} {j₀ : Fin (n + 1)} {β : ℝ} {V : Set (Fin (t + (n + 1)) → ℝ)}
  {unit : (Fin (t + (n + 1)) → ℝ) → ℝ} {A : Set (Fin t → ℝ)} {b₁ : ℝ}
  (SD : StripData (nIdx t j₀) V (unitRoot β (2 * k j₀) unit) (stripBase t A j₀ b₁))

/-- **Joint analyticity of the normal-form amplitude** at points over the image of the strip. -/
theorem analyticAt_normalAmp (hβ : 0 < β) (hk : 0 < k j₀)
    (hunit : AnalyticOnNhd ℝ unit V) (hpos : ∀ y ∈ V, 0 < unit y)
    {F : (Fin (t + (n + 1)) → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F V)
    {p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)}
    (hp : prodToPi t n p ∈ rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S) :
    AnalyticAt ℝ (normalAmp SD F) p := by
  have hρ : AnalyticOnNhd ℝ (unitRoot β (2 * k j₀) unit) V := fun y hy =>
    analyticAt_unitRoot hβ (by omega) (hunit y hy) (hpos y hy)
  have h1 : AnalyticAt ℝ (fun w => |(fderiv ℝ SD.inv w).det|) (prodToPi t n p) :=
    SD.analyticAt_det_fderiv_inv hρ hp
  have h2 : AnalyticAt ℝ (fun w => F (SD.inv w)) (prodToPi t n p) :=
    (hF _ (SD.S_sub (SD.inv_mem hp))).comp (SD.inv_analytic _ hp)
  exact ((h1.mul h2).comp (analyticAt_prodToPi p))

/-- The joint amplitude `w ↦ normalAmp (w ∘ inl, w ∘ inr)` is analytic. -/
theorem analyticAt_normalAmp_joint (hβ : 0 < β) (hk : 0 < k j₀)
    (hunit : AnalyticOnNhd ℝ unit V) (hpos : ∀ y ∈ V, 0 < unit y)
    {F : (Fin (t + (n + 1)) → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F V) {w : Fin t ⊕ Fin (n + 1) → ℝ}
    (hw : prodToPi t n (w ∘ Sum.inl, w ∘ Sum.inr) ∈
      rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S) :
    AnalyticAt ℝ (fun w : Fin t ⊕ Fin (n + 1) → ℝ => normalAmp SD F (w ∘ Sum.inl, w ∘ Sum.inr))
      w := by
  have hL : AnalyticAt ℝ (fun w : Fin t ⊕ Fin (n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr)) w := by
    have : (fun w : Fin t ⊕ Fin (n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr)) =
        ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)).prod
          (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)) :
            (Fin t ⊕ Fin (n + 1) → ℝ) →L[ℝ] (Fin t → ℝ) × (Fin (n + 1) → ℝ)) := by
      funext w
      rfl
    rw [this]
    exact ContinuousLinearMap.analyticAt _ w
  exact AnalyticAt.comp (g := normalAmp SD F)
    (f := fun w : Fin t ⊕ Fin (n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr))
    (analyticAt_normalAmp SD hβ hk hunit hpos hF hw) hL

/-- **The local unconditional single-chart expansion.** For the phase `unit · ∏ y_{n_j}^{2k_j}` with
an analytic positive unit and an analytic observable, some adapted region around the strip point
over the tangential origin has the full power–log cutoff expansion, with no series hypothesis. -/
theorem strip_cutoffExpansion_local (hV : IsOpen V) (hk : ∀ j, 0 < k j) (hβ : 0 < β)
    (hunit : AnalyticOnNhd ℝ unit V) (hpos : ∀ y ∈ V, 0 < unit y)
    {K : (Fin (t + (n + 1)) → ℝ) → ℝ}
    (hK : ∀ y ∈ V, K y = unit y * ∏ j, y (nIdx t j) ^ (2 * k j)) (hA : IsCompact A)
    (h0 : (0 : Fin t → ℝ) ∈ A) (hb₁ : 0 < b₁) {F : (Fin (t + (n + 1)) → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧ ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
      CutoffExpansion Q Dg (fun N => ∫ y in SD.inv '' zBox t (A ∩ Metric.closedBall 0 B) b',
        F y * Real.exp (-N * K y)) c := by
  -- the joint series at the tangential origin
  set b₂ : ℝ := min b₁ SD.b with hb₂
  have hb₂pos : 0 < b₂ := lt_min hb₁ SD.b_pos
  have hmem : prodToPi t n ((0 : Fin t → ℝ), (0 : Fin (n + 1) → ℝ)) ∈
      rescale (nIdx t j₀) (unitRoot β (2 * k j₀) unit) '' SD.S := by
    have hz : prodToPi t n ((0 : Fin t → ℝ), (0 : Fin (n + 1) → ℝ)) ∈ zBox t A b₂ :=
      ⟨(0, 0), ⟨h0, fun j _ => by simp [hb₂pos.le]⟩, rfl⟩
    exact ((zBox_subset_cylinder le_rfl (min_le_left _ _) (min_le_right _ _)).trans
      SD.cyl_sub_image) hz
  have han := analyticAt_normalAmp_joint SD hβ (hk j₀) hunit hpos hF
    (w := (0 : Fin t ⊕ Fin (n + 1) → ℝ)) (by simpa using hmem)
  obtain ⟨P, R, hPR⟩ := han
  obtain ⟨ρ, hρ0, hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hPR.r_pos
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  -- the margin
  set B : ℝ := ρ / ((t + (n + 1) : ℕ) + 2) with hB
  have hBpos : 0 < B := by positivity
  have hBρ : ((t + (n + 1) : ℕ) : ℝ) * B < ρ := by
    rw [hB, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hB1 : B < ρ := by
    rw [hB, div_lt_iff₀ (by positivity)]
    nlinarith
  set b' : ℝ := min B b₂ with hb'
  have hb'pos : 0 < b' := lt_min hBpos hb₂pos
  refine ⟨B, b', hBpos, hb'pos, ?_⟩
  have hA' : IsCompact (A ∩ Metric.closedBall (0 : Fin t → ℝ) B) :=
    hA.inter_right Metric.isClosed_closedBall
  have hAB : ∀ v ∈ A ∩ Metric.closedBall (0 : Fin t → ℝ) B, ∀ i, |v i| ≤ B := by
    intro v hv i
    have h1 : ‖v‖ ≤ B := by simpa using hv.2
    exact (norm_le_pi_norm v i).trans h1
  exact strip_cutoffExpansion SD hV hk hβ hpos hK hA' inter_subset_left hb'pos
    ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
    (min_le_left _ _) hBpos hAB hF.continuousOn hPR hρR hBρ hB1 hδ

end Main

end Grammar
