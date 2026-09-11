/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CentredChart
import Grammar.StripLocalExpansion

/-!
# The orthant charts of a centred hironaka chart (towards the chart theorem)

Given the centred chart data `C` of a hironaka chart at a divisor point and strip data `SD` for the
unit-removal rescaling of its phase unit, the **orthant chart** for the sign pattern `s` is the
composite `Ψ_s(y) = φ(T⁻¹(R_s y) + y₀)` of the reflection of the normal coordinates, the inverse
strip normalisation and the translated chart (`orthantChart`). On the positive box it is a split box
chart (`exists_splitBoxChart_orthant`): its Jacobian factorises as
`|det DΨ_s| = ∏_j u_j^{h_j} · jac₀ · ρ^{-h_{j₀}} · |det DT⁻¹|` (chain rule, `det_comp'`,
`prod_abs_pow_inv_nIdx`), the phase is exactly `β ∏ u_j^{2k_j}` (`phase_inv`), it is injective off
the normal hyperplanes (from the chart's injectivity off the Jacobian divisor and
`StripData.inv_apply_ne_zero`), and the amplitude `orthantAmp = jac · F∘Ψ_s` is realised by the
tangential datum of its joint series.

Non-claims: the joint series of the amplitude is a hypothesis here (discharged locally in the next
unit); no tiling yet.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-! ### Determinants of compositions -/

theorem det_comp' (f g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) : (f.comp g).det = f.det * g.det := by
  unfold ContinuousLinearMap.det
  exact LinearMap.det_comp _ _

/-! ### Nonvanishing of the inverse strip normalisation off the divisor -/

section Strip

variable {i : Fin d} {V : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ} {Q₀ : Set (Fin d → ℝ)}
  (SD : StripData i V ρ Q₀)

/-- The coordinates of the inverse image: unchanged except at `i`, where they are divided by `ρ`. -/
theorem StripData.inv_apply_of_ne {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) {x : Fin d}
    (hx : x ≠ i) : SD.inv z x = z x := by
  have := congrFun (SD.apply_inv hz) x
  rwa [rescale_apply_of_ne hx] at this

theorem StripData.inv_apply_self_mul {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) :
    SD.inv z i * ρ (SD.inv z) = z i := by
  have := congrFun (SD.apply_inv hz) i
  rwa [rescale_apply_self] at this

/-- The inverse preserves nonvanishing of every coordinate. -/
theorem StripData.inv_apply_ne_zero {z : Fin d → ℝ} (hz : z ∈ rescale i ρ '' SD.S) {x : Fin d}
    (hx : z x ≠ 0) : SD.inv z x ≠ 0 := by
  by_cases hxi : x = i
  · subst hxi
    intro h0
    have := SD.inv_apply_self_mul hz
    rw [h0, zero_mul] at this
    exact hx this.symm
  · rwa [SD.inv_apply_of_ne hz hxi]

end Strip

/-- The normal monomial of the inverse image:
`∏_j |y'_{n_j}|^{e_j} = (∏_j |z_{n_j}|^{e_j}) / ρ(y')^{e_{j₀}}` for `T y' = z`. -/
theorem prod_abs_pow_inv_nIdx {t n : ℕ} (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) (e : Fin (n + 1) → ℕ)
    (j₀ : Fin (n + 1)) {ρ : (Fin d → ℝ) → ℝ} {y' z : Fin d → ℝ}
    (hz : rescale (nIdx σ j₀) ρ y' = z) (hρ : 0 < ρ y') :
    ∏ j, |y' (nIdx σ j)| ^ e j = (∏ j, |z (nIdx σ j)| ^ e j) * (ρ y' ^ e j₀)⁻¹ := by
  have h : ∏ j, |z (nIdx σ j)| ^ e j = ρ y' ^ e j₀ * ∏ j, |y' (nIdx σ j)| ^ e j := by
    rw [← hz, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
      ← Finset.mul_prod_erase Finset.univ (fun j => |y' (nIdx σ j)| ^ e j) (Finset.mem_univ j₀),
      rescale_apply_self, abs_mul, abs_of_pos hρ, mul_pow,
      Finset.prod_congr rfl fun j hj => by
        rw [rescale_apply_of_ne (fun h => Finset.ne_of_mem_erase hj (nIdx_injective h))]]
    ring
  rw [h]
  field_simp

/-! ### The orthant chart -/

variable {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {h : Fin d →₀ ℕ} {y₀ : Fin d → ℝ}
  (C : CentredChartData K φ h y₀) {β : ℝ} {j₀ : Fin (C.n + 1)} {A : Set (Fin C.t → ℝ)} {b₁ : ℝ}
  (SD : StripData (nIdx C.σ j₀) C.V₀ (unitRoot β (2 * C.k j₀) C.unit₀) (stripBase C.σ A j₀ b₁))

/-- The translated chart `y ↦ φ(y + y₀)`. -/
def translated (φ : (Fin d → ℝ) → (Fin d → ℝ)) (y₀ y : Fin d → ℝ) : Fin d → ℝ := φ (y + y₀)

/-- The orthant chart `Ψ_s = φ̃ ∘ T⁻¹ ∘ R_s`. -/
noncomputable def orthantChart (s : Fin (C.n + 1) → Bool) (y : Fin d → ℝ) : Fin d → ℝ :=
  translated φ y₀ (SD.inv (splitReflect C.σ s y))

/-- The open set on which the orthant chart is analytic. -/
def orthantDomain (s : Fin (C.n + 1) → Bool) : Set (Fin d → ℝ) :=
  splitReflect C.σ s ⁻¹' (rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀) '' SD.S)

/-- The Jacobian factor of the orthant chart: `jac₀ · ρ^{-h_{j₀}} · |det DT⁻¹|`. -/
noncomputable def orthantJacFun (s : Fin (C.n + 1) → Bool) (y : Fin d → ℝ) : ℝ :=
  C.jac₀ (SD.inv (splitReflect C.σ s y)) *
    (unitRoot β (2 * C.k j₀) C.unit₀ (SD.inv (splitReflect C.σ s y)) ^ h (nIdx C.σ j₀))⁻¹ *
    |(fderiv ℝ SD.inv (splitReflect C.σ s y)).det|

/-- The Jacobian factor extended by zero off the orthant domain. -/
noncomputable def orthantJac (s : Fin (C.n + 1) → Bool) : (Fin d → ℝ) → ℝ :=
  open scoped Classical in (orthantDomain C SD s).piecewise (orthantJacFun C SD s) 0

/-- The amplitude of the orthant chart in product coordinates. -/
noncomputable def orthantAmp (s : Fin (C.n + 1) → Bool) (F : (Fin d → ℝ) → ℝ)
    (p : (Fin C.t → ℝ) × (Fin (C.n + 1) → ℝ)) : ℝ :=
  orthantJac C SD s (prodToPi C.σ p) * F (orthantChart C SD s (prodToPi C.σ p))

theorem isOpen_orthantDomain (s : Fin (C.n + 1) → Bool) : IsOpen (orthantDomain C SD s) :=
  SD.image_open.preimage (splitReflect C.σ s).continuous

theorem mem_orthantDomain_iff (s : Fin (C.n + 1) → Bool) (y : Fin d → ℝ) :
    y ∈ orthantDomain C SD s ↔
      splitReflect C.σ s y ∈ rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀) '' SD.S :=
  Iff.rfl

/-- The positive box lies in the orthant domain when its side is below the strip heights. -/
theorem splitPosBox_subset_orthantDomain (s : Fin (C.n + 1) → Bool) {A' : Set (Fin C.t → ℝ)}
    (hA'A : A' ⊆ A) {b : ℝ} (hbb₁ : b ≤ b₁) (hbSD : b ≤ SD.b) :
    splitPosBox C.σ A' b ⊆ orthantDomain C SD s := by
  intro y hy
  rw [mem_orthantDomain_iff]
  refine ((zBox_subset_cylinder hA'A hbb₁ hbSD).trans SD.cyl_sub_image) ?_
  rw [splitPosBox] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [splitReflect_prodToPi]
  refine ⟨reflectChart s p, ⟨hp.1, fun j _ => ?_⟩, rfl⟩
  rw [reflectChart_apply]
  simp only [reflectEquiv_apply]
  have := hp.2 j (mem_univ j)
  rw [mem_Icc, ← abs_le, abs_mul, abs_boolSgn, one_mul]
  exact abs_le.2 ⟨by linarith [this.1, this.2], this.2⟩

/-! ### Analyticity and derivative of the orthant chart -/

section Analytic

variable (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀)) (s : Fin (C.n + 1) → Bool)
  {y : Fin d → ℝ} (hy : y ∈ orthantDomain C SD s)
include hy

/-- The inverse image of the reflected point lies in the strip. -/
theorem inv_reflect_mem : SD.inv (splitReflect C.σ s y) ∈ SD.S := SD.inv_mem hy

theorem inv_reflect_mem_V₀ : SD.inv (splitReflect C.σ s y) ∈ C.V₀ := SD.S_sub (SD.inv_mem hy)

include hφ in
theorem analyticAt_orthantChart : AnalyticAt ℝ (orthantChart C SD s) y := by
  have h1 : AnalyticAt ℝ (splitReflect C.σ s) y := (splitReflect C.σ s).analyticAt y
  have h2 : AnalyticAt ℝ SD.inv (splitReflect C.σ s y) := SD.inv_analytic _ hy
  have h3 : AnalyticAt ℝ (fun w => w + y₀) (SD.inv (splitReflect C.σ s y)) :=
    analyticAt_id.add analyticAt_const
  have h4 := hφ _ (inv_reflect_mem_V₀ C SD s hy)
  have h5 : AnalyticAt ℝ (φ ∘ fun w => w + y₀) (SD.inv (splitReflect C.σ s y)) :=
    AnalyticAt.comp (g := φ) (f := fun w => w + y₀) h4 h3
  have h6 : AnalyticAt ℝ (SD.inv ∘ splitReflect C.σ s) y :=
    AnalyticAt.comp (g := SD.inv) (f := splitReflect C.σ s) h2 h1
  exact AnalyticAt.comp (g := φ ∘ fun w => w + y₀) (f := SD.inv ∘ splitReflect C.σ s) h5 h6

include hβ in
theorem analyticAt_orthantJacFun : AnalyticAt ℝ (orthantJacFun C SD s) y := by
  have hw := inv_reflect_mem_V₀ C SD s hy
  have h1 : AnalyticAt ℝ (splitReflect C.σ s) y := (splitReflect C.σ s).analyticAt y
  have h2 : AnalyticAt ℝ (SD.inv ∘ splitReflect C.σ s) y :=
    AnalyticAt.comp (g := SD.inv) (f := splitReflect C.σ s) (SD.inv_analytic _ hy) h1
  have hρ : AnalyticOnNhd ℝ (unitRoot β (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot hβ (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  have hA : AnalyticAt ℝ (fun y => C.jac₀ (SD.inv (splitReflect C.σ s y))) y :=
    AnalyticAt.comp (g := C.jac₀) (f := SD.inv ∘ splitReflect C.σ s) (C.jac₀_analytic _ hw) h2
  have hB : AnalyticAt ℝ (fun y =>
      (unitRoot β (2 * C.k j₀) C.unit₀ (SD.inv (splitReflect C.σ s y)) ^ h (nIdx C.σ j₀))⁻¹) y := by
    have := ((hρ _ hw).pow (h (nIdx C.σ j₀))).inv
      (pow_ne_zero _ (unitRoot_pos β _ C.unit₀ _).ne')
    exact AnalyticAt.comp (g := (unitRoot β (2 * C.k j₀) C.unit₀ ^ h (nIdx C.σ j₀))⁻¹)
      (f := SD.inv ∘ splitReflect C.σ s) this h2
  have hC : AnalyticAt ℝ (fun y => |(fderiv ℝ SD.inv (splitReflect C.σ s y)).det|) y :=
    AnalyticAt.comp (g := fun w => |(fderiv ℝ SD.inv w).det|) (f := splitReflect C.σ s)
      (SD.analyticAt_det_fderiv_inv hρ hy) h1
  exact (hA.mul hB).mul hC

include hβ in
theorem orthantJacFun_pos : 0 < orthantJacFun C SD s y := by
  have hw := inv_reflect_mem_V₀ C SD s hy
  have hρ : AnalyticOnNhd ℝ (unitRoot β (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot hβ (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  unfold orthantJacFun
  refine mul_pos (mul_pos (C.jac₀_pos _ hw) (inv_pos.2 (pow_pos (unitRoot_pos _ _ _ _) _))) ?_
  exact abs_pos.2 (SD.det_fderiv_inv_pos hρ hy).ne'

include hφ in
/-- **The Jacobian of the orthant chart** off the normal hyperplanes: with `w = T⁻¹(R_s y)`,
`|det DΨ_s(y)| = |det Dφ(w + y₀)| · |det DT⁻¹(R_s y)|`. -/
theorem abs_det_fderiv_orthantChart :
    |(fderiv ℝ (orthantChart C SD s) y).det| =
      |(fderiv ℝ φ (SD.inv (splitReflect C.σ s y) + y₀)).det| *
        |(fderiv ℝ SD.inv (splitReflect C.σ s y)).det| := by
  set z := splitReflect C.σ s y with hz
  set w := SD.inv z with hw
  have hwV := inv_reflect_mem_V₀ C SD s hy
  have hR : HasFDerivAt (splitReflect C.σ s)
      ((splitReflect C.σ s : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) y :=
    (splitReflect C.σ s).hasFDerivAt
  have hI := SD.hasFDerivAt_inv hy
  have hadd : HasFDerivAt (fun v => v + y₀) (ContinuousLinearMap.id ℝ (Fin d → ℝ)) w :=
    (hasFDerivAt_id w).add_const y₀
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (w + y₀)) (w + y₀) :=
    (hφ _ hwV).differentiableAt.hasFDerivAt
  have hcomp := ((hφ'.comp w hadd).comp z hI).comp y hR
  have hΨ : HasFDerivAt (orthantChart C SD s)
      ((((fderiv ℝ φ (w + y₀)).comp (ContinuousLinearMap.id ℝ (Fin d → ℝ))).comp
        (fderiv ℝ SD.inv z)).comp (splitReflect C.σ s : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) y :=
    hcomp
  have hid : (ContinuousLinearMap.id ℝ (Fin d → ℝ)).det = 1 := by
    unfold ContinuousLinearMap.det
    rw [ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [hΨ.fderiv, det_comp', det_comp', det_comp', hid, abs_mul, abs_mul, abs_mul,
    abs_det_splitReflect, mul_one, abs_one, mul_one]

end Analytic

/-! ### The orthant chart as a split box chart -/

theorem measurable_orthantJac (hβ : 0 < β) (s : Fin (C.n + 1) → Bool) :
    Measurable (orthantJac C SD s) := by
  classical
  unfold orthantJac
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
    (isOpen_orthantDomain C SD s).measurableSet
  intro y hy
  exact (analyticAt_orthantJacFun C SD hβ s hy).continuousAt.continuousWithinAt

theorem orthantJac_eq (s : Fin (C.n + 1) → Bool) {y : Fin d → ℝ} (hy : y ∈ orthantDomain C SD s) :
    orthantJac C SD s y = orthantJacFun C SD s y := by
  classical
  unfold orthantJac
  exact Set.piecewise_eq_of_mem _ _ _ hy

/-- The normal coordinates of the positive box are positive. -/
theorem prodToPi_apply_nIdx_pos {A' : Set (Fin C.t → ℝ)} {b : ℝ}
    {p : (Fin C.t → ℝ) × (Fin (C.n + 1) → ℝ)} (hp : p ∈ A' ×ˢ piBox (C.n + 1) (Ioc 0 b))
    (j : Fin (C.n + 1)) : 0 < prodToPi C.σ p (nIdx C.σ j) := by
  rw [prodToPi_apply_nIdx]
  exact (hp.2 j (mem_univ j)).1

/-- **The orthant chart is a split box chart.** Hypotheses: the chart `φ` is analytic on the
centred neighbourhood and injective off the Jacobian divisor there, the localisation data has
phase `K` and observable `F` on the translated chart, and the orthant amplitude has a joint power
series with a margin `(t + n + 1) B < r₀ < R` over the compact tangential base `A' ⊆ A`. -/
theorem exists_splitBoxChart_orthant (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    {D : LocalisationData (Fin d → ℝ)}
    (hphase : ∀ w ∈ C.V₀, D.phase (translated φ y₀ w) = K (translated φ y₀ w))
    {F : (Fin d → ℝ) → ℝ} (hobs : ∀ w ∈ C.V₀, D.obs (translated φ y₀ w) = F (translated φ y₀ w))
    {A' : Set (Fin C.t → ℝ)} (hA' : IsCompact A') (hA'A : A' ⊆ A) {b B : ℝ} (hb : 0 < b)
    (hbb₁ : b ≤ b₁) (hbSD : b ≤ SD.b) (hbB : b ≤ B) (hB : 0 < B)
    (hAB : ∀ v ∈ A', ∀ i, |v i| ≤ B) (s : Fin (C.n + 1) → Bool)
    {P : FormalMultilinearSeries ℝ (Fin C.t ⊕ Fin (C.n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall
      (fun w => orthantAmp C SD s F (w ∘ Sum.inl, w ∘ Sum.inr)) P 0 R) {r₀ : ℝ≥0}
    (hr₀ : (r₀ : ℝ≥0∞) < R) (hBr₀ : ((C.t + (C.n + 1) : ℕ) : ℝ) * B < r₀) (hB1 : B < r₀) :
    ∃ X : SplitBoxChart C.σ D A' b β, X.Ψ = orthantChart C SD s ∧
      X.h = (fun j => h (nIdx C.σ j)) ∧ X.k = C.k ∧ X.jac = orthantJac C SD s ∧
      ∀ (v : A') (u : Fin (C.n + 1) → ℝ), (∀ j, |u j| ≤ b) →
        evalF (toEta b (X.amp v)) u = orthantAmp C SD s F (v.1, u) := by
  classical
  have : CompactSpace A' := isCompact_iff_compactSpace.1 hA'
  have hcard : (Fintype.card (Fin C.t ⊕ Fin (C.n + 1)) : ℝ) * B < r₀ := by
    simpa [Fintype.card_sum] using hBr₀
  have hW : Summable (jointWeight P B) :=
    summable_jointWeight P B (summable_monoFamily_mul_pow P (hr₀.trans_le hG.r_le) hB.le hcard)
  set x : TangentialData A' (C.n + 1) := jointTangentialData P B hb hbB hB hW A' hAB with hx
  have hbox := splitPosBox_subset_orthantDomain C SD s hA'A hbb₁ hbSD
  have hρ : AnalyticOnNhd ℝ (unitRoot β (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot hβ (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  -- the reflected point of a box point has nonvanishing normal coordinates
  have hne : ∀ p ∈ A' ×ˢ piBox (C.n + 1) (Ioc 0 b), ∀ j,
      splitReflect C.σ s (prodToPi C.σ p) (nIdx C.σ j) ≠ 0 := fun p hp j => by
    rw [splitReflect_apply]
    exact mul_ne_zero (splitSgn_ne_zero _ _ _) (prodToPi_apply_nIdx_pos C hp j).ne'
  refine ⟨⟨fun j => h (nIdx C.σ j), C.k, C.k_pos, orthantChart C SD s, orthantDomain C SD s,
    isOpen_orthantDomain C SD s, hbox, ?_, ?_, orthantJac C SD s, measurable_orthantJac C SD hβ s,
    ?_, ?_, ?_, x, fun v => xiCoord_jointTangentialData P B hb hbB hB hW A' hAB v, ?_⟩,
    rfl, rfl, rfl, rfl, fun v u hu => ?_⟩
  · -- `C¹` on the orthant domain
    have han : AnalyticOnNhd ℝ (orthantChart C SD s) (orthantDomain C SD s) :=
      fun y hy => analyticAt_orthantChart C SD hφ s hy
    exact han.contDiffOn (isOpen_orthantDomain C SD s).uniqueDiffOn
  · -- injectivity on the positive box
    intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨p₁, hp₁, rfl⟩ := hy₁
    obtain ⟨p₂, hp₂, rfl⟩ := hy₂
    have hd₁ := hbox ⟨p₁, hp₁, rfl⟩
    have hd₂ := hbox ⟨p₂, hp₂, rfl⟩
    have hw₁ := inv_reflect_mem_V₀ C SD s hd₁
    have hw₂ := inv_reflect_mem_V₀ C SD s hd₂
    have hm₁ := C.monomialEval_ne_zero _ hw₁ fun j => SD.inv_apply_ne_zero hd₁ (hne p₁ hp₁ j)
    have hm₂ := C.monomialEval_ne_zero _ hw₂ fun j => SD.inv_apply_ne_zero hd₂ (hne p₂ hp₂ j)
    have h1 := hinj _ hw₁ _ hw₂ hm₁ hm₂ heq
    have h2 := SD.injOn_inv hd₁ hd₂ h1
    exact (splitReflect C.σ s).injective h2
  · -- nonnegativity of the Jacobian factor
    intro y hy
    rw [orthantJac_eq C SD s (hbox hy)]
    exact (orthantJacFun_pos C SD hβ s (hbox hy)).le
  · -- the Jacobian factorisation
    intro p hp
    set y := prodToPi C.σ p with hy
    have hd : y ∈ orthantDomain C SD s := hbox ⟨p, hp, rfl⟩
    set z := splitReflect C.σ s y with hz
    set w := SD.inv z with hw
    have hwV := inv_reflect_mem_V₀ C SD s hd
    rw [abs_det_fderiv_orthantChart C SD hφ s hd, C.det_eq w hwV, orthantJac_eq C SD s hd,
      prod_abs_pow_inv_nIdx C.σ (fun j => h (nIdx C.σ j)) j₀ (SD.apply_inv hd)
        (unitRoot_pos _ _ _ _)]
    have hzp : ∀ j, |z (nIdx C.σ j)| = p.2 j := fun j => by
      rw [hz, splitReflect_apply, abs_mul, abs_splitSgn, one_mul, hy, prodToPi_apply_nIdx,
        abs_of_pos (hp.2 j (mem_univ j)).1]
    rw [Finset.prod_congr rfl fun j _ => by rw [hzp j]]
    unfold orthantJacFun
    ring
  · -- the exact phase
    intro p hp
    have hd : prodToPi C.σ p ∈ orthantDomain C SD s := hbox ⟨p, hp, rfl⟩
    have hwV := inv_reflect_mem_V₀ C SD s hd
    change D.phase (translated φ y₀ _) = _
    rw [hphase _ hwV]
    have := phase_inv SD hβ (C.k_pos j₀) C.unit₀_pos (K := fun w => K (φ (w + y₀)))
      C.phase_eq hd
    change K (φ (_ + y₀)) = _
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Even.pow_abs (even_two_mul _), splitReflect_apply, abs_mul, abs_splitSgn, one_mul,
      Even.pow_abs (even_two_mul _), prodToPi_apply_nIdx]
  · -- the amplitude clause
    intro v u hu
    have hu' : ∀ j, |u j| ≤ b := fun j => by
      have := hu j (mem_univ j)
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    have hd : prodToPi C.σ (v.1, u) ∈ orthantDomain C SD s := hbox ⟨(v.1, u), ⟨v.2, hu⟩, rfl⟩
    have hwV := inv_reflect_mem_V₀ C SD s hd
    rw [hx, evalF_toEta_jointTangentialData P B hb hbB hB hW A' hAB hG hr₀ hBr₀ hB1 v hu']
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    unfold orthantAmp
    change _ = _ * D.obs (translated φ y₀ _)
    rw [hobs _ hwV]
    rfl
  · -- the amplitude clause on the closed two-sided box
    change evalF (toEta b (x v)) u = _
    rw [hx, evalF_toEta_jointTangentialData P B hb hbB hB hW A' hAB hG hr₀ hBr₀ hB1 v hu]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]

end Grammar
