/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceDistribution

/-!
# The quantitative bound on the renormalised functionals (consult #124 §5.1)

`|renormFunctional D h k p β b J a μ q U| ≤ renormConst h k p β b J a μ q · 2^{∑p} · M_D · M_U`
whenever `RectBound D (2p) b M_D` and `RectBound U p b M_U`: the renormalised functional of the
density `D` applied to `U` is controlled by the mixed derivatives of `U` of orders `≤ p` on the
closed box, with a constant depending only on the engine data. The proof is the one of the
engine's coefficient bound (CDXIII): each face integral is bounded through `faceAmp_bound` and the
absolute majorant `faceMajorant`, the product `∂^{m−a}_J D · U` through the Leibniz bound
`RectBound.mul`, and the normal derivatives of the density through `pdMulti_add` (orders `≤ 2p`).
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {h k p : Fin d → ℕ} {β b μ : ℝ}

theorem le_of_mem_idxL {l : List (Fin d)} {m : Fin d → ℕ} (hm : m ∈ idxL p l) (i : Fin d) :
    m i ≤ p i := by
  have := (Fintype.mem_piFinset.1 hm) i
  by_cases hi : i ∈ l
  · simp only [hi, if_true, Finset.mem_range] at this
    exact this.le
  · simp only [hi, if_false, Finset.mem_singleton] at this
    rw [this]
    exact Nat.zero_le _

/-- The bound constant of the renormalised functional `renormFunctional … J a μ q`. -/
noncomputable def renormConst (h k p : Fin d → ℕ) (β b : ℝ) (J : Finset (Fin d)) (a : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ (idxL p (lJ J)).filter (fun m => ∀ i, a i ≤ m i), faceW J (m - a) *
    ∑ j ∈ Finset.Ico q (DJ J + 1), |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q) *
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) *
        faceMajorant (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
          (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q))

theorem renormConst_nonneg (h k p : Fin d → ℕ) (β b : ℝ) (J : Finset (Fin d)) (a : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : 0 ≤ renormConst h k p β b J a μ q :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (faceW_nonneg _ _) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (faceMajorant_nonneg _ _ _ _ _ _)))

/-- The normal derivatives of the density inherit a rectangular bound of doubled depth. -/
theorem rectBound_pdMulti_lJ {D : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) {J : Finset (Fin d)}
    {m : Fin d → ℕ} (hm : m ∈ idxL p (lJ J)) {MD : ℝ} (hD2 : RectBound D (fun i => 2 * p i) b MD) :
    RectBound (pdMulti m (lJ J) D) p b MD := by
  intro β' hβ' v hv
  rw [pdMulti_lJ_eq_finRange hm hD, pdMulti_add hD]
  refine hD2 _ (fun i => ?_) v hv
  have := le_of_mem_idxL hm i
  have := hβ' i
  simp only [Pi.add_apply]
  omega

/-- ★★ **The quantitative bound on the renormalised functional.** -/
theorem abs_renormFunctional_le {D U : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hU : ContDiff ℝ ∞ U)
    (hb : 0 < b) (hp0 : ∀ i, 0 < p i) (hμ : ∀ i, 2 * (k i : ℝ) * μ < p i + h i + 1)
    (J : Finset (Fin d)) (a : Fin d → ℕ) (q : ℕ) {MD MU : ℝ}
    (hD2 : RectBound D (fun i => 2 * p i) b MD) (hU1 : RectBound U p b MU) :
    |renormFunctional D h k p β b J a μ q U| ≤
      renormConst h k p β b J a μ q * (2 ^ (∑ i, p i) * MD * MU) := by
  have hMD : 0 ≤ MD := hD2.nonneg hb.le
  have hMU : 0 ≤ MU := hU1.nonneg hb.le
  have hM : 0 ≤ 2 ^ (∑ i, p i) * MD * MU := by positivity
  unfold renormFunctional renormConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm' : m ∈ idxL p (lJ J) := (Finset.mem_filter.1 hm).1
  have hma : m - a ∈ idxL p (lJ J) := mem_idxL_of_le hm' fun i => Nat.sub_le _ _
  set F : (Fin d → ℝ) → ℝ := fun v => pdMulti (m - a) (lJ J) D v * U v with hF
  have hFsm : ContDiff ℝ ∞ F := (contDiff_pdMulti hD _ _).mul hU
  have hFb : RectBound F p b (2 ^ (∑ i, p i) * MD * MU) :=
    RectBound.mul (contDiff_pdMulti hD _ _) hU hb.le (rectBound_pdMulti_lJ hD hma hD2) hU1
  rw [abs_mul, abs_of_nonneg (faceW_nonneg _ _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (faceW_nonneg _ _)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hGM : ∀ w ∈ box {i // ¬ inJ J i} b, |faceAmp p J F 0 w| ≤
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * (2 ^ (∑ i, p i) * MD * MU)) *
        mono (fun i : {i // ¬ inJ J i} => p i) w := fun w hw =>
    faceAmp_bound p J hFsm hb hp0 hFb (zero_mem_idxL p hp0 (lJ J)) hw
  have hint := abs_faceCoeffInt_le (ι := {i // ¬ inJ J i}) hb
    (continuous_faceAmp p J hFsm 0).aestronglyMeasurable hGM
    (fun i => face_convergence hμ J i) (j - q)
  rw [abs_mul, abs_mul, Nat.abs_cast]
  calc |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q : ℝ) *
        |faceCoeffInt (faceAmp p J F 0) (fun i : {i // ¬ inJ J i} => h i)
          (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)|
      ≤ |faceCoef k β b J (fun i => m i + h i) μ j| * (j.choose q : ℝ) *
        (((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * (2 ^ (∑ i, p i) * MD * MU)) *
          faceMajorant (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
            (fun i : {i // ¬ inJ J i} => 2 * k i) b μ (j - q)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

end SmoothEngine

end Grammar
