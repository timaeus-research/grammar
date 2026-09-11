/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductChartExtremalPair

/-!
# Nonnegative cell coefficients

Unit 5(a) of consult #78 (`tide-log/gpt6_bigpicture_v78.md`): the face integrand
`η(faceProj u) · residualWeight u` is nonnegative on the unit box when `η ≥ 0` on the closed cube
(`amplitudeCoeff_nonneg_of_closedCube`), so the box and scalar face coefficients are nonnegative
when the amplitude is nonnegative on the closed normal ball (`boxFaceCoeff_nonneg`,
`scalarBoxFaceCoeff_nonneg`), and a **scalar-unit cell's coefficient is nonnegative** when its base
weight is nonnegative a.e. and its amplitude is nonnegative on base × closed ball
(`ScalarUnitCell.coeff_nonneg`) — for EVERY ratio configuration, not only the all-minimal case.
Reflection preserves the closed ball (`reflect_mem_closedBall_iff`), so the orthant cells of a
symmetric cell inherit the nonnegativity (`ScalarUnitCell.reflected_coeff_nonneg`).

Non-claims: strict positivity is the all-minimal criterion of CCXXXIX; this unit only supplies
the nonnegativity of every tied coefficient needed for the positive total of the end-to-end theorem.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Nonnegativity of the face coefficients -/

theorem amplitudeCoeff_nonneg_of_closedCube {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) {η : (Fin d → ℝ) → ℝ} (hη : ∀ u ∈ closedCube d, 0 ≤ η u) :
    0 ≤ amplitudeCoeff h k l β η :=
  mul_nonneg (faceLeadConst_pos h k hk l β hl hβ).le (setIntegral_nonneg (measurableSet_unitBox d)
    fun u hu => mul_nonneg (hη _ (faceProj_mapsTo h k l hu)) (residualWeight_nonneg h k l u hu))

theorem smul_mem_closedBall_of_mem_closedCube {r : ℕ} {b : ℝ} (hb : 0 < b) {v : Fin r → ℝ}
    (hv : v ∈ closedCube r) : b • v ∈ Metric.closedBall (0 : Fin r → ℝ) b := by
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hb.le).2 fun i => ?_
  have hvi := hv i (mem_univ i)
  rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.le hvi.1)]
  exact mul_le_of_le_one_right hb.le hvi.2

theorem boxFaceCoeff_nonneg {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) {t : ℕ} (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) {l : ℝ}
    (hl : 0 < l) {z : Fin t → ℝ}
    (hA : ∀ u ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) b, 0 ≤ A z u) :
    0 ≤ boxFaceCoeff n h k β b A l z := by
  unfold boxFaceCoeff
  refine mul_nonneg (mul_nonneg (pow_nonneg hb.le _) (Real.rpow_pos_of_pos (pow_pos hb _) _).le) ?_
  exact amplitudeCoeff_nonneg_of_closedCube h k hk hl hβ fun v hv =>
    hA _ (smul_mem_closedBall_of_mem_closedCube hb hv)

theorem scalarBoxFaceCoeff_nonneg {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {t : ℕ} (q : (Fin t → ℝ) → ℝ) (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) {l : ℝ}
    (hl : 0 < l) {z : Fin t → ℝ} (hq : 0 < q z)
    (hA : ∀ u ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) b, 0 ≤ A z u) :
    0 ≤ scalarBoxFaceCoeff n h k b q A l z :=
  mul_nonneg (Real.rpow_pos_of_pos hq _).le (boxFaceCoeff_nonneg h k hk one_pos hb A hl hA)

/-! ### Nonnegative cell coefficients -/

namespace ScalarUnitCell

variable {t : ℕ} (c : ScalarUnitCell t)

/-- **A cell's coefficient is nonnegative** when its base weight is nonnegative a.e. and its
amplitude is nonnegative on base × closed ball. -/
theorem coeff_nonneg (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ z ∈ c.base, ∀ u ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 ≤ c.A z u) :
    0 ≤ c.coeff := by
  have hbaseM : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
  unfold ScalarUnitCell.coeff
  refine setIntegral_nonneg_of_ae_restrict ?_
  filter_upwards [hβ, (ae_restrict_iff' hbaseM).2 (Eventually.of_forall fun z (hz : z ∈ c.base) =>
    hz)] with z h1 hz
  exact mul_nonneg h1 (scalarBoxFaceCoeff_nonneg c.h c.k c.k_pos c.b_pos c.q c.A c.lam_pos
    (c.q_pos z hz) (hA z hz))

theorem reflect_mem_closedBall_iff {r : ℕ} (σ : Fin r → Bool) {b : ℝ} (hb : 0 ≤ b)
    (n : Fin r → ℝ) : reflect σ n ∈ Metric.closedBall (0 : Fin r → ℝ) b ↔
      n ∈ Metric.closedBall (0 : Fin r → ℝ) b := by
  simp only [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hb, Real.norm_eq_abs, reflect,
    abs_mul, abs_sgn', one_mul]

/-- The orthant cells of a symmetric cell inherit nonnegativity. -/
theorem reflected_coeff_nonneg (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ z ∈ c.base, ∀ u ∈ Metric.closedBall (0 : Fin (c.n + 1) → ℝ) c.b, 0 ≤ c.A z u)
    (σ : Fin (c.n + 1) → Bool) : 0 ≤ (c.reflected σ).coeff :=
  (c.reflected σ).coeff_nonneg hβ fun z hz u hu =>
    hA z hz _ ((reflect_mem_closedBall_iff σ c.b_pos.le u).2 hu)

end ScalarUnitCell

end Grammar
