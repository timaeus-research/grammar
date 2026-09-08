/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FamilyCoeffLipschitz

/-!
# Continuity of the canonical coefficient functionals on the data space (Stage S3 — A1)

Unit 272 (Astra #33, unit 3 of Programme S). **Headline XXXIV**: the paper-facing canonical
coefficient `C_{μ,j} = dataBoxCoeff n h k β b · μ j` — the coefficient of `N^{-μ} (log N)^j` in the
Taylor-tree expansion of the original box integral `Z(N; ξ, η)` — is Lipschitz on every ball of
the weighted-ℓ¹ data space `E_b × E_b` (`taylorTree_coeff_lipschitzOn_ball`), hence continuous
(`continuous_taylorTree_coeff`) and Borel measurable, for every real `μ` and every `j`; finite
vectors of coefficients are continuous (`continuous_taylorTree_coeffVec`). This is a precise
sufficient replacement for the paper's cited-but-unstated `prop:convergence` (continuity of
`ξ ↦ C_{μ,m}(ξ)`), in the weighted-ℓ¹ topology at the box radius `b`; the identification with a
topology on `C^ω([0,b]^d)` is not claimed. The Lipschitz constant on the ball of radius `R` is
`dataLipConst = b^{|h|+d} (b^{2|k|})^{-μ} (∑_{q=j}^{d-1} C(q,j) |log b^{2|k|}|^{q-j}) · 2 familyLipConst`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The Lipschitz constant of the canonical box coefficient on the data ball of radius `R`. -/
noncomputable def dataLipConst (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
    (∑ q ∈ Finset.Ico j (n + 1), (q.choose j : ℝ) * |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j)) *
    (2 * familyLipConst n k β μ R)

theorem dataLipConst_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (j : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ dataLipConst n h k β b μ j R := by
  unfold dataLipConst
  have h1 := familyLipConst_nonneg n k β hβ μ hR
  have h2 : 0 ≤ ∑ q ∈ Finset.Ico j (n + 1),
      (q.choose j : ℝ) * |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j) :=
    Finset.sum_nonneg fun q _ => by positivity
  have h3 : 0 ≤ (b ^ (2 * ∑ i, k i)) ^ (-μ) := Real.rpow_nonneg (by positivity) _
  positivity

/-- The unit-box coefficients of the raw coordinates are Lipschitz on data balls. -/
theorem abs_familySpectralCoeff_coord_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (μ : ℝ)
    (q : ℕ) :
    |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q -
        familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q| ≤
      familyLipConst n k β μ R * (2 * ‖y - x‖) := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have h := abs_familySpectralCoeff_sub_le n h k hk β hβ (absSummable_xiCoord x)
    (absSummable_xiCoord y) (absSummable_etaCoord x) (absSummable_etaCoord y)
    ((mass_xiCoord_le x).trans hx) ((mass_xiCoord_le y).trans hy) ((mass_etaCoord_le x).trans hx)
    ((mass_etaCoord_le y).trans hy) μ q
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (familyLipConst_nonneg n k β hβ μ hR0))
  have h1 : mass (xiCoord y - xiCoord x) ≤ ‖y - x‖ := by
    have := mass_xiCoord_sub_le y x
    simpa [Pi.sub_def] using this
  have h2 : mass (etaCoord y - etaCoord x) ≤ ‖y - x‖ := by
    have := mass_etaCoord_sub_le y x
    simpa [Pi.sub_def] using this
  linarith

/-- **Headline XXXIV (quantitative form)**: the canonical box coefficient is Lipschitz on the
data ball of radius `R`. -/
theorem abs_dataBoxCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |dataBoxCoeff n h k β b y μ j - dataBoxCoeff n h k β b x μ j| ≤
      dataLipConst n h k β b μ j R * ‖y - x‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  rw [dataBoxCoeff_eq n h k β hb, dataBoxCoeff_eq n h k β hb]
  set P := b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) with hP
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  set ℓ := Real.log (b ^ (2 * ∑ i, k i)) with hℓ
  set L := familyLipConst n k β μ R with hL
  have hL0 : 0 ≤ L := familyLipConst_nonneg n k β hβ μ hR0
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hP0]
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q * (q.choose j : ℝ) * ℓ ^ (q - j) -
        familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q * (q.choose j : ℝ) *
          ℓ ^ (q - j)| ≤
      (q.choose j : ℝ) * |ℓ| ^ (q - j) * (L * (2 * ‖y - x‖)) := by
    intro q _
    rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have := abs_familySpectralCoeff_coord_sub_le n h k hk β hβ hx hy μ q
    calc |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q -
            familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q| *
          (q.choose j : ℝ) * |ℓ| ^ (q - j)
        ≤ L * (2 * ‖y - x‖) * (q.choose j : ℝ) * |ℓ| ^ (q - j) := by
          gcongr
      _ = _ := by ring
  refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hterm)) hP0).trans ?_
  rw [← Finset.sum_mul]
  unfold dataLipConst
  rw [← hP, ← hℓ, ← hL]
  apply le_of_eq
  ring

/-- **Headline XXXIV**: the canonical coefficient map is Lipschitz on every closed data ball. -/
theorem taylorTree_coeff_lipschitzOn_ball (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (dataLipConst n h k β b μ j R))
      (fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hy' : ‖y‖ ≤ R := by simpa using hy
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx'
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (dataLipConst_nonneg n h k β hβ hb μ j hR0)]
  exact abs_dataBoxCoeff_sub_le n h k hk β hβ hb hy' hx' μ j

/-- **Headline XXXIV**: the canonical coefficient map is continuous on the data space (the
paper's `prop:convergence`, in the weighted-ℓ¹ topology). -/
theorem continuous_taylorTree_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Continuous fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : Metric.closedBall (0 : DataSpace (n + 1)) (‖x‖ + 1) ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp)
  exact (taylorTree_coeff_lipschitzOn_ball n h k hk β hβ hb μ j (‖x‖ + 1)).continuousOn.continuousAt
    hmem

theorem measurable_taylorTree_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Measurable fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j :=
  (continuous_taylorTree_coeff n h k hk β hβ hb μ j).measurable

/-- A finite vector of canonical coefficients `(C_{μ_i, j_i})_i`. -/
noncomputable def dataCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {m : ℕ}
    (F : Fin m → ℝ × ℕ) (x : DataSpace (n + 1)) : Fin m → ℝ :=
  fun i => dataBoxCoeff n h k β b x (F i).1 (F i).2

/-- **Headline XXXIV (finite vectors)**: every finite vector of canonical coefficients is
continuous on the data space. -/
theorem continuous_taylorTree_coeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) :
    Continuous (dataCoeffVec n h k β b F) :=
  continuous_pi fun i => continuous_taylorTree_coeff n h k hk β hβ hb (F i).1 (F i).2

theorem measurable_taylorTree_coeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) :
    Measurable (dataCoeffVec n h k β b F) :=
  (continuous_taylorTree_coeffVec n h k hk β hβ hb F).measurable

end Grammar
