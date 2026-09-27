/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthTwo
import Grammar.GaussianProductZeta

/-!
# The Gaussian-prior deep linear network at every depth: the exact conditional reduction

For the normalised Gaussian prior on `ℝ^L` and the phase `K = (∏ W_i)²/2`, the partition function
`Z_L(N) = E exp(−N (∏ W_i)²/2)` reduces exactly, by the Gaussian integral in the last coordinate,
to a depth-`(L−1)` expectation without any Bessel function:

  `Z_{L+1}(N) = E[(1 + N (∏_{i<L} W_i)²)^{−1/2}]`  (★★★ `gaussLaplaceL_succ`),

the all-depth version of `Grammar.GaussianDepthTwo` (`L = 1` is `gaussLaplace2_eq_integral`).  The
zeta function of the phase, `ζ_K(s) = E K^{−s} = 2^s ζ_L(s)` (`gaussKZeta_eq`), has the leading
coefficient `(s − ½)^L ζ_K(s) → √2 (−1/√(2π))^L` (★★ `tendsto_pole_gaussK`), i.e.
`2^{−(L−1)/2} π^{−L/2}` up to the sign `(−1)^L` of the negative-moment variable — the population
prediction `Z_L(N) ~ (log N)^{L−1}/((L−1)! (2π)^{(L−1)/2} √N)` for the note's eq. (dln_gauss)
(Astra round-6 target 3; the asymptotic transfer at depth `L ≥ 3` remains a derivation).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The standard Gaussian density. -/
noncomputable def gaussDensity (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

theorem gaussDensity_nonneg (x : ℝ) : 0 ≤ gaussDensity x := by unfold gaussDensity; positivity

theorem continuous_gaussDensity : Continuous gaussDensity := by unfold gaussDensity; fun_prop

theorem integrable_gaussDensity : Integrable gaussDensity := by
  have := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).div_const (Real.sqrt (2 * Real.pi))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [gaussDensity]
  congr 2
  ring

/-- The depth-`L` Gaussian partition function with the normalised prior. -/
noncomputable def gaussLaplaceL (L : ℕ) (N : ℝ) : ℝ :=
  ∫ w : Fin L → ℝ, Real.exp (-N * (∏ i, w i) ^ 2 / 2) * ∏ i, gaussDensity (w i)

theorem continuous_prod_coord (L : ℕ) : Continuous fun w : Fin L → ℝ => ∏ i, w i :=
  continuous_finsetProd _ fun i _ => continuous_apply i

theorem continuous_prod_gaussDensity (L : ℕ) :
    Continuous fun w : Fin L → ℝ => ∏ i, gaussDensity (w i) :=
  continuous_finsetProd _ fun i _ => continuous_gaussDensity.comp (continuous_apply i)

theorem integrable_prod_gaussDensity (L : ℕ) :
    Integrable fun w : Fin L → ℝ => ∏ i, gaussDensity (w i) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun _ : Fin L => gaussDensity)
    fun _ => integrable_gaussDensity

theorem integrable_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun w : Fin L → ℝ =>
      Real.exp (-N * (∏ i, w i) ^ 2 / 2) * ∏ i, gaussDensity (w i) := by
  have hP := continuous_prod_coord L
  have hG := continuous_prod_gaussDensity L
  have h1 : Continuous fun w : Fin L → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2) :=
    Real.continuous_exp.comp (by fun_prop)
  refine (integrable_prod_gaussDensity L).mono' (h1.mul hG).measurable.aestronglyMeasurable ?_
  refine Eventually.of_forall fun w => ?_
  have hG0 : 0 ≤ ∏ i, gaussDensity (w i) := Finset.prod_nonneg fun i _ => gaussDensity_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left hG0
    (Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hN (sq_nonneg (∏ i, w i))]))

/-- **Bochner peel of the first coordinate, integrated last**:
`∫ F = ∫ b, ∫ a, F (a, b)` on `Fin (d+1) → ℝ`. -/
theorem integral_pi_succ_symm (d : ℕ) (F : (Fin (d + 1) → ℝ) → ℝ) (hF : Integrable F) :
    ∫ x, F x = ∫ b : Fin d → ℝ, ∫ a : ℝ, F (Fin.cons a b) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin d → ℝ))) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  simp only [hsymm]

/-- ★★★ **The exact conditional reduction at every depth**:
`Z_{L+1}(N) = E[(1 + N (∏_{i<L} W_i)²)^{−1/2}]` for `N ≥ 0`. -/
theorem gaussLaplaceL_succ (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL (L + 1) N =
      ∫ b : Fin L → ℝ, 1 / Real.sqrt (1 + N * (∏ i, b i) ^ 2) * ∏ i, gaussDensity (b i) := by
  unfold gaussLaplaceL
  rw [integral_pi_succ_symm L _ (integrable_gaussLaplaceL (L + 1) hN)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  have hc : 0 < 1 + N * (∏ i, b i) ^ 2 := by positivity
  have hpt : ∀ a : ℝ, Real.exp (-N * (∏ i, (Fin.cons a b : Fin (L + 1) → ℝ) i) ^ 2 / 2) *
      ∏ i, gaussDensity ((Fin.cons a b : Fin (L + 1) → ℝ) i) =
      (1 / Real.sqrt (2 * Real.pi) * ∏ i, gaussDensity (b i)) *
        Real.exp (-(1 + N * (∏ i, b i) ^ 2) * a ^ 2 / 2) := by
    intro a
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have e : Real.exp (-N * (a * ∏ i, b i) ^ 2 / 2) * Real.exp (-a ^ 2 / 2) =
        Real.exp (-(1 + N * (∏ i, b i) ^ 2) * a ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show gaussDensity a = Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi) from rfl]
    linear_combination (∏ i, gaussDensity (b i)) / Real.sqrt (2 * Real.pi) * e
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, integral_exp_cond hc,
    Real.sqrt_div' _ hc.le]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs1 : 0 < Real.sqrt (1 + N * (∏ i, b i) ^ 2) := Real.sqrt_pos.2 hc
  field_simp

/-- `gaussLaplaceL 1 N = gaussLaplace2`'s one-dimensional integrand: the depth-two case of the
reduction is `Grammar.GaussianDepthTwo`. -/
theorem gaussLaplaceL_one_succ {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL 2 N = ∫ b : Fin 1 → ℝ, 1 / Real.sqrt (1 + N * (∏ i, b i) ^ 2) *
      ∏ i, gaussDensity (b i) := gaussLaplaceL_succ 1 hN

/-! ### The zeta function of the phase and its leading coefficient -/

/-- `ζ_K(s) = E K^{−s}` for `K = (∏ W_i)²/2`. -/
noncomputable def gaussKZeta (L : ℕ) (s : ℂ) : ℂ :=
  ∫ w : Fin L → ℝ, (((∏ i, w i) ^ 2 / 2 : ℝ) : ℂ) ^ (-s) * ∏ i, ((gaussDensity (w i) : ℝ) : ℂ)

/-- `(1/2)^{−s} = 2^s`. -/
theorem half_cpow_neg (s : ℂ) : (((1 / 2 : ℝ) : ℂ)) ^ (-s) = (2 : ℂ) ^ s := by
  rw [show ((1 / 2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ by push_cast; ring,
    Complex.inv_cpow _ _ (by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg, inv_inv]

/-- ★★ `ζ_K(s) = 2^s ζ_L(s)`. -/
theorem gaussKZeta_eq (L : ℕ) (s : ℂ) : gaussKZeta L s = (2 : ℂ) ^ s * gaussProductZeta L s := by
  unfold gaussKZeta gaussProductZeta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  have hden : ∀ i, ((gaussDensity (w i) : ℝ) : ℂ) =
      ((Real.exp (-w i ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := fun i => rfl
  simp_rw [hden]
  rw [← mul_assoc]
  congr 1
  rcases eq_or_ne (∏ i, w i) 0 with hP | hP
  · rw [hP]
    rcases eq_or_ne s 0 with hs | hs
    · simp [hs]
    · rw [show ((0 : ℝ) ^ 2 / 2 : ℝ) = 0 by norm_num, abs_zero]
      push_cast
      rw [Complex.zero_cpow (neg_ne_zero.2 hs), Complex.zero_cpow (by
        exact mul_ne_zero (by norm_num) hs), mul_zero]
  · have hP2 : 0 < |∏ i, w i| := abs_pos.2 hP
    have h := Complex.mul_cpow_ofReal_nonneg (a := |∏ i, w i| ^ 2) (b := 1 / 2) (by positivity)
      (by norm_num) (-s)
    rw [show ((∏ i, w i) ^ 2 / 2 : ℝ) = |∏ i, w i| ^ 2 * (1 / 2) by rw [sq_abs]; ring,
      Complex.ofReal_mul, h, cpow_sq_ofReal hP2, half_cpow_neg, mul_comm,
      show 2 * -s = -2 * s by ring]

/-- ★★ **The leading coefficient of `ζ_K` at `½`**:
`(s − ½)^L · 2^s ζ_L(s) → √2 (−1/√(2π))^L` as `s → ½`. -/
theorem tendsto_pole_gaussK (L : ℕ) :
    Tendsto (fun s : ℂ => (s - 1 / 2) ^ L * ((2 : ℂ) ^ s * gaussZeta1Closed s ^ L))
      (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 (((Real.sqrt 2 : ℝ) : ℂ) * (-(1 / (Real.sqrt (2 * Real.pi) : ℂ))) ^ L)) := by
  have h1 := tendsto_pole_gaussZeta L
  have h2 : Tendsto (fun s : ℂ => (2 : ℂ) ^ s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 ((Real.sqrt 2 : ℝ) : ℂ)) := by
    rw [← two_cpow_half]
    exact (continuousAt_const.cpow continuousAt_id (Or.inl (by norm_num))).tendsto.mono_left
      nhdsWithin_le_nhds
  refine (h2.mul h1).congr' (Eventually.of_forall fun s => ?_)
  ring

end Grammar
