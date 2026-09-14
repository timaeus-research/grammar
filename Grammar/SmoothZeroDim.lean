/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothGeneral

/-!
# Regression: the smooth-amplitude expansion in dimension zero (consult #117 §8)

For `d = 0` the box `(0,b]^0` is the one-point space, `volume` is the Dirac mass and every empty
monomial is `1`, so the smooth-amplitude integral is the single exponential
`F(∗) · e^{−Nβ}` (`smoothIntegral_zeroDim`). It is `o(N^{−L})` for every `L`, hence a cutoff
expansion with the ZERO coefficient system (`cutoffExpansion_zero_zeroDim`), and the canonical
coefficients vanish identically (`smoothCoeff_zeroDim`, directly from the face sum over the empty
face; `smoothCoeff_zeroDim_of_unique` recovers the lattice part by canonicity). Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable (F : (Fin 0 → ℝ) → ℝ) (h k : Fin 0 → ℕ) (β b : ℝ)

/-- The point of the zero-dimensional coordinate space. -/
def pt0 : Fin 0 → ℝ := fun i => Fin.elim0 i

theorem box_zeroDim : box (Fin 0) b = univ := by
  ext x
  simp [box]

/-- ★ **The zero-dimensional smooth-amplitude integral** is the single exponential
`F(∗) · e^{−Nβ}`. -/
theorem smoothIntegral_zeroDim (N : ℝ) :
    smoothIntegral F h k β b N = F (fun i => Fin.elim0 i) * Real.exp (-(N * β)) := by
  unfold smoothIntegral
  rw [box_zeroDim, Measure.restrict_univ, Measure.volume_pi_eq_dirac (fun i => Fin.elim0 i),
    integral_dirac]
  simp [mono]

/-- The exponential `e^{−Nβ}` is eventually bounded by `N^{−L}`, for `β > 0` and every `L`. -/
theorem exp_neg_mul_le_rpow_neg (hβ : 0 < β) (L : ℝ) :
    ∀ᶠ N : ℝ in atTop, Real.exp (-(N * β)) ≤ N ^ (-L) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero L β hβ).eventually
    (eventually_le_nhds one_pos)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  rw [Real.rpow_neg hN0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hN0 L), mul_comm]
  have : -β * N = -(N * β) := by ring
  rwa [this] at hN

/-- ★ The zero-dimensional integral has the cutoff expansion with the ZERO coefficient system:
it is `o(N^{−L})` for every `L`. -/
theorem cutoffExpansion_zero_zeroDim (hβ : 0 < β) :
    CutoffExpansion (Qamb k) 0 (smoothIntegral F h k β b) fun _ _ => 0 := by
  intro L _
  refine ⟨|F (fun i => Fin.elim0 i)|, ?_⟩
  filter_upwards [exp_neg_mul_le_rpow_neg β hβ L] with N hN
  rw [smoothIntegral_zeroDim]
  simp only [absSpectralSum, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero, pow_zero,
    mul_one, abs_mul, Real.abs_exp]
  exact mul_le_mul_of_nonneg_left hN (abs_nonneg _)

/-- ★ **The canonical coefficients vanish in dimension zero**: the face sum runs over the empty
face only, whose face coefficients are `0`. -/
theorem smoothCoeff_zeroDim (μ : ℝ) (q : ℕ) : smoothCoeff F h k β b μ q = 0 := by
  unfold smoothCoeff smoothCoeffAtDepth
  refine Finset.sum_eq_zero fun x _ => ?_
  have hJ : x.1 = ∅ := Finset.eq_empty_of_isEmpty x.1
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [faceCoef, dif_neg (by rw [hJ]; exact Finset.not_nonempty_empty)]
  simp

/-- The lattice part of `smoothCoeff_zeroDim` by canonicity (`smoothCoeff_unique`) against the
zero coefficient system. -/
theorem smoothCoeff_zeroDim_of_unique (hF : ContDiff ℝ ∞ F) (hβ : 0 < β) (hb : 0 < b) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) : smoothCoeff F h k β b μ 0 = 0 :=
  (smoothCoeff_unique hF (fun i => Fin.elim0 i) hβ hb (cutoffExpansion_zero_zeroDim F h k β b hβ)
    hμ le_rfl).symm

end SmoothEngine

end Grammar
