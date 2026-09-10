/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ResolutionTransport
import Grammar.MonomialRep
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Orthant reflection as a weighted measure identity

A resolution chart is a cube in all orthants; grammar's standard box is the positive orthant
`(0, b]^d`.  The coordinate reflection `y ↦ (s_i y_i)` with signs `|s_i| = 1` preserves Lebesgue
measure (`map_signReflect_volume`), fixes every even monomial `y^e` (`mono_signReflect_of_even`) and
turns `y^h` on the positive box into `|y|^h` on the reflected box: the weighted measure identity
`map_signReflect_weightedPosBox`.  With `map_withDensity_comp` this is a one-line consequence of the
Lebesgue invariance.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Grammar

open MonoRep

variable {d : ℕ}

/-- The coordinate reflection by signs `s`. -/
def signReflect (s : Fin d → ℝ) (y : Fin d → ℝ) : Fin d → ℝ := fun i => s i * y i

/-- The reflection as a linear map. -/
def signReflectLinear (s : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLin' (Matrix.diagonal s)

theorem reflectLinear_apply (s y : Fin d → ℝ) : signReflectLinear s y = signReflect s y := by
  funext i
  simp [signReflectLinear, signReflect, Matrix.mulVec_diagonal]

theorem measurable_signReflect (s : Fin d → ℝ) : Measurable (signReflect s) :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _

theorem signReflect_signReflect {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) (y : Fin d → ℝ) :
    signReflect s (signReflect s y) = y := by
  funext i
  have : s i * s i = 1 := by
    have h := hs i
    rcases abs_eq (zero_le_one' ℝ) |>.1 h with h1 | h1 <;> rw [h1] <;> norm_num
  simp only [signReflect]
  rw [← mul_assoc, this, one_mul]

theorem det_diagonal_abs_eq_one {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) :
    |(Matrix.diagonal s).det| = 1 := by
  rw [Matrix.det_diagonal, Finset.abs_prod]
  exact Finset.prod_eq_one fun i _ => hs i

/-- **Lebesgue measure is reflection invariant.** -/
theorem map_signReflect_volume {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) :
    (volume : Measure (Fin d → ℝ)).map (signReflect s) = volume := by
  have hdet : (Matrix.diagonal s).det ≠ 0 := by
    intro h; have := det_diagonal_abs_eq_one hs; rw [h, abs_zero] at this; exact zero_ne_one this
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hfun : ⇑(Matrix.toLin' (Matrix.diagonal s)) = signReflect s := funext (reflectLinear_apply s)
  rw [hfun] at h
  rw [h, abs_inv, det_diagonal_abs_eq_one hs, inv_one, ENNReal.ofReal_one, one_smul]

/-- Even monomials are reflection invariant. -/
theorem mono_signReflect_of_even {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) {e : Fin d → ℕ}
    (he : ∀ i, Even (e i)) (y : Fin d → ℝ) : mono e (signReflect s y) = mono e y := by
  unfold mono signReflect
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨k, hk⟩ := he i
  rw [hk, ← two_mul, pow_mul, pow_mul, mul_pow]
  have : s i ^ 2 = 1 := by rw [← sq_abs, hs i, one_pow]
  rw [this, one_mul]

/-- The absolute monomial `|y|^h`. -/
def absMono (h : Fin d → ℕ) (y : Fin d → ℝ) : ℝ := ∏ i, |y i| ^ h i

theorem absMono_signReflect {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) (h : Fin d → ℕ) (y : Fin d → ℝ) :
    absMono h (signReflect s y) = absMono h y := by
  unfold absMono signReflect
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_mul, hs i, one_mul]

theorem absMono_eq_mono_of_pos {h : Fin d → ℕ} {y : Fin d → ℝ} (hy : ∀ i, 0 ≤ y i) :
    absMono h y = mono h y := by
  unfold absMono mono
  exact Finset.prod_congr rfl fun i _ => by rw [abs_of_nonneg (hy i)]

theorem measurable_absMono (h : Fin d → ℕ) : Measurable (absMono h) :=
  Finset.measurable_prod _ fun i _ =>
    (continuous_abs.measurable.comp (measurable_pi_apply i) :
      Measurable fun y : Fin d → ℝ => |y i|).pow_const _

/-- The reflected box `signReflect s ⁻¹' B`. -/
def signReflectBox (s : Fin d → ℝ) (B : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := signReflect s ⁻¹' B

/-- **The orthant reflection identity**: the reflection pushes `y^h dy` on the positive box `B` to
`|y|^h dy` on the reflected box. -/
theorem map_signReflect_weightedPosBox {s : Fin d → ℝ} (hs : ∀ i, |s i| = 1) {B : Set (Fin d → ℝ)}
    (hB : MeasurableSet B) (hBpos : ∀ y ∈ B, ∀ i, 0 ≤ y i) (h : Fin d → ℕ) :
    ((volume.restrict (signReflectBox s B)).withDensity fun y => ENNReal.ofReal (absMono h y)).map
        (signReflect s) =
      (volume.restrict B).withDensity fun y => ENNReal.ofReal (mono h y) := by
  have hg : Measurable fun y : Fin d → ℝ => ENNReal.ofReal (absMono h y) :=
    ENNReal.measurable_ofReal.comp (measurable_absMono h)
  have hcomp : (fun y : Fin d → ℝ => ENNReal.ofReal (absMono h y)) =
      fun y => ENNReal.ofReal (absMono h (signReflect s y)) := by
    funext y; rw [absMono_signReflect hs]
  rw [hcomp, map_withDensity_comp _ (measurable_signReflect s) hg, signReflectBox,
    ← Measure.restrict_map (measurable_signReflect s) hB, map_signReflect_volume hs]
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hB]
  exact Eventually.of_forall fun y hy => by rw [absMono_eq_mono_of_pos (hBpos y hy)]

end Grammar
