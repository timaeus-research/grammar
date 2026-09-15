/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ParametricCoordinateDerivative
import Grammar.SmoothFaceDistribution

/-!
# Joint smoothness of the face amplitude of a parametrised smooth family

For a jointly smooth `G : B × ℝ^d → ℝ` the coordinate derivatives, coordinate Taylor remainders
and iterated remainders of the slices `v ↦ G (s, v)` are jointly smooth in `(s, v)`
(`contDiff_pdPow_slice`, `contDiff_pdMulti_slice`, `contDiff_coordRem_slice`,
`contDiff_remList_slice`), hence so is the face amplitude `(s, w) ↦ G_{J,m}(s; w)` of the slice
family (★ `contDiff_faceAmp_slice`). The engine of `ParametricCoordinateDerivative` identifies the
coordinate derivatives of a slice with iterated Fréchet derivatives of the joint function applied
to constant words; the remainder operators are finite combinations of such derivatives at the
coordinate projections `v ↦ v[i := 0]`, so the induction over the remainder list stays inside
jointly smooth functions. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {G : B × (Fin d → ℝ) → ℝ}

/-- An iterated Fréchet derivative of a smooth function applied to a constant word is smooth. -/
theorem contDiff_iteratedFDeriv_apply_const (hG : ContDiff ℝ ∞ G) (n : ℕ)
    (w : Fin n → B × (Fin d → ℝ)) : ContDiff ℝ ∞ fun z => iteratedFDeriv ℝ n G z w := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ n G) :=
    hG.iteratedFDeriv_right (m := ∞) (by rw [← WithTop.coe_natCast, ← WithTop.coe_add, top_add])
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => B × (Fin d → ℝ)) ℝ w).contDiff.comp h

theorem contDiff_pdPow_slice (hG : ContDiff ℝ ∞ G) (i : Fin d) (k : ℕ) :
    ContDiff ℝ ∞ fun z : B × (Fin d → ℝ) => pdPow i k (fun v => G (z.1, v)) z.2 := by
  have h : (fun z : B × (Fin d → ℝ) => pdPow i k (fun v => G (z.1, v)) z.2) =
      fun z => iteratedFDeriv ℝ k G z fun _ => ((0 : B), Pi.single i 1) :=
    funext fun z => pdPow_slice_eq_iteratedFDeriv hG i k z.1 z.2
  rw [h]
  exact contDiff_iteratedFDeriv_apply_const hG k _

theorem contDiff_pdMulti_slice (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (l : List (Fin d)) :
    ContDiff ℝ ∞ fun z : B × (Fin d → ℝ) => pdMulti m l (fun v => G (z.1, v)) z.2 := by
  have h : (fun z : B × (Fin d → ℝ) => pdMulti m l (fun v => G (z.1, v)) z.2) =
      fun z => iteratedFDeriv ℝ (wordLen m l) G z fun j => ((0 : B), coordWord m l j) :=
    funext fun z => pdMulti_slice_eq_iteratedFDeriv hG m l z.1 z.2
  rw [h]
  exact contDiff_iteratedFDeriv_apply_const hG _ _

theorem contDiff_coordRem_slice (hG : ContDiff ℝ ∞ G) (i : Fin d) (q : ℕ) :
    ContDiff ℝ ∞ fun z : B × (Fin d → ℝ) => coordRem i q (fun v => G (z.1, v)) z.2 := by
  unfold coordRem coordTaylor
  refine ContDiff.sub hG (ContDiff.sum fun j _ => ContDiff.mul
    (contDiff_const.mul (((contDiff_apply ℝ ℝ i).comp contDiff_snd).pow j)) ?_)
  exact (contDiff_pdPow_slice hG i j).comp
    (contDiff_fst.prodMk ((contDiff_setZero i).comp contDiff_snd))

theorem contDiff_remList_slice (p : Fin d → ℕ) (hG : ContDiff ℝ ∞ G) (l : List (Fin d)) :
    ContDiff ℝ ∞ fun z : B × (Fin d → ℝ) => remList p l (fun v => G (z.1, v)) z.2 := by
  induction l with
  | nil => exact hG
  | cons i l ih =>
    exact contDiff_coordRem_slice (G := fun z => remList p l (fun v => G (z.1, v)) z.2) ih i (p i)

/-- ★ The face amplitude of a jointly smooth slice family is jointly smooth in the parameter and
the complementary coordinates. -/
theorem contDiff_faceAmp_slice (hG : ContDiff ℝ ∞ G) (p : Fin d → ℕ) (J : Finset (Fin d))
    (m : Fin d → ℕ) :
    ContDiff ℝ ∞ fun z : B × ({i // ¬ inJ J i} → ℝ) =>
      faceAmp p J (fun v => G (z.1, v)) m z.2 := by
  have hrem := contDiff_remList_slice p (contDiff_pdMulti_slice hG m (lJ J)) (lK J)
  exact hrem.comp (contDiff_fst.prodMk ((contDiff_glue_zero J).comp contDiff_snd))

end SmoothEngine

end Grammar
