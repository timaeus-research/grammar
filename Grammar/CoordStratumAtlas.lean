/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularGlobalExpansion

/-!
# The coordinate stratum of a chart as an analytic LCI stratum

In a hironaka chart the exceptional-divisor strata are coordinate planes. This file presents the
model coordinate plane `{x ∈ ℝ^{m+k} : stratumProj x = 0}` (the last `k` coordinates vanish) as a
`CompatibleAnalyticLCIAtlas` with a single chart (`coordStratumAtlas`: `G = stratumProj`, constant
Jacobian `stratumJ`), identifies its normal field with strucdual's (`coordStratumAtlas_normal`),
and transports strucdual's analytic tube of every radius to it (`coordStratumTube`) — the
resolved-space instance of the tubular strand's input data.
-/

open scoped Manifold ContDiff Matrix
open Set Function StrucDual.Geometry

namespace Grammar

section CoordStratum

variable (m k : ℕ)

/-- The model coordinate plane `{x : stratumProj x = 0} ⊆ ℝ^{m+k}`. -/
def coordPlaneModel : Set (Fin (m + k) → ℝ) := {x | stratumProj m k x = 0}

/-- `stratumProj` as a continuous linear map. -/
noncomputable def stratumProjCLM : (Fin (m + k) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  (stratumJ m k).mulVecLin.toContinuousLinearMap

theorem stratumProjCLM_apply (x : Fin (m + k) → ℝ) : stratumProjCLM m k x = stratumProj m k x := by
  change (stratumJ m k).mulVec x = stratumProj m k x
  funext j
  simp [Matrix.mulVec, dotProduct, stratumJ_apply, stratumProj]

/-- **The coordinate plane as an analytic LCI stratum**: one chart, `G = stratumProj`,
`J = stratumJ`. -/
noncomputable def coordStratumAtlas : CompatibleAnalyticLCIAtlas k (coordPlaneModel m k) where
  ι := Unit
  V _ := univ
  isOpen_V _ := isOpen_univ
  G _ := stratumProj m k
  J _ _ := stratumJ m k
  analyticAt_G _ p := by
    have h := (stratumProjCLM m k).analyticAt p
    refine h.congr (Filter.Eventually.of_forall fun x => stratumProjCLM_apply m k x)
  hJG _ p := by
    have h := (stratumProjCLM m k).hasFDerivAt (x := p)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (stratumProjCLM_apply m k
      x).symm)
  cover _ := ⟨(), mem_univ _⟩
  zero_iff := fun _ {_} _ => Iff.rfl
  fullRank := fun _ {_} _ _ => fullRowRank_stratumJ m k
  tangent _ := tangentSpaceOf (stratumJ m k)
  tangent_eq := fun _ {_} _ _ => rfl

theorem coordStratumAtlas_normal (x : Fin (m + k) → ℝ) :
    (coordStratumAtlas m k).normal x = normalSpaceOf (stratumJ m k) :=
  (normalSpaceOf_eq_orthogonalSubmodule_tangent (fullRowRank_stratumJ m k)).symm

/-- **strucdual's analytic tube of every radius**, for the atlas normal field. -/
theorem coordStratumTube (ε : ℝ) (hε : 0 < ε) :
    Nonempty (AnalyticNormalTubularChart (coordStratumAtlas m k).normal (coordPlaneModel m k)) := by
  have hN : (fun _ : Fin (m + k) → ℝ => normalSpaceOf (stratumJ m k)) =
      (coordStratumAtlas m k).normal := funext fun x => (coordStratumAtlas_normal m k x).symm
  have := stratum_tube m k ε hε
  rw [hN] at this
  exact this

end CoordStratum

end Grammar
