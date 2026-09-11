/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.PopulationDataBridge
import Grammar.MonomialAmplitudeAsymptotic

/-!
# Scalar multiples of data-space elements

Linearity of the coordinates, the box families, the evaluation and the face functional under
scalar multiplication of a data-space element: `xiCoord (c • x) = c • xiCoord x`,
`toEta b (c • x) = c • toEta b x`, `evalF (c • η) u = c * evalF η u`,
`dataAmplitude (c • x) = c • dataAmplitude x`, `amplitudeCoeff … (c • η) = c * amplitudeCoeff … η`.
Used for the tangential Jacobian weights of the orthant charts (the datum of a piece is a continuous
scalar weight times the datum of the unweighted amplitude).
-/

open MeasureTheory Set

namespace Grammar

open CoeffFamily

variable {d : ℕ}

theorem DataSpace.smul_apply (c : ℝ) (x : DataSpace d) (γ : (Fin d → ℕ) ⊕ (Fin d → ℕ)) :
    (c • x) γ = c * x γ := by
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem xiCoord_smul (c : ℝ) (x : DataSpace d) : xiCoord (c • x) = c • xiCoord x := by
  funext γ
  simp [xiCoord, DataSpace.smul_apply]

theorem etaCoord_smul (c : ℝ) (x : DataSpace d) : etaCoord (c • x) = c • etaCoord x := by
  funext γ
  simp [etaCoord, DataSpace.smul_apply]

theorem toEta_smul (b c : ℝ) (x : DataSpace d) : toEta b (c • x) = c • toEta b x := by
  funext γ
  simp only [toEta, DataSpace.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem evalF_smul (c : ℝ) (η : CoeffFamily d) (u : Fin d → ℝ) :
    evalF (c • η) u = c * evalF η u := by
  unfold evalF
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem dataAmplitude_smul (c : ℝ) (x : DataSpace d) (u : Fin d → ℝ) :
    dataAmplitude (c • x) u = c * dataAmplitude x u := by
  unfold dataAmplitude
  rw [etaCoord_smul, evalF_smul]

theorem amplitudeCoeff_smul (h k : Fin d → ℕ) (l β c : ℝ) (η : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff h k l β (fun u => c * η u) = c * amplitudeCoeff h k l β η := by
  unfold amplitudeCoeff
  have hint : ∫ u in unitBox d, (fun u => c * η u) (faceProj h k l u) * residualWeight h k l u =
      c * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    ring
  rw [hint]
  ring

end Grammar
