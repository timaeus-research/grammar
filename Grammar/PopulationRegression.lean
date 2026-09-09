/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MixedRatioCounterexample
import Grammar.PopulationEquivalent

/-!
# Regression examples for the §3 rewrite (Astra #37 §6, unit 298)

Two examples in the mixed-ratio model `d = 2`, `h = (0,2)`, `k = (1,1)`, `β = 1` (ratios `1/2`,
`3/2`; `λ = 1/2`, `J = {0}`, `m = 1`; the face is `{u₀ = 0}` with residual weight `u₁`), which the
corrected §3 theorem must accommodate and the old one contradicts:

* **Face dependence** (`face_dependence`): the amplitudes `1` and `1 + u₁` have the same corner
  value `1` but different leading coefficients, `√π/4` and `5√π/12`. The general leading
  coefficient is the face integral, not a corner evaluation (this sharpens unit 206's
  `corner_evaluation_fails`).
* **Signed cancellation** (`signed_cancellation`): the amplitude `ψ = 1 − (3/2)u₁` has `ψ(0) = 1 ≠
0`
  yet its face functional vanishes, `∫₀¹ (1 − (3/2)v) v dv = 0`, so the first-candidate coefficient
  is zero although the deepest normal jet is nonzero. "Nonzero jet on the stratum ⇒ leading exponent
  `μ_I(φ)`" (`eq:lambda_I_f`) fails without a nonvanishing hypothesis on the face functional,
  and this happens within one chart, without cross-chart cancellation.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Grammar

namespace MixedCounterexample

/-- The signed amplitude `ψ(u) = 1 − (3/2) u₁`. -/
noncomputable def ψEx (u : Fin 2 → ℝ) : ℝ := 1 - 3 / 2 * u 1

theorem ψEx_zero : ψEx 0 = 1 := by simp [ψEx]

theorem continuous_ψEx : Continuous ψEx :=
  continuous_const.sub (continuous_const.mul (continuous_apply 1))

/-- The constant amplitude has face functional `√π/4`. -/
theorem amplitudeCoeff_one : amplitudeCoeff hEx kEx (1 / 2) 1 (fun _ => (1 : ℝ)) =
    Real.sqrt π / 4 := by
  rw [amplitudeCoeff_const hEx kEx hk (1 / 2) 1 hmin, mixedConst_eq, one_mul]

/-- **Face dependence**: `1` and `1 + u₁` agree at the corner but have different leading
coefficients. -/
theorem face_dependence :
    (fun _ : Fin 2 → ℝ => (1 : ℝ)) 0 = ηEx 0 ∧
      amplitudeCoeff hEx kEx (1 / 2) 1 (fun _ => (1 : ℝ)) ≠ amplitudeCoeff hEx kEx (1 / 2) 1 ηEx :=
by
  refine ⟨by simp [ηEx], ?_⟩
  rw [amplitudeCoeff_one, amplitudeCoeff_eq]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  intro h
  nlinarith

/-- **The face functional of `ψ = 1 − (3/2)u₁` vanishes.** -/
theorem amplitudeCoeff_ψEx : amplitudeCoeff hEx kEx (1 / 2) 1 ψEx = 0 := by
  have hA := face_moment_eq hEx kEx hk (1 / 2) 1 hmin (fun _ => 0) (fun _ _ => rfl)
  have hB := face_moment_eq hEx kEx hk (1 / 2) 1 hmin ![0, 1] (by
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => rfl, fun h => absurd h (by rw [ratio1]; norm_num)⟩)
  have hI : ∀ γ : Fin 2 → ℕ, IntegrableOn (fun u => (∏ i, faceProj hEx kEx (1 / 2) u i ^ γ i) *
      (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) (unitBox 2) := by
    intro γ
    refine (integrableOn_face_mul hEx kEx hk (1 / 2) hmin
      (fun x => faceLeadConst hEx kEx (1 / 2) 1 * ∏ i, x i ^ γ i)
      (continuous_const.mul (continuous_prod_pow γ))).congr_fun (fun u _ => ?_)
      (measurableSet_unitBox 2)
    ring
  have hsplit : amplitudeCoeff hEx kEx (1 / 2) 1 ψEx =
      (∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (fun _ : Fin 2 => 0) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) -
      3 / 2 * ∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (![0, 1] : Fin 2 → ℕ) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u) := by
    unfold amplitudeCoeff
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hI _) ((hI _).const_mul _)]
    refine setIntegral_congr_fun (measurableSet_unitBox 2) fun u _ => ?_
    simp only [ψEx, Fin.prod_univ_two, pow_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      pow_one, one_mul]
    ring
  rw [hsplit, hA, hB, mixedConst_shift_eq]
  have : monomialMixedConst (fun i => hEx i + (fun _ : Fin 2 => 0) i) kEx (1 / 2) 1 =
      monomialMixedConst hEx kEx (1 / 2) 1 := by
    congr 1
  rw [this, mixedConst_eq]
  ring

/-- **Signed cancellation**: a nonzero deepest normal jet with a vanishing first-candidate
coefficient, within a single chart. -/
theorem signed_cancellation : ψEx 0 ≠ 0 ∧ amplitudeCoeff hEx kEx (1 / 2) 1 ψEx = 0 :=
  ⟨by rw [ψEx_zero]; exact one_ne_zero, amplitudeCoeff_ψEx⟩

/-- The population integral of `ψ` is `o(N^{-1/2})`: the first candidate carries no term. -/
theorem ψEx_normalised_tendsto_zero :
    Tendsto (fun N : ℝ => (∫ x in unitBox 2,
        ψEx x * ((∏ i, x i ^ hEx i) * Real.exp (-(1 * N * ∏ i, x i ^ (2 * kEx i))))) /
        N ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hT := amplitude_tendsto 1 hEx kEx hk (1 / 2) 1 (by norm_num) one_pos hmin hatt ψEx
    continuous_ψEx
  rw [multCount_eq, Nat.sub_self, amplitudeCoeff_ψEx] at hT
  simpa using hT

end MixedCounterexample

end Grammar
