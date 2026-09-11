/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.DivisorFreePieces

/-!
# Integrating fibrewise leading terms over a base

Module 3 of the adapted-density programme (`tide-log/gpt6_bigpicture_v75.md`): a family of
kernels `L_N(z)` indexed by the inverse temperature, each with a leading-term certificate
`L_N(z) / (N^{-λ} (log N)^k) → ℓ(z)` at a common pair `(λ, k)`, together with an **eventual
normalised domination** `|L_N(z)| / (N^{-λ} (log N)^k) ≤ G(z)` a.e. for all large `N`, integrates
against a
merely measurable base weight `β` to a certificate for `∫ β(z) L_N(z) dz` with coefficient
`∫ β(z) ℓ(z) dz` (`hasLeadingTerm_integral_of_dominated_kernel`); the quantifier order — an eventual
range of `N` with an a.e. bound for each such `N` — is the one dominated convergence needs. The
restricted form over a measurable base `B` is `hasLeadingTerm_setIntegral_of_dominated_kernel`,
and `hasLeadingTerm_integral_of_uniform_bound` takes a bound uniform in `z` with `β` integrable.

This is the routine half of the adapted-density programme: the substantive input — the
prescribed-box uniform Mellin kernel asymptotics with its face coefficient — is supplied
separately as the certificate and domination hypotheses.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

section Integrated

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {lam : ℝ} {k : ℕ}

/-- **Integrating fibrewise leading terms**: certificates for the kernels `L_N(z)` at a common pair,
an eventual normalised domination `|L_N(z)| / scale(N) ≤ G(z)` a.e. for large `N`, and
`|β| · G` integrable give the certificate for `∫ β L_N` with coefficient `∫ β ℓ`. -/
theorem hasLeadingTerm_integral_of_dominated_kernel {L : ℝ → α → ℝ} {ℓ β G : α → ℝ}
    (hmeas : ∀ᶠ N in atTop, AEStronglyMeasurable (fun z => β z * L N z) μ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => L N z / powLogScale lam k N) atTop (𝓝 (ℓ z)))
    (hbound : ∀ᶠ N in atTop, ∀ᵐ z ∂μ, |L N z / powLogScale lam k N| ≤ G z)
    (hG : Integrable (fun z => |β z| * G z) μ) :
    HasLeadingTerm (fun N => ∫ z, β z * L N z ∂μ) (∫ z, β z * ℓ z ∂μ) lam k := by
  unfold HasLeadingTerm
  simp_rw [← integral_div]
  have hmeas' : ∀ᶠ N in atTop,
      AEStronglyMeasurable (fun z => β z * L N z / powLogScale lam k N) μ :=
    hmeas.mono fun N hN => (hN.mul_const (powLogScale lam k N)⁻¹).congr
      (Eventually.of_forall fun z => (div_eq_mul_inv _ _).symm)
  refine tendsto_integral_filter_of_dominated_convergence (fun z => |β z| * G z) hmeas'
    (hbound.mono fun N hN => hN.mono fun z hz => ?_) hG (hlim.mono fun z hz => ?_)
  · rw [Real.norm_eq_abs, mul_div_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  · refine (hz.const_mul (β z)).congr' (Eventually.of_forall fun N => ?_)
    simp only [mul_div_assoc]

/-- The restricted form over a measurable base `B`. -/
theorem hasLeadingTerm_setIntegral_of_dominated_kernel {B : Set α} {L : ℝ → α → ℝ}
    {ℓ β G : α → ℝ}
    (hmeas : ∀ᶠ N in atTop, AEStronglyMeasurable (fun z => β z * L N z) (μ.restrict B))
    (hlim : ∀ᵐ z ∂μ.restrict B, Tendsto (fun N => L N z / powLogScale lam k N) atTop (𝓝 (ℓ z)))
    (hbound : ∀ᶠ N in atTop, ∀ᵐ z ∂μ.restrict B, |L N z / powLogScale lam k N| ≤ G z)
    (hG : IntegrableOn (fun z => |β z| * G z) B μ) :
    HasLeadingTerm (fun N => ∫ z in B, β z * L N z ∂μ) (∫ z in B, β z * ℓ z ∂μ) lam k :=
  hasLeadingTerm_integral_of_dominated_kernel hmeas hlim hbound hG

/-- The uniform-bound form: a bound `C` independent of `z` and an integrable base weight. -/
theorem hasLeadingTerm_integral_of_uniform_bound {L : ℝ → α → ℝ} {ℓ β : α → ℝ} {C : ℝ}
    (hmeas : ∀ᶠ N in atTop, AEStronglyMeasurable (fun z => β z * L N z) μ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => L N z / powLogScale lam k N) atTop (𝓝 (ℓ z)))
    (hbound : ∀ᶠ N in atTop, ∀ᵐ z ∂μ, |L N z / powLogScale lam k N| ≤ C)
    (hβ : Integrable β μ) :
    HasLeadingTerm (fun N => ∫ z, β z * L N z ∂μ) (∫ z, β z * ℓ z ∂μ) lam k :=
  hasLeadingTerm_integral_of_dominated_kernel hmeas hlim hbound (G := fun _ => C)
    (hβ.abs.mul_const C)

/-- The pointwise-certificate form: a certificate `HasLeadingTerm (L · z) (ℓ z)` for every `z`. -/
theorem hasLeadingTerm_integral_of_pointwise {L : ℝ → α → ℝ} {ℓ β G : α → ℝ}
    (hmeas : ∀ᶠ N in atTop, AEStronglyMeasurable (fun z => β z * L N z) μ)
    (hlim : ∀ z, HasLeadingTerm (fun N => L N z) (ℓ z) lam k)
    (hbound : ∀ᶠ N in atTop, ∀ᵐ z ∂μ, |L N z / powLogScale lam k N| ≤ G z)
    (hG : Integrable (fun z => |β z| * G z) μ) :
    HasLeadingTerm (fun N => ∫ z, β z * L N z ∂μ) (∫ z, β z * ℓ z ∂μ) lam k :=
  hasLeadingTerm_integral_of_dominated_kernel hmeas (Eventually.of_forall hlim) hbound hG

end Integrated

end Grammar
