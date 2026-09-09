/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorDraw

/-!
# Quenched convergence and stable convergence to the random kernel

For random phases `X_m → X` almost surely in `C(K, ℝ)`, the posterior laws converge almost surely,
`Q_{N_m}(ext X_m(ω)) ⇒ Q̃(ext X(ω))` (`posteriorMap_tendsto_ae`: one exceptional null set for all
observables at once, from the continuous convergence of the posterior laws).

If moreover `Z_m` are posterior draws in the integrated test form — for the bounded measurable
environment variable `H` and the bounded continuous test `g`,
`E[H g(Z_m)] = E[H ∫ g dQ_{N_m}(ext X_m)]` — then `E[H g(Z_m)] → E[H ∫ g dQ̃(ext X)]`
(`randomField_stable_tendsto`): stable convergence of the posterior draw to the random kernel
`Q̃(ext X)`, by pathwise weak convergence and dominated convergence.

Trap (recorded as the hypothesis): knowing the conditional law of `Z_m` given `X_m` alone does not
give the integrated identity for an arbitrary environment variable `H`; the hypothesis is the
full-environment conditional sampling identity for the `H` at hand.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open BoundedContinuousFunction

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (X : ℕ → Ω → C(PhaseDomain n, ℝ)) (X₀ : Ω → C(PhaseDomain n, ℝ))
  (hX : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (X₀ ω)))

include hk hmin hatt hN1 hN hX in
/-- **Quenched convergence**: if `X_m → X` a.s. in `C(K, ℝ)`, then a.s. the posterior laws
converge weakly, `Q_{N_m}(ext X_m(ω)) ⇒ Q̃(ext X(ω))`. -/
theorem posteriorMap_tendsto_ae :
    ∀ᵐ ω ∂P, Tendsto (fun m => phaseJointLawP n h k (Nseq m) hβ.le hηc hηnn hW (X m ω)) atTop
      (𝓝 (limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW (X₀ ω))) := by
  filter_upwards [hX] with ω hω
  exact (continuouslyConverges_posteriorMap n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1
    hN).tendsto_seq id tendsto_id (fun m => X m ω) (X₀ ω) hω

include hk hmin hatt hN1 hN hX in
/-- **Stable convergence to the random kernel**: for a bounded measurable environment variable `H`
and posterior draws `Z_m` satisfying the integrated conditional-law identity
`E[H g(Z_m)] = E[H ∫ g dQ_{N_m}(ext X_m)]`, `E[H g(Z_m)] → E[H ∫ g dQ̃(ext X)]`. -/
theorem randomField_stable_tendsto (hXm : ∀ m, Measurable (X m)) {H : Ω → ℝ} (hHm : Measurable H)
    {C : ℝ} (hH : ∀ ω, |H ω| ≤ C) (g : (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)
    (Zd : ℕ → Ω → ℝ × (Fin (n + 1) → ℝ))
    (hcond : ∀ m, ∫ ω, H ω * g (Zd m ω) ∂P = ∫ ω, H ω *
      ∫ z, g z ∂(phaseJointLawP n h k (Nseq m) hβ.le hηc hηnn hW (X m ω) :
        Measure (ℝ × (Fin (n + 1) → ℝ))) ∂P) :
    Tendsto (fun m => ∫ ω, H ω * g (Zd m ω) ∂P) atTop
      (𝓝 (∫ ω, H ω * ∫ z, g z ∂(limitPosteriorMap n h k hk hβ hηc hηnn hmin hatt hW (X₀ ω) :
        Measure (ℝ × (Fin (n + 1) → ℝ))) ∂P)) := by
  simp_rw [hcond]
  refine tendsto_integral_of_dominated_convergence (fun _ => C * ‖g‖) (fun m => ?_)
    (integrable_const _) (fun m => Eventually.of_forall fun ω => ?_) ?_
  · exact (hHm.mul ((continuous_phaseJointLaw_integral n h k (Nseq m) hβ.le hηc hηnn hW
      g).measurable.comp (hXm m))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hH ω) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hH ω))
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_norm _ g
  · filter_upwards [posteriorMap_tendsto_ae n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN X X₀ hX]
      with ω hω
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hω g).const_mul (H ω)

end Grammar
