/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NormalJet
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Moment functionals, invariant pairing, and the fibre pushforward

The paper's moment tensors pair with the normal Taylor tensors.  Rather than building symmetric
tensor powers we use the dual of the space of `r`-forms: for a measure `η` on the normal space with
finite `r`-th moment, the **moment functional** is `A ↦ ∫ A(u,…,u) dη(u)`, a continuous linear
functional on `JetForm E r` of norm at most `∫ ‖u‖^r dη` (`momentFunctional`,
`norm_momentFunctional_le`).

* `moment_pairing_invariant`: the pairing `⟨Moment_η, D^r F(0)⟩` is invariant under every invertible
  linear change of fibre frame `L`, provided the measure is transported: with `η' = L_*η` and
  `F' = F ∘ L⁻¹`, `⟨Moment_{η'}, D^r F'(0)⟩ = ⟨Moment_η, D^r F(0)⟩`.  No condition on `L` is needed.
* `eq:pushforward_local`: for a chart density `c(v,u) ≥ 0` on `B × E` with fibre mass
  `C(v) = ∫ c(v,u) du`, the pushforward of `Ω = c dν⊗du` to the base is `C(v) dν` (`map_fst_omega`),
  and integrating against `Ω` is integrating the **normalised conditional fibre integrals**
  `∫ H(v,u) dκ_v`, `κ_v = C(v)⁻¹ c(v,·) du`, against `τ_*Ω` (`integral_omega_eq_condFibre`).  Fibres
  with `C(v) = 0` contribute nothing on both sides.

Normalisation warning (formalised by the statements): raw fibre moments containing `c` integrated
against `τ_*Ω` would count `C(v)` twice; the paper's `|μ_I|_v` must be read as the normalised
conditional fibre measure `κ_v`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

section Moment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}

theorem continuous_diagEval (A : JetForm E r) : Continuous fun u : E => A fun _ => u :=
  A.cont.comp (continuous_pi fun _ => continuous_id)

theorem norm_diagEval_le (A : JetForm E r) (u : E) : ‖A fun _ => u‖ ≤ ‖A‖ * ‖u‖ ^ r := by
  have := A.le_opNorm fun _ => u
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this

variable [MeasurableSpace E] [OpensMeasurableSpace E]

theorem integrable_diagEval (η : Measure E) (hr : Integrable (fun u => ‖u‖ ^ r) η)
    (A : JetForm E r) : Integrable (fun u => A fun _ => u) η :=
  (hr.const_mul ‖A‖).mono' (continuous_diagEval A).aestronglyMeasurable
    (Eventually.of_forall (norm_diagEval_le A))

/-- **The moment functional** `A ↦ ∫ A(u,…,u) dη`, a continuous linear functional on `r`-forms. -/
noncomputable def momentFunctional (η : Measure E) (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    JetForm E r →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun A => ∫ u, A (fun _ => u) ∂η
      map_add' := fun A B => integral_add (integrable_diagEval η hr A) (integrable_diagEval η hr B)
      map_smul' := fun c A => integral_smul c _ }
    (∫ u, ‖u‖ ^ r ∂η) fun A => by
      calc ‖∫ u, A (fun _ => u) ∂η‖ ≤ ∫ u, ‖A‖ * ‖u‖ ^ r ∂η :=
            norm_integral_le_of_norm_le (hr.const_mul _)
              (Eventually.of_forall (norm_diagEval_le A))
        _ = (∫ u, ‖u‖ ^ r ∂η) * ‖A‖ := by rw [integral_const_mul]; ring

@[simp] theorem momentFunctional_apply (η : Measure E) (hr : Integrable (fun u => ‖u‖ ^ r) η)
    (A : JetForm E r) : momentFunctional η hr A = ∫ u, A (fun _ => u) ∂η := rfl

theorem norm_momentFunctional_le (η : Measure E) (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    ‖momentFunctional η hr‖ ≤ ∫ u, ‖u‖ ^ r ∂η :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _) _

variable [BorelSpace E]

theorem integrable_norm_pow_map (L : E →L[ℝ] E) {η : Measure E}
    (hr : Integrable (fun u => ‖u‖ ^ r) η) : Integrable (fun u => ‖u‖ ^ r) (η.map L) := by
  have hmeas : AEStronglyMeasurable (fun u : E => ‖u‖ ^ r) (η.map L) :=
    (by fun_prop : Continuous fun u : E => ‖u‖ ^ r).aestronglyMeasurable
  rw [integrable_map_measure hmeas L.continuous.measurable.aemeasurable]
  refine (hr.const_mul (‖L‖ ^ r)).mono'
    (by fun_prop : Continuous fun u : E => ‖L u‖ ^ r).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm u) r

/-- **Invariance of the moment–jet pairing** under fibre-linear changes of frame with transported
measure: with `η' = L_*η` and `F' = F ∘ L⁻¹`, `⟨Moment_{η'}, D^r F'(0)⟩ = ⟨Moment_η, D^r F(0)⟩`. -/
theorem moment_pairing_invariant (L : E ≃L[ℝ] E) {η : Measure E}
    (hr : Integrable (fun u => ‖u‖ ^ r) η) {F : E → ℝ} (hF : ContDiff ℝ r F) :
    momentFunctional (η.map (L : E →L[ℝ] E)) (integrable_norm_pow_map (L : E →L[ℝ] E) hr)
        (normalJet (F ∘ L.symm) r) =
      momentFunctional η hr (normalJet F r) := by
  simp only [momentFunctional_apply]
  rw [integral_map (L : E →L[ℝ] E).continuous.measurable.aemeasurable
    (continuous_diagEval _).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [normalJet_comp_equiv hF L.symm, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp

end Moment

/-! ### The fibre pushforward `τ_*Ω = C(v) dν` and normalised conditional fibre measures -/

section Pushforward

variable {V E : Type*} [MeasurableSpace V] [MeasurableSpace E] (ν : Measure V)
  (vol : Measure E)

/-- The chart measure `Ω = c(v,u) dν(v) du` of a nonnegative density `c`. -/
noncomputable def omegaMeasure (c : V × E → ℝ) : Measure (V × E) :=
  (ν.prod vol).withDensity fun p => ENNReal.ofReal (c p)

/-- The fibre mass `C(v) = ∫ c(v,u) du` (as an extended nonnegative real). -/
noncomputable def fibreMass (c : V × E → ℝ) (v : V) : ℝ≥0∞ := ∫⁻ u, ENNReal.ofReal (c (v, u)) ∂vol

/-- The normalised conditional fibre measure `κ_v = C(v)⁻¹ c(v,·) du` (zero where `C(v) = 0`). -/
noncomputable def condFibre (c : V × E → ℝ) (v : V) : Measure E :=
  (fibreMass vol c v)⁻¹ • vol.withDensity fun u => ENNReal.ofReal (c (v, u))

variable {c : V × E → ℝ} (hc : Measurable c)
include hc

theorem integral_condFibre (hc0 : ∀ p, 0 ≤ c p) (v : V) (H : V × E → ℝ) :
    ∫ u, H (v, u) ∂condFibre vol c v =
      (fibreMass vol c v).toReal⁻¹ * ∫ u, c (v, u) * H (v, u) ∂vol := by
  unfold condFibre
  have hmv : Measurable fun u : E => ENNReal.ofReal (c (v, u)) :=
    (hc.comp measurable_prodMk_left).ennreal_ofReal
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    integral_withDensity_eq_integral_toReal_smul hmv
      (Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [ENNReal.toReal_ofReal (hc0 (v, u)), smul_eq_mul]

theorem integral_mul_eq_zero_of_fibreMass_eq_zero (hc0 : ∀ p, 0 ≤ c p) {v : V}
    (h0 : fibreMass vol c v = 0) (H : V × E → ℝ) : ∫ u, c (v, u) * H (v, u) ∂vol = 0 := by
  have hae : ∀ᵐ u ∂vol, ENNReal.ofReal (c (v, u)) = 0 :=
    (lintegral_eq_zero_iff (hc.comp measurable_prodMk_left).ennreal_ofReal).1 h0
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hae] with u hu
  have : c (v, u) = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 hu) (hc0 (v, u))
  simp [this]

variable [SFinite vol]

/-- **`eq:pushforward_local`, measure form**: the pushforward of `Ω` to the base is `C(v) dν`. -/
theorem map_fst_omega : (omegaMeasure ν vol c).map Prod.fst = ν.withDensity (fibreMass vol c) := by
  ext s hs
  have hm : Measurable fun p : V × E => ENNReal.ofReal (c p) := hc.ennreal_ofReal
  rw [Measure.map_apply measurable_fst hs, omegaMeasure, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_fst hs),
    lintegral_prod _ (hm.indicator (measurable_fst hs)).aemeasurable, ← lintegral_indicator hs]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ s
  · rw [indicator_of_mem hv]
    exact lintegral_congr fun u => indicator_of_mem (show (v, u) ∈ Prod.fst ⁻¹' s from hv) _
  · rw [indicator_of_notMem hv]
    refine (lintegral_congr fun u => ?_).trans lintegral_zero
    exact indicator_of_notMem (show (v, u) ∉ Prod.fst ⁻¹' s from hv) _

theorem measurable_fibreMass : Measurable (fibreMass vol c) :=
  hc.ennreal_ofReal.lintegral_prod_right'

variable [SFinite ν]

theorem integral_omega_eq_prod (hc0 : ∀ p, 0 ≤ c p) {H : V × E → ℝ}
    (hH : Integrable H (omegaMeasure ν vol c)) :
    ∫ p, H p ∂omegaMeasure ν vol c = ∫ v, ∫ u, c (v, u) * H (v, u) ∂vol ∂ν := by
  have hm : Measurable fun p : V × E => ENNReal.ofReal (c p) := hc.ennreal_ofReal
  have hlt : ∀ᵐ p ∂ν.prod vol, ENNReal.ofReal (c p) < ∞ :=
    Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  have hint : Integrable (fun p => (ENNReal.ofReal (c p)).toReal • H p) (ν.prod vol) :=
    (integrable_withDensity_iff_integrable_smul' hm hlt).1 hH
  unfold omegaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm hlt, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun v => integral_congr_ae
    (Eventually.of_forall fun u => ?_))
  simp only [ENNReal.toReal_ofReal (hc0 (v, u)), smul_eq_mul]

/-- **`eq:pushforward_local`, integral form**: integrating `H` against `Ω = c dν du` equals
integrating the normalised conditional fibre integrals `∫ H(v,u) dκ_v` against the base pushforward
`τ_*Ω = C(v) dν`; fibres with `C(v) = 0` contribute nothing on both sides. -/
theorem integral_omega_eq_condFibre (hc0 : ∀ p, 0 ≤ c p) (hfin : ∀ v, fibreMass vol c v ≠ ∞)
    {H : V × E → ℝ} (hH : Integrable H (omegaMeasure ν vol c)) :
    ∫ p, H p ∂omegaMeasure ν vol c =
      ∫ v, (∫ u, H (v, u) ∂condFibre vol c v) ∂ν.withDensity (fibreMass vol c) := by
  rw [integral_omega_eq_prod ν vol hc hc0 hH,
    integral_withDensity_eq_integral_toReal_smul (measurable_fibreMass vol hc)
      (Eventually.of_forall fun v => lt_top_iff_ne_top.2 (hfin v))]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [integral_condFibre vol hc hc0 v, smul_eq_mul]
  by_cases h0 : fibreMass vol c v = 0
  · rw [integral_mul_eq_zero_of_fibreMass_eq_zero vol hc hc0 h0, h0]; simp
  · rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, hfin v⟩), one_mul]

end Pushforward

end Grammar
