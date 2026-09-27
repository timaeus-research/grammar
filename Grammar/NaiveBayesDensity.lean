/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The fibre volume of the naive Bayes moment map: the product density and the `t`-integral

For Lebesgue measure on the rectangle `[−α, β] × [−γ, δ]` (all four positive) the pushforward
along `(η₁, η₂) ↦ η₁η₂` has the density `log⁺(βδ/z) + log⁺(αγ/z)` at `z > 0` and
`log⁺(βγ/|z|) + log⁺(αδ/|z|)` at `z < 0`, one logarithm per sign quadrant
(★★ `lintegral_rect_prod`: `∫_rect Ψ(η₁η₂) = ∫ Ψ(z) prodDensity(z) dz` for every measurable
`Ψ ≥ 0`; proof: Tonelli, the substitution `w = η₁η₂` on each `η₁`-slice via
`Real.map_volume_mul_left`, Tonelli again, and the fibre `{η₁ : z/η₁ ∈ [−γ, δ]} ∩ [−α, β]`
computed as two intervals, `prodFibre_pos`/`prodFibre_neg`, whose `∫ dη/|η|` are the logarithms).

For the two-leaf naive Bayes model at fixed means `λ = (λ₁, λ₂)` the moment map carries the
uniform prior to Lebesgue measure on the region `nbRegion λ` of `(t, (η₁, η₂))`, a rectangle
`[−αᵢ(t), βᵢ(t)]` in `η` over each `t ∈ (0,1)` (`nbLo`, `nbHi`), and the covariance is
`μ = t(1 − t)η₁η₂`.  ★★ `lintegral_nbRegion`: the pushforward along `μ` has the density

  `nbFibreDensity λ z = ∫₀¹ dt/(t(1 − t)) · prodDensity(α(t), β(t))(z/(t(1 − t)))`,

the one-dimensional integral (examples_slop eq. (nb_rho_integral)) whose closed form is
`2 log(M±/|z|) log(V/(M±|z|))`, the `log²` singularity that is the multiplicity three of the
model.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- `∫_a^b dx/x = log(b/a)` for `0 < a ≤ b`, as a lower integral. -/
theorem lintegral_Icc_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ x in Icc a b, ENNReal.ofReal x⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Icc a b) :=
    ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun x hx =>
      ne_of_gt (lt_of_lt_of_le ha hx.1))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => inv_nonneg.mpr (ha.le.trans hx.1))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]

/-- `∫_a^b dx/(−x) = log(a/b)` for `a ≤ b < 0`, as a lower integral. -/
theorem lintegral_Icc_neg_inv {a b : ℝ} (hb : b < 0) (hab : a ≤ b) :
    ∫⁻ x in Icc a b, ENNReal.ofReal (-x)⁻¹ = ENNReal.ofReal (Real.log (a / b)) := by
  have hint : IntegrableOn (fun x : ℝ => (-x)⁻¹) (Icc a b) := by
    refine ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.inv₀ continuousOn_neg fun x hx => ?_
    exact neg_ne_zero.mpr (ne_of_lt (hx.2.trans_lt hb))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc fun x hx =>
      inv_nonneg.mpr (neg_nonneg.mpr (hx.2.trans hb.le)))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have : ∫ x in a..b, (-x)⁻¹ = -∫ x in a..b, x⁻¹ := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; simp
  rw [this, integral_inv_of_neg (hab.trans_lt hb) hb, ← Real.log_inv, inv_div]

/-- The product-of-uniforms density of Lebesgue measure on `[−α, β] × [−γ, δ]` along
`(η₁, η₂) ↦ η₁η₂`. -/
noncomputable def prodDensity (α β γ δ z : ℝ) : ℝ≥0∞ :=
  if 0 < z then
    ENNReal.ofReal (max (Real.log (β * δ / z)) 0) + ENNReal.ofReal (max (Real.log (α * γ / z)) 0)
  else if z < 0 then
    ENNReal.ofReal (max (Real.log (β * γ / -z)) 0) + ENNReal.ofReal (max (Real.log (α * δ / -z)) 0)
  else 0

/-- The fibre of the product map over `z`, inside the rectangle, as a subset of the `η₁`-line. -/
def prodFibre (α β γ δ z : ℝ) : Set ℝ := {η | η ∈ Icc (-α) β ∧ z / η ∈ Icc (-γ) δ}

theorem measurableSet_prodFibre (α β γ δ z : ℝ) : MeasurableSet (prodFibre α β γ δ z) :=
  measurableSet_Icc.inter (measurableSet_Icc.preimage (by fun_prop))

/-- `∫_{Icc c d} dη/|η| = log⁺` in the positive case: `c = z/δ`, `d = β`. -/
theorem lintegral_Icc_abs_inv_pos {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∫⁻ η in Icc c d, ENNReal.ofReal |η|⁻¹ = ENNReal.ofReal (max (Real.log (d / c)) 0) := by
  rcases le_or_gt c d with hcd | hcd
  · rw [setLIntegral_congr_fun measurableSet_Icc (g := fun η => ENNReal.ofReal η⁻¹)
      (fun η hη => by rw [abs_of_pos (hc.trans_le hη.1)]), lintegral_Icc_inv hc hcd]
    congr 1
    exact (max_eq_left (Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith))).symm
  · rw [Icc_eq_empty (not_le.mpr hcd), Measure.restrict_empty, lintegral_zero_measure]
    have : Real.log (d / c) ≤ 0 :=
      Real.log_nonpos (by positivity) (by rw [div_le_one hc]; exact hcd.le)
    rw [max_eq_right this, ENNReal.ofReal_zero]

/-- `∫_{Icc c d} dη/|η| = log⁺` in the negative case: `c = −α`, `d = −z/γ`. -/
theorem lintegral_Icc_abs_inv_neg {c d : ℝ} (hc : c < 0) (hd : d < 0) :
    ∫⁻ η in Icc c d, ENNReal.ofReal |η|⁻¹ = ENNReal.ofReal (max (Real.log (c / d)) 0) := by
  rcases le_or_gt c d with hcd | hcd
  · rw [setLIntegral_congr_fun measurableSet_Icc (g := fun η => ENNReal.ofReal (-η)⁻¹)
      (fun η hη => by rw [abs_of_neg (hη.2.trans_lt hd)]), lintegral_Icc_neg_inv hd hcd]
    congr 1
    refine (max_eq_left (Real.log_nonneg ?_)).symm
    rw [le_div_iff_of_neg hd]; linarith
  · rw [Icc_eq_empty (not_le.mpr hcd), Measure.restrict_empty, lintegral_zero_measure]
    have : Real.log (c / d) ≤ 0 := by
      refine Real.log_nonpos (div_nonneg_of_nonpos hc.le hd.le) ?_
      rw [div_le_one_of_neg hd]; exact hcd.le
    rw [max_eq_right this, ENNReal.ofReal_zero]

section Rectangle

variable {α β γ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
include hα hβ hγ hδ

/-- For `z > 0` the fibre is `[z/δ, β] ∪ [−α, −z/γ]` together with the null point `0`. -/
theorem prodFibre_pos {z : ℝ} (hz : 0 < z) :
    prodFibre α β γ δ z = Icc (z / δ) β ∪ Icc (-α) (-z / γ) ∪ {0} := by
  ext η
  simp only [prodFibre, mem_ofPred_eq, mem_Icc, mem_union, mem_singleton_iff]
  rcases lt_trichotomy η 0 with hη | rfl | hη
  · have h1 : z / η ≤ δ := (div_neg_of_pos_of_neg hz hη).le.trans hδ.le
    have h2 : -γ ≤ z / η ↔ η ≤ -z / γ := by
      rw [le_div_iff_of_neg hη, le_div_iff₀ hγ]
      constructor <;> intro h <;> linarith
    have h3 : ¬ z / δ ≤ η := not_le.mpr (hη.trans (div_pos hz hδ))
    constructor
    · rintro ⟨⟨h4, -⟩, h5, -⟩
      exact Or.inl (Or.inr ⟨h4, h2.mp h5⟩)
    · rintro ((⟨h4, -⟩ | ⟨h4, h5⟩) | h4)
      · exact absurd h4 h3
      · exact ⟨⟨h4, hη.le.trans hβ.le⟩, h2.mpr h5, h1⟩
      · exact absurd h4 hη.ne
  · simp [hα.le, hβ.le, hγ.le, hδ.le]
  · have h1 : -γ ≤ z / η := (neg_neg_of_pos hγ).le.trans (div_pos hz hη).le
    have h2 : z / η ≤ δ ↔ z / δ ≤ η := by
      rw [div_le_iff₀ hη, div_le_iff₀ hδ]
      constructor <;> intro h <;> linarith
    have h3 : ¬ η ≤ -z / γ := not_le.mpr ((div_neg_of_neg_of_pos (neg_neg_of_pos hz) hγ).trans hη)
    constructor
    · rintro ⟨⟨-, h4⟩, -, h5⟩
      exact Or.inl (Or.inl ⟨h2.mp h5, h4⟩)
    · rintro ((⟨h4, h5⟩ | ⟨-, h4⟩) | h4)
      · exact ⟨⟨(neg_neg_of_pos hα).le.trans hη.le, h5⟩, h1, h2.mpr h4⟩
      · exact absurd h4 h3
      · exact absurd h4 hη.ne'

/-- For `z < 0` the fibre is `[−z/γ, β] ∪ [−α, z/δ]` together with the null point `0`. -/
theorem prodFibre_neg {z : ℝ} (hz : z < 0) :
    prodFibre α β γ δ z = Icc (-z / γ) β ∪ Icc (-α) (z / δ) ∪ {0} := by
  ext η
  simp only [prodFibre, mem_ofPred_eq, mem_Icc, mem_union, mem_singleton_iff]
  rcases lt_trichotomy η 0 with hη | rfl | hη
  · have h1 : -γ ≤ z / η := (neg_neg_of_pos hγ).le.trans (div_pos_of_neg_of_neg hz hη).le
    have h2 : z / η ≤ δ ↔ η ≤ z / δ := by
      rw [div_le_iff_of_neg hη, le_div_iff₀ hδ]
      constructor <;> intro h <;> linarith
    have h3 : ¬ -z / γ ≤ η := not_le.mpr (hη.trans (div_pos (neg_pos.mpr hz) hγ))
    constructor
    · rintro ⟨⟨h4, -⟩, -, h5⟩
      exact Or.inl (Or.inr ⟨h4, h2.mp h5⟩)
    · rintro ((⟨h4, -⟩ | ⟨h4, h5⟩) | h4)
      · exact absurd h4 h3
      · exact ⟨⟨h4, hη.le.trans hβ.le⟩, h1, h2.mpr h5⟩
      · exact absurd h4 hη.ne
  · simp [hα.le, hβ.le, hγ.le, hδ.le]
  · have h1 : z / η ≤ δ := (div_neg_of_neg_of_pos hz hη).le.trans hδ.le
    have h2 : -γ ≤ z / η ↔ -z / γ ≤ η := by
      rw [le_div_iff₀ hη, div_le_iff₀ hγ]
      constructor <;> intro h <;> linarith
    have h3 : ¬ η ≤ z / δ := not_le.mpr ((div_neg_of_neg_of_pos hz hδ).trans hη)
    constructor
    · rintro ⟨⟨-, h4⟩, h5, -⟩
      exact Or.inl (Or.inl ⟨h2.mp h5, h4⟩)
    · rintro ((⟨h4, h5⟩ | ⟨-, h4⟩) | h4)
      · exact ⟨⟨(neg_neg_of_pos hα).le.trans hη.le, h5⟩, h2.mpr h4, h1⟩
      · exact absurd h4 h3
      · exact absurd h4 hη.ne'

/-- The fibre integral of `1/|η|` is the product density. -/
theorem lintegral_prodFibre {z : ℝ} (hz : z ≠ 0) :
    ∫⁻ η in prodFibre α β γ δ z, ENNReal.ofReal |η|⁻¹ = prodDensity α β γ δ z := by
  have hsing : ∫⁻ η in ({0} : Set ℝ), ENNReal.ofReal |η|⁻¹ = 0 := by
    rw [lintegral_singleton, Real.volume_singleton, mul_zero]
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hd1 : Disjoint (Icc (-z / γ) β) (Icc (-α) (z / δ)) := by
      rw [Set.disjoint_left]
      intro η h1 h2
      have := h1.1; have := h2.2
      have : 0 < -z / γ := div_pos (neg_pos.mpr hz) hγ
      have : z / δ < 0 := div_neg_of_neg_of_pos hz hδ
      linarith
    have hd2 : Disjoint (Icc (-z / γ) β ∪ Icc (-α) (z / δ)) ({0} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      rintro (h | h)
      · have := h.1; have : 0 < -z / γ := div_pos (neg_pos.mpr hz) hγ; linarith
      · have := h.2; have : z / δ < 0 := div_neg_of_neg_of_pos hz hδ; linarith
    rw [prodFibre_neg hα hβ hγ hδ hz, lintegral_union (measurableSet_singleton 0) hd2,
      lintegral_union measurableSet_Icc hd1, hsing, add_zero,
      lintegral_Icc_abs_inv_pos (div_pos (neg_pos.mpr hz) hγ) hβ,
      lintegral_Icc_abs_inv_neg (neg_neg_of_pos hα) (div_neg_of_neg_of_pos hz hδ),
      prodDensity, if_neg (not_lt.mpr hz.le), if_pos hz]
    have e1 : β / (-z / γ) = β * γ / -z := by field_simp
    have e2 : -α / (z / δ) = α * δ / -z := by field_simp
    rw [e1, e2]
  · have hd1 : Disjoint (Icc (z / δ) β) (Icc (-α) (-z / γ)) := by
      rw [Set.disjoint_left]
      intro η h1 h2
      have := h1.1; have := h2.2
      have : 0 < z / δ := div_pos hz hδ
      have : -z / γ < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hz) hγ
      linarith
    have hd2 : Disjoint (Icc (z / δ) β ∪ Icc (-α) (-z / γ)) ({0} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      rintro (h | h)
      · have := h.1; have : 0 < z / δ := div_pos hz hδ; linarith
      · have := h.2; have : -z / γ < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hz) hγ; linarith
    rw [prodFibre_pos hα hβ hγ hδ hz, lintegral_union (measurableSet_singleton 0) hd2,
      lintegral_union measurableSet_Icc hd1, hsing, add_zero,
      lintegral_Icc_abs_inv_pos (div_pos hz hδ) hβ,
      lintegral_Icc_abs_inv_neg (neg_neg_of_pos hα) (div_neg_of_neg_of_pos (neg_neg_of_pos hz) hγ),
      prodDensity, if_pos hz]
    have e1 : β / (z / δ) = β * δ / z := by field_simp
    have e2 : -α / (-z / γ) = α * γ / z := by field_simp
    rw [e1, e2]

omit hα hβ hγ hδ in
/-- The inner substitution `w = η₁ η₂` for a fixed `η₁ ≠ 0`. -/
theorem lintegral_Icc_mul_left {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) {η₁ : ℝ} (hη₁ : η₁ ≠ 0) :
    ∫⁻ η₂ in Icc (-γ) δ, Ψ (η₁ * η₂) =
      ENNReal.ofReal |η₁|⁻¹ * ∫⁻ w, (Icc (-γ) δ).indicator 1 (w / η₁) * Ψ w := by
  have hg : Measurable fun w : ℝ => (Icc (-γ) δ).indicator (1 : ℝ → ℝ≥0∞) (w / η₁) * Ψ w :=
    ((measurable_const.indicator measurableSet_Icc).comp (measurable_id.div_const η₁)).mul hΨ
  have h1 : ∫⁻ η₂ in Icc (-γ) δ, Ψ (η₁ * η₂) =
      ∫⁻ η₂, (fun w => (Icc (-γ) δ).indicator (1 : ℝ → ℝ≥0∞) (w / η₁) * Ψ w) (η₁ * η₂) := by
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun η₂ => ?_
    simp only [indicator, mul_div_cancel_left₀ _ hη₁, Pi.one_apply]
    split_ifs <;> simp
  rw [h1, ← lintegral_map hg (measurable_const_mul η₁), Real.map_volume_mul_left hη₁,
    lintegral_smul_measure, abs_inv, smul_eq_mul]

/-- ★★ The product-of-uniforms density: for Lebesgue measure on the rectangle
`[−α, β] × [−γ, δ]` and every measurable `Ψ ≥ 0`,
`∫ Ψ(η₁η₂) dη = ∫ Ψ(z) (log⁺(βδ/z) + log⁺(αγ/z)) dz` over `z > 0` plus the mirror term. -/
theorem lintegral_rect_prod {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ η in Icc (-α) β ×ˢ Icc (-γ) δ, Ψ (η.1 * η.2) = ∫⁻ z, Ψ z * prodDensity α β γ δ z := by
  have hae : ∀ᵐ η₁ ∂(volume : Measure ℝ), η₁ ≠ 0 := by
    rw [ae_iff]; simp
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal |p.1|⁻¹ * ((Icc (-γ) δ).indicator (1 : ℝ → ℝ≥0∞) (p.2 / p.1) * Ψ p.2) :=
    (measurable_fst.abs.inv.ennreal_ofReal).mul
      (((measurable_const.indicator measurableSet_Icc).comp (measurable_snd.div measurable_fst)).mul
        (hΨ.comp measurable_snd))
  have hΨ2 : Measurable fun η : ℝ × ℝ => Ψ (η.1 * η.2) := by fun_prop
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hΨ2.aemeasurable]
  calc ∫⁻ η₁ in Icc (-α) β, ∫⁻ η₂ in Icc (-γ) δ, Ψ (η₁ * η₂)
      = ∫⁻ η₁ in Icc (-α) β, ∫⁻ w,
          ENNReal.ofReal |η₁|⁻¹ * ((Icc (-γ) δ).indicator 1 (w / η₁) * Ψ w) := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with η₁ hη₁
        have hg : Measurable fun w : ℝ => (Icc (-γ) δ).indicator (1 : ℝ → ℝ≥0∞) (w / η₁) * Ψ w :=
          ((measurable_const.indicator measurableSet_Icc).comp (measurable_id.div_const η₁)).mul hΨ
        rw [lintegral_Icc_mul_left hΨ hη₁, ← lintegral_const_mul _ hg]
    _ = ∫⁻ w, ∫⁻ η₁ in Icc (-α) β,
          ENNReal.ofReal |η₁|⁻¹ * ((Icc (-γ) δ).indicator 1 (w / η₁) * Ψ w) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ w, Ψ w * ∫⁻ η₁ in prodFibre α β γ δ w, ENNReal.ofReal |η₁|⁻¹ := by
        refine lintegral_congr fun w => ?_
        have hf : Measurable fun η₁ : ℝ => ENNReal.ofReal |η₁|⁻¹ :=
          measurable_abs.inv.ennreal_ofReal
        rw [← lintegral_const_mul _ hf, ← lintegral_indicator measurableSet_Icc,
          ← lintegral_indicator (measurableSet_prodFibre _ _ _ _ _)]
        refine lintegral_congr fun η₁ => ?_
        simp only [indicator, prodFibre, mem_ofPred_eq, Pi.one_apply]
        split_ifs with h1 h2 h2 <;> simp_all [mul_comm]
    _ = ∫⁻ w, Ψ w * prodDensity α β γ δ w := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with w hw
        rw [lintegral_prodFibre hα hβ hγ hδ hw]

end Rectangle

/-- Scaling: `∫ F(c w) dw = |c|⁻¹ ∫ F(z) dz` for lower integrals. -/
theorem lintegral_comp_mul_left' {F : ℝ → ℝ≥0∞} (hF : Measurable F) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ w, F (c * w) = ENNReal.ofReal |c|⁻¹ * ∫⁻ z, F z := by
  rw [← lintegral_map hF (measurable_const_mul c), Real.map_volume_mul_left hc,
    lintegral_smul_measure, abs_inv, smul_eq_mul]

section Fibre

/-- The lower end `αᵢ(t) = min(λ/(1 − t), (1 − λ)/t)` of the edge-effect interval. -/
noncomputable def nbLo (l t : ℝ) : ℝ := min (l / (1 - t)) ((1 - l) / t)

/-- The upper end `βᵢ(t) = min((1 − λ)/(1 − t), λ/t)` of the edge-effect interval. -/
noncomputable def nbHi (l t : ℝ) : ℝ := min ((1 - l) / (1 - t)) (l / t)

theorem nbLo_pos {l t : ℝ} (hl : 0 < l) (hl' : l < 1) (ht : 0 < t) (ht' : t < 1) :
    0 < nbLo l t :=
  lt_min (div_pos hl (sub_pos.mpr ht')) (div_pos (sub_pos.mpr hl') ht)

theorem nbHi_pos {l t : ℝ} (hl : 0 < l) (hl' : l < 1) (ht : 0 < t) (ht' : t < 1) :
    0 < nbHi l t :=
  lt_min (div_pos (sub_pos.mpr hl') (sub_pos.mpr ht')) (div_pos hl ht)

/-- The region of `(t, (η₁, η₂))` over fixed means `λ`: the image of the cube under the moment
map, sliced at `λ` (up to the null slices `t = 0, 1`). -/
def nbRegion (l₁ l₂ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Icc (-nbLo l₁ p.1) (nbHi l₁ p.1) ×ˢ Icc (-nbLo l₂ p.1) (nbHi l₂ p.1)}

/-- The fibre volume of `μ = t(1 − t)η₁η₂` over the region, as a `t`-integral of the product
density (examples_slop eq. (nb_rho_integral)). -/
noncomputable def nbFibreDensity (l₁ l₂ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ *
    prodDensity (nbLo l₁ t) (nbHi l₁ t) (nbLo l₂ t) (nbHi l₂ t) (z / (t * (1 - t)))

theorem measurable_prodDensity :
    Measurable fun p : ℝ × ℝ × ℝ × ℝ × ℝ => prodDensity p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  unfold prodDensity
  refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) ?_ ?_
  · exact ((Real.measurable_log.comp (by fun_prop)).max measurable_const).ennreal_ofReal.add
      ((Real.measurable_log.comp (by fun_prop)).max measurable_const).ennreal_ofReal
  · refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
    exact ((Real.measurable_log.comp (by fun_prop)).max measurable_const).ennreal_ofReal.add
      ((Real.measurable_log.comp (by fun_prop)).max measurable_const).ennreal_ofReal

theorem measurable_nbLo (l : ℝ) : Measurable (nbLo l) := by unfold nbLo; fun_prop
theorem measurable_nbHi (l : ℝ) : Measurable (nbHi l) := by unfold nbHi; fun_prop

theorem measurableSet_nbRegion (l₁ l₂ : ℝ) : MeasurableSet (nbRegion l₁ l₂) := by
  unfold nbRegion
  refine (measurableSet_Ioo.preimage measurable_fst).inter ?_
  have h : ∀ l : ℝ, MeasurableSet {p : ℝ × (ℝ × ℝ) | -nbLo l p.1 ≤ p.2.1 ∧ p.2.1 ≤ nbHi l p.1} :=
    fun l => (measurableSet_le ((measurable_nbLo l).comp measurable_fst).neg
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd)
        ((measurable_nbHi l).comp measurable_fst))
  have h' : ∀ l : ℝ, MeasurableSet {p : ℝ × (ℝ × ℝ) | -nbLo l p.1 ≤ p.2.2 ∧ p.2.2 ≤ nbHi l p.1} :=
    fun l => (measurableSet_le ((measurable_nbLo l).comp measurable_fst).neg
      (measurable_snd.comp measurable_snd)).inter
      (measurableSet_le (measurable_snd.comp measurable_snd)
        ((measurable_nbHi l).comp measurable_fst))
  exact (h l₁).inter (h' l₂)

/-- The slice density at `t`: `prodDensity` of the rectangle at `t`, evaluated at `z/(t(1 − t))`. -/
noncomputable def nbSliceDensity (l₁ l₂ t z : ℝ) : ℝ≥0∞ :=
  prodDensity (nbLo l₁ t) (nbHi l₁ t) (nbLo l₂ t) (nbHi l₂ t) (z / (t * (1 - t)))

theorem measurable_nbSliceDensity (l₁ l₂ : ℝ) :
    Measurable fun p : ℝ × ℝ => nbSliceDensity l₁ l₂ p.1 p.2 := by
  have hmap : Measurable fun p : ℝ × ℝ =>
      (nbLo l₁ p.1, nbHi l₁ p.1, nbLo l₂ p.1, nbHi l₂ p.1, p.2 / (p.1 * (1 - p.1))) :=
    ((measurable_nbLo l₁).comp measurable_fst).prodMk
      (((measurable_nbHi l₁).comp measurable_fst).prodMk
        (((measurable_nbLo l₂).comp measurable_fst).prodMk
          (((measurable_nbHi l₂).comp measurable_fst).prodMk (by fun_prop))))
  exact measurable_prodDensity.comp hmap

theorem measurable_nbSliceDensity_right (l₁ l₂ t : ℝ) :
    Measurable fun z => nbSliceDensity l₁ l₂ t z :=
  (measurable_nbSliceDensity l₁ l₂).comp (measurable_const.prodMk measurable_id)

theorem measurable_nbSliceDensity_left (l₁ l₂ z : ℝ) :
    Measurable fun t => nbSliceDensity l₁ l₂ t z :=
  (measurable_nbSliceDensity l₁ l₂).comp (measurable_id.prodMk measurable_const)

theorem nbFibreDensity_eq (l₁ l₂ z : ℝ) : nbFibreDensity l₁ l₂ z =
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ * nbSliceDensity l₁ l₂ t z := rfl

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- The slice at `t ∈ (0,1)`: the rectangle integral, pushed forward and rescaled. -/
theorem lintegral_nbRegion_slice {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ η, (nbRegion l₁ l₂).indicator
        (fun p : ℝ × (ℝ × ℝ) => Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2)) (t, η) =
      ENNReal.ofReal (t * (1 - t))⁻¹ * ∫⁻ z, Ψ z * nbSliceDensity l₁ l₂ t z := by
  have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have e1 : ∫⁻ η, (nbRegion l₁ l₂).indicator
      (fun p : ℝ × (ℝ × ℝ) => Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2)) (t, η) =
      ∫⁻ η in Icc (-nbLo l₁ t) (nbHi l₁ t) ×ˢ Icc (-nbLo l₂ t) (nbHi l₂ t),
        (fun w => Ψ (t * (1 - t) * w)) (η.1 * η.2) := by
    rw [← lintegral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
    refine lintegral_congr fun η => ?_
    simp [indicator, nbRegion, ht.1, ht.2, mul_assoc]
  have hΨ' : Measurable fun w : ℝ => Ψ (t * (1 - t) * w) := hΨ.comp (measurable_const_mul _)
  rw [e1, lintegral_rect_prod (nbLo_pos h₁ h₁' ht.1 ht.2) (nbHi_pos h₁ h₁' ht.1 ht.2)
    (nbLo_pos h₂ h₂' ht.1 ht.2) (nbHi_pos h₂ h₂' ht.1 ht.2) hΨ']
  have e2 := lintegral_comp_mul_left' (F := fun z => Ψ z * nbSliceDensity l₁ l₂ t z)
    (hΨ.mul (measurable_nbSliceDensity_right l₁ l₂ t)) hc.ne'
  simp only [nbSliceDensity, mul_div_cancel_left₀ _ hc.ne'] at e2
  rw [e2, abs_of_pos hc]
  rfl

/-- ★★ The pushforward of Lebesgue measure on the region along `μ = t(1 − t)η₁η₂` has density
`nbFibreDensity`: `∫_region Ψ(t(1 − t)η₁η₂) = ∫ Ψ(z) nbFibreDensity(λ, z) dz`. -/
theorem lintegral_nbRegion {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ p in nbRegion l₁ l₂, Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2) =
      ∫⁻ z, Ψ z * nbFibreDensity l₁ l₂ z := by
  have hΨ3 : Measurable fun p : ℝ × (ℝ × ℝ) => Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2) := by fun_prop
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 * (1 - p.1))⁻¹ * (Ψ p.2 * nbSliceDensity l₁ l₂ p.1 p.2) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1 * (1 - p.1))⁻¹).ennreal_ofReal.mul
      ((hΨ.comp measurable_snd).mul (measurable_nbSliceDensity l₁ l₂))
  have hslice : ∀ t : ℝ, ∫⁻ η, (nbRegion l₁ l₂).indicator
      (fun p : ℝ × (ℝ × ℝ) => Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2)) (t, η) =
      (Ioo (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal (t * (1 - t))⁻¹ * ∫⁻ z, Ψ z * nbSliceDensity l₁ l₂ t z) t := by
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem ht, lintegral_nbRegion_slice h₁ h₁' h₂ h₂' hΨ ht]
    · rw [indicator_of_notMem ht]
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun η => ?_)
      simp only [indicator, nbRegion, mem_ofPred_eq, Pi.zero_apply]
      exact if_neg fun h => ht h.1
  rw [← lintegral_indicator (measurableSet_nbRegion l₁ l₂), Measure.volume_eq_prod,
    lintegral_prod _ (hΨ3.indicator (measurableSet_nbRegion l₁ l₂)).aemeasurable]
  calc ∫⁻ t, ∫⁻ η, (nbRegion l₁ l₂).indicator
          (fun p : ℝ × (ℝ × ℝ) => Ψ (p.1 * (1 - p.1) * p.2.1 * p.2.2)) (t, η)
      = ∫⁻ t, (Ioo (0 : ℝ) 1).indicator
          (fun t => ENNReal.ofReal (t * (1 - t))⁻¹ * ∫⁻ z, Ψ z * nbSliceDensity l₁ l₂ t z) t :=
        lintegral_congr hslice
    _ = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ z,
          ENNReal.ofReal (t * (1 - t))⁻¹ * (Ψ z * nbSliceDensity l₁ l₂ t z) := by
        rw [lintegral_indicator measurableSet_Ioo]
        refine lintegral_congr fun t => ?_
        have hm : Measurable fun z => Ψ z * nbSliceDensity l₁ l₂ t z :=
          hΨ.mul (measurable_nbSliceDensity_right l₁ l₂ t)
        rw [lintegral_const_mul _ hm]
    _ = ∫⁻ z, ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (t * (1 - t))⁻¹ * (Ψ z * nbSliceDensity l₁ l₂ t z) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ z, Ψ z * nbFibreDensity l₁ l₂ z := by
        refine lintegral_congr fun z => ?_
        have hm : Measurable fun t : ℝ =>
            ENNReal.ofReal (t * (1 - t))⁻¹ * nbSliceDensity l₁ l₂ t z :=
          (by fun_prop : Measurable fun t : ℝ => (t * (1 - t))⁻¹).ennreal_ofReal.mul
            (measurable_nbSliceDensity_left l₁ l₂ z)
        rw [nbFibreDensity_eq, ← lintegral_const_mul _ hm]
        refine lintegral_congr fun t => ?_
        ring

end Fibre

end Grammar
