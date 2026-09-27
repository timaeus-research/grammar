/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.NaiveBayesClosedForm
import Grammar.MellinTransferInterfaces

/-!
# The naive-Bayes pushforward density as a fixed-domain parameter integral

The fibre density `ρ(λ, μ) = ∫₀¹ dt/(t(1−t)) · h_λ(t, μ/(t(1−t)))` of examples_slop
eq. nb_rho_integral is `nbFibreDensity` (DXCII, an `ℝ≥0∞`-valued Lebesgue integral).  Here it is
identified with a real-valued fixed-domain integral of the jointly measurable rectangle kernel
`nbRectKernel λ t z = (prodDensity (α₁(t), β₁(t), α₂(t), β₂(t)) z).toReal` — the instance of
DCLIII's `measurable_fixedDomainIntegral` that Astra round 17 asked for — and both versions are
jointly measurable in `(λ, μ)`:

* `measurable_nbFibreDensity` : `(λ, μ) ↦ nbFibreDensity λ₁ λ₂ μ` is measurable
  (`Measurable.lintegral_prod_right'`);
* `nbFixedDensity`, `measurable_nbFixedDensity` : the real fixed-domain integral and its
  measurability through DCLIII;
* `nbFixedDensity_eq_toReal` : `nbFixedDensity ((λ₁, λ₂), μ) = (nbFibreDensity λ₁ λ₂ μ).toReal`
  unconditionally (`integral_eq_lintegral_of_nonneg_ae`; `prodDensity` is never `⊤`);
* `nbFixedDensity_closed_pos/neg` : the real closed form `2 log(M±/|μ|) log(V/(M±|μ|))` on
  `0 < |μ| < M±` (from DXCIV).

Not included: fibre integrability of `ρ` beyond the closed-form window.  Examples_slop §6.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-- `prodDensity` is a finite sum of `ENNReal.ofReal`s, never `⊤`. -/
theorem prodDensity_ne_top (α β γ δ z : ℝ) : prodDensity α β γ δ z ≠ ⊤ := by
  unfold prodDensity
  split_ifs <;> simp

/-- The slice density is jointly measurable in `(λ₁, λ₂, z, t)`. -/
theorem measurable_nbSliceDensity_joint :
    Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ => nbSliceDensity q.1.1.1 q.1.1.2 q.2 q.1.2 := by
  unfold nbSliceDensity
  have hmap : Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      (nbLo q.1.1.1 q.2, nbHi q.1.1.1 q.2, nbLo q.1.1.2 q.2, nbHi q.1.1.2 q.2,
        q.1.2 / (q.2 * (1 - q.2))) := by
    unfold nbLo nbHi; fun_prop
  exact measurable_prodDensity.comp hmap

/-- ★★ The naive-Bayes fibre density is jointly measurable in `(λ, μ)`. -/
theorem measurable_nbFibreDensity :
    Measurable fun p : (ℝ × ℝ) × ℝ => nbFibreDensity p.1.1 p.1.2 p.2 := by
  have hm : Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      ENNReal.ofReal (q.2 * (1 - q.2))⁻¹ * nbSliceDensity q.1.1.1 q.1.1.2 q.2 q.1.2 :=
    ((measurable_snd.mul (measurable_const.sub measurable_snd)).inv.ennreal_ofReal).mul
      measurable_nbSliceDensity_joint
  change Measurable fun p : (ℝ × ℝ) × ℝ =>
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t * (1 - t))⁻¹ * nbSliceDensity p.1.1 p.1.2 t p.2
  exact hm.lintegral_prod_right'

/-- The real rectangle kernel `h_λ(t, z)`: the two-logarithm density of `η₁η₂` on the
rectangle `[−α₁(t), β₁(t)] × [−α₂(t), β₂(t)]` at fixed means `λ = (λ₁, λ₂)`. -/
noncomputable def nbRectKernel (L : ℝ × ℝ) (t z : ℝ) : ℝ :=
  (prodDensity (nbLo L.1 t) (nbHi L.1 t) (nbLo L.2 t) (nbHi L.2 t) z).toReal

/-- The real fixed-domain density `ρ(λ, μ) = ∫₀¹ dt/(t(1−t)) · h_λ(t, μ/(t(1−t)))`
(examples_slop eq. nb_rho_integral). -/
noncomputable def nbFixedDensity (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, (t * (1 - t))⁻¹ * nbRectKernel p.1 t (p.2 / (t * (1 - t)))

/-- The composed rectangle kernel is jointly measurable (the hypothesis of DCLIII). -/
theorem measurable_nbRectKernel :
    Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      nbRectKernel p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2))) :=
  measurable_nbSliceDensity_joint.ennreal_toReal

/-- ★★ The real fixed-domain density is measurable in `(λ, μ)`: DCLIII instantiated. -/
theorem measurable_nbFixedDensity : Measurable nbFixedDensity := by
  unfold nbFixedDensity
  exact measurable_fixedDomainIntegral (Λ := ℝ × ℝ) (h := nbRectKernel) measurable_nbRectKernel

/-- ★★ The two versions agree: `nbFixedDensity ((λ₁, λ₂), μ) = (nbFibreDensity λ₁ λ₂ μ).toReal`. -/
theorem nbFixedDensity_eq_toReal (l₁ l₂ z : ℝ) :
    nbFixedDensity ((l₁, l₂), z) = (nbFibreDensity l₁ l₂ z).toReal := by
  have hmeas : Measurable fun t : ℝ =>
      (t * (1 - t))⁻¹ * nbRectKernel (l₁, l₂) t (z / (t * (1 - t))) :=
    (measurable_id.mul (measurable_const.sub measurable_id)).inv.mul
      (measurable_nbSliceDensity_left l₁ l₂ z).ennreal_toReal
  unfold nbFixedDensity
  rw [integral_eq_lintegral_of_nonneg_ae ?_ hmeas.aestronglyMeasurable, nbFibreDensity_eq]
  · congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), nbRectKernel,
      ENNReal.ofReal_toReal (prodDensity_ne_top _ _ _ _ _)]
    rfl
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
    have hc : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
    exact mul_nonneg (inv_nonneg.mpr hc.le) ENNReal.toReal_nonneg

section Closed

variable {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₁' : l₁ < 1) (h₂ : 0 < l₂) (h₂' : l₂ < 1)
include h₁ h₁' h₂ h₂'

/-- ★★ The real closed form, `μ > 0`: for `0 < μ < M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`,
`ρ(λ, μ) = 2 log(M₊/μ) · log(V/(M₊μ))`, `V = λ₁(1−λ₁)λ₂(1−λ₂)`. -/
theorem nbFixedDensity_closed_pos {z : ℝ} (hz : 0 < z)
    (hzM : z < min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))) :
    nbFixedDensity ((l₁, l₂), z) = 2 *
      (Real.log (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) / z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) * z))) := by
  have hM2 : (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))) ^ 2 ≤ l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    have h1 := min_le_left (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
    have h2 := min_le_right (l₁ * (1 - l₂)) (l₂ * (1 - l₁))
    have h0 : 0 ≤ min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) := le_min (by nlinarith) (by nlinarith)
    nlinarith [mul_le_mul h1 h2 h0 (by nlinarith)]
  rw [nbFixedDensity_eq_toReal, nbFibreDensity_closed_pos h₁ h₁' h₂ h₂' hz hzM,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (closed_nonneg hz hzM.le hM2))]

/-- ★★ The real closed form, `μ < 0`: for `−M₋ < μ < 0`, `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`,
`ρ(λ, μ) = 2 log(M₋/|μ|) · log(V/(M₋|μ|))`. -/
theorem nbFixedDensity_closed_neg {z : ℝ} (hz : z < 0)
    (hzM : -z < min (l₁ * l₂) ((1 - l₁) * (1 - l₂))) :
    nbFixedDensity ((l₁, l₂), z) = 2 *
      (Real.log (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) / -z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) * -z))) := by
  have hz' : 0 < -z := neg_pos.mpr hz
  have hM2 : (min (l₁ * l₂) ((1 - l₁) * (1 - l₂))) ^ 2 ≤ l₁ * (1 - l₁) * (l₂ * (1 - l₂)) := by
    have h1 := min_le_left (l₁ * l₂) ((1 - l₁) * (1 - l₂))
    have h2 := min_le_right (l₁ * l₂) ((1 - l₁) * (1 - l₂))
    have h0 : 0 ≤ min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) := le_min (by nlinarith) (by nlinarith)
    nlinarith [mul_le_mul h1 h2 h0 (by nlinarith)]
  rw [nbFixedDensity_eq_toReal, nbFibreDensity_closed_neg h₁ h₁' h₂ h₂' hz hzM,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (closed_nonneg hz' hzM.le hM2))]

end Closed

end Grammar
