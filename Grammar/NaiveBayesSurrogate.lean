/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatField
import Grammar.ConeClosedForm

/-!
# The naive Bayes quadratic surrogate: the log-square mechanism in isolation

The two-leaf naive Bayes model at an independent truth has the exact fibre density
`ρ = 2 log²(√V/|μ|) − (u₁² + u₂²)/2 + u₁u₂ sgn μ` (`Grammar.NaiveBayesClosedForm`) and a Morse
phase with Fisher information `diag(1/v₁, 1/v₂, 1/V)` (`Grammar.NaiveBayes`).  Replacing the phase
by its quadratic part and extending the density formula to the whole line gives the *surrogate*
partition function, which is computed exactly (★★★ `nbSurrogate`):

  `∫_{ℝ³} e^{−N(x²/2v₁ + y²/2v₂ + μ²/2V)} (2 log²(√V/|μ|) − c + u·sgn μ) dx dy dμ
     = (2π)^{3/2} V N^{−3/2} [ ½ log²N + g log N + 2 m₂/√(2π) − c ]`,

`g = γ + log 2`, `m₂ = ∫ e^{−z²/2} log²|z| dz`: the coefficient of `N^{−3/2} log²N` is
`c₃ = π√(2π) V`, the multiplicity three of the model as an exact identity, the shift `g` is the
Gamma derivative at `½`, and the sign jump integrates to zero at this order (examples_slop §6).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The second Gaussian logarithmic moment `m₂ = ∫ e^{−z²/2} log²|z| dz`
(its value `√(2π)(g²/4 + π²/8)` is a derivation). -/
noncomputable def gaussLogSq : ℝ := ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2

/-- `|log x| ≤ 4 x^{−1/4} + x` for `x > 0`. -/
theorem abs_log_le_rpow_quarter (x : ℝ) (hx : 0 < x) :
    |Real.log x| ≤ 4 * x ^ (-(1 / 4 : ℝ)) + x := by
  have h0 : 0 ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
  rcases le_or_gt 1 x with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hx
    linarith
  · rw [abs_of_neg (Real.log_neg hx h)]
    have h1 : Real.log (x ^ (-(1 / 4 : ℝ))) = -(1 / 4) * Real.log x := Real.log_rpow hx _
    have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-(1 / 4 : ℝ)))
    linarith

/-- The dominant `(16|z|^{−1/2} + z²) e^{−z²/2}` is integrable. -/
theorem integrable_dominant_sq :
    Integrable fun z : ℝ => (16 * |z| ^ (-(1 / 2 : ℝ)) + z ^ 2) * Real.exp (-z ^ 2 / 2) := by
  set g : ℝ → ℝ := fun z => (16 * |z| ^ (-(1 / 2 : ℝ)) + z ^ 2) * Real.exp (-z ^ 2 / 2) with hg
  have hgeven : ∀ z, g (-z) = g z := by intro z; simp only [hg, abs_neg, neg_sq]
  have hpos : IntegrableOn g (Ioi 0) := by
    have h1 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      (s := -(1 / 2)) (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    have h2 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 2)
      (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
    refine IntegrableOn.congr_fun ((h1.const_mul 16).add h2) (fun z hz => ?_) measurableSet_Ioi
    simp only [hg, Pi.add_apply, abs_of_pos (mem_Ioi.mp hz), Real.rpow_two]
    ring_nf
  have hneg : IntegrableOn g (Iio 0) := by
    have := hpos.comp_neg
    rw [Set.neg_Ioi, neg_zero] at this
    exact this.congr_fun (fun z _ => hgeven z) measurableSet_Iio
  rw [← integrableOn_univ, ← Iio_union_Ici, integrableOn_union]
  refine ⟨hneg, ?_⟩
  rw [IntegrableOn, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  exact hpos

/-- `e^{−z²/2} log²|z|` is integrable on `ℝ`. -/
theorem integrable_exp_neg_sq_log_sq :
    Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2 := by
  refine (integrable_dominant_sq.const_mul 2).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℝ =>
      Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, sq_abs]
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · have hlog := abs_log_le_rpow_quarter |z| (abs_pos.mpr hz)
      have hsq : Real.log (abs z) ^ 2 ≤ 2 * (16 * abs z ^ (-(1 / 2 : ℝ)) + z ^ 2) := by
        have h1 : abs (Real.log (abs z)) ^ 2 ≤ (4 * abs z ^ (-(1 / 4 : ℝ)) + abs z) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hlog 2
        have h2 : (4 * abs z ^ (-(1 / 4 : ℝ)) + abs z) ^ 2 ≤
            2 * (16 * (abs z ^ (-(1 / 4 : ℝ))) ^ 2 + abs z ^ 2) := by
          nlinarith [sq_nonneg (4 * abs z ^ (-(1 / 4 : ℝ)) - abs z)]
        have h3 : (abs z ^ (-(1 / 4 : ℝ))) ^ 2 = abs z ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg z)]; norm_num
        rw [sq_abs] at h1
        rw [h3, sq_abs] at h2
        linarith
      calc Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2
          ≤ Real.exp (-z ^ 2 / 2) * (2 * (16 * |z| ^ (-(1 / 2 : ℝ)) + z ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
        _ = 2 * ((16 * |z| ^ (-(1 / 2 : ℝ)) + z ^ 2) * Real.exp (-z ^ 2 / 2)) := by ring

/-- Even functions: `∫_ℝ f = 2 ∫_0^∞ f`. -/
theorem integral_even_eq_two_mul_Ioi {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ x, f (-x) = f x) :
    ∫ x, f x = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  rw [← integral_add_compl measurableSet_Iio hf, compl_Iio, integral_Iio_zero_eq_Ioi_neg,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  simp only [heven]
  ring

/-- `∫_ℝ e^{−z²/2} log|z| dz = −(√(2π)/2)(γ + log 2)`. -/
theorem integral_exp_neg_sq_half_log_abs :
    ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * Real.log |z| =
      -(Real.sqrt (2 * Real.pi) / 2) * (Real.eulerMascheroniConstant + Real.log 2) := by
  have hint : Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2) * Real.log |z| := by
    have := integrable_exp_quadratic_log 0
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp
  rw [integral_even_eq_two_mul_Ioi hint (fun z => by simp [abs_neg])]
  have : ∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2 / 2) * Real.log |z| =
      ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2 / 2) * Real.log u :=
    setIntegral_congr_fun measurableSet_Ioi fun z hz => by rw [abs_of_pos hz]
  rw [this, integral_exp_neg_sq_half_log]
  ring

/-- The sign is odd, so `∫ e^{−z²/2} sgn z = 0`. -/
theorem integral_exp_neg_sq_half_sign : ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * Real.sign z = 0 := by
  have h := integral_neg_eq_self (fun z : ℝ => Real.exp (-z ^ 2 / 2) * Real.sign z) volume
  simp only [neg_sq, Real.sign_neg, mul_neg] at h
  rw [integral_neg] at h
  linarith

/-- The Gaussian `∫ e^{−z²/2} = √(2π)`. -/
theorem integral_exp_neg_sq_half : ∫ z : ℝ, Real.exp (-z ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have := integral_gaussian (1 / 2 : ℝ)
  rw [show (fun z : ℝ => Real.exp (-z ^ 2 / 2)) = fun z => Real.exp (-(1 / 2) * z ^ 2) by
    funext z; ring_nf, this]
  congr 1; ring

/-- ★★ The one-dimensional surrogate integral: for `N, V > 0`,
`∫ e^{−Nμ²/(2V)} (2 log²(√V/|μ|) − c + u sgn μ) dμ
   = √(V/N) [√(2π)(½ log²N − c) + √(2π)(γ + log 2) log N + 2 m₂]`. -/
theorem integral_surrogate_line {N V : ℝ} (hN : 0 < N) (hV : 0 < V) (c u : ℝ) :
    ∫ μ : ℝ, Real.exp (-N * μ ^ 2 / (2 * V)) *
        (2 * Real.log (Real.sqrt V / |μ|) ^ 2 - c + u * Real.sign μ) =
      Real.sqrt (V / N) * (Real.sqrt (2 * Real.pi) * (Real.log N ^ 2 / 2 - c) +
        Real.sqrt (2 * Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) * Real.log N +
        2 * gaussLogSq) := by
  set s := Real.sqrt (V / N) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (div_pos hV hN)
  have hs2 : s ^ 2 = V / N := Real.sq_sqrt (div_pos hV hN).le
  have hae : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
  set f : ℝ → ℝ := fun μ => Real.exp (-N * μ ^ 2 / (2 * V)) *
    (2 * Real.log (Real.sqrt V / |μ|) ^ 2 - c + u * Real.sign μ) with hf
  have h := MeasureTheory.Measure.integral_comp_mul_left f s
  rw [abs_of_pos (inv_pos.mpr hs0), smul_eq_mul] at h
  have hI : ∫ μ, f μ = s * ∫ z, f (s * z) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
  -- pointwise off `z = 0`
  have e : ∀ z ≠ (0 : ℝ), f (s * z) = Real.exp (-z ^ 2 / 2) *
      (Real.log N ^ 2 / 2 - 2 * Real.log N * Real.log |z| + 2 * Real.log |z| ^ 2 - c +
        u * Real.sign z) := by
    intro z hz
    simp only [hf]
    have e1 : -N * (s * z) ^ 2 / (2 * V) = -z ^ 2 / 2 := by
      rw [mul_pow, hs2]; field_simp
    have e2 : Real.log (Real.sqrt V / |s * z|) = Real.log N / 2 - Real.log |z| := by
      rw [abs_mul, abs_of_pos hs0, hs, Real.sqrt_div hV.le, ← Real.log_sqrt hN.le]
      have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
      rw [show Real.sqrt V / (Real.sqrt V / Real.sqrt N * |z|) = Real.sqrt N / |z| by
        field_simp, Real.log_div hsN.ne' (abs_ne_zero.mpr hz)]
    have e3 : Real.sign (s * z) = Real.sign z := by
      rcases lt_or_gt_of_ne hz with h | h
      · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hs0 h)]
      · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hs0 h)]
    rw [e1, e2, e3]
    ring
  have hae' : (fun z => f (s * z)) =ᵐ[volume] fun z => Real.exp (-z ^ 2 / 2) *
      (Real.log N ^ 2 / 2 - 2 * Real.log N * Real.log |z| + 2 * Real.log |z| ^ 2 - c +
        u * Real.sign z) :=
    hae.mono fun z hz => e z hz
  rw [hI, integral_congr_ae hae']
  -- integrability of the pieces
  have hg : Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring_nf
  have hlog : Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2) * Real.log |z| := by
    have := integrable_exp_quadratic_log 0
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp
  have hsignm : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const)
  have hsign : Integrable fun z : ℝ => Real.exp (-z ^ 2 / 2) * Real.sign z := by
    refine hg.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((by fun_prop : Measurable fun z : ℝ => Real.exp (-z ^ 2 / 2)).mul
        hsignm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have : |Real.sign z| ≤ 1 := by
        rcases lt_trichotomy z 0 with h | rfl | h
        · rw [Real.sign_of_neg h]; simp
        · simp
        · rw [Real.sign_of_pos h]; simp
      nlinarith [Real.exp_pos (-z ^ 2 / 2)]
  have e4 : (fun z : ℝ => Real.exp (-z ^ 2 / 2) *
      (Real.log N ^ 2 / 2 - 2 * Real.log N * Real.log |z| + 2 * Real.log |z| ^ 2 - c +
        u * Real.sign z)) = fun z =>
      (Real.log N ^ 2 / 2 - c) * Real.exp (-z ^ 2 / 2) -
        (2 * Real.log N) * (Real.exp (-z ^ 2 / 2) * Real.log |z|) +
        2 * (Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2) +
        u * (Real.exp (-z ^ 2 / 2) * Real.sign z) := by
    funext z; ring
  have hA : Integrable fun z : ℝ => (Real.log N ^ 2 / 2 - c) * Real.exp (-z ^ 2 / 2) :=
    hg.const_mul _
  have hB : Integrable fun z : ℝ => (2 * Real.log N) * (Real.exp (-z ^ 2 / 2) * Real.log |z|) :=
    hlog.const_mul _
  have hC : Integrable fun z : ℝ => 2 * (Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2) :=
    integrable_exp_neg_sq_log_sq.const_mul 2
  have hD : Integrable fun z : ℝ => u * (Real.exp (-z ^ 2 / 2) * Real.sign z) := hsign.const_mul u
  have hAB : Integrable fun z : ℝ => (Real.log N ^ 2 / 2 - c) * Real.exp (-z ^ 2 / 2) -
      (2 * Real.log N) * (Real.exp (-z ^ 2 / 2) * Real.log |z|) := hA.sub hB
  have hABC : Integrable fun z : ℝ => (Real.log N ^ 2 / 2 - c) * Real.exp (-z ^ 2 / 2) -
      (2 * Real.log N) * (Real.exp (-z ^ 2 / 2) * Real.log |z|) +
        2 * (Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2) := hAB.add hC
  rw [e4, integral_add hABC hD, integral_add hAB hC, integral_sub hA hB, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_exp_neg_sq_half,
    integral_exp_neg_sq_half_log_abs, integral_exp_neg_sq_half_sign, gaussLogSq]
  ring

/-- The one-dimensional Gaussian factor `∫ e^{−Nx²/(2v)} dx = √(2πv/N)`. -/
theorem integral_exp_neg_mul_sq_div {N v : ℝ} (hN : 0 < N) (hv : 0 < v) :
    ∫ x : ℝ, Real.exp (-N * x ^ 2 / (2 * v)) = Real.sqrt (2 * Real.pi * v / N) := by
  have := integral_gaussian (N / (2 * v))
  rw [show (fun x : ℝ => Real.exp (-N * x ^ 2 / (2 * v))) =
    fun x => Real.exp (-(N / (2 * v)) * x ^ 2) by funext x; ring_nf, this]
  congr 1
  field_simp

/-- ★★★ **The naive Bayes quadratic surrogate, exactly**: for `N, v₁, v₂ > 0`, `V = v₁v₂`,
`∫_{ℝ³} e^{−N(x²/2v₁ + y²/2v₂ + μ²/2V)} (2 log²(√V/|μ|) − c + u sgn μ)
   = (2π)^{3/2} V N^{−3/2} [½ log²N + (γ + log 2) log N + 2m₂/√(2π) − c]`;
the coefficient of `N^{−3/2} log²N` is `π√(2π) V`. -/
theorem nbSurrogate {N v₁ v₂ : ℝ} (hN : 0 < N) (h₁ : 0 < v₁) (h₂ : 0 < v₂) (c u : ℝ) :
    ∫ p : ℝ × ℝ × ℝ, Real.exp (-N * p.1 ^ 2 / (2 * v₁)) *
        (Real.exp (-N * p.2.1 ^ 2 / (2 * v₂)) *
          (Real.exp (-N * p.2.2 ^ 2 / (2 * (v₁ * v₂))) *
            (2 * Real.log (Real.sqrt (v₁ * v₂) / |p.2.2|) ^ 2 - c + u * Real.sign p.2.2))) =
      2 * Real.pi * Real.sqrt (2 * Real.pi) * (v₁ * v₂) / (N * Real.sqrt N) *
        (Real.log N ^ 2 / 2 + (Real.eulerMascheroniConstant + Real.log 2) * Real.log N +
          2 * gaussLogSq / Real.sqrt (2 * Real.pi) - c) := by
  rw [Measure.volume_eq_prod, integral_prod_mul (f := fun x : ℝ => Real.exp (-N * x ^ 2 / (2 * v₁)))
    (g := fun q : ℝ × ℝ => Real.exp (-N * q.1 ^ 2 / (2 * v₂)) *
      (Real.exp (-N * q.2 ^ 2 / (2 * (v₁ * v₂))) *
        (2 * Real.log (Real.sqrt (v₁ * v₂) / |q.2|) ^ 2 - c + u * Real.sign q.2))),
    Measure.volume_eq_prod, integral_prod_mul (f := fun y : ℝ => Real.exp (-N * y ^ 2 / (2 * v₂)))
    (g := fun μ : ℝ => Real.exp (-N * μ ^ 2 / (2 * (v₁ * v₂))) *
      (2 * Real.log (Real.sqrt (v₁ * v₂) / |μ|) ^ 2 - c + u * Real.sign μ)),
    integral_surrogate_line hN (mul_pos h₁ h₂) c u, integral_exp_neg_mul_sq_div hN h₁,
    integral_exp_neg_mul_sq_div hN h₂]
  -- square-root algebra: write everything through `a = √v₁`, `b = √v₂`, `r = √N`, `p = √(2π)`
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℝ, 0 < a ∧ v₁ = a ^ 2 :=
    ⟨Real.sqrt v₁, Real.sqrt_pos.mpr h₁, (Real.sq_sqrt h₁.le).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b : ℝ, 0 < b ∧ v₂ = b ^ 2 :=
    ⟨Real.sqrt v₂, Real.sqrt_pos.mpr h₂, (Real.sq_sqrt h₂.le).symm⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ N = r ^ 2 :=
    ⟨Real.sqrt N, Real.sqrt_pos.mpr hN, (Real.sq_sqrt hN.le).symm⟩
  set p := Real.sqrt (2 * Real.pi) with hp
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hp2 : 2 * Real.pi = p ^ 2 := (Real.sq_sqrt (by positivity)).symm
  rw [hp2]
  have e1 : Real.sqrt (p ^ 2 * a ^ 2 / r ^ 2) = p * a / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hp0.le,
      Real.sqrt_sq ha.le, Real.sqrt_sq hr.le]
  have e2 : Real.sqrt (p ^ 2 * b ^ 2 / r ^ 2) = p * b / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hp0.le,
      Real.sqrt_sq hb.le, Real.sqrt_sq hr.le]
  have e3 : Real.sqrt (a ^ 2 * b ^ 2 / r ^ 2) = a * b / r := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le,
      Real.sqrt_sq hb.le, Real.sqrt_sq hr.le]
  rw [e1, e2, e3, Real.sqrt_sq hr.le, Real.log_pow]
  push_cast
  field_simp
  ring

end Grammar
