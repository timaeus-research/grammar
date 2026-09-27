/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PrincipalPartUniqueness

/-!
# The polar distributions of the one-dimensional state densities

The exact one-dimensional reductions of the examples note (examples_slop §2) are integrals
against *state densities* on `[−1, 1]`: `ρ_log(t) = 2 log(1/|t|)` for the crossing `x²y²` (the
depth-two deep linear network, flat prior) and `ρ_mix(t) = |t|^{−2/3} − 1` for the mixed exponents
`x²y⁶`.  The paper's polar distributions are the principal parts of the Mellin transforms
`s ↦ ∫ ρ(t) φ(t) |t|^{−2s} dt` at their poles, as distributions in the test amplitude `φ`.  This
module computes them.

For the symmetrised amplitude `ψ(t) = φ(t) + φ(−t)` on `(0, 1]` (`integral_symm`), with `ψ`
continuous and `|ψ(t) − ψ(0)| ≤ L t`:

* `mellinIoc g s = ∫_0^1 g(t) t^{−2s} dt` is holomorphic on `Re s < (b+1)/2` whenever
  `‖g(t)‖ ≤ C t^b` (★★ `hasDerivAt_mellinIoc`, dominated differentiation with the log majorant
  `|log t| ≤ t^{−δ}/δ`);
* log density: `∫_0^1 2 log(1/t) ψ(t) t^{−2s} dt = ψ(0) · 2/(1−2s)² + R_log(ψ, s)` on `Re s < ½`
  (`logMellin_eq`), `R_log` holomorphic on `Re s < 1` (`differentiableOn_logRem`), so the
  continuation has the principal part `(ψ(0)/2)/(s−½)²` at `½` and NO simple pole
  (★★★ `logCont_sub_polarPart_isBigO`, `logCont_polarCoeff_unique`): for the full density on
  `[−1,1]` this is `C_{½,2} = φ(0)`, `C_{½,1} = 0` — the polar distribution is `δ₀` at order two;
* mixed density: `∫_0^1 (t^{−2/3} − 1) ψ(t) t^{−2s} dt = ψ(0)(1/(⅓−2s) − 1/(1−2s)) + R_mix(ψ, s)`
  on `Re s < 1/6` (`mixMellin_eq`), `R_mix` holomorphic on `Re s < 2/3`
  (`differentiableOn_mixRem`), so the continuation has the simple poles `−(ψ(0)/2)/(s−1/6)` and
  `(ψ(0)/2)/(s−½)` (★★★ `mixCont_sub_polarPart_isBigO_sixth/half`): `C_{1/6,1} = −φ(0)`,
  `C_{½,1} = +φ(0)` — the polar distributions are `∓δ₀`, the second with the opposite sign.

Conventions: `polarPart D a μ s = Σ_{q ≤ D} a_q/(s−μ)^{q+1}` (powers of `s − μ`), so a simple
coefficient `1/(1−2s) = −(1/2)/(s−½)` is negative in this convention;
`polarPart_eq_of_sub_isBigO_one` makes the coefficients unique.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The log majorant and integrability on `(0, 1]` -/

/-- `|log t| ≤ t^{−δ}/δ` on `(0, 1]`. -/
theorem abs_log_le_rpow_div {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    |Real.log t| ≤ t ^ (-δ) / δ := by
  have ht0 : 0 < t := ht.1
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
  rw [abs_of_nonpos hlog, le_div_iff₀ hδ]
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (-δ))
  rw [Real.log_rpow ht0] at h
  linarith

theorem integrableOn_rpow_Ioc {c : ℝ} (hc : -1 < c) :
    IntegrableOn (fun t : ℝ => t ^ c) (Ioc (0 : ℝ) 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact intervalIntegral.intervalIntegrable_rpow' hc

theorem integrableOn_rpow_mul_log_Ioc {c : ℝ} (hc : -1 < c) :
    IntegrableOn (fun t : ℝ => t ^ c * |Real.log t|) (Ioc (0 : ℝ) 1) := by
  set δ := (c + 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hint := (integrableOn_rpow_Ioc (c := c - δ) (by rw [hδ]; linarith)).const_mul (1 / δ)
  refine hint.mono' ?_ ?_
  · exact ((measurable_id.pow_const c).mul Real.measurable_log.abs).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ c * |Real.log t| ≤ t ^ c * (t ^ (-δ) / δ) := by
          gcongr; exact abs_log_le_rpow_div hδpos ht
      _ = 1 / δ * t ^ (c - δ) := by
          rw [Real.rpow_sub ht0, Real.rpow_neg ht0.le]
          field_simp

/-! ### The Mellin integral on `(0, 1]` and its holomorphy -/

/-- The Mellin-type integral `∫_0^1 g(t) t^{−2s} dt`. -/
noncomputable def mellinIoc (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (-2 * s)

theorem norm_cpow_neg_two (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-2 * s)‖ = t ^ (-2 * s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  congr 1
  simp

theorem aestronglyMeasurable_cpow_neg_two (s : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-2 * s)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (Complex.measurable_ofReal.pow_const _).aestronglyMeasurable

/-- Integrability of the Mellin integrand under the power bound `‖g t‖ ≤ C t^b`. -/
theorem integrableOn_mellinIoc {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {s : ℂ} (hs : s.re < (b + 1) / 2) :
    IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (-2 * s)) (Ioc (0 : ℝ) 1) := by
  refine ((integrableOn_rpow_Ioc (c := b - 2 * s.re) (by linarith)).const_mul C).mono'
    (hg.mul (aestronglyMeasurable_cpow_neg_two s)) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  rw [norm_mul, norm_cpow_neg_two s ht0]
  calc ‖g t‖ * t ^ (-2 * s.re) ≤ C * t ^ b * t ^ (-2 * s.re) := by
        gcongr; exact hb t ht
    _ = C * t ^ (b - 2 * s.re) := by
        rw [mul_assoc, ← Real.rpow_add ht0]; congr 2; ring

/-- Integrability of the differentiated Mellin integrand. -/
theorem integrableOn_mellinIoc_log {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {s : ℂ} (hs : s.re < (b + 1) / 2) :
    IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)))
      (Ioc (0 : ℝ) 1) := by
  refine ((integrableOn_rpow_mul_log_Ioc (c := b - 2 * s.re) (by linarith)).const_mul
    (2 * C)).mono' ((hg.mul (aestronglyMeasurable_cpow_neg_two s)).mul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        Real.measurable_log.aestronglyMeasurable).const_mul _)) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, norm_mul, norm_cpow_neg_two s ht0, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, h2]
  calc ‖g t‖ * t ^ (-2 * s.re) * (2 * |Real.log t|)
      ≤ C * t ^ b * t ^ (-2 * s.re) * (2 * |Real.log t|) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hb t ht) (by positivity)
    _ = 2 * C * (t ^ (b - 2 * s.re) * |Real.log t|) := by
        rw [show b - 2 * s.re = b + -2 * s.re by ring, Real.rpow_add ht0]
        ring

/-- ★★ **Holomorphy of the Mellin integral on `(0, 1]`**: under `‖g t‖ ≤ C t^b`, the function
`s ↦ ∫_0^1 g(t) t^{−2s} dt` is differentiable at every `s` with `Re s < (b+1)/2`, with derivative
`∫_0^1 g(t) t^{−2s} (−2 log t) dt`. -/
theorem hasDerivAt_mellinIoc {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {s : ℂ} (hs : s.re < (b + 1) / 2) :
    HasDerivAt (mellinIoc g)
      (∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ))) s := by
  set ε : ℝ := ((b + 1) / 2 - s.re) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set σ : ℝ := s.re + ε with hσ
  have hσlt : σ < (b + 1) / 2 := by rw [hσ, hε]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun x (t : ℝ) => g t * (t : ℂ) ^ (-2 * x))
    (F' := fun x (t : ℝ) => g t * (t : ℂ) ^ (-2 * x) * (-2 * (Real.log t : ℂ)))
    (bound := fun t => 2 * C * (t ^ (b - 2 * σ) * |Real.log t|))
    (s := Metric.ball s ε) (Metric.ball_mem_nhds s hεpos)
    (Eventually.of_forall fun x => hg.mul (aestronglyMeasurable_cpow_neg_two x))
    (integrableOn_mellinIoc hg hb hs)
    ((hg.mul (aestronglyMeasurable_cpow_neg_two s)).mul
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        Real.measurable_log.aestronglyMeasurable).const_mul _))
    ?_ ((integrableOn_rpow_mul_log_Ioc (c := b - 2 * σ) (by linarith)).const_mul _) ?_
  · exact key.2
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht x hx => ?_
    have ht0 : 0 < t := ht.1
    have hxre : x.re ≤ σ := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := Complex.abs_re_le_norm (x - s)
      rw [Complex.sub_re] at this
      rw [hσ]
      linarith [abs_le.1 (this.trans hx.le) |>.2]
    have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, norm_cpow_neg_two x ht0, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, h2]
    have hB : t ^ (-2 * x.re) ≤ t ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
    calc ‖g t‖ * t ^ (-2 * x.re) * (2 * |Real.log t|)
        ≤ C * t ^ b * t ^ (-2 * σ) * (2 * |Real.log t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (hb t ht) hB (by positivity) (by positivity)
      _ = 2 * C * (t ^ (b - 2 * σ) * |Real.log t|) := by
          rw [show b - 2 * σ = b + -2 * σ by ring, Real.rpow_add ht0]
          ring
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht x _ => ?_
    have ht0 : 0 < t := ht.1
    have h0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hd := (((hasDerivAt_id x).const_mul (-2 : ℂ)).const_cpow (Or.inl h0)).const_mul (g t)
    refine hd.congr_deriv ?_
    simp only [id, mul_one]
    rw [← Complex.ofReal_log ht0.le]
    ring

theorem differentiableOn_mellinIoc {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) :
    DifferentiableOn ℂ (mellinIoc g) {s : ℂ | s.re < (b + 1) / 2} := fun _ hs =>
  (hasDerivAt_mellinIoc hg hC hb hs).differentiableAt.differentiableWithinAt

/-! ### The exact pole evaluations -/

/-- `∫_0^1 t^{−2s} dt = 1/(1 − 2s)` for `Re s < ½`. -/
theorem mellinIoc_one {s : ℂ} (hs : s.re < 1 / 2) : mellinIoc (fun _ => 1) s = 1 / (1 - 2 * s) := by
  unfold mellinIoc
  simp only [one_mul]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by simp; linarith))]
  have h1 : (-2 * s + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow h1]
  rw [sub_zero]
  congr 1
  ring

/-- `∫_0^1 t^{−2s} (−2 log t) dt = 2/(1 − 2s)²` for `Re s < ½`: the derivative of the previous
evaluation. -/
theorem integral_cpow_log_Ioc {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ)) = 2 / (1 - 2 * s) ^ 2 := by
  have h1 := hasDerivAt_mellinIoc (g := fun _ => (1 : ℂ)) aestronglyMeasurable_const (C := 1)
    (b := 0) zero_le_one (fun t ht => by simp [Real.rpow_zero]) (by simpa using hs)
  have hne : (1 - 2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : HasDerivAt (fun s : ℂ => 1 / (1 - 2 * s)) (2 / (1 - 2 * s) ^ 2) s := by
    have := (((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub 1).inv hne
    simp only [one_div]
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    ring
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : HasDerivAt (mellinIoc fun _ => (1 : ℂ)) (2 / (1 - 2 * s) ^ 2) s :=
    h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hopen.mem_nhds hs)
      fun z hz => mellinIoc_one hz)
  have := h1.unique h3
  simpa only [one_mul] using this

/-- `∫_0^1 (t^{−2/3} − 1) t^{−2s} dt = 1/(⅓ − 2s) − 1/(1 − 2s)` for `Re s < 1/6`. -/
theorem mellinIoc_mixed {s : ℂ} (hs : s.re < 1 / 6) :
    mellinIoc (fun t : ℝ => ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ)) s =
      1 / (1 / 3 - 2 * s) - 1 / (1 - 2 * s) := by
  unfold mellinIoc
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s) =
      (t : ℂ) ^ (-(2 / 3 : ℂ) + -2 * s) - (t : ℂ) ^ (-2 * s) := by
    intro t ht
    have h0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    rw [Complex.cpow_add _ _ h0]
    push_cast
    rw [Complex.ofReal_cpow ht.1.le]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)),
    integral_cpow (Or.inl (by simp; linarith)), integral_cpow (Or.inl (by simp; linarith))]
  have h1 : (-(2 / 3 : ℂ) + -2 * s + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (-2 * s + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow h1,
    Complex.zero_cpow h2]
  have h3 : (1 / 3 - 2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h4 : (1 - 2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [show -(2 / 3 : ℂ) + -2 * s + 1 = 1 / 3 - 2 * s by ring,
    show (-2 * s + 1 : ℂ) = 1 - 2 * s by ring, sub_zero]

/-! ### Rational identities for the principal parts -/

theorem two_div_one_sub_sq {s : ℂ} (hs : s ≠ 1 / 2) :
    2 / (1 - 2 * s) ^ 2 = (1 / 2) / (s - 1 / 2) ^ 2 := by
  have h1 : s - 1 / 2 ≠ 0 := sub_ne_zero.2 hs
  have h2 : (1 - 2 * s) ≠ 0 := by
    intro h; apply h1; linear_combination -h / 2
  rw [div_eq_div_iff (pow_ne_zero 2 h2) (pow_ne_zero 2 h1)]
  ring

theorem one_div_one_sub {s : ℂ} (hs : s ≠ 1 / 2) :
    1 / (1 - 2 * s) = -(1 / 2) / (s - 1 / 2) := by
  have h1 : s - 1 / 2 ≠ 0 := sub_ne_zero.2 hs
  have h2 : (1 - 2 * s) ≠ 0 := by
    intro h; apply h1; linear_combination -h / 2
  rw [div_eq_div_iff h2 h1]
  ring

theorem one_div_third_sub {s : ℂ} (hs : s ≠ 1 / 6) :
    1 / (1 / 3 - 2 * s) = -(1 / 2) / (s - 1 / 6) := by
  have h1 : s - 1 / 6 ≠ 0 := sub_ne_zero.2 hs
  have h2 : (1 / 3 - 2 * s) ≠ 0 := by
    intro h; apply h1; linear_combination -h / 2
  rw [div_eq_div_iff h2 h1]
  ring

theorem polarPart_zero_apply (a : ℕ → ℂ) (μ s : ℂ) : polarPart 0 a μ s = a 0 / (s - μ) := by
  simp [polarPart]

theorem polarPart_one_apply (a : ℕ → ℂ) (μ s : ℂ) :
    polarPart 1 a μ s = a 0 / (s - μ) + a 1 / (s - μ) ^ 2 := by
  simp [polarPart, Finset.sum_range_succ]

theorem isOpen_re_lt (c : ℝ) : IsOpen {z : ℂ | z.re < c} :=
  isOpen_lt Complex.continuous_re continuous_const

/-! ### The log density `2 log(1/t)` -/

/-- The amplitude of the log density: `2 log(1/t) ψ(t)`. -/
noncomputable def logAmp (ψ : ℝ → ℝ) (t : ℝ) : ℂ := ((2 * Real.log (1 / t) * ψ t : ℝ) : ℂ)

/-- The Mellin transform of the log density with amplitude `ψ`:
`∫_0^1 2 log(1/t) ψ(t) t^{−2s} dt`. -/
noncomputable def logMellin (ψ : ℝ → ℝ) (s : ℂ) : ℂ := mellinIoc (logAmp ψ) s

/-- The remainder `∫_0^1 2 log(1/t) (ψ(t) − ψ(0)) t^{−2s} dt`, holomorphic on `Re s < 1`. -/
noncomputable def logRem (ψ : ℝ → ℝ) (s : ℂ) : ℂ := mellinIoc (logAmp fun t => ψ t - ψ 0) s

/-- The continuation `ψ(0) · 2/(1−2s)² + R_log(ψ, s)`. -/
noncomputable def logCont (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (ψ 0 : ℂ) * (2 / (1 - 2 * s) ^ 2) + logRem ψ s

theorem measurable_logAmp {ψ : ℝ → ℝ} (hψ : Measurable ψ) : Measurable (logAmp ψ) :=
  Complex.measurable_ofReal.comp ((measurable_const.mul
    (Real.measurable_log.comp (measurable_const.div measurable_id))).mul hψ)

theorem norm_logAmp_sub_le {ψ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {δ : ℝ} (hδ : 0 < δ) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logAmp (fun t => ψ t - ψ 0) t‖ ≤ 2 * L / δ * t ^ (1 - δ) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  unfold logAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
    one_div, Real.log_inv, abs_neg]
  calc 2 * |Real.log t| * |ψ t - ψ 0| ≤ 2 * (t ^ (-δ) / δ) * (L * t) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (abs_log_le_rpow_div hδ ht) (by norm_num))
          (hL t ht) (abs_nonneg _) (by positivity)
    _ = 2 * L / δ * t ^ (1 - δ) := by
        rw [show (1 : ℝ) - δ = 1 + -δ by ring, Real.rpow_add ht0, Real.rpow_one]
        field_simp

theorem nonneg_of_bound {ψ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) : 0 ≤ L :=
  (abs_nonneg _).trans (by simpa using hL 1 ⟨one_pos, le_rfl⟩)

/-- The log density on the strip: `∫_0^1 2 log(1/t) ψ(t) t^{−2s} dt = ψ(0)·2/(1−2s)² + R_log`. -/
theorem logMellin_eq {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {s : ℂ} (hs : s.re < 1 / 2) :
    logMellin ψ s = logCont ψ s := by
  unfold logMellin logCont logRem mellinIoc
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, logAmp ψ t * (t : ℂ) ^ (-2 * s) =
      (ψ 0 : ℂ) * ((t : ℂ) ^ (-2 * s) * (-2 * (Real.log t : ℂ))) +
        logAmp (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s) := by
    intro t _
    unfold logAmp
    rw [one_div, Real.log_inv]
    push_cast
    ring
  have hi1 := integrableOn_mellinIoc_log (g := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (C := 1) (b := 0) (fun t _ => by simp) (by simpa using hs)
  simp only [one_mul] at hi1
  have hi2 : IntegrableOn (fun t : ℝ => logAmp (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s))
      (Ioc (0 : ℝ) 1) := integrableOn_mellinIoc
    (measurable_logAmp (hψ.sub continuous_const).measurable).aestronglyMeasurable
    (norm_logAmp_sub_le hL (δ := 1 / 2) (by norm_num)) (s := s) (by norm_num; linarith)
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add (hi1.const_mul _) hi2,
    integral_const_mul, integral_cpow_log_Ioc hs]

/-- The remainder of the log density is holomorphic on `Re s < 1`. -/
theorem differentiableOn_logRem {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    DifferentiableOn ℂ (logRem ψ) {s : ℂ | s.re < 1} := by
  intro s hs
  have hs' : s.re < 1 := hs
  have hδpos : 0 < 1 - s.re := by linarith
  have hL0 := nonneg_of_bound hL
  exact (hasDerivAt_mellinIoc
    (measurable_logAmp (hψ.sub continuous_const).measurable).aestronglyMeasurable
    (C := 2 * L / (1 - s.re)) (div_nonneg (by linarith) hδpos.le)
    (norm_logAmp_sub_le hL hδpos) (by linarith)).differentiableAt.differentiableWithinAt

/-- ★★★ **The polar distribution of the log density at `½`**: the continuation has the principal
part `(ψ(0)/2)/(s − ½)²` and no simple pole — `C_{½,2} = ½ δ₀` on `(0,1]`, `C_{½,1} = 0`. -/
theorem logCont_sub_polarPart_isBigO {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    (fun s => logCont ψ s - polarPart 1 (fun q => if q = 1 then (ψ 0 : ℂ) / 2 else 0)
      (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | z.re < 1} := by
    simp only [mem_ofPred_eq]; norm_num
  have hcont : ContinuousAt (logRem ψ) (1 / 2) :=
    ((differentiableOn_logRem hψ hL).differentiableAt
      ((isOpen_re_lt 1).mem_nhds hmem)).continuousAt
  have hO : logRem ψ =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  beta_reduce
  unfold logCont
  rw [polarPart_one_apply, two_div_one_sub_sq hs]
  simp only [zero_ne_one, ↓reduceIte, zero_div, zero_add]
  ring

/-- Uniqueness: any bounded principal part of the log continuation at `½` has these coefficients. -/
theorem logCont_polarCoeff_unique {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {a : ℕ → ℂ}
    (h : (fun s => logCont ψ s - polarPart 1 a (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)]
      fun _ => (1 : ℂ)) :
    a 1 = (ψ 0 : ℂ) / 2 ∧ a 0 = 0 := by
  have key := polarPart_eq_of_sub_isBigO_one (D := 1) (a := a)
    (b := fun q => if q = 1 then (ψ 0 : ℂ) / 2 else 0) (μ := 1 / 2)
    (((logCont_sub_polarPart_isBigO hψ hL).sub h).congr_left fun s => by ring)
  exact ⟨by simpa using key 1 le_rfl, by simpa using key 0 zero_le_one⟩

/-! ### The mixed density `t^{−2/3} − 1` -/

/-- The amplitude of the mixed density: `(t^{−2/3} − 1) ψ(t)`. -/
noncomputable def mixAmp (ψ : ℝ → ℝ) (t : ℝ) : ℂ := (((t ^ (-(2 / 3 : ℝ)) - 1) * ψ t : ℝ) : ℂ)

noncomputable def mixMellin (ψ : ℝ → ℝ) (s : ℂ) : ℂ := mellinIoc (mixAmp ψ) s

noncomputable def mixRem (ψ : ℝ → ℝ) (s : ℂ) : ℂ := mellinIoc (mixAmp fun t => ψ t - ψ 0) s

/-- The continuation `ψ(0)(1/(⅓−2s) − 1/(1−2s)) + R_mix(ψ, s)`. -/
noncomputable def mixCont (ψ : ℝ → ℝ) (s : ℂ) : ℂ :=
  (ψ 0 : ℂ) * (1 / (1 / 3 - 2 * s) - 1 / (1 - 2 * s)) + mixRem ψ s

theorem measurable_mixAmp {ψ : ℝ → ℝ} (hψ : Measurable ψ) : Measurable (mixAmp ψ) :=
  Complex.measurable_ofReal.comp (((measurable_id.pow_const _).sub measurable_const).mul hψ)

theorem mixed_density_bounds {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ t ^ (-(2 / 3 : ℝ)) - 1 ∧ t ^ (-(2 / 3 : ℝ)) - 1 ≤ t ^ (-(2 / 3 : ℝ)) := by
  have h1 : 1 ≤ t ^ (-(2 / 3 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by norm_num)
  constructor <;> linarith

theorem norm_mixAmp_sub_le {ψ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖mixAmp (fun t => ψ t - ψ 0) t‖ ≤ L * t ^ (1 / 3 : ℝ) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  obtain ⟨hb0, hb1⟩ := mixed_density_bounds ht
  unfold mixAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb0]
  calc (t ^ (-(2 / 3 : ℝ)) - 1) * |ψ t - ψ 0| ≤ t ^ (-(2 / 3 : ℝ)) * (L * t) :=
        mul_le_mul hb1 (hL t ht) (abs_nonneg _) (by positivity)
    _ = L * t ^ (1 / 3 : ℝ) := by
        rw [show (1 / 3 : ℝ) = -(2 / 3) + 1 by norm_num, Real.rpow_add ht0, Real.rpow_one]
        ring

/-- The mixed density on the strip. -/
theorem mixedMellin_eq {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {s : ℂ} (hs : s.re < 1 / 6) :
    mixMellin ψ s = mixCont ψ s := by
  unfold mixMellin mixCont mixRem mellinIoc
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, mixAmp ψ t * (t : ℂ) ^ (-2 * s) =
      (ψ 0 : ℂ) * (((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s)) +
        mixAmp (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s) := by
    intro t _
    unfold mixAmp
    push_cast
    ring
  have hi1 := integrableOn_mellinIoc (g := fun t : ℝ => ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp ((measurable_id.pow_const _).sub
      measurable_const)).aestronglyMeasurable (C := 1) (b := -(2 / 3))
    (fun t ht => by
      obtain ⟨hb0, hb1⟩ := mixed_density_bounds ht
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0, one_mul]
      exact hb1) (s := s) (by norm_num; linarith)
  have hi2 : IntegrableOn (fun t : ℝ => mixAmp (fun t => ψ t - ψ 0) t * (t : ℂ) ^ (-2 * s))
      (Ioc (0 : ℝ) 1) := integrableOn_mellinIoc
    (measurable_mixAmp (hψ.sub continuous_const).measurable).aestronglyMeasurable
    (norm_mixAmp_sub_le hL) (s := s) (by norm_num; linarith)
  have hm := mellinIoc_mixed hs
  unfold mellinIoc at hm
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_add (hi1.const_mul _) hi2,
    integral_const_mul, hm]

/-- The remainder of the mixed density is holomorphic on `Re s < 2/3`. -/
theorem differentiableOn_mixedRem {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    DifferentiableOn ℂ (mixRem ψ) {s : ℂ | s.re < 2 / 3} := by
  have := differentiableOn_mellinIoc
    (measurable_mixAmp (hψ.sub continuous_const).measurable).aestronglyMeasurable
    (nonneg_of_bound hL) (norm_mixAmp_sub_le hL)
  rwa [show ((1 / 3 : ℝ) + 1) / 2 = 2 / 3 by norm_num] at this

/-- ★★★ **The polar distribution of the mixed density at `1/6`**: a simple pole with coefficient
`−ψ(0)/2` — `C_{1/6,1} = −½ δ₀` on `(0,1]`. -/
theorem mixCont_sub_polarPart_isBigO_sixth {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    (fun s => mixCont ψ s - polarPart 0 (fun _ => -(ψ 0 : ℂ) / 2) (1 / 6 : ℂ) s)
      =O[𝓝[≠] (1 / 6 : ℂ)] fun _ => (1 : ℂ) := by
  have hmem : (1 / 6 : ℂ) ∈ {z : ℂ | z.re < 2 / 3} := by
    simp only [mem_ofPred_eq]; norm_num
  have hrem : ContinuousAt (mixRem ψ) (1 / 6) :=
    ((differentiableOn_mixedRem hψ hL).differentiableAt
      ((isOpen_re_lt _).mem_nhds hmem)).continuousAt
  have hne : (1 : ℂ) - 2 * (1 / 6) ≠ 0 := by norm_num
  have hcont : ContinuousAt (fun s : ℂ => -(ψ 0 : ℂ) * (1 / (1 - 2 * s)) + mixRem ψ s)
      (1 / 6) :=
    (continuousAt_const.mul (continuousAt_const.div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hne)).add hrem
  have hO : (fun s : ℂ => -(ψ 0 : ℂ) * (1 / (1 - 2 * s)) + mixRem ψ s) =O[𝓝[≠] (1 / 6 : ℂ)]
      fun _ => (1 : ℂ) := (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  beta_reduce
  unfold mixCont
  rw [polarPart_zero_apply, one_div_third_sub hs]
  ring

/-- ★★★ **The polar distribution of the mixed density at `½`**: a simple pole with coefficient
`+ψ(0)/2` — `C_{½,1} = +½ δ₀` on `(0,1]`, the opposite sign. -/
theorem mixCont_sub_polarPart_isBigO_half {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) :
    (fun s => mixCont ψ s - polarPart 0 (fun _ => (ψ 0 : ℂ) / 2) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | z.re < 2 / 3} := by
    simp only [mem_ofPred_eq]; norm_num
  have hrem : ContinuousAt (mixRem ψ) (1 / 2) :=
    ((differentiableOn_mixedRem hψ hL).differentiableAt
      ((isOpen_re_lt _).mem_nhds hmem)).continuousAt
  have hne : (1 / 3 : ℂ) - 2 * (1 / 2) ≠ 0 := by norm_num
  have hcont : ContinuousAt (fun s : ℂ => (ψ 0 : ℂ) * (1 / (1 / 3 - 2 * s)) + mixRem ψ s)
      (1 / 2) :=
    (continuousAt_const.mul (continuousAt_const.div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) hne)).add hrem
  have hO : (fun s : ℂ => (ψ 0 : ℂ) * (1 / (1 / 3 - 2 * s)) + mixRem ψ s) =O[𝓝[≠] (1 / 2 : ℂ)]
      fun _ => (1 : ℂ) := (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  beta_reduce
  unfold mixCont
  rw [polarPart_zero_apply, one_div_one_sub hs]
  ring

theorem mixCont_polarCoeff_unique_sixth {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {a : ℕ → ℂ}
    (h : (fun s => mixCont ψ s - polarPart 0 a (1 / 6 : ℂ) s) =O[𝓝[≠] (1 / 6 : ℂ)]
      fun _ => (1 : ℂ)) : a 0 = -(ψ 0 : ℂ) / 2 :=
  polarPart_eq_of_sub_isBigO_one (D := 0) (a := a) (b := fun _ => -(ψ 0 : ℂ) / 2) (μ := 1 / 6)
    (((mixCont_sub_polarPart_isBigO_sixth hψ hL).sub h).congr_left fun s => by ring) 0 le_rfl

theorem mixCont_polarCoeff_unique_half {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ}
    (hL : ∀ t ∈ Ioc (0 : ℝ) 1, |ψ t - ψ 0| ≤ L * t) {a : ℕ → ℂ}
    (h : (fun s => mixCont ψ s - polarPart 0 a (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)]
      fun _ => (1 : ℂ)) : a 0 = (ψ 0 : ℂ) / 2 :=
  polarPart_eq_of_sub_isBigO_one (D := 0) (a := a) (b := fun _ => (ψ 0 : ℂ) / 2) (μ := 1 / 2)
    (((mixCont_sub_polarPart_isBigO_half hψ hL).sub h).congr_left fun s => by ring) 0 le_rfl

/-! ### Symmetrisation: the full interval `[−1, 1]` -/

/-- An even density against a general amplitude on `[−1, 1]` reduces to `(0, 1]` with the
symmetrised amplitude `φ(t) + φ(−t)`. -/
theorem integral_symm (f : ℝ → ℂ) (φ : ℝ → ℝ)
    (h₁ : IntervalIntegrable (fun t => f t * (φ t : ℂ)) volume 0 1)
    (h₂ : IntervalIntegrable (fun t => f t * (φ (-t) : ℂ)) volume 0 1) :
    ∫ t in (-1 : ℝ)..1, f |t| * (φ t : ℂ) = ∫ t in (0 : ℝ)..1, f t * ((φ t + φ (-t) : ℝ) : ℂ) := by
  have e₁ : ∫ t in (0 : ℝ)..1, f |t| * (φ t : ℂ) = ∫ t in (0 : ℝ)..1, f t * (φ t : ℂ) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      simp [abs_of_nonneg ht.1]
  have e₂ : ∫ t in (0 : ℝ)..1, f t * (φ (-t) : ℂ) = ∫ t in (-1 : ℝ)..0, f |t| * (φ t : ℂ) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1)
      (f := fun t => f |t| * (φ t : ℂ))
    simp only [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      simp [abs_of_nonneg ht.1]
  have h₂' : IntervalIntegrable (fun t => f |(-t)| * (φ (-t) : ℂ)) volume 0 1 := by
    refine h₂.congr fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    simp [abs_of_nonneg ht.1.le]
  have h₃ : IntervalIntegrable (fun t => f |t| * (φ t : ℂ)) volume (-1) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (a := 0) (b := 1)
      (f := fun t => f |(-t)| * (φ (-t) : ℂ))).1 h₂'
    simp only [neg_neg, neg_zero] at this
    exact this.symm
  have h₄ : IntervalIntegrable (fun t => f |t| * (φ t : ℂ)) volume 0 1 := by
    refine h₁.congr fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    simp [abs_of_nonneg ht.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals h₃ h₄, e₁, ← e₂,
    ← intervalIntegral.integral_add h₂ h₁]
  exact intervalIntegral.integral_congr fun t _ => by push_cast; ring

/-- The Mellin transform of the log density on `[−1, 1]`:
`∫_{−1}^1 2 log(1/|t|) φ(t) |t|^{−2s} dt`. -/
noncomputable def logMellinFull (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, ((2 * Real.log (1 / |t|) : ℝ) : ℂ) * ((|t| : ℝ) : ℂ) ^ (-2 * s) * (φ t : ℂ)

/-- The Mellin transform of the mixed density on `[−1, 1]`:
`∫_{−1}^1 (|t|^{−2/3} − 1) φ(t) |t|^{−2s} dt`. -/
noncomputable def mixMellinFull (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, ((|t| ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * ((|t| : ℝ) : ℂ) ^ (-2 * s) * (φ t : ℂ)

/-- The symmetrised amplitude. -/
def symmAmp (φ : ℝ → ℝ) (t : ℝ) : ℝ := φ t + φ (-t)

theorem symmAmp_zero (φ : ℝ → ℝ) : symmAmp φ 0 = 2 * φ 0 := by simp [symmAmp]; ring

theorem continuous_symmAmp {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (symmAmp φ) :=
  hφ.add (hφ.comp continuous_neg)

theorem symmAmp_bound {φ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc (0 : ℝ) 1, |symmAmp φ t - symmAmp φ 0| ≤ 2 * L * t := by
  intro t ht
  have h1 := hL t ⟨by linarith [ht.1], ht.2⟩
  have h2 := hL (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [abs_of_pos ht.1] at h1
  rw [abs_neg, abs_of_pos ht.1] at h2
  rw [symmAmp, symmAmp_zero]
  calc |φ t + φ (-t) - 2 * φ 0| = |(φ t - φ 0) + (φ (-t) - φ 0)| := by ring_nf
    _ ≤ |φ t - φ 0| + |φ (-t) - φ 0| := abs_add_le _ _
    _ ≤ 2 * L * t := by linarith

theorem bounded_of_bound {φ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Icc (-1 : ℝ) 1, |φ t| ≤ |φ 0| + L := by
  intro t ht
  have h := hL t ht
  have hL0 : 0 ≤ L := by
    have := hL 1 ⟨by norm_num, le_rfl⟩
    simp only [abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  have ht1 : |t| ≤ 1 := abs_le.2 ⟨ht.1, ht.2⟩
  calc |φ t| = |φ 0 + (φ t - φ 0)| := by ring_nf
    _ ≤ |φ 0| + |φ t - φ 0| := abs_add_le _ _
    _ ≤ |φ 0| + L := by nlinarith

/-- The log density on `[−1, 1]` is the half-line transform of the symmetrised amplitude. -/
theorem logMellinFull_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) {s : ℂ} (hs : s.re < 1 / 2) :
    logMellinFull φ s = logMellin (symmAmp φ) s := by
  have hM := bounded_of_bound hL
  -- integrability of the two half-line pieces
  have hint : ∀ χ : ℝ → ℝ, Continuous χ → (∀ t ∈ Ioc (0 : ℝ) 1, |χ t| ≤ |φ 0| + L) →
      IntervalIntegrable (fun t => ((2 * Real.log (1 / t) : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s) *
        (χ t : ℂ)) volume 0 1 := by
    intro χ hχ hχb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have := integrableOn_mellinIoc_log (g := fun t => (χ t : ℂ))
      (Complex.continuous_ofReal.comp hχ).measurable.aestronglyMeasurable (C := |φ 0| + L)
      (b := 0) (fun t ht => by
        rw [Real.rpow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact hχb t ht) (s := s) (by simpa using hs)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only
    rw [one_div, Real.log_inv]
    push_cast
    ring
  unfold logMellinFull logMellin mellinIoc
  have e := integral_symm (fun t => ((2 * Real.log (1 / t) : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s)) φ
    (hint φ hφ fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩)
    (hint (fun t => φ (-t)) (hφ.comp continuous_neg)
      fun t ht => hM (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  rw [e, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [logAmp, symmAmp]
  push_cast
  ring

/-- The mixed density on `[−1, 1]` is the half-line transform of the symmetrised amplitude. -/
theorem mixMellinFull_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) {s : ℂ} (hs : s.re < 1 / 6) :
    mixMellinFull φ s = mixMellin (symmAmp φ) s := by
  have hM := bounded_of_bound hL
  have hint : ∀ χ : ℝ → ℝ, Continuous χ → (∀ t ∈ Ioc (0 : ℝ) 1, |χ t| ≤ |φ 0| + L) →
      IntervalIntegrable (fun t => ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s) *
        (χ t : ℂ)) volume 0 1 := by
    intro χ hχ hχb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have := integrableOn_mellinIoc (g := fun t => ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * (χ t : ℂ))
      ((Complex.measurable_ofReal.comp ((measurable_id.pow_const _).sub measurable_const)).mul
        (Complex.continuous_ofReal.comp hχ).measurable).aestronglyMeasurable
      (C := |φ 0| + L) (b := -(2 / 3))
      (fun t ht => by
        obtain ⟨hb0, hb1⟩ := mixed_density_bounds ht
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hb0]
        calc (t ^ (-(2 / 3 : ℝ)) - 1) * |χ t| ≤ t ^ (-(2 / 3 : ℝ)) * (|φ 0| + L) :=
              mul_le_mul hb1 (hχb t ht) (abs_nonneg _) (Real.rpow_nonneg ht.1.le _)
          _ = (|φ 0| + L) * t ^ (-(2 / 3 : ℝ)) := by ring) (s := s) (by norm_num; linarith)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only
    ring
  unfold mixMellinFull mixMellin mellinIoc
  have e := integral_symm (fun t => ((t ^ (-(2 / 3 : ℝ)) - 1 : ℝ) : ℂ) * (t : ℂ) ^ (-2 * s)) φ
    (hint φ hφ fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩)
    (hint (fun t => φ (-t)) (hφ.comp continuous_neg)
      fun t ht => hM (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  rw [e, intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  simp only [mixAmp, symmAmp]
  push_cast
  ring

/-- ★★★ **The polar distribution of the log density `2 log(1/|t|)` on `[−1, 1]`**: the
continuation `logCont (symmAmp φ)` of `∫_{−1}^1 2 log(1/|t|) φ(t) |t|^{−2s} dt` (agreeing with it on
`Re s < ½`, `logMellinFull_eq`) has the principal part `φ(0)/(s − ½)²` at `½` and no simple
pole: `C_{½,2} = δ₀`, `C_{½,1} = 0`. -/
theorem logMellinFull_polar {φ : ℝ → ℝ} (hφ : Continuous φ) {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    (fun s => logCont (symmAmp φ) s - polarPart 1 (fun q => if q = 1 then (φ 0 : ℂ) else 0)
      (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have h := logCont_sub_polarPart_isBigO (continuous_symmAmp hφ) (symmAmp_bound hL)
  refine h.congr_left fun s => ?_
  simp only [symmAmp_zero]
  congr 2
  funext q
  split_ifs <;> push_cast <;> ring

/-- ★★★ **The polar distributions of the mixed density `|t|^{−2/3} − 1` on `[−1, 1]`**: simple
poles with coefficients `−φ(0)` at `1/6` and `+φ(0)` at `½`: `C_{1/6,1} = −δ₀`, `C_{½,1} = +δ₀`. -/
theorem mixMellinFull_polar {φ : ℝ → ℝ} (hφ : Continuous φ) {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ((fun s => mixCont (symmAmp φ) s - polarPart 0 (fun _ => -(φ 0 : ℂ)) (1 / 6 : ℂ) s)
        =O[𝓝[≠] (1 / 6 : ℂ)] fun _ => (1 : ℂ)) ∧
      ((fun s => mixCont (symmAmp φ) s - polarPart 0 (fun _ => (φ 0 : ℂ)) (1 / 2 : ℂ) s)
        =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ)) := by
  constructor
  · have h := mixCont_sub_polarPart_isBigO_sixth (continuous_symmAmp hφ) (symmAmp_bound hL)
    refine h.congr_left fun s => ?_
    simp only [symmAmp_zero]
    congr 2
    funext _
    push_cast
    ring
  · have h := mixCont_sub_polarPart_isBigO_half (continuous_symmAmp hφ) (symmAmp_bound hL)
    refine h.congr_left fun s => ?_
    simp only [symmAmp_zero]
    congr 2
    funext _
    push_cast
    ring

end Grammar
