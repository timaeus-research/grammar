/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThree

/-!
# The Gaussian-prior deep linear network at every depth: the leading asymptotic

The scalar recursion `Z_{L+1}(N) = ∫ g(x) Z_L(N x²) dx` (`gaussLaplaceL_succ_scalar`, the first
coordinate peeled and integrated last) propagates the leading asymptotic: if
`|f(t) − A (log t)^{m+1}/√t| ≤ C (1 + log t)^m/√t` for `t ≥ 1` with `0 ≤ f ≤ 1`, then
`F(N) = ∫ g(x) f(N x²) dx` satisfies the same with `A' = A/((m+2)√(2π))` and exponent `m+1`
(★★ `gaussianStep_bound`), and by induction from the depth-two case

  `|Z_{m+2}(N) − (log N)^{m+1}/((m+1)! √(2π)^{m+1} √N)| ≤ C_m (1 + log N)^m/√N`  for `N ≥ 1`
  (★★★ `gaussLaplaceL_leading_bound`),

so `√N Z_L(N)/(log N)^{L−1} → 1/((L−1)! (2π)^{(L−1)/2})` for every `L ≥ 2`
(★★★ `gaussLaplaceL_leading`): the leading coefficient of the note's eq. (dln_gauss) at every depth
(Astra round-8 target 3).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The scalar recursion at every depth -/

/-- **Bochner peel of the first coordinate, integrated first**:
`∫ F = ∫ a, ∫ b, F (a, b)` on `Fin (d+1) → ℝ`. -/
theorem integral_pi_succ (d : ℕ) (F : (Fin (d + 1) → ℝ) → ℝ) (hF : Integrable F) :
    ∫ x, F x = ∫ a : ℝ, ∫ b : Fin d → ℝ, F (Fin.cons a b) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin d → ℝ))) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  simp only [hsymm]

/-- ★★ **The scalar recursion**: `Z_{L+1}(N) = ∫ g(x) Z_L(N x²) dx` for `N ≥ 0`. -/
theorem gaussLaplaceL_succ_scalar (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL (L + 1) N = ∫ x : ℝ, gaussDensity x * gaussLaplaceL L (N * x ^ 2) := by
  unfold gaussLaplaceL
  rw [integral_pi_succ L _ (integrable_gaussLaplaceL (L + 1) hN)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show -N * (a * ∏ i, b i) ^ 2 / 2 = -(N * a ^ 2) * (∏ i, b i) ^ 2 / 2 by ring]
  ring

/-- `Z_L(N) ∈ [0, 1]` for `N ≥ 0`. -/
theorem gaussLaplaceL_nonneg (L : ℕ) (N : ℝ) : 0 ≤ gaussLaplaceL L N := by
  unfold gaussLaplaceL
  refine integral_nonneg fun w => ?_
  exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => gaussDensity_nonneg _)

theorem gaussLaplaceL_zero_eq_one (L : ℕ) : gaussLaplaceL L 0 = 1 := by
  unfold gaussLaplaceL
  simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, one_mul]
  rw [volume_pi, integral_fintype_prod_eq_pow (fun x : ℝ => gaussDensity x)]
  have h1 : ∫ x : ℝ, gaussDensity x = 1 := by
    have := gaussLaplace2_zero
    rw [gaussLaplace2_eq_density_integral le_rfl] at this
    simpa using this
  rw [h1, one_pow]

theorem gaussLaplaceL_le_one (L : ℕ) {N : ℝ} (hN : 0 ≤ N) : gaussLaplaceL L N ≤ 1 := by
  rw [← gaussLaplaceL_zero_eq_one L]
  unfold gaussLaplaceL
  refine integral_mono (integrable_gaussLaplaceL L hN) (integrable_gaussLaplaceL L le_rfl)
    fun w => ?_
  simp only
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => gaussDensity_nonneg _)
  exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hN (sq_nonneg (∏ i, w i))])

/-- The recursion integrand is integrable (Fubini on the pi space). -/
theorem integrable_density_mul_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun x : ℝ => gaussDensity x * gaussLaplaceL L (N * x ^ 2) := by
  have hF := integrable_gaussLaplaceL (L + 1) hN
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin L → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (L + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  set F : (Fin (L + 1) → ℝ) → ℝ := fun w =>
    Real.exp (-N * (∏ i, w i) ^ 2 / 2) * ∏ i, gaussDensity (w i) with hFdef
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin L → ℝ))) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod] at hint
  refine hint.integral_prod_left.congr (Eventually.of_forall fun a => ?_)
  simp only [hsymm, hFdef]
  unfold gaussLaplaceL
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show -N * (a * ∏ i, b i) ^ 2 / 2 = -(N * a ^ 2) * (∏ i, b i) ^ 2 / 2 by ring]
  ring

/-! ### Elementary estimates for the propagation step -/

theorem intervalIntegrable_pow_log_div {a : ℝ} (b : ℝ) (n : ℕ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun x => (b + 2 * Real.log x) ^ n / x) volume a 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hlogc : ContinuousOn Real.log (uIcc a 1) :=
    Real.continuousOn_log.mono fun x hx => by
      rw [uIcc_of_le ha1] at hx
      exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
  refine ContinuousOn.div (by fun_prop) continuousOn_id fun x hx => ?_
  rw [uIcc_of_le ha1] at hx
  exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)

/-- `∫_a^1 (b + 2 log x)^n / x dx = (b^{n+1} − (b + 2 log a)^{n+1})/(2(n+1))` for `0 < a ≤ 1`. -/
theorem integral_pow_log_div {a : ℝ} (b : ℝ) (n : ℕ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ x in Ioc a 1, (b + 2 * Real.log x) ^ n / x =
      (b ^ (n + 1) - (b + 2 * Real.log a) ^ (n + 1)) / (2 * (n + 1)) := by
  have hn : (0 : ℝ) < 2 * (n + 1) := by positivity
  have hderiv : ∀ x ∈ uIcc a 1, HasDerivAt (fun x => (b + 2 * Real.log x) ^ (n + 1) / (2 * (n + 1)))
      ((b + 2 * Real.log x) ^ n / x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hin : HasDerivAt (fun x : ℝ => b + 2 * Real.log x) (2 * x⁻¹) x :=
      ((Real.hasDerivAt_log hx0.ne').const_mul 2).const_add b
    have hout := (hasDerivAt_pow (n + 1) (b + 2 * Real.log x)).comp x hin
    have h := hout.div_const (2 * (n + 1))
    refine h.congr_deriv ?_
    push_cast
    field_simp
  have hint := intervalIntegrable_pow_log_div b n ha0 ha1
  rw [← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.log_one, mul_zero, add_zero]
  ring

/-- `x (1 + 2|log x|)^{n+1} ≤ (2n + 3)^{n+1}` on `(0, 1]`. -/
theorem mul_pow_one_add_log_le {x : ℝ} (n : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    x * (1 + 2 * |Real.log x|) ^ (n + 1) ≤ (2 * n + 3) ^ (n + 1) := by
  have hx0 : 0 < x := hx.1
  have hδ : (0 : ℝ) < 1 / (n + 1) := by positivity
  have hlog := abs_log_le_rpow_div hδ hx
  have hpow1 : 1 ≤ x ^ (-(1 / (n + 1) : ℝ)) := by
    rw [Real.rpow_neg hx0.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hx0 _) |>.2 (Real.rpow_le_one hx0.le hx.2 hδ.le)
  have h1 : 1 + 2 * |Real.log x| ≤ (2 * n + 3) * x ^ (-(1 / (n + 1) : ℝ)) := by
    have : |Real.log x| ≤ (n + 1) * x ^ (-(1 / (n + 1) : ℝ)) := by
      rw [div_div_eq_mul_div, div_one] at hlog
      linarith [hlog]
    nlinarith
  have h2 : (1 + 2 * |Real.log x|) ^ (n + 1) ≤
      ((2 * n + 3) * x ^ (-(1 / (n + 1) : ℝ))) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (x ^ (-(1 / (n + 1) : ℝ))) ^ (n + 1) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show (-(1 / (n + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ)) = -1 by push_cast; field_simp,
      Real.rpow_neg_one]
  rw [mul_pow, h3] at h2
  calc x * (1 + 2 * |Real.log x|) ^ (n + 1) ≤ x * ((2 * n + 3) ^ (n + 1) * x⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hx0.le
    _ = (2 * n + 3) ^ (n + 1) := by field_simp

/-- `x^n e^{−x²/2} ≤ n! e² e^{−x/2}` for `x ≥ 0`. -/
theorem pow_mul_exp_neg_half_sq_le {x : ℝ} (n : ℕ) (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x ^ 2 / 2) ≤ (n.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2) := by
  have h1 : x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx n
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : Real.exp x * Real.exp (-x ^ 2 / 2) ≤ Real.exp 2 * Real.exp (-x / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (x - 3 / 2)])
  calc x ^ n * Real.exp (-x ^ 2 / 2) ≤ (n.factorial : ℝ) * Real.exp x * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (Real.exp x * Real.exp (-x ^ 2 / 2)) := by ring
    _ ≤ (n.factorial : ℝ) * (Real.exp 2 * Real.exp (-x / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (n.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2) := by ring

/-! ### The propagation step -/

/-- The hypotheses of the propagation step: `0 ≤ f ≤ 1` on `t ≥ 0` and the leading asymptotic
`|f(t) − A (log t)^{m+1}/√t| ≤ C (1 + log t)^m/√t` for `t ≥ 1`. -/
structure LeadingData (f : ℝ → ℝ) (A C : ℝ) (m : ℕ) : Prop where
  A_nonneg : 0 ≤ A
  C_nonneg : 0 ≤ C
  f_nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  f_le_one : ∀ t, 0 ≤ t → f t ≤ 1
  bound : ∀ t, 1 ≤ t → |f t - A * (Real.log t) ^ (m + 1) / Real.sqrt t| ≤
    C * (1 + Real.log t) ^ m / Real.sqrt t

variable {f : ℝ → ℝ} {A C : ℝ} {m : ℕ}

/-- The inner piece `(0, a]`: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem step_inner_le (h : LeadingData f A C m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussDensity x * f (N * x ^ 2)) (C := 1 / Real.sqrt (2 * Real.pi))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      have h0 := h.f_nonneg (N * x ^ 2) (by positivity)
      have h1 := h.f_le_one (N * x ^ 2) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _) h0)]
      unfold gaussDensity
      calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * f (N * x ^ 2)
          ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right
              (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le) h1 h0 (by positivity)
        _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _)
  have hv : volume.real (Ioc (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), sub_zero]
  rwa [Real.norm_eq_abs, hv] at hb

/-- At `t = N x² ≥ 1`: `log t = log N + 2 log x`, `√t = √N x`. -/
theorem log_sqrt_mul_sq {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x ∧ Real.sqrt (N * x ^ 2) = Real.sqrt N * x :=
        by
  constructor
  · rw [Real.log_mul hN.ne' (by positivity), Real.log_pow]; push_cast; ring
  · rw [Real.sqrt_mul hN.le, Real.sqrt_sq hx.le]

theorem one_le_mul_sq_of_le {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N ≤ x) : 1 ≤ N * x ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h3 : (1 / Real.sqrt N) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
  have h4 : (1 / Real.sqrt N) ^ 2 * N = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hN0.le]; field_simp
  nlinarith

/-- The middle piece: with `P(x) = (log N + 2 log x)^{m+1}/(√N x)`,
`|∫_a^1 (g f(Nx²) − A P/√(2π))| ≤ (C + A(2m+3)^{m+1})(1 + log N)^{m+1}/(4√N)`. -/
theorem step_middle_le (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioc (1 / Real.sqrt N) 1, (gaussDensity x * f (N * x ^ 2) -
      1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))))| ≤
      (C + A * (2 * m + 3) ^ (m + 1)) * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  set K₁ : ℝ := (2 * m + 3) ^ (m + 1) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- the majorant
  set D : ℝ → ℝ := fun x => C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
    ((1 + Real.log N + 2 * Real.log x) ^ m / x) +
    A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) with hD
  have hDint : IntegrableOn D (Ioc (1 / Real.sqrt N) 1) := by
    rw [hD, ← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact ((intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1).const_mul _).add
      intervalIntegrable_const
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (1 / Real.sqrt N) 1))
    (f := fun x => gaussDensity x * f (N * x ^ 2) - 1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) hDint ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [hD, integral_add ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
        ((intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1).const_mul _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1 intervalIntegrable_const),
      integral_const_mul, integral_pow_log_div (1 + Real.log N) m ha0 ha1, setIntegral_const]
    have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
      rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
    have hv : volume.real (Ioc (1 / Real.sqrt N) 1) = 1 - 1 / Real.sqrt N := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [hloga, hv, smul_eq_mul, show 1 + Real.log N + 2 * -(Real.log N / 2) = 1 by ring, one_pow]
    have hp1 : 1 ≤ (1 + Real.log N) ^ (m + 1) := one_le_pow₀ (by linarith)
    have hp0 : 0 ≤ (1 + Real.log N) ^ (m + 1) := by positivity
    have h1 : C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) ≤
        C * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
      have hm1 : (1 : ℝ) ≤ 2 * (m + 1) := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [show C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) =
        C * (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : ((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) ≤ (1 + Real.log N) ^ (m + 1) / 2
          := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h3 : 0 ≤ C * ((1 + Real.log N) ^ (m + 1) / 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hC, mul_le_mul_of_nonneg_left hs2 h3,
        mul_le_mul_of_nonneg_left hs2 (mul_nonneg h3 hsN.le)]
    have h2 : (1 - 1 / Real.sqrt N) *
        (A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N)) ≤
        A * K₁ * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
      have hpos : 0 ≤ A * K₁ * (1 + Real.log N) ^ (m + 1) := by positivity
      calc (1 - 1 / Real.sqrt N) *
            (A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N))
          ≤ 1 * (A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N))
              :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ A * K₁ * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
            rw [one_mul]
            refine div_le_div_of_nonneg_left hpos (by positivity) ?_
            nlinarith
    calc C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) +
          (1 - 1 / Real.sqrt N) *
            (A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N))
        ≤ C * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) +
          A * K₁ * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := add_le_add h1 h2
      _ = (C + A * K₁) * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by ring
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := lt_trans ha0 hx.1
    have ht := one_le_mul_sq_of_le hN hx.1.le
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := h.bound (N * x ^ 2) ht
    rw [hlog, hsqrt] at hbd
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx.2
    have hg : 0 ≤ gaussDensity x := gaussDensity_nonneg x
    have hg1 : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
      unfold gaussDensity
      exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le
    have hgd : |gaussDensity x - 1 / Real.sqrt (2 * Real.pi)| ≤ x ^ 2 / (2 * Real.sqrt (2 *
        Real.pi)) := by
      unfold gaussDensity
      have h1 : Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) - 1 / Real.sqrt (2 * Real.pi) =
          -((1 - Real.exp (-x ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) := by ring
      rw [h1, abs_neg, abs_of_nonneg (div_nonneg (by
        linarith [Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x] : -x ^ 2 / 2 ≤ 0)]) hs.le),
        ← div_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.add_one_le_exp (-x ^ 2 / 2)]) hs.le
    -- the two pieces of the pointwise error
    set P : ℝ := (Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) with hP
    have hdec : gaussDensity x * f (N * x ^ 2) - 1 / Real.sqrt (2 * Real.pi) * (A * P) =
        gaussDensity x * (f (N * x ^ 2) - A * P) +
          (gaussDensity x - 1 / Real.sqrt (2 * Real.pi)) * (A * P) := by ring
    have hT1 : |gaussDensity x * (f (N * x ^ 2) - A * P)| ≤
        C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((1 + Real.log N + 2 * Real.log x) ^ m / x) := by
      rw [abs_mul, abs_of_nonneg hg]
      calc gaussDensity x * |f (N * x ^ 2) - A * P|
          ≤ 1 / Real.sqrt (2 * Real.pi) *
            (C * (1 + (Real.log N + 2 * Real.log x)) ^ m / (Real.sqrt N * x)) := by
            refine mul_le_mul hg1 ?_ (abs_nonneg _) (by positivity)
            rw [hP, ← mul_div_assoc]
            exact hbd
        _ = C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
            ((1 + Real.log N + 2 * Real.log x) ^ m / x) := by
            field_simp
            ring
    have hT2 : |(gaussDensity x - 1 / Real.sqrt (2 * Real.pi)) * (A * P)| ≤
        A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA]
      have hPabs : |P| ≤ (1 + Real.log N) ^ (m + 1) * (1 + 2 * |Real.log x|) ^ (m + 1) /
          (Real.sqrt N * x) := by
        rw [hP, abs_div, abs_pow, abs_of_pos (mul_pos hsN hx0)]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [← mul_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        calc |Real.log N + 2 * Real.log x| ≤ Real.log N + 2 * |Real.log x| := by
              rw [abs_le]; constructor <;> linarith [le_abs_self (Real.log x), neg_abs_le (Real.log
                  x)]
          _ ≤ (1 + Real.log N) * (1 + 2 * |Real.log x|) := by nlinarith [abs_nonneg (Real.log x)]
      have hxK : x * (1 + 2 * |Real.log x|) ^ (m + 1) ≤ K₁ := by
        rw [hK₁]; exact mul_pow_one_add_log_le m ⟨hx0, hx.2⟩
      calc |gaussDensity x - 1 / Real.sqrt (2 * Real.pi)| * (A * |P|)
          ≤ x ^ 2 / (2 * Real.sqrt (2 * Real.pi)) *
            (A * ((1 + Real.log N) ^ (m + 1) * (1 + 2 * |Real.log x|) ^ (m + 1) /
              (Real.sqrt N * x))) :=
            mul_le_mul hgd (mul_le_mul_of_nonneg_left hPabs hA) (by positivity) (by positivity)
        _ = A * (1 + Real.log N) ^ (m + 1) * (x * (1 + 2 * |Real.log x|) ^ (m + 1)) /
            (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
            field_simp
        _ ≤ A * (1 + Real.log N) ^ (m + 1) * K₁ / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
            gcongr
        _ = A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) := by
            ring
    rw [Real.norm_eq_abs, hD]
    simp only
    rw [hdec]
    calc |gaussDensity x * (f (N * x ^ 2) - A * P) +
          (gaussDensity x - 1 / Real.sqrt (2 * Real.pi)) * (A * P)|
        ≤ |gaussDensity x * (f (N * x ^ 2) - A * P)| +
          |(gaussDensity x - 1 / Real.sqrt (2 * Real.pi)) * (A * P)| := abs_add_le _ _
      _ ≤ _ := add_le_add hT1 hT2

/-- The tail `(1, ∞)`: `|∫₁^∞ g f(Nx²)| ≤ 8 (A + C) 3^{m+1} m! (1 + log N)^{m+1}/√N`. -/
theorem step_tail_le (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 : ℝ), gaussDensity x * f (N * x ^ 2)| ≤
      8 * (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  have he : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  set K : ℝ := (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * m.factorial * Real.exp 2 /
    (Real.sqrt (2 * Real.pi) * Real.sqrt N) with hK
  have hK0 : 0 ≤ K := by positivity
  have hmaj : IntegrableOn (fun x : ℝ => K * Real.exp (-x / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K) (fun w _ => ?_)
      measurableSet_Ioi
    congr 2
    ring
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun x => gaussDensity x * f (N * x ^ 2)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)]
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have hKle : K * (2 * Real.exp (-1 / 2)) ≤ K * 2 := by
      have := Real.exp_pos (-1 / 2)
      nlinarith
    refine hKle.trans ?_
    rw [hK, show (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * m.factorial * Real.exp 2 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt N) * 2 =
      (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) *
        (2 * Real.exp 2 / Real.sqrt (2 * Real.pi)) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    have hq : 2 * Real.exp 2 / Real.sqrt (2 * Real.pi) ≤ 8 := by
      rw [div_le_iff₀ hs]; nlinarith
    have hbase : 0 ≤ (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hq hbase]
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
    have ht := one_le_mul_sq_of_le (x := x) hN (ha1.trans hx.le)
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := (abs_le.1 (h.bound (N * x ^ 2) ht)).2
    rw [hlog, hsqrt] at hbd
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
    have hf0 := h.f_nonneg (N * x ^ 2) (by positivity)
    have hg0 := gaussDensity_nonneg x
    -- `f(Nx²) ≤ (A + C)(1 + log N + 2 log x)^{m+1}/(√N x) ≤ (A + C)(1 + log N)^{m+1} 3^{m+1}
    -- x^m/√N`
    have hbase : 0 ≤ Real.log N + 2 * Real.log x := by linarith
    have h1 : (Real.log N + 2 * Real.log x) ^ (m + 1) ≤
        (1 + Real.log N + 2 * Real.log x) ^ (m + 1) :=
      pow_le_pow_left₀ hbase (by linarith) _
    have h2 : (1 + (Real.log N + 2 * Real.log x)) ^ m ≤
        (1 + Real.log N + 2 * Real.log x) ^ (m + 1) := by
      rw [show 1 + (Real.log N + 2 * Real.log x) = 1 + Real.log N + 2 * Real.log x by ring]
      exact pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have h3 : 1 + Real.log N + 2 * Real.log x ≤ (1 + Real.log N) * (3 * x) := by
      nlinarith
    have h4 : (1 + Real.log N + 2 * Real.log x) ^ (m + 1) ≤
        (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1) := by
      calc (1 + Real.log N + 2 * Real.log x) ^ (m + 1) ≤ ((1 + Real.log N) * (3 * x)) ^ (m + 1) :=
            pow_le_pow_left₀ (by linarith) h3 _
        _ = (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1) := by
            rw [mul_pow, mul_pow]; ring
    have hf : f (N * x ^ 2) ≤ (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m /
        Real.sqrt N := by
      calc f (N * x ^ 2) ≤ A * (Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) +
            C * (1 + (Real.log N + 2 * Real.log x)) ^ m / (Real.sqrt N * x) := by linarith
        _ ≤ A * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) +
            C * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) := by
            gcongr
        _ = (A + C) * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) := by ring
        _ ≤ (A + C) * ((1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1)) /
            (Real.sqrt N * x) := by gcongr
        _ = (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m / Real.sqrt N := by
            field_simp
            ring
    have hxm := pow_mul_exp_neg_half_sq_le m hx0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hf0)]
    unfold gaussDensity
    calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * f (N * x ^ 2)
        ≤ Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
          ((A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (x ^ m * Real.exp (-x ^ 2 / 2)) := by
          field_simp
      _ ≤ (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((m.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)) :=
          mul_le_mul_of_nonneg_left hxm (by positivity)
      _ = K * Real.exp (-x / 2) := by rw [hK]; field_simp

/-- ★★ **The propagation step**: if `f` has the leading asymptotic `A (log t)^{m+1}/√t` with error
`C (1 + log t)^m/√t`, then `F(N) = ∫ g(x) f(N x²) dx` has the leading asymptotic
`A/((m+2)√(2π)) · (log N)^{m+2}/√N` with error `C' (1 + log N)^{m+1}/√N`,
`C' = 1 + (C + A(2m+3)^{m+1})/2 + 16(A + C)3^{m+1} m!`. -/
theorem gaussianStep_bound (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N)
    (hint : Integrable fun x => gaussDensity x * f (N * x ^ 2)) :
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      A / ((m + 2) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 2) / Real.sqrt N| ≤
      (1 + (C + A * (2 * m + 3) ^ (m + 1)) / 2 + 16 * (A + C) * 3 ^ (m + 1) * m.factorial) *
        (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  -- evenness
  have heven : ∫ x, gaussDensity x * f (N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => gaussDensity x * f (N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [gaussDensity, sq_abs]
  -- the split
  have hsplit : ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2)) +
        (∫ x in Ioc (1 / Real.sqrt N) 1, gaussDensity x * f (N * x ^ 2)) +
        ∫ x in Ioi (1 : ℝ), gaussDensity x * f (N * x ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
        hint.integrableOn,
      ← Ioc_union_Ioc_eq_Ioc ha0.le ha1,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hint.integrableOn
        hint.integrableOn]
  -- the main term on `(a, 1]`
  have hM : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) (Ioc (1 / Real.sqrt N)
          1) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 1) / x)
            := by
      intro x; field_simp
    simp_rw [e]
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact (intervalIntegrable_pow_log_div (Real.log N) (m + 1) ha0 ha1).const_mul _
  have hMval : ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))) =
      A / ((m + 2) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 2) / Real.sqrt N / 2 := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 1) / x)
            := by
      intro x; field_simp
    simp_rw [e]
    rw [integral_const_mul, integral_pow_log_div (Real.log N) (m + 1) ha0 ha1]
    have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
      rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
    rw [hloga, show Real.log N + 2 * -(Real.log N / 2) = 0 by ring, zero_pow (by omega), sub_zero]
    push_cast
    field_simp
    ring
  have hmid : ∫ x in Ioc (1 / Real.sqrt N) 1, gaussDensity x * f (N * x ^ 2) =
      (∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) +
      ∫ x in Ioc (1 / Real.sqrt N) 1, (gaussDensity x * f (N * x ^ 2) -
        1 / Real.sqrt (2 * Real.pi) *
          (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) := by
    rw [integral_sub hint.integrableOn hM]; ring
  have h0 := step_inner_le h hN0.le ha0.le
  have h1 := step_middle_le h hN
  have h2 := step_tail_le h hN
  rw [heven, hsplit, hmid, hMval]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2) with hI₀
  set E := ∫ x in Ioc (1 / Real.sqrt N) 1, (gaussDensity x * f (N * x ^ 2) -
    1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) with hE
  set T := ∫ x in Ioi (1 : ℝ), gaussDensity x * f (N * x ^ 2) with hT
  clear_value I₀ E T
  clear hI₀ hE hT hsplit hmid hMval hM heven
  set X := (1 + Real.log N) ^ (m + 1) / Real.sqrt N with hX
  have hX1 : 1 / Real.sqrt N ≤ X := by
    rw [hX]
    exact div_le_div_of_nonneg_right (one_le_pow₀ (by linarith)) hsN.le
  have hX0 : 0 ≤ X := by positivity
  set K₁ : ℝ := (2 * m + 3) ^ (m + 1) with hK₁
  set K₂ : ℝ := 8 * (A + C) * 3 ^ (m + 1) * m.factorial with hK₂
  have h1' : |E| ≤ (C + A * K₁) / 4 * X := by
    rw [hX]
    calc |E| ≤ (C + A * K₁) * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := h1
      _ = (C + A * K₁) / 4 * ((1 + Real.log N) ^ (m + 1) / Real.sqrt N) := by ring
  have h2' : |T| ≤ K₂ * X := by
    rw [hX]
    calc |T| ≤ 8 * (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) / Real.sqrt N :=
          h2
      _ = K₂ * ((1 + Real.log N) ^ (m + 1) / Real.sqrt N) := by rw [hK₂]; ring
  have h0' : |I₀| ≤ 1 / 2 * X := by
    calc |I₀| ≤ 1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N) := h0
      _ ≤ 1 / 2 * (1 / Real.sqrt N) := by
          gcongr
      _ ≤ 1 / 2 * X := by linarith
  clear_value X K₁ K₂
  have hkey : 2 * (I₀ + (A / ((m + 2) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 2) /
      Real.sqrt N / 2 + E) + T) -
      A / ((m + 2) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 2) / Real.sqrt N =
      2 * I₀ + 2 * E + 2 * T := by ring
  rw [hkey, show (16 : ℝ) * (A + C) * 3 ^ (m + 1) * m.factorial = 2 * K₂ by rw [hK₂]; ring,
    show (1 + (C + A * K₁) / 2 + 2 * K₂) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N =
      (1 + (C + A * K₁) / 2 + 2 * K₂) * X by rw [hX]; ring]
  rw [abs_le] at h0' h1' h2' ⊢
  constructor <;> nlinarith [h0'.1, h0'.2, h1'.1, h1'.2, h2'.1, h2'.2]

/-! ### The induction on the depth -/

/-- `Z_2 = gaussLaplace2` (the pair transported to `Fin 2 → ℝ`). -/
theorem gaussLaplaceL_two (N : ℝ) : gaussLaplaceL 2 N = gaussLaplace2 N := by
  unfold gaussLaplaceL gaussLaplace2
  have hmp := volume_preserving_finTwoArrow ℝ
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) with he
  set G : ℝ × ℝ → ℝ := fun p => Real.exp (-N * (p.1 * p.2) ^ 2 / 2) *
    (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi)) with hG
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hcomp : ∀ b : Fin 2 → ℝ, Real.exp (-N * (∏ i, b i) ^ 2 / 2) * ∏ i, gaussDensity (b i) =
      G (e b) := by
    intro b
    simp only [hG, he, MeasurableEquiv.finTwoArrow_apply, Fin.prod_univ_two, gaussDensity]
    rw [show Real.exp (-(b 0 ^ 2 + b 1 ^ 2) / 2) = Real.exp (-b 0 ^ 2 / 2) * Real.exp (-b 1 ^ 2 /
        2) by
      rw [← Real.exp_add]; ring_nf]
    generalize hsdef : Real.sqrt (2 * Real.pi) = s at hsq ⊢
    rw [← hsq]
    field_simp
  simp_rw [hcomp]
  exact hmp.integral_comp e.measurableEmbedding G

/-- The depth-two base of the induction: `A = 1/√(2π)`, `C = 5/2`, `m = 0`. -/
theorem leadingData_two : LeadingData gaussLaplace2 (1 / Real.sqrt (2 * Real.pi)) (5 / 2) 0 where
  A_nonneg := by positivity
  C_nonneg := by norm_num
  f_nonneg t ht := gaussLaplace2_nonneg ht
  f_le_one t ht := gaussLaplace2_le_one ht
  bound t ht := by
    have ht0 : 0 < t := by linarith
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
    obtain ⟨hb, -⟩ := gaussLaplace2_bounds ht
    obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
    have hrem : (Real.log (2 * t) + 3) / (2 * t * (Real.sqrt (2 * Real.pi) * Real.sqrt t)) ≤
        2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by
      have hlog : Real.log (2 * t) ≤ 2 * t - 1 := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hs hst]
    have hb2 := (abs_le.1 hb)
    simp only [zero_add, pow_one, pow_zero, mul_one]
    rw [abs_le]
    have e1 : 1 / Real.sqrt (2 * Real.pi) * Real.log t / Real.sqrt t =
        Real.log t / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by field_simp
    have e2 : (Real.log t + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt t) = Real.log t / (Real.sqrt (2 * Real.pi) * Real.sqrt
            t) +
        (3 * Real.log 2 - Real.eulerMascheroniConstant) / (Real.sqrt (2 * Real.pi) * Real.sqrt t)
            := by
      ring
    rw [e2] at hb2
    have hcs : (3 * Real.log 2 - Real.eulerMascheroniConstant) / (Real.sqrt (2 * Real.pi) *
        Real.sqrt t) ≤
        3 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := div_le_div_of_nonneg_right hc3 (by
            positivity)
    have hcs0 : 0 ≤ (3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt t) := div_nonneg (by linarith) (by positivity)
    have h5 : 5 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) ≤ 5 / 2 / Real.sqrt t := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hs2 hst.le]
    have h35 : 2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) + 3 / (Real.sqrt (2 * Real.pi) *
        Real.sqrt t) =
        5 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by ring
    rw [e1]
    constructor <;> linarith [hb2.1, hb2.2]

/-- ★★★ **The leading asymptotic at every depth**: for every `m`, there is `C_m` with
`|Z_{m+2}(N) − (log N)^{m+1}/((m+1)! √(2π)^{m+1} √N)| ≤ C_m (1 + log N)^m/√N` for all `N ≥ 1`
(packaged as the leading data of `Z_{m+2}`). -/
theorem gaussLaplaceL_leading_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    LeadingData (gaussLaplaceL (m + 2))
      (1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1))) C m := by
  induction m with
  | zero =>
    refine ⟨5 / 2, by norm_num, ?_⟩
    have e : gaussLaplaceL 2 = gaussLaplace2 := funext gaussLaplaceL_two
    rw [e]
    simpa using leadingData_two
  | succ m ih =>
    obtain ⟨C, hC, hd⟩ := ih
    set A := 1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)) with hA
    have hA0 : 0 ≤ A := hd.A_nonneg
    refine ⟨1 + (C + A * (2 * m + 3) ^ (m + 1)) / 2 + 16 * (A + C) * 3 ^ (m + 1) * m.factorial,
      by positivity, ?_⟩
    have hA' : 1 / ((m + 1 + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1 + 1)) =
        A / ((m + 2) * Real.sqrt (2 * Real.pi)) := by
      rw [hA, Nat.factorial_succ]
      have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
      push_cast
      field_simp
      ring
    refine ⟨by rw [hA']; positivity, by positivity, fun t _ => gaussLaplaceL_nonneg _ t,
      fun t ht => gaussLaplaceL_le_one _ ht, fun t ht => ?_⟩
    have hint := integrable_density_mul_gaussLaplaceL (m + 2) (by linarith : (0 : ℝ) ≤ t)
    have h := gaussianStep_bound hd ht hint
    rw [← gaussLaplaceL_succ_scalar (m + 2) (by linarith)] at h
    rw [hA']
    exact h

/-- ★★★ `√N Z_L(N)/(log N)^{L−1} → 1/((L−1)! (2π)^{(L−1)/2})` for every depth `L = m + 2 ≥ 2`. -/
theorem gaussLaplaceL_leading (m : ℕ) :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1)) atTop
      (𝓝 (1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)))) := by
  obtain ⟨C, hC, hd⟩ := gaussLaplaceL_leading_bound m
  set A := 1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)) with hA
  clear_value A
  have hbound : ∀ᶠ N : ℝ in atTop,
      |Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1) - A| ≤
        C * 2 ^ m / Real.log N := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log N := by linarith
    have h := hd.bound N hN
    have e : Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1) - A =
        (Real.sqrt N / (Real.log N) ^ (m + 1)) *
          (gaussLaplaceL (m + 2) N - A * (Real.log N) ^ (m + 1) / Real.sqrt N) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hpow : (1 + Real.log N) ^ m ≤ (2 * Real.log N) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    calc Real.sqrt N / (Real.log N) ^ (m + 1) *
          |gaussLaplaceL (m + 2) N - A * (Real.log N) ^ (m + 1) / Real.sqrt N|
        ≤ Real.sqrt N / (Real.log N) ^ (m + 1) * (C * (1 + Real.log N) ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * (1 + Real.log N) ^ m / (Real.log N) ^ (m + 1) := by field_simp
      _ ≤ C * (2 * Real.log N) ^ m / (Real.log N) ^ (m + 1) := by gcongr
      _ = C * 2 ^ m / Real.log N := by
          rw [mul_pow, pow_succ]
          field_simp
  have hlim : Tendsto (fun N : ℝ => C * 2 ^ m / Real.log N) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (C * 2 ^ m)
    simpa [div_eq_mul_inv] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [hbound] with N hN
  rw [Real.norm_eq_abs]
  exact hN

end Grammar
