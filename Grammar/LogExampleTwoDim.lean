/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ProductUniformLog
import Grammar.MellinLogWeights

/-!
# A two-dimensional example with a logarithm and a `∂_ν S_ν` weight (§20, consult #146/#147)

`K = x²y²` on `(0,1]²`, `h = 0`, constant field `a`: the ratios `(hᵢ+1)/(2kᵢ) = 1/2` coincide, so
`λ = 1/2` with multiplicity `2` and the leading term carries `log n`. Exactly
(★ `logExample_eq`):
`∫_0^1∫_0^1 e^{−n x²y² + a√n xy} dx dy = (4√n)⁻¹ ∫_0^n t^{−1/2} e^{−t + a√t} (log n − log t) dt`
(the product `u = xy` has density `−log u`, then `t = n u²`), and asymptotically
(★★ `tendsto_logExample`):
`4√n · I(n) − (S_{1/2}(a) log n − ∂_ν S_ν(a)|_{ν=1/2}) → 0`, with `∂_ν S_ν(a)|_{1/2} =
∫_0^∞ t^{−1/2} (log t) e^{−t+a√t} dt` (`iteratedDeriv_fluctuation_eq`). The coefficient of
`n^{−1/2}` is a genuine index derivative of the fluctuation function: the lower logarithmic weight
of `MellinLogWeights` appears concretely. At `a = 0` the two constants are `Γ(1/2)` and `Γ'(1/2)`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace Grammar

namespace SmoothEngine

/-- The two-dimensional example integral `∫_0^1∫_0^1 e^{−n(xy)² + a√n·xy} dy dx`. -/
noncomputable def logExample (a n : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, exp (-n * (x * y) ^ 2 + a * Real.sqrt n * (x * y))

/-- The radial integrand `t^{−1/2} e^{−t + a√t}`. -/
noncomputable def radial (a t : ℝ) : ℝ := t ^ (-(1 / 2 : ℝ)) * exp (-t + a * Real.sqrt t)

theorem continuousOn_radial (a : ℝ) : ContinuousOn (radial a) (Ioi 0) := by
  unfold radial
  exact (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)).mul
    (continuous_exp.comp (by fun_prop)).continuousOn

theorem integrableOn_radial (a : ℝ) : IntegrableOn (radial a) (Ioi 0) := by
  have h := integrableOn_fluctuationLog_integrand (ν := 1 / 2) (by norm_num) a 0
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [radial, pow_zero, mul_one]
  congr 2
  norm_num

theorem integrableOn_radial_log (a : ℝ) :
    IntegrableOn (fun t => radial a t * Real.log t) (Ioi 0) := by
  have h := integrableOn_fluctuationLog_integrand (ν := 1 / 2) (by norm_num) a 1
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [radial, pow_one]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  ring

/-- The density identity: `∫_0^1∫_0^1 φ(xy) = ∫_0^1 φ(u)(−log u)` for the example integrand. -/
theorem logExample_eq_neg_log (a n : ℝ) :
    logExample a n =
      ∫ u in (0 : ℝ)..1, exp (-n * u ^ 2 + a * Real.sqrt n * u) * (-Real.log u) := by
  unfold logExample
  exact integral_integral_mul_eq_neg_log (φ := fun u => exp (-n * u ^ 2 + a * Real.sqrt n * u))
    (continuous_exp.comp (by fun_prop)).continuousOn

/-- ★ **The exact radial form**: for `n > 0`,
`I(n) = (4√n)⁻¹ ∫_0^n t^{−1/2} e^{−t + a√t} (log n − log t) dt`. -/
theorem logExample_eq {a n : ℝ} (hn : 0 < n) :
    logExample a n =
      (4 * Real.sqrt n)⁻¹ * ∫ t in (0 : ℝ)..n, radial a t * (Real.log n - Real.log t) := by
  rw [logExample_eq_neg_log]
  set f : ℝ → ℝ := fun u => n * u ^ 2 with hf
  set f' : ℝ → ℝ := fun u => 2 * n * u with hf'
  set g : ℝ → ℝ := fun t => (4 * Real.sqrt n)⁻¹ * (radial a t * (Real.log n - Real.log t)) with hg
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  -- the integrand identity on `[0,1]`
  have hpt : ∀ u ∈ Icc (0 : ℝ) 1, exp (-n * u ^ 2 + a * Real.sqrt n * u) * (-Real.log u) =
      (g ∘ f) u * f' u := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hu0
    · subst h0
      simp [hf', hg, hf]
    · simp only [Function.comp, hg, hf, hf', radial]
      have h1 : Real.sqrt (n * u ^ 2) = Real.sqrt n * u := by
        rw [Real.sqrt_mul hn.le, Real.sqrt_sq hu0.le]
      have h2 : (n * u ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n * u)⁻¹ := by
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, h1]
      have h3 : Real.log (n * u ^ 2) = Real.log n + 2 * Real.log u := by
        rw [Real.log_mul hn.ne' (by positivity), Real.log_pow]
        push_cast
        ring
      have hn' : (2 : ℝ) * n * u = 2 * (Real.sqrt n * Real.sqrt n) * u := by
        rw [Real.mul_self_sqrt hn.le]
      rw [h1, h2, h3, hn']
      field_simp
      ring
  have hcong : EqOn (fun u => exp (-n * u ^ 2 + a * Real.sqrt n * u) * (-Real.log u))
      (fun u => (g ∘ f) u * f' u) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact hpt
  rw [intervalIntegral.integral_congr hcong]
  have hfc : ContinuousOn f (uIcc 0 1) := (by fun_prop : Continuous f).continuousOn
  have hff' : ∀ u ∈ Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivWithinAt f (f' u) (Ioi u) u := by
    intro u _
    have : HasDerivAt f (2 * n * u) u := by
      have := ((hasDerivAt_pow 2 u).const_mul n)
      simpa [hf, mul_comm, mul_assoc, mul_left_comm] using this
    exact this.hasDerivWithinAt
  have himg1 : f '' Ioo (min (0 : ℝ) 1) (max 0 1) ⊆ Ioi 0 := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at hu
    change 0 < n * u ^ 2
    exact mul_pos hn (pow_pos hu.1 2)
  have himg2 : f '' uIcc (0 : ℝ) 1 ⊆ Icc 0 n := by
    rintro _ ⟨u, hu, rfl⟩
    rw [uIcc_of_le zero_le_one] at hu
    refine ⟨?_, ?_⟩
    · show 0 ≤ n * u ^ 2
      positivity
    change n * u ^ 2 ≤ n
    have : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    nlinarith
  have hgc : ContinuousOn g (f '' Ioo (min (0 : ℝ) 1) (max 0 1)) := by
    refine ContinuousOn.mono ?_ himg1
    exact continuousOn_const.mul ((continuousOn_radial a).mul
      (continuousOn_const.sub (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)))
  have hgint : IntegrableOn g (Icc 0 n) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    have h1 : IntegrableOn (fun t => radial a t * (Real.log n - Real.log t)) (Ioi 0) := by
      have this : IntegrableOn (fun t => Real.log n * radial a t - radial a t * Real.log t)
          (Ioi 0) :=
        ((integrableOn_radial a).const_mul (Real.log n)).sub (integrableOn_radial_log a)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      ring
    exact ((h1.mono_set Ioc_subset_Ioi_self).const_mul _)
  have hgint1 : IntegrableOn g (f '' uIcc (0 : ℝ) 1) := hgint.mono_set himg2
  have hgint2 : IntegrableOn (fun u => (g ∘ f) u * f' u) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one, ← intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    have : IntervalIntegrable (fun u => exp (-n * u ^ 2 + a * Real.sqrt n * u) * (-Real.log u))
        volume 0 1 := by
      have := intervalIntegrable_log'.neg.continuousOn_mul (a := (0 : ℝ)) (b := 1)
        (g := fun u => exp (-n * u ^ 2 + a * Real.sqrt n * u))
        (continuous_exp.comp (by fun_prop)).continuousOn
      simpa using this
    refine this.congr ?_
    rw [uIoc_of_le zero_le_one]
    intro u hu
    exact hpt u ⟨hu.1.le, hu.2⟩
  rw [intervalIntegral.integral_comp_mul_deriv''' hfc hff' hgc hgint1 hgint2]
  simp only [hf, mul_zero, zero_pow two_ne_zero, one_pow, mul_one]
  rw [intervalIntegral.integral_const_mul]

/-! ### The asymptotics -/

theorem radial_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ radial a t :=
  mul_nonneg (Real.rpow_nonneg ht _) (exp_pos _).le

/-- For `t ≥ 1`: `radial a t ≤ e^{a²/2} e^{−t/4} e^{−t/4}` (AM–GM `a√t ≤ t/2 + a²/2`). -/
theorem radial_le_of_one_le (a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    radial a t ≤ exp (a ^ 2 / 2) * exp (-(t / 4)) * exp (-(t / 4)) := by
  unfold radial
  have h1 : t ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have h2 : exp (-t + a * Real.sqrt t) ≤ exp (a ^ 2 / 2) * exp (-(t / 4)) * exp (-(t / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt (zero_le_one.trans ht)]
  calc t ^ (-(1 / 2 : ℝ)) * exp (-t + a * Real.sqrt t) ≤ 1 * exp (-t + a * Real.sqrt t) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp (-t + a * Real.sqrt t) := one_mul _
    _ ≤ _ := h2

theorem integrableOn_exp_neg_quarter : IntegrableOn (fun t : ℝ => exp (-(t / 4))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1 / 4) (by norm_num)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  ring_nf

/-- The tail `∫_{t>n} radial a t` is `O(e^{−n/4})`. -/
theorem tail_radial_le (a : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    ∫ t in Ioi n, radial a t ≤
      exp (a ^ 2 / 2) * exp (-(n / 4)) * ∫ t in Ioi (0 : ℝ), exp (-(t / 4)) := by
  have hint := integrableOn_exp_neg_quarter
  have hpos : 0 < n := zero_lt_one.trans_le hn
  have hstep : ∫ t in Ioi n, radial a t ≤
      ∫ t in Ioi n, exp (a ^ 2 / 2) * exp (-(n / 4)) * exp (-(t / 4)) := by
    refine setIntegral_mono_on ((integrableOn_radial a).mono_set (Ioi_subset_Ioi hpos.le))
      ((hint.mono_set (Ioi_subset_Ioi hpos.le)).const_mul _) measurableSet_Ioi fun t ht => ?_
    have htn : n < t := ht
    have ht' : 1 ≤ t := hn.trans htn.le
    refine (radial_le_of_one_le a ht').trans ?_
    have : exp (-(t / 4)) ≤ exp (-(n / 4)) := Real.exp_le_exp.2 (by linarith)
    gcongr
  have hmono : ∫ t in Ioi n, exp (-(t / 4)) ≤ ∫ t in Ioi (0 : ℝ), exp (-(t / 4)) :=
    setIntegral_mono_set hint (Eventually.of_forall fun t => (exp_pos _).le)
      (Eventually.of_forall (Ioi_subset_Ioi hpos.le))
  calc ∫ t in Ioi n, radial a t
      ≤ ∫ t in Ioi n, exp (a ^ 2 / 2) * exp (-(n / 4)) * exp (-(t / 4)) := hstep
    _ = exp (a ^ 2 / 2) * exp (-(n / 4)) * ∫ t in Ioi n, exp (-(t / 4)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ exp (a ^ 2 / 2) * exp (-(n / 4)) * ∫ t in Ioi (0 : ℝ), exp (-(t / 4)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)

theorem tail_radial_nonneg (a : ℝ) {n : ℝ} (hn : 0 ≤ n) : 0 ≤ ∫ t in Ioi n, radial a t :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => radial_nonneg a (hn.trans (le_of_lt ht))

theorem fluctuation_half_eq (a : ℝ) : fluctuation 1 (1 / 2) a = ∫ t in Ioi (0 : ℝ), radial a t := by
  rw [← fluctuationLog_zero]
  unfold fluctuationLog
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [radial, pow_zero, mul_one]
  congr 2
  norm_num

theorem deriv_fluctuation_half_eq (a : ℝ) :
    deriv (fun ν => fluctuation 1 ν a) (1 / 2) = ∫ t in Ioi (0 : ℝ), radial a t * Real.log t := by
  rw [← iteratedDeriv_one, iteratedDeriv_fluctuation_eq (by norm_num) a 1]
  unfold fluctuationLog
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [radial, pow_one]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  ring

/-- The exact decomposition for `n ≥ 1`:
`4√n·I(n) − (S log n − L) = −log n · ∫_{t>n} radial − (∫_0^n radial·log − L)`. -/
theorem logExample_decomp (a : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    4 * Real.sqrt n * logExample a n -
      (Real.log n * (∫ t in Ioi (0 : ℝ), radial a t) -
        ∫ t in Ioi (0 : ℝ), radial a t * Real.log t) =
    -(Real.log n * ∫ t in Ioi n, radial a t) -
      ((∫ t in (0 : ℝ)..n, radial a t * Real.log t) -
        ∫ t in Ioi (0 : ℝ), radial a t * Real.log t) := by
  have hpos : 0 < n := zero_lt_one.trans_le hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hpos
  rw [logExample_eq hpos, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hA : ∫ t in (0 : ℝ)..n, radial a t =
      (∫ t in Ioi (0 : ℝ), radial a t) - ∫ t in Ioi n, radial a t := by
    have hunion := setIntegral_union (μ := volume) (f := radial a)
      (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := n)) measurableSet_Ioi
      ((integrableOn_radial a).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_radial a).mono_set (Ioi_subset_Ioi hpos.le))
    rw [Ioc_union_Ioi_eq_Ioi hpos.le] at hunion
    rw [intervalIntegral.integral_of_le hpos.le]
    linarith
  have h1 : IntervalIntegrable (radial a) volume 0 n :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le).2
      ((integrableOn_radial a).mono_set Ioc_subset_Ioi_self)
  have h2 : IntervalIntegrable (fun t => radial a t * Real.log t) volume 0 n :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le).2
      ((integrableOn_radial_log a).mono_set Ioc_subset_Ioi_self)
  have hsplit : ∫ t in (0 : ℝ)..n, radial a t * (Real.log n - Real.log t) =
      Real.log n * (∫ t in (0 : ℝ)..n, radial a t) -
        ∫ t in (0 : ℝ)..n, radial a t * Real.log t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (h1.const_mul _) h2]
    congr 1
    funext t
    ring
  rw [hsplit, hA]
  ring

/-- ★★ **The two-dimensional log asymptotics**:
`4√n · I(n) − (S_{1/2}(a) log n − ∂_ν S_ν(a)|_{ν=1/2}) → 0` as `n → ∞`. -/
theorem tendsto_logExample (a : ℝ) :
    Tendsto (fun n : ℝ => 4 * Real.sqrt n * logExample a n -
      (Real.log n * fluctuation 1 (1 / 2) a - deriv (fun ν => fluctuation 1 ν a) (1 / 2)))
      atTop (𝓝 0) := by
  rw [fluctuation_half_eq, deriv_fluctuation_half_eq]
  set K : ℝ := exp (a ^ 2 / 2) * ∫ t in Ioi (0 : ℝ), exp (-(t / 4)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (exp_pos _).le
    (setIntegral_nonneg measurableSet_Ioi fun t _ => (exp_pos _).le)
  -- the tail term tends to zero
  have htail : Tendsto (fun n : ℝ => Real.log n * ∫ t in Ioi n, radial a t) atTop (𝓝 0) := by
    have hbig : Tendsto (fun n : ℝ => K * (4 * ((n / 4) ^ 1 * exp (-(n / 4))))) atTop (𝓝 0) := by
      have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))
      have h' := (h.const_mul 4).const_mul K
      simpa [Function.comp] using h'
    refine squeeze_zero' ?_ ?_ hbig
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
      exact mul_nonneg (Real.log_nonneg hn) (tail_radial_nonneg a (zero_le_one.trans hn))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
      have hpos : 0 < n := zero_lt_one.trans_le hn
      have hlog : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
      calc Real.log n * ∫ t in Ioi n, radial a t
          ≤ n * (exp (a ^ 2 / 2) * exp (-(n / 4)) * ∫ t in Ioi (0 : ℝ), exp (-(t / 4))) :=
            mul_le_mul hlog (tail_radial_le a hn) (tail_radial_nonneg a hpos.le) hpos.le
        _ = K * (4 * ((n / 4) ^ 1 * exp (-(n / 4)))) := by
            rw [hK]
            ring
  -- the log-weighted integral converges
  have hB : Tendsto (fun n : ℝ => ∫ t in (0 : ℝ)..n, radial a t * Real.log t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), radial a t * Real.log t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_radial_log a) tendsto_id
  have hlim := htail.neg.sub (hB.sub_const (∫ t in Ioi (0 : ℝ), radial a t * Real.log t))
  rw [neg_zero, sub_self, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
  exact (logExample_decomp a hn).symm

end SmoothEngine

end Grammar
