/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalIntegratedPolar

/-!
# Log moments of the chart zeta functional and the coupling interchange (route B, unit B13a)

Three analytic/algebraic inputs for the coupling-average form (B4) of the empirical polar
coefficients.

* **Box log moments.**
  `chartZetaLogMoment G h k n s = ∫_{(0,1]^ι} G(w) w^{h−2ks} (−2 logSum k w)^n dw`;
  for a `p`-flat amplitude these are the derivatives of the chart zeta functional on the flat
  strip (★ `iteratedDeriv_chartZeta_flat`), by the dominated differentiation of unit 2 with the
  polynomial log factor.
* **The binomial split of the coupled log moments.**  Expanding `(log t − 2 logSum k w)^n`,
  `coupledLogMoment H h k n s = Σ_{a ≤ n} C(n,a) ∫_0^∞ t^{s−1} e^{−t} (log t)^a
  chartZetaLogMoment (H √t) h k (n−a) s dt` (★ `coupledLogMoment_eq_sum`), with the marginal
  integrability of every term.
* **Normalised Leibniz.**  With `taylorCoeff f μ n = f^{(n)}(μ)/n!`, the Taylor coefficients of a
  product of functions analytic at `μ` are the Cauchy product (`taylorCoeff_mul`, from Mathlib's
  `iteratedDeriv_fun_mul`).
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Box log moments -/

section BoxMoments

variable {ι : Type*} [Fintype ι]

/-- The `n`-th box log moment `∫ G(w) w^{h−2ks} (−2 logSum k w)^n dw`. -/
noncomputable def chartZetaLogMoment (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in SmoothEngine.box ι 1,
    (G u : ℂ) * cpowWeight h k s u * ((-2 : ℂ) * (logSum k u : ℂ)) ^ n

theorem chartZetaLogMoment_zero (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (s : ℂ) :
    chartZetaLogMoment G h k 0 s = chartZeta G h k s := by
  unfold chartZetaLogMoment chartZeta
  simp only [pow_zero, mul_one]

/-- The log factor is dominated by the log envelope of `SmoothLogIntegrable`. -/
theorem norm_neg_two_logSum_pow_le (k : ι → ℕ) (u : ι → ℝ) (n : ℕ) :
    ‖((-2 : ℂ) * (logSum k u : ℂ)) ^ n‖ ≤ (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ n := by
  rw [norm_pow, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have : ∑ i, 2 * (k i : ℝ) * Real.log (u i) = 2 * logSum k u := by
    unfold logSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg (logSum k u)]

/-- Integrability of the box log moment integrand for a flat amplitude on the flat strip. -/
theorem integrableOn_chartZetaLogMoment_integrand {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hflat : FlatOn G p C) (h k : ι → ℕ) (n : ℕ) {s : ℂ} (hs : FlatStrip p h k s) :
    IntegrableOn (fun u => (G u : ℂ) * cpowWeight h k s u * ((-2 : ℂ) * (logSum k u : ℂ)) ^ n)
      (SmoothEngine.box ι 1) := by
  have hc : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re) := fun i => by
    linarith [hs i]
  have hint : IntegrableOn (fun u : ι → ℝ => C *
      ((∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ n)) (SmoothEngine.box ι 1) :=
    (integrableOn_prod_rpow_mul_log_pow hc (fun i => 2 * (k i : ℝ)) n zero_le_one).const_mul C
  have hmeasG : AEStronglyMeasurable (fun u => (G u : ℂ))
      (volume.restrict (SmoothEngine.box ι 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hG.aestronglyMeasurable (SmoothEngine.measurableSet_box 1))
  refine hint.mono' ((hmeasG.mul ((continuousOn_cpowWeight h k s).aestronglyMeasurable
    (SmoothEngine.measurableSet_box 1))).mul (((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_logSum k)).aestronglyMeasurable (SmoothEngine.measurableSet_box 1)
      |>.const_mul _).pow _)) ?_
  rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
  refine Eventually.of_forall fun u hu => ?_
  have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpowWeight h k s hu']
  have hG0 : |G u| ≤ C * mono p u := hflat u hu
  have hP0 : 0 ≤ ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hu' i).le _
  have hCm : 0 ≤ C * mono p u := mul_nonneg hC (mono_nonneg_of_pos hu' p)
  calc |G u| * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
        ‖((-2 : ℂ) * (logSum k u : ℂ)) ^ n‖
      ≤ (C * mono p u) * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ n :=
        mul_le_mul (mul_le_mul hG0 le_rfl hP0 hCm) (norm_neg_two_logSum_pow_le k u n)
          (norm_nonneg _) (mul_nonneg hCm hP0)
    _ = C * ((mono p u * ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ n) := by ring
    _ = _ := by rw [mono_mul_prod_rpow p _ hu']

/-- ★ **Dominated differentiation of the box log moments** on the flat strip. -/
theorem hasDerivAt_chartZetaLogMoment {G : (ι → ℝ) → ℝ} (hG : ContinuousOn G (SmoothEngine.box ι 1))
    {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C) (hflat : FlatOn G p C) (h k : ι → ℕ) (n : ℕ) {s : ℂ}
    (hs : FlatStrip p h k s) :
    HasDerivAt (chartZetaLogMoment G h k n) (chartZetaLogMoment G h k (n + 1) s) s := by
  have hopen := (FlatStrip.isOpen p h k).mem_nhds (show s ∈ {t | FlatStrip p h k t} from hs)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hopen
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hs' : FlatStrip p h k (s + ε') := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε'pos]
    linarith)
  have hc : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re) := fun i => by
    linarith [hs' i]
  have hint : IntegrableOn (fun u : ι → ℝ => C *
      ((∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ (n + 1)))
      (SmoothEngine.box ι 1) :=
    (integrableOn_prod_rpow_mul_log_pow hc (fun i => 2 * (k i : ℝ)) (n + 1)
      zero_le_one).const_mul C
  have hmeasG : AEStronglyMeasurable (fun u => (G u : ℂ))
      (volume.restrict (SmoothEngine.box ι 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hG.aestronglyMeasurable (SmoothEngine.measurableSet_box 1))
  have hmeasL : AEStronglyMeasurable (fun u => (-2 : ℂ) * (logSum k u : ℂ))
      (volume.restrict (SmoothEngine.box ι 1)) :=
    ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_logSum k)).aestronglyMeasurable
      (SmoothEngine.measurableSet_box 1)).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (SmoothEngine.box ι 1))
    (F := fun t u => (G u : ℂ) * cpowWeight h k t u * ((-2 : ℂ) * (logSum k u : ℂ)) ^ n)
    (F' := fun t u => (G u : ℂ) * cpowWeight h k t u * ((-2 : ℂ) * (logSum k u : ℂ)) ^ (n + 1))
    (bound := fun u => C * ((∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
      (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ (n + 1)))
    (s := Metric.ball s ε') (Metric.ball_mem_nhds s hε'pos)
    (Eventually.of_forall fun t => (hmeasG.mul
      ((continuousOn_cpowWeight h k t).aestronglyMeasurable (SmoothEngine.measurableSet_box 1))).mul
      (hmeasL.pow _))
    (integrableOn_chartZetaLogMoment_integrand hG hC hflat h k n hs)
    ((hmeasG.mul ((continuousOn_cpowWeight h k s).aestronglyMeasurable
      (SmoothEngine.measurableSet_box 1))).mul (hmeasL.pow _))
    ?_ hint ?_
  · exact key.2
  · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    refine Eventually.of_forall fun u hu t ht => ?_
    have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpowWeight h k t hu']
    have hre : t.re ≤ (s + ε').re := by
      rw [Metric.mem_ball, dist_eq_norm] at ht
      have := Complex.abs_re_le_norm (t - s)
      rw [Complex.sub_re] at this
      simp only [Complex.add_re, Complex.ofReal_re, hε']
      linarith [abs_le.1 (this.trans ht.le) |>.2]
    have hprod : mono p u * ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re) ≤
        ∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re)) := by
      rw [mono_mul_prod_rpow p _ hu']
      exact prod_rpow_le_of_le (fun i => hu i (mem_univ i)) fun i => by
        have : (0 : ℝ) ≤ 2 * k i := by positivity
        nlinarith
    have hG0 : |G u| ≤ C * mono p u := hflat u hu
    have hP0 : 0 ≤ ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hu' i).le _
    have hCm : 0 ≤ C * mono p u := mul_nonneg hC (mono_nonneg_of_pos hu' p)
    calc |G u| * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) *
          ‖((-2 : ℂ) * (logSum k u : ℂ)) ^ (n + 1)‖
        ≤ (C * mono p u) * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ (n + 1) :=
          mul_le_mul (mul_le_mul hG0 le_rfl hP0 hCm) (norm_neg_two_logSum_pow_le k u (n + 1))
            (norm_nonneg _) (mul_nonneg hCm hP0)
      _ = C * (mono p u * ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ (n + 1) := by ring
      _ ≤ C * (∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) ^ (n + 1) := by
          gcongr
      _ = _ := by ring
  · exact Eventually.of_forall fun u t _ => by
      have h1 := ((hasDerivAt_cpowWeight h k u t).const_mul (G u : ℂ)).mul_const
        (((-2 : ℂ) * (logSum k u : ℂ)) ^ n)
      refine h1.congr_deriv ?_
      ring

/-- ★ **The derivatives of the chart zeta functional are the box log moments** on the flat
strip. -/
theorem iteratedDeriv_chartZeta_flat {G : (ι → ℝ) → ℝ} (hG : ContinuousOn G (SmoothEngine.box ι 1))
    {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C) (hflat : FlatOn G p C) (h k : ι → ℕ) (n : ℕ) :
    ∀ (m : ℕ) {s : ℂ}, FlatStrip p h k s →
      iteratedDeriv n (chartZetaLogMoment G h k m) s = chartZetaLogMoment G h k (m + n) s := by
  induction n with
  | zero => intro m s _; simp
  | succ n ih =>
    intro m s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (chartZetaLogMoment G h k m) =ᶠ[𝓝 s]
        chartZetaLogMoment G h k (m + n) := by
      filter_upwards [(FlatStrip.isOpen p h k).mem_nhds (show s ∈ {t | FlatStrip p h k t} from hs)]
        with t ht
      exact ih m ht
    rw [hev.deriv_eq, (hasDerivAt_chartZetaLogMoment hG hC hflat h k (m + n) hs).deriv]
    rfl

theorem iteratedDeriv_chartZeta_eq_logMoment {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hflat : FlatOn G p C) (h k : ι → ℕ) (n : ℕ) {s : ℂ} (hs : FlatStrip p h k s) :
    iteratedDeriv n (chartZeta G h k) s = chartZetaLogMoment G h k n s := by
  have := iteratedDeriv_chartZeta_flat hG hC hflat h k n 0 hs
  rw [zero_add] at this
  rw [← this]
  congr 1
  funext t
  rw [chartZetaLogMoment_zero]

end BoxMoments

/-! ### The binomial split of the coupled log moments -/

section Split

variable {ι : Type*} [Fintype ι]

/-- One term of the split coupled integrand: `t^{s−1} e^{−t} (log t)^a · H(√t,w) w^{h−2ks}
(−2 logSum k w)^b`. -/
noncomputable def coupTerm (H : ℝ → (ι → ℝ) → ℝ) (h k : ι → ℕ) (a b : ℕ) (s : ℂ)
    (z : ℝ × (ι → ℝ)) : ℂ :=
  coupKernel s z.1 * (Real.log z.1 : ℂ) ^ a *
    ((H (Real.sqrt z.1) z.2 : ℂ) * cpowWeight h k s z.2 * ((-2 : ℂ) * (logSum k z.2 : ℂ)) ^ b)

theorem measurable_coupTerm {H : ℝ → (ι → ℝ) → ℝ}
    (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (h k : ι → ℕ) (a b : ℕ) (s : ℂ) :
    Measurable (coupTerm H h k a b s) := by
  unfold coupTerm
  have hH' : Continuous fun z : ℝ × (ι → ℝ) => H (Real.sqrt z.1) z.2 :=
    hH.comp ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd)
  refine (((measurable_coupKernel s).comp measurable_fst).mul
    ((Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)).pow_const _)).mul
    (((Complex.measurable_ofReal.comp hH'.measurable).mul
      ((measurable_cpowWeight h k s).comp measurable_snd)).mul
      ((measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_logSum k).comp measurable_snd))).pow_const _))

/-- The coupled integrand is the binomial sum of the split terms. -/
theorem coupIntegrand_eq_sum_coupTerm (H : ℝ → (ι → ℝ) → ℝ) (h k : ι → ℕ) (n : ℕ) (s : ℂ)
    (z : ℝ × (ι → ℝ)) :
    coupIntegrand H h k n s z =
      ∑ a ∈ range (n + 1), (n.choose a : ℂ) * coupTerm H h k a (n - a) s z := by
  unfold coupIntegrand coupTerm
  have hsplit : ((Real.log z.1 : ℂ) - 2 * (logSum k z.2 : ℂ)) ^ n =
      ∑ a ∈ range (n + 1), (Real.log z.1 : ℂ) ^ a * ((-2 : ℂ) * (logSum k z.2 : ℂ)) ^ (n - a) *
        (n.choose a : ℂ) := by
    rw [sub_eq_add_neg, ← neg_mul, add_pow]
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The split terms are dominated by the `(a+b)`-th envelope. -/
theorem norm_coupTerm_le {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}
    (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (a b : ℕ) {s : ℂ} {z : ℝ × (ι → ℝ)}
    (hz : 0 < z.1 ∧ z.2 ∈ SmoothEngine.box ι 1) :
    ‖coupTerm H h k a b s z‖ ≤
      ((z.1 ^ (s.re - 1) + z.1 ^ (s.re - 1)) *
        ((1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * Real.exp (-z.1)) *
          (1 + |Real.log z.1|) ^ (a + b)) *
      (C * (∏ i, z.2 i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ (a + b)) := by
  obtain ⟨ht, hw⟩ := hz
  have hw' : ∀ i, 0 < z.2 i := fun i => SmoothEngine.pos_of_mem_box hw i
  have hτ : 0 ≤ Real.sqrt z.1 := Real.sqrt_nonneg _
  unfold coupTerm
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_coupKernel ht, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, norm_cpowWeight h k s hw']
  have hA : |H (Real.sqrt z.1) z.2| ≤ C * (1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) *
      mono p z.2 := hflat _ hτ z.2 hw
  have hla : |Real.log z.1| ^ a ≤ (1 + |Real.log z.1|) ^ (a + b) :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log z.1)]) a).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log z.1)]) (by omega))
  have hlb : ‖((-2 : ℂ) * (logSum k z.2 : ℂ)) ^ b‖ ≤
      (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ (a + b) :=
    (norm_neg_two_logSum_pow_le k z.2 b).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg (∑ i, 2 * (k i : ℝ) * Real.log (z.2 i))])
        (by omega))
  have hP : mono p z.2 * ∏ i, z.2 i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) =
      ∏ i, z.2 i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) :=
    mono_mul_prod_rpow p _ hw'
  have hP0 : 0 ≤ ∏ i, z.2 i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hw' i).le _
  have hK0 : 0 ≤ z.1 ^ (s.re - 1) := Real.rpow_nonneg ht.le _
  have hK : z.1 ^ (s.re - 1) ≤ z.1 ^ (s.re - 1) + z.1 ^ (s.re - 1) := by linarith
  have hm0 : 0 ≤ mono p z.2 := mono_nonneg_of_pos hw' p
  have hexp : 0 ≤ Real.exp (-z.1) := (Real.exp_pos _).le
  have hE0 : 0 ≤ (1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) := by positivity
  calc z.1 ^ (s.re - 1) * Real.exp (-z.1) * |Real.log z.1| ^ a *
        (|H (Real.sqrt z.1) z.2| * (∏ i, z.2 i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
          ‖((-2 : ℂ) * (logSum k z.2 : ℂ)) ^ b‖)
      ≤ (z.1 ^ (s.re - 1) + z.1 ^ (s.re - 1)) * Real.exp (-z.1) *
        (1 + |Real.log z.1|) ^ (a + b) *
        ((C * (1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * mono p z.2) *
          (∏ i, z.2 i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ (a + b)) := by
        gcongr
    _ = (z.1 ^ (s.re - 1) + z.1 ^ (s.re - 1)) *
        ((1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * Real.exp (-z.1)) *
        (1 + |Real.log z.1|) ^ (a + b) *
        (C * (mono p z.2 * ∏ i, z.2 i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ (a + b)) := by ring
    _ = _ := by rw [hP]

/-- The split terms are integrable on the positive flat strip. -/
theorem integrable_coupTerm {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}
    (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (a b : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    Integrable (coupTerm H h k a b s) (coupMeasure ι) := by
  have hbflat : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re) := fun i => by
    linarith [hs i]
  refine (integrable_coupEnvelope C R M (a + b) hs0 le_rfl hbflat).mono'
    (measurable_coupTerm hH h k a b s).aestronglyMeasurable ?_
  filter_upwards [ae_coupMeasure_mem] with z hz
  exact norm_coupTerm_le hC hflat h k a b hz

/-- The `t`-marginal of a split term is `coupKernel s t (log t)^a · chartZetaLogMoment (H √t) b s`,
integrable on `(0, ∞)`. -/
theorem integrable_coupKernel_logpow_mul_logMoment {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ}
    {R : ℕ} {M : ℝ} (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (a b : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    Integrable (fun t : ℝ => coupKernel s t * (Real.log t : ℂ) ^ a *
      chartZetaLogMoment (H (Real.sqrt t)) h k b s) (volume.restrict (Ioi 0)) := by
  have hint := (integrable_coupTerm hH hC hflat h k a b hs0 hs).integral_prod_left
  refine hint.congr (Eventually.of_forall fun t => ?_)
  simp only
  unfold chartZetaLogMoment
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun w _ => ?_
  simp only [coupTerm]

/-- ★ **The binomial split of the coupled log moments.** -/
theorem coupledLogMoment_eq_sum {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}
    (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    coupledLogMoment H h k n s = ∑ a ∈ range (n + 1), (n.choose a : ℂ) *
      ∫ t in Ioi (0 : ℝ), coupKernel s t * (Real.log t : ℂ) ^ a *
        chartZetaLogMoment (H (Real.sqrt t)) h k (n - a) s := by
  unfold coupledLogMoment
  simp_rw [coupIntegrand_eq_sum_coupTerm]
  rw [integral_finsetSum _ fun a _ => (integrable_coupTerm hH hC hflat h k a (n - a)
    hs0 hs).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]
  congr 1
  unfold coupMeasure
  rw [integral_prod _ (integrable_coupTerm hH hC hflat h k a (n - a) hs0 hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  unfold chartZetaLogMoment
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun w _ => ?_
  simp only [coupTerm]

end Split

/-! ### Normalised Taylor coefficients and the Leibniz rule -/

section Taylor

/-- The `n`-th Taylor coefficient `f^{(n)}(μ)/n!`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (μ : ℂ) (n : ℕ) : ℂ := iteratedDeriv n f μ / (n ! : ℂ)

/-- Normalised Leibniz rule: the Taylor coefficients of a product are the Cauchy product. -/
theorem taylorCoeff_mul {f g : ℂ → ℂ} {μ : ℂ} (hf : AnalyticAt ℂ f μ) (hg : AnalyticAt ℂ g μ)
    (n : ℕ) :
    taylorCoeff (fun s => f s * g s) μ n =
      ∑ i ∈ range (n + 1), taylorCoeff f μ i * taylorCoeff g μ (n - i) := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_mul (hf.contDiffAt (n := n)) (hg.contDiffAt (n := n)), Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hfac : (n.choose i : ℂ) * (i ! : ℂ) * ((n - i)! : ℂ) = (n ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have hi0 : (i ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n - i)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hch : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin).ne'
  rw [← hfac]
  field_simp

end Taylor

end Grammar
