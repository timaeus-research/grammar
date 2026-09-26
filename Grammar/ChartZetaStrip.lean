/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SmoothLogIntegrable
import Grammar.SmoothFaceTheorem
import Grammar.SmoothAmplitudeFamily
import Grammar.LeadingFaceMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The chart zeta functional on its strip of convergence (polar-distribution programme, unit 2)

Consult #167 (A1, `tide-log/plan_polar_distribution.md`). The chart zeta functional of a smooth
amplitude `G` on the unit box with data `(h,k)` is
  `chartZeta G h k s = ∫_{(0,1]^d} G(u) ∏ᵢ uᵢ^{hᵢ − 2kᵢ s} du`,
the complex weight being written as `exp((∑ hᵢ log uᵢ) − 2 s ∑ kᵢ log uᵢ)` (`cpowWeight`), which
on the box agrees with the product of complex powers (`cpowWeight_eq_prod_cpow`) and has norm
`∏ uᵢ^{hᵢ − 2kᵢ Re s}` (`norm_cpowWeight`). On the strip `ZetaStrip h k s : ∀ i, 2kᵢ Re s < hᵢ + 1`
the integrand is integrable for a bounded (e.g. continuous) amplitude
(`integrableOn_chartZeta_integrand`) and the functional is holomorphic, with derivative the
log-weighted integral (★ `hasDerivAt_chartZeta`: `∂_s chartZeta = ∫ G · cpowWeight · (−2 logSum k)`;
`differentiableOn_chartZeta`). At a real point the functional is the real face integral
`faceCoeffInt G h (2k) 1 μ 0` of the smooth engine (`chartZeta_ofReal`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset

namespace Grammar

open SmoothEngine

variable {ι : Type*} [Fintype ι]

/-- The complex monomial weight `∏ᵢ uᵢ^{hᵢ − 2kᵢ s}` written through the logarithmic sums. -/
noncomputable def cpowWeight (h k : ι → ℕ) (s : ℂ) (u : ι → ℝ) : ℂ :=
  Complex.exp ((logSum h u : ℂ) - 2 * s * (logSum k u : ℂ))

/-- The chart zeta functional `∫_{(0,1]^ι} G(u) ∏ᵢ uᵢ^{hᵢ − 2kᵢ s} du`. -/
noncomputable def chartZeta (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (s : ℂ) : ℂ :=
  ∫ u in SmoothEngine.box ι 1, (G u : ℂ) * cpowWeight h k s u

/-- The strip of absolute convergence for a `p`-flat amplitude: `2kᵢ Re s < pᵢ + hᵢ + 1`. -/
def FlatStrip (p h k : ι → ℕ) (s : ℂ) : Prop := ∀ i, 2 * (k i : ℝ) * s.re < p i + h i + 1

/-- The strip of absolute convergence for a bounded amplitude: `2kᵢ Re s < hᵢ + 1`. -/
def ZetaStrip (h k : ι → ℕ) (s : ℂ) : Prop := ∀ i, 2 * (k i : ℝ) * s.re < h i + 1

omit [Fintype ι] in
theorem ZetaStrip.flatStrip {h k : ι → ℕ} {s : ℂ} (hs : ZetaStrip h k s) :
    FlatStrip 0 h k s := fun i => by simpa using hs i

theorem FlatStrip.isOpen (p h k : ι → ℕ) : IsOpen {s : ℂ | FlatStrip p h k s} := by
  have : {s : ℂ | FlatStrip p h k s} =
      ⋂ i, {s : ℂ | 2 * (k i : ℝ) * s.re < p i + h i + 1} := by
    ext s; simp [FlatStrip]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_const.mul Complex.continuous_re) continuous_const

theorem ZetaStrip.isOpen (h k : ι → ℕ) : IsOpen {s : ℂ | ZetaStrip h k s} := by
  have : {s : ℂ | ZetaStrip h k s} = ⋂ i, {s : ℂ | 2 * (k i : ℝ) * s.re < h i + 1} := by
    ext s; simp [ZetaStrip]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_const.mul Complex.continuous_re) continuous_const

omit [Fintype ι] in
theorem FlatStrip.of_re_le {p h k : ι → ℕ} {s t : ℂ} (hs : FlatStrip p h k s)
    (hts : t.re ≤ s.re) : FlatStrip p h k t := fun i => by
  have := hs i
  have hk : (0 : ℝ) ≤ 2 * k i := by positivity
  nlinarith

omit [Fintype ι] in
theorem ZetaStrip.of_re_le {h k : ι → ℕ} {s t : ℂ} (hs : ZetaStrip h k s) (hts : t.re ≤ s.re) :
    ZetaStrip h k t := fun i => by
  have := hs i
  have hk : (0 : ℝ) ≤ 2 * k i := by positivity
  nlinarith

/-- A `p`-flat amplitude on the box: `|G w| ≤ C ∏ᵢ wᵢ^{pᵢ}`. -/
def FlatOn (G : (ι → ℝ) → ℝ) (p : ι → ℕ) (C : ℝ) : Prop :=
  ∀ w ∈ SmoothEngine.box ι 1, |G w| ≤ C * mono p w

/-- The weight on the box is the product of complex powers of the coordinates. -/
theorem cpowWeight_eq_prod_cpow (h k : ι → ℕ) (s : ℂ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    cpowWeight h k s u = ∏ i, ((u i : ℂ) ^ ((h i : ℂ) - 2 * (k i : ℂ) * s)) := by
  unfold cpowWeight logSum
  have hlog : ∀ i, Complex.log (u i : ℂ) = (Real.log (u i) : ℂ) := fun i =>
    (Complex.ofReal_log (hu i).le).symm
  have hne : ∀ i, (u i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hu i).ne'
  rw [Finset.prod_congr rfl fun i _ => Complex.cpow_def_of_ne_zero (hne i) _,
    ← Complex.exp_sum]
  congr 1
  simp only [hlog]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The norm of the weight is the real monomial `∏ᵢ uᵢ^{hᵢ − 2kᵢ Re s}`. -/
theorem norm_cpowWeight (h k : ι → ℕ) (s : ℂ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    ‖cpowWeight h k s u‖ = ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) := by
  unfold cpowWeight
  rw [Complex.norm_exp]
  have hre : ((logSum h u : ℂ) - 2 * s * (logSum k u : ℂ)).re =
      logSum h u - 2 * s.re * logSum k u := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [hre]
  unfold logSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_def_of_pos (hu i)]
  congr 1
  ring

theorem continuousOn_logSum (a : ι → ℕ) :
    ContinuousOn (logSum a) (SmoothEngine.box ι 1) := by
  unfold logSum
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
  exact Real.continuousOn_log.comp (continuous_apply i).continuousOn fun u hu =>
    (SmoothEngine.pos_of_mem_box hu i).ne'

theorem continuousOn_cpowWeight (h k : ι → ℕ) (s : ℂ) :
    ContinuousOn (cpowWeight h k s) (SmoothEngine.box ι 1) := by
  unfold cpowWeight
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine (Complex.continuous_ofReal.comp_continuousOn ?_).sub
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_))
  · exact continuousOn_logSum h
  · exact continuousOn_logSum k

theorem measurable_cpowWeight (h k : ι → ℕ) (s : ℂ) : Measurable (cpowWeight h k s) := by
  unfold cpowWeight
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_logSum h)).sub
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_logSum k))))

/-- The strip bound for `u ∈ (0,1]^ι`: `uᵢ^a ≤ uᵢ^b` when `b ≤ a`. -/
theorem prod_rpow_le_of_le {u : ι → ℝ} (hu : ∀ i, u i ∈ Ioc (0 : ℝ) 1) {a b : ι → ℝ}
    (hab : ∀ i, b i ≤ a i) : ∏ i, u i ^ a i ≤ ∏ i, u i ^ b i :=
  Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hu i).1.le _) fun i _ =>
    Real.rpow_le_rpow_of_exponent_ge (hu i).1 (hu i).2 (hab i)

/-- A natural monomial times a real-power product is a real-power product. -/
theorem mono_mul_prod_rpow (p : ι → ℕ) (c : ι → ℝ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    mono p u * ∏ i, u i ^ c i = ∏ i, u i ^ ((p i : ℝ) + c i) := by
  unfold mono
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_add (hu i)]

omit [Fintype ι] in
/-- The closed box `[0,1]^ι` for an arbitrary finite index type, and its compactness. -/
theorem isCompact_closedBox' (b : ℝ) : IsCompact (Set.pi univ fun _ : ι => Icc (0 : ℝ) b) :=
  isCompact_univ_pi fun _ => isCompact_Icc

omit [Fintype ι] in
theorem box_subset_closedBox' (b : ℝ) :
    SmoothEngine.box ι b ⊆ Set.pi univ fun _ : ι => Icc (0 : ℝ) b := fun _ hv i _ =>
  Ioc_subset_Icc_self (hv i (Set.mem_univ i))

theorem mono_nonneg_of_pos {u : ι → ℝ} (hu : ∀ i, 0 < u i) (p : ι → ℕ) : 0 ≤ mono p u :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hu i).le _

/-- A continuous amplitude is `0`-flat with the sup bound. -/
theorem flatOn_of_continuous {G : (ι → ℝ) → ℝ} (hG : Continuous G) :
    ∃ M : ℝ, 0 ≤ M ∧ FlatOn G 0 M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBox' 1).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
  rw [show mono (0 : ι → ℕ) w = 1 by simp [mono], mul_one]
  exact (hM w (box_subset_closedBox' 1 hw)).trans (le_max_left _ _)

/-- The integrand is integrable on the flat strip for a `p`-flat amplitude. -/
theorem integrableOn_chartZeta_integrand_flat {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ}
    (hflat : FlatOn G p C) (h k : ι → ℕ) {s : ℂ} (hs : FlatStrip p h k s) :
    IntegrableOn (fun u => (G u : ℂ) * cpowWeight h k s u) (SmoothEngine.box ι 1) := by
  have hc : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re) := fun i => by
    linarith [hs i]
  have hint := integrableOn_prod_rpow_mul_log_pow hc (fun _ => 0) 0 zero_le_one
  simp only [pow_zero, mul_one] at hint
  have hint' : IntegrableOn
      (fun u : ι → ℝ => C * ∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re)))
      (SmoothEngine.box ι 1) := hint.const_mul C
  refine hint'.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hG.aestronglyMeasurable (SmoothEngine.measurableSet_box 1))).mul
      ((continuousOn_cpowWeight h k s).aestronglyMeasurable (SmoothEngine.measurableSet_box 1))
  · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    refine Eventually.of_forall fun u hu => ?_
    have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpowWeight h k s hu',
      ← mono_mul_prod_rpow p _ hu', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hflat u hu)
      (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hu' i).le _)

/-- The integrand is integrable on the strip for a continuous amplitude. -/
theorem integrableOn_chartZeta_integrand {G : (ι → ℝ) → ℝ} (hG : Continuous G)
    (h k : ι → ℕ) {s : ℂ} (hs : ZetaStrip h k s) :
    IntegrableOn (fun u => (G u : ℂ) * cpowWeight h k s u) (SmoothEngine.box ι 1) := by
  obtain ⟨M, hM0, hM⟩ := flatOn_of_continuous hG
  exact integrableOn_chartZeta_integrand_flat hG.continuousOn hM h k hs.flatStrip

/-- The `s`-derivative of the weight is `−2 logSum k · weight`. -/
theorem hasDerivAt_cpowWeight (h k : ι → ℕ) (u : ι → ℝ) (s : ℂ) :
    HasDerivAt (fun s => cpowWeight h k s u) (cpowWeight h k s u * (-2 * (logSum k u : ℂ))) s := by
  unfold cpowWeight
  have h1 : HasDerivAt (fun s : ℂ => (logSum h u : ℂ) - 2 * s * (logSum k u : ℂ))
      (-2 * (logSum k u : ℂ)) s := by
    have := ((hasDerivAt_id s).const_mul (2 : ℂ)).mul_const (logSum k u : ℂ)
    simpa using this.const_sub (logSum h u : ℂ)
  exact h1.cexp

/-- ★ **Holomorphy on the flat strip**: the chart zeta functional of a `p`-flat amplitude is
complex-differentiable at every point of the flat strip, with derivative the log-weighted
integral. -/
theorem hasDerivAt_chartZeta_flat {G : (ι → ℝ) → ℝ} (hG : ContinuousOn G (SmoothEngine.box ι 1))
    {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C) (hflat : FlatOn G p C) (h k : ι → ℕ) {s : ℂ}
    (hs : FlatStrip p h k s) :
    HasDerivAt (chartZeta G h k)
      (∫ u in SmoothEngine.box ι 1,
        (G u : ℂ) * cpowWeight h k s u * (-2 * (logSum k u : ℂ))) s := by
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
  have hint₀ := integrableOn_prod_rpow_mul_log_pow hc (fun i => 2 * (k i : ℝ)) 1 zero_le_one
  simp only [pow_one] at hint₀
  have hint : IntegrableOn (fun u : ι → ℝ => C *
      ((∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|)))
      (SmoothEngine.box ι 1) := hint₀.const_mul C
  have hmeasG : AEStronglyMeasurable (fun u => (G u : ℂ))
      (volume.restrict (SmoothEngine.box ι 1)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hG.aestronglyMeasurable (SmoothEngine.measurableSet_box 1))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (SmoothEngine.box ι 1))
    (F := fun t u => (G u : ℂ) * cpowWeight h k t u)
    (F' := fun t u => (G u : ℂ) * cpowWeight h k t u * (-2 * (logSum k u : ℂ)))
    (bound := fun u => C * ((∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
      (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|)))
    (s := Metric.ball s ε') (Metric.ball_mem_nhds s hε'pos)
    (Eventually.of_forall fun t => hmeasG.mul
      ((continuousOn_cpowWeight h k t).aestronglyMeasurable (SmoothEngine.measurableSet_box 1)))
    (integrableOn_chartZeta_integrand_flat hG hflat h k hs)
    ((hmeasG.mul ((continuousOn_cpowWeight h k s).aestronglyMeasurable
      (SmoothEngine.measurableSet_box 1))).mul
      ((Complex.continuous_ofReal.comp_continuousOn (continuousOn_logSum k)).aestronglyMeasurable
        (SmoothEngine.measurableSet_box 1) |>.const_mul _))
    ?_ hint ?_
  · exact key.2
  · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    refine Eventually.of_forall fun u hu t ht => ?_
    have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpowWeight h k t hu',
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
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
    have hlog : ‖(-2 : ℂ)‖ * |logSum k u| ≤ 1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)| := by
      rw [norm_neg, Complex.norm_ofNat]
      unfold logSum
      have : ∑ i, 2 * (k i : ℝ) * Real.log (u i) = 2 * ∑ i, (k i : ℝ) * Real.log (u i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg (∑ i, (k i : ℝ) * Real.log (u i))]
    have hG0 : |G u| ≤ C * mono p u := hflat u hu
    have hP0 : 0 ≤ ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hu' i).le _
    have hCm : 0 ≤ C * mono p u := mul_nonneg hC (mono_nonneg_of_pos hu' p)
    calc |G u| * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) * (‖(-2 : ℂ)‖ * |logSum k u|)
        ≤ (C * mono p u) * (∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) :=
          mul_le_mul (mul_le_mul hG0 le_rfl hP0 hCm) hlog (by positivity)
            (mul_nonneg hCm hP0)
      _ = C * (mono p u * ∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * t.re)) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) := by ring
      _ ≤ C * (∏ i, u i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s + ε').re))) *
          (1 + |∑ i, 2 * (k i : ℝ) * Real.log (u i)|) := by
          gcongr
      _ = _ := by ring
  · exact Eventually.of_forall fun u t _ => by
      simpa [mul_assoc] using (hasDerivAt_cpowWeight h k u t).const_mul (G u : ℂ)

/-- ★ **Holomorphy on the strip** for a continuous amplitude. -/
theorem hasDerivAt_chartZeta {G : (ι → ℝ) → ℝ} (hG : Continuous G) (h k : ι → ℕ)
    {s : ℂ} (hs : ZetaStrip h k s) :
    HasDerivAt (chartZeta G h k)
      (∫ u in SmoothEngine.box ι 1,
        (G u : ℂ) * cpowWeight h k s u * (-2 * (logSum k u : ℂ))) s := by
  obtain ⟨M, hM0, hM⟩ := flatOn_of_continuous hG
  exact hasDerivAt_chartZeta_flat hG.continuousOn hM0 hM h k hs.flatStrip

theorem differentiableOn_chartZeta_flat {G : (ι → ℝ) → ℝ}
    (hG : ContinuousOn G (SmoothEngine.box ι 1)) {p : ι → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hflat : FlatOn G p C) (h k : ι → ℕ) :
    DifferentiableOn ℂ (chartZeta G h k) {s | FlatStrip p h k s} :=
  fun _ hs => (hasDerivAt_chartZeta_flat hG hC hflat h k hs).differentiableAt.differentiableWithinAt

theorem differentiableOn_chartZeta {G : (ι → ℝ) → ℝ} (hG : Continuous G)
    (h k : ι → ℕ) : DifferentiableOn ℂ (chartZeta G h k) {s | ZetaStrip h k s} :=
  fun _ hs => (hasDerivAt_chartZeta hG h k hs).differentiableAt.differentiableWithinAt

/-- At a real point the chart zeta functional is the real face integral of the smooth engine. -/
theorem chartZeta_ofReal (G : (ι → ℝ) → ℝ) (h k : ι → ℕ) (μ : ℝ) :
    chartZeta G h k (μ : ℂ) = (faceCoeffInt G h (fun i => 2 * k i) 1 μ 0 : ℂ) := by
  unfold chartZeta faceCoeffInt
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun u hu => ?_
  have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
  rw [cpowWeight_eq_prod_cpow h k _ hu', pow_zero, mul_one]
  have hprod : ∏ i, ((u i : ℂ) ^ ((h i : ℂ) - 2 * (k i : ℂ) * (μ : ℂ))) =
      ((∏ i, u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * μ) : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_cpow (hu' i).le]
    congr 1
    push_cast
    ring
  rw [hprod, ← residueWeight_eq_prod h k μ hu']
  unfold residueWeight
  push_cast
  ring

end Grammar
