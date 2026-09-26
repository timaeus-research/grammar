/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaStrip
import Grammar.EmpiricalInnerTwoRegime

/-!
# The coupled chart zeta functional (route B, units B8–B9)

For a real coupling family `H : ℝ → (ι → ℝ) → ℝ` (the coupling `τ = √t` enters through the
amplitude only) the *coupled chart zeta functional* is

  `coupledChartZeta H h k s = ∫_0^∞ t^{s−1} e^{−t} · chartZeta (H √t) h k s dt`,

the Mellin transform in the coupling variable of the chart zeta functional of the tilted amplitude.
All holomorphic dependence on `s` sits in the explicit scalar kernels `t^{s−1}` and
`cpowWeight h k s w = w^{h − 2ks}`; the amplitude is real and `s`-independent.  Under the flat
growth hypothesis `|H τ w| ≤ C (1+τ)^R e^{Mτ} · w^p` (the form supplied for the face amplitudes of
the empirical field family by `growthLE_faceAmp_fieldFam`) the double integral converges
absolutely on the *positive flat strip* `0 < Re s`, `2kᵢ Re s < pᵢ + hᵢ + 1` (the positivity is
needed at `t = 0`), and dominated differentiation on the product measure with the single multiplier
`log t − 2 logSum k w` gives holomorphy there and the closed form of every derivative:

  `iteratedDeriv n (coupledChartZeta H h k) s
     = ∫∫ t^{s−1} e^{−t} H(√t, w) w^{h−2ks} (log t − 2 logSum k w)^n dw dt`
  (`coupledLogMoment H h k n s`).

The envelopes (`integrableOn_coupEnvelope_t`, the box envelope of `SmoothLogIntegrable`) and the
pointwise bound `norm_coupIntegrand_le` are stated for `a ≤ Re s ≤ b` so that one integrable
majorant serves a whole disc.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

/-! ### The coupling kernel -/

section Kernel

/-- The coupling kernel `t^{s−1} e^{−t}`. -/
noncomputable def coupKernel (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ)

theorem norm_coupKernel {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖coupKernel s t‖ = t ^ (s.re - 1) * Real.exp (-t) := by
  unfold coupKernel
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]

theorem hasDerivAt_coupKernel {t : ℝ} (ht : 0 < t) (s : ℂ) :
    HasDerivAt (fun s => coupKernel s t) (coupKernel s t * (Real.log t : ℂ)) s := by
  unfold coupKernel
  have h1 : HasDerivAt (fun s : ℂ => (t : ℂ) ^ (s - 1))
      ((t : ℂ) ^ (s - 1) * Complex.log (t : ℂ) * 1) s :=
    ((hasDerivAt_id' s).sub_const 1).const_cpow (Or.inl (by exact_mod_cast ht.ne'))
  rw [← Complex.ofReal_log ht.le] at h1
  have := h1.mul_const (Real.exp (-t) : ℂ)
  refine this.congr_deriv ?_
  ring

theorem measurable_coupKernel (s : ℂ) : Measurable (coupKernel s) :=
  (Complex.measurable_ofReal.pow_const _).mul
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg))

end Kernel

/-! ### Envelopes -/

section Envelope

theorem rpow_sub_one_le_add {t a b σ : ℝ} (ht : 0 < t) (ha : a ≤ σ) (hb : σ ≤ b) :
    t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith : a - 1 ≤ σ - 1)
    linarith [Real.rpow_nonneg ht.le (b - 1)]
  · have := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith : σ - 1 ≤ b - 1)
    linarith [Real.rpow_nonneg ht.le (a - 1)]

theorem one_add_pow_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ 2 ^ n * (1 + x ^ n) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    have := le_max_left 1 x
    have := le_max_right 1 x
    linarith
  have h2 : (max 1 x) ^ n ≤ 1 + x ^ n := by
    rcases le_total x 1 with hx1 | hx1
    · rw [max_eq_left hx1, one_pow]; linarith [pow_nonneg hx n]
    · rw [max_eq_right hx1]; linarith
  calc (1 + x) ^ n ≤ (2 * max 1 x) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = 2 ^ n * (max 1 x) ^ n := mul_pow _ _ _
    _ ≤ 2 ^ n * (1 + x ^ n) := by gcongr

/-- The `t`-envelope `(t^{a−1} + t^{b−1}) (1+√t)^R e^{M√t} e^{−t} (1 + |log t|)^n` is integrable on
`(0, ∞)` for `0 < a ≤ b`. -/
theorem integrableOn_coupEnvelope_t {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (M : ℝ)
    (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t ^ (a - 1) + t ^ (b - 1)) *
      ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t)) *
        (1 + |Real.log t|) ^ n) (Ioi 0) := by
  have hb : 0 < b := ha.trans_le hab
  have hE : ∀ (c : ℝ), 0 < c → ∀ ℓ : ℕ, IntegrableOn (fun t : ℝ => t ^ (c - 1) * |Real.log t| ^ ℓ *
      ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t))) (Ioi 0) :=
    fun c hc ℓ => integrableOn_envelope R M hc ℓ
  have hmaj : IntegrableOn (fun t : ℝ => 2 ^ n *
      ((t ^ (a - 1) * |Real.log t| ^ 0 * ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) *
          Real.exp (-t)) +
        t ^ (a - 1) * |Real.log t| ^ n * ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) *
          Real.exp (-t))) +
       (t ^ (b - 1) * |Real.log t| ^ 0 * ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) *
          Real.exp (-t)) +
        t ^ (b - 1) * |Real.log t| ^ n * ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) *
          Real.exp (-t))))) (Ioi 0) :=
    (((hE a ha 0).add (hE a ha n)).add ((hE b hb 0).add (hE b hb n))).const_mul _
  refine hmaj.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hE0 : 0 ≤ (1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t) := by
      positivity
    have hpa : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht'.le _
    have hpb : 0 ≤ t ^ (b - 1) := Real.rpow_nonneg ht'.le _
    have hlog := one_add_pow_le_of_nonneg (abs_nonneg (Real.log t)) n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [pow_zero, mul_one]
    calc (t ^ (a - 1) + t ^ (b - 1)) *
          ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t)) *
          (1 + |Real.log t|) ^ n
        ≤ (t ^ (a - 1) + t ^ (b - 1)) *
          ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t)) *
          (2 ^ n * (1 + |Real.log t| ^ n)) := by gcongr
      _ = _ := by ring

end Envelope

/-! ### The coupled integrand -/

section Integrand

variable {ι : Type*} [Fintype ι]

/-- The coupling measure: Lebesgue measure on `(0,∞) × (0,1]^ι`. -/
noncomputable def coupMeasure (ι : Type*) [Fintype ι] : Measure (ℝ × (ι → ℝ)) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (SmoothEngine.box ι 1))

theorem coupMeasure_eq_restrict :
    coupMeasure ι = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ SmoothEngine.box ι 1) :=
  Measure.prod_restrict _ _

theorem ae_coupMeasure_mem :
    ∀ᵐ z ∂(coupMeasure ι), 0 < z.1 ∧ z.2 ∈ SmoothEngine.box ι 1 := by
  rw [coupMeasure_eq_restrict, ae_restrict_iff' (measurableSet_Ioi.prod
    (SmoothEngine.measurableSet_box 1))]
  exact Eventually.of_forall fun z hz => ⟨hz.1, hz.2⟩

/-- The integrand of the `n`-th log moment:
`t^{s−1} e^{−t} H(√t, w) w^{h−2ks} (log t − 2 logSum k w)^n`. -/
noncomputable def coupIntegrand (H : ℝ → (ι → ℝ) → ℝ) (h k : ι → ℕ) (n : ℕ) (s : ℂ)
    (z : ℝ × (ι → ℝ)) : ℂ :=
  coupKernel s z.1 * (H (Real.sqrt z.1) z.2 : ℂ) * cpowWeight h k s z.2 *
    ((Real.log z.1 : ℂ) - 2 * (logSum k z.2 : ℂ)) ^ n

theorem measurable_coupIntegrand {H : ℝ → (ι → ℝ) → ℝ}
    (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (h k : ι → ℕ) (n : ℕ) (s : ℂ) :
    Measurable (coupIntegrand H h k n s) := by
  unfold coupIntegrand
  have hH' : Continuous fun z : ℝ × (ι → ℝ) => H (Real.sqrt z.1) z.2 :=
    hH.comp ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd)
  refine (((measurable_coupKernel s).comp measurable_fst).mul
    (Complex.measurable_ofReal.comp hH'.measurable)).mul
    ((measurable_cpowWeight h k s).comp measurable_snd) |>.mul (Measurable.pow_const ?_ n)
  exact (Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)).sub
    (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_logSum k).comp measurable_snd)))

/-- The pointwise envelope of the coupled integrand for `a ≤ Re s ≤ b`. -/
theorem norm_coupIntegrand_le {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}
    (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (n : ℕ) {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    {z : ℝ × (ι → ℝ)} (hz : 0 < z.1 ∧ z.2 ∈ SmoothEngine.box ι 1) :
    ‖coupIntegrand H h k n s z‖ ≤
      ((z.1 ^ (a - 1) + z.1 ^ (b - 1)) *
        ((1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * Real.exp (-z.1)) *
          (1 + |Real.log z.1|) ^ n) *
      (C * (∏ i, z.2 i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * b))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ n) := by
  obtain ⟨ht, hw⟩ := hz
  set t := z.1
  set w := z.2
  have hw' : ∀ i, 0 < w i := fun i => SmoothEngine.pos_of_mem_box hw i
  have hτ : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  unfold coupIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_coupKernel ht, Complex.norm_real, Real.norm_eq_abs,
    norm_cpowWeight h k s hw', norm_pow]
  -- the amplitude bound
  have hA : |H (Real.sqrt t) w| ≤ C * (1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) *
      mono p w := hflat _ hτ w hw
  -- the kernel bound
  have hK : t ^ (s.re - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := rpow_sub_one_le_add ht ha hb
  -- the log bound
  have hL : ‖(Real.log t : ℂ) - 2 * (logSum k w : ℂ)‖ ≤
      (1 + |Real.log t|) * (1 + |∑ i, 2 * (k i : ℝ) * Real.log (w i)|) := by
    have h2 : (2 : ℂ) * (logSum k w : ℂ) = ((∑ i, 2 * (k i : ℝ) * Real.log (w i) : ℝ) : ℂ) := by
      unfold logSum
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := abs_sub (Real.log t) (∑ i, 2 * (k i : ℝ) * Real.log (w i))
    nlinarith [abs_nonneg (Real.log t), abs_nonneg (∑ i, 2 * (k i : ℝ) * Real.log (w i))]
  -- the box bound
  have hP : mono p w * ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) ≤
      ∏ i, w i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * b)) := by
    rw [mono_mul_prod_rpow p _ hw']
    exact prod_rpow_le_of_le (fun i => hw i (mem_univ i)) fun i => by
      have : (0 : ℝ) ≤ 2 * k i := by positivity
      nlinarith
  have hP0 : 0 ≤ ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hw' i).le _
  have hE0 : 0 ≤ (1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) := by positivity
  have hm0 : 0 ≤ mono p w := mono_nonneg_of_pos hw' p
  have hK0 : 0 ≤ t ^ (s.re - 1) := Real.rpow_nonneg ht.le _
  have hexp : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  calc t ^ (s.re - 1) * Real.exp (-t) * |H (Real.sqrt t) w| *
        (∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
        ‖(Real.log t : ℂ) - 2 * (logSum k w : ℂ)‖ ^ n
      ≤ (t ^ (a - 1) + t ^ (b - 1)) * Real.exp (-t) *
        (C * (1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * mono p w) *
        (∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
        ((1 + |Real.log t|) * (1 + |∑ i, 2 * (k i : ℝ) * Real.log (w i)|)) ^ n := by
        gcongr
      _ = (t ^ (a - 1) + t ^ (b - 1)) *
          ((1 + Real.sqrt t) ^ R * Real.exp (M * Real.sqrt t) * Real.exp (-t)) *
          (1 + |Real.log t|) ^ n *
          (C * (mono p w * ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * s.re)) *
            (1 + |∑ i, 2 * (k i : ℝ) * Real.log (w i)|) ^ n) := by rw [mul_pow]; ring
      _ ≤ _ := by gcongr

/-- The product envelope is integrable for the coupling measure. -/
theorem integrable_coupEnvelope {p h k : ι → ℕ} (C : ℝ) (R : ℕ) (M : ℝ) (n : ℕ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbflat : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * b)) :
    Integrable (fun z : ℝ × (ι → ℝ) =>
      ((z.1 ^ (a - 1) + z.1 ^ (b - 1)) *
        ((1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * Real.exp (-z.1)) *
          (1 + |Real.log z.1|) ^ n) *
      (C * (∏ i, z.2 i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * b))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ n)) (coupMeasure ι) := by
  have hw := (integrableOn_prod_rpow_mul_log_pow hbflat (fun i => 2 * (k i : ℝ)) n
    zero_le_one).const_mul C
  have hw' : Integrable (fun w : ι → ℝ =>
      C * (∏ i, w i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * b))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (w i)|) ^ n)
      (volume.restrict (SmoothEngine.box ι 1)) := by
    refine hw.congr (Eventually.of_forall fun w => ?_)
    ring
  exact (integrableOn_coupEnvelope_t ha hab R M n).mul_prod hw'

variable {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}

/-- The coupled integrand is integrable on the positive flat strip. -/
theorem integrable_coupIntegrand (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2) (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    Integrable (coupIntegrand H h k n s) (coupMeasure ι) := by
  have hbflat : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * s.re) := fun i => by
    linarith [hs i]
  refine (integrable_coupEnvelope C R M n hs0 le_rfl hbflat).mono'
    (measurable_coupIntegrand hH h k n s).aestronglyMeasurable ?_
  filter_upwards [ae_coupMeasure_mem] with z hz
  exact norm_coupIntegrand_le hC hflat h k n le_rfl le_rfl hz

end Integrand

/-! ### The coupled chart zeta functional and its log moments -/

section Coupled

variable {ι : Type*} [Fintype ι]

/-- The `n`-th log moment of the coupled chart zeta functional (a product-measure integral). -/
noncomputable def coupledLogMoment (H : ℝ → (ι → ℝ) → ℝ) (h k : ι → ℕ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ z, coupIntegrand H h k n s z ∂(coupMeasure ι)

/-- The coupled chart zeta functional `∫_0^∞ t^{s−1} e^{−t} chartZeta (H √t) h k s dt`. -/
noncomputable def coupledChartZeta (H : ℝ → (ι → ℝ) → ℝ) (h k : ι → ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), coupKernel s t * chartZeta (H (Real.sqrt t)) h k s

variable {H : ℝ → (ι → ℝ) → ℝ} {p : ι → ℕ} {C : ℝ} {R : ℕ} {M : ℝ}

/-- On the positive flat strip the coupled chart zeta functional is the zeroth log moment. -/
theorem coupledChartZeta_eq_logMoment_zero (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    coupledChartZeta H h k s = coupledLogMoment H h k 0 s := by
  unfold coupledChartZeta coupledLogMoment coupMeasure
  rw [integral_prod _ (integrable_coupIntegrand hH hC hflat h k 0 hs0 hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  unfold chartZeta
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun w _ => ?_
  simp only [coupIntegrand, pow_zero, mul_one]
  ring

omit [Fintype ι] in
/-- The open positive flat strip. -/
theorem isOpen_posFlatStrip [Finite ι] (p h k : ι → ℕ) :
    IsOpen {s : ℂ | 0 < s.re ∧ FlatStrip p h k s} := by
  have := Fintype.ofFinite ι
  exact (isOpen_lt continuous_const Complex.continuous_re).inter (FlatStrip.isOpen p h k)

/-- ★ **Holomorphy of the log moments** on the positive flat strip, with the derivative given by
the next log moment. -/
theorem hasDerivAt_coupledLogMoment (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (n : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    HasDerivAt (coupledLogMoment H h k n) (coupledLogMoment H h k (n + 1) s) s := by
  have hopen := (isOpen_posFlatStrip p h k).mem_nhds
    (show s ∈ {t : ℂ | 0 < t.re ∧ FlatStrip p h k t} from ⟨hs0, hs⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hopen
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hmem : ∀ x : ℝ, |x| < ε → s + x ∈ {t : ℂ | 0 < t.re ∧ FlatStrip p h k t} := fun x hx =>
    hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      exact hx)
  have hplus := hmem ε' (by rw [abs_of_pos hε'pos]; linarith)
  have hminus := hmem (-ε') (by rw [abs_neg, abs_of_pos hε'pos]; linarith)
  have ha : 0 < s.re - ε' := by
    have := hminus.1
    simpa [Complex.add_re, Complex.ofReal_re] using this
  have hbflat : ∀ i, -1 < (p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s.re + ε')) := fun i => by
    have := hplus.2 i
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  have hint := integrable_coupEnvelope (p := p) (h := h) (k := k) C R M (n + 1) ha
    (by linarith) hbflat
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := coupMeasure ι)
    (F := fun t z => coupIntegrand H h k n t z)
    (F' := fun t z => coupIntegrand H h k (n + 1) t z)
    (bound := fun z : ℝ × (ι → ℝ) =>
      ((z.1 ^ (s.re - ε' - 1) + z.1 ^ (s.re + ε' - 1)) *
        ((1 + Real.sqrt z.1) ^ R * Real.exp (M * Real.sqrt z.1) * Real.exp (-z.1)) *
          (1 + |Real.log z.1|) ^ (n + 1)) *
      (C * (∏ i, z.2 i ^ ((p i : ℝ) + ((h i : ℝ) - 2 * (k i : ℝ) * (s.re + ε')))) *
        (1 + |∑ i, 2 * (k i : ℝ) * Real.log (z.2 i)|) ^ (n + 1)))
    (s := Metric.ball s ε') (Metric.ball_mem_nhds s hε'pos)
    (Eventually.of_forall fun t => (measurable_coupIntegrand hH h k n t).aestronglyMeasurable)
    (integrable_coupIntegrand hH hC hflat h k n hs0 hs)
    (measurable_coupIntegrand hH h k (n + 1) s).aestronglyMeasurable ?_ hint ?_
  · exact key.2
  · filter_upwards [ae_coupMeasure_mem] with z hz t ht
    have hre : |t.re - s.re| ≤ ε' := by
      rw [Metric.mem_ball, dist_eq_norm] at ht
      have := Complex.abs_re_le_norm (t - s)
      rw [Complex.sub_re] at this
      exact this.trans ht.le
    exact norm_coupIntegrand_le hC hflat h k (n + 1) (by linarith [abs_le.1 hre |>.1])
      (by linarith [abs_le.1 hre |>.2]) hz
  · filter_upwards [ae_coupMeasure_mem] with z hz t _
    unfold coupIntegrand
    have h1 := ((hasDerivAt_coupKernel hz.1 t).mul_const
      ((H (Real.sqrt z.1) z.2 : ℝ) : ℂ)).mul (hasDerivAt_cpowWeight h k z.2 t)
    have h2 := h1.mul_const (((Real.log z.1 : ℂ) - 2 * (logSum k z.2 : ℂ)) ^ n)
    refine h2.congr_deriv ?_
    ring

theorem differentiableOn_coupledLogMoment (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (n : ℕ) :
    DifferentiableOn ℂ (coupledLogMoment H h k n) {s : ℂ | 0 < s.re ∧ FlatStrip p h k s} :=
  fun _ hs => (hasDerivAt_coupledLogMoment hH hC hflat h k n hs.1
    hs.2).differentiableAt.differentiableWithinAt

/-- Iterated derivatives of functions agreeing near a point agree there. -/
theorem EventuallyEq.iteratedDeriv_eq_of_nhds {f g : ℂ → ℂ} (n : ℕ) :
    ∀ {x : ℂ}, f =ᶠ[𝓝 x] g → iteratedDeriv n f x = iteratedDeriv n g x := by
  induction n with
  | zero => intro x hx; simpa using hx.eq_of_nhds
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    refine Filter.EventuallyEq.deriv_eq ?_
    obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.1 hx
    refine eventually_nhds_iff.2 ⟨U, fun y hy => ih ?_, hUopen, hxU⟩
    exact eventually_nhds_iff.2 ⟨U, hU, hUopen, hy⟩

/-- ★ **All derivatives of the log moments** on the positive flat strip. -/
theorem iteratedDeriv_coupledLogMoment (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (m : ℕ) :
    ∀ (n : ℕ) {s : ℂ}, 0 < s.re → FlatStrip p h k s →
      iteratedDeriv m (coupledLogMoment H h k n) s = coupledLogMoment H h k (n + m) s := by
  induction m with
  | zero => intro n s _ _; simp
  | succ m ih =>
    intro n s hs0 hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m (coupledLogMoment H h k n) =ᶠ[𝓝 s]
        coupledLogMoment H h k (n + m) := by
      filter_upwards [(isOpen_posFlatStrip p h k).mem_nhds
        (show s ∈ {t : ℂ | 0 < t.re ∧ FlatStrip p h k t} from ⟨hs0, hs⟩)] with t ht
      exact ih n ht.1 ht.2
    rw [hev.deriv_eq, (hasDerivAt_coupledLogMoment hH hC hflat h k (n + m) hs0 hs).deriv]
    rfl

/-- ★★ **The coupled chart zeta functional is holomorphic on the positive flat strip and its
derivatives are the log moments.** -/
theorem iteratedDeriv_coupledChartZeta (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) (m : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs : FlatStrip p h k s) :
    iteratedDeriv m (coupledChartZeta H h k) s = coupledLogMoment H h k m s := by
  have hev : coupledChartZeta H h k =ᶠ[𝓝 s] coupledLogMoment H h k 0 := by
    filter_upwards [(isOpen_posFlatStrip p h k).mem_nhds
      (show s ∈ {t : ℂ | 0 < t.re ∧ FlatStrip p h k t} from ⟨hs0, hs⟩)] with t ht
    exact coupledChartZeta_eq_logMoment_zero hH hC hflat h k ht.1 ht.2
  rw [EventuallyEq.iteratedDeriv_eq_of_nhds m hev,
    iteratedDeriv_coupledLogMoment hH hC hflat h k m 0 hs0 hs, zero_add]

theorem differentiableOn_coupledChartZeta (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C) (hflat : ∀ τ, 0 ≤ τ → FlatOn (H τ) p (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (h k : ι → ℕ) :
    DifferentiableOn ℂ (coupledChartZeta H h k) {s : ℂ | 0 < s.re ∧ FlatStrip p h k s} := by
  refine (differentiableOn_coupledLogMoment hH hC hflat h k 0).congr fun s hs => ?_
  exact coupledChartZeta_eq_logMoment_zero hH hC hflat h k hs.1 hs.2

end Coupled

end Grammar
