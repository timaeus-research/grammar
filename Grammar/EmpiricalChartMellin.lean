/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CoupledChartZeta
import Grammar.EmpiricalGeneral
import Grammar.MellinTiltIntegrable
import Grammar.FluctuationComplex

/-!
# The Mellin transform of the empirical chart integral (route B, unit B10)

The empirical chart integral
`empIntegral η ζ h k N = ∫_{(0,1]^d} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)} dv`
has the Mellin transform

  `mellin (empIntegral η ζ h k) s = coupledChartZeta (fieldFam η ζ) h k s
                                  = ∫_0^∞ t^{s−1} e^{−t} chartZeta (η e^{√t ζ}) h k s dt`

on the initial strip `0 < Re s`, `2kᵢ Re s < hᵢ + 1` (★★ `mellin_empIntegral_eq_coupledChartZeta`).
The proof substitutes `N = t / v^{2k}` in the inner Mellin integral (`mellin_exp_tilt`, giving the
complex fluctuation function `S(s, ζ(v))`) after one Fubini interchange, then unfolds `S` and
interchanges again; both interchanges are justified by the AM–GM majorant `exp_tilt_le` and the
coupled envelope of `CoupledChartZeta`.  The two side conditions of `polarCoeff_unique` — local
integrability of the empirical integral on `(0, ∞)` and boundedness at `0⁺` — are derived from
`MellinTiltIntegrable` (`locallyIntegrableOn_empIntegral`, `empIntegral_isBigO_one_zero`).
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### Bounds on the closed box -/

section Bounds

theorem exists_abs_bound_closedBox {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ closedBox d 1, |η v| ≤ C := by
  obtain ⟨M, hM⟩ := exists_field_bound hη
  exact ⟨max M 0, le_max_right _ _, fun v hv => (hM v hv).trans (le_max_left _ _)⟩

theorem mem_closedBox_of_mem_box {v : Fin d → ℝ} (hv : v ∈ SmoothEngine.box (Fin d) 1) :
    v ∈ closedBox d 1 :=
  box_subset_closedBox' 1 hv

/-- The field family is flat of order `0` with exponential growth in the coupling. -/
theorem flatOn_fieldFam {η ζ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    ∃ C M : ℝ, 0 ≤ C ∧ ∀ τ, 0 ≤ τ →
      FlatOn (fieldFam η ζ τ) 0 (C * (1 + τ) ^ 0 * Real.exp (M * τ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  refine ⟨C, M, hC0, fun τ hτ v hv => ?_⟩
  have hv' := mem_closedBox_of_mem_box hv
  have hmono : mono (0 : Fin d → ℕ) v = 1 := by simp [mono]
  rw [hmono, mul_one, pow_zero, mul_one]
  unfold fieldFam
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (hC v hv') ?_ (Real.exp_pos _).le hC0
  rw [Real.exp_le_exp]
  calc τ * ζ v ≤ τ * |ζ v| := by gcongr; exact le_abs_self _
    _ ≤ τ * M := by gcongr; exact hM v hv'
    _ = M * τ := mul_comm _ _

end Bounds

/-! ### Pointwise identities on the box -/

section Pointwise

variable (h k : Fin d → ℕ)

theorem mono_two_mul_eq_sq (v : Fin d → ℝ) :
    mono (fun i => 2 * k i) v = mono k v ^ 2 := by
  unfold mono
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

theorem sqrt_mono_two_mul {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    Real.sqrt (mono (fun i => 2 * k i) v) = mono k v := by
  rw [mono_two_mul_eq_sq, Real.sqrt_sq (mono_pos k hv).le]

/-- `v^h (v^{2k})^{−s} = cpowWeight h k s v` on the positive box. -/
theorem mono_mul_cpow_neg {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) (s : ℂ) :
    ((mono h v : ℝ) : ℂ) * ((mono (fun i => 2 * k i) v : ℝ) : ℂ) ^ (-s) =
      cpowWeight h k s v := by
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have hmono : ∀ a : Fin d → ℕ, mono a v = Real.exp (logSum a v) := fun a => by
    unfold mono logSum
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Real.exp_nat_mul, Real.exp_log (hv i)]
  have hlog : Real.log (mono (fun i => 2 * k i) v) = 2 * logSum k v := by
    rw [hmono, Real.log_exp]
    unfold logSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hK.ne'), ← Complex.ofReal_log hK.le, hlog,
    hmono h, Complex.ofReal_exp, ← Complex.exp_add]
  unfold cpowWeight
  congr 1
  push_cast
  ring

end Pointwise

/-! ### The Mellin integrand of the empirical integral -/

section MellinIntegrand

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The empirical integrand in the paper's form. -/
noncomputable def empIntegrandFun (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ)
    (v : Fin d → ℝ) : ℝ :=
  η v * mono h v * Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v)

theorem continuous_empIntegrandFun (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    Continuous fun z : ℝ × (Fin d → ℝ) => empIntegrandFun η ζ h k z.1 z.2 := by
  unfold empIntegrandFun
  refine ((hη.continuous.comp continuous_snd).mul ((continuous_mono h).comp continuous_snd)).mul
    (Real.continuous_exp.comp ?_)
  refine ((continuous_neg.comp continuous_fst).mul
    ((continuous_mono _).comp continuous_snd)).add ?_
  exact ((Real.continuous_sqrt.comp continuous_fst).mul
    ((continuous_mono k).comp continuous_snd)).mul (hζ.continuous.comp continuous_snd)

/-- The Mellin double integrand `N^{s−1} η(v) v^h e^{−N v^{2k} + √N v^k ζ(v)}`. -/
noncomputable def mellinEmpIntegrand (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (s : ℂ)
    (z : ℝ × (Fin d → ℝ)) : ℂ :=
  (z.1 : ℂ) ^ (s - 1) * (empIntegrandFun η ζ h k z.1 z.2 : ℂ)

theorem measurable_mellinEmpIntegrand (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (s : ℂ) :
    Measurable (mellinEmpIntegrand η ζ h k s) :=
  ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (Complex.measurable_ofReal.comp (continuous_empIntegrandFun hη hζ).measurable)

/-- The Mellin measure: Lebesgue measure on `(0,∞) × (0,1]^d`. -/
noncomputable def mellinMeasure (d : ℕ) : Measure (ℝ × (Fin d → ℝ)) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (SmoothEngine.box (Fin d) 1))

/-- The AM–GM majorant of the Mellin integrand at a fixed box point. -/
theorem norm_mellinEmpIntegrand_le {s : ℂ} {N : ℝ} (hN : 0 < N) {v : Fin d → ℝ}
    (hv : ∀ i, 0 < v i) {M : ℝ} (hζv : |ζ v| ≤ M) :
    ‖mellinEmpIntegrand η ζ h k s (N, v)‖ ≤
      |η v| * mono h v * Real.exp (M ^ 2 / 2) *
        (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) := by
  unfold mellinEmpIntegrand empIntegrandFun
  simp only
  rw [norm_cpow_mul_ofReal hN, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (mono_pos h hv)]
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have htilt := exp_tilt_le hK (mono k v * ζ v) hN.le
  have hH : (mono k v * ζ v) ^ 2 / (2 * mono (fun i => 2 * k i) v) = ζ v ^ 2 / 2 := by
    rw [mono_two_mul_eq_sq]
    have := (mono_pos k hv).ne'
    field_simp
  rw [hH] at htilt
  have hζ2 : Real.exp (ζ v ^ 2 / 2) ≤ Real.exp (M ^ 2 / 2) := by
    rw [Real.exp_le_exp]
    have := sq_abs (ζ v)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hζv
    nlinarith [abs_nonneg (ζ v)]
  have hN' : 0 ≤ N ^ (s.re - 1) := Real.rpow_nonneg hN.le _
  have hexp : Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v) ≤
      Real.exp (M ^ 2 / 2) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N) := by
    rw [mul_assoc (Real.sqrt N)]
    exact htilt.trans (mul_le_mul_of_nonneg_right hζ2 (Real.exp_pos _).le)
  have hηm : 0 ≤ |η v| * mono h v := mul_nonneg (abs_nonneg _) (mono_pos h hv).le
  calc N ^ (s.re - 1) * (|η v| * mono h v *
        Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * mono k v * ζ v))
      ≤ N ^ (s.re - 1) * (|η v| * mono h v *
        (Real.exp (M ^ 2 / 2) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hηm) hN'
    _ = _ := by ring

/-- ★ **Absolute integrability of the Mellin double integral** on the initial strip. -/
theorem integrable_mellinEmpIntegrand (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {s : ℂ}
    (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    Integrable (mellinEmpIntegrand η ζ h k s) (mellinMeasure d) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, _, hM⟩ := exists_abs_bound_closedBox hζ
  have hmeas := (measurable_mellinEmpIntegrand (h := h) (k := k) hη hζ s).aestronglyMeasurable
    (μ := mellinMeasure d)
  unfold mellinMeasure
  rw [integrable_prod_iff' hmeas]
  constructor
  · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    refine Eventually.of_forall fun v hv => ?_
    have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
    have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv'
    have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1)
      (b := mono (fun i => 2 * k i) v / 2) (by linarith) one_pos (by positivity)).const_mul
      (|η v| * mono h v * Real.exp (M ^ 2 / 2))
    refine hint.mono' ((measurable_mellinEmpIntegrand hη hζ s).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun N hN => ?_
    have := norm_mellinEmpIntegrand_le (η := η) (ζ := ζ) (h := h) (k := k) (s := s) hN hv'
      (hM v (mem_closedBox_of_mem_box hv))
    simp only [Real.rpow_one] at this ⊢
    exact this
  · -- the inner integral is bounded by the population zeta integrand
    have hc : ∀ i, -1 < (h i : ℝ) + (-2 * (k i : ℝ) * s.re) := fun i => by linarith [hs i]
    have hbox : Integrable (fun v : Fin d → ℝ =>
        Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re) *
          ∏ i, v i ^ ((h i : ℝ) + (-2 * (k i : ℝ) * s.re)))
        (volume.restrict (SmoothEngine.box (Fin d) 1)) := by
      have := (integrableOn_prod_rpow_mul_log_pow hc (fun i => 2 * (k i : ℝ)) 0
        zero_le_one).const_mul (Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re))
      simp only [pow_zero, mul_one] at this
      exact this
    refine hbox.mono' ?_ ?_
    · exact ((measurable_mellinEmpIntegrand (h := h) (k := k) hη hζ
        s).norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
      refine Eventually.of_forall fun v hv => ?_
      have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
      have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv'
      have hvc := mem_closedBox_of_mem_box hv
      -- the majorant integral in `N`
      have hmaj : ∫ N in Ioi (0 : ℝ), |η v| * mono h v * Real.exp (M ^ 2 / 2) *
          (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) =
          |η v| * mono h v * Real.exp (M ^ 2 / 2) *
            ((mono (fun i => 2 * k i) v / 2) ^ (-s.re) * Real.Gamma s.re) := by
        rw [integral_const_mul]
        congr 1
        have := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s.re - 1)
          (b := mono (fun i => 2 * k i) v / 2) one_pos (by linarith) (by positivity)
        simp only [Real.rpow_one, sub_add_cancel, div_one, mul_one] at this
        rw [this]
      have hint : IntegrableOn (fun N : ℝ => |η v| * mono h v * Real.exp (M ^ 2 / 2) *
          (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N))) (Ioi 0) := by
        refine IntegrableOn.congr_fun (Integrable.const_mul (integrableOn_rpow_mul_exp_neg_mul_rpow
          (p := 1) (s := s.re - 1) (b := mono (fun i => 2 * k i) v / 2) (by linarith) one_pos
          (by positivity)) (|η v| * mono h v * Real.exp (M ^ 2 / 2))) (fun N _ => ?_)
          measurableSet_Ioi
        simp only [Real.rpow_one]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ N in Ioi (0 : ℝ), ‖mellinEmpIntegrand η ζ h k s (N, v)‖
          ≤ ∫ N in Ioi (0 : ℝ), |η v| * mono h v * Real.exp (M ^ 2 / 2) *
              (N ^ (s.re - 1) * Real.exp (-(mono (fun i => 2 * k i) v / 2) * N)) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
            exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun N hN =>
              norm_mellinEmpIntegrand_le hN hv' (hM v hvc))
        _ = |η v| * mono h v * Real.exp (M ^ 2 / 2) *
              ((mono (fun i => 2 * k i) v / 2) ^ (-s.re) * Real.Gamma s.re) := hmaj
        _ ≤ Cη * Real.exp (M ^ 2 / 2) * ((1 / 2) ^ (-s.re) * Real.Gamma s.re) *
              ∏ i, v i ^ ((h i : ℝ) + (-2 * (k i : ℝ) * s.re)) := by
            have hG : 0 ≤ Real.Gamma s.re := Real.Gamma_nonneg_of_nonneg hs0.le
            have hpow : (mono (fun i => 2 * k i) v / 2) ^ (-s.re) =
                (1 / 2) ^ (-s.re) * ∏ i, v i ^ (-2 * (k i : ℝ) * s.re) := by
              rw [div_eq_mul_one_div, mul_comm, Real.mul_rpow (by norm_num) hK.le]
              congr 1
              unfold mono
              rw [← Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hv' i).le _]
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [← Real.rpow_natCast, ← Real.rpow_mul (hv' i).le]
              congr 1
              push_cast
              ring
            rw [hpow, ← mono_mul_prod_rpow h _ hv']
            have hη' : |η v| ≤ Cη := hCη v hvc
            have hm0 : 0 ≤ mono h v := (mono_pos h hv').le
            have hP0 : 0 ≤ ∏ i, v i ^ (-2 * (k i : ℝ) * s.re) :=
              Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hv' i).le _
            have h20 : (0 : ℝ) ≤ (1 / 2) ^ (-s.re) := Real.rpow_nonneg (by norm_num) _
            have hX : 0 ≤ (1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) *
                Real.Gamma s.re :=
              mul_nonneg (mul_nonneg h20 hP0) hG
            calc |η v| * mono h v * Real.exp (M ^ 2 / 2) *
                  ((1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) * Real.Gamma s.re)
                ≤ Cη * mono h v * Real.exp (M ^ 2 / 2) *
                  ((1 / 2) ^ (-s.re) * (∏ i, v i ^ (-2 * (k i : ℝ) * s.re)) * Real.Gamma s.re) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hη' hm0) (Real.exp_pos _).le) hX
              _ = _ := by ring

end MellinIntegrand

/-! ### The Mellin identity -/

section Identity

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The inner Mellin integral at a box point: `∫_0^∞ N^{s−1} η v^h e^{−Nv^{2k}+√N v^k ζ} dN
= η(v) · cpowWeight h k s v · S(s, ζ(v))`. -/
theorem integral_mellinEmpIntegrand_eq {s : ℂ} {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    ∫ N in Ioi (0 : ℝ), mellinEmpIntegrand η ζ h k s (N, v) =
      (η v : ℂ) * cpowWeight h k s v * fluctuationCplx s (ζ v) := by
  have hK : 0 < mono (fun i => 2 * k i) v := mono_pos _ hv
  have hfun : (fun N : ℝ => mellinEmpIntegrand η ζ h k s (N, v)) =
      fun N : ℝ => ((η v * mono h v : ℝ) : ℂ) * ((N : ℂ) ^ (s - 1) •
        (Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * (mono k v * ζ v)) : ℂ)) := by
    funext N
    unfold mellinEmpIntegrand empIntegrandFun
    simp only [smul_eq_mul]
    push_cast
    ring_nf
  rw [hfun, integral_const_mul]
  change ((η v * mono h v : ℝ) : ℂ) * mellin (fun N : ℝ =>
    (Real.exp (-N * mono (fun i => 2 * k i) v + Real.sqrt N * (mono k v * ζ v)) : ℂ)) s = _
  rw [mellin_exp_tilt hK, sqrt_mono_two_mul k hv,
    mul_div_cancel_left₀ _ (mono_pos k hv).ne', Complex.ofReal_mul, mul_assoc,
    ← mul_assoc ((mono h v : ℝ) : ℂ), mono_mul_cpow_neg h k hv s, mul_assoc]

/-- The coupled integrand of the field family in the paper's form. -/
theorem coupIntegrand_fieldFam_zero (s : ℂ) (z : ℝ × (Fin d → ℝ)) :
    coupIntegrand (fieldFam η ζ) h k 0 s z =
      (η z.2 : ℂ) * cpowWeight h k s z.2 *
        ((z.1 : ℂ) ^ (s - 1) * (Real.exp (-z.1 + ζ z.2 * Real.sqrt z.1) : ℂ)) := by
  unfold coupIntegrand coupKernel fieldFam
  rw [Real.exp_add]
  push_cast
  ring_nf

/-- ★★ **The Mellin transform of the empirical chart integral is the coupled chart zeta
functional of the field family**, on the initial strip. -/
theorem mellin_empIntegral_eq_coupledChartZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    {s : ℂ} (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    mellin (fun N => (empIntegral η ζ h k N : ℂ)) s = coupledChartZeta (fieldFam η ζ) h k s := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_fieldFam hη hζ
  have hcont : Continuous fun z : ℝ × (Fin d → ℝ) => fieldFam η ζ z.1 z.2 :=
    (contDiff_fieldFam_joint hη hζ).continuous
  -- step 1: the Mellin transform as a double integral, and the first interchange
  have h1 : mellin (fun N => (empIntegral η ζ h k N : ℂ)) s =
      ∫ v in SmoothEngine.box (Fin d) 1, ∫ N in Ioi (0 : ℝ),
        mellinEmpIntegrand η ζ h k s (N, v) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
      (f := fun N v => mellinEmpIntegrand η ζ h k s (N, v))
      (integrable_mellinEmpIntegrand hη hζ hs0 hs)
    rw [← hswap]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun N _ => ?_
    beta_reduce
    rw [empIntegral_eq, ← integral_complex_ofReal, smul_eq_mul, ← integral_const_mul]
    rfl
  -- step 2: the inner integrals
  have h2 : ∫ v in SmoothEngine.box (Fin d) 1, ∫ N in Ioi (0 : ℝ),
      mellinEmpIntegrand η ζ h k s (N, v) =
      ∫ v in SmoothEngine.box (Fin d) 1, ∫ t in Ioi (0 : ℝ),
        coupIntegrand (fieldFam η ζ) h k 0 s (t, v) := by
    refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v hv => ?_
    have hv' : ∀ i, 0 < v i := fun i => SmoothEngine.pos_of_mem_box hv i
    rw [integral_mellinEmpIntegrand_eq hv']
    unfold fluctuationCplx
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [coupIntegrand_fieldFam_zero]
  -- step 3: the second interchange
  have hint := integrable_coupIntegrand hcont hC hflat h k 0 hs0 hs.flatStrip
  have h3 : ∫ v in SmoothEngine.box (Fin d) 1, ∫ t in Ioi (0 : ℝ),
      coupIntegrand (fieldFam η ζ) h k 0 s (t, v) = coupledLogMoment (fieldFam η ζ) h k 0 s := by
    unfold coupledLogMoment coupMeasure
    rw [integral_prod _ hint]
    exact (integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
      (f := fun t v => coupIntegrand (fieldFam η ζ) h k 0 s (t, v)) hint).symm
  rw [h1, h2, h3, coupledChartZeta_eq_logMoment_zero hcont hC hflat h k hs0 hs.flatStrip]

end Identity

/-! ### Local integrability and boundedness at the origin -/

section Regularity

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

theorem measurableSet_closedBox (b : ℝ) : MeasurableSet (closedBox d b) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

instance isFiniteMeasure_restrict_box :
    IsFiniteMeasure (volume.restrict (SmoothEngine.box (Fin d) 1)) :=
  isFiniteMeasure_restrict.2 (volume_box_lt_top 1).ne

/-- The empirical integral as a tilt integral with globally bounded data. -/
theorem empIntegral_eq_integral_tilt (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral η ζ h k N = ∫ v, (closedBox d 1).indicator (fun v => η v * mono h v) v *
      Real.exp (-N * mono (fun i => 2 * k i) v +
        Real.sqrt N * (closedBox d 1).indicator (fun v => mono k v * ζ v) v)
      ∂(volume.restrict (SmoothEngine.box (Fin d) 1)) := by
  rw [empIntegral_eq]
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v hv => ?_
  have hv' := mem_closedBox_of_mem_box hv
  simp only [Set.indicator_of_mem hv']
  ring_nf

theorem abs_indicator_le {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ v ∈ closedBox d 1, |f v| ≤ C) (v : Fin d → ℝ) :
    |(closedBox d 1).indicator f v| ≤ C := by
  by_cases hv : v ∈ closedBox d 1
  · rw [Set.indicator_of_mem hv]; exact hf v hv
  · rw [Set.indicator_of_notMem hv, abs_zero]; exact hC

theorem mono_le_one_closedBox (a : Fin d → ℕ) {v : Fin d → ℝ} (hv : v ∈ closedBox d 1) :
    mono a v ≤ 1 :=
  Finset.prod_le_one (fun i _ => pow_nonneg ((mem_closedBox.1 hv i).1) _)
    fun i _ => pow_le_one₀ ((mem_closedBox.1 hv i).1) ((mem_closedBox.1 hv i).2)

theorem mono_nonneg_closedBox (a : Fin d → ℕ) {v : Fin d → ℝ} (hv : v ∈ closedBox d 1) :
    0 ≤ mono a v :=
  Finset.prod_nonneg fun i _ => pow_nonneg ((mem_closedBox.1 hv i).1) _

/-- ★ The empirical integral is locally integrable on `(0, ∞)`. -/
theorem locallyIntegrableOn_empIntegral (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    LocallyIntegrableOn (fun N => (empIntegral η ζ h k N : ℂ)) (Ioi 0) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  have hobs : ∀ v, |(closedBox d 1).indicator (fun v => η v * mono h v) v| ≤ Cη :=
    abs_indicator_le hCη0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox h hv)]
      calc |η v| * mono h v ≤ Cη * 1 :=
            mul_le_mul (hCη v hv) (mono_le_one_closedBox h hv) (mono_nonneg_closedBox h hv) hCη0
        _ = Cη := mul_one _
  have hΞ : ∀ v, |(closedBox d 1).indicator (fun v => mono k v * ζ v) v| ≤ M :=
    abs_indicator_le hM0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox k hv)]
      calc mono k v * |ζ v| ≤ 1 * M :=
            mul_le_mul (mono_le_one_closedBox k hv) (hM v hv) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
  have hK : ∀ᵐ v ∂(volume.restrict (SmoothEngine.box (Fin d) 1)),
      0 ≤ mono (fun i => 2 * k i) v := by
    rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    exact Eventually.of_forall fun v hv => (mono_pos _ fun i => SmoothEngine.pos_of_mem_box hv i).le
  have := locallyIntegrableOn_integral_tilt (ν := volume.restrict (SmoothEngine.box (Fin d) 1))
    (continuous_mono _).measurable
    (((continuous_mono k).mul hζ.continuous).measurable.indicator (measurableSet_closedBox 1))
    ((hη.continuous.mul (continuous_mono h)).measurable.indicator (measurableSet_closedBox 1))
    hK hΞ hobs
  have hfun : (fun N => (empIntegral η ζ h k N : ℂ)) = fun N =>
      ((∫ v, (closedBox d 1).indicator (fun v => η v * mono h v) v *
        Real.exp (-N * mono (fun i => 2 * k i) v +
          Real.sqrt N * (closedBox d 1).indicator (fun v => mono k v * ζ v) v)
        ∂(volume.restrict (SmoothEngine.box (Fin d) 1)) : ℝ) : ℂ) := by
    funext N
    rw [empIntegral_eq_integral_tilt]
  rw [hfun]
  exact this

/-- ★ The empirical integral is bounded at `0⁺`. -/
theorem empIntegral_isBigO_one_zero (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    (fun N => (empIntegral η ζ h k N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ) := by
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_bound_closedBox hη
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound_closedBox hζ
  have hobs : ∀ v, |(closedBox d 1).indicator (fun v => η v * mono h v) v| ≤ Cη :=
    abs_indicator_le hCη0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox h hv)]
      calc |η v| * mono h v ≤ Cη * 1 :=
            mul_le_mul (hCη v hv) (mono_le_one_closedBox h hv) (mono_nonneg_closedBox h hv) hCη0
        _ = Cη := mul_one _
  have hΞ : ∀ v, |(closedBox d 1).indicator (fun v => mono k v * ζ v) v| ≤ M :=
    abs_indicator_le hM0 fun v hv => by
      rw [abs_mul, abs_of_nonneg (mono_nonneg_closedBox k hv)]
      calc mono k v * |ζ v| ≤ 1 * M :=
            mul_le_mul (mono_le_one_closedBox k hv) (hM v hv) (abs_nonneg _) zero_le_one
        _ = M := one_mul _
  have hK : ∀ᵐ v ∂(volume.restrict (SmoothEngine.box (Fin d) 1)),
      0 ≤ mono (fun i => 2 * k i) v := by
    rw [ae_restrict_iff' (SmoothEngine.measurableSet_box 1)]
    exact Eventually.of_forall fun v hv => (mono_pos _ fun i => SmoothEngine.pos_of_mem_box hv i).le
  have := integral_tilt_isBigO_one (ν := volume.restrict (SmoothEngine.box (Fin d) 1)) hK hΞ hobs
  refine this.congr_left fun N => ?_
  rw [empIntegral_eq_integral_tilt]

end Regularity

end Grammar
