/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthFourRateLinear

/-!
# The depth-five polynomial limit

`√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ → E₅` (★★★ `gaussLaplaceL_five_constant`), the DCLI route one
depth up: with the full depth-four polynomial `P₄(u) = A₄u³ + B₄u² + C₄u + D₄` (`depthFourJet`) and
the residual `q₄(v) = Z₄(v²) − 1_{v>1} P₄(2 log v)/v` (`depthFiveQ`), the linear-log rate DCLIV
gives `|q₄(v)| ≤ K(1 + 2 log v)/v²` on `(1, ∞)`, so `q₄` is integrable; the scalar recursion
`√N Z₅ = 2∫₀^∞ γ(v/√N) Z₄(v²) dv`, the substitution `x = v/√N` on the tail, `γ = (h + 1_{(0,1]})/s`,
the flat part `∫_a^1 P₄(ℓ + 2 log x)/x = A₄ℓ⁴/8 + B₄ℓ³/6 + C₄ℓ²/4 + D₄ℓ/2` and the `h`-part
`Σ_j c_j(ℓ) ∫_a^∞ h log^j x/x` (`j ≤ 3`) with the cutoff moments `O(1/√N)`.  The quartic
coefficients `A₅ = gaussCoeffA 1`, `B₅ = gaussCoeffB 1`, `C₅ = thirdCoeff 1` are the existing
all-depth ones; the linear coefficient `D₅ = [D₄ + 2C₄R₀ + 8B₄J + 24A₄J₂]/s` (`depthFiveLinCoeff`)
and the constant `E₅ = (2/s)[Q₄ + D₄R₀ + 2C₄J + 4B₄J₂ + 8A₄J₃]` (`depthFiveConst`) are new,
with `J₃ = ∫₀^∞ h log³x/x` (`gaussJlog3`) and `Q₄ = ∫₀^∞ q₄` (`depthFiveQint`).
Astra round 17, target 3.  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The depth-four polynomial and the residual `q₄` -/

/-- The full depth-four polynomial `P₄(u) = A₄u³ + B₄u² + C₄u + D₄`. -/
noncomputable def depthFourJet (u : ℝ) : ℝ :=
  gaussCoeffA 0 * u ^ 3 + gaussCoeffB 0 * u ^ 2 + thirdCoeff 0 * u + depthFourConst

/-- `q₄(v) = Z₄(v²) − 1_{(1,∞)}(v) P₄(2 log v)/v`. -/
noncomputable def depthFiveQ (v : ℝ) : ℝ :=
  gaussLaplaceL 4 (v ^ 2) - (Ioi (1 : ℝ)).indicator (fun v => depthFourJet (2 * Real.log v) / v) v

theorem measurable_gaussLaplaceL_four_sq : Measurable fun v : ℝ => gaussLaplaceL 4 (v ^ 2) := by
  have e : (fun v : ℝ => gaussLaplaceL 4 (v ^ 2)) =
      fun v => ∫ x : ℝ, gaussDensity x * gaussLaplaceL 3 ((v * x) ^ 2) := by
    funext v
    rw [gaussLaplaceL_succ_scalar 3 (sq_nonneg v)]
    simp only [mul_pow]
  rw [e]
  exact ((continuous_gaussDensity.measurable.comp measurable_snd).mul
    (measurable_gaussLaplaceL_three_sq.comp
      (measurable_fst.mul measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

theorem continuous_depthFourJet : Continuous depthFourJet := by
  unfold depthFourJet; fun_prop

theorem measurable_depthFiveQ : Measurable depthFiveQ := by
  unfold depthFiveQ
  refine measurable_gaussLaplaceL_four_sq.sub (Measurable.indicator ?_ measurableSet_Ioi)
  exact (continuous_depthFourJet.measurable.comp (measurable_const.mul Real.measurable_log)).div
    measurable_id

theorem depthFiveQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthFiveQ v = gaussLaplaceL 4 (v ^ 2) := by
  unfold depthFiveQ
  rw [indicator_of_notMem (fun h : v ∈ Ioi (1 : ℝ) => absurd hv.2 (not_le.2 h)), sub_zero]

/-- On `(1,∞)`: `|q₄(v)| ≤ K(1 + 2 log v)/v²` from the linear-log depth-four rate at `N = v²`. -/
theorem depthFiveQ_outer_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 1 < v →
    |depthFiveQ v| ≤ K * (1 + 2 * Real.log v) / v ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := gaussLaplaceL_four_constant_rate_linear
  refine ⟨K, hK0, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have h := hK (v ^ 2) hv2
  rw [Real.sqrt_sq hv0.le, Real.log_pow, Nat.cast_ofNat] at h
  unfold depthFiveQ depthFourJet
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  have e : gaussLaplaceL 4 (v ^ 2) - (gaussCoeffA 0 * (2 * Real.log v) ^ 3 +
      gaussCoeffB 0 * (2 * Real.log v) ^ 2 + thirdCoeff 0 * (2 * Real.log v) +
        depthFourConst) / v =
      (v * gaussLaplaceL 4 (v ^ 2) - gaussCoeffA 0 * (2 * Real.log v) ^ 3 -
        gaussCoeffB 0 * (2 * Real.log v) ^ 2 - thirdCoeff 0 * (2 * Real.log v) -
          depthFourConst) / v := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
  calc |v * gaussLaplaceL 4 (v ^ 2) - gaussCoeffA 0 * (2 * Real.log v) ^ 3 -
        gaussCoeffB 0 * (2 * Real.log v) ^ 2 - thirdCoeff 0 * (2 * Real.log v) -
          depthFourConst| ≤ K * (1 + 2 * Real.log v) / v := h
    _ = K * (1 + 2 * Real.log v) / v ^ 2 * v := by field_simp

theorem integrableOn_depthFiveQ_inner : IntegrableOn depthFiveQ (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    measurable_depthFiveQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  rw [depthFiveQ_inner hv, Real.norm_eq_abs, abs_of_nonneg (gaussLaplaceL_nonneg 4 _)]
  exact gaussLaplaceL_le_one 4 (sq_nonneg _)

theorem integrableOn_depthFiveQ_outer : IntegrableOn depthFiveQ (Ioi 1) := by
  obtain ⟨K, hK0, hK⟩ := depthFiveQ_outer_le
  have h : IntegrableOn (fun v : ℝ => K * v ^ (-2 : ℝ) + 2 * K * (v ^ (-2 : ℝ) * Real.log v))
      (Ioi 1) := by
    have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul K
    have h2 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).const_mul (2 * K)
    refine IntegrableOn.congr_fun (h1.add h2) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, zero_sub]
  refine h.mono' measurable_depthFiveQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  rw [Real.norm_eq_abs]
  refine (hK v hv1).trans (le_of_eq ?_)
  rw [Real.rpow_neg hv0.le, Real.rpow_two]
  field_simp

theorem integrableOn_depthFiveQ : IntegrableOn depthFiveQ (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact integrableOn_depthFiveQ_inner.union integrableOn_depthFiveQ_outer

/-! ### The constants -/

/-- `J₃ = ∫₀^∞ h(x) log³x/x dx`. -/
noncomputable def gaussJlog3 : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 3 / x

/-- `Q₄ = ∫₀^∞ q₄`. -/
noncomputable def depthFiveQint : ℝ := ∫ v in Ioi (0 : ℝ), depthFiveQ v

/-- The depth-five linear coefficient `D₅ = [D₄ + 2C₄R₀ + 8B₄J + 24A₄J₂]/s`. -/
noncomputable def depthFiveLinCoeff : ℝ :=
  (depthFourConst + 2 * thirdCoeff 0 * gaussR₀ + 8 * gaussCoeffB 0 * gaussJlog +
    24 * gaussCoeffA 0 * gaussJlog2) / Real.sqrt (2 * Real.pi)

/-- The depth-five constant `E₅ = (2/s)[Q₄ + D₄R₀ + 2C₄J + 4B₄J₂ + 8A₄J₃]`. -/
noncomputable def depthFiveConst : ℝ :=
  2 / Real.sqrt (2 * Real.pi) * (depthFiveQint + depthFourConst * gaussR₀ +
    2 * thirdCoeff 0 * gaussJlog + 4 * gaussCoeffB 0 * gaussJlog2 + 8 * gaussCoeffA 0 * gaussJlog3)

/-! ### `√N Z₅ = 2∫₀^∞ γ(v/√N) Z₄(v²) dv` -/

theorem integrable_gaussDensity_mul_gaussLaplaceL_four {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL 4 (N * x ^ 2)) := by
  have hm : Measurable fun x : ℝ => gaussLaplaceL 4 (N * x ^ 2) := by
    have e : (fun x : ℝ => gaussLaplaceL 4 (N * x ^ 2)) =
        fun x => gaussLaplaceL 4 ((Real.sqrt N * x) ^ 2) := by
      funext x; rw [mul_pow, Real.sq_sqrt hN]
    rw [e]
    exact measurable_gaussLaplaceL_four_sq.comp (measurable_const.mul measurable_id)
  refine integrable_gaussDensity.mono'
    (continuous_gaussDensity.measurable.mul hm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg x),
    abs_of_nonneg (gaussLaplaceL_nonneg 4 _)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg x) (gaussLaplaceL_le_one 4 (by positivity))

/-- `√N Z₅(N) = 2 ∫₀^∞ γ(v/√N) Z₄(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_five_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 5 N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 4 (v ^ 2) := by
  rw [gaussLaplaceL_succ_scalar 4 hN.le]
  have h := integral_comp_abs (f := fun x : ℝ => gaussDensity x * gaussLaplaceL 4 (N * x ^ 2))
  simp only [gaussDensity_abs, sq_abs] at h
  rw [h]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h2 := integral_comp_mul_left_Ioi
    (fun x => gaussDensity x * gaussLaplaceL 4 (N * x ^ 2)) 0 hb
  rw [mul_zero, smul_eq_mul, inv_div, div_one] at h2
  calc Real.sqrt N * (2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 4 (N * x ^ 2))
      = 2 * (Real.sqrt N * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 4 (N * x ^ 2)) := by
        ring
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (1 / Real.sqrt N * v) *
          gaussLaplaceL 4 (N * (1 / Real.sqrt N * v) ^ 2) := by rw [h2]
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 4 (v ^ 2) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
          mul_div_cancel₀ _ hN.ne']

/-! ### The residual term `2∫ γ(v/√N) q₄ → (2/s) Q₄` -/

theorem tendsto_depthFiveQ_term :
    Tendsto (fun N : ℝ => 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v)
      atTop (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFiveQint)) := by
  unfold depthFiveQint
  have e : 2 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (0 : ℝ), depthFiveQ v =
      2 * ∫ v in Ioi (0 : ℝ), 1 / Real.sqrt (2 * Real.pi) * depthFiveQ v := by
    rw [integral_const_mul]; ring
  rw [e]
  refine Tendsto.const_mul 2 ?_
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun N v => gaussDensity (v / Real.sqrt N) * depthFiveQ v)
    (f := fun v => 1 / Real.sqrt (2 * Real.pi) * depthFiveQ v)
    (fun v => 1 / Real.sqrt (2 * Real.pi) * |depthFiveQ v|)
    (Eventually.of_forall fun N => (continuous_gaussDensity.comp (continuous_id.div_const _)
      |>.measurable.mul measurable_depthFiveQ).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_)
    (integrableOn_depthFiveQ.abs.const_mul _)
    (Eventually.of_forall fun v => ?_)
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
    exact mul_le_mul_of_nonneg_right (gaussDensity_le_inv_sqrt _) (abs_nonneg _)
  · have h1 : Tendsto (fun N : ℝ => v / Real.sqrt N) atTop (𝓝 0) := by
      have := tendsto_one_div_sqrt.const_mul v
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have := ((continuous_gaussDensity.tendsto 0).comp h1).mul_const (depthFiveQ v)
    rw [gaussDensity_zero] at this
    exact this

/-! ### The tail `2∫ γ(v/√N) 1_{v>1} P₄(2 log v)/v` in the variable `x = v/√N` -/

/-- The tail integrand. -/
noncomputable def depthFiveTail (v : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun v => depthFourJet (2 * Real.log v) / v) v

theorem depthFiveQ_add_tail (v : ℝ) : depthFiveQ v + depthFiveTail v = gaussLaplaceL 4 (v ^ 2) := by
  unfold depthFiveQ depthFiveTail; ring

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL_four {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL 4 (v ^ 2))
      (Ioi 0) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => gaussDensity x * gaussLaplaceL 4 (N * x ^ 2)) 0 hb).2
    (by rw [mul_zero]; exact (integrable_gaussDensity_mul_gaussLaplaceL_four hN.le).integrableOn)
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp only
  rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
    mul_div_cancel₀ _ hN.ne']

theorem integrableOn_gaussDensity_div_mul_depthFiveQ {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFiveQ v) (Ioi 0) := by
  refine (integrableOn_depthFiveQ.abs.const_mul (1 / Real.sqrt (2 * Real.pi))).mono'
    ((continuous_gaussDensity.comp (continuous_id.div_const _)).measurable.mul
      measurable_depthFiveQ).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
  exact mul_le_mul_of_nonneg_right (gaussDensity_le_inv_sqrt _) (abs_nonneg _)

/-- `√N Z₅ = 2∫ γ(v/√N) q₄ + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_five_split {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 5 N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveTail v := by
  rw [sqrt_mul_gaussLaplaceL_five_eq hN, ← mul_add]
  congr 1
  have hT : IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFiveTail v)
      (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_gaussDensity_div_mul_gaussLaplaceL_four hN).sub
      (integrableOn_gaussDensity_div_mul_depthFiveQ (N := N))) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [← depthFiveQ_add_tail]
    ring
  rw [← integral_add (integrableOn_gaussDensity_div_mul_depthFiveQ (N := N)) hT]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [← depthFiveQ_add_tail]
  ring

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P₄(ℓ + 2 log x)/x dx`. -/
theorem depthFive_tail_integral_eq {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveTail v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have h := integral_comp_mul_left_Ioi
    (fun v => gaussDensity (v / Real.sqrt N) * depthFiveTail v) 0 hsN
  rw [mul_zero, smul_eq_mul] at h
  have h' : ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveTail v =
      Real.sqrt N * ∫ x in Ioi (0 : ℝ),
        gaussDensity (Real.sqrt N * x / Real.sqrt N) * depthFiveTail (Real.sqrt N * x) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hsN.ne', one_mul]
  rw [h', ← integral_const_mul]
  have e : ∀ x ∈ Ioi (0 : ℝ), Real.sqrt N *
      (gaussDensity (Real.sqrt N * x / Real.sqrt N) * depthFiveTail (Real.sqrt N * x)) =
      (Ioi (1 / Real.sqrt N)).indicator
        (fun x => gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [mul_div_cancel_left₀ _ hsN.ne']
    unfold depthFiveTail
    by_cases hm : x ∈ Ioi (1 / Real.sqrt N)
    · have hm1 : (1 : ℝ) < Real.sqrt N * x := by
        have : (1 : ℝ) / Real.sqrt N < x := hm
        rwa [div_lt_iff₀ hsN, mul_comm] at this
      rw [indicator_of_mem hm, indicator_of_mem (show Real.sqrt N * x ∈ Ioi (1 : ℝ) from hm1),
        Real.log_mul hsN.ne' hx0.ne', Real.log_sqrt hN.le]
      have hP : 2 * (Real.log N / 2 + Real.log x) = Real.log N + 2 * Real.log x := by ring
      rw [hP]
      field_simp
    · have hm1 : Real.sqrt N * x ∉ Ioi (1 : ℝ) := by
        intro h1
        apply hm
        have : (1 : ℝ) < Real.sqrt N * x := h1
        change (1 : ℝ) / Real.sqrt N < x
        rw [div_lt_iff₀ hsN, mul_comm]
        exact this
      rw [indicator_of_notMem hm, indicator_of_notMem hm1, mul_zero, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi (1 / Real.sqrt N) = Ioi (1 / Real.sqrt N) from
      inter_eq_right.2 fun x (hx : 1 / Real.sqrt N < x) =>
        (show (0 : ℝ) < x from lt_trans (by positivity) hx)]

/-! ### `γ = (h + 1_{(0,1]})/s`: the flat part and the `h`-part -/

/-- `P₄(ℓ + 2y)` as a polynomial in `y`. -/
theorem depthFourJet_shift (ℓ y : ℝ) :
    depthFourJet (ℓ + 2 * y) =
      (gaussCoeffA 0 * ℓ ^ 3 + gaussCoeffB 0 * ℓ ^ 2 + thirdCoeff 0 * ℓ + depthFourConst) +
      (6 * gaussCoeffA 0 * ℓ ^ 2 + 4 * gaussCoeffB 0 * ℓ + 2 * thirdCoeff 0) * y +
      (12 * gaussCoeffA 0 * ℓ + 4 * gaussCoeffB 0) * y ^ 2 +
      8 * gaussCoeffA 0 * y ^ 3 := by
  unfold depthFourJet; ring

theorem integrableOn_gaussH_depthFourJet {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N)) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have h0 := integrableOn_gaussH_log_pow 0 ha0 ha1
  have h1 := integrableOn_gaussH_log_pow 1 ha0 ha1
  have h2 := integrableOn_gaussH_log_pow 2 ha0 ha1
  have h3 := integrableOn_gaussH_log_pow 3 ha0 ha1
  have h0123 : IntegrableOn (fun x : ℝ =>
      (gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
        thirdCoeff 0 * Real.log N + depthFourConst) * (gaussH x * Real.log x ^ 0 / x) +
      (6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
        2 * thirdCoeff 0) * (gaussH x * Real.log x ^ 1 / x) +
      (12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0) * (gaussH x * Real.log x ^ 2 / x) +
      8 * gaussCoeffA 0 * (gaussH x * Real.log x ^ 3 / x)) (Ioi (1 / Real.sqrt N)) :=
    (((h0.const_mul _).add (h1.const_mul _)).add (h2.const_mul _)).add (h3.const_mul _)
  refine IntegrableOn.congr_fun h0123 (fun x _ => ?_) measurableSet_Ioi
  simp only [pow_zero, pow_one]
  rw [depthFourJet_shift]
  ring

theorem integrableOn_depthFourJet_div_Ioc {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => depthFourJet (Real.log N + 2 * Real.log x) / x)
      (Ioc (1 / Real.sqrt N) 1) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (ContinuousOn.comp continuous_depthFourJet.continuousOn
    (continuousOn_const.add (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_)))
    (mapsTo_univ _ _)) continuousOn_id fun x hx => ?_
  · rw [uIcc_of_le ha1] at hx
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))
  · rw [uIcc_of_le ha1] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)

/-- The tail splits into the flat part and the `h`-part. -/
theorem depthFive_tail_integral_split {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, depthFourJet (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have hind : IntegrableOn (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator
      (fun x => depthFourJet (Real.log N + 2 * Real.log x) / x) x) (Ioi (1 / Real.sqrt N)) := by
    have := (integrableOn_depthFourJet_div_Ioc hN).integrable_indicator measurableSet_Ioc
    refine this.integrableOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : 1 / Real.sqrt N < x := hx
    by_cases hm : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc (1 / Real.sqrt N) 1 from ⟨hx', hm⟩),
        indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨lt_trans ha0 hx', hm⟩)]
    · rw [indicator_of_notMem (fun h : x ∈ Ioc (1 / Real.sqrt N) 1 => hm h.2),
        indicator_of_notMem (fun h : x ∈ Ioc (0 : ℝ) 1 => hm h.2)]
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N),
      gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) * ((Ioc (0 : ℝ) 1).indicator
        (fun x => depthFourJet (Real.log N + 2 * Real.log x) / x) x +
        gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x) := by
    intro x hx
    have hx0 : 0 < x := lt_trans ha0 hx
    rw [gaussDensity_eq_gaussH]
    by_cases hm : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hm, indicator_of_mem hm, Pi.one_apply]
      field_simp
      ring
    · rw [indicator_of_notMem hm, indicator_of_notMem hm]
      field_simp
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_add hind (integrableOn_gaussH_depthFourJet hN),
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (1 / Real.sqrt N) ∩ Ioc 0 1 = Ioc (1 / Real.sqrt N) 1 from by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, lt_trans ha0 h1, h3⟩]

/-- The flat part exactly: `∫_a^1 P₄(ℓ + 2 log x)/x = A₄ℓ⁴/8 + B₄ℓ³/6 + C₄ℓ²/4 + D₄ℓ/2`. -/
theorem depthFive_flat_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthFourJet (Real.log N + 2 * Real.log x) / x =
      gaussCoeffA 0 * (Real.log N) ^ 4 / 8 + gaussCoeffB 0 * (Real.log N) ^ 3 / 6 +
        thirdCoeff 0 * (Real.log N) ^ 2 / 4 + depthFourConst * Real.log N / 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  set ℓ := Real.log N with hℓ
  set G : ℝ → ℝ := fun x => gaussCoeffA 0 * (ℓ + 2 * Real.log x) ^ 4 / 8 +
    gaussCoeffB 0 * (ℓ + 2 * Real.log x) ^ 3 / 6 + thirdCoeff 0 * (ℓ + 2 * Real.log x) ^ 2 / 4 +
    depthFourConst * (ℓ + 2 * Real.log x) / 2 with hG
  have hderiv : ∀ x ∈ uIcc (1 / Real.sqrt N) 1,
      HasDerivAt G (depthFourJet (ℓ + 2 * Real.log x) / x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hl : HasDerivAt (fun x : ℝ => ℓ + 2 * Real.log x) (2 * x⁻¹) x :=
      ((Real.hasDerivAt_log hx0.ne').const_mul 2).const_add ℓ
    have h4 : HasDerivAt (fun x : ℝ => gaussCoeffA 0 * (ℓ + 2 * Real.log x) ^ 4 / 8)
        (gaussCoeffA 0 * (((4 : ℕ) : ℝ) * (ℓ + 2 * Real.log x) ^ (4 - 1) * (2 * x⁻¹)) / 8) x :=
      ((hl.pow 4).const_mul _).div_const _
    have h3 : HasDerivAt (fun x : ℝ => gaussCoeffB 0 * (ℓ + 2 * Real.log x) ^ 3 / 6)
        (gaussCoeffB 0 * (((3 : ℕ) : ℝ) * (ℓ + 2 * Real.log x) ^ (3 - 1) * (2 * x⁻¹)) / 6) x :=
      ((hl.pow 3).const_mul _).div_const _
    have h2 : HasDerivAt (fun x : ℝ => thirdCoeff 0 * (ℓ + 2 * Real.log x) ^ 2 / 4)
        (thirdCoeff 0 * (((2 : ℕ) : ℝ) * (ℓ + 2 * Real.log x) ^ (2 - 1) * (2 * x⁻¹)) / 4) x :=
      ((hl.pow 2).const_mul _).div_const _
    have h1 : HasDerivAt (fun x : ℝ => depthFourConst * (ℓ + 2 * Real.log x) / 2)
        (depthFourConst * (2 * x⁻¹) / 2) x := (hl.const_mul _).div_const _
    have := ((h4.add h3).add h2).add h1
    refine this.congr_deriv ?_
    unfold depthFourJet
    norm_num
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => depthFourJet (ℓ + 2 * Real.log x) / x) volume
      (1 / Real.sqrt N) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact integrableOn_depthFourJet_div_Ioc hN
  rw [← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog : ℓ + 2 * Real.log (1 / Real.sqrt N) = 0 := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le, hℓ]; ring
  simp only [hG, Real.log_one, mul_zero, add_zero, hlog]
  ring

/-- The cutoff `h`-moments: `∫_a^∞ h P₄(ℓ + 2 log x)/x = Σ_j c_j(ℓ) ∫_a^∞ h log^j x/x`. -/
theorem depthFive_hpart_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      (gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
        thirdCoeff 0 * Real.log N + depthFourConst) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x / x) +
      (6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
        2 * thirdCoeff 0) * (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) +
      (12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
      8 * gaussCoeffA 0 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 3 / x := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have h0 := integrableOn_gaussH_log_pow 0 ha0 ha1
  have h1 := integrableOn_gaussH_log_pow 1 ha0 ha1
  have h2 := integrableOn_gaussH_log_pow 2 ha0 ha1
  have h3 := integrableOn_gaussH_log_pow 3 ha0 ha1
  simp only [pow_zero, pow_one] at h0 h1
  set c₀ := gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
    thirdCoeff 0 * Real.log N + depthFourConst with hc₀
  set c₁ := 6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
    2 * thirdCoeff 0 with hc₁
  set c₂ := 12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0 with hc₂
  have h01 : Integrable (fun x : ℝ => c₀ * (gaussH x * 1 / x) + c₁ * (gaussH x * Real.log x / x))
      (volume.restrict (Ioi (1 / Real.sqrt N))) :=
    (h0.const_mul _).add (h1.const_mul _)
  have h012 : Integrable (fun x : ℝ => (c₀ * (gaussH x * 1 / x) +
      c₁ * (gaussH x * Real.log x / x)) + c₂ * (gaussH x * Real.log x ^ 2 / x))
      (volume.restrict (Ioi (1 / Real.sqrt N))) :=
    h01.add (h2.const_mul _)
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N),
      gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      ((c₀ * (gaussH x * 1 / x) + c₁ * (gaussH x * Real.log x / x)) +
        c₂ * (gaussH x * Real.log x ^ 2 / x)) +
        8 * gaussCoeffA 0 * (gaussH x * Real.log x ^ 3 / x) := by
    intro x _
    rw [depthFourJet_shift, hc₀, hc₁, hc₂]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add h012 (h3.const_mul _),
    integral_add h01 (h2.const_mul _), integral_add (h0.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  simp only [mul_one]

/-! ### The assembled remainder and the limit -/

theorem tendsto_cube_log_div_sqrt :
    Tendsto (fun N : ℝ => (Real.log N) ^ 3 / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
  have h3 := h.pow 3
  simp only [zero_pow three_ne_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (N ^ (1 / 6 : ℝ)) 3, ← Real.rpow_mul hN.le]
  norm_num

theorem gaussCoeffA_zero_eq : gaussCoeffA 0 = 1 / (6 * Real.sqrt (2 * Real.pi) ^ 3) := by
  unfold gaussCoeffA; norm_num [Nat.factorial]

theorem gaussCoeffB_zero_eq : gaussCoeffB 0 =
    (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) / (2 * Real.sqrt (2 * Real.pi) ^ 3) := by
  unfold gaussCoeffB; norm_num [Nat.factorial]

theorem gaussCoeffA_one_eq : gaussCoeffA 1 = 1 / (24 * Real.sqrt (2 * Real.pi) ^ 4) := by
  unfold gaussCoeffA; norm_num [Nat.factorial]

theorem gaussCoeffB_one_eq : gaussCoeffB 1 =
    (6 * Real.log 2 - 4 * Real.eulerMascheroniConstant) / (6 * Real.sqrt (2 * Real.pi) ^ 4) := by
  unfold gaussCoeffB; norm_num [Nat.factorial]

theorem thirdCoeff_one_eq : thirdCoeff 1 = (thirdCoeff 0 / 2 + 2 * gaussCoeffB 0 * gaussR₀ +
    12 * gaussCoeffA 0 * gaussJlog) / Real.sqrt (2 * Real.pi) := by
  have h : thirdCoeff 1 = (thirdCoeff 0 / (((0 : ℕ) : ℝ) + 2) + 2 * gaussCoeffB 0 * gaussR₀ +
      4 * (((0 : ℕ) : ℝ) + 3) * gaussCoeffA 0 * gaussJlog) / Real.sqrt (2 * Real.pi) := rfl
  rw [h]; norm_num

/-- The assembled remainder: for `N ≥ 1`,
`√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ = 2∫γ(v/√N)q₄ + (2/s)[−c₀ε₀ − c₁ε₁ − c₂ε₂ + 8A₄(J₃ − ε₃) + D₄R₀ +
2C₄J + 4B₄J₂]`. -/
theorem sqrt_mul_gaussLaplaceL_five_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * (Real.log N) ^ 4 -
      gaussCoeffB 1 * (Real.log N) ^ 3 - thirdCoeff 1 * (Real.log N) ^ 2 -
      depthFiveLinCoeff * Real.log N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v) +
      2 / Real.sqrt (2 * Real.pi) *
        ((gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
          thirdCoeff 0 * Real.log N + depthFourConst) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        (6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
          2 * thirdCoeff 0) * (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        (12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
        8 * gaussCoeffA 0 *
          (gaussJlog3 - ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 3 / x) +
        depthFourConst * gaussR₀ + 2 * thirdCoeff 0 * gaussJlog +
        4 * gaussCoeffB 0 * gaussJlog2) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [sqrt_mul_gaussLaplaceL_five_split hN0, depthFive_tail_integral_eq hN0,
    depthFive_tail_integral_split hN, depthFive_flat_integral_eq hN, depthFive_hpart_integral_eq hN,
    integral_gaussH_div_Ioi ha0]
  have hJ := gaussH_log_pow_cutoff 1 ha0 ha1
  have hJ2 := gaussH_log_pow_cutoff 2 ha0 ha1
  have hJ3 := gaussH_log_pow_cutoff 3 ha0 ha1
  simp only [pow_one] at hJ
  rw [hJ, hJ2, hJ3]
  unfold depthFiveLinCoeff
  rw [thirdCoeff_one_eq, gaussCoeffA_one_eq, gaussCoeffB_one_eq, gaussCoeffA_zero_eq,
    gaussCoeffB_zero_eq]
  unfold gaussJlog gaussJlog2 gaussJlog3 gaussR₀
  set Q := ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v with hQ
  set E0 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hE0
  set J := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x with hJd
  set E1 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x with hE1
  set J2 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x with hJ2d
  set E2 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x with hE2
  set J3 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 3 / x with hJ3d
  set E3 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 3 / x with hE3
  set C := thirdCoeff 0 with hC
  set D := depthFourConst with hD
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  clear_value Q E0 J E1 J2 E2 J3 E3 C D S
  field_simp
  ring

/-- ★★★ **The depth-five constant**: `√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ → E₅`. -/
theorem gaussLaplaceL_five_constant :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * (Real.log N) ^ 4 -
      gaussCoeffB 1 * (Real.log N) ^ 3 - thirdCoeff 1 * (Real.log N) ^ 2 -
      depthFiveLinCoeff * Real.log N) atTop (𝓝 depthFiveConst) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ3 := tendsto_cube_log_div_sqrt
  have hℓ2 := tendsto_sq_log_div_sqrt
  have hℓ1 := tendsto_log_div_sqrt
  have hℓ0 := tendsto_one_div_sqrt
  have hpiece : ∀ (j : ℕ) (c₃ c₂ c₁ c₀ : ℝ),
      Tendsto (fun N : ℝ => (c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀) *
        ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x) atTop (𝓝 0) := by
    intro j c₃ c₂ c₁ c₀
    refine squeeze_zero_norm' ?_ (a := fun N : ℝ => (|c₃| * ((Real.log N) ^ 3 / Real.sqrt N) +
      |c₂| * ((Real.log N) ^ 2 / Real.sqrt N) + |c₁| * (Real.log N / Real.sqrt N) +
      |c₀| * (1 / Real.sqrt N)) * ((j + 1) ^ j / 2)) ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
      have hN0 : 0 < N := by linarith
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
      have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
      have hI := abs_integral_gaussH_log_pow_Ioc_le j ha0 ha1
      have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
      have hc : |c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀| ≤
          |c₃| * (Real.log N) ^ 3 + |c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀| := by
        calc |c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀|
            ≤ |c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2 + c₁ * Real.log N| + |c₀| :=
              abs_add_le _ _
          _ ≤ |c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2| + |c₁ * Real.log N| + |c₀| := by
              gcongr; exact abs_add_le _ _
          _ ≤ |c₃ * (Real.log N) ^ 3| + |c₂ * (Real.log N) ^ 2| + |c₁ * Real.log N| + |c₀| := by
              gcongr; exact abs_add_le _ _
          _ = |c₃| * (Real.log N) ^ 3 + |c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hℓ, abs_pow, abs_pow,
                abs_of_nonneg hℓ]
      rw [Real.norm_eq_abs, abs_mul]
      calc |c₃ * (Real.log N) ^ 3 + c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀| *
            |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x|
          ≤ (|c₃| * (Real.log N) ^ 3 + |c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀|) *
            ((j + 1) ^ j / 2 * (1 / Real.sqrt N)) :=
            mul_le_mul hc hI (abs_nonneg _) (by positivity)
        _ = (|c₃| * ((Real.log N) ^ 3 / Real.sqrt N) + |c₂| * ((Real.log N) ^ 2 / Real.sqrt N) +
            |c₁| * (Real.log N / Real.sqrt N) + |c₀| * (1 / Real.sqrt N)) *
              ((j + 1) ^ j / 2) := by ring
    · have := ((((hℓ3.const_mul |c₃|).add (hℓ2.const_mul |c₂|)).add (hℓ1.const_mul |c₁|)).add
        (hℓ0.const_mul |c₀|)).mul_const (((j : ℝ) + 1) ^ j / 2)
      simpa using this
  -- assemble
  have h0 := hpiece 0 (gaussCoeffA 0) (gaussCoeffB 0) (thirdCoeff 0) depthFourConst
  have h1 := hpiece 1 0 (6 * gaussCoeffA 0) (4 * gaussCoeffB 0) (2 * thirdCoeff 0)
  have h2 := hpiece 2 0 0 (12 * gaussCoeffA 0) (4 * gaussCoeffB 0)
  have h3 := hpiece 3 0 0 0 (8 * gaussCoeffA 0)
  simp only [pow_zero, pow_one, zero_mul, zero_add, mul_one] at h0 h1 h2 h3
  have hQ := tendsto_depthFiveQ_term
  have hsum := hQ.add (((((h0.neg.add h1.neg).add h2.neg).add (h3.neg.add
    (tendsto_const_nhds (x := 8 * gaussCoeffA 0 * gaussJlog3)))).add
    (tendsto_const_nhds (x := depthFourConst * gaussR₀ + 2 * thirdCoeff 0 * gaussJlog +
      4 * gaussCoeffB 0 * gaussJlog2))).const_mul (2 / Real.sqrt (2 * Real.pi)))
  have key : Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 5 N -
      gaussCoeffA 1 * (Real.log N) ^ 4 - gaussCoeffB 1 * (Real.log N) ^ 3 -
      thirdCoeff 1 * (Real.log N) ^ 2 - depthFiveLinCoeff * Real.log N) atTop
      (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFiveQint + 2 / Real.sqrt (2 * Real.pi) *
        (-0 + -0 + -0 + (-0 + 8 * gaussCoeffA 0 * gaussJlog3) +
          (depthFourConst * gaussR₀ + 2 * thirdCoeff 0 * gaussJlog +
            4 * gaussCoeffB 0 * gaussJlog2)))) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    rw [sqrt_mul_gaussLaplaceL_five_sub_eq hN]
    ring
  convert key using 2
  unfold depthFiveConst
  ring

end Grammar
