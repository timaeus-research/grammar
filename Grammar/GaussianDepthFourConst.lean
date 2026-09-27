/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthThreeRate
import Grammar.GaussianDepthAllThirdCoeff
import Grammar.DepthThreeMellinClosedForm

/-!
# The depth-four constant of the Gaussian DLN as an integral-defined limit

`√N Z₄(N) = A₄ℓ³ + B₄ℓ² + C₄ℓ + D₄ + o(1)` (★★★ `gaussLaplaceL_four_constant`), `ℓ = log N`, with

  `D₄ = depthFourConst = (2/s)[4A₃ J₂ + 2B₃ J + C₃ R₀ + Q₃]`,

`J₂ = ∫₀^∞ h(x) log²x/x dx` (`gaussJlog2`), `Q₃ = ∫₀^∞ q₃` with
`q₃(v) = Z₃(v²) − 1_{(1,∞)}(v) P₃(2 log v)/v`, `P₃(u) = A₃u² + B₃u + C₃` the depth-three jet
(`A₃ = 1/(4π)`, `B₃ = (2 log 2 − γ)/π`, `C₃ = depthThreeConst`).  Route (DCXXXI one order up, but
through the scalar recursion and the depth-three RATE instead of a bespoke decomposition):
`√N Z₄ = 2∫₀^∞ γ(v/√N) Z₃(v²) dv` (`sqrt_mul_gaussLaplaceL_four_eq`), the residual part
`2∫ γ(v/√N) q₃ → (2/s) Q₃` by dominated convergence (`|q₃| ≤ 1` on `(0,1]`,
`≤ 8(1 + 2 log v)/v²` beyond, from `gaussLaplaceL_three_rate`), and the tail
`2∫₁^∞ γ(v/√N) P₃(2 log v)/v`, back in `x = v/√N`, splits through `γ = (h + 1_{(0,1]})/s` into the
exact flat part `A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2` and the `h`-moments `R₀(a), J(a), J₂(a)` at the cutoff
`a = N^{−1/2}`, whose deviations from `R₀, J, J₂` are `O(N^{−1})`, `O(N^{−1/2})`, `O(N^{−1/2})`.
The coefficients agree with DCXXVI/DCXXXVI (`A₄ = gaussCoeffA 0`, `B₄ = gaussCoeffB 0`,
`C₄ = thirdCoeff 0`).  No rate is claimed (Astra round-15 target 3; examples_slop §2).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The depth-three jet and the residual `q₃` -/

/-- The depth-three jet `P₃(u) = A₃u² + B₃u + C₃`. -/
noncomputable def depthThreeJet (u : ℝ) : ℝ :=
  u ^ 2 / (4 * Real.pi) + (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * u +
    depthThreeConst

/-- `q₃(v) = Z₃(v²) − 1_{(1,∞)}(v) P₃(2 log v)/v`. -/
noncomputable def depthFourQ (v : ℝ) : ℝ :=
  gaussLaplaceL 3 (v ^ 2) - (Ioi (1 : ℝ)).indicator (fun v => depthThreeJet (2 * Real.log v) / v) v

theorem measurable_gaussLaplaceL_three_sq : Measurable fun v : ℝ => gaussLaplaceL 3 (v ^ 2) := by
  have e : (fun v : ℝ => gaussLaplaceL 3 (v ^ 2)) =
      fun v => ∫ x : ℝ, gaussDensity x * gaussLaplace2 (v ^ 2 * x ^ 2) := by
    funext v
    rw [gaussLaplaceL_succ_scalar 2 (sq_nonneg v)]
    simp only [gaussLaplaceL_two]
  rw [e]
  exact ((continuous_gaussDensity.measurable.comp measurable_snd).mul
    (measurable_gaussLaplace2.comp ((measurable_fst.pow_const 2).mul
      (measurable_snd.pow_const 2)))).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_depthFourQ : Measurable depthFourQ := by
  unfold depthFourQ
  refine measurable_gaussLaplaceL_three_sq.sub (Measurable.indicator ?_ measurableSet_Ioi)
  unfold depthThreeJet
  fun_prop

theorem depthFourQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthFourQ v = gaussLaplaceL 3 (v ^ 2) := by
  unfold depthFourQ
  rw [indicator_of_notMem (fun h : v ∈ Ioi (1 : ℝ) => absurd hv.2 (not_le.2 h)), sub_zero]

/-- On `(1,∞)`: `|q₃(v)| ≤ 8(1 + 2 log v)/v²` from the depth-three rate at `N = v²`. -/
theorem depthFourQ_outer_le {v : ℝ} (hv : 1 < v) :
    |depthFourQ v| ≤ 8 * (1 + 2 * Real.log v) / v ^ 2 := by
  have hv0 : 0 < v := by linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have h := gaussLaplaceL_three_rate hv2
  rw [Real.sqrt_sq hv0.le, Real.log_pow, Nat.cast_ofNat] at h
  unfold depthFourQ depthThreeJet
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  have e : gaussLaplaceL 3 (v ^ 2) - ((2 * Real.log v) ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (2 * Real.log v) +
        depthThreeConst) / v =
      (v * gaussLaplaceL 3 (v ^ 2) - ((2 * Real.log v) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (2 * Real.log v) +
          depthThreeConst)) / v := by
    field_simp
  rw [e, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
  calc |v * gaussLaplaceL 3 (v ^ 2) - ((2 * Real.log v) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (2 * Real.log v) +
          depthThreeConst)| ≤ 8 * (1 + 2 * Real.log v) / v := h
    _ = 8 * (1 + 2 * Real.log v) / v ^ 2 * v := by field_simp

theorem integrableOn_depthFourQ_inner : IntegrableOn depthFourQ (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    measurable_depthFourQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  rw [depthFourQ_inner hv, Real.norm_eq_abs, abs_of_nonneg (gaussLaplaceL_nonneg 3 _)]
  exact gaussLaplaceL_le_one 3 (sq_nonneg _)

theorem integrableOn_depthFourQ_outer : IntegrableOn depthFourQ (Ioi 1) := by
  have h : IntegrableOn (fun v : ℝ => 8 * v ^ (-2 : ℝ) + 16 * (v ^ (-2 : ℝ) * Real.log v))
      (Ioi 1) := by
    have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul 8
    have h2 := (integrableOn_Ioi_one_rpow_mul_log (z := 0) (by norm_num)).const_mul 16
    refine IntegrableOn.congr_fun (h1.add h2) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, zero_sub]
  refine h.mono' measurable_depthFourQ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  rw [Real.norm_eq_abs]
  refine (depthFourQ_outer_le hv1).trans (le_of_eq ?_)
  rw [Real.rpow_neg hv0.le, Real.rpow_two]
  field_simp
  ring

theorem integrableOn_depthFourQ : IntegrableOn depthFourQ (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact integrableOn_depthFourQ_inner.union integrableOn_depthFourQ_outer

/-! ### The constants -/

/-- `J₂ = ∫₀^∞ h(x) log²x/x dx`. -/
noncomputable def gaussJlog2 : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x

/-- `Q₃ = ∫₀^∞ q₃`. -/
noncomputable def depthFourQint : ℝ := ∫ v in Ioi (0 : ℝ), depthFourQ v

/-- The depth-four constant `D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]`. -/
noncomputable def depthFourConst : ℝ :=
  2 / Real.sqrt (2 * Real.pi) * (4 * (1 / (4 * Real.pi)) * gaussJlog2 +
    2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussJlog +
    depthThreeConst * gaussR₀ + depthFourQint)

/-! ### `√N Z₄ = 2∫₀^∞ γ(v/√N) Z₃(v²) dv` -/

theorem integrable_gaussDensity_mul_gaussLaplaceL_three {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)) := by
  have hm : Measurable fun x : ℝ => gaussLaplaceL 3 (N * x ^ 2) := by
    have e : (fun x : ℝ => gaussLaplaceL 3 (N * x ^ 2)) =
        fun x => gaussLaplaceL 3 ((Real.sqrt N * x) ^ 2) := by
      funext x; rw [mul_pow, Real.sq_sqrt hN]
    rw [e]
    exact measurable_gaussLaplaceL_three_sq.comp (measurable_const.mul measurable_id)
  refine integrable_gaussDensity.mono'
    (continuous_gaussDensity.measurable.mul hm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg x),
    abs_of_nonneg (gaussLaplaceL_nonneg 3 _)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg x) (gaussLaplaceL_le_one 3 (by positivity))

/-- `√N Z₄(N) = 2 ∫₀^∞ γ(v/√N) Z₃(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_four_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 4 N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 3 (v ^ 2) := by
  rw [gaussLaplaceL_succ_scalar 3 hN.le]
  have h := integral_comp_abs (f := fun x : ℝ => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2))
  simp only [gaussDensity_abs, sq_abs] at h
  rw [h]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h2 := integral_comp_mul_left_Ioi
    (fun x => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)) 0 hb
  rw [mul_zero, smul_eq_mul, inv_div, div_one] at h2
  calc Real.sqrt N * (2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2))
      = 2 * (Real.sqrt N * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)) := by
        ring
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (1 / Real.sqrt N * v) *
          gaussLaplaceL 3 (N * (1 / Real.sqrt N * v) ^ 2) := by rw [h2]
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 3 (v ^ 2) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
          mul_div_cancel₀ _ hN.ne']

/-! ### The residual term `2∫ γ(v/√N) q₃ → (2/s) Q₃` -/

theorem gaussDensity_le_inv_sqrt (x : ℝ) : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold gaussDensity
  exact div_le_div_of_nonneg_right
    (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) (Real.sqrt_nonneg _)

theorem tendsto_depthFourQ_term :
    Tendsto (fun N : ℝ => 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v)
      atTop (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFourQint)) := by
  unfold depthFourQint
  have e : 2 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (0 : ℝ), depthFourQ v =
      2 * ∫ v in Ioi (0 : ℝ), 1 / Real.sqrt (2 * Real.pi) * depthFourQ v := by
    rw [integral_const_mul]; ring
  rw [e]
  refine Tendsto.const_mul 2 ?_
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun N v => gaussDensity (v / Real.sqrt N) * depthFourQ v)
    (f := fun v => 1 / Real.sqrt (2 * Real.pi) * depthFourQ v)
    (fun v => 1 / Real.sqrt (2 * Real.pi) * |depthFourQ v|)
    (Eventually.of_forall fun N => (continuous_gaussDensity.comp (continuous_id.div_const _)
      |>.measurable.mul measurable_depthFourQ).aestronglyMeasurable)
    (Eventually.of_forall fun N => ?_)
    (integrableOn_depthFourQ.abs.const_mul _)
    (Eventually.of_forall fun v => ?_)
  · refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
    exact mul_le_mul_of_nonneg_right (gaussDensity_le_inv_sqrt _) (abs_nonneg _)
  · have h1 : Tendsto (fun N : ℝ => v / Real.sqrt N) atTop (𝓝 0) := by
      have := tendsto_one_div_sqrt.const_mul v
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have := ((continuous_gaussDensity.tendsto 0).comp h1).mul_const (depthFourQ v)
    rw [gaussDensity_zero] at this
    exact this

/-! ### The tail `2∫ γ(v/√N) 1_{v>1} P₃(2 log v)/v` in the variable `x = v/√N` -/

/-- The tail integrand. -/
noncomputable def depthFourTail (v : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun v => depthThreeJet (2 * Real.log v) / v) v

theorem depthFourQ_add_tail (v : ℝ) : depthFourQ v + depthFourTail v = gaussLaplaceL 3 (v ^ 2) := by
  unfold depthFourQ depthFourTail; ring

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL 3 (v ^ 2))
      (Ioi 0) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2)) 0 hb).2
    (by rw [mul_zero]; exact (integrable_gaussDensity_mul_gaussLaplaceL_three hN.le).integrableOn)
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp only
  rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
    mul_div_cancel₀ _ hN.ne']

theorem integrableOn_gaussDensity_div_mul_depthFourQ {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFourQ v) (Ioi 0) := by
  refine (integrableOn_depthFourQ.abs.const_mul (1 / Real.sqrt (2 * Real.pi))).mono'
    ((continuous_gaussDensity.comp (continuous_id.div_const _)).measurable.mul
      measurable_depthFourQ).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg _)]
  exact mul_le_mul_of_nonneg_right (gaussDensity_le_inv_sqrt _) (abs_nonneg _)

/-- `√N Z₄ = 2∫ γ(v/√N) q₃ + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_four_split {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 4 N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourTail v := by
  rw [sqrt_mul_gaussLaplaceL_four_eq hN, ← mul_add]
  congr 1
  have hT : IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFourTail v) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_gaussDensity_div_mul_gaussLaplaceL hN).sub
      (integrableOn_gaussDensity_div_mul_depthFourQ (N := N))) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [← depthFourQ_add_tail]
    ring
  rw [← integral_add (integrableOn_gaussDensity_div_mul_depthFourQ (N := N)) hT]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [← depthFourQ_add_tail]
  ring

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P₃(ℓ + 2 log x)/x dx`,
`a = N^{−1/2}`, `ℓ = log N`. -/
theorem tail_integral_eq {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourTail v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  -- `v = √N x`
  have h := integral_comp_mul_left_Ioi
    (fun v => gaussDensity (v / Real.sqrt N) * depthFourTail v) 0 hsN
  rw [mul_zero, smul_eq_mul] at h
  have h' : ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourTail v =
      Real.sqrt N * ∫ x in Ioi (0 : ℝ),
        gaussDensity (Real.sqrt N * x / Real.sqrt N) * depthFourTail (Real.sqrt N * x) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hsN.ne', one_mul]
  rw [h', ← integral_const_mul]
  have e : ∀ x ∈ Ioi (0 : ℝ), Real.sqrt N *
      (gaussDensity (Real.sqrt N * x / Real.sqrt N) * depthFourTail (Real.sqrt N * x)) =
      (Ioi (1 / Real.sqrt N)).indicator
        (fun x => gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [mul_div_cancel_left₀ _ hsN.ne']
    unfold depthFourTail
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
        show (1 : ℝ) / Real.sqrt N < x
        rwa [div_lt_iff₀ hsN, mul_comm]
      rw [indicator_of_notMem hm, indicator_of_notMem hm1, mul_zero, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi (1 / Real.sqrt N) = Ioi (1 / Real.sqrt N) from
      inter_eq_right.2 fun x (hx : 1 / Real.sqrt N < x) =>
        (show (0 : ℝ) < x from lt_trans (by positivity) hx)]

/-! ### `γ = (h + 1_{(0,1]})/s`: the flat part and the `h`-part -/

theorem gaussDensity_eq_gaussH (x : ℝ) :
    gaussDensity x = (gaussH x + (Ioc (0 : ℝ) 1).indicator 1 x) / Real.sqrt (2 * Real.pi) := by
  unfold gaussDensity gaussH; ring

/-- The jet evaluated at `ℓ + 2 log x`, as a polynomial in `log x`. -/
theorem depthThreeJet_shift (ℓ y : ℝ) :
    depthThreeJet (ℓ + 2 * y) = (ℓ ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * ℓ + depthThreeConst) +
      (4 * ℓ / (4 * Real.pi) + 2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) * y +
      4 * (1 / (4 * Real.pi)) * y ^ 2 := by
  unfold depthThreeJet; ring

theorem integrableOn_gaussH_jet {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N)) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have h0 := integrableOn_gaussH_log_pow 0 ha0 ha1
  have h1 := integrableOn_gaussH_log_pow 1 ha0 ha1
  have h2 := integrableOn_gaussH_log_pow 2 ha0 ha1
  have h012 : IntegrableOn (fun x : ℝ =>
      ((Real.log N) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst) *
        (gaussH x * Real.log x ^ 0 / x) +
      (4 * Real.log N / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
        (gaussH x * Real.log x ^ 1 / x) +
      4 * (1 / (4 * Real.pi)) * (gaussH x * Real.log x ^ 2 / x)) (Ioi (1 / Real.sqrt N)) :=
    ((h0.const_mul _).add (h1.const_mul _)).add (h2.const_mul _)
  refine IntegrableOn.congr_fun h012 (fun x _ => ?_) measurableSet_Ioi
  simp only [pow_zero, pow_one]
  rw [depthThreeJet_shift]
  ring

theorem integrableOn_jet_div_Ioc {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => depthThreeJet (Real.log N + 2 * Real.log x) / x)
      (Ioc (1 / Real.sqrt N) 1) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (ContinuousOn.comp (by unfold depthThreeJet; fun_prop : Continuous depthThreeJet).continuousOn
    (continuousOn_const.add (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ?_)))
    (mapsTo_univ _ _)) continuousOn_id fun x hx => ?_
  · rw [uIcc_of_le ha1] at hx
    exact mem_compl_singleton_iff.2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))
  · rw [uIcc_of_le ha1] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)

/-- The tail splits into the flat part and the `h`-part. -/
theorem tail_integral_split {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeJet (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have hind : IntegrableOn (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator
      (fun x => depthThreeJet (Real.log N + 2 * Real.log x) / x) x) (Ioi (1 / Real.sqrt N)) := by
    have := (integrableOn_jet_div_Ioc hN).integrable_indicator measurableSet_Ioc
    refine this.integrableOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : 1 / Real.sqrt N < x := hx
    by_cases hm : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc (1 / Real.sqrt N) 1 from ⟨hx', hm⟩),
        indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨lt_trans ha0 hx', hm⟩)]
    · rw [indicator_of_notMem (fun h : x ∈ Ioc (1 / Real.sqrt N) 1 => hm h.2),
        indicator_of_notMem (fun h : x ∈ Ioc (0 : ℝ) 1 => hm h.2)]
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N),
      gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) * ((Ioc (0 : ℝ) 1).indicator
        (fun x => depthThreeJet (Real.log N + 2 * Real.log x) / x) x +
        gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x) := by
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
    integral_add hind (integrableOn_gaussH_jet hN), setIntegral_indicator measurableSet_Ioc,
    show Ioi (1 / Real.sqrt N) ∩ Ioc 0 1 = Ioc (1 / Real.sqrt N) 1 from by
      ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, lt_trans ha0 h1, h3⟩]

/-- The flat part exactly: `∫_a^1 P₃(ℓ + 2 log x)/x = A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2`. -/
theorem flat_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeJet (Real.log N + 2 * Real.log x) / x =
      1 / (4 * Real.pi) * (Real.log N) ^ 3 / 6 +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (Real.log N) ^ 2 / 4 +
        depthThreeConst * Real.log N / 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  set ℓ := Real.log N with hℓ
  set G : ℝ → ℝ := fun x => 1 / (4 * Real.pi) * (ℓ + 2 * Real.log x) ^ 3 / 6 +
    (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (ℓ + 2 * Real.log x) ^ 2 / 4 +
    depthThreeConst * (ℓ + 2 * Real.log x) / 2 with hG
  have hderiv : ∀ x ∈ uIcc (1 / Real.sqrt N) 1,
      HasDerivAt G (depthThreeJet (ℓ + 2 * Real.log x) / x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hl : HasDerivAt (fun x : ℝ => ℓ + 2 * Real.log x) (2 * x⁻¹) x :=
      ((Real.hasDerivAt_log hx0.ne').const_mul 2).const_add ℓ
    have h3 : HasDerivAt (fun x : ℝ => 1 / (4 * Real.pi) * (ℓ + 2 * Real.log x) ^ 3 / 6)
        (1 / (4 * Real.pi) * (((3 : ℕ) : ℝ) * (ℓ + 2 * Real.log x) ^ (3 - 1) * (2 * x⁻¹)) / 6) x :=
      ((hl.pow 3).const_mul _).div_const _
    have h2 : HasDerivAt (fun x : ℝ =>
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (ℓ + 2 * Real.log x) ^ 2 / 4)
        ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi *
          (((2 : ℕ) : ℝ) * (ℓ + 2 * Real.log x) ^ (2 - 1) * (2 * x⁻¹)) / 4) x :=
      ((hl.pow 2).const_mul _).div_const _
    have h1 : HasDerivAt (fun x : ℝ => depthThreeConst * (ℓ + 2 * Real.log x) / 2)
        (depthThreeConst * (2 * x⁻¹) / 2) x := (hl.const_mul _).div_const _
    have := (h3.add h2).add h1
    refine this.congr_deriv ?_
    unfold depthThreeJet
    norm_num
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => depthThreeJet (ℓ + 2 * Real.log x) / x) volume
      (1 / Real.sqrt N) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact integrableOn_jet_div_Ioc hN
  rw [← intervalIntegral.integral_of_le ha1,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog : ℓ + 2 * Real.log (1 / Real.sqrt N) = 0 := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le, hℓ]; ring
  simp only [hG, Real.log_one, mul_zero, add_zero, hlog]
  ring

/-- The cutoff `h`-moments `R(a) = ∫_a^∞ h/x`, `J(a) = ∫_a^∞ h log x/x`, `J₂(a) = ∫_a^∞ h log²x/x`. -/
theorem hpart_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      ((Real.log N) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x / x) +
      (4 * Real.log N / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) +
      4 * (1 / (4 * Real.pi)) * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have h0 := integrableOn_gaussH_log_pow 0 ha0 ha1
  have h1 := integrableOn_gaussH_log_pow 1 ha0 ha1
  have h2 := integrableOn_gaussH_log_pow 2 ha0 ha1
  simp only [pow_zero, pow_one] at h0 h1
  have h01 : Integrable (fun x : ℝ => ((Real.log N) ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst) *
        (gaussH x * 1 / x) + (4 * Real.log N / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
        (gaussH x * Real.log x / x)) (volume.restrict (Ioi (1 / Real.sqrt N))) :=
    (h0.const_mul _).add (h1.const_mul _)
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N),
      gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      (((Real.log N) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst) *
        (gaussH x * 1 / x) + (4 * Real.log N / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
        (gaussH x * Real.log x / x)) +
        4 * (1 / (4 * Real.pi)) * (gaussH x * Real.log x ^ 2 / x) := by
    intro x _
    rw [depthThreeJet_shift]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add h01 (h2.const_mul _),
    integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  simp only [mul_one]

/-! ### The cutoff `h`-moments and their limits -/

/-- `∫_a^∞ h log^j x/x = ∫₀^∞ h log^j x/x − ∫₀^a h log^j x/x`. -/
theorem gaussH_log_pow_cutoff (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ x in Ioi a, gaussH x * Real.log x ^ j / x =
      (∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ j / x) -
        ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x := by
  rw [← Ioc_union_Ioi_eq_Ioi ha0, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    ((integrableOn_gaussH_log_pow_Ioc j le_rfl).mono_set (Ioc_subset_Ioc_right ha1))
    (integrableOn_gaussH_log_pow j ha0 ha1)]
  ring

/-- `|∫₀^a h log^j x/x| ≤ (j+1)^j a/2` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_log_pow_Ioc_le (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤ (j + 1) ^ j / 2 * a := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussH x * Real.log x ^ j / x) (C := (j + 1) ^ j / 2) measure_Ioc_lt_top
    (fun x hx => by
      have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans ha1⟩
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hx.1]
      exact gaussH_log_pow_inner j hx')
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha0]

theorem tendsto_log_div_sqrt : Tendsto (fun N : ℝ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [Real.sqrt_eq_rpow]

theorem tendsto_sq_log_div_sqrt :
    Tendsto (fun N : ℝ => (Real.log N) ^ 2 / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have h2 := h.pow 2
  simp only [zero_pow two_ne_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (N ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hN.le]
  norm_num

/-- The assembled remainder: for `N ≥ 1`,
`√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ = 2∫γ(v/√N)q₃ + (2/s)[c₀ε₀ + c₁ε₁ + c₂(J₂ − ε₂) + C₃R₀ + 2B₃J]`. -/
theorem sqrt_mul_gaussLaplaceL_four_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
      gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) +
      2 / Real.sqrt (2 * Real.pi) *
        (((Real.log N) ^ 2 / (4 * Real.pi) +
          (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N +
            depthThreeConst) * (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        (4 * Real.log N / (4 * Real.pi) +
          2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        4 * (1 / (4 * Real.pi)) *
          (gaussJlog2 - ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
        depthThreeConst * gaussR₀ +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussJlog) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [sqrt_mul_gaussLaplaceL_four_split hN0, tail_integral_eq hN0, tail_integral_split hN,
    flat_integral_eq hN, hpart_integral_eq hN, integral_gaussH_div_Ioi ha0]
  have hJ := gaussH_log_pow_cutoff 1 ha0 ha1
  have hJ2 := gaussH_log_pow_cutoff 2 ha0 ha1
  simp only [pow_one] at hJ
  rw [hJ, hJ2]
  unfold thirdCoeff gaussCoeffA gaussCoeffB
  unfold gaussJlog gaussJlog2 gaussR₀
  simp only [Nat.factorial, Nat.cast_zero, zero_add]
  set Q := ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v with hQ
  set E0 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hE0
  set J := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x with hJd
  set E1 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x with hE1
  set J2 := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x with hJ2d
  set E2 := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x with hE2
  set C := depthThreeConst with hC
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  clear_value Q E0 J E1 J2 E2 C S
  rw [hpi]
  field_simp
  ring

/-- ★★★ **The depth-four constant**: `√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ → D₄`. -/
theorem gaussLaplaceL_four_constant :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
      gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N) atTop (𝓝 depthFourConst) := by
  -- the three cutoff pieces tend to zero
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hℓ2 := tendsto_sq_log_div_sqrt
  have hℓ1 := tendsto_log_div_sqrt
  have hℓ0 := tendsto_one_div_sqrt
  set B₃ := (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi with hB₃
  set C₃ := depthThreeConst with hC₃
  have hpiece : ∀ (j : ℕ) (c₂ c₁ c₀ : ℝ),
      Tendsto (fun N : ℝ => (c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀) *
        ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x) atTop (𝓝 0) := by
    intro j c₂ c₁ c₀
    refine squeeze_zero_norm' ?_ (a := fun N : ℝ => (|c₂| * ((Real.log N) ^ 2 / Real.sqrt N) +
      |c₁| * (Real.log N / Real.sqrt N) + |c₀| * (1 / Real.sqrt N)) * ((j + 1) ^ j / 2)) ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
      have hN0 : 0 < N := by linarith
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
      have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
      have hI := abs_integral_gaussH_log_pow_Ioc_le j ha0 ha1
      have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
      have hc : |c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀| ≤
          |c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀| := by
        calc |c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀|
            ≤ |c₂ * (Real.log N) ^ 2 + c₁ * Real.log N| + |c₀| := abs_add_le _ _
          _ ≤ |c₂ * (Real.log N) ^ 2| + |c₁ * Real.log N| + |c₀| := by
              gcongr; exact abs_add_le _ _
          _ = |c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hℓ, abs_pow, abs_of_nonneg hℓ]
      rw [Real.norm_eq_abs, abs_mul]
      calc |c₂ * (Real.log N) ^ 2 + c₁ * Real.log N + c₀| *
            |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x|
          ≤ (|c₂| * (Real.log N) ^ 2 + |c₁| * Real.log N + |c₀|) *
            ((j + 1) ^ j / 2 * (1 / Real.sqrt N)) :=
            mul_le_mul hc hI (abs_nonneg _) (by positivity)
        _ = (|c₂| * ((Real.log N) ^ 2 / Real.sqrt N) + |c₁| * (Real.log N / Real.sqrt N) +
            |c₀| * (1 / Real.sqrt N)) * ((j + 1) ^ j / 2) := by ring
    · have := (((hℓ2.const_mul |c₂|).add (hℓ1.const_mul |c₁|)).add (hℓ0.const_mul |c₀|)).mul_const
        (((j : ℝ) + 1) ^ j / 2)
      simpa using this
  -- assemble
  have h0 := hpiece 0 (1 / (4 * Real.pi)) B₃ C₃
  have h1 := hpiece 1 0 (4 / (4 * Real.pi)) (2 * B₃)
  have h2 := hpiece 2 0 0 (4 * (1 / (4 * Real.pi)))
  simp only [pow_zero, pow_one, zero_mul, zero_add, mul_one] at h0 h1 h2
  have hQ := tendsto_depthFourQ_term
  have hsum := hQ.add ((((h0.neg.add h1.neg).add (h2.neg.add
    (tendsto_const_nhds (x := 4 * (1 / (4 * Real.pi)) * gaussJlog2)))).add
    (tendsto_const_nhds (x := C₃ * gaussR₀ + 2 * B₃ * gaussJlog))).const_mul
    (2 / Real.sqrt (2 * Real.pi)))
  have key : Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 4 N -
      gaussCoeffA 0 * (Real.log N) ^ 3 - gaussCoeffB 0 * (Real.log N) ^ 2 -
      thirdCoeff 0 * Real.log N) atTop
      (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFourQint + 2 / Real.sqrt (2 * Real.pi) *
        (-0 + -0 + (-0 + 4 * (1 / (4 * Real.pi)) * gaussJlog2) +
          (C₃ * gaussR₀ + 2 * B₃ * gaussJlog)))) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    rw [sqrt_mul_gaussLaplaceL_four_sub_eq hN]
    simp only [hB₃, hC₃]
    ring
  convert key using 2
  unfold depthFourConst
  simp only [hB₃, hC₃]
  ring

end Grammar
