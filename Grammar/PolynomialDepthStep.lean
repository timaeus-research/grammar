/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolynomialJetTools

/-!
# The all-depth engine: the depth step with the linear-log rate

`HasPolyRate L P` says `|√N Z_L(N) − P(log N)| ≤ K(1 + log N)/√N` for `N ≥ 1`
(★★★ `HasPolyRate.step`): if it holds at depth `L` for `P : Polynomial ℝ` then it holds at depth
`L + 1` for
`stepPoly P Q = (1/s) primZero P + (2/s) Σ_{j ≤ deg P} 2^j J_j H_j P + 2Q/s`,
`J_j = ∫₀^∞ h log^j x/x` (`gaussJlogPow`), `H_j = hasseDeriv j`, `Q = ∫₀^∞ q_L` the mass of the
residual `q_L(v) = Z_L(v²) − 1_{v>1} P(2 log v)/v` (`polyResidual`, `residualMass`).  The proof is
DCLVIII's with `depthFourJet` replaced by `P.eval`: the scalar recursion
`√N Z_{L+1} = 2∫₀^∞ γ(v/√N) Z_L(v²) dv`, the residual bound of DCLVII (from the rate at `N = v²`),
the tail substituted and split by `γ = (h + 1_{(0,1]})/s`, the flat part by `primZero` (DCLXII), the
`h`-part by Taylor with Hasse derivatives, the cutoff moments `(2j)^j/3 · N^{−3/4}` (DCLVII) and
the absorption `(1 + ℓ)^d N^{−3/4} ≤ C(1 + ℓ)/√N` (DCLXII).  No hypothesis on `deg P`; the
exponent `m = 1` is the invariant.  Astra rounds 18–19.  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

/-! ### Measurability of the depth functions -/

theorem measurable_gaussLaplaceL (L : ℕ) : Measurable (gaussLaplaceL L) := by
  unfold gaussLaplaceL
  have hc : Continuous fun p : ℝ × (Fin L → ℝ) =>
      Real.exp (-p.1 * (∏ i, p.2 i) ^ 2 / 2) * ∏ i, gaussDensity (p.2 i) := by
    refine (Real.continuous_exp.comp ?_).mul
      (continuous_finsetProd _ fun i _ => continuous_gaussDensity.comp
        ((continuous_apply i).comp continuous_snd))
    exact ((continuous_fst.neg.mul
      (((continuous_prod_coord L).comp continuous_snd).pow 2)).div_const 2)
  exact hc.measurable.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_gaussLaplaceL_sq (L : ℕ) : Measurable fun v : ℝ => gaussLaplaceL L (v ^ 2) :=
  (measurable_gaussLaplaceL L).comp (measurable_id.pow_const 2)

/-! ### The residual, the rate predicate and the step polynomial -/

/-- `q_L(v) = Z_L(v²) − 1_{(1,∞)}(v) P(2 log v)/v`. -/
noncomputable def polyResidual (L : ℕ) (P : ℝ[X]) (v : ℝ) : ℝ :=
  gaussLaplaceL L (v ^ 2) - (Ioi (1 : ℝ)).indicator (fun v => P.eval (2 * Real.log v) / v) v

/-- `Q_L = ∫₀^∞ q_L`. -/
noncomputable def residualMass (L : ℕ) (P : ℝ[X]) : ℝ := ∫ v in Ioi (0 : ℝ), polyResidual L P v

/-- The linear-log rate at depth `L` with polynomial `P`. -/
def HasPolyRate (L : ℕ) (P : ℝ[X]) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
    |Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N)| ≤ K * (1 + Real.log N) / Real.sqrt N

/-- The log moments `J_j = ∫₀^∞ h(x) log^j x/x dx`. -/
noncomputable def gaussJlogPow (j : ℕ) : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ j / x

/-- The step `P ↦ (1/s) primZero P + (2/s) Σ_j 2^j J_j H_j P + 2Q/s`. -/
noncomputable def stepPoly (P : ℝ[X]) (Q : ℝ) : ℝ[X] :=
  C (1 / Real.sqrt (2 * Real.pi)) * primZero P +
    C (2 / Real.sqrt (2 * Real.pi)) *
      ∑ j ∈ range (P.natDegree + 1), C (2 ^ j * gaussJlogPow j) * hasseDeriv j P +
    C (2 * Q / Real.sqrt (2 * Real.pi))

theorem eval_stepPoly (P : ℝ[X]) (Q ℓ : ℝ) :
    (stepPoly P Q).eval ℓ = 1 / Real.sqrt (2 * Real.pi) * (primZero P).eval ℓ +
      2 / Real.sqrt (2 * Real.pi) *
        ∑ j ∈ range (P.natDegree + 1), 2 ^ j * gaussJlogPow j * (hasseDeriv j P).eval ℓ +
      2 * Q / Real.sqrt (2 * Real.pi) := by
  simp only [stepPoly, eval_add, eval_mul, eval_C, eval_finsetSum]

theorem measurable_polyResidual (L : ℕ) (P : ℝ[X]) : Measurable (polyResidual L P) := by
  unfold polyResidual
  refine (measurable_gaussLaplaceL_sq L).sub (Measurable.indicator ?_ measurableSet_Ioi)
  exact (P.continuous.measurable.comp (measurable_const.mul Real.measurable_log)).div
    measurable_id

theorem polyResidual_inner (L : ℕ) (P : ℝ[X]) {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    polyResidual L P v = gaussLaplaceL L (v ^ 2) := by
  unfold polyResidual
  rw [indicator_of_notMem (fun h : v ∈ Ioi (1 : ℝ) => absurd hv.2 (not_le.2 h)), sub_zero]

theorem abs_polyResidual_inner_le (L : ℕ) (P : ℝ[X]) {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    |polyResidual L P v| ≤ 1 := by
  rw [polyResidual_inner L P hv, abs_of_nonneg (gaussLaplaceL_nonneg L _)]
  exact gaussLaplaceL_le_one L (sq_nonneg _)

/-- The rate at `N = v²` bounds the residual: `|q_L(v)| ≤ K(1 + 2 log v)/v²` on `(1,∞)`. -/
theorem polyResidual_outer_le {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 1 < v →
      |polyResidual L P v| ≤ K * (1 + 2 * Real.log v) / v ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := h
  refine ⟨K, hK0, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have h := hK (v ^ 2) hv2
  rw [Real.sqrt_sq hv0.le, Real.log_pow, Nat.cast_ofNat] at h
  unfold polyResidual
  rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv)]
  have e : gaussLaplaceL L (v ^ 2) - P.eval (2 * Real.log v) / v =
      (v * gaussLaplaceL L (v ^ 2) - P.eval (2 * Real.log v)) / v := by
    field_simp
  rw [e, abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
  calc |v * gaussLaplaceL L (v ^ 2) - P.eval (2 * Real.log v)|
      ≤ K * (1 + 2 * Real.log v) / v := h
    _ = K * (1 + 2 * Real.log v) / v ^ 2 * v := by field_simp

theorem integrableOn_polyResidual {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    IntegrableOn (polyResidual L P) (Ioi 0) := by
  obtain ⟨K, -, hK⟩ := polyResidual_outer_le h
  exact integrableOn_of_le_one_add_two_log (measurable_polyResidual L P)
    (fun v hv => abs_polyResidual_inner_le L P hv) hK

/-! ### The scalar recursion -/

theorem integrable_gaussDensity_mul_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL L (N * x ^ 2)) := by
  have hm : Measurable fun x : ℝ => gaussLaplaceL L (N * x ^ 2) :=
    (measurable_gaussLaplaceL L).comp (measurable_const.mul (measurable_id.pow_const 2))
  refine integrable_gaussDensity.mono'
    (continuous_gaussDensity.measurable.mul hm).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg x),
    abs_of_nonneg (gaussLaplaceL_nonneg L _)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg x) (gaussLaplaceL_le_one L (by positivity))

/-- `√N Z_{L+1}(N) = 2 ∫₀^∞ γ(v/√N) Z_L(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_succ_eq (L : ℕ) {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL L (v ^ 2) := by
  rw [gaussLaplaceL_succ_scalar L hN.le]
  have h := integral_comp_abs (f := fun x : ℝ => gaussDensity x * gaussLaplaceL L (N * x ^ 2))
  simp only [gaussDensity_abs, sq_abs] at h
  rw [h]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h2 := integral_comp_mul_left_Ioi
    (fun x => gaussDensity x * gaussLaplaceL L (N * x ^ 2)) 0 hb
  rw [mul_zero, smul_eq_mul, inv_div, div_one] at h2
  calc Real.sqrt N * (2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL L (N * x ^ 2))
      = 2 * (Real.sqrt N * ∫ x in Ioi (0 : ℝ), gaussDensity x * gaussLaplaceL L (N * x ^ 2)) := by
        ring
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (1 / Real.sqrt N * v) *
          gaussLaplaceL L (N * (1 / Real.sqrt N * v) ^ 2) := by rw [h2]
    _ = 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL L (v ^ 2) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
          mul_div_cancel₀ _ hN.ne']

/-- The tail integrand `1_{v>1} P(2 log v)/v`. -/
noncomputable def polyTail (P : ℝ[X]) (v : ℝ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun v => P.eval (2 * Real.log v) / v) v

theorem polyResidual_add_tail (L : ℕ) (P : ℝ[X]) (v : ℝ) :
    polyResidual L P v + polyTail P v = gaussLaplaceL L (v ^ 2) := by
  unfold polyResidual polyTail; ring

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL_sq (L : ℕ) {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL L (v ^ 2))
      (Ioi 0) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hb : 0 < 1 / Real.sqrt N := by positivity
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => gaussDensity x * gaussLaplaceL L (N * x ^ 2)) 0 hb).2
    (by rw [mul_zero]; exact (integrable_gaussDensity_mul_gaussLaplaceL L hN.le).integrableOn)
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  simp only
  rw [show 1 / Real.sqrt N * v = v / Real.sqrt N by ring, div_pow, Real.sq_sqrt hN.le,
    mul_div_cancel₀ _ hN.ne']

/-- `√N Z_{L+1} = 2∫ γ(v/√N) q_L + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_succ_split {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) {N : ℝ}
    (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyTail P v := by
  have hq := integrableOn_gaussDensity_div_mul_of_integrableOn (measurable_polyResidual L P)
    (integrableOn_polyResidual h) (N := N)
  rw [sqrt_mul_gaussLaplaceL_succ_eq L hN, ← mul_add]
  congr 1
  have hT : IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * polyTail P v)
      (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_gaussDensity_div_mul_gaussLaplaceL_sq L hN).sub
      hq) (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [← polyResidual_add_tail L P]
    ring
  rw [← integral_add hq hT]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [← polyResidual_add_tail L P]
  ring

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P(ℓ + 2 log x)/x dx`. -/
theorem polyTail_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyTail P v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have h := integral_comp_mul_left_Ioi
    (fun v => gaussDensity (v / Real.sqrt N) * polyTail P v) 0 hsN
  rw [mul_zero, smul_eq_mul] at h
  have h' : ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyTail P v =
      Real.sqrt N * ∫ x in Ioi (0 : ℝ),
        gaussDensity (Real.sqrt N * x / Real.sqrt N) * polyTail P (Real.sqrt N * x) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hsN.ne', one_mul]
  rw [h', ← integral_const_mul]
  have e : ∀ x ∈ Ioi (0 : ℝ), Real.sqrt N *
      (gaussDensity (Real.sqrt N * x / Real.sqrt N) * polyTail P (Real.sqrt N * x)) =
      (Ioi (1 / Real.sqrt N)).indicator
        (fun x => gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [mul_div_cancel_left₀ _ hsN.ne']
    unfold polyTail
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

/-! ### The `h`-part as a sum of log moments -/

/-- `h(x) P(ℓ + 2 log x)/x = Σ_j (H_jP)(ℓ) 2^j (h(x) log^j x/x)`. -/
theorem gaussH_eval_log_eq_sum (P : ℝ[X]) (ℓ x : ℝ) :
    gaussH x * P.eval (ℓ + 2 * Real.log x) / x =
      ∑ j ∈ range (P.natDegree + 1),
        (hasseDeriv j P).eval ℓ * 2 ^ j * (gaussH x * Real.log x ^ j / x) := by
  rw [eval_add_eq_sum_hasseDeriv, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]; ring

theorem integrableOn_gaussH_eval_log (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * P.eval (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N)) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hsum : IntegrableOn (fun x : ℝ => ∑ j ∈ range (P.natDegree + 1),
      (hasseDeriv j P).eval (Real.log N) * 2 ^ j * (gaussH x * Real.log x ^ j / x))
      (Ioi (1 / Real.sqrt N)) :=
    integrable_finsetSum _ fun j _ => (integrableOn_gaussH_log_pow j ha0 ha1).const_mul _
  exact hsum.congr_fun (fun x _ => (gaussH_eval_log_eq_sum P (Real.log N) x).symm)
    measurableSet_Ioi

/-- The `h`-part: `∫_a^∞ h P(ℓ + 2 log x)/x = Σ_j (H_jP)(ℓ) 2^j ∫_a^∞ h log^j x/x`. -/
theorem poly_hpart_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * P.eval (Real.log N + 2 * Real.log x) / x =
      ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
        ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x _ => gaussH_eval_log_eq_sum P (Real.log N) x),
    integral_finsetSum _ fun j _ => (integrableOn_gaussH_log_pow j ha0 ha1).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-! ### The tail split and the flat part -/

theorem polyTail_integral_split (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, P.eval (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * P.eval (Real.log N + 2 * Real.log x) / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hind : IntegrableOn (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator
      (fun x => P.eval (Real.log N + 2 * Real.log x) / x) x) (Ioi (1 / Real.sqrt N)) := by
    have := (integrableOn_eval_log_div P (Real.log N) ha0 ha1).integrable_indicator
      measurableSet_Ioc
    refine this.integrableOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : 1 / Real.sqrt N < x := hx
    by_cases hm : x ≤ 1
    · rw [indicator_of_mem (show x ∈ Ioc (1 / Real.sqrt N) 1 from ⟨hx', hm⟩),
        indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨lt_trans ha0 hx', hm⟩)]
    · rw [indicator_of_notMem (fun h : x ∈ Ioc (1 / Real.sqrt N) 1 => hm h.2),
        indicator_of_notMem (fun h : x ∈ Ioc (0 : ℝ) 1 => hm h.2)]
  have e : ∀ x ∈ Ioi (1 / Real.sqrt N),
      gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) * ((Ioc (0 : ℝ) 1).indicator
        (fun x => P.eval (Real.log N + 2 * Real.log x) / x) x +
        gaussH x * P.eval (Real.log N + 2 * Real.log x) / x) := by
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
    integral_add hind (integrableOn_gaussH_eval_log P hN),
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (1 / Real.sqrt N) ∩ Ioc 0 1 = Ioc (1 / Real.sqrt N) 1 from by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, lt_trans ha0 h1, h3⟩]

/-- The flat part with `a = N^{−1/2}`: `∫_a^1 P(ℓ + 2 log x)/x = (primZero P)(ℓ)/2`. -/
theorem poly_flat_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, P.eval (Real.log N + 2 * Real.log x) / x =
      (primZero P).eval (Real.log N) / 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [integral_eval_log_div P (Real.log N) ha0 ha1]
  have hlog : Real.log N + 2 * Real.log (1 / Real.sqrt N) = 0 := by
    rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]; ring
  rw [hlog, eval_primZero_zero, sub_zero]

/-! ### The assembled remainder -/

/-- The exact remainder: for `N ≥ 1`,
`√N Z_{L+1} − (stepPoly P Q_L)(ℓ) = [2∫γ(v/√N)q_L − (2/s)Q_L] − (2/s) Σ_j (H_jP)(ℓ) 2^j ε_j`,
`ε_j = ∫₀^a h log^j x/x`. -/
theorem sqrt_mul_gaussLaplaceL_succ_sub_eq {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) {N : ℝ}
    (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N -
        (stepPoly P (residualMass L P)).eval (Real.log N) =
      (2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) -
        2 / Real.sqrt (2 * Real.pi) * residualMass L P) -
      2 / Real.sqrt (2 * Real.pi) *
        ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
          ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [sqrt_mul_gaussLaplaceL_succ_split h hN0, polyTail_integral_eq P hN0,
    polyTail_integral_split P hN, poly_flat_integral_eq P hN, poly_hpart_integral_eq P hN,
    eval_stepPoly]
  have hsplit : ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
      ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x =
      (∑ j ∈ range (P.natDegree + 1),
        2 ^ j * gaussJlogPow j * (hasseDeriv j P).eval (Real.log N)) -
      ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
        ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gaussH_log_pow_cutoff j ha0 ha1]
    unfold gaussJlogPow
    ring
  rw [hsplit]
  ring

/-! ### The step -/

set_option maxHeartbeats 1600000 in
-- the assembled remainder and the finite-sum bounds exceed the default budget
/-- ★★★ **The depth step**: the linear-log rate propagates from depth `L` with `P` to depth
`L + 1` with `stepPoly P Q_L`. -/
theorem HasPolyRate.step {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    HasPolyRate (L + 1) (stepPoly P (residualMass L P)) := by
  obtain ⟨K, hK0, hK⟩ := polyResidual_outer_le h
  set s := Real.sqrt (2 * Real.pi) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set d := P.natDegree with hd
  -- the coefficient constants
  set Cc : ℕ → ℝ := fun j => ∑ i ∈ range (d + 1), |(hasseDeriv j P).coeff i| with hCc
  have hCc0 : ∀ j, 0 ≤ Cc j := fun j => Finset.sum_nonneg fun i _ => abs_nonneg _
  set M : ℝ := ∑ j ∈ range (d + 1), Cc j * 2 ^ j * ((2 * j) ^ j / 3) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => by
    have := hCc0 j; positivity
  obtain ⟨Cd, hCd0, hCd⟩ := exists_log_pow_cutoff_constant d
  refine ⟨2 / s * (1 / 2 + K / 2 + 3 * K + M * Cd), by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  set ℓ := Real.log N with hℓdef
  set a : ℝ := 1 / Real.sqrt N with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one hsN]; exact hsN1
  have hasqrt : a * Real.sqrt a = N ^ (-(3 / 4 : ℝ)) := by
    rw [ha_def]; exact one_div_sqrt_mul_sqrt hN0
  set X : ℝ := (1 + ℓ) / Real.sqrt N with hX
  have hX0 : 0 < X := by positivity
  -- the residual term
  have hres := residual_term_bound_of_le (measurable_polyResidual L P) hK0
    (fun v hv => abs_polyResidual_inner_le L P hv) hK hN
  have hres' : |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) -
      2 / s * residualMass L P| ≤ 2 / s * (1 / 2 + K / 2 + 3 * K) * X := by
    unfold residualMass
    refine hres.trans ?_
    have h1 : 1 / (2 * N) ≤ 1 / 2 * X := by
      rw [hX]
      have hNs : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
      have h1' : 1 / N ≤ 1 / Real.sqrt N := one_div_le_one_div_of_le hsN hNs
      have h1'' : 1 / Real.sqrt N ≤ (1 + ℓ) / Real.sqrt N :=
        div_le_div_of_nonneg_right (by linarith) hsN.le
      have := h1'.trans h1''
      calc 1 / (2 * N) = 1 / 2 * (1 / N) := by ring
        _ ≤ 1 / 2 * ((1 + ℓ) / Real.sqrt N) := by linarith
    have h2 : K * (1 + ℓ) / (2 * Real.sqrt N) = K / 2 * X := by rw [hX]; ring
    have h3 : K * (3 + ℓ) / Real.sqrt N ≤ 3 * K * X := by
      rw [hX, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hsN.le
      nlinarith
    calc 2 / s * (1 / (2 * N) + K * (1 + ℓ) / (2 * Real.sqrt N) + K * (3 + ℓ) / Real.sqrt N)
        ≤ 2 / s * (1 / 2 * X + K / 2 * X + 3 * K * X) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [h1, h2, h3]
      _ = 2 / s * (1 / 2 + K / 2 + 3 * K) * X := by ring
  -- the cutoff sum
  have hcut : |∑ j ∈ range (d + 1), (hasseDeriv j P).eval ℓ * 2 ^ j *
      ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤ M * (Cd * X) := by
    have hterm : ∀ j ∈ range (d + 1), |(hasseDeriv j P).eval ℓ * 2 ^ j *
        ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤
        Cc j * 2 ^ j * ((2 * j) ^ j / 3) * ((1 + ℓ) ^ d * N ^ (-(3 / 4 : ℝ))) := by
      intro j _
      have hc : |(hasseDeriv j P).eval ℓ| ≤ Cc j * (1 + ℓ) ^ d :=
        abs_eval_le (hasseDeriv j P) ((natDegree_hasseDeriv_le P j).trans (Nat.sub_le _ _)) hℓ
      have he : |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤
          (2 * j) ^ j / 3 * N ^ (-(3 / 4 : ℝ)) := by
        rw [← hasqrt]; exact abs_integral_gaussH_log_pow_Ioc_le_sqrt j ha0 ha1
      rw [abs_mul, abs_mul, abs_pow, abs_two]
      calc |(hasseDeriv j P).eval ℓ| * 2 ^ j *
            |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x|
          ≤ Cc j * (1 + ℓ) ^ d * 2 ^ j * ((2 * j) ^ j / 3 * N ^ (-(3 / 4 : ℝ))) := by
            gcongr
        _ = Cc j * 2 ^ j * ((2 * j) ^ j / 3) * ((1 + ℓ) ^ d * N ^ (-(3 / 4 : ℝ))) := by ring
    calc |∑ j ∈ range (d + 1), (hasseDeriv j P).eval ℓ * 2 ^ j *
          ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x|
        ≤ ∑ j ∈ range (d + 1), |(hasseDeriv j P).eval ℓ * 2 ^ j *
          ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (d + 1), Cc j * 2 ^ j * ((2 * j) ^ j / 3) *
          ((1 + ℓ) ^ d * N ^ (-(3 / 4 : ℝ))) := Finset.sum_le_sum hterm
      _ = M * ((1 + ℓ) ^ d * N ^ (-(3 / 4 : ℝ))) := by rw [hM, Finset.sum_mul]
      _ ≤ M * (Cd * X) := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          rw [hX, ← mul_div_assoc]
          exact hCd N hN
  -- assemble
  rw [sqrt_mul_gaussLaplaceL_succ_sub_eq h hN]
  rw [← hℓdef, ← ha_def, ← hd]
  calc |(2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) -
        2 / s * residualMass L P) - 2 / s * ∑ j ∈ range (d + 1),
          (hasseDeriv j P).eval ℓ * 2 ^ j * ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x|
      ≤ |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) -
        2 / s * residualMass L P| + 2 / s * |∑ j ∈ range (d + 1),
          (hasseDeriv j P).eval ℓ * 2 ^ j *
            ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / s)]
    _ ≤ 2 / s * (1 / 2 + K / 2 + 3 * K) * X + 2 / s * (M * (Cd * X)) := by gcongr
    _ = 2 / s * (1 / 2 + K / 2 + 3 * K + M * Cd) * X := by ring
    _ = 2 / s * (1 / 2 + K / 2 + 3 * K + M * Cd) * (1 + ℓ) / Real.sqrt N := by
        rw [hX]; ring

end Grammar
