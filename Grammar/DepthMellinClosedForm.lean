/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeMellinClosedForm
import Grammar.PolynomialEngineCoefficients
import Grammar.MellinLogPolynomialTransfer

/-!
# The Mellin transform at every depth and the residual masses as finite parts

`M_L(z) = ∫₀^∞ v^{z−1} Z_L(v²) dv` (`depthMellin`).  Through the expectation form
`Z_{L+1}(v²) = E[(1 + v²X²)^{−1/2}]`, `X = ∏_{i<L} W_i` (DCXVI's `gaussLaplaceL_succ`), the
substitution `u = |X|v` and the negative Gaussian moment (DCXLIV, one factor per coordinate):
★★★ `depthMellin_succ_eq : M_{L+1}(z) = (2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1} / (2√π^{L+1})` for
`0 < z < 1`, `L ≥ 1` (DCXLIV is `L = 1`).  Integrability of `v^{z−1} Z_L(v²)` on `(0,∞)` comes from
the engine's rate (`gaussLaplaceL_sq_le_of_hasPolyRate`: `Z_L(v²) ≤ C(1 + 2 log v)^{deg+1}/v` beyond
`1`).  With DCXLIX's log-polynomial transfer and the engine's residual, the residual mass at every
depth is the finite part of the Mellin transform at the pole `z = 1`:
★★★ `tendsto_depthMellin_sub_poles : M_L(z) − Σ_{k<L} 2^k k! a_k/(1−z)^{k+1} → Q_L` as `z → 1⁻`,
`a_k = (enginePoly L)_k`, `Q_L = residualMass L (enginePoly L)`, and in the closed form
`tendsto_gammaProduct_sub_poles`.  The Laurent expansion of the Gamma product to order `L` — the
jet — is what remains to close the constants (`ζ(3)` at depth three).  Astra round 21.
Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial
open Finset (range)

namespace Grammar

/-- `M_L(z) = ∫₀^∞ v^{z−1} Z_L(v²) dv`. -/
noncomputable def depthMellin (L : ℕ) (z : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * gaussLaplaceL L (v ^ 2)

theorem depthMellin_two (z : ℝ) : depthMellin 2 z = depthThreeMellin z := by
  unfold depthMellin depthThreeMellin
  simp only [gaussLaplaceL_two]

/-! ### Integrability of `v^{z−1} Z_L(v²)` -/

theorem integrableOn_rpow_mul_gaussLaplaceL_sq_inner (L : ℕ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioc 0 1) := by
  have hI : IntegrableOn (fun v : ℝ => v ^ (z - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine hI.mono' ((measurable_id.pow_const _).mul
    (measurable_gaussLaplaceL_sq L)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun v hv => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _),
    abs_of_nonneg (gaussLaplaceL_nonneg L _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hv.1.le _) (gaussLaplaceL_le_one L (sq_nonneg _))

/-- Beyond `1`, `Z_L(v²) ≤ C(1 + 2 log v)^{deg P + 1}/v` from a rate with polynomial `P`. -/
theorem gaussLaplaceL_sq_le_of_hasPolyRate {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 1 ≤ v →
      gaussLaplaceL L (v ^ 2) ≤ C * (1 + 2 * Real.log v) ^ (P.natDegree + 1) / v := by
  obtain ⟨K, hK0, hK⟩ := h
  set Cc : ℝ := ∑ i ∈ range (P.natDegree + 1), |P.coeff i| with hCc
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨Cc + K, by positivity, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have hv2 : 1 ≤ v ^ 2 := by nlinarith
  have hl : 0 ≤ 2 * Real.log v := by linarith [Real.log_nonneg hv]
  set T := 1 + 2 * Real.log v with hT
  have hT1 : 1 ≤ T := by linarith
  have h1 := hK (v ^ 2) hv2
  rw [Real.sqrt_sq hv0.le, Real.log_pow, Nat.cast_ofNat] at h1
  have hP : |P.eval (2 * Real.log v)| ≤ Cc * T ^ P.natDegree := abs_eval_le P le_rfl hl
  have hZ : v * gaussLaplaceL L (v ^ 2) ≤ |P.eval (2 * Real.log v)| + K * T / v := by
    have h2 : v * gaussLaplaceL L (v ^ 2) - P.eval (2 * Real.log v) ≤ K * T / v :=
      (le_abs_self _).trans h1
    linarith [le_abs_self (P.eval (2 * Real.log v))]
  have hTd : T ^ P.natDegree ≤ T ^ (P.natDegree + 1) := pow_le_pow_right₀ hT1 (Nat.le_succ _)
  have hTT : T ≤ T ^ (P.natDegree + 1) := le_self_pow₀ hT1 (Nat.succ_ne_zero _)
  have hKv : K * T / v ≤ K * T := by
    rw [div_le_iff₀ hv0]
    nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ T)]
  rw [le_div_iff₀ hv0]
  calc gaussLaplaceL L (v ^ 2) * v = v * gaussLaplaceL L (v ^ 2) := mul_comm _ _
    _ ≤ Cc * T ^ P.natDegree + K * T := by linarith
    _ ≤ Cc * T ^ (P.natDegree + 1) + K * T ^ (P.natDegree + 1) := by
        gcongr
    _ = (Cc + K) * T ^ (P.natDegree + 1) := by ring

theorem integrableOn_rpow_mul_one_add_log_pow (d : ℕ) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * (1 + 2 * Real.log v) ^ d) (Ioi 1) := by
  have h : IntegrableOn (fun v : ℝ => ∑ m ∈ range (d + 1),
      (d.choose m : ℝ) * 2 ^ m * (v ^ (z - 2) * Real.log v ^ m)) (Ioi 1) :=
    integrable_finsetSum _ fun m _ => (integrableOn_Ioi_one_rpow_mul_log_pow hz m).const_mul _
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  rw [add_comm (1 : ℝ), add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, one_pow]
  ring

theorem integrableOn_rpow_mul_gaussLaplaceL_sq_outer (L : ℕ) (hL : 2 ≤ L) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioi 1) := by
  obtain ⟨C, hC0, hC⟩ := gaussLaplaceL_sq_le_of_hasPolyRate (hasPolyRate_enginePoly L hL)
  refine ((integrableOn_rpow_mul_one_add_log_pow ((enginePoly L).natDegree + 1) hz).const_mul
    C).mono' ((measurable_id.pow_const _).mul (measurable_gaussLaplaceL_sq L)).aestronglyMeasurable
    ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  have hv0 : 0 < v := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv0.le _),
    abs_of_nonneg (gaussLaplaceL_nonneg L _)]
  calc v ^ (z - 1) * gaussLaplaceL L (v ^ 2)
      ≤ v ^ (z - 1) * (C * (1 + 2 * Real.log v) ^ ((enginePoly L).natDegree + 1) / v) :=
        mul_le_mul_of_nonneg_left (hC v hv1.le) (Real.rpow_nonneg hv0.le _)
    _ = C * (v ^ (z - 2) * (1 + 2 * Real.log v) ^ ((enginePoly L).natDegree + 1)) := by
        have hv2 : v ^ (z - 1) = v ^ (z - 2) * v := by
          rw [← Real.rpow_add_one hv0.ne']; congr 1; ring
        rw [hv2]
        field_simp

/-- ★★ `v^{z−1} Z_L(v²)` is integrable on `(0,∞)` for `0 < z < 1`, `L ≥ 2`. -/
theorem integrableOn_rpow_mul_gaussLaplaceL_sq (L : ℕ) (hL : 2 ≤ L) {z : ℝ} (hz0 : 0 < z)
    (hz1 : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_rpow_mul_gaussLaplaceL_sq_inner L hz0).union
    (integrableOn_rpow_mul_gaussLaplaceL_sq_outer L hL hz1)

/-! ### The closed form -/

/-- The Mellin integrand at depth `L + 1`, `(v, b) ↦ v^{z−1}(1 + v²(∏b)²)^{−1/2} ∏γ(bᵢ)`. -/
noncomputable def mellinIntegrand (L : ℕ) (z : ℝ) (v : ℝ) (b : Fin L → ℝ) : ℝ :=
  v ^ (z - 1) * (1 / Real.sqrt (1 + v ^ 2 * (∏ i, b i) ^ 2) * ∏ i, gaussDensity (b i))

theorem measurable_uncurry_mellinIntegrand (L : ℕ) (z : ℝ) :
    Measurable (Function.uncurry (mellinIntegrand L z)) := by
  have : Function.uncurry (mellinIntegrand L z) = fun p : ℝ × (Fin L → ℝ) =>
      p.1 ^ (z - 1) *
        (1 / Real.sqrt (1 + p.1 ^ 2 * (∏ i, p.2 i) ^ 2) * ∏ i, gaussDensity (p.2 i)) := by
    funext p; rfl
  rw [this]
  refine (measurable_fst.pow_const _).mul ((measurable_const.div ?_).mul
    ((continuous_prod_gaussDensity L).measurable.comp measurable_snd))
  exact Real.continuous_sqrt.measurable.comp (measurable_const.add
    ((measurable_fst.pow_const 2).mul
      (((continuous_prod_coord L).measurable.comp measurable_snd).pow_const 2)))

theorem mellinIntegrand_nonneg (L : ℕ) (z : ℝ) {v : ℝ} (hv : 0 < v) (b : Fin L → ℝ) :
    0 ≤ mellinIntegrand L z v b := by
  unfold mellinIntegrand
  have := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => gaussDensity_nonneg (b i)
  have := Real.rpow_nonneg hv.le (z - 1)
  positivity

theorem integrable_mellinIntegrand (L : ℕ) (hL : 1 ≤ L) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry (mellinIntegrand L z))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  rw [integrable_prod_iff (measurable_uncurry_mellinIntegrand L z).aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    have hm : AEStronglyMeasurable (fun b : Fin L → ℝ => mellinIntegrand L z v b) volume :=
      ((measurable_uncurry_mellinIntegrand L z).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    simp only [Function.uncurry_apply_pair]
    refine ((integrable_prod_gaussDensity L).const_mul (v ^ (z - 1))).mono' hm
      (Eventually.of_forall fun b => ?_)
    have h1 : 1 ≤ Real.sqrt (1 + v ^ 2 * (∏ i, b i) ^ 2) :=
      Real.one_le_sqrt.2 (by linarith [mul_nonneg (sq_nonneg v) (sq_nonneg (∏ i, b i))])
    have hγ := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => gaussDensity_nonneg (b i)
    have hvp : 0 ≤ v ^ (z - 1) := Real.rpow_nonneg hv'.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mellinIntegrand_nonneg L z hv' b)]
    unfold mellinIntegrand
    calc v ^ (z - 1) * (1 / Real.sqrt (1 + v ^ 2 * (∏ i, b i) ^ 2) * ∏ i, gaussDensity (b i))
        ≤ v ^ (z - 1) * (1 / 1 * ∏ i, gaussDensity (b i)) := by gcongr
      _ = v ^ (z - 1) * ∏ i, gaussDensity (b i) := by rw [div_one, one_mul]
  · have e : ∀ v ∈ Ioi (0 : ℝ),
        (∫ b : Fin L → ℝ, ‖Function.uncurry (mellinIntegrand L z) (v, b)‖) =
        v ^ (z - 1) * gaussLaplaceL (L + 1) (v ^ 2) := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      rw [gaussLaplaceL_succ L (sq_nonneg v), ← integral_const_mul]
      congr 1
      funext b
      rw [Function.uncurry_apply_pair, Real.norm_eq_abs,
        abs_of_nonneg (mellinIntegrand_nonneg L z hv' b)]
      rfl
    exact (integrableOn_rpow_mul_gaussLaplaceL_sq (L + 1) (by omega) hz0 hz1).congr_fun
      (fun v hv => (e v hv).symm) measurableSet_Ioi

/-- Almost every `b` has `∏ bᵢ ≠ 0`. -/
theorem ae_prod_ne_zero (L : ℕ) : ∀ᵐ b : Fin L → ℝ, ∏ i, b i ≠ 0 := by
  rw [volume_pi]
  have h : ∀ᵐ b : Fin L → ℝ ∂(Measure.pi fun _ => volume), ∀ i, b i ≠ 0 :=
    ae_all_iff.2 fun i => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) i 0
  exact h.mono fun b hb => Finset.prod_ne_zero_iff.2 fun i _ => hb i

/-- ★★★ **The closed form at every depth**:
`M_{L+1}(z) = (2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1} / (2√π^{L+1})` for `0 < z < 1`, `L ≥ 1`. -/
theorem depthMellin_succ_eq (L : ℕ) (hL : 1 ≤ L) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthMellin (L + 1) z = ((2 : ℝ) ^ (-z / 2)) ^ L * Real.Gamma (z / 2) *
      Real.Gamma ((1 - z) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1)) := by
  unfold depthMellin
  have e : ∀ v ∈ Ioi (0 : ℝ), v ^ (z - 1) * gaussLaplaceL (L + 1) (v ^ 2) =
      ∫ b : Fin L → ℝ, mellinIntegrand L z v b := by
    intro v _
    rw [gaussLaplaceL_succ L (sq_nonneg v), ← integral_const_mul]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_integral_swap (integrable_mellinIntegrand L hL hz0 hz1)]
  have e2 : ∀ b : Fin L → ℝ, ∏ i, b i ≠ 0 →
      (∫ v in Ioi (0 : ℝ), mellinIntegrand L z v b) =
        mellinHalfBeta z * ∏ i, (|b i| ^ (-z) * gaussDensity (b i)) := by
    intro b hb
    have : (fun v : ℝ => mellinIntegrand L z v b) = fun v =>
        (∏ i, gaussDensity (b i)) * (v ^ (z - 1) / Real.sqrt (1 + v ^ 2 * (∏ i, b i) ^ 2)) := by
      funext v; unfold mellinIntegrand; ring
    rw [this, integral_const_mul, integral_rpow_div_sqrt_one_add_mul_sq hb, Finset.abs_prod,
      ← Real.finsetProd_rpow _ _ (fun i _ => abs_nonneg _) _, Finset.prod_mul_distrib]
    ring
  rw [integral_congr_ae ((ae_prod_ne_zero L).mono fun b hb => e2 b hb), integral_const_mul,
    volume_pi, integral_fintype_prod_eq_pow (f := fun g : ℝ => |g| ^ (-z) * gaussDensity g),
    Fintype.card_fin, integral_abs_rpow_neg_mul_gaussDensity hz1, mellinHalfBeta_eq hz0 hz1]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [div_pow, mul_pow]
  field_simp
  ring

/-- Consistency with DCXLIV at `L = 1`. -/
theorem depthMellin_two_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthMellin 2 z =
      (2 : ℝ) ^ (-1 - z / 2) * Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) ^ 2 / Real.pi := by
  rw [depthMellin_two, depthThreeMellin_eq hz0 hz1]

/-! ### The residual mass as the finite part -/

/-- The engine's tail is DCXLIX's log-polynomial tail with coefficients `2^k a_k`. -/
theorem polyTail_eq_mellinLogTail (P : ℝ[X]) :
    polyTail P = mellinLogTail (fun k : Fin (P.natDegree + 1) => 2 ^ (k : ℕ) * P.coeff k) := by
  funext v
  unfold polyTail mellinLogTail
  by_cases hv : 1 < v
  · rw [indicator_of_mem (show v ∈ Ioi (1 : ℝ) from hv), if_pos hv]
    congr 1
    rw [eval_eq_sum_range,
      Fin.sum_univ_eq_sum_range (fun k => 2 ^ k * P.coeff k * Real.log v ^ k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  · rw [indicator_of_notMem (show v ∉ Ioi (1 : ℝ) from hv), if_neg hv]

/-- ★★★ **The residual mass is the finite part of the Mellin transform at `z = 1`**: for `L ≥ 2`,
`M_L(z) − Σ_{k ≤ L−1} 2^k a_k k!/(1−z)^{k+1} → Q_L` as `z → 1⁻`, `a_k = (enginePoly L)_k`. -/
theorem tendsto_depthMellin_sub_poles (L : ℕ) (hL : 2 ≤ L) :
    Tendsto (fun z : ℝ => depthMellin L z -
      ∑ k : Fin ((enginePoly L).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly L).coeff k) *
        ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (residualMass L (enginePoly L))) := by
  have hq := integrableOn_polyResidual (hasPolyRate_enginePoly L hL)
  have hsmall : IntegrableOn (fun v : ℝ => v ^ ((1 / 2 : ℝ) - 1) * polyResidual L (enginePoly L) v)
      (Ioc 0 1) := by
    have hI : IntegrableOn (fun v : ℝ => v ^ ((1 / 2 : ℝ) - 1)) (Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine hI.mono' ((measurable_id.pow_const _).mul
      (measurable_polyResidual L _)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v hv => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hv.1.le _)
      (abs_polyResidual_inner_le L _ hv)
  have h := tendsto_mellin_sub_logPolynomial
    (fun k : Fin ((enginePoly L).natDegree + 1) => 2 ^ (k : ℕ) * (enginePoly L).coeff k)
    (q := polyResidual L (enginePoly L)) (a := 1 / 2) (by norm_num)
    (measurable_polyResidual L _) hsmall (hq.mono_set (Ioi_subset_Ioi zero_le_one))
  unfold residualMass
  refine h.congr' (Eventually.of_forall fun z => ?_)
  simp only
  congr 1
  unfold depthMellin
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [← polyTail_eq_mellinLogTail, polyResidual_add_tail]

/-- ★★★ The finite part of the Gamma product: for `L ≥ 1`,
`(2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1}/(2√π^{L+1}) − Σ_k 2^k a_k k!/(1−z)^{k+1} → Q_{L+1}`. -/
theorem tendsto_gammaProduct_sub_poles (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun z : ℝ => ((2 : ℝ) ^ (-z / 2)) ^ L * Real.Gamma (z / 2) *
      Real.Gamma ((1 - z) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1)) -
      ∑ k : Fin ((enginePoly (L + 1)).natDegree + 1),
        (2 ^ (k : ℕ) * (enginePoly (L + 1)).coeff k) *
          ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (residualMass (L + 1) (enginePoly (L + 1)))) := by
  refine (tendsto_depthMellin_sub_poles (L + 1) (by omega)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with z hz
  rw [depthMellin_succ_eq L hL hz.1 hz.2]

end Grammar
