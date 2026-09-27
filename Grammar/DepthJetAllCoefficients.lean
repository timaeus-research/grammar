/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.JetUniqueness

/-!
# Every coefficient of every `P_L` from the Taylor jet of `H_L`

With `H_D(z) = 2^{(D−1)z} Γ(½ − z) Γ(1 + z)^D/√π` (`depthJet`, analytic at `0`) and its Taylor
coefficients `h_{D,j} = H_D^{(j)}(0)/j!` (`depthJetCoeff`, complex), the closed Mellin transform
of DCLXX reads `M_{L+1}(1 − 2u) = H_{L+1}(u)/(2 s^L u^{L+1})` (`depthClosed_eq`, `s = √(2π)`)
and the poles `Σ_k 2^k k! a_k/(2u)^{k+1}` collapse to `Σ_j s^L (L−j)! a_{L−j} u^j/(2 s^L u^{L+1})`
(`depthPoles_sum_eq`), so DCLXX's finite-part limit is a scaled-remainder statement for
`H_{L+1}` of order `L + 1` (`tendsto_depthJet_scaled`).  Mathlib's power-series bound
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow` gives the Taylor remainder
(`tendsto_depthJet_remainder`), and the jet uniqueness lemma of `JetUniqueness` identifies
(★★★ `coeff_enginePoly_eq_depthJetCoeff`, ★★★ `residualMass_eq_depthJetCoeff`)

  `a_{L+1,k} = h_{L+1,L−k}/(s^L k!)` for `k ≤ L`,   `Q_{L+1} = h_{L+1,L+1}/(2 s^L)`,

at every depth: the engine's polynomial and residual mass are the Taylor jet of one explicit
analytic Gamma product, whose derivatives at `0` are polynomials in `log 2`, `Γ^{(j)}(1)` and
`Γ^{(j)}(½)` (DCLXXIII, DCLXXII).  Regression: `depthJetCoeff_zero = 1` reproduces the leading
coefficient.  Examples_slop §2; Astra round 24 target 1.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset Asymptotics Polynomial

namespace Grammar

/-! ### The jet function -/

/-- `H_D(u) = 2^{(D−1)u} Γ(½ − u) Γ(1 + u)^D/√π` (real). -/
noncomputable def depthJetReal (D : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ) ^ (((D : ℝ) - 1) * u) * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ D /
    Real.sqrt Real.pi

/-- `H_D(z) = 2^{(D−1)z} Γ(½ − z) Γ(1 + z)^D/√π` (complex). -/
noncomputable def depthJet (D : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ (((D : ℂ) - 1) * z) * Complex.Gamma (1 / 2 - z) * Complex.Gamma (1 + z) ^ D /
    ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- The Taylor coefficients `h_{D,j} = H_D^{(j)}(0)/j!`. -/
noncomputable def depthJetCoeff (D j : ℕ) : ℂ := iteratedDeriv j (depthJet D) 0 / (j.factorial : ℂ)

theorem depthJet_ofReal (D : ℕ) (u : ℝ) : depthJet D u = ((depthJetReal D u : ℝ) : ℂ) := by
  unfold depthJet depthJetReal
  rw [show (1 / 2 : ℂ) - (u : ℂ) = ((1 / 2 - u : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
    show ((D : ℂ) - 1) * (u : ℂ) = ((((D : ℝ) - 1) * u : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  rw [Complex.ofReal_cpow (by norm_num)]
  push_cast
  ring

theorem depthJet_zero (D : ℕ) : depthJet D 0 = 1 := by
  unfold depthJet
  rw [mul_zero, Complex.cpow_zero, sub_zero, add_zero, Gamma_one_half_ofReal, Complex.Gamma_one,
    one_pow, one_mul, mul_one, div_self]
  exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'

theorem depthJetCoeff_zero (D : ℕ) : depthJetCoeff D 0 = 1 := by
  unfold depthJetCoeff
  rw [iteratedDeriv_zero, depthJet_zero, Nat.factorial_zero, Nat.cast_one, div_one]

theorem analyticAt_depthJet (D : ℕ) : AnalyticAt ℂ (depthJet D) 0 := by
  have hA : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ (((D : ℂ) - 1) * z)) 0 :=
    analyticAt_const.cpow (analyticAt_const.mul analyticAt_id)
      (by simp)
  have hB : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (1 / 2 - z)) 0 :=
    (analyticAt_Gamma_of_re_pos (z := 1 / 2 - 0) (by norm_num)).comp
      (analyticAt_const.sub analyticAt_id)
  have hC : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (1 + z)) 0 :=
    (analyticAt_Gamma_of_re_pos (z := 1 + 0) (by norm_num)).comp
      (analyticAt_const.add analyticAt_id)
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  exact ((hA.mul hB).mul (hC.pow D)).div analyticAt_const hsp

/-! ### The Taylor remainder -/

theorem isBigO_depthJet_sub_partialSum (D : ℕ) :
    (fun y : ℂ => depthJet D y - ∑ j ∈ range (D + 1), depthJetCoeff D j * y ^ j) =O[𝓝 0]
      fun y => ‖y‖ ^ (D + 1) := by
  obtain ⟨p, hp⟩ := analyticAt_depthJet D
  have hcoeff : ∀ j, p.coeff j = depthJetCoeff D j := by
    intro j
    obtain ⟨r, hr⟩ := hp
    have h := hr.factorial_smul 1 j
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul, nsmul_eq_mul,
      ← iteratedDeriv_eq_iteratedFDeriv] at h
    unfold depthJetCoeff
    rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne'), mul_comm]
    exact h
  have h := hp.isBigO_sub_partialSum_pow (D + 1)
  refine h.congr_left fun y => ?_
  rw [zero_add]
  unfold FormalMultilinearSeries.partialSum
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, hcoeff, mul_comm]

theorem tendsto_depthJet_remainder (D : ℕ) :
    Tendsto (fun u : ℝ => (depthJet D u - ∑ j ∈ range (D + 1), depthJetCoeff D j * (u : ℂ) ^ j) /
      (u : ℂ) ^ D) (𝓝[>] 0) (𝓝 0) := by
  have hO := (isBigO_depthJet_sub_partialSum D).comp_tendsto tendsto_ofReal_nhdsGT_zero
  obtain ⟨C, hC⟩ := hO.bound
  have hbound : (fun u : ℝ => (depthJet D u - ∑ j ∈ range (D + 1),
      depthJetCoeff D j * (u : ℂ) ^ j) / (u : ℂ) ^ D) =O[𝓝[>] 0] fun u : ℝ => u := by
    refine IsBigO.of_bound C ?_
    filter_upwards [hC, self_mem_nhdsWithin] with u hu hu0
    have hu0' : (0 : ℝ) < u := hu0
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_of_nonneg hu0'.le,
      Real.norm_of_nonneg (pow_nonneg hu0'.le (D + 1))] at hu
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0'.le,
      div_le_iff₀ (pow_pos hu0' D)]
    calc ‖depthJet D u - ∑ j ∈ range (D + 1), depthJetCoeff D j * (u : ℂ) ^ j‖
        ≤ C * u ^ (D + 1) := hu
      _ = C * u * u ^ D := by ring
  have hid : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact hbound.trans_tendsto hid

/-! ### The closed Mellin transform at `z = 1 − 2u` and the poles -/

theorem two_rpow_neg_half_sub (u : ℝ) : (2 : ℝ) ^ (-(1 - 2 * u) / 2) = 2 ^ u / Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- `M_{L+1}(1 − 2u) = H_{L+1}(u)/(2 s^L u^{L+1})`. -/
theorem depthClosed_eq (L : ℕ) {u : ℝ} (hu0 : 0 < u) :
    ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ L * Real.Gamma ((1 - 2 * u) / 2) *
      Real.Gamma ((1 - (1 - 2 * u)) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1)) =
      depthJetReal (L + 1) u / (2 * Real.sqrt (2 * Real.pi) ^ L * u ^ (L + 1)) := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hG : Real.Gamma ((1 - (1 - 2 * u)) / 2) = Real.Gamma (1 + u) / u := by
    rw [show (1 - (1 - 2 * u)) / 2 = u by ring, add_comm, Real.Gamma_add_one hu0.ne']
    field_simp
  have hpow : ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ L =
      (2 : ℝ) ^ ((((L + 1 : ℕ) : ℝ) - 1) * u) / Real.sqrt 2 ^ L := by
    rw [two_rpow_neg_half_sub, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 2
    push_cast
    ring
  have hs : Real.sqrt (2 * Real.pi) ^ L = Real.sqrt 2 ^ L * Real.sqrt Real.pi ^ L := by
    rw [Real.sqrt_mul (by norm_num), mul_pow]
  rw [hG, div_pow, hpow, hs, show (1 - 2 * u) / 2 = 1 / 2 - u by ring]
  unfold depthJetReal
  have hu' : u ≠ 0 := hu0.ne'
  have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
  have hsp' : Real.sqrt Real.pi ≠ 0 := hsp.ne'
  field_simp
  ring

/-- The poles at `z = 1 − 2u`, reindexed: `Σ_k 2^k k! a_k/(2u)^{k+1} =
Σ_j s^L (L−j)! a_{L−j} u^j/(2 s^L u^{L+1})`. -/
theorem depthPoles_sum_eq (L : ℕ) (hL : 1 ≤ L) {u : ℝ} (hu : u ≠ 0) :
    ∑ k : Fin ((enginePoly (L + 1)).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly (L + 1)).coeff k) *
      ((k : ℕ).factorial : ℝ) / (1 - (1 - 2 * u)) ^ ((k : ℕ) + 1) =
      (∑ j ∈ range (L + 1), Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) * u ^ j) /
        (2 * Real.sqrt (2 * Real.pi) ^ L * u ^ (L + 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (2 ^ k * (enginePoly (L + 1)).coeff k) *
    (k.factorial : ℝ) / (1 - (1 - 2 * u)) ^ (k + 1)), natDegree_enginePoly (L + 1) (by omega),
    Nat.add_sub_cancel,
    ← Finset.sum_range_reflect (fun k => (2 ^ k * (enginePoly (L + 1)).coeff k) *
      (k.factorial : ℝ) / (1 - (1 - 2 * u)) ^ (k + 1)) (L + 1), Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Nat.add_sub_cancel]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs' : Real.sqrt (2 * Real.pi) ≠ 0 := hs.ne'
  have hu' : u ^ (L + 1) = u ^ (L - j + 1) * u ^ j := by
    rw [← pow_add]
    congr 1
    omega
  rw [hu', show (1 - (1 - 2 * u)) = 2 * u by ring, mul_pow]
  field_simp
  ring

/-- DCLXX's finite part as a scaled remainder of `H_{L+1}` of order `L + 1`. -/
theorem tendsto_depthJet_scaled (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun u : ℝ => (depthJet (L + 1) u - ∑ j ∈ range (L + 1),
      ((Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) : ℝ) : ℂ) * (u : ℂ) ^ j) / (u : ℂ) ^ (L + 1))
      (𝓝[>] 0)
      (𝓝 ((2 * Real.sqrt (2 * Real.pi) ^ L *
        residualMass (L + 1) (enginePoly (L + 1)) : ℝ) : ℂ)) := by
  have h1 := (tendsto_gammaProduct_sub_poles L hL).comp tendsto_one_sub_two_mul_nhdsLT
  have h2 := h1.const_mul (2 * Real.sqrt (2 * Real.pi) ^ L)
  have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
  simp only [Function.comp_apply]
  rw [depthPoles_sum_eq L hL hu.1.ne', depthClosed_eq L hu.1, depthJet_ofReal]
  push_cast
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi)).ne'
  field_simp

/-! ### The identification -/

/-- The jet of `H_{L+1}` to order `L + 1` in terms of `P_{L+1}` and `Q_{L+1}`. -/
theorem depthJetCoeff_eq (L : ℕ) (hL : 1 ≤ L) :
    (∀ j < L + 1, depthJetCoeff (L + 1) j =
      ((Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
        (enginePoly (L + 1)).coeff (L - j) : ℝ) : ℂ)) ∧
    depthJetCoeff (L + 1) (L + 1) =
      ((2 * Real.sqrt (2 * Real.pi) ^ L * residualMass (L + 1) (enginePoly (L + 1)) : ℝ) : ℂ) :=
  jet_unique_of_scaled_remainders (L + 1) (fun u => depthJet (L + 1) u) (depthJetCoeff (L + 1))
    (fun j => ((Real.sqrt (2 * Real.pi) ^ L * ((L - j).factorial : ℝ) *
      (enginePoly (L + 1)).coeff (L - j) : ℝ) : ℂ)) _
    (tendsto_depthJet_remainder (L + 1)) (tendsto_depthJet_scaled L hL)

/-- ★★★ **Every coefficient of every `P_{L+1}` is a Taylor coefficient of `H_{L+1}`**:
`a_{L+1,k} = h_{L+1,L−k}/(s^L k!)` for `k ≤ L`. -/
theorem coeff_enginePoly_eq_depthJetCoeff (L : ℕ) (hL : 1 ≤ L) {k : ℕ} (hk : k ≤ L) :
    (enginePoly (L + 1)).coeff k =
      (depthJetCoeff (L + 1) (L - k)).re / (Real.sqrt (2 * Real.pi) ^ L * (k.factorial : ℝ)) := by
  have h := (depthJetCoeff_eq L hL).1 (L - k) (by omega)
  rw [Nat.sub_sub_self hk] at h
  rw [h, Complex.ofReal_re, eq_div_iff (by positivity)]
  ring

/-- ★★★ **Every residual mass is a Taylor coefficient of `H_{L+1}`**:
`Q_{L+1} = h_{L+1,L+1}/(2 s^L)`. -/
theorem residualMass_eq_depthJetCoeff (L : ℕ) (hL : 1 ≤ L) :
    residualMass (L + 1) (enginePoly (L + 1)) =
      (depthJetCoeff (L + 1) (L + 1)).re / (2 * Real.sqrt (2 * Real.pi) ^ L) := by
  have h := (depthJetCoeff_eq L hL).2
  rw [h, Complex.ofReal_re, eq_div_iff (by positivity)]
  ring

/-- The jet coefficients are real. -/
theorem depthJetCoeff_im (L : ℕ) (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ L + 1) :
    (depthJetCoeff (L + 1) j).im = 0 := by
  rcases Nat.lt_or_ge j (L + 1) with h | h
  · rw [(depthJetCoeff_eq L hL).1 j h, Complex.ofReal_im]
  · rw [show j = L + 1 by omega, (depthJetCoeff_eq L hL).2, Complex.ofReal_im]

/-- Regression: the leading coefficient `a_{L+1,L} = 1/(s^L L!)` from `h_{L+1,0} = 1`. -/
theorem coeff_enginePoly_top_eq (L : ℕ) (hL : 1 ≤ L) :
    (enginePoly (L + 1)).coeff L = 1 / (Real.sqrt (2 * Real.pi) ^ L * (L.factorial : ℝ)) := by
  rw [coeff_enginePoly_eq_depthJetCoeff L hL le_rfl, Nat.sub_self, depthJetCoeff_zero,
    Complex.one_re]

end Grammar
