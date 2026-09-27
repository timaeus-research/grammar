/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeGammaJet
import Grammar.DepthThreeMellinClosedForm
import Grammar.GaussJlogExact

/-!
# The depth-three constant of the Gaussian DLN in closed form

`Q = ∫₀^∞ q = (c² + 5π²/6)/(4s)` (★★★ `depthThreeQint_eq`), `c = 3 log 2 − γ`, `s = √(2π)`:
the Mellin bridge `M(z) − poles(z) → Q` as `z → 1⁻` (DCXLII), the closed form
`M(z) = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` (DCXLIV) rewritten at `z = 1 − 2u` as `F(u)/(2su²)` with
`poles(1 − 2u) = (1 + cu)/(2su²)` (`depthThreeMellin_sub_poles_eq`), and the regularised jet
`(F(u) − 1 − cu)/u² → (c² + 5π²/6)/2` (DCXLIII); uniqueness of limits closes.  With the exact
`J = R₀²/2 + π²/48` (DCXXXVIII) the depth-three constant is

  `C₃ = depthThreeConst = ((4 log 2 − 2γ)² + π²)/(4π) = 0.99377`   (★★★ `depthThreeConst_eq`),

i.e. `√N Z₃(N) = (log N)²/(4π) + (2 log 2 − γ)(log N)/π + ((4 log 2 − 2γ)² + π²)/(4π) + O(log N/√N)`
(examples_slop §2 eq. dln_gauss at `L = 3`; Astra round-13).  Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

/-! ### `F` as a real closed form -/

theorem jetF_ofReal (u : ℝ) :
    jetF u = ((2 ^ u * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ 2 / Real.sqrt Real.pi : ℝ) :
      ℂ) := by
  unfold jetF
  have h2 : (2 : ℂ) ^ (u : ℂ) = ((2 ^ u : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num) u]; push_cast; rfl
  have hg1 : Complex.Gamma (1 / 2 - (u : ℂ)) = ((Real.Gamma (1 / 2 - u) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have hg2 : Complex.Gamma (1 + (u : ℂ)) = ((Real.Gamma (1 + u) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  rw [h2, hg1, hg2]
  push_cast
  rfl

theorem gammaJetF_eq (u : ℝ) :
    gammaJetF u = 2 ^ u * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ 2 / Real.sqrt Real.pi := by
  rw [gammaJetF, jetF_ofReal, Complex.ofReal_re]

/-! ### `M(1 − 2u) − poles(1 − 2u) = (F(u) − 1 − cu)/(2su²)` -/

theorem depthThreeMellin_sub_poles_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    depthThreeMellin (1 - 2 * u) - depthThreePoles (1 - 2 * u) =
      (gammaJetF u - 1 - depthThreeC * u) / (2 * Real.sqrt (2 * Real.pi) * u ^ 2) := by
  rw [depthThreeMellin_eq (by linarith) (by linarith), gammaJetF_eq]
  unfold depthThreePoles
  have hs2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  -- the Gamma arguments
  have hG1 : Real.Gamma ((1 - 2 * u) / 2) = Real.Gamma (1 / 2 - u) := by congr 1; ring
  have hG2 : Real.Gamma ((1 - (1 - 2 * u)) / 2) = Real.Gamma (1 + u) / u := by
    rw [show (1 - (1 - 2 * u)) / 2 = u by ring, eq_div_iff hu0.ne', mul_comm,
      ← Real.Gamma_add_one hu0.ne', add_comm]
  -- the power of two
  have h2 : (2 : ℝ) ^ (-1 - (1 - 2 * u) / 2) = 2 ^ u / (2 * Real.sqrt 2) := by
    rw [show (-1 - (1 - 2 * u) / 2 : ℝ) = u + (-1) + (-(1 / 2)) by ring, Real.rpow_add two_pos,
      Real.rpow_add two_pos, Real.rpow_neg (by norm_num), Real.rpow_one,
      Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    field_simp
  rw [hG1, hG2, h2, hs2]
  have hu2 : u ≠ 0 := hu0.ne'
  set P := Real.sqrt Real.pi with hP
  have hP2 : Real.pi = P ^ 2 := by rw [hP, Real.sq_sqrt Real.pi_pos.le]
  clear_value P
  rw [hP2]
  field_simp
  ring

/-! ### The exact `Q` -/

theorem tendsto_one_sub_two_mul_nhdsLT :
    Tendsto (fun u : ℝ => 1 - 2 * u) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Tendsto (fun u : ℝ => 1 - 2 * u) (𝓝 0) (𝓝 (1 - 2 * 0)) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with u hu
    change 1 - 2 * u < 1
    have : (0 : ℝ) < u := hu
    linarith

/-- ★★★ **The depth-three residual constant**: `Q = (c² + 5π²/6)/(4√(2π))`. -/
theorem depthThreeQint_eq :
    depthThreeQint = (depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / (4 * Real.sqrt (2 * Real.pi)) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h1 : Tendsto (fun u : ℝ => depthThreeMellin (1 - 2 * u) - depthThreePoles (1 - 2 * u))
      (𝓝[>] (0 : ℝ)) (𝓝 depthThreeQint) :=
    tendsto_depthThree_mellin_sub_poles.comp tendsto_one_sub_two_mul_nhdsLT
  have h2 : Tendsto (fun u : ℝ => depthThreeMellin (1 - 2 * u) - depthThreePoles (1 - 2 * u))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / 2 / (2 * Real.sqrt (2 * Real.pi)))) := by
    have := tendsto_gammaJetF_second.div_const (2 * Real.sqrt (2 * Real.pi))
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    rw [depthThreeMellin_sub_poles_eq hu.1 hu.2]
    have hu0 : u ≠ 0 := hu.1.ne'
    field_simp
  rw [tendsto_nhds_unique h1 h2]
  field_simp
  ring

/-! ### The depth-three constant `C₃` -/

/-- ★★★ **The depth-three constant in closed form**: `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)`. -/
theorem depthThreeConst_eq :
    depthThreeConst =
      ((4 * Real.log 2 - 2 * Real.eulerMascheroniConstant) ^ 2 + Real.pi ^ 2) / (4 * Real.pi) := by
  unfold depthThreeConst
  rw [gaussJlog_eq, depthThreeQint_eq]
  unfold gaussR₀ depthThreeC
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  set S := Real.sqrt (2 * Real.pi) with hS
  have hpi : Real.pi = S ^ 2 / 2 := by rw [hS, Real.sq_sqrt (by positivity)]; ring
  clear_value S
  rw [hpi]
  field_simp
  ring

end Grammar
