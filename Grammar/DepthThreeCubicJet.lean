/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeGammaJet
import Grammar.DepthMellinClosedForm
import Grammar.PolynomialEngineSubleading

/-!
# The depth-three residual mass as a cubic Gamma jet

The regularised depth-three Mellin transform is `M₃(1 − 2u) = H₃(u)/(4πu³)` with the analytic
`H₃(u) = 2^{2u} Γ(½ − u) Γ(1 + u)³/√π`, `H₃(0) = 1` (Astra round 22).  Its cubic jet
`H₃(u) = 1 + c₁u + c₂u² + c₃u³ + o(u³)` is computed by three derivatives of the product
(★★ `tendsto_gammaJetH_third`, l'Hôpital twice and the slope limit, as DCXLIII one order up),
with `c₁ = 4 log 2 − 2γ`, `c₂ = (c₁² + π²)/2` (the known Gamma data at `½` and `1`) and `c₃`
explicit in the two third-derivative symbols `Γ'''(½)`, `Γ'''(1)` (`gammaThirdHalf`,
`gammaThirdOne`, the real parts of the complex third derivatives; their identification with
`ζ(3)` is a derivation).  Matching with DCLXX's finite part at depth three
(`c₁, c₂` reproduce `B₃`, `C₃`) gives ★★★ `residualMass_three_eq_jet : Q₃ = c₃/(4π)`, hence
`depthFourQint` and `D₄ = (enginePoly 4)₀` in closed form modulo the third derivatives
(`depthFourQint_eq_jet`).  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

/-! ### Third derivatives of `Γ` -/

theorem hasDerivAt_deriv_deriv_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv (deriv Complex.Gamma)) (deriv (deriv (deriv Complex.Gamma)) z) z :=
  (analyticAt_Gamma_of_re_pos hz).deriv.deriv.differentiableAt.hasDerivAt

/-- `Γ'''(1)` (real part of the complex third derivative). -/
noncomputable def gammaThirdOne : ℝ := (deriv (deriv (deriv Complex.Gamma)) 1).re

/-- `Γ'''(½)` (real part of the complex third derivative). -/
noncomputable def gammaThirdHalf : ℝ := (deriv (deriv (deriv Complex.Gamma)) (1 / 2)).re

/-! ### The jet function and its first two derivatives -/

/-- `H(w) = 2^{2w} Γ(½ − w) Γ(1 + w)³` (without the `1/√π`). -/
noncomputable def cubicH (w : ℂ) : ℂ :=
  (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 3

/-- `H'(w)` by the product rule. -/
noncomputable def cubicH' (w : ℂ) : ℂ :=
  2 * Complex.log 2 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 3 +
    (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) ^ 3 +
    3 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 *
      deriv Complex.Gamma (1 + w)

/-- `H''(w)` by the product rule. -/
noncomputable def cubicH'' (w : ℂ) : ℂ :=
  (2 * Complex.log 2) ^ 2 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 3 +
    2 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) *
      Complex.Gamma (1 + w) ^ 3 +
    6 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2 * deriv Complex.Gamma (1 + w) +
    (2 : ℂ) ^ (2 * w) * deriv (deriv Complex.Gamma) (1 / 2 - w) * Complex.Gamma (1 + w) ^ 3 +
    6 * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) ^ 2 *
      deriv Complex.Gamma (1 + w) +
    6 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) *
      deriv Complex.Gamma (1 + w) ^ 2 +
    3 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 *
      deriv (deriv Complex.Gamma) (1 + w)

theorem hasDerivAt_two_cpow_two_mul (w : ℂ) :
    HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (2 * w)) ((2 : ℂ) ^ (2 * w) * (2 * Complex.log 2)) w := by
  have h := (hasDerivAt_two_cpow (2 * w)).comp w ((hasDerivAt_id' (x := w)).const_mul 2)
  simp only [Function.comp_def, mul_one] at h
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_cB {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 - w)) (-deriv Complex.Gamma (1 / 2 - w)) w :=
  (hasDerivAt_Gamma_of_re_pos (re_half_sub_pos hw2)).comp_const_sub (1 / 2) w

theorem hasDerivAt_cB' {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => -deriv Complex.Gamma (1 / 2 - w))
      (deriv (deriv Complex.Gamma) (1 / 2 - w)) w := by
  refine (((hasDerivAt_deriv_Gamma_of_re_pos (re_half_sub_pos hw2)).comp_const_sub (1 / 2)
    w).neg).congr_deriv ?_
  ring

theorem hasDerivAt_cB'' {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (1 / 2 - w))
      (-deriv (deriv (deriv Complex.Gamma)) (1 / 2 - w)) w :=
  (hasDerivAt_deriv_deriv_Gamma_of_re_pos (re_half_sub_pos hw2)).comp_const_sub (1 / 2) w

theorem hasDerivAt_cC {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w)) (deriv Complex.Gamma (1 + w)) w :=
  (hasDerivAt_Gamma_of_re_pos (re_one_add_pos hw1)).comp_const_add 1 w

theorem hasDerivAt_cC' {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => deriv Complex.Gamma (1 + w)) (deriv (deriv Complex.Gamma) (1 + w)) w :=
  (hasDerivAt_deriv_Gamma_of_re_pos (re_one_add_pos hw1)).comp_const_add 1 w

theorem hasDerivAt_cC'' {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (1 + w))
      (deriv (deriv (deriv Complex.Gamma)) (1 + w)) w :=
  (hasDerivAt_deriv_deriv_Gamma_of_re_pos (re_one_add_pos hw1)).comp_const_add 1 w

section Derivatives

variable {w : ℂ} (hw1 : -1 < w.re) (hw2 : w.re < 1 / 2)
include hw1 hw2

/-- `H` is differentiable with derivative `cubicH'`. -/
theorem hasDerivAt_cubicH : HasDerivAt cubicH (cubicH' w) w := by
  have hA := hasDerivAt_two_cpow_two_mul w
  have hB := hasDerivAt_cB hw2
  have hC := hasDerivAt_cC hw1
  have hC3 := hC.pow 3
  have := (hA.mul hB).mul hC3
  unfold cubicH cubicH'
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  norm_num
  ring

/-- `H'` is differentiable with derivative `cubicH''`. -/
theorem hasDerivAt_cubicH' : HasDerivAt cubicH' (cubicH'' w) w := by
  have hA := hasDerivAt_two_cpow_two_mul w
  have hB := hasDerivAt_cB hw2
  have hB' := hasDerivAt_cB' hw2
  have hC := hasDerivAt_cC hw1
  have hC' := hasDerivAt_cC' hw1
  have hC3 := hC.pow 3
  have hC2 := hC.pow 2
  have hT1 := (((hA.const_mul (2 * Complex.log 2)).mul hB).mul hC3)
  have hT2 := ((hA.mul hB').mul hC3)
  have hT3 := ((((hA.const_mul 3).mul hB).mul hC2).mul hC')
  have := (hT1.add hT2).add hT3
  unfold cubicH' cubicH''
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  norm_num
  ring

/-- `H''` is differentiable; its derivative at `w` (used only at `w = 0`). -/
theorem hasDerivAt_cubicH'' : HasDerivAt cubicH''
    ((2 * Complex.log 2) ^ 3 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
        Complex.Gamma (1 + w) ^ 3 +
      3 * (2 * Complex.log 2) ^ 2 * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) *
        Complex.Gamma (1 + w) ^ 3 +
      9 * (2 * Complex.log 2) ^ 2 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
        Complex.Gamma (1 + w) ^ 2 * deriv Complex.Gamma (1 + w) +
      3 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * deriv (deriv Complex.Gamma) (1 / 2 - w) *
        Complex.Gamma (1 + w) ^ 3 +
      18 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) *
        Complex.Gamma (1 + w) ^ 2 * deriv Complex.Gamma (1 + w) +
      18 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
        Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w) ^ 2 +
      9 * (2 * Complex.log 2) * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
        Complex.Gamma (1 + w) ^ 2 * deriv (deriv Complex.Gamma) (1 + w) +
      (2 : ℂ) ^ (2 * w) * (-deriv (deriv (deriv Complex.Gamma)) (1 / 2 - w)) *
        Complex.Gamma (1 + w) ^ 3 +
      9 * (2 : ℂ) ^ (2 * w) * deriv (deriv Complex.Gamma) (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 *
        deriv Complex.Gamma (1 + w) +
      18 * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) *
        deriv Complex.Gamma (1 + w) ^ 2 +
      9 * (2 : ℂ) ^ (2 * w) * (-deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) ^ 2 *
        deriv (deriv Complex.Gamma) (1 + w) +
      6 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * deriv Complex.Gamma (1 + w) ^ 3 +
      18 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) *
        deriv Complex.Gamma (1 + w) * deriv (deriv Complex.Gamma) (1 + w) +
      3 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 *
        deriv (deriv (deriv Complex.Gamma)) (1 + w)) w := by
  have hA := hasDerivAt_two_cpow_two_mul w
  have hB := hasDerivAt_cB hw2
  have hB' := hasDerivAt_cB' hw2
  have hB'' := hasDerivAt_cB'' hw2
  have hC := hasDerivAt_cC hw1
  have hC' := hasDerivAt_cC' hw1
  have hC'' := hasDerivAt_cC'' hw1
  have hC3 := hC.pow 3
  have hC2 := hC.pow 2
  have hC'2 := hC'.pow 2
  have hT1 := (((hA.const_mul ((2 * Complex.log 2) ^ 2)).mul hB).mul hC3)
  have hT2 := (((hA.const_mul (2 * (2 * Complex.log 2))).mul hB').mul hC3)
  have hT3 := ((((hA.const_mul (6 * (2 * Complex.log 2))).mul hB).mul hC2).mul hC')
  have hT4 := ((hA.mul hB'').mul hC3)
  have hT5 := ((((hA.const_mul 6).mul hB').mul hC2).mul hC')
  have hT6 := ((((hA.const_mul 6).mul hB).mul hC).mul hC'2)
  have hT7 := ((((hA.const_mul 3).mul hB).mul hC2).mul hC'')
  have := (((((hT1.add hT2).add hT3).add hT4).add hT5).add hT6).add hT7
  unfold cubicH''
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply]
  norm_num
  ring

end Derivatives

/-! ### The values at `0` -/

theorem cubicH_zero : cubicH 0 = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  unfold cubicH
  rw [mul_zero, Complex.cpow_zero, sub_zero, add_zero, Gamma_one_half_ofReal, Complex.Gamma_one]
  ring

/-- `c₁ = 4 log 2 − 2γ`. -/
noncomputable def depthThreeJetLinear : ℝ := 4 * Real.log 2 - 2 * Real.eulerMascheroniConstant

/-- `c₂ = (c₁² + π²)/2`. -/
noncomputable def depthThreeJetQuadratic : ℝ := (depthThreeJetLinear ^ 2 + Real.pi ^ 2) / 2

/-- `6c₃√π = √π[k³ + 3k²p − 9k²γ + 3k(p² + π²/2) − 18kpγ + 18kγ² + 9kq − 9γ(p² + π²/2) + 18pγ²
+ 9pq − 6γ³ − 18γq] − Γ⁽³⁾(½) + 3√π Γ⁽³⁾(1)`, `k = 2 log 2`, `p = γ + 2 log 2`, `q = γ² + π²/6`. -/
noncomputable def depthThreeJetCubic : ℝ :=
  (((2 * Real.log 2) ^ 3 +
    3 * (2 * Real.log 2) ^ 2 * (Real.eulerMascheroniConstant + 2 * Real.log 2) -
    9 * (2 * Real.log 2) ^ 2 * Real.eulerMascheroniConstant +
    3 * (2 * Real.log 2) * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) -
    18 * (2 * Real.log 2) * (Real.eulerMascheroniConstant + 2 * Real.log 2) *
      Real.eulerMascheroniConstant +
    18 * (2 * Real.log 2) * Real.eulerMascheroniConstant ^ 2 +
    9 * (2 * Real.log 2) * (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) -
    9 * Real.eulerMascheroniConstant *
      ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) +
    18 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.eulerMascheroniConstant ^ 2 +
    9 * (Real.eulerMascheroniConstant + 2 * Real.log 2) *
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) -
    6 * Real.eulerMascheroniConstant ^ 3 -
    18 * Real.eulerMascheroniConstant * (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6)) *
      Real.sqrt Real.pi - gammaThirdHalf + 3 * Real.sqrt Real.pi * gammaThirdOne) /
    (6 * Real.sqrt Real.pi)

theorem cubicH'_zero : cubicH' 0 = ((Real.sqrt Real.pi * depthThreeJetLinear : ℝ) : ℂ) := by
  unfold cubicH' depthThreeJetLinear
  rw [mul_zero, Complex.cpow_zero, sub_zero, add_zero, Gamma_one_half_ofReal, Complex.Gamma_one,
    Complex.hasDerivAt_Gamma_one_half.deriv, Complex.hasDerivAt_Gamma_one.deriv]
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [hlog]
  push_cast
  ring

theorem cubicH''_zero :
    cubicH'' 0 = ((Real.sqrt Real.pi * (2 * depthThreeJetQuadratic) : ℝ) : ℂ) := by
  unfold cubicH'' depthThreeJetQuadratic depthThreeJetLinear
  rw [mul_zero, Complex.cpow_zero, sub_zero, add_zero, Gamma_one_half_ofReal, Complex.Gamma_one,
    Complex.hasDerivAt_Gamma_one_half.deriv, Complex.hasDerivAt_Gamma_one.deriv,
    deriv_deriv_Gamma_one_half, deriv_deriv_Gamma_one]
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  have hpi : ((Real.pi : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [hlog]
  push_cast
  rw [hpi]
  ring

/-- The third derivative at `0` in the form `↑a + ↑b · Γ⁽³⁾(1) + ↑c · Γ⁽³⁾(½)`. -/
theorem hasDerivAt_cubicH''_zero' :
    HasDerivAt cubicH''
      (((6 * Real.sqrt Real.pi * depthThreeJetCubic + gammaThirdHalf -
          3 * Real.sqrt Real.pi * gammaThirdOne : ℝ) : ℂ) +
        ((3 * Real.sqrt Real.pi : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) 1 +
        ((-1 : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) (1 / 2)) 0 := by
  have h0 : (0 : ℂ).re < 1 / 2 := by simp
  have h0' : -1 < (0 : ℂ).re := by simp
  refine (hasDerivAt_cubicH'' h0' h0).congr_deriv ?_
  rw [mul_zero, Complex.cpow_zero, sub_zero, add_zero, Gamma_one_half_ofReal, Complex.Gamma_one,
    Complex.hasDerivAt_Gamma_one_half.deriv, Complex.hasDerivAt_Gamma_one.deriv,
    deriv_deriv_Gamma_one_half, deriv_deriv_Gamma_one]
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold depthThreeJetCubic
  rw [hlog]
  push_cast
  field_simp
  ring

/-! ### The real jet and its derivatives -/

/-- `H(u)/√π` as a real function of a real variable. -/
noncomputable def gammaJetH (u : ℝ) : ℝ := (cubicH u).re / Real.sqrt Real.pi

noncomputable def gammaJetH' (u : ℝ) : ℝ := (cubicH' u).re / Real.sqrt Real.pi

noncomputable def gammaJetH'' (u : ℝ) : ℝ := (cubicH'' u).re / Real.sqrt Real.pi

theorem hasDerivAt_gammaJetH {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetH (gammaJetH' u) u :=
  ((hasDerivAt_cubicH (by simpa using hu1) (by simpa using hu2)).real_of_complex).div_const _

theorem hasDerivAt_gammaJetH' {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetH' (gammaJetH'' u) u :=
  ((hasDerivAt_cubicH' (by simpa using hu1) (by simpa using hu2)).real_of_complex).div_const _

theorem hasDerivAt_gammaJetH''_zero : HasDerivAt gammaJetH'' (6 * depthThreeJetCubic) 0 := by
  have h : HasDerivAt cubicH'' (((6 * Real.sqrt Real.pi * depthThreeJetCubic + gammaThirdHalf -
      3 * Real.sqrt Real.pi * gammaThirdOne : ℝ) : ℂ) +
        ((3 * Real.sqrt Real.pi : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) 1 +
        ((-1 : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) (1 / 2)) ((0 : ℝ) : ℂ) := by
    simpa using hasDerivAt_cubicH''_zero'
  have h2 := (h.real_of_complex).div_const (Real.sqrt Real.pi)
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  refine h2.congr_deriv ?_
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  unfold gammaThirdOne gammaThirdHalf
  field_simp
  ring

theorem gammaJetH_zero : gammaJetH 0 = 1 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [gammaJetH, Complex.ofReal_zero, cubicH_zero, Complex.ofReal_re, div_self hs.ne']

theorem gammaJetH'_zero : gammaJetH' 0 = depthThreeJetLinear := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [gammaJetH', Complex.ofReal_zero, cubicH'_zero, Complex.ofReal_re]
  field_simp

theorem gammaJetH''_zero : gammaJetH'' 0 = 2 * depthThreeJetQuadratic := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [gammaJetH'', Complex.ofReal_zero, cubicH''_zero, Complex.ofReal_re]
  field_simp

/-! ### The cubic jet by l'Hôpital -/

/-- ★★ **The cubic jet**: `(H(u) − 1 − c₁u − c₂u²)/u³ → c₃` as `u → 0⁺`. -/
theorem tendsto_gammaJetH_third :
    Tendsto (fun u : ℝ => (gammaJetH u - 1 - depthThreeJetLinear * u -
      depthThreeJetQuadratic * u ^ 2) / u ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 depthThreeJetCubic) := by
  have hmem : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hinner : Tendsto (fun u : ℝ => (gammaJetH'' u - 2 * depthThreeJetQuadratic) / (6 * u))
      (𝓝[>] (0 : ℝ)) (𝓝 depthThreeJetCubic) := by
    have h := hasDerivAt_gammaJetH''_zero.tendsto_slope_zero_right
    have h2 := h.div_const 6
    rw [show 6 * depthThreeJetCubic / 6 = depthThreeJetCubic by ring] at h2
    refine h2.congr' ?_
    filter_upwards [hmem] with u hu
    rw [zero_add, gammaJetH''_zero]
    have hu0 : u ≠ 0 := hu.1.ne'
    simp only [smul_eq_mul]
    field_simp
  have hmid : Tendsto (fun u : ℝ => (gammaJetH' u - depthThreeJetLinear -
      2 * depthThreeJetQuadratic * u) / (3 * u ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 depthThreeJetCubic) := by
    refine HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun u => gammaJetH'' u - 2 * depthThreeJetQuadratic)
      (g' := fun u => 6 * u) ?_ ?_ ?_ ?_ ?_ hinner
    · filter_upwards [hmem] with u hu
      have h2 : HasDerivAt (fun u : ℝ => 2 * depthThreeJetQuadratic * u)
          (2 * depthThreeJetQuadratic) u := by
        simpa using (hasDerivAt_id' (x := u)).const_mul (2 * depthThreeJetQuadratic)
      exact ((hasDerivAt_gammaJetH' (by linarith [hu.1]) hu.2).sub_const _).sub h2
    · refine Eventually.of_forall fun u => ?_
      have h : HasDerivAt (fun u : ℝ => 3 * u ^ 2) (3 * (((2 : ℕ) : ℝ) * u ^ (2 - 1) * 1)) u :=
        ((hasDerivAt_id' (x := u)).pow 2).const_mul 3
      refine h.congr_deriv ?_
      norm_num
      ring
    · filter_upwards [hmem] with u hu
      have := hu.1; positivity
    · have hc : ContinuousAt gammaJetH' 0 :=
        (hasDerivAt_gammaJetH' (by norm_num) (by norm_num)).continuousAt
      have := ((hc.tendsto.sub_const depthThreeJetLinear).sub
        (tendsto_id.const_mul (2 * depthThreeJetQuadratic))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [gammaJetH'_zero] using this
    · have : Tendsto (fun u : ℝ => 3 * u ^ 2) (𝓝 0) (𝓝 (3 * (0 : ℝ) ^ 2)) :=
        ((continuous_pow 2).tendsto 0).const_mul 3
      simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  refine HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun u => gammaJetH' u - depthThreeJetLinear - 2 * depthThreeJetQuadratic * u)
    (g' := fun u => 3 * u ^ 2) ?_ ?_ ?_ ?_ ?_ hmid
  · filter_upwards [hmem] with u hu
    have h1 : HasDerivAt (fun u : ℝ => depthThreeJetLinear * u) depthThreeJetLinear u := by
      simpa using (hasDerivAt_id' (x := u)).const_mul depthThreeJetLinear
    have h2 : HasDerivAt (fun u : ℝ => depthThreeJetQuadratic * u ^ 2)
        (2 * depthThreeJetQuadratic * u) u := by
      have := ((hasDerivAt_id' (x := u)).pow 2).const_mul depthThreeJetQuadratic
      refine this.congr_deriv ?_
      norm_num
      ring
    exact (((hasDerivAt_gammaJetH (by linarith [hu.1]) hu.2).sub_const 1).sub h1).sub h2
  · refine Eventually.of_forall fun u => ?_
    have h : HasDerivAt (fun u : ℝ => u ^ 3) (((3 : ℕ) : ℝ) * u ^ (3 - 1) * 1) u :=
      (hasDerivAt_id' (x := u)).pow 3
    refine h.congr_deriv ?_
    norm_num
  · filter_upwards [hmem] with u hu
    have := hu.1; positivity
  · have hc : ContinuousAt gammaJetH 0 :=
      (hasDerivAt_gammaJetH (by norm_num) (by norm_num)).continuousAt
    have := (((hc.tendsto.sub_const 1).sub (tendsto_id.const_mul depthThreeJetLinear)).sub
      ((tendsto_id.pow 2).const_mul depthThreeJetQuadratic)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [gammaJetH_zero] using this
  · have : Tendsto (fun u : ℝ => u ^ 3) (𝓝 0) (𝓝 ((0 : ℝ) ^ 3)) := (continuous_pow 3).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

/-! ### The finite part at depth three -/

theorem coeff_depthThreePoly_zero' : depthThreePoly.coeff 0 = depthThreeConst := by
  simp only [depthThreePoly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

theorem coeff_depthThreePoly_one :
    depthThreePoly.coeff 1 = (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi := by
  simp only [depthThreePoly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

theorem coeff_depthThreePoly_two : depthThreePoly.coeff 2 = 1 / (4 * Real.pi) := by
  simp only [depthThreePoly, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

/-- The depth-three pole sum at `z = 1 − 2u`: `1/(4πu³) + c₁/(4πu²) + c₂/(4πu)`. -/
theorem depthThreePoles_sum_eq {u : ℝ} (hu : u ≠ 0) :
    ∑ k : Fin ((enginePoly 3).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly 3).coeff k) *
      ((k : ℕ).factorial : ℝ) / (1 - (1 - 2 * u)) ^ ((k : ℕ) + 1) =
      (1 + depthThreeJetLinear * u + depthThreeJetQuadratic * u ^ 2) / (4 * Real.pi * u ^ 3) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (2 ^ k * (enginePoly 3).coeff k) *
    (k.factorial : ℝ) / (1 - (1 - 2 * u)) ^ (k + 1)), enginePoly_three, natDegree_depthThreePoly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_depthThreePoly_zero',
    coeff_depthThreePoly_one, coeff_depthThreePoly_two, depthThreeConst_eq, Nat.factorial_zero,
    Nat.factorial_one, Nat.factorial_two, pow_zero, pow_one]
  unfold depthThreeJetQuadratic depthThreeJetLinear
  have hpi : 0 < Real.pi := Real.pi_pos
  push_cast
  field_simp
  ring

/-- The closed Mellin form at depth three at `z = 1 − 2u` is `H(u)/(4πu³)`. -/
theorem depthThreeClosed_eq {u : ℝ} (hu0 : 0 < u) :
    ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ 2 * Real.Gamma ((1 - 2 * u) / 2) *
      Real.Gamma ((1 - (1 - 2 * u)) / 2) ^ (2 + 1) / (2 * Real.sqrt Real.pi ^ (2 + 1)) =
      gammaJetH u / (4 * Real.pi * u ^ 3) := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  simp only [show (2 : ℕ) + 1 = 3 from rfl]
  have hre : (cubicH u).re =
      (2 : ℝ) ^ (2 * u) * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ 3 := by
    unfold cubicH
    rw [show (1 / 2 : ℂ) - (u : ℂ) = ((1 / 2 - u : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring,
      show (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) by push_cast; ring,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num),
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hΓ : Real.Gamma ((1 - (1 - 2 * u)) / 2) = Real.Gamma (1 + u) / u := by
    rw [show (1 - (1 - 2 * u)) / 2 = u by ring, add_comm, Real.Gamma_add_one hu0.ne']
    field_simp
  have h2 : ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ 2 = (2 : ℝ) ^ (2 * u) / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), show (-(1 - 2 * u) / 2 * ((2 : ℕ) : ℝ))
      = 2 * u - 1 by push_cast; ring, Real.rpow_sub_one two_ne_zero]
  have hpi3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [h2, show (1 - 2 * u) / 2 = 1 / 2 - u by ring, hΓ, hpi3, gammaJetH, hre]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu' : u ≠ 0 := hu0.ne'
  field_simp
  ring

/-- ★★★ **The depth-three residual mass is the cubic jet coefficient**: `Q₃ = c₃/(4π)`. -/
theorem residualMass_three_eq_jet :
    residualMass 3 (enginePoly 3) = depthThreeJetCubic / (4 * Real.pi) := by
  have h1 := (tendsto_gammaProduct_sub_poles 2 (by norm_num)).comp tendsto_one_sub_two_mul_nhdsLT
  have h2 : Tendsto (fun u : ℝ => (gammaJetH u - 1 - depthThreeJetLinear * u -
      depthThreeJetQuadratic * u ^ 2) / u ^ 3 / (4 * Real.pi)) (𝓝[>] (0 : ℝ))
      (𝓝 (depthThreeJetCubic / (4 * Real.pi))) := tendsto_gammaJetH_third.div_const _
  have h3 : Tendsto (fun u : ℝ => (gammaJetH u - 1 - depthThreeJetLinear * u -
      depthThreeJetQuadratic * u ^ 2) / u ^ 3 / (4 * Real.pi)) (𝓝[>] (0 : ℝ))
      (𝓝 (residualMass (2 + 1) (enginePoly (2 + 1)))) := by
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    simp only [Function.comp_apply]
    rw [depthThreePoles_sum_eq hu.1.ne', depthThreeClosed_eq hu.1]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hu0 : u ≠ 0 := hu.1.ne'
    field_simp
    ring
  exact tendsto_nhds_unique h3 h2

/-- `Q₃ = depthFourQint` in closed form modulo `Γ⁽³⁾(½)`, `Γ⁽³⁾(1)`. -/
theorem depthFourQint_eq_jet : depthFourQint = depthThreeJetCubic / (4 * Real.pi) := by
  rw [← residualMass_three, ← enginePoly_three, residualMass_three_eq_jet]

end Grammar
