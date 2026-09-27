/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaSecondDerivOne
import Grammar.DepthThreeMellinBridge

/-!
# The regularised Gamma jet for the depth-three constant

`F(u) = 2^u Γ(½ − u) Γ(1 + u)² / √π` is the regular factor of the Mellin transform of the depth-two
Gaussian DLN at `z = 1 − 2u`: `M(1 − 2u) = F(u)/(2 s u²)` (next unit).  Here

  `F(0) = 1`,  `F'(0) = c = 3 log 2 − γ`,  `F''(0) = c² + 5π²/6`,

from `Γ(½) = √π`, `Γ(1) = 1`, `Γ'(½) = −√π(γ + 2 log 2)`, `Γ'(1) = −γ`, DCVIII's
`Γ''(½) = √π((γ + 2 log 2)² + π²/2)` and DCXXXVIII's `Γ''(1) = γ² + π²/6`, so by l'Hôpital

  `(F(u) − 1 − c u)/u² → (c² + 5π²/6)/2` as `u → 0⁺`   (★★★ `tendsto_depthThreeF_second`).

The complex function `jetF` carries the derivatives (through DCVIII's `hasDerivAt_Gamma_of_re_pos`
and `hasDerivAt_deriv_Gamma_of_re_pos`); the real `gammaJetF u = (jetF u).re` inherits them by
`HasDerivAt.real_of_complex` (examples_slop §2; Astra round-13 target 3).  Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

/-- `F(w) = 2^w Γ(½ − w) Γ(1 + w)² / √π`. -/
noncomputable def jetF (w : ℂ) : ℂ :=
  (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 /
    ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- `F'(w)` by the product rule. -/
noncomputable def jetF' (w : ℂ) : ℂ :=
  ((2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2 +
    (2 : ℂ) ^ w * (-deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) ^ 2 +
    (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) *
      (2 * Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w))) /
    ((Real.sqrt Real.pi : ℝ) : ℂ)

theorem re_half_sub_pos {w : ℂ} (hw : w.re < 1 / 2) : 0 < (1 / 2 - w).re := by
  have : ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.sub_re, Complex.ofReal_re]
  rw [this]
  linarith

theorem re_one_add_pos {w : ℂ} (hw : -1 < w.re) : 0 < (1 + w).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem hasDerivAt_two_cpow (w : ℂ) :
    HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w) ((2 : ℂ) ^ w * Complex.log 2) w := by
  have := (hasDerivAt_id' (x := w)).const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  simpa using this

/-- `F` is differentiable for `−1 < Re w < ½`, with derivative `jetF'`. -/
theorem hasDerivAt_jetF {w : ℂ} (hw1 : -1 < w.re) (hw2 : w.re < 1 / 2) :
    HasDerivAt jetF (jetF' w) w := by
  have hA := hasDerivAt_two_cpow w
  have hG1 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 - w))
      (-deriv Complex.Gamma (1 / 2 - w)) w :=
    (hasDerivAt_Gamma_of_re_pos (re_half_sub_pos hw2)).comp_const_sub (1 / 2) w
  have hG2 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w)) (deriv Complex.Gamma (1 + w)) w :=
    (hasDerivAt_Gamma_of_re_pos (re_one_add_pos hw1)).comp_const_add 1 w
  have hG2sq : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w) ^ 2)
      (((2 : ℕ) : ℂ) * Complex.Gamma (1 + w) ^ (2 - 1) * deriv Complex.Gamma (1 + w)) w :=
    hG2.pow 2
  have hAG : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w))
      ((2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) +
        (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w)) w := hA.mul hG1
  have hAGG : HasDerivAt
      (fun w : ℂ => (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) * Complex.Gamma (1 + w) ^ 2)
      (((2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) +
        (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w)) * Complex.Gamma (1 + w) ^ 2 +
        (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) *
          (((2 : ℕ) : ℂ) * Complex.Gamma (1 + w) ^ (2 - 1) * deriv Complex.Gamma (1 + w))) w :=
    hAG.mul hG2sq
  have := hAGG.div_const ((Real.sqrt Real.pi : ℝ) : ℂ)
  unfold jetF jetF'
  refine this.congr_deriv ?_
  norm_num
  ring

/-- The derivative of `jetF'` at `0`, expressed through the Gamma data. -/
theorem hasDerivAt_jetF'_zero :
    HasDerivAt jetF'
      ((Complex.log 2 * (Complex.log 2 * Complex.Gamma (1 / 2) * Complex.Gamma 1 ^ 2 +
          (-deriv Complex.Gamma (1 / 2)) * Complex.Gamma 1 ^ 2 +
          Complex.Gamma (1 / 2) * (2 * Complex.Gamma 1 * deriv Complex.Gamma 1)) +
        (Complex.log 2 * (-deriv Complex.Gamma (1 / 2)) * Complex.Gamma 1 ^ 2 +
          deriv (deriv Complex.Gamma) (1 / 2) * Complex.Gamma 1 ^ 2 +
          (-deriv Complex.Gamma (1 / 2)) * (2 * Complex.Gamma 1 * deriv Complex.Gamma 1)) +
        (Complex.log 2 * Complex.Gamma (1 / 2) * (2 * Complex.Gamma 1 * deriv Complex.Gamma 1) +
          (-deriv Complex.Gamma (1 / 2)) * (2 * Complex.Gamma 1 * deriv Complex.Gamma 1) +
          Complex.Gamma (1 / 2) * (2 * (deriv Complex.Gamma 1 * deriv Complex.Gamma 1 +
            Complex.Gamma 1 * deriv (deriv Complex.Gamma) 1)))) /
        ((Real.sqrt Real.pi : ℝ) : ℂ)) 0 := by
  have h0 : (0 : ℂ).re < 1 / 2 := by simp
  have h0' : -1 < (0 : ℂ).re := by simp
  have hA := hasDerivAt_two_cpow 0
  have hG1 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 - w))
      (-deriv Complex.Gamma (1 / 2 - 0)) 0 :=
    (hasDerivAt_Gamma_of_re_pos (re_half_sub_pos h0)).comp_const_sub (1 / 2) 0
  have hG2 : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w)) (deriv Complex.Gamma (1 + 0)) 0 :=
    (hasDerivAt_Gamma_of_re_pos (re_one_add_pos h0')).comp_const_add 1 0
  have hD1' : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (1 / 2 - w))
      (-deriv (deriv Complex.Gamma) (1 / 2 - 0)) 0 :=
    (hasDerivAt_deriv_Gamma_of_re_pos (re_half_sub_pos h0)).comp_const_sub (1 / 2) 0
  have hD1 : HasDerivAt (fun w : ℂ => -deriv Complex.Gamma (1 / 2 - w))
      (-(-deriv (deriv Complex.Gamma) (1 / 2 - 0))) 0 := hD1'.neg
  have hD2 : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (1 + w))
      (deriv (deriv Complex.Gamma) (1 + 0)) 0 :=
    (hasDerivAt_deriv_Gamma_of_re_pos (re_one_add_pos h0')).comp_const_add 1 0
  have hG2sq : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w) ^ 2)
      (((2 : ℕ) : ℂ) * Complex.Gamma (1 + 0) ^ (2 - 1) * deriv Complex.Gamma (1 + 0)) 0 :=
    hG2.pow 2
  have hGD : HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w))
      (deriv Complex.Gamma (1 + 0) * deriv Complex.Gamma (1 + 0) +
        Complex.Gamma (1 + 0) * deriv (deriv Complex.Gamma) (1 + 0)) 0 := hG2.mul hD2
  have hQ : HasDerivAt (fun w : ℂ => 2 * (Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w)))
      (2 * (deriv Complex.Gamma (1 + 0) * deriv Complex.Gamma (1 + 0) +
        Complex.Gamma (1 + 0) * deriv (deriv Complex.Gamma) (1 + 0))) 0 := hGD.const_mul 2
  have hAl : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.log 2)
      ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.log 2) 0 := hA.mul_const _
  -- T₁ = 2^w log 2 Γ(½−w) Γ(1+w)²
  have hT₁a : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w))
      ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.log 2 * Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * -deriv Complex.Gamma (1 / 2 - 0)) 0 := hAl.mul hG1
  have hT₁ : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2)
      (((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.log 2 * Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * -deriv Complex.Gamma (1 / 2 - 0)) *
          Complex.Gamma (1 + 0) ^ 2 +
        (2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.Gamma (1 / 2 - 0) *
          (((2 : ℕ) : ℂ) * Complex.Gamma (1 + 0) ^ (2 - 1) * deriv Complex.Gamma (1 + 0))) 0 :=
    hT₁a.mul hG2sq
  -- T₂ = 2^w (−Γ'(½−w)) Γ(1+w)²
  have hT₂a : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w))
      ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * -deriv Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * -(-deriv (deriv Complex.Gamma) (1 / 2 - 0))) 0 := hA.mul hD1
  have hT₂ : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2)
      (((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * -deriv Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * -(-deriv (deriv Complex.Gamma) (1 / 2 - 0))) *
          Complex.Gamma (1 + 0) ^ 2 +
        (2 : ℂ) ^ (0 : ℂ) * -deriv Complex.Gamma (1 / 2 - 0) *
          (((2 : ℕ) : ℂ) * Complex.Gamma (1 + 0) ^ (2 - 1) * deriv Complex.Gamma (1 + 0))) 0 :=
    hT₂a.mul hG2sq
  -- T₃ = 2^w Γ(½−w) (2 Γ(1+w) Γ'(1+w))
  have hT₃a : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w))
      ((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * -deriv Complex.Gamma (1 / 2 - 0)) 0 := hA.mul hG1
  have hT₃ : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) *
      (2 * (Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w))))
      (((2 : ℂ) ^ (0 : ℂ) * Complex.log 2 * Complex.Gamma (1 / 2 - 0) +
        (2 : ℂ) ^ (0 : ℂ) * -deriv Complex.Gamma (1 / 2 - 0)) *
          (2 * (Complex.Gamma (1 + 0) * deriv Complex.Gamma (1 + 0))) +
        (2 : ℂ) ^ (0 : ℂ) * Complex.Gamma (1 / 2 - 0) *
          (2 * (deriv Complex.Gamma (1 + 0) * deriv Complex.Gamma (1 + 0) +
            Complex.Gamma (1 + 0) * deriv (deriv Complex.Gamma) (1 + 0)))) 0 := hT₃a.mul hQ
  have hsum : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2 + (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2 + (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) *
      (2 * (Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w)))) _ 0 := (hT₁.add hT₂).add hT₃
  have := hsum.div_const ((Real.sqrt Real.pi : ℝ) : ℂ)
  have hfun : jetF' = fun w : ℂ => ((2 : ℂ) ^ w * Complex.log 2 * Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2 + (2 : ℂ) ^ w * -deriv Complex.Gamma (1 / 2 - w) *
      Complex.Gamma (1 + w) ^ 2 + (2 : ℂ) ^ w * Complex.Gamma (1 / 2 - w) *
      (2 * (Complex.Gamma (1 + w) * deriv Complex.Gamma (1 + w)))) /
      ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    funext w
    unfold jetF'
    ring
  rw [hfun]
  refine this.congr_deriv ?_
  simp only [sub_zero, add_zero, Complex.cpow_zero]
  norm_num
  ring

/-! ### The values at `0` -/

theorem Gamma_one_half_ofReal : Complex.Gamma (1 / 2) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast
  rfl

theorem jetF_zero : jetF 0 = 1 := by
  unfold jetF
  rw [sub_zero, add_zero, Complex.cpow_zero, Gamma_one_half_ofReal, Complex.Gamma_one]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

theorem jetF'_zero : jetF' 0 = ((depthThreeC : ℝ) : ℂ) := by
  unfold jetF' depthThreeC
  rw [sub_zero, add_zero, Complex.cpow_zero, Gamma_one_half_ofReal, Complex.Gamma_one,
    Complex.hasDerivAt_Gamma_one_half.deriv, Complex.hasDerivAt_Gamma_one.deriv]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [hlog]
  push_cast
  field_simp
  ring

theorem hasDerivAt_jetF'_zero' :
    HasDerivAt jetF' (((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6 : ℝ) : ℂ)) 0 := by
  refine hasDerivAt_jetF'_zero.congr_deriv ?_
  rw [Gamma_one_half_ofReal, Complex.Gamma_one, Complex.hasDerivAt_Gamma_one_half.deriv,
    Complex.hasDerivAt_Gamma_one.deriv, deriv_deriv_Gamma_one_half, deriv_deriv_Gamma_one]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  have hpi : ((Real.pi : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  unfold depthThreeC
  rw [hlog]
  push_cast
  rw [hpi]
  field_simp
  ring

/-! ### The real function and the l'Hôpital limit -/

/-- `F(u) = 2^u Γ(½ − u) Γ(1 + u)²/√π` as a real function (the real part of `jetF`). -/
noncomputable def gammaJetF (u : ℝ) : ℝ := (jetF u).re

/-- `F'(u)` (the real part of `jetF'`). -/
noncomputable def gammaJetF' (u : ℝ) : ℝ := (jetF' u).re

theorem hasDerivAt_depthThreeF {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetF (gammaJetF' u) u :=
  (hasDerivAt_jetF (by simpa using hu1) (by simpa using hu2)).real_of_complex

theorem hasDerivAt_depthThreeF'_zero :
    HasDerivAt gammaJetF' (depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) 0 := by
  have h : HasDerivAt jetF' (((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6 : ℝ) : ℂ)) ((0 : ℝ) : ℂ) := by
    simpa using hasDerivAt_jetF'_zero'
  have := h.real_of_complex
  rw [Complex.ofReal_re] at this
  exact this

theorem depthThreeF_zero : gammaJetF 0 = 1 := by
  simp [gammaJetF, jetF_zero]

theorem gammaJetF'_zero : gammaJetF' 0 = depthThreeC := by
  rw [gammaJetF', Complex.ofReal_zero, jetF'_zero, Complex.ofReal_re]

/-- ★★★ **The regularised jet**: `(F(u) − 1 − c u)/u² → (c² + 5π²/6)/2` as `u → 0⁺`. -/
theorem tendsto_depthThreeF_second :
    Tendsto (fun u : ℝ => (gammaJetF u - 1 - depthThreeC * u) / u ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / 2)) := by
  have hmem : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  refine HasDerivAt.lhopital_zero_nhdsGT (f' := fun u => gammaJetF' u - depthThreeC)
    (g' := fun u => 2 * u) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hmem] with u hu
    have h2 : HasDerivAt (fun u : ℝ => depthThreeC * u) depthThreeC u := by
      simpa using (hasDerivAt_id' (x := u)).const_mul depthThreeC
    exact ((hasDerivAt_depthThreeF (by linarith [hu.1]) hu.2).sub_const 1).sub h2
  · refine Eventually.of_forall fun u => ?_
    have h : HasDerivAt (fun u : ℝ => u ^ 2) (((2 : ℕ) : ℝ) * u ^ (2 - 1) * 1) u :=
      (hasDerivAt_id' (x := u)).pow 2
    refine h.congr_deriv ?_
    norm_num
  · filter_upwards [hmem] with u hu
    linarith [hu.1]
  · have hc : ContinuousAt gammaJetF 0 :=
      (hasDerivAt_depthThreeF (by norm_num) (by norm_num)).continuousAt
    have := ((hc.tendsto.sub_const 1).sub (tendsto_id.const_mul depthThreeC)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [depthThreeF_zero] using this
  · have : Tendsto (fun u : ℝ => u ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  · have h := hasDerivAt_depthThreeF'_zero.tendsto_slope_zero_right
    have h2 := h.div_const 2
    refine h2.congr' ?_
    filter_upwards [hmem] with u hu
    rw [zero_add, gammaJetF'_zero]
    have hu0 : u ≠ 0 := hu.1.ne'
    simp only [smul_eq_mul]
    field_simp

end Grammar
