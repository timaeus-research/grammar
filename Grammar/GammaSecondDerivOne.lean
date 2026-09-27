/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RenormalisedExpIntegral

/-!
# `Γ''(1) = γ² + π²/6`

Legendre's duplication formula `Γ(w)Γ(w + ½) = Γ(2w) 2^{1−2w} √π` (Mathlib
`Complex.Gamma_mul_Gamma_add_half`) differentiated twice at `w = ½`, with `Γ(1) = 1`, `Γ(½) = √π`,
`Γ'(1) = −γ`, `Γ'(½) = −√π(γ + 2 log 2)` (Mathlib) and `Γ''(½) = √π((γ + 2 log 2)² + π²/2)`
(DCVIII),
gives (★★★ `deriv_deriv_Gamma_one`)

  `Γ''(½)·Γ(1) + 2Γ'(½)Γ'(1) + Γ(½)Γ''(1) = √π[4Γ''(1) − 8 log 2·Γ'(1) + 4(log 2)²]`,

hence `Γ''(1) = γ² + π²/6` (the trigamma value `ψ'(1) = π²/6` without a polygamma API), and by the
Mellin machinery of DCVIII at `s = 1` the second Gamma log-moment
`∫₀^∞ e^{−v} log² v dv = γ² + π²/6`
(★★ `integral_exp_neg_log_sq`).  This is the Gamma input of the exact `J = R₀²/2 + π²/48`
(`GaussJlogExact`; Astra round-12 target 2).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The derivative of the duplication product `Γ(w)Γ(w + ½)` on `Re w > 0`. -/
theorem deriv_duplication {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2))
      (deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
        Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2)) z := by
  have h1' : 0 < (z + 1 / 2).re := by simp; linarith
  have hlin : HasDerivAt (fun w : ℂ => w + 1 / 2) 1 z := (hasDerivAt_id z).add_const _
  have hcomp := (hasDerivAt_Gamma_of_re_pos h1').comp z hlin
  have := (hasDerivAt_Gamma_of_re_pos h0).mul hcomp
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

/-- The second derivative of the duplication product at `½`. -/
theorem deriv_deriv_duplication :
    deriv (deriv fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) (1 / 2) =
      deriv (deriv Complex.Gamma) (1 / 2) * Complex.Gamma 1 +
        2 * deriv Complex.Gamma (1 / 2) * deriv Complex.Gamma 1 +
        Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1 := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hev : deriv (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
        Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2) := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (deriv_duplication hz).deriv
  rw [hev.deriv_eq]
  have h1 : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  have hlin : HasDerivAt (fun w : ℂ => w + 1 / 2) 1 (1 / 2) := (hasDerivAt_id _).add_const _
  have hA := hasDerivAt_deriv_Gamma_of_re_pos hhalf
  have hB : HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1 / 2)) (deriv Complex.Gamma 1)
      (1 / 2) := by
    have := (hasDerivAt_Gamma_of_re_pos (z := 1 / 2 + 1 / 2)
      (by rw [h1]; exact hone)).comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [h1] at this
    exact this
  have hC := hasDerivAt_Gamma_of_re_pos hhalf
  have hD : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (w + 1 / 2))
      (deriv (deriv Complex.Gamma) 1) (1 / 2) := by
    have := (hasDerivAt_deriv_Gamma_of_re_pos (z := 1 / 2 + 1 / 2)
      (by rw [h1]; exact hone)).comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [h1] at this
    exact this
  have hDD : HasDerivAt (fun z => deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
      Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2)) _ (1 / 2) := (hA.mul hB).add (hC.mul hD)
  rw [hDD.deriv, h1]
  ring

/-- The derivative of the right side `Γ(2w) 2^{1−2w} √π` on `Re w > 0`. -/
theorem deriv_duplication_rhs {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w : ℂ =>
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ))
      ((deriv Complex.Gamma (2 * z) * 2 * (2 : ℂ) ^ (1 - 2 * z) +
        Complex.Gamma (2 * z) * ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2))) *
          ((Real.sqrt Real.pi : ℝ) : ℂ)) z := by
  have h2 : 0 < (2 * z).re := by simp; linarith
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hG := (hasDerivAt_Gamma_of_re_pos h2).comp z hlin
  have hlin2 : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_sub 1
  have hP := hlin2.const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  have := (hG.mul hP).mul_const ((Real.sqrt Real.pi : ℝ) : ℂ)
  refine this.congr_deriv ?_
  simp only [Function.comp]

/-- The second derivative of the right side at `½`: `√π[4Γ''(1) − 8 log 2 Γ'(1) + 4(log 2)²]`. -/
theorem deriv_deriv_duplication_rhs :
    deriv (deriv fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) *
      ((Real.sqrt Real.pi : ℝ) : ℂ)) (1 / 2) =
      (4 * deriv (deriv Complex.Gamma) 1 - 8 * Complex.log 2 * deriv Complex.Gamma 1 +
        4 * Complex.log 2 ^ 2 * Complex.Gamma 1) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hev : deriv (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) *
      ((Real.sqrt Real.pi : ℝ) : ℂ)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => (deriv Complex.Gamma (2 * z) * 2 * (2 : ℂ) ^ (1 - 2 * z) +
        Complex.Gamma (2 * z) * ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2))) *
          ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (deriv_duplication_rhs hz).deriv
  rw [hev.deriv_eq]
  have h1 : (2 * (1 / 2 : ℂ)) = 1 := by norm_num
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)
  have hlin2 : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)).const_sub 1
  -- the factors at ½
  have hA : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (2 * w))
      (deriv (deriv Complex.Gamma) 1 * 2) (1 / 2) := by
    have := (hasDerivAt_deriv_Gamma_of_re_pos (z := 2 * (1 / 2)) (by rw [h1]; exact hone)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    exact this
  have hP : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
      ((2 : ℂ) ^ (1 - 2 * (1 / 2 : ℂ)) * Complex.log 2 * (-2)) (1 / 2) :=
    hlin2.const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  have hG : HasDerivAt (fun w : ℂ => Complex.Gamma (2 * w)) (deriv Complex.Gamma 1 * 2)
      (1 / 2) := by
    have := (hasDerivAt_Gamma_of_re_pos (z := 2 * (1 / 2)) (by rw [h1]; exact hone)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    exact this
  have hDD : HasDerivAt (fun z : ℂ => (deriv Complex.Gamma (2 * z) * 2 * (2 : ℂ) ^ (1 - 2 * z) +
      Complex.Gamma (2 * z) * ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2))) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)) _ (1 / 2) :=
    (((hA.mul_const 2).mul hP).add
      (hG.mul ((hP.mul_const (Complex.log 2)).mul_const (-2)))).mul_const
      ((Real.sqrt Real.pi : ℝ) : ℂ)
  rw [hDD.deriv, h1, sub_self, Complex.cpow_zero]
  ring

/-- ★★★ **`Γ''(1) = γ² + π²/6`.** -/
theorem deriv_deriv_Gamma_one :
    deriv (deriv Complex.Gamma) 1 =
      ((Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  have hdup : (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =
      fun w : ℂ =>
        Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    funext w
    exact Complex.Gamma_mul_Gamma_add_half w
  have key := deriv_deriv_duplication
  rw [hdup, deriv_deriv_duplication_rhs] at key
  have hG : Complex.Gamma (1 / 2) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  have hG' : deriv Complex.Gamma (1 / 2) =
      -((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.eulerMascheroniConstant : ℂ) + 2 * Real.log 2) := by
    have := Complex.hasDerivAt_Gamma_one_half.deriv
    rw [this, ← Complex.ofNat_log]
  have hG1 : deriv Complex.Gamma 1 = -(Real.eulerMascheroniConstant : ℂ) :=
    Complex.hasDerivAt_Gamma_one.deriv
  have hG'' := deriv_deriv_Gamma_one_half
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [Complex.Gamma_one, hG, hG', hG1, hG'', hlog] at key
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi : ((Real.pi : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  push_cast at key ⊢
  rw [hpi] at key ⊢
  set S : ℂ := ((Real.sqrt Real.pi : ℝ) : ℂ) with hS
  set g : ℂ := (Real.eulerMascheroniConstant : ℂ) with hg
  set l : ℂ := ((Real.log 2 : ℝ) : ℂ) with hl
  clear_value S g l
  -- key : S((g+2l)² + (S²)²/2) + 2(−S(g+2l))(−g) + S Γ''(1) = (4Γ''(1) − 8l(−g) + 4l²)S
  have e : S * (3 * deriv (deriv Complex.Gamma) 1) = S * (3 * g ^ 2 + (S ^ 2) ^ 2 / 2) := by
    linear_combination key
  have := mul_left_cancel₀ hsp e
  linear_combination this / 3

/-- ★★ **The second Gamma log-moment at `1`**: `∫₀^∞ e^{−v} log² v dv = Γ''(1) = γ² + π²/6`. -/
theorem integral_exp_neg_log_sq :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * (Real.log v) ^ 2 =
      Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 := by
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hev : deriv Complex.Gamma =ᶠ[𝓝 (1 : ℂ)]
      mellin fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ) := by
    filter_upwards [isOpen_re_pos.mem_nhds hone] with z hz
    exact deriv_Gamma_eq_mellin hz
  have h := deriv_deriv_Gamma_one
  rw [hev.deriv_eq, (hasDerivAt_mellin_log_exp hone).deriv] at h
  unfold mellin at h
  have hcast : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) •
      (Real.log t • (Real.log t • ((Real.exp (-t) : ℝ) : ℂ)))) =
      ((∫ v in Ioi (0 : ℝ), Real.exp (-v) * (Real.log v) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [sub_self, Complex.cpow_zero, one_smul]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hcast] at h
  exact_mod_cast h

end Grammar
