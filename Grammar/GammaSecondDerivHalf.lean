/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatDepth
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# `Γ''(½)` and the second Gamma log-moment `H₂`

Two facts complete the depth-three constants of the flat-prior expansion (examples_slop §2,
`Q₂ = (t − ψ)² + π²/2`):

* the reflection formula `Γ(z)Γ(1 − z) = π/sin(πz)` differentiated twice at `z = ½` gives
  `2Γ(½)Γ''(½) − 2Γ'(½)² = π³`, hence, with `Γ(½) = √π` and `Γ'(½) = −√π(γ + 2 log 2)` (Mathlib),

    `Γ''(½) = √π((γ + 2 log 2)² + π²/2)`  (★★★ `deriv_deriv_Gamma_one_half`);

* differentiating the Gamma integral twice under the integral sign (Mathlib's Mellin-derivative
  theorem `mellin_hasDerivAt_of_isBigO_rpow` applied to `e^{−t}` and to `log t · e^{−t}`) identifies

    `H₂ = ∫₀^∞ e^{−x} x^{−1/2} log² x dx = Γ''(½)`  (★★ `gammaLogMoment_two_eq`),

so `gammaLogMoment 2 = √π((γ + 2 log 2)² + π²/2)` (★★★ `gammaLogMoment_two`) and the depth-three
binomial polynomial `depthPoly 2` of `Grammar.CrossingFlatDepth` is explicit (`depthPoly_two`).
Astra round-4 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The reflection formula differentiated twice -/

theorem isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  linarith [this, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `Γ` is analytic at every point of positive real part; in particular `deriv Γ` is
differentiable there. -/
theorem analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (ne_neg_nat_of_re_pos hw)).differentiableWithinAt
  exact hd.analyticAt (isOpen_re_pos.mem_nhds hz)

theorem hasDerivAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z :=
  (Complex.differentiableAt_Gamma z (ne_neg_nat_of_re_pos hz)).hasDerivAt

theorem hasDerivAt_deriv_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv Complex.Gamma) (deriv (deriv Complex.Gamma) z) z :=
  (analyticAt_Gamma_of_re_pos hz).deriv.differentiableAt.hasDerivAt

/-- The derivative of the reflection product on the strip `0 < Re z < 1`. -/
theorem deriv_reflection {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (1 - w))
      (deriv Complex.Gamma z * Complex.Gamma (1 - z) -
        Complex.Gamma z * deriv Complex.Gamma (1 - z)) z := by
  have h1' : 0 < (1 - z).re := by simp; linarith
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hcomp := (hasDerivAt_Gamma_of_re_pos h1').comp z hlin
  have := (hasDerivAt_Gamma_of_re_pos h0).mul hcomp
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

/-- The second derivative of the reflection product at `½`: `2Γ(½)Γ''(½) − 2Γ'(½)²`. -/
theorem deriv_deriv_reflection :
    deriv (deriv fun w => Complex.Gamma w * Complex.Gamma (1 - w)) (1 / 2) =
      2 * Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) (1 / 2) -
        2 * deriv Complex.Gamma (1 / 2) ^ 2 := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    isOpen_re_pos.inter (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
    norm_num
  have hev : deriv (fun w => Complex.Gamma w * Complex.Gamma (1 - w)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => deriv Complex.Gamma z * Complex.Gamma (1 - z) -
        Complex.Gamma z * deriv Complex.Gamma (1 - z) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact (deriv_reflection hz.1 hz.2).deriv
  rw [hev.deriv_eq]
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub 1
  have h1 : (1 - 1 / 2 : ℂ) = 1 / 2 := by norm_num
  -- derivatives of the four factors at ½
  have hA := hasDerivAt_deriv_Gamma_of_re_pos hhalf
  have hB : HasDerivAt (fun w : ℂ => Complex.Gamma (1 - w)) (-deriv Complex.Gamma (1 / 2))
      (1 / 2) := by
    have := (hasDerivAt_Gamma_of_re_pos (z := 1 - 1 / 2) (by rw [h1]; exact hhalf)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    refine this.congr_deriv ?_
    ring
  have hC := hasDerivAt_Gamma_of_re_pos hhalf
  have hD : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (1 - w))
      (-deriv (deriv Complex.Gamma) (1 / 2)) (1 / 2) := by
    have := (hasDerivAt_deriv_Gamma_of_re_pos (z := 1 - 1 / 2) (by rw [h1]; exact hhalf)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    refine this.congr_deriv ?_
    ring
  have hDD : HasDerivAt (fun z => deriv Complex.Gamma z * Complex.Gamma (1 - z) -
      Complex.Gamma z * deriv Complex.Gamma (1 - z)) _ (1 / 2) := (hA.mul hB).sub (hC.mul hD)
  rw [hDD.deriv, h1]
  ring

/-- The derivative of `π/sin(πz)` where `sin(πz) ≠ 0`. -/
theorem hasDerivAt_pi_div_sin {z : ℂ} (hz : Complex.sin (Real.pi * z) ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w))
      (-(Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z) ^ 2) z := by
  have hs : HasDerivAt (fun w : ℂ => Complex.sin (Real.pi * w))
      (Complex.cos (Real.pi * z) * Real.pi) z :=
    (Complex.hasDerivAt_sin (Real.pi * z)).comp z ((hasDerivAt_id z).const_mul (Real.pi : ℂ))
      |>.congr_deriv (by simp)
  have := (hasDerivAt_const z (Real.pi : ℂ)).div hs hz
  refine this.congr_deriv ?_
  ring

/-- The second derivative of `π/sin(πz)` at `½` is `π³`. -/
theorem deriv_deriv_pi_div_sin :
    deriv (deriv fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w)) (1 / 2) =
      (Real.pi : ℂ) ^ 3 := by
  have hsin : Complex.sin (Real.pi * (1 / 2 : ℂ)) = 1 := by
    rw [show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring]
    exact_mod_cast Complex.sin_pi_div_two
  have hcos : Complex.cos (Real.pi * (1 / 2 : ℂ)) = 0 := by
    rw [show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring]
    exact_mod_cast Complex.cos_pi_div_two
  have hcont : ContinuousAt (fun w : ℂ => Complex.sin (Real.pi * w)) (1 / 2) := by fun_prop
  have hne : ∀ᶠ w in 𝓝 (1 / 2 : ℂ), Complex.sin (Real.pi * w) ≠ 0 := by
    have : (1 : ℂ) ≠ 0 := one_ne_zero
    rw [← hsin] at this
    exact hcont.eventually_ne this
  have hev : deriv (fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => -(Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z) ^ 2 := by
    filter_upwards [hne] with z hz
    exact (hasDerivAt_pi_div_sin hz).deriv
  rw [hev.deriv_eq]
  have hs : HasDerivAt (fun w : ℂ => Complex.sin (Real.pi * w))
      (Complex.cos (Real.pi * (1 / 2 : ℂ)) * Real.pi) (1 / 2) :=
    (Complex.hasDerivAt_sin _).comp (1 / 2 : ℂ) ((hasDerivAt_id _).const_mul (Real.pi : ℂ))
      |>.congr_deriv (by simp)
  have hc : HasDerivAt (fun w : ℂ => Complex.cos (Real.pi * w))
      (-Complex.sin (Real.pi * (1 / 2 : ℂ)) * Real.pi) (1 / 2) :=
    (Complex.hasDerivAt_cos _).comp (1 / 2 : ℂ) ((hasDerivAt_id _).const_mul (Real.pi : ℂ))
      |>.congr_deriv (by simp)
  have hsq := hs.pow 2
  have hne' : Complex.sin (Real.pi * (1 / 2 : ℂ)) ^ 2 ≠ 0 := by rw [hsin]; norm_num
  have hDD : HasDerivAt (fun z : ℂ => -(Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * z) /
      Complex.sin (Real.pi * z) ^ 2) _ (1 / 2) := (hc.const_mul (-(Real.pi : ℂ) ^ 2)).div hsq hne'
  rw [hDD.deriv, hsin, hcos]
  simp
  ring

/-- ★★★ **`Γ''(½) = √π((γ + 2 log 2)² + π²/2)`.** -/
theorem deriv_deriv_Gamma_one_half :
    deriv (deriv Complex.Gamma) (1 / 2) =
      ((Real.sqrt Real.pi * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 +
        Real.pi ^ 2 / 2) : ℝ) : ℂ) := by
  have hrefl : (fun w => Complex.Gamma w * Complex.Gamma (1 - w)) =
      fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  have key := deriv_deriv_reflection
  rw [hrefl, deriv_deriv_pi_div_sin] at key
  have hG : Complex.Gamma (1 / 2) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  have hG' : deriv Complex.Gamma (1 / 2) =
      -((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.eulerMascheroniConstant : ℂ) + 2 * Real.log 2) := by
    have := Complex.hasDerivAt_Gamma_one_half.deriv
    rw [this, ← Complex.ofNat_log]
  rw [hG, hG'] at key
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hpi : ((Real.pi : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  push_cast
  rw [hpi] at key ⊢
  set S : ℂ := ((Real.sqrt Real.pi : ℝ) : ℂ) with hS
  set g : ℂ := (Real.eulerMascheroniConstant : ℂ) + 2 * Real.log 2 with hg
  clear_value S g
  have e : 2 * S * deriv (deriv Complex.Gamma) (1 / 2) = (S ^ 2) ^ 3 + 2 * (S * g) ^ 2 := by
    linear_combination (-1 : ℂ) * key
  have h2 : (2 * S) ≠ 0 := mul_ne_zero two_ne_zero hsp
  calc deriv (deriv Complex.Gamma) (1 / 2)
      = (2 * S * deriv (deriv Complex.Gamma) (1 / 2)) / (2 * S) := by field_simp
    _ = ((S ^ 2) ^ 3 + 2 * (S * g) ^ 2) / (2 * S) := by rw [e]
    _ = S * (g ^ 2 + (S ^ 2) ^ 2 / 2) := by field_simp; ring

/-! ### The second Gamma log-moment -/

/-- `e^{−t}` (as a complex function) is `O(t^{−a})` at infinity for every `a`. -/
theorem exp_neg_isBigO_rpow_atTop (a : ℝ) :
    (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop] (· ^ (-a)) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop one_pos (-a)).isBigO
  have h' : (fun t : ℝ => Real.exp (-t)) =O[atTop] (· ^ (-a)) :=
    h.congr_left fun t => by simp
  refine IsBigO.of_norm_left ?_
  refine h'.norm_left.congr_left fun t => ?_
  rw [Complex.norm_real]

/-- `e^{−t}` is `O(t^0)` near `0⁺`. -/
theorem exp_neg_isBigO_rpow_zero :
    (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_zero, Real.rpow_zero,
    norm_one, one_mul]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The first derivative of the Gamma integral as a Mellin transform, differentiated once more:
`d/ds ∫ t^{s−1} log t e^{−t} dt = ∫ t^{s−1} log² t e^{−t} dt` for `Re s > 0`. -/
theorem hasDerivAt_mellin_log_exp {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (mellin fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ))
      (mellin (fun t : ℝ => Real.log t • (Real.log t • ((Real.exp (-t) : ℝ) : ℂ))) s) s := by
  have hf : LocallyIntegrableOn (fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine ContinuousOn.smul (Real.continuousOn_log.mono fun t ht => ?_) (by fun_prop)
    exact ne_of_gt ht
  have htop : (fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop]
      (· ^ (-(s.re + 1))) :=
    isBigO_rpow_top_log_smul (by linarith) (exp_neg_isBigO_rpow_atTop (s.re + 2))
  have hbot : (fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ)) =O[𝓝[>] 0]
      (· ^ (-(s.re / 2))) :=
    isBigO_rpow_zero_log_smul (by linarith) exp_neg_isBigO_rpow_zero
  exact (mellin_hasDerivAt_of_isBigO_rpow hf htop (by linarith) hbot (by linarith)).2

/-- `Γ' = M[log t · e^{−t}]` on `Re s > 0`. -/
theorem deriv_Gamma_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.Gamma s = mellin (fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ)) s := by
  have hev : Complex.Gamma =ᶠ[𝓝 s] Complex.GammaIntegral := by
    filter_upwards [isOpen_re_pos.mem_nhds hs] with z hz
    exact Complex.Gamma_eq_integral hz
  rw [hev.deriv_eq, (Complex.hasDerivAt_GammaIntegral hs).deriv]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.real_smul]
  ring

/-- ★★ **`H₂ = Γ''(½)`**: the second Gamma log-moment is the second derivative of `Γ` at `½`. -/
theorem gammaLogMoment_two_eq :
    ((gammaLogMoment 2 : ℝ) : ℂ) = deriv (deriv Complex.Gamma) (1 / 2) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hev : deriv Complex.Gamma =ᶠ[𝓝 (1 / 2 : ℂ)]
      mellin fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ) := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact deriv_Gamma_eq_mellin hz
  rw [hev.deriv_eq, (hasDerivAt_mellin_log_exp hhalf).deriv]
  unfold mellin gammaLogMoment
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  simp only [Complex.real_smul]
  push_cast
  rw [Complex.ofReal_cpow ht0.le]
  push_cast
  ring_nf

/-- ★★★ **`H₂ = √π((γ + 2 log 2)² + π²/2)`.** -/
theorem gammaLogMoment_two :
    gammaLogMoment 2 =
      Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) := by
  have := gammaLogMoment_two_eq
  rw [deriv_deriv_Gamma_one_half] at this
  exact_mod_cast this

/-- The depth-three binomial polynomial, explicit:
`B₂(X) = √π[(X + γ + 2 log 2)² + π²/2]`. -/
theorem depthPoly_two (X : ℝ) :
    depthPoly 2 X = Real.sqrt Real.pi *
      ((X + Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) := by
  simp [depthPoly, Finset.sum_range_succ, gammaLogMoment_zero, gammaLogMoment_one,
    gammaLogMoment_two]
  ring


end Grammar
