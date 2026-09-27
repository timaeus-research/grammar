/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthThreeCubicJet

/-!
# `Γ'''(½)` from `Γ'''(1)` by duplication: the cubic jet modulo one symbol

Legendre's duplication formula `Γ(w)Γ(w + ½) = Γ(2w) 2^{1−2w} √π` differentiated three times at
`w = ½` (DCXXXVIII one order up) gives

  `Γ'''(½)Γ(1) + 3Γ''(½)Γ'(1) + 3Γ'(½)Γ''(1) + Γ(½)Γ'''(1)
     = √π[8Γ'''(1) − 24 log 2 Γ''(1) + 24 log² 2 Γ'(1) − 8 log³ 2 Γ(1)]`

(★★ `deriv_deriv_deriv_duplication`), hence with the known lower data at `½` and `1`
(★★★ `deriv_deriv_deriv_Gamma_one_half`, real form `gammaThirdHalf_eq`)

  `Γ'''(½) = √π[7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`,  `p = γ + 2 log 2`.

With the log-Gamma symbol `λ₃ = Γ'''(1) + γ³ + γπ²/2` (`gammaLogThirdOne`; the identification
`λ₃ = (log Γ)'''(1) = −2ζ(3)` is a derivation) the DCLXXI cubic jet coefficient collapses to
★★★ `depthThreeJetCubic_eq_logThird : c₃ = c₁³/6 + c₁π²/2 − (2/3)λ₃`, so the depth-three
residual mass `Q₃ = [c₁³/6 + c₁π²/2 − (2/3)λ₃]/(4π)` (`residualMass_three_eq_logThird`,
`depthFourQint_eq_logThird`) is closed modulo ONE symbol.  Examples_slop §2; Astra round 23
target 1.  Zero `sorry`/`axiom`.
-/

open Filter Topology

namespace Grammar

/-! ### The left side `Γ(w)Γ(w + ½)` -/

/-- `(Γ(w)Γ(w + ½))'`. -/
noncomputable def dupL' (z : ℂ) : ℂ :=
  deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
    Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2)

/-- `(Γ(w)Γ(w + ½))''`. -/
noncomputable def dupL'' (z : ℂ) : ℂ :=
  deriv (deriv Complex.Gamma) z * Complex.Gamma (z + 1 / 2) +
    2 * deriv Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2) +
    Complex.Gamma z * deriv (deriv Complex.Gamma) (z + 1 / 2)

theorem re_add_half_pos {z : ℂ} (h0 : 0 < z.re) : 0 < (z + 1 / 2).re := by
  simp
  linarith

theorem hasDerivAt_dupL {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) (dupL' z) z :=
  deriv_duplication h0

theorem hasDerivAt_dupL' {z : ℂ} (h0 : 0 < z.re) : HasDerivAt dupL' (dupL'' z) z := by
  have hA := hasDerivAt_deriv_Gamma_of_re_pos h0
  have hB := (hasDerivAt_Gamma_of_re_pos (re_add_half_pos h0)).comp_add_const z (1 / 2)
  have hC := hasDerivAt_Gamma_of_re_pos h0
  have hD := (hasDerivAt_deriv_Gamma_of_re_pos (re_add_half_pos h0)).comp_add_const z (1 / 2)
  have := (hA.mul hB).add (hC.mul hD)
  unfold dupL' dupL''
  refine this.congr_deriv ?_
  ring

/-- The third derivative of the left side at `½`. -/
theorem hasDerivAt_dupL''_half :
    HasDerivAt dupL''
      (deriv (deriv (deriv Complex.Gamma)) (1 / 2) * Complex.Gamma 1 +
        3 * deriv (deriv Complex.Gamma) (1 / 2) * deriv Complex.Gamma 1 +
        3 * deriv Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1 +
        Complex.Gamma (1 / 2) * deriv (deriv (deriv Complex.Gamma)) 1) (1 / 2) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have h1 : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  have hA := hasDerivAt_deriv_deriv_Gamma_of_re_pos hhalf
  have hB : HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1 / 2)) (deriv Complex.Gamma 1)
      (1 / 2) := by
    have := (hasDerivAt_Gamma_of_re_pos (z := 1 / 2 + 1 / 2)
      (by rw [h1]; exact hone)).comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [h1] at this
    exact this
  have hC := hasDerivAt_deriv_Gamma_of_re_pos hhalf
  have hD : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (w + 1 / 2))
      (deriv (deriv Complex.Gamma) 1) (1 / 2) := by
    have := (hasDerivAt_deriv_Gamma_of_re_pos (z := 1 / 2 + 1 / 2)
      (by rw [h1]; exact hone)).comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [h1] at this
    exact this
  have hE := hasDerivAt_Gamma_of_re_pos hhalf
  have hF : HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (w + 1 / 2))
      (deriv (deriv (deriv Complex.Gamma)) 1) (1 / 2) := by
    have := (hasDerivAt_deriv_deriv_Gamma_of_re_pos (z := 1 / 2 + 1 / 2)
      (by rw [h1]; exact hone)).comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [h1] at this
    exact this
  have := ((hA.mul hB).add ((hC.const_mul 2).mul hD)).add (hE.mul hF)
  unfold dupL''
  refine this.congr_deriv ?_
  rw [h1]
  ring

/-! ### The right side `Γ(2w) 2^{1−2w} √π` -/

/-- `(Γ(2w) 2^{1−2w} √π)'` (the form of DCXXXVIII's `deriv_duplication_rhs`). -/
noncomputable def dupR' (z : ℂ) : ℂ :=
  (deriv Complex.Gamma (2 * z) * 2 * (2 : ℂ) ^ (1 - 2 * z) +
    Complex.Gamma (2 * z) * ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2))) *
      ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- `(Γ(2w) 2^{1−2w} √π)''`. -/
noncomputable def dupR'' (z : ℂ) : ℂ :=
  (4 * deriv (deriv Complex.Gamma) (2 * z) * (2 : ℂ) ^ (1 - 2 * z) -
    8 * Complex.log 2 * deriv Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) +
    4 * Complex.log 2 ^ 2 * Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z)) *
      ((Real.sqrt Real.pi : ℝ) : ℂ)

theorem hasDerivAt_dupR {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w : ℂ =>
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ))
      (dupR' z) z :=
  deriv_duplication_rhs h0

theorem hasDerivAt_dupR' {z : ℂ} (h0 : 0 < z.re) : HasDerivAt dupR' (dupR'' z) z := by
  have h2 : 0 < (2 * z).re := by
    simp
    linarith
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  have hlin2 : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_sub 1
  have hA := (hasDerivAt_deriv_Gamma_of_re_pos h2).comp z hlin
  have hP := hlin2.const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  have hG := (hasDerivAt_Gamma_of_re_pos h2).comp z hlin
  have := (((hA.mul_const 2).mul hP).add
    (hG.mul ((hP.mul_const (Complex.log 2)).mul_const (-2)))).mul_const
      ((Real.sqrt Real.pi : ℝ) : ℂ)
  unfold dupR' dupR''
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

/-- The third derivative of the right side at `½`. -/
theorem hasDerivAt_dupR''_half :
    HasDerivAt dupR''
      ((8 * deriv (deriv (deriv Complex.Gamma)) 1 -
        24 * Complex.log 2 * deriv (deriv Complex.Gamma) 1 +
        24 * Complex.log 2 ^ 2 * deriv Complex.Gamma 1 - 8 * Complex.log 2 ^ 3 * Complex.Gamma 1) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)) (1 / 2) := by
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have h1 : (2 * (1 / 2 : ℂ)) = 1 := by norm_num
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)
  have hlin2 : HasDerivAt (fun w : ℂ => 1 - 2 * w) (-2) (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)).const_sub 1
  have hA : HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (2 * w))
      (deriv (deriv (deriv Complex.Gamma)) 1 * 2) (1 / 2) := by
    have := (hasDerivAt_deriv_deriv_Gamma_of_re_pos (z := 2 * (1 / 2))
      (by rw [h1]; exact hone)).comp (1 / 2 : ℂ) hlin
    rw [h1] at this
    exact this
  have hB : HasDerivAt (fun w : ℂ => deriv Complex.Gamma (2 * w))
      (deriv (deriv Complex.Gamma) 1 * 2) (1 / 2) := by
    have := (hasDerivAt_deriv_Gamma_of_re_pos (z := 2 * (1 / 2)) (by rw [h1]; exact hone)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    exact this
  have hG : HasDerivAt (fun w : ℂ => Complex.Gamma (2 * w)) (deriv Complex.Gamma 1 * 2)
      (1 / 2) := by
    have := (hasDerivAt_Gamma_of_re_pos (z := 2 * (1 / 2)) (by rw [h1]; exact hone)).comp
      (1 / 2 : ℂ) hlin
    rw [h1] at this
    exact this
  have hP : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w))
      ((2 : ℂ) ^ (1 - 2 * (1 / 2 : ℂ)) * Complex.log 2 * (-2)) (1 / 2) :=
    hlin2.const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  have := ((((hA.const_mul 4).mul hP).sub ((hB.const_mul (8 * Complex.log 2)).mul hP)).add
    ((hG.const_mul (4 * Complex.log 2 ^ 2)).mul hP)).mul_const ((Real.sqrt Real.pi : ℝ) : ℂ)
  unfold dupR''
  refine this.congr_deriv ?_
  rw [h1, sub_self, Complex.cpow_zero]
  ring

/-! ### The third-order duplication identity -/

/-- ★★ The duplication formula differentiated three times at `½`. -/
theorem deriv_deriv_deriv_duplication :
    deriv (deriv (deriv Complex.Gamma)) (1 / 2) * Complex.Gamma 1 +
        3 * deriv (deriv Complex.Gamma) (1 / 2) * deriv Complex.Gamma 1 +
        3 * deriv Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1 +
        Complex.Gamma (1 / 2) * deriv (deriv (deriv Complex.Gamma)) 1 =
      (8 * deriv (deriv (deriv Complex.Gamma)) 1 -
        24 * Complex.log 2 * deriv (deriv Complex.Gamma) 1 +
        24 * Complex.log 2 ^ 2 * deriv Complex.Gamma 1 - 8 * Complex.log 2 ^ 3 * Complex.Gamma 1) *
        ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hdup : (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =
      fun w : ℂ =>
        Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    funext w
    exact Complex.Gamma_mul_Gamma_add_half w
  have hL1 : deriv (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      dupL' := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (hasDerivAt_dupL hz).deriv
  have hL2 : deriv dupL' =ᶠ[𝓝 (1 / 2 : ℂ)] dupL'' := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (hasDerivAt_dupL' hz).deriv
  have hR1 : deriv (fun w : ℂ =>
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ)) =ᶠ[𝓝
        (1 / 2 : ℂ)] dupR' := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (hasDerivAt_dupR hz).deriv
  have hR2 : deriv dupR' =ᶠ[𝓝 (1 / 2 : ℂ)] dupR'' := by
    filter_upwards [isOpen_re_pos.mem_nhds hhalf] with z hz
    exact (hasDerivAt_dupR' hz).deriv
  have hL : deriv (deriv (deriv (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2))))
      (1 / 2) = deriv (deriv (deriv (fun w : ℂ =>
        Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ))))
        (1 / 2) := by
    rw [hdup]
  rw [hL1.deriv.deriv_eq, hL2.deriv_eq, hasDerivAt_dupL''_half.deriv, hR1.deriv.deriv_eq,
    hR2.deriv_eq, hasDerivAt_dupR''_half.deriv] at hL
  exact hL

/-- ★★★ **`Γ'''(½) = 7√π Γ'''(1) + √π[7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`**, `p = γ + 2 log 2`. -/
theorem deriv_deriv_deriv_Gamma_one_half :
    deriv (deriv (deriv Complex.Gamma)) (1 / 2) =
      ((7 * Real.sqrt Real.pi : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) 1 +
        ((Real.sqrt Real.pi * (7 * Real.eulerMascheroniConstant ^ 3 +
          7 * Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 -
          (Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
          3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2) : ℝ) : ℂ) := by
  have key := deriv_deriv_deriv_duplication
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
  have hG2 := deriv_deriv_Gamma_one
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [Complex.Gamma_one, hG, hG', hG1, hG'', hG2, hlog] at key
  have hpi : ((Real.pi : ℝ) : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  push_cast at key ⊢
  rw [hpi] at key ⊢
  set S : ℂ := ((Real.sqrt Real.pi : ℝ) : ℂ) with hS
  set g : ℂ := (Real.eulerMascheroniConstant : ℂ) with hg
  set l : ℂ := ((Real.log 2 : ℝ) : ℂ) with hl
  clear_value S g l
  linear_combination key

/-- The log-Gamma symbol `λ₃ = Γ'''(1) + γ³ + γπ²/2` (`= (log Γ)'''(1) = −2ζ(3)`; identification
with `ζ(3)` is a derivation). -/
noncomputable def gammaLogThirdOne : ℝ :=
  gammaThirdOne + Real.eulerMascheroniConstant ^ 3 +
    Real.eulerMascheroniConstant * Real.pi ^ 2 / 2

/-- ★★★ The real form: `Γ'''(½) = √π[7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`. -/
theorem gammaThirdHalf_eq :
    gammaThirdHalf = Real.sqrt Real.pi * (7 * gammaThirdOne +
      7 * Real.eulerMascheroniConstant ^ 3 + 7 * Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 -
      (Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
      3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2) := by
  unfold gammaThirdHalf gammaThirdOne
  rw [deriv_deriv_deriv_Gamma_one_half, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

/-- ★★★ **The cubic jet coefficient modulo one symbol**:
`c₃ = c₁³/6 + c₁π²/2 − (2/3)λ₃`. -/
theorem depthThreeJetCubic_eq_logThird :
    depthThreeJetCubic = depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
      2 / 3 * gammaLogThirdOne := by
  unfold depthThreeJetCubic gammaLogThirdOne depthThreeJetLinear
  rw [gammaThirdHalf_eq]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  ring

/-- ★★★ `Q₃ = [c₁³/6 + c₁π²/2 − (2/3)λ₃]/(4π)`. -/
theorem residualMass_three_eq_logThird :
    residualMass 3 (enginePoly 3) =
      (depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
        2 / 3 * gammaLogThirdOne) / (4 * Real.pi) := by
  rw [residualMass_three_eq_jet, depthThreeJetCubic_eq_logThird]

theorem depthFourQint_eq_logThird :
    depthFourQint =
      (depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
        2 / 3 * gammaLogThirdOne) / (4 * Real.pi) := by
  rw [depthFourQint_eq_jet, depthThreeJetCubic_eq_logThird]

end Grammar
