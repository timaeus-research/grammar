/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DigammaJets

/-!
# The depth recurrence: every `P_L` from the digamma jets

The logarithmic derivative of `H_D(z) = 2^{(D−1)z}Γ(½−z)Γ(1+z)^D/√π` is
`H_D'/H_D = (D−1) log 2 − ψ(½−z) + Dψ(1+z)` (`hasDerivAt_depthJet`, an explicit product rule on
`−1 < Re z < ½`), whose jet at `0` is `q_{D,j} = (D−1) log 2·[j=0] − (−1)^j ψ½_j + Dψ_j`
(`depthLogDerivCoeff`, `taylorCoeff_depthLogDeriv`), so the Taylor coefficients of `H_D` satisfy
the Cauchy recurrence

  ★★★ `depthJetCoeff_succ_mul : (n+1) h_{D,n+1} = Σ_{j≤n} q_{D,j} h_{D,n−j}`,

and by the digamma duplication `q_{D,j} = (D − (−1)^j(2^{j+1} − 1))ψ_j + (D+1) log 2·[j=0]`
(`depthLogDerivCoeff_eq_one`): with DCLXXV every coefficient of every `P_L` and every residual mass
is a polynomial in `log 2` and the one-point digamma jets `ψ_j` alone.  Regression:
`q_{D,0} = (D+1) log 2 − (D−1)γ`, the all-depth centring `D_L` of the note.  Astra round 26
target (β).  Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-- `H_D'/H_D` as a function: `(D−1) log 2 − ψ(½−z) + Dψ(1+z)`. -/
noncomputable def depthLogDeriv (D : ℕ) (z : ℂ) : ℂ :=
  ((D : ℂ) - 1) * Complex.log 2 +
    ((-1) * gammaLogDeriv (1 / 2 - z) + (D : ℂ) * gammaLogDeriv (1 + z))

/-- `q_{D,j} = (D−1) log 2·[j=0] − (−1)^j ψ½_j + Dψ_j`. -/
noncomputable def depthLogDerivCoeff (D j : ℕ) : ℂ :=
  (if j = 0 then ((D : ℂ) - 1) * Complex.log 2 else 0) - (-1) ^ j * psiHalfCoeff j +
    (D : ℂ) * psiOneCoeff j

/-- The explicit product rule: `H_{D+1}' = (H_{D+1}'/H_{D+1}) · H_{D+1}` on `−1 < Re z < ½`. -/
theorem hasDerivAt_depthJet (D : ℕ) {z : ℂ} (hz1 : -1 < z.re) (hz2 : z.re < 1 / 2) :
    HasDerivAt (depthJet (D + 1)) (depthLogDeriv (D + 1) z * depthJet (D + 1) z) z := by
  have hA : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ ((((D + 1 : ℕ) : ℂ) - 1) * w))
      ((2 : ℂ) ^ ((((D + 1 : ℕ) : ℂ) - 1) * z) * Complex.log 2 * (((D + 1 : ℕ) : ℂ) - 1)) z := by
    have h := (hasDerivAt_two_cpow ((((D + 1 : ℕ) : ℂ) - 1) * z)).comp z
      ((hasDerivAt_id' (x := z)).const_mul (((D + 1 : ℕ) : ℂ) - 1))
    simp only [Function.comp_def, mul_one] at h
    refine h.congr_deriv ?_
    ring
  have hB := hasDerivAt_cB hz2
  have hC := hasDerivAt_cC hz1
  have hCD := hC.pow (D + 1)
  have := ((hA.mul hB).mul hCD).div_const ((Real.sqrt Real.pi : ℝ) : ℂ)
  unfold depthJet depthLogDeriv gammaLogDeriv
  refine this.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.add_sub_cancel]
  have hB0 : Complex.Gamma (1 / 2 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (re_half_sub_pos hz2)
  have hC0 : Complex.Gamma (1 + z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (re_one_add_pos hz1)
  have hB' : deriv Complex.Gamma (1 / 2 - z) / Complex.Gamma (1 / 2 - z) *
      Complex.Gamma (1 / 2 - z) = deriv Complex.Gamma (1 / 2 - z) := div_mul_cancel₀ _ hB0
  have hC' : deriv Complex.Gamma (1 + z) / Complex.Gamma (1 + z) * Complex.Gamma (1 + z) =
      deriv Complex.Gamma (1 + z) := div_mul_cancel₀ _ hC0
  linear_combination
    ((2 : ℂ) ^ ((((D + 1 : ℕ) : ℂ) - 1) * z) * Complex.Gamma (1 + z) ^ (D + 1) /
      ((Real.sqrt Real.pi : ℝ) : ℂ)) * hB' -
    (((D + 1 : ℕ) : ℂ) * (2 : ℂ) ^ ((((D + 1 : ℕ) : ℂ) - 1) * z) * Complex.Gamma (1 / 2 - z) *
      Complex.Gamma (1 + z) ^ D / ((Real.sqrt Real.pi : ℝ) : ℂ)) * hC'

theorem isOpen_strip : IsOpen {z : ℂ | -1 < z.re ∧ z.re < 1 / 2} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem depthJet_deriv_eventually (D : ℕ) :
    deriv (depthJet (D + 1)) =ᶠ[𝓝 0] fun z => depthLogDeriv (D + 1) z * depthJet (D + 1) z := by
  filter_upwards [isOpen_strip.mem_nhds (by simp)] with z hz
  exact (hasDerivAt_depthJet D hz.1 hz.2).deriv

theorem analyticAt_gammaLogDeriv_half_sub :
    AnalyticAt ℂ (fun z : ℂ => gammaLogDeriv (1 / 2 - z)) 0 :=
  (analyticAt_gammaLogDeriv (z := 1 / 2) (by norm_num)).comp_of_eq
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 / 2 - z) 0) (by norm_num)

theorem analyticAt_gammaLogDeriv_one_add :
    AnalyticAt ℂ (fun z : ℂ => gammaLogDeriv (1 + z)) 0 :=
  (analyticAt_gammaLogDeriv (z := 1) (by norm_num)).comp_of_eq
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0) (by norm_num)

theorem analyticAt_depthLogDeriv (D : ℕ) : AnalyticAt ℂ (depthLogDeriv D) 0 := by
  unfold depthLogDeriv
  exact analyticAt_const.add ((analyticAt_const.mul analyticAt_gammaLogDeriv_half_sub).add
    (analyticAt_const.mul analyticAt_gammaLogDeriv_one_add))

/-- `[z^j] ψ(½ − z) = (−1)^j ψ½_j`. -/
theorem taylorCoeff_gammaLogDeriv_half_sub (j : ℕ) :
    taylorCoeff (fun z : ℂ => gammaLogDeriv (1 / 2 - z)) 0 j = (-1) ^ j * psiHalfCoeff j := by
  have e : (fun z : ℂ => gammaLogDeriv (1 / 2 - z)) =
      fun z => (fun w => gammaLogDeriv (1 / 2 + w)) ((-1) * z) := by
    funext z
    simp only
    congr 1
    ring
  rw [e, taylorCoeff_comp_const_mul (fun w => gammaLogDeriv (1 / 2 + w)) (-1) 0 j, mul_zero,
    taylorCoeff_comp_const_add, add_zero]
  rfl

/-- The jet of `H_D'/H_D` at `0` is `q_{D,·}`. -/
theorem taylorCoeff_depthLogDeriv (D j : ℕ) :
    taylorCoeff (depthLogDeriv D) 0 j = depthLogDerivCoeff D j := by
  unfold depthLogDeriv depthLogDerivCoeff
  have h1 : AnalyticAt ℂ (fun z : ℂ => (-1) * gammaLogDeriv (1 / 2 - z)) 0 :=
    analyticAt_const.mul analyticAt_gammaLogDeriv_half_sub
  have h2 : AnalyticAt ℂ (fun z : ℂ => (D : ℂ) * gammaLogDeriv (1 + z)) 0 :=
    analyticAt_const.mul analyticAt_gammaLogDeriv_one_add
  rw [taylorCoeff_const_add, taylorCoeff_add h1 h2, taylorCoeff_const_mul, taylorCoeff_const_mul,
    taylorCoeff_gammaLogDeriv_half_sub, taylorCoeff_comp_const_add, add_zero]
  unfold psiOneCoeff
  ring

/-- ★★★ **The depth recurrence**: `(n+1) h_{D+1,n+1} = Σ_{j≤n} q_{D+1,j} h_{D+1,n−j}`. -/
theorem depthJetCoeff_succ_mul (D n : ℕ) :
    ((n : ℂ) + 1) * depthJetCoeff (D + 1) (n + 1) =
      ∑ j ∈ range (n + 1), depthLogDerivCoeff (D + 1) j * depthJetCoeff (D + 1) (n - j) := by
  rw [depthJetCoeff_eq_taylorCoeff, ← taylorCoeff_deriv,
    taylorCoeff_congr (depthJet_deriv_eventually D),
    taylorCoeff_mul (analyticAt_depthLogDeriv (D + 1)) (analyticAt_depthJet (D + 1))]
  simp only [depthJetCoeff_eq_taylorCoeff, taylorCoeff_depthLogDeriv]

/-- `q_{D,j}` in the one-point jets alone. -/
theorem depthLogDerivCoeff_eq_one (D j : ℕ) :
    depthLogDerivCoeff D j =
      ((D : ℂ) - (-1) ^ j * ((2 : ℂ) ^ (j + 1) - 1)) * psiOneCoeff j +
        (if j = 0 then ((D : ℂ) + 1) * Complex.log 2 else 0) := by
  unfold depthLogDerivCoeff
  rw [psiHalfCoeff_eq]
  split_ifs with hj
  · subst hj
    ring
  · ring

/-- Regression: `q_{D,0} = (D+1) log 2 − (D−1)γ`, the all-depth centring. -/
theorem depthLogDerivCoeff_zero (D : ℕ) :
    depthLogDerivCoeff D 0 =
      ((D : ℂ) + 1) * Complex.log 2 - ((D : ℂ) - 1) * (Real.eulerMascheroniConstant : ℂ) := by
  rw [depthLogDerivCoeff_eq_one, psiOneCoeff_zero, if_pos rfl]
  ring

/-- Regression: `h_{D+1,1} = q_{D+1,0}`. -/
theorem depthJetCoeff_one (D : ℕ) :
    depthJetCoeff (D + 1) 1 = depthLogDerivCoeff (D + 1) 0 := by
  have h := depthJetCoeff_succ_mul D 0
  simp only [Finset.sum_range_one, Nat.sub_zero, depthJetCoeff_zero, mul_one, Nat.cast_zero,
    zero_add, one_mul] at h
  exact h

end Grammar
