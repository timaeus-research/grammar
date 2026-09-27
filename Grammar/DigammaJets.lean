/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaDuplicationAllOrders

/-!
# Digamma jets: the one-point recurrence and the digamma duplication at every order

With `ψ = Γ'/Γ` (`gammaLogDeriv`, analytic on `Re z > 0`) and the normalised jets
`psiOneCoeff j = ψ^{(j)}(1)/j!`, `psiHalfCoeff j = ψ^{(j)}(½)/j!`:

* `Γ' = ψ·Γ` near `1` gives the one-point recurrence for `g_n = Γ^{(n)}(1)/n!`
  (★★ `gammaOneCoeff_succ_mul : (n+1) g_{n+1} = Σ_{j≤n} ψ_j g_{n−j}`), with
  `ψ_0 = −γ`, `ψ_1 = π²/6`, `ψ_2 = λ₃/2` (`psiOneCoeff_zero/one/two`);
* the shifted duplication formula differentiated once and divided by itself gives the digamma
  duplication `ψ(½+z) + ψ(1+z) = 2ψ(1+2z) − 2 log 2` on `Re z > −½`
  (★★ `gammaLogDeriv_duplication`), hence at every order
  ★★★ `psiHalfCoeff_eq : ψ½_j = (2^{j+1} − 1) ψ_j − 2 log 2·[j = 0]`.

Jet tools on `taylorCoeff`: `taylorCoeff_deriv` (`[z^n]f' = (n+1)[z^{n+1}]f`), `taylorCoeff_congr`
(eventual equality), `taylorCoeff_add`, `taylorCoeff_const_mul`, `taylorCoeff_const_add`,
`taylorCoeff_const`.  This is the boundary at which the ζ-values enter:
`ψ_j = (−1)^{j+1} ζ(j+1)` for `j ≥ 1` is the remaining derivation.  Astra round 26 targets (α), (γ).
Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-! ### Jet tools -/

theorem taylorCoeff_deriv (f : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    taylorCoeff (deriv f) z n = ((n : ℂ) + 1) * taylorCoeff f z (n + 1) := by
  unfold taylorCoeff
  rw [iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

theorem taylorCoeff_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) (n : ℕ) :
    taylorCoeff f z n = taylorCoeff g z n := by
  unfold taylorCoeff
  rw [h.iteratedDeriv_eq n]

theorem taylorCoeff_add {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (n : ℕ) :
    taylorCoeff (fun w => f w + g w) z n = taylorCoeff f z n + taylorCoeff g z n := by
  unfold taylorCoeff
  rw [show (fun w => f w + g w) = f + g from rfl,
    iteratedDeriv_add (hf.contDiffAt (n := n)) (hg.contDiffAt (n := n)), add_div]

theorem taylorCoeff_const_mul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    taylorCoeff (fun w => c * f w) z n = c * taylorCoeff f z n := by
  unfold taylorCoeff
  rw [iteratedDeriv_const_mul_field]
  ring

theorem taylorCoeff_const (c z : ℂ) (n : ℕ) :
    taylorCoeff (fun _ => c) z n = if n = 0 then c else 0 := by
  unfold taylorCoeff
  rw [iteratedDeriv_const]
  split_ifs with h
  · subst h
    simp
  · simp

theorem taylorCoeff_const_add (c : ℂ) (f : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    taylorCoeff (fun w => c + f w) z n = (if n = 0 then c else 0) + taylorCoeff f z n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [taylorCoeff_zero']
  · unfold taylorCoeff
    rw [iteratedDeriv_const_add hn, if_neg hn.ne', zero_add]

/-! ### The digamma function and its jets -/

/-- `ψ = Γ'/Γ` (Lean's total division; the analytic object on `Re z > 0`). -/
noncomputable def gammaLogDeriv (z : ℂ) : ℂ := deriv Complex.Gamma z / Complex.Gamma z

/-- `ψ^{(j)}(1)/j!`. -/
noncomputable def psiOneCoeff (j : ℕ) : ℂ := taylorCoeff gammaLogDeriv 1 j

/-- `ψ^{(j)}(½)/j!`. -/
noncomputable def psiHalfCoeff (j : ℕ) : ℂ := taylorCoeff gammaLogDeriv (1 / 2) j

theorem analyticAt_gammaLogDeriv {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ gammaLogDeriv z :=
  (analyticAt_Gamma_of_re_pos hz).deriv.div (analyticAt_Gamma_of_re_pos hz)
    (Complex.Gamma_ne_zero_of_re_pos hz)

theorem deriv_Gamma_eq_logDeriv_mul {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.Gamma z = gammaLogDeriv z * Complex.Gamma z := by
  unfold gammaLogDeriv
  rw [div_mul_cancel₀ _ (Complex.Gamma_ne_zero_of_re_pos hz)]

/-- ★★ **The one-point recurrence**: `(n+1) g_{n+1} = Σ_{j≤n} ψ_j g_{n−j}`. -/
theorem gammaOneCoeff_succ_mul (n : ℕ) :
    ((n : ℂ) + 1) * gammaOneCoeff (n + 1) =
      ∑ j ∈ range (n + 1), psiOneCoeff j * gammaOneCoeff (n - j) := by
  have hone : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hev : deriv Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] fun z => gammaLogDeriv z * Complex.Gamma z := by
    filter_upwards [isOpen_re_pos.mem_nhds hone] with z hz
    exact deriv_Gamma_eq_logDeriv_mul hz
  unfold gammaOneCoeff psiOneCoeff
  rw [← taylorCoeff_deriv, taylorCoeff_congr hev,
    taylorCoeff_mul (analyticAt_gammaLogDeriv hone) (analyticAt_Gamma_of_re_pos hone)]

theorem psiOneCoeff_zero : psiOneCoeff 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  rw [psiOneCoeff, taylorCoeff_zero', gammaLogDeriv, Complex.hasDerivAt_Gamma_one.deriv,
    Complex.Gamma_one, div_one]

/-- `ψ'(1) = π²/6` (the trigamma value, from `Γ''(1)` and the recurrence). -/
theorem psiOneCoeff_one : psiOneCoeff 1 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  have h := gammaOneCoeff_succ_mul 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [gammaOneCoeff_one, gammaOneCoeff_two, psiOneCoeff_zero, gammaOneCoeff_zero] at h
  push_cast at h ⊢
  linear_combination -1 * h

/-- `ψ''(1)/2 = λ₃/2`. -/
theorem psiOneCoeff_two : psiOneCoeff 2 = ((gammaLogThirdOne : ℝ) : ℂ) / 2 := by
  have h := gammaOneCoeff_succ_mul 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [gammaOneCoeff_one, gammaOneCoeff_two, gammaOneCoeff_three, psiOneCoeff_zero,
    psiOneCoeff_one, gammaOneCoeff_zero] at h
  unfold gammaLogThirdOne
  push_cast at h ⊢
  linear_combination -1 * h

/-! ### The digamma duplication formula -/

/-- ★★ `ψ(½+z) + ψ(1+z) = 2ψ(1+2z) − 2 log 2` on `Re z > −½`. -/
theorem gammaLogDeriv_duplication {z : ℂ} (hz : -1 / 2 < z.re) :
    gammaLogDeriv (1 / 2 + z) + gammaLogDeriv (1 + z) =
      2 * gammaLogDeriv (1 + 2 * z) - 2 * Complex.log 2 := by
  have h1 : 0 < (1 / 2 + z).re := by
    simp
    linarith
  have h2 : 0 < (1 + z).re := by
    simp
    linarith
  have h3 : 0 < (1 + 2 * z).re := by
    simp
    linarith
  have hA := Complex.Gamma_ne_zero_of_re_pos h1
  have hB := Complex.Gamma_ne_zero_of_re_pos h2
  have hC := Complex.Gamma_ne_zero_of_re_pos h3
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hE : Complex.exp ((-2 * Complex.log 2) * z) ≠ 0 := Complex.exp_ne_zero _
  have hL : HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 + w) * Complex.Gamma (1 + w))
      (deriv Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 + z) +
        Complex.Gamma (1 / 2 + z) * deriv Complex.Gamma (1 + z)) z :=
    ((hasDerivAt_Gamma_of_re_pos h1).comp_const_add (1 / 2) z).mul
      ((hasDerivAt_Gamma_of_re_pos h2).comp_const_add 1 z)
  have hlin : HasDerivAt (fun w : ℂ => 1 + 2 * w) 2 z := by
    simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_add 1
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((-2 * Complex.log 2) * w))
      (Complex.exp ((-2 * Complex.log 2) * z) * (-2 * Complex.log 2)) z := by
    have := ((hasDerivAt_id z).const_mul (-2 * Complex.log 2)).cexp
    simpa using this
  have hG := (hasDerivAt_Gamma_of_re_pos h3).comp z hlin
  have hR : HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 + w) * Complex.Gamma (1 + w))
      ((Complex.exp ((-2 * Complex.log 2) * z) * (-2 * Complex.log 2) * Complex.Gamma (1 + 2 * z) +
        Complex.exp ((-2 * Complex.log 2) * z) * (deriv Complex.Gamma (1 + 2 * z) * 2)) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)) z := by
    have hfun : (fun w : ℂ => Complex.Gamma (1 / 2 + w) * Complex.Gamma (1 + w)) =
        fun w => (Complex.exp ((-2 * Complex.log 2) * w) * Complex.Gamma (1 + 2 * w)) *
          ((Real.sqrt Real.pi : ℝ) : ℂ) := by
      funext w
      exact duplication_shifted w
    rw [hfun]
    exact (hexp.mul hG).mul_const _
  have key := hL.unique hR
  have hdup := duplication_shifted z
  calc gammaLogDeriv (1 / 2 + z) + gammaLogDeriv (1 + z)
      = (deriv Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 + z) +
          Complex.Gamma (1 / 2 + z) * deriv Complex.Gamma (1 + z)) /
          (Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 + z)) := by
        unfold gammaLogDeriv
        rw [div_add_div _ _ hA hB]
    _ = ((Complex.exp ((-2 * Complex.log 2) * z) * (-2 * Complex.log 2) *
          Complex.Gamma (1 + 2 * z) +
          Complex.exp ((-2 * Complex.log 2) * z) * (deriv Complex.Gamma (1 + 2 * z) * 2)) *
          ((Real.sqrt Real.pi : ℝ) : ℂ)) /
          ((Complex.exp ((-2 * Complex.log 2) * z) * Complex.Gamma (1 + 2 * z)) *
            ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
        rw [key, hdup]
    _ = 2 * gammaLogDeriv (1 + 2 * z) - 2 * Complex.log 2 := by
        unfold gammaLogDeriv
        field_simp
        ring

theorem taylorCoeff_gammaLogDeriv_one_add_two_mul (m : ℕ) :
    taylorCoeff (fun z : ℂ => gammaLogDeriv (1 + 2 * z)) 0 m = 2 ^ m * psiOneCoeff m := by
  have := taylorCoeff_comp_const_mul (fun w => gammaLogDeriv (1 + w)) 2 0 m
  simp only [mul_zero] at this
  rw [taylorCoeff_comp_const_add, add_zero] at this
  exact this

/-- ★★★ **Digamma duplication at every order**: `ψ½_j = (2^{j+1} − 1) ψ_j − 2 log 2·[j = 0]`. -/
theorem psiHalfCoeff_eq (j : ℕ) :
    psiHalfCoeff j = ((2 : ℂ) ^ (j + 1) - 1) * psiOneCoeff j -
      (if j = 0 then 2 * Complex.log 2 else 0) := by
  have hopen : IsOpen {z : ℂ | -1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z : ℂ => gammaLogDeriv (1 / 2 + z) + gammaLogDeriv (1 + z)) =ᶠ[𝓝 0]
      fun z => (-2 * Complex.log 2) + 2 * gammaLogDeriv (1 + 2 * z) := by
    filter_upwards [hopen.mem_nhds (by simp; norm_num : (0 : ℂ) ∈ {z : ℂ | -1 / 2 < z.re})]
      with z hz
    rw [gammaLogDeriv_duplication hz]
    ring
  have hl1 : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z) 0 := by fun_prop
  have hl2 : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := by fun_prop
  have hB : AnalyticAt ℂ (fun z : ℂ => gammaLogDeriv (1 / 2 + z)) 0 :=
    (analyticAt_gammaLogDeriv (z := 1 / 2) (by norm_num)).comp_of_eq hl1 (by norm_num)
  have hC : AnalyticAt ℂ (fun z : ℂ => gammaLogDeriv (1 + z)) 0 :=
    (analyticAt_gammaLogDeriv (z := 1) (by norm_num)).comp_of_eq hl2 (by norm_num)
  have h := taylorCoeff_congr hev j
  rw [taylorCoeff_add hB hC, taylorCoeff_const_add, taylorCoeff_const_mul,
    taylorCoeff_gammaLogDeriv_one_add_two_mul] at h
  simp only [taylorCoeff_comp_const_add, add_zero] at h
  simp only [psiHalfCoeff, psiOneCoeff] at h ⊢
  split_ifs at h ⊢ with hj
  · subst hj
    linear_combination h
  · linear_combination h

end Grammar
