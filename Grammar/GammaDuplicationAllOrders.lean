/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DepthJetAllCoefficients
import Grammar.CoupledPolarInterchange

/-!
# The duplication formula at every order: `Γ^{(n)}(½)` from `Γ^{(k)}(1)`, `k ≤ n`

Legendre duplication shifted to the origin, `Γ(½ + z)Γ(1 + z) = e^{−2z log 2} Γ(1 + 2z) √π`
(`duplication_shifted`, global), read through the Cauchy product of Taylor coefficients
(`taylorCoeff_mul`, the normalised Leibniz rule) with the shift, scale and exponential jets
(`taylorCoeff_comp_const_add`, `taylorCoeff_comp_const_mul`, `taylorCoeff_cexp_const_mul`), gives
for the normalised coefficients `g_n = Γ^{(n)}(1)/n!` (`gammaOneCoeff`) and
`e_n = Γ^{(n)}(½)/(√π n!)` (`gammaHalfCoeff`) the convolution identity

  `Σ_{k≤n} e_k g_{n−k} = Σ_{k≤n} (−2 log 2)^k/k! · 2^{n−k} g_{n−k}`   (★★ `gammaHalfCoeff_conv`)

and its successor form ★★★ `gammaHalfCoeff_succ` (no `e_{n+1}` on the right), an all-orders
elimination of the half-point derivatives.  Regressions: `e₁ = −(γ + 2 log 2)`,
`e₂ = ((γ + 2 log 2)² + π²/2)/2`, `e₃ = [7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]/6` computed from
the recurrence (`gammaHalfCoeff_one/two/three`) agree with Mathlib's `Γ'(½)`, DCVIII's `Γ''(½)`
and DCLXXII's third-order relation (`gammaHalfCoeff_two_eq_deriv`, `gammaHalfCoeff_three_eq_deriv`).
Astra round 25 target 1.  Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-! ### Jet tools: shift, scale, exponential, constant factor -/

theorem depthJetCoeff_eq_taylorCoeff (D j : ℕ) : depthJetCoeff D j = taylorCoeff (depthJet D) 0 j :=
  rfl

theorem iteratedDeriv_comp_const_add' (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => f (a + z)) = fun z => iteratedDeriv n f (a + z) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_comp_const_add, iteratedDeriv_succ]

theorem iteratedDeriv_comp_const_mul' (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => f (c * z)) = fun z => c ^ n * iteratedDeriv n f (c * z) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ, smul_eq_mul]
    ring

theorem taylorCoeff_comp_const_add (f : ℂ → ℂ) (a z : ℂ) (n : ℕ) :
    taylorCoeff (fun w => f (a + w)) z n = taylorCoeff f (a + z) n := by
  unfold taylorCoeff
  rw [iteratedDeriv_comp_const_add']

theorem taylorCoeff_comp_const_mul (f : ℂ → ℂ) (c z : ℂ) (n : ℕ) :
    taylorCoeff (fun w => f (c * w)) z n = c ^ n * taylorCoeff f (c * z) n := by
  unfold taylorCoeff
  rw [iteratedDeriv_comp_const_mul']
  ring

theorem taylorCoeff_mul_const (f : ℂ → ℂ) (c z : ℂ) (n : ℕ) :
    taylorCoeff (fun w => f w * c) z n = taylorCoeff f z n * c := by
  unfold taylorCoeff
  rw [iteratedDeriv_mul_const_field]
  ring

/-- `[z^n] e^{cz} = c^n/n!` at `0`. -/
theorem taylorCoeff_cexp_const_mul (c : ℂ) (n : ℕ) :
    taylorCoeff (fun z => Complex.exp (c * z)) 0 n = c ^ n / (n.factorial : ℂ) := by
  unfold taylorCoeff
  rw [iteratedDeriv_cexp_const_mul]
  simp

theorem taylorCoeff_zero' (f : ℂ → ℂ) (z : ℂ) : taylorCoeff f z 0 = f z := by
  simp [taylorCoeff, iteratedDeriv_zero]

/-! ### The normalised Gamma jets at `1` and `½` -/

/-- `g_n = Γ^{(n)}(1)/n!`. -/
noncomputable def gammaOneCoeff (n : ℕ) : ℂ := taylorCoeff Complex.Gamma 1 n

/-- `e_n = Γ^{(n)}(½)/(√π n!)`. -/
noncomputable def gammaHalfCoeff (n : ℕ) : ℂ :=
  taylorCoeff Complex.Gamma (1 / 2) n / ((Real.sqrt Real.pi : ℝ) : ℂ)

theorem gammaOneCoeff_zero : gammaOneCoeff 0 = 1 := by
  rw [gammaOneCoeff, taylorCoeff_zero', Complex.Gamma_one]

theorem gammaHalfCoeff_zero : gammaHalfCoeff 0 = 1 := by
  rw [gammaHalfCoeff, taylorCoeff_zero', Gamma_one_half_ofReal, div_self]
  exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'

theorem gammaOneCoeff_one : gammaOneCoeff 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  rw [gammaOneCoeff, taylorCoeff, iteratedDeriv_one, Complex.hasDerivAt_Gamma_one.deriv]
  simp

theorem gammaOneCoeff_two :
    gammaOneCoeff 2 = ((Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 : ℝ) : ℂ) / 2 := by
  rw [gammaOneCoeff, taylorCoeff, iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_Gamma_one]
  norm_num

theorem gammaOneCoeff_three : gammaOneCoeff 3 = ((gammaThirdOne : ℝ) : ℂ) / 6 := by
  rw [gammaOneCoeff, taylorCoeff, iteratedDeriv_eq_iterate, ← gammaOneLogMoment_eq_iterate,
    gammaOneLogMoment_three_eq]
  norm_num

/-! ### The shifted duplication formula -/

theorem duplication_shifted (z : ℂ) :
    Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 + z) =
      (Complex.exp ((-2 * Complex.log 2) * z) * Complex.Gamma (1 + 2 * z)) *
        ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_add_half (1 / 2 + z)
  rw [show (1 - 2 * (1 / 2 + z) : ℂ) = -2 * z by ring, show (1 / 2 + z + 1 / 2 : ℂ) = 1 + z by ring,
    show (2 * (1 / 2 + z) : ℂ) = 1 + 2 * z by ring] at h
  rw [h, Complex.cpow_def_of_ne_zero two_ne_zero,
    show Complex.log 2 * (-2 * z) = (-2 * Complex.log 2) * z by ring]
  ring

theorem taylorCoeff_Gamma_one_add_two_mul (m : ℕ) :
    taylorCoeff (fun z : ℂ => Complex.Gamma (1 + 2 * z)) 0 m =
      2 ^ m * taylorCoeff Complex.Gamma 1 m := by
  have := taylorCoeff_comp_const_mul (fun w => Complex.Gamma (1 + w)) 2 0 m
  simp only [mul_zero] at this
  rw [taylorCoeff_comp_const_add, add_zero] at this
  exact this

/-- ★★ **The convolution identity of the normalised jets.** -/
theorem gammaHalfCoeff_conv (n : ℕ) :
    ∑ k ∈ range (n + 1), gammaHalfCoeff k * gammaOneCoeff (n - k) =
      ∑ k ∈ range (n + 1), (-2 * Complex.log 2) ^ k / (k.factorial : ℂ) *
        (2 ^ (n - k) * gammaOneCoeff (n - k)) := by
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hl1 : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z) 0 := by fun_prop
  have hl2 : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := by fun_prop
  have hl3 : AnalyticAt ℂ (fun z : ℂ => (-2 * Complex.log 2) * z) 0 := by fun_prop
  have hl4 : AnalyticAt ℂ (fun z : ℂ => 1 + 2 * z) 0 := by fun_prop
  have hB : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (1 / 2 + z)) 0 :=
    (analyticAt_Gamma_of_re_pos (z := 1 / 2) (by norm_num)).comp_of_eq hl1 (by norm_num)
  have hC : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (1 + z)) 0 :=
    (analyticAt_Gamma_of_re_pos (z := 1) (by norm_num)).comp_of_eq hl2 (by norm_num)
  have hE : AnalyticAt ℂ (fun z : ℂ => Complex.exp ((-2 * Complex.log 2) * z)) 0 := hl3.cexp
  have hD : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (1 + 2 * z)) 0 :=
    (analyticAt_Gamma_of_re_pos (z := 1) (by norm_num)).comp_of_eq hl4 (by norm_num)
  have hfun : (fun z : ℂ => Complex.Gamma (1 / 2 + z) * Complex.Gamma (1 + z)) =
      fun z => (Complex.exp ((-2 * Complex.log 2) * z) * Complex.Gamma (1 + 2 * z)) *
        ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    funext z
    exact duplication_shifted z
  have h1 := taylorCoeff_mul hB hC n
  rw [hfun, taylorCoeff_mul_const, taylorCoeff_mul hE hD n] at h1
  simp only [taylorCoeff_comp_const_add, taylorCoeff_cexp_const_mul, add_zero,
    taylorCoeff_Gamma_one_add_two_mul] at h1
  -- h1 : (Σ_k (−2ℓ)^k/k! * (2^(n−k) tcΓ 1 (n−k))) * √π = Σ_k tcΓ ½ k * tcΓ 1 (n−k)
  unfold gammaHalfCoeff gammaOneCoeff
  calc ∑ k ∈ range (n + 1), taylorCoeff Complex.Gamma (1 / 2) k / ((Real.sqrt Real.pi : ℝ) : ℂ) *
        taylorCoeff Complex.Gamma 1 (n - k)
      = (∑ k ∈ range (n + 1), taylorCoeff Complex.Gamma (1 / 2) k *
          taylorCoeff Complex.Gamma 1 (n - k)) / ((Real.sqrt Real.pi : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = _ := by
        rw [← h1]
        field_simp

/-- ★★★ **The successor form**: `e_{n+1}` from `e_0, …, e_n` and `g_0, …, g_{n+1}`. -/
theorem gammaHalfCoeff_succ (n : ℕ) :
    gammaHalfCoeff (n + 1) =
      (∑ k ∈ range (n + 1 + 1), (-2 * Complex.log 2) ^ k / (k.factorial : ℂ) *
        (2 ^ (n + 1 - k) * gammaOneCoeff (n + 1 - k))) -
      ∑ k ∈ range (n + 1), gammaHalfCoeff k * gammaOneCoeff (n + 1 - k) := by
  have h := gammaHalfCoeff_conv (n + 1)
  rw [Finset.sum_range_succ _ (n + 1), Nat.sub_self, gammaOneCoeff_zero, mul_one] at h
  rw [← h]
  ring

/-! ### Regressions: orders one, two, three -/

theorem gammaHalfCoeff_one :
    gammaHalfCoeff 1 = -((Real.eulerMascheroniConstant : ℂ) + 2 * ((Real.log 2 : ℝ) : ℂ)) := by
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [gammaHalfCoeff_succ 0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlog]
  norm_num [gammaHalfCoeff_zero, gammaOneCoeff_zero, gammaOneCoeff_one]
  ring

theorem gammaHalfCoeff_two :
    gammaHalfCoeff 2 = (((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 +
      Real.pi ^ 2 / 2 : ℝ) : ℂ) / 2 := by
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [gammaHalfCoeff_succ 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlog]
  norm_num [gammaHalfCoeff_zero, gammaHalfCoeff_one, gammaOneCoeff_zero, gammaOneCoeff_one,
    gammaOneCoeff_two]
  ring

/-- `e₂` from the recurrence agrees with DCVIII's `Γ''(½)`. -/
theorem gammaHalfCoeff_two_eq_deriv :
    gammaHalfCoeff 2 =
      deriv (deriv Complex.Gamma) (1 / 2) / (2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
  rw [gammaHalfCoeff_two, deriv_deriv_Gamma_one_half]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  push_cast
  field_simp

theorem gammaHalfCoeff_three :
    gammaHalfCoeff 3 = (7 * ((gammaThirdOne : ℝ) : ℂ) +
      ((7 * Real.eulerMascheroniConstant ^ 3 + 7 * Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 -
        (Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
        3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2 : ℝ) : ℂ)) / 6 := by
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := (Complex.ofNat_log).symm
  rw [gammaHalfCoeff_succ 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hlog]
  norm_num [gammaHalfCoeff_zero, gammaHalfCoeff_one, gammaHalfCoeff_two, gammaOneCoeff_zero,
    gammaOneCoeff_one, gammaOneCoeff_two, gammaOneCoeff_three]
  ring

/-- `e₃` from the recurrence agrees with DCLXXII's third-order duplication relation. -/
theorem gammaHalfCoeff_three_eq_deriv :
    gammaHalfCoeff 3 =
      deriv (deriv (deriv Complex.Gamma)) (1 / 2) / (6 * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
  rw [gammaHalfCoeff_three, deriv_deriv_deriv_Gamma_one_half]
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hG : deriv (deriv (deriv Complex.Gamma)) 1 = ((gammaThirdOne : ℝ) : ℂ) := by
    rw [← gammaOneLogMoment_three_eq, gammaOneLogMoment_eq_iterate]
    rfl
  rw [hG]
  push_cast
  field_simp

end Grammar
