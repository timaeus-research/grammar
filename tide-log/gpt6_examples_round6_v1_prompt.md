You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 73a2401, 947 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-5 targets ALL landed: (1) blow-up Laurent data (DCX), (2) the depth-two Gaussian two-term expansion (DCXI: −γ as a renormalised integral; DCXII: the J(ε) estimate, Z_N = J(1/2N)/√(2πN), explicit remainder, IsBigO), (3) the domination adapter for DCIX (DCXIII: explicit logSqDomBound, the averaged theorem on a ball, averaged_naiveBayes_polar). This is round 6.

## HEADLINES rows DCX–DCXIII
| **DCX** | ★★★ **THE LAURENT DATA OF THE BLOW-UP ZETA FUNCTION AT ITS DOUBLE POLE (u944; examples_slop §4; Astra round-5 target 1)**: `blowupZeta w = 2^{3w+1}Γ(w+½)²` (the closed form of DXC), `blowupZetaReg t = 2^{3t−½}Γ(1+t)²` (`blowupZeta_eq_reg : ζ(−½+t) = reg t / t²` for `t ≠ 0`, via `Gamma_add_one`; `differentiableOn_blowupZetaReg` on `Re t > −1`), `exp_neg_half_log_two`, `blowupZetaReg_zero = 1/√2`, `hasDerivAt_blowupZetaReg_zero` (derivative `(3log2 − 2γ)/√2` from `Γ(1) = 1`, `Γ'(1) = −γ`); ★★★ `blowupZeta_laurent : ζ(−½ + t) − (1/√2)/t² − ((3log2−2γ)/√2)/t = O(1)` on `𝓝[≠] 0` (from the library's `pole_taylor_isBigO_one` with `n = 2`): the population polar data `A_{½,2} = 1/√2`, `A_{½,1} = (3log2 − 2γ)/√2` of the blow-up example, previously a derivation in the note — no derivative of `Γ` at its pole (regularise first). The Laplace polynomial `√(π/2)[log N + 5log2 − γ]` at `N^{−1/2}` remains a derivation (transfer). Also the round-5 consult `tide-log/gpt6_examples_round5_v1.md` (fidelity of DCVII–DCIX; DCIX's interface endorsed with a shrinking-cutoff domination adapter as the geometric bridge — negative moments of `M(λ)` needed, envelope `W(1+M^{−2r})(1+|log M|⁴)`; targets: this Laurent unit, the depth-two Gaussian two-term expansion via `∫₀^∞(e^{−v} − 1_{(0,1)})/v = −γ` and `J(ε)`, the domination adapter; the convention table for the three coefficient systems). Lean gotchas: `HasDerivAt.mul hG hG` for the SAME function produces a Pi-mul function whose instance path does not unify with a stated `HasDerivAt` type — let the product's function be inferred (`have hprod := hE.mul (hG.mul hG)`) and transfer to the named function by `congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)`, then `simp only [Pi.mul_apply]` in the derivative goal; `HasDerivAt.comp_const_add` keeps the instance path of Mathlib's `hasDerivAt_Gamma_one`; `beta_reduce` before rewriting inside a `congr'` goal. | BlowUpLaurent.lean |
| **DCXI** | ★★★ **EULER'S CONSTANT AS A RENORMALISED INTEGRAL (u945; examples_slop §2, the depth-two Gaussian expansion; Astra round-5 target 2, step 1)**: `integral_exp_neg_log` (`∫₀^∞ e^{−v} log v = Γ'(1) = −γ` as a real integral, from Mathlib's `hasDerivAt_GammaIntegral` and `hasDerivAt_Gamma_one`), `logKernel v u = 1_{(1,v]}(u)/u − 1_{(v,1]}(u)/u` (measurable, `integral_kernel_log : ∫₀^∞ logKernel v u du = log v`, `integral_abs_kernel_log : … = |log v|`, `integrableOn_logKernel`), `integral_exp_kernel` (the inner `v`-integral `∫₀^∞ e^{−v} logKernel v u dv = (e^{−u} − 1_{(0,1]}(u))/u`, by cases `u > 1`/`u ≤ 1` with `integral_exp_neg_Ioi` and `integral_exp`), `integrableOn_exp_neg_abs_log`; ★★★ `integral_renormalised_exp_inv : ∫₀^∞ (e^{−u} − 1_{(0,1]}(u))/u du = −γ` by Fubini (`integrable_prod_iff'` + `integral_integral_swap`) on `e^{−v} logKernel v u` over `(0,∞)²` — the constant behind `J(ε) = log(4/ε) − γ + O(ε log(1/ε))` and hence the two-term expansion `Z_N = (log N + 3log2 − γ)/√(2πN) + O(N^{−3/2}log N)` of the depth-two Gaussian DLN (step 2, the `J(ε)` estimate, to follow). Lean gotchas: `Ioc_eq_empty` needs a `show ¬ a < b from …` to fix which interval it rewrites; `intervalIntegral.intervalIntegrable_inv` takes a `ContinuousOn` second argument; `Integrable.add` of two `IntegrableOn` facts is an `Integrable` — call `IntegrableOn.congr_fun` explicitly; an `Integrable` witness for `fun x => uncurry g (x, v)` transfers from the lambda form by `.congr (Eventually.of_forall fun x => rfl)`. | RenormalisedExpIntegral.lean |
| **DCXII** | ★★★ **THE DEPTH-TWO GAUSSIAN DLN TWO-TERM EXPANSION (u946; examples_slop §2, eq. dln_gauss at `L = 2`; Astra round-5 target 2, step 2 — COMPLETE)**: `gaussJ ε = ∫₀^∞ 2e^{−w²}/√(w² + ε) dw` (the consult's `J(ε) = ∫₀^∞ e^{−v}/√(v(v+ε)) dv` in the variable `v = w²`); the elementary part `integral_elem : ∫₀¹ 2/√(w² + ε) = 2 log((1 + √(1+ε))/√ε)` (antiderivative `2 log(w + √(w² + ε))`, no improper endpoint in the `w` variable) with `elem_bounds : log(4/ε) ≤ … ≤ log(4/ε) + ε`; the pointwise gap `gap_bounds : 0 ≤ 2/w − 2/√(w²+ε) ≤ 2ε/(w(w²+ε))`; the remainders `rem_inner_le : |∫₀¹ (e^{−w²} − 1)(2/√(w²+ε) − 2/w)| ≤ ε(log(1/ε) + 1)` (majorant `2εw/(w²+ε)`, `integral_majorant`) and `rem_outer_le : |∫₁^∞ e^{−w²}(2/√(w²+ε) − 2/w)| ≤ ε` (majorant `2εe^{−w}`, `2/e ≤ 1`); the renormalised constant transported by `integral_comp_rpow_Ioi_of_pos` (`integral_renormalised_sq : ∫₀^∞ (e^{−w²} − 1_{(0,1]}(w))·2/w = −γ`) and split at `w = 1` (`renorm_split`); ★★ `gaussJ_two_term : |J(ε) − (log(4/ε) − γ)| ≤ ε(log(1/ε) + 3)` for `0 < ε ≤ 1`; ★★ `gaussLaplace2_eq_J : Z_N = J(1/(2N))/√(2πN)` (from DCVII's conditional reduction by `integral_comp_abs` and `integral_comp_mul_left_Ioi`, `x = √2 w`); ★★ `gaussLaplace2_two_term_bound : |Z_N − (log N + 3log2 − γ)/√(2πN)| ≤ (log(2N) + 3)/(2N√(2πN))` for `N ≥ 1/2`; ★★★ `gaussLaplace2_two_term : Z_N − (log N + 3log2 − γ)/√(2πN) = O(N^{−3/2} log N)` at `N → ∞`. This closes eq. (dln_gauss) at `L = 2` formally, with the constant `3 log 2 − γ` and an explicit remainder. Lean gotchas: `div_le_div_iff₀` (not `_of_pos`) is the two-sided division comparison; `generalize √(…) = s at h₁ h₂ ⊢` then `subst` of `ε = s² − w²` lets `nlinarith` see the sqrt as a free atom; `Real.sqrt_mul` needs `(x := …)` when several products of the same shape are present; fold an integral into a `set`/`clear_value` atom BEFORE `field_simp`, which otherwise rewrites under the binder; `rw [one_div]` inside an rpow exponent `1/2` — use `inv_eq_one_div` on the intended side; `Measure.integrableOn_of_bounded (M := C)` with `Real.volume_Ioc` + `ENNReal.ofReal_ne_top` for bounded functions on `Ioc`. | GaussianDepthTwoExpansion.lean |
| **DCXIII** | ★★★ **THE DOMINATION ADAPTER FOR THE AVERAGED FIBRE THEOREM (u947; examples_slop §6; Astra round-5 target 3 — COMPLETE; all round-5 targets done)**: `integral_rpow_mul_abs_log_Ioc : ∫₀¹ t^a|log t| = 1/(a+1)²` (from `integral_cpow_log_Ioc` at real `s = −a/2`); `norm_deriv_mellinIoc_le` (`‖g‖ ≤ Ct^b` on `(0,1]`, `Re s ≤ σ`, `b − 2σ > −1` ⇒ `‖(Mg)'(s)‖ ≤ 2C/(b−2σ+1)²`); `norm_deriv_mellinIoc_cutoff_le` (`‖g‖ ≤ K` on `(M,1]`, `Re s ≤ ½ + r` ⇒ `‖(M[1_{(M,1]}g])'(s)‖ ≤ K|log M|M^{−2r}/r` — the negative moment of the cutoff predicted by the consult); `re_le_of_mem_ball_half`; `norm_logSqOddAmp_le`, `measurable_logSqOddAmp`, `norm_logSqAmp_symm_cutoff_le` (even amplitude `≤ (2(|ℓ|+|log M|)²+|c|)(2|φ(0)|+2L)` on `(M,1]`); the explicit constant `logSqDomBound ℓ c b M L φ₀ r` (four pieces, polynomial in `ℓ, |c|, |b|, L, |φ₀|, |log M|` times `(1 + M^{−2r})`); ★★ `norm_deriv_logSqHolo_le : ‖(logSqHolo ℓ c b M φ)'(s)‖ ≤ logSqDomBound …` on `|s − ½| < r`, `0 < r < ½` (with `δ = (½ − r)/2` for the remainder piece); `averaged_logSq_polar_ball` (DCIX on a ball around `½` with one dominating function, per the consult's recommendation); `integral_logSqMellinFull_eq` (averaged fibre Mellin transform = averaged continuation on `Re s < ½`); ★★★ `averaged_naiveBayes_polar`: for a family of fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)` with `0 < M_λ ≤ 1`, `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, integrable polar coefficients and integrable `logSqDomBound` (+ measurability/integrability of the remainders in `λ`), the averaged continuation has principal part `polarPart 2 (logSqAvgA …)` at `½`: `C̄_{½,3} = −∫φ_λ(0)`, `C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`. The analytic domination hypothesis of DCIX is now derived from the fibre data; what remains for the actual naive Bayes envelope is the facewise verification of the integrability of `logSqDomBound` (the consult's negative-moment condition `2rβ + η < a`). Lean gotchas: `abs_add_le` (not `abs_add`) on this pin; `pow_le_pow_left₀`; `intervalIntegral.intervalIntegrable_rpow (Or.inr …)` for negative exponents away from `0`; `integral_congr_ae` per-point goals need `beta_reduce` before `rw`. | LogSqDominationAdapter.lean |

## Public statements of the four new files (verbatim signatures)
### Grammar/BlowUpLaurent.lean
```lean
/-- The closed-form zeta function of the blow-up example. -/
noncomputable def blowupZeta (w : ℂ) : ℂ

/-- The regularised function `t² ζ(−½ + t) = 2^{3t − ½} Γ(1 + t)²`, analytic at `0`. -/
noncomputable def blowupZetaReg (t : ℂ) : ℂ

/-- `ζ(−½ + t) = blowupZetaReg t / t²` for `t ≠ 0`. -/
theorem blowupZeta_eq_reg {t : ℂ} (ht : t ≠ 0) :
    blowupZeta (-1 / 2 + t) = blowupZetaReg t / t ^ 2 := by
  unfold blowupZeta blowupZetaReg
  have hG

theorem differentiableOn_blowupZetaReg :
    DifferentiableOn ℂ blowupZetaReg {t : ℂ | -1 < t.re} := by
  intro t ht
  have ht' : 0 < (1 + t).re

/-- `exp(−½ log 2) = 1/√2`. -/
theorem exp_neg_half_log_two :
    Complex.exp ((-1 / 2 : ℂ) * Real.log 2) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  have h : Real.exp (-1 / 2 * Real.log 2) = 1 / Real.sqrt 2

theorem blowupZetaReg_zero : blowupZetaReg 0 = ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- The derivative of the regularised function at `0`: `(3 log 2 − 2γ)/√2`. -/
theorem hasDerivAt_blowupZetaReg_zero :
    HasDerivAt blowupZetaReg
      (((3 * Real.log 2 - 2 * Real.eulerMascheroniConstant) / Real.sqrt 2 : ℝ) : ℂ) 0 := by
  have hE : HasDerivAt (fun t : ℂ => Complex.exp ((3 * t - 1 / 2) * Real.log 2))
      (Complex.exp ((3 * (0 : ℂ) - 1 / 2) * Real.log 2) * (3 * Real.log 2)) 0 := by
    have hl : HasDerivAt (fun t : ℂ => (3 * t - 1 / 2) * Real.log 2) (3 * Real.log 2) 0 := by
      have := (((hasDerivAt_id (0 : ℂ)).const_mul (3 : ℂ)).sub_const (1 / 2)).mul_const
        ((Real.log 2 : ℝ) : ℂ)
      refine this.congr_deriv ?_
      simp
    exact (Complex.hasDerivAt_exp _).comp 0 hl
  have hG : HasDerivAt (fun t : ℂ => Complex.Gamma (1 + t)) (-Real.eulerMascheroniConstant) 0 := by
    have hg : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ)) (1 + 0) := by
      simpa using Complex.hasDerivAt_Gamma_one
    exact hg.comp_const_add 1
  have hprod := hE.mul (hG.mul hG)
  refine (hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · first
    | rfl
    | simp only [blowupZetaReg, Pi.mul_apply, sq]
  simp only [Pi.mul_apply]
  rw [show (3 * (0 : ℂ) - 1 / 2) = -1 / 2 by ring, exp_neg_half_log_two, add_zero,
    Complex.Gamma_one]
  push_cast
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0

/-- ★★★ **The Laurent data of the blow-up zeta function at `w = −½`**:
`ζ(−½ + t) = (1/√2)/t² + ((3 log 2 − 2γ)/√2)/t + O(1)`, i.e. `A_{½,2} = 1/√2`,
`A_{½,1} = (3 log 2 − 2γ)/√2`. -/
theorem blowupZeta_laurent :
    (fun t : ℂ => blowupZeta (-1 / 2 + t) - ((1 / Real.sqrt 2 : ℝ) : ℂ) / t ^ 2 -
      (((3 * Real.log 2 - 2 * Real.eulerMascheroniConstant) / Real.sqrt 2 : ℝ) : ℂ) / t)
      =O[𝓝[≠] (0 : ℂ)] fun _ => (1 : ℂ) := by
  have hU : {t : ℂ | -1 < t.re} ∈ 𝓝 (0 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  have h := pole_taylor_isBigO_one hU differentiableOn_blowupZetaReg 2
  refine h.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun t ht => ?_
  have ht0 : t ≠ 0
```
### Grammar/RenormalisedExpIntegral.lean
```lean
/-- `∫₀^∞ e^{−v} log v dv = Γ'(1) = −γ`. -/
theorem integral_exp_neg_log :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v = -Real.eulerMascheroniConstant := by
  have h1 : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
        ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) 1 := by
    have h := Complex.hasDerivAt_GammaIntegral (s := 1) (by norm_num)
    refine h.congr_of_eventuallyEq ?_
    have hopen : {s : ℂ | 0 < s.re} ∈ nhds (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact Complex.Gamma_eq_integral hs
  have huniq := h1.unique Complex.hasDerivAt_Gamma_one
  have hcast : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v : ℝ) : ℂ)

/-- The kernel `(1_{u ≤ v} − 1_{u ≤ 1})/u` written as an indicator of the interval between `1` and
`v`, with sign. -/
noncomputable def logKernel (v u : ℝ) : ℝ

theorem measurable_logKernel : Measurable (Function.uncurry logKernel)

/-- `∫₀^∞ logKernel v u du = log v` for `v > 0`. -/
theorem integral_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), logKernel v u = Real.log v := by
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · have e : ∀ u ∈ Ioi (0 : ℝ), (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u = (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u := by
      intro u _
      rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 1 v = Ioc 1 v from inter_eq_right.2 fun u hu => lt_trans one_pos hu.1,
      ← intervalIntegral.integral_of_le h, integral_inv_of_pos one_pos hv, div_one]
  · have e : ∀ u ∈ Ioi (0 : ℝ), (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u = -(Ioc v 1).indicator (fun u : ℝ => u⁻¹) u

/-- The inner `v`-integral: `∫₀^∞ e^{−v} logKernel v u dv = (e^{−u} − 1_{u ≤ 1})/u` for `u > 0`. -/
theorem integral_exp_kernel {u : ℝ} (hu : 0 < u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * logKernel v u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u := by
  unfold logKernel
  -- `u ∈ Ioc 1 v ↔ 1 < u ∧ u ≤ v`; `u ∈ Ioc v 1 ↔ v < u ∧ u ≤ 1`
  have e : ∀ v ∈ Ioi (0 : ℝ), Real.exp (-v) * ((Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
      (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u) =
      (if 1 < u then (Ici u).indicator (fun v => Real.exp (-v)) v else 0) * u⁻¹ -
        (if u ≤ 1 then (Iio u).indicator (fun v => Real.exp (-v)) v else 0) * u⁻¹ := by
    intro v _
    simp only [indicator, mem_Ioc, mem_Ici, mem_Iio]
    by_cases h1 : 1 < u <;> by_cases h2 : u ≤ v <;> by_cases h3 : v < u <;> by_cases h4 : u ≤ 1 <;>
      simp [h1, h2, h3, h4]
  rw [setIntegral_congr_fun measurableSet_Ioi e]
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0 : ℝ) one_pos
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp
  have hA : IntegrableOn (fun v : ℝ => (if 1 < u then (Ici u).indicator (fun v => Real.exp (-v)) v
      else 0) * u⁻¹) (Ioi 0) := by
    split_ifs
    · exact (hexp.indicator measurableSet_Ici).mul_const _
    · simp
  have hB : IntegrableOn (fun v : ℝ => (if u ≤ 1 then (Iio u).indicator (fun v => Real.exp (-v)) v
      else 0) * u⁻¹) (Ioi 0) := by
    split_ifs
    · exact (hexp.indicator measurableSet_Iio).mul_const _
    · simp
  rw [integral_sub hA hB, integral_mul_const, integral_mul_const]
  rcases lt_or_ge 1 u with h1 | h1
  · have h2 : ¬ u ≤ 1 := not_le.2 h1
    simp only [if_pos h1, if_neg h2, integral_zero, zero_mul, sub_zero]
    rw [setIntegral_indicator measurableSet_Ici,
      show Ioi (0 : ℝ) ∩ Ici u = Ici u from inter_eq_right.2 fun v hv => lt_of_lt_of_le hu hv,
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi, indicator_of_notMem (by
        simp only [mem_Ioc, not_and, not_le]; intro _; exact h1), sub_zero, div_eq_mul_inv]
  · have h2 : ¬ 1 < u := not_lt.2 h1
    simp only [if_neg h2, if_pos h1, integral_zero, zero_mul, zero_sub]
    rw [setIntegral_indicator measurableSet_Iio,
      show Ioi (0 : ℝ) ∩ Iio u = Ioo 0 u from rfl, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hu.le,
      indicator_of_mem (s := Ioc (0 : ℝ) 1) (f := (1 : ℝ → ℝ)) ⟨hu, h1⟩]
    have : ∫ v in (0 : ℝ)..u, Real.exp (-v) = 1 - Real.exp (-u) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := u) (f

/-- `∫₀^∞ |logKernel v u| du = |log v|` for `v > 0`. -/
theorem integral_abs_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), |logKernel v u| = |Real.log v| := by
  unfold logKernel
  rcases le_or_gt 1 v with h | h
  · have e : ∀ u ∈ Ioi (0 : ℝ), |(Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u| = (Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u := by
      intro u hu
      rw [Ioc_eq_empty (show ¬ v < (1 : ℝ) from not_lt.2 h)]
      simp only [indicator_empty, sub_zero]
      exact abs_of_nonneg
        (indicator_nonneg (fun u hu => inv_nonneg.2 (le_trans zero_le_one hu.1.le)) u)
    rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 1 v = Ioc 1 v from inter_eq_right.2 fun u hu => lt_trans one_pos hu.1,
      ← intervalIntegral.integral_of_le h, integral_inv_of_pos one_pos hv, div_one,
      abs_of_nonneg (Real.log_nonneg h)]
  · have e : ∀ u ∈ Ioi (0 : ℝ), |(Ioc 1 v).indicator (fun u : ℝ => u⁻¹) u -
        (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u| = (Ioc v 1).indicator (fun u : ℝ => u⁻¹) u

/-- The kernel is integrable in `u` on `(0, ∞)` for every `v > 0`. -/
theorem integrableOn_logKernel {v : ℝ} (hv : 0 < v) : IntegrableOn (logKernel v) (Ioi 0) := by
  unfold logKernel
  have h1 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc 1 v) := by
    rcases le_or_gt 1 v with h | h
    · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le h]
      exact intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le h] at hx; exact ne_of_gt (lt_of_lt_of_le one_pos hx.1)) continuousOn_id
    · rw [Ioc_eq_empty (show ¬ (1 : ℝ) < v from not_lt.2 h.le)]
      exact integrableOn_empty
  have h2 : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc v 1)

/-- `e^{−v}|log v|` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_abs_log :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * |Real.log v|) (Ioi 0) := by
  have hint : IntegrableOn (fun v : ℝ => (2 * v ^ (-(1 / 2 : ℝ)) + v) * Real.exp (-v)) (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_rpow (s := -(1 / 2 : ℝ)) (p := 1) (by norm_num) one_pos
    have h2 := integrableOn_rpow_mul_exp_neg_rpow (s := 1) (p := 1) (by norm_num) one_pos
    refine IntegrableOn.congr_fun ((h1.const_mul 2).add h2) (fun v hv => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_one]
    ring
  refine hint.mono' (by fun_prop : Measurable fun v : ℝ =>
    Real.exp (-v) * |Real.log v|).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun v hv => ?_
  have hv' : (0 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := abs_log_le_rpow v hv'
  calc Real.exp (-v) * |Real.log v| ≤ Real.exp (-v) * (2 * v ^ (-(1 / 2 : ℝ)) + v) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = (2 * v ^ (-(1 / 2 : ℝ)) + v) * Real.exp (-v)

/-- ★★★ **Euler's constant as a renormalised integral**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u))/u du = −γ`. -/
theorem integral_renormalised_exp_inv :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u =
      -Real.eulerMascheroniConstant := by
  set g : ℝ → ℝ → ℝ := fun u v => Real.exp (-v) * logKernel v u with hg
  have hmeas : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have : Function.uncurry g = fun p : ℝ × ℝ => Real.exp (-p.2) *
        Function.uncurry logKernel (p.2, p.1) := by
      funext p; rfl
    rw [this]
    exact ((Real.measurable_exp.comp measurable_snd.neg).mul
      (measurable_logKernel.comp (measurable_snd.prodMk measurable_fst)))
  have hint : Integrable (Function.uncurry g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun v hv => ?_
      have hv' : (0 : ℝ) < v := hv
      refine ((integrableOn_logKernel hv').const_mul (Real.exp (-v))).congr
        (Eventually.of_forall fun x => ?_)
      rfl
    · have e : ∀ v ∈ Ioi (0 : ℝ), (∫ u in Ioi (0 : ℝ), ‖Function.uncurry g (u, v)‖) =
          Real.exp (-v) * |Real.log v| := by
        intro v hv
        have hv' : (0 : ℝ) < v := hv
        simp only [hg, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        rw [integral_const_mul, integral_abs_kernel_log hv']
      exact (integrableOn_exp_neg_abs_log.congr_fun (fun v hv => (e v hv).symm) measurableSet_Ioi)
  have hswap := integral_integral_swap hint
  -- the two iterated integrals
  have hL : ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), g u v = -Real.eulerMascheroniConstant := by
    rw [← integral_exp_neg_log]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv' : (0 : ℝ) < v := hv
    simp only [hg]
    rw [integral_const_mul, integral_kernel_log hv']
  have hR : ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), g u v =
      ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u
```
### Grammar/GaussianDepthTwoExpansion.lean
```lean
/-- `J(ε) = ∫₀^∞ 2 e^{−w²}/√(w² + ε) dw`. -/
noncomputable def gaussJ (ε : ℝ) : ℝ

/-- `∫₀¹ 2/√(w² + ε) dw = 2 log((1 + √(1 + ε))/√ε)`. -/
theorem integral_elem {ε : ℝ} (hε : 0 < ε) :
    ∫ w in (0 : ℝ)..1, 2 / Real.sqrt (w ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
  have hderiv : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun w => 2 * Real.log (w + Real.sqrt (w ^ 2 + ε)))
      (2 / Real.sqrt (w ^ 2 + ε)) w := by
    intro w hw
    rw [uIcc_of_le zero_le_one] at hw
    have hpos : 0 < w ^ 2 + ε := by positivity
    have hsq : 0 < Real.sqrt (w ^ 2 + ε) := Real.sqrt_pos.2 hpos
    have hne : w + Real.sqrt (w ^ 2 + ε) ≠ 0 := by linarith [hw.1]
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + ε) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const ε
    have h2 : HasDerivAt (fun w : ℝ => Real.sqrt (w ^ 2 + ε))
        (1 / (2 * Real.sqrt (w ^ 2 + ε)) * (2 * w)) w := (Real.hasDerivAt_sqrt hpos.ne').comp w h1
    have h3 : HasDerivAt (fun w : ℝ => w + Real.sqrt (w ^ 2 + ε))
        (1 + 1 / (2 * Real.sqrt (w ^ 2 + ε)) * (2 * w)) w := (hasDerivAt_id w).add h2
    have h4 := ((Real.hasDerivAt_log hne).comp w h3).const_mul 2
    refine h4.congr_deriv ?_
    have hs2 : Real.sqrt (w ^ 2 + ε) ^ 2 = w ^ 2 + ε := Real.sq_sqrt hpos.le
    field_simp
    nlinarith [hs2]
  have hint : IntervalIntegrable (fun w => 2 / Real.sqrt (w ^ 2 + ε)) volume 0 1

/-- `log(4/ε) ≤ 2 log((1 + √(1+ε))/√ε) ≤ log(4/ε) + ε` for `0 < ε ≤ 1`. -/
theorem elem_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log (4 / ε) ≤ 2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ∧
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ≤ Real.log (4 / ε) + ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : 1 ≤ Real.sqrt (1 + ε) := Real.one_le_sqrt.2 (by linarith)
  have h2 : Real.sqrt (1 + ε) ≤ 1 + ε / 2 := Real.sqrt_one_add_le (by linarith)
  have e : 2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) =
      Real.log ((1 + Real.sqrt (1 + ε)) ^ 2 / ε) := by
    have h : ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) ^ 2 = (1 + Real.sqrt (1 + ε)) ^ 2 / ε := by
      rw [div_pow, Real.sq_sqrt hε.le]
    rw [← h, Real.log_pow]; push_cast; ring
  rw [e]
  constructor
  · refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff_of_pos_right hε]
    nlinarith
  · have h3 : (1 + Real.sqrt (1 + ε)) ^ 2 / ε ≤ 4 / ε * (1 + ε) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]
      nlinarith
    calc Real.log ((1 + Real.sqrt (1 + ε)) ^ 2 / ε) ≤ Real.log (4 / ε * (1 + ε)) :=
          Real.log_le_log (by positivity) h3
      _ = Real.log (4 / ε) + Real.log (1 + ε) := Real.log_mul (by positivity) (by positivity)
      _ ≤ Real.log (4 / ε) + ε

/-- `0 ≤ 2/w − 2/√(w² + ε) ≤ 2ε/(w(w² + ε))` for `w, ε > 0`. -/
theorem gap_bounds {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w) :
    0 ≤ 2 / w - 2 / Real.sqrt (w ^ 2 + ε) ∧
      2 / w - 2 / Real.sqrt (w ^ 2 + ε) ≤ 2 * ε / (w * (w ^ 2 + ε)) := by
  have hpos : 0 < w ^ 2 + ε := by positivity
  have hs2 : Real.sqrt (w ^ 2 + ε) ^ 2 = w ^ 2 + ε := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt (w ^ 2 + ε) := Real.sqrt_pos.2 hpos
  have hws : w ≤ Real.sqrt (w ^ 2 + ε) := by
    rw [Real.le_sqrt hw.le hpos.le]; linarith
  generalize Real.sqrt (w ^ 2 + ε) = s at hs2 hs0 hws ⊢
  constructor
  · have : 2 / s ≤ 2 / w := div_le_div_of_nonneg_left (by norm_num) hw hws
    linarith
  · rw [div_sub_div _ _ hw.ne' hs0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hε' : ε = s ^ 2 - w ^ 2

/-- `0 ≤ 1 − e^{−w²} ≤ w²`. -/
theorem one_sub_exp_neg_sq_bounds (w : ℝ) :
    0 ≤ 1 - Real.exp (-w ^ 2) ∧ 1 - Real.exp (-w ^ 2) ≤ w ^ 2

/-- The inner remainder integrand is bounded by `2εw/(w² + ε)`. -/
theorem rem_inner_bound {ε w : ℝ} (hε : 0 < ε) (hw : 0 < w) :
    |(Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤
      2 * ε * w / (w ^ 2 + ε) := by
  obtain ⟨h1, h2⟩ := gap_bounds hε hw
  obtain ⟨h3, h4⟩ := one_sub_exp_neg_sq_bounds w
  rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  calc -(Real.exp (-w ^ 2) - 1) * -(2 / Real.sqrt (w ^ 2 + ε) - 2 / w)
      ≤ w ^ 2 * (2 * ε / (w * (w ^ 2 + ε))) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    _ = 2 * ε * w / (w ^ 2 + ε)

/-- `∫₀¹ 2εw/(w² + ε) dw = ε (log(1 + ε) − log ε)`. -/
theorem integral_majorant {ε : ℝ} (hε : 0 < ε) :
    ∫ w in (0 : ℝ)..1, 2 * ε * w / (w ^ 2 + ε) = ε * (Real.log (1 + ε) - Real.log ε) := by
  have hderiv : ∀ w ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun w => ε * Real.log (w ^ 2 + ε))
      (2 * ε * w / (w ^ 2 + ε)) w := by
    intro w _
    have hpos : 0 < w ^ 2 + ε := by positivity
    have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + ε) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const ε
    have h2 := ((Real.hasDerivAt_log hpos.ne').comp w h1).const_mul ε
    refine h2.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun w => 2 * ε * w / (w ^ 2 + ε)) volume 0 1

/-- `|∫₀¹ (e^{−w²} − 1)(2/√(w² + ε) − 2/w) dw| ≤ ε (log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem rem_inner_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤
      ε * (Real.log (1 / ε) + 1) := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * ε * w / (w ^ 2 + ε)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun w : ℝ => 2 * ε * w) (uIcc 0 1)).div (by fun_prop)
        fun w _ => by positivity)
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun w => (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_majorant hε]
    have h1 : Real.log (1 + ε) ≤ 1

/-- `|∫₁^∞ e^{−w²}(2/√(w² + ε) − 2/w) dw| ≤ ε` for `ε > 0`. -/
theorem rem_outer_le {ε : ℝ} (hε : 0 < ε) :
    |∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)| ≤ ε := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * ε * Real.exp (-w)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 one_pos).const_mul (2 * ε)) (fun w _ => ?_) measurableSet_Ioi
    simp
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun w => Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w)) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_const_mul, integral_exp_neg_Ioi]
    have he : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have h2 : Real.exp (-1) * 2 ≤ 1 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos 1)]; linarith
    nlinarith
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun w hw => ?_
    have hw : (1 : ℝ) < w := hw
    have hw0 : 0 < w := by linarith
    obtain ⟨h1, h2⟩ := gap_bounds hε hw0
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonpos (by linarith)]
    have h3 : Real.exp (-w ^ 2) ≤ Real.exp (-w) := Real.exp_le_exp.2 (by nlinarith)
    have h4 : 2 * ε / (w * (w ^ 2 + ε)) ≤ 2 * ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hw.le (by nlinarith : (1 : ℝ) ≤ w ^ 2 + ε) zero_le_one hw0.le]
    calc Real.exp (-w ^ 2) * -(2 / Real.sqrt (w ^ 2 + ε) - 2 / w) ≤ Real.exp (-w) * (2 * ε) :=
          mul_le_mul h3 (by linarith) (by linarith) (Real.exp_pos _).le
      _ = 2 * ε * Real.exp (-w)

/-- `∫₀^∞ (e^{−w²} − 1_{(0,1]}(w))·2/w dw = −γ`. -/
theorem integral_renormalised_sq :
    ∫ w in Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w) =
      -Real.eulerMascheroniConstant := by
  rw [← integral_renormalised_exp_inv, ← integral_comp_rpow_Ioi_of_pos
    (g := fun u => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u) two_pos]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw : (0 : ℝ) < w := hw
  have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (w ^ 2) = (Ioc 0 1).indicator 1 w := by
    by_cases h : w ≤ 1
    · have hm : w ^ 2 ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
      have hm' : w ∈ Ioc (0 : ℝ) 1 := ⟨hw, h⟩
      rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
    · have h' := not_le.1 h
      have hm : w ^ 2 ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by nlinarith))
      have hm' : w ∉ Ioc (0 : ℝ) 1

theorem measurable_renorm :
    Measurable fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w)

theorem integrableOn_renorm_inner :
    IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) measurable_renorm.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun w hw => ?_
  obtain ⟨h3, h4⟩ := one_sub_exp_neg_sq_bounds w
  have hw0 : 0 < w := hw.1
  rw [Real.norm_eq_abs, indicator_of_mem hw, Pi.one_apply, abs_mul, abs_of_nonpos (by linarith),
    abs_of_pos (by positivity)]
  calc -(Real.exp (-w ^ 2) - 1) * (2 / w) ≤ w ^ 2 * (2 / w) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * w := by field_simp
    _ ≤ 2

theorem integrableOn_renorm_outer :
    IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioi 1) := by
  have hmaj : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 one_pos).const_mul 2) (fun w _ => ?_) measurableSet_Ioi
    simp
  refine hmaj.mono' measurable_renorm.aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun w hw => ?_
  have hw : (1 : ℝ) < w := hw
  have hw0 : 0 < w := by linarith
  have hm : w ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hw)
  rw [Real.norm_eq_abs, indicator_of_notMem hm, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity)]
  have h3 : Real.exp (-w ^ 2) ≤ Real.exp (-w) := Real.exp_le_exp.2 (by nlinarith)
  have h4 : 2 / w ≤ 2 := by rw [div_le_iff₀ hw0]; linarith
  calc Real.exp (-w ^ 2) * (2 / w) ≤ Real.exp (-w) * 2 :=
        mul_le_mul h3 h4 (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-w)

/-- `∫₀¹ (e^{−w²} − 1)·2/w dw + ∫₁^∞ e^{−w²}·2/w dw = −γ`. -/
theorem renorm_split :
    (∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / w)) +
      ∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / w) = -Real.eulerMascheroniConstant

theorem integrableOn_gaussJ {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioi 0) := by
  have hmaj : Integrable fun w : ℝ => 2 / Real.sqrt ε * Real.exp (-1 * w ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine (hmaj.mono' (Measurable.aestronglyMeasurable ?_) ?_).integrableOn
  · refine (by fun_prop : Measurable fun w : ℝ => 2 * Real.exp (-w ^ 2)).div (by fun_prop)
  · refine Eventually.of_forall fun w => ?_
    have hs : Real.sqrt ε ≤ Real.sqrt (w ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w])
    have hs0 : 0 < Real.sqrt ε

theorem integrableOn_elem {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun w : ℝ => 2 / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1)

/-- ★★ **The two-term expansion of `J`**:
`|J(ε) − (log(4/ε) − γ)| ≤ ε (log(1/ε) + 3)` for `0 < ε ≤ 1`. -/
theorem gaussJ_two_term {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |gaussJ ε - (Real.log (4 / ε) - Real.eulerMascheroniConstant)| ≤
      ε * (Real.log (1 / ε) + 3) := by
  have hA := integrableOn_gaussJ hε
  have hA1 : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1) :=
    hA.mono_set Ioc_subset_Ioi_self
  have hA2 : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) (Ioi 1) :=
    hA.mono_set (Ioi_subset_Ioi zero_le_one)
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - 1) * (2 / w)) (Ioc 0 1) :=
    integrableOn_renorm_inner.congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun w : ℝ => Real.exp (-w ^ 2) * (2 / w)) (Ioi 1) :=
    integrableOn_renorm_outer.congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : gaussJ ε = (∫ w in Ioc (0 : ℝ) 1, 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε)) +
      ∫ w in Ioi (1 : ℝ), 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) := by
    unfold gaussJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ w in Ioc (0 : ℝ) 1, 2 / Real.sqrt (w ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  have hR1 : ∫ w in Ioc (0 : ℝ) 1, 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) =
      (∫ w in Ioc (0 : ℝ) 1, 2 / Real.sqrt (w ^ 2 + ε)) +
        (∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / w)) +
        ∫ w in Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) := by
    have e : ∀ w ∈ Ioc (0 : ℝ) 1, (Real.exp (-w ^ 2) - 1) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) =
        2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) - 2 / Real.sqrt (w ^ 2 + ε) -
          (Real.exp (-w ^ 2) - 1) * (2 / w) := fun w _ => by ring
    have hAp : IntegrableOn (fun w : ℝ => 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) -
        2 / Real.sqrt (w ^ 2 + ε)) (Ioc 0 1) := hA1.sub hp1
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_sub hAp hq1, integral_sub hA1 hp1]
    ring
  have hR2 : ∫ w in Ioi (1 : ℝ), 2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) =
      (∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / w)) +
        ∫ w in Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) := by
    have e : ∀ w ∈ Ioi (1 : ℝ), Real.exp (-w ^ 2) * (2 / Real.sqrt (w ^ 2 + ε) - 2 / w) =
        2 * Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + ε) - Real.exp (-w ^ 2) * (2 / w) :=
      fun w _ => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hA2 hq2]
    ring
  have hb1 := elem_bounds hε hε1
  have hb2 := rem_inner_le hε hε1
  have hb3 := rem_outer_le hε
  have hγ

/-- ★★ **`Z_N = J(1/(2N))/√(2πN)`** for `N > 0` (from the conditional reduction, `x = √2 w`). -/
theorem gaussLaplace2_eq_J {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N = gaussJ (1 / (2 * N)) / Real.sqrt (2 * Real.pi * N) := by
  rw [gaussLaplace2_eq_integral hN.le]
  have h1 : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sq_abs]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h2 : ∫ x in Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) =
      Real.sqrt 2 * ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.sqrt 2 * w) ^ 2 / 2) /
        Real.sqrt (1 + N * (Real.sqrt 2 * w) ^ 2) := by
    rw [integral_comp_mul_left_Ioi (fun x => Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2)) 0
      hs2, mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs2.ne', one_mul]
  have h3 : ∀ w ∈ Ioi (0 : ℝ), Real.exp (-(Real.sqrt 2 * w) ^ 2 / 2) /
      Real.sqrt (1 + N * (Real.sqrt 2 * w) ^ 2) =
      (Real.sqrt (2 * N))⁻¹ * (Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + 1 / (2 * N))) := by
    intro w _
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have e1 : -(Real.sqrt 2 * w) ^ 2 / 2 = -w ^ 2 := by rw [mul_pow, hs]; ring
    have e2 : 1 + N * (Real.sqrt 2 * w) ^ 2 = (2 * N) * (w ^ 2 + 1 / (2 * N)) := by
      rw [mul_pow, hs]; field_simp; ring
    rw [e1, e2, Real.sqrt_mul (by positivity)]
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  unfold gaussJ
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  set I := ∫ w in Ioi (0 : ℝ), Real.exp (-w ^ 2) / Real.sqrt (w ^ 2 + 1 / (2 * N)) with hI
  clear_value I
  rw [Real.sqrt_mul (x := 2 * Real.pi) (by positivity) N,
    Real.sqrt_mul (x := 2) (by norm_num) Real.pi, Real.sqrt_mul (x

/-- ★★ **The two-term expansion with an explicit remainder**: for `N ≥ 1/2`,
`|Z_N − (log N + 3 log 2 − γ)/√(2πN)| ≤ (log(2N) + 3)/(2N √(2πN))`. -/
theorem gaussLaplace2_two_term_bound {N : ℝ} (hN : 1 / 2 ≤ N) :
    |gaussLaplace2 N - (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      Real.sqrt (2 * Real.pi * N)| ≤
      (Real.log (2 * N) + 3) / (2 * N * Real.sqrt (2 * Real.pi * N)) := by
  have hN0 : 0 < N := by linarith
  have hε : 0 < 1 / (2 * N) := by positivity
  have hε1 : 1 / (2 * N) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hb := gaussJ_two_term hε hε1
  have hs : 0 < Real.sqrt (2 * Real.pi * N) := Real.sqrt_pos.2 (by positivity)
  have hlog4 : Real.log (4 / (1 / (2 * N))) = Real.log N + 3 * Real.log 2 := by
    rw [show (4 : ℝ) / (1 / (2 * N)) = 2 ^ 3 * N by field_simp; ring,
      Real.log_mul (by norm_num) hN0.ne', Real.log_pow]
    push_cast; ring
  have hlog1 : Real.log (1 / (1 / (2 * N))) = Real.log (2 * N)

/-- ★★★ **The depth-two Gaussian deep linear network expansion**:
`Z_N = (log N + 3 log 2 − γ)/√(2πN) + O(N^{−3/2} log N)` (the note's eq. (dln_gauss) at
`L = 2`). -/
theorem gaussLaplace2_two_term :
    (fun N : ℝ => gaussLaplace2 N -
      (Real.log N + 3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi * N))
      =O[atTop] fun N => N ^ (-(3 / 2 : ℝ)) * Real.log N := by
  refine Asymptotics.IsBigO.of_bound (5 / (2 * Real.sqrt (2 * Real.pi))) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hb := gaussLaplace2_two_term_bound (by linarith : 1 / 2 ≤ N)
  have hsπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN.le _) (by linarith))]
  refine hb.trans ?_
  have hlog2 : Real.log (2 * N) = Real.log 2 + Real.log N := Real.log_mul two_ne_zero hN.ne'
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : N ^ (-(3 / 2 : ℝ)) = 1 / (N * Real.sqrt N) := by
    rw [Real.rpow_neg hN.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hN,
      Real.rpow_one, Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [hpow, Real.sqrt_mul (by positivity) N]
  calc (Real.log (2 * N) + 3) / (2 * N * (Real.sqrt (2 * Real.pi) * Real.sqrt N))
      ≤ 5 * Real.log N / (2 * N * (Real.sqrt (2 * Real.pi) * Real.sqrt N)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 5 / (2 * Real.sqrt (2 * Real.pi)) * (1 / (N * Real.sqrt N) * Real.log N)
```
### Grammar/LogSqDominationAdapter.lean
```lean
/-- `∫₀¹ t^a |log t| dt = 1/(a + 1)²` for `a > −1`. -/
theorem integral_rpow_mul_abs_log_Ioc {a : ℝ} (ha : -1 < a) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ a * |Real.log t| = 1 / (a + 1) ^ 2 := by
  have hs : ((-a / 2 : ℝ) : ℂ).re < 1 / 2 := by simp; linarith
  have h := integral_cpow_log_Ioc hs
  have e : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (-2 * ((-a / 2 : ℝ) : ℂ)) * (-2 * (Real.log t : ℂ)) =
      ((2 * (t ^ a * |Real.log t|) : ℝ) : ℂ) := by
    intro t ht
    rw [show (-2 * ((-a / 2 : ℝ) : ℂ)) = ((a : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht.1.le, abs_of_nonpos (Real.log_nonpos ht.1.le ht.2)]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc e, integral_complex_ofReal, integral_const_mul,
    show (1 - 2 * ((-a / 2 : ℝ) : ℂ)) = ((a + 1 : ℝ) : ℂ) by push_cast; ring,
    show (2 : ℂ) / ((a + 1 : ℝ) : ℂ) ^ 2 = ((2 / (a + 1) ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
  have h' := Complex.ofReal_inj.1 h
  have : (1 : ℝ) / (a + 1) ^ 2 = 2 / (a + 1) ^ 2 / 2

/-- Derivative domination for a power-bounded Mellin integrand: `‖g(t)‖ ≤ C t^b` on `(0,1]` and
`Re s ≤ σ` with `b − 2σ > −1` give `‖(M g)'(s)‖ ≤ 2C/(b − 2σ + 1)²`. -/
theorem norm_deriv_mellinIoc_le {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {σ : ℝ} (hσ : -1 < b - 2 * σ) {s : ℂ}
    (hs : s.re ≤ σ) :
    ‖deriv (mellinIoc g) s‖ ≤ 2 * C / (b - 2 * σ + 1) ^ 2 := by
  have hs' : s.re < (b + 1) / 2 := by linarith
  rw [(hasDerivAt_mellinIoc hg hC hb hs').deriv]
  have hmaj : IntegrableOn (fun t : ℝ => 2 * C * (t ^ (b - 2 * σ) * |Real.log t|)) (Ioc 0 1) :=
    (integrableOn_rpow_mul_log_Ioc hσ).const_mul _
  refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have h2 : ‖(-2 * (Real.log t : ℂ))‖ = 2 * |Real.log t| := by
      rw [norm_mul, norm_neg, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
    have hpow : t ^ (-2 * s.re) ≤ t ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
    rw [norm_mul, norm_mul, norm_cpow_neg_two s ht0, h2]
    calc ‖g t‖ * t ^ (-2 * s.re) * (2 * |Real.log t|)
        ≤ C * t ^ b * t ^ (-2 * σ) * (2 * |Real.log t|) := by
          gcongr
          exact hb t ht
      _ = 2 * C * (t ^ (b - 2 * σ) * |Real.log t|)

/-- Derivative domination for a cutoff integrand: `g` bounded by `K` on `(M, 1]`, `0 < M ≤ 1`,
`Re s ≤ ½ + r`, `0 < r < ½`: `‖(M[1_{(M,1]} g])'(s)‖ ≤ K |log M| M^{−2r}/r`. -/
theorem norm_deriv_mellinIoc_cutoff_le {g : ℝ → ℂ} (hg : Measurable g) {K : ℝ} (hK : 0 ≤ K)
    {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) (hb : ∀ t ∈ Ioc M 1, ‖g t‖ ≤ K) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) {s : ℂ} (hs : s.re ≤ 1 / 2 + r) :
    ‖deriv (mellinIoc ((Ioc M 1).indicator g)) s‖ ≤ K * |Real.log M| * M ^ (-2 * r) / r := by
  have hmeas : AEStronglyMeasurable ((Ioc M 1).indicator g) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hg.indicator measurableSet_Ioc).aestronglyMeasurable
  have hM3 : 0 < M ^ (3 : ℝ) := Real.rpow_pos_of_pos hM0 _
  have hb' : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(Ioc M 1).indicator g t‖ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by
    intro t ht
    by_cases hmem : t ∈ Ioc M 1
    · rw [indicator_of_mem hmem]
      have h1 : M ^ (3 : ℝ) ≤ t ^ (3 : ℝ) := Real.rpow_le_rpow hM0.le hmem.1.le (by norm_num)
      calc ‖g t‖ ≤ K := hb t hmem
        _ = K / M ^ (3 : ℝ) * M ^ (3 : ℝ) := by field_simp
        _ ≤ K / M ^ (3 : ℝ) * t ^ (3 : ℝ) := by gcongr
    · rw [indicator_of_notMem hmem, norm_zero]
      have : 0 ≤ t ^ (3 : ℝ) := Real.rpow_nonneg ht.1.le _
      positivity
  have hs3 : s.re < ((3 : ℝ) + 1) / 2 := by norm_num; linarith
  rw [(hasDerivAt_mellinIoc hmeas (by positivity) hb' hs3).deriv]
  have hlogM : 0 ≤ |Real.log M| := abs_nonneg _
  -- the majorant `2K|log M| t^{−1−2r}` on `(M, 1]`
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-1 - 2 * r)) volume M 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr fun h => by
      rw [uIcc_of_le hM1] at h; exact absurd h.1 (not_le.2 hM0))
  have hmajM : IntegrableOn (fun t : ℝ => 2 * K * |Real.log M| * t ^ (-1 - 2 * r)) (Ioc M 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM1).1 hint).const_mul _
  have hmaj : IntegrableOn ((Ioc M 1).indicator
      fun t : ℝ => 2 * K * |Real.log M| * t ^ (-1 - 2 * r)) (Ioc 0 1) :=
    (hmajM.integrable_indicator measurableSet_Ioc).integrableOn
  refine (norm_integral_le_of_norm_le hmaj ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    by_cases hmem : t ∈ Ioc M 1
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      have h2 : ‖(-2 * (Real.log t : ℂ))‖ = 2 * |Real.log t| := by
        rw [norm_mul, norm_neg, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
      have hpow : t ^ (-2 * s.re) ≤ t ^ (-1 - 2 * r) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
      have hlt : |Real.log t| ≤ |Real.log M| := by
        rw [abs_of_nonpos (Real.log_nonpos ht0.le ht.2), abs_of_nonpos (Real.log_nonpos hM0.le hM1)]
        linarith [Real.log_le_log hM0 hmem.1.le]
      rw [norm_mul, norm_mul, norm_cpow_neg_two s ht0, h2]
      calc ‖g t‖ * t ^ (-2 * s.re) * (2 * |Real.log t|)
          ≤ K * t ^ (-1 - 2 * r) * (2 * |Real.log M|) := by
            gcongr
            exact hb t hmem
        _ = 2 * K * |Real.log M| * t ^ (-1 - 2 * r) := by ring
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
      simp
  · rw [setIntegral_indicator measurableSet_Ioc,
      show Ioc (0 : ℝ) 1 ∩ Ioc M 1 = Ioc M 1 from
        inter_eq_right.2 fun t ht => ⟨hM0.trans ht.1, ht.2⟩,
      ← intervalIntegral.integral_of_le hM1, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, fun h => by
        rw [uIcc_of_le hM1] at h; exact absurd h.1 (not_le.2 hM0)⟩)]
    rw [show (-1 - 2 * r + 1) = -2 * r by ring, Real.one_rpow]
    have hM2 : 0 < M ^ (-2 * r) := Real.rpow_pos_of_pos hM0 _
    have : 2 * K * |Real.log M| * ((1 - M ^ (-2 * r)) / (-2 * r)) =
        K * |Real.log M| * (M ^ (-2 * r) - 1) / r := by
      field_simp
      ring
    rw [this]
    have hKL : 0 ≤ K * |Real.log M|

/-- The explicit dominating constant for `(logSqHolo ℓ c b M φ)'` on `|s − ½| < r`: the four
pieces (even remainder, even cutoff, odd part, odd cutoff). -/
noncomputable def logSqDomBound (ℓ c b M L φ₀ r : ℝ) : ℝ

/-- The odd amplitude bound `‖b(φ(t) − φ(−t))‖ ≤ 2|b|L t` on `(0, 1]`. -/
theorem norm_logSqOddAmp_le (b : ℝ) {φ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ) := by
  intro t ht
  have h1 := hL t ⟨by linarith [ht.1], ht.2⟩
  have h2 := hL (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [abs_of_pos ht.1] at h1
  rw [abs_neg, abs_of_pos ht.1] at h2
  unfold logSqOddAmp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.rpow_one]
  have : |φ t - φ (-t)| ≤ 2 * L * t := by
    calc |φ t - φ (-t)| = |(φ t - φ 0) - (φ (-t) - φ 0)| := by ring_nf
      _ ≤ |φ t - φ 0| + |φ (-t) - φ 0| := abs_sub _ _
      _ ≤ 2 * L * t := by linarith
  calc |b| * |φ t - φ (-t)| ≤ |b| * (2 * L * t) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 2 * |b| * L * t

theorem measurable_logSqOddAmp (b : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Measurable (logSqOddAmp b φ)

/-- The even amplitude is bounded on `(M, 1]` by `(2(|ℓ| + |log M|)² + |c|)(2|φ(0)| + 2L)`. -/
theorem norm_logSqAmp_symm_cutoff_le (ℓ c : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc M 1, ‖logSqAmp ℓ c (symmAmp φ) t‖ ≤
      (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ 0| + 2 * L) := by
  intro t ht
  have ht0 : 0 < t := hM0.trans ht.1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (by simpa using hL 1 ⟨by norm_num, le_rfl⟩)
  have hψL := symmAmp_bound hL t ⟨ht0, ht.2⟩
  have hψ0 := symmAmp_zero φ
  have hlt : |Real.log (1 / t)| ≤ |Real.log M| := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos ht0.le ht.2),
      abs_of_nonpos (Real.log_nonpos hM0.le hM1)]
    linarith [Real.log_le_log hM0 ht.1.le]
  have hsq : (ℓ + Real.log (1 / t)) ^ 2 ≤ (|ℓ| + |Real.log M|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (by linarith)) 2
  have hden : |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| ≤ 2 * (|ℓ| + |Real.log M|) ^ 2 + |c| := by
    calc |2 * (ℓ + Real.log (1 / t)) ^ 2 - c| ≤ |2 * (ℓ + Real.log (1 / t)) ^ 2| + |c| :=
          abs_sub _ _
      _ ≤ 2 * (|ℓ| + |Real.log M|) ^ 2 + |c| := by
          rw [abs_of_nonneg (by positivity)]
          linarith
  have hamp : |symmAmp φ t| ≤ 2 * |φ 0| + 2 * L := by
    have h1 := abs_le.1 hψL
    have h2 : 2 * L * t ≤ 2 * L

/-- `|s − ½| < r` gives `Re s ≤ ½ + r`. -/
theorem re_le_of_mem_ball_half {r : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    s.re ≤ 1 / 2 + r := by
  have h := Complex.abs_re_le_norm (s - 1 / 2)
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have : (s - 1 / 2).re = s.re - 1 / 2

/-- ★★ **Derivative domination for the fibre remainder**: on the ball `|s − ½| < r`, `0 < r < ½`,
`‖(logSqHolo ℓ c b M φ)'(s)‖ ≤ logSqDomBound ℓ c b M L φ(0) r`. -/
theorem norm_deriv_logSqHolo_le (ℓ c b : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    ‖deriv (logSqHolo ℓ c b M φ) s‖ ≤ logSqDomBound ℓ c b M L (φ 0) r := by
  have hsre : s.re ≤ 1 / 2 + r := re_le_of_mem_ball_half hs
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (by simpa using hL 1 ⟨by norm_num, le_rfl⟩)
  have hψ := continuous_symmAmp hφ
  have hψL := symmAmp_bound hL
  set δ : ℝ := (1 / 2 - r) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  -- the four pieces and their derivatives
  have hAm : AEStronglyMeasurable (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_logSqAmp ℓ c (hψ.sub continuous_const).measurable).aestronglyMeasurable
  have hAb := norm_logSqAmp_sub_le ℓ c hψL hδpos
  have hC0 : 0 ≤ (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L) := by positivity
  have hA : HasDerivAt (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0))
      (deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s) s :=
    (hasDerivAt_mellinIoc hAm hC0 hAb (by rw [hδ]; linarith)).differentiableAt.hasDerivAt
  have hBm : Measurable (logSqAmp ℓ c (symmAmp φ)) := measurable_logSqAmp ℓ c hψ.measurable
  have hBb := norm_logSqAmp_symm_cutoff_le ℓ c hM0 hM1 hL
  have hK0 : 0 ≤ (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ 0| + 2 * L) := by positivity
  have hB : HasDerivAt (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ))))
      (deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s) s :=
    ((differentiableOn_mellinIoc_cutoff hBm hK0 hM0 hBb).differentiableAt
      ((isOpen_re_lt 2).mem_nhds (by change s.re < 2; linarith))).hasDerivAt
  have hCm : Measurable (logSqOddAmp b φ) := measurable_logSqOddAmp b hφ
  have hCb := norm_logSqOddAmp_le b hL
  have hCC : 0 ≤ 2 * |b| * L := by positivity
  have hC : HasDerivAt (mellinIoc (logSqOddAmp b φ)) (deriv (mellinIoc (logSqOddAmp b φ)) s) s :=
    (hasDerivAt_mellinIoc hCm.aestronglyMeasurable hCC hCb
      (by norm_num; linarith)).differentiableAt.hasDerivAt
  have hDb : ∀ t ∈ Ioc M 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L := by
    intro t ht
    have ht0 : 0 < t := hM0.trans ht.1
    calc ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ) := hCb t ⟨ht0, ht.2⟩
      _ ≤ 2 * |b| * L := by rw [Real.rpow_one]; nlinarith [ht.2]
  have hD : HasDerivAt (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ)))
      (deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s) s :=
    ((differentiableOn_mellinIoc_cutoff hCm hCC hM0 hDb).differentiableAt
      ((isOpen_re_lt 2).mem_nhds (by change s.re < 2; linarith))).hasDerivAt
  have hsum := (hA.sub hB).add (hC.sub hD)
  have hderiv : deriv (logSqHolo ℓ c b M φ) s =
      deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s -
        deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s +
        (deriv (mellinIoc (logSqOddAmp b φ)) s -
          deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s) := by
    refine HasDerivAt.deriv ?_
    exact hsum
  rw [hderiv]
  -- the four bounds
  have h1 := norm_deriv_mellinIoc_le hAm hC0 hAb (σ := 1 / 2 + r) (by rw [hδ]; linarith) hsre
  have h2 := norm_deriv_mellinIoc_cutoff_le hBm hK0 hM0 hM1 hBb hr hr1 hsre
  have h3 := norm_deriv_mellinIoc_le hCm.aestronglyMeasurable hCC hCb (σ := 1 / 2 + r)
    (by linarith) hsre
  have h4 := norm_deriv_mellinIoc_cutoff_le hCm hCC hM0 hM1 hDb hr hr1 hsre
  have e1 : (1 - 2 * δ - 2 * (1 / 2 + r) + 1) = 1 / 2 - r := by rw [hδ]; ring
  have e3 : ((1 : ℝ) - 2 * (1 / 2 + r) + 1) = 1 - 2 * r := by ring
  rw [e1] at h1
  rw [e3] at h3
  unfold logSqDomBound
  rw [← hδ]
  calc ‖deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s -
        deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s +
        (deriv (mellinIoc (logSqOddAmp b φ)) s -
          deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s)‖
      ≤ ‖deriv (mellinIoc (logSqAmp ℓ c fun t => symmAmp φ t - symmAmp φ 0)) s‖ +
        ‖deriv (mellinIoc ((Ioc M 1).indicator (logSqAmp ℓ c (symmAmp φ)))) s‖ +
        (‖deriv (mellinIoc (logSqOddAmp b φ)) s‖ +
          ‖deriv (mellinIoc ((Ioc M 1).indicator (logSqOddAmp b φ))) s‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
    _ ≤ _

/-- The averaged polar theorem on a ball `|s − ½| < r` with a single dominating function `B`. -/
theorem averaged_logSq_polar_ball {φ₀ ℓ c : Λ → ℝ} {H : Λ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableOn ℂ (H l) (Metric.ball (1 / 2 : ℂ) r))
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, Integrable (fun l => H l s) ν)
    {B : Λ → ℝ} (hB : Integrable B ν)
    (hdom : ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv (H l) s‖ ≤ B l) :
    (fun s => (∫ l, (((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s) ∂ν) -
      polarPart 2 (logSqAvgA φ₀ ℓ c ν) (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  have hopen : IsOpen (Metric.ball (1 / 2 : ℂ) r) := Metric.isOpen_ball
  have hmem : (1 / 2 : ℂ) ∈ Metric.ball (1 / 2 : ℂ) r := Metric.mem_ball_self hr
  have hdom' : ∀ s₀ ∈ Metric.ball (1 / 2 : ℂ) r, ∃ ε > 0,
      Metric.ball s₀ ε ⊆ Metric.ball (1 / 2 : ℂ) r ∧ ∃ B : Λ → ℝ, Integrable B ν ∧
        ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball s₀ ε, ‖deriv (H l) s‖ ≤ B l := by
    intro s₀ hs₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hs₀)
    exact ⟨ε, hε, hball, B, hB, hdom.mono fun l hl s hs => hl s (hball hs)⟩
  have hHol := differentiableOn_integral_of_deriv_dominated hopen hmeas hdiff hint hdom'
  have hcont : ContinuousAt (fun s => ∫ l, H l s ∂ν) (1 / 2) :=
    (hHol.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have hO : (fun s => ∫ l, H l s ∂ν) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  have hU : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s ∈ Metric.ball (1 / 2 : ℂ) r :=
    eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hmem)
  filter_upwards [hU, self_mem_nhdsWithin] with s hs hs'
  have hs2 : s ≠ 1 / 2 := hs'
  have hpt : ∀ l, ((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s =
      polarPart 2 (logSqA (ℓ l) (c l) (2 * φ₀ l)) (1 / 2 : ℂ) s + H l s

/-- On the strip `Re s < ½` the averaged fibre Mellin transform is the averaged continuation. -/
theorem integral_logSqMellinFull_eq {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ}
    (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ l, logSqMellinFull (ℓ l) (c l) (b l) (M l) (φ l) s ∂ν =
      ∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
        logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν

/-- ★★★ **The averaged naive Bayes polar distributions from the fibre data**: for a family of
fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)` with `0 < M_λ ≤ 1` and `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, if the
fibre polar coefficients and the explicit bound `logSqDomBound` are `ν`-integrable (and the
remainders are measurable and integrable in `λ` at each `s` of the ball `|s − ½| < r`), the averaged
continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`: `C̄_{½,3} = −∫φ_λ(0)`,
`C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`. -/
theorem averaged_naiveBayes_polar {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ} {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ l 0) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      AEStronglyMeasurable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      Integrable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hB : Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r) ν) :
    (fun s => (∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
      logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν) -
      polarPart 2 (logSqAvgA (fun l => φ l 0) ℓ c ν) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  refine averaged_logSq_polar_ball (φ₀ := fun l => φ l 0) hr hcoef hmeas ?_ hint hB ?_
  · refine Eventually.of_forall fun l => ?_
    refine ((logSqMellinFull_eq (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l)).1).mono ?_
    intro s hs
    have
```

## State of the note (pinned to grammar 73a2401)
Formal (theorems in Lean, cited by declaration name): §2 DLN flat prior at every depth on [−1,1]^L (exact identity with Gamma log-moments H_j; H₀,H₁,H₂ evaluated); polar dictionaries of the 1D state densities (log, mixed, log²); Gaussian product zeta ζ_L and its order-L pole; depth-two Gaussian conditional reduction AND its two-term expansion with explicit remainder (Z_N − (log N + 3log2 − γ)/√(2πN) bounded by (log(2N)+3)/(2N√(2πN)) for N ≥ 1/2). §3 cone: exact Leray closed form with Gaussian tails. §4 blow-up: tie formulas (polynomial, smooth with supplied decomposition, arbitrary smooth via Hadamard), the Laurent data of ζ(w)=2^{3w+1}Γ(w+½)² at −½. §5 rank-one: normal Gaussian integral in adapted coordinates, gauge-independent tilt. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball with the domination derived from fibre data (integrability of the explicit bound as the hypothesis).
Derivation-only (checked numerically): Gaussian-prior asymptotic transfer (poles → Z_N) and the Gaussian polynomials P_{L−1} for L ≥ 3 (P₂(t) = t² + π² etc.); the Bessel closed form e^{1/4N}K₀(1/4N)/√(2πN) at L=2; H₃ and ζ(3) in Q₃; the naive Bayes envelope M_±(λ): facewise integrability of logSqDomBound (M ≍ d^β, L ≲ d^{−η}, dν ≲ d^{a−1}dd ⇒ 2rβ+η<a), joint measurability of the fibre family, KL-vs-surrogate remainder, m₂ = √(2π)(g²/4+π²/8); cone averaged-posterior domination and the exact expansion prefactors; blow-up assembly (chart polar data → global expansion of the blow-up model) and the Laplace polynomial √(π/2)[…] multiplying N^{−1/2}; Morse–Bott passage / orientation for rank-one beyond alignment; the smooth-amplitude tie remainder beyond O(1).

## Library facts
Everything of rounds 1–5 (Mellin engine `hasDerivAt_mellinIoc`, `differentiableOn_integral_of_deriv_dominated`, `integral_comp_rpow_Ioi_of_pos`, `integral_comp_abs`, `integral_comp_mul_left_Ioi`, Gamma/digamma values at ½ and 1, `Complex.hasDerivAt_Gamma_one`, `integral_exp_neg_Ioi`, `integral_rpow`, `Measure.integrableOn_of_bounded`, `norm_integral_le_of_norm_le`, chart polar coefficients `chartPolarCoeff`, `polarPart`, `polarPart_eq_of_sub_isBigO_one`, blow-up model zeta `blowupZeta`, `gaussProductZeta`, `depth_flat_allOrders`, `gaussLaplace2`, `gaussJ`, `logSqHolo`, `logSqDomBound`, `logSqAvgA`). Mathlib pin v4.33.1 (no Bessel functions, no polygamma beyond what is derived, `Real.eulerMascheroniConstant` with Γ'(1) = −γ).

## Questions
1. Fidelity check (brief) of DCX–DCXIII against the note's claims and against your round-5 specifications: in particular (a) the constant ε(log(1/ε)+3) in `gaussJ_two_term` and the remainder (log(2N)+3)/(2N√(2πN)) — are these consistent with your J(ε) = log(4/ε) − γ + O(ε log(1/ε)); (b) the shape of `logSqDomBound` (four pieces; the remainder piece carries 4/δ² with δ = (½−r)/2, the cutoff pieces |log M| M^{−2r}/r) versus your suggested W(1+M^{−2r})(1+|log M|⁴); is anything missing for the facewise verification beyond integrability of this bound and joint measurability?
2. Rank the next three day-sized formal targets by value-per-effort for the note (concrete Lean statements + routes). Candidates: (a) the Gaussian DLN at depth L ≥ 3: is there a Bessel-free exact reduction analogous to DCVII (e.g. iterated conditional Gaussian integrals giving Z_N = E[(1+N∏_{i<L}W_i²)^{−1/2}]) and a route to the leading term (log N)^{L−1}/((L−1)!√(2πN))·… with an explicit remainder, or at least the leading coefficient; (b) the facewise integrability of logSqDomBound for the actual naive Bayes envelope M_±(λ) = … (which faces, which exponents β, η, a; is the joint measurability of λ ↦ logSqHolo_λ(s) obtainable from a jointly measurable amplitude family by Fubini-type lemmas); (c) the blow-up assembly: from the chart polar coefficients of DXCVII/DC/DCV and the Laurent data of DCX to the two-term expansion of the blow-up model partition function (what exactly is the model, what is the cleanest formal statement); (d) the cone model averaged posterior (domination for the ξ-average); (e) H₃ = Γ'''(½) via a third derivative of the reflection formula (is it worth it; the note needs ζ(3)); (f) the rank-one tilt beyond aligned coordinates. Say which of these are honest day-sized targets and give the Lean-facing interface for the top three.
3. Any convention hazards you see in the four new files (signs, the variable w = √v in `gaussJ`, the ball radius r < ½ and δ = (½−r)/2 choice, the (0,1] vs (0,1) indicators in the renormalised integral).
Answer concisely with Lean-facing detail.
