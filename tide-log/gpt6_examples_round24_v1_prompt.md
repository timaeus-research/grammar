You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 6a3e9fd, 1009 modules, zero sorry/axiom) of the examples note `examples_slop.tex` (Gerraty–Murfet grammar paper). Your round-23 targets 1 and 2 are BOTH DONE, each compiled first try:

DCLXXII (`GammaThirdDerivDuplication.lean`): duplication differentiated three times at ½ with explicit derivative functions `dupL'`, `dupL''`, `dupR'`, `dupR''` and the `Filter.EventuallyEq.deriv` chain; `Γ'''(½) = √π[7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]` exactly your boxed relation; `gammaLogThirdOne = λ₃`; `c₃ = c₁³/6 + c₁π²/2 − (2/3)λ₃`; `Q₃` modulo one symbol. Numerics to 40 digits.

DCLXXIII (`GammaLogMomentsIteratedDeriv.lean`): the log-weighted kernels `k_r = log^r t · e^{−t}` (recursive so `k_{r+1} = log • k_r` is `rfl`), growth at every order by induction through Mathlib's `isBigO_rpow_top_log_smul`/`isBigO_rpow_zero_log_smul`, and `mellin_hasDerivAt_of_isBigO_rpow` iterated: `deriv^[r] Γ s = M[k_r](s)` on `Re s > 0`, hence `G_r = Γ^{(r)}(1)` and `H_j = Γ^{(j)}(½)` at EVERY order (no restriction to `m ≤ 2`; the domination is Mathlib's, not ours). Consequence: `J₂` closed modulo `λ₃` and ★★★ `depthFourConst_eq_logThird : D₄ = (2b³ + 7π²b − 6λ₃)/(24π√(2π))`, `b = 5 log 2 − 3γ` (sympy-derived, `field_simp; ring`; = `(b³/6 + 7π²b/12 + ζ(3))/(2π)^{3/2}` = 0.7654005 with `λ₃ = −2ζ(3)`). So `P₄` is a theorem modulo the single symbol `λ₃`.

MATHLIB SCOUT (pin v4.33.1): there is NO Leibniz rule for `iteratedDeriv` of a product (only `iteratedDeriv_mul_const_field`, `norm_iteratedFDeriv_mul_le`); `iteratedDeriv_eq_iterate`, `iteratedDeriv_comp_const_mul` (needs `ContDiff`), `IteratedDeriv/FaaDiBruno.lean`, `IteratedDeriv/Analytic.lean` exist; `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` exists; `Complex.Gamma` is analytic on `Re z > 0` (`analyticAt_Gamma_of_re_pos`, ours) and `AnalyticAt.iteratedDeriv`-style API is available.

## HEADLINES rows DCLXXII–DCLXXIII
| **DCLXXII** | ★★★ **`Γ'''(½)` FROM `Γ'''(1)` BY DUPLICATION: THE CUBIC JET MODULO ONE SYMBOL (u1008; examples_slop §2; Astra round-23 target 1)**: `GammaThirdDerivDuplication.lean` — the explicit derivative functions `dupL'`, `dupL''` of `Γ(w)Γ(w+½)` and `dupR'`, `dupR''` of `Γ(2w)2^{1−2w}√π` (`hasDerivAt_dupL'`, `hasDerivAt_dupR'` on `Re z > 0`; `hasDerivAt_dupL''_half`, `hasDerivAt_dupR''_half` at `½`), the eventual-equality chain `deriv f =ᶠ dupL'`, `deriv dupL' =ᶠ dupL''` (`Filter.EventuallyEq.deriv`) on both sides of Mathlib's `Complex.Gamma_mul_Gamma_add_half`, ★★ `deriv_deriv_deriv_duplication` (`Γ'''(½)Γ(1) + 3Γ''(½)Γ'(1) + 3Γ'(½)Γ''(1) + Γ(½)Γ'''(1) = √π[8Γ'''(1) − 24 log 2 Γ''(1) + 24 log² 2 Γ'(1) − 8 log³ 2 Γ(1)]`), ★★★ `deriv_deriv_deriv_Gamma_one_half` / real `gammaThirdHalf_eq` (`Γ'''(½) = √π[7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`, `p = γ + 2 log 2`, DCXXXVIII's `linear_combination` closer one order up), the log-Gamma symbol `gammaLogThirdOne = λ₃ = Γ'''(1) + γ³ + γπ²/2` (`= (log Γ)'''(1) = −2ζ(3)`, a derivation), ★★★ `depthThreeJetCubic_eq_logThird` (`c₃ = c₁³/6 + c₁π²/2 − (2/3)λ₃`, `field_simp; ring` after substituting the relation into DCLXXI's 14-term `c₃`), ★★★ `residualMass_three_eq_logThird`, `depthFourQint_eq_logThird` (`Q₃ = [c₁³/6 + c₁π²/2 − (2/3)λ₃]/(4π)`): the depth-three residual mass and `D₄` are closed modulo ONE symbol. Astra round 23 (`tide-log/gpt6_examples_round23_v1.md`): DCLXXI fidelity confirmed (Leibniz coefficients, real-part extraction, pole matching); ranked (a) duplication ≫ (c) `G₃ = Γ'''(1)` by differentiation under the integral (needs an iterated `GammaIntegral` derivative; domination `e^{−u}(1+|log u|⁴)u^{∓1/2}`) > (d) the general ζ-recurrence packaging (must keep the log-Gamma bridge an explicit hypothesis) > NB ratio, cone `c₃`, blow-up > (b) `ζ(3)` (multi-day: differentiated log-Gamma series + locally uniform convergence). Numerics: relation to 29 digits (`mpmath`), `λ₃ = −2ζ(3) = −2.4041138063`, `c₃ = 10.2942020780`. Lean: `HasDerivAt.comp_add_const z (1/2)` (point first, shift second) avoids the `* 1` of `.comp`; `instantiateMVars` beta-reduces the product-rule values, so `rw [h1]` finds `Γ(½ + ½)` directly. | GammaThirdDerivDuplication.lean |
| **DCLXXIII** | ★★★ **THE GAMMA LOG-MOMENTS ARE THE ITERATED DERIVATIVES OF `Γ`: `G_r = Γ^{(r)}(1)`, `H_j = Γ^{(j)}(½)` FOR EVERY ORDER, AND `D₄` MODULO ONE SYMBOL (u1009; examples_slop §2; Astra round-23 target 2)**: `GammaLogMomentsIteratedDeriv.lean` — the kernels `gammaLogKernel r = log^r t · e^{−t}` (recursive, `k_{r+1} = log • k_r` definitional; `gammaLogKernel_apply`), growth at every order by induction (`gammaLogKernel_isBigO_atTop` for every `a` via `isBigO_rpow_top_log_smul`, `gammaLogKernel_isBigO_zero` for every `b > 0` via `isBigO_rpow_zero_log_smul`, base `e^{−t} ≤ 1 ≤ t^{−b}` on `(0,1)`), `continuousOn_gammaLogKernel`, `locallyIntegrableOn_gammaLogKernel`, `hasDerivAt_mellin_gammaLogKernel` (Mathlib's `mellin_hasDerivAt_of_isBigO_rpow` with `a = Re s + 1`, `b = Re s/2`), ★★ `iterate_deriv_Gamma_eq_mellin` (`deriv^[r] Γ s = M[k_r](s)` on `Re s > 0`, induction with `Function.iterate_succ_apply'` and the eventual equality on the open half-plane; base `Complex.Gamma_eq_integral` + `Complex.GammaIntegral_eq_mellin`), ★★★ `gammaOneLogMoment_eq_iterate` (`G_r = Γ^{(r)}(1)` for every `r`), ★★ `gammaLogMoment_eq_iterate` (`H_j = Γ^{(j)}(½)` for every `j`, DCVIII's `j = 2` at every order), `gammaOneLogMoment_three_eq : G₃ = gammaThirdOne` (`deriv^[3] = deriv ∘ deriv ∘ deriv` by `rfl`), `gammaOneLogMoment_two_eq_iterate` (regression), `gammaOneLogMoment_three_eq_logThird`, `gaussJlog2_eq_logThird` (`J₂ = ⅛[log³2/3 − γlog²2 + (γ² + π²/6)log 2 + (λ₃ − γ³ − γπ²/2)/3]`), ★★★ `depthFourConst_eq_logThird : D₄ = (2b³ + 7π²b − 6λ₃)/(24π√(2π))`, `b = 5 log 2 − 3γ` (`unfold`, the closed forms of `J`, `J₂`, `C₃`, `Q₃`, then `field_simp; ring`; with `λ₃ = −2ζ(3)` this is `(b³/6 + 7π²b/12 + ζ(3))/(2π)^{3/2} = 0.7654005`, the Mellin-jet value). The depth-four polynomial `P₄` is therefore closed modulo the single symbol `λ₃`, whose value `−2ζ(3)` is the only derivation left at depth four. Compiled first try. | GammaLogMomentsIteratedDeriv.lean |

## Public statements of DCLXXII
```lean
/-- `(Γ(w)Γ(w + ½))'`. -/
noncomputable def dupL' (z : ℂ) : ℂ

/-- `(Γ(w)Γ(w + ½))''`. -/
noncomputable def dupL'' (z : ℂ) : ℂ

theorem re_add_half_pos {z : ℂ} (h0 : 0 < z.re) : 0 < (z + 1 / 2).re

theorem hasDerivAt_dupL {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) (dupL' z) z

theorem hasDerivAt_dupL' {z : ℂ} (h0 : 0 < z.re) : HasDerivAt dupL' (dupL'' z) z

/-- The third derivative of the left side at `½`. -/
theorem hasDerivAt_dupL''_half :
    HasDerivAt dupL''
      (deriv (deriv (deriv Complex.Gamma)) (1 / 2) * Complex.Gamma 1 +
        3 * deriv (deriv Complex.Gamma) (1 / 2) * deriv Complex.Gamma 1 +
        3 * deriv Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1 +
        Complex.Gamma (1 / 2) * deriv (deriv (deriv Complex.Gamma)) 1) (1 / 2)

/-- `(Γ(2w) 2^{1−2w} √π)'` (the form of DCXXXVIII's `deriv_duplication_rhs`). -/
noncomputable def dupR' (z : ℂ) : ℂ

/-- `(Γ(2w) 2^{1−2w} √π)''`. -/
noncomputable def dupR'' (z : ℂ) : ℂ

theorem hasDerivAt_dupR {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w : ℂ =>
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ))
      (dupR' z) z

theorem hasDerivAt_dupR' {z : ℂ} (h0 : 0 < z.re) : HasDerivAt dupR' (dupR'' z) z

/-- The third derivative of the right side at `½`. -/
theorem hasDerivAt_dupR''_half :
    HasDerivAt dupR''
      ((8 * deriv (deriv (deriv Complex.Gamma)) 1 -
        24 * Complex.log 2 * deriv (deriv Complex.Gamma) 1 +
        24 * Complex.log 2 ^ 2 * deriv Complex.Gamma 1 - 8 * Complex.log 2 ^ 3 * Complex.Gamma 1) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)) (1 / 2)

/-- ★★ The duplication formula differentiated three times at `½`. -/
theorem deriv_deriv_deriv_duplication :
    deriv (deriv (deriv Complex.Gamma)) (1 / 2) * Complex.Gamma 1 +
        3 * deriv (deriv Complex.Gamma) (1 / 2) * deriv Complex.Gamma 1 +
        3 * deriv Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1 +
        Complex.Gamma (1 / 2) * deriv (deriv (deriv Complex.Gamma)) 1 =
      (8 * deriv (deriv (deriv Complex.Gamma)) 1 -
        24 * Complex.log 2 * deriv (deriv Complex.Gamma) 1 +
        24 * Complex.log 2 ^ 2 * deriv Complex.Gamma 1 - 8 * Complex.log 2 ^ 3 * Complex.Gamma 1) *
        ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- ★★★ **`Γ'''(½) = 7√π Γ'''(1) + √π[7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`**, `p = γ + 2 log 2`. -/
theorem deriv_deriv_deriv_Gamma_one_half :
    deriv (deriv (deriv Complex.Gamma)) (1 / 2) =
      ((7 * Real.sqrt Real.pi : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) 1 +
        ((Real.sqrt Real.pi * (7 * Real.eulerMascheroniConstant ^ 3 +
          7 * Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 -
          (Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
          3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2) : ℝ) : ℂ)

/-- The log-Gamma symbol `λ₃ = Γ'''(1) + γ³ + γπ²/2` (`= (log Γ)'''(1) = −2ζ(3)`; identification
with `ζ(3)` is a derivation). -/
noncomputable def gammaLogThirdOne : ℝ

/-- ★★★ The real form: `Γ'''(½) = √π[7Γ'''(1) + 7γ³ + 7γπ²/2 − p³ − 3pπ²/2]`. -/
theorem gammaThirdHalf_eq :
    gammaThirdHalf = Real.sqrt Real.pi * (7 * gammaThirdOne +
      7 * Real.eulerMascheroniConstant ^ 3 + 7 * Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 -
      (Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 3 -
      3 * (Real.eulerMascheroniConstant + 2 * Real.log 2) * Real.pi ^ 2 / 2)

/-- ★★★ **The cubic jet coefficient modulo one symbol**:
`c₃ = c₁³/6 + c₁π²/2 − (2/3)λ₃`. -/
theorem depthThreeJetCubic_eq_logThird :
    depthThreeJetCubic = depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
      2 / 3 * gammaLogThirdOne

/-- ★★★ `Q₃ = [c₁³/6 + c₁π²/2 − (2/3)λ₃]/(4π)`. -/
theorem residualMass_three_eq_logThird :
    residualMass 3 (enginePoly 3) =
      (depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
        2 / 3 * gammaLogThirdOne) / (4 * Real.pi)

theorem depthFourQint_eq_logThird :
    depthFourQint =
      (depthThreeJetLinear ^ 3 / 6 + depthThreeJetLinear * Real.pi ^ 2 / 2 -
        2 / 3 * gammaLogThirdOne) / (4 * Real.pi)
```

## Public statements of DCLXXIII
```lean
/-- `k_r(t) = log^r t · e^{−t}` (as a complex function), defined so that
`k_{r+1} = log · k_r` is definitional. -/
noncomputable def gammaLogKernel : ℕ → ℝ → ℂ
  | 0 => fun t => ((Real.exp (-t) : ℝ) : ℂ)
  | r + 1 => fun t => Real.log t • gammaLogKernel r t

theorem gammaLogKernel_zero : gammaLogKernel 0 = fun t => ((Real.exp (-t) : ℝ) : ℂ)

theorem gammaLogKernel_succ (r : ℕ) :
    gammaLogKernel (r + 1) = fun t => Real.log t • gammaLogKernel r t

theorem gammaLogKernel_apply (r : ℕ) (t : ℝ) :
    gammaLogKernel r t = ((Real.exp (-t) * Real.log t ^ r : ℝ) : ℂ)

theorem gammaLogKernel_isBigO_atTop (r : ℕ) (a : ℝ) :
    gammaLogKernel r =O[atTop] (· ^ (-a))

theorem gammaLogKernel_isBigO_zero (r : ℕ) {b : ℝ} (hb : 0 < b) :
    gammaLogKernel r =O[𝓝[>] 0] (· ^ (-b))

theorem continuousOn_gammaLogKernel (r : ℕ) : ContinuousOn (gammaLogKernel r) (Ioi 0)

theorem locallyIntegrableOn_gammaLogKernel (r : ℕ) :
    LocallyIntegrableOn (gammaLogKernel r) (Ioi 0)

/-- `d/ds M[k_r](s) = M[k_{r+1}](s)` on `Re s > 0`. -/
theorem hasDerivAt_mellin_gammaLogKernel (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (mellin (gammaLogKernel r)) (mellin (gammaLogKernel (r + 1)) s) s

/-- ★★ `Γ^{(r)}(s) = ∫₀^∞ t^{s−1} log^r t e^{−t} dt` for `Re s > 0`, every `r`. -/
theorem iterate_deriv_Gamma_eq_mellin (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    deriv^[r] Complex.Gamma s = mellin (gammaLogKernel r) s

/-- ★★★ **`G_r = Γ^{(r)}(1)`** for every `r`. -/
theorem gammaOneLogMoment_eq_iterate (r : ℕ) :
    ((gammaOneLogMoment r : ℝ) : ℂ) = deriv^[r] Complex.Gamma 1

/-- ★★ **`H_j = Γ^{(j)}(½)`** for every `j` (DCVIII's `gammaLogMoment_two_eq` at every order). -/
theorem gammaLogMoment_eq_iterate (j : ℕ) :
    ((gammaLogMoment j : ℝ) : ℂ) = deriv^[j] Complex.Gamma (1 / 2)

/-- `G₃ = Γ'''(1)`. -/
theorem gammaOneLogMoment_three_eq : gammaOneLogMoment 3 = gammaThirdOne

/-- `G₂ = Γ''(1)` regression: the DCLXVIII value agrees with DCXXXVIII's. -/
theorem gammaOneLogMoment_two_eq_iterate :
    ((gammaOneLogMoment 2 : ℝ) : ℂ) = deriv (deriv Complex.Gamma) 1

theorem gammaOneLogMoment_three_eq_logThird :
    gammaOneLogMoment 3 = gammaLogThirdOne - Real.eulerMascheroniConstant ^ 3 -
      Real.eulerMascheroniConstant * Real.pi ^ 2 / 2

/-- `J₂ = ⅛[log³2/3 − γ log²2 + (γ² + π²/6) log 2 + (λ₃ − γ³ − γπ²/2)/3]`. -/
theorem gaussJlog2_eq_logThird :
    gaussJlog2 = (1 / 8) * (Real.log 2 ^ 3 / 3 - Real.log 2 ^ 2 * Real.eulerMascheroniConstant +
      Real.log 2 * (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) +
      (gammaLogThirdOne - Real.eulerMascheroniConstant ^ 3 -
        Real.eulerMascheroniConstant * Real.pi ^ 2 / 2) / 3)

/-- ★★★ **The depth-four constant modulo one symbol**:
`D₄ = (2b³ + 7π²b − 6λ₃)/(24π√(2π))`, `b = 5 log 2 − 3γ`. -/
theorem depthFourConst_eq_logThird :
    depthFourConst =
      (2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) ^ 3 +
        7 * Real.pi ^ 2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) -
        6 * gammaLogThirdOne) / (24 * Real.pi * Real.sqrt (2 * Real.pi))
```

## Questions
1. Fidelity (brief): (a) `dupR''` and the third derivative of the right side `√π[8Γ'''(1) − 24 log 2 Γ''(1) + 24 log² 2 Γ'(1) − 8 log³ 2 Γ(1)]`; (b) the kernel-growth induction (`b/2 < b` step, base `e^{−t} ≤ 1 ≤ t^{−b}` on `(0,1)`) and the use of `mellin_hasDerivAt_of_isBigO_rpow` with `a = Re s + 1`, `b = Re s/2`; (c) the closed `D₄` (please re-derive `D₄·π√(2π) = b³/12 + 7π²b/24 − λ₃/4` from `D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]` with `A₃ = 1/4π`, `B₃ = (2log2 − γ)/π`, `C₃ = ((4log2 − 2γ)² + π²)/4π`, `R₀ = (log2 − γ)/2`, `J = R₀²/2 + π²/48`, `J₂` as stated, `Q₃ = [c₁³/6 + c₁π²/2 − (2/3)λ₃]/4π`).
2. NEXT day-sized targets — rank with Lean-facing interfaces. Candidates: (i) THE ALL-DEPTH JET THEOREM: `H_L(u) = 2^{(L−1)u}Γ(½−u)Γ(1+u)^L/√π` is analytic at `0`; with `HasFPowerSeriesAt` (or `AnalyticAt` + `isBigO_sub_partialSum_pow`) the jet to order `L` is `Σ_{k≤L} (iteratedDeriv k H_L 0 / k!) u^k + O(u^{L+1})`, and matching against DCLXX's finite part `tendsto_gammaProduct_sub_poles` (`M_L(1−2u) = H_L(u)/(2s^{L−1}u^L)`, poles `Σ_{k<L} 2^k k! a_{L,k}/(2u)^{k+1}`) would give at EVERY depth `a_{L,k} = iteratedDeriv (L−1−k) H_L 0 / ((L−1−k)! · 2^k k! · 2 s^{L−1}) · 2^{k+1}`-type identities and `Q_L = iteratedDeriv L H_L 0/(L! 2 s^{L−1})` — i.e. every coefficient of every `P_L` closed modulo the iterated derivatives of one analytic function (which are polynomials in `Γ^{(j)}(1)`, `Γ^{(j)}(½)`, `log 2`). Is the pole-matching (uniqueness of the Laurent principal part from the limit statement) formalisable in a day given DCLXX (the limit exists and equals `Q_L`) and DCLXXI's depth-three proof (`depthThreePoles_sum_eq`, l'Hôpital twice)? What is the cleanest formal route from `H_L(u) = Σ_{k≤L} h_k u^k + O(u^{L+1})` and `lim [H_L(u)/(2s^{L−1}u^L) − Σ_{k<L} p_k/u^{k+1}] = Q_L` to `h_k = 2s^{L−1}p_{L−1−k}` and `Q_L = h_L/(2s^{L−1})`? (I would take `u^L·(…)` limits inductively: multiply by `u^L`, let `u → 0` to identify `h_0`, subtract, divide by `u`, repeat — as a Lean lemma about `Tendsto` of `(f(u) − Σ_{k<n} c_k u^k)/u^n`.) (ii) `E₅` modulo `λ₃, λ₄` by the depth-five instance of (i) plus a fourth-order duplication (hand-rolled Leibniz for `iteratedDeriv` of a product, by induction — worth a general lemma `iteratedDeriv_mul` for `ContDiff` functions?) — or is (i) strictly better? (iii) ALL-ORDERS duplication `Γ^{(n)}(½)` in terms of `Γ^{(k)}(1)`, `k ≤ n` (needs `iteratedDeriv_mul`, `iteratedDeriv` of `Γ(2w)` and `2^{1−2w}`) — reduces every `Γ^{(j)}(½)` symbol to `Γ^{(k)}(1)` = the log-Gamma symbols `λ_k`; (iv) the ζ-recurrence packaging (`h₀ = 1`, `n h_n = Σ j b_j h_{n−j}`, `b_1 = (L+1)log2 − (L−1)γ`, `b_n = (2^n − 1 + L(−1)^n)ζ(n)/n` for `n ≥ 2`) as a definition + the theorem that under the bridge hypothesis `iteratedDeriv k H_L 0 / k! = h_k` the coefficients are `a_{L,k} = 2C_L h_{L−1−k}/k!` — only meaningful after (i); (v) NB surrogate posterior ratio; (vi) cone `c₃`; (vii) blow-up `N^{−3/2} log N`. Please give the exact statement you would formalise for (i) including normalisations (`s = √(2π)`, the `2^{k+1}` from `z = 1 − 2u`), and the coefficient identities at `L = 3` as a regression against DCLXXI (`c₁ = 2πB₃`, `c₂ = 2πC₃`, `Q₃ = c₃/4π`).
3. Convention hazards in DCLXXII–DCLXXIII (real-part symbols; `gammaLogKernel` as complex-valued with real `log`-scalar; `deriv^[r]` vs `iteratedDeriv`).
Answer concisely with Lean-facing detail.
