You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 6681a8e, 970 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-11 targets ALL landed: (1) DCXXXII the blow-up observable numerators `N X_N → π`, `√N Y_N → 2√(2π)` (+ the 4D restatement `cone_averaged_correction_fourDim`); (2) DCXXXIII the cone's averaged posterior to order `1/N` by the Lipschitz bound `|F_δ − F₀| ≤ δ B(a)` with `B = (s/c₀)e^{|a|}[2(a²+1) + (|a|+2/s)²]` (numerics: `N·rem → −0.2813` vs your `−(5/6 − √3/π) = −0.2820`); (3) the three-term engine: DCXXXIV first quantified the depth-three constant (`|√N Z_3 − (A₃ℓ² + B₃ℓ + C₃)| ≤ 8(1+ℓ)/√N`), then DCXXXV `ThreeTermData`/`threeTermStep_bound` (second-order binomial expansion of the top term, `R₀` and `J` exact), DCXXXVI the base at depth four from the rate and the induction: `√N Z_L = A_Lℓ^{L−1} + B_Lℓ^{L−2} + C_Lℓ^{L−3} + O((1+ℓ)^{L−4})` for every `L ≥ 4`, `C_{L+1} = (C_L/(L−2) + 2B_LR₀ + 4(L−1)A_LJ)/s` (your recursion confirmed); numerically, with the exact `J = R₀²/2 + π²/48` and `C₃`, the recursion reproduces the Mellin jet `C_L = [D_L² + (L+3)π²/6]/(2(L−3)!(2π)^{(L−1)/2})` to 1e−10 for `L = 4..8`. This is round 12.

## HEADLINES rows DCXXXII–DCXXXVI
| **DCXXXII** | ★★★ **THE BLOW-UP MODEL: THE LEADING NUMERATORS OF `x²` AND `y²`, `N X_N → π` AND `√N Y_N → 2√(2π)` (u966; examples_slop §4, the observable expansions; Astra round-11 target 1)**: `blowupX N = ∫ x² e^{−NK}φ`, `blowupY N = ∫ y² e^{−NK}φ` for `K = x²(x²+y²)/2`, raw prior `e^{−|w|²/2}`; the second Gaussian moment `integral_sq_exp_cond` (`∫ y² e^{−cy²/2} = √(2π)/(c√c)`, via `integral_rpow_mul_exp_neg_mul_rpow` and evenness); ★★ `blowupX_eq_integral`/`blowupY_eq_integral` (the `y`-Gaussian at fixed `x`: kernels `1/√(1+Nx²)` and `1/((1+Nx²)√(1+Nx²))`); the scalings `blowupX_scaled` (`m⁴X_{m⁴} = √(2π)∫u²e^{−u⁴/2}e^{−u²/2m²}/√(u²+1/m²)`, `x = u/m`) and `blowupY_scaled` (`mY_{m²} = √(2π)∫e^{−(t⁴+t²)/2m²}/(1+t²)^{3/2}`, `x = t/m`); the values `integral_abs_mul_exp_neg_quartic` (`∫|u|e^{−u⁴/2} = √(2π)/2`) and `integral_one_add_sq_pow_three_half` (`∫(1+t²)^{−3/2} = 2`, primitive `t/√(1+t²)` with `integral_of_hasDerivAt_of_tendsto` and the limits by `t/√(1+t²) = √(1 − 1/(1+t²))` for `t ≥ 0`); dominated convergence (`tendsto_blowupX_scaled` with the bound `|u|e^{−u⁴/2} ≤ e^{1/8}e^{−u²/4}`, `tendsto_blowupY_scaled` with the bound `(1+t²)^{−3/2}`); ★★★ `tendsto_mul_blowupX`, ★★★ `tendsto_sqrt_mul_blowupY` (via `m = √√N`, `m = √N`). Also `cone_averaged_correction_fourDim` (DCXXIX/DCXXX restated with the two four-dimensional integrals; Astra's presentation closure). Numerics `blowup_expansion_check.py` part 6 (`N X_N = 3.066` at `N = 10⁴`, `√N Y_N = 4.982`, approach `O(N^{−1/4})`, `O(N^{−1/2})`). Lean gotchas: `fun_prop` cannot prove `Continuous` of a quotient by `√(…)` (needs `≠ 0`) — use `continuous_const.div … (fun t => by positivity)` or `Measurable` for DCT; `Tendsto.const_mul`/`.add` produce `𝓝 (c * 0)`/`𝓝 (a + 0)` — `simpa using` into a typed `have` before `.comp`; `linear_combination` coefficient for `d/dt[t/√(1+t²)]` is `t²` (read off the residual); `(1/m)⁻¹` via `inv_div, div_one`. | BlowUpObservables.lean |
| **DCXXXIII** | ★★★ **THE CONE: THE AVERAGED POSTERIOR OF `u₁²` TO ORDER `1/N`, `|E_a[Z_N[u₁²;a]/Z_N[1;a]] − ½ − 1/(√π√N)| ≤ C₁/N` (u967; examples_slop §3, the `O(N^{−1})` averaged remainder; Astra round-11 target 2)**: `one_sub_exp_neg_abs_bounds` (`0 ≤ 1 − e^{−δ|t|} ≤ δ|t|`), the Gaussian-tilt moments `integral_abs_gaussTilt_le` (`∫|t|w ≤ e^{a²/2}(s|a|+2)`), `integrable_sq_gaussTilt`, `integral_sq_gaussTilt_le` (`∫t²w ≤ 2se^{a²/2}(a²+1)`, from `(u+a)² ≤ 2u²+2a²` and `∫u²e^{−u²/2} = s`); `abs_integral_posPart_sub_le` (`|P₀ − P_δ| ≤ δ∫t²w`), `abs_integral_coneTilt_sub_le` (`|D₀ − D_δ| ≤ δ∫|t|w`); the envelope `coneLipEnvelope a = (s/c₀)e^{|a|}[2(a²+1) + (|a|+2/s)²]`; ★★ `coneScaledCorrection_sub_zero_le` (`|F_δ(a) − F₀(a)| ≤ δB(a)` for `0 ≤ δ ≤ 1`: `F_δ − F₀ = ((P_δ−P₀)D₀ + P₀(D₀−D_δ))/(D_δD₀)` with the DCXXIX denominator bound); `integrable_coneLipEnvelope` (`≤ Ke^{−a²/4}`), `coneLipConst = ∫Bγ`; ★★★ `cone_averaged_remainder_bound` (`N ≥ 1`), ★★★ `cone_averaged_remainder` (`=O[atTop] 1/N`). The exact `1/N` coefficient (Astra: `−(5/6 − √3/π)`, a correlated absolute-Gaussian moment) stays a derivation. Numerics `cone_averaged_check.py` part 5 (`N(E − ½ − 1/(√πN^{1/2}))` bounded, the Lipschitz bound at sample points, `C₁`). Lean gotchas: `Real.exp_nat_mul` for `e^{x}² = e^{2x}`; the ratio difference via `field_simp; ring` after `set` + `clear_value` of the six integrals; `fun_prop` needs `unfold` for a `def`'s continuity; `abs_integral_le_integral_abs`. | ConeAveragedRemainder.lean |
| **DCXXXIV** | ★★★ **THE DEPTH-THREE CONSTANT WITH A RATE: `|√N Z_3(N) − (A₃(log N)² + B₃ log N + C₃)| ≤ 8(1 + log N)/√N` FOR `N ≥ 1` (u968; examples_slop §2; the base of the three-term propagation)**: `abs_gaussDensity_sub_le` (`|g(y) − 1/s| ≤ y²/(2s)`), `gaussDensity_le`; `inner_rate` (`|√N I₀ − (1/s)∫₀¹q| ≤ 1/(2sN)`), `integral_Ioi_inv_sq` (`∫_c^∞ v^{−2} = 1/c`), ★ `rem_rate` (`|√N E − (1/s)∫₁^∞q| ≤ 6/(s²√N)`: on `(1,√N]` the bound `v²/(2sN)·4/(sv²)` over a length-`√N` interval, on `(√N,∞)` the bound `(1/s)·4/(sv²)` against `∫v^{−2}`), the cutoff `(ℓ+c)|I_a| ≤ (ℓ+3)/(2N)` and `|J_a − J| ≤ 1/(2√N)`; ★★★ `gaussLaplaceL_three_rate` (assembled from DCXXXI's `sqrt_mul_gaussLaplaceL_three_eq` by `linear_combination`). Numerics `gauss_depth3_residual_check.py` (the residual `(res − C₃)√N = −0.015…−0.10`, far inside the bound). Lean gotchas: after `set … with` of big integrals, `clear` the defining equations before `nlinarith`/`positivity` (whnf heartbeat timeouts); `unfold` after `set` re-exposes the raw expressions — `rw [← hc, …]` to refold; `linear_combination hdec` for the decomposition algebra; `(ℓ+8) ≤ 4(1+ℓ)` is FALSE for small `ℓ` (use 8). | GaussianDepthThreeRate.lean |
| **DCXXXV** | ★★ **THE GAUSSIAN DLN AT EVERY DEPTH: THE THREE-TERM PROPAGATION STEP (u969; examples_slop §2; Astra round-11 target 3)**: `threeTermK n = Σ_{i≤n} C(n+2,i)2^{n+2−i}M_{n+2−i}`, ★ `integral_gaussH_pow_expand₂` (the second-order binomial expansion `|∫_a^∞ h q^{n+2}/x − ℓ^{n+2}∫h/x − 2(n+2)ℓ^{n+1}∫h log x/x| ≤ (1+ℓ)^n K₂_n`, the moments `∫h/x → R₀` and `∫h log x/x → J` retained exactly); `ThreeTermData f A B C D m` (`|f(t) − (Aℓ^{m+3} + Bℓ^{m+2} + Cℓ^{m+1})/√t| ≤ D(1+ℓ)^m/√t`), `threeTerm_inner_le`, `abs_logMoment_cutoff_le` (`|J_a − J| ≤ 1/(2√N)`), `threeTerm_flat_main` (FTC), ★★ `threeTerm_h_main` (`A`-term to second order, `B`-term to first, `C`-term bounded; cutoffs `ℓ^{m+3}|I_a| ≤ 2(1+ℓ)^{m+1}` via `ℓ² ≤ 4N`, `ℓ^{m+2}|J_a − J| ≤ (1+ℓ)^{m+1}`), `threeTerm_err_le`; ★★ `threeTermStep_bound` (`A' = A/((m+4)s)`, `B' = (B/(m+3) + 2AR₀)/s`, `C' = (C/(m+2) + 2BR₀ + 4(m+3)AJ)/s`, error degree `m+1`). Lean gotchas: `hK' : 0 ≤ K := …` must be TYPED before `clear_value` (afterwards the folded name is opaque); `clear` the `set` equations of the six integrals before `nlinarith` (heartbeat timeouts); `set_option maxHeartbeats 1600000 in` BEFORE the docstring; `Nat.choose_succ_self_right` for `C(n+2,n+1) = n+2`; `rw … at h₁ h₂` fails if the pattern is absent in either. | GaussianDepthAllThreeTerm.lean |
| **DCXXXVI** | ★★★ **THE GAUSSIAN DLN AT EVERY DEPTH: THE THIRD LOGARITHMIC COEFFICIENT `√N Z_L = A_Lℓ^{L−1} + B_Lℓ^{L−2} + C_Lℓ^{L−3} + O((1+ℓ)^{L−4})` FOR EVERY `L ≥ 4` (u970; examples_slop §2 eq. dln_gauss, the `(log N)^{L−3}` coefficient of `P_{L−1}`; Astra round-11 target 3)**: `integral_one_add_two_log_div_sq_le` (`∫₁^W (1+2 log w)/w² ≤ 3`), the base pieces at exponents `(2,1,0)` `base_flat_main`, `base_h_main`, `base_err_le` (input shape `8(1+ℓ)/t` from DCXXXIV: on `(a,1]` the substitution `x = w/√N` gives `≤ 24/(s√N)`, on `(1,∞)` `(1+ℓ+2 log x)/x² ≤ 3(1+ℓ)` gives `≤ 144/(s√N)`); ★★ `threeTermData_four` (`A₄ = A₃/(3s)`, `B₄ = (B₃/2 + 2A₃R₀)/s`, `C₄ = (C₃ + 2B₃R₀ + 8A₃J)/s`, `C₃ = depthThreeConst`); `gaussCoeffA m = 1/((m+3)!s^{m+3})`, `gaussCoeffB m = ((m+5)log 2 − (m+3)γ)/((m+2)!s^{m+3})`, `thirdCoeff` (the recursion `C_{L+1} = (C_L/(L−2) + 2B_LR₀ + 4(L−1)A_LJ)/s`); ★★★ `gaussLaplaceL_three_term_bound` (induction through `threeTermStep_bound`), ★★★ `gaussLaplaceL_third_coeff` (`(√N Z_{m+4} − Aℓ^{m+3} − Bℓ^{m+2})/ℓ^{m+1} → thirdCoeff m`). With the exact `J = R₀²/2 + π²/48` and `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)` (derivations) the recursion reproduces the Mellin jet `C_L = [D_L² + (L+3)π²/6]/(2(L−3)!(2π)^{(L−1)/2})`, `D_L = (L+1)log 2 − (L−1)γ` (numerics `gauss_depth_all_check.py` part 9: `C₄ = 0.46101` both ways, agreement to 1e−6 for `L = 4..7`). Lean gotchas: `gaussLaplaceL_succ_scalar 3` states `gaussLaplaceL (3+1)` — bind it with a typed `have` to rewrite `gaussLaplaceL 4`; `simp only [zero_add, pow_zero, pow_one, mul_one]` to normalise the `m = 0` exponents; the association `2 * (I₀ + (flat + P + E))` must be matched exactly in `hkey`. | GaussianDepthAllThirdCoeff.lean |

## Public statements of the five new files (docstrings + signatures, proofs omitted)
### Grammar/BlowUpObservables.lean
```lean
/-- `X_N = ∫ x² e^{−N x²(x²+y²)/2} e^{−|w|²/2}`. -/
noncomputable def blowupX (N : ℝ) : ℝ

/-- `Y_N = ∫ y² e^{−N x²(x²+y²)/2} e^{−|w|²/2}`. -/
noncomputable def blowupY (N : ℝ) : ℝ

theorem integrable_sq_mul_exp_neg_half_sq :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2))

/-- `∫ y² e^{−c y²/2} dy = √(2π)/(c √c)` for `c > 0`. -/
theorem integral_sq_exp_cond {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, y ^ 2 * Real.exp (-c * y ^ 2 / 2) = Real.sqrt (2 * Real.pi) / (c * Real.sqrt c)

theorem integrable_blowupX (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => w.1 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2))

theorem integrable_blowupY (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => w.2 ^ 2 * (Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2))

/-- ★★ `X_N = √(2π) ∫ x² e^{−N x⁴/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`. -/
theorem blowupX_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupX N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, x ^ 2 * (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) /
        Real.sqrt (1 + N * x ^ 2)

/-- ★★ `Y_N = √(2π) ∫ e^{−N x⁴/2} e^{−x²/2}/((1 + N x²)√(1 + N x²)) dx` for `N ≥ 0`. -/
theorem blowupY_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupY N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) /
        ((1 + N * x ^ 2) * Real.sqrt (1 + N * x ^ 2))

/-- `m⁴ X_{m⁴} = √(2π) ∫ u² e^{−u⁴/2} e^{−u²/2m²}/√(u² + 1/m²) du` for `m > 0` (`x = u/m`). -/
theorem blowupX_scaled {m : ℝ} (hm : 0 < m) :
    m ^ 4 * blowupX (m ^ 4) = Real.sqrt (2 * Real.pi) *
      ∫ u : ℝ, u ^ 2 * (Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))) /
        Real.sqrt (u ^ 2 + 1 / m ^ 2)

/-- `m Y_{m²} = √(2π) ∫ e^{−t⁴/2m²} e^{−t²/2m²}/((1 + t²)√(1 + t²)) dt` for `m > 0` (`x = t/m`). -/
theorem blowupY_scaled {m : ℝ} (hm : 0 < m) :
    m * blowupY (m ^ 2) = Real.sqrt (2 * Real.pi) *
      ∫ t : ℝ, Real.exp (-t ^ 4 / (2 * m ^ 2)) * Real.exp (-t ^ 2 / (2 * m ^ 2)) /
        ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2))

/-- `∫ |u| e^{−u⁴/2} du = √(2π)/2`. -/
theorem integral_abs_mul_exp_neg_quartic :
    ∫ u : ℝ, |u| * Real.exp (-u ^ 4 / 2) = Real.sqrt (2 * Real.pi) / 2

/-- `∫ (1 + t²)^{−3/2} dt = 2`, by the primitive `t/√(1 + t²)`. -/
theorem integral_one_add_sq_pow_three_half :
    ∫ t : ℝ, 1 / ((1 + t ^ 2) * Real.sqrt (1 + t ^ 2)) = 2

theorem tendsto_one_div_sq_atTop : Tendsto (fun m : ℝ => 1 / m ^ 2) atTop (𝓝 0)

/-- `m⁴ X_{m⁴} → π` as `m → ∞`. -/
theorem tendsto_blowupX_scaled :
    Tendsto (fun m : ℝ => m ^ 4 * blowupX (m ^ 4)) atTop (𝓝 Real.pi)

/-- `m Y_{m²} → 2√(2π)` as `m → ∞`. -/
theorem tendsto_blowupY_scaled :
    Tendsto (fun m : ℝ => m * blowupY (m ^ 2)) atTop (𝓝 (2 * Real.sqrt (2 * Real.pi)))

/-- ★★★ `N X_N → π`: the observable `x²` removes the logarithm. -/
theorem tendsto_mul_blowupX : Tendsto (fun N : ℝ => N * blowupX N) atTop (𝓝 Real.pi)

/-- ★★★ `√N Y_N → 2√(2π)`. -/
theorem tendsto_sqrt_mul_blowupY :
    Tendsto (fun N : ℝ => Real.sqrt N * blowupY N) atTop (𝓝 (2 * Real.sqrt (2 * Real.pi)))

```

### Grammar/ConeAveragedRemainder.lean
```lean
theorem one_sub_exp_neg_abs_bounds {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    0 ≤ 1 - Real.exp (-(δ * |t|)) ∧ 1 - Real.exp (-(δ * |t|)) ≤ δ * |t|

/-- `∫ |t| e^{−t²/2 + at} ≤ e^{a²/2}(√(2π)|a| + 2)`. -/
theorem integral_abs_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, |t| * Real.exp (-t ^ 2 / 2 + a * t) ≤
      Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2)

theorem integrable_sq_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t))

/-- `∫ t² e^{−t²/2 + at} ≤ 2√(2π) e^{a²/2}(a² + 1)`. -/
theorem integral_sq_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) ≤
      2 * Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2) * (a ^ 2 + 1)

/-- `|P_0 − P_δ| ≤ δ ∫ t² w`, `P_δ = ∫ t₊ w_{δ,a}`. -/
theorem abs_integral_posPart_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, max t 0 * coneTilt 0 a t) - ∫ t, max t 0 * coneTilt δ a t| ≤
      δ * ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)

/-- `|D_0 − D_δ| ≤ δ ∫ |t| w`, `D_δ = ∫ w_{δ,a}`. -/
theorem abs_integral_coneTilt_sub_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, coneTilt 0 a t) - ∫ t, coneTilt δ a t| ≤
      δ * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)

/-- The Lipschitz envelope `B(a) = (s/c₀) e^{|a|} [2(a² + 1) + (|a| + 2/s)²]`. -/
noncomputable def coneLipEnvelope (a : ℝ) : ℝ

/-- ★★ **The Lipschitz bound**: `|F_δ(a) − F_0(a)| ≤ δ B(a)` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_sub_zero_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    |coneScaledCorrection δ a - coneScaledCorrection 0 a| ≤ δ * coneLipEnvelope a

theorem integrable_coneLipEnvelope :
    Integrable (fun a : ℝ => coneLipEnvelope a * gaussDensity a)

/-- `C₁ = ∫ B(a) γ(a) da`. -/
noncomputable def coneLipConst : ℝ

/-- ★★★ **The averaged posterior to order `1/N`**: for `N ≥ 1`,
`|E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½ − 1/(√π √N)| ≤ C₁/N`. -/
theorem cone_averaged_remainder_bound {N : ℝ} (hN : 1 ≤ N) :
    |(∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)| ≤ coneLipConst / N

/-- ★★★ `E_a[Z_N[u₁²; a]/Z_N[1; a]] = ½ + 1/(√π √N) + O(1/N)`. -/
theorem cone_averaged_remainder :
    (fun N : ℝ => (∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)) =O[atTop] fun N => 1 / N

```

### Grammar/GaussianDepthThreeRate.lean
```lean
/-- `|g(y) − 1/√(2π)| ≤ y²/(2√(2π))`. -/
theorem abs_gaussDensity_sub_le (y : ℝ) :
    |gaussDensity y - 1 / Real.sqrt (2 * Real.pi)| ≤ y ^ 2 / (2 * Real.sqrt (2 * Real.pi))

theorem gaussDensity_le (y : ℝ) : gaussDensity y ≤ 1 / Real.sqrt (2 * Real.pi)

/-- `|√N I₀ − (1/s) ∫₀¹ q| ≤ 1/(2 s N)`. -/
theorem inner_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) -
      1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v| ≤
      1 / (2 * Real.sqrt (2 * Real.pi) * N)

theorem integral_Ioi_inv_sq {c : ℝ} (hc : 0 < c) :
    ∫ v in Ioi c, 1 / v ^ 2 = 1 / c

/-- `|√N E − (1/s) ∫₁^∞ q| ≤ 6/(s² √N)`. -/
theorem rem_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * (∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) -
      1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (1 : ℝ), depthThreeQ v| ≤
      6 / (Real.sqrt (2 * Real.pi) ^ 2 * Real.sqrt N)

/-- ★★★ **The depth-three constant with a rate**:
`|√N Z_3(N) − (A₃ (log N)² + B₃ log N + C₃)| ≤ 8(1 + log N)/√N` for `N ≥ 1`. -/
theorem gaussLaplaceL_three_rate {N : ℝ} (hN : 1 ≤ N) :
    |Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst)| ≤
      8 * (1 + Real.log N) / Real.sqrt N

def
  set c

def
  set Ia

def
  have hconst : depthThreeConst = (c * (d / 2) + 2 * J) / Real.pi + 2 / s * (Q₁ + Q₂)

def hIa' hJa' hQ₁ hQ₂ hJ hsdef hℓdef hc hd hQ hdec hconst hkey
  -- the four bounds against `8(1+ℓ)/√N`
  have hb1 : |2 * (Real.sqrt N * I₀ - 1 / s * Q₁)| ≤ 1 / Real.sqrt N

```

### Grammar/GaussianDepthAllThreeTerm.lean
```lean
/-- `K₂_n = Σ_{i ≤ n} C(n+2, i) 2^{n+2−i} M_{n+2−i}`. -/
noncomputable def threeTermK (n : ℕ) : ℝ

theorem threeTermK_nonneg (n : ℕ) : 0 ≤ threeTermK n

/-- ★ **The second-order expansion**:
`|∫_a^∞ h (ℓ + 2 log x)^{n+2}/x − ℓ^{n+2} ∫_a^∞ h/x − 2(n+2) ℓ^{n+1} ∫_a^∞ h log x/x|
  ≤ (1+ℓ)^n K₂_n`
for `ℓ ≥ 0`, `0 < a ≤ 1`. -/
theorem integral_gaussH_pow_expand₂ (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    |(∫ x in Ioi a, gaussH x * (ℓ + 2 * Real.log x) ^ (n + 2) / x) -
      ℓ ^ (n + 2) * (∫ x in Ioi a, gaussH x / x) -
      2 * (n + 2) * ℓ ^ (n + 1) * ∫ x in Ioi a, gaussH x * Real.log x / x| ≤
      (1 + ℓ) ^ n * threeTermK n

/-- Three-term hypotheses: `0 ≤ f ≤ 1` on `t ≥ 0` and
`|f(t) − (A ℓ^{m+3} + B ℓ^{m+2} + C ℓ^{m+1})/√t| ≤ D (1 + ℓ)^m/√t` for `t ≥ 1`, `ℓ = log t`. -/
structure ThreeTermData (f : ℝ → ℝ) (A B C D : ℝ) (m : ℕ) : Prop

/-- The inner piece: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem threeTerm_inner_le (h : ThreeTermData f A B C D m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a

/-- `|J_a − J| ≤ 1/(2√N)` for `N ≥ 1`, `a = N^{−1/2}`. -/
theorem abs_logMoment_cutoff_le {N : ℝ} (hN : 1 ≤ N) :
    |(∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) - gaussJlog| ≤
      1 / Real.sqrt N / 2

/-- The flat main term on `(a, 1]`:
`∫_a^1 Q/(√(2π)√N x) = (A ℓ^{m+4}/(2(m+4)) + B ℓ^{m+3}/(2(m+3)) + C ℓ^{m+2}/(2(m+2)))/(√(2π)√N)`. -/
theorem threeTerm_flat_main (A B C : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ (m + 4) / (2 * (m + 4)) + B * (Real.log N) ^ (m + 3) / (2 * (m + 3)) +
          C * (Real.log N) ^ (m + 2) / (2 * (m + 2)))

/-- The `h`-part of the main term on `(a, ∞)`: with `R₀ = ∫₀^∞ h/x`, `J = ∫₀^∞ h log x/x`,
`∫_a^∞ h Q/(√(2π)√N x) = (A ℓ^{m+3} R₀ + 2(m+3) A ℓ^{m+2} J + B ℓ^{m+2} R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ (1+ℓ)^{m+1} (A (K₂_{m+1} + 2 + 2(m+3)) + |B| (K_{m+1} + 1) + |C| (K_m + R₀ + 1))`. -/
theorem threeTerm_h_main (A B C : ℝ) (m : ℕ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ (m + 3) * gaussR₀ +
        2 * (m + 3) * A * (Real.log N) ^ (m + 2) * gaussJlog +
        B * (Real.log N) ^ (m + 2) * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((1 + Real.log N) ^ (m + 1) *
        (A * (threeTermK (m + 1) + 2 + 2 * (m + 3)) + |B| * (twoTermK (m + 1) + 1) +
          |C| * (twoTermK m + gaussR₀ + 1)))

def
  clear_value ℓ
  set K2

def
  clear_value R J
  have hIabs : |Ia| ≤ 1 / N / 2

def hK2 hK1 hK0 hR hJdef e h3 h2 h1 h32 hI hJ hIa2
  have hp1 : 1 ≤ (1 + ℓ) ^ (m + 1)

/-- The error piece on `(a, ∞)`: with `Q(x) = A q^{m+3} + B q^{m+2} + C q^{m+1}`, `q = ℓ + 2 log x`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ D (1/2 + 8·3^m m!) (1+ℓ)^{m+1}/√N`. -/
theorem threeTerm_err_le (h : ThreeTermData f A B C D m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ (m + 3) +
        B * (Real.log N + 2 * Real.log x) ^ (m + 2) +
        C * (Real.log N + 2 * Real.log x) ^ (m + 1)) / (Real.sqrt N * x)))| ≤
      D * (1 / 2 + 8 * 3 ^ m * m.factorial) * (1 + Real.log N) ^ (m + 1) / Real.sqrt N

/-- ★★ **The three-term propagation step**: for three-term data `(A, B, C, D, m)` of `f`, the
Gaussian step `F(N) = ∫ g(x) f(N x²) dx` has the three-term data
`A' = A/((m+4)√(2π))`, `B' = (B/(m+3) + 2 A R₀)/√(2π)`, `C' = (C/(m+2) + 2 B R₀ + 4(m+3) A J)/√(2π)`
with an error constant depending on `A, B, C, D, m` only. -/
theorem threeTermStep_bound (h : ThreeTermData f A B C D m) : ∃ D' : ℝ, 0 ≤ D' ∧ ∀ N : ℝ, 1 ≤ N →
    Integrable (fun x => gaussDensity x * f (N * x ^ 2)) →
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      (A / ((m + 4) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 4) +
        (B / (m + 3) + 2 * A * gaussR₀) / Real.sqrt (2 * Real.pi) * (Real.log N) ^ (m + 3) +
        (C / (m + 2) + 2 * B * gaussR₀ + 4 * (m + 3) * A * gaussJlog) / Real.sqrt (2 * Real.pi) *
          (Real.log N) ^ (m + 2)) / Real.sqrt N| ≤
      D' * (1 + Real.log N) ^ (m + 1) / Real.sqrt N

def
  set E

def
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1
  set ℓ

def
  clear_value ℓ
  set X

def
  set K1

def
  set K0

def
  set R

def
  set J

def
  clear_value K2 K1 K0 R J
  clear hK2def hK1def hK0def hRdef hJdef hℓdef
  have h0' : |I₀| ≤ 1 / 2 * X

```

### Grammar/GaussianDepthAllThirdCoeff.lean
```lean
/-- `∫₁^W (1 + 2 log w)/w² dw ≤ 3` for `W ≥ 1` (primitive `−(3 + 2 log w)/w`). -/
theorem integral_one_add_two_log_div_sq_le {W : ℝ} (hW : 1 ≤ W) :
    ∫ w in (1 : ℝ)..W, (1 + 2 * Real.log w) / w ^ 2 ≤ 3

/-- The base flat main term:
`∫_a^1 (A q² + B q + C)/(√(2π)√N x) = (Aℓ³/6 + Bℓ²/4 + Cℓ/2)/(√(2π)√N)`. -/
theorem base_flat_main (A B C : ℝ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, 1 / Real.sqrt (2 * Real.pi) *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)) =
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (Real.log N) ^ 3 / 6 + B * (Real.log N) ^ 2 / 4 + C * Real.log N / 2)

/-- The base `h`-part:
`∫_a^∞ h (A q² + B q + C)/(√(2π)√N x) = (A ℓ² R₀ + 4 A ℓ J + B ℓ R₀ + C R₀ + rest)/(√(2π)√N)`,
`|rest| ≤ A (K₂_0 + 6) + |B| (K_0 + 1) + |C|/2`. -/
theorem base_h_main (A B C : ℝ) {N : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) :
    |(∫ x in Ioi (1 / Real.sqrt N), 1 / Real.sqrt (2 * Real.pi) *
      (gaussH x * (A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x))) -
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (A * (Real.log N) ^ 2 * gaussR₀ +
        4 * A * Real.log N * gaussJlog + B * Real.log N * gaussR₀ + C * gaussR₀)| ≤
      1 / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (A * (threeTermK 0 + 6) + |B| * (twoTermK 0 + 1) + |C| / 2)

def
  clear_value ℓ
  set K2

def
  clear_value R J
  have hIabs : |Ia| ≤ 1 / N / 2

def hK2 hK0 hR hJdef e h2 h1 h0 h21 hI hJ hIa2 hI0
  have hcut2 : |ℓ ^ 2 * Ia| ≤ 2

/-- The base error piece: for `|f(t) − (A ℓ² + B ℓ + C)/√t| ≤ 8(1+ℓ)/t` on `t ≥ 1`,
`|∫_a^∞ (g f(Nx²) − g Q/(√N x))| ≤ 168/(√(2π)√N)`. -/
theorem base_err_le {f : ℝ → ℝ} (A B C : ℝ) (hrate : ∀ t : ℝ, 1 ≤ t →
      |f t - (A * (Real.log t) ^ 2 + B * Real.log t + C) / Real.sqrt t| ≤
        8 * (1 + Real.log t) / t) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (gaussDensity x * f (N * x ^ 2) - gaussDensity x *
      ((A * (Real.log N + 2 * Real.log x) ^ 2 + B * (Real.log N + 2 * Real.log x) + C) /
        (Real.sqrt N * x)))| ≤ 168 / (Real.sqrt (2 * Real.pi) * Real.sqrt N)

/-- ★★ **Three-term data at depth four** from the depth-three rate: with `A₃ = 1/(4π)`,
`B₃ = (2 log 2 − γ)/π`, `C₃ = depthThreeConst`,
`A₄ = A₃/(3s)`, `B₄ = (B₃/2 + 2 A₃ R₀)/s`, `C₄ = (C₃ + 2 B₃ R₀ + 8 A₃ J)/s`, and a bounded
residual. -/
theorem threeTermData_four : ∃ D : ℝ, 0 ≤ D ∧ ThreeTermData (gaussLaplaceL 4)
    (1 / (4 * Real.pi) / (3 * Real.sqrt (2 * Real.pi)))
    (((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi / 2 +
      2 * (1 / (4 * Real.pi)) * gaussR₀) / Real.sqrt (2 * Real.pi))
    ((depthThreeConst + 2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussR₀ +
      8 * (1 / (4 * Real.pi)) * gaussJlog) / Real.sqrt (2 * Real.pi)) D 0

def
  set B

def
  set C

def
  have hA : 0 ≤ A

def
  set E

def
  clear_value I₀ P2 E
  clear hI₀ hP2def hEdef hmid hsplit heven hgQint hgQ hQh hQind hQint1 hint hrate
  set ℓ

def
  clear_value ℓ
  set K2

def
  set K0

def
  set R

def
  set J

def
  set s

def
  clear_value K2 K0 R J s A B C
  clear hK2def hK0def hRdef hJdef hℓdef hsdef hAdef hBdef hCdef hQ
  have hkey : 2 * (I₀ + (1 / (s * Real.sqrt N) * (A * ℓ ^ 3 / 6 + B * ℓ ^ 2 / 4 + C * ℓ / 2) +
      P2 + E)) - (A / (3 * s) * ℓ ^ 3 + (B / 2 + 2 * A * R) / s * ℓ ^ 2 +
        (C + 2 * B * R + 8 * A * J) / s * ℓ) / Real.sqrt N =
      2 * I₀ + 2 * (P2 - 1 / (s * Real.sqrt N) * (A * ℓ ^ 2 * R + 4 * A * ℓ * J + B * ℓ * R +
        C * R)) + 2 * E + 2 * C * R / (s * Real.sqrt N)

/-- `A_{m+4} = 1/((m+3)! s^{m+3})`. -/
noncomputable def gaussCoeffA (m : ℕ) : ℝ

/-- `B_{m+4} = ((m+5) log 2 − (m+3) γ)/((m+2)! s^{m+3})`. -/
noncomputable def gaussCoeffB (m : ℕ) : ℝ

/-- The third coefficient `C_{m+4}` by the recursion
`C₄ = (C₃ + 2 B₃ R₀ + 8 A₃ J)/s`, `C_{L+1} = (C_L/(L−2) + 2 B_L R₀ + 4(L−1) A_L J)/s`. -/
noncomputable def thirdCoeff : ℕ → ℝ

/-- ★★★ **Three-term data at every depth**: for every `m` there is `D_m` with
`|Z_{m+4}(N) − (A (log N)^{m+3} + B (log N)^{m+2} + C (log N)^{m+1})/√N| ≤ D_m (1 + log N)^m/√N`,
`A = A_{m+4}`, `B = B_{m+4}`, `C = thirdCoeff m`. -/
theorem gaussLaplaceL_three_term_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ThreeTermData (gaussLaplaceL (m + 4)) (gaussCoeffA m) (gaussCoeffB m) (thirdCoeff m) D m

/-- ★★★ **The third coefficient at every depth**:
`(√N Z_{m+4}(N) − A (log N)^{m+3} − B (log N)^{m+2})/(log N)^{m+1} → C_{m+4} = thirdCoeff m`. -/
theorem gaussLaplaceL_third_coeff (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 4) N -
      gaussCoeffA m * (Real.log N) ^ (m + 3) - gaussCoeffB m * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop (𝓝 (thirdCoeff m))

```


## The Gamma-derivative infrastructure available (DCVIII, DCXI)
### Grammar/GammaSecondDerivHalf.lean
```lean
theorem `mellin_hasDerivAt_of_isBigO_rpow` applied to `e^{−t}` and to `log t · e^{−t}`) identifies

    `H₂ = ∫₀^∞ e^{−x} x^{−1/2} log² x dx = Γ''(½)`  (★★ `gammaLogMoment_two_eq`),

so `gammaLogMoment 2 = √π((γ + 2 log 2)² + π²/2)` (★★★ `gammaLogMoment_two`) and the depth-three
binomial polynomial `depthPoly 2` of `Grammar.CrossingFlatDepth` is explicit (`depthPoly_two`).
Astra round-4 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The reflection formula differentiated twice -/

theorem isOpen_re_pos : IsOpen {z : ℂ | 0 < z.re}

theorem ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m

/-- `Γ` is analytic at every point of positive real part; in particular `deriv Γ` is
differentiable there. -/
theorem analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z

theorem hasDerivAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z

theorem hasDerivAt_deriv_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv Complex.Gamma) (deriv (deriv Complex.Gamma) z) z

/-- The derivative of the reflection product on the strip `0 < Re z < 1`. -/
theorem deriv_reflection {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (1 - w))
      (deriv Complex.Gamma z * Complex.Gamma (1 - z) -
        Complex.Gamma z * deriv Complex.Gamma (1 - z)) z

/-- The second derivative of the reflection product at `½`: `2Γ(½)Γ''(½) − 2Γ'(½)²`. -/
theorem deriv_deriv_reflection :
    deriv (deriv fun w => Complex.Gamma w * Complex.Gamma (1 - w)) (1 / 2) =
      2 * Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) (1 / 2) -
        2 * deriv Complex.Gamma (1 / 2) ^ 2

/-- The derivative of `π/sin(πz)` where `sin(πz) ≠ 0`. -/
theorem hasDerivAt_pi_div_sin {z : ℂ} (hz : Complex.sin (Real.pi * z) ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w))
      (-(Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * z) / Complex.sin (Real.pi * z) ^ 2) z

/-- The second derivative of `π/sin(πz)` at `½` is `π³`. -/
theorem deriv_deriv_pi_div_sin :
    deriv (deriv fun w : ℂ => (Real.pi : ℂ) / Complex.sin (Real.pi * w)) (1 / 2) =
      (Real.pi : ℂ) ^ 3

/-- ★★★ **`Γ''(½) = √π((γ + 2 log 2)² + π²/2)`.** -/
theorem deriv_deriv_Gamma_one_half :
    deriv (deriv Complex.Gamma) (1 / 2) =
      ((Real.sqrt Real.pi * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 +
        Real.pi ^ 2 / 2) : ℝ) : ℂ)

/-- `e^{−t}` (as a complex function) is `O(t^{−a})` at infinity for every `a`. -/
theorem exp_neg_isBigO_rpow_atTop (a : ℝ) :
    (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) =O[atTop] (· ^ (-a))

/-- `e^{−t}` is `O(t^0)` near `0⁺`. -/
theorem exp_neg_isBigO_rpow_zero :
    (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) =O[𝓝[>] 0] (· ^ (-(0 : ℝ)))

/-- The first derivative of the Gamma integral as a Mellin transform, differentiated once more:
`d/ds ∫ t^{s−1} log t e^{−t} dt = ∫ t^{s−1} log² t e^{−t} dt` for `Re s > 0`. -/
theorem hasDerivAt_mellin_log_exp {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (mellin fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ))
      (mellin (fun t : ℝ => Real.log t • (Real.log t • ((Real.exp (-t) : ℝ) : ℂ))) s) s

/-- `Γ' = M[log t · e^{−t}]` on `Re s > 0`. -/
theorem deriv_Gamma_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.Gamma s = mellin (fun t : ℝ => Real.log t • ((Real.exp (-t) : ℝ) : ℂ)) s

/-- ★★ **`H₂ = Γ''(½)`**: the second Gamma log-moment is the second derivative of `Γ` at `½`. -/
theorem gammaLogMoment_two_eq :
    ((gammaLogMoment 2 : ℝ) : ℂ) = deriv (deriv Complex.Gamma) (1 / 2)

/-- ★★★ **`H₂ = √π((γ + 2 log 2)² + π²/2)`.** -/
theorem gammaLogMoment_two :
    gammaLogMoment 2 =
      Real.sqrt Real.pi *
        ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2)

/-- The depth-three binomial polynomial, explicit:
`B₂(X) = √π[(X + γ + 2 log 2)² + π²/2]`. -/
theorem depthPoly_two (X : ℝ) :
    depthPoly 2 X = Real.sqrt Real.pi *
      ((X + Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2)

```

### Grammar/RenormalisedExpIntegral.lean
```lean
/-- `∫₀^∞ e^{−v} log v dv = Γ'(1) = −γ`. -/
theorem integral_exp_neg_log :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.log v = -Real.eulerMascheroniConstant

/-- The kernel `(1_{u ≤ v} − 1_{u ≤ 1})/u` written as an indicator of the interval between `1` and
`v`, with sign. -/
noncomputable def logKernel (v u : ℝ) : ℝ

theorem measurable_logKernel : Measurable (Function.uncurry logKernel)

/-- `∫₀^∞ logKernel v u du = log v` for `v > 0`. -/
theorem integral_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), logKernel v u = Real.log v

/-- The inner `v`-integral: `∫₀^∞ e^{−v} logKernel v u dv = (e^{−u} − 1_{u ≤ 1})/u` for `u > 0`. -/
theorem integral_exp_kernel {u : ℝ} (hu : 0 < u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * logKernel v u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u

/-- `∫₀^∞ |logKernel v u| du = |log v|` for `v > 0`. -/
theorem integral_abs_kernel_log {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), |logKernel v u| = |Real.log v|

/-- The kernel is integrable in `u` on `(0, ∞)` for every `v > 0`. -/
theorem integrableOn_logKernel {v : ℝ} (hv : 0 < v) : IntegrableOn (logKernel v) (Ioi 0)

/-- `e^{−v}|log v|` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_abs_log :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * |Real.log v|) (Ioi 0)

/-- ★★★ **Euler's constant as a renormalised integral**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u))/u du = −γ`. -/
theorem integral_renormalised_exp_inv :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u =
      -Real.eulerMascheroniConstant

```

Mathlib pin v4.33.1 also has `Real.Gamma_mul_Gamma_add_half (s : ℝ) : Gamma s * Gamma (s + 1/2) = Gamma (2*s) * 2^(1-2*s) * √π` (Legendre duplication, real and complex), `Complex.differentiableAt_Gamma`, `Complex.deriv_Gamma_add_one`, `hasSum_zeta_two`; no polygamma, no `Γ'(1) = −γ` as such (DCXI has `∫₀^∞ e^{−v} log v dv = −γ` through Mathlib's `Real.eulerMascheroniConstant` API — see the signatures above for what exactly).

## State of the note (pinned to grammar 6681a8e)
Formal: §2 DLN flat prior at every depth; Gaussian DLN: depth-two two-term expansion, Bessel closed form and `e^zK₀` corollary; the crossing corollary; all-depth conditional reduction; at every depth the leading, second AND third logarithmic coefficients (the third by the recursion in `J`, `R₀`, `C₃`); the depth-three constant as an integral-defined limit with a rate. §3 cone: exact Leray closed form; the averaged posterior of `u₁²` with its first correction `1/√π` and an `O(1/N)` remainder, both sides four-dimensional. §4 blow-up: tie formulas, Laurent data, two-term Laplace expansion, monomial constant, family theorem with log-free remainder, the observable numerators `x²`, `y²`. §5 rank-one: normal integral and tilt at aligned and general orbit points, invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): the exact `J = R₀²/2 + π²/48` and `Q = (c² + 5π²/6)/(4s)` (hence `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)` and the closed form of all `C_L`); the constant terms for `L ≥ 4`; `H₃`, `ζ(3)`; the naive Bayes envelope `M_±(λ)` facewise integrability and the joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the cone's exact `1/N` coefficient `−(5/6 − √3/π)`; the blow-up higher poles (`α₁ = √(π/2)/16`), the posterior expectations `E[x²] ∼ √(2π)/(√N log N)`, `E[y²] ∼ 4/log N` as ratios; the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; an abstract Mellin transfer theorem.

## Questions
1. Fidelity check (brief) of DCXXXII–DCXXXVI against the note's claims and your round-11 specifications; in particular (a) `ThreeTermData`'s error shape `D(1+ℓ)^m/√t` with leading degree `m+3` and the base at depth four (does the recursion with `C₃ = depthThreeConst` and the quantitative base give exactly the note's `P_{L−1}` coefficient of `(log N)^{L−3}` — we verified the Mellin jet numerically; please derive it once more independently: `C_L = [D_L² + ψ'(½) + Lψ'(1)]·H(0)/(2(L−3)!)·2^{(1−L)/2}π^{−L/2}` with `H(0) = √π`); (b) DCXXXIII's envelope and the statement `cone_averaged_remainder_bound`; (c) DCXXXII's limits and the normalisation (raw prior, so `E[x²] = X_N/Z_N` with `Z_N ∼ √(π/2)(log N + …)/√N`).
2. Rank the next three day-sized formal targets by value-per-effort (concrete Lean statements + routes). Candidates: (a) the exact `J = R₀²/2 + π²/48`: with `Real.Gamma_mul_Gamma_add_half` and DCVIII's complex `Γ''(½)` machinery (`hasDerivAt_deriv_Gamma_of_re_pos`, `deriv_deriv_Gamma_one_half`), give the cleanest route to `Γ''(1) = γ² + π²/6` (differentiate the duplication product twice at `½`? we need `Γ'(½) = −√π(γ + 2 log 2)` and `Γ'(1) = −γ` in the complex/deriv API — say which of these DCVIII/DCXI already provide from the signatures, and what is missing), and then the passage from `Γ''(1)` to `J` (the renormalised Mellin transform `∫₀^∞ h(x)x^{z−1}dx = (2^{z/2}Γ(1+z/2) − 1)/z` and its derivative at `0`: differentiation under the integral at a removable singularity — or the substitution `y = x²/2` giving `J = (log 2/4)(log 2 − γ) + K/4` with `K = ∫₀^∞ (e^{−y} − 1_{(0,1/2]}) log y/y dy = (Γ''(1) − (log 2)²)/2`, and `K` as the derivative at `s = 0` of `Γ(s) − b^s/s`, i.e. of `(Γ(1+s) − b^s)/s` — which is a Taylor statement about `Γ(1+s)` to second order plus differentiation under the integral for `∫(e^{−y} − 1_{(0,b]})y^{s−1}dy` near `s = 0`; which formulation is cheapest?); (b) the blow-up posterior expectations as ratios: `E[y²] = Y_N/Z_N ∼ 4/log N` with an explicit remainder from `blowupLaplace_two_term_bound` and a rate for `√N Y_N → 2√(2π)` — is a rate `|√N Y_N − 2√(2π)| ≤ C(1+log N)/√N` (or `C/√N`) day-sized from the scaled form, and similarly for `X_N` (rate `O(N^{−1/4})`)?; (c) the cone's exact `1/N` coefficient `−(5/6 − √3/π)`: give the reduced 1D/2D integral and say whether it is day-sized given `∫ (a+G)₊`-type Fubini machinery of DCXXIX; (d) the constant terms for `L ≥ 4` (needs `∫h log²x/x` and a `FourTermData`? or is the next natural closure the identification of `C₃`, i.e. (a)+`Q`); (e) the NB face certificate as a generic power/log integrability lemma; (f) the exact `Q` via the Mellin factorisation you described (which pieces are day-sized: the Mellin transform of `Z_2(v²)` as a Beta integral, the pole subtraction, the expansion). Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the five new files (`ThreeTermData`'s `m` = leading degree `m+3`, depth `m+4`; `thirdCoeff m = C_{m+4}`; `gaussCoeffA/B` indexing; the base's input shape `8(1+ℓ)/t` vs the engine's `D(1+ℓ)^m/√t`; `coneLipEnvelope` constants; `blowupX/Y` with the raw prior).
Answer concisely with Lean-facing detail.
