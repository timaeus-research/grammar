You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 774d930 + the assembly unit DCXLV landing now, 981 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-13 programme is COMPLETE: (1) the cone's second coefficient EXACT, `c₂ = −5/6 + √3/π`, by your reflection identity + `m(a) = a b(a) + 2γ(a)` + three Gaussian integrations by parts (DCXL, DCXLI); (2) the Mellin residual bridge (DCXLII); (3) the regularised Gamma jet (DCXLIII, parametrised by `u = ε/2`: `F(u) = 2^uΓ(½−u)Γ(1+u)²/√π`, `F''(0) = c² + 5π²/6`); the Mellin evaluation `M(z) = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` by the Gamma representation `(1+u²)^{−1/2} = π^{−1/2}∫w^{−1/2}e^{−(1+u²)w}` and Tonelli — no Beta-function API (DCXLIV); and the assembly `Q = (c² + 5π²/6)/(4s)`, `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)` (DCXLV). So `√N Z₃ = ℓ²/(4π) + (2log2−γ)ℓ/π + ((4log2−2γ)²+π²)/(4π) + O(ℓ/√N)` is a theorem and, through DCXXXVI's recursion with exact `J`, `R₀`, `C₃`, the third logarithmic coefficient `C_L` of the Gaussian DLN is explicit at every depth.

## HEADLINES rows DCXL–DCXLV
| **DCXL** | ★★★ **THE CONE: THE SYMMETRIC FORM OF THE SECOND COEFFICIENT `c₂ = −½∫(a² + 1 − m(a)²)γ`, `m(a) = E_a|T|` (u975; examples_slop §3; Astra round-13 target 1, first half)**: `coneTilt_zero` (simp), `integral_mul_exp_neg_half_sq_eq_zero`, `integrable_mul_exp_neg_half_sq`, `integral_sq_gaussTilt` (`∫ t² w_{0,a} = (a²+1)√(2π)e^{a²/2}`), the reflections `t ↦ −t`, `a ↦ −a`: `posPart_coneTilt_neg`, `posSq_coneTilt_neg`, `abs_gaussTilt_neg`, `mass_coneTilt_neg` (`integral_neg_eq_self`), `integrable_negPart_coneTilt`, `integrable_negSq_coneTilt`, `posPart_add_negPart_coneTilt` (`P₀(a) + P₀(−a) = M₁`, via `max_zero_add_max_neg_zero_eq_abs_self`), `posSq_add_negSq_coneTilt` (`Q₁(a) + Q₁(−a) = ∫ t² w`); `coneAbsMean`, ★★ `coneCorrectionDeriv_add_neg` (`G(a) + G(−a) = −(a² + 1 − m(a)²)`), `gaussDensity_neg`, `integrable_coneCorrectionDeriv_neg`, ★★★ `coneSecondCoeff_eq_symmetric`. Astra round 13 (`tide-log/gpt6_examples_round13_v1.md`): fidelity of DCXXXVIII–DCXXXIX confirmed (one constant-name correction `c = 3 log 2 − γ` in the DCXXXVIII row, applied); the exact value `−5/6 + √3/π` via `m(a) = a b(a) + 2γ(a)`, `b = 2∫₀^a γ`, and three Gaussian integrations by parts (`∫b²γ = ⅓`, `∫abγ² = ∫γ³`, `∫a²b²γ = ∫b²γ + 4∫abγ²`, `∫γ³ = 1/(2π√3)`) is the second half. | ConeSecondCoefficientSymmetric.lean |
| **DCXLI** | ★★★ **THE CONE: THE EXACT SECOND COEFFICIENT `c₂ = −5/6 + √3/π = −0.28200`, SO `E_a[Z_N[u₁²;a]/Z_N[1;a]] = ½ + 1/(√π√N) + (−5/6 + √3/π)/N + O(N^{−3/2})` (u976–977; examples_slop §3; Astra round-13 target 1, second half)**: `GaussianAbsMean.lean` — `hasDerivAt_gaussDensity` (`γ' = −uγ`), `gaussDensity_le_one`, `tendsto_gaussDensity_atTop/atBot`, the half masses `integral_gaussDensity_Ioi/Iic` (`½`, via `integral_gaussian_Ioi` and `integral_comp_neg_Iic`), `integral_gaussDensity` (`= 1`); `coneB a = 2∫₀^a γ` with `hasDerivAt_coneB` (`b' = 2γ`), `abs_coneB_le` (`|b| ≤ 1`), `tendsto_coneB_atTop/atBot` (`±1`, `intervalIntegral_tendsto_integral_Ioi/Iic`); `coneAbsMean_eq_integral` (`m(a) = ∫|t|γ(t−a)`), the antiderivative `absMeanPrim a t = −γ(t−a) + a∫₀^{t−a}γ` of `tγ(t−a)` (`hasDerivAt_absMeanPrim`, limits `±a/2`, `absMeanPrim_zero = −γ(a) − ab(a)/2`), ★★ `coneAbsMean_eq` (`m(a) = a b(a) + 2γ(a)` by `integral_Ioi_of_hasDerivAt_of_tendsto` + `integral_Iic_of_hasDerivAt_of_tendsto`). `ConeSecondCoefficientExact.lean` — `integrable_mul_of_bounded` (`Integrable.bdd_mul` wrapper), the integrability of every piece, the three whole-line integrations by parts (`integral_mul_deriv_eq_deriv_mul_of_integrable`, `integral_of_hasDerivAt_of_tendsto`): `integral_coneB_sq_mul_gaussDensity` (`∫b²γ = ⅓`), `integral_mul_coneB_mul_gaussDensity_sq` (`∫abγ² = ∫γ³`), `integral_sq_mul_coneB_sq_mul_gaussDensity` (`∫a²b²γ = ∫b²γ + 4∫abγ²`), `integral_gaussDensity_cube` (`∫γ³ = 1/(2π√3)`), ★★ `integral_coneAbsMean_sq` (`∫m²γ = ⅓ + 2√3/π`, i.e. `E|A+G₁||A+G₂|`), `integral_sq_mul_gaussDensity` (`= 1`), ★★★ `coneSecondCoeff_eq`. Exactly Astra's round-13 route (no polar coordinates, no Sheppard). Numerics `cone_second_coeff_check.py`: `∫m²γ = 1.43599112` both ways. Lean gotchas: `Continuous.pow/mul` produce `Pi` functions (`coneB ^ 2`) — pass `(f := fun a => …)` explicitly to bounded-multiplier lemmas; `Integrable.add` witnesses must be typed lambdas before `integral_add`; a theorem named `Integrable.foo` inside `namespace Grammar` is NOT dot-callable on `MeasureTheory.Integrable`; `tendsto_pow_atTop` needs the base type pinned. | GaussianAbsMean.lean, ConeSecondCoefficientExact.lean |
| **DCXLII** | ★★★ **THE MELLIN RESIDUAL BRIDGE FOR THE DEPTH-THREE CONSTANT: `M(z) − [2/(s(1−z)²) + c/(s(1−z))] → Q` AS `z → 1⁻`, `M(z) = ∫₀^∞ v^{z−1}Z₂(v²)dv` (u978; examples_slop §2; Astra round-13 target 2)**: `depthThreeC` (`c = 3 log 2 − γ`), `depthThreeMellin`, `depthThreePoles`; `integral_Ioi_one_rpow` (`∫₁^∞ v^{z−2} = 1/(1−z)`), `integrableOn_Ioi_one_rpow_mul_log` (`log v ≤ v^ε/ε`, `ε = (1−z)/2`), `integral_Ioi_one_rpow_mul_log` (`∫₁^∞ v^{z−2} log v = 1/(1−z)²`, antiderivative `v^{z−1}((z−1)log v − 1)/(z−1)²`, tails by `tendsto_rpow_neg_atTop` and `isLittleO_log_rpow_atTop`), `depthThree_mellin_pole_integral`; `integrableOn_rpow_mul_gaussLaplace2` (inner `Z₂ ≤ 1`, outer via `gaussLaplace2_sq_eq_depthThreeQ_add` and `integrableOn_rpow_mul_pole`), ★★ `depthThree_mellin_sub_poles` (`0 < z < 1`), `integrable_mellin_bound` (`1_{(0,1]}v^{−1/2} + |q|`), ★★★ `tendsto_depthThree_mellin_sub_poles` (dominated convergence along `𝓝[<] 1`, eventually `z ∈ (½,1)`). Remaining for the exact `Q`: the closed form `M(z) = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` (scalar reduction + Beta integral + negative Gaussian moment) and the regularised Gamma jet `B(ε) = 2^{ε/2}Γ(½−ε/2)Γ(1+ε/2)²/√π`, `M(1−ε) = 2B(ε)/(sε²)`, `B''(0) = c²/4 + 5π²/24`. Lean gotchas: `Real.rpow_sub_one` orientation (`v^(y−1) = v^y/v`); `nhdsWithin_le_nhds` needs `(s := Iio 1)` under `mono_left`; `inter_eq_right.2` membership proofs need `show (0:ℝ) < v`; `field_simp` needs `1 − z ≠ 0` supplied. | DepthThreeMellinBridge.lean |
| **DCXLIII** | ★★★ **THE REGULARISED GAMMA JET: `F(u) = 2^uΓ(½−u)Γ(1+u)²/√π`, `F(0) = 1`, `F'(0) = c`, `F''(0) = c² + 5π²/6`, `(F(u) − 1 − cu)/u² → (c² + 5π²/6)/2` AS `u → 0⁺` (u979; examples_slop §2; Astra round-13 target 3)**: `jetF`, `jetF'` (complex), `re_half_sub_pos`, `re_one_add_pos`, `hasDerivAt_two_cpow`, `hasDerivAt_jetF` (`−1 < Re w < ½`; DCVIII's `hasDerivAt_Gamma_of_re_pos` through `comp_const_sub`/`comp_const_add`), `hasDerivAt_jetF'_zero` (the product rule on the three summands with `hasDerivAt_deriv_Gamma_of_re_pos`), `Gamma_one_half_ofReal`, `jetF_zero`, `jetF'_zero` (`= c`), `hasDerivAt_jetF'_zero'` (`= c² + 5π²/6` from `Γ'(½) = −√π(γ+2log2)`, `Γ'(1) = −γ`, DCVIII's `Γ''(½)`, DCXXXVIII's `Γ''(1)`); the real `gammaJetF u = (jetF u).re`, `gammaJetF'`, `hasDerivAt_gammaJetF`, `hasDerivAt_gammaJetF'_zero` (`HasDerivAt.real_of_complex`), ★★★ `tendsto_gammaJetF_second` (`HasDerivAt.lhopital_zero_nhdsGT` with `f = F − 1 − cu`, `g = u²`, and `tendsto_slope_zero_right` for `F'`). Hand check: `T₁' + T₂' + T₃' = S[lc + c(γ+2l) + π²/2 + 2γ² − 6lγ + π²/3] = S[(3l−γ)² + 5π²/6]`; numerics (finite differences) `F'(0) = 1.50223`, `F''(0) = 10.4814` vs `c² + 5π²/6 = 10.4814`. Lean gotchas: `HasDerivAt.mul/.pow` produce `Pi` functions — bind every product with a typed `have` before `congr_deriv`; `real_of_complex` needs the point as `((0:ℝ):ℂ)` (`simpa` with `ofReal_zero`) and `Complex.ofReal_re` applied by `rw`, not `simp` (which pushes casts inside); a def named `depthThreeF` already existed (DCXXXI) — `gammaJetF`. | DepthThreeGammaJet.lean |
| **DCXLIV** | ★★★ **THE MELLIN TRANSFORM OF THE DEPTH-TWO GAUSSIAN DLN IN CLOSED FORM: `M(z) = ∫₀^∞ v^{z−1}Z₂(v²)dv = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` FOR `0 < z < 1` (u980; examples_slop §2; Astra round-13, the Mellin evaluation)**: `integral_rpow_mul_exp_neg_mul_sq'` (`∫₀^∞ u^{z−1}e^{−wu²} = w^{−z/2}Γ(z/2)/2`), `integral_rpow_mul_exp_neg_mul'` (`∫₀^∞ w^{a−1}e^{−bw} = b^{−a}Γ(a)`), `inv_sqrt_one_add_eq_integral` (`(1+t)^{−1/2} = π^{−1/2}∫₀^∞ w^{−1/2}e^{−(1+t)w}`); `mellinHalfBeta` (`A(z) = ∫₀^∞ u^{z−1}(1+u²)^{−1/2}`), `integrable_halfBeta_prod`, ★★ `mellinHalfBeta_eq` (`A = Γ(z/2)Γ((1−z)/2)/(2√π)` by Tonelli — no Beta-function API); `gaussDensity_abs`, `integral_abs_rpow_neg_mul_gaussDensity` (`∫|g|^{−z}γ = 2^{−z/2}Γ((1−z)/2)/√π`, via `integral_comp_abs`); `integral_rpow_div_sqrt_one_add_mul_sq` (`∫₀^∞ v^{z−1}(1+v²g²)^{−1/2} = |g|^{−z}A(z)`, `u = |g|v`), `integrable_mellin_prod` (the `v`-marginal of the norm is `v^{z−1}Z₂(v²)`, integrable by DCXLII, so `integrable_prod_iff` needs no negative-moment integrability), ★★★ `depthThreeMellin_eq` (scalar reduction DCXIX + Tonelli + a.e. substitution `g ≠ 0`). Numerics `gauss_mellin_bridge_check.py`: closed form vs quadrature to 1e−9. Lean gotchas: `integral_comp_mul_left_Ioi` is `∫ g(b x) = b⁻¹ • ∫ g` (fold `b⁻¹ = b^{−1}` by `rpow_neg`); `ae_iff` + `Set.ofPred_eq_eq_singleton` + `measure_singleton` for `∀ᵐ g, g ≠ 0`; `rw [show 1 = √1]` rewrites every `1` (use `Real.one_le_sqrt`); `rw [← hpi]` rewrites `π` under `√π` (use `Real.sq_sqrt` on the goal). | DepthThreeMellinClosedForm.lean |
| **DCXLV** | ★★★ **THE DEPTH-THREE CONSTANT OF THE GAUSSIAN DLN IN CLOSED FORM: `Q = (c² + 5π²/6)/(4√(2π))` AND `C₃ = ((4 log 2 − 2γ)² + π²)/(4π) = 0.99377`, SO `√N Z₃ = (log N)²/(4π) + (2 log 2 − γ)(log N)/π + ((4 log 2 − 2γ)² + π²)/(4π) + O(log N/√N)` (u981; examples_slop §2 eq. dln_gauss at `L = 3`; Astra round-13 assembly)**: `jetF_ofReal`, `gammaJetF_eq` (`F(u) = 2^uΓ(½−u)Γ(1+u)²/√π` as a real closed form via `Complex.Gamma_ofReal`, `Complex.ofReal_cpow`), `depthThreeMellin_sub_poles_eq` (`M(1−2u) − poles(1−2u) = (F(u) − 1 − cu)/(2su²)` for `0 < u < ½`; `Γ(u) = Γ(1+u)/u`, `2^{−1−(1−2u)/2} = 2^u/(2√2)`), `tendsto_one_sub_two_mul_nhdsLT`, ★★★ `depthThreeQint_eq` (uniqueness of limits between DCXLII's bridge composed with `z = 1 − 2u` and DCXLIII's jet divided by `2s`), ★★★ `depthThreeConst_eq` (with DCXXXVIII's exact `J`). Numerics: `gauss_depth3_residual_check.py` (`C₃ = 0.99377`, residual `0.9936` at `N = 10⁴`), `gauss_mellin_bridge_check.py` (`Q = 1.0453637088`). With DCXXXVI's recursion the third logarithmic coefficient `C_L` is now explicit at every depth. Lean gotchas: never `rw [← hsq]` with `hsq : √π·√π = π` (it rewrites `π` under `√π`) — fold the radical into an atom by `set`, `clear_value`, then rewrite the bare `π` as `P²`; `\bdepthThreeF\b` does not match inside `tendsto_depthThreeF_second` (word boundary at `_`) — the DCXLIII identifiers are now uniformly `gammaJetF…`. | DepthThreeConstExact.lean |

## Public statements of the six new files (docstrings + signatures, proofs omitted)
### Grammar/ConeSecondCoefficientSymmetric.lean
```lean
theorem coneTilt_zero (a t : ℝ) : coneTilt 0 a t = Real.exp (-t ^ 2 / 2 + a * t)

/-- `∫ u e^{−u²/2} du = 0` (odd integrand). -/
theorem integral_mul_exp_neg_half_sq_eq_zero : ∫ u : ℝ, u * Real.exp (-u ^ 2 / 2) = 0

theorem integrable_mul_exp_neg_half_sq : Integrable (fun u : ℝ => u * Real.exp (-u ^ 2 / 2))

/-- `∫ t² e^{−t²/2 + at} dt = (a² + 1) √(2π) e^{a²/2}`. -/
theorem integral_sq_gaussTilt (a : ℝ) :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t) =
      (a ^ 2 + 1) * Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2)

theorem posPart_coneTilt_neg (a : ℝ) :
    ∫ t, max t 0 * coneTilt 0 (-a) t = ∫ t, max (-t) 0 * coneTilt 0 a t

theorem posSq_coneTilt_neg (a : ℝ) :
    ∫ t, max t 0 * |t| * coneTilt 0 (-a) t = ∫ t, max (-t) 0 * |t| * coneTilt 0 a t

theorem abs_gaussTilt_neg (a : ℝ) :
    ∫ t, |t| * Real.exp (-t ^ 2 / 2 + -a * t) = ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)

theorem mass_coneTilt_neg (a : ℝ) : ∫ t, coneTilt 0 (-a) t = ∫ t, coneTilt 0 a t

theorem integrable_negPart_coneTilt (a : ℝ) :
    Integrable (fun t : ℝ => max (-t) 0 * coneTilt 0 a t)

theorem integrable_negSq_coneTilt (a : ℝ) :
    Integrable (fun t : ℝ => max (-t) 0 * |t| * coneTilt 0 a t)

/-- `P₀(a) + P₀(−a) = M₁(a)`. -/
theorem posPart_add_negPart_coneTilt (a : ℝ) :
    (∫ t, max t 0 * coneTilt 0 a t) + ∫ t, max (-t) 0 * coneTilt 0 a t =
      ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)

/-- `Q₁(a) + Q₁(−a) = ∫ t² w_{0,a}`. -/
theorem posSq_add_negSq_coneTilt (a : ℝ) :
    (∫ t, max t 0 * |t| * coneTilt 0 a t) + ∫ t, max (-t) 0 * |t| * coneTilt 0 a t =
      ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)

/-- `m(a) = E_a|T| = ∫ |t| w_{0,a} / ∫ w_{0,a}`. -/
noncomputable def coneAbsMean (a : ℝ) : ℝ

/-- ★★ **The reflection identity** `G(a) + G(−a) = −(a² + 1 − m(a)²)`. -/
theorem coneCorrectionDeriv_add_neg (a : ℝ) :
    coneCorrectionDeriv a + coneCorrectionDeriv (-a) = -(a ^ 2 + 1 - coneAbsMean a ^ 2)

theorem gaussDensity_neg (a : ℝ) : gaussDensity (-a) = gaussDensity a

theorem integrable_coneCorrectionDeriv_neg :
    Integrable (fun a : ℝ => coneCorrectionDeriv (-a) * gaussDensity a)

/-- ★★★ **The symmetric form**: `c₂ = −½ ∫ (a² + 1 − m(a)²) γ(a) da`. -/
theorem coneSecondCoeff_eq_symmetric :
    coneSecondCoeff = -(1 / 2 : ℝ) * ∫ a, (a ^ 2 + 1 - coneAbsMean a ^ 2) * gaussDensity a
```

### Grammar/GaussianAbsMean.lean
```lean
theorem of calculus on `(−∞, 0]` and `[0, ∞)` with the antiderivative
`F(t) = −γ(t − a) + a ∫₀^{t−a} γ` of `t γ(t − a)`:

  `m(a) = a b(a) + 2 γ(a)`   (★★ `coneAbsMean_eq`).

Used by the exact value of the cone's second coefficient (examples_slop §3; Astra round-13
target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The Gaussian density: derivative, tails, half masses -/

theorem hasDerivAt_gaussDensity (u : ℝ) :
    HasDerivAt gaussDensity (-u * gaussDensity u) u

theorem gaussDensity_le_one (u : ℝ) : gaussDensity u ≤ 1

theorem tendsto_gaussDensity_atTop : Tendsto gaussDensity atTop (𝓝 0)

theorem tendsto_gaussDensity_atBot : Tendsto gaussDensity atBot (𝓝 0)

theorem integral_gaussDensity_Ioi : ∫ t in Ioi (0 : ℝ), gaussDensity t = 1 / 2

theorem integral_gaussDensity_Iic : ∫ t in Iic (0 : ℝ), gaussDensity t = 1 / 2

theorem integral_gaussDensity : ∫ t, gaussDensity t = 1

/-- `b(a) = 2∫₀^a γ = 2Φ(a) − 1`. -/
noncomputable def coneB (a : ℝ) : ℝ := 2 * ∫ t in (0 : ℝ)..a, gaussDensity t

theorem hasDerivAt_intervalIntegral_gaussDensity (a : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) (gaussDensity a) a

theorem hasDerivAt_coneB (a : ℝ) : HasDerivAt coneB (2 * gaussDensity a) a

theorem continuous_coneB : Continuous coneB

/-- `|∫₀^a γ| ≤ ½`. -/
theorem abs_intervalIntegral_gaussDensity_le (a : ℝ) :
    |∫ t in (0 : ℝ)..a, gaussDensity t| ≤ 1 / 2

theorem abs_coneB_le (a : ℝ) : |coneB a| ≤ 1

theorem tendsto_intervalIntegral_gaussDensity_atTop :
    Tendsto (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) atTop (𝓝 (1 / 2))

theorem tendsto_intervalIntegral_gaussDensity_atBot :
    Tendsto (fun u => ∫ t in (0 : ℝ)..u, gaussDensity t) atBot (𝓝 (-(1 / 2)))

theorem tendsto_coneB_atTop : Tendsto coneB atTop (𝓝 1)

theorem tendsto_coneB_atBot : Tendsto coneB atBot (𝓝 (-1))

/-- `m(a) = ∫ |t| γ(t − a) dt`. -/
theorem coneAbsMean_eq_integral (a : ℝ) :
    coneAbsMean a = ∫ t, |t| * gaussDensity (t - a)

/-- The antiderivative `F(t) = −γ(t − a) + a ∫₀^{t−a} γ` of `t γ(t − a)`. -/
noncomputable def absMeanPrim (a t : ℝ) : ℝ

theorem hasDerivAt_absMeanPrim (a t : ℝ) :
    HasDerivAt (absMeanPrim a) (t * gaussDensity (t - a)) t

theorem tendsto_absMeanPrim_atTop (a : ℝ) :
    Tendsto (absMeanPrim a) atTop (𝓝 (a * (1 / 2)))

theorem tendsto_absMeanPrim_atBot (a : ℝ) :
    Tendsto (absMeanPrim a) atBot (𝓝 (a * (-(1 / 2))))

/-- `F(0) = −γ(a) − a b(a)/2`. -/
theorem absMeanPrim_zero (a : ℝ) : absMeanPrim a 0 = -gaussDensity a - a * (coneB a / 2)

theorem integrable_abs_mul_gaussDensity_sub (a : ℝ) :
    Integrable (fun t : ℝ => |t| * gaussDensity (t - a))

/-- ★★ **The absolute mean**: `m(a) = a b(a) + 2 γ(a)`. -/
theorem coneAbsMean_eq (a : ℝ) : coneAbsMean a = a * coneB a + 2 * gaussDensity a
```

### Grammar/ConeSecondCoefficientExact.lean
```lean
theorem integrable_sq_mul_gaussDensity : Integrable (fun a : ℝ => a ^ 2 * gaussDensity a)

theorem integrable_mul_gaussDensity : Integrable (fun a : ℝ => a * gaussDensity a)

/-- Multiplying an integrable function by a bounded continuous one keeps it integrable. -/
theorem integrable_mul_of_bounded {g f : ℝ → ℝ} (hg : Integrable g) (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable (fun x => f x * g x)

theorem abs_coneB_sq_le (a : ℝ) : |coneB a ^ 2| ≤ 1

theorem integrable_coneB_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => coneB a ^ 2 * gaussDensity a)

theorem integrable_gaussDensity_sq : Integrable (fun a : ℝ => gaussDensity a ^ 2)

theorem integrable_mul_coneB_mul_gaussDensity_sq :
    Integrable (fun a : ℝ => a * coneB a * gaussDensity a ^ 2)

theorem integrable_gaussDensity_cube : Integrable (fun a : ℝ => gaussDensity a ^ 3)

theorem integrable_sq_mul_coneB_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => a ^ 2 * coneB a ^ 2 * gaussDensity a)

/-- `B = ∫ b² γ = ⅓`. -/
theorem integral_coneB_sq_mul_gaussDensity : ∫ a, coneB a ^ 2 * gaussDensity a = 1 / 3

/-- `I = ∫ a b γ² = ∫ γ³`. -/
theorem integral_mul_coneB_mul_gaussDensity_sq :
    ∫ a, a * coneB a * gaussDensity a ^ 2 = ∫ a, gaussDensity a ^ 3

/-- `∫ a² b² γ = ∫ b² γ + 4 ∫ a b γ²`. -/
theorem integral_sq_mul_coneB_sq_mul_gaussDensity :
    ∫ a, a ^ 2 * coneB a ^ 2 * gaussDensity a =
      (∫ a, coneB a ^ 2 * gaussDensity a) + 4 * ∫ a, a * coneB a * gaussDensity a ^ 2

/-- `H = ∫ γ³ = 1/(2π√3)`. -/
theorem integral_gaussDensity_cube : ∫ a, gaussDensity a ^ 3 = 1 / (2 * Real.pi * Real.sqrt 3)

theorem integrable_coneAbsMean_sq_mul_gaussDensity :
    Integrable (fun a : ℝ => coneAbsMean a ^ 2 * gaussDensity a)

/-- ★★ `∫ m(a)² γ(a) da = ⅓ + 2√3/π`. -/
theorem integral_coneAbsMean_sq :
    ∫ a, coneAbsMean a ^ 2 * gaussDensity a = 1 / 3 + 2 * Real.sqrt 3 / Real.pi

theorem integral_sq_mul_gaussDensity : ∫ a, a ^ 2 * gaussDensity a = 1

/-- ★★★ **The exact second coefficient of the averaged cone posterior**: `c₂ = −5/6 + √3/π`. -/
theorem coneSecondCoeff_eq : coneSecondCoeff = -(5 / 6 : ℝ) + Real.sqrt 3 / Real.pi
```

### Grammar/DepthThreeMellinBridge.lean
```lean
/-- `c = 3 log 2 − γ`. -/
noncomputable def depthThreeC : ℝ := 3 * Real.log 2 - Real.eulerMascheroniConstant

/-- The Mellin transform `M(z) = ∫₀^∞ v^{z−1} Z₂(v²) dv`. -/
noncomputable def depthThreeMellin (z : ℝ) : ℝ

/-- The polar part `2/(s(1−z)²) + c/(s(1−z))`. -/
noncomputable def depthThreePoles (z : ℝ) : ℝ

/-- `∫₁^∞ v^{z−2} dv = 1/(1−z)` for `z < 1`. -/
theorem integral_Ioi_one_rpow {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) = 1 / (1 - z)

theorem integrableOn_Ioi_one_rpow {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2)) (Ioi 1)

/-- `v^{z−2} log v` is integrable on `(1,∞)` for `z < 1` (`log v ≤ v^ε/ε`, `ε = (1−z)/2`). -/
theorem integrableOn_Ioi_one_rpow_mul_log {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * Real.log v) (Ioi 1)

/-- `∫₁^∞ v^{z−2} log v dv = 1/(1−z)²` for `z < 1`. -/
theorem integral_Ioi_one_rpow_mul_log {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) * Real.log v = 1 / (1 - z) ^ 2

/-- `∫₁^∞ v^{z−1}(2 log v + c)/(s v) dv = 2/(s(1−z)²) + c/(s(1−z))` for `z < 1`. -/
theorem depthThree_mellin_pole_integral {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 1) *
      ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v)) = depthThreePoles z

theorem integrableOn_rpow_mul_gaussLaplace2_inner {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioc 0 1)

/-- On `(1,∞)`: `Z₂(v²) = q(v) + (2 log v + c)/(s v)`. -/
theorem gaussLaplace2_sq_eq_depthThreeQ_add {v : ℝ} (hv : 1 < v) :
    gaussLaplace2 (v ^ 2) = depthThreeQ v +
      (2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v)

theorem integrableOn_rpow_mul_pole {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) *
      ((2 * Real.log v + depthThreeC) / (Real.sqrt (2 * Real.pi) * v))) (Ioi 1)

theorem integrableOn_rpow_mul_depthThreeQ {z : ℝ} (hz : z ≤ 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * depthThreeQ v) (Ioi 1)

theorem integrableOn_rpow_mul_gaussLaplace2_outer {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioi 1)

theorem integrableOn_rpow_mul_gaussLaplace2 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplace2 (v ^ 2)) (Ioi 0)

/-- ★★ **The Mellin transform minus its poles is the Mellin transform of `q`**: for `0 < z < 1`,
`M(z) − [2/(s(1−z)²) + c/(s(1−z))] = ∫₀^∞ v^{z−1} q(v) dv`. -/
theorem depthThree_mellin_sub_poles {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthThreeMellin z - depthThreePoles z =
      ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * depthThreeQ v

/-- The dominating function `1_{(0,1]}(v) v^{−1/2} + |q(v)|`. -/
theorem integrable_mellin_bound :
    IntegrableOn (fun v : ℝ => (Ioc (0 : ℝ) 1).indicator (fun v => v ^ (-(1 / 2 : ℝ))) v +
      |depthThreeQ v|) (Ioi 0)

/-- ★★★ **The residual bridge**: `M(z) − [2/(s(1−z)²) + c/(s(1−z))] → Q` as `z → 1⁻`. -/
theorem tendsto_depthThree_mellin_sub_poles :
    Tendsto (fun z => depthThreeMellin z - depthThreePoles z) (𝓝[<] (1 : ℝ))
      (𝓝 depthThreeQint)
```

### Grammar/DepthThreeGammaJet.lean
```lean
/-- `F(w) = 2^w Γ(½ − w) Γ(1 + w)² / √π`. -/
noncomputable def jetF (w : ℂ) : ℂ

/-- `F'(w)` by the product rule. -/
noncomputable def jetF' (w : ℂ) : ℂ

theorem re_half_sub_pos {w : ℂ} (hw : w.re < 1 / 2) : 0 < (1 / 2 - w).re

theorem re_one_add_pos {w : ℂ} (hw : -1 < w.re) : 0 < (1 + w).re

theorem hasDerivAt_two_cpow (w : ℂ) :
    HasDerivAt (fun w : ℂ => (2 : ℂ) ^ w) ((2 : ℂ) ^ w * Complex.log 2) w

/-- `F` is differentiable for `−1 < Re w < ½`, with derivative `jetF'`. -/
theorem hasDerivAt_jetF {w : ℂ} (hw1 : -1 < w.re) (hw2 : w.re < 1 / 2) :
    HasDerivAt jetF (jetF' w) w

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
        ((Real.sqrt Real.pi : ℝ) : ℂ)) 0

theorem Gamma_one_half_ofReal : Complex.Gamma (1 / 2) = ((Real.sqrt Real.pi : ℝ) : ℂ)

theorem jetF_zero : jetF 0 = 1

theorem jetF'_zero : jetF' 0 = ((depthThreeC : ℝ) : ℂ)

theorem hasDerivAt_jetF'_zero' :
    HasDerivAt jetF' (((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6 : ℝ) : ℂ)) 0

/-- `F(u) = 2^u Γ(½ − u) Γ(1 + u)²/√π` as a real function (the real part of `jetF`). -/
noncomputable def gammaJetF (u : ℝ) : ℝ := (jetF u).re

/-- `F'(u)` (the real part of `jetF'`). -/
noncomputable def gammaJetF' (u : ℝ) : ℝ := (jetF' u).re

theorem hasDerivAt_gammaJetF {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetF (gammaJetF' u) u

theorem hasDerivAt_gammaJetF'_zero :
    HasDerivAt gammaJetF' (depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) 0

theorem gammaJetF_zero : gammaJetF 0 = 1

theorem gammaJetF'_zero : gammaJetF' 0 = depthThreeC

/-- ★★★ **The regularised jet**: `(F(u) − 1 − c u)/u² → (c² + 5π²/6)/2` as `u → 0⁺`. -/
theorem tendsto_gammaJetF_second :
    Tendsto (fun u : ℝ => (gammaJetF u - 1 - depthThreeC * u) / u ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / 2))
```

### Grammar/DepthThreeMellinClosedForm.lean
```lean
/-- `∫₀^∞ u^{z−1} e^{−w u²} du = w^{−z/2} Γ(z/2)/2` for `z, w > 0`. -/
theorem integral_rpow_mul_exp_neg_mul_sq' {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    ∫ u in Ioi (0 : ℝ), u ^ (z - 1) * Real.exp (-w * u ^ 2) =
      w ^ (-z / 2) * (1 / 2) * Real.Gamma (z / 2)

/-- `∫₀^∞ w^{a−1} e^{−b w} dw = b^{−a} Γ(a)` for `a, b > 0`. -/
theorem integral_rpow_mul_exp_neg_mul' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ w in Ioi (0 : ℝ), w ^ (a - 1) * Real.exp (-b * w) = b ^ (-a) * Real.Gamma a

/-- The Gamma representation `(1 + t)^{−1/2} = π^{−1/2} ∫₀^∞ w^{−1/2} e^{−(1+t)w} dw` for
`t ≥ 0`. -/
theorem inv_sqrt_one_add_eq_integral {t : ℝ} (ht : 0 ≤ t) :
    1 / Real.sqrt (1 + t) =
      1 / Real.sqrt Real.pi * ∫ w in Ioi (0 : ℝ), w ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 + t) * w)

/-- `A(z) = ∫₀^∞ u^{z−1}(1 + u²)^{−1/2} du`. -/
noncomputable def mellinHalfBeta (z : ℝ) : ℝ

/-- The two-variable integrand `w^{−1/2} e^{−w} u^{z−1} e^{−w u²}` is integrable on `(0,∞)²`. -/
theorem integrable_halfBeta_prod {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry fun u w : ℝ =>
      w ^ (-(1 / 2 : ℝ)) * Real.exp (-w) * (u ^ (z - 1) * Real.exp (-w * u ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))

/-- ★★ `A(z) = Γ(z/2) Γ((1−z)/2)/(2√π)` for `0 < z < 1`. -/
theorem mellinHalfBeta_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    mellinHalfBeta z = Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) / (2 * Real.sqrt Real.pi)

theorem gaussDensity_abs (g : ℝ) : gaussDensity |g| = gaussDensity g

/-- `∫ |g|^{−z} γ(g) dg = 2^{−z/2} Γ((1−z)/2)/√π` for `z < 1`. -/
theorem integral_abs_rpow_neg_mul_gaussDensity {z : ℝ} (hz : z < 1) :
    ∫ g : ℝ, |g| ^ (-z) * gaussDensity g =
      (2 : ℝ) ^ (-z / 2) * Real.Gamma ((1 - z) / 2) / Real.sqrt Real.pi

/-- For `g ≠ 0`: `∫₀^∞ v^{z−1}(1 + v²g²)^{−1/2} dv = |g|^{−z} A(z)` (the substitution
`u = |g| v`). -/
theorem integral_rpow_div_sqrt_one_add_mul_sq {z g : ℝ} (hg : g ≠ 0) :
    ∫ v in Ioi (0 : ℝ), v ^ (z - 1) / Real.sqrt (1 + v ^ 2 * g ^ 2) =
      |g| ^ (-z) * mellinHalfBeta z

/-- The integrand `v^{z−1} γ(g)(1 + v²g²)^{−1/2}` is integrable on `(0,∞) × ℝ` for `0 < z < 1`
(the `v`-marginal of its norm is `v^{z−1} Z₂(v²)`, integrable by DCXLII). -/
theorem integrable_mellin_prod {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry fun v g : ℝ =>
      v ^ (z - 1) * (gaussDensity g / Real.sqrt (1 + v ^ 2 * g ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)

/-- ★★★ **The closed form**: `M(z) = 2^{−1−z/2} Γ(z/2) Γ((1−z)/2)² / π` for `0 < z < 1`. -/
theorem depthThreeMellin_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthThreeMellin z =
      (2 : ℝ) ^ (-1 - z / 2) * Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) ^ 2 / Real.pi
```

### Grammar/DepthThreeConstExact.lean
```lean
theorem jetF_ofReal (u : ℝ) :
    jetF u = ((2 ^ u * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ 2 / Real.sqrt Real.pi : ℝ) :
      ℂ)

theorem gammaJetF_eq (u : ℝ) :
    gammaJetF u = 2 ^ u * Real.Gamma (1 / 2 - u) * Real.Gamma (1 + u) ^ 2 / Real.sqrt Real.pi

theorem depthThreeMellin_sub_poles_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    depthThreeMellin (1 - 2 * u) - depthThreePoles (1 - 2 * u) =
      (gammaJetF u - 1 - depthThreeC * u) / (2 * Real.sqrt (2 * Real.pi) * u ^ 2)

theorem tendsto_one_sub_two_mul_nhdsLT :
    Tendsto (fun u : ℝ => 1 - 2 * u) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ))

/-- ★★★ **The depth-three residual constant**: `Q = (c² + 5π²/6)/(4√(2π))`. -/
theorem depthThreeQint_eq :
    depthThreeQint = (depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / (4 * Real.sqrt (2 * Real.pi))

/-- ★★★ **The depth-three constant in closed form**: `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)`. -/
theorem depthThreeConst_eq :
    depthThreeConst =
      ((4 * Real.log 2 - 2 * Real.eulerMascheroniConstant) ^ 2 + Real.pi ^ 2) / (4 * Real.pi)
```

## Definitions relied on
```lean
noncomputable def gaussDensity (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)
noncomputable def coneTilt (δ a t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2 + a * t - δ * |t|)
noncomputable def coneScaledCorrection (δ a : ℝ) : ℝ := (∫ t, max t 0 * coneTilt δ a t) / ∫ t, coneTilt δ a t
noncomputable def coneCorrectionDeriv (a : ℝ) : ℝ :=
  -((∫ t, max t 0 * |t| * coneTilt 0 a t) * (∫ t, coneTilt 0 a t) -
      (∫ t, max t 0 * coneTilt 0 a t) * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)) / (∫ t, coneTilt 0 a t) ^ 2
noncomputable def coneSecondCoeff : ℝ := ∫ a, coneCorrectionDeriv a * gaussDensity a
noncomputable def depthThreeQ (v : ℝ) : ℝ :=
  gaussLaplace2 (v ^ 2) - (Ioi (1 : ℝ)).indicator (fun v =>
    (2 * Real.log v + (3 * Real.log 2 - Real.eulerMascheroniConstant)) / (Real.sqrt (2 * Real.pi) * v)) v
noncomputable def depthThreeQint : ℝ := ∫ v in Ioi (0 : ℝ), depthThreeQ v
noncomputable def gaussJlog : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x / x   -- gaussH x = e^{−x²/2} − 1_{(0,1]}(x)
noncomputable def depthThreeConst : ℝ :=
  ((3 * Real.log 2 - Real.eulerMascheroniConstant) * ((Real.log 2 - Real.eulerMascheroniConstant) / 2) +
    2 * gaussJlog) / Real.pi + 2 / Real.sqrt (2 * Real.pi) * depthThreeQint
theorem gaussLaplaceL_three_rate : ... |√N Z_3 − (ℓ²/(4π) + ((2log2−γ)/π)ℓ + depthThreeConst)| ≤ 8(1+ℓ)/√N  (DCXXXIV, N ≥ 1)
thirdCoeff (DCXXXVI): C_4 = (C_3 + 2B_3R₀ + 8A_3J)/s, C_{L+1} = (C_L/(L−2) + 2B_LR₀ + 4(L−1)A_LJ)/s
```
Numerics: `c₂ = −0.282004` (both integrals; `√N(N·rem − c₂) → 0.0698`); `Q = 1.0453637088` = `(c²+5π²/6)/(4s)` to 1e−10; `M(z)` closed form vs quadrature 1e−9; `C₃ = 0.99377`, residual `0.9936` at `N = 10⁴`.

## State of the note (pinned to grammar main after DCXLV)
Formal: §2 Gaussian DLN at every depth: leading, second and third logarithmic coefficients; the depth-three constant EXACT (`C₃`), `J`, `Q`, `Γ''(1)`, the Mellin transform of `Z₂` in closed form with its residual bridge and regularised jet; depth-two two-term expansion, Bessel form, crossing corollary. §3 cone: exact Leray closed form; averaged posterior `½ + 1/(√π√N) + (−5/6 + √3/π)/N + O(N^{−3/2})` with the `1/√N` rate on the second coefficient, both sides four-dimensional. §4 blow-up: tie formulas, Laurent data, two-term Laplace expansion, monomial constant, family theorem with log-free remainder, observable numerators and posterior ratios. §5 rank-one: normal integral and tilt at aligned and general orbit points, invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): the closed form of all `C_L` (the recursion is a theorem; the Mellin-jet closed form `C_L = [D_L² + (L+3)π²/6]/(2(L−3)!s^{L−1})` is checked numerically — is the closed-form solution of the recursion day-sized as an induction?); the constant terms for `L ≥ 4`; `H₃`, `ζ(3)`; the naive Bayes envelope facewise integrability and joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the blow-up higher poles (`α₁ = √(π/2)/16`); the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; an abstract Mellin transfer theorem; the cone's third coefficient (numerically `√N(N·rem − c₂) → 0.0698`, i.e. an `N^{−3/2}` term with coefficient `≈ 0.0698`).

## Questions
1. Fidelity check (brief) of DCXL–DCXLV against the note's claims and your round-13 specifications; in particular (a) `coneCorrectionDeriv_add_neg` and the sign in `coneSecondCoeff_eq_symmetric`; (b) `coneAbsMean_eq` (`m = ab + 2γ` with `b = 2∫₀^a γ`), the three IBP identities and `∫γ³ = 1/(2π√3)`; (c) the bridge's `depthThreePoles` and the direction of the limit; (d) `gammaJetF` parametrised by `u` (not `ε`), `F''(0) = c² + 5π²/6` (= `4B''(0)`), and `depthThreeMellin_sub_poles_eq`; (e) the closed form's bookkeeping `2^{−1−z/2}` and the negative moment `2^{−z/2}Γ((1−z)/2)/√π`; (f) `depthThreeConst_eq` — please re-derive `C₃ = [(c+2R₀)² + π²]/(4π)` from `C₃ = (cR₀ + 2J)/π + (2/s)Q` with `J = R₀²/2 + π²/48`, `Q = (c²+5π²/6)/(4s)` independently.
2. Rank the next three day-sized formal targets by value-per-effort with concrete Lean statements and routes. Candidates: (a) the closed-form solution of the third-coefficient recursion: prove by induction that `thirdCoeff m` equals `[D_L² + (L+3)π²/6]/(2(L−3)!s^{L−1})` at `L = m+4`, `D_L = (L+1)log 2 − (L−1)γ`, given `A_L = 1/((L−1)!s^{L−1})`, `B_L = D_L/((L−2)!s^{L−1})` (DCXXVI), the exact `J`, `R₀`, `C₃` — is this a routine `Nat.rec` with `ring`/`field_simp` per step (state the step identity `T_{L+1} − T_L` with `T_L = (L−3)!s^{L−1}C_L`)? (b) the constant terms for `L ≥ 4`: a `FourTermData` propagation needs the fourth moment `∫h log²x/x` (weighted kernel with `log²u`, `⅓log³v`) and `Γ'''(1)` (needs `ζ(3)`: Mathlib has `Complex.Gamma` but is `Γ'''(1) = −γ³ − γπ²/2 − 2ζ(3)` available? probably not) — say what is honestly day-sized (perhaps `D₄` as an integral-defined limit with a rate, like DCXXXI/DCXXXIV at depth three?); (c) the blow-up higher pole `α₁ = √(π/2)/16` (a `1/N` correction to `Z_N` of the blow-up model: needs a second-order expansion of the reduced 1D integral in DCXV); (d) the cone's third coefficient `≈ 0.0698` as an integral-defined limit (`N^{3/2}(E_N − ½ − 1/(√π√N) − c₂/N) → c₃ = ∫ G₂ γ` with `G₂` the second `δ`-derivative — a third-order tilt expansion with `|1 − e^{−x} − x + x²/2| ≤ x³/6`); (e) the NB generic power/log face certificate; (f) an abstract Mellin transfer theorem (from `Z(N)` expansions to zeta poles) as a library lemma. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the six new files (the `u`-vs-`ε` parametrisation; `depthThreePoles` uses `depthThreeC` while `depthThreeQ` spells the constant inline; `coneB` normalisation `2∫₀^a γ`; `mellinHalfBeta` naming; `depthThreeMellin` defined only as an integral — say whether the closed form should replace it in the note's statement).
Answer concisely with Lean-facing detail.
