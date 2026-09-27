You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main f3f2b18, 1007 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-22 headline target is DONE (DCLXXI): the depth-three residual mass as a cubic Gamma jet, by route B (l'Hôpital twice + the slope limit, DCXLIII one order up), with `c₁ = 4 log 2 − 2γ`, `c₂ = (c₁² + π²)/2` closed and `c₃` explicit in `log 2, γ, π²` and the two third-derivative symbols `Γ⁽³⁾(½)`, `Γ⁽³⁾(1)` (defined as real parts of the complex third derivatives, which exist by analyticity), and `Q₃ = c₃/(4π)` (`residualMass_three_eq_jet`, `depthFourQint_eq_jet`) by uniqueness of limits against DCLXX's finite part. I did NOT use the duplication trick (both symbols remain). NUMERICS (`gauss_depth3_cubic_jet_check.py`): the formal `c₃` expression = Taylor coefficient of `H₃` = your ζ-form `t³/6 + tπ²/2 + (4/3)ζ(3)` = 10.294202078 to 12 digits; `Γ⁽³⁾(1) = −γ³ − γπ²/2 − 2ζ(3)`, `Γ⁽³⁾(½) = √π[−p³ − (3π²/2)p − 14ζ(3)]` (`p = γ + 2 log 2`) to 12 digits; `Q₃ = 0.8191865730`.

## HEADLINES row DCLXXI
| **DCLXXI** | ★★★ **THE DEPTH-THREE RESIDUAL MASS AS A CUBIC GAMMA JET (u1007; Astra round 22)**: `hasDerivAt_deriv_deriv_Gamma_of_re_pos` (third derivative of `Γ` from analyticity); symbols `gammaThirdOne = (Γ⁽³⁾(1)).re`, `gammaThirdHalf = (Γ⁽³⁾(½)).re`; the complex jet `cubicH w = 2^{2w}Γ(½−w)Γ(1+w)³` with explicit `cubicH'`, `cubicH''` and the third derivative (`hasDerivAt_cubicH/cubicH'/cubicH''`, product rule to third order, 14 terms); values `cubicH_zero/'_zero/''_zero` (`c₁ = 4 log 2 − 2γ`, `c₂ = (c₁² + π²)/2` from `Γ', Γ''` at `½`, `1`), `hasDerivAt_cubicH''_zero'` (`↑a + ↑(3√π)·Γ⁽³⁾(1) − Γ⁽³⁾(½)`); the real jet `gammaJetH = (cubicH u).re/√π` and ★★ `tendsto_gammaJetH_third : (H(u) − 1 − c₁u − c₂u²)/u³ → c₃` (l'Hôpital twice + `tendsto_slope_zero_right`, DCXLIII one order up), `c₃ = depthThreeJetCubic` explicit in `log 2, γ, π², Γ⁽³⁾(½), Γ⁽³⁾(1)`; `depthThreePoles_sum_eq` (`P₃`'s pole sum at `z = 1−2u` is `(1 + c₁u + c₂u²)/(4πu³)` — `c₁, c₂` reproduce `B₃, C₃`), `depthThreeClosed_eq` (`M₃(1−2u) = H(u)/(4πu³)`); ★★★ `residualMass_three_eq_jet : Q₃ = c₃/(4π)` (uniqueness of limits with DCLXX's finite part), ★★★ `depthFourQint_eq_jet`. With `Γ⁽³⁾(1) = −γ³ − γπ²/2 − 2ζ(3)` and `Γ⁽³⁾(½) = √π[−(γ+2log2)³ − (3π²/2)(γ+2log2) − 14ζ(3)]` (derivations) this is `Q₃ = [t³/6 + tπ²/2 + (4/3)ζ(3)]/(4π)`, `t = 4 log 2 − 2γ`, and `D₄` closes. | DepthThreeCubicJet.lean |

## Public statements of DCLXXI
```lean
theorem hasDerivAt_deriv_deriv_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv (deriv Complex.Gamma)) (deriv (deriv (deriv Complex.Gamma)) z) z

/-- `Γ'''(1)` (real part of the complex third derivative). -/
noncomputable def gammaThirdOne : ℝ := (deriv (deriv (deriv Complex.Gamma)) 1).re

/-- `Γ'''(½)` (real part of the complex third derivative). -/
noncomputable def gammaThirdHalf : ℝ := (deriv (deriv (deriv Complex.Gamma)) (1 / 2)).re

/-! ### The jet function and its first two derivatives -/

/-- `H(w) = 2^{2w} Γ(½ − w) Γ(1 + w)³` (without the `1/√π`). -/
noncomputable def cubicH (w : ℂ) : ℂ

/-- `H'(w)` by the product rule. -/
noncomputable def cubicH' (w : ℂ) : ℂ

/-- `H''(w)` by the product rule. -/
noncomputable def cubicH'' (w : ℂ) : ℂ

theorem hasDerivAt_two_cpow_two_mul (w : ℂ) :
    HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (2 * w)) ((2 : ℂ) ^ (2 * w) * (2 * Complex.log 2)) w

theorem hasDerivAt_cB {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => Complex.Gamma (1 / 2 - w)) (-deriv Complex.Gamma (1 / 2 - w)) w

theorem hasDerivAt_cB' {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => -deriv Complex.Gamma (1 / 2 - w))
      (deriv (deriv Complex.Gamma) (1 / 2 - w)) w

theorem hasDerivAt_cB'' {w : ℂ} (hw2 : w.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (1 / 2 - w))
      (-deriv (deriv (deriv Complex.Gamma)) (1 / 2 - w)) w

theorem hasDerivAt_cC {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => Complex.Gamma (1 + w)) (deriv Complex.Gamma (1 + w)) w

theorem hasDerivAt_cC' {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => deriv Complex.Gamma (1 + w)) (deriv (deriv Complex.Gamma) (1 + w)) w

theorem hasDerivAt_cC'' {w : ℂ} (hw1 : -1 < w.re) :
    HasDerivAt (fun w : ℂ => deriv (deriv Complex.Gamma) (1 + w))
      (deriv (deriv (deriv Complex.Gamma)) (1 + w)) w

/-- `H` is differentiable with derivative `cubicH'`. -/
theorem hasDerivAt_cubicH : HasDerivAt cubicH (cubicH' w) w

/-- `H'` is differentiable with derivative `cubicH''`. -/
theorem hasDerivAt_cubicH' : HasDerivAt cubicH' (cubicH'' w) w

/-- `H''` is differentiable; its derivative at `w` (used only at `w = 0`). -/
theorem hasDerivAt_cubicH'' : HasDerivAt cubicH''
    ((2 * Complex.log 2) ^ 3 * (2 : ℂ) ^ (2 * w) * Complex.Gamma (1 / 2 - w) *
        Complex.Gamma (1 + w) ^ 3 +
      3 * (2 * Complex.log 2) ^ 2 * … (14-term third derivative omitted)

theorem cubicH_zero : cubicH 0 = ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- `c₁ = 4 log 2 − 2γ`. -/
noncomputable def depthThreeJetLinear : ℝ := 4 * Real.log 2 - 2 * Real.eulerMascheroniConstant

/-- `c₂ = (c₁² + π²)/2`. -/
noncomputable def depthThreeJetQuadratic : ℝ := (depthThreeJetLinear ^ 2 + Real.pi ^ 2) / 2

/-- `6c₃√π = √π[k³ + 3k²p − 9k²γ + 3k(p² + π²/2) − 18kpγ + 18kγ² + 9kq − 9γ(p² + π²/2) + 18pγ²
+ 9pq − 6γ³ − 18γq] − Γ⁽³⁾(½) + 3√π Γ⁽³⁾(1)`, `k = 2 log 2`, `p = γ + 2 log 2`, `q = γ² + π²/6`. -/
noncomputable def depthThreeJetCubic : ℝ

theorem cubicH'_zero : cubicH' 0 = ((Real.sqrt Real.pi * depthThreeJetLinear : ℝ) : ℂ)

theorem cubicH''_zero :
    cubicH'' 0 = ((Real.sqrt Real.pi * (2 * depthThreeJetQuadratic) : ℝ) : ℂ)

/-- The third derivative at `0` in the form `↑a + ↑b · Γ⁽³⁾(1) + ↑c · Γ⁽³⁾(½)`. -/
theorem hasDerivAt_cubicH''_zero' :
    HasDerivAt cubicH''
      (((6 * Real.sqrt Real.pi * depthThreeJetCubic + gammaThirdHalf -
          3 * Real.sqrt Real.pi * gammaThirdOne : ℝ) : ℂ) +
        ((3 * Real.sqrt Real.pi : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) 1 +
        ((-1 : ℝ) : ℂ) * deriv (deriv (deriv Complex.Gamma)) (1 / 2)) 0

/-- `H(u)/√π` as a real function of a real variable. -/
noncomputable def gammaJetH (u : ℝ) : ℝ := (cubicH u).re / Real.sqrt Real.pi

noncomputable def gammaJetH' (u : ℝ) : ℝ := (cubicH' u).re / Real.sqrt Real.pi

noncomputable def gammaJetH'' (u : ℝ) : ℝ := (cubicH'' u).re / Real.sqrt Real.pi

theorem hasDerivAt_gammaJetH {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetH (gammaJetH' u) u

theorem hasDerivAt_gammaJetH' {u : ℝ} (hu1 : -1 < u) (hu2 : u < 1 / 2) :
    HasDerivAt gammaJetH' (gammaJetH'' u) u

theorem hasDerivAt_gammaJetH''_zero : HasDerivAt gammaJetH'' (6 * depthThreeJetCubic) 0

theorem gammaJetH_zero : gammaJetH 0 = 1

theorem gammaJetH'_zero : gammaJetH' 0 = depthThreeJetLinear

theorem gammaJetH''_zero : gammaJetH'' 0 = 2 * depthThreeJetQuadratic

/-- ★★ **The cubic jet**: `(H(u) − 1 − c₁u − c₂u²)/u³ → c₃` as `u → 0⁺`. -/
theorem tendsto_gammaJetH_third :
    Tendsto (fun u : ℝ => (gammaJetH u - 1 - depthThreeJetLinear * u -
      depthThreeJetQuadratic * u ^ 2) / u ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 depthThreeJetCubic)

theorem coeff_depthThreePoly_zero' : depthThreePoly.coeff 0 = depthThreeConst

theorem coeff_depthThreePoly_one :
    depthThreePoly.coeff 1 = (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi

theorem coeff_depthThreePoly_two : depthThreePoly.coeff 2 = 1 / (4 * Real.pi)

/-- The depth-three pole sum at `z = 1 − 2u`: `1/(4πu³) + c₁/(4πu²) + c₂/(4πu)`. -/
theorem depthThreePoles_sum_eq {u : ℝ} (hu : u ≠ 0) :
    ∑ k : Fin ((enginePoly 3).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly 3).coeff k) *
      ((k : ℕ).factorial : ℝ) / (1 - (1 - 2 * u)) ^ ((k : ℕ) + 1) =
      (1 + depthThreeJetLinear * u + depthThreeJetQuadratic * u ^ 2) / (4 * Real.pi * u ^ 3)

/-- The closed Mellin form at depth three at `z = 1 − 2u` is `H(u)/(4πu³)`. -/
theorem depthThreeClosed_eq {u : ℝ} (hu0 : 0 < u) :
    ((2 : ℝ) ^ (-(1 - 2 * u) / 2)) ^ 2 * Real.Gamma ((1 - 2 * u) / 2) *
      Real.Gamma ((1 - (1 - 2 * u)) / 2) ^ (2 + 1) / (2 * Real.sqrt Real.pi ^ (2 + 1)) =
      gammaJetH u / (4 * Real.pi * u ^ 3)

/-- ★★★ **The depth-three residual mass is the cubic jet coefficient**: `Q₃ = c₃/(4π)`. -/
theorem residualMass_three_eq_jet :
    residualMass 3 (enginePoly 3) = depthThreeJetCubic / (4 * Real.pi)

/-- `Q₃ = depthFourQint` in closed form modulo `Γ⁽³⁾(½)`, `Γ⁽³⁾(1)`. -/
theorem depthFourQint_eq_jet : depthFourQint = depthThreeJetCubic / (4 * Real.pi)
```

## Questions
1. Fidelity (brief): (a) the third-derivative Leibniz expansion of `A·B·C³` (`A = 2^{2w}`, `B = Γ(½−w)`, `C = Γ(1+w)`): `S = k³b₀ + 3k²b₁ + 9k²b₀c₁ + 3kb₂ + 18kb₁c₁ + 18kb₀c₁² + 9kb₀c₂ + b₃ + 9b₂c₁ + 18b₁c₁² + 9b₁c₂ + 6b₀c₁³ + 18b₀c₁c₂ + 3b₀c₃` with `k = 2 log 2`, `b_j = B^{(j)}(0)`, `c_j = C^{(j)}(0)` — the numerics confirm, but please sanity-check the multinomial coefficients; (b) the symbolic `c₃` (docstring) and the real-part extraction `(↑a + ↑(3√π)·Γ⁽³⁾(1) + ↑(−1)·Γ⁽³⁾(½)).re`; (c) `depthThreePoles_sum_eq`'s matching `B₃ = c₁/(2π)`, `C₃ = c₂/(2π)`.
2. NEXT day-sized targets, please rank with Lean-facing interfaces: (a) ONE SYMBOL via duplication: differentiate `Γ(z)Γ(z+½) = 2^{1−2z}√π Γ(2z)` (Mathlib `Real.Gamma_mul_Gamma_add_half`/`Complex.Gamma_mul_Gamma_add_half`) three times at `z = ½` as DCXXXVIII did twice (it obtained `Γ''(1)` from `Γ''(½)`), giving `Γ⁽³⁾(½) = √π[...] + c·Γ⁽³⁾(1)`-type relation so that `c₃ = t³/6 + tπ²/2 − (2/3)λ₃`, `λ₃ = Γ⁽³⁾(1) + γ³ + γπ²/2`; what is the exact relation (with the known lower derivatives at ½ and 1), and is the third derivative of the duplication product formalisable in one day with DCXXXVIII's `hasDerivAt` chain (it used `hasDerivAt_deriv_Gamma_of_re_pos` for the second order; the third order needs `hasDerivAt_deriv_deriv_Gamma_of_re_pos`, available)?; (b) the ζ(3) IDENTIFICATION `Γ⁽³⁾(1) = −γ³ − γπ²/2 − 2ζ(3)`: what infrastructure does the pin lack (digamma/polygamma, `ψ''(1) = −2ζ(3)`; Weierstrass product; `Complex.GammaSeq` derivative convergence)? honest size; (c) `G₃ = Γ⁽³⁾(1)` (`gammaOneLogMoment 3 = gammaThirdOne`): differentiation under the integral `Γ(s) = ∫₀^∞ e^{−u}u^{s−1}` three times at `s = 1` — Mathlib has `Complex.hasDerivAt_GammaIntegral` (first order, `GammaIntegral` with `log`-weight?) — is there an iterated version or a `ContDiff`/`AnalyticAt` statement for `GammaIntegral` whose derivatives are the log-moment integrals? If yes, `D₄` becomes closed modulo ONE symbol `λ₃` (`D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]` with `J₂` in `G₃`), and with (b) fully closed; (d) the general Laurent recurrence for `H_L` (`n h_n = Σ_j j b_j h_{n−j}`, `b_n = (2^n − 1 + L(−1)^n)ζ(n)/n`) as a DEFINITION-level object plus the theorem that the engine's coefficients satisfy `a_k = 2C_L h_{L−1−k}/k!` — the formal content being only the finite-part matching (already available) — is this a useful "closed-form modulo the log-Gamma series" packaging?; (e) the naive-Bayes surrogate posterior ratio; (f) cone `c₃`; (g) the blow-up `N^{−3/2} log N` coefficient.
3. Convention hazards in DCLXXI (symbols as real parts of complex derivatives; `H₃` without the `1/√π` inside `cubicH`; the `Fin (natDegree + 1)` pole sum).
Answer concisely with Lean-facing detail.
