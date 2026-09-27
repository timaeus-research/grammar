You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 4c0cd00, 984 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-14 programme is COMPLETE: (1) the closed form of the third coefficient at every depth (DCXLVI, by induction exactly as you prescribed: `T_{L+1} − T_L = 2D_LR₀ + 4J`); (2) the abstract Mellin residual lemma `tendsto_mellin_residual` and the log-power transforms `∫₁^∞ v^{z−2}log^k v = k!/(1−z)^{k+1}` (DCXLVII; the transforms by the substitution `v = e^x` and the Gamma integral, no integration by parts; the residual lemma needs only `a < 1`, the hypothesis `0 < a` was unused and dropped); (3) the generic power/log face certificate (DCXLVIII; note the bound is `(1+|log x|)^k ≤ (1+1/ε)^k x^{−kε}` — the constant `(2/ε)^k` is FALSE for `ε > 1`, a slip in my first draft caught by Lean). The note is pinned to `4c0cd00` (§2: exact `C₃`, `Q`, `J`, the Mellin closed form, the jet, the transfer lemma, the closed-form `C_L`; §3: exact cone `c₂`; §6: the certificate).

## HEADLINES rows DCXLVI–DCXLVIII
| **DCXLVI** | ★★★ **THE THIRD LOGARITHMIC COEFFICIENT OF THE GAUSSIAN DLN IN CLOSED FORM AT EVERY DEPTH: `C_L = [D_L² + (L+3)π²/6]/(2(L−3)! √(2π)^{L−1})`, `D_L = (L+1) log 2 − (L−1)γ`, FOR EVERY `L ≥ 4` (u982; examples_slop §2 eq. dln_gauss, the full three-term jet of `P_{L−1}`; Astra round-14 target 1)**: `thirdCoeffD` (`D_{m+4}`), `thirdCoeffClosed` (`[D² + (m+7)π²/6]/(2(m+1)! s^{m+3})`), `thirdCoeffD_succ` (`D_{L+1} = D_L + 2R₀`), `thirdCoeff_zero_eq` (the base `C₄` from the exact `C₃` (DCXLV), `J` (DCXXXVIII), `R₀`: `(4l−2γ)² + 4(2l−γ)(l−γ) + (l−γ)² + 7π²/6 = (5l−3γ)² + 7π²/6`), `thirdCoeffClosed_succ` (the recursion preserves the closed form: `T_{L+1} − T_L = 2D_LR₀ + 4J` with `4J = 2R₀² + π²/12`), ★★★ `thirdCoeff_eq_closed` (induction). Numerics: `gauss_third_coeff_check.py` (`C₄ = 0.461015`, closed form vs recursion to 1e−10 for `L = 4..8`). With DCXXVI (`A_L`, `B_L`) and DCXXXVI the three leading coefficients of `P_{L−1}` are explicit theorems at every depth `L ≥ 3`. Lean: fold `√(2π)` into an atom `S` with `π = S²/2` before `field_simp; ring`; `Nat.factorial_succ` twice for `(m+3)!`. | GaussianThirdCoeffClosed.lean |
| **DCXLVII** | ★★★ **THE ABSTRACT MELLIN RESIDUAL LEMMA AND THE LOG-POWER MELLIN TRANSFORMS (u983; examples_slop §2, the Mellin transfer between `Z(N)` expansions and zeta poles as a library lemma; Astra round-14 target 2)**: ★★ `integral_Ioi_one_rpow_mul_log_pow` (`∫₁^∞ v^{z−2}(log v)^k = k!/(1−z)^{k+1}` for `z < 1`, by the substitution `v = e^x` (`integral_comp_exp_Ioi`) and the Gamma integral — no integration by parts), `integrableOn_Ioi_one_rpow_mul_log_pow` (`(log v)^k ≤ (v^ε/ε)^k`, `ε = (1−z)/(2(k+1))`), ★★★ `tendsto_mellin_residual` (`IntegrableOn (v^{a−1}q) (Ioc 0 1)` for some `a < 1` and `IntegrableOn q (Ioi 1)` ⇒ `∫₀^∞ v^{z−1}q → ∫₀^∞ q` along `𝓝[<] 1`; dominated convergence with `1_{(0,1]}v^{a−1}|q| + 1_{(1,∞)}|q|`), `tendsto_mellin_residual_depthThreeQ` (DCXLII's limit re-derived from the lemma with `a = ½`). Numerics: the transforms for `z ∈ {0.3, 0.7}`, `k ≤ 3` agree with `k!/(1−z)^{k+1}` to 1e−9. Lean: `Integrable.abs` results need `IntegrableOn.congr_fun`/`.integrable_indicator` called by name; `Real.rpow_mul` after `mul_comm` to get `(v^ε)^k`. | MellinResidualLemma.lean |
| **DCXLVIII** | ★★★ **THE GENERIC POWER/LOG FACE CERTIFICATE: `x^a(1+|log x|)^k` INTEGRABLE ON `(0,1)` FOR `a > −1` AND FINITE PRODUCTS INTEGRABLE ON THE CUBE (u984; examples_slop §6, the analytic building block of the naive-Bayes envelope certificate DCXVII; Astra round-14 target 3)**: `one_add_abs_log_pow_le` (`(1+|log x|)^k ≤ (1+1/ε)^k x^{−kε}` on `(0,1]` — NOT `(2/ε)^k`, which fails for `ε > 1`), ★★ `integrableOn_rpow_mul_logWeight` (`ε = (a+1)/(2(k+1))`, exponent `a − kε > −1`, `intervalIntegrable_rpow'`), `powerLogFaceWeight`, ★★★ `integrable_powerLogFaceWeight` (`Integrable.fintype_prod` on `Measure.pi (fun _ => volume.restrict (Ioo 0 1))`), `integrable_of_le_powerLogFaceWeight` (domination adapter). Lean: `Grammar.faceWeight` already existed (`SpatialEnergyLaw`) — check `grep -rn "def <name>"` before naming. Not included: that the naive-Bayes envelope has these exponents on each face, chart Jacobians, joint measurability of the fibre family. | PowerLogFaceCertificate.lean |

## Public statements of the three new files (docstrings + signatures, proofs omitted)
### Grammar/GaussianThirdCoeffClosed.lean
```lean
/-- `D_L = (L+1) log 2 − (L−1) γ` at `L = m + 4`. -/
noncomputable def thirdCoeffD (m : ℕ) : ℝ

/-- The closed form at `L = m + 4`: `[D² + (m+7)π²/6] / (2 (m+1)! s^{m+3})`. -/
noncomputable def thirdCoeffClosed (m : ℕ) : ℝ

theorem thirdCoeffD_succ (m : ℕ) : thirdCoeffD (m + 1) = thirdCoeffD m + 2 * gaussR₀

/-- The base `C₄ = [D₄² + 7π²/6]/(2 s³)` from the exact `C₃`, `J`, `R₀`. -/
theorem thirdCoeff_zero_eq : thirdCoeff 0 = thirdCoeffClosed 0

/-- The step: the recursion preserves the closed form. -/
theorem thirdCoeffClosed_succ (m : ℕ) :
    (thirdCoeffClosed m / (m + 2) + 2 * gaussCoeffB m * gaussR₀ +
      4 * (m + 3) * gaussCoeffA m * gaussJlog) / Real.sqrt (2 * Real.pi) =
      thirdCoeffClosed (m + 1)

/-- ★★★ **The third coefficient in closed form at every depth**:
`C_{m+4} = [((m+5) log 2 − (m+3)γ)² + (m+7)π²/6] / (2 (m+1)! √(2π)^{m+3})`. -/
theorem thirdCoeff_eq_closed (m : ℕ) : thirdCoeff m = thirdCoeffClosed m
```

### Grammar/MellinResidualLemma.lean
```lean
lemma and the log-power Mellin transforms

DCXLII's mechanism as a library lemma (★★★ `tendsto_mellin_residual`): if `v^{a−1} q` is
integrable on `(0,1]` for some `a < 1` and `q` is integrable on `(1,∞)`, then

  `∫₀^∞ v^{z−1} q(v) dv → ∫₀^∞ q(v) dv`  as `z → 1⁻`

(dominated convergence: eventually `a < z < 1`, `v^{z−1} ≤ v^{a−1}` on `(0,1]`, `≤ 1` beyond).
So for `Z(v) = q(v) + 1_{(1,∞)}(v) P(log v)/v` the finite part of the Mellin transform at its pole
is the residual integral, the polar part being `Σ_k p_k k!/(1−z)^{k+1}` by the log-power transforms

  `∫₁^∞ v^{z−2} (log v)^k dv = k!/(1−z)^{k+1}`  for `z < 1`
  (★★ `integral_Ioi_one_rpow_mul_log_pow`),

evaluated by the substitution `v = e^x` (`integral_comp_exp_Ioi`) and the Gamma integral — no
integration by parts.  Examples_slop §2 (the Mellin transfer between `Z(N)` expansions and zeta
poles); Astra round-14 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The log-power Mellin transforms on `(1,∞)` -/

/-- ★★ `∫₁^∞ v^{z−2} (log v)^k dv = k!/(1−z)^{k+1}` for `z < 1`. -/
theorem integral_Ioi_one_rpow_mul_log_pow {z : ℝ} (hz : z < 1) (k : ℕ) :
    ∫ v in Ioi (1 : ℝ), v ^ (z - 2) * Real.log v ^ k = (k.factorial : ℝ) / (1 - z) ^ (k + 1)

/-- `v^{z−2} (log v)^k` is integrable on `(1,∞)` for `z < 1`
(`(log v)^k ≤ (v^ε/ε)^k`, `ε = (1−z)/(2(k+1))`). -/
theorem integrableOn_Ioi_one_rpow_mul_log_pow {z : ℝ} (hz : z < 1) (k : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * Real.log v ^ k) (Ioi 1)

lemma -/

/-- ★★★ **The Mellin residual lemma**: if `v^{a−1} q` is integrable on `(0,1]` for some
`a < 1` and `q` is integrable on `(1,∞)`, then `∫₀^∞ v^{z−1} q → ∫₀^∞ q` as `z → 1⁻`. -/
theorem tendsto_mellin_residual {q : ℝ → ℝ} {a : ℝ} (ha1 : a < 1)
    (hq : Measurable q) (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * q v) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ v in Ioi (0 : ℝ), q v))

/-- The residual lemma with a Lebesgue-integrable `q` on `(0,∞)` and `v^{a−1}` bounded on `(0,1]`
by an explicit hypothesis is a special case; the version above only asks for the weighted
integrability near `0`.  Consequence for DCXLII: `depthThreeQ` satisfies the hypotheses with
`a = ½` (`q = Z₂(v²) ≤ 1` on `(0,1]`). -/
theorem tendsto_mellin_residual_depthThreeQ :
    Tendsto (fun z : ℝ => ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * depthThreeQ v) (𝓝[<] (1 : ℝ))
      (𝓝 depthThreeQint)
```

### Grammar/PowerLogFaceCertificate.lean
```lean
/-- `(1 + |log x|)^k ≤ (1 + 1/ε)^k x^{−kε}` on `(0,1]` for `ε > 0`. -/
theorem one_add_abs_log_pow_le {x ε : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) (k : ℕ) :
    (1 + |Real.log x|) ^ k ≤ (1 + 1 / ε) ^ k * x ^ (-(k * ε))

/-- ★★ `x^a (1 + |log x|)^k` is integrable on `(0,1)` for `a > −1`. -/
theorem integrableOn_rpow_mul_logWeight {a : ℝ} (ha : -1 < a) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ a * (1 + |Real.log x|) ^ k) (Ioo 0 1)

/-- The face weight `W(x) = ∏ᵢ (xᵢ)^{aᵢ} (1 + |log xᵢ|)^{kᵢ}` on the cube `(0,1)^d`. -/
noncomputable def powerLogFaceWeight {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (x : Fin d → ℝ) : ℝ

/-- ★★★ **The face certificate**: `W` is integrable on `(0,1)^d` when every `aᵢ > −1`. -/
theorem integrable_powerLogFaceWeight {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (ha : ∀ i, -1 < a i) :
    Integrable (powerLogFaceWeight a k)
      (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))

/-- The domination adapter: a measurable `f` with `‖f‖ ≤ C · W` is integrable on the cube. -/
theorem integrable_of_le_powerLogFaceWeight {d : ℕ} {a : Fin d → ℝ} {k : Fin d → ℕ}
    (ha : ∀ i, -1 < a i)
    {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)))
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C * powerLogFaceWeight a k x) :
    Integrable f (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))
```

## Definitions relied on
```lean
noncomputable def gaussCoeffA (m : ℕ) : ℝ := 1 / ((m + 3).factorial * Real.sqrt (2 * Real.pi) ^ (m + 3))
noncomputable def gaussCoeffB (m : ℕ) : ℝ :=
  ((m + 5) * Real.log 2 - (m + 3) * Real.eulerMascheroniConstant) / ((m + 2).factorial * Real.sqrt (2 * Real.pi) ^ (m + 3))
noncomputable def thirdCoeff : ℕ → ℝ
  | 0 => (depthThreeConst + 2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussR₀ + 8 * (1 / (4 * Real.pi)) * gaussJlog) / Real.sqrt (2 * Real.pi)
  | m + 1 => (thirdCoeff m / (m + 2) + 2 * gaussCoeffB m * gaussR₀ + 4 * (m + 3) * gaussCoeffA m * gaussJlog) / Real.sqrt (2 * Real.pi)
theorem gaussLaplaceL_third_coeff (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 4) N - gaussCoeffA m * (Real.log N) ^ (m + 3) - gaussCoeffB m * (Real.log N) ^ (m + 2)) / (Real.log N) ^ (m + 1)) atTop (𝓝 (thirdCoeff m))
theorem depthThreeConst_eq : depthThreeConst = ((4 * Real.log 2 - 2 * Real.eulerMascheroniConstant) ^ 2 + Real.pi ^ 2) / (4 * Real.pi)
theorem depthThreeQint_eq : depthThreeQint = (depthThreeC ^ 2 + 5 * Real.pi ^ 2 / 6) / (4 * Real.sqrt (2 * Real.pi))
theorem gaussJlog_eq : gaussJlog = gaussR₀ ^ 2 / 2 + Real.pi ^ 2 / 48
theorem deriv_deriv_Gamma_one_half : deriv (deriv Complex.Gamma) (1 / 2) = ((Real.sqrt Real.pi * ((Real.eulerMascheroniConstant + 2 * Real.log 2) ^ 2 + Real.pi ^ 2 / 2) : ℝ) : ℂ)   -- DCVIII
theorem deriv_deriv_Gamma_one : deriv (deriv Complex.Gamma) 1 = ((Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 : ℝ) : ℂ)   -- DCXXXVIII
theorem integral_exp_neg_log_sq : ∫ v in Ioi 0, Real.exp (-v) * (Real.log v) ^ 2 = γ² + π²/6   -- DCXXXVIII
theorem coneScaledCorrection_second_order : |F_δ a − F_0 a − δ G a| ≤ δ² K a   (0 ≤ δ ≤ 1; DCXXXIX)
theorem cone_second_coeff_bound : |N (E_N − ½ − 1/(√π√N)) − c₂| ≤ C₂/√N   (N ≥ 1; DCXXXIX);  coneSecondCoeff_eq : c₂ = −5/6 + √3/π  (DCXLI)
blowupLaplace_two_term_bound (DCXV): |Z_N − √(π/2)(log N + 5log2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N for the blow-up model K = x²(x²+y²)/2
```

## State of the note (pinned to grammar 4c0cd00)
Formal: §2 Gaussian DLN at every depth: `A_L`, `B_L`, `C_L` explicit (closed forms), the depth-three constant exact, `J`, `Q`, `Γ''(1)`, the Mellin transform of `Z₂` closed with residual bridge, jet, and the abstract transfer lemma; depth-two two-term expansion, Bessel form, crossing corollary; DLN flat prior at every depth. §3 cone: exact Leray closed form; averaged posterior `½ + 1/(√π√N) + (−5/6 + √3/π)/N + O(N^{−3/2})` with the `1/√N` rate on `c₂`, both sides four-dimensional. §4 blow-up: tie formulas, Laurent data, two-term Laplace expansion with explicit remainder, monomial constant, family theorem with log-free remainder, observable numerators and posterior ratios. §5 rank-one: normal integral and tilt at aligned and general orbit points, invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter, the generic power/log certificate.
Derivation-only (checked numerically): the constant terms of `P_{L−1}` for `L ≥ 4` (the fourth jet coefficient); `H₃`, `ζ(3)`; the naive-Bayes envelope exponents per face after the chart Jacobian, joint measurability of the fibre family, KL-vs-surrogate remainder; the naive-Bayes `m₂ = ∫e^{−z²/2}log²|z|dz = √(2π)(g²/4 + π²/8)`, `g = γ + log 2`; the blow-up higher pole `α₁ = √(π/2)/16`; the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; the cone's third coefficient (`√N(N·rem − c₂) → 0.0698`).

## Questions
1. Fidelity check (brief) of DCXLVI–DCXLVIII against the note's claims and your round-14 specifications; in particular (a) `thirdCoeffClosed` indexing (`m = L − 4`: `D = (m+5)log2 − (m+3)γ`, `(m+7)π²/6`, `(m+1)!`, `s^{m+3}`) against `C_L = [D_L² + (L+3)π²/6]/(2(L−3)!s^{L−1})`; (b) `tendsto_mellin_residual` with only `a < 1` (no lower bound on `a`): is the lemma correctly stated (the hypothesis `IntegrableOn (v^{a−1} q) (Ioc 0 1)` with `a` possibly ≤ 0)? (c) `integrableOn_rpow_mul_logWeight`'s exponent bookkeeping `a − kε > −1` with `ε = (a+1)/(2(k+1))`.
2. Rank the next three day-sized formal targets by value-per-effort with concrete Lean statements and routes. Candidates: (a) the naive-Bayes `m₂ = ∫_ℝ e^{−z²/2} log²|z| dz = √(2π)(g²/4 + π²/8)`: via `z² = 2t` it is `√2 ∫₀^∞ t^{−1/2} e^{−t} (½ log(2t))² dt`, i.e. the second log-moment of the Gamma integrand at `s = ½` — DCVIII has `deriv_deriv_Gamma_one_half` and DCXXXVIII proved `∫₀^∞ e^{−v}log²v = Γ''(1)` through `deriv_Gamma_eq_mellin`/`hasDerivAt_mellin_log_exp`; is the same route at `s = ½` day-sized (the Mellin derivative machinery is stated for `0 < Re s`)?; (b) the polynomial-subtraction corollary of the residual lemma (`Z = q + 1_{v>1}P(log v)/v` with `P` of degree `d`, coefficients `p : Fin (d+1) → ℝ`: `M_Z(z) − Σ p_k k!/(1−z)^{k+1} → ∫q`), as the general Mellin transfer; (c) the cone's third coefficient `c₃` as an integral-defined limit with rate (third-order tilt expansion `|1 − e^{−x} − x + x²/2| ≤ x³/6`, `G₂ = ½ ∂²_δ F` — your normalisation warning noted), with the Gaussian domination as the main work; (d) the blow-up `α₁ = √(π/2)/16` (a `1/N` term of `Z_N`): DCXV's reduced integral is `√(2π)∫ e^{−Nx⁴/2}e^{−x²/2}/√(1+Nx²)dx`; is a second-order expansion with explicit remainder `O(N^{−3/2})` day-sized given DCXIV's `AmplitudeJ` engine?; (e) the depth-four constant `D₄` as an integral-defined limit with a rate (DCXXXI/DCXXXIV pattern one order up; needs the `log²` weighted kernel `∫h log²x/x` as an integral-defined constant, not its value); (f) the joint measurability of the naive-Bayes fibre family or the KL-vs-surrogate remainder. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the three new files (`thirdCoeffClosed` vs `thirdCoeff` naming and the `m` offset; `powerLogFaceWeight` on `Measure.pi (fun _ => volume.restrict (Ioo 0 1))` vs the cube as a set; the residual lemma's `Measurable q` vs `AEStronglyMeasurable`).
Answer concisely with Lean-facing detail.
