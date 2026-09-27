You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main e6b3348, 992 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-17 programme is COMPLETE, all three targets as theorems: (2) the linear-log depth-four rate `K(1+ℓ)/√N` (DCLIV, exactly your route: `a²/2` for `j = 0`, `ℓ² /(2N) ≤ ℓ/√N`); (1) the naive-Bayes fixed-domain density (DCLV: joint measurability of `nbFibreDensity`, the real kernel/density `nbRectKernel`/`nbFixedDensity` with `measurable_nbFixedDensity` = DCLIII instantiated, the unconditional identification `nbFixedDensity = (nbFibreDensity).toReal`, and the real closed form on `0 < |μ| < M±`); (3) the depth-five polynomial limit (DCLVI: `√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ → E₅`, with `D₅ = [D₄ + 2C₄R₀ + 8B₄J + 24A₄J₂]/s`, `E₅ = (2/s)[Q₄ + D₄R₀ + 2C₄J + 4B₄J₂ + 8A₄J₃]`).

NUMERICS (new route, `gauss_depth5_const_check.py`): every `Z_L(e^{2t})` computed as the convolution of the `(L−1)`-fold convolution of the `log|W|` density `√(2/π)e^{u−e^{2u}/2}` with `k(−·)`, `k(y) = (1+e^{2y})^{−1/2}`, on one log grid (FFT). Results: `Q₃ = 0.8191867`, `D₄ = 0.7654007`, `Q₄ = 1.0422974`, `D₅ = 0.3553670`, `E₅ = 1.0205197`; direct `√N Z₅ − P₅(ℓ) = 1.02034, 1.02049, 1.02052` at `N = 10⁴,10⁵,10⁶`. MELLIN JET for general `L` (my derivation, please check): `√N Z_L ∼ 2^{−(L−1)/2}π^{−L/2} Σ_k g_k ℓ^{L−1−k}/(L−1−k)!`, `g_k = [u^k] Γ(½−u)Γ(1+u)^L 2^{(L−1)u}` — the residue at the order-`L` pole `s = ½` of `Γ(s)Γ(½−s)N^{−s}E|X|^{−2s}/√π`, `X = ∏_{i<L} W_i`, `E|X|^{−2s} = (2^{−s}Γ(½−s)/√π)^{L−1}` (DCVI). It reproduces `A_L, B_L, C_L` (`L = 4, 5`) to `10⁻¹⁵`, `D₄ = 0.7654005`, `D₅ = 0.3553669`, `E₅ = 1.0205207`. So the integral-defined constants agree with the jet to `10⁻⁶` at both depths.

## HEADLINES rows DCLIV–DCLVI
| **DCLIV** | ★★★ **THE DEPTH-FOUR CONSTANT WITH THE LINEAR-LOG RATE (u990; Astra round-17 target 2)**: ★★★ `gaussLaplaceL_four_constant_rate_linear : ∃ K ≥ 0, ∀ N ≥ 1, |√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1 + ℓ)/√N` — DCLII's assembly with the `j = 0` cutoff moment bounded by DCXXXI's `|∫₀^a h/x| ≤ a²/2` (`abs_integral_gaussH_div_Ioc_le`) instead of `a/2`, so the quadratic cutoff product costs `ℓ²/(2N) ≤ ℓ/√N` (`log_le_two_mul_sqrt : log N ≤ 2√N`); no combined-cutoff refactor. Sharper rates (`(1 + ℓ)^k/N`) need `q₃ = O((1 + log v)²/v³)`, not available from the DCXXXI input `|q₃| ≤ 8(1 + 2 log v)/v²` (Astra). | GaussianDepthFourRateLinear.lean |
| **DCLV** | ★★ **THE NAIVE-BAYES PUSHFORWARD DENSITY AS A FIXED-DOMAIN PARAMETER INTEGRAL (u991; Astra round-17 target 1)**: ★★ `measurable_nbFibreDensity` (`(λ, μ) ↦ nbFibreDensity λ₁ λ₂ μ` jointly measurable, `Measurable.lintegral_prod_right'` with the jointly measurable slice density `measurable_nbSliceDensity_joint`); the real rectangle kernel `nbRectKernel λ t z = (prodDensity (α₁(t), β₁(t), α₂(t), β₂(t)) z).toReal` and the real fixed-domain density `nbFixedDensity (λ, μ) = ∫₀¹ dt/(t(1−t)) h_λ(t, μ/(t(1−t)))` (examples_slop eq. nb_rho_integral) with ★★ `measurable_nbFixedDensity` = DCLIII's `measurable_fixedDomainIntegral` instantiated; ★★ `nbFixedDensity_eq_toReal : nbFixedDensity ((λ₁,λ₂), μ) = (nbFibreDensity λ₁ λ₂ μ).toReal` unconditionally (`integral_eq_lintegral_of_nonneg_ae`, `prodDensity_ne_top`); ★★ `nbFixedDensity_closed_pos/neg`: the REAL closed form `ρ(λ, μ) = 2 log(M±/|μ|) log(V/(M±|μ|))` on `0 < |μ| < M±` (eq. nb_rho). Not included: fibre integrability outside the closed-form window. | NaiveBayesFixedDomainDensity.lean |
| **DCLVI** | ★★★ **THE DEPTH-FIVE POLYNOMIAL LIMIT (u992; Astra round-17 target 3)**: ★★★ `gaussLaplaceL_five_constant : √N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ → E₅` with `A₅ = gaussCoeffA 1`, `B₅ = gaussCoeffB 1`, `C₅ = thirdCoeff 1` (the all-depth coefficients), the NEW linear coefficient `depthFiveLinCoeff = [D₄ + 2C₄R₀ + 8B₄J + 24A₄J₂]/s` and constant `depthFiveConst = (2/s)[Q₄ + D₄R₀ + 2C₄J + 4B₄J₂ + 8A₄J₃]`, `J₃ = ∫₀^∞ h log³x/x` (`gaussJlog3`), `Q₄ = ∫₀^∞ q₄` (`depthFiveQint`), `q₄(v) = Z₄(v²) − 1_{v>1}P₄(2 log v)/v` (`depthFiveQ`, full depth-four polynomial `depthFourJet`), `|q₄| ≤ K(1 + 2 log v)/v²` from DCLIV (`depthFiveQ_outer_le`). DCLI's route one depth up: scalar recursion `sqrt_mul_gaussLaplaceL_five_eq`, DCT `tendsto_depthFiveQ_term`, tail substitution, `depthFourJet_shift`, flat part `A₄ℓ⁴/8 + B₄ℓ³/6 + C₄ℓ²/4 + D₄ℓ/2`, four cutoff moments (`tendsto_cube_log_div_sqrt`), exact remainder `sqrt_mul_gaussLaplaceL_five_sub_eq` (with `gaussCoeffA/B_zero/one_eq`, `thirdCoeff_one_eq`). Numerics `gauss_depth5_const_check.py`. | GaussianDepthFiveConst.lean |

## Public statements of DCLVI (docstrings + signatures, proofs omitted)
```lean
/-- The full depth-four polynomial `P₄(u) = A₄u³ + B₄u² + C₄u + D₄`. -/
noncomputable def depthFourJet (u : ℝ) : ℝ

/-- `q₄(v) = Z₄(v²) − 1_{(1,∞)}(v) P₄(2 log v)/v`. -/
noncomputable def depthFiveQ (v : ℝ) : ℝ

theorem measurable_gaussLaplaceL_four_sq : Measurable fun v : ℝ => gaussLaplaceL 4 (v ^ 2)

theorem continuous_depthFourJet : Continuous depthFourJet

theorem measurable_depthFiveQ : Measurable depthFiveQ

theorem depthFiveQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthFiveQ v = gaussLaplaceL 4 (v ^ 2)

/-- On `(1,∞)`: `|q₄(v)| ≤ K(1 + 2 log v)/v²` from the linear-log depth-four rate at `N = v²`. -/
theorem depthFiveQ_outer_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 1 < v →
    |depthFiveQ v| ≤ K * (1 + 2 * Real.log v) / v ^ 2

theorem integrableOn_depthFiveQ_inner : IntegrableOn depthFiveQ (Ioc 0 1)

theorem integrableOn_depthFiveQ_outer : IntegrableOn depthFiveQ (Ioi 1)

theorem integrableOn_depthFiveQ : IntegrableOn depthFiveQ (Ioi 0)

/-- `J₃ = ∫₀^∞ h(x) log³x/x dx`. -/
noncomputable def gaussJlog3 : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 3 / x

/-- `Q₄ = ∫₀^∞ q₄`. -/
noncomputable def depthFiveQint : ℝ := ∫ v in Ioi (0 : ℝ), depthFiveQ v

/-- The depth-five linear coefficient `D₅ = [D₄ + 2C₄R₀ + 8B₄J + 24A₄J₂]/s`. -/
noncomputable def depthFiveLinCoeff : ℝ

/-- The depth-five constant `E₅ = (2/s)[Q₄ + D₄R₀ + 2C₄J + 4B₄J₂ + 8A₄J₃]`. -/
noncomputable def depthFiveConst : ℝ

theorem integrable_gaussDensity_mul_gaussLaplaceL_four {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL 4 (N * x ^ 2))

/-- `√N Z₅(N) = 2 ∫₀^∞ γ(v/√N) Z₄(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_five_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 5 N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 4 (v ^ 2)

theorem tendsto_depthFiveQ_term :
    Tendsto (fun N : ℝ => 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v)
      atTop (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFiveQint))

/-- The tail integrand. -/
noncomputable def depthFiveTail (v : ℝ) : ℝ

theorem depthFiveQ_add_tail (v : ℝ) : depthFiveQ v + depthFiveTail v = gaussLaplaceL 4 (v ^ 2)

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL_four {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL 4 (v ^ 2))
      (Ioi 0)

theorem integrableOn_gaussDensity_div_mul_depthFiveQ {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFiveQ v) (Ioi 0)

/-- `√N Z₅ = 2∫ γ(v/√N) q₄ + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_five_split {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 5 N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveTail v

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P₄(ℓ + 2 log x)/x dx`. -/
theorem depthFive_tail_integral_eq {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveTail v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x

/-- `P₄(ℓ + 2y)` as a polynomial in `y`. -/
theorem depthFourJet_shift (ℓ y : ℝ) :
    depthFourJet (ℓ + 2 * y) =
      (gaussCoeffA 0 * ℓ ^ 3 + gaussCoeffB 0 * ℓ ^ 2 + thirdCoeff 0 * ℓ + depthFourConst) +
      (6 * gaussCoeffA 0 * ℓ ^ 2 + 4 * gaussCoeffB 0 * ℓ + 2 * thirdCoeff 0) * y +
      (12 * gaussCoeffA 0 * ℓ + 4 * gaussCoeffB 0) * y ^ 2 +
      8 * gaussCoeffA 0 * y ^ 3

theorem integrableOn_gaussH_depthFourJet {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N))

theorem integrableOn_depthFourJet_div_Ioc {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => depthFourJet (Real.log N + 2 * Real.log x) / x)
      (Ioc (1 / Real.sqrt N) 1)

/-- The tail splits into the flat part and the `h`-part. -/
theorem depthFive_tail_integral_split {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, depthFourJet (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x)

/-- The flat part exactly: `∫_a^1 P₄(ℓ + 2 log x)/x = A₄ℓ⁴/8 + B₄ℓ³/6 + C₄ℓ²/4 + D₄ℓ/2`. -/
theorem depthFive_flat_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthFourJet (Real.log N + 2 * Real.log x) / x =
      gaussCoeffA 0 * (Real.log N) ^ 4 / 8 + gaussCoeffB 0 * (Real.log N) ^ 3 / 6 +
        thirdCoeff 0 * (Real.log N) ^ 2 / 4 + depthFourConst * Real.log N / 2

/-- The cutoff `h`-moments: `∫_a^∞ h P₄(ℓ + 2 log x)/x = Σ_j c_j(ℓ) ∫_a^∞ h log^j x/x`. -/
theorem depthFive_hpart_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * depthFourJet (Real.log N + 2 * Real.log x) / x =
      (gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
        thirdCoeff 0 * Real.log N + depthFourConst) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x / x) +
      (6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
        2 * thirdCoeff 0) * (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) +
      (12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
      8 * gaussCoeffA 0 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 3 / x

theorem tendsto_cube_log_div_sqrt :
    Tendsto (fun N : ℝ => (Real.log N) ^ 3 / Real.sqrt N) atTop (𝓝 0)

theorem gaussCoeffA_zero_eq : gaussCoeffA 0 = 1 / (6 * Real.sqrt (2 * Real.pi) ^ 3)

theorem gaussCoeffB_zero_eq : gaussCoeffB 0 =
    (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) / (2 * Real.sqrt (2 * Real.pi) ^ 3)

theorem gaussCoeffA_one_eq : gaussCoeffA 1 = 1 / (24 * Real.sqrt (2 * Real.pi) ^ 4)

theorem gaussCoeffB_one_eq : gaussCoeffB 1 =
    (6 * Real.log 2 - 4 * Real.eulerMascheroniConstant) / (6 * Real.sqrt (2 * Real.pi) ^ 4)

theorem thirdCoeff_one_eq : thirdCoeff 1 = (thirdCoeff 0 / 2 + 2 * gaussCoeffB 0 * gaussR₀ +
    12 * gaussCoeffA 0 * gaussJlog) / Real.sqrt (2 * Real.pi)

/-- The assembled remainder: for `N ≥ 1`,
`√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ = 2∫γ(v/√N)q₄ + (2/s)[−c₀ε₀ − c₁ε₁ − c₂ε₂ + 8A₄(J₃ − ε₃) + D₄R₀ +
2C₄J + 4B₄J₂]`. -/
theorem sqrt_mul_gaussLaplaceL_five_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * (Real.log N) ^ 4 -
      gaussCoeffB 1 * (Real.log N) ^ 3 - thirdCoeff 1 * (Real.log N) ^ 2 -
      depthFiveLinCoeff * Real.log N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFiveQ v) +
      2 / Real.sqrt (2 * Real.pi) *
        ((gaussCoeffA 0 * (Real.log N) ^ 3 + gaussCoeffB 0 * (Real.log N) ^ 2 +
          thirdCoeff 0 * Real.log N + depthFourConst) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        (6 * gaussCoeffA 0 * (Real.log N) ^ 2 + 4 * gaussCoeffB 0 * Real.log N +
          2 * thirdCoeff 0) * (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        (12 * gaussCoeffA 0 * Real.log N + 4 * gaussCoeffB 0) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
        8 * gaussCoeffA 0 *
          (gaussJlog3 - ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 3 / x) +
        depthFourConst * gaussR₀ + 2 * thirdCoeff 0 * gaussJlog +
        4 * gaussCoeffB 0 * gaussJlog2)

/-- ★★★ **The depth-five constant**: `√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ → E₅`. -/
theorem gaussLaplaceL_five_constant :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 5 N - gaussCoeffA 1 * (Real.log N) ^ 4 -
      gaussCoeffB 1 * (Real.log N) ^ 3 - thirdCoeff 1 * (Real.log N) ^ 2 -
      depthFiveLinCoeff * Real.log N) atTop (𝓝 depthFiveConst)
```

## Public statements of DCLV
```lean
/-- `prodDensity` is a finite sum of `ENNReal.ofReal`s, never `⊤`. -/
theorem prodDensity_ne_top (α β γ δ z : ℝ) : prodDensity α β γ δ z ≠ ⊤

/-- The slice density is jointly measurable in `(λ₁, λ₂, z, t)`. -/
theorem measurable_nbSliceDensity_joint :
    Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ => nbSliceDensity q.1.1.1 q.1.1.2 q.2 q.1.2

/-- ★★ The naive-Bayes fibre density is jointly measurable in `(λ, μ)`. -/
theorem measurable_nbFibreDensity :
    Measurable fun p : (ℝ × ℝ) × ℝ => nbFibreDensity p.1.1 p.1.2 p.2

/-- The real rectangle kernel `h_λ(t, z)`: the two-logarithm density of `η₁η₂` on the
rectangle `[−α₁(t), β₁(t)] × [−α₂(t), β₂(t)]` at fixed means `λ = (λ₁, λ₂)`. -/
noncomputable def nbRectKernel (L : ℝ × ℝ) (t z : ℝ) : ℝ

/-- The real fixed-domain density `ρ(λ, μ) = ∫₀¹ dt/(t(1−t)) · h_λ(t, μ/(t(1−t)))`
(examples_slop eq. nb_rho_integral). -/
noncomputable def nbFixedDensity (p : (ℝ × ℝ) × ℝ) : ℝ

/-- The composed rectangle kernel is jointly measurable (the hypothesis of DCLIII). -/
theorem measurable_nbRectKernel :
    Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      nbRectKernel p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2)))

/-- ★★ The real fixed-domain density is measurable in `(λ, μ)`: DCLIII instantiated. -/
theorem measurable_nbFixedDensity : Measurable nbFixedDensity

/-- ★★ The two versions agree: `nbFixedDensity ((λ₁, λ₂), μ) = (nbFibreDensity λ₁ λ₂ μ).toReal`. -/
theorem nbFixedDensity_eq_toReal (l₁ l₂ z : ℝ) :
    nbFixedDensity ((l₁, l₂), z) = (nbFibreDensity l₁ l₂ z).toReal

/-- ★★ The real closed form, `μ > 0`: for `0 < μ < M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`,
`ρ(λ, μ) = 2 log(M₊/μ) · log(V/(M₊μ))`, `V = λ₁(1−λ₁)λ₂(1−λ₂)`. -/
theorem nbFixedDensity_closed_pos {z : ℝ} (hz : 0 < z)
    (hzM : z < min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))) :
    nbFixedDensity ((l₁, l₂), z) = 2 *
      (Real.log (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) / z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * (1 - l₂)) (l₂ * (1 - l₁)) * z)))

/-- ★★ The real closed form, `μ < 0`: for `−M₋ < μ < 0`, `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`,
`ρ(λ, μ) = 2 log(M₋/|μ|) · log(V/(M₋|μ|))`. -/
theorem nbFixedDensity_closed_neg {z : ℝ} (hz : z < 0)
    (hzM : -z < min (l₁ * l₂) ((1 - l₁) * (1 - l₂))) :
    nbFixedDensity ((l₁, l₂), z) = 2 *
      (Real.log (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) / -z) *
        Real.log (l₁ * (1 - l₁) * (l₂ * (1 - l₂)) /
          (min (l₁ * l₂) ((1 - l₁) * (1 - l₂)) * -z)))
```

## State (pinned to grammar e6b3348)
Formal: §2 Gaussian DLN: `A_L, B_L, C_L` closed at every depth; `C₃` exact; `D₄` with the linear-log rate; the full depth-five polynomial as a limit (`D₅`, `E₅` integral-defined); `J`, `Q`, `Γ''(1)`, Mellin closed form of `Z₂`, residual bridge, jet, abstract/log-polynomial/a.e. transfer; depth-two two-term, Bessel form. §3 cone: exact `c₂` with rate. §4 blow-up: two-term expansion, family theorem, observables. §5 rank-one: normal integral, tilts. §6 naive Bayes: pushforward density (ENNReal and real fixed-domain forms, jointly measurable, closed form), surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificates (also on the cube as a set), basepoint adapter, `m₂`.
Derivation-only: the jet identification of `D₄`, `D₅`, `E₅` (needs `Γ'''(1)`/`ζ(3)`, `Γ''''(1)`/`ζ(4)`); `J₂`, `J₃` exact; the all-depth engine; the sharp depth-four rate; the naive-Bayes fibre integrability outside the closed-form window, chart envelope exponents, KL-vs-surrogate; blow-up `N^{−3/2}log N` coefficient; rank-one Morse–Bott; smooth-amplitude tie remainder; cone `c₃`.

## Questions
1. Fidelity check (brief) of DCLIV–DCLVI: (a) `depthFiveLinCoeff` and `depthFiveConst` against your recursion `P_{L+1}(ℓ) = (1/s)∫₀^ℓ P_L + (2/s)Σ_j 2^j P_L^{(j)}(ℓ)J_j/j! + (2/s)Q_L` (with `J₀ = R₀`) — are the coefficients `8B₄J`, `24A₄J₂` in `D₅` and `4B₄J₂`, `8A₄J₃` in `E₅` right?; (b) the general Mellin-jet formula above (prefactor `2^{−(L−1)/2}π^{−L/2}`, `g_k` with `Γ(½−u)`, `2^{(L−1)u}`), and its consequence: `E₅ = g₄/(4π^{5/2})` — could you give the closed form of `E₅` (and re-derive `D₅` closed) in terms of `log 2, γ, π², ζ(3), ζ(4) = π⁴/90`? (c) DCLV: is `nbFixedDensity_eq_toReal` unconditional as stated (Lean's Bochner integral of a non-integrable nonnegative function is `0`, and `(⊤).toReal = 0`, so both sides vanish together; the lintegral is finite wherever the closed form applies)?
2. Now that two instances (depth 4→5 and 3→4) of the step exist, is the ALL-DEPTH ENGINE day-sized? Concretely: a structure `PolyResidualData (L) (P : polynomial coefficients c : Fin n → ℝ) (Q)` with hypotheses (i) `√N Z_L(N) − Σ c_k ℓ^k → 0` is NOT enough (you said the residual `(1+log v)^m/v` need not be integrable); so what IS the right hypothesis? Options: (H1) a rate `|√N Z_L(N) − P_L(log N)| ≤ K(1+ℓ)^m/√N` for `N ≥ 1` (this is what DCLIV gives at `L = 4` with `m = 1` and what DCXXXIV gave at `L = 3` with `m = 1`) — then `|q_L(v)| ≤ K(1+2log v)^m/v²`, integrable, and the step yields the LIMIT `√N Z_{L+1} − P_{L+1}(ℓ) → 0` but NOT a rate at `L+1` (so the induction cannot continue) — unless the residual bound is made quantitative as in DCLII (split at `√N`: `O((1+ℓ)^{m+1}/√N)`) plus the cutoff moments `O((1+ℓ)^{deg P}/√N)`: then the rate at `L+1` is `K'(1+ℓ)^{max(m+1, L−1)}/√N` — and the induction closes with `m_L = L − 1`. Is this right? If so the engine is: `theorem poly_step (hrate : ∀ N ≥ 1, |√N Z_L N − P.eval (log N)| ≤ K (1+log N)^m/√N) : ∃ K', ∀ N ≥ 1, |√N Z_{L+1} N − (stepPoly P Q_L).eval (log N)| ≤ K' (1 + log N)^{m'}/√N` with `stepPoly` the recursion above and `Q_L = ∫ q_L` defined from `P`. Please give the cleanest Lean-facing interface (coefficient vectors `Fin (n+1) → ℝ` vs `Polynomial ℝ`; how to state `∫₀^ℓ P` and `P^{(j)}` — `Polynomial.derivative` iterated, `Polynomial.eval` — and which Mathlib lemmas give `HasDerivAt (fun x => (P.comp (C ℓ + C 2 * X)).eval (log x)) …`), and an honest day-count. Alternatively rank a cheaper deliverable: the depth-five RATE `K(1+ℓ)^m/√N` from DCLII's residual bound with `|q₄| ≤ K(1+2log v)/v²` (identical mechanism; gives `m = 2` or, with the `a²/2` trick, `m = 1`?).
3. Other day-sized candidates, ranked: (a) `Γ'''(1) = −γ³ − γπ²/2 − 2ζ(3)` in Mathlib on this pin — the route through the Hadamard/Weierstrass product or through `Real.Gamma` and `hasSum_zeta_nat`? (Mathlib has `Complex.Gamma`, `Real.Gamma`, `Real.log_Gamma`? the Bohr–Mollerup? `Real.eulerMascheroniConstant` as `lim H_n − log n`, `riemannZeta`, `hasSum_zeta_two/four`; is `deriv (deriv (deriv Gamma)) 1` reachable? If not, what about `J₂`, `J₃` as integrals of `(e^{−u} − 1_{(0,1]}) log^k u/u = Γ^{(k+1)}(1)/(k+1)` — a theorem relating `J_k` to `Γ^{(k+1)}(1)` WITHOUT evaluating the derivative (the DCXXXVIII/GaussJlogExact route generalised to all `k`)? That would make `D₄`, `D₅`, `E₅` closed in terms of `Γ^{(k)}(1)`, with the ζ-values a separate identification; (b) the cone `c₃`; (c) naive-Bayes fibre integrability: `nbFixedDensity` integrable in `μ` over `ℝ` for fixed `λ ∈ (0,1)²` (it is a probability density: mass `1`, from `lintegral_nbBox_moments` with `Ψ = 1`?) — is `∫ ρ(λ,μ) dμ = 1` for a.e. `λ` a theorem from the pushforward chain (Tonelli), giving integrability for free?; (d) the blow-up `N^{−3/2} log N` coefficient. Give the Lean-facing interface for the top two.
Answer concisely with Lean-facing detail.
