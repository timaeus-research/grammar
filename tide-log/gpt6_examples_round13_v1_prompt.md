You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 4662242, 974 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-12 targets ALL landed: (1) DCXXXVII the blow-up posterior ratios; (2) DCXXXVIII the exact `J = R₀²/2 + π²/48` through the WEIGHTED DCXI kernel exactly as you prescribed, and `Γ''(1) = γ² + π²/6` by differentiating the complex duplication formula twice at `½` (Mathlib supplied `Γ'(1) = −γ` and `Γ'(½)`; DCVIII supplied `Γ''(½)`); (3) DCXXXIX the cone's second coefficient with a rate `C₂/√N` — by a second-order expansion of the tilt integrals with `|1 − e^{−x} − x| ≤ x²` (no differentiation of a parameter integral). Numerics: `J` and every intermediate integral to 1e−11; `c₂ = −0.282004` by both `∫Gγ` and `−½∫(a²+1−m²)γ`, equal to `−5/6 + √3/π`, with `√N(N·rem − c₂) → 0.0698` (the `1/√N` rate is sharp).

## HEADLINES rows DCXXXVIII–DCXXXIX
| **DCXXXVIII** | ★★★ **THE EXACT LOGARITHMIC MOMENT `J = ∫₀^∞ h(x) log x/x dx = R₀²/2 + π²/48` AND `Γ''(1) = γ² + π²/6` (u972–973; examples_slop §2, the third Gaussian coefficient made explicit up to `Q`; Astra round-12 target 2)**: `GammaSecondDerivOne.lean` — `deriv_duplication`/`deriv_deriv_duplication` (Legendre duplication `Γ(z)Γ(z+½) = Γ(2z)2^{1−2z}√π` differentiated twice at `z = ½` via DCVIII's `hasDerivAt_Gamma_of_re_pos`/`hasDerivAt_deriv_Gamma_of_re_pos`, Mathlib's `Γ'(1) = −γ`, `Γ'(½)` and DCVIII's `Γ''(½)`), ★★★ `deriv_deriv_Gamma_one`, ★★ `integral_exp_neg_log_sq` (`∫₀^∞ e^{−v} log² v = γ² + π²/6` through `deriv_Gamma_eq_mellin`). `GaussJlogExact.lean` — the weighted DCXI kernel: `integral_log_div_self` (`∫₁^v log u/u = ½ log² v`), `integral_kernel_log_sq`, `integral_abs_kernel_log_sq`, `integrableOn_logKernel_log`, `integral_exp_kernel_log` (`∫ e^{−v} logKernel(v,u) log u dv = (e^{−u} − 1_{(0,1]}) log u/u`), `integrableOn_exp_neg_log_sq` (`log² v ≤ 16 v^{−1/2} + v²`), `integrable_expKernelLog_prod`, `integrableOn_renormalised_exp_log`, ★★ `integral_renormalised_exp_log` (Fubini: `∫₀^∞ (e^{−u} − 1_{(0,1]}) log u/u = ½ Γ''(1)`); the cutoff moved to `½`: `integral_Ioc_half_one_inv` (`log 2`), `integral_Ioc_half_one_inv_mul_log` (`−½ log² 2`), `half_cut_split_inv/log`, `integrableOn_renormalised_exp_inv_half/log_half`, `integral_renormalised_exp_inv_half` (`log 2 − γ`), `integral_renormalised_exp_log_half`; the substitution `y = x²/2` (`integral_comp_rpow_Ioi_of_pos` with `p = 2`, then `integral_comp_mul_left_Ioi`): `gaussJlog_eq_half_cut` (`J = ¼∫(e^{−y} − 1_{(0,½]})(log 2 + log y)/y`), ★★★ `gaussJlog_eq`. Consequences: `C₃ = depthThreeConst = ((log 2 − γ)R₀ + 2J)/π + (2/s)Q` is explicit up to `Q`; the DCXXXVI recursion then reproduces the Mellin jet exactly once `Q` is closed (numerics `gauss_jlog_exact_check.py`). Lean gotchas: `HasDerivAt.comp_add_const` for `Γ(w + ½)` (plain `.comp` mis-unifies `w + ½`); anonymous-constructor memberships `(⟨hu, h⟩ : u ∈ Ioc 0 (1/2))` unify `indicator_of_mem` against `And (0 < u)` as the set — bind the membership with a typed `have` or use `indicator_apply` + `if_pos`; `IntegrableOn.congr_fun` must be called by name on a `.div_const` result (dot notation lands on `And.congr_fun`); `Integrable.integral_prod_left` gives marginal integrability for free. | GammaSecondDerivOne.lean, GaussJlogExact.lean |
| **DCXXXIX** | ★★★ **THE CONE: THE SECOND COEFFICIENT OF THE AVERAGED POSTERIOR `N(E_N − ½ − 1/(√π√N)) → c₂ = ∫ G γ`, `G(a) = −Cov_{T∼N(a,1)}(T₊,|T|)`, WITH THE RATE `C₂/√N` (u974; examples_slop §3; Astra round-12 target 3)**: `abs_one_sub_exp_neg_sub_le` (`|1 − e^{−x} − x| ≤ x²` via `e^{−x} ≤ 1/(1+x) ≤ 1 − x + x²`), `integral_cube_abs_mul_exp_neg_half_sq` (`∫|t|³e^{−t²/2} = 4`), `integrable_cube_abs_gaussTilt`, `integral_cube_abs_gaussTilt_le` (`M₃ ≤ 4E(4 + s|a|³)`), the second-order expansions `posPart_coneTilt_second_order` (`|P_δ − P_0 + δQ₁| ≤ δ²M₃`) and `coneTilt_second_order` (`|D_δ − D_0 + δM₁| ≤ δ²M₂`); `coneCorrectionDeriv` (`G = −(Q₁D₀ − P₀M₁)/D₀²`), `sqrt_two_pi_bounds`, `conePosSqMoment_le` (`Q₁ ≤ M₂`), `abs_coneCorrectionDeriv_le` (`|G| ≤ 4(a²+1)`), the envelope `coneQuadEnvelope = (e^{|a|}/c₀)[6s(a²+1)(|a|+1) + 4s|a|³ + 16]`, ★★ `coneScaledCorrection_second_order` (`|F_δ − F_0 − δG| ≤ δ²K`; key identity `F_δ − F_0 − δG = Gδ(D₀ − D_δ)/D_δ + (ε_P D₀ − P₀ε_D)/(D_δD₀)`), `measurable_coneCorrectionDeriv`, `integrable_coneCorrectionDeriv`, `integrable_coneQuadEnvelope` (`Kγ ≤ 268e⁴/(sc₀)·e^{−a²/4}`), `coneSecondCoeff`, `coneQuadConst`, `cone_averaged_sub_eq`, ★★★ `cone_second_coeff_bound` (`|N(E_N − ½ − 1/(√π√N)) − c₂| ≤ C₂/√N` for `N ≥ 1`), ★★★ `tendsto_cone_second_coeff`. Numerics `cone_second_coeff_check.py`: `c₂ = −0.282004` by both the covariance integral and `−½∫(a²+1−m²)γ`, equal to `−5/6 + √3/π`; the finite-`N` values approach it with `√N·(deviation) → 0.0698`, confirming the `1/√N` rate. The symmetric form `c₂ = −½∫(a²+1−m(a)²)γ` and the closed value are the next unit. Lean gotchas: `|t||` does not parse (write `|(…)|`); `rw [← hNN]` with `hNN : √N√N = N` also rewrites the `N` under `√N` — isolate `N/√N = √N` by `div_eq_iff`; a `calc` with `Real.sqrt_le_sqrt`/`sqrt_sq` instead of `rw [show 2 = √(2²)]` (which rewrites every `2`); per-declaration heartbeats: twelve `set`s + long `calc`s need `maxHeartbeats 1600000`. | ConeSecondCoefficient.lean |

## Public statements of the three new files (docstrings + signatures, proofs omitted)
### Grammar/GammaSecondDerivOne.lean
```lean
/-- The derivative of the duplication product `Γ(w)Γ(w + ½)` on `Re w > 0`. -/
theorem deriv_duplication {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2))
      (deriv Complex.Gamma z * Complex.Gamma (z + 1 / 2) +
        Complex.Gamma z * deriv Complex.Gamma (z + 1 / 2)) z

/-- The second derivative of the duplication product at `½`. -/
theorem deriv_deriv_duplication :
    deriv (deriv fun w => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) (1 / 2) =
      deriv (deriv Complex.Gamma) (1 / 2) * Complex.Gamma 1 +
        2 * deriv Complex.Gamma (1 / 2) * deriv Complex.Gamma 1 +
        Complex.Gamma (1 / 2) * deriv (deriv Complex.Gamma) 1

/-- The derivative of the right side `Γ(2w) 2^{1−2w} √π` on `Re w > 0`. -/
theorem deriv_duplication_rhs {z : ℂ} (h0 : 0 < z.re) :
    HasDerivAt (fun w : ℂ =>
      Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * ((Real.sqrt Real.pi : ℝ) : ℂ))
      ((deriv Complex.Gamma (2 * z) * 2 * (2 : ℂ) ^ (1 - 2 * z) +
        Complex.Gamma (2 * z) * ((2 : ℂ) ^ (1 - 2 * z) * Complex.log 2 * (-2))) *
          ((Real.sqrt Real.pi : ℝ) : ℂ)) z

/-- The second derivative of the right side at `½`: `√π[4Γ''(1) − 8 log 2 Γ'(1) + 4(log 2)²]`. -/
theorem deriv_deriv_duplication_rhs :
    deriv (deriv fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) *
      ((Real.sqrt Real.pi : ℝ) : ℂ)) (1 / 2) =
      (4 * deriv (deriv Complex.Gamma) 1 - 8 * Complex.log 2 * deriv Complex.Gamma 1 +
        4 * Complex.log 2 ^ 2 * Complex.Gamma 1) * ((Real.sqrt Real.pi : ℝ) : ℂ)

/-- ★★★ **`Γ''(1) = γ² + π²/6`.** -/
theorem deriv_deriv_Gamma_one :
    deriv (deriv Complex.Gamma) 1 =
      ((Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6 : ℝ) : ℂ)

/-- ★★ **The second Gamma log-moment at `1`**: `∫₀^∞ e^{−v} log² v dv = Γ''(1) = γ² + π²/6`. -/
theorem integral_exp_neg_log_sq :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * (Real.log v) ^ 2 =
      Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6
```

### Grammar/GaussJlogExact.lean
```lean
/-- `∫₁^v log u/u du = ½ (log v)²` for `v > 0` (as an interval integral). -/
theorem integral_log_div_self {v : ℝ} (hv : 0 < v) :
    ∫ u in (1 : ℝ)..v, u⁻¹ * Real.log u = (Real.log v) ^ 2 / 2

/-- `∫₀^∞ logKernel v u · log u du = ½ (log v)²` for `v > 0`. -/
theorem integral_kernel_log_sq {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), logKernel v u * Real.log u = (Real.log v) ^ 2 / 2

/-- `∫₀^∞ |logKernel v u · log u| du = ½ (log v)²` for `v > 0`. -/
theorem integral_abs_kernel_log_sq {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), |logKernel v u * Real.log u| = (Real.log v) ^ 2 / 2

/-- The weighted kernel is integrable in `u` on `(0, ∞)` for every `v > 0`. -/
theorem integrableOn_logKernel_log {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun u => logKernel v u * Real.log u) (Ioi 0)

/-- The inner `v`-integral of the weighted kernel:
`∫₀^∞ e^{−v} logKernel v u log u dv = (e^{−u} − 1_{u ≤ 1}) log u/u`. -/
theorem integral_exp_kernel_log {u : ℝ} (hu : 0 < u) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-v) * (logKernel v u * Real.log u) =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u

/-- `e^{−v} log² v` is integrable on `(0, ∞)`: `log² v ≤ 16 v^{−1/2} + v²`. -/
theorem integrableOn_exp_neg_log_sq :
    IntegrableOn (fun v : ℝ => Real.exp (-v) * (Real.log v) ^ 2) (Ioi 0)

/-- The weighted kernel `e^{−v} logKernel(v,u) log u` is integrable on `(0,∞)²`. -/
theorem integrable_expKernelLog_prod :
    Integrable (Function.uncurry fun u v : ℝ => Real.exp (-v) * (logKernel v u * Real.log u))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))

/-- `(e^{−u} − 1_{(0,1]}(u)) log u/u` is integrable on `(0, ∞)` (the marginal of the product). -/
theorem integrableOn_renormalised_exp_log :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u)
      (Ioi 0)

/-- ★★ **The weighted renormalised integral**:
`∫₀^∞ (e^{−u} − 1_{(0,1]}(u)) log u/u du = ½ Γ''(1) = ½(γ² + π²/6)`. -/
theorem integral_renormalised_exp_log :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u =
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) / 2

/-- `u⁻¹ log u` is integrable on `(a, b]` for `0 < a ≤ b`. -/
theorem integrableOn_inv_mul_log_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : ℝ => u⁻¹ * Real.log u) (Ioc a b)

/-- `u⁻¹` is integrable on `(a, b]` for `0 < a ≤ b`. -/
theorem integrableOn_inv_Ioc_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u : ℝ => u⁻¹) (Ioc a b)

/-- `∫_{½}^1 du/u = log 2`. -/
theorem integral_Ioc_half_one_inv : ∫ u in Ioc (1 / 2 : ℝ) 1, u⁻¹ = Real.log 2

/-- `∫_{½}^1 log u/u du = −½ (log 2)²`. -/
theorem integral_Ioc_half_one_inv_mul_log :
    ∫ u in Ioc (1 / 2 : ℝ) 1, u⁻¹ * Real.log u = -(Real.log 2) ^ 2 / 2

/-- Pointwise: changing the cutoff from `1` to `½` adds `1_{(½,1]}(u)/u`. -/
theorem half_cut_split_inv {u : ℝ} (hu : 0 < u) :
    (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) / u +
        (Ioc (1 / 2 : ℝ) 1).indicator (fun u => u⁻¹) u

/-- Pointwise: the log-weighted version of `half_cut_split_inv`. -/
theorem half_cut_split_log {u : ℝ} (hu : 0 < u) :
    (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u =
      (Real.exp (-u) - (Ioc 0 1).indicator 1 u) * Real.log u / u +
        (Ioc (1 / 2 : ℝ) 1).indicator (fun u => u⁻¹ * Real.log u) u

/-- Integrability with the cutoff at `½`. -/
theorem integrableOn_renormalised_exp_inv_half :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u) (Ioi 0)

/-- Log-weighted integrability with the cutoff at `½`. -/
theorem integrableOn_renormalised_exp_log_half :
    IntegrableOn (fun u : ℝ => (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u)
      (Ioi 0)

/-- `∫₀^∞ (e^{−u} − 1_{(0,½]}(u))/u du = log 2 − γ`. -/
theorem integral_renormalised_exp_inv_half :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) / u =
      Real.log 2 - Real.eulerMascheroniConstant

/-- `∫₀^∞ (e^{−u} − 1_{(0,½]}(u)) log u/u du = ½(γ² + π²/6) − ½(log 2)²`. -/
theorem integral_renormalised_exp_log_half :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-u) - (Ioc 0 (1 / 2)).indicator 1 u) * Real.log u / u =
      (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) / 2 - (Real.log 2) ^ 2 / 2

/-- `J = ¼ ∫₀^∞ (e^{−y} − 1_{(0,½]}(y)) (log 2 + log y)/y dy`. -/
theorem gaussJlog_eq_half_cut :
    gaussJlog = (∫ y in Ioi (0 : ℝ),
      (Real.exp (-y) - (Ioc 0 (1 / 2)).indicator 1 y) * (Real.log 2 + Real.log y) / y) / 4

/-- ★★★ **The exact logarithmic moment**: `J = R₀²/2 + π²/48` with `R₀ = (log 2 − γ)/2`. -/
theorem gaussJlog_eq : gaussJlog = gaussR₀ ^ 2 / 2 + Real.pi ^ 2 / 48
```

### Grammar/ConeSecondCoefficient.lean
```lean
/-- `|1 − e^{−x} − x| ≤ x²` for `x ≥ 0` (via `e^{−x} ≤ 1/(1+x) ≤ 1 − x + x²`). -/
theorem abs_one_sub_exp_neg_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |1 - Real.exp (-x) - x| ≤ x ^ 2

/-- `∫ |t|³ e^{−t²/2} dt = 4`. -/
theorem integral_cube_abs_mul_exp_neg_half_sq :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 2) = 4

theorem integrable_cube_abs_mul_exp_neg_half_sq :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2))

/-- `|t|³ w_{0,a}` is integrable. -/
theorem integrable_cube_abs_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t))

/-- `∫ |t|³ w_{0,a} ≤ 4 e^{a²/2}(4 + √(2π)|a|³)`. -/
theorem integral_cube_abs_gaussTilt_le (a : ℝ) :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t) ≤
      4 * Real.exp (a ^ 2 / 2) * (4 + Real.sqrt (2 * Real.pi) * |a| ^ 3)

/-- `|P_δ − P_0 + δ Q₁| ≤ δ² M₃`, `Q₁ = ∫ t₊|t| w_{0,a}`, `M₃ = ∫ |t|³ w_{0,a}`. -/
theorem posPart_coneTilt_second_order {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, max t 0 * coneTilt δ a t) - (∫ t, max t 0 * coneTilt 0 a t) +
      δ * ∫ t, max t 0 * |t| * coneTilt 0 a t| ≤
      δ ^ 2 * ∫ t, |t| ^ 3 * Real.exp (-t ^ 2 / 2 + a * t)

/-- `|D_δ − D_0 + δ M₁| ≤ δ² M₂`, `M₁ = ∫ |t| w_{0,a}`, `M₂ = ∫ t² w_{0,a}`. -/
theorem coneTilt_second_order {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    |(∫ t, coneTilt δ a t) - (∫ t, coneTilt 0 a t) +
      δ * ∫ t, |t| * Real.exp (-t ^ 2 / 2 + a * t)| ≤
      δ ^ 2 * ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)

/-- `G(a) = −(Q₁D₀ − P₀M₁)/D₀² = −Cov_{T ∼ N(a,1)}(T₊, |T|)`: the `δ`-derivative of `F_δ(a)`
at `0`. -/
noncomputable def coneCorrectionDeriv (a : ℝ) : ℝ

/-- `2 ≤ √(2π) ≤ 3`. -/
theorem sqrt_two_pi_bounds : 2 ≤ Real.sqrt (2 * Real.pi) ∧ Real.sqrt (2 * Real.pi) ≤ 3

theorem conePosSqMoment_nonneg (a : ℝ) : 0 ≤ ∫ t, max t 0 * |t| * coneTilt 0 a t

/-- `Q₁ ≤ M₂`. -/
theorem conePosSqMoment_le (a : ℝ) :
    ∫ t, max t 0 * |t| * coneTilt 0 a t ≤ ∫ t, t ^ 2 * Real.exp (-t ^ 2 / 2 + a * t)

/-- `|G(a)| ≤ 4(a² + 1)`. -/
theorem abs_coneCorrectionDeriv_le (a : ℝ) : |coneCorrectionDeriv a| ≤ 4 * (a ^ 2 + 1)

/-- The second-order envelope `K(a) = (e^{|a|}/c₀)[6s(a² + 1)(|a| + 1) + 4s|a|³ + 16]`. -/
noncomputable def coneQuadEnvelope (a : ℝ) : ℝ

/-- ★★ **The second-order bound**: `|F_δ(a) − F_0(a) − δ G(a)| ≤ δ² K(a)` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_second_order {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    |coneScaledCorrection δ a - coneScaledCorrection 0 a - δ * coneCorrectionDeriv a| ≤
      δ ^ 2 * coneQuadEnvelope a

def
  clear_value G
  -- the key identity
  have key : Pδ / Dδ - P₀ / D₀ - δ * G =
      G * δ * (D₀ - Dδ) / Dδ +
        ((Pδ - P₀ + δ * Q₁) * D₀ - P₀ * (Dδ - D₀ + δ * M₁)) / (Dδ * D₀)

theorem measurable_coneCorrectionDeriv : Measurable coneCorrectionDeriv

/-- `(a² + 1) γ(a)` is integrable. -/
theorem integrable_sq_add_one_mul_gaussDensity :
    Integrable (fun a : ℝ => (a ^ 2 + 1) * gaussDensity a)

theorem integrable_coneCorrectionDeriv :
    Integrable (fun a : ℝ => coneCorrectionDeriv a * gaussDensity a)

/-- `K(a) γ(a) ≤ 268 e⁴/(√(2π) c₀) e^{−a²/4}`, so it is integrable. -/
theorem integrable_coneQuadEnvelope :
    Integrable (fun a : ℝ => coneQuadEnvelope a * gaussDensity a)

/-- `c₂ = ∫ G(a) γ(a) da`. -/
noncomputable def coneSecondCoeff : ℝ := ∫ a, coneCorrectionDeriv a * gaussDensity a

/-- `C₂ = ∫ K(a) γ(a) da`. -/
noncomputable def coneQuadConst : ℝ := ∫ a, coneQuadEnvelope a * gaussDensity a

/-- The averaged posterior minus its two leading terms is `N^{−1/2} ∫ (F_δ − F_0) γ`,
`δ = N^{−1/2}`. -/
theorem cone_averaged_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    (∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N) =
      1 / Real.sqrt N * ∫ a, (coneScaledCorrection (1 / Real.sqrt N) a -
        coneScaledCorrection 0 a) * gaussDensity a

/-- ★★★ **The second coefficient with a rate**: for `N ≥ 1`,
`|N(E_N − ½ − 1/(√π√N)) − c₂| ≤ C₂/√N`. -/
theorem cone_second_coeff_bound {N : ℝ} (hN : 1 ≤ N) :
    |N * ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N)) - coneSecondCoeff| ≤ coneQuadConst / Real.sqrt N

/-- ★★★ **The second coefficient**: `N(E_N − ½ − 1/(√π√N)) → c₂ = ∫ G γ`. -/
theorem tendsto_cone_second_coeff :
    Tendsto (fun N : ℝ => N * ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2 -
      1 / (Real.sqrt Real.pi * Real.sqrt N))) atTop (𝓝 coneSecondCoeff)
```

## Definitions the cone unit relies on (DCXXIX/DCXXXIII)
```lean
noncomputable def coneTilt (δ a t : ℝ) : ℝ := Real.exp (-t ^ 2 / 2 + a * t - δ * |t|)
noncomputable def coneScaledCorrection (δ a : ℝ) : ℝ :=
  (∫ t, max t 0 * coneTilt δ a t) / ∫ t, coneTilt δ a t
noncomputable def coneC₀ : ℝ := ∫ s : ℝ, Real.exp (-|s| - s ^ 2 / 2)
theorem cone_posterior_ratio_eq {N : ℝ} (hN : 0 < N) (a : ℝ) :
    coneNumSq N a / coneDen N a =
      1 / 2 + 1 / Real.sqrt N * coneScaledCorrection (1 / Real.sqrt N) a
theorem integral_coneScaledCorrection_zero :
    ∫ a, coneScaledCorrection 0 a * gaussDensity a = 1 / Real.sqrt Real.pi
noncomputable def gaussDensity (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)
```
The depth-three constant (DCXXXI): `depthThreeConst = ((3 log 2 − γ) R₀ + 2 J)/π + (2/s) Q`, `s = √(2π)`, `R₀ = (log 2 − γ)/2`, `J = gaussJlog`, `Q = depthThreeQint = ∫₀^∞ q`, `q(v) = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/(s v)`, `c = 3 log 2 − γ`, `Z_2(N) = gaussLaplace2 N = ∫∫ e^{−N x²y²/2} γ(x)γ(y)` (normalised Gaussian prior), with the Bessel form `Z_2(N) = e^{1/4N}K₀(1/4N)/√(2πN)` (DCXXVII) and `|Z_2(N) − (log N + 3 log 2 − γ)/(√(2π)√N)| ≤ (log(2N)+3)/(2N√(2πN))` for `N ≥ ½` (DCXII).

## State of the note (pinned to grammar 4662242)
Formal: §2 Gaussian DLN at every depth: leading, second and third logarithmic coefficients; the depth-three constant as an integral-defined limit with a rate; `J` EXACT (`R₀²/2 + π²/48`), `Γ''(1)`; so `C₃` is explicit up to `Q`. §3 cone: exact Leray closed form; averaged posterior of `u₁²`: `½ + 1/(√π√N) + c₂/N + O(N^{−3/2})` with `c₂ = ∫ G γ` and the `1/√N` rate on the second coefficient. §4 blow-up: tie formulas, Laurent data, two-term Laplace expansion, monomial constant, family theorem with log-free remainder, observable numerators and the posterior ratios `log N·E[y²] → 4`, `√N log N·E[x²] → √(2π)`. §5 rank-one: normal integral and tilt at aligned and general orbit points, invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): `Q = (c² + 5π²/6)/(4s)` (hence `C₃ = ((4 log 2 − 2γ)² + π²)/(4π)` and the closed form of all `C_L`); the constant terms for `L ≥ 4` (need `∫ h log² x/x`, presumably `Γ'''(1)`-type data by the same weighted-kernel route with `log² u`, whose `u`-integral is `⅓ log³ v`); `H₃`, `ζ(3)`; the cone's symmetric form `c₂ = −½∫(a²+1−m(a)²)γ` (odd cancellation of `E_a(T|T|) − a m(a)`) and the value `−5/6 + √3/π` (`E|X||Y| = (2/π)(√(1−ρ²) + ρ arcsin ρ)` at `ρ = ½`); the naive Bayes envelope `M_±(λ)` facewise integrability and joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the blow-up higher poles (`α₁ = √(π/2)/16`); the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; an abstract Mellin transfer theorem.

## Questions
1. Fidelity check (brief) of DCXXXVIII–DCXXXIX against the note's claims and your round-12 specifications; in particular (a) the sign/constant bookkeeping in `gaussJlog_eq_half_cut` and `gaussJlog_eq` (`J = ¼[log 2 (log 2 − γ) + ½(γ² + π²/6) − ½ log² 2]`); (b) `coneCorrectionDeriv` as `−Cov_a(T₊,|T|)` and the statement of `cone_second_coeff_bound` (is `N(E_N − ½ − 1/(√π√N))` the right normalisation, given `cone_posterior_ratio_eq`?); (c) whether `coneQuadEnvelope` and the `268 e⁴` integrability constant hide any error (we bounded `M₁ ≤ E(s|a|+2) ≤ E s(|a|+1)` using `s ≥ 2`, `M₂ ≤ 2sE(a²+1)`, `M₃ ≤ 4E(4 + s|a|³)`, `D_δ ≥ e^{−|a|}E c₀`, `|G| ≤ 4(a²+1)`).
2. Rank the next three day-sized formal targets by value-per-effort with concrete Lean statements and routes. Candidates: (a) the exact `Q`: you sketched `∫₀^∞ v^{z−1} Z_2(v²) dv = 2^{−1−z/2}Γ(z/2)Γ((1−z)/2)²/π` on `0 < z < 1` and the expansion at `z = 1⁻` giving `Q = (c² + 5π²/6)/(4s)` after proving that the pole-subtracted Mellin integral tends to the residual integral `∫₀^∞ q`; which stages are day-sized (the Mellin transform of `Z_2(v²)` as a Beta/Gamma product via the scalar reduction `Z_2(N) = E[(1+N G²)^{−1/2}]`; the pole subtraction `∫ 1_{(1,∞)}(2 log v + c) v^{z−2}/s dv = (2/(s(1−z)²) + c/(s(1−z)))`; the limit `z → 1⁻` of the difference by dominated convergence with the `O(v^{−2})` bound `depthThreeQ_outer_le`; the Gamma jet `Γ(z/2)Γ((1−z)/2)²` to second order at `z = 1`, needing `Γ(½)`, `Γ'(½)`, `Γ''(½)` (DCVIII) and `Γ(ε) = 1/ε − γ + …` i.e. `Γ(1+ε)` to second order — `Γ''(1)` now available)? Give the cleanest decomposition into Lean lemmas. (b) the cone's symmetric form and value: the odd cancellation is elementary (`integral_neg_eq_self`); for `∫ m(a)² γ(a) da = E|A+G₁||A+G₂|` the 2D Gaussian correlated absolute moment — is there a route avoiding polar coordinates (e.g. `E|X||Y| = E[XY sgn(X)sgn(Y)]` and the Gaussian conditional expectation `E[Y | X] = ρX` plus `E|X|·…`? or the identity `E|X||Y| = (2/π)(√(1−ρ²) + ρ arcsin ρ)` via differentiating in `ρ`: `d/dρ E|X||Y| = (2/π) arcsin ρ` from `E[sgn X sgn Y] = (2/π) arcsin ρ` (Sheppard) — which needs Sheppard's formula itself; or a direct polar computation with Mathlib's `integral_comp_polarCoord_symm`), say which is day-sized. (c) the constant terms for `L ≥ 4`: the fourth moment `∫ h log² x/x` via the weighted kernel with `log² u` and `Γ'''(1)` (from duplication thrice? or Mathlib's `Complex.Gamma` Taylor data), and a `FourTermData` propagation — is the constant term of `P_{L−1}` for every `L ≥ 4` day-sized as a recursion, or is the closed-form-via-`Q` route better? (d) the NB face certificate as a generic power/log integrability lemma; (e) the naive Bayes KL-vs-surrogate remainder; (f) the blow-up higher pole `α₁`. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the three new files (the cutoff sets `Ioc 0 1` vs `Ioc 0 (1/2)`; `logKernel v u = 1_{(1,v]}(u)/u − 1_{(v,1]}(u)/u`; `coneCorrectionDeriv` built from `coneTilt 0 a` in three places but `Real.exp (-t^2/2 + a*t)` for `M₁` — same function, different spelling; `coneSecondCoeff` integrates against the normalised `gaussDensity`).
Answer concisely with Lean-facing detail.
