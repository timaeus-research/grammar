You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 8484d83, 1006 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-21 programme is COMPLETE and exceeded: the `J_k` BRIDGE for all `k` (DCLXVIII: `G_r = ∫₀^∞ e^{−u} log^r u`, integrability, split IBP `∫(e^{−u} − 1_{(0,1]}) log^r u/u = G_{r+1}/(r+1)`, `G₀,G₁,G₂ = 1, −γ, γ²+π²/6` by comparing `r = 0,1` with DCXI/DCXXXVIII; DCLXIX: `J_k = 2^{−(k+1)}[Σ_r C(k,r) log^{k−r}2 · G_{r+1}/(r+1) + log^{k+1}2/(k+1)]` with the regressions `J₀ = R₀`, `J₁ = R₀²/2 + π²/48` and `J₂, J₃` explicit in `G₃, G₄`), and then the GENERAL-DEPTH MELLIN CLOSED FORM with the finite-part identification of every residual mass (DCLXX): `M_{L+1}(z) = (2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1}/(2√π^{L+1})` for `0 < z < 1`, and `M_L(z) − Σ_{k<L} 2^k k! a_k/(1−z)^{k+1} → Q_L = residualMass L (enginePoly L)` as `z → 1⁻` (DCXLIX's transfer + the engine's residual + the rate-based integrability of `v^{z−1}Z_L(v²)`). NUMERICS: `gauss_jlog_bridge_check.py` (bridge to 12 digits; `G_r = Γ^{(r)}(1)` and `G₃ = −γ³ − γπ²/2 − 2ζ(3)`, `G₄ = γ⁴ + γ²π² + 8γζ(3) + 3π⁴/20` to 12 digits); `gauss_mellin_finite_part_check.py` (finite part at `z = 1 − 10⁻⁷` recovers `Q₂..Q₅ = 1.045364, 0.819187, 1.042299, 0.876664`; `Q₂` = DCXLV's closed form).

So: every coefficient of every `enginePoly L` is now formally the finite part of an explicit Gamma product, and the only missing formal step to CLOSED ζ-forms is the LAURENT JET of `F_L(u) := (2^{−(1−2u)/2})^{L−1} Γ((1−2u)/2) Γ(u)^L /(2√π^L)` at `u = 0` (`z = 1 − 2u`) to order `L`, i.e. the Taylor coefficients of `Γ(½ − u)`, `Γ(1+u)^L`, `2^{(L−1)u}` up to `u^{L}` — which involve `Γ^{(k)}(½)`, `Γ^{(k)}(1)` for `k ≤ L` (DCXLIII did `L = 2` by l'Hôpital twice with `Γ', Γ''` at `½` and `1`).

## HEADLINES rows DCLXVIII–DCLXX
| **DCLXVIII** | ★★ **THE LOG MOMENTS OF `e^{−u}` AT `Γ(1)` AND THE RENORMALISED INTEGRALS FOR EVERY POWER (u1004; Astra round 21, the `J_k` bridge stage 1)**: `gammaOneLogMoment r = ∫₀^∞ e^{−u} log^r u` (`G_r`, formally `Γ^{(r)}(1)`, not identified); ★★ `integrableOn_exp_neg_mul_log_pow` (every `r`: DCXLVIII's `(1+|log u|)^r` certificate on `(0,1]`, `log u ≤ u` against `u^r e^{−u}` beyond), `integrableOn_renormalised_log_pow` (`|e^{−u} − 1| ≤ u`); `tendsto_mul_log_pow_nhdsGT_zero` (`u log^m u → 0`), `tendsto_exp_neg_mul_log_pow_atTop`; the primitives `hasDerivAt_inner/outer_primitive` (`F₋ = (e^{−u}−1) log^{r+1}u/(r+1)`, `F₊ = e^{−u} log^{r+1}u/(r+1)`); ★★ `integral_renormalised_exp_log_pow (r) : ∫₀^∞ (e^{−u} − 1_{(0,1]}) log^r u/u = G_{r+1}/(r+1)` (split IBP: `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` on `(0,1)`, `integral_Ioi_of_hasDerivAt_of_tendsto` on `(1,∞)`); `gammaOneLogMoment_zero/one/two = 1, −γ, γ² + π²/6` by comparing `r = 0, 1` with DCXI/DCXXXVIII (no new differentiation under the integral). | GammaOneLogMoments.lean |
| **DCLXIX** | ★★★ **THE GAUSSIAN LOG MOMENTS THROUGH THE GAMMA LOG MOMENTS (u1005; Astra round 21, the `J_k` bridge stage 2)**: `gaussJlogPow_eq_half_cut (k) : J_k = 2^{−(k+1)} ∫₀^∞ (e^{−y} − 1_{(0,½]}) (log 2 + log y)^k/y` (substitution `x² = 2y`, DCXXXVIII's route for every power); `half_cut_split_pow`, `unit_cut_binomial` (`add_pow`), `integrableOn_unit_cut_pow`, `integral_unit_cut_pow` (binomial expansion against DCLXVIII), `integral_log_two_add_log_pow_div : ∫_{½}^1 (log 2 + log y)^k/y = log^{k+1}2/(k+1)` (FTC); ★★★ `gaussJlogPow_eq_gammaOneLogMoment (k) : J_k = 2^{−(k+1)}[Σ_{r ≤ k} C(k,r) log^{k−r}2 · G_{r+1}/(r+1) + log^{k+1}2/(k+1)]` for EVERY `k`; regressions `gaussJlogPow_zero_eq = (log 2 − γ)/2`, `gaussJlogPow_one_eq = R₀²/2 + π²/48` (recovering DCXXVI's `R₀` and DCXXXVIII's `J`); ★★ `gaussJlog2_eq_gammaOneLogMoment`, `gaussJlog3_eq_gammaOneLogMoment` (`J₂`, `J₃` explicit in `G₃`, `G₄`): every lower coefficient of `enginePoly L` is a polynomial in `log 2, γ, π², G₃, G₄, …` and the residual masses. Numerics `gauss_jlog_bridge_check.py` (bridge to 12 digits, `G_r = Γ^{(r)}(1)` and their ζ-closed forms to 12 digits). | GaussJlogPowBridge.lean |
| **DCLXX** | ★★★ **THE MELLIN TRANSFORM AT EVERY DEPTH AND THE RESIDUAL MASSES AS FINITE PARTS (u1006; Astra round 21)**: `depthMellin L z = ∫₀^∞ v^{z−1} Z_L(v²)`; ★★ `integrableOn_rpow_mul_gaussLaplaceL_sq` (`0 < z < 1`, `L ≥ 2`; `gaussLaplaceL_sq_le_of_hasPolyRate : Z_L(v²) ≤ C(1+2 log v)^{deg+1}/v` from the engine's rate, `integrableOn_rpow_mul_one_add_log_pow`); the joint integrand `mellinIntegrand` (Fubini via `integrable_prod_iff`, `gaussLaplaceL_succ`), `ae_prod_ne_zero` (`Measure.ae_eval_ne`); ★★★ `depthMellin_succ_eq : M_{L+1}(z) = (2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1}/(2√π^{L+1})` for `0 < z < 1`, `L ≥ 1` (`integral_rpow_div_sqrt_one_add_mul_sq` per fibre, `integral_fintype_prod_eq_pow`, DCXLIV's negative moment; DCXLIV is `L = 1`: `depthMellin_two_eq`); `polyTail_eq_mellinLogTail` (engine tail = DCXLIX's log-polynomial tail with `p_k = 2^k a_k`); ★★★ `tendsto_depthMellin_sub_poles : M_L(z) − Σ_{k<L} 2^k k! a_k/(1−z)^{k+1} → Q_L = residualMass L (enginePoly L)` as `z → 1⁻` (`L ≥ 2`; DCXLIX transfer with `a = ½`), ★★★ `tendsto_gammaProduct_sub_poles` (the same in the closed form): every residual mass is the finite part of an explicit Gamma product at its pole; the Laurent jet to order `L` is what remains (`ζ(3)` at depth three). | DepthMellinClosedForm.lean |

## Public statements of DCLXX
```lean
/-- `M_L(z) = ∫₀^∞ v^{z−1} Z_L(v²) dv`. -/
noncomputable def depthMellin (L : ℕ) (z : ℝ) : ℝ

theorem depthMellin_two (z : ℝ) : depthMellin 2 z = depthThreeMellin z

theorem integrableOn_rpow_mul_gaussLaplaceL_sq_inner (L : ℕ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioc 0 1)

/-- Beyond `1`, `Z_L(v²) ≤ C(1 + 2 log v)^{deg P + 1}/v` from a rate with polynomial `P`. -/
theorem gaussLaplaceL_sq_le_of_hasPolyRate {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 1 ≤ v →
      gaussLaplaceL L (v ^ 2) ≤ C * (1 + 2 * Real.log v) ^ (P.natDegree + 1) / v

theorem integrableOn_rpow_mul_one_add_log_pow (d : ℕ) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 2) * (1 + 2 * Real.log v) ^ d) (Ioi 1)

theorem integrableOn_rpow_mul_gaussLaplaceL_sq_outer (L : ℕ) (hL : 2 ≤ L) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioi 1)

/-- ★★ `v^{z−1} Z_L(v²)` is integrable on `(0,∞)` for `0 < z < 1`, `L ≥ 2`. -/
theorem integrableOn_rpow_mul_gaussLaplaceL_sq (L : ℕ) (hL : 2 ≤ L) {z : ℝ} (hz0 : 0 < z)
    (hz1 : z < 1) :
    IntegrableOn (fun v : ℝ => v ^ (z - 1) * gaussLaplaceL L (v ^ 2)) (Ioi 0)

/-- The Mellin integrand at depth `L + 1`, `(v, b) ↦ v^{z−1}(1 + v²(∏b)²)^{−1/2} ∏γ(bᵢ)`. -/
noncomputable def mellinIntegrand (L : ℕ) (z : ℝ) (v : ℝ) (b : Fin L → ℝ) : ℝ

theorem measurable_uncurry_mellinIntegrand (L : ℕ) (z : ℝ) :
    Measurable (Function.uncurry (mellinIntegrand L z))

theorem mellinIntegrand_nonneg (L : ℕ) (z : ℝ) {v : ℝ} (hv : 0 < v) (b : Fin L → ℝ) :
    0 ≤ mellinIntegrand L z v b

theorem integrable_mellinIntegrand (L : ℕ) (hL : 1 ≤ L) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Integrable (Function.uncurry (mellinIntegrand L z))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)

/-- Almost every `b` has `∏ bᵢ ≠ 0`. -/
theorem ae_prod_ne_zero (L : ℕ) : ∀ᵐ b : Fin L → ℝ, ∏ i, b i ≠ 0

/-- ★★★ **The closed form at every depth**:
`M_{L+1}(z) = (2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1} / (2√π^{L+1})` for `0 < z < 1`, `L ≥ 1`. -/
theorem depthMellin_succ_eq (L : ℕ) (hL : 1 ≤ L) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthMellin (L + 1) z = ((2 : ℝ) ^ (-z / 2)) ^ L * Real.Gamma (z / 2) *
      Real.Gamma ((1 - z) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1))

/-- Consistency with DCXLIV at `L = 1`. -/
theorem depthMellin_two_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    depthMellin 2 z =
      (2 : ℝ) ^ (-1 - z / 2) * Real.Gamma (z / 2) * Real.Gamma ((1 - z) / 2) ^ 2 / Real.pi

/-- The engine's tail is DCXLIX's log-polynomial tail with coefficients `2^k a_k`. -/
theorem polyTail_eq_mellinLogTail (P : ℝ[X]) :
    polyTail P = mellinLogTail (fun k : Fin (P.natDegree + 1) => 2 ^ (k : ℕ) * P.coeff k)

/-- ★★★ **The residual mass is the finite part of the Mellin transform at `z = 1`**: for `L ≥ 2`,
`M_L(z) − Σ_{k ≤ L−1} 2^k a_k k!/(1−z)^{k+1} → Q_L` as `z → 1⁻`, `a_k = (enginePoly L)_k`. -/
theorem tendsto_depthMellin_sub_poles (L : ℕ) (hL : 2 ≤ L) :
    Tendsto (fun z : ℝ => depthMellin L z -
      ∑ k : Fin ((enginePoly L).natDegree + 1), (2 ^ (k : ℕ) * (enginePoly L).coeff k) *
        ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (residualMass L (enginePoly L)))

/-- ★★★ The finite part of the Gamma product: for `L ≥ 1`,
`(2^{−z/2})^L Γ(z/2) Γ((1−z)/2)^{L+1}/(2√π^{L+1}) − Σ_k 2^k a_k k!/(1−z)^{k+1} → Q_{L+1}`. -/
theorem tendsto_gammaProduct_sub_poles (L : ℕ) (hL : 1 ≤ L) :
    Tendsto (fun z : ℝ => ((2 : ℝ) ^ (-z / 2)) ^ L * Real.Gamma (z / 2) *
      Real.Gamma ((1 - z) / 2) ^ (L + 1) / (2 * Real.sqrt Real.pi ^ (L + 1)) -
      ∑ k : Fin ((enginePoly (L + 1)).natDegree + 1),
        (2 ^ (k : ℕ) * (enginePoly (L + 1)).coeff k) *
          ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (residualMass (L + 1) (enginePoly (L + 1))))
```

## Questions
1. Fidelity check (brief) of DCLXVIII–DCLXX: (a) the bridge formula and the `G_r` regressions; (b) the closed form's prefactor `(2^{−z/2})^L … /(2√π^{L+1})` at `L = 1` against DCXLIV's `2^{−1−z/2}ΓΓ²/π`; (c) the finite-part statement's pole sum `Σ_{k : Fin (natDegree+1)} 2^k a_k k!/(1−z)^{k+1}` (with DCXLVII's `∫₁^∞ v^{z−2} log^k v = k!/(1−z)^{k+1}`) and the transfer hypotheses (`a = ½`: `v^{−1/2}q` integrable on `(0,1]` since `|q| ≤ 1`).
2. THE JET. Design the Lean route to the depth-three constant `Q₃` (hence `D₄`) in closed form. Options: (A) a SYMBOLIC jet: define the Taylor coefficients of `u ↦ Γ(½ − u)` and `u ↦ Γ(1 + u)` at `0` as `iteratedDeriv k Real.Gamma (1/2)`/`(1)` (or via `Complex.Gamma`'s analyticity: `Complex.differentiableAt_Gamma`, is there `AnalyticAt ℂ Complex.Gamma` / `HasFPowerSeriesAt` on the pin?), prove the third-order Taylor expansion with remainder `o(u³)` from `ContDiff`/`taylor_mean_remainder` (is `ContDiff ℝ ⊤ Real.Gamma` on `(0,∞)` available? `Real.differentiable_Gamma`? `Real.contDiffAt_Gamma`?), multiply the three expansions (`Γ(½−u)·Γ(1+u)³·2^{2u}`), extract `[u³]`, and state `Q₃ = (2/s)·(jet coefficient)` — the ζ(3) identification of `Γ'''(1)`, `Γ'''(½)` left as derivation; (B) l'Hôpital thrice as in DCXLIII (`tendsto_gammaJetF_second`): `(F(u) − 1 − c₁u − c₂u²)/u³ → c₃` from `HasDerivAt` of the jet function to third order — needs the third derivative of `Γ` at `½` and `1` as explicit values or symbols; (C) via the engine: `Q₃` is already determined by `D₄ = (enginePoly 4)₀ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]` and `J₂` is now explicit in `G₃`; so a closed `D₄` needs exactly `Q₃`; conversely the finite part gives `Q₃` from the jet. Which of (A)/(B) is day-sized on the pin, and what are the exact Mathlib names for `Real.Gamma` smoothness (`Real.Gamma` is `ContDiff`? `Real.hasDerivAt_Gamma`? `Complex.hasDerivAt_Gamma`?) and for Taylor expansions with Peano remainder (`taylor_isLittleO`, `HasFTaylorSeriesUpTo`, or `Polynomial.taylor`-free `Filter.IsLittleO` statements like `Real.exp_sub_sum_range_isLittleO`)? Please give the cleanest interface, e.g. `theorem tendsto_depthThreeJet_third : Tendsto (fun u => (F₃(u) − 1 − c₁u − c₂u²)/u³) (𝓝[>] 0) (𝓝 c₃)` with `c₃` a named real defined from `iteratedDeriv`, and the corollary `depthFourQint_eq_jet : Q₃ = (2/s)·c₃`-type statement — check the normalisation (`F_L` vs `M_L`: `M_L(1−2u) = F_L(u)/(2 s u^L)`?).
3. Alternatively, rank against the jet: (a) the general Laurent expansion machinery (`Γ(u)^L = u^{−L}Γ(1+u)^L`, `Γ(1+u) = exp(−γu + Σ_{k≥2} (−1)^k ζ(k) u^k/k)` — the EXPONENTIAL form is exactly the generating function Astra gave in round 18; is Mathlib's `Real.Gamma`/`Complex.Gamma` log-derivative (digamma) or the Weierstrass product available? `Real.Gamma_seq_tendsto_Gamma`, `Complex.GammaSeq`? — a formal `Γ(1+u) = exp(−γu + Σ ζ(k)(−u)^k/k)` on `|u| < 1` would close EVERY depth's constants in ζ-values; honest size?); (b) the naive-Bayes surrogate posterior ratio; (c) cone `c₃`; (d) the blow-up `N^{−3/2} log N`.
Answer concisely with Lean-facing detail.
