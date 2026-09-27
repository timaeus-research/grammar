You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main c2cc041, 987 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-15 programme is COMPLETE: (1) the log-polynomial Mellin transfer (DCXLIX); (2) the naive-Bayes second log moment `m₂ = √(2π)((γ+log 2)²/4 + π²/8)` via the Gamma log-moments at ½ (DCL); (3) the depth-four constant `D₄` as an integral-defined limit (DCLI) — NOT by extending the DCXXXI decomposition but through the scalar recursion `√N Z₄ = 2∫₀^∞ γ(v/√N) Z₃(v²) dv` and the depth-three RATE: `q₃(v) = Z₃(v²) − 1_{v>1}P₃(2 log v)/v` obeys `|q₃| ≤ 8(1 + 2 log v)/v²`, dominated convergence gives `2∫γ(v/√N)q₃ → (2/s)Q₃`, and the tail `2∫₁^∞ γ(v/√N)P₃(2 log v)/v`, back in `x = v/√N`, splits through `γ = (h + 1_{(0,1]})/s` into the exact flat integral `A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2` and the cutoff `h`-moments `R₀(a), J(a), J₂(a)` (`|∫₀^a h log^j x/x| ≤ (j+1)^j a/2`); `D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]`. The exact remainder identity `sqrt_mul_gaussLaplaceL_four_sub_eq` also re-derives `A₄ = gaussCoeffA 0`, `B₄ = gaussCoeffB 0`, `C₄ = thirdCoeff 0` from the decomposition. Numerics: `J₂ = −0.07627`, `Q₃ = 0.81919`, `D₄ = 0.76540`; direct nested quadrature of `√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ` gives `0.7711, 0.7664, 0.7656, 0.76543` at `N = 10², 10³, 10⁴, 10⁵` (Gauss–Hermite quadrature FAILS here: the integrand `Z₃(Nv²)` has its log-scale structure at `v ∼ N^{−1/2}`; adaptive quadrature split at `1/√N` was needed). The note is pinned to `c2cc041`.

## HEADLINES rows DCXLIX–DCLI
| **DCXLIX** | ★★★ **THE MELLIN TRANSFER FOR A LOG-POLYNOMIAL TAIL: `∫₀^∞ v^{z−1}(q + 1_{v>1}P(log v)/v) − Σ_k p_k k!/(1−z)^{k+1} → ∫₀^∞ q` AS `z → 1⁻` (u985; examples_slop §2, the transfer from an expansion of `Z` in `(log v)^k/v` to the poles of its Mellin transform; Astra round-15 target 1)**: `mellinLogTail` (`if 1 < v then (Σ_k p_k log^k v)/v else 0`), `measurable_mellinLogTail`, `integrableOn_rpow_mul_residual` (`v^{z−1}q` integrable on `(0,∞)` for `a ≤ z ≤ 1`), `rpow_mul_mellinLogTail_eq`, `integral_rpow_mul_mellinLogTail` (`= Σ p_k k!/(1−z)^{k+1}` by DCXLVII), `integrableOn_rpow_mul_mellinLogTail`, ★★★ `tendsto_mellin_sub_logPolynomial` (eventual equality + `tendsto_mellin_residual`). Lean: `integral_finsetSum`/`integrable_finsetSum` need the summand function supplied as `(f := fun k v => …)` when the index is a `Fin` cast to `ℕ` inside; `Integrable.mono'` dominators must be the ABSOLUTE values (`hsmall.abs`). | MellinLogPolynomialTransfer.lean |
| **DCL** | ★★★ **THE GAUSSIAN SECOND LOG MOMENT `m₂ = ∫ e^{−z²/2} log²|z| dz = √(2π)((γ + log 2)²/4 + π²/8)` (u986; examples_slop §6, the naive-Bayes surrogate's `N^{−3/2}log²N` datum; Astra round-15 target 2)**: `integral_Ioi_exp_neg_half_sq_mul_log_sq` (`∫₀^∞ e^{−z²/2}log²z = (1/(4√2))[log²2·H₀ + 2log2·H₁ + H₂]` by `z ↦ z²` (`integral_comp_rpow_Ioi_of_pos`) and `y = 2t` (`integral_comp_mul_left_Ioi`), the Gamma log-moments `H_j = gammaLogMoment j` of `CrossingFlatDepth` (`H₀ = √π`, `H₁ = Γ'(½)`) and DCVIII (`H₂ = Γ''(½)`)), `gaussian_log_abs_sq_even`, ★★★ `integral_gaussian_log_abs_sq` (`integral_comp_abs`; the algebra reduces to `log²2 + 2log2·(−(γ+2log2)) + (γ+2log2)² = (γ+log2)²` and `1/(2√2) = √2/4`). Numerics: quadrature `m₂ = 4.1037415` = formula to 1e−12. Lean: `integral_comp_abs (f := …)` then `simp only [sq_abs] at h` (the `rw` pattern `∫ f |x|` does not match a beta-redex); fold `√2` into an atom and use `T·T = 2` through a scalar `key` identity rather than `linear_combination` on the whole goal. | NaiveBayesLogSqMoment.lean |
| **DCLI** | ★★★ **THE DEPTH-FOUR CONSTANT OF THE GAUSSIAN DLN AS AN INTEGRAL-DEFINED LIMIT: `√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ → D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]` (u987; examples_slop §2, the constant term of `P₃`; Astra round-15 target 3)**: `depthThreeJet` (`P₃(u) = A₃u² + B₃u + C₃`), `depthFourQ` (`q₃(v) = Z₃(v²) − 1_{v>1}P₃(2 log v)/v`), `measurable_gaussLaplaceL_three_sq` (via the scalar recursion and `measurable_gaussLaplace2`), `depthFourQ_outer_le` (`|q₃| ≤ 8(1+2 log v)/v²` from `gaussLaplaceL_three_rate` at `N = v²`), `integrableOn_depthFourQ`, `gaussJlog2` (`J₂ = ∫h log²x/x`), `depthFourQint`, `depthFourConst`; `sqrt_mul_gaussLaplaceL_four_eq` (`√N Z₄ = 2∫γ(v/√N)Z₃(v²)` by the scalar recursion, evenness and `x = v/√N`), `tendsto_depthFourQ_term` (DCT), `depthFourTail`, `sqrt_mul_gaussLaplaceL_four_split`, `tail_integral_eq` (back to `x = v/√N`), `gaussDensity_eq_gaussH`, `depthThreeJet_shift`, `tail_integral_split` (`γ = (h + 1_{(0,1]})/s`), `flat_integral_eq` (FTC: `A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2`), `hpart_integral_eq`, `gaussH_log_pow_cutoff`, `abs_integral_gaussH_log_pow_Ioc_le` (`≤ (j+1)^j a/2`), `tendsto_log_div_sqrt`, `tendsto_sq_log_div_sqrt`, ★★ `sqrt_mul_gaussLaplaceL_four_sub_eq` (the exact remainder identity; the coefficients reproduce `gaussCoeffA 0`, `gaussCoeffB 0`, `thirdCoeff 0` with `s² = 2π`), ★★★ `gaussLaplaceL_four_constant`. No rate is claimed. Route: DCXXXI one order up but through the scalar recursion and the depth-three RATE instead of a bespoke decomposition — the same route gives every depth's constant from the previous depth's rate. Lean gotchas: fold all six integrals and `depthThreeConst` into atoms before `field_simp` (it renormalises integrands); unfold `thirdCoeff` BEFORE `gaussJlog` (it re-exposes it); `← Real.rpow_natCast` must name its base; the assembled `Tendsto` must be stated before `congr'` (the eventual equality needs a concrete target). | GaussianDepthFourConst.lean |

## Public statements of the three new files (docstrings + signatures, proofs omitted)
### Grammar/MellinLogPolynomialTransfer.lean
```lean
/-- The log-polynomial tail `1_{(1,∞)}(v) (Σ_k p_k (log v)^k)/v`. -/
noncomputable def mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) (v : ℝ) : ℝ

theorem measurable_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) :
    Measurable (mellinLogTail p)

/-- The weighted residual `v^{z−1} q` is integrable on `(0,∞)` for `a ≤ z ≤ 1`. -/
theorem integrableOn_rpow_mul_residual {q : ℝ → ℝ} {a z : ℝ} (hq : Measurable q)
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) (hz0 : a ≤ z) (hz1 : z ≤ 1) :
    IntegrableOn (fun v => v ^ (z - 1) * q v) (Ioi 0)

/-- The weighted tail `v^{z−1} · tail` on `(0,∞)` equals the indicator of `(1,∞)` of
`Σ_k p_k v^{z−2}(log v)^k`. -/
theorem rpow_mul_mellinLogTail_eq {d : ℕ} (p : Fin (d + 1) → ℝ) {z v : ℝ} (hv : 0 < v) :
    v ^ (z - 1) * mellinLogTail p v =
      (Ioi (1 : ℝ)).indicator (fun v => ∑ k : Fin (d + 1),
        p k * (v ^ (z - 2) * Real.log v ^ (k : ℕ))) v

/-- `∫₀^∞ v^{z−1} · tail = Σ_k p_k k!/(1−z)^{k+1}` for `z < 1`. -/
theorem integral_rpow_mul_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) {z : ℝ} (hz : z < 1) :
    ∫ v in Ioi (0 : ℝ), v ^ (z - 1) * mellinLogTail p v =
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1)

theorem integrableOn_rpow_mul_mellinLogTail {d : ℕ} (p : Fin (d + 1) → ℝ) {z : ℝ} (hz : z < 1) :
    IntegrableOn (fun v => v ^ (z - 1) * mellinLogTail p v) (Ioi 0)

/-- ★★★ **The Mellin transfer for a log-polynomial tail**: for `Z = q + tail`,
`∫₀^∞ v^{z−1} Z − Σ_k p_k k!/(1−z)^{k+1} → ∫₀^∞ q` as `z → 1⁻`. -/
theorem tendsto_mellin_sub_logPolynomial {d : ℕ} (p : Fin (d + 1) → ℝ) {q : ℝ → ℝ} {a : ℝ}
    (ha : a < 1) (hq : Measurable q)
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q v + mellinLogTail p v)) -
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ v in Ioi (0 : ℝ), q v))
```

### Grammar/NaiveBayesLogSqMoment.lean
```lean
/-- The half-line integral `∫₀^∞ e^{−z²/2} (log z)² dz = (1/(4√2))[log²2 H₀ + 2 log 2 H₁ + H₂]`. -/
theorem integral_Ioi_exp_neg_half_sq_mul_log_sq :
    ∫ z in Ioi (0 : ℝ), Real.exp (-z ^ 2 / 2) * Real.log z ^ 2 =
      1 / (4 * Real.sqrt 2) * (Real.log 2 ^ 2 * gammaLogMoment 0 +
        2 * Real.log 2 * gammaLogMoment 1 + gammaLogMoment 2)

theorem gaussian_log_abs_sq_even (z : ℝ) :
    Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2 =
      (fun t : ℝ => Real.exp (-t ^ 2 / 2) * Real.log t ^ 2) |z|

/-- ★★★ **The Gaussian second log moment**:
`∫ e^{−z²/2} (log |z|)² dz = √(2π)((γ + log 2)²/4 + π²/8)`. -/
theorem integral_gaussian_log_abs_sq :
    ∫ z : ℝ, Real.exp (-z ^ 2 / 2) * Real.log |z| ^ 2 =
      Real.sqrt (2 * Real.pi) *
        ((Real.eulerMascheroniConstant + Real.log 2) ^ 2 / 4 + Real.pi ^ 2 / 8)
```

### Grammar/GaussianDepthFourConst.lean
```lean
/-- The depth-three jet `P₃(u) = A₃u² + B₃u + C₃`. -/
noncomputable def depthThreeJet (u : ℝ) : ℝ

/-- `q₃(v) = Z₃(v²) − 1_{(1,∞)}(v) P₃(2 log v)/v`. -/
noncomputable def depthFourQ (v : ℝ) : ℝ

theorem measurable_gaussLaplaceL_three_sq : Measurable fun v : ℝ => gaussLaplaceL 3 (v ^ 2)

theorem measurable_depthFourQ : Measurable depthFourQ

theorem depthFourQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthFourQ v = gaussLaplaceL 3 (v ^ 2)

/-- On `(1,∞)`: `|q₃(v)| ≤ 8(1 + 2 log v)/v²` from the depth-three rate at `N = v²`. -/
theorem depthFourQ_outer_le {v : ℝ} (hv : 1 < v) :
    |depthFourQ v| ≤ 8 * (1 + 2 * Real.log v) / v ^ 2

theorem integrableOn_depthFourQ_inner : IntegrableOn depthFourQ (Ioc 0 1)

theorem integrableOn_depthFourQ_outer : IntegrableOn depthFourQ (Ioi 1)

theorem integrableOn_depthFourQ : IntegrableOn depthFourQ (Ioi 0)

/-- `J₂ = ∫₀^∞ h(x) log²x/x dx`. -/
noncomputable def gaussJlog2 : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ 2 / x

/-- `Q₃ = ∫₀^∞ q₃`. -/
noncomputable def depthFourQint : ℝ := ∫ v in Ioi (0 : ℝ), depthFourQ v

/-- The depth-four constant `D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]`. -/
noncomputable def depthFourConst : ℝ

theorem integrable_gaussDensity_mul_gaussLaplaceL_three {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL 3 (N * x ^ 2))

/-- `√N Z₄(N) = 2 ∫₀^∞ γ(v/√N) Z₃(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_four_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 4 N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL 3 (v ^ 2)

theorem gaussDensity_le_inv_sqrt (x : ℝ) : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi)

theorem tendsto_depthFourQ_term :
    Tendsto (fun N : ℝ => 2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v)
      atTop (𝓝 (2 / Real.sqrt (2 * Real.pi) * depthFourQint))

/-- The tail integrand. -/
noncomputable def depthFourTail (v : ℝ) : ℝ

theorem depthFourQ_add_tail (v : ℝ) : depthFourQ v + depthFourTail v = gaussLaplaceL 3 (v ^ 2)

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL 3 (v ^ 2))
      (Ioi 0)

theorem integrableOn_gaussDensity_div_mul_depthFourQ {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * depthFourQ v) (Ioi 0)

/-- `√N Z₄ = 2∫ γ(v/√N) q₃ + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_four_split {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL 4 N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourTail v

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P₃(ℓ + 2 log x)/x dx`,
`a = N^{−1/2}`, `ℓ = log N`. -/
theorem tail_integral_eq {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourTail v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x

theorem gaussDensity_eq_gaussH (x : ℝ) :
    gaussDensity x = (gaussH x + (Ioc (0 : ℝ) 1).indicator 1 x) / Real.sqrt (2 * Real.pi)

/-- The jet evaluated at `ℓ + 2 log x`, as a polynomial in `log x`. -/
theorem depthThreeJet_shift (ℓ y : ℝ) :
    depthThreeJet (ℓ + 2 * y) = (ℓ ^ 2 / (4 * Real.pi) +
      (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * ℓ + depthThreeConst) +
      (4 * ℓ / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) * y +
      4 * (1 / (4 * Real.pi)) * y ^ 2

theorem integrableOn_gaussH_jet {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N))

theorem integrableOn_jet_div_Ioc {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => depthThreeJet (Real.log N + 2 * Real.log x) / x)
      (Ioc (1 / Real.sqrt N) 1)

/-- The tail splits into the flat part and the `h`-part. -/
theorem tail_integral_split {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeJet (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x)

/-- The flat part exactly: `∫_a^1 P₃(ℓ + 2 log x)/x = A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2`. -/
theorem flat_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeJet (Real.log N + 2 * Real.log x) / x =
      1 / (4 * Real.pi) * (Real.log N) ^ 3 / 6 +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * (Real.log N) ^ 2 / 4 +
        depthThreeConst * Real.log N / 2

/-- The cutoff `h`-moments `R(a) = ∫_a^∞ h/x`, `J(a) = ∫_a^∞ h log x/x`,
`J₂(a) = ∫_a^∞ h log²x/x`. -/
theorem hpart_integral_eq {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * depthThreeJet (Real.log N + 2 * Real.log x) / x =
      ((Real.log N) ^ 2 / (4 * Real.pi) +
        (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N + depthThreeConst) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x / x) +
      (4 * Real.log N / (4 * Real.pi) +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
        (∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) +
      4 * (1 / (4 * Real.pi)) * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x

/-- `∫_a^∞ h log^j x/x = ∫₀^∞ h log^j x/x − ∫₀^a h log^j x/x`. -/
theorem gaussH_log_pow_cutoff (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ x in Ioi a, gaussH x * Real.log x ^ j / x =
      (∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ j / x) -
        ∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x

/-- `|∫₀^a h log^j x/x| ≤ (j+1)^j a/2` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_log_pow_Ioc_le (j : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤ (j + 1) ^ j / 2 * a

theorem tendsto_log_div_sqrt : Tendsto (fun N : ℝ => Real.log N / Real.sqrt N) atTop (𝓝 0)

theorem tendsto_sq_log_div_sqrt :
    Tendsto (fun N : ℝ => (Real.log N) ^ 2 / Real.sqrt N) atTop (𝓝 0)

/-- The assembled remainder: for `N ≥ 1`,
`√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ = 2∫γ(v/√N)q₃ + (2/s)[c₀ε₀ + c₁ε₁ + c₂(J₂ − ε₂) + C₃R₀ + 2B₃J]`. -/
theorem sqrt_mul_gaussLaplaceL_four_sub_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
      gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) +
      2 / Real.sqrt (2 * Real.pi) *
        (((Real.log N) ^ 2 / (4 * Real.pi) +
          (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi * Real.log N +
            depthThreeConst) * (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        (4 * Real.log N / (4 * Real.pi) +
          2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi)) *
          (-∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x / x) +
        4 * (1 / (4 * Real.pi)) *
          (gaussJlog2 - ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ 2 / x) +
        depthThreeConst * gaussR₀ +
        2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi) * gaussJlog)

/-- ★★★ **The depth-four constant**: `√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ → D₄`. -/
theorem gaussLaplaceL_four_constant :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
      gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N) atTop (𝓝 depthFourConst)
```

## State of the note (pinned to grammar c2cc041)
Formal: §2 Gaussian DLN: `A_L`, `B_L`, `C_L` explicit at every depth; the depth-three constant exact (`C₃ = ((4log2−2γ)²+π²)/(4π)`); the depth-four constant `D₄` as an integral-defined limit; `J`, `Q`, `Γ''(1)`, the Mellin transform of `Z₂` closed with residual bridge, jet, the abstract transfer lemma and its log-polynomial form; depth-two two-term expansion, Bessel form, crossing corollary; DLN flat prior at every depth. §3 cone: exact Leray closed form; averaged posterior `½ + 1/(√π√N) + (−5/6 + √3/π)/N + O(N^{−3/2})` with the `1/√N` rate on `c₂`. §4 blow-up: tie formulas, Laurent data, two-term Laplace expansion with explicit remainder, monomial constant, family theorem with log-free remainder, observable numerators and posterior ratios. §5 rank-one: normal integral and tilt at aligned and general orbit points, invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter, the generic power/log certificate, `m₂`.
Derivation-only (checked numerically): the values `J₂ = ∫h log²x/x = −0.07627` (needs `Γ'''(1)`, i.e. `ζ(3)`), `Q₃ = 0.81919`, and the identification of `D₄ = 0.76540` with the `ε³` coefficient of the Mellin jet; a RATE at depth four; the constants for `L ≥ 5`; the naive-Bayes envelope exponents per face after the chart Jacobian, joint measurability of the fibre family, KL-vs-surrogate remainder; the blow-up `N^{−3/2} log N` coefficient `√(π/2)/16` (your correction noted); the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; the cone's third coefficient (`≈ 0.0698`).

## Questions
1. Fidelity check (brief) of DCXLIX–DCLI against the note's claims and your round-15 specifications; in particular (a) `mellinLogTail` and the sign/indexing of `Σ p_k k!/(1−z)^{k+1}`; (b) DCL's `1/(2√2)` bookkeeping (`m₂ = (√2/4)[log²2·Γ(½) + 2 log 2·Γ'(½) + Γ''(½)]`) and the final constant; (c) DCLI: is `depthFourConst` the correct constant (please re-derive `D₄ = (2/s)[4A₃J₂ + 2B₃J + C₃R₀ + Q₃]` independently from `√N Z₄ = 2∫γ(v/√N)Z₃(v²)` and the depth-three jet, and confirm the flat part `∫_a^1 P₃(ℓ + 2 log x)/x = A₃ℓ³/6 + B₃ℓ²/4 + C₃ℓ/2` and the `h`-part's coefficients `c₀ = A₃ℓ² + B₃ℓ + C₃`, `c₁ = 4A₃ℓ + 2B₃`, `c₂ = 4A₃`), and that the `(j+1)^j a/2` cutoff bound is enough (it gives `ℓ²·a/2 = ℓ²/(2√N) → 0`, weaker than DCXXXI's `a²/2` but sufficient); (d) whether the numerical `D₄ = 0.7654` is consistent with the Mellin jet: the `ε³` coefficient of `Γ(½−ε)2^{3ε}Γ(1+ε)⁴` normalised as for `C_L` — please compute the jet prediction for `D₄` in closed form (it should involve `ζ(3)` through `Γ'''(1) = −γ³ − γπ²/2 − 2ζ(3)` and `Γ'''(½)`) and evaluate it numerically to compare with `0.7654`.
2. Rank the next three day-sized formal targets by value-per-effort with concrete Lean statements and routes. Candidates: (a) a RATE at depth four: the DCT step needs `|2∫(γ(v/√N) − γ(0))q₃|`; with `|γ(v/√N) − γ(0)| ≤ v²/(2sN)` (DCXXXIV's `abs_gaussDensity_sub_le`) the integral `∫ v²|q₃|` diverges (`|q₃| ∼ log v/v²`), so a split at `v = √N` or a better bound is needed — what is the honest rate (`O(log²N/√N)`?) and the day-sized statement?; (b) the all-depth constant as a recursion `D_{L+1} = f(D_L, C_L, B_L, A_L; R₀, J, J₂, Q_L)` — DCLI's route uses the depth-`L` RATE, so propagating needs rates at every depth; is a `FourTermData`-style engine (four-term jet with error `D(1+ℓ)^m/√t`) the right abstraction, and is its step day-sized given DCXXXV's `threeTermStep_bound` as a template?; (c) `J₂` exact: `∫h log²x/x` via the weighted kernel with `log²u` (`∫logKernel(v,u)log²u du = ⅓log³v`) gives `∫₀^∞(e^{−u} − 1_{(0,1]})log²u/u = ⅓Γ'''(1)`?? (check: at depth one the kernel gave `Γ'(1)`, with `log u` it gave `½Γ''(1)`; with `log²u` it gives `⅓∫e^{−v}log³v = ⅓Γ'''(1)`) — is `Γ'''(1)` reachable (Mathlib has `Complex.Gamma` analytic; `ζ(3)` appears only through the digamma/polygamma values; is there a Mathlib statement of `ψ''(1) = −2ζ(3)`? if not, `J₂` should stay integral-defined); (d) the cone `c₃` as a limit with the halved second derivative; (e) the naive-Bayes joint measurability given an explicit fixed-domain integral representation of the fibre density (`eq:nb_rho_integral` in the note: `ρ(λ,μ) = ∫₀¹ dt/(t(1−t)) h_t(μ/(t(1−t)))`); (f) polish: `tendsto_mellin_residual` with `AEStronglyMeasurable q`, the cube-set and a.e. domination adapters for the certificate, the user-facing corollary rewriting `gaussLaplaceL_third_coeff` to `thirdCoeffClosed`. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the three new files (`depthThreeJet` vs `thirdCoeffClosed` naming; `gaussJlog2` named like `gaussJlog` (both integral-defined, only `J` exact); `depthFourQ` vs `depthThreeQ` indexing by the depth of `Z`; `depthFourTail` as an `indicator`; `mellinLogTail` as an `if`).
Answer concisely with Lean-facing detail.
