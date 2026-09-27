You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 19f0430, 1000 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). THE ALL-DEPTH ENGINE IS DONE (your rounds 18–19 design, three units): DCLXII the polynomial tools (Hasse–Taylor, `primZero`, the general flat integral, coefficient bound, absorption), DCLXIII `HasPolyRate.step` for EVERY depth and EVERY `P : Polynomial ℝ` with no degree hypothesis, DCLXIV the all-depth theorem `hasPolyRate_enginePoly : ∀ L ≥ 2, HasPolyRate L (enginePoly L)` by iteration from the depth-two base case, and the acceptance tests `stepPoly P₂ Q₂ = P₃`, `stepPoly P₃ Q₃ = P₄`, `stepPoly P₄ Q₄ = P₅` as polynomial identities. Also DCLXI (your round-19 top choice): the conditional density `p_λ = ρ/m(λ)` as a probability measure, positivity set = punctured interval, and the exact conditional mean `E[μ|λ] = [M₊²(A₊+1) − M₋²(A₋+1)]/(2m(λ))`.

NUMERICS (`gauss_depth_engine_check.py`): iterating the step numerically from `P₂` with `Q₂..Q₆ = 1.04536, 0.81918, 1.04231, 0.87663, 1.04386` reproduces EVERY coefficient of the Mellin jet `2^{−(L−1)/2}π^{−L/2} Σ_k g_k ℓ^{L−1−k}/(L−1−k)!` through `L = 7` (max discrepancy `2e−7` at `L=3` growing to `6e−5` at `L=7`, accumulated quadrature error), and `√N Z_L − P_L(ℓ) < 1e−5` at `N = 10⁶` for every `L ≤ 7`.

## HEADLINES rows DCLXI–DCLXIV
| **DCLXI** | ★★★ **THE CONDITIONAL DENSITY OF THE COVARIANCE GIVEN THE MEANS (u997; Astra round-19 target 1)**: `nbClosed_pos`; ★★ `nbFibreDensity_pos_iff : 0 < ρ(λ,z) ↔ −M₋ < z < M₊ ∧ z ≠ 0` (positivity set = punctured interval; topological support `[−M₋, M₊]`); `nbFibreMass_pos`; `nbConditionalDensity = ρ/ofReal m(λ)`, ★★ `lintegral_nbConditionalDensity = 1`, `nbConditionalMeasure = volume.withDensity p_λ`, ★★ `isProbabilityMeasure_nbConditionalMeasure`; the first moment of the closed piece `integral_mul_nbClosed : ∫₀^M z·nbClosed = M²(log(V/M²)+1)/2` (antiderivative `z²[(c₁−L)(c₂−L) + (c₁+c₂−2L)/2 + ½]`), reflected `integral_mul_nbClosed_neg`; real decomposition `nbFixedDensity_eq_indicator`; ★★★ `integral_mul_nbFixedDensity : ∫ z ρ(λ,z) dz = [M₊²(A₊+1) − M₋²(A₋+1)]/2`, `A± = log(V/M±²)`; `nbConditionalMean = that/(2m(λ))`, `integral_nbConditionalMean`. NOT the surrogate posterior mean of eq. nb_postmu (likelihood weight). | NaiveBayesConditionalDensity.lean |
| **DCLXII** | ★★ **POLYNOMIAL TOOLS FOR THE ALL-DEPTH ENGINE (u998; Astra round 19, engine stage A)**: `eval_add_eq_sum_hasseDeriv : P(x+y) = Σ_{j ≤ deg P} (H_jP)(x) y^j` (Mathlib `taylor_eval`/`taylor_coeff`); `primZero` with `derivative_primZero`, `eval_primZero_zero`; `hasDerivAt_eval_log`; ★★ `integral_eval_log_div : ∫_a^1 P(ℓ + 2 log x)/x = [(primZero P)(ℓ) − (primZero P)(ℓ + 2 log a)]/2`; `abs_eval_le : |Q(ℓ)| ≤ (Σ_{i≤d}|coeff_i|)(1+ℓ)^d`; `log_le_rpow_div : log N ≤ N^ε/ε`; `exists_one_add_log_pow_le : (1+ℓ)^d ≤ C N^{1/4}`; ★★ absorption `exists_log_pow_cutoff_constant : (1+ℓ)^d N^{−3/4} ≤ C(1+ℓ)/√N`; `one_div_sqrt_mul_sqrt : a√a = N^{−3/4}`. | PolynomialJetTools.lean |
| **DCLXIII** | ★★★ **THE ALL-DEPTH ENGINE: THE DEPTH STEP WITH THE LINEAR-LOG RATE (u999; Astra rounds 18–19, engine stage B)**: `polyResidual L P v = Z_L(v²) − 1_{v>1}P(2 log v)/v`, `residualMass L P = ∫₀^∞ polyResidual`, `HasPolyRate L P : ∃ K ≥ 0, ∀ N ≥ 1, |√N Z_L(N) − P(log N)| ≤ K(1+ℓ)/√N`, `gaussJlogPow j = ∫₀^∞ h log^j x/x`, `stepPoly P Q = (1/s) primZero P + (2/s) Σ_{j ≤ deg P} 2^j J_j hasseDeriv j P + 2Q/s` (`eval_stepPoly`); ★★★ `HasPolyRate.step : HasPolyRate L P → HasPolyRate (L+1) (stepPoly P (residualMass L P))` for EVERY `L` and EVERY `P : ℝ[X]` (no degree hypothesis): `measurable_gaussLaplaceL` (all depths, `integral_prod_right'`), `polyResidual_outer_le` (the rate at `N = v²`), the scalar recursion `sqrt_mul_gaussLaplaceL_succ_eq`, `polyTail_integral_eq/split`, `poly_flat_integral_eq` (= `(primZero P)(ℓ)/2`), `gaussH_eval_log_eq_sum` + `poly_hpart_integral_eq` (Hasse–Taylor), the exact remainder `sqrt_mul_gaussLaplaceL_succ_sub_eq`, then DCLVII's residual bound and `a√a` cutoff moments with DCLXII's coefficient bound and absorption. The exponent `m = 1` is the invariant. | PolynomialDepthStep.lean |
| **DCLXIV** | ★★★ **THE ALL-DEPTH THEOREM AND THE ACCEPTANCE TESTS (u1000; Astra round 19, engine stage C)**: `depthTwoPoly`, `depthThreePoly`, `depthFourPoly`, `depthFivePoly` as `Polynomial ℝ` with eval lemmas; ★★ `hasPolyRate_two : HasPolyRate 2 P₂` (from DCXII's `gaussLaplace2_two_term_bound`); `enginePoly : ℕ → ℝ[X]` (`enginePoly 2 = P₂`, `enginePoly (L+1) = stepPoly (enginePoly L) (residualMass L (enginePoly L))`); ★★★ `hasPolyRate_enginePoly : ∀ L ≥ 2, HasPolyRate L (enginePoly L)` — the full log-polynomial with the linear-log rate `|√N Z_L(N) − (enginePoly L)(log N)| ≤ K_L(1+ℓ)/√N` at EVERY depth, by induction with DCLXIII's step. ACCEPTANCE TESTS: `polyResidual_two/three/four_eq` (`= depthThreeQ, depthFourQ, depthFiveQ`), `residualMass_two/three/four` (`= depthThreeQint, depthFourQint, depthFiveQint`), `eval_hasseDeriv_zero/one/two/three` (via `factorial_smul_hasseDeriv`), `primZero_eq_of` (characterisation by derivative and value at 0) with `primZero_depthTwo/Three/FourPoly`, ★★ `stepPoly_two : stepPoly P₂ Q₂ = P₃` (DCXXXI's `depthThreeConst`), ★★ `stepPoly_three : stepPoly P₃ Q₃ = P₄` (DCLI's `depthFourConst`), ★★ `stepPoly_four : stepPoly P₄ Q₄ = P₅` (DCLVI's `depthFiveLinCoeff`, `depthFiveConst`) — the engine reproduces every hand-built depth (`Polynomial.funext` + `field_simp; ring` with `π = s²/2`). | PolynomialDepthAll.lean |

## Public statements of DCLXIII (docstrings + signatures)
```lean
theorem measurable_gaussLaplaceL (L : ℕ) : Measurable (gaussLaplaceL L)

theorem measurable_gaussLaplaceL_sq (L : ℕ) : Measurable fun v : ℝ => gaussLaplaceL L (v ^ 2)

/-- `q_L(v) = Z_L(v²) − 1_{(1,∞)}(v) P(2 log v)/v`. -/
noncomputable def polyResidual (L : ℕ) (P : ℝ[X]) (v : ℝ) : ℝ

/-- `Q_L = ∫₀^∞ q_L`. -/
noncomputable def residualMass (L : ℕ) (P : ℝ[X]) : ℝ := ∫ v in Ioi (0 : ℝ), polyResidual L P v

/-- The linear-log rate at depth `L` with polynomial `P`. -/
def HasPolyRate (L : ℕ) (P : ℝ[X]) : Prop

/-- The log moments `J_j = ∫₀^∞ h(x) log^j x/x dx`. -/
noncomputable def gaussJlogPow (j : ℕ) : ℝ := ∫ x in Ioi (0 : ℝ), gaussH x * Real.log x ^ j / x

/-- The step `P ↦ (1/s) primZero P + (2/s) Σ_j 2^j J_j H_j P + 2Q/s`. -/
noncomputable def stepPoly (P : ℝ[X]) (Q : ℝ) : ℝ[X]

theorem eval_stepPoly (P : ℝ[X]) (Q ℓ : ℝ) :
    (stepPoly P Q).eval ℓ = 1 / Real.sqrt (2 * Real.pi) * (primZero P).eval ℓ +
      2 / Real.sqrt (2 * Real.pi) *
        ∑ j ∈ range (P.natDegree + 1), 2 ^ j * gaussJlogPow j * (hasseDeriv j P).eval ℓ +
      2 * Q / Real.sqrt (2 * Real.pi)

theorem measurable_polyResidual (L : ℕ) (P : ℝ[X]) : Measurable (polyResidual L P)

theorem polyResidual_inner (L : ℕ) (P : ℝ[X]) {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    polyResidual L P v = gaussLaplaceL L (v ^ 2)

theorem abs_polyResidual_inner_le (L : ℕ) (P : ℝ[X]) {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    |polyResidual L P v| ≤ 1

/-- The rate at `N = v²` bounds the residual: `|q_L(v)| ≤ K(1 + 2 log v)/v²` on `(1,∞)`. -/
theorem polyResidual_outer_le {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 1 < v →
      |polyResidual L P v| ≤ K * (1 + 2 * Real.log v) / v ^ 2

theorem integrableOn_polyResidual {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    IntegrableOn (polyResidual L P) (Ioi 0)

theorem integrable_gaussDensity_mul_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x : ℝ => gaussDensity x * gaussLaplaceL L (N * x ^ 2))

/-- `√N Z_{L+1}(N) = 2 ∫₀^∞ γ(v/√N) Z_L(v²) dv` for `N > 0`. -/
theorem sqrt_mul_gaussLaplaceL_succ_eq (L : ℕ) {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N =
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * gaussLaplaceL L (v ^ 2)

/-- The tail integrand `1_{v>1} P(2 log v)/v`. -/
noncomputable def polyTail (P : ℝ[X]) (v : ℝ) : ℝ

theorem polyResidual_add_tail (L : ℕ) (P : ℝ[X]) (v : ℝ) :
    polyResidual L P v + polyTail P v = gaussLaplaceL L (v ^ 2)

theorem integrableOn_gaussDensity_div_mul_gaussLaplaceL_sq (L : ℕ) {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * gaussLaplaceL L (v ^ 2))
      (Ioi 0)

/-- `√N Z_{L+1} = 2∫ γ(v/√N) q_L + 2∫ γ(v/√N) tail`. -/
theorem sqrt_mul_gaussLaplaceL_succ_split {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) {N : ℝ}
    (hN : 0 < N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N =
      2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) +
      2 * ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyTail P v

/-- The tail in `x = v/√N`: `∫₀^∞ γ(v/√N) tail(v) dv = ∫_{a}^∞ γ(x) P(ℓ + 2 log x)/x dx`. -/
theorem polyTail_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyTail P v =
      ∫ x in Ioi (1 / Real.sqrt N),
        gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x

/-- `h(x) P(ℓ + 2 log x)/x = Σ_j (H_jP)(ℓ) 2^j (h(x) log^j x/x)`. -/
theorem gaussH_eval_log_eq_sum (P : ℝ[X]) (ℓ x : ℝ) :
    gaussH x * P.eval (ℓ + 2 * Real.log x) / x =
      ∑ j ∈ range (P.natDegree + 1),
        (hasseDeriv j P).eval ℓ * 2 ^ j * (gaussH x * Real.log x ^ j / x)

theorem integrableOn_gaussH_eval_log (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussH x * P.eval (Real.log N + 2 * Real.log x) / x)
      (Ioi (1 / Real.sqrt N))

/-- The `h`-part: `∫_a^∞ h P(ℓ + 2 log x)/x = Σ_j (H_jP)(ℓ) 2^j ∫_a^∞ h log^j x/x`. -/
theorem poly_hpart_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussH x * P.eval (Real.log N + 2 * Real.log x) / x =
      ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
        ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x

theorem polyTail_integral_split (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x * P.eval (Real.log N + 2 * Real.log x) / x =
      1 / Real.sqrt (2 * Real.pi) *
        ((∫ x in Ioc (1 / Real.sqrt N) 1, P.eval (Real.log N + 2 * Real.log x) / x) +
          ∫ x in Ioi (1 / Real.sqrt N),
            gaussH x * P.eval (Real.log N + 2 * Real.log x) / x)

/-- The flat part with `a = N^{−1/2}`: `∫_a^1 P(ℓ + 2 log x)/x = (primZero P)(ℓ)/2`. -/
theorem poly_flat_integral_eq (P : ℝ[X]) {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, P.eval (Real.log N + 2 * Real.log x) / x =
      (primZero P).eval (Real.log N) / 2

/-- The exact remainder: for `N ≥ 1`,
`√N Z_{L+1} − (stepPoly P Q_L)(ℓ) = [2∫γ(v/√N)q_L − (2/s)Q_L] − (2/s) Σ_j (H_jP)(ℓ) 2^j ε_j`,
`ε_j = ∫₀^a h log^j x/x`. -/
theorem sqrt_mul_gaussLaplaceL_succ_sub_eq {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) {N : ℝ}
    (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL (L + 1) N -
        (stepPoly P (residualMass L P)).eval (Real.log N) =
      (2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * polyResidual L P v) -
        2 / Real.sqrt (2 * Real.pi) * residualMass L P) -
      2 / Real.sqrt (2 * Real.pi) *
        ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval (Real.log N) * 2 ^ j *
          ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x * Real.log x ^ j / x

/-- ★★★ **The depth step**: the linear-log rate propagates from depth `L` with `P` to depth
`L + 1` with `stepPoly P Q_L`. -/
theorem HasPolyRate.step {L : ℕ} {P : ℝ[X]} (h : HasPolyRate L P) :
    HasPolyRate (L + 1) (stepPoly P (residualMass L P))

def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set d := P.natDegree with hd
  -- the coefficient constants
  set Cc : ℕ → ℝ := fun j => ∑ i ∈ range (d + 1), |(hasseDeriv j P).coeff i| with hCc
  have hCc0 : ∀ j, 0 ≤ Cc j := fun j => Finset.sum_nonneg fun i _ => abs_nonneg _
  set M : ℝ := ∑ j ∈ range (d + 1), Cc j * 2 ^ j * ((2 * j) ^ j / 3) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => by
    have := hCc0 j; positivity
  obtain ⟨Cd, hCd0, hCd⟩ := exists_log_pow_cutoff_constant d
  refine ⟨2 / s * (1 / 2 + K / 2 + 3 * K + M * Cd), by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  set ℓ := Real.log N with hℓdef
  set a : ℝ := 1 / Real.sqrt N with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha_def, div_le_one hsN]; exact hsN1
  have hasqrt : a * Real.sqrt a = N ^ (-(3 / 4 : ℝ))
```

## Public statements of DCLXIV
```lean
theorem and the acceptance tests

Iterating the depth step from the depth-two base case gives the full polynomial with the
linear-log rate at EVERY depth: `enginePoly 2 = P₂ = (X + 3 log 2 − γ)/s` (from DCXII's two-term
bound), `enginePoly (L+1) = stepPoly (enginePoly L) (residualMass L (enginePoly L))`, and
★★★ `hasPolyRate_enginePoly : ∀ L ≥ 2, HasPolyRate L (enginePoly L)`, i.e.
`|√N Z_L(N) − (enginePoly L)(log N)| ≤ K_L(1 + log N)/√N` for `N ≥ 1`.

The acceptance tests (Astra round 19) certify the engine against the hand-built depths:
`stepPoly P₂ Q₂ = P₃` (`stepPoly_two`, so `enginePoly 3 = P₃` with DCXXXI's `depthThreeConst`),
`stepPoly P₃ Q₃ = P₄` (`stepPoly_three`, DCLI's `depthFourConst`), `stepPoly P₄ Q₄ = P₅`
(`stepPoly_four`, DCLVI's `depthFiveLinCoeff`, `depthFiveConst`), the residual masses being
identified with `depthThreeQint`, `depthFourQint`, `depthFiveQint`.  Examples_slop §2.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Polynomial Finset

namespace Grammar

/-! ### The explicit low-depth polynomials -/

/-- `P₂(u) = (u + 3 log 2 − γ)/s`. -/
noncomputable def depthTwoPoly : ℝ[X]

/-- `P₃(u) = A₃u² + B₃u + C₃`. -/
noncomputable def depthThreePoly : ℝ[X]

/-- `P₄(u) = A₄u³ + B₄u² + C₄u + D₄`. -/
noncomputable def depthFourPoly : ℝ[X]

/-- `P₅(u) = A₅u⁴ + B₅u³ + C₅u² + D₅u + E₅`. -/
noncomputable def depthFivePoly : ℝ[X]

theorem eval_depthTwoPoly (u : ℝ) : depthTwoPoly.eval u =
    (u + (3 * Real.log 2 - Real.eulerMascheroniConstant)) / Real.sqrt (2 * Real.pi)

theorem eval_depthThreePoly (u : ℝ) : depthThreePoly.eval u = depthThreeJet u

theorem eval_depthFourPoly (u : ℝ) : depthFourPoly.eval u = depthFourJet u

theorem eval_depthFivePoly (u : ℝ) : depthFivePoly.eval u =
    gaussCoeffA 1 * u ^ 4 + gaussCoeffB 1 * u ^ 3 + thirdCoeff 1 * u ^ 2 + depthFiveLinCoeff * u +
      depthFiveConst

/-- ★★ `HasPolyRate 2 P₂` from the depth-two two-term bound. -/
theorem hasPolyRate_two : HasPolyRate 2 depthTwoPoly

def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  refine ⟨2 / s, by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have h := gaussLaplace2_two_term_bound (by linarith : 1 / 2 ≤ N)
  have hsq : Real.sqrt (2 * Real.pi * N) = s * Real.sqrt N

/-- The polynomial at every depth: `enginePoly 2 = P₂`, `enginePoly (L+1) = stepPoly …`. -/
noncomputable def enginePoly : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => depthTwoPoly
  | L + 3 => stepPoly (enginePoly (L + 2)) (residualMass (L + 2) (enginePoly (L + 2)))

theorem enginePoly_two : enginePoly 2 = depthTwoPoly := rfl

theorem enginePoly_succ (L : ℕ) (hL : 2 ≤ L) :
    enginePoly (L + 1) = stepPoly (enginePoly L) (residualMass L (enginePoly L))

/-- ★★★ **The all-depth theorem**: at every depth `L ≥ 2`,
`|√N Z_L(N) − (enginePoly L)(log N)| ≤ K_L (1 + log N)/√N` for `N ≥ 1`. -/
theorem hasPolyRate_enginePoly : ∀ L : ℕ, 2 ≤ L → HasPolyRate L (enginePoly L)

theorem eval_hasseDeriv_zero (P : ℝ[X]) (u : ℝ) : (hasseDeriv 0 P).eval u = P.eval u

theorem eval_hasseDeriv_one (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 1 P).eval u = (derivative P).eval u

theorem eval_hasseDeriv_two (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 2 P).eval u = (derivative (derivative P)).eval u / 2

theorem eval_hasseDeriv_three (P : ℝ[X]) (u : ℝ) :
    (hasseDeriv 3 P).eval u = (derivative (derivative (derivative P))).eval u / 6

/-- The primitive is characterised by its derivative and its value at `0`. -/
theorem primZero_eq_of {P G : ℝ[X]} (hG : derivative G = P) (h0 : G.eval 0 = 0) :
    primZero P = G

theorem polyResidual_two_eq : polyResidual 2 depthTwoPoly = depthThreeQ

theorem residualMass_two : residualMass 2 depthTwoPoly = depthThreeQint

theorem polyResidual_three_eq : polyResidual 3 depthThreePoly = depthFourQ

theorem residualMass_three : residualMass 3 depthThreePoly = depthFourQint

theorem polyResidual_four_eq : polyResidual 4 depthFourPoly = depthFiveQ

theorem residualMass_four : residualMass 4 depthFourPoly = depthFiveQint

theorem natDegree_depthTwoPoly : depthTwoPoly.natDegree = 1

theorem natDegree_depthThreePoly : depthThreePoly.natDegree = 2

theorem natDegree_depthFourPoly : depthFourPoly.natDegree = 3

theorem primZero_depthTwoPoly : primZero depthTwoPoly =
    C (1 / (2 * Real.sqrt (2 * Real.pi))) * X ^ 2 +
      C ((3 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt (2 * Real.pi)) * X

theorem primZero_depthThreePoly : primZero depthThreePoly =
    C (1 / (12 * Real.pi)) * X ^ 3 +
      C ((2 * Real.log 2 - Real.eulerMascheroniConstant) / (2 * Real.pi)) * X ^ 2 +
      C depthThreeConst * X

theorem primZero_depthFourPoly : primZero depthFourPoly =
    C (gaussCoeffA 0 / 4) * X ^ 4 + C (gaussCoeffB 0 / 3) * X ^ 3 + C (thirdCoeff 0 / 2) * X ^ 2 +
      C depthFourConst * X

/-- The step from depth two reproduces `P₃` (DCXXXI's constant). -/
theorem stepPoly_two : stepPoly depthTwoPoly (residualMass 2 depthTwoPoly) = depthThreePoly

/-- The step from depth three reproduces `P₄` (DCLI's constant). -/
theorem stepPoly_three :
    stepPoly depthThreePoly (residualMass 3 depthThreePoly) = depthFourPoly

/-- The step from depth four reproduces `P₅` (DCLVI's coefficients). -/
theorem stepPoly_four :
    stepPoly depthFourPoly (residualMass 4 depthFourPoly) = depthFivePoly
```

## State (pinned to grammar 19f0430)
Formal: §2 Gaussian DLN: THE FULL LOG-POLYNOMIAL WITH A LINEAR-LOG RATE AT EVERY DEPTH (engine), `A_L, B_L, C_L` closed, `C₃` exact, `D₄, D₅, E₅` integral-defined, generic residual/cutoff lemmas, Mellin closed form of `Z₂`, residual bridge, jet, transfers; depth-two two-term, Bessel. §3 cone: exact `c₂` with rate. §4 blow-up. §5 rank-one. §6 naive Bayes: density (both forms), closed form, support, fibre mass, conditional density/measure, conditional mean, joint mass 1, surrogate exactness, fibre polar distributions, averaged theorem, certificates, `m₂`.
Derivation-only: jet identification of the engine's constants (`ζ(3), ζ(4), …`); `J_k` exact; the naive-Bayes surrogate posterior mean (eq. nb_postmu) as a ratio of weighted closed-piece integrals; chart envelope exponents; KL-vs-surrogate; blow-up `N^{−3/2}log N`; rank-one Morse–Bott; smooth-amplitude tie remainder; cone `c₃`.

## Questions
1. Fidelity check (brief) of DCLXIII–DCLXIV: (a) `stepPoly` with `C (2^j * gaussJlogPow j) * hasseDeriv j P` summed over `range (natDegree P + 1)` — is truncating at `natDegree P` right (yes since `hasseDeriv j P = 0` for `j > natDegree`), and is the `(2/s)` factor and `2Q/s` constant right against your recursion?; (b) `HasPolyRate.step` needs NO hypothesis on `L` — the scalar recursion `gaussLaplaceL_succ_scalar` holds for all `L` including `L = 0, 1`, so the theorem applies even at `L = 0, 1` where the premise is false/vacuous; fine?; (c) `enginePoly 0 = enginePoly 1 = 0` are dummies; (d) the base case constant `K₂ = 2/s` from `(log 2N + 3)/(2sN) ≤ 4(1+ℓ)/(2sN)`.
2. NEXT: the engine now makes the COEFFICIENT recursion mechanical. Which of these is the best day-sized deliverable? (a) `leadingCoeff_enginePoly : (enginePoly L).coeff (L−1) = 1/((L−1)! s^{L−1})` and `natDegree_enginePoly = L−1`, then the second and third coefficients `(enginePoly L).coeff (L−2) = B_L`, `.coeff (L−3) = C_L` (DCXXVI/DCXLVI closed forms) by induction through `stepPoly`'s coefficient formula `coeff_stepPoly : (stepPoly P Q).coeff k = (1/s) P.coeff (k−1)/k + (2/s) Σ_j 2^j J_j C(k+j, j) P.coeff (k+j) + [k=0] 2Q/s` — is `Polynomial.coeff` of `hasseDeriv` available as `coeff_hasseDeriv`? This would re-derive DCXXIV/DCXXVI/DCXLVI from the engine (consistency) and give `natDegree`; (b) the CONSTANT term recursion `(enginePoly (L+1)).coeff 0 = (2/s)[Σ_j 2^j J_j (H_j P_L)(0) + Q_L]` (trivial from `eval_stepPoly` at 0) plus the identification `(H_j P)(0) = coeff j`; (c) an explicit `K_L` (track the constants through the step: `K_{L+1} = (2/s)(1/2 + K_L/2 + 3K_L + M_L C_d)`) — is an explicit but crude `K_L` worth stating?; (d) `HasPolyRate` uniqueness: if `HasPolyRate L P` and `HasPolyRate L P'` then `P = P'` (from `(P − P')(ℓ) = O((1+ℓ)/√N) → 0` and a polynomial vanishing at infinity is zero: `Polynomial.eq_zero_of_...`? needs `tendsto_atTop` of polynomials) — this would make `enginePoly L` THE polynomial and identify it with any other expansion (e.g. the Mellin jet, once the jet asymptotic is proved); (e) the naive-Bayes surrogate posterior mean as a ratio of weighted integrals (your round-19 item 2; please state the exact weight from eq. nb_surrogate/nb_postmu: `w(z) = e^{−N z²/(2V)}`?); (f) `J_k`–`G_r` bridge. Please rank (a)–(f) and give the Lean-facing interface for the top two, including the exact Mathlib names you expect for coefficient of hasseDeriv, natDegree of primZero, and polynomial-tends-to-zero-implies-zero.
3. Any convention hazards in DCLXIII–DCLXIV (`enginePoly` vs the note's `P_L`; `gaussJlogPow j` vs `gaussJlog`/`gaussJlog2`/`gaussJlog3`; `residualMass` vs `depthThreeQint` etc.)?
Answer concisely with Lean-facing detail.
