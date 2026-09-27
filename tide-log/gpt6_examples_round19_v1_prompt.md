You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 25156d7, 996 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-18 programme is COMPLETE: (1) the depth-five LINEAR-LOG rate `|√N Z₅ − P₅(ℓ) − E₅| ≤ K(1+ℓ)/√N` (DCLVIII) from two generic lemmas (DCLVII): the residual bound `residual_term_bound_of_le` for any residual with `|q| ≤ 1` on `(0,1]` and `|q| ≤ K(1+2log v)/v²` beyond (`(2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]`, exponent preserved — your quadratic split), and the cutoff moments `|∫₀^a h log^j x/x| ≤ (2j)^j/3 · a√a` (from `|log x|^j ≤ (2j)^j/√x`; the cutoff products of the cubic then cost `(1+ℓ)³N^{−3/4} ≤ 81(1+ℓ)/√N` via `1 + log N ≤ 9N^{1/8}`) — I used the per-moment `a^{3/2}` bound rather than your combined `a²` cutoff (simpler in Lean; the exponent `m = 1` is preserved either way); (2) naive Bayes: joint mass `1` and a.e. fibre finiteness by Tonelli (DCLIX), then the SUPPORT theorem and the exact fibre mass for EVERY interior `λ` (DCLX): `m(λ) = 2M₊(log(V/M₊²)+2) + 2M₋(log(V/M₋²)+2)`, `m(½,½) = 2` as you predicted; numerically `m(λ)` = closed-form quadrature = `t`-integral quadrature = area of the `(t,η)`-region (8 digits) and `∫_{(0,1)²} m = 1` (10⁻¹⁰).

## HEADLINES rows DCLVII–DCLX
| **DCLVII** | ★★ **THE RESIDUAL AND CUTOFF BOUNDS, GENERICALLY (u993; Astra round 18: the two quantitative lemmas of the all-depth engine)**: ★★ `residual_term_bound_of_le` (measurable `q`, `|q| ≤ 1` on `(0,1]`, `|q(v)| ≤ K(1+2 log v)/v²` on `(1,∞)` ⇒ `|2∫γ(v/√N)q − (2/s)∫q| ≤ (2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]`, `N ≥ 1`; DCLII's `residual_term_bound` is `K = 8`; the logarithmic exponent is preserved), `integrableOn_of_le_one_add_two_log`, `integrableOn_gaussDensity_div_mul_of_integrableOn`; ★★ `abs_integral_gaussH_log_pow_Ioc_le_sqrt : |∫₀^a h log^j x/x| ≤ (2j)^j/3 · a√a` for `0 < a ≤ 1` (one power of `√a` better than DCLI's `(j+1)^j a/2`; from `|h| ≤ x²/2` and `abs_log_pow_le_div_sqrt : |log x|^j ≤ (2j)^j/√x` on `(0,1]`, `∫₀^a √x = (2/3)a^{3/2}`). | GaussianResidualCutoffBounds.lean |
| **DCLVIII** | ★★★ **THE DEPTH-FIVE POLYNOMIAL WITH THE LINEAR-LOG RATE (u994; Astra round-18 target 1)**: ★★★ `gaussLaplaceL_five_constant_rate : ∃ K ≥ 0, ∀ N ≥ 1, |√N Z₅ − A₅ℓ⁴ − B₅ℓ³ − C₅ℓ² − D₅ℓ − E₅| ≤ K(1+ℓ)/√N` — DCLVI's exact remainder with DCLVII's generic residual bound (`|q₄| ≤ K₄(1+2 log v)/v²` from DCLIV) and the `a√a` cutoff moments, so the cutoff products of the cubic `P₄` cost `(1+ℓ)³ N^{−3/4} ≤ 81(1+ℓ)/√N` via `one_add_log_le_nine_mul_rpow : 1 + log N ≤ 9N^{1/8}` and `sqrt_eq_rpow_eighth_pow`. The exponent `m = 1` is PRESERVED from depth four to five: the invariant of the all-depth engine. | GaussianDepthFiveRate.lean |
| **DCLIX** | ★★ **A.E. FIBRE FINITENESS OF THE NAIVE-BAYES DENSITY (u995; Astra round-18 target 2, part 1)**: `volume_nbBox = 1`; ★★ `lintegral_nbFibreDensity_joint : ∫⁻_{(0,1)²} ∫⁻ ρ(λ,μ) dμ dλ = 1` (DXCV's `lintegral_nbBox_moments` with `Ψ = 1`); ★★ `ae_lintegral_nbFibreDensity_lt_top` (Tonelli: for a.e. `λ`, `∫ρ(λ,·) < ∞`, via `ae_lt_top` and `measurable_lintegral_nbFibreDensity`); ★★ `ae_integrable_nbFixedDensity` (for a.e. `λ` the real fixed-domain density is integrable in `μ` with `ofReal ∫ nbFixedDensity = ∫⁻ nbFibreDensity`); ★★ `integral_nbFixedDensity_joint : ∫_{(0,1)²} ∫ nbFixedDensity = 1`. The fixed-`λ` density is NOT normalised (Astra: mass 2 at `λ = (½,½)`); pointwise mass needs the support theorem (next). | NaiveBayesFibreFiniteness.lean |
| **DCLX** | ★★★ **THE SUPPORT AND THE FIBRE MASS OF THE NAIVE-BAYES DENSITY (u996; Astra round-18 target 2, part 2)**: the Fréchet bounds `nbMplus = min(λ₁(1−λ₂), λ₂(1−λ₁))`, `nbMminus = min(λ₁λ₂, (1−λ₁)(1−λ₂))`, `nbV`; ★★ support theorem `nbFibreDensity_eq_zero_of_ge/le` (ρ = 0 for `μ ≥ M₊` and `μ ≤ −M₋`, from `quadP_div_le : P(t)/(t(1−t)) ≤ M` and `quadJ_eq_zero_of_ge`); `nbFibreDensity_eq_indicator` (ρ = closed form on `(0,M₊)` + reflected closed form on `(−M₋,0)`); the closed piece `nbClosed M V z = 2 log(M/z) log(V/(Mz))`: `abs_nbClosed_le` (≤ `2(1+|log M|)(1+|log(V/M)|)(1+|log z|)²`), `integrableOn_nbClosed` (via DCXLVIII's `integrableOn_rpow_mul_logWeight`), the antiderivative `hasDerivAt_nbClosed_primitive` (`2z[(c₁−L)(c₂−L) + (c₁+c₂−2L) + 2]`), `tendsto_nbClosed_primitive_zero` (`z log z, z log² z → 0`), ★★ `integral_nbClosed : ∫₀^M nbClosed = 2M(log(V/M²) + 2)` (FTC with limits), reflected `integral_nbClosed_neg`; ★★★ `lintegral_nbFibreDensity_eq_mass : ∫⁻ ρ(λ,·) = ofReal m(λ)`, `m(λ) = nbFibreMass = 2M₊(log(V/M₊²)+2) + 2M₋(log(V/M₋²)+2)` for EVERY `λ ∈ (0,1)²`; `lintegral_nbFibreDensity_ne_top`, ★★ `integrable_nbFixedDensity`, ★★★ `integral_nbFixedDensity_eq_mass`; `nbFibreMass_half : m(½,½) = 2` (Astra's example: the fixed-λ density is not normalised). | NaiveBayesFibreMass.lean |

## Public statements of DCLVII (docstrings + signatures)
```lean
theorem integrableOn_of_le_one_add_two_log {q : ℝ → ℝ} (hq : Measurable q) {K : ℝ}
    (hin : ∀ v ∈ Ioc (0 : ℝ) 1, |q v| ≤ 1)
    (hout : ∀ v : ℝ, 1 < v → |q v| ≤ K * (1 + 2 * Real.log v) / v ^ 2) :
    IntegrableOn q (Ioi 0)

theorem integrableOn_gaussDensity_div_mul_of_integrableOn {q : ℝ → ℝ} (hq : Measurable q)
    (hqi : IntegrableOn q (Ioi 0)) {N : ℝ} :
    IntegrableOn (fun v : ℝ => gaussDensity (v / Real.sqrt N) * q v) (Ioi 0)

/-- ★★ **The residual term, quantitatively and generically**: for measurable `q` with `|q| ≤ 1`
on `(0,1]` and `|q(v)| ≤ K(1 + 2 log v)/v²` on `(1,∞)`,
`|2∫ γ(v/√N) q − (2/s)∫ q| ≤ (2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]` for `N ≥ 1`
(DCLII's `residual_term_bound` is the instance `K = 8`). -/
theorem residual_term_bound_of_le {q : ℝ → ℝ} (hq : Measurable q) {K : ℝ} (hK : 0 ≤ K)
    (hin : ∀ v ∈ Ioc (0 : ℝ) 1, |q v| ≤ 1)
    (hout : ∀ v : ℝ, 1 < v → |q v| ≤ K * (1 + 2 * Real.log v) / v ^ 2)
    {N : ℝ} (hN : 1 ≤ N) :
    |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * q v) -
      2 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (0 : ℝ), q v| ≤
      2 / Real.sqrt (2 * Real.pi) *
        (1 / (2 * N) + K * (1 + Real.log N) / (2 * Real.sqrt N) +
          K * (3 + Real.log N) / Real.sqrt N)

def
  have hdiff : 2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * q v) -
      2 / s * ∫ v in Ioi (0 : ℝ), q v =
      2 * ∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * q v

/-- `|log x|^j ≤ (2j)^j/√x` on `(0,1]`. -/
theorem abs_log_pow_le_div_sqrt {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    |Real.log x| ^ j ≤ (2 * j) ^ j / Real.sqrt x

/-- ★★ The cutoff moment with the extra `√a`: `|∫₀^a h log^j x/x| ≤ (2j)^j/3 · a√a` for
`0 < a ≤ 1`. -/
theorem abs_integral_gaussH_log_pow_Ioc_le_sqrt (j : ℕ) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x * Real.log x ^ j / x| ≤
      (2 * j) ^ j / 3 * (a * Real.sqrt a)
```

## Public statements of DCLX
```lean
/-- The upper Fréchet bound `M₊ = min(λ₁(1−λ₂), λ₂(1−λ₁))`. -/
noncomputable def nbMplus (l₁ l₂ : ℝ) : ℝ := min (l₁ * (1 - l₂)) (l₂ * (1 - l₁))

/-- The lower Fréchet bound `M₋ = min(λ₁λ₂, (1−λ₁)(1−λ₂))`. -/
noncomputable def nbMminus (l₁ l₂ : ℝ) : ℝ := min (l₁ * l₂) ((1 - l₁) * (1 - l₂))

/-- The variance product `V = λ₁(1−λ₁)λ₂(1−λ₂)`. -/
noncomputable def nbV (l₁ l₂ : ℝ) : ℝ := l₁ * (1 - l₁) * (l₂ * (1 - l₂))

/-- The closed-form fibre density on one side, `2 log(M/z) log(V/(Mz))`. -/
noncomputable def nbClosed (M V z : ℝ) : ℝ := 2 * (Real.log (M / z) * Real.log (V / (M * z)))

/-- The fibre mass `m(λ) = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)`. -/
noncomputable def nbFibreMass (l₁ l₂ : ℝ) : ℝ

/-- `P(t)/(t(1−t)) ≤ min(b₁(1−b₂), b₂(1−b₁))` on `(0,1)`. -/
theorem quadP_div_le {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    quadP b₁ b₂ t / (t * (1 - t)) ≤ min (b₁ * (1 - b₂)) (b₂ * (1 - b₁))

/-- The quadrant integral vanishes at and beyond the Fréchet bound. -/
theorem quadJ_eq_zero_of_ge {z : ℝ} (hz : 0 < z)
    (hzM : min (b₁ * (1 - b₂)) (b₂ * (1 - b₁)) ≤ z) : quadJ b₁ b₂ z = 0

theorem nbMplus_pos : 0 < nbMplus l₁ l₂

theorem nbMminus_pos : 0 < nbMminus l₁ l₂

theorem nbV_pos : 0 < nbV l₁ l₂

theorem nbMplus_sq_le : nbMplus l₁ l₂ ^ 2 ≤ nbV l₁ l₂

theorem nbMminus_sq_le : nbMminus l₁ l₂ ^ 2 ≤ nbV l₁ l₂

theorem nbMplus_le_one : nbMplus l₁ l₂ ≤ 1

theorem nbMminus_le_one : nbMminus l₁ l₂ ≤ 1

/-- ★★ The support theorem, `μ ≥ M₊`: the fibre density vanishes. -/
theorem nbFibreDensity_eq_zero_of_ge {z : ℝ} (hz : nbMplus l₁ l₂ ≤ z) :
    nbFibreDensity l₁ l₂ z = 0

/-- ★★ The support theorem, `μ ≤ −M₋`. -/
theorem nbFibreDensity_eq_zero_of_le {z : ℝ} (hz : z ≤ -nbMminus l₁ l₂) :
    nbFibreDensity l₁ l₂ z = 0

theorem nbFibreDensity_zero : nbFibreDensity l₁ l₂ 0 = 0

/-- The fibre density as the sum of the two closed-form pieces on `(0, M₊)` and `(−M₋, 0)`. -/
theorem nbFibreDensity_eq_indicator (z : ℝ) :
    nbFibreDensity l₁ l₂ z =
      (Ioo (0 : ℝ) (nbMplus l₁ l₂)).indicator
        (fun z => ENNReal.ofReal (nbClosed (nbMplus l₁ l₂) (nbV l₁ l₂) z)) z +
      (Ioo (-nbMminus l₁ l₂) 0).indicator
        (fun z => ENNReal.ofReal (nbClosed (nbMminus l₁ l₂) (nbV l₁ l₂) (-z))) z

theorem measurable_nbClosed (M V : ℝ) : Measurable (nbClosed M V)

theorem nbClosed_nonneg {M V z : ℝ} (hz : 0 < z) (hzM : z ≤ M) (hM2 : M ^ 2 ≤ V) :
    0 ≤ nbClosed M V z

/-- `|nbClosed M V z| ≤ 2(1 + |log M|)(1 + |log(V/M)|)(1 + |log z|)²` for `z > 0`. -/
theorem abs_nbClosed_le {M V z : ℝ} (hM : 0 < M) (hV : 0 < V) (hz : 0 < z) :
    |nbClosed M V z| ≤ 2 * ((1 + |Real.log M|) * (1 + |Real.log (V / M)|)) *
      (1 + |Real.log z|) ^ 2

theorem integrableOn_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntegrableOn (nbClosed M V) (Ioo 0 M)

theorem intervalIntegrable_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntervalIntegrable (nbClosed M V) volume 0 M

/-- The antiderivative `2z[(c₁ − log z)(c₂ − log z) + (c₁ + c₂ − 2 log z) + 2]`. -/
theorem hasDerivAt_nbClosed_primitive {M V z : ℝ} (hM : 0 < M) (hV : 0 < V) (hz : 0 < z) :
    HasDerivAt (fun z : ℝ => 2 * (z * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) + 2))) (nbClosed M V z) z

/-- The primitive tends to `0` at `0⁺` (`z log z → 0`, `z log² z → 0`). -/
theorem tendsto_nbClosed_primitive_zero (M V : ℝ) :
    Tendsto (fun z : ℝ => 2 * (z * ((Real.log M - Real.log z) * (Real.log (V / M) - Real.log z) +
      (Real.log M + Real.log (V / M) - 2 * Real.log z) + 2))) (𝓝[>] 0) (𝓝 0)

/-- ★★ `∫₀^M 2 log(M/z) log(V/(Mz)) dz = 2M(log(V/M²) + 2)`. -/
theorem integral_nbClosed {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (0 : ℝ) M, nbClosed M V z = 2 * M * (Real.log (V / M ^ 2) + 2)

/-- The reflected piece: `∫_{−M}^0 nbClosed M V (−z) dz = 2M(log(V/M²) + 2)`. -/
theorem integral_nbClosed_neg {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    ∫ z in Ioo (-M) (0 : ℝ), nbClosed M V (-z) = 2 * M * (Real.log (V / M ^ 2) + 2)

theorem integrableOn_nbClosed_neg {M V : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hV : 0 < V) :
    IntegrableOn (fun z => nbClosed M V (-z)) (Ioo (-M) 0)

theorem nbFibreMass_nonneg : 0 ≤ nbFibreMass l₁ l₂

/-- ★★★ **The fibre mass**: for every `λ ∈ (0,1)²`,
`∫ ρ(λ, μ) dμ = 2M₊(log(V/M₊²) + 2) + 2M₋(log(V/M₋²) + 2)`. -/
theorem lintegral_nbFibreDensity_eq_mass :
    ∫⁻ z, nbFibreDensity l₁ l₂ z = ENNReal.ofReal (nbFibreMass l₁ l₂)

/-- ★★ Every interior fibre has finite mass. -/
theorem lintegral_nbFibreDensity_ne_top : ∫⁻ z, nbFibreDensity l₁ l₂ z ≠ ⊤

/-- ★★ The real fixed-domain density is integrable in `μ` for every interior `λ`. -/
theorem integrable_nbFixedDensity : Integrable fun z : ℝ => nbFixedDensity ((l₁, l₂), z)

/-- ★★★ The real fibre mass: `∫ nbFixedDensity ((λ₁, λ₂), μ) dμ = m(λ)`. -/
theorem integral_nbFixedDensity_eq_mass :
    ∫ z : ℝ, nbFixedDensity ((l₁, l₂), z) = nbFibreMass l₁ l₂

/-- At `λ = (½, ½)` the fibre mass is `2`: the fixed-`λ` density is not normalised. -/
theorem nbFibreMass_half : nbFibreMass (1 / 2) (1 / 2) = 2
```

## State (pinned to grammar 25156d7)
Formal: §2 Gaussian DLN: `A_L, B_L, C_L` closed at every depth; `C₃` exact; `D₄` and the full depth-five polynomial (`D₅`, `E₅` integral-defined) BOTH with linear-log rates; generic residual/cutoff lemmas; Mellin closed form of `Z₂`, residual bridge, jet, transfers; depth-two two-term, Bessel. §3 cone: exact `c₂` with rate. §4 blow-up: two-term expansion, family theorem, observables. §5 rank-one. §6 naive Bayes: pushforward density (ENNReal and real fixed-domain forms, jointly measurable, closed form, SUPPORT, fibre mass `m(λ)` for every interior `λ`, joint mass 1), surrogate exactness, fibre polar distributions, averaged theorem, domination/envelope certificates, `m₂`.
Derivation-only: jet identification of `D₄, D₅, E₅` (`ζ(3), ζ(4)`); `J₂, J₃` exact; the all-depth engine (`HasPolyRate.step`); sharp depth-four rate; NB chart envelope exponents, KL-vs-surrogate; blow-up `N^{−3/2}log N`; rank-one Morse–Bott; smooth-amplitude tie remainder; cone `c₃`.

## Questions
1. Fidelity check (brief) of DCLVII–DCLX: (a) the generic residual bound's constant `(2/s)[1/(2N) + K(1+ℓ)/(2√N) + K(3+ℓ)/√N]` (middle piece `∫₁^{√N} K(1+2log v)/(2N) ≤ K(1+ℓ)/(2√N)`, tail `K(3+2log √N)/√N`); (b) `abs_log_pow_le_div_sqrt : |log x|^j ≤ (2j)^j/√x` on `(0,1]` (from `−log x ≤ 2j x^{−1/(2j)}`); (c) the support theorem's mechanism `P(t)/(t(1−t)) ≤ M` — is the support of `ρ(λ,·)` EXACTLY `(−M₋, M₊)` (i.e. `ρ > 0` inside)? (d) `nbFibreMass` and `integral_nbClosed` (antiderivative check).
2. THE ALL-DEPTH ENGINE, now with the two generic lemmas in hand. Proposed Lean interface (please refine):
```lean
def polyResidual (L : ℕ) (P : Polynomial ℝ) (v : ℝ) : ℝ :=
  gaussLaplaceL L (v ^ 2) - (Ioi 1).indicator (fun v => P.eval (2 * Real.log v) / v) v
def HasPolyRate (L : ℕ) (P : Polynomial ℝ) : Prop :=   -- m = 1 fixed
  ∃ K, 0 ≤ K ∧ ∀ N ≥ 1, |√N Z_L N − P.eval (log N)| ≤ K (1 + log N)/√N
def stepPoly (P : Polynomial ℝ) (Q : ℝ) : Polynomial ℝ :=
  C (1/s) * prim P + C (2/s) * Σ_{j ≤ deg P} C (2^j J_j / j!) * derivative^[j] P + C (2 Q / s)
theorem HasPolyRate.step (hL : 2 ≤ L) (h : HasPolyRate L P) : HasPolyRate (L+1) (stepPoly P (∫ polyResidual L P))
```
The proof would be DCLVIII's with `depthFourJet` replaced by `P.eval`: (i) `|polyResidual L P v| ≤ K(1+2log v)/v²` on `(1,∞)` from `h` at `N = v²` — for general `P` the bound `|P.eval(2 log v)| ≤ Σ|c_k|(2 log v)^k` is NOT needed there (the rate hypothesis gives it directly); (ii) the tail substitution and `γ = (h + 1_{(0,1]})/s` split are polynomial-agnostic (need only measurability/integrability of `x ↦ h(x) P.eval(ℓ + 2 log x)/x`, from `Polynomial.eval` = finite sum of `log^j`); (iii) the FLAT part `∫_a^1 P.eval(ℓ + 2 log x)/x dx = (1/2)∫₀^ℓ P` via the antiderivative `(prim P).eval(ℓ + 2 log x)/2` — needs `HasDerivAt (fun x => (prim P).eval (ℓ + 2 log x)) ((derivative (prim P)).eval(ℓ + 2 log x) · 2/x)` = `Polynomial.hasDerivAt` composed; (iv) the `h`-part expansion `P.eval(ℓ + 2 log x) = Σ_j (derivative^[j] P).eval ℓ · (2 log x)^j / j!` — TAYLOR'S FORMULA for polynomials: is `Polynomial.taylor`/`Polynomial.eval_add`-type API on this pin enough (`Polynomial.taylor_coeff`, `Polynomial.sum_taylor_eq`, `Polynomial.hasseDeriv`)? or should I use `Polynomial.eval_eq_sum_range` with the binomial expansion of `(ℓ + y)^k` and re-sum (messy)?; (v) the cutoff moments with `|(derivative^[j] P).eval ℓ| ≤ C_j (1+ℓ)^{deg P − j}` and `(1+ℓ)^{deg P} a^{3/2} ≤ C(1+ℓ)/√N` — for `deg P ≥ 3` this needs `(1+ℓ)^{d−1} ≤ C_d N^{1/4}`, i.e. `log N ≤ C N^{1/(4(d−1))}` (generic `log_le_rpow_div`); (vi) the constant: `stepPoly`'s constant term `(2/s)(Σ_j 2^j J_j (derivative^[j] P).eval 0/j! + Q)` = `E_{L+1}`. Which of (iii)–(iv) are the real Lean risk, and what is the cleanest formulation of the Taylor step? Is a 2–3 day estimate right? Please also state the INSTANTIATION theorems that would certify the engine against DCLI–DCLVIII: `stepPoly P₃ Q₃ = P₄` and `stepPoly P₄ Q₄ = P₅` as polynomial identities (coefficient-wise, `Polynomial.ext`), and the base case `HasPolyRate 3 P₃` (DCXXXIV) — is that the right acceptance test?
3. Cheaper day-sized alternatives, ranked against the engine: (a) `J_k` ↔ `Γ^{(k+1)}(1)` bridge without evaluating the derivative (your staged plan: `G_r = ∫₀^∞ e^{−u} log^r u du`, `I_k = G_{k+1}/(k+1)` by IBP, `J_k` formula by `u = x²/2`, then `G_r = iteratedDeriv r Γ 1` separately); which Mathlib API gives `iteratedDeriv r Real.Gamma 1 = ∫ e^{−u} log^r u` — `Real.Gamma_eq_integral` + `hasDerivAt_integral_of_dominated_loc_of_deriv_le` iterated? Is stage 4 realistically ≤ 1 day on this pin (DCXXXVIII did `Γ''(1)` via the duplication formula, not by differentiating under the integral); (b) the naive-Bayes CONDITIONAL density `ρ/m(λ)` as a probability density and the posterior-mean-of-`μ` formula of the note (eq. nb_postmu) in the surrogate — what is the day-sized statement?; (c) `ρ > 0` on the open support; (d) cone `c₃`. Give the Lean-facing interface for your top choice.
Answer concisely with Lean-facing detail.
