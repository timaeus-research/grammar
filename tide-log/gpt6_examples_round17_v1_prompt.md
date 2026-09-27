You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main fcfc508 + DCLIII landing, 989 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-16 programme is COMPLETE: (1) the depth-four rate `|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1+ℓ)²/√N` (DCLII; split at `R = √N` exactly as you prescribed; the recorded quadrature shows the proven rate is valid but far from sharp — the deviation scaled by `√N/(1+ℓ)²` goes `0.0018 → 0.00005` over `N = 10²…10⁵`, and `N·|deviation| = 0.57, 1.0, 1.7, 2.6`, i.e. the true decay looks like `log N/N`); (2)+(3) the interfaces (DCLIII): the a.e.-measurable Mellin transfer, `measurable_fixedDomainIntegral` for the naive-Bayes-shaped parameter integral, the certificate on the cube as a set with an a.e. domination adapter; plus the polish (`gaussLaplaceL_third_coeff_closed`, `depthFourTail_eq_mellinLogTail`). The note is pinned to fcfc508.

## HEADLINES rows DCLII–DCLIII
| **DCLII** | ★★★ **THE DEPTH-FOUR CONSTANT WITH A RATE: `|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1+ℓ)²/√N` FOR `N ≥ 1` (u988; examples_slop §2; Astra round-16 target 1)**: `gaussLaplaceL_third_coeff_closed` (the third-coefficient limit restated with `thirdCoeffClosed`), `depthFourTail_eq_mellinLogTail` (`depthFourTail = mellinLogTail ![C₃, 2B₃, 4A₃]`, the DCXLIX bridge), `integral_Ioi_one_add_two_log_div_sq` (`∫_R^∞ (1+2log v)/v² = (3+2log R)/R`, antiderivative `−(3+2log v)/v`), ★★ `residual_term_bound` (`|2∫γ(v/√N)q₃ − (2/s)Q₃| ≤ (2/s)[1/(2N) + 4(1+ℓ)/√N + 8(3+ℓ)/√N]`: the DCT step made quantitative by the split `(0,1] ∪ (1,√N] ∪ (√N,∞)` with `|γ(v/√N) − γ(0)| ≤ v²/(2sN)` and `≤ 1/s`, and the majorant `1_{(0,1]}/(2N) + 1_{(1,√N]}4(1+2log v)/N + 1_{(√N,∞)}8(1+2log v)/v²` integrated), ★★★ `gaussLaplaceL_four_constant_rate` (with `∃ K`; from DCLI's exact remainder identity, the cutoff bounds `|ε_j| ≤ (j+1)^j/(2√N)` and `1/N ≤ 1/√N`, `1+ℓ`, `ℓ`, `ℓ²`, `3+ℓ ≤ 3(1+ℓ)²`). Numerics (recorded direct quadrature): `√N·|deviation|/(1+ℓ)² = 0.0018, 0.0005, 0.0002, 0.00005` at `N = 10², 10³, 10⁴, 10⁵`, and `N·|deviation| = 0.57, 1.0, 1.7, 2.6` — the proven rate is valid but far from sharp: the observed decay is `≈ log N/N` (Astra: the argument gives `(1+ℓ)/√N` with the combined-cutoff strengthening; the true order needs a second-order treatment of `γ(v/√N) − γ(0)`). Lean gotchas: `add_le_add_left h c : c + a ≤ c + b` (adds on the LEFT) — use `add_le_add le_rfl h`; `norm_num` rewrites `1/√N` to `(√N)⁻¹` and breaks later `rw`s — obtain constants by `convert … using 2; try norm_num`; `set X := 1/√N` BEFORE the final inequality so that `linarith`/`nlinarith` see one atom; the per-declaration heartbeat budget (`maxHeartbeats 1600000`). | GaussianDepthFourRate.lean |
| **DCLIII** | ★★ **INTERFACES: THE A.E.-MEASURABLE MELLIN TRANSFER, THE FIXED-DOMAIN PARAMETER INTEGRAL, THE CUBE-SET CERTIFICATE (u989; Astra round-16 targets 2–3)**: ★★ `tendsto_mellin_sub_logPolynomial_ae` (DCXLIX with only `AEStronglyMeasurable q (volume.restrict (Ioi 0))`, via the measurable representative `hq.mk`, `ae_restrict_of_ae_restrict_of_subset` and `integral_congr_ae`); ★★ `measurable_fixedDomainIntegral` (`p ↦ ∫ t in (0,1), (t(1−t))⁻¹ h p.1 t (p.2/(t(1−t)))` measurable in `p : Λ × ℝ` from joint measurability of the composed kernel — the shape of the naive-Bayes pushforward density `ρ(λ,μ)`, examples_slop eq. nb_rho_integral; `StronglyMeasurable.integral_prod_right'`); `unitCube`, `measure_pi_restrict_eq_restrict_unitCube` (`Measure.restrict_pi_pi` + `rfl`), `integrableOn_powerLogFaceWeight_cube` (DCXLVIII on the cube as a SET under Lebesgue measure), `integrableOn_of_le_powerLogFaceWeight_cube` (a.e. domination adapter). Not included (Astra): that the naive-Bayes fibre family is such a fixed-domain integral of a jointly measurable kernel, and the fibre integrability. | MellinTransferInterfaces.lean |

## Public statements of the two new files (docstrings + signatures, proofs omitted)
### Grammar/GaussianDepthFourRate.lean
```lean
/-- The third-coefficient limit with the closed form in the target. -/
theorem gaussLaplaceL_third_coeff_closed (m : ℕ) :
    Tendsto (fun N : ℝ => (Real.sqrt N * gaussLaplaceL (m + 4) N -
      gaussCoeffA m * (Real.log N) ^ (m + 3) - gaussCoeffB m * (Real.log N) ^ (m + 2)) /
        (Real.log N) ^ (m + 1)) atTop (𝓝 (thirdCoeffClosed m))

/-- `depthFourTail = mellinLogTail ![C₃, 2B₃, 4A₃]`: the depth-four tail is the log-polynomial tail
of DCXLIX with coefficients `p₀ = C₃`, `p₁ = 2B₃`, `p₂ = 4A₃` (the jet is evaluated at
`2 log v`). -/
theorem depthFourTail_eq_mellinLogTail (v : ℝ) :
    depthFourTail v = mellinLogTail ![depthThreeConst,
      2 * ((2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi),
      4 * (1 / (4 * Real.pi))] v

/-- `∫_R^∞ (1 + 2 log v)/v² dv = (3 + 2 log R)/R` for `R ≥ 1`. -/
theorem integral_Ioi_one_add_two_log_div_sq {R : ℝ} (hR : 1 ≤ R) :
    ∫ v in Ioi R, (1 + 2 * Real.log v) / v ^ 2 = (3 + 2 * Real.log R) / R

/-- `|2∫ γ(v/√N) q₃ − (2/s) Q₃| ≤ (2/s)[1/(2N) + 4(1 + ℓ)/√N + 8(3 + ℓ)/√N]` for `N ≥ 1`. -/
theorem residual_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) -
      2 / Real.sqrt (2 * Real.pi) * depthFourQint| ≤
      2 / Real.sqrt (2 * Real.pi) *
        (1 / (2 * N) + 4 * (1 + Real.log N) / Real.sqrt N +
          8 * (3 + Real.log N) / Real.sqrt N)

def
  -- the difference as one integral
  have hdiff : 2 * (∫ v in Ioi (0 : ℝ), gaussDensity (v / Real.sqrt N) * depthFourQ v) -
      2 / s * depthFourQint =
      2 * ∫ v in Ioi (0 : ℝ), (gaussDensity (v / Real.sqrt N) - 1 / s) * depthFourQ v

/-- ★★★ **The depth-four constant with a rate**: there is `K ≥ 0` with
`|√N Z₄ − A₄ℓ³ − B₄ℓ² − C₄ℓ − D₄| ≤ K(1 + ℓ)²/√N` for all `N ≥ 1`. -/
theorem gaussLaplaceL_four_constant_rate :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
      |Real.sqrt N * gaussLaplaceL 4 N - gaussCoeffA 0 * (Real.log N) ^ 3 -
        gaussCoeffB 0 * (Real.log N) ^ 2 - thirdCoeff 0 * Real.log N - depthFourConst| ≤
        K * (1 + Real.log N) ^ 2 / Real.sqrt N

def
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set A₃ : ℝ := 1 / (4 * Real.pi) with hA₃
  set B₃ : ℝ := (2 * Real.log 2 - Real.eulerMascheroniConstant) / Real.pi with hB₃
  set C₃ : ℝ := depthThreeConst with hC₃
  have hA₃0 : 0 < A₃ := by rw [hA₃]; positivity
  refine ⟨2 / s * (1 / 2 + 4 + 24 + (A₃ + |B₃| + |C₃|) / 2 + (4 * A₃ + 2 * |B₃|) +
    4 * A₃ * (9 / 2)),
    by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have ha0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  set ℓ := Real.log N with hℓdef
  -- the pieces
  have hid := sqrt_mul_gaussLaplaceL_four_sub_eq hN
  have hres := residual_term_bound hN
  have he0 : |∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x| ≤ 1 / 2 * (1 / Real.sqrt N)

def
  set L := (1 + ℓ) ^ 2 with hLdef
  have hres' : |2 * Q - 2 / s * depthFourQint| ≤
      2 / s * (1 / (2 * N) + 4 * (1 + ℓ) * X + 8 * (3 + ℓ) * X)
```

### Grammar/MellinTransferInterfaces.lean
```lean
/-- ★★ DCXLIX with an a.e.-strongly-measurable residual on `(0,∞)`. -/
theorem tendsto_mellin_sub_logPolynomial_ae {d : ℕ} (p : Fin (d + 1) → ℝ) {q : ℝ → ℝ} {a : ℝ}
    (ha : a < 1) (hq : AEStronglyMeasurable q (volume.restrict (Ioi (0 : ℝ))))
    (hsmall : IntegrableOn (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto (fun z : ℝ => (∫ v in Ioi (0 : ℝ), v ^ (z - 1) * (q v + mellinLogTail p v)) -
      ∑ k : Fin (d + 1), p k * ((k : ℕ).factorial : ℝ) / (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ v in Ioi (0 : ℝ), q v))

/-- ★★ The parameter integral `p ↦ ∫ t in (0,1), (t(1−t))⁻¹ h p.1 t (p.2/(t(1−t)))` is measurable
in `p : Λ × ℝ` when the composed kernel is jointly measurable. -/
theorem measurable_fixedDomainIntegral {h : Λ → ℝ → ℝ → ℝ}
    (hh : Measurable fun p : (Λ × ℝ) × ℝ => h p.1.1 p.2 (p.1.2 / (p.2 * (1 - p.2)))) :
    Measurable fun p : Λ × ℝ =>
      ∫ t in Ioo (0 : ℝ) 1, (t * (1 - t))⁻¹ * h p.1 t (p.2 / (t * (1 - t)))

/-- The cube `(0,1)^d` as a set of `Fin d → ℝ`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioo (0 : ℝ) 1

theorem measurableSet_unitCube (d : ℕ) : MeasurableSet (unitCube d)

/-- The product-restricted measure of DCXLVIII is Lebesgue measure restricted to the cube. -/
theorem measure_pi_restrict_eq_restrict_unitCube (d : ℕ) :
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) =
      (volume : Measure (Fin d → ℝ)).restrict (unitCube d)

/-- ★★ DCXLVIII on the cube as a set: the face weight is integrable on `(0,1)^d`. -/
theorem integrableOn_powerLogFaceWeight_cube {d : ℕ} (a : Fin d → ℝ) (k : Fin d → ℕ)
    (ha : ∀ i, -1 < a i) : IntegrableOn (powerLogFaceWeight a k) (unitCube d)

/-- The a.e. domination adapter on the cube: `‖f‖ ≤ C·W` a.e. on the cube suffices. -/
theorem integrableOn_of_le_powerLogFaceWeight_cube {d : ℕ} {a : Fin d → ℝ} {k : Fin d → ℕ}
    (ha : ∀ i, -1 < a i) {f : (Fin d → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f ((volume : Measure (Fin d → ℝ)).restrict (unitCube d)))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)).restrict (unitCube d),
      ‖f x‖ ≤ C * powerLogFaceWeight a k x) :
    IntegrableOn f (unitCube d)
```

## State (pinned to grammar fcfc508)
Formal: §2 Gaussian DLN: `A_L, B_L, C_L` closed at every depth; `C₃` exact; `D₄` as an integral-defined limit WITH a rate; `J`, `Q`, `Γ''(1)`, Mellin transform of `Z₂` closed, residual bridge, jet, abstract and log-polynomial transfer (a.e. version); depth-two two-term expansion, Bessel form. §3 cone: exact `c₂ = −5/6 + √3/π` with `1/√N` rate. §4 blow-up: two-term expansion, family theorem, observable numerators/ratios. §5 rank-one: normal integral and tilts. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter, generic power/log certificate (also on the cube as a set), `m₂`, the fixed-domain parameter-integral measurability shape.
Derivation-only: `J₂ = [(log2−γ)³ + (π²/2)(log2−γ) − 2ζ(3)]/24` and the jet identification of `D₄` (need `Γ'''(1)`/`ζ(3)`); the sharp depth-four rate (`log N/N` observed); constants for `L ≥ 5`; the naive-Bayes envelope exponents per face after the chart Jacobian, the instantiation of the fibre family as a fixed-domain integral of a jointly measurable kernel, KL-vs-surrogate; the blow-up `N^{−3/2}log N` coefficient `√(π/2)/16`; rank-one Morse–Bott; smooth-amplitude tie remainder; cone `c₃`.

## Questions
1. Fidelity check (brief) of DCLII–DCLIII: (a) `residual_term_bound`'s three pieces and the majorant (is `4(1+2 log v)/N` on `(1,√N]` right: `v²/(2sN) · 8(1+2log v)/v² = 4(1+2 log v)/(sN)` ✓?), the cutoff bound `(j+1)^j a/2` used for `j = 0` (weaker than DCXXXI's `a²/2`, giving `ℓ²/(2√N)`) — fine for the stated rate?; (b) the `∃ K` packaging — should the note state the explicit `K` (it is `(2/s)[1/2 + 4 + 24 + (A₃+|B₃|+|C₃|)/2 + 4A₃ + 2|B₃| + 18A₃]`)?; (c) the a.e. transfer's route through `hq.mk` and `ae_restrict_of_ae_restrict_of_subset`; (d) `unitCube`/`measure_pi_restrict_eq_restrict_unitCube` (Lebesgue on `Fin d → ℝ` is `Measure.pi` by `rfl` on this pin).
2. Rank the next three day-sized formal targets by value-per-effort with concrete Lean statements and routes. Candidates: (a) the sharp depth-four rate: the observed `log N/N` suggests the first-order term `−∫(v²/(2sN)) q₃(v) dv`-type correction is what remains; is `O((1+ℓ)/N)` provable by a second-order expansion of `γ(v/√N) − γ(0) + v²/(2sN)` (`|·| ≤ v⁴/(8sN²)`) with the splits, given `∫ v² |q₃|` diverges like `∫ log v`? (i.e. `∫_1^R v² · 8(1+2log v)/v² dv = O(R log R)`, so the first-order term contributes `(1/N)·O(√N log N)` — no; so what IS the mechanism for `log N/N`? Perhaps the first-order term `(1/(2sN))∫ v² q₃(v) dv` is itself a divergent-looking integral whose combination with the tail is finite — please analyse honestly and say what rate is provable day-sized); (b) the all-depth engine: a `PolyJetData` structure `(f, P : polynomial in ℓ, D, m)` with `|f(t) − P(log t)/√t| ≤ D(1+log t)^m/√t` and the step `P_{L+1}(ℓ) = (1/s)∫₀^ℓ P_L + (2/s)Σ_j 2^j P_L^{(j)}(ℓ)H_j/j! + (2/s)Q_L` with a quantitative residual certificate — DCLI/DCLII are the depth-3→4 instance; is the general step day-sized as a theorem about `Polynomial ℝ` (with `Polynomial.eval`, `derivative`, `Polynomial.integral`?) or better as `Fin (n+1) → ℝ` coefficient vectors?; (c) the depth-five constant `D₅` by the same route from DCLII's rate (a concrete second instance before abstracting); (d) `ζ(3)` in Mathlib: is `Γ'''(1) = −γ³ − γπ²/2 − 2ζ(3)` (or `ψ''(1) = −2ζ(3)`) obtainable from Mathlib's `riemannZeta`/`hasSum_zeta_nat`-type results and DCVIII's Mellin derivative machinery? If yes, `J₂` and the jet identification of `D₄` become day-sized; (e) the naive-Bayes fibre family as a fixed-domain integral (instantiate `measurable_fixedDomainIntegral` with the actual `h_t`, from the note's rectangle density); (f) the blow-up `N^{−3/2}log N` coefficient with an explicit remainder, via a second-order treatment of DCXV's reduced integral. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards (`unitCube` vs `Set.pi univ`; `measurable_fixedDomainIntegral`'s kernel argument order `h λ t μ'`; the `∃ K` vs explicit `K`).
Answer concisely with Lean-facing detail.
