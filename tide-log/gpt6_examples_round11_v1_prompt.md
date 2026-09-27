You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 77300e3, 965 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-10 targets ALL landed, plus one closure: (1) DCXXVIII the log-free family remainder `7√(2π)/(√N N^{1/k})` by the whole-integral comparison you proposed; (2) DCXXIX the cone averaged posterior (average of RATIOS: `√N(E_a[Z_N[u₁²;a]/Z_N[1;a]] − ½) → 1/√π`, envelope `(√(2π)|a| + 2)e^{|a|}/c₀` uniform in `0 ≤ δ ≤ 1` — a direct lower bound on the denominator from `|t| ≤ |a| + |t − a|` rather than the tilt-monotonicity lemma — and the value by Fubini) and DCXXX the weighted Leray density `π²e^{−|v|}(1+v+|v|)` of `u₁²e^{−|u|²/2}` (swap symmetry + weighted bipolar reduction), so the theorem is about the 4D model on both sides; (3) DCXXXI the depth-three residual limit `√N Z_3 − [ℓ² + 4(2 log 2 − γ)ℓ]/(4π) → (cR₀ + 2J)/π + (2/s)Q` with `J`, `Q` integral-defined (numerics: `J = R₀²/2 + π²/48` to 1e−12, the constant `0.993766` vs `((4 log 2 − 2γ)² + π²)/(4π) = 0.993766`). Your round-10 correction (`e^zK₀(z) = log(1/z) + log 2 − γ`) was applied and exported as `expK0_two_term_bound`. This is round 11.

## HEADLINES rows DCXXVIII–DCXXXI
| **DCXXVIII** | ★★★ **THE FAMILY `K = x²(x^{2k−2}+y²)/2`: THE LOG-FREE REMAINDER `|Z_k(N) − √(2π)/√N[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤ 7√(2π)/(√N N^{1/k})` (u962; examples_slop §4; Astra round-10 target 1)**: the quartic-defect inner remainder `amp_rem_inner_quartic_le` (`|∫₀¹ (a−1)(2/√(u²+ε) − 2/u)| ≤ Bε` when `1 − a ≤ Bu⁴`, the kernel `2εu³/(u²+ε) ≤ 2εu` — no logarithm), ★ `ampJ_two_term_quartic` (`|J_a(ε) − (log(4/ε) + R_a)| ≤ (4+B)ε`); `monoAmp_near_quartic` (`1 − e^{−u^{2k}/2} ≤ u⁴/2` for `k ≥ 2`), `monoAmp_le_gauss` (`e^{−u^{2k}/2} ≤ e^{1/2}e^{−u²/2}` from `u² ≤ 1 + u^{2k}`), `integral_mul_exp_neg_half_sq_Ioi` (`∫₀^∞ u e^{−u²/2} = 1` from `integral_rpow_mul_exp_neg_mul_rpow`), `exp_half_le_two`; ★★ `ampJ_famAmp_sub_monoAmp_le` (`|J_{a_m}(ε) − J_{a_∞}(ε)| ≤ 2/m²`: the scaled and the fixed amplitudes compared at the level of the WHOLE integrals via `1 − e^{−u²/2m²} ≤ u²/2m²` and `√(u²+ε) ≥ u`, not through the renormalised constants); ★★ `ampJ_monoAmp_two_term` (`≤ 5ε`), `ampJ_famAmp_logFree` (`≤ 7/m²`), `monomialFamily_logFree_m`, ★★★ `monomialFamily_logFree_bound`, `monomialFamily_logFree` (`O(N^{−1/2−1/k})`). Lean gotchas: `le_or_lt` is now `le_or_gt`; `field_simp` closes `(Bu⁴)(2ε/(u(u²+ε))) = 2Bε(u³/(u²+ε))` outright (a trailing `ring` errors with no goals); `neg_div` must be supplied to `linarith` to align `−u²/(2m²)` with `−(u²/(2m²))`. | MonomialFamilyLogFree.lean |
| **DCXXIX** | ★★★ **THE CONE: THE AVERAGED POSTERIOR OF `u₁²` AND ITS FIRST CORRECTION `√N (E_a[Z_N[u₁²;a]/Z_N[1;a]] − ½) → 1/√π` (u963; examples_slop §3, the domination argument the note does not give; Astra round-10 target 2)**: the tilted weight `coneTilt δ a t = e^{−t²/2 + at − δ|t|}`, `coneScaledCorrection δ a = E_{δ,a}[t₊] = ∫ t₊ w/∫ w` with integrability/positivity (`integrable_coneTilt`, `integrable_posPart_coneTilt`, `integral_coneTilt_pos`); the Gaussian-tilt facts `integral_gaussTilt` (`√(2π)e^{a²/2}`), `integrable_abs_gaussTilt`, `integral_abs_mul_exp_neg_half_sq` (`= 2`); ★★ `coneScaledCorrection_le` (`0 ≤ E_{δ,a}[t₊] ≤ (√(2π)|a| + 2)e^{|a|}/c₀` for `0 ≤ δ ≤ 1`, `c₀ = ∫ e^{−|s|−s²/2}`: numerator `≤ e^{a²/2}(√(2π)|a| + 2)`, denominator `≥ e^{−|a|}e^{a²/2}c₀` from `|t| ≤ |a| + |t−a|`); ★★ `cone_posterior_ratio_eq` (`coneNumSq N a/coneDen N a = ½ + N^{−1/2}E_{δ,a}[t₊]` with the Leray densities `π²e^{−|v|}(1+v+|v|)` and `2π²e^{−|v|}`, `coneDen_eq` = `cone_evidence_eq`; substitution `t = √N v` via `Measure.integral_comp_mul_left`); `measurable_coneScaledCorrection` (`StronglyMeasurable.integral_prod_right'`), `integrable_coneEnvelope` (`≤ Ke^{−a²/4}`), `tendsto_coneScaledCorrection` (DCT in `t` as `δ → 0`), `tendsto_integral_coneScaledCorrection` (DCT in `a`); the value ★★ `integral_coneScaledCorrection_zero : ∫ E_{0,a}[t₊]γ(a) = 1/√π` (kernel `K(a,t) = t₊e^{−(t−a)²/2−a²/2}/(2π)`, Fubini via `integrable_prod_iff'`, the `a`-Gaussian `√π e^{−t²/4}`, `∫₀^∞ te^{−t²/4} = 2`); ★★★ `cone_averaged_correction`. The identification of `coneNumSq` with the four-dimensional integral `∫ u₁² e^{−Nq²/2+√N qa}φ` (the weighted Leray density) is the next unit. Numerics `cone_averaged_check.py` (0.5614 at N = 10⁴ vs 0.5642; envelope ratio ≤ 0.27). Lean gotchas: `Integrable.mono'` (no norm on the bound) avoids the `Pi.add` beta-redex under `abs_of_nonneg`; `1 + v + |v|` parses as `(1 + v) + |v|` — `add_assoc` before `add_abs_eq_two_mul_max`; after `set s := √N`, `unfold` re-exposes `√N` — `rw [← hs]`; `field_simp` closes several goals outright (trailing `ring` errors). | ConeAveragedPosterior.lean |
| **DCXXX** | ★★★ **THE LERAY DENSITY OF `u₁² e^{−|u|²/2}` ON THE CONE IS `π² e^{−|v|}(1 + v + |v|)` (u964; examples_slop §3 cor. cone_gaussian; closes the input of DCXXIX)**: the swap `u₁ ↔ u₂` (`swapFirst`, `measurePreserving_swapFirst` via `Measure.prod_swap` and `MeasurePreserving.prod`) preserves `q` and the Gaussian, so `lintegral_cone_sq_swap`/`lintegral_cone_sq_eq_half` (`2∫u₁²(…) = ∫(u₁²+u₂²)(…)`); ★ `lintegral_cone_gauss_weight` (the bipolar reduction of `ConeGaussian` with the radial weight `p = u₁²+u₂²` riding along in the outer polar integral); `integral_mul_exp_neg_Ioi`/`lintegral_mul_exp_neg_Ioi` (`∫_c^∞ p e^{−p} = (c+1)e^{−c}` for `c ≥ 0`, by FTC with `−(p+1)e^{−p}`); ★★ `lintegral_quadrant_weight` (`∫₀^∞∫₀^∞ p G((p−t)/2)e^{−(p+t)/2} = 2∫G(v)e^{−|v|}(1+v+|v|)`, the `p`-integral at `c = max(0,2v)`: `e^{v}(2v+1)e^{−2v} = (1+2v)e^{−v}` for `v ≥ 0`); ★★★ `map_coneQ_gaussian_sq` (the pushforward of `u₁²e^{−|u|²/2}du` along `q`), ★★ `integral_cone_gaussian_sq` (Bochner form for every measurable `g`), ★★ `coneNumSq_eq` (`coneNumSq N a = ∫_{ℝ⁴} u₁² e^{−Nq²/2+√Nqa} e^{−|u|²/2}`): with DCXXIX the averaged first correction `cone_averaged_correction` is now a statement about the four-dimensional model on both sides. Numerics `cone_averaged_check.py` part 4 (Monte Carlo on `ℝ⁴` vs the 1D Leray integral). Lean gotchas: `Measure.volume_eq_prod` needs its type arguments explicit inside `rw`; `MeasurePreserving Prod.swap` from `⟨measurable_swap, Measure.prod_swap⟩`; `Prod.map Prod.swap id` must carry a type ascription on `Prod.swap`; `HasDerivAt.congr_deriv` instead of `convert … using 1` for derivative algebra; `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` is namespaced; `(ae_restrict_iff' hs).2` by `refine` for `≤ᵐ` goals; `lintegral_cone_sq_eq_half` needs `G` explicit (`measurable_const.indicator` does not determine the constant). | ConeLerayWeighted.lean |
| **DCXXXI** | ★★★ **THE DEPTH-THREE GAUSSIAN DLN: THE CONSTANT TERM AS AN INTEGRAL-DEFINED LIMIT `√N Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π) → (cR₀ + 2J)/π + (2/s)Q` (u965; examples_slop §2 eq. dln_gauss at `L = 3`, the `O(1/√N)` residual of DCXXIII identified; Astra round-10 target 3)**: `measurable_gaussLaplace2` (`StronglyMeasurable.integral_prod_right'`), `depthThreeQ v = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/(sv)` with `depthThreeQ_inner` (`= Z_2(v²) ∈ [0,1]` on `(0,1]`), ★ `depthThreeQ_outer_le` (`|q| ≤ 4/(sv²)` from `gaussLaplace2_bounds` at `t = v²` and `log(2v²) + 3 ≤ 8v`), `integrableOn_depthThreeQ`; the constants `gaussJlog = ∫₀^∞ h log x/x`, `depthThreeQint = ∫₀^∞ q`, `depthThreeConst`; the small pieces `tendsto_cutoff_term` (`(log N + c)I_a = O(log N/N)` via `Real.isLittleO_log_id_atTop`), `tendsto_logMoment_term` (`J_a → J`, `|∫₀^a h log x/x| ≤ a/2` by `norm_setIntegral_le_of_norm_le_const`); the substitution `x = v/√N`: `sqrt_mul_inner_eq` (`intervalIntegral.integral_comp_div`), `depthThree_rem_scaled` (`(F − gL)(v/√N) = g(v/√N)q(v)` for `v > 1`, `log(v/√N) = log v − (log N)/2`), `sqrt_mul_rem_eq` (`integral_comp_mul_left_Ioi`); the two dominated convergences `tendsto_inner_term` (bound `1/s` on `(0,1]`) and `tendsto_rem_term` (bound `|q|/s` on `(1,∞)`); ★ `sqrt_mul_gaussLaplaceL_three_eq` (the DCXXIII decomposition scaled by `√N`); ★★★ `gaussLaplaceL_three_residual`. The exact values `J = R₀²/2 + π²/48` and `Q = (c² + 5π²/6)/(4s)` (giving `((4 log 2 − 2γ)² + π²)/(4π) = 0.99377`) stay derivations, checked numerically (`gauss_depth3_residual_check.py`: `J`, `Q` to 1e−6, constant 0.993766). Lean gotchas: `indicator_apply` + `if_neg (fun h : v ∈ Ioi 1 => …)` (the condition is membership, not `1 < v`); `measureReal_def` before `Real.volume_Ioc` (`norm_setIntegral_le_of_norm_le_const` now returns `volume.real`); `intervalIntegral.integral_of_le (a := …) (b := …)` explicit or the wrong interval converts; `tendsto_integral_filter_of_dominated_convergence` needs `F`/`f` explicit; `inv_div, div_one` for `(1/√N)⁻¹`. | GaussianDepthThreeResidual.lean |

## Public statements of the four new files (docstrings + signatures, proofs omitted)
### Grammar/MonomialFamilyLogFree.lean
```lean
/-- `|∫₀¹ (a(u) − 1)(2/√(u² + ε) − 2/u) du| ≤ B ε` when `1 − a(u) ≤ B u⁴` on `(0,1]`. -/
theorem amp_rem_inner_quartic_le (h : AmpData a A) {B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ u ∈ Ioc (0 : ℝ) 1, 1 - a u ≤ B * u ^ 4) {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤ B * ε

/-- The log-free two-term expansion for an amplitude with a quartic defect at zero:
`|J_a(ε) − (log(4/ε) + R_a)| ≤ (4 + B) ε` for `0 < ε ≤ 1`. -/
theorem ampJ_two_term_quartic (h : AmpData a A) {B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ u ∈ Ioc (0 : ℝ) 1, 1 - a u ≤ B * u ^ 4) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ a ε - (Real.log (4 / ε) + ampRenorm a)| ≤ (4 + B) * ε

/-- `1 − e^{−u^{2k}/2} ≤ u⁴/2` on `(0,1]` for `k ≥ 2`. -/
theorem monoAmp_near_quartic {k : ℕ} (hk : 2 ≤ k) :
    ∀ u ∈ Ioc (0 : ℝ) 1, 1 - monoAmp k u ≤ 1 / 2 * u ^ 4

/-- `e^{−u^{2k}/2} ≤ e^{1/2} e^{−u²/2}` for `u ≥ 0`, `k ≥ 1` (`u² ≤ 1 + u^{2k}`). -/
theorem monoAmp_le_gauss {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    monoAmp k u ≤ Real.exp (1 / 2) * Real.exp (-u ^ 2 / 2)

/-- `∫₀^∞ u e^{−u²/2} du = 1`. -/
theorem integral_mul_exp_neg_half_sq_Ioi :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-u ^ 2 / 2) = 1

/-- `u e^{−u²/2}` is integrable on `(0,∞)`. -/
theorem integrableOn_mul_exp_neg_half_sq_Ioi :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) (Ioi 0)

/-- `e^{1/2} ≤ 2`. -/
theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2

/-- `|J_{a_m}(ε) − J_{a_∞}(ε)| ≤ 2/m²` for `m ≥ 1`, `k ≥ 1`, `ε > 0`: the scaled amplitude
`a_m = a_∞ · e^{−u²/2m²}` differs from the monomial amplitude by at most `a_∞(u) u²/(2m²)`, and
`2 a_∞(u) (u²/2m²)/√(u² + ε) ≤ e^{1/2} u e^{−u²/2}/m²`. -/
theorem ampJ_famAmp_sub_monoAmp_le {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 1 ≤ m) {ε : ℝ}
    (hε : 0 < ε) :
    |ampJ (famAmp k m) ε - ampJ (monoAmp k) ε| ≤ 2 / m ^ 2

/-- ★★ `|J_{a_∞}(ε) − (log(4/ε) + (log 2 − γ)/k)| ≤ 5ε` for `0 < ε ≤ 1`, `k ≥ 2`. -/
theorem ampJ_monoAmp_two_term {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (monoAmp k) ε -
      (Real.log (4 / ε) + (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤ 5 * ε

/-- ★★ `|J_{a_m}(m^{2−2k}) − (2 log 2 + (2k−2) log m + (log 2 − γ)/k)| ≤ 7/m²` for `m ≥ 1`,
`k ≥ 2`. -/
theorem ampJ_famAmp_logFree {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) -
      (2 * Real.log 2 + (2 * k - 2) * Real.log m +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤ 7 / m ^ 2

/-- The `m`-form: for `m ≥ 1`, `k ≥ 2`,
`|Z_k(m^{2k}) − √(2π)/m^k · (2(k−1) log m + 2 log 2 + (log 2 − γ)/k)| ≤ √(2π)/m^k · 7/m²`. -/
theorem monomialFamily_logFree_m {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |monomialFamilyZ k (m ^ (2 * k)) - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) / m ^ k * (7 / m ^ 2)

/-- ★★★ **The log-free two-term expansion of the family**: for `N ≥ 1` and `k ≥ 2`,
`|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤ 7√(2π)/(√N · N^{1/k})`. -/
theorem monomialFamily_logFree_bound {k : ℕ} (hk : 2 ≤ k) {N : ℝ} (hN : 1 ≤ N) :
    |monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      7 * Real.sqrt (2 * Real.pi) / (Real.sqrt N * N ^ (1 / (k : ℝ)))

/-- ★★★ `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2−1/k})`
for every `k ≥ 2`: the log-free remainder. -/
theorem monomialFamily_logFree {k : ℕ} (hk : 2 ≤ k) :
    (fun N : ℝ => monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k))
      =O[atTop] fun N => 1 / (Real.sqrt N * N ^ (1 / (k : ℝ)))

```

### Grammar/ConeAveragedPosterior.lean
```lean
/-- The tilted weight `w_{δ,a}(t) = e^{−t²/2 + a t − δ|t|}`. -/
noncomputable def coneTilt (δ a t : ℝ) : ℝ

theorem coneTilt_pos (δ a t : ℝ) : 0 < coneTilt δ a t

theorem continuous_coneTilt (δ a : ℝ) : Continuous (coneTilt δ a)

/-- The Gaussian tilt completes the square: `e^{−t²/2 + at} = e^{a²/2} e^{−(t−a)²/2}`. -/
theorem gaussTilt_eq (a t : ℝ) :
    Real.exp (-t ^ 2 / 2 + a * t) = Real.exp (a ^ 2 / 2) * Real.exp (-(t - a) ^ 2 / 2)

theorem integrable_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2 / 2 + a * t))

/-- `∫ e^{−t²/2 + at} dt = √(2π) e^{a²/2}`. -/
theorem integral_gaussTilt (a : ℝ) :
    ∫ t : ℝ, Real.exp (-t ^ 2 / 2 + a * t) = Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2)

/-- `∫ |t| e^{−t²/2} dt = 2`. -/
theorem integral_abs_mul_exp_neg_half_sq : ∫ t : ℝ, |t| * Real.exp (-t ^ 2 / 2) = 2

theorem integrable_abs_mul_exp_neg_half_sq :
    Integrable (fun t : ℝ => |t| * Real.exp (-t ^ 2 / 2))

theorem integrable_abs_gaussTilt (a : ℝ) :
    Integrable (fun t : ℝ => |t| * Real.exp (-t ^ 2 / 2 + a * t))

theorem coneTilt_le {δ : ℝ} (hδ : 0 ≤ δ) (a t : ℝ) :
    coneTilt δ a t ≤ Real.exp (-t ^ 2 / 2 + a * t)

theorem integrable_coneTilt {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) : Integrable (coneTilt δ a)

theorem integrable_posPart_coneTilt {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    Integrable (fun t : ℝ => max t 0 * coneTilt δ a t)

theorem integral_coneTilt_pos {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) : 0 < ∫ t, coneTilt δ a t

/-- `E_{δ,a}[t₊] = ∫ t₊ w_{δ,a} / ∫ w_{δ,a}`: the scaled first correction at the field `a`. -/
noncomputable def coneScaledCorrection (δ a : ℝ) : ℝ

theorem coneScaledCorrection_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    0 ≤ coneScaledCorrection δ a

/-- `c₀ = ∫ e^{−|s| − s²/2} ds`. -/
noncomputable def coneC₀ : ℝ

theorem integrable_coneC₀ : Integrable (fun s : ℝ => Real.exp (-|s| - s ^ 2 / 2))

theorem coneC₀_pos : 0 < coneC₀

/-- The denominator from below: `∫ w_{δ,a} ≥ e^{−|a|} e^{a²/2} c₀` for `0 ≤ δ ≤ 1`. -/
theorem integral_coneTilt_ge {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    Real.exp (-|a|) * Real.exp (a ^ 2 / 2) * coneC₀ ≤ ∫ t, coneTilt δ a t

/-- The numerator from above: `∫ t₊ w_{δ,a} ≤ e^{a²/2}(√(2π)|a| + 2)` for `δ ≥ 0`. -/
theorem integral_posPart_coneTilt_le {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    ∫ t, max t 0 * coneTilt δ a t ≤ Real.exp (a ^ 2 / 2) * (Real.sqrt (2 * Real.pi) * |a| + 2)

/-- ★★ **The envelope**: `0 ≤ E_{δ,a}[t₊] ≤ (√(2π)|a| + 2) e^{|a|}/c₀` for `0 ≤ δ ≤ 1`. -/
theorem coneScaledCorrection_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    coneScaledCorrection δ a ≤ (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀

/-- `v + |v| = 2 max(v, 0)`. -/
theorem add_abs_eq_two_mul_max (v : ℝ) : v + |v| = 2 * max v 0

/-- `Z_N[u₁²; a]` through its Leray density `π² e^{−|v|}(1 + v + |v|)` (examples_slop §3). -/
noncomputable def coneNumSq (N a : ℝ) : ℝ

/-- `Z_N[1; a]` through its Leray density `2π² e^{−|v|}`. -/
noncomputable def coneDen (N a : ℝ) : ℝ

/-- The denominator is the four-dimensional frozen partition function (`cone_evidence_eq`). -/
theorem coneDen_eq (N a : ℝ) :
    coneDen N a = ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * gaussW u

/-- ★★ **The frozen ratio**: `Z_N[u₁²; a]/Z_N[1; a] = ½ + N^{−1/2} E_{δ,a}[t₊]`, `δ = N^{−1/2}`. -/
theorem cone_posterior_ratio_eq {N : ℝ} (hN : 0 < N) (a : ℝ) :
    coneNumSq N a / coneDen N a =
      1 / 2 + 1 / Real.sqrt N * coneScaledCorrection (1 / Real.sqrt N) a

theorem continuous_coneTilt_pair (δ : ℝ) : Continuous fun p : ℝ × ℝ => coneTilt δ p.1 p.2

theorem measurable_coneScaledCorrection (δ : ℝ) :
    Measurable fun a => coneScaledCorrection δ a

/-- The envelope `(√(2π)|a| + 2) e^{|a|}/c₀ · γ(a)` is integrable: it is at most
`K e^{−a²/4}` with `K = (√(2π) + 2) e⁴/(√(2π) c₀)`. -/
theorem integrable_coneEnvelope :
    Integrable (fun a : ℝ =>
      (Real.sqrt (2 * Real.pi) * |a| + 2) * Real.exp |a| / coneC₀ * gaussDensity a)

theorem tendsto_one_div_sqrt : Tendsto (fun N : ℝ => 1 / Real.sqrt N) atTop (𝓝 0)

theorem continuous_coneTilt_delta (a t : ℝ) : Continuous fun δ => coneTilt δ a t

/-- `E_{δ,a}[t₊] → E_{0,a}[t₊]` as `δ = N^{−1/2} → 0`, by dominated convergence in `t`. -/
theorem tendsto_coneScaledCorrection (a : ℝ) :
    Tendsto (fun N : ℝ => coneScaledCorrection (1 / Real.sqrt N) a) atTop
      (𝓝 (coneScaledCorrection 0 a))

/-- The average over the sample field converges,
`∫ E_{δ_N,a}[t₊] γ(a) da → ∫ E_{0,a}[t₊] γ(a) da`, by dominated convergence under the envelope. -/
theorem tendsto_integral_coneScaledCorrection :
    Tendsto (fun N : ℝ => ∫ a, coneScaledCorrection (1 / Real.sqrt N) a * gaussDensity a) atTop
      (𝓝 (∫ a, coneScaledCorrection 0 a * gaussDensity a))

/-- At `δ = 0`: `E_{0,a}[t₊] = ∫ t₊ e^{−t²/2 + at} / (√(2π) e^{a²/2})`. -/
theorem coneScaledCorrection_zero (a : ℝ) :
    coneScaledCorrection 0 a = (∫ t, max t 0 * Real.exp (-t ^ 2 / 2 + a * t)) /
      (Real.sqrt (2 * Real.pi) * Real.exp (a ^ 2 / 2))

/-- The kernel `K(a,t) = t₊ e^{−(t−a)²/2 − a²/2}/(2π)`. -/
noncomputable def coneKernel (a t : ℝ) : ℝ

theorem continuous_coneKernel : Continuous fun p : ℝ × ℝ => coneKernel p.1 p.2

theorem coneKernel_nonneg (a t : ℝ) : 0 ≤ coneKernel a t

/-- `E_{0,a}[t₊] γ(a) = ∫ K(a,t) dt`. -/
theorem coneScaledCorrection_zero_mul_gaussDensity (a : ℝ) :
    coneScaledCorrection 0 a * gaussDensity a = ∫ t, coneKernel a t

/-- `K(a,t) = [t₊ e^{−t²/4}/(2π)] e^{−(a − t/2)²}`. -/
theorem coneKernel_eq (a t : ℝ) :
    coneKernel a t = max t 0 * Real.exp (-t ^ 2 / 4) / (2 * Real.pi) *
      Real.exp (-(1 : ℝ) * (a - t / 2) ^ 2)

/-- The `a`-integral of the kernel: `∫ K(a,t) da = t₊ √π e^{−t²/4}/(2π)`. -/
theorem integral_coneKernel_left (t : ℝ) :
    ∫ a, coneKernel a t = max t 0 * Real.exp (-t ^ 2 / 4) / (2 * Real.pi) * Real.sqrt Real.pi

theorem integrable_coneKernel_slice (t : ℝ) : Integrable (fun a => coneKernel a t)

/-- `∫₀^∞ t e^{−t²/4} dt = 2`. -/
theorem integral_mul_exp_neg_quarter_sq_Ioi :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-t ^ 2 / 4) = 2

theorem integrable_coneKernel_uncurry :
    Integrable (Function.uncurry fun a t => coneKernel a t) (volume.prod volume)

/-- ★★ `∫ E_{0,a}[t₊] γ(a) da = E[(a + G)₊] = 1/√π`: Fubini on the kernel, the `a`-integral is a
Gaussian, and `∫₀^∞ t e^{−t²/4} dt = 2`. -/
theorem integral_coneScaledCorrection_zero :
    ∫ a, coneScaledCorrection 0 a * gaussDensity a = 1 / Real.sqrt Real.pi

/-- ★★★ **The averaged first correction of the cone posterior**: with the sample field
`a ∼ N(0,1)`, `√N (E_a[Z_N[u₁²; a]/Z_N[1; a]] − ½) → 1/√π` (the average of the RATIOS; the
average of the evidences is the prior mass). -/
theorem cone_averaged_correction :
    Tendsto (fun N : ℝ => Real.sqrt N *
      ((∫ a, coneNumSq N a / coneDen N a * gaussDensity a) - 1 / 2)) atTop
      (𝓝 (1 / Real.sqrt Real.pi))

```

### Grammar/ConeLerayWeighted.lean
```lean
/-- The swap of the first pair. -/
def swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ)

theorem coneQ_swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : coneQ (swapFirst u) = coneQ u

theorem gaussW_swapFirst (u : (ℝ × ℝ) × (ℝ × ℝ)) : gaussW (swapFirst u) = gaussW u

theorem measurePreserving_swapFirst : MeasurePreserving swapFirst volume volume

/-- `∫ u₁² G(q) W = ∫ u₂² G(q) W` (lower integrals). -/
theorem lintegral_cone_sq_swap (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u))

/-- `2 ∫ u₁² G(q) W = ∫ (u₁² + u₂²) G(q) W`. -/
theorem lintegral_cone_sq_eq_half (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    2 * ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2 + u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u))

/-- The bipolar reduction with the weight `u₁² + u₂² = p`:
`∫ (u₁² + u₂²) G(q) e^{−|u|²/2} = π² ∫₀^∞ p ∫₀^∞ G((p − t)/2) e^{−(p+t)/2} dt dp`. -/
theorem lintegral_cone_gauss_weight (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u : (ℝ × ℝ) × (ℝ × ℝ),
        ENNReal.ofReal (u.1.1 ^ 2 + u.1.2 ^ 2) * (G (coneQ u) * ENNReal.ofReal (gaussW u)) =
      ENNReal.ofReal Real.pi * (ENNReal.ofReal Real.pi *
        ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)))

theorem integral_mul_exp_neg_Ioi {c : ℝ} (hc : 0 ≤ c) :
    ∫ p in Ioi c, p * Real.exp (-p) = (c + 1) * Real.exp (-c)

theorem lintegral_mul_exp_neg_Ioi {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ p in Ioi c, ENNReal.ofReal (p * Real.exp (-p)) =
      ENNReal.ofReal ((c + 1) * Real.exp (-c))

/-- ★★ **The weighted quadrant integral is the weighted Leray integral**:
`∫₀^∞∫₀^∞ p G((p − t)/2) e^{−(p+t)/2} dt dp = 2 ∫_ℝ G(v) e^{−|v|}(1 + v + |v|) dv`. -/
theorem lintegral_quadrant_weight (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)) =
      2 * ∫⁻ v, G v * ENNReal.ofReal (Real.exp (-|v|) * (1 + v + |v|))

/-- ★★★ **The Leray density of `u₁² e^{−|u|²/2}` is `π² e^{−|v|}(1 + v + |v|)`**: the pushforward
of `u₁² e^{−|u|²/2} du` along `q`. -/
theorem map_coneQ_gaussian_sq :
    Measure.map coneQ (volume.withDensity fun u => ENNReal.ofReal (u.1.1 ^ 2 * gaussW u)) =
      volume.withDensity fun v =>
        ENNReal.ofReal (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))

/-- ★★ **The Bochner form**: for every measurable `g`,
`∫_{ℝ⁴} g(q(u)) u₁² e^{−|u|²/2} du = ∫_ℝ g(v) π² e^{−|v|}(1 + v + |v|) dv`. -/
theorem integral_cone_gaussian_sq (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ u : (ℝ × ℝ) × (ℝ × ℝ), g (coneQ u) * (u.1.1 ^ 2 * gaussW u) =
      ∫ v, g v * (Real.pi ^ 2 * Real.exp (-|v|) * (1 + v + |v|))

/-- ★★ **The numerator of the cone posterior is the four-dimensional frozen numerator**:
`coneNumSq N a = ∫_{ℝ⁴} u₁² e^{−N q²/2 + √N q a} e^{−|u|²/2} du`. -/
theorem coneNumSq_eq (N a : ℝ) :
    coneNumSq N a = ∫ u : (ℝ × ℝ) × (ℝ × ℝ),
      Real.exp (-N * coneQ u ^ 2 / 2 + Real.sqrt N * coneQ u * a) * (u.1.1 ^ 2 * gaussW u)

```

### Grammar/GaussianDepthThreeResidual.lean
```lean
theorem measurable_gaussLaplace2 : Measurable gaussLaplace2

/-- `q(v) = Z_2(v²) − 1_{(1,∞)}(v)(2 log v + c)/(s v)`, `c = 3 log 2 − γ`, `s = √(2π)`. -/
noncomputable def depthThreeQ (v : ℝ) : ℝ

theorem measurable_depthThreeQ : Measurable depthThreeQ

theorem depthThreeQ_inner {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) :
    depthThreeQ v = gaussLaplace2 (v ^ 2)

/-- On `(1,∞)`: `|q(v)| ≤ 4/(s v²)`, from `gaussLaplace2_bounds` at `t = v²`. -/
theorem depthThreeQ_outer_le {v : ℝ} (hv : 1 < v) :
    |depthThreeQ v| ≤ 4 / (Real.sqrt (2 * Real.pi) * v ^ 2)

theorem integrableOn_depthThreeQ_inner : IntegrableOn depthThreeQ (Ioc 0 1)

theorem integrableOn_depthThreeQ_outer : IntegrableOn depthThreeQ (Ioi 1)

theorem integrableOn_depthThreeQ : IntegrableOn depthThreeQ (Ioi 0)

/-- `J = ∫₀^∞ h(x) log x/x dx`. -/
noncomputable def gaussJlog : ℝ

/-- `Q = ∫₀^∞ q(v) dv`. -/
noncomputable def depthThreeQint : ℝ

/-- The depth-three constant `(c R₀ + 2J)/π + (2/s) Q`. -/
noncomputable def depthThreeConst : ℝ

theorem tendsto_log_div_atTop : Tendsto (fun N : ℝ => Real.log N / N) atTop (𝓝 0)

/-- `(log N + c) I_a → 0`, `I_a = ∫₀^a h/x`, `|I_a| ≤ a²/2 = 1/(2N)`. -/
theorem tendsto_cutoff_term :
    Tendsto (fun N : ℝ => (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
      ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) atTop (𝓝 0)

/-- `J_a = ∫_a^∞ h log x/x → J` as `a = N^{−1/2} → 0`. -/
theorem tendsto_logMoment_term :
    Tendsto (fun N : ℝ => ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) atTop
      (𝓝 gaussJlog)

theorem gaussDensity_zero : gaussDensity 0 = 1 / Real.sqrt (2 * Real.pi)

theorem depthThreeF_scaled {N v : ℝ} (hN : 0 < N) :
    depthThreeF N (v / Real.sqrt N) = gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2)

/-- `√N ∫₀^a F_N = ∫₀^1 g(v/√N) Z_2(v²) dv`. -/
theorem sqrt_mul_inner_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x =
      ∫ v in Ioc (0 : ℝ) 1, gaussDensity (v / Real.sqrt N) * gaussLaplace2 (v ^ 2)

theorem tendsto_inner_term :
    Tendsto (fun N : ℝ => Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x)
      atTop (𝓝 (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioc (0 : ℝ) 1, depthThreeQ v))

/-- The remainder integrand at `x = v/√N` is `g(v/√N) q(v)` for `v > 1`. -/
theorem depthThree_rem_scaled {N v : ℝ} (hN : 0 < N) (hv : 1 < v) :
    depthThreeF N (1 / Real.sqrt N * v) - gaussDensity (1 / Real.sqrt N * v) *
      ((Real.log N + 2 * Real.log (1 / Real.sqrt N * v) +
        3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * (1 / Real.sqrt N * v)))) =
      gaussDensity (1 / Real.sqrt N * v) * depthThreeQ v

/-- `√N ∫_a^∞ (F_N − gL_N) = ∫₁^∞ g(v/√N) q(v) dv`. -/
theorem sqrt_mul_rem_eq {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) =
      ∫ v in Ioi (1 : ℝ), gaussDensity (v / Real.sqrt N) * depthThreeQ v

theorem tendsto_rem_term :
    Tendsto (fun N : ℝ => Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x -
      gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi) * ∫ v in Ioi (1 : ℝ), depthThreeQ v))

/-- The DCXXIII decomposition, scaled by `√N`: for `N ≥ 1`,
`√N Z_3 − [ℓ² + 4(2 log 2 − γ)ℓ]/(4π) = 2√N I₀ + 2√N E + (1/π)(c d/2 − (ℓ + c) I_a + 2 J_a)`. -/
theorem sqrt_mul_gaussLaplaceL_three_eq {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) / (4 * Real.pi) =
      2 * (Real.sqrt N * ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) +
      2 * (Real.sqrt N * ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))) +
      1 / Real.pi * ((3 * Real.log 2 - Real.eulerMascheroniConstant) *
          ((Real.log 2 - Real.eulerMascheroniConstant) / 2) -
        (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
          (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        2 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x)

/-- ★★★ **The depth-three constant as a limit**:
`√N Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π) → (c R₀ + 2J)/π + (2/s) Q`. -/
theorem gaussLaplaceL_three_residual :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) / (4 * Real.pi)) atTop
      (𝓝 depthThreeConst)

```


## The naive Bayes adapter and envelope (DCXIII, DCXVII) — the definitions you asked for
### Grammar/LogSqDominationAdapter.lean
```lean
theorem

`Grammar.AveragedFibrePolar` averages the fibre polar distributions of the naive Bayes model
(`Grammar.LogSquareDensityPolar`) under an abstract hypothesis: the holomorphic remainders `H_λ`
have derivatives dominated by an integrable function of `λ`.  This file derives that hypothesis
from the fibre data, on a ball `|s − ½| < r`, `0 < r < ½` (Astra round-5 target 3):

* `norm_deriv_mellinIoc_le`: for `‖g(t)‖ ≤ C t^b` on `(0,1]` and `Re s ≤ σ` with `b − 2σ > −1`,
  `‖(M g)'(s)‖ ≤ 2C/(b − 2σ + 1)²` (the exact log-moment `∫₀¹ t^a |log t| dt = 1/(a+1)²`);
* `norm_deriv_mellinIoc_cutoff_le`: for a cutoff integrand `1_{(M,1]} g` with `‖g‖ ≤ K` there and
  `Re s ≤ ½ + r`, `‖(M[1_{(M,1]} g])'(s)‖ ≤ K |log M| M^{−2r}/r` — the negative moment `M^{−2r}`
  of the cutoff, as the consult predicted;
* ★★ `norm_deriv_logSqHolo_le`: the derivative of the fibre remainder `logSqHolo ℓ c b M φ` on the
  ball is bounded by the explicit `logSqDomBound ℓ c b M L φ(0) r`, a polynomial in
  `ℓ, |c|, |b|, L, |φ(0)|, |log M|` times `(1 + M^{−2r})`;
* `averaged_logSq_polar_ball`: the averaged theorem on a ball around `½` (only a neighbourhood is
  needed for the polar conclusion);
* ★★★ `averaged_naiveBayes_polar`: for a measurable family of fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)`
  with `0 < M_λ ≤ 1` and `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, if the polar coefficients and the explicit
  bound are `ν`-integrable (and the remainders are measurable and integrable in `λ` at each `s`),
  the averaged continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`:
  `C̄_{½,3} = −∫φ_λ(0)`, `C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`;
  `integral_logSqMellinFull_eq` identifies it with the averaged fibre Mellin transform on the
  strip `Re s < ½`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The real log-moment and the two derivative bounds -/

/-- `∫₀¹ t^a |log t| dt = 1/(a + 1)²` for `a > −1`. -/
theorem integral_rpow_mul_abs_log_Ioc {a : ℝ} (ha : -1 < a) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ a * |Real.log t| = 1 / (a + 1) ^ 2

/-- Derivative domination for a power-bounded Mellin integrand: `‖g(t)‖ ≤ C t^b` on `(0,1]` and
`Re s ≤ σ` with `b − 2σ > −1` give `‖(M g)'(s)‖ ≤ 2C/(b − 2σ + 1)²`. -/
theorem norm_deriv_mellinIoc_le {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1))) {C b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ b) {σ : ℝ} (hσ : -1 < b - 2 * σ) {s : ℂ}
    (hs : s.re ≤ σ) :
    ‖deriv (mellinIoc g) s‖ ≤ 2 * C / (b - 2 * σ + 1) ^ 2

/-- Derivative domination for a cutoff integrand: `g` bounded by `K` on `(M, 1]`, `0 < M ≤ 1`,
`Re s ≤ ½ + r`, `0 < r < ½`: `‖(M[1_{(M,1]} g])'(s)‖ ≤ K |log M| M^{−2r}/r`. -/
theorem norm_deriv_mellinIoc_cutoff_le {g : ℝ → ℂ} (hg : Measurable g) {K : ℝ} (hK : 0 ≤ K)
    {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) (hb : ∀ t ∈ Ioc M 1, ‖g t‖ ≤ K) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) {s : ℂ} (hs : s.re ≤ 1 / 2 + r) :
    ‖deriv (mellinIoc ((Ioc M 1).indicator g)) s‖ ≤ K * |Real.log M| * M ^ (-2 * r) / r

/-- The explicit dominating constant for `(logSqHolo ℓ c b M φ)'` on `|s − ½| < r`: the four
pieces (even remainder, even cutoff, odd part, odd cutoff). -/
noncomputable def logSqDomBound (ℓ c b M L φ₀ r : ℝ) : ℝ

/-- The odd amplitude bound `‖b(φ(t) − φ(−t))‖ ≤ 2|b|L t` on `(0, 1]`. -/
theorem norm_logSqOddAmp_le (b : ℝ) {φ : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖logSqOddAmp b φ t‖ ≤ 2 * |b| * L * t ^ (1 : ℝ)

theorem measurable_logSqOddAmp (b : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Measurable (logSqOddAmp b φ)

/-- The even amplitude is bounded on `(M, 1]` by `(2(|ℓ| + |log M|)² + |c|)(2|φ(0)| + 2L)`. -/
theorem norm_logSqAmp_symm_cutoff_le (ℓ c : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|) :
    ∀ t ∈ Ioc M 1, ‖logSqAmp ℓ c (symmAmp φ) t‖ ≤
      (2 * (|ℓ| + |Real.log M|) ^ 2 + |c|) * (2 * |φ 0| + 2 * L)

/-- `|s − ½| < r` gives `Re s ≤ ½ + r`. -/
theorem re_le_of_mem_ball_half {r : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    s.re ≤ 1 / 2 + r

/-- ★★ **Derivative domination for the fibre remainder**: on the ball `|s − ½| < r`, `0 < r < ½`,
`‖(logSqHolo ℓ c b M φ)'(s)‖ ≤ logSqDomBound ℓ c b M L φ(0) r`. -/
theorem norm_deriv_logSqHolo_le (ℓ c b : ℝ) {M : ℝ} (hM0 : 0 < M) (hM1 : M ≤ 1) {φ : ℝ → ℝ}
    (hφ : Continuous φ) {L : ℝ} (hL : ∀ t ∈ Icc (-1 : ℝ) 1, |φ t - φ 0| ≤ L * |t|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) :
    ‖deriv (logSqHolo ℓ c b M φ) s‖ ≤ logSqDomBound ℓ c b M L (φ 0) r

theorem on a ball and the naive Bayes corollary -/

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}

/-- The averaged polar theorem on a ball `|s − ½| < r` with a single dominating function `B`. -/
theorem averaged_logSq_polar_ball {φ₀ ℓ c : Λ → ℝ} {H : Λ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ₀ l) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, AEStronglyMeasurable (fun l => H l s) ν)
    (hdiff : ∀ᵐ l ∂ν, DifferentiableOn ℂ (H l) (Metric.ball (1 / 2 : ℂ) r))
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, Integrable (fun l => H l s) ν)
    {B : Λ → ℝ} (hB : Integrable B ν)
    (hdom : ∀ᵐ l ∂ν, ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv (H l) s‖ ≤ B l) :
    (fun s => (∫ l, (((2 * φ₀ l : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s + H l s) ∂ν) -
      polarPart 2 (logSqAvgA φ₀ ℓ c ν) (1 / 2 : ℂ) s) =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ)

/-- On the strip `Re s < ½` the averaged fibre Mellin transform is the averaged continuation. -/
theorem integral_logSqMellinFull_eq {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ}
    (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ l, logSqMellinFull (ℓ l) (c l) (b l) (M l) (φ l) s ∂ν =
      ∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
        logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν

/-- ★★★ **The averaged naive Bayes polar distributions from the fibre data**: for a family of
fibres `(ℓ_λ, c_λ, b_λ, M_λ, φ_λ)` with `0 < M_λ ≤ 1` and `|φ_λ(t) − φ_λ(0)| ≤ L_λ|t|`, if the
fibre polar coefficients and the explicit bound `logSqDomBound` are `ν`-integrable (and the
remainders are measurable and integrable in `λ` at each `s` of the ball `|s − ½| < r`), the averaged
continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`: `C̄_{½,3} = −∫φ_λ(0)`,
`C̄_{½,2} = 2∫ℓ_λφ_λ(0)`, `C̄_{½,1} = ∫(c_λ − 2ℓ_λ²)φ_λ(0)`. -/
theorem averaged_naiveBayes_polar {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ} {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1) (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ l 0) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      AEStronglyMeasurable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hint : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      Integrable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hB : Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r) ν) :
    (fun s => (∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
      logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν) -
      polarPart 2 (logSqAvgA (fun l => φ l 0) ℓ c ν) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ)

```

### Grammar/LogSqEnvelopeCertificate.lean
```lean
theorem

`Grammar.LogSqDominationAdapter` bounds the derivative of the fibre remainder by the explicit
`logSqDomBound`.  This file makes that bound usable facewise (Astra round-6 target 2):

* ★★ `logSqDomBound_le_envelope`: for fixed `0 < r < ½`,
  `logSqDomBound ℓ c b M L φ₀ r ≤ envelopeConst r · W · (1 + M^{−2r})(1 + |log M|⁴)` with the weight
  `W = (1 + |φ₀| + L)(1 + ℓ² + |c| + |b|)` — the consult's coarse envelope, so that near a face with
  `M ≳ d^β`, `W ≲ d^{−η}` and `dν ≲ d^{a−1} dd` the condition is `η + 2rβ < a`;
* `integrable_logSqDomBound_of_envelope`: integrability of the bound from integrability of the
  envelope (measurable fibre data);
* `norm_sub_le_of_deriv_le_ball`: the mean value inequality `‖H(s) − H(½)‖ ≤ B r` on the ball;
* ★★★ `averaged_naiveBayes_polar_basepoint`: the averaged polar theorem with the remainders
  required to be integrable at the single basepoint `s = ½` only (plus the integrable envelope):
  the analytic hypotheses of `averaged_naiveBayes_polar` are discharged from the fibre data.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### Elementary polynomial bounds -/

theorem le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ 4

theorem pow_three_le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 1 + x ^ 4

/-- The envelope constant `C_r` of the coarse bound. -/
noncomputable def envelopeConst (r : ℝ) : ℝ

/-- ★★ **The coarse envelope**: for `0 < r < ½`, `M > 0`, `L ≥ 0`,
`logSqDomBound ℓ c b M L φ₀ r ≤
  C_r (1 + |φ₀| + L)(1 + ℓ² + |c| + |b|)(1 + M^{−2r})(1 + |log M|⁴)`. -/
theorem logSqDomBound_le_envelope {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2)
    (hM0 : 0 < M) (hL : 0 ≤ L) :
    logSqDomBound ℓ c b M L φ₀ r ≤ envelopeConst r *
      ((1 + |φ₀| + L) * (1 + ℓ ^ 2 + |c| + |b|)) * (1 + M ^ (-2 * r)) *
        (1 + |Real.log M| ^ 4)

theorem logSqDomBound_nonneg {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hM0 : 0 < M) (hL : 0 ≤ L) :
    0 ≤ logSqDomBound ℓ c b M L φ₀ r

theorem measurable_logSqDomBound {ℓ c b M L φ₀ : Λ → ℝ} (hℓ : Measurable ℓ) (hc : Measurable c)
    (hb : Measurable b) (hM : Measurable M) (hL : Measurable L) (hφ : Measurable φ₀) (r : ℝ) :
    Measurable fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r

/-- ★★ **Integrability of the domination bound from an integrable envelope.** -/
theorem integrable_logSqDomBound_of_envelope {ℓ c b M L φ₀ : Λ → ℝ} (hℓ : Measurable ℓ)
    (hc : Measurable c) (hb : Measurable b) (hM : Measurable M) (hLm : Measurable L)
    (hφ : Measurable φ₀) {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l)
    (hL : ∀ l, 0 ≤ L l)
    (hEnv : Integrable (fun l => (1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|) *
      (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4)) ν) :
    Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r) ν

/-- The mean value inequality on the ball: `‖H(s) − H(½)‖ ≤ B r`. -/
theorem norm_sub_le_of_deriv_le_ball {H : ℂ → ℂ} {r B : ℝ}
    (hdiff : DifferentiableOn ℂ H (Metric.ball (1 / 2 : ℂ) r))
    (hbound : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv H s‖ ≤ B) (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) : ‖H s - H (1 / 2)‖ ≤ B * r

/-- ★★★ **The averaged naive Bayes polar distributions with a basepoint hypothesis**: the
remainders `logSqHolo_λ` need only be measurable in `λ` on the ball and integrable at `s = ½`; with
the fibre polar coefficients and the explicit bound `logSqDomBound` integrable, the averaged
continuation has the principal part `polarPart 2 (logSqAvgA …)` at `½`. -/
theorem averaged_naiveBayes_polar_basepoint {φ : Λ → ℝ → ℝ} {ℓ c b M L : Λ → ℝ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1 / 2) (hM0 : ∀ l, 0 < M l) (hM1 : ∀ l, M l ≤ 1)
    (hφ : ∀ l, Continuous (φ l))
    (hL : ∀ l, ∀ t ∈ Icc (-1 : ℝ) 1, |φ l t - φ l 0| ≤ L l * |t|)
    (hcoef : ∀ q ≤ 2, Integrable (fun l => logSqA (ℓ l) (c l) (2 * φ l 0) q) ν)
    (hmeas : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r,
      AEStronglyMeasurable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ν)
    (hint0 : Integrable (fun l => logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)) ν)
    (hB : Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r) ν) :
    (fun s => (∫ l, (((2 * φ l 0 : ℝ) : ℂ) * logSqRat (ℓ l) (c l) s +
      logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s) ∂ν) -
      polarPart 2 (logSqAvgA (fun l => φ l 0) ℓ c ν) (1 / 2 : ℂ) s)
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ)

```


## State of the note (pinned to grammar 77300e3)
Formal: §2 DLN flat prior at every depth; Gaussian DLN: depth-two two-term expansion with explicit remainder and the Bessel closed form with its `e^zK₀` corollary; the crossing corollary; the all-depth conditional reduction, `ζ_K = 2^s ζ_L`; the all-depth leading asymptotic AND second coefficient; the depth-three constant as an integral-defined limit. §3 cone: exact Leray closed form; the averaged posterior of `u₁²` with its first correction `1/√π`, both sides four-dimensional. §4 blow-up: tie formulas, Laurent data, the two-term Laplace expansion, the monomial constant, the family theorem for every `k ≥ 2` with a log-free remainder. §5 rank-one: normal integral and tilt at aligned and general orbit points, the invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): the exact `J = R₀²/2 + π²/48` and `Q = (c² + 5π²/6)/(4s)` (hence the depth-three constant `((4 log 2 − 2γ)² + π²)/(4π)`); the constant terms for `L ≥ 4`; `H₃`, `ζ(3)`; the naive Bayes envelope `M_±(λ)` facewise integrability and the joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the cone's `O(N^{−1})` averaged remainder and the exact expansion prefactors; the blow-up higher poles (`α₁ = √(π/2)/16`) and the observable expansions of §4; the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; an abstract Mellin transfer theorem.

## Library facts
Everything of rounds 1–10: the amplitude engine (`ampJ_two_term`, `ampJ_two_term_quartic`), the monomial constants, `gaussLaplace2_bounds`, `LeadingData`/`TwoTermData` propagation, the scalar recursion at every depth, `measurable_gaussLaplace2`, the Gaussian-tilt facts (`integral_gaussTilt`, `integrable_abs_gaussTilt`), `∫₀^∞ u e^{−u²/2} = 1`, `∫ |t| e^{−t²/2} = 2`, `∫_c^∞ p e^{−p} = (c+1)e^{−c}`, dominated convergence along `atTop` on ℝ (`tendsto_integral_filter_of_dominated_convergence`), Fubini via `integrable_prod_iff'`/`integral_integral_swap`, `Γ''(½)` (DCVIII: `2ΓΓ'' − 2Γ'² = π³` at ½ from the reflection formula), `Γ'(1) = −γ` as the renormalised integral (DCXI), `hasDerivAt_mellinIoc` (holomorphy of `s ↦ ∫₀¹ g(t)t^{−2s}` for `|g| ≤ Ct^b`), the Mellin engine `logMellinFull_eq`/`logSqMellinFull`. Mathlib pin v4.33.1 (no Bessel, no polygamma, no Gamma duplication formula that I know of — `Real.Gamma_mul_Gamma_add_half`? please say if you recall it on this pin, we will grep).

## Questions
1. Fidelity check (brief) of DCXXVIII–DCXXXI against the note's claims and your round-10 specifications; in particular (a) DCXXIX's envelope route (direct denominator lower bound instead of tilt monotonicity) and the statement `cone_averaged_correction` (is `∫ (coneNumSq/coneDen) γ` the note's `E_ξ[E[u₁²|ξ]]`, with `coneNumSq_eq`/`coneDen_eq` making both sides four-dimensional); (b) DCXXXI's `depthThreeQ` with the `1/v` and the constant `depthThreeConst` — please recheck `(cR₀ + 2J)/π + (2/s)Q` against your round-9/10 formula and the Mellin value; (c) DCXXVIII's constant 7 and the interface `ampJ_two_term_quartic`.
2. Rank the next three day-sized formal targets by value-per-effort (concrete Lean statements + routes). Candidates: (a) the exact `J = ∫₀^∞ h(x) log x/x dx = R₀²/2 + π²/48` — the renormalised Mellin transform `∫₀^∞ h(x) x^{z−1} dx = (2^{z/2}Γ(1 + z/2) − 1)/z` and its derivative at `0`: what is the cleanest Lean route given DCVIII's `Γ''(½)` and DCXI's `Γ'(1) = −γ` — is `Γ''(1) = γ² + π²/6` needed, and how to get it (duplication `Γ(z)Γ(z+½) = 2^{1−2z}√π Γ(2z)` differentiated twice at ½? or the reflection formula at 1? or Mathlib's `Real.Gamma` Bohr–Mollerup/`Real.log_Gamma` convexity data)? Or a route avoiding polygamma: `∫₀^∞ e^{−x²/2} log² x dx` by differentiating `∫ e^{−x²/2} x^{s}` twice — which needs `Γ''(½)` only (we have it)? (b) the exact `Q = (c² + 5π²/6)/(4s)` — route (does it reduce to `J`-type Gamma data or is it a genuinely 2D integral identity)? (c) the blow-up observable numerators `X_N = ∫ x² e^{−N x²(x²+y²)/2} e^{−|w|²/2}`, `Y_N` with `y²`: `N X_N → π`, `√N Y_N → 2√(2π)` — give the reduced 1D integrals and the DCT statements; (d) the naive Bayes face lemma: with the definitions now supplied above (`logSqDomBound`, `envelopeConst`, the ball/basepoint adapters), state the face patch and the envelope with `a = 0, b = 2` precisely in terms of these Lean objects, and which pieces are day-sized; (e) `ThreeTermData` propagation for the `(log N)^{L−3}` coefficient at every depth `L ≥ 4` (with `J` as a constant): the recursion `C_{L+1} = (C_L/(L−2) + 2B_LR₀ + 4(L−1)A_LJ)/s` — confirm and give the interface; (f) the cone's second correction (the `O(N^{−1})` term of the averaged ratio, or the exact ratio expansion at fixed `a` to `O(N^{−1})`); (g) the rank-one Morse–Bott passage (normal integral → `Z_N[1;Ξ]`) in a reduced form. Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the four new files (`coneTilt`'s `δ` vs `N`, the `1/√N` argument, `depthThreeQ`'s indicator, `gaussJlog` vs `J_a`, the raw vs normalised Gaussian in `coneNumSq`/`coneDen`).
Answer concisely with Lean-facing detail.
