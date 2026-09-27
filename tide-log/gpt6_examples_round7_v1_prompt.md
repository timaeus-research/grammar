You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 245a456, 951 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-6 targets ALL landed: (1) the blow-up Laplace expansion — done for the NOTE'S model `K = x²(x²+y²)/2` with the prior `e^{−|w|²/2}` (not the `x²y²` shortcut; the extra factor `e^{−Nx⁴/2}` is absorbed into a general-amplitude version of the `J(ε)` engine): DCXIV `AmplitudeJ.lean` + DCXV `BlowUpLaplaceExpansion.lean`, `|Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N` for `N ≥ 1`; (2) the envelope certificate + basepoint adapter: DCXVII `LogSqEnvelopeCertificate.lean`; (3) the all-depth Gaussian conditional reduction and the leading coefficient of `ζ_K`: DCXVI `GaussianDepthAll.lean`. This is round 7.

## HEADLINES rows DCXIV–DCXVII
| **DCXIV** | ★★ **THE TWO-TERM EXPANSION OF `∫₀^∞ 2a(u)/√(u²+ε) du` FOR A GENERAL AMPLITUDE (u948; the engine of the blow-up expansion; Astra round-6 target 1, part 1)**: `ampJ a ε`, `ampRenorm a = ∫₀^∞ (a(u) − 1_{(0,1]}(u))·2/u du`, the amplitude class `AmpData a A` (measurable, `0 ≤ a ≤ 1`, `1 − a(u) ≤ Au²` on `(0,1]`, `a(u) ≤ e^{−u/2}` for `u ≥ 1`); `amp_rem_inner_le` (`≤ Aε(log(1/ε)+1)`), `integral_exp_neg_half_Ioi_one` (`∫₁^∞ e^{−u/2} = 2e^{−1/2}`), `amp_rem_outer_le` (`≤ 3ε`), integrability of the renormalised integrand and of `2a/√(u²+ε)` on `(0,1]` and `(1,∞)`, `ampRenorm_split`; ★★ `ampJ_two_term : |J_a(ε) − (log(4/ε) + R_a)| ≤ Aε(log(1/ε)+1) + 4ε` for `0 < ε ≤ 1` (DCXII's argument with the Gaussian amplitude replaced by the hypotheses). | AmplitudeJ.lean |
| **DCXV** | ★★★ **THE TWO-TERM EXPANSION OF THE BLOW-UP MODEL'S PARTITION FUNCTION (u949; examples_slop §4 eq. blowup_population, `c_{½,1} = √(π/2)`, `c_{½,0} = √(π/2)(5 log 2 − γ)`; Astra round-6 target 1 — done for the NOTE'S model `K = x²(x²+y²)/2` with the prior `e^{−|w|²/2}`, not the consult's `x²y²` shortcut)**: `blowupLaplace N = ∫_{ℝ²} e^{−N x²(x²+y²)/2} e^{−(x²+y²)/2}`; `integrable_blowupLaplace`; ★★ `blowupLaplace_eq_integral : Z_N = √(2π)∫_ℝ e^{−Nx⁴/2}e^{−x²/2}/√(1+Nx²) dx` (Gaussian in `y` at fixed `x`); ★★ `blowupLaplace_eq_ampJ : Z_{m⁴} = √(2π)/m² · J_{a_m}(1/m²)` with `a_m(u) = e^{−u⁴/2}e^{−u²/2m²}` (evenness + `x = u/m`); `blowAmp_ampData` (`A = 1`, `m ≥ 1`), `blowAmpInf_ampData` (`A = ½`); `integrableOn_renormalised_exp_inv`, `integral_renormalised_half` (`∫₀^∞ (e^{−v} − 1_{(0,½]})/v = log 2 − γ`); ★★ `ampRenorm_blowAmpInf : ∫₀^∞ (e^{−u⁴/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/2` (substitutions `y = u⁴` via `integral_comp_rpow_Ioi_of_pos` and `y = 2v` via `integral_comp_mul_left_Ioi`); `ampRenorm_blowAmp_sub_le : |R_{a_m} − R_∞| ≤ 3/m²` (pointwise `|a_m − a_∞| ≤ a_∞ u²/2m²`, `u e^{−u⁴/2} ≤ e^{−u/2}` for `u ≥ 1`); `sqrt_two_pi_div_two`; `blowupLaplace_two_term_m`; ★★★ `blowupLaplace_two_term_bound : |Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N` for `N ≥ 1`; ★★★ `blowupLaplace_two_term` (`=O[atTop] log N/N`). The first two coefficients of the note's population expansion of the blow-up model are theorems, proved directly from the integral rather than through the Gamma transform of DCX's Laurent data (which they match: `Γ(½)A₂ = √(π/2)`, `Γ(½)A₁ − Γ'(½)A₂ = √(π/2)(5 log 2 − γ)`). Numerics: `blowup_expansion_check.py`. Lean gotchas: `field_simp` may cancel a common nonzero factor, changing which `linear_combination` coefficient is needed (read the residual); `show (4:ℝ)/(1/m²) = 2²·m² by field_simp; norm_num`; `volume.real (Ioc 0 1) = 1` by `simp [Measure.real, Real.volume_Ioc]`; `inv_mul_cancel₀` vs `mul_inv_cancel₀` orientation after `integral_comp_mul_left_Ioi`. | BlowUpLaplaceExpansion.lean |
| **DCXVI** | ★★★ **THE GAUSSIAN DLN AT EVERY DEPTH: THE EXACT CONDITIONAL REDUCTION AND THE LEADING COEFFICIENT OF `ζ_K` (u950; examples_slop §2 eq. dln_gauss; Astra round-6 target 3)**: `gaussDensity`, `gaussLaplaceL L N = E exp(−N(∏W_i)²/2)` (normalised Gaussian prior on `ℝ^L`), `integrable_gaussLaplaceL`, `integrable_prod_gaussDensity` (`Integrable.fintype_prod` + `volume_pi`); `integral_pi_succ_symm` (Bochner peel of the first coordinate integrated LAST: `∫ F = ∫ b, ∫ a, F (Fin.cons a b)` via `volume_preserving_piFinSuccAbove` and `integral_prod_symm`); ★★★ `gaussLaplaceL_succ : Z_{L+1}(N) = E[(1 + N(∏_{i<L} W_i)²)^{−1/2}]` for `N ≥ 0` (Gaussian integral in the last coordinate; no Bessel function; `L = 1` is DCVII); `gaussKZeta L s = E K^{−s}`, `half_cpow_neg`, ★★ `gaussKZeta_eq : ζ_K(s) = 2^s ζ_L(s)` (pointwise, `P = 0` and `s = 0` cases separately); ★★ `tendsto_pole_gaussK : (s − ½)^L · 2^s ζ1Closed(s)^L → √2(−1/√(2π))^L` (the consult's `2^{−(L−1)/2}π^{−L/2}` up to the sign of the negative-moment variable), from DCVI's `tendsto_pole_gaussZeta` and the continuity of `2^s`. The asymptotic transfer to `Z_L(N) ~ (log N)^{L−1}/((L−1)!(2π)^{(L−1)/2}√N)` for `L ≥ 3` remains a derivation. Lean gotchas: `continuous_finset_prod` is deprecated for `continuous_finsetProd`; `Complex.mul_cpow_ofReal_nonneg` has the casts INSIDE the product (`(↑a * ↑b)^r`) — pass `(a := …) (b := …)` and `Complex.ofReal_mul` first; `Complex.arg 2 ≠ π` via `arg_ofReal_of_nonneg`. | GaussianDepthAll.lean |
| **DCXVII** | ★★★ **THE ENVELOPE CERTIFICATE AND THE BASEPOINT ADAPTER (u951; examples_slop §6; Astra round-6 target 2 — ALL ROUND-6 TARGETS DONE)**: `le_one_add_pow_four`, `pow_three_le_one_add_pow_four`; `envelopeConst r = 4(5 + 4/δ²)/(½−r)² + 18/r + 4/(1−2r)² + 2/r` (`δ = (½−r)/2`); ★★ `logSqDomBound_le_envelope : logSqDomBound ℓ c b M L φ₀ r ≤ C_r (1+|φ₀|+L)(1+ℓ²+|c|+|b|)(1+M^{−2r})(1+|log M|⁴)` for `0 < r < ½`, `M > 0`, `L ≥ 0` (piecewise: `4ℓ²+|c|+4/δ² ≤ (5+4/δ²)Q`, `(2(|ℓ|+x)²+|c|)x ≤ 9Q(1+x⁴)` via `x, x³ ≤ 1 + x⁴`); `logSqDomBound_nonneg`, `measurable_logSqDomBound` (`fun_prop`); ★★ `integrable_logSqDomBound_of_envelope` (integrable envelope ⇒ integrable bound; the consult's facewise condition `η + 2rβ < a` is then a statement about the envelope alone); `norm_sub_le_of_deriv_le_ball` (`‖H(s) − H(½)‖ ≤ Br` on the ball, `Convex.norm_image_sub_le_of_norm_deriv_le`); ★★★ `averaged_naiveBayes_polar_basepoint`: the averaged polar theorem with the remainders integrable at `s = ½` only (measurability on the ball, integrable coefficients and bound): every analytic hypothesis of DCIX is now derived from the fibre data and one basepoint integrability. Lean gotchas: `set … with` on `|·|`, rpow and products ⇒ `clear_value` before `nlinarith` (whnf timeouts otherwise); `4ℓ² + |c| ≤ 5Q` not `4Q` (count the terms); `le_mul_of_one_le_left`. | LogSqEnvelopeCertificate.lean |

## Public statements of the four new files (verbatim signatures)
### Grammar/AmplitudeJ.lean
```lean
/-- `J_a(ε) = ∫₀^∞ 2 a(u)/√(u² + ε) du`. -/
noncomputable def ampJ (a : ℝ → ℝ) (ε : ℝ) : ℝ

/-- The renormalised constant `R_a = ∫₀^∞ (a(u) − 1_{(0,1]}(u))·2/u du`. -/
noncomputable def ampRenorm (a : ℝ → ℝ) : ℝ

/-- The amplitude hypotheses. -/
structure AmpData (a : ℝ → ℝ) (A : ℝ) : Prop

/-- `|∫₀¹ (a(u) − 1)(2/√(u² + ε) − 2/u) du| ≤ A ε (log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem amp_rem_inner_le (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤
      A * (ε * (Real.log (1 / ε) + 1)) := by
  have hA := h.A_nonneg
  have hmaj : IntegrableOn (fun u : ℝ => A * (2 * ε * u / (u ^ 2 + ε))) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun w : ℝ => 2 * ε * w) (uIcc 0 1)).div (by fun_prop)
        fun w _ => by positivity)).const_mul A
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u => (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_majorant hε]
    have h1 : Real.log (1 + ε) ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε)]
    rw [one_div, Real.log_inv]
    refine mul_le_mul_of_nonneg_left ?_ h.A_nonneg
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu.1
    obtain ⟨g1, g2⟩ := gap_bounds hε hu0
    have hn := h.near u hu
    have hle := h.le_one u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc -(a u - 1) * -(2 / Real.sqrt (u ^ 2 + ε) - 2 / u)
        ≤ (A * u ^ 2) * (2 * ε / (u * (u ^ 2 + ε))) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = A * (2 * ε * u / (u ^ 2 + ε))

/-- `∫₁^∞ e^{−u/2} du = 2e^{−1/2}`. -/
theorem integral_exp_neg_half_Ioi_one :
    ∫ u in Ioi (1 : ℝ), Real.exp (-u / 2) = 2 * Real.exp (-1 / 2) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 1 (b := 1 / 2) (by norm_num)
  simp only [smul_eq_mul, mul_one] at h
  have e : (fun u : ℝ => Real.exp (-u / 2)) = fun u => Real.exp (-(1 / 2 * u))

/-- `|∫₁^∞ a(u)(2/√(u² + ε) − 2/u) du| ≤ 3ε` for `ε > 0`. -/
theorem amp_rem_outer_le (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤ 3 * ε := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * ε * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * ε))
      (fun w _ => ?_) measurableSet_Ioi
    change 2 * ε * Real.exp (-(1 / 2 : ℝ) * w) = 2 * ε * Real.exp (-w / 2)
    congr 2
    ring
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun u => a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, integral_exp_neg_half_Ioi_one]
    have he : 3 / 2 ≤ Real.exp (1 / 2) := by
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h2 : Real.exp (-1 / 2) * 4 ≤ 3 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu : (1 : ℝ) < u := hu
    have hu0 : 0 < u := by linarith
    obtain ⟨g1, g2⟩ := gap_bounds hε hu0
    have ha0 := h.nonneg u
    have hat := h.tail u hu.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha0, abs_of_nonpos (by linarith)]
    have h4 : 2 * ε / (u * (u ^ 2 + ε)) ≤ 2 * ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hu.le (by nlinarith : (1 : ℝ) ≤ u ^ 2 + ε) zero_le_one hu0.le]
    calc a u * -(2 / Real.sqrt (u ^ 2 + ε) - 2 / u) ≤ Real.exp (-u / 2) * (2 * ε) :=
          mul_le_mul hat (by linarith) (by linarith) (Real.exp_pos _).le
      _ = 2 * ε * Real.exp (-u / 2)

theorem measurable_ampRenorm (h : AmpData a A) :
    Measurable fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u)

theorem integrableOn_ampRenorm_inner (h : AmpData a A) :
    IntegrableOn (fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2 * A)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_ampRenorm h).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hn := h.near u hu
  have hle := h.le_one u
  rw [Real.norm_eq_abs, indicator_of_mem hu, Pi.one_apply, abs_mul, abs_of_nonpos (by linarith),
    abs_of_pos (by positivity)]
  calc -(a u - 1) * (2 / u) ≤ A * u ^ 2 * (2 / u) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * A * u := by field_simp
    _ ≤ 2 * A

theorem integrableOn_ampRenorm_outer (h : AmpData a A) :
    IntegrableOn (fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u)) (Ioi 1) := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2)
      (fun w _ => ?_) measurableSet_Ioi
    change 2 * Real.exp (-(1 / 2 : ℝ) * w) = 2 * Real.exp (-w / 2)
    congr 2
    ring
  refine hmaj.mono' (measurable_ampRenorm h).aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  have hm : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hu)
  rw [Real.norm_eq_abs, indicator_of_notMem hm, sub_zero, abs_mul, abs_of_nonneg (h.nonneg u),
    abs_of_pos (by positivity)]
  have h4 : 2 / u ≤ 2 := by rw [div_le_iff₀ hu0]; linarith
  calc a u * (2 / u) ≤ Real.exp (-u / 2) * 2 :=
        mul_le_mul (h.tail u hu.le) h4 (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-u / 2)

/-- `R_a = ∫₀¹ (a(u) − 1)·2/u du + ∫₁^∞ a(u)·2/u du`. -/
theorem ampRenorm_split (h : AmpData a A) :
    ampRenorm a = (∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / u)) +
      ∫ u in Ioi (1 : ℝ), a u * (2 / u)

theorem measurable_ampJ (h : AmpData a A) (ε : ℝ) :
    Measurable fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε)

theorem integrableOn_ampJ_inner (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε)) (Ioc 0 1) := by
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine Measure.integrableOn_of_bounded (M := 2 / Real.sqrt ε)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_ampJ h ε).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u _ => ?_
  have hs : Real.sqrt ε ≤ Real.sqrt (u ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  have ha0 := h.nonneg u
  have ha1 := h.le_one u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 2 * a u / Real.sqrt (u ^ 2 + ε) ≤ 2 / Real.sqrt (u ^ 2 + ε) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
    _ ≤ 2 / Real.sqrt ε

theorem integrableOn_ampJ_outer (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε)) (Ioi 1) := by
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hmaj : IntegrableOn (fun u : ℝ => 2 / Real.sqrt ε * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 / Real.sqrt ε))
      (fun w _ => ?_) measurableSet_Ioi
    change 2 / Real.sqrt ε * Real.exp (-(1 / 2 : ℝ) * w) = 2 / Real.sqrt ε * Real.exp (-w / 2)
    congr 2
    ring
  refine hmaj.mono' (measurable_ampJ h ε).aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hs : Real.sqrt ε ≤ Real.sqrt (u ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  have ha0 := h.nonneg u
  have hat := h.tail u hu.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 2 * a u / Real.sqrt (u ^ 2 + ε) ≤ 2 * Real.exp (-u / 2) / Real.sqrt ε := by
        rw [div_le_div_iff₀ (by positivity) hs0]
        have : 0 ≤ 2 * Real.exp (-u / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hs this]
    _ = 2 / Real.sqrt ε * Real.exp (-u / 2)

/-- ★★ **The two-term expansion for a general amplitude**:
`|J_a(ε) − (log(4/ε) + R_a)| ≤ A ε (log(1/ε) + 1) + 4ε` for `0 < ε ≤ 1`. -/
theorem ampJ_two_term (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ a ε - (Real.log (4 / ε) + ampRenorm a)| ≤ A * (ε * (Real.log (1 / ε) + 1)) + 4 * ε := by
  have hA1 := integrableOn_ampJ_inner h hε
  have hA2 := integrableOn_ampJ_outer h hε
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun u : ℝ => (a u - 1) * (2 / u)) (Ioc 0 1) :=
    (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun u : ℝ => a u * (2 / u)) (Ioi 1) :=
    (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : ampJ a ε = (∫ u in Ioc (0 : ℝ) 1, 2 * a u / Real.sqrt (u ^ 2 + ε)) +
      ∫ u in Ioi (1 : ℝ), 2 * a u / Real.sqrt (u ^ 2 + ε) := by
    unfold ampJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  have hR1 : ∫ u in Ioc (0 : ℝ) 1, 2 * a u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε)) +
        (∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / u)) +
        ∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) := by
    have e : ∀ u ∈ Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) =
        2 * a u / Real.sqrt (u ^ 2 + ε) - 2 / Real.sqrt (u ^ 2 + ε) - (a u - 1) * (2 / u) :=
      fun u _ => by ring
    have hAp : IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε) -
        2 / Real.sqrt (u ^ 2 + ε)) (Ioc 0 1) := hA1.sub hp1
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_sub hAp hq1, integral_sub hA1 hp1]
    ring
  have hR2 : ∫ u in Ioi (1 : ℝ), 2 * a u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioi (1 : ℝ), a u * (2 / u)) +
        ∫ u in Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) := by
    have e : ∀ u ∈ Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) =
        2 * a u / Real.sqrt (u ^ 2 + ε) - a u * (2 / u) := fun u _ => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hA2 hq2]
    ring
  have hb1 := elem_bounds hε hε1
  have hb2 := amp_rem_inner_le h hε hε1
  have hb3 := amp_rem_outer_le h hε
  have hsplit := ampRenorm_split h
  rw [hJ, hR1, hR2, hE, hsplit]
  rw [abs_le] at hb2 hb3 ⊢
  have hA := h.A_nonneg
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hAε : 0 ≤ A * (ε * (Real.log (1 / ε) + 1))
```
### Grammar/BlowUpLaplaceExpansion.lean
```lean
/-- The blow-up model's partition function with the Gaussian prior `e^{−|w|²/2}`. -/
noncomputable def blowupLaplace (N : ℝ) : ℝ

/-- The amplitude `a_m(u) = e^{−u⁴/2} e^{−u²/2m²}`. -/
noncomputable def blowAmp (m u : ℝ) : ℝ

/-- The limiting amplitude `e^{−u⁴/2}`. -/
noncomputable def blowAmpInf (u : ℝ) : ℝ

theorem integrable_blowupLaplace (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) := by
  have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  have hprod : Integrable (fun w : ℝ × ℝ => Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
      (volume.prod volume) := hg.mul_prod hg
  rw [Measure.volume_eq_prod]
  refine hprod.mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg hN (by positivity : 0 ≤ w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2))])
    have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
        Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : 0 ≤ Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by positivity
    calc Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
          (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
        ≤ 1 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)

/-- ★★ **The exact conditional reduction**:
`Z_N = √(2π) ∫_ℝ e^{−N x⁴/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`. -/
theorem blowupLaplace_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupLaplace N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
  unfold blowupLaplace
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_blowupLaplace N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hpt : ∀ y : ℝ, Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2) =
      (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_exp_cond hc]
  have hsq : Real.sqrt (2 * Real.pi / (1 + N * x ^ 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (1 + N * x ^ 2)

theorem blowAmp_eq (m u : ℝ) : blowAmp m u = Real.exp (-u ^ 4 / 2 + -u ^ 2 / (2 * m ^ 2))

/-- ★★ `Z_{m⁴} = √(2π)/m² · J_{a_m}(1/m²)` for `m > 0`. -/
theorem blowupLaplace_eq_ampJ {m : ℝ} (hm : 0 < m) :
    blowupLaplace (m ^ 4) = Real.sqrt (2 * Real.pi) / m ^ 2 * ampJ (blowAmp m) (1 / m ^ 2) := by
  rw [blowupLaplace_eq_integral (by positivity)]
  set f : ℝ → ℝ := fun x =>
    Real.exp (-m ^ 4 * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + m ^ 4 * x ^ 2) with hf
  have h1 : ∫ x : ℝ, f x = 2 * ∫ x in Ioi (0 : ℝ), f x := by
    rw [← integral_comp_abs (f := f)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [show |x| ^ 4 = x ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul],
      sq_abs]
  have hm1 : 0 < 1 / m := by positivity
  have h2 : ∫ x in Ioi (0 : ℝ), f x = m⁻¹ * ∫ u in Ioi (0 : ℝ), f (1 / m * u) := by
    rw [integral_comp_mul_left_Ioi f 0 hm1, mul_zero, smul_eq_mul, one_div, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ hm.ne', one_mul]
  have h3 : ∀ u ∈ Ioi (0 : ℝ), f (1 / m * u) =
      m⁻¹ * (blowAmp m u / Real.sqrt (u ^ 2 + 1 / m ^ 2)) := by
    intro u _
    simp only [hf]
    have e1 : -m ^ 4 * (1 / m * u) ^ 4 / 2 = -u ^ 4 / 2 := by field_simp
    have e2 : -(1 / m * u) ^ 2 / 2 = -u ^ 2 / (2 * m ^ 2) := by field_simp
    have e3 : 1 + m ^ 4 * (1 / m * u) ^ 2 = m ^ 2 * (u ^ 2 + 1 / m ^ 2)

theorem blowAmp_ampData {m : ℝ} (hm : 1 ≤ m) : AmpData (blowAmp m) 1 where
  meas := by unfold blowAmp; fun_prop
  nonneg u := by unfold blowAmp; positivity
  le_one u := by
    unfold blowAmp
    have hm0 : 0 < m := by linarith
    calc Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ 1 * 1 :=
          mul_le_mul (Real.exp_le_one_iff.2 (by nlinarith [pow_nonneg (sq_nonneg u) 2]))
            (Real.exp_le_one_iff.2 (by
              have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
              linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  A_nonneg := zero_le_one
  near u hu := by
    rw [blowAmp_eq]
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have hdiv : u ^ 2 / (2 * m ^ 2) ≤ u ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg u]
    have := Real.add_one_le_exp (-u ^ 4 / 2 + -u ^ 2 / (2 * m ^ 2))
    have e : -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) := by ring
    rw [e] at this ⊢
    linarith
  tail u hu := by
    unfold blowAmp
    have hm0 : 0 < m := by linarith
    calc Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ Real.exp (-u ^ 4 / 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by
            have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
            linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le
      _ ≤ Real.exp (-u / 2)

theorem blowAmpInf_ampData : AmpData blowAmpInf (1 / 2) where
  meas := by unfold blowAmpInf; fun_prop
  nonneg u := by unfold blowAmpInf; positivity
  le_one u := by
    unfold blowAmpInf
    exact Real.exp_le_one_iff.2 (by nlinarith [pow_nonneg (sq_nonneg u) 2])
  A_nonneg := by norm_num
  near u hu := by
    unfold blowAmpInf
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have := Real.add_one_le_exp (-u ^ 4 / 2)
    linarith
  tail u hu

/-- The renormalised exponential integrand `(e^{−v} − 1_{(0,1]}(v))/v` is integrable on `(0, ∞)`. -/
theorem integrableOn_renormalised_exp_inv :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v) (Ioi 0) := by
  have hmeas : Measurable fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v :=
    ((by fun_prop : Measurable fun v : ℝ => Real.exp (-v)).sub
      (measurable_one.indicator measurableSet_Ioc)).div measurable_id
  have h1 : IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v)
      (Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 1)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v hv => ?_
    have hv0 : 0 < v := hv.1
    have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-v)
    rw [Real.norm_eq_abs, indicator_of_mem hv, Pi.one_apply, abs_div, abs_of_pos hv0,
      abs_of_nonpos (by linarith), div_le_one hv0]
    linarith
  have h2 : IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v) (Ioi 1) := by
    have hmaj : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 1) := by
      refine IntegrableOn.congr_fun (s := Ioi 1) (exp_neg_integrableOn_Ioi 1 one_pos)
        (fun w _ => ?_) measurableSet_Ioi
      simp
    refine hmaj.mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv : (1 : ℝ) < v

/-- `∫₀^∞ (e^{−v} − 1_{(0,1/2]}(v))/v dv = log 2 − γ`. -/
theorem integral_renormalised_half :
    ∫ v in Ioi (0 : ℝ), (Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v =
      Real.log 2 - Real.eulerMascheroniConstant := by
  have e : ∀ v ∈ Ioi (0 : ℝ), (Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v =
      (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v +
        (Ioc (1 / 2) 1).indicator (fun v => v⁻¹) v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    by_cases h1 : v ≤ 1 / 2
    · have hm1 : v ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hv0, h1⟩
      have hm2 : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, by linarith⟩
      have hm3 : v ∉ Ioc (1 / 2 : ℝ) 1 := fun h => absurd h.1 (not_lt.2 h1)
      rw [indicator_of_mem hm1, indicator_of_mem hm2, indicator_of_notMem hm3, add_zero]
    · have h1' := not_le.1 h1
      have hm1 : v ∉ Ioc (0 : ℝ) (1 / 2) := fun h => absurd h.2 (not_le.2 h1')
      rw [indicator_of_notMem hm1]
      by_cases h2 : v ≤ 1
      · have hm2 : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, h2⟩
        have hm3 : v ∈ Ioc (1 / 2 : ℝ) 1 := ⟨h1', h2⟩
        rw [indicator_of_mem hm2, indicator_of_mem hm3, Pi.one_apply, sub_zero]
        field_simp
        ring
      · have h2' := not_le.1 h2
        have hm2 : v ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        have hm3 : v ∉ Ioc (1 / 2 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        rw [indicator_of_notMem hm2, indicator_of_notMem hm3, add_zero]
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator fun v => v⁻¹) (Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc (1 / 2) 1)

/-- ★★ `R_∞ = ∫₀^∞ (e^{−u⁴/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/2`. -/
theorem ampRenorm_blowAmpInf :
    ampRenorm blowAmpInf = (Real.log 2 - Real.eulerMascheroniConstant) / 2 := by
  unfold ampRenorm blowAmpInf
  -- the substitution `y = u⁴`
  set g : ℝ → ℝ := fun y => (Real.exp (-y / 2) - (Ioc 0 1).indicator 1 y) / (2 * y) with hg
  have h4 := integral_comp_rpow_Ioi_of_pos (g := g) (p := 4) (by norm_num)
  have e4 : ∀ u ∈ Ioi (0 : ℝ), (4 * u ^ ((4 : ℝ) - 1)) • g (u ^ (4 : ℝ)) =
      (Real.exp (-u ^ 4 / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (u ^ 4) = (Ioc 0 1).indicator 1 u := by
      by_cases h : u ≤ 1
      · have hm : u ^ 4 ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hu0.le h⟩
        have hm' : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, h⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have h' := not_le.1 h
        have hm : u ^ 4 ∉ Ioc (0 : ℝ) 1 := fun hm =>
          absurd hm.2 (not_le.2 (one_lt_pow₀ h' (by norm_num)))
        have hm' : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg, smul_eq_mul]
    rw [show ((4 : ℝ) - 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hI]
    field_simp
    ring
  rw [← setIntegral_congr_fun measurableSet_Ioi e4, h4]
  -- the scaling `y = 2v`
  have h2 := integral_comp_mul_left_Ioi g 0 (b := 2) two_pos
  rw [mul_zero, smul_eq_mul] at h2
  have e2 : ∀ v ∈ Ioi (0 : ℝ), g (2 * v) =
      (1 / 4) * ((Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (2 * v) = (Ioc 0 (1 / 2)).indicator 1 v := by
      by_cases h : v ≤ 1 / 2
      · have hm : 2 * v ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
        have hm' : v ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hv0, h⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have h' := not_le.1 h
        have hm : 2 * v ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by linarith))
        have hm' : v ∉ Ioc (0 : ℝ) (1 / 2) := fun hm => absurd hm.2 (not_le.2 h')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg]
    rw [hI, show -(2 * v) / 2 = -v by ring]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, integral_renormalised_half]
    at h2
  have : ∫ y in Ioi (0 : ℝ), g y = 2 * ((1 / 4) * (Real.log 2 - Real.eulerMascheroniConstant))

/-- `|R_{a_m} − R_∞| ≤ 3/m²` for `m ≥ 1`. -/
theorem ampRenorm_blowAmp_sub_le {m : ℝ} (hm : 1 ≤ m) :
    |ampRenorm (blowAmp m) - ampRenorm blowAmpInf| ≤ 3 / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hd := blowAmp_ampData hm
  have hd' := blowAmpInf_ampData
  -- the pointwise comparison
  have hpt : ∀ u, 0 < u → |(blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u)| ≤
      blowAmpInf u * u / m ^ 2 ∧ |blowAmp m u * (2 / u) - blowAmpInf u * (2 / u)| ≤
      blowAmpInf u * u / m ^ 2 := by
    intro u hu
    have hx : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
    have he1 : Real.exp (-(u ^ 2 / (2 * m ^ 2))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-(u ^ 2 / (2 * m ^ 2)))
    have ha0 : 0 ≤ blowAmpInf u := hd'.nonneg u
    have hkey : |blowAmp m u - blowAmpInf u| ≤ blowAmpInf u * (u ^ 2 / (2 * m ^ 2)) := by
      unfold blowAmp blowAmpInf at *
      rw [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring, abs_of_nonpos (by nlinarith)]
      nlinarith
    have hfin : |blowAmp m u - blowAmpInf u| * (2 / u) ≤ blowAmpInf u * u / m ^ 2 := by
      calc |blowAmp m u - blowAmpInf u| * (2 / u)
          ≤ blowAmpInf u * (u ^ 2 / (2 * m ^ 2)) * (2 / u) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = blowAmpInf u * u / m ^ 2 := by field_simp
    have h2u : |2 / u| = 2 / u := abs_of_pos (by positivity)
    constructor
    · rw [show (blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u) =
          (blowAmp m u - blowAmpInf u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
    · rw [show blowAmp m u * (2 / u) - blowAmpInf u * (2 / u) =
          (blowAmp m u - blowAmpInf u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
  -- the split of both constants and the two pieces
  have hq1 : ∀ {a : ℝ → ℝ} {A : ℝ}, AmpData a A →
      IntegrableOn (fun u : ℝ => (a u - 1) * (2 / u)) (Ioc 0 1) :=
    fun h => (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : ∀ {a : ℝ → ℝ} {A : ℝ}, AmpData a A →
      IntegrableOn (fun u : ℝ => a u * (2 / u)) (Ioi 1) :=
    fun h => (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  rw [ampRenorm_split hd, ampRenorm_split hd']
  have hI1 : |(∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) -
      ∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)| ≤ 1 / m ^ 2 := by
    rw [← integral_sub (hq1 hd) (hq1 hd')]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (f := fun u => (blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u)) (C := 1 / m ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · have hv : volume.real (Ioc (0 : ℝ) 1) = 1 := by simp [Measure.real, Real.volume_Ioc]
      rw [Real.norm_eq_abs, hv, mul_one] at h
      exact h
    · intro u hu
      have hu0 : 0 < u := hu.1
      rw [Real.norm_eq_abs]
      refine ((hpt u hu0).1).trans ?_
      have ha1 := hd'.le_one u
      have ha0 := hd'.nonneg u
      rw [div_le_div_iff_of_pos_right hm2]
      nlinarith [hu.2]
  have hI2 : |(∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
      ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u)| ≤ 2 / m ^ 2 := by
    rw [← integral_sub (hq2 hd) (hq2 hd')]
    have hmaj : IntegrableOn (fun u : ℝ => 1 / m ^ 2 * Real.exp (-u / 2)) (Ioi 1) := by
      refine IntegrableOn.congr_fun (s := Ioi 1)
        ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (1 / m ^ 2))
        (fun w _ => ?_) measurableSet_Ioi
      congr 2
      ring
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun u => blowAmp m u * (2 / u) - blowAmpInf u * (2 / u)) hmaj ?_
    · rw [Real.norm_eq_abs] at h
      refine h.trans ?_
      rw [integral_const_mul, integral_exp_neg_half_Ioi_one]
      have he : 3 / 2 ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
      have h2 : Real.exp (-1 / 2) * 2 ≤ 2 := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        linarith
      have : 1 / m ^ 2 * (2 * Real.exp (-1 / 2)) = (Real.exp (-1 / 2) * 2) / m ^ 2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right h2 hm2.le
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu : (1 : ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      rw [Real.norm_eq_abs]
      refine ((hpt u hu0).2).trans ?_
      -- `e^{−u⁴/2} u ≤ e^{−u/2}` for `u ≥ 1`
      have hkey : blowAmpInf u * u ≤ Real.exp (-u / 2) := by
        unfold blowAmpInf
        have h1 := Real.add_one_le_exp (u ^ 4 / 2 - u / 2)
        have h2 : u ≤ Real.exp (u ^ 4 / 2 - u / 2) := by
          nlinarith [sq_nonneg (u - 1), sq_nonneg u, sq_nonneg (u ^ 2 - 1), sq_nonneg (u + 1)]
        calc Real.exp (-u ^ 4 / 2) * u ≤ Real.exp (-u ^ 4 / 2) * Real.exp (u ^ 4 / 2 - u / 2) :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = Real.exp (-u / 2) := by rw [← Real.exp_add]; ring_nf
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc |(∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) +
        (∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
        ((∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
          ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u))|
      = |((∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) -
          ∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
          ((∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
            ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u))| := by ring_nf
    _ ≤ 1 / m ^ 2 + 2 / m ^ 2 := (abs_add_le _ _).trans (add_le_add hI1 hI2)
    _ = 3 / m ^ 2

theorem sqrt_two_pi_div_two : Real.sqrt (2 * Real.pi) / 2 = Real.sqrt (Real.pi / 2) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2' : 0 < Real.sqrt 2

/-- The `m`-form of the expansion: for `m ≥ 1`,
`|Z_{m⁴} − √(π/2)(4 log m + 5 log 2 − γ)/m²| ≤ √(2π)(2 log m + 8)/m⁴`. -/
theorem blowupLaplace_two_term_m {m : ℝ} (hm : 1 ≤ m) :
    |blowupLaplace (m ^ 4) - Real.sqrt (Real.pi / 2) *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2| ≤
      Real.sqrt (2 * Real.pi) * (2 * Real.log m + 8) / m ^ 4 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hε : 0 < 1 / m ^ 2 := by positivity
  have hε1 : 1 / m ^ 2 ≤ 1 := by rw [div_le_one hm2]; nlinarith
  have hJ := ampJ_two_term (blowAmp_ampData hm) hε hε1
  have hR := ampRenorm_blowAmp_sub_le hm
  rw [ampRenorm_blowAmpInf] at hR
  have hlog4 : Real.log (4 / (1 / m ^ 2)) = 2 * Real.log 2 + 2 * Real.log m := by
    rw [show (4 : ℝ) / (1 / m ^ 2) = 2 ^ 2 * m ^ 2 by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog1 : Real.log (1 / (1 / m ^ 2)) = 2 * Real.log m := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  rw [hlog4, hlog1, one_mul] at hJ
  rw [blowupLaplace_eq_ampJ hm0, ← sqrt_two_pi_div_two]
  set J := ampJ (blowAmp m) (1 / m ^ 2) with hJdef
  set R := ampRenorm (blowAmp m) with hRdef
  clear_value J R
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have key : Real.sqrt (2 * Real.pi) / m ^ 2 * J - Real.sqrt (2 * Real.pi) / 2 *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2 =
      Real.sqrt (2 * Real.pi) / m ^ 2 * ((J - (2 * Real.log 2 + 2 * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / 2)) := by
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  calc Real.sqrt (2 * Real.pi) / m ^ 2 * |(J - (2 * Real.log 2 + 2 * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / 2)|
      ≤ Real.sqrt (2 * Real.pi) / m ^ 2 *
        ((1 / m ^ 2 * (2 * Real.log m + 1) + 4 * (1 / m ^ 2)) + 3 / m ^ 2) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hJ hR)) (by positivity)
    _ = Real.sqrt (2 * Real.pi) * (2 * Real.log m + 8) / m ^ 4

/-- ★★★ **The two-term expansion of the blow-up model's partition function**: for `N ≥ 1`,
`|Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N`
(the note's `c_{½,1} = √(π/2)`, `c_{½,0} = √(π/2)(5 log 2 − γ)`). -/
theorem blowupLaplace_two_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N| ≤
      Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8) / N := by
  have hN0 : 0 < N := by linarith
  set m := N ^ (1 / 4 : ℝ) with hm
  have hm1 : 1 ≤ m := Real.one_le_rpow hN (by norm_num)
  have hm0 : 0 < m := by linarith
  have hm4 : m ^ 4 = N := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlogm : Real.log N = 4 * Real.log m := by
    rw [← hm4, Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt N = m ^ 2 := by
    rw [← hm4, show m ^ 4 = (m ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h := blowupLaplace_two_term_m hm1
  have h2 : 2 * Real.log m = Real.log N / 2

/-- ★★★ `Z_N = √(π/2)(log N + 5 log 2 − γ)/√N + O(N^{−1} log N)` as `N → ∞`. -/
theorem blowupLaplace_two_term :
    (fun N : ℝ => blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N)
      =O[atTop] fun N => Real.log N / N := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt (2 * Real.pi) * (17 / 2)) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hb := blowupLaplace_two_term_bound (by linarith : 1 ≤ N)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hN.le)]
  refine hb.trans ?_
  rw [show Real.sqrt (2 * Real.pi) * (17 / 2) * (Real.log N / N) =
    Real.sqrt (2 * Real.pi) * (17 / 2 * Real.log N) / N by ring]
  refine div_le_div_of_nonneg_right ?_ hN.le
  have : 0 ≤ Real.sqrt (2 * Real.pi)
```
### Grammar/GaussianDepthAll.lean
```lean
/-- The standard Gaussian density. -/
noncomputable def gaussDensity (x : ℝ) : ℝ

theorem gaussDensity_nonneg (x : ℝ) : 0 ≤ gaussDensity x

theorem continuous_gaussDensity : Continuous gaussDensity

theorem integrable_gaussDensity : Integrable gaussDensity := by
  have := (integrable_exp_neg_mul_sq (b

/-- The depth-`L` Gaussian partition function with the normalised prior. -/
noncomputable def gaussLaplaceL (L : ℕ) (N : ℝ) : ℝ

theorem continuous_prod_coord (L : ℕ) : Continuous fun w : Fin L → ℝ => ∏ i, w i

theorem continuous_prod_gaussDensity (L : ℕ) :
    Continuous fun w : Fin L → ℝ => ∏ i, gaussDensity (w i)

theorem integrable_prod_gaussDensity (L : ℕ) :
    Integrable fun w : Fin L → ℝ => ∏ i, gaussDensity (w i) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f

theorem integrable_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun w : Fin L → ℝ =>
      Real.exp (-N * (∏ i, w i) ^ 2 / 2) * ∏ i, gaussDensity (w i) := by
  have hP := continuous_prod_coord L
  have hG := continuous_prod_gaussDensity L
  have h1 : Continuous fun w : Fin L → ℝ => Real.exp (-N * (∏ i, w i) ^ 2 / 2) :=
    Real.continuous_exp.comp (by fun_prop)
  refine (integrable_prod_gaussDensity L).mono' (h1.mul hG).measurable.aestronglyMeasurable ?_
  refine Eventually.of_forall fun w => ?_
  have hG0 : 0 ≤ ∏ i, gaussDensity (w i)

/-- **Bochner peel of the first coordinate, integrated last**:
`∫ F = ∫ b, ∫ a, F (a, b)` on `Fin (d+1) → ℝ`. -/
theorem integral_pi_succ_symm (d : ℕ) (F : (Fin (d + 1) → ℝ) → ℝ) (hF : Integrable F) :
    ∫ x, F x = ∫ b : Fin d → ℝ, ∫ a : ℝ, F (Fin.cons a b) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin d → ℝ)))

/-- ★★★ **The exact conditional reduction at every depth**:
`Z_{L+1}(N) = E[(1 + N (∏_{i<L} W_i)²)^{−1/2}]` for `N ≥ 0`. -/
theorem gaussLaplaceL_succ (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL (L + 1) N =
      ∫ b : Fin L → ℝ, 1 / Real.sqrt (1 + N * (∏ i, b i) ^ 2) * ∏ i, gaussDensity (b i) := by
  unfold gaussLaplaceL
  rw [integral_pi_succ_symm L _ (integrable_gaussLaplaceL (L + 1) hN)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  have hc : 0 < 1 + N * (∏ i, b i) ^ 2 := by positivity
  have hpt : ∀ a : ℝ, Real.exp (-N * (∏ i, (Fin.cons a b : Fin (L + 1) → ℝ) i) ^ 2 / 2) *
      ∏ i, gaussDensity ((Fin.cons a b : Fin (L + 1) → ℝ) i) =
      (1 / Real.sqrt (2 * Real.pi) * ∏ i, gaussDensity (b i)) *
        Real.exp (-(1 + N * (∏ i, b i) ^ 2) * a ^ 2 / 2) := by
    intro a
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have e : Real.exp (-N * (a * ∏ i, b i) ^ 2 / 2) * Real.exp (-a ^ 2 / 2) =
        Real.exp (-(1 + N * (∏ i, b i) ^ 2) * a ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show gaussDensity a = Real.exp (-a ^ 2 / 2) / Real.sqrt (2 * Real.pi) from rfl]
    linear_combination (∏ i, gaussDensity (b i)) / Real.sqrt (2 * Real.pi) * e
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, integral_exp_cond hc,
    Real.sqrt_div' _ hc.le]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs1 : 0 < Real.sqrt (1 + N * (∏ i, b i) ^ 2)

/-- `gaussLaplaceL 1 N = gaussLaplace2`'s one-dimensional integrand: the depth-two case of the
reduction is `Grammar.GaussianDepthTwo`. -/
theorem gaussLaplaceL_one_succ {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL 2 N = ∫ b : Fin 1 → ℝ, 1 / Real.sqrt (1 + N * (∏ i, b i) ^ 2) *
      ∏ i, gaussDensity (b i)

/-- `ζ_K(s) = E K^{−s}` for `K = (∏ W_i)²/2`. -/
noncomputable def gaussKZeta (L : ℕ) (s : ℂ) : ℂ

/-- `(1/2)^{−s} = 2^s`. -/
theorem half_cpow_neg (s : ℂ) : (((1 / 2 : ℝ) : ℂ)) ^ (-s) = (2 : ℂ) ^ s

/-- ★★ `ζ_K(s) = 2^s ζ_L(s)`. -/
theorem gaussKZeta_eq (L : ℕ) (s : ℂ) : gaussKZeta L s = (2 : ℂ) ^ s * gaussProductZeta L s := by
  unfold gaussKZeta gaussProductZeta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  have hden : ∀ i, ((gaussDensity (w i) : ℝ) : ℂ) =
      ((Real.exp (-w i ^ 2 / 2) / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := fun i => rfl
  simp_rw [hden]
  rw [← mul_assoc]
  congr 1
  rcases eq_or_ne (∏ i, w i) 0 with hP | hP
  · rw [hP]
    rcases eq_or_ne s 0 with hs | hs
    · simp [hs]
    · rw [show ((0 : ℝ) ^ 2 / 2 : ℝ) = 0 by norm_num, abs_zero]
      push_cast
      rw [Complex.zero_cpow (neg_ne_zero.2 hs), Complex.zero_cpow (by
        exact mul_ne_zero (by norm_num) hs), mul_zero]
  · have hP2 : 0 < |∏ i, w i| := abs_pos.2 hP
    have h := Complex.mul_cpow_ofReal_nonneg (a := |∏ i, w i| ^ 2) (b

/-- ★★ **The leading coefficient of `ζ_K` at `½`**:
`(s − ½)^L · 2^s ζ_L(s) → √2 (−1/√(2π))^L` as `s → ½`. -/
theorem tendsto_pole_gaussK (L : ℕ) :
    Tendsto (fun s : ℂ => (s - 1 / 2) ^ L * ((2 : ℂ) ^ s * gaussZeta1Closed s ^ L))
      (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 (((Real.sqrt 2 : ℝ) : ℂ) * (-(1 / (Real.sqrt (2 * Real.pi) : ℂ))) ^ L)) := by
  have h1 := tendsto_pole_gaussZeta L
  have h2 : Tendsto (fun s : ℂ => (2 : ℂ) ^ s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 ((Real.sqrt 2 : ℝ) : ℂ))
```
### Grammar/LogSqEnvelopeCertificate.lean
```lean
theorem le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ 4 := by
  rcases le_or_gt x 1 with h | h
  · nlinarith [pow_nonneg hx 4]
  · have h3 : 1 ≤ x ^ 3

theorem pow_three_le_one_add_pow_four {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 1 + x ^ 4 := by
  rcases le_or_gt x 1 with h | h
  · nlinarith [pow_le_one₀ hx h (n := 3), pow_nonneg hx 4]
  · have : x ^ 3 ≤ x ^ 4

/-- The envelope constant `C_r` of the coarse bound. -/
noncomputable def envelopeConst (r : ℝ) : ℝ

/-- ★★ **The coarse envelope**: for `0 < r < ½`, `M > 0`, `L ≥ 0`,
`logSqDomBound ℓ c b M L φ₀ r ≤
  C_r (1 + |φ₀| + L)(1 + ℓ² + |c| + |b|)(1 + M^{−2r})(1 + |log M|⁴)`. -/
theorem logSqDomBound_le_envelope {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2)
    (hM0 : 0 < M) (hL : 0 ≤ L) :
    logSqDomBound ℓ c b M L φ₀ r ≤ envelopeConst r *
      ((1 + |φ₀| + L) * (1 + ℓ ^ 2 + |c| + |b|)) * (1 + M ^ (-2 * r)) *
        (1 + |Real.log M| ^ 4) := by
  unfold logSqDomBound envelopeConst
  set P := 1 + |φ₀| + L with hP
  set Q := 1 + ℓ ^ 2 + |c| + |b| with hQ
  set x := |Real.log M| with hx
  set δ := (1 / 2 - r) / 2 with hδ
  have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg φ₀]
  have hQ1 : 1 ≤ Q := by rw [hQ]; linarith [abs_nonneg c, abs_nonneg b, sq_nonneg ℓ]
  have hx0 : 0 ≤ x := abs_nonneg _
  have hMr : 0 < M ^ (-2 * r) := Real.rpow_pos_of_pos hM0 _
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hd1 : 0 < (1 / 2 - r) ^ 2 := by positivity
  have hd3 : 0 < (1 - 2 * r) ^ 2 := by nlinarith
  have hℓQ : ℓ ^ 2 ≤ Q := by rw [hQ]; linarith [abs_nonneg c, abs_nonneg b]
  have hcQ : |c| ≤ Q := by rw [hQ]; linarith [abs_nonneg b, sq_nonneg ℓ]
  have hbQ : |b| ≤ Q := by rw [hQ]; linarith [abs_nonneg c, sq_nonneg ℓ]
  have hLP : L ≤ P := by rw [hP]; linarith [abs_nonneg φ₀]
  have hφP : |φ₀| ≤ P := by rw [hP]; linarith
  clear_value P Q x δ
  set E := P * Q * (1 + M ^ (-2 * r)) * (1 + x ^ 4) with hE
  clear_value E
  have hPQ : 0 ≤ P * Q := by positivity
  have hE1 : P * Q ≤ E := by
    rw [hE]
    have h1 : 1 ≤ 1 + M ^ (-2 * r) := by linarith
    have h2 : 1 ≤ 1 + x ^ 4 := by nlinarith [pow_nonneg hx0 4]
    nlinarith [mul_le_mul_of_nonneg_left h1 hPQ, mul_le_mul_of_nonneg_left h2
      (mul_nonneg hPQ (by linarith : (0 : ℝ) ≤ 1 + M ^ (-2 * r)))]
  have hE0 : 0 ≤ E := hPQ.trans hE1
  have ha : 4 * ℓ ^ 2 + |c| + 4 / δ ^ 2 ≤ (5 + 4 / δ ^ 2) * Q := by
    have : 0 ≤ 4 / δ ^ 2 := by positivity
    nlinarith
  have hc' : (2 * (|ℓ| + x) ^ 2 + |c|) * x ≤ 9 * Q * (1 + x ^ 4) := by
    have h1 : (|ℓ| + x) ^ 2 ≤ 2 * ℓ ^ 2 + 2 * x ^ 2 := by
      nlinarith [sq_nonneg (|ℓ| - x), sq_abs ℓ]
    have h2 : x ≤ 1 + x ^ 4 := le_one_add_pow_four hx0
    have h3 : x ^ 3 ≤ 1 + x ^ 4 := pow_three_le_one_add_pow_four hx0
    have h4 : (4 * ℓ ^ 2 + |c|) * x ≤ 5 * Q * x :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    have h5 : 5 * Q * x ≤ 5 * Q * (1 + x ^ 4) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : 4 * x ^ 3 ≤ 4 * Q * (1 + x ^ 4) := by
      have : 1 + x ^ 4 ≤ Q * (1 + x ^ 4) := le_mul_of_one_le_left (by positivity) hQ1
      linarith
    have h7 : (2 * (|ℓ| + x) ^ 2 + |c|) * x ≤ (4 * ℓ ^ 2 + 4 * x ^ 2 + |c|) * x :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    have h8 : (4 * ℓ ^ 2 + 4 * x ^ 2 + |c|) * x = (4 * ℓ ^ 2 + |c|) * x + 4 * x ^ 3 := by ring
    linarith
  -- piece 1
  have hp1 : 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2 ≤
      4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E := by
    have h1 : (4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L) ≤ ((5 + 4 / δ ^ 2) * Q) * (2 * P) :=
      mul_le_mul ha (by linarith) (by positivity) (by positivity)
    calc 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2
        ≤ 2 * (((5 + 4 / δ ^ 2) * Q) * (2 * P)) / (1 / 2 - r) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) hd1.le
      _ = 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * (P * Q) := by ring
      _ ≤ 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
  -- piece 2
  have hp2 : (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) / r ≤
      18 / r * E := by
    have h1 : (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) =
        ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r) := by ring
    have h2 : 2 * |φ₀| + 2 * L ≤ 2 * P := by linarith
    have h3 : M ^ (-2 * r) ≤ 1 + M ^ (-2 * r) := by linarith
    have h4 : ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r) ≤
        (9 * Q * (1 + x ^ 4)) * (2 * P) * (1 + M ^ (-2 * r)) := by
      have hA0 : 0 ≤ (2 * (|ℓ| + x) ^ 2 + |c|) * x := by positivity
      refine mul_le_mul (mul_le_mul hc' h2 (by positivity) (by positivity)) h3 hMr.le ?_
      positivity
    rw [h1, div_le_iff₀ hr]
    calc ((2 * (|ℓ| + x) ^ 2 + |c|) * x) * (2 * |φ₀| + 2 * L) * M ^ (-2 * r)
        ≤ (9 * Q * (1 + x ^ 4)) * (2 * P) * (1 + M ^ (-2 * r)) := h4
      _ = 18 * E := by rw [hE]; ring
      _ = 18 / r * E * r := by field_simp
  -- piece 3
  have hp3 : 2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 ≤ 4 / (1 - 2 * r) ^ 2 * E := by
    have h1 : |b| * L ≤ Q * P := mul_le_mul hbQ hLP hL (by linarith)
    calc 2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 = 4 / (1 - 2 * r) ^ 2 * (|b| * L) := by ring
      _ ≤ 4 / (1 - 2 * r) ^ 2 * (P * Q) := by
          rw [mul_comm P Q]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 / (1 - 2 * r) ^ 2 * E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  -- piece 4
  have hp4 : 2 * |b| * L * x * M ^ (-2 * r) / r ≤ 2 / r * E := by
    have h1 : |b| * L ≤ Q * P := mul_le_mul hbQ hLP hL (by linarith)
    have h2 : x ≤ 1 + x ^ 4 := le_one_add_pow_four hx0
    have h3 : M ^ (-2 * r) ≤ 1 + M ^ (-2 * r) := by linarith
    have h4 : |b| * L * x * M ^ (-2 * r) ≤ Q * P * (1 + x ^ 4) * (1 + M ^ (-2 * r)) := by
      refine mul_le_mul (mul_le_mul h1 h2 hx0 (by positivity)) h3 hMr.le (by positivity)
    rw [div_le_iff₀ hr]
    calc 2 * |b| * L * x * M ^ (-2 * r) = 2 * (|b| * L * x * M ^ (-2 * r)) := by ring
      _ ≤ 2 * (Q * P * (1 + x ^ 4) * (1 + M ^ (-2 * r))) := by
          exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * E := by rw [hE]; ring
      _ = 2 / r * E * r := by field_simp
  calc 2 * ((4 * ℓ ^ 2 + |c| + 4 / δ ^ 2) * (2 * L)) / (1 / 2 - r) ^ 2 +
        (2 * (|ℓ| + x) ^ 2 + |c|) * (2 * |φ₀| + 2 * L) * x * M ^ (-2 * r) / r +
        2 * (2 * |b| * L) / (1 - 2 * r) ^ 2 + 2 * |b| * L * x * M ^ (-2 * r) / r
      ≤ 4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 * E + 18 / r * E + 4 / (1 - 2 * r) ^ 2 * E +
        2 / r * E := by linarith
    _ = (4 * (5 + 4 / δ ^ 2) / (1 / 2 - r) ^ 2 + 18 / r + 4 / (1 - 2 * r) ^ 2 + 2 / r) *
        (P * Q) * (1 + M ^ (-2 * r)) * (1 + x ^ 4)

theorem logSqDomBound_nonneg {ℓ c b M L φ₀ r : ℝ} (hr : 0 < r) (hM0 : 0 < M) (hL : 0 ≤ L) :
    0 ≤ logSqDomBound ℓ c b M L φ₀ r := by
  unfold logSqDomBound
  have

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
    Integrable (fun l => logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r) ν := by
  refine (hEnv.const_mul (envelopeConst r)).mono'
    (measurable_logSqDomBound hℓ hc hb hM hLm hφ r).aestronglyMeasurable ?_
  refine Eventually.of_forall fun l => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (logSqDomBound_nonneg hr (hM0 l) (hL l))]
  calc logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ₀ l) r
      ≤ envelopeConst r * ((1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|)) *
        (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4) :=
        logSqDomBound_le_envelope hr hr1 (hM0 l) (hL l)
    _ = envelopeConst r * ((1 + |φ₀ l| + L l) * (1 + ℓ l ^ 2 + |c l| + |b l|) *
        (1 + M l ^ (-2 * r)) * (1 + |Real.log (M l)| ^ 4))

/-- The mean value inequality on the ball: `‖H(s) − H(½)‖ ≤ B r`. -/
theorem norm_sub_le_of_deriv_le_ball {H : ℂ → ℂ} {r B : ℝ}
    (hdiff : DifferentiableOn ℂ H (Metric.ball (1 / 2 : ℂ) r))
    (hbound : ∀ s ∈ Metric.ball (1 / 2 : ℂ) r, ‖deriv H s‖ ≤ B) (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (1 / 2 : ℂ) r) : ‖H s - H (1 / 2)‖ ≤ B * r := by
  have h := (convex_ball (1 / 2 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hx)) hbound
    (Metric.mem_ball_self hr) hs
  refine h.trans ?_
  have hlt : ‖s - 1 / 2‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hs
  have hB : 0 ≤ B

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
      =O[𝓝[≠] (1 / 2 : ℂ)] fun _ => (1 : ℂ) := by
  refine averaged_naiveBayes_polar hr hr1 hM0 hM1 hφ hL hcoef hmeas ?_ hB
  intro s hs
  refine (hint0.norm.add (hB.const_mul r)).mono' (hmeas s hs) ?_
  refine Eventually.of_forall fun l => ?_
  have hdiff : DifferentiableOn ℂ (logSqHolo (ℓ l) (c l) (b l) (M l) (φ l))
      (Metric.ball (1 / 2 : ℂ) r) := by
    refine ((logSqMellinFull_eq (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l)).1).mono ?_
    intro z hz
    have := re_le_of_mem_ball_half hz
    change z.re < 1
    linarith
  have hbound : ∀ z ∈ Metric.ball (1 / 2 : ℂ) r,
      ‖deriv (logSqHolo (ℓ l) (c l) (b l) (M l) (φ l)) z‖ ≤
        logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r :=
    fun z hz => norm_deriv_logSqHolo_le (ℓ l) (c l) (b l) (hM0 l) (hM1 l) (hφ l) (hL l) hr hr1 hz
  have hmv := norm_sub_le_of_deriv_le_ball hdiff hbound hr hs
  calc ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s‖
      ≤ ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) s -
          logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ +
        ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ := norm_le_norm_sub_add _ _
    _ ≤ logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r * r +
        ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ := by linarith
    _ = ‖logSqHolo (ℓ l) (c l) (b l) (M l) (φ l) (1 / 2)‖ +
        r * logSqDomBound (ℓ l) (c l) (b l) (M l) (L l) (φ l 0) r
```

## State of the note (pinned to grammar 245a456)
Formal: §2 DLN flat prior at every depth (exact identity with the Gamma log-moments `H_j`; `H₀,H₁,H₂` evaluated); 1D polar dictionaries (log, mixed, log²); Gaussian product zeta `ζ_L` and its order-`L` pole; the depth-two Gaussian two-term expansion with explicit remainder; the all-depth conditional reduction `Z_{L+1}(N) = E[(1+N(∏W)²)^{−1/2}]` and `ζ_K = 2^s ζ_L` with its leading coefficient. §3 cone: exact Leray closed form with Gaussian tails. §4 blow-up: tie formulas (polynomial / smooth with supplied decomposition / arbitrary smooth via Hadamard), the Laurent data of `ζ(w) = 2^{3w+1}Γ(w+½)²` at `−½`, AND the two-term Laplace expansion of the model itself with `c_{½,1} = √(π/2)`, `c_{½,0} = √(π/2)(5 log 2 − γ)`. §5 rank-one: normal Gaussian integral in adapted coordinates, gauge-independent tilt. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball with the domination, the envelope and the basepoint adapter derived from the fibre data.
Derivation-only (checked numerically): the Gaussian DLN asymptotic transfer for `L ≥ 3` (`Z_3(N)/[(log N)²/(2·2π^{1/2}... )]` still 1.30 at `N = 10⁶`, slow `1/log N` approach; the note's polynomials `P_{L−1}`); the Bessel closed form at `L = 2`; `H₃`, `ζ(3)` in `Q₃`; the naive Bayes envelope `M_±(λ)`: facewise integrability of the envelope (`η + 2rβ < a`), joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the cone averaged posterior (domination for the `ξ`-average) and the exact expansion prefactors; the blow-up higher poles `c_{3/2,·}` and the observable expansions of §4; rank-one beyond alignment; the Morse–Bott passage; the smooth-amplitude tie remainder beyond `O(1)`.

## Library facts
Everything of rounds 1–6, in particular the general-amplitude engine `ampJ_two_term` (`AmpData`: `0 ≤ a ≤ 1`, `1 − a ≤ Au²` on `(0,1]`, `a ≤ e^{−u/2}` for `u ≥ 1`; conclusion `|J_a(ε) − (log(4/ε) + R_a)| ≤ Aε(log(1/ε)+1) + 4ε`, `R_a = ∫₀^∞ (a − 1_{(0,1]})·2/u`), the renormalised constants `−γ` (`∫(e^{−v} − 1_{(0,1]})/v`), `log 2 − γ` (with `1_{(0,½]}`), `(log 2 − γ)/2` (`a = e^{−u⁴/2}`), Bochner peel `integral_pi_succ_symm`, `Integrable.fintype_prod`, `integral_comp_rpow_Ioi_of_pos`, `integral_comp_mul_left_Ioi`, `integral_comp_abs`, Mellin engine `hasDerivAt_mellinIoc`, `Convex.norm_image_sub_le_of_norm_deriv_le`, Gamma values at ½ and 1, `Complex.hasDerivAt_Gamma_one`. Mathlib pin v4.33.1 (no Bessel functions, no polygamma beyond what is derived).

## Questions
1. Fidelity check (brief) of DCXIV–DCXVII against the note's claims and your round-6 specifications: (a) DCXV proves the note's model, with remainder `O(N^{−1} log N)` rather than the true `O(N^{−3/2} log N)` — is the stated bound and the constant `5 log 2 − γ` right (the renormalised constant of `e^{−u⁴/2}` is `(log 2 − γ)/2`; `log(4m²)` gives `2 log 2 + ½ log N`); (b) DCXVI's leading coefficient `√2(−1/√(2π))^L` in the negative-moment variable versus your `2^{−(L−1)/2}π^{−L/2}`; (c) DCXVII's envelope constant `C_r = 4(5+4/δ²)/(½−r)² + 18/r + 4/(1−2r)² + 2/r`, `δ = (½−r)/2` — any missing case (e.g. `M > 1`, `L < 0`)?
2. Rank the next three day-sized formal targets by value-per-effort for the note (concrete Lean statements + routes). Candidates: (a) the crossing `x²y²` with the unnormalised Gaussian prior, `∫ e^{−Nx²y²/2}e^{−|w|²/2} = 2π·gaussLaplace2(N)`, hence its two-term expansion `√(2π)(log N + 3 log 2 − γ)/√N` — a cheap corollary of DCVII/DCXII for the paper's running example (is it worth a row, and what does the note claim for it); (b) the depth-three Gaussian DLN expansion `Z_3(N) = E[(1 + N W₁²W₂²)^{−1/2}]`: is there a route through the `J` engine (inner integral at fixed `W₁` is `J`-like with `ε = 1/(N W₁²)`, but the outer integral of `log(1/|x|)/|x|`-type terms needs the cutoff at `|x| ~ N^{−1/2}`) to the `(log N)²` leading term with explicit remainder, or at least the leading coefficient `1/(2·√(2π)·... )`; give the two-term/three-term target and the route if day-sized; (c) the cone model averaged posterior (state what the note's exact `ξ`-dependent integrand is and what majorant is needed); (d) rank-one beyond alignment: the orthogonal change of coordinates lemma (Gaussian invariance) for the normal integral of DXCVIII; (e) the blow-up model's next pole `c_{3/2,1} = √(π/2)/16`: a three-term expansion `Z_N = √(π/2)(log N + 5 log 2 − γ)/√N + N^{−3/2}(α₁ log N − β₁) + O(N^{−2} log N)` via a second-order version of the amplitude engine (expand `1/√(u²+ε)` and the amplitude to the next order) — day-sized?; (f) an abstract "Mellin transfer" theorem for a zeta with a double pole and an explicit Mellin representation of `Z_N`, which would make DCX ⇒ DCXV a theorem for every model with the same zeta (what is the minimal hypothesis set; is it a week rather than a day). Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the four new files (the `w`/`u` variable names, `AmpData` with `A` versus your `W`, the unnormalised prior `e^{−|w|²/2}` of the blow-up model versus the normalised prior of the Gaussian DLN files, the sign `(−1)^L`).
Answer concisely with Lean-facing detail.
