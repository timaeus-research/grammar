You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 18f2d91, 1022 modules, zero sorry/axiom) of the examples note `examples_slop.tex`. Round 29 executed: DCLXXXV (`FlatDepthZetaClosed.lean`: `H₃ = Γ'''(½) = √π[−p³ − 3pπ²/2 − 14ζ(3)]`, the flat-prior depth-two/three identities with the note's `Q₂, Q₃` (`14ζ(3)`), and the depressed form `(taylor (−κ_L) (enginePoly L)).coeff (L−2) = 0` at every depth) and DCLXXXVI (`BlowUpQuarticLinear.lean`, your target (vi) first half): ★★★ `quarticJ_linear_remainder : |J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)ε)| ≤ 2ε²(log(1/ε)+1)` for `0 < ε ≤ 1`, with `quarticLinear_eq : ∫₀^∞(1−e^{−u⁴/2})/u³ = ∫₀^∞ u e^{−u⁴/2} = ½√(π/2)` by Mathlib's improper by-parts lemma (no `arsinh` needed: I used the kernel gap `2/√(u²+ε) − 2/u = −ε/u³ + r`, `0 ≤ r ≤ (3/4)ε²/u⁵`, the split at `√ε`, and the elementary integral to second order). Numerics: residual/(ε²log(1/ε)) → −3/16 from above (−0.203 at ε = 10⁻⁴), as you predicted.

## HEADLINES rows DCLXXXV–DCLXXXVI
| **DCLXXXV** | ★★★ **§2 COROLLARIES: THE FLAT-PRIOR POLYNOMIALS IN ζ-VALUES AND THE DEPRESSED FORM AT EVERY DEPTH (u1021; examples_slop §2 eq. dln_flat; Astra round-29 items 2(a)–(b))**: `FlatDepthZetaClosed.lean` — `gammaThirdOne_eq_zeta` (`Γ'''(1) = −2ζ(3) − γ³ − γπ²/2`), `gammaLogMoment_three : H₃ = Γ'''(½) = √π[−p³ − 3pπ²/2 − 14ζ(3)]` (DCLXXIII's `gammaLogMoment_eq_iterate` + DCLXXII's third-order relation + the ζ-bridge), `depthPoly_two_eq : P₂ = √π[(X+p)² + π²/2]`, `depthPoly_three_eq : P₃ = √π[(X+p)³ + (3π²/2)(X+p) + 14ζ(3)]` (DCI's binomial polynomial; `norm_num [values]` AFTER `simp only [sum_range_succ]` because the indices `2 − 1` block the rewrites), ★★ `depthInt_two_closed`, ★★★ `depthInt_three_closed` (`Z_N^{flat} = √(2π)/(6√N)·[t³ + (3π²/2)t + 14ζ(3)] − R₃(N)`, `t = log N + γ + log 2`, `|R₃| ≤ (2/N)⁴e^{−N/2}` by DCI): the note's `Q₂`, `Q₃` with `14ζ(3)` against the Gaussian prior's `6ζ(3)`; ★★ `taylor_enginePoly_coeff_sub_two : (taylor (−κ_L) (enginePoly L)).coeff (L−2) = 0` for every `L ≥ 2` (`Polynomial.taylor_coeff` → `hasseDeriv (L−2)` of degree ≤ 1 → `eval_eq_sum_range'`, `hasseDeriv_coeff`, `Nat.choose_succ_self_right`, DCLXVII's `coeff_enginePoly_second` and the leading coefficient; `L = K + 2`), `taylor_enginePoly_eval` (`= P_L(t − κ_L)`): the depressed form `P_L(log N + κ_L)` with no `t^{L−2}` term is a theorem at every depth. Astra round 29 (`tide-log/gpt6_examples_round29_v1.md`): DCLXXXIII–DCLXXXIV fidelity confirmed (`Q₅` re-derived from the centred log-jet `ℓ₂ = 2π²/3, ℓ₃ = −λ₃/3, ℓ₄ = 5λ₄/6, ℓ₅ = −13λ₅/60`); post-§2 ranking: (vi) the blow-up frozen quartic correction `J_∞(ε) = log(4/ε) + R_∞ + ½√(π/2)ε + O(ε²(log(1/ε)+1))` by parts (`arsinh`), then `−(3/16)ε²log(1/ε)` and the moving-amplitude `+¼`, net `√(2π)/32 · N^{−3/2}log N`; (v) the cone vertex for a general `C_c²` prior as `lim (ρ_F(t) + ρ_F(−t) − 2ρ_F(0))/t = −4π²F(0)`; (vii) NB: a localised uniform exact-phase replacement theorem `|e^{−NK} − e^{−NK₀}| ≤ N|K − K₀|e^{−cNr²}` away from `V = 0`; observable rates `E[w₁²] ~ 2(L−1)/log N` (not `2/log N`) via `2P_L'/P_L`. | FlatDepthZetaClosed.lean |
| **DCLXXXVI** | ★★★ **THE FROZEN QUARTIC AMPLITUDE TO SECOND ORDER: `J_∞(ε) = log(4/ε) + R_∞ + ½√(π/2)ε + O(ε²(log(1/ε)+1))` (u1022; examples_slop §4; Astra round-29 target (vi), first half)**: `BlowUpQuarticLinear.lean` — `kernel_second_order` (`0 ≤ 2/√(u²+ε) − 2/u + ε/u³ ≤ (3/4)ε²/u⁵`: with `s = √(u²+ε)` the left side is `(s−u)²(s+2u)/(su³)` and `(s+2u)u² ≤ (3/4)(s+u)²s` factors as `(s−u)(¾s² + (9/4)su + 2u²) ≥ 0`), `one_sub_blowAmpInf_nonneg/le` (`0 ≤ 1 − e^{−u⁴/2} ≤ u⁴/2`), the inner remainder `quarticRem ε u = (a−1)(2/√ − 2/u + ε/u³)` with `|·| ≤ u³ + εu/2` (any `u`) and `≤ (3/8)ε²/u` (second order), `integrableOn_quarticRem`, ★★ `abs_integral_quarticRem_le ≤ ε²/2 + (3/16)ε² log(1/ε)` (split at `√ε`: `integral_pow` below, `integral_one_div_of_pos` + `Real.log_sqrt` above), the outer remainder `quarticOuter` with `≤ (3/4)ε²u^{−5}` and `abs_integral_quarticOuter_le ≤ (3/16)ε²` (`integral_Ioi_rpow_of_lt` at `−5`), `elem_second_order` (`|2 log((1+√(1+ε))/√ε) − log(4/ε) − ε/2| ≤ ε²/4`, via `1 + ε/2 − ε²/8 ≤ √(1+ε) ≤ 1 + ε/2` and `x − x² ≤ log(1+x) ≤ x`), `quarticLinear = ∫₀^∞(1 − a)/u³`, `integral_mul_exp_neg_quartic : ∫₀^∞ u e^{−u⁴/2} = ½√(π/2)` (`integral_rpow_mul_exp_neg_mul_rpow` at `p = 4, q = 1, b = ½`), ★★ `quarticLinear_eq = ½√(π/2)` (Mathlib's improper by parts `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = 1 − e^{−x⁴/2}`, `v = −1/(2x²)`, both boundary limits by `squeeze_zero_norm'` with EXPLICIT `(a := …)`), `integral_inv_cube_Ioi_one`, ★★★ `quarticJ_linear_remainder : |J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)ε)| ≤ 2ε²(log(1/ε)+1)` for `0 < ε ≤ 1` (DCXIV's decomposition with the two refined remainders and the linear coefficient `−∫₀¹(a−1)/u³ − ∫₁^∞ a/u³ + ½ = ∫₀^∞(1−a)/u³`). So the frozen quartic amplitude has NO `ε log(1/ε)` term; the moving amplitude `e^{−u⁴/2}e^{−εu²/2}` cancels the linear term and the `N^{−3/2}log N` coefficient `√(2π)/32` needs the next order `−(3/16)ε²log(1/ε)` (frozen) `+ ¼` (moving) — the second half. Lean: typed `IntegrableOn` witnesses for every `integral_add`/`integral_sub` (Pi-add lambdas do not match); `hasDerivAt_pow` avoids the `Pi.pow_apply` mess; `HasDerivAt.div` with `hasDerivAt_const` for `−1/(2x²)`; `field_simp` closes several goals outright (no trailing `ring`). | BlowUpQuarticLinear.lean |

## Public statements of DCLXXXVI
```lean
/-- `0 ≤ 2/√(u²+ε) − 2/u + ε/u³ ≤ (3/4) ε²/u⁵`. -/
theorem kernel_second_order {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ 2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3 ∧
      2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3 ≤ 3 / 4 * ε ^ 2 / u ^ 5

theorem one_sub_blowAmpInf_nonneg (u : ℝ) : 0 ≤ 1 - blowAmpInf u

theorem one_sub_blowAmpInf_le (u : ℝ) : 1 - blowAmpInf u ≤ u ^ 4 / 2

/-- The remainder integrand. -/
noncomputable def quarticRem (ε u : ℝ) : ℝ

theorem measurable_quarticRem (ε : ℝ) : Measurable (quarticRem ε)

theorem abs_quarticRem_le_low {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticRem ε u| ≤ u ^ 3 + ε * u / 2

theorem abs_quarticRem_le_high {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticRem ε u| ≤ 3 / 8 * ε ^ 2 / u

theorem integrableOn_quarticRem {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (quarticRem ε) (Ioc 0 1)

/-- `|∫₀¹ quarticRem| ≤ ε²/2 + (3/16)ε² log(1/ε)`. -/
theorem abs_integral_quarticRem_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ u in Ioc (0 : ℝ) 1, quarticRem ε u| ≤ ε ^ 2 / 2 + 3 / 16 * ε ^ 2 * Real.log (1 / ε)

theorem integrableOn_rpow_neg_five : IntegrableOn (fun u : ℝ => u ^ (-5 : ℝ)) (Ioi 1)

theorem integral_rpow_neg_five : ∫ u in Ioi (1 : ℝ), u ^ (-5 : ℝ) = 1 / 4

theorem integrableOn_blowAmpInf_div_cube :
    IntegrableOn (fun u : ℝ => blowAmpInf u / u ^ 3) (Ioi 1)

/-- The outer remainder integrand. -/
noncomputable def quarticOuter (ε u : ℝ) : ℝ

theorem abs_quarticOuter_le {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |quarticOuter ε u| ≤ 3 / 4 * ε ^ 2 * u ^ (-5 : ℝ)

theorem integrableOn_quarticOuter {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (quarticOuter ε) (Ioi 1)

/-- `|∫₁^∞ quarticOuter| ≤ (3/16) ε²`. -/
theorem abs_integral_quarticOuter_le {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioi (1 : ℝ), quarticOuter ε u| ≤ 3 / 16 * ε ^ 2

/-- `|2 log((1 + √(1+ε))/√ε) − log(4/ε) − ε/2| ≤ ε²/4` for `0 < ε ≤ 1`. -/
theorem elem_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) - Real.log (4 / ε) - ε / 2| ≤
      ε ^ 2 / 4

/-- The linear coefficient `κ = ∫₀^∞ (1 − e^{−u⁴/2})/u³ du`. -/
noncomputable def quarticLinear : ℝ := ∫ u in Ioi (0 : ℝ), (1 - blowAmpInf u) / u ^ 3

theorem integrableOn_one_sub_blowAmpInf_div_cube_inner :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioc 0 1)

theorem integrableOn_one_sub_blowAmpInf_div_cube_outer :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioi 1)

theorem integrableOn_one_sub_blowAmpInf_div_cube :
    IntegrableOn (fun u : ℝ => (1 - blowAmpInf u) / u ^ 3) (Ioi 0)

theorem integrableOn_mul_exp_neg_quartic :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u ^ 4 / 2)) (Ioi 0)

/-- `∫₀^∞ u e^{−u⁴/2} du = ½√(π/2)`. -/
theorem integral_mul_exp_neg_quartic :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-u ^ 4 / 2) = Real.sqrt (Real.pi / 2) / 2

/-- ★★ **The linear coefficient**: `∫₀^∞ (1 − e^{−u⁴/2})/u³ du = ½√(π/2)`, by parts. -/
theorem quarticLinear_eq : quarticLinear = Real.sqrt (Real.pi / 2) / 2

theorem integral_inv_cube_Ioi_one : ∫ u in Ioi (1 : ℝ), blowAmpInf u / u ^ 3 =
    1 / 2 - ∫ u in Ioi (1 : ℝ), (1 - blowAmpInf u) / u ^ 3

/-- ★★★ **The frozen quartic amplitude to second order**:
`|J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)·ε)| ≤ 2ε²(log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem quarticJ_linear_remainder {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ blowAmpInf ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      Real.sqrt (Real.pi / 2) / 2 * ε)| ≤ 2 * ε ^ 2 * (Real.log (1 / ε) + 1)
```

## The blow-up reduction (DCXV, `BlowUpLaplaceExpansion.lean`)
```lean
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
    have e3 : 1 + m ^ 4 * (1 / m * u) ^ 2 = m ^ 2 * (u ^ 2 + 1 / m ^ 2) := by field_simp; ring
    rw [e1, e2, e3, Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
    unfold blowAmp
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  unfold ampJ
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  field_simp

/-! ### The amplitude data -/


```
with `blowAmp m u = e^{−u⁴/2} e^{−u²/(2m²)}`, `blowAmpInf u = e^{−u⁴/2}`, `ε = 1/m²`, `N = m⁴`, `blowupLaplace (m⁴) = √(2π)/m² · ampJ (blowAmp m) (1/m²)`, `ampRenorm_blowAmpInf = (log 2 − γ)/2`, `ampRenorm_blowAmp_sub_le : |R_{a_m} − R_∞| ≤ 3/m²`, and `blowupLaplace_two_term_bound : |Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N`.

## Questions
1. Fidelity of DCLXXXVI (brief): the kernel second-order bound and its constant `3/4`; the split constants `ε²/2` (below `√ε`) and `(3/16)ε² log(1/ε)` (above); the outer `(3/16)ε²`; the elementary `ε²/4`; the linear coefficient identity `−∫₀¹(a−1)/u³ − ∫₁^∞ a/u³ + ½ = ∫₀^∞(1−a)/u³` and the by-parts boundary terms.
2. THE SECOND HALF. The true evidence is `Z_N = √(2π)ε·J_{a_ε}(ε)` with the MOVING amplitude `a_ε(u) = e^{−u⁴/2}e^{−εu²/2}` and `ε = N^{−1/2}`, and the target is the `N^{−3/2}log N` coefficient `√(2π)/32`, i.e. `J_{a_ε}(ε) = log(4/ε) + R_∞ + (1/16)ε²log(1/ε) + O(ε²)`. Decomposition I have in mind: `J_{a_ε}(ε) − J_∞(ε) = ∫₀^∞ 2(a_ε − a_∞)/√(u²+ε)` with `a_ε − a_∞ = e^{−u⁴/2}(e^{−εu²/2} − 1) = −(ε/2)u²e^{−u⁴/2} + O(ε²u⁴e^{−u⁴/2})`, so the difference is `−ε∫₀^∞ u²e^{−u⁴/2}/√(u²+ε) + O(ε²)`, and `∫₀^∞ u²e^{−u⁴/2}/√(u²+ε) = ∫₀^∞ u e^{−u⁴/2}du + ∫₀^∞ u²e^{−u⁴/2}(1/√(u²+ε) − 1/u) = ½√(π/2) − (ε/2)∫ u²e^{−u⁴/2}/u³ + … ` — the last integral `∫₀^∞ e^{−u⁴/2}/u du` DIVERGES logarithmically at 0, which is exactly the source of the `ε·ε log(1/ε)` term: `∫₀^∞ u²e^{−u⁴/2}(1/√(u²+ε) − 1/u)du = −(ε/2)·(½ log(1/ε)) + O(ε)`? (so that the moving amplitude contributes `−ε·[½√(π/2) − (ε/4)log(1/ε) + O(ε)] = −½√(π/2)ε + (1/4)ε²log(1/ε) + O(ε²)`, cancelling the frozen linear term and adding `+¼`, as you said). And the frozen `−(3/16)ε²log(1/ε)`: from DCLXXXVI's inner remainder above `√ε`, `∫_{√ε}^1 (a−1)(r)` with `(a−1) ≈ −u⁴/2` and `r ≈ (3/4)ε²/u⁵`, giving `−(3/8)ε²∫_{√ε}^1 du/u = −(3/16)ε²log(1/ε)` (the bound is attained asymptotically). Please give: (a) the exact statements for the moving-amplitude unit, e.g. `movingJ_sub_frozen : |J_{a_ε}(ε) − J_∞(ε) + ½√(π/2)ε − ¼ε²log(1/ε)| ≤ Cε²` and for the frozen refinement `|J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)ε) + (3/16)ε²log(1/ε)| ≤ Cε²`, with the mechanism for the exact `log(1/ε)` coefficients (an explicit integral `∫_{√ε}^1 du/u` after subtracting the Taylor tails — how to organise the subtraction so that each piece is either an exact elementary integral or `O(ε²)`); (b) the honest size (one unit each? the frozen refinement needs the third-order kernel gap `r = (3/4)ε²/u⁵ + O(ε³/u⁷)` and the quartic amplitude's `1 − a = u⁴/2 − u⁸/8 + …` — which cutoffs); (c) the final theorem `blowupLaplace` with `N^{−3/2}log N`: `|Z_N − √(π/2)(log N + 5log2 − γ)/√N − (√(2π)/32)·log N/N^{3/2}| ≤ C/N^{3/2}`? (note the moving amplitude ALSO changes the constant `R_{a_ε} − R_∞ = O(ε)` — DCXV bounds it by `3ε`; its exact linear coefficient enters the `N^{−3/2}` constant, which we do not need for the logarithmic coefficient but should we identify it?).
3. Alternatively pivot: (v) the cone general-prior corner limit (`(ρ_F(t)+ρ_F(−t)−2ρ_F(0))/t → −4π²F(0)` for `F ∈ C_c²`) — is it a better day than the blow-up second half? (vii) NB localised exact-phase replacement. Rank.
4. Convention hazards: `ε = N^{−1/2}` vs `1/m²` with `N = m⁴`; `log(4/ε)` vs `log N`; the sign of `R_{a_ε} − R_∞`.
Answer concisely with Lean-facing detail.
