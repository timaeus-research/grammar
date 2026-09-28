You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 6f88eea, 1024 modules, zero sorry/axiom) of the examples note `examples_slop.tex`. Round 30 executed in full: DCLXXXVII (`BlowUpMovingAmplitude.lean`, part A) and DCLXXXVIII (`BlowUpQuarticSecondOrder.lean`, parts B+C). The blow-up second half is CLOSED. Public statements:

```lean
noncomputable def movingAmp (ε u : ℝ) : ℝ := blowAmpInf u * Real.exp (-ε * u ^ 2 / 2)
theorem blowAmp_eq_movingAmp {m : ℝ} (hm : 0 < m) : blowAmp m = movingAmp (1 / m ^ 2)
theorem exp_neg_sub_one_add_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp (-x) - 1 + x ∧ Real.exp (-x) - 1 + x ≤ x ^ 2 / 2
theorem integral_cube_mul_exp_neg_quartic : ∫ u in Ioi (0 : ℝ), u ^ 3 * Real.exp (-u ^ 4 / 2) = 1 / 2
noncomputable def movingMoment (ε : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)
theorem movingJ_taylor_remainder {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + ε * movingMoment ε ∧
      ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + ε * movingMoment ε ≤ ε ^ 2 / 8
noncomputable def momentRem (ε u : ℝ) : ℝ := u ^ 2 * blowAmpInf u * (1 / Real.sqrt (u ^ 2 + ε) - 1 / u)
theorem momentRem_middle {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |momentRem ε u + ε / (2 * u)| ≤ ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 / u ^ 3
theorem movingMoment_log_remainder {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |movingMoment ε - Real.sqrt (Real.pi / 2) / 2 + ε / 4 * Real.log (1 / ε)| ≤ 2 * ε
theorem movingJ_sub_frozen {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + Real.sqrt (Real.pi / 2) / 2 * ε -
      ε ^ 2 / 4 * Real.log (1 / ε)| ≤ 3 * ε ^ 2
-- DCLXXXVIII
theorem kernel_third_order {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ 3 / 4 * ε ^ 2 / u ^ 5 - (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) ∧
      3 / 4 * ε ^ 2 / u ^ 5 - (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) ≤ 5 / 8 * ε ^ 3 / u ^ 7
theorem blowAmpInf_sub_one_add_bounds (u : ℝ) :
    0 ≤ blowAmpInf u - 1 + u ^ 4 / 2 ∧ blowAmpInf u - 1 + u ^ 4 / 2 ≤ u ^ 8 / 8
theorem quarticRem_middle {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ quarticRem ε u + 3 / 8 * ε ^ 2 / u ∧
      quarticRem ε u + 3 / 8 * ε ^ 2 / u ≤ 3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 / u ^ 3
theorem abs_integral_quarticRem_second {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |(∫ u in Ioc (0 : ℝ) 1, quarticRem ε u) + 3 / 16 * ε ^ 2 * Real.log (1 / ε)| ≤ ε ^ 2
theorem quarticJ_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ blowAmpInf ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      Real.sqrt (Real.pi / 2) / 2 * ε - 3 / 16 * ε ^ 2 * Real.log (1 / ε))| ≤ 2 * ε ^ 2
theorem movingJ_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (movingAmp ε) ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      1 / 16 * ε ^ 2 * Real.log (1 / ε))| ≤ 5 * ε ^ 2
theorem blowupLaplace_three_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N -
      Real.sqrt (2 * Real.pi) / 32 * Real.log N / (N * Real.sqrt N)| ≤
      5 * Real.sqrt (2 * Real.pi) / (N * Real.sqrt N)
```

Numerics (`blowup_three_term_check.py`, mpmath): frozen residual/ε² → −0.1458, moving residual/ε² → 0.090266, and `(Z_N − main − third)·N^{3/2} = 0.22626` from N = 10² to 10⁵ (0.018 of the bound). OBSERVATION (mine, please check): the Mellin transfer from `ζ(w) = 2^{3w+1}Γ(w+½)²` at its double pole `w = −3/2` gives `Γ(t−1)² = 1/t² + (2−2γ)/t + …`, `2^{3w+1} = 2^{−7/2}(1 + 3t log2 + …)`, so `ζ(−3/2+t) = 2^{−7/2}[t^{−2} + (2 − 2γ + 3log2)t^{−1} + …]` and the `N^{−3/2}` term of `Z_N` is `Γ(3/2)·2^{−7/2}·N^{−3/2}[log N − ψ(3/2) + 2 − 2γ + 3log2] = (√(2π)/32)(log N + 5log2 − γ)N^{−3/2}` (using `ψ(3/2) = 2 − γ − 2log2`), whose constant `(√(2π)/32)(5log2 − γ) = 0.22626` matches the numerics exactly, and in ε-form the ε² constant of `J_{a_ε}` is `(5log2 − γ)/32 = 0.090266` — also matching. So the SAME bracket `log N + 5log2 − γ` multiplies both `N^{−1/2}` and `N^{−3/2}` (a coincidence of `Γ(t−1)² = Γ(t)²/(t−1)²`: the `2/t` from `1/(1−t)²` cancels the `−2` in `ψ(3/2) − ψ(1/2) = 2`). The full three-term statement would therefore be
  `|Z_N − √(π/2)(log N + 5log2 − γ)/√N − (√(2π)/32)(log N + 5log2 − γ)/(N√N)| ≤ C (log N + 1)/N^{5/2}`  (next pole at −5/2, double).

## Existing cone API (for candidate (v))
```lean
noncomputable def coneQ (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ  -- q(u) = (|z₁|² − |z₂|²)/2
noncomputable def gaussW (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ -- e^{−|u|²/2}
theorem lintegral_radial_sq (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :  -- ∫_{ℝ²} Ψ(|z|²) = π ∫₀^∞ Ψ
theorem lintegral_cone_gauss (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u, G (coneQ u) * ENNReal.ofReal (gaussW u) =
      ENNReal.ofReal Real.pi * (ENNReal.ofReal Real.pi *
        ∫⁻ p in Ioi 0, ∫⁻ t in Ioi 0, G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)))
theorem lintegral_quadrant (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p in Ioi 0, ∫⁻ t in Ioi 0, G ((p - t) / 2) * ENNReal.ofReal (Real.exp (-(p + t) / 2)) =
      2 * ∫⁻ v, G v * ENNReal.ofReal (Real.exp (-|v|))
theorem map_coneQ_gaussian : Measure.map coneQ (volume.withDensity (ofReal ∘ gaussW)) =
      volume.withDensity fun v => ENNReal.ofReal (2 * Real.pi ^ 2 * Real.exp (-|v|))
theorem integral_cone_gaussian (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ u, g (coneQ u) * gaussW u = ∫ v, g v * (2 * Real.pi ^ 2 * Real.exp (-|v|))
theorem cone_evidence_closed {N : ℝ} (hN : 0 < N) (a : ℝ) : ... -- Gaussian tail closed form
theorem cone_third_coefficient : Tendsto (fun N => N√N(Z_N − 4π²√(π/2)/√N + 4π²/N)) atTop (𝓝 (2π²√(π/2)))
```
The note's Proposition (prop:cone_leray): for `F` smooth with derivatives integrable against the Leray form, `L_F(v) = A_F(v) + B_F(v)|v|` with `A_F, B_F` smooth, `A_F(0) = L_F(0)`, `B_F(0) = ½(L_F'(0⁺) − L_F'(0⁻)) = −2π²F(0)` (proof: for v > 0 the density is `2π²∫_{2v}^∞ F̄(p, p−2v)dp`, for v < 0 it is `2π²∫₀^∞ F̄(p, p−2v)dp`, with `F̄` the circle averages in `(p,t) = (|z₁|², |z₂|²)`; the jump of the derivative is `−4π²F̄(0,0)`). The round-29/30 candidate (v) was the "corner limit" `(L_F(t) + L_F(−t) − 2L_F(0))/t → −4π²F(0)` for `F ∈ C_c²` — you judged it "attractive but likely needs more fresh prior-localization and density regularity infrastructure".

## Naive Bayes candidate (vii)
Round 29 §3 proposed the localised exact-phase replacement `|e^{−NK} − e^{−NK₀}| ≤ N|K − K₀|e^{−cNr²}` on `V ≥ v₀`, where the surrogate `nbSurrogate` (quadratic phase, exact) is a theorem and `NaiveBayesLogSqMoment` gives `c₃ = π√(2π)V` for `N^{−3/2}log²N`. The library's NB files: NaiveBayes, NaiveBayesClosedForm, NaiveBayesConditionalDensity, NaiveBayesDensity, NaiveBayesFibreFiniteness, NaiveBayesFibreMass, NaiveBayesFixedDomainDensity, NaiveBayesLogSqMoment, NaiveBayesPushforward, NaiveBayesSurrogate.

## Questions
1. Fidelity of DCLXXXVII–DCLXXXVIII (brief): the constants `ε²/8`, `2ε`, `3ε²`, `2ε²`, `5ε²`, `5√(2π)`; the sign conventions; the claim in HEADLINES that the `N^{−3/2}log N` coefficient "is the double pole of ζ at −3/2 read off from the integral"; and my transfer computation above (the bracket coincidence) — is `(√(2π)/32)(log N + 5log2 − γ)` right?
2. NEXT UNIT (design in Lean-facing detail, with explicit constants and the split points). Candidates: (x) THE `N^{−3/2}` CONSTANT: prove `J_{a_ε}(ε) = log(4/ε) + R_∞ + (1/16)ε²log(1/ε) + ((5log2 − γ)/32)ε² + O(ε³log(1/ε))` — this needs every piece to third order: the elementary integral's ε² coefficient (−3/16, from `2log(1+x) = 2x − x² + …`, `x = (s−1)/2`), the frozen inner/outer remainders' ε² constants (Hadamard finite parts `∫(a − 1 + (u⁴/2)1_{u≤1})/u⁵`-type, which evaluate through `Γ` at quarter arguments? or through the substitution `y = u⁴` to `∫(e^{−y/2} − 1 + (y/2)1_{y<1})y^{−2}dy` = a renormalised Gamma value in γ, log2), the moving moment's ε constant `c_I` in `I(ε) = ½√(π/2) − (ε/4)log(1/ε) + c_Iε + …`, and the Taylor term `(ε²/8)·∫(…)`. Is there a slicker route — e.g. prove the ε² constant by an EXACT identity (differentiate in ε? the function `ε ↦ J_∞(ε)` satisfies an ODE? `J_∞` as a Mellin convolution with the closed-form zeta?) — or via the library's Mellin transfer if the blow-up model's `ζ` and the transfer theorem are available (`BlowUpZeta.lean` has `lintegral_blowK_gauss_closed`; is there a transfer theorem `Z_N = residue sum + O(N^{-k})` for a model with a closed-form zeta on a strip? I believe the library proves the leading two terms "directly from the integral rather than through the transfer" for this model, which suggests no). Size estimate in units. (v) the cone general-prior corner, minimal meaningful statement (e.g. `F(u) = f(|z₁|²)g(|z₂|²)` product-radial with `f,g` C¹ compactly supported, so that the bipolar reduction `lintegral_cone_gauss` generalises verbatim to `π²∫∫ f(p)g(t)G((p−t)/2)`, and the density is `2π²∫ f(p)g(p−2v)dp` on `v<0`, `2π²∫_{2v}^∞ f(p)g(p−2v)dp` on `v>0`; the corner limit is then a one-variable FTC statement). (vii) NB localised exact-phase. Rank (x), (v), (vii) with reasons, and design the top one completely: definitions, lemma list with statements, constants, Mathlib lemmas, hazards.
3. Convention hazards for the chosen unit.
Answer concisely with Lean-facing detail.
