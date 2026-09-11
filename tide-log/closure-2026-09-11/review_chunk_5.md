# Fidelity review — dot chunk 5/6 (141 dots)

Only problematic dots are listed. Verdict tags: OVER-CLAIM / MISLINK / IMPRECISE / CONDITIONAL-NOT-STATED.

## Mirror (`grammar_lean.tex`)

- **[mirror L2417] `headline_chart_posterior_limit`, `headline_quotient_in_distribution`** — OVER-CLAIM.
  Both dots sit on `\begin{cor}\label{cor:empirical_expectation}`, i.e. they certify the whole corollary (full expansion `eq:empirical_expectation_full_expansion`, recursive division via `lemma:division`, convergence of all `A_{k,p}`, `B_{k,p}`, `d_{s,q}`). Lean proves only the 2D chart-level leading term with deterministic amplitudes, equal starting exponents `(h₁+1)/k₁ = (h₂+1)/k₂ = p`, and `0 < y₁(0,0)` (`headline_chart_posterior_limit`), plus a generic quotient-in-distribution lemma (`headline_quotient_in_distribution`, whose own docstring says it is "NOT the paper's formal division lemma"). The scope remark `rem:empirical_expectation_lean` says this honestly, but the header placement contradicts the "bounded precise statements only" dot convention.
  Fix: delete both `\leanrefL` from the `\begin{cor}` line and attach them inside `rem:empirical_expectation_lean`: after `the Lean formalisation proves the leading term of the quotient: $Z_n[\phi]/Z_n[1]\Rightarrow\eta_\phi(0)/\eta_1(0)$` put `\leanrefL{Grammar/HeadlinePosterior.lean\#L82}{headline\_chart\_posterior\_limit}`, and after `the generic quotient theorem for jointly convergent pairs with a.s.\ positive limiting denominator` put `\leanrefL{Grammar/HeadlinePosterior.lean\#L46}{headline\_quotient\_in\_distribution}`.

- **[mirror L2300] `evalF_xiCoord_sampleDatum_eq_neg_zetaEmp`, `dataBoxIntegral_sampleDatum_eq_sampling`** — CONDITIONAL-NOT-STATED.
  Both theorems assume `hA : xiCoord A = 0` (zero-phase amplitude datum); the box-core identity additionally assumes `hφ : ∀ v ∈ piBox …, ∫ a (X 0 ω') v ∂P = ∏ v i ^ k i` (the standard-form mean `E a(X,v) = v^k`) and `hca` on the whole box. The mirror sentence mentions neither (the companion note, L117–L121, states both).
  Fix: replace `when the coefficient family is the Taylor family of $-a$ the sample phase is minus the centred empirical process of the coefficient, and the certified box core at the sample datum is the sampling integral` by `when the amplitude datum $A$ has zero phase and the coefficient family is the Taylor family of $-a$ the sample phase is minus the centred empirical process of the coefficient, and, when moreover $\mathbb E a(X,v)=v^k$ on the box, the certified box core at the sample datum is the sampling integral`.

- **[mirror L2300] `lintegral_exp_phase_sampleDatum_le`** — CONDITIONAL-NOT-STATED.
  Lean takes `(hA : xiCoord A = 0)`; without it the sample phase carries `+ phase(A)(u)` and the Hoeffding bound fails. Sentence: "for the sample datum of an i.i.d. sample with bounded chart phase observations".
  Fix: add qualifier: `for the sample datum of an i.i.d.\ sample with bounded chart phase observations and a zero-phase amplitude datum`.

- **[mirror L2300] `tendsto_integral_scaled_assembly_sampleDatum`** — OVER-CLAIM ("needs only").
  Besides the three named inputs, Lean assumes `hA : ∀ j, xiCoord (A j) = 0`, `hAM : ∀ j, mass (etaCoord (A j)) ≤ M`, `hobs : ‖phaseObs …‖ ≤ M₀`, and the temperature constraint `hc2 : p * β * M₀ ^ 2 < 2` with `hp : 1 < p`.
  Fix: replace `needs only the distributional limit of the scaled core, dominated box exponent pairs and the remainder estimate` by `needs, for zero-phase amplitude data of bounded mass and $p\beta M_0^2<2$ for some $p>1$, only the distributional limit of the scaled core, dominated box exponent pairs and the remainder estimate`.

- **[mirror L2300] `tendsto_integral_scaled_sampleDatum_single`, `tendsto_integral_scaled_coreSum_sampleDatum`** — IMPRECISE ("conditional only on").
  Both also assume the chart moment certificate (`hsum`, `hc2`), `‖phaseObs‖ ≤ M₀` with `p * β * M₀ ^ 2 < 2`, `1 < p`, and zero-phase amplitude data with `mass (etaCoord A) ≤ M`. Only "bounded chart phase observations" is in the surrounding prose; the temperature restriction `βM₀² < 2` and the zero-phase amplitude are silent.
  Fix: replace `is a theorem conditional only on $\mathbb E|A_n\mathrm{Rem}_n|\to0$` by `is a theorem conditional, under the standing certificates (chart moment certificate, $\|\mathrm{obs}\|_{\ell^1}\le M_0$ with $\beta M_0^2<2$, zero-phase amplitude datum of bounded mass), only on $\mathbb E|A_n\mathrm{Rem}_n|\to0$`.

- **[mirror L2300] `integral_dataBoxCoeff_leading_eq`** — CONDITIONAL-NOT-STATED.
  Lean requires `hM : ∀ x, ‖phaseObs …‖ ≤ M₀`, `hβM : β * M₀ ^ 2 < 2` and `hA : xiCoord A = 0`; the sentence gives the face-integral formula unconditionally (the later "hence βc<2" sentence is about uniform integrability, a different point).
  Fix: add qualifier before the formula: `and, for bounded phase observations with $\beta M_0^2<2$ and a zero-phase amplitude datum, the limiting expectation is the covariance-modified face integral …`.

- **[mirror L2300] `map_eq_gaussianReal_of_marginals`** — CONDITIONAL-NOT-STATED (minor).
  Section `include hY hmarg htail` plus the theorem's own `(hM : ∀ ω, ‖Y 0 ω‖ ≤ M₀)`: a sure ℓ¹ bound on the observation, not just `L²` coordinates. Sentence: "every continuous linear functional of that ℓ¹ Gaussian limit … is a centred Gaussian variable".
  Fix: add qualifier: `for bounded observations, every continuous linear functional …`.

- **[mirror L2300] `exponentPair_eq_of_population_comparison`, `exists_exponentPair_of_Q`** — IMPRECISE (minor).
  Lean concludes `lam = lamH ∧ m - 1 = qH` (resp. `m - 1 = thetaH - 1`) with ℕ-subtraction, so `m = 0` and `m = 1` are not distinguished (they give the same `scaleA`); `θ_H` is used in the mirror without definition (it is the multiplicity `q_H + 1`, cf. `1 ≤ thetaH` in `exists_exponentPair_of_Q`).
  Fix: replace `forces $(\lambda,m)=(\lambda_H,\theta_H)$` by `forces $\lambda=\lambda_H$ and $m-1=\theta_H-1$ (the multiplicity $\theta_H\ge1$ being hironaka's log power plus one), i.e.\ $(\lambda,m)=(\lambda_H,\theta_H)$ for $m\ge1$`.

- **[mirror L2436] `gInt_isolated_bound`, `tendstoInMeasure_randomOneTerm`, `tendstoInDistribution_posterior_second_order_one`** — IMPRECISE.
  All three are stated at unit box radii only (`gInt ν h k β (fun _ => 1) …`, `gCoeff … (fun _ => 1) …`), whereas the neighbouring assembled statements (`tendstoInDistribution_posterior_second_order`, `…_posterior_leading`) carry general `b : Fin M → ℝ`. The sentence does not signal the restriction.
  Fix: add qualifier: `At multiplicity one (both leading log degrees $0$, and at unit box radii) the two-term remainder …` and `… converges in distribution to $0$ (at unit box radii): no $1/\log n$ correction at multiplicity one`.

- **[mirror L2453] `tendsto_dataBoxCoeff_leading`** — IMPRECISE.
  Lean: `dataBoxCoeff n h k β 1 (X a) lam …` — box radius `b = 1` only (docstring: "on the unit box"), and `lam` must be the attained minimum ratio (`hmin`, `hatt`). Sentence: "when the limit has ξ=0 the first-candidate coefficient converges to the population face functional".
  Fix: add qualifier: `when the limit has $\xi=0$ the first-candidate coefficient (on the unit box) converges to the population face functional`.

- **[mirror L2300] `reconstruct_tendstoInDistribution`** — IMPRECISE (minor).
  "transports the theorem": Lean concludes only `∃ ν, TendstoInDistribution (fun N ω => T (empiricalSum V P N ω) + A) atTop (fun z => T z + A) …`; the Gaussian finite-marginal identification of `ν` (part of "the theorem") is not restated in this conclusion.
  Fix: replace `transports the theorem` by `transports the convergence in distribution`.

- **[mirror L2300] `TorusCertificate.ofDivision`** — IMPRECISE (minor).
  The clause `$\|a(x,w)\|=\|f(x,\pi_{\mathbb C}(w))\|\,r^{-|k|}$ exactly on the torus` is not a stated conclusion; the def only records `torus_bound : ‖a x w‖ ≤ M x` with `M := fun x => H x * r⁻¹ ^ (∑ i, k i)` (the equality appears inside the proof as `hnorm`).
  Fix: move the dot so it certifies only the certificate: `… holds, then $\|a(x,w)\|=\|f(x,\pi_{\mathbb C}(w))\|\,r^{-|k|}$ exactly on the torus, and $a$ carries a torus certificate with envelope $H(x)r^{-|k|}$\leanrefL{…}{TorusCertificate.ofDivision}` (i.e. insert a comma so the dot's clause is the certificate).

## Companion note (`averaging_dataset.tex`)

- **[note L286] `polyBoundedPi_quartetW`** — MISLINK.
  The sentence certifies the explicit bound `0 ≤ W_i(g) ≤ √(2λ/β) + |g_i|/2`; the cited declaration only states `PolyBoundedPi (quartetW β lam ρ i)`, i.e. `∃ C k, ∀ z, |H z| ≤ C * (1 + ‖z‖) ^ k`. The explicit bound is `quartetW_le` (`Grammar/GaussianQuartetDet.lean#L126`) and nonnegativity is `quartetW_nonneg` (`#L98`).
  Fix: replace `\leanrefL{Grammar/GaussianQuartetDet.lean\#L171}{polyBoundedPi\_quartetW}` by `\leanrefL{Grammar/GaussianQuartetDet.lean\#L98}{quartetW\_nonneg}\leanrefL{Grammar/GaussianQuartetDet.lean\#L126}{quartetW\_le}` (optionally keep `polyBoundedPi_quartetW` on the later clause "the normalised quantities … are polynomially bounded in $g$").

- **[note L219] `lintegral_bilocalIntegrand_lt_top`** — OVER-CLAIM.
  The dot certifies `It is finite if and only if $A>0$, $B>0$ and either $H<2\sqrt{AB}$`. Lean proves only sufficiency: `(ha : 0 < a) (hb : 0 < b) (hh : h < 2 * Real.sqrt (a * b)) : … < ⊤`. The necessity of `A>0, B>0` (divergence when `A ≤ 0` or `B ≤ 0`) is not certified by any cited declaration (all `eq_top` results also assume `0 < a`, `0 < b`); the note's own summary sentence ("The Lean results establish …") omits that case, so the "if and only if" is over-certified.
  Fix: replace `It is finite if and only if $A>0$, $B>0$ and either $H<2\sqrt{AB}$\leanrefL{…}{lintegral\_bilocalIntegrand\_lt\_top}` by `For $A>0$, $B>0$ it is finite if $H<2\sqrt{AB}$\leanrefL{…}{lintegral\_bilocalIntegrand\_lt\_top}` (and keep "or $H=2\sqrt{AB}$ and $\lambda<1/4$" as the iff on the critical line; add `; the necessity of $A,B>0$ is not formalised` if the iff wording is retained).

- **[note L233] `cov_fluctuation_eq_connected`** — CONDITIONAL-NOT-STATED (minor).
  The prose condition is "(for β<1, so that the individual means are finite)" with `c=c'=2`; Lean additionally requires `hh : β ^ 2 * B_ij < 2 * √(a b)`, i.e. `βb < 2(1−β)` — for `b>0` this is `β<(1+b/2)^{-1}`, strictly stronger than `β<1`. (The threshold is stated two sentences earlier, but the parenthetical suggests `β<1` suffices for the identity.)
  Fix: replace `(for $\beta<1$, so that the individual means are finite)` by `(for $\beta<1$ and $H<2\sqrt{AB}$, i.e.\ $\beta<(1+b/2)^{-1}$ when $b>0$, so that the individual means and the product are finite)`.

- **[note L113] `dataPhase_sampleDatum`** — IMPRECISE / partial MISLINK.
  The sentence certifies two things: (a) the phase coefficients are `n^{-1/2}Σ(c_γ(X_i) − E c_γ)` and (b) they enter the standard integral "with the sign `+β√N u^k ξ`". The cited theorem is the phase-*evaluation* identity `dataPhase (sampleDatum …) u = n^{-1/2} Σ (evalF (c (X i ω)) (b • u) − ∫ …) + dataPhase A u` — it includes a `+ dataPhase A u` term the sentence omits, says nothing about the standard-integral sign, and (a) at the coefficient level is `xiCoord_sampleDatum` (`SampleDatum.lean#L142`).
  Fix: replace the single dot by `phase coefficients $n^{-1/2}\sum_i(c_\gamma(X_i)-\mathbb E c_\gamma)$\leanrefL{Grammar/SampleDatum.lean\#L142}{xiCoord\_sampleDatum} entering the standard integral with the sign $+\beta\sqrt N u^k\xi$\leanrefL{Grammar/SamplingCompatibility.lean\#L161}{exp\_sampling\_exponent\_eq\_core\_factor}` (keep `dataPhase_sampleDatum` if desired on the phrase "phase coefficients", noting it holds for a zero-phase `A`).

- **[note L241] `integrable_quartetD_rpow`** — CONDITIONAL-NOT-STATED (minor).
  Lean needs `(hpos : ∀ i, 0 < (A * A.transpose) i i)` (nondegenerate coordinates) in addition to `pβB_ii < 2`; the sentence states only the latter.
  Fix: add qualifier: `when $B_{ii}>0$ and $\beta pB_{ii}<2$ for every $i$`.

## Summary

141 dots reviewed (128 in the mirror remark at L2300/L2315/L2417–L2453, 13+ in the companion note sections L67–L287); 121 are faithful, 20 dots (grouped into 17 findings above) have problems. No dot was found linking to a theorem unrelated to its sentence; the one genuine MISLINK is `polyBoundedPi_quartetW` (polynomial-boundedness predicate cited for an explicit bound proved by `quartetW_le`/`quartetW_nonneg`). The systematic pattern is hypothesis leakage in the long L2300 remark: the sample-datum theorems (`SamplingCompatibility`, `SampleDatumMGF`, `SampleDatumLimit`, `JointSampleLimit`, `LeadingCoeffGaussianMoment`) all carry `xiCoord A = 0` (zero-phase amplitude datum), a sure ℓ¹ bound `‖phaseObs‖ ≤ M₀`, and the temperature constraint `pβM₀² < 2`, which the companion note states carefully but the mirror sentences drop, producing "needs only"/"conditional only on" over-claims. A second pattern is silent specialisation to unit box radii (`b ≡ 1`) in `IsolatedRemainderUniform`, `SecondOrderStochasticOne`, `ZeroNoiseContinuity` while the surrounding prose uses general `b`. The most consequential finding is the pair of dots on the `cor:empirical_expectation` header, which certify the full recursive division expansion when Lean proves a 2D chart-level leading term and a generic quotient lemma; they should be moved into the scope remark. In the note, the "if and only if A>0, B>0" bilocal finiteness claim over-certifies (Lean has sufficiency and the critical/divergent cases, never the A ≤ 0 necessity).
