# Consult #86 — grammar Lean: #85 units 1–6 landed; the regression, and what comes after the resolved-space programme

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
580 modules, axiom-clean). Your #85 programme is landed through unit 6, in your order and with your
design decisions (source amplitudes outside the geometric package; zero-compatible expansions;
positivity at the extremal pair before discarding zeros; certificates supplied, not derived from
`Q_all`):

* CCLXXIII `LeadingTermNegligible` (unit 1): `HasLeadingTerm.add_isLittleO`, `HasExponentialBound`
  (closed under neg/add/sum/const_mul), `isLittleO_powLogScale` (`e^{−κN} = o` of every scale),
  `add_exponential`, `|∫_S g e^{−NK}| ≤ e^{−κN}∫_S|g|` for `K ≥ κ` a.e. on `S`, the compact phase gap,
  `hasExponentialBound_setIntegral_of_isCompact`.
* CCLXXIV `SourceAmplitudeBridge` + CCLXXV `SourceAmplitudeLeadingTerm` (unit 2): `sourcePieceIntegral`
  with an arbitrary source amplitude `G` (measurable, continuous on the compact chart domain) in
  place of `F ∘ φ`; the bridge `exists_sourceVarPieceAtlas_of_chart_data` (amplitude
  `|v||y_tang^h|(p∘φ)G`); the source dominant face (`0 < G` at the foot) and cell positivity;
  `sourceChartIntegral`, its piece decomposition, the negligible divisor-free piece,
  `P.sourceCoeff G lam₀ k₀`, ★ `hasLeadingTerm_sourceChartIntegral(_extremal)` (zero-compatible),
  `sourceCoeff_nonneg/pos`, `sourceChartIntegral_isEquivalent`, and compatibility
  `sourceCoeff_pullback : sourceCoeff (F ∘ Φ) = productCoeffV` by uniqueness of certificates.
* CCLXXVI `SourceDecompositionAssembly` (unit 3): `SourceDecomposition R χ K p Z` (exact finite
  decomposition into the source-weighted one-chart integrals of the charts of a cover `R`, plus
  `rem`), `sourceChartCoeff'`/`sourceDecompCoeff` over the ACTIVE charts (CCLXIX's extremal pair),
  ★★ `hasLeadingTerm_of_sourceDecomposition` (`rem = o(scale)`; `_exponential`),
  `isEquivalent_of_sourceDecomposition`, free energy, and `tendsto_div_of_sourceDecompositions`
  (ratio of two certificates over the same packages → `c₁/c₂`, numerator may vanish).
* CCLXXVII `CompactSourceLocalization` (unit 4, your corrected geometry): `productBox_eq_closedBall`,
  plateau bumps `clamp(3 − 4 dist/ρ)` and `θ_k = b_k / max(1, ∑b)` (`∑θ = 1` on the union of the
  half-balls, no partition-of-unity API), `sourceAmpIntegral φ K a p N = ∫ a |det Dφ| (p∘φ) e^{−N K∘φ}`,
  the structure `SourceLocalization` (finite divisor points, radii, `χ_k = a θ_k ≤ a` supported in
  the open boxes, uniform `ε`, exponentially small `rem`), ★ `IsMonomialChart.exists_sourceLocalization`
  for continuous `a ≥ 0` with compact `tsupport a ⊆ W`; a localisation is a certificate over the box
  cover with the box packages, so `SourceLocalization.hasLeadingTerm/isEquivalent`.
* CCLXXVIII `AEDisjointSourceAssembly` (unit 5): `AEDisjointImages`, `integral_iUnion_eq_sum_of_aeDisjoint`
  (from `integral_iUnion_ae`), `boltzmannIntegral_eq_sum_ofChart`, the certificate
  `sourceDecompositionOfAEDisjoint` (amplitudes `F ∘ Φ_i`, `rem = 0`), ★★
  `boltzmannIntegral_isEquivalent_of_aeDisjoint`, free energy, ★ `tendsto_posteriorExpectation_of_aeDisjoint`
  (`E_N[F] → c_F/c_1`), transfer to a region a.e.-equal to the union of images.
* CCLXXIX `CertifiedResolutionExplicitCoefficient` (unit 6): `sourceDecomp_pair_unique`,
  `sourceDecomp_coeff_unique` (independence from boxes/cutoffs/charts/packages, not the region);
  `targetIntegral_eq_boltzmannIntegral_ofPartialResolution` (the region `N` of hironaka's
  `PartialResolution d K N` is covered a.e. by images lying in `N`), ★★
  `targetIntegral_isEquivalent_ofPartialResolution` (a.e.-disjoint images + supplied product packages
  ⇒ `∫_N F p e^{−nK} ~ c n^{−λ*}(log n)^{k*}`, `c > 0` explicit) with the posterior corollary, and
  `exists_monomialResolution_of_analytic` (what `Q_all` supplies) — the gap named exactly as you put it.

Paper mirror: a "Certified source decompositions" paragraph with 15 dots; the "not yet formalised"
sentence now reads: the production of the certificate for an arbitrary compact chart domain from a
resolution alone (continuous target partitions need not exist, a centred box at a divisor point need
not lie in the chart domain, no common resolved space is exposed); the subleading terms.

## Q1 (unit 7, the blow-up square regression — in progress; sanity-check the plan)
hironaka provides `blowUpChart (B : ι ↪ Fin d) (β : ι)` with `blowUpChart_apply_scaling : φ y (B β) = y (B β)`,
`blowUpChart_apply_ratio (γ ≠ β) : φ y (B γ) = y (B β) * y (B γ)`, `det_fderiv_blowUpChart :
(fderiv ℝ φ y).det = y (B β) ^ (card ι − 1)` (axiom-clean), `contDiff_blowUpChart`,
`blowUpChart_injOn_compl_pivotHyperplane : InjOn φ {x | x (B β) ≠ 0}`, `pivotHyperplane_null`. With
`ι = Fin 2`, `B = refl`, `d = 2`: `φ₀(s,t) = (s, st)`, `φ₁(s,t) = (st, t)`, both on `dom = [−1,1]²`,
`K(a,b) = a² + b²`, `F = 1`, `p = 1`. Plan: (a) `ResolutionChart`s with `E_β = dom ∩ {y_β = 0}`;
(b) the one-chart Var packages: `e = single β 2`, `h = single β 1`, `u = 1 + y_{rev β}²`, `v = 1`,
`T = {x_β = 0, |x_{rev β}| ≤ 1}`, `b = 1`, `IsMonomialChart` by hand (`W = univ`; analyticity of the
polynomial chart via `AnalyticOnNhd.pi`/`.mul`; injectivity from the pivot lemma since
`monomialEval y h = y_β`); (c) images `A_β` with `A₀ ∪ A₁ = [−1,1]²` exactly (case on `|b| ≤ |a|`)
and `A₀ ∩ A₁ ⊆ {a = b} ∪ {a = −b}`, null by `Measure.addHaar_submodule` (kernels of `proj 0 ∓ proj 1`);
(d) per chart: `coverLamV = 1`, `coverDegV = 0`, minimal set `{β}`, base `{z : Fin 1 → ℝ | |z 0| ≤ 1}`,
`scalarPhase = 1 + z₀²`, `pieceAmp = 1`, face integral `∫_{|t|≤1} dt/(1+t²) = π/2`
(`integral_inv_one_add_sq`, `arctan 1 = π/4`; transport `Fin 1 → ℝ` to `ℝ` by
`volume_preserving_funUnique`), so `productCoeffV = 2 · Γ(1)/0! · (1/2) · π/2 = π/2`
(`productCoeffV_extremal_eq_sum_minimal`), `sourceChartCoeff' β = π/2` via `sourceCoeff_pullback`,
both charts tied at `(1,0)`, `aeDisjointCoeff = π`; (e) ★ `∫_{[−1,1]²} e^{−N(a²+b²)} ~ π N^{−1}`
through `targetIntegral_isEquivalent_of_aeDisjoint` — the classical value `(√π N^{−1/2})² = π/N` as a
check. Anything wrong or missing (e.g. the dominant-face hypothesis: the source dominant face of the
stratum `{β}` at cutoff `ε = 1` is the set of feet `z` with `|z₀| ≤ 1` — positive measure; the
`footCondition` is vacuous since `D = {β} = I`)? Is `ε = 1 ≤ b = 1` the cutoff to use, or does the
piece structure at `ε = b` degenerate (the divisor-free piece `sizePiece D 1 ∅ = {|y_β| ≥ 1}` meets
`dom` only on the boundary — fine, but is there a subtlety with `|y_β| < ε` being strict)?

## Q2 (after the programme)
With units 1–6 landed and 7 in progress, rank the next directions (3–5 units each, or say "stop"):
 (A) closing the named gap partially: a whole-chart-domain certificate when the chart domain is
     ITSELF a centred product box around a single divisor point (the box packages already are), or a
     finite a.e.-disjoint union of such boxes ("boundary-compatible product pieces") — i.e. an honest
     class of resolutions for which the certificate is DERIVED: `blowUpResolution` (hironaka's
     package: chart boxes `blowUpChartBox B β ρ`, images covering `[−ρ,ρ]^d`) — are its images a.e.
     disjoint? (For the standard blow-up of the origin in ℝ^d: the images are the wedges
     `{|y_γ| ≤ |y_β| ∀γ}` — a.e. disjoint, yes!) So: `blowUpResolution` gives a DERIVED certificate for
     phases that are monomial in every blow-up chart (e.g. `K = ∑ y_i²`, or more generally any `K`
     whose single blow-up at the origin monomialises it). How valuable is a general theorem
     "one blow-up suffices ⇒ explicit coefficient for the box `[−ρ,ρ]^d`"?
 (B) the small-ball region: the pair is intrinsic (CCIX) but the coefficient is region-dependent; is
     there an honest statement about the coefficient of `closedBall w r` for small `r` (e.g. for
     `K = ∑ y_i^{2k_i}`-type phases where the ball is handled directly)? Or is "coefficient of the
     region N" the right final form (the paper's Theorem is over a compact region / the whole
     parameter space with a prior)?
 (C) the statistical transfer of the identified coefficient to the empirical posterior (Astra #71
     (iv)): the population theorem gives `E_n[φ] → c_φ/c_1`; the paper's expectation theorem is for
     `E_{w|D_n}`. What is the honest minimal statement (a.s. or in probability) that the library could
     prove given its existing empirical/Gaussian companion material (`averaging_dataset.tex`)?
 (D) the subleading terms (still declared out of scope) — is there a first honest step (the next
     pole: `Z_N = c N^{−λ}(log N)^k + c' N^{−λ}(log N)^{k−1} + o(·)` for the all-minimal one-chart
     case, where the box kernel's Mellin expansion is explicit)?
 (E) anything in the paper's §3–§4 you now consider under-served given 951 mirror dots.
Please rank and give the first unit of the top choice with its statement.

## Q3 (Mathlib/Lean specifics for Q1)
Name (or flag as uncertain) the lemmas for: transporting a set integral over `Fin 1 → ℝ` to `ℝ`
(`MeasureTheory.volume_preserving_funUnique`, `MeasurePreserving.setIntegral_preimage_emb`?), the
interval integral of `(1+x²)⁻¹` (`integral_inv_one_add_sq`), `Real.arctan_one`, `Measure.addHaar_submodule`
for `volume` on `Fin 2 → ℝ` (is `volume` registered as `IsAddHaarMeasure` on pi types?), the
analyticity of coordinate projections (`ContinuousLinearMap.analyticOnNhd (proj j)`?), and
`Finsupp.support_single_ne_zero`.
