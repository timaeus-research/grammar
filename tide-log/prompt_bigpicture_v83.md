# Consult #83 — grammar Lean: #82 programme complete (prelude, 4A–4C, B-small, B-full, Q3 compatibility, R4 scope); planning R3 and beyond

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
564 modules, axiom-clean). Your #82 programme is landed in full, in your order:

* CCLVII `VariableUnitCellRegressions` (B-small): hand-built one-point-base cells;
  `(1+y²)x²y⁴ ~ 2Γ(1/4)N^{−1/4}`; `(1+x²+y²)x²y⁴ ~ Γ(1/4)·I·N^{−1/4}`, `I = ∫₀¹x^{−1/2}(1+x²)^{−1/4}dx > 0`
  (≈ 1.9234, numerically confirmed: `Z(10⁸)·10² ≈ 6.92 → Γ(1/4)I ≈ 6.97`, not `2Γ(1/4) ≈ 7.25`);
  `x²y⁴z⁴ ~ Γ(1/4)N^{−1/4}log N` — all three constants as you predicted.
* CCLVIII `LeadingAtlas` (prelude): `LeadingCell`, `FiniteLeadingAtlas` (tied, `hasLeadingTerm_of_extremal`),
  `FiniteVarUnitAtlas`, conversions, generic `hasLeadingTerm_boltzmannIntegral_of_leadingAtlases`
  (`scalarAtlasPieceCoeff'_eq_leading` by `rfl`), extension independence `VarUnitCell.withData_*`.
* CCLIX `VariableUnitPieceAtlas` (4A): `varPhase = u(Ψ(z,n))·tangentialMonomial(z)`, `phase_varNormalForm`
  (no `hind`), positivity on the closed normal ball by the IVT along the connected ball (no `u > 0`
  on `W`, no connectedness of `W` — your Q2(ii) argument, IVT instead of density), `varPieceCell`,
  `varPieceAtlas`, `exists_varPieceAtlas_of_chart_data` (Tietze of `uncurry varPhase` and `pieceAmp`
  from base × closed ball).
* CCLX `ProductChartVar` (4B): `ProductMonomialChartVar` (fields minus `unit_indep`), `toVar`,
  exponent bookkeeping agreeing by `rfl`, `VarUnitCell.coeff_nonneg`, **the frozen cell**
  (`VarUnitCell.frozen`: `q z := u z 0`; `coeff_eq_frozen_of_all_minimal`, so positivity reduces to CCXL
  exactly — your `A·u_face^{−λ}` reduction became an equality), `IsVarPieceAtlasData`, `pieceAtlasV`,
  `productCoeffV`, signed `hasLeadingTerm_boltzmannIntegral_of_productChartsV(_extremal)`,
  `productCoeffV_pos`, ★★ `boltzmannIntegral_isEquivalent_of_productChartsV_extremal`.
* CCLXI `ProductChartVarPosterior` (4C): `normaliserCoeffV`, ★ `tendsto_posteriorExpectation_of_productChartsV`,
  tied strata (`tied_iffV`, `productCoeffV_extremal_eq_sum_tied`), all-minimal tied sum through the frozen cell
  (`varPieceAtlas_sum_tied`, `tiedSum_of_all_minimalV` — literally the scalar formula with
  `scalarPhase = u(Ψ(z,0))·tangentialMonomial`), `productCoeffV_extremal_eq_sum_minimal`, residual tied sum
  `varPieceAtlas_sum_tied_residual` (`2^{|J|}` × residual sign classes, CCLVI face integrals).
* CCLXII `VariableUnitSquareExample` (B-full): `(1+x²+y²)x²y²` on `[−1,1]²` end to end through the new
  package (`ProductMonomialChartVar` one-chart cover; both coordinates normal for the tied stratum, so the
  old package does not apply): ★ `~ √π N^{−1/2} log N`.
* CCLXIII `ProductChartVarCompat` (Q3): under `unit_indep` the two classically chosen atlases have equal tied
  sums ⇒ ★ `productCoeffV (toVar Ps) = productCoeffD Ps` at every pair, `normaliserCoeffV_toVar_eq`;
  with `coverLamV_toVar` etc. the new theorems restrict exactly to CCXLV/CCXLVII. HEADLINES CCLXIII carries
  your R4 scope statement verbatim in substance.

Mirror: the normal-dependent-unit paragraph now carries dots for CCLVIII–CCLXIII; the scope remark cites
the general-unit theorems; the not-yet-formalised list reads "regular supplied cover weights depending on
all coordinates; the subleading terms".

## The weight architecture (for R3)
* `ResolutionCover d ι := { chart : ι → ResolutionChart d }`; `R.image i := φ_i '' dom_i`;
  `R.weight i := coverWeight R.image i` with `coverWeight A i x = 1_{A i}(x) / ∑_j 1_{A j}(x)` — the
  COUNTING partition of unity on the union of chart images (measurable, `∑_i = 1` on the union, not
  continuous). `TubeWeight d := { w, measurable, nonneg, bound, le_bound }` is the prior/observable weight.
* `boltzmannChartDensity i N K p y := 1_{dom_i}(y) · jac_i(y) · ρ_i(Φ_i y) · e^{−N K(Φ_i y)} · p(Φ_i y)`
  with `ρ_i = R.weight i`; `pieceIntegral D ε i I F K p N := ∫_{sizePiece (D i) ε I} density · F(φ_i y)`;
  `boltzmannIntegral F K p N := R.coverIntegral (F·p) (−N K)` (the transport theorem
  `∫_{⋃ images} F p e^{−NK} = ∑_i ∫_{dom_i} jac · ρ_i∘Φ · … ` — CCXXIV), `boltzmannIntegral_eq_sum_pieces`.
* The piece bridge: `AdaptedProductDensity τ w piece := { base, normalBox, beta, amp, density_ae :
  1_piece w (Ψ q) =ᵐ 1_base(q.1) β(q.1) · 1_normalBox(q.2) amp(q.1, q.2) }`;
  `adaptedProductDensity_of_fibreConstant`: if a.e. on the piece the allocation factor
  `1_{dom_i}·(ρ_i∘Φ_i)` is a function `β(foot)` of the foot, then base = foot condition, box = ε-ball,
  `beta z = β(Ψ(z,0))`, `amp z n = jac(Ψ(z,n))·p(Φ Ψ(z,n))`; `compactFibreConstantDensity` intersects the
  base with the tangential carrier of `dom`; `chartPieceDensity` restricts the base to the fibres over a
  closed foot set `T'` with `β = 1_{T'}·ρT` (hypotheses `hdom : y ∈ dom ↔ foot y ∈ T'` on the piece,
  `hρ : ρ_i(Φ y) = ρT(foot y)` on the piece ∩ dom). `pieceAmp = |v(Ψ)|·|tangential Jacobian monomial|·
  p(φΨ)·F(φΨ)` is the continuous amplitude (Tietze-extended); `hamp : Ad.amp z n · F(φΨ) = A' z n ∏|n_a|^{h_a}`.
  The product package supplies `hρ` through `weight_eq : ρ_i(Φ y) = r(zeroOn J y)` (factoring through the
  inactive coordinates) — R3 is exactly the removal of this.
* `R.weight` is used in 12 modules (transport, tube densities, piece decomposition, the assembly).

## Questions

**Q1 (R3 design).** Supplied regular cover weights depending on ALL coordinates. Options:
 (A) Generalise the cover: `WeightedCover := { chart, ρ : ι → (Fin d → ℝ) → ℝ, ρ_meas, ρ_nonneg, sum_ρ = 1
     on ⋃ images }` (or `ρ` supplied as functions on the chart domains `ρ_i∘Φ_i`), re-derive the transport
     theorem and `boltzmannIntegral_eq_sum_pieces` for it (the counting cover is the instance
     `ρ := coverWeight`), then absorb `ρ_i∘Φ_i` into the AMPLITUDE of the adapted density
     (`amp z n := ρ_i(Φ Ψ(z,n))·jac·p(ΦΨ)`, `beta := 1_{T'}(foot)`), requiring `ρ_i∘Φ_i` continuous on
     `W` (it becomes a factor of `pieceAmp`; positivity of the dominant face needs `ρ_i(Φ Ψ(z,0)) > 0`).
     Cost: the transport/decomposition layer is re-derived generically (how much of CCXXIV–CCXXX depends
     on `coverWeight` specifically vs an abstract measurable `ρ` with `∑ = 1`?); the product package
     loses `r, r_meas, Cr, r_bound, weight_eq` and gains `ρ_cont`.
 (B) Keep the counting cover but generalise the PRIOR: since `p` already enters the amplitude as
     `p(Φ Ψ(z,n))`, a supplied regular partition of unity `{ψ_i}` can be absorbed into `p` chart by chart —
     `Z_N[F] = ∑_i ∫ F p ψ_i e^{−NK}` where each `∫ F (p ψ_i) e^{−NK}` over the image of chart `i` is
     a one-chart Boltzmann integral with prior `p ψ_i` (a `TubeWeight` if `ψ_i` measurable, nonneg,
     bounded; continuity of `ψ_i∘φ_i` on `W` gives the continuous amplitude). Then the leading term of
     `Z_N[F]` is the sum over `i` of one-chart leading terms (already available: `ofChart`, CCXLIX; the
     product package for a one-chart cover has `r = 1` automatically), summed by `hasLeadingTerm_sum_of_extremal`.
     No change to the cover structure, no transport re-derivation; the "cover weight factoring through the
     inactive coordinates" hypothesis disappears because the counting weight of a one-chart cover is 1.
     Cost: a new top-level statement `Z_N[F] = ∑_i Z^{(i)}_N[F ψ_i]` (needs `∑ ψ_i = 1` on the union and
     measurability), the extremal pair over charts computed from the per-chart pairs (the existing
     cover-level `coverLam/coverDeg` bookkeeping applies with `Ps i` one-chart packages), and positivity:
     the dominant face of the chart attaining the pair needs `ψ_{i₀} > 0` at the foot.
 (C) Something else you prefer.
 My inclination: (B) — it is a theorem about DECOMPOSING the integral by a partition of unity and then
 applying the landed one-chart theorem, so it is cheap and matches the paper's "choose a partition of
 unity subordinate to the cover". Do you agree, and what exactly should the headline statement be
 (hypotheses on `ψ_i`: continuous on `φ_i(dom_i)`? on an open neighbourhood? nonnegative, bounded,
 `∑_i ψ_i = 1` on `⋃ φ_i(dom_i)`; supports?) and what are the traps (a chart image is a compact set, the
 partition of unity is naturally continuous on an open neighbourhood of the union; `ψ_i` may be positive
 outside `φ_i(dom_i)`, so `F p ψ_i` must be restricted to the image of chart `i` — the decomposition needs
 `supp ψ_i ⊆ φ_i(dom_i)`, or else the sum over `i` of `∫_{φ_i(dom_i)} F p ψ_i e^{−NK}` is NOT `Z_N[F]`)?
 Please state the decomposition identity precisely.

**Q2 (the residual end-to-end regression).** CCLVII did `(1+x²+y²)x²y⁴` on a hand-built cell; end to end
through the cover the residual stratum `{0,1}` is tied but NOT all-minimal, so `productCoeffV_extremal_eq_sum_minimal`
does not apply and one needs the residual tied sum in chart data (CCLI did the scalar analogue for `x²y⁴`
in ~700 lines: `tiedSum_univ_of_inner`, `productCoeffD_eq_of_inner`). Is this worth doing for the variable
package (it would exhibit `Γ(1/4)·I` end to end), or is CCLVII + CCLXII enough evidence? If worth doing,
should the generic layer first provide a chart-data residual formula (`IsVarPieceAtlasData` ⇒ tied sum =
`2^{|J|} ∑_τ` reflected face integrals of `pieceAmp · varPhase^{−λ}` on the face), analogous to
`tiedSum_of_all_minimalV`, so that examples only compute the face integral?

**Q3 (Θ and the subleading remainder).** You said the Θ statement is a cheap corollary once the positive-
coefficient equivalence is available: is there a specific Θ/two-sided-bound statement for the variable
package worth adding now (e.g. `∃ c₁ c₂ > 0, c₁ ≤ Z_N/(N^{−λ*}log^{k*}N) ≤ c₂` eventually, or the
free-energy form `−log Z_N = λ* log N − k* log log N + O(1)`)? The library has `CCVI`/`CCIX-c` free-energy
forms for the small-ball pair; a version for the cover theorem would connect the two programmes.

**Q4 (priority).** Rank for the next 3–5 units, given "new theorems first": (i) R3 via your preferred
design; (ii) the residual end-to-end regression; (iii) Θ/free-energy corollaries for the cover theorems;
(iv) the one-chart `unit_indep`-free posterior example with a genuinely normal-dependent unit and a
nontrivial observable (e.g. `E_N[x²]` for `K=(1+x²+y²)x²y²`: the observable amplitude at the face is
`x² = 0`, so the limit is `0` — dominated — or `E_N[1+x²+y²] → 1`: trivial; maybe `F = e^{x}`,
`E_N[e^x] → 1`); (v) anything else in the paper's §3–§4 you now consider under-served (the mirror has 922
dots; remaining explicit gaps: the localisation bridge from a resolution to the product package, and the
subleading expansion).
