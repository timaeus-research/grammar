# Plan: the coordinate-free expansion theorem (consults #91–#92)

Goal set by the user (2026-09-12): the final statement of the asymptotic expansion of the partition
function with insertion must involve **no coordinates** — only conormal derivatives, the
stratification of the exceptional divisor, moment tensors and stratum densities. Charts may appear
in hypotheses (a certificate that the geometry is resolved) and in proofs, never in the formula.

## 1. The target statement

For a resolved space `U` with a proper map `π : U → W`, closed divisor components `E_i` with orders
`(k_i, h_i)`, strata `S_I = {u | ∀ i, u ∈ E_i ↔ i ∈ I}`, normal bundles `N S_I` with the conormal
splitting `N^*S_I ≅ ⊕_{i∈I} L_i`, a chosen tubular map `Φ_I` (germ at the zero section), an
`n`-independent stratum density `ν_I`, and an adapted partition of unity:

```
∫_W φ ϕ e^{−nK} dw
  = Σ_{(α,j) : α ≤ A} n^{−α} (log n)^j · Σ_I Σ'_{r≥0} (1/r!) ∫_{S_I} ⟨ D^r_⊥(φ∘π), B_{I,r,α,j} ⟩ dν_I
    + o(n^{−A})
```

* `D^r_⊥(φ∘π)(s) = D^r((φ∘π)∘Φ_{I,s})(0)`: the UNNORMALISED normal jet, a symmetric `r`-form on
  the normal space `N_s S_I` (`normalDifferential`, CCXCVII; `r! • normalTaylorForm = D^r_⊥`).
* `B_{I,r,α,j}(s) ∈ Sym^r N_s S_I` (represented as the dual of the symmetric `r`-forms): the
  coefficient of `n^{−α}(log n)^j` in the asymptotic expansion of the exact normal fibre moment
  `M̂_{I,r}(n)(s)(A) = ∫ A(v,…,v) dη_{I,s,n}(v)`; exact moments are NOT finite power–log sums, so
  `exactMoment`, `momentCoeff`, `momentCutoff` are distinct objects.
* `ν_I`: a measure on `S_I`, the paper's `τ_*|μ_I|`; the split (base density, fibre density) is a
  choice, `(ν, M) ~ (fν, f⁻¹M)`.
* The remainder convention: all log terms at exponent `A` are included, then `o(n^{−A})`.
* `Σ' r` is genuinely infinite at tied crossings (`K = xy`: `∫∫ x^R e^{−nxy} ~ ε^R/R · n^{−1}` for
  every `R`); the sum is proved absolutely convergent from analytic normal Taylor bounds on `φ`.
  A `C^∞` finite-jet version is false.

Leading corollary: `n^{λ}/(log n)^{m−1} ∫_W φ ϕ e^{−nK} → ∫_W φ dμ_lead`,
`μ_lead = Σ_{I tied} π_*( Γ(λ)/(m−1)! · a_I · ν_I |_{c₀} )`, and `μ_lead` equals the leading measure
of CCXC–CCXCIII (a separate equality theorem).

Canonical: the total coefficient functionals, the total leading measure, the expansion.
Chosen: `Φ_I`, `ρ_I`, the per-stratum split, the base/fibre density split, individual `B`'s.

## 2. Where the library stands

* Chart level: the full Taylor tree on unit boxes with exact normal form (`thm_TaylorTree_taylor`),
  canonical coefficient maps, cutoff expansions with quantitative remainders.
* Assembled, conditional on exact analytic core certificates:
  `cutoffExpansion_of_hasAnalyticCoreDecomposition` with coefficients `Σ_I ∫_{K_I} C_{μ,j}(x v) dν`.
* Resolved-space contraction identity `coverIntegral_eq_sum_pieceContraction` (exact, no asymptotics).
* Normal machinery relative to a chosen normal family: `NormalTaylorForm`, `IsGlobalNormalSection`,
  `conormalSplitting`, `LabelledNormalBundle`, `TubularFibreIntegration`, `SymmetricWeights`.
* Global leading term: the leading measure programme CCXC–CCXCVI (canonical finite measure on `W`,
  concentration on the zero set, cube regression `π^{d/2} δ₀`, unconditional Θ-exponent over compact
  and bounded open regions).
* Unconditional local: `IsMonomialChart.local_leading_term`, `exponent_of_analytic`,
  `laplace_pair_eq_resolution_pair`.

## 3. The interface gap

hironaka exposes `PartialResolution`: finitely many compact chart domains with analytic maps into
`W`, images covering a compact set a.e. with finite multiplicity, `IsMonomialChart` per chart. It has
no common resolved space, no `π`, no transition maps, no global divisor components, no strata. So
the theorem is CONDITIONAL on certified resolved geometry; making it unconditional needs hironaka to
expose `U`, a proper analytic `π`, an atlas with overlaps, labelled components `E_i` and their
incidence — a separate upstream programme (Astra #92 §5).

## 4. The structures (charts only in the last one)

1. `ResolvedGeometry` — `U` (topological, later a smooth manifold embedded in a Euclidean `A`),
   `π : U → W` continuous and proper, `Component` finite, `E i` closed, orders `k i, h i`; derived:
   `stratumSet I`, `Stratum I`, incidence set of a point, disjointness/cover identities,
   `stratumLam I = min_{i∈I} (h_i+1)/(2k_i)`, `stratumMult`.
2. `ResolvedNormalData` — normal fibres `N I s ⊆ A` (representing `T_sU/T_sS_I`), labelled conormal
   lines and the fibrewise splitting, tubular germs `Φ_I s : N I s → U` with zero-section and
   retraction identities; `normalDifferential` of `φ∘π`; bridge to `IsGlobalNormalSection`.
3. `ResolvedIntegrationData` — resolved measure `μ_U` with `Measure.map π μ_U = μ_W` on the region,
   stratum base measures `ν I`, measurable families of normal fibre measures, the adapted partition
   `ρ_I` (germwise normal constancy, subordinate supports, quantitative integrability), away-piece
   with a positive phase gap; the tubular disintegration identity.
4. `MonomialCompatibilityCertificate` — an actual atlas of `U`, divisor incidence (labelled
   coordinate hyperplanes), normal crossings, monomial phase and density, normal and density
   compatibility, localisation compatibility; separately `AnalyticExpansionAdmissible φ` (Taylor
   radii, majorants, summable bounds). No conclusion of the theorem may be a field.

## 5. Units (as executed; gates in bold)

| # | Unit | Content | Status |
|---|---|---|---|
| 1 | `NormalDifferentialConvention` | `D^r_⊥ := rawNormalJet`, `r! • T_r = D^r_⊥`, linearity | CCXCVII |
| 2 | `ResolvedGeometry` | `U`, proper `π`, components `E i`, strata `S_I`, incidence, `stratumLam`, `IsResolutionOf` | CCXCVIII |
| 3 | `ResolvedNormalData` | normal spaces, labelled conormal differentials + splitting, tubular germs, `normalDifferential (φ∘π)`, `MomentTensor`, `HasCoordFreeExpansion` | CCXCIX |
| 4 | `ResolvedMomentRepresentation` | `ResolvedCertificate` = the library's `AdaptedStrataData` (conditional geometric main theorem) on compact stratum pieces + frames `ℝ^{n+1} ≃ N_s`; exact moment tensors; ★★★ `∫_W φϕe^{−NK} = Σ_I ∫_{S_I} Σ'_r (1/r!)⟨D^r_⊥(φ∘π), M̂_{I,r}(N)⟩ dν_I + tail`; `cutoffExpansion_globalLaplace` | CCC |
| 5 | `ZeroFluctSpectralKernel` | the canonical box coefficients are ℓ¹ kernel pairings of the amplitude family (`monoKernel`, `boxSpectralKernel`, uniform bounds, `AbsSummableAt.conv`) | CCCI |
| 6 | `ChartCoefficientTensors` | `shiftedKernel`, `chartMomentCoeff` (coefficient tensor of the exact fibre moment tensor), `jetFamily`, ★★ termwise identity `boxCoeff 0 (cc ⋆ jetFamily F) μ j = Σ'_r (1/r!)⟨D^rF(0), B_r⟩`; `MomentTensor.pushFrame` | CCCII |
| 7 | `ResolvedCoordFreeExpansion` | `CoefficientCertificate`; chart tensors on the strata via frames; per-point identity; `stratumMeasure` (pushforward sums), `field` (Radon–Nikodym-weighted tensor fields, no disjointness); ★★ `expansionCoefficient_eq_gCoeff`; ★★★ `hasCoordFreeExpansion` — **THE TARGET THEOREM**, conditional on the two certificates | CCCIII |
| 8 | certificate instances | `OneDimResolvedGeometry` (CCCV: `ℝ¹`, `π = id`, `{x = 0}`, normal data, frames), `OneDimPolynomialSeries` (CCCVI: `jetFamily_poly`), ★★ `OneDimCoordFreeInstance` (CCCVII: both certificates for `∫_0^ρ P(x)e^{−nx²}dx`, `hasCoordFreeExpansion_poly` with spectrum `½ℕ`); `JetFamilyOfSeries` (CCCIX: `jetFamily = monoFamily p` in every dimension, `CoefficientCertificate.ofSeries`) | CCCV–CCCVII, CCCIX |
| 9 | `ProjectorBlowup*` | `U = {(x,P) : P symmetric idempotent of trace 1, Px = x}` as a `ResolvedGeometry` with certificate (Astra #93: after the certificate API stabilises; 6–12 modules) | planned |
| 10 | `CoordFreeLeadingTerm` | ★★ `hasLeadingTerm_expansionCoefficient` (first admissible index with vanishing predecessors ⇒ leading term), `exists_first_nonzero_expansionCoefficient`, ★★ `expansionCoefficient_eq_integral_leadingMeasure` (bridge to the CCXC leading measure for bounded continuous `φϕ`) | CCCX |
| 11 | `CutoffExpansionUniqueness` | ★★★ `CutoffExpansion.coeff_unique`/`coeff_eq_of_lattices`; ★★★ `expansionCoefficient_eq_of_certificates` — two certificate pairs for the same original integral give the same coordinate-free coefficients at every index (canonicity of the assembled scalar coefficients) | CCCVIII |
| 12 | examples and regressions | CCCXI `PolynomialTaylorFamily` (`jetFamily_polyD`, every dimension); ★★ CCCXII `OneDimExplicitCoefficients` (`expansionCoefficient_oneDim = Γ((m+1)/2)/2 · f_m`; `√π/2`, `a√π/4`; `hasLeadingTerm_quad`); CCCXIII `CoordinateResolvedGeometry` (`ℝ^d` resolving `∏ u_i^{2k_i}`); ★★ CCCXIV `TiedCrossingInstance` (`∫_{[0,b]²} P e^{−nx²y²}`, spectrum ½ℕ, log degree ≤ 1); ★★ CCCXV `TiedCrossingLogCoefficient` (`n^{−1/2} log n` coefficient `√π/4 · P(0)`, `hasLeadingTerm_log_tied`) | CCCXI–CCCXV |

Gates 9 and 10 of the original plan (integrable tensor coefficients; summable interchange over `r`)
were passed by design: the coefficient tensors are constructed explicitly from the chart kernels
(no finite-part regularisation is needed for the CERTIFIED presentations, whose densities are
analytic on the box), and the normal-order series is summed pointwise inside the stratum integral,
so no interchange with the integral is required. `expansionCoefficient` was accordingly redefined as
`Σ_I ∫_{S_I} Σ'_r (1/r!)⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩ dν_I`.

## 5a. Status (2026-09-12, after consults #93–#94; main `efb8929`, 616 modules) — PROGRAMME CLOSED AT ASTRA'S RECOMMENDED STOPPING POINT

★★★ `hasCoordFreeExpansion`/`hasCoordFreeExpansion_le` (CCCIII–CCCIV): the coordinate-free expansion of
`∫_W φ ϕ e^{−nK}` conditional on `ResolvedCertificate` + `CoefficientCertificate`, normal-order series summed
pointwise inside the stratum integrals (convergent, integrable), truncation to exponents `≤ A`. Audits (#93,
#94): a certified coordinate-free REPRESENTATION, not an intrinsic final theorem; docstrings/headline state the
non-claims (fields chosen, `cc` a factorisation family, unnormalised integral, no certificate existence from
the hironaka interface). Landed on top: ★★★ canonicity of the assembled scalar coefficients across
certificates (CCCVIII); `jetFamily = monoFamily p` and `CoefficientCertificate.ofSeries` (CCCIX); the leading
term and the bridge to the CCXC leading measure (CCCX); instances with closed-form coefficients — the
one-dimensional `∫_0^ρ P e^{−nx²}` (CCCV–VII, CCCXII: `Γ((m+1)/2)/2 · f_m`) and the tied crossing
`∫_{[0,b]²} P e^{−nx²y²}` (CCCXIII–XV: `√π/4 · P(0)` at `n^{−1/2} log n`). Astra #94: further work should buy a
named example, a functional-level statement, or a new existence/transport interface; candidates (deferred)
are I (core + phase-gap certificate for curved sublevel sets), J (observable-independent coefficient
functional on an observable class), E (projector blow-up model), G (two-sided interval).

## 5b. Phase 2 — fundamentals of the certified resolved geometry (user request 2026-09-12; consult #95)

Goal: PRODUCE certificates from geometry and series data rather than assume them, with cores + phase-gap
tails as the primary interface, then genuine tubular/divisor compatibility. Astra #95
(`tide-log/gpt6_bigpicture_v95.md`): keep the structures backward-compatible; add separate compatibility
structures later (normal quotient identification, labelled defining equations, tubular map from the total
normal bundle, `incident_eq`, monomial-phase unit, full-dimensional density change of variables, chart
`label`/`k_eq`/`h_eq`/`frame_conormal`); producer sequence rectangular series → parameterised series →
normal-unit normalisation → analytic-normal collar decomposition → general compact-box producer.

| unit | module | status |
|---|---|---|
| F1 core moment representation + adapters | `CoreNormalMomentRepresentation` (CCCXVI) | done |
| F1' refactor `ResolvedCertificate` onto `cores : AnalyticCoreDecomposition` | `ResolvedMomentRepresentation` (7a8ef2d) | done |
| F2 weighted-ℓ¹ families are analytic; Taylor family = coefficient family | `AnalyticSeriesFamily` (CCCXVII) | done |
| F3 rectangular series producer (★★★ `SeriesBox.hasCoordFreeExpansion_box`, no certificate hypotheses) | `CoordinateBoxCoreCertificate` (CCCXVIII) | done |
| F4 parameterised series datum, continuous in the ℓ¹ data topology | `ParameterisedSeriesDatum` (CCCXIX) | done |
| F5 normal-unit normalisation: fibrewise diagonal transport + the normalised box core at a coordinate stratum | `DiagonalBoxTransport` (CCCXX), `NormalisedBoxCore` (CCCXXI) | done |
| F6 water-filling collar (consult #96): compact bases in the exact strata, common side `b_I`, `β = 1`; covering + disjointness off thresholds; exact decomposition `μ = Σ μ|_{C_I} + tail`, gap `δ` | `WaterFillingCollar` (CCCXXII), `CollarDecomposition` (CCCXXIII) | done |
| F7 general compact-box producer from local normal series (★★★ `WaterFilling.hasCoordFreeExpansion_collar`, all nonempty coordinate strata) | `CoordinateBoxCertificate` (CCCXXIV) | done |
| F7′ public inputs: original-variable closed-face series adapter (`OriginalFaceSeries.toFaceSeries`, ★★★ `hasCoordFreeExpansion_collar_of_face`) and box-local nonnegativity (`posPart`, ★★★ `hasCoordFreeExpansion_collar_of_nonneg_on`); log degree `commonD = d − 1` | `CoordinateBoxInputs` (CCCXXV), CCCXXIV addendum | done |
| F8 coordinate normal compatibility (consult #97 §2): diagonal conormal frames with scale `λ_i(s)`, tubular identity, constructive consumer `produceCore_of_coordinateCompat`, fixed-germ jets (★★ `normalJet_stratumCore_eq_normalDifferential`: chart jets = coordinate-free normal differentials along the frame) | `CoordinateNormalCompatibility` (CCCXXVI) | done |
| F9 analytic-neighbourhood → uniform face-series bridge (5b): complex neighbourhood + Cauchy estimates with radius shrink | — | phase 3 (consult #98) |

Status: main `7e5cc68`, 627 modules; consult #97's stopping gate for phase 2 MET (original-face input produces the collar-base series; coordinate conormals evaluate the diagonal frames with scale `λ_i(s)`; tubular-frame series construct a core without assuming transport or the phase normal form; fibre jets identified with the fixed normal germ through the frame; all instantiated on the water-filling certificate). PHASE 2 CLOSED. Mirror pin `7e5cc68`.

## 5c. Phase 3 — the complex analytic-neighbourhood bridge (consult #98, 2026-09-12)

Goal: from holomorphic extensions of the prior and the observable on a complex neighbourhood of the
embedded compact box, agreeing with them on its real slice (`HolomorphicBoxExtension`), produce the
closed-face normal series `OriginalFaceSeries` at a COMMON radius `ρ`, then choose the collar level
(CCCXXVII) and feed CCCXXV. Interfaces stay unchanged (per-face `ρ` kept downstream). Box-only agreement
gives a different theorem (about chosen extensions) and is optional; complexification from real
analyticity is NOT part of this phase.

| unit | module | content | status |
|---|---|---|---|
| P0 | `CollarDeltaSelection` (CCCXXVII) | small-level selection `exists_delta`; `hasCoordFreeExpansion_collar_of_face_exists` | done |
| P1 | `AnalyticUniformSeries` (CCCXXVIII) | radius-parametric Cauchy → `UniformSeriesFamily X m ρ` for `0 < ρ < r < R` (`polyRealCoeff m r`, majorant `M r^{-|γ|}`, weighted geometric summability, reconstruction `evalF = Re F` on the real ball of radius `r`) | done |
| P2 | `ComplexNormalInsertion` (CCCXXIX) | `complexify`, insertion CLM `L_I : ℂ^m →L ℂ^d`, `‖L_I z‖ ≤ ‖z‖`, compatibility with `originalNormalMap`, `isCompact_faceSet` | done |
| P3 | `HolomorphicBoxBuffer` (CCCXXX) | `HolomorphicBoxExtension` packet; uniform buffer `∃ R > 0, ∀ w ∈ W, ∀ z, ‖z‖ ≤ R → complexify w + z ∈ Ω` (closed thickening), compact tube, uniform bounds | done |
| P4 | `HolomorphicOriginalFaceSeries` (CCCXXXI) | recentred family `G s z = H(complexify s + L_I z)`; containment, holomorphicity, joint continuity, bounds; common-radius `OriginalFaceSeries` producer (`exists_originalFaceSeries_of_holomorphicBoxExtension`) | done |
| P5 | `AnalyticCoordinateBoxExpansion` (CCCXXXII) | composition: holomorphic box extension ⇒ coordinate-free expansion for some collar level (★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension`, `_nonneg_on`); real-neighbourhood wrapper `ofRealNhd` | done |

| H-A | `ExpansionCongruence` (CCCXXXIII) | the expansion depends on `(ϕ,φ)` only through `∫_W` and the `ν_I`-a.e. germs of `φ` (`normalDifferential_congr`, `expansionCoefficient_congr`, ★ `HasCoordFreeExpansion.congr`); stratum measures of a certificate live on its bases (`ae_stratumMeasure`, `ae_stratumMeasure_mem_box`) | done |
| H1–H3 | `LocalAnalyticInputs` (CCCXXXIV) | real domain, measurable representatives `1_U·Re H∘complexify`, `toRep` packet, boundedness and weighted integrability on the box; ★★★ `hasCoordFreeExpansion_of_holomorphicBoxExtension_local` (hypotheses: packet, `0<d`, `0<a`, prior `≥ 0` on the box) with named `producedCertificate`/`producedCoeffCertificate` | done |
| gate 5 | `PolynomialBoxInstance` (CCCXXXV) | polynomial packets `ofPolynomials`, `flatPolynomial`; ★★ `hasCoordFreeExpansion_polynomial`, ★★ `hasCoordFreeExpansion_flat_polynomial`; `▸` casts in certificate arguments replaced by the named `integrable_posPart` (kernel timeout otherwise) | done |

Status: main `f8df720`, 636 modules; phase 3 and the hygiene phase (consult #99) CLOSED — the public coordinate-model theorem assumes only the holomorphic packet near the box, `0<d`, `0<a` and nonnegativity of the prior on the box. Next: phase G (signed coordinates `[−a,a]^d`, consult #100), then a discharged geometric instance (E).

## 5d. Phase G — the signed box `[−a,a]^d` (consult #100; CCCXXXVI–CCCXLI, main 64696c5, 642 modules)

Design (#100): reflection cover `[−a,a]^d = ⋃_σ R_σ [0,a]^d`; transport EXPANSIONS (not certificates) along
`R_σ`; assemble with summed stratum measures and Radon–Nikodym-weighted fields (reflected bases with the
same off-`I` signs but different normal signs live at the SAME base points, so full-sign piecewise gluing
fails and the fields must be averaged in one fibre).

| Unit | Module | Content | Status |
|---|---|---|---|
| G1 | `SignedBoxPackets` (CCCXXXVI) | signs, reflections, orthant pieces, signed packet + pullbacks, common collar level, at-level local theorem | done |
| G2 | `OrthantDecomposition` (CCCXXXVII) | a.e. unique orthant; `∫_{[−a,a]^d} = ∑_σ ∫_{orthant σ}`; Laplace decomposition for even phases | done |
| G3 | `NormalReflectionTransport` (CCCXXXVIII) | `reflNormal : N_I ≃L N_I`, `reflStratum`, `refl_Φ`, unconditional jet identity, `reflField`, `reflMeasure`, ★★ `hasCoordFreeExpansion_refl` | done |
| G5 | `CertificateSeriesRegularity` (CCCXXXIX) | field pairing depends only on germs at the bases; summability everywhere; integrability | done |
| G4 | `ExpansionAssembly` (CCCXL) | `sumMeasure`, `rnWeight`, `glueField`, ★ `expansionCoefficient_glue`, ★★ `HasCoordFreeExpansion.sum` | done |
| G6 | `SignedBoxExpansion` (CCCXLI) | ★★★ `hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local`; `signedStratumMeasure = ∑_σ (R_σ)_* ν_σ`, `signedMomentField`, specs (finite, support, coefficient sum), spectrum normalisation `coordCommonQ k`, polynomial instance | done |

| G7 | `SignedBoxRegression` (CCCXLII) | reflection-sensitive checks: transported evaluation tensors pick up the sign product; deepest stratum = plain sum of piece measures; synthetic `d = 1` assembly: odd observable cancels (`+1 − 1 = 0`), order zero gives `2` | done |

Status: PHASE G CLOSED (consult #101 audit passed; gate item 7 met by G7). Main 94bd4be, 643 modules. Next (consult #101 §B): E0 obligation table for the projector blow-up chart, then a Jacobian-weighted producer (E1–E5). Not included: Jacobian orders `h ≠ 0`; nonconstant analytic unit; general chart gluing.
pending consult #101. Not included: Jacobian orders `h ≠ 0`; nonconstant analytic unit; general chart gluing.

## 5e. Phase E — the cube blow-up as a chart model (consult #102)

The blow-up cover of the cube for `K = |x|²` exists at leading order (CCLXXXIII–CCXCV). The all-order
expansion needs the producer generalised from "every coordinate is a divisor" to a CHART MODEL: active set
`A ⊆ Fin d` (components `↥A`), `k_i > 0`, orders `h_i` on `A`, phase `u₀(y|_{Aᶜ})·∏_{i∈A} y_i^{2k_i}` with a
positive analytic unit depending only on the INACTIVE coordinates, weight `∏_{i∈A}|y_i|^{h_i}`, signed box.
Corrections from #102: the absolute Jacobian `|y_β|^{d−1}` is even for every `d` (the determinant is not);
at `I ⊊ A` the weight also has active-tangential factors `∏_{j∈A∖I}|t_j|^{h_j}`; the full chart map is not
proper (keep `π = id` + an exact change-of-variables adapter); a general tangential unit must be reflected
per orthant (the cube's is invariant).

| Unit | Scope | Gate |
|---|---|---|
| E0a | executable obligation fixture: singleton active data of the cube, unit through inactive coordinates, absolute-Jacobian/reflection identities, exact chart integral adapter | compiles with no producer assumptions |
| E1 | partial-active geometry and normal data (`ChartModel.geometry d A k h`); full-active adapter | old coordinate geometry recovered; deepest stratum `≅ ℝ^{d−|A|}` |
| E2 | weighted abstract normalised core: general `h`, `c_h = J·H_I·L_I·fϕ`, `xData`/coefficient compatibility | `h = 0` recovery; nonzero-order core; `I ⊊ A` test |
| E3 | singleton tangential-unit producer: one core `n = 0`, `λ = u^{-1/(2k)}`, compact tangential base, common collar, negligible complement | arbitrary `d`, one active coordinate, explicit `h`, nonconstant unit |
| E4 | signed blow-up charts + exact finite-sum assembly of the ORIGINAL cube integral (all orders) | leading coefficient = CCXCV; odd normal orders vanish; constant packet has no higher coefficients |
| E5 (optional) | general partial-active water-filling collar | recovers G (full active, unit 1) and E3 (singleton) |

Stop after E4 for the paper ("assembled chart expansions of the cube integral"); the projector space and
intrinsic gluing are a separately gated phase.

Status (2026-09-13, main `d8853e3`, 648 modules): E0a = CCCXLIV (`BlowUpCubeChartModel`), E1 = CCCXLIII
(`ChartModelGeometry`), E2 = CCCXLV (`WeightedNormalisedBoxCore`), E3 = CCCXLVI (`SingletonChartCertificate`,
generalised to a positive-part prior representative), E4 = CCCXLVII (`BlowUpCubeExpansion`:
★★★ `BlowUpCube.cube_hasExpansion`, spectrum `spectrumLe 2 0`, exact decomposition
`cube_integral_eq_sum_pieces`) — ALL LANDED, axiom-clean. The E4 gate items (leading coefficient = CCXCV, odd
normal orders vanish, constant packet has no higher coefficients) are open follow-ups, not blockers; E5 not
started. Phase E is at the stopping point pending the audit consult (#103).

### 5f. Phase E4F — coefficient fidelity (consult #103: phase E ACCEPTED; bounded gate)

| Unit | Deliverable | Status |
|---|---|---|
| F0 | scope/parity/density documentation; observable germ bridge (`obsRep_piece_eventuallyEq`, `normalDifferential_obsRep_piece`) | CCCXLVIII |
| F1 | below-leading vanishing + leading coefficient `C(d/2) = π^{d/2} F(0)p(0)` by uniqueness of a finite power sum against the leading remainder (CCXCV, `1 < d`); wrapper over `d/2 ≤ α ≤ A` | CCCXLVIII |
| F2 step 1 | singleton support: coefficients vanish unless `α = (d+ℓ)/2` (kernel candidate exponents; every `d ≥ 1`); packet independence on the declared spectrum | CCCXLIX |
| F2 steps 2–3 | parity cancellation between paired normal-sign pieces (support `d/2 + ℕ`) | DEFERRED (needs the prior-coefficient/observable-jet convolution under the sign flip — a new bridge; time-box reached) |
| F3 | directional-derivative/Gamma coefficient formula | deferred (#103) |

Status (2026-09-13, main `cf32d46`, 650 modules): E4F closed at Astra's stopping point ("F1, preferably F2").
Paper may claim: singleton chart certificates in the signed blow-up coordinates assembled into an all-order
expansion of the original cube integral, indexed by the ambient half-integer lattice, with coefficients
vanishing below `d/2`, leading coefficient `π^{d/2}F(0)p(0)` (`d ≥ 2`), support `(d+ℓ)/2`, packet-independent.
Not claimed: a global resolved geometry for the blow-up / intrinsic coefficient field on the exceptional divisor;
parity cancellation; the Gamma formula. Next gate: consult #104 (closure + direction: J vs E5 vs gluing).

### 5h. Programme J-min — observable-independent coefficient functionals (consult #104 §3; main `fbbccc2`, 654 modules)

J0 finding: in a coefficient certificate the field `B_{I,r,q}` is built from bases, base measures, orders, sides,
frames and the PRIOR's density families only — the observable enters the coefficients only through
`D^r_⊥(φ∘π)` paired against it (definitional, `field_eq_kernelData := rfl`). The abstract certificate does
entangle observable and prior in the amplitude datum (`amplitude_eq : evalF x = c · obs∘Φ`, no separate density
identity), so re-observabling an abstract certificate is not possible; the route is the producer level with a
fixed extension domain (packet `withObs`: same `Ω`, same prior extension; the produced kernel is unchanged since
the prior's face-series coefficients are `rfl`-independent of the observable's extension).

| Unit | Deliverable | Status |
|---|---|---|
| J1 | `MomentKernelData` (observable-free kernel: bases, `ν`, `h, k, β, b`, frames, `cc`), its `field`/`stratumMeasure`, the jet functional `coefficient Kd ψ q` for every `ψ`; `Cc.field = Cc.kernelData.field` by `rfl` | CCCL |
| J2 | explicit coordinate kernel `coordKernelData` (`kernelData_coeffCertificate` by `rfl`), `withObs`, `producedKernel_withObs`, ★★ `hasCoordFreeExpansion_withObs` (every observable with an extension on the packet's neighbourhood: same measures, same field) | CCCLI |
| J3 | `normalDifferential_add/smul`, `expansionCoefficient_add/smul`, `Covered`/`field_eq_zero_of_not_covered`, `SmoothObs`, `Certified`, `coefficient_add/smul`; `contDiffAt_obs_base`, `certified`; `obsSpace Ω` (a real subspace), `certified_of_mem`, ★★★ `jetFunctional : obsSpace A.Ω →ₗ[ℝ] ℝ`, ★★★ `hasCoordFreeExpansion_obsSpace` | CCCLII–CCCLIII |
| J4 | finite-order seminorm bound / distribution | REJECTED TARGET (consult #105): the exact-moment representation need not truncate at an observable-independent normal order — at a fixed spectral index it can involve arbitrarily high normal derivatives (on the unit square `∫∫ x^a y^b e^{−Nx²y²} = (J_a − J_b)/(b−a)` contributes to `N^{−(a+1)/2}` for every `b > a`; nonminimal candidate exponents also contribute subleading terms). Terminology: "linear coefficient functional on analytic observables, represented by a convergent series of normal-jet pairings" (analytic jet functional); no topology/continuity/distribution asserted. The optional one-unit absolute-majorant estimate was NOT taken. |

### 5i. Paper closure (#105) and the companion note (#106)

Paper: Lean-facing programme CLOSED after the wording pass (pin `32cdbf6`; Overleaf push pending the user's
authorisation). Companion note `averaging_dataset.tex` (consult #106 ledger, `gpt6_bigpicture_v106.md`; G0 sheet
`g0_signature_sheet.md`): ten mandatory wording repairs applied; units:

| Rank | Unit | Status |
|---|---|---|
| 0 | G0 signature-and-composition audit (CLT/tail law constructed by `ClosureEndpoint`; consumed: certified chart data, sub-Gaussian proxy, bounded amplitude mass, `𝔼|A_n Rem_n| → 0`) | DONE (sheet) |
| 1 | finite-resolution quartet expectation transfer, every `β, λ > 0` | CCCLIV |
| 2 | expected quartet coefficients from `L¹` observable transfer (`expected_quartet_of_L1_transfer`) | CCCLV |
| 3 | predictive Taylor remainder `n 𝔼 sup_t ⟨|f|³⟩_{n,x,t} → 0 ⇒ n 𝔼|R_n| → 0`, then one controlled model | open |
| 4 | CLT/tail closure packaging (only if a gap remains after G0 — none found) | closed by G0 |
| 5 | `GaussianField.ofL1TaylorLimit` (compact field from the Taylor-data law + a bounded evaluation map) | open |
| 6 | ratio first-correction algebra | optional |

J-min CLOSED at the jet-functional theorem (Astra's stopping rule; #105 accepted). Paper closure gate (#105): a
wording pass on the mirror (distribution / support / expectation / general resolution / canonical / finite order),
repin + audit, Overleaf push (user authorisation), then the Lean-facing paper programme is CLOSED. Next: consult
#106 — claim-and-dependency survey of the companion note `averaging_dataset.tex`.

## 6. Hypotheses that remain at the end

Two levels (consult #99 §A5).

*Coordinate-model endpoint* (phases 1–3 and the hygiene phase): for the monomial phase on the compact
positive box the only hypotheses are the holomorphic extension packet on a complex neighbourhood of
the box (real-part agreement on its real slice, or on a real neighbourhood), `0 < d`, `0 < a`, and
nonnegativity of the prior on the box. The face radii, majorants, collar level, certificates, stratum
measures and coefficient field are produced. Not produced: the extensions themselves from real
analyticity; the box-only agreement theorem (chosen extensions); the optimal spectral lattice.

*General resolved application*: certified resolved geometry with a compatible monomial atlas
(a.e.-disjoint or multiplicity-corrected change of variables, exact core transport, tail gap, unit
handling), analytic admissibility of `φ` in the form of holomorphic extensions near the strata, and
uniform integrable bounds for the base integrals remain CERTIFICATE INTERFACES. Given them, the strata,
the normal differentials, the moment coefficients, the densities and the expansion are theorems; the
compact-box producer is the local model, and the geometry beyond the coordinate model (signed
coordinates, blow-up instances, a compatible SNC atlas) is the remaining programme.

## 7. Bookkeeping

Each unit: `Grammar/<Name>.lean`, HEADLINES row, README count, THEOREM_MAP chain, gated build,
axiom probe, merge to main; mirror paragraph and pin bump at milestones (after unit 7 — done with CCCIII —, 10, 11).
