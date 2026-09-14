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
| 3 | predictive Taylor remainder: `|R| ≤ S/6` from tilted absolute centred third moments ≤ S on [0,1]; `n𝔼S_n → 0 ⇒ n𝔼|R_n| → 0` (CCCLVI); one controlled model test (#107: normal location; posterior `N(m_n, d_n⁻¹)`, envelope `4(C₃|x−m|³v^{3/2}+C₆(v/2)³)`, `𝔼|R_n| ≤ (32C₃²d_n^{−3/2}+C₆d_n^{−3}/2)/6`, fresh-point and training certificates; marginal laws only) | CCCLVI (lemma); CCCLVII–CCCLVIII (model test DONE; thin quartet instantiation not attempted) |
| 4 | CLT/tail closure packaging (only if a gap remains after G0 — none found) | closed by G0 |
| 5 | `GaussianField.ofL1TaylorLimit` (compact field from the Taylor-data law + a bounded evaluation map): the ℓ¹ CLT law is `IsGaussian` (CCCLIX `clt_l1_isGaussian`), the synthesis map `∑ a_r φ_r` is bounded for `sup‖φ_r‖ ≤ M`, and the field with kernel `∫T(a)(y)T(a)(z)dν` exists through the Banach-law adapter (CCCLX `exists_gaussianField_of_clt`) | CCCLIX–CCCLX DONE (double-series kernel identification not claimed) |
| 6 | ratio first-correction algebra | optional |

COMPANION NOTE PROGRAMME CLOSED 2026-09-13 (consult #108, `gpt6_bigpicture_v108.md`): model test and Rank 5 accepted; closure wording pass applied to the note (pin `9a8cdc9`); no Lean units required. Deferred on downstream demand only: the thin normal-location quartet instantiation (≈2–4 units; two-sign identification sanity-checked in #108 but the actual prior gives finite-n rate β + a/n and marginal laws do not give Z_n ⇒ N(0,1)) and the coefficient-covariance double-series identification of `synthesisKernel` (≈1–2 units). Overleaf push of mirror and note awaits the user's authorisation.

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

*Domain hypothesis (consult #110 §1.1, 2026-09-13).* Compactness of `W` alone does not give power–log
asymptotics: for `K = x²`, `φ = ϕ = 1` and `W = {0} ∪ ⋃_{j≥0} [4^{−j}/2, 4^{−j}]` one has
`I(16n) = I(n)/4 + O(e^{−4n})`, so `n^{1/2} I(n)` is asymptotically log-periodic and non-constant
(`G(1) ≈ 0.4518`, `G(2) ≈ 0.4641`, `G(4) ≈ 0.4344`, `G(8) ≈ 0.4222`, `G(1)+G(4) = √π/2`): no leading
coefficient, no expansion. The producers therefore assume the zero set of `K` in `W` lies in the
interior of `W` (`K > 0` on the frontier; the boundary region is then a tail by compactness). Two
further exclusions: `K` identically zero on an open set carrying prior mass; boundaries touching the
zero set (a transversal analytic boundary `{π ≥ 0}` is the planned EXTENSION: resolve `K·π`, read the
domain as sign conditions on chart coordinates through the signed-box producers). Neither is part of
the present statements.

## 7. Bookkeeping

Each unit: `Grammar/<Name>.lean`, HEADLINES row, README count, THEOREM_MAP chain, gated build,
axiom probe, merge to main; mirror paragraph and pin bump at milestones (after unit 7 — done with CCCIII —, 10, 11).

## 8. Consult #109 phase (2026-09-13): the plan reopened

The user set the companion note aside and asked for the remaining gaps of THIS plan; Astra #109
(`gpt6_bigpicture_v109.md`) ranked them. Two tracks are in scope; the stopping rule is expectation
closure + genuine geometry closure + transport fidelity + statement audit (#109 §6).

| Track | Unit | Status |
|---|---|---|
| B | B0 feasibility (nontrivial normal line, local divisor equation, tubular from the total normal bundle — no global coorientation assumed) | passed (reading of `ResolvedGeometry`/`ResolvedNormalData`) |
| B | B1 projector blow-up space and charts | CCCLXI `BlowUpSpace` |
| B | B2 genuine normal data (tautological line, tubular map) | CCCLXII `BlowUpNormalData` |
| B | B3 transport toolkit (pushforward, base reindexing, finite sums of data and decompositions) | CCCLXIII `CoreTransport`, CCCLXIV `CoreFinsum` |
| B | B4 assembly: measure-level chart decomposition, piece bases and frames, ONE `ResolvedCertificate` on the genuine blow-up | CCCLXV–CCCLXVII (★★★ `cubeCert`, `cube_hasCoordFreeExpansion_blowUp`) |
| B | B5 transport fidelity: original packet, scalar canonicity with `cube_hasExpansion`, leading coefficient `π^{d/2}F(0)p(0)` | CCCLXVIII (★★★ `blowUpCoefficient_eq_cubeCoefficient`) |
| I | I1 scalar rational-log quotient theorem (Q1+Q2: `quotNum` recursion `S_{m+1} = Q_{m+1}P_0^{m+1} − Σ P_{β+1} S_{m−β} P_0^β`, `R_m = S_m/P_0^{m+1}`; inputs beyond the output cutoff) | next |
| I | I2 certificate integration (Q3: numerator and denominator from one kernel, `N_n[φ]/N_n[1]`, `φ = 1 ↦ 1`, linearity) | planned |
| I | I3 leading probability measure and the cube regression `E_n[F] → F(0)` (Q4) | planned |

TRACK B CLOSED 2026-09-13 (CCCLXI–CCCLXVIII, main `9f33370`).

## 9. Consults #110–#111 phase (2026-09-13): the certificate producer from a DOMAIN-sector atlas — LANDED

User directives: work on the certificate producer, then the product-sector atlas work (Track I set aside);
the domain `W = {π_j ≥ 0}` is resolved JOINTLY with `K` (Watanabe) and read as selected coordinate orthants
per chart — NO frontier-positivity hypothesis; standing hypothesis `K ≥ 0` on an open neighbourhood of `W`
(even phase orders). hironaka work in the LOCAL copy (`lean/hironaka`, branch `sector-atlas`, fork only).

| Unit | Content | Status |
|---|---|---|
| A/B (hironaka) | `DomainSectorAtlas extends ProductSectorAtlas` (`W`, `signs`, `domain_ae`, `sector`, `sectorMeasure`, ★ `domainTransport`); constructors `ofBoundaryMonomials` (boundary functions `π_j ∘ φ_i = u_{ij}·y^{m_{ij}}`, admissible signs) and `ofAll` | 078766c64 (fork) |
| C | compact-sheet spike: `Sheet.Space A = Σ_i ↥(dom i)`, proper `π`, `Sheet.geometry`, `Sheet.normalData` (clamp germs), `mapAmbient_ae` | CCCLXX |
| D | active-coordinate water-filling with inactive coordinates as parameters (`ChartCollar`) | CCCLXXI |
| E | parameterised tangential-unit weighted collar, chart-box certificate (`certificate`, `coeffCertificate`, ★★★ `hasCoordFreeExpansion_chart`) | CCCLXXII |
| F | analytic inputs from holomorphic packets (`toChartFaceSeries`, `exists_delta_chart`, `hasCoordFreeExpansion_chart_of_holomorphicBoxExtension`) | CCCLXXIII |
| G | orthant pieces on the symmetric box (`pieceCert`, `map_refl_pieceMeasure`, `exists_delta_pieces`) | CCCLXXIV |
| H1 | `LocalisationData.map_ae`, `reindexAll`, ★ `AnalyticCoreDecomposition.sigma` | CCCLXXV |
| H2 | `SheetInputs`; piece integrability FROM the domain (`hφint`); per-chart level with fibre-ball bound; `Ψ_p = incl_i ∘ R_σ`, phase/obs compatibilities, `pieceDatum`, `pieceCores`, `bmap`/`baseHomeo` onto sheet strata | CCCLXXVI |
| H3 | `datum`, ★ `datum_map_π`, `cores` (sigma), `pieceT`, `frameS`, ★ `Φ_eq`; ★★★ `cert`, ★★ `coeffCert`, ★★★ `hasCoordFreeExpansion` / `hasCoordFreeExpansion_of_domainSectorAtlas` | CCCLXXVII |
| I | cube regression through the general producer: `cubeInputs`, ★★ `cube_hasCoordFreeExpansion_generic`, log degree 0 | CCCLXXVIII |

Main `5e9babc` (680 modules). Hypotheses of the producer (`SheetInputs`): a `DomainSectorAtlas d K Ω`
with symmetric chart boxes `[−a,a]^d`, every chart with a nonempty active set, continuous tangential
phase units (`phaseUnit i` independent of the active coordinates) bounded below by `c_i > 0` on the box,
measurable charts and Jacobian units, a nonnegative measurable prior, an observable integrable for the
prior measure on `W`, holomorphic signed-box packets of `|jacUnit_i|·prior∘φ_i` and `obs∘φ_i` on every
chart box, nonempty `signs i`. Non-claims: the EXISTENCE of such an atlas for a general analytic `K` on a
semi-analytic `W` is not proved (the named open theorem, #110 §4); rectangular boxes (origin-preserving
scaling), charts with empty active set (all-tail), packets by composition with holomorphic chart data,
and the tangential-unit normal form of Watanabe's units are the remaining adapters. Next: consult #112 —
the atlas-existence programme from hironaka's exports (`WatanabeModificationOn`, `WatanabeEvenChartAt`,
`AnalyticQChartPacket`) with the boundary functions in the joint resolution.

## 10. Consult #112 (2026-09-13): atlas existence — verdict and the recorded stopping point

Astra #112 (`gpt6_bigpicture_v112.md`): the exported local resolution theorem (Watanabe's triple: manifold `U`,
proper `g`, LOCAL even charts) does NOT give a finite a.e.-disjoint box atlas; multiplicity correction does not
repair this while preserving the holomorphic-box hypotheses; the "real zero set in coordinate hyperplanes ⇒
unit·monomial" lemma is FALSE over ℝ (`x²+y²`) — the right algebraic core for joint monomialisation is the
factor-of-monomial germ lemma (`a·b = u·y^N ⇒ a = v·y^α, b = w·y^β`); complexification of real-analytic data
near a compact box is a separate project; the general route from a proper modification is SMOOTH LOCALISATION
on the resolved manifold, which needs a new smooth-amplitude expansion engine (G5), not a wrapper.

Executed (Astra's H1–H3 / G1–G4 list, stopping rule met):

| Unit | Content | Status |
|---|---|---|
| H2 | `MonomialBoxAtlas` (hironaka): `PartialResolution.ofId`, `monomialBoxAtlas`, `monomialHalfBoxAtlas` (coordinate half-spaces through `ofBoundaryMonomials`) | fork ca4a10a2b |
| G2 | boundary regression: `boundaryInputs`, ★★ `boundary_hasCoordFreeExpansion` (proper orthant subset, crossing divisor), `boundaryInputs_commonD = n − 1` | CCCLXXIX |
| G3 | inactive charts are tails: `SheetInputs` without `act_nonempty`; `addTail`, `inactive_gap`; `sigma` without a nonempty index | CCCLXXX |
| H3 | `ProductSectorAtlasRescale` (hironaka): centred boxes → `[−a,a]^n`, units × scaling constants, images unchanged, `DomainSectorAtlas.rescale` | fork 5890cebb7 |
| G1/G4 | `SheetRescale`: `compDiag`, `mulConst`, `CentredInputs → SheetInputs`, ★★ `hasCoordFreeExpansion_of_centred` (the conditional joint packet IS `CentredInputs`/`DomainSectorAtlas`) | CCCLXXXI |

Main `b9c4b13` (682 modules). RECORDED (Astra's wording): explicit and conditional jointly monomial
domain-sector atlases feed the coordinate-free expansion theorem; general extraction of finite exact box
transport from a proper analytic modification remains unproved. Open continuations (user decision): (i) H4–H7
local joint normal form (analytic coordinate division, factor-of-monomial germs, finite-factor neighbourhood
extraction, positive-unit absorption, properness-to-finite-cover) — real analytic-germ algebra, does NOT close
the transport gap by itself; (ii) G5 smoothly localised box expansion (new engine: smooth amplitudes with
Taylor remainders, all orders) — the standard general route; (iii) complexification of compact real-analytic
data (independent infrastructure). Deferred adapters: packets by composition with polynomial/rational charts
(generalising `pullbackChart`), a second boundary regression `π = xy` (same-sign orthants).
Addendum: CCCLXXXII `SheetCentredCubeRegression` (main `6c3be29`, 683 modules) — the `ρ`-cube (centred, non-symmetric
boxes) through `CentredInputs` with polynomial packets by substitution (`chartPoly`, `bind₁`): the end-to-end test of H3.
Mirror `grammar_lean.tex` local commit 634e45e (not pushed): domain paragraph rewritten to the landed state, pins bumped,
`\leanrefH` macro for the hironaka fork.

## 11. Consult #113 (2026-09-13): weights instead of disjointness — verdict and the Q1-α programme

User: a.e.-disjointness is not needed; is the obstruction that partitions of unity are not analytic? Astra #113
(`gpt6_bigpicture_v113.md`): yes. The engine needs, on each core, an amplitude that is a convergent normal
power series (ℓ¹ family, `amplitude_eq`), continuous in the base; a weight that is a continuous function of the
BASE point only is admissible today (`Fϕ.smul`), a weight varying in the normal directions is not, and a
multiplicity weight is discontinuous. Stratum-adapted partitions (normally constant near the divisor):
(a) own-chart admissibility IS the right certificate requirement (pieces need not share a normal foliation);
(b) but normalisation `a_i/∑a_j` destroys own-chart constancy in general, and a normally constant partition
subordinate to an ARBITRARY prescribed SNC analytic atlas is FALSE (collar counterexample `f(s)+g(s+t)=1` ⇒
both constant; circular divisor covered by two arcs); (c) Watanabe's clause gives no normal-coordinate
compatibility (`s' = s+u`, `s+u²` transitions); (d) single dominant-coordinate blow-up: concrete construction
`a_β = ∏_{γ≠β} η(z_γ²/z_β²)` (all numerators factor through the SAME direction map, so normalisation is safe);
composites along coordinate centres: a restricted programme needing an induction invariant. Smooth route (Q2):
finite deepest-corner jets do NOT determine even the leading coefficient (`∫∫ f(x)e^{−nx²y²}`, `f` supported
away from 0: leading term `(√π/2)n^{−1/2}∫f(x)/x`), so a smooth engine needs facewise transverse jets with
tangential dependence and controlled remainders (D1); moving the weight into the measure (D2) keeps analytic
data and §4 infrastructure but requires new weighted-moment asymptotics; stratum-adapted weights (D3) lose
nothing downstream, only geometric scope. Canonicity in the smooth setting: total coefficients `c_{α,j}` are
canonical, stratumwise allocations are not automatically. Log degree "codim − 1" is a bound/resonance
statement, not an unconditional equality.

Programme (Astra's top choice, user "happy either way"): Q1-α weighted-atlas producer with an explicit
`StratumAdaptedPartition` hypothesis (per-core base factorisation `χ_i(Φ_{i,c}(s,v)) = w_{i,c}(s)` a.e. on the
WHOLE core box, partition identity, gap on the excluded region, weighted transport), units: (1) core base-weight
adapter (scale `c`, `x`, certificate data by a continuous base weight); (2) weighted transport algebra (no
disjointness); (3) adapted-partition structure; (4) weighted domain-atlas producer; (5) tail bookkeeping;
(6) compatibility: disjoint atlases embed as the old case. First regression: enlarged overlapping
dominant-coordinate cover of a single blow-up with the direction weights. Stopping rule: one two-stage
coordinate-centre composite; stop unless an induction invariant preserving the base-factorisation equations is
provable. Non-claim wording: "certificates from weighted domain-sector atlases equipped with an explicit
per-core stratum-adapted partition; verified for the stated blow-up models; no claim that arbitrary SNC
resolutions or Watanabe modifications supply such partitions, nor that normally varying smooth weights enter the
analytic engine."

## 13. Consult #114 (2026-09-14): DESIGN of the smooth-amplitude engine (run in parallel with Q1-α, §12 = Q1-α agent's status)

Astra #114 (`gpt6_bigpicture_v114.md`): build D1 as a FACEWISE Mellin expansion theorem with D2 (analytic
datum for prior/observable, smooth weight `χ` as a parameter of the coefficient map) as the integration path.
Corrections: a full-box core is NOT face-free because cores are a.e.-disjoint (boundary layers near the faces
`v_J = 0` have positive volume and contribute algebraic terms); corner Taylor remainders `O(‖v‖^M)` are
insufficient; finite transverse order along faces ≠ finite normal order at the deepest base (Option A keeps the
infinite `r`-sum of observable jets with new smooth-weight moments; Option B = face-supported coefficient
distributions, later). Coefficients: `H_F(s,z) = Γ(z)β^{−z} Z_F(s,z)`, `Z_F(s,z) = ∫_{(0,b]^d} F ∏ v_i^{h_i − a_i z}`,
Laurent principal parts at poles `μ ∈ ⋃_i {(h_i+1+m)/a_i}`, `C_{μ,j}(F) = (1/j!)∫_K d_{μ,j+1}(s) dν`; explicit
face-subtraction continuation `Z_F = Σ_{J⊆[d]} Σ_{m_J<p_J} [∏_{i∈J} b^{h_i+m_i+1−a_i z}/(h_i+m_i+1−a_i z)]
∫_{(0,b]^{J^c}} (∏_{J^c} R_i) F_{J,m} ∏ v_i^{h_i−a_i z}` with `F_{J,m} = ∂_J^m F/m!|_{v_J=0}`; remainder
`≤ C_L ‖F‖_{mixed,p} N^{−L}(1+log N)^{d−1}`. D2: `M_{γ,χ}(N,s) = ∫ χ v^{γ+h} e^{−Nβ∏v^{2k}}` with
index-dependent subtraction depths `p_i(γ)` giving uniform-in-γ bounds `≤ C_L ‖χ‖_{mixed,P} b^{|γ|} N^{−L}…`
(fallback: Cauchy margin `b' > b` absorbs `(1+|γ|)^M`); coefficient map `smoothTanCoeff_χ(x; μ, j) =
∫ Σ_γ c_γ(s) m_{γ,μ,j}(χ; s) dν` linear and bounded in the ℓ¹ datum. Units: U0 regression
`∫_0^b∫_0^b f(x)e^{−Nx²y²} = (√π/2)N^{−1/2}∫f/x + O(e^{−cN})` for `f` supported away from 0 (all corner jets
vanish); U1 one-coordinate subtraction operator (parameterised meromorphic continuation); U2 tensor
subtraction + Laurent bookkeeping (`FaceMellinDatum`); U3 smooth core expansion (`O(N^{−T})` contour theorem,
then the cutoff bound — smooth replacement of `cutoffExpansion_gInt`); U4 D2 adapter (shifted moments,
uniform-in-γ, equality with old coefficients for `χ = 1`); U5 weighted core/decomposition assembly; U6
coordinate-free D2 certificate (Option A; total canonicity, J-min independence); U7 facewise finite-order
presentation (later); U8 stochastic adapter. Stopping rule: engine usable at U6. Non-claims: smooth weights
can cancel poles (flatness ⇒ faster-than-algebraic decay); RLCT readout needs nonvanishing; `C^M` certificates
license only finitely many orders.
Consult #116 (2026-09-14, `gpt6_bigpicture_v116.md`): the real-variable route for U2–U3 is sound; corrections/simplifications:
normalise face remainders by `1/∏_{i∈J} m_i!`; nonempty inner faces only call the monomial engine (the fully flat term
`J = ∅` is bounded elementarily by `e^{−x} ≤ C_L x^{−L}`: `≤ M C_L β^{−L} N^{−L} ∫ v^{p+h−aL}` — no logs); the two-regime
inner bound is global (no shrinking region), with `1+|log(N w^{a})| ≤ (1+log N)(1+|S(w)|)` and the reusable
integrability of `∏ w_i^{c_i}(1+|Σ a_i log w_i|)^D` on `(0,b]^K` for `c_i > −1`; log degree preserved (`≤ |J|−1`);
use the box API `boxCoeff` at side `b` with `t = N w^{a_K}`; pad inner lattices `Q_J | Q_all`; define
`smoothCoeffAtDepth p F μ q` FIRST, prove the expansion for every valid `L`, prove UNIQUENESS of finite power-log
expansions, then the depth-free `smoothCoeff`. Lean: index by an arbitrary `[Fintype ι]` (cores instantiate
`ι := Nrm I`), inline hypotheses `ContDiff ℝ ∞ F` + rectangular mixed-derivative bound `M`, a split wrapper
(reuse `Tan/Nrm/split` or `piEquivPiSubtypeProd`), faces `J ∈ univ.powerset` with `FaceMultiIndex p J := (i : ↥J) → Fin (p i)`,
subset sum externally + list induction internally; parameters via a wrapper (joint continuity of `∂_v^α F(s,v)`,
finite `ν`); U4 by the radius margin (`sup|∂^α A_c| ≤ C‖c‖_{ℓ¹_{b'}}`), new `WeightedCorePresentation` exposing the
same expansion interface. Milestones: (1) the 1D smooth theorem (coefficients `Σ_{m<p} F^{(m)}(0)/m! c^{(m)}_{μ,0}`,
NOT Gamma identification), (2) the generic one-flat-complement face theorem, (3) `d = 2` tensor expansion (U0 check).

## 12. Q1-α executed (2026-09-14, Q1-α agent): the weighted-atlas producer and the overlap regression

Landed (main `5059e8f`, 686 modules; hironaka fork `sector-atlas` 98b308864):
- hironaka: `ProductSectorAtlas` split into `ProductChartAtlas` (chart data, no disjointness) + `aeDisjoint`;
  `WeightedSectorAtlas` (weights `ω_i`, `HasWeightedTransport`), `WeightedDomainAtlas` (+ `W`, orthants;
  ★ `weightedDomainTransport`), ★ `hasWeightedTransport_of_partition` (weights `χ_i ∘ φ_i` from a partition
  of unity a.e. on the resolved set), `congr_ae`, `toWeighted` embeddings; `ShiftedBoxAtlas` (two translated
  identity charts, ramp weights, `shiftWeight_sum`, ★★ `shiftedAtlas : WeightedDomainAtlas`).
- grammar CCCLXXXIV: `Sheet.*` over `ProductChartAtlas`; `SheetInputs` over `WeightedDomainAtlas` with the
  stratum-adapted hypotheses `t₀`, `ω_indep`, `ω_contOn`; base weight `gw`, ★ `ω_Φ_eq` (weight constant on
  every core, via `ω_eq_of_agree` and the collar level `δ_t₀`), face series `F := F₀.Fϕ.smul gw`, chart-box
  certificates of CCCLXXII called directly; ★★★ `hasCoordFreeExpansion_of_weightedDomainAtlas`;
  `hasCoordFreeExpansion_of_domainSectorAtlas` = weights 1 (all earlier regressions unchanged via `toWeighted`).
  Units 1–6 of #113 done (base-weight adapter, weighted transport, adapted partition structure, weighted
  producer, tails (already per chart + inactive charts), compatibility).
- grammar CCCLXXXVI: unit 7 in the honest form that exists: `overlapInputs`, positive-measure overlap,
  nonconstant continuous tangential weights, partition identity, ★★ `overlap_hasCoordFreeExpansion`.

NOT done, with the reason: Astra's single-blow-up instance (dominant-coordinate charts with tangentially
enlarged boxes `|y_γ| ≤ 1+ε`). With box charts of finite normal extent the union of the images is a star with
"ears" (points whose dominant coordinate exceeds 1 lie only in a non-dominant chart); a direction-only
partition subordinate to that cover cannot exist (at a direction with two near-maximal coordinates both
weights are forced to vanish). Repair: a normal cutoff `θ(|x_β|)` supported in the tail `K ≥ δ`; then the
pulled-back weight is base-only near the divisor but DISCONTINUOUS at the outer face of the box where the
normalising sum vanishes — admissible for the producer (weights need only be measurable and bounded globally,
continuous and base-only near the divisor), not yet formalised (a.e. positivity of the normaliser on the star,
measurability, the partition identity a.e.). The two-stage composite was not attempted. Lake note: an olean
built in another worktree may not be materialised (artifact cache `synthetic` trace without the file); fix by
hard-linking `$LAKE_CACHE_DIR/artifacts/<hash>.olean` into `.lake/build/lib/lean/Grammar/`.
Status 2026-09-14 (main `d68cf78`, 687 modules). Smooth engine landed: U0 CCCLXXXIII `SmoothFaceRegression`
(★ `faceRegression`: face integral `(√π/2)N^{−1/2}∫f/x`, corner jets vanish); U1 CCCLXXXV `SmoothCoordTaylor`
(coordinate derivatives with symmetry, `coordRem_bound`, commutation, ★★ `remList_bound`); U2 milestone 1
CCCLXXXVII `SmoothOneDim` (★★ `oneDim_smooth` with explicit constants; `flat_bound` without logarithmic loss;
half-line monomial integral and tail). Q1-α agent (§12): CCCLXXXIV weighted-atlas producer
(`hasCoordFreeExpansion_of_weightedDomainAtlas`, hironaka `WeightedDomainAtlas`, `hasWeightedTransport_of_partition`),
CCCLXXXVI `SheetOverlapRegression` (two overlapping shifted charts with ramp weights); the enlarged dominant-coordinate
blow-up cover is OBSTRUCTED as stated ("ears": points whose dominant coordinate exceeds the box lie only in a
non-dominant chart; a direction-only partition cannot exist) — a tail-supported normal cutoff repairs it (weights
need only be measurable/bounded globally, base-only near the divisor) but was not formalised. Next (smooth engine):
milestone 2 = the generic one-flat-complement face theorem (inner monomial integral with the two-regime estimate
integrated against a product-flat outer amplitude), milestone 3 = `d = 2` tensor expansion (U0 compatibility), then
U3 general `d`, U4 D2 adapter (radius margin), U5/U6.

### 13.1 Status 2026-09-14 (after U3): smooth engine milestones 1–3 and U3 CLOSED
Main `3a10735` (698 modules). Landed: CCCLXXXVIII `SmoothLogIntegrable` + `SmoothFaceTheorem`
(★★ `face_expansion`, the generic one-flat-complement face theorem with the GLOBAL two-regime input and
preserved log degree); CCCLXXXIX `SmoothInnerMonomial` + `SmoothTwoDim` (★★ `twoDim_smooth`: corner jets ×
monomial box integrals + two edge face integrals + `O(N^{−L})`, explicit constant; U0 compatibility confirmed);
CCCXC `SmoothFaceOperators` + `SmoothFaceSplit` (★ `sum_faceOp` subset formula, ★ `tayList_eq_sum`,
★★ `faceTerm_integral`, ★ `faceAmp_bound`); CCCXCI (delegated agent) `SmoothFaceMonomial` (★★
`faceMono_two_regime` through the box engine, `faceMonoCoeff`) + `SmoothFiniteUniqueness` (★★
`finite_coeff_unique`); CCCXCII `SmoothAssemblyAlgebra` + `SmoothGeneralDepth` + `SmoothGeneral`:
★★★ `smooth_expansion_at_depth` and ★★★ `smooth_cutoffExpansion : CutoffExpansion (2∏k) (d−1)
(smoothIntegral F h k β b) (smoothCoeff F h k β b)` from `ContDiff ℝ ∞ F` alone, ★★ `smoothCoeff_unique`.
Design notes: depth `pᵢ = 2kᵢL − hᵢ` for `L ≥ L₀ = Σhᵢ + 1`; canonical coefficient at `μ` uses the cutoff
`max(⌊μ⌋₊+1, L₀)`; the empty face is `e^{−βt}`; `inJ` predicate keeps `Subtype.fintype` on face subtypes.
NEXT: consult #117 (U4 base parameters / units β(s), U5 smooth core presentation, U6 coordinate-free
smooth statement and the weighted-atlas closure without `ω_indep`/`ω_contOn`).

### 13.2 Status 2026-09-14 (after U4–U6b): the smooth route is CLOSED through the producer
Main `a97005c` (708 modules). Consult #117 (`gpt6_bigpicture_v117.md`) designed U4–U6; all landed.
CCCXCIII `SmoothTimeRescale` (`smoothIntegral F h k β b N = smoothIntegral F h k 1 b (βN)`, `scaleCoeff`
log-degree mixing, zero-support of canonical coefficients), `SmoothAmplitudeFamily` (jointly continuous
derivatives over a compact base; uniform rect bound; `continuous_smoothCoeff`; `uniform_cutoff`),
`SmoothFamilyIntegral` (`cutoffExpansion_integral(_beta)`: integrate the family expansion against a finite
base measure with a continuous positive unit β(s)). CCCXCIV `SmoothCoreDecomposition` (`SmoothCorePresentation`
with nonnegative transport density ρ, observable kept out of the density; ★★★ `cutoffExpansion` of the
global Laplace integral from finitely many cores + an exponentially small tail). CCCXCV
`SmoothExpansionCertificate` (scalar coefficient functional, `HasSmoothCoordFreeExpansion`, analytic
compatibility `coeff_eq_gCoeff` by uniqueness) + `SmoothCoreCertificate` (★★★ `hasSmoothCoordFreeExpansion`,
★★ presentation independence `coeff_eq_of_decompositions`). CCCXCVI `SmoothAffineFamily` (orthant
reflections/glue, chain rule for `pdMulti`, `SmoothAmplitudeFamily.ofAffine`) + `SmoothSheetTransport`
(`baseMeasure`, ★★ `map_glueE'_pieceMeasure`). CCCXCVII `SmoothSheetPieces` (`SmoothSheetInputs d`: smooth
weighted domain atlas, NO `ω_indep`/`ω_contOn`; per-orthant `piecePresentation`) + `SmoothSheetProducer`
(★★★ `SmoothSheetInputs.hasSmoothCoordFreeExpansion`, ★★ `coeff_eq_of_inputs`).
Non-claims: chart data assumed globally smooth (neighbourhood/smooth-extension version not done);
coefficients are scalars, not a jet field; existence of a smooth weighted atlas is an input.
IN FLIGHT: U6c regression (overlapping shifted boxes with an ACTIVE-dependent smooth ramp; hironaka
`shiftedAtlasOf` for an arbitrary partition function); optional: smooth-extension helper, d=0 regression,
coefficient linearity; audit consult #118.

### 13.3 Status 2026-09-14 (U6c + refinements): the smooth route is COMPLETE
CCCXCVIII `SmoothExtension` (smooth Urysohn `exists_contDiff_zero_one_nhds`, `exists_contDiff_eqOn_of_contDiffOn`;
`SmoothSheetNhdsInputs`: prior/observable smooth only on an open neighbourhood of the closed domain — the
producer's global-smoothness non-claim for the DATA is removed; chart data remain globally smooth, they live in the
atlas). CCCXCIX `SmoothCoefficientLinearity` (certificate `add/smul/zero/congr`; ★★ `coeff_add`, `coeff_smul`: the
intrinsic coefficient at each `(μ,q)` is a linear functional of the observable). CD `SmoothOverlapRegression` (U6c,
delegated): hironaka `shiftedAtlasOf τ` for an arbitrary partition function (fork `sector-atlas` 001c545b6, pin bumped);
`activeRamp` depends on the active coordinate, ★ `activeRamp_not_ω_indep` (analytic producer's hypothesis FAILS),
★★ `smoothOverlap_hasSmoothCoordFreeExpansion`, ★★ `coeff_eq_of_ramp` / `coeff_active_eq_coeff_tangential`.
Remaining optional items: d = 0 regression; cube blow-up with radial weight `χ(‖x‖²)`; audit consult #118.

### 13.4 CLOSURE 2026-09-14 (Astra #118 audit: "close U1–U6c")
Audit verdict: the smooth engine is complete as a CONDITIONAL asymptotic theorem (conditional on `SmoothSheetInputs`);
the remaining gaps are geometric, not analytic: (a) resolution-space → weighted-transport bridge (partition of unity
on the RESOLVED space, chartwise change of variables, null sets, a.e. injectivity), very large unless hironaka exports it;
(b) domain rectification (inequalities defining `W`); (c) unit normalisation (`hu_tan`; the paper's local coordinate
change `u₁ ↦ ε^{1/2k₁} u₁` — no cheap amplitude workaround: `e^{−N(u−β)y^{2k}}` makes the amplitude `N`-dependent);
(d) neighbourhood smoothness of chart data (wrapper); (e) zero-phase components (constant summand — now `const`+`add`).
Checks done: log convention positive (`scaleCoeff` uses `(log β)^{j−q}` for `N^{−μ}(log N)^q` scales); active dimension
`0` = positive phase, exponentially small (d = 0 regression). CDI `SmoothClosure` (const certificate, chart-wise
support). Coefficient functional: scalar linear functional is the final form; optional future target
`coeff_eq_of_equal_finiteJets` (∃ R independent of f, g). Mirror paragraph: Astra's §4 wording adapted into
`grammar_lean.tex` (local commit only). NEXT PROJECT (separate name/acceptance): "a smooth weighted normalised atlas
from resolution data", starting with the resolution-space-to-weighted-transport bridge.
