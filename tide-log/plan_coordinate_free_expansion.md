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
Final state 2026-09-14: main `62af5df` (714 modules). CDII `SmoothCubeRegression` (radial smooth non-analytic prior on
the cube blow-up, `commonD = 0`) + `SmoothZeroDim` (`smoothIntegral_zeroDim`, `smoothCoeff_zeroDim`). SMOOTH PROGRAMME CLOSED.

## 14. PROJECT: a smooth weighted normalised atlas from resolution data (opened 2026-09-14; user: "proceed with 1"; consult #119 = design)
Astra #119 (`gpt6_bigpicture_v119.md`): **Target A** = `K` analytic on open `U₀`, `K ≥ 0` on connected open `W ∋ 0`, `K(0) = 0`,
`K ≢ 0` near `0`, prior `C_c^∞`, `tsupport prior ⊆ W`, obs smooth ⇒ `∃ c Q D, HasSmoothCoordFreeExpansion (∫ prior·obs·e^{−NK}) c Q D`.
Output interface is NOT the strict `WeightedDomainAtlas` (a support-local partition cannot sum to one on full outer-box images):
`SmoothWeightedNormalisedCoreTransport K prior` = finitely many ZERO charts `ψᵢ` (Watanabe even chart form, `phaseConst·∏v^{2k}`,
`det = bᵢ·v^h`, bᵢ ≠ 0 analytic on open `Vᵢ ⊇ box`), smooth weights `ωᵢ` on `Vᵢ`, a TAIL MEASURE with phase gap `δ`, and
`∑ (sourceMeasure prior i).map ψᵢ + tail = vol.withDensity (ofReal prior)`. Bridge = Euclidean chart-by-chart change of variables
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on box ∖ walls; NOT `PartialResolution`); cutoffs = chartwise bumps `βᵢ∘φᵢ`
extended by zero, normalised by a smooth `q(s)` with `t·q(t) = 1` for `t ≥ 1/2` (NOT `1/s`; NOT Mathlib manifold PoU); target
weights `χᵢ = ρᵢ∘g⁻¹` on the regular locus (measurable via BijOn + local homeo inverse), a.e.-identified with the smooth
`ρᵢ∘φᵢ.symm` (phase walls null); residual `α = ∑χᵢ`, tail density `prior·(1−α)`, gap from compactness of `C ∖ {s > 1/2}`;
`vol(S ∩ {K=0}) = 0` by finite chart images of walls (no analytic-zero-set theorem). Global-smoothness: extend the ONE scalar
amplitude `Gᵢ = ωᵢ|bᵢ|·prior∘ψᵢ·obs∘ψᵢ` (CCCXCVIII), not the atlas fields. Units 0–9 (§7 of the consult); land Unit 1 first
(supported one-chart transport kernel, hironaka, arbitrary measurable target density); regressions: `d=1`, `K=x²`, identity
modification, no-tail AND genuine-tail AND empty-core cases. Target B (semianalytic W) after A: needs a simultaneous exact chart
packet for `K` and the boundary functions (hironaka export). Acceptance: (1) `WatanabeModificationOn K W` + prior ⇒ the
core-transport-with-tail, no atlas hypothesis; (2) compose with `exists_watanabeModificationOn` ⇒ Target A; (3) regressions.
Progress 2026-09-14 (hironaka fork `sector-atlas`, remotes renamed: origin = fork, upstream = timaeus-research):
60f0676c4 Units 1–2 `SupportedTransport` (`lintegral_supported`, `map_supported`, `sum_withDensity_add_residual`);
2fa91f429 `NormalisedCoreTransport` (interface + `ofMonomialNoTail`); f6d377f42 `ChartWeights` (`targetWeight` via
`Function.extend` + `measurableEmbedding_of_fderivWithin`, `map_targetWeight`, `sum_targetWeight_le_one/eq_one`);
769cabf43 `CoreTransportAssembly` (`activeWalls`, `ChartData`, ★★ `assemble`). In flight (agents): Unit 5
`ZeroChartExtraction` (`EvenChartBox`, `exists_finite_evenChartBoxes`, `isCompact_zeroFibre`, `injOn_offZero`,
`zeroSet_eq_walls`), Unit 4 `ChartCutoffs` (`exists_chartCutoffs`), Unit 3 grammar `SmoothBridgeConsumer`. INCIDENT:
Lake wiped the symlinked clone (see memory); package dirs are now Lake-managed clones.
★★★ TARGET A LANDED 2026-09-14: main `83d9986` (716 modules). hironaka fork `sector-atlas` 26f92335d: `ZeroChartExtraction`
(Unit 5, agent), `ChartCutoffs` (Unit 4, agent), `CoreTransportAssembly` (`assemble`), `ResolutionBridge`
(★★★ `exists_normalisedCoreTransport_of_modification` / `_of_analyticOnNhd`). Grammar CDIII `SmoothBridgeConsumer` (Unit 3,
agent; ★★★ `NormalisedCoreTransport.hasSmoothCoordFreeExpansion`, `coeff_eq_of_transports`), CDIV `SmoothTargetA`
(★★★ `exists_hasSmoothCoordFreeExpansion_of_analyticOnNhd`: analytic `K ≥ 0` on connected open `W ∋ 0`, `K(0)=0`, `K ≢ 0`,
smooth prior with compact support in `W`, smooth obs ⇒ `∃ c Q D, HasSmoothCoordFreeExpansion`; extra hypothesis `Measurable K`).
Design deviations from #119: per-chart box radii (no rescaling), a.e. gap hypothesis in `assemble`, `hu_tan` free (Watanabe
unit = 1), `IsManifold` not needed for cutoffs. In flight: hironaka regressions `ofMonomialWithTail` (d = 1, genuine tail),
`ofEmptyCores` (agent, branch bridge/regress). NEXT: consult #120 (audit of Target A; design of Target B).
Consult #120 (`gpt6_bigpicture_v120.md`): Target A AUDIT PASSED (deviations harmless). Cleanups (agent, branch tide/targetA2):
phase-localisation wrapper removing `Measurable K` (indicator representative + locality of the integral in the phase on the
prior support), translation wrapper (any zero of K, not the origin), positive-phase case via `ofEmptyCores` (all coefficients
zero), certificate-facing theorem `∃ C : SmoothExpansionCertificate Z, C.D ≤ d − 1` with `hKnt : ∃ x ∈ W, K x ≠ 0`, consumer
regressions (`ofMonomialWithTail`, `ofEmptyCores`). TARGET B design: (i) ambient vs domain-only nonnegativity (`K = x` on
`[0,1]` has odd order at the boundary zero — the even-chart interface needs AMBIENT `K ≥ 0`; else arbitrary exponents on
selected orthants + `u = s v²` sector adapter); (ii) the export needed = ONE proper surjective modification for the FAMILY
`(K, π_j)` with INDIVIDUAL factor monomial forms (resolving the product suffices given the factor-divides-monomial lemma in the
analytic local ring: coordinate germs prime; zero-set containment is NOT enough — `x²+y²`); (iii) interface
`NormalisedDomainCoreTransport` with `sectors`, source restricted to selected orthants, target `vol|_{Wdom}·prior`; bridge:
cutoffs unchanged, exceptional set = zero sets of ALL factors; consumer: existing per-(chart, orthant) presentations. hironaka
sector-atlas d5ae59da5 (regressions merged, ProdId linter fix; the Monomialize root builds). BM89 export audit in flight (agent).
hironaka sector-atlas 1c1bf695b: `DomainCoreTransport` (Target B interface `NormalisedDomainCoreTransport d K prior Wdom` with
`sectors`, `sectorSource`; `DomainChartData` (+ `domain_ae`), `χ_eq_zero_ae` off the domain, `map_sectorSource_restrict`,
★★ `assembleDomain`). In flight (agents): BM89 export audit (what hironaka provides towards ONE modification with individual
factor forms); grammar Target A cleanups (tide/targetA2); grammar domain consumer `SmoothDomainConsumer` (tide/domainconsumer,
worktree grammar-tide-phase7).
BM89 AUDIT (agent) for Target B: hironaka has NO family monomialisation, BUT (i) `watanabe_thm_2_3_of_isConnected_of_bo`
runs on an arbitrary single analytic `F` — apply it to the PRODUCT `F := K · ∏ π_j` (iso off the WHOLE family zero divisor);
(ii) the factor-splitting lemma exists and is certified: `Monomialize/Analytic/Germ/MonomialFun.lean:46
exists_nhd_eq_unit_mul_monomial` (F·G = unit·monomial on an open nbhd of 0 ⇒ F = unit·monomial on a polydisc; germ version
`eq_unit_mul_monomial_of_mul_eq`, `prime_convX`, `Conv` is a UFD); (iii) `ofBoundaryMonomials`/`domain_ae_of_boundaryMonomials`
consume exactly the per-factor forms (as hypotheses). TARGET B PLAN (hironaka): B1 factor splitting at a centred chart
(iterate the lemma over the family; Σ exponents = θ); B2 parity/sign on a connected polydisc (K ≥ 0 ambient ⇒ even exps,
positive unit; boundary units constant sign ε_ℓ); B3 ALIGNED UNIT ABSORPTION `e(u) = (v^{1/2k₁}u₁, u₂, …)` (or general
diagonal unit rescaling) preserving all unit×monomial forms with the SAME exponents and the maximal-atlas membership
(`restrOpen_trans_mem_maximalAtlas`) — makes `K∘rep' = ∏u^{2k}` exactly; B4 per-chart `domain_ae` from constant-sign monomial
boundary forms (adapt `domain_ae_of_boundaryMonomials`); B5 generalise `ChartData.injOn` to an arbitrary closed null wall set
⊇ active walls (the product blow-down is injective only off ALL factor walls) + the domain bridge (C₀ = g⁻¹(Wdom ∩ supp ∩
{K=0}); nullity of `E ∩ S` via a SEPARATE finite chart family at F-zeros); B6 Target B final theorem (grammar).
CDV `SmoothTargetAClean` LANDED (Target A final form: `exists_smoothExpansionCertificate_of_analyticOnNhd`, no Measurable K, any
zero, positive-phase pure tail, regressions). hironaka sector-atlas bb46913a7: `ChartData.walls` generalised (B5 prerequisite).
In flight (agents): B1–B2 `FactorSplitting` (wtA), B3 `UnitAbsorption` (wtB), B4 `ChartDomainReading` (wtC), grammar
`SmoothDomainConsumer` (phase7).
hironaka sector-atlas 5ef3fc813 (Target B, all glue except the final assembly): `ChartDomainReading` (B4, agent: `chart_domain_ae`,
`chartAdmissibleSigns`, `DomainChartData.ofBoundaryMonomials`), `UnitAbsorption` (B3, agent: `AbsorbingChange`, `Φ.chart`,
`watanabeRep_chart_phase` — exact even phase after absorbing the unit on one active coordinate; all other unit×monomial forms
preserved with the same exponents), `FactorSplitting` (B1–B2, agent: `exists_box_factors_unit_mul_monomial`, `exists_evenBox_factors`),
`DomainBridge` (mine: `ProductChartBox`, `exists_normalisedDomainCoreTransport_of_cover`, `volume_zeroSet_inter_compact`).
Grammar CDVI `SmoothDomainConsumer` LANDED (main 24b32f4, 718 modules; half-box/half-line regressions). In flight: B5a
`ProductChartExtraction` (agent: `exists_productChartBox` from the product resolution via factor splitting + unit absorption,
`exists_finite_productChartBoxes`). Then B6: hironaka `exists_normalisedDomainCoreTransport_of_analyticOnNhd` (Watanabe on
`F = K·∏π`) and the grammar Target B theorem `∫_{Wdom} prior·obs·e^{−NK}` (Wdom = boundaryDomain W π compact).
★★★ TARGET B LANDED 2026-09-14: main `5e14080` (719 modules); hironaka sector-atlas 9ca3ad986 (`ProductChartExtraction` B5a
agent, `DomainBridgeFinal`: `exists_normalisedDomainCoreTransport_of_analyticOnNhd`). Grammar CDVII `SmoothTargetB`:
`exists_hasSmoothCoordFreeExpansion_domain_of_analyticOnNhd` (K, π_ℓ analytic on U₀; K ≥ 0 on connected open W ∋ 0;
`K·∏π` vanishes at 0, ≢ 0 near 0; `Wdom = W ∩ {π ≥ 0}` compact; smooth prior with compact support in W; smooth obs;
Measurable K) and the certificate form with `C.D ≤ d − 1`. NEXT: consult #121 (audit of Target B; cleanups — remove
`Measurable K`, translation/positive-phase wrappers as for Target A; ball-inequality regression; mirror paragraph; closure).
Consult #121 (`gpt6_bigpicture_v121.md`): TARGET B AUDIT PASSED. Domain class = compact BASIC analytic-inequality domains
`D = A ∩ ⋂{π_ℓ ≥ 0}` inside a connected open analytic ambient `A` (not arbitrary compact semianalytic sets — finite gluing of
overlapping basic domains is out of scope). Identically-zero chart factors excluded by the product form on raw Watanabe
charts (not by image openness). PROJECT CLOSED after a Target B façade (agent, tide/targetB2): arbitrary phase-zero anchor,
positive-phase branch, local prior/observable via cutoff, no Measurable K, named domain. Non-claims: no general semianalytic
front end; no zero-phase/disconnected-ambient treatment; no RLCT identification of the leading nonzero exponent; no nonzero
leading coefficient for arbitrary observables; no coefficient algorithm.
★★★ PROJECT CLOSED 2026-09-14: main `b183f46` (720 modules). CDVIII `SmoothTargetBFacade` (agent):
`exists_smoothExpansionCertificate_domain` (any zero anchor, no Measurable K, pure-tail branch, local data wrapper, named
domain, interval regression). Mirror `grammar_lean.tex` commit 1140ae4 (Overleaf clone, LOCAL, ahead 4; pins b183f46 /
hironaka 9ca3ad986; all 1100+ dots verified). Candidate next projects (Astra #121): (1) general compact semianalytic front
end — finite gluing of overlapping basic domains (M+); (2) RLCT identification of the leading nonzero exponent via
hironaka's E5 readout (separate readout project; S/M only if the leading asymptotic aligns exactly); (3) disconnected
ambient / identically zero phase components (M).

## 15. Strata-integral form of the smooth coefficients (opened 2026-09-14; user: "go ahead with 1"; consult #122 = design)
Astra #122: the ORDINARY kernel form `c_{μ,q} = Σ_I ∫_{S_I} Σ_{|α|≤R} ⟨∂^α_⊥(φ∘π), B_{I,α}⟩ dν_I` with integrable fields is FALSE
in general for smooth data at crossings: on `[0,1]²` with `K = x²y²`, `∫∫ x^M e^{−nx²y²} ~ (√π/2M) n^{−1/2}` for EVERY `M`
(arbitrarily high corner Taylor terms at the same exponent — the observable is seen along the axis `y = 0`, not through
a finite corner jet), and `f_ε = χ(x/ε)χ(y/ε)` has `c_{1/2,0}(f_ε) = c(χ⊗χ) + 4A log ε` unbounded while its axis values and
corner jet are bounded — the missing objects are SUBTRACTED integrals `∫_0^1 (f(x,0) − f(0,0))/x dx` (finite parts), which is
exactly what the engine's `remList` remainders encode. Correct targets: **Theorem A** finite-jet determination
(`∃ R, ∀ f g, equal R-jets on the resolved divisor (then: on `D ∩ K⁻¹0` ambiently) → c_{μ,q}(f) = c_{μ,q}(g)`; the
coefficient factors through the range of the finite-jet restriction map — a linear functional on finite face jets);
**Theorem B** the renormalised chart-strata formula separating observable jets from density-only functionals
`𝓑_{J,a,μ,q}(u) = ∫_s Σ_{a≤m<p} 1/(m−a)! Σ_j C_{J,m,μ,j} C(j,q) ∫_{K-box} R_K^p[d_{J,m−a} u] w^{h_K}(w^{2k_K})^{−μ} log^{j−q}`
(Leibniz on `∂^m_J(D f)`; do NOT commute `remList` past the product); **Theorem C** (later, XL) distributional global
packaging. Units: 1 face-trace dependency of `remList`/`faceAmp` (M); 2 intrinsic finite-jet theorem (M–L); 3 finite-order
`C^R` bound (M–L); 4 Leibniz-separated formula (L); 5 choice comparison by uniqueness (S–M); 6 global (XL); 7 ordinary-kernel
specialisation under extra hypotheses. Regressions: `c_{1/2,1}(P) = √π/4·P(0,0)` (CCCXV), `c_{1/2,0}(x^M) = √π/(2M)`,
axis-subtraction form of the constant coefficient, weight Leibniz. Non-claims recorded per §8 of the consult.
CDIX `SmoothJetDetermination` LANDED (Theorem A; agent): `smoothCoeff_congr` (jets of order `depthOf h k (cutoffOf h μ)` on the
walls), `SmoothCoreDecomposition.coeff_congr`, ★★★ `BridgeInputs.coeff_congr_of_jets` (order `chartJetOrder i μ` on active
walls). In flight: Theorem B `SmoothRenormalisedStrata` (agent, tide/jets2): `renormFunctional`, `smoothCoeffAtDepth_mul_eq`,
family/decomposition level, `BridgeInputs.coeff_eq_renormSum`.
CDX `ShallowStratumRegression` LANDED (main 18c0fca, 722 modules): `xM_isEquivalent`, `no_finite_cornerJet_formula`.
★★★ THEOREM B LANDED: CDXI `SmoothRenormalisedStrata` (agent): `renormFunctional`, `smoothCoeff_mul_eq`, `renormFunctional_add_smul/_congr`,
`familyCoeff_mul_eq`, `BridgeInputs.coeff_eq_renormSum` (723 modules). §15 Theorems A, B and the counterexample regression DONE.
Remaining (Astra #122): Unit 3 finite-order `C^R` bound (continuity of the coefficient functional), Unit 6 global distributional
packaging (XL), Unit 7 ordinary-kernel specialisation under extra hypotheses; paper-facing remark on the finite-part reading of
eq:thm_coordfree; mirror paragraph.

## 16. PROJECT: Theorem C — the coefficient functional as a distribution (opened 2026-09-14; user: "proceed with this larger project"; consult #123 = design)
Astra #123 (`tide-log/gpt6_bigpicture_v123.md`): statement of record = (a) + Theorem B: for each `(μ,q)` the coefficient
functional `f ↦ coeff of ∫ prior·f·e^{−nK}` is an INTRINSIC, compactly supported distribution `T_{μ,q} ∈ 𝓓'(ℝ^d)` (Mathlib
`Distribution ⊤ ℝ ⊤`, smooth test functions; NO extension to `𝓓^{R}` — density of `C^∞_c` in `C^R_c` is not in Mathlib) with an
explicit finite-order estimate `|T f| ≤ C·M` for `JetBound R (coreImage X) f M` (`R = engineOrder X μ = max_P Σ_ℓ p_{P,ℓ}` the SUM
of the engine depths, NOT the max coordinate depth; `≤ max_i chartJetTotal i μ` by arithmetic), `dsupport T ⊆ wallImage X ∩ tsupport
prior ⊆ K⁻¹0 ∩ tsupport prior` (wall image `⋃ ψ_i(activeWalls i)` is COMPACT, so no continuity of `K` needed; Theorem A against
the zero observable; prior support by the scalar integral vanishing), intrinsicness (two bridge presentations of the same phase
and prior give the same distribution, by certificate uniqueness). Then (b) chart-face distributions `B_{P,J,a,μ,q}` on the
tangential Euclidean space (base × K-coordinates), support in the CLOSED face box, compact-support pairing with a cutoff (chart maps
need not be proper), `T(f) = Σ_{P,J,a} faceW·⟨B, ∂^a_J (f∘ψ∘T_P)|_{v_J=0}⟩` — PRESENTATION DATA (individual terms depend on
weights; only the sum is intrinsic; density-splitting lemma is the only checkable independence); NO carrier type (c), NO `Sym^r`
tensors. (d) `Z_n` as a distribution with the WEAK (test-function-wise) expansion; the seminorm-uniform remainder is a separate
L–XL unit needing a full quantitative audit (remainder depths, strict exponent margin for critical logs, tail ≤ prior·vol).
Units: C0a coefficient linearity (S–M) · C0b compact core/wall images, wall ⊆ zero set (S–M) · C0c `pdMulti` ↔ `iteratedFDeriv`
bridge `|pdMulti m l f x| ≤ ‖iteratedFDeriv ℝ (Σ m) f x‖` (M–L) · C1a `|smoothCoeffAtDepth F| ≤ coeffBoundConstant · M` for
`RectBound F p b M` with an EXPLICIT constant (absolute majorants; M–L) · C1b product `2^{Σp}`, LOCAL chain rule for `f∘ψ_i`
(ψ smooth only near the box), affine transfer (L) · C1c global `JetBound` estimate + order comparison (M–L) · C2 distribution
via `TestFunction.mkCLM`/`limitCLM` + `Seminorm` continuity, finite-order theorem (M) · C3 support + intrinsicness (S–M) · C4w
`Z_n` weak expansion (M) · C5a face factorisation + tangential bounds (L) · C5b face distributions, cutoff pairing,
presentation (L–XL) · C4s uniform remainder (L–XL) · C6 regression: finite part `F(u) = ∫_0^1 (u(x)−u(0))/x dx` — exists,
linear, `|F u| ≤ sup|u'|`, support `[0,1]`, NO order-0 bound (`F(u_ε) ≥ log(1/ε)`), `F(x^M) = 1/M` (M). First release boundary:
C2 + C3 + intrinsicness with Theorem B as the presentation. Non-claims: minimal order, `C^R` extension, resolved manifold,
intrinsic per-stratum tensors, measure coefficients, chart-transition compatibility, strong-topology expansion.
Execution 2026-09-14: agents on C0c (`tide/c0c`), C1a (`tide/c1a`), C6 (`tide/c6`); C0a/C0b/C1b/C1c/C2/C3 in `tide/smooth`.
### 16.1 Status 2026-09-14 — FIRST RELEASE BOUNDARY REACHED (C2 + C3 + intrinsicness)
Landed (all axiom-clean, gated): CDXII `CoordinateFrechetBridge` (C0c: `pdMulti_eq_iteratedFDeriv`, `abs_pdMulti_le_norm_iteratedFDeriv`,
`rectBound_of_jetBound`, local chain rule `exists_chart_jet_bound`; agent) · CDXIII `SmoothCoeffBound` (C1a: `coeffBoundConstant`,
`abs_smoothCoeff_le`, `abs_familyCoeff_le_const_beta`; agent) · CDXIV `FinitePartRegression` (C6: `finitePart`, `abs_finitePart_le`,
`no_order_zero_bound`, `finitePart_pow`; agent) · CDXV `SmoothObservableCoeff` (C0a/C0b/C3: `observableCoeff`, `_add/_smul/_zero`,
`observableCoeff_eq_of_eq`, `coreImage`/`wallImage` compact, `wallImage_subset_zeroSet`, `observableCoeff_eq_zero_of_tsupport_subset`,
`_of_disjoint_prior`) · CDXVI `SmoothCoeffJetBound` (C1b/C1c: `RectBound.mul`, `engineOrder`, `engineOrder_le_chartJetTotal`,
`rectBound_obsfam`, `abs_coeff_le`, `abs_observableCoeff_le`) · CDXVII `SmoothCoeffDistribution` (C2/C3/C4w: `Distribution.ofJetBound`,
`coeffDistribution : 𝓓'(ℝ^d,ℝ)`, `coeffDistribution_bound`, `coeffDistribution_eq_of_eq`, `dsupport_coeffDistribution_subset(_zeroSet)`,
`isCompact_dsupport_coeffDistribution`, `hasSmoothCoordFreeExpansion_partitionObs`). 729 modules. Mirror paragraph appended.
Remaining: C5a/C5b chart-face distributions and the pairing presentation (L–XL); C4s seminorm-uniform remainder / `Z_n` as a
distribution (L–XL); paper-facing wording. Next: consult #124 audit of the release boundary + C5 design.
### 16.2 Consult #124 (2026-09-14): AUDIT of the release boundary — PASSED; C5 design
Astra #124 (`tide-log/gpt6_bigpicture_v124.md`): the first release boundary is reached (intrinsic coefficient distribution on
the original space, concrete finite-order estimate, compact support, wall-image support theorem, testwise expansion; Theorem B =
chart-face presentation). Qualifications: `{K = 0}` need not be closed for measurable `K` (containment is fine; "vanishes on the open
complement" needs open subsets of `{K ≠ 0}`); `engineOrder` is a presentation-dependent UPPER bound, not the order; `Ω = ⊤` only;
`commonQ/commonD` are admissible presentation lattice data. Cheap additions: (A) `coeffDistribution = 0` off the lattice / above the
log degree (from `coeff_support`, keep `d = 0` honest); (B) `coeffLinearMap` alias; (C) `IsVanishingOn` on open `U ⊆ {K ≠ 0}`;
`Zdist X N (hN : 0 ≤ N) : 𝓓'(Ω,ℝ)` (order 0, `|Z_N f| ≤ (∫ prior)·M`, support ⊆ tsupport prior, `Zdist_eq_of_eq`) — land now (S);
C4w restated via `Zdist_apply`. NOT cheap: order-0 of the top log coefficient (needs leading exponent/multiplicity identification).
C5 design: `FaceSpace P J := BaseSpace P × (Tangential P J → ℝ)` (ambient Euclidean, `faceBox` compact = baseBox × [0,b]^K); face
factorisation as an OPERATOR IDENTITY `remList p (lK J) F (glue J 0 w) = remList p_K (finRange K) (F ∘ glue J 0) w` (C5a, first
unit, independent); tangential density `H_{s,m,a} = ∂^{m−a}_J ρ_{P,s} ∘ glue J 0`; `faceFunctional P J a μ q : SmoothFace →ₗ ℝ`
(no topology; `faceW J a` kept OUTSIDE) with density-splitting identity `= ∫_s renormFunctional (ρfam P s) … (u(s, ·) ∘ proj) dν`;
tangential order `R_{P,J} = Σ_{k∈K} p_k`, anisotropic `TangentialJetBound` (no base derivatives); `faceDistribution :
𝓓'(FaceSpace)` by restriction; support via `u =ᶠ[𝓝ˢ faceBox] 0 → B u = 0` (NOT "integral over the box": remList has Taylor
subtraction terms); face-jet REPRESENTATIVES (chart pullback smooth only near the box: use `obsExt`/cutoff, prove independence);
reconstruction `coeffDistribution X μ q f = Σ_{P,J,a} faceW J a * faceFunctional … (faceJet X P J a f)` from Theorem B on
`X.withObs f`; regrouping `|a| = r` optional, `1/r!` tensor normalisation OUT of scope. Units: C5a restriction/remList algebra (M) ·
C5b face geometry, joint→tangential jet bound (S–M) · C5c functional, integrability, linearity, density splitting (M) · C5d tangential
bound, distribution constructor, support (M) · C5e face-jet representatives, independence, reconstruction (M) · C5f regrouping (S).
C4s after C5: `JetBound`-uniform remainder `|Zdist N f − S_A(N,f)| ≤ C·M·N^{−A}(log N)^L` for `N ≥ N₀ ≥ 2`; little-o via `A' > A`
plus the finite band `S_{A'} − S_A` (all log powers at each `μ ≤ A`); `remainderOrder X L := sup_P Σ_j remainderDepth`.
Execution: agents C5a (`tide/c5a`), C5d-generic (`tide/c5d`: compact-set smooth functional → distribution, tangential jet bounds);
Zdist + cheap additions in `tide/smooth`; then C5c/C5e.
### 16.3 Status 2026-09-14 — C5 in progress
Landed: CDXIX `ProductJetDistribution` (agent; general-`E` `Distribution.ofJetBoundOn`, slices `norm_iteratedFDeriv_slice_le`,
`TangentialJetBound`, `Distribution.ofTangentialJetBound`, compact support from neighbourhood vanishing) · CDXX
`SmoothPartitionDistribution` (`Zdist`, lattice/degree vanishing, `isVanishingOn_of_subset_nonzero`, `coeffLinearMap`) · CDXXII
`SmoothFaceDistribution` (algebraic C5c/C5e: `face`, `pdMulti_lK_eqOn_face`, `renormFunctional_eqOn_face` (face factorisation via
`renormFunctional_congr` — no operator identity needed), `projK`, `cyl`, `FaceSpace`, `faceJet` + `contDiff_faceJet`, `faceFunctional`,
★★★ `coeff_eq_sum_faceFunctional`, `coeffDistribution_eq_sum_faceFunctional`). In flight: C5a `FaceRestrictionOperators` (agent,
`tide/c5a`; ι-generalised operators, restriction identities — now optional for the reconstruction, still useful for the tangential
bound) and C5g `ParametricCoordinateDerivative` (agent, `tide/c5g`; `pdMulti_slice_eq_iteratedFDeriv`, joint continuity,
`SmoothAmplitudeFamily.ofSlice`) — needed for the analytic part: integrability of `s ↦ renormFunctional … (cyl u s)` ⇒ linearity of
`faceFunctional`; tangential finite-order bound ⇒ `faceDistribution : 𝓓'(PieceFaceSpace)` with support in the closed face box.
### 16.4 Status 2026-09-14 — C5 COMPLETE (chart-face form of Theorem C)
Landed: CDXVIII `FaceRestrictionOperators` (agent; ι-operators, `faceAmp_eq_remListι`, `norm_iteratedFDeriv_faceRes_le`) · CDXXI
`ParametricCoordinateDerivative` (agent; `pdMulti_slice_eq_iteratedFDeriv`, `continuous_pdMulti_slice`, `SmoothAmplitudeFamily.ofSlice`) ·
CDXXIII `SmoothFaceFunctionalBound` (`abs_renormFunctional_le`, `renormConst`) · CDXXIV `SmoothFaceDistributionAnalytic` (linearity via
`cylFam`/`continuous_renormFunctional_cyl`; tangential bound `abs_faceFunctional_le` with `faceOrder = Σ pieceDepth`, `rectBound_cyl`;
locality; ★★★ `faceDistribution : 𝓓'(PieceFaceSpace)`, bound, `dsupport ⊆ faceBox`, compact). Together with CDXXII's reconstruction:
`T_{μ,q}(f) = Σ_{P,J,a} faceW J a · 𝓑_{P,J,a}(faceJet f)`. Name clashes between concurrent agent modules (`projK`, `faceRes`,
`contDiff_slice`) resolved by renaming (`tangProj`, `faceResFam`, `contDiff_sliceFin`). Remaining from #124: C5f regrouping (optional),
C4s uniform remainder (L–XL), paper-facing wording; consult #125 audit of C5.
### 16.5 Consult #125 (2026-09-14): AUDIT of C5 — PASSED; CLOSE after a small interface tidy-up
Astra #125 (`tide-log/gpt6_bigpicture_v125.md`): C5 realises the chart-face design (termwise reconstruction from fixed functionals
independent of the observable; ambient base space fine; `faceOrder` an upper bound; smooth pairing vs test-function pairing correct
but the bridge should be exposed; `obsExt` dependence = presentation choice until an invariance theorem is stated). Tidy-up (all S):
(A) smooth neighbourhood-congruence of `faceFunctional` (from linearity + locality); (B) cutoff pairing identity `faceFunctional u =
faceDistribution (χ·u)` for a smooth `χ = 1` near `faceBox`, cutoff independence; (C) extension independence via the closed-box jet
lemma (`pdMulti_eqOn_centeredBox`; face-value agreement alone is NOT enough — normal jets); (D) a documentation block. C4s: cheaper
now but not automatically M — the missing audit is the REMAINDER proof's uniformity (one depth, one jet order, one compact set, `f`-free
constants and threshold); recommendation: STOP, reopen only if the paper needs a distribution-topology expansion; C5f not required.
Non-claims for the closure record: no seminorm-uniform remainder; no canonical intrinsic stratification or chart-independent summands;
no minimal tangential order / minimal jet representation / uniqueness of the face decomposition; no base-density regularity from the
absence of base derivatives; `faceJetObs f` not compactly supported; no arbitrary representative independence beyond what is proved;
support statements are inclusions; no single finite face-jet list for all coefficients. Mirror: Astra's eight-sentence chart-face paragraph.
### 16.6 CLOSURE 2026-09-14 — THEOREM C PROJECT CLOSED (Astra #125 tidy-up done)
CDXXV `SmoothFaceDistributionClosure`: neighbourhood congruence, closed-box congruence, extension independence
(`faceFunctional_faceJetOf_eq`), cutoff pairing (`faceFunctional_eq_faceDistribution_mulCutoff`, `exists_cutoff_faceBox`), and
`coeffDistribution_eq_sum_faceDistribution` (pairing of compactly supported face distributions with normal jets, cutoff-independent).
737 modules. Not done (recorded non-claims): C4s uniform remainder; C5f regrouping; minimal orders; canonical stratification.
### 16.7 C4s DONE 2026-09-14 (user: "just get the distribution thing done")
CDXXVI `SmoothUniformRemainder`: `smooth_expansion_at_depth_linear`, `smooth_uniform_cutoff_linear`, `family_uniform_cutoff_linear`,
`absSpectralSum_eq_of_dvd/_of_le/_finset_sum`, `exp_neg_mul_le_rpow_profile`, bridge piece data at a cutoff (`remDepth`, `remOrder`,
`chartConstL`, `densityBoundL`, `rectBound_mul_rem`, `chartInt_eq_mul`, `familyCoeff_amp_eq_mul`, `abs_tailInt_le`), ★★★
`uniform_remainder_cutoff`, `uniform_remainder_spectrumLe` (explicit gap `latticeGap`), `uniform_remainder_Zdist`. Astra's five-point
audit satisfied: one depth (`remDepth`), one jet order (`remOrder`), one compact set (`coreImage ∪ tsupport prior`), `f`-free constants,
threshold `N ≥ 1`; little-o via truncation at `cutoffExponent A` plus the finite band (all log powers at each `μ ≤ A`). The theorem is
proved for the bridge's own observable (`uniform_remainder_cutoff_aux`) and instantiated at `X.withObs f` — this avoids mixed-type rewrites.
Open (not planned): the statement in Mathlib's compact-convergence topology on `𝓓'`. 738 modules.

## 17. PROJECT: Theorem D — the coefficient distributions on the RESOLVED manifold and their stratification (opened 2026-09-14; user: "let's proceed with this"; consult #126 = design)
Motivation (user): Theorem C on `W` is sensible but the interesting content is the expression in terms of resolution data and the
stratification. Finding: the carrier exists upstream — hironaka's `WatanabeModificationOn K W` carries the resolved manifold `R.U`
(Mathlib `AnalyticManifold`), the proper analytic blow-down `g`, iso off the zero set, Watanabe charts of the maximal atlas
(`EvenChartBox`), and the bridge proof builds cutoffs and cores ON `R.U` before pushing to `W`. Plan: a resolved transport keeping
`U`; the U-integral `Z_n[F] = ∫_U F e^{−nK∘g} dμ_U` with `Z_n[φ∘g] = Z_n[φ]`; `𝒯_{μ,q}` on smooth functions on `U`, canonical by
uniqueness, supported on the divisor; local-depth stratification; support filtration, ordinary kernels on open strata, top-log
measures. Design consult #126 (`tide-log/prompt_bigpicture_v126.md`).
### 17.1 Consult #126 design (2026-09-14)
Three levels: (1) intrinsic coefficient functional on the FIXED measured resolution `(U, π = R.gv, μ_U)`; (2) intrinsic
normal-crossing depth/resonance filtration from a chart-invariance lemma; (3) smooth stratum-kernel presentations of RESTRICTIONS —
NOT a canonical splitting into per-stratum summands (finite-part extension across deeper strata is ambiguous by terms supported
there). Corrections: the highest log coefficient at an arbitrary exponent is NOT a measure (1-D: `n^{-3/2}` coefficient is `δ''`);
only the globally first nonzero term (smallest exponent, highest log) is a positive order-0 measure (positivity argument); candidate
exponents are UNIONS of the branch lattices `L_j = {(h_j+1+m)/(2k_j)}`, multiple poles from COINCIDENCES `2k_j μ = h_j+1+m_j`, not sums.
D0 (hironaka): off-divisor subtype homeomorphism `e : {P // K(gv P) ≠ 0} ≃ₜ {x : W // K x ≠ 0}`; canonical `μ_U := incl_* (e⁻¹_* ν^×)`
(ν = prior·vol restricted off the zero set); `μ_U D = 0`, `μ_U.map gv = priorMeasure`, concentration on `gv⁻¹(supp prior)` (compact);
uniqueness of null-divisor lifts `η D = 0 → ξ D = 0 → η.map gv = ξ.map gv → η = ξ`; integral identity `Z^U_t[f∘π] = ∫ f e^{−tK} prior`.
D1: lift cores (`(coreSource_i).map φ_i.symm` via SUBTYPE maps on the core box) and tail (`tail_W.map e⁻¹`, off the zero set by the
gap), `∑ coreU + tailU = μ_U` by the uniqueness of lifts; structure `ResolvedCoreTransport` (minimal interface for grammar).
D2–D3 (grammar): `𝒯^R_{μ,q}` a linear functional on smooth functions on `U` with a compact finite-chart jet estimate (NOT an
overlap-compatible chart family first); certificate for `t ↦ Z^U_t[F]`, intrinsic by `coeff_eq`; `𝒯(f∘π) = coeffDistribution f`;
support in `D ∩ π⁻¹(supp prior)`; uniform remainder. D4 (L, standalone): local wall correspondence — two monomial-unit descriptions
of the same phase and Jacobian determinant at `P` under a local diffeo `H` give `σ : J ≃ J'` with `k = k'∘σ`, `h = h'∘σ`, matching
tangent hyperplanes (leading homogeneous terms / restriction to lines; no irreducible decomposition). D5: `d_D(P) = |J(P)|`,
`D_{≥c}` closed, `S_c` locally closed smooth submanifold of codim `c`, `U_c := U ∖ D_{≥c+1}` open; resonant count
`r_μ(P) = #{j ∈ J(P) : μ ∈ L_j}`. D6: `supp 𝒯_{μ,q} ⊆ C ∩ {r_μ ≥ q+1} ⊆ D_{≥q+1}` (necessary conditions; localise + uniqueness).
D7: on `U_c`, a functional supported on `D_{≥c}` is a finite transverse differential operator applied to smooth densities on `S_c`
(adapted coordinates; `B_a` coordinate-dependent, the transverse-order filtration intrinsic); automatic case `𝒯_{μ,q}|_{U_{q+1}}`.
D8: the globally leading coefficient is a positive Radon measure (`|𝒯(F)| ≤ C sup|F|` by positivity); explicit leading density under
sufficient conditions. Regression: quadrant `x²y²`: off the corner `T_{1/2,0}(u) = (√π/2)∫_0^1 u(x,0)/x dx` (+ vertical),
`T_{1/2,1} = (√π/4)δ_0`. Non-claims: no canonical per-stratum summands; `B_a` coordinate-dependent; no order 0 at higher exponents;
no global integrability up to deeper strata; no nonvanishing; no resolution-independence without comparison maps; no Whitney/global
components. Execution: D0 (me, hironaka clone, branch sector-atlas, fork only); D4 (agent, grammar worktree `tide/d4`).
### 17.2 Status after consult #127 (2026-09-14)
LANDED (all axiom-clean): D0 hironaka `ResolvedMeasure` (Borel `R.U`; `liftMeasure` = off-divisor lift of any measure, divisor-null,
`π_*` = restriction to the regular locus, UNCONDITIONAL uniqueness `eq_liftMeasure_of_map_gv`; `resolvedMeasure := liftMeasure (prior·vol)`,
`π_* μ_U = prior·vol`, finite, carried by the compact `π⁻¹(supp prior)`, observable identity `∫_U f∘π e^{−tK∘π} dμ_U = ∫ f e^{−tK} prior`);
D1 hironaka `ResolvedCoreTransport` (transport + resolution charts `φ i` of the maximal atlas, `V i = target`, `ψ i = π ∘ φ_i⁻¹`;
`coreU i = core_i.map φ_i⁻¹`, `tailU = liftMeasure tail`; `∑ coreU + tailU = μ_U` EXACTLY by uniqueness; `integral_resolvedMeasure_eq`;
`chartInv` measurable totalisation; `contDiffOn_comp_symm` (F∘φ⁻¹ smooth on the target for F ∈ C^∞(U)); `contMDiff_gv`;
existence from the bridge data `exists_evenChartData_of_modification` (bridge proof split)); fork rev `34cbdee3e`, grammar pin bumped.
D2 grammar `SmoothResolvedConsumer` (CDXXVIII): `ResolvedData` (F smooth on U), `μU`, `Z`, `D Y`, `decomp Y`, `hasSmoothCoordFreeExpansion`,
`coeff Ξ Y μ q = 𝒯^U_{μ,q}[F]`, `coeff_eq_of_transports` (intrinsic in Y for fixed R), `coeff_comp_gv` (= Theorem C on pull-backs).
D3 grammar `SmoothResolvedCoefficient` (CDXXIX): `coeff_add/smul/zero`, `zeroFibre = D ∩ π⁻¹(supp prior)` compact, `exists_phase_gap`,
`abs_Z_le_of_eventually_zero` (exponentially small), `coeff_eq_zero_of_eventually_zero`, `coeff_congr_of_eventuallyEq` (germ locality).
D4 grammar `NormalCrossingWallInvariance` (CDXXVII, agent): `MonomialForm`, `exists_wall_equiv`, `exponent_eq_of_unit_monomial_eq`,
`exists_wall_equiv_jac(_det)`, `card_eq_of_phase_eq`, `multiset_pairs_eq_of_phase_eq`.
Consult #127 (`gpt6_bigpicture_v127.md`): AUDIT — level (1) delivered as designed (domain C^∞(U) right; germ locality is the correct
support statement; do NOT say "depends only on F|_{Z₀}"); missing: continuity (chart-wise jet bound, unit D3b, M–L, independent, not
blocking D5), resolution-independence, stratum kernels. DESIGN level (2): D5a atlas-transition adapter (transition `H = φ'∘φ⁻¹` analytic
near 0 with inverse, phase equality, Jacobian chain rule) + `EvenChartBox.h_eq_zero_of_k_eq_zero` (inactive Jacobian exponents vanish:
at a point with u_j = 0, others ≠ 0, the phase is nonzero so the blow-down is a local iso there and det ≠ 0; via isoOff) + centred
comparison `pairData` equality (M–L); D5b `pairs P : Multiset (ℕ×ℕ)` on ALL of U (empty off D), `depth = card`, `Resonates μ (k,h) :=
∃ m, 2kμ = h+1+m`, `resonanceCount`, basic lemmas (S–M); D5c local formula `pairs Q = {(k_j,h_j) : j active, (φ Q)_j = 0}` for Q in the
source of ANY even chart (translate by u₀, D4 with general unit), closed `depthGE c`, `resonanceGE μ c`, open `shallowOpen c`, coordinate
description of the stratum in a centred chart; no bundled submanifold, no Whitney (M). D6 `resonantZeroFibre μ q := zeroFibre ∩
resonanceGE μ (q+1)`, target `coeff_eq_zero_of_eventually_zero_on_resonantZeroFibre`; GATE: inspect the engine for a LOCAL wall-supported
coefficient lemma (coefficient of (μ,q) vanishes when the amplitude vanishes near the set of points with ≥ q+1 resonant vanishing active
coordinates); chart-wide multiplicity bound alone is insufficient; partition of unity is NOT free (no subordinate-transport theorem).
D7 minimal: restrictions to `U_c` (q ≥ c ⇒ 0; q = c−1 supported on `Z₀ ∩ S_c ∩ {r_μ = c}`), kernels deferred (normal jets). D8a: define
leading at the FUNCTIONAL level (`IsLeadingFunctionalIndex μ₀ q₀`: some G with C ≠ 0, all preceding indices vanish for all G); normalised
limit `N^{μ₀}(log N)^{−q₀} Z_N[G] → C_{μ₀,q₀}(G)`; positivity `G ≥ 0 on L ⇒ C ≥ 0`; `|C(G)| ≤ M C(1)`; alternative hypothesis "leading
for Z_N[1]" implies it by domination; Riesz separate (M–L). Regression x²y² at D5 (depth/resonance counts), constants later.
Paper paragraph for level (1) in §C of the consult (nine sentences).
### 17.3 Level (2) progress (2026-09-14, after consult #127)
LANDED: D5a hironaka `ResolvedJacobian` (fork `a67aad4a7`: `isLocalDiffeomorphAt_gv` off the zero set via `isoOff` ∘ inclusion-of-`W`
partial diffeomorphism; `det_fderiv_rep_ne_zero`; `h_eq_zero_of_k_eq_zero`; `prod_pow_h_eq_active`) + grammar `ResolvedDepth` (CDXXX:
`pairData`, `monomialForm` (unit 1), transition analyticity, Jacobian chain rule, `pairData_eq_of_centered`; `divisor`, `pairs R hK0 P`,
`depth`, `Resonates`, `resonanceCount`, `pairs_eq_pairData`, `depth_pos_iff`, …); D5c grammar `ResolvedDepthLocal` (CDXXXI:
`pairs_eq_of_mem_source` local formula via `translatedForm` (D4 with unit), sub-multiset monotonicity, `isClosed_depthGE`,
`isClosed_resonanceGE`, `isOpen_shallowOpen`, `depthGE_one`, `depthGE_succ_dim`, `mem_depthGE_iff_of_centered`); D8a grammar
`SmoothLeadingTerm` + `SmoothResolvedLeading` (CDXXXII: `tendsto_normalised_of_leading`, `IsLeadingIndex` (functional level),
`tendsto_normalised_Z`, `coeff_nonneg_of_leading`, `abs_coeff_le_of_leading`). Main `a2c47f8`, 745 modules.
D6 GATE RESULT: the engine's face coefficients `faceCoef = faceMonoCoeff = boxCoeff (spectral coefficients of the old engine)` have only
the lattice support (`faceMonoCoeff_eq_zero_of_not_lattice`) and the coarse degree bound (`_of_lt`/`DJ`); the MULTIPLICITY bound
(log degree at (μ,q) ≤ #{i ∈ J : (e_i+1)/(2k_i) = μ} − 1) is NOT present → D6a is an engine dig into `boxCoeff`/`familySpectralCoeff`
(L). Deferred. Also needed for D6b: the chart amplitude `ρf · F∘φ⁻¹` vanishes near a face iff F vanishes near the face points in U OR
prior∘ψ vanishes near them; jets of the smooth EXTENSION at box-boundary face points vanish since it agrees with the vanishing function on a
full-dimensional wedge (Lean-painful); `Filter.eventually_nhdsSet_iff_forall` for pointwise-to-set. D7 minimal and D8 Riesz/Z₀-sup bound
not started. Regression x²y² (depth/resonance counts) not started.
### 17.4 D6 + D8 second theorem LANDED (2026-09-14). Main d820762, 749 modules.
D6a (agent, `SmoothResonantSupport`, CDXXXIII): the engine DID have the pole-multiplicity bound at the state-density level
(`stateDensityRep_coeffAt_eq_zero_of_le`: coeffAt vanishes at log degree ≥ `expMult`); the agent threaded it through
`coeffTerm → spectralCoeff → familySpectralCoeff → boxCoeff → faceMonoCoeff → faceCoef` with the honest multi-index tracking of the
monomial reps (`mul_support_ge`, `truncList_support_ge`, `scale_support_ge`, `monoFam_support_ge`), `resonantCount`, and the face
amplitude vanishing `faceAmp_eq_zero_of_jets_zero` (`JetsZeroOn`, `remList_eq_zero_of_jetsZeroOn`), giving
`smoothCoeff_eq_zero_of_resonant`. D6b geometric half (`SmoothResolvedResonant`): `pdMulti_eq_zero_of_eqOn_inter_closedBox` (jets at
box-boundary points are limits of interior jets — needed because the engine sees the smooth EXTENSION of the chart amplitude),
`faceResonant_le_resonanceCount` (via the local formula in the piece's even chart box `Y.evenChartBox` — hironaka D1 addendum
`phaseConst_eq_one`, fork `5a310bdba`), `Gloc_eventually_zero` (F vanishes near the divisor point, OR the point is off `supp prior` so
`prior ∘ ψ` vanishes near the chart point), `pdMulti_amp_eq_zero_on_face`. Assembly (`SmoothResolvedResonantSupport`, CDXXXV):
`coeff_eq_zero_of_eventually_zero_resonant`, `coeff_congr_of_eventuallyEq_resonant`, `coeff_eq_zero_of_eventually_zero_depth`,
`coeff_eq_zero_of_tsupport_subset_shallowOpen` (minimal D7). D8a second theorem (`SmoothResolvedLeadingOne`, CDXXXIV):
`isLeadingIndex_of_one` by domination + first-nonzero-index extraction from the finite certified spectrum.
Remaining from #127: D3b chart-wise jet bound on U (continuity of 𝒯^U), D7 kernels (deferred: normal jets), D8b Riesz / sup over Z₀ bound,
regression x²y² (needs a `WatanabeModificationOn` for x²y² — construct charts at all zero points; M). Next: consult #128 audit of level (2).
### 17.5 Consult #128 (2026-09-14): CLOSE level (2) as the resolved geometric + germ-locality layer. Wording corrections for the paper:
"closed SUPERLEVEL sets" (exact strata only locally closed), "chart-independent on a FIXED modification" (not resolution-independent),
"germ-local coefficient FUNCTIONALS" (not distributions until D3b), "CONDITIONAL leading-index results" (no RLCT identification). Resonance
convention confirmed (Mellin denominator h+m+1−2kμ). Add the contrapositive corollary `𝒯 ≠ 0 → S_{μ,q} ∩ tsupport F ≠ ∅`. Ranked follow-ups:
(1) leading sup bound over S_{μ₀,q₀} via SMOOTH SATURATION θ∘G (θ = id near G(S), |θ| ≤ M) + germ congruence + existing bound, M ↓ sup
(S–M, try first); (2) D3b chart-wise seminorm bound ⇒ continuity (if the paper says "distribution"); (3) scalar coefficient independence
across modifications for PULL-BACK observables (uniqueness of expansions; cheap corollary to check); (4) Riesz (after the sup bound;
density/extension interface is the cost); (5) RLCT bridge: nonvanishing of the leading coefficient of Z_N[1] via a POSITIVE BOX LOWER
BOUND `Z_N[1] ≥ c N^{−λ*}(log N)^{m*−1}` at a point with positive prior realising the extremal pair (new lemma); (6) x²y² local-data
regressions without a global modification; D7 kernels and common-refinement comparison DEFERRED. Paper paragraph (ten sentences) in §C.

### 17.6 D3b LANDED (2026-09-14). Main 9f5f74b, 751 modules.
CDXXXVII `SmoothResolvedJetBound`: `abs_coeff_le_of_chartJetBound : ChartJetBound Y (engineOrder μ) M → |𝒯^U_{μ,q}[F]| ≤ jetConstU μ q * M`,
`ChartJetBound R M := ∀ i, JetBound R (centeredBox d (a i)) (F ∘ chartInv i) M`. Proof = Theorem C's CDXVI with `F ∘ chartInv i` in place of
`obs ∘ ψ i` (`obsExtU` smooth extension off the box, `obsfamU` affine family, `amp_eq_mul`, `rectBound_obsfamU` via
`abs_pdMulti_comp_affineMap_finRange` + `pdMulti_eqOn_centeredBox` + `abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem`; no chartConst
since the hypothesis is stated in the resolution charts). Built first try. Consult #128 follow-ups (1)+(2) DONE; the coefficient
functionals may now be called "distributions of finite order on U (chart-wise)". Mirror: sentence + pin 9f5f74b (local commit, unpushed).
Remaining optional: (3) scalar independence across modifications for pull-backs, (4) Riesz, (5) RLCT nonvanishing via positive box lower
bound, (6) x²y² regression; D7 kernels / common refinement DEFERRED.

### 17.7 Follow-ups (3) and (5) LANDED (2026-09-14). Main a40ab1f, 755 modules.
CDXXXVIII `SmoothResolvedModificationIndependence`: `coeff_comp_gv_eq_of_modifications` (same K, prior; any two modifications; pull-back
observables agree), `coeff_eq_of_Z_eventuallyEq` (uniqueness across resolved data), `coeff_one_eq_of_modifications`,
`isLeadingIndexOne_iff_of_modifications`. CDXXXIX `SmoothResolvedRLCTIndex`: `IsExtremalData lam m` (2kλ* ≤ h+1 on all walls of Z₀;
resonanceCount λ* ≤ m*), `resonantZeroFibre_eq_empty_of_precedes`, `coeff_eq_zero_of_precedes` (ALL observables), `isLeadingIndex_of_extremalData`
(unconditional leading index), `tendsto_normalised_Z_of_extremalData`, `coeff_nonneg_of_extremalData`. CDXL `MonomialBoxLowerBound`:
`exists_tendsto_monoBoxIntegral` (inactive coordinates split off by Fubini along piEquivPiSubtypeProd; relabel; `boxIntegralGen_isEquivalent_general`).
CDXLI `SmoothResolvedRLCTPositive`: `coeff_one_pos_of_realised` (realised extremal pair, prior > 0 at π P₀ ⇒ 0 < 𝒯^U_{λ*,m*−1}[1]) via
`integral_image_orthant` (Mathlib `integral_image_eq_integral_abs_det_fderiv_smul` on the orthant box of the even chart at P₀, injectivity from
`injOn_offZero`), `exists_orthant_bound`, `Z_one_ge_mul_monoBoxIntegral`, `resonanceCount_eq_card_of_centered`; `isLeadingIndexOne_of_realised`.
⇒ the RLCT identification on U: Z_N[1] ~ c N^{−λ*}(log N)^{m*−1}, c > 0, (λ*, m*) = extremal pair of the intrinsic wall data.
Lessons: HO-unification failures — pass `g`/`f g` explicitly to `integral_image_orthant`/`integral_prod_mul`; `Tendsto`-typed `have`s
need `(G := …)` for `contMDiff_const`; anonymous constructor into `{u | p u ∧ q u}` needs the subset statement typed first;
`ae_restrict_of_forall_mem` goals need `beta_reduce`; `Finset.mem_val` is an Eq (rw, not .2). Mirror pin a40ab1f (local, unpushed; 6 ahead).
Remaining optional: (4) Riesz; (6) x²y² regression; realisation of the extremal pair on a compact zero fibre (semicontinuity of pairs);
D7 kernels / common refinement DEFERRED.

### 17.8 CONSULT #129 (2026-09-14): THEOREM D CLOSED. Main 3d7d6ff, 757 modules.
Landed after #128: CDXXXVII D3b chart-wise jet bound; CDXXXVIII modification independence on pull-backs; CDXXXIX extremal pair ⇒ leading
index (all observables); CDXL monomial orthant-box asymptotics; CDXLI positivity at a realised pair; CDXLII realisation on a compact zero
fibre; CDXLIII packaging: `rlct_asymptotic_of_realised` / `exists_rlct_asymptotic` (∫ prior e^{−NK} ∼ c N^{−λ*}(log N)^{m*−1}, c > 0).
Astra #129 audit: route sufficient (one orthant suffices; no upper comparison needed); wording: "finite-order chart-seminorm estimates"
(not "distributions chart-wise"); extremal ≠ attained (isExtremalData_zero is the warning label; "candidate leading index" for general
extremal data); the REALISER version is primary (uniform positivity on the zero set excludes ordinary cutoffs, e.g. K = x² with a bump);
"RLCT in the Laplace-asymptotic sense; zeta-pole identification not formalised" (pole at −λ* of order m* for ζ = ∫ K^z prior);
c is identified as the positive unit coefficient (no explicit local formula); common leading SCALE for all observables, not a nonzero
leading term for each. Modification independence + positive leading asymptotic on both ⇒ (λ*, m*) is an invariant of (K, prior).
Optional after closure (ranked): x²y² local regression (S), Riesz on the compact resonant fibre (M), zeta-pole identification (M–L),
D7 common refinement (L). Paper paragraph in gpt6_bigpicture_v129.md §B (adopted in the mirror).

## 18. PROJECT: Theorem E — graded stratum formulas for the resolved coefficient functionals (opened 2026-09-15; user: "proceed with this kernel project"; consult #130 = design)
Design (Astra #130, adopted): NOT chosen-kernel calculus, NOT zeta regularisation. Graded formulation: 𝓘_c := {F = 0 near D_c := Z₀ ∩ depthGE c};
𝒯^U_{μ,c−1}|_{𝓘_{c+1}} is canonical and descends to 𝓘_{c+1}/𝓘_c. On 𝓘_{c+1}, 𝒯^U_{μ,c−1}[F] = Σ over size-c faces J with ALL walls
resonant (2k_jμ = h_j+1+α_j, α_j ∈ ℕ unique) of Γ(μ)β^{−μ}/((c−1)! ∏_j 2k_j α_j!) · ∫_{(0,b]^{Jᶜ}} (∂_J^α A)(0_J,w) ∏_{i∉J} w_i^{h_i−2k_iμ} dw,
A = ω|b|·prior∘π·F the WHOLE amplitude (Leibniz: normal derivatives of F up to α). Correction: faceCoef ≠ 0 at the TOP log j = |J|−1
forces full resonance (not for lower j: x²y² with amplitude y² has both exponents 1/2 and 3/2). Units: E0 resonance semantics (S);
E1a remList = self when K-jets vanish on complementary hyperplanes (M); E1b faceMonoCoeff_top = Γ(μ)β^{−μ}∏(2k_j)^{−1}/(c−1)!,
box-length independent (M); E1c integrability/collar of the unremaindered weighted face integrand (M); E1d engine collapse at (μ,c−1) (M);
E2 resolved chart-piece definition + equality + exact-stratum interpretation (face point with u_J = 0, complementary active ≠ 0 lies in
{depth = c, r_μ = c}) (L); E3 zero-order positivity + values-only (M); E4 Euclidean pullback + paper paragraph (S). Names: "graded
stratum formulas", density = "local top Mellin-residue weight along the stratum" (residual phase factor after removing the normal monomial,
raised to −μ; NOT (K∘π|_S)^{−μ}); lower log powers = "convergent Taylor-subtracted chart-face formulas" (not divergent, not canonical per
stratum). Vanishing-near is the hypothesis; flatness a non-claim. Paper statement in gpt6_bigpicture_v130.md §10.

### 18.1 THEOREM E UNITS E0–E4 LANDED (2026-09-15). Main b370f6d, 765 modules.
CDXLIV `SmoothExactResonance` (E0: `exactCount`, exact-support vanishing chain, `faceCoef_top_eq_zero_of_not_exact`, `taylorOrder_unique`);
CDXLV `SmoothRemainderIdentity` (E1a: `remList_eq_self_of_jetsZeroOn`); CDXLVI `SmoothFaceSumCollapse` (E1d: `deepSet`, `resOrder`,
`smoothCoeff_eq_faceSum_top`); CDXLVII `SmoothFaceMonoTop` (E1b: `faceMonoCoeff_top = Γ(μ)β^{−μ}/((|ι|−1)!∏2k)`, via two-regime ⇒
CutoffExpansion ⇒ `tendsto_normalised_of_leading` + `monomialBoxRealCutoff_equal_isEquivalent`); CDXLVIII `SmoothResolvedStratumFormula`
(E2: `deepZeroFibre`, `jetsZeroOn_amp_deep`, `pieceStratumSum`, `stratumSum`, `coeff_eq_stratumSum`, `wallsAt_facePt_eq`, `depth_divPt_eq`,
`resonanceCount_divPt_eq`); CDXLIX `SmoothResolvedStratumPositive` (E3: `exactStratum`, `ZeroOrder`, `stratum_or_jets_zero`,
`coeff_nonneg_of_deep`, `coeff_eq_of_eqOn_exactStratum`); CDL `SmoothResolvedStratumEuclidean` (E4: `observableCoeff_eq_zero_of_eventually_zero_image`,
`observableCoeff_eq_stratumSum`, `_nonneg_of_deep`, `_eq_of_eqOn_image`); CDLI `SmoothStratumIntegrable` (E1c: collar + `integrable_faceCoeff`,
`integrableOn_pieceStratum_integrand`). Mirror: Theorem E paragraph appended (pin to bump to b370f6d). Lessons: existing
`pdMulti_lJ_eq_finRange` name clash (different signature) → suffix `_of_zero_off`; `ae_restrict_of_forall_mem` / `setIntegral_nonneg`
goals arrive as beta-redexes → `beta_reduce`; `Finset.mem_val` is an Eq (rw); `pow_le_pow_left` → `pow_le_pow_left₀`;
`isOpen_setOf_eventually_nhds` → `isOpen_setOfPred_eventually_nhds`; images `(fun w => f w) '' B` leave beta-redexes — use `f '' B`.
Next: consult #131 (audit + closure of Theorem E).

### 18.2 CONSULT #131 (2026-09-15): THEOREM E CLOSED. Main f923221, 766 modules.
Audit: constant Γ(μ)β^{−μ}/((c−1)!∏_{j∈J}(2k_j)α_j!) = faceW · faceCoef_top ✓; exact-support cutoff indexing ✓. Wording: "finite localized
chart-face representation on the exact stratum" (summed coefficient is the invariant; no intrinsic normal-derivative density), derivatives of
the WHOLE localized amplitude, "absolutely convergent complementary-face integrals" (joint base/face integrability = the engine family
integral, not restated), "nonnegative" not strictly positive, ZeroOrder on the whole exact stratum, neighbourhood vanishing not flatness,
Radon-measure interpretation on U ∖ deepZeroFibre is the standard consequence (not a landed construction), no finite extension across
deeper strata. Corollary (1) landed: CDLII `zeroOrder_of_extremalData` (extremality ⇒ n = 0 for resonant walls), `coeff_nonneg_of_deep_extremal`,
`coeff_eq_of_eqOn_exactStratum_extremal`; m* bounds the resonance count not the depth, so the restriction to observables vanishing near
the depth-≥ c+1 fibre is NOT vacuous. Optional after closure (ranked): x²y² regression through the graded formula (needs an identity
modification constructor in hironaka), explicit lower-log Taylor-subtracted formulas (API packaging), flatness extension (M).
Mirror: Theorem E paragraph revised per §C, pinned f923221 (local master 11 ahead of Overleaf; push user-side).

### 18.3 RESIDUE PROGRAMME (2026-09-15; user: "the phrasing in terms of Poincaré residues is beautiful and should be centered going forward … Proceed with 1-3"; consult #132 = design). Main 86bbdb5, 770 modules.
Item 1 (pole orders, residue weight, residue-sum restatement) landed as CDLIII `SmoothResolvedResidue`: `poleOrder k h μ = 2kμ−h`,
`resonates_iff_poleOrder`, `exactCount_eq_card_simplePole`, `residueWeight`, `dlogResidueInt` (∏(2k_j)⁻¹ · ∫ A·∏w^h(∏w^{2k})^{−μ} over the
face), `residueConst μ c = Γ(μ)/(c−1)!`, `faceTerm_eq_residue_of_simple`, `simpleFaces`, `residueSum`, `coeff_eq_residueSum`,
`observableCoeff_eq_residueSum`. Items 2–3 per Astra #132 (adopt (3B): the residue is a MEASURE defined from the coefficient functional;
defer log-form calculus and zeta continuation): units 1–3 = CDLIV `SmoothStratumTest` (X := U ∖ D_{c+1} = `stratumOpen`, `IsTest`, `T`,
linearity/positivity/locality/monotonicity, local bound `abs_T_le`, cutoffs) + CDLV `SmoothStratumApprox` (extension by zero `ext`, fixed-
support uniform approximation `exists_approx` via `exists_contMDiffMap_forall_mem_convex_of_local_const`, Cauchy limit `Λ₀`,
`Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ`, `Λ_toCc`); units 4–10 = CDLVI `SmoothStratumMeasure`: `stratumMeasure := RealRMK.rieszMeasure Λ` (Regular),
`integral_stratumMeasure_test`, `stratumMeasure_compl_exactStratum` (inner regularity + cutoffs supported in the open set
X ∖ S^μ_c, which is open because within X the exact stratum is cut out by the closed depth/resonance filtrations,
`stratumOpen_inter_exactStratum`), `coeff_withF_eq_integral_stratumMeasure` (F ∈ 𝓘_{c+1} not nec. compactly supported in X: cutoff = 1 on
Z₀ ∖ O, values-only dependence, a.e. equality), `observableCoeff_eq_integral_stratumMeasure`, `integral_stratumMeasure_eq_residueSum`,
`residueMeasure := ofReal((c−1)!/Γ(μ)) • ν`, `integral_residueMeasure_eq` (bare residue sum), `stratumMeasure_eq_of_transports`,
`eq_stratumMeasure_of_tests` (uniqueness among regular measures by smooth tests; fixed-support approximation +
`ext_of_integral_eq_on_compactlySupported`). Deferred (Astra ranking): measure on the subtype S, explicit chart-pushforward measure and
equality with Riesz (M–L), restricted log-density residue calculus (L), general log-form calculus / zeta continuation (L+).
Wording (Astra): "intrinsic positive Radon measure on U ∖ D_{c+1}, carried by the exact stratum; in normal-crossings coordinates
Γ(μ)/(c−1)! times the multiplicity-weighted logarithmic residue of the twisted prior density, normalised against d log(u_j^{2k_j})";
distinguish from the classical alternating-form Poincaré residue; avoid the unqualified equation ν = Γ/(c−1)!·Res unless Res is defined.

### 18.4 CONSULT #133 (2026-09-15): RESIDUE PROGRAMME CLOSED. Main 7c909a0, 771 modules.
Verdict CLOSE in the adopted measure-theoretic sense (3B). Four paper-level corrections applied to the mirror paragraph: state c ≥ 1 and μ > 0
(for ℛ); "intrinsic" = independent of the auxiliary transport data for the fixed resolved geometry and prior (NOT modification/resolution
independence); the logarithmic residue is the DENSITY-RESIDUE CONVENTION defined by the proved face-integral formula (each simple density pole
contributes (2k_j)⁻¹ = normalisation against d log(u_j^{2k_j}); chart and face multiplicities retained), not an independent residue calculus;
distinguish the normalised-limit coefficient (valid even if zero) from a nonzero leading asymptotic, and ν from ℛ (keep the Γ(λ*)/(m*−1)! factor).
"Carried by the exact stratum" ✓ (S^μ_c relatively closed in X, so supp_X ν ⊆ S^μ_c; no ambient-U support statement, no extension across
D_{c+1}). Representation on 𝓘_{c+1} = vanishing on a NEIGHBOURHOOD of D_{c+1} (not flat/finite order). API completion landed: explicit
`integrable_stratumMeasure`/`integrable_residueMeasure` (cutoff + a.e. equality). Extra unit CDLVII `SmoothStratumMeasureExtremal`:
`extremalStratumMeasure`, `tendsto_normalised_Z_extremal`, `tendsto_normalised_partitionObs_extremal`, `partitionObs_isEquivalent_extremal`
(nonzero coefficient required). Total mass: general ν can be infinite (x²y², μ=1/2, c=1: dy/|y| near the crossing); at extremal data
finiteness is plausible via a limsup bound on Z_1 + cutoffs + inner regularity, but equality with the unit coefficient needs "no leading mass
escaping to D_{m*+1}" — NOT claimed; never use ν.real univ as total mass without finiteness. Ranked follow-ups: (1) x²y² regression
(crossing multiplicities, Γ normalisation, infinite lower-stratum mass, finite leading atomic measure); (2) local positivity ∫f∘π dν > 0
(needs a local lower bound in charts; orthant lower bound plausible); (3) explicit chart-pushforward measure = ν (M–L); (4) measure on the
subtype S (repackaging); (5) zeta continuation (new programme). Mirror paragraph replaced by Astra's §(d) wording with dots, pin 7c909a0
(local master 13 ahead of Overleaf; push user-side).

### 18.5 Follow-ups (2) and mass finiteness LANDED (2026-09-15). Main fc4edd0, 773 modules.
CDLVIII `SmoothStratumMeasurePositive`: orthant lower bound with a nonnegative base observable (`Z_ge_mul_monoBoxIntegral`,
`exists_orthant_bound_obs`); `coeff_comp_gv_pos_of_realised`, `observableCoeff_pos_of_realised` (0 < C_{λ*,m*−1}(f) for f ≥ 0 positive at
π(P₀), P₀ a realiser with positive prior); `integral_extremalStratumMeasure_pos`; `partitionObs_isEquivalent_of_pos` (genuine ∼ with positive
constant). CDLIX `SmoothStratumMeasureFinite`: `coeff_le_coeff_one_of_extremalData` (monotone leading functional), `extremalStratumMeasure_univ_le`
(ν^{λ*}_{m*}(X) ≤ 𝒯[1]; IsFiniteMeasure + Regular instances), `extremalStratumMeasure_univ_eq_of_deep_empty` (mass = RLCT constant when
D_{m*+1} = ∅). Mirror sentences + pin fc4edd0 (local master 14 ahead). Artifact a142c13e rewritten with 5 diagrams (resolution, exponent ladders,
depth filtration, construction pipeline, x²y² density) — fixed a CSS rule that blew up MathJax SVG in captions. Remaining ranked: x²y² regression
(needs identity WatanabeModificationOn in hironaka: charts (x₀x₁, x₁−a) at axis points, maximal-atlas membership, plus a ResolvedCoreTransport
instance — L); explicit chart-pushforward measure = ν (M–L); subtype measure (S); zeta (L+).

### 18.6 MONOMIAL REGRESSION LANDED (2026-09-15). Main bffaf9e, 775 modules; hironaka fork cb11bc8d9 (pin bumped from 5a310bdba).
hironaka `Monomialize/Transport/MonomialModification.lean` (branch sector-atlas, fork only): `modelOn W`, `idMap W` (identity AnalyticMap),
`isAnalyticIsoOver_idMap`, `translation c` (OpenPartialHomeomorph), `stdChart`/`transChart P` (translated standard chart, in the maximal atlas via
`restrOpen_trans_mem_maximalAtlas`), `watanabeRep_idMap_transChart` (rep u = u + P), `monoPhase k = ∏ x_i^{2k_i}`, `activeExp k P`,
`exists_monomialChart` (AbsorbingChange on the translated chart: phase exactly ∏u^{2k'}, Jacobian unit·∏u^0, box in target),
`watanabeChartAt_monoPhase`, `WatanabeModificationOn.ofMonomial k W`, `exists_evenChartBox_ofMonomial` (E.k = activeExp, E.h = 0), `ofMonomial_gv`.
Grammar CDLX `MonomialResolvedData`: `monomialData`, `pairs_ofMonomial` (walls = active zero coords, pairs (k_i,0)), `depth_ofMonomial`,
`resonanceCount_ofMonomial`, `kmax`, `mstar`, `lamStar = 1/(2 kmax)`, `resonates_lamStar_iff` (⇔ k_i = kmax), `isExtremalData_monomial`,
`resonanceCount_monomial_zero` (origin realises m*), `monomial_rlct_asymptotic` (classical (min 1/(2k_i), #argmin) recovered; needs
`exists_resolvedCoreTransport_of_modification` for Y). CDLXI `MonomialStratumMeasure`: equal exponents κ: `deepZeroFibre_equal_eq_empty`
(depth ≤ d), `exactStratum_equal_subset` (= origin), `equalMeasure_compl_origin`, `equalMeasure_eq_smul_dirac` (ν^{λ*}_d = c·δ₀, c = 𝒯[1]),
`tendsto_normalised_partitionObs_equal` (every insertion: c·f(0)). Axiom probe clean. Not derived: explicit c = √π φ(0) for x²y² (CORRECTION: the earlier (√π/4)φ(0) counted ONE orthant sector; there are four)
(would need matching the abstract 𝒯[1] against the box-model asymptotic); depth-one measures ν^{1/2}_1 for x²y². Mirror pins bffaf9e/cb11bc8d9
(15 ahead of Overleaf). Lean gotchas: section `variable` hypotheses not mentioned in a statement need `include … in`; `{j | p j}` Finset notation
resists `simp only [Finset.mem_filter]` under binders — prove filter identities by `ext; rw [mem_filter]; by_cases`; `Finset.sup` attained via
`Finset.exists_mem_eq_sup`; `Multiset.map_congr rfl`; `measure_inter_add_sdiff` + `Set.sdiff_eq` for the singleton decomposition.

### 18.7 x²y² EXPLICIT CONSTANT LANDED (2026-09-15). Main 72f89d5 (merge of 7ba9aa9), 776 modules.
CDLXII `MonomialExplicitConstant`: `headline_symmetric_abs_phase_leading` (Headline XIX, zero phase, h=0, k=1, l=1/2, β=1) + `phaseCoeff_equal`
+ `phaseMoment_zero` + `Real.Gamma_one_half_eq`: four sectors × φ(0)√π/2, transport N ↦ √N (compose with `tendsto_rpow_atTop (1/2)`, `Real.sq_sqrt`,
`Real.log_sqrt`) halves the log ⇒ `x2y2_tendsto_headline : normalised (1/2) 1 (partitionObs (x²y²) φ 1) → √π φ(0)` (prior supported in symBox 2);
uniqueness against `tendsto_normalised_Z_of_extremalData` + `Z_one` ⇒ `x2y2_coeff_one_eq : 𝒯[1] = √π φ(0)`; `x2y2_measure_eq : ν^{1/2}_2 = √π φ(0) δ₀`;
`x2y2_tendsto_normalised : → √π φ(0) f(0)` for every smooth f. CORRECTION propagated everywhere: the constant is √π φ(0), NOT (√π/4)φ(0) (the
chart-face constant Γ(1/2)/(1!·2·2) is PER ORTHANT SECTOR; four sectors). Sanity: ∫ e^{−Mx²y²}dy = √π/(√M|x|), ∫_{1/√M<|x|<1} dx/|x| = log M.
Mirror pin 72f89d5 (17 ahead of Overleaf). Remaining: priors not supported in the symmetric box (scaling), depth-one measure ν^{1/2}_1 explicitly,
chart-pushforward = ν, subtype measure, zeta continuation. Consult #134 (audit + direction) launched.

### 18.8 CONSULT #134 (2026-09-15): follow-ups AUDITED. Wording: distinguish admissible extremal data from realised positive leading data;
equal-exponent exact stratum "contained in the origin" (membership needs 0 ∈ W ∩ supp); "need not satisfy"/"these results do not identify" for the
mass; do not mix the original-parameter (√π/4 per orthant) and square-parameter (√π/2 per orthant, then halve the log) explanations. Constants
CONFIRMED: ν^{1/2}_2 = √π φ(0) δ₀; ν^{1/2}_1 = √π(φ(x,0)dx/|x| + φ(0,y)dy/|y|) on the punctured axes (both normal sides; no tangential doubling).
Regression not circular (end-to-end; CDLXII adds an independent normalisation check). Box support: acceptable technical hypothesis; remove via scaling
x = tz, φ_t(z) = t²φ(tz), Z_φ(N) = Z_{φ_t}(t⁴N). NEXT (ranked): (1) mixed-monomial explicit constant for all smooth insertions — 𝒯[f] =
2^m Γ(λ)/((m−1)!∏_{J}2k_i) ∫ φ(0_J,z) f(0_J,z) ∏_{j∉J}|z_j|^{−2k_jλ} dz (positive-dimensional leading measure; via headline XIX at zero phase +
`phaseCoeff_zero_phase`/`amplitudeCoeff`; candidate (v) corrected: prior restricted to the subspace, 2^m not 2^d); (2) chart-pushforward = ν
(general structural); (3) depth-one x²y² by a DIRECT route (√N ∫φ f e^{−Nx²y²} → √π(∫φf(x,0)dx/|x| + …) for f vanishing near 0, then uniqueness);
subtype S packaging low; zeta separate. Mirror wording applied (pin 72f89d5; 18 ahead of Overleaf).

### 18.9 MIXED-MONOMIAL EXPLICIT INSERTION FUNCTIONAL LANDED (2026-09-15). Main 7077a28, 777 modules.
CDLXIII `MonomialInsertionConstant` (Astra #134 (c)(1)): `monomialInsertion k η := Σ_σ amplitudeCoeff 0 k λ* 1 (η∘reflect σ)`;
`monomial_tendsto_insertion` (headline XIX zero phase + `phaseCoeff_zero_phase` + N ↦ √N: normalised → monomialInsertion k (φf), all k_i > 0,
φ supported in symBox); `monomial_coeff_comp_gv_eq` (𝒯[f∘π] = explicit, by uniqueness); `monomial_integral_extremalStratumMeasure_eq`
(∫ f∘π dν^{λ*}_{m*} = explicit for f∘π vanishing near D_{m*+1}: the positive-dimensional leading measure = weighted restriction of the prior
to {x_i = 0 : k_i = kmax}); `monomialInsertion_equal` (2^d Γ(1/2κ) η(0)/((d−1)!(2κ)^d)); `monomialInsertion_x2y2 = √π η(0)` ✓ CDLXII.
Mirror sentence + pin 7077a28 (19 ahead of Overleaf). Remaining (Astra ranking): chart-pushforward = ν (general structural, M–L); depth-one
x²y² by the direct route (√N ∫φ f e^{−Nx²y²} → √π(∫φf(x,0)dx/|x| + ∫φf(0,y)dy/|y|) for f vanishing near 0); scaling to drop the symBox
support hypothesis; k_i = 0 exponents; subtype S packaging (low); zeta (separate programme).

### 18.10 CONSULT #135 (2026-09-15): DESIGN of the structural unit P1 (chart-pushforward = ℛ). Corrections to my Definition B: use |f|ω
(positive densities, signed f); the naive collar (2ε)⁻¹∫_{|f|<ε} g ω DIVERGES — correct: (2ε)⁻¹∫_{|f|<ε} g|f|ω or (2 log 1/ε)⁻¹∫_{ε<|f|<r} g ω;
ℛ sums NORMAL SIDES: full two-sided c-fold crossing = 2^c/∏_J 2k_j × ordinary iterated residue (sanity: x^{2k}, μ=1/2k: ℛ = (1/k)δ₀). A′
(truncated negative moment, constant c!) CONFIRMED but label "expected classical characterisation, not formalised". PLAN P1 (M–L; unit 4 gating):
U1 F-free context Ξ₁ := Ξ.withF 1; withF-invariance of geometry/base measures; amplitude factorisation ((withF G).amp p).amp s v =
(Ξ₁.amp p).amp s v * G (divPt p s v) on the chart domain. U2 face parameter space Q_{p,J} = Base_p × W_{p,J} (W = complementary coords),
reference q = β_p ⊗ volume|box, maps z(s,w) = glue J 0 w, e(s,w) = divPt p s z, restricted to valid chart points with e ∈ X (face points must
be shown in (Y.φ i).target; OpenPartialHomeomorph not globally continuous). U3 density D_{p,J} = ∏_J(2k)⁻¹ · A⁰_p(s,z) · residueWeight(h|Jᶜ,k|Jᶜ,μ,w);
faceResidueMeasure = map e (q.withDensity ofReal D) on X; chartResidueMeasure μ c = Σ_I Σ_{J simple} faceResidueMeasure. U4 (gating): local
finiteness — for compact C ⊆ X, ∫_{e⁻¹C} D dq < ∞ (extra vanishing active coord ⇒ image in D_{c+1}; need chart-box closure/target containment/
weight support control) or cutoff domination via integrability behind integrableOn_pieceStratum_integrand; then Regular via sigma-compact
locally-finite (check exact Mathlib name). U5 ENNReal pushforward formula, then real test bridge ∫_X G dm_{p,J} = ∫_s dlogResidueInt(...) dβ_p
(integral_map, withDensity, Fubini on prod, amplitude factorisation). U6 headline: chartResidueMeasure μ c = residueMeasure Y hc hzero and
stratumMeasure = ofReal(residueConst) • chartResidueMeasure (via eq_stratumMeasure_of_tests on ν' := ofReal residueConst • chartResidueMeasure).
U7 optional monomial specialisation 2^{m*}/∏_J 2k_j. No extremality hypothesis. Paper sentence: "On X the intrinsically defined normalised residue
measure is exactly the finite sum of the pushforwards of the multiplicity-normalised simple-face densities in any resolved chart transport;
equivalently the sum over normal sides of the iterated logarithmic density residue of (K∘π)^{−μ}μ_U, each normal side contributing (2k_j)⁻¹ per
wall." Artifact A/B wording corrected accordingly.

### 18.11 CHART-PUSHFORWARD IDENTITY LANDED (2026-09-15). Main 3b39911, 780 modules. (P1 of consult #135, units 1–6.)
CDLXIV `SmoothChartResidueCollar`: `ampObs` (amplitude family of an observable typed over Ξ.X Y — needed because `(Ξ.withF G hG).amp` carries
`(withF).X Y` types that block `rw`), `amp_withF_eq` (amp = ρloc(Tm)·G(divPt) on the closed box; ρloc = ω|b|prior∘ψ F-free), joint continuity/
bounds, `gv_divPt_eq`, `eventually_amp_zero_of_deep` (divPt deep ⇒ in D_{c+1} (G vanishes nearby) or off supp prior (ρloc vanishes nearby)),
`exists_collar` (tube lemma over compact Base × deepSet; `isCompact_deepSet`), `integrable_faceIntegrand` (joint, base ⊗ vol|box; bound M·C off the
collar via `exists_bound_residueWeight`). CDLXV `SmoothChartResidueMeasure`: `faceRef`, `faceNorm'`, `faceDensity` (uses ρf, the smooth global
extension of ρloc, for measurability), `faceMap` (through chartInv), `faceMeasureU := map faceMap (faceRef.withDensity ofReal D)`,
`faceMeasure := comap val faceMeasureU` on X, `chartResidueMeasure := Σ_I Σ_{J simple} faceMeasure`, `integral_faceMeasure_test` (embedding →
integral_map → withDensity smul → Fubini → dlogResidueInt). CDLXVI `SmoothChartResidueIdentity`: `integrable_faceMeasure_test`,
`faceMeasure_lt_top_of_isCompact` (cutoff domination + ofReal_integral_eq_lintegral_ofReal), IsFiniteMeasureOnCompacts + Regular instances
(`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`; X is σ-compact and pseudometrisable automatically), `integral_chartResidueMeasure_test`
(= Σ_I ∫ pieceResidueSum), `residueConst_mul_integral_chartResidueMeasure` (= T[G]), `stratumMeasure_eq_smul_chartResidueMeasure` (via
eq_stratumMeasure_of_tests with Regular.smul), `chartResidueMeasure_eq_residueMeasure` (μ > 0), inherited support + transport independence.
Axiom probe clean. Mirror paragraph updated with Astra #135's paper sentence and the corrected Definition B wording (|f|ω, log-collar, 2^c/∏2k_j);
pin 3b39911 (21 ahead of Overleaf). Artifact Section 8 status updated. Lean gotchas: `set`-bound measures hide Regular instances; `classical`
breaks `Function.update` rewrites (instance mismatch) — use explicit ite or avoid; `MeasurableEmbedding.integrable_map_iff` with named args fails —
build the restricted-integrability fact and use `.1`; `Subtype.val` needs type ascription in `Measure.map/comap`.

### 18.12 CONSULT #136 (2026-09-15): CHART-PUSHFORWARD IDENTITY CLOSED; SECTION-4 PROGRAMME DECLARED COMPLETE FOR THE PAPER.
Verdict CLOSE (all six P1 units accounted for; no missing unit). Wording applied: hypotheses visible (μ > 0, c ≥ 1, zero-order); "pushforwards,
restricted to X"; "finite sum of measures finite on compact subsets of X" (not a finite measure); residue terminology scoped to the simple-pole faces;
HEADLINES row "Definition B realised: explicit chart-density formula proved equal to the intrinsic residue measure" (not "made a theorem").
comap along the embedding X ↪ U is acceptable (= restrict-and-retype; nothing lost). Transport dependence of the DEFINITION is explicit and
eliminated by `chartResidueMeasure_eq_of_transports` (independence among transports of the FIXED resolved core, not under change of resolution).
Collar dichotomy complete (depth + zero fibre + supported prior ⇒ D_{c+1}; else open complement of tsupport prior). Programme status: for the
paper's purposes the Section-4 programme is COMPLETE at the level of the intrinsic residue measure, its explicit resolved-chart representation and
transport independence; NOT claimed: meromorphic continuation, manifold-level residue calculus, Radon extension across D_{c+1}. Remaining (extensions
/examples/future work, ranked): depth-one x²y² direct route; scaling to drop box support in CDLXII–CDLXIII; k_i = 0 exponents; subtype-S packaging;
zeta continuation (separate programme). Mirror pin 3b39911 (21 ahead of Overleaf).

### 18.13 JET DEPENDENCE UNIT LANDED (2026-09-15). CDLXVII `SmoothStratumJetDependence`, 781 modules.
User question: is the transverse jet in the pairing `C_{μ,c−1}(f) = ⟨Res, j^α_S(f∘π)⟩` a coordinate-free object, and is the pairing formalised?
Answer now: yes, chart-free. `VanishesToOrderAt n H P` (locally a finite sum of products of n smooth functions vanishing at P) and
`MemIdealPowNear S n H P` (H ∈ 𝓘_S^n near P). Intrinsic order `stratumJetOrder μ P = Σ_{(k,h)∈pairs P} (⌊2kμ⌋₊ − h − 1)`; at face points equals
Σ_J resOrder (`stratumJetOrder_divPt_eq`, unconditional — pairs at a face point are exactly the J-walls); zero under ZeroOrder. Main:
`coeff_eq_zero_of_vanishesToOrder` / `coeff_eq_of_vanishesToOrder` / `coeff_eq_of_memIdealPow` / `T_eq_of_memIdealPow` — NO zero-order
hypothesis (first coefficient theorem on the exact stratum beyond order zero). Proof: coeff_eq_stratumSum; non-exact faces vanish
(`faceCoef_top_eq_zero_of_not_exact`); exact faces: face point in exact stratum (prior support) ⇒ amp = ρloc(Tm)·F(divPt) on the box, F locally
Σ_i ∏_l g_il, extend g_il∘chartInv and ρloc smoothly off the closed box (`exists_contDiff_eqOn_of_contDiffOn`), derivatives agree on O ∩ closedBox
(`pdMulti_eq_of_eqOn_inter_closedBox`), Leibniz `pdMulti_mul` + `pdMulti_prod_eq_zero_of_forall_eq_zero` (order < n ⇒ some factor undifferentiated);
face point off prior support ⇒ `pdMulti_amp_eq_zero_of_not_mem_tsupport`. Only vanishing AT the point is used (the S-version is the ideal-theoretic
packaging). Lean gotchas: `pdMulti_finset_sum` lives in `SmoothRenormalisedStrata` (import it); a `?_` inside `fun l => ?_` in `rw [...]` loses the
binder name — hoist to a named `have`; dot-notation lemmas need `variable {Ξ} in`; after `rw [hEqOn hx]` a beta-redex `(fun u => …) x` blocks the next
`rw` — `change` first; style linter forbids `show` (use `change`). Follow-ups: mirror sentence + leanref dots (pin bump); artifact §11 status;
optionally the fine multi-order version (per-wall orders α_j via Σ_j 𝓘_{E_j}^{α_j+1}) and Astra audit #137.

### 18.14 CONSULT #137 (2026-09-15) AUDIT OF THE JET UNIT; DESCENT LANDED (CDLXVIII, 782 modules).
Verdict: CDLXVII establishes intrinsic finite-jet dependence (kernel/invariance), not a separately constructed residue–jet pairing. Corrections
applied: (1) exponent zero — the original definitions made `MemIdealPowNear S 0 H P` mean "H locally = m" (empty products); fixed by allowing
smooth coefficients `Σ_i a_i ∏_l g_il` (now 𝓘_S^0 = C^∞, `memIdealPowNear_zero`), index type `ι` with `[Fintype ι]` (so `.add` uses `ι ⊕ ι'`);
(2) paper wording must include the prior φ among the determining data, must not suggest an explicit pairing object was constructed, and "finite
jet" is a per-point bound. Astra's replacement wording adopted in the mirror; Lean annotation "Formalised: invariance under the ideal-power
equivalence and the descent; an explicit residue–jet pairing as separately defined objects is not constructed". Order formula confirmed: at
exact-stratum points ⌊2kμ⌋₊ − h − 1 = α_j exactly (natural floor + truncated subtraction), n(P) = |α| is an order BOUND (cancellations may lower the
true order). "Depends only on the transverse jet" is justified in the ideal-theoretic sense (class mod 𝓘_S^{n+1}); equivalence with normal Taylor
coefficients (Hadamard in submanifold coordinates) is standard but NOT formalised — paper should define the jet ideal-theoretically. Do not say
tangential derivatives are "absorbed in density integration". Ranked: (1) fix + align wording [done]; (2) package the descent A/(A ∩ J) [done:
CDLXVIII `admissible`, `jetKernel`, `coeffLin`, `descendedCoeff`, `descendedCoeff_mk`]; (3) per-wall version Σ_j 𝓘_{E_j}^{α_j+1} optional
(annihilates a LARGER ideal — sharper; needed only for anisotropic j^α notation); (4) do NOT assert "conormal distribution of order n" (needs
continuity/order estimates). Lean gotchas: `at` is a keyword (variable name `aT`); `lake env lean` on a dependent uses STALE oleans after editing the
dependency — `lake build` the dependency first; `Sum.elim` cases reduce by rfl.

## 19. PROJECT: the EMPIRICAL version (K_n) in light of the population results (opened 2026-09-15; user: "focus on the empirical version"; consult #138 = audit of my proposal E1–E6)
Setting: Z^0_n[φ] = ∫ φ e^{−βnK_n} φ_prior, K_n∘π = u^{2k} − n^{−1/2} u^k ξ_n(u) (Watanabe standard form; u^k SIGNED), ξ_n ⇒ G. Paper Thm (strataempiricalexpansion) needs
C^ω-convergence of ξ_n (Hypothesis I); Lean has the chart-level Taylor-data version (weighted ℓ¹, all d; headline_*), far-phase bound, Gibbs concentration,
ratio transfer, sample-datum ℓ¹ CLT, Gaussian moments of S_λ, bilocal second moments, uniform moments, annealed assembly. Nothing coordinate-free/global.
Astra #138 corrections to my proposal: (1) a graded stratum coefficient is NOT a leading limit unless (μ,c) is the leading pair on the localisation (lower
exponents from shallower strata) — state the leading theorem for the leading pair (extremal pair first), the coefficient theorem separately; (2) convergence
of ξ_n only on Z_0 is insufficient (counterexample ξ_n(u) = h(√n u), trace 0, limit A(0)∫e^{−βv²+βvh(v)}dv) — need ξ_n ⇒ G in C(B) on a compact
neighbourhood B of the zero fibre (or trace convergence + transverse stochastic equicontinuity); (3) SIGNED monomial: u^kξ = |u^k|(sgn(u^k)ξ); the effective
field ξ̂ = sgn(u^k)ξ is branchwise (normal sides): K=x² two-sided with constant field a gives √N∫φe^{−Nx²+√Nxa} → √π φ(0)e^{a²/4} = φ(0)(S_{1/2}(a)+S_{1/2}(−a))/2,
NOT φ(0)S_{1/2}(a). Global object: on the normal-side cover Û →p U, ν_β(ξ̂) = p_*((S_{μ,β}(ξ̂)/Γ(μ)) ν̂), p_*ν̂ = ν; absolutely continuous w.r.t. ν with a
branch-averaged density. Our chartResidueMeasure is already a sum over orthant pieces σ (normal sides), so the branchwise density is natural there.
Normalisations: S_{μ,β}(a) = ∫t^{μ−1}e^{−βt+βa√t}dt, S(0) = Γ(μ)β^{−μ}, ∂_a^p S_{μ,β} = β^p S_{μ+p/2,β}; ν^μ_{c,β}(ξ) = (S_{μ,β}(ξ)/Γ(μ))ν^μ_c = (S_{μ,β}(ξ)/(c−1)!)ℛ^μ_c.
Proof route for the leading theorem: MARKED RADIAL LIMIT a_N (P, NK(P))_*(e^{−NK}μ_U) ⇒ ν ⊗ t^{μ−1}e^{−t}dt/Γ(μ) (reuse the population leading theorem at
rescaled N: a_N∫Fe^{−sNK} → s^{−μ}∫Fdν gives the Laplace transform of the radial marginal), then test against F e^{(1−β)t+βξ√t} with the tail bound
e^{−βt+βM√t} ≤ e^{βM²/2}e^{−βt/2}; fallback: fixed-δ face sandwich (freeze ξ on {u_j ≤ δ ∀ resonant j}, the rest loses one log; N→∞ then δ→0; the
N^{−ε} region is an O(ε) fraction of the log-simplex, not an O(1) layer). Annealed: E S_{μ,β}(G(P)) = Γ(μ)[β(1−βv(P)/2)]^{−μ} for βv<2 (first moment uses only
the variance function); E L² < ∞ iff ∬H(P,Q)ρ(dP)ρ(dQ) < ∞ with the bilocal kernel (d<2√(ab) finite; = iff μ<1/4); sup βv < 1 sufficient. Paper statements
(A) continuous-field leading residue theorem (no analyticity), (B) empirical leading law + posterior law (C(B) convergence, O_p(1) far envelope, ratio with
shared leading pair and a.s. positive finite denominator), (C) annealed residue + second moments, (D) keep the analytic full expansion; add finite-jet
locality of fixed graded coefficients (initially under analytic hypotheses). Ranked programme (new LOC est.): 0 leading-pair + signed/root interfaces +
regressions (300–800); 1 F1+E2 fluctuation bounds, weighted measure, locality, Lipschitz (300–900); 2 marked radial limit + continuous-field leading theorem
(1500–4000); 3 chart/piece assembly + branchwise pushforward (800–2500); 4 varying-field distributional transfer, joint observables, ratios, far phase
(500–1500); 5 Gaussian mean measure + UI transfer (400–1200); 6 bilocal variance criterion (500–1500); 7 fixed-index joint finite-jet coefficient theorem
(1500–4000); 8 uniform C^k asymptotics (3000–8000+). Parallel: compatibility lemma "analytic Taylor-tree coefficient = S-weighted face integral in a
zero-order leading chart" (500–1500). Regression suite: x² one/two-sided constant field; x²y² constant field with normal-side conventions; boundary-layer
field h(√n u); a localisation with a lower exponent; constant Gaussian face variance (effective temperature).

### 19.1 RANKS 0–1 LANDED (2026-09-15): CDLXIX `FluctuationLipschitz` + `EmpiricalRegressionOneDim`, CDLXX `EmpiricalStratumMeasure`; 785 modules.
Conventions fixed by the regressions: the root field is Watanabe's ψ = √n(K − K_n)/√K pulled back to U (β-free: with chart phase βv^{2k}, t = Nβv^{2k}
gives √N√β|v^k|ψ = √t ψ, so the density relative to OUR ν (which already carries β^{−μ}) is S_{μ,1}(ψ̂)/Γ(μ) — no extra β); the effective field on a piece is the
branch representative (sign ∏σ_i^{k_i} of u^k absorbed), so the two-sided x² example gives (S(a)+S(−a))/2 (`fluctuation_half_add_neg`,
`twoSided_constant_field_limit`); the boundary-layer field h(√N x) shows zero-fibre trace convergence is insufficient (`boundaryLayer_field_limit`).
`RootField` = ψ + continuous branch representatives `loc p` on Base × ℝ^{da} with `loc_eq` off the walls (open box). Empirical measure
`empiricalStratumMeasure ξ μ c = Γ(μ)/(c−1)! • Σ_I Σ_J (faceDensity · S_μ(faceTrace)/Γ(μ))_*`; zero field = ν; locality; domination ≤ S_μ(M)/Γ(μ) • ν; finite on
compacts, regular; Lipschitz in sup norm of the representatives with constant fluctLip μ M = S_{μ+1/2}(M)/Γ(μ). NEXT: rank 2 — the marked radial limit
a_N (P, N·K∘π(P))_*(e^{−NK∘π} μ_U) ⇒ ν ⊗ t^{μ−1}e^{−t}dt/Γ(μ) on X for the leading pair (start: extremal pair (λ*, m*) via `tendsto_normalised_partitionObs_extremal`
at rescaled N — a_N ∫F e^{−sNK} → s^{−μ}∫F dν is the Laplace transform of the radial marginal), then the continuous-field leading theorem by testing against
F e^{(1−β)t + βξ√t} (tail bound e^{−βt+βM√t} ≤ e^{βM²/2}e^{−βt/2}); fallback: fixed-δ face sandwich. Lean gotchas recorded in HEADLINES CDLXX.
