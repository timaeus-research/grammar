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
| 12 | further examples | tied-crossing (two-variable) regression for the infinite normal-order sum; two-sided interval (two charts); closed-form coefficient values for the 1D instance (`monoKernel` evaluation) | planned |

Gates 9 and 10 of the original plan (integrable tensor coefficients; summable interchange over `r`)
were passed by design: the coefficient tensors are constructed explicitly from the chart kernels
(no finite-part regularisation is needed for the CERTIFIED presentations, whose densities are
analytic on the box), and the normal-order series is summed pointwise inside the stratum integral,
so no interchange with the integral is required. `expansionCoefficient` was accordingly redefined as
`Σ_I ∫_{S_I} Σ'_r (1/r!)⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩ dν_I`.

## 5a. Status (2026-09-12, after consult #93 A–D; main `c4ad71b`, 611 modules)

★★★ `hasCoordFreeExpansion`/`hasCoordFreeExpansion_le` (CCCIII–CCCIV): the coordinate-free expansion of
`∫_W φ ϕ e^{−nK}` conditional on `ResolvedCertificate` + `CoefficientCertificate`, with the normal-order
series summed pointwise inside the stratum integrals (pointwise convergent, integrable sum) and the
truncation to exponents `≤ A`. Astra #93 audit: a certified coordinate-free REPRESENTATION, not an
intrinsic final theorem — headline and docstrings corrected (fields chosen, `cc` a factorisation family,
unnormalised integral). Then: ★★ first instance `∫_0^ρ P(x)e^{−nx²}dx` (CCCV–CCCVII); ★★★ canonicity of
the assembled scalar coefficients across certificates (CCCVIII); `jetFamily = monoFamily p` and
`CoefficientCertificate.ofSeries` (CCCIX); leading term and the bridge to the CCXC leading measure
(CCCX). Remaining: projector blow-up model (E), tied-crossing regression, two-sided interval, explicit
coefficient values.

## 6. Hypotheses that remain at the end

Certified resolved geometry with a compatible monomial atlas (a.e.-disjoint or multiplicity-corrected
change of variables, exact core transport, tail gap, unit handling), analytic admissibility of `φ`
(radii, majorants), uniform integrable bounds for the base integrals. Everything else — the strata,
the normal differentials, the moment coefficients, the densities, the expansion — is a theorem.

## 7. Bookkeeping

Each unit: `Grammar/<Name>.lean`, HEADLINES row, README count, THEOREM_MAP chain, gated build,
axiom probe, merge to main; mirror paragraph and pin bump at milestones (after unit 7 — done with CCCIII —, 10, 11).
