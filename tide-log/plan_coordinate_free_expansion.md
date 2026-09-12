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

## 5. Units (order of execution; sizes are targets; gates in bold)

| # | Unit | Content | Gate |
|---|---|---|---|
| 1 | `NormalDifferentialConvention` (CCXCVII, DONE) | `D^r_⊥ := rawNormalJet`, `r! • T_r = D^r_⊥`, germ locality, linearity | — |
| 2 | `ResolvedGeometry` | structure, strata, incidence combinatorics, stratum pair | no asymptotic fields |
| 3 | `ResolvedNormalData` | normal/tubular interface, `normalDifferential` of `φ∘π`, symmetry, bridge to `IsGlobalNormalSection` | reuse existing bundle API |
| 4 | `ResolvedIntegrationData` | `localisedIntegral_eq_stratum_fibreIntegral`, away piece, change of variables `π_* μ_U = μ_W` | genuine change of variables |
| 5 | `ResolvedMonomialCertificate` | certificate structures; chart integral = stored localised integral | quantitative hypotheses explicit |
| 6 | `ProjectorBlowupGeometry` | `U = {(x,P) : P symmetric idempotent of trace 1, Px = x}`, `π(x,P) = x`, divisor `{x = 0}`, properness, explicit chart equivalences on `P_ii > 0` | matrix lemmas suffice |
| 7 | `ProjectorBlowupCertificate` | `K = |x|²`: `k = 1` (order 2), `h = d−1`, tubular normal family, density compatibility | first substantive instance |
| 8 | `ResolvedExactMoments` | `pair_exactMoment_eq_integral`, `localisedIntegral_eq_tsum_stratumContraction` | analytic domination, dependent-fibre measurability |
| 9 | `StratumMomentCoefficients` | construct `B_{I,r,α,j}` from chart results (finite parts of #91 as engine), gluing, integrability | **integrable tensor coefficients under adapted localisation** |
| 10 | `ResolvedCutoffExpansion` | `expectation_expansion` (the target), summable interchange over `r` | **tied-crossing infinite-`r` test** |
| 11 | `ResolvedLeadingMeasure` | leading corollary; `geometricLeadingMeasure = leadingMeasure` of CCXC | constants and `c₀` restriction |
| 12 | `ResolvedNormalCrossingExamples` | cube and tied normal-crossing instances; non-local-finiteness regression | ordinary integrability vs finite part |

If gate 9 or 10 fails, the statement is adjusted (tensor-valued distributions with intrinsic
regularisation), never patched with an axiom asserting the missing theorem.

## 6. Hypotheses that remain at the end

Certified resolved geometry with a compatible monomial atlas (a.e.-disjoint or multiplicity-corrected
change of variables, exact core transport, tail gap, unit handling), analytic admissibility of `φ`
(radii, majorants), uniform integrable bounds for the base integrals. Everything else — the strata,
the normal differentials, the moment coefficients, the densities, the expansion — is a theorem.

## 7. Bookkeeping

Each unit: `Grammar/<Name>.lean`, HEADLINES row, README count, THEOREM_MAP chain, gated build,
axiom probe, merge to main; mirror paragraph and pin bump at milestones (after unit 5, 7, 10, 11).
