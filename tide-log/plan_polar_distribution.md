# Plan: the polar-distribution reorganisation (opened 2026-09-26; consult #167)

Origin. The end-to-end review of the new paper (review-log 2026-09-26, `deep_review_perspective.md`)
judged the draft "the right idea, not yet the right hierarchy". The user (2026-09-26) asked to start
preparing the reorganisation in the proposed manner: do the mathematics, formalise what needs to be
formalised, rewrite the paper around one invariant object. This file is the standing plan; update it as
steps land. Lean content pinned at d56efc8 (897 modules) unless stated.

## 0. The target hierarchy

1. **The intrinsic object downstairs.** `⟨T(s), f⟩ = ∫_W f K^{-s} φ dw`, holomorphic for `Re s < λ`,
   with a distribution-valued meromorphic continuation. Its resolved presentation is
   `T̃(s) = (K∘π)^{-s} π^*(φ dw)` with `π_* T̃ = T`. Near a positive candidate `μ`:
   `T̃(s) = Σ_{r=1}^{M_μ} A_{μ,r}/(μ−s)^r + H_μ(s)`, the `A_{μ,r}` distributions of finite transverse
   order supported on the `μ`-resonant locus.
2. **The universal radial kernel.** Mellin in `N` of the frozen partition function is
   `⟨T̃(s), F S_s(ψ)⟩` (population: `Γ(s)⟨T̃(s),F⟩`). The empirical theory is the population
   meromorphic distribution applied to the holomorphic amplitude `F S_s(ψ)`.
3. **The all-log coefficient formula (*).** For every `μ` on the lattice and `q ≤ M_μ − 1`,
   ```
   c_{μ,q}(F;ψ) = (1/q!) Σ_{r=q+1}^{M_μ} ((−1)^{r−q−1}/(r−q−1)!) ⟨ A_{μ,r}, F ∂_s^{r−q−1} S_s(ψ)|_{s=μ} ⟩,
   ```
   population case with `Γ^{(r−q−1)}(μ)` in place of the index derivative. Top log `q = M_μ−1`:
   `c = ⟨A_{μ,M_μ}, F S_μ(ψ)⟩/(M_μ−1)!` (the graded formula); the tie case `M_μ=2` gives the paper's
   `x²y²` constants.
4. **The global leading measure.** At the first pole `(λ, m)`, `A_{λ,m}` is a finite positive measure
   `ρ_λ` (extends integrably across intersections with nonminimal walls, since those have exponent
   `> λ`); for every smooth `F`, `N^λ (log N)^{−(m−1)} Z_N[F;ψ] → (1/(m−1)!) ∫ F S_λ(ψ) dρ_λ`. No
   admissibility.
5. **Normalisation.** `Z_N^ψ ~ N^{−λ} Σ_j B_j^ψ(log N) x^j` with distribution-valued polynomial blocks;
   the posterior is its formal normalisation; leading probability measure
   `Π_ψ = p_*(S_λ(ψ)ρ_λ / ∫S_λ(ψ)dρ_λ)`. Frozen / diagonal / Gaussian limits stated separately.
6. **The branch space.** Work on the real oriented blow-up of the resolution along the divisor (sides
   separated), so that "measurable field with orthantwise smooth representatives" becomes one smooth
   field on a manifold with corners, and the leading measure lives on a compact space.

## 1. Mathematics to do (paper level)

M1. Distribution-valued meromorphic continuation of `T̃(s)` on a normal-crossing chart, with pole order
    `≤ #resonant coordinates ≤ d` and Laurent coefficients `A_{μ,r}` continuous in finitely many
    derivatives of the amplitude (Taylor subtraction in each coordinate: `∫_0^b g(u) u^{a−2ks} du =
    Σ_{i<M} g^{(i)}(0) b^{a−2ks+i+1}/(i!(a−2ks+i+1)) + ∫(g − T_M g) u^{a−2ks} du`). Assemble over charts.
M2. Holomorphic amplitude families: for `G(s,u)` holomorphic in `s` near `μ`, smooth in `u`, jointly
    controlled, `s ↦ ∫ G(s,u) u^{h−2ks} du` continues with pole order `≤ M_μ` and Laurent data obtained
    by Taylor-expanding `G` in `s` to order `M_μ` (the remainder `(s−μ)^{M_μ}·(pole order ≤ M_μ)` is
    holomorphic). Apply to `G = F S_s(ψ)`. This is the proof of (*).
M3. Identification of `A_{μ,r}` with the paper's objects: `A_{μ,1}` at a simple pole = the finite-part
    face functional (tier 2); `A_{μ,c}` under the zero-order condition = `(c−1)!·ν^μ_c/Γ(μ)`·... (fix
    the exact normalisation: with `Γ(s)` factored out, `A_{μ,M}` is the residue measure `R^μ_c` up to
    sign conventions `(μ−s)^r` vs `(s−μ)^r`); lower `A_{μ,r}` = finite parts + index-derivative
    weights (the `x²y²` computation as the worked case).
M4. The global leading measure (item 4): integrability across nonminimal walls at the extremal pair;
    assembly; positivity; identification with the branchwise face limit; the compact branch space.
M5. Support and transverse order of `A_{μ,r}`: support in `{r_μ ≥ r}` (resonance count), transverse
    order `≤ n_μ` (jet dependence); descent to jet quotients (already formal for the top coefficient).
M6. Invariance: `π_* A_{μ,r}` paired with `f∘π`-type amplitudes is resolution-independent (uniqueness
    of the expansion downstairs); candidate poles are not.
M7. Variance-2 lemma: in the realisable standard form `E a(X,u)² → 2` as `u^k → 0` from
    `E e^{−u^k a} = 1`; consequence for the evidence threshold. Realisable `x²y²` model
    `p = N₂(√2 xy v(z), I)`, field `√2 v(z)·Z_n`, leading axis reweighting `exp((v(z)·Z_n)²/2)`.

## 1b. Conventions fixed by consult #167 (gpt6_bigpicture_v167.md)

* Polar functionals EXCLUDE the radial Gamma factor: `T_{h,k}(s)[G] = ∫_{(0,1]^d} G u^{h−2ks} du`,
  `T = Σ_{r=1}^{M_μ} A_{μ,r}/(μ−s)^r + H_μ(s)`; `M_μ = #{i : 2k_iμ − h_i − 1 ∈ ℕ}` is a candidate order
  bound, not the pole order of a given pairing.
* Library convention: `polarCoeff c μ q = (−1)^{q+1} q! c_{μ,q}` and
  `polarPart D a μ s = Σ_q a q/(s−μ)^{q+1}` (PrincipalPartUniqueness.lean); eq:laurent is right.
* `A_{μ,c}[F] = ∫ F d(residueMeasure)` holds ONLY on `stratumOpen c` for tests vanishing near
  `deepZeroFibre c` under `ZeroOrder`; no sign (A uses `(μ−s)^{−r}`); the standard-Laurent
  distribution is `(−1)^c A_{μ,c}`.
* `A_{μ,1}` at one resonant coordinate `i₀` of order `α`: `(1/(2k_{i₀}α!)) FP∫ ∂^α_{i₀}G(0,w) w^{h−2kμ}dw`
  with FP the coordinatewise Taylor-subtracted finite part (16); valid for ALL α, no gap hypothesis.
* Regression: `h=0, k=(1,1), μ=1/2`: `A_{1/2,2}[G] = G(0,0)/4`,
  `A_{1/2,1}[G] = ½∫(G(x,0)−G(0,0))/x + ½∫(G(0,y)−G(0,0))/y`; `c_{1/2,1} = A_2[G S]`,
  `c_{1/2,0} = A_1[G S] − A_2[G ∂_s S]` (must match `tendsto_logExample`).
* Orthant adapters: on a signed chart with signed-root field ξ the positive-box representative is
  `ζ_σ(v) = (∏σ_i^{k_i}) ξ(σv)`; test `K=x²` (branches a,−a), `K=x⁴` (both a), `K=x²y²` (σ_xσ_y a).
* The empirical leading limit for ALL smooth F already exists (`hasLeadingTerm_empZ`); what is missing
  at the extremal pair is the MEASURE IDENTIFICATION (no leading mass on `deepZeroFibre m`), not the
  limit. `IsExtremalData` (intrinsic, support-truncated) does not imply `ChartLeading Y` for an
  arbitrary transport: an adapted local cover certificate is needed.
* Branch space: first a finite disjoint union of closed leading-face parameter boxes (compact metric,
  atlas-dependent); the intrinsic real oriented blow-up later.

## 2. Formalisation to do (grammar library) — Astra's 24-unit route (each one file ≤ ~600 lines)

1. `PolarAmplitudeAlgebra` — START HERE. Pure algebra: `polarAmplitudeCoeff D a q = Σ_{j∈Ico q (D+1)}
   (−1)^{j+1} a j (j−q)/(j−q)!`, `logAmplitudeCoeff D a q = (1/q!) Σ (−1)^{j−q} a j (j−q)/(j−q)!`,
   `polarAmplitudeCoeff = (−1)^{q+1} q! · logAmplitudeCoeff`; with `P_j(s) = Σ_ℓ a_{j,ℓ}(s−μ)^ℓ/ℓ!`, for
   `s ≠ μ`: `Σ_j P_j(s)/(μ−s)^{j+1} − polarPart D (polarAmplitudeCoeff D a) μ s = Σ_j Σ_{ℓ>j}
   (−1)^{j+1} a_{j,ℓ}(s−μ)^{ℓ−j−1}/ℓ!` (polynomial). 300–450 lines.
2. `ComplexCubeTaylor` — complex-linear coordinate Taylor / faceAmp / rectangular remainder.
3. `ChartZetaStrip` — `chartZeta G h k s`, strip integrability, holomorphy on the strip.
4. `ChartZetaRegularization` — `chartZetaAtDepth p` (expression (3)), equality on the strip,
   holomorphy after denominators, compatibility.
5. `ChartZetaPolar` — `chartPolarFunctional h k μ r`, holomorphic difference, vanishing for r > M_μ,
   finite-jet bound.
6. `ChartZetaPolarSupport` — support in the resonance superlevel set, reality, rectangular jet congruence
   (NOT an exact-stratum ideal-power statement for lower r: false).
7. `HolomorphicCubeFamily` — Taylor in s with remainder controlled in a finite-jet seminorm (genuine
   infrastructure; de-risk in d = 1 with `g = g₀ + (s−μ)g₁` at a double pole).
8. `ChartZetaHolomorphicAmplitude` — polar array of a family via 1, 5, 7.
9. `ComplexFluctuation` — `complexFluctuation (s : ℂ) (a : ℝ)`, ofReal, derivative, index derivatives
   `= iteratedDeriv (fun ν ↦ fluctuation 1 ν a)` (do not change the real `fluctuation`).
10. `FluctuationAmplitudeFamily` — `G · S(s, ζ)` is a HolomorphicCubeFamily; jet Lipschitz.
11. `EmpiricalChartMellin` — `mellin (empIntegral G ζ h k) s = chartZeta (G S(s,ζ)) h k s` on the strip;
    local integrability; O(1) at 0⁺.
12. `EmpiricalPolarCoefficients` — (*) in real form:
    `empCoeff G ζ h k μ q = (1/q!) Σ_{j∈Ico q d} ((−1)^{j−q}/(j−q)!) chartPolarReal h k μ (j+1)
    (fun u ↦ G u * iteratedDeriv (j−q) (fun ν ↦ fluctuation 1 ν (ζ u)) μ)`; population form (12) with
    `Γ^{(j−q)}(μ)`. Via `polarCoeff_unique` (do NOT reprove the face construction equals it).
13. `ChartPolarFinitePart` — `finitePartPower`, depth independence, `chartPolar_one_resonant` (15),
    top = faceCoeffInt under the gap.
14. `PolarTwoDimExamples` — the x²y² regression against `tendsto_logExample`. FIRST MILESTONE.
15. `ResolvedZetaFunctional` — `ResolvedData.zetaPairing`, `polarFunctional`, transport independence,
    `comp_gv` (phase constants c^{−s} retained).
16. `ResolvedPolarStratum` — `polarFunctional = ∫ residueMeasure` on tests, resonant support.
17. `EmpiricalResolvedPolar` — branchwise (*) for `SmoothRootField.resolvedCoeff`.
18. `LeadingFaceMeasure` — closed-face measure (17) with amplitude, boundary null, = `boxFaceLimit`
    (uses `tendsto_empBoxIntegral_div_boxFaceLimit`). PARALLEL TRACK, start early.
19. `ResolvedLeadingMeasureChart` — under `ChartLeading`: `leadingResidueMeasureU`, finite, zero on
    `deepZeroFibre m`, `hasLeadingTerm_empZ_eq_integral_leading` for all smooth F.
20. `ResolvedExtremalLocalisation` — intrinsic `IsExtremalData` ⇒ global representation via an adapted
    local cover certificate (main size risk; may split).
21. `SmoothGlobalLeadingMeasure` — `globalExtremalStratumMeasure := (extremalStratumMeasure).map val`;
    coefficient = integral; `tendsto_normalised_partitionObs_extremal_all` (no `h0`); mass equality.
    Then strengthen `tendsto_normalised_partitionObs_extremal` in place (keep old as wrapper).
22. `CompactLeadingBranches` — `LeadingBranchSpace` = Σ over pieces/faces of closed boxes;
    `branchResidueMeasure`, `branchProjection`, `RootField.branchTrace : C(·,ℝ)`.
23. `LeadingBranchGibbs` — `leadingPosterior_eq_compactAvg`, presentation independence.
24. `EmpiricalAllLogContinuity` — every `(μ,q)` coefficient locally Lipschitz in finitely many jets
    without admissibility; then the old top-coefficient results become corollaries.

Total ≈ 9–13 kLOC. Sequence: 1 → 2–12 (+14 as the milestone) → 18–23 in parallel → 15–17 → 24.
Variance-2 lemma (M7): greybook bridge, hypothesis `E[e^{−va} − 1 + va − v²a²/2] = o(v²)`, `v = u^k`.

### Superseded lines of the first draft (kept for the record)
F1–F7 above are subsumed by units 1–24; the "generalise coeff_eq_of_memIdealPow to all r" idea is
withdrawn (false for lower orders: `A_{1/2,1}[x²] ≠ 0` for `x²y²` although `x²` vanishes at the crossing).


Existing pieces to reuse: `CutoffExpansion`, `emp_cutoffExpansion`/`smooth_cutoffExpansion` (the
Laplace side), `mellin_eq_mellin_cutoffRemainderFun_add_principalParts` + `polarCoeff_unique`
(Laurent data of the Laplace integral = coefficients), `fluctuation` at complex index and
`mellinMom_pow_mul_exp_eq_iteratedDeriv` (index derivatives), bridge `mellin_frozenEvidenceObs_eq`
(Mellin of the frozen evidence = `∫ f K^{-s} S_s(ψ) φ`), `SmoothStratumMeasure`/`residueMeasure`
(the top-log measure), `EmpiricalGeneratingIdentity`, `FirstCorrection` (tier 2 at `α ≤ 1`).

F1. **Chart zeta functionals.** `chartZeta G h k (s : ℂ) = ∫_{(0,1]^d} G u u^{h−2ks} du` for smooth
    `G`; strip convergence; meromorphic continuation by coordinatewise Taylor subtraction;
    definition of `polarFunctional h k μ r : (smooth amplitudes) →ₗ ℝ` (the `A_{μ,r}` in a chart);
    pole order bound `≤ resonantCount`; continuity in `C^R` jets.
F2. **Laurent data of the Laplace chart integral through Γ.** `Γ(s)·chartZeta` has Laurent data
    `c_{μ,q}`: relate `smoothCoeff G h k 1 1 μ q` to `polarFunctional` via the Taylor coefficients of
    `Γ` at `μ` (population (*)); this identifies the face-construction coefficients with polar data
    without going through `polarCoeff_unique`, or use uniqueness to identify.
F3. **Holomorphic amplitude families (M2) at chart level**, and the empirical (*):
    `empCoeff η ζ h k μ q = (1/q!) Σ_r ((−1)^{r−q−1}/(r−q−1)!) polarFunctional μ r (η · ∂^{r−q−1}_s S_s(ζ)|_μ)`.
    Uses the chart-level Mellin identity of the frozen integral (bridge-style, easy), the pole-order
    bound, and `polarCoeff_unique`.
F4. **Resolved polar functionals.** Assemble `A_{μ,r}` over a `ResolvedCoreTransport` as functionals
    on smooth functions on `U` (orthantwise); support in `{r_μ ≥ r}`; transverse order; jet descent
    (generalise `coeff_eq_of_memIdealPow`/`descendedCoeff` from the top coefficient to all `r`).
F5. **Global leading measure (M4).** Extend `extremalStratumMeasure` across `deepZeroFibre` at the
    extremal pair: integrability of the tangential weight when all complementary walls have exponent
    `> λ`; `tendsto_normalised_partitionObs_extremal` for all smooth `f` (drop `h0`).
F6. **Branch space** (later): the real oriented blow-up as a manifold with corners; probably a
    separate seabed or a `RootField`-level abstraction first.
F7. **Variance-2 lemma (M7)** on the greybook bridge side.

Order: F1 → F2 → F3 (the mathematical centre; chart level, ~6–10 units) → F5 (independent; ~3 units)
→ F4 (~4 units) → F7; F6 deferred.

## 3. Paper reorganisation (after F1–F3 and M4 are in hand)

New architecture (per the perspective review):
1. What a posterior expectation sees — thesis, main theorem (accessible form), one complete `x²y²`
   calculation through the constant log term, what is classical / newly formalised / new.
2. Meromorphic distributions and normal-crossing computation — `T(s)`, `T̃(s)`, actual vs candidate
   poles, support and transverse order, why crossing jets alone do not suffice, tests upstairs vs
   observables `f∘π`. (Absorbs §§2–5.)
3. Polar coefficients, residues and finite parts — all coefficients as Laurent data; the leading
   positive measure (global); associated-graded formulas; finite-part evaluation; observable
   vanishing and cancellation, with admissibility introduced before the restricted statements.
4. Universal radial tilting — `S_μ`, ladder, index derivatives, (*), the uniform expansion theorem,
   generating identity, two worked empirical calculations. (Weber/Weyl to an appendix.)
5. Posterior normalisation and the sample limit — distribution-valued blocks, formal normalisation,
   frozen / diagonal / Gaussian stated separately, source cumulants as a corollary.
6. What averaging does and does not preserve — bounded posterior convergence, critical failure of
   evidence uniform integrability (variance-2 lemma), two-site illustration, Gaussian Gibbs model in
   brief. Stein/replica/inverse-evidence/quenched-source to an appendix.
Appendices: chart proofs; finite-part computations; expansion algebra; special functions; Gaussian
Gibbs identities; formalisation coverage (a coverage document, not a source of hidden hypotheses).
Delete Appendix E. Examples: `x²y²` with the realisable model; `x²y⁶` as the boundary/finite-part
chart example; `x²(x²+y²)` for observability limits; a one-line regular two-sided sanity check.
Notation: `T(s)`, `M_F(s;ψ)`; `N` frozen, `n` diagonal; `E^pop_N`; "polar distributions"; drop
"wall-crossing" and "primes"; lattice denominator lcm.

## 4. Log
- 2026-09-26: plan drafted; consult #167 (Astra) returned the 24-unit route above, the conventions of §1b, the risk list (two-variable continuation interface; ChartLeading vs IsExtremalData; orthant signs; branch-space compactness; lower-pole jets; variance-2 hypotheses) and twelve further paper corrections (applied 2026-09-26). Unit 1 `PolarAmplitudeAlgebra` LANDED (u898, DLXIII). Unit 18 `LeadingFaceMeasure` LANDED (u899, DLXIV). Unit 2 LANDED as `ChartZetaStrip` (u900, DLXV; the complex amplitude infrastructure of Astra's unit 2 is avoided: amplitudes stay real, complex families will be split into real and imaginary parts, and the flat-amplitude strip theorem replaces the separate bounded/flat treatments). Next: unit 3 `ChartZetaFace` (zeta face-term identity and subset formula on the strip, mirroring `faceTerm_integral`/`integral_eq_sum_faceIntegral` with the inner integral `∏ 1/(mᵢ+hᵢ+1−2kᵢs)`), unit 4 `ChartZetaRegularization` (the face sum as the continuation), unit 5 `ChartZetaPolar`.
