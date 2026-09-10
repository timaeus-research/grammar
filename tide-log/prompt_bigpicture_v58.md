# Direction consult #58 — Astra #57's five units are landed; what is the next campaign?

Setting unchanged: Lean 4 + Mathlib `v4.33.1`, `timaeus-research/grammar` (440 modules, zero `sorry`/`axiom`, Headlines I–CXXXVIII), `timaeus-research/hironaka` pinned (axiom-clean declarations only, `Q n` explicit). Your #57 programme has been executed in full:

## Landed since #57 (all axiom-clean; formulas Monte-Carlo checked where numerical)
- **Unit 1 (CXXXIV)**: `E₊S_λ(G_j) = ∫₀^∞ t^{λ−1}e^{−β(1−βB_jj/2)t}dt`, `= +∞` for `βB_jj ≥ 2`; `E D(G) = Γ(λ)(βδ)^{−λ}∑ρᵢ` with integrability below threshold, `E₊D(G) = +∞` and `D` not integrable at `βc ≥ 2`; the clipping bridge: `X_n ⇒ Z` (Mathlib `TendstoInDistribution`, laws on different spaces) and `sup_n E|X_n|^p ≤ M`, `p > 1` ⇒ `Z` integrable and `E X_n → E Z`; conversely `X_n ≥ 0`, `X_n ⇒ Z ≥ 0`, `E₊Z = ∞` ⇒ `E₊X_n → ∞`; both specialised to `D(G)`. (The library also has a law-level UI theorem `integrable_and_tendsto_integral_of_uniformIntegrable` from an earlier campaign.)
- **Unit 2 = A3 (CXXXV)**: on `K = φ² ≥ κ`, `sup|ξ| ≤ B`, `2B ≤ √(Nκ)` ⇒ `−βNφ² + β√Nφξ ≤ −βNκ/2`; `‖∫_S a e^{phase}‖ ≤ e^{−βNκ/2}∫_S g`; sampling-exponent form via `N = n`, `ξ_n = −ζ_n`; big-O form under an eventual fluctuation bound.
- **Unit 3 = A2 (CXXXVI)**: box measure on `(0,b]^d` is the product of the box measures on `(0,b]^N × (0,b]^T` along `piEquivPiSubtypeProd`; the monomial phase depends only on the normal coordinates; `∫ u^h e^{…} = (∏_{i∈T} b^{hᵢ+1}/(hᵢ+1)) ∫_{(0,b]^N} w^h e^{…}`.
- **Unit 4 (CXXXVII)**: a `TorusCertificate` in all `d+m` chart variables gives the bi-indexed `TanCertificate` with envelope `M R^{−|γ|}R^{−|α|}` (Cauchy coefficients indexed by `γ ⧺ α`), so `assembled_expansion_of_jointTorus` needs only joint torus envelopes; for a joint analytic certificate the double Cauchy series rearranges absolutely and the phase of the reconstructed datum is `Re a(x, b·u ⧺ θ(v))` — the tangential reconstruction recovers the chart function.
- **Unit 5 (CXXXVIII)**: for a `ResolutionCover`, `∫_{⋃ images} F e^{E} = ∑ᵢ` chart pullbacks against `|det Dφᵢ|(ρᵢ∘Φᵢ)dy`; each chart splits over a measurable core and the gap `domᵢ∖coreᵢ`; with `κ ≤ K∘Φᵢ` on gaps, `Z(N) = ∑ᵢ Zᵢ^{core}(N) + Rem(N)`, `‖Rem(N)‖ ≤ e^{−Nκ}∑ᵢ∫_{gapᵢ}|F∘Φᵢ|`; the same for the empirical phase under the gap fluctuation bound with rate `e^{−Nκ/2}`.
- Text: all your #57 corrections A–Q applied to the note (the `½` in `W_i = ½⟨T 1_i⟩` removed; series vs finiteness domains separated; `cor:denominator` and the bridge paragraph added); three Lean remarks added to the paper mirror (empirical remainder + cover assembly after `rem:cutoff_correct`; the tangential/normal split in `subsec:tubular_nbhd`; joint torus envelopes in the stochastic remark).

## The refreshed non-claims list (from THEOREM_MAP.md)
## Non-claims (recorded in the mirror `grammar_lean.tex`)
Next-order corrections for observables not given by coefficient families; convergence in law of the
phase field itself (a scalar CLT is not sufficient); stable convergence relative to an environment
σ-algebra without the sampling identity; draw-level corrections from corrections of expectations;
process convergence in the Laplace parameter `s`; any correction after cancellation of the face
coefficient (or of the total assembled leading coefficient); variable-temperature or sharper
lattice-order expansions; all-orders division. Geometric bridge: Hironaka and the existence of the
certified presentation (charts, adapted partition of unity, exact normal form — a positive unit
`a(v,u)u^{2k}` is not removed); global tubular neighbourhoods; canonical normal derivatives beyond
fibre-linear covariance; an asymptotic ordering by normal Taylor degree; the fluctuation term (population
case only). Empirical CLT: an `ℓ¹` CLT under `MemLp Y 2` alone (`ℓ¹` is not of type 2); the existence
of the complexified resolution presentation (torus inclusion in the Hypothesis-I neighbourhood, analytic
divisibility; the joint product-polydisc Cauchy estimate is now a theorem GIVEN a joint torus envelope — CXXXVII — but the envelope itself
comes from the presentation); analytic units and a compatible localisation for the exact bridge from hironaka's chart form (its record has
continuous units and a chart cover, not a chart-exact analytic partition); the identification of a chart core with a weighted box in
adapted coordinates carrying certified data (the cover assembly CXXXVIII stops at the pulled-back core integrals); an exponentially small
*expected* remainder (the pathwise bound `sup|ξ_n| ≤ ½√(nκ)` is not a tail estimate on the exceptional datasets). Landed since this list
was first written: the tangential/normal split (CXXXVI), the identification `N = n` (CXXVII), the empirical exponential remainder (CXXXV).


## Candidate directions (please rank, correct, add; ≤ 8 units)
1. **Compact base I–II** (your #57 units 6–7): atomic approximation of `ρ`, partition-independent deterministic bounds `|log D| ≤ |log M| + C + βR²/2 + 2λR`, `0 ≤ V ≤ c(2λ/β + R²/4)` in terms of `R = ‖g‖_∞`, and transfer of `E H = βE V`, `E log D ≥ log D(0)`, the interpolation identity under an explicit second sup-norm moment of a measurable `C(K)`-valued `G` with `gaussianVector` finite-dimensional laws. Worth doing now? What exactly is the cleanest formal statement of "finite-dimensional laws are `gaussianVector`" for a `C(K,ℝ)`-valued random element, and is a *mass-preserving atomic approximation* of a finite Borel measure on a compact metric space available in Mathlib or must it be built (Riemann-sum style via a finite measurable partition of mesh `< ε`)?
2. **Strict `p`-moment thresholds** (your #57 unit 8) by scalar bounds `S_λ(a) ≤ Γ(λ)(βη)^{−λ}exp(βa₊²/(4(1−η)))` and `S_λ(a) ≥ C a^{2λ−1}e^{βa²/4}` for large `a`.
3. **The expected remainder**: an exponentially small *expected* remainder from a tail bound on the exceptional datasets, e.g. `P(sup_S|ξ_n| > ½√(nκ)) ≤ …` from a Bernstein/Hoeffding bound for bounded coefficients (Mathlib has `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`-type Hoeffding? please name what exists), giving `E|Rem_n| ≤ e^{−βnκ/2}∫g + ‖F‖·P(bad)`.
4. **Core = weighted box**: a theorem that a chart core given as the image of a box `(0,b]^d` in adapted coordinates in which `K∘Φ = u^{2k}·a(u)` with `a ≥ a₀ > 0` produces (after absorbing `a` — this needs a change of variables `u ↦ u·a^{1/(2k)}` in one coordinate, or the division bridge) a standard integral with the paper's data; i.e. connect `chartIntegral` on a box core to `boxIntegralFin`/the Taylor tree with a TanCertificate. Which precise statement is provable NOW without the analytic unit removal (e.g. keeping `a` inside the observable as a positive unit, since the Taylor tree treats the observable as a coefficient family — does the paper's theorem allow `a(u)u^{2k}` with `a` analytic positive by absorbing `a` into the *phase* rather than the observable? If not, what is the honest statement)?
5. **The bilocal critical line** `h = 2√(ab)` (finite iff `λ < 1/4`) and the cases `a ≤ 0`/`b ≤ 0` — worth a unit, or leave?
6. **Hironaka input**: is there anything more the pinned dependency now makes provable end-to-end, e.g. combining `laplaceTheta_of_analyticOnNhd_nonneg_of_Q` (population exponent pair) with the empirical remainder and the dataset bridge to state a *conditional* empirical theorem "if the scaled empirical coefficients are UI then their expectations converge to the population Laplace coefficient" at the level of exponents (not coefficients)?
7. Anything you consider more valuable for the paper as it stands (the mirror's Lean remarks are now dense; are there paper statements still un-dotted that are provable?).

## Ask
A ranked, bounded programme (≤ 8 units) with precise Lean-level statements, Mathlib inputs (names where you are confident; say so when not), traps, non-claims, and a stop rule; plus any further text corrections for the note or the mirror remarks.
