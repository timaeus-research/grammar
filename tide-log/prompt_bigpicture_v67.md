# Astra consult #67 — the geometric bridge on top of hironaka: build the certified presentation ourselves

You are Astra, direction-setting consultant for the Lean 4 (Mathlib v4.33.1) formalisation of Gerraty–Murfet, *Grammar (Expectations and the Exceptional Divisor)*, repo `timaeus-research/grammar` (main `2024ead`, 489 modules, axiom-clean). The fidelity pass you asked for in #66 is done (closure certificate with coverage statement and external register committed). Two things changed since:

1. **`timaeus-research/hironaka` is complete** (356/356 leaves). Bierstone–Milman Thm 3.2 in chart form is the theorem `Monomialize.Analytic.Q_all (n) : Q n` (also `Q'_all` with analytic units), `#print axioms = [propext, Classical.choice, Quot.sound]`, same Lean/Mathlib pins as grammar. Grammar bumped the pin and the population exponent pair is now unconditional (CLXXXV: `laplaceTheta_of_analyticOnNhd_nonneg`, `exists_exponentPair`, `tendstoInMeasure_log_div_log_of_analyticOnNhd_nonneg`).
2. **The owner's directive**: proceed with the remaining externals — the certified chart presentation (charts, adapted partition of unity, exact normal form), the lifted foot, the remainder estimates, the model coefficient identification — and *any material we need on top of hironaka we develop ourselves in grammar* (no waiting on the hironaka team; hironaka's E6 analytic-space resolution sits on a sorried `AnalyticSpace` skeleton and is NOT available to us; only the chart-form strand is).

## What hironaka exports (verbatim)

```lean
structure PartialResolution (n : ℕ) (F : (Fin n → ℝ) → ℝ) (K : Set (Fin n → ℝ)) where
  K_compact : IsCompact K
  ι : Type
  [fin : Fintype ι]
  dom : ι → Set (Fin n → ℝ)
  dom_compact : ∀ i, IsCompact (dom i)
  φ : ι → (Fin n → ℝ) → (Fin n → ℝ)
  smooth : ∀ i, ∃ U, IsOpen U ∧ dom i ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (φ i) U
  mapsTo : ∀ i, MapsTo (φ i) (dom i) K
  cover : volume (K \ ⋃ i, φ i '' dom i) = 0
  E : ι → Set (Fin n → ℝ)
  E_subset : ∀ i, E i ⊆ dom i
  E_closed : ∀ i, IsClosed (E i)
  E_null : ∀ i, volume (E i) = 0
  inj : ∀ i, InjOn (φ i) (dom i \ E i)
  jac_ne_zero : ∀ i, ∀ x ∈ dom i \ E i, (fderiv ℝ (φ i) x).det ≠ 0
  mult : ℕ
  multN : Set (Fin n → ℝ)
  multN_null : volume multN = 0
  mult_bound : ∀ y ∈ K \ multN, {p : ι × (Fin n → ℝ) | p.2 ∈ dom p.1 ∧ φ p.1 p.2 = y}.encard ≤ mult
```
```lean
Monomialize/Analytic/Structural/Terminal.lean:46:structure IsMonomialChart (F : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
Monomialize/Analytic/Structural/Terminal.lean-47-    (dom : Set (Fin n → ℝ)) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)) : Prop where
Monomialize/Analytic/Structural/Terminal.lean-48-  isOpen : IsOpen W
Monomialize/Analytic/Structural/Terminal.lean-49-  subset : dom ⊆ W
Monomialize/Analytic/Structural/Terminal.lean-50-  analyticOnNhd : AnalyticOnNhd ℝ φ W
Monomialize/Analytic/Structural/Terminal.lean-51-  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
Monomialize/Analytic/Structural/Terminal.lean-52-  exists_unit : ∃ u : (Fin n → ℝ) → ℝ, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧
Monomialize/Analytic/Structural/Terminal.lean-53-    ∀ y ∈ W, F (φ y) = u y * monomialEval y e
Monomialize/Analytic/Structural/Terminal.lean-54-  exists_jacUnit : ∃ v : (Fin n → ℝ) → ℝ, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
Monomialize/Analytic/Structural/Terminal.lean-55-    ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h
Monomialize/Analytic/Structural/Terminal.lean-56-
Monomialize/Analytic/Structural/Terminal.lean-57-/-- A per-chart predicate: a property of the chart map, its domain and its exceptional set. -/
Monomialize/Analytic/Structural/Terminal.lean-58-abbrev ChartPred (n : ℕ) : Type :=
Monomialize/Analytic/BM89/Readout.lean:117:theorem exists_monomialResolution_at (hQ : Q n) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
Monomialize/Analytic/BM89/Readout.lean-118-    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U)
Monomialize/Analytic/BM89/Readout.lean-119-    (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) :
Monomialize/Analytic/BM89/Readout.lean-120-    ∃ N : Set (Fin n → ℝ), IsCompact N ∧ N ∈ 𝓝 w ∧
Monomialize/Analytic/BM89/Readout.lean-121-      ∃ R : PartialResolution n K N, R.IsMonomial := by
Monomialize/Analytic/BM89/Readout.lean-122-  obtain ⟨N, hNc, hNn, R, hR⟩ := hQ 1 (e4Data hU hK hw hKw hne)
Monomialize/Analytic/BM89/Readout.lean-123-  exact ⟨N, hNc, hNn, R, fun i => (hR i).e4_isMonomialChart⟩
Monomialize/Analytic/BM89/Readout.lean-124-
Monomialize/Analytic/BM89/Readout.lean-125-end Monomialize.Analytic
```

(`R.IsMonomial` := every chart is an `IsMonomialChart K (R.φ i) (R.dom i) e h W` for some `e h W`; the units `u, v` are recorded `ContinuousOn` but are analytic by hironaka's bridge lemma `analyticOnNhd_of_eq_continuousOn_mul_monomial` — a continuous `u` on open `W` with `F = u · y^e`, `F` analytic, is analytic; `IsQChart`/`IsAnalyticQChart` are equivalent, `Q'_all`.) Also available: `Monomialize.Analytic.exists_monomialResolution_at (hQ : Q n) … : ∃ N, IsCompact N ∧ N ∈ 𝓝 w ∧ ∃ R : PartialResolution n K N, R.IsMonomial` for `K` analytic near a zero `w`, not identically zero near `w`. The E4/E5 read-outs (`LogResolutionData` with two-sided monomial bounds `cf·mon e ≤ K∘φ ≤ Cf·mon e`, `cJ·mon h ≤ jacAbs ≤ CJ·mon h`, and `HasLLCExponentsOn`) we already consume. hironaka also has convergent Weierstrass division/preparation for `MvPowerSeries (Fin (m+1)) ℝ` (`exists_unique_weierstrassDivision`), Mathlib's `IsWeierstrassDivision`.

Important: hironaka gives a **finite family of charts into `W`** with a.e. cover and a finite multiplicity bound `mult`, not a global resolved manifold `U` with a proper `π : U → W`. Chart images may overlap.

## What grammar's certified presentation demands (verbatim)

```lean
structure LocalisationData (U : Type*) [MeasurableSpace U] where
  μ : Measure U          -- resolved measure (prior and Jacobian absorbed)
  phase : U → ℝ          -- K ∘ π
  obs : U → ℝ            -- observable ∘ π
  phase_measurable : Measurable phase
  phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ
  δ : ℝ
  δ_pos : 0 < δ

structure FiniteSublevelPartition (ι) [Fintype ι] where   -- ρ_i ≥ 0 measurable, ∑ ρ_i = 1 a.e. on {phase < δ}

structure ChartPresentation (D : LocalisationData U) (ρ : U → ℝ) (K : Type*) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ) where
  ν : Measure K  [IsFiniteMeasure ν]          -- base measure on the compact stratum piece
  h : Fin (n + 1) → ℕ                          -- Jacobian exponents
  k : Fin (n + 1) → ℕ ; k_pos : ∀ i, 0 < k i   -- phase exponents
  b : ℝ ; b_pos : 0 < b                        -- box side
  Φ : K × (Fin (n + 1) → ℝ) → U ; measurable_Φ
  c : K × (Fin (n + 1) → ℝ) → ℝ ; measurable_c ; nonneg_c   -- density factor (prior, Jacobian unit, cutoff)
  x : TangentialData K (n + 1)                 -- tangential datum realising the amplitude (a continuous map K → ℓ¹ coefficient data)
  transport : ((chartMeasure ν n b).withDensity (chartDensity h c)).map Φ = (D.μ.restrict D.sublevel).withDensity ρ
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)     -- EXACT monomial phase
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b, evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)  -- amplitude is a convergent power series in the normal variable on the whole box (0,b]^{n+1}
  fluct_zero : ∀ v, xiCoord (x v) = 0

structure AdaptedStrataData (D) (M) (K : Fin M → Type*) (n : Fin M → ℕ) (β) where
  partition : D.FiniteSublevelPartition (Fin M)
  chart : ∀ I, ChartPresentation D (partition.ρ I) (K I) (n I) β
```
`expectation_expansion_of_adaptedStrataData` then gives the paper's `thm:expectation_expansion` (power–log expansion with canonical coefficients, cutoff remainder `K N^{−L}(1+log N)^D`) — conditional on an `AdaptedStrataData`. Also present: `ResolutionChart`/`ResolutionCover` (the chart data of `PartialResolution`, with the exact transport identity `ResolutionChart.map_absDet` from Mathlib's change of variables off the null exceptional set), `LocalisationData.partitionOfCover` (normalised indicators of an a.e. cover — measurable weights, **not analytic**), and the stochastic `ExactBoxCoreCertificate` (adapted coordinates `ψ` on a core with the measure identity, `φ(Φ(ψ(v,u))) = ∏ u_j^{k_j}`, `ξ(Φ(ψ(v,u))) = evalF (toXi b (x v)) u`, `F(Φ(ψ(v,u))) = evalF (toEta b (x v)) u · ∏ u_j^{h_j}`).

The recorded obstruction (`LocalisationObstruction.lean`): a chart-exact analytic amplitude on the whole box cannot absorb an exact sublevel cutoff `{K < δ}` (analytic continuation forces vanishing), so the normalised-indicator partition of a chart cover does not yield an `AdaptedStrataData`; a compatible localisation (cutoffs depending on the tangential variable only, or an analytic-core decomposition modulo an exponentially small remainder) is needed.

The paper's `lem:adapted_pou`: open `V_I ⊆ U_ε` and a smooth partition of unity `ρ_I` with (i) `V_I ∩ E_I = S_I`, (ii) `V_I ∩ E_j = ∅` for `j ∉ I`, (iii) cover, (iv) fibre-saturated, (v) `ρ_I(v,u) = ρ_I(v)` in tubular coordinates near `S_I`. In a monomial chart the strata are coordinate subspaces `{y_I = 0}`, so an explicit candidate is `ρ_I(y) = ∏_{j∈I} θ(y_j) ∏_{j∉I} (1 − θ(y_j))` with a smooth cutoff `θ` (1 on `|y| ≤ a`, 0 on `|y| ≥ 2a`): `∑_I ρ_I = 1`, and on the tube `|y_I| < a` the weight is a function of the tangential variables only.

Unit removal: on a monomial chart `K∘φ = u · y^e` with analytic `u ≠ 0`; `K ≥ 0` fixes signs (orthant reflection `map_signReflect_weightedPosBox` exists in grammar); the reparametrisation `ỹ_i = y_i · |u|^{1/e_i}` (one `i` with `e_i > 0`) is analytic (`AnalyticAt.log`, `Real.exp` analytic) with Jacobian `|u|^{1/e_i} + y_i ∂_i|u|^{1/e_i}`, invertible **near `{y_i = 0}`** but not necessarily on the whole box; Mathlib has `HasStrictFDerivAt.toOpenPartialHomeomorph` and `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` (analytic inverse function theorem). So exact normal form is local near the divisor; away from `{K = 0}` the integrand is exponentially small (`localisation_bound`).

The lifted foot (`LiftedFoot`, CLXXX): in a monomial chart the strata are coordinate subspaces, so the foot is the coordinate projection (CLXXVIII's coordinate model) — the abstract lifted foot is only needed off-chart.

Stochastic side: the paper's `f(x, π(u)) = u^k a(x,u)` (Watanabe's standard form / division) is consumed through `TorusCertificate.ofDivision` with the division as a hypothesis. hironaka's Weierstrass division is for a single convergent series, not uniform in the sample point `x`.

## Questions

1. **Architecture.** Given finitely many overlapping monomial charts with a.e. cover and a multiplicity bound (no global `U`), what is the right *certified presentation* to build? Options: (a) per chart, an analytic-core decomposition: `∫_W F e^{−nK} = ∑_charts ∫_{core_i} (…) + O(e^{−δn})`, with cores where the exact normal form holds and tangential-only cutoffs, overlaps handled by a partition of unity on `W` pulled back (not analytic in `y` — is that fatal, or can the overlap weights be pushed into the tangential variable/into the exponentially small remainder?); (b) an "orthant-and-divisor" refinement of hironaka's charts into subcharts on which unit removal is global; (c) something else. Be concrete about how overlaps between chart images are to be handled so that the amplitude stays analytic in the normal variables.
2. **Unit list.** Give a bounded programme (≤ 8 units, each a Lean module with stop rules and Mathlib inputs) that ends with **the paper's population expansion theorem for a real-analytic `K ≥ 0` and analytic prior/observable, unconditional** (i.e., `AdaptedStrataData` constructed from `exists_monomialResolution_at`), including: exact normal form by unit removal (analytic inverse function theorem), orthant reflection, the coordinate-adapted partition of unity with tangential-only weights near strata, the chart-presentation certificate (transport via `map_absDet`, `phase_normal`, `amplitude_eq` via real-analytic power series with radius > box side — note real-analytic, not holomorphic), the assembly over finitely many charts with the multiplicity issue, and the exponentially small remainder. Which of these are genuinely hard in Lean and where is the risk?
3. **Coefficient identification and the stochastic side.** Is there a bounded path from hironaka's chart form to Watanabe's standard form `f(x,π(u)) = u^k a(x,u)` for the log-likelihood ratio (the division uniform in `x`, with the Hypothesis-I envelope), or should the division stay a hypothesis (`hca`, `hφ`) with the population theorem the target? What about the remainder estimate `E|A_n Rem_n| → 0` — is the exponentially small tail from localisation plus the annealed remainder bound already enough once the certified core is constructed?
4. **What not to open.**

Answer in Markdown; be concrete about Lean statements where possible.
