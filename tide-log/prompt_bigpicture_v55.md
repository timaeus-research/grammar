# Direction consult #55 — the Hironaka input exists in Lean: bridging `timaeus-research/hironaka`'s chart form to grammar's geometric bridge

Same setting (Lean 4 + Mathlib, repo `timaeus-research/grammar`, zero `sorry`/`axiom`, 414 modules, Headlines I–CXXII). Grammar main `5368098`, Lean pin `0d15103`, toolchain `v4.33.0` / Mathlib `v4.33.0`. Since consult #54: the concrete tangential reconstruction landed (CXXII: `TanChart.tanReconstruct : L1Seq (TanIdx m d) →L[ℝ] C(K, DataSpace d)`, `TanCertificate`, `assembled_expansion_of_tangential`). Every remaining non-claim of the grammar formalisation is now the resolution input: the certified chart presentation (charts, exact monomial phase, Jacobian, transport, partition of unity), its complexification for Hypothesis I, and the joint product-polydisc Cauchy estimate.

**New fact.** The user points me to `timaeus-research/hironaka` (Lean `v4.33.1`, Mathlib `v4.33.1`, 2416 files, an orchestrated campaign: 328/353 leaves done). Its Step 9 ("real-analytic strand A: the chart form", 39/39 leaves done) proves Bierstone–Milman 1989 Theorem 3.2 in chart form and the read-out (E4) that singular learning theory consumes. I have not yet finished an independent build of it (running); the repo's own gate claims `Monomialize`/`Proofs` sorry-free with `Statements` holding the frozen `sorry`-by-design records.

## What hironaka offers (exact interfaces, transcribed)

```lean
-- Monomialize/VolumeScaling/PartialResolution.lean
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
  E : ι → Set (Fin n → ℝ)              -- exceptional sets
  E_subset : ∀ i, E i ⊆ dom i
  E_closed : ∀ i, IsClosed (E i)
  E_null : ∀ i, volume (E i) = 0
  inj : ∀ i, InjOn (φ i) (dom i \ E i)
  jac_ne_zero : ∀ i, ∀ x ∈ dom i \ E i, (fderiv ℝ (φ i) x).det ≠ 0
  mult : ℕ
  multN : Set (Fin n → ℝ)
  multN_null : volume multN = 0
  mult_bound : ∀ y ∈ K \ multN, {p : ι × (Fin n → ℝ) | p.2 ∈ dom p.1 ∧ φ p.1 p.2 = y}.encard ≤ mult

-- Monomialize/Analytic/Structural/Terminal.lean
structure IsMonomialChart (F : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (dom : Set (Fin n → ℝ)) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen W
  subset : dom ⊆ W
  analyticOnNhd : AnalyticOnNhd ℝ φ W
  injOn : InjOn φ {y | y ∈ W ∧ monomialEval y h ≠ 0}
  exists_unit : ∃ u : (Fin n → ℝ) → ℝ, ContinuousOn u W ∧ (∀ y ∈ W, u y ≠ 0) ∧
    ∀ y ∈ W, F (φ y) = u y * monomialEval y e
  exists_jacUnit : ∃ v : (Fin n → ℝ) → ℝ, ContinuousOn v W ∧ (∀ y ∈ W, v y ≠ 0) ∧
    ∀ y ∈ W, (fderiv ℝ φ y).det = v y * monomialEval y h
def PartialResolution.IsMonomial (R : PartialResolution n F K) : Prop :=
  ∀ i, ∃ (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)), IsMonomialChart F (R.φ i) (R.dom i) e h W

-- Monomialize/Analytic/BM89/Readout.lean (conditional on Q n; `Q_all : ∀ n, Q n` is proved in Proofs/Step9/9_3_16.lean)
theorem exists_monomialResolution_at (hQ : Q n) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin n → ℝ} (hw : w ∈ U)
    (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ N : Set (Fin n → ℝ), IsCompact N ∧ N ∈ 𝓝 w ∧ ∃ R : PartialResolution n K N, R.IsMonomial

-- Monomialize/Analytic/Readout/Assembly.lean (the read-out to the SLT toolkit `LogResolutionData`, two-sided monomial bounds only)
theorem exists_logResolutionData_of_isMonomial … (hR : R.IsMonomial) (hKw : K w = 0) :
    ∃ ι … (D : LogResolutionData (Fin n → ℝ) volume (fun x => |K x|) w ι),
      ∀ α, ∃ (i : R.ι) (b : Fin n → ℝ) (ϱ : ℝ) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)),
        IsMonomialChart K (R.φ i) (R.dom i) e h W ∧ b ∈ R.dom i ∧ R.φ i b = w ∧ 0 < ϱ ∧
        Metric.closedBall b ϱ ⊆ W ∧ (D.chart α).φ '' (D.chart α).K = R.φ i '' Metric.closedBall b ϱ ∧
        (∃ hd : (D.chart α).d = n, (∀ k, (D.chart α).e (Fin.cast hd.symm k) = if b k = 0 then e k else 0) ∧
          ∀ k, (D.chart α).h (Fin.cast hd.symm k) = if b k = 0 then h k else 0) ∧
        ((∀ᶠ x in 𝓝 w, 0 ≤ K x) → ∀ k, Even ((D.chart α).e k))
```
Notes: (i) the units `u, v` are recorded only as `ContinuousOn` (the construction composes analytic functions with analytic local isomorphisms, so they are in fact analytic, but the frozen records do not say so; I cannot edit hironaka); (ii) charts are on all of `ℝ^n` (cubes `closedBall b ϱ` in the sup metric, both signs of every coordinate), with exponents `e, h ∈ ℕ^n` and no tangential/normal split; (iii) the phase form is `K ∘ φ = u · y^e`, NOT `y^{2k}`; (iv) evenness of `e` is available when `K ≥ 0` near `w`; (v) `PartialResolution` gives injectivity and nonvanishing Jacobian off a closed null set, a null-set cover, finite multiplicity — no pushforward identity as such; (vi) the `LogResolutionData` toolkit (two-sided bounds `cf·y^e ≤ |K|∘φ ≤ Cf·y^e`, `cJ·y^h ≤ jacAbs ≤ CJ·y^h`, and `TransportsToOn volume volume K φ (ofReal ∘ jacAbs)` = exact transport identity for every subset of the box) also exists and already yields `HasLLCExponentsOn` (E5: sublevel volumes `≍ ε^λ(−log ε)^{θ−1}`).

## What grammar needs (exact interfaces)

```lean
structure LocalisationData (U) [MeasurableSpace U] where
  μ : Measure U; phase obs : U → ℝ; phase_measurable; phase_nonneg : ∀ᵐ z ∂μ, 0 ≤ phase z
  obs_integrable : Integrable obs μ; δ : ℝ; δ_pos
-- Z N = ∫ obs · exp(−N·phase) dμ; sublevel = {phase < δ}
structure FiniteSublevelPartition (ι) [Fintype ι] where
  ρ : ι → U → ℝ; measurable_ρ; nonneg_ρ : ∀ i, ∀ᵐ z ∂D.μ, 0 ≤ ρ i z
  sum_eq_one : ∀ᵐ z ∂D.μ.restrict D.sublevel, ∑ i, ρ i z = 1
structure ChartPresentation (D : LocalisationData U) (ρ : U → ℝ) (K) [TopologicalSpace K] [MeasurableSpace K] (n : ℕ) (β : ℝ) where
  ν : Measure K; [IsFiniteMeasure ν]
  h k : Fin (n + 1) → ℕ; k_pos : ∀ i, 0 < k i; b : ℝ; b_pos
  Φ : K × (Fin (n + 1) → ℝ) → U; measurable_Φ
  c : K × (Fin (n + 1) → ℝ) → ℝ; measurable_c; nonneg_c : ∀ᵐ p ∂chartMeasure ν n b, 0 ≤ c p   -- chartMeasure ν n b = ν ⊗ Lebesgue on (0,b]^{n+1}
  x : TangentialData K (n + 1)                                                                  -- C(K, DataSpace (n+1)), the ℓ¹ Taylor data (phase slots, amplitude slots)
  transport : ((chartMeasure ν n b).withDensity fun p => ((chartDensity h c p).toNNReal : ℝ≥0∞)).map Φ
      = (D.μ.restrict D.sublevel).withDensity fun z => ((ρ z).toNNReal : ℝ≥0∞)               -- chartDensity h c p = (∏ p.2 i ^ h i) * c p
  phase_normal : ∀ᵐ p ∂chartMeasure ν n b, D.phase (Φ p) = β * ∏ i, p.2 i ^ (2 * k i)
  amplitude_eq : ∀ᵐ p ∂chartMeasure ν n b, evalF (toEta b (x p.1)) p.2 = c p * D.obs (Φ p)       -- evalF = the absolutely convergent power series of the amplitude coefficients in the normal variable
  fluct_zero : ∀ v, xiCoord (x v) = 0
structure NormalMomentPresentation (C : ChartPresentation D ρ K n β) where
  p : K → FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ; R : K → ℝ≥0∞
  analytic : ∀ v, HasFPowerSeriesOnBall (C.obsFibre v) (p v) 0 (R v); radius : ∀ v, ENNReal.ofReal C.b < R v   -- obsFibre v u := c (v,u) * obs (Φ (v,u))
  cBound : ℝ; c_le : ∀ q, C.c q ≤ cBound
structure AdaptedStrataData (D) (M) (K : Fin M → Type*) … (n : Fin M → ℕ) (β) where
  partition : D.FiniteSublevelPartition (Fin M); chart : ∀ I, ChartPresentation D (partition.ρ I) (K I) (n I) β
theorem expectation_expansion_of_adaptedStrataData (A : AdaptedStrataData D M K n β) (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) D.Z (gCoeff A.ν A.h A.k β A.b A.x) ∧ (exponentially small tail) ∧ (Taylor–moment form) ∧ …
```
Downstream everything (canonical coefficients `gCoeff`, first nonzero pair, `(λ, m)`, posterior laws, next-log corrections, the stochastic theorems) hangs off `gInt A.ν A.h A.k β A.b A.x` = the sum of the tangential standard integrals `∫_K ∫_{(0,b]^{n+1}} evalF(η(x v))(u) u^h e^{−βN u^{2k}} du dν(v)`.

## The gaps I see between the two (please correct/complete)
1. **Exact monomial phase.** grammar needs `K∘Φ = β u^{2k}` exactly on the box; hironaka gives `u(y) y^e` with `u` continuous nonvanishing, `e` even when `K ≥ 0`. The classical fix picks one coordinate `i₀` with `e_{i₀} > 0` and substitutes `y_{i₀} ↦ y_{i₀} |u|^{1/e_{i₀}}` — an analytic local isomorphism only if `u` is analytic; with `u` merely continuous the new chart is a homeomorphism with a continuous Jacobian factor, which breaks `analyticOnNhd` and the power-series amplitude. Options: (a) keep `u` in the amplitude: impossible, the phase is in the exponent; (b) the Mellin/“two-sided” route: with `u` only bounded above and below, `Z(N)` is sandwiched between two exact standard integrals at `β cf` and `β Cf`, which gives `Z(N) = Θ(N^{−λ}(log N)^{m−1})` with the CORRECT `(λ, m)` but not the coefficient — a genuinely new, provable theorem in grammar today (“the two-sided chart form determines the exponent pair of the population integral”), matching hironaka's E5 on the volume side; (c) request an analytic-unit record from the hironaka campaign (`AnalyticOnNhd ℝ u W`), after which the substitution is available in grammar.
2. **Sign/orthants.** hironaka's cubes include negative coordinates; grammar's box is `(0,b]^{n+1}`. Reflection `y_i ↦ −y_i` on each orthant: even `e` keeps the phase, `|det|` picks `|y|^h`, `v` changes by a sign — one `ChartPresentation` per orthant, `2^{n}` of them per hironaka chart, with `ρ` split accordingly (or `ν` absorbing the tangential orthants).
3. **Tangential/normal split.** hironaka exponents `e ∈ ℕ^n` with zeros; grammar needs the normal coordinates `{i : e_i > 0}` (all `k_i > 0`) as the box and the rest as the compact tangential base `K` (a cube, `ν` = Lebesgue with the tangential part of `y^h` and of the units absorbed into `c` and `ν`). The Jacobian exponents on tangential coordinates go into `c`; the normal `h_i` are grammar's `h`.
4. **Transport.** grammar's `transport` is a pushforward-with-density identity on the whole box; hironaka gives `InjOn` off a null set, `det ≠ 0` off a null set, analyticity; Mathlib's change of variables `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` / `Measure.map` for injective `C¹` maps on measurable sets should produce it, chart by chart, with the partition `ρ_I` the (disjointified) indicators of the chart images `φ_I(dom_I)` times a prior density. Is disjointification by indicators compatible with `amplitude_eq` (the amplitude must be a power series in the normal variable on the whole box)? An indicator in the normal variable is not. The paper uses a partition of unity; grammar's `amplitude_eq` forces the cutoff to depend on the tangential variable only (or to be handled by choosing the boxes so that overlaps are null — hironaka's `mult_bound` says images overlap on a set of finite multiplicity, not measure zero). What is the right way to get a `FiniteSublevelPartition` whose pieces are chart-exact? (Maybe: refine to disjoint boxes in `y` before pushing forward — overlaps of *images* are the issue, the fibres `φ_I⁻¹(φ_J(dom_J))` are semianalytic, not boxes.)
5. **Observable and prior analyticity.** `amplitude_eq` needs `c · obs∘Φ` to be a power series in `u` with continuous tangential coefficients: `obs` analytic and the prior analytic on the chart, `Φ` analytic (given), the Jacobian unit analytic (the same regularity issue as in 1).
6. **Hypothesis I / complexification for the stochastic side**: real-analytic `φ` extends holomorphically to a complex neighbourhood; the torus inclusion `T_R ⊆ W^{(ℂ)}` and the divisibility `f(x, φ(w)) = w^k a(x,w)` are further steps; probably out of reach this round.
7. **Toolchain/dependency.** grammar `v4.33.0` vs hironaka `v4.33.1`: adding `hironaka` as a lake dependency means bumping grammar's Mathlib one patch and pulling 2400 files (build time); the alternative is to TRANSCRIBE `IsMonomialChart`/`PartialResolution` verbatim as a grammar hypothesis structure (`MonomialResolutionData`) and prove `MonomialResolutionData → AdaptedStrataData`-shaped bridges in grammar, leaving one final `hironaka_type_eq`-style identification for later.

## Ask
A ranked, bounded (≤ 8 units) plan of NEW THEOREMS in grammar that consume hironaka's chart form as it stands (continuous units), with precise Lean statements, Mathlib inputs (names where you know them; I will grep), traps, and non-claims. In particular: (A) is the two-sided route (gap 1(b)) — `Z(N) = Θ(N^{−λ}(log N)^{m−1})` from a `PartialResolution`+`IsMonomial` with `K ≥ 0`, via sandwiching by standard integrals, with `(λ, m)` the minimum over charts and orthants of `(h_i+1)/(2k_i)`-type ratios in grammar's normalisation — worth a headline, and what is the cleanest formulation (from `LogResolutionData`'s two-sided bounds directly? from `HasLLCExponentsOn` by a Laplace-transform Tauberian argument — grammar already has the Mellin/Abelian leading coefficient machinery `MellinCoefficient.lean` for the exact case)? (B) which bridge pieces (orthant reflection, tangential/normal split, transport from `InjOn`+`det ≠ 0`, chart-exact partitions) are provable now and reusable once analytic units arrive? (C) the precise strengthened record I should ask the hironaka campaign for (`AnalyticOnNhd ℝ u W`, `0 < u` when `K ≥ 0`, anything else) so that grammar's `expectation_expansion_of_adaptedStrataData` becomes unconditional for analytic `K ≥ 0` with analytic observable and prior. (D) dependency vs transcription. Stop rule: when the plan's units are exhausted or a unit needs the analytic-unit record.
