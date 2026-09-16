# Consult #151 — from the joint jet law to a subleading chart-coefficient law (Stage E)

You advised on consults #148–#150 (grammar ↔ greybook bridge). Everything you designed in #150 is now built and axiom-clean (bridge repo, imports `Grammar` and `GreyBook`):

## Landed (exact Lean statements)

Grammar (dependency-free): `CoordinateJetTower` (`contDiffOn_of_coordTower`, `iteratedFDeriv_coordTower_apply`), `LpRepresentativeLimit` (`ae_eq_of_tendsto_Lp_of_tendsto_ae`, `ae_fderiv_eq_of_representative`, `memLp_tsum_abs_majorant`), `EmpiricalBoxFieldLimit` (`tendstoInDistribution_boxZ_div`).

Bridge Stage A: `AnalyticChartKernel A F` (open chart targets `S α ⊇ box`, analytic `a α : ℝ^d → Lp ℝ s μ`, `F (g α u) = u^k • a α u`, mean `u^k`), `exists_analyticChartKernel`; `derivKernel Q α k v u := iteratedFDeriv ℝ k (Q.a α) u v` analytic, a Definition 5.3 datum.
Stage B (upgraded to C^∞, all orders on one conull set):
```lean
structure ChartKernelRep (X : ℕ → Ω → E) (P : Measure Ω) (Q : AnalyticChartKernel A F) (α : ι) where
  U : Set (Fin d → ℝ);  isOpen_U;  box_subset_U : GreyBook.box d (A.b α) ⊆ U;  U_subset_S : U ⊆ Q.S α
  f : E → (Fin d → ℝ) → ℝ
  smooth : ∀ x, ContDiffOn ℝ ⊤ (f x) U
  measurable_jet : ∀ k b, ∀ u ∈ U, Measurable fun x => iteratedFDeriv ℝ k (f x) u (coordVecs b)   -- coordVecs b i := Pi.single (b i) 1
  represents : ∀ k b, ∀ u ∈ U, (fun x => iteratedFDeriv ℝ k (f x) u (coordVecs b)) =ᵐ[μ] Q.derivKernel α k (coordVecs b) u
  jet : (k : ℕ) → (Fin k → Fin d) → E → (Fin d → ℝ) → ℝ;  jet_cont; jet_meas; jet_rep
  jet_eq : ∀ᵐ x ∂μ, ∀ k b, ∀ u ∈ U, iteratedFDeriv ℝ k (f x) u (coordVecs b) = jet k b x u
  jet_exp : ∀ k b, ∃ h : CoeffExpansion X P (jet k b) (fun w => ∫ x, Q.derivKernel α k (coordVecs b) w x ∂μ) U s, ∀ i, Continuous (h.c i)
theorem exists_chartKernelRep (hX : Measurable (X 0)) (hμ : P.map (X 0) = μ) (hs : 1 ≤ s) (hd : 0 < d) : Nonempty (ChartKernelRep X P Q α)
```
Stage C (s = 6): `JetWord d R := Σ k : Fin (R+1), (Fin k.1 → Fin d)`; `jetKernel Rp p := (Rp p.1).jet p.2.1 p.2.2`, `jetMean Rp p u := ∫ jetKernel Rp p x u ∂μ`;
```lean
theorem jointJetLaw (R : ℕ) (hrb : ∀ α, A.b α = fun _ => rb α) (hX hμ hindep hXm hident) :
  (∃ μlim : ProbabilityMeasure C(chartUnion d (fun p : ι × JetWord d R => rb p.1), ℝ),
     Tendsto (fun n => ⟨P.map (chartProcessCM X (jetKernel Rp) (jetMean Rp) _ _ n), _⟩) atTop (𝓝 μlim) ∧
     ∀ r ws, μlim.map (evalFinE ws) = multivariateGaussian 0 (covMatrix (fidiVec X (fun x p => jetKernel Rp p.1 x p.2) (fun p => jetMean Rp p.1 p.2) _ 0) P)) ∧
  BoundedInProbabilitySeq (fun _ => P) fun n ω => ‖chartProcessCM X (jetKernel Rp) (jetMean Rp) _ _ n ω‖
```
Stage D: `chartMean Q α u := ∫ a_α(u) dμ` (C^∞ on S α; `D^k m_α(u)[e_b] = ∫ derivKernel`), `empField Q Rp α n ω := preEmpiricalProcess X (Rp α).f (chartMean Q α) n ω` (= `(1/√n) Σ_{i<n} (f (X i ω) u − m_α u)`, C^∞ on U for EVERY ω),
```lean
theorem ae_iteratedFDeriv_empField_eq (R) (hXm hident hμ) : ∀ᵐ ω ∂P, ∀ n α (k : Fin (R+1)) (b : Fin k.1 → Fin d), ∀ u ∈ (Rp α).U,
  iteratedFDeriv ℝ k.1 (empField Q Rp α n ω) u (coordVecs b) = chartUnionProcess X (jetKernel Rp) (jetMean Rp) n ω ((α, ⟨k, b⟩), u)
```
So: the joint law of ALL coordinate derivatives (order ≤ R, all charts) of the empirical fields of the C^∞ representatives converges to a Gaussian limit in `C(⨆ boxes)`.

Grammar's deterministic cube-level subleading results (single cube `[0,b]^d`, exponents `h k`, cutoff amplitude `η`, field `ζ`):
```lean
empIntegralRect η ζ h k b N = ∫_{rect b} η v · v^h · exp(−N v^{2k} + √N v^k ζ v)
theorem empRect_cutoffExpansion (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i) (hb : ∀ i, 0 < b i) :
  CutoffExpansion (Qamb k) (d - 1) (empIntegralRect η ζ h k b) (empCoeffRect η ζ h k b)   -- canonical coefficients empCoeffRect η ζ h k b μ q
theorem empCoeffRect_top_eq_smoothCoeff (hη) (hζ) (hk) (hb : 0 < b) (hμ : 0 < μ) (hc : 1 ≤ c) (hdeep : DeepVanishing η b c) :
  empCoeffRect η ζ h k (fun _ => b) μ (c - 1) = smoothCoeff (fun v => η v * fluctuation 1 μ (ζ v) / Γ μ) h k 1 b μ (c - 1)
theorem tendsto_empCoeffRect_top (hη) (hk) (hb) (hμ) (hc) (hdeep) {ζ : ℕ → ℝ^d → ℝ} {ζ₀} (hζ : ∀ n, ContDiff ℝ ∞ (ζ n)) (hζ₀) {M : ℕ → ℝ} (hM0')
  (hM : ∀ n, JetClose (∑ i, depthOf h k (cutoffOf h μ) i) (closedBox d b) (ζ n) ζ₀ (M n)) (hM0 : Tendsto M atTop (𝓝 0)) :
  Tendsto (fun n => empCoeffRect η (ζ n) h k (fun _ => b) μ (c - 1)) atTop (𝓝 (empCoeffRect η ζ₀ h k (fun _ => b) μ (c - 1)))
-- JetClose R K f₁ f₂ ε := ∀ r ≤ R, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x‖ ≤ ε  (C^R closeness on the CLOSED box)
```
plus the local Lipschitz bound `exists_pieceCoeff_top_bound`/`exists_resolvedCoeff_top_bound` (resolved level), and the resolved-level jet machinery: `BranchJetSpace μ := ∀ p r ≤ pieceOrder p μ, C(chartImage p, ContinuousMultilinearMap ℝ (fun _ : Fin r => ℝ^d) ℝ)` (a `def` with one NormedAddCommGroup instance), `branchJet`, `coeffOnJets` (continuous on the realizable jets), `coeffOnClosedJets := limUnder (𝓝[range branchJet] z) coeffOnJets'` (continuous on the closure), `tendstoInDistribution_resolvedCoeff_top_closed` (continuous mapping). All of that is for a `ResolvedData Ξ` + `ResolvedCoreTransport Y` (hironaka fork), NOT for a single cube; the grey book's `ChartedAtlas` (cubes `[0,b_α]^d`, chart maps `g α`, exponents `k h`, unit weights, `decomp`) is a different atlas object (hironaka upstream Thm 2.3) — identifying it with grammar's resolved core transport is the open geometry obligation (E6).

## Questions

E2. The grey book's chart field is `chartXi X D.fa α n ω u = (1/√n) Σ (fa (X i) u − u^k)` with `fa` its own C⁰/C¹ representative; our `empField` uses the smooth `f`. Both are continuous in `u` on the box; for each `u`, `fa · u =ᵐ a_α u =ᵐ f · u`. Cheapest Lean route to `∀ᵐ ω, ∀ n, ∀ u ∈ box, chartXi … u = empField … u` (countable dense set + continuity, as before)? Then the grey book's chart evidence `∫_{box} chartBoltzmann (chartXi) unitWt u^h` (already = grammar's `empBoxIntegral … chartXi unitWt`, unit 1) equals `empIntegralRect (unitWt) (empField) h k (fun _ => b) n` a.s. for all n. Is there any subtlety with `unitWt` (only `ContDiff ⊤` on ℝ^d in `exists_atlasData` via `hAw`) and with grammar's `DeepVanishing η b c` hypothesis (vanishing near the deep set relative to the closed box) — the grey book's unit weights are cut-offs from the resolution; is `DeepVanishing` expected to hold for the top index of a chart, or must it be imposed?

E3–E5 (single-chart subleading law). Target: for a chart α and an index `(μ, c)` with `DeepVanishing (unitWt α) b c`, the top coefficient `empCoeffRect (unitWt α) (empField α n ω) h k (fun _ => b) μ (c−1)` converges in distribution to a random variable given by the same coefficient functional at the Gaussian jet limit. Ingredients: (a) `empField α n ω` is C^∞ on U ⊇ closedBox but grammar's theorems need `ContDiff ℝ ∞ ζ` on ALL of ℝ^d: multiply by a smooth bump `χ ≡ 1` near the closed box (`ContDiffBump`), `ζ_n := χ · empField`; coefficients depend only on the box (do they? `empCoeffRect` is defined via the expansion of the box integral, so it depends on ζ only on `rect b`, and `empCoeffRect_top_eq_smoothCoeff` shows the top one depends on the jets on the closed box — please confirm the extension is harmless and how to state "coefficients only see the box" cheaply: uniqueness `empCoeffRect_unique`?). (b) A cube-level jet space `CubeJetSpace R b := ∀ r : Fin (R+1), C(closedBox d b, ContinuousMultilinearMap ℝ (fun _ : Fin r => ℝ^d) ℝ)` and the map `cubeJet R ζ` (jets of a smooth ζ restricted to the closed box); (c) the coefficient as a function on the realizable cube jets, continuity from `tendsto_empCoeffRect_top` (metric: JetClose ε ⇔ ‖jet₁ − jet₂‖ ≤ ε in the sup-product norm), extension to the closure as in `coeffOnClosedJets`, continuous mapping theorem. Is it better to (i) build this cube-level machinery afresh in grammar (mirroring EmpiricalBranchJets/ClosedJets ~600 lines), or (ii) realise the single cube as a trivial instance of grammar's resolved data (is there a `ResolvedData` for `K = u^{2k}` on a cube with one piece? grammar has `MonomialResolvedData`/`MonomialModification` (the identity as a Watanabe modification of a monomial phase) — could `tendstoInDistribution_resolvedCoeff_top_closed` be applied with Ξ := the monomial resolved data of the chart phase `u^{2k_α}` and the root field ψ := empField? That would give the subleading law for a chart FOR FREE if the monomial resolved data's pieces are the cube), or (iii) something else? (d) Transport of the Stage C law (coordinate jets in `∏_{(k,b)} C(box, ℝ)`) to `CubeJetSpace R b` (CMM-valued): the reconstruction `D^k f u = Σ_b h_{k,b} u • coordMono k b` (grammar `iteratedFDeriv_eq_sum_coordMono`) is a continuous linear map between the two spaces — fine? And measurability/Borel structure on `CubeJetSpace` (`borel` + `BorelSpace`, as for `BranchJetSpace`)? (e) The limit: the continuous extension `coeffOnClosedJets` evaluated at the Gaussian jet field — it lives on the closure of realizable jets; is the limit law supported on the closure (closed-set support passes to weak limits: which Mathlib statement — `ProbabilityMeasure` + `IsClosed` ⇒ `μlim Cᶜ = 0` from `μ_n Cᶜ = 0`; `ProbabilityMeasure.le_liminf_measure_open_of_tendsto`/portmanteau)?

E6. Given that E3–E5 yield a SINGLE-CHART subleading law, how much of the paper's Theorem (resolved, multi-chart) would that instantiate? Is the multi-chart subleading law obtainable by summing over charts of the grey book's `ChartedAtlas` (its `decomp` gives `∫ G dνχ = Σ_α ∫_{box_α} G(g_α u) unitWt u^h`) WITHOUT grammar's resolved core transport — i.e. define the total empirical evidence on the greybook atlas, expand chartwise (each chart is a cube with its own `(h_α, k_α)` on the common lattice `Qamb`), and sum the top coefficients — and is that acceptable as "the paper's empirical Theorem E on the grey book's data model" (the paper's resolved manifold IS such a charted atlas), or does the paper's statement genuinely need the resolved core transport (branch representatives, walls)?

Please rank, give Lean statement shapes for E2–E5 and the exact Mathlib/greybook/grammar declarations to consume, and flag anything wrong above.
