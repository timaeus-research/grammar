# Consult #149 — grammar ↔ greybook bridge: where to go after the leading-order units

You are advising on the Lean 4 formalisation (repo `timaeus-research/grammar`, namespace `Grammar`, 831 modules, axiom-clean) of §4 of the grammar paper, and on a glue workspace `grammar-greybook-bridge` that imports both `Grammar` and the grey-book formalisation `GreyBook` (1246 modules) under a single hironaka pin. Consult #148 (yours) designed the bridge: (b) glue repo, deliverables (1) single-chart C⁰ bridge, (2) joint finite-chart finite-jet law, (3)/(4) resolved assemblies, (5) dependency consolidation.

## What landed since #148 (all axiom-clean, built)

Grammar (dependency-free contract, module `EmpiricalBoxFieldLimit`):
```lean
noncomputable def boxExt {b : ℝ} (hb : 0 ≤ b) (φ : C(closedBox d b, ℝ)) : (Fin d → ℝ) → ℝ :=
  fun u => φ ⟨clampBox b u, clampBox_mem_closedBox hb u⟩
noncomputable def boxZ (h k : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b) (η : (Fin d → ℝ) → ℝ)
    (φ : C(closedBox d b, ℝ)) (N : ℝ) : ℝ := empBoxIntegral h k N b (boxExt hb φ) η
-- empBoxIntegral h k N b ξ η = ∫_{(0,b]^d} η u · u^h · exp(−N u^{2k} + √N u^k ξ u) du
theorem abs_boxZ_sub_le ... |boxZ φ N − boxZ ψ N| ≤ e^{R²} ‖φ−ψ‖ A · empBoxIntegral h k (N/2) b 0 1   (‖φ‖,‖ψ‖ ≤ R)
theorem exists_eventually_lipschitz_boxZ_div, continuous_boxZ, continuous_boxLimit, tendstoUniformlyOn_boxZ_div(_nat)
theorem isTightMeasureSet_range_of_tendstoInDistribution {E} [MetricSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (hLG : TendstoInDistribution L atTop G (fun _ => P) P') :
    IsTightMeasureSet (Set.range fun n => P.map (L n))     -- converse Prokhorov (Mathlib isTightMeasureSet_of_isCompact_closure)
theorem tendstoInDistribution_boxZ_div (h k) (hk : ∀ i, 0 < k i) (hb : 0 < b) (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) (hηc)
    [MeasurableSpace C(closedBox d b, ℝ)] [BorelSpace _] {L : ℕ → Ω → C(closedBox d b, ℝ)} (hLm) {G : Ω' → C(closedBox d b, ℝ)}
    (hLG : TendstoInDistribution L atTop G (fun _ => P) P') :
    TendstoInDistribution (fun n ω => boxZ h k hb.le η (L n ω) n / powLogScale lam (m-1) n) atTop
      (fun ω' => boxFaceLimit h k lam m b (boxExt hb.le (G ω')) η) (fun _ => P) P'
```
Bridge (`Bridge/ChartBox`, `Bridge/ChartLaw`, `Bridge/ChartLimitLaw`), for `D : GreyBook.Ch6.AtlasData P X F K ν χ A rb β` (the grey book's Theorem 6.7 data: joint continuous empirical field `ξCM n ω : C(chartUnion d rb, ℝ)`, laws → `μlim`, Gaussian fidis, `hCf/hCfbox` identifying it with `−chartXi` on each chart box) and a chart `α`:
```lean
def chartEmb rb α : C(closedBox d (rb α), chartUnion d rb)          -- u ↦ (α, u)
noncomputable def chartField D α n ω : C(closedBox d (rb α), ℝ) := (D.ξCM n ω).comp (chartEmb rb α)
noncomputable def chartLaw D α : ProbabilityMeasure C(closedBox d (rb α), ℝ) := D.μlim.map precomp
theorem tendstoInDistribution_chartField : TendstoInDistribution (chartField D α) atTop (fun φ => φ) (fun _ => P) (chartLaw D α)
theorem chartField_apply : chartField D α n ω u = −A.chartXi X D.fa α n ω u.1
theorem integral_chartBoltzmann_eq_empBoxIntegral_chartFieldExt :   -- grey-book chart evidence in standard form = grammar's box integral
    ∫ u in box d (fun _ => rb α), A.chartBoltzmann 1 n (A.chartXi X D.fa α n ω) α u * A.unitWt α u * ∏ j, u j ^ A.h α j
      = empBoxIntegral (A.h α) (A.k α) n (rb α) (chartFieldExt D α hrb n ω) (A.unitWt α)
theorem chartLaw_map_evalFinE : (chartLaw D α).map (evalFinE us) = multivariateGaussian 0 (covMatrix (fidiVec …) P)
theorem tendstoInDistribution_chartZ_div (hk) (hrb : 0 < rb α) (hm) (hlead : BoxLeading (A.h α) (A.k α) lam m) (hη : Continuous (A.unitWt α)) :
    TendstoInDistribution (fun n ω => chartZ D α n ω / powLogScale lam (m-1) n) atTop
      (fun φ => boxFaceLimit (A.h α) (A.k α) lam m (rb α) (boxExt hrb.le (−φ)) (A.unitWt α)) (fun _ => P) (chartLaw D α)
```
So deliverable (1) is done: the stochastic input of grammar's empirical leading theorem is instantiated for a standard-form chart.

## The finding that changes the plan

The grey book formalisation ALREADY proves the leading-order law from the process law, in its own normal form. `GreyBook.Ch6.theorem_6_7_of_process` / `theorem_6_7_of_chartedAtlas_of_process`: given essential charts `E α : EssentialChart` (split coordinates `Fin (r+2) ⊕ Fin s ≃ Fin d`, exponents `k h k' h'`, `hlam : ∀ i, (h i + 1)/(2 k i) = lam`, `hμ : ∀ j, 2 lam k' j < h' j + 1`, C¹ envelope data), nonessential charts, tail data, and `hξ : TendstoInDistribution ξ atTop ξlim (fun _ => P) P` in `C(M, ℝ)` with continuous chart pull-backs `gα`, it concludes
```lean
TendstoInDistribution (scaledEvidence …) atTop
  (fun ω => ∑ α, boxGamma (E α).k (E α).h (E α).b lam * limitY (E α).k' (E α).h' (E α).b β lam (E α).φ (chartField (gα α) (ξlim ω))) (fun _ => P) P
-- limitY k' h' b β lam φ ξ = ∫_{scaledBox s b} yWt h' y · φ(0,y) · yK k' y^(−lam) · fluctuationFunction β lam (ξ (0,y)) dy
-- boxGamma k h b lam = b^{Σh + r + 1 − 2Σk·lam} · (∏ 1/(2kᵢ)) / r!
-- fluctuationFunction β lam a = ∫₀^∞ t^{lam−1} e^{−βt + β a √t} dt   (= grammar's fluctuation 1 lam a at β = 1)
```
(`continuous_limitYb`, `limitYb_tendstoInDistribution` do the continuous-mapping step; `main_theorem_6_2_law_of_chartedAtlas` gives the law of −log of the scaled evidence.) The grey book also has Theorem 6.1 unconditionally (`main_theorem_6_1_unconditional`: standard form `f(x, g_α u) = a_α(x,u) u^{k}` with `a` continuous in `u` on the box, measurable in `x`, `∫ a dμ = u^k`, and the empirical standard form) and `exists_atlasData`(`_even`). It has NO C^r (r ≥ 2) control of `ξ_n`; `AtlasData.fa` is only `ContinuousOn` in `u`; the analytic input is `IsLpValuedAnalytic F U₀` (F : ℝ^d → L^s(μ), s = 6 or 2k+4) and analytic (hironaka) charts.

Grammar's leading constant is in coordinate-free form:
```lean
faceFunctional h k l b ξ η = (1 / ((multCount (ratioExp h k) l − 1)! · ∏_{i ∈ resSet h k l} 2 kᵢ)) ·
  ∫_{w ∈ box {i // i ∉ resSet} b} η (glue (resSet h k l) 0 w) · fluctuation 1 l (ξ (glue (resSet h k l) 0 w)) · residueWeight (h|non-res) (k|non-res) l w
residueWeight h k μ w = w^h · (w^{2k})^(−μ);  boxFaceLimit h k lam m b ξ η = if multCount (ratioExp h k) lam = m then faceFunctional … else 0
```
Hence: the bridge's leading-order route (units 1, 2, 1b) is a second proof of the grey book's per-chart law, with a differently packaged constant; it is NOT new mathematics for the leading term. What the grey book lacks and grammar has is the SUBLEADING theory: the full empirical expansion with coefficients that are Borel functions of the branch jets (`coeffOnClosedJets`), the conditional theorem `tendstoInDistribution_resolvedCoeff_top_closed` (jets ⇒ in distribution ⟹ top coefficient ⇒ in distribution), jet tightness from envelopes `isTightMeasureSet_of_jetEnvelope` (needs ∫ Aₙ² ≤ C for a sup+Lipschitz envelope of the order-`R_p(μ)` jets), and the lower-log Mellin weights.

## Candidates (please rank, and design the top one to statement level)

(i) **Constant identification**: `boxFaceLimit (h) (k) lam m b ξ η = boxGamma k_E h_E b lam · limitY k' h' b 1 lam φ ξ'` in split coordinates (`splitCoords e`, `e : Fin (r+2) ⊕ Fin s ≃ Fin d`, essential coordinates = `resSet`, `r + 2 = m`), a consistency theorem between the two formalisations of the book's (6.7) constant; moderate effort (a change of variables and the identification `fluctuation 1 l = fluctuationFunction 1 l`, `residueWeight = yWt · yK^(−λ)` on the non-resonant coordinates, `1/((m−1)! ∏ 2kᵢ) · b^{…}` vs `boxGamma`). Payoff: independent cross-check of both developments; no new probability.

(ii) **Deliverable 2, finite-jet law** (the real gap): joint law of the order-`R` jets of `ξ_n` on the chart boxes. Needs, on the grey-book side, L^s-analyticity of the derivative kernels `u ↦ D^γ a_α(·,u)` — does it follow from `IsLpValuedAnalytic F U₀` + analytic charts (Mathlib `AnalyticOnNhd.fderiv`, composition) + the division `a = (F∘g)/u^k`? — plus your representative-selection lemma, plus Thm 5.9 on the finite family of derivative kernels (greybook `theorem_5_9_law` needs `CoeffExpansion`/`IsLpValuedAnalytic` for the KERNEL family), then continuity of grammar's `coeffOnClosedJets` gives the law of the top empirical coefficient. Large (weeks). Please say precisely which greybook statements are missing and whether they are provable from the present hypotheses (e.g. is the standard form `a` even analytic in `u` as an `L^s`-valued map in greybook's construction, or only continuous? Theorem 6.1's proof uses hironaka's chart form; the division by `u^k` in `L^s` is the crux).

(iii) **Jet tightness at order ≤ 1 from greybook envelopes**: greybook has sup-norm moments (`supNormPsi_moment_even`, Thm 5.8) and gradient bounds `exists_gradientBound_even`, `boundedInProbabilitySeq_gradient_xi_even` (O_p(1), moments?). Instantiating `isTightMeasureSet_of_jetEnvelope` at jet order 0/1 would give tight laws of the C¹ jets — but the conditional theorem needs order `R_p(μ)` which is typically > 1, so this only helps indices with `R_p(μ) ≤ 1`. Worth it?

(iv) **Close**: record units 1–2–1b as "the grey book's data model instantiates grammar's box contract; leading order agrees with GreyBook Thm 6.7 (modulo (i))", write the paper remark, stop the bridge.

Also: (v) should the grammar-side generic theorem be generalised to a finite family of boxes with a joint field in `∀ α, C(closedBox d (b α), ℝ)` (vector-valued transfer through uniformly convergent maps), to feed greybook's `hY` hypothesis form `TendstoInDistribution (fun n ω α => Yval α n ω)`? Given `theorem_6_7_of_process` already discharges `hY` internally, is there any consumer for that?

Constraints: grammar stays dependency-free (contracts only); greybook is "book only"; the bridge repo is local. Please be concrete about Lean statement shapes and about which existing declarations to consume, and flag any claim above you believe is wrong.
