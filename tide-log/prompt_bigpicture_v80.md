# Consult #80 — grammar Lean: #79 units 1, 2, 3, 5 landed; what next?

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
550 modules, axiom-clean). Your #79 programme: P1 (posterior) → P3 (coefficient formula) → P2 (one-chart
examples), fidelity gate throughout. Landed since #79 (exact statements in the appendix):

* CCXLVI `PosteriorTransfer` (unit 1): `HasLeadingTerm.eventually_pos`, `tendsto_div_same_pair` (numerator
  coefficient may vanish), `tendsto_div_zero_of_dominated`, `isLittleO_div_ratio`, `div_isEquivalent`;
  `ResolutionCover.posteriorExpectation E_N[φ] := Z_N[φ]/Z_N[1]` (totalised), linearity of `Z_N[·]`
  (`boltzmannIntegral_add/const_mul/const`), certificates additive/homogeneous,
  `tendsto_posteriorExpectation_of_hasLeadingTerm`, `_zero_of_dominated`.
* CCXLVII `ProductChartPosterior` (unit 2): `hasLeadingTerm_boltzmannIntegral_of_productChartsD_extremal`
  for ANY admissible observable (no sign condition), `normaliserCoeff` (F = 1), `normaliserCoeff_pos`,
  ★ `tendsto_posteriorExpectation_of_productCharts` (0 < c₁ ∧ Z_N[1] > 0 eventually ∧ E_N[F] → c_F/c₁);
  coefficient intrinsic: `productCoeffD_add`, `_const_mul`, `_const` (= a·c₁), `productCoeffD_eq_of_cutoff`.
* CCXLVIII `ProductChartTiedStrata` (unit 3): `minimalSet M_i`, `pieceLam_eq_iff`, `pieceMult_eq_card_inter`,
  `card_minimalSet_le`, ★ `tied_iff` (tied at (λ*,k*) ⇔ M_i ⊆ I ∧ |M_i| = k*+1), `eq_minimalSet_of_all_minimal`,
  `pieceAtlas_sum_tied` (2^{|I|} × orthant coefficient), `prod_normalHalfExp_inv`,
  `tiedSum_of_all_minimal` (= 2^{|I|} Γ(λ*)/(|I|−1)! ∏_{j∈I} 1/e_j ∫_base β scalarPhase^{−λ*} pieceAmp(·,0)),
  `scalarAtlasPieceCoeff'_minimalSet`, `productCoeffD_extremal_eq_sum_tied` (sum over M_i ⊆ I ⊆ supp e_i of
  charts with |M_i| = k*+1), `productCoeffD_extremal_eq_sum_minimal` (all attaining charts with M_i = supp e_i).
* CCXLIX `OneChartProductExample` (unit 5): `ofChart` (one-chart cover), `ofChart_weight_eq_one` (counting
  weight = 1 on the image), `ProductMonomialChart.ofUnit` (package from geometric data, r = 1);
  `SquareExample`: identity chart on [−1,1]², K = y₀²y₁², `coverLam_eq = 1/2`, `coverDeg_eq = 1`,
  `dominantFace_eq_univ` (zero-dimensional base, volume 1), `integral_face_eq_one`,
  ★ `productCoeffD_eq_sqrt_pi` and `integral_isEquivalent`: ∫_{[−1,1]²} e^{−N y₀²y₁²} ~ √π N^{−1/2} log N.
  The predicted √π came out (reflection factor 2², Γ(1/2), ∏ 1/e_j = 1/4, face integral 1).

NOT done: unit 4 — the residual-face formula for tied I ⊋ M_i. In the library a cell coefficient is
`coeff = ∫_base β · q^{−λ} · boxFaceCoeff`, `boxFaceCoeff = b^{Σh+n+1} (b^{2Σk})^{−λ} amplitudeCoeff h k λ 1
(A z (b•·))`, `amplitudeCoeff = faceLeadConst · ∫_{unitBox} η(faceProj u) residualWeight u` with `faceProj`
zeroing the minimal coordinates and `residualWeight = ∏_{nonminimal} u_a^{h_a − 2k_a λ}` (appendix). So the
general tied sum is Σ_σ of these with A(z, reflect σ (b • faceProj u)); getting to your displayed formula
needs: factor 2^{|M|} from reflections on M (A independent of σ_M since those coordinates are 0), the
u_M-integration over (0,1]^M trivial, change of variables v = b·u_L on the nonminimal coordinates with the
b-powers cancelling exactly, and symmetrisation of the σ_L sum into ∫_{[−b,b]^L} (we have
`integral_symBox_eq_sum_reflect` for the full box only). Estimate: 300–400 lines of coordinate-splitting
measure theory. Integrability exponent h_a − 2k_a λ > −1 on L follows from λ < ratioExp a.

## Candidates for the next programme (3–5 units)
(R1) Unit 4 as above (residual-face formula) + K = x²y⁴ example (λ* = 1/2 from x: ratio 1/2 vs y: 1/4?? — no:
     ratios (0+1)/2 = 1/2 and (0+1)/4 = 1/4, so λ* = 1/4 from y alone, M = {y}, k* = 0; the tied strata are
     {y} and {x,y}; the {x,y} piece has residual coordinate x with exponent 0 − 2·1·(1/4) = −1/2 > −1). Payoff:
     completes P3; the paper does not print this case (its eq:thm_leading_coeff is all-minimal only).
(R2) N3 normal-dependent phase unit (G2): currently `unit_indep : u y = u (P_J y)` on dom; removing it is the
     main analytic restriction left inside a chart.
(R3) Weights (P4): `coverWeight` counting weights only factor through inactive coordinates when the overlap
     pattern is a product; you noted a smooth partition of unity would need regular weights entering the
     continuous amplitude. Design + implementation of `ResolutionCover` with supplied weights, or an amplitude-
     absorbing variant.
(R4) Bridge from hironaka's resolution (`Q_all` / `exponent_of_analytic`) to a cover of centred product charts
     — the one thing that would make the product-chart theorem UNCONDITIONAL for analytic K ≥ 0. What is
     realistic? (Shrink hironaka's charts to product boxes around divisor points; the inactive base T is a box
     in the non-divisor coordinates; units are not normal-independent in general → needs R2 first; the weights
     are the counting weights of the shrunken boxes → product overlap pattern is NOT automatic.)
(R5) Empirical/statistical transfer: the paper's object is E_{w|D_n}[φ] with the empirical L_n; the library has
     population/empirical exponent theorems (CCIX-b) — transfer the product-chart posterior limit to the
     empirical posterior (concentration of L_n − K on the dominant face? or the paper's fluctuation
     function S_μ route?).
(R6) Subleading terms (N5): the next order of E_N[φ]; needs certificates beyond leading order for scalar-unit
     cells (the library has all-orders cutoff expansions for monomial cells: `cutoffExpansion`).
(R7) Fidelity review (N7) of CCXLI–CCXLIX statements vs the paper's thm:expectation_expansion, and a mirror
     remark consolidating what the Lean theorem states (hypotheses: product charts, weight factorisation,
     positive-mass face) vs the paper's analytic-observable statement.

Q1. Rank R1–R7 for the next 3–5 units; reasons. My prior: R1 (finish P3) → R7 → R2 → R4.
Q2. For the top item, module contracts (statements, reuse, pitfalls). If R1: is there a cheaper route to the
    residual formula than coordinate splitting — e.g. define the residual face integral abstractly as
    `∫_{unitBox} A(z, b•faceProj u) residualWeight u` (already the library's form) and only prove the
    2^{|M|} factor + symmetrisation as a SEPARATE identity for the symmetric box; or keep the orthant form
    as THE formula and add a lemma identifying it with the signed-box form?
Q3. Any misstatement in CCXLVI–CCXLIX (appendix)? In particular: `tied_iff` uses `pieceMult − 1 = k*` with
    natural subtraction (pieceMult ≥ 1 for tied pieces, fine?); `productCoeffD_extremal_eq_sum_minimal`
    hypothesis `M_i = supp e_i` for attaining charts; the `√π` example's use of the zero-dimensional base
    (volume univ = 1 for `Fin 0 → ℝ`).

## Appendix — exact Lean statements

```lean
-- Grammar/PosteriorTransfer.lean
theorem HasLeadingTerm.tendsto_div_same_pair (h₁ : HasLeadingTerm Z₁ c₁ lam k)
    (h₂ : HasLeadingTerm Z₂ c₂ lam k) (hc₂ : c₂ ≠ 0) :
    Tendsto (fun N => Z₁ N / Z₂ N) atTop (𝓝 (c₁ / c₂)) := by
```

```lean
-- Grammar/PosteriorTransfer.lean
noncomputable def posteriorExpectation (K : (Fin d → ℝ) → ℝ) (p : TubeWeight d)
    (φ : (Fin d → ℝ) → ℝ) (N : ℝ) : ℝ :=
```

```lean
-- Grammar/PosteriorTransfer.lean
theorem tendsto_posteriorExpectation_of_hasLeadingTerm {K φ : (Fin d → ℝ) → ℝ}
    {p : TubeWeight d} {cφ c₁ lam : ℝ} {k : ℕ}
    (hφ : HasLeadingTerm (R.boltzmannIntegral φ K p) cφ lam k)
    (h₁ : HasLeadingTerm (R.boltzmannIntegral (fun _ => 1) K p) c₁ lam k) (hc₁ : 0 < c₁) :
    (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p φ) atTop (𝓝 (cφ / c₁)) :=
```

```lean
-- Grammar/ProductChartPosterior.lean
theorem normaliserCoeff_pos (hact : (R.activeCoords Ps).Nonempty) (hp0 : ∀ x, 0 ≤ p.w x)
    (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d)) (hI₀ : I₀ ⊆ (Ps i₀).e.support)
    (hne₀ : I₀.Nonempty) (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact) :=
```

```lean
-- Grammar/ProductChartPosterior.lean
theorem tendsto_posteriorExpectation_of_productCharts (hact : (R.activeCoords Ps).Nonempty)
    {F : (Fin d → ℝ) → ℝ} (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
    (hFm : Measurable F) (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hp0 : ∀ x, 0 ≤ p.w x) (hr0 : ∀ i x, 0 ≤ (Ps i).r x) (i₀ : ι) (I₀ : Finset (Fin d))
    (hI₀ : I₀ ⊆ (Ps i₀).e.support) (hne₀ : I₀.Nonempty)
    (hall : ∀ j ∈ I₀, (Ps i₀).ratio j = R.coverLam Ps hact)
    (hdeg : I₀.card - 1 = R.coverDeg Ps hact)
    (hpos : 0 < volume ((Ps i₀).dominantFace (fun i => (Ps i).e.support) ε I₀ hne₀
      (fun _ => (1 : ℝ)) p)) :
    0 < R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact) ∧
      (∀ᶠ N in atTop, 0 < R.boltzmannIntegral (fun _ => 1) K p N) ∧
      Tendsto (R.posteriorExpectation K p F) atTop
        (𝓝 (R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact)
          (R.coverDeg Ps hact) /
          R.normaliserCoeff Ps hK0 hε hεb hpc hp hK (R.coverLam Ps hact) (R.coverDeg Ps hact))) :=
```

```lean
-- Grammar/ProductChartPosterior.lean
theorem productCoeffD_add {F G : (Fin d → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W)
    (hGc : ∀ i, ContinuousOn (fun y => G ((R.chart i).φ y)) (Ps i).W)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hG : Integrable (fun x => G x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hFGc : ∀ i, ContinuousOn (fun y => (fun x => F x + G x) ((R.chart i).φ y)) (Ps i).W)
    (hFGm : Measurable fun x => F x + G x)
    (hFG : Integrable (fun x => (fun x => F x + G x) x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε hεb hFGc hpc hFGm hFG hK lam₀ k₀ =
      R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK lam₀ k₀ +
        R.productCoeffD Ps hK0 hε hεb hGc hpc hGm hG hK lam₀ k₀ :=
```

```lean
-- Grammar/ProductChartPosterior.lean
theorem productCoeffD_eq_of_cutoff {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hεb₁ : ∀ i, ε₁ ≤ (Ps i).b)
    (hε₂ : 0 < ε₂) (hεb₂ : ∀ i, ε₂ ≤ (Ps i).b) {F : (Fin d → ℝ) → ℝ}
    (hFc : ∀ i, ContinuousOn (fun y => F ((R.chart i).φ y)) (Ps i).W) (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty, lam₀ ≤ R.productPieceLam Ps i I hne)
    (hk : ∀ i I, I ⊆ (Ps i).e.support → ∀ hne : I.Nonempty,
      R.productPieceLam Ps i I hne = lam₀ → R.productPieceMult Ps i I hne - 1 ≤ k₀) :
    R.productCoeffD Ps hK0 hε₁ hεb₁ hFc hpc hFm hF hK lam₀ k₀ =
      R.productCoeffD Ps hK0 hε₂ hεb₂ hFc hpc hFm hF hK lam₀ k₀ :=
```

```lean
-- Grammar/ProductChartTiedStrata.lean
noncomputable def minimalSet (lam : ℝ) : Finset (Fin d) :=
```

```lean
-- Grammar/ProductChartTiedStrata.lean
theorem tied_iff (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (Ps i).e.support) (hne : I.Nonempty) :
    ((Ps i).pieceLam I hne = R.coverLam Ps hact ∧ (Ps i).pieceMult I hne - 1 = R.coverDeg Ps hact) ↔
      ((Ps i).minimalSet (R.coverLam Ps hact) ⊆ I ∧
        ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1) := by
```

```lean
-- Grammar/ProductChartTiedStrata.lean
theorem tiedSum_of_all_minimal {lam₀ : ℝ} {k₀ : ℕ} (hall : ∀ j ∈ I, P.ratio j = lam₀)
    (hdeg : I.card - 1 = k₀)
    {At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)}
    (hAt : P.IsPieceAtlasData hK0 hε hεb hD hFm hF hK I hI hne At) :
    ∑ σ ∈ At.tied lam₀ k₀, (At.cell σ).coeff =
      2 ^ I.card * ((Real.Gamma lam₀ / ((I.card - 1).factorial : ℝ) * ∏ j ∈ I, 1 / (P.e j : ℝ)) *
        ∫ z in (P.pieceDensity hε hεb hD I hI hne p).base,
          (P.pieceDensity hε hεb hD I hI hne p).beta z *
            (scalarPhase I hne P.u P.e z ^ (-lam₀) *
              R.pieceAmp i I hne P.h P.v (F := F) (p := p) z 0)) := by
```

```lean
-- Grammar/ProductChartTiedStrata.lean
theorem productCoeffD_extremal_eq_sum_tied :
    R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) =
      ∑ i, ∑ I ∈ ((Ps i).e.support.powerset.filter fun I => I.Nonempty).filter
          (fun I => (Ps i).minimalSet (R.coverLam Ps hact) ⊆ I ∧
            ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1),
        scalarAtlasPieceCoeff' (R.productAtlasesD Ps hK0 hε hεb hFc hpc hFm hF hK)
          (R.coverLam Ps hact) (R.coverDeg Ps hact) i I := by
```

```lean
-- Grammar/ProductChartTiedStrata.lean
theorem productCoeffD_extremal_eq_sum_minimal
    (hsupp : ∀ i, ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1 →
      (Ps i).minimalSet (R.coverLam Ps hact) = (Ps i).e.support) :
    R.productCoeffD Ps hK0 hε hεb hFc hpc hFm hF hK (R.coverLam Ps hact) (R.coverDeg Ps hact) =
      ∑ i, if hM : ((Ps i).minimalSet (R.coverLam Ps hact)).card = R.coverDeg Ps hact + 1 then
        2 ^ ((Ps i).minimalSet (R.coverLam Ps hact)).card *
          ((Real.Gamma (R.coverLam Ps hact) /
              ((((Ps i).minimalSet (R.coverLam Ps hact)).card - 1).factorial : ℝ) *
            ∏ j ∈ (Ps i).minimalSet (R.coverLam Ps hact), 1 / ((Ps i).e j : ℝ)) *
          ∫ z in ((Ps i).pieceDensity (D := fun i => (Ps i).e.support) hε (hεb i) rfl
```

```lean
-- Grammar/OneChartProductExample.lean
theorem ofChart_weight_eq_one (C : ResolutionChart d) {x : Fin d → ℝ} (hx : x ∈ C.φ '' C.dom) :
    (ofChart C).weight () x = 1 := by
```

```lean
-- Grammar/OneChartProductExample.lean
def ProductMonomialChart.ofUnit {d : ℕ} (C : ResolutionChart d) {K : (Fin d → ℝ) → ℝ}
    (e h : Fin d →₀ ℕ) (W : Set (Fin d → ℝ)) (W_open : IsOpen W) (dom_subset : C.dom ⊆ W)
    (monomial : IsMonomialChart K C.φ C.dom e h W) (u : (Fin d → ℝ) → ℝ) (u_cont : ContinuousOn u W)
    (u_ne : ∀ y ∈ W, u y ≠ 0) (phase_eq : ∀ y ∈ W, K (C.φ y) = u y * monomialEval y e)
    (v : (Fin d → ℝ) → ℝ) (v_cont : ContinuousOn v W)
    (det_eq : ∀ y ∈ W, (fderiv ℝ C.φ y).det = v y * monomialEval y h) (T : Set (Fin d → ℝ))
    (T_compact : IsCompact T) (T_nonempty : T.Nonempty) (T_zero : ∀ x ∈ T, ∀ j ∈ e.support, x j = 0)
    (b : ℝ) (b_pos : 0 < b) (dom_eq : C.dom = productDom e.support T b)
    (unit_indep : ∀ y ∈ C.dom, u y = u (zeroOn e.support y)) :
    ProductMonomialChart (ResolutionCover.ofChart C) () K where
```

```lean
-- Grammar/OneChartProductExample.lean
theorem productCoeffD_eq_sqrt_pi :
    (ResolutionCover.ofChart chart).productCoeffD Ps hK0 one_pos hεb hFc hpc hFm hF hK
      ((ResolutionCover.ofChart chart).coverLam Ps hact)
      ((ResolutionCover.ofChart chart).coverDeg Ps hact) = Real.sqrt Real.pi := by
```

```lean
-- Grammar/OneChartProductExample.lean
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ y in box, Real.exp (-N * K y)) ~[atTop]
      fun N => Real.sqrt Real.pi * (N ^ (-(1 / 2 : ℝ)) * Real.log N) := by
```

```lean
-- Grammar/ProductChartPositivity.lean
def IsPieceAtlasData
    (At : FiniteScalarUnitAtlas (d - (I.card - 1 + 1)) (R.pieceIntegral D ε i I F K p)) : Prop :=
```

```lean
-- Grammar/ProductChartPositivity.lean
def dominantFace (F : (Fin d → ℝ) → ℝ) (p : TubeWeight d) :
    Set (Fin (d - (I.card - 1 + 1)) → ℝ) :=
```

```lean
-- Grammar/ConstantUnitKernel.lean
noncomputable def boxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
```

```lean
-- Grammar/ScalarUnitKernel.lean
noncomputable def scalarBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
```

```lean
-- Grammar/MonomialAmplitudeAsymptotic.lean
noncomputable def amplitudeCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ :=
```

```lean
-- Grammar/MonomialAmplitudeAsymptotic.lean
noncomputable def faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
```

```lean
-- Grammar/MonomialAmplitudeAsymptotic.lean
noncomputable def residualWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : ℝ :=
```

```lean
-- Grammar/MonomialAmplitudeAsymptotic.lean
noncomputable def faceLeadConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ :=
```

```lean
-- Grammar/SymmetricScalarUnitCells.lean
noncomputable def coeff : ℝ :=
```