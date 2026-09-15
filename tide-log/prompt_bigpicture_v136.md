# Consult #136 — CLOSURE AUDIT of the chart-pushforward identity (P1 of #135): ℛ^μ_c = sum of face-density pushforwards

All six units of your P1 design are landed (grammar main `3b39911`, 780 modules, zero sorry/axiom; `#print axioms` clean on both headline identities). Same protocol: audit the SIGNATURES (proofs compile), the paper wording, then say CLOSE or name the missing unit.

## CDLXIV SmoothChartResidueCollar (unit 1 + the collar)
```
theorem isClosed_zeroCard (d : ℕ) (c : ℕ) :
    IsClosed {v : Fin d → ℝ | c + 1 ≤ ((univ : Finset (Fin d)).filter fun i => v i = 0).card}
theorem isCompact_deepSet (d : ℕ) (b : ℝ) (c : ℕ) : IsCompact (deepSet d b c)
theorem continuousOn_amp_pair :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      (Ξ.amp Y p).amp z.1 z.2) (univ ×ˢ closedBox _ (Y.T.a p.1))
theorem exists_bound_amp : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ∀ v ∈ closedBox _ (Y.T.a p.1),
    |(Ξ.amp Y p).amp s v| ≤ M
noncomputable def ampObs {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1)
theorem ampObs_amp {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (v : Fin ((Ξ.X Y).da p) → ℝ) :
    (Ξ.ampObs Y p hG).amp s v = ((Ξ.withF G hG).amp Y p).amp s v := rfl
theorem exists_bound_amp_withF {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      ∀ v ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1), |(Ξ.ampObs Y p hG).amp s v| ≤ M
theorem amp_withF_eq {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    (Ξ.ampObs Y p hG).amp s v =
      (Ξ.X Y).ρloc p.1 ((Ξ.X Y).Tm p s v) * G (Ξ.divPt Y p s v)
theorem continuousOn_divPt_pair :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      Ξ.divPt Y p z.1 z.2) (univ ×ˢ closedBox _ (Y.T.a p.1))
theorem gv_divPt_eq (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.R.gv (Ξ.divPt Y p s v) = Y.T.ψ p.1 ((Ξ.X Y).Tm p s v)
theorem continuousOn_ψ_Tm :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      Y.T.ψ p.1 ((Ξ.X Y).Tm p z.1 z.2)) (univ ×ˢ closedBox _ (Y.T.a p.1))
theorem eventually_amp_zero_of_deep {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) :
    ∀ᶠ z in 𝓝 (s, v), z.2 ∈ closedBox _ (Y.T.a p.1) →
      (Ξ.ampObs Y p hG).amp z.1 z.2 = 0
theorem exists_collar {c : ℕ} {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      ∀ v ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1),
      ∀ v' ∈ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c, dist v v' < ε →
        (Ξ.ampObs Y p hG).amp s v = 0
theorem continuous_mono' {ι : Type*} [Fintype ι] (a : ι → ℕ) : Continuous (mono a)
theorem exists_bound_residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {ε : ℝ}
    (b : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ι → ℝ, (∀ i, ε ≤ w i ∧ w i ≤ b) → |residueWeight h k μ w| ≤ C
theorem volume_box_lt_top {ι : Type*} [Fintype ι] (b : ℝ) : volume (box ι b) < ⊤
theorem integrable_faceIntegrand {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) (J : Finset (Fin ((Ξ.X Y).da p)))
    (hJc : J.card = c) (μ : ℝ) :
    Integrable (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ
          z.2)
      ((Ξ.piecePresentation Y p).ν.prod
        (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1))))
```
Notes. `ampObs Y p hG := (Ξ.withF G hG).amp Y p` retyped over `Ξ.X Y` (the chart machinery is F-independent; needed to make rewriting work). `amp_withF_eq` is the factorisation on the CLOSED box (`ρloc = ω·|jacUnit|·prior∘ψ`, F-free; `G` enters only at the divisor point). `exists_collar`: `O := {z | ∀ᶠ z' in 𝓝 z, z'.2 ∈ closedBox → amp z' = 0}` is open and contains `S × deepSet` (by `eventually_amp_zero_of_deep`: depth ≥ c+1 at the divisor point; either it is in `D_(c+1)` and `G` vanishes on a neighbourhood, or `π(divPt) ∉ tsupport prior` and `prior∘ψ∘Tm` vanishes nearby); `IsCompact.exists_thickening_subset_open` gives ε. `integrable_faceIntegrand`: pointwise bound `M·C` off the collar (`C` bounds residueWeight on `[ε,b]^(Jᶜ)`), zero on the collar (the point with one more zero coordinate is in the deep set at sup-distance `w_i < ε`), finite product measure.

## CDLXV SmoothChartResidueMeasure (units 2–3, 5)
```
noncomputable def faceRef :
    Measure (Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ))
instance : IsFiniteMeasure (Ξ.faceRef Y p J)
theorem faceRef_eq_restrict : Ξ.faceRef Y p J =
    ((Ξ.piecePresentation Y p).ν.prod volume).restrict
      (Set.univ ×ˢ box {i // ¬ inJ J i} (Y.T.a p.1))
theorem ae_faceRef_mem_box :
    ∀ᵐ z ∂(Ξ.faceRef Y p J), z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)
theorem glue_mem_closedBox_of_mem_box {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : glue J 0 w ∈ closedBox _ (Y.T.a p.1)
noncomputable def faceNorm' : ℝ := ∏ j : {i // inJ J i}, (2 * ((Ξ.X Y).kA p j : ℝ))⁻¹
theorem faceNorm'_pos : 0 < Ξ.faceNorm' Y p J
noncomputable def faceDensity (μ : ℝ)
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : ℝ
theorem faceDensity_nonneg (μ : ℝ)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) : 0 ≤ Ξ.faceDensity Y p J μ z
theorem measurable_faceDensity (μ : ℝ) : Measurable (Ξ.faceDensity Y p J μ)
noncomputable def faceMap
    (z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)) : Ξ.R.U
theorem measurable_faceMap : Measurable (Ξ.faceMap Y p J)
theorem faceMap_eq_divPt {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    Ξ.faceMap Y p J z = Ξ.divPt Y p z.1 (glue J 0 z.2)
theorem faceDensity_mul_eq {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (μ : ℝ)
    {z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ)}
    (hz : z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1)) :
    Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z) =
      Ξ.faceNorm' Y p J * ((Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ
          z.2)
noncomputable def faceMeasureU (μ : ℝ) : Measure Ξ.R.U
noncomputable def faceMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c)
noncomputable def chartResidueMeasure (μ : ℝ) (c : ℕ) : Measure (Ξ.stratumOpen c)
theorem measurableEmbedding_val (c : ℕ) :
    MeasurableEmbedding (Subtype.val : Ξ.stratumOpen c → Ξ.R.U)
theorem integral_faceMeasure_eq_faceMeasureU {c : ℕ} {G : Ξ.R.U → ℝ} (hGt : Ξ.IsTest c G)
    (μ : ℝ) : ∫ x, G x.1 ∂(Ξ.faceMeasure Y p J μ c) = ∫ y, G y ∂(Ξ.faceMeasureU Y p J μ)
theorem integrable_faceDensity_mul {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) :
    Integrable (fun z => Ξ.faceDensity Y p J μ z * G (Ξ.faceMap Y p J z)) (Ξ.faceRef Y p J)
theorem integral_faceDensity_mul_eq_dlogResidueInt {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (μ : ℝ) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) :
    ∫ w in box {i // ¬ inJ J i} (Y.T.a p.1),
        Ξ.faceDensity Y p J μ (s, w) * G (Ξ.faceMap Y p J (s, w)) =
      dlogResidueInt ((Ξ.X Y).kA p) ((Ξ.X Y).hA p) μ (Y.T.a p.1) J ((Ξ.ampObs Y p hG).amp s)
theorem integral_faceMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) :
    ∫ x, G x.1 ∂(Ξ.faceMeasure Y p J μ c) =
      ∫ s, dlogResidueInt ((Ξ.X Y).kA p) ((Ξ.X Y).hA p) μ (Y.T.a p.1) J
        ((Ξ.ampObs Y p hG).amp s) ∂(Ξ.piecePresentation Y p).ν
```
Notes. `faceDensity` uses `ρf` (the smooth global extension of `ρloc`, equal on the box; measurable) so the density is measurable; `faceMap` goes through the measurable `chartInv` (= `φ⁻¹` on the target) and equals `divPt` on the box. `faceMeasure := Measure.comap Subtype.val faceMeasureU` (restriction along the measurable embedding `X ↪ U`), NOT a restriction of the parameter space (your §2.3 suggestion) — is that acceptable? (`comap` along a measurable embedding satisfies `comap_apply : comap f μ s = μ (f '' s)` and `map f (comap f μ) = μ.restrict (range f)`, which is all we use.)

## CDLXVI SmoothChartResidueIdentity (units 4, 6)
```
theorem integrable_faceMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (hJc : J.card = c)
    (μ : ℝ) : Integrable (fun x : Ξ.stratumOpen c => G x.1) (Ξ.faceMeasure Y p J μ c)
theorem faceMeasure_lt_top_of_isCompact {c : ℕ} (hJc : J.card = c) (μ : ℝ)
    {C : Set (Ξ.stratumOpen c)} (hC : IsCompact C) : Ξ.faceMeasure Y p J μ c C < ⊤
theorem chartResidueMeasure_lt_top_of_isCompact (μ : ℝ) (c : ℕ) {C : Set (Ξ.stratumOpen c)}
    (hC : IsCompact C) : Ξ.chartResidueMeasure Y μ c C < ⊤
instance (μ : ℝ) (c : ℕ) : IsFiniteMeasureOnCompacts (Ξ.chartResidueMeasure Y μ c)
instance (μ : ℝ) (c : ℕ) : (Ξ.chartResidueMeasure Y μ c).Regular
theorem integral_chartResidueMeasure_test {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) (μ : ℝ) :
    ∫ x, G x.1 ∂(Ξ.chartResidueMeasure Y μ c) =
      ∑ I, ∫ s, (Ξ.withF G hG).pieceResidueSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν
theorem residueConst_mul_integral_chartResidueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hGt : Ξ.IsTest c G) :
    residueConst μ c * ∫ x, G x.1 ∂(Ξ.chartResidueMeasure Y μ c) = Ξ.T Y μ c G hG
theorem stratumMeasure_eq_smul_chartResidueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero =
      ENNReal.ofReal (residueConst μ c) • Ξ.chartResidueMeasure Y μ c
theorem chartResidueMeasure_eq_residueMeasure {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.residueMeasure Y hc hzero
theorem chartResidueMeasure_compl_exactStratum {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0
theorem chartResidueMeasure_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
    {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Ξ.chartResidueMeasure Y μ c = Ξ.chartResidueMeasure Y' μ c
```
Notes. Regularity: `IsFiniteMeasureOnCompacts` from `faceMeasure_lt_top_of_isCompact` (cutoff `χ = 1` on the compact, `0 ≤ χ ≤ 1`, `IsTest`; `∫⁻ 1_(e⁻¹C) D ≤ ∫⁻ ofReal(D·χ∘e) = ofReal ∫ D·χ∘e < ∞` by the collar integrability), then Mathlib's `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` (X is σ-compact — locally compact + second countable — and pseudometrisable — regular + second countable — by instances). Identity: `residueConst·∫ G dchart = T[G]` via `coeff_eq_residueSum` (CDLIII) for `withF G`; then `eq_stratumMeasure_of_tests` on `ofReal(residueConst) • chart` (Regular via `Regular.smul`); `chart = ℛ` by cancelling `((c−1)!/Γ)·(Γ/(c−1)!) = 1` (needs `μ > 0`).

## Paper wording now in the mirror (after the residue paragraph)
> On X the intrinsically defined normalised residue measure is exactly the finite sum of the pushforwards of the multiplicity-normalised simple-face densities in any resolved chart transport [faceDensity][chartResidueMeasure][chartResidueMeasure_eq_residueMeasure]: the face measures are finite on compact subsets of X because an observable vanishing near D_(c+1) has amplitude vanishing on a uniform collar of the deeper faces [exists_collar], the chart sum is therefore a regular measure, and it integrates smooth tests to the residue sums, so uniqueness identifies it with ℛ^μ_c and gives ν^μ_c = Γ(μ)/(c−1)! · Σ_(pieces, faces) (face density)_* [stratumMeasure_eq_smul_chartResidueMeasure]. Equivalently, ℛ^μ_c is the sum over normal sides of the iterated logarithmic density residue of (K∘π)^(−μ)μ_U, each normal side contributing (2k_j)^(−1) per wall: for a simple-pole density ω the ordinary residue along E = {f = 0} is the tangential density (|f|ω)|_E/|df|, invariant under replacing f by a nonvanishing multiple, its iterates along transverse walls commute, and a full two-sided c-fold crossing contributes 2^c/∏_j 2k_j times the ordinary iterated density residue. The measure identity and its chart-independence are formalised; the terminology of iterated density residues describes the explicit local density formula rather than invoking a separately formalised manifold-level residue calculus. No identification with a Laurent coefficient of a meromorphically continued zeta function, and no Radon extension across D_(c+1), is asserted.

(The artifact's Definition B passage was rewritten per your §1B: `|f|ω`, the log-collar formula `(2 log 1/ε)⁻¹ ∫_(ε<|f|<r) g ω`, symmetric iteration, normal-side sum with `2^c/∏2k_j`, the `x^(2k)` sanity check `ℛ = δ₀/k`; A′ labelled a truncated negative moment, expected classical characterisation, not formalised.)

## Questions
(a) Audit the ★★★ statements: does `chartResidueMeasure_eq_residueMeasure` (with `hμ hc hzero`) say what the paper sentence says? Is the `comap`-along-the-embedding construction of the face measure on X acceptable, and is anything lost by not restricting the parameter space (the raw `faceMeasureU` on U is a well-defined possibly-infinite Borel measure — fine)? Any hidden dependence on the transport in the DEFINITION of `chartResidueMeasure` that the paper sentence "in any resolved chart transport" hides (the sum is over `Y`'s pieces; the theorem is for every `Y`; independence proved via ℛ)?
(b) The collar argument: is the two-case analysis (`divPt ∈ D_(c+1)` or `π(divPt) ∉ tsupport prior`) complete? (It uses `depth(divPt) ≥ c+1` from the ≥ c+1 zero coordinates, and `K(π(divPt)) = 0`.)
(c) Wording check of the mirror paragraph above (overclaims?), and whether "Definition B made a theorem" is fair in the HEADLINES row given no separate density-residue calculus exists.
(d) CLOSE? If yes, final ranking of what remains (depth-one x²y² by the direct route; scaling to drop the box support of CDLXII–CDLXIII; the k_i = 0 exponents; subtype-S packaging; zeta continuation) — and whether the Section-4 programme of the grammar paper should now be declared complete for the paper's purposes.
