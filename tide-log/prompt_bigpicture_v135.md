# Consult #135 — DESIGN of the structural unit: the stratum measure as an explicit chart-pushforward, and the iterated density residue ("Definition B")

Context. The residue programme is closed (consults #132–#134): `ν^μ_c := RealRMK.rieszMeasure Λ` on `X = U ∖ D_(c+1)`, `ℛ^μ_c := ((c−1)!/Γ(μ))·ν`, carried by `S^μ_c`, unique among regular measures by smooth tests, transport-independent, and in every chart `∫ G dℛ = residueSum`-type face integrals. Main `7077a28`, 777 modules. The user asked how the residue is defined intrinsically WITHOUT coordinates; I answered with two descriptions and put both in the artifact: (A) the formalised one — through the asymptotics (`∫F dℛ = ((c−1)!/Γ(μ)) lim N^μ (log N)^(−(c−1)) ∫ F e^(−NK∘π) μ_U`, and the equivalent sublevel-set form `lim_(δ→0) c! (log 1/δ)^(−c) ∫_(K∘π>δ) F (K∘π)^(−μ) μ_U`, the constant from the simplex volume after `t_j = 2k_j log(1/|u_j|)` — please CHECK this constant); (B) the classical iterated density residue: for a positive density `ω` with a simple pole along a hypersurface `E` with defining function `f`, `Res_E ω := (fω)|_E / |df|` (`∫_E g Res = lim (2ε)^(−1) ∫_(|f|<ε) g ω`), invariant under `f ↦ af`; iterated along the `c` transversal walls (symmetric for densities); normalised against the divisor `div(K∘π) = Σ 2k_j E_j` (dividing by `2k_j` per wall). The user now says: PROCEED WITH THAT STRUCTURAL UNIT — the identification of `ℛ` (Definition A) with Definition B as a measure object, i.e. Astra #133/#134's "explicit chart-pushforward measure = ν". I need a precise formal design.

## 1. The infrastructure the formula lives in
Resolved core transport `Y : ResolvedCoreTransport R hKc prior` wraps a Euclidean `NormalisedCoreTransport d K prior`:
```
structure NormalisedCoreTransport (d) (K prior) where
  ι : Type; [fin : Fintype ι]; a : ι → ℝ (box half-sides, > 0); ψ : ι → (Fin d → ℝ) → (Fin d → ℝ) (chart maps, analytic on V i ⊇ centeredBox d (a i));
  k : ι → Fin d → ℕ; phaseConst = 1 here; phase_eq : K (ψ i u) = ∏ j, u j ^ (2 * k i j) on V i;
  h : ι → Fin d → ℕ; jacUnit : ι → (Fin d → ℝ) → ℝ (analytic, nonvanishing); jac_eq : (fderiv (ψ i) u).det = jacUnit i u * ∏ u^h;
  ω : ι → (Fin d → ℝ) → ℝ (smooth chart weights in [0,1]); tail; transport : ∑ i, (coreSource (ψ i) (ω i) (a i) prior).map (ψ i) + tail = volume.withDensity (ofReal prior)
```
and on the resolved side `Y.φ i : OpenPartialHomeomorph R.U (Fin d → ℝ)` with `Y.T.ψ i u = R.gv ((Y.φ i).symm u)`. Pieces `PIdx := Σ i : ι, CoordSign d` (chart × orthant sign σ). Per piece:
```
abbrev PIdx : Type := Σ _ : X.T.ι, WaterFilling.CoordSign d

/-- The core measure of a piece: the weighted orthant-box measure pushed along the chart. -/
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (X.T.a p.1))).withDensity fun w =>
...
noncomputable def coreMeasure (p : X.PIdx) : Measure (Fin d → ℝ) :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (X.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (X.T.h p.1) w * X.ρf p.1 w)).map (X.T.ψ p.1)

/-- The pieces of a chart exhaust its transported core source. -/
...
noncomputable def da (p : X.PIdx) : ℕ := Fintype.card {j // inJ (X.act p.1) j}

theorem da_le (p : X.PIdx) : X.da p ≤ d := by
  have := Fintype.card_subtype_le (inJ (X.act p.1))
  rwa [Fintype.card_fin] at this
...
noncomputable def Tm (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
    Fin d → ℝ :=
  affineMap (X.eqv p) p.2 (X.sc p s) v

theorem Tm_eq_refl_glueE (p : X.PIdx) (s : Base (X.act p.1) (X.T.a p.1)) (v : Fin (X.da p) → ℝ) :
...
noncomputable def amp (p : X.PIdx) :
    SmoothAmplitudeFamily (Base (X.act p.1) (X.T.a p.1)) (X.da p) (X.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine (X.continuous_sc p) (X.eqv p) p.2 (X.contDiff_G p.1) (X.T.a p.1)

/-- The active phase exponents of a piece. -/
```
(`Base (act) (a)` = the base box in the INACTIVE coordinates (those with `k i j = 0`); `da p` = number of active coordinates; `Tm p s v` = the affine map putting active coordinates `v` (in the orthant σ) and base coordinates `s` together into `Fin d → ℝ`; `X.eqv p : Fin (da p) ≃ {j // inJ (act) j}`.) The amplitude family of a piece:
```
noncomputable def SmoothAmplitudeFamily.ofAffine {S : Type*} [TopologicalSpace S]
    {sc : S → {i // ¬ inJ J i} → ℝ} (hsc : Continuous sc) (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) {G : (Fin d → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (b : ℝ) :
    SmoothAmplitudeFamily S da b where
  amp s v := G (affineMap e σ (sc s) v)
  smooth s := hG.comp (contDiff_affineMap e σ (sc s))
  deriv_cont m := by
    simp only [pdMulti_comp_affineMap]
    exact (continuous_const.mul ((contDiff_pdMulti hG _ _).continuous.comp
      ((continuous_affineMap_pair e σ).comp
        ((hsc.comp continuous_fst).prodMk continuous_snd)))).continuousOn

...
theorem SmoothAmplitudeFamily.ofAffine_amp {S : Type*} [TopologicalSpace S]
    {sc : S → {i // ¬ inJ J i} → ℝ} (hsc : Continuous sc) {G : (Fin d → ℝ) → ℝ}
    (hG : ContDiff ℝ ∞ G) (b : ℝ) (s : S) (v : Fin da → ℝ) :
    (SmoothAmplitudeFamily.ofAffine hsc e σ hG b) s v = G (affineMap e σ (sc s) v) := rfl

end SmoothEngine

end Grammar

```
so `(amp p).amp s v` = (chart weight ω · |jacUnit| · prior∘ψ · F∘φ⁻¹ ... assembled by `ofAffine` from the smooth `G := ...` at the point `Tm p s v`) — the F-dependence is `amp_withF`-type linear (F enters the product; `SmoothAmplitudeFamily.ofAffine_amp` gives the pointwise formula). Face points and divisor points:
```
noncomputable def facePt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Fin d → ℝ := (Ξ.X Y).Tm p s v

...
noncomputable def divPt (p : (Ξ.X Y).PIdx) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    (v : Fin ((Ξ.X Y).da p) → ℝ) : Ξ.R.U := (Y.φ p.1).symm (Ξ.facePt Y p s v)

```
The residue objects (CDLIII):
```
noncomputable def residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) (w : ι → ℝ) : ℝ :=
  mono h w * mono (fun i => 2 * k i) w ^ (-μ)

theorem residueWeight_nonneg {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {b : ℝ}
    {w : ι → ℝ} (hw : w ∈ box ι b) : 0 ≤ residueWeight h k μ w :=
  mul_nonneg (mono_nonneg_of_mem_box hw h) (Real.rpow_nonneg (mono_nonneg_of_mem_box hw _) _)
...
noncomputable def dlogResidueInt (k h : Fin d → ℕ) (μ b : ℝ) (J : Finset (Fin d))
    (A : (Fin d → ℝ) → ℝ) : ℝ :=
  (∏ j : {i // inJ J i}, (2 * (k j : ℝ))⁻¹) *
    ∫ w in box {i // ¬ inJ J i} b,
      A (glue J 0 w) * residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) μ w

...
noncomputable def residueConst (μ : ℝ) (c : ℕ) : ℝ := Real.Gamma μ / ((c - 1).factorial : ℝ)

theorem residueConst_pos {μ : ℝ} (hμ : 0 < μ) (c : ℕ) : 0 < residueConst μ c :=
  div_pos (Real.Gamma_pos_of_pos hμ) (Nat.cast_pos.2 (Nat.factorial_pos _))

/-- A face all of whose walls carry simple poles has resonant Taylor order zero. -/
...
noncomputable def simpleFaces (p : (Ξ.X Y).PIdx) (μ : ℝ) (c : ℕ) :
    Finset (Finset (Fin ((Ξ.X Y).da p))) :=
  (univ : Finset (Finset (Fin ((Ξ.X Y).da p)))).filter fun J =>
    J.card = c ∧ ∀ j ∈ J, 2 * ((Ξ.X Y).kA p j : ℝ) * μ = (Ξ.X Y).hA p j + 1

/-- The residue term of a piece at a base point: the sum over its simple-pole faces of the
...
noncomputable def pieceResidueSum (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) (μ : ℝ) (c : ℕ) : ℝ :=
  ∑ J ∈ Ξ.simpleFaces Y ((Ξ.X Y).en I) μ c,
    dlogResidueInt ((Ξ.X Y).kA ((Ξ.X Y).en I)) ((Ξ.X Y).hA ((Ξ.X Y).en I)) μ
      (Y.T.a ((Ξ.X Y).en I).1) J ((Ξ.amp Y ((Ξ.X Y).en I)).amp s)

...
noncomputable def residueSum (μ : ℝ) (c : ℕ) : ℝ :=
  residueConst μ c * ∑ I, ∫ s, Ξ.pieceResidueSum Y I s μ c ∂((Ξ.decomp Y).chart I).ν

theorem pieceStratumSum_eq_residue {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (I : Fin (Fintype.card (Ξ.X Y).PIdx))
    (s : Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1)) :
...
theorem coeff_eq_residueSum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (hF : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), Ξ.F P = 0) :
    Ξ.coeff Y μ (c - 1) = Ξ.residueSum Y μ c := by
  rw [Ξ.coeff_eq_stratumSum Y hc hF μ]
  unfold stratumSum residueSum
  rw [Finset.mul_sum]
```
with `glue J 0 w` inserting `0` in the `J` coordinates and `w : {i // ¬ inJ J i} → ℝ` elsewhere:
```
/home/daniel/timaeus/sri/learning-theory/lean/grammar/Grammar/SmoothFaceSplit.lean:120:def glue (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) : Fin d → ℝ :=
/home/daniel/timaeus/sri/learning-theory/lean/grammar/Grammar/SmoothFaceSplit.lean-121-  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm (u, w)
/home/daniel/timaeus/sri/learning-theory/lean/grammar/Grammar/SmoothFaceSplit.lean-122-
/home/daniel/timaeus/sri/learning-theory/lean/grammar/Grammar/SmoothFaceSplit.lean-123-theorem glue_apply_of_mem (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) {i : Fin d}

```
The measure objects (CDLVI):
```
noncomputable def stratumMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  RealRMK.rieszMeasure (Ξ.Λ Y hc hzero)

instance {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    (Ξ.stratumMeasure Y hc hzero).Regular :=
...
theorem integral_stratumMeasure_test {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) (hGt : Ξ.IsTest c G) :
    ∫ x, G x.1 ∂(Ξ.stratumMeasure Y hc hzero) = Ξ.T Y μ c G hG := by
  rw [← Ξ.Λ_toCc Y hc hzero hG hGt]
  exact Ξ.integral_stratumMeasure Y hc hzero (Ξ.toCc c hG hGt)

...
theorem stratumMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
    Ξ.stratumMeasure Y hc hzero (Subtype.val ⁻¹' Ξ.exactStratum μ c)ᶜ = 0 := by
  set ν := Ξ.stratumMeasure Y hc hzero with hν
  have hopen : IsOpen (Subtype.val ⁻¹' Ξ.exactStratum μ c : Set (Ξ.stratumOpen c))ᶜ := by
    have : (Subtype.val ⁻¹' Ξ.exactStratum μ c : Set (Ξ.stratumOpen c))ᶜ =
...
noncomputable def residueMeasure {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c) :
    Measure (Ξ.stratumOpen c) :=
  ENNReal.ofReal ((c - 1).factorial / Real.Gamma μ) • Ξ.stratumMeasure Y hc hzero

theorem residueMeasure_compl_exactStratum {μ : ℝ} {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) :
...
theorem integral_residueMeasure_eq {μ : ℝ} (hμ : 0 < μ) {c : ℕ} (hc : 1 ≤ c)
    (hzero : Ξ.ZeroOrder μ c) {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∫ x, G x.1 ∂(Ξ.residueMeasure Y hc hzero) =
      ∑ I, ∫ s, (Ξ.withF G hG).pieceResidueSum Y I s μ c
        ∂(((Ξ.withF G hG).decomp Y).chart I).ν := by
...
theorem eq_stratumMeasure_of_tests {μ : ℝ} {c : ℕ} (hc : 1 ≤ c) (hzero : Ξ.ZeroOrder μ c)
    (ν' : Measure (Ξ.stratumOpen c)) [ν'.Regular]
    (h : ∀ (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G), Ξ.IsTest c G →
      ∫ x, G x.1 ∂ν' = Ξ.T Y μ c G hG) :
    ν' = Ξ.stratumMeasure Y hc hzero := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
```
And the monomial instance (CDLXIII) where everything is explicit (`amplitudeCoeff`, `faceProj`, `residualWeight` from the box headline):
```
noncomputable def faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if ratioExp h k i = l then 0 else u i

...
noncomputable def residualWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : ℝ :=
  ∏ i, if ratioExp h k i = l then 1 else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)

...
noncomputable def faceLeadConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ :=
  Real.Gamma l * β ^ (-l) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1
...
noncomputable def amplitudeCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ :=
  faceLeadConst h k l β * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u

...
noncomputable def monomialInsertion (η : (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∑ σ : Fin (m + 1) → Bool, amplitudeCoeff (fun _ => 0) k (lamStar k) 1 fun u => η (reflect σ u)

variable {prior : (Fin (m + 1) → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior)
  (hbox : tsupport prior ⊆ symBox (m + 1))

include hk hps hbox in
/-- ★★★ **The explicit normalised limit for every smooth insertion** (symmetric-box headline at
zero phase, square-parameter transport). -/
theorem monomial_tendsto_insertion {f : (Fin (m + 1) → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    Tendsto (normalised (lamStar k) (mstar k - 1) (partitionObs (monoPhase k) prior f)) atTop
      (𝓝 (monomialInsertion k fun x => prior x * f x)) := by
...
theorem monomial_integral_extremalStratumMeasure_eq
    (Y : ResolvedCoreTransport (monomialData k W hps hp0 hpc hpW).R
      (monomialData k W hps hp0 hpc hpW).hKc prior) {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ᶠ P in 𝓝ˢ ((monomialData k W hps hp0 hpc hpW).deepZeroFibre (mstar k)),
      f ((monomialData k W hps hp0 hpc hpW).R.gv P) = 0) :
    ∫ x, f ((monomialData k W hps hp0 hpc hpW).R.gv x.1)
        ∂((monomialData k W hps hp0 hpc hpW).extremalStratumMeasure Y
          (isExtremalData_monomial k W hps hp0 hpc hpW ⟨0, hk 0⟩) (one_le_mstar k ⟨0, hk 0⟩)) =
      monomialInsertion k fun x => prior x * f x := by
  unfold ResolvedData.extremalStratumMeasure
  rw [← (monomialData k W hps hp0 hpc hpW).coeff_withF_eq_integral_stratumMeasure Y
```

## 2. Candidate formal statements (please choose/redesign; give the unit list with costs)
(P1) GENERAL CHART-PUSHFORWARD IDENTITY. For each piece `p` and simple face `J` (|J| = c, all `2 k_j μ = h_j + 1`), define the measure on `U`
  `m_(p,J) := ((∏_(j∈J) (2 k_j)⁻¹) · [the F-free amplitude at the face point] · residueWeight (h|Jᶜ) (k|Jᶜ) μ w) d(volume on box_Jᶜ) ⊗ dν_p(s)`, pushed forward by `(s, w) ↦ divPt p s (glue J 0 w)`,
and prove `ν^μ_c = residueConst μ c · Σ_(p,J) (m_(p,J)).restrict X` as MEASURES on X. Proof route: both regular on X; agree on smooth compactly supported tests by `integral_stratumMeasure_test` + `coeff_eq_residueSum` + `ofAffine_amp` (to split `F∘φ⁻¹` off the amplitude) + change of variables for the pushforward; conclude by `Measure.ext_of_integral_eq_on_compactlySupported` (or `eq_stratumMeasure_of_tests`). Concerns: (i) regularity/local finiteness of `m_(p,J)` on X (the residual weight `∏ w^(h−2kμ)` may be non-integrable at the box boundary where more coordinates vanish — but those points lie in `D_(c+1)`, off X; is `m_(p,J).restrict X` locally finite? via `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`?); (ii) the map `(s,w) ↦ divPt` is continuous but its image is the face — pushforward of a density under an injective smooth map onto a submanifold: fine as a Measure, measurability via `Measure.map` with measurable map; (iii) the `Base` integration `∫ s ∂ν_p` — `(decomp Y).chart I).ν` is the base measure; how is it related to the core measure/prior? The statement is a Measure identity so `Measure.prod`/`Measure.map` of the product; (iv) do I even need `Measure.prod`, or can I state the identity on test functions only (`∫ G dν = Σ ∫∫ …`) — that we essentially HAVE (`integral_stratumMeasure_eq_residueSum`); the new content is the MEASURE object.
(P2) MONOMIAL INSTANCE FIRST. For `K = ∏ x_i^(2k_i)` (all `k_i > 0`, `φ` in the symmetric box): `ν^(λ*)_(m*)|_X = (Γ(λ*)/((m*−1)!)) · 2^(m*)/∏_J 2k_j · push_(ι_J)[ φ(0_J, z) ∏_(J^c) |z_j|^(−2k_jλ*) dz ]` where `ι_J : ℝ^(J^c) → W`, `z ↦ (0_J, z)`. Concrete, no transport bookkeeping (the test-function identity is CDLXIII's `monomial_integral_extremalStratumMeasure_eq`); needs: the explicit measure as `Measure.map ι_J (volume.withDensity …)` restricted to X, its regularity, and the equation `∫ f d(explicit) = monomialInsertion k (φf)` — i.e. converting `Σ_σ ∫_(unitBox) (φf)(faceProj (reflect σ u)) residualWeight u du` into `∫_(ℝ^(J^c)) …` (orthant decomposition of ℝ^(J^c) into 2^(d−m) sign patterns × unit box, using support in the box; the 2^m J-reflections give the factor `2^m`). Cost M. This is "Definition B" made explicit for the monomial family: the density on the subspace IS the iterated residue of `(K)^(−λ) φ dx` along the J-walls with the multiplicity normalisation.
(P3) DEFINITION B AS A CALCULUS: `Res_E` for densities on U with simple poles, invariance, iteration, and `ℛ = Res^(div K∘π)_S[(K∘π)^(−μ) μ_U]` in general — needs a notion of density with a simple pole along a normal-crossing divisor on the analytic manifold U, the collar limit, and the identification through charts. L (or L+).
(P4) DEFINITION A′ (sublevel sets): `∫F dℛ = lim c!(log 1/δ)^(−c) ∫_(K∘π>δ) F (K∘π)^(−μ) μ_U` — a Tauberian/Mellin equivalence with the Laplace form; the engine would have to be rerun with the kernel `1_(t>δ) t^(−μ)`. L.

## 3. Questions
(a) Check the two coordinate-free descriptions (A: Laplace + sublevel-set with `c!`; B: density residue with `(fω)|_E/|df|`, invariance, symmetric iteration, `div(K∘π)` normalisation). Any error? Is B's normalisation statement ("residue relative to the divisor with multiplicities" = dividing by `2k_j`) the right way to say it, and is `Res^(div K∘π)_S` a reasonable notation?
(b) Which of P1–P4 is the structural unit to build now, and in what order? Give the precise Lean-level statement you recommend for the first one (measure identity on X; how to handle the Base integration and the F-free amplitude; regularity route), a unit list with S/M/L costs, and the paper sentence it would justify.
(c) For P1: is the natural object `Σ_(p,J) m_(p,J)` a canonical measure or only its restriction to X (near `D_(c+1)` the face densities diverge)? Should the identity be stated for `ν` (finite on compacts of X) or for the ℛ-normalised version, and does anything need the extremal index?
(d) Anything in my artifact wording for A/B to fix.
