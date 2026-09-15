# Consult #134 — AUDIT of the post-closure follow-ups (positivity, finiteness, monomial regression, x²y² constant) and DIRECTION for what remains

Context: consult #133 closed the residue programme and ranked follow-ups: (1) x²y² regression, (2) local positivity, (3) explicit chart-pushforward measure = ν, (4) measure on the subtype S, (5) zeta continuation. Since then, ALL of (1) and (2) plus the finiteness question you raised have landed. Grammar main `72f89d5` (776 modules, zero sorry/axiom, `#print axioms` = [propext, Classical.choice, Quot.sound] on the headline theorems); hironaka fork `cb11bc8d9` (pin bumped) adds ONE unit. As before: audit the SIGNATURES (proofs compile); check statements and wording; then advise on direction.

## 1. Landed since #133

### CDLVIII SmoothStratumMeasurePositive (namespace Grammar.SmoothEngine.ResolvedData)
```
theorem integrable_prior_mul_exp {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun y => Ξ.prior y * f y * Real.exp (-N * Ξ.K y)
theorem Z_ge_mul_monoBoxIntegral {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y)
    {ε : ℝ} (hε : ε ≤ E.r) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u ∈ orthant d ε,
      c ≤ |E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u)))
    {N : ℝ} (hN : 0 ≤ N) :
    c * monoBoxIntegral E.k E.h ε N ≤
      (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).Z N
theorem exists_orthant_bound_obs {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {P₀ : Ξ.R.U}
    (hP : P₀ ∈ E.φ.source) (hP0 : E.φ P₀ = 0)
    (hpos : 0 < Ξ.prior (Ξ.R.gv P₀) * f (Ξ.R.gv P₀)) :
    ∃ ε c : ℝ, 0 < ε ∧ ε ≤ E.r ∧ 0 < c ∧ ∀ u ∈ orthant d ε,
      c ≤ |E.b u| * (Ξ.prior (watanabeRep Ξ.R.g E.φ u) * f (watanabeRep Ξ.R.g E.φ u))
theorem coeff_comp_gv_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y lam (m - 1)
theorem observableCoeff_pos_of_realised {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) (hm1 : 1 ≤ m) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀)) :
    0 < (Ξ.X Y).observableCoeff lam (m - 1) f hf
theorem integral_extremalStratumMeasure_pos {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀))
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    0 < ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)
theorem partitionObs_isEquivalent_of_pos {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) {P₀ : Ξ.R.U} (hP₀ : P₀ ∈ Ξ.zeroFibre) (hprior : 0 < Ξ.prior (Ξ.R.gv P₀))
    (hres : resonanceCount Ξ.R Ξ.hK0 lam P₀ = m) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf0 : ∀ y, 0 ≤ f y) (hfP : 0 < f (Ξ.R.gv P₀))
    (h0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre m), f (Ξ.R.gv P) = 0) :
    0 < ∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm) ∧
      (fun N => partitionObs Ξ.K Ξ.prior f N) ~[atTop]
        fun N => (∫ x, f (Ξ.R.gv x.1) ∂(Ξ.extremalStratumMeasure Y h hm)) *
          (N ^ (-lam) * Real.log N ^ (m - 1))
```
### CDLIX SmoothStratumMeasureFinite
```
theorem coeff_le_coeff_one_of_extremalData {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    {χ : Ξ.R.U → ℝ} (hχ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ χ) (hχ1 : ∀ P, χ P ≤ 1) :
    (Ξ.withF χ hχ).coeff Y lam (m - 1) ≤
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)
instance {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    (Ξ.extremalStratumMeasure Y h hm).Regular
theorem extremalStratumMeasure_univ_le {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) :
    Ξ.extremalStratumMeasure Y h hm univ ≤
      ENNReal.ofReal ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1))
instance {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.extremalStratumMeasure Y h hm)
theorem extremalStratumMeasure_univ_eq_of_deep_empty {lam : ℝ} {m : ℕ} (h : Ξ.IsExtremalData lam m)
    (hm : 1 ≤ m) (hD : Ξ.deepZeroFibre m = ∅) :
    (Ξ.extremalStratumMeasure Y h hm).real univ =
      (Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff Y lam (m - 1)
```
Proof of `extremalStratumMeasure_univ_le`: your conditional argument made unconditional — `coeff_nonneg_of_extremalData` gives monotonicity T[χ] ≤ 𝒯[1] for cutoffs χ ≤ 1, inner regularity + cutoffs bound ν(K) ≤ 𝒯[1] for every compact K ⊆ X.

### hironaka `Monomialize/Transport/MonomialModification.lean` (fork cb11bc8d9; namespace Monomialize.Manifold / Monomialize.Transport)
```
noncomputable def idMap (W : Opens (Fin d → ℝ)) : AnalyticMap (modelOn W) (modelOn W)
theorem idMap_apply (W : Opens (Fin d → ℝ)) (P : modelOn W) : idMap W P = P := rfl
theorem coe_idMap (W : Opens (Fin d → ℝ)) : ⇑(idMap W) = id := rfl
theorem isAnalyticIsoOver_idMap (W : Opens (Fin d → ℝ)) (S : Set (modelOn W)) :
    (idMap W).IsAnalyticIsoOver S
noncomputable def translation (c : Fin d → ℝ) : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)
theorem translation_apply (c u : Fin d → ℝ) : translation c u = u + -c
theorem translation_source (c : Fin d → ℝ) : (translation c).source = univ
theorem translation_target (c : Fin d → ℝ) : (translation c).target = univ
theorem translation_symm_apply (c u : Fin d → ℝ) : (translation c).symm u = u + c
theorem translation_analytic (c : Fin d → ℝ) :
    AnalyticOnNhd ℝ (translation c) (translation c).source
theorem translation_symm_analytic (c : Fin d → ℝ) :
    AnalyticOnNhd ℝ (translation c).symm (translation c).target
noncomputable def stdChart (P : modelOn W) : OpenPartialHomeomorph (modelOn W) (Fin d → ℝ)
theorem stdChart_mem (P : modelOn W) : stdChart W P ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω (modelOn W)
theorem stdChart_apply (P x : modelOn W) : stdChart W P x = x.1 := rfl
theorem stdChart_source (P : modelOn W) : (stdChart W P).source = univ
theorem stdChart_symm_val (P : modelOn W) {u : Fin d → ℝ} (hu : u ∈ (stdChart W P).target) :
    ((stdChart W P).symm u).1 = u
noncomputable def transChart (P : modelOn W) : OpenPartialHomeomorph (modelOn W) (Fin d → ℝ)
theorem transChart_mem (P : modelOn W) :
    transChart W P ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω (modelOn W)
theorem transChart_source (P : modelOn W) : (transChart W P).source = univ
theorem mem_transChart_source (P x : modelOn W) : x ∈ (transChart W P).source
theorem transChart_apply (P x : modelOn W) : transChart W P x = x.1 + -P.1
theorem transChart_zero (P : modelOn W) : transChart W P P = 0
theorem restrOpen_target_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (s : Set X) (hs : IsOpen s) :
    (e.restrOpen s hs).target ⊆ e.target
theorem transChart_symm_val (P : modelOn W) {u : Fin d → ℝ} (hu : u ∈ (transChart W P).target) :
    ((transChart W P).symm u).1 = u + P.1
theorem zero_mem_transChart_target (P : modelOn W) : (0 : Fin d → ℝ) ∈ (transChart W P).target
theorem watanabeRep_idMap_transChart (P : modelOn W) {u : Fin d → ℝ}
    (hu : u ∈ (transChart W P).target) :
    watanabeRep (idMap W) (transChart W P) u = u + P.1
def monoPhase (k : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ i, x i ^ (2 * k i)
theorem monoPhase_nonneg (k : Fin d → ℕ) (x : Fin d → ℝ) : 0 ≤ monoPhase k x
theorem analyticOnNhd_monoPhase (k : Fin d → ℕ) (s : Set (Fin d → ℝ)) :
    AnalyticOnNhd ℝ (monoPhase k) s
noncomputable def activeExp (k : Fin d → ℕ) (P : Fin d → ℝ) (i : Fin d) : ℕ
theorem exists_monomialChart (k : Fin d → ℕ) (P : modelOn W) (hP : monoPhase k P.1 = 0) :
    ∃ (φ : OpenPartialHomeomorph (modelOn W) (Fin d → ℝ)) (b : (Fin d → ℝ) → ℝ),
      φ ∈ maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω (modelOn W) ∧ P ∈ φ.source ∧ φ P = 0 ∧
      AnalyticOnNhd ℝ b φ.target ∧ (∀ u ∈ φ.target, b u ≠ 0) ∧
      (∀ u ∈ φ.target, monoPhase k (watanabeRep (idMap W) φ u) =
        ∏ i, u i ^ (2 * activeExp k P.1 i)) ∧
      (∀ u ∈ φ.target, (fderiv ℝ (watanabeRep (idMap W) φ) u).det = b u * ∏ i, u i ^ (0 : ℕ)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ centeredBox d ρ ⊆ φ.target
theorem watanabeChartAt_monoPhase (k : Fin d → ℕ) (P : modelOn W) (hP : monoPhase k P.1 = 0) :
    WatanabeChartAt (monoPhase k) (idMap W) P
noncomputable def _root_.Monomialize.Transport.WatanabeModificationOn.ofMonomial (k : Fin d → ℕ)
    (W : Opens (Fin d → ℝ)) : WatanabeModificationOn (monoPhase k) W where
theorem _root_.Monomialize.Transport.WatanabeModificationOn.ofMonomial_U (k : Fin d → ℕ) :
    (WatanabeModificationOn.ofMonomial k W).U = modelOn W := rfl
theorem _root_.Monomialize.Transport.WatanabeModificationOn.ofMonomial_g (k : Fin d → ℕ)
    (P : modelOn W) : (WatanabeModificationOn.ofMonomial k W).g P = P := rfl
theorem exists_evenChartBox_ofMonomial (k : Fin d → ℕ) (P : modelOn W)
    (hP : monoPhase k P.1 = 0) :
    ∃ E : EvenChartBox (WatanabeModificationOn.ofMonomial k W),
      P ∈ E.φ.source ∧ E.φ P = 0 ∧ E.k = activeExp k P.1 ∧ E.h = 0
theorem _root_.Monomialize.Transport.WatanabeModificationOn.ofMonomial_gv (k : Fin d → ℕ)
    (P : modelOn W) : (WatanabeModificationOn.ofMonomial k W).gv P = P.1 := rfl
```
Construction: `modelOn W` = the model manifold restricted to `W`, `idMap` = identity; at a zero `P` the translated standard chart `u = x − P` reads `monoPhase k (u+P) = a(u)·∏_(P_i=0) u_i^(2k_i)` with `a(u) = ∏_(P_i≠0)(u_i+P_i)^(2k_i)` positive analytic near 0, Jacobian 1; the existing unit-absorption machinery (`AbsorbingChange`, `exists_absorbingChange`, `chart_mem_maximalAtlas`, `watanabeRep_chart_phase`, `det_fderiv_watanabeRep_chart`) then gives an exact monomial chart in the maximal atlas with `h = 0`.

### CDLX MonomialResolvedData (namespace Grammar.SmoothEngine)
```
theorem continuous_monoPhase : Continuous (monoPhase k)
noncomputable def monomialData {prior : (Fin d → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior)
    (hp0 : ∀ y, 0 ≤ prior y) (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ (W : Set (Fin d → ℝ))) : ResolvedData d where
noncomputable def zeroActive (P : Fin d → ℝ) : Finset (Fin d)
theorem mem_zeroActive {P : Fin d → ℝ} {i : Fin d} : i ∈ zeroActive k P ↔ P i = 0 ∧ 0 < k i
theorem monoK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ monoPhase k x := fun x _ => monoPhase_nonneg k x
theorem pairs_ofMonomial (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    pairs (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) P =
      (zeroActive k P.1).val.map fun i => (k i, 0)
theorem depth_ofMonomial (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    depth (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) P = (zeroActive k P.1).card
theorem resonanceCount_ofMonomial (μ : ℝ) (P : (WatanabeModificationOn.ofMonomial k W).U)
    (hP : monoPhase k P.1 = 0) :
    resonanceCount (WatanabeModificationOn.ofMonomial k W) (monoK0 k W) μ P =
      ((zeroActive k P.1).filter fun i => Resonates μ (k i, 0)).card
theorem monomialData_R :
    (monomialData k W hps hp0 hpc hpW).R = WatanabeModificationOn.ofMonomial k W := rfl
noncomputable def kmax : ℕ := Finset.univ.sup k
noncomputable def mstar : ℕ := (Finset.univ.filter fun i => k i = kmax k).card
theorem le_kmax (i : Fin d) : k i ≤ kmax k := Finset.le_sup (Finset.mem_univ i)
theorem kmax_pos (hk : ∃ i, 0 < k i) : 0 < kmax k
theorem exists_eq_kmax [Nonempty (Fin d)] : ∃ i, k i = kmax k
theorem one_le_mstar (hk : ∃ i, 0 < k i) : 1 ≤ mstar k
noncomputable def lamStar : ℝ := 1 / (2 * (kmax k : ℝ))
theorem resonates_lamStar_iff (hk : ∃ i, 0 < k i) (i : Fin d) :
    Resonates (lamStar k) (k i, 0) ↔ k i = kmax k
theorem isExtremalData_monomial (hk : ∃ i, 0 < k i) :
    (monomialData k W hps hp0 hpc hpW).IsExtremalData (lamStar k) (mstar k)
def originPt (h0W : (0 : Fin d → ℝ) ∈ W) : (monomialData k W hps hp0 hpc hpW).R.U := ⟨0, h0W⟩
theorem monoPhase_zero (hk : ∃ i, 0 < k i) : monoPhase k 0 = 0
theorem resonanceCount_monomial_zero (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W) :
    resonanceCount (monomialData k W hps hp0 hpc hpW).R (monomialData k W hps hp0 hpc hpW).hK0
      (lamStar k) (originPt k W hps hp0 hpc hpW h0W) = mstar k
theorem originPt_mem_zeroFibre (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hp : 0 < prior 0) :
    originPt k W hps hp0 hpc hpW h0W ∈ (monomialData k W hps hp0 hpc hpW).zeroFibre
theorem monomial_rlct_asymptotic (hk : ∃ i, 0 < k i) (h0W : (0 : Fin d → ℝ) ∈ W)
    (hp : 0 < prior 0) :
    ∃ c : ℝ, 0 < c ∧ (fun N => partitionObs (monoPhase k) prior (fun _ => (1 : ℝ)) N) ~[atTop]
      fun N => c * (N ^ (-lamStar k) * Real.log N ^ (mstar k - 1))
```
### CDLXI MonomialStratumMeasure
```
abbrev equalExp (d κ : ℕ) : Fin d → ℕ := fun _ => κ
theorem kmax_equal [Nonempty (Fin d)] : kmax (equalExp d κ) = κ
theorem mstar_equal [Nonempty (Fin d)] : mstar (equalExp d κ) = d
theorem exists_pos_equal (hκ : 0 < κ) [Nonempty (Fin d)] : ∃ i, 0 < equalExp d κ i
theorem deepZeroFibre_equal_eq_empty :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).deepZeroFibre d = ∅
theorem exactStratum_equal_subset [Nonempty (Fin d)] :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).exactStratum (lamStar (equalExp d κ)) d ⊆
      {P | P.1 = 0}
def originX (h0W : (0 : Fin d → ℝ) ∈ W) :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).stratumOpen d
theorem isExtremalData_equal [Nonempty (Fin d)] :
    (monomialData (equalExp d κ) W hps hp0 hpc hpW).IsExtremalData (lamStar (equalExp d κ)) d
theorem one_le_dim [Nonempty (Fin d)] : 1 ≤ d := Fin.pos (Classical.arbitrary (Fin d))
noncomputable def equalMeasure [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    Measure ((monomialData (equalExp d κ) W hps hp0 hpc hpW).stratumOpen d)
theorem equalMeasure_compl_origin [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure κ W hps hp0 hpc hpW hκ Y {originX κ W hps hp0 hpc hpW h0W}ᶜ = 0
theorem equalMeasure_eq_smul_dirac [Nonempty (Fin d)]
    (Y : ResolvedCoreTransport (monomialData (equalExp d κ) W hps hp0 hpc hpW).R
      (monomialData (equalExp d κ) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure κ W hps hp0 hpc hpW hκ Y =
      ENNReal.ofReal (((monomialData (equalExp d κ) W hps hp0 hpc hpW).withF (fun _ => (1 : ℝ))
        contMDiff_const).coeff Y (lamStar (equalExp d κ)) (d - 1)) •
        Measure.dirac (originX κ W hps hp0 hpc hpW h0W)
theorem tendsto_normalised_partitionObs_equal [Nonempty (Fin d)] {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (normalised (lamStar (equalExp d κ)) (d - 1)
      (partitionObs (monoPhase (equalExp d κ)) prior f)) atTop (𝓝 (c * f 0))
```
### CDLXII MonomialExplicitConstant
```
theorem lamStar_x2y2 : lamStar (equalExp 2 1) = 1 / 2
theorem mstar_x2y2 : mstar (equalExp 2 1) = 2 := mstar_equal 1
theorem ratioExp_x2y2 (i : Fin 2) : ratioExp (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) i = 1 / 2
theorem multCount_x2y2 :
    multCount (ratioExp (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1)) (1 / 2) = 2
theorem phaseCoeff_x2y2 (σ : Fin 2 → Bool) :
    phaseCoeff (fun _ : Fin 2 => (0 : ℕ)) (fun _ => 1) (1 / 2) 1
      (fun u => phaseSign (fun _ : Fin 2 => 1) σ * (fun _ : Fin 2 → ℝ => (0 : ℝ)) u)
      (fun u => prior (reflect σ u)) = prior 0 * (Real.sqrt Real.pi / 2)
theorem x2y2_tendsto_headline :
    Tendsto (normalised (1 / 2) 1 (partitionObs (monoPhase (equalExp 2 1)) prior (fun _ => 1)))
      atTop (𝓝 (Real.sqrt Real.pi * prior 0))
theorem x2y2_coeff_one_eq
    (Y : ResolvedCoreTransport (monomialData (equalExp 2 1) W hps hp0 hpc hpW).R
      (monomialData (equalExp 2 1) W hps hp0 hpc hpW).hKc prior) :
    ((monomialData (equalExp 2 1) W hps hp0 hpc hpW).withF (fun _ => (1 : ℝ))
      contMDiff_const).coeff Y (lamStar (equalExp 2 1)) (2 - 1) = Real.sqrt Real.pi * prior 0
theorem x2y2_measure_eq (h0W : (0 : Fin 2 → ℝ) ∈ W)
    (Y : ResolvedCoreTransport (monomialData (equalExp 2 1) W hps hp0 hpc hpW).R
      (monomialData (equalExp 2 1) W hps hp0 hpc hpW).hKc prior) :
    equalMeasure 1 W hps hp0 hpc hpW one_pos Y =
      ENNReal.ofReal (Real.sqrt Real.pi * prior 0) •
        Measure.dirac (originX 1 W hps hp0 hpc hpW h0W)
theorem x2y2_tendsto_normalised (h0W : (0 : Fin 2 → ℝ) ∈ W) {f : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    Tendsto (normalised (1 / 2) 1 (partitionObs (monoPhase (equalExp 2 1)) prior f)) atTop
      (𝓝 (Real.sqrt Real.pi * prior 0 * f 0))
```
(`headline_symmetric_abs_phase_leading` is the pre-existing Headline XIX: for `∫_(symBox) η ∏|x|^h exp(−βN²∏x^(2k) + βN∏x^k·ξ)` normalised by `N^(−2l)(log N)^(mult−1)` the limit is `Σ_σ phaseCoeff …(η∘reflect σ)`; `phaseCoeff_equal` evaluates it at equal ratios as `η(0)·phaseMoment β (2l) (ξ 0)/(m!∏k_i)`; `phaseMoment_zero`: `phaseMoment β p 0 = Γ(p/2)β^(−p/2)/2`. Four sign patterns σ, each `φ(0)√π/2`; the transport `N ↦ √N` halves the log; total `√π φ(0)`.)

A CORRECTION I made along the way: my earlier prose (artifact + mirror) had `ν^(1/2)_2 = (√π/4)φ(0)δ₀` for x²y². That is the chart-face constant `Γ(1/2)/(1!·2·2)` of ONE orthant sector; the identity modification has four sectors at the origin, so the true constant is `√π φ(0)` — confirmed by the direct computation `∫ e^(−Mx²y²)dy = √π/(√M|x|)`, `∫_(1/√M<|x|<1) dx/|x| = log M`, and now by CDLXII. The depth-one density is likewise `√π(φ(x,0)dx/|x| + φ(0,y)dy/|y|)` (two sides per axis), not `√π/2`. Please confirm these numbers.

## 2. Mirror wording added (after the residue paragraph)
> The coefficient is strictly positive whenever f ≥ 0 is positive at the image of a point of Z₀ through which exactly m* walls resonate with λ* and at which the prior is positive [observableCoeff_pos_of_realised]; for such f with pull-back vanishing near D_(m*+1) the integral ∫ f∘π dν is positive [integral_extremalStratumMeasure_pos] and the asymptotic equivalence holds with a positive constant [partitionObs_isEquivalent_of_pos]. The leading stratum measure ν^(λ*)_(m*) is finite, with total mass at most the unit-insertion coefficient [extremalStratumMeasure_univ_le], with equality when D_(m*+1) = ∅ [extremalStratumMeasure_univ_eq_of_deep_empty]; in general the unit insertion fails the neighbourhood-vanishing hypothesis and the mass is not identified with the coefficient. Off the extremal index the stratum measures can have infinite mass. Regression. For a monomial phase K = ∏ x_i^(2k_i) the identity is itself a Watanabe modification (hironaka WatanabeModificationOn.ofMonomial …), so the whole construction applies with U = W. The intrinsic walls at a zero P are the coordinates with P_i = 0, k_i > 0, with pairs (k_i, 0) [pairs_ofMonomial]; the extremal data are λ* = 1/(2k_max) and m* = #{i : k_i = k_max} [isExtremalData_monomial], and the general theorem reproduces the classical monomial asymptotic ∫φe^(−NK) ∼ c N^(−1/(2k_max))(log N)^(m*−1), c > 0, for φ(0) > 0 [monomial_rlct_asymptotic]. For equal exponents k_i = κ (the x²y² example is d = 2, κ = 1) the deep zero fibre D_(d+1) is empty, the exact stratum is the origin, and the leading stratum measure is exactly the point mass c δ₀ with c the RLCT constant [equalMeasure_eq_smul_dirac]: every insertion has leading coefficient c f(0) [tendsto_normalised_partitionObs_equal]. For x²y² with φ supported in (−1,1]² the symmetric-box headline at zero phase evaluates the same limit and identifies the constant, c = √π φ(0) (each of the four orthant sectors contributes Γ(1/2)/(1!·2·2) φ(0), and the square-parameter transport halves the logarithm) [x2y2_coeff_one_eq]: the leading stratum measure is exactly √π φ(0) δ₀ [x2y2_measure_eq] and N^(1/2)(log N)^(−1)∫φ f e^(−Nx²y²) → √π φ(0) f(0) for every smooth f [x2y2_tendsto_normalised].

## 3. Questions
(a) Audit the ★★★ statements above (hypotheses, hedges). In particular: is `IsExtremalData (lamStar k) (mstar k)` + realisation at the origin the right formal content of "the classical monomial RLCT is recovered"? Is anything in the monomial regression circular (the identity modification's charts come from the same unit-absorption lemma the general theory uses; is that a genuine test of the machinery or a tautology)? Is the equal-exponent point-mass theorem correctly hedged (D_(d+1) = ∅ uses depth ≤ d; exact stratum ⊆ origin)?
(b) Confirm the x²y² numbers (√π φ(0) for the point mass; √π(φ(x,0)dx/|x| + φ(0,y)dy/|y|) for the depth-one measure). Is the hypothesis "φ supported in (−1,1]²" for CDLXII acceptable for the paper, or should I remove it by a scaling argument (K is homogeneous of degree 4: x ↦ tx scales N by t⁴)?
(c) What is now the most valuable next unit? Candidates: (i) the depth-one measure of x²y² explicitly (ν^(1/2)_1 as a density on the axes — needs the graded stratum formula with c = 1 for observables vanishing near the origin and the identification of `residueSum` for the identity modification and SOME transport Y — hard because the transport's chart weights enter); (ii) explicit chart-pushforward measure = ν in general (M–L); (iii) measure on the subtype S^μ_c (S); (iv) zeta continuation (L+); (v) general monomial explicit constant `𝒯[1] = (Γ(λ*)/((m*−1)!)) · 2^d φ(0)/(∏_(argmax) 2k_i) · (residual ∫ over the non-extremal coordinates)` via the existing mixed headline (`monomialSymReal_tendsto`, `monomialMixedConst`) — plausible S–M and it would give the general monomial point mass explicitly; (vi) something you consider more important for the paper.
(d) Paper wording check for the regression sentences above (anything overclaimed?).
