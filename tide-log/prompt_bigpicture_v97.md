# Consult #97 — audit of the water-filling collar and the compact-box producer; next: compatibility layer or the analytic bridge?

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 625 modules, zero sorry/axiom), companion to the paper *Grammar (Expectations
and the Exceptional Divisor)* (Gerraty–Murfet 2026). Your consult #96 designed the water-filling collar and
ranked the units. We have now landed units 3a, 3b, 4 and 5a exactly along your design; this consult asks for
(1) an honesty audit of what landed, (2) the precise next step — the compatibility first slice (§5 of #96)
versus the analytic-neighbourhood bridge (5b) — with Lean-level specifications, and (3) the stopping point.

## 1. What landed since #96 (main `768f406`)

* **CCCXX `DiagonalBoxTransport`** (unit 3a). `diagEquiv a : (ι → ℝ) ≃ᵐ (ι → ℝ)`, `v ↦ (a_i v_i)`;
  `map_diagEquiv_restrict_withDensity : ((Leb|_s).withDensity (ofReal ∏a)).map (diagEquiv a) = Leb|_{diag '' s}`
  (from `Real.map_linearMap_volume_pi_eq_smul_volume_pi`); the coordinate split
  `split I : ℝ^d ≃ᵐ ℝ^I × ℝ^{Iᶜ}` (volume preserving) and `reindex σ`. For `e : K → ℝ^{Iᶜ}` a measurable
  embedding, `lamT : ℝ^{Iᶜ} → ℝ^I` measurable and positive on `range e`, box side `b`:
  `Φ(s,v) = split⁻¹(λ(e s)·(v∘σ⁻¹), e s)`, `image = {w : tan w ∈ range e, 0 < nrm_j w ≤ λ_j(tan w) b}`,
  `baseMeasure = (Leb|_{range e}).comap e`, and ★ `NormalisedBox.map_Φ :
  ((baseMeasure ⊗ Leb|_{(0,b]^ι}).withDensity (ofReal (∏_j λ_j(e s)) · g(Φ p))).map Φ = (Leb.withDensity g)|_{image}`,
  proved fibrewise (no differentiation of λ; Fubini across the split).
* **CCCXXI `NormalisedBoxCore`** (unit 3b). `CoeffFamily.rescale a f = f_γ ∏ a_j^{γ_j}` with
  `evalF_rescale`; `UniformSeriesFamily.rescale` (majorant `M_γ ∏ L_j^{γ_j}`, summable at `b'` when `L_j b' ≤ ρ`)
  and `.smul`. `NormalisedBox.Data k I n K W ϕ φ` bundles `σ`, `e` (continuous injective), `lamT`
  (measurable, continuous on the base, positive), `β` with `hnorm : t_I(t) ∏ λ_j^{2k_j} = β`, `b < b'`,
  `image ⊆ W`, `Fϕ Fφ : UniformSeriesFamily K (n+1) b'` with `hϕ_eq` (on the box) and `hφ_eq` (on the open
  ball of radius `b'`). ★★ `NormalisedBox.core : CorePresentation L (L.μ|_{image}) K n β` — density
  `c(s,v) = J(s)·evalF (Fϕ.f s) (clamp b v)` (`J = ∏λ_j`), datum `(J·fϕ) ⋆ fφ`, `transport` from `map_Φ`
  (+ `density_ae`), `phase_normal` from `phase_Φ : K(Φ(s,v)) = t_I(e s)·∏λ^{2k}·∏ v_i^{2kι_i}` and `hnorm`,
  `amplitude_eq` from the scaled product rule; `presentation : CoreNormalMomentPresentation core`
  (radius `b'`, `cBound = J_max·Σ M_γ b^{|γ|}`); `jetFamily_obsFibre : jetFamily n (core.obsFibre s) = Fφ.f s`;
  `toEta_core_x`.
* **CCCXXII `WaterFillingCollar`** (unit 4, geometry). `q_I(t) = (δ/t_I(t))^{1/|I|}`,
  `baseSet = {t : 0 ≤ t_j ≤ a, δ ≤ t_I(t)(t_j^{2k_j})^{|I|}}` (compact; every `t_j > 0`; `q_I ≤ t_j^{2k_j}`;
  `q_I ≤ δ^{1/d}`), `ell_{I,i} = q_I^{1/(2k_i)} < a` (given `δ^{1/d} < a^{2k_i}`), `side = δ^{1/(2Σ_{i∈I}k_i)}`,
  `lamT = ell/side`, ★ `tanUnit_mul_prod_lamT : t_I ∏ λ^{2k} = 1`, `image_subset_box`,
  ★★ `covering` (IVT on `∏ max(y_i, r)`), ★★ `disjoint_or_threshold`.
* **CCCXXIII `CollarDecomposition`** (unit 4, measure). `StratumSeries` (per nonempty `I`: compact `K`,
  `e` with `range e = B_I`, `Fϕ Fφ` at radius `2 b_I`, identities), `StratumSeries.toData`,
  `measure_image_inter_threshold : μ(C_I ∩ {w_i = ℓ_{I,i}}) = 0` (via the core's exact transport and
  `Measure.pi_hyperplane`), ★ `aeDisjoint_image`, `restrict_collarUnion`, ★ `measure_compl_inter_sublevel :
  μ((⋃C_I)ᶜ ∩ {K < δ}) = 0`, ★★ `WaterFilling.collar : AnalyticCoreDecomposition L numCores (K∘coreIdx) (n∘coreIdx) 1`
  with `δ₀ = δ`.
* **CCCXXIV `CoordinateBoxCertificate`** (unit 5a). `baseStratum I ⊆ S_I` (stratum points with tangential
  coordinates in `B_I`), compact (`compactSpace_KI`, continuous image of `B_I`), `eI`, `range_eI`;
  `σI : Fin (|I|-1+1) ≃ ↥I`; `frameLin/frameI s : ℝ^{|I|} ≃L N_I` = `(Basis.span).equivFun.symm ∘ diag(λ) ∘ reindex`,
  `coe_frameI_apply`, ★ `Φ_eq_frame : Φ(s,u) = normalData.Φ I s (frameI s u)`; `FaceSeries` (per nonempty `I`:
  `Fϕ Fφ : UniformSeriesFamily (KI I) (nI I + 1) (2 b_I)`, `ϕ∘Φ = evalF Fϕ` on the box, `φ∘Φ = evalF Fφ`
  on the ball); `locData`; ★★ `WaterFilling.certificate : ResolvedCertificate geometry normalData [0,a]^d K ϕ φ`;
  ★★ `coeffCertificate`; ★★★ `hasCoordFreeExpansion_collar : HasCoordFreeExpansion certificate.stratumMeasure
  coeffCertificate.field (spectrumLe (commonQ cores.k) (commonD n)) [0,a]^d K ϕ φ`. Hypotheses: `0 < d`,
  `k_i > 0`, `0 < a`, `0 < δ`, `δ^{1/d} < a^{2k_i}`, `Measurable ϕ`, `∀ w, 0 ≤ ϕ w` (GLOBAL, as required by
  `hasCoordFreeExpansion_le`), `Measurable φ`, `Integrable φ (ϕ·Leb|_W)`, and `F : ∀ I, FaceSeries I`.

Key declarations (verbatim signatures; helper lemmas elided):

### Grammar/DiagonalBoxTransport.lean
```lean
noncomputable def diagEquiv (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) : (ι → ℝ) ≃ᵐ (ι → ℝ) where

theorem diagEquiv_image_pi_Ioc (a : ι → ℝ) (ha : ∀ i, 0 < a i) (b : ℝ) :
    diagEquiv a (fun i => (ha i).ne') '' pi univ (fun _ => Ioc 0 b) =
      {z | ∀ i, 0 < z i ∧ z i ≤ a i * b} := by

theorem map_diagEquiv_volume (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    volume.map (diagEquiv a ha) = ENNReal.ofReal |(∏ i, a i)⁻¹| • volume := by

theorem map_diagEquiv_restrict_withDensity (a : ι → ℝ) (ha : ∀ i, 0 < a i) (s : Set (ι → ℝ)) :
    ((volume.restrict s).withDensity fun _ => ENNReal.ofReal (∏ i, a i)).map
        (diagEquiv a fun i => (ha i).ne') =
      volume.restrict (diagEquiv a (fun i => (ha i).ne') '' s) := by

theorem lintegral_diagEquiv_image (a : ι → ℝ) (ha : ∀ i, 0 < a i) (s : Set (ι → ℝ))
    {F : (ι → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in diagEquiv a (fun i => (ha i).ne') '' s, F z =
      ∫⁻ v in s, ENNReal.ofReal (∏ i, a i) * F (diagEquiv a (fun i => (ha i).ne') v) := by

abbrev Nrm := {i : Fin d // i ∈ I}

abbrev Tan := {i : Fin d // ¬ i ∈ I}

noncomputable def split : (Fin d → ℝ) ≃ᵐ (Nrm I → ℝ) × (Tan I → ℝ) :=

theorem measurePreserving_split : MeasurePreserving (split I) volume volume := by

def reindex : (ι → ℝ) ≃ᵐ (Nrm I → ℝ) where

theorem measurePreserving_reindex [Fintype ι] :
    MeasurePreserving (reindex I σ) volume volume := by

def normalMap (s : K) (v : ι → ℝ) : Nrm I → ℝ := fun j => lamT (e s) j * v (σ.symm j)

noncomputable def Φ (p : K × (ι → ℝ)) : Fin d → ℝ :=

def box : Set (ι → ℝ) := pi univ fun _ => Ioc 0 b

def fibre (t : Tan I → ℝ) : Set (Nrm I → ℝ) := {z | ∀ j, 0 < z j ∧ z j ≤ lamT t j * b}

def image : Set (Fin d → ℝ) :=

noncomputable def baseMeasure (e : K → (Tan I → ℝ)) : Measure K :=

theorem map_Φ [Fintype ι] [MeasurableSpace K] (he : MeasurableEmbedding e)
    (hlam : Measurable lamT) (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j)
    {g : (Fin d → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (((baseMeasure I e).prod (volume.restrict (box (ι := ι) b))).withDensity

```

### Grammar/NormalisedBoxCore.lean
```lean
noncomputable def rescale (a : Fin d → ℝ) (f : CoeffFamily d) : CoeffFamily d :=

theorem evalF_rescale (a : Fin d → ℝ) (f : CoeffFamily d) (v : Fin d → ℝ) :
    evalF (rescale a f) v = evalF f fun i => a i * v i := by

theorem absSummableAt_rescale {f : CoeffFamily d} {ρ : ℝ} (hρ : AbsSummableAt f ρ)
    {a L : Fin d → ℝ} (hL : ∀ i, |a i| ≤ L i) (hL0 : ∀ i, 0 ≤ L i) {b : ℝ} (hb : 0 ≤ b)
    (hbL : ∀ i, L i * b ≤ ρ) : AbsSummableAt (rescale a f) b := by

noncomputable def rescale (a : X → Fin d → ℝ) (ha : ∀ i, Continuous fun x => a x i) (L : Fin d → ℝ)
    (hL : ∀ x i, |a x i| ≤ L i) (hL0 : ∀ i, 0 ≤ L i) {b' : ℝ} (hb' : 0 ≤ b')
    (hbL : ∀ i, L i * b' ≤ ρ) : UniformSeriesFamily X d b' where

noncomputable def smul (J : X → ℝ) (hJ : Continuous J) (Jb : ℝ) (hJb : ∀ x, |J x| ≤ Jb) :
    UniformSeriesFamily X d ρ where

theorem evalF_smul_f (J : X → ℝ) (hJ : Continuous J) (Jb : ℝ) (hJb : ∀ x, |J x| ≤ Jb) (x : X)
    (v : Fin d → ℝ) :
    evalF ((F.smul J hJ Jb hJb).f x) v = J x * evalF (F.f x) v := by

def kι (i : Fin (n + 1)) : ℕ := k (σ i).1

noncomputable def J (s : K) : ℝ := ∏ j, lamT (e s) j

noncomputable def tanUnit (t : Tan I → ℝ) : ℝ := ∏ j : Tan I, t j ^ (2 * k j.1)

theorem mem_image_Φ {b : ℝ} (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K)
    {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) b) :

theorem phase_Φ (s : K) (v : Fin (n + 1) → ℝ) :
    CoordModel.phase d k (Φ I σ e lamT (s, v)) =
      (tanUnit k I (e s) * ∏ j : Nrm I, lamT (e s) j ^ (2 * k j.1)) *
        ∏ i, v i ^ (2 * kι k I σ i) := by

noncomputable def Jb : ℝ := (exists_J_bound I e he lamT hlam_cont).choose

theorem measurableEmbedding_e : MeasurableEmbedding e :=

theorem isFiniteMeasure_baseMeasure : IsFiniteMeasure (baseMeasure I e) := by

noncomputable def c (p : K × (Fin (n + 1) → ℝ)) : ℝ :=

noncomputable def xData : TangentialData K (n + 1) :=

theorem density_ae :
    (fun p : K × (Fin (n + 1) → ℝ) =>
      ((chartDensity (fun _ => 0) (c I e lamT b b' hb Fϕ) p).toNNReal : ℝ≥0∞)) =ᵐ[chartMeasure
        (baseMeasure I e) n b]
      fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) * ENNReal.ofReal (ϕ (Φ I σ e lamT p)) := by

structure Data (k : Fin d → ℕ) (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
    (W : Set (Fin d → ℝ)) (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the identification of box coordinates with the normal coordinates -/
  σ : Fin (n + 1) ≃ Nrm I
  /-- the tangential coordinates of the base -/
  e : K → (Tan I → ℝ)
  he : Continuous e
  he_inj : Function.Injective e
  /-- the normal widths -/
  lamT : (Tan I → ℝ) → (Nrm I → ℝ)
  hlamT : Measurable lamT
  hlam_cont : ContinuousOn lamT (range e)
  hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j
  /-- the normalised unit -/
  β : ℝ
  hnorm : ∀ t ∈ range e, tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β
  /-- the box side and the series radius -/
  b : ℝ
  b' : ℝ
  hb : 0 < b
  hbb' : b < b'
  hW : image I e lamT b ⊆ W
  /-- the prior and observable series in the normalised normal variables -/
  Fϕ : UniformSeriesFamily K (n + 1) b'
  Fφ : UniformSeriesFamily K (n + 1) b'
  hϕ_eq : ∀ s, ∀ v ∈ box (ι := Fin (n + 1)) b, ϕ (Φ I σ e lamT (s, v)) = evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (n + 1) → ℝ), ‖v‖ < b' → φ (Φ I σ e lamT (s, v)) = evalF (Fφ.f s) v

noncomputable def core : CorePresentation L (L.μ.restrict (image I D.e D.lamT D.b)) K n D.β where

theorem core_obsFibre (s : K) (v : Fin (n + 1) → ℝ) :
    (core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).obsFibre s v = φ (Φ I D.σ D.e D.lamT (s, v)) := by

noncomputable def presentation :
    CoreNormalMomentPresentation (core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D) where

theorem jetFamily_obsFibre (s : K) :
    jetFamily n ((core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).obsFibre s) = D.Fφ.f s := by

theorem toEta_core_x (s : K) :
    toEta D.b ((core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).x s) =
      CoeffFamily.conv (fun γ => J I D.e D.lamT s * D.Fϕ.f s γ) (D.Fφ.f s) :=

```

### Grammar/WaterFillingCollar.lean
```lean
def tan (w : Fin d → ℝ) : Tan I → ℝ := fun j => w j.1

noncomputable def q (t : Tan I → ℝ) : ℝ := (δ / tanUnit k I t) ^ ((I.card : ℝ)⁻¹)

def baseSet : Set (Tan I → ℝ) :=

noncomputable def ell (t : Tan I → ℝ) (i : Nrm I) : ℝ := q k I δ t ^ (((2 * k i.1 : ℕ) : ℝ)⁻¹)

noncomputable def side : ℝ := δ ^ (((2 * ∑ i ∈ I, k i : ℕ) : ℝ)⁻¹)

noncomputable def lamT (t : Tan I → ℝ) (i : Nrm I) : ℝ := ell k I δ t i / side k I δ

theorem q_le_rpow (hd : 0 < d) {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    q k I δ t ≤ δ ^ ((d : ℝ)⁻¹) := by

theorem ell_lt_of_mem_baseSet (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
    {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (i : Nrm I) : ell k I δ t i < a := by

theorem tanUnit_mul_prod_lamT {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    tanUnit k I t * ∏ i : Nrm I, lamT k I δ t i ^ (2 * k i.1) = 1 := by

theorem isCompact_baseSet : IsCompact (baseSet k I a δ) := by

theorem continuousOn_q (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hδ : 0 < δ) :
    ContinuousOn (q k I δ) (baseSet k I a δ) := by

theorem continuousOn_lamT (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hδ : 0 < δ) :
    ContinuousOn (lamT k I δ) (baseSet k I a δ) := by

theorem image_subset_box (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) :
    NormalisedBox.image I e (lamT k I δ) (side k I δ) ⊆ piBox d (Icc 0 a) := by

theorem covering (hk : ∀ i, 0 < k i) (hd : 0 < d) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc 0 a)) (hpos : ∀ i, 0 < w i) (hK : CoordModel.phase d k w < δ) :
    ∃ I : Finset (Fin d), I.Nonempty ∧ tan I w ∈ baseSet k I a δ ∧
      ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k I δ (tan I w) i := by

theorem disjoint_or_threshold (hk : ∀ i, 0 < k i) (hδ : 0 < δ) {I J : Finset (Fin d)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hIJ : I ≠ J) {w : Fin d → ℝ}
    (hwI : tan I w ∈ baseSet k I a δ ∧ ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k I δ (tan I w) i)
    (hwJ : tan J w ∈ baseSet k J a δ ∧ ∀ i : Nrm J, 0 < w i.1 ∧ w i.1 ≤ ell k J δ (tan J w) i) :
    (∃ i : Nrm I, w i.1 = ell k I δ (tan I w) i) ∨
      (∃ i : Nrm J, w i.1 = ell k J δ (tan J w) i) := by

```

### Grammar/CollarDecomposition.lean
```lean
theorem gives `μ((⋃ C_I)ᶜ ∩ {K < δ}) = 0` (`measure_compl_inter_sublevel`; the exceptional points
lie off the box or on a coordinate hyperplane).

★★ `collar : AnalyticCoreDecomposition L numCores (K ∘ coreIdx) (n ∘ coreIdx) 1` — the finite
analytic-normal collar decomposition with uniform tail gap `δ₀ = δ`, all cores normalised to
`β = 1`.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open NormalisedBox CoeffFamily

variable {d : ℕ} (k : Fin d → ℕ) (a δ : ℝ)

/-- The per-stratum input of the collar: a compact base embedded onto `B_I` and uniform series
families for the prior and the observable in the normalised normal variables. -/
structure StratumSeries (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
    (ϕ φ : (Fin d → ℝ) → ℝ) where

noncomputable def StratumSeries.toData {I : Finset (Fin d)} (hI : I.Nonempty) {n : ℕ} {K : Type*}
    [TopologicalSpace K] {ϕ φ : (Fin d → ℝ) → ℝ} (S : StratumSeries k a δ I n K ϕ φ) :
    NormalisedBox.Data k I n K (piBox d (Icc 0 a)) ϕ φ where

abbrev NonemptyIdx (d : ℕ) := {I : Finset (Fin d) // I.Nonempty}

def imageSet (I : NonemptyIdx d) : Set (Fin d → ℝ) :=

def thresholdSet (I : NonemptyIdx d) (i : Nrm I.1) : Set (Fin d → ℝ) :=

theorem measurableEmbedding_e (I : NonemptyIdx d) : MeasurableEmbedding (S I).e :=

noncomputable def stratumCore (I : NonemptyIdx d) :
    CorePresentation L (L.μ.restrict (imageSet k a δ S I)) (K I) (n I) 1 :=

theorem measure_image_inter_threshold (I : NonemptyIdx d) (i : Nrm I.1) :
    L.μ (imageSet k a δ S I ∩ thresholdSet k δ I i) = 0 := by

theorem aeDisjoint_image {I J : NonemptyIdx d} (hIJ : I ≠ J) :
    L.μ (imageSet k a δ S I ∩ imageSet k a δ S J) = 0 := by

abbrev numCores (d : ℕ) : ℕ := Fintype.card (NonemptyIdx d)

noncomputable def coreIdx : Fin (numCores d) ≃ NonemptyIdx d :=

def collarUnion : Set (Fin d → ℝ) := ⋃ i : Fin (numCores d), imageSet k a δ S (coreIdx i)

theorem measure_compl_inter_sublevel :
    L.μ ((collarUnion k a δ S)ᶜ ∩ {w | CoordModel.phase d k w < δ}) = 0 := by

noncomputable def collar :
    AnalyticCoreDecomposition L (numCores d) (fun i => K (coreIdx i))
      (fun i => n (coreIdx i)) 1 where

```

### Grammar/CoordinateBoxCertificate.lean
```lean
def zeroOrders (d : ℕ) : Fin d → ℕ := fun _ => 0

def baseStratum (I : Finset (Fin d)) : Set ((geometry d k (zeroOrders d) hk).Stratum I) :=

abbrev KI (I : Finset (Fin d)) := ↥(baseStratum k hk a δ I)

def eI (I : Finset (Fin d)) : KI k hk a δ I → (Tan I → ℝ) := fun s => tan I s.1.1

noncomputable def liftPoint (I : Finset (Fin d)) (t : Tan I → ℝ) : Fin d → ℝ :=

noncomputable def liftBase {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ)
    (t : ↥(baseSet k I a δ)) : KI k hk a δ I :=

theorem range_eI (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    range (eI k hk a δ I) = baseSet k I a δ := by

theorem compactSpace_KI (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    CompactSpace (KI k hk a δ I) := by

theorem isCompact_baseStratum (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    IsCompact (baseStratum k hk a δ I) :=

abbrev nI (I : NonemptyIdx d) : ℕ := I.1.card - 1

noncomputable def σI (I : NonemptyIdx d) : Fin (nI I + 1) ≃ Nrm I.1 :=

noncomputable def frameLin (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    (Fin (nI I + 1) → ℝ) ≃ₗ[ℝ] normalSpace d I.1 :=

noncomputable def frameI (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    (Fin (nI I + 1) → ℝ) ≃L[ℝ] normalSpace d I.1 :=

theorem Φ_eq_frame (I : NonemptyIdx d) (s : KI k hk a δ I.1) (u : Fin (nI I + 1) → ℝ) :
    Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, u) =
      (normalData d k (zeroOrders d) hk).Φ I.1 s.1 (frameI k hk a δ hδ I s u) := by

structure FaceSeries (I : NonemptyIdx d) where
  Fϕ : UniformSeriesFamily (KI k hk a δ I.1) (nI I + 1) (2 * side k I.1 δ)
  Fφ : UniformSeriesFamily (KI k hk a δ I.1) (nI I + 1) (2 * side k I.1 δ)
  hϕ_eq : ∀ s, ∀ v ∈ NormalisedBox.box (ι := Fin (nI I + 1)) (side k I.1 δ),
    ϕ (Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v)) = evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (nI I + 1) → ℝ), ‖v‖ < 2 * side k I.1 δ →
    φ (Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v)) = evalF (Fφ.f s) v

noncomputable def FaceSeries.toStratumSeries {I : NonemptyIdx d} (F : FaceSeries k hk a δ ϕ φ I) :
    StratumSeries k a δ I.1 (nI I) (KI k hk a δ I.1) ϕ φ where

noncomputable def locData : LocalisationData (Fin d → ℝ) where

noncomputable def stratumInputs (I : NonemptyIdx d) :
    StratumSeries k a δ I.1 (nI I) (KI k hk a δ I.1) ϕ φ :=

noncomputable def certificate :
    ResolvedCertificate (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk)
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by

noncomputable def coreData (i : Fin (numCores d)) :
    NormalisedBox.Data k (coreIdx i).1 (nI (coreIdx i)) (KI k hk a δ (coreIdx i).1)
      (piBox d (Icc 0 a)) ϕ φ :=

noncomputable def coeffCertificate :
    (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).CoefficientCertificate := by

theorem hasCoordFreeExpansion_collar :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).stratumMeasure
      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).field
      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).cores.k)
        (commonD (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).n))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=

```

Headline rows (verbatim) for CCCXX–CCCXXIV:

| **CCCXXIV** | ★★★ **THE COMPACT-BOX CERTIFICATE ON THE COORDINATE MODEL — THE GENERAL PRODUCER FROM LOCAL NORMAL SERIES (u642; consult #96 unit 5a)**: on the coordinate model (`CoordModel.geometry d k 0`, `normalData`) with the monomial phase on `W = [0,a]^d`, a measurable nonnegative prior `ϕ` and an observable `φ` (integrable against `ϕ·Leb|_W`), the water-filling collar is assembled into the certificates: the bases `baseStratum I ⊆ S_I` are the stratum points with tangential coordinates in `B_I` (COMPACT — the continuous image of `B_I` under the lift `t ↦ (0,t)`, `compactSpace_KI`; embedded by the tangential coordinates `eI`, `range_eI`, `eI_injective`); the frames `frameI s : ℝ^{|I|} ≃L N_I = span{e_i : i∈I}` are the reindexed diagonal scalings `u ↦ Σ_i λ_{I,i}(s) u_{σ⁻¹i} e_i` built from `Module.Basis.span`, `LinearEquiv.piCongrRight` and `smulOfNeZero` (`coe_frameI_apply`), and ★ `Φ_eq_frame` identifies the core parametrisation `s + Σ λ_i v_i e_i` with the coordinate model's tubular germ `s + ξ`, `ξ = frame u`. Input: `FaceSeries` — for every nonempty `I`, uniform series families `Fϕ Fφ` over the base in the NORMALISED normal variables at radius `2b_I`, with `ϕ∘Φ = evalF Fϕ` on the box and `φ∘Φ = evalF Fφ` on the ball. Then ★★ `WaterFilling.certificate : ResolvedCertificate geometry normalData W K ϕ φ` (`M = numCores`, `β = 1`, cores = the collar, presentations from the observable series), ★★ `coeffCertificate` (density family `J·fϕ`, jets `fφ` via `jetFamily_obsFibre`, datum identity `toEta_core_x`; `cc_abs_aux`, `jet_abs_aux`, `datum_eq_aux` on concrete indices), and ★★★ `hasCoordFreeExpansion_collar : HasCoordFreeExpansion certificate.stratumMeasure coeffCertificate.field (spectrumLe (commonQ cores.k) (commonD n)) W K ϕ φ` — the coordinate-free expansion of `∫_{[0,a]^d} φϕe^{−nK}` with strata integrals over ALL nonempty coordinate strata, produced from LOCAL normal series (not one series across the box). This is consult #96's recommended stopping theorem for the phase minus the analytic-neighbourhood bridge. Non-claims: face series are hypotheses in normalised variables (rescaling adapter `UniformSeriesFamily.rescale` available); spectrum stated as the cores' common lattice; the `Data.hnorm`/frames are the coordinate model's, not derived SNC geometry. Axiom-clean | CoordinateBoxCertificate.lean |
| **CCCXXIII** | ★★ **THE COLLAR DECOMPOSITION OF THE PRIOR-WEIGHTED BOX MEASURE (u641; consult #96 §3.3–3.4, unit 4 measure theory)**: with the water-filling geometry of CCCXXII and, for every nonempty `I`, a `StratumSeries` input (a compact base `K_I` embedded onto `B_I`, uniform series families `Fϕ Fφ` at radius `2b_I` in the normalised normal variables, series identities on the box / the ball), each core is the normalised box core of CCCXXI (`StratumSeries.toData`, `stratumCore`; `β = 1`, side `b_I`, `image ⊆ W`). The exact transport identity makes the THRESHOLDS `{w ∈ C_I : w_i = ℓ_{I,i}}` `μ`-null (`measure_image_inter_threshold`: they pull back to the coordinate hyperplane `v_{σ⁻¹i} = b_I` of the normal box, `Measure.pi_hyperplane`), hence ★ `aeDisjoint_image : μ(C_I ∩ C_J) = 0` for `I ≠ J` (by `disjoint_or_threshold`), `restrict_collarUnion : μ|_{⋃ C_I} = Σ_I μ|_{C_I}` (`Measure.restrict_iUnion_ae`), and ★ `measure_compl_inter_sublevel : μ((⋃ C_I)ᶜ ∩ {K < δ}) = 0` (by `covering`; the exceptional points lie off the box or on a coordinate hyperplane, both `μ`-null). Hence ★★ `WaterFilling.collar : AnalyticCoreDecomposition L numCores (K ∘ coreIdx) (n ∘ coreIdx) 1` — the finite analytic-normal collar decomposition `μ = Σ_I μ|_{C_I} + μ|_{(⋃C_I)ᶜ}` with uniform tail gap `δ₀ = δ` and all cores normalised (`β = 1`), for the prior-weighted Lebesgue measure on `[0,a]^d` and any measurable nonnegative prior. Gate of consult #96 unit 4 met: positive exact measure decomposition and uniform tail gap, WITHOUT changing the fixed-side core interface. Non-claims: the stratum inputs (bases, normalised series) are hypotheses here; the coordinate-model instance (bases as subsets of the strata, rescaled face series) and the `ResolvedCertificate` are the next unit. Axiom-clean | CollarDecomposition.lean |
| **CCCXXII** | ★★ **THE WATER-FILLING COLLAR OF THE COORDINATE MONOMIAL PHASE — GEOMETRY (u640; consult #96 §3, unit 4)**: on `W = [0,a]^d` with `K = ∏ w_i^{2k_i}` and a level `δ > 0` with `δ^{1/d} < a^{2k_i}`, for every nonempty `I` (`m = |I|`) the tangential unit `t_I(t) = ∏_{j∉I} t_j^{2k_j}`, the WATER LEVEL `q_I(t) = (δ/t_I(t))^{1/m}` (`WaterFilling.q`), the BASE `B_I = {t : 0 ≤ t_j ≤ a, δ ≤ t_I(t)(t_j^{2k_j})^m}` (`baseSet`; closed and bounded hence COMPACT, `isCompact_baseSet`; every `t_j > 0` so it lies in the EXACT stratum, `pos_of_mem_baseSet`; on it `q_I ≤ t_j^{2k_j}` and `q_I ≤ δ^{1/d}`, `q_le_rpow`), the physical widths `ℓ_{I,i}(t) = q_I(t)^{1/(2k_i)} < a` (`ell`, `ell_lt_of_mem_baseSet`), the common normalised side `b_I = δ^{1/(2Σ_{i∈I}k_i)}` (`side`) and the widths `λ_{I,i} = ℓ_{I,i}/b_I` (`lamT`, measurable, continuous on the base) with the ★ NORMALISATION IDENTITY `tanUnit_mul_prod_lamT : t_I(t)·∏_i λ_{I,i}(t)^{2k_i} = 1` — every core has `β = 1` and the FIXED side `b_I` (no variable-width interface is needed, consult #96 §3.6). The core image `C_I = {w : tan_I w ∈ B_I, 0 < w_i ≤ ℓ_{I,i}}` (`mem_image_iff`, the `NormalisedBox.image` of CCCXX with `range e = B_I`) lies in `W` (`image_subset_box`). ★★ `covering`: every `w ∈ W` with positive coordinates and `K(w) < δ` lies in some `C_I` (water-filling: the intermediate value theorem on `H(r) = ∏ max(w_i^{2k_i}, r)` between `min_i w_i^{2k_i}` and a large level gives the level `r` with `H(r) = δ`; `I = {i : w_i^{2k_i} < r}` is nonempty and `r = q_I`). ★★ `disjoint_or_threshold`: `w ∈ C_I ∩ C_J`, `I ≠ J` forces some normal coordinate onto its upper boundary `w_i = ℓ_{I,i}` or `w_i = ℓ_{J,i}` (the two water levels coincide by a strict product comparison `δ = q_I^{|I|} t_I ≤ q_I^{|I|} q_J^{|J∖I|} t_J < q_J^{|J|} t_J = δ`). The measure-theoretic assembly (null thresholds, `μ = Σ μ|_{C_I} + tail`, gap on the tail) is the next unit. Axiom-clean | WaterFillingCollar.lean |
| **CCCXXI** | ★★ **THE NORMALISED BOX CORE AT A COORDINATE STRATUM (u639; consult #96 unit 3b, the parameterised normal-rescaling PRODUCER)**: `NormalisedBox.Data k I n K W ϕ φ` bundles a compact base `K` embedded in the stratum `S_I` by tangential coordinates `e` (continuous, injective), positive normal widths `lamT` (measurable, continuous on the base) with the normalisation identity `hnorm : t_I(t) ∏_{j∈I} λ_j(t)^{2k_j} = β` (`tanUnit`), a box side `b < b'`, `image ⊆ W`, and prior/observable given near the base by uniform series families `Fϕ Fφ : UniformSeriesFamily K (n+1) b'` in the NORMALISED normal variables (`hϕ_eq` on the box, `hφ_eq` on the open ball of radius `b'`). From this ★★ `NormalisedBox.core : CorePresentation L (L.μ.restrict image) K n β` is CONSTRUCTED: base measure `ν_B` (coordinate Lebesgue on the base, finite by compactness), `Φ(s,v) = s + Σ_j λ_j(s) v_j e_j`, density `c(s,v) = J(s)·ϕ̃(v)` with the normal Jacobian `J = ∏λ_j` (realised through a bounded clamped representative, equal to `J·ϕ∘Φ` on the box), amplitude datum `(J·fϕ) ⋆ fφ` (`xData`, continuous by CCCXIX); `transport` is the exact identity of CCCXX (`map_Φ` + `density_ae`), `phase_normal` is the phase identity `phase_Φ : K(Φ(s,v)) = t_I(e s)·∏λ_j^{2k_j}·∏ v_i^{2kι_i}` (`Finset.prod_subtype` split) plus `hnorm`, `amplitude_eq` the scaled product rule (`evalF_conv_of_absSummableAt`, `evalF_const_mul`). ★ `NormalisedBox.presentation : CoreNormalMomentPresentation core` (fibre series `polySeriesD (Fφ.f s)`, radius `b'`, `cBound = J_max·Σ M_γ b^{|γ|}`); `jetFamily_obsFibre : jetFamily n (core.obsFibre s) = Fφ.f s`, `toEta_core_x`. Also the rescaling adapter from series in the ORIGINAL normal variables: `CoeffFamily.rescale a f = f_γ ∏ a_j^{γ_j}` with `evalF_rescale : evalF (rescale a f) v = evalF f (a·v)`, `UniformSeriesFamily.rescale` (majorant `M_γ ∏ L_j^{γ_j}`, summable at `b'` when `L_j b' ≤ ρ` — the radius shrink of consult #96 §2.4) and `UniformSeriesFamily.smul`. Non-claims: no `ResolvedCertificate` yet (the collar decomposition sums such cores with a phase-gap tail); the base is any compact `K`, the coordinate-model stratum instance is assembled later. Axiom-clean | NormalisedBoxCore.lean |
| **CCCXX** | ★ **DIAGONAL BOX TRANSPORT: THE MEASURE IDENTITY OF A NORMALISED CORE (u638; consult #96 unit 3a)**: for a normal index set `I ⊆ Fin d`, a measurable embedding `e : K → ℝ^{Iᶜ}` of the base, measurable positive widths `lamT : ℝ^{Iᶜ} → ℝ^I`, and the box `(0,b]^ι` (`σ : ι ≃ I`), the parametrisation `Φ(s,v) = split⁻¹(λ(e s)·v∘σ⁻¹, e s)` (`NormalisedBox.Φ`, i.e. `s + Σ_j λ_j(s) v_j e_j`) satisfies the EXACT transport identity ★ `NormalisedBox.map_Φ`: `((ν_B ⊗ Leb|_{(0,b]^ι}).withDensity (ofReal (∏_j λ_j(s)) · g(Φ(s,v)))).map Φ = (Leb.withDensity g).restrict image`, where `ν_B = (Leb|_{range e}).comap e` is coordinate Lebesgue measure on the base and `image = {w : tan w ∈ range e, 0 < nrm_j w ≤ λ_j(tan w)·b}` is the curved image (`measurableSet_image`). This is the `CorePresentation.transport` field of a core at a positive-dimensional coordinate stratum with `s`-dependent normal widths, proved fibrewise WITHOUT differentiating `λ`: the diagonal scaling `v ↦ (a_j v_j)` (`diagEquiv`) pushes the Jacobian-weighted Lebesgue measure `∏a_j · Leb|_s` to `Leb|_{image}` (`map_diagEquiv_restrict_withDensity`, from `Real.map_linearMap_volume_pi_eq_smul_volume_pi` + `det_toLin'_diagonal`), then Fubini across the volume-preserving coordinate split `ℝ^d ≃ ℝ^I × ℝ^{Iᶜ}` (`split`, `measurePreserving_split`) and the reindexing `reindex σ` (`measurePreserving_reindex`); `lintegral_diagEquiv_image`, `diagEquiv_image_pi_Ioc`, `reindex_image_pi`. No Haar Jacobian theorem on the subtype product is needed (consult #96 §2.5). Axiom-clean | DiagonalBoxTransport.lean |

## 2. Questions

**Q1 (audit).** Is CCCXXIV an honest instance of the theorem you specified in #96 §4.1 ("uniform
face-normal series input")? Points to check: (a) our `FaceSeries` input is stated over the BASES `baseStratum I`
(exact strata, compact) rather than over the closed faces `X_I`, and in the NORMALISED variables at radius `2b_I`
— is this acceptable as the producer's interface, or should the public hypothesis be the face families in the
original normal variables (radius `ρ_I`, `2δ^{1/(2k_i d)} < ρ_I`) with the rescaling/restriction done inside
(we have `UniformSeriesFamily.rescale`)? (b) the observable identity `hφ_eq` is required on the OPEN BALL of
radius `2b_I` in the normalised variables (so at physical points `s + Σ λ_i v_i e_i` with `|v_i| < 2b_I`,
including negative `v_i`, i.e. outside `[0,a]^d` for boundary strata) — is this the right requirement, or
should `φ` be allowed to be an arbitrary extension there? (c) `hϕ0` is GLOBAL (`∀ w, 0 ≤ ϕ w`) because
`hasCoordFreeExpansion_le` demands it; should we weaken the completion theorem to `∀ w ∈ W` (the integral only
sees `W`)? (d) the spectrum is `spectrumLe (commonQ cores.k) (commonD n)`; we can evaluate
`commonD = d − 1` and `commonQ = ∏_I 2∏_{i∈I} k_i` — is the paper-facing statement better with the evaluated
lattice, and is `commonQ` (product over all cores) the right common denominator or should it be the lcm?
(e) any hidden hypothesis, overclaim in the headline rows, or a place where our construction silently
depends on a choice (e.g. `σI` via `Finset.equivFin`, the `numCores` indexing)?

**Q2 (compatibility first slice).** Given the concrete objects now in place — the coordinate model's
`normalData` (`N_I = span{e_i : i ∈ I}`, `du_i`, `Φ_s ξ = s + ξ`), the certificate's diagonal frames
`frameI s` with `coe_frameI_apply`, and `Φ_eq_frame` — write the field lists (compilable Lean as far as
possible) of the FIRST compatibility slice you recommend, tailored to what exists: which of
`SNCNormalCompatibility` / `ResolvedTubularCompatibility` / `MonomialPhaseCompatibility` /
`ResolvedDensityCompatibility` / chart `label/k_eq/h_eq/frame_conormal` (with `frameScale s i = λ_{I,i}(s)`)
should be stated first, exactly how they should be verified on the coordinate model (which lemmas we already
have: `phase_Φ`, `map_Φ`, `Φ_eq_frame`, `coe_frameI_apply`, `du_apply_basisVec`), and what the FIRST
CONSUMER theorem should be — you proposed `produceCore_of_coordinateCompat` (constructive) then the
fixed-germ jet interpretation `D^r(G_s∘F_s)(0) = D^rG_s(0)∘(F_s,…,F_s)`. Please give the precise statement
of each and estimate the Lean effort.

**Q3 (5b bridge).** State precisely the analytic-neighbourhood-to-face-series theorem you would accept as
"the bridge": hypotheses on `ϕ, φ` (real-analytic on an open neighbourhood of `[0,a]^d`? complex-analytic on a
polydisc neighbourhood? uniformly bounded?), the conclusion (`∃ δ, ∀ I, FaceSeries I` for our `certificate`,
or the face families over `X_I` at a uniform radius), and the proof route you consider cheapest in Mathlib
(compactness + local expansions + radius shrink, or Cauchy estimates on a complex neighbourhood — we have
`AnalyticFamilyData` doing the complex route for a single chart with `polyRealCoeff`). Is it worth doing now,
or is the stopping theorem already CCCXXIV?

**Q4 (paper-facing statement and stopping).** Draft the one-paragraph theorem statement for the mirror
(companion note) describing CCCXXIV honestly, and say whether this phase should stop after the
compatibility first slice, after 5b, or now. Rank by value per effort with size estimates.

Be concrete and mathematically precise; flag every place our current interface is wrong or too narrow.
