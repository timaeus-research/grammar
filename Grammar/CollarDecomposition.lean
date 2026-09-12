/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.WaterFillingCollar

/-!
# The collar decomposition of the prior-weighted box measure (CCCXXIII)

Consult #96 §3.3–3.4 (unit 4, measure theory). With the water-filling geometry of CCCXXII, the
prior-weighted Lebesgue measure `μ = ϕ·Leb|_{[0,a]^d}` decomposes EXACTLY as

`μ = Σ_{I ≠ ∅} μ|_{C_I} + μ|_{(⋃ C_I)ᶜ}`,

with the phase `K ≥ δ` almost everywhere on the tail. The inputs are, for every nonempty `I`, a
compact base `K_I` embedded onto `B_I` and uniform series families for the prior and the
observable in the normalised normal variables (`StratumSeries`); each core is the normalised box
core of CCCXXI (`StratumSeries.toData`), whose exact transport identity also yields that the
THRESHOLDS `{w ∈ C_I : w_i = ℓ_{I,i}}` are `μ`-null (`measure_image_inter_threshold`: they pull
back to a coordinate hyperplane of the normal box). Hence the core images are `μ`-a.e. disjoint
(`aeDisjoint_image`, by `disjoint_or_threshold`), `μ|_{⋃ C_I} = Σ μ|_{C_I}`, and the covering
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
  /-- box coordinates ↔ normal coordinates -/
  σ : Fin (n + 1) ≃ Nrm I
  /-- the tangential embedding of the base -/
  e : K → (Tan I → ℝ)
  he : Continuous e
  he_inj : Function.Injective e
  hre : range e = baseSet k I a δ
  /-- the prior and observable series in the normalised normal variables -/
  Fϕ : UniformSeriesFamily K (n + 1) (2 * side k I δ)
  Fφ : UniformSeriesFamily K (n + 1) (2 * side k I δ)
  hϕ_eq : ∀ s, ∀ v ∈ NormalisedBox.box (ι := Fin (n + 1)) (side k I δ),
    ϕ (Φ I σ e (lamT k I δ) (s, v)) = evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (n + 1) → ℝ), ‖v‖ < 2 * side k I δ →
    φ (Φ I σ e (lamT k I δ) (s, v)) = evalF (Fφ.f s) v

variable (hk : ∀ i, 0 < k i) (hd : 0 < d) (ha : 0 < a) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))

/-- The normalised box data of a stratum input. -/
noncomputable def StratumSeries.toData {I : Finset (Fin d)} (hI : I.Nonempty) {n : ℕ} {K : Type*}
    [TopologicalSpace K] {ϕ φ : (Fin d → ℝ) → ℝ} (S : StratumSeries k a δ I n K ϕ φ) :
    NormalisedBox.Data k I n K (piBox d (Icc 0 a)) ϕ φ where
  σ := S.σ
  e := S.e
  he := S.he
  he_inj := S.he_inj
  lamT := lamT k I δ
  hlamT := measurable_lamT k I δ
  hlam_cont := by rw [S.hre]; exact continuousOn_lamT k I a δ hk hI hδ
  hpos := fun t ht j => lamT_pos_of_mem_baseSet k I a δ hk hI hδ (S.hre ▸ ht) j
  β := 1
  hnorm := fun t ht => tanUnit_mul_prod_lamT k I a δ hk hI hδ (S.hre ▸ ht)
  b := side k I δ
  b' := 2 * side k I δ
  hb := side_pos k I δ hδ
  hbb' := by linarith [side_pos k I δ hδ]
  hW := image_subset_box k I a δ S.e S.hre hδ hk hI hd ha hδa
  Fϕ := S.Fϕ
  Fφ := S.Fφ
  hϕ_eq := S.hϕ_eq
  hφ_eq := S.hφ_eq

/-! ### The collar -/

/-- The nonempty coordinate subsets. -/
abbrev NonemptyIdx (d : ℕ) := {I : Finset (Fin d) // I.Nonempty}

variable {ϕ φ : (Fin d → ℝ) → ℝ} (hϕm : Measurable ϕ) (hϕ0 : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
  (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ)
  {n : NonemptyIdx d → ℕ} {K : NonemptyIdx d → Type*} [∀ I, TopologicalSpace (K I)]
  [∀ I, CompactSpace (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, BorelSpace (K I)]
  (S : ∀ I : NonemptyIdx d, StratumSeries k a δ I.1 (n I) (K I) ϕ φ)

/-- The core image of the stratum `I`. -/
def imageSet (I : NonemptyIdx d) : Set (Fin d → ℝ) :=
  NormalisedBox.image I.1 (S I).e (lamT k I.1 δ) (side k I.1 δ)

/-- The threshold set of the normal coordinate `i` of the stratum `I`: `w_i = ℓ_{I,i}(tan w)`. -/
def thresholdSet (I : NonemptyIdx d) (i : Nrm I.1) : Set (Fin d → ℝ) :=
  {w | (split I.1 w).1 i = ell k I.1 δ (split I.1 w).2 i}

theorem measurableSet_thresholdSet (I : NonemptyIdx d) (i : Nrm I.1) :
    MeasurableSet (thresholdSet k δ I i) :=
  measurableSet_eq_fun ((measurable_pi_apply i).comp (measurable_fst.comp (split I.1).measurable))
    ((measurable_ell k I.1 δ i).comp (measurable_snd.comp (split I.1).measurable))

theorem measurableEmbedding_e (I : NonemptyIdx d) : MeasurableEmbedding (S I).e :=
  NormalisedBox.measurableEmbedding_e I.1 (S I).e (S I).he (S I).he_inj

theorem measurableSet_imageSet (I : NonemptyIdx d) : MeasurableSet (imageSet k a δ S I) :=
  measurableSet_image I.1 (side k I.1 δ) (measurableEmbedding_e k a δ S I) (measurable_lamT k I.1 δ)

omit [∀ I, CompactSpace (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, BorelSpace (K I)] in
include hδ in
theorem mem_imageSet_iff (I : NonemptyIdx d) (w : Fin d → ℝ) :
    w ∈ imageSet k a δ S I ↔ tan I.1 w ∈ baseSet k I.1 a δ ∧
      ∀ i : Nrm I.1, 0 < w i.1 ∧ w i.1 ≤ ell k I.1 δ (tan I.1 w) i :=
  mem_image_iff k I.1 a δ (S I).e (S I).hre hδ w

/-- The measurable set of the box. -/
theorem measurableSet_W : MeasurableSet (piBox d (Icc 0 a)) :=
  measurableSet_piBox d _ measurableSet_Icc

include hk hd ha hδ hδa hϕm hϕ0 hLμ hLphase hLobs in
/-- The core of the stratum `I` (the normalised box core of CCCXXI). -/
noncomputable def stratumCore (I : NonemptyIdx d) :
    CorePresentation L (L.μ.restrict (imageSet k a δ S I)) (K I) (n I) 1 :=
  NormalisedBox.core hk (measurableSet_W a) hϕm hϕ0 L hLμ hLphase hLobs
    ((S I).toData k a δ hk hd ha hδ hδa I.2)

include hk hd ha hδ hδa hϕm hϕ0 hLμ hLphase hLobs in
/-- The thresholds are `μ`-null: they pull back to a coordinate hyperplane of the normal box. -/
theorem measure_image_inter_threshold (I : NonemptyIdx d) (i : Nrm I.1) :
    L.μ (imageSet k a δ S I ∩ thresholdSet k δ I i) = 0 := by
  set C := stratumCore k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S I
  have htr := C.transport
  rw [inter_comm, ← Measure.restrict_apply (measurableSet_thresholdSet k δ I i), ← htr,
    Measure.map_apply C.measurable_Φ (measurableSet_thresholdSet k δ I i)]
  refine (withDensity_absolutelyContinuous _ _) (measure_mono_null (t := {p | p.2 ((S I).σ.symm i) =
    side k I.1 δ}) ?_ ?_)
  · rintro ⟨s, v⟩ hp
    change (split I.1 (Φ I.1 (S I).σ (S I).e (lamT k I.1 δ) (s, v))).1 i =
      ell k I.1 δ (split I.1 (Φ I.1 (S I).σ (S I).e (lamT k I.1 δ) (s, v))).2 i at hp
    rw [split_Φ] at hp
    change lamT k I.1 δ ((S I).e s) i * v ((S I).σ.symm i) = ell k I.1 δ ((S I).e s) i at hp
    rw [← lamT_mul_side k I.1 δ hδ] at hp
    have hl : 0 < lamT k I.1 δ ((S I).e s) i :=
      lamT_pos_of_mem_baseSet k I.1 a δ hk I.2 hδ ((S I).hre ▸ mem_range_self s) i
    exact mul_left_cancel₀ hl.ne' hp
  · change chartMeasure (baseMeasure I.1 (S I).e) (n I) (side k I.1 δ) _ = 0
    rw [chartMeasure, show {p : K I × (Fin (n I + 1) → ℝ) | p.2 ((S I).σ.symm i) = side k I.1 δ} =
      univ ×ˢ {v | v ((S I).σ.symm i) = side k I.1 δ} from by
        ext p
        simp [mem_prod], Measure.prod_prod]
    have h0 : (volume : Measure (Fin (n I + 1) → ℝ)) {v | v ((S I).σ.symm i) = side k I.1 δ} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hres : (volume.restrict (piBox (n I + 1) (Ioc 0 (side k I.1 δ))))
        {v | v ((S I).σ.symm i) = side k I.1 δ} = 0 :=
      le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans h0.le) zero_le
    rw [hres, mul_zero]

include hk hd ha hδ hδa hϕm hϕ0 hLμ hLphase hLobs in
/-- ★ **The core images are `μ`-a.e. disjoint** (consult #96 §3.3). -/
theorem aeDisjoint_image {I J : NonemptyIdx d} (hIJ : I ≠ J) :
    L.μ (imageSet k a δ S I ∩ imageSet k a δ S J) = 0 := by
  refine measure_mono_null (t := (⋃ i, imageSet k a δ S I ∩ thresholdSet k δ I i) ∪
    ⋃ i, imageSet k a δ S J ∩ thresholdSet k δ J i) ?_
    (measure_union_null (measure_iUnion_null fun i =>
      measure_image_inter_threshold k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S I i)
      (measure_iUnion_null fun i =>
      measure_image_inter_threshold k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S J i))
  rintro w ⟨hwI, hwJ⟩
  have hIJ' : I.1 ≠ J.1 := fun h => hIJ (Subtype.ext h)
  rcases disjoint_or_threshold k a δ hk hδ I.2 J.2 hIJ' ((mem_imageSet_iff k a δ hδ S I w).1 hwI)
    ((mem_imageSet_iff k a δ hδ S J w).1 hwJ) with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact Or.inl (mem_iUnion.2 ⟨i, hwI, hi⟩)
  · exact Or.inr (mem_iUnion.2 ⟨i, hwJ, hi⟩)

/-- The number of cores. -/
abbrev numCores (d : ℕ) : ℕ := Fintype.card (NonemptyIdx d)

/-- The indexing of the cores. -/
noncomputable def coreIdx : Fin (numCores d) ≃ NonemptyIdx d :=
  (Fintype.equivFin (NonemptyIdx d)).symm

/-- The union of the core images. -/
def collarUnion : Set (Fin d → ℝ) := ⋃ i : Fin (numCores d), imageSet k a δ S (coreIdx i)

theorem measurableSet_collarUnion : MeasurableSet (collarUnion k a δ S) :=
  MeasurableSet.iUnion fun i => measurableSet_imageSet k a δ S (coreIdx i)

include hk hd ha hδ hδa hϕm hϕ0 hLμ hLphase hLobs in
theorem restrict_collarUnion :
    L.μ.restrict (collarUnion k a δ S) =
      ∑ i : Fin (numCores d), L.μ.restrict (imageSet k a δ S (coreIdx i)) := by
  rw [collarUnion, Measure.restrict_iUnion_ae, Measure.sum_fintype]
  · intro i j hij
    exact aeDisjoint_image k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S
      (fun h => hij ((coreIdx (d := d)).injective h))
  · exact fun i => (measurableSet_imageSet k a δ S (coreIdx i)).nullMeasurableSet

include hLμ in
theorem measure_compl_W : L.μ (piBox d (Icc 0 a))ᶜ = 0 := by
  rw [hLμ]
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply' (measurableSet_W a), compl_inter_self, measure_empty]

include hLμ in
theorem measure_hyperplane (i : Fin d) : L.μ {w | w i = 0} = 0 := by
  rw [hLμ]
  refine (withDensity_absolutelyContinuous _ _) (measure_mono_null (fun _ hw => hw) ?_)
  exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans
    (Measure.pi_hyperplane _ i 0).le) zero_le

omit [∀ I, CompactSpace (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, BorelSpace (K I)] in
include hk hd hδ hLμ in
/-- ★ **The tail lies in `{K ≥ δ}` up to a `μ`-null set** (covering theorem). -/
theorem measure_compl_inter_sublevel :
    L.μ ((collarUnion k a δ S)ᶜ ∩ {w | CoordModel.phase d k w < δ}) = 0 := by
  refine measure_mono_null (t := (piBox d (Icc 0 a))ᶜ ∪ ⋃ i, {w | w i = 0}) ?_
    (measure_union_null (measure_compl_W a L hLμ)
      (measure_iUnion_null fun i => measure_hyperplane a L hLμ i))
  rintro w ⟨hwc, hK⟩
  by_contra hcon
  simp only [mem_union, mem_iUnion, not_or, not_exists, mem_compl_iff, not_not,
    mem_ofPred_eq] at hcon
  have hw : w ∈ piBox d (Icc 0 a) := hcon.1
  have hpos : ∀ i, 0 < w i := fun i =>
    lt_of_le_of_ne (hw i (mem_univ _)).1 fun h => hcon.2 i h.symm
  obtain ⟨I, hI, hbase, hnrm⟩ := covering k a δ hk hd hw hpos hK
  refine hwc (mem_iUnion.2 ⟨(coreIdx (d := d)).symm ⟨I, hI⟩, ?_⟩)
  rw [Equiv.apply_symm_apply, mem_imageSet_iff k a δ hδ S]
  exact ⟨hbase, hnrm⟩

include hk hd ha hδ hδa hϕm hϕ0 hLμ hLphase hLobs in
/-- ★★ **The collar decomposition**: `μ = Σ_I μ|_{C_I} + μ|_{(⋃ C_I)ᶜ}` with the phase `≥ δ` a.e.
on the tail; every core is the normalised box core (`β = 1`, side `b_I`). -/
noncomputable def collar :
    AnalyticCoreDecomposition L (numCores d) (fun i => K (coreIdx i))
      (fun i => n (coreIdx i)) 1 where
  core := fun i => L.μ.restrict (imageSet k a δ S (coreIdx i))
  tail := L.μ.restrict (collarUnion k a δ S)ᶜ
  measure_eq := by
    rw [← restrict_collarUnion k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S,
      Measure.restrict_add_restrict_compl (measurableSet_collarUnion k a δ S)]
  δ₀ := δ
  δ₀_pos := hδ
  gap := by
    rw [ae_restrict_iff' (measurableSet_collarUnion k a δ S).compl, ae_iff]
    refine measure_mono_null (fun w hw => ?_)
      (measure_compl_inter_sublevel k a δ hk hd hδ L hLμ S)
    rw [mem_ofPred_eq, Classical.not_imp, not_le] at hw
    rw [hLphase] at hw
    exact ⟨hw.1, hw.2⟩
  chart := fun i => stratumCore k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs S (coreIdx i)

end WaterFilling

end Grammar
