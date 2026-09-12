/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticCorePresentation

/-!
# Diagonal box transport: the measure identity of a normalised core (CCCXX)

Consult #96 unit 3a. A core at a positive-dimensional coordinate stratum `S_I ⊆ ℝ^d` is
parametrised by `Φ(s, v) = s + Σ_{j∈I} λ_j(s) v_j e_j`: tangential point `s` (coordinates in `Iᶜ`),
normal box coordinates `v ∈ (0,b]^{I}` rescaled by positive widths `λ(s)` chosen so that the phase
becomes `∏ v_j^{2k_j}` with a constant unit. This file proves the exact measure identity such a
core needs (`CorePresentation.transport`): the Jacobian-weighted product measure
`ν_B ⊗ Leb|_{(0,b]^I}` with density `∏_j λ_j(s) · g(Φ(s,v))` pushes forward along `Φ` to
`g · Leb` restricted to the curved image `{w : tan w ∈ B, 0 < nrm_j w ≤ λ_j(tan w) b}`, where the
base measure `ν_B` is coordinate Lebesgue measure on `B = range e` pulled back along the tangential
embedding `e`. The proof is fibrewise (no differentiation of `λ`): the diagonal scaling
`v ↦ (λ_j v_j)` pushes `∏λ_j · Leb|_s` to `Leb|_{image}` (`map_diagEquiv_restrict_withDensity`,
from `Real.map_linearMap_volume_pi_eq_smul_volume_pi`), then Fubini across the coordinate split
`ℝ^d ≃ ℝ^I × ℝ^{Iᶜ}` (`MeasurableEquiv.piEquivPiSubtypeProd`, volume preserving).

Main statement: ★ `NormalisedBox.map_Φ`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Fibrewise diagonal scaling -/

section Diag

variable {ι : Type*}

/-- The diagonal scaling `v ↦ (a_i v_i)` as a measurable equivalence (`a_i ≠ 0`). -/
noncomputable def diagEquiv (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) : (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun v i := a i * v i
  invFun v i := (a i)⁻¹ * v i
  left_inv v := by funext i; simp [ha i]
  right_inv v := by funext i; simp [ha i]
  measurable_toFun := measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _
  measurable_invFun := measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _

theorem diagEquiv_apply (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (v : ι → ℝ) (i : ι) :
    diagEquiv a ha v i = a i * v i := rfl

theorem diagEquiv_symm_apply (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (v : ι → ℝ) (i : ι) :
    (diagEquiv a ha).symm v i = (a i)⁻¹ * v i := rfl

/-- The image of the box `(0,b]^ι` under a positive diagonal scaling. -/
theorem diagEquiv_image_pi_Ioc (a : ι → ℝ) (ha : ∀ i, 0 < a i) (b : ℝ) :
    diagEquiv a (fun i => (ha i).ne') '' pi univ (fun _ => Ioc 0 b) =
      {z | ∀ i, 0 < z i ∧ z i ≤ a i * b} := by
  ext z
  rw [MeasurableEquiv.image_eq_preimage_symm, mem_preimage, mem_univ_pi]
  refine forall_congr' fun i => ?_
  rw [diagEquiv_symm_apply, mem_Ioc, inv_mul_le_iff₀ (ha i)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_pos_iff_of_pos_left (inv_pos.2 (ha i))).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_pos (inv_pos.2 (ha i)) h1, h2⟩

variable [Fintype ι]

theorem coe_diagEquiv [DecidableEq ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    ⇑(diagEquiv a ha) = ⇑(Matrix.toLin' (Matrix.diagonal a)) := by
  funext v i
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rfl

theorem det_toLin'_diagonal [DecidableEq ι] (a : ι → ℝ) :
    LinearMap.det (Matrix.toLin' (Matrix.diagonal a)) = ∏ i, a i := by
  rw [LinearMap.det_toLin', Matrix.det_diagonal]

theorem map_diagEquiv_volume (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    volume.map (diagEquiv a ha) = ENNReal.ofReal |(∏ i, a i)⁻¹| • volume := by
  classical
  rw [coe_diagEquiv]
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal a)) ≠ 0 := by
    rw [det_toLin'_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => ha i
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet, det_toLin'_diagonal]

/-- ★ **Fibrewise diagonal transport**: the Jacobian-weighted Lebesgue measure on `s` pushes
forward along `v ↦ (a_i v_i)` to Lebesgue measure on the image. -/
theorem map_diagEquiv_restrict_withDensity (a : ι → ℝ) (ha : ∀ i, 0 < a i) (s : Set (ι → ℝ)) :
    ((volume.restrict s).withDensity fun _ => ENNReal.ofReal (∏ i, a i)).map
        (diagEquiv a fun i => (ha i).ne') =
      volume.restrict (diagEquiv a (fun i => (ha i).ne') '' s) := by
  set e := diagEquiv a fun i => (ha i).ne'
  have h1 : (volume.restrict s).map e = (volume.map e).restrict (e '' s) := by
    rw [e.measurableEmbedding.restrict_map, preimage_image_eq _ e.injective]
  rw [withDensity_const, Measure.map_smul, h1, map_diagEquiv_volume, Measure.restrict_smul,
    smul_smul]
  have hp : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [abs_of_pos (inv_pos.2 hp), ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne',
    ENNReal.ofReal_one, one_smul]

/-- The integral form of the fibrewise transport. -/
theorem lintegral_diagEquiv_image (a : ι → ℝ) (ha : ∀ i, 0 < a i) (s : Set (ι → ℝ))
    {F : (ι → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in diagEquiv a (fun i => (ha i).ne') '' s, F z =
      ∫⁻ v in s, ENNReal.ofReal (∏ i, a i) * F (diagEquiv a (fun i => (ha i).ne') v) := by
  rw [← map_diagEquiv_restrict_withDensity a ha s,
    lintegral_map hF (diagEquiv a fun i => (ha i).ne').measurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_const
      (show Measurable fun v => F (diagEquiv a (fun i => (ha i).ne') v) from
        hF.comp (diagEquiv a fun i => (ha i).ne').measurable)]
  rfl

end Diag

/-! ### The coordinate split `ℝ^d ≃ ℝ^I × ℝ^{Iᶜ}` -/

section Split

variable {d : ℕ} (I : Finset (Fin d))

/-- The normal index type: the coordinates in `I`. -/
abbrev Nrm := {i : Fin d // i ∈ I}

/-- The tangential index type: the coordinates not in `I`. -/
abbrev Tan := {i : Fin d // ¬ i ∈ I}

/-- The coordinate split `ℝ^d ≃ᵐ ℝ^I × ℝ^{Iᶜ}` (normal part first). -/
noncomputable def split : (Fin d → ℝ) ≃ᵐ (Nrm I → ℝ) × (Tan I → ℝ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℝ) (· ∈ I)

theorem split_apply (w : Fin d → ℝ) :
    split I w = (fun i : Nrm I => w i.1, fun i : Tan I => w i.1) := rfl

theorem split_symm_apply (q : (Nrm I → ℝ) × (Tan I → ℝ)) (j : Fin d) :
    (split I).symm q j = if h : j ∈ I then q.1 ⟨j, h⟩ else q.2 ⟨j, h⟩ := rfl

theorem measurePreserving_split : MeasurePreserving (split I) volume volume := by
  have h := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (· ∈ I)
  convert h <;> rfl

variable {ι : Type*} (σ : ι ≃ Nrm I)

/-- Reindexing the normal coordinates `(ι → ℝ) ≃ᵐ (Nrm I → ℝ)` along `σ`. -/
def reindex : (ι → ℝ) ≃ᵐ (Nrm I → ℝ) where
  toFun v j := v (σ.symm j)
  invFun z i := z (σ i)
  left_inv v := by funext i; simp
  right_inv z := by funext j; simp
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem reindex_apply (v : ι → ℝ) (j : Nrm I) : reindex I σ v j = v (σ.symm j) := rfl

theorem reindex_eq_piCongrLeft :
    ⇑(reindex I σ) = ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ) := by
  funext v j
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  rfl

theorem reindex_image_pi (S : Set ℝ) :
    reindex I σ '' pi univ (fun _ => S) = pi univ fun _ => S := by
  ext z
  rw [MeasurableEquiv.image_eq_preimage_symm, mem_preimage, mem_univ_pi, mem_univ_pi]
  constructor
  · intro h j
    have := h (σ.symm j)
    change z (σ (σ.symm j)) ∈ S at this
    rwa [Equiv.apply_symm_apply] at this
  · intro h i
    exact h (σ i)

theorem measurePreserving_reindex [Fintype ι] :
    MeasurePreserving (reindex I σ) volume volume := by
  refine ⟨(reindex I σ).measurable, ?_⟩
  have h := (measurePreserving_piCongrLeft (α := fun _ : Nrm I => ℝ)
    (μ := fun _ => volume) σ).map_eq
  rw [reindex_eq_piCongrLeft]
  exact h

end Split

/-! ### The normalised box core: parametrisation, image, transport -/

namespace NormalisedBox

variable {d : ℕ} (I : Finset (Fin d)) {ι : Type*} (σ : ι ≃ Nrm I)
  {K : Type*} (e : K → (Tan I → ℝ)) (lamT : (Tan I → ℝ) → (Nrm I → ℝ)) (b : ℝ)

/-- The rescaled normal coordinates at the base point `s`: `v ↦ (λ_j(s) v_{σ⁻¹ j})_j`. -/
def normalMap (s : K) (v : ι → ℝ) : Nrm I → ℝ := fun j => lamT (e s) j * v (σ.symm j)

/-- The core parametrisation `Φ(s, v) = s + Σ_j λ_j(s) v_j e_j`. -/
noncomputable def Φ (p : K × (ι → ℝ)) : Fin d → ℝ :=
  (split I).symm (normalMap I σ e lamT p.1 p.2, e p.1)

/-- The normal box `(0,b]^ι`. -/
def box : Set (ι → ℝ) := pi univ fun _ => Ioc 0 b

/-- The normal fibre of the image over the tangential point `t`: `0 < z_j ≤ λ_j(t) b`. -/
def fibre (t : Tan I → ℝ) : Set (Nrm I → ℝ) := {z | ∀ j, 0 < z j ∧ z j ≤ lamT t j * b}

/-- The curved image of the core: tangential part in `range e`, normal part in the fibre. -/
def image : Set (Fin d → ℝ) :=
  {w | (split I w).2 ∈ range e ∧ (split I w).1 ∈ fibre I lamT b (split I w).2}

theorem Φ_apply (p : K × (ι → ℝ)) (j : Fin d) :
    Φ I σ e lamT p j =
      if h : j ∈ I then lamT (e p.1) ⟨j, h⟩ * p.2 (σ.symm ⟨j, h⟩) else e p.1 ⟨j, h⟩ := rfl

theorem split_Φ (p : K × (ι → ℝ)) :
    split I (Φ I σ e lamT p) = (normalMap I σ e lamT p.1 p.2, e p.1) :=
  (split I).apply_symm_apply _

variable {e lamT}

theorem normalMap_eq (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K) (v : ι → ℝ) :
    normalMap I σ e lamT s v =
      diagEquiv (lamT (e s)) (fun j => (hpos (e s) (mem_range_self s) j).ne') (reindex I σ v) :=
  rfl

theorem mem_image_symm (q : (Nrm I → ℝ) × (Tan I → ℝ)) :
    (split I).symm q ∈ image I e lamT b ↔ q.2 ∈ range e ∧ q.1 ∈ fibre I lamT b q.2 := by
  simp only [image, mem_ofPred_eq, MeasurableEquiv.apply_symm_apply]

section Measurability

variable [MeasurableSpace K]

/-- The base measure: coordinate Lebesgue measure on `range e`, pulled back along `e`. -/
noncomputable def baseMeasure (e : K → (Tan I → ℝ)) : Measure K :=
  (volume.restrict (range e)).comap e

theorem measurable_Φ (he : MeasurableEmbedding e) (hlam : Measurable lamT) :
    Measurable (Φ I σ e lamT) := by
  refine (split I).symm.measurable.comp (Measurable.prodMk ?_ (he.measurable.comp measurable_fst))
  exact measurable_pi_lambda _ fun j =>
    ((hlam.comp (he.measurable.comp measurable_fst)).eval).mul
      ((measurable_pi_apply (σ.symm j)).comp measurable_snd)

theorem measurableSet_fibre_prod (hlam : Measurable lamT) :
    MeasurableSet {q : (Nrm I → ℝ) × (Tan I → ℝ) | q.1 ∈ fibre I lamT b q.2} := by
  have : {q : (Nrm I → ℝ) × (Tan I → ℝ) | q.1 ∈ fibre I lamT b q.2} =
      ⋂ j, {q | 0 < q.1 j} ∩ {q | q.1 j ≤ lamT q.2 j * b} := by
    ext q
    simp only [fibre, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)
  · exact measurableSet_le ((measurable_pi_apply j).comp measurable_fst)
      (((hlam.comp measurable_snd).eval).mul_const _)

theorem measurableSet_fibre (t : Tan I → ℝ) : MeasurableSet (fibre I lamT b t) := by
  have : fibre I lamT b t = ⋂ j, {z | 0 < z j} ∩ {z | z j ≤ lamT t j * b} := by
    ext z
    simp only [fibre, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_lt measurable_const (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j) measurable_const)

theorem measurableSet_image (he : MeasurableEmbedding e) (hlam : Measurable lamT) :
    MeasurableSet (image I e lamT b) := by
  have : image I e lamT b = (split I) ⁻¹'
      ((Prod.snd ⁻¹' range e) ∩ {q : (Nrm I → ℝ) × (Tan I → ℝ) | q.1 ∈ fibre I lamT b q.2}) := by
    ext w
    simp only [image, mem_ofPred_eq, mem_preimage, mem_inter_iff]
  rw [this]
  exact (split I).measurable
    ((measurable_snd he.measurableSet_range).inter (measurableSet_fibre_prod I b hlam))

end Measurability

/-- ★ **The transport identity of the normalised box core.** The Jacobian-weighted product
measure `ν_B ⊗ Leb|_{(0,b]^ι}` with density `∏_j λ_j(s) · g(Φ(s,v))` pushes forward along `Φ` to
`g · Leb` restricted to the curved image. -/
theorem map_Φ [Fintype ι] [MeasurableSpace K] (he : MeasurableEmbedding e)
    (hlam : Measurable lamT) (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j)
    {g : (Fin d → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    (((baseMeasure I e).prod (volume.restrict (box (ι := ι) b))).withDensity
        fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) * g (Φ I σ e lamT p)).map (Φ I σ e lamT) =
      (volume.withDensity g).restrict (image I e lamT b) := by
  have hΦ := measurable_Φ I σ he hlam
  have hT : Measurable fun p : K × (ι → ℝ) => e p.1 := he.measurable.comp measurable_fst
  have hdens : Measurable fun p : K × (ι → ℝ) =>
      ENNReal.ofReal (∏ j, lamT (e p.1) j) * g (Φ I σ e lamT p) :=
    (Finset.measurable_prod _ fun j _ => (hlam.comp hT).eval).ennreal_ofReal.mul (hg.comp hΦ)
  ext A hA
  -- the product-space integrand appearing on both sides
  set Fq : (Nrm I → ℝ) × (Tan I → ℝ) → ℝ≥0∞ := fun q =>
    {q : (Nrm I → ℝ) × (Tan I → ℝ) | q.1 ∈ fibre I lamT b q.2}.indicator
      (fun q => A.indicator g ((split I).symm q)) q with hFq
  have hFq_meas : Measurable Fq :=
    ((hg.indicator hA).comp (split I).symm.measurable).indicator
      (measurableSet_fibre_prod I b hlam)
  have hFq_eq : ∀ t z, Fq (z, t) = (fibre I lamT b t).indicator
      (fun z => A.indicator g ((split I).symm (z, t))) z := by
    intro t z
    simp only [hFq, indicator, mem_ofPred_eq]
  -- the tangential integrand
  set H : (Tan I → ℝ) → ℝ≥0∞ := fun t => ∫⁻ z, Fq (z, t) with hH
  have hH_meas : Measurable H := by
    have := (hFq_meas.comp measurable_swap).lintegral_prod_right'
      (ν := (volume : Measure (Nrm I → ℝ)))
    simp only [Function.comp_def, Prod.swap_prod_mk] at this
    exact this
  -- LHS
  rw [Measure.map_apply hΦ hA, withDensity_apply _ (hΦ hA), ← lintegral_indicator (hΦ hA),
    lintegral_prod _ (hdens.indicator (hΦ hA)).aemeasurable]
  have hinner : ∀ s : K, ∫⁻ v, (Φ I σ e lamT ⁻¹' A).indicator
      (fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) * g (Φ I σ e lamT p)) (s, v)
        ∂volume.restrict (box b) = H (e s) := by
    intro s
    have hne : ∀ j, lamT (e s) j ≠ 0 := fun j => (hpos (e s) (mem_range_self s) j).ne'
    have hpos' : ∀ j, 0 < lamT (e s) j := hpos (e s) (mem_range_self s)
    set D := diagEquiv (lamT (e s)) hne
    have h1 : ∀ v, (Φ I σ e lamT ⁻¹' A).indicator
        (fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) * g (Φ I σ e lamT p)) (s, v) =
        ENNReal.ofReal (∏ j, lamT (e s) j) *
          A.indicator g ((split I).symm (D (reindex I σ v), e s)) := by
      intro v
      have hΦ' : Φ I σ e lamT (s, v) = (split I).symm (D (reindex I σ v), e s) := rfl
      rw [← hΦ']
      by_cases h : Φ I σ e lamT (s, v) ∈ A
      · rw [indicator_of_mem (show (s, v) ∈ Φ I σ e lamT ⁻¹' A from h), indicator_of_mem h]
      · rw [indicator_of_notMem (show (s, v) ∉ Φ I σ e lamT ⁻¹' A from h),
          indicator_of_notMem h, mul_zero]
    simp_rw [h1]
    have hF : Measurable fun z : Nrm I → ℝ => A.indicator g ((split I).symm (z, e s)) :=
      (hg.indicator hA).comp ((split I).symm.measurable.comp (measurable_prodMk_right))
    have h2 := ((measurePreserving_reindex I σ).restrict_image_emb
      (reindex I σ).measurableEmbedding (box b)).lintegral_comp
      (f := fun z => ENNReal.ofReal (∏ j, lamT (e s) j) *
        A.indicator g ((split I).symm (D z, e s)))
      (measurable_const.mul (hF.comp D.measurable))
    rw [h2, box, reindex_image_pi, ← lintegral_diagEquiv_image _ hpos' _ hF,
      diagEquiv_image_pi_Ioc _ hpos', hH]
    change ∫⁻ z in fibre I lamT b (e s), A.indicator g ((split I).symm (z, e s)) =
      ∫⁻ z, Fq (z, e s)
    rw [← lintegral_indicator (measurableSet_fibre I b (e s))]
    refine lintegral_congr fun z => ?_
    rw [hFq_eq]
  simp_rw [hinner]
  rw [← lintegral_map hH_meas he.measurable, baseMeasure, he.map_comap,
    Measure.restrict_restrict he.measurableSet_range, inter_self]
  -- RHS
  rw [Measure.restrict_apply hA, withDensity_apply _ (hA.inter (measurableSet_image I b he hlam)),
    ← lintegral_indicator (hA.inter (measurableSet_image I b he hlam)),
    ← (measurePreserving_split I).symm.lintegral_comp (hg.indicator
      (hA.inter (measurableSet_image I b he hlam))),
    show (volume : Measure ((Nrm I → ℝ) × (Tan I → ℝ))) =
      (volume : Measure (Nrm I → ℝ)).prod volume from rfl,
    lintegral_prod_symm (fun q => (A ∩ image I e lamT b).indicator g ((split I).symm q))
      (show Measurable fun q => (A ∩ image I e lamT b).indicator g ((split I).symm q) from
        (hg.indicator (hA.inter (measurableSet_image I b he hlam))).comp
          (split I).symm.measurable).aemeasurable]
  rw [← lintegral_indicator he.measurableSet_range]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ range e
  · rw [indicator_of_mem ht, hH]
    refine lintegral_congr fun z => ?_
    rw [hFq_eq]
    by_cases hz : z ∈ fibre I lamT b t
    · rw [indicator_of_mem hz]
      have hmem : (split I).symm (z, t) ∈ image I e lamT b := (mem_image_symm I b _).2 ⟨ht, hz⟩
      by_cases hAz : (split I).symm (z, t) ∈ A
      · rw [indicator_of_mem (show (split I).symm (z, t) ∈ A ∩ image I e lamT b from
          ⟨hAz, hmem⟩), indicator_of_mem hAz]
      · rw [indicator_of_notMem (show (split I).symm (z, t) ∉ A ∩ image I e lamT b from
          fun h => hAz h.1), indicator_of_notMem hAz]
    · rw [indicator_of_notMem hz]
      have hnot : (split I).symm (z, t) ∉ image I e lamT b := fun h =>
        hz ((mem_image_symm I b _).1 h).2
      rw [indicator_of_notMem (show (split I).symm (z, t) ∉ A ∩ image I e lamT b from
        fun h => hnot h.2)]
  · rw [indicator_of_notMem ht]
    symm
    refine (lintegral_eq_zero_iff ?_).2 ?_
    · exact ((hg.indicator (hA.inter (measurableSet_image I b he hlam))).comp
        ((split I).symm.measurable.comp (measurable_prodMk_right)))
    · refine Filter.Eventually.of_forall fun z => ?_
      have hnot : (split I).symm (z, t) ∉ image I e lamT b := fun h =>
        ht ((mem_image_symm I b _).1 h).1
      simp only [Pi.zero_apply]
      exact indicator_of_notMem (show (split I).symm (z, t) ∉ A ∩ image I e lamT b from
        fun h => hnot h.2) _

end NormalisedBox

end Grammar
