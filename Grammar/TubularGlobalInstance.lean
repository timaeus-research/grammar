/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularLocalInstance

/-!
# The global analytic tubular equivalence of a compact analytic LCI stratum

`TubularLocalInstance` produces, near every point of a compact analytic LCI stratum `S ⊆ ℝ^d`,
a graph parametrisation over a piece of the tangent space and the resulting tubular equivalence
over that piece. This file glues the pieces into a structure on the whole stratum:

* `ModelGraphChart` — a tangent-graph chart transported to the fixed model `ℝ^{d−r}` through a
  linear isomorphism of the tangent space (`finrank_tangentSpaceOf`, `exists_modelGraphChart`).
* `Stratum A` — the stratum as a type tagged by its atlas, with the charted-space structure whose
  chart at `x` is the tangential coordinate of a model graph chart at `x` (`modelChart`,
  `instChartedSpaceStratum`), a real-analytic manifold (`instIsManifoldStratum`: transition maps
  are `ft' ∘ emb`).
* `contMDiff_val` — the inclusion `Stratum A → ℝ^d` is real-analytic; `contMDiffOn_foot` — the
  foot projection of an analytic tube, viewed in the stratum, is real-analytic on the tube.
* `stratumFrameData` — the Jacobian-row frame–coframe atlas over the whole stratum, indexed by
  the atlas charts, and `liftedFoot_stratum` — the `LiftedFoot` with `emb` the inclusion and `P`
  the foot.
* `exists_global_tubular_equivalence_analytic` — the headline: for a compact analytic LCI
  stratum, strucdual's analytic tube `U` is real-analytically equivalent to the certified domain
  `{‖n‖ < ε}` of the Jacobian-row normal bundle over the manifold `Stratum A`, by
  `Ψ (x, n) = x + Σ_a n_a ∇G_a(x)`, with `Ψ (x, 0) = x` and real-analytic inverse
  `y ↦ (proj y, (J Jᵀ)⁻¹ J (y − proj y))` — the paper's tubular neighbourhood
  (`Φ : NX → M`, a diffeomorphism from a neighbourhood of the zero section restricting to the
  inclusion on it), in the analytic category and without a metric.
-/

open scoped Manifold ContDiff Matrix
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology

namespace Grammar

section Model

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S)

/-- The tangent space of a chart at a stratum point has dimension `d − r`. -/
theorem finrank_tangentSpaceOf (i : A.ι) {s : Fin d → ℝ} (hs : s ∈ S) (hsi : s ∈ A.V i) :
    Module.finrank ℝ ↥(tangentSpaceOf (A.J i s)) = d - r := by
  have h := LinearMap.finrank_range_add_finrank_ker (A.J i s).mulVecLin
  have hr : LinearMap.range (A.J i s).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 (fullRowRank_iff_surjective.1 (A.fullRank i hs hsi))
  rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  have hker : Module.finrank ℝ ↥(tangentSpaceOf (A.J i s)) =
    Module.finrank ℝ ↥(LinearMap.ker (A.J i s).mulVecLin) := rfl
  omega

/-- **A model graph chart** of the stratum at `s`: a tangent-graph chart transported to the fixed
model `ℝ^{d−r}` — an open `W ⊆ ℝ^{d−r}`, an open ambient `V'` around `s`, the analytic graph
parametrisation `emb : W → S ∩ V'` and its analytic two-sided inverse `ft` on `S ∩ V'`. -/
structure ModelGraphChart (A : CompatibleAnalyticLCIAtlas r S) (s : Fin d → ℝ) where
  /-- The atlas chart containing the piece. -/
  i : A.ι
  /-- The parameter domain in the model. -/
  W : Opens (Fin (d - r) → ℝ)
  /-- The ambient neighbourhood of `s` on which the graph description holds. -/
  V' : Set (Fin d → ℝ)
  isOpen_V' : IsOpen V'
  V'_subset : V' ⊆ A.V i
  s_mem : s ∈ S ∩ V'
  /-- The graph parametrisation. -/
  emb : (Fin (d - r) → ℝ) → Fin d → ℝ
  contDiffOn_emb : ContDiffOn ℝ ω emb (W : Set (Fin (d - r) → ℝ))
  emb_mem : ∀ z ∈ W, emb z ∈ S ∩ V'
  /-- The model coordinate. -/
  ft : (Fin d → ℝ) → (Fin (d - r) → ℝ)
  contDiff_ft : ContDiff ℝ ω ft
  ft_mem : ∀ x ∈ S ∩ V', ft x ∈ W
  emb_ft : ∀ x ∈ S ∩ V', emb (ft x) = x
  ft_emb : ∀ z ∈ W, ft (emb z) = z

/-- Every point of the stratum has a model graph chart. -/
theorem exists_modelGraphChart {s : Fin d → ℝ} (hs : s ∈ S) :
    Nonempty (ModelGraphChart A s) := by
  obtain ⟨i, hsi⟩ := A.cover hs
  obtain ⟨C⟩ := exists_tangentGraphChart A i hs hsi
  have hfin : Module.finrank ℝ ↥(tangentSpaceOf (A.J i s)) =
      Module.finrank ℝ (Fin (d - r) → ℝ) := by
    rw [finrank_tangentSpaceOf A i hs hsi, Module.finrank_fin_fun]
  let e : ↥(tangentSpaceOf (A.J i s)) ≃L[ℝ] (Fin (d - r) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq hfin
  have hft_emb : ∀ w ∈ C.W, C.ft (C.emb w) = w := by
    intro w hw
    have hmem := C.emb_mem w hw
    exact C.emb_injOn (C.ft_mem _ hmem) hw (C.emb_ft _ hmem)
  refine ⟨⟨i, ⟨e.symm ⁻¹' (C.W : Set _), C.W.isOpen.preimage e.symm.continuous⟩, C.V', C.isOpen_V',
    C.V'_subset, C.s_mem, fun z => C.emb (e.symm z), ?_, fun z hz => C.emb_mem _ hz,
    fun x => e (C.ft x),
    e.contDiff.comp C.contDiff_ft, ?_, ?_, ?_⟩⟩
  · exact C.contDiffOn_emb.comp e.symm.contDiff.contDiffOn (mapsTo_preimage _ _)
  · intro x hx
    change e.symm (e (C.ft x)) ∈ C.W
    rw [e.symm_apply_apply]
    exact C.ft_mem x hx
  · intro x hx
    rw [e.symm_apply_apply]
    exact C.emb_ft x hx
  · intro z hz
    rw [hft_emb _ hz, e.apply_symm_apply]

end Model

section StratumType

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S)

/-- **The stratum as a type**, tagged by its atlas so that the graph charted-space structure below
is an instance. -/
def Stratum (_A : CompatibleAnalyticLCIAtlas r S) : Type := ↥S

variable {A}

instance : TopologicalSpace (Stratum A) := inferInstanceAs (TopologicalSpace ↥S)

/-- A point of the stratum as an ambient vector. -/
def Stratum.val (x : Stratum A) : Fin d → ℝ := Subtype.val (x : ↥S)

/-- A stratum point from an ambient vector in `S`. -/
def Stratum.mk (x : Fin d → ℝ) (hx : x ∈ S) : Stratum A := (⟨x, hx⟩ : ↥S)

theorem Stratum.val_mem (x : Stratum A) : x.val ∈ S := (x : ↥S).2

@[simp] theorem Stratum.val_mk (x : Fin d → ℝ) (hx : x ∈ S) : (Stratum.mk (A := A) x hx).val = x :=
  rfl

theorem Stratum.ext {x y : Stratum A} (h : x.val = y.val) : x = y := Subtype.ext h

theorem Stratum.val_injective : Injective (Stratum.val (A := A)) := Subtype.val_injective

theorem Stratum.continuous_val : Continuous (Stratum.val (A := A)) := continuous_subtype_val

theorem Stratum.isInducing_val : IsInducing (Stratum.val (A := A)) := IsInducing.subtypeVal

/-- A chosen model graph chart at each point of the stratum. -/
noncomputable def chartData (x : Stratum A) : ModelGraphChart A x.val :=
  Classical.choice (exists_modelGraphChart A x.val_mem)

open Classical in
/-- The inverse chart: the graph parametrisation on `W` (the point `x` elsewhere). -/
noncomputable def chartInv (x : Stratum A) (z : Fin (d - r) → ℝ) : Stratum A :=
  if h : z ∈ (chartData x).W then
    Stratum.mk ((chartData x).emb z) (mem_of_mem_inter_left ((chartData x).emb_mem z h)) else x

theorem chartInv_val (x : Stratum A) {z : Fin (d - r) → ℝ} (hz : z ∈ (chartData x).W) :
    (chartInv x z).val = (chartData x).emb z := by
  rw [chartInv, dif_pos hz, Stratum.val_mk]

/-- **The chart of the stratum at `x`**: the model coordinate of the chosen graph chart, with
inverse the graph parametrisation. -/
noncomputable def modelChart (x : Stratum A) :
    OpenPartialHomeomorph (Stratum A) (Fin (d - r) → ℝ) where
  toFun y := (chartData x).ft y.val
  invFun := chartInv x
  source := {y | y.val ∈ (chartData x).V'}
  target := (chartData x).W
  map_source' y hy := (chartData x).ft_mem y.val ⟨y.val_mem, hy⟩
  map_target' z hz := by
    change (chartInv x z).val ∈ (chartData x).V'
    rw [chartInv_val x hz]
    exact mem_of_mem_inter_right ((chartData x).emb_mem z hz)
  left_inv' y hy := by
    refine Stratum.ext ?_
    rw [chartInv_val x ((chartData x).ft_mem y.val ⟨y.val_mem, hy⟩)]
    exact (chartData x).emb_ft y.val ⟨y.val_mem, hy⟩
  right_inv' z hz := by
    rw [chartInv_val x hz]
    exact (chartData x).ft_emb z hz
  open_source := (chartData x).isOpen_V'.preimage Stratum.continuous_val
  open_target := (chartData x).W.isOpen
  continuousOn_toFun :=
    ((chartData x).contDiff_ft.continuous.comp Stratum.continuous_val).continuousOn
  continuousOn_invFun := by
    intro z hz
    rw [Stratum.isInducing_val.continuousWithinAt_iff]
    exact ((chartData x).contDiffOn_emb.continuousOn z hz).congr
      (fun z' hz' => chartInv_val x hz') (chartInv_val x hz)

theorem modelChart_apply (x y : Stratum A) : modelChart x y = (chartData x).ft y.val := rfl

theorem modelChart_symm_apply (x : Stratum A) {z : Fin (d - r) → ℝ} (hz : z ∈ (chartData x).W) :
    ((modelChart x).symm z).val = (chartData x).emb z :=
  chartInv_val x hz

theorem modelChart_source (x : Stratum A) :
    (modelChart x).source = {y | y.val ∈ (chartData x).V'} := rfl

theorem modelChart_target (x : Stratum A) : (modelChart x).target = (chartData x).W := rfl

/-- **The graph charted-space structure on the stratum.** -/
noncomputable instance instChartedSpaceStratum : ChartedSpace (Fin (d - r) → ℝ) (Stratum A) where
  atlas := range (modelChart (A := A))
  chartAt := modelChart
  mem_chart_source x := (chartData x).s_mem.2
  chart_mem_atlas x := mem_range_self x

theorem chartAt_eq (x : Stratum A) : chartAt (Fin (d - r) → ℝ) x = modelChart x := rfl

/-- **The stratum is a real-analytic manifold**: transition maps are `ft' ∘ emb`. -/
instance instIsManifoldStratum : IsManifold 𝓘(ℝ, Fin (d - r) → ℝ) ω (Stratum A) := by
  refine isManifold_of_contDiffOn 𝓘(ℝ, Fin (d - r) → ℝ) ω (Stratum A) fun e e' he he' => ?_
  obtain ⟨x, rfl⟩ := he
  obtain ⟨x', rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, preimage_id, range_id, inter_univ]
  have hsub : ((modelChart x).symm ≫ₕ modelChart x').source ⊆ (chartData x).W := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1
  refine (((chartData x').contDiff_ft.comp_contDiffOn
    ((chartData x).contDiffOn_emb.mono hsub))).congr fun z hz => ?_
  rw [OpenPartialHomeomorph.trans_apply, modelChart_apply, modelChart_symm_apply x (hsub hz)]
  rfl

/-- **The inclusion of the stratum is real-analytic.** -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, Fin (d - r) → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (Stratum.val (A := A)) := by
  intro x
  refine contMDiffAt_iff.2 ⟨Stratum.continuous_val.continuousAt, ?_⟩
  refine ContDiffAt.contDiffWithinAt ?_
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    Function.comp_id, Function.id_comp, chartAt_eq, modelChart_apply]
  have hmem : (chartData x).ft x.val ∈ (chartData x).W := (chartData x).ft_mem _ (chartData x).s_mem
  refine ((chartData x).contDiffOn_emb.contDiffAt
    ((chartData x).W.isOpen.mem_nhds hmem)).congr_of_eventuallyEq ?_
  filter_upwards [(chartData x).W.isOpen.mem_nhds hmem] with z hz
  exact modelChart_symm_apply x hz

end StratumType

section Foot

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S}

open Classical in
/-- **The foot in the stratum**: `y ↦ proj y` on the tube (a fixed point `x₀` elsewhere). -/
noncomputable def stratumFoot (T : NormalTubularChart A.normal S) (x₀ : Stratum A) :
    (Fin d → ℝ) → Stratum A := fun y =>
  if h : y ∈ T.U then Stratum.mk (T.proj y) (T.proj_mem h) else x₀

theorem stratumFoot_val (T : NormalTubularChart A.normal S) (x₀ : Stratum A) {y : Fin d → ℝ}
    (hy : y ∈ T.U) : (stratumFoot T x₀ y).val = T.proj y := by
  simp only [stratumFoot, dif_pos hy, Stratum.val_mk]

/-- **The foot is real-analytic on an analytic tube**, as a map into the stratum. -/
theorem contMDiffOn_foot (T : AnalyticNormalTubularChart A.normal S) (x₀ : Stratum A) :
    ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin (d - r) → ℝ) ω (stratumFoot T.toNormalTubularChart x₀)
      T.U := by
  intro y hy
  refine ContMDiffAt.contMDiffWithinAt (contMDiffAt_iff.2 ⟨?_, ?_⟩)
  · rw [Stratum.isInducing_val.continuousAt_iff]
    refine (T.analyticAt_proj hy).continuousAt.congr ?_
    filter_upwards [T.isOpen_U.mem_nhds hy] with y' hy'
    exact (stratumFoot_val _ x₀ hy').symm
  · refine ContDiffAt.contDiffWithinAt ?_
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      Function.comp_id, Function.id_comp, chartAt_eq]
    set x := stratumFoot T.toNormalTubularChart x₀ y with hx
    have h1 : ContDiffAt ℝ ω (fun y' => (chartData x).ft (T.proj y')) y :=
      (chartData x).contDiff_ft.contDiffAt.comp y (T.analyticAt_proj hy).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [T.isOpen_U.mem_nhds hy] with y' hy'
    change modelChart x (stratumFoot T.toNormalTubularChart x₀
      ((OpenPartialHomeomorph.refl (Fin d → ℝ)).symm y')) = _
    rw [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq, modelChart_apply,
      stratumFoot_val _ x₀ hy']

end Foot

section Global

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S)

/-- **The Jacobian-row frame–coframe atlas over the whole stratum**, indexed by the atlas charts:
on `S ∩ V_i` the frame is `c ↦ J_i(x)ᵀ c` and the coframe `(J_i J_iᵀ)⁻¹ J_i`, both analytic. -/
noncomputable def stratumFrameData :
    FrameCoframeData 𝓘(ℝ, Fin (d - r) → ℝ) (Fin r → ℝ) ω
      (fun x : Stratum A => A.normal x.val) A.ι where
  baseSet i := {x | x.val ∈ A.V i}
  isOpen_baseSet i := (A.isOpen_V i).preimage Stratum.continuous_val
  indexAt x := Classical.choose (A.cover x.val_mem)
  mem_baseSet_at x := Classical.choose_spec (A.cover x.val_mem)
  frame i x := rowFrame A i x.val
  range_frame i x hx := range_rowFrame A i x.val_mem hx
  contMDiffOn_frame i x _ :=
    ((contDiffAt_rowFrame A i x.val).contMDiffAt.comp x (contMDiff_val x)).contMDiffWithinAt
  coframe i x := rowCoframe A i x.val
  coframe_frame i x hx v := rowCoframe_rowFrame A i x.val_mem hx v
  contMDiffOn_coframe i x hx :=
    ((contDiffAt_rowCoframe A i x.val_mem hx).contMDiffAt.comp x
      (contMDiff_val x)).contMDiffWithinAt

/-- **The global lifted foot**: the inclusion of the stratum, the Jacobian-row atlas and the foot
of an analytic tube form a real-analytic `LiftedFoot` on the whole tube. -/
theorem liftedFoot_stratum (T : AnalyticNormalTubularChart A.normal S) (x₀ : Stratum A) :
    LiftedFoot T.toNormalTubularChart (Stratum.val (A := A)) (stratumFrameData A)
      (stratumFoot T.toNormalTubularChart x₀) where
  contMDiff_emb := contMDiff_val
  emb_mem x := x.val_mem
  emb_injective := Stratum.val_injective
  contMDiffOn_P := contMDiffOn_foot T x₀
  emb_P _ hy := stratumFoot_val _ x₀ hy
  contDiffAt_ncoord _ hy := (T.analyticAt_ncoord hy).contDiffAt

/-- `Ψ` restricts to the inclusion on the zero section. -/
theorem tubeMap_zero_section (x : Stratum A) :
    tubeMap (Stratum.val (A := A)) (stratumFrameData A) ⟨x, 0⟩ = x.val := by
  change x.val + (stratumFrameData A).frame ((stratumFrameData A).indexAt x) x 0 = x.val
  rw [map_zero, add_zero]

/-- **The global analytic tubular equivalence of a compact analytic LCI stratum.** For a compact
`S ⊆ ℝ^d` with a compatible analytic LCI atlas `A` (and `S ≠ ∅`), strucdual's analytic tube `U`
is real-analytically equivalent to the certified domain `{‖n‖ < ε}` of the Jacobian-row normal
bundle over the analytic manifold `Stratum A`: an open partial homeomorphism `Ψ` with
`Ψ (x, n) = x + Σ_a n_a ∇G_a(x)`, `Ψ (x, 0) = x`, real-analytic, with real-analytic inverse
`y ↦ (proj y, (J Jᵀ)⁻¹ J (y − proj y))` on `U`. -/
theorem exists_global_tubular_equivalence_analytic (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ T : AnalyticNormalTubularChart A.normal S,
      ∃ Ψ : OpenPartialHomeomorph
          (TotalSpace (Fin r → ℝ) (stratumFrameData A).toAtlas.toCore.Fiber) (Fin d → ℝ),
        Ψ.source = tubeDom T.toNormalTubularChart (Stratum.val (A := A)) (stratumFrameData A) ∧
        Ψ.target = T.U ∧
        (∀ p, Ψ p = p.1.val + (stratumFrameData A).toAtlas.realise p) ∧
        (∀ x : Stratum A, Ψ ⟨x, 0⟩ = x.val) ∧
        (∀ y ∈ T.U, (Ψ.symm y).1.val = T.proj y) ∧
        ContMDiff (𝓘(ℝ, Fin (d - r) → ℝ).prod 𝓘(ℝ, Fin r → ℝ)) 𝓘(ℝ, Fin d → ℝ) ω Ψ ∧
        ContMDiffOn 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin (d - r) → ℝ).prod 𝓘(ℝ, Fin r → ℝ)) ω
          Ψ.symm T.U := by
  obtain ⟨T⟩ := exists_analyticNormalTubularChart_of_atlas hS A
  obtain ⟨s, hs⟩ := hne
  have h := liftedFoot_stratum A T (Stratum.mk s hs)
  refine ⟨T, tubeHomeomorph h, rfl, rfl, fun _ => rfl, tubeMap_zero_section A, fun y hy => ?_,
    contMDiff_tubeMap h, contMDiffOn_tubeInv h⟩
  change (tubeInv _ _ _ h y).1.val = T.proj y
  rw [tubeInv_proj]
  exact stratumFoot_val _ _ hy

end Global

end Grammar
