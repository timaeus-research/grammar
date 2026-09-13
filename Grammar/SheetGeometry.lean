/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.HironakaChartForm
import Grammar.CoordinateResolvedGeometry
import Grammar.CoreTransport

/-!
# The sheet geometry of a product-sector atlas (consult #111, unit C)

The compact resolved space attached to a product-sector atlas: the disjoint union
`Space A = Σ_i ↥(dom i)` of the closed chart boxes, with `π (i, y) = φ_i y`. Compactness of the
finitely many boxes makes `π` proper (`Continuous.isProperMap`). The divisor components are the
pairs `(i, j)` with `k_{ij} > 0` (`E (i,j) = {(i, y) : y_j = 0}`), the orders `(k_{ij}, h_{ij})`;
a stratum `S_I` is empty unless every component of `I` lies on one sheet (`sheet_eq_of_mem`), on
which its normal space is the coordinate span `N_I = span{e_j : (i,j) ∈ I}` of the coordinate
model (CCCXIII), with the coordinate conormal differentials. The tubular germ
`Φ_s(ξ) = (i, clamp_i (y + ξ))` clamps back into the box; for an active face in the interior of
the box the germ at `0` is the honest translation. A resolved geometry needs only `Φ_s 0 = s` and
continuity at `0`, both of which hold.

The transport variants `mapAmbient_ae` require the phase compatibility of the ambient map only
almost everywhere on the chart measure (and on the tail) rather than pointwise on the source
space — what a map into a sheet, which is defined by clamping, can satisfy.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open Monomialize.VolumeScaling

namespace Sheet

variable {d : ℕ} {F : (Fin d → ℝ) → ℝ} {Ω : Set (Fin d → ℝ)} (A : ProductSectorAtlas d F Ω)

/-! ### The space -/

instance (i : A.ι) : CompactSpace ↥(A.dom i) :=
  isCompact_iff_compactSpace.1 (A.toPartialResolution.dom_compact i)

/-- The sheet space: the disjoint union of the closed chart boxes. -/
def Space : Type := Σ i : A.ι, ↥(A.dom i)

instance : TopologicalSpace (Space A) := inferInstanceAs (TopologicalSpace (Σ i : A.ι, ↥(A.dom i)))
instance : T2Space (Space A) := inferInstanceAs (T2Space (Σ i : A.ι, ↥(A.dom i)))
instance : CompactSpace (Space A) := inferInstanceAs (CompactSpace (Σ i : A.ι, ↥(A.dom i)))
instance : MeasurableSpace (Space A) := borel _
instance : BorelSpace (Space A) := ⟨rfl⟩

/-- The resolution map `π (i, y) = φ_i y`. -/
def π (p : Space A) : Fin d → ℝ := A.φ p.1 p.2.1

theorem continuous_π : Continuous (π A) :=
  continuous_sigma fun i => (A.toPartialResolution.continuousOn i).comp_continuous
    continuous_subtype_val fun y => y.2

theorem isProperMap_π : IsProperMap (π A) := (continuous_π A).isProperMap

/-! ### The divisor components -/

/-- A divisor component: a chart and an active coordinate. -/
abbrev Component : Type := {c : A.ι × Fin d // 0 < A.k c.1 c.2}

noncomputable instance : DecidableEq (Component A) := Classical.decEq _

/-- The component `(i, j)` as the set `{(i, y) : y_j = 0}` of the sigma type. -/
def E' (c : Component A) : Set (Σ i : A.ι, ↥(A.dom i)) :=
  {p | p.1 = c.1.1 ∧ (p.2 : Fin d → ℝ) c.1.2 = 0}

theorem isClosed_E' (c : Component A) : IsClosed (E' A c) := by
  rw [isClosed_sigma_iff]
  intro i
  by_cases hi : i = c.1.1
  · subst hi
    have : Sigma.mk c.1.1 ⁻¹' E' A c = {y : ↥(A.dom c.1.1) | (y : Fin d → ℝ) c.1.2 = 0} := by
      ext y; simp [E']
    rw [this]
    exact isClosed_eq ((continuous_apply _).comp continuous_subtype_val) continuous_const
  · have : Sigma.mk i ⁻¹' E' A c = ∅ := by
      ext y; simp [E', hi]
    rw [this]
    exact isClosed_empty

/-- The component `(i, j)` as a subset of the sheet space. -/
def E (c : Component A) : Set (Space A) := E' A c

theorem isClosed_E (c : Component A) : IsClosed (E A c) := isClosed_E' A c

/-- ★ **The sheet geometry** of a product-sector atlas: a compact resolved space with a proper
resolution map, one divisor component per active chart coordinate. -/
noncomputable def geometry : ResolvedGeometry d (Space A) where
  π := π A
  continuous_π := continuous_π A
  proper_π := isProperMap_π A
  Component := Component A
  E := E A
  isClosed_E := isClosed_E A
  k := fun c => A.k c.1.1 c.1.2
  h := fun c => A.h c.1.1 c.1.2
  k_pos := fun c => c.2

theorem geometry_π (p : Space A) : (geometry A).π p = A.φ p.1 p.2.1 := rfl

/-- The components through a stratum point all lie on its sheet. -/
theorem sheet_eq_of_mem {I : Finset (Component A)} (s : (geometry A).Stratum I) {c : Component A}
    (hc : c ∈ I) : c.1.1 = (s : Space A).1 :=
  (((s.2 c).2 hc).1).symm

/-! ### Normal data -/

/-- The ambient coordinates of a component finset. -/
noncomputable def amb (I : Finset (Component A)) : Finset (Fin d) := I.image fun c => c.1.2

theorem mem_amb_of_mem {I : Finset (Component A)} (c : ↥I) : c.1.1.2 ∈ amb A I :=
  Finset.mem_image.2 ⟨c.1, c.2, rfl⟩

/-- On a nonempty stratum the coordinate map `c ↦ j` is injective on `I`. -/
theorem injOn_coord {I : Finset (Component A)} (s : (geometry A).Stratum I) :
    Set.InjOn (fun c : Component A => c.1.2) (I : Set (Component A)) := by
  intro c hc c' hc' h
  apply Subtype.ext
  apply Prod.ext
  · rw [sheet_eq_of_mem A s hc, sheet_eq_of_mem A s hc']
  · exact h

theorem card_amb {I : Finset (Component A)} (s : (geometry A).Stratum I) :
    (amb A I).card = I.card :=
  Finset.card_image_of_injOn (injOn_coord A s)

/-- The conormal differentials, through the ambient coordinates. -/
noncomputable def du (I : Finset (Component A)) (c : ↥I) :
    Module.Dual ℝ (CoordModel.normalSpace d (amb A I)) :=
  CoordModel.du d (amb A I) ⟨c.1.1.2, mem_amb_of_mem A c⟩

theorem linearIndependent_du {I : Finset (Component A)} (s : (geometry A).Stratum I) :
    LinearIndependent ℝ (du A I) :=
  (CoordModel.linearIndependent_du d (amb A I)).comp
    (fun c : ↥I => (⟨c.1.1.2, mem_amb_of_mem A c⟩ : ↥(amb A I)))
    fun c c' h => Subtype.ext (injOn_coord A s c.2 c'.2 (congrArg Subtype.val h))

/-- Clamping a point back into the box of chart `i`. -/
noncomputable def clamp (i : A.ι) (y : Fin d → ℝ) : Fin d → ℝ := fun j =>
  (Set.projIcc (A.lo i j) (A.hi i j) (A.lo_lt_hi i j).le (y j) : ℝ)

theorem clamp_mem (i : A.ι) (y : Fin d → ℝ) : clamp A i y ∈ A.dom i := by
  rw [A.dom_eq]
  exact fun j _ => (Set.projIcc (A.lo i j) (A.hi i j) (A.lo_lt_hi i j).le (y j)).2

theorem clamp_of_mem (i : A.ι) {y : Fin d → ℝ} (hy : y ∈ A.dom i) : clamp A i y = y := by
  rw [A.dom_eq] at hy
  funext j
  exact congrArg Subtype.val (Set.projIcc_of_mem _ (hy j (mem_univ _)))

theorem continuous_clamp (i : A.ι) : Continuous (clamp A i) :=
  continuous_pi fun j => continuous_subtype_val.comp (continuous_projIcc.comp (continuous_apply j))

/-- The tubular germ at a stratum point: translate along the normal vector and clamp back into the
box. -/
noncomputable def Φ (I : Finset (Component A)) (s : (geometry A).Stratum I)
    (ξ : CoordModel.normalSpace d (amb A I)) : Space A :=
  ⟨(s : Space A).1, ⟨clamp A (s : Space A).1 (fun j => ((s : Space A).2 : Fin d → ℝ) j +
    (ξ : CoordModel.Amb d) j), clamp_mem A _ _⟩⟩

theorem Φ_zero (I : Finset (Component A)) (s : (geometry A).Stratum I) :
    Φ A I s 0 = (s : Space A) := by
  have h : clamp A (s : Space A).1 (fun j => ((s : Space A).2 : Fin d → ℝ) j +
      ((0 : CoordModel.normalSpace d (amb A I)) : CoordModel.Amb d) j) =
      ((s : Space A).2 : Fin d → ℝ) := by
    have : (fun j => ((s : Space A).2 : Fin d → ℝ) j +
        ((0 : CoordModel.normalSpace d (amb A I)) : CoordModel.Amb d) j) =
        ((s : Space A).2 : Fin d → ℝ) := by
      funext j; simp
    rw [this, clamp_of_mem A _ (s : Space A).2.2]
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext h))

theorem continuousAt_Φ (I : Finset (Component A)) (s : (geometry A).Stratum I) :
    ContinuousAt (Φ A I s) 0 := by
  refine Continuous.continuousAt ?_
  refine continuous_sigmaMk.comp (Continuous.subtype_mk ?_ _)
  refine (continuous_clamp A _).comp (continuous_pi fun j => continuous_const.add ?_)
  exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp continuous_subtype_val

/-- ★ **The normal data of the sheet geometry**: coordinate normal spaces and conormal
differentials through the ambient coordinates, tubular germs by translation and clamping. -/
noncomputable def normalData : ResolvedNormalData (geometry A) (CoordModel.Amb d) where
  N := fun I _ => CoordModel.normalSpace d (amb A I)
  finrank_N := fun _ s => (CoordModel.finrank_normalSpace d _).trans (card_amb A s)
  finiteDimensional_N := fun _ _ => inferInstance
  du := fun I _ => du A I
  du_linearIndependent := fun _ s => linearIndependent_du A s
  Φ := Φ A
  Φ_zero := Φ_zero A
  continuousAt_Φ := continuousAt_Φ A

/-- The sheet inclusion of chart `i`: clamp into the box and place on sheet `i`. -/
noncomputable def incl (i : A.ι) (y : Fin d → ℝ) : Space A := ⟨i, ⟨clamp A i y, clamp_mem A i y⟩⟩

theorem continuous_incl (i : A.ι) : Continuous (incl A i) :=
  continuous_sigmaMk.comp (Continuous.subtype_mk (continuous_clamp A i) _)

theorem measurable_incl (i : A.ι) : Measurable (incl A i) := (continuous_incl A i).measurable

theorem π_incl (i : A.ι) {y : Fin d → ℝ} (hy : y ∈ A.dom i) : π A (incl A i y) = A.φ i y := by
  unfold π incl
  simp only
  rw [clamp_of_mem A i hy]

end Sheet

/-! ### Transport with almost-everywhere phase compatibility -/

section AmbientAe

variable {V U : Type*} [MeasurableSpace V] [MeasurableSpace U] {D : LocalisationData V}
  {target : Measure V} {K : Type*} [TopologicalSpace K] [MeasurableSpace K] {n : ℕ} {β : ℝ}

/-- Ambient transport of a core presentation with phase compatibility only almost everywhere on
the chart measure. -/
noncomputable def CorePresentation.mapAmbient_ae (C : CorePresentation D target K n β) (Ψ : V → U)
    (hΨ : Measurable Ψ) (D' : LocalisationData U)
    (hp : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.phase (Ψ (C.Φ q)) = D.phase (C.Φ q))
    (ho : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.obs (Ψ (C.Φ q)) = D.obs (C.Φ q)) :
    CorePresentation D' (target.map Ψ) K n β where
  ν := C.ν
  h := C.h
  k := C.k
  k_pos := C.k_pos
  b := C.b
  b_pos := C.b_pos
  Φ := Ψ ∘ C.Φ
  measurable_Φ := hΨ.comp C.measurable_Φ
  c := C.c
  measurable_c := C.measurable_c
  nonneg_c := C.nonneg_c
  x := C.x
  transport := by rw [← Measure.map_map hΨ C.measurable_Φ, C.transport]
  phase_normal := by
    filter_upwards [C.phase_normal, hp] with q h1 h2
    change D'.phase (Ψ (C.Φ q)) = _
    rw [h2]
    exact h1
  amplitude_eq := by
    filter_upwards [C.amplitude_eq, ho] with q h1 h2
    change _ = C.c q * D'.obs (Ψ (C.Φ q))
    rw [h2]
    exact h1
  fluct_zero := C.fluct_zero

theorem CorePresentation.mapAmbient_ae_Φ (C : CorePresentation D target K n β) (Ψ : V → U)
    (hΨ : Measurable Ψ) (D' : LocalisationData U) (hp) (ho) :
    (C.mapAmbient_ae Ψ hΨ D' hp ho).Φ = Ψ ∘ C.Φ := rfl

/-- The normal-moment presentation follows the transported core when the observables agree on the
fibre balls. -/
noncomputable def CoreNormalMomentPresentation.mapAmbient_ae {C : CorePresentation D target K n β}
    (T : CoreNormalMomentPresentation C) (Ψ : V → U) (hΨ : Measurable Ψ) (D' : LocalisationData U)
    (hp : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.phase (Ψ (C.Φ q)) = D.phase (C.Φ q))
    (ho : ∀ᵐ q ∂chartMeasure C.ν n C.b, D'.obs (Ψ (C.Φ q)) = D.obs (C.Φ q))
    (hball : ∀ v, ∀ u ∈ Metric.eball (0 : Fin (n + 1) → ℝ) (T.R v),
      D'.obs (Ψ (C.Φ (v, u))) = D.obs (C.Φ (v, u))) :
    CoreNormalMomentPresentation (C.mapAmbient_ae Ψ hΨ D' hp ho) where
  p := T.p
  R := T.R
  analytic := fun v => (T.analytic v).congr fun u hu => (hball v u hu).symm
  radius := T.radius
  cBound := T.cBound
  c_le := T.c_le

/-- Ambient transport of an analytic core decomposition with phase compatibility almost
everywhere on each chart measure and on the tail. -/
noncomputable def AnalyticCoreDecomposition.mapAmbient_ae {M : ℕ} {K : Fin M → Type*}
    [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ}
    (A : AnalyticCoreDecomposition D M K n β) (Ψ : V → U) (hΨ : Measurable Ψ)
    (D' : LocalisationData U) (hμ : D'.μ = D.μ.map Ψ)
    (hp : ∀ I, ∀ᵐ q ∂chartMeasure (A.chart I).ν (n I) (A.chart I).b,
      D'.phase (Ψ ((A.chart I).Φ q)) = D.phase ((A.chart I).Φ q))
    (htail : ∀ᵐ z ∂A.tail, D'.phase (Ψ z) = D.phase z)
    (ho : ∀ I, ∀ᵐ q ∂chartMeasure (A.chart I).ν (n I) (A.chart I).b,
      D'.obs (Ψ ((A.chart I).Φ q)) = D.obs ((A.chart I).Φ q)) :
    AnalyticCoreDecomposition D' M K n β where
  core := fun I => (A.core I).map Ψ
  tail := A.tail.map Ψ
  measure_eq := by
    rw [hμ, A.measure_eq, Measure.map_add _ _ hΨ]
    congr 1
    induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hΨ, ih]
  δ₀ := A.δ₀
  δ₀_pos := A.δ₀_pos
  gap := by
    rw [ae_map_iff hΨ.aemeasurable (measurableSet_le measurable_const D'.phase_measurable)]
    filter_upwards [A.gap, htail] with z hz h2
    change A.δ₀ ≤ D'.phase (Ψ z)
    rw [h2]
    exact hz
  chart := fun I => (A.chart I).mapAmbient_ae Ψ hΨ D' (hp I) (ho I)

end AmbientAe

end Grammar
