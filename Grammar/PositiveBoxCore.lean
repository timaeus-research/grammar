/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AnalyticCorePresentation
import Grammar.ResolutionTransport
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The core presentation of a positive-orthant exact box chart (Astra #68 unit 7a)

The measure-theoretic assembly of one core. A **positive box chart** on the product space
`(Fin t → ℝ) × (Fin (n+1) → ℝ)` (tangential × normal coordinates) over a measurable tangential
base `A` is a `C¹` map `Ψ`, injective on the box `A × (0,b]^{n+1}`, whose Jacobian is the monomial
`u^h` times a measurable factor `jac`, on whose box image the phase is exactly `β u^{2k}`, and
whose amplitude `jac · F∘Ψ` is realised on the box by a tangential datum
(`PositiveBoxChart`). Then the Lebesgue measure on the image of the box is the target of a
**core presentation** with base measure the Lebesgue measure of `A`, chart `Ψ`, density factor
`jac` and the given amplitude (`PositiveBoxChart.exists_corePresentation`): the transport clause is
Mathlib's change of variables `map_withDensity_abs_det_fderiv_eq_addHaar` after identifying the
chart measure `ν_A ⊗ vol|_{(0,b]^{n+1}}` with `vol|_{A × (0,b]^{n+1}}` through the product of the
subtype embedding with the identity.

The other orthants are obtained by composing `Ψ` with sign reflections (even phase exponents,
`|det|` unchanged) and enter the analytic core decomposition as further cores; the union over the
orthants recovers the full box up to the null faces. Non-claims: no orthant assembly here; the
tangential datum is a hypothesis (supplied by `jointTangentialData` after covering `A` by finitely
many joint-series centres); nothing about several charts.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {t n : ℕ}

/-- **A positive-orthant exact box chart** over the tangential base `A` with box side `b`. -/
structure PositiveBoxChart (D : LocalisationData ((Fin t → ℝ) × (Fin (n + 1) → ℝ)))
    (A : Set (Fin t → ℝ)) (b β : ℝ) where
  /-- the Jacobian exponents -/
  h : Fin (n + 1) → ℕ
  /-- the phase exponents -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- the chart -/
  Ψ : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → (Fin t → ℝ) × (Fin (n + 1) → ℝ)
  /-- an open neighbourhood of the box on which the chart is `C¹` -/
  V : Set ((Fin t → ℝ) × (Fin (n + 1) → ℝ))
  V_open : IsOpen V
  box_subset : A ×ˢ piBox (n + 1) (Ioc 0 b) ⊆ V
  contDiffOn : ContDiffOn ℝ 1 Ψ V
  injOn : InjOn Ψ (A ×ˢ piBox (n + 1) (Ioc 0 b))
  /-- the Jacobian unit -/
  jac : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ
  measurable_jac : Measurable jac
  jac_nonneg : ∀ p ∈ A ×ˢ piBox (n + 1) (Ioc 0 b), 0 ≤ jac p
  det_eq : ∀ p ∈ A ×ˢ piBox (n + 1) (Ioc 0 b),
    |(fderiv ℝ Ψ p).det| = (∏ i, p.2 i ^ h i) * jac p
  phase_eq : ∀ p ∈ A ×ˢ piBox (n + 1) (Ioc 0 b), D.phase (Ψ p) = β * ∏ i, p.2 i ^ (2 * k i)
  /-- the tangential datum realising the amplitude `jac · F∘Ψ` -/
  amp : TangentialData A (n + 1)
  amp_xi : ∀ v, xiCoord (amp v) = 0
  amp_eq : ∀ (v : A), ∀ u ∈ piBox (n + 1) (Ioc 0 b),
    evalF (toEta b (amp v)) u = jac (v.1, u) * D.obs (Ψ (v.1, u))

namespace PositiveBoxChart

variable {D : LocalisationData ((Fin t → ℝ) × (Fin (n + 1) → ℝ))} {A : Set (Fin t → ℝ)}
  {b β : ℝ} (C : PositiveBoxChart D A b β)

/-- **The core presentation of a positive box chart**: the Lebesgue measure on the image of the
box `A × (0,b]^{n+1}` is exactly presented, with base measure the Lebesgue measure of `A`. -/
theorem exists_corePresentation (hA : MeasurableSet A) (hAfin : volume A < ∞) (hb : 0 < b) :
    Nonempty (CorePresentation D (volume.restrict (C.Ψ '' (A ×ˢ piBox (n + 1) (Ioc 0 b))))
      A n β) := by
  classical
  set S := A ×ˢ piBox (n + 1) (Ioc 0 b) with hSdef
  have hS : MeasurableSet S := hA.prod (measurableSet_piBox _ _ measurableSet_Ioc)
  -- the base measure
  set ν : Measure A := Measure.comap Subtype.val volume with hν
  have hemb : MeasurableEmbedding (Subtype.val : A → Fin t → ℝ) :=
    MeasurableEmbedding.subtype_coe hA
  have hνfin : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.comap_apply _ Subtype.val_injective
      (fun s hs => hemb.measurableSet_image.2 hs) _ MeasurableSet.univ, image_univ,
      Subtype.range_coe]
    exact hAfin⟩
  -- the embedding of the parameter space into the product space
  set ι : A × (Fin (n + 1) → ℝ) → (Fin t → ℝ) × (Fin (n + 1) → ℝ) := fun p => (p.1.1, p.2)
    with hι
  have hιm : Measurable ι := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hιeq : ι = Prod.map (Subtype.val : A → Fin t → ℝ) id := by
    funext p
    rfl
  have hmem : ∀ p : A × (Fin (n + 1) → ℝ), p.2 ∈ piBox (n + 1) (Ioc 0 b) → ι p ∈ S :=
    fun p hp => ⟨p.1.2, hp⟩
  -- the measurable extension of the chart
  set Ψ' := S.piecewise C.Ψ 0 with hΨ'
  have hΨ'eq : EqOn Ψ' C.Ψ S := fun q hq => piecewise_eq_of_mem _ _ _ hq
  have hcont : ContinuousOn C.Ψ S := C.contDiffOn.continuousOn.mono C.box_subset
  have hΨ'm : Measurable Ψ' := by
    refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · have h : S.domRestrict Ψ' = S.domRestrict C.Ψ := funext fun q => hΨ'eq q.2
      rw [h]
      exact (continuousOn_iff_continuous_domRestrict.1 hcont).measurable
    · have h : Sᶜ.domRestrict Ψ' = fun _ => (0 : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :=
        funext fun q => piecewise_eq_of_notMem _ _ _ q.2
      rw [h]
      exact measurable_const
  -- the chart measure is the Lebesgue measure of the box
  have hmapι : (chartMeasure ν n b).map ι = volume.restrict S := by
    unfold chartMeasure
    rw [hιeq, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id, Measure.map_id, hν,
      hemb.map_comap, Subtype.range_coe, Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- the density
  set g : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal ((∏ i, q.2 i ^ C.h i) * C.jac q) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp ((Finset.measurable_prod _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).pow_const _).mul C.measurable_jac)
  have hdens : (fun p : A × (Fin (n + 1) → ℝ) =>
      ((chartDensity C.h (fun p => C.jac (ι p)) p).toNNReal : ℝ≥0∞)) = fun p => g (ι p) := by
    funext p
    rfl
  have hderiv : ∀ q ∈ S, HasFDerivWithinAt C.Ψ (fderiv ℝ C.Ψ q) S q := fun q hq =>
    (((C.contDiffOn.differentiableOn one_ne_zero) q (C.box_subset hq)).differentiableAt
      (C.V_open.mem_nhds (C.box_subset hq))).hasFDerivAt.hasFDerivWithinAt
  have hgdet : g =ᵐ[volume.restrict S] fun q => ENNReal.ofReal |(fderiv ℝ C.Ψ q).det| := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hS]
    refine Eventually.of_forall fun q hq => ?_
    simp only [hg]
    rw [C.det_eq q hq]
  have hΨ'ae : Ψ' =ᵐ[(volume.restrict S).withDensity g] C.Ψ := by
    refine (withDensity_absolutelyContinuous _ _).ae_eq ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hS]
    exact Eventually.of_forall fun q hq => hΨ'eq hq
  have : (volume : Measure ((Fin t → ℝ) × (Fin (n + 1) → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have htransport : ((chartMeasure ν n b).withDensity fun p =>
      ((chartDensity C.h (fun p => C.jac (ι p)) p).toNNReal : ℝ≥0∞)).map (Ψ' ∘ ι) =
      volume.restrict (C.Ψ '' S) := by
    rw [hdens, ← Measure.map_map hΨ'm hιm, map_withDensity_comp _ hιm hgm, hmapι,
      Measure.map_congr hΨ'ae, withDensity_congr_ae hgdet]
    exact map_withDensity_abs_det_fderiv_eq_addHaar volume hS.nullMeasurableSet hderiv C.injOn
  refine ⟨⟨ν, C.h, C.k, C.k_pos, b, hb, Ψ' ∘ ι, hΨ'm.comp hιm, fun p => C.jac (ι p),
    C.measurable_jac.comp hιm, ?_, C.amp, htransport, ?_, ?_, C.amp_xi⟩⟩
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    exact C.jac_nonneg _ (hmem p hp)
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    change D.phase (Ψ' (ι p)) = _
    rw [hΨ'eq (hmem p hp)]
    exact C.phase_eq _ (hmem p hp)
  · filter_upwards [ae_snd_mem_box ν n b] with p hp
    change evalF (toEta b (C.amp p.1)) p.2 = C.jac (ι p) * D.obs (Ψ' (ι p))
    rw [hΨ'eq (hmem p hp)]
    exact C.amp_eq p.1 p.2 hp

end PositiveBoxChart

end Grammar
