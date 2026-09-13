/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetAssembly
import Grammar.BlowUpCubeExpansion

/-!
# Regression: the cube through the general producer (unit I)

The cube blow-up atlas of `hironaka` (CCCLXIX), with every orthant selected (`ofAll`), satisfies
the sheet-assembly inputs (`cubeInputs`): symmetric boxes `[−1,1]^d`, active sets `{β}`, the
tangential units `1 + Σ_{γ≠β} y_γ²` (bounded below by `1`), Jacobian units `1`, and the chart
packets `A.pullbackChart β` of CCCXLVI. The general producer therefore reproduces the
coordinate-free expansion of the cube integral `∫_{[−1,1]^d} F · p · e^{−n|x|²}` on the sheet
geometry of the cube atlas (★★ `cube_hasCoordFreeExpansion_generic`), with log degree `0`
(`cubeInputs_commonD`). The hypotheses on `(p, F)` are the global ones of the producer
(measurable, `p ≥ 0`), where the dedicated cube certificate CCCLXVII used cut-offs. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling WaterFilling BlowUpCube ChartCollar

variable {d : ℕ} [NeZero d] {p F : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension 1 p F)
  (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hFm : Measurable F)

/-- The cube domain atlas: the cube blow-up atlas with every orthant selected, `W = [−1,1]^d`. -/
noncomputable def cubeDomainAtlas : DomainSectorAtlas d K (centeredBox d 1) := ofAll cubeAtlas

theorem cubeDomainAtlas_W : (cubeDomainAtlas (d := d)).W = centeredBox d 1 := rfl

theorem cubeDomainAtlas_φ (β : Fin d) : (cubeDomainAtlas (d := d)).φ β = φ β := rfl

theorem cubeDomainAtlas_jacUnit (β : Fin d) (v : Fin d → ℝ) :
    (cubeDomainAtlas (d := d)).jacUnit β v = 1 := rfl

/-- The analytic prior factor of a cube chart is `p ∘ φ_β`. -/
theorem cubePriorFactor_eq (β : Fin d) :
    (fun v => |(cubeDomainAtlas (d := d)).jacUnit β v| * p ((cubeDomainAtlas (d := d)).φ β v)) =
      p ∘ φ β := by
  funext v
  rw [cubeDomainAtlas_jacUnit, abs_one, one_mul]
  rfl

omit [NeZero d] in
include A hFm in
/-- The observable is integrable for the prior measure on the cube (both are continuous on the
compact cube, from the packet). -/
theorem cube_obs_int :
    Integrable F ((volume.restrict (centeredBox d 1)).withDensity fun w =>
      ENNReal.ofReal (p w)) := by
  rw [centeredBox_one_eq_cube]
  obtain ⟨Cp, hCp⟩ := isCompact_cube.exists_bound_of_continuousOn A.continuousOn_prior
  obtain ⟨CF, hCF⟩ := isCompact_cube.exists_bound_of_continuousOn A.continuousOn_obs
  have hm : MeasurableSet (cube d) := isCompact_cube.isClosed.measurableSet
  have : IsFiniteMeasure ((volume.restrict (cube d)).withDensity fun w =>
      ENNReal.ofReal (p w)) := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ w, ENNReal.ofReal (p w) ∂(volume.restrict (cube d))
        ≤ ∫⁻ _, ENNReal.ofReal Cp ∂(volume.restrict (cube d)) := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hm]
          refine Eventually.of_forall fun w hw => ENNReal.ofReal_le_ofReal ?_
          have := hCp w hw
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal Cp * volume (cube d) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top isCompact_cube.measure_lt_top
  refine (integrable_const CF).mono' hFm.aestronglyMeasurable ?_
  refine Filter.le_def.1 (withDensity_absolutelyContinuous _ _).ae_le _ ?_
  change ∀ᵐ w ∂volume.restrict (cube d), ‖F w‖ ≤ CF
  rw [ae_restrict_iff' hm]
  exact Eventually.of_forall fun w hw => hCF w hw

/-- ★★ **The cube satisfies the sheet-assembly inputs**: the cube domain atlas, half side `1`,
units bounded below by `1`, the chart packets `A.pullbackChart β`. -/
noncomputable def cubeInputs : SheetInputs d where
  K := K
  K_m := continuous_K.measurable
  Ω := centeredBox d 1
  A := cubeDomainAtlas
  a := 1
  ha := one_pos
  lo_eq := fun (β : Fin d) (j : Fin d) => by
    change -(if j = β then (1 : ℝ) else 1) = -1
    simp
  hi_eq := fun (β : Fin d) (j : Fin d) => by
    change (if j = β then (1 : ℝ) else 1) = 1
    simp
  φ_m := fun (β : Fin d) => (continuous_φ β).measurable
  jacUnit_m := fun _ => measurable_const
  act_nonempty := fun (β : Fin d) => ⟨β, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
    change 0 < (if β = β then 1 else 0)
    simp⟩⟩
  hu_cont := fun (β : Fin d) => continuous_unit β
  hu_tan := fun (β : Fin d) w w' h => unit_tan β w w' fun j hj => h j (by
    change ¬ 0 < (if j = β then 1 else 0)
    simp [hj])
  c := fun _ => 1
  hc := fun _ => one_pos
  hu_lb := fun (β : Fin d) w _ => one_le_unit β w
  prior := p
  obs := F
  prior_m := hp
  prior_nonneg := hp0
  obs_m := hFm
  obs_int := cube_obs_int A hFm
  P := fun (β : Fin d) =>
    cast (by rw [cubePriorFactor_eq, cubeDomainAtlas_φ]) (A.pullbackChart β)
  signs_nonempty := fun _ => Finset.univ_nonempty
  ι_nonempty := ⟨(0 : Fin d)⟩

theorem cubeInputs_SA : (cubeInputs A hp hp0 hFm).SA = cubeAtlas := rfl

theorem cubeInputs_W : (cubeInputs A hp hp0 hFm).A.W = centeredBox d 1 := rfl

/-- The active set of a cube chart is the pivot. -/
theorem cubeInputs_act (β : Fin d) : (cubeInputs A hp hp0 hFm).act β = {β} := by
  unfold SheetInputs.act
  ext j
  rw [Finset.mem_filter, Finset.mem_singleton]
  change (j ∈ Finset.univ ∧ 0 < (if j = β then 1 else 0)) ↔ j = β
  constructor
  · rintro ⟨-, h⟩
    by_contra hne
    rw [if_neg hne] at h
    exact lt_irrefl _ h
  · rintro rfl
    exact ⟨Finset.mem_univ _, by rw [if_pos rfl]; exact one_pos⟩

theorem cubeInputs_act_card (β : Fin d) : ((cubeInputs A hp hp0 hFm).act β).card = 1 := by
  rw [cubeInputs_act, Finset.card_singleton]

/-- ★★ **Regression**: the general producer reproduces the coordinate-free expansion of the cube
integral `∫_{[−1,1]^d} F · p · e^{−n|x|²}` on the sheet geometry of the cube blow-up atlas. -/
theorem cube_hasCoordFreeExpansion_generic :
    (Sheet.normalData (cubeAtlas (d := d))).HasCoordFreeExpansion
      (cubeInputs A hp hp0 hFm).cert.stratumMeasure (cubeInputs A hp hp0 hFm).coeffCert.field
      (spectrumLe (commonQ (cubeInputs A hp hp0 hFm).cert.cores.k)
        (commonD (cubeInputs A hp hp0 hFm).cert.n))
      (centeredBox d 1) K p F :=
  (cubeInputs A hp hp0 hFm).hasCoordFreeExpansion

/-- The normal dimension of every core is one: `n = 0`. -/
theorem cubeInputs_n (k : Fin (cubeInputs A hp hp0 hFm).N) :
    (cubeInputs A hp hp0 hFm).cert.n k = 0 := by
  change (amb ((cubeInputs A hp hp0 hFm).act _) _).card - 1 = 0
  exact Nat.sub_eq_zero_of_le ((Finset.card_le_card (amb_subset _ _)).trans
    (cubeInputs_act_card A hp hp0 hFm _).le)

/-- ★ **No logarithms for the cube**: the produced log degree is `0`. -/
theorem cubeInputs_commonD : commonD (cubeInputs A hp hp0 hFm).cert.n = 0 :=
  le_antisymm (Finset.sup_le fun k _ => (cubeInputs_n A hp hp0 hFm k).le) (Nat.zero_le _)

end SheetAssembly

end Grammar
