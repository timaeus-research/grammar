/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartPieces
import Grammar.CoreSigma
import Monomialize.Transport.DomainSectorAtlas
import Monomialize.Transport.DomainSectorAtlasBoundary
import Monomialize.Transport.WeightedSectorAtlas

/-!
# The pieces of a domain-sector atlas on the sheet geometry (unit H, part 2)

For a domain-sector atlas with symmetric chart boxes `[−a,a]^d`, positive
tangential units and holomorphic signed-box packets for the analytic prior factor
`|jacUnit_i| · prior ∘ φ_i` and the observable `obs ∘ φ_i` (`SheetInputs`), every selected orthant
`σ ∈ signs i` of every chart `i` is a piece (`PIdx`) with its chart-box certificate (CCCLXXIV) at
a collar level chosen per chart (`exists_delta_chart'`, which also keeps the fibre balls inside
the box). The piece data are pushed onto the sheet geometry (CCCLXX) along
`Ψ_p = incl_i ∘ R_σ`, with the phase `K ∘ π` and the observable `obs ∘ π`, compatible on the box
(`phase_compat`, `obs_compat`), the cores transported by `mapAmbient_ae` and based on the sheet
strata (`baseHomeo`), and the transported measures sum, through the reflection push-forward of
CCCLXXIV and the domain transport of the atlas, to the prior measure on `W` (★ `datum_map_π`).
The integrability of the observable on every piece follows from its integrability on the domain
(`hφint`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling NormalisedBox WaterFilling CoordModel ChartCollar

/-! ### The inputs -/

/-- The inputs of the sheet assembly: a domain-sector atlas with symmetric chart boxes, positive
tangential units, measurable chart data, a nonnegative measurable prior, an
observable integrable for the prior measure on the domain, and holomorphic signed-box packets for
the analytic prior factor and the observable of every chart. -/
structure SheetInputs (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  K_m : Measurable K
  /-- the resolved set of the atlas -/
  Ω : Set (Fin d → ℝ)
  /-- the weighted domain atlas (chart weights `ω_i`, exact weighted transport) -/
  A : WeightedDomainAtlas d K Ω
  /-- the half side of the chart boxes -/
  a : ℝ
  ha : 0 < a
  lo_eq : ∀ i j, A.lo i j = -a
  hi_eq : ∀ i j, A.hi i j = a
  φ_m : ∀ i, Measurable (A.φ i)
  jacUnit_m : ∀ i, Measurable (A.jacUnit i)
  hu_cont : ∀ i, Continuous (A.phaseUnit i)
  hu_tan : ∀ i (w w' : Fin d → ℝ), (∀ j, ¬ 0 < A.k i j → w j = w' j) →
    A.phaseUnit i w = A.phaseUnit i w'
  /-- the lower bounds of the units on the boxes -/
  c : A.ι → ℝ
  hc : ∀ i, 0 < c i
  hu_lb : ∀ i, ∀ w ∈ piBox d (Icc (-a) a), c i ≤ A.phaseUnit i w
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  /-- the observable -/
  obs : (Fin d → ℝ) → ℝ
  prior_m : Measurable prior
  prior_nonneg : ∀ w, 0 ≤ prior w
  obs_m : Measurable obs
  obs_int : Integrable obs ((volume.restrict A.W).withDensity fun w => ENNReal.ofReal (prior w))
  /-- the packets of the charts -/
  P : ∀ i, HolomorphicSignedBoxExtension a (fun v => |A.jacUnit i v| * prior (A.φ i v))
    (obs ∘ A.φ i)
  signs_nonempty : ∀ i, (A.signs i).Nonempty
  ι_nonempty : Nonempty A.ι
  /-- the radius within which the weights are constant along every active coordinate -/
  t₀ : ℝ
  t₀_pos : 0 < t₀
  /-- the weights do not depend on an active coordinate of absolute value `≤ t₀` -/
  ω_indep : ∀ i j, 0 < A.k i j → ∀ y : Fin d → ℝ, |y j| ≤ t₀ →
    A.ω i (Function.update y j 0) = A.ω i y
  /-- the weights are continuous near the divisor -/
  ω_contOn : ∀ i, ContinuousOn (A.ω i) {y | ∃ j, 0 < A.k i j ∧ |y j| ≤ t₀}

variable {d : ℕ} (X : SheetInputs d)

namespace SheetInputs

/-- The active set of chart `i`. -/
def act (i : X.A.ι) : Finset (Fin d) := Finset.univ.filter fun j => 0 < X.A.k i j

theorem hkA (i : X.A.ι) : ∀ j ∈ X.act i, 0 < X.A.k i j := fun _ hj => (Finset.mem_filter.1 hj).2

theorem hk0 (i : X.A.ι) : ∀ j, j ∉ X.act i → X.A.k i j = 0 := fun j hj => by
  by_contra h
  exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩)

theorem hu_tan' (i : X.A.ι) : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ X.act i → w j = w' j) →
    X.A.phaseUnit i w = X.A.phaseUnit i w' :=
  fun w w' hw => X.hu_tan i w w' fun j hj => hw j fun hj' => hj (Finset.mem_filter.1 hj').2

/-- The analytic prior factor of chart `i`. -/
def ϕ (i : X.A.ι) : (Fin d → ℝ) → ℝ := fun v => |X.A.jacUnit i v| * X.prior (X.A.φ i v)

theorem ϕ_m (i : X.A.ι) : Measurable (X.ϕ i) :=
  (X.jacUnit_m i).abs.mul (X.prior_m.comp (X.φ_m i))

theorem ϕ_nonneg (i : X.A.ι) : ∀ w, 0 ≤ X.ϕ i w := fun _ =>
  mul_nonneg (abs_nonneg _) (X.prior_nonneg _)

theorem dom_eq (i : X.A.ι) : X.A.dom i = piBox d (Icc (-X.a) X.a) := by
  rw [X.A.dom_eq]
  simp only [X.lo_eq, X.hi_eq]
  rfl

/-- The product-chart atlas underlying the weighted domain atlas. -/
abbrev SA : ProductChartAtlas d X.K X.Ω := X.A.toProductChartAtlas

/-- The weighted analytic prior factor of chart `i`: `ω_i · |jacUnit_i| · prior ∘ φ_i`. -/
def ϕw (i : X.A.ι) : (Fin d → ℝ) → ℝ := fun v => X.A.ω i v * X.ϕ i v

theorem ϕw_m (i : X.A.ι) : Measurable (X.ϕw i) := (X.A.ω_measurable i).mul (X.ϕ_m i)

theorem ϕw_nonneg (i : X.A.ι) : ∀ w, 0 ≤ X.ϕw i w := fun w =>
  mul_nonneg (X.A.ω_nonneg i w) (X.ϕ_nonneg i w)

/-- The weights are constant along the active coordinates of absolute value `≤ t₀`: two points
agreeing off a set `J` of such coordinates, the second vanishing on `J`, have the same weight. -/
theorem ω_eq_of_agree (i : X.A.ι) (J : Finset (Fin d)) (y' : Fin d → ℝ) :
    ∀ y : Fin d → ℝ, (∀ j ∈ J, 0 < X.A.k i j ∧ |y j| ≤ X.t₀ ∧ y' j = 0) →
      (∀ j, j ∉ J → y j = y' j) → X.A.ω i y = X.A.ω i y' := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro y _ hoff
    congr 1
    funext j
    exact hoff j (Finset.notMem_empty j)
  | insert j J hj ih =>
    intro y hJ hoff
    have hjJ := hJ j (Finset.mem_insert_self j J)
    rw [← X.ω_indep i j hjJ.1 y hjJ.2.1]
    refine ih (Function.update y j 0) (fun l hl => ?_) fun l hl => ?_
    · have hl' := hJ l (Finset.mem_insert_of_mem hl)
      have hne : l ≠ j := fun h => hj (h ▸ hl)
      rw [Function.update_of_ne hne]
      exact hl'
    · by_cases hlj : l = j
      · subst hlj
        rw [Function.update_self]
        exact hjJ.2.2.symm
      · rw [Function.update_of_ne hlj]
        exact hoff l fun h => hl ((Finset.mem_insert.1 h).resolve_left hlj)

/-- The pieces: a chart and a selected orthant. -/
abbrev PIdx : Type := Σ i : X.A.ι, ↥(X.A.signs i)

instance : Nonempty X.PIdx :=
  ⟨⟨X.ι_nonempty.some, ⟨(X.signs_nonempty X.ι_nonempty.some).choose,
    (X.signs_nonempty X.ι_nonempty.some).choose_spec⟩⟩⟩

/-! ### Boxes and orthants -/

theorem symBox_subset {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 X.a)) :
    w ∈ piBox d (Icc (-X.a) X.a) := fun j hj => by
  have := hw j hj
  rw [mem_Icc] at this ⊢
  exact ⟨by linarith [X.ha], this.2⟩

theorem refl_mem_symBox (σ : WaterFilling.CoordSign d) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc (-X.a) X.a)) : refl σ w ∈ piBox d (Icc (-X.a) X.a) := fun j hj => by
  have := hw j hj
  rw [mem_Icc] at this ⊢
  rw [refl_apply]
  unfold WaterFilling.sgn
  split_ifs <;> constructor <;> linarith

theorem mem_dom_of_mem_symBox (i : X.A.ι) (σ : WaterFilling.CoordSign d) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc (-X.a) X.a)) : refl σ w ∈ X.A.dom i := by
  rw [X.dom_eq]
  exact X.refl_mem_symBox σ hw

theorem mem_dom_of_mem_box (i : X.A.ι) (σ : WaterFilling.CoordSign d) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc 0 X.a)) : refl σ w ∈ X.A.dom i :=
  X.mem_dom_of_mem_symBox i σ (X.symBox_subset hw)

/-- The orthant box of a sign is, up to the null walls, the box intersected with the open
orthant. -/
theorem orthantBox_ae_eq (i : X.A.ι) (σ : WaterFilling.CoordSign d) :
    (orthantBox σ X.a : Set (Fin d → ℝ)) =ᵐ[volume]
      (X.A.dom i ∩ openOrthant σ : Set (Fin d → ℝ)) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun y hy => ?_) walls_null
    obtain ⟨hy1, hy2⟩ := hy
    have hdom : y ∈ X.A.dom i := by
      rw [X.dom_eq]
      exact orthantBox_subset σ X.a hy1
    have hno : y ∉ openOrthant σ := fun h => hy2 ⟨hdom, h⟩
    unfold openOrthant at hno
    rw [mem_ofPred_eq] at hno
    push Not at hno
    obtain ⟨j, hj⟩ := hno
    refine ⟨j, ?_⟩
    have h0 : 0 ≤ WaterFilling.sgn σ j * y j := ((mem_orthantBox.1 hy1) j).1
    have h1 : WaterFilling.sgn σ j * y j = 0 := le_antisymm hj h0
    exact (mul_eq_zero.1 h1).resolve_left (WaterFilling.sgn_ne_zero σ j)
  · have hsub : X.A.dom i ∩ openOrthant σ ⊆ orthantBox σ X.a := by
      intro y hy
      rw [mem_orthantBox]
      intro j
      have hpos : 0 < WaterFilling.sgn σ j * y j := hy.2 j
      refine ⟨hpos.le, ?_⟩
      have hdom := hy.1
      rw [X.dom_eq] at hdom
      have hb := hdom j (mem_univ _)
      rw [mem_Icc] at hb
      have : |WaterFilling.sgn σ j * y j| ≤ X.a := by
        rw [abs_mul, abs_sgn, one_mul]
        exact abs_le.2 hb
      exact (le_abs_self _).trans this
    rw [sdiff_eq_empty.2 hsub, measure_empty]

/-- The restriction to the selected sector is the sum of the restrictions to the selected orthant
boxes. -/
theorem restrict_sector_eq (i : X.A.ι) :
    volume.restrict (X.A.sector i) =
      ∑ σ ∈ X.A.signs i, volume.restrict (orthantBox σ X.a : Set (Fin d → ℝ)) := by
  unfold WeightedDomainAtlas.sector selectedOrthants
  rw [inter_iUnion₂]
  rw [Measure.restrict_biUnion_finset (fun σ _ τ _ hστ => (openOrthant_disjoint hστ).mono
    inter_subset_right inter_subset_right)
    (fun σ => (X.A.toPartialResolution.dom_measurable i).inter (measurableSet_openOrthant σ))]
  rw [Measure.sum_fintype,
    Finset.sum_coe_sort (X.A.signs i) fun σ => volume.restrict (X.A.dom i ∩ openOrthant σ)]
  exact Finset.sum_congr rfl fun σ _ => (Measure.restrict_congr_set (X.orthantBox_ae_eq i σ)).symm

/-- The weighted analytic prior factor on the sector is the weighted atlas sector measure of the
prior. -/
theorem withDensity_sector_eq (i : X.A.ι) :
    ((volume.restrict (X.A.sector i)).withDensity fun w =>
      ENNReal.ofReal (wgt (X.A.h i) w * X.ϕw i w)) =
      X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) i := by
  unfold WeightedDomainAtlas.sectorMeasure
  refine withDensity_congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (X.A.measurableSet_sector i)]
  refine Eventually.of_forall fun w hw => ?_
  have hV : w ∈ X.A.V i := X.A.dom_subset_V i hw.1
  rw [X.SA.jacDensity_eq i hV, ← ENNReal.ofReal_mul (X.prior_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (X.prior_nonneg _) (mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun j _ => pow_nonneg (abs_nonneg _) _)))]
  congr 1
  unfold ϕw ϕ wgt
  ring

theorem withDensity_mono_left {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SFinite μ]
    [SFinite ν] (h : μ ≤ ν) (f : α → ℝ≥0∞) : μ.withDensity f ≤ ν.withDensity f := by
  intro s
  rw [withDensity_apply', withDensity_apply']
  exact lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl

/-- The reflected piece measure is dominated by the sector measure of the prior. -/
theorem map_refl_le (p : X.PIdx) :
    (pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1).map (refl p.2.1) ≤
      X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) p.1 := by
  rw [map_refl_pieceMeasure, ← X.withDensity_sector_eq p.1]
  refine withDensity_mono_left ?_ _
  intro s
  rw [X.restrict_sector_eq, Measure.finsetSum_apply]
  exact Finset.single_le_sum (f := fun σ => volume.restrict (orthantBox σ X.a) s)
    (fun _ _ => zero_le) p.2.2

/-- The observable is integrable for the sector measure of every chart. -/
theorem integrable_sector (i : X.A.ι) :
    Integrable (X.obs ∘ X.A.φ i) (X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) i) := by
  have hm : Measurable fun w => ENNReal.ofReal (X.prior w) :=
    ENNReal.measurable_ofReal.comp X.prior_m
  have hle : (X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) i).map (X.A.φ i) ≤
      (volume.restrict X.A.W).withDensity fun w => ENNReal.ofReal (X.prior w) := by
    rw [← X.A.weightedDomainTransport hm]
    intro s
    rw [Measure.finsetSum_apply]
    exact Finset.single_le_sum
      (f := fun j => ((X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) j).map (X.A.φ j)) s)
      (fun _ _ => zero_le) (Finset.mem_univ i)
  exact (integrable_map_measure X.obs_m.aestronglyMeasurable (X.φ_m i).aemeasurable).1
    (X.obs_int.mono_measure hle)

/-- Pushforward of a finite sum of measures. -/
theorem map_finset_sum {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] {ι : Type*}
    (s : Finset ι) (μ : ι → Measure α) {f : α → γ} (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

/-- ★ **The observable is integrable on every piece**, from its integrability on the domain. -/
theorem hφint (p : X.PIdx) :
    Integrable ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) (pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1) :=
  (integrable_map_measure (X.obs_m.comp (X.φ_m p.1)).aestronglyMeasurable
    (measurable_refl _).aemeasurable).1 ((X.integrable_sector p.1).mono_measure (X.map_refl_le p))

/-! ### The collar level of a chart, with the fibre balls inside the box -/

/-- One collar level per chart: below the radii of all the selected pieces, with the width bound
`(δ/c)^{1/|A|} < a^{2k}` and the fibre-ball bound `2 (δ/c)^{1/(2k|A|)} < a`. -/
theorem exists_delta_chart' (i : X.A.ι) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ j ∈ X.act i, (δ / X.c i) ^ (((X.act i).card : ℝ)⁻¹) <
        X.a ^ (2 * X.A.k i j)) ∧
      (∀ j ∈ X.act i, 2 * (δ / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
        ((2 * X.A.k i j : ℕ) : ℝ)⁻¹) < X.a) ∧
      (∀ j ∈ X.act i, 2 * (δ / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
        ((2 * X.A.k i j : ℕ) : ℝ)⁻¹) < X.t₀) ∧
      ∀ σ ∈ X.A.signs i, ∀ (I : Idx (X.act i)) (l : Fin (nI (X.act i) I + 1)),
        2 * (δ / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
          ((2 * X.A.k i (σI (X.act i) I l).1 : ℕ) : ℝ)⁻¹) <
          (((X.P i).pullback σ).faceSeries X.a (toNonemptyIdx (X.act i) I)).ρ := by
  by_cases hA : (X.act i).Nonempty
  · have hS := X.signs_nonempty i
    set ρmin := (X.A.signs i).inf' hS fun σ => ((X.P i).pullback σ).radius X.a with hρ
    have hmin : 0 < min ρmin (min X.a X.t₀) := by
      refine lt_min ?_ (lt_min X.ha X.t₀_pos)
      rw [hρ, Finset.lt_inf'_iff]
      exact fun σ _ => ((X.P i).pullback σ).radius_pos X.a
    obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta_chart (X.act i) (X.A.k i) (X.hkA i) X.a (X.c i)
      (X.hc i) X.ha hA hmin
    refine ⟨δ, hδ, hδa,
      fun j hj => (hsm j hj).trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      fun j hj => (hsm j hj).trans_le ((min_le_right _ _).trans (min_le_right _ _)),
      fun σ hσ I l => ?_⟩
    change 2 * (δ / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
      ((2 * X.A.k i (σI (X.act i) I l).1 : ℕ) : ℝ)⁻¹) < ((X.P i).pullback σ).radius X.a
    refine ((hsm (σI (X.act i) I l).1 (amb_subset (X.act i) I (σI (X.act i) I l).2)).trans_le
      (min_le_left _ _)).trans_le ?_
    rw [hρ]
    exact Finset.inf'_le _ hσ
  · refine ⟨1, one_pos, fun j hj => absurd ⟨j, hj⟩ hA, fun j hj => absurd ⟨j, hj⟩ hA,
      fun j hj => absurd ⟨j, hj⟩ hA,
      fun _ _ I _ => absurd ((amb_nonempty (X.act i) I).mono (amb_subset (X.act i) I)) hA⟩

/-- The collar level of chart `i`. -/
noncomputable def δ (i : X.A.ι) : ℝ := (X.exists_delta_chart' i).choose

theorem δ_pos (i : X.A.ι) : 0 < X.δ i := (X.exists_delta_chart' i).choose_spec.1

theorem δ_lt (i : X.A.ι) : ∀ j ∈ X.act i, (X.δ i / X.c i) ^ (((X.act i).card : ℝ)⁻¹) <
    X.a ^ (2 * X.A.k i j) :=
  (X.exists_delta_chart' i).choose_spec.2.1

theorem δ_ball (i : X.A.ι) : ∀ j ∈ X.act i, 2 * (X.δ i / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
    ((2 * X.A.k i j : ℕ) : ℝ)⁻¹) < X.a :=
  (X.exists_delta_chart' i).choose_spec.2.2.1

theorem δ_t₀ (i : X.A.ι) : ∀ j ∈ X.act i, 2 * (X.δ i / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
    ((2 * X.A.k i j : ℕ) : ℝ)⁻¹) < X.t₀ :=
  (X.exists_delta_chart' i).choose_spec.2.2.2.1

theorem δ_t₀' (i : X.A.ι) (I : Idx (X.act i)) : ∀ l : Fin (nI (X.act i) I + 1),
    2 * (X.δ i / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
      ((2 * X.A.k i (σI (X.act i) I l).1 : ℕ) : ℝ)⁻¹) < X.t₀ :=
  fun l => X.δ_t₀ i _ (amb_subset (X.act i) I (σI (X.act i) I l).2)

theorem δ_ball' (i : X.A.ι) (I : Idx (X.act i)) : ∀ l : Fin (nI (X.act i) I + 1),
    2 * (X.δ i / X.c i) ^ (((X.act i).card : ℝ)⁻¹ *
      ((2 * X.A.k i (σI (X.act i) I l).1 : ℕ) : ℝ)⁻¹) < X.a :=
  fun l => X.δ_ball i _ (amb_subset (X.act i) I (σI (X.act i) I l).2)

theorem δ_small (p : X.PIdx) : ∀ (I : Idx (X.act p.1)) (l : Fin (nI (X.act p.1) I + 1)),
    2 * (X.δ p.1 / X.c p.1) ^ (((X.act p.1).card : ℝ)⁻¹ *
      ((2 * X.A.k p.1 (σI (X.act p.1) I l).1 : ℕ) : ℝ)⁻¹) <
      (((X.P p.1).pullback p.2.1).faceSeries X.a (toNonemptyIdx (X.act p.1) I)).ρ :=
  (X.exists_delta_chart' p.1).choose_spec.2.2.2.2 p.2.1 p.2.2

theorem ae_mem_box' (p : X.PIdx) :
    ∀ᵐ z ∂pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1, z ∈ piBox d (Icc 0 X.a) := by
  unfold pieceMeasure
  exact mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
    (mem_ae_iff.1 (ae_restrict_mem (measurableSet_W X.a))))

/-! ### The piece certificates -/

/-- The reflected unit of a piece. -/
noncomputable abbrev uP (p : X.PIdx) : (Fin d → ℝ) → ℝ := unitR (X.A.phaseUnit p.1) p.2.1

/-- The face series of a piece for the UNWEIGHTED prior factor, from the pulled-back packet. -/
noncomputable def F₀ (p : X.PIdx) (I : Idx (X.act p.1)) :
    FaceSeries (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (X.ϕ p.1 ∘ refl p.2.1) ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) I :=
  toChartFaceSeries (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a
    (X.δ p.1) (X.δ_pos p.1) (continuous_unitR (X.hu_cont p.1) p.2.1) (X.c p.1) (X.hc p.1)
    (unitR_lb (X.hu_lb p.1) p.2.1) X.ha
    (((X.P p.1).pullback p.2.1).faceSeries X.a (toNonemptyIdx (X.act p.1) I)) (X.δ_small p I)

/-- The base weight of a piece core: the chart weight at the (reflected) base point. -/
noncomputable def gw (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) : ℝ :=
  X.A.ω p.1 (refl p.2.1 s.1.1)

theorem continuous_gw (p : X.PIdx) (I : Idx (X.act p.1)) : Continuous (X.gw p I) := by
  refine (X.ω_contOn p.1).comp_continuous ((continuous_refl _).comp
    (continuous_subtype_val.comp continuous_subtype_val)) fun s => ?_
  obtain ⟨j, hj⟩ := amb_nonempty (X.act p.1) I
  refine ⟨j, X.hkA p.1 j (amb_subset (X.act p.1) I hj), ?_⟩
  rw [refl_apply, stratum_coord_zero (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) s.1 hj,
    mul_zero, abs_zero]
  exact X.t₀_pos.le

theorem abs_gw_le (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    |X.gw p I s| ≤ 1 := by
  change |X.A.ω p.1 (refl p.2.1 s.1.1)| ≤ 1
  rw [abs_of_nonneg (X.A.ω_nonneg _ _)]
  exact X.A.ω_le_one _ _

/-- **The weight is constant on the core**: at the core parametrisation the chart weight is the
base weight (the normal coordinates stay within `t₀`). -/
theorem ω_Φ_eq (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I)
    (v : Fin (nI (X.act p.1) I + 1) → ℝ)
    (hv : v ∈ NormalisedBox.box (ι := Fin (nI (X.act p.1) I + 1))
      (side (X.A.k p.1) (amb (X.act p.1) I) (X.δ p.1))) :
    X.A.ω p.1 (refl p.2.1 (Φ (amb (X.act p.1) I) (σI (X.act p.1) I)
      (eI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I)
      (lamT (X.A.k p.1) (X.uP p) (amb (X.act p.1) I) (X.δ p.1)) (s, v))) = X.gw p I s := by
  have hside := side_pos (X.A.k p.1) (amb (X.act p.1) I) (X.δ p.1) (X.δ_pos p.1)
  have hvn : ‖v‖ < 2 * side (X.A.k p.1) (amb (X.act p.1) I) (X.δ p.1) := by
    refine lt_of_le_of_lt (pi_norm_le_iff_of_nonneg hside.le |>.2 fun l => ?_) (by linarith)
    have := hv l (mem_univ _)
    rw [mem_Ioc] at this
    rw [Real.norm_eq_abs, abs_of_pos this.1]
    exact this.2
  have hz := norm_widthsC_mul_lt (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1)
    (X.uP p) X.a (X.δ p.1) (X.δ_pos p.1) (X.c p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha
    I X.t₀_pos (X.δ_t₀' p.1 I) s hvn
  rw [Φ_eq_originalNormalMapC (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a
    (X.δ p.1) I s v]
  refine X.ω_eq_of_agree p.1 (amb (X.act p.1) I) _ _ (fun j hj => ⟨?_, ?_, ?_⟩) fun j hj => ?_
  · exact X.hkA p.1 j (amb_subset (X.act p.1) I hj)
  · have hj' : j ∈ (toNonemptyIdx (X.act p.1) I).1 := hj
    simp only [refl_apply, originalNormalMap, abs_mul, abs_sgn, one_mul]
    rw [dif_pos hj', stratum_coord_zero (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) s.1 hj,
      zero_add]
    have := (pi_norm_lt_iff X.t₀_pos).1 hz ((σI (X.act p.1) I).symm ⟨j, hj⟩)
    rw [Real.norm_eq_abs] at this
    exact this.le
  · rw [refl_apply, stratum_coord_zero (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) s.1 hj,
      mul_zero]
  · have hj' : j ∉ (toNonemptyIdx (X.act p.1) I).1 := hj
    simp only [refl_apply, originalNormalMap]
    rw [dif_neg hj']

/-- The face series of a piece for the WEIGHTED prior factor: the unweighted series multiplied
by the base weight. -/
noncomputable def F (p : X.PIdx) (I : Idx (X.act p.1)) :
    FaceSeries (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (X.ϕw p.1 ∘ refl p.2.1) ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) I where
  Fϕ := (X.F₀ p I).Fϕ.smul (X.gw p I) (X.continuous_gw p I) 1 (X.abs_gw_le p I)
  Fφ := (X.F₀ p I).Fφ
  hϕ_eq := fun s v hv => by
    change X.A.ω p.1 (refl p.2.1 _) * (X.ϕ p.1 ∘ refl p.2.1) _ = _
    rw [X.ω_Φ_eq p I s v hv, (X.F₀ p I).hϕ_eq s v hv]
    exact (CoeffFamily.evalF_const_mul _ _ _).symm
  hφ_eq := (X.F₀ p I).hφ_eq

/-- ★★ **The chart-box certificate of a weighted piece** (CCCLXXII), at the chart's collar
level, with the weighted prior factor. -/
noncomputable def pieceCertP (p : X.PIdx) (hA : (X.act p.1).Nonempty) :=
  certificate (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a (X.δ p.1)
    (X.δ_pos p.1) (continuous_unitR (X.hu_cont p.1) p.2.1) (X.ϕw p.1 ∘ refl p.2.1)
    ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) (unitR_tan (X.hu_tan' p.1) p.2.1) (X.hc p.1)
    (unitR_lb (X.hu_lb p.1) p.2.1) X.ha (X.δ_lt p.1) ((X.ϕw_m p.1).comp (measurable_refl _))
    (fun _ => X.ϕw_nonneg p.1 _) (X.hφint p) (X.F p) hA

/-- The coefficient certificate of a weighted piece. -/
noncomputable def pieceCoeffP (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    (X.pieceCertP p hA).CoefficientCertificate :=
  coeffCertificate (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a
    (X.δ p.1) (X.δ_pos p.1) (continuous_unitR (X.hu_cont p.1) p.2.1) (X.ϕw p.1 ∘ refl p.2.1)
    ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) (unitR_tan (X.hu_tan' p.1) p.2.1) (X.hc p.1)
    (unitR_lb (X.hu_lb p.1) p.2.1) X.ha (X.δ_lt p.1) ((X.ϕw_m p.1).comp (measurable_refl _))
    (fun _ => X.ϕw_nonneg p.1 _) (X.hφint p) (X.F p) hA

theorem pieceCertP_L_μ (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    (X.pieceCertP p hA).L.μ = pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1 := rfl

theorem pieceCertP_L_phase (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    (X.pieceCertP p hA).L.phase = ChartModel.phase d (X.act p.1) (X.A.k p.1) (X.uP p) := rfl

theorem pieceCertP_L_obs (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    (X.pieceCertP p hA).L.obs = (X.obs ∘ X.A.φ p.1) ∘ refl p.2.1 := rfl

theorem pieceCertP_β (p : X.PIdx) (hA : (X.act p.1).Nonempty) : (X.pieceCertP p hA).β = 1 := rfl

theorem ae_mem_box (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    ∀ᵐ z ∂(X.pieceCertP p hA).L.μ, z ∈ piBox d (Icc 0 X.a) := by
  rw [pieceCertP_L_μ]
  exact X.ae_mem_box' p

instance instCompactKI (p : X.PIdx) (I : Idx (X.act p.1)) :
    CompactSpace (KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :=
  compactSpace_KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
    (X.δ_pos p.1) (continuous_unitR (X.hu_cont p.1) p.2.1) I

/-- The core parametrisation of every stratum of a piece lands in the box, a.e. on the chart
measure. -/
theorem chart_Φ_mem (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1))) :
    ∀ᵐ q ∂chartMeasure ((X.pieceCertP p hA).cores.chart I).ν ((X.pieceCertP p hA).n I)
      ((X.pieceCertP p hA).cores.chart I).b,
      ((X.pieceCertP p hA).cores.chart I).Φ q ∈ piBox d (Icc 0 X.a) :=
  stratumCore_Φ_mem_box (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a
    (X.δ p.1) (X.δ_pos p.1) (continuous_unitR (X.hu_cont p.1) p.2.1) (X.ϕw p.1 ∘ refl p.2.1)
    ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) (unitR_tan (X.hu_tan' p.1) p.2.1) (X.c p.1) (X.hc p.1) X.ha
    ((X.ϕw_m p.1).comp (measurable_refl _)) (fun _ => X.ϕw_nonneg p.1 _)
    (unitR_lb (X.hu_lb p.1) p.2.1) (X.δ_lt p.1) (X.hφint p) (X.F p) (coreIdx (X.act p.1) I)

/-! ### The piece charts into the sheet space and the compatibilities -/

/-- The piece chart `z ↦ incl_i (R_σ z)` into the sheet space. -/
noncomputable def Ψ (p : X.PIdx) (z : Fin d → ℝ) : Sheet.Space X.SA :=
  Sheet.incl X.SA p.1 (refl p.2.1 z)

theorem measurable_Ψ (p : X.PIdx) : Measurable (X.Ψ p) :=
  (Sheet.measurable_incl X.SA p.1).comp (measurable_refl _)

theorem π_Ψ (p : X.PIdx) {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc (-X.a) X.a)) :
    Sheet.π X.SA (X.Ψ p z) = X.A.φ p.1 (refl p.2.1 z) :=
  Sheet.π_incl X.SA p.1 (X.mem_dom_of_mem_symBox p.1 p.2.1 hz)

theorem measurable_Kπ : Measurable (X.K ∘ Sheet.π X.SA) :=
  X.K_m.comp (Sheet.continuous_π X.SA).measurable

/-- **Phase compatibility on the box**: `K ∘ π ∘ Ψ_p` is the piece's chart phase. -/
theorem phase_compat (p : X.PIdx) {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc 0 X.a)) :
    X.K (Sheet.π X.SA (X.Ψ p z)) = ChartModel.phase d (X.act p.1) (X.A.k p.1) (X.uP p) z := by
  have hd := X.mem_dom_of_mem_box p.1 p.2.1 hz
  rw [X.π_Ψ p (X.symBox_subset hz), X.A.phase_eq p.1 _ (X.A.dom_subset_V p.1 hd),
    ← chartPhase_refl]
  unfold ChartModel.phase
  congr 1
  exact coordPhase_eq_monoPhase (X.act p.1) (X.A.k p.1) (X.hk0 p.1) (refl p.2.1 z)

/-- **Observable compatibility on the symmetric box**. -/
theorem obs_compat (p : X.PIdx) {z : Fin d → ℝ} (hz : z ∈ piBox d (Icc (-X.a) X.a)) :
    X.obs (Sheet.π X.SA (X.Ψ p z)) = ((X.obs ∘ X.A.φ p.1) ∘ refl p.2.1) z := by
  rw [X.π_Ψ p hz]
  rfl

/-- **The transported piece datum** on the sheet space: measure `μ_p.map Ψ_p`, phase `K ∘ π`,
observable `obs ∘ π`, level `1` (defined for every piece, active or not). -/
noncomputable def pieceDatum (p : X.PIdx) : LocalisationData (Sheet.Space X.SA) where
  μ := (pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1).map (X.Ψ p)
  phase := X.K ∘ Sheet.π X.SA
  obs := X.obs ∘ Sheet.π X.SA
  phase_measurable := X.measurable_Kπ
  phase_nonneg := by
    rw [ae_map_iff (X.measurable_Ψ p).aemeasurable
      (measurableSet_le measurable_const X.measurable_Kπ)]
    refine (X.ae_mem_box' p).mono fun z hz => ?_
    change 0 ≤ X.K (Sheet.π X.SA (X.Ψ p z))
    rw [X.π_Ψ p (X.symBox_subset hz)]
    exact X.SA.phase_nonneg p.1 (X.A.dom_subset_V p.1 (X.mem_dom_of_mem_box p.1 p.2.1 hz))
  obs_integrable :=
    (integrable_map_measure (X.obs_m.comp (Sheet.continuous_π X.SA).measurable).aestronglyMeasurable
      (X.measurable_Ψ p).aemeasurable).2 ((X.hφint p).congr
        ((X.ae_mem_box' p).mono fun z hz => (X.obs_compat p (X.symBox_subset hz)).symm))
  δ := 1
  δ_pos := one_pos

theorem pieceDatum_μ (p : X.PIdx) :
    (X.pieceDatum p).μ = (pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1).map (X.Ψ p) := rfl

theorem pieceDatum_phase (p : X.PIdx) : (X.pieceDatum p).phase = X.K ∘ Sheet.π X.SA := rfl

theorem pieceDatum_obs (p : X.PIdx) : (X.pieceDatum p).obs = X.obs ∘ Sheet.π X.SA := rfl

theorem chart_hp (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1))) :
    ∀ᵐ q ∂chartMeasure ((X.pieceCertP p hA).cores.chart I).ν ((X.pieceCertP p hA).n I)
      ((X.pieceCertP p hA).cores.chart I).b,
      (X.K ∘ Sheet.π X.SA) (X.Ψ p (((X.pieceCertP p hA).cores.chart I).Φ q)) =
        (X.pieceCertP p hA).L.phase (((X.pieceCertP p hA).cores.chart I).Φ q) :=
  (X.chart_Φ_mem p hA I).mono fun _ hq => X.phase_compat p hq

theorem chart_ho (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1))) :
    ∀ᵐ q ∂chartMeasure ((X.pieceCertP p hA).cores.chart I).ν ((X.pieceCertP p hA).n I)
      ((X.pieceCertP p hA).cores.chart I).b,
      (X.obs ∘ Sheet.π X.SA) (X.Ψ p (((X.pieceCertP p hA).cores.chart I).Φ q)) =
        (X.pieceCertP p hA).L.obs (((X.pieceCertP p hA).cores.chart I).Φ q) :=
  (X.chart_Φ_mem p hA I).mono fun _ hq => X.obs_compat p (X.symBox_subset hq)

theorem htail (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    ∀ᵐ z ∂(X.pieceCertP p hA).cores.tail,
      (X.K ∘ Sheet.π X.SA) (X.Ψ p z) = (X.pieceCertP p hA).L.phase z :=
  Filter.le_def.1 (Measure.absolutelyContinuous_of_le (X.pieceCertP p hA).cores.tail_le).ae_le _
    ((X.ae_mem_box p hA).mono fun _ hz => X.phase_compat p hz)

/-- The transported core decomposition of a piece (bases still the chart strata). -/
noncomputable def pieceCores (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    AnalyticCoreDecomposition (X.pieceDatum p) (numCores (X.act p.1))
      (fun I => KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
        (coreIdx (X.act p.1) I))
      (fun I => nI (X.act p.1) (coreIdx (X.act p.1) I)) 1 :=
  (X.pieceCertP p hA).cores.mapAmbient_ae (X.Ψ p) (X.measurable_Ψ p) (X.pieceDatum p) rfl
    (X.chart_hp p hA) (X.htail p hA) (X.chart_ho p hA)

/-! ### The bases on the sheet strata -/

/-- An active coordinate of chart `i` as a divisor component of the sheet geometry. -/
def toComp (i : X.A.ι) (j : ↥(X.act i)) : Sheet.Component X.SA := ⟨(i, j.1), X.hkA i j.1 j.2⟩

/-- The sheet stratum of a chart stratum. -/
noncomputable def J (p : X.PIdx) (I : Idx (X.act p.1)) : Finset (Sheet.Component X.SA) :=
  I.1.image (X.toComp p.1)

theorem amb_J (p : X.PIdx) (I : Idx (X.act p.1)) :
    Sheet.amb X.SA (X.J p I) = amb (X.act p.1) I := by
  unfold Sheet.amb J ChartCollar.amb ChartModel.amb
  rw [Finset.image_image, Finset.map_eq_image]
  rfl

theorem base_mem_box (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    s.1.1 ∈ piBox d (Icc 0 X.a) := by
  intro j _
  by_cases hj : j ∈ amb (X.act p.1) I
  · rw [stratum_coord_zero (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) s.1 hj]
    exact ⟨le_rfl, X.ha.le⟩
  · have := s.2 ⟨j, hj⟩
    exact ⟨this.1, this.2.1⟩

theorem bmap_mem (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    ∀ c : Sheet.Component X.SA, X.Ψ p s.1.1 ∈ Sheet.E X.SA c ↔ c ∈ X.J p I := by
  intro c
  have hd := X.mem_dom_of_mem_box p.1 p.2.1 (X.base_mem_box p I s)
  change (X.Ψ p s.1.1).1 = c.1.1 ∧ ((X.Ψ p s.1.1).2 : Fin d → ℝ) c.1.2 = 0 ↔ c ∈ X.J p I
  have hcl : ((X.Ψ p s.1.1).2 : Fin d → ℝ) = refl p.2.1 s.1.1 :=
    Sheet.clamp_of_mem X.SA p.1 hd
  rw [hcl]
  change p.1 = c.1.1 ∧ WaterFilling.sgn p.2.1 c.1.2 * s.1.1 c.1.2 = 0 ↔ _
  rw [mul_eq_zero, or_iff_right (WaterFilling.sgn_ne_zero _ _), J, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : c.1.2 ∈ X.act p.1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [h1]; exact c.2⟩
    refine ⟨⟨c.1.2, hc⟩, ?_, Subtype.ext (Prod.ext h1 rfl)⟩
    exact ((ChartModel.mem_stratumSet_iff d (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) I.1
      s.1.1).1 s.1.2 ⟨c.1.2, hc⟩).1 h2
  · rintro ⟨j, hj, rfl⟩
    exact ⟨rfl, ((ChartModel.mem_stratumSet_iff d (X.act p.1) (X.A.k p.1) (X.A.h p.1)
      (X.hkA p.1) I.1 s.1.1).1 s.1.2 j).2 hj⟩

/-- The base map of a piece stratum into the sheet stratum. -/
noncomputable def bmap (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    (Sheet.geometry X.SA).Stratum (X.J p I) :=
  ⟨X.Ψ p s.1.1, fun c => X.bmap_mem p I s c⟩

theorem bmap_val (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    (X.bmap p I s : Sheet.Space X.SA) = X.Ψ p s.1.1 := rfl

theorem continuous_bmap (p : X.PIdx) (I : Idx (X.act p.1)) : Continuous (X.bmap p I) :=
  Continuous.subtype_mk ((Sheet.continuous_incl X.SA p.1).comp ((continuous_refl _).comp
    (continuous_subtype_val.comp continuous_subtype_val))) _

theorem bmap_injective (p : X.PIdx) (I : Idx (X.act p.1)) : Function.Injective (X.bmap p I) := by
  intro s s' h
  have h1 : X.Ψ p s.1.1 = X.Ψ p s'.1.1 := congrArg Subtype.val h
  unfold Ψ Sheet.incl at h1
  have h2 := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.1 h1).2)
  change Sheet.clamp X.SA p.1 (refl p.2.1 s.1.1) = Sheet.clamp X.SA p.1 (refl p.2.1 s'.1.1) at h2
  rw [Sheet.clamp_of_mem X.SA p.1 (X.mem_dom_of_mem_box p.1 p.2.1 (X.base_mem_box p I s)),
    Sheet.clamp_of_mem X.SA p.1 (X.mem_dom_of_mem_box p.1 p.2.1 (X.base_mem_box p I s'))] at h2
  have h3 : s.1.1 = s'.1.1 := by rw [← refl_refl p.2.1 s.1.1, h2, refl_refl]
  exact Subtype.ext (Subtype.ext h3)

/-- The base of a piece stratum on the sheet: the image of the chart base. -/
noncomputable def baseSetS (p : X.PIdx) (I : Idx (X.act p.1)) :
    Set ((Sheet.geometry X.SA).Stratum (X.J p I)) := range (X.bmap p I)

theorem isCompact_baseSetS (p : X.PIdx) (I : Idx (X.act p.1)) : IsCompact (X.baseSetS p I) :=
  isCompact_range (X.continuous_bmap p I)

/-- The chart base is homeomorphic to its image on the sheet stratum. -/
noncomputable def baseHomeo (p : X.PIdx) (I : Idx (X.act p.1)) :
    KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I ≃ₜ
      ↥(X.baseSetS p I) :=
  ((X.continuous_bmap p I).isClosedEmbedding (X.bmap_injective p I)).isEmbedding.toHomeomorph

theorem baseHomeo_apply_coe (p : X.PIdx) (I : Idx (X.act p.1))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) I) :
    ((X.baseHomeo p I s : ↥(X.baseSetS p I)) : (Sheet.geometry X.SA).Stratum (X.J p I)) =
      X.bmap p I s := rfl

theorem baseHomeo_symm_spec (p : X.PIdx) (I : Idx (X.act p.1)) (s : ↥(X.baseSetS p I)) :
    X.bmap p I ((X.baseHomeo p I).symm s) = s.1 := by
  have := X.baseHomeo_apply_coe p I ((X.baseHomeo p I).symm s)
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

/-- The transported core decomposition of a piece, based on the sheet strata. -/
noncomputable def pieceCores' (p : X.PIdx) (hA : (X.act p.1).Nonempty) :
    AnalyticCoreDecomposition (X.pieceDatum p) (numCores (X.act p.1))
      (fun I => ↥(X.baseSetS p (coreIdx (X.act p.1) I)))
      (fun I => nI (X.act p.1) (coreIdx (X.act p.1) I)) 1 :=
  (X.pieceCores p hA).reindexAll fun I => X.baseHomeo p (coreIdx (X.act p.1) I)

theorem pieceCores'_chart_Φ (p : X.PIdx) (hA : (X.act p.1).Nonempty)
    (I : Fin (numCores (X.act p.1)))
    (q : ↥(X.baseSetS p (coreIdx (X.act p.1) I)) ×
      (Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)) :
    ((X.pieceCores' p hA).chart I).Φ q =
      X.Ψ p (((X.pieceCertP p hA).cores.chart I).Φ
        ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm q.1, q.2)) := rfl

end SheetInputs

end SheetAssembly

end Grammar
