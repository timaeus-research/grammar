/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.OneChartProductExample
import Grammar.PosteriorTransfer

/-!
# Localisation by a supplied partition of unity (CCLXIV)

The resolved Boltzmann integral of a cover decomposes along any **supplied** partition of unity
`ψ_i` subordinate (relatively to the union `U = ⋃ φ_i(dom_i)`) to the chart images:

`Z_N[F] = ∑_i Z^{(i)}_N[F; p ψ_i]`,

where `Z^{(i)}` is the Boltzmann integral of the one-chart cover of chart `i` with prior `p ψ_i`.
The core identity (`boltzmannIntegral_eq_sum_partition`) needs only the **masked** partition
identity `∑_i 1_{A_i} ψ_i = 1` on `U`; the user-facing wrapper (`SubordinatePartition.ofPartition`)
takes an ordinary partition `∑_i ψ_i = 1` on `U` together with relative subordination
(`ψ_i = 0` on `U ∖ A_i`). The counting weights of the cover are an instance
(`SubordinatePartition.counting`). No regularity is needed for the decomposition; the analytic
theorems downstream take the pullbacks `ψ_i ∘ φ_i` as continuous factors of the prior.

This is the localisation step of consult #83 (R3): it removes the restriction that the cover weight
factors through the inactive coordinates, since a one-chart cover has counting weight `1`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- **A supplied partition of unity, masked to the chart images**: bounded nonnegative measurable
weights with `∑_i 1_{A_i} ψ_i = 1` on the union of the chart images. -/
structure SubordinatePartition {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι) where
  /-- The weights. -/
  ψ : ι → (Fin d → ℝ) → ℝ
  meas : ∀ i, Measurable (ψ i)
  nonneg : ∀ i x, 0 ≤ ψ i x
  /-- A uniform bound. -/
  bound : ℝ
  le_bound : ∀ i x, ψ i x ≤ bound
  /-- The masked partition identity on the union of the chart images. -/
  masked_sum : ∀ x ∈ ⋃ i, R.image i, ∑ i, (R.image i).indicator (ψ i) x = 1

namespace SubordinatePartition

variable {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι} (P : SubordinatePartition R)

theorem bound_nonneg (i : ι) : 0 ≤ P.bound := (P.nonneg i 0).trans (P.le_bound i 0)

theorem norm_indicator_le (i : ι) (x : Fin d → ℝ) :
    ‖(R.image i).indicator (P.ψ i) x‖ ≤ P.bound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun x _ => P.nonneg i x) x)]
  by_cases hx : x ∈ R.image i
  · rw [Set.indicator_of_mem hx]
    exact P.le_bound i x
  · rw [Set.indicator_of_notMem hx]
    exact P.bound_nonneg i

/-- **An ordinary partition of unity, relatively subordinate to the chart images**, as a masked
one: `∑_i ψ_i = 1` on `U` and `ψ_i = 0` on `U ∖ A_i`. -/
def ofPartition (ψ : ι → (Fin d → ℝ) → ℝ) (meas : ∀ i, Measurable (ψ i))
    (nonneg : ∀ i x, 0 ≤ ψ i x) (bound : ℝ) (le_bound : ∀ i x, ψ i x ≤ bound)
    (sum_eq : ∀ x ∈ ⋃ i, R.image i, ∑ i, ψ i x = 1)
    (subord : ∀ i, ∀ x ∈ ⋃ i, R.image i, x ∉ R.image i → ψ i x = 0) :
    SubordinatePartition R where
  ψ := ψ
  meas := meas
  nonneg := nonneg
  bound := bound
  le_bound := le_bound
  masked_sum := fun x hx => by
    rw [← sum_eq x hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hxi : x ∈ R.image i
    · exact Set.indicator_of_mem hxi _
    · rw [Set.indicator_of_notMem hxi, subord i x hx hxi]

/-- **The counting weights of the cover** form a subordinate partition. -/
noncomputable def counting (R : ResolutionCover d ι) : SubordinatePartition R where
  ψ := R.weight
  meas := R.measurable_weight
  nonneg := fun i x => coverWeight_nonneg R.image i x
  bound := 1
  le_bound := fun i x => coverWeight_le_one R.image i x
  masked_sum := fun x hx => by
    rw [← sum_coverWeight hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hxi : x ∈ R.image i
    · exact Set.indicator_of_mem hxi _
    · rw [Set.indicator_of_notMem hxi, coverWeight_eq_zero_of_notMem hxi]

end SubordinatePartition

/-! ### The prior multiplied by a partition member -/

/-- The prior `p ψ_i`. -/
def TubeWeight.mulPartition {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι}
    (p : TubeWeight d) (P : SubordinatePartition R) (i : ι) : TubeWeight d where
  w := fun x => p.w x * P.ψ i x
  measurable := p.measurable.mul (P.meas i)
  nonneg := fun x => mul_nonneg (p.nonneg x) (P.nonneg i x)
  bound := p.bound * P.bound
  le_bound := fun x => mul_le_mul (p.le_bound x) (P.le_bound i x) (P.nonneg i x)
    ((p.nonneg 0).trans (p.le_bound 0))

theorem TubeWeight.mulPartition_w {d : ℕ} {ι : Type*} [Fintype ι] {R : ResolutionCover d ι}
    (p : TubeWeight d) (P : SubordinatePartition R) (i : ι) (x : Fin d → ℝ) :
    (p.mulPartition P i).w x = p.w x * P.ψ i x := rfl

namespace ResolutionCover

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The Boltzmann integral of a one-chart cover is the integral over the chart image. -/
theorem ofChart_boltzmannIntegral (C : ResolutionChart d) (F K : (Fin d → ℝ) → ℝ)
    (p : TubeWeight d) (N : ℝ) :
    (ofChart C).boltzmannIntegral F K p N =
      ∫ x in C.φ '' C.dom, F x * p.w x * Real.exp (-N * K x) := by
  rw [boltzmannIntegral_eq, ofChart_iUnion_image]

variable (P : SubordinatePartition R) {F K : (Fin d → ℝ) → ℝ} {p : TubeWeight d}

/-- The observable against the prior `p ψ_i` is integrable on the image of chart `i`. -/
theorem integrable_mulPartition (i : ι)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i))) :
    Integrable (fun x => F x * (p.mulPartition P i).w x)
      (volume.restrict (⋃ j, (ofChart (R.chart i)).image j)) := by
  rw [ofChart_iUnion_image]
  have hsub : (R.chart i).φ '' (R.chart i).dom ⊆ ⋃ i, R.image i := subset_iUnion R.image i
  have h := (hF.mono_measure (Measure.restrict_mono hsub le_rfl)).bdd_mul (c := P.bound)
    (f := P.ψ i) (P.meas i).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg i x)]
      exact P.le_bound i x)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [TubeWeight.mulPartition_w]
  ring

/-- **Localisation by a supplied partition of unity**: the resolved Boltzmann integral is the sum
over the charts of the one-chart Boltzmann integrals with priors `p ψ_i`. -/
theorem boltzmannIntegral_eq_sum_partition (hF : Integrable (fun x => F x * p.w x)
    (volume.restrict (⋃ i, R.image i))) (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x) {N : ℝ}
    (hN : 0 ≤ N) :
    R.boltzmannIntegral F K p N =
      ∑ i, (ofChart (R.chart i)).boltzmannIntegral F K (p.mulPartition P i) N := by
  have hU : MeasurableSet (⋃ i, R.image i) := MeasurableSet.iUnion R.measurableSet_image
  have hg := R.integrable_boltzmann hF hK hK0 hN
  have hint : ∀ i, Integrable (fun x => (R.image i).indicator (P.ψ i) x *
      (F x * p.w x * Real.exp (-N * K x))) (volume.restrict (⋃ i, R.image i)) := fun i =>
    hg.bdd_mul (c := P.bound) ((P.meas i).indicator (R.measurableSet_image i)).aestronglyMeasurable
      (Eventually.of_forall fun x => P.norm_indicator_le i x)
  rw [boltzmannIntegral_eq]
  have hsplit : ∫ x in ⋃ i, R.image i, F x * p.w x * Real.exp (-N * K x) =
      ∫ x in ⋃ i, R.image i, ∑ i, (R.image i).indicator (P.ψ i) x *
        (F x * p.w x * Real.exp (-N * K x)) := by
    refine setIntegral_congr_fun hU fun x hx => ?_
    rw [← Finset.sum_mul, P.masked_sum x hx, one_mul]
  rw [hsplit, integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofChart_boltzmannIntegral (R.chart i)]
  have hind : ∀ x, (R.image i).indicator (P.ψ i) x * (F x * p.w x * Real.exp (-N * K x)) =
      (R.image i).indicator (fun x => F x * (p.w x * P.ψ i x) * Real.exp (-N * K x)) x := by
    intro x
    by_cases hx : x ∈ R.image i
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [hind]
  rw [setIntegral_indicator (R.measurableSet_image i),
    Set.inter_eq_right.2 (subset_iUnion R.image i)]
  rfl

end ResolutionCover

end Grammar
