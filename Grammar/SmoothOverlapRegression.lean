/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothSheetProducer
import Grammar.SheetOverlapRegression

/-!
# Regression: overlapping shifted boxes with a smooth ACTIVE-dependent ramp (consult #117 §8)

The definitive regression for the smooth weighted-atlas producer. The phase `y_{i₀}²` on the union
`Ω` of the box `[−a,a]^n` and its translate by `0 < s < 2a` along an inactive coordinate
`i₁ ≠ i₀` is covered by the identity chart and the translation chart on the common box
(`hironaka`'s `shiftedAtlasOf`), whose images overlap in a set of positive measure
(`SheetAssembly.overlap_volume_pos`). The weights are `τ ∘ φ₁`, `(1 − τ) ∘ φ₂` for an admissible
SMOOTH partition function `τ` (`SmoothRamp`: `C^∞`, `0 ≤ τ ≤ 1`, `τ = 1` on the part covered only
by the box, `τ = 0` on the part covered only by the translate).

1. The weights are smooth and subordinate (`SmoothRamp.partWeight_subordinate`,
   `smoothOverlapInputs.ω_smooth`).
2. The weighted change-of-variables identity holds for the atlas
   (`smoothOverlap_weightedDomainTransport`).
3. ★ The ramp `activeRamp` — `τ(x) = 1 − σ(2 r(x_{i₁}) − 1 + σ(x_{i₀}²))`, `σ` Mathlib's
   `Real.smoothTransition`, `r` the affine coordinate of the overlap — depends NONTRIVIALLY on the
   active coordinate `x_{i₀}`: for every `t₀ > 0` the analytic producer's hypothesis `ω_indep`
   (`SheetInputs.ω_indep`) FAILS (`activeRamp_not_tangential`, `activeRamp_not_ω_indep`).
4. ★★★ The smooth producer nevertheless yields the coordinate-free expansion of
   `∫_Ω Q · P · e^{−N y_{i₀}²}` for smooth `P ≥ 0`, `Q`
   (`smoothOverlap_hasSmoothCoordFreeExpansion`, instantiated at the active ramp in
   `activeOverlap_hasSmoothCoordFreeExpansion`).
5. ★★ Changing the ramp leaves the scalar coefficients unchanged, by presentation independence
   (`coeff_eq_of_ramp`; in particular the active ramp and the purely tangential smooth ramp
   `tangentialRamp` agree, `coeff_active_eq_coeff_tangential`).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {n : ℕ}

/-! ### Admissible smooth partition functions on the union -/

/-- A smooth partition function on the union of the box `[−a,a]^n` and its translate by `s` along
`i₁`: `C^∞`, valued in `[0,1]`, `1` on the part covered only by the box and `0` on the part covered
only by the translate. -/
structure SmoothRamp (i₁ : Fin n) (a s : ℝ) where
  /-- the partition function -/
  τ : (Fin n → ℝ) → ℝ
  smooth : ContDiff ℝ ∞ τ
  nonneg : ∀ x, 0 ≤ τ x
  le_one : ∀ x, τ x ≤ 1
  eq_one : ∀ x, x ∈ centeredBox n a → x ∉ shift i₁ s '' centeredBox n a → τ x = 1
  eq_zero : ∀ x, x ∈ shift i₁ s '' centeredBox n a → x ∉ centeredBox n a → τ x = 0

namespace SmoothRamp

variable {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {a : ℝ} (ha : 0 < a) {s : ℝ} (ρ : SmoothRamp i₁ a s)

/-- The overlapping weighted domain atlas with the weights of the smooth ramp. -/
noncomputable def atlas : WeightedDomainAtlas n (monoPhase (Pi.single i₀ 1)) (shiftedSet i₁ a s) :=
  shiftedAtlasOf i₀ i₁ hne ha s ρ.τ ρ.smooth.continuous.measurable ρ.nonneg ρ.le_one ρ.eq_one
    ρ.eq_zero

theorem atlas_ω (b : Bool) (y : Fin n → ℝ) :
    (ρ.atlas hne ha).ω b y = partWeight ρ.τ b (twoCharts i₁ s b y) := rfl

theorem atlas_ω_false (y : Fin n → ℝ) : (ρ.atlas hne ha).ω false y = ρ.τ y := rfl

theorem atlas_ω_true (y : Fin n → ℝ) :
    (ρ.atlas hne ha).ω true y = 1 - ρ.τ (shift i₁ s y) := rfl

theorem atlas_φ (b : Bool) : (ρ.atlas hne ha).φ b = twoCharts i₁ s b := rfl

theorem atlas_W : (ρ.atlas hne ha).W = shiftedSet i₁ a s := rfl

/-- (1) **Subordination**: the target weight of a chart vanishes on the part of the union not
covered by that chart. -/
theorem partWeight_subordinate (b : Bool) {x : Fin n → ℝ} (hx : x ∈ shiftedSet i₁ a s)
    (hb : x ∉ twoCharts i₁ s b '' centeredBox n a) : partWeight ρ.τ b x = 0 := by
  cases b
  · rw [twoCharts_false, image_id] at hb
    rw [partWeight_false]
    exact ρ.eq_zero x (hx.resolve_left hb) hb
  · rw [twoCharts_true] at hb
    rw [partWeight_true, ρ.eq_one x (hx.resolve_right hb) hb, sub_self]

/-- (1) The chart weights are smooth. -/
theorem contDiff_atlas_ω (b : Bool) : ContDiff ℝ ∞ ((ρ.atlas hne ha).ω b) :=
  (contDiff_partWeight ρ.smooth b).comp (contDiff_twoCharts i₁ s b)

/-- (2) **The weighted change-of-variables identity** for the atlas: the sum over the two charts
of the push-forwards of the weighted sector measures is `(vol|_Ω).withDensity f`. -/
theorem weightedDomainTransport {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∑ b, ((ρ.atlas hne ha).sectorMeasure f b).map (twoCharts i₁ s b) =
      (volume.restrict (shiftedSet i₁ a s)).withDensity f :=
  (ρ.atlas hne ha).weightedDomainTransport hf

end SmoothRamp

/-! ### The smooth sheet inputs -/

section Inputs

variable {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) {a : ℝ} (ha : 0 < a) {s : ℝ} (ρ : SmoothRamp i₁ a s)
  {P Q : (Fin n → ℝ) → ℝ} (hP : ContDiff ℝ ∞ P) (hP0 : ∀ w, 0 ≤ P w) (hQ : ContDiff ℝ ∞ Q)

/-- ★★ **The overlapping atlas with a smooth ramp satisfies the smooth sheet inputs**, for smooth
`P ≥ 0` and `Q`: no `ω_indep`, no packets. -/
noncomputable def smoothOverlapInputs : SmoothSheetInputs n where
  K := monoPhase (Pi.single i₀ 1)
  K_m := (SheetAssembly.continuous_monoPhase _).measurable
  Ω := shiftedSet i₁ a s
  A := ρ.atlas hne ha
  a := a
  ha := ha
  lo_eq _ _ := rfl
  hi_eq _ _ := rfl
  K_nonneg w _ := by
    rw [monoPhase_single]
    exact sq_nonneg _
  prior := P
  obs := Q
  prior_nonneg := hP0
  prior_smooth := hP
  obs_smooth := hQ
  obs_int := SheetAssembly.integrable_of_continuous_of_subset_compact hP.continuous hQ.continuous
    (isCompact_shiftedSet i₁ a s) subset_rfl (isCompact_shiftedSet i₁ a s).isClosed.measurableSet
  φ_smooth b := contDiff_twoCharts i₁ s b
  ω_smooth b := ρ.contDiff_atlas_ω hne ha b
  jacAbs_smooth b := by
    change ContDiff ℝ ∞ fun _ : Fin n → ℝ => |(1 : ℝ)|
    exact contDiff_const
  hu_tan _ _ _ _ := rfl

theorem smoothOverlapInputs_K : (smoothOverlapInputs hne ha ρ hP hP0 hQ).K =
    monoPhase (Pi.single i₀ 1) := rfl

theorem smoothOverlapInputs_W : (smoothOverlapInputs hne ha ρ hP hP0 hQ).A.W =
    shiftedSet i₁ a s := rfl

/-- The phase as a coordinate square. -/
theorem monoPhase_single_eq : monoPhase (Pi.single i₀ 1) = fun x : Fin n → ℝ => x i₀ ^ 2 :=
  funext (monoPhase_single i₀)

/-- ★★★ (4) **Smooth overlap regression**: the coordinate-free expansion of
`∫_Ω Q · P · e^{−N y_{i₀}²}` on the union of the box and its translate, through two genuinely
overlapping charts with arbitrary smooth partition weights. -/
theorem smoothOverlap_hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion
      (globalLaplace (shiftedSet i₁ a s) (fun x => x i₀ ^ 2) fun w => P w * Q w)
      (smoothOverlapInputs hne ha ρ hP hP0 hQ).decomp.coeff
      (smoothOverlapInputs hne ha ρ hP hP0 hQ).decomp.commonQ
      (smoothOverlapInputs hne ha ρ hP hP0 hQ).decomp.commonD := by
  rw [← monoPhase_single_eq]
  exact (smoothOverlapInputs hne ha ρ hP hP0 hQ).hasSmoothCoordFreeExpansion

/-- ★★ (5) **Ramp independence**: two admissible smooth ramps give the same scalar coefficients,
by presentation independence (`coeff_eq_of_inputs`). -/
theorem coeff_eq_of_ramp (ρ' : SmoothRamp i₁ a s) :
    (smoothOverlapInputs hne ha ρ hP hP0 hQ).decomp.coeff =
      (smoothOverlapInputs hne ha ρ' hP hP0 hQ).decomp.coeff :=
  funext fun μ => funext fun q =>
    (smoothOverlapInputs hne ha ρ hP hP0 hQ).coeff_eq_of_inputs
      (Y := smoothOverlapInputs hne ha ρ' hP hP0 hQ) rfl rfl rfl rfl μ q

end Inputs

/-! ### The smooth ramp with a genuine active dependence -/

/-- The affine coordinate of the overlap along `i₁`: `0` at `x_{i₁} = s − a`, `1` at
`x_{i₁} = a`. -/
noncomputable def overlapCoord (i₁ : Fin n) (a s : ℝ) (x : Fin n → ℝ) : ℝ :=
  (x i₁ - (s - a)) / (2 * a - s)

theorem contDiff_overlapCoord (i₁ : Fin n) (a s : ℝ) : ContDiff ℝ ∞ (overlapCoord i₁ a s) :=
  ((contDiff_apply ℝ ℝ i₁).sub contDiff_const).div_const _

theorem overlapCoord_nonpos {i₁ : Fin n} {a s : ℝ} (hs : s < 2 * a) {x : Fin n → ℝ}
    (hx : x i₁ ≤ s - a) : overlapCoord i₁ a s x ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem one_le_overlapCoord {i₁ : Fin n} {a s : ℝ} (hs : s < 2 * a) {x : Fin n → ℝ}
    (hx : a ≤ x i₁) : 1 ≤ overlapCoord i₁ a s x := by
  rw [overlapCoord, le_div_iff₀ (by linarith)]
  linarith

theorem overlapCoord_of_mid {i₁ : Fin n} {a s : ℝ} (hs : s < 2 * a) {x : Fin n → ℝ}
    (hx : x i₁ = s / 2) : overlapCoord i₁ a s x = 1 / 2 := by
  rw [overlapCoord, hx, div_eq_div_iff (by linarith) two_ne_zero]
  ring

/-- ★ **The active ramp**: `τ(x) = 1 − σ(2 r(x_{i₁}) − 1 + σ(x_{i₀}²))` with `σ` the smooth
transition. It is `1` for `x_{i₁} ≤ s − a`, `0` for `x_{i₁} ≥ a`, and in between depends on the
ACTIVE coordinate `x_{i₀}`. -/
noncomputable def activeRamp (i₀ i₁ : Fin n) (a s : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 - Real.smoothTransition
    (2 * overlapCoord i₁ a s x - 1 + Real.smoothTransition (x i₀ ^ 2))

section activeRamp

variable {i₀ i₁ : Fin n} {a s : ℝ}

theorem contDiff_activeRamp : ContDiff ℝ ∞ (activeRamp i₀ i₁ a s) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_overlapCoord i₁ a s)).sub contDiff_const).add
      (Real.smoothTransition.contDiff.comp ((contDiff_apply ℝ ℝ i₀).pow 2))))

theorem activeRamp_nonneg (x : Fin n → ℝ) : 0 ≤ activeRamp i₀ i₁ a s x :=
  sub_nonneg.2 (Real.smoothTransition.le_one _)

theorem activeRamp_le_one (x : Fin n → ℝ) : activeRamp i₀ i₁ a s x ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem activeRamp_eq_one (hs : s < 2 * a) {x : Fin n → ℝ} (hx : x i₁ ≤ s - a) :
    activeRamp i₀ i₁ a s x = 1 := by
  unfold activeRamp
  rw [Real.smoothTransition.zero_of_nonpos, sub_zero]
  linarith [overlapCoord_nonpos hs hx, Real.smoothTransition.le_one (x i₀ ^ 2)]

theorem activeRamp_eq_zero (hs : s < 2 * a) {x : Fin n → ℝ} (hx : a ≤ x i₁) :
    activeRamp i₀ i₁ a s x = 0 := by
  unfold activeRamp
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  linarith [one_le_overlapCoord hs hx, Real.smoothTransition.nonneg (x i₀ ^ 2)]

variable (i₀ i₁)

/-- The active ramp is an admissible smooth partition function on the union. -/
noncomputable def activeSmoothRamp (hs0 : 0 < s) (hs : s < 2 * a) : SmoothRamp i₁ a s where
  τ := activeRamp i₀ i₁ a s
  smooth := contDiff_activeRamp
  nonneg := activeRamp_nonneg
  le_one := activeRamp_le_one
  eq_one x h0 h1 := activeRamp_eq_one hs
    (by linarith [coord_le_of_notMem_shift_image i₁ hs0 h0 h1])
  eq_zero x h1 h0 := activeRamp_eq_zero hs (le_coord_of_notMem_centeredBox i₁ hs0 h1 h0)

/-! ### Non-tangentiality -/

/-- The witness point: `x_{i₁} = s/2` (the middle of the overlap), `x_{i₀} = t`, `0` elsewhere. -/
noncomputable def midPoint (s t : ℝ) : Fin n → ℝ :=
  Function.update (Function.update 0 i₁ (s / 2)) i₀ t

variable {i₀ i₁}

theorem midPoint_apply_i₀ (s t : ℝ) : midPoint i₀ i₁ s t i₀ = t := Function.update_self _ _ _

theorem midPoint_apply_i₁ (hne : i₀ ≠ i₁) (s t : ℝ) : midPoint i₀ i₁ s t i₁ = s / 2 := by
  rw [midPoint, Function.update_of_ne hne.symm, Function.update_self]

theorem update_midPoint (s t t' : ℝ) :
    Function.update (midPoint i₀ i₁ s t) i₀ t' = midPoint i₀ i₁ s t' :=
  Function.update_idem _ _ _

/-- At the middle of the overlap the active ramp is `1 − σ(σ(x_{i₀}²))`. -/
theorem activeRamp_midPoint (hne : i₀ ≠ i₁) (hs : s < 2 * a) (t : ℝ) :
    activeRamp i₀ i₁ a s (midPoint i₀ i₁ s t) =
      1 - Real.smoothTransition (Real.smoothTransition (t ^ 2)) := by
  rw [activeRamp, overlapCoord_of_mid hs (midPoint_apply_i₁ hne s t), midPoint_apply_i₀]
  norm_num

/-- ★ (3) **Non-tangentiality of the active ramp**: for every `t₀ > 0` there is a point with
`|x_{i₀}| ≤ t₀` at which the identity-chart weight changes when the active coordinate is set to
`0`. -/
theorem activeRamp_not_tangential (hne : i₀ ≠ i₁) (ha : 0 < a) (hs0 : 0 < s) (hs : s < 2 * a)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ x : Fin n → ℝ, |x i₀| ≤ t₀ ∧
      ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).ω false (Function.update x i₀ 0) ≠
        ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).ω false x := by
  refine ⟨midPoint i₀ i₁ s (t₀ / 2), ?_, ?_⟩
  · rw [midPoint_apply_i₀, abs_of_pos (by linarith)]
    linarith
  · rw [SmoothRamp.atlas_ω_false, SmoothRamp.atlas_ω_false, update_midPoint]
    change activeRamp i₀ i₁ a s (midPoint i₀ i₁ s 0) ≠ activeRamp i₀ i₁ a s (midPoint i₀ i₁ s _)
    rw [activeRamp_midPoint hne hs, activeRamp_midPoint hne hs]
    have h0 : Real.smoothTransition (Real.smoothTransition ((0 : ℝ) ^ 2)) = 0 := by
      rw [zero_pow two_ne_zero, Real.smoothTransition.zero, Real.smoothTransition.zero]
    have hpos : 0 < Real.smoothTransition (Real.smoothTransition ((t₀ / 2) ^ 2)) :=
      Real.smoothTransition.pos_of_pos (Real.smoothTransition.pos_of_pos (by positivity))
    rw [h0]
    intro h
    linarith

/-- ★ (3) **The analytic producer's hypothesis `ω_indep` fails** for the active ramp, at every
`t₀ > 0`: the weights are NOT constant along the active coordinate near the divisor. -/
theorem activeRamp_not_ω_indep (hne : i₀ ≠ i₁) (ha : 0 < a) (hs0 : 0 < s) (hs : s < 2 * a)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ¬ ∀ i j, 0 < ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).k i j →
      ∀ y : Fin n → ℝ, |y j| ≤ t₀ →
        ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).ω i (Function.update y j 0) =
          ((activeSmoothRamp i₀ i₁ hs0 hs).atlas hne ha).ω i y := by
  intro h
  obtain ⟨x, hx, hx'⟩ := activeRamp_not_tangential hne ha hs0 hs ht₀
  refine hx' (h false i₀ ?_ x hx)
  change 0 < (Pi.single i₀ 1 : Fin n → ℕ) i₀
  rw [Pi.single_eq_same]
  exact one_pos

/-! ### The expansion and the ramp independence at the active ramp -/

variable {P Q : (Fin n → ℝ) → ℝ}

/-- ★★★ (4) **The expansion through the active ramp**: the coordinate-free expansion of
`∫_Ω Q · P · e^{−N y_{i₀}²}` through the two overlapping charts weighted by the smooth ramp that
depends nontrivially on the active coordinate. -/
theorem activeOverlap_hasSmoothCoordFreeExpansion (hne : i₀ ≠ i₁) (ha : 0 < a) (hs0 : 0 < s)
    (hs : s < 2 * a) (hP : ContDiff ℝ ∞ P) (hP0 : ∀ w, 0 ≤ P w) (hQ : ContDiff ℝ ∞ Q) :
    HasSmoothCoordFreeExpansion
      (globalLaplace (shiftedSet i₁ a s) (fun x => x i₀ ^ 2) fun w => P w * Q w)
      (smoothOverlapInputs hne ha (activeSmoothRamp i₀ i₁ hs0 hs) hP hP0 hQ).decomp.coeff
      (smoothOverlapInputs hne ha (activeSmoothRamp i₀ i₁ hs0 hs) hP hP0 hQ).decomp.commonQ
      (smoothOverlapInputs hne ha (activeSmoothRamp i₀ i₁ hs0 hs) hP hP0 hQ).decomp.commonD :=
  smoothOverlap_hasSmoothCoordFreeExpansion hne ha _ hP hP0 hQ

/-- The purely tangential smooth ramp `τ(x) = 1 − σ(r(x_{i₁}))`, constant along `x_{i₀}`. -/
noncomputable def tangentialRamp (i₁ : Fin n) (a s : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 - Real.smoothTransition (overlapCoord i₁ a s x)

theorem tangentialRamp_eq_one (hs : s < 2 * a) {x : Fin n → ℝ} (hx : x i₁ ≤ s - a) :
    tangentialRamp i₁ a s x = 1 := by
  rw [tangentialRamp, Real.smoothTransition.zero_of_nonpos (overlapCoord_nonpos hs hx), sub_zero]

theorem tangentialRamp_eq_zero (hs : s < 2 * a) {x : Fin n → ℝ} (hx : a ≤ x i₁) :
    tangentialRamp i₁ a s x = 0 := by
  rw [tangentialRamp, Real.smoothTransition.one_of_one_le (one_le_overlapCoord hs hx), sub_self]

/-- The tangential ramp is constant along every coordinate other than `i₁`. -/
theorem tangentialRamp_update {j : Fin n} (hj : j ≠ i₁) (x : Fin n → ℝ) (t : ℝ) :
    tangentialRamp i₁ a s (Function.update x j t) = tangentialRamp i₁ a s x := by
  simp only [tangentialRamp, overlapCoord, Function.update_of_ne hj.symm]

/-- The tangential ramp is an admissible smooth partition function on the union. -/
noncomputable def tangentialSmoothRamp (i₁ : Fin n) (hs0 : 0 < s) (hs : s < 2 * a) :
    SmoothRamp i₁ a s where
  τ := tangentialRamp i₁ a s
  smooth := contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_overlapCoord i₁ a s))
  nonneg _ := sub_nonneg.2 (Real.smoothTransition.le_one _)
  le_one _ := sub_le_self _ (Real.smoothTransition.nonneg _)
  eq_one x h0 h1 := tangentialRamp_eq_one hs
    (by linarith [coord_le_of_notMem_shift_image i₁ hs0 h0 h1])
  eq_zero x h1 h0 := tangentialRamp_eq_zero hs (le_coord_of_notMem_centeredBox i₁ hs0 h1 h0)

/-- ★★ (5) **Ramp independence at the active ramp**: the active (non-tangential) smooth ramp and
the tangential smooth ramp give literally the same scalar coefficients. -/
theorem coeff_active_eq_coeff_tangential (hne : i₀ ≠ i₁) (ha : 0 < a) (hs0 : 0 < s)
    (hs : s < 2 * a) (hP : ContDiff ℝ ∞ P) (hP0 : ∀ w, 0 ≤ P w) (hQ : ContDiff ℝ ∞ Q) :
    (smoothOverlapInputs hne ha (activeSmoothRamp i₀ i₁ hs0 hs) hP hP0 hQ).decomp.coeff =
      (smoothOverlapInputs hne ha (tangentialSmoothRamp i₁ hs0 hs) hP hP0 hQ).decomp.coeff :=
  coeff_eq_of_ramp hne ha _ hP hP0 hQ _

end activeRamp

end SmoothEngine

end Grammar
