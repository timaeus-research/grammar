/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetBoundaryRegression
import Grammar.SheetCentredCubeRegression
import Monomialize.Transport.ShiftedBoxAtlas

/-!
# Regression: genuinely overlapping charts through the weighted producer (consult #113 unit 7)

The phase `y_{i₀}²` on the union of the box `[−a,a]^n` and its translate by `0 < s < 2a` along
an inactive coordinate `i₁ ≠ i₀`, covered by the identity chart and the translation chart on the
common box (`hironaka`'s `shiftedAtlas`): the two chart images overlap in a set of positive
measure (`overlap_volume_pos`), the weights are the ramp `ρ(x_{i₁})`, `1 − ρ(x_{i₁})` — genuinely
nonconstant (`ω_false_eq_one`, `ω_false_eq_zero`), continuous, constant along the active
coordinate (`ω_indep`), summing to one on the union — and the weighted producer (CCCLXXXIV)
gives the coordinate-free expansion of `∫_Ω Q · P · e^{−n y_{i₀}²}` for polynomial `P ≥ 0`, `Q`,
with the packets of the translated chart by polynomial substitution
(★★ `overlap_hasCoordFreeExpansion`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling WaterFilling

/-- The translation as a polynomial substitution. -/
noncomputable def shiftPoly {n : ℕ} (i₁ : Fin n) (s : ℝ) (j : Fin n) : MvPolynomial (Fin n) ℝ :=
  X j + C (if j = i₁ then s else 0)

theorem eval_shiftPoly_fun {n : ℕ} (i₁ : Fin n) (s : ℝ) (v : Fin n → ℝ) :
    (fun j => eval v (shiftPoly i₁ s j)) = shift i₁ s v := by
  funext j
  simp only [shiftPoly, map_add, eval_X, eval_C, shift_apply, Pi.single_apply]

variable {n : ℕ} (i₀ i₁ : Fin n) (hne : i₀ ≠ i₁) {a : ℝ} (ha : 0 < a) {s : ℝ} (hs0 : 0 < s)
  (hs : s < 2 * a) (P Q : MvPolynomial (Fin n) ℝ) (hP : ∀ w, 0 ≤ eval w P)

omit hP in
/-- The packets of the two charts: the polynomials themselves for the identity chart, their
substitutions for the translation chart. -/
noncomputable def overlapPacket (b : Bool) :
    HolomorphicSignedBoxExtension a
      (fun v => |(shiftedAtlas i₀ i₁ hne ha hs0 hs).jacUnit b v| *
        eval ((shiftedAtlas i₀ i₁ hne ha hs0 hs).φ b v) P)
      ((fun w => eval w Q) ∘ (shiftedAtlas i₀ i₁ hne ha hs0 hs).φ b) := by
  cases b
  · exact (HolomorphicSignedBoxExtension.ofPolynomials a P Q).congr
      (by
        funext v
        change |(1 : ℝ)| * eval v P = eval v P
        rw [abs_one, one_mul]) rfl
  · exact (HolomorphicSignedBoxExtension.ofPolynomials a (bind₁ (shiftPoly i₁ s) P)
      (bind₁ (shiftPoly i₁ s) Q)).congr
      (by
        funext v
        change |(1 : ℝ)| * eval (shift i₁ s v) P = eval v (bind₁ (shiftPoly i₁ s) P)
        rw [abs_one, one_mul, eval_bind₁', eval_shiftPoly_fun])
      (by
        funext v
        change eval (shift i₁ s v) Q = eval v (bind₁ (shiftPoly i₁ s) Q)
        rw [eval_bind₁', eval_shiftPoly_fun])

omit hP in
/-- The chart weights depend only on the coordinate `i₁`. -/
theorem ω_eq_of_coord (b : Bool) {y y' : Fin n → ℝ} (h : y i₁ = y' i₁) :
    (shiftedAtlas i₀ i₁ hne ha hs0 hs).ω b y = (shiftedAtlas i₀ i₁ hne ha hs0 hs).ω b y' := by
  change shiftWeight i₁ a s b (twoCharts i₁ s b y) = shiftWeight i₁ a s b (twoCharts i₁ s b y')
  cases b
  · rw [twoCharts_false, shiftWeight_false, shiftWeight_false]
    exact congrArg _ h
  · rw [twoCharts_true, shiftWeight_true, shiftWeight_true, shift_apply_self, shift_apply_self, h]

omit hP in
theorem continuous_ω (b : Bool) : Continuous ((shiftedAtlas i₀ i₁ hne ha hs0 hs).ω b) := by
  cases b
  · exact (continuous_shiftWeight i₁ a s false).comp continuous_id
  · exact (continuous_shiftWeight i₁ a s true).comp (continuous_shift i₁ s)

/-- ★★ **The overlapping atlas satisfies the sheet-assembly inputs.** -/
noncomputable def overlapInputs : SheetInputs n where
  K := monoPhase (Pi.single i₀ 1)
  K_m := (continuous_monoPhase _).measurable
  Ω := shiftedSet i₁ a s
  A := shiftedAtlas i₀ i₁ hne ha hs0 hs
  a := a
  ha := ha
  lo_eq _ _ := rfl
  hi_eq _ _ := rfl
  φ_m b := by
    cases b
    · exact measurable_id
    · exact (continuous_shift i₁ s).measurable
  jacUnit_m _ := measurable_const
  hu_cont _ := continuous_const
  hu_tan _ _ _ _ := rfl
  c _ := 1
  hc _ := one_pos
  hu_lb _ _ _ := le_rfl
  prior := fun w => eval w P
  obs := fun w => eval w Q
  prior_m := (MvPolynomial.continuous_eval P).measurable
  prior_nonneg := hP
  obs_m := (MvPolynomial.continuous_eval Q).measurable
  obs_int := integrable_of_continuous_of_subset_compact (MvPolynomial.continuous_eval P)
    (MvPolynomial.continuous_eval Q) (isCompact_shiftedSet i₁ a s) subset_rfl
    (isCompact_shiftedSet i₁ a s).isClosed.measurableSet
  P := overlapPacket i₀ i₁ hne ha hs0 hs P Q
  signs_nonempty _ := Finset.univ_nonempty
  ι_nonempty := ⟨false⟩
  t₀ := a
  t₀_pos := ha
  ω_indep := fun b j hj y _ => by
    have hj0 : j = i₀ := by
      by_contra hcon
      change 0 < (Pi.single i₀ 1 : Fin n → ℕ) j at hj
      rw [Pi.single_eq_of_ne hcon] at hj
      exact lt_irrefl _ hj
    rw [hj0]
    exact ω_eq_of_coord i₀ i₁ hne ha hs0 hs b (Function.update_of_ne hne.symm _ _)
  ω_contOn b := (continuous_ω i₀ i₁ hne ha hs0 hs b).continuousOn

omit hP in
include hs0 hs in
/-- The chart images overlap in a set of positive measure. -/
theorem overlap_volume_pos :
    0 < volume (centeredBox n a ∩ shift i₁ s '' centeredBox n a) := by
  have hsub : (pi univ fun i => Ioo (if i = i₁ then -a + s else -a) a) ⊆
      centeredBox n a ∩ shift i₁ s '' centeredBox n a := by
    intro x hx
    refine ⟨fun i => ?_, (mem_shift_image i₁ s).2 fun i => ?_⟩
    · have := hx i (mem_univ _)
      rw [mem_Ioo] at this
      rw [abs_le]
      split_ifs at this with hi
      · constructor <;> linarith
      · constructor <;> linarith
    · have := hx i (mem_univ _)
      rw [mem_Ioo] at this
      by_cases hi : i = i₁
      · subst hi
        rw [if_pos rfl] at this
        rw [Pi.sub_apply, Pi.single_eq_same, abs_le]
        constructor <;> linarith
      · rw [if_neg hi] at this
        rw [Pi.sub_apply, Pi.single_eq_of_ne hi, sub_zero, abs_le]
        constructor <;> linarith
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_pi_Ioo]
  refine CanonicallyOrderedAdd.prod_pos.2 fun i _ => ?_
  rw [ENNReal.ofReal_pos]
  split_ifs <;> linarith

omit hP in
/-- The weight of the identity chart is `1` at the far end of its box. -/
theorem ω_false_eq_one : (shiftedAtlas i₀ i₁ hne ha hs0 hs).ω false (fun _ => -a) = 1 := by
  change shiftWeight i₁ a s false (twoCharts i₁ s false fun _ => -a) = 1
  rw [twoCharts_false, shiftWeight_false]
  exact Monomialize.VolumeScaling.ramp_eq_one hs (by change (-a : ℝ) ≤ -a + s; linarith)

omit hP in
/-- The weight of the identity chart is `0` at the near end of its box. -/
theorem ω_false_eq_zero : (shiftedAtlas i₀ i₁ hne ha hs0 hs).ω false (fun _ => a) = 0 := by
  change shiftWeight i₁ a s false (twoCharts i₁ s false fun _ => a) = 0
  rw [twoCharts_false, shiftWeight_false]
  exact Monomialize.VolumeScaling.ramp_eq_zero hs le_rfl

/-- ★★ **Overlap regression**: the coordinate-free expansion of `∫_Ω Q · P · e^{−n y_{i₀}²}` on the
union of the box and its translate, through two genuinely overlapping charts with nonconstant
tangential weights. -/
theorem overlap_hasCoordFreeExpansion :
    (Sheet.normalData (shiftedChartAtlas i₀ i₁ hne ha s)).HasCoordFreeExpansion
      (overlapInputs i₀ i₁ hne ha hs0 hs P Q hP).cert.stratumMeasure
      (overlapInputs i₀ i₁ hne ha hs0 hs P Q hP).coeffCert.field
      (spectrumLe (commonQ (overlapInputs i₀ i₁ hne ha hs0 hs P Q hP).cert.cores.k)
        (commonD (overlapInputs i₀ i₁ hne ha hs0 hs P Q hP).cert.n))
      (shiftedSet i₁ a s) (monoPhase (Pi.single i₀ 1)) (fun w => eval w P) (fun w => eval w Q) :=
  (overlapInputs i₀ i₁ hne ha hs0 hs P Q hP).hasCoordFreeExpansion

end SheetAssembly

end Grammar
