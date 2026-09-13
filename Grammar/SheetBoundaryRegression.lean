/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetAssembly
import Grammar.SignedBoxExpansion
import Monomialize.Transport.MonomialBoxAtlas

/-!
# Regression: a genuine boundary through the general producer (consult #112 §6)

The monomial phase `∏_j y_j^{2 k_j}` (all `k_j > 0`) on the centred box `[−a,a]^n`, on the domain
`W = [−a,a]^n ∩ {y_{c 1} ≥ 0, …, y_{c r} ≥ 0}` cut out by coordinate half-spaces (`hironaka`'s
`monomialHalfBoxAtlas`: the identity chart, the admissible orthants are exactly those with
`σ (c j) = true`), with polynomial prior `P ≥ 0` and observable `Q`, satisfies the sheet-assembly
inputs (`boundaryInputs`). The general producer therefore gives the coordinate-free expansion of
`∫_W Q · P · e^{−n ∏ y^{2k}}` on the sheet strata (★★ `boundary_hasCoordFreeExpansion`), with the
full logarithmic degree `n − 1` (`boundaryInputs_commonD`). Astra's instance is `n = 2`,
`k = (1,1)`, `c = (0)`, `P = Q = 1`: `∫_0^1 ∫_{−1}^1 e^{−n x² y²} ∼ (√π/2) n^{−1/2} log n`. This
exercises a PROPER subset of the orthants (sign filtering by `ofBoundaryMonomials`), a crossing
divisor and a logarithmic term, through the domain-sector producer. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling WaterFilling ChartCollar

/-- A continuous observable is integrable for the measure with a continuous nonnegative density on
a subset of a compact set. -/
theorem integrable_of_continuous_of_subset_compact {d : ℕ} {p F : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) (hF : Continuous F) {W Kc : Set (Fin d → ℝ)} (hKc : IsCompact Kc)
    (hW : W ⊆ Kc) (hWm : MeasurableSet W) :
    Integrable F ((volume.restrict W).withDensity fun w => ENNReal.ofReal (p w)) := by
  obtain ⟨Cp, hCp⟩ := hKc.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn hF.continuousOn
  have : IsFiniteMeasure ((volume.restrict W).withDensity fun w => ENNReal.ofReal (p w)) := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ w, ENNReal.ofReal (p w) ∂(volume.restrict W)
        ≤ ∫⁻ _, ENNReal.ofReal Cp ∂(volume.restrict W) := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hWm]
          refine Eventually.of_forall fun w hw => ENNReal.ofReal_le_ofReal ?_
          have := hCp w (hW hw)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal Cp * volume W := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono hW).trans_lt hKc.measure_lt_top)
  refine (integrable_const CF).mono' hF.measurable.aestronglyMeasurable ?_
  refine Filter.le_def.1 (withDensity_absolutelyContinuous _ _).ae_le _ ?_
  change ∀ᵐ w ∂volume.restrict W, ‖F w‖ ≤ CF
  rw [ae_restrict_iff' hWm]
  exact Eventually.of_forall fun w hw => hCF w (hW hw)

variable {n : ℕ} (k : Fin n → ℕ) (hk : ∀ j, 0 < k j) {a : ℝ} (ha : 0 < a) {r : ℕ}
  (c : Fin r → Fin n) (P Q : MvPolynomial (Fin n) ℝ) (hP : ∀ w, 0 ≤ eval w P)

theorem continuous_monoPhase : Continuous (monoPhase k) :=
  continuous_finsetProd _ fun j _ => (continuous_apply j).pow _

include k ha in
/-- The half-space domain atlas has measurable domain. -/
theorem measurableSet_halfBox :
    MeasurableSet (centeredBox n a ∩ {y : Fin n → ℝ | ∀ j, 0 ≤ y (c j)}) :=
  (monomialHalfBoxAtlas k ha c).measurableSet_W

omit hk hP in
/-- The prior factor of the identity chart is the polynomial prior. -/
theorem priorFactor_eq (i : Unit) :
    (fun v => |(monomialHalfBoxAtlas k ha c).jacUnit i v| *
      eval ((monomialHalfBoxAtlas k ha c).φ i v) P) = fun w => eval w P := by
  funext v
  change |(1 : ℝ)| * eval v P = eval v P
  rw [abs_one, one_mul]

/-- ★★ **The coordinate half-space domain satisfies the sheet-assembly inputs**: the identity
chart, units `1`, the polynomial packets. -/
noncomputable def boundaryInputs [NeZero n] : SheetInputs n where
  K := monoPhase k
  K_m := (continuous_monoPhase k).measurable
  Ω := centeredBox n a
  A := monomialHalfBoxAtlas k ha c
  a := a
  ha := ha
  lo_eq _ _ := rfl
  hi_eq _ _ := rfl
  φ_m _ := measurable_id
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
    (MvPolynomial.continuous_eval Q) (isCompact_centeredBox n a) inter_subset_left
    (measurableSet_halfBox k ha c)
  P i := (HolomorphicSignedBoxExtension.ofPolynomials a P Q).congr (priorFactor_eq k ha c P i) rfl
  signs_nonempty i := signs_monomialHalfBoxAtlas_nonempty k ha c i
  ι_nonempty := ⟨()⟩

theorem boundaryInputs_W [NeZero n] :
    (boundaryInputs k ha c P Q hP).A.W =
      centeredBox n a ∩ {y : Fin n → ℝ | ∀ j, 0 ≤ y (c j)} := rfl

theorem boundaryInputs_signs [NeZero n] (i : Unit) (σ : WaterFilling.CoordSign n) :
    σ ∈ (boundaryInputs k ha c P Q hP).A.signs i ↔ ∀ j, σ (c j) = true :=
  mem_signs_monomialHalfBoxAtlas k ha c i σ

/-- ★★ **Boundary regression**: the coordinate-free expansion of
`∫_{[−a,a]^n ∩ {y_{c j} ≥ 0}} Q · P · e^{−n ∏ y^{2k}}` through the domain-sector producer. -/
theorem boundary_hasCoordFreeExpansion [NeZero n] :
    (Sheet.normalData (monomialBoxAtlas k ha)).HasCoordFreeExpansion
      (boundaryInputs k ha c P Q hP).cert.stratumMeasure
      (boundaryInputs k ha c P Q hP).coeffCert.field
      (spectrumLe (commonQ (boundaryInputs k ha c P Q hP).cert.cores.k)
        (commonD (boundaryInputs k ha c P Q hP).cert.n))
      (centeredBox n a ∩ {y : Fin n → ℝ | ∀ j, 0 ≤ y (c j)}) (monoPhase k)
      (fun w => eval w P) (fun w => eval w Q) :=
  (boundaryInputs k ha c P Q hP).hasCoordFreeExpansion

/-! ### The logarithmic degree -/

include hk in
/-- Every coordinate is active. -/
theorem boundaryInputs_act [NeZero n] (i : Unit) :
    (boundaryInputs k ha c P Q hP).act i = Finset.univ := by
  unfold SheetInputs.act
  exact Finset.filter_true_of_mem fun j _ => hk j

theorem boundaryInputs_n_le [NeZero n] (l : Fin (boundaryInputs k ha c P Q hP).N) :
    (boundaryInputs k ha c P Q hP).cert.n l ≤ n - 1 := by
  change (amb ((boundaryInputs k ha c P Q hP).act _) _).card - 1 ≤ n - 1
  exact Nat.sub_le_sub_right ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n)) 1

/-- The crossing core: the deepest stratum of the (unique) chart, all signs positive. -/
noncomputable def crossingCore [NeZero n] : Fin (boundaryInputs k ha c P Q hP).N :=
  (boundaryInputs k ha c P Q hP).coreEnum.symm
    ⟨⟨⟨(), ⟨fun _ => true, (boundaryInputs_signs k ha c P Q hP () _).2 fun _ => rfl⟩⟩,
      ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk 0⟩⟩⟩,
      (coreIdx ((boundaryInputs k ha c P Q hP).act ())).symm
        ⟨Finset.univ, Finset.univ_nonempty_iff.2 ⟨⟨0, by
          rw [boundaryInputs_act k hk ha c P Q hP]; exact Finset.mem_univ _⟩⟩⟩⟩

theorem n_crossingCore [NeZero n] :
    (boundaryInputs k ha c P Q hP).cert.n (crossingCore k hk ha c P Q hP) = n - 1 := by
  change nI ((boundaryInputs k ha c P Q hP).act
      ((boundaryInputs k ha c P Q hP).coreEnum (crossingCore k hk ha c P Q hP)).1.1.1)
    (coreIdx _ ((boundaryInputs k ha c P Q hP).coreEnum (crossingCore k hk ha c P Q hP)).2) =
      n - 1
  rw [crossingCore, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (amb ((boundaryInputs k ha c P Q hP).act ()) _).card - 1 = n - 1
  rw [card_amb]
  change (Finset.univ : Finset ↥((boundaryInputs k ha c P Q hP).act ())).card - 1 = n - 1
  rw [Finset.card_univ, Fintype.card_coe, boundaryInputs_act k hk ha c P Q hP, Finset.card_univ,
    Fintype.card_fin]

include hk in
/-- ★ **The full logarithmic degree**: `commonD = n − 1` (the crossing of all `n` coordinate
divisors), in contrast with the cube's `0`. -/
theorem boundaryInputs_commonD [NeZero n] :
    commonD (boundaryInputs k ha c P Q hP).cert.n = n - 1 :=
  le_antisymm (Finset.sup_le fun l _ => boundaryInputs_n_le k ha c P Q hP l)
    ((n_crossingCore k hk ha c P Q hP).symm.le.trans (le_commonD _))

end SheetAssembly

end Grammar
