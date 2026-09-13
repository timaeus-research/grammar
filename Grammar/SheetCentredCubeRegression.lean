/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetRescale
import Grammar.SheetCubeRegression
import Grammar.SignedBoxExpansion

/-!
# Regression: the `ρ`-cube through the centred-box producer

The cube blow-up atlas of side `ρ` (`cubeBlowUpAtlas ρ`) has CENTRED, non-symmetric chart boxes
(side `ρ` at the pivot, `1` elsewhere). With every orthant selected, polynomial prior `P ≥ 0` and
observable `Q`, and the chart packets obtained by SUBSTITUTING the polynomial chart
`y ↦ (y_β, y_β y_γ)` into `P`, `Q` (`chartPoly`, `bind₁`), it satisfies the centred inputs
(`cubeCentredInputs`), and the rescaled producer (CCCLXXXI) gives the coordinate-free expansion of
`∫_{[−ρ,ρ]^d} Q · P · e^{−n|x|²}` (★★ `cubeρ_hasCoordFreeExpansion`). This is the end-to-end test
of the centred-box normalisation and of polynomial packets by substitution. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling WaterFilling BlowUpCube

/-- Evaluation of a substituted polynomial. -/
theorem eval_bind₁' {σ τ : Type*} (v : τ → ℝ) (g : σ → MvPolynomial τ ℝ) (p : MvPolynomial σ ℝ) :
    eval v (bind₁ g p) = eval (fun i => eval v (g i)) p := by
  rw [hom_bind₁]
  have : (eval v).comp C = RingHom.id ℝ := RingHom.ext fun r => eval_C r
  rw [this]
  rfl

variable {d : ℕ} [NeZero d] {ρ : ℝ} (hρ : 0 < ρ) (P Q : MvPolynomial (Fin d) ℝ)
  (hP : ∀ w, 0 ≤ eval w P)

/-- The `ρ`-cube domain atlas: every orthant selected. -/
noncomputable def cubeDomainAtlasρ : DomainSectorAtlas d (sumSq (d := d)) (centeredBox d ρ) :=
  ofAll (cubeBlowUpAtlas (d := d) ρ hρ)

theorem cubeDomainAtlasρ_centred :
    (cubeDomainAtlasρ (d := d) hρ).toProductSectorAtlas.IsCentred :=
  fun _ _ => rfl

/-- The blow-up chart `β` as a polynomial map: `y ↦ (y_β, y_β y_γ)`. -/
noncomputable def chartPoly (β j : Fin d) : MvPolynomial (Fin d) ℝ :=
  if j = β then X β else X β * X j

omit [NeZero d] in
theorem eval_chartPoly (β : Fin d) (v : Fin d → ℝ) (j : Fin d) :
    eval v (chartPoly β j) = blowUpChart (fullBlock d) β v j := by
  rw [blowUpChart_fullBlock_apply]
  unfold chartPoly
  split_ifs <;> simp

omit [NeZero d] in
theorem eval_chartPoly_fun (β : Fin d) (v : Fin d → ℝ) :
    (fun j => eval v (chartPoly β j)) = blowUpChart (fullBlock d) β v :=
  funext fun j => eval_chartPoly β v j

omit hP in
theorem priorFactorρ_eq (β : Fin d) :
    (fun v => |(cubeDomainAtlasρ hρ).jacUnit β v| * eval ((cubeDomainAtlasρ hρ).φ β v) P) =
      fun w => eval w (bind₁ (chartPoly β) P) := by
  funext v
  change |(1 : ℝ)| * eval (blowUpChart (fullBlock d) β v) P = _
  rw [abs_one, one_mul, eval_bind₁', eval_chartPoly_fun]

omit hP in
theorem obsFactorρ_eq (β : Fin d) :
    ((fun w => eval w Q) ∘ (cubeDomainAtlasρ hρ).φ β) =
      fun w => eval w (bind₁ (chartPoly β) Q) := by
  funext v
  change eval (blowUpChart (fullBlock d) β v) Q = _
  rw [eval_bind₁', eval_chartPoly_fun]

/-- ★★ **The `ρ`-cube satisfies the centred inputs**: chart boxes of sides `(ρ, 1, …, 1)`,
enclosing boxes of half side `max ρ 1`, polynomial packets by substitution. -/
noncomputable def cubeCentredInputs : CentredInputs d where
  K := sumSq
  K_m := continuous_K.measurable
  Ω := centeredBox d ρ
  A := cubeDomainAtlasρ hρ
  centred := cubeDomainAtlasρ_centred hρ
  a := 1
  ha := one_pos
  a' _ := max ρ 1
  hi_le := fun (β : Fin d) (j : Fin d) => by
    change (if j = β then ρ else 1) ≤ max ρ 1
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  φ_m := fun (β : Fin d) => (continuous_φ β).measurable
  jacUnit_m := fun _ => measurable_const
  hu_cont := fun (β : Fin d) => continuous_unit β
  hu_tan := fun (β : Fin d) w w' h => unit_tan β w w' fun j hj => h j (by
    change ¬ 0 < (if j = β then 1 else 0)
    simp [hj])
  c := fun _ => 1
  hc := fun _ => one_pos
  hu_lb := fun (β : Fin d) w _ => one_le_unit β w
  prior := fun w => eval w P
  obs := fun w => eval w Q
  prior_m := (MvPolynomial.continuous_eval P).measurable
  prior_nonneg := hP
  obs_m := (MvPolynomial.continuous_eval Q).measurable
  obs_int := integrable_of_continuous_of_subset_compact (MvPolynomial.continuous_eval P)
    (MvPolynomial.continuous_eval Q) (isCompact_centeredBox d ρ) subset_rfl
    (isCompact_centeredBox d ρ).isClosed.measurableSet
  P := fun (β : Fin d) => (HolomorphicSignedBoxExtension.ofPolynomials (max ρ 1)
    (bind₁ (chartPoly β) P) (bind₁ (chartPoly β) Q)).congr (priorFactorρ_eq hρ P β)
    (obsFactorρ_eq hρ Q β)
  signs_nonempty := fun _ => Finset.univ_nonempty
  ι_nonempty := ⟨(0 : Fin d)⟩

theorem cubeCentredInputs_W : (cubeCentredInputs hρ P Q hP).A.W = centeredBox d ρ := rfl

/-- ★★ **Regression**: the coordinate-free expansion of `∫_{[−ρ,ρ]^d} Q · P · e^{−n|x|²}` through
the rescaled cube blow-up atlas. -/
theorem cubeρ_hasCoordFreeExpansion :
    (Sheet.normalData (cubeCentredInputs hρ P Q hP).toSheetInputs.SA).HasCoordFreeExpansion
      (cubeCentredInputs hρ P Q hP).toSheetInputs.cert.stratumMeasure
      (cubeCentredInputs hρ P Q hP).toSheetInputs.coeffCert.field
      (spectrumLe (commonQ (cubeCentredInputs hρ P Q hP).toSheetInputs.cert.cores.k)
        (commonD (cubeCentredInputs hρ P Q hP).toSheetInputs.cert.n))
      (centeredBox d ρ) sumSq (fun w => eval w P) (fun w => eval w Q) :=
  (cubeCentredInputs hρ P Q hP).hasCoordFreeExpansion

end SheetAssembly

end Grammar
