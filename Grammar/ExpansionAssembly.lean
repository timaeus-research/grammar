/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedCoordFreeExpansion

/-!
# Assembly of coordinate-free expansions over finitely many pieces (CCCXL; phase G, unit G4)

Consult #100 §2, §3. Expansions on finitely many pieces `W_e` of a domain `W`, on a common
spectrum, with stratum measures `ν_e` and moment fields `B_e`, assemble into one expansion on `W`:
the stratum measures add (`sumMeasure ν I = ∑_e ν_e I`) and the fields are averaged with the
**Radon–Nikodym weights** `w_e = d ν_e / d(∑ ν_e)` (`glueField ν B (s) = ∑_e w_e(s) • B_e(s)`, a
finite sum in one moment-tensor fibre). The weighted integral identity
`∫ w_e f d(∑ν) = ∫ f dν_e` (`integral_rnWeight_mul`) gives the exact coefficient-sum
specification `C_{∑ν, glue}(φ, q) = ∑_e C_{ν_e, B_e}(φ, q)` (★ `expansionCoefficient_glue`) under
pointwise summability of the normal-order series and integrability of its sums (consult #100:
`tsum` is totalised, so both are genuine hypotheses), and with the additivity of the Laplace
integral over the pieces the expansions assemble (★★ `HasCoordFreeExpansion.sum`: a finite sum of
`IsLittleO`s). The measures are finite and any a.e. property common to the pieces holds for the
sum (`ae_sumMeasure_of_forall`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [MeasurableSpace U] {R : ResolvedGeometry d U}
  {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] (D : ResolvedNormalData R A)
  {ι : Type*} [Fintype ι]

namespace ResolvedNormalData

variable (ν : ι → ∀ I : Finset R.Component, Measure (R.Stratum I))

/-- **The summed stratum measures** `∑_e ν_e`. -/
noncomputable def sumMeasure : ∀ I : Finset R.Component, Measure (R.Stratum I) := fun I =>
  ∑ e, ν e I

omit D in
theorem le_sumMeasure (e : ι) (I : Finset R.Component) : ν e I ≤ sumMeasure ν I :=
  Finset.single_le_sum (f := fun e => ν e I) (fun _ _ => Measure.zero_le _) (Finset.mem_univ e)

omit D in
theorem isFiniteMeasure_sumMeasure [∀ e I, IsFiniteMeasure (ν e I)] (I : Finset R.Component) :
    IsFiniteMeasure (sumMeasure ν I) := by
  refine ⟨?_⟩
  unfold sumMeasure
  rw [Measure.finsetSum_apply]
  exact ENNReal.sum_lt_top.2 fun e _ => measure_lt_top _ _

omit D in
/-- An a.e. property common to all pieces holds for the sum. -/
theorem ae_sumMeasure_of_forall (I : Finset R.Component) {P : R.Stratum I → Prop}
    (hP : MeasurableSet {s | P s}) (h : ∀ e, ∀ᵐ (s : R.Stratum I) ∂ν e I, P s) :
    ∀ᵐ (s : R.Stratum I) ∂sumMeasure ν I, P s := by
  unfold sumMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff' hP]
  exact h

omit D in
theorem absolutelyContinuous_sumMeasure (e : ι) (I : Finset R.Component) :
    ν e I ≪ sumMeasure ν I :=
  Measure.absolutelyContinuous_of_le (le_sumMeasure ν e I)

/-- **The Radon–Nikodym weight** `w_e = d ν_e / d(∑ ν_e)` (real-valued). -/
noncomputable def rnWeight (e : ι) (I : Finset R.Component) (s : R.Stratum I) : ℝ :=
  ((ν e I).rnDeriv (sumMeasure ν I) s).toReal

/-- **The glued moment field** `∑_e w_e • B_e`. -/
noncomputable def glueField (B : ι → D.MomentCoefficientField) : D.MomentCoefficientField :=
  fun I r q s => ∑ e, rnWeight ν e I s • B e I r q s

variable [∀ e I, IsFiniteMeasure (ν e I)]

omit D in
/-- ★ The weighted integral identity `∫ w_e f d(∑ν) = ∫ f dν_e`. -/
theorem integral_rnWeight_mul (e : ι) (I : Finset R.Component) (f : R.Stratum I → ℝ) :
    ∫ s, rnWeight ν e I s * f s ∂sumMeasure ν I = ∫ s, f s ∂ν e I := by
  have := isFiniteMeasure_sumMeasure ν I
  have h := integral_rnDeriv_smul (absolutelyContinuous_sumMeasure ν e I) (f := f)
  simp only [smul_eq_mul] at h
  exact h

omit D in
theorem integrable_rnWeight_mul (e : ι) (I : Finset R.Component) (f : R.Stratum I → ℝ)
    (hf : Integrable f (ν e I)) :
    Integrable (fun s => rnWeight ν e I s * f s) (sumMeasure ν I) := by
  have := isFiniteMeasure_sumMeasure ν I
  have h := (integrable_rnDeriv_smul_iff (absolutelyContinuous_sumMeasure ν e I) (f := f)).2 hf
  simpa [rnWeight, smul_eq_mul] using h

/-- ★ **The coefficient-sum specification**: the expansion coefficients of the glued data are the
sums of the coefficients of the pieces. -/
theorem expansionCoefficient_glue (B : ι → D.MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ)
    (q : PowerLogIndex)
    (hsum : ∀ (e : ι) (I : Finset R.Component) (s : R.Stratum I), Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r))
    (hint : ∀ (e : ι) (I : Finset R.Component), Integrable (fun s => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r)) (ν e I)) :
    D.expansionCoefficient (sumMeasure ν) (D.glueField ν B) φ q =
      ∑ e, D.expansionCoefficient (ν e) (B e) φ q := by
  unfold ResolvedNormalData.expansionCoefficient
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hpt : ∀ s : R.Stratum I, (∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
      (D.glueField ν B I r q s).pair (D.normalDifferential φ I s r)) =
      ∑ e, rnWeight ν e I s * ∑' r : ℕ,
        (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r) := by
    intro s
    have hterm : ∀ r : ℕ, (r.factorial : ℝ)⁻¹ *
        (D.glueField ν B I r q s).pair (D.normalDifferential φ I s r) =
        ∑ e, rnWeight ν e I s *
          ((r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r)) := by
      intro r
      unfold ResolvedNormalData.glueField MomentTensor.pair
      rw [sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [smul_apply, smul_eq_mul]
      ring
    rw [tsum_congr hterm, Summable.tsum_finsetSum]
    · exact Finset.sum_congr rfl fun e _ => tsum_mul_left
    · exact fun e _ => (hsum e I s).mul_left _
  simp_rw [hpt]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun e _ => integral_rnWeight_mul ν e I _
  · exact fun e _ => integrable_rnWeight_mul ν e I _ (hint e I)

/-- ★★ **Assembly of expansions over finitely many pieces**: expansions on pieces `W_e` on a
common spectrum, whose Laplace integrals add up to that of `W`, assemble into the expansion on
`W` with the summed stratum measures and the Radon–Nikodym-glued field. -/
theorem HasCoordFreeExpansion.sum (B : ι → D.MomentCoefficientField)
    (spec : ℝ → Finset PowerLogIndex) (W : Set (Fin d → ℝ)) (We : ι → Set (Fin d → ℝ))
    (K ϕ φ : (Fin d → ℝ) → ℝ)
    (hL : ∀ n : ℝ, globalLaplace W K (fun w => φ w * ϕ w) n =
      ∑ e, globalLaplace (We e) K (fun w => φ w * ϕ w) n)
    (hsum : ∀ (e : ι) (I : Finset R.Component) (s : R.Stratum I) (q : PowerLogIndex),
      Summable fun r : ℕ =>
        (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r))
    (hint : ∀ (e : ι) (I : Finset R.Component) (q : PowerLogIndex), Integrable (fun s => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (B e I r q s).pair (D.normalDifferential φ I s r)) (ν e I))
    (h : ∀ e, D.HasCoordFreeExpansion (ν e) (B e) spec (We e) K ϕ φ) :
    D.HasCoordFreeExpansion (sumMeasure ν) (D.glueField ν B) spec W K ϕ φ := by
  intro A
  have hcoef : ∀ q, D.expansionCoefficient (sumMeasure ν) (D.glueField ν B) φ q =
      ∑ e, D.expansionCoefficient (ν e) (B e) φ q := fun q =>
    D.expansionCoefficient_glue ν B φ q (fun e I s => hsum e I s q) (fun e I => hint e I q)
  have heq : (fun n : ℝ => globalLaplace W K (fun w => φ w * ϕ w) n -
      ∑ q ∈ spec A, D.expansionCoefficient (sumMeasure ν) (D.glueField ν B) φ q * q.scale n) =
      ∑ e, fun n : ℝ => globalLaplace (We e) K (fun w => φ w * ϕ w) n -
        ∑ q ∈ spec A, D.expansionCoefficient (ν e) (B e) φ q * q.scale n := by
    funext n
    rw [Finset.sum_apply, hL n, Finset.sum_sub_distrib]
    congr 1
    simp only [hcoef, Finset.sum_mul]
    exact Finset.sum_comm
  rw [heq]
  exact IsLittleO.sum fun e _ => h e A

end ResolvedNormalData

end Grammar
