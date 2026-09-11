/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ExactNormalTiling
import Grammar.JointAmplitude
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The unconditional expansion of an exact-monomial box integral (Astra #69 B0)

The first **unconditional** endpoint of the geometric bridge, and its integration test: for the
exact monomial phase `β ∏_i u_i^{2k_i}` on the positive box `A × [0,b]^{n+1}` (a compact tangential
base `A` inside the cube `|v_i| ≤ B`, box side `b ≤ B`) and a jointly analytic observable `F`
represented by one power series in the `(t + n + 1)` variables with the margin
`(t+n+1)·B < ρ < R`, the box integral

  `Z(N) = ∫_{A × [0,b]^{n+1}} F(v,u) e^{−Nβ∏ u_i^{2k_i}} dv du`

has the full power–log cutoff expansion with the assembled canonical coefficients
(`monomialBox_cutoffExpansion`). The proof runs the whole bridge: the box is one tiling piece with
the identity chart (Jacobian `1`, exponents `h = 0`), the amplitude datum is the tangential datum of
the joint series (`jointTangentialData`), the faces `u_i = 0` are null so the tail is empty
(`ae_ne_zero_snd`), and `ExactNormalTiling.cutoffExpansion` concludes.

Non-claims: one orthant (the two-sided box needs the reflected pieces); one joint-series centre
(finite covering of the base is the assembly unit's task); no analytic unit in the phase or the
Jacobian (that is the strip-normalised single-chart theorem, B1).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {t n : ℕ}

/-- The exact monomial phase `β ∏_i u_i^{2k_i}` on the product space. -/
def monomialPhase (k : Fin (n + 1) → ℕ) (β : ℝ) (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  β * ∏ i, p.2 i ^ (2 * k i)

theorem monomialPhase_nonneg {k : Fin (n + 1) → ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) : 0 ≤ monomialPhase k β p := by
  unfold monomialPhase
  refine mul_nonneg hβ (Finset.prod_nonneg fun i _ => ?_)
  rw [pow_mul]
  positivity

theorem continuous_monomialPhase (k : Fin (n + 1) → ℕ) (β : ℝ) :
    Continuous (monomialPhase (t := t) k β) :=
  continuous_const.mul (continuous_finsetProd _ fun i _ =>
    ((continuous_apply i).comp continuous_snd).pow _)

/-- The positive box `A × [0,b]^{n+1}`. -/
def posBox (A : Set (Fin t → ℝ)) (b : ℝ) : Set ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) :=
  A ×ˢ piBox (n + 1) (Icc 0 b)

theorem isCompact_posBox {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b : ℝ) :
    IsCompact (posBox (n := n) A b) :=
  hA.prod (isCompact_univ_pi fun _ => isCompact_Icc)

theorem measurableSet_posBox {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b : ℝ) :
    MeasurableSet (posBox (n := n) A b) :=
  hA.isClosed.measurableSet.prod (measurableSet_piBox _ _ measurableSet_Icc)

/-- The localisation datum of the box integral. -/
noncomputable def monomialBoxData (k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β)
    {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b : ℝ) {F : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContinuousOn F (posBox A b)) {δ : ℝ} (hδ : 0 < δ) :
    LocalisationData ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) where
  μ := volume.restrict (posBox A b)
  phase := monomialPhase k β
  obs := F
  phase_measurable := (continuous_monomialPhase k β).measurable
  phase_nonneg := Eventually.of_forall (monomialPhase_nonneg hβ.le)
  obs_integrable := hF.integrableOn_compact (isCompact_posBox hA b)
  δ := δ
  δ_pos := hδ

theorem monomialBoxData_Z (k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β) {A : Set (Fin t → ℝ)}
    (hA : IsCompact A) (b : ℝ) {F : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContinuousOn F (posBox A b)) {δ : ℝ} (hδ : 0 < δ) (N : ℝ) :
    (monomialBoxData k hβ hA b hF hδ).Z N =
      ∫ z in posBox A b, F z * Real.exp (-N * monomialPhase k β z) := rfl

/-- Almost every point of the product space has all normal coordinates nonzero. -/
theorem ae_ne_zero_snd :
    ∀ᵐ z ∂(volume : Measure ((Fin t → ℝ) × (Fin (n + 1) → ℝ))), ∀ i, z.2 i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have h1 : {z : (Fin t → ℝ) × (Fin (n + 1) → ℝ) | ¬ z.2 i ≠ 0} =
      univ ×ˢ {u : Fin (n + 1) → ℝ | u i = 0} := by
    ext z
    simp
  have h2 : volume {u : Fin (n + 1) → ℝ | u i = 0} = 0 := by
    rw [volume_pi]
    exact Measure.pi_hyperplane _ i 0
  rw [h1, Measure.volume_eq_prod, Measure.prod_prod, h2, mul_zero]

/-- **The unconditional expansion of the exact-monomial box integral.** -/
theorem monomialBox_cutoffExpansion (k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {A : Set (Fin t → ℝ)} (hA : IsCompact A) {B b : ℝ} (hb : 0 < b) (hbB : b ≤ B)
    (hB : 0 < B) (hAB : ∀ v ∈ A, ∀ i, |v i| ≤ B) {F : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContinuousOn F (posBox A b)) {P : FormalMultilinearSeries ℝ (Fin t ⊕ Fin (n + 1) → ℝ) ℝ}
    {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall (fun w => F (w ∘ Sum.inl, w ∘ Sum.inr)) P 0 R) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < R) (hBρ : ((t + (n + 1) : ℕ) : ℝ) * B < ρ) (hB1 : B < ρ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
      CutoffExpansion Q Dg (fun N => ∫ z in posBox A b, F z * Real.exp (-N * monomialPhase k β z))
        c := by
  classical
  set D := monomialBoxData k hβ hA b hF hδ with hD
  have : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have hcard : (Fintype.card (Fin t ⊕ Fin (n + 1)) : ℝ) * B < ρ := by
    simpa [Fintype.card_sum] using hBρ
  have hW : Summable (jointWeight P B) :=
    summable_jointWeight P B (summable_monoFamily_mul_pow P (hρ.trans_le hG.r_le) hB.le hcard)
  set x : TangentialData A (n + 1) := jointTangentialData P B hb hbB hB hW A hAB with hx
  -- the positive box chart with the identity chart
  let chart : PositiveBoxChart (D.comapEquiv (MeasurableEquiv.refl _)) A b β :=
    ⟨fun _ => 0, k, hk, id, univ, isOpen_univ, subset_univ _, contDiff_id.contDiffOn,
      injOn_id _, fun _ => 1, measurable_const, fun _ _ => zero_le_one,
      fun p _ => by simp [fderiv_id, ContinuousLinearMap.det],
      fun p _ => rfl, x, fun v => xiCoord_jointTangentialData P B hb hbB hB hW A hAB v,
      fun v u hu => by
        have hu' : ∀ j, |u j| ≤ b := fun j => by
          have := hu j (mem_univ j)
          rw [abs_le]
          constructor <;> linarith [this.1, this.2]
        rw [hx, evalF_toEta_jointTangentialData P B hb hbB hB hW A hAB hG hρ hBρ hB1 v hu',
          one_mul]
        simp only [LocalisationData.comapEquiv_obs, MeasurableEquiv.refl_apply, id, hD,
          monomialBoxData, Sum.elim_comp_inl, Sum.elim_comp_inr]⟩
  let piece : TilingPiece D β :=
    { t := t, n := n, e := MeasurableEquiv.refl _, e_vol := MeasurePreserving.id _, A := A,
      A_compact := hA, b := b, b_pos := hb, chart := chart }
  have himage : piece.image = A ×ˢ piBox (n + 1) (Ioc 0 b) := by
    simp [TilingPiece.image, TilingPiece.box, piece, chart]
  let T : ExactNormalTiling D β :=
    { Ω := posBox A b, μ_eq := rfl, M := 1, piece := fun _ => piece,
      image_subset := fun _ => by
        rw [himage]
        exact prod_mono le_rfl (pi_mono fun _ _ => Ioc_subset_Icc_self),
      aedisjoint := fun I J hIJ => absurd (Subsingleton.elim I J) hIJ,
      δ₀ := 1, δ₀_pos := one_pos,
      gap := by
        have hΩ : MeasurableSet (posBox (n := n) A b) := measurableSet_posBox hA b
        change ∀ᵐ z ∂(volume.restrict (posBox A b)), _
        filter_upwards [ae_restrict_mem hΩ, ae_restrict_of_ae (ae_ne_zero_snd (t := t) (n := n))]
          with z hz hz0 hnot
        exfalso
        refine hnot (mem_iUnion.2 ⟨0, ?_⟩)
        rw [himage]
        exact ⟨hz.1, fun i _ => ⟨lt_of_le_of_ne (hz.2 i (mem_univ i)).1 (hz0 i).symm,
          (hz.2 i (mem_univ i)).2⟩⟩ }
  exact T.cutoffExpansion hβ

end Grammar
