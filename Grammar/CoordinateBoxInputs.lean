/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxCertificate

/-!
# Public inputs of the compact-box producer (CCCXXV)

Consult #97 §1.2 and §1.4: two adapters that turn the collar-adapted interface of CCCXXIV into
paper-facing hypotheses.

* **Original-variable face series.** `OriginalFaceSeries I` carries uniform series families for
  the prior and the observable over the CLOSED FACE `X_I = {w ∈ [0,a]^d : w_i = 0, i ∈ I}` in the
  ORIGINAL normal variables `z` (the insertion `Ψ_I(s,z) = s + Σ_i z_i e_{σ i}`,
  `originalNormalMap`) at a radius `ρ_I`, with the evaluation identities on the open normal ball.
  Under the smallness condition `2 δ^{1/(2k_i d)} < ρ_I` (`i ∈ I`) the water-filling widths satisfy
  `λ_{I,i}(s) ≤ L_i := δ^{1/(2k_i d)}/b_I` with `2 b_I L_i = 2δ^{1/(2k_i d)}`, so restriction to the
  collar base (`UniformSeriesFamily.precomp`) and rescaling (`UniformSeriesFamily.rescale`) produce
  the collar-base series `FaceSeries` of CCCXXIV (`OriginalFaceSeries.toFaceSeries`), and the
  expansion follows (`hasCoordFreeExpansion_collar_of_face`).
* **Box-local nonnegativity.** For a prior nonnegative only on the box, the positive part
  `ϕ⁺ = max ϕ 0` is globally nonnegative, agrees with `ϕ` on `[0,a]^d`, defines the same
  prior-weighted measure, has the same collar-base series and the same observable; hence the
  coordinate-free expansion of `∫_{[0,a]^d} φ ϕ e^{−nK}` holds with the certificate of `ϕ⁺`
  (`hasCoordFreeExpansion_collar_of_nonneg_on`), stated precisely with that certificate.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace UniformSeriesFamily

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {d : ℕ} {b' : ℝ}

/-- Pulling a uniform family back along a continuous map of parameter spaces. -/
def precomp (F : UniformSeriesFamily X d b') (g : Y → X) (hg : Continuous g) :
    UniformSeriesFamily Y d b' where
  f y := F.f (g y)
  M := F.M
  continuous_coeff γ := (F.continuous_coeff γ).comp hg
  abs_le y γ := F.abs_le (g y) γ
  M_abs := F.M_abs

theorem precomp_f (F : UniformSeriesFamily X d b') (g : Y → X) (hg : Continuous g) (y : Y) :
    (F.precomp g hg).f y = F.f (g y) := rfl

end UniformSeriesFamily

namespace WaterFilling

open NormalisedBox CoeffFamily CoordModel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ)

/-! ### Original-variable face series -/

omit k hk δ in
/-- The closed coordinate face `X_I = {w ∈ [0,a]^d : w_i = 0 for i ∈ I}`. -/
def faceSet (I : Finset (Fin d)) : Set (Fin d → ℝ) :=
  {w | w ∈ piBox d (Icc 0 a) ∧ ∀ i ∈ I, w i = 0}

omit k hk a δ in
/-- The insertion of original normal coordinates: `Ψ_I(s, z) = s + Σ_i z_i e_{σ i}`. -/
noncomputable def originalNormalMap (I : NonemptyIdx d) (s : Fin d → ℝ) (z : Fin (nI I + 1) → ℝ) :
    Fin d → ℝ :=
  fun j => if h : j ∈ I.1 then s j + z ((σI I).symm ⟨j, h⟩) else s j

variable (ϕ φ : (Fin d → ℝ) → ℝ)

omit k hk δ in
/-- Uniform normal-series families for the prior and the observable over the closed face, in the
original normal variables, at a radius `ρ`. -/
structure OriginalFaceSeries (I : NonemptyIdx d) where
  /-- the normal radius -/
  ρ : ℝ
  hρ : 0 < ρ
  Fϕ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
  Fφ : UniformSeriesFamily (↥(faceSet a I.1)) (nI I + 1) ρ
  hϕ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
    ϕ (originalNormalMap I s.1 z) = evalF (Fϕ.f s) z
  hφ_eq : ∀ (s : ↥(faceSet a I.1)) (z : Fin (nI I + 1) → ℝ), ‖z‖ < ρ →
    φ (originalNormalMap I s.1 z) = evalF (Fφ.f s) z

/-- A collar base point lies on the closed face. -/
theorem mem_faceSet_of_KI (ha : 0 < a) (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    s.1.1 ∈ faceSet a I.1 := by
  refine ⟨?_, fun i hi => stratum_coord_zero k hk s.1 hi⟩
  rw [piBox, mem_univ_pi]
  intro j
  by_cases hj : j ∈ I.1
  · rw [stratum_coord_zero k hk s.1 hj]
    exact ⟨le_rfl, ha.le⟩
  · exact ⟨(s.2 ⟨j, hj⟩).1, (s.2 ⟨j, hj⟩).2.1⟩

/-- The restriction of a collar base point to the closed face. -/
def toFace (ha : 0 < a) (I : NonemptyIdx d) (s : KI k hk a δ I.1) : ↥(faceSet a I.1) :=
  ⟨s.1.1, mem_faceSet_of_KI k hk a δ ha I s⟩

theorem continuous_toFace (ha : 0 < a) (I : NonemptyIdx d) : Continuous (toFace k hk a δ ha I) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The water-filling widths in box coordinates. -/
noncomputable def widths (I : NonemptyIdx d) (s : KI k hk a δ I.1) (i : Fin (nI I + 1)) : ℝ :=
  lamT k I.1 δ (eI k hk a δ I.1 s) (σI I i)

omit hk a in
/-- The uniform bound `L_i = δ^{1/(2k_i d)} / b_I` on the widths. -/
noncomputable def widthBound (I : NonemptyIdx d) (i : Fin (nI I + 1)) : ℝ :=
  δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) / side k I.1 δ

theorem continuous_widths (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    Continuous fun s => widths k hk a δ I s i :=
  (continuous_apply _).comp ((continuousOn_lamT k I.1 a δ hk I.2 hδ).comp_continuous
    (continuous_eI k hk a δ I.1) fun s => s.2)

theorem widths_pos (hδ : 0 < δ) (I : NonemptyIdx d) (s : KI k hk a δ I.1) (i : Fin (nI I + 1)) :
    0 < widths k hk a δ I s i :=
  lamT_pos_of_mem_baseSet k I.1 a δ hk I.2 hδ s.2 _

omit hk a in
theorem widthBound_pos (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    0 < widthBound k δ I i :=
  div_pos (Real.rpow_pos_of_pos hδ _) (side_pos k I.1 δ hδ)

/-- `λ_{I,i}(s) ≤ L_i` on the collar base. -/
theorem abs_widths_le (hδ : 0 < δ) (hd : 0 < d) (I : NonemptyIdx d) (s : KI k hk a δ I.1)
    (i : Fin (nI I + 1)) : |widths k hk a δ I s i| ≤ widthBound k δ I i := by
  rw [abs_of_pos (widths_pos k hk a δ hδ I s i), widths, widthBound, lamT]
  refine div_le_div_of_nonneg_right ?_ (side_pos k I.1 δ hδ).le
  rw [ell, Real.rpow_mul hδ.le]
  exact Real.rpow_le_rpow (q_nonneg k I.1 δ _ hδ.le)
    (q_le_rpow k I.1 a δ hk I.2 hδ hd s.2) (by positivity)

omit hk a in
/-- The rescaled radius: `L_i · 2 b_I = 2 δ^{1/(2k_i d)}`. -/
theorem widthBound_mul (hδ : 0 < δ) (I : NonemptyIdx d) (i : Fin (nI I + 1)) :
    widthBound k δ I i * (2 * side k I.1 δ) =
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) := by
  have hs := (side_pos k I.1 δ hδ).ne'
  rw [widthBound]
  field_simp

/-- The core parametrisation in original normal coordinates: `Φ(s, v) = Ψ_I(s, λ(s)·v)`. -/
theorem Φ_eq_originalNormalMap (I : NonemptyIdx d) (s : KI k hk a δ I.1)
    (v : Fin (nI I + 1) → ℝ) :
    Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v) =
      originalNormalMap I s.1.1 fun i => widths k hk a δ I s i * v i := by
  funext j
  rw [Φ_apply, originalNormalMap]
  by_cases hj : j ∈ I.1
  · rw [dif_pos hj, dif_pos hj, stratum_coord_zero k hk s.1 hj, zero_add, widths,
      Equiv.apply_symm_apply]
  · rw [dif_neg hj, dif_neg hj]
    rfl

variable {ϕ φ}

/-- The rescaled displacement lies in the original normal ball. -/
theorem norm_widths_mul_lt (hδ : 0 < δ) (hd : 0 < d) (I : NonemptyIdx d) {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ∀ i : Fin (nI I + 1), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < ρ)
    (s : KI k hk a δ I.1) {v : Fin (nI I + 1) → ℝ} (hv : ‖v‖ < 2 * side k I.1 δ) :
    ‖fun i => widths k hk a δ I s i * v i‖ < ρ := by
  rw [pi_norm_lt_iff hρ]
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  have hvi : |v i| < 2 * side k I.1 δ := by
    have := (pi_norm_lt_iff (by linarith [side_pos k I.1 δ hδ])).1 hv i
    rwa [Real.norm_eq_abs] at this
  calc |widths k hk a δ I s i| * |v i|
      ≤ widthBound k δ I i * (2 * side k I.1 δ) :=
        mul_le_mul (abs_widths_le k hk a δ hδ hd I s i) hvi.le (abs_nonneg _)
          (widthBound_pos k δ hδ I i).le
    _ = 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) := widthBound_mul k δ hδ I i
    _ < ρ := hsmall i

/-- ★ **The original-face adapter**: restriction to the collar base and rescaling by the widths turn
face series in the original normal variables into the collar-base series of CCCXXIV. -/
noncomputable def OriginalFaceSeries.toFaceSeries {I : NonemptyIdx d}
    (O : OriginalFaceSeries a ϕ φ I) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
    (hsmall : ∀ i : Fin (nI I + 1), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < O.ρ) :
    FaceSeries k hk a δ ϕ φ I where
  Fϕ := (O.Fϕ.precomp (toFace k hk a δ ha I) (continuous_toFace k hk a δ ha I)).rescale
    (widths k hk a δ I) (continuous_widths k hk a δ hδ I) (widthBound k δ I)
    (abs_widths_le k hk a δ hδ hd I) (fun i => (widthBound_pos k δ hδ I i).le)
    (by linarith [side_pos k I.1 δ hδ]) fun i => by
      rw [widthBound_mul k δ hδ I i]
      exact (hsmall i).le
  Fφ := (O.Fφ.precomp (toFace k hk a δ ha I) (continuous_toFace k hk a δ ha I)).rescale
    (widths k hk a δ I) (continuous_widths k hk a δ hδ I) (widthBound k δ I)
    (abs_widths_le k hk a δ hδ hd I) (fun i => (widthBound_pos k δ hδ I i).le)
    (by linarith [side_pos k I.1 δ hδ]) fun i => by
      rw [widthBound_mul k δ hδ I i]
      exact (hsmall i).le
  hϕ_eq := fun s v hv => by
    have hv' : ‖v‖ < 2 * side k I.1 δ := by
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (side_pos k I.1 δ hδ).le).2 fun i => ?_)
        (by linarith [side_pos k I.1 δ hδ])
      have := hv i (mem_univ _)
      rw [mem_Ioc] at this
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith, this.2⟩
    exact (congrArg ϕ (Φ_eq_originalNormalMap k hk a δ I s v)).trans
      ((O.hϕ_eq (toFace k hk a δ ha I s) _
        (norm_widths_mul_lt k hk a δ hδ hd I O.hρ hsmall s hv')).trans
        (evalF_rescale (widths k hk a δ I s) (O.Fϕ.f (toFace k hk a δ ha I s)) v).symm)
  hφ_eq := fun s v hv => by
    exact (congrArg φ (Φ_eq_originalNormalMap k hk a δ I s v)).trans
      ((O.hφ_eq (toFace k hk a δ ha I s) _
        (norm_widths_mul_lt k hk a δ hδ hd I O.hρ hsmall s hv)).trans
        (evalF_rescale (widths k hk a δ I s) (O.Fφ.f (toFace k hk a δ ha I s)) v).symm)

variable (hϕm : Measurable ϕ) (hφm : Measurable φ)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
  (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))

include hφm in
/-- ★★★ **The compact-box expansion from original-variable face series** (globally nonnegative
prior): with radii `ρ_I` and `2 δ^{1/(2k_i d)} < ρ_I`. -/
theorem hasCoordFreeExpansion_collar_of_face (hϕ0 : ∀ w, 0 ≤ ϕ w)
    (O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I)
    (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (O I).ρ) :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).stratumMeasure
      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).field
      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa
        fun I => (O I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).cores.k) (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=
  hasCoordFreeExpansion_collar' k hk a δ hδ ϕ φ hϕm hϕ0 hφm hφint hd ha hδa _

/-! ### Box-local nonnegativity -/

omit k hk a δ in
/-- The positive part of the prior. -/
def posPart (ϕ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun w => max (ϕ w) 0

omit k hk a δ in
theorem posPart_nonneg (ϕ : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : 0 ≤ posPart ϕ w :=
  le_max_right _ _

omit k hk a δ in
theorem measurable_posPart (hϕm : Measurable ϕ) : Measurable (posPart ϕ) :=
  hϕm.max measurable_const

omit k hk δ in
theorem posPart_eq_of_mem (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc 0 a)) : posPart ϕ w = ϕ w :=
  max_eq_left (hϕ0W w hw)

omit k hk δ in
/-- The prior-weighted measures of `ϕ` and `ϕ⁺` on the box coincide. -/
theorem withDensity_posPart (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) :
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (posPart ϕ w)) =
      (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w) := by
  refine withDensity_congr_ae ((ae_restrict_iff' (measurableSet_W a)).2
    (Eventually.of_forall fun w hw => ?_))
  change ENNReal.ofReal (posPart ϕ w) = ENNReal.ofReal (ϕ w)
  rw [posPart_eq_of_mem a hϕ0W hw]

/-- The collar-base series of `ϕ` are collar-base series of `ϕ⁺`. -/
noncomputable def FaceSeries.toPosPart {I : NonemptyIdx d} (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
    (F : FaceSeries k hk a δ ϕ φ I) : FaceSeries k hk a δ (posPart ϕ) φ I where
  Fϕ := F.Fϕ
  Fφ := F.Fφ
  hϕ_eq := fun s v hv => by
    rw [posPart_eq_of_mem a hϕ0W (image_subset_box k I.1 a δ (eI k hk a δ I.1)
      (range_eI k hk a δ I.1 I.2 hδ) hδ hk I.2 hd ha hδa (mem_image_Φ I.1 (σI I) (eI k hk a δ I.1)
        (lamT k I.1 δ) (fun t ht j => lamT_pos_of_mem_baseSet k I.1 a δ hk I.2 hδ
          ((range_eI k hk a δ I.1 I.2 hδ) ▸ ht) j) s hv))]
    exact F.hϕ_eq s v hv
  hφ_eq := F.hφ_eq

omit k hk δ in
theorem globalLaplace_congr_on {K a' a'' : (Fin d → ℝ) → ℝ}
    (h : ∀ w ∈ piBox d (Icc 0 a), a' w = a'' w) (N : ℝ) :
    globalLaplace (piBox d (Icc 0 a)) K a' N = globalLaplace (piBox d (Icc 0 a)) K a'' N := by
  unfold globalLaplace
  exact setIntegral_congr_fun (measurableSet_W a) fun w hw => by simp only [h w hw]

/-- Integrability of the observable against the positive-part weight, as a named theorem: a
`▸`-cast in a certificate argument makes the kernel reduce the equality proof when two statements
are compared, so certificate statements use this constant instead. -/
theorem integrable_posPart (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
    (hint : Integrable φ
      ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w))) :
    Integrable φ
      ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (posPart ϕ w)) :=
  (withDensity_posPart a hϕ0W).symm ▸ hint

include hφm in
/-- ★★★ **The compact-box expansion for a prior nonnegative on the box**: the expansion of
`∫_{[0,a]^d} φ ϕ e^{−nK}` holds with the certificate and coefficient field of the positive part
`ϕ⁺`, which agrees with `ϕ` on the box. -/
theorem hasCoordFreeExpansion_collar_of_nonneg_on (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
    (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I) :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
        (integrable_posPart a hϕ0W hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).stratumMeasure
      (coeffCertificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm) (posPart_nonneg ϕ)
        (integrable_posPart a hϕ0W hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).field
      (spectrumLe (commonQ (certificate k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
        (posPart_nonneg ϕ) (integrable_posPart a hϕ0W hφint) hd ha hδa
        fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W).cores.k) (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  have h := hasCoordFreeExpansion_collar' k hk a δ hδ (posPart ϕ) φ (measurable_posPart hϕm)
    (posPart_nonneg ϕ) hφm (integrable_posPart a hϕ0W hφint) hd ha hδa
    fun I => (F I).toPosPart k hk a δ hδ hd ha hδa hϕ0W
  intro A
  have hA := h A
  refine hA.congr_left fun n => ?_
  rw [globalLaplace_congr_on a (a' := fun w => φ w * posPart ϕ w) (a'' := fun w => φ w * ϕ w)
    (fun w hw => by rw [posPart_eq_of_mem a hϕ0W hw])]

end WaterFilling

end Grammar
