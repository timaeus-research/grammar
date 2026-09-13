/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.OrthantReflection
import Grammar.LocalAnalyticInputs

/-!
# Signed boxes: sign patterns, reflections, the signed analytic packet (CCCXXXVI; phase G, G1)

Consult #100 §1, §5. The signed box `[−a,a]^d` is covered by the `2^d` reflected copies
`R_σ [0,a]^d` of the positive box, `R_σ(w)_i = σ_i w_i` (`refl σ`, built on `signReflect`). This
unit provides the sign patterns `CoordSign d = Fin d → Bool`, the real and complex reflections and
their basic identities (involution, measurability, Lebesgue invariance `map_refl_volume`,
evenness of the monomial phase `phase_refl`, `complexify_refl`), the orthant pieces
`orthantBox σ a = R_σ⁻¹ [0,a]^d` of the signed box, the reflection as a measurable equivalence, and
the set-integral change of variables `setIntegral_refl`, the **signed analytic packet**
`HolomorphicSignedBoxExtension a ϕ φ` (the packet of CCCXXX over the signed box) with its pullbacks
`A.pullback σ : HolomorphicBoxExtension a (ϕ ∘ R_σ) (φ ∘ R_σ)` along the complex reflection, and the
selection of one collar level for finitely many radii (`exists_delta_common`) together with the
at-level form of the local-input theorem (`hasCoordFreeExpansion_local_at`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ}

/-! ### Sign patterns and reflections -/

/-- A sign pattern on the coordinates. -/
abbrev CoordSign (d : ℕ) := Fin d → Bool

/-- The sign vector `±1` of a pattern. -/
def sgn (σ : CoordSign d) : Fin d → ℝ := fun i => if σ i then 1 else -1

theorem abs_sgn (σ : CoordSign d) (i : Fin d) : |sgn σ i| = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem sq_sgn (σ : CoordSign d) (i : Fin d) : sgn σ i ^ 2 = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem sgn_mul_self (σ : CoordSign d) (i : Fin d) : sgn σ i * sgn σ i = 1 := by
  rw [← sq, sq_sgn]

theorem sgn_ne_zero (σ : CoordSign d) (i : Fin d) : sgn σ i ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num

/-- The reflection `R_σ (w)_i = σ_i w_i`. -/
def refl (σ : CoordSign d) : (Fin d → ℝ) → (Fin d → ℝ) := signReflect (sgn σ)

theorem refl_apply (σ : CoordSign d) (w : Fin d → ℝ) (i : Fin d) : refl σ w i = sgn σ i * w i :=
  rfl

theorem refl_refl (σ : CoordSign d) (w : Fin d → ℝ) : refl σ (refl σ w) = w :=
  signReflect_signReflect (abs_sgn σ) w

theorem refl_involutive (σ : CoordSign d) : Function.Involutive (refl σ) := refl_refl σ

theorem measurable_refl (σ : CoordSign d) : Measurable (refl σ) := measurable_signReflect _

theorem continuous_refl (σ : CoordSign d) : Continuous (refl σ) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem map_refl_volume (σ : CoordSign d) : (volume : Measure (Fin d → ℝ)).map (refl σ) = volume :=
  map_signReflect_volume (abs_sgn σ)

/-- The monomial phase is even in every coordinate. -/
theorem phase_refl (k : Fin d → ℕ) (σ : CoordSign d) (w : Fin d → ℝ) :
    phase d k (refl σ w) = phase d k w := by
  unfold phase
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [refl_apply, mul_pow, pow_mul, sq_sgn, one_pow, one_mul]

/-- The reflection as a measurable equivalence. -/
def reflEquiv (σ : CoordSign d) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  MeasurableEquiv.ofInvolutive (refl σ) (refl_involutive σ) (measurable_refl σ)

theorem reflEquiv_apply (σ : CoordSign d) (w : Fin d → ℝ) : reflEquiv σ w = refl σ w := rfl

theorem map_reflEquiv_volume (σ : CoordSign d) :
    (volume : Measure (Fin d → ℝ)).map (reflEquiv σ) = volume :=
  map_refl_volume σ

/-- **Change of variables along a reflection**: `∫_S f = ∫_{R_σ⁻¹ S} f ∘ R_σ`. -/
theorem setIntegral_refl (σ : CoordSign d) (f : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) :
    ∫ w in S, f w = ∫ w in refl σ ⁻¹' S, f (refl σ w) := by
  conv_lhs => rw [← map_reflEquiv_volume σ]
  exact setIntegral_map_equiv (reflEquiv σ) f S

/-! ### Boxes -/

/-- The orthant piece `R_σ⁻¹ [0,a]^d` of the signed box. -/
def orthantBox (σ : CoordSign d) (a : ℝ) : Set (Fin d → ℝ) := refl σ ⁻¹' piBox d (Icc 0 a)

theorem mem_orthantBox {σ : CoordSign d} {a : ℝ} {w : Fin d → ℝ} :
    w ∈ orthantBox σ a ↔ ∀ i, 0 ≤ sgn σ i * w i ∧ sgn σ i * w i ≤ a := by
  unfold orthantBox piBox
  simp only [mem_preimage, Set.mem_univ_pi, mem_Icc, refl_apply]

theorem measurableSet_orthantBox (σ : CoordSign d) (a : ℝ) : MeasurableSet (orthantBox σ a) :=
  (measurableSet_W a).preimage (measurable_refl σ)

theorem orthantBox_subset (σ : CoordSign d) (a : ℝ) : orthantBox σ a ⊆ piBox d (Icc (-a) a) := by
  intro w hw i _
  obtain ⟨h0, h1⟩ := mem_orthantBox.1 hw i
  have h : |w i| ≤ a := by
    rw [← abs_of_nonneg h0, abs_mul, abs_sgn, one_mul] at h1
    exact h1
  exact abs_le.1 h

theorem refl_mem_signedBox {σ : CoordSign d} {a : ℝ} {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 a)) :
    refl σ w ∈ piBox d (Icc (-a) a) :=
  orthantBox_subset σ a (by
    change refl σ (refl σ w) ∈ piBox d (Icc 0 a)
    rwa [refl_refl])

/-- The sign pattern of a point. -/
noncomputable def signOf (w : Fin d → ℝ) : CoordSign d := fun i => decide (0 ≤ w i)

theorem sgn_signOf_mul_nonneg (w : Fin d → ℝ) (i : Fin d) : 0 ≤ sgn (signOf w) i * w i := by
  unfold sgn signOf
  by_cases h : 0 ≤ w i
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, if_false, neg_one_mul]
    linarith

theorem sgn_signOf_mul_eq_abs (w : Fin d → ℝ) (i : Fin d) : sgn (signOf w) i * w i = |w i| := by
  unfold sgn signOf
  by_cases h : 0 ≤ w i
  · simp [h, abs_of_nonneg h]
  · simp only [h, decide_false, Bool.false_eq_true, if_false, neg_one_mul]
    rw [abs_of_neg (not_le.1 h)]

/-- Every point of the signed box lies in the orthant piece of its own sign pattern. -/
theorem mem_orthantBox_signOf {a : ℝ} {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc (-a) a)) :
    w ∈ orthantBox (signOf w) a := by
  rw [mem_orthantBox]
  intro i
  rw [sgn_signOf_mul_eq_abs]
  exact ⟨abs_nonneg _, abs_le.2 (hw i (mem_univ i))⟩

theorem signedBox_eq_iUnion (a : ℝ) : piBox d (Icc (-a) a) = ⋃ σ : CoordSign d, orthantBox σ a := by
  ext w
  constructor
  · intro hw
    exact mem_iUnion.2 ⟨signOf w, mem_orthantBox_signOf hw⟩
  · intro hw
    obtain ⟨σ, hσ⟩ := mem_iUnion.1 hw
    exact orthantBox_subset σ a hσ

/-- Off the coordinate hyperplanes the orthant pieces are disjoint: a point with all coordinates
nonzero lies in `orthantBox σ a` only for `σ = signOf w`. -/
theorem eq_signOf_of_mem_orthantBox {σ : CoordSign d} {a : ℝ} {w : Fin d → ℝ}
    (hw : ∀ i, w i ≠ 0) (h : w ∈ orthantBox σ a) : σ = signOf w := by
  funext i
  have h0 := (mem_orthantBox.1 h i).1
  unfold signOf
  unfold sgn at h0
  by_cases hs : σ i
  · rw [hs] at h0 ⊢
    simp only [if_true, one_mul] at h0
    simp [h0]
  · simp only [hs, Bool.false_eq_true, if_false, neg_one_mul] at h0
    have : w i < 0 := lt_of_le_of_ne (by linarith) (hw i)
    simp [hs, not_le.2 this]

/-! ### Complex reflections and the signed packet -/

/-- The complex reflection. -/
def reflC (σ : CoordSign d) : (Fin d → ℂ) → (Fin d → ℂ) := fun z i => (sgn σ i : ℂ) * z i

theorem complexify_refl (σ : CoordSign d) (w : Fin d → ℝ) :
    complexify (refl σ w) = reflC σ (complexify w) := by
  funext i
  change ((sgn σ i * w i : ℝ) : ℂ) = (sgn σ i : ℂ) * (w i : ℂ)
  push_cast
  rfl

theorem continuous_reflC (σ : CoordSign d) : Continuous (reflC σ) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem differentiable_reflC (σ : CoordSign d) : Differentiable ℂ (reflC σ) :=
  differentiable_pi.2 fun i => (differentiable_const _).mul (differentiable_apply i)

variable (a : ℝ)

/-- **The signed analytic packet**: holomorphic extensions of the prior and the observable on a
complex neighbourhood of the signed box `[−a,a]^d`, agreeing with them (as real parts) on its real
slice. (Same convention as `HolomorphicBoxExtension`: real parts of holomorphic representatives.) -/
structure HolomorphicSignedBoxExtension (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the complex neighbourhood -/
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc (-a) a), complexify w ∈ Ω
  /-- the holomorphic extensions -/
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re

namespace HolomorphicSignedBoxExtension

variable {a} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension a ϕ φ)

/-- ★ **Pullback along a reflection**: the packet of `(ϕ ∘ R_σ, φ ∘ R_σ)` over the positive box, on
`R_σ⁻¹ Ω` with the extensions `H ∘ R_σ`. -/
def pullback (σ : CoordSign d) : HolomorphicBoxExtension a (ϕ ∘ refl σ) (φ ∘ refl σ) where
  Ω := reflC σ ⁻¹' A.Ω
  isOpen_Ω := A.isOpen_Ω.preimage (continuous_reflC σ)
  box_subset := fun w hw => by
    rw [mem_preimage, ← complexify_refl]
    exact A.box_subset _ (refl_mem_signedBox hw)
  Hϕ := A.Hϕ ∘ reflC σ
  Hφ := A.Hφ ∘ reflC σ
  holϕ := A.holϕ.comp (differentiable_reflC σ).differentiableOn (mapsTo_preimage _ _)
  holφ := A.holφ.comp (differentiable_reflC σ).differentiableOn (mapsTo_preimage _ _)
  eqϕ := fun w hw => by
    have hw' : complexify (refl σ w) ∈ A.Ω := by rwa [complexify_refl]
    simpa [Function.comp, complexify_refl] using A.eqϕ (refl σ w) hw'
  eqφ := fun w hw => by
    have hw' : complexify (refl σ w) ∈ A.Ω := by rwa [complexify_refl]
    simpa [Function.comp, complexify_refl] using A.eqφ (refl σ w) hw'

theorem pullback_nonneg (hϕ0 : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ ϕ w) (σ : CoordSign d) :
    ∀ w ∈ piBox d (Icc 0 a), 0 ≤ (ϕ ∘ refl σ) w :=
  fun _ hw => hϕ0 _ (refl_mem_signedBox hw)

end HolomorphicSignedBoxExtension

/-! ### One collar level for finitely many radii, and the at-level local theorem -/

variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hd : 0 < d) (ha : 0 < a)

include hk hd ha in
/-- One collar level below finitely many radii. -/
theorem exists_delta_common {ι : Type*} [Finite ι] [Nonempty ι] (ρ : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      ∀ (j : ι) (i : Fin d), 2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ j := by
  cases nonempty_fintype ι
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have hmin : 0 < Finset.univ.inf' hne ρ := by
    rw [Finset.lt_inf'_iff]
    exact fun j _ => hρ j
  obtain ⟨δ, hδ, hδa, hsm⟩ := exists_delta k hk a hd ha hmin
  exact ⟨δ, hδ, hδa, fun j i => (hsm i).trans_le (Finset.inf'_le ρ (Finset.mem_univ j))⟩

variable {a} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)
  (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)

/-- ★ **The local-input theorem at a given collar level** (CCCXXXIV, with `δ` supplied). -/
theorem hasCoordFreeExpansion_local_at :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).stratumMeasure
      (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).field
      (spectrumLe (commonQ (producedCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).cores.k) (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  have h := hasCoordFreeExpansion_collar_of_nonneg_on k hk a δ A.measurable_priorRep
    A.measurable_obsRep A.integrable_obsRep hδ hd ha hδa (A.priorRep_nonneg_on hϕ0W)
    fun I => (A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)
  refine h.congr (measurableSet_W a) ?_ ?_
  · intro w hw
    rw [A.obsRep_eq_of_mem (A.box_subset_realDomain hw),
      A.priorRep_eq_of_mem (A.box_subset_realDomain hw)]
  · intro I
    filter_upwards [ae_stratumMeasure_mem_box k hk a δ hδ (posPart A.priorRep) A.obsRep
      (measurable_posPart A.measurable_priorRep) (posPart_nonneg A.priorRep)
      (integrable_posPart a (A.priorRep_nonneg_on hϕ0W) A.integrable_obsRep) hd ha hδa
      (fun I => ((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k
        hk a δ hδ hd ha hδa (A.priorRep_nonneg_on hϕ0W)) I] with s hs
    exact eventually_of_mem (A.isOpen_realDomain.mem_nhds (A.box_subset_realDomain hs))
      fun w hw => A.obsRep_eq_of_mem hw

end WaterFilling

end Grammar
