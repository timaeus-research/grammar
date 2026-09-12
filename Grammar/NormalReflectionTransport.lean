/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.OrthantDecomposition

/-!
# Reflection transport of stratum data and expansions (CCCXXXVIII; phase G, unit G3)

Consult #100 §4. A coordinate reflection `R_σ` preserves every coordinate stratum
(`reflStratum`), acts on the ambient Euclidean space and on each normal space `N_I = span{e_i}`
as a continuous linear involution (`reflAmb`, `reflNormal`), and is compatible with the tubular
germs: `R_σ (Φ_I s v) = Φ_I (R_σ s) (L_σ v)` (`refl_Φ`). Hence the normal differentials of the
reflected observable are the pullbacks of those of the observable at the reflected point
(`normalDifferential_comp_refl`, unconditional, via
`ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`),
and a moment field transported by `reflField σ B (t) = B (R_σ t) ∘ P_σ` pairs with the jets of `φ`
at `t` as `B (R_σ t)` pairs with the jets of `φ ∘ R_σ` at `R_σ t` (`reflField_pair`). Pushing the
stratum measures forward (`reflMeasure`) therefore transports the expansion coefficients
(`expansionCoefficient_reflMeasure`) and the expansion itself from the positive box for
`(ϕ ∘ R_σ, φ ∘ R_σ)` to the orthant piece `R_σ⁻¹ [0,a]^d` for `(ϕ, φ)`
(★★ `hasCoordFreeExpansion_refl`); a.e. support in the positive box transports to the orthant piece
(`ae_reflMeasure_mem_orthantBox`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ}

/-! ### The reflection on the ambient space and on the normal spaces -/

/-- The reflection on the ambient Euclidean space, as a linear map. -/
def reflAmbLin (σ : CoordSign d) : Amb d →ₗ[ℝ] Amb d where
  toFun v := WithLp.toLp 2 fun i => sgn σ i * v.ofLp i
  map_add' v w := by
    ext i
    simp [mul_add]
  map_smul' c v := by
    ext i
    simp [mul_left_comm]

theorem reflAmbLin_ofLp (σ : CoordSign d) (v : Amb d) (i : Fin d) :
    (reflAmbLin σ v).ofLp i = sgn σ i * v.ofLp i := rfl

theorem reflAmbLin_reflAmbLin (σ : CoordSign d) (v : Amb d) :
    reflAmbLin σ (reflAmbLin σ v) = v := by
  ext i
  rw [reflAmbLin_ofLp, reflAmbLin_ofLp, ← mul_assoc, sgn_mul_self, one_mul]

theorem reflAmbLin_basisVec (σ : CoordSign d) (i : Fin d) :
    reflAmbLin σ (basisVec d i) = sgn σ i • basisVec d i := by
  ext j
  rw [reflAmbLin_ofLp, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

theorem reflAmbLin_mem (σ : CoordSign d) (I : Finset (Fin d)) {v : Amb d}
    (hv : v ∈ normalSpace d I) : reflAmbLin σ v ∈ normalSpace d I := by
  have h : (normalSpace d I).map (reflAmbLin σ) ≤ normalSpace d I := by
    unfold normalSpace
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    rw [reflAmbLin_basisVec]
    exact Submodule.smul_mem _ _ (basisVec_mem d I i)
  exact h (Submodule.mem_map_of_mem hv)

/-- The reflection restricted to the normal space `N_I`, as a linear map. -/
noncomputable def reflNormalLin (σ : CoordSign d) (I : Finset (Fin d)) :
    normalSpace d I →ₗ[ℝ] normalSpace d I :=
  (reflAmbLin σ).restrict fun _ hv => reflAmbLin_mem σ I hv

theorem coe_reflNormalLin (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
    ((reflNormalLin σ I v : normalSpace d I) : Amb d) = reflAmbLin σ v := rfl

theorem reflNormalLin_involutive (σ : CoordSign d) (I : Finset (Fin d)) :
    Function.Involutive (reflNormalLin σ I) := fun v =>
  Subtype.ext (by rw [coe_reflNormalLin, coe_reflNormalLin, reflAmbLin_reflAmbLin])

/-- **The reflection on the normal space `N_I`** as a continuous linear equivalence. -/
noncomputable def reflNormal (σ : CoordSign d) (I : Finset (Fin d)) :
    normalSpace d I ≃L[ℝ] normalSpace d I :=
  (LinearEquiv.ofInvolutive (reflNormalLin σ I)
    (reflNormalLin_involutive σ I)).toContinuousLinearEquiv

theorem reflNormal_apply (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
    reflNormal σ I v = reflNormalLin σ I v := rfl

theorem reflNormal_ofLp (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) (i : Fin d) :
    ((reflNormal σ I v : normalSpace d I) : Amb d).ofLp i = sgn σ i * (v : Amb d).ofLp i := rfl

theorem reflNormal_reflNormal (σ : CoordSign d) (I : Finset (Fin d)) (v : normalSpace d I) :
    reflNormal σ I (reflNormal σ I v) = v :=
  reflNormalLin_involutive σ I v

/-! ### The reflection on the strata -/

variable (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i)

theorem refl_mem_stratumSet (σ : CoordSign d) (I : Finset (Fin d)) (w : Fin d → ℝ) :
    refl σ w ∈ (geometry d k h hk).stratumSet I ↔ w ∈ (geometry d k h hk).stratumSet I := by
  have hE : ∀ i, refl σ w ∈ (geometry d k h hk).E i ↔ w ∈ (geometry d k h hk).E i := fun i => by
    change sgn σ i * w i = 0 ↔ w i = 0
    have := sgn_ne_zero σ i
    simp [mul_eq_zero, this]
  unfold ResolvedGeometry.stratumSet
  change (∀ i, refl σ w ∈ (geometry d k h hk).E i ↔ i ∈ I) ↔
    (∀ i, w ∈ (geometry d k h hk).E i ↔ i ∈ I)
  simp only [hE]

/-- The reflection of a stratum. -/
def reflStratum (σ : CoordSign d) (I : Finset (Fin d)) :
    (geometry d k h hk).Stratum I → (geometry d k h hk).Stratum I := fun s =>
  ⟨refl σ s.1, (refl_mem_stratumSet k h hk σ I s.1).2 s.2⟩

theorem coe_reflStratum (σ : CoordSign d) (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I) :
    (reflStratum k h hk σ I s : Fin d → ℝ) = refl σ s.1 := rfl

theorem reflStratum_reflStratum (σ : CoordSign d) (I : Finset (Fin d))
    (s : (geometry d k h hk).Stratum I) :
    reflStratum k h hk σ I (reflStratum k h hk σ I s) = s :=
  Subtype.ext (refl_refl σ s.1)

theorem measurable_reflStratum (σ : CoordSign d) (I : Finset (Fin d)) :
    Measurable (reflStratum k h hk σ I) :=
  ((measurable_refl σ).comp measurable_subtype_coe).subtype_mk

/-- The reflection of a stratum as a measurable equivalence. -/
def reflStratumEquiv (σ : CoordSign d) (I : Finset (Fin d)) :
    (geometry d k h hk).Stratum I ≃ᵐ (geometry d k h hk).Stratum I :=
  MeasurableEquiv.ofInvolutive (reflStratum k h hk σ I) (reflStratum_reflStratum k h hk σ I)
    (measurable_reflStratum k h hk σ I)

theorem reflStratumEquiv_apply (σ : CoordSign d) (I : Finset (Fin d))
    (s : (geometry d k h hk).Stratum I) :
    reflStratumEquiv k h hk σ I s = reflStratum k h hk σ I s := rfl

/-- ★ **Tubular compatibility**: `R_σ (Φ_I s v) = Φ_I (R_σ s) (L_σ v)`. -/
theorem refl_Φ (σ : CoordSign d) (I : Finset (Fin d)) (s : (geometry d k h hk).Stratum I)
    (v : normalSpace d I) :
    refl σ ((normalData d k h hk).Φ I s v) =
      (normalData d k h hk).Φ I (reflStratum k h hk σ I s) (reflNormal σ I v) := by
  funext i
  change sgn σ i * (s.1 i + (v : Amb d).ofLp i) =
    refl σ s.1 i + ((reflNormal σ I v : normalSpace d I) : Amb d).ofLp i
  rw [refl_apply, reflNormal_ofLp]
  ring

/-! ### Jets, tensors and fields -/

/-- ★ **Normal differentials of a reflected observable** are pullbacks of the normal differentials
at the reflected point along `L_σ` (unconditional: `L_σ` is a continuous linear equivalence). -/
theorem normalDifferential_comp_refl (φ : (Fin d → ℝ) → ℝ) (σ : CoordSign d) (I : Finset (Fin d))
    (s : (geometry d k h hk).Stratum I) (r : ℕ) :
    (normalData d k h hk).normalDifferential (φ ∘ refl σ) I s r =
      ((normalData d k h hk).normalDifferential φ I (reflStratum k h hk σ I s)
        r).compContinuousLinearMap
        fun _ => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I) := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential rawNormalJet
  have hfun : (fun n : normalSpace d I =>
      ((φ ∘ refl σ) ∘ (geometry d k h hk).π) ((normalData d k h hk).Φ I s n)) =
      (fun n : normalSpace d I => (φ ∘ (geometry d k h hk).π)
        ((normalData d k h hk).Φ I (reflStratum k h hk σ I s) n)) ∘ (reflNormal σ I) := by
    funext n
    simp only [Function.comp, geometry_π]
    rw [refl_Φ]
  have key := (reflNormal σ I).iteratedFDerivWithin_comp_right
    (fun n : normalSpace d I => (φ ∘ (geometry d k h hk).π)
      ((normalData d k h hk).Φ I (reflStratum k h hk σ I s) n)) uniqueDiffOn_univ
    (x := 0) (mem_univ _) r
  rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, map_zero] at key
  exact (congrArg (fun f => iteratedFDeriv ℝ r f (0 : normalSpace d I)) hfun).trans key

/-- The pullback of jet forms along `L_σ`, as a continuous linear operator. -/
noncomputable def jetPull (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) :
    JetForm (normalSpace d I) r →L[ℝ] JetForm (normalSpace d I) r :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ : Fin r => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I)

theorem jetPull_apply (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
    (J : JetForm (normalSpace d I) r) :
    jetPull σ I r J = J.compContinuousLinearMap
      fun _ => (reflNormal σ I : normalSpace d I →L[ℝ] normalSpace d I) := rfl

/-- The transported moment tensor `B ∘ P_σ`. -/
noncomputable def reflTensor (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
    (B : MomentTensor (normalSpace d I) r) : MomentTensor (normalSpace d I) r :=
  B.comp (jetPull σ I r)

theorem reflTensor_pair (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ)
    (B : MomentTensor (normalSpace d I) r) (J : JetForm (normalSpace d I) r) :
    (reflTensor σ I r B).pair J = B.pair (jetPull σ I r J) := rfl

/-- **The transported moment field** `(R_σ)_* B (t) = B (R_σ t) ∘ P_σ`. -/
noncomputable def reflField (σ : CoordSign d) (B : (normalData d k h hk).MomentCoefficientField) :
    (normalData d k h hk).MomentCoefficientField := fun I r q t =>
  reflTensor σ I r (B I r q (reflStratum k h hk σ I t))

/-- ★ **The pairing identity**: the transported field at `t` paired with the jets of `φ` at `t`
equals the field at `R_σ t` paired with the jets of `φ ∘ R_σ` at `R_σ t`. -/
theorem reflField_pair (B : (normalData d k h hk).MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ)
    (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) (q : PowerLogIndex)
    (t : (geometry d k h hk).Stratum I) :
    (reflField k h hk σ B I r q t).pair ((normalData d k h hk).normalDifferential φ I t r) =
      (B I r q (reflStratum k h hk σ I t)).pair
        ((normalData d k h hk).normalDifferential (φ ∘ refl σ) I (reflStratum k h hk σ I t) r) := by
  rw [normalDifferential_comp_refl, reflStratum_reflStratum]
  rfl

/-! ### Measures, coefficients and the expansion -/

/-- **The transported stratum measures** `(R_σ)_* ν`. -/
noncomputable def reflMeasure (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) :
    ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I) := fun I =>
  (ν I).map (reflStratumEquiv k h hk σ I)

theorem isFiniteMeasure_reflMeasure (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
    [∀ I, IsFiniteMeasure (ν I)] (I : Finset (Fin d)) :
    IsFiniteMeasure (reflMeasure k h hk σ ν I) :=
  Measure.isFiniteMeasure_map _ _

theorem integral_reflMeasure (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
    (f : (geometry d k h hk).Stratum I → ℝ) :
    ∫ t, f t ∂reflMeasure k h hk σ ν I = ∫ s, f (reflStratum k h hk σ I s) ∂ν I :=
  integral_map_equiv _ _

theorem ae_reflMeasure_iff (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
    {P : (geometry d k h hk).Stratum I → Prop} (hP : MeasurableSet {t | P t}) :
    (∀ᵐ (t : (geometry d k h hk).Stratum I) ∂reflMeasure k h hk σ ν I, P t) ↔
      ∀ᵐ (s : (geometry d k h hk).Stratum I) ∂ν I, P (reflStratum k h hk σ I s) :=
  ae_map_iff (measurable_reflStratum k h hk σ I).aemeasurable hP

/-- Support in the positive box transports to support in the orthant piece. -/
theorem ae_reflMeasure_mem_orthantBox (a : ℝ) (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I)) (I : Finset (Fin d))
    (hν : ∀ᵐ (s : (geometry d k h hk).Stratum I) ∂ν I, (s : Fin d → ℝ) ∈ piBox d (Icc 0 a)) :
    ∀ᵐ (t : (geometry d k h hk).Stratum I) ∂reflMeasure k h hk σ ν I,
      (t : Fin d → ℝ) ∈ orthantBox σ a := by
  rw [ae_reflMeasure_iff k h hk σ ν I
    ((measurableSet_orthantBox σ a).preimage measurable_subtype_coe)]
  filter_upwards [hν] with s hs
  change refl σ s.1 ∈ orthantBox σ a
  unfold orthantBox
  rw [mem_preimage, refl_refl]
  exact hs

/-- ★ **Transport of the expansion coefficients.** -/
theorem expansionCoefficient_reflMeasure (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
    (B : (normalData d k h hk).MomentCoefficientField) (φ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) :
    (normalData d k h hk).expansionCoefficient (reflMeasure k h hk σ ν) (reflField k h hk σ B) φ q =
      (normalData d k h hk).expansionCoefficient ν B (φ ∘ refl σ) q := by
  unfold ResolvedNormalData.expansionCoefficient
  refine Finset.sum_congr rfl fun I _ => ?_
  refine (integral_reflMeasure k h hk σ ν I _).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  refine tsum_congr fun r => ?_
  rw [reflField_pair k h hk B φ σ I r q (reflStratum k h hk σ I s),
    reflStratum_reflStratum k h hk σ I s]

/-- ★★ **Transport of the expansion along a reflection**: the coordinate-free expansion on the
positive box for `(ϕ ∘ R_σ, φ ∘ R_σ)` gives the expansion on the orthant piece `R_σ⁻¹ [0,a]^d` for
`(ϕ, φ)`, with the pushed-forward stratum measures and the transported field. -/
theorem hasCoordFreeExpansion_refl (a : ℝ) (σ : CoordSign d)
    (ν : ∀ I : Finset (Fin d), Measure ((geometry d k h hk).Stratum I))
    (B : (normalData d k h hk).MomentCoefficientField) (spec : ℝ → Finset PowerLogIndex)
    (ϕ φ : (Fin d → ℝ) → ℝ)
    (hexp : (normalData d k h hk).HasCoordFreeExpansion ν B spec (piBox d (Icc 0 a)) (phase d k)
      (ϕ ∘ refl σ) (φ ∘ refl σ)) :
    (normalData d k h hk).HasCoordFreeExpansion (reflMeasure k h hk σ ν) (reflField k h hk σ B) spec
      (orthantBox σ a) (phase d k) ϕ φ := by
  intro A
  have hL : ∀ n : ℝ, globalLaplace (orthantBox σ a) (phase d k) (fun w => φ w * ϕ w) n =
      globalLaplace (piBox d (Icc 0 a)) (phase d k)
        (fun w => (φ ∘ refl σ) w * (ϕ ∘ refl σ) w) n := fun n => by
    unfold globalLaplace
    rw [setIntegral_orthantBox a σ]
    simp only [Function.comp, phase_refl]
  simp only [hL, expansionCoefficient_reflMeasure]
  exact hexp A

end WaterFilling

end Grammar
