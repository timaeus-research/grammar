/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SignedBoxExpansion

/-!
# Reflection-sensitive regression checks for the signed box (CCCXLII; phase G, unit G7)

Consult #101 §A2 (stopping-gate item 7 of #100). Three fixtures that fail if the normal-sign
action on jets were omitted or the assembly overcounted:

* **Tensor transport** (general `d`): the transported evaluation tensor at basis normal vectors
  picks up the product of the signs (★ `reflTensor_evalV_basis_pair`); in particular a negative
  reflection negates the order-one evaluation (`reflTensor_evalV_neg`, R3) and a crossing picks up
  `sgn σ i · sgn σ j` at order two (`reflTensor_evalV_two`, R2); the coordinate observable `w ↦ w_i`
  has normal differential `1` along `e_i` (`normalDifferential_coord_basisN`).
* **Deepest stratum** (general `d`): reflections fix the deepest stratum, so the assembled stratum
  measure there is the plain sum of the piece measures (`signedStratumMeasure_univ`, R1/R2 actual
  pieces).
* **Synthetic assembly** (`d = 1`): with Dirac measures at the origin for both signs and the
  order-one evaluation field, the assembled coefficient of the odd observable `w ↦ w₀` is `0`
  (★ `synthetic_cancellation`: the two contributions are `+1` and `−1`; without the jet action one
  would get `2`), while with the order-zero field and the observable `1` the assembled mass and
  coefficient are `2` (`synthetic_mass`, `synthetic_order_zero`: no RN overcounting).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ}

/-! ### Evaluation tensors and their transport -/

section tensors

variable (I : Finset (Fin d))

/-- The basis normal vector `e_i ∈ N_I`. -/
noncomputable def basisN (i : I) : normalSpace d I := ⟨basisVec d i, basisVec_mem d I i⟩

theorem coe_basisN (i : I) : ((basisN I i : normalSpace d I) : Amb d) = basisVec d i := rfl

/-- The evaluation tensor `J ↦ J v`. -/
noncomputable def evalV {r : ℕ} (v : Fin r → normalSpace d I) : MomentTensor (normalSpace d I) r :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => normalSpace d I) ℝ v

theorem evalV_pair {r : ℕ} (v : Fin r → normalSpace d I) (J : JetForm (normalSpace d I) r) :
    (evalV I v).pair J = J v := rfl

theorem reflNormal_basisN (σ : CoordSign d) (i : I) :
    reflNormal σ I (basisN I i) = sgn σ i • basisN I i :=
  Subtype.ext (by
    rw [reflNormal_apply, coe_reflNormalLin, Submodule.coe_smul]
    exact reflAmbLin_basisVec σ i)

/-- ★ **Transported evaluation tensors pick up the product of the signs.** -/
theorem reflTensor_evalV_basis_pair (σ : CoordSign d) {r : ℕ} (j : Fin r → I)
    (J : JetForm (normalSpace d I) r) :
    (reflTensor σ I r (evalV I fun i => basisN I (j i))).pair J =
      (∏ i, sgn σ (j i)) * J (fun i => basisN I (j i)) := by
  rw [reflTensor_pair, evalV_pair, jetPull_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, reflNormal_basisN]
  rw [J.map_smul_univ, smul_eq_mul]

/-- **R3**: a negative reflection negates the order-one evaluation along `e_i`. -/
theorem reflTensor_evalV_neg (σ : CoordSign d) (i : I) (hσ : σ i = false)
    (J : JetForm (normalSpace d I) 1) :
    (reflTensor σ I 1 (evalV I fun _ => basisN I i)).pair J = -(J fun _ => basisN I i) := by
  rw [reflTensor_evalV_basis_pair I σ (fun _ => i) J]
  simp [sgn, hσ]

/-- **R2**: at a crossing the order-two evaluation picks up `sgn σ i · sgn σ j`. -/
theorem reflTensor_evalV_two (σ : CoordSign d) (j : Fin 2 → I) (J : JetForm (normalSpace d I) 2) :
    (reflTensor σ I 2 (evalV I fun i => basisN I (j i))).pair J =
      (sgn σ (j 0) * sgn σ (j 1)) * J (fun i => basisN I (j i)) := by
  rw [reflTensor_evalV_basis_pair I σ j J, Fin.prod_univ_two]

end tensors

/-! ### The coordinate observable -/

section jets

variable (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i) (I : Finset (Fin d))

/-- The `i`-th coordinate of a normal vector, as a continuous linear functional on `N_I`. -/
def coordN (i : Fin d) : normalSpace d I →L[ℝ] ℝ where
  toFun n := (n : Amb d).ofLp i
  map_add' x y := by simp
  map_smul' c x := by simp
  cont := (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val

theorem coordN_apply (i : Fin d) (n : normalSpace d I) : coordN I i n = (n : Amb d).ofLp i := rfl

/-- The normal differential of the coordinate observable `w ↦ w_i` is the `i`-th coordinate. -/
theorem normalDifferential_coord (s : (geometry d k h hk).Stratum I) (i : Fin d)
    (m : Fin 1 → normalSpace d I) :
    (normalData d k h hk).normalDifferential (fun w => w i) I s 1 m =
      ((m 0 : normalSpace d I) : Amb d).ofLp i := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential rawNormalJet
  have hf : (fun n : normalSpace d I => ((fun w : Fin d → ℝ => w i) ∘ (geometry d k h hk).π)
      ((normalData d k h hk).Φ I s n)) = fun n => s.1 i + coordN I i n := funext fun n => rfl
  have key : fderiv ℝ (fun n : normalSpace d I => s.1 i + coordN I i n) 0 (m 0) =
      ((m 0 : normalSpace d I) : Amb d).ofLp i := by
    rw [fderiv_const_add, (coordN I i).fderiv]
    rfl
  exact (iteratedFDeriv_one_apply m).trans
    ((congrArg (fun f => fderiv ℝ f (0 : normalSpace d I) (m 0)) hf).trans key)

theorem normalDifferential_coord_basisN (s : (geometry d k h hk).Stratum I) (i : Fin d)
    (hi : i ∈ I) :
    (normalData d k h hk).normalDifferential (fun w => w i) I s 1 (fun _ => basisN I ⟨i, hi⟩) = 1 :=
  (normalDifferential_coord k h hk I s i _).trans (by rw [coe_basisN, basisVec_ofLp, if_pos rfl])

end jets

/-! ### The deepest stratum: reflections act trivially -/

section deepest

variable (k h : Fin d → ℕ) (hk : ∀ i, 0 < k i)

theorem refl_zero (σ : CoordSign d) : refl σ (0 : Fin d → ℝ) = 0 := by
  funext i
  simp [refl_apply]

theorem reflStratum_univ (σ : CoordSign d)
    (s : (geometry d k h hk).Stratum (Finset.univ : Finset (geometry d k h hk).Component)) :
    reflStratum k h hk σ Finset.univ s = s := by
  have h0 : (s : Fin d → ℝ) = 0 := (mem_stratumSet_univ_iff d k h hk _).1 s.2
  exact Subtype.ext ((congrArg (refl σ) h0).trans ((refl_zero σ).trans h0.symm))

theorem map_reflStratumEquiv_univ (σ : CoordSign d)
    (ν : Measure ((geometry d k h hk).Stratum
      (Finset.univ : Finset (geometry d k h hk).Component))) :
    ν.map (reflStratumEquiv k h hk σ Finset.univ) = ν := by
  have : ⇑(reflStratumEquiv k h hk σ Finset.univ) = id := funext (reflStratum_univ k h hk σ)
  rw [this]
  exact Measure.map_id

variable {a : ℝ} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension a ϕ φ) (hd : 0 < d)
  (ha : 0 < a) (hϕ0 : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ ϕ w) (δ : ℝ) (hδ : 0 < δ)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (hsmall : ∀ (σ : CoordSign d) (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
      ((A.pullback σ).toRep.faceSeries a I).ρ)

omit h in
/-- **R1/R2 (actual pieces)**: at the deepest stratum the assembled measure is the plain sum of
the `2^d` piece measures (no quotient by the stabiliser, no division by `2^d`). -/
theorem signedStratumMeasure_univ :
    signedStratumMeasure k hk A hd ha hϕ0 δ hδ hδa hsmall Finset.univ =
      ∑ σ : CoordSign d,
        (pieceCertificate k hk A hd ha hϕ0 δ hδ hδa hsmall σ).stratumMeasure Finset.univ :=
  (signedStratumMeasure_eq k hk A hd ha hϕ0 δ hδ hδa hsmall Finset.univ).trans
    (Finset.sum_congr rfl fun σ _ => map_reflStratumEquiv_univ k (zeroOrders d) hk σ _)

end deepest

/-! ### Synthetic assembly fixtures in dimension one -/

section synthetic

variable (k h : Fin 1 → ℕ) (hk : ∀ i, 0 < k i)

/-- The fixture measure: the Dirac mass at the origin on the deepest stratum, `0` elsewhere. -/
noncomputable def fixMeasure (I : Finset (geometry 1 k h hk).Component) :
    Measure ((geometry 1 k h hk).Stratum I) :=
  Measure.count.restrict {s | (s : Fin 1 → ℝ) = 0}

theorem fixMeasure_of_ne (I : Finset (geometry 1 k h hk).Component) (hI : I ≠ Finset.univ) :
    fixMeasure k h hk I = 0 := by
  have : {s : (geometry 1 k h hk).Stratum I | (s : Fin 1 → ℝ) = 0} = ∅ := by
    ext s
    refine ⟨fun h0 => ?_, fun h' => h'.elim⟩
    have hm := s.2
    rw [show (s : Fin 1 → ℝ) = 0 from h0] at hm
    exact hI (Finset.eq_univ_iff_forall.2 fun i => (hm i).1 rfl)
  exact (congrArg (Measure.count (α := (geometry 1 k h hk).Stratum I)).restrict this).trans
    Measure.restrict_empty

theorem fixMeasure_univ : fixMeasure k h hk Finset.univ = Measure.dirac (origin 1 k h hk) := by
  have : {s : (geometry 1 k h hk).Stratum Finset.univ | (s : Fin 1 → ℝ) = 0} =
      {origin 1 k h hk} := by
    ext s
    refine ⟨fun h0 => Subtype.ext h0, fun h' => ?_⟩
    rw [mem_singleton_iff] at h'
    subst h'
    rfl
  refine (congrArg (Measure.count (α := (geometry 1 k h hk).Stratum Finset.univ)).restrict
    this).trans ?_
  rw [Measure.restrict_singleton, Measure.count_singleton, one_smul]

theorem isFiniteMeasure_dirac_origin : IsFiniteMeasure (Measure.dirac (origin 1 k h hk)) :=
  ⟨by rw [Measure.dirac_apply_of_mem (mem_univ _)]; exact ENNReal.one_lt_top⟩

theorem isFiniteMeasure_fixMeasure (I : Finset (geometry 1 k h hk).Component) :
    IsFiniteMeasure (fixMeasure k h hk I) := by
  by_cases hI : I = Finset.univ
  · subst hI
    rw [fixMeasure_univ]
    exact isFiniteMeasure_dirac_origin k h hk
  · rw [fixMeasure_of_ne k h hk I hI]
    infer_instance

/-- The fixture family: the same fixture measure for every sign. -/
noncomputable def fixNu : CoordSign 1 → ∀ I : Finset (geometry 1 k h hk).Component,
    Measure ((geometry 1 k h hk).Stratum I) := fun _ => fixMeasure k h hk

instance (σ : CoordSign 1) (I : Finset (geometry 1 k h hk).Component) :
    IsFiniteMeasure (fixNu k h hk σ I) :=
  isFiniteMeasure_fixMeasure k h hk I

/-- The distinguished normal vector `e₀ ∈ N_I` (zero if `0 ∉ I`). -/
noncomputable def coordV (I : Finset (Fin 1)) : normalSpace 1 I :=
  if h0 : (0 : Fin 1) ∈ I then basisN I ⟨0, h0⟩ else 0

theorem coordV_univ :
    coordV (Finset.univ : Finset (geometry 1 k h hk).Component) =
      basisN Finset.univ ⟨0, Finset.mem_univ _⟩ :=
  dif_pos (Finset.mem_univ _)

open Classical in
/-- The fixture field of order `r₀` at the index `q₀`: evaluation at `(e₀, …, e₀)`. -/
noncomputable def fixField (r₀ : ℕ) (q₀ : PowerLogIndex) :
    (normalData 1 k h hk).MomentCoefficientField := fun I r q _ =>
  (if r = r₀ ∧ q = q₀ then (1 : ℝ) else 0) • evalV I (fun _ : Fin r => coordV I)

theorem reflTensor_smul (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) (c : ℝ)
    (T : MomentTensor (normalSpace d I) r) :
    reflTensor σ I r (c • T) = c • reflTensor σ I r T :=
  ContinuousLinearMap.smul_comp c T (jetPull σ I r)

theorem reflTensor_zero (σ : CoordSign d) (I : Finset (Fin d)) (r : ℕ) :
    reflTensor σ I r 0 = 0 :=
  ContinuousLinearMap.zero_comp (jetPull σ I r)

theorem fixField_pair_of_ne (r₀ : ℕ) (q₀ : PowerLogIndex) (σ : CoordSign 1)
    (I : Finset (geometry 1 k h hk).Component) {r : ℕ} (hr : r ≠ r₀) (q : PowerLogIndex)
    (s : (geometry 1 k h hk).Stratum I) (J : JetForm ((normalData 1 k h hk).N I s) r) :
    (reflField k h hk σ (fixField k h hk r₀ q₀) I r q s).pair J = 0 := by
  unfold reflField fixField
  rw [if_neg (fun h' => hr h'.1), zero_smul]
  exact congrArg (fun T : MomentTensor (normalSpace 1 I) r => T.pair J) (reflTensor_zero σ I r)

/-- The sum of the signs over all patterns in dimension one vanishes. -/
theorem sum_sgn_zero : ∑ σ : CoordSign 1, sgn σ 0 = 0 := by
  have := Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) (fun σ : CoordSign 1 => sgn σ 0)
    (fun b => if b then (1 : ℝ) else -1) fun σ => rfl
  rw [this, Fintype.sum_bool]
  norm_num

/-- The order-one fixture: the coefficient of the odd observable `w ↦ w₀` for one sign is
`sgn σ 0`. -/
theorem fixture_one_value (q₀ : PowerLogIndex) (σ : CoordSign 1) :
    (normalData 1 k h hk).expansionCoefficient (fixMeasure k h hk)
      (reflField k h hk σ (fixField k h hk 1 q₀)) (fun w => w 0) q₀ = sgn σ 0 := by
  unfold ResolvedNormalData.expansionCoefficient
  rw [Finset.sum_eq_single (Finset.univ : Finset (geometry 1 k h hk).Component)]
  · rw [fixMeasure_univ, integral_dirac, tsum_eq_single 1]
    · rw [Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
      unfold reflField fixField
      rw [if_pos ⟨rfl, rfl⟩, one_smul, coordV_univ k h hk]
      refine (reflTensor_evalV_basis_pair (Finset.univ : Finset (geometry 1 k h hk).Component) σ
        (fun _ => ⟨0, Finset.mem_univ _⟩) _).trans ?_
      refine (congrArg (fun x => (∏ i : Fin 1, sgn σ ((fun _ : Fin 1 =>
        (⟨(0 : Fin 1), Finset.mem_univ _⟩ :
          ↥(Finset.univ : Finset (geometry 1 k h hk).Component))) i).1) * x)
        (normalDifferential_coord_basisN k h hk Finset.univ (origin 1 k h hk) (0 : Fin 1)
          (Finset.mem_univ _))).trans ?_
      rw [mul_one, Fin.prod_univ_one]
    · intro r hr
      rw [fixField_pair_of_ne k h hk 1 q₀ σ Finset.univ hr, mul_zero]
  · intro I _ hI
    rw [fixMeasure_of_ne k h hk I hI, integral_zero_measure]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- ★ **Synthetic cancellation (R3)**: with Dirac masses at the origin for both signs and the
order-one evaluation field, the assembled coefficient of the odd observable is `0` — the two
contributions are `+1` and `−1`. -/
theorem synthetic_cancellation (q₀ : PowerLogIndex) :
    (normalData 1 k h hk).expansionCoefficient
      (ResolvedNormalData.sumMeasure (R := geometry 1 k h hk) (fixNu k h hk))
      ((normalData 1 k h hk).glueField (fixNu k h hk)
        fun σ => reflField k h hk σ (fixField k h hk 1 q₀)) (fun w => w 0) q₀ = 0 := by
  rw [ResolvedNormalData.expansionCoefficient_glue (normalData 1 k h hk) (fixNu k h hk)
    (fun σ => reflField k h hk σ (fixField k h hk 1 q₀)) (fun w => w 0) q₀]
  · exact (Finset.sum_congr rfl fun σ _ => fixture_one_value k h hk q₀ σ).trans sum_sgn_zero
  · intro σ I s
    refine (hasSum_single 1 fun r hr => ?_).summable
    rw [fixField_pair_of_ne k h hk 1 q₀ σ I hr, mul_zero]
  · intro σ I
    change Integrable _ (fixMeasure k h hk I)
    by_cases hI : I = Finset.univ
    · subst hI
      rw [fixMeasure_univ]
      exact integrable_dirac enorm_lt_top
    · rw [fixMeasure_of_ne k h hk I hI]
      exact integrable_zero_measure

/-- **Synthetic mass (R1)**: the assembled fixture measure at the origin is twice the Dirac mass. -/
theorem synthetic_mass :
    ResolvedNormalData.sumMeasure (R := geometry 1 k h hk) (fixNu k h hk) Finset.univ =
      (2 : ℕ) • Measure.dirac (origin 1 k h hk) := by
  unfold ResolvedNormalData.sumMeasure fixNu
  rw [Finset.sum_const, Finset.card_univ, fixMeasure_univ]
  congr 1

/-- The order-zero fixture: the coefficient of the observable `1` for one sign is `1`. -/
theorem fixture_zero_value (q₀ : PowerLogIndex) (σ : CoordSign 1) :
    (normalData 1 k h hk).expansionCoefficient (fixMeasure k h hk)
      (reflField k h hk σ (fixField k h hk 0 q₀)) (fun _ => (1 : ℝ)) q₀ = 1 := by
  unfold ResolvedNormalData.expansionCoefficient
  rw [Finset.sum_eq_single (Finset.univ : Finset (geometry 1 k h hk).Component)]
  · rw [fixMeasure_univ, integral_dirac, tsum_eq_single 0]
    · rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
      unfold reflField fixField
      rw [if_pos ⟨rfl, rfl⟩, one_smul]
      erw [reflTensor_pair, evalV_pair, jetPull_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      exact (normalData 1 k h hk).normalDifferential_zero _ _ _ _
    · intro r hr
      rw [fixField_pair_of_ne k h hk 0 q₀ σ Finset.univ hr, mul_zero]
  · intro I _ hI
    rw [fixMeasure_of_ne k h hk I hI, integral_zero_measure]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- **Synthetic order zero (R1)**: the assembled coefficient of the observable `1` is `2` — the
Radon–Nikodym assembly does not overcount. -/
theorem synthetic_order_zero (q₀ : PowerLogIndex) :
    (normalData 1 k h hk).expansionCoefficient
      (ResolvedNormalData.sumMeasure (R := geometry 1 k h hk) (fixNu k h hk))
      ((normalData 1 k h hk).glueField (fixNu k h hk)
        fun σ => reflField k h hk σ (fixField k h hk 0 q₀)) (fun _ => (1 : ℝ)) q₀ = 2 := by
  rw [ResolvedNormalData.expansionCoefficient_glue (normalData 1 k h hk) (fixNu k h hk)
    (fun σ => reflField k h hk σ (fixField k h hk 0 q₀)) (fun _ => (1 : ℝ)) q₀]
  · refine (Finset.sum_congr rfl fun σ _ => fixture_zero_value k h hk q₀ σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp
  · intro σ I s
    refine (hasSum_single 0 fun r hr => ?_).summable
    rw [fixField_pair_of_ne k h hk 0 q₀ σ I hr, mul_zero]
  · intro σ I
    change Integrable _ (fixMeasure k h hk I)
    by_cases hI : I = Finset.univ
    · subst hI
      rw [fixMeasure_univ]
      exact integrable_dirac enorm_lt_top
    · rw [fixMeasure_of_ne k h hk I hI]
      exact integrable_zero_measure

end synthetic

end WaterFilling

end Grammar
