/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.JointSample
import Grammar.TaylorMoment
import Grammar.LpContinuity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The concrete tangential reconstruction

Joint tangential data `C(K, DataSpace d)` are reconstructed from a scalar `ℓ¹` datum indexed by
pairs `(j, α)` — a normal data slot `j` and a tangential multi-index `α` — by evaluating the
tangential power series at the base point: with tangential coordinates `θ : C(K, ℝ^m)` bounded by
`ρ` (`TanChart`), the reconstruction is

  `(T z)(v)_j = ∑_α z_{(j,α)} (θ(v)/ρ)^α`.

The weights `ρ^{|α|}` are carried by the coefficients, so `|(θ(v)/ρ)^α| ≤ 1` and
`‖(T z)(v)‖_{ℓ¹} ≤ ‖z‖_{ℓ¹}` for every `v` (`norm_recDatum_le`); coordinatewise continuity in `v`
follows from the uniform convergence of the tangential series (`continuous_tsum`) and the `ℓ¹`
criterion (`continuous_dataSpace_of_majorant`).  `tanReconstruct` is the resulting continuous linear
map of norm at most `1` (`norm_tanReconstruct_le`), and `jointTanReconstruct` its finite-chart
version into `JointData K n`, the reconstruction interface of `JointSample.lean` made concrete.

Non-claim: the identification of the reconstructed data with the paper's tangentially analytic
chart amplitudes is a statement about joint Cauchy coefficients on a product polydisc (next unit).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily MonoRep

/-- The latent index of a chart: a normal data slot and a tangential multi-index. -/
abbrev TanIdx (m d : ℕ) := DataIdx d × (Fin m → ℕ)

/-- Tangential coordinates on a compact base, bounded by `ρ`. -/
structure TanChart (K : Type*) [TopologicalSpace K] (m : ℕ) where
  /-- the tangential coordinates -/
  θ : C(K, Fin m → ℝ)
  /-- the tangential radius -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  bound : ∀ v i, |θ v i| ≤ ρ

namespace TanChart

variable {K : Type*} [TopologicalSpace K] {m d : ℕ} (T : TanChart K m)

/-- The normalised tangential coordinate `θ(v)/ρ`, in the closed unit ball of the sup norm. -/
noncomputable def w (v : K) : Fin m → ℝ := T.ρ⁻¹ • T.θ v

theorem norm_w_le (v : K) : ‖T.w v‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, w, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 T.ρ_pos),
    ← div_eq_inv_mul, div_le_one T.ρ_pos]
  exact T.bound v i

theorem continuous_w : Continuous T.w := by
  unfold w
  exact (continuous_const (y := T.ρ⁻¹)).smul T.θ.continuous

theorem abs_mono_w_le (α : Fin m → ℕ) (v : K) : |mono α (T.w v)| ≤ 1 :=
  (abs_mono_le_norm_pow α (T.w v)).trans (pow_le_one₀ (norm_nonneg _) (T.norm_w_le v))

/-- The tangential majorant `B_j(z) = ∑_α |z_{(j,α)}|`. -/
noncomputable def majorant (z : L1Seq (TanIdx m d)) (j : DataIdx d) : ℝ := ∑' α, |z (j, α)|

theorem summable_abs_slice (z : L1Seq (TanIdx m d)) (j : DataIdx d) :
    Summable fun α : Fin m → ℕ => |z (j, α)| :=
  ((summable_prod_of_nonneg fun _ => abs_nonneg _).1 (L1Seq.summable_abs z)).1 j

theorem summable_majorant (z : L1Seq (TanIdx m d)) : Summable (majorant (m := m) z) :=
  ((summable_prod_of_nonneg fun _ => abs_nonneg _).1 (L1Seq.summable_abs z)).2

theorem tsum_majorant (z : L1Seq (TanIdx m d)) : ∑' j, majorant (m := m) z j = ‖z‖ := by
  rw [L1Seq.norm_eq_tsum, (L1Seq.summable_abs z).tsum_prod' fun j => summable_abs_slice z j]
  rfl

theorem summable_recTerm (z : L1Seq (TanIdx m d)) (v : K) (j : DataIdx d) :
    Summable fun α : Fin m → ℕ => z (j, α) * mono α (T.w v) :=
  Summable.of_norm_bounded (summable_abs_slice z j) fun α => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (T.abs_mono_w_le α v)

/-- The reconstructed coordinate `(T z)(v)_j = ∑_α z_{(j,α)} (θ(v)/ρ)^α`. -/
noncomputable def recCoord (z : L1Seq (TanIdx m d)) (v : K) (j : DataIdx d) : ℝ :=
  ∑' α, z (j, α) * mono α (T.w v)

theorem abs_recCoord_le (z : L1Seq (TanIdx m d)) (v : K) (j : DataIdx d) :
    |T.recCoord z v j| ≤ majorant (m := m) z j := by
  unfold recCoord majorant
  refine (norm_tsum_le_tsum_norm (T.summable_recTerm z v j).norm).trans ?_
  refine Summable.tsum_le_tsum (fun α => ?_) (T.summable_recTerm z v j).norm
    (summable_abs_slice z j)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (T.abs_mono_w_le α v)

/-- The reconstructed datum at a base point. -/
noncomputable def recDatum (z : L1Seq (TanIdx m d)) (v : K) : DataSpace d :=
  ⟨fun j => T.recCoord z v j, by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    exact (summable_majorant z).of_nonneg_of_le (fun j => abs_nonneg _) (T.abs_recCoord_le z v)⟩

@[simp] theorem recDatum_apply (z : L1Seq (TanIdx m d)) (v : K) (j : DataIdx d) :
    T.recDatum z v j = T.recCoord z v j := rfl

theorem norm_recDatum_le (z : L1Seq (TanIdx m d)) (v : K) : ‖T.recDatum z v‖ ≤ ‖z‖ := by
  rw [dataNorm_eq_tsum_abs, ← tsum_majorant z]
  exact Summable.tsum_le_tsum (fun j => T.abs_recCoord_le z v j)
    ((summable_majorant z).of_nonneg_of_le (fun j => abs_nonneg _) (T.abs_recCoord_le z v))
    (summable_majorant z)

theorem continuous_recDatum (z : L1Seq (TanIdx m d)) : Continuous fun v => T.recDatum z v := by
  refine continuous_dataSpace_of_majorant _ (fun j => ?_) (majorant z) (summable_majorant z)
    fun v j => T.abs_recCoord_le z v j
  simp only [recDatum_apply, recCoord]
  refine continuous_tsum (fun α => continuous_const.mul ((continuous_mono α).comp T.continuous_w))
    (summable_abs_slice z j) fun α v => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (T.abs_mono_w_le α v)

variable [CompactSpace K]

/-- **The tangential reconstruction**: the continuous linear map from bi-indexed `ℓ¹` coefficients
to tangential data, `(T z)(v)_j = ∑_α z_{(j,α)} (θ(v)/ρ)^α`, of norm at most `1`. -/
noncomputable def tanReconstruct : L1Seq (TanIdx m d) →L[ℝ] TangentialData K d :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨fun v => T.recDatum z v, T.continuous_recDatum z⟩
      map_add' := fun z z' => by
        ext v j
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, lp.coeFn_add, Pi.add_apply,
          recDatum_apply, recCoord, add_mul]
        exact Summable.tsum_add (T.summable_recTerm z v j) (T.summable_recTerm z' v j)
      map_smul' := fun c z => by
        ext v j
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, lp.coeFn_smul, Pi.smul_apply,
          smul_eq_mul, recDatum_apply, recCoord, mul_assoc, RingHom.id_apply]
        exact tsum_mul_left } 1 fun z => by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg z)).2 fun v => T.norm_recDatum_le z v

@[simp] theorem tanReconstruct_apply (z : L1Seq (TanIdx m d)) (v : K) (j : DataIdx d) :
    T.tanReconstruct z v j = ∑' α, z (j, α) * mono α (T.w v) := rfl

theorem norm_tanReconstruct_le (z : L1Seq (TanIdx m d)) : ‖T.tanReconstruct z‖ ≤ ‖z‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg z)).2 fun v => T.norm_recDatum_le z v

end TanChart

/-! ### Unpacking a sigma-indexed `ℓ¹` datum -/

section Sigma

variable {ι : Type*} {κ : ι → Type*}

/-- The `I`-component of an `ℓ¹` datum over a sigma type. -/
noncomputable def sigmaUnpack (I : ι) : L1Seq (Σ i, κ i) →L[ℝ] L1Seq (κ I) :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨fun j => z ⟨I, j⟩, by
        change Memℓp _ 1
        rw [memℓp_gen_iff (p := 1) (by simp)]
        simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
        exact (L1Seq.summable_abs z).comp_injective
          (fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2 :
            Function.Injective fun j : κ I => (⟨I, j⟩ : Σ i, κ i))⟩
      map_add' := fun z w => by ext j; rfl
      map_smul' := fun c z => by ext j; rfl } 1 fun z => by
    rw [one_mul, L1Seq.norm_eq_tsum, L1Seq.norm_eq_tsum]
    have hinj : Function.Injective fun j : κ I => (⟨I, j⟩ : Σ i, κ i) :=
      fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
    refine Summable.tsum_le_tsum_of_inj (fun j : κ I => (⟨I, j⟩ : Σ i, κ i)) hinj ?_ ?_ ?_ ?_
    · exact fun _ _ => abs_nonneg _
    · exact fun _ => le_rfl
    · exact (L1Seq.summable_abs z).comp_injective hinj
    · exact L1Seq.summable_abs z

@[simp] theorem sigmaUnpack_apply (I : ι) (z : L1Seq (Σ i, κ i)) (j : κ I) :
    sigmaUnpack I z j = z ⟨I, j⟩ := rfl

end Sigma

/-! ### The joint tangential reconstruction -/

section Joint

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  {n m : Fin M → ℕ}

/-- The latent index of the joint charts. -/
abbrev JointTanIdx (m n : Fin M → ℕ) := Σ I : Fin M, TanIdx (m I) (n I + 1)

/-- **The joint tangential reconstruction** into `JointData K n`. -/
noncomputable def jointTanReconstruct (Tc : ∀ I, TanChart (K I) (m I)) :
    L1Seq (JointTanIdx m n) →L[ℝ] JointData K n :=
  ContinuousLinearMap.pi fun I => (Tc I).tanReconstruct.comp (sigmaUnpack I)

@[simp] theorem jointTanReconstruct_apply (Tc : ∀ I, TanChart (K I) (m I))
    (z : L1Seq (JointTanIdx m n)) (I : Fin M) (v : K I) (j : DataIdx (n I + 1)) :
    jointTanReconstruct Tc z I v j = ∑' α, z ⟨I, (j, α)⟩ * mono α ((Tc I).w v) := rfl

end Joint

end Grammar
