/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1SeqUpgrade
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Uniform tail estimates for the empirical `ℓ¹` sums

For i.i.d. `ℓ¹`-valued observations `Y_i` with the moment hypothesis `SummableCoordL2`, the
normalised centred empirical sums `S_n = n^{−1/2} ∑_{i<n} (Y_i − E Y_0)` (`empiricalSum`) satisfy,
uniformly in `n`, the tail estimate

  `E ‖S_n − T_F S_n‖ ≤ ∑_{j ∉ F} σ_j`,  `σ_j = √Var(Y_{0,j})`

(`lintegral_enorm_sub_truncate_empirical_le`): each coordinate of `S_n` is centred with variance
`σ_j²` (independence kills the cross terms, `variance_empiricalCoord`), Jensen gives
`E|S_{n,j}| ≤ σ_j` (`integral_abs_empiricalCoord_le`), and Tonelli sums over the coordinates.
The tails `∑_{j∉F_k} σ_j` tend to `0` along any covering exhaustion (`tendsto_sigmaTail`).

Sample size is `n : ℕ`; the case `n = 0` (empty sum) is covered by the inequality but not by the
variance identity.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The coordinate standard deviation `σ_j = √Var(Y_j)`. -/
noncomputable def coordSigma (P : Measure Ω) (Y : Ω → L1Seq ι) (j : ι) : ℝ :=
  Real.sqrt (Var[fun ω => Y ω j; P])

theorem coordSigma_nonneg (Y : Ω → L1Seq ι) (j : ι) : 0 ≤ coordSigma P Y j := Real.sqrt_nonneg _

/-- The normalised centred empirical sum `n^{−1/2} ∑_{i<n} (Y_i − E Y_0)` in `ℓ¹`. -/
noncomputable def empiricalSum (Y : ℕ → Ω → L1Seq ι) (P : Measure Ω) (n : ℕ) (ω : Ω) :
    L1Seq ι :=
  (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, (Y i ω - ∫ ω, Y 0 ω ∂P)

theorem empiricalSum_apply {Y : ℕ → Ω → L1Seq ι} (hint : Integrable (Y 0) P) (n : ℕ) (ω : Ω)
    (j : ι) : empiricalSum Y P n ω j =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (Y i ω j - ∫ ω, Y 0 ω j ∂P) := by
  unfold empiricalSum
  rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, coord_integral P hint j]

theorem identDistrib_coord {Y : ℕ → Ω → L1Seq ι} (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (i : ℕ) (j : ι) : IdentDistrib (fun ω => Y i ω j) (fun ω => Y 0 ω j) P P :=
  (hident i).comp (measurable_coord j)

variable [IsProbabilityMeasure P]

/-- Jensen: `E|X| ≤ √(E X²)`. -/
theorem integral_abs_le_sqrt_integral_sq {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, |X ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have h2 : MemLp (fun ω => |X ω|) 2 P := hX.abs
  have hv := variance_nonneg (fun ω => |X ω|) P
  rw [variance_eq_sub h2] at hv
  refine Real.le_sqrt_of_sq_le ?_
  have : ∫ ω, |X ω| ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P := by simp [sq_abs]
  simp only [Pi.pow_apply] at hv
  linarith

theorem coordSigma_le_coordL2 {Y : Ω → L1Seq ι} (hY : ∀ j, MemLp (fun ω => Y ω j) 2 P) (j : ι) :
    coordSigma P Y j ≤ coordL2 P Y j := by
  unfold coordSigma coordL2
  refine Real.sqrt_le_sqrt ?_
  rw [variance_eq_sub (hY j)]
  simp only [Pi.pow_apply]
  nlinarith [sq_nonneg (∫ ω, Y ω j ∂P)]

theorem summable_coordSigma {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) :
    Summable (coordSigma P Y) :=
  hY.summable.of_nonneg_of_le (fun j => coordSigma_nonneg Y j)
    (coordSigma_le_coordL2 hY.memLp_coord)

section IID

variable [Countable ι] {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0))
  (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
include hY hident

omit [IsProbabilityMeasure P] [Countable ι] in
theorem memLp_coord_iid (i : ℕ) (j : ι) : MemLp (fun ω => Y i ω j) 2 P :=
  (identDistrib_coord hident i j).memLp_iff.2 (hY.memLp_coord j)

omit [Countable ι] in
theorem memLp_coord_sub (i : ℕ) (j : ι) :
    MemLp (fun ω => Y i ω j - ∫ ω, Y 0 ω j ∂P) 2 P :=
  (memLp_coord_iid hY hident i j).sub (memLp_const _)

omit [Countable ι] in
theorem integral_coord_sub (i : ℕ) (j : ι) : ∫ ω, (Y i ω j - ∫ ω, Y 0 ω j ∂P) ∂P = 0 := by
  rw [integral_sub ((memLp_coord_iid hY hident i j).integrable one_le_two) (integrable_const _),
    integral_const, (identDistrib_coord hident i j).integral_eq]
  simp

omit hident in
theorem empiricalCoord_eq (n : ℕ) (j : ι) :
    (fun ω => empiricalSum Y P n ω j) =
      (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, fun ω => Y i ω j - ∫ ω, Y 0 ω j ∂P := by
  funext ω
  rw [empiricalSum_apply (integrable_of_summableCoordL2 P hY) n ω j]
  simp [Finset.sum_apply]

theorem memLp_empiricalCoord (n : ℕ) (j : ι) :
    MemLp (fun ω => empiricalSum Y P n ω j) 2 P := by
  simp_rw [empiricalSum_apply (integrable_of_summableCoordL2 P hY)]
  exact (memLp_finsetSum _ fun i _ => memLp_coord_sub hY hident i j).const_mul _

theorem integral_empiricalCoord (n : ℕ) (j : ι) : ∫ ω, empiricalSum Y P n ω j ∂P = 0 := by
  simp_rw [empiricalSum_apply (integrable_of_summableCoordL2 P hY)]
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    (memLp_coord_sub hY hident i j).integrable one_le_two]
  simp [integral_coord_sub hY hident]

include hindep in
/-- The variance of a coordinate of the empirical sum is at most `σ_j²` (equal for `n ≥ 1`). -/
theorem variance_empiricalCoord_le (n : ℕ) (j : ι) :
    Var[fun ω => empiricalSum Y P n ω j; P] ≤ Var[fun ω => Y 0 ω j; P] := by
  rw [empiricalCoord_eq hY n j, variance_smul,
    IndepFun.variance_sum (fun i _ => memLp_coord_sub hY hident i j) ?_]
  · have hv : ∀ i, Var[fun ω => Y i ω j - ∫ ω, Y 0 ω j ∂P; P] = Var[fun ω => Y 0 ω j; P] :=
      fun i => by
        rw [variance_sub_const (memLp_coord_iid hY hident i j).aestronglyMeasurable,
          (identDistrib_coord hident i j).variance_eq]
    simp_rw [hv]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [variance_nonneg]
    · have : ((Real.sqrt n)⁻¹) ^ 2 * (n * Var[fun ω => Y 0 ω j; P]) =
          Var[fun ω => Y 0 ω j; P] := by
        rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
      exact this.le
  · intro i _ i' _ hii'
    exact (hindep.indepFun hii').comp ((measurable_coord j).sub_const _)
      ((measurable_coord j).sub_const _)

include hindep in
/-- Jensen: `E|S_{n,j}| ≤ σ_j`, uniformly in `n`. -/
theorem integral_abs_empiricalCoord_le (n : ℕ) (j : ι) :
    ∫ ω, |empiricalSum Y P n ω j| ∂P ≤ coordSigma P (Y 0) j := by
  refine (integral_abs_le_sqrt_integral_sq (memLp_empiricalCoord hY hident n j)).trans ?_
  unfold coordSigma
  refine Real.sqrt_le_sqrt ?_
  have h := variance_eq_sub (memLp_empiricalCoord hY hident n j)
  simp only [Pi.pow_apply] at h
  rw [integral_empiricalCoord hY hident n j] at h
  have := variance_empiricalCoord_le hY hindep hident n j
  norm_num at h
  linarith

omit hident in
theorem measurable_empiricalSum (hYm : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (empiricalSum Y P n) := by
  refine measurable_of_coords fun j => ?_
  simp_rw [empiricalSum_apply (integrable_of_summableCoordL2 P hY)]
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_coord j).comp (hYm i)).sub_const _).const_mul _

end IID

/-! ### Tails -/

variable [DecidableEq ι]

/-- The tail `∑_{j ∉ F} σ_j`. -/
noncomputable def sigmaTail (P : Measure Ω) (Y : Ω → L1Seq ι) (F : Finset ι) : ℝ :=
  ∑' j, if j ∈ F then 0 else coordSigma P Y j

omit [IsProbabilityMeasure P] in
theorem sigmaTail_nonneg (Y : Ω → L1Seq ι) (F : Finset ι) : 0 ≤ sigmaTail P Y F :=
  tsum_nonneg fun j => by split_ifs <;> simp [coordSigma_nonneg]

theorem summable_sigmaTail_term {Y : Ω → L1Seq ι} (hY : SummableCoordL2 P Y) (F : Finset ι) :
    Summable fun j => if j ∈ F then 0 else coordSigma P Y j :=
  (summable_coordSigma hY).of_nonneg_of_le (fun j => by split_ifs <;> simp [coordSigma_nonneg])
    (fun j => by split_ifs <;> simp [coordSigma_nonneg])

omit [IsProbabilityMeasure P] in
theorem sigmaTail_eq_tsum_subtype (Y : Ω → L1Seq ι) (F : Finset ι) :
    sigmaTail P Y F = ∑' j : {x // x ∉ F}, coordSigma P Y j := by
  unfold sigmaTail
  have h : (∑' j : {x // x ∉ F}, coordSigma P Y j) =
      ∑' x : ↥((↑F : Set ι)ᶜ), coordSigma P Y x := rfl
  rw [h, tsum_subtype]
  refine tsum_congr fun j => ?_
  simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.mem_coe]
  split_ifs <;> simp_all

omit [IsProbabilityMeasure P] in
/-- The tails vanish along a covering exhaustion. -/
theorem tendsto_sigmaTail (Y : Ω → L1Seq ι) {F : ℕ → Finset ι} (hF : Monotone F)
    (hcov : ∀ j, ∃ k, j ∈ F k) : Tendsto (fun k => sigmaTail P Y (F k)) atTop (𝓝 0) := by
  simp_rw [sigmaTail_eq_tsum_subtype]
  exact (tendsto_tsum_compl_atTop_zero (coordSigma P Y)).comp
    (tendsto_atTop_finset_of_monotone hF hcov)

section IIDTail

variable [Countable ι] {Y : ℕ → Ω → L1Seq ι} (hY : SummableCoordL2 P (Y 0))
  (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
include hY hindep hident

/-- **The uniform tail estimate**: `E‖S_n − T_F S_n‖ ≤ ∑_{j∉F} σ_j` for every `n`. -/
theorem lintegral_enorm_sub_truncate_empirical_le (hYm : ∀ i, Measurable (Y i))
    (F : Finset ι) (n : ℕ) :
    ∫⁻ ω, ‖empiricalSum Y P n ω - truncate F (empiricalSum Y P n ω)‖ₑ ∂P ≤
      ENNReal.ofReal (sigmaTail P (Y 0) F) := by
  have hS : ∀ ω, ‖empiricalSum Y P n ω - truncate F (empiricalSum Y P n ω)‖ₑ =
      ∑' j, ENNReal.ofReal (if j ∈ F then 0 else |empiricalSum Y P n ω j|) := fun ω => by
    rw [← ofReal_norm, norm_sub_truncate,
      ENNReal.ofReal_tsum_of_nonneg (fun j => by split_ifs <;> simp)
        ((L1Seq.summable_abs (empiricalSum Y P n ω)).of_nonneg_of_le
          (fun j => by split_ifs <;> simp) (fun j => by split_ifs <;> simp))]
  simp_rw [hS]
  have hm : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal
      (if j ∈ F then 0 else |empiricalSum Y P n ω j|)) P := fun j => by
    by_cases hj : j ∈ F
    · simp only [hj, if_true]; exact aemeasurable_const
    · simp only [hj, if_false]
      exact ((measurable_coord j).comp
        (measurable_empiricalSum hY hYm n)).abs.ennreal_ofReal.aemeasurable
  rw [lintegral_tsum hm]
  calc ∑' j, ∫⁻ ω, ENNReal.ofReal (if j ∈ F then 0 else |empiricalSum Y P n ω j|) ∂P
      ≤ ∑' j, ENNReal.ofReal (if j ∈ F then 0 else coordSigma P (Y 0) j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        by_cases hj : j ∈ F
        · simp [hj]
        · simp only [hj, if_false]
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((memLp_empiricalCoord hY hident n j).integrable one_le_two).abs
            (Eventually.of_forall fun ω => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (integral_abs_empiricalCoord_le hY hindep hident n j)
    _ = ENNReal.ofReal (sigmaTail P (Y 0) F) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by split_ifs <;> simp [coordSigma_nonneg])
          (summable_sigmaTail_term hY F)).symm

end IIDTail

end Grammar
