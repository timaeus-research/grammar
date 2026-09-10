/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.L1SeqUpgrade

/-!
# Compactness in `ℓ¹` and tightness from uniform tails

* `isCompact_tailSet`: a norm-bounded set in `ℓ¹(ι, ℝ)` whose truncation tails
  `‖x − T_{F_m} x‖ ≤ ε_m` are uniformly small (`ε_m → 0`) is compact — closed, and totally bounded
  because its truncations lie in a compact finite-dimensional ball.
* `isTightMeasureSet_of_tails`: the laws of an `ℓ¹`-valued sequence with `E‖S_n‖ ≤ C` and uniform
  `L¹` tails `E‖S_n − T_k S_n‖ ≤ t_k`, `t_k → 0`, form a tight family (Markov on each constraint of
  a tail set with a summable probability budget).

These are the two inputs for extracting a weak limit of the empirical laws by Prokhorov's theorem.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Grammar

variable {ι : Type*} [DecidableEq ι]

/-- The tail set `{‖x‖ ≤ R} ∩ ⋂_m {‖x − T_{F_m} x‖ ≤ ε_m}`. -/
def tailSet (R : ℝ) (F : ℕ → Finset ι) (ε : ℕ → ℝ) : Set (L1Seq ι) :=
  {x | ‖x‖ ≤ R} ∩ ⋂ m, {x | ‖x - truncate (F m) x‖ ≤ ε m}

theorem isClosed_tailSet (R : ℝ) (F : ℕ → Finset ι) (ε : ℕ → ℝ) : IsClosed (tailSet R F ε) :=
  (isClosed_le continuous_norm continuous_const).inter (isClosed_iInter fun m =>
    isClosed_le ((continuous_id.sub (truncate (F m)).continuous).norm) continuous_const)

omit [DecidableEq ι] in
theorem norm_finiteCoords_le (F : Finset ι) (x : L1Seq ι) :
    ‖finiteCoords F x‖ ≤ ‖finiteCoords F‖ * ‖x‖ :=
  (finiteCoords F).le_opNorm x

theorem totallyBounded_tailSet (R : ℝ) (F : ℕ → Finset ι) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) : TotallyBounded (tailSet R F ε) := by
  rw [Metric.totallyBounded_iff]
  intro δ hδ
  obtain ⟨m, hm⟩ := (hε.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 3 by positivity))).exists
  -- the truncations lie in a compact finite-dimensional ball
  have hC : IsCompact ((embedF (F m)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (F m)) (‖finiteCoords (F m)‖ * R)) :=
    (isCompact_closedBall _ _).image (embedF (F m)).continuous
  obtain ⟨t, htfin, hcov⟩ := Metric.totallyBounded_iff.1 hC.totallyBounded (δ / 3) (by positivity)
  refine ⟨t, htfin, fun x hx => ?_⟩
  obtain ⟨hxR, hxtail⟩ := hx
  have hxm : ‖x - truncate (F m) x‖ ≤ ε m := Set.mem_iInter.1 hxtail m
  have hTx : truncate (F m) x ∈ (embedF (F m)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (F m)) (‖finiteCoords (F m)‖ * R) := by
    refine ⟨finiteCoords (F m) x, ?_, embedF_finiteCoords _ _⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_finiteCoords_le _ _).trans (mul_le_mul_of_nonneg_left hxR (norm_nonneg _))
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (hcov hTx)
  refine Set.mem_iUnion₂.2 ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball] at hy ⊢
  calc dist x y ≤ dist x (truncate (F m) x) + dist (truncate (F m) x) y := dist_triangle _ _ _
    _ < δ / 3 + δ / 3 := by
        refine add_lt_add_of_le_of_lt ?_ hy
        rw [dist_eq_norm]
        exact hxm.trans hm.le
    _ < δ := by linarith

/-- **The `ℓ¹` compactness criterion**: bounded with uniformly small tails ⇒ compact. -/
theorem isCompact_tailSet (R : ℝ) (F : ℕ → Finset ι) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    IsCompact (tailSet R F ε) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨totallyBounded_tailSet R F hε, (isClosed_tailSet R F ε).isComplete⟩

/-! ### Tightness -/

section Tight

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [DecidableEq ι] [IsProbabilityMeasure P] in
/-- Markov: `P(‖X‖ > R) ≤ E‖X‖ / R`, in the form needed below. -/
theorem measure_norm_gt_le {X : Ω → L1Seq ι} (hX : Measurable X) {C R : ℝ} (hR : 0 < R)
    (hC : ∫⁻ ω, ‖X ω‖ₑ ∂P ≤ ENNReal.ofReal C) {e : ℝ} (he0 : 0 ≤ e) (he : C ≤ e * R) :
    P {ω | R < ‖X ω‖} ≤ ENNReal.ofReal e := by
  have h1 : {ω | R < ‖X ω‖} ⊆ {ω | ENNReal.ofReal R ≤ ‖X ω‖ₑ} := fun ω hω => by
    change ENNReal.ofReal R ≤ ‖X ω‖ₑ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
  refine (measure_mono h1).trans ?_
  refine (meas_ge_le_lintegral_div hX.enorm.aemeasurable (by simpa using hR)
    ENNReal.ofReal_ne_top).trans ?_
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.ofReal_mul he0]
  exact hC.trans (ENNReal.ofReal_le_ofReal he)

omit [IsProbabilityMeasure P] in
/-- **Tightness from uniform tails**: the laws of a sequence with `E‖S_n‖ ≤ C` and
`E‖S_n − T_k S_n‖ ≤ t_k → 0` uniformly in `n` form a tight family. -/
theorem isTightMeasureSet_of_tails {S : ℕ → Ω → L1Seq ι} (hS : ∀ n, Measurable (S n)) {C : ℝ}
    (hnorm : ∀ n, ∫⁻ ω, ‖S n ω‖ₑ ∂P ≤ ENNReal.ofReal C) {F : ℕ → Finset ι} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0))
    (htail : ∀ k n, ∫⁻ ω, ‖S n ω - truncate (F k) (S n ω)‖ₑ ∂P ≤ ENNReal.ofReal (t k)) :
    IsTightMeasureSet {μ : Measure (L1Seq ι) | ∃ n, μ = P.map (S n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he0, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_or_ne ε ∞ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  have hk : ∀ m : ℕ, ∃ k, t k ≤ e / 2 / 2 / 2 ^ m * (1 / ((m : ℝ) + 1)) := fun m => by
    have hpos : 0 < e / 2 / 2 / 2 ^ m * (1 / ((m : ℝ) + 1)) := by positivity
    exact (ht.eventually (gt_mem_nhds hpos)).exists.imp fun k hk => hk.le
  choose k hk using hk
  set R : ℝ := 2 * max C 0 / e + 1 with hRdef
  have hR : 0 < R := by positivity
  refine ⟨tailSet R (fun m => F (k m)) (fun m => 1 / ((m : ℝ) + 1)),
    isCompact_tailSet _ _ tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hK := isClosed_tailSet R (fun m => F (k m)) (fun m => 1 / ((m : ℝ) + 1))
  rw [Measure.map_apply (hS n) hK.measurableSet.compl]
  have hsub : S n ⁻¹' (tailSet R (fun m => F (k m)) (fun m => 1 / ((m : ℝ) + 1)))ᶜ ⊆
      {ω | R < ‖S n ω‖} ∪
        ⋃ m : ℕ, {ω | 1 / ((m : ℝ) + 1) < ‖S n ω - truncate (F (k m)) (S n ω)‖} := by
    intro ω hω
    by_cases h : R < ‖S n ω‖
    · exact Or.inl h
    · refine Or.inr ?_
      have hω' : S n ω ∉ tailSet R (fun m => F (k m)) (fun m => 1 / ((m : ℝ) + 1)) := hω
      simp only [tailSet, Set.mem_inter_iff, Set.mem_iInter, not_and, not_forall] at hω'
      obtain ⟨m, hm⟩ := hω' (not_lt.1 h)
      exact Set.mem_iUnion.2 ⟨m, show 1 / ((m : ℝ) + 1) <
        ‖S n ω - truncate (F (k m)) (S n ω)‖ from not_le.1 hm⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h1 : P {ω | R < ‖S n ω‖} ≤ ENNReal.ofReal (e / 2) := by
    refine measure_norm_gt_le (hS n) hR (hnorm n) (by positivity) ?_
    have : e / 2 * R = max C 0 + e / 2 := by rw [hRdef]; field_simp
    rw [this]
    linarith [le_max_left C 0]
  have h2 : P (⋃ m : ℕ, {ω | 1 / ((m : ℝ) + 1) < ‖S n ω - truncate (F (k m)) (S n ω)‖}) ≤
      ENNReal.ofReal (e / 2) := by
    refine (measure_iUnion_le _).trans ?_
    calc ∑' m : ℕ, P {ω | 1 / ((m : ℝ) + 1) < ‖S n ω - truncate (F (k m)) (S n ω)‖}
        ≤ ∑' m, ENNReal.ofReal (e / 2 / 2 / 2 ^ m) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          exact measure_norm_gt_le
            ((continuous_id.sub (truncate (F (k m))).continuous).measurable.comp (hS n))
            (by positivity) (htail (k m) n) (by positivity) (hk m)
      _ = ENNReal.ofReal (∑' m, e / 2 / 2 / 2 ^ m) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
            (summable_geometric_two' _)).symm
      _ = ENNReal.ofReal (e / 2) := by rw [tsum_geometric_two']
  calc P {ω | R < ‖S n ω‖} +
        P (⋃ m : ℕ, {ω | 1 / ((m : ℝ) + 1) < ‖S n ω - truncate (F (k m)) (S n ω)‖})
      ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal e := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ ε := heε

end Tight

end Grammar
