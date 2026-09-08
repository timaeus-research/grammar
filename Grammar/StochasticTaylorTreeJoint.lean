/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticTaylorTree

/-!
# Joint convergence of several ordered remainders; predecessor-set interface (Stage S8)

Unit 277 (review v28 nonblocking exports). (i) `mem_predSet_iff` and the cutoff independence of
the predecessor set: filtering the index set of any cutoff `L > μ` by `≺ (μ, j)` gives the same
finite set (`predSet_eq_filter`). (ii) The uniform-on-balls argument for vector-valued errors
(`tendstoInMeasure_zero_of_uniform_on_balls'`), and the **joint** version of Headline XXXV: for
finitely many targets `(μ_i, j_i)` the vector of ordered normalised remainders converges in
distribution to the vector of limiting coefficients (`tendstoInDistribution_orderedRemainderVec`),
which is what later division and assembly steps consume.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

open scoped Classical

/-! ### The predecessor set -/

theorem mem_predSet_iff {n Q : ℕ} {μ : ℝ} {j : ℕ} {p : ℝ × ℕ} :
    p ∈ predSet n Q μ j ↔ p ∈ indexSet n Q (μ + 1) ∧ precedes p (μ, j) := by
  unfold predSet; exact Finset.mem_filter

theorem mem_latticeBelow_iff {Q : ℕ} (hQ : 0 < Q) {L ν : ℝ} :
    ν ∈ latticeBelow Q L ↔ (∃ m : ℕ, ν = (m : ℝ) / Q) ∧ ν < L := by
  constructor
  · intro hν
    refine ⟨?_, lt_of_mem_latticeBelow hQ hν⟩
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hν
    exact ⟨m, rfl⟩
  · rintro ⟨⟨m, rfl⟩, hlt⟩
    exact mem_latticeBelow hQ hlt

theorem mem_indexSet_iff {n Q : ℕ} {L : ℝ} {p : ℝ × ℕ} :
    p ∈ indexSet n Q L ↔ p.1 ∈ latticeBelow Q L ∧ p.2 < n + 1 := by
  unfold indexSet
  rw [Finset.mem_product, Finset.mem_range]

/-- **Cutoff independence**: the predecessor set is the `≺ (μ,j)`-filter of the index set of any
cutoff `L > μ`. -/
theorem predSet_eq_filter {n Q : ℕ} (hQ : 0 < Q) {μ L : ℝ} (hL : μ < L) (j : ℕ) :
    predSet n Q μ j = (indexSet n Q L).filter fun p => precedes p (μ, j) := by
  ext p
  rw [mem_predSet_iff, Finset.mem_filter, mem_indexSet_iff, mem_indexSet_iff,
    mem_latticeBelow_iff hQ, mem_latticeBelow_iff hQ]
  have hle : precedes p (μ, j) → p.1 ≤ μ := by
    rintro (h | ⟨h, -⟩)
    · exact h.le
    · exact h.le
  constructor
  · rintro ⟨⟨⟨hm, -⟩, hn⟩, hp⟩
    exact ⟨⟨⟨hm, lt_of_le_of_lt (hle hp) hL⟩, hn⟩, hp⟩
  · rintro ⟨⟨⟨hm, -⟩, hn⟩, hp⟩
    exact ⟨⟨⟨hm, lt_of_le_of_lt (hle hp) (by linarith)⟩, hn⟩, hp⟩

/-! ### Joint convergence -/

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}

/-- Vector-valued version of `tendstoInMeasure_zero_of_uniform_on_balls`. -/
theorem tendstoInMeasure_zero_of_uniform_on_balls' {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : ι → Ω → E) (X : ι → Ω → DataSpace d)
    (hf : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ ω, ‖X n ω‖ ≤ M → ‖f n ω‖ ≤ ε)
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  filter_upwards [hev, hf M hM (ε / 2) (half_pos hε)] with n hn hfn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [mem_setOf_eq, sub_zero] at hω ⊢
  by_contra hcon
  have := hfn ω (not_lt.1 hcon)
  linarith

/-- The vector of ordered normalised remainders at the targets `F i = (μ_i, j_i)`. -/
noncomputable def orderedRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {m : ℕ}
    (F : Fin m → ℝ × ℕ) (x : DataSpace (n + 1)) (N : ℝ) : Fin m → ℝ :=
  fun i => orderedRemainder n h k β b x (F i).1 (F i).2 N

theorem measurable_orderedRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : DataSpace (n + 1) => orderedRemainderVec n h k β b F x N :=
  measurable_pi_lambda _ fun i => measurable_orderedRemainder n h k hk β hβ hb (F i).1 (F i).2 hN

/-- The vector of remainders minus the vector of coefficients tends to zero in probability. -/
theorem tendstoInMeasure_orderedRemainderVec_sub (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (hF : ∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => orderedRemainderVec n h k β b F (X i ω) (Nseq i) -
      dataCoeffVec n h k β b F (X i ω)) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls' _ X (fun M hM ε hε => ?_)
    (dataNormBounded_of_tendstoInDistribution X Z hX)
  have hall : ∀ i : Fin m, ∀ᶠ N in atTop, ∀ x ∈ Metric.closedBall (0 : DataSpace (n + 1)) M,
      dist (dataBoxCoeff n h k β b x (F i).1 (F i).2)
        (orderedRemainder n h k β b x (F i).1 (F i).2 N) < ε := fun i =>
    Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_orderedRemainder n h k hk β hβ hb (hF i).1 (hF i).2 M) ε hε
  have hev := hN.eventually (Filter.eventually_all.2 hall)
  filter_upwards [hev] with i hi ω hω
  rw [pi_norm_le_iff_of_nonneg hε.le]
  intro t
  have := hi t (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  simpa [orderedRemainderVec, dataCoeffVec, Real.norm_eq_abs] using this.le

variable [l.IsCountablyGenerated]

/-- **Headline XXXV (joint form)**: finitely many ordered normalised remainders converge jointly
in distribution to the vector of limiting coefficients. -/
theorem tendstoInDistribution_orderedRemainderVec (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (hF : ∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => orderedRemainderVec n h k β b F (X i ω) (Nseq i)) l
      (fun ω => dataCoeffVec n h k β b F (Z ω)) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_dataCoeffVec n h k hk β hβ hb F X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_orderedRemainderVec n h k hk β hβ hb F (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_orderedRemainderVec_sub n h k hk β hβ hb F hF X Z hX Nseq hN

end Grammar
