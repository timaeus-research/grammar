/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TwoScaleDivision
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Two-scale division in probability (§20, the posterior expectation at the diagonal)

Random numerator and denominator `A_n, B_n` with random block coefficients `a_{j,n}, b_{j,n}`
and deterministic scales `x_n`, `g_n ≥ 1`, `x_n g_n → 0`: if the scaled blocks `a_{j,n}/g_n`,
`b_{j,n}/g_n` are bounded in probability, `b_{0,n}` is bounded below in probability, and the two
remainders `(A_n − Σ_{j<J} a_{j,n} x_n^j)/(x_n^J g_n)` are bounded in probability, then

★★★ `twoScale_div_boundedInProbSeq`:
`(A_n/B_n − Σ_{j<J} R_{j,n} x_n^j) / (x_n^J g_n^{J+1})` is bounded in probability,

with the pointwise quotient blocks `R_{j,n} = quotientBlocks (a_{·,n}) (b_{·,n}) j`.  The proof
localises to the event where the finitely many bounds hold with common constants and applies the
deterministic quantitative estimate `twoScale_div_bound` (consult #160, B2: use the proof structure,
not the `IsBigO` statement; the lower-tail condition on `b_0` is genuine since `0⁻¹ = 0`).

Applied with `x_n = n^{−1/Q}`, `g_n = (1 + log n)^D` to the empirical evidence with and without
insertion (blocks tight from the joint law of the coefficients, remainders `O_P` from the cutoff
expansions in probability at a cutoff `U > λ + J/Q`, the leading block bounded below from the
positivity of `b_{λ,m−1}`), this is the all-orders expansion of the posterior expectation at the
diagonal `N = n` with an `O_P` remainder.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Bounded in probability: `∀ ε > 0, ∃ C ≥ 0, eventually P{|Z_n| > C} ≤ ε`. -/
def BoundedInProbSeq (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, P {ω | C < |Z n ω|} ≤ ENNReal.ofReal ε

/-- Bounded below in probability: `∀ ε > 0, ∃ c > 0, eventually P{|Z_n| < c} ≤ ε`. -/
def BoundedBelowInProbSeq (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, P {ω | |Z n ω| < c} ≤ ENNReal.ofReal ε

/-- ★★★ **Two-scale division in probability.** -/
theorem twoScale_div_boundedInProbSeq {A B : ℕ → Ω → ℝ} {a b : ℕ → ℕ → Ω → ℝ} {x g : ℕ → ℝ}
    {J : ℕ} (hJ : 1 ≤ J) (hg : ∀ᶠ n in atTop, 1 ≤ g n)
    (hxg : Tendsto (fun n => x n * g n) atTop (𝓝 0))
    (ha : ∀ j < J, BoundedInProbSeq P fun n ω => a j n ω / g n)
    (hb : ∀ j < J, BoundedInProbSeq P fun n ω => b j n ω / g n)
    (hb0 : BoundedBelowInProbSeq P fun n ω => b 0 n ω)
    (hA : BoundedInProbSeq P fun n ω =>
      (A n ω - ∑ j ∈ range J, a j n ω * x n ^ j) / (x n ^ J * g n))
    (hB : BoundedInProbSeq P fun n ω =>
      (B n ω - ∑ j ∈ range J, b j n ω * x n ^ j) / (x n ^ J * g n)) :
    BoundedInProbSeq P fun n ω => (A n ω / B n ω -
      ∑ j ∈ range J, quotientBlocks (fun i => a i n ω) (fun i => b i n ω) j * x n ^ j) /
      (x n ^ J * g n ^ (J + 1)) := by
  intro ε hε
  obtain ⟨ε', hε'⟩ : ∃ ε', ε' = ε / (2 * J + 3) := ⟨_, rfl⟩
  have hε'pos : 0 < ε' := hε' ▸ div_pos hε (by positivity)
  -- constants for the finitely many hypotheses
  have ha' : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, j < J →
      P {ω | C < |a j n ω / g n|} ≤ ENNReal.ofReal ε' := fun j => by
    by_cases hj : j < J
    · obtain ⟨C, hC0, hC⟩ := ha j hj ε' hε'pos
      exact ⟨C, hC0, hC.mono fun n hn _ => hn⟩
    · exact ⟨0, le_rfl, Eventually.of_forall fun n hn => absurd hn hj⟩
  have hb' : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, j < J →
      P {ω | C < |b j n ω / g n|} ≤ ENNReal.ofReal ε' := fun j => by
    by_cases hj : j < J
    · obtain ⟨C, hC0, hC⟩ := hb j hj ε' hε'pos
      exact ⟨C, hC0, hC.mono fun n hn _ => hn⟩
    · exact ⟨0, le_rfl, Eventually.of_forall fun n hn => absurd hn hj⟩
  choose Ca hCa0 hCa using ha'
  choose Cb hCb0 hCb using hb'
  obtain ⟨c, hc, hcev⟩ := hb0 ε' hε'pos
  obtain ⟨KA, hKA0, hKAev⟩ := hA ε' hε'pos
  obtain ⟨KB, hKB0, hKBev⟩ := hB ε' hε'pos
  obtain ⟨Cab, hCab⟩ : ∃ Cab, Cab = ∑ j ∈ range J, (Ca j + Cb j) := ⟨_, rfl⟩
  have hCab0 : 0 ≤ Cab := hCab ▸ Finset.sum_nonneg fun j _ => add_nonneg (hCa0 j) (hCb0 j)
  have hCaCab : ∀ j < J, Ca j ≤ Cab := fun j hj => by
    rw [hCab]
    exact le_trans (le_add_of_nonneg_right (hCb0 j))
      (Finset.single_le_sum (f := fun i => Ca i + Cb i)
        (fun i _ => add_nonneg (hCa0 i) (hCb0 i)) (mem_range.2 hj))
  have hCbCab : ∀ j < J, Cb j ≤ Cab := fun j hj => by
    rw [hCab]
    exact le_trans (le_add_of_nonneg_left (hCa0 j))
      (Finset.single_le_sum (f := fun i => Ca i + Cb i)
        (fun i _ => add_nonneg (hCa0 i) (hCb0 i)) (mem_range.2 hj))
  obtain ⟨δ, C, hδ, hC0, hbound⟩ := twoScale_div_bound hJ hc hCab0 hKA0 hKB0
  refine ⟨C, hC0, ?_⟩
  have hev : ∀ᶠ n in atTop, |x n * g n| ≤ δ :=
    hxg.abs.eventually_le_const (by simpa using hδ)
  have hCaev : ∀ᶠ n in atTop, ∀ j ∈ range J,
      P {ω | Ca j < |a j n ω / g n|} ≤ ENNReal.ofReal ε' := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact (hCa j).mono fun n hn => hn (mem_range.1 hj)
  have hCbev : ∀ᶠ n in atTop, ∀ j ∈ range J,
      P {ω | Cb j < |b j n ω / g n|} ≤ ENNReal.ofReal ε' := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact (hCb j).mono fun n hn => hn (mem_range.1 hj)
  filter_upwards [hg, hev, hCaev, hCbev, hcev, hKAev, hKBev] with n hgn hxgn hCan hCbn hcn hKAn
    hKBn
  have hgn0 : 0 < g n := by linarith
  -- the bad event
  obtain ⟨Bad, hBad⟩ : ∃ Bad : Set Ω, Bad =
      (⋃ j ∈ range J, {ω | Ca j < |a j n ω / g n|}) ∪
      (⋃ j ∈ range J, {ω | Cb j < |b j n ω / g n|}) ∪ {ω | |b 0 n ω| < c} ∪
      {ω | KA < |(A n ω - ∑ j ∈ range J, a j n ω * x n ^ j) / (x n ^ J * g n)|} ∪
      {ω | KB < |(B n ω - ∑ j ∈ range J, b j n ω * x n ^ j) / (x n ^ J * g n)|} := ⟨_, rfl⟩
  have hsub : {ω | C < |(A n ω / B n ω -
      ∑ j ∈ range J, quotientBlocks (fun i => a i n ω) (fun i => b i n ω) j * x n ^ j) /
      (x n ^ J * g n ^ (J + 1))|} ⊆ Bad := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hbad
    rw [hBad] at hbad
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_lt]
      at hbad
    obtain ⟨⟨⟨⟨hna, hnb⟩, hnc⟩, hnA⟩, hnB⟩ := hbad
    -- `x n ≠ 0`, else the quotient error is `0`
    have hx0 : x n ≠ 0 := by
      intro hx0
      rw [hx0, zero_pow (by omega : J ≠ 0), zero_mul, div_zero, abs_zero] at hω
      linarith
    have hxJg : 0 < |x n| ^ J * g n := mul_pos (pow_pos (abs_pos.2 hx0) _) hgn0
    have hxJg1 : 0 < |x n| ^ J * g n ^ (J + 1) :=
      mul_pos (pow_pos (abs_pos.2 hx0) _) (pow_pos hgn0 _)
    have habn : ∀ j < J, |a j n ω| ≤ Cab * g n ∧ |b j n ω| ≤ Cab * g n := by
      intro j hj
      have h1 := hna j (mem_range.2 hj)
      have h2 := hnb j (mem_range.2 hj)
      rw [abs_div, abs_of_pos hgn0, div_le_iff₀ hgn0] at h1 h2
      exact ⟨h1.trans (mul_le_mul_of_nonneg_right (hCaCab j hj) hgn0.le),
        h2.trans (mul_le_mul_of_nonneg_right (hCbCab j hj) hgn0.le)⟩
    have hb0n : c ≤ |b 0 n ω| := hnc
    have hKAn' : |A n ω - ∑ j ∈ range J, a j n ω * x n ^ j| ≤ KA * (|x n| ^ J * g n) := by
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hgn0, div_le_iff₀ hxJg] at hnA
      exact hnA
    have hKBn' : |B n ω - ∑ j ∈ range J, b j n ω * x n ^ j| ≤ KB * (|x n| ^ J * g n) := by
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hgn0, div_le_iff₀ hxJg] at hnB
      exact hnB
    have hxgn' : |x n| * g n ≤ δ := by
      rw [abs_mul, abs_of_pos hgn0] at hxgn
      exact hxgn
    have h := hbound (A n ω) (B n ω) (x n) (g n) (fun i => a i n ω) (fun i => b i n ω) hgn hxgn'
      habn hb0n hKAn' hKBn'
    rw [abs_div, abs_mul, abs_pow, abs_of_pos (pow_pos hgn0 _), lt_div_iff₀ hxJg1] at hω
    linarith
  have hmeas : P Bad ≤ ENNReal.ofReal ε := by
    rw [hBad]
    have hJε : ∑ j ∈ range J, ENNReal.ofReal ε' = ENNReal.ofReal (J * ε') := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    have hUa : P (⋃ j ∈ range J, {ω | Ca j < |a j n ω / g n|}) ≤ ENNReal.ofReal (J * ε') := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      rw [← hJε]
      exact Finset.sum_le_sum fun j hj => hCan j hj
    have hUb : P (⋃ j ∈ range J, {ω | Cb j < |b j n ω / g n|}) ≤ ENNReal.ofReal (J * ε') := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      rw [← hJε]
      exact Finset.sum_le_sum fun j hj => hCbn j hj
    have hJε0 : 0 ≤ (J : ℝ) * ε' := mul_nonneg (Nat.cast_nonneg _) hε'pos.le
    calc P (_ ∪ _ ∪ _ ∪ _ ∪ _)
        ≤ P (_ ∪ _ ∪ _ ∪ _) + P _ := measure_union_le _ _
      _ ≤ P (_ ∪ _ ∪ _) + P _ + P _ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ P (_ ∪ _) + P _ + P _ + P _ :=
          add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ ≤ P _ + P _ + P _ + P _ + P _ :=
          add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl) le_rfl
      _ ≤ ENNReal.ofReal (J * ε') + ENNReal.ofReal (J * ε') + ENNReal.ofReal ε' +
            ENNReal.ofReal ε' + ENNReal.ofReal ε' :=
          add_le_add (add_le_add (add_le_add (add_le_add hUa hUb) hcn) hKAn) hKBn
      _ = ENNReal.ofReal (J * ε' + J * ε' + ε' + ε' + ε') := by
          rw [← ENNReal.ofReal_add hJε0 hJε0, ← ENNReal.ofReal_add (by linarith) hε'pos.le,
            ← ENNReal.ofReal_add (by linarith) hε'pos.le,
            ← ENNReal.ofReal_add (by linarith) hε'pos.le]
      _ = ENNReal.ofReal ε := by
          congr 1
          rw [hε']
          field_simp
          ring
  exact (measure_mono hsub).trans hmeas

end Grammar
