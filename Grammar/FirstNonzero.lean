/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationAssembly

/-!
# The first nonzero coefficient in the asymptotic order (Programme Q, N1, unit 306)

Programme P proves a zero limit at the first candidate when the assembled coefficient cancels.
This file supplies the order theory needed to say what happens next. Coefficient systems are
`c : ℝ → ℕ → ℝ` (coefficient of `N^{-μ}(log N)^j`), the asymptotic order is
`precedes p q ↔ p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)` (smaller exponent first, larger log power first
at equal exponents), and the **admissible domain** of a lattice `Q⁻¹ℕ` with degree bound `D` is
`admissible D Q = {p | p.1 ∈ Q⁻¹ℕ ∧ p.2 ≤ D}`. `precedes` is not well-founded on `ℝ × ℕ`; selection
is done on the finite index set below a cutoff and lifted:

* `exists_first_nonzero_finset`: a finite set with a nonzero coefficient has a first nonzero pair
  (minimal exponent among the nonzero pairs, then maximal log degree);
* `indexSet_pred_closed`: the index set below a cutoff `L` contains every admissible predecessor of
  each of its members (since `q.1 ≤ p.1 < L`), so the finite selection is globally first;
* `first_nonzero_unique`: the globally first nonzero admissible pair is unique (any two distinct
  pairs are comparable), hence cutoff coherence;
* `absPredSum_eq_zero_of_first`: at the first nonzero pair the predecessor sum vanishes.

Regression: at a fixed exponent the larger log degree wins (`first_nonzero_snd_ge`). The
selection theorem says nothing about the size of the coefficient; and "no nonzero coefficient
below any cutoff" is the flat case, treated in unit 308. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The admissible pairs of a lattice with denominator `Q` and degree bound `D`. -/
def admissible (D Q : ℕ) : Set (ℝ × ℕ) := {p | (∃ m : ℕ, p.1 = (m : ℝ) / Q) ∧ p.2 ≤ D}

/-- Distinct pairs are comparable in the asymptotic order. -/
theorem precedes_or_precedes_of_ne {p q : ℝ × ℕ} (hpq : p ≠ q) : precedes p q ∨ precedes q p := by
  unfold precedes
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
    · exact absurd (Prod.ext h h2) hpq
    · exact Or.inl (Or.inr ⟨h, h2⟩)
  · exact Or.inr (Or.inl h)

/-- **Finite selection**: a finite set carrying a nonzero coefficient has a first nonzero pair. -/
theorem exists_first_nonzero_finset (S : Finset (ℝ × ℕ)) (c : ℝ → ℕ → ℝ)
    (hne : ∃ p ∈ S, c p.1 p.2 ≠ 0) :
    ∃ p ∈ S, c p.1 p.2 ≠ 0 ∧ ∀ q ∈ S, precedes q p → c q.1 q.2 = 0 := by
  classical
  set T := S.filter fun p => c p.1 p.2 ≠ 0 with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, hp, hc⟩ := hne
    exact ⟨p, Finset.mem_filter.2 ⟨hp, hc⟩⟩
  -- minimal exponent among the nonzero pairs
  obtain ⟨p₀, hp₀, hmin⟩ := T.exists_min_image (fun p => p.1) hTne
  set U := T.filter fun p => p.1 = p₀.1 with hU
  have hUne : U.Nonempty := ⟨p₀, Finset.mem_filter.2 ⟨hp₀, rfl⟩⟩
  -- maximal log degree at that exponent
  obtain ⟨p, hpU, hmax⟩ := U.exists_max_image (fun p => p.2) hUne
  have hpT : p ∈ T := (Finset.mem_filter.1 hpU).1
  have hp1 : p.1 = p₀.1 := (Finset.mem_filter.1 hpU).2
  refine ⟨p, (Finset.mem_filter.1 hpT).1, (Finset.mem_filter.1 hpT).2, fun q hq hqp => ?_⟩
  by_contra hcq
  have hqT : q ∈ T := Finset.mem_filter.2 ⟨hq, hcq⟩
  rcases hqp with hlt | ⟨heq, hgt⟩
  · have := hmin q hqT
    linarith [hlt, hp1]
  · have hqU : q ∈ U := Finset.mem_filter.2 ⟨hqT, by rw [heq, hp1]⟩
    have := hmax q hqU
    omega

/-- The index set below `L` lies in the admissible domain. -/
theorem indexSet_subset_admissible {D Q : ℕ} (hQ : 0 < Q) {L : ℝ} {p : ℝ × ℕ}
    (hp : p ∈ indexSet D Q L) : p ∈ admissible D Q := by
  obtain ⟨h1, h2⟩ := mem_indexSet_iff.1 hp
  obtain ⟨hm, -⟩ := (mem_latticeBelow_iff hQ).1 h1
  exact ⟨hm, Nat.lt_succ_iff.1 h2⟩

/-- **Predecessor closure**: every admissible predecessor of a member of the index set below `L`
lies in that index set. -/
theorem indexSet_pred_closed {D Q : ℕ} (hQ : 0 < Q) {L : ℝ} {p q : ℝ × ℕ}
    (hp : p ∈ indexSet D Q L) (hq : q ∈ admissible D Q) (hqp : precedes q p) :
    q ∈ indexSet D Q L := by
  obtain ⟨h1, -⟩ := mem_indexSet_iff.1 hp
  obtain ⟨-, hpL⟩ := (mem_latticeBelow_iff hQ).1 h1
  obtain ⟨⟨m, hm⟩, hqD⟩ := hq
  have hq1 : q.1 ≤ p.1 := by
    rcases hqp with hlt | ⟨heq, -⟩
    · exact hlt.le
    · exact heq.le
  refine mem_indexSet_iff.2 ⟨?_, Nat.lt_succ_of_le hqD⟩
  rw [hm]
  exact mem_latticeBelow hQ (by rw [← hm]; exact lt_of_le_of_lt hq1 hpL)

/-- **Global first nonzero pair**: a nonzero coefficient below some cutoff yields a first nonzero
admissible pair, first among all admissible pairs. -/
theorem exists_first_nonzero {D Q : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {L : ℝ}
    (hne : ∃ p ∈ indexSet D Q L, c p.1 p.2 ≠ 0) :
    ∃ p ∈ admissible D Q, c p.1 p.2 ≠ 0 ∧ ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0 := by
  obtain ⟨p, hpS, hcp, hfirst⟩ := exists_first_nonzero_finset (indexSet D Q L) c hne
  exact ⟨p, indexSet_subset_admissible hQ hpS, hcp, fun q hq hqp =>
    hfirst q (indexSet_pred_closed hQ hpS hq hqp) hqp⟩

/-- **Uniqueness** of the first nonzero admissible pair (cutoff coherence). -/
theorem first_nonzero_unique {D Q : ℕ} (c : ℝ → ℕ → ℝ) {p p' : ℝ × ℕ}
    (hp : p ∈ admissible D Q) (hcp : c p.1 p.2 ≠ 0)
    (hfirst : ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0)
    (hp' : p' ∈ admissible D Q) (hcp' : c p'.1 p'.2 ≠ 0)
    (hfirst' : ∀ q ∈ admissible D Q, precedes q p' → c q.1 q.2 = 0) : p = p' := by
  by_contra hne
  rcases precedes_or_precedes_of_ne hne with h | h
  · exact hcp (hfirst' p hp h)
  · exact hcp' (hfirst p' hp' h)

/-- The unique-existence form. -/
theorem existsUnique_first_nonzero {D Q : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {L : ℝ}
    (hne : ∃ p ∈ indexSet D Q L, c p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible D Q ∧ c p.1 p.2 ≠ 0 ∧
      ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0 := by
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ c hne
  refine ⟨p, ⟨hp, hcp, hfirst⟩, fun p' ⟨hp', hcp', hfirst'⟩ => ?_⟩
  exact (first_nonzero_unique c hp hcp hfirst hp' hcp' hfirst').symm

/-- At the first nonzero admissible pair the predecessor sum vanishes. -/
theorem absPredSum_eq_zero_of_first {D Q : ℕ} (hQ : 0 < Q) (c : ℝ → ℕ → ℝ) {p : ℝ × ℕ}
    (hfirst : ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0) (N : ℝ) :
    absPredSum Q D c p.1 p.2 N = 0 := by
  unfold absPredSum
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨hqi, hprec⟩ := mem_predSet_iff.1 hq
  unfold absTerm
  rw [hfirst q (indexSet_subset_admissible hQ hqi) hprec, zero_mul]

/-- **Regression**: at the exponent of the first nonzero pair, every nonzero admissible coefficient
has log degree at most that of the first pair (the larger log degree wins). -/
theorem first_nonzero_snd_ge {D Q : ℕ} (c : ℝ → ℕ → ℝ) {p : ℝ × ℕ}
    (hfirst : ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0) {q : ℝ × ℕ}
    (hq : q ∈ admissible D Q) (hq1 : q.1 = p.1) (hcq : c q.1 q.2 ≠ 0) : q.2 ≤ p.2 := by
  by_contra hgt
  rw [not_le] at hgt
  exact hcq (hfirst q hq (Or.inr ⟨hq1, hgt⟩))

end Grammar
