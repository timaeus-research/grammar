# Fidelity review v37 — units 306–308 (Programme Q, N1: first nonzero term after cancellation; flatness)

Context: your #38 design (Programme Q, cap 24; N1 budget 6 with four required outputs — finite first-nonzero selection; independence from enlarging the cutoff; the asymptotic equivalent specialised to the assembled population integral, with the decomposition error negligible at the SELECTED scale; flatness `∀ L, 𝒵_pop = o(N^{-L})` under all-cutoff coefficient vanishing, requiring expansions at arbitrarily large cutoffs and NOT concluding exact zero). Regression you asked for: at fixed μ the larger j wins; flat is not zero. Units 306–308 implement N1 in 3 units. Everything compiles (branch `tide/programme-q`, base grammar main `88e5ba0`; no `sorry`, no added `axiom`).

Frozen interfaces (beyond earlier reviews):
```lean
def precedes (p q : ℝ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)
noncomputable def indexSet (n Q : ℕ) (L : ℝ) : Finset (ℝ × ℕ) := latticeBelow Q L ×ˢ Finset.range (n + 1)
theorem mem_indexSet_iff {n Q : ℕ} {L : ℝ} {p : ℝ × ℕ} : p ∈ indexSet n Q L ↔ p.1 ∈ latticeBelow Q L ∧ p.2 < n + 1
theorem mem_latticeBelow_iff {Q : ℕ} (hQ : 0 < Q) {L ν : ℝ} : ν ∈ latticeBelow Q L ↔ (∃ m : ℕ, ν = (m : ℝ) / Q) ∧ ν < L
theorem mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L : ℝ} {m : ℕ} (hm : (m : ℝ) / Q < L) : (m : ℝ) / Q ∈ latticeBelow Q L
noncomputable def predSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) := (indexSet n Q (μ + 1)).filter fun p => precedes p (μ, j)
theorem mem_predSet_iff : p ∈ predSet n Q μ j ↔ p ∈ indexSet n Q (μ + 1) ∧ precedes p (μ, j)
noncomputable def absTerm (c : ℝ → ℕ → ℝ) (N : ℝ) (p : ℝ × ℕ) : ℝ := c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)
noncomputable def absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : ℝ := ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j
theorem absSpectralSum_eq_sum_indexSet (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : absSpectralSum Q D c L N = ∑ p ∈ indexSet D Q L, absTerm c N p
noncomputable def absPredSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := ∑ p ∈ predSet D Q μ j, absTerm c N p
noncomputable def abstractRemainder (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := (Z N - absPredSum Q D c μ j N) / (N ^ (-μ) * Real.log N ^ j)
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop := ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop, |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)
theorem tendsto_abstractRemainder {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) : Tendsto (fun N => abstractRemainder Q D Z c μ j N) atTop (𝓝 (c μ j))
theorem tendsto_cutoff_ratio (n : ℕ) {L μ : ℝ} (hμL : μ < L) : Tendsto (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-μ)) atTop (𝓝 0)
theorem gCutoff_bound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {L : ℝ} (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) {R : ℝ} {x : JointData K n} (hx : ‖x‖ ≤ R) :
    |gInt ν h k β b x N - absSpectralSum (commonQ k) (commonD n) (gCoeff ν h k β b x) L N| ≤ gCutoffConst ν h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ (commonD n))
noncomputable def boxScale {d : ℕ} (k : Fin d → ℕ) (b N : ℝ) : ℝ := N * b ^ (2 * ∑ i, k i)
theorem isEquivalent_normalForm_pop (hk) (hβ) (hb : ∀ I, 0 < b I) (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N) (hE : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0)) (hpred : ∀ N, absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b x) μ₀ j N = 0) (hc : gCoeff ν h k β b x μ₀ j ≠ 0) : Zpop ~[atTop] fun N => gCoeff ν h k β b x μ₀ j * (N ^ (-μ₀) * Real.log N ^ j)
theorem tendsto_target_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (μ₀ : ℝ) (j : ℕ) : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0)
-- TaylorTreeConclusion.remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N → |familyPhaseIntegralBox n h k β N b cξ cη − b^(∑h+(n+1)) * ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) * ∑ j ∈ range (n+1), C μ j * log(boxScale k b N)^j| ≤ b^(…) * cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) * (boxScale k b N ^ (-L) * (1 + log (boxScale k b N))^n)
theorem boxScale_one {d : ℕ} (k : Fin d → ℕ) (N : ℝ) : boxScale k 1 N = N
```

## The three units (complete files)

### Grammar/FirstNonzero.lean
```lean
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
```

### Grammar/FirstNonzeroAsymptotic.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FirstNonzero

/-!
# The first nonzero term is the leading term (Programme Q, N1, unit 307)

For any finite-cutoff expansion (`CutoffExpansion Q D Z c`) the ordered normalised remainder at an
admissible target converges to the target coefficient (Programme S, `tendsto_abstractRemainder`);
at the first nonzero admissible pair the predecessor sum vanishes, so
```
Z(N) ∼ c_p · N^{-p.1} (log N)^{p.2}                 (isEquivalent_first_nonzero_of_cutoffExpansion)
```
and the pair is unique (`existsUnique_first_nonzero_isEquivalent`). Specialisations:

* **chart level**: the population Taylor tree on the unit box is a `CutoffExpansion`
  (`cutoffExpansion_of_conclusion`), so the population integral is asymptotically its first nonzero
  term (`population_first_nonzero_chart`);
* **assembled**: for `𝒵_pop = ∑_I 𝒵^I + E` with `E` negligible at **every** admissible scale (in
  particular exponentially small), the assembled integral is asymptotically its first nonzero
  assembled term (`population_first_nonzero_assembled`, `_exp`). The residual hypothesis is at all
  scales because the selected pair is existential: negligibility at Programme P's first candidate is
  not enough after a cancellation.

Non-claims: the theorems presuppose SOME nonzero coefficient below some cutoff; the flat alternative
is unit 308. Nothing is said about the size of the selected coefficient, and the selected exponent
is
not identified with any RLCT. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- A tendsto of the normalised remainder to a nonzero coefficient, with vanishing predecessor sum,
is an asymptotic equivalence. -/
theorem isEquivalent_of_tendsto_remainder {Z : ℝ → ℝ} {c μ : ℝ} {j : ℕ}
    (ht : Tendsto (fun N => Z N / (N ^ (-μ) * Real.log N ^ j)) atTop (𝓝 c)) (hc : c ≠ 0) :
    Z ~[atTop] fun N => c * (N ^ (-μ) * Real.log N ^ j) := by
  have h1 := ht.div_const c
  rw [div_self hc] at h1
  refine isEquivalent_of_tendsto_one (h1.congr' (Eventually.of_forall fun N => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- **First nonzero term of a finite-cutoff expansion.** -/
theorem isEquivalent_first_nonzero_of_cutoffExpansion {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {p : ℝ × ℕ} (hp : p ∈ admissible D Q)
    (hcp : c p.1 p.2 ≠ 0) (hfirst : ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0) :
    Z ~[atTop] fun N => c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
  have ht := tendsto_abstractRemainder hQ h hp.1 hp.2
  refine isEquivalent_of_tendsto_remainder (ht.congr' (Eventually.of_forall fun N => ?_)) hcp
  unfold abstractRemainder
  rw [absPredSum_eq_zero_of_first hQ c hfirst, sub_zero]

/-- **Unique first nonzero pair with its asymptotic equivalence.** -/
theorem existsUnique_first_nonzero_isEquivalent {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {L : ℝ}
    (hne : ∃ p ∈ indexSet D Q L, c p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible D Q ∧ c p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0) ∧
      Z ~[atTop] fun N => c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ c hne
  refine ⟨p, ⟨hp, hcp, hfirst, isEquivalent_first_nonzero_of_cutoffExpansion hQ h hp hcp hfirst⟩,
    fun p' hp' => ?_⟩
  exact (first_nonzero_unique c hp hcp hfirst hp'.1 hp'.2.1 hp'.2.2.1).symm

/-- The Taylor-tree conclusion on the unit box is a finite-cutoff expansion. -/
theorem cutoffExpansion_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ} (hC : TaylorTreeConclusion n h k β 1 cξ cη C) :
    CutoffExpansion (latticeQ k) n (fun N => familyPhaseIntegralBox n h k β N 1 cξ cη) C := by
  intro L hL
  refine ⟨cutoffBound n k β L (CoeffFamily.scale cξ 1 0) (CoeffFamily.mass (CoeffFamily.scale cη 1))
    (CoeffFamily.mass (CoeffFamily.scale cξ 1)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hrem := hC.remainder L hL N (by linarith) (by rw [boxScale_one]; exact hN)
  rw [boxScale_one, one_pow, one_mul, one_mul] at hrem
  exact hrem

/-- **Chart level**: the population integral is asymptotically its first nonzero term. -/
theorem population_first_nonzero_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) {cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 0 cη C) {η : (Fin (n + 1) → ℝ) → ℝ}
    (hI : ∀ N, familyPhaseIntegralBox n h k β N 1 0 cη =
      origPhaseIntegral n h k β N 1 (fun _ => 0) η) {L : ℝ}
    (hne : ∃ p ∈ indexSet n (latticeQ k) L, C p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible n (latticeQ k) ∧ C p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible n (latticeQ k), precedes q p → C q.1 q.2 = 0) ∧
      (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop]
        fun N => C p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
  have hcut := cutoffExpansion_of_conclusion n h k β hC
  have hcut' : CutoffExpansion (latticeQ k) n
      (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) C := by
    have : (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) =
        fun N => familyPhaseIntegralBox n h k β N 1 0 cη := funext fun N => (hI N).symm
    rw [this]
    exact hcut
  exact existsUnique_first_nonzero_isEquivalent (latticeQ_pos k hk) hcut' hne

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- **Assembled**: with a residual negligible at every admissible scale, the assembled population
integral is asymptotically its first nonzero assembled term. -/
theorem population_first_nonzero_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) (x : JointData K n) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : ∀ (μ : ℝ) (j : ℕ), Tendsto (fun N => E N / (N ^ (-μ) * Real.log N ^ j)) atTop (𝓝 0))
    {L : ℝ} (hne : ∃ p ∈ indexSet (commonD n) (commonQ k) L, gCoeff ν h k β b x p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible (commonD n) (commonQ k) ∧ gCoeff ν h k β b x p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible (commonD n) (commonQ k), precedes q p → gCoeff ν h k β b x q.1 q.2 = 0) ∧
      Zpop ~[atTop] fun N => gCoeff ν h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
  have hQ := commonQ_pos k hk
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ (gCoeff ν h k β b x) hne
  refine ⟨p, ⟨hp, hcp, hfirst, ?_⟩, fun p' hp' =>
    (first_nonzero_unique _ hp hcp hfirst hp'.1 hp'.2.1 hp'.2.2.1).symm⟩
  exact isEquivalent_normalForm_pop ν h k β b hk hβ hb x hp.1 hp.2 Zpop E hdecomp (hE p.1 p.2)
    (absPredSum_eq_zero_of_first hQ _ hfirst) hcp

/-- The exponentially-small-residual form. -/
theorem population_first_nonzero_assembled_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (hb : ∀ I, 0 < b I) (x : JointData K n) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    {L : ℝ} (hne : ∃ p ∈ indexSet (commonD n) (commonQ k) L, gCoeff ν h k β b x p.1 p.2 ≠ 0) :
    ∃! p : ℝ × ℕ, p ∈ admissible (commonD n) (commonQ k) ∧ gCoeff ν h k β b x p.1 p.2 ≠ 0 ∧
      (∀ q ∈ admissible (commonD n) (commonQ k), precedes q p → gCoeff ν h k β b x q.1 q.2 = 0) ∧
      Zpop ~[atTop] fun N => gCoeff ν h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) :=
  population_first_nonzero_assembled ν h k β b hk hβ hb x Zpop E hdecomp
    (fun μ j => tendsto_target_of_exp E hε hE μ j) hne

end Grammar
```

### Grammar/Flatness.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FirstNonzeroAsymptotic

/-!
# Superpolynomial flatness under all-cutoff coefficient vanishing (Programme Q, N1, unit 308)

The alternative to a first nonzero coefficient: if every admissible coefficient of a finite-cutoff
expansion vanishes, then `Z(N) = o(N^{-L})` for every real `L` (`flat_of_cutoffExpansion`), because
the expansion at cutoff `L+1` reduces to its remainder `O(N^{-(L+1)}(1+log N)^D)`. Assembled: the
global integral of zero-noise (or any) joint data is a finite-cutoff expansion
(`cutoffExpansion_gInt`, from the uniform assembled cutoff bound), so `𝒵_pop = ∑_I 𝒵^I + E` with all
assembled coefficients zero and `E = o(N^{-L})` for all `L` is itself `o(N^{-L})` for all `L`
(`population_flat`, `_exp`).

**Flat does not mean zero**: `e^{-N}` is `o(N^{-L})` for every `L` and never vanishes
(`exp_neg_flat`, `exp_neg_ne_zero`); the flat branch asserts nothing beyond superpolynomial decay.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Flatness**: all admissible coefficients zero ⇒ `Z = o(N^{-L})` for every `L`. -/
theorem flat_of_cutoffExpansion {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) (hzero : ∀ p ∈ admissible D Q, c p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Z N / N ^ (-L)) atTop (𝓝 0) := by
  have hL : 0 < L + 1 ∨ True := Or.inr trivial
  -- use the cutoff `max (L+1) 1 > 0`
  set L' : ℝ := max (L + 1) 1 with hL'
  have hL'pos : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLL' : L < L' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨K, hK⟩ := h L' hL'pos
  have hsum : ∀ N, absSpectralSum Q D c L' N = 0 := by
    intro N
    rw [absSpectralSum_eq_sum_indexSet]
    refine Finset.sum_eq_zero fun p hp => ?_
    unfold absTerm
    rw [hzero p (indexSet_subset_admissible hQ hp), zero_mul]
  have hmaj := (tendsto_cutoff_ratio D hLL').const_mul |K|
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hK, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  rw [hsum N, sub_zero] at hN
  have hpow : 0 < N ^ (-L) := Real.rpow_pos_of_pos (by linarith) _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow, ← mul_div_assoc,
    div_mul_cancel₀ _ hpow.ne']
  exact hN.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The assembled integral of a fixed joint datum is a finite-cutoff expansion. -/
theorem cutoffExpansion_gInt (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) :
    CutoffExpansion (commonQ k) (commonD n) (gInt ν h k β b x) (gCoeff ν h k β b x) := by
  intro L hL
  refine ⟨gCutoffConst ν h k β b L ‖x‖, ?_⟩
  have hbs : ∀ᶠ N : ℝ in atTop, ∀ I, 1 ≤ boxScale (k I) (b I) N := by
    rw [eventually_all]
    intro I
    have hc : 0 < (b I) ^ (2 * ∑ i, k I i) := pow_pos (hb I) _
    filter_upwards [eventually_ge_atTop (1 / (b I) ^ (2 * ∑ i, k I i))] with N hN
    unfold boxScale
    rwa [div_le_iff₀ hc] at hN
  filter_upwards [hbs, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  exact gCutoff_bound ν h k β b hk hβ hb hL hN1 hN le_rfl

/-- **Assembled flatness**: all assembled coefficients zero and a residual `o(N^{-L})` for every
`L` give `𝒵_pop = o(N^{-L})` for every `L`. -/
theorem population_flat (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    (hE : ∀ L : ℝ, Tendsto (fun N => E N / N ^ (-L)) atTop (𝓝 0))
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ k), gCoeff ν h k β b x p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Zpop N / N ^ (-L)) atTop (𝓝 0) := by
  have h1 := flat_of_cutoffExpansion (commonQ_pos k hk) (cutoffExpansion_gInt ν h k β b hk hβ hb x)
    hzero L
  have := h1.add (hE L)
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [hdecomp N, add_div]

/-- The exponentially small residual is `o(N^{-L})` for every `L`. -/
theorem tendsto_div_rpow_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (L : ℝ) :
    Tendsto (fun N => E N / N ^ (-L)) atTop (𝓝 0) := by
  have := tendsto_target_of_exp E hε hE L 0
  simpa using this

/-- Assembled flatness with an exponentially small residual. -/
theorem population_flat_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (x : JointData K n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N)
    {ε : ℝ} (hε : 0 < ε) (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0))
    (hzero : ∀ p ∈ admissible (commonD n) (commonQ k), gCoeff ν h k β b x p.1 p.2 = 0) (L : ℝ) :
    Tendsto (fun N => Zpop N / N ^ (-L)) atTop (𝓝 0) :=
  population_flat ν h k β b hk hβ hb x Zpop E hdecomp (tendsto_div_rpow_of_exp E hε hE) hzero L

/-- **Regression: flat is not zero.** `e^{-N} = o(N^{-L})` for every `L`… -/
theorem exp_neg_flat (L : ℝ) :
    Tendsto (fun N : ℝ => Real.exp (-N) / N ^ (-L)) atTop (𝓝 0) := by
  have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero L 1 one_pos
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [Real.rpow_neg hN.le, div_inv_eq_mul, mul_comm, neg_one_mul]

/-- …and never vanishes. -/
theorem exp_neg_ne_zero (N : ℝ) : Real.exp (-N) ≠ 0 := (Real.exp_pos _).ne'

end Grammar
```

## Questions
1. u306: is the admissible domain `admissible D Q` the right global domain (the assembled coefficients vanish off it: off the common lattice by `tanCoeff_eq_zero_of_not_lattice` + divisibility, above `commonD` by `tanCoeff_eq_zero_of_lt`; this is NOT restated in the file — should it be, as a lemma `gCoeff_eq_zero_of_not_admissible`, or is it unnecessary because the theorems quantify over admissible pairs only)? Is `indexSet_pred_closed` the correct "cutoff strictly above the target" argument (it uses `q.1 ≤ p.1 < L`)? Is uniqueness (`precedes_or_precedes_of_ne`) sound?
2. u307: is `isEquivalent_first_nonzero_of_cutoffExpansion` a correct use of `tendsto_abstractRemainder` (predecessor sum vanishes at the first nonzero pair), and is `cutoffExpansion_of_conclusion` right (at `b = 1` the Taylor-tree remainder IS the `CutoffExpansion` estimate)? For the assembled theorem the residual hypothesis is `∀ μ j, E/(N^{-μ} log^j) → 0` (every scale) — is this the right way to honour your "negligible at the selected scale" requirement, given the selected pair is existential? Anything hidden in `population_first_nonzero_chart`'s use of `hI` to transfer the expansion to the original integral?
3. u308: is `flat_of_cutoffExpansion` correct (cutoff `max(L+1, 1)`, all index-set coefficients zero ⇒ the spectral sum is zero ⇒ `|Z| ≤ K N^{-L'}(1+log N)^D` eventually ⇒ `Z/N^{-L} → 0`)? Is `cutoffExpansion_gInt` a legitimate derivation from `gCutoff_bound` (eventually `boxScale ≥ 1` for every chart, `R = ‖x‖`)? Is the flat-is-not-zero regression adequate?
4. N1 non-claims to record; blocking/nonblocking fixes; and GO/NO-GO for N3 with the unit list from your #38 (generic weighted-ℓ¹ continuity criterion; continuity of Cauchy coefficients in the parameter; uniform geometric majorant; continuous coefficient-family map; reconstruction; zero-noise `ofFamilies`/`TangentialData` wrapper; multiplication by a continuous tangential factor; public bridge). The seabed has `polyCoeff d r F γ` (iterated circle operator, `‖polyCoeff‖ ≤ M r^{-|γ|}` for `F` bounded by `M` on the closed polydisc of radius `r`, reconstruction `∑ polyCoeff z^γ = F z` on the open polydisc), `taylorFamily`/`polyRealCoeff`, `CircleOpParam` (parametric continuity of circle integrals), `ofFamilies b hb cξ cη hξ hη : DataSpace d` with `toXi_ofFamilies`, `toEta_ofFamilies`, and `DataSpace d = lp (fun _ => ℝ) 1` over `(Fin d → ℕ) ⊕ (Fin d → ℕ)`. Please give the exact statement of the first N3 unit (the ℓ¹ continuity criterion) in this vocabulary.

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
