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
