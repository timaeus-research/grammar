/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.SecondOrderAssembled

/-!
# Observable insertions and local constancy of the selected pair (unit 324)

Two paper-facing corollaries. (1) `population_second_order_observable`: the second-order quotient
of `SecondOrderQuotient` written for an observable `φ∘π = u^{s} ψ` inserted into the amplitude, the
monomial factor becoming the weight shift `h ↦ h + s`. (2) Wall-crossing (the paper's remark that
the leading pair can change along a parameter only through cancellation): abstractly, if the
coefficient at an admissible pair `p` depends continuously on a parameter, is nonzero at `t₀`, and
all predecessors of `p` vanish throughout a neighbourhood, then `p` is the unique first nonzero pair
throughout a neighbourhood (`first_nonzero_locally_constant`); for a continuous family of zero-noise
joint data the assembled population integral is therefore asymptotically
`C_p(t) N^{-p.1} (log N)^{p.2}` with the SAME pair `p` for all `t` near `t₀`
(`population_first_nonzero_locally_constant`). Nothing is claimed about what happens where the
coefficient vanishes: continuity alone does not make predecessor vanishing persist, which is why it
is a hypothesis. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Second-order quotient for an observable insertion `u^{s} ψ`** (chart level): the monomial
factor is the weight shift `h ↦ h + s`. -/
theorem population_second_order_observable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη Fψ : (Fin (n + 1) → ℂ) → ℂ}
    {η ψ : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u) (hηc : Continuous η)
    (hFψ : DifferentiableOn ℂ Fψ (openPolydisc (n + 1) R))
    (hψ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fψ fun i => (u i : ℂ)).re = ψ u)
    (hψc : Continuous ψ) (s : Fin (n + 1) → ℕ) {l l' : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hmin' : ∀ i, l' ≤ ratioExp (fun i => h i + s i) k i)
    (hatt' : ∃ i, ratioExp (fun i => h i + s i) k i = l') (hA : amplitudeCoeff h k l β η ≠ 0) :
    Tendsto (fun N => Real.log N *
        (origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ s i) * ψ u) /
          origPhaseIntegral n h k β N 1 (fun _ => 0) η *
        (N ^ (l' - l) * Real.log N ^ (multCount (ratioExp h k) l - 1) /
          Real.log N ^ (multCount (ratioExp (fun i => h i + s i) k) l' - 1)) -
        amplitudeCoeff (fun i => h i + s i) k l' β ψ / amplitudeCoeff h k l β η)) atTop
      (𝓝 ((amplitudeCoeff h k l β η * secondCoeff n (fun i => h i + s i) k β Fψ l' -
        amplitudeCoeff (fun i => h i + s i) k l' β ψ * secondCoeff n h k β Fη l) /
        amplitudeCoeff h k l β η ^ 2)) := by
  refine (population_second_order_chart n h (fun i => h i + s i) k hk β hβ hR hFη hη hηc hFψ hψ
    hψc hmin hatt hmin' hatt' hA).congr' (Eventually.of_forall fun N => ?_)
  dsimp only
  rw [origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => 0) ψ s]

/-- **Local constancy of the first nonzero pair**: if the coefficient at the admissible pair `p`
is continuous in the parameter and nonzero at `t₀`, and every predecessor of `p` vanishes
throughout a neighbourhood, then near `t₀` the pair `p` is first nonzero and is the only such
pair. -/
theorem first_nonzero_locally_constant {D Q : ℕ} {T : Type*} [TopologicalSpace T]
    (c : T → ℝ → ℕ → ℝ) {p : ℝ × ℕ} (hp : p ∈ admissible D Q) {t₀ : T}
    (hc : ContinuousAt (fun t => c t p.1 p.2) t₀) (hne : c t₀ p.1 p.2 ≠ 0)
    (hpred : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ admissible D Q, precedes q p → c t q.1 q.2 = 0) :
    ∀ᶠ t in 𝓝 t₀,
      (p ∈ admissible D Q ∧ c t p.1 p.2 ≠ 0 ∧
        ∀ q ∈ admissible D Q, precedes q p → c t q.1 q.2 = 0) ∧
      ∀ p' : ℝ × ℕ, p' ∈ admissible D Q → c t p'.1 p'.2 ≠ 0 →
        (∀ q ∈ admissible D Q, precedes q p' → c t q.1 q.2 = 0) → p' = p := by
  filter_upwards [hc.eventually_ne hne, hpred] with t hct hpt
  refine ⟨⟨hp, hct, hpt⟩, fun p' hp' hcp' hfirst' => ?_⟩
  exact first_nonzero_unique (c t) hp' hcp' hfirst' hp hct hpt

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- **No wall-crossing without cancellation**: along a continuous family of joint data, where the
coefficient at the admissible pair `p` is nonzero and all predecessors vanish on a neighbourhood,
the assembled population integral is asymptotically `C_p(t) N^{-p.1}(log N)^{p.2}` with the same
`p` for every `t` near `t₀`. -/
theorem population_first_nonzero_locally_constant (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    {T : Type*} [TopologicalSpace T] {X : T → JointData K n} (hX : Continuous X) {p : ℝ × ℕ}
    (hp : p ∈ admissible (commonD n) (commonQ k)) {t₀ : T}
    (hne : gCoeff ν h k β (fun _ => 1) (X t₀) p.1 p.2 ≠ 0)
    (hpred : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ admissible (commonD n) (commonQ k), precedes q p →
      gCoeff ν h k β (fun _ => 1) (X t) q.1 q.2 = 0) :
    ∀ᶠ t in 𝓝 t₀, gCoeff ν h k β (fun _ => 1) (X t) p.1 p.2 ≠ 0 ∧
      gInt ν h k β (fun _ => 1) (X t) ~[atTop]
        fun N => gCoeff ν h k β (fun _ => 1) (X t) p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2) := by
  have hc : ContinuousAt (fun t => gCoeff ν h k β (fun _ => 1) (X t) p.1 p.2) t₀ :=
    ((continuous_gCoeff ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) p.1 p.2).comp
      hX).continuousAt
  filter_upwards [first_nonzero_locally_constant (fun t => gCoeff ν h k β (fun _ => 1) (X t)) hp hc
    hne hpred] with t ht
  refine ⟨ht.1.2.1, ?_⟩
  exact isEquivalent_first_nonzero_of_cutoffExpansion (commonQ_pos k hk)
    (cutoffExpansion_gInt ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) (X t)) hp ht.1.2.1 ht.1.2.2

end Grammar
