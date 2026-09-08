/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingCoeff
import Grammar.MonomialShiftedMoments

/-!
# Monomial factors shift the candidate support (grammar §3 rewrite, Astra #37 P2, unit 295)

The paper's "vanishing order" mechanism (`eq:lambda_I_f`, `eq:mu_I_phi`): if the amplitude
carries an admissible monomial factor, `η(u) = u^s ψ(u)` with `s : Fin (n+1) → ℕ`, then
`u^h η = u^{h+s} ψ`, so the population integral is the population integral of `ψ` with the
shifted weight `h + s` (`origPhaseIntegral_monomial_shift`). Applying the population Taylor tree
and Headline VIII to `(h + s, ψ)`:

* the coefficient system is supported on the shifted candidate set `Λ(h+s, k)`
  (`population_shift_vanish`);
* the first shifted candidate is `λ_s = min_i (hᵢ+sᵢ+1)/(2kᵢ) ≥ λ`, with multiplicity `m_s`; the
  coefficients at `λ_s` vanish above log degree `m_s − 1`, and the `(λ_s, m_s − 1)` coefficient is
  the face functional of the **residual** amplitude `ψ` for the shifted weight,
  `amplitudeCoeff (h+s) k λ_s β ψ` (`population_shift_leadingCoeff`) — not of `u^s ψ`
  (Astra #37: using `u^s ψ` after shifting the weight counts the vanishing twice).

The factorisation `η = u^s ψ` with `ψ` continuous and holomorphically extendable is the
hypothesis ("admissible monomial factor", not necessarily maximal); the implication from a
divisorial vanishing order to such a factorisation belongs to the geometric/analytic bridge and is
not formalised. The shifted system is a system for the shifted presentation; identifying it with an
unshifted system's coefficients requires uniqueness, not done here. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Monomial shift of the amplitude**: `∫ (u^s ψ) u^h e^{…} = ∫ ψ u^{h+s} e^{…}` for any phase. -/
theorem origPhaseIntegral_monomial_shift (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (ξ ψ : (Fin (n + 1) → ℝ) → ℝ) (s : Fin (n + 1) → ℕ) :
    origPhaseIntegral n h k β N b ξ (fun u => (∏ i, u i ^ s i) * ψ u) =
      origPhaseIntegral n (fun i => h i + s i) k β N b ξ ψ := by
  unfold origPhaseIntegral
  congr 1
  funext u
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

/-- Coefficient systems of the shifted presentation vanish off the shifted candidate set. -/
theorem population_shift_vanish (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (s : Fin (n + 1) → ℕ)
    {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n (fun i => h i + s i) k β 1 cξ cη C) (μ : ℝ) (j : ℕ)
    (hμ : ¬ candidateExp (fun i => h i + s i) k μ) : C μ j = 0 :=
  hC.vanish μ j hμ

/-- The shifted minimal ratio is at least the unshifted one. -/
theorem shift_min_le {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (s : Fin d → ℕ) {l ls : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt_s : ∃ i, ratioExp (fun i => h i + s i) k i = ls) :
    l ≤ ls := by
  obtain ⟨i, hi⟩ := hatt_s
  rw [← hi]
  exact shift_min h k s hk l hmin i

/-- **The leading coefficient after a monomial shift** (`eq:lambda_I_f` corrected, chart level,
`b = 1`): for `η = u^s ψ` with `ψ` continuous on `ℝ^{n+1}` and a holomorphic `Fψ` on the polydisc
of radius `R > 1`, `Re Fψ = ψ` on the box, and `λ_s = min_i (hᵢ+sᵢ+1)/(2kᵢ)` with multiplicity
`m_s`: there is a coefficient system `C` for the shifted weight `h + s` with the full Taylor-tree
conclusion whose family integral is the original population integral of `u^s ψ` with weight `h`,
supported on `Λ(h+s,k)`, with `C(λ_s, j) = 0` for `m_s − 1 < j ≤ n` and
`C(λ_s, m_s − 1) = amplitudeCoeff (h+s) k λ_s β ψ` (the face functional of the residual `ψ`). -/
theorem population_shift_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fψ : (Fin (n + 1) → ℂ) → ℂ}
    {ψ : (Fin (n + 1) → ℝ) → ℝ} (hFψ : DifferentiableOn ℂ Fψ (openPolydisc (n + 1) R))
    (hψ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fψ fun i => (u i : ℂ)).re = ψ u)
    (hψc : Continuous ψ) (s : Fin (n + 1) → ℕ) {ls : ℝ}
    (hmin : ∀ i, ls ≤ ratioExp (fun i => h i + s i) k i)
    (hatt : ∃ i, ratioExp (fun i => h i + s i) k i = ls) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n (fun i => h i + s i) k β 1 0 (taylorFamily (n + 1) Fψ) C ∧
      (∀ N, familyPhaseIntegralBox n (fun i => h i + s i) k β N 1 0 (taylorFamily (n + 1) Fψ) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ s i) * ψ u)) ∧
      (∀ μ j, ¬ candidateExp (fun i => h i + s i) k μ → C μ j = 0) ∧
      (∀ j ∈ Finset.range (n + 1),
        multCount (ratioExp (fun i => h i + s i) k) ls - 1 < j → C ls j = 0) ∧
      C ls (multCount (ratioExp (fun i => h i + s i) k) ls - 1) =
        amplitudeCoeff (fun i => h i + s i) k ls β ψ := by
  obtain ⟨C, hC, hI, hzero, hlead⟩ :=
    population_leadingCoeff n (fun i => h i + s i) k hk β hβ hR hFψ hψ hψc hmin hatt
  refine ⟨C, hC, fun N => ?_, hC.vanish, hzero, hlead⟩
  rw [hI N, origPhaseIntegral_monomial_shift]

end Grammar
