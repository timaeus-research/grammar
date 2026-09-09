/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationDataBridge

/-!
# Zero-noise continuity of the coefficient functionals (Programme Q, N8 reserve, unit 319)

`rem:pop_vs_emp` of the paper says the population expansion is the `ξ = 0` specialisation of the
empirical one. At the level of the canonical coefficient functionals this is a continuity statement,
immediate from Headline XXXIV (`continuous_taylorTree_coeff`): if data `X a → x` in the weighted-ℓ¹
data topology and `x` has zero noise, then every canonical coefficient converges to the population
coefficient, `dataBoxCoeff (X a) μ j → dataBoxCoeff x μ j` (`tendsto_dataBoxCoeff_of_tendsto`), and
at the first candidate the limit is the face functional of the represented amplitude
(`tendsto_dataBoxCoeff_leading`). Non-claims (Astra #38): this is convergence of individual
coefficients, not of whole expansions (that needs uniform remainder control), and normalised
empirical noise need not converge to zero (it may have a nondegenerate limit); nothing stochastic is
asserted. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Coefficient functionals are continuous in the data**: `X a → x ⇒ C_{μ,j}(X a) → C_{μ,j}(x)`.
-/
theorem tendsto_dataBoxCoeff_of_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {ι : Type*} {l : Filter ι}
    {X : ι → DataSpace (n + 1)} {x : DataSpace (n + 1)} (hX : Tendsto X l (𝓝 x)) (μ : ℝ) (j : ℕ) :
    Tendsto (fun a => dataBoxCoeff n h k β b (X a) μ j) l (𝓝 (dataBoxCoeff n h k β b x μ j)) :=
  ((continuous_taylorTree_coeff n h k hk β hβ hb μ j).tendsto x).comp hX

/-- **Population limit at the first candidate**: for data converging to a zero-noise datum on the
unit box, the first-candidate coefficient converges to the face functional of the represented
amplitude. -/
theorem tendsto_dataBoxCoeff_leading (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {ι : Type*} {l : Filter ι} {X : ι → DataSpace (n + 1)}
    {x : DataSpace (n + 1)} (hX : Tendsto X l (𝓝 x)) (hx : xiCoord x = 0) {lam : ℝ}
    (hmin : ∀ i, lam ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = lam) :
    Tendsto (fun a => dataBoxCoeff n h k β 1 (X a) lam (multCount (ratioExp h k) lam - 1)) l
      (𝓝 (amplitudeCoeff h k lam β (dataAmplitude x))) := by
  have := tendsto_dataBoxCoeff_of_tendsto n h k hk β hβ one_pos hX lam
    (multCount (ratioExp h k) lam - 1)
  rwa [(dataBoxCoeff_population_leading n h k hk β hβ x hx hmin hatt).2] at this

end Grammar
