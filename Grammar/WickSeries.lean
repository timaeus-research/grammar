/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianAveraging
import Grammar.AnnealedGeneratingSeries
import Grammar.EmpiricalGeneratingIdentity

/-!
# The Wick series of the expected empirical coefficient (§20, item 6)

For a random smooth chart field `ζ_o` whose scaled one-point values `u^k ζ_o(x)` are centred
Gaussian with variance `W(x)`, and a smooth amplitude `η`, the expected empirical coefficient is the
Wick series of population coefficients:

★★★ `integral_empCoeff_gaussian_wick`:
`E[empCoeff η ζ_o h k μ q] = Σ_j (1/(2^j j!)) · empCoeff (η W^j) 0 h k (μ + j) q`.

Route: the all-orders generating identity `hasSum_empCoeff_population_mono`
(`C_{μ,q}[ζ,η] = Σ_r (1/r!) C^pop_{μ+r/2,q}[η (u^kζ)^r]`), the annealed series with Wick weights
`integral_eq_tsum_wickWeights` (DXXXII, under the absolute-moment envelope), and the Gaussian
averaging of each population term (DXLI: odd terms vanish, even terms give `(2j)!/(2^j j!)` times
the term with `W^j`), with the depth data `L = cutoffOf h (μ + r/2)`, `p = depthOf h k L` at each
order.  Hypotheses: the pointwise Gaussian laws, Bochner integrability of all jets of `η (u^kζ)^r`,
and summability of the absolute moments of the generating terms (the Gaussian threshold).  No joint
Gaussianity, no Isserlis theorem, no differentiation under the expectation.

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ} {h k : Fin d → ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
-- the Gaussian-averaging steps unify jet spaces indexed by `Σ depthOf h k (cutoffOf h (μ + r/2))`
/-- ★★★ **The Wick series of the expected empirical coefficient.** -/
theorem integral_empCoeff_gaussian_wick (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1)
    {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {ζ : Ω → (Fin d → ℝ) → ℝ}
    (hζ : ∀ o, ContDiff ℝ ∞ (ζ o)) {W : (Fin d → ℝ) → ℝ} (hW : ContDiff ℝ ∞ W)
    (hW0 : ∀ x, 0 ≤ W x)
    (hlaw : ∀ x ∈ closedBox d 1,
      HasLaw (fun o => mono k x * ζ o x) (gaussianReal 0 ⟨W x, hW0 x⟩) P)
    (hint : ∀ r R : ℕ, Integrable (fun o => cubeJet R 1 (fun v => η v * (mono k v * ζ o v) ^ r)
      (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) P)
    (habs : Summable fun r : ℕ => ∫ o, |(1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q| ∂P) :
    Integrable (fun o => empCoeff η (ζ o) h k μ q) P ∧
    ∫ o, empCoeff η (ζ o) h k μ q ∂P = ∑' j : ℕ, (1 / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q := by
  have hQ := Qamb_pos k hk
  obtain ⟨m, hm⟩ := hμ
  -- the shifted exponents lie on the lattice below the cutoff
  have hμr : ∀ r : ℕ, ∃ m' : ℕ, μ + r / 2 = (m' : ℝ) / Qamb k := fun r => by
    obtain ⟨m₀, hm₀⟩ := half_mem_lattice (k := k) hk r
    refine ⟨m + m₀, ?_⟩
    rw [hm, hm₀]
    push_cast
    ring
  have hL0 : ∀ r : ℕ, 0 < cutoffOf h (μ + r / 2) := fun r =>
    lt_of_lt_of_le (by unfold L₀; omega) (L₀_le_cutoffOf h _)
  have hLL : ∀ r : ℕ, L₀ h ≤ cutoffOf h (μ + r / 2) := fun r => L₀_le_cutoffOf h _
  have hμL : ∀ r : ℕ, μ + r / 2 ∈ latticeBelow (Qamb k) (cutoffOf h (μ + r / 2)) := fun r =>
    (mem_latticeBelow_iff hQ).2 ⟨hμr r, lt_cutoffOf h _⟩
  -- the coefficient functionals at each order
  have hΦ : ∀ r : ℕ,
      ∃ Φ : CubeJetSpace d (∑ i, depthOf h k (cutoffOf h (μ + r / 2)) i) 1 →L[ℝ] ℝ,
      ∀ (η' : (Fin d → ℝ) → ℝ) (hη' : ContDiff ℝ ∞ η'),
        Φ (cubeJet _ 1 η' hη') = empCoeff η' (fun _ => 0) h k (μ + r / 2) q := fun r =>
    exists_popCoeffCLM hk (hL0 r) (depthOf_add hk (hLL r)) (depthOf_pos hk (hLL r)) le_rfl (hμL r)
      hq
  choose Φ hΦ using hΦ
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Ω → ℝ, T = fun (r : ℕ) (o : Ω) =>
    empCoeff (fun v => η v * (mono k v * ζ o v) ^ r) (fun _ => 0) h k (μ + r / 2) q := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Ω → ℝ,
      g = fun (r : ℕ) (o : Ω) => (1 / (r.factorial : ℝ)) * T r o := ⟨_, rfl⟩
  have hgT : ∀ r o, g r o = (1 / (r.factorial : ℝ)) * T r o := fun r o => by rw [hg]
  have hTΦ : ∀ r o, T r o = Φ r (cubeJet _ 1 (fun v => η v * (mono k v * ζ o v) ^ r)
      (hη.mul (((contDiff_mono k).mul (hζ o)).pow r))) := fun r o => by
    rw [hT, hΦ r]
  have hgint : ∀ r, Integrable (g r) P := fun r => by
    have h1 := ((Φ r).integrable_comp (hint r _)).const_mul (1 / (r.factorial : ℝ))
    refine h1.congr (Filter.Eventually.of_forall fun o => ?_)
    rw [hgT, hTΦ]
  have hsum : ∀ o, HasSum (fun r => g r o) (empCoeff η (ζ o) h k μ q) := fun o => by
    have := hasSum_empCoeff_population_mono h k hη (hζ o) hk ⟨m, hm⟩ hq
    rw [hg, hT]
    exact this
  have hc : AEStronglyMeasurable (fun o => empCoeff η (ζ o) h k μ q) P := by
    have hfun : (fun o => empCoeff η (ζ o) h k μ q) = fun o => ∑' r, g r o :=
      funext fun o => (hsum o).tsum_eq.symm
    rw [hfun]
    exact (AEMeasurable.tsum fun r => (hgint r).aemeasurable).aestronglyMeasurable
  -- Gaussian averaging of each term
  have hodd : ∀ j : ℕ, ∫ o, T (2 * j + 1) o ∂P = 0 := fun j => by
    have key := integral_empCoeff_zero_pow_odd hk (hL0 (2 * j + 1)) (depthOf_add hk (hLL _))
      (depthOf_pos hk (hLL _)) le_rfl (hμL (2 * j + 1)) hq hη
      (Y := fun o v => mono k v * ζ o v) (fun o => (contDiff_mono k).mul (hζ o)) hW0 j
      (hint (2 * j + 1) (∑ i, depthOf h k (cutoffOf h (μ + ((2 * j + 1 : ℕ) : ℝ) / 2)) i)) hlaw
    rw [hT]
    exact key
  have heven : ∀ j : ℕ, ∫ o, T (2 * j) o ∂P = ((2 * j).factorial / (2 ^ j * (j.factorial : ℝ))) *
      empCoeff (fun v => η v * W v ^ j) (fun _ => 0) h k (μ + j) q := fun j => by
    have := integral_empCoeff_zero_pow_even hk (hL0 (2 * j)) (depthOf_add hk (hLL _))
      (depthOf_pos hk (hLL _)) le_rfl (hμL (2 * j)) hq hη
      (Y := fun o v => mono k v * ζ o v) (fun o => (contDiff_mono k).mul (hζ o)) hW hW0 j
      (hint (2 * j) (∑ i, depthOf h k (cutoffOf h (μ + ((2 * j : ℕ) : ℝ) / 2)) i)) hlaw
    rw [hT]
    change ∫ o, empCoeff (fun v => η v * (mono k v * ζ o v) ^ (2 * j)) (fun _ => 0) h k
      (μ + ((2 * j : ℕ) : ℝ) / 2) q ∂P = _
    rw [show μ + ((2 * j : ℕ) : ℝ) / 2 = μ + j by push_cast; ring] at this ⊢
    exact this
  have habs' : Summable fun r => ∫ o, |g r o| ∂P := by
    rw [hg, hT]
    exact habs
  obtain ⟨hcint, -, heq⟩ := integral_eq_tsum_wickWeights hgT hc hgint
    (Filter.Eventually.of_forall hsum) habs' hodd heven
  exact ⟨hcint, heq⟩

end Grammar
