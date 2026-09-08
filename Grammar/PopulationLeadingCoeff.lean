/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingIsolation
import Grammar.HeadlineAmplitude

/-!
# The first-candidate coefficient of the population expansion is the face functional
(grammar §3 rewrite, Astra #37 P1, unit 294)

For the population Taylor tree on the unit box (`ξ = 0`, `b = 1`) with a continuous amplitude
`η` admitting a holomorphic `Fη` on a polydisc of radius `R > 1` with `Re Fη = η` on the box, let
`λ = min_i (hᵢ+1)/(2kᵢ)` and `m = |{i : (hᵢ+1)/(2kᵢ) = λ}|`. Then the canonical Taylor-tree
coefficients at the exponent `λ` satisfy
```
C(λ, j) = 0  for m − 1 < j ≤ n,        C(λ, m − 1) = amplitudeCoeff h k λ β η,
```
where `amplitudeCoeff h k λ β η = Γ(λ)β^{-λ}/(m−1)! ∏_{i∈J} 1/(2kᵢ) ·
∫_{(0,1]^{n+1}} η(P_J u) ∏_{i∉J} uᵢ^{hᵢ−2kᵢλ} du` is the face-supported functional of Headline VIII
(`P_J` zeroes the minimal-ratio coordinates). This is the corrected form of the paper's
`eq:thm_leading_coeff` at chart level (Astra #37 Theorem A(c)): the coefficient lives on the
minimal-ratio face, and evaluation at the corner is the answer only when every ratio is minimal
(`amplitudeCoeff_equal`). No nonvanishing is asserted: `C(λ, m−1)` may be zero for a signed `η`.

Route (review v32 §5): the isolated cutoff expansion gives `𝒵(N) = N^{-λ} P(log N) + o(N^{-λ}
(log N)^{m−1})` with `P(x) = ∑_{j≤n} C(λ,j) x^j`; Headline VIII gives `𝒵(N)/(N^{-λ}(log N)^{m−1})
→ A`; hence `P(log N)/(log N)^{m−1} → A`, and polynomial growth uniqueness reads off the
coefficients. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The population integral on the unit box in the form of Headline VIII. -/
theorem origPhaseIntegral_population_one (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 (fun _ => 0) η =
      ∫ x in unitBox (n + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) := by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset]
  congr 1
  funext u
  simp [mul_assoc]

/-- The multiplicity is at most the dimension. -/
theorem multCount_le_card {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : multCount ℓ l ≤ d := by
  unfold multCount
  calc (∑ i, if ℓ i = l then 1 else 0) ≤ ∑ _i : Fin d, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = d := by simp

/-- **Identification of the first-candidate coefficient** for any coefficient system satisfying
the Taylor-tree conclusion on the unit box whose family integral is the population integral of a
continuous amplitude: the coefficients at `λ` vanish above log degree `m − 1`, and the coefficient
at `(λ, m − 1)` is the face functional of Headline VIII. -/
theorem population_leadingCoeff_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {η : (Fin (n + 1) → ℝ) → ℝ}
    (hηc : Continuous η)
    (hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη =
      origPhaseIntegral n h k β N 1 (fun _ => 0) η)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η := by
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- Headline VIII: the normalised integral converges to the face functional
  have hA : Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η /
      (N ^ (-l) * Real.log N ^ (m - 1))) atTop (𝓝 (amplitudeCoeff h k l β η)) := by
    have := amplitude_tendsto n h k hk l β hl0 hβ hmin hatt η hηc
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [origPhaseIntegral_population_one, hm]
  -- the isolated remainder tends to zero
  have hR := population_remainder_tendsto n h k hk β hC hmin hatt
  -- hence the normalised polynomial tends to the face functional
  have hP : Tendsto (fun N => (∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j) /
      Real.log N ^ (m - 1)) atTop (𝓝 (amplitudeCoeff h k l β η)) := by
    have hsub := hA.sub hR
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    rw [← hI N, ← sub_div, sub_sub_cancel, mul_div_mul_left _ _ hpow]
  have hm_le : m - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  obtain ⟨hzero, hlead, -⟩ := coeff_eq_of_tendsto_div_pow (a := fun j => C l j)
    Real.tendsto_log_atTop hP
  exact ⟨hzero, hlead hm_le⟩

/-- **Headline (P1): the leading population coefficient is the face functional.** For a
continuous amplitude `η` on `(0,1]^{n+1}` with a holomorphic `Fη` on the polydisc of radius
`R > 1`, `Re Fη = η` on the box: there is a coefficient system `C` with the full Taylor-tree
conclusion for the population integral `∫ η u^h e^{-βN u^{2k}}`, whose coefficients at the
minimal ratio `λ` vanish above log degree `m − 1` and whose `(λ, m − 1)` coefficient is
`Γ(λ)β^{-λ}/(m−1)! ∏_{J} 1/(2kᵢ) ∫ η(P_J u) ∏_{∉J} uᵢ^{hᵢ−2kᵢλ} du`. -/
theorem population_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β 1 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η := by
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor' n h k hk β hβ one_pos hR hFη hη
  obtain ⟨hzero, hlead⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC hηc hI hmin hatt
  exact ⟨C, hC, hI, hzero, hlead⟩

end Grammar
