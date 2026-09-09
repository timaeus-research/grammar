/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BoxDilation
import Grammar.PopulationLeadingCoeff
import Grammar.PopulationDataBridge

/-!
# Coefficient transport to a positive normal box (Programme Q, N4, unit 318)

For the population Taylor tree on `(0,b]^d` (`0 < b < R`, Headline XXXIII at `ξ = 0`), the
coefficient system `C` of the box conclusion is the unit-box system of the **rescaled** family
`scale cη b` (which represents `η(b·)` on the unit box), so the unit-box identification applies:
`C(λ, j) = 0` for `m − 1 < j ≤ n` and `C(λ, m−1) = amplitudeCoeff h k λ β (η(b·))`
(`population_box_leadingCoeff`). The paper-facing coefficient of `N^{-λ}(log N)^{m−1}` on the box,
`boxCoeff n h k β b 0 cη λ (m−1)`, is by definition the binomially transported sum
`b^H (b^{2K})^{-λ} ∑_{q ≥ m−1} C(λ,q) C(q, m−1) (log b^{2K})^{q−(m−1)}`; since `C(λ,q) = 0` above
`m − 1`, only `q = m−1` survives:
```
boxCoeff … b … λ (m−1) = b^H (b^{2K})^{-λ} · amplitudeCoeff h k λ β (η(b·))    (boxCoeff_leading)
```
in agreement with the direct limit of unit 317. Lower log coefficients at `λ` follow the same
binomial formula (they involve the unit-box coefficients `C(λ, q)`, `q ≤ m−1`, and powers of
`2K log b`); no separate closed form is claimed for them. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- Scaling the zero family. -/
theorem scale_zero (b : ℝ) : scale (0 : CoeffFamily d) b = 0 := by
  funext γ
  simp [scale]

/-- **The box Taylor tree's leading coefficient**: the unit-box identification transported to
`(0,b]^d`. -/
theorem population_box_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b R : ℝ} (hb : 0 < b) (hbR : b < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N b 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N b (fun _ => 0) η) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β (fun v => η (b • v)) ∧
      boxCoeff n h k β b 0 (taylorFamily (n + 1) Fη) l (multCount (ratioExp h k) l - 1) =
        b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
          amplitudeCoeff h k l β (fun v => η (b • v)) := by
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor' n h k hk β hβ hb hbR hFη hη
  set cη := taylorFamily (n + 1) Fη with hcη
  -- the rescaled family is absolutely summable and represents `η(b·)` on the unit box
  set r : ℝ := (b + R) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hbr : b < r := by rw [hr]; linarith
  have hrR : r < R := by rw [hr]; linarith
  have hcb : AbsSummableAt cη b := by
    have := absSummableAt_polyRealCoeff hr0 hrR hb.le hbr hFη
    rwa [polyRealCoeff_eq_taylorFamily hr0 hrR hFη] at this
  have hsc : AbsSummable (scale cη b) := AbsSummable.of_scale hb.le hcb
  obtain ⟨C₁, hC₁⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    (absSummableAt_zero (d := n + 1) 1) ((absSummableAt_one_iff _).2 hsc)
  have hI₁ : ∀ M, familyPhaseIntegralBox n h k β M 1 0 (scale cη b) =
      origPhaseIntegral n h k β M 1 (fun _ => 0) (fun v => η (b • v)) := by
    intro M
    refine familyPhaseIntegralBox_eq_orig n h k β M 1 (fun u _ => evalF_zero u) fun u hu => ?_
    rw [evalF_scale, hcη, ← polyRealCoeff_eq_taylorFamily hr0 hrR hFη,
      evalF_polyRealCoeff hr0 hrR hbr hFη ((smul_mem_piBox_Ioc_iff hb u).2 hu)]
    exact hη (b • u) ((smul_mem_piBox_Ioc_iff hb u).2 hu)
  obtain ⟨hzero₁, hlead₁⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC₁
    (continuous_rescale b hηc) hI₁ hmin hatt
  -- the two coefficient systems agree
  have hlink : ∀ μ j, C μ j = C₁ μ j := by
    intro μ j
    rw [hC.coeff_eq, hC₁.coeff_eq, scale_zero, scale_zero, scale_one]
  have hzero : ∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0 :=
    fun j hj hgt => by rw [hlink]; exact hzero₁ j hj hgt
  have hlead : C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β (fun v => η (b • v)) :=
    by rw [hlink]; exact hlead₁
  refine ⟨C, hC, hI, hzero, hlead, ?_⟩
  -- the box coefficient
  have hmn : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  unfold boxCoeff
  rw [scale_zero, Finset.sum_eq_single (multCount (ratioExp h k) l - 1)]
  · have hfsc : familySpectralCoeff n h k β 0 (scale cη b) l (multCount (ratioExp h k) l - 1) =
        amplitudeCoeff h k l β (fun v => η (b • v)) := by
      rw [← hlead, hC.coeff_eq, scale_zero]
    rw [hfsc]
    simp
  · intro q hq hne
    have hq' : multCount (ratioExp h k) l - 1 < q :=
      lt_of_le_of_ne (Finset.mem_Ico.1 hq).1 (Ne.symm hne)
    have hz : familySpectralCoeff n h k β 0 (scale cη b) l q = 0 := by
      have := hzero q (Finset.mem_range.2 (Finset.mem_Ico.1 hq).2) hq'
      rwa [hC.coeff_eq, scale_zero] at this
    rw [hz]
    ring
  · intro hnot
    exact absurd (Finset.mem_Ico.2 ⟨le_rfl, Nat.lt_succ_of_le hmn⟩) hnot

end Grammar
