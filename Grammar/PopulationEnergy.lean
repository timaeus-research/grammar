/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationShift
import Grammar.PopulationQuotient

/-!
# The energy observable `φ = K` (Astra #37 P5, unit 304; paper `ex:phi_equals_K`)

In a normal-form chart `K∘π = u^{2k}`, so inserting the observable `K` multiplies the amplitude by
`u^{2k}`, i.e. shifts the weight `h ↦ h + 2k`. Every ratio shifts by exactly one,
`(hᵢ+2kᵢ+1)/(2kᵢ) = (hᵢ+1)/(2kᵢ) + 1` (`ratioExp_add_two_k`), so the minimiser set, the
multiplicity, the face projection and the residual weight are unchanged, and the face constant
picks up `Γ(λ+1)β^{-(λ+1)}/(Γ(λ)β^{-λ}) = λ/β`:
```
amplitudeCoeff (h+2k) k (λ+1) β ψ = (λ/β) · amplitudeCoeff h k λ β ψ        
(amplitudeCoeff_add_two_k)
```
Hence, when the denominator face functional `A = amplitudeCoeff h k λ β ψ` is nonzero,
```
N · 𝒵_N[K∘π] / 𝒵_N[1] → λ/β                                                  (energy_ratio_tendsto)
```
at chart level (`β = 1`: the posterior expected KL divergence decays as `λ/n`, Watanabe's
Theorem 6.10). The factor `λ/β` comes from the face-functional normalisation, not merely from the
exponent shift. Not established: the exact identity `𝒵_n[K] = −𝒵_n'(n)` (differentiation under
the geometric integral) and the correction `−(m−1)/(n log n)`, which is not a consequence of
differentiating an asymptotic equivalent. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

variable {d : ℕ}

/-- Inserting `u^{2k}` shifts every ratio by one. -/
theorem ratioExp_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ratioExp (fun i => h i + 2 * k i) k i = ratioExp h k i + 1 := by
  unfold ratioExp
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  field_simp
  push_cast
  ring

theorem ratioExp_add_two_k_eq_iff (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (i : Fin d) :
    ratioExp (fun i => h i + 2 * k i) k i = l + 1 ↔ ratioExp h k i = l := by
  rw [ratioExp_add_two_k h k hk i, add_left_inj]

theorem multCount_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l := by
  unfold multCount
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]

theorem faceProj_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    faceProj (fun i => h i + 2 * k i) k (l + 1) = faceProj h k l := by
  funext u i
  unfold faceProj
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]

theorem residualWeight_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (u : Fin d → ℝ) :
    residualWeight (fun i => h i + 2 * k i) k (l + 1) u = residualWeight h k l u := by
  unfold residualWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]
  split_ifs
  · rfl
  · congr 1
    push_cast
    ring

theorem hmin_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) : ∀ i, l + 1 ≤ ratioExp (fun i => h i + 2 * k i) k i := by
  intro i
  rw [ratioExp_add_two_k h k hk i]
  linarith [hmin i]

theorem hatt_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) : ∃ i, ratioExp (fun i => h i + 2 * k i) k i = l + 1 := by
  obtain ⟨i, hi⟩ := hatt
  exact ⟨i, by rw [ratioExp_add_two_k h k hk i, hi]⟩

/-- The face constant of the shifted weight is `λ/β` times the original. -/
theorem faceLeadConst_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l)
    (hβ : 0 < β) :
    faceLeadConst (fun i => h i + 2 * k i) k (l + 1) β = l / β * faceLeadConst h k l β := by
  unfold faceLeadConst
  rw [multCount_add_two_k h k hk l, Real.Gamma_add_one hl.ne']
  have hprod : (∏ i, if ratioExp (fun i => h i + 2 * k i) k i = l + 1
      then 1 / (2 * (k i : ℝ)) else 1) = ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1
:=
    Finset.prod_congr rfl fun i _ => by simp only [ratioExp_add_two_k_eq_iff h k hk l i]
  rw [hprod, show -(l + 1) = -l + -1 by ring, Real.rpow_add hβ, Real.rpow_neg_one]
  field_simp

/-- **The face functional of the energy observable**: `A_K = (λ/β) A_1`. -/
theorem amplitudeCoeff_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l)
    (hβ : 0 < β) (ψ : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff (fun i => h i + 2 * k i) k (l + 1) β ψ = l / β * amplitudeCoeff h k l β ψ := by
  unfold amplitudeCoeff
  rw [faceLeadConst_add_two_k h k hk hl hβ, faceProj_add_two_k h k hk l]
  simp_rw [residualWeight_add_two_k h k hk l]
  ring

/-- **`N · E_N[K∘π] → λ/β`** at chart level: for a continuous amplitude `ψ` with nonzero face
functional, the ratio of the population integral with `K∘π = u^{2k}` inserted to the population
integral, times `N`, converges to `λ/β`. -/
theorem energy_ratio_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ψ : (Fin (n + 1) → ℝ) → ℝ) (hψc : Continuous ψ) (hA : amplitudeCoeff h k l β ψ ≠ 0) :
    Tendsto (fun N => N * (origPhaseIntegral n h k β N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) / origPhaseIntegral n h k β N 1 (fun _ => 0) ψ))
      atTop (𝓝 (l / β)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- the numerator is the population integral with the shifted weight
  have hshift : ∀ N, origPhaseIntegral n h k β N 1 (fun _ => 0)
      (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) =
      origPhaseIntegral n (fun i => h i + 2 * k i) k β N 1 (fun _ => 0) ψ := fun N =>
    origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => 0) ψ (fun i => 2 * k i)
  have hA' : amplitudeCoeff (fun i => h i + 2 * k i) k (l + 1) β ψ ≠ 0 := by
    rw [amplitudeCoeff_add_two_k h k hk hl hβ]
    exact mul_ne_zero (div_ne_zero hl.ne' hβ.ne') hA
  have hn := population_isEquivalent n (fun i => h i + 2 * k i) k hk β hβ
    (hmin_add_two_k h k hk hmin) (hatt_add_two_k h k hk hatt) ψ hψc hA'
  rw [amplitudeCoeff_add_two_k h k hk hl hβ, multCount_add_two_k h k hk l] at hn
  have hd := population_isEquivalent n h k hk β hβ hmin hatt ψ hψc hA
  have hq := isEquivalent_quotient_powLog hn hd hA
  have hmul := (IsEquivalent.refl (u := fun N : ℝ => N) (l := atTop)).mul hq
  simp_rw [hshift]
  refine hmul.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.mul_apply]
  rw [show -(l + 1 - l) = (-1 : ℝ) by ring, Real.rpow_neg_one, div_self hlog,
    mul_div_assoc, div_self hA]
  field_simp

/-- `β = 1`: `n E_n[K] → λ`, the posterior expected KL divergence decays as `λ/n`. -/
theorem energy_ratio_tendsto_one (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ψ : (Fin (n + 1) → ℝ) → ℝ) (hψc : Continuous ψ) (hA : amplitudeCoeff h k l 1 ψ ≠ 0) :
    Tendsto (fun N => N * (origPhaseIntegral n h k 1 N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) / origPhaseIntegral n h k 1 N 1 (fun _ => 0) ψ))
      atTop (𝓝 l) := by
  have := energy_ratio_tendsto n h k hk 1 one_pos hmin hatt ψ hψc hA
  rwa [div_one] at this

end Grammar
