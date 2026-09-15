/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothResonantSupport

/-!
# Exact resonance at the top logarithmic power

Consult #130, Unit E0. The resonance count of CDXXXIII (`resonantCount`: coordinates with
`2k_iμ ∈ e_i + 1 + ℕ`) bounds the pole order of a general amplitude family, whose Taylor
multi-indices may exceed `e`. For the face MONOMIAL family `u^e` (support exactly `{e}`) the
pole order is the EXACT count `exactCount k e μ = #{i : 2k_iμ = e_i + 1}`, and the coefficients
vanish from that log degree on (★ `faceMonoCoeff_eq_zero_of_exactCount_le`, the chain
`coeffTerm → spectralCoeff → familySpectralCoeff → boxCoeff` rerun with exact support). Hence at
the top logarithmic power `|J| − 1` of a face `J`, a nonzero face coefficient forces EVERY
coordinate of the face to resonate exactly, `2k_jμ = m_j + h_j + 1`
(`faceCoef_top_eq_zero_of_not_exact`), which pins the Taylor order `m_j = 2k_jμ − h_j − 1`
uniquely (`taylorOrder_unique`). This is the
collapse of the face sum to a single normal jet in the graded stratum formula (Theorem E).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

open MonoRep CoeffFamily

variable {d : ℕ}

/-- The exact resonance count `#{i : 2k_iμ = e_i + 1}`. -/
noncomputable def exactCount {ι : Type*} [Fintype ι] (k e : ι → ℕ) (μ : ℝ) : ℕ :=
  (univ.filter fun i => 2 * (k i : ℝ) * μ = e i + 1).card

theorem exactCount_le_resonantCount {ι : Type*} [Fintype ι] (k e : ι → ℕ) (μ : ℝ) :
    exactCount k e μ ≤ resonantCount k e μ := by
  classical
  unfold exactCount resonantCount
  refine Finset.card_le_card fun i hi => ?_
  rw [mem_filter] at hi ⊢
  exact ⟨mem_univ _, 0, by rw [Nat.cast_zero, add_zero]; exact hi.2⟩

theorem exactCount_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) (k e : ι → ℕ)
    (μ : ℝ) : exactCount (k ∘ σ.symm) (e ∘ σ.symm) μ = exactCount k e μ := by
  unfold exactCount
  refine Finset.card_bij (fun j _ => σ.symm j) ?_ ?_ ?_
  · intro j hj
    rw [mem_filter] at hj ⊢
    exact ⟨mem_univ _, hj.2⟩
  · intro j₁ _ j₂ _ h
    exact σ.symm.injective h
  · intro i hi
    rw [mem_filter] at hi
    refine ⟨σ i, mem_filter.2 ⟨mem_univ _, ?_⟩, σ.symm_apply_apply i⟩
    rw [Function.comp_apply, Function.comp_apply, σ.symm_apply_apply]
    exact hi.2

theorem monoWeights_add_one_eq_iff {n : ℕ} (k e : Fin n → ℕ) (hk : ∀ i, 0 < k i) (μ : ℝ)
    (i : Fin n) : monoWeights e k i + 1 = μ ↔ 2 * (k i : ℝ) * μ = e i + 1 := by
  have hk' : (2 * (k i : ℝ)) ≠ 0 := by
    have := Nat.cast_pos (α := ℝ) |>.2 (hk i)
    positivity
  unfold monoWeights
  rw [sub_add_cancel, div_eq_iff hk']
  constructor <;> intro h <;> linarith

theorem expMult_monoWeights_eq_exactCount {n : ℕ} (k e : Fin n → ℕ) (hk : ∀ i, 0 < k i)
    (μ : ℝ) : expMult (monoWeights e k) μ = exactCount k e μ := by
  unfold expMult exactCount
  congr 1
  exact Finset.filter_congr fun i _ => monoWeights_add_one_eq_iff k e hk μ i

/-! ### The exact-support vanishing chain -/

theorem coeffTerm_eq_zero_of_expMult_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ)
    (μ : ℝ) {j : ℕ} (P : MonoRep (n + 1)) (e : Fin (n + 1) → ℕ)
    (hP : ∀ s ∈ P, s.2 ≠ 0 → s.1 = e) (hj : expMult (monoWeights (h + e) k) μ ≤ j) :
    coeffTerm n h k β a p μ j P = 0 := by
  unfold coeffTerm
  rw [List.sum_eq_zero, mul_zero]
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  by_cases hs2 : s.2 = 0
  · rw [hs2, zero_mul]
  · rw [Finset.sum_eq_zero, mul_zero]
    intro q hq
    rw [hP s hs hs2, stateDensityRep_coeffAt_eq_zero_of_le, zero_mul, zero_mul]
    exact hj.trans (Finset.mem_Ico.1 hq).1

theorem pow_fluct_support {P : MonoRep d} (hP : ∀ s ∈ P, s.2 = 0) (p : ℕ) :
    ∀ x ∈ MonoRep.pow (MonoRep.fluct P) p, x.2 ≠ 0 → x.1 = 0 := by
  induction p with
  | zero =>
    intro x hx _
    rw [MonoRep.pow, List.mem_singleton] at hx
    rw [hx]
  | succ p _ =>
    intro x hx hx2
    obtain ⟨s, hs, t, -, rfl⟩ := mem_mul hx
    exfalso
    have hs0 : s.2 = 0 := hP s (List.mem_of_mem_filter hs)
    exact hx2 (by rw [hs0, zero_mul])

theorem mul_support_eq {e : Fin d → ℕ} {P Q : MonoRep d} (hP : ∀ s ∈ P, s.2 ≠ 0 → s.1 = e)
    (hQ : ∀ t ∈ Q, t.2 ≠ 0 → t.1 = 0) : ∀ x ∈ MonoRep.mul P Q, x.2 ≠ 0 → x.1 = e := by
  intro x hx hx2
  obtain ⟨s, hs, t, ht, rfl⟩ := mem_mul hx
  rw [hP s hs (left_ne_zero_of_mul hx2), hQ t ht (right_ne_zero_of_mul hx2), add_zero]

theorem spectralCoeff_eq_zero_of_expMult_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (ξ η : MonoRep (n + 1)) {e : Fin (n + 1) → ℕ} (hξ : ∀ s ∈ ξ, s.2 = 0)
    (hη : ∀ s ∈ η, s.2 ≠ 0 → s.1 = e) {μ : ℝ} {j : ℕ}
    (hj : expMult (monoWeights (h + e) k) μ ≤ j) : spectralCoeff n h k β ξ η μ j = 0 := by
  unfold spectralCoeff
  have hz : ∀ p : ℕ, β ^ p / (p.factorial : ℝ) *
      coeffTerm n h k β (MonoRep.eval ξ 0) p μ j
        (MonoRep.mul η (MonoRep.pow (MonoRep.fluct ξ) p)) = 0 := fun p => by
    rw [coeffTerm_eq_zero_of_expMult_le n h k β _ p μ _ e
      (mul_support_eq hη (pow_fluct_support hξ p)) hj, mul_zero]
  simp_rw [hz]
  exact tsum_zero

theorem truncList_zero_coeff {c : CoeffFamily d} (hc : ∀ γ, c γ = 0) (m : ℕ) :
    ∀ s ∈ truncList c m, s.2 = 0 := by
  intro s hs
  unfold truncList at hs
  rw [List.mem_map] at hs
  obtain ⟨γ, -, rfl⟩ := hs
  exact hc γ

theorem truncList_support_eq {e : Fin d → ℕ} {c : CoeffFamily d} (hc : ∀ γ, c γ ≠ 0 → γ = e)
    (m : ℕ) : ∀ s ∈ truncList c m, s.2 ≠ 0 → s.1 = e := by
  intro s hs
  unfold truncList at hs
  rw [List.mem_map] at hs
  obtain ⟨γ, -, rfl⟩ := hs
  exact hc γ

theorem familySpectralCoeff_eq_zero_of_expMult_le (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hξ0 : ∀ γ, cξ γ = 0) (hη : AbsSummable cη) {e : Fin (n + 1) → ℕ}
    (hsupp : ∀ γ, cη γ ≠ 0 → γ = e) {μ : ℝ} {j : ℕ}
    (hj : expMult (monoWeights (h + e) k) μ ≤ j) : familySpectralCoeff n h k β cξ cη μ j = 0 := by
  have h1 := tendsto_truncCoeff n h k hk β hβ hξ hη μ j
  have h2 : Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 0) := by
    have : truncCoeff n h k β cξ cη μ j = fun _ => 0 := funext fun m =>
      spectralCoeff_eq_zero_of_expMult_le n h k β _ _ (truncList_zero_coeff hξ0 m)
        (truncList_support_eq hsupp m) hj
    rw [this]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

theorem boxCoeff_eq_zero_of_expMult_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummableAt cξ b) (hξ0 : ∀ γ, cξ γ = 0) (hη : AbsSummableAt cη b)
    {e : Fin (n + 1) → ℕ} (hsupp : ∀ γ, cη γ ≠ 0 → γ = e) {μ : ℝ} {j : ℕ}
    (hj : expMult (monoWeights (h + e) k) μ ≤ j) : boxCoeff n h k β b cξ cη μ j = 0 := by
  unfold boxCoeff
  rw [Finset.sum_eq_zero (s := Finset.Ico j (n + 1)), mul_zero]
  intro q hq
  rw [familySpectralCoeff_eq_zero_of_expMult_le n h k hk β hβ (AbsSummable.of_scale hb.le hξ)
    (fun γ => by unfold scale; rw [hξ0, zero_mul]) (AbsSummable.of_scale hb.le hη)
    (fun γ hγ => hsupp γ (by unfold scale at hγ; exact left_ne_zero_of_mul hγ))
    (hj.trans (Finset.mem_Ico.1 hq).1), zero_mul, zero_mul]

/-- ★ **Exact vanishing of the face monomial coefficients**: the coefficients of the face monomial
`u^e` vanish at every log degree `j ≥ #{i : 2k_iμ = e_i + 1}`. -/
theorem faceMonoCoeff_eq_zero_of_exactCount_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} {j : ℕ}
    (hj : exactCount k e μ ≤ j) : faceMonoCoeff k e β b μ j = 0 := by
  unfold faceMonoCoeff
  refine boxCoeff_eq_zero_of_expMult_le _ 0 (k ∘ (faceEquiv ι).symm) (fun i => hk _) β hβ hb
    (absSummableAt_zero b) (fun _ => rfl) (absSummableAt_monoFam _ b)
    (e := e ∘ (faceEquiv ι).symm) (fun γ hγ => ?_) ?_
  · unfold monoFam at hγ
    by_contra hne
    exact hγ (if_neg hne)
  · rw [zero_add, expMult_monoWeights_eq_exactCount (k ∘ (faceEquiv ι).symm)
      (e ∘ (faceEquiv ι).symm) (fun i => hk _), exactCount_comp_equiv]
    exact hj

/-- ★★ **Exact resonance at the top logarithmic power**: if some coordinate does not resonate
exactly, the face monomial coefficient at log degree `|ι| − 1` vanishes. -/
theorem faceMonoCoeff_top_eq_zero_of_not_exact {ι : Type*} [Fintype ι] [Nonempty ι]
    (k e : ι → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} {i : ι}
    (hi : 2 * (k i : ℝ) * μ ≠ e i + 1) : faceMonoCoeff k e β b μ (Fintype.card ι - 1) = 0 := by
  refine faceMonoCoeff_eq_zero_of_exactCount_le k e hk hβ hb ?_
  unfold exactCount
  have hss : (univ.filter fun j => 2 * (k j : ℝ) * μ = e j + 1) ⊂ univ :=
    Finset.filter_ssubset.2 ⟨i, mem_univ _, hi⟩
  have := Finset.card_lt_card hss
  rw [Finset.card_univ] at this
  omega

/-- The engine's face coefficient at the top log power `|J| − 1` vanishes unless every coordinate
of the face resonates exactly: `2k_jμ = e_j + 1` for all `j ∈ J`. -/
theorem faceCoef_top_eq_zero_of_not_exact (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {β b : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (J : Finset (Fin d)) (e : Fin d → ℕ) {μ : ℝ} {j : Fin d}
    (hj : j ∈ J) (hne : 2 * (k j : ℝ) * μ ≠ e j + 1) : faceCoef k β b J e μ (DJ J) = 0 := by
  unfold faceCoef
  rw [dif_pos ⟨j, hj⟩]
  have := nonempty_subtype_inJ ⟨j, hj⟩
  exact faceMonoCoeff_top_eq_zero_of_not_exact (fun i : {i // inJ J i} => k i)
    (fun i : {i // inJ J i} => e i) (fun i => hk i.1) hβ hb (i := ⟨j, hj⟩) hne

/-- The Taylor order of an exactly resonant coordinate is determined:
`m = 2kμ − h − 1`. -/
theorem taylorOrder_unique {k h m m' : ℕ} {μ : ℝ}
    (h1 : 2 * (k : ℝ) * μ = m + h + 1) (h2 : 2 * (k : ℝ) * μ = m' + h + 1) : m = m' := by
  have : (m : ℝ) = m' := by linarith
  exact_mod_cast this

end SmoothEngine

end Grammar
