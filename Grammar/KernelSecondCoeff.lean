/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StateDensitySecondCoeff
import Grammar.CoeffKernel
import Grammar.PopulationLeadingCoeff

/-!
# The monomial kernel at the two top log degrees (unit 362; Astra #45 unit 2, step 2)

For the shifted monomial `u^{h+γ}` the state density has minimal exponent `λ` with multiplicity
`m_γ = #{i ∈ J : γᵢ = 0}` (`expMult_add_shift`).  Consequently, with `m = |J|`:

* at log degree `m − 1` the coefficient is `(1/(m−1)!) ∏_{i∉J} 1/(w_{γ,i}+1−λ)` when `γ_J = 0`
  and `0` otherwise (`coeffAt_monoWeights_top`);
* at log degree `m − 2` (`m ≥ 2`) it is
  `−(1/(m−2)!) (∏_{i∉J} 1/(w_{γ,i}+1−λ)) ∑_{i∉J} 1/(w_{γ,i}+1−λ)` when `γ_J = 0`, and
  `(1/(m−2)!) (∏_{i∉J} 1/(w_{γ,i}+1−λ)) · 2k_{i₀}/γ_{i₀}` when exactly one `i₀ ∈ J` has
  `γ_{i₀} ≠ 0`, and `0` otherwise (`coeffAt_monoWeights_second`).

The monomial kernel `S_p(λ, j; γ)` then reduces to one term at `j = m − 1` (`kernelS_top`) and to
two terms at `j = m − 2` (`kernelS_second`), the second carrying the log-weighted moment
`fluctMoment β a p λ 1 = −∂_ν J_ν`.  Here `w_{γ,i} + 1 − λ = (hᵢ + γᵢ + 1 − 2kᵢλ)/(2kᵢ)`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep

variable {d : ℕ}

theorem monoWeights_add_one_eq (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    monoWeights (h + γ) k i + 1 = ratioExp h k i + (γ i : ℝ) / (2 * (k i : ℝ)) := by
  unfold monoWeights ratioExp
  rw [sub_add_cancel, Pi.add_apply]
  have : (2 * (k i : ℝ)) ≠ 0 := by
    have := hk i
    positivity
  field_simp
  push_cast
  ring

theorem le_monoWeights_add_one (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (i : Fin d) :
    l ≤ monoWeights (h + γ) k i + 1 := by
  rw [monoWeights_add_one_eq h k γ hk i]
  have : (0 : ℝ) ≤ (γ i : ℝ) / (2 * (k i : ℝ)) := by positivity
  linarith [hmin i]

theorem monoWeights_add_one_eq_iff (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (i : Fin d) :
    monoWeights (h + γ) k i + 1 = l ↔ ratioExp h k i = l ∧ γ i = 0 := by
  rw [monoWeights_add_one_eq h k γ hk i]
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
    have := hk i
    positivity
  constructor
  · intro heq
    have hq : (0 : ℝ) ≤ (γ i : ℝ) / (2 * (k i : ℝ)) := by positivity
    have h1 : ratioExp h k i = l := by linarith [hmin i]
    refine ⟨h1, ?_⟩
    have hq0 : (γ i : ℝ) / (2 * (k i : ℝ)) = 0 := by linarith
    rw [div_eq_zero_iff] at hq0
    rcases hq0 with hq0 | hq0
    · exact_mod_cast hq0
    · exact absurd hq0 hk'.ne'
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

open Classical in
theorem expMult_monoWeights_add (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) :
    expMult (monoWeights (h + γ) k) l =
      (Finset.univ.filter fun i => ratioExp h k i = l ∧ γ i = 0).card := by
  unfold expMult
  rw [Finset.filter_congr fun i _ => monoWeights_add_one_eq_iff h k hk hmin γ i]

open Classical in
/-- `m_γ + #{i ∈ J : γᵢ ≠ 0} = m`. -/
theorem expMult_add_shift (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) :
    expMult (monoWeights (h + γ) k) l +
      (Finset.univ.filter fun i => ratioExp h k i = l ∧ γ i ≠ 0).card =
      multCount (ratioExp h k) l := by
  rw [expMult_monoWeights_add h k hk hmin γ, multCount_eq_card]
  have := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => ratioExp h k i = l) (fun i => γ i = 0)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  simpa using this

/-- The shift vanishes on the dominant face `J`. -/
def faceZero (h k : Fin d → ℕ) (l : ℝ) (γ : Fin d → ℕ) : Prop :=
  ∀ i, ratioExp h k i = l → γ i = 0

/-- The residual product `∏_{i∉J} 1/(w_{γ,i} + 1 − λ)`. -/
noncomputable def residualProd (h k γ : Fin d → ℕ) (l : ℝ) : ℝ :=
  ∏ i, if ratioExp h k i = l then (1 : ℝ) else 1 / (monoWeights (h + γ) k i + 1 - l)

/-- The residual sum `∑_{i∉J} 1/(w_{γ,i} + 1 − λ)`. -/
noncomputable def residualSum (h k γ : Fin d → ℕ) (l : ℝ) : ℝ :=
  ∑ i, if ratioExp h k i = l then (0 : ℝ) else 1 / (monoWeights (h + γ) k i + 1 - l)

open Classical in
/-- **Top coefficient of the shifted monomial density.** -/
theorem coeffAt_monoWeights_top (n : ℕ) (h k γ : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1) =
      if faceZero h k l γ then
        (1 / ((multCount (ratioExp h k) l - 1).factorial : ℝ)) * residualProd h k γ l
      else 0 := by
  set m := multCount (ratioExp h k) l with hm
  have hsplit := expMult_add_shift h k hk hmin γ
  have hiff := monoWeights_add_one_eq_iff h k hk hmin γ
  by_cases hf : faceZero h k l γ
  · rw [if_pos hf]
    have hshift : (Finset.univ.filter fun i => ratioExp h k i = l ∧ γ i ≠ 0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i _ ⟨h1, h2⟩
      exact h2 (hf i h1)
    have hE : expMult (monoWeights (h + γ) k) l = m := by omega
    have hatt' : ∃ i, monoWeights (h + γ) k i + 1 = l := by
      obtain ⟨i, hi⟩ := hatt
      exact ⟨i, (hiff i).2 ⟨hi, hf i hi⟩⟩
    have hlead := stateDensityRep_leadCoeff n _ l (le_monoWeights_add_one h k hk hmin γ) hatt'
    rw [hE] at hlead
    rw [hlead]
    unfold residualProd
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ratioExp h k i = l
    · rw [if_pos hi, if_pos ((hiff i).2 ⟨hi, hf i hi⟩)]
    · rw [if_neg hi, if_neg fun h' => hi ((hiff i).1 h').1]
  · rw [if_neg hf]
    have hshift : 0 < (Finset.univ.filter fun i => ratioExp h k i = l ∧ γ i ≠ 0).card := by
      rw [Finset.card_pos]
      unfold faceZero at hf
      push Not at hf
      obtain ⟨i, h1, h2⟩ := hf
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩⟩
    exact stateDensityRep_coeffAt_eq_zero_of_le n _ l (by omega)

open Classical in
/-- **Second-top coefficient of the shifted monomial density** (`m ≥ 2`): the face-zero shifts
carry the second state-density coefficient, the shifts moving exactly one face coordinate
`i₀` carry the top coefficient of the reduced face with the factor `2k_{i₀}/γ_{i₀}`. -/
theorem coeffAt_monoWeights_second (n : ℕ) (h k γ : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hm : 2 ≤ multCount (ratioExp h k) l) :
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 2) =
      (if faceZero h k l γ then
        -(1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) *
          (residualProd h k γ l * residualSum h k γ l)
      else 0) +
      ∑ i₀, if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧ (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
        (1 / ((multCount (ratioExp h k) l - 2).factorial : ℝ)) * residualProd h k γ l *
          (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
      else 0 := by
  set m := multCount (ratioExp h k) l with hm_def
  have hsplit := expMult_add_shift h k hk hmin γ
  set S := Finset.univ.filter fun i => ratioExp h k i = l ∧ γ i ≠ 0 with hS
  have hle := le_monoWeights_add_one h k hk hmin γ
  have hiff := monoWeights_add_one_eq_iff h k hk hmin γ
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · rcases Nat.lt_or_ge S.card 1 with h0 | h1
    · have hS0 : S = ∅ := Finset.card_eq_zero.1 (by omega)
      have hf : faceZero h k l γ := by
        intro i hi
        by_contra hne
        have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hne⟩
        rw [hS0] at this
        exact absurd this (Finset.notMem_empty i)
      have hsum : (∑ i₀, if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧
          (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
            (1 / ((m - 2).factorial : ℝ)) * residualProd h k γ l * (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
          else (0 : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun i₀ _ => ?_
        rw [if_neg]
        rintro ⟨h1, h2, -⟩
        exact h2 (hf i₀ h1)
      rw [hsum, add_zero, if_pos hf]
      have hE : expMult (monoWeights (h + γ) k) l = m := by
        have : S.card = 0 := by omega
        omega
      have hsec := stateDensityRep_secondCoeff n _ l hle (by rw [hE]; exact hm)
      rw [hE] at hsec
      rw [hsec]
      unfold residualProd residualSum
      congr 2
      · refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : ratioExp h k i = l
        · rw [if_pos hi, if_pos ((hiff i).2 ⟨hi, hf i hi⟩)]
        · rw [if_neg hi, if_neg fun h' => hi ((hiff i).1 h').1]
      · refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : ratioExp h k i = l
        · rw [if_pos hi, if_pos ((hiff i).2 ⟨hi, hf i hi⟩)]
        · rw [if_neg hi, if_neg fun h' => hi ((hiff i).1 h').1]
    · have hS1 : S.card = 1 := by omega
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 hS1
      have hmem : i₀ ∈ S := by rw [hi₀]; exact Finset.mem_singleton_self _
      obtain ⟨-, hr₀, hγ₀⟩ := Finset.mem_filter.1 hmem
      have hothers : ∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0 := by
        intro i hi hne
        by_contra hne'
        have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hne'⟩
        rw [hi₀, Finset.mem_singleton] at this
        exact hne this
      have hf : ¬ faceZero h k l γ := fun hf => hγ₀ (hf i₀ hr₀)
      rw [if_neg hf, zero_add, Finset.sum_eq_single i₀ (fun b _ hb => ?_)
        (fun h => absurd (Finset.mem_univ i₀) h), if_pos ⟨hr₀, hγ₀, hothers⟩]
      · have hE : expMult (monoWeights (h + γ) k) l = m - 1 := by omega
        have hJ : (Finset.univ.filter fun i => ratioExp h k i = l).card = m :=
          (multCount_eq_card _ _).symm
        have hJ' : 0 < ((Finset.univ.filter fun i => ratioExp h k i = l).erase i₀).card := by
          rw [Finset.card_erase_of_mem (s := Finset.univ.filter fun i => ratioExp h k i = l)
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr₀⟩), hJ]
          omega
        obtain ⟨i₁, hi₁⟩ := Finset.card_pos.1 hJ'
        obtain ⟨hne₁, hmem₁⟩ := Finset.mem_erase.1 hi₁
        have hr₁ := (Finset.mem_filter.1 hmem₁).2
        have hatt' : ∃ i, monoWeights (h + γ) k i + 1 = l :=
          ⟨i₁, (hiff i₁).2 ⟨hr₁, hothers i₁ hr₁ hne₁⟩⟩
        have hlead := stateDensityRep_leadCoeff n _ l hle hatt'
        rw [hE, show m - 1 - 1 = m - 2 by omega] at hlead
        rw [hlead, mul_assoc]
        congr 1
        unfold residualProd
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
          ← Finset.mul_prod_erase Finset.univ
            (fun i => if ratioExp h k i = l then (1 : ℝ)
              else 1 / (monoWeights (h + γ) k i + 1 - l)) (Finset.mem_univ i₀)]
        rw [if_pos hr₀, one_mul, if_neg fun h' => hγ₀ ((hiff i₀).1 h').2, mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hi' : i ≠ i₀ := Finset.ne_of_mem_erase hi
          by_cases hr : ratioExp h k i = l
          · rw [if_pos hr, if_pos ((hiff i).2 ⟨hr, hothers i hr hi'⟩)]
          · rw [if_neg hr, if_neg fun h' => hr ((hiff i).1 h').1]
        · rw [monoWeights_add_one_eq h k γ hk i₀, hr₀, add_sub_cancel_left, one_div_div]
      · rw [if_neg]
        rintro ⟨-, -, hb3⟩
        exact hγ₀ (hb3 i₀ hr₀ (Ne.symm hb))
  · have hf : ¬ faceZero h k l γ := by
      intro hf
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < S.card by omega)
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hi
      exact h2 (hf i h1)
    have hsum : (∑ i₀, if ratioExp h k i₀ = l ∧ γ i₀ ≠ 0 ∧
        (∀ i, ratioExp h k i = l → i ≠ i₀ → γ i = 0) then
          (1 / ((m - 2).factorial : ℝ)) * residualProd h k γ l * (2 * (k i₀ : ℝ) / (γ i₀ : ℝ))
        else (0 : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun i₀ _ => ?_
      rw [if_neg]
      rintro ⟨-, -, hothers⟩
      have hsub : S ⊆ {i₀} := by
        intro i hi
        obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hi
        rw [Finset.mem_singleton]
        by_contra hne
        exact h2 (hothers i h1 hne)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    rw [if_neg hf, zero_add, hsum]
    exact stateDensityRep_coeffAt_eq_zero_of_le n _ l (by omega)

/-! ### The kernel at the two top log degrees -/

/-- **The monomial kernel at log degree `m − 1`** is a single term. -/
theorem kernelS_top (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (γ : Fin (n + 1) → ℕ) :
    kernelS n h k β a p l (multCount (ratioExp h k) l - 1) γ =
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
        (multCount (ratioExp h k) l - 1) * fluctMoment β a p l 0 := by
  set m := multCount (ratioExp h k) l with hm
  have hm1 : 1 ≤ m := multCount_pos _ _ hatt
  have hmn : m ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  have hsplit := expMult_add_shift h k hk hmin γ
  unfold kernelS
  rw [Finset.sum_eq_single (m - 1)]
  · rw [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self]
  · intro q hq hne
    have hq' := Finset.mem_Ico.1 hq
    rw [stateDensityRep_coeffAt_eq_zero_of_le n _ l (by omega), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) h

/-- **The monomial kernel at log degree `m − 2`** (`m ≥ 2`) has two terms, the second carrying
the log-weighted moment `fluctMoment β a p λ 1`. -/
theorem kernelS_second (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ) (p : ℕ)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hm : 2 ≤ multCount (ratioExp h k) l)
    (γ : Fin (n + 1) → ℕ) :
    kernelS n h k β a p l (multCount (ratioExp h k) l - 2) γ =
      PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
          (multCount (ratioExp h k) l - 2) * fluctMoment β a p l 0 +
        PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l
          (multCount (ratioExp h k) l - 1) * ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
          fluctMoment β a p l 1 := by
  set m := multCount (ratioExp h k) l with hm_def
  have hmn : m ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  have hsplit := expMult_add_shift h k hk hmin γ
  unfold kernelS
  rw [← Finset.sum_Ico_consecutive _ (show m - 2 ≤ m by omega) (show m ≤ n + 1 by omega),
    Finset.sum_eq_zero (s := Finset.Ico m (n + 1)) (fun q hq => by
      have hq' := Finset.mem_Ico.1 hq
      rw [stateDensityRep_coeffAt_eq_zero_of_le n _ l (by omega), zero_mul, zero_mul]),
    add_zero]
  have hpair : Finset.Ico (m - 2) m = {m - 2, m - 1} := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hpair, Finset.sum_pair (show m - 2 ≠ m - 1 by omega)]
  have h2 : (m - 1).choose (m - 2) = m - 1 := by
    rw [show m - 1 = m - 2 + 1 by omega]
    exact Nat.choose_succ_self_right _
  have h3 : m - 1 - (m - 2) = 1 := by omega
  rw [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, h2, h3]

end Grammar
