/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LeadingTermInterface

/-!
# Range partitions of a positive unit and the approximate squeeze

Unit 1 of consult #81 (`tide-log/gpt6_bigpicture_v81.md`): the analytic helpers for removing the
normal-independence of the phase unit by comparison on the RANGE of the unit.

* **Ramps and the telescoping partition of unity.** `ramp c w s = clamp((s − c)/w, 0, 1)`; with
  `G 0 = 1`, `G (j+1) = ramp (a + j w) w`, the differences `chi a w j = G j − G (j+1)` are
  continuous, nonnegative, sum to `1` on `(−∞, a + m w]` over `j < m + 1` (`sum_chi`,
  telescoping), and `chi j` vanishes outside `(a + (j−1) w, a + (j+1) w)`
  (`lowerPt_le_of_chi_ne_zero`, `lt_upperPt_of_chi_ne_zero`); the support interval
  `[lowerPt j, upperPt j]` has multiplicative width `≤ 1 + 2w/a` (`upperPt_le_mul_lowerPt`).
  Choosing `w ≤ aδ/2` gives width `≤ 1 + δ`.
* **Bounds of a positive continuous function on a compact set**
  (`exists_pos_bounds_of_continuousOn`).
* **The approximate squeeze**: if for every `ε > 0` the function is eventually sandwiched between
  two functions whose normalised limits lie within `ε` of `C`, then its normalised limit is `C`
  (`tendsto_div_of_approx_squeeze`); in `HasLeadingTerm` form `hasLeadingTerm_of_approx_squeeze`.
-/

open Filter Topology Set

namespace Grammar

/-! ### Ramps -/

/-- The ramp `clamp((s − c)/w, 0, 1)`. -/
noncomputable def ramp (c w s : ℝ) : ℝ := max 0 (min 1 ((s - c) / w))

theorem ramp_nonneg (c w s : ℝ) : 0 ≤ ramp c w s := le_max_left _ _

theorem ramp_le_one (c w s : ℝ) : ramp c w s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_ramp (c w : ℝ) : Continuous (ramp c w) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const w))

theorem ramp_eq_zero_of_le {c w s : ℝ} (hw : 0 < w) (hs : s ≤ c) : ramp c w s = 0 := by
  unfold ramp
  rw [max_eq_left]
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)

theorem ramp_eq_one_of_le {c w s : ℝ} (hw : 0 < w) (hs : c + w ≤ s) : ramp c w s = 1 := by
  unfold ramp
  rw [min_eq_left, max_eq_right zero_le_one]
  rw [le_div_iff₀ hw]
  linarith

/-- The ramp is antitone in its centre. -/
theorem ramp_anti {c c' w s : ℝ} (hw : 0 < w) (hc : c ≤ c') : ramp c' w s ≤ ramp c w s := by
  unfold ramp
  refine max_le_max le_rfl (min_le_min le_rfl ?_)
  exact div_le_div_of_nonneg_right (by linarith) hw.le

/-! ### The telescoping partition of unity on the range -/

/-- The cumulative ramps: `G 0 = 1`, `G (j+1) = ramp (a + j w) w`. -/
noncomputable def G (a w : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | j + 1 => ramp (a + j * w) w

/-- The `j`-th piece of the partition of unity. -/
noncomputable def chi (a w : ℝ) (j : ℕ) (s : ℝ) : ℝ := G a w j s - G a w (j + 1) s

theorem continuous_G (a w : ℝ) (j : ℕ) : Continuous (G a w j) := by
  cases j with
  | zero => exact continuous_const
  | succ j => exact continuous_ramp _ _

theorem continuous_chi (a w : ℝ) (j : ℕ) : Continuous (chi a w j) :=
  (continuous_G a w j).sub (continuous_G a w (j + 1))

theorem G_succ_le {a w : ℝ} (hw : 0 < w) (j : ℕ) (s : ℝ) : G a w (j + 1) s ≤ G a w j s := by
  cases j with
  | zero => exact ramp_le_one _ _ _
  | succ j =>
    change ramp (a + ((j + 1 : ℕ) : ℝ) * w) w s ≤ ramp (a + (j : ℝ) * w) w s
    refine ramp_anti hw ?_
    push_cast
    nlinarith

theorem chi_nonneg {a w : ℝ} (hw : 0 < w) (j : ℕ) (s : ℝ) : 0 ≤ chi a w j s :=
  sub_nonneg.2 (G_succ_le hw j s)

/-- **The pieces sum to one** on `(−∞, a + m w]`. -/
theorem sum_chi {a w : ℝ} (hw : 0 < w) (m : ℕ) {s : ℝ} (hs : s ≤ a + m * w) :
    ∑ j ∈ Finset.range (m + 1), chi a w j s = 1 := by
  unfold chi
  rw [Finset.sum_range_sub' (fun j => G a w j s)]
  change (1 : ℝ) - ramp (a + (m : ℝ) * w) w s = 1
  rw [ramp_eq_zero_of_le hw hs, sub_zero]

/-- The lower end of the support of `chi j`: `max a (a + j w − w)`. -/
noncomputable def lowerPt (a w : ℝ) (j : ℕ) : ℝ := max a (a + j * w - w)

/-- The upper end of the support of `chi j`: `a + j w + w`. -/
noncomputable def upperPt (a w : ℝ) (j : ℕ) : ℝ := a + j * w + w

theorem lowerPt_pos {a w : ℝ} (ha : 0 < a) (j : ℕ) : 0 < lowerPt a w j :=
  lt_of_lt_of_le ha (le_max_left _ _)

theorem le_lowerPt (a w : ℝ) (j : ℕ) : a ≤ lowerPt a w j := le_max_left _ _

/-- On the support of `chi j` and above `a`, the argument is at least `lowerPt j`. -/
theorem lowerPt_le_of_chi_ne_zero {a w : ℝ} (hw : 0 < w) {j : ℕ} {s : ℝ} (has : a ≤ s)
    (h : chi a w j s ≠ 0) : lowerPt a w j ≤ s := by
  refine max_le has ?_
  cases j with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; linarith
  | succ j =>
    by_contra hlt
    have hlt' := not_le.1 hlt
    apply h
    unfold chi
    have h1 : G a w (j + 1) s = 0 := by
      change ramp (a + (j : ℝ) * w) w s = 0
      refine ramp_eq_zero_of_le hw ?_
      push_cast at hlt'
      linarith
    have h2 : G a w (j + 1 + 1) s = 0 := by
      change ramp (a + ((j + 1 : ℕ) : ℝ) * w) w s = 0
      refine ramp_eq_zero_of_le hw ?_
      push_cast at hlt' ⊢
      linarith
    rw [h1, h2, sub_zero]

/-- On the support of `chi j`, the argument is below `upperPt j`. -/
theorem lt_upperPt_of_chi_ne_zero {a w : ℝ} (hw : 0 < w) {j : ℕ} {s : ℝ} (h : chi a w j s ≠ 0) :
    s < upperPt a w j := by
  by_contra hle
  have hle' := not_lt.1 hle
  apply h
  unfold chi upperPt at *
  have h2 : G a w (j + 1) s = 1 := by
    change ramp (a + (j : ℝ) * w) w s = 1
    exact ramp_eq_one_of_le hw hle'
  have h1 : G a w j s = 1 := by
    cases j with
    | zero => rfl
    | succ j =>
      change ramp (a + (j : ℝ) * w) w s = 1
      refine ramp_eq_one_of_le hw ?_
      push_cast at hle'
      linarith
  rw [h1, h2, sub_self]

/-- **Multiplicative width of the support**: `upperPt j ≤ (1 + 2w/a) · lowerPt j`. -/
theorem upperPt_le_mul_lowerPt {a w : ℝ} (ha : 0 < a) (hw : 0 < w) (j : ℕ) :
    upperPt a w j ≤ (1 + 2 * w / a) * lowerPt a w j := by
  unfold upperPt lowerPt
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases le_or_gt (a + j * w - w) a with hle | hlt
  · rw [max_eq_left hle]
    have : (j : ℝ) * w ≤ w := by linarith
    have h2w : 2 * w / a * a = 2 * w := by field_simp
    nlinarith
  · rw [max_eq_right hlt.le]
    have hpos : a ≤ a + j * w - w := hlt.le
    have : (1 + 2 * w / a) * (a + j * w - w) = (a + j * w - w) + 2 * w / a * (a + j * w - w) := by
      ring
    rw [this]
    have h3 : 2 * w ≤ 2 * w / a * (a + j * w - w) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith
    linarith

/-! ### Bounds of a positive continuous function on a compact set -/

theorem exists_pos_bounds_of_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty) {u : X → ℝ} (hu : ContinuousOn u S)
    (hpos : ∀ x ∈ S, 0 < u x) : ∃ a B : ℝ, 0 < a ∧ ∀ x ∈ S, a ≤ u x ∧ u x ≤ B := by
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hu
  obtain ⟨x₁, hx₁, hmax⟩ := hS.exists_isMaxOn hne hu
  exact ⟨u x₀, u x₁, hpos x₀ hx₀, fun x hx => ⟨isMinOn_iff.1 hmin x hx, isMaxOn_iff.1 hmax x hx⟩⟩

/-! ### The approximate squeeze -/

/-- **The approximate squeeze**: if for every `ε > 0` the function is eventually sandwiched between
two functions whose normalised limits lie within `ε` of `C`, its normalised limit is `C`. -/
theorem tendsto_div_of_approx_squeeze {Z s : ℝ → ℝ} {C : ℝ} (hs : ∀ᶠ N in atTop, 0 < s N)
    (h : ∀ ε > 0, ∃ (lo hi : ℝ → ℝ) (clo chi : ℝ),
      (∀ᶠ N in atTop, lo N ≤ Z N ∧ Z N ≤ hi N) ∧
      Tendsto (fun N => lo N / s N) atTop (𝓝 clo) ∧
      Tendsto (fun N => hi N / s N) atTop (𝓝 chi) ∧ C - ε ≤ clo ∧ chi ≤ C + ε) :
    Tendsto (fun N => Z N / s N) atTop (𝓝 C) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨lo, hi, clo, chi, hsand, hlo, -, hclo, -⟩ := h ((C - a) / 2) (by linarith)
    have hlt : a < clo := by linarith
    filter_upwards [hs, hsand, hlo.eventually (eventually_gt_nhds hlt)] with N hN hsN hloN
    exact hloN.trans_le (div_le_div_of_nonneg_right hsN.1 hN.le)
  · obtain ⟨lo, hi, clo, chi, hsand, -, hhi, -, hchi⟩ := h ((b - C) / 2) (by linarith)
    have hlt : chi < b := by linarith
    filter_upwards [hs, hsand, hhi.eventually (eventually_lt_nhds hlt)] with N hN hsN hhiN
    exact (div_le_div_of_nonneg_right hsN.2 hN.le).trans_lt hhiN

/-- The approximate squeeze in `HasLeadingTerm` form. -/
theorem hasLeadingTerm_of_approx_squeeze {Z : ℝ → ℝ} {C lam : ℝ} {k : ℕ}
    (h : ∀ ε > 0, ∃ (lo hi : ℝ → ℝ) (clo chi : ℝ),
      (∀ᶠ N in atTop, lo N ≤ Z N ∧ Z N ≤ hi N) ∧
      HasLeadingTerm lo clo lam k ∧ HasLeadingTerm hi chi lam k ∧ C - ε ≤ clo ∧ chi ≤ C + ε) :
    HasLeadingTerm Z C lam k :=
  tendsto_div_of_approx_squeeze ((eventually_gt_atTop 1).mono fun N hN => powLogScale_pos lam k hN)
    fun ε hε => by
      obtain ⟨lo, hi, clo, chi, hsand, hlo, hhi, hclo, hchi⟩ := h ε hε
      exact ⟨lo, hi, clo, chi, hsand, hlo, hhi, hclo, hchi⟩

end Grammar
