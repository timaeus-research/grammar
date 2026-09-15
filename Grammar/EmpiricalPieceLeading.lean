/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFaceFunctional

/-!
# The empirical box integral on `(0,b]^d`: leading term at a chart-leading pair

`empBoxIntegral h k N b ξ η = ∫_{(0,b]^d} η u^h e^{−N u^{2k} + √N u^k ξ(u)} du` (temperature one,
any `d`, `ξ` continuous). At a pair `(λ, m)` which is **chart-leading** for the box (all ratios
`(h_i+1)/2k_i ≥ λ`, at most `m` of them equal to `λ`; `BoxLeading`), the normalised integral
converges to the **box face limit**: the empirical face functional if exactly `m` coordinates
have ratio `λ`, and `0` otherwise (`tendsto_empBoxIntegral_div_boxFaceLimit`). The case `d = 0`
(no active coordinate) is exponentially small. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {d : ℕ}

/-- The empirical box integral at temperature one. -/
noncomputable def empBoxIntegral (h k : Fin d → ℕ) (N b : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ u in SmoothEngine.box (Fin d) b, η u * SmoothEngine.mono h u *
    Real.exp (-N * SmoothEngine.mono (fun i => 2 * k i) u +
      Real.sqrt N * SmoothEngine.mono k u * ξ u)

theorem empBoxIntegral_eq_origPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (N b : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) :
    empBoxIntegral h k N b ξ η = origPhaseIntegral n h k 1 N b ξ η := by
  unfold empBoxIntegral origPhaseIntegral SmoothEngine.mono
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u _ => ?_
  simp only [one_mul, neg_mul]

/-- The chart-leading condition for a box at the pair `(λ, m)`. -/
def BoxLeading (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) : Prop :=
  (∀ i, lam ≤ ratioExp h k i) ∧ multCount (ratioExp h k) lam ≤ m

/-- The box face limit at `(λ, m)`: the empirical face functional when the box realises the
multiplicity `m`, and `0` otherwise. -/
noncomputable def boxFaceLimit (h k : Fin d → ℕ) (lam : ℝ) (m : ℕ) (b : ℝ)
    (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  if multCount (ratioExp h k) lam = m then faceFunctional h k lam b ξ η else 0

/-! ### Positive dimension -/

theorem tendsto_empBoxIntegral_div_faceFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {lam : ℝ} (hmin : ∀ i, lam ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = lam) (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ)
    (hηc : Continuous η) :
    Tendsto (fun N => empBoxIntegral h k N b ξ η /
        (N ^ (-lam) * Real.log N ^ (multCount (ratioExp h k) lam - 1))) atTop
      (𝓝 (faceFunctional h k lam b ξ η)) := by
  have := spatialPhase_box_tendsto n h k hk 1 one_pos hb hmin hatt ξ η hξc hηc
  rw [spatialFace_dilated_eq_faceFunctional n h k hk hmin hatt hb ξ η hξc hηc] at this
  refine this.congr fun N => ?_
  rw [empBoxIntegral_eq_origPhaseIntegral]

theorem tendsto_empBoxIntegral_div_boxFaceLimit_succ (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hlead : BoxLeading h k lam m) (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ)
    (hηc : Continuous η) :
    Tendsto (fun N => empBoxIntegral h k N b ξ η / (N ^ (-lam) * Real.log N ^ (m - 1))) atTop
      (𝓝 (boxFaceLimit h k lam m b ξ η)) := by
  obtain ⟨hmin, hle⟩ := hlead
  unfold boxFaceLimit
  by_cases heq : multCount (ratioExp h k) lam = m
  · rw [if_pos heq]
    have hatt : ∃ i, ratioExp h k i = lam := by
      have hpos : 0 < (resSet h k lam).card := by rw [card_resSet, heq]; omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
      exact ⟨i, mem_resSet.1 hi⟩
    have := tendsto_empBoxIntegral_div_faceFunctional n h k hk hb hmin hatt ξ η hξc hηc
    rwa [heq] at this
  · rw [if_neg heq]
    have hlt : multCount (ratioExp h k) lam < m := lt_of_le_of_ne hle heq
    by_cases hatt : ∃ i, ratioExp h k i = lam
    · -- the box attains `λ` with a smaller multiplicity
      have hpos : 1 ≤ multCount (ratioExp h k) lam := by
        obtain ⟨i, hi⟩ := hatt
        rw [← card_resSet]
        exact Finset.card_pos.2 ⟨i, mem_resSet.2 hi⟩
      have hpre : SmoothEngine.Precedes lam (m - 1) lam (multCount (ratioExp h k) lam - 1) :=
        Or.inr ⟨rfl, by omega⟩
      have := tendsto_origPhaseIntegral_div_zero_of_precedes n h k hk 1 one_pos hb hmin hatt ξ η
        hξc hηc hpre
      refine this.congr fun N => ?_
      rw [empBoxIntegral_eq_origPhaseIntegral]
    · -- every ratio exceeds `λ`: the box's own exponent is larger
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (ratioExp h k) Finset.univ_nonempty
      set l' := ratioExp h k i₀ with hl'
      have hmin' : ∀ i, l' ≤ ratioExp h k i := fun i => hi₀ i (Finset.mem_univ i)
      have hatt' : ∃ i, ratioExp h k i = l' := ⟨i₀, rfl⟩
      have hlt' : lam < l' := lt_of_le_of_ne (hmin i₀) fun h' => hatt ⟨i₀, h'.symm⟩
      have hpre : SmoothEngine.Precedes lam (m - 1) l' (multCount (ratioExp h k) l' - 1) :=
        Or.inl hlt'
      have := tendsto_origPhaseIntegral_div_zero_of_precedes n h k hk 1 one_pos hb hmin' hatt' ξ η
        hξc hηc hpre
      refine this.congr fun N => ?_
      rw [empBoxIntegral_eq_origPhaseIntegral]

/-! ### Dimension zero -/

theorem box_fin_zero_eq_univ (b : ℝ) : SmoothEngine.box (Fin 0) b = univ := by
  ext u
  simp only [SmoothEngine.box, Set.mem_pi, Set.mem_univ, true_implies, iff_true]
  exact fun i => Fin.elim0 i

theorem empBoxIntegral_fin_zero (h k : Fin 0 → ℕ) (N b : ℝ) (ξ η : (Fin 0 → ℝ) → ℝ) :
    empBoxIntegral h k N b ξ η =
      η default * Real.exp (-N + Real.sqrt N * ξ default) := by
  unfold empBoxIntegral
  rw [box_fin_zero_eq_univ, Measure.restrict_univ, volume_pi, Measure.pi_of_empty, integral_dirac]
  simp only [SmoothEngine.mono, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  have hX : (fun a : Fin 0 => (isEmptyElim a : ℝ)) = default := Subsingleton.elim _ _
  simp only [hX]

theorem tendsto_empBoxIntegral_div_zero_fin_zero (h k : Fin 0 → ℕ) (b : ℝ) {lam : ℝ} (q : ℕ)
    (ξ η : (Fin 0 → ℝ) → ℝ) :
    Tendsto (fun N => empBoxIntegral h k N b ξ η / (N ^ (-lam) * Real.log N ^ q)) atTop (𝓝 0) := by
  simp only [empBoxIntegral_fin_zero]
  set a := ξ default with ha
  have hexp : Tendsto (fun N : ℝ => N ^ lam * Real.exp (-(1 / 2) * N)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (1 / 2) (by norm_num)
  have h1 := hexp.const_mul (|η default| * Real.exp (a ^ 2 / 2))
  rw [mul_zero] at h1
  have h0 := h1.zero_mul_isBoundedUnder_le (SmoothEngine.isBoundedUnder_inv_log_pow q)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hkey : Real.exp (-N + Real.sqrt N * a) ≤
      Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 2) * N) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (Real.sqrt N - a), Real.sq_sqrt hN0.le])
  have hpos : 0 < N ^ (-lam) * Real.log N ^ q :=
    mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos hlog _)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, abs_mul, Real.abs_exp, div_le_iff₀ hpos]
  calc |η default| * Real.exp (-N + Real.sqrt N * a)
      ≤ |η default| * (Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 2) * N)) :=
        mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    _ = |η default| * Real.exp (a ^ 2 / 2) * (N ^ lam * Real.exp (-(1 / 2) * N)) *
          (Real.log N ^ q)⁻¹ * (N ^ (-lam) * Real.log N ^ q) := by
        rw [Real.rpow_neg hN0.le]
        field_simp

/-! ### The combined statement -/

/-- ★★ **The empirical box integral at a chart-leading pair** converges, normalised at `(λ, m−1)`,
to the box face limit. -/
theorem tendsto_empBoxIntegral_div_boxFaceLimit (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m)
    (ξ η : (Fin d → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    Tendsto (fun N => empBoxIntegral h k N b ξ η / (N ^ (-lam) * Real.log N ^ (m - 1))) atTop
      (𝓝 (boxFaceLimit h k lam m b ξ η)) := by
  cases d with
  | zero =>
    have hmc : multCount (ratioExp h k) lam = 0 := by simp [multCount]
    unfold boxFaceLimit
    rw [if_neg (by omega)]
    exact tendsto_empBoxIntegral_div_zero_fin_zero h k b (m - 1) ξ η
  | succ n => exact tendsto_empBoxIntegral_div_boxFaceLimit_succ n h k hk hb hm hlead ξ η hξc hηc

end Grammar
