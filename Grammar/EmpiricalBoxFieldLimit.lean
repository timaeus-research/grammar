/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldLimit
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The single-box empirical partition function with a random continuous field

The box-level analogue of `tendstoInDistribution_tupleZ_div`: the field is a random element of
`C([0, b]^d, ℝ)`, extended to `ℝ^d` by clamping (`boxExt`), and the box partition function
`boxZ φ N = empBoxIntegral h k N b (boxExt φ) η` is Lipschitz on every ball of fields, with
an eventual Lipschitz constant for the normalised family; hence the face limit is continuous
and the convergence is uniform on compact families of fields. Convergence in distribution of
the random fields `L n ⇒ G` in `C([0, b]^d, ℝ)` therefore transfers to

`boxZ (L n) n / (n^{−λ} (log n)^{m−1}) ⇒ boxFaceLimit (boxExt G)`.

Tightness of the laws is automatic: a convergent sequence of probability measures on a Polish
space has compact closure, hence is tight (`isTightMeasureSet_range_of_tendstoInDistribution`,
the converse half of Prokhorov's theorem from Mathlib).

This is the contract the grey-book bridge instantiates for a standard-form chart: there the
random field is the restriction of the grey book's empirical process `ξ_n` to the chart box.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-! ### Continuous fields on the closed box, extended by clamping -/

/-- A continuous function on the closed box `[0, b]^d`, extended to `ℝ^d` by clamping. -/
noncomputable def boxExt {b : ℝ} (hb : 0 ≤ b) (φ : C(closedBox d b, ℝ)) : (Fin d → ℝ) → ℝ :=
  fun u => φ ⟨clampBox b u, clampBox_mem_closedBox hb u⟩

theorem continuous_boxExt {b : ℝ} (hb : 0 ≤ b) (φ : C(closedBox d b, ℝ)) :
    Continuous (boxExt hb φ) :=
  φ.continuous.comp ((continuous_clampBox b).subtype_mk _)

theorem boxExt_apply_of_mem {b : ℝ} (hb : 0 ≤ b) (φ : C(closedBox d b, ℝ)) {u : Fin d → ℝ}
    (hu : u ∈ closedBox d b) : boxExt hb φ u = φ ⟨u, hu⟩ := by
  unfold boxExt
  congr 1
  exact Subtype.ext (clampBox_eq_of_mem hu)

theorem abs_boxExt_le {b : ℝ} (hb : 0 ≤ b) (φ : C(closedBox d b, ℝ)) (u : Fin d → ℝ) :
    |boxExt hb φ u| ≤ ‖φ‖ := by
  rw [← Real.norm_eq_abs]
  exact φ.norm_coe_le_norm _

theorem abs_boxExt_sub_le {b : ℝ} (hb : 0 ≤ b) (φ ψ : C(closedBox d b, ℝ)) (u : Fin d → ℝ) :
    |boxExt hb φ u - boxExt hb ψ u| ≤ ‖φ - ψ‖ := by
  rw [← Real.norm_eq_abs]
  exact (φ - ψ).norm_coe_le_norm _

/-! ### The box partition function as a function of the field -/

/-- The empirical box partition function at sample size `N`, as a function of the continuous
field on the closed box. -/
noncomputable def boxZ (h k : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b) (η : (Fin d → ℝ) → ℝ)
    (φ : C(closedBox d b, ℝ)) (N : ℝ) : ℝ :=
  empBoxIntegral h k N b (boxExt hb φ) η

/-- Lipschitz bound in the field on a ball of radius `R`, with the damped zero-field integral
as the Lipschitz factor. -/
theorem abs_boxZ_sub_le (h k : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) {A : ℝ} (hA : ∀ u ∈ closedBox d b, |η u| ≤ A) {N : ℝ} (hN : 0 ≤ N)
    {R : ℝ} {φ ψ : C(closedBox d b, ℝ)} (hφ : ‖φ‖ ≤ R) (hψ : ‖ψ‖ ≤ R) :
    |boxZ h k hb η φ N - boxZ h k hb η ψ N| ≤
      Real.exp (R ^ 2) * ‖φ - ψ‖ * A * empBoxIntegral h k (N / 2) b (fun _ => 0) fun _ => 1 :=
  abs_empBoxIntegral_sub_le h k hN (continuous_boxExt hb φ) (continuous_boxExt hb ψ) hηc
    (fun u _ => (abs_boxExt_le hb φ u).trans hφ) (fun u _ => (abs_boxExt_le hb ψ u).trans hψ)
    (fun u _ => abs_boxExt_sub_le hb φ ψ u) fun u hu => hA u (box_subset_closedBox b hu)

/-- A continuous amplitude is bounded on the closed box by a nonnegative constant. -/
theorem exists_abs_le_of_continuous {b : ℝ} {η : (Fin d → ℝ) → ℝ} (hηc : Continuous η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ closedBox d b, |η u| ≤ A := by
  have hcont : ContinuousOn η (closedBox d b) := hηc.continuousOn
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBox b).exists_bound_of_continuousOn hcont
  refine ⟨max A₀ 0, le_max_right _ _, fun u hu => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hA₀ u hu).trans (le_max_left _ _)

theorem exists_lipschitz_boxZ (h k : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) {N : ℝ} (hN : 0 ≤ N) (R : ℝ) :
    ∃ L : ℝ, ∀ φ ψ : C(closedBox d b, ℝ), ‖φ‖ ≤ R → ‖ψ‖ ≤ R →
      |boxZ h k hb η φ N - boxZ h k hb η ψ N| ≤ L * ‖φ - ψ‖ := by
  obtain ⟨A, _, hA⟩ := exists_abs_le_of_continuous (b := b) hηc
  refine ⟨Real.exp (R ^ 2) * A * empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1),
    fun φ ψ hφ hψ => ?_⟩
  refine (abs_boxZ_sub_le h k hb hηc hA hN hφ hψ).trans (le_of_eq ?_)
  ring

/-- The box partition function at fixed `N ≥ 0` is continuous in the field. -/
theorem continuous_boxZ (h k : Fin d → ℕ) {b : ℝ} (hb : 0 ≤ b) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) {N : ℝ} (hN : 0 ≤ N) : Continuous fun φ => boxZ h k hb η φ N :=
  SmoothEngine.ResolvedData.continuous_of_lipschitz_on_balls (exists_lipschitz_boxZ h k hb hηc hN)

/-! ### The normalised family: eventual Lipschitz bound and pointwise limit -/

/-- Eventual Lipschitz bound of the normalised box partition functions on a ball of fields. -/
theorem exists_eventually_lipschitz_boxZ_div (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m)
    {η : (Fin d → ℝ) → ℝ} (hηc : Continuous η) (R : ℝ) :
    ∃ L : ℝ, ∀ᶠ N in atTop, ∀ φ ψ : C(closedBox d b, ℝ), ‖φ‖ ≤ R → ‖ψ‖ ≤ R →
      |boxZ h k hb.le η φ N / powLogScale lam (m - 1) N -
        boxZ h k hb.le η ψ N / powLogScale lam (m - 1) N| ≤ L * ‖φ - ψ‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_of_continuous (b := b) hηc
  obtain ⟨C, hC⟩ := exists_eventually_bound_empBoxIntegral_half h k hk hb hm hlead
  refine ⟨Real.exp (R ^ 2) * A * C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with N hN hN1
  intro φ ψ hφ hψ
  have hs : 0 < powLogScale lam (m - 1) N := powLogScale_pos _ _ hN1
  have hpl : powLogScale lam (m - 1) N = N ^ (-lam) * Real.log N ^ (m - 1) := rfl
  have hZ := abs_boxZ_sub_le h k hb.le hηc hA (by linarith : (0 : ℝ) ≤ N) hφ hψ
  have hZ0 : empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) ≤
      C * powLogScale lam (m - 1) N := by
    rw [← div_le_iff₀ hs, hpl]
    exact (le_abs_self _).trans hN
  rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc |boxZ h k hb.le η φ N - boxZ h k hb.le η ψ N|
      ≤ Real.exp (R ^ 2) * ‖φ - ψ‖ * A *
          empBoxIntegral h k (N / 2) b (fun _ => 0) (fun _ => 1) := hZ
    _ ≤ Real.exp (R ^ 2) * ‖φ - ψ‖ * A * (C * powLogScale lam (m - 1) N) :=
        mul_le_mul_of_nonneg_left hZ0
          (mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hA0)
    _ = Real.exp (R ^ 2) * A * C * ‖φ - ψ‖ * powLogScale lam (m - 1) N := by ring

/-- Pointwise leading asymptotics of the box partition function at a fixed continuous field. -/
theorem tendsto_boxZ_div (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b) {lam : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) (φ : C(closedBox d b, ℝ)) :
    Tendsto (fun N => boxZ h k hb.le η φ N / powLogScale lam (m - 1) N) atTop
      (𝓝 (boxFaceLimit h k lam m b (boxExt hb.le φ) η)) :=
  tendsto_empBoxIntegral_div_boxFaceLimit h k hk hb hm hlead _ η (continuous_boxExt hb.le φ) hηc

/-- The face limit is Lipschitz in the field on every ball. -/
theorem exists_lipschitz_boxLimit (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) (R : ℝ) :
    ∃ L : ℝ, ∀ φ ψ : C(closedBox d b, ℝ), ‖φ‖ ≤ R → ‖ψ‖ ≤ R →
      |boxFaceLimit h k lam m b (boxExt hb.le φ) η - boxFaceLimit h k lam m b (boxExt hb.le ψ) η|
        ≤ L * ‖φ - ψ‖ := by
  obtain ⟨L, hL⟩ := exists_eventually_lipschitz_boxZ_div h k hk hb hm hlead hηc R
  refine ⟨L, fun φ ψ hφ hψ => ?_⟩
  have h := abs_limit_sub_le_of_eventually_lipschitz
    (T := fun N φ => boxZ h k hb.le η φ N / powLogScale lam (m - 1) N)
    (Tlim := fun φ => boxFaceLimit h k lam m b (boxExt hb.le φ) η)
    (C := Metric.closedBall 0 R) (L := L)
    (fun φ _ => tendsto_boxZ_div h k hk hb hm hlead hηc φ)
    (hL.mono fun N hN φ hφ ψ hψ => by
      rw [mem_closedBall_zero_iff] at hφ hψ
      rw [dist_eq_norm]
      exact hN φ ψ hφ hψ)
    (mem_closedBall_zero_iff.2 hφ) (mem_closedBall_zero_iff.2 hψ)
  rwa [dist_eq_norm] at h

/-- The face limit is continuous in the field. -/
theorem continuous_boxLimit (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) :
    Continuous fun φ : C(closedBox d b, ℝ) => boxFaceLimit h k lam m b (boxExt hb.le φ) η :=
  SmoothEngine.ResolvedData.continuous_of_lipschitz_on_balls
    (exists_lipschitz_boxLimit h k hk hb hm hlead hηc)

/-- Uniform convergence of the normalised box partition functions on compact families of
fields. -/
theorem tendstoUniformlyOn_boxZ_div (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m) {η : (Fin d → ℝ) → ℝ}
    (hηc : Continuous η) {C : Set C(closedBox d b, ℝ)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun N φ => boxZ h k hb.le η φ N / powLogScale lam (m - 1) N)
      (fun φ => boxFaceLimit h k lam m b (boxExt hb.le φ) η) atTop C := by
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  obtain ⟨L, hL⟩ := exists_eventually_lipschitz_boxZ_div h k hk hb hm hlead hηc R
  refine tendstoUniformlyOn_of_eventually_lipschitz (L := L) hC
    (fun φ _ => tendsto_boxZ_div h k hk hb hm hlead hηc φ) ?_
  filter_upwards [hL] with N hN
  intro φ hφ ψ hψ
  rw [dist_eq_norm]
  exact hN φ ψ (hR φ hφ) (hR ψ hψ)

/-- Uniform convergence on compacts along the integer sample sizes. -/
theorem tendstoUniformlyOn_boxZ_div_nat (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m)
    {η : (Fin d → ℝ) → ℝ} (hηc : Continuous η) {C : Set C(closedBox d b, ℝ)} (hC : IsCompact C) :
    TendstoUniformlyOn (fun (n : ℕ) φ => boxZ h k hb.le η φ n / powLogScale lam (m - 1) n)
      (fun φ => boxFaceLimit h k lam m b (boxExt hb.le φ) η) atTop C := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_boxZ_div h k hk hb hm hlead hηc hC) ε hε
  exact tendsto_natCast_atTop_atTop.eventually h

/-! ### Tightness of a convergent sequence of laws (converse Prokhorov) -/

/-- In a Polish space, the laws of a sequence converging in distribution form a tight set: the
sequence together with its limit is compact in the topology of weak convergence. -/
theorem isTightMeasureSet_range_of_tendstoInDistribution {E : Type*} [MetricSpace E]
    [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {L : ℕ → Ω → E}
    {G : Ω' → E} (hLG : TendstoInDistribution L atTop G (fun _ => P) P') :
    IsTightMeasureSet (Set.range fun n => P.map (L n)) := by
  have hc := hLG.tendsto.isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure (by rwa [hc.isClosed.closure_eq])
  refine ht.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨_, Set.subset_insert _ _ (Set.mem_range_self n), rfl⟩

/-! ### The single-box random-field theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- ★★ **Convergence in distribution of the normalised box partition function** at a random
continuous field: if `L n ⇒ G` in `C([0, b]^d, ℝ)`, then at a box-leading pair `(λ, m)`
`boxZ (L n) n / (n^{−λ} (log n)^{m−1}) ⇒ boxFaceLimit (boxExt G)`. Tightness of the laws is
automatic (converse Prokhorov). -/
theorem tendstoInDistribution_boxZ_div (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) {lam : ℝ} {m : ℕ} (hm : 1 ≤ m) (hlead : BoxLeading h k lam m)
    {η : (Fin d → ℝ) → ℝ} (hηc : Continuous η) [MeasurableSpace C(closedBox d b, ℝ)]
    [BorelSpace C(closedBox d b, ℝ)] {L : ℕ → Ω → C(closedBox d b, ℝ)}
    (hLm : ∀ n, Measurable (L n)) {G : Ω' → C(closedBox d b, ℝ)}
    (hLG : TendstoInDistribution L atTop G (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => boxZ h k hb.le η (L n ω) n / powLogScale lam (m - 1) n) atTop
      (fun ω' => boxFaceLimit h k lam m b (boxExt hb.le (G ω')) η) (fun _ => P) P' :=
  tendstoInDistribution_comp_of_tendstoUniformlyOn_compacts hLm hLG
    (isTightMeasureSet_range_of_tendstoInDistribution hLG)
    (T := fun (n : ℕ) φ => boxZ h k hb.le η φ n / powLogScale lam (m - 1) n)
    (fun n => (continuous_boxZ h k hb.le hηc (Nat.cast_nonneg n)).div_const _)
    (continuous_boxLimit h k hk hb hm hlead hηc)
    fun _ hC => tendstoUniformlyOn_boxZ_div_nat h k hk hb hm hlead hηc hC

end Grammar
