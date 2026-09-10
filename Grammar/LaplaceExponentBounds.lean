/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.Localisation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Two-sided sublevel growth implies two-sided Laplace growth

The resolution input available today (the chart form of `timaeus-research/hironaka`, with
continuous units) determines the sublevel volumes of the phase two-sidedly,
`μ{K ≤ t} ≍ t^λ (−log t)^q` as `t → 0⁺` (`SublevelTheta`, the shape of hironaka's
`HasLLCExponentsOn`).  This file proves the coefficient-free consequence for the population
integral: `∫ e^{−NK} dμ ≍ N^{−λ} (log N)^q` as `N → ∞` (`LaplaceTheta`), by an elementary Abelian
argument — the lower bound from the sublevel set `{K ≤ 1/N}`, the upper bound from a dyadic
decomposition of the sublevel sets `{K ≤ 2^j/N}` and the exponentially small tail — and its
stability under a weight bounded above and bounded below near the zero locus
(`laplaceTheta_weighted`), in particular for the localisation datum's population integral
(`LocalisationData.Z_isTheta`).

`q` is the log degree (the paper's `m − 1`).  Non-claims: no leading coefficient, no asymptotic
equivalence, no converse (Tauberian) statement, no signed observable.
-/

open MeasureTheory Filter Topology Asymptotics Set
open scoped ENNReal

namespace Grammar

/-- The power–log rate `N^{−λ} (log N)^q`. -/
noncomputable def powerLogRate (lam : ℝ) (q : ℕ) (N : ℝ) : ℝ := N ^ (-lam) * Real.log N ^ q

/-- The sublevel mass `μ{f ≤ t}`. -/
noncomputable def sublevelMass {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (t : ℝ) :
    ℝ := (μ {x | f x ≤ t}).toReal

/-- The sublevel scale `t^λ (−log t)^q`. -/
noncomputable def sublevelScale (lam : ℝ) (q : ℕ) (t : ℝ) : ℝ := t ^ lam * (-Real.log t) ^ q

/-- **Two-sided sublevel growth**: `μ{f ≤ t} ≍ t^λ (−log t)^q` as `t → 0⁺` (hironaka's
`HasLLCExponentsOn volume K f λ (q+1)` for the restricted measure). -/
def SublevelTheta {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (lam : ℝ) (q : ℕ) :
    Prop := sublevelMass μ f =Θ[𝓝[>] 0] sublevelScale lam q

/-- **Two-sided Laplace growth**: `∫ e^{−N f} dμ ≍ N^{−λ} (log N)^q` as `N → ∞`. -/
def LaplaceTheta {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (lam : ℝ) (q : ℕ) :
    Prop := (fun N => ∫ x, Real.exp (-N * f x) ∂μ) =Θ[atTop] powerLogRate lam q

theorem powerLogRate_pos {lam : ℝ} {q : ℕ} {N : ℝ} (hN : 1 < N) : 0 < powerLogRate lam q N :=
  mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN) _)

theorem powerLogRate_nonneg {lam : ℝ} {q : ℕ} {N : ℝ} (hN : 1 ≤ N) : 0 ≤ powerLogRate lam q N :=
  mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg hN) _)

theorem sublevelScale_inv {lam : ℝ} {q : ℕ} {N : ℝ} (hN : 0 < N) :
    sublevelScale lam q N⁻¹ = powerLogRate lam q N := by
  unfold sublevelScale powerLogRate
  rw [Real.inv_rpow hN.le, ← Real.rpow_neg hN.le, Real.log_inv, neg_neg]

theorem sublevelScale_nonneg {lam : ℝ} {q : ℕ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ sublevelScale lam q t :=
  mul_nonneg (Real.rpow_nonneg ht.le _)
    (pow_nonneg (neg_nonneg.2 (Real.log_nonpos ht.le ht1)) _)

theorem sublevelMass_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (t : ℝ) :
    0 ≤ sublevelMass μ f t := ENNReal.toReal_nonneg

theorem sublevelMass_mono {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) {s t : ℝ} (h : s ≤ t) : sublevelMass μ f s ≤ sublevelMass μ f t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun _ hx => le_trans hx h)

/-- Two-sided sublevel growth as explicit constants on a right neighbourhood of `0`. -/
theorem SublevelTheta.exists_bounds {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {lam : ℝ} {q : ℕ} (h : SublevelTheta μ f lam q) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧ ε < 1 ∧ ∀ t, 0 < t → t ≤ ε →
      c * sublevelScale lam q t ≤ sublevelMass μ f t ∧
        sublevelMass μ f t ≤ C * sublevelScale lam q t := by
  obtain ⟨C, hC, hup⟩ := h.1.exists_pos
  obtain ⟨c', hc', hlow⟩ := h.2.exists_pos
  have hev := (hup.bound.and hlow.bound).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu' : 0 < u := hu
  refine ⟨c'⁻¹, C, min (u / 2) (1 / 2), inv_pos.2 hc', hC, lt_min (half_pos hu') (by norm_num), ?_,
    fun t ht htε => ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  have htu : t ∈ Ioo (0 : ℝ) u :=
    ⟨ht, (htε.trans (min_le_left _ _)).trans_lt (by linarith)⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hsub htu
  have hm := sublevelMass_nonneg μ f t
  have hs := sublevelScale_nonneg (lam := lam) (q := q) ht (h3.2.le)
  rw [Real.norm_of_nonneg hm, Real.norm_of_nonneg hs] at h1 h2
  refine ⟨?_, h1⟩
  rw [inv_mul_le_iff₀ hc']
  exact h2

section Bounds

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}

theorem integrable_exp_neg_mul (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun x => Real.exp (-N * f x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hf.const_mul (-N)).exp.aestronglyMeasurable ?_
  filter_upwards [hf0] with x hx
  have hx' : 0 ≤ f x := hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.2 (by nlinarith)

/-- **The lower bound** `∫ e^{−N f} ≥ e^{−1} μ{f ≤ 1/N}`, weighted by `w ≥ c` on the sublevel
set. -/
theorem le_integral_exp_neg_mul (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) {w : X → ℝ}
    (hwm : AEStronglyMeasurable w μ) {c C : ℝ} (hw0 : 0 ≤ᵐ[μ] w) (hwC : ∀ᵐ x ∂μ, w x ≤ C)
    {N : ℝ} (hN : 0 < N) (hwc : ∀ᵐ x ∂μ, f x ≤ N⁻¹ → c ≤ w x) :
    c * Real.exp (-1) * sublevelMass μ f N⁻¹ ≤ ∫ x, w x * Real.exp (-N * f x) ∂μ := by
  have hS : MeasurableSet {x | f x ≤ N⁻¹} := measurableSet_le hf measurable_const
  have hint : Integrable (fun x => w x * Real.exp (-N * f x)) μ := by
    refine (integrable_const (C : ℝ)).mono'
      (hwm.mul (hf.const_mul (-N)).exp.aestronglyMeasurable) ?_
    filter_upwards [hf0, hw0, hwC] with x hx h0 hC
    have hx' : 0 ≤ f x := hx
    have h0' : 0 ≤ w x := h0
    rw [Real.norm_of_nonneg (mul_nonneg h0' (Real.exp_pos _).le)]
    exact (mul_le_of_le_one_right h0' (Real.exp_le_one_iff.2 (by nlinarith))).trans hC
  have hind : Integrable ({x | f x ≤ N⁻¹}.indicator fun _ => c * Real.exp (-1)) μ :=
    (integrable_const _).indicator hS
  calc c * Real.exp (-1) * sublevelMass μ f N⁻¹
      = ∫ x, {x | f x ≤ N⁻¹}.indicator (fun _ => c * Real.exp (-1)) x ∂μ := by
        rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]; rfl
    _ ≤ ∫ x, w x * Real.exp (-N * f x) ∂μ := by
        refine integral_mono_ae hind hint ?_
        filter_upwards [hw0, hwc] with x h0 hc
        have h0' : 0 ≤ w x := h0
        by_cases hx : f x ≤ N⁻¹
        · rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ N⁻¹} from hx)]
          refine mul_le_mul (hc hx) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le h0'
          have := mul_le_mul_of_nonneg_left hx hN.le
          rw [mul_inv_cancel₀ hN.ne'] at this
          linarith
        · rw [Set.indicator_of_notMem (show x ∉ {x | f x ≤ N⁻¹} from hx)]
          exact mul_nonneg h0' (Real.exp_pos _).le

omit [MeasurableSpace X] in
/-- **The dyadic pointwise bound**:
`e^{−N f} ≤ 1_{f ≤ 1/N} + ∑_{j<J} e^{−2^j} 1_{f ≤ 2^{j+1}/N} + e^{−2^J}`. -/
theorem exp_neg_mul_le_dyadic {N : ℝ} (hN : 0 < N) {x : X} (hx : 0 ≤ f x) (J : ℕ) :
    Real.exp (-N * f x) ≤ {y | f y ≤ 1 / N}.indicator (fun _ => (1 : ℝ)) x +
      ∑ j ∈ Finset.range J,
        Real.exp (-(2 : ℝ) ^ j) * {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x +
      Real.exp (-(2 : ℝ) ^ J) := by
  classical
  have hterm_nonneg : ∀ j, 0 ≤ Real.exp (-(2 : ℝ) ^ j) *
      {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x :=
    fun j => mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hnn : 0 ≤ ∑ j ∈ Finset.range J,
      Real.exp (-(2 : ℝ) ^ j) * {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x :=
    Finset.sum_nonneg fun j _ => hterm_nonneg j
  have h0 : 0 ≤ {y | f y ≤ 1 / N}.indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hJpos := (Real.exp_pos (-(2 : ℝ) ^ J)).le
  by_cases hJ : f x ≤ 2 ^ J / N
  · have hex : ∃ j, f x ≤ 2 ^ j / N := ⟨J, hJ⟩
    have hj₀ : f x ≤ 2 ^ Nat.find hex / N := Nat.find_spec hex
    have hj₀J : Nat.find hex ≤ J := Nat.find_min' hex hJ
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
    · have hx0 : x ∈ {y | f y ≤ 1 / N} := by
        change f x ≤ 1 / N
        rw [hz, pow_zero] at hj₀; exact hj₀
      rw [Set.indicator_of_mem hx0]
      have : Real.exp (-N * f x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      linarith
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hjJ : j < J := by omega
      have hnot : ¬ f x ≤ 2 ^ j / N := Nat.find_min hex (by omega)
      have hmem : x ∈ {y | f y ≤ 2 ^ (j + 1) / N} := by
        change f x ≤ 2 ^ (j + 1) / N
        rw [← hj]; exact hj₀
      have hterm := Finset.single_le_sum (fun i _ => hterm_nonneg i) (Finset.mem_range.2 hjJ)
      rw [Set.indicator_of_mem hmem, mul_one] at hterm
      have hexp : Real.exp (-N * f x) ≤ Real.exp (-(2 : ℝ) ^ j) := by
        apply Real.exp_le_exp.2
        rw [not_le, div_lt_iff₀ hN] at hnot
        linarith
      linarith
  · rw [not_le, div_lt_iff₀ hN] at hJ
    have hexp : Real.exp (-N * f x) ≤ Real.exp (-(2 : ℝ) ^ J) := by
      apply Real.exp_le_exp.2
      linarith
    linarith

/-- **The dyadic integral bound.** -/
theorem integral_exp_le_dyadic (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) {N : ℝ} (hN : 0 < N) (J : ℕ) :
    ∫ x, Real.exp (-N * f x) ∂μ ≤ sublevelMass μ f (1 / N) +
      ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N) +
      Real.exp (-(2 : ℝ) ^ J) * (μ univ).toReal := by
  have hS : ∀ t, MeasurableSet {y | f y ≤ t} := fun t => measurableSet_le hf measurable_const
  have hi1 : Integrable ({y | f y ≤ 1 / N}.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const _).indicator (hS _)
  have hi2 : ∀ j, Integrable (fun x => Real.exp (-(2 : ℝ) ^ j) *
      {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x) μ :=
    fun j => ((integrable_const _).indicator (hS _)).const_mul _
  have hsum : Integrable (fun x => ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) *
      {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x) μ :=
    integrable_finsetSum _ fun j _ => hi2 j
  have hi3 : Integrable (fun _ : X => Real.exp (-(2 : ℝ) ^ J)) μ := integrable_const _
  calc ∫ x, Real.exp (-N * f x) ∂μ
      ≤ ∫ x, ({y | f y ≤ 1 / N}.indicator (fun _ => (1 : ℝ)) x +
          ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) *
            {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x +
          Real.exp (-(2 : ℝ) ^ J)) ∂μ := by
        refine integral_mono_ae (integrable_exp_neg_mul hf hf0 hN.le) ((hi1.add hsum).add hi3) ?_
        filter_upwards [hf0] with x hx
        exact exp_neg_mul_le_dyadic hN hx J
    _ = _ := by
        have hA : Integrable (fun x => {y | f y ≤ 1 / N}.indicator (fun _ => (1 : ℝ)) x +
            ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) *
              {y | f y ≤ 2 ^ (j + 1) / N}.indicator (fun _ => (1 : ℝ)) x) μ := hi1.add hsum
        rw [integral_add hA hi3, integral_add hi1 hsum,
          integral_finsetSum _ fun j _ => hi2 j, integral_const, integral_indicator_const _ (hS _)]
        simp only [integral_const_mul, integral_indicator_const _ (hS _), smul_eq_mul, mul_one]
        unfold sublevelMass
        simp only [measureReal_def]
        ring

/-- The dyadic weights are summably dominated: `e^{−2^j} (2^{j+1})^λ ≤ 2^{k+1} (k+1)! 2^{−j}` with
`k = ⌈λ⌉`. -/
theorem exp_neg_two_pow_mul_rpow_le (lam : ℝ) (j : ℕ) :
    Real.exp (-(2 : ℝ) ^ j) * ((2 : ℝ) ^ (j + 1)) ^ lam ≤
      (2 : ℝ) ^ ⌈lam⌉₊ * ((⌈lam⌉₊ + 1).factorial : ℝ) * (1 / 2) ^ j := by
  set k := ⌈lam⌉₊ with hk
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : ((2 : ℝ) ^ (j + 1)) ^ lam ≤ ((2 : ℝ) ^ (j + 1)) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (Nat.le_ceil lam)
  rw [Real.rpow_natCast] at h1
  have h2 : Real.exp (-(2 : ℝ) ^ j) ≤ ((k + 1).factorial : ℝ) / ((2 : ℝ) ^ j) ^ (k + 1) := by
    have := Real.pow_div_factorial_le_exp _ h2j.le (k + 1)
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  calc Real.exp (-(2 : ℝ) ^ j) * ((2 : ℝ) ^ (j + 1)) ^ lam
      ≤ ((k + 1).factorial : ℝ) / ((2 : ℝ) ^ j) ^ (k + 1) * ((2 : ℝ) ^ (j + 1)) ^ k :=
        mul_le_mul h2 h1 (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (2 : ℝ) ^ k * ((k + 1).factorial : ℝ) * (1 / 2) ^ j := by
        rw [one_div, inv_pow]
        field_simp
        ring

/-- **The upper bound** from a one-sided sublevel bound on `(0, ε]`: for `εN ≥ 2`,
`∫ e^{−N f} ≤ C (1 + 2^{k+1}(k+1)!) N^{−λ}(log N)^q + μ(X) e^{−εN/2}` with `k = ⌈λ⌉`. -/
theorem integral_exp_le_of_sublevel_bound (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) {C ε lam : ℝ}
    {q : ℕ} (hC : 0 < C) (hε : 0 < ε) (hε1 : ε < 1)
    (hmass : ∀ t, 0 < t → t ≤ ε → sublevelMass μ f t ≤ C * sublevelScale lam q t) {N : ℝ}
    (hN : 2 ≤ ε * N) :
    ∫ x, Real.exp (-N * f x) ∂μ ≤
      C * (1 + (2 : ℝ) ^ (⌈lam⌉₊ + 1) * ((⌈lam⌉₊ + 1).factorial : ℝ)) * powerLogRate lam q N +
        (μ univ).toReal * Real.exp (-(ε / 2) * N) := by
  have hNpos : 0 < N := by nlinarith
  have hN1 : 1 < N := by nlinarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  set J := Nat.log 2 ⌊ε * N⌋₊ with hJ
  have hfl : (1 : ℕ) ≤ ⌊ε * N⌋₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.floor_eq_zero, not_lt]; linarith)
  have h2J : (2 : ℝ) ^ J ≤ ε * N := by
    have := Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.1 hfl)
    calc (2 : ℝ) ^ J = ((2 ^ J : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊ε * N⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ ε * N := Nat.floor_le (by positivity)
  have hJ2 : ε * N < 2 * (2 : ℝ) ^ J := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊ε * N⌋₊
    calc ε * N < (⌊ε * N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      _ ≤ ((2 ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * (2 : ℝ) ^ J := by push_cast; ring
  -- the level bounds
  have hlevel : ∀ j, j + 1 ≤ J → 0 < (2 : ℝ) ^ (j + 1) / N ∧ (2 : ℝ) ^ (j + 1) / N ≤ ε := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hNpos]
    calc (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
      _ ≤ ε * N := h2J
  have hpl : 0 ≤ powerLogRate lam q N := powerLogRate_nonneg hN1.le
  have hscale : ∀ t, N⁻¹ ≤ t → t ≤ ε →
      sublevelScale lam q t ≤ t ^ lam * Real.log N ^ q := by
    intro t htN htε
    have ht : 0 < t := lt_of_lt_of_le (inv_pos.2 hNpos) htN
    unfold sublevelScale
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ q) (Real.rpow_nonneg ht.le _)
    · exact neg_nonneg.2 (Real.log_nonpos ht.le (htε.trans hε1.le))
    · have := Real.log_le_log (inv_pos.2 hNpos) htN
      rw [Real.log_inv] at this
      linarith
  -- the first term
  have hfirst : sublevelMass μ f (1 / N) ≤ C * powerLogRate lam q N := by
    have h1N : 1 / N ≤ ε := by
      rw [div_le_iff₀ hNpos]; linarith
    calc sublevelMass μ f (1 / N) ≤ C * sublevelScale lam q (1 / N) :=
          hmass _ (by positivity) h1N
      _ = C * powerLogRate lam q N := by rw [one_div, sublevelScale_inv hNpos]
  -- (the first term uses the exact scale at `1/N`)
  -- the dyadic terms
  have hdy : ∀ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N) ≤
      C * powerLogRate lam q N *
        ((2 : ℝ) ^ ⌈lam⌉₊ * ((⌈lam⌉₊ + 1).factorial : ℝ) * (1 / 2) ^ j) := by
    intro j hj
    have hj' : j + 1 ≤ J := Finset.mem_range.1 hj
    obtain ⟨ht, htε⟩ := hlevel j hj'
    have hm := hmass _ ht htε
    have htN : N⁻¹ ≤ (2 : ℝ) ^ (j + 1) / N := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num)) hNpos.le
    have hs := hscale _ htN htε
    have hpow : ((2 : ℝ) ^ (j + 1) / N) ^ lam = ((2 : ℝ) ^ (j + 1)) ^ lam * N ^ (-lam) := by
      rw [Real.div_rpow (by positivity) hNpos.le, Real.rpow_neg hNpos.le, div_eq_mul_inv]
    have hE := exp_neg_two_pow_mul_rpow_le lam j
    calc Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N)
        ≤ Real.exp (-(2 : ℝ) ^ j) * (C * (((2 : ℝ) ^ (j + 1) / N) ^ lam * Real.log N ^ q)) :=
          mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hs hC.le))
            (Real.exp_pos _).le
      _ = C * powerLogRate lam q N * (Real.exp (-(2 : ℝ) ^ j) * ((2 : ℝ) ^ (j + 1)) ^ lam) := by
          rw [hpow]; unfold powerLogRate; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (mul_nonneg hC.le hpl)
  have hgeom : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j ≤ 2 := sum_geometric_two_le J
  have hsum : ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N) ≤
      C * powerLogRate lam q N * ((2 : ℝ) ^ (⌈lam⌉₊ + 1) * ((⌈lam⌉₊ + 1).factorial : ℝ)) := by
    calc ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N)
        ≤ ∑ j ∈ Finset.range J, C * powerLogRate lam q N *
            ((2 : ℝ) ^ ⌈lam⌉₊ * ((⌈lam⌉₊ + 1).factorial : ℝ) * (1 / 2) ^ j) :=
          Finset.sum_le_sum hdy
      _ = C * powerLogRate lam q N * ((2 : ℝ) ^ ⌈lam⌉₊ * ((⌈lam⌉₊ + 1).factorial : ℝ)) *
            ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ C * powerLogRate lam q N * ((2 : ℝ) ^ ⌈lam⌉₊ * ((⌈lam⌉₊ + 1).factorial : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg (mul_nonneg hC.le hpl) (by positivity))
      _ = _ := by ring
  have htail : Real.exp (-(2 : ℝ) ^ J) * (μ univ).toReal ≤
      (μ univ).toReal * Real.exp (-(ε / 2) * N) := by
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) ENNReal.toReal_nonneg
    linarith
  calc ∫ x, Real.exp (-N * f x) ∂μ
      ≤ sublevelMass μ f (1 / N) +
        ∑ j ∈ Finset.range J, Real.exp (-(2 : ℝ) ^ j) * sublevelMass μ f (2 ^ (j + 1) / N) +
        Real.exp (-(2 : ℝ) ^ J) * (μ univ).toReal := integral_exp_le_dyadic hf hf0 hNpos J
    _ ≤ C * powerLogRate lam q N +
        C * powerLogRate lam q N * ((2 : ℝ) ^ (⌈lam⌉₊ + 1) * ((⌈lam⌉₊ + 1).factorial : ℝ)) +
        (μ univ).toReal * Real.exp (-(ε / 2) * N) := add_le_add (add_le_add hfirst hsum) htail
    _ = _ := by ring

/-- The exponential tail is eventually below the power–log rate. -/
theorem eventually_exp_tail_le (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (A : ℝ) (q : ℕ) :
    ∀ᶠ N : ℝ in atTop, A * Real.exp (-(ε / 2) * N) ≤ powerLogRate lam q N := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (ε / 2) (by positivity)
  have hA : 0 < |A| + 1 := by positivity
  have hev := (tendsto_order.1 ht).2 _ (inv_pos.2 hA)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1)] with N hN hNe
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hNpos : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hNe
  have hq : 1 ≤ Real.log N ^ q := one_le_pow₀ hlog
  have hrp : 0 < N ^ (-lam) := Real.rpow_pos_of_pos hNpos _
  have hsplit : A * Real.exp (-(ε / 2) * N) =
      N ^ (-lam) * (A * (N ^ lam * Real.exp (-(ε / 2) * N))) := by
    rw [Real.rpow_neg hNpos.le]
    field_simp
  rw [hsplit]
  unfold powerLogRate
  refine mul_le_mul_of_nonneg_left ?_ hrp.le
  have hx : 0 ≤ N ^ lam * Real.exp (-(ε / 2) * N) := by positivity
  calc A * (N ^ lam * Real.exp (-(ε / 2) * N)) ≤ |A| * (N ^ lam * Real.exp (-(ε / 2) * N)) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) hx
    _ ≤ (|A| + 1) * (|A| + 1)⁻¹ := mul_le_mul (by linarith) hN.le hx (by positivity)
    _ = 1 := mul_inv_cancel₀ hA.ne'
    _ ≤ Real.log N ^ q := hq

end Bounds

/-! ### The main theorems -/

section Main

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} {lam : ℝ}
  {q : ℕ}

/-- **Two-sided sublevel growth implies two-sided Laplace growth**, weighted: for a measurable
weight `0 ≤ w ≤ C` bounded below by `c > 0` on a sublevel set `{f ≤ δ}`,
`∫ w e^{−N f} dμ ≍ N^{−λ} (log N)^q`. -/
theorem SublevelTheta.laplaceTheta_weighted (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f)
    (h : SublevelTheta μ f lam q) {w : X → ℝ} (hwm : AEStronglyMeasurable w μ) {c C δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hw0 : 0 ≤ᵐ[μ] w) (hwC : ∀ᵐ x ∂μ, w x ≤ C)
    (hwc : ∀ᵐ x ∂μ, f x ≤ δ → c ≤ w x) :
    (fun N => ∫ x, w x * Real.exp (-N * f x) ∂μ) =Θ[atTop] powerLogRate lam q := by
  obtain ⟨c₀, C₀, ε, hc₀, hC₀, hε, hε1, hb⟩ := h.exists_bounds
  set C' := max C 0 with hC'
  have hC : 0 ≤ C' := le_max_right _ _
  have hwC' : ∀ᵐ x ∂μ, w x ≤ C' := by
    filter_upwards [hwC] with x hx; exact hx.trans (le_max_left _ _)
  constructor
  · -- upper bound
    refine IsBigO.of_bound
      (C' * (C₀ * (1 + (2 : ℝ) ^ (⌈lam⌉₊ + 1) * ((⌈lam⌉₊ + 1).factorial : ℝ)) + 1)) ?_
    filter_upwards [eventually_ge_atTop (2 / ε), eventually_ge_atTop 1,
      eventually_exp_tail_le lam hε (μ univ).toReal q] with N hN hN1 htail
    have hNε : 2 ≤ ε * N := by rwa [div_le_iff₀ hε, mul_comm] at hN
    have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
    have hint : Integrable (fun x => w x * Real.exp (-N * f x)) μ := by
      refine (integrable_const C').mono' (hwm.mul (hf.const_mul (-N)).exp.aestronglyMeasurable) ?_
      filter_upwards [hf0, hw0, hwC'] with x hx h0 hCx
      have hx' : 0 ≤ f x := hx
      have h0' : 0 ≤ w x := h0
      rw [Real.norm_of_nonneg (mul_nonneg h0' (Real.exp_pos _).le)]
      exact (mul_le_of_le_one_right h0' (Real.exp_le_one_iff.2 (by nlinarith))).trans hCx
    have hup := integral_exp_le_of_sublevel_bound hf hf0 hC₀ hε hε1
      (fun t ht htε => (hb t ht htε).2) hNε
    have hle : ∫ x, w x * Real.exp (-N * f x) ∂μ ≤ C' * ∫ x, Real.exp (-N * f x) ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono_ae hint ((integrable_exp_neg_mul hf hf0 hNpos.le).const_mul C') ?_
      filter_upwards [hwC'] with x hCx
      exact mul_le_mul_of_nonneg_right hCx (Real.exp_pos _).le
    have hnn : 0 ≤ ∫ x, w x * Real.exp (-N * f x) ∂μ :=
      integral_nonneg_of_ae
        (by filter_upwards [hw0] with x h0; exact mul_nonneg h0 (Real.exp_pos _).le)
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (powerLogRate_nonneg hN1)]
    calc ∫ x, w x * Real.exp (-N * f x) ∂μ ≤ C' * ∫ x, Real.exp (-N * f x) ∂μ := hle
      _ ≤ C' * (C₀ * (1 + (2 : ℝ) ^ (⌈lam⌉₊ + 1) * ((⌈lam⌉₊ + 1).factorial : ℝ)) *
            powerLogRate lam q N + powerLogRate lam q N) :=
          mul_le_mul_of_nonneg_left (hup.trans (by linarith)) hC
      _ = _ := by ring
  · -- lower bound
    refine IsBigO.of_bound (c * Real.exp (-1) * c₀)⁻¹ ?_
    filter_upwards [eventually_ge_atTop (1 / ε), eventually_ge_atTop (1 / δ), eventually_ge_atTop 1]
      with N hNε hNδ hN1
    have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
    have hinvε : N⁻¹ ≤ ε := by
      rw [inv_eq_one_div, div_le_iff₀ hNpos]; rwa [div_le_iff₀ hε, mul_comm] at hNε
    have hinvδ : N⁻¹ ≤ δ := by
      rw [inv_eq_one_div, div_le_iff₀ hNpos]; rwa [div_le_iff₀ hδ, mul_comm] at hNδ
    have hlow := le_integral_exp_neg_mul hf hf0 hwm hw0 hwC hNpos
      (by filter_upwards [hwc] with x hx hfx; exact hx (hfx.trans hinvδ))
    have hmass := (hb N⁻¹ (inv_pos.2 hNpos) hinvε).1
    rw [sublevelScale_inv hNpos] at hmass
    have hnn : 0 ≤ ∫ x, w x * Real.exp (-N * f x) ∂μ :=
      integral_nonneg_of_ae
        (by filter_upwards [hw0] with x h0; exact mul_nonneg h0 (Real.exp_pos _).le)
    have hpos : 0 < c * Real.exp (-1) * c₀ := by positivity
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (powerLogRate_nonneg hN1), ← div_eq_inv_mul,
      le_div_iff₀ hpos]
    calc powerLogRate lam q N * (c * Real.exp (-1) * c₀)
        = c * Real.exp (-1) * (c₀ * powerLogRate lam q N) := by ring
      _ ≤ c * Real.exp (-1) * sublevelMass μ f N⁻¹ :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := hlow

/-- **Two-sided sublevel growth implies two-sided Laplace growth**: `μ{f ≤ t} ≍ t^λ (−log t)^q` as
`t → 0⁺` gives `∫ e^{−N f} dμ ≍ N^{−λ} (log N)^q` as `N → ∞`. -/
theorem SublevelTheta.laplaceTheta (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f)
    (h : SublevelTheta μ f lam q) : LaplaceTheta μ f lam q := by
  unfold LaplaceTheta
  have := h.laplaceTheta_weighted hf hf0 (w := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (c := 1) (C := 1) (δ := 1) one_pos one_pos (Eventually.of_forall fun _ => zero_le_one)
    (Eventually.of_forall fun _ => le_rfl) (Eventually.of_forall fun _ _ => le_rfl)
  simpa only [one_mul] using this

end Main

/-! ### The population integral of a localisation datum -/

namespace LocalisationData

variable {U : Type*} [MeasurableSpace U] (D : LocalisationData U) [IsFiniteMeasure D.μ]

/-- **The exponent pair of the population integral**: if the sublevel mass of the phase grows
two-sidedly as `t^λ (−log t)^q` and the observable is bounded above and bounded below by a positive
constant on a sublevel set, then `Z(N) ≍ N^{−λ} (log N)^q`. -/
theorem Z_isTheta {lam : ℝ} {q : ℕ} (h : SublevelTheta D.μ D.phase lam q)
    {c C δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hobs0 : 0 ≤ᵐ[D.μ] D.obs)
    (hobsC : ∀ᵐ z ∂D.μ, D.obs z ≤ C) (hobsc : ∀ᵐ z ∂D.μ, D.phase z ≤ δ → c ≤ D.obs z) :
    D.Z =Θ[atTop] powerLogRate lam q :=
  h.laplaceTheta_weighted D.phase_measurable D.phase_nonneg
    D.obs_integrable.aestronglyMeasurable hc hδ hobs0 hobsC hobsc

end LocalisationData

end Grammar
