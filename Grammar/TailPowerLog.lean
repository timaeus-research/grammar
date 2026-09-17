/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Tail integrals of `t^{−a−1} (log t)^q`

`∫_N^∞ t^{−a−1} (log t)^q dt = N^{−a} Σ_{i ≤ q} (q!/(i! a^{q−i+1})) (log N)^i` for `a > 0`, `N ≥ 1`
(`integral_rpow_neg_mul_log_pow_Ioi`), by the integration-by-parts recursion
`I_{q+1} = N^{−a}(log N)^{q+1}/a + ((q+1)/a) I_q`.  The coefficients `tailLogCoeff a q i` satisfy
the inversion identity `a·tailLogCoeff q i − (i+1)·tailLogCoeff q (i+1) = δ_{qi}`
(`tailLogCoeff_inv`), which is what turns "integrate a cutoff expansion" into the exact shift
recursion of the coefficients.
Also the crude tail bound `∫_N^∞ t^{−L}(1+log t)^D dt ≤ (1+2D)^D N^{−L+3/2}/(L−3/2)`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset

namespace Grammar

/-- `log t ^ q ≤ ε^{−q} t^{qε}` for `t ≥ 1`, `ε > 0`. -/
theorem log_pow_le_rpow {t ε : ℝ} (ht : 1 ≤ t) (hε : 0 < ε) (q : ℕ) :
    Real.log t ^ q ≤ (1 / ε) ^ q * t ^ ((q : ℝ) * ε) := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  calc Real.log t ^ q ≤ (t ^ ε / ε) ^ q := pow_le_pow_left₀ h0 h1 q
    _ = (1 / ε) ^ q * t ^ ((q : ℝ) * ε) := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm (q : ℝ) ε,
          div_eq_mul_one_div, mul_comm]
        ring_nf

/-- The integrand `t^{−a−1} (log t)^q` is integrable on `(N, ∞)` for `a > 0`, `N ≥ 1`. -/
theorem integrableOn_rpow_neg_mul_log_pow_Ioi {a : ℝ} (ha : 0 < a) (q : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun t : ℝ => t ^ (-a - 1) * Real.log t ^ q) (Ioi N) := by
  set ε : ℝ := a / (2 * (q + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hexp : -a - 1 + q * ε < -1 := by
    have : (q : ℝ) * ε ≤ a / 2 := by
      rw [hε, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith [ha]
    linarith
  have hmaj : IntegrableOn (fun t : ℝ => (1 / ε) ^ q * t ^ (-a - 1 + q * ε)) (Ioi N) :=
    (integrableOn_Ioi_rpow_of_lt hexp (by linarith)).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (fun t ht => ?_) ?_
    · exact (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [mem_Ioi.1 ht]))).continuousWithinAt
    · exact (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ioi.1 ht]).pow q
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 ≤ t := by linarith [mem_Ioi.1 ht]
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
      (pow_nonneg (Real.log_nonneg ht1) q))]
    calc t ^ (-a - 1) * Real.log t ^ q ≤ t ^ (-a - 1) * ((1 / ε) ^ q * t ^ ((q : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_left (log_pow_le_rpow ht1 hεpos q) (Real.rpow_nonneg ht0.le _)
      _ = (1 / ε) ^ q * t ^ (-a - 1 + q * ε) := by
          rw [Real.rpow_add ht0]
          ring

/-- `t^{−a} (log t)^q → 0` as `t → ∞` for `a > 0`. -/
theorem tendsto_rpow_neg_mul_log_pow_atTop {a : ℝ} (ha : 0 < a) (q : ℕ) :
    Tendsto (fun t : ℝ => t ^ (-a) * Real.log t ^ q) atTop (𝓝 0) := by
  set ε : ℝ := a / (2 * (q + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hexp : 0 < a - q * ε := by
    have : (q : ℝ) * ε ≤ a / 2 := by
      rw [hε, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith [ha]
    linarith
  have hlim : Tendsto (fun t : ℝ => (1 / ε) ^ q * t ^ (-(a - q * ε))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hexp).const_mul ((1 / ε) ^ q)
    simpa using this
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 1] with t ht
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (pow_nonneg (Real.log_nonneg ht) q)
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    calc t ^ (-a) * Real.log t ^ q ≤ t ^ (-a) * ((1 / ε) ^ q * t ^ ((q : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_left (log_pow_le_rpow ht hεpos q) (Real.rpow_nonneg ht0.le _)
      _ = (1 / ε) ^ q * t ^ (-(a - q * ε)) := by
          rw [show -(a - q * ε) = -a + q * ε by ring, Real.rpow_add ht0]
          ring

/-- The derivative of `t^{−a} (log t)^{q+1}`. -/
theorem hasDerivAt_rpow_neg_mul_log_pow (a : ℝ) (q : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ (-a) * Real.log t ^ (q + 1))
      (-a * (t ^ (-a - 1) * Real.log t ^ (q + 1)) + (q + 1) * (t ^ (-a - 1) * Real.log t ^ q))
      t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-a) * Real.log t ^ (q + 1))
      (-a * t ^ (-a - 1) * Real.log t ^ (q + 1) +
        t ^ (-a) * (((q + 1 : ℕ) : ℝ) * Real.log t ^ (q + 1 - 1) * t⁻¹)) t :=
    (Real.hasDerivAt_rpow_const (p := -a) (Or.inl ht.ne')).mul
      ((Real.hasDerivAt_log ht.ne').pow (q + 1))
  refine h1.congr_deriv ?_
  have hr : t ^ (-a - 1) = t ^ (-a) * t⁻¹ := by
    rw [Real.rpow_sub_one ht.ne', div_eq_mul_inv]
  rw [hr, Nat.add_sub_cancel]
  push_cast
  ring

/-- The integration-by-parts recursion `I_{q+1} = N^{−a}(log N)^{q+1}/a + ((q+1)/a) I_q`. -/
theorem integral_rpow_neg_mul_log_pow_Ioi_succ {a : ℝ} (ha : 0 < a) (q : ℕ) {N : ℝ}
    (hN : 1 ≤ N) :
    ∫ t in Ioi N, t ^ (-a - 1) * Real.log t ^ (q + 1) =
      N ^ (-a) * Real.log N ^ (q + 1) / a +
        ((q + 1) / a) * ∫ t in Ioi N, t ^ (-a - 1) * Real.log t ^ q := by
  have hN0 : 0 < N := by linarith
  have hderiv : ∀ t ∈ Ioi N, HasDerivAt (fun t : ℝ => -(1 / a) * (t ^ (-a) * Real.log t ^ (q + 1)))
      (t ^ (-a - 1) * Real.log t ^ (q + 1) - ((q + 1) / a) * (t ^ (-a - 1) * Real.log t ^ q)) t :=
    fun t ht => by
    have ht0 : 0 < t := by linarith [mem_Ioi.1 ht]
    refine ((hasDerivAt_rpow_neg_mul_log_pow a q ht0).const_mul (-(1 / a))).congr_deriv ?_
    field_simp
    ring
  have hint1 := integrableOn_rpow_neg_mul_log_pow_Ioi ha (q + 1) hN
  have hint0 := integrableOn_rpow_neg_mul_log_pow_Ioi ha q hN
  have hint : IntegrableOn (fun t : ℝ => t ^ (-a - 1) * Real.log t ^ (q + 1) -
      ((q + 1) / a) * (t ^ (-a - 1) * Real.log t ^ q)) (Ioi N) :=
    hint1.sub (hint0.const_mul _)
  have hlim : Tendsto (fun t : ℝ => -(1 / a) * (t ^ (-a) * Real.log t ^ (q + 1))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_mul_log_pow_atTop ha (q + 1)).const_mul (-(1 / a))
    rwa [mul_zero] at this
  have hcont : ContinuousWithinAt (fun t : ℝ => -(1 / a) * (t ^ (-a) * Real.log t ^ (q + 1)))
      (Ici N) N :=
    ((hasDerivAt_rpow_neg_mul_log_pow a q hN0).const_mul (-(1 / a))).continuousAt.continuousWithinAt
  have hfund := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_sub hint1 (hint0.const_mul _), integral_const_mul] at hfund
  linear_combination hfund

/-- The coefficient of `(log N)^i` in `N^a ∫_N^∞ t^{−a−1} (log t)^q dt`: `q!/(i! a^{q−i+1})`. -/
noncomputable def tailLogCoeff (a : ℝ) (q i : ℕ) : ℝ :=
  if i ≤ q then (q.factorial : ℝ) / (i.factorial * a ^ (q - i + 1)) else 0

theorem tailLogCoeff_succ_of_le {a : ℝ} (ha : 0 < a) {q i : ℕ} (hi : i ≤ q) :
    tailLogCoeff a (q + 1) i = ((q + 1) / a) * tailLogCoeff a q i := by
  unfold tailLogCoeff
  rw [if_pos (hi.trans (Nat.le_succ q)), if_pos hi, Nat.factorial_succ,
    show q + 1 - i + 1 = (q - i + 1) + 1 by omega, pow_succ]
  push_cast
  field_simp

theorem tailLogCoeff_self {a : ℝ} (ha : 0 < a) (q : ℕ) : tailLogCoeff a q q = 1 / a := by
  unfold tailLogCoeff
  rw [if_pos le_rfl, Nat.sub_self, zero_add, pow_one, div_eq_div_iff (by positivity) ha.ne']
  ring

/-- ★ **The tail integral in closed form**:
`∫_N^∞ t^{−a−1}(log t)^q dt = N^{−a} Σ_{i≤q} tailLogCoeff a q i (log N)^i`. -/
theorem integral_rpow_neg_mul_log_pow_Ioi {a : ℝ} (ha : 0 < a) (q : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in Ioi N, t ^ (-a - 1) * Real.log t ^ q =
      N ^ (-a) * ∑ i ∈ range (q + 1), tailLogCoeff a q i * Real.log N ^ i := by
  have hN0 : 0 < N := by linarith
  induction q with
  | zero =>
    rw [zero_add, range_one, sum_singleton, tailLogCoeff_self ha]
    simp only [pow_zero, mul_one]
    rw [integral_Ioi_rpow_of_lt (by linarith) hN0, show -a - 1 + 1 = -a by ring]
    field_simp
  | succ q ih =>
    rw [integral_rpow_neg_mul_log_pow_Ioi_succ ha q hN, ih, sum_range_succ _ (q + 1),
      tailLogCoeff_self ha]
    have hs : ∑ i ∈ range (q + 1), tailLogCoeff a (q + 1) i * Real.log N ^ i =
        ∑ i ∈ range (q + 1), ((q + 1) / a) * (tailLogCoeff a q i * Real.log N ^ i) :=
      sum_congr rfl fun i hi => by
        rw [tailLogCoeff_succ_of_le ha (Nat.lt_succ_iff.1 (mem_range.1 hi))]
        ring
    rw [hs, ← mul_sum]
    ring

/-- ★ **The inversion identity**:
`a·tailLogCoeff a q i − (i+1)·tailLogCoeff a q (i+1) = δ_{q i}`. -/
theorem tailLogCoeff_inv {a : ℝ} (ha : 0 < a) (q i : ℕ) :
    a * tailLogCoeff a q i - (i + 1) * tailLogCoeff a q (i + 1) = if i = q then 1 else 0 := by
  unfold tailLogCoeff
  rcases lt_trichotomy i q with hlt | heq | hgt
  · rw [if_pos hlt.le, if_pos (Nat.lt_iff_add_one_le.1 hlt), if_neg hlt.ne, Nat.factorial_succ,
      show q - i + 1 = (q - (i + 1) + 1) + 1 by omega, pow_succ]
    push_cast
    field_simp
    ring
  · subst heq
    rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, Nat.sub_self, zero_add, pow_one]
    field_simp
    ring
  · rw [if_neg (not_le.2 hgt), if_neg (by omega), if_neg hgt.ne']
    ring

/-! ### The crude remainder tail -/

/-- `(1 + log t)^D ≤ (1 + 2D)^D t^{1/2}` for `t ≥ 1`. -/
theorem one_add_log_pow_le {t : ℝ} (ht : 1 ≤ t) (D : ℕ) :
    (1 + Real.log t) ^ D ≤ (1 + 2 * D) ^ D * t ^ (1 / 2 : ℝ) := by
  have ht0 : 0 < t := by linarith
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    rw [pow_zero, pow_zero, one_mul]
    exact Real.one_le_rpow ht (by norm_num)
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    set ε : ℝ := 1 / (2 * D) with hε
    have hεpos : 0 < ε := by positivity
    have h1 : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0.le hεpos
    have h2 : 1 ≤ t ^ ε := Real.one_le_rpow ht hεpos.le
    have h3 : 1 + Real.log t ≤ (1 + 2 * D) * t ^ ε := by
      have : t ^ ε / ε = 2 * D * t ^ ε := by
        rw [hε]
        field_simp
      nlinarith
    have h4 : 0 ≤ 1 + Real.log t := by linarith [Real.log_nonneg ht]
    calc (1 + Real.log t) ^ D ≤ ((1 + 2 * D) * t ^ ε) ^ D := pow_le_pow_left₀ h4 h3 D
      _ = (1 + 2 * D) ^ D * t ^ (1 / 2 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (t ^ ε), ← Real.rpow_mul ht0.le]
          congr 2
          rw [hε]
          field_simp

/-- The remainder integrand `t^{−L}(1+log t)^D` is integrable on `(N, ∞)` for `L > 3/2`. -/
theorem integrableOn_rpow_neg_mul_one_add_log_pow_Ioi {L : ℝ} (hL : 3 / 2 < L) (D : ℕ) {N : ℝ}
    (hN : 1 ≤ N) :
    IntegrableOn (fun t : ℝ => t ^ (-L) * (1 + Real.log t) ^ D) (Ioi N) := by
  have hmaj : IntegrableOn (fun t : ℝ => (1 + 2 * D) ^ D * t ^ (-L + 1 / 2)) (Ioi N) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (fun t ht => ?_) ?_
    · exact (Real.continuousAt_rpow_const _ _
        (Or.inl (by linarith [mem_Ioi.1 ht]))).continuousWithinAt
    · exact (continuousOn_const.add (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]; linarith [mem_Ioi.1 ht])).pow D
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 ≤ t := by linarith [mem_Ioi.1 ht]
    have ht0 : 0 < t := by linarith
    have h4 : 0 ≤ 1 + Real.log t := by linarith [Real.log_nonneg ht1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (pow_nonneg h4 D))]
    calc t ^ (-L) * (1 + Real.log t) ^ D ≤ t ^ (-L) * ((1 + 2 * D) ^ D * t ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (one_add_log_pow_le ht1 D) (Real.rpow_nonneg ht0.le _)
      _ = (1 + 2 * D) ^ D * t ^ (-L + 1 / 2) := by
          rw [Real.rpow_add ht0]
          ring

/-- ★ **The crude remainder tail**: `∫_N^∞ t^{−L}(1+log t)^D dt ≤ (1+2D)^D N^{−L+3/2}/(L−3/2)`. -/
theorem integral_rpow_neg_mul_one_add_log_pow_Ioi_le {L : ℝ} (hL : 3 / 2 < L) (D : ℕ) {N : ℝ}
    (hN : 1 ≤ N) :
    ∫ t in Ioi N, t ^ (-L) * (1 + Real.log t) ^ D ≤
      (1 + 2 * D) ^ D * N ^ (-L + 3 / 2) / (L - 3 / 2) := by
  have hN0 : 0 < N := by linarith
  have hmaj : IntegrableOn (fun t : ℝ => (1 + 2 * D) ^ D * t ^ (-L + 1 / 2)) (Ioi N) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
  calc ∫ t in Ioi N, t ^ (-L) * (1 + Real.log t) ^ D
      ≤ ∫ t in Ioi N, (1 + 2 * D) ^ D * t ^ (-L + 1 / 2) := by
        refine setIntegral_mono_on (integrableOn_rpow_neg_mul_one_add_log_pow_Ioi hL D hN) hmaj
          measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 ≤ t := by linarith [mem_Ioi.1 ht]
        have ht0 : 0 < t := by linarith
        calc t ^ (-L) * (1 + Real.log t) ^ D ≤ t ^ (-L) * ((1 + 2 * D) ^ D * t ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left (one_add_log_pow_le ht1 D) (Real.rpow_nonneg ht0.le _)
          _ = (1 + 2 * D) ^ D * t ^ (-L + 1 / 2) := by
              rw [Real.rpow_add ht0]
              ring
    _ = (1 + 2 * D) ^ D * N ^ (-L + 3 / 2) / (L - 3 / 2) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0,
          show -L + 1 / 2 + 1 = -L + 3 / 2 by ring, neg_div, div_eq_mul_inv,
          show (-L + 3 / 2)⁻¹ = -(L - 3 / 2)⁻¹ by
            rw [show -L + 3 / 2 = -(L - 3 / 2) by ring, ← neg_inv]]
        ring

end Grammar
