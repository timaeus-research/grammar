/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialFamilyExpansion

/-!
# The family `K = x²(x^{2k−2} + y²)/2`: the log-free remainder

DCXXV's remainder `O(N^{−1/2−1/k} log N)` carries a logarithm inherited from the generic
amplitude engine, whose near-zero defect bound `1 − a(u) ≤ A u²` feeds the kernel
`2ε u/(u² + ε)` and produces `ε log(1/ε)`.  For the monomial amplitude `e^{−u^{2k}/2}` with
`k ≥ 2` the defect is quartic, `1 − a(u) ≤ u⁴/2`, and the inner remainder is `O(ε)` outright
(`amp_rem_inner_quartic_le`, `ampJ_two_term_quartic`).  The scaled amplitude `a_m` of the family is
compared with the fixed monomial amplitude at the level of the WHOLE integrals,
`|J_{a_m}(ε) − J_{a_∞}(ε)| ≤ 2/m²` (`ampJ_famAmp_sub_monoAmp_le`, from `1 − e^{−u²/2m²} ≤ u²/2m²`,
`√(u² + ε) ≥ u` and `e^{−u^{2k}/2} ≤ e^{1/2} e^{−u²/2}`), rather than through the renormalised
constants.  Hence (★★★ `monomialFamily_logFree_bound`)

  `|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤ 7√(2π)/(√N N^{1/k})`

for `N ≥ 1`, `k ≥ 2`, and `monomialFamily_logFree` is the `O(N^{−1/2−1/k})` form
(examples_slop §4; Astra round-10 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

variable {a : ℝ → ℝ} {A : ℝ}

/-! ### The quartic-defect inner remainder -/

/-- `|∫₀¹ (a(u) − 1)(2/√(u² + ε) − 2/u) du| ≤ B ε` when `1 − a(u) ≤ B u⁴` on `(0,1]`. -/
theorem amp_rem_inner_quartic_le (h : AmpData a A) {B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ u ∈ Ioc (0 : ℝ) 1, 1 - a u ≤ B * u ^ 4) {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤ B * ε := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * B * ε * u) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u => (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
      integral_id]
    ring_nf
    exact le_rfl
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hu' : u ≠ 0 := hu0.ne'
    obtain ⟨g1, g2⟩ := gap_bounds hε hu0
    have hn := hnear u hu
    have hle := h.le_one u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc -(a u - 1) * -(2 / Real.sqrt (u ^ 2 + ε) - 2 / u)
        ≤ (B * u ^ 4) * (2 * ε / (u * (u ^ 2 + ε))) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = 2 * B * ε * (u ^ 3 / (u ^ 2 + ε)) := by field_simp
      _ ≤ 2 * B * ε * u := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg u]

/-- The log-free two-term expansion for an amplitude with a quartic defect at zero:
`|J_a(ε) − (log(4/ε) + R_a)| ≤ (4 + B) ε` for `0 < ε ≤ 1`. -/
theorem ampJ_two_term_quartic (h : AmpData a A) {B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ u ∈ Ioc (0 : ℝ) 1, 1 - a u ≤ B * u ^ 4) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ a ε - (Real.log (4 / ε) + ampRenorm a)| ≤ (4 + B) * ε := by
  have hA1 := integrableOn_ampJ_inner h hε
  have hA2 := integrableOn_ampJ_outer h hε
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun u : ℝ => (a u - 1) * (2 / u)) (Ioc 0 1) :=
    (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun u : ℝ => a u * (2 / u)) (Ioi 1) :=
    (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : ampJ a ε = (∫ u in Ioc (0 : ℝ) 1, 2 * a u / Real.sqrt (u ^ 2 + ε)) +
      ∫ u in Ioi (1 : ℝ), 2 * a u / Real.sqrt (u ^ 2 + ε) := by
    unfold ampJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  have hR1 : ∫ u in Ioc (0 : ℝ) 1, 2 * a u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε)) +
        (∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / u)) +
        ∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) := by
    have e : ∀ u ∈ Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) =
        2 * a u / Real.sqrt (u ^ 2 + ε) - 2 / Real.sqrt (u ^ 2 + ε) - (a u - 1) * (2 / u) :=
      fun u _ => by ring
    have hAp : IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε) -
        2 / Real.sqrt (u ^ 2 + ε)) (Ioc 0 1) := hA1.sub hp1
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_sub hAp hq1, integral_sub hA1 hp1]
    ring
  have hR2 : ∫ u in Ioi (1 : ℝ), 2 * a u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioi (1 : ℝ), a u * (2 / u)) +
        ∫ u in Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) := by
    have e : ∀ u ∈ Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u) =
        2 * a u / Real.sqrt (u ^ 2 + ε) - a u * (2 / u) := fun u _ => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hA2 hq2]
    ring
  have hb1 := elem_bounds hε hε1
  have hb2 := amp_rem_inner_quartic_le h hB hnear hε
  have hb3 := amp_rem_outer_le h hε
  have hsplit := ampRenorm_split h
  rw [hJ, hR1, hR2, hE, hsplit]
  rw [abs_le] at hb2 hb3 ⊢
  constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2]

/-! ### The monomial amplitude: quartic defect and a Gaussian majorant -/

/-- `1 − e^{−u^{2k}/2} ≤ u⁴/2` on `(0,1]` for `k ≥ 2`. -/
theorem monoAmp_near_quartic {k : ℕ} (hk : 2 ≤ k) :
    ∀ u ∈ Ioc (0 : ℝ) 1, 1 - monoAmp k u ≤ 1 / 2 * u ^ 4 := by
  intro u hu
  unfold monoAmp
  have hpow : u ^ (2 * k) ≤ u ^ 4 := pow_le_pow_of_le_one hu.1.le hu.2 (by omega)
  have := Real.add_one_le_exp (-u ^ (2 * k) / 2)
  linarith

/-- `e^{−u^{2k}/2} ≤ e^{1/2} e^{−u²/2}` for `u ≥ 0`, `k ≥ 1` (`u² ≤ 1 + u^{2k}`). -/
theorem monoAmp_le_gauss {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    monoAmp k u ≤ Real.exp (1 / 2) * Real.exp (-u ^ 2 / 2) := by
  unfold monoAmp
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : u ^ 2 ≤ 1 + u ^ (2 * k) := by
    rcases le_or_gt u 1 with h | h
    · have h1 : u ^ 2 ≤ 1 := pow_le_one₀ hu h
      have h0 : 0 ≤ u ^ (2 * k) := pow_nonneg hu _
      linarith
    · have : u ^ 2 ≤ u ^ (2 * k) := pow_le_pow_right₀ h.le (by omega)
      linarith
  linarith

/-- `∫₀^∞ u e^{−u²/2} du = 1`. -/
theorem integral_mul_exp_neg_half_sq_Ioi :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-u ^ 2 / 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) =
      x * Real.exp (-x ^ 2 / 2) := by
    intro x _
    rw [Real.rpow_one, Real.rpow_two]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e] at h
  rw [h, show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, Real.rpow_neg (by norm_num), Real.rpow_one,
    show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one]
  norm_num

/-- `u e^{−u²/2}` is integrable on `(0,∞)`. -/
theorem integrableOn_mul_exp_neg_half_sq_Ioi :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only
  rw [Real.rpow_one, Real.rpow_two]
  congr 2
  ring

/-- `e^{1/2} ≤ 2`. -/
theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos (1 / 2)
  nlinarith

/-! ### Comparison of the whole integrals -/

/-- `|J_{a_m}(ε) − J_{a_∞}(ε)| ≤ 2/m²` for `m ≥ 1`, `k ≥ 1`, `ε > 0`: the scaled amplitude
`a_m = a_∞ · e^{−u²/2m²}` differs from the monomial amplitude by at most `a_∞(u) u²/(2m²)`, and
`2 a_∞(u) (u²/2m²)/√(u² + ε) ≤ e^{1/2} u e^{−u²/2}/m²`. -/
theorem ampJ_famAmp_sub_monoAmp_le {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 1 ≤ m) {ε : ℝ}
    (hε : 0 < ε) :
    |ampJ (famAmp k m) ε - ampJ (monoAmp k) ε| ≤ 2 / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hd1 := famAmp_ampData hk hm
  have hd2 := monoAmp_ampData (by omega : 0 < k)
  have hI1 : IntegrableOn (fun u : ℝ => 2 * famAmp k m u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact (integrableOn_ampJ_inner hd1 hε).union (integrableOn_ampJ_outer hd1 hε)
  have hI2 : IntegrableOn (fun u : ℝ => 2 * monoAmp k u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact (integrableOn_ampJ_inner hd2 hε).union (integrableOn_ampJ_outer hd2 hε)
  unfold ampJ
  rw [← integral_sub hI1 hI2]
  have hmaj : IntegrableOn
      (fun u : ℝ => Real.exp (1 / 2) / m ^ 2 * (u * Real.exp (-u ^ 2 / 2))) (Ioi 0) :=
    integrableOn_mul_exp_neg_half_sq_Ioi.const_mul _
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun u => 2 * famAmp k m u / Real.sqrt (u ^ 2 + ε) -
      2 * monoAmp k u / Real.sqrt (u ^ 2 + ε)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, integral_mul_exp_neg_half_sq_Ioi, mul_one]
    exact div_le_div_of_nonneg_right exp_half_le_two hm2.le
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu
    have hs : 0 < Real.sqrt (u ^ 2 + ε) := Real.sqrt_pos.2 (by positivity)
    have hus : u ≤ Real.sqrt (u ^ 2 + ε) := by
      calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0.le).symm
        _ ≤ Real.sqrt (u ^ 2 + ε) := Real.sqrt_le_sqrt (by linarith)
    have hfam : famAmp k m u = monoAmp k u * Real.exp (-u ^ 2 / (2 * m ^ 2)) := rfl
    have hmono0 := hd2.nonneg u
    have hx : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
    have hexp : 1 - Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ u ^ 2 / (2 * m ^ 2) := by
      have := Real.add_one_le_exp (-u ^ 2 / (2 * m ^ 2))
      have hnd : -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) := neg_div _ _
      linarith
    have hexp0 : 0 ≤ 1 - Real.exp (-u ^ 2 / (2 * m ^ 2)) := by
      have : Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ u ^ 2 / (2 * m ^ 2) := hx
        rw [neg_div]; linarith)
      linarith
    have hval : 2 * famAmp k m u / Real.sqrt (u ^ 2 + ε) -
        2 * monoAmp k u / Real.sqrt (u ^ 2 + ε) =
        -(2 * monoAmp k u * (1 - Real.exp (-u ^ 2 / (2 * m ^ 2))) / Real.sqrt (u ^ 2 + ε)) := by
      rw [hfam]; ring
    rw [Real.norm_eq_abs, hval, abs_neg, abs_of_nonneg (by positivity)]
    have hg := monoAmp_le_gauss hk hu0.le
    calc 2 * monoAmp k u * (1 - Real.exp (-u ^ 2 / (2 * m ^ 2))) / Real.sqrt (u ^ 2 + ε)
        ≤ 2 * monoAmp k u * (u ^ 2 / (2 * m ^ 2)) / u := by
          calc 2 * monoAmp k u * (1 - Real.exp (-u ^ 2 / (2 * m ^ 2))) / Real.sqrt (u ^ 2 + ε)
              ≤ 2 * monoAmp k u * (u ^ 2 / (2 * m ^ 2)) / Real.sqrt (u ^ 2 + ε) := by
                gcongr
            _ ≤ 2 * monoAmp k u * (u ^ 2 / (2 * m ^ 2)) / u :=
                div_le_div_of_nonneg_left (by positivity) hu0 hus
      _ = monoAmp k u * u / m ^ 2 := by field_simp
      _ ≤ Real.exp (1 / 2) * Real.exp (-u ^ 2 / 2) * u / m ^ 2 := by gcongr
      _ = Real.exp (1 / 2) / m ^ 2 * (u * Real.exp (-u ^ 2 / 2)) := by ring

/-! ### The log-free expansion -/

/-- ★★ `|J_{a_∞}(ε) − (log(4/ε) + (log 2 − γ)/k)| ≤ 5ε` for `0 < ε ≤ 1`, `k ≥ 2`. -/
theorem ampJ_monoAmp_two_term {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (monoAmp k) ε -
      (Real.log (4 / ε) + (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤ 5 * ε := by
  have h := ampJ_two_term_quartic (monoAmp_ampData (by omega : 0 < k))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (monoAmp_near_quartic hk) hε hε1
  rw [ampRenorm_monoAmp (by omega)] at h
  calc _ ≤ (4 + 1 / 2) * ε := h
    _ ≤ 5 * ε := by linarith

/-- ★★ `|J_{a_m}(m^{2−2k}) − (2 log 2 + (2k−2) log m + (log 2 − γ)/k)| ≤ 7/m²` for `m ≥ 1`,
`k ≥ 2`. -/
theorem ampJ_famAmp_logFree {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) -
      (2 * Real.log 2 + (2 * k - 2) * Real.log m +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤ 7 / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hpow : 0 < m ^ (2 * k - 2) := by positivity
  have hpow1 : 1 ≤ m ^ (2 * k - 2) := one_le_pow₀ hm
  have hpow2 : m ^ 2 ≤ m ^ (2 * k - 2) := pow_le_pow_right₀ hm (by omega)
  have hε : 0 < 1 / m ^ (2 * k - 2) := by positivity
  have hε1 : 1 / m ^ (2 * k - 2) ≤ 1 := by rw [div_le_one hpow]; exact hpow1
  have hεm : 1 / m ^ (2 * k - 2) ≤ 1 / m ^ 2 := by
    rw [div_le_div_iff₀ hpow hm2]; nlinarith
  have hcast : ((2 * k - 2 : ℕ) : ℝ) = 2 * k - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlog4 : Real.log (4 / (1 / m ^ (2 * k - 2))) =
      2 * Real.log 2 + (2 * k - 2) * Real.log m := by
    rw [show (4 : ℝ) / (1 / m ^ (2 * k - 2)) = 2 ^ 2 * m ^ (2 * k - 2) by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, hcast]
    push_cast
    ring
  have h1 := ampJ_monoAmp_two_term hk hε hε1
  have h2 := ampJ_famAmp_sub_monoAmp_le (by omega : 1 ≤ k) hm hε
  rw [hlog4] at h1
  set J := ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) with hJ
  set J₀ := ampJ (monoAmp k) (1 / m ^ (2 * k - 2)) with hJ₀
  set c := 2 * Real.log 2 + (2 * k - 2) * Real.log m +
    (Real.log 2 - Real.eulerMascheroniConstant) / k with hc
  set ε := 1 / m ^ (2 * k - 2) with hεdef
  clear_value J J₀ c ε
  calc |J - c| = |(J - J₀) + (J₀ - c)| := by ring_nf
    _ ≤ |J - J₀| + |J₀ - c| := abs_add_le _ _
    _ ≤ 2 / m ^ 2 + 5 * ε := add_le_add h2 h1
    _ ≤ 2 / m ^ 2 + 5 * (1 / m ^ 2) := by gcongr
    _ = 7 / m ^ 2 := by ring

/-- The `m`-form: for `m ≥ 1`, `k ≥ 2`,
`|Z_k(m^{2k}) − √(2π)/m^k · (2(k−1) log m + 2 log 2 + (log 2 − γ)/k)| ≤ √(2π)/m^k · 7/m²`. -/
theorem monomialFamily_logFree_m {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |monomialFamilyZ k (m ^ (2 * k)) - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) / m ^ k * (7 / m ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 0 < m := by linarith
  have h := ampJ_famAmp_logFree hk hm
  rw [monomialFamilyZ_eq_ampJ hk1 hm0]
  set J := ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) with hJdef
  clear_value J
  have key : Real.sqrt (2 * Real.pi) / m ^ k * J - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k) =
      Real.sqrt (2 * Real.pi) / m ^ k * (J - (2 * Real.log 2 + (2 * k - 2) * Real.log m +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)) := by ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- ★★★ **The log-free two-term expansion of the family**: for `N ≥ 1` and `k ≥ 2`,
`|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤ 7√(2π)/(√N · N^{1/k})`. -/
theorem monomialFamily_logFree_bound {k : ℕ} (hk : 2 ≤ k) {N : ℝ} (hN : 1 ≤ N) :
    |monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      7 * Real.sqrt (2 * Real.pi) / (Real.sqrt N * N ^ (1 / (k : ℝ))) := by
  have hN0 : 0 < N := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set m := N ^ (1 / (2 * (k : ℝ))) with hm
  have hm1 : 1 ≤ m := Real.one_le_rpow hN (by positivity)
  have hm0 : 0 < m := by linarith
  have hm2k : m ^ (2 * k) = N := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    push_cast
    rw [show 1 / (2 * (k : ℝ)) * (2 * k) = 1 by field_simp, Real.rpow_one]
  have hlogm : Real.log N = 2 * k * Real.log m := by
    rw [← hm2k, Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt N = m ^ k := by
    rw [← hm2k, show m ^ (2 * k) = (m ^ k) ^ 2 by rw [← pow_mul]; ring_nf,
      Real.sqrt_sq (by positivity)]
  have hNk : N ^ (1 / (k : ℝ)) = m ^ 2 := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    field_simp
  have h := monomialFamily_logFree_m hk hm1
  rw [hm2k] at h
  have e1 : 2 * (k - 1) * Real.log m = (k - 1) / k * Real.log N := by rw [hlogm]; field_simp
  rw [e1, ← hsqrt] at h
  rw [hNk]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- ★★★ `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2−1/k})`
for every `k ≥ 2`: the log-free remainder. -/
theorem monomialFamily_logFree {k : ℕ} (hk : 2 ≤ k) :
    (fun N : ℝ => monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k))
      =O[atTop] fun N => 1 / (Real.sqrt N * N ^ (1 / (k : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (7 * Real.sqrt (2 * Real.pi)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hpos : (0 : ℝ) ≤ 1 / (Real.sqrt N * N ^ (1 / (k : ℝ))) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  refine (monomialFamily_logFree_bound hk hN).trans (le_of_eq ?_)
  ring

end Grammar
