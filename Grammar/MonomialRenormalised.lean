/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpLaplaceExpansion

/-!
# The renormalised constant of the monomial amplitude `e^{−u^{2k}/2}`

For every `k ≥ 1`,

  `∫₀^∞ (e^{−u^{2k}/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/k`  (★★ `ampRenorm_monoAmp`),

by the substitution `v = u^k` (`integral_comp_rpow_Ioi_of_pos`) from the case `k = 1`, which is the
Gaussian renormalised constant of `Grammar.GaussianDepthTwoExpansion` rescaled by `u = √2 w`
(`integral_renormalised_sq_cut`: cutting the indicator at `b` instead of `1` shifts the constant by
`−2 log b`).  The split form without indicators is `monomial_renorm_constant`.  With the amplitude
data `monoAmp_ampData` this is the constant of the two-term expansion of every model
`K = x²(x^{2k−2} + y²)/2` with the Gaussian prior (`k = 2` is the blow-up model of
`Grammar.BlowUpLaplaceExpansion`; Astra round-8 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The monomial amplitude `e^{−u^{2k}/2}`. -/
noncomputable def monoAmp (k : ℕ) (u : ℝ) : ℝ := Real.exp (-u ^ (2 * k) / 2)

/-! ### The Gaussian constant with a shifted cut -/

/-- `∫₀^∞ (e^{−w²} − 1_{(0,b]}(w))·2/w dw = −γ − 2 log b` for `0 < b ≤ 1`. -/
theorem integral_renormalised_sq_cut {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∫ w in Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 b).indicator 1 w) * (2 / w) =
      -Real.eulerMascheroniConstant - 2 * Real.log b := by
  have e : ∀ w ∈ Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 b).indicator 1 w) * (2 / w) =
      (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w) +
        (Ioc b 1).indicator (fun w => 2 / w) w := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    by_cases h1 : w ≤ b
    · have hm1 : w ∈ Ioc (0 : ℝ) b := ⟨hw0, h1⟩
      have hm2 : w ∈ Ioc (0 : ℝ) 1 := ⟨hw0, by linarith⟩
      have hm3 : w ∉ Ioc b 1 := fun h => absurd h.1 (not_lt.2 h1)
      rw [indicator_of_mem hm1, indicator_of_mem hm2, indicator_of_notMem hm3, add_zero]
    · have h1' := not_le.1 h1
      have hm1 : w ∉ Ioc (0 : ℝ) b := fun h => absurd h.2 (not_le.2 h1')
      rw [indicator_of_notMem hm1]
      by_cases h2 : w ≤ 1
      · have hm2 : w ∈ Ioc (0 : ℝ) 1 := ⟨hw0, h2⟩
        have hm3 : w ∈ Ioc b 1 := ⟨h1', h2⟩
        rw [indicator_of_mem hm2, indicator_of_mem hm3, Pi.one_apply, sub_zero]
        ring
      · have h2' := not_le.1 h2
        have hm2 : w ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        have hm3 : w ∉ Ioc b 1 := fun h => absurd h.2 (not_le.2 h2')
        rw [indicator_of_notMem hm2, indicator_of_notMem hm3, add_zero]
  have hint : IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact integrableOn_renorm_inner.union integrableOn_renorm_outer
  have hind : IntegrableOn ((Ioc b 1).indicator fun w : ℝ => 2 / w) (Ioi 0) := by
    have : IntegrableOn (fun w : ℝ => 2 / w) (Ioc b 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb1]
      refine ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id fun x hx => ?_)
      rw [uIcc_of_le hb1] at hx
      exact ne_of_gt (lt_of_lt_of_le hb0 hx.1)
    exact (this.integrable_indicator measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add hint hind, integral_renormalised_sq,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc b 1 = Ioc b 1 from
      inter_eq_right.2 fun w hw => show (0 : ℝ) < w by linarith [hw.1],
    ← intervalIntegral.integral_of_le hb1]
  have : ∫ w in b..1, 2 / w = 2 * ∫ w in b..1, w⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun w _ => ?_
    rw [div_eq_mul_inv]
  rw [this, integral_inv_of_pos hb0 one_pos, one_div, Real.log_inv]
  ring

/-- The case `k = 1`: `∫₀^∞ (e^{−u²/2} − 1_{(0,1]}(u))·2/u du = log 2 − γ` (rescale `u = √2 w`). -/
theorem ampRenorm_monoAmp_one :
    ampRenorm (monoAmp 1) = Real.log 2 - Real.eulerMascheroniConstant := by
  unfold ampRenorm monoAmp
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set g : ℝ → ℝ := fun u => (Real.exp (-u ^ (2 * 1) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u)
    with hg
  have h := integral_comp_mul_left_Ioi g 0 (b := Real.sqrt 2) hs
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ w ∈ Ioi (0 : ℝ), g (Real.sqrt 2 * w) = (Real.sqrt 2)⁻¹ *
      ((Real.exp (-w ^ 2) - (Ioc 0 (1 / Real.sqrt 2)).indicator 1 w) * (2 / w)) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (Real.sqrt 2 * w) =
        (Ioc 0 (1 / Real.sqrt 2)).indicator 1 w := by
      by_cases hle : w ≤ 1 / Real.sqrt 2
      · have hm : Real.sqrt 2 * w ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by
          rw [le_div_iff₀ hs] at hle; linarith⟩
        have hm' : w ∈ Ioc (0 : ℝ) (1 / Real.sqrt 2) := ⟨hw0, hle⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have hle' := not_le.1 hle
        have hm : Real.sqrt 2 * w ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by
          rw [div_lt_iff₀ hs] at hle'; linarith))
        have hm' : w ∉ Ioc (0 : ℝ) (1 / Real.sqrt 2) := fun hm => absurd hm.2 (not_le.2 hle')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg]
    rw [hI, show -(Real.sqrt 2 * w) ^ (2 * 1) / 2 = -w ^ 2 by rw [mul_pow, mul_one, hs2]; ring]
    field_simp
  have hb1 : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one hs]; exact Real.one_le_sqrt.2 (by norm_num)
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_renormalised_sq_cut (by positivity) hb1] at h
  have hlog : Real.log (1 / Real.sqrt 2) = -(Real.log 2 / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt (by norm_num)]
  rw [hlog] at h
  have hX := mul_left_cancel₀ (inv_ne_zero hs.ne') h
  rw [← hX]
  ring

/-- ★★ **The monomial renormalised constant**:
`∫₀^∞ (e^{−u^{2k}/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/k` for `k ≥ 1`. -/
theorem ampRenorm_monoAmp {k : ℕ} (hk : 0 < k) :
    ampRenorm (monoAmp k) = (Real.log 2 - Real.eulerMascheroniConstant) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold ampRenorm monoAmp
  set g : ℝ → ℝ := fun v => (Real.exp (-v ^ 2 / 2) - (Ioc 0 1).indicator 1 v) * (2 / v) with hg
  have h := integral_comp_rpow_Ioi_of_pos (g := fun v => g v / k) (p := (k : ℝ)) hk'
  have e : ∀ u ∈ Ioi (0 : ℝ), ((k : ℝ) * u ^ ((k : ℝ) - 1)) • (g (u ^ (k : ℝ)) / k) =
      (Real.exp (-u ^ (2 * k) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (u ^ k) = (Ioc 0 1).indicator 1 u := by
      by_cases hle : u ≤ 1
      · have hm : u ^ k ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hu0.le hle⟩
        have hm' : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, hle⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have hle' := not_le.1 hle
        have hm : u ^ k ∉ Ioc (0 : ℝ) 1 := fun hm =>
          absurd hm.2 (not_le.2 (one_lt_pow₀ hle' hk.ne'))
        have hm' : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hle')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg, smul_eq_mul]
    rw [Real.rpow_natCast, Real.rpow_sub hu0, Real.rpow_natCast, Real.rpow_one, hI,
      show (u ^ k) ^ 2 = u ^ (2 * k) by ring]
    field_simp
  rw [← setIntegral_congr_fun measurableSet_Ioi e, h, integral_div]
  have h1 := ampRenorm_monoAmp_one
  unfold ampRenorm monoAmp at h1
  simp only [mul_one] at h1
  rw [hg, h1]

/-- The amplitude data of `e^{−u^{2k}/2}`, `k ≥ 1`: `A = 1/2`. -/
theorem monoAmp_ampData {k : ℕ} (hk : 0 < k) : AmpData (monoAmp k) (1 / 2) where
  meas := by unfold monoAmp; fun_prop
  nonneg u := by unfold monoAmp; positivity
  le_one u := by
    unfold monoAmp
    exact Real.exp_le_one_iff.2 (by
      have : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
      linarith)
  A_nonneg := by norm_num
  near u hu := by
    unfold monoAmp
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hpow : u ^ (2 * k) ≤ u ^ 2 := by
      rw [pow_mul]
      calc (u ^ 2) ^ k ≤ (u ^ 2) ^ 1 := pow_le_pow_of_le_one (by positivity) hu2 hk
        _ = u ^ 2 := pow_one _
    have := Real.add_one_le_exp (-u ^ (2 * k) / 2)
    linarith
  tail u hu := by
    unfold monoAmp
    have h1 : u ≤ u ^ (2 * k) := by
      calc u = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ (2 * k) := pow_le_pow_right₀ hu (by omega)
    exact Real.exp_le_exp.2 (by linarith)

/-- The split form: `2(∫₀¹ (e^{−u^{2k}/2} − 1)/u + ∫₁^∞ e^{−u^{2k}/2}/u) = (log 2 − γ)/k`. -/
theorem monomial_renorm_constant {k : ℕ} (hk : 0 < k) :
    2 * ((∫ u in Ioc (0 : ℝ) 1, (Real.exp (-u ^ (2 * k) / 2) - 1) / u) +
      ∫ u in Ioi (1 : ℝ), Real.exp (-u ^ (2 * k) / 2) / u) =
      (Real.log 2 - Real.eulerMascheroniConstant) / k := by
  have h := ampRenorm_monoAmp hk
  rw [ampRenorm_split (monoAmp_ampData hk)] at h
  unfold monoAmp at h
  rw [← h, mul_add, ← integral_const_mul, ← integral_const_mul]
  congr 1 <;> refine setIntegral_congr_fun (by measurability) fun u hu => ?_ <;> ring

end Grammar
