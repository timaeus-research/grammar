/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpMovingAmplitude

/-!
# The frozen quartic amplitude to second order, and the moving amplitude with it

The inner remainder of DCLXXXVI is refined one order: with the third-order kernel gap
`0 ≤ (3/4)ε²/u⁵ − r ≤ (5/8)ε³/u⁷` (`r = 2/√(u²+ε) − 2/u + ε/u³`) and the amplitude
`0 ≤ a − 1 + u⁴/2 ≤ u⁸/8`, the middle interval `(√ε, 1]` carries the exact logarithm
`−(3/8)ε²∫_{√ε}^1 du/u = −(3/16)ε² log(1/ε)`, so

  ★★ `quarticJ_second_order : |J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)ε − (3/16)ε² log(1/ε))| ≤ 2ε²`

and, with DCLXXXVII's moving-amplitude comparison,

  ★★★ `movingJ_second_order : |J_{a_ε}(ε) − (log(4/ε) + R_∞ + (1/16)ε² log(1/ε))| ≤ 5ε²`

for `0 < ε ≤ 1`: the linear terms cancel exactly and the net `ε² log(1/ε)` coefficient is
`−3/16 + 1/4 = 1/16` (Astra round 30, part B).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The kernel gap to third order -/

/-- `0 ≤ (3/4)ε²/u⁵ − (2/√(u²+ε) − 2/u + ε/u³) ≤ (5/8)ε³/u⁷`. -/
theorem kernel_third_order {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ 3 / 4 * ε ^ 2 / u ^ 5 - (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) ∧
      3 / 4 * ε ^ 2 / u ^ 5 - (2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) ≤
        5 / 8 * ε ^ 3 / u ^ 7 := by
  have hpos : 0 < u ^ 2 + ε := by positivity
  set s := Real.sqrt (u ^ 2 + ε) with hs
  have hs2 : s ^ 2 = u ^ 2 + ε := Real.sq_sqrt hpos.le
  have hsu : u < s := Real.lt_sqrt hu.le |>.2 (by linarith)
  have hs0 : 0 < s := by linarith
  have hε' : ε = s ^ 2 - u ^ 2 := by linarith
  have h1 : 0 ≤ s - u := by linarith
  have e : 3 / 4 * ε ^ 2 / u ^ 5 - (2 / s - 2 / u + ε / u ^ 3) =
      (s - u) ^ 3 * (3 * s ^ 2 + 9 * s * u + 8 * u ^ 2) / (4 * s * u ^ 5) := by
    rw [hε']
    field_simp
    ring
  rw [e]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity), hε']
    have h3 : 0 ≤ (s - u) ^ 3 := pow_nonneg h1 3
    have key : (3 * s ^ 2 + 9 * s * u + 8 * u ^ 2) * u ^ 2 ≤ 5 / 2 * (s + u) ^ 3 * s := by
      nlinarith [mul_nonneg h1
        (by positivity : (0 : ℝ) ≤ 5 * s ^ 3 + 20 * s ^ 2 * u + 29 * s * u ^ 2 + 16 * u ^ 3)]
    have : (s - u) ^ 3 * (3 * s ^ 2 + 9 * s * u + 8 * u ^ 2) * u ^ 7 ≤
        5 / 8 * ((s - u) ^ 3 * (s + u) ^ 3) * (4 * s * u ^ 5) := by
      have := mul_le_mul_of_nonneg_left key (mul_nonneg h3 (by positivity : (0 : ℝ) ≤ u ^ 5))
      nlinarith [this]
    calc (s - u) ^ 3 * (3 * s ^ 2 + 9 * s * u + 8 * u ^ 2) * u ^ 7
        ≤ 5 / 8 * ((s - u) ^ 3 * (s + u) ^ 3) * (4 * s * u ^ 5) := this
      _ = 5 / 8 * (s ^ 2 - u ^ 2) ^ 3 * (4 * s * u ^ 5) := by ring

/-! ### The amplitude to second order -/

/-- `0 ≤ e^{−u⁴/2} − 1 + u⁴/2 ≤ u⁸/8`. -/
theorem blowAmpInf_sub_one_add_bounds (u : ℝ) :
    0 ≤ blowAmpInf u - 1 + u ^ 4 / 2 ∧ blowAmpInf u - 1 + u ^ 4 / 2 ≤ u ^ 8 / 8 := by
  have h := exp_neg_sub_one_add_bounds (by positivity : 0 ≤ u ^ 4 / 2)
  unfold blowAmpInf
  rw [show -u ^ 4 / 2 = -(u ^ 4 / 2) by ring]
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  ring

/-! ### The middle interval: `quarticRem = −(3/8)ε²/u + O(ε²u³ + ε³/u³)` -/

/-- `0 ≤ quarticRem ε u + (3/8)ε²/u ≤ (3/32)ε²u³ + (5/16)ε³/u³`. -/
theorem quarticRem_middle {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    0 ≤ quarticRem ε u + 3 / 8 * ε ^ 2 / u ∧
      quarticRem ε u + 3 / 8 * ε ^ 2 / u ≤ 3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 / u ^ 3 := by
  unfold quarticRem
  obtain ⟨k1, k2⟩ := kernel_second_order hε hu
  obtain ⟨g1, g2⟩ := kernel_third_order hε hu
  obtain ⟨a1, a2⟩ := blowAmpInf_sub_one_add_bounds u
  -- `(a − 1) r + (3/8)ε²/u = (u⁴/2)·gap + E_a·r` with `E_a = a − 1 + u⁴/2`, `gap = (3/4)ε²/u⁵ − r`
  set r := 2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3 with hr
  have e : (blowAmpInf u - 1) * r + 3 / 8 * ε ^ 2 / u =
      u ^ 4 / 2 * (3 / 4 * ε ^ 2 / u ^ 5 - r) + (blowAmpInf u - 1 + u ^ 4 / 2) * r := by
    field_simp
    ring
  rw [e]
  constructor
  · positivity
  · have hA : u ^ 4 / 2 * (3 / 4 * ε ^ 2 / u ^ 5 - r) ≤ u ^ 4 / 2 * (5 / 8 * ε ^ 3 / u ^ 7) :=
      mul_le_mul_of_nonneg_left g2 (by positivity)
    have hB : (blowAmpInf u - 1 + u ^ 4 / 2) * r ≤ u ^ 8 / 8 * (3 / 4 * ε ^ 2 / u ^ 5) :=
      mul_le_mul a2 k2 k1 (by positivity)
    have e1 : u ^ 4 / 2 * (5 / 8 * ε ^ 3 / u ^ 7) = 5 / 16 * ε ^ 3 / u ^ 3 := by
      field_simp
      ring
    have e2 : u ^ 8 / 8 * (3 / 4 * ε ^ 2 / u ^ 5) = 3 / 32 * ε ^ 2 * u ^ 3 := by
      field_simp
      ring
    linarith

/-- ★★ `|∫₀¹ quarticRem + (3/16)ε² log(1/ε)| ≤ ε²` for `0 < ε ≤ 1`. -/
theorem abs_integral_quarticRem_second {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |(∫ u in Ioc (0 : ℝ) 1, quarticRem ε u) + 3 / 16 * ε ^ 2 * Real.log (1 / ε)| ≤ ε ^ 2 := by
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsε1 : Real.sqrt ε ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hε1
  have hint := integrableOn_quarticRem hε hε1
  have hsplit : Ioc (0 : ℝ) 1 = Ioc 0 (Real.sqrt ε) ∪ Ioc (Real.sqrt ε) 1 :=
    (Ioc_union_Ioc_eq_Ioc hsε.le hsε1).symm
  have hlow : IntegrableOn (quarticRem ε) (Ioc 0 (Real.sqrt ε)) :=
    hint.mono_set (Ioc_subset_Ioc_right hsε1)
  have hhigh : IntegrableOn (quarticRem ε) (Ioc (Real.sqrt ε) 1) :=
    hint.mono_set (Ioc_subset_Ioc_left hsε.le)
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.sqrt ε)) (Ioc (Real.sqrt ε) 1) :=
    Set.disjoint_left.2 fun u h1 h2 => absurd h2.1 (not_lt.2 h1.2)
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hlow hhigh]
  -- the low piece: `≤ ε²/2`
  have hmajL : IntegrableOn (fun u : ℝ => u ^ 3 + ε * u / 2) (Ioc 0 (Real.sqrt ε)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε.le]
    exact (by fun_prop : Continuous fun u : ℝ => u ^ 3 + ε * u / 2).intervalIntegrable _ _
  have hL := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc 0 (Real.sqrt ε)))
    (f := quarticRem ε) hmajL (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact abs_quarticRem_le_low hε hu.1)
  have hLval : ∫ u in Ioc (0 : ℝ) (Real.sqrt ε), (u ^ 3 + ε * u / 2) = ε ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hsε.le, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun u : ℝ => u ^ 3).intervalIntegrable 0 (Real.sqrt ε))
      ((by fun_prop : Continuous fun u : ℝ => ε * u / 2).intervalIntegrable 0 (Real.sqrt ε))]
    have e1 : ∫ u in (0 : ℝ)..Real.sqrt ε, u ^ 3 = Real.sqrt ε ^ 4 / 4 := by
      rw [integral_pow]; norm_num
    have e2 : ∫ u in (0 : ℝ)..Real.sqrt ε, ε * u / 2 = ε * Real.sqrt ε ^ 2 / 4 := by
      have : (fun u : ℝ => ε * u / 2) = fun u => (ε / 2) * u ^ 1 := by funext u; ring
      rw [this, intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
    rw [e1, e2, show Real.sqrt ε ^ 4 = (Real.sqrt ε ^ 2) ^ 2 by ring, Real.sq_sqrt hε.le]
    ring
  rw [Real.norm_eq_abs, hLval] at hL
  -- the middle piece: subtract the exact logarithm
  have hinv : IntegrableOn (fun u : ℝ => 3 / 8 * ε ^ 2 / u) (Ioc (Real.sqrt ε) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1]
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_const.div continuousOn_id fun u hu => ?_)
    rw [uIcc_of_le hsε1] at hu
    exact (lt_of_lt_of_le hsε hu.1).ne'
  have hinv_val : ∫ u in Ioc (Real.sqrt ε) 1, 3 / 8 * ε ^ 2 / u =
      3 / 16 * ε ^ 2 * Real.log (1 / ε) := by
    rw [← intervalIntegral.integral_of_le hsε1]
    have : (fun u : ℝ => 3 / 8 * ε ^ 2 / u) = fun u => (3 / 8 * ε ^ 2) * (1 / u) := by
      funext u; ring
    rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos hsε one_pos]
    simp only [one_div, Real.log_inv]
    rw [Real.log_sqrt hε.le]
    ring
  have hmajM : IntegrableOn (fun u : ℝ => 3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 * u ^ (-3 : ℤ))
      (Ioc (Real.sqrt ε) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1]
    refine ContinuousOn.intervalIntegrable ?_
    refine (by fun_prop : ContinuousOn (fun u : ℝ => 3 / 32 * ε ^ 2 * u ^ 3) _).add
      (continuousOn_const.mul (continuousOn_id.zpow₀ (-3) fun u hu => ?_))
    rw [uIcc_of_le hsε1] at hu
    exact Or.inl (lt_of_lt_of_le hsε hu.1).ne'
  have hM := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (Real.sqrt ε) 1))
    (f := fun u => quarticRem ε u + 3 / 8 * ε ^ 2 / u) hmajM (by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : 0 < u := lt_trans hsε hu.1
      obtain ⟨m1, m2⟩ := quarticRem_middle hε hu0
      rw [Real.norm_eq_abs, abs_of_nonneg m1,
        show u ^ (-3 : ℤ) = 1 / u ^ 3 by rw [zpow_neg, zpow_ofNat, one_div]]
      calc quarticRem ε u + 3 / 8 * ε ^ 2 / u
          ≤ 3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 / u ^ 3 := m2
        _ = 3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 * (1 / u ^ 3) := by ring)
  rw [integral_add hhigh hinv, hinv_val, Real.norm_eq_abs] at hM
  have hMval :
      ∫ u in Ioc (Real.sqrt ε) 1, (3 / 32 * ε ^ 2 * u ^ 3 + 5 / 16 * ε ^ 3 * u ^ (-3 : ℤ)) ≤
        ε ^ 2 / 2 := by
    have hc : IntegrableOn (fun u : ℝ => 3 / 32 * ε ^ 2 * u ^ 3) (Ioc (Real.sqrt ε) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1).1
        ((by fun_prop : Continuous fun u : ℝ => 3 / 32 * ε ^ 2 * u ^ 3).intervalIntegrable _ _)
    have hz : IntegrableOn (fun u : ℝ => 5 / 16 * ε ^ 3 * u ^ (-3 : ℤ)) (Ioc (Real.sqrt ε) 1) :=
      (hmajM.sub hc).congr_fun (fun u _ => by rw [Pi.sub_apply]; ring) measurableSet_Ioc
    rw [integral_add hc hz, integral_const_mul, integral_const_mul,
      integral_zpow_neg_three hsε hsε1, ← intervalIntegral.integral_of_le hsε1, integral_pow]
    rw [zpow_neg, zpow_two, Real.mul_self_sqrt hε.le]
    push_cast
    have h4 : 0 ≤ Real.sqrt ε ^ 4 := by positivity
    have : ε ^ 3 * (ε⁻¹ - 1) ≤ ε ^ 2 := by
      have h' : ε ^ 3 * ε⁻¹ = ε ^ 2 := by
        rw [pow_succ, mul_assoc, mul_inv_cancel₀ hε.ne', mul_one]
      rw [mul_sub, h']
      nlinarith [pow_nonneg hε.le 3]
    nlinarith
  have hM' := hM.trans hMval
  rw [abs_le] at hL hM' ⊢
  constructor <;> linarith

/-! ### The frozen amplitude to second order -/

/-- ★★ **The frozen quartic amplitude to second order**:
`|J_∞(ε) − (log(4/ε) + R_∞ + ½√(π/2)ε − (3/16)ε² log(1/ε))| ≤ 2ε²` for `0 < ε ≤ 1`. -/
theorem quarticJ_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ blowAmpInf ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      Real.sqrt (Real.pi / 2) / 2 * ε - 3 / 16 * ε ^ 2 * Real.log (1 / ε))| ≤ 2 * ε ^ 2 := by
  have h := blowAmpInf_ampData
  have hA1 := integrableOn_ampJ_inner h hε
  have hA2 := integrableOn_ampJ_outer h hε
  have hp1 := integrableOn_elem hε
  have hq1 : IntegrableOn (fun u : ℝ => (blowAmpInf u - 1) * (2 / u)) (Ioc 0 1) :=
    (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : IntegrableOn (fun u : ℝ => blowAmpInf u * (2 / u)) (Ioi 1) :=
    (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  have hJ : ampJ blowAmpInf ε = (∫ u in Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) +
      ∫ u in Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) := by
    unfold ampJ
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA1 hA2]
  have hE : ∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε) =
      2 * Real.log ((1 + Real.sqrt (1 + ε)) / Real.sqrt ε) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_elem hε]
  have hin := integrableOn_one_sub_blowAmpInf_div_cube_inner
  have hqR := integrableOn_quarticRem hε hε1
  have hR1 : ∫ u in Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioc (0 : ℝ) 1, 2 / Real.sqrt (u ^ 2 + ε)) +
        (∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
        (∫ u in Ioc (0 : ℝ) 1, quarticRem ε u) +
        ε * ∫ u in Ioc (0 : ℝ) 1, (1 - blowAmpInf u) / u ^ 3 := by
    have e : ∀ u ∈ Ioc (0 : ℝ) 1, 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
        2 / Real.sqrt (u ^ 2 + ε) + (blowAmpInf u - 1) * (2 / u) + quarticRem ε u +
          ε * ((1 - blowAmpInf u) / u ^ 3) := by
      intro u hu
      have hu0 : 0 < u := hu.1
      unfold quarticRem
      field_simp
      ring
    have hI1 : IntegrableOn (fun u : ℝ => 2 / Real.sqrt (u ^ 2 + ε) +
        (blowAmpInf u - 1) * (2 / u)) (Ioc 0 1) := hp1.add hq1
    have hI2 : IntegrableOn (fun u : ℝ => 2 / Real.sqrt (u ^ 2 + ε) +
        (blowAmpInf u - 1) * (2 / u) + quarticRem ε u) (Ioc 0 1) := hI1.add hqR
    have hI3 : IntegrableOn (fun u : ℝ => ε * ((1 - blowAmpInf u) / u ^ 3)) (Ioc 0 1) :=
      hin.const_mul ε
    rw [setIntegral_congr_fun measurableSet_Ioc e, integral_add hI2 hI3, integral_add hI1 hqR,
      integral_add hp1 hq1, integral_const_mul]
  have hout := integrableOn_blowAmpInf_div_cube
  have hqO := integrableOn_quarticOuter hε
  have hR2 : ∫ u in Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
      (∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u)) + (∫ u in Ioi (1 : ℝ), quarticOuter ε u) -
        ε * ∫ u in Ioi (1 : ℝ), blowAmpInf u / u ^ 3 := by
    have e : ∀ u ∈ Ioi (1 : ℝ), 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) =
        blowAmpInf u * (2 / u) + quarticOuter ε u - ε * (blowAmpInf u / u ^ 3) := by
      intro u hu
      have hu0 : 0 < u := by linarith [show (1 : ℝ) < u from hu]
      unfold quarticOuter
      field_simp
      ring
    have hO1 : IntegrableOn (fun u : ℝ => blowAmpInf u * (2 / u) + quarticOuter ε u) (Ioi 1) :=
      hq2.add hqO
    have hO2 : IntegrableOn (fun u : ℝ => ε * (blowAmpInf u / u ^ 3)) (Ioi 1) := hout.const_mul ε
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub hO1 hO2, integral_add hq2 hqO,
      integral_const_mul]
  have hκ : quarticLinear = (∫ u in Ioc (0 : ℝ) 1, (1 - blowAmpInf u) / u ^ 3) +
      ∫ u in Ioi (1 : ℝ), (1 - blowAmpInf u) / u ^ 3 := by
    unfold quarticLinear
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi hin integrableOn_one_sub_blowAmpInf_div_cube_outer]
  have hb1 := elem_second_order hε hε1
  have hb2 := abs_integral_quarticRem_second hε hε1
  have hb3 := abs_integral_quarticOuter_le hε
  have hsplit := ampRenorm_split h
  rw [hJ, hR1, hR2, hE, hsplit, ← quarticLinear_eq, hκ, integral_inv_cube_Ioi_one]
  rw [abs_le] at hb1 hb2 hb3 ⊢
  constructor <;> nlinarith [sq_nonneg ε]

/-! ### The moving amplitude to second order -/

/-- ★★★ **The blow-up amplitude integral to second order**:
`|J_{a_ε}(ε) − (log(4/ε) + R_∞ + (1/16)ε² log(1/ε))| ≤ 5ε²` for `0 < ε ≤ 1`, with
`a_ε(u) = e^{−u⁴/2}e^{−εu²/2}`: the linear terms of the frozen amplitude and of the moving
correction cancel exactly, and the `ε² log(1/ε)` coefficient is `−3/16 + 1/4 = 1/16`. -/
theorem movingJ_second_order {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (movingAmp ε) ε - (Real.log (4 / ε) + ampRenorm blowAmpInf +
      1 / 16 * ε ^ 2 * Real.log (1 / ε))| ≤ 5 * ε ^ 2 := by
  have h1 := quarticJ_second_order hε hε1
  have h2 := movingJ_sub_frozen hε hε1
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [sq_nonneg ε]

/-! ### The evidence to three terms -/

/-- The three-term expansion at `N = m⁴`, `m ≥ 1`:
`|Z_{m⁴} − √(π/2)(4 log m + 5 log 2 − γ)/m² − √(2π) log m/(8m⁶)| ≤ 5√(2π)/m⁶`. -/
theorem blowupLaplace_three_term_m {m : ℝ} (hm : 1 ≤ m) :
    |blowupLaplace (m ^ 4) - Real.sqrt (Real.pi / 2) *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2 -
      Real.sqrt (2 * Real.pi) * Real.log m / (8 * m ^ 6)| ≤
      5 * Real.sqrt (2 * Real.pi) / m ^ 6 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hε : 0 < 1 / m ^ 2 := by positivity
  have hε1 : 1 / m ^ 2 ≤ 1 := by rw [div_le_one hm2]; nlinarith
  have hJ := movingJ_second_order hε hε1
  rw [ampRenorm_blowAmpInf] at hJ
  have hlog4 : Real.log (4 / (1 / m ^ 2)) = 2 * Real.log 2 + 2 * Real.log m := by
    rw [show (4 : ℝ) / (1 / m ^ 2) = 2 ^ 2 * m ^ 2 by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog1 : Real.log (1 / (1 / m ^ 2)) = 2 * Real.log m := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  rw [hlog4, hlog1] at hJ
  rw [blowupLaplace_eq_ampJ hm0, blowAmp_eq_movingAmp hm0, ← sqrt_two_pi_div_two]
  set J := ampJ (movingAmp (1 / m ^ 2)) (1 / m ^ 2) with hJdef
  clear_value J
  have key : Real.sqrt (2 * Real.pi) / m ^ 2 * J - Real.sqrt (2 * Real.pi) / 2 *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2 -
      Real.sqrt (2 * Real.pi) * Real.log m / (8 * m ^ 6) =
      Real.sqrt (2 * Real.pi) / m ^ 2 * (J - (2 * Real.log 2 + 2 * Real.log m +
        (Real.log 2 - Real.eulerMascheroniConstant) / 2 +
        1 / 16 * (1 / m ^ 2) ^ 2 * (2 * Real.log m))) := by
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  calc Real.sqrt (2 * Real.pi) / m ^ 2 * |J - (2 * Real.log 2 + 2 * Real.log m +
        (Real.log 2 - Real.eulerMascheroniConstant) / 2 +
        1 / 16 * (1 / m ^ 2) ^ 2 * (2 * Real.log m))|
      ≤ Real.sqrt (2 * Real.pi) / m ^ 2 * (5 * (1 / m ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 5 * Real.sqrt (2 * Real.pi) / m ^ 6 := by
        field_simp

/-- ★★★ **The three-term expansion of the blow-up model's partition function**: for `N ≥ 1`,
`|Z_N − √(π/2)(log N + 5 log 2 − γ)/√N − (√(2π)/32) log N/(N√N)| ≤ 5√(2π)/(N√N)`:
the `N^{−3/2} log N` coefficient is `√(2π)/32` (the frozen `−3/16` and the moving `+1/4`), and
the `N^{−1}` order is empty (no `N^{−1}` or `N^{−1} log N` term). -/
theorem blowupLaplace_three_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N -
      Real.sqrt (2 * Real.pi) / 32 * Real.log N / (N * Real.sqrt N)| ≤
      5 * Real.sqrt (2 * Real.pi) / (N * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  set m := N ^ (1 / 4 : ℝ) with hm
  have hm1 : 1 ≤ m := Real.one_le_rpow hN (by norm_num)
  have hm0 : 0 < m := by linarith
  have hm4 : m ^ 4 = N := by
    rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlogm : Real.log N = 4 * Real.log m := by
    rw [← hm4, Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt N = m ^ 2 := by
    rw [← hm4, show m ^ 4 = (m ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h := blowupLaplace_three_term_m hm1
  rw [hsqrt, hlogm, ← hm4]
  have e1 : Real.sqrt (2 * Real.pi) / 32 * (4 * Real.log m) / (m ^ 4 * m ^ 2) =
      Real.sqrt (2 * Real.pi) * Real.log m / (8 * m ^ 6) := by
    field_simp
    ring
  have e2 : 5 * Real.sqrt (2 * Real.pi) / (m ^ 4 * m ^ 2) =
      5 * Real.sqrt (2 * Real.pi) / m ^ 6 := by
    ring
  rw [e1, e2]
  exact h

end Grammar
