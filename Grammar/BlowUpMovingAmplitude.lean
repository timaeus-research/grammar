/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpQuarticLinear

/-!
# The moving amplitude: `J_{a_ε}(ε) − J_∞(ε) = −½√(π/2)ε + ¼ε² log(1/ε) + O(ε²)`

The true blow-up amplitude is `a_ε(u) = e^{−u⁴/2}e^{−εu²/2}` (`movingAmp`, `= blowAmp m` at
`ε = 1/m²`).  Its difference from the frozen amplitude is controlled by the quadratic exponential
bound `0 ≤ e^{−x} − 1 + x ≤ x²/2`:

  `0 ≤ J_{a_ε}(ε) − J_∞(ε) + ε·I(ε) ≤ ε²/8`,   `I(ε) = ∫₀^∞ u² e^{−u⁴/2}/√(u²+ε) du`
  (`movingJ_taylor_remainder`, with the moment `∫₀^∞ u³e^{−u⁴/2} = ½`),

and the moment carries the logarithm: `|I(ε) − ½√(π/2) + (ε/4) log(1/ε)| ≤ 2ε`
(★★ `movingMoment_log_remainder`, three intervals `(0,√ε]`, `(√ε,1]`, `(1,∞)` with the exact
`−(ε/2)∫_{√ε}^1 du/u = −(ε/4) log(1/ε)` in the middle), hence

  ★★★ `movingJ_sub_frozen : |J_{a_ε}(ε) − J_∞(ε) + ½√(π/2)ε − ¼ε² log(1/ε)| ≤ 3ε²`  (`0 < ε ≤ 1`):

the moving amplitude cancels the frozen linear term and contributes `+¼` to the `ε² log(1/ε)`
coefficient (Astra round 30, part A).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The moving amplitude -/

/-- `a_ε(u) = e^{−u⁴/2} e^{−εu²/2}`. -/
noncomputable def movingAmp (ε u : ℝ) : ℝ := blowAmpInf u * Real.exp (-ε * u ^ 2 / 2)

theorem blowAmp_eq_movingAmp {m : ℝ} (hm : 0 < m) : blowAmp m = movingAmp (1 / m ^ 2) := by
  funext u
  unfold blowAmp movingAmp blowAmpInf
  congr 2
  field_simp

/-- `0 ≤ e^{−x} − 1 + x ≤ x²/2` for `x ≥ 0`. -/
theorem exp_neg_sub_one_add_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp (-x) - 1 + x ∧ Real.exp (-x) - 1 + x ≤ x ^ 2 / 2 := by
  constructor
  · linarith [Real.add_one_le_exp (-x)]
  · have h := Real.quadratic_le_exp_of_nonneg hx
    have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
    have he : Real.exp (-x) ≤ 1 / (1 + x + x ^ 2 / 2) := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) hpos]
      linarith
    have h2 : 1 / (1 + x + x ^ 2 / 2) ≤ 1 - x + x ^ 2 / 2 := by
      rw [div_le_iff₀ hpos]
      nlinarith [pow_nonneg hx 4]
    linarith

/-! ### The cubic moment -/

theorem integrableOn_cube_mul_exp_neg_quartic :
    IntegrableOn (fun u : ℝ => u ^ 3 * Real.exp (-u ^ 4 / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 3) (p := 4) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu : (0 : ℝ) < u := hu
  simp only
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  congr 1
  ring

/-- `∫₀^∞ u³ e^{−u⁴/2} du = ½`. -/
theorem integral_cube_mul_exp_neg_quartic :
    ∫ u in Ioi (0 : ℝ), u ^ 3 * Real.exp (-u ^ 4 / 2) = 1 / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 4) (q := 3) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  rw [setIntegral_congr_fun (g := fun u : ℝ => u ^ (3 : ℝ) * Real.exp (-(1 / 2) * u ^ (4 : ℝ)))
    measurableSet_Ioi (fun u (hu : (0 : ℝ) < u) => by
    beta_reduce
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Real.rpow_natCast]
    congr 1
    ring), h]
  rw [show ((3 : ℝ) + 1) / 4 = 1 by norm_num, Real.Gamma_one,
    show (-((3 : ℝ) + 1) / 4) = -(1 : ℝ) by norm_num, Real.rpow_neg_one]
  norm_num

/-! ### The moment `I(ε) = ∫₀^∞ u² e^{−u⁴/2}/√(u²+ε)` -/

/-- `I(ε) = ∫₀^∞ u² e^{−u⁴/2}/√(u² + ε) du`. -/
noncomputable def movingMoment (ε : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)

theorem inv_sqrt_le_inv {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    1 / Real.sqrt (u ^ 2 + ε) ≤ 1 / u := by
  have h := (gap_bounds hε hu).1
  have e1 : 2 / u = 2 * (1 / u) := by ring
  have e2 : 2 / Real.sqrt (u ^ 2 + ε) = 2 * (1 / Real.sqrt (u ^ 2 + ε)) := by ring
  linarith

theorem integrableOn_movingMoment {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := by
  refine integrableOn_mul_exp_neg_quartic.mono'
    ((by unfold blowAmpInf; fun_prop : Measurable fun u : ℝ =>
      u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (0 : ℝ) < u := hu
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := inv_sqrt_le_inv hε hu
  calc u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)
      = u ^ 2 * blowAmpInf u * (1 / Real.sqrt (u ^ 2 + ε)) := by ring
    _ ≤ u ^ 2 * blowAmpInf u * (1 / u) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = u * Real.exp (-u ^ 4 / 2) := by unfold blowAmpInf; field_simp

theorem integrableOn_two_blowAmpInf_div_sqrt {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (integrableOn_ampJ_inner blowAmpInf_ampData hε).union
    (integrableOn_ampJ_outer blowAmpInf_ampData hε)

theorem integrableOn_two_movingAmp_div_sqrt {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := by
  refine (integrableOn_two_blowAmpInf_div_sqrt hε).mono'
    ((by unfold movingAmp blowAmpInf; fun_prop : Measurable fun u : ℝ =>
      2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (0 : ℝ) < u := hu
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have he : Real.exp (-ε * u ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hs : 0 < Real.sqrt (u ^ 2 + ε) := Real.sqrt_pos.2 (by positivity)
  unfold movingAmp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_div_iff_of_pos_right hs]
  nlinarith [Real.exp_pos (-ε * u ^ 2 / 2)]

/-- `0 ≤ J_{a_ε}(ε) − J_∞(ε) + ε I(ε) ≤ ε²/8`. -/
theorem movingJ_taylor_remainder {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + ε * movingMoment ε ∧
      ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + ε * movingMoment ε ≤ ε ^ 2 / 8 := by
  have hJε := integrableOn_two_movingAmp_div_sqrt hε
  have hJ := integrableOn_two_blowAmpInf_div_sqrt hε
  have hI := integrableOn_movingMoment hε
  have hsub : IntegrableOn (fun u : ℝ => 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
      2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) (Ioi 0) := hJε.sub hJ
  have hIε : IntegrableOn (fun u : ℝ => ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)))
      (Ioi 0) := hI.const_mul ε
  have hT : IntegrableOn (fun u : ℝ => 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
      2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) + ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)))
      (Ioi 0) := hsub.add hIε
  have e : ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + ε * movingMoment ε =
      ∫ u in Ioi (0 : ℝ), (2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
        2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) +
        ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε))) := by
    unfold ampJ movingMoment
    rw [integral_add hsub hIε, integral_sub hJε hJ, integral_const_mul]
  -- pointwise: the integrand is `2a(e^{−x} − 1 + x)/√(u²+ε)` with `x = εu²/2`
  have hpt : ∀ u ∈ Ioi (0 : ℝ), 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
      2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) +
      ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) =
      2 * blowAmpInf u * (Real.exp (-(ε * u ^ 2 / 2)) - 1 + ε * u ^ 2 / 2) /
        Real.sqrt (u ^ 2 + ε) := by
    intro u _
    unfold movingAmp
    rw [show -ε * u ^ 2 / 2 = -(ε * u ^ 2 / 2) by ring]
    ring
  have hnn : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
      2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) +
      ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) := by
    intro u hu
    rw [hpt u hu]
    have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
    have := (exp_neg_sub_one_add_bounds (by positivity : 0 ≤ ε * u ^ 2 / 2)).1
    positivity
  have hle : ∀ u ∈ Ioi (0 : ℝ), 2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
      2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) +
      ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)) ≤
      ε ^ 2 / 4 * (u ^ 3 * Real.exp (-u ^ 4 / 2)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [hpt u hu]
    have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
    have hb := (exp_neg_sub_one_add_bounds (by positivity : 0 ≤ ε * u ^ 2 / 2)).2
    have hinv := inv_sqrt_le_inv hε hu0
    calc 2 * blowAmpInf u * (Real.exp (-(ε * u ^ 2 / 2)) - 1 + ε * u ^ 2 / 2) /
          Real.sqrt (u ^ 2 + ε)
        = 2 * blowAmpInf u * (Real.exp (-(ε * u ^ 2 / 2)) - 1 + ε * u ^ 2 / 2) *
          (1 / Real.sqrt (u ^ 2 + ε)) := by ring
      _ ≤ 2 * blowAmpInf u * ((ε * u ^ 2 / 2) ^ 2 / 2) * (1 / u) := by
          gcongr
      _ = ε ^ 2 / 4 * (u ^ 3 * Real.exp (-u ^ 4 / 2)) := by
          unfold blowAmpInf
          field_simp
          ring
  constructor
  · rw [e]
    exact setIntegral_nonneg measurableSet_Ioi hnn
  · rw [e]
    calc ∫ u in Ioi (0 : ℝ), (2 * movingAmp ε u / Real.sqrt (u ^ 2 + ε) -
          2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε) +
          ε * (u ^ 2 * blowAmpInf u / Real.sqrt (u ^ 2 + ε)))
        ≤ ∫ u in Ioi (0 : ℝ), ε ^ 2 / 4 * (u ^ 3 * Real.exp (-u ^ 4 / 2)) :=
          setIntegral_mono_on hT (integrableOn_cube_mul_exp_neg_quartic.const_mul _)
            measurableSet_Ioi hle
      _ = ε ^ 2 / 8 := by
          rw [integral_const_mul, integral_cube_mul_exp_neg_quartic]
          ring

/-! ### The moment to first order: `I(ε) = ½√(π/2) − (ε/4) log(1/ε) + O(ε)` -/

/-- The moment remainder integrand `u² a (1/√(u²+ε) − 1/u)`. -/
noncomputable def momentRem (ε u : ℝ) : ℝ :=
  u ^ 2 * blowAmpInf u * (1 / Real.sqrt (u ^ 2 + ε) - 1 / u)

theorem momentRem_nonpos {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) : momentRem ε u ≤ 0 := by
  unfold momentRem
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have := inv_sqrt_le_inv hε hu
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem abs_momentRem_le_low {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) : |momentRem ε u| ≤ u := by
  unfold momentRem
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have ha1 : blowAmpInf u ≤ 1 := by linarith [one_sub_blowAmpInf_nonneg u]
  have h1 := inv_sqrt_le_inv hε hu
  have h2 : 0 ≤ 1 / Real.sqrt (u ^ 2 + ε) := by positivity
  rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonpos (by linarith)]
  calc u ^ 2 * blowAmpInf u * -(1 / Real.sqrt (u ^ 2 + ε) - 1 / u)
      ≤ u ^ 2 * 1 * (1 / u) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha1 (by positivity)) (by linarith) (by linarith)
          (by positivity)
    _ = u := by field_simp

theorem abs_momentRem_le_high {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |momentRem ε u| ≤ u * blowAmpInf u * (ε / (u ^ 2 + ε)) := by
  unfold momentRem
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  obtain ⟨g1, g2⟩ := gap_bounds hε hu
  have e1 : 2 / u = 2 * (1 / u) := by ring
  have e2 : 2 / Real.sqrt (u ^ 2 + ε) = 2 * (1 / Real.sqrt (u ^ 2 + ε)) := by ring
  have e3 : 2 * ε / (u * (u ^ 2 + ε)) = 2 * (ε / (u * (u ^ 2 + ε))) := by ring
  rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonpos (by linarith [inv_sqrt_le_inv hε hu])]
  have : -(1 / Real.sqrt (u ^ 2 + ε) - 1 / u) ≤ ε / (u * (u ^ 2 + ε)) := by linarith
  calc u ^ 2 * blowAmpInf u * -(1 / Real.sqrt (u ^ 2 + ε) - 1 / u)
      ≤ u ^ 2 * blowAmpInf u * (ε / (u * (u ^ 2 + ε))) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = u * blowAmpInf u * (ε / (u ^ 2 + ε)) := by
        have hne : u ≠ 0 := hu.ne'
        have hne2 : u ^ 2 + ε ≠ 0 := by positivity
        field_simp

/-- The middle-interval decomposition: `momentRem = −ε/(2u) + E` with
`|E| ≤ ε u³/4 + (3/8) ε²/u³`. -/
theorem momentRem_middle {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    |momentRem ε u + ε / (2 * u)| ≤ ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 / u ^ 3 := by
  unfold momentRem
  obtain ⟨k1, k2⟩ := kernel_second_order hε hu
  have h1 := one_sub_blowAmpInf_nonneg u
  have h2 := one_sub_blowAmpInf_le u
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  -- `1/√ − 1/u = −ε/(2u³) + r/2`, `r = 2/√ − 2/u + ε/u³`
  have e : u ^ 2 * blowAmpInf u * (1 / Real.sqrt (u ^ 2 + ε) - 1 / u) + ε / (2 * u) =
      ε * (1 - blowAmpInf u) / (2 * u) +
        u ^ 2 * blowAmpInf u * ((2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) / 2) := by
    field_simp
    ring
  rw [e]
  have hA : |ε * (1 - blowAmpInf u) / (2 * u)| ≤ ε * u ^ 3 / 4 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
  have hB : |u ^ 2 * blowAmpInf u * ((2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) / 2)| ≤
      3 / 8 * ε ^ 2 / u ^ 3 := by
    rw [abs_of_nonneg (by positivity)]
    have ha1 : blowAmpInf u ≤ 1 := by linarith
    calc u ^ 2 * blowAmpInf u * ((2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) / 2)
        ≤ u ^ 2 * 1 * (3 / 4 * ε ^ 2 / u ^ 5 / 2) := by gcongr
      _ = 3 / 8 * ε ^ 2 / u ^ 3 := by field_simp; ring
  calc |ε * (1 - blowAmpInf u) / (2 * u) +
        u ^ 2 * blowAmpInf u * ((2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) / 2)|
      ≤ |ε * (1 - blowAmpInf u) / (2 * u)| +
        |u ^ 2 * blowAmpInf u * ((2 / Real.sqrt (u ^ 2 + ε) - 2 / u + ε / u ^ 3) / 2)| :=
        abs_add_le _ _
    _ ≤ ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 / u ^ 3 := add_le_add hA hB

theorem integrableOn_momentRem {ε : ℝ} (hε : 0 < ε) : IntegrableOn (momentRem ε) (Ioi 0) := by
  refine integrableOn_mul_exp_neg_quartic.mono'
    ((by unfold momentRem blowAmpInf; fun_prop : Measurable (momentRem ε)).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs]
  unfold momentRem
  have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
  have h1 := inv_sqrt_le_inv hε hu
  have h2 : 0 ≤ 1 / Real.sqrt (u ^ 2 + ε) := by positivity
  rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonpos (by linarith)]
  calc u ^ 2 * blowAmpInf u * -(1 / Real.sqrt (u ^ 2 + ε) - 1 / u)
      ≤ u ^ 2 * blowAmpInf u * (1 / u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = u * Real.exp (-u ^ 4 / 2) := by unfold blowAmpInf; field_simp

/-- `I(ε) − ½√(π/2) = ∫₀^∞ momentRem`. -/
theorem movingMoment_sub_eq {ε : ℝ} (hε : 0 < ε) :
    movingMoment ε - Real.sqrt (Real.pi / 2) / 2 = ∫ u in Ioi (0 : ℝ), momentRem ε u := by
  rw [← integral_mul_exp_neg_quartic]
  unfold movingMoment
  rw [← integral_sub (integrableOn_movingMoment hε) integrableOn_mul_exp_neg_quartic]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu : (0 : ℝ) < u := hu
  unfold momentRem blowAmpInf
  field_simp

theorem integral_zpow_neg_three {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ u in Ioc δ 1, u ^ (-3 : ℤ) = (δ ^ (-2 : ℤ) - 1) / 2 := by
  rw [← intervalIntegral.integral_of_le hδ1, integral_zpow]
  · norm_num
    ring
  · right
    refine ⟨by norm_num, ?_⟩
    rw [uIcc_of_le hδ1]
    exact fun h => absurd h.1 (not_le.2 hδ)

/-- ★★ **The moment to first order**: `|I(ε) − ½√(π/2) + (ε/4) log(1/ε)| ≤ 2ε` for `0 < ε ≤ 1`. -/
theorem movingMoment_log_remainder {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |movingMoment ε - Real.sqrt (Real.pi / 2) / 2 + ε / 4 * Real.log (1 / ε)| ≤ 2 * ε := by
  rw [movingMoment_sub_eq hε]
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsε1 : Real.sqrt ε ≤ 1 := by rw [Real.sqrt_le_one]; exact hε1
  have hint := integrableOn_momentRem hε
  -- three intervals
  have hsplit : Ioi (0 : ℝ) = Ioc 0 (Real.sqrt ε) ∪ (Ioc (Real.sqrt ε) 1 ∪ Ioi 1) := by
    rw [Ioc_union_Ioi_eq_Ioi hsε1, Ioc_union_Ioi_eq_Ioi hsε.le]
  have hlow : IntegrableOn (momentRem ε) (Ioc 0 (Real.sqrt ε)) :=
    hint.mono_set (Ioc_subset_Ioi_self)
  have hmid : IntegrableOn (momentRem ε) (Ioc (Real.sqrt ε) 1) :=
    hint.mono_set (fun u hu => mem_Ioi.2 (lt_trans hsε hu.1))
  have hhigh : IntegrableOn (momentRem ε) (Ioi 1) :=
    hint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hdisj1 : Disjoint (Ioc (0 : ℝ) (Real.sqrt ε)) (Ioc (Real.sqrt ε) 1 ∪ Ioi 1) :=
    Set.disjoint_left.2 fun u h1 h2 => by
      rcases h2 with h2 | h2
      · exact absurd h2.1 (not_lt.2 h1.2)
      · exact absurd (lt_of_le_of_lt h1.2 (lt_of_le_of_lt hsε1 h2)) (lt_irrefl u)
  rw [hsplit, setIntegral_union hdisj1 (measurableSet_Ioc.union measurableSet_Ioi) hlow
    (hmid.union hhigh), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hmid hhigh]
  -- low: `≤ ε/2`
  have hL : |∫ u in Ioc (0 : ℝ) (Real.sqrt ε), momentRem ε u| ≤ ε / 2 := by
    have hmaj : IntegrableOn (fun u : ℝ => u) (Ioc 0 (Real.sqrt ε)) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε.le]
      exact continuous_id.intervalIntegrable _ _
    have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc 0 (Real.sqrt ε)))
      (f := momentRem ε) hmaj (by
        rw [ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun u hu => by
          rw [Real.norm_eq_abs]; exact abs_momentRem_le_low hε hu.1)
    have hid : ∫ x in Ioc (0 : ℝ) (Real.sqrt ε), x = ε / 2 := by
      rw [← intervalIntegral.integral_of_le hsε.le, integral_id, Real.sq_sqrt hε.le]
      ring
    rw [Real.norm_eq_abs, hid] at hb
    exact hb
  -- middle: `= −(ε/4) log(1/ε) + O(ε)`
  have hM : |(∫ u in Ioc (Real.sqrt ε) 1, momentRem ε u) + ε / 4 * Real.log (1 / ε)| ≤ ε / 4 := by
    have hinv : IntegrableOn (fun u : ℝ => ε / (2 * u)) (Ioc (Real.sqrt ε) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1]
      refine ContinuousOn.intervalIntegrable ((continuousOn_const.div (by fun_prop)) fun u hu => ?_)
      rw [uIcc_of_le hsε1] at hu
      have : (0 : ℝ) < u := lt_of_lt_of_le hsε hu.1
      positivity
    have hinv_val : ∫ u in Ioc (Real.sqrt ε) 1, ε / (2 * u) = ε / 4 * Real.log (1 / ε) := by
      rw [← intervalIntegral.integral_of_le hsε1]
      have : (fun u : ℝ => ε / (2 * u)) = fun u => (ε / 2) * (1 / u) := by funext u; ring
      rw [this, intervalIntegral.integral_const_mul, integral_one_div_of_pos hsε one_pos]
      simp only [one_div, Real.log_inv]
      rw [Real.log_sqrt hε.le]
      ring
    have hE : IntegrableOn (fun u : ℝ => momentRem ε u + ε / (2 * u)) (Ioc (Real.sqrt ε) 1) :=
      hmid.add hinv
    have hmaj : IntegrableOn (fun u : ℝ => ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 * u ^ (-3 : ℤ))
        (Ioc (Real.sqrt ε) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1]
      refine ContinuousOn.intervalIntegrable ?_
      refine (by fun_prop : ContinuousOn (fun u : ℝ => ε * u ^ 3 / 4) _).add
        (continuousOn_const.mul (continuousOn_id.zpow₀ (-3) fun u hu => ?_))
      rw [uIcc_of_le hsε1] at hu
      exact Or.inl (lt_of_lt_of_le hsε hu.1).ne'
    have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (Real.sqrt ε) 1))
      (f := fun u => momentRem ε u + ε / (2 * u)) hmaj (by
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun u hu => ?_
        have hu0 : 0 < u := lt_trans hsε hu.1
        rw [Real.norm_eq_abs, show u ^ (-3 : ℤ) = 1 / u ^ 3 by rw [zpow_neg, zpow_ofNat, one_div]]
        have := momentRem_middle hε hu0
        calc |momentRem ε u + ε / (2 * u)| ≤ ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 / u ^ 3 := this
          _ = ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 * (1 / u ^ 3) := by ring)
    rw [integral_add hmid hinv, hinv_val, Real.norm_eq_abs] at hb
    have hval :
        ∫ u in Ioc (Real.sqrt ε) 1, (ε * u ^ 3 / 4 + 3 / 8 * ε ^ 2 * u ^ (-3 : ℤ)) ≤ ε / 4 := by
      have hc : IntegrableOn (fun u : ℝ => ε * u ^ 3 / 4) (Ioc (Real.sqrt ε) 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hsε1).1
          ((by fun_prop : Continuous fun u : ℝ => ε * u ^ 3 / 4).intervalIntegrable _ _)
      have hz : IntegrableOn (fun u : ℝ => 3 / 8 * ε ^ 2 * u ^ (-3 : ℤ)) (Ioc (Real.sqrt ε) 1) :=
        (hmaj.sub hc).congr_fun (fun u _ => by rw [Pi.sub_apply]; ring) measurableSet_Ioc
      rw [integral_add hc hz, integral_const_mul, integral_zpow_neg_three hsε hsε1,
        ← intervalIntegral.integral_of_le hsε1]
      have e1 : ∫ u in (Real.sqrt ε : ℝ)..1, ε * u ^ 3 / 4 =
          ε / 4 * ((1 - Real.sqrt ε ^ 4) / 4) := by
        have : (fun u : ℝ => ε * u ^ 3 / 4) = fun u => (ε / 4) * u ^ 3 := by funext u; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow]
        norm_num
      rw [e1, zpow_neg, zpow_two, Real.mul_self_sqrt hε.le]
      have h4 : 0 ≤ Real.sqrt ε ^ 4 := by positivity
      have : ε ^ 2 * (ε⁻¹ - 1) ≤ ε := by
        have h' : ε ^ 2 * ε⁻¹ = ε := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hε.ne', mul_one]
        rw [mul_sub, h']
        nlinarith
      nlinarith
    exact hb.trans hval
  -- high: `≤ ε/2`
  have hH : |∫ u in Ioi (1 : ℝ), momentRem ε u| ≤ ε / 2 := by
    have hmaj : IntegrableOn (fun u : ℝ => ε * (u ^ 3 * Real.exp (-u ^ 4 / 2))) (Ioi 1) :=
      (integrableOn_cube_mul_exp_neg_quartic.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul ε
    have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := momentRem ε) hmaj (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun u hu => ?_
        have hu1 : (1 : ℝ) < u := hu
        have hu0 : 0 < u := by linarith
        rw [Real.norm_eq_abs]
        refine (abs_momentRem_le_high hε hu0).trans ?_
        have ha0 : 0 ≤ blowAmpInf u := by unfold blowAmpInf; positivity
        have : ε / (u ^ 2 + ε) ≤ ε := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : 1 ≤ u ^ 2 + ε := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
        have hu3 : u ≤ u ^ 3 := by nlinarith
        calc u * blowAmpInf u * (ε / (u ^ 2 + ε)) ≤ u ^ 3 * blowAmpInf u * ε :=
              mul_le_mul (mul_le_mul_of_nonneg_right hu3 ha0) this (by positivity) (by positivity)
          _ = ε * (u ^ 3 * Real.exp (-u ^ 4 / 2)) := by unfold blowAmpInf; ring)
    rw [Real.norm_eq_abs, integral_const_mul] at hb
    have hnn : 0 ≤ ∫ u in Ioi (1 : ℝ), u ^ 3 * Real.exp (-u ^ 4 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun u hu => by
        have : (0 : ℝ) < u := by linarith [show (1 : ℝ) < u from hu]
        positivity
    have hle : ∫ u in Ioi (1 : ℝ), u ^ 3 * Real.exp (-u ^ 4 / 2) ≤ 1 / 2 := by
      rw [← integral_cube_mul_exp_neg_quartic]
      exact setIntegral_mono_set integrableOn_cube_mul_exp_neg_quartic
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => by
          have : (0 : ℝ) < u := hu
          rw [Pi.zero_apply]
          positivity))
        (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
    nlinarith
  rw [abs_le] at hL hM hH ⊢
  constructor <;> linarith

/-! ### The assembly -/

/-- ★★★ **The moving amplitude**:
`|J_{a_ε}(ε) − J_∞(ε) + ½√(π/2)ε − ¼ε² log(1/ε)| ≤ 3ε²` for `0 < ε ≤ 1`. -/
theorem movingJ_sub_frozen {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (movingAmp ε) ε - ampJ blowAmpInf ε + Real.sqrt (Real.pi / 2) / 2 * ε -
      ε ^ 2 / 4 * Real.log (1 / ε)| ≤ 3 * ε ^ 2 := by
  obtain ⟨h1, h2⟩ := movingJ_taylor_remainder hε
  have h3 := movingMoment_log_remainder hε hε1
  rw [abs_le] at h3 ⊢
  constructor <;> nlinarith [sq_nonneg ε]

end Grammar
