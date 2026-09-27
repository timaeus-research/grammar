/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GaussianDepthTwoExpansion

/-!
# The two-term expansion of `∫₀^∞ 2a(u)/√(u² + ε) du` for a general amplitude

`Grammar.GaussianDepthTwoExpansion` expands `J(ε) = ∫₀^∞ 2e^{−w²}/√(w² + ε) dw`.  The same argument
works for any amplitude `a` with `0 ≤ a ≤ 1`, `1 − a(u) ≤ A u²` near `0` and `a(u) ≤ e^{−u/2}` for
`u ≥ 1` (`AmpData`):

  `|J_a(ε) − (log(4/ε) + R_a)| ≤ A ε (log(1/ε) + 1) + 4ε`  for `0 < ε ≤ 1`  (★★ `ampJ_two_term`),

with the renormalised constant `R_a = ∫₀^∞ (a(u) − 1_{(0,1]}(u))·2/u du` (`ampRenorm`).  This is the
engine of the blow-up model's expansion (`Grammar.BlowUpLaplaceExpansion`, amplitude
`e^{−u⁴/2}e^{−u²/2m²}`).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- `J_a(ε) = ∫₀^∞ 2 a(u)/√(u² + ε) du`. -/
noncomputable def ampJ (a : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), 2 * a u / Real.sqrt (u ^ 2 + ε)

/-- The renormalised constant `R_a = ∫₀^∞ (a(u) − 1_{(0,1]}(u))·2/u du`. -/
noncomputable def ampRenorm (a : ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), (a u - (Ioc 0 1).indicator 1 u) * (2 / u)

/-- The amplitude hypotheses. -/
structure AmpData (a : ℝ → ℝ) (A : ℝ) : Prop where
  meas : Measurable a
  nonneg : ∀ u, 0 ≤ a u
  le_one : ∀ u, a u ≤ 1
  A_nonneg : 0 ≤ A
  near : ∀ u ∈ Ioc (0 : ℝ) 1, 1 - a u ≤ A * u ^ 2
  tail : ∀ u, 1 ≤ u → a u ≤ Real.exp (-u / 2)

variable {a : ℝ → ℝ} {A : ℝ}

/-! ### The two remainders -/

/-- `|∫₀¹ (a(u) − 1)(2/√(u² + ε) − 2/u) du| ≤ A ε (log(1/ε) + 1)` for `0 < ε ≤ 1`. -/
theorem amp_rem_inner_le (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤
      A * (ε * (Real.log (1 / ε) + 1)) := by
  have hA := h.A_nonneg
  have hmaj : IntegrableOn (fun u : ℝ => A * (2 * ε * u / (u ^ 2 + ε))) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (ContinuousOn.intervalIntegrable
      ((by fun_prop : ContinuousOn (fun w : ℝ => 2 * ε * w) (uIcc 0 1)).div (by fun_prop)
        fun w _ => by positivity)).const_mul A
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun u => (a u - 1) * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, integral_majorant hε]
    have h1 : Real.log (1 + ε) ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + ε)]
    rw [one_div, Real.log_inv]
    refine mul_le_mul_of_nonneg_left ?_ h.A_nonneg
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu.1
    obtain ⟨g1, g2⟩ := gap_bounds hε hu0
    have hn := h.near u hu
    have hle := h.le_one u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc -(a u - 1) * -(2 / Real.sqrt (u ^ 2 + ε) - 2 / u)
        ≤ (A * u ^ 2) * (2 * ε / (u * (u ^ 2 + ε))) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = A * (2 * ε * u / (u ^ 2 + ε)) := by field_simp

/-- `∫₁^∞ e^{−u/2} du = 2e^{−1/2}`. -/
theorem integral_exp_neg_half_Ioi_one :
    ∫ u in Ioi (1 : ℝ), Real.exp (-u / 2) = 2 * Real.exp (-1 / 2) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 1 (b := 1 / 2) (by norm_num)
  simp only [smul_eq_mul, mul_one] at h
  have e : (fun u : ℝ => Real.exp (-u / 2)) = fun u => Real.exp (-(1 / 2 * u)) := by
    funext u; ring_nf
  rw [e, h, integral_exp_neg_Ioi]
  norm_num

/-- `|∫₁^∞ a(u)(2/√(u² + ε) − 2/u) du| ≤ 3ε` for `ε > 0`. -/
theorem amp_rem_outer_le (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    |∫ u in Ioi (1 : ℝ), a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)| ≤ 3 * ε := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * ε * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * ε))
      (fun w _ => ?_) measurableSet_Ioi
    change 2 * ε * Real.exp (-(1 / 2 : ℝ) * w) = 2 * ε * Real.exp (-w / 2)
    congr 2
    ring
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun u => a u * (2 / Real.sqrt (u ^ 2 + ε) - 2 / u)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, integral_exp_neg_half_Ioi_one]
    have he : 3 / 2 ≤ Real.exp (1 / 2) := by
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h2 : Real.exp (-1 / 2) * 4 ≤ 3 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu : (1 : ℝ) < u := hu
    have hu0 : 0 < u := by linarith
    obtain ⟨g1, g2⟩ := gap_bounds hε hu0
    have ha0 := h.nonneg u
    have hat := h.tail u hu.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha0, abs_of_nonpos (by linarith)]
    have h4 : 2 * ε / (u * (u ^ 2 + ε)) ≤ 2 * ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hu.le (by nlinarith : (1 : ℝ) ≤ u ^ 2 + ε) zero_le_one hu0.le]
    calc a u * -(2 / Real.sqrt (u ^ 2 + ε) - 2 / u) ≤ Real.exp (-u / 2) * (2 * ε) :=
          mul_le_mul hat (by linarith) (by linarith) (Real.exp_pos _).le
      _ = 2 * ε * Real.exp (-u / 2) := by ring

/-! ### Integrability and the splitting of the renormalised constant -/

theorem measurable_ampRenorm (h : AmpData a A) :
    Measurable fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u) :=
  (h.meas.sub (measurable_one.indicator measurableSet_Ioc)).mul (by fun_prop)

theorem integrableOn_ampRenorm_inner (h : AmpData a A) :
    IntegrableOn (fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u)) (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 2 * A)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_ampRenorm h).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hn := h.near u hu
  have hle := h.le_one u
  rw [Real.norm_eq_abs, indicator_of_mem hu, Pi.one_apply, abs_mul, abs_of_nonpos (by linarith),
    abs_of_pos (by positivity)]
  calc -(a u - 1) * (2 / u) ≤ A * u ^ 2 * (2 / u) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * A * u := by field_simp
    _ ≤ 2 * A := by nlinarith [hu.2, h.A_nonneg]

theorem integrableOn_ampRenorm_outer (h : AmpData a A) :
    IntegrableOn (fun u : ℝ => (a u - (Ioc 0 1).indicator 1 u) * (2 / u)) (Ioi 1) := by
  have hmaj : IntegrableOn (fun u : ℝ => 2 * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2)
      (fun w _ => ?_) measurableSet_Ioi
    change 2 * Real.exp (-(1 / 2 : ℝ) * w) = 2 * Real.exp (-w / 2)
    congr 2
    ring
  refine hmaj.mono' (measurable_ampRenorm h).aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  have hm : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hu)
  rw [Real.norm_eq_abs, indicator_of_notMem hm, sub_zero, abs_mul, abs_of_nonneg (h.nonneg u),
    abs_of_pos (by positivity)]
  have h4 : 2 / u ≤ 2 := by rw [div_le_iff₀ hu0]; linarith
  calc a u * (2 / u) ≤ Real.exp (-u / 2) * 2 :=
        mul_le_mul (h.tail u hu.le) h4 (by positivity) (Real.exp_pos _).le
    _ = 2 * Real.exp (-u / 2) := by ring

/-- `R_a = ∫₀¹ (a(u) − 1)·2/u du + ∫₁^∞ a(u)·2/u du`. -/
theorem ampRenorm_split (h : AmpData a A) :
    ampRenorm a = (∫ u in Ioc (0 : ℝ) 1, (a u - 1) * (2 / u)) +
      ∫ u in Ioi (1 : ℝ), a u * (2 / u) := by
  unfold ampRenorm
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (integrableOn_ampRenorm_inner h)
      (integrableOn_ampRenorm_outer h)]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioc fun w hw => by
      rw [indicator_of_mem hw, Pi.one_apply]
  · exact setIntegral_congr_fun measurableSet_Ioi fun w hw => by
      rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero]

theorem measurable_ampJ (h : AmpData a A) (ε : ℝ) :
    Measurable fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε) :=
  (measurable_const.mul h.meas).div (by fun_prop)

theorem integrableOn_ampJ_inner (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε)) (Ioc 0 1) := by
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine Measure.integrableOn_of_bounded (M := 2 / Real.sqrt ε)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_ampJ h ε).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun u _ => ?_
  have hs : Real.sqrt ε ≤ Real.sqrt (u ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  have ha0 := h.nonneg u
  have ha1 := h.le_one u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 2 * a u / Real.sqrt (u ^ 2 + ε) ≤ 2 / Real.sqrt (u ^ 2 + ε) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]; linarith
    _ ≤ 2 / Real.sqrt ε := div_le_div_of_nonneg_left (by norm_num) hs0 hs

theorem integrableOn_ampJ_outer (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun u : ℝ => 2 * a u / Real.sqrt (u ^ 2 + ε)) (Ioi 1) := by
  have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hmaj : IntegrableOn (fun u : ℝ => 2 / Real.sqrt ε * Real.exp (-u / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 / Real.sqrt ε))
      (fun w _ => ?_) measurableSet_Ioi
    change 2 / Real.sqrt ε * Real.exp (-(1 / 2 : ℝ) * w) = 2 / Real.sqrt ε * Real.exp (-w / 2)
    congr 2
    ring
  refine hmaj.mono' (measurable_ampJ h ε).aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu : (1 : ℝ) < u := hu
  have hs : Real.sqrt ε ≤ Real.sqrt (u ^ 2 + ε) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  have ha0 := h.nonneg u
  have hat := h.tail u hu.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 2 * a u / Real.sqrt (u ^ 2 + ε) ≤ 2 * Real.exp (-u / 2) / Real.sqrt ε := by
        rw [div_le_div_iff₀ (by positivity) hs0]
        have : 0 ≤ 2 * Real.exp (-u / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hs this]
    _ = 2 / Real.sqrt ε * Real.exp (-u / 2) := by ring

/-- ★★ **The two-term expansion for a general amplitude**:
`|J_a(ε) − (log(4/ε) + R_a)| ≤ A ε (log(1/ε) + 1) + 4ε` for `0 < ε ≤ 1`. -/
theorem ampJ_two_term (h : AmpData a A) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ a ε - (Real.log (4 / ε) + ampRenorm a)| ≤ A * (ε * (Real.log (1 / ε) + 1)) + 4 * ε := by
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
  have hb2 := amp_rem_inner_le h hε hε1
  have hb3 := amp_rem_outer_le h hε
  have hsplit := ampRenorm_split h
  rw [hJ, hR1, hR2, hE, hsplit]
  rw [abs_le] at hb2 hb3 ⊢
  have hA := h.A_nonneg
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hAε : 0 ≤ A * (ε * (Real.log (1 / ε) + 1)) := by positivity
  constructor <;> nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2]

end Grammar
