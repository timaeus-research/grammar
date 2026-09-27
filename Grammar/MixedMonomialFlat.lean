/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatAllOrders

/-!
# The mixed monomial `x²y⁶` with the flat prior: two exponents, no logarithms, to all orders

The law of `t = x y³` under Lebesgue measure on `[−1, 1]²` has density `|t|^{−2/3} − 1` on
`0 < |t| < 1` (★★ `lintegral_square_cube`), so that

  `∫_{[−1,1]²} e^{−N x²y⁶} dx dy = Γ(1/6) N^{−1/6} − √π N^{−1/2} + R_N`,  `0 ≤ R_N ≤ e^{−N}/N`

(★★★ `mixed_flat_allOrders`, `mixed_flat_remainder_le`): the two walls `x = 0` and `y = 0` of the
mixed monomial carry the two exponents `1/6` and `1/2`, both simple, with nothing in between and
an exponentially small remainder — the three-tier example of examples_slop §2 in closed form.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-- The density of `t = x y³` under Lebesgue measure on the square. -/
noncomputable def mixedDensity (t : ℝ) : ℝ≥0∞ :=
  if 0 < |t| ∧ |t| < 1 then ENNReal.ofReal (|t| ^ (-(2 / 3) : ℝ) - 1) else 0

/-- `∫_r^1 y^{−3} dy = (r^{−2} − 1)/2` for `0 < r ≤ 1`, as a lower integral. -/
theorem lintegral_Icc_inv_cube {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ y in Icc r 1, ENNReal.ofReal (|y| ^ (-3 : ℝ)) = ENNReal.ofReal ((r ^ (-2 : ℝ) - 1) / 2) := by
  have hcont : ContinuousOn (fun y : ℝ => y ^ (-3 : ℝ)) (Icc r 1) := by
    refine ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl (hr.trans_le hy.1).ne'
  have hnn : ∀ y ∈ Icc r 1, 0 ≤ y ^ (-3 : ℝ) := fun y hy =>
    Real.rpow_nonneg (hr.le.trans hy.1) _
  rw [setLIntegral_congr_fun measurableSet_Icc (g := fun y => ENNReal.ofReal (y ^ (-3 : ℝ)))
    (fun y hy => by rw [abs_of_pos (hr.trans_le hy.1)]),
    ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (ae_restrict_of_forall_mem measurableSet_Icc hnn)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr1,
    integral_rpow (Or.inr ⟨by norm_num, fun h => ?_⟩)]
  · rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.one_rpow]
    ring
  · rw [uIcc_of_le hr1] at h
    exact absurd h.1 (not_le.mpr hr)

/-- The same on the reflected interval `[−1, −r]`. -/
theorem lintegral_Icc_inv_cube_neg {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ y in Icc (-1) (-r), ENNReal.ofReal (|y| ^ (-3 : ℝ)) =
      ENNReal.ofReal ((r ^ (-2 : ℝ) - 1) / 2) := by
  rw [← lintegral_Icc_inv_cube hr hr1]
  have := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (s := Icc r 1) measurableSet_Icc
    (f := fun y => ENNReal.ofReal (|y| ^ (-3 : ℝ))) (by fun_prop)
  rw [show (fun y : ℝ => -y) ⁻¹' Icc r 1 = Icc (-1) (-r) by
    ext y; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith]
    at this
  simp only [abs_neg] at this
  exact this

/-- The fibre of `(x, y) ↦ x y³` over `w` with `0 < |w| ≤ 1`, on the `y`-line inside the square:
`{|y| ≥ |w|^{1/3}}` together with the null point `0`. -/
theorem cube_fibre {w : ℝ} (hw : w ≠ 0) (hw1 : |w| ≤ 1) :
    {y | y ∈ Icc (-1 : ℝ) 1 ∧ w / y ^ 3 ∈ Icc (-1 : ℝ) 1} =
      Icc (-1) (-(|w| ^ (1 / 3 : ℝ))) ∪ Icc (|w| ^ (1 / 3 : ℝ)) 1 ∪ {0} := by
  set r := |w| ^ (1 / 3 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (abs_pos.mpr hw) _
  have hr3 : r ^ 3 = |w| := by
    rw [hr, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow (abs_nonneg w) (by norm_num)]
  have hr1 : r ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < r ^ 3 := one_lt_pow₀ h (by norm_num)
    linarith
  ext y
  simp only [mem_ofPred_eq, mem_Icc, mem_union, mem_singleton_iff]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have key : (-1 ≤ w / y ^ 3 ∧ w / y ^ 3 ≤ 1) ↔ r ≤ |y| := by
      rw [← abs_le, abs_div, abs_pow, div_le_one (pow_pos (abs_pos.mpr hy) 3), ← hr3]
      exact pow_le_pow_iff_left₀ hr0.le (abs_nonneg y) (by norm_num)
    rw [key]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases le_or_gt 0 y with hy0 | hy0
      · rw [abs_of_nonneg hy0] at h3
        exact Or.inl (Or.inr ⟨h3, h2⟩)
      · rw [abs_of_neg hy0] at h3
        exact Or.inl (Or.inl ⟨h1, by linarith⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h)
      · refine ⟨⟨h1, by linarith⟩, ?_⟩
        rw [abs_of_neg (by linarith)]
        linarith
      · refine ⟨⟨by linarith, h2⟩, ?_⟩
        rw [abs_of_pos (hr0.trans_le h1)]
        exact h1
      · exact absurd h hy

/-- Over `|w| > 1` the fibre is the null point `0`. -/
theorem cube_fibre_empty {w : ℝ} (hw1 : 1 < |w|) :
    {y | y ∈ Icc (-1 : ℝ) 1 ∧ w / y ^ 3 ∈ Icc (-1 : ℝ) 1} = {0} := by
  ext y
  simp only [mem_ofPred_eq, mem_Icc, mem_singleton_iff]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exfalso
      have hy3 : 0 < |y| ^ 3 := pow_pos (abs_pos.mpr hy) 3
      have : |w| ≤ |y| ^ 3 := by
        rw [← abs_pow, ← div_le_one (abs_pos.mpr (pow_ne_zero 3 hy)), ← abs_div]
        exact abs_le.mpr ⟨h3, h4⟩
      have : |y| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg y) (abs_le.mpr ⟨h1, h2⟩)
      linarith
    · intro h; exact absurd h hy

/-- The fibre integral of `|y|^{−3}` is the density. -/
theorem lintegral_cube_fibre {w : ℝ} (hw : w ≠ 0) :
    ∫⁻ y in {y | y ∈ Icc (-1 : ℝ) 1 ∧ w / y ^ 3 ∈ Icc (-1 : ℝ) 1},
        ENNReal.ofReal (|y| ^ (-3 : ℝ)) = mixedDensity w := by
  have hsing : ∫⁻ y in ({0} : Set ℝ), ENNReal.ofReal (|y| ^ (-3 : ℝ)) = 0 := by
    rw [lintegral_singleton, Real.volume_singleton, mul_zero]
  rcases le_or_gt |w| 1 with hw1 | hw1
  · set r := |w| ^ (1 / 3 : ℝ) with hr
    have hr0 : 0 < r := Real.rpow_pos_of_pos (abs_pos.mpr hw) _
    have hr3 : r ^ 3 = |w| := by
      rw [hr, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.rpow_inv_natCast_pow (abs_nonneg w) (by norm_num)]
    have hr1 : r ≤ 1 := by
      by_contra h
      push Not at h
      have : 1 < r ^ 3 := one_lt_pow₀ h (by norm_num)
      linarith
    have hd1 : Disjoint (Icc (-1) (-r)) (Icc r 1) := by
      rw [Set.disjoint_left]
      intro y h1 h2
      linarith [h1.2, h2.1]
    have hd2 : Disjoint (Icc (-1) (-r) ∪ Icc r 1) ({0} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      rintro (h | h)
      · linarith [h.2]
      · linarith [h.1]
    rw [cube_fibre hw hw1, lintegral_union (measurableSet_singleton 0) hd2,
      lintegral_union measurableSet_Icc hd1, hsing, add_zero, lintegral_Icc_inv_cube_neg hr0 hr1,
      lintegral_Icc_inv_cube hr0 hr1, mixedDensity]
    have hr2 : r ^ (-2 : ℝ) = |w| ^ (-(2 / 3) : ℝ) := by
      rw [hr, ← Real.rpow_mul (abs_nonneg w)]
      norm_num
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · rw [if_pos ⟨abs_pos.mpr hw, hlt⟩, ← ENNReal.ofReal_add, hr2]
      · congr 1; ring
      · rw [hr2]
        have : 1 ≤ |w| ^ (-(2 / 3) : ℝ) := by
          rw [Real.rpow_neg (abs_nonneg w), one_le_inv₀ (Real.rpow_pos_of_pos (abs_pos.mpr hw) _)]
          exact Real.rpow_le_one (abs_nonneg w) hw1 (by norm_num)
        linarith
      · rw [hr2]
        have : 1 ≤ |w| ^ (-(2 / 3) : ℝ) := by
          rw [Real.rpow_neg (abs_nonneg w), one_le_inv₀ (Real.rpow_pos_of_pos (abs_pos.mpr hw) _)]
          exact Real.rpow_le_one (abs_nonneg w) hw1 (by norm_num)
        linarith
    · have hr' : r = 1 := by rw [hr, heq, Real.one_rpow]
      rw [if_neg (fun h => absurd h.2 (not_lt.mpr heq.ge)), hr', Real.one_rpow]
      simp
  · rw [cube_fibre_empty hw1, hsing, mixedDensity,
      if_neg (fun h => absurd h.2 (not_lt.mpr hw1.le))]

/-- ★★ The law of `t = x y³` under Lebesgue measure on the square: for every measurable `Ψ ≥ 0`,
`∫_{[−1,1]²} Ψ(x y³) dx dy = ∫ Ψ(t) · (|t|^{−2/3} − 1) 1_{0<|t|<1} dt`. -/
theorem lintegral_square_cube {Ψ : ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Ψ (w.1 * w.2 ^ 3) = ∫⁻ t, Ψ t * mixedDensity t := by
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by rw [ae_iff]; simp
  have hΨ2 : Measurable fun w : ℝ × ℝ => Ψ (w.1 * w.2 ^ 3) := by fun_prop
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal |p.1 ^ 3|⁻¹ *
      ((Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (p.2 / p.1 ^ 3) * Ψ p.2) := by
    have e : (fun p : ℝ × ℝ => (Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (p.2 / p.1 ^ 3)) =
        fun p => if p.2 / p.1 ^ 3 ∈ Icc (-1 : ℝ) 1 then 1 else 0 := by
      funext p; simp [indicator_apply]
    refine ((measurable_fst.pow_const 3).abs.inv.ennreal_ofReal).mul (Measurable.mul ?_ ?_)
    · rw [e]
      exact Measurable.ite (measurableSet_Icc.preimage
        (measurable_snd.div (measurable_fst.pow_const 3))) measurable_const measurable_const
    · exact hΨ.comp measurable_snd
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hΨ2.aemeasurable]
  calc ∫⁻ y in Icc (-1 : ℝ) 1, ∫⁻ x in Icc (-1 : ℝ) 1, Ψ (x * y ^ 3)
      = ∫⁻ y in Icc (-1 : ℝ) 1, ∫⁻ w, ENNReal.ofReal |y ^ 3|⁻¹ *
          ((Icc (-1 : ℝ) 1).indicator 1 (w / y ^ 3) * Ψ w) := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with y hy
        have hy3 : y ^ 3 ≠ 0 := pow_ne_zero 3 hy
        have hg : Measurable fun w : ℝ =>
            (Icc (-1 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (w / y ^ 3) * Ψ w :=
          ((measurable_const.indicator measurableSet_Icc).comp (measurable_id.div_const _)).mul hΨ
        have e : ∫⁻ x in Icc (-1 : ℝ) 1, Ψ (x * y ^ 3) = ∫⁻ x in Icc (-1 : ℝ) 1, Ψ (y ^ 3 * x) :=
          setLIntegral_congr_fun measurableSet_Icc fun x _ => by rw [mul_comm]
        rw [e, lintegral_Icc_mul_left (γ := 1) (δ := 1) hΨ hy3, ← lintegral_const_mul _ hg]
    _ = ∫⁻ w, ∫⁻ y in Icc (-1 : ℝ) 1, ENNReal.ofReal |y ^ 3|⁻¹ *
          ((Icc (-1 : ℝ) 1).indicator 1 (w / y ^ 3) * Ψ w) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ w, Ψ w * ∫⁻ y in {y | y ∈ Icc (-1 : ℝ) 1 ∧ w / y ^ 3 ∈ Icc (-1 : ℝ) 1},
          ENNReal.ofReal (|y| ^ (-3 : ℝ)) := by
        refine lintegral_congr fun w => ?_
        have hset : MeasurableSet {y | y ∈ Icc (-1 : ℝ) 1 ∧ w / y ^ 3 ∈ Icc (-1 : ℝ) 1} :=
          measurableSet_Icc.inter (measurableSet_Icc.preimage (measurable_const.div
            (measurable_id.pow_const 3)))
        have hf : Measurable fun y : ℝ => ENNReal.ofReal (|y| ^ (-3 : ℝ)) := by fun_prop
        rw [← lintegral_const_mul _ hf, ← lintegral_indicator measurableSet_Icc,
          ← lintegral_indicator hset]
        refine lintegral_congr fun y => ?_
        have e3 : ENNReal.ofReal |y ^ 3|⁻¹ = ENNReal.ofReal (|y| ^ (-3 : ℝ)) := by
          rw [abs_pow, Real.rpow_neg (abs_nonneg y),
            show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        simp only [indicator_apply, mem_ofPred_eq, Pi.one_apply, e3]
        split_ifs with h1 h2 h2 <;> simp_all [mul_comm]
    _ = ∫⁻ w, Ψ w * mixedDensity w := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with w hw
        rw [lintegral_cube_fibre hw]

/-- ★★★ **The mixed monomial `x²y⁶` with flat prior, to all orders**: for `N > 0`,

  ∫_{[−1,1]²} e^{−N x²y⁶} dx dy = Γ(1/6) N^{−1/6} − √π N^{−1/2} + 2∫_1^∞ e^{−Nt²}(1 − t^{−2/3}) dt`. -/
theorem mixed_flat_allOrders {N : ℝ} (hN : 0 < N) :
    ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Real.exp (-N * (w.1 * w.2 ^ 3) ^ 2) =
      Real.Gamma (1 / 6) * N ^ (-(1 / 6) : ℝ) - Real.sqrt Real.pi / Real.sqrt N +
        2 * ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2) * (1 - t ^ (-(2 / 3) : ℝ)) := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
  set G : ℝ → ℝ := fun t => Real.exp (-N * t ^ 2) * (|t| ^ (-(2 / 3) : ℝ) - 1) with hG
  set F : ℝ → ℝ := fun t => Real.exp (-N * t ^ 2) * (t ^ (-(2 / 3) : ℝ) - 1) with hF
  have hGeven : ∀ t, G (-t) = G t := by intro t; simp only [hG, neg_sq, abs_neg]
  have hGm : Measurable G := by rw [hG]; fun_prop
  have hGae : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 1)), 0 ≤ G t := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    refine mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ?_)
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr ht) (abs_lt.mpr hmem).le
      (by norm_num)
  -- C1: the reduction to the polar distribution
  have hl := lintegral_square_cube (Ψ := fun t => ENNReal.ofReal (Real.exp (-N * t ^ 2)))
    (by fun_prop)
  have hR : ∫⁻ t, ENNReal.ofReal (Real.exp (-N * t ^ 2)) * mixedDensity t =
      ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (G t) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [mixedDensity, indicator_apply]
    by_cases h : 0 < |t| ∧ |t| < 1
    · have hmem : t ∈ Ioo (-1 : ℝ) 1 := by rw [mem_Ioo, ← abs_lt]; exact h.2
      rw [if_pos h, if_pos hmem, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    · rw [if_neg h, mul_zero]
      have hnot : t ∉ Ioo (-1 : ℝ) 1 := fun hmem => h ⟨abs_pos.mpr ht, abs_lt.mpr hmem⟩
      rw [if_neg hnot]
  rw [hR] at hl
  have hbox : IntegrableOn (fun w : ℝ × ℝ => Real.exp (-N * (w.1 * w.2 ^ 3) ^ 2))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    (by fun_prop : Continuous fun w : ℝ × ℝ =>
      Real.exp (-N * (w.1 * w.2 ^ 3) ^ 2)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hboxnn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)]
      fun w : ℝ × ℝ => Real.exp (-N * (w.1 * w.2 ^ 3) ^ 2) :=
    ae_of_all _ fun w => (Real.exp_pos _).le
  have hGIo : IntegrableOn G (Ioo (-1 : ℝ) 1) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have : ∫⁻ t in Ioo (-1 : ℝ) 1, ‖G t‖ₑ = ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (G t) :=
      lintegral_congr_ae (hGae.mono fun t ht => Real.enorm_eq_ofReal ht)
    rw [this, ← hl, ← ofReal_integral_eq_lintegral_ofReal hbox hboxnn]
    exact ENNReal.ofReal_lt_top
  have hred : ∫ w in Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, Real.exp (-N * (w.1 * w.2 ^ 3) ^ 2) =
      ∫ t in Ioo (-1 : ℝ) 1, G t := by
    rw [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hboxnn)
      (integral_nonneg_of_ae hGae), ofReal_integral_eq_lintegral_ofReal hbox hboxnn,
      ofReal_integral_eq_lintegral_ofReal hGIo hGae, hl]
  -- C2: symmetry
  have hsym : ∫ t in Ioo (-1 : ℝ) 1, G t = 2 * ∫ t in (0 : ℝ)..1, G t := by
    have hGI : IntervalIntegrable G volume (-1) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), IntegrableOn,
        ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact hGIo
    have h1 : IntervalIntegrable G volume (-1) 0 :=
      hGI.mono_set (uIcc_subset_uIcc_left (by norm_num [uIcc_of_le]))
    have h2 : IntervalIntegrable G volume 0 1 :=
      hGI.mono_set (uIcc_subset_uIcc_right (by norm_num [uIcc_of_le]))
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have : ∫ t in (-1 : ℝ)..0, G t = ∫ t in (0 : ℝ)..1, G t := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, show (0 : ℝ) = -(0 : ℝ) by norm_num,
        ← intervalIntegral.integral_comp_neg]
      simp only [hGeven, neg_zero]
    rw [this]; ring
  -- C3: on `(0, 1]` the density is `t^{−2/3} − 1`; split `∫_0^1 = ∫_0^∞ − ∫_1^∞`
  have hpos : ∫ t in (0 : ℝ)..1, G t = ∫ t in Ioc (0 : ℝ) 1, F t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [hG, hF]; rw [abs_of_pos ht.1]
  have h1 := (integrable_rpow_mul_exp_neg_mul_sq hN (s := -(2 / 3)) (by norm_num)).integrableOn
    (s := Ioi (0 : ℝ))
  have h2 := (integrable_exp_neg_mul_sq hN).integrableOn (s := Ioi (0 : ℝ))
  have hFint : IntegrableOn F (Ioi 0) :=
    (h1.sub h2).congr_fun (fun t _ => by simp only [hF, Pi.sub_apply]; ring) measurableSet_Ioi
  have hsplit : ∫ t in Ioc (0 : ℝ) 1, F t =
      (∫ t in Ioi (0 : ℝ), F t) - ∫ t in Ioi (1 : ℝ), F t := by
    have hu := setIntegral_union (f := F) (μ := volume) (s := Ioc (0 : ℝ) 1) (t := Ioi 1)
      Ioc_disjoint_Ioi_same measurableSet_Ioi (hFint.mono_set Ioc_subset_Ioi_self)
      (hFint.mono_set (Ioi_subset_Ioi one_pos.le))
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
    rw [hu]; ring
  have hval : ∫ t in Ioi (0 : ℝ), F t =
      Real.Gamma (1 / 6) * N ^ (-(1 / 6) : ℝ) / 2 - Real.sqrt (Real.pi / N) / 2 := by
    have e : ∫ t in Ioi (0 : ℝ), F t = ∫ t in Ioi (0 : ℝ),
        (t ^ (-(2 / 3) : ℝ) * Real.exp (-N * t ^ 2) - Real.exp (-N * t ^ 2)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp only [hF]; ring
    rw [e, integral_sub h1 h2, integral_gaussian_Ioi]
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := -(2 / 3)) (b := N) two_pos
      (by norm_num) hN
    have hfun : (fun t : ℝ => t ^ (-(2 / 3) : ℝ) * Real.exp (-N * t ^ 2)) =
        fun t => t ^ (-(2 / 3) : ℝ) * Real.exp (-N * t ^ (2 : ℝ)) := by
      funext t; rw [Real.rpow_two]
    rw [hfun, h, show (-(2 / 3) + 1) / 2 = (1 / 6 : ℝ) by norm_num,
      show -(-(2 / 3) + 1) / 2 = (-(1 / 6) : ℝ) by norm_num]
    ring
  have hneg : ∫ t in Ioi (1 : ℝ), F t =
      -∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2) * (1 - t ^ (-(2 / 3) : ℝ)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hF]; ring
  rw [hred, hsym, hpos, hsplit, hval, hneg, Real.sqrt_div Real.pi_pos.le]
  ring

/-- The remainder of `mixed_flat_allOrders` is nonnegative and at most `e^{−N}/(2N)`. -/
theorem mixed_flat_remainder_le {N : ℝ} (hN : 0 < N) :
    0 ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2) * (1 - t ^ (-(2 / 3) : ℝ)) ∧
      ∫ t in Ioi (1 : ℝ), Real.exp (-N * t ^ 2) * (1 - t ^ (-(2 / 3) : ℝ)) ≤
        Real.exp (-N) / (2 * N) := by
  have h1 := (integrable_rpow_mul_exp_neg_mul_sq hN (s := -(2 / 3)) (by norm_num)).integrableOn
    (s := Ioi (1 : ℝ))
  have h2 := (integrable_exp_neg_mul_sq hN).integrableOn (s := Ioi (1 : ℝ))
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ 2) * (1 - t ^ (-(2 / 3) : ℝ)))
      (Ioi 1) :=
    (h2.sub h1).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hint' : IntegrableOn (fun t : ℝ => t * Real.exp (-N * t ^ 2)) (Ioi 1) :=
    ((integrable_rpow_mul_exp_neg_mul_sq hN (s := 1) (by norm_num)).integrableOn
      (s := Ioi (1 : ℝ))).congr_fun (fun x _ => by simp only [Real.rpow_one]) measurableSet_Ioi
  have hderiv : ∀ t ∈ Ioi (1 : ℝ),
      HasDerivAt (fun t => -Real.exp (-N * t ^ 2) / (2 * N)) (t * Real.exp (-N * t ^ 2)) t := by
    intro t _
    have h := (hasDerivAt_pow 2 t).const_mul (-N)
    have h2 := (Real.hasDerivAt_exp _).comp t h
    have h3 := (h2.neg).div_const (2 * N)
    refine h3.congr_deriv ?_
    field_simp
    ring
  have htend : Filter.Tendsto (fun t : ℝ => -Real.exp (-N * t ^ 2) / (2 * N)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -N * t ^ 2) Filter.atTop Filter.atBot :=
      (Filter.tendsto_pow_atTop two_ne_zero : Filter.Tendsto (fun t : ℝ => t ^ 2)
        Filter.atTop Filter.atTop).const_mul_atTop_of_neg (neg_neg_of_pos hN)
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.neg).div_const (2 * N)
    simpa using h3
  have hval : ∫ t in Ioi (1 : ℝ), t * Real.exp (-N * t ^ 2) = Real.exp (-N) / (2 * N) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop : Continuous fun t : ℝ =>
      -Real.exp (-N * t ^ 2) / (2 * N)).continuousWithinAt hderiv hint' htend]
    ring_nf
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    refine mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ?_)
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ht) (by norm_num)
  · rw [← hval]
    refine setIntegral_mono_on hint hint' measurableSet_Ioi fun t ht => ?_
    have ht1 : (1 : ℝ) < t := ht
    have : 0 ≤ t ^ (-(2 / 3) : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Grammar
