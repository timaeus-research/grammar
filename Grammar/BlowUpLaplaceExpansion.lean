/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AmplitudeJ

/-!
# The two-term expansion of the blow-up model's partition function

The blow-up example of the note (examples_slop §4): `K = x²(x² + y²)/2` with the Gaussian prior
`e^{−|w|²/2}` on `ℝ²`,

  `Z_N = ∫_{ℝ²} e^{−N x²(x² + y²)/2} e^{−(x² + y²)/2} dx dy`  (`blowupLaplace`).

The Gaussian integral in `y` at fixed `x` gives the exact reduction
`Z_N = √(2π) ∫_ℝ e^{−N x⁴/2} e^{−x²/2}/√(1 + N x²) dx` (`blowupLaplace_eq_integral`); the scaling
`x = u/m`, `N = m⁴`, turns it into `√(2π)/m² · J_a(1/m²)` with the amplitude
`a_m(u) = e^{−u⁴/2} e^{−u²/2m²}` (`blowupLaplace_eq_ampJ`).  The engine of
`Grammar.AmplitudeJ` then gives, with the renormalised constant
`R_∞ = ∫₀^∞ (e^{−u⁴/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/2` (`ampRenorm_blowAmpInf`, by the
substitutions `y = u⁴` and `y = 2v` from `Grammar.RenormalisedExpIntegral`) and the comparison
`|R_{a_m} − R_∞| ≤ 2/m²`,

  `|Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 7)/N`  for `N ≥ 1`
  (★★★ `blowupLaplace_two_term_bound`),

hence `Z_N = √(π/2)(log N + 5 log 2 − γ)/√N + O(N^{−1} log N)` (★★★ `blowupLaplace_two_term`):
the note's coefficients `c_{½,1} = √(π/2)`, `c_{½,0} = √(π/2)(5 log 2 − γ)` of
eq. (blowup_population), proved directly from the integral rather than through the Gamma transform
of the Laurent data of `Grammar.BlowUpLaurent` (Astra round-6 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The blow-up model's partition function with the Gaussian prior `e^{−|w|²/2}`. -/
noncomputable def blowupLaplace (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
    Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)

/-- The amplitude `a_m(u) = e^{−u⁴/2} e^{−u²/2m²}`. -/
noncomputable def blowAmp (m u : ℝ) : ℝ := Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))

/-- The limiting amplitude `e^{−u⁴/2}`. -/
noncomputable def blowAmpInf (u : ℝ) : ℝ := Real.exp (-u ^ 4 / 2)

/-! ### The conditional reduction -/

theorem integrable_blowupLaplace (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) := by
  have hg : Integrable fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    congr 1
    ring
  have hprod : Integrable (fun w : ℝ × ℝ => Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
      (volume.prod volume) := hg.mul_prod hg
  rw [Measure.volume_eq_prod]
  refine hprod.mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        nlinarith [mul_nonneg hN (by positivity : 0 ≤ w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2))])
    have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
        Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : 0 ≤ Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by positivity
    calc Real.exp (-N * (w.1 ^ 2 * (w.1 ^ 2 + w.2 ^ 2)) / 2) *
          (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
        ≤ 1 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by ring

/-- ★★ **The exact conditional reduction**:
`Z_N = √(2π) ∫_ℝ e^{−N x⁴/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`. -/
theorem blowupLaplace_eq_integral {N : ℝ} (hN : 0 ≤ N) :
    blowupLaplace N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + N * x ^ 2) := by
  unfold blowupLaplace
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_blowupLaplace N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hpt : ∀ y : ℝ, Real.exp (-N * (x ^ 2 * (x ^ 2 + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2) =
      (Real.exp (-N * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2)) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_exp_cond hc]
  have hsq : Real.sqrt (2 * Real.pi / (1 + N * x ^ 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (1 + N * x ^ 2) := Real.sqrt_div' _ hc.le
  rw [hsq]
  ring

/-! ### Scaling to the amplitude form -/

theorem blowAmp_eq (m u : ℝ) : blowAmp m u = Real.exp (-u ^ 4 / 2 + -u ^ 2 / (2 * m ^ 2)) := by
  unfold blowAmp; rw [Real.exp_add]

/-- ★★ `Z_{m⁴} = √(2π)/m² · J_{a_m}(1/m²)` for `m > 0`. -/
theorem blowupLaplace_eq_ampJ {m : ℝ} (hm : 0 < m) :
    blowupLaplace (m ^ 4) = Real.sqrt (2 * Real.pi) / m ^ 2 * ampJ (blowAmp m) (1 / m ^ 2) := by
  rw [blowupLaplace_eq_integral (by positivity)]
  set f : ℝ → ℝ := fun x =>
    Real.exp (-m ^ 4 * x ^ 4 / 2) * Real.exp (-x ^ 2 / 2) / Real.sqrt (1 + m ^ 4 * x ^ 2) with hf
  have h1 : ∫ x : ℝ, f x = 2 * ∫ x in Ioi (0 : ℝ), f x := by
    rw [← integral_comp_abs (f := f)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [show |x| ^ 4 = x ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul],
      sq_abs]
  have hm1 : 0 < 1 / m := by positivity
  have h2 : ∫ x in Ioi (0 : ℝ), f x = m⁻¹ * ∫ u in Ioi (0 : ℝ), f (1 / m * u) := by
    rw [integral_comp_mul_left_Ioi f 0 hm1, mul_zero, smul_eq_mul, one_div, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ hm.ne', one_mul]
  have h3 : ∀ u ∈ Ioi (0 : ℝ), f (1 / m * u) =
      m⁻¹ * (blowAmp m u / Real.sqrt (u ^ 2 + 1 / m ^ 2)) := by
    intro u _
    simp only [hf]
    have e1 : -m ^ 4 * (1 / m * u) ^ 4 / 2 = -u ^ 4 / 2 := by field_simp
    have e2 : -(1 / m * u) ^ 2 / 2 = -u ^ 2 / (2 * m ^ 2) := by field_simp
    have e3 : 1 + m ^ 4 * (1 / m * u) ^ 2 = m ^ 2 * (u ^ 2 + 1 / m ^ 2) := by field_simp; ring
    rw [e1, e2, e3, Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
    unfold blowAmp
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  unfold ampJ
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  field_simp

/-! ### The amplitude data -/

theorem blowAmp_ampData {m : ℝ} (hm : 1 ≤ m) : AmpData (blowAmp m) 1 where
  meas := by unfold blowAmp; fun_prop
  nonneg u := by unfold blowAmp; positivity
  le_one u := by
    unfold blowAmp
    have hm0 : 0 < m := by linarith
    calc Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ 1 * 1 :=
          mul_le_mul (Real.exp_le_one_iff.2 (by nlinarith [pow_nonneg (sq_nonneg u) 2]))
            (Real.exp_le_one_iff.2 (by
              have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
              linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  A_nonneg := zero_le_one
  near u hu := by
    rw [blowAmp_eq]
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have hdiv : u ^ 2 / (2 * m ^ 2) ≤ u ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg u]
    have := Real.add_one_le_exp (-u ^ 4 / 2 + -u ^ 2 / (2 * m ^ 2))
    have e : -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) := by ring
    rw [e] at this ⊢
    linarith
  tail u hu := by
    unfold blowAmp
    have hm0 : 0 < m := by linarith
    calc Real.exp (-u ^ 4 / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ Real.exp (-u ^ 4 / 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by
            have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
            linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le
      _ ≤ Real.exp (-u / 2) := by
          rw [mul_one]
          exact Real.exp_le_exp.2 (by
            nlinarith [sq_nonneg u, sq_nonneg (u - 1), sq_nonneg (u ^ 2 - 1)])

theorem blowAmpInf_ampData : AmpData blowAmpInf (1 / 2) where
  meas := by unfold blowAmpInf; fun_prop
  nonneg u := by unfold blowAmpInf; positivity
  le_one u := by
    unfold blowAmpInf
    exact Real.exp_le_one_iff.2 (by nlinarith [pow_nonneg (sq_nonneg u) 2])
  A_nonneg := by norm_num
  near u hu := by
    unfold blowAmpInf
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hu4 : u ^ 4 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
    have := Real.add_one_le_exp (-u ^ 4 / 2)
    linarith
  tail u hu := by
    unfold blowAmpInf
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg u, sq_nonneg (u - 1), sq_nonneg (u ^ 2 - 1)])

/-! ### The renormalised constant of the limiting amplitude -/

/-- The renormalised exponential integrand `(e^{−v} − 1_{(0,1]}(v))/v` is integrable on `(0, ∞)`. -/
theorem integrableOn_renormalised_exp_inv :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v) (Ioi 0) := by
  have hmeas : Measurable fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v :=
    ((by fun_prop : Measurable fun v : ℝ => Real.exp (-v)).sub
      (measurable_one.indicator measurableSet_Ioc)).div measurable_id
  have h1 : IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v)
      (Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 1)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun v hv => ?_
    have hv0 : 0 < v := hv.1
    have he1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-v)
    rw [Real.norm_eq_abs, indicator_of_mem hv, Pi.one_apply, abs_div, abs_of_pos hv0,
      abs_of_nonpos (by linarith), div_le_one hv0]
    linarith
  have h2 : IntegrableOn (fun v : ℝ => (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v) (Ioi 1) := by
    have hmaj : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 1) := by
      refine IntegrableOn.congr_fun (s := Ioi 1) (exp_neg_integrableOn_Ioi 1 one_pos)
        (fun w _ => ?_) measurableSet_Ioi
      simp
    refine hmaj.mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun v hv => ?_
    have hv : (1 : ℝ) < v := hv
    rw [Real.norm_eq_abs, indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hv)), sub_zero,
      abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
    nlinarith [Real.exp_pos (-v)]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

/-- `∫₀^∞ (e^{−v} − 1_{(0,1/2]}(v))/v dv = log 2 − γ`. -/
theorem integral_renormalised_half :
    ∫ v in Ioi (0 : ℝ), (Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v =
      Real.log 2 - Real.eulerMascheroniConstant := by
  have e : ∀ v ∈ Ioi (0 : ℝ), (Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v =
      (Real.exp (-v) - (Ioc 0 1).indicator 1 v) / v +
        (Ioc (1 / 2) 1).indicator (fun v => v⁻¹) v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    by_cases h1 : v ≤ 1 / 2
    · have hm1 : v ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hv0, h1⟩
      have hm2 : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, by linarith⟩
      have hm3 : v ∉ Ioc (1 / 2 : ℝ) 1 := fun h => absurd h.1 (not_lt.2 h1)
      rw [indicator_of_mem hm1, indicator_of_mem hm2, indicator_of_notMem hm3, add_zero]
    · have h1' := not_le.1 h1
      have hm1 : v ∉ Ioc (0 : ℝ) (1 / 2) := fun h => absurd h.2 (not_le.2 h1')
      rw [indicator_of_notMem hm1]
      by_cases h2 : v ≤ 1
      · have hm2 : v ∈ Ioc (0 : ℝ) 1 := ⟨hv0, h2⟩
        have hm3 : v ∈ Ioc (1 / 2 : ℝ) 1 := ⟨h1', h2⟩
        rw [indicator_of_mem hm2, indicator_of_mem hm3, Pi.one_apply, sub_zero]
        field_simp
        ring
      · have h2' := not_le.1 h2
        have hm2 : v ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        have hm3 : v ∉ Ioc (1 / 2 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        rw [indicator_of_notMem hm2, indicator_of_notMem hm3, add_zero]
  have hind : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator fun v => v⁻¹) (Ioi 0) := by
    have : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc (1 / 2) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
      exact intervalIntegral.intervalIntegrable_inv (fun x hx => by
        rw [uIcc_of_le (by norm_num)] at hx; exact ne_of_gt (by linarith [hx.1])) continuousOn_id
    exact (this.integrable_indicator measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_add integrableOn_renormalised_exp_inv hind,
    integral_renormalised_exp_inv, setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc (1 / 2) 1 = Ioc (1 / 2) 1 from
      inter_eq_right.2 fun v hv => show (0 : ℝ) < v by linarith [hv.1],
    ← intervalIntegral.integral_of_le (by norm_num), integral_inv_of_pos (by norm_num) one_pos]
  norm_num
  ring

/-- ★★ `R_∞ = ∫₀^∞ (e^{−u⁴/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/2`. -/
theorem ampRenorm_blowAmpInf :
    ampRenorm blowAmpInf = (Real.log 2 - Real.eulerMascheroniConstant) / 2 := by
  unfold ampRenorm blowAmpInf
  -- the substitution `y = u⁴`
  set g : ℝ → ℝ := fun y => (Real.exp (-y / 2) - (Ioc 0 1).indicator 1 y) / (2 * y) with hg
  have h4 := integral_comp_rpow_Ioi_of_pos (g := g) (p := 4) (by norm_num)
  have e4 : ∀ u ∈ Ioi (0 : ℝ), (4 * u ^ ((4 : ℝ) - 1)) • g (u ^ (4 : ℝ)) =
      (Real.exp (-u ^ 4 / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (u ^ 4) = (Ioc 0 1).indicator 1 u := by
      by_cases h : u ≤ 1
      · have hm : u ^ 4 ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hu0.le h⟩
        have hm' : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, h⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have h' := not_le.1 h
        have hm : u ^ 4 ∉ Ioc (0 : ℝ) 1 := fun hm =>
          absurd hm.2 (not_le.2 (one_lt_pow₀ h' (by norm_num)))
        have hm' : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 h')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg, smul_eq_mul]
    rw [show ((4 : ℝ) - 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hI]
    field_simp
    ring
  rw [← setIntegral_congr_fun measurableSet_Ioi e4, h4]
  -- the scaling `y = 2v`
  have h2 := integral_comp_mul_left_Ioi g 0 (b := 2) two_pos
  rw [mul_zero, smul_eq_mul] at h2
  have e2 : ∀ v ∈ Ioi (0 : ℝ), g (2 * v) =
      (1 / 4) * ((Real.exp (-v) - (Ioc 0 (1 / 2)).indicator 1 v) / v) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (2 * v) = (Ioc 0 (1 / 2)).indicator 1 v := by
      by_cases h : v ≤ 1 / 2
      · have hm : 2 * v ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
        have hm' : v ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hv0, h⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have h' := not_le.1 h
        have hm : 2 * v ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by linarith))
        have hm' : v ∉ Ioc (0 : ℝ) (1 / 2) := fun hm => absurd hm.2 (not_le.2 h')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg]
    rw [hI, show -(2 * v) / 2 = -v by ring]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, integral_renormalised_half]
    at h2
  have : ∫ y in Ioi (0 : ℝ), g y = 2 * ((1 / 4) * (Real.log 2 - Real.eulerMascheroniConstant)) := by
    rw [h2]; ring
  rw [this]
  ring

/-! ### Comparison of the renormalised constants -/

/-- `|R_{a_m} − R_∞| ≤ 3/m²` for `m ≥ 1`. -/
theorem ampRenorm_blowAmp_sub_le {m : ℝ} (hm : 1 ≤ m) :
    |ampRenorm (blowAmp m) - ampRenorm blowAmpInf| ≤ 3 / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hd := blowAmp_ampData hm
  have hd' := blowAmpInf_ampData
  -- the pointwise comparison
  have hpt : ∀ u, 0 < u → |(blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u)| ≤
      blowAmpInf u * u / m ^ 2 ∧ |blowAmp m u * (2 / u) - blowAmpInf u * (2 / u)| ≤
      blowAmpInf u * u / m ^ 2 := by
    intro u hu
    have hx : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
    have he1 : Real.exp (-(u ^ 2 / (2 * m ^ 2))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-(u ^ 2 / (2 * m ^ 2)))
    have ha0 : 0 ≤ blowAmpInf u := hd'.nonneg u
    have hkey : |blowAmp m u - blowAmpInf u| ≤ blowAmpInf u * (u ^ 2 / (2 * m ^ 2)) := by
      unfold blowAmp blowAmpInf at *
      rw [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring, abs_of_nonpos (by nlinarith)]
      nlinarith
    have hfin : |blowAmp m u - blowAmpInf u| * (2 / u) ≤ blowAmpInf u * u / m ^ 2 := by
      calc |blowAmp m u - blowAmpInf u| * (2 / u)
          ≤ blowAmpInf u * (u ^ 2 / (2 * m ^ 2)) * (2 / u) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = blowAmpInf u * u / m ^ 2 := by field_simp
    have h2u : |2 / u| = 2 / u := abs_of_pos (by positivity)
    constructor
    · rw [show (blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u) =
          (blowAmp m u - blowAmpInf u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
    · rw [show blowAmp m u * (2 / u) - blowAmpInf u * (2 / u) =
          (blowAmp m u - blowAmpInf u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
  -- the split of both constants and the two pieces
  have hq1 : ∀ {a : ℝ → ℝ} {A : ℝ}, AmpData a A →
      IntegrableOn (fun u : ℝ => (a u - 1) * (2 / u)) (Ioc 0 1) :=
    fun h => (integrableOn_ampRenorm_inner h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_mem hw, Pi.one_apply]) measurableSet_Ioc
  have hq2 : ∀ {a : ℝ → ℝ} {A : ℝ}, AmpData a A →
      IntegrableOn (fun u : ℝ => a u * (2 / u)) (Ioi 1) :=
    fun h => (integrableOn_ampRenorm_outer h).congr_fun (fun w hw => by
      simp only; rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.2 hw)), sub_zero])
      measurableSet_Ioi
  rw [ampRenorm_split hd, ampRenorm_split hd']
  have hI1 : |(∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) -
      ∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)| ≤ 1 / m ^ 2 := by
    rw [← integral_sub (hq1 hd) (hq1 hd')]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (f := fun u => (blowAmp m u - 1) * (2 / u) - (blowAmpInf u - 1) * (2 / u)) (C := 1 / m ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · have hv : volume.real (Ioc (0 : ℝ) 1) = 1 := by simp [Measure.real, Real.volume_Ioc]
      rw [Real.norm_eq_abs, hv, mul_one] at h
      exact h
    · intro u hu
      have hu0 : 0 < u := hu.1
      rw [Real.norm_eq_abs]
      refine ((hpt u hu0).1).trans ?_
      have ha1 := hd'.le_one u
      have ha0 := hd'.nonneg u
      rw [div_le_div_iff_of_pos_right hm2]
      nlinarith [hu.2]
  have hI2 : |(∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
      ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u)| ≤ 2 / m ^ 2 := by
    rw [← integral_sub (hq2 hd) (hq2 hd')]
    have hmaj : IntegrableOn (fun u : ℝ => 1 / m ^ 2 * Real.exp (-u / 2)) (Ioi 1) := by
      refine IntegrableOn.congr_fun (s := Ioi 1)
        ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (1 / m ^ 2))
        (fun w _ => ?_) measurableSet_Ioi
      congr 2
      ring
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun u => blowAmp m u * (2 / u) - blowAmpInf u * (2 / u)) hmaj ?_
    · rw [Real.norm_eq_abs] at h
      refine h.trans ?_
      rw [integral_const_mul, integral_exp_neg_half_Ioi_one]
      have he : 3 / 2 ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
      have h2 : Real.exp (-1 / 2) * 2 ≤ 2 := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        linarith
      have : 1 / m ^ 2 * (2 * Real.exp (-1 / 2)) = (Real.exp (-1 / 2) * 2) / m ^ 2 := by ring
      rw [this]
      exact div_le_div_of_nonneg_right h2 hm2.le
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu : (1 : ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      rw [Real.norm_eq_abs]
      refine ((hpt u hu0).2).trans ?_
      -- `e^{−u⁴/2} u ≤ e^{−u/2}` for `u ≥ 1`
      have hkey : blowAmpInf u * u ≤ Real.exp (-u / 2) := by
        unfold blowAmpInf
        have h1 := Real.add_one_le_exp (u ^ 4 / 2 - u / 2)
        have h2 : u ≤ Real.exp (u ^ 4 / 2 - u / 2) := by
          nlinarith [sq_nonneg (u - 1), sq_nonneg u, sq_nonneg (u ^ 2 - 1), sq_nonneg (u + 1)]
        calc Real.exp (-u ^ 4 / 2) * u ≤ Real.exp (-u ^ 4 / 2) * Real.exp (u ^ 4 / 2 - u / 2) :=
              mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
          _ = Real.exp (-u / 2) := by rw [← Real.exp_add]; ring_nf
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc |(∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) +
        (∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
        ((∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
          ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u))|
      = |((∫ u in Ioc (0 : ℝ) 1, (blowAmp m u - 1) * (2 / u)) -
          ∫ u in Ioc (0 : ℝ) 1, (blowAmpInf u - 1) * (2 / u)) +
          ((∫ u in Ioi (1 : ℝ), blowAmp m u * (2 / u)) -
            ∫ u in Ioi (1 : ℝ), blowAmpInf u * (2 / u))| := by ring_nf
    _ ≤ 1 / m ^ 2 + 2 / m ^ 2 := (abs_add_le _ _).trans (add_le_add hI1 hI2)
    _ = 3 / m ^ 2 := by ring

/-! ### Assembly -/

theorem sqrt_two_pi_div_two : Real.sqrt (2 * Real.pi) / 2 = Real.sqrt (Real.pi / 2) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2' : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  rw [Real.sqrt_mul (by norm_num) Real.pi, Real.sqrt_div' Real.pi (by norm_num)]
  field_simp
  linear_combination hs2

/-- The `m`-form of the expansion: for `m ≥ 1`,
`|Z_{m⁴} − √(π/2)(4 log m + 5 log 2 − γ)/m²| ≤ √(2π)(2 log m + 8)/m⁴`. -/
theorem blowupLaplace_two_term_m {m : ℝ} (hm : 1 ≤ m) :
    |blowupLaplace (m ^ 4) - Real.sqrt (Real.pi / 2) *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2| ≤
      Real.sqrt (2 * Real.pi) * (2 * Real.log m + 8) / m ^ 4 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hε : 0 < 1 / m ^ 2 := by positivity
  have hε1 : 1 / m ^ 2 ≤ 1 := by rw [div_le_one hm2]; nlinarith
  have hJ := ampJ_two_term (blowAmp_ampData hm) hε hε1
  have hR := ampRenorm_blowAmp_sub_le hm
  rw [ampRenorm_blowAmpInf] at hR
  have hlog4 : Real.log (4 / (1 / m ^ 2)) = 2 * Real.log 2 + 2 * Real.log m := by
    rw [show (4 : ℝ) / (1 / m ^ 2) = 2 ^ 2 * m ^ 2 by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog1 : Real.log (1 / (1 / m ^ 2)) = 2 * Real.log m := by
    rw [one_div_one_div, Real.log_pow]; push_cast; ring
  rw [hlog4, hlog1, one_mul] at hJ
  rw [blowupLaplace_eq_ampJ hm0, ← sqrt_two_pi_div_two]
  set J := ampJ (blowAmp m) (1 / m ^ 2) with hJdef
  set R := ampRenorm (blowAmp m) with hRdef
  clear_value J R
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have key : Real.sqrt (2 * Real.pi) / m ^ 2 * J - Real.sqrt (2 * Real.pi) / 2 *
      (4 * Real.log m + 5 * Real.log 2 - Real.eulerMascheroniConstant) / m ^ 2 =
      Real.sqrt (2 * Real.pi) / m ^ 2 * ((J - (2 * Real.log 2 + 2 * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / 2)) := by
    field_simp
    ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  calc Real.sqrt (2 * Real.pi) / m ^ 2 * |(J - (2 * Real.log 2 + 2 * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / 2)|
      ≤ Real.sqrt (2 * Real.pi) / m ^ 2 *
        ((1 / m ^ 2 * (2 * Real.log m + 1) + 4 * (1 / m ^ 2)) + 3 / m ^ 2) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hJ hR)) (by positivity)
    _ = Real.sqrt (2 * Real.pi) * (2 * Real.log m + 8) / m ^ 4 := by
        field_simp
        ring

/-- ★★★ **The two-term expansion of the blow-up model's partition function**: for `N ≥ 1`,
`|Z_N − √(π/2)(log N + 5 log 2 − γ)/√N| ≤ √(2π)(log N/2 + 8)/N`
(the note's `c_{½,1} = √(π/2)`, `c_{½,0} = √(π/2)(5 log 2 − γ)`). -/
theorem blowupLaplace_two_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N| ≤
      Real.sqrt (2 * Real.pi) * (Real.log N / 2 + 8) / N := by
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
  have h := blowupLaplace_two_term_m hm1
  have h2 : 2 * Real.log m = Real.log N / 2 := by rw [hlogm]; ring
  rw [hm4, ← hlogm, h2] at h
  rw [hsqrt]
  exact h

/-- ★★★ `Z_N = √(π/2)(log N + 5 log 2 − γ)/√N + O(N^{−1} log N)` as `N → ∞`. -/
theorem blowupLaplace_two_term :
    (fun N : ℝ => blowupLaplace N - Real.sqrt (Real.pi / 2) *
      (Real.log N + 5 * Real.log 2 - Real.eulerMascheroniConstant) / Real.sqrt N)
      =O[atTop] fun N => Real.log N / N := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt (2 * Real.pi) * (17 / 2)) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hb := blowupLaplace_two_term_bound (by linarith : 1 ≤ N)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hN.le)]
  refine hb.trans ?_
  rw [show Real.sqrt (2 * Real.pi) * (17 / 2) * (Real.log N / N) =
    Real.sqrt (2 * Real.pi) * (17 / 2 * Real.log N) / N by ring]
  refine div_le_div_of_nonneg_right ?_ hN.le
  have : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  nlinarith

end Grammar
