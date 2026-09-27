/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MonomialRenormalised

/-!
# The family `K = x²(x^{2k−2} + y²)/2`: the two-term expansion for every `k ≥ 2`

The blow-up model of `Grammar.BlowUpLaplaceExpansion` is the member `k = 2` of the family
`K_k = x²(x^{2k−2} + y²)/2` with the Gaussian prior `e^{−|w|²/2}` on `ℝ²`:

  `Z_k(N) = ∫_{ℝ²} e^{−N x²(x^{2k−2} + y²)/2} e^{−(x² + y²)/2} dx dy`  (`monomialFamilyZ`).

The Gaussian integral in `y` gives `Z_k(N) = √(2π)∫_ℝ e^{−Nx^{2k}/2} e^{−x²/2}/√(1 + Nx²) dx`
(`monomialFamilyZ_eq_integral`); with `N = m^{2k}` and `x = u/m` this is
`√(2π)/m^k · J_{a_m}(m^{2−2k})` for the amplitude `a_m(u) = e^{−u^{2k}/2} e^{−u²/2m²}`
(`monomialFamilyZ_eq_ampJ`), and the engine of `Grammar.AmplitudeJ` with the monomial
renormalised constant `(log 2 − γ)/k` of `Grammar.MonomialRenormalised` gives

  `|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤
     √(2π)(((k−1)/k) log N + 8)/(√N · N^{1/k})`  for `N ≥ 1`, `k ≥ 2`
  (★★★ `monomialFamily_two_term_bound`),

hence `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2−1/k} log N)`
(★★★ `monomialFamily_two_term`; the log-free `O(N^{−1/2−1/k})` of the consult needs a sharper
kernel estimate).  At `k = 2` this is the blow-up model's `√(π/2)(log N + 5 log 2 − γ)/√N`
(Astra round-9 target 1).  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- The family's partition function with the prior `e^{−|w|²/2}`. -/
noncomputable def monomialFamilyZ (k : ℕ) (N : ℝ) : ℝ :=
  ∫ w : ℝ × ℝ, Real.exp (-N * (w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2)) / 2) *
    Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2)

/-- The amplitude `a_m(u) = e^{−u^{2k}/2} e^{−u²/2m²}`. -/
noncomputable def famAmp (k : ℕ) (m u : ℝ) : ℝ :=
  Real.exp (-u ^ (2 * k) / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2))

/-! ### The conditional reduction -/

theorem integrable_monomialFamilyZ (k : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    Integrable fun w : ℝ × ℝ => Real.exp (-N * (w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2)) / 2) *
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
    have hpow : 0 ≤ w.1 ^ (2 * k - 2) := by
      rcases Nat.even_or_odd (2 * k - 2) with h | h
      · exact h.pow_nonneg _
      · exfalso
        obtain ⟨j, hj⟩ := h
        omega
    have h1 : Real.exp (-N * (w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2)) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2) := by positivity
        nlinarith [mul_nonneg hN this])
    have h2 : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 2) =
        Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 : 0 ≤ Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by positivity
    calc Real.exp (-N * (w.1 ^ 2 * (w.1 ^ (2 * k - 2) + w.2 ^ 2)) / 2) *
          (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2))
        ≤ 1 * (Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h1 h3
      _ = Real.exp (-w.1 ^ 2 / 2) * Real.exp (-w.2 ^ 2 / 2) := by ring

/-- ★★ **The exact conditional reduction**:
`Z_k(N) = √(2π) ∫_ℝ e^{−N x^{2k}/2} e^{−x²/2}/√(1 + N x²) dx` for `N ≥ 0`, `k ≥ 1`. -/
theorem monomialFamilyZ_eq_integral {k : ℕ} (hk : 1 ≤ k) {N : ℝ} (hN : 0 ≤ N) :
    monomialFamilyZ k N = Real.sqrt (2 * Real.pi) *
      ∫ x : ℝ, Real.exp (-N * x ^ (2 * k) / 2) * Real.exp (-x ^ 2 / 2) /
        Real.sqrt (1 + N * x ^ 2) := by
  unfold monomialFamilyZ
  rw [Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_monomialFamilyZ k N hN
    rwa [Measure.volume_eq_prod] at this), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hc : 0 < 1 + N * x ^ 2 := by positivity
  have hx2k : x ^ 2 * x ^ (2 * k - 2) = x ^ (2 * k) := by
    rw [← pow_add]; congr 1; omega
  have hpt : ∀ y : ℝ, Real.exp (-N * (x ^ 2 * (x ^ (2 * k - 2) + y ^ 2)) / 2) *
      Real.exp (-(x ^ 2 + y ^ 2) / 2) =
      (Real.exp (-N * x ^ (2 * k) / 2) * Real.exp (-x ^ 2 / 2)) *
        Real.exp (-(1 + N * x ^ 2) * y ^ 2 / 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← hx2k]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_exp_cond hc]
  have hsq : Real.sqrt (2 * Real.pi / (1 + N * x ^ 2)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt (1 + N * x ^ 2) := Real.sqrt_div' _ hc.le
  rw [hsq]
  ring

/-! ### Scaling to the amplitude form -/

theorem famAmp_eq (k : ℕ) (m u : ℝ) :
    famAmp k m u = Real.exp (-u ^ (2 * k) / 2 + -u ^ 2 / (2 * m ^ 2)) := by
  unfold famAmp; rw [Real.exp_add]

/-- ★★ `Z_k(m^{2k}) = √(2π)/m^k · J_{a_m}(m^{2−2k})` for `m > 0`, `k ≥ 1`
(the scale `ε = 1/m^{2k−2}`). -/
theorem monomialFamilyZ_eq_ampJ {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 0 < m) :
    monomialFamilyZ k (m ^ (2 * k)) =
      Real.sqrt (2 * Real.pi) / m ^ k * ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) := by
  rw [monomialFamilyZ_eq_integral hk (by positivity)]
  set f : ℝ → ℝ := fun x =>
    Real.exp (-m ^ (2 * k) * x ^ (2 * k) / 2) * Real.exp (-x ^ 2 / 2) /
      Real.sqrt (1 + m ^ (2 * k) * x ^ 2) with hf
  have h1 : ∫ x : ℝ, f x = 2 * ∫ x in Ioi (0 : ℝ), f x := by
    rw [← integral_comp_abs (f := f)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [show |x| ^ (2 * k) = x ^ (2 * k) by rw [pow_mul, sq_abs, ← pow_mul], sq_abs]
  have hm1 : 0 < 1 / m := by positivity
  have h2 : ∫ x in Ioi (0 : ℝ), f x = m⁻¹ * ∫ u in Ioi (0 : ℝ), f (1 / m * u) := by
    rw [integral_comp_mul_left_Ioi f 0 hm1, mul_zero, smul_eq_mul, one_div, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ hm.ne', one_mul]
  have hmk : 0 < m ^ k := by positivity
  have hm2k2 : m ^ (2 * k) = m ^ (2 * k - 2) * m ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have h3 : ∀ u ∈ Ioi (0 : ℝ), f (1 / m * u) =
      (m ^ (k - 1))⁻¹ * (famAmp k m u / Real.sqrt (u ^ 2 + 1 / m ^ (2 * k - 2))) := by
    intro u _
    simp only [hf]
    have e1 : -m ^ (2 * k) * (1 / m * u) ^ (2 * k) / 2 = -u ^ (2 * k) / 2 := by
      rw [mul_pow, div_pow, one_pow]; field_simp
    have e2 : -(1 / m * u) ^ 2 / 2 = -u ^ 2 / (2 * m ^ 2) := by field_simp
    have hpos : 0 < m ^ (2 * k - 2) := by positivity
    have e3 : 1 + m ^ (2 * k) * (1 / m * u) ^ 2 =
        m ^ (2 * k - 2) * (u ^ 2 + 1 / m ^ (2 * k - 2)) := by
      rw [hm2k2]; field_simp; ring
    have hsq : Real.sqrt (m ^ (2 * k - 2)) = m ^ (k - 1) := by
      rw [show 2 * k - 2 = (k - 1) * 2 by omega, pow_mul, Real.sqrt_sq (by positivity)]
    have hmk1 : m ^ k = m ^ (k - 1) * m := by
      rw [← pow_succ]; congr 1; omega
    rw [e1, e2, e3, Real.sqrt_mul hpos.le, hsq]
    unfold famAmp
    field_simp
  rw [h1, h2, setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  unfold ampJ
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  have hmk1 : m ^ k = m ^ (k - 1) * m := by
    rw [← pow_succ]; congr 1; omega
  set I := ∫ u in Ioi (0 : ℝ), famAmp k m u / Real.sqrt (u ^ 2 + 1 / m ^ (2 * k - 2)) with hI
  clear_value I
  have hmk1' : 0 < m ^ (k - 1) := by positivity
  rw [hmk1]
  field_simp

/-! ### The amplitude data -/

theorem famAmp_ampData {k : ℕ} (hk : 1 ≤ k) {m : ℝ} (hm : 1 ≤ m) : AmpData (famAmp k m) 1 where
  meas := by unfold famAmp; fun_prop
  nonneg u := by unfold famAmp; positivity
  le_one u := by
    unfold famAmp
    have hm0 : 0 < m := by linarith
    have hu2k : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
    calc Real.exp (-u ^ (2 * k) / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤ 1 * 1 :=
          mul_le_mul (Real.exp_le_one_iff.2 (by linarith))
            (Real.exp_le_one_iff.2 (by
              have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
              linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  A_nonneg := zero_le_one
  near u hu := by
    rw [famAmp_eq]
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hu2k : u ^ (2 * k) ≤ u ^ 2 := by
      rw [pow_mul]
      calc (u ^ 2) ^ k ≤ (u ^ 2) ^ 1 := pow_le_pow_of_le_one (by positivity) hu2 hk
        _ = u ^ 2 := pow_one _
    have hdiv : u ^ 2 / (2 * m ^ 2) ≤ u ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg u]
    have := Real.add_one_le_exp (-u ^ (2 * k) / 2 + -u ^ 2 / (2 * m ^ 2))
    have e : -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) := by ring
    rw [e] at this ⊢
    linarith
  tail u hu := by
    unfold famAmp
    have hm0 : 0 < m := by linarith
    have h1 : u ≤ u ^ (2 * k) := by
      calc u = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ (2 * k) := pow_le_pow_right₀ hu (by omega)
    calc Real.exp (-u ^ (2 * k) / 2) * Real.exp (-u ^ 2 / (2 * m ^ 2)) ≤
          Real.exp (-u ^ (2 * k) / 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by
            have : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
            linarith [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring]))
            (Real.exp_pos _).le
      _ ≤ Real.exp (-u / 2) := by
          rw [mul_one]
          exact Real.exp_le_exp.2 (by linarith)

/-! ### Comparison of the renormalised constants -/

/-- `|R_{a_m} − R_∞| ≤ 3/m²` for `m ≥ 1`, `k ≥ 2`. -/
theorem ampRenorm_famAmp_sub_le {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |ampRenorm (famAmp k m) - ampRenorm (monoAmp k)| ≤ 3 / m ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hd := famAmp_ampData hk1 hm
  have hd' := monoAmp_ampData (by omega : 0 < k)
  -- the pointwise comparison
  have hpt : ∀ u, 0 < u → |(famAmp k m u - 1) * (2 / u) - (monoAmp k u - 1) * (2 / u)| ≤
      monoAmp k u * u / m ^ 2 ∧ |famAmp k m u * (2 / u) - monoAmp k u * (2 / u)| ≤
      monoAmp k u * u / m ^ 2 := by
    intro u hu
    have hx : 0 ≤ u ^ 2 / (2 * m ^ 2) := by positivity
    have he1 : Real.exp (-(u ^ 2 / (2 * m ^ 2))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have he2 := Real.add_one_le_exp (-(u ^ 2 / (2 * m ^ 2)))
    have ha0 : 0 ≤ monoAmp k u := hd'.nonneg u
    have hkey : |famAmp k m u - monoAmp k u| ≤ monoAmp k u * (u ^ 2 / (2 * m ^ 2)) := by
      unfold famAmp monoAmp at *
      rw [show -u ^ 2 / (2 * m ^ 2) = -(u ^ 2 / (2 * m ^ 2)) by ring, abs_of_nonpos (by nlinarith)]
      nlinarith
    have hfin : |famAmp k m u - monoAmp k u| * (2 / u) ≤ monoAmp k u * u / m ^ 2 := by
      calc |famAmp k m u - monoAmp k u| * (2 / u)
          ≤ monoAmp k u * (u ^ 2 / (2 * m ^ 2)) * (2 / u) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = monoAmp k u * u / m ^ 2 := by field_simp
    have h2u : |2 / u| = 2 / u := abs_of_pos (by positivity)
    constructor
    · rw [show (famAmp k m u - 1) * (2 / u) - (monoAmp k u - 1) * (2 / u) =
          (famAmp k m u - monoAmp k u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
    · rw [show famAmp k m u * (2 / u) - monoAmp k u * (2 / u) =
          (famAmp k m u - monoAmp k u) * (2 / u) by ring, abs_mul, h2u]
      exact hfin
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
  have hI1 : |(∫ u in Ioc (0 : ℝ) 1, (famAmp k m u - 1) * (2 / u)) -
      ∫ u in Ioc (0 : ℝ) 1, (monoAmp k u - 1) * (2 / u)| ≤ 1 / m ^ 2 := by
    rw [← integral_sub (hq1 hd) (hq1 hd')]
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) 1)
      (f := fun u => (famAmp k m u - 1) * (2 / u) - (monoAmp k u - 1) * (2 / u)) (C := 1 / m ^ 2)
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
  have hI2 : |(∫ u in Ioi (1 : ℝ), famAmp k m u * (2 / u)) -
      ∫ u in Ioi (1 : ℝ), monoAmp k u * (2 / u)| ≤ 2 / m ^ 2 := by
    rw [← integral_sub (hq2 hd) (hq2 hd')]
    have hmaj : IntegrableOn (fun u : ℝ => 1 / m ^ 2 * Real.exp (-u / 2)) (Ioi 1) := by
      refine IntegrableOn.congr_fun (s := Ioi 1)
        ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (1 / m ^ 2))
        (fun w _ => ?_) measurableSet_Ioi
      congr 2
      ring
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun u => famAmp k m u * (2 / u) - monoAmp k u * (2 / u)) hmaj ?_
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
      -- `e^{−u^{2k}/2} u ≤ e^{−u/2}` for `u ≥ 1`, `k ≥ 2`
      have hkey : monoAmp k u * u ≤ Real.exp (-u / 2) := by
        unfold monoAmp
        have h4 : u ^ 4 ≤ u ^ (2 * k) := pow_le_pow_right₀ hu.le (by omega)
        have h1 := Real.add_one_le_exp (u ^ 4 / 2 - u / 2)
        have h2 : u ≤ Real.exp (u ^ 4 / 2 - u / 2) := by
          nlinarith [sq_nonneg (u - 1), sq_nonneg u, sq_nonneg (u ^ 2 - 1), sq_nonneg (u + 1)]
        have h3 : Real.exp (-u ^ (2 * k) / 2) ≤ Real.exp (-u ^ 4 / 2) :=
          Real.exp_le_exp.2 (by linarith)
        calc Real.exp (-u ^ (2 * k) / 2) * u
            ≤ Real.exp (-u ^ 4 / 2) * Real.exp (u ^ 4 / 2 - u / 2) :=
              mul_le_mul h3 h2 hu0.le (Real.exp_pos _).le
          _ = Real.exp (-u / 2) := by rw [← Real.exp_add]; ring_nf
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc |(∫ u in Ioc (0 : ℝ) 1, (famAmp k m u - 1) * (2 / u)) +
        (∫ u in Ioi (1 : ℝ), famAmp k m u * (2 / u)) -
        ((∫ u in Ioc (0 : ℝ) 1, (monoAmp k u - 1) * (2 / u)) +
          ∫ u in Ioi (1 : ℝ), monoAmp k u * (2 / u))|
      = |((∫ u in Ioc (0 : ℝ) 1, (famAmp k m u - 1) * (2 / u)) -
          ∫ u in Ioc (0 : ℝ) 1, (monoAmp k u - 1) * (2 / u)) +
          ((∫ u in Ioi (1 : ℝ), famAmp k m u * (2 / u)) -
            ∫ u in Ioi (1 : ℝ), monoAmp k u * (2 / u))| := by ring_nf
    _ ≤ 1 / m ^ 2 + 2 / m ^ 2 := (abs_add_le _ _).trans (add_le_add hI1 hI2)
    _ = 3 / m ^ 2 := by ring

/-! ### Assembly -/

/-- The `m`-form: for `m ≥ 1`, `k ≥ 2`,
`|Z_k(m^{2k}) − √(2π)/m^k · (2(k−1) log m + 2 log 2 + (log 2 − γ)/k)| ≤
  √(2π)/m^k · ((2k−2) log m + 8)/m²`. -/
theorem monomialFamily_two_term_m {k : ℕ} (hk : 2 ≤ k) {m : ℝ} (hm : 1 ≤ m) :
    |monomialFamilyZ k (m ^ (2 * k)) - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) / m ^ k * ((2 * k - 2) * Real.log m + 8) / m ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m ^ 2 := by positivity
  have hpow : 0 < m ^ (2 * k - 2) := by positivity
  have hpow1 : 1 ≤ m ^ (2 * k - 2) := one_le_pow₀ hm
  have hpow2 : m ^ 2 ≤ m ^ (2 * k - 2) := pow_le_pow_right₀ hm (by omega)
  have hε : 0 < 1 / m ^ (2 * k - 2) := by positivity
  have hε1 : 1 / m ^ (2 * k - 2) ≤ 1 := by rw [div_le_one hpow]; exact hpow1
  have hεm : 1 / m ^ (2 * k - 2) ≤ 1 / m ^ 2 := by
    rw [div_le_div_iff₀ hpow hm2]; nlinarith
  have hJ := ampJ_two_term (famAmp_ampData hk1 hm) hε hε1
  have hR := ampRenorm_famAmp_sub_le hk hm
  rw [ampRenorm_monoAmp (by omega : 0 < k)] at hR
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : ((2 * k - 2 : ℕ) : ℝ) = 2 * k - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hlog4 : Real.log (4 / (1 / m ^ (2 * k - 2))) =
      2 * Real.log 2 + (2 * k - 2) * Real.log m := by
    rw [show (4 : ℝ) / (1 / m ^ (2 * k - 2)) = 2 ^ 2 * m ^ (2 * k - 2) by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, hcast]
    push_cast
    ring
  have hlog1 : Real.log (1 / (1 / m ^ (2 * k - 2))) = (2 * k - 2) * Real.log m := by
    rw [one_div_one_div, Real.log_pow, hcast]
  rw [hlog4, hlog1, one_mul] at hJ
  rw [monomialFamilyZ_eq_ampJ hk1 hm0]
  set J := ampJ (famAmp k m) (1 / m ^ (2 * k - 2)) with hJdef
  set R := ampRenorm (famAmp k m) with hRdef
  set ε := 1 / m ^ (2 * k - 2) with hεdef
  clear_value J R ε
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hmk : 0 < m ^ k := by positivity
  have key : Real.sqrt (2 * Real.pi) / m ^ k * J - Real.sqrt (2 * Real.pi) / m ^ k *
      (2 * (k - 1) * Real.log m + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k) =
      Real.sqrt (2 * Real.pi) / m ^ k * ((J - (2 * Real.log 2 + (2 * k - 2) * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / k)) := by ring
  rw [key, abs_mul, abs_of_pos (by positivity)]
  have hE : |(J - (2 * Real.log 2 + (2 * k - 2) * Real.log m + R)) +
      (R - (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      ((2 * k - 2) * Real.log m + 8) / m ^ 2 := by
    calc |(J - (2 * Real.log 2 + (2 * k - 2) * Real.log m + R)) +
          (R - (Real.log 2 - Real.eulerMascheroniConstant) / k)|
        ≤ |J - (2 * Real.log 2 + (2 * k - 2) * Real.log m + R)| +
          |R - (Real.log 2 - Real.eulerMascheroniConstant) / k| := abs_add_le _ _
      _ ≤ (ε * ((2 * k - 2) * Real.log m + 1) + 4 * ε) + 3 / m ^ 2 := add_le_add hJ hR
      _ ≤ (1 / m ^ 2 * ((2 * k - 2) * Real.log m + 1) + 4 * (1 / m ^ 2)) + 3 / m ^ 2 := by
          have h1 : 0 ≤ (2 * k - 2) * Real.log m + 1 := by nlinarith
          gcongr
      _ = ((2 * k - 2) * Real.log m + 8) / m ^ 2 := by ring
  calc Real.sqrt (2 * Real.pi) / m ^ k * |(J - (2 * Real.log 2 + (2 * k - 2) * Real.log m + R)) +
        (R - (Real.log 2 - Real.eulerMascheroniConstant) / k)|
      ≤ Real.sqrt (2 * Real.pi) / m ^ k * (((2 * k - 2) * Real.log m + 8) / m ^ 2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = Real.sqrt (2 * Real.pi) / m ^ k * ((2 * k - 2) * Real.log m + 8) / m ^ 2 := by ring

/-- ★★★ **The two-term expansion of the family**: for `N ≥ 1` and `k ≥ 2`,
`|Z_k(N) − √(2π)/√N · [((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k]| ≤
  √(2π)(((k−1)/k) log N + 8)/(√N · N^{1/k})`. -/
theorem monomialFamily_two_term_bound {k : ℕ} (hk : 2 ≤ k) {N : ℝ} (hN : 1 ≤ N) :
    |monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      Real.sqrt (2 * Real.pi) * ((k - 1) / k * Real.log N + 8) /
        (Real.sqrt N * N ^ (1 / (k : ℝ))) := by
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
  have h := monomialFamily_two_term_m hk hm1
  rw [hm2k] at h
  have e1 : 2 * (k - 1) * Real.log m = (k - 1) / k * Real.log N := by rw [hlogm]; field_simp
  have e2 : (2 * k - 2) * Real.log m = (k - 1) / k * Real.log N := by rw [hlogm]; field_simp
  rw [e1, e2, ← hsqrt] at h
  rw [hNk]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- ★★★ `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2−1/k} log N)`
for every `k ≥ 2`. -/
theorem monomialFamily_two_term {k : ℕ} (hk : 2 ≤ k) :
    (fun N : ℝ => monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      ((k - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k))
      =O[atTop] fun N => Real.log N / (Real.sqrt N * N ^ (1 / (k : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt (2 * Real.pi) * 9) ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
  have hN : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hNk : 0 < N ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hℓ : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : (k - 1) / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ (k - 1) / (k : ℝ) := div_nonneg (by linarith) (by linarith)
  have hb := monomialFamily_two_term_bound hk hN
  have hpos : (0 : ℝ) ≤ Real.log N / (Real.sqrt N * N ^ (1 / (k : ℝ))) :=
    div_nonneg (by linarith) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  refine hb.trans ?_
  rw [show Real.sqrt (2 * Real.pi) * 9 * (Real.log N / (Real.sqrt N * N ^ (1 / (k : ℝ)))) =
    Real.sqrt (2 * Real.pi) * (9 * Real.log N) / (Real.sqrt N * N ^ (1 / (k : ℝ))) by ring]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have h9 : (k - 1) / (k : ℝ) * Real.log N + 8 ≤ 9 * Real.log N := by
    nlinarith [mul_le_mul_of_nonneg_right hfrac (by linarith : (0 : ℝ) ≤ Real.log N)]
  exact mul_le_mul_of_nonneg_left h9 this

end Grammar
