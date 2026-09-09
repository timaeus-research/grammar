/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationQuotient
import Grammar.PhaseLeadingTerm

/-!
# Bounded observables and the order constraint on leading pairs (Astra #37 P4, unit 303)

For a genuine posterior expectation the numerator is the insertion of a bounded observable `φ`
into the positive denominator integrand: on a chart, with amplitude `φ · c`, `c ≥ 0`,
```
|∫ (φ c) u^h e^{-βN u^{2k}}| ≤ ‖φ‖_∞ ∫ c u^h e^{-βN u^{2k}}          (abs_origPhaseIntegral_mul_le)
```
(`abs_integral_le_integral_abs` and monotonicity of the set integral). Consequently, if both
integrals have actual nonzero leading terms `C_φ N^{-μ}(log N)^{jn}` and `C N^{-λ}(log N)^{jd}`,
the numerator cannot precede the denominator in the asymptotic order: `λ ≤ μ`, and `jn ≤ jd` when
`μ = λ` (`not_precedes_of_bounded_quotient`; otherwise the quotient would be unbounded). This is
the exclusion Astra #37 attached to Corollary B: it uses the common positive underlying integrand,
not two unrelated abstract expansions. The three admissible cases are exactly those of unit 302.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- The population weight `u^h e^{-βN u^{2k}}`. -/
noncomputable def popWeight {d : ℕ} (h k : Fin d → ℕ) (β N : ℝ) (u : Fin d → ℝ) : ℝ :=
  (∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)))

theorem continuous_popWeight {d : ℕ} (h k : Fin d → ℕ) (β N : ℝ) :
    Continuous (popWeight h k β N) :=
  (continuous_prod_pow h).mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_prod_pow fun i => 2 * k i)).neg)

theorem popWeight_nonneg {d : ℕ} (h k : Fin d → ℕ) (β N : ℝ) {u : Fin d → ℝ}
    (hu : u ∈ unitBox d) : 0 ≤ popWeight h k β N u := by
  unfold popWeight
  refine mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg ?_ _) (Real.exp_pos _).le
  exact (Set.mem_univ_pi.1 hu i).1.le

/-- The population integral in terms of the weight. -/
theorem origPhaseIntegral_population_eq_weight (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 (fun _ => 0) η =
      ∫ x in unitBox (n + 1), η x * popWeight h k β N x := by
  rw [origPhaseIntegral_population_one]
  rfl

/-- **Bounded observables**: `|𝒵[φ c]| ≤ ‖φ‖_∞ 𝒵[c]` for `c ≥ 0` on the box. -/
theorem abs_origPhaseIntegral_mul_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {φ c : (Fin (n + 1) → ℝ) → ℝ} (hφ : Continuous φ) (hc : Continuous c) {B : ℝ}
    (hB : ∀ u ∈ unitBox (n + 1), |φ u| ≤ B) (hc0 : ∀ u ∈ unitBox (n + 1), 0 ≤ c u) :
    |origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => φ u * c u)| ≤
      B * origPhaseIntegral n h k β N 1 (fun _ => 0) c := by
  rw [origPhaseIntegral_population_eq_weight, origPhaseIntegral_population_eq_weight,
    ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  have hw := continuous_popWeight h k β N
  refine setIntegral_mono_on (integrableOn_unitBox_of_continuous _ ((hφ.mul hc).mul hw).abs)
    (integrableOn_unitBox_of_continuous _ (continuous_const.mul (hc.mul hw)))
    (measurableSet_unitBox _) fun u hu => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (hc0 u hu), abs_of_nonneg (popWeight_nonneg h k β N hu)]
  have hBu : 0 ≤ B := (abs_nonneg _).trans (hB u hu)
  calc |φ u| * c u * popWeight h k β N u ≤ B * c u * popWeight h k β N u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB u hu) (hc0 u hu))
          (popWeight_nonneg h k β N hu)
    _ = B * (c u * popWeight h k β N u) := by ring

/-- `N^{s} / (log N)^j → ∞` for `s > 0`. -/
theorem tendsto_rpow_div_log_pow_atTop {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Tendsto (fun N : ℝ => N ^ s / Real.log N ^ j) atTop atTop := by
  have h0 := tendsto_rpow_neg_mul_one_add_log_pow j hs
  have hpos : ∀ᶠ N : ℝ in atTop, 0 < N ^ (-s) * (1 + Real.log N) ^ j := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have : 0 < Real.log N := Real.log_pos hN
    positivity
  have hinv : Tendsto (fun N : ℝ => (N ^ (-s) * (1 + Real.log N) ^ j)⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.2 ⟨h0, hpos⟩).inv_tendsto_nhdsGT_zero
  refine tendsto_atTop_mono' atTop ?_ hinv
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hN
  have hN0 : 0 < N := by linarith
  calc (N ^ (-s) * (1 + Real.log N) ^ j)⁻¹ = N ^ s / (1 + Real.log N) ^ j := by
        rw [mul_inv, ← Real.rpow_neg hN0.le, neg_neg, div_eq_mul_inv]
    _ ≤ N ^ s / Real.log N ^ j :=
        div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN0 s).le (pow_pos (by linarith) j)
          (pow_le_pow_left₀ (by linarith) (by linarith) j)

/-- **Order constraint for bounded quotients**: if the quotient of two integrals with actual
nonzero leading terms stays bounded, the numerator does not precede the denominator: `λ ≤ μ`, and
`jn ≤ jd` when `μ = λ`. -/
theorem not_precedes_of_bounded_quotient {Zn Zd : ℝ → ℝ} {Cn Cd μ l : ℝ} {jn jd : ℕ}
    (hn : Zn ~[atTop] fun N => Cn * (N ^ (-μ) * Real.log N ^ jn))
    (hd : Zd ~[atTop] fun N => Cd * (N ^ (-l) * Real.log N ^ jd)) (hCn : Cn ≠ 0) (hCd : Cd ≠ 0)
    {B : ℝ} (hbound : ∀ᶠ N in atTop, |Zn N / Zd N| ≤ B) :
    l ≤ μ ∧ (μ = l → jn ≤ jd) := by
  have h := isEquivalent_quotient_powLog hn hd hCd
  set R : ℝ → ℝ := fun N => Cn / Cd * (N ^ (-(μ - l)) * (Real.log N ^ jn / Real.log N ^ jd))
    with hR
  have hC : Cn / Cd ≠ 0 := div_ne_zero hCn hCd
  have hRne : ∀ᶠ N : ℝ in atTop, R N ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos hN
    simp only [hR]
    positivity
  have hone : Tendsto (fun N => (Zn N / Zd N) / R N) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hRne).1 h
  -- the quotient is eventually at least half of `|R|`
  have hhalf : ∀ᶠ N : ℝ in atTop, |R N| / 2 ≤ |Zn N / Zd N| := by
    have h1 : ∀ᶠ N : ℝ in atTop, 1 / 2 < |(Zn N / Zd N) / R N| :=
      (hone.abs.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < |1|)))
    filter_upwards [h1, hRne] with N hN hRN
    rw [abs_div, lt_div_iff₀ (abs_pos.2 hRN)] at hN
    linarith
  -- if `|R| → ∞` the bound is contradicted
  have key : ¬ Tendsto (fun N => |R N|) atTop atTop := by
    intro hT
    have hgt : ∀ᶠ N : ℝ in atTop, 2 * B < |R N| := hT.eventually_gt_atTop _
    obtain ⟨N, hN1, hN2, hN3⟩ := (hgt.and (hhalf.and hbound)).exists
    linarith
  have habsR : ∀ᶠ N : ℝ in atTop, |R N| =
      |Cn / Cd| * (N ^ (l - μ) * (Real.log N ^ jn / Real.log N ^ jd)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos hN
    simp only [hR]
    rw [abs_mul, abs_of_pos (by positivity : 0 < N ^ (-(μ - l)) *
      (Real.log N ^ jn / Real.log N ^ jd)), neg_sub]
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    apply key
    have hs : 0 < l - μ := sub_pos.2 hlt
    have hT := (tendsto_rpow_div_log_pow_atTop hs jd).const_mul_atTop (abs_pos.2 hC)
    refine tendsto_atTop_mono' atTop ?_ hT
    filter_upwards [habsR, eventually_ge_atTop (Real.exp 1)] with N hRN hN
    have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) hN
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hN
    rw [hRN]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (by linarith) _).le
    exact div_le_div_of_nonneg_right (one_le_pow₀ hlog) (pow_pos (by linarith) jd).le
  · intro hμl
    by_contra hgt
    rw [not_le] at hgt
    apply key
    have hT := ((tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hgt)).comp
      Real.tendsto_log_atTop).const_mul_atTop (abs_pos.2 hC)
    refine tendsto_atTop_mono' atTop ?_ hT
    filter_upwards [habsR, eventually_gt_atTop (1 : ℝ)] with N hRN hN
    have hlog : 0 < Real.log N := Real.log_pos hN
    rw [hRN, hμl, sub_self, Real.rpow_zero, one_mul, Function.comp,
      pow_sub₀ _ hlog.ne' hgt.le]
    simp only [div_eq_mul_inv, le_refl]

end Grammar
