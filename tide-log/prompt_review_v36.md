# Fidelity review v36 — units 302–305 (grammar §3 rewrite, Programme P per Astra #37; unit-16 review, work packages P4–P5)

Context: your #37 design; reviews v32–v35 all PASS. Your v35 §5–6 guidance for P4/P5: keep the log shift as a quotient of natural powers `log^{r−1}/log^{m−1}`; require `C ≠ 0`, `C_φ ≠ 0`; bounded-observable bridge `|Z_φ| ≤ ‖φ‖∞ Z` for a nonnegative base weight rules out the numerator preceding the denominator; three cases; for `φ = K` prove `A(h+2k,k,λ+1,β;ψ) = (λ/β) A(h,k,λ,β;ψ)` preserving the minimiser set and multiplicity with the factor from the face-functional normalisation, then the quotient with the same amplitude/measure/charts, nonzero denominator coefficient, both residuals controlled; assembled: tied charts have `λ_I = μ_*` so inserted coefficients sum to `(μ_*/β) A_*`. Units 302–305 implement this. Everything compiles (branch `tide/population-normal-form`, 296 modules, no `sorry`, no added `axiom`). This is the last theorem tranche of the 20-unit programme (16 units used; the remaining budget is the release audit).

Frozen interfaces beyond v32–v35 (Mathlib names at this pin):
```lean
protected theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) : (fun x => t x / v x) ~[l] fun x => u x / w x
theorem IsEquivalent.congr_right (huv : u ~[l] v) (hvw : v =ᶠ[l] w) : u ~[l] w
theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) : Tendsto v l (𝓝 c)
theorem isEquivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1)
theorem Real.rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z
theorem Real.Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s
theorem tendsto_log_pow_div_pow (a b : ℕ) (hab : a < b) : Tendsto (fun N => Real.log N ^ a / Real.log N ^ b) atTop (𝓝 0)
theorem tendsto_rpow_neg_mul_one_add_log_pow (n : ℕ) {s : ℝ} (hs : 0 < s) : Tendsto (fun N : ℝ => N ^ (-s) * (1 + Real.log N) ^ n) atTop (𝓝 0)
theorem integrableOn_unitBox_of_continuous {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) : IntegrableOn f (unitBox d)
theorem origPhaseIntegral_population_one … : origPhaseIntegral n h k β N 1 (fun _ => 0) η = ∫ x in unitBox (n + 1), η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))
theorem origPhaseIntegral_monomial_shift … (ξ ψ) (s : Fin (n + 1) → ℕ) : origPhaseIntegral n h k β N b ξ (fun u => (∏ i, u i ^ s i) * ψ u) = origPhaseIntegral n (fun i => h i + s i) k β N b ξ ψ
theorem population_isEquivalent … (hmin) (hatt) (η) (hηc : Continuous η) (hA : amplitudeCoeff h k l β η ≠ 0) : (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop] fun N => amplitudeCoeff h k l β η * (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))
-- u301: chartFace ν h k β x lam I := ∫ v, amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v)) ∂(ν I);
--       assembledFace ν h k β x lam μs ms := ∑ I, if lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms then chartFace ν h k β x lam I else 0;
--       population_assembled_isEquivalent … (hA : assembledFace … ≠ 0) : Zpop ~[atTop] fun N => assembledFace ν h k β x lam μs ms * (N ^ (-μs) * Real.log N ^ (ms - 1))
noncomputable def faceLeadConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ := Real.Gamma l * β ^ (-l) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) * ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1
noncomputable def amplitudeCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ := faceLeadConst h k l β * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u
```

## The four units (complete files)

### Grammar/PopulationQuotient.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationEquivalent
import Grammar.MonomialShiftedMoments
import Grammar.OrderedRemainder

/-!
# Corollary B: leading population expectations (Astra #37 P4, unit 302)

If the denominator and numerator have actual nonzero leading terms
```
𝒵_n[1] ∼ C n^{-λ}(log n)^{m−1},  C ≠ 0,        𝒵_n[φ] ∼ C_φ n^{-μ}(log n)^{r−1},
```
then the quotient `E_n[φ] = 𝒵_n[φ]/𝒵_n[1]` satisfies
```
E_n[φ] ∼ (C_φ/C) n^{-(μ−λ)} (log n)^{r−1}/(log n)^{m−1}          (isEquivalent_quotient_powLog)
```
(the logarithmic shift `(r−1) − (m−1)` is kept as a quotient of natural powers, which composes
with `IsEquivalent.div` and the natural-power statements of P1–P3), and the three cases of §3.6:

* `μ = λ`, `r = m` (generic observable): `E_n[φ] → C_φ/C` (`quotient_tendsto_const`);
* `μ = λ`, `r < m` (partially vanishing): `E_n[φ] → 0` logarithmically
(`quotient_tendsto_zero_log`);
* `μ > λ` (fully vanishing): `E_n[φ] → 0` with power decay (`quotient_tendsto_zero_pow`).

These classify **actual leading pairs** (supplied as asymptotic equivalences with nonzero
coefficients), not pairs derived from divisor orders; with `C_φ = 0` nothing is asserted. The
inputs are the equivalences produced by P2/P3 (`population_isEquivalent`,
`tanIntegral_population_isEquivalent`, `population_assembled_isEquivalent`) for the numerator and
denominator, with the denominator coefficient positive by `amplitudeCoeff_pos` and its
descendants. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- **Quotient of leading terms** (Corollary B core). -/
theorem isEquivalent_quotient_powLog {Zn Zd : ℝ → ℝ} {Cn Cd μ l : ℝ} {jn jd : ℕ}
    (hn : Zn ~[atTop] fun N => Cn * (N ^ (-μ) * Real.log N ^ jn))
    (hd : Zd ~[atTop] fun N => Cd * (N ^ (-l) * Real.log N ^ jd)) (hCd : Cd ≠ 0) :
    (fun N => Zn N / Zd N) ~[atTop]
      fun N => Cn / Cd * (N ^ (-(μ - l)) * (Real.log N ^ jn / Real.log N ^ jd)) := by
  refine (hn.div hd).congr_right ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  simp only [Pi.div_apply]
  rw [show -(μ - l) = -μ - -l by ring, Real.rpow_sub hN0]
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hlog : Real.log N ^ jd ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  field_simp

/-- **Generic observable**: same exponent and log degree — the expectation converges to the
ratio of leading coefficients. -/
theorem quotient_tendsto_const {Zn Zd : ℝ → ℝ} {Cn Cd μ l : ℝ} {jn jd : ℕ}
    (hn : Zn ~[atTop] fun N => Cn * (N ^ (-μ) * Real.log N ^ jn))
    (hd : Zd ~[atTop] fun N => Cd * (N ^ (-l) * Real.log N ^ jd)) (hCd : Cd ≠ 0) (hμ : μ = l)
    (hj : jn = jd) : Tendsto (fun N => Zn N / Zd N) atTop (𝓝 (Cn / Cd)) := by
  have h := isEquivalent_quotient_powLog hn hd hCd
  subst hμ hj
  refine h.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  rw [sub_self, neg_zero, Real.rpow_zero, div_self (pow_ne_zero _ (Real.log_pos hN).ne'), mul_one,
    mul_one]

/-- **Partially vanishing observable**: same exponent, smaller log degree — logarithmic decay to
zero. -/
theorem quotient_tendsto_zero_log {Zn Zd : ℝ → ℝ} {Cn Cd μ l : ℝ} {jn jd : ℕ}
    (hn : Zn ~[atTop] fun N => Cn * (N ^ (-μ) * Real.log N ^ jn))
    (hd : Zd ~[atTop] fun N => Cd * (N ^ (-l) * Real.log N ^ jd)) (hCd : Cd ≠ 0) (hμ : μ = l)
    (hj : jn < jd) : Tendsto (fun N => Zn N / Zd N) atTop (𝓝 0) := by
  have h := isEquivalent_quotient_powLog hn hd hCd
  subst hμ
  refine h.symm.tendsto_nhds ?_
  have := ((tendsto_log_pow_div_pow jn jd hj).const_mul (1 : ℝ)).const_mul (Cn / Cd)
  simpa [sub_self, neg_zero, Real.rpow_zero] using this

/-- **Fully vanishing observable**: larger exponent — power decay to zero. -/
theorem quotient_tendsto_zero_pow {Zn Zd : ℝ → ℝ} {Cn Cd μ l : ℝ} {jn jd : ℕ}
    (hn : Zn ~[atTop] fun N => Cn * (N ^ (-μ) * Real.log N ^ jn))
    (hd : Zd ~[atTop] fun N => Cd * (N ^ (-l) * Real.log N ^ jd)) (hCd : Cd ≠ 0) (hμ : l < μ) :
    Tendsto (fun N => Zn N / Zd N) atTop (𝓝 0) := by
  have h := isEquivalent_quotient_powLog hn hd hCd
  refine h.symm.tendsto_nhds ?_
  have hmaj := (tendsto_rpow_neg_mul_one_add_log_pow jn (sub_pos.2 hμ)).const_mul |Cn / Cd|
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) hN
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hN
  have hpow : 0 < N ^ (-(μ - l)) := Real.rpow_pos_of_pos (by linarith) _
  have hjd : 1 ≤ Real.log N ^ jd := one_le_pow₀ hlog
  have hratio : Real.log N ^ jn / Real.log N ^ jd ≤ (1 + Real.log N) ^ jn := by
    calc Real.log N ^ jn / Real.log N ^ jd ≤ Real.log N ^ jn / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos hjd
      _ = Real.log N ^ jn := div_one _
      _ ≤ (1 + Real.log N) ^ jn := pow_le_pow_left₀ (by linarith) (by linarith) jn
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log N ^ jn / Real.log N ^ jd)]
  gcongr

end Grammar
```

### Grammar/PopulationBounded.lean
```lean
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
```

### Grammar/PopulationEnergy.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationShift
import Grammar.PopulationQuotient

/-!
# The energy observable `φ = K` (Astra #37 P5, unit 304; paper `ex:phi_equals_K`)

In a normal-form chart `K∘π = u^{2k}`, so inserting the observable `K` multiplies the amplitude by
`u^{2k}`, i.e. shifts the weight `h ↦ h + 2k`. Every ratio shifts by exactly one,
`(hᵢ+2kᵢ+1)/(2kᵢ) = (hᵢ+1)/(2kᵢ) + 1` (`ratioExp_add_two_k`), so the minimiser set, the
multiplicity, the face projection and the residual weight are unchanged, and the face constant
picks up `Γ(λ+1)β^{-(λ+1)}/(Γ(λ)β^{-λ}) = λ/β`:
```
amplitudeCoeff (h+2k) k (λ+1) β ψ = (λ/β) · amplitudeCoeff h k λ β ψ        
(amplitudeCoeff_add_two_k)
```
Hence, when the denominator face functional `A = amplitudeCoeff h k λ β ψ` is nonzero,
```
N · 𝒵_N[K∘π] / 𝒵_N[1] → λ/β                                                  (energy_ratio_tendsto)
```
at chart level (`β = 1`: the posterior expected KL divergence decays as `λ/n`, Watanabe's
Theorem 6.10). The factor `λ/β` comes from the face-functional normalisation, not merely from the
exponent shift. Not established: the exact identity `𝒵_n[K] = −𝒵_n'(n)` (differentiation under
the geometric integral) and the correction `−(m−1)/(n log n)`, which is not a consequence of
differentiating an asymptotic equivalent. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

variable {d : ℕ}

/-- Inserting `u^{2k}` shifts every ratio by one. -/
theorem ratioExp_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) :
    ratioExp (fun i => h i + 2 * k i) k i = ratioExp h k i + 1 := by
  unfold ratioExp
  have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
  field_simp
  push_cast
  ring

theorem ratioExp_add_two_k_eq_iff (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (i : Fin d) :
    ratioExp (fun i => h i + 2 * k i) k i = l + 1 ↔ ratioExp h k i = l := by
  rw [ratioExp_add_two_k h k hk i, add_left_inj]

theorem multCount_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l := by
  unfold multCount
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]

theorem faceProj_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) :
    faceProj (fun i => h i + 2 * k i) k (l + 1) = faceProj h k l := by
  funext u i
  unfold faceProj
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]

theorem residualWeight_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (u : Fin d → ℝ) :
    residualWeight (fun i => h i + 2 * k i) k (l + 1) u = residualWeight h k l u := by
  unfold residualWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [ratioExp_add_two_k_eq_iff h k hk l i]
  split_ifs
  · rfl
  · congr 1
    push_cast
    ring

theorem hmin_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) : ∀ i, l + 1 ≤ ratioExp (fun i => h i + 2 * k i) k i := by
  intro i
  rw [ratioExp_add_two_k h k hk i]
  linarith [hmin i]

theorem hatt_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hatt : ∃ i, ratioExp h k i = l) : ∃ i, ratioExp (fun i => h i + 2 * k i) k i = l + 1 := by
  obtain ⟨i, hi⟩ := hatt
  exact ⟨i, by rw [ratioExp_add_two_k h k hk i, hi]⟩

/-- The face constant of the shifted weight is `λ/β` times the original. -/
theorem faceLeadConst_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l)
    (hβ : 0 < β) :
    faceLeadConst (fun i => h i + 2 * k i) k (l + 1) β = l / β * faceLeadConst h k l β := by
  unfold faceLeadConst
  rw [multCount_add_two_k h k hk l, Real.Gamma_add_one hl.ne']
  have hprod : (∏ i, if ratioExp (fun i => h i + 2 * k i) k i = l + 1
      then 1 / (2 * (k i : ℝ)) else 1) = ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1
:=
    Finset.prod_congr rfl fun i _ => by simp only [ratioExp_add_two_k_eq_iff h k hk l i]
  rw [hprod, show -(l + 1) = -l + -1 by ring, Real.rpow_add hβ, Real.rpow_neg_one]
  field_simp

/-- **The face functional of the energy observable**: `A_K = (λ/β) A_1`. -/
theorem amplitudeCoeff_add_two_k (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ} (hl : 0 < l)
    (hβ : 0 < β) (ψ : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff (fun i => h i + 2 * k i) k (l + 1) β ψ = l / β * amplitudeCoeff h k l β ψ := by
  unfold amplitudeCoeff
  rw [faceLeadConst_add_two_k h k hk hl hβ, faceProj_add_two_k h k hk l]
  simp_rw [residualWeight_add_two_k h k hk l]
  ring

/-- **`N · E_N[K∘π] → λ/β`** at chart level: for a continuous amplitude `ψ` with nonzero face
functional, the ratio of the population integral with `K∘π = u^{2k}` inserted to the population
integral, times `N`, converges to `λ/β`. -/
theorem energy_ratio_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ψ : (Fin (n + 1) → ℝ) → ℝ) (hψc : Continuous ψ) (hA : amplitudeCoeff h k l β ψ ≠ 0) :
    Tendsto (fun N => N * (origPhaseIntegral n h k β N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) / origPhaseIntegral n h k β N 1 (fun _ => 0) ψ))
      atTop (𝓝 (l / β)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- the numerator is the population integral with the shifted weight
  have hshift : ∀ N, origPhaseIntegral n h k β N 1 (fun _ => 0)
      (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) =
      origPhaseIntegral n (fun i => h i + 2 * k i) k β N 1 (fun _ => 0) ψ := fun N =>
    origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => 0) ψ (fun i => 2 * k i)
  have hA' : amplitudeCoeff (fun i => h i + 2 * k i) k (l + 1) β ψ ≠ 0 := by
    rw [amplitudeCoeff_add_two_k h k hk hl hβ]
    exact mul_ne_zero (div_ne_zero hl.ne' hβ.ne') hA
  have hn := population_isEquivalent n (fun i => h i + 2 * k i) k hk β hβ
    (hmin_add_two_k h k hk hmin) (hatt_add_two_k h k hk hatt) ψ hψc hA'
  rw [amplitudeCoeff_add_two_k h k hk hl hβ, multCount_add_two_k h k hk l] at hn
  have hd := population_isEquivalent n h k hk β hβ hmin hatt ψ hψc hA
  have hq := isEquivalent_quotient_powLog hn hd hA
  have hmul := (IsEquivalent.refl (u := fun N : ℝ => N) (l := atTop)).mul hq
  simp_rw [hshift]
  refine hmul.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.mul_apply]
  rw [show -(l + 1 - l) = (-1 : ℝ) by ring, Real.rpow_neg_one, div_self hlog,
    mul_div_assoc, div_self hA]
  field_simp

/-- `β = 1`: `n E_n[K] → λ`, the posterior expected KL divergence decays as `λ/n`. -/
theorem energy_ratio_tendsto_one (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (ψ : (Fin (n + 1) → ℝ) → ℝ) (hψc : Continuous ψ) (hA : amplitudeCoeff h k l 1 ψ ≠ 0) :
    Tendsto (fun N => N * (origPhaseIntegral n h k 1 N 1 (fun _ => 0)
        (fun u => (∏ i, u i ^ (2 * k i)) * ψ u) / origPhaseIntegral n h k 1 N 1 (fun _ => 0) ψ))
      atTop (𝓝 l) := by
  have := energy_ratio_tendsto n h k hk 1 one_pos hmin hatt ψ hψc hA
  rwa [div_one] at this

end Grammar
```

### Grammar/PopulationEnergyAssembled.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationAssembly
import Grammar.PopulationEnergy

/-!
# The energy observable after finite chart assembly (Astra #37 P5, unit 305)

With the same charts, tangential measures and zero-noise data as the denominator, inserting
`K∘π = u^{2k_I}` on chart `I` is the weight change `h_I ↦ h_I + 2k_I`; the global first candidate
moves from `(μ_*, m_*−1)` to `(μ_*+1, m_*−1)` with the same tied charts, and the assembled face
functional becomes `(μ_*/β) A_*` (`assembledFace_add_two_k`: every tied chart has `λ_I = μ_*`, so
each contribution is multiplied by `μ_*/β`). Hence, for
```
𝒵_pop[1] = ∑_I 𝒵^I(h_I) + E,        𝒵_pop[K] = ∑_I 𝒵^I(h_I + 2k_I) + E_K
```
with residuals negligible at the respective scales and `A_* ≠ 0`,
```
N · 𝒵_pop[K](N) / 𝒵_pop[1](N) → μ_*/β                     (energy_ratio_assembled_tendsto)
```
(`β = 1`: `n E_n[K] → λ`, the global RLCT). Conditional on the two external decompositions; if
`A_* = 0` the first-candidate theorems do not justify the conclusion. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- The chart face functional of the shifted weight is `λ_I/β` times the original. -/
theorem chartFace_add_two_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (lam : Fin M → ℝ) (hlam : ∀ I, 0 < lam I) (I : Fin M) :
    chartFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) I =
      lam I / β * chartFace ν h k β x lam I := by
  unfold chartFace
  rw [← integral_const_mul]
  congr 1
  funext v
  exact amplitudeCoeff_add_two_k (h I) (k I) (hk I) (hlam I) hβ _

omit [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]
  [∀ I, IsFiniteMeasure (ν I)] in
/-- **The assembled face functional of the energy observable is `(μ_*/β) A_*`.** -/
theorem assembledFace_add_two_k (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (lam : Fin M → ℝ) (hlam : ∀ I, 0 < lam I) (μs : ℝ) (ms : ℕ) :
    assembledFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) (μs + 1) ms =
      μs / β * assembledFace ν h k β x lam μs ms := by
  unfold assembledFace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [add_left_inj, multCount_add_two_k (h I) (k I) (hk I) (lam I)]
  split_ifs with hI
  · rw [chartFace_add_two_k ν h k β hk hβ x lam hlam I, hI.1]
  · rw [mul_zero]

/-- **`N · E_N[K∘π] → μ_*/β` after finite chart assembly**: for zero-noise joint data, external
decompositions of the population integrals with and without the energy inserted (with residuals
negligible at the respective first-candidate scales), and `A_* ≠ 0`. -/
theorem energy_ratio_assembled_tendsto (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms)
    (Zpop E ZK EK : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hdecompK : ∀ N, ZK N = gInt ν (fun I i => h I i + 2 * k I i) k β (fun _ => 1) x N + EK N)
    (hEK : Tendsto (fun N => EK N / (N ^ (-(μs + 1)) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Tendsto (fun N => N * (ZK N / Zpop N)) atTop (𝓝 (μs / β)) := by
  have hlam : ∀ I, 0 < lam I := fun I => by
    obtain ⟨i, hi⟩ := hatt I
    rw [← hi]
    exact ratioExp_pos (h I) (k I) (hk I) i
  have hμs : 0 < μs := by
    obtain ⟨I, hI⟩ := hμatt
    rw [← hI]
    exact hlam I
  -- the denominator
  have hd := population_assembled_isEquivalent ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt
    Zpop E hdecomp hE hA
  -- the numerator: shifted weights
  have hminK : ∀ I i, lam I + 1 ≤ ratioExp (fun i => h I i + 2 * k I i) (k I) i := fun I =>
    hmin_add_two_k (h I) (k I) (hk I) (hmin I)
  have hattK : ∀ I, ∃ i, ratioExp (fun i => h I i + 2 * k I i) (k I) i = lam I + 1 := fun I =>
    hatt_add_two_k (h I) (k I) (hk I) (hatt I)
  have hμK : ∀ I, μs + 1 ≤ lam I + 1 := fun I => by linarith [hμ I]
  have hμattK : ∃ I, lam I + 1 = μs + 1 := by
    obtain ⟨I, hI⟩ := hμatt
    exact ⟨I, by rw [hI]⟩
  have hmK : ∀ I, lam I + 1 = μs + 1 →
      multCount (ratioExp (fun i => h I i + 2 * k I i) (k I)) (lam I + 1) ≤ ms := fun I hI => by
    rw [multCount_add_two_k (h I) (k I) (hk I)]
    exact hm I (add_left_inj 1 |>.1 hI)
  have hmattK : ∃ I, lam I + 1 = μs + 1 ∧
      multCount (ratioExp (fun i => h I i + 2 * k I i) (k I)) (lam I + 1) = ms := by
    obtain ⟨I, hI1, hI2⟩ := hmatt
    exact ⟨I, by rw [hI1], by rw [multCount_add_two_k (h I) (k I) (hk I)]; exact hI2⟩
  have hAK : assembledFace ν (fun I i => h I i + 2 * k I i) k β x (fun I => lam I + 1) (μs + 1)
      ms ≠ 0 := by
    rw [assembledFace_add_two_k ν h k β hk hβ x lam hlam μs ms]
    exact mul_ne_zero (div_ne_zero hμs.ne' hβ.ne') hA
  have hn := population_assembled_isEquivalent ν (fun I i => h I i + 2 * k I i) k β hk hβ x hx
    (fun I => lam I + 1) hminK hattK hμK hμattK hmK hmattK ZK EK hdecompK hEK hAK
  rw [assembledFace_add_two_k ν h k β hk hβ x lam hlam μs ms] at hn
  have hq := isEquivalent_quotient_powLog hn hd hA
  have hmul := (IsEquivalent.refl (u := fun N : ℝ => N) (l := atTop)).mul hq
  refine hmul.symm.tendsto_nhds (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ^ (ms - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  simp only [Pi.mul_apply]
  rw [show -(μs + 1 - μs) = (-1 : ℝ) by ring, Real.rpow_neg_one, div_self hlog,
    mul_div_assoc, div_self hA]
  field_simp

end Grammar
```

## Questions
1. u302: is `isEquivalent_quotient_powLog` the faithful Corollary B core (log shift as a natural-power quotient; `Cd ≠ 0` only), and are the three case theorems correct, including the power-decay squeeze (`log^jn/log^jd ≤ (1+log N)^jn` for `N ≥ e`)?
2. u303: is the bounded-observable inequality stated for the right objects (continuous `φ`, `c ≥ 0` on the box, `|φ| ≤ B` on the box, population weight nonnegative), and is `not_precedes_of_bounded_quotient` sound (equivalence ⇒ `q/R → 1` ⇒ `|q| ≥ |R|/2` eventually; `|R| → ∞` in the two excluded cases via `N^{s}/log^{jd} → ∞` and `log^{jn−jd} → ∞`; contradiction with the bound)? Any hypothesis missing (e.g. `Cn ≠ 0` is used for `R ≠ 0` eventually)?
3. u304: is `amplitudeCoeff_add_two_k` correct — ratios shift by exactly one (`ratioExp_add_two_k`), minimiser set/multiplicity/face projection/residual weight unchanged, `Γ(λ+1)β^{-(λ+1)} = (λ/β) Γ(λ)β^{-λ}` — and does `energy_ratio_tendsto` deliver `N·E_N[K∘π] → λ/β` at chart level with the right hypotheses (`ψ` continuous, `A ≠ 0`; `K∘π = u^{2k}` inserted as the monomial factor `∏ uᵢ^{2kᵢ}`)? Is the docstring's non-claim list right (no `𝒵_n[K] = −𝒵_n'(n)`, no `−(m−1)/(n log n)` correction)?
4. u305: is the assembled statement faithful (same charts/data for numerator and denominator; numerator = shifted weights `h_I + 2k_I` with the SAME zero-noise data `x`; `assembledFace_add_two_k`; two external decompositions with residuals negligible at the respective scales; `A_* ≠ 0`), and is `N·𝒵_pop[K]/𝒵_pop[1] → μ_*/β` the right conclusion (`β = 1`: the global RLCT)?
5. Release audit: the 20-unit programme has 4 units left for the audit (HEADLINES release block, hand-off report, mirror annotations, author note). Please give (a) the one-paragraph release statement for Programme P (what is proved, in the paper's terms, and what remains external), (b) the final list of non-claims to reproduce in the headline documentation and the author note, (c) any last statement-level corrections before freezing, and (d) whether anything in P1–P5 should NOT be labelled with the paper's labels (`thm:expectation_expansion`, `eq:thm_leading_coeff`, `eq:lambda_I_f`, `eq:mu_I_phi`, `eq:expectation_leading`, `ex:phi_equals_K`) in the mirror annotations, given that the paper's statements are being rewritten.

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
