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
