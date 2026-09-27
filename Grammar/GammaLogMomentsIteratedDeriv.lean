/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GammaThirdDerivDuplication
import Grammar.GaussJlogPowBridge

/-!
# The Gamma log-moments are the iterated derivatives of `Γ`: `D₄` modulo one symbol

The log-weighted kernels `k_r(t) = log^r t · e^{−t}` satisfy the growth hypotheses of Mathlib's
`mellin_hasDerivAt_of_isBigO_rpow` at every order (`O(t^{−a})` at infinity for every `a`,
`O(t^{−b})` near `0⁺` for every `b > 0`, by induction through `isBigO_rpow_top_log_smul` and
`isBigO_rpow_zero_log_smul`), so `d/ds M[k_r](s) = M[k_{r+1}](s)` on `Re s > 0`
(`hasDerivAt_mellin_gammaLogKernel`) and by induction `Γ^{(r)}(s) = M[k_r](s)` there
(★★ `iterate_deriv_Gamma_eq_mellin`, DCVIII's `deriv_Gamma_eq_mellin` at every order).  At
`s = 1` this identifies every Gamma log-moment `G_r = ∫₀^∞ e^{−u} log^r u du` (DCLXVIII) with
`Γ^{(r)}(1)` (★★★ `gammaOneLogMoment_eq_iterate`), at `s = ½` every half-point moment `H_j`
(DCVIII) with `Γ^{(j)}(½)` (`gammaLogMoment_eq_iterate`); in particular `G₃ = Γ'''(1)`
(`gammaOneLogMoment_three_eq`), so the second Gaussian log-moment `J₂` and with DCLXXII the
depth-four constant are closed modulo the single symbol `λ₃ = Γ'''(1) + γ³ + γπ²/2`:

  ★★★ `depthFourConst_eq_logThird : D₄ = (2b³ + 7π²b − 6λ₃)/(24π√(2π))`, `b = 5 log 2 − 3γ`.

Examples_slop §2; Astra round 23 target 2.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### The log-weighted Gamma kernels -/

/-- `k_r(t) = log^r t · e^{−t}` (as a complex function), defined so that
`k_{r+1} = log · k_r` is definitional. -/
noncomputable def gammaLogKernel : ℕ → ℝ → ℂ
  | 0 => fun t => ((Real.exp (-t) : ℝ) : ℂ)
  | r + 1 => fun t => Real.log t • gammaLogKernel r t

theorem gammaLogKernel_zero : gammaLogKernel 0 = fun t => ((Real.exp (-t) : ℝ) : ℂ) := rfl

theorem gammaLogKernel_succ (r : ℕ) :
    gammaLogKernel (r + 1) = fun t => Real.log t • gammaLogKernel r t := rfl

theorem gammaLogKernel_apply (r : ℕ) (t : ℝ) :
    gammaLogKernel r t = ((Real.exp (-t) * Real.log t ^ r : ℝ) : ℂ) := by
  induction r with
  | zero => simp [gammaLogKernel_zero]
  | succ r ih =>
    rw [gammaLogKernel_succ]
    change Real.log t • gammaLogKernel r t = _
    rw [ih, Complex.real_smul]
    push_cast
    ring

theorem gammaLogKernel_isBigO_atTop (r : ℕ) (a : ℝ) :
    gammaLogKernel r =O[atTop] (· ^ (-a)) := by
  induction r generalizing a with
  | zero => exact exp_neg_isBigO_rpow_atTop a
  | succ r ih =>
    rw [gammaLogKernel_succ]
    exact isBigO_rpow_top_log_smul (lt_add_one a) (ih (a + 1))

theorem gammaLogKernel_isBigO_zero (r : ℕ) {b : ℝ} (hb : 0 < b) :
    gammaLogKernel r =O[𝓝[>] 0] (· ^ (-b)) := by
  induction r generalizing b with
  | zero =>
    rw [gammaLogKernel_zero]
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht.1 _), one_mul]
    exact (Real.exp_le_one_iff.2 (by linarith [ht.1])).trans
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le (by linarith))
  | succ r ih =>
    rw [gammaLogKernel_succ]
    exact isBigO_rpow_zero_log_smul (by linarith : b / 2 < b) (ih (by linarith))

theorem continuousOn_gammaLogKernel (r : ℕ) : ContinuousOn (gammaLogKernel r) (Ioi 0) := by
  induction r with
  | zero =>
    rw [gammaLogKernel_zero]
    exact Continuous.continuousOn (by fun_prop)
  | succ r ih =>
    rw [gammaLogKernel_succ]
    exact ContinuousOn.smul (Real.continuousOn_log.mono fun t ht => ne_of_gt ht) ih

theorem locallyIntegrableOn_gammaLogKernel (r : ℕ) :
    LocallyIntegrableOn (gammaLogKernel r) (Ioi 0) :=
  (continuousOn_gammaLogKernel r).locallyIntegrableOn measurableSet_Ioi

/-- `d/ds M[k_r](s) = M[k_{r+1}](s)` on `Re s > 0`. -/
theorem hasDerivAt_mellin_gammaLogKernel (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (mellin (gammaLogKernel r)) (mellin (gammaLogKernel (r + 1)) s) s := by
  rw [gammaLogKernel_succ]
  exact (mellin_hasDerivAt_of_isBigO_rpow (locallyIntegrableOn_gammaLogKernel r)
    (gammaLogKernel_isBigO_atTop r (s.re + 1)) (by linarith)
    (gammaLogKernel_isBigO_zero r (b := s.re / 2) (by linarith)) (by linarith)).2

/-! ### `Γ^{(r)} = M[log^r t · e^{−t}]` -/

/-- ★★ `Γ^{(r)}(s) = ∫₀^∞ t^{s−1} log^r t e^{−t} dt` for `Re s > 0`, every `r`. -/
theorem iterate_deriv_Gamma_eq_mellin (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    deriv^[r] Complex.Gamma s = mellin (gammaLogKernel r) s := by
  induction r generalizing s with
  | zero =>
    simp only [Function.iterate_zero, id_eq, gammaLogKernel_zero]
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral_eq_mellin]
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hev : deriv^[r] Complex.Gamma =ᶠ[𝓝 s] mellin (gammaLogKernel r) := by
      filter_upwards [isOpen_re_pos.mem_nhds hs] with z hz
      exact ih hz
    rw [hev.deriv_eq, (hasDerivAt_mellin_gammaLogKernel r hs).deriv]

/-- ★★★ **`G_r = Γ^{(r)}(1)`** for every `r`. -/
theorem gammaOneLogMoment_eq_iterate (r : ℕ) :
    ((gammaOneLogMoment r : ℝ) : ℂ) = deriv^[r] Complex.Gamma 1 := by
  rw [iterate_deriv_Gamma_eq_mellin r (by norm_num)]
  unfold mellin gammaOneLogMoment
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, Complex.cpow_zero, one_smul, gammaLogKernel_apply]

/-- ★★ **`H_j = Γ^{(j)}(½)`** for every `j` (DCVIII's `gammaLogMoment_two_eq` at every order). -/
theorem gammaLogMoment_eq_iterate (j : ℕ) :
    ((gammaLogMoment j : ℝ) : ℂ) = deriv^[j] Complex.Gamma (1 / 2) := by
  rw [iterate_deriv_Gamma_eq_mellin j (by norm_num)]
  unfold mellin gammaLogMoment
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [smul_eq_mul, gammaLogKernel_apply]
  push_cast
  rw [Complex.ofReal_cpow ht0.le]
  push_cast
  ring_nf

/-- `G₃ = Γ'''(1)`. -/
theorem gammaOneLogMoment_three_eq : gammaOneLogMoment 3 = gammaThirdOne := by
  unfold gammaThirdOne
  have h := gammaOneLogMoment_eq_iterate 3
  rw [show deriv^[3] Complex.Gamma = deriv (deriv (deriv Complex.Gamma)) from rfl] at h
  rw [← h, Complex.ofReal_re]

/-- `G₂ = Γ''(1)` regression: the DCLXVIII value agrees with DCXXXVIII's. -/
theorem gammaOneLogMoment_two_eq_iterate :
    ((gammaOneLogMoment 2 : ℝ) : ℂ) = deriv (deriv Complex.Gamma) 1 :=
  gammaOneLogMoment_eq_iterate 2

/-! ### `J₂` and `D₄` modulo one symbol -/

theorem gammaOneLogMoment_three_eq_logThird :
    gammaOneLogMoment 3 = gammaLogThirdOne - Real.eulerMascheroniConstant ^ 3 -
      Real.eulerMascheroniConstant * Real.pi ^ 2 / 2 := by
  rw [gammaOneLogMoment_three_eq]
  unfold gammaLogThirdOne
  ring

/-- `J₂ = ⅛[log³2/3 − γ log²2 + (γ² + π²/6) log 2 + (λ₃ − γ³ − γπ²/2)/3]`. -/
theorem gaussJlog2_eq_logThird :
    gaussJlog2 = (1 / 8) * (Real.log 2 ^ 3 / 3 - Real.log 2 ^ 2 * Real.eulerMascheroniConstant +
      Real.log 2 * (Real.eulerMascheroniConstant ^ 2 + Real.pi ^ 2 / 6) +
      (gammaLogThirdOne - Real.eulerMascheroniConstant ^ 3 -
        Real.eulerMascheroniConstant * Real.pi ^ 2 / 2) / 3) := by
  rw [gaussJlog2_eq_gammaOneLogMoment, gammaOneLogMoment_one, gammaOneLogMoment_two,
    gammaOneLogMoment_three_eq_logThird]
  ring

/-- ★★★ **The depth-four constant modulo one symbol**:
`D₄ = (2b³ + 7π²b − 6λ₃)/(24π√(2π))`, `b = 5 log 2 − 3γ`. -/
theorem depthFourConst_eq_logThird :
    depthFourConst =
      (2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) ^ 3 +
        7 * Real.pi ^ 2 * (5 * Real.log 2 - 3 * Real.eulerMascheroniConstant) -
        6 * gammaLogThirdOne) / (24 * Real.pi * Real.sqrt (2 * Real.pi)) := by
  unfold depthFourConst
  rw [gaussJlog2_eq_logThird, gaussJlog_eq, depthThreeConst_eq, depthFourQint_eq_logThird]
  unfold gaussR₀ depthThreeJetLinear
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp
  ring

end Grammar
