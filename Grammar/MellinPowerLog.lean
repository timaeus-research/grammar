/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.MellinTransform

/-!
# The Mellin transform of `N^{−μ} (log N)^q` on `[1, ∞)` (§20, the fluctuation zeta function)

`hasMellin_powLogIci : HasMellin (𝟙_{[1,∞)} N^{−μ} (log N)^q) s (q! / (μ − s)^{q+1})` for
`Re s < μ` — the elementary Mellin lemma behind the principal parts of the zeta function of a
cutoff expansion.  Route: the `(0,1]` power `t^μ (log t)^q` has transform `(−1)^q q!/(s+μ)^{q+1}`
for `Re s > −μ` (Mathlib's `hasMellin_cpow_Ioc` at `q = 0`, then differentiation in `s`:
`d/ds mellin f = mellin (log · f)`, `mellin_hasDerivAt_of_isBigO_rpow`), and inversion
`t ↦ t⁻¹` (`mellin_comp_inv`) carries it to `[1, ∞)`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- `t^μ (log t)^q` on `(0,1]`, as a complex-valued function on `ℝ`. -/
noncomputable def powLogIoc (μ : ℝ) (q : ℕ) : ℝ → ℂ :=
  indicator (Ioc (0 : ℝ) 1) fun t => (t : ℂ) ^ (μ : ℂ) * (Real.log t : ℂ) ^ q

/-- `N^{−μ} (log N)^q` on `[1, ∞)`, as a complex-valued function on `ℝ`. -/
noncomputable def powLogIci (μ : ℝ) (q : ℕ) : ℝ → ℂ :=
  indicator (Ici (1 : ℝ)) fun N => (N : ℂ) ^ (-(μ : ℂ)) * (Real.log N : ℂ) ^ q

theorem powLogIoc_zero (μ : ℝ) :
    powLogIoc μ 0 = indicator (Ioc (0 : ℝ) 1) fun t => (t : ℂ) ^ (μ : ℂ) := by
  funext t
  simp [powLogIoc]

theorem powLogIoc_succ (μ : ℝ) (q : ℕ) :
    powLogIoc μ (q + 1) = fun t => Real.log t • powLogIoc μ q t := by
  funext t
  unfold powLogIoc
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [indicator_of_mem ht, Complex.real_smul, pow_succ]
    ring
  · simp [indicator_of_notMem ht]

theorem norm_powLogIoc_le {μ : ℝ} {q : ℕ} {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖powLogIoc μ q t‖ = t ^ μ * |Real.log t| ^ q := by
  unfold powLogIoc
  rw [indicator_of_mem ht, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    ← Complex.ofReal_cpow ht.1.le, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]

theorem isBigO_powLogIoc_atTop (μ : ℝ) (q : ℕ) (a : ℝ) :
    powLogIoc μ q =O[atTop] fun t : ℝ => t ^ (-a) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.2 ht)
  simp [powLogIoc, indicator_of_notMem hnot]

theorem isBigO_powLogIoc_zero (μ : ℝ) (q : ℕ) {b : ℝ} (hb : -μ < b) :
    powLogIoc μ q =O[𝓝[>] 0] fun t : ℝ => t ^ (-b) := by
  induction q generalizing b with
  | zero =>
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    rw [norm_powLogIoc_le ht', pow_zero, mul_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith)
  | succ q ih =>
    have hmid : -μ < (b + -μ) / 2 := by linarith
    have h := isBigO_rpow_zero_log_smul (by linarith : (b + -μ) / 2 < b) (ih hmid)
    rwa [← powLogIoc_succ] at h

theorem continuousOn_powLog (μ : ℝ) (q : ℕ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (μ : ℂ) * (Real.log t : ℂ) ^ q) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ((Complex.continuous_ofReal.comp_continuousOn
    (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)).pow q)
  intro t ht
  have : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (μ : ℂ)) t :=
    (Complex.continuousAt_ofReal_cpow_const t μ (Or.inr (ne_of_gt ht)))
  exact this.continuousWithinAt

theorem locallyIntegrableOn_powLogIoc (μ : ℝ) (q : ℕ) :
    LocallyIntegrableOn (powLogIoc μ q) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  exact ((continuousOn_powLog μ q).mono hK).integrableOn_compact hKc |>.indicator measurableSet_Ioc

/-- ★ `∫_0^1 t^{s+μ−1} (log t)^q dt = (−1)^q q!/(s+μ)^{q+1}` for `Re s > −μ`. -/
theorem hasMellin_powLogIoc (μ : ℝ) (q : ℕ) {s : ℂ} (hs : -μ < s.re) :
    HasMellin (powLogIoc μ q) s ((-1) ^ q * (q.factorial : ℂ) / (s + μ) ^ (q + 1)) := by
  induction q generalizing s with
  | zero =>
    have h := hasMellin_cpow_Ioc (μ : ℂ) (s := s) (by simp only [Complex.ofReal_re]; linarith)
    rw [powLogIoc_zero]
    simpa using h
  | succ q ih =>
    have hsμ : s + μ ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    -- the derivative of the closed form
    have hD : HasDerivAt (fun z : ℂ => (-1) ^ q * (q.factorial : ℂ) / (z + μ) ^ (q + 1))
        ((-1) ^ (q + 1) * ((q + 1).factorial : ℂ) / (s + μ) ^ (q + 1 + 1)) s := by
      have h1 : HasDerivAt (fun z : ℂ => (z + μ) ^ (q + 1))
          (((q + 1 : ℕ) : ℂ) * (s + μ) ^ q * 1) s :=
        ((hasDerivAt_id s).add_const (μ : ℂ)).pow (q + 1)
      have h2 := (h1.inv (pow_ne_zero _ hsμ)).const_mul ((-1) ^ q * (q.factorial : ℂ))
      refine h2.congr_deriv ?_
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    -- the Mellin derivative
    have hmid : -μ < (-μ + s.re) / 2 := by linarith
    obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow (locallyIntegrableOn_powLogIoc μ q)
      (isBigO_powLogIoc_atTop μ q (s.re + 1)) (by linarith)
      (isBigO_powLogIoc_zero μ q hmid) (by linarith)
    have heq : mellin (powLogIoc μ q) =ᶠ[𝓝 s]
        fun z : ℂ => (-1) ^ q * (q.factorial : ℂ) / (z + μ) ^ (q + 1) := by
      have hopen : IsOpen {z : ℂ | -μ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show s ∈ {z : ℂ | -μ < z.re} from hs)] with z hz
      exact (ih hz).2
    have hder' := hder.congr_of_eventuallyEq heq.symm
    have hval := hder'.unique hD
    refine ⟨?_, ?_⟩
    · rw [powLogIoc_succ]
      exact hconv
    · rw [powLogIoc_succ]
      exact hval

theorem powLogIci_eq_inv (μ : ℝ) (q : ℕ) {N : ℝ} (hN : 0 < N) :
    powLogIci μ q N = (-1) ^ q * powLogIoc μ q N⁻¹ := by
  unfold powLogIci powLogIoc
  have hmem : N ∈ Ici (1 : ℝ) ↔ N⁻¹ ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · intro h
      exact ⟨inv_pos.2 hN, inv_le_one_of_one_le₀ h⟩
    · intro h
      have := h.2
      rwa [inv_le_one₀ hN] at this
  by_cases h : N ∈ Ici (1 : ℝ)
  · rw [indicator_of_mem h, indicator_of_mem (hmem.1 h)]
    have h1 : ((N⁻¹ : ℝ) : ℂ) ^ (μ : ℂ) = (N : ℂ) ^ (-(μ : ℂ)) := by
      rw [← Complex.ofReal_cpow (inv_nonneg.2 hN.le), Real.inv_rpow hN.le, ← Real.rpow_neg hN.le,
        Complex.ofReal_cpow hN.le]
      push_cast
      rfl
    rw [h1, Real.log_inv]
    push_cast
    rw [neg_pow]
    have h2 : ((-1 : ℂ)) ^ q * (-1) ^ q = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (-((N : ℂ) ^ (-(μ : ℂ)) * (Real.log N : ℂ) ^ q)) * h2
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hmem.2 h'))]
    ring

theorem isBigO_powLogIci_zero (μ : ℝ) (q : ℕ) (b : ℝ) :
    powLogIci μ q =O[𝓝[>] 0] fun t : ℝ => t ^ (-b) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hnot : t ∉ Ici (1 : ℝ) := fun h => absurd h (not_le.2 ht.2)
  simp [powLogIci, indicator_of_notMem hnot]

theorem isBigO_powLogIci_atTop (μ : ℝ) (q : ℕ) {a : ℝ} (ha : a < μ) :
    powLogIci μ q =O[atTop] fun t : ℝ => t ^ (-a) := by
  induction q generalizing a with
  | zero =>
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hmem : t ∈ Ici (1 : ℝ) := ht
    unfold powLogIci
    rw [indicator_of_mem hmem, pow_zero, mul_one, one_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow ht0.le, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  | succ q ih =>
    have hmid : (a + μ) / 2 < μ := by linarith
    have h := isBigO_rpow_top_log_smul (by linarith : a < (a + μ) / 2) (ih hmid)
    refine h.congr_left fun t => ?_
    unfold powLogIci
    by_cases ht : t ∈ Ici (1 : ℝ)
    · simp only [indicator_of_mem ht, Complex.real_smul, pow_succ]
      ring
    · simp [indicator_of_notMem ht]

theorem locallyIntegrableOn_powLogIci (μ : ℝ) (q : ℕ) :
    LocallyIntegrableOn (powLogIci μ q) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  have hc : ContinuousOn (fun N : ℝ => (N : ℂ) ^ (-(μ : ℂ)) * (Real.log N : ℂ) ^ q) (Ioi 0) := by
    have := continuousOn_powLog (-μ) q
    simpa [Complex.ofReal_neg] using this
  exact (hc.mono hK).integrableOn_compact hKc |>.indicator measurableSet_Ici

/-- ★ **The elementary Mellin lemma**: `∫_1^∞ N^{s−μ−1} (log N)^q dN = q!/(μ − s)^{q+1}` for
`Re s < μ`. -/
theorem hasMellin_powLogIci (μ : ℝ) (q : ℕ) {s : ℂ} (hs : s.re < μ) :
    HasMellin (powLogIci μ q) s ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1)) := by
  have hmid : s.re < (s.re + μ) / 2 := by linarith
  have hconv : MellinConvergent (powLogIci μ q) s :=
    mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_powLogIci μ q)
      (isBigO_powLogIci_atTop μ q (by linarith : (s.re + μ) / 2 < μ)) hmid
      (isBigO_powLogIci_zero μ q (s.re - 1)) (by linarith)
  refine ⟨hconv, ?_⟩
  have hs' : -μ < (-s).re := by
    rw [Complex.neg_re]
    linarith
  have hIoc := hasMellin_powLogIoc μ q hs'
  have h1 : mellin (powLogIci μ q) s = mellin (fun t => (-1 : ℂ) ^ q • powLogIoc μ q t⁻¹) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun N hN => ?_
    simp only [smul_eq_mul]
    rw [powLogIci_eq_inv μ q hN]
  rw [h1, mellin_const_smul, mellin_comp_inv, hIoc.2, smul_eq_mul]
  have hμs : (μ : ℂ) - s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  rw [show (-s + (μ : ℂ)) = (μ : ℂ) - s by ring]
  have h2 : ((-1 : ℂ)) ^ q * (-1) ^ q = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [mul_div_assoc', ← mul_assoc, h2, one_mul]

end Grammar
