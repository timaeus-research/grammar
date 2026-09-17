/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CutoffExpansionIntegral
import Grammar.PopulationDerivative
import Grammar.EmpiricalMonomialFamily
import Grammar.EmpiricalLeadingConsistency

/-!
# The monomial shift identity for the population coefficients

The population coefficients of the amplitude `u^{2k} η` at exponent `μ + 1` are read off those of
`η` at `μ`: since `u^{2k} e^{−N u^{2k}} = −∂_N e^{−N u^{2k}}`, the population integral of `η` is the
tail integral of that of `u^{2k} η` (`PopulationDerivative`), and integrating the cutoff expansion
term by term (`CutoffExpansionIntegral`) identifies the coefficients through canonicity.  The
result is the exact recursion

`C_{μ+1,q}[u^{2k} η] = μ · C_{μ,q}[η] − (q+1) · C_{μ,q+1}[η]`  (`empCoeff_mono_mul_shift`),

with `C_{μ+1,d−1}[u^{2k} η] = μ · C_{μ,d−1}[η]` at the top log order.  Iterating,
`|C_{μ₀+j,q}[u^{2jk} η]| ≤ Π_{i<j} (μ₀ + i + d − 1) · max_q |C_{μ₀,q}[η]|`
(`abs_empCoeff_mono_pow_le`): the Gamma growth of the Wick terms at FIXED depth data of `μ₀`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- The monomial factor `u^{2k}` is absorbed into the weight. -/
theorem empIntegral_mono_mul (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (N : ℝ) :
    empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k N =
      empIntegral η (fun _ => 0) (fun i => h i + 2 * k i) k N := by
  rw [empIntegral_zero_eq, empIntegral_zero_eq]
  refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
  rw [← mono_mul_mono h (fun i => 2 * k i) v]
  ring

theorem contDiff_mono_mul (hη : ContDiff ℝ ∞ η) (a : Fin d → ℕ) :
    ContDiff ℝ ∞ fun v => mono a v * η v :=
  (contDiff_mono a).mul hη

/-- The coefficients of `u^{2k} η` with weight `h` are those of `η` with weight `h + 2k`. -/
theorem empCoeff_mono_mul_eq (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k μ q =
      empCoeff η (fun _ => 0) (fun i => h i + 2 * k i) k μ q := by
  have hc : CutoffExpansion (Qamb k) (d - 1)
      (empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k)
      (empCoeff η (fun _ => 0) (fun i => h i + 2 * k i) k) := by
    have := emp_cutoffExpansion (ζ := fun _ => (0 : ℝ)) (h := fun i => h i + 2 * k i) hη
      contDiff_const hk
    rwa [show empIntegral η (fun _ => 0) (fun i => h i + 2 * k i) k =
      empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k from
      funext fun N => (empIntegral_mono_mul η h k N).symm] at this
  exact (empCoeff_unique (contDiff_mono_mul hη _) contDiff_const hk hc hμ hq).symm

/-- The coefficients of `u^{2k} η` vanish at every exponent `≤ 1`. -/
theorem empCoeff_mono_mul_eq_zero_of_le_one (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {m : ℕ}
    (hm : (m : ℝ) / Qamb k ≤ 1) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k ((m : ℝ) / Qamb k) q
      = 0 := by
  rw [empCoeff_mono_mul_eq hη hk ⟨m, rfl⟩ hq]
  have hBL : BoxLeading (fun i => h i + 2 * k i) k 1 0 := by
    have := boxLeading_shift h k hk 2
    rwa [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num] at this
  rcases hm.lt_or_eq with hlt | heq
  · exact empCoeff_eq_zero_of_boxLeading_lt _ k hk hBL hlt q
  · rw [heq]
    exact empCoeff_eq_zero_of_boxLeading_deg _ k hk hBL (Nat.zero_le q)

/-- ★★ **The population integral of `η` has the integrated expansion of that of `u^{2k} η`**. -/
theorem cutoffExpansion_empIntegral_zero_intCoeff (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) :
    CutoffExpansion (Qamb k) (d - 1) (empIntegral η (fun _ => 0) h k)
      (intCoeff (d - 1)
        (empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k)) := by
  have hQ := Qamb_pos k hk
  have hη' := contDiff_mono_mul hη (fun i => 2 * k i)
  have hexp : CutoffExpansion (Qamb k) (d - 1)
      (empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k)
      (empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k) :=
    emp_cutoffExpansion hη' contDiff_const hk
  have hcont := continuous_empIntegral_zero hη' h k
  have hlow : ∀ m : ℕ, (m : ℝ) / Qamb k ≤ 1 → ∀ q ≤ d - 1,
      empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k ((m : ℝ) / Qamb k) q
        = 0 :=
    fun m hm q hq => empCoeff_mono_mul_eq_zero_of_le_one hη hk hm hq
  refine (hexp.integral_Ioi hQ hcont hlow).congr_eventually ?_
  filter_upwards [hexp.eventually_integrableOn_Ioi hQ hcont hlow] with N hN
  have hderiv : ∀ t ∈ Ioi N, HasDerivAt (empIntegral η (fun _ => 0) h k)
      (-(empIntegral (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k t)) t :=
    fun t _ => hasDerivAt_empIntegral_zero hη h k t
  have hcontZ : ContinuousWithinAt (empIntegral η (fun _ => 0) h k) (Ici N) N :=
    (continuous_empIntegral_zero hη h k).continuousWithinAt
  have hfund := integral_Ioi_of_hasDerivAt_of_tendsto hcontZ hderiv hN.neg
    (tendsto_empIntegral_zero_atTop hη h k)
  rw [integral_neg] at hfund
  linarith

/-- The population coefficients of `η` are the integrated coefficients of `u^{2k} η`. -/
theorem empCoeff_eq_intCoeff (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff η (fun _ => 0) h k μ q = intCoeff (d - 1)
      (empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k) μ q :=
  (empCoeff_unique hη contDiff_const hk (cutoffExpansion_empIntegral_zero_intCoeff hη hk) hμ
    hq).symm

/-- ★★★ **The monomial shift identity**:
`C_{μ+1,q}[u^{2k} η] = μ · C_{μ,q}[η] − (q+1) · C_{μ,q+1}[η]` for `q < d − 1`. -/
theorem empCoeff_mono_mul_shift (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) {q : ℕ} (hq : q < d - 1) :
    empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k (μ + 1) q =
      μ * empCoeff η (fun _ => 0) h k μ q - (q + 1) * empCoeff η (fun _ => 0) h k μ (q + 1) := by
  rw [← intCoeff_shift (empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k)
    hμ0 hq.le, empCoeff_eq_intCoeff hη hk hμ hq.le, empCoeff_eq_intCoeff hη hk hμ hq]

/-- ★★★ **The monomial shift identity at the top log order**:
`C_{μ+1,d−1}[u^{2k} η] = μ · C_{μ,d−1}[η]`. -/
theorem empCoeff_mono_mul_shift_top (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) :
    empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k (μ + 1) (d - 1) =
      μ * empCoeff η (fun _ => 0) h k μ (d - 1) := by
  have := intCoeff_shift (empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k)
    hμ0 (le_refl (d - 1))
  rw [intCoeff_eq_zero_of_lt _ _ (Nat.lt_succ_self (d - 1)), mul_zero, sub_zero] at this
  rw [← this, empCoeff_eq_intCoeff hη hk hμ le_rfl]

/-- ★ **One shift loses at most a factor `μ + d − 1`** on the sup over log orders. -/
theorem abs_empCoeff_mono_mul_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ0 : 0 < μ) {B : ℝ}
    (hB : ∀ q ≤ d - 1, |empCoeff η (fun _ => 0) h k μ q| ≤ B) :
    ∀ q ≤ d - 1, |empCoeff (fun v => mono (fun i => 2 * k i) v * η v) (fun _ => 0) h k (μ + 1) q|
      ≤ (μ + ((d - 1 : ℕ) : ℝ)) * B := by
  intro q hq
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hd0 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases hq.lt_or_eq with hlt | heq
  · rw [empCoeff_mono_mul_shift hη hk hμ hμ0 hlt]
    have hq1 : ((q : ℝ) + 1) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hlt
    calc |μ * empCoeff η (fun _ => 0) h k μ q - (q + 1) * empCoeff η (fun _ => 0) h k μ (q + 1)|
        ≤ μ * |empCoeff η (fun _ => 0) h k μ q| +
            (q + 1) * |empCoeff η (fun _ => 0) h k μ (q + 1)| := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_pos hμ0, abs_of_pos (by positivity : (0 : ℝ) < q + 1)]
      _ ≤ μ * B + (q + 1) * B :=
          add_le_add (mul_le_mul_of_nonneg_left (hB q hq) hμ0.le)
            (mul_le_mul_of_nonneg_left (hB (q + 1) hlt) (by positivity))
      _ ≤ (μ + ((d - 1 : ℕ) : ℝ)) * B := by nlinarith
  · subst heq
    rw [empCoeff_mono_mul_shift_top hη hk hμ hμ0, abs_mul, abs_of_pos hμ0]
    calc μ * |empCoeff η (fun _ => 0) h k μ (d - 1)| ≤ μ * B :=
          mul_le_mul_of_nonneg_left (hB _ le_rfl) hμ0.le
      _ ≤ (μ + ((d - 1 : ℕ) : ℝ)) * B := by nlinarith

theorem mono_two_mul_succ (k : Fin d → ℕ) (j : ℕ) (v : Fin d → ℝ) :
    mono (fun i => 2 * k i) v * mono (fun i => 2 * j * k i) v =
      mono (fun i => 2 * (j + 1) * k i) v := by
  rw [mono_mul_mono]
  congr 1
  funext i
  ring

theorem mono_zero_exp (k : Fin d → ℕ) (v : Fin d → ℝ) : mono (fun i => 2 * 0 * k i) v = 1 := by
  simp [mono]

/-- The lattice is stable under integer shifts. -/
theorem lattice_add_nat (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (j : ℕ) :
    ∃ m : ℕ, μ + j = (m : ℝ) / Qamb k := by
  obtain ⟨m, hm⟩ := hμ
  have hQ : (0 : ℝ) < Qamb k := by exact_mod_cast Qamb_pos k hk
  refine ⟨m + j * Qamb k, ?_⟩
  rw [hm]
  push_cast
  field_simp

/-- ★★★ **The iterated shift bound — Gamma growth at fixed depth**:
`|C_{μ₀+j,q}[u^{2jk} η]| ≤ Π_{i<j} (μ₀ + i + d − 1) · B` whenever `|C_{μ₀,q}[η]| ≤ B` for all
`q ≤ d − 1`. -/
theorem abs_empCoeff_mono_pow_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {μ₀ : ℝ}
    (hμ₀ : ∃ m : ℕ, μ₀ = (m : ℝ) / Qamb k) (hμ₀pos : 0 < μ₀) {B : ℝ}
    (hB : ∀ q ≤ d - 1, |empCoeff η (fun _ => 0) h k μ₀ q| ≤ B) (j : ℕ) :
    ∀ q ≤ d - 1, |empCoeff (fun v => mono (fun i => 2 * j * k i) v * η v) (fun _ => 0) h k
      (μ₀ + j) q| ≤ (∏ i ∈ range j, (μ₀ + i + ((d - 1 : ℕ) : ℝ))) * B := by
  induction j with
  | zero =>
    intro q hq
    have hamp : (fun v => mono (fun i => 2 * 0 * k i) v * η v) = η := by
      funext v
      rw [mono_zero_exp, one_mul]
    rw [hamp, prod_range_zero, one_mul, Nat.cast_zero, add_zero]
    exact hB q hq
  | succ j ih =>
    intro q hq
    have hpos : 0 < μ₀ + j := by positivity
    have h1 := abs_empCoeff_mono_mul_le (contDiff_mono_mul hη (fun i => 2 * j * k i)) hk
      (lattice_add_nat hk hμ₀ j) hpos ih q hq
    have hamp : (fun v => mono (fun i => 2 * k i) v *
        ((fun v => mono (fun i => 2 * j * k i) v * η v) v)) =
        fun v => mono (fun i => 2 * (j + 1) * k i) v * η v := by
      funext v
      simp only []
      rw [← mul_assoc, mono_two_mul_succ]
    rw [hamp, show μ₀ + j + 1 = μ₀ + ((j + 1 : ℕ) : ℝ) by push_cast; ring] at h1
    rw [prod_range_succ]
    calc _ ≤ (μ₀ + j + ((d - 1 : ℕ) : ℝ)) * ((∏ i ∈ range j, (μ₀ + i + ((d - 1 : ℕ) : ℝ))) * B) :=
          h1
      _ = _ := by ring

end Grammar
