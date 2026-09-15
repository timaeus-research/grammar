/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.Fluctuation
import Grammar.Asymptotic
import Grammar.SmoothOneDim

/-!
# The jets of `η e^{τξ}` and the fluctuation-function ladder

For smooth `η, ξ : ℝ → ℝ` and a parameter `τ`, the `j`-th derivative of `v ↦ η(v) e^{τ ξ(v)}` is
`P_j(v, τ) e^{τ ξ(v)}` with `P_j` a polynomial of degree `≤ j` in `τ` whose coefficients
`jetCoeff η ξ j r` are smooth functions of `v` defined by the recursion
`p_{0,0} = η`, `p_{j+1,r} = p_{j,r}' + ξ' p_{j,r−1}` (`iteratedDeriv_mul_exp_field`). On a compact
`v`-interval, `|P_j(v, τ)| ≤ C_j (1 + τ)^j` for `τ ≥ 0` (`exists_jetPoly_bound`).

Differentiating `η(v) S_μ(ξ(v)) = ∫ s^{μ−1} e^{−s} η(v) e^{√s ξ(v)} ds` under the integral gives
★★ `iteratedDeriv_mul_fluctuation`:
`∂_v^j [η · S_μ∘ξ] = ∫ s^{μ−1} e^{−s} P_j(v, √s) e^{√s ξ(v)} ds`, the exact form in which the
normal jets of the field enter the empirical coefficients: each power `τ^r = s^{r/2}` of the
field-derivative polynomial shifts the fluctuation index by `r/2` (the ladder `∂_a^r S_μ =
S_{μ+r/2}`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable (η ξ : ℝ → ℝ)

/-! ### The jet coefficients -/

/-- The coefficient functions `p_{j,r}` of `∂_v^j[η e^{τξ}] = (∑_r p_{j,r}(v) τ^r) e^{τξ(v)}`. -/
noncomputable def jetCoeff : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => η
  | 0, _ + 1 => fun _ => 0
  | j + 1, 0 => deriv (jetCoeff j 0)
  | j + 1, r + 1 => fun v => deriv (jetCoeff j (r + 1)) v + deriv ξ v * jetCoeff j r v

/-- The field-derivative polynomial `P_j(v, τ) = ∑_{r ≤ j} p_{j,r}(v) τ^r`. -/
noncomputable def jetPoly (j : ℕ) (v τ : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1), jetCoeff η ξ j r v * τ ^ r

theorem jetCoeff_zero_zero : jetCoeff η ξ 0 0 = η := rfl

theorem jetCoeff_zero_succ (r : ℕ) : jetCoeff η ξ 0 (r + 1) = fun _ => 0 := rfl

theorem jetCoeff_succ_zero (j : ℕ) : jetCoeff η ξ (j + 1) 0 = deriv (jetCoeff η ξ j 0) := rfl

theorem jetCoeff_succ_succ (j r : ℕ) : jetCoeff η ξ (j + 1) (r + 1) =
    fun v => deriv (jetCoeff η ξ j (r + 1)) v + deriv ξ v * jetCoeff η ξ j r v := rfl

/-- The coefficients vanish above the diagonal: `p_{j,r} = 0` for `r > j`. -/
theorem jetCoeff_eq_zero_of_lt : ∀ j r : ℕ, j < r → jetCoeff η ξ j r = fun _ => 0
  | 0, r + 1, _ => rfl
  | j + 1, r + 1, h => by
    rw [jetCoeff_succ_succ]
    have h1 := jetCoeff_eq_zero_of_lt j (r + 1) (by omega)
    have h2 := jetCoeff_eq_zero_of_lt j r (by omega)
    funext v
    simp [h1, h2]

variable {η ξ}

theorem contDiff_jetCoeff (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) :
    ∀ j r : ℕ, ContDiff ℝ ∞ (jetCoeff η ξ j r)
  | 0, 0 => hη
  | 0, _ + 1 => contDiff_const
  | j + 1, 0 => by
    rw [jetCoeff_succ_zero]
    simpa using (contDiff_jetCoeff hη hξ j 0).iterate_deriv 1
  | j + 1, r + 1 => by
    rw [jetCoeff_succ_succ]
    have h1 : ContDiff ℝ ∞ (deriv (jetCoeff η ξ j (r + 1))) := by
      simpa using (contDiff_jetCoeff hη hξ j (r + 1)).iterate_deriv 1
    have h2 : ContDiff ℝ ∞ (deriv ξ) := by simpa using hξ.iterate_deriv 1
    exact h1.add (h2.mul (contDiff_jetCoeff hη hξ j r))

theorem continuous_jetCoeff (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (j r : ℕ) :
    Continuous (jetCoeff η ξ j r) :=
  (contDiff_jetCoeff hη hξ j r).continuous

theorem differentiable_jetCoeff (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (j r : ℕ) :
    Differentiable ℝ (jetCoeff η ξ j r) :=
  (contDiff_jetCoeff hη hξ j r).differentiable (by simp)

/-! ### The derivative recursion -/

/-- One `v`-derivative of `P_j(v, τ) e^{τ ξ(v)}` is `P_{j+1}(v, τ) e^{τ ξ(v)}`. -/
theorem hasDerivAt_jetPoly_mul_exp (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (j : ℕ) (τ v : ℝ) :
    HasDerivAt (fun v => jetPoly η ξ j v τ * exp (τ * ξ v))
      (jetPoly η ξ (j + 1) v τ * exp (τ * ξ v)) v := by
  have hξd : Differentiable ℝ ξ := hξ.differentiable (by simp)
  have hexp : HasDerivAt (fun v => exp (τ * ξ v)) (exp (τ * ξ v) * (τ * deriv ξ v)) v :=
    ((hξd v).hasDerivAt.const_mul τ).exp
  have hpoly : HasDerivAt (fun v => jetPoly η ξ j v τ)
      (∑ r ∈ Finset.range (j + 1), deriv (jetCoeff η ξ j r) v * τ ^ r) v := by
    unfold jetPoly
    exact HasDerivAt.fun_sum fun r _ =>
      ((differentiable_jetCoeff hη hξ j r) v).hasDerivAt.mul_const _
  have hz : deriv (jetCoeff η ξ j (j + 1)) v = 0 := by
    rw [jetCoeff_eq_zero_of_lt η ξ j (j + 1) (by omega)]
    simp
  have hj1 : jetPoly η ξ (j + 1) v τ =
      (∑ r ∈ Finset.range (j + 1), deriv (jetCoeff η ξ j r) v * τ ^ r) +
        jetPoly η ξ j v τ * (τ * deriv ξ v) := by
    unfold jetPoly
    calc ∑ r ∈ Finset.range (j + 1 + 1), jetCoeff η ξ (j + 1) r v * τ ^ r
        = ∑ r ∈ Finset.range (j + 1), jetCoeff η ξ (j + 1) (r + 1) v * τ ^ (r + 1) +
            jetCoeff η ξ (j + 1) 0 v * τ ^ 0 := Finset.sum_range_succ' _ _
      _ = ∑ r ∈ Finset.range (j + 1), (deriv (jetCoeff η ξ j (r + 1)) v * τ ^ (r + 1) +
            jetCoeff η ξ j r v * τ ^ r * (τ * deriv ξ v)) + deriv (jetCoeff η ξ j 0) v := by
          simp only [jetCoeff_succ_succ, jetCoeff_succ_zero, pow_zero, mul_one]
          refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun r _ => ?_) rfl
          ring
      _ = (∑ r ∈ Finset.range (j + 1), deriv (jetCoeff η ξ j (r + 1)) v * τ ^ (r + 1) +
            deriv (jetCoeff η ξ j 0) v) +
            (∑ r ∈ Finset.range (j + 1), jetCoeff η ξ j r v * τ ^ r) * (τ * deriv ξ v) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
          ring
      _ = ∑ r ∈ Finset.range (j + 1), deriv (jetCoeff η ξ j r) v * τ ^ r +
            (∑ r ∈ Finset.range (j + 1), jetCoeff η ξ j r v * τ ^ r) * (τ * deriv ξ v) := by
          congr 1
          rw [Finset.sum_range_succ' (fun r => deriv (jetCoeff η ξ j r) v * τ ^ r),
            Finset.sum_range_succ (fun r => deriv (jetCoeff η ξ j (r + 1)) v * τ ^ (r + 1)), hz]
          simp
  refine (hpoly.mul hexp).congr_deriv ?_
  rw [hj1]
  ring

/-- `∂_v^j [η e^{τξ}] = P_j(v, τ) e^{τ ξ(v)}`. -/
theorem iteratedDeriv_mul_exp_field (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (τ : ℝ) :
    ∀ j : ℕ, iteratedDeriv j (fun v => η v * exp (τ * ξ v)) =
      fun v => jetPoly η ξ j v τ * exp (τ * ξ v)
  | 0 => by
    funext v
    simp [jetPoly, jetCoeff_zero_zero]
  | j + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_mul_exp_field hη hξ τ j]
    funext v
    exact (hasDerivAt_jetPoly_mul_exp hη hξ j τ v).deriv

/-! ### Bounds on compact intervals -/

/-- On a compact `v`-interval, `|P_j(v, τ)| ≤ C (1 + τ)^j` for `τ ≥ 0`. -/
theorem exists_jetPoly_bound (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (j : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Icc a b, ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j v τ| ≤ C * (1 + τ) ^ j := by
  have hbd : ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Icc a b, |jetCoeff η ξ j r v| ≤ C := fun r => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_jetCoeff hη hξ j r).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
    exact (Real.norm_eq_abs _ ▸ hC v hv).trans (le_max_left _ _)
  choose Cf hCf using hbd
  refine ⟨∑ r ∈ Finset.range (j + 1), Cf r, Finset.sum_nonneg fun r _ => (hCf r).1,
    fun v hv τ hτ => ?_⟩
  unfold jetPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg hτ r)]
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have hτr : τ ^ r ≤ (1 + τ) ^ j :=
    (pow_le_pow_left₀ hτ (by linarith) r).trans (pow_le_pow_right₀ (by linarith) hr')
  exact mul_le_mul ((hCf r).2 v hv) hτr (pow_nonneg hτ r) (hCf r).1

/-- `(1 + y)^n ≤ n! e^{1 + y}` for `y ≥ 0`. -/
theorem one_add_pow_le_factorial_mul_exp (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ n ≤ (n.factorial : ℝ) * exp (1 + y) := by
  have h := Real.pow_div_factorial_le_exp (1 + y) (by linarith) n
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
  rw [div_le_iff₀ hf] at h
  linarith

/-! ### Differentiation under the fluctuation integral -/

variable (η ξ) in
/-- The `j`-th fluctuation-jet integral `∫₀^∞ s^{μ−1} e^{−s} P_j(v, √s) e^{√s ξ(v)} ds`. -/
noncomputable def fluctJet (μ : ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (μ - 1) * exp (-s) *
    (jetPoly η ξ j v (Real.sqrt s) * exp (Real.sqrt s * ξ v))

/-- The dominating kernel `s^{μ−1} e^{−s} (1+√s)^j e^{M√s}` is integrable. -/
theorem integrableOn_jet_kernel {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (M : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ (μ - 1) * exp (-s) *
      ((1 + Real.sqrt s) ^ j * exp (M * Real.sqrt s))) (Ioi 0) := by
  have hint := fluctuation_integrableOn 1 μ one_pos hμ (M + 1)
  have hmeas : Measurable fun s : ℝ => s ^ (μ - 1) * exp (-s) *
      ((1 + Real.sqrt s) ^ j * exp (M * Real.sqrt s)) := by fun_prop
  refine ((hint.const_mul ((j.factorial : ℝ) * exp 1)).mono' hmeas.aestronglyMeasurable ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 < s := hs
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hp : 0 ≤ s ^ (μ - 1) := Real.rpow_nonneg hs0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := one_add_pow_le_factorial_mul_exp j hsq
  calc s ^ (μ - 1) * exp (-s) * ((1 + Real.sqrt s) ^ j * exp (M * Real.sqrt s))
      ≤ s ^ (μ - 1) * exp (-s) *
          ((j.factorial : ℝ) * exp (1 + Real.sqrt s) * exp (M * Real.sqrt s)) := by
        gcongr
    _ = (j.factorial : ℝ) * exp 1 * (s ^ (μ - 1) * exp (-1 * s + 1 * (M + 1) * Real.sqrt s)) := by
        have e1 : exp (1 + Real.sqrt s) = exp 1 * exp (Real.sqrt s) := Real.exp_add _ _
        have e2 : exp (-1 * s + 1 * (M + 1) * Real.sqrt s) =
            exp (-s) * (exp (M * Real.sqrt s) * exp (Real.sqrt s)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [e1, e2]
        ring

theorem measurable_fluctJet_integrand (μ : ℝ) (j : ℕ) (v : ℝ) :
    Measurable fun s : ℝ => s ^ (μ - 1) * exp (-s) *
      (jetPoly η ξ j v (Real.sqrt s) * exp (Real.sqrt s * ξ v)) := by
  unfold jetPoly
  fun_prop

/-- Differentiating the fluctuation-jet integral under the integral sign. -/
theorem hasDerivAt_fluctJet (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) {μ : ℝ} (hμ : 0 < μ)
    (j : ℕ) (v : ℝ) : HasDerivAt (fluctJet η ξ μ j) (fluctJet η ξ μ (j + 1) v) v := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hξ.continuous.continuousOn (s := Icc (v - 1) (v + 1)))
  obtain ⟨C, hC0, hC⟩ := exists_jetPoly_bound hη hξ (j + 1) (v - 1) (v + 1)
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_jetPoly_bound hη hξ j (v - 1) (v + 1)
  have hvmem : v ∈ Icc (v - 1) (v + 1) := ⟨by linarith, by linarith⟩
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x s => s ^ (μ - 1) * exp (-s) *
      (jetPoly η ξ j x (Real.sqrt s) * exp (Real.sqrt s * ξ x)))
    (F' := fun x s => s ^ (μ - 1) * exp (-s) *
      (jetPoly η ξ (j + 1) x (Real.sqrt s) * exp (Real.sqrt s * ξ x)))
    (x₀ := v) (s := Icc (v - 1) (v + 1))
    (bound := fun s => C * (s ^ (μ - 1) * exp (-s) *
      ((1 + Real.sqrt s) ^ (j + 1) * exp (M * Real.sqrt s))))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x => (measurable_fluctJet_integrand μ j x).aestronglyMeasurable)
    ?_ (measurable_fluctJet_integrand μ (j + 1) v).aestronglyMeasurable ?_
    ((integrableOn_jet_kernel hμ (j + 1) M).const_mul C) ?_
  · exact hkey.2
  · -- integrability of `F v`
    refine ((integrableOn_jet_kernel hμ j M).const_mul C₀).mono'
      (measurable_fluctJet_integrand μ j v).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    have hp : 0 ≤ s ^ (μ - 1) := Real.rpow_nonneg hs0.le _
    have hξv : ξ v ≤ M := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM v hvmem)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    have h1 : |jetPoly η ξ j v (Real.sqrt s)| ≤ C₀ * (1 + Real.sqrt s) ^ j := hC₀ v hvmem _ hsq
    have h2 : exp (Real.sqrt s * ξ v) ≤ exp (M * Real.sqrt s) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc s ^ (μ - 1) * exp (-s) * (|jetPoly η ξ j v (Real.sqrt s)| * exp (Real.sqrt s * ξ v))
        ≤ s ^ (μ - 1) * exp (-s) * (C₀ * (1 + Real.sqrt s) ^ j * exp (M * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.exp_pos _).le
            (mul_nonneg hC₀0 (pow_nonneg (by positivity) _))) (mul_nonneg hp (Real.exp_pos _).le)
      _ = C₀ * (s ^ (μ - 1) * exp (-s) * ((1 + Real.sqrt s) ^ j * exp (M * Real.sqrt s))) := by ring
  · -- the derivative bound
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs x hx => ?_)
    have hs0 : 0 < s := hs
    have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    have hp : 0 ≤ s ^ (μ - 1) := Real.rpow_nonneg hs0.le _
    have hξx : ξ x ≤ M := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM x hx)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    have h1 : |jetPoly η ξ (j + 1) x (Real.sqrt s)| ≤ C * (1 + Real.sqrt s) ^ (j + 1) :=
      hC x hx _ hsq
    have h2 : exp (Real.sqrt s * ξ x) ≤ exp (M * Real.sqrt s) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc s ^ (μ - 1) * exp (-s) * (|jetPoly η ξ (j + 1) x (Real.sqrt s)| * exp (Real.sqrt s * ξ x))
        ≤ s ^ (μ - 1) * exp (-s) * (C * (1 + Real.sqrt s) ^ (j + 1) * exp (M * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.exp_pos _).le
            (mul_nonneg hC0 (pow_nonneg (by positivity) _))) (mul_nonneg hp (Real.exp_pos _).le)
      _ = C * (s ^ (μ - 1) * exp (-s) * ((1 + Real.sqrt s) ^ (j + 1) * exp (M * Real.sqrt s))) := by
          ring
  · -- the pointwise derivative
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ x _ => ?_)
    exact (hasDerivAt_jetPoly_mul_exp hη hξ j (Real.sqrt s) x).const_mul _

/-- ★★ **The jets of `η · S_μ∘ξ` are fluctuation-jet integrals**:
`∂_v^j [η(v) S_μ(ξ(v))] = ∫₀^∞ s^{μ−1} e^{−s} P_j(v, √s) e^{√s ξ(v)} ds`. -/
theorem iteratedDeriv_mul_fluctuation (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) {μ : ℝ}
    (hμ : 0 < μ) : ∀ j : ℕ,
    iteratedDeriv j (fun v => η v * fluctuation 1 μ (ξ v)) = fluctJet η ξ μ j
  | 0 => by
    funext v
    rw [iteratedDeriv_zero]
    unfold fluctJet fluctuation
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have hP : jetPoly η ξ 0 v (Real.sqrt s) = η v := by
      simp [jetPoly, jetCoeff_zero_zero]
    rw [hP, show (-1 : ℝ) * s + 1 * ξ v * Real.sqrt s = -s + Real.sqrt s * ξ v by ring,
      Real.exp_add]
    ring
  | j + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_mul_fluctuation hη hξ hμ j]
    funext v
    exact (hasDerivAt_fluctJet hη hξ hμ j v).deriv

end SmoothEngine

end Grammar
