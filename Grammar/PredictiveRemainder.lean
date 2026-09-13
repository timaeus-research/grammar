/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor

/-!
# The predictive Taylor remainder from the tilted third moment
(CCCLVI; companion note, consult #106 Rank 3)

For a probability measure `μ` (a posterior) and an observable `X` (`X = −f` for a loss `f`) whose
exponential moments exist on a neighbourhood of `[0,1]`, the log-normaliser `ℓ(t) = log μ[e^{tX}]`
(Mathlib's `cgf`) satisfies
`ℓ(1) = μ[X] + Var(X)/2 + κ₃(u)/6` for some `u ∈ (0,1)` (★ `cgf_taylor`), where
`κ₃(t) = m₃/m₀ − 3m₁m₂/m₀² + 2m₁³/m₀³` is the third derivative of `ℓ` — the third cumulant of the
`t`-tilted law (`iteratedDeriv_three_cgf`, `tiltKappa3_eq_centred`: it is the tilted centred third
moment `μ_t[(X − ⟨X⟩_t)³]`). Hence the **predictive remainder**
`R = ℓ(1) − μ[X] − Var(X)/2` obeys ★★ `abs_predictiveRemainder_le : |R| ≤ S/6` whenever the tilted
absolute centred third moments `μ_t[|X − ⟨X⟩_t|³]` are bounded by `S` on `[0,1]`, and
★★ `tendsto_mul_integral_abs_remainder`: `n·𝔼 sup_t μ_t[|X − ⟨X⟩_t|³] → 0 ⇒ n·𝔼|R_n| → 0`. With
`X = −f`: `−ℓ(1) = ⟨f⟩ − ½Var(f) − R`. Not included: the discharge of the tilted-third-moment
certificate in a statistical model (the second half of Rank 3).
-/

open MeasureTheory ProbabilityTheory Filter Set Real Topology

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

/-! ### Tilted raw moments and the third cumulant -/

/-- The raw tilted moments `m_k(t) = μ[X^k e^{tX}]`. -/
noncomputable def tiltMoment (X : Ω → ℝ) (μ : Measure Ω) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, X ω ^ k * exp (t * X ω) ∂μ

/-- The tilted mean `m₁/m₀`. -/
noncomputable def tiltMean (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  tiltMoment X μ 1 t / tiltMoment X μ 0 t

/-- The third cumulant of the tilted law, `m₃/m₀ − 3m₁m₂/m₀² + 2m₁³/m₀³`. -/
noncomputable def tiltKappa3 (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  tiltMoment X μ 3 t / tiltMoment X μ 0 t -
    3 * tiltMoment X μ 1 t * tiltMoment X μ 2 t / tiltMoment X μ 0 t ^ 2 +
    2 * tiltMoment X μ 1 t ^ 3 / tiltMoment X μ 0 t ^ 3

theorem tiltMoment_zero_eq_mgf : tiltMoment X μ 0 t = mgf X μ t := by
  simp [tiltMoment, mgf]

theorem tiltMoment_zero_pos [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    0 < tiltMoment X μ 0 t := by
  rw [tiltMoment_zero_eq_mgf]
  exact mgf_pos (interior_subset (s := integrableExpSet X μ) ht)

theorem hasDerivAt_tiltMoment (ht : t ∈ interior (integrableExpSet X μ)) (k : ℕ) :
    HasDerivAt (tiltMoment X μ k) (tiltMoment X μ (k + 1) t) t :=
  hasDerivAt_integral_pow_mul_exp_real ht k

theorem integrable_tilt (ht : t ∈ interior (integrableExpSet X μ)) (k : ℕ) :
    Integrable (fun ω => X ω ^ k * exp (t * X ω)) μ :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht k

theorem deriv_cgf_eq (ht : t ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) t = tiltMean X μ t := by
  rw [deriv_cgf ht]
  simp [tiltMean, tiltMoment, mgf]

theorem iteratedDeriv_two_cgf_eq (ht : t ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) t =
      tiltMoment X μ 2 t / tiltMoment X μ 0 t - (tiltMoment X μ 1 t / tiltMoment X μ 0 t) ^ 2 := by
  rw [iteratedDeriv_two_cgf ht, deriv_cgf_eq ht]
  simp [tiltMean, tiltMoment, mgf]

/-- The third derivative of the log-normaliser is the third tilted cumulant. -/
theorem hasDerivAt_iteratedDeriv_two_cgf [IsProbabilityMeasure μ]
    (ht : t ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (iteratedDeriv 2 (cgf X μ)) (tiltKappa3 X μ t) t := by
  have hev : iteratedDeriv 2 (cgf X μ) =ᶠ[𝓝 t] fun u =>
      tiltMoment X μ 2 u / tiltMoment X μ 0 u - (tiltMoment X μ 1 u / tiltMoment X μ 0 u) ^ 2 := by
    filter_upwards [isOpen_interior.eventually_mem ht] with u hu
    exact iteratedDeriv_two_cgf_eq hu
  rw [hev.hasDerivAt_iff]
  have hm0 : tiltMoment X μ 0 t ≠ 0 := (tiltMoment_zero_pos ht).ne'
  have h := ((hasDerivAt_tiltMoment ht 2).div (hasDerivAt_tiltMoment ht 0) hm0).sub
    (((hasDerivAt_tiltMoment ht 1).div (hasDerivAt_tiltMoment ht 0) hm0).pow 2)
  simp only [Pi.div_apply] at h
  convert h using 1
  · funext u
    rfl
  · unfold tiltKappa3
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    ring

theorem iteratedDeriv_three_cgf [IsProbabilityMeasure μ]
    (ht : t ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 3 (cgf X μ) t = tiltKappa3 X μ t := by
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_iteratedDeriv_two_cgf ht).deriv

/-- The third cumulant is the tilted centred third moment. -/
theorem integrable_centred_cube (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ) :
    Integrable (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) μ := by
  have e : (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) = fun ω =>
      X ω ^ 3 * exp (t * X ω) - 3 * p * (X ω ^ 2 * exp (t * X ω)) +
        3 * p ^ 2 * (X ω ^ 1 * exp (t * X ω)) - p ^ 3 * (X ω ^ 0 * exp (t * X ω)) :=
    funext fun ω => by ring
  rw [e]
  exact (((integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)).add
    ((integrable_tilt ht 1).const_mul _)).sub ((integrable_tilt ht 0).const_mul _)

theorem tiltKappa3_eq_centred [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    tiltKappa3 X μ t =
      (∫ ω, (X ω - tiltMean X μ t) ^ 3 * exp (t * X ω) ∂μ) / tiltMoment X μ 0 t := by
  set p := tiltMean X μ t with hp
  have e : (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) = fun ω =>
      X ω ^ 3 * exp (t * X ω) - 3 * p * (X ω ^ 2 * exp (t * X ω)) +
        3 * p ^ 2 * (X ω ^ 1 * exp (t * X ω)) - p ^ 3 * (X ω ^ 0 * exp (t * X ω)) :=
    funext fun ω => by ring
  rw [e, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · have hm0 : (∫ ω, exp (t * X ω) ∂μ) ≠ 0 := by
      have := (tiltMoment_zero_pos ht).ne'
      simpa [tiltMoment] using this
    simp only [tiltKappa3, hp, tiltMean, tiltMoment, pow_zero, one_mul, pow_one]
    field_simp
    ring
  · exact integrable_tilt ht 3
  · exact (integrable_tilt ht 2).const_mul _
  · exact (integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)
  · exact (integrable_tilt ht 1).const_mul _
  · exact ((integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)).add
      ((integrable_tilt ht 1).const_mul _)
  · exact (integrable_tilt ht 0).const_mul _

/-- The tilted absolute centred third moment `μ_t[|X − ⟨X⟩_t|³]`. -/
noncomputable def tiltAbsThird (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  (∫ ω, |X ω - tiltMean X μ t| ^ 3 * exp (t * X ω) ∂μ) / tiltMoment X μ 0 t

/-- ★ **The third cumulant is bounded by the tilted absolute centred third moment.** -/
theorem abs_tiltKappa3_le [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    |tiltKappa3 X μ t| ≤ tiltAbsThird X μ t := by
  rw [tiltKappa3_eq_centred ht, tiltAbsThird, abs_div, abs_of_pos (tiltMoment_zero_pos ht)]
  refine div_le_div_of_nonneg_right ?_ (tiltMoment_zero_pos ht).le
  refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (Eventually.of_forall
    fun ω => ?_)))
  simp only [abs_mul, abs_pow, abs_of_pos (exp_pos _)]

/-! ### Taylor at order two on `[0,1]` -/

theorem cgf_taylor [IsProbabilityMeasure μ] (hs : Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet X μ)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      cgf X μ 1 = μ[X] + variance X μ / 2 + tiltKappa3 X μ u / 6 := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc one_pos
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X μ) := hs ⟨le_rfl, zero_le_one⟩
  have hcont : ContDiffOn ℝ 3 (cgf X μ) (Icc (0 : ℝ) 1) := (analyticOn_cgf.mono hs).contDiffOn hu
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 (cgf X μ) (uIcc (0 : ℝ) 1))
      (uIoo (0 : ℝ) 1) := by
    rw [uIcc_of_lt one_pos, uIoo_of_lt one_pos]
    exact (hcont.differentiableOn_iteratedDerivWithin (mod_cast (by norm_num : (2 : ℕ) < 3))
      hu).mono Ioo_subset_Icc_self
  obtain ⟨u, hu', hTay⟩ := taylor_mean_remainder_lagrange (f := cgf X μ) (x₀ := (0 : ℝ)) (x := 1)
    (n := 2) zero_ne_one (by rw [uIcc_of_lt one_pos]; exact hcont.of_le (by norm_num)) hf'
  rw [uIoo_of_lt one_pos] at hu'
  rw [uIcc_of_lt one_pos] at hTay
  refine ⟨u, hu', ?_⟩
  have hXint : Integrable X μ := by
    have := integrable_tilt h0 1
    simpa using this
  -- the Taylor polynomial: `ℓ(0) + ℓ'(0) + ℓ''(0)/2`
  have hpoly : taylorWithinEval (cgf X μ) 2 (Icc (0 : ℝ) 1) 0 1 = μ[X] + variance X μ / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, sub_zero, one_pow,
      smul_eq_mul, iteratedDerivWithin_zero, zero_add]
    have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hca : ∀ n : ℕ, ContDiffAt ℝ n (cgf X μ) 0 := fun n => (analyticAt_cgf h0).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca 1) hmem,
      iteratedDerivWithin_eq_iteratedDeriv hu (hca 2) hmem, iteratedDeriv_one, deriv_cgf_zero h0,
      iteratedDeriv_two_cgf_eq_integral h0, cgf_zero, deriv_cgf_zero h0]
    simp only [probReal_univ, div_one, zero_mul, exp_zero, mul_one, mgf_zero]
    rw [variance_eq_integral hXint.aemeasurable]
    push_cast
    ring
  have hthird : iteratedDerivWithin 3 (cgf X μ) (Icc (0 : ℝ) 1) u = tiltKappa3 X μ u := by
    have hu'' : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu'
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (analyticAt_cgf (hs hu'')).contDiffAt hu'',
      iteratedDeriv_three_cgf (hs hu'')]
  rw [hpoly, hthird] at hTay
  have h3 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at hTay
  linarith

/-! ### The predictive remainder -/

/-- The predictive remainder `R = ℓ(1) − μ[X] − Var(X)/2`. -/
noncomputable def predictiveRemainder (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cgf X μ 1 - μ[X] - variance X μ / 2

/-- ★★ **The predictive remainder is bounded by the tilted absolute centred third moments**:
`|R| ≤ S/6` when `μ_t[|X − ⟨X⟩_t|³] ≤ S` for all `t ∈ [0,1]`. -/
theorem abs_predictiveRemainder_le [IsProbabilityMeasure μ]
    (hs : Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet X μ)) {S : ℝ}
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, tiltAbsThird X μ t ≤ S) :
    |predictiveRemainder X μ| ≤ S / 6 := by
  obtain ⟨u, hu, hT⟩ := cgf_taylor hs
  have hR : predictiveRemainder X μ = tiltKappa3 X μ u / 6 := by
    unfold predictiveRemainder
    linarith
  rw [hR, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  gcongr
  exact (abs_tiltKappa3_le (hs (Ioo_subset_Icc_self hu))).trans (hS u (Ioo_subset_Icc_self hu))

/-- With `X = −f`: `−ℓ(1) = ⟨f⟩ − Var(f)/2 − R` where `ℓ(1) = log μ[e^{−f}]`. -/
theorem neg_log_integral_exp_neg_eq [IsProbabilityMeasure μ] {f : Ω → ℝ} :
    -Real.log (∫ ω, exp (-f ω) ∂μ) =
      μ[f] - variance f μ / 2 - predictiveRemainder (fun ω => -f ω) μ := by
  have h1 : cgf (fun ω => -f ω) μ 1 = Real.log (∫ ω, exp (-f ω) ∂μ) := by
    simp [cgf, mgf]
  have h2 : ∫ ω, -f ω ∂μ = -∫ ω, f ω ∂μ := integral_neg f
  have h3 : variance (fun ω => -f ω) μ = variance f μ := by
    simp only [variance, evariance, integral_neg]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [show -f ω - -∫ a, f a ∂μ = -(f ω - ∫ a, f a ∂μ) by ring, enorm_neg]
  unfold predictiveRemainder
  rw [h1, h2, h3]
  ring

/-- ★★ **The annealed remainder estimate**: if `|R_n(ω)| ≤ S_n(ω)/6` and `n·𝔼S_n → 0`, then
`n·𝔼|R_n| → 0`. -/
theorem tendsto_mul_integral_abs_remainder {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {R S : ℕ → Ω' → ℝ} (hRm : ∀ n, AEStronglyMeasurable (R n) P)
    (hSint : ∀ n, Integrable (S n) P) (hRS : ∀ n ω, |R n ω| ≤ S n ω / 6)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, S n ω ∂P) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, |R n ω| ∂P) atTop (𝓝 0) := by
  have hRint : ∀ n, Integrable (fun ω => |R n ω|) P := fun n =>
    ((hSint n).div_const 6).mono' (hRm n).norm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]
      exact hRS n ω)
  have hS0 : ∀ n ω, 0 ≤ S n ω := fun n ω => by linarith [abs_nonneg (R n ω), hRS n ω]
  refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n)
    (integral_nonneg fun ω => abs_nonneg _)) (fun n => ?_) hS
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  calc ∫ ω, |R n ω| ∂P ≤ ∫ ω, S n ω / 6 ∂P :=
        integral_mono (hRint n) ((hSint n).div_const 6) fun ω => hRS n ω
    _ ≤ ∫ ω, S n ω ∂P := by
        rw [integral_div]
        have : 0 ≤ ∫ ω, S n ω ∂P := integral_nonneg fun ω => hS0 n ω
        linarith [div_le_self this (by norm_num : (1 : ℝ) ≤ 6)]

end Grammar
