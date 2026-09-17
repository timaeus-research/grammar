/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.InverseEvidence

/-!
# The anchored quenched source (§20, averaged posterior cumulants)

On the compact base the limit posterior of a random continuous field `g` has the normalised
weights `S_λ(g(x)) dρ(x) / D_ρ(g)`; the posterior average of an observable `φ` is
`⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)` (`compactAvg`).  For a bounded observable `f` the **anchored
source** is `log⟨e^{εf}⟩_g = log (D(g; ρ e^{εf}) / D(g; ρ))` (`logTilt`), whose `ε`-derivatives
are the posterior cumulants of `f`:

* ★ `abs_logTilt_le`: `|log⟨e^{εf}⟩_g| ≤ |ε| ‖f‖_∞` — the anchoring makes the source bounded
  without any evidence moment;
* ★★ `hasDerivAt_logTilt`: `∂_ε log⟨e^{εf}⟩_g = ⟨f⟩_{g,ε}` (the tilted average `compactAvgTilt`),
  so `deriv (logTilt) 0 = ⟨f⟩_g` and `deriv (deriv logTilt) 0 = ⟨f²⟩_g − ⟨f⟩_g²` (`compactVar`,
  `deriv_deriv_logTilt_zero`).

Averaged over the field, `Ψ(ε) = E log⟨e^{εf}⟩_G` (`quenchedSource`):

* ★★★ `hasDerivAt_quenchedSource_zero`: `Ψ'(0) = E⟨f⟩_G`, and ★★★ `deriv_deriv_quenchedSource_zero`:
  `Ψ''(0) = E[⟨f²⟩_G − ⟨f⟩_G²]` — averages of the conditional (quenched) cumulants, obtained by
  differentiating under `E` with the bounded dominations `|⟨f⟩_{g,ε}| ≤ M`, `|⟨f²⟩_{g,ε}| ≤ M²`
  (Astra #162 §4).  No moment of the evidence enters: only the finiteness of `P` and the
  measurability of the field.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset

namespace Grammar

section Defs

variable {K : Type*} [MeasurableSpace K]

/-- The weighted evidence `∫ φ S_λ(g) dρ`. -/
noncomputable def compactWeighted (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  ∫ x, φ x * fluctuation β lam (g x) ∂ρ

/-- The limit posterior average `⟨φ⟩_g = ∫ φ S_λ(g) dρ / D_ρ(g)`. -/
noncomputable def compactAvg (β lam : ℝ) (ρ : Measure K) (g φ : K → ℝ) : ℝ :=
  compactWeighted β lam ρ g φ / compactD β lam ρ g

/-- The tilted evidence `D(g; ρ e^{εf}) = ∫ e^{εf} S_λ(g) dρ`. -/
noncomputable def compactTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  compactWeighted β lam ρ g fun x => Real.exp (ε * f x)

/-- The tilted average `⟨f⟩_{g,ε} = ∫ f e^{εf} S_λ(g) dρ / D(g; ρ e^{εf})`. -/
noncomputable def compactAvgTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  compactWeighted β lam ρ g (fun x => f x * Real.exp (ε * f x)) / compactTilt β lam ρ g f ε

/-- The tilted second moment `⟨f²⟩_{g,ε}`. -/
noncomputable def compactAvgTiltSq (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  compactWeighted β lam ρ g (fun x => f x ^ 2 * Real.exp (ε * f x)) / compactTilt β lam ρ g f ε

/-- The anchored source `log⟨e^{εf}⟩_g = log (D(g; ρ e^{εf}) / D(g; ρ))`. -/
noncomputable def logTilt (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) (ε : ℝ) : ℝ :=
  Real.log (compactTilt β lam ρ g f ε / compactD β lam ρ g)

/-- The limit posterior variance `⟨f²⟩_g − ⟨f⟩_g²`. -/
noncomputable def compactVar (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) : ℝ :=
  compactAvg β lam ρ g (fun x => f x ^ 2) - compactAvg β lam ρ g f ^ 2

theorem compactWeighted_one (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) :
    compactWeighted β lam ρ g (fun _ => 1) = compactD β lam ρ g := by
  simp [compactWeighted, compactD]

theorem compactTilt_zero (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) :
    compactTilt β lam ρ g f 0 = compactD β lam ρ g := by
  simp [compactTilt, compactWeighted, compactD]

theorem compactAvgTilt_zero (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) :
    compactAvgTilt β lam ρ g f 0 = compactAvg β lam ρ g f := by
  simp [compactAvgTilt, compactAvg, compactTilt, compactWeighted, compactD]

theorem compactAvgTiltSq_zero (β lam : ℝ) (ρ : Measure K) (g f : K → ℝ) :
    compactAvgTiltSq β lam ρ g f 0 = compactAvg β lam ρ g (fun x => f x ^ 2) := by
  simp [compactAvgTiltSq, compactAvg, compactTilt, compactWeighted, compactD]

end Defs

section Bounded

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (g : C(K, ℝ)) {f : K → ℝ} (hf : Measurable f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |f x| ≤ M)

include hβ hlam in
theorem integrable_mul_fluctuation_comp {φ : K → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hφb : ∀ x, |φ x| ≤ C) : Integrable (fun x => φ x * fluctuation β lam (g x)) ρ :=
  (integrable_fluctuation_comp ρ hβ hlam g).bdd_mul hφ.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb x)

omit [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hM in
/-- `|ε f(x)| ≤ |ε| M`, so `e^{−|ε|M} ≤ e^{ε f(x)} ≤ e^{|ε|M}`. -/
theorem exp_mul_le_of_abs_le (ε : ℝ) (x : K) :
    Real.exp (-(|ε| * M)) ≤ Real.exp (ε * f x) ∧ Real.exp (ε * f x) ≤ Real.exp (|ε| * M) := by
  have h : |ε * f x| ≤ |ε| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg ε)
  exact ⟨Real.exp_le_exp.2 (by linarith [neg_abs_le (ε * f x)]),
    Real.exp_le_exp.2 ((le_abs_self _).trans h)⟩

include hβ hlam hf hM in
/-- `e^{−|ε|M} D_ρ(g) ≤ D(g; ρ e^{εf}) ≤ e^{|ε|M} D_ρ(g)`. -/
theorem compactTilt_bounds (ε : ℝ) :
    Real.exp (-(|ε| * M)) * compactD β lam ρ g ≤ compactTilt β lam ρ g f ε ∧
      compactTilt β lam ρ g f ε ≤ Real.exp (|ε| * M) * compactD β lam ρ g := by
  have hexp : Measurable fun x => Real.exp (ε * f x) := (hf.const_mul ε).exp
  have hint : Integrable (fun x => Real.exp (ε * f x) * fluctuation β lam (g x)) ρ :=
    integrable_mul_fluctuation_comp ρ hβ hlam g hexp (C := Real.exp (|ε| * M)) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact (exp_mul_le_of_abs_le hM ε x).2
  have hD := integrable_fluctuation_comp ρ hβ hlam g
  unfold compactTilt compactWeighted compactD
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hD.const_mul _) hint fun x =>
      mul_le_mul_of_nonneg_right (exp_mul_le_of_abs_le hM ε x).1
        (fluctuation_pos β lam _ hβ hlam).le
  · rw [← integral_const_mul]
    exact integral_mono hint (hD.const_mul _) fun x =>
      mul_le_mul_of_nonneg_right (exp_mul_le_of_abs_le hM ε x).2
        (fluctuation_pos β lam _ hβ hlam).le

include hβ hlam hf hM in
theorem compactTilt_pos (hρ : ρ ≠ 0) (ε : ℝ) : 0 < compactTilt β lam ρ g f ε :=
  lt_of_lt_of_le (mul_pos (Real.exp_pos _) (compactD_pos ρ hβ hlam hρ g))
    (compactTilt_bounds ρ hβ hlam g hf hM ε).1

include hβ hlam hf hM in
/-- ★ **The anchored source is bounded by the observable**: `|log⟨e^{εf}⟩_g| ≤ |ε| M`. -/
theorem abs_logTilt_le (hρ : ρ ≠ 0) (ε : ℝ) : |logTilt β lam ρ g f ε| ≤ |ε| * M := by
  have hD := compactD_pos ρ hβ hlam hρ g
  obtain ⟨h1, h2⟩ := compactTilt_bounds ρ hβ hlam g hf hM ε
  have hT := compactTilt_pos ρ hβ hlam g hf hM hρ ε
  unfold logTilt
  rw [abs_le]
  constructor
  · have : Real.exp (-(|ε| * M)) ≤ compactTilt β lam ρ g f ε / compactD β lam ρ g := by
      rw [le_div_iff₀ hD]; exact h1
    have := Real.log_le_log (Real.exp_pos _) this
    rwa [Real.log_exp] at this
  · have : compactTilt β lam ρ g f ε / compactD β lam ρ g ≤ Real.exp (|ε| * M) := by
      rw [div_le_iff₀ hD]; exact h2
    have := Real.log_le_log (div_pos hT hD) this
    rwa [Real.log_exp] at this

include hβ hlam hf hM0 hM in
/-- Differentiation of `ε ↦ ∫ φ e^{εf} S_λ(g) dρ` under the integral, for bounded measurable
`φ`. -/
theorem hasDerivAt_compactWeighted_exp {φ : K → ℝ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hφb : ∀ x, |φ x| ≤ C) (ε₀ : ℝ) :
    HasDerivAt (fun ε => compactWeighted β lam ρ g fun x => φ x * Real.exp (ε * f x))
      (compactWeighted β lam ρ g fun x => φ x * f x * Real.exp (ε₀ * f x)) ε₀ := by
  unfold compactWeighted
  have hmeasF : ∀ ε : ℝ, AEStronglyMeasurable
      (fun x => φ x * Real.exp (ε * f x) * fluctuation β lam (g x)) ρ := fun ε =>
    ((hφ.mul (hf.const_mul ε).exp).mul
      ((continuous_fluctuation β lam hβ hlam).measurable.comp g.continuous.measurable))
      |>.aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun x => φ x * f x * Real.exp (ε₀ * f x) * fluctuation β lam (g x)) ρ :=
    (((hφ.mul hf).mul (hf.const_mul ε₀).exp).mul
      ((continuous_fluctuation β lam hβ hlam).measurable.comp g.continuous.measurable))
      |>.aestronglyMeasurable
  have hbound : Integrable (fun x => C * M * Real.exp ((|ε₀| + 1) * M) * fluctuation β lam (g x))
      ρ := (integrable_fluctuation_comp ρ hβ hlam g).const_mul _
  have hintF : Integrable (fun x => φ x * Real.exp (ε₀ * f x) * fluctuation β lam (g x)) ρ :=
    integrable_mul_fluctuation_comp ρ hβ hlam g (hφ.mul (hf.const_mul ε₀).exp)
      (C := C * Real.exp (|ε₀| * M)) fun x => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hφb x) (exp_mul_le_of_abs_le hM ε₀ x).2 (Real.exp_pos _).le hC0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (x₀ := ε₀)
    (s := Metric.ball ε₀ 1)
    (F := fun ε x => φ x * Real.exp (ε * f x) * fluctuation β lam (g x))
    (F' := fun ε x => φ x * f x * Real.exp (ε * f x) * fluctuation β lam (g x))
    (bound := fun x => C * M * Real.exp ((|ε₀| + 1) * M) * fluctuation β lam (g x))
    (Metric.ball_mem_nhds ε₀ one_pos) (Eventually.of_forall hmeasF) hintF hmeasF' ?_ hbound ?_
  · exact key.2
  · refine Eventually.of_forall fun x ε hε => ?_
    have hε' : |ε| ≤ |ε₀| + 1 := by
      have := Metric.mem_ball.1 hε
      rw [Real.dist_eq] at this
      linarith [abs_sub_abs_le_abs_sub ε ε₀]
    have hS := fluctuation_pos β lam (g x) hβ hlam
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hS, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (ε * f x) ≤ Real.exp ((|ε₀| + 1) * M) :=
      (exp_mul_le_of_abs_le hM ε x).2.trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right hε' hM0))
    have h1 : |φ x| * |f x| ≤ C * M := mul_le_mul (hφb x) (hM x) (abs_nonneg _) hC0
    have h2 : |φ x| * |f x| * Real.exp (ε * f x) ≤ C * M * Real.exp ((|ε₀| + 1) * M) :=
      mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_right h2 hS.le
  · refine Eventually.of_forall fun x ε _ => ?_
    have h : HasDerivAt (fun ε : ℝ => Real.exp (ε * f x)) (Real.exp (ε * f x) * f x) ε := by
      have := ((hasDerivAt_id ε).mul_const (f x)).exp
      simpa using this
    have := (h.const_mul (φ x)).mul_const (fluctuation β lam (g x))
    exact this.congr_deriv (by ring)

include hβ hlam hf hM0 hM in
/-- `∂_ε D(g; ρ e^{εf}) = ∫ f e^{εf} S_λ(g) dρ`. -/
theorem hasDerivAt_compactTilt (ε₀ : ℝ) :
    HasDerivAt (compactTilt β lam ρ g f)
      (compactWeighted β lam ρ g fun x => f x * Real.exp (ε₀ * f x)) ε₀ := by
  have h := hasDerivAt_compactWeighted_exp ρ hβ hlam g hf hM0 hM (φ := fun _ => 1)
    measurable_const (C := 1) zero_le_one (fun _ => by simp) ε₀
  have hfun : compactTilt β lam ρ g f =
      fun ε => compactWeighted β lam ρ g fun x => Real.exp (ε * f x) := rfl
  rw [hfun]
  simpa only [one_mul] using h

include hβ hlam hf hM0 hM in
/-- `∂_ε ∫ f e^{εf} S_λ(g) dρ = ∫ f² e^{εf} S_λ(g) dρ`. -/
theorem hasDerivAt_compactWeighted_mul_exp (ε₀ : ℝ) :
    HasDerivAt (fun ε => compactWeighted β lam ρ g fun x => f x * Real.exp (ε * f x))
      (compactWeighted β lam ρ g fun x => f x ^ 2 * Real.exp (ε₀ * f x)) ε₀ := by
  have h := hasDerivAt_compactWeighted_exp ρ hβ hlam g hf hM0 hM hf hM0 hM ε₀
  simpa only [sq] using h

include hβ hlam hf hM0 hM in
/-- ★★ **The derivative of the anchored source is the tilted posterior average**:
`∂_ε log⟨e^{εf}⟩_g = ⟨f⟩_{g,ε}`. -/
theorem hasDerivAt_logTilt (hρ : ρ ≠ 0) (ε₀ : ℝ) :
    HasDerivAt (logTilt β lam ρ g f) (compactAvgTilt β lam ρ g f ε₀) ε₀ := by
  have hD := compactD_pos ρ hβ hlam hρ g
  have hT := compactTilt_pos ρ hβ hlam g hf hM hρ ε₀
  have h := ((hasDerivAt_compactTilt ρ hβ hlam g hf hM0 hM ε₀).div_const
    (compactD β lam ρ g)).log (div_pos hT hD).ne'
  refine h.congr_deriv ?_
  unfold compactAvgTilt
  exact div_div_div_cancel_right₀ hD.ne' _ _

include hβ hlam hf hM0 hM in
theorem deriv_logTilt (hρ : ρ ≠ 0) :
    deriv (logTilt β lam ρ g f) = compactAvgTilt β lam ρ g f :=
  funext fun ε => (hasDerivAt_logTilt ρ hβ hlam g hf hM0 hM hρ ε).deriv

include hβ hlam hf hM0 hM in
/-- `∂_ε ⟨f⟩_{g,ε} = ⟨f²⟩_{g,ε} − ⟨f⟩_{g,ε}²`. -/
theorem hasDerivAt_compactAvgTilt (hρ : ρ ≠ 0) (ε₀ : ℝ) :
    HasDerivAt (compactAvgTilt β lam ρ g f)
      (compactAvgTiltSq β lam ρ g f ε₀ - compactAvgTilt β lam ρ g f ε₀ ^ 2) ε₀ := by
  have hT := compactTilt_pos ρ hβ hlam g hf hM hρ ε₀
  have h := (hasDerivAt_compactWeighted_mul_exp ρ hβ hlam g hf hM0 hM ε₀).div
    (hasDerivAt_compactTilt ρ hβ hlam g hf hM0 hM ε₀) hT.ne'
  refine h.congr_deriv ?_
  unfold compactAvgTiltSq compactAvgTilt
  have hT' := hT.ne'
  set N' := compactWeighted β lam ρ g fun x => f x ^ 2 * Real.exp (ε₀ * f x)
  set N := compactWeighted β lam ρ g fun x => f x * Real.exp (ε₀ * f x)
  set T := compactTilt β lam ρ g f ε₀
  field_simp

include hβ hlam hf hM0 hM in
/-- ★★ **The second derivative of the anchored source at `0` is the posterior variance**. -/
theorem deriv_deriv_logTilt_zero (hρ : ρ ≠ 0) :
    deriv (deriv (logTilt β lam ρ g f)) 0 = compactVar β lam ρ g f := by
  rw [deriv_logTilt ρ hβ hlam g hf hM0 hM hρ,
    (hasDerivAt_compactAvgTilt ρ hβ hlam g hf hM0 hM hρ 0).deriv, compactAvgTiltSq_zero,
    compactAvgTilt_zero]
  rfl

include hβ hlam hf hM0 hM in
/-- `|⟨f⟩_{g,ε}| ≤ M`. -/
theorem abs_compactAvgTilt_le (hρ : ρ ≠ 0) (ε : ℝ) : |compactAvgTilt β lam ρ g f ε| ≤ M := by
  have hT := compactTilt_pos ρ hβ hlam g hf hM hρ ε
  unfold compactAvgTilt
  rw [abs_div, abs_of_pos hT, div_le_iff₀ hT]
  unfold compactTilt compactWeighted
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  have hexp : Measurable fun x => Real.exp (ε * f x) := (hf.const_mul ε).exp
  refine integral_mono ?_ ((integrable_mul_fluctuation_comp ρ hβ hlam g hexp
    (C := Real.exp (|ε| * M)) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact (exp_mul_le_of_abs_le hM ε x).2).const_mul M) fun x => ?_
  · exact (integrable_mul_fluctuation_comp ρ hβ hlam g
      (φ := fun x => f x * Real.exp (ε * f x)) (hf.mul hexp)
      (C := M * Real.exp (|ε| * M)) fun x => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hM x) (exp_mul_le_of_abs_le hM ε x).2 (Real.exp_pos _).le hM0).abs
  · have hS := fluctuation_pos β lam (g x) hβ hlam
    rw [abs_mul, abs_mul, abs_of_pos hS, abs_of_pos (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_right (hM x) (Real.exp_pos (ε * f x)).le
    nlinarith [hS.le, this]

include hβ hlam hf hM in
/-- `|⟨f²⟩_{g,ε}| ≤ M²`. -/
theorem abs_compactAvgTiltSq_le (hρ : ρ ≠ 0) (ε : ℝ) :
    |compactAvgTiltSq β lam ρ g f ε| ≤ M ^ 2 := by
  have hT := compactTilt_pos ρ hβ hlam g hf hM hρ ε
  have hsq : ∀ x, |f x ^ 2| ≤ M ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  unfold compactAvgTiltSq
  rw [abs_div, abs_of_pos hT, div_le_iff₀ hT]
  unfold compactTilt compactWeighted
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  have hexp : Measurable fun x => Real.exp (ε * f x) := (hf.const_mul ε).exp
  refine integral_mono ?_ ((integrable_mul_fluctuation_comp ρ hβ hlam g hexp
    (C := Real.exp (|ε| * M)) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact (exp_mul_le_of_abs_le hM ε x).2).const_mul (M ^ 2)) fun x => ?_
  · exact (integrable_mul_fluctuation_comp ρ hβ hlam g
      (φ := fun x => f x ^ 2 * Real.exp (ε * f x)) ((hf.pow_const 2).mul hexp)
      (C := M ^ 2 * Real.exp (|ε| * M)) fun x => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (hsq x) (exp_mul_le_of_abs_le hM ε x).2 (Real.exp_pos _).le
          (by positivity)).abs
  · have hS := fluctuation_pos β lam (g x) hβ hlam
    rw [abs_mul, abs_mul, abs_of_pos hS, abs_of_pos (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_right (hsq x) (Real.exp_pos (ε * f x)).le
    nlinarith [hS.le, this]

end Bounded

section Quenched

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
  (G : Ω → C(K, ℝ)) (hG : Measurable fun q : Ω × K => G q.1 q.2)
  {f : K → ℝ} (hf : Measurable f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |f x| ≤ M)

include hβ hlam hG in
/-- The weighted evidence of a measurable random field is measurable. -/
theorem measurable_compactWeighted_comp {φ : K → ℝ} (hφ : Measurable φ) :
    Measurable fun ω => compactWeighted β lam ρ (G ω) φ := by
  have h : Measurable fun q : Ω × K => φ q.2 * fluctuation β lam (G q.1 q.2) :=
    (hφ.comp measurable_snd).mul ((continuous_fluctuation β lam hβ hlam).measurable.comp hG)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

include hβ hlam hG hf in
theorem measurable_compactTilt_comp (ε : ℝ) :
    Measurable fun ω => compactTilt β lam ρ (G ω) f ε :=
  measurable_compactWeighted_comp ρ hβ hlam G hG (hf.const_mul ε).exp

include hβ hlam hG hf in
theorem measurable_logTilt_comp (ε : ℝ) : Measurable fun ω => logTilt β lam ρ (G ω) f ε := by
  have hD : Measurable fun ω => compactD β lam ρ (G ω) := by
    have := measurable_compactWeighted_comp ρ hβ hlam G hG (φ := fun _ => (1 : ℝ))
      measurable_const
    simpa only [compactWeighted_one] using this
  exact ((measurable_compactTilt_comp ρ hβ hlam G hG hf ε).div hD).log

include hβ hlam hG hf in
theorem measurable_compactAvgTilt_comp (ε : ℝ) :
    Measurable fun ω => compactAvgTilt β lam ρ (G ω) f ε :=
  (measurable_compactWeighted_comp ρ hβ hlam G hG (hf.mul (hf.const_mul ε).exp)).div
    (measurable_compactTilt_comp ρ hβ hlam G hG hf ε)

include hβ hlam hG hf in
theorem measurable_compactAvgTiltSq_comp (ε : ℝ) :
    Measurable fun ω => compactAvgTiltSq β lam ρ (G ω) f ε :=
  (measurable_compactWeighted_comp ρ hβ hlam G hG ((hf.pow_const 2).mul (hf.const_mul ε).exp)).div
    (measurable_compactTilt_comp ρ hβ hlam G hG hf ε)

/-- The **anchored quenched source** `Ψ(ε) = E log⟨e^{εf}⟩_G`. -/
noncomputable def quenchedSource (β lam : ℝ) (ρ : Measure K) (P : Measure Ω) (G : Ω → C(K, ℝ))
    (f : K → ℝ) (ε : ℝ) : ℝ :=
  ∫ ω, logTilt β lam ρ (G ω) f ε ∂P

include hβ hlam hG hf hM0 hM in
/-- ★★★ **The quenched source is differentiable, with derivative the averaged tilted posterior
mean**: `Ψ'(ε) = E⟨f⟩_{G,ε}`. -/
theorem hasDerivAt_quenchedSource (hρ : ρ ≠ 0) (ε₀ : ℝ) :
    HasDerivAt (quenchedSource β lam ρ P G f)
      (∫ ω, compactAvgTilt β lam ρ (G ω) f ε₀ ∂P) ε₀ := by
  unfold quenchedSource
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (x₀ := ε₀) (s := univ)
    (F := fun ε ω => logTilt β lam ρ (G ω) f ε)
    (F' := fun ε ω => compactAvgTilt β lam ρ (G ω) f ε) (bound := fun _ => M) univ_mem
    (Eventually.of_forall fun ε =>
      (measurable_logTilt_comp ρ hβ hlam G hG hf ε).aestronglyMeasurable)
    (Integrable.of_bound (measurable_logTilt_comp ρ hβ hlam G hG hf ε₀).aestronglyMeasurable
      (|ε₀| * M) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_logTilt_le ρ hβ hlam (G ω) hf hM hρ ε₀))
    (measurable_compactAvgTilt_comp ρ hβ hlam G hG hf ε₀).aestronglyMeasurable
    (Eventually.of_forall fun ω ε _ => by
      rw [Real.norm_eq_abs]
      exact abs_compactAvgTilt_le ρ hβ hlam (G ω) hf hM0 hM hρ ε) (integrable_const M)
    (Eventually.of_forall fun ω ε _ => hasDerivAt_logTilt ρ hβ hlam (G ω) hf hM0 hM hρ ε)
  exact key.2

include hβ hlam hG hf hM0 hM in
/-- ★★★ `Ψ'(0) = E⟨f⟩_G`: the derivative of the quenched source at the origin is the averaged
posterior mean. -/
theorem hasDerivAt_quenchedSource_zero (hρ : ρ ≠ 0) :
    HasDerivAt (quenchedSource β lam ρ P G f) (∫ ω, compactAvg β lam ρ (G ω) f ∂P) 0 := by
  have h := hasDerivAt_quenchedSource ρ hβ hlam P G hG hf hM0 hM hρ 0
  simpa only [compactAvgTilt_zero] using h

include hβ hlam hG hf hM0 hM in
theorem deriv_quenchedSource (hρ : ρ ≠ 0) :
    deriv (quenchedSource β lam ρ P G f) = fun ε => ∫ ω, compactAvgTilt β lam ρ (G ω) f ε ∂P :=
  funext fun ε => (hasDerivAt_quenchedSource ρ hβ hlam P G hG hf hM0 hM hρ ε).deriv

include hβ hlam hG hf hM0 hM in
/-- `∂_ε E⟨f⟩_{G,ε} = E[⟨f²⟩_{G,ε} − ⟨f⟩_{G,ε}²]`. -/
theorem hasDerivAt_integral_compactAvgTilt (hρ : ρ ≠ 0) (ε₀ : ℝ) :
    HasDerivAt (fun ε => ∫ ω, compactAvgTilt β lam ρ (G ω) f ε ∂P)
      (∫ ω, compactAvgTiltSq β lam ρ (G ω) f ε₀ - compactAvgTilt β lam ρ (G ω) f ε₀ ^ 2 ∂P)
      ε₀ := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (x₀ := ε₀) (s := univ)
    (F := fun ε ω => compactAvgTilt β lam ρ (G ω) f ε)
    (F' := fun ε ω => compactAvgTiltSq β lam ρ (G ω) f ε - compactAvgTilt β lam ρ (G ω) f ε ^ 2)
    (bound := fun _ => M ^ 2 + M ^ 2) univ_mem
    (Eventually.of_forall fun ε =>
      (measurable_compactAvgTilt_comp ρ hβ hlam G hG hf ε).aestronglyMeasurable)
    (Integrable.of_bound (measurable_compactAvgTilt_comp ρ hβ hlam G hG hf ε₀).aestronglyMeasurable
      M (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_compactAvgTilt_le ρ hβ hlam (G ω) hf hM0 hM hρ ε₀))
    ((measurable_compactAvgTiltSq_comp ρ hβ hlam G hG hf ε₀).sub
      ((measurable_compactAvgTilt_comp ρ hβ hlam G hG hf ε₀).pow_const 2)).aestronglyMeasurable
    (Eventually.of_forall fun ω ε _ => by
      rw [Real.norm_eq_abs]
      have h1 := abs_compactAvgTiltSq_le ρ hβ hlam (G ω) hf hM hρ ε
      have h2 := abs_compactAvgTilt_le ρ hβ hlam (G ω) hf hM0 hM hρ ε
      have h3 : |compactAvgTilt β lam ρ (G ω) f ε ^ 2| ≤ M ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      exact (abs_sub _ _).trans (add_le_add h1 h3)) (integrable_const _)
    (Eventually.of_forall fun ω ε _ =>
      hasDerivAt_compactAvgTilt ρ hβ hlam (G ω) hf hM0 hM hρ ε)
  exact key.2

include hβ hlam hG hf hM0 hM in
/-- ★★★ `Ψ''(0) = E[⟨f²⟩_G − ⟨f⟩_G²]`: the second derivative of the quenched source at the origin
is the averaged posterior variance. -/
theorem deriv_deriv_quenchedSource_zero (hρ : ρ ≠ 0) :
    deriv (deriv (quenchedSource β lam ρ P G f)) 0 = ∫ ω, compactVar β lam ρ (G ω) f ∂P := by
  rw [deriv_quenchedSource ρ hβ hlam P G hG hf hM0 hM hρ,
    (hasDerivAt_integral_compactAvgTilt ρ hβ hlam P G hG hf hM0 hM hρ 0).deriv]
  simp only [compactAvgTiltSq_zero, compactAvgTilt_zero]
  rfl

end Quenched

end Grammar
