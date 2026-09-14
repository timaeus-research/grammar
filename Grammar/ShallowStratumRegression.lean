/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.LogTwoD
import Grammar.SmoothFaceOperators

/-!
# Shallow-stratum detection: the observable `x^M` on the corner `x²y² = 0`

For the phase `K(x,y) = x²y²` on the unit square and every `M ≥ 1`,

  `∫₀¹ ∫₀¹ x^M e^{-n x²y²} dy dx ~ (√π/(2M)) · n^{-1/2}`   (`n → ∞`).

The observable `x^M` has vanishing jet of order `M − 1` at the deepest stratum, the corner
`(0,0)`: every coordinate derivative `∂^α (x^M)` with `α₀ < M` (in particular every one of total
order `< M`) vanishes there. Yet its `n^{-1/2}` coefficient `√π/(2M)` is **nonzero**: the
observable is seen along the axis `y = 0` (the shallow stratum), not at the corner.

Together the two facts refute every reading of the coefficient formula of the shape

  `c_{1/2,0}(f) = ∑_{|α| ≤ R} B_α · ∂^α f(0,0)`   for a fixed finite `R` and fixed weights `B_α`:

take `f = x^{R+1}`; the right-hand side is `0` while `c_{1/2,0}(f) = √π/(2(R+1)) ≠ 0`
(`no_finite_cornerJet_formula`). Finite-jet dependence of the leading coefficients holds only along
the **whole** divisor `{x²y² = 0}` (`SmoothJetDetermination.lean`), and the constant coefficient
carries a finite-part (subtracted) integral along the axes.

The asymptotic is proved without any two-dimensional Fubini: the inner Gaussian integral is
`(x√n)^{-1} ∫₀^{x√n} e^{-t²} dt` (`twoD_inner` at `β = 1`, `a = 0`), the split
`∫₀^{s} e^{-t²} = √π/2 − T(s)` with the tail `T(s) = ∫_s^∞ e^{-t²} dt ≤ min(√π/2, M₁/s)`
(`quadMass_sub_primitive_le`, `M₁ = ∫₀^∞ t e^{-t²} dt = 1/2`) reduces `√n · ∫∫` to
`√π/(2M) − ∫₀¹ x^{M−1} T(x√n) dx`, and the error integral tends to `0` by dominated convergence.
Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Asymptotics Filter Topology

namespace Grammar

namespace SmoothEngine

/-! ### The Gaussian kernel and its tail as the quadratic kernel at `β = 1`, `a = 0` -/

theorem quadKernel_one_zero (s : ℝ) : quadKernel 1 0 s = Real.exp (-s ^ 2) := by
  simp [quadKernel]

theorem quadPrimitive_one_zero (s : ℝ) (hs : 0 ≤ s) :
    quadPrimitive 1 0 s = ∫ t in Ioc (0 : ℝ) s, Real.exp (-t ^ 2) := by
  rw [quadPrimitive, intervalIntegral.integral_of_le hs]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ => quadKernel_one_zero t

/-- `∫₀^∞ e^{-t²} dt = √π/2`. -/
theorem quadMass_one_zero : quadMass 1 0 = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi 1
  rw [quadMass, setIntegral_congr_fun measurableSet_Ioi fun t _ => quadKernel_one_zero t]
  simpa [neg_one_mul] using h

/-- `∫₀^∞ t e^{-t²} dt = 1/2`. -/
theorem quadMoment_one_zero : quadMoment 1 0 = 1 / 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1) (by norm_num)
    (by norm_num) one_pos
  rw [quadMoment, setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [quadKernel_one_zero]]
  have h2 : ∀ t : ℝ, t ^ (1 : ℝ) * Real.exp (-1 * t ^ (2 : ℝ)) = t * Real.exp (-t ^ 2) := by
    intro t; rw [Real.rpow_one, Real.rpow_two]; ring_nf
  simp_rw [h2] at h
  rw [h]; norm_num [Real.Gamma_one]

/-- The Gaussian tail `T(s) = √π/2 − ∫₀^s e^{-t²} dt` (`= ∫_s^∞ e^{-t²} dt` for `s ≥ 0`). -/
noncomputable def gaussTail (s : ℝ) : ℝ := quadMass 1 0 - quadPrimitive 1 0 s

theorem gaussTail_continuous : Continuous gaussTail :=
  continuous_const.sub (quadPrimitive_continuous 1 0)

theorem gaussTail_eq_integral (s : ℝ) (hs : 0 ≤ s) :
    gaussTail s = ∫ t in Ioi s, Real.exp (-t ^ 2) := by
  rw [gaussTail, quadMass_sub_primitive 1 0 s one_pos hs]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => quadKernel_one_zero t

theorem gaussTail_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ gaussTail s :=
  quadMass_sub_primitive_nonneg 1 0 s one_pos hs

theorem gaussTail_le_sqrt_pi (s : ℝ) (hs : 0 ≤ s) : gaussTail s ≤ Real.sqrt Real.pi / 2 := by
  rw [gaussTail, quadMass_one_zero]
  linarith [quadPrimitive_nonneg 1 0 s hs]

/-- The tail bound `T(s) ≤ 1/(2s)` for `s > 0` (from `∫_s^∞ e^{-t²} ≤ ∫_s^∞ (t/s) e^{-t²}`). -/
theorem gaussTail_le_inv (s : ℝ) (hs : 0 < s) : gaussTail s ≤ 1 / (2 * s) := by
  have h := quadMass_sub_primitive_le 1 0 s one_pos hs
  rw [quadMoment_one_zero] at h
  rw [gaussTail]; convert h using 1; field_simp

/-- **The Gaussian split** `∫₀^s e^{-t²} dt = √π/2 − T(s)` for `s ≥ 0`. -/
theorem integral_Ioc_exp_neg_sq (s : ℝ) (hs : 0 ≤ s) :
    ∫ t in Ioc (0 : ℝ) s, Real.exp (-t ^ 2) = Real.sqrt Real.pi / 2 - gaussTail s := by
  rw [gaussTail, quadMass_one_zero, quadPrimitive_one_zero s hs]; ring

/-! ### The inner integral -/

/-- **Inner substitution** `t = x√n · y`. -/
theorem xM_inner (M : ℕ) (n x : ℝ) (hn : 0 < n) (hx : 0 < x) :
    ∫ y in Ioc (0 : ℝ) 1, x ^ M * Real.exp (-n * (x ^ 2 * y ^ 2))
      = x ^ M * ((1 / (x * Real.sqrt n))
          * ∫ t in Ioc (0 : ℝ) (x * Real.sqrt n), Real.exp (-t ^ 2)) := by
  have h := twoD_inner 1 0 1 n x hn hx one_pos
  have hfun : ∀ y : ℝ, x ^ M * Real.exp (-n * (x ^ 2 * y ^ 2))
      = x ^ M * Real.exp (-1 * n * (x * y) ^ 2 + 1 * Real.sqrt n * (x * y) * 0) := by
    intro y; congr 2; ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_const_mul, h, mul_one,
    quadPrimitive_one_zero _ (by positivity), one_div, mul_comm x]

/-- On `(0,1]`, the inner integral is `n^{-1/2} · x^{M−1} · (√π/2 − T(x√n))` (`M ≥ 1`). -/
theorem xM_inner_eq (K : ℕ) (n x : ℝ) (hn : 0 < n) (hx : 0 < x) :
    ∫ y in Ioc (0 : ℝ) 1, x ^ (K + 1) * Real.exp (-n * (x ^ 2 * y ^ 2))
      = (Real.sqrt n)⁻¹ * (x ^ K * (Real.sqrt Real.pi / 2 - gaussTail (x * Real.sqrt n))) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  rw [xM_inner (K + 1) n x hn hx, integral_Ioc_exp_neg_sq _ (by positivity), pow_succ]
  field_simp

/-! ### The outer integral and the error term -/

/-- `√n · ∫∫ x^{K+1} e^{-n x²y²} = √π/(2(K+1)) − ∫₀¹ x^K T(x√n) dx` for `n > 0`. -/
theorem xM_sqrt_mul_eq (K : ℕ) (n : ℝ) (hn : 0 < n) :
    Real.sqrt n * ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1,
        x ^ (K + 1) * Real.exp (-n * (x ^ 2 * y ^ 2))
      = Real.sqrt Real.pi / (2 * ((K + 1 : ℕ) : ℝ))
        - ∫ x in Ioc (0 : ℝ) 1, x ^ K * gaussTail (x * Real.sqrt n) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  rw [setIntegral_congr_fun measurableSet_Ioc fun x hx => xM_inner_eq K n x hn hx.1,
    MeasureTheory.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hsn.ne', one_mul]
  have h1 : IntegrableOn (fun x : ℝ => x ^ K * (Real.sqrt Real.pi / 2)) (Ioc 0 1) :=
    ((continuous_pow K).mul continuous_const).integrableOn_Ioc
  have h2 : IntegrableOn (fun x : ℝ => x ^ K * gaussTail (x * Real.sqrt n)) (Ioc 0 1) :=
    ((continuous_pow K).mul
      (gaussTail_continuous.comp (continuous_id.mul continuous_const))).integrableOn_Ioc
  simp_rw [mul_sub]
  rw [MeasureTheory.integral_sub h1 h2, MeasureTheory.integral_mul_const,
    ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  push_cast
  simp only [one_pow, zero_pow (Nat.succ_ne_zero K), sub_zero]
  congr 1
  field_simp

/-- **The error term vanishes**: `∫₀¹ x^K T(x√n) dx → 0` (dominated convergence, bound `√π/2`). -/
theorem xM_error_tendsto (K : ℕ) :
    Tendsto (fun n : ℝ => ∫ x in Ioc (0 : ℝ) 1, x ^ K * gaussTail (x * Real.sqrt n))
      atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (l := atTop) (F := fun (n : ℝ) (x : ℝ) => x ^ K * gaussTail (x * Real.sqrt n))
    (f := fun _ => (0 : ℝ)) (fun _ => Real.sqrt Real.pi / 2) ?_ ?_ ?_ ?_
  · simpa using h
  · exact Eventually.of_forall fun n => ((continuous_pow K).mul
      (gaussTail_continuous.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hxs : 0 ≤ x * Real.sqrt n := mul_nonneg hx.1.le (Real.sqrt_nonneg n)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hx.1.le K) (gaussTail_nonneg _ hxs))]
    calc x ^ K * gaussTail (x * Real.sqrt n) ≤ 1 * (Real.sqrt Real.pi / 2) := by
          gcongr
          · exact gaussTail_nonneg _ hxs
          · exact pow_le_one₀ hx.1.le hx.2
          · exact gaussTail_le_sqrt_pi _ hxs
      _ = _ := one_mul _
  · exact continuous_const.integrableOn_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    have hT : Tendsto (fun n : ℝ => gaussTail (x * Real.sqrt n)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ (g := fun n : ℝ => 1 / (2 * x) * (Real.sqrt n)⁻¹) ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with n hn
        exact gaussTail_nonneg _ (mul_nonneg hx.1.le (Real.sqrt_nonneg n))
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
        have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
        calc gaussTail (x * Real.sqrt n) ≤ 1 / (2 * (x * Real.sqrt n)) :=
              gaussTail_le_inv _ (mul_pos hx.1 hsn)
          _ = 1 / (2 * x) * (Real.sqrt n)⁻¹ := by field_simp
      · have := (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).const_mul (1 / (2 * x))
        rw [mul_zero] at this
        exact this
    have := hT.const_mul (x ^ K)
    rw [mul_zero] at this
    exact this

/-! ### The asymptotic -/

/-- **`√n`-scaled limit**: `n^{1/2} ∫∫ x^M e^{-n x²y²} → √π/(2M)` for `M ≥ 1`. -/
theorem xM_tendsto (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun n : ℝ => n ^ (1 / 2 : ℝ) * ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1,
        x ^ M * Real.exp (-n * (x ^ 2 * y ^ 2)))
      atTop (𝓝 (Real.sqrt Real.pi / (2 * M))) := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  have h := (tendsto_const_nhds (x := Real.sqrt Real.pi / (2 * ((K + 1 : ℕ) : ℝ)))).sub
    (xM_error_tendsto K)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  rw [← xM_sqrt_mul_eq K n hn, Real.sqrt_eq_rpow]

/-- **Shallow-stratum detection** (consult #122, regression 2): for every `M ≥ 1`,
`∫₀¹∫₀¹ x^M e^{-n x²y²} dy dx ~ (√π/(2M)) · n^{-1/2}`. The coefficient is nonzero although
`x^M` has vanishing jet of order `M − 1` at the corner (`xM_jet_vanish`). -/
theorem xM_isEquivalent (M : ℕ) (hM : 1 ≤ M) :
    (fun n : ℝ => ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1,
        x ^ M * Real.exp (-n * (x ^ 2 * y ^ 2)))
      ~[atTop] fun n : ℝ => Real.sqrt Real.pi / (2 * M) * n ^ (-(1 / 2 : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : Real.sqrt Real.pi / (2 * (M : ℝ)) ≠ 0 := by positivity
  apply isEquivalent_of_tendsto_one
  have h := (xM_tendsto M hM).div_const (Real.sqrt Real.pi / (2 * M))
  rw [div_self hc] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  have hp : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  simp only [Pi.div_apply]
  rw [Real.rpow_neg hn.le]
  field_simp

theorem xM_coeff_ne_zero (M : ℕ) (hM : 1 ≤ M) : Real.sqrt Real.pi / (2 * (M : ℝ)) ≠ 0 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  positivity

/-! ### The corner jet of `x^M` vanishes -/

theorem pd_zero_const_mul_pow (c : ℝ) (k : ℕ) :
    pd 0 (fun v : Fin 2 → ℝ => c * v 0 ^ k) = fun v => c * k * v 0 ^ (k - 1) := by
  funext v
  unfold pd line
  simp only [Function.update_self]
  rw [((hasDerivAt_pow k (v 0)).const_mul c).deriv]; ring

theorem pd_one_const_mul_pow (c : ℝ) (k : ℕ) :
    pd 1 (fun v : Fin 2 → ℝ => c * v 0 ^ k) = 0 := by
  funext v
  unfold pd line
  simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), deriv_const, Pi.zero_apply]

theorem pd_zero_fun {d : ℕ} (i : Fin d) : pd i (0 : (Fin d → ℝ) → ℝ) = 0 := by
  funext v
  unfold pd line
  simp only [Pi.zero_apply, deriv_const]

theorem pdPow_zero_fun {d : ℕ} (i : Fin d) (a : ℕ) : pdPow i a (0 : (Fin d → ℝ) → ℝ) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pdPow_succ', ih, pd_zero_fun]

/-- `∂₀^a (x^k) = c · x^{k−a}` for some constant `c`. -/
theorem pdPow_zero_pow (a k : ℕ) :
    ∃ c : ℝ, pdPow 0 a (fun v : Fin 2 → ℝ => v 0 ^ k) = fun v => c * v 0 ^ (k - a) := by
  induction a with
  | zero => exact ⟨1, by funext v; simp [pdPow_zero]⟩
  | succ a ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * ((k - a : ℕ) : ℝ), ?_⟩
    rw [pdPow_succ', hc, pd_zero_const_mul_pow]
    funext v
    rw [Nat.sub_sub]

/-- `∂₁^q (x^k) = 0` for `q ≥ 1`. -/
theorem pdPow_one_pow (q k : ℕ) (hq : 1 ≤ q) :
    pdPow 1 q (fun v : Fin 2 → ℝ => v 0 ^ k) = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  induction q with
  | zero =>
    rw [pdPow_succ', pdPow_zero]
    simpa using pd_one_const_mul_pow 1 k
  | succ q ih => rw [pdPow_succ', ih (by omega), pd_zero_fun]

/-- **The corner jet vanishes**: every coordinate derivative `∂^α (x^M)` with `α₀ < M` is `0` at
the corner `(0,0)`. -/
theorem xM_jet_vanish (M : ℕ) {α : Fin 2 → ℕ} (hα : α 0 < M) :
    pdMulti α (List.finRange 2) (fun v : Fin 2 → ℝ => v 0 ^ M) 0 = 0 := by
  rw [show List.finRange 2 = [0, 1] from rfl, pdMulti_cons, pdMulti_cons, pdMulti_nil]
  rcases Nat.eq_zero_or_pos (α 1) with h1 | h1
  · rw [h1, pdPow_zero]
    obtain ⟨c, hc⟩ := pdPow_zero_pow (α 0) M
    rw [hc]
    simp only [Pi.zero_apply]
    rw [zero_pow (by omega), mul_zero]
  · rw [pdPow_one_pow _ _ h1, pdPow_zero_fun]; rfl

/-- The total-order form: all corner derivatives of `x^M` of total order `< M` vanish. -/
theorem xM_jet_vanish_of_total (M : ℕ) {α : Fin 2 → ℕ} (hα : ∑ i, α i < M) :
    pdMulti α (List.finRange 2) (fun v : Fin 2 → ℝ => v 0 ^ M) 0 = 0 := by
  rw [Fin.sum_univ_two] at hα
  exact xM_jet_vanish M (by omega)

/-- **No finite corner-jet formula.** For every order `R`, every finite family `S` of multi-indices
of total order `≤ R`, and every weights `B`, the observable `x^{R+1}` has jet sum `0` at the corner
while its `n^{-1/2}` coefficient is `√π/(2(R+1)) ≠ 0`. -/
theorem no_finite_cornerJet_formula (R : ℕ) (S : Finset (Fin 2 → ℕ))
    (hS : ∀ α ∈ S, ∑ i, α i ≤ R) (B : (Fin 2 → ℕ) → ℝ) :
    ∑ α ∈ S, B α * pdMulti α (List.finRange 2) (fun v : Fin 2 → ℝ => v 0 ^ (R + 1)) 0 = 0
      ∧ Tendsto (fun n : ℝ => n ^ (1 / 2 : ℝ) * ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1,
          x ^ (R + 1) * Real.exp (-n * (x ^ 2 * y ^ 2)))
        atTop (𝓝 (Real.sqrt Real.pi / (2 * ((R + 1 : ℕ) : ℝ))))
      ∧ Real.sqrt Real.pi / (2 * ((R + 1 : ℕ) : ℝ)) ≠ 0 :=
  ⟨Finset.sum_eq_zero fun α hα => by
      rw [xM_jet_vanish_of_total (R + 1) (Nat.lt_succ_of_le (hS α hα)), mul_zero],
    xM_tendsto (R + 1) (by omega), xM_coeff_ne_zero (R + 1) (by omega)⟩

end SmoothEngine

end Grammar
