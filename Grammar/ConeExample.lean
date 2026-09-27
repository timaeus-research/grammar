/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PolarTwoDimExamples

/-!
# The cone example: the blow-up chart of `K = q²`, `q` a quadratic form of signature `(2,2)`

The bilinear model `q(a, b) = a₁b₁ + a₂b₂` (a linear network with a width-two hidden layer and zero
target) has divergence `K = q²` whose zero set is a quadric cone in `ℝ⁴`, singular at the vertex.
Blowing up the vertex, `w = x·(1, y, z, u)`, gives `K = x⁴ (y + zu)²`, and with `v = y + zu` the
phase is the normal-crossing monomial `x⁴ v²` with Jacobian `|x|³`: the blow-up chart has the wall
data `h = (3, 0)`, `k = (2, 1)` in the active coordinates `(x, v)` (the coordinates `z, u` are
inert).
The exceptional divisor `x = 0` has ratio `(3+1)/4 = 1` and the strict transform of the cone `v = 0`
has ratio `1/2`, so the leading pair is `(½, 1)` and the vertex enters at the exponent `1`.

This module computes the chart data of the paper's machinery for this chart with a constant
amplitude and a constant field, exactly as `PolarTwoDimExamples` does for `x²y²`:

* `chartZeta c (3,0) (2,1) s = c / ((4 − 4s)(1 − 2s))`, so the polar coefficients are
  `C_{½,1} = −c/4` (i.e. `A_{½,1} = c/4`) at `μ = ½` and `C_{1,1} = c/4` (`A_{1,1} = −c/4`) at
  `μ = 1`, both simple poles (`chartPolarCoeff_const_cone_half`, `chartPolarCoeff_const_cone_one`);
  the candidate double pole at `μ = 1` (the `v`-wall resonates there at order one) has coefficient
  zero for a constant amplitude;
* the coupling-average formula (B4) with a constant field `a` gives the frozen coefficients
  `c_{½,0} = S_{½}(a)/4` and `c_{1,0} = −S_1(a)/4` of the chart integral
  `∫_{(0,1]²} x³ e^{−N x⁴v² + √N x²v a} dx dv` (★★ `empCoeff_cone_half`, `empCoeff_cone_one`):
  the cone wall carries the leading term with the fluctuation function at index `½`, and the
  vertex wall carries a NEGATIVE first correction with the fluctuation function at index `1`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-- The Jacobian exponents of the blow-up chart of the cone: `(3, 0)`. -/
def coneH : Fin 2 → ℕ := ![3, 0]

/-- The half phase exponents of the blow-up chart of the cone: `(2, 1)`. -/
def coneK : Fin 2 → ℕ := ![2, 1]

theorem coneH_zero : coneH 0 = 3 := rfl
theorem coneH_one : coneH 1 = 0 := rfl
theorem coneK_zero : coneK 0 = 2 := rfl
theorem coneK_one : coneK 1 = 1 := rfl

theorem coneK_pos : ∀ i, 0 < coneK i := by
  intro i; fin_cases i <;> simp [coneK]

/-- The chart zeta functional of a constant amplitude on the cone chart. -/
theorem chartZeta_const_cone {F : (Fin 2 → ℝ) → ℝ} {c : ℝ} (hFc : ∀ v, F v = c) {s : ℂ}
    (hs : ZetaStrip coneH coneK s) :
    chartZeta F coneH coneK s = (c : ℂ) / ((4 - 4 * s) * (1 - 2 * s)) := by
  have h1 : (4 : ℂ) - 4 * s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    have hs0 := hs 0
    simp [coneH, coneK] at this hs0
    linarith
  have h2 : (1 : ℂ) - 2 * s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    have hs1 := hs 1
    simp [coneH, coneK] at this hs1
    linarith
  unfold chartZeta
  have hpt : ∀ u, (F u : ℂ) * cpowWeight coneH coneK s u =
      (c : ℂ) * cpowWeight coneH coneK s u := fun u => by rw [hFc]
  simp_rw [hpt]
  rw [integral_const_mul, integral_box_cpowWeight _ _ hs, Fin.prod_univ_two]
  simp only [coneH, coneK, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  rw [show (3 : ℂ) - 2 * 2 * s + 1 = 4 - 4 * s by ring,
    show (0 : ℂ) - 2 * 1 * s + 1 = 1 - 2 * s by ring, one_div_mul_one_div, mul_one_div]

/-- The local representative `g(s) = c/((4 − 4s)(1 − 2s))` is holomorphic off `{½, 1}`. -/
theorem differentiableOn_cone_g (c : ℝ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun s : ℂ => (c : ℂ) / ((4 - 4 * s) * (1 - 2 * s)))
      (U \ ({((1 / 2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)} : Set ℂ)) := by
  refine (differentiableOn_const _).div
    (((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).mul
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)))
    fun s hs => ?_
  refine mul_ne_zero (fun h0 => hs.2 ?_) fun h0 => hs.2 ?_
  · have : s = ((1 : ℝ) : ℂ) := by push_cast; linear_combination -h0 / 4
    simp [this]
  · have : s = ((1 / 2 : ℝ) : ℂ) := by push_cast; linear_combination -h0 / 2
    simp [this]

theorem cone_seed' : ((-1 / 2 : ℝ) : ℂ) ∉ ({((1 / 2 : ℝ) : ℂ), ((1 : ℝ) : ℂ)} : Set ℂ) := by
  norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, Complex.ofReal_inj]

/-- The face sum of a constant amplitude on the cone chart agrees with `g` near every `μ` in the
flat strip. -/
theorem chartZetaAtDepth_const_cone_eventuallyEq (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    {F : (Fin 2 → ℝ) → ℝ} {c : ℝ} (hFc : ∀ v, F v = c) {μ : ℝ}
    (hμ : FlatStrip p coneH coneK (μ : ℂ)) (hμ1 : -1 < μ) :
    chartZetaAtDepth p F coneH coneK =ᶠ[𝓝[≠] (μ : ℂ)]
      fun s : ℂ => (c : ℂ) / ((4 - 4 * s) * (1 - 2 * s)) := by
  have hF : ContDiff ℝ ∞ F := by
    have : F = fun _ => c := funext hFc
    rw [this]; exact contDiff_const
  exact chartZetaAtDepth_eventuallyEq_of_eqOn_strip p hF coneH coneK coneK_pos hp0
    (Set.toFinite _) (differentiableOn_cone_g c _) (fun s hs _ => chartZeta_const_cone hFc hs)
    cone_seed' hμ hμ1

theorem poleOrder_cone_le (p : Fin 2 → ℕ) (μ : ℝ) :
    ∀ x ∈ SmoothEngine.faceIndex p, poleOrder coneH coneK x.1 x.2 μ ≤ 1 + 1 :=
  fun x _ => poleOrder_le _ _ x.1 x.2 _

/-- ★ The polar coefficients of a constant amplitude on the cone chart at `μ = ½`: a simple pole
with `C_{½,1} = −c/4`. -/
theorem chartPolarCoeff_const_cone_half (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p coneH coneK ((1 / 2 : ℝ) : ℂ)) {F : (Fin 2 → ℝ) → ℝ} {c : ℝ}
    (hFc : ∀ v, F v = c) :
    chartPolarCoeff p F coneH coneK (1 / 2) 0 = -(c : ℂ) / 4 ∧
      chartPolarCoeff p F coneH coneK (1 / 2) 1 = 0 := by
  have hF : ContDiff ℝ ∞ F := by
    have : F = fun _ => c := funext hFc
    rw [this]; exact contDiff_const
  have hev := chartZetaAtDepth_const_cone_eventuallyEq p hp0 hFc hμ (by norm_num)
  set a : ℕ → ℂ := fun q => if q = 0 then -(c : ℂ) / 4 else 0 with hadef
  -- `g − polarPart = −c/(4(1−s))` on a punctured neighbourhood, a bounded function
  have hr : Tendsto (fun s : ℂ => -(c : ℂ) / (4 * (1 - s))) (𝓝[≠] ((1 / 2 : ℝ) : ℂ))
      (𝓝 (-(c : ℂ) / (4 * (1 - ((1 / 2 : ℝ) : ℂ))))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
    refine continuousAt_const.div (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))
      ?_
    norm_num
  have ha : (fun s => (c : ℂ) / ((4 - 4 * s) * (1 - 2 * s)) -
      polarPart 1 a ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
    refine (hr.isBigO_one (F := ℂ)).congr' ?_ (EventuallyEq.refl _ _)
    have hne1 : ∀ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), s ≠ ((1 : ℝ) : ℂ) := by
      refine nhdsWithin_le_nhds (isOpen_ne.mem_nhds ?_)
      norm_num [Complex.ofReal_inj]
    filter_upwards [self_mem_nhdsWithin, hne1] with s hs hs1
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := by
      intro h0; apply hs'; push_cast; linear_combination -h0 / 2
    have h1s : (1 : ℂ) - s ≠ 0 := by
      intro h0; apply hs1; push_cast; linear_combination -h0
    have h4s : (4 : ℂ) - 4 * s ≠ 0 := by
      intro h0; apply h1s; linear_combination h0 / 4
    have hPP : polarPart 1 a ((1 / 2 : ℝ) : ℂ) s = -(c : ℂ) / 4 / (s - ((1 / 2 : ℝ) : ℂ)) := by
      unfold polarPart
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp [hadef]
    rw [hPP]
    push_cast at hs' ⊢
    have hA : (4 - 4 * s) * (1 - 2 * s) ≠ 0 := mul_ne_zero h4s h2s
    have hC : (4 : ℂ) * (1 - s) ≠ 0 := mul_ne_zero (by norm_num) h1s
    rw [div_sub_div _ _ hA hs', div_eq_div_iff hC (mul_ne_zero hA hs')]
    ring
  have := chartPolarCoeff_eq_of_eventuallyEq p hF coneH coneK hp0 hμ (poleOrder_cone_le p _) hev ha
  exact ⟨by simpa [hadef] using this 0 zero_le_one, by simpa [hadef] using this 1 le_rfl⟩

/-- ★ The polar coefficients of a constant amplitude on the cone chart at `μ = 1`: a simple pole
with `C_{1,1} = c/4`; the candidate double pole has coefficient zero. -/
theorem chartPolarCoeff_const_cone_one (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p coneH coneK ((1 : ℝ) : ℂ)) {F : (Fin 2 → ℝ) → ℝ} {c : ℝ}
    (hFc : ∀ v, F v = c) :
    chartPolarCoeff p F coneH coneK 1 0 = (c : ℂ) / 4 ∧
      chartPolarCoeff p F coneH coneK 1 1 = 0 := by
  have hF : ContDiff ℝ ∞ F := by
    have : F = fun _ => c := funext hFc
    rw [this]; exact contDiff_const
  have hev := chartZetaAtDepth_const_cone_eventuallyEq p hp0 hFc hμ (by norm_num)
  set a : ℕ → ℂ := fun q => if q = 0 then (c : ℂ) / 4 else 0 with hadef
  -- `g − polarPart = c/(2(1−2s))` on a punctured neighbourhood, a bounded function
  have hr : Tendsto (fun s : ℂ => (c : ℂ) / (2 * (1 - 2 * s))) (𝓝[≠] ((1 : ℝ) : ℂ))
      (𝓝 ((c : ℂ) / (2 * (1 - 2 * ((1 : ℝ) : ℂ))))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
    refine continuousAt_const.div (continuousAt_const.mul
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))) ?_
    norm_num
  have ha : (fun s => (c : ℂ) / ((4 - 4 * s) * (1 - 2 * s)) -
      polarPart 1 a ((1 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
    refine (hr.isBigO_one (F := ℂ)).congr' ?_ (EventuallyEq.refl _ _)
    have hne1 : ∀ᶠ s in 𝓝[≠] ((1 : ℝ) : ℂ), s ≠ ((1 / 2 : ℝ) : ℂ) := by
      refine nhdsWithin_le_nhds (isOpen_ne.mem_nhds ?_)
      norm_num [Complex.ofReal_inj]
    filter_upwards [self_mem_nhdsWithin, hne1] with s hs hs1
    have hs' : s - (1 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := by
      intro h0; apply hs1; push_cast; linear_combination -h0 / 2
    have h4s : (4 : ℂ) - 4 * s ≠ 0 := by
      intro h0; apply hs'; push_cast; linear_combination -h0 / 4
    have hPP : polarPart 1 a ((1 : ℝ) : ℂ) s = (c : ℂ) / 4 / (s - ((1 : ℝ) : ℂ)) := by
      unfold polarPart
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp [hadef]
    rw [hPP]
    push_cast at hs' ⊢
    have hA : (4 - 4 * s) * (1 - 2 * s) ≠ 0 := mul_ne_zero h4s h2s
    have hC : (2 : ℂ) * (1 - 2 * s) ≠ 0 := mul_ne_zero (by norm_num) h2s
    rw [div_sub_div _ _ hA hs', div_eq_div_iff hC (mul_ne_zero hA hs')]
    ring
  have := chartPolarCoeff_eq_of_eventuallyEq p hF coneH coneK hp0 hμ (poleOrder_cone_le p _) hev ha
  exact ⟨by simpa [hadef] using this 0 zero_le_one, by simpa [hadef] using this 1 le_rfl⟩

/-! ### The frozen coefficients with a constant field, via the coupling-average formula -/

/-- The canonical depth of the cone chart at cutoff `4` is `(13, 8)`. -/
theorem depthOf_cone : depthOf coneH coneK 4 = ![13, 8] := by
  funext i; fin_cases i <;> simp [depthOf, coneH, coneK]

theorem flatStrip_cone_half : FlatStrip (![13, 8] : Fin 2 → ℕ) coneH coneK ((1 / 2 : ℝ) : ℂ) := by
  intro i; fin_cases i <;> norm_num [coneH, coneK]

theorem flatStrip_cone_one : FlatStrip (![13, 8] : Fin 2 → ℕ) coneH coneK ((1 : ℝ) : ℂ) := by
  intro i; fin_cases i <;> norm_num [coneH, coneK]

theorem Qamb_cone : Qamb coneK = 4 := by simp [Qamb, coneK, Fin.prod_univ_two]

theorem L₀_cone : L₀ coneH = 4 := by simp [L₀, coneH, Fin.sum_univ_two]

/-- The coupling kernel at a real index against a real function is a real integral. -/
theorem integral_coupKernel_mul_ofReal (μ : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), coupKernel (μ : ℂ) t * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * Real.exp (-t) * f t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  unfold coupKernel
  rw [show (μ : ℂ) - 1 = ((μ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht'.le]
  push_cast
  ring

/-- The coupling integral of the constant tilted amplitude `e^{a√t}` at index `μ` is `S_μ(a)`. -/
theorem integral_coupKernel_exp_sqrt (μ a : ℝ) :
    ∫ t in Ioi (0 : ℝ), coupKernel (μ : ℂ) t * ((Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) =
      ((fluctuation 1 μ a / 4 : ℝ) : ℂ) := by
  rw [integral_coupKernel_mul_ofReal]
  congr 1
  unfold fluctuation
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show Real.exp (-1 * t + 1 * a * Real.sqrt t) = Real.exp (-t) * Real.exp (Real.sqrt t * a) by
    rw [← Real.exp_add]; ring_nf]
  ring

/-- ★★ **The coupling-average coefficients of the cone chart with constant field `a`.** -/
theorem couplingPolarCoeff_cone (a : ℝ) :
    couplingPolarCoeff ![13, 8] (fun _ => 1) (fun _ => a) coneH coneK (1 / 2) 0 =
        (-(fluctuation 1 (1 / 2) a) / 4 : ℝ) ∧
      couplingPolarCoeff ![13, 8] (fun _ => 1) (fun _ => a) coneH coneK 1 0 =
        (fluctuation 1 1 a / 4 : ℝ) := by
  have hp0 : ∀ i : Fin 2, 0 < (![13, 8] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp
  have hhalf : ∀ t : ℝ,
      chartPolarCoeff ![13, 8] (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) coneH coneK
          (1 / 2) 0 = -(Real.exp (Real.sqrt t * a) : ℂ) / 4 ∧
      chartPolarCoeff ![13, 8] (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) coneH coneK
          (1 / 2) 1 = 0 := fun t =>
    chartPolarCoeff_const_cone_half _ hp0 flatStrip_cone_half
      (c := Real.exp (Real.sqrt t * a)) fun v => by simp [fieldFam]
  have hone : ∀ t : ℝ,
      chartPolarCoeff ![13, 8] (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) coneH coneK
          1 0 = (Real.exp (Real.sqrt t * a) : ℂ) / 4 ∧
      chartPolarCoeff ![13, 8] (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) coneH coneK
          1 1 = 0 := fun t =>
    chartPolarCoeff_const_cone_one _ hp0 flatStrip_cone_one
      (c := Real.exp (Real.sqrt t * a)) fun v => by simp [fieldFam]
  constructor
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 0 2 = {0, 1} from rfl, Finset.sum_pair (by norm_num)]
    simp only [Nat.sub_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
      pow_zero, pow_one, mul_one]
    simp_rw [(hhalf _).1, (hhalf _).2]
    simp only [mul_zero, integral_zero, add_zero]
    have hfun : (fun t : ℝ => coupKernel ((1 / 2 : ℝ) : ℂ) t *
        (-(Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => -(coupKernel ((1 / 2 : ℝ) : ℂ) t *
          ((Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ)) := by
      funext t; push_cast; ring
    rw [hfun, integral_neg, integral_coupKernel_exp_sqrt]
    push_cast
    ring
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 0 2 = {0, 1} from rfl, Finset.sum_pair (by norm_num)]
    simp only [Nat.sub_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
      pow_zero, pow_one, mul_one]
    simp_rw [(hone _).1, (hone _).2]
    simp only [mul_zero, integral_zero, add_zero]
    have hfun : (fun t : ℝ => coupKernel ((1 : ℝ) : ℂ) t * ((Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => coupKernel ((1 : ℝ) : ℂ) t * ((Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) := by
      funext t; push_cast; ring
    rw [hfun, integral_coupKernel_exp_sqrt]

theorem cone_lattice_half : (1 / 2 : ℝ) ∈ latticeBelow (Qamb coneK) ((4 : ℕ) : ℝ) := by
  rw [Qamb_cone, show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) by norm_num]
  exact mem_latticeBelow (by norm_num) (by norm_num)

theorem cone_lattice_one : (1 : ℝ) ∈ latticeBelow (Qamb coneK) ((4 : ℕ) : ℝ) := by
  rw [Qamb_cone, show (1 : ℝ) = ((4 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) by norm_num]
  exact mem_latticeBelow (by norm_num) (by norm_num)

/-- ★★★ **The frozen leading coefficient of the cone chart**: with a constant field `a`, the
coefficient of `N^{−½}` in `∫_{(0,1]²} x³ e^{−N x⁴v² + √N x²v a}` is `S_{½}(a)/4`. -/
theorem empCoeff_cone_half (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) coneH coneK (1 / 2) 0 =
      fluctuation 1 (1 / 2) a / 4 := by
  have hL : L₀ coneH ≤ 4 := by rw [L₀_cone]
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const coneK_pos hL cone_lattice_half
    (by norm_num) (by norm_num) (q := 0) (by norm_num)
  rw [depthOf_cone, (couplingPolarCoeff_cone a).1] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- ★★★ **The frozen first correction of the cone chart**: with a constant field `a`, the
coefficient of `N^{−1}` is `−S_1(a)/4`, a NEGATIVE contribution carried by the vertex wall, with
no logarithm. -/
theorem empCoeff_cone_one (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) coneH coneK 1 0 =
      -(fluctuation 1 1 a) / 4 := by
  have hL : L₀ coneH ≤ 4 := by rw [L₀_cone]
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const coneK_pos hL cone_lattice_one
    (by norm_num) (by norm_num) (q := 0) (by norm_num)
  rw [depthOf_cone, (couplingPolarCoeff_cone a).2] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- The candidate logarithm at `μ = 1` is absent: the coefficient of `N^{−1} log N` vanishes. -/
theorem empCoeff_cone_one_log (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) coneH coneK 1 1 = 0 := by
  have hL : L₀ coneH ≤ 4 := by rw [L₀_cone]
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const coneK_pos hL cone_lattice_one
    (by norm_num) (by norm_num) (q := 1) (by norm_num)
  rw [depthOf_cone] at h
  have hp0 : ∀ i : Fin 2, 0 < (![13, 8] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp
  have hzero : couplingPolarCoeff ![13, 8] (fun _ => 1) (fun _ => a) coneH coneK 1 1 = 0 := by
    unfold couplingPolarCoeff
    rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton]
    have hone : ∀ t : ℝ,
        chartPolarCoeff ![13, 8] (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) coneH coneK
          1 1 = 0 := fun t =>
      (chartPolarCoeff_const_cone_one _ hp0 flatStrip_cone_one
        (c := Real.exp (Real.sqrt t * a)) fun v => by simp [fieldFam]).2
    simp [hone]
  rw [hzero] at h
  apply Complex.ofReal_injective
  rw [h]
  simp

/-- At zero field the two coefficients are the population values `√π/4` and `−1/4`. -/
theorem empCoeff_cone_zero_field :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => (0 : ℝ)) coneH coneK (1 / 2) 0 =
        Real.sqrt Real.pi / 4 ∧
      empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => (0 : ℝ)) coneH coneK 1 0 = -1 / 4 := by
  rw [empCoeff_cone_half, empCoeff_cone_one, fluctuation_zero 1 (1 / 2) one_pos (by norm_num),
    fluctuation_zero 1 1 one_pos one_pos, Real.Gamma_one_half_eq, Real.Gamma_one]
  norm_num

end Grammar
