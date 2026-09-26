/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalCouplingAllLog
import Grammar.LogExampleTwoDim

/-!
# Regression of the coupling-average formula against the `x²y²` example (unit 14)

Two general determination lemmas and one worked example.

* `chartZetaAtDepth_eventuallyEq_of_eqOn_strip`: the meromorphic face sum is determined by the
  strip values of the chart zeta functional — if a function `g` holomorphic on the strip
  `−1 < Re s < flatEdge` minus a finite set agrees with `chartZeta F h k` on the initial strip,
  then it agrees with `chartZetaAtDepth p F h k` on a punctured neighbourhood of every `μ` in the
  flat strip (identity theorem, as in `chartZetaAtDepth_eq_of_depths`).
* `chartPolarCoeff_eq_of_eventuallyEq`: the chart polar coefficients are the principal-part
  coefficients of any such local representative (`polarPart_eq_of_sub_isBigO_one`).

The example is the paper's `x²y²` chart on the unit square with a constant amplitude and a
constant field `a`: `chartZeta c 0 (1,1) s = c/(1−2s)² = (c/4)/(s−½)²`, so at `μ = ½` the polar
coefficients are `c/4` (order two) and `0` (order one); the coupling-average formula (B4) then
gives

  `empCoeff 1 a 0 (1,1) ½ 1 = S_{½}(a)/4`,  `empCoeff 1 a 0 (1,1) ½ 0 = −∂_ν S_ν(a)|_{½} / 4`

(★★ `empCoeff_xy_sq_one`, `empCoeff_xy_sq_zero`), exactly the constants of the independently
proved asymptotic `tendsto_logExample` of `LogExampleTwoDim`
(`4√n ∫∫ e^{−n x²y² + a√n xy} − (log n · S_{½}(a) − ∂_ν S_ν(a)|_{½}) → 0`), restated as
★ `tendsto_logExample_empCoeff`.  For `a = 0` these are `√π/4` and `−Γ'(½)/4`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

/-! ### Determination of the face sum by its strip values -/

section Determination

variable {d : ℕ} [Nonempty (Fin d)]

/-- ★ **The face sum is determined by the strip values of the chart zeta functional.** -/
theorem chartZetaAtDepth_eventuallyEq_of_eqOn_strip (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hp0 : ∀ i, 0 < p i)
    {g : ℂ → ℂ} {P' : Set ℂ} (hP' : P'.Finite)
    (hg : DifferentiableOn ℂ g ({s : ℂ | -1 < s.re ∧ s.re < flatEdge p h k} \ P'))
    (hseed : ∀ s : ℂ, ZetaStrip h k s → s ∉ P' → chartZeta F h k s = g s)
    (hseed' : ((-1 / 2 : ℝ) : ℂ) ∉ P') {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ)) (hμ1 : -1 < μ) :
    chartZetaAtDepth p F h k =ᶠ[𝓝[≠] (μ : ℂ)] g := by
  set P : Set ℂ := {t | PoleAt p h k t} ∪ P' with hP
  set U : Set ℂ := {t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ P with hU
  have hPfin : P.Finite := (finite_poleSet p h k hk).union hP'
  have hUopen : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin.isClosed
  have hUsub : ∀ t ∈ U, FlatStrip p h k t ∧ ¬ PoleAt p h k t := fun t ht =>
    ⟨(flatStrip_iff_re_lt p h k hk t).2 ht.1.2, fun hp => ht.2 (Or.inl hp)⟩
  have hf : AnalyticOnNhd ℂ (chartZetaAtDepth p F h k) U :=
    ((differentiableOn_chartZetaAtDepth p hF h k hp0).mono hUsub).analyticOnNhd hUopen
  have hg' : AnalyticOnNhd ℂ g U :=
    (hg.mono fun t ht => ⟨ht.1, fun hp => ht.2 (Or.inr hp)⟩).analyticOnNhd hUopen
  have hLpos : 0 < flatEdge p h k := flatEdge_pos p h k hk
  have hconn : IsPreconnected U := isPreconnected_strip_diff_finite (by linarith) hPfin
  have hz₀ : ((-1 / 2 : ℝ) : ℂ) ∈ U := by
    refine ⟨⟨by simp; norm_num, by simp; linarith⟩, ?_⟩
    rintro (hp | hp)
    · have := pos_re_of_poleAt hk hp; simp at this; linarith
    · exact hseed' hp
  have hfg : chartZetaAtDepth p F h k =ᶠ[𝓝 ((-1 / 2 : ℝ) : ℂ)] g := by
    filter_upwards [(ZetaStrip.isOpen h k).mem_nhds (zetaStrip_neg_half h k),
      hP'.isClosed.isOpen_compl.mem_nhds hseed'] with t ht ht'
    rw [chartZetaAtDepth_eq_chartZeta p hF h k ht, hseed t ht ht']
  have hEq : EqOn (chartZetaAtDepth p F h k) g U :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg' hconn hz₀ hfg
  -- a punctured neighbourhood of `μ` lies in `U`
  have hPfin' : (P \ {(μ : ℂ)}).Finite := hPfin.sdiff
  have hopen : IsOpen ({t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ (P \ {(μ : ℂ)})) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).sdiff hPfin'.isClosed
  have hmem : (μ : ℂ) ∈ {t : ℂ | -1 < t.re ∧ t.re < flatEdge p h k} \ (P \ {(μ : ℂ)}) :=
    ⟨⟨by simpa using hμ1, by simpa using (flatStrip_iff_re_lt p h k hk _).1 hμ⟩,
      fun hp => hp.2 rfl⟩
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin] with t ht htμ
  exact hEq ⟨ht.1, fun hp => ht.2 ⟨hp, htμ⟩⟩

end Determination

section Coefficients

variable {d : ℕ}

/-- ★ **The chart polar coefficients are the principal-part coefficients of any local
representative.** -/
theorem chartPolarCoeff_eq_of_eventuallyEq (p : Fin d → ℕ) {F : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) {D : ℕ}
    (hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder h k x.1 x.2 μ ≤ D + 1) {g : ℂ → ℂ}
    {a : ℕ → ℂ} (hg : chartZetaAtDepth p F h k =ᶠ[𝓝[≠] (μ : ℂ)] g)
    (ha : (fun s => g s - polarPart D a (μ : ℂ) s) =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, chartPolarCoeff p F h k μ q = a q := by
  have h1 := chartZetaAtDepth_sub_polarPart_isBigO_one p hF h k hp0 hμ hD
  have h2 : (fun s => g s - polarPart D (chartPolarCoeff p F h k μ) (μ : ℂ) s)
      =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ) := by
    refine h1.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hg] with s hs
    rw [hs]
  have h3 := ha.sub h2
  intro q hq
  refine polarPart_eq_of_sub_isBigO_one (D := D) (a := chartPolarCoeff p F h k μ) (b := a)
    (h3.congr_left fun s => ?_) q hq
  ring

end Coefficients

/-! ### The `x²y²` chart with a constant amplitude -/

section Example

/-- The polar coefficients of a constant amplitude `c` on the `x²y²` unit square at `μ = ½`:
`c/4` at order two and `0` at order one (for every positive depth whose flat strip contains `½`,
with `D = 1`). -/
theorem chartPolarCoeff_const_xy_sq (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p 0 (fun _ => 1) ((1 / 2 : ℝ) : ℂ)) {F : (Fin 2 → ℝ) → ℝ} {c : ℝ}
    (hFc : ∀ v, F v = c) :
    chartPolarCoeff p F 0 (fun _ => 1) (1 / 2) 1 = (c : ℂ) / 4 ∧
      chartPolarCoeff p F 0 (fun _ => 1) (1 / 2) 0 = 0 := by
  have hF : ContDiff ℝ ∞ F := by
    have : F = fun _ => c := funext hFc
    rw [this]; exact contDiff_const
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  set g : ℂ → ℂ := fun s => (c : ℂ) / (1 - 2 * s) ^ 2 with hgdef
  -- the strip values
  have hseed : ∀ s : ℂ, ZetaStrip (0 : Fin 2 → ℕ) (fun _ => 1) s →
      s ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) → chartZeta F 0 (fun _ => 1) s = g s := by
    intro s hs _
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      have hs0 := hs 0
      simp at this hs0
      linarith
    unfold chartZeta
    have hpt : ∀ u, (F u : ℂ) * cpowWeight 0 (fun _ => 1) s u =
        (c : ℂ) * cpowWeight 0 (fun _ => 1) s u := fun u => by rw [hFc]
    simp_rw [hpt]
    rw [integral_const_mul, integral_box_cpowWeight _ _ hs]
    simp only [hgdef, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply,
      Nat.cast_zero, Nat.cast_one]
    rw [div_pow, one_pow, mul_one_div]
    congr 1
    ring
  have hg : DifferentiableOn ℂ g
      ({s : ℂ | -1 < s.re ∧ s.re < flatEdge p 0 (fun _ => 1)} \ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ)) := by
    refine (differentiableOn_const _).div
      (((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).pow _)
      fun s hs => ?_
    refine pow_ne_zero _ fun h0 => hs.2 ?_
    have : s = ((1 / 2 : ℝ) : ℂ) := by push_cast; linear_combination -h0 / 2
    simp [this]
  have hseed' : ((-1 / 2 : ℝ) : ℂ) ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) := by
    norm_num [Set.mem_singleton_iff, Complex.ofReal_inj]
  have hev := chartZetaAtDepth_eventuallyEq_of_eqOn_strip p hF 0 (fun _ => 1) hk hp0
    (Set.finite_singleton _) hg hseed hseed' hμ (by norm_num)
  -- the principal part of `g` at `½`
  set a : ℕ → ℂ := fun q => if q = 1 then (c : ℂ) / 4 else 0 with hadef
  have ha : (fun s => g s - polarPart 1 a ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)]
      fun _ => (1 : ℂ) := by
    refine (isBigO_refl (fun _ : ℂ => (0 : ℂ)) _).congr' ?_ (EventuallyEq.refl _ _) |>.trans
      (isBigO_zero _ _)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    have h2s : (1 : ℂ) - 2 * s ≠ 0 := by
      intro h0
      apply hs'
      push_cast
      linear_combination -h0 / 2
    have h4 : ((1 : ℂ) - 2 * s) ^ 2 = 4 * (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 := by push_cast; ring
    have hs2 : (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ hs'
    have hPP : polarPart 1 a ((1 / 2 : ℝ) : ℂ) s = (c : ℂ) / 4 / (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 := by
      unfold polarPart
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp [hadef]
    rw [hPP]
    simp only [hgdef]
    rw [h4]
    field_simp
    ring
  have hD : ∀ x ∈ SmoothEngine.faceIndex p, poleOrder 0 (fun _ => 1) x.1 x.2 (1 / 2) ≤ 1 + 1 :=
    fun x _ => poleOrder_le _ _ x.1 x.2 _
  have := chartPolarCoeff_eq_of_eventuallyEq p hF 0 (fun _ => 1) hp0 hμ hD hev ha
  exact ⟨by simpa [hadef] using this 1 le_rfl, by simpa [hadef] using this 0 zero_le_one⟩

/-- The canonical depth of the `x²y²` chart at cutoff `1` is `(2, 2)`. -/
theorem depthOf_xy_sq : depthOf (0 : Fin 2 → ℕ) (fun _ => 1) 1 = fun _ => 2 := by
  funext i; simp [depthOf]

theorem flatStrip_xy_sq_half :
    FlatStrip (fun _ => 2 : Fin 2 → ℕ) 0 (fun _ => 1) ((1 / 2 : ℝ) : ℂ) := fun _ => by
  simp

/-- The coupling kernel at `½` against a real function is the real fluctuation-type integral. -/
theorem integral_coupKernel_half_mul_ofReal (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), coupKernel ((1 / 2 : ℝ) : ℂ) t * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), t ^ ((1 / 2 : ℝ) - 1) * Real.exp (-t) * f t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  unfold coupKernel
  rw [show ((1 / 2 : ℝ) : ℂ) - 1 = (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht'.le]
  push_cast
  ring

/-- ★★ **The coupling-average coefficients of the `x²y²` chart with constant field `a`.** -/
theorem couplingPolarCoeff_xy_sq (a : ℝ) :
    couplingPolarCoeff (fun _ : Fin 2 => 2) (fun _ => 1) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 =
        (fluctuation 1 (1 / 2) a / 4 : ℝ) ∧
      couplingPolarCoeff (fun _ : Fin 2 => 2) (fun _ => 1) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0 =
        (deriv (fun ν => fluctuation 1 ν a) (1 / 2) / 4 : ℝ) := by
  have hp0 : ∀ i : Fin 2, 0 < (fun _ => 2 : Fin 2 → ℕ) i := fun _ => two_pos
  -- the tilted amplitudes are constant
  have hcoef : ∀ t : ℝ,
      chartPolarCoeff (fun _ => 2) (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) 0
          (fun _ => 1) (1 / 2) 1 = (Real.exp (Real.sqrt t * a) : ℂ) / 4 ∧
      chartPolarCoeff (fun _ => 2) (fieldFam (fun _ => 1) (fun _ => a) (Real.sqrt t)) 0
          (fun _ => 1) (1 / 2) 0 = 0 := fun t =>
    chartPolarCoeff_const_xy_sq _ hp0 flatStrip_xy_sq_half
      (c := Real.exp (Real.sqrt t * a)) fun v => by simp [fieldFam]
  constructor
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton]
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, mul_one]
    simp_rw [(hcoef _).1]
    have hfun : (fun t : ℝ => coupKernel ((1 / 2 : ℝ) : ℂ) t *
        ((Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => coupKernel ((1 / 2 : ℝ) : ℂ) t * ((Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) := by
      funext t; push_cast; ring
    rw [hfun, integral_coupKernel_half_mul_ofReal]
    congr 1
    unfold fluctuation
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show Real.exp (-1 * t + 1 * a * Real.sqrt t) = Real.exp (-t) * Real.exp (Real.sqrt t * a) by
      rw [← Real.exp_add]; ring_nf]
    ring
  · unfold couplingPolarCoeff
    rw [show Finset.Ico 0 2 = {0, 1} from rfl, Finset.sum_pair (by norm_num)]
    simp only [Nat.sub_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
      pow_zero, pow_one, mul_one]
    simp_rw [(hcoef _).1, (hcoef _).2]
    simp only [mul_zero, integral_zero, zero_add]
    have hfun : (fun t : ℝ => coupKernel ((1 / 2 : ℝ) : ℂ) t * (Real.log t : ℂ) *
        ((Real.exp (Real.sqrt t * a) : ℂ) / 4)) =
        fun t => coupKernel ((1 / 2 : ℝ) : ℂ) t *
          ((Real.log t * Real.exp (Real.sqrt t * a) / 4 : ℝ) : ℂ) := by
      funext t; push_cast; ring
    rw [hfun, integral_coupKernel_half_mul_ofReal, ← iteratedDeriv_one,
      iteratedDeriv_fluctuation_eq (by norm_num) a 1]
    congr 1
    unfold fluctuationLog
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show Real.exp (-t + a * Real.sqrt t) = Real.exp (-t) * Real.exp (Real.sqrt t * a) by
      rw [← Real.exp_add]; ring_nf]
    ring

/-- ★★★ **Regression**: the empirical coefficients of the `x²y²` chart with constant field `a`
at `μ = ½` — via the coupling-average formula — are `S_{½}(a)/4` and `−∂_ν S_ν(a)|_{½}/4`. -/
theorem empCoeff_xy_sq_one (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 =
      fluctuation 1 (1 / 2) a / 4 := by
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  have hL : L₀ (0 : Fin 2 → ℕ) ≤ 1 := by simp [L₀]
  have hQ : Qamb (fun _ => 1 : Fin 2 → ℕ) = 2 := by simp [Qamb]
  have hlat : (1 / 2 : ℝ) ∈ latticeBelow (Qamb (fun _ => 1 : Fin 2 → ℕ)) ((1 : ℕ) : ℝ) := by
    rw [hQ]
    have := mem_latticeBelow (Q := 2) two_pos (L := ((1 : ℕ) : ℝ)) (m := 1) (by norm_num)
    simpa using this
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const hk hL hlat
    (by norm_num) (by norm_num) (q := 1) (by norm_num)
  rw [depthOf_xy_sq, (couplingPolarCoeff_xy_sq a).1] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

theorem empCoeff_xy_sq_zero (a : ℝ) :
    empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0 =
      -(deriv (fun ν => fluctuation 1 ν a) (1 / 2)) / 4 := by
  have hk : ∀ i : Fin 2, 0 < (fun _ => 1 : Fin 2 → ℕ) i := fun _ => one_pos
  have hL : L₀ (0 : Fin 2 → ℕ) ≤ 1 := by simp [L₀]
  have hQ : Qamb (fun _ => 1 : Fin 2 → ℕ) = 2 := by simp [Qamb]
  have hlat : (1 / 2 : ℝ) ∈ latticeBelow (Qamb (fun _ => 1 : Fin 2 → ℕ)) ((1 : ℕ) : ℝ) := by
    rw [hQ]
    have := mem_latticeBelow (Q := 2) two_pos (L := ((1 : ℕ) : ℝ)) (m := 1) (by norm_num)
    simpa using this
  have h := ofReal_empCoeff_eq_couplingPolarCoeff (η := fun _ => (1 : ℝ)) (ζ := fun _ => a)
    contDiff_const contDiff_const hk hL hlat
    (by norm_num) (by norm_num) (q := 0) (by norm_num)
  rw [depthOf_xy_sq, (couplingPolarCoeff_xy_sq a).2] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  ring

/-- ★ **Consistency with the direct asymptotic** `tendsto_logExample`: the leading behaviour of
`∫∫ e^{−n x²y² + a√n xy}` is `n^{−½}(log n · c_{½,1} + c_{½,0})` with the coefficients of
`empCoeff_xy_sq_one`/`empCoeff_xy_sq_zero`. -/
theorem tendsto_logExample_empCoeff (a : ℝ) :
    Tendsto (fun n : ℝ => Real.sqrt n * logExample a n -
      (Real.log n * empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 1 +
        empCoeff (fun _ : Fin 2 → ℝ => (1 : ℝ)) (fun _ => a) 0 (fun _ => 1) (1 / 2) 0)) atTop
          (𝓝 0) := by
  rw [empCoeff_xy_sq_one, empCoeff_xy_sq_zero]
  have := (tendsto_logExample a).const_mul (1 / 4 : ℝ)
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  ring

end Example

end Grammar
