/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TieFormulaPolynomial
import Grammar.StateDensityPolar

/-!
# The tie formula for smooth amplitudes on the blow-up chart

The unequal-wall tie formula of `Grammar.TieFormulaPolynomial` (chart `h = (1,0)`, `k = (2,1)`,
tie of order two at `½`) extended from polynomial to smooth amplitudes given in the wall
decomposition

  `η(u, v) = a + u g₁(u) + v g₂(v) + u v ρ(u, v)`  (`tieAmp`),

`g₁, g₂ : ℝ → ℝ` and `ρ : ℝ² → ℝ` smooth (examples_slop §4; Astra next-round target 2).  The chart
zeta functional splits into four pieces (`chartZeta_tieAmp`): the constant `a/((2−4s)(1−2s))`, the
two wall transforms `W₁(s)/(1−2s)` with `W₁(s) = ∫₀¹ g₁(u) u^{2−4s} du` and `W₂(s)/(2−4s)` with
`W₂(s) = ∫₀¹ g₂(v) v^{1−2s} dv` (`chartZeta_wallU/V`, Fubini on the box), and the mixed term, the
chart zeta functional of `ρ` on the shifted chart `h = (2,1)`, holomorphic near `½`.  The wall
transforms are holomorphic on `Re s < 3/4` and `Re s < 1` (`differentiableOn_wallU/V`, from
`hasDerivAt_mellinIoc`), and their values at `½` are the wall integrals `∫₀¹ g₁`, `∫₀¹ g₂`.  The
uniqueness of principal parts then gives (★★★ `chartPolarCoeff_tieAmp_half`):

  `C_{½,2}[η] = a/8 = η(0,0)/8`,   `C_{½,1}[η] = −½ ∫₀¹ g₁ − ¼ ∫₀¹ g₂`,

i.e. `A_{½,1}[η] = ½∫₀¹(η(u,0)−η(0,0))/u du + ¼∫₀¹(η(0,v)−η(0,0))/v dv` in the paper's convention:
the lower polar datum of an unequal-wall tie is the pair of wall finite parts weighted by
`1/(2kᵢ)`, for arbitrary smooth wall profiles.  The polar coefficients are taken at depth `p =
(1,1)`, whose flat strip `Re s < 3/4` is exactly the holomorphy domain of the wall transforms.
The decomposition is supplied as data; producing it from a general smooth `η` (Hadamard's lemma)
is not part of this module.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

/-- The shifted chart data of the mixed term `u v ρ`: `h = (2,1)`. -/
def tieHuv : Fin 2 → ℕ := ![2, 1]

/-- The decomposed amplitude `a + u g₁(u) + v g₂(v) + u v ρ(u, v)`. -/
noncomputable def tieAmp (a : ℝ) (g₁ g₂ : ℝ → ℝ) (ρ : (Fin 2 → ℝ) → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  a + u 0 * g₁ (u 0) + u 1 * g₂ (u 1) + u 0 * u 1 * ρ u

theorem contDiff_tieAmp (a : ℝ) {g₁ g₂ : ℝ → ℝ} (hg₁ : ContDiff ℝ ∞ g₁) (hg₂ : ContDiff ℝ ∞ g₂)
    {ρ : (Fin 2 → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (tieAmp a g₁ g₂ ρ) := by
  unfold tieAmp
  fun_prop

/-- The wall transform of the exceptional wall: `W₁(s) = ∫₀¹ g₁(u) u^{2−4s} du`. -/
noncomputable def wallU (g₁ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (g₁ t : ℂ) * (t : ℂ) ^ (2 - 4 * s)

/-- The wall transform of the strict transform: `W₂(s) = ∫₀¹ g₂(v) v^{1−2s} dv`. -/
noncomputable def wallV (g₂ : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (g₂ t : ℂ) * (t : ℂ) ^ (1 - 2 * s)

theorem tieH_zero : tieH 0 = 1 := rfl
theorem tieH_one : tieH 1 = 0 := rfl
theorem tieK_zero : tieK 0 = 2 := rfl
theorem tieK_one : tieK 1 = 1 := rfl
theorem tieHuv_zero : tieHuv 0 = 2 := rfl
theorem tieHuv_one : tieHuv 1 = 1 := rfl

/-- The chart weight on `(0,1]²`, written out: `u^{1−4s} v^{−2s}`. -/
theorem cpowWeight_tie (s : ℂ) {u : Fin 2 → ℝ} (hu : ∀ i, 0 < u i) :
    cpowWeight tieH tieK s u = (u 0 : ℂ) ^ (1 - 4 * s) * (u 1 : ℂ) ^ (-2 * s) := by
  rw [cpowWeight_eq_prod_cpow tieH tieK s hu, Fin.prod_univ_two, tieH_zero, tieH_one, tieK_zero,
    tieK_one]
  push_cast
  ring_nf

theorem cpowWeight_tieHuv (s : ℂ) {u : Fin 2 → ℝ} (hu : ∀ i, 0 < u i) :
    cpowWeight tieHuv tieK s u = (u 0 : ℂ) ^ (2 - 4 * s) * (u 1 : ℂ) ^ (1 - 2 * s) := by
  rw [cpowWeight_eq_prod_cpow tieHuv tieK s hu, Fin.prod_univ_two, tieHuv_zero, tieHuv_one,
    tieK_zero, tieK_one]
  push_cast
  ring_nf

theorem box_two_eq : SmoothEngine.box (Fin 2) 1 = Set.pi univ fun _ : Fin 2 => Ioc (0 : ℝ) 1 := rfl

/-- Fubini for a product integrand on the unit square. -/
theorem integral_box_two (f₀ f₁ : ℝ → ℂ) :
    ∫ u in SmoothEngine.box (Fin 2) 1, f₀ (u 0) * f₁ (u 1) =
      (∫ t in Ioc (0 : ℝ) 1, f₀ t) * ∫ t in Ioc (0 : ℝ) 1, f₁ t := by
  have hpt : ∀ u : Fin 2 → ℝ, f₀ (u 0) * f₁ (u 1) = ∏ i, (![f₀, f₁] i) (u i) := fun u => by
    rw [Fin.prod_univ_two]
    rfl
  simp_rw [hpt]
  rw [box_two_eq, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i (t : ℝ) => (![f₀, f₁] i) t), Fin.prod_univ_two]
  rfl

/-- The wall piece `u g₁(u)` on the chart: `W₁(s)/(1−2s)` on the strip `Re s < ½`. -/
theorem chartZeta_wallU (g₁ : ℝ → ℝ) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ u in SmoothEngine.box (Fin 2) 1, ((u 0 * g₁ (u 0) : ℝ) : ℂ) * cpowWeight tieH tieK s u =
      wallU g₁ s * (1 / (1 - 2 * s)) := by
  have hpt : ∀ u ∈ SmoothEngine.box (Fin 2) 1,
      ((u 0 * g₁ (u 0) : ℝ) : ℂ) * cpowWeight tieH tieK s u =
        ((g₁ (u 0) : ℂ) * (u 0 : ℂ) ^ (2 - 4 * s)) * (u 1 : ℂ) ^ (-2 * s) := by
    intro u hu
    have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
    rw [cpowWeight_tie s hu']
    have h0 : (u 0 : ℂ) ≠ 0 := by exact_mod_cast (hu' 0).ne'
    rw [show (2 - 4 * s : ℂ) = 1 + (1 - 4 * s) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
    push_cast
    ring
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) hpt,
    integral_box_two (fun t => (g₁ t : ℂ) * (t : ℂ) ^ (2 - 4 * s)) (fun t => (t : ℂ) ^ (-2 * s)),
    integral_Ioc_cpow (by simp; linarith)]
  unfold wallU
  congr 2
  ring

/-- The wall piece `v g₂(v)` on the chart: `W₂(s)/(2−4s)` on the strip `Re s < ½`. -/
theorem chartZeta_wallV (g₂ : ℝ → ℝ) {s : ℂ} (hs : s.re < 1 / 2) :
    ∫ u in SmoothEngine.box (Fin 2) 1, ((u 1 * g₂ (u 1) : ℝ) : ℂ) * cpowWeight tieH tieK s u =
      (1 / (2 - 4 * s)) * wallV g₂ s := by
  have hpt : ∀ u ∈ SmoothEngine.box (Fin 2) 1,
      ((u 1 * g₂ (u 1) : ℝ) : ℂ) * cpowWeight tieH tieK s u =
        (u 0 : ℂ) ^ (1 - 4 * s) * ((g₂ (u 1) : ℂ) * (u 1 : ℂ) ^ (1 - 2 * s)) := by
    intro u hu
    have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
    rw [cpowWeight_tie s hu']
    have h1 : (u 1 : ℂ) ≠ 0 := by exact_mod_cast (hu' 1).ne'
    rw [show (1 - 2 * s : ℂ) = 1 + (-2 * s) by ring, Complex.cpow_add _ _ h1, Complex.cpow_one]
    push_cast
    ring
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) hpt,
    integral_box_two (fun t => (t : ℂ) ^ (1 - 4 * s)) (fun t => (g₂ t : ℂ) * (t : ℂ) ^ (1 - 2 * s)),
    integral_Ioc_cpow (by simp; linarith)]
  unfold wallV
  congr 2
  ring

/-- The mixed piece `u v ρ` is the chart zeta functional of `ρ` on the shifted chart `(2,1)`. -/
theorem chartZeta_mixed (ρ : (Fin 2 → ℝ) → ℝ) (s : ℂ) :
    ∫ u in SmoothEngine.box (Fin 2) 1, ((u 0 * u 1 * ρ u : ℝ) : ℂ) * cpowWeight tieH tieK s u =
      chartZeta ρ tieHuv tieK s := by
  unfold chartZeta
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun u hu => ?_
  have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
  rw [cpowWeight_tie s hu', cpowWeight_tieHuv s hu']
  have h0 : (u 0 : ℂ) ≠ 0 := by exact_mod_cast (hu' 0).ne'
  have h1 : (u 1 : ℂ) ≠ 0 := by exact_mod_cast (hu' 1).ne'
  rw [show (2 - 4 * s : ℂ) = 1 + (1 - 4 * s) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one,
    show (1 - 2 * s : ℂ) = 1 + (-2 * s) by ring, Complex.cpow_add _ _ h1, Complex.cpow_one]
  push_cast
  ring

/-- The rational term of the constant: `a/((2−4s)(1−2s)) = a · monoTerm 0`. -/
theorem chartZeta_const (a : ℝ) {s : ℂ} (hs : ZetaStrip tieH tieK s) :
    ∫ u in SmoothEngine.box (Fin 2) 1, (a : ℂ) * cpowWeight tieH tieK s u =
      (a : ℂ) * monoTerm 0 s := by
  rw [integral_const_mul]
  have := chartZeta_mono 0 hs
  unfold chartZeta at this
  rw [← this]
  congr 1
  refine setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun u _ => ?_
  simp [mono]

theorem zetaStrip_tie_iff (s : ℂ) : ZetaStrip tieH tieK s ↔ s.re < 1 / 2 := by
  unfold ZetaStrip
  constructor
  · intro h
    have := h 0
    rw [tieH_zero, tieK_zero] at this
    push_cast at this
    linarith
  · intro h i
    fin_cases i <;> simp [tieH, tieK] <;> linarith

/-- ★★ **The chart zeta functional of the decomposed amplitude** on the strip `Re s < ½`:
`a·monoTerm 0 + W₁(s)/(1−2s) + W₂(s)/(2−4s) + ζ_ρ^{(2,1)}(s)`. -/
theorem chartZeta_tieAmp (a : ℝ) {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    {ρ : (Fin 2 → ℝ) → ℝ} (hρ : Continuous ρ) {s : ℂ} (hs : ZetaStrip tieH tieK s) :
    chartZeta (tieAmp a g₁ g₂ ρ) tieH tieK s =
      (a : ℂ) * monoTerm 0 s + wallU g₁ s * (1 / (1 - 2 * s)) +
        (1 / (2 - 4 * s)) * wallV g₂ s + chartZeta ρ tieHuv tieK s := by
  have hs' : s.re < 1 / 2 := (zetaStrip_tie_iff s).1 hs
  have hpt : ∀ u : Fin 2 → ℝ, (tieAmp a g₁ g₂ ρ u : ℂ) * cpowWeight tieH tieK s u =
      (a : ℂ) * cpowWeight tieH tieK s u +
        ((u 0 * g₁ (u 0) : ℝ) : ℂ) * cpowWeight tieH tieK s u +
        ((u 1 * g₂ (u 1) : ℝ) : ℂ) * cpowWeight tieH tieK s u +
        ((u 0 * u 1 * ρ u : ℝ) : ℂ) * cpowWeight tieH tieK s u := by
    intro u
    unfold tieAmp
    push_cast
    ring
  have hi : ∀ G : (Fin 2 → ℝ) → ℝ, Continuous G →
      IntegrableOn (fun u => (G u : ℂ) * cpowWeight tieH tieK s u) (SmoothEngine.box (Fin 2) 1) :=
    fun G hG => integrableOn_chartZeta_integrand hG tieH tieK hs
  have h1 := hi (fun _ => a) continuous_const
  have h2 := hi (fun u => u 0 * g₁ (u 0)) ((continuous_apply 0).mul (hg₁.comp (continuous_apply 0)))
  have h3 := hi (fun u => u 1 * g₂ (u 1)) ((continuous_apply 1).mul (hg₂.comp (continuous_apply 1)))
  have h4 := hi (fun u => u 0 * u 1 * ρ u)
    (((continuous_apply 0).mul (continuous_apply 1)).mul hρ)
  have h12 : IntegrableOn (fun u : Fin 2 → ℝ => (a : ℂ) * cpowWeight tieH tieK s u +
      ((u 0 * g₁ (u 0) : ℝ) : ℂ) * cpowWeight tieH tieK s u) (SmoothEngine.box (Fin 2) 1) :=
    h1.add h2
  have h123 : IntegrableOn (fun u : Fin 2 → ℝ => (a : ℂ) * cpowWeight tieH tieK s u +
      ((u 0 * g₁ (u 0) : ℝ) : ℂ) * cpowWeight tieH tieK s u +
      ((u 1 * g₂ (u 1) : ℝ) : ℂ) * cpowWeight tieH tieK s u) (SmoothEngine.box (Fin 2) 1) :=
    h12.add h3
  unfold chartZeta
  simp_rw [hpt]
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
    chartZeta_const a hs, chartZeta_wallU g₁ hs', chartZeta_wallV g₂ hs', chartZeta_mixed ρ s]
  rfl

/-! ### Holomorphy and the values at `½` of the wall transforms -/

theorem exists_bound_Icc {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  exact (Real.norm_eq_abs (g t) ▸ hM t ht).trans (le_max_left _ _)

/-- `W₁(s) = M[g₁ t²](2s)`: the wall transform as a Mellin integral. -/
theorem wallU_eq_mellinIoc (g₁ : ℝ → ℝ) (s : ℂ) :
    wallU g₁ s = mellinIoc (fun t => (g₁ t : ℂ) * (t : ℂ) ^ 2) (2 * s) := by
  unfold wallU mellinIoc
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have h0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  rw [mul_assoc, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ h0]
  congr 2
  push_cast
  ring

theorem wallV_eq_mellinIoc (g₂ : ℝ → ℝ) (s : ℂ) :
    wallV g₂ s = mellinIoc (fun t => (g₂ t : ℂ) * (t : ℂ)) s := by
  unfold wallV mellinIoc
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have h0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
  rw [mul_assoc]
  congr 1
  rw [show (1 - 2 * s : ℂ) = 1 + -2 * s by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]

/-- `W₁` is holomorphic on `Re s < 3/4`. -/
theorem differentiableOn_wallU {g₁ : ℝ → ℝ} (hg₁ : Continuous g₁) :
    DifferentiableOn ℂ (wallU g₁) {s : ℂ | s.re < 3 / 4} := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_Icc hg₁
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (g₁ t : ℂ) * (t : ℂ) ^ 2)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((Complex.continuous_ofReal.comp hg₁).mul
      (Complex.continuous_ofReal.pow 2)).aestronglyMeasurable
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(g₁ t : ℂ) * (t : ℂ) ^ 2‖ ≤ M * t ^ (2 : ℝ) := by
    intro t ht
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht.1, Real.rpow_two]
    exact mul_le_mul_of_nonneg_right (hM t ⟨ht.1.le, ht.2⟩) (by positivity)
  have hD := differentiableOn_mellinIoc hmeas hM0 hb
  have hcomp : DifferentiableOn ℂ
      (fun s : ℂ => mellinIoc (fun t => (g₁ t : ℂ) * (t : ℂ) ^ 2) (2 * s))
      {s : ℂ | s.re < 3 / 4} := by
    refine hD.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn fun s hs => ?_
    have hs' : s.re < 3 / 4 := hs
    change (2 * s).re < ((2 : ℝ) + 1) / 2
    rw [Complex.mul_re]
    simp
    linarith
  exact hcomp.congr fun s _ => wallU_eq_mellinIoc g₁ s

/-- `W₂` is holomorphic on `Re s < 1`. -/
theorem differentiableOn_wallV {g₂ : ℝ → ℝ} (hg₂ : Continuous g₂) :
    DifferentiableOn ℂ (wallV g₂) {s : ℂ | s.re < 1} := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_Icc hg₂
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (g₂ t : ℂ) * (t : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((Complex.continuous_ofReal.comp hg₂).mul Complex.continuous_ofReal).aestronglyMeasurable
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(g₂ t : ℂ) * (t : ℂ)‖ ≤ M * t ^ (1 : ℝ) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht.1, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (hM t ⟨ht.1.le, ht.2⟩) ht.1.le
  have hD := differentiableOn_mellinIoc hmeas hM0 hb
  rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num] at hD
  exact hD.congr fun s _ => wallV_eq_mellinIoc g₂ s

/-- `W₁(½) = ∫₀¹ g₁`. -/
theorem wallU_half (g₁ : ℝ → ℝ) :
    wallU g₁ ((1 / 2 : ℝ) : ℂ) = ((∫ t in (0 : ℝ)..1, g₁ t : ℝ) : ℂ) := by
  unfold wallU
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [show (2 - 4 * ((1 / 2 : ℝ) : ℂ) : ℂ) = 0 by push_cast; ring, Complex.cpow_zero, mul_one]

/-- `W₂(½) = ∫₀¹ g₂`. -/
theorem wallV_half (g₂ : ℝ → ℝ) :
    wallV g₂ ((1 / 2 : ℝ) : ℂ) = ((∫ t in (0 : ℝ)..1, g₂ t : ℝ) : ℂ) := by
  unfold wallV
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [show (1 - 2 * ((1 / 2 : ℝ) : ℂ) : ℂ) = 0 by push_cast; ring, Complex.cpow_zero, mul_one]

/-- A function differentiable at `½` divided by `1 − 2s`: the principal part is
`−(W(½)/2)/(s − ½)` and the rest is bounded. -/
theorem div_one_sub_sub_polar_isBigO {W : ℂ → ℂ} (hW : DifferentiableAt ℂ W ((1 / 2 : ℝ) : ℂ)) :
    (fun s => W s * (1 / (1 - 2 * s)) - polarPart 0 (fun _ => -(W ((1 / 2 : ℝ) : ℂ)) / 2)
      ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 hW.hasDerivAt
  have hO := (hslope.const_mul (-(1 / 2 : ℂ))).isBigO_one (F := ℂ)
  refine hO.congr' ?_ EventuallyEq.rfl
  refine eventually_nhdsWithin_of_forall fun s hs => ?_
  have hs' : s ≠ 1 / 2 := by
    intro h; apply hs; rw [h]; push_cast; rfl
  beta_reduce
  rw [polarPart_zero_apply, slope_def_field]
  push_cast
  rw [one_div_one_sub hs']
  have h1 : s - 1 / 2 ≠ 0 := sub_ne_zero.2 hs'
  field_simp
  ring

/-- The `(2 − 4s)` variant: principal part `−(W(½)/4)/(s − ½)`. -/
theorem div_two_sub_sub_polar_isBigO {W : ℂ → ℂ} (hW : DifferentiableAt ℂ W ((1 / 2 : ℝ) : ℂ)) :
    (fun s => (1 / (2 - 4 * s)) * W s - polarPart 0 (fun _ => -(W ((1 / 2 : ℝ) : ℂ)) / 4)
      ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
  have h := div_one_sub_sub_polar_isBigO hW
  refine (h.const_mul_left (1 / 2 : ℂ)).congr_left fun s => ?_
  rw [polarPart_zero_apply, polarPart_zero_apply]
  have e : (1 / (2 - 4 * s) : ℂ) = (1 / 2) * (1 / (1 - 2 * s)) := by
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring
  rw [e]
  ring

/-! ### The tie formula -/

/-- The polar data of the decomposed amplitude at `½`. -/
noncomputable def tieSmoothA (a : ℝ) (g₁ g₂ : ℝ → ℝ) : ℕ → ℂ := fun q =>
  if q = 1 then (a : ℂ) / 8
  else if q = 0 then
    -((∫ t in (0 : ℝ)..1, g₁ t : ℝ) : ℂ) / 2 - ((∫ t in (0 : ℝ)..1, g₂ t : ℝ) : ℂ) / 4
  else 0

theorem flatStrip_tie_half : FlatStrip ![1, 1] tieH tieK ((1 / 2 : ℝ) : ℂ) := by
  intro i
  fin_cases i <;> norm_num [tieH, tieK]

theorem re_lt_of_flatEdge {s : ℂ} (hs : s.re < flatEdge ![1, 1] tieH tieK) : s.re < 3 / 4 := by
  have h := ((flatStrip_iff_re_lt ![1, 1] tieH tieK tieK_pos s).2 hs) 0
  simp [tieH, tieK] at h
  linarith

/-- The tie formula with the minimal hypotheses: `η = tieAmp a g₁ g₂ ρ` smooth and the wall
profiles `g₁, g₂, ρ` merely continuous (the proof uses only their continuity). -/
theorem chartPolarCoeff_tieAmp_half' (a : ℝ) {g₁ g₂ : ℝ → ℝ} {ρ : (Fin 2 → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ (tieAmp a g₁ g₂ ρ)) (hg₁c : Continuous g₁) (hg₂c : Continuous g₂)
    (hρc : Continuous ρ) :
    ∀ q ≤ 1, chartPolarCoeff ![1, 1] (tieAmp a g₁ g₂ ρ) tieH tieK (1 / 2) q =
      tieSmoothA a g₁ g₂ q := by
  have hp0 : ∀ i, 0 < (![1, 1] : Fin 2 → ℕ) i := fun i => by fin_cases i <;> simp
  -- the explicit continuation
  set g : ℂ → ℂ := fun s => (a : ℂ) * monoTerm 0 s + wallU g₁ s * (1 / (1 - 2 * s)) +
    (1 / (2 - 4 * s)) * wallV g₂ s + chartZeta ρ tieHuv tieK s with hgdef
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
  have hUV : DifferentiableOn ℂ (chartZeta ρ tieHuv tieK) {s : ℂ | s.re < 3 / 4} := by
    refine (differentiableOn_chartZeta hρc tieHuv tieK).mono fun s hs => ?_
    intro i
    fin_cases i <;> simp [tieHuv, tieK] <;> linarith [show s.re < 3 / 4 from hs]
  have hg : DifferentiableOn ℂ g
      ({s : ℂ | -1 < s.re ∧ s.re < flatEdge ![1, 1] tieH tieK} \ {((1 / 2 : ℝ) : ℂ)}) := by
    intro s hs
    have hs34 : s.re < 3 / 4 := re_lt_of_flatEdge hs.1.2
    have hsne : s ≠ 1 / 2 := by
      intro h; apply hs.2; rw [h, hhalf]; rfl
    have h1 : (1 - 2 * s : ℂ) ≠ 0 := by
      intro h; apply hsne; linear_combination -h / 2
    have h2 : (2 - 4 * s : ℂ) ≠ 0 := by
      intro h; apply hsne; linear_combination -h / 4
    have hmono : DifferentiableAt ℂ (fun s => (a : ℂ) * monoTerm 0 s) s := by
      unfold monoTerm
      simp only [Pi.zero_apply, Nat.cast_zero, zero_add]
      refine (differentiableAt_const _).mul ((differentiableAt_const _).div ?_ (mul_ne_zero h2 h1))
      fun_prop
    have hU : DifferentiableAt ℂ (wallU g₁) s :=
      (differentiableOn_wallU hg₁c).differentiableAt ((isOpen_re_lt _).mem_nhds hs34)
    have hV : DifferentiableAt ℂ (wallV g₂) s :=
      (differentiableOn_wallV hg₂c).differentiableAt ((isOpen_re_lt _).mem_nhds
        (by change s.re < 1; linarith))
    have hR : DifferentiableAt ℂ (chartZeta ρ tieHuv tieK) s :=
      hUV.differentiableAt ((isOpen_re_lt _).mem_nhds hs34)
    have hd1 : DifferentiableAt ℂ (fun s : ℂ => 1 / (1 - 2 * s)) s :=
      (differentiableAt_const _).div (by fun_prop) h1
    have hd2 : DifferentiableAt ℂ (fun s : ℂ => 1 / (2 - 4 * s)) s :=
      (differentiableAt_const _).div (by fun_prop) h2
    exact (((hmono.add (hU.mul hd1)).add (hd2.mul hV)).add hR).differentiableWithinAt
  have hseed : ∀ s : ℂ, ZetaStrip tieH tieK s → s ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) →
      chartZeta (tieAmp a g₁ g₂ ρ) tieH tieK s = g s :=
    fun s hs _ => chartZeta_tieAmp a hg₁c hg₂c hρc hs
  have hseed' : ((-1 / 2 : ℝ) : ℂ) ∉ ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) := by
    simp only [mem_singleton_iff, Complex.ofReal_inj]
    norm_num
  have hev := chartZetaAtDepth_eventuallyEq_of_eqOn_strip ![1, 1] hF tieH tieK tieK_pos hp0
    (Set.finite_singleton _) hg hseed hseed' flatStrip_tie_half (by norm_num)
  -- the principal part
  have hmemhalf : ((1 / 2 : ℝ) : ℂ) ∈ {s : ℂ | s.re < 3 / 4} := by
    change ((1 / 2 : ℝ) : ℂ).re < 3 / 4
    norm_num
  have hmemhalf' : ((1 / 2 : ℝ) : ℂ) ∈ {s : ℂ | s.re < 1} := by
    change ((1 / 2 : ℝ) : ℂ).re < 1
    norm_num
  have hU : DifferentiableAt ℂ (wallU g₁) ((1 / 2 : ℝ) : ℂ) :=
    (differentiableOn_wallU hg₁c).differentiableAt ((isOpen_re_lt _).mem_nhds hmemhalf)
  have hV : DifferentiableAt ℂ (wallV g₂) ((1 / 2 : ℝ) : ℂ) :=
    (differentiableOn_wallV hg₂c).differentiableAt ((isOpen_re_lt _).mem_nhds hmemhalf')
  have hRc : ContinuousAt (chartZeta ρ tieHuv tieK) ((1 / 2 : ℝ) : ℂ) :=
    (hUV.differentiableAt ((isOpen_re_lt _).mem_nhds hmemhalf)).continuousAt
  have hO1 := monoTerm_sub_polarPart_isBigO 0 a
  have hO2 := div_one_sub_sub_polar_isBigO hU
  have hO3 := div_two_sub_sub_polar_isBigO hV
  have hO4 : (chartZeta ρ tieHuv tieK) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) :=
    (hRc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one (F := ℂ)
  have ha : (fun s => g s - polarPart 1 (tieSmoothA a g₁ g₂) ((1 / 2 : ℝ) : ℂ) s)
      =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
    refine (((hO1.add hO2).add hO3).add hO4).congr_left fun s => ?_
    simp only [hgdef, polarPart_one_apply, polarPart_zero_apply, tieSmoothA,
      monoA, wallU_half, wallV_half]
    simp
    ring
  exact chartPolarCoeff_eq_of_eventuallyEq ![1, 1] hF tieH tieK hp0 flatStrip_tie_half
    (fun x _ => poleOrder_le _ _ x.1 x.2 _) hev ha

/-- ★★★ **The tie formula for smooth amplitudes in the wall decomposition**: for
`η = a + u g₁(u) + v g₂(v) + u v ρ(u,v)` with `g₁, g₂, ρ` smooth, on the chart `h = (1,0)`,
`k = (2,1)`, `C_{½,2}[η] = a/8` and `C_{½,1}[η] = −½ ∫₀¹ g₁ − ¼ ∫₀¹ g₂`. -/
theorem chartPolarCoeff_tieAmp_half (a : ℝ) {g₁ g₂ : ℝ → ℝ} (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) {ρ : (Fin 2 → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ∀ q ≤ 1, chartPolarCoeff ![1, 1] (tieAmp a g₁ g₂ ρ) tieH tieK (1 / 2) q =
      tieSmoothA a g₁ g₂ q :=
  chartPolarCoeff_tieAmp_half' a (contDiff_tieAmp a hg₁ hg₂ hρ) hg₁.continuous hg₂.continuous
    hρ.continuous

end Grammar
