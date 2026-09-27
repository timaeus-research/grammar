/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RealDigammaSeries

/-!
# The ζ-bridge: `ψ_j = (−1)^{j+1} ζ(j+1)`

The complex series `S(z) = Σ_{n≥0} z/((n+1)(n+1+z))` is analytic on the half-ball `‖z‖ < ½`
(majorant `1/(n+1)²`, `differentiableOn_tsum_of_summable_norm`), agrees with
`ψ(1+z) − ψ(1)` on the real points `1/(m+3) → 0` (the real series of `RealDigammaSeries` and the
reality of `ψ` on `(0,∞)`, `digamma_ofReal`), hence near `0` by the principle of isolated zeros
(`digammaSeries_eventuallyEq`).  Termwise differentiation at every order
(`hasSum_deriv_of_summable_norm` iterated, `hasSum_iteratedDeriv_digammaSeries`) with
`(d/dz)^j z/((n+1)(n+1+z)) = (−1)^{j+1} j!/(n+1+z)^{j+1}` for `j ≥ 1` gives

  ★★★ `hasSum_psiOneCoeff : Σ_{n≥0} (−1)^{j+1}/(n+1)^{j+1} = ψ_j`,
  ★★★ `psiOneCoeff_eq_zeta : ψ_j = (−1)^{j+1} ζ(j+1)`  (`j ≥ 1`, Mathlib's `riemannZeta`),

so `λ₃ = −2ζ(3)`, `λ₄ = 6ζ(4) = π⁴/15`, `λ₅ = −24ζ(5)` (`gammaLogThirdOne_eq_zeta`,
`gammaLogFourthOne_eq`, `gammaLogFifthOne_eq_zeta`): every coefficient of every `P_L` and every
residual mass of the Gaussian deep linear network is now a polynomial in `log 2`, `γ`, `π²` and
the odd ζ-values, with no symbols left.  Astra round 28, route B, modules 3–4.
Zero `sorry`/`axiom`.
-/

open Filter Topology Finset

namespace Grammar

/-! ### The series and the half-ball -/

/-- The summand `z/((n+1)(n+1+z))`. -/
noncomputable def dsTerm (n : ℕ) (z : ℂ) : ℂ := z / (((n : ℂ) + 1) * ((n : ℂ) + 1 + z))

/-- `S(z) = Σ_{n≥0} z/((n+1)(n+1+z))`. -/
noncomputable def digammaSeries (z : ℂ) : ℂ := ∑' n : ℕ, dsTerm n z

/-- The half-ball `‖z‖ < ½`. -/
def halfBall : Set ℂ := Metric.ball 0 (1 / 2)

theorem isOpen_halfBall : IsOpen halfBall := Metric.isOpen_ball

theorem zero_mem_halfBall : (0 : ℂ) ∈ halfBall := by simp [halfBall]

theorem norm_lt_half_of_mem_halfBall {z : ℂ} (hz : z ∈ halfBall) : ‖z‖ < 1 / 2 := by
  simpa [halfBall] using hz

theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast
  ring

theorem half_le_norm_add {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + 1 + z‖ := by
  have hz' := norm_lt_half_of_mem_halfBall hz
  have h := norm_le_add_norm_add ((n : ℂ) + 1) z
  rw [norm_natCast_add_one] at h
  linarith

theorem add_ne_zero_of_mem_halfBall {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    (n : ℂ) + 1 + z ≠ 0 := by
  have h := half_le_norm_add hz n
  have : (0 : ℝ) < ‖(n : ℂ) + 1 + z‖ := by
    have : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
    linarith
  exact norm_pos_iff.1 this

theorem natCast_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

theorem summable_inv_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
  refine this.congr fun n => ?_
  push_cast
  ring

theorem norm_dsTerm_le {z : ℂ} (hz : z ∈ halfBall) (n : ℕ) :
    ‖dsTerm n z‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold dsTerm
  rw [norm_div, norm_mul, norm_natCast_add_one]
  have hz' : ‖z‖ ≤ 1 / 2 := (norm_lt_half_of_mem_halfBall hz).le
  have hA := half_le_norm_add hz n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ‖(n : ℂ) + 1 + z‖ := by
    have : (0 : ℝ) < ‖(n : ℂ) + 1 + z‖ := by linarith
    positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith [norm_nonneg z]

theorem differentiableOn_dsTerm (n : ℕ) : DifferentiableOn ℂ (dsTerm n) halfBall := by
  unfold dsTerm
  refine DifferentiableOn.div differentiableOn_id
    ((differentiableOn_const _).mul ((differentiableOn_const _).add differentiableOn_id))
    fun z hz => ?_
  exact mul_ne_zero (natCast_add_one_ne_zero n) (add_ne_zero_of_mem_halfBall hz n)

/-- `S` is analytic on the half-ball. -/
theorem analyticOnNhd_digammaSeries : AnalyticOnNhd ℂ digammaSeries halfBall :=
  (Complex.differentiableOn_tsum_of_summable_norm summable_inv_sq differentiableOn_dsTerm
    isOpen_halfBall fun n _ hz => norm_dsTerm_le hz n).analyticOnNhd isOpen_halfBall

/-! ### Reality of `ψ` on the positive axis and the series on real points -/

theorem deriv_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = (((deriv Complex.Gamma (x : ℂ)).re : ℝ) : ℂ) := by
  have h1 := (hasDerivAt_Gamma_of_re_pos (z := (x : ℂ)) (by simpa using hx)).comp_ofReal
  have h2 := (hasDerivAt_realGamma hx).ofReal_comp
  have hfun : (fun y : ℝ => Complex.Gamma (y : ℂ)) = fun y => ((Real.Gamma y : ℝ) : ℂ) := by
    funext y
    rw [Complex.Gamma_ofReal]
  rw [hfun] at h1
  exact h1.unique h2

/-- `ψ` is real on `(0,∞)`. -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((realDigamma x : ℝ) : ℂ) := by
  rw [realDigamma_eq_div, Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx,
    Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_re]

theorem digammaSeries_ofReal {x : ℝ} (hx0 : -1 < x) (hx1 : x ≤ 1) :
    digammaSeries (x : ℂ) = Complex.digamma (1 + (x : ℂ)) - Complex.digamma 1 := by
  have h := Complex.hasSum_ofReal.2 (hasSum_realDigamma_sub hx0 hx1)
  have e : (fun n : ℕ => ((x / (((n : ℝ) + 1) * ((n : ℝ) + 1 + x)) : ℝ) : ℂ)) =
      fun n => dsTerm n (x : ℂ) := by
    funext n
    unfold dsTerm
    push_cast
    ring
  rw [e] at h
  unfold digammaSeries
  rw [h.tsum_eq, show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; ring,
    digamma_ofReal (by linarith), show (1 : ℂ) = ((1 : ℝ) : ℂ) by simp, digamma_ofReal one_pos]
  push_cast
  ring

theorem analyticAt_digamma_one_add :
    AnalyticAt ℂ (fun z : ℂ => Complex.digamma (1 + z) - Complex.digamma 1) 0 := by
  have := (analyticAt_gammaLogDeriv (z := 1) (by norm_num)).comp_of_eq
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0) (by norm_num)
  rw [gammaLogDeriv_eq_digamma] at this
  exact this.sub analyticAt_const

/-- ★★ `S(z) = ψ(1+z) − ψ(1)` near `0` (isolated zeros on the real points `1/(m+3)`). -/
theorem digammaSeries_eventuallyEq :
    digammaSeries =ᶠ[𝓝 (0 : ℂ)] fun z => Complex.digamma (1 + z) - Complex.digamma 1 := by
  have hS : AnalyticAt ℂ digammaSeries 0 := analyticOnNhd_digammaSeries 0 zero_mem_halfBall
  refine (hS.frequently_eq_iff_eventually_eq analyticAt_digamma_one_add).1 ?_
  have hreal : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 3)) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3)
    refine this.congr fun m => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hseq : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 3) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp hreal
      rw [Complex.ofReal_zero] at this
      exact this
    · refine Eventually.of_forall fun m => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  refine hseq.frequently (Frequently.of_forall fun m => ?_)
  have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 3) := by positivity
  have hm1 : 1 / ((m : ℝ) + 3) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact digammaSeries_ofReal (by linarith) hm1

/-! ### Termwise iterated derivatives -/

theorem analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- `(d/dw)^j (c + w)⁻¹ = (−1)^j j! (c+w)^{−(j+1)}` where `c + z ≠ 0`. -/
theorem iteratedDeriv_inv_const_add (c : ℂ) (j : ℕ) :
    ∀ {z : ℂ}, c + z ≠ 0 →
      iteratedDeriv j (fun w : ℂ => (c + w)⁻¹) z =
        (-1) ^ j * (j.factorial : ℂ) * ((c + z) ^ (j + 1))⁻¹ := by
  induction j with
  | zero =>
    intro z _
    simp [iteratedDeriv_zero]
  | succ j ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {w : ℂ | c + w ≠ 0} :=
      isOpen_ne.preimage (continuous_const.add continuous_id)
    have hev : iteratedDeriv j (fun w : ℂ => (c + w)⁻¹) =ᶠ[𝓝 z]
        fun w => (-1) ^ j * (j.factorial : ℂ) * ((c + w) ^ (j + 1))⁻¹ := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun w : ℂ => (-1) ^ j * (j.factorial : ℂ) * ((c + w) ^ (j + 1))⁻¹)
        ((-1) ^ j * (j.factorial : ℂ) *
          (-(((j + 1 : ℕ) : ℂ) * (c + z) ^ (j + 1 - 1) * 1) / ((c + z) ^ (j + 1)) ^ 2)) z :=
      ((((hasDerivAt_id z).const_add c).pow (j + 1)).inv (pow_ne_zero _ hz)).const_mul _
    rw [hd.deriv, Nat.add_sub_cancel, Nat.factorial_succ]
    have hcz : c + z ≠ 0 := hz
    push_cast
    field_simp
    ring

theorem dsTerm_eq (n : ℕ) {z : ℂ} (hz : (n : ℂ) + 1 + z ≠ 0) :
    dsTerm n z = ((n : ℂ) + 1)⁻¹ + (-1) * ((n : ℂ) + 1 + z)⁻¹ := by
  unfold dsTerm
  have := natCast_add_one_ne_zero n
  field_simp
  ring

/-- `(d/dz)^j` of the summand for `j ≥ 1`: `(−1)^{j+1} j!/(n+1+z)^{j+1}`. -/
theorem iteratedDeriv_dsTerm (n j : ℕ) (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ halfBall) :
    iteratedDeriv j (dsTerm n) z =
      (-1) ^ (j + 1) * (j.factorial : ℂ) * (((n : ℂ) + 1 + z) ^ (j + 1))⁻¹ := by
  have hev : dsTerm n =ᶠ[𝓝 z] fun w => ((n : ℂ) + 1)⁻¹ + (-1) * ((n : ℂ) + 1 + w)⁻¹ := by
    filter_upwards [isOpen_halfBall.mem_nhds hz] with w hw
    exact dsTerm_eq n (add_ne_zero_of_mem_halfBall hw n)
  rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
    iteratedDeriv_inv_const_add ((n : ℂ) + 1) j (add_ne_zero_of_mem_halfBall hz n)]
  ring

theorem norm_iteratedDeriv_dsTerm_le (n j : ℕ) (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ halfBall) :
    ‖iteratedDeriv j (dsTerm n) z‖ ≤ (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ 2 := by
  rw [iteratedDeriv_dsTerm n j hj hz, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hA := half_le_norm_add hz n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < ‖(n : ℂ) + 1 + z‖ := by linarith
  have h1 : (((n : ℝ) + 1) / 2) ^ (j + 1) ≤ ‖(n : ℂ) + 1 + z‖ ^ (j + 1) :=
    pow_le_pow_left₀ (by positivity) hA _
  have h2 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (j + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hf : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  rw [div_pow] at h1
  calc (j.factorial : ℝ) * (‖(n : ℂ) + 1 + z‖ ^ (j + 1))⁻¹
      ≤ (j.factorial : ℝ) * ((((n : ℝ) + 1) ^ (j + 1) / 2 ^ (j + 1)))⁻¹ := by
        gcongr
    _ = (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ (j + 1) := by
        field_simp
    _ ≤ (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ 2 := by
        gcongr

theorem differentiableOn_iteratedDeriv_dsTerm (n j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j (dsTerm n)) halfBall := fun z hz =>
  (analyticAt_iteratedDeriv ((differentiableOn_dsTerm n).analyticOnNhd isOpen_halfBall z hz)
    j).differentiableAt.differentiableWithinAt

theorem summable_bound (j : ℕ) :
    Summable (fun n : ℕ => (j.factorial : ℝ) * 2 ^ (j + 1) / ((n : ℝ) + 1) ^ 2) := by
  refine (summable_inv_sq.mul_left ((j.factorial : ℝ) * 2 ^ (j + 1))).congr fun n => ?_
  ring

/-- ★★ Termwise differentiation of `S` at every order `j ≥ 1` on the half-ball. -/
theorem hasSum_iteratedDeriv_digammaSeries (j : ℕ) (hj : 1 ≤ j) :
    ∀ {z : ℂ}, z ∈ halfBall →
      HasSum (fun n : ℕ => iteratedDeriv j (dsTerm n) z) (iteratedDeriv j digammaSeries z) := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro z hz
    simp only [iteratedDeriv_one]
    exact Complex.hasSum_deriv_of_summable_norm summable_inv_sq differentiableOn_dsTerm
      isOpen_halfBall (fun n w hw => norm_dsTerm_le hw n) hz
  | succ j hj ih =>
    intro z hz
    simp only [iteratedDeriv_succ]
    have hev : iteratedDeriv j digammaSeries =ᶠ[𝓝 z]
        fun w => ∑' n : ℕ, iteratedDeriv j (dsTerm n) w := by
      filter_upwards [isOpen_halfBall.mem_nhds hz] with w hw
      exact (ih hw).tsum_eq.symm
    rw [hev.deriv_eq]
    exact Complex.hasSum_deriv_of_summable_norm (summable_bound j)
      (fun n => differentiableOn_iteratedDeriv_dsTerm n j) isOpen_halfBall
      (fun n w hw => norm_iteratedDeriv_dsTerm_le n j hj hw) hz

/-! ### The ζ-bridge -/

/-- ★★★ **`Σ_{n≥0} (−1)^{j+1}/(n+1)^{j+1} = ψ_j`** for `j ≥ 1`. -/
theorem hasSum_psiOneCoeff (j : ℕ) (hj : 1 ≤ j) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ (j + 1) / ((n : ℂ) + 1) ^ (j + 1)) (psiOneCoeff j) := by
  have h := hasSum_iteratedDeriv_digammaSeries j hj zero_mem_halfBall
  have e1 : iteratedDeriv j digammaSeries 0 = (j.factorial : ℂ) * psiOneCoeff j := by
    rw [digammaSeries_eventuallyEq.iteratedDeriv_eq j]
    have e : (fun z : ℂ => Complex.digamma (1 + z) - Complex.digamma 1) =
        fun z => (-Complex.digamma 1) + Complex.digamma (1 + z) := by
      funext z
      ring
    rw [e, iteratedDeriv_const_add (by omega), iteratedDeriv_comp_const_add' Complex.digamma 1 j]
    simp only [add_zero]
    unfold psiOneCoeff taylorCoeff
    rw [gammaLogDeriv_eq_digamma]
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    field_simp
  have h2 := h.div_const (j.factorial : ℂ)
  rw [e1, mul_div_cancel_left₀ _ (by exact_mod_cast (Nat.factorial_pos j).ne')] at h2
  have e2 : (fun n : ℕ => iteratedDeriv j (dsTerm n) 0 / (j.factorial : ℂ)) =
      fun n : ℕ => (-1 : ℂ) ^ (j + 1) / ((n : ℂ) + 1) ^ (j + 1) := by
    funext n
    rw [iteratedDeriv_dsTerm n j hj zero_mem_halfBall, add_zero]
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    field_simp
  rwa [e2] at h2

/-- ★★★ **The ζ-bridge**: `ψ_j = (−1)^{j+1} ζ(j+1)` for `j ≥ 1`. -/
theorem psiOneCoeff_eq_zeta (j : ℕ) (hj : 1 ≤ j) :
    psiOneCoeff j = (-1 : ℂ) ^ (j + 1) * riemannZeta ((j : ℂ) + 1) := by
  have hre : 1 < ((j : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    exact_mod_cast Nat.lt_add_of_pos_left hj
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, ← (hasSum_psiOneCoeff j hj).tsum_eq,
    ← tsum_mul_left]
  congr 1
  funext n
  rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
  ring

theorem psiOneCoeff_two_eq_zeta : psiOneCoeff 2 = -riemannZeta 3 := by
  rw [psiOneCoeff_eq_zeta 2 (by norm_num)]
  norm_num

theorem psiOneCoeff_three_eq_zeta : psiOneCoeff 3 = riemannZeta 4 := by
  rw [psiOneCoeff_eq_zeta 3 (by norm_num)]
  norm_num

theorem psiOneCoeff_four_eq_zeta : psiOneCoeff 4 = -riemannZeta 5 := by
  rw [psiOneCoeff_eq_zeta 4 (by norm_num)]
  norm_num

/-- `λ₃ = −2ζ(3)`. -/
theorem gammaLogThirdOne_eq_zeta : gammaLogThirdOne = -2 * (riemannZeta 3).re := by
  have h := psiOneCoeff_two
  rw [psiOneCoeff_two_eq_zeta] at h
  have h' := congrArg Complex.re h
  rw [Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re] at h'
  linarith

/-- `λ₄ = 6ζ(4)`. -/
theorem gammaLogFourthOne_eq_zeta : gammaLogFourthOne = 6 * (riemannZeta 4).re := by
  have h := psiOneCoeff_three_eq
  rw [psiOneCoeff_three_eq_zeta] at h
  have h' := congrArg Complex.re h
  rw [Complex.ofReal_re] at h'
  linarith

/-- `λ₅ = −24ζ(5)`. -/
theorem gammaLogFifthOne_eq_zeta : gammaLogFifthOne = -24 * (riemannZeta 5).re := by
  have h := psiOneCoeff_four_eq
  rw [psiOneCoeff_four_eq_zeta] at h
  have h' := congrArg Complex.re h
  rw [Complex.neg_re, Complex.ofReal_re] at h'
  linarith

end Grammar
