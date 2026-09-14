/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StandardIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The one-dimensional smooth expansion (consult #114/#116, first milestone)

For a smooth amplitude `F` on `[0,b]`, a Jacobian exponent `h` and the phase `N β v^{2k}`,
`∫_0^b F(v) v^h e^{−Nβ v^{2k}} dv = ∑_{m<p} F^{(m)}(0)/m! · Γ(λ_m)/(2k β^{λ_m}) · N^{−λ_m}`
`+ O(N^{−L})`,
`λ_m = (m+h+1)/(2k)`, for every natural cutoff `L` and Taylor depth `p` with `2kL ≤ p + h`
(★ `oneDim_smooth`). Ingredients, all reusable in the multivariate engine: the half-line monomial
integral through the fluctuation function (`integral_pow_mul_exp_Ioi`), its exponentially small
tail beyond `b` (`tail_le`), the elementary bound `e^{−x} ≤ max(1, L!) x^{−L}` (`exp_neg_le`),
the fully flat remainder bound (`flat_bound`: no logarithmic loss), and Taylor's theorem along the
line. The coefficients are the exact monomial coefficients of the analytic engine on the line
(compare `OneDim.expansionCoefficient_oneDim` for `k = 1`); in one variable there are no faces and
no logarithms — the face structure begins at `d = 2` (`SmoothFaceRegression`). Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Elementary bounds -/

/-- `e^{−x} ≤ max(1, L!) · x^{−L}` for `x > 0`, in the form `x^L e^{−x} ≤ max 1 L!`. -/
theorem pow_mul_exp_neg_le (L : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ L * exp (-x) ≤ max 1 (L.factorial : ℝ) := by
  rcases le_or_gt x 1 with h1 | h1
  · calc x ^ L * exp (-x) ≤ 1 * 1 := by
          refine mul_le_mul (pow_le_one₀ hx.le h1) ?_ (exp_pos _).le zero_le_one
          exact exp_le_one_iff.2 (by linarith)
      _ = 1 := one_mul 1
      _ ≤ _ := le_max_left _ _
  · have h := Real.pow_div_factorial_le_exp x hx.le L
    have hf : (0 : ℝ) < L.factorial := by exact_mod_cast L.factorial_pos
    calc x ^ L * exp (-x) = x ^ L / exp x := by rw [exp_neg, div_eq_mul_inv]
      _ ≤ (L.factorial : ℝ) := by
          rw [div_le_iff₀ (exp_pos _)]
          have := (div_le_iff₀ hf).1 h
          linarith
      _ ≤ _ := le_max_right _ _

/-- `e^{−cN} ≤ (L!/c^L) N^{−L}` for `c > 0`, `N > 0`. -/
theorem exp_neg_mul_le (L : ℕ) {c N : ℝ} (hc : 0 < c) (hN : 0 < N) :
    exp (-(c * N)) ≤ (L.factorial : ℝ) / c ^ L / N ^ L := by
  have h := Real.pow_div_factorial_le_exp (c * N) (mul_pos hc hN).le L
  have hf : (0 : ℝ) < L.factorial := by exact_mod_cast L.factorial_pos
  rw [exp_neg]
  calc (exp (c * N))⁻¹ ≤ ((c * N) ^ L / (L.factorial : ℝ))⁻¹ := inv_anti₀ (by positivity) h
    _ = (L.factorial : ℝ) / c ^ L / N ^ L := by rw [inv_div, mul_pow]; ring

/-! ### The half-line monomial integral and its tail -/

variable {β : ℝ} (hβ : 0 < β) {k : ℕ} (hk : 0 < k)

/-- The exponent `λ_e = (e+1)/(2k)`. -/
noncomputable def lam (k e : ℕ) : ℝ := ((e : ℝ) + 1) / (2 * k)

include hk in
theorem lam_pos (e : ℕ) : 0 < lam k e := by
  unfold lam
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

include hβ hk in
/-- The half-line monomial integral:
`∫_0^∞ v^e e^{−Nβ v^{2k}} dv = Γ(λ_e)/(2k β^{λ_e}) N^{−λ_e}`. -/
theorem integral_pow_mul_exp_Ioi (e : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ v in Ioi (0 : ℝ), v ^ e * exp (-(N * β) * v ^ (2 * k)) =
      Gamma (lam k e) / (2 * k * β ^ lam k e) * N ^ (-lam k e) := by
  have h := standardIntegral1D_eq_fluctuation β N 0 e k hN hk
  have hint : ∀ u : ℝ, u ^ e * exp (-β * N * u ^ (2 * k) + β * √N * u ^ k * 0) =
      u ^ e * exp (-(N * β) * u ^ (2 * k)) := fun u => by ring_nf
  simp only [hint] at h
  rw [h, fluctuation_zero β (((e : ℝ) + 1) / (2 * k)) hβ (lam_pos hk e)]
  unfold lam
  rw [rpow_neg hβ.le]
  have : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp

/-- The tail integral `∫_b^∞ v^e e^{−Nβ v^{2k}} dv`. -/
noncomputable def monoTail (β : ℝ) (k e : ℕ) (b N : ℝ) : ℝ :=
  ∫ v in Ioi b, v ^ e * exp (-(N * β) * v ^ (2 * k))

include hβ hk in
theorem integrableOn_pow_mul_exp (e : ℕ) {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun v : ℝ => v ^ e * exp (-(N * β) * v ^ (2 * k))) (Ioi 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := ((2 * k : ℕ) : ℝ)) (s := (e : ℝ))
    (b := N * β) (by linarith [(Nat.cast_nonneg e : (0 : ℝ) ≤ e)])
    (by push_cast; linarith) (mul_pos hN hβ)
  refine h.congr_fun (fun _ _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast]

omit hβ hk in
theorem monoTail_nonneg (e : ℕ) {b : ℝ} (hb : 0 ≤ b) (N : ℝ) : 0 ≤ monoTail β k e b N :=
  setIntegral_nonneg measurableSet_Ioi fun _ hv =>
    mul_nonneg (pow_nonneg (hb.trans (le_of_lt hv)) _) (exp_pos _).le

/-- The tail constant `T_e = ∫_0^∞ v^e e^{−(β/2) v^{2k}} dv`. -/
noncomputable def tailConst (β : ℝ) (k e : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), v ^ e * exp (-(β / 2) * v ^ (2 * k))

include hβ hk in
/-- **The tail is exponentially small**: `∫_b^∞ v^e e^{−Nβ v^{2k}} ≤ e^{−Nβ b^{2k}/2} T_e` for
`N ≥ 1`, `b ≥ 0`. -/
theorem monoTail_le (e : ℕ) {b : ℝ} (hb : 0 ≤ b) {N : ℝ} (hN : 1 ≤ N) :
    monoTail β k e b N ≤ exp (-(N * β * b ^ (2 * k) / 2)) * tailConst β k e := by
  have hint : IntegrableOn (fun v : ℝ => v ^ e * exp (-(β / 2) * v ^ (2 * k))) (Ioi 0) := by
    have := integrableOn_pow_mul_exp (β := β / 2) (half_pos hβ) hk e (N := 1) one_pos
    simpa using this
  have h1 : monoTail β k e b N ≤
      ∫ v in Ioi b, exp (-(N * β * b ^ (2 * k) / 2)) * (v ^ e * exp (-(β / 2) * v ^ (2 * k))) := by
    refine setIntegral_mono_on ((integrableOn_pow_mul_exp hβ hk e (one_pos.trans_le hN)).mono_set
      (Ioi_subset_Ioi hb)) ((hint.mono_set (Ioi_subset_Ioi hb)).const_mul _) measurableSet_Ioi
      fun v hv => ?_
    have hv : b < v := hv
    have hv0 : 0 ≤ v := hb.trans hv.le
    rw [mul_left_comm, ← exp_add]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (pow_nonneg hv0 _)
    have hpow : b ^ (2 * k) ≤ v ^ (2 * k) := pow_le_pow_left₀ hb hv.le _
    have hvk : 0 ≤ v ^ (2 * k) := pow_nonneg hv0 _
    nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg (by linarith : (0:ℝ) ≤ N) hβ.le),
      mul_le_mul_of_nonneg_right hN (mul_nonneg hβ.le hvk)]
  refine h1.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  exact setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun v hv => mul_nonneg (pow_nonneg (le_of_lt hv) _) (exp_pos _).le))
    (Eventually.of_forall (Ioi_subset_Ioi hb))

include hβ hk in
/-- **The monomial box integral**:
`∫_0^b v^e e^{−Nβ v^{2k}} = Γ(λ_e)/(2kβ^{λ_e}) N^{−λ_e} − tail`. -/
theorem integral_pow_mul_exp_eq (e : ℕ) {b : ℝ} (hb : 0 ≤ b) {N : ℝ} (hN : 0 < N) :
    ∫ v in (0 : ℝ)..b, v ^ e * exp (-(N * β) * v ^ (2 * k)) =
      Gamma (lam k e) / (2 * k * β ^ lam k e) * N ^ (-lam k e) -
        monoTail β k e b N := by
  rw [← integral_pow_mul_exp_Ioi hβ hk e hN, monoTail]
  exact (integral_Ioi_sub_Ioi (integrableOn_pow_mul_exp hβ hk e hN) hb).symm

/-! ### The fully flat remainder -/

include hβ in
/-- **The flat bound**: if `|R v| ≤ M' v^p` on `[0,b]` (`p ≥ 1`) and `2kL ≤ p + h`, then
`|∫_0^b R(v) v^h e^{−Nβ v^{2k}} dv| ≤ M' · max(1, L!) · β^{−L} · b^{p+h−2kL+1}/(p+h−2kL+1) / N^L`.
-/
theorem flat_bound {R : ℝ → ℝ} (hR : Continuous R) (h p L : ℕ) (hp : 0 < p)
    (hpL : 2 * k * L ≤ p + h) {b : ℝ} (hb : 0 < b) {M' : ℝ} (hM'0 : 0 ≤ M')
    (hM' : ∀ v ∈ Icc 0 b, |R v| ≤ M' * v ^ p) {N : ℝ} (hN : 0 < N) :
    |∫ v in (0 : ℝ)..b, R v * v ^ h * exp (-(N * β) * v ^ (2 * k))| ≤
      M' * max 1 (L.factorial : ℝ) / β ^ L * (b ^ (p + h - 2 * k * L + 1) /
        ((p + h - 2 * k * L : ℕ) + 1)) / N ^ L := by
  have hcont : Continuous fun v : ℝ => R v * v ^ h * exp (-(N * β) * v ^ (2 * k)) :=
    (hR.mul (continuous_pow h)).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_pow _)))
  set c : ℝ := M' * max 1 (L.factorial : ℝ) / β ^ L / N ^ L with hc
  have hc0 : 0 ≤ c := by positivity
  set n : ℕ := p + h - 2 * k * L with hn
  -- pointwise bound on `[0, b]`
  have hpt : ∀ v ∈ uIcc (0 : ℝ) b, |R v * v ^ h * exp (-(N * β) * v ^ (2 * k))| ≤ c * v ^ n := by
    intro v hv
    rw [uIcc_of_le hb.le] at hv
    rcases hv.1.eq_or_lt with hv0 | hv0
    · subst hv0
      have hR0 : R 0 = 0 := by
        have := hM' 0 (left_mem_Icc.2 hb.le)
        rw [zero_pow hp.ne', mul_zero] at this
        exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))
      rw [hR0, zero_mul, zero_mul, abs_zero]
      positivity
    · have hx : 0 < N * β * v ^ (2 * k) := by positivity
      have hexp : exp (-(N * β * v ^ (2 * k))) ≤
          max 1 (L.factorial : ℝ) / (N * β * v ^ (2 * k)) ^ L := by
        rw [le_div_iff₀ (pow_pos hx _), mul_comm]
        exact pow_mul_exp_neg_le L hx
      have h1 : |R v * v ^ h * exp (-(N * β) * v ^ (2 * k))| ≤
          M' * v ^ p * v ^ h * (max 1 (L.factorial : ℝ) / (N * β * v ^ (2 * k)) ^ L) := by
        rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (pow_pos hv0 h)]
        have := hM' v ⟨hv0.le, hv.2⟩
        rw [show -(N * β) * v ^ (2 * k) = -(N * β * v ^ (2 * k)) by ring]
        exact mul_le_mul (mul_le_mul_of_nonneg_right this (pow_pos hv0 h).le) hexp (exp_pos _).le
          (by positivity)
      refine h1.trans (le_of_eq ?_)
      rw [hc, hn, mul_pow, mul_pow, ← pow_mul, pow_sub₀ v hv0.ne' hpL, pow_add]
      field_simp
  have hint : |∫ v in (0 : ℝ)..b, R v * v ^ h * exp (-(N * β) * v ^ (2 * k))| ≤
      ∫ v in (0 : ℝ)..b, c * v ^ n := by
    refine (intervalIntegral.norm_integral_le_integral_norm
      (f := fun v => R v * v ^ h * exp (-(N * β) * v ^ (2 * k))) hb.le).trans ?_
    exact integral_mono_on hb.le (hcont.norm.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _) fun v hv => hpt v
        (by rw [uIcc_of_le hb.le]; exact hv)
  refine hint.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow, hc, hn, zero_pow (Nat.succ_ne_zero _),
    sub_zero]
  ring

/-! ### Taylor's theorem on `[0,b]` -/

/-- The Taylor remainder of order `p` at `0`. -/
noncomputable def taylorRem (F : ℝ → ℝ) (p : ℕ) (v : ℝ) : ℝ :=
  F v - ∑ m ∈ Finset.range p, iteratedDeriv m F 0 / (m.factorial : ℝ) * v ^ m

theorem continuous_taylorRem {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℕ) :
    Continuous (taylorRem F p) :=
  hF.continuous.sub (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_pow m))

/-- `|R_p F (v)| ≤ M v^p/(p−1)!` on `[0,b]` when `|F^{(p)}| ≤ M` there (`p ≥ 1`). -/
theorem taylorRem_bound {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (q : ℕ) {b : ℝ} (hb : 0 < b) {M : ℝ}
    (hM : ∀ t ∈ Icc 0 b, |iteratedDeriv (q + 1) F t| ≤ M) {v : ℝ} (hv : v ∈ Icc 0 b) :
    |taylorRem F (q + 1) v| ≤ M / (q.factorial : ℝ) * v ^ (q + 1) := by
  have hcast : ∀ m : ℕ, ((m : ℕ) : ℕ∞ω) ≤ ∞ := fun m => WithTop.coe_le_coe.2 le_top
  have hF' : ContDiff ℝ (q + 1) F := hF.of_le (hcast _)
  have hbnd : ∀ y ∈ Icc (0 : ℝ) b, ‖iteratedDerivWithin (q + 1) F (Icc 0 b) y‖ ≤ M := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb) hF'.contDiffAt hy,
      Real.norm_eq_abs]
    exact hM y hy
  have h := taylor_mean_remainder_bound hb.le hF'.contDiffOn hv hbnd
  rw [taylor_within_apply] at h
  have hT : ∑ k ∈ Finset.range (q + 1), (((k.factorial : ℝ)⁻¹ * (v - 0) ^ k) •
      iteratedDerivWithin k F (Icc 0 b) 0) =
      ∑ m ∈ Finset.range (q + 1), iteratedDeriv m F 0 / (m.factorial : ℝ) * v ^ m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb) (hF.of_le (hcast m)).contDiffAt
      (left_mem_Icc.2 hb.le), smul_eq_mul, sub_zero]
    ring
  rw [hT, Real.norm_eq_abs, sub_zero] at h
  unfold taylorRem
  exact h.trans (le_of_eq (by ring))

/-! ### The one-dimensional smooth expansion -/

/-- The coefficient at `N^{−λ_m}`: `F^{(m)}(0)/m! · Γ(λ_m)/(2k β^{λ_m})`. -/
noncomputable def oneDimCoeff (F : ℝ → ℝ) (β : ℝ) (k h m : ℕ) : ℝ :=
  iteratedDeriv m F 0 / (m.factorial : ℝ) * (Gamma (lam k (m + h)) / (2 * k * β ^ lam k (m + h)))

include hβ hk in
/-- ★ **The one-dimensional smooth expansion**: for smooth `F` with `|F^{(p)}| ≤ M` on `[0,b]`
and `2kL ≤ p + h`, for all `N ≥ 1`,
`|∫_0^b F(v) v^h e^{−Nβ v^{2k}} dv − ∑_{m<p} oneDimCoeff m · N^{−λ_{m+h}}| ≤ C / N^L` with the
explicit constant `C` (tails of the monomials plus the flat remainder). -/
theorem oneDim_smooth {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (h q L : ℕ) (hpL : 2 * k * L ≤ q + 1 + h)
    {b : ℝ} (hb : 0 < b) {M : ℝ} (hM : ∀ t ∈ Icc 0 b, |iteratedDeriv (q + 1) F t| ≤ M) {N : ℝ}
    (hN : 1 ≤ N) :
    |(∫ v in (0 : ℝ)..b, F v * v ^ h * exp (-(N * β) * v ^ (2 * k))) -
        ∑ m ∈ Finset.range (q + 1), oneDimCoeff F β k h m * N ^ (-lam k (m + h))| ≤
      ((∑ m ∈ Finset.range (q + 1),
        |iteratedDeriv m F 0| / (m.factorial : ℝ) * tailConst β k (m + h)) *
        ((L.factorial : ℝ) / (β * b ^ (2 * k) / 2) ^ L) +
      M / (q.factorial : ℝ) * max 1 (L.factorial : ℝ) / β ^ L *
        (b ^ (q + 1 + h - 2 * k * L + 1) / ((q + 1 + h - 2 * k * L : ℕ) + 1))) / N ^ L := by
  have hNpos : 0 < N := one_pos.trans_le hN
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (left_mem_Icc.2 hb.le))
  -- the decomposition of the integrand
  have hcontF : Continuous fun v : ℝ => F v * v ^ h * exp (-(N * β) * v ^ (2 * k)) :=
    (hF.continuous.mul (continuous_pow h)).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_pow _)))
  have hcontm : ∀ m : ℕ, Continuous fun v : ℝ => v ^ (m + h) * exp (-(N * β) * v ^ (2 * k)) :=
    fun m => (continuous_pow _).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_pow _)))
  have hcontR : Continuous fun v : ℝ => taylorRem F (q + 1) v * v ^ h *
      exp (-(N * β) * v ^ (2 * k)) :=
    ((continuous_taylorRem hF _).mul (continuous_pow h)).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_pow _)))
  set G : ℝ → ℝ := fun x => ∑ m ∈ Finset.range (q + 1),
    iteratedDeriv m F 0 / (m.factorial : ℝ) * (x ^ (m + h) * exp (-(N * β) * x ^ (2 * k)))
    with hG
  set Rf : ℝ → ℝ := fun v => taylorRem F (q + 1) v * v ^ h * exp (-(N * β) * v ^ (2 * k)) with hRf
  have hcontG : Continuous G :=
    continuous_finsetSum _ fun m _ => continuous_const.mul (hcontm m)
  have hsplit : ∫ v in (0 : ℝ)..b, F v * v ^ h * exp (-(N * β) * v ^ (2 * k)) =
      (∑ m ∈ Finset.range (q + 1), iteratedDeriv m F 0 / (m.factorial : ℝ) *
        (∫ v in (0 : ℝ)..b, v ^ (m + h) * exp (-(N * β) * v ^ (2 * k)))) +
      ∫ v in (0 : ℝ)..b, Rf v := by
    calc ∫ v in (0 : ℝ)..b, F v * v ^ h * exp (-(N * β) * v ^ (2 * k))
        = ∫ v in (0 : ℝ)..b, G v + Rf v := by
          refine integral_congr fun v _ => ?_
          simp only [hG, hRf, taylorRem]
          have : ∀ m ∈ Finset.range (q + 1), iteratedDeriv m F 0 / (m.factorial : ℝ) *
              (v ^ (m + h) * exp (-(N * β) * v ^ (2 * k))) =
              iteratedDeriv m F 0 / (m.factorial : ℝ) * v ^ m * v ^ h *
                exp (-(N * β) * v ^ (2 * k)) :=
            fun m _ => by rw [pow_add]; ring
          rw [sub_mul, sub_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_congr rfl this]
          ring
      _ = (∫ v in (0 : ℝ)..b, G v) + ∫ v in (0 : ℝ)..b, Rf v :=
          integral_add (hcontG.intervalIntegrable _ _) (hcontR.intervalIntegrable _ _)
      _ = _ := by
          congr 1
          simp only [hG]
          rw [intervalIntegral.integral_finsetSum fun m _ =>
            ((hcontm m).intervalIntegrable _ _).const_mul _]
          simp_rw [intervalIntegral.integral_const_mul]
  -- the monomial integrals
  have hmono : ∀ m ∈ Finset.range (q + 1),
      iteratedDeriv m F 0 / (m.factorial : ℝ) *
        (∫ v in (0 : ℝ)..b, v ^ (m + h) * exp (-(N * β) * v ^ (2 * k))) =
      oneDimCoeff F β k h m * N ^ (-lam k (m + h)) -
        iteratedDeriv m F 0 / (m.factorial : ℝ) * monoTail β k (m + h) b N := by
    intro m _
    rw [integral_pow_mul_exp_eq hβ hk (m + h) hb.le hNpos, oneDimCoeff]
    ring
  -- the flat remainder
  have hflat : |∫ v in (0 : ℝ)..b, Rf v| ≤ M / (q.factorial : ℝ) * max 1 (L.factorial : ℝ) / β ^ L *
      (b ^ (q + 1 + h - 2 * k * L + 1) / ((q + 1 + h - 2 * k * L : ℕ) + 1)) / N ^ L :=
    flat_bound hβ (continuous_taylorRem hF (q + 1)) h (q + 1) L (Nat.succ_pos q) hpL hb
      (by positivity : (0 : ℝ) ≤ M / (q.factorial : ℝ))
      (fun v hv => taylorRem_bound hF q hb hM hv) hNpos
  -- the tails
  have htails : |∑ m ∈ Finset.range (q + 1),
      iteratedDeriv m F 0 / (m.factorial : ℝ) * monoTail β k (m + h) b N| ≤
      (∑ m ∈ Finset.range (q + 1), |iteratedDeriv m F 0| / (m.factorial : ℝ) *
        tailConst β k (m + h)) * ((L.factorial : ℝ) / (β * b ^ (2 * k) / 2) ^ L) / N ^ L := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [abs_mul, abs_of_nonneg (monoTail_nonneg (β := β) (k := k) (m + h) hb.le N),
      abs_div, abs_of_pos (by exact_mod_cast m.factorial_pos : (0 : ℝ) < m.factorial), mul_assoc,
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc monoTail β k (m + h) b N
        ≤ exp (-(N * β * b ^ (2 * k) / 2)) * tailConst β k (m + h) :=
          monoTail_le hβ hk (m + h) hb.le hN
      _ ≤ ((L.factorial : ℝ) / (β * b ^ (2 * k) / 2) ^ L / N ^ L) * tailConst β k (m + h) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · have := exp_neg_mul_le L (c := β * b ^ (2 * k) / 2) (N := N) (by positivity) hNpos
            rwa [show β * b ^ (2 * k) / 2 * N = N * β * b ^ (2 * k) / 2 by ring] at this
          · exact setIntegral_nonneg measurableSet_Ioi fun v hv =>
              mul_nonneg (pow_nonneg (le_of_lt hv) _) (exp_pos _).le
      _ = tailConst β k (m + h) * ((L.factorial : ℝ) / (β * b ^ (2 * k) / 2) ^ L * (N ^ L)⁻¹) := by
          ring
  rw [hsplit, Finset.sum_congr rfl hmono, Finset.sum_sub_distrib,
    show ∀ S1 S2 I : ℝ, S1 - S2 + I - S1 = I - S2 from fun _ _ _ => by ring, add_div]
  exact (abs_sub _ _).trans (by linarith [hflat, htails])

end SmoothEngine

end Grammar
