/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldJets

/-!
# The one-dimensional empirical smooth engine

For smooth `η, ξ : ℝ → ℝ`, `k ≥ 1`, `h ≥ 0` and `b > 0`, the one-dimensional empirical integral
`Z(N) = ∫_0^b η(u) u^h e^{−N u^{2k} + √N u^k ξ(u)} du` has the full no-log cutoff expansion
`Z(N) = ∑_{j ≤ q} C_j N^{−μ_j} + O(N^{−L})`, `μ_j = (h+j+1)/(2k)`, with
`C_j = ∂_u^j [η(u) S_{μ_j}(ξ(u))]|_{u=0} / (j! · 2k)` (★★★ `empOneDim_expansion`): the
coefficients are the normal jets of `η · S_μ∘ξ`, so derivatives of the fluctuation function enter
through the chain rule (`iteratedDeriv_mul_fluctuation`). At `ξ = 0` these are the population
coefficients `η^{(j)}(0) Γ(μ_j)/(j!·2k)` of `oneDim_smooth`.

Proof: substitute `u = N^{−1/2k} x`, Taylor-expand `v ↦ η(v) e^{x^k ξ(v)}` at `v = 0` for fixed `x`
(the jets `P_j(0, x^k) e^{x^k ξ(0)}` of `EmpiricalFieldJets`), extend the coefficient integrals to
`(0, ∞)` (tails `O(e^{−bN^{1/2k}/2})`) and bound the remainder by the master estimate
`(1+x^k)^n e^{Mx^k} e^{−x^{2k}} ≤ n! e^{1+(M+1)²/2} e^{−x^{2k}/2}`; the substitution `s = x^{2k}`
identifies the coefficient integrals with the fluctuation-jet integrals. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Elementary bounds -/

theorem le_one_add_pow {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ k := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans (by linarith [pow_nonneg hx k])
  · exact (le_self_pow₀ h1.le hk.ne').trans (by linarith)

theorem pow_le_one_add_pow_pow {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x ^ m ≤ (1 + x ^ k) ^ m :=
  pow_le_pow_left₀ hx (le_one_add_pow hk hx) m

/-- **The master bound**: `(1+x^k)^n e^{Mx^k} e^{−x^{2k}} ≤ n! e^{1+(M+1)²/2} e^{−x^{2k}/2}`. -/
theorem jet_kernel_le (k n : ℕ) (M : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x ^ k) ^ n * exp (M * x ^ k) * exp (-x ^ (2 * k)) ≤
      (n.factorial : ℝ) * exp (1 + (M + 1) ^ 2 / 2) * exp (-x ^ (2 * k) / 2) := by
  have hy0 : 0 ≤ x ^ k := pow_nonneg hx k
  have hsq : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hsq]
  have h1 := one_add_pow_le_factorial_mul_exp n hy0
  have hexp : exp (1 + x ^ k) * exp (M * x ^ k) * exp (-(x ^ k) ^ 2) ≤
      exp (1 + (M + 1) ^ 2 / 2) * exp (-(x ^ k) ^ 2 / 2) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    exact exp_le_exp.2 (by nlinarith [sq_nonneg (x ^ k - (M + 1))])
  calc (1 + x ^ k) ^ n * exp (M * x ^ k) * exp (-(x ^ k) ^ 2)
      ≤ (n.factorial : ℝ) * exp (1 + x ^ k) * exp (M * x ^ k) * exp (-(x ^ k) ^ 2) := by
        gcongr
    _ = (n.factorial : ℝ) * (exp (1 + x ^ k) * exp (M * x ^ k) * exp (-(x ^ k) ^ 2)) := by ring
    _ ≤ (n.factorial : ℝ) * (exp (1 + (M + 1) ^ 2 / 2) * exp (-(x ^ k) ^ 2 / 2)) := by gcongr
    _ = _ := by ring

/-- The half-Gaussian kernel `e^{−x^{2k}/2}` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_pow_half {k : ℕ} (hk : 0 < k) :
    IntegrableOn (fun x : ℝ => exp (-x ^ (2 * k) / 2)) (Ioi 0) := by
  have h := integrableOn_pow_mul_exp (β := 1) (k := k) (hβ := one_pos) (hk := hk) 0
    (N := 1 / 2) one_half_pos
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [pow_zero, one_mul]
  congr 1
  ring

/-- The tail of the half-Gaussian kernel: `∫_X^∞ e^{−x^{2k}/2} dx ≤ 2 e^{−X/2}` for `X ≥ 1`. -/
theorem integral_exp_neg_pow_half_Ioi_le {k : ℕ} (hk : 0 < k) {X : ℝ} (hX : 1 ≤ X) :
    ∫ x in Ioi X, exp (-x ^ (2 * k) / 2) ≤ 2 * exp (-X / 2) := by
  have hle : ∀ x ∈ Ioi X, exp (-x ^ (2 * k) / 2) ≤ exp (-(1 / 2 * x)) := fun x hx => by
    have hx1 : 1 ≤ x := hX.trans (le_of_lt hx)
    have := le_self_pow₀ hx1 (by omega : 2 * k ≠ 0)
    exact exp_le_exp.2 (by linarith)
  have hint2 : IntegrableOn (fun x : ℝ => exp (-(1 / 2 * x))) (Ioi X) :=
    (exp_neg_integrableOn_Ioi X (b := 1 / 2) one_half_pos).congr_fun
      (fun x _ => by ring_nf) measurableSet_Ioi
  have hX0 : (0 : ℝ) ≤ X := by linarith
  calc ∫ x in Ioi X, exp (-x ^ (2 * k) / 2)
      ≤ ∫ x in Ioi X, exp (-(1 / 2 * x)) :=
        setIntegral_mono_on ((integrableOn_exp_neg_pow_half hk).mono_set
          (Ioi_subset_Ioi hX0)) hint2 measurableSet_Ioi hle
    _ = 2 * exp (-X / 2) := by
        have := integral_comp_mul_left_Ioi (fun x => exp (-x)) X (b := 1 / 2) one_half_pos
        simp only [smul_eq_mul, integral_exp_neg_Ioi] at this
        rw [this]
        ring_nf

/-- `e^{−X/2} ≤ max(1, (2kL)!) (2/b)^{2kL} N^{−L}` when `X = b N^{1/2k}`. -/
theorem exp_neg_half_scaled_le (k L : ℕ) (hk : 0 < k) {b N : ℝ} (hb : 0 < b) (hN : 0 < N) :
    exp (-(b * N ^ (1 / (2 * (k : ℝ)))) / 2) ≤
      max 1 ((2 * k * L).factorial : ℝ) * (2 / b) ^ (2 * k * L) * N ^ (-(L : ℝ)) := by
  set y : ℝ := b * N ^ (1 / (2 * (k : ℝ))) / 2 with hy
  have hNr : 0 < N ^ (1 / (2 * (k : ℝ))) := Real.rpow_pos_of_pos hN _
  have hy0 : 0 < y := by positivity
  have h := pow_mul_exp_neg_le (2 * k * L) hy0
  have hyL : y ^ (2 * k * L) = (b / 2) ^ (2 * k * L) * N ^ (L : ℝ) := by
    rw [hy, show b * N ^ (1 / (2 * (k : ℝ))) / 2 = b / 2 * N ^ (1 / (2 * (k : ℝ))) by ring,
      mul_pow, ← Real.rpow_natCast (N ^ (1 / (2 * (k : ℝ)))), ← Real.rpow_mul hN.le]
    congr 2
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
  rw [show -(b * N ^ (1 / (2 * (k : ℝ)))) / 2 = -y by rw [hy]; ring]
  rw [hyL] at h
  have hb2 : (0 : ℝ) < (b / 2) ^ (2 * k * L) := by positivity
  have hNL : (0 : ℝ) < N ^ (L : ℝ) := Real.rpow_pos_of_pos hN _
  have hNinv : N ^ (-(L : ℝ)) = (N ^ (L : ℝ))⁻¹ := Real.rpow_neg hN.le _
  rw [hNinv]
  have h2 : (2 / b) ^ (2 * k * L) = ((b / 2) ^ (2 * k * L))⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [h2]
  have hprod : 0 < (b / 2) ^ (2 * k * L) * N ^ (L : ℝ) := mul_pos hb2 hNL
  calc exp (-y)
      = (b / 2) ^ (2 * k * L) * N ^ (L : ℝ) * exp (-y) / ((b / 2) ^ (2 * k * L) * N ^ (L : ℝ)) := by
        field_simp
    _ ≤ max 1 ((2 * k * L).factorial : ℝ) / ((b / 2) ^ (2 * k * L) * N ^ (L : ℝ)) :=
        div_le_div_of_nonneg_right h hprod.le
    _ = max 1 ((2 * k * L).factorial : ℝ) * ((b / 2) ^ (2 * k * L))⁻¹ * (N ^ (L : ℝ))⁻¹ := by
        rw [div_eq_mul_inv, mul_inv]
        ring

/-! ### The empirical integral, its coefficients and the coefficient integrands -/

variable (η ξ : ℝ → ℝ)

/-- The one-dimensional empirical integral `∫_0^b η(u) u^h e^{−N u^{2k} + √N u^k ξ(u)} du`. -/
noncomputable def empOneDim (h k : ℕ) (b N : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..b, η u * u ^ h * exp (-N * u ^ (2 * k) + Real.sqrt N * u ^ k * ξ u)

/-- The coefficient at `N^{−μ_j}`, `μ_j = (h+j+1)/(2k)`: `∂_u^j[η · S_{μ_j}∘ξ](0)/(j!·2k)`. -/
noncomputable def empOneDimCoeff (h k j : ℕ) : ℝ :=
  iteratedDeriv j (fun v => η v * fluctuation 1 (lam k (j + h)) (ξ v)) 0 /
    ((j.factorial : ℝ) * (2 * k))

/-- The coefficient integrand in the scaled variable:
`P_j(0, x^k) e^{x^k ξ(0)} x^{h+j} e^{−x^{2k}}`. -/
noncomputable def jetInt (h k j : ℕ) (x : ℝ) : ℝ :=
  jetPoly η ξ j 0 (x ^ k) * exp (x ^ k * ξ 0) * (x ^ (h + j) * exp (-x ^ (2 * k)))

/-- The scaled integrand `η(εx) e^{x^k ξ(εx)} x^h e^{−x^{2k}}`. -/
noncomputable def scaledInt (h k : ℕ) (ε x : ℝ) : ℝ :=
  η (ε * x) * exp (x ^ k * ξ (ε * x)) * (x ^ h * exp (-x ^ (2 * k)))

variable {η ξ}

theorem continuous_jetPoly_snd (j : ℕ) (v : ℝ) : Continuous fun τ => jetPoly η ξ j v τ := by
  unfold jetPoly
  fun_prop

theorem continuous_jetInt (h k j : ℕ) : Continuous (jetInt η ξ h k j) := by
  unfold jetInt
  have := continuous_jetPoly_snd (η := η) (ξ := ξ) j 0
  fun_prop

theorem continuous_scaledInt (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h k : ℕ) (ε : ℝ) :
    Continuous (scaledInt η ξ h k ε) := by
  unfold scaledInt
  have := hη.continuous
  have := hξ.continuous
  fun_prop

/-! ### The scaling substitution `u = N^{−1/2k} x` -/

/-- The scale `ε = N^{−1/2k}`. -/
noncomputable def scaleEps (k : ℕ) (N : ℝ) : ℝ := N ^ (-(1 : ℝ) / (2 * (k : ℝ)))

theorem scaleEps_pos {k : ℕ} {N : ℝ} (hN : 0 < N) : 0 < scaleEps k N :=
  Real.rpow_pos_of_pos hN _

theorem scaleEps_le_one {k : ℕ} (hk : 0 < k) {N : ℝ} (hN : 1 ≤ N) : scaleEps k N ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN (by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))

theorem scaleEps_pow_two_mul {k : ℕ} (hk : 0 < k) {N : ℝ} (hN : 0 < N) :
    N * scaleEps k N ^ (2 * k) = 1 := by
  unfold scaleEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : -(1 : ℝ) / (2 * (k : ℝ)) * ((2 * k : ℕ) : ℝ) = -1 := by push_cast; field_simp
  rw [this, Real.rpow_neg_one, mul_inv_cancel₀ hN.ne']

theorem sqrt_mul_scaleEps_pow {k : ℕ} (hk : 0 < k) {N : ℝ} (hN : 0 < N) :
    Real.sqrt N * scaleEps k N ^ k = 1 := by
  unfold scaleEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, Real.sqrt_eq_rpow, ← Real.rpow_add hN]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have : (1 : ℝ) / 2 + -(1 : ℝ) / (2 * (k : ℝ)) * (k : ℝ) = 0 := by field_simp; ring
  rw [this, Real.rpow_zero]

theorem scaleEps_pow_eq_rpow {k : ℕ} {N : ℝ} (hN : 0 < N) (m : ℕ) :
    scaleEps k N ^ m = N ^ (-((m : ℝ) / (2 * (k : ℝ)))) := by
  unfold scaleEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

theorem scaleEps_pow_eq_rpow_neg_lam {k : ℕ} {N : ℝ} (hN : 0 < N) (e : ℕ) :
    scaleEps k N ^ (e + 1) = N ^ (-lam k e) := by
  rw [scaleEps_pow_eq_rpow hN]
  unfold lam
  push_cast
  ring_nf

/-- **The scaling substitution**:
`Z(N) = ε^{h+1} ∫_0^{b/ε} η(εx) e^{x^k ξ(εx)} x^h e^{−x^{2k}} dx`. -/
theorem empOneDim_eq_scaled {k : ℕ} (hk : 0 < k) (h : ℕ) (b : ℝ) {N : ℝ} (hN : 0 < N) :
    empOneDim η ξ h k b N = scaleEps k N ^ (h + 1) *
      ∫ x in (0 : ℝ)..(b / scaleEps k N), scaledInt η ξ h k (scaleEps k N) x := by
  set ε := scaleEps k N with hε
  have hε0 : 0 < ε := scaleEps_pos hN
  have hN2 : N * ε ^ (2 * k) = 1 := scaleEps_pow_two_mul hk hN
  have hNs : Real.sqrt N * ε ^ k = 1 := sqrt_mul_scaleEps_pow hk hN
  have hpt : ∀ x : ℝ, η (ε * x) * (ε * x) ^ h *
      exp (-N * (ε * x) ^ (2 * k) + Real.sqrt N * (ε * x) ^ k * ξ (ε * x)) =
      ε ^ h * scaledInt η ξ h k ε x := by
    intro x
    unfold scaledInt
    have e1 : -N * (ε * x) ^ (2 * k) + Real.sqrt N * (ε * x) ^ k * ξ (ε * x) =
        -x ^ (2 * k) + x ^ k * ξ (ε * x) := by
      rw [mul_pow, mul_pow,
        show -N * (ε ^ (2 * k) * x ^ (2 * k)) = -(N * ε ^ (2 * k)) * x ^ (2 * k) by ring, hN2,
        show Real.sqrt N * (ε ^ k * x ^ k) = (Real.sqrt N * ε ^ k) * x ^ k by ring, hNs]
      ring
    rw [e1, exp_add, mul_pow]
    ring
  have h1 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := b / ε)
    (fun u => η u * u ^ h * exp (-N * u ^ (2 * k) + Real.sqrt N * u ^ k * ξ u)) hε0.ne'
  rw [mul_zero, mul_div_cancel₀ _ hε0.ne', smul_eq_mul] at h1
  unfold empOneDim
  have h2 : (∫ u in (0 : ℝ)..b, η u * u ^ h *
      exp (-N * u ^ (2 * k) + Real.sqrt N * u ^ k * ξ u)) =
      ε * ∫ x in (0 : ℝ)..b / ε, η (ε * x) * (ε * x) ^ h *
        exp (-N * (ε * x) ^ (2 * k) + Real.sqrt N * (ε * x) ^ k * ξ (ε * x)) := by
    rw [h1]
    field_simp
  rw [h2]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, pow_succ]
  ring

/-! ### The coefficient integrands -/

/-- The kernel constant `n! e^{1+(M+1)²/2}` of the master bound. -/
noncomputable def kernelConst (n : ℕ) (M : ℝ) : ℝ := (n.factorial : ℝ) * exp (1 + (M + 1) ^ 2 / 2)

theorem kernelConst_nonneg (n : ℕ) (M : ℝ) : 0 ≤ kernelConst n M := by
  unfold kernelConst
  positivity

/-- `|P_j(0, x^k)| e^{x^k ξ(0)} x^{h+j} e^{−x^{2k}} ≤ C · kernelConst (h+2j) M · e^{−x^{2k}/2}`
given `|P_j(0, τ)| ≤ C (1+τ)^j` and `ξ(0) ≤ M`. -/
theorem abs_jetInt_le {k : ℕ} (hk : 0 < k) (h j : ℕ) {C M : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j 0 τ| ≤ C * (1 + τ) ^ j) (hM : ξ 0 ≤ M) {x : ℝ}
    (hx : 0 ≤ x) :
    |jetInt η ξ h k j x| ≤ C * kernelConst (h + 2 * j) M * exp (-x ^ (2 * k) / 2) := by
  unfold jetInt
  have hy0 : 0 ≤ x ^ k := pow_nonneg hx k
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _),
    abs_of_nonneg (pow_nonneg hx _)]
  have h1 : |jetPoly η ξ j 0 (x ^ k)| ≤ C * (1 + x ^ k) ^ j := hC _ hy0
  have h2 : exp (x ^ k * ξ 0) ≤ exp (M * x ^ k) := exp_le_exp.2 (by nlinarith)
  have h3 : x ^ (h + j) ≤ (1 + x ^ k) ^ (h + j) := pow_le_one_add_pow_pow hk hx _
  have hK := jet_kernel_le k (h + 2 * j) M hx
  calc |jetPoly η ξ j 0 (x ^ k)| * exp (x ^ k * ξ 0) * (x ^ (h + j) * exp (-x ^ (2 * k)))
      ≤ C * (1 + x ^ k) ^ j * exp (M * x ^ k) * ((1 + x ^ k) ^ (h + j) * exp (-x ^ (2 * k))) := by
        gcongr
    _ = C * ((1 + x ^ k) ^ (h + 2 * j) * exp (M * x ^ k) * exp (-x ^ (2 * k))) := by
        rw [show h + 2 * j = j + (h + j) by ring, pow_add]
        ring
    _ ≤ C * (kernelConst (h + 2 * j) M * exp (-x ^ (2 * k) / 2)) := by
        unfold kernelConst
        gcongr
    _ = C * kernelConst (h + 2 * j) M * exp (-x ^ (2 * k) / 2) := by ring

theorem integrableOn_jetInt_Ioi {k : ℕ} (hk : 0 < k) (h j : ℕ) {C M : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j 0 τ| ≤ C * (1 + τ) ^ j) (hM : ξ 0 ≤ M) :
    IntegrableOn (jetInt η ξ h k j) (Ioi 0) := by
  refine ((integrableOn_exp_neg_pow_half hk).const_mul (C * kernelConst (h + 2 * j) M)).mono'
    (continuous_jetInt h k j).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_jetInt_le hk h j hC0 hC hM (le_of_lt hx)

/-- The coefficient integral is the fluctuation-jet integral: substituting `s = x^{2k}`,
`∫_0^∞ P_j(0,x^k) e^{x^k ξ(0)} x^{h+j} e^{−x^{2k}} dx`
`  = (1/2k) ∫_0^∞ s^{μ_j−1} e^{−s} P_j(0,√s) e^{√s ξ(0)} ds`. -/
theorem integral_jetInt_eq_fluctJet {k : ℕ} (hk : 0 < k) (h j : ℕ) :
    ∫ x in Ioi (0 : ℝ), jetInt η ξ h k j x =
      (1 / (2 * (k : ℝ))) * fluctJet η ξ (lam k (j + h)) j 0 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by positivity
  set μ := lam k (j + h) with hμ
  have hsub := integral_comp_rpow_Ioi_of_pos (p := ((2 * k : ℕ) : ℝ))
    (g := fun s => (1 / (2 * (k : ℝ))) * (s ^ (μ - 1) * exp (-s) *
      (jetPoly η ξ j 0 (Real.sqrt s) * exp (Real.sqrt s * ξ 0)))) hp
  unfold fluctJet
  rw [← MeasureTheory.integral_const_mul, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [smul_eq_mul]
  have hnat : x ^ ((2 * k : ℕ) : ℝ) = x ^ (2 * k) := Real.rpow_natCast x (2 * k)
  have hsq : Real.sqrt (x ^ (2 * k)) = x ^ k := by
    rw [show x ^ (2 * k) = (x ^ k) ^ 2 by rw [← pow_mul, mul_comm]]
    exact Real.sqrt_sq (pow_nonneg hx0.le k)
  have hpow : x ^ (((2 * k : ℕ) : ℝ) - 1) * (x ^ (2 * k)) ^ (μ - 1) = x ^ (h + j) := by
    rw [← Real.rpow_natCast x (2 * k), ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    rw [← Real.rpow_natCast x (h + j)]
    congr 1
    rw [hμ]
    unfold lam
    push_cast
    field_simp
    ring
  rw [hnat, hsq]
  unfold jetInt
  symm
  calc ((2 * k : ℕ) : ℝ) * x ^ (((2 * k : ℕ) : ℝ) - 1) * ((1 / (2 * (k : ℝ))) *
        ((x ^ (2 * k)) ^ (μ - 1) * exp (-x ^ (2 * k)) *
          (jetPoly η ξ j 0 (x ^ k) * exp (x ^ k * ξ 0))))
      = (((2 * k : ℕ) : ℝ) * (1 / (2 * (k : ℝ)))) *
          (x ^ (((2 * k : ℕ) : ℝ) - 1) * (x ^ (2 * k)) ^ (μ - 1)) *
          (exp (-x ^ (2 * k)) * (jetPoly η ξ j 0 (x ^ k) * exp (x ^ k * ξ 0))) := by ring
    _ = jetPoly η ξ j 0 (x ^ k) * exp (x ^ k * ξ 0) * (x ^ (h + j) * exp (-x ^ (2 * k))) := by
        rw [hpow, show ((2 * k : ℕ) : ℝ) * (1 / (2 * (k : ℝ))) = 1 by push_cast; field_simp]
        ring

/-! ### Tails of the coefficient integrals -/

/-- `|∫_X^∞ jetInt| ≤ C · kernelConst · 2 e^{−X/2}` for `X ≥ 1`. -/
theorem abs_integral_jetInt_Ioi_le {k : ℕ} (hk : 0 < k) (h j : ℕ) {C M : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ j 0 τ| ≤ C * (1 + τ) ^ j) (hM : ξ 0 ≤ M) {X : ℝ}
    (hX : 1 ≤ X) :
    |∫ x in Ioi X, jetInt η ξ h k j x| ≤
      C * kernelConst (h + 2 * j) M * (2 * exp (-X / 2)) := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hg0 : IntegrableOn (fun x : ℝ => C * kernelConst (h + 2 * j) M * exp (-x ^ (2 * k) / 2))
      (Ioi 0) := (integrableOn_exp_neg_pow_half hk).const_mul _
  have hg : IntegrableOn (fun x : ℝ => C * kernelConst (h + 2 * j) M * exp (-x ^ (2 * k) / 2))
      (Ioi X) := hg0.mono_set (Ioi_subset_Ioi hX0)
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi X))
    (f := jetInt η ξ h k j) hg ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        exact abs_jetInt_le hk h j hC0 hC hM (hX0.trans (le_of_lt hx))))
  rw [Real.norm_eq_abs, MeasureTheory.integral_const_mul] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (integral_exp_neg_pow_half_Ioi_le hk hX)
    (mul_nonneg hC0 (kernelConst_nonneg _ _))

/-! ### The Taylor remainder in the scaled variable -/

variable (η ξ) in
/-- The scaled integrand minus its `q`-th Taylor jets: `scaledInt − ∑_{j≤q} ε^j/j! · jetInt_j`. -/
noncomputable def remFn (h k q : ℕ) (ε x : ℝ) : ℝ :=
  scaledInt η ξ h k ε x -
    ∑ j ∈ Finset.range (q + 1), ε ^ j / (j.factorial : ℝ) * jetInt η ξ h k j x

theorem continuous_remFn (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h k q : ℕ) (ε : ℝ) :
    Continuous (remFn η ξ h k q ε) := by
  unfold remFn
  exact (continuous_scaledInt hη hξ h k ε).sub
    (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_jetInt h k j))

/-- The remainder function is the Taylor remainder of `v ↦ η(v) e^{x^k ξ(v)}` at `v = εx`, times
`x^h e^{−x^{2k}}`. -/
theorem remFn_eq_taylorRem (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h k q : ℕ) (ε x : ℝ) :
    remFn η ξ h k q ε x =
      taylorRem (fun v => η v * exp (x ^ k * ξ v)) (q + 1) (ε * x) *
        (x ^ h * exp (-x ^ (2 * k))) := by
  unfold remFn taylorRem scaledInt jetInt
  have hd : ∀ m : ℕ, iteratedDeriv m (fun v => η v * exp (x ^ k * ξ v)) 0 =
      jetPoly η ξ m 0 (x ^ k) * exp (x ^ k * ξ 0) := fun m =>
    congrFun (iteratedDeriv_mul_exp_field hη hξ (x ^ k) m) 0
  simp only [hd]
  rw [sub_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, pow_add]
  ring

/-- The remainder bound: for `0 ≤ x` with `εx ≤ b`,
`|remFn ε x| ≤ (C/q!) ε^{q+1} (1+x^k)^{h+2q+2} e^{Mx^k} e^{−x^{2k}}`. -/
theorem abs_remFn_le (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ} (hk : 0 < k)
    (q : ℕ) {b : ℝ} (hb : 0 < b) {C M : ℝ}
    (hC : ∀ t ∈ Icc 0 b, ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ (q + 1) t τ| ≤ C * (1 + τ) ^ (q + 1))
    (hM : ∀ t ∈ Icc 0 b, ξ t ≤ M) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) (hxb : ε * x ≤ b) :
    |remFn η ξ h k q ε x| ≤ C / (q.factorial : ℝ) * ε ^ (q + 1) *
      ((1 + x ^ k) ^ (h + 2 * q + 2) * exp (M * x ^ k) * exp (-x ^ (2 * k))) := by
  have hy0 : 0 ≤ x ^ k := pow_nonneg hx k
  have hC0 : 0 ≤ C := by
    have := hC 0 (left_mem_Icc.2 hb.le) 0 le_rfl
    have h0 : (0 : ℝ) ≤ |jetPoly η ξ (q + 1) 0 0| := abs_nonneg _
    simpa using h0.trans this
  set F : ℝ → ℝ := fun v => η v * exp (x ^ k * ξ v) with hF
  have hFc : ContDiff ℝ ∞ F := hη.mul ((contDiff_const.mul hξ).exp)
  have hder : ∀ t ∈ Icc 0 b, |iteratedDeriv (q + 1) F t| ≤
      C * (1 + x ^ k) ^ (q + 1) * exp (M * x ^ k) := by
    intro t ht
    rw [hF, iteratedDeriv_mul_exp_field hη hξ (x ^ k) (q + 1)]
    simp only
    rw [abs_mul, abs_of_pos (exp_pos _)]
    have h1 := hC t ht (x ^ k) hy0
    have h2 : exp (x ^ k * ξ t) ≤ exp (M * x ^ k) := exp_le_exp.2 (by nlinarith [hM t ht])
    exact mul_le_mul h1 h2 (exp_pos _).le (mul_nonneg hC0 (pow_nonneg (by positivity) _))
  have hv : ε * x ∈ Icc 0 b := ⟨by positivity, hxb⟩
  have hT := taylorRem_bound hFc q hb hder hv
  rw [remFn_eq_taylorRem hη hξ h k q ε x, abs_mul,
    abs_of_nonneg (mul_nonneg (pow_nonneg hx h) (exp_pos _).le)]
  have hpow : x ^ h * x ^ (q + 1) ≤ (1 + x ^ k) ^ (h + q + 1) := by
    rw [← pow_add]
    exact pow_le_one_add_pow_pow hk hx _
  calc |taylorRem F (q + 1) (ε * x)| * (x ^ h * exp (-x ^ (2 * k)))
      ≤ C * (1 + x ^ k) ^ (q + 1) * exp (M * x ^ k) / (q.factorial : ℝ) * (ε * x) ^ (q + 1) *
          (x ^ h * exp (-x ^ (2 * k))) := by gcongr
    _ = C / (q.factorial : ℝ) * ε ^ (q + 1) *
          ((1 + x ^ k) ^ (q + 1) * (x ^ h * x ^ (q + 1)) * exp (M * x ^ k) *
            exp (-x ^ (2 * k))) := by
        rw [mul_pow]
        ring
    _ ≤ C / (q.factorial : ℝ) * ε ^ (q + 1) *
          ((1 + x ^ k) ^ (q + 1) * (1 + x ^ k) ^ (h + q + 1) * exp (M * x ^ k) *
            exp (-x ^ (2 * k))) := by
        gcongr
    _ = C / (q.factorial : ℝ) * ε ^ (q + 1) *
          ((1 + x ^ k) ^ (h + 2 * q + 2) * exp (M * x ^ k) * exp (-x ^ (2 * k))) := by
        rw [← pow_add, show q + 1 + (h + q + 1) = h + 2 * q + 2 by ring]

/-- The integrated remainder:
`|∫_0^X remFn| ≤ ε^{q+1} · (C/q!) kernelConst (h+2q+2) M ∫_0^∞ e^{−x^{2k}/2}`. -/
theorem abs_integral_remFn_le (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) (q : ℕ) {b : ℝ} (hb : 0 < b) {C M : ℝ}
    (hC : ∀ t ∈ Icc 0 b, ∀ τ : ℝ, 0 ≤ τ → |jetPoly η ξ (q + 1) t τ| ≤ C * (1 + τ) ^ (q + 1))
    (hM : ∀ t ∈ Icc 0 b, ξ t ≤ M) {ε : ℝ} (hε : 0 < ε) {X : ℝ} (hX0 : 0 ≤ X) (hXb : ε * X ≤ b) :
    |∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x| ≤ ε ^ (q + 1) *
      (C / (q.factorial : ℝ) * kernelConst (h + 2 * q + 2) M *
        ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2)) := by
  have hC0 : 0 ≤ C := by
    have := hC 0 (left_mem_Icc.2 hb.le) 0 le_rfl
    have h0 : (0 : ℝ) ≤ |jetPoly η ξ (q + 1) 0 0| := abs_nonneg _
    simpa using h0.trans this
  have hK0 : 0 ≤ kernelConst (h + 2 * q + 2) M := kernelConst_nonneg _ _
  set c : ℝ := C / (q.factorial : ℝ) * ε ^ (q + 1) * kernelConst (h + 2 * q + 2) M with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg (div_nonneg hC0 (Nat.cast_nonneg _)) (pow_nonneg hε.le _)) hK0
  have hgi : IntervalIntegrable (fun x : ℝ => c * exp (-x ^ (2 * k) / 2)) volume 0 X :=
    (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le (f := remFn η ξ h k q ε)
    (g := fun x => c * exp (-x ^ (2 * k) / 2)) hX0 (Eventually.of_forall fun t ht => ?_) hgi
  · rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hX0]
    have hmono : ∫ x in Ioc (0 : ℝ) X, exp (-x ^ (2 * k) / 2) ≤
        ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2) :=
      setIntegral_mono_set (integrableOn_exp_neg_pow_half hk)
        (Eventually.of_forall fun x => (exp_pos _).le)
        (LE.le.eventuallyLE Ioc_subset_Ioi_self)
    calc c * ∫ x in Ioc (0 : ℝ) X, exp (-x ^ (2 * k) / 2)
        ≤ c * ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2) := mul_le_mul_of_nonneg_left hmono hc0
      _ = _ := by rw [hc]; ring
  · have ht0 : 0 ≤ t := le_of_lt ht.1
    have htb : ε * t ≤ b := (mul_le_mul_of_nonneg_left ht.2 hε.le).trans hXb
    rw [Real.norm_eq_abs]
    refine (abs_remFn_le hη hξ h hk q hb hC hM hε ht0 htb).trans ?_
    have hker : (1 + t ^ k) ^ (h + 2 * q + 2) * exp (M * t ^ k) * exp (-t ^ (2 * k)) ≤
        kernelConst (h + 2 * q + 2) M * exp (-t ^ (2 * k) / 2) := by
      unfold kernelConst
      exact jet_kernel_le k _ M ht0
    calc C / (q.factorial : ℝ) * ε ^ (q + 1) *
          ((1 + t ^ k) ^ (h + 2 * q + 2) * exp (M * t ^ k) * exp (-t ^ (2 * k)))
        ≤ C / (q.factorial : ℝ) * ε ^ (q + 1) *
          (kernelConst (h + 2 * q + 2) M * exp (-t ^ (2 * k) / 2)) :=
          mul_le_mul_of_nonneg_left hker
            (mul_nonneg (div_nonneg hC0 (Nat.cast_nonneg _)) (pow_nonneg hε.le _))
      _ = c * exp (-t ^ (2 * k) / 2) := by rw [hc]; ring

/-! ### The expansion -/

/-- ★★★ **The one-dimensional empirical smooth expansion**: for smooth `η, ξ`, `k ≥ 1`, `b > 0` and
`2kL ≤ q + 1 + h`, there is `C` with
`|∫_0^b η u^h e^{−Nu^{2k} + √N u^k ξ} du − ∑_{j ≤ q} empOneDimCoeff_j N^{−(h+j+1)/2k}| ≤ C N^{−L}`
for all `N ≥ 1` with `b N^{1/2k} ≥ 1`, where
`empOneDimCoeff_j = ∂_u^j[η(u) S_{(h+j+1)/2k}(ξ(u))]|_{u=0} / (j! · 2k)`. -/
theorem empOneDim_expansion (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) {b : ℝ} (hb : 0 < b) (q L : ℕ) (hqL : 2 * k * L ≤ q + 1 + h) :
    ∃ C : ℝ, ∀ N : ℝ, 1 ≤ N → 1 ≤ b * N ^ (1 / (2 * (k : ℝ))) →
      |empOneDim η ξ h k b N -
        ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h))| ≤
        C * N ^ (-(L : ℝ)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hξ.continuous.continuousOn (s := Icc 0 b))
  have hM' : ∀ t ∈ Icc 0 b, ξ t ≤ M := fun t ht =>
    (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM t ht)
  have hM0 : ξ 0 ≤ M := hM' 0 (left_mem_Icc.2 hb.le)
  choose Cj hCj using fun j => exists_jetPoly_bound hη hξ j 0 b
  have hCj0 : ∀ j τ, 0 ≤ τ → |jetPoly η ξ j 0 τ| ≤ Cj j * (1 + τ) ^ j :=
    fun j τ hτ => (hCj j).2 0 (left_mem_Icc.2 hb.le) τ hτ
  set R : ℝ := Cj (q + 1) / (q.factorial : ℝ) * kernelConst (h + 2 * q + 2) M *
    ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2) with hR
  set T : ℝ := ∑ j ∈ Finset.range (q + 1),
    2 * Cj j * kernelConst (h + 2 * j) M / (j.factorial : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => by
    have := (hCj j).1
    have := kernelConst_nonneg (h + 2 * j) M
    positivity
  set E : ℝ := max 1 ((2 * k * L).factorial : ℝ) * (2 / b) ^ (2 * k * L) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨T * E + R, fun N hN hX => ?_⟩
  have hN0 : 0 < N := by linarith
  set ε := scaleEps k N with hε
  have hε0 : 0 < ε := scaleEps_pos hN0
  have hε1 : ε ≤ 1 := scaleEps_le_one hk hN
  set X := b / ε with hXdef
  have hXeq : X = b * N ^ (1 / (2 * (k : ℝ))) := by
    rw [hXdef, hε]
    unfold scaleEps
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le]
    congr 2
    ring
  have hX1 : 1 ≤ X := hXeq ▸ hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXb : ε * X = b := by rw [hXdef]; field_simp
  have hNL : 0 < N ^ (-(L : ℝ)) := Real.rpow_pos_of_pos hN0 _
  -- the decomposition of the scaled integral
  have hdecomp : empOneDim η ξ h k b N = ε ^ (h + 1) *
      ((∑ j ∈ Finset.range (q + 1), ε ^ j / (j.factorial : ℝ) *
        ∫ x in (0 : ℝ)..X, jetInt η ξ h k j x) + ∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x) := by
    rw [empOneDim_eq_scaled hk h b hN0, ← hε, ← hXdef]
    congr 1
    have hint : ∀ j ∈ Finset.range (q + 1),
        IntervalIntegrable (fun x => ε ^ j / (j.factorial : ℝ) * jetInt η ξ h k j x) volume 0 X :=
      fun j _ => (continuous_const.mul (continuous_jetInt h k j)).intervalIntegrable _ _
    calc ∫ x in (0 : ℝ)..X, scaledInt η ξ h k ε x
        = ∫ x in (0 : ℝ)..X, (∑ j ∈ Finset.range (q + 1),
            ε ^ j / (j.factorial : ℝ) * jetInt η ξ h k j x) + remFn η ξ h k q ε x := by
          refine intervalIntegral.integral_congr fun x _ => ?_
          simp only [remFn]
          ring
      _ = (∫ x in (0 : ℝ)..X, ∑ j ∈ Finset.range (q + 1),
            ε ^ j / (j.factorial : ℝ) * jetInt η ξ h k j x) +
            ∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x :=
          intervalIntegral.integral_add
            ((continuous_finsetSum _ fun j _ =>
              continuous_const.mul (continuous_jetInt h k j)).intervalIntegrable _ _)
            ((continuous_remFn hη hξ h k q ε).intervalIntegrable _ _)
      _ = _ := by
          rw [intervalIntegral.integral_finsetSum hint]
          simp_rw [intervalIntegral.integral_const_mul]
  -- the coefficient integrals over `[0, X]` versus `(0, ∞)`
  have hsplit : ∀ j, ∫ x in (0 : ℝ)..X, jetInt η ξ h k j x =
      (∫ x in Ioi (0 : ℝ), jetInt η ξ h k j x) - ∫ x in Ioi X, jetInt η ξ h k j x := by
    intro j
    have hI := integrableOn_jetInt_Ioi hk h j (hCj j).1 (hCj0 j) hM0
    rw [intervalIntegral.integral_of_le hX0, ← Ioc_union_Ioi_eq_Ioi hX0,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hI.mono_set Ioc_subset_Ioi_self)
        (hI.mono_set (Ioi_subset_Ioi hX0))]
    ring
  -- identification of the coefficients
  have hcoef : ∀ j, ε ^ (h + 1) *
      (ε ^ j / (j.factorial : ℝ) * ∫ x in Ioi (0 : ℝ), jetInt η ξ h k j x) =
      empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h)) := by
    intro j
    rw [integral_jetInt_eq_fluctJet hk h j]
    unfold empOneDimCoeff
    rw [iteratedDeriv_mul_fluctuation hη hξ (lam_pos hk (j + h)) j,
      ← scaleEps_pow_eq_rpow_neg_lam hN0 (j + h), ← hε, show j + h + 1 = (h + 1) + j by ring,
      pow_add]
    have hj : (0 : ℝ) < j.factorial := Nat.cast_pos.2 (Nat.factorial_pos j)
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
    ring
  -- the difference
  have hdiff : empOneDim η ξ h k b N -
      ∑ j ∈ Finset.range (q + 1), empOneDimCoeff η ξ h k j * N ^ (-lam k (j + h)) =
      ε ^ (h + 1) * ((∑ j ∈ Finset.range (q + 1),
        -(ε ^ j / (j.factorial : ℝ) * ∫ x in Ioi X, jetInt η ξ h k j x)) +
        ∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x) := by
    rw [hdecomp, ← Finset.sum_congr rfl fun j _ => hcoef j]
    simp only [hsplit, mul_add, Finset.mul_sum]
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- bounds
  have hsum : |∑ j ∈ Finset.range (q + 1),
      -(ε ^ j / (j.factorial : ℝ) * ∫ x in Ioi X, jetInt η ξ h k j x)| ≤ T * exp (-X / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_neg, abs_mul, abs_div, abs_of_pos (pow_pos hε0 j),
      abs_of_pos (Nat.cast_pos.2 (Nat.factorial_pos j))]
    have hεj : ε ^ j ≤ 1 := pow_le_one₀ hε0.le hε1
    have hj : (0 : ℝ) < j.factorial := Nat.cast_pos.2 (Nat.factorial_pos j)
    have htail := abs_integral_jetInt_Ioi_le hk h j (hCj j).1 (hCj0 j) hM0 hX1
    calc ε ^ j / (j.factorial : ℝ) * |∫ x in Ioi X, jetInt η ξ h k j x|
        ≤ 1 / (j.factorial : ℝ) * (Cj j * kernelConst (h + 2 * j) M * (2 * exp (-X / 2))) := by
          gcongr
      _ = 2 * Cj j * kernelConst (h + 2 * j) M / (j.factorial : ℝ) * exp (-X / 2) := by ring
  have hrem : |∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x| ≤ ε ^ (q + 1) * R :=
    abs_integral_remFn_le hη hξ h hk q hb (hCj (q + 1)).2 hM' hε0 hX0 hXb.le
  have hexpX : exp (-X / 2) ≤ E * N ^ (-(L : ℝ)) := by
    rw [hXeq, hE]
    exact exp_neg_half_scaled_le k L hk hb hN0
  have hεL : ε ^ (h + 1) * ε ^ (q + 1) ≤ N ^ (-(L : ℝ)) := by
    rw [← pow_add, hε, scaleEps_pow_eq_rpow hN0]
    refine Real.rpow_le_rpow_of_exponent_le hN ?_
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have : (2 * k * L : ℝ) ≤ q + 1 + h := by exact_mod_cast hqL
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hεh : ε ^ (h + 1) ≤ 1 := pow_le_one₀ hε0.le hε1
  have hR0 : 0 ≤ R := by
    rw [hR]
    have := (hCj (q + 1)).1
    have := kernelConst_nonneg (h + 2 * q + 2) M
    have : 0 ≤ ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun x _ => (exp_pos _).le
    positivity
  rw [hdiff, abs_mul, abs_of_pos (pow_pos hε0 _)]
  calc ε ^ (h + 1) * |(∑ j ∈ Finset.range (q + 1),
        -(ε ^ j / (j.factorial : ℝ) * ∫ x in Ioi X, jetInt η ξ h k j x)) +
        ∫ x in (0 : ℝ)..X, remFn η ξ h k q ε x|
      ≤ ε ^ (h + 1) * (T * exp (-X / 2) + ε ^ (q + 1) * R) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hsum hrem)) (pow_pos hε0 _).le
    _ = ε ^ (h + 1) * (T * exp (-X / 2)) + ε ^ (h + 1) * ε ^ (q + 1) * R := by ring
    _ ≤ 1 * (T * (E * N ^ (-(L : ℝ)))) + N ^ (-(L : ℝ)) * R := by
        gcongr
    _ = (T * E + R) * N ^ (-(L : ℝ)) := by ring

/-! ### Compatibility and the first jets -/

/-- At zero field the coefficients are the population coefficients `η^{(j)}(0) Γ(μ_j)/(j!·2k)`
of `oneDim_smooth` (at `β = 1`). -/
theorem empOneDimCoeff_zero_field (hη : ContDiff ℝ ∞ η) (h : ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    empOneDimCoeff η (fun _ => 0) h k j = oneDimCoeff η 1 k h j := by
  unfold empOneDimCoeff oneDimCoeff
  have hμ : 0 < lam k (j + h) := lam_pos hk _
  simp only [fluctuation_zero 1 _ one_pos hμ, Real.one_rpow, one_mul]
  have hcd : ContDiffAt ℝ (↑j) η 0 := (hη.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [show (fun v => η v * Real.Gamma (lam k (j + h))) =
      fun v => Real.Gamma (lam k (j + h)) * η v from funext fun v => mul_comm _ _,
    iteratedDeriv_const_mul _ hcd]
  ring

/-- The leading coefficient: `C_0 = η(0) S_{μ_0}(ξ(0))/2k`, the one-dimensional rank-2 limit. -/
theorem empOneDimCoeff_zero (h : ℕ) (k : ℕ) :
    empOneDimCoeff η ξ h k 0 = η 0 * fluctuation 1 (lam k h) (ξ 0) / (2 * k) := by
  unfold empOneDimCoeff
  simp [iteratedDeriv_zero]

/-- The first correction exhibits the ladder: with `μ = μ_1 = (h+2)/2k`,
`C_1 = (η'(0) S_μ(ξ(0)) + η(0) ξ'(0) S_{μ+1/2}(ξ(0))) / 2k`. -/
theorem empOneDimCoeff_one (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    empOneDimCoeff η ξ h k 1 = (deriv η 0 * fluctuation 1 (lam k (1 + h)) (ξ 0) +
      η 0 * deriv ξ 0 * fluctuation 1 (lam k (1 + h) + 1 / 2) (ξ 0)) / (2 * k) := by
  unfold empOneDimCoeff
  have hμ : 0 < lam k (1 + h) := lam_pos hk _
  have hd : HasDerivAt (fun v => η v * fluctuation 1 (lam k (1 + h)) (ξ v))
      (deriv η 0 * fluctuation 1 (lam k (1 + h)) (ξ 0) +
        η 0 * (1 * fluctuation 1 (lam k (1 + h) + 1 / 2) (ξ 0) * deriv ξ 0)) 0 :=
    ((hη.differentiable (by simp)) 0).hasDerivAt.mul
      ((hasDerivAt_fluctuation 1 _ one_pos hμ (ξ 0)).comp 0
        ((hξ.differentiable (by simp)) 0).hasDerivAt)
  rw [iteratedDeriv_one, hd.deriv]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul]
  ring

end SmoothEngine

end Grammar
