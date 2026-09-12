/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.OneDimCoordFreeInstance
import Grammar.CoordFreeLeadingTerm

/-!
# Explicit coordinate-free coefficients on the line (CCCXII)

Consult #94 H — the regression test of the whole pipeline against the Gaussian moments. For the
one-dimensional instance of CCCVII (`∫_0^ρ P(x) e^{−nx²} dx`, `P = ∑_m f_m x^m`) the coordinate-free
coefficients are computed in closed form through the kernels of CCCI–CCCII:

* in one variable the state-density representation is the single term `(w+1, 0, 1)`, the
  zero-fluctuation moment is `Γ(μ)` (`fluctMoment_one_zero`), so the monomial kernel is
  `monoKernel_{μ,0}(m) = [μ = (m+1)/2] · Γ(μ)/2` (`monoKernel_oneDim`) and the box side cancels
  exactly in the box kernel (`boxSpectralKernel_oneDim`);
* ★★ `expansionCoefficient_oneDim`: the coordinate-free coefficient at `n^{−(m+1)/2}` is
  `Γ((m+1)/2)/2 · f_m` — **the Gaussian half-moment `∫_0^∞ u^m e^{−u²} du = Γ((m+1)/2)/2` times the
  Taylor coefficient**, the classical Laplace/Watson expansion; every other coefficient vanishes
  (`expansionCoefficient_oneDim_eq_zero`, `expansionCoefficient_oneDim_eq_zero_of_pos`);
* for `P = 1 + a x²`: the coefficients `√π/2` at `n^{−1/2}` and `a√π/4` at `n^{−3/2}`
  (`coeff_quad_half`, `coeff_quad_three_half`), and the leading term
  `∫_0^ρ (1 + a x²) e^{−nx²} dx · n^{1/2} → √π/2` (`hasLeadingTerm_quad`) from CCCX.

These are statements about the exact coefficients of the certified expansion, obtained through
the strata/normal-tensor representation — not a separate asymptotic analysis; the finite endpoint
`ρ` contributes only to the `o(n^{−A})` remainders.
-/

open Set Filter Topology MeasureTheory Asymptotics

namespace Grammar

namespace OneDim

open CoeffFamily MonoRep

/-! ### The one-variable kernels -/

theorem fluctMoment_one_zero {μ : ℝ} (hμ : 0 < μ) : fluctMoment 1 0 0 μ 0 = Real.Gamma μ := by
  unfold fluctMoment phaseKernel
  rw [Real.Gamma_eq_integral hμ]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [pow_zero, mul_one, one_mul, mul_zero, add_zero]
  ring

theorem coeffAt_single (w μ : ℝ) (q : ℕ) :
    PowLogRep.coeffAt [(w + 1, 0, 1)] μ q = if w + 1 = μ ∧ 0 = q then 1 else 0 := by
  rw [PowLogRep.coeffAt_cons, PowLogRep.coeffAt_nil, add_zero]

theorem monoWeights_oneDim (γ : Fin 1 → ℕ) :
    monoWeights ((fun _ => 0 : Fin 1 → ℕ) + γ) (fun _ => 1) 0 + 1 = ((γ 0 : ℝ) + 1) / 2 := by
  unfold monoWeights
  simp only [Pi.add_apply, zero_add, Nat.cast_one, mul_one]
  ring

/-- **The one-variable monomial kernel**: `monoKernel_{μ,0}(m) = [μ = (m+1)/2] · Γ(μ)/2`. -/
theorem monoKernel_oneDim (γ : Fin 1 → ℕ) {μ : ℝ} (hμ : 0 < μ) :
    monoKernel 0 (fun _ => 0) (fun _ => 1) 1 μ 0 γ =
      if μ = ((γ 0 : ℝ) + 1) / 2 then Real.Gamma μ / 2 else 0 := by
  unfold monoKernel
  rw [show Finset.Ico 0 (0 + 1) = {0} by decide, Finset.sum_singleton, stateDensityRep_zero,
    coeffAt_single, monoWeights_oneDim, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    fluctMoment_one_zero hμ, Fin.prod_univ_one]
  by_cases h : μ = ((γ 0 : ℝ) + 1) / 2
  · rw [if_pos h, if_pos ⟨h.symm, rfl⟩]
    push_cast
    ring
  · rw [if_neg h, if_neg fun hc => h hc.1.symm]
    ring

theorem monoKernel_oneDim_eq_zero (γ : Fin 1 → ℕ) {μ : ℝ} (hne : ∀ m : ℕ, μ ≠ ((m : ℝ) + 1) / 2) :
    monoKernel 0 (fun _ => 0) (fun _ => 1) 1 μ 0 γ = 0 := by
  refine monoKernel_eq_zero_of_not_candidate 0 _ _ 1 μ 0 ?_ γ
  rintro ⟨i, r, hr⟩
  refine hne r ?_
  rw [hr]
  simp

/-- **The one-variable box kernel**: the box side cancels, `K^b_{μ,0}(m) = [μ = (m+1)/2] Γ(μ)/2`. -/
theorem boxSpectralKernel_oneDim {b : ℝ} (hb : 0 < b) (γ : Fin 1 → ℕ) {μ : ℝ} (hμ : 0 < μ) :
    boxSpectralKernel 0 (fun _ => 0) (fun _ => 1) 1 b μ 0 γ =
      if μ = ((γ 0 : ℝ) + 1) / 2 then Real.Gamma μ / 2 else 0 := by
  unfold boxSpectralKernel
  have hs0 : (∑ _x : Fin (0 + 1), (0 : ℕ)) = 0 := by simp
  have hs1 : (∑ _x : Fin (0 + 1), (1 : ℕ)) = 1 := by simp
  have hsγ : (∑ i : Fin (0 + 1), γ i) = γ 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rw [hs0, hs1, hsγ, mul_one, show Finset.Ico 0 (0 + 1) = {0} by decide,
    Finset.sum_singleton, monoKernel_oneDim γ hμ, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    pow_zero, mul_one, mul_one]
  by_cases h : μ = ((γ 0 : ℝ) + 1) / 2
  · rw [if_pos h]
    have h1 : ((b ^ (2 * 1) : ℝ)) ^ (-μ) = b ^ (-((γ 0 : ℝ) + 1)) := by
      rw [h, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1
      push_cast
      ring
    have h2 : (b : ℝ) ^ (0 + 1) * b ^ (-((γ 0 : ℝ) + 1)) * b ^ (γ 0) = 1 := by
      rw [← Real.rpow_natCast b (0 + 1), ← Real.rpow_natCast b (γ 0), ← Real.rpow_add hb,
        ← Real.rpow_add hb]
      push_cast
      rw [show (1 : ℝ) + -((γ 0 : ℝ) + 1) + γ 0 = 0 by ring, Real.rpow_zero]
    rw [h1]
    calc b ^ (0 + 1) * b ^ (-((γ 0 : ℝ) + 1)) * (b ^ γ 0 * (Real.Gamma μ / 2))
        = (b ^ (0 + 1) * b ^ (-((γ 0 : ℝ) + 1)) * b ^ γ 0) * (Real.Gamma μ / 2) := by ring
      _ = Real.Gamma μ / 2 := by rw [h2, one_mul]
  · rw [if_neg h]
    ring

theorem boxSpectralKernel_oneDim_eq_zero {b : ℝ} (γ : Fin 1 → ℕ) {μ : ℝ}
    (hne : ∀ m : ℕ, μ ≠ ((m : ℝ) + 1) / 2) :
    boxSpectralKernel 0 (fun _ => 0) (fun _ => 1) 1 b μ 0 γ = 0 := by
  unfold boxSpectralKernel
  rw [show Finset.Ico 0 (0 + 1) = {0} by decide, Finset.sum_singleton,
    monoKernel_oneDim_eq_zero γ hne]
  ring

/-! ### The box coefficients of a polynomial -/

section Poly

variable (f : CoeffFamily 1) {supp : Finset (Fin 1 → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0) {b : ℝ}
  (hb : 0 < b)
include hf hb

/-- **The canonical box coefficient of a polynomial on the line** at `n^{−(m+1)/2}` is
`Γ((m+1)/2)/2 · f_m`. -/
theorem boxCoeff_oneDim (m : ℕ) :
    boxCoeff 0 (fun _ => 0) (fun _ => 1) 1 b 0 f (((m : ℝ) + 1) / 2) 0 =
      Real.Gamma (((m : ℝ) + 1) / 2) / 2 * f (fun _ => m) := by
  have hμ : (0 : ℝ) < ((m : ℝ) + 1) / 2 := by positivity
  rw [boxCoeff_zero_eq_tsum 0 _ _ 1 _ _ (fun _ => one_pos) one_pos hb
    (absSummableAt_of_support f hf b)]
  rw [tsum_eq_single (fun _ => m)]
  · rw [boxSpectralKernel_oneDim hb _ hμ, if_pos rfl]
    ring
  · intro γ hγ
    rw [boxSpectralKernel_oneDim hb γ hμ, if_neg, mul_zero]
    intro h
    apply hγ
    funext i
    rw [Fin.fin_one_eq_zero i]
    have : (m : ℝ) = γ 0 := by linarith
    exact (Nat.cast_injective this).symm

omit hb in
theorem boxCoeff_oneDim_eq_zero {μ : ℝ} (hne : ∀ m : ℕ, μ ≠ ((m : ℝ) + 1) / 2) (hb : 0 < b) :
    boxCoeff 0 (fun _ => 0) (fun _ => 1) 1 b 0 f μ 0 = 0 := by
  rw [boxCoeff_zero_eq_tsum 0 _ _ 1 _ _ (fun _ => one_pos) one_pos hb
    (absSummableAt_of_support f hf b)]
  rw [show (fun γ => f γ * boxSpectralKernel 0 (fun _ => 0) (fun _ => 1) 1 b μ 0 γ) =
    fun _ => (0 : ℝ) from funext fun γ => by rw [boxSpectralKernel_oneDim_eq_zero γ hne, mul_zero]]
  exact tsum_zero

/-! ### The coordinate-free coefficients of the instance -/

variable (ρ : ℝ) (hbρ : b ≤ ρ)
include hbρ

theorem expansionCoefficient_eq_boxCoeff (μ : ℝ) (j : ℕ) :
    normalData.expansionCoefficient (certificate f hf ρ b hb hbρ).stratumMeasure
        (coeffCertificate f hf ρ b hb hbρ).field (poly f) ⟨μ, j⟩ =
      boxCoeff 0 (fun _ => 0) (fun _ => 1) 1 b 0 f μ j := by
  rw [(coeffCertificate f hf ρ b hb hbρ).expansionCoefficient_eq_gCoeff]
  unfold gCoeff
  have hM : Subsingleton (Fin (certificate f hf ρ b hb hbρ).M) :=
    Fin.subsingleton_iff_le_one.2 (by change 1 ≤ 1; exact le_rfl)
  rw [Fintype.sum_subsingleton _ (⟨0, by change 0 < 1; exact one_pos⟩ :
    Fin (certificate f hf ρ b hb hbρ).M)]
  change ∫ v, dataBoxCoeff 0 (fun _ => 0) (fun _ => 1) 1 b ((chart f hf ρ b hb hbρ).x v) μ j
    ∂(Measure.dirac basePt) = _
  rw [integral_dirac]
  change dataBoxCoeff 0 (fun _ => 0) (fun _ => 1) 1 b (datum f hf b hb) μ j = _
  unfold dataBoxCoeff
  rw [toEta_datum]
  unfold datum
  rw [toXi_ofFamilies]

/-- ★★ **The coordinate-free coefficients of `∫_0^ρ P(x) e^{−nx²} dx` in closed form**: at
`n^{−(m+1)/2}` the coefficient is the Gaussian half-moment times the Taylor coefficient,
`Γ((m+1)/2)/2 · f_m`. -/
theorem expansionCoefficient_oneDim (m : ℕ) :
    normalData.expansionCoefficient (certificate f hf ρ b hb hbρ).stratumMeasure
        (coeffCertificate f hf ρ b hb hbρ).field (poly f) ⟨((m : ℝ) + 1) / 2, 0⟩ =
      Real.Gamma (((m : ℝ) + 1) / 2) / 2 * f (fun _ => m) := by
  rw [expansionCoefficient_eq_boxCoeff f hf hb ρ hbρ, boxCoeff_oneDim f hf hb m]

/-- Off the half-integers the coefficients vanish. -/
theorem expansionCoefficient_oneDim_eq_zero {μ : ℝ} (hne : ∀ m : ℕ, μ ≠ ((m : ℝ) + 1) / 2) :
    normalData.expansionCoefficient (certificate f hf ρ b hb hbρ).stratumMeasure
        (coeffCertificate f hf ρ b hb hbρ).field (poly f) ⟨μ, 0⟩ = 0 := by
  rw [expansionCoefficient_eq_boxCoeff f hf hb ρ hbρ, boxCoeff_oneDim_eq_zero f hf hne hb]

/-- No logarithms: the coefficients of positive log degree vanish. -/
theorem expansionCoefficient_oneDim_eq_zero_of_pos (μ : ℝ) {j : ℕ} (hj : 0 < j) :
    normalData.expansionCoefficient (certificate f hf ρ b hb hbρ).stratumMeasure
        (coeffCertificate f hf ρ b hb hbρ).field (poly f) ⟨μ, j⟩ = 0 := by
  rw [(coeffCertificate f hf ρ b hb hbρ).expansionCoefficient_eq_gCoeff]
  exact gCoeff_eq_zero_of_lt _ _ _ _ _ _ (by rwa [commonD_certificate])

end Poly

/-! ### The quadratic observable `1 + a x²` -/

section Quad

/-- The coefficient family of `1 + a x²`. -/
noncomputable def quadFamily (a : ℝ) : CoeffFamily 1 :=
  fun γ => if γ 0 = 0 then 1 else if γ 0 = 2 then a else 0

theorem quadFamily_support (a : ℝ) :
    ∀ γ ∉ ({fun _ => 0, fun _ => 2} : Finset (Fin 1 → ℕ)), quadFamily a γ = 0 := by
  intro γ hγ
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
  unfold quadFamily
  rw [if_neg, if_neg]
  · intro h
    exact hγ.2 (funext fun i => by rw [Fin.fin_one_eq_zero i, h])
  · intro h
    exact hγ.1 (funext fun i => by rw [Fin.fin_one_eq_zero i, h])

theorem poly_quadFamily (a : ℝ) (u : Space) : poly (quadFamily a) u = 1 + a * u 0 ^ 2 := by
  rw [poly_eq_sum _ (quadFamily_support a)]
  rw [Finset.sum_pair]
  · simp [quadFamily, mono_eq_pow]
  · intro h
    have := congrFun h 0
    simp at this

variable (a : ℝ) {ρ b : ℝ} (hb : 0 < b) (hbρ : b ≤ ρ)
include hb hbρ

/-- The coefficient of `n^{−1/2}` is `√π/2`. -/
theorem coeff_quad_half :
    normalData.expansionCoefficient
        (certificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).stratumMeasure
        (coeffCertificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).field
        (poly (quadFamily a)) ⟨1 / 2, 0⟩ = Real.sqrt Real.pi / 2 := by
  have h := expansionCoefficient_oneDim (quadFamily a) (quadFamily_support a) hb ρ hbρ 0
  rw [show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num] at h
  rw [h, Real.Gamma_one_half_eq]
  simp [quadFamily]

/-- The coefficient of `n^{−3/2}` is `a√π/4`. -/
theorem coeff_quad_three_half :
    normalData.expansionCoefficient
        (certificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).stratumMeasure
        (coeffCertificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).field
        (poly (quadFamily a)) ⟨3 / 2, 0⟩ = a * Real.sqrt Real.pi / 4 := by
  have h := expansionCoefficient_oneDim (quadFamily a) (quadFamily_support a) hb ρ hbρ 2
  rw [show (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 by norm_num] at h
  rw [h]
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have := Real.Gamma_nat_add_half 1
    rw [show ((1 : ℕ) : ℝ) + 1 / 2 = 3 / 2 by norm_num] at this
    rw [this]
    norm_num
  rw [hg]
  simp [quadFamily]
  ring

/-- The coefficient at the exponent `0` vanishes. -/
theorem coeff_quad_zero :
    normalData.expansionCoefficient
        (certificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).stratumMeasure
        (coeffCertificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ).field
        (poly (quadFamily a)) ⟨0, 0⟩ = 0 :=
  expansionCoefficient_oneDim_eq_zero (quadFamily a) (quadFamily_support a) hb ρ hbρ fun m h => by
    have : (0 : ℝ) < ((m : ℝ) + 1) / 2 := by positivity
    linarith

/-- ★★ **The leading term through the coordinate-free machinery**:
`∫_0^ρ (1 + a x²) e^{−nx²} dx / n^{−1/2} → √π/2`. -/
theorem hasLeadingTerm_quad :
    HasLeadingTerm (globalLaplace (region ρ) phase fun w => poly (quadFamily a) w * 1)
      (Real.sqrt Real.pi / 2) (1 / 2) 0 := by
  rw [← coeff_quad_half a hb hbρ]
  refine ResolvedCertificate.CoefficientCertificate.hasLeadingTerm_expansionCoefficient
    (coeffCertificate (quadFamily a) (quadFamily_support a) ρ b hb hbρ) measurable_phase
    measurable_const (fun _ => zero_le_one) (continuous_poly _ (quadFamily_support a)).measurable
    ⟨1 / 2, 0⟩ ?_ ?_
  · refine ⟨⟨1, ?_⟩, le_rfl⟩
    rw [commonQ_certificate]
    norm_num
  · intro q' hq' hpre
    obtain ⟨⟨m, hm⟩, hj⟩ := hq'
    rw [commonQ_certificate] at hm
    rw [commonD_certificate] at hj
    have hj0 : q'.logDegree = 0 := Nat.le_zero.1 hj
    rcases hpre with hlt | ⟨heq, hgt⟩
    · -- exponent `m/2 < 1/2`, so `m = 0`
      change q'.exponent < 1 / 2 at hlt
      have hm0 : m = 0 := by
        rw [hm] at hlt
        have : (m : ℝ) < 1 := by
          push_cast at hlt
          linarith
        exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
      subst hm0
      have hq0 : q' = ⟨0, 0⟩ := by
        cases q' with
        | mk e j => simp only at hm hj0; rw [hm, hj0]; simp
      rw [hq0]
      exact coeff_quad_zero a hb hbρ
    · change 0 < q'.logDegree at hgt
      omega

/-- The integral is asymptotically `(√π/2) n^{−1/2}`. -/
theorem isEquivalent_quad :
    (globalLaplace (region ρ) phase fun w => poly (quadFamily a) w * 1) ~[atTop] fun N =>
      Real.sqrt Real.pi / 2 * powLogScale (1 / 2) 0 N :=
  (hasLeadingTerm_quad a hb hbρ).isEquivalent (by positivity)

end Quad

end OneDim

end Grammar
