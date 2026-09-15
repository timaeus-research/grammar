/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialExplicitConstant

/-!
# Regression: the explicit leading insertion functional of a mixed monomial phase

For `K = ∏ x_i^{2k_i}` with all `k_i > 0` and a smooth compactly supported prior `φ` supported in
the symmetric box, the symmetric-box headline at zero phase gives, for EVERY smooth insertion `f`,
the explicit normalised limit
`N^{λ*} (log N)^{−(m*−1)} ∫ φ f e^{−NK} → Σ_σ amplitudeCoeff 0 k λ* 1 ((φ f) ∘ reflect σ)`,
a sum over the `2^d` sign patterns of the face-supported leading functional
`Γ(λ*)/((m*−1)! ∏_{k_i = k_max} 2k_i) · ∫_{(0,1]^d} (φf)(faceProj u) ∏_{k_i < k_max} u_i^{−2k_iλ*}`
(`monomial_tendsto_insertion`). Uniqueness of limits identifies the abstract coefficient
`𝒯^U_{λ*,m*−1}[f ∘ π]` with this explicit value (`monomial_coeff_comp_gv_eq`), and hence the
integral of every admissible insertion against the leading stratum measure
(`monomial_integral_extremalStratumMeasure_eq`): the positive-dimensional leading measure of a
mixed monomial phase is the weighted restriction of the prior to the coordinate subspace
`{x_i = 0 : k_i = k_max}`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing

namespace Grammar

namespace SmoothEngine

section Mixed

variable {m : ℕ} (k : Fin (m + 1) → ℕ) (hk : ∀ i, 0 < k i)

theorem ratioExp_zero_eq (i : Fin (m + 1)) :
    ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) k i = 1 / (2 * (k i : ℝ)) := by
  simp [ratioExp]

include hk in
theorem ratioExp_zero_eq_lamStar_iff (i : Fin (m + 1)) :
    ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) k i = lamStar k ↔ k i = kmax k := by
  have hki : (0 : ℝ) < k i := Nat.cast_pos.2 (hk i)
  have hkm : (0 : ℝ) < kmax k := Nat.cast_pos.2 (kmax_pos k ⟨0, hk 0⟩)
  rw [ratioExp_zero_eq, lamStar]
  constructor
  · intro h
    have h' : (k i : ℝ) = kmax k := by
      field_simp at h
      linarith
    exact_mod_cast h'
  · intro h
    rw [h]

include hk in
theorem multCount_zero_eq_mstar :
    multCount (ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) k) (lamStar k) = mstar k := by
  unfold multCount mstar
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ratioExp_zero_eq_lamStar_iff k hk i]

include hk in
theorem lamStar_le_ratioExp (i : Fin (m + 1)) :
    lamStar k ≤ ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) k i := by
  rw [ratioExp_zero_eq, lamStar]
  have hki : (0 : ℝ) < k i := Nat.cast_pos.2 (hk i)
  have hle : (k i : ℝ) ≤ kmax k := Nat.cast_le.2 (le_kmax k i)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

include hk in
theorem exists_ratioExp_eq_lamStar :
    ∃ i, ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) k i = lamStar k := by
  obtain ⟨i, hi⟩ := exists_eq_kmax k
  exact ⟨i, (ratioExp_zero_eq_lamStar_iff k hk i).2 hi⟩

/-- ★ **The explicit leading insertion functional** of the monomial phase: the sum over the `2^d`
sign patterns of the face-supported amplitude coefficient at zero Jacobian exponents. -/
noncomputable def monomialInsertion (η : (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∑ σ : Fin (m + 1) → Bool, amplitudeCoeff (fun _ => 0) k (lamStar k) 1 fun u => η (reflect σ u)

variable {prior : (Fin (m + 1) → ℝ) → ℝ} (hps : ContDiff ℝ ∞ prior)
  (hbox : tsupport prior ⊆ symBox (m + 1))

include hk hps hbox in
/-- ★★★ **The explicit normalised limit for every smooth insertion** (symmetric-box headline at
zero phase, square-parameter transport). -/
theorem monomial_tendsto_insertion {f : (Fin (m + 1) → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    Tendsto (normalised (lamStar k) (mstar k - 1) (partitionObs (monoPhase k) prior f)) atTop
      (𝓝 (monomialInsertion k fun x => prior x * f x)) := by
  have hlam : 0 < lamStar k := by
    unfold lamStar
    have := kmax_pos k ⟨0, hk 0⟩
    positivity
  have hT := headline_symmetric_abs_phase_leading m (fun _ => 0) k hk (lamStar k) 1 hlam one_pos
    (fun i => by
      have := lamStar_le_ratioExp k hk i
      rw [ratioExp_zero_eq] at this
      simpa using this)
    (by
      obtain ⟨i, hi⟩ := exists_ratioExp_eq_lamStar k hk
      rw [ratioExp_zero_eq] at hi
      exact ⟨i, by simpa using hi⟩)
    (fun _ => 0) (fun x => prior x * f x) continuous_const (hps.continuous.mul hf.continuous)
  rw [multCount_zero_eq_mstar k hk] at hT
  have hcoef : ∀ σ : Fin (m + 1) → Bool,
      phaseCoeff (fun _ : Fin (m + 1) => (0 : ℕ)) k (lamStar k) 1
        (fun u => phaseSign k σ * (fun _ : Fin (m + 1) → ℝ => (0 : ℝ)) u)
        (fun u => (fun x => prior x * f x) (reflect σ u)) =
      2 ^ (mstar k - 1) * amplitudeCoeff (fun _ => 0) k (lamStar k) 1
        (fun u => prior (reflect σ u) * f (reflect σ u)) := by
    intro σ
    have h := phaseCoeff_zero_phase (fun _ : Fin (m + 1) => (0 : ℕ)) k (lamStar k) 1 hlam one_pos
      (fun u => prior (reflect σ u) * f (reflect σ u))
    rw [multCount_zero_eq_mstar k hk] at h
    simp only [mul_zero] at h ⊢
    exact h
  simp only [hcoef, ← Finset.mul_sum] at hT
  have hsqrt : Tendsto (fun M : ℝ => Real.sqrt M) atTop atTop := by
    have := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    refine this.congr' (Eventually.of_forall fun M => ?_)
    exact (Real.sqrt_eq_rpow M).symm
  have hcomp := (hT.comp hsqrt).div_const ((2 : ℝ) ^ (mstar k - 1))
  have h2pos : (0 : ℝ) < 2 ^ (mstar k - 1) := by positivity
  rw [mul_div_cancel_left₀ _ h2pos.ne'] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with M hM
  have hM0 : 0 < M := by linarith
  have hlog : 0 < Real.log M := Real.log_pos hM
  have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0.le
  have hsqpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  simp only [Function.comp_apply]
  unfold normalised partitionObs
  have hint : ∫ x in symBox (m + 1), prior x * f x * ((∏ i, |x i| ^ (0 : ℕ)) *
      Real.exp (-(1 * Real.sqrt M ^ 2 * ∏ i, x i ^ (2 * k i)) +
        1 * (Real.sqrt M * ∏ i, x i ^ k i) * 0)) =
      ∫ y, prior y * f y * Real.exp (-M * monoPhase k y) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)]
    · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [pow_zero, Finset.prod_const_one, one_mul, mul_zero, add_zero, hsq, monoPhase]
      ring_nf
    · rw [image_eq_zero_of_notMem_tsupport fun h => hy (hbox h), zero_mul, zero_mul]
  rw [hint, Real.log_sqrt hM0.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hM0.le,
    show (1 / 2 : ℝ) * (-(2 * lamStar k)) = -lamStar k by ring, Real.rpow_neg hM0.le, div_pow]
  field_simp

variable (W : TopologicalSpace.Opens (Fin (m + 1) → ℝ)) (hp0 : ∀ y, 0 ≤ prior y)
  (hpc : HasCompactSupport prior) (hpW : tsupport prior ⊆ (W : Set (Fin (m + 1) → ℝ)))

include hk hbox in
/-- ★★★ **The abstract leading coefficient of every pulled-back insertion is the explicit
functional**: `𝒯^U_{λ*,m*−1}[f ∘ π] = monomialInsertion k (φ f)`. -/
theorem monomial_coeff_comp_gv_eq
    (Y : ResolvedCoreTransport (monomialData k W hps hp0 hpc hpW).R
      (monomialData k W hps hp0 hpc hpW).hKc prior) {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ((monomialData k W hps hp0 hpc hpW).withF
      (fun P => f ((monomialData k W hps hp0 hpc hpW).R.gv P))
      ((monomialData k W hps hp0 hpc hpW).contMDiff_comp_gv hf)).coeff Y (lamStar k)
        (mstar k - 1) =
      monomialInsertion k fun x => prior x * f x := by
  have h1 := (monomialData k W hps hp0 hpc hpW).tendsto_normalised_Z_of_extremalData Y
    (isExtremalData_monomial k W hps hp0 hpc hpW ⟨0, hk 0⟩)
    ((monomialData k W hps hp0 hpc hpW).contMDiff_comp_gv hf)
  have h1' : Tendsto (normalised (lamStar k) (mstar k - 1) (partitionObs (monoPhase k) prior f))
      atTop (𝓝 (((monomialData k W hps hp0 hpc hpW).withF
        (fun P => f ((monomialData k W hps hp0 hpc hpW).R.gv P))
        ((monomialData k W hps hp0 hpc hpW).contMDiff_comp_gv hf)).coeff Y (lamStar k)
          (mstar k - 1))) := by
    refine h1.congr fun N => ?_
    unfold normalised
    rw [(monomialData k W hps hp0 hpc hpW).Z_withF_comp_gv hf N]
    rfl
  exact tendsto_nhds_unique h1' (monomial_tendsto_insertion k hk hps hbox hf)

include hk hbox in
/-- ★★★ **The leading stratum measure of a mixed monomial phase, on admissible insertions**: for
`f ∘ π` vanishing near `D_{m*+1}`, `∫ f ∘ π dν^{λ*}_{m*} = monomialInsertion k (φ f)` — the
weighted restriction of `φ f` to the coordinate subspace `{x_i = 0 : k_i = k_max}`. -/
theorem monomial_integral_extremalStratumMeasure_eq
    (Y : ResolvedCoreTransport (monomialData k W hps hp0 hpc hpW).R
      (monomialData k W hps hp0 hpc hpW).hKc prior) {f : (Fin (m + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ᶠ P in 𝓝ˢ ((monomialData k W hps hp0 hpc hpW).deepZeroFibre (mstar k)),
      f ((monomialData k W hps hp0 hpc hpW).R.gv P) = 0) :
    ∫ x, f ((monomialData k W hps hp0 hpc hpW).R.gv x.1)
        ∂((monomialData k W hps hp0 hpc hpW).extremalStratumMeasure Y
          (isExtremalData_monomial k W hps hp0 hpc hpW ⟨0, hk 0⟩) (one_le_mstar k ⟨0, hk 0⟩)) =
      monomialInsertion k fun x => prior x * f x := by
  unfold ResolvedData.extremalStratumMeasure
  rw [← (monomialData k W hps hp0 hpc hpW).coeff_withF_eq_integral_stratumMeasure Y
    (one_le_mstar k ⟨0, hk 0⟩) _ ((monomialData k W hps hp0 hpc hpW).contMDiff_comp_gv hf) h0]
  exact monomial_coeff_comp_gv_eq k hk hps hbox W hp0 hpc hpW Y hf

/-! ### Equal exponents: the closed form -/

theorem ratioExp_equal (κ : ℕ) (hκ : 0 < κ) (i : Fin (m + 1)) :
    ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) (equalExp (m + 1) κ) i =
      lamStar (equalExp (m + 1) κ) :=
  (ratioExp_zero_eq_lamStar_iff (equalExp (m + 1) κ) (fun _ => hκ) i).2 (kmax_equal κ).symm

/-- ★★ **The equal-exponent closed form**: `monomialInsertion (κ,…,κ) η = 2^d Γ(1/(2κ)) η(0) /
((d−1)! (2κ)^d)`, `d = m + 1`. -/
theorem monomialInsertion_equal (κ : ℕ) (hκ : 0 < κ) (η : (Fin (m + 1) → ℝ) → ℝ) :
    monomialInsertion (equalExp (m + 1) κ) η =
      2 ^ (m + 1) *
        (Real.Gamma (1 / (2 * (κ : ℝ))) / ((m.factorial : ℝ) * (2 * (κ : ℝ)) ^ (m + 1))) * η 0 := by
  have hratio := ratioExp_equal (m := m) κ hκ
  have hl : lamStar (equalExp (m + 1) κ) = 1 / (2 * (κ : ℝ)) := by
    unfold lamStar
    rw [kmax_equal]
  have hmult : multCount (ratioExp (fun _ : Fin (m + 1) => (0 : ℕ)) (equalExp (m + 1) κ))
      (lamStar (equalExp (m + 1) κ)) = m + 1 := by
    unfold multCount
    simp [hratio]
  have hπ : faceProj (fun _ : Fin (m + 1) => (0 : ℕ)) (equalExp (m + 1) κ)
      (lamStar (equalExp (m + 1) κ)) = fun _ => 0 := by
    funext u i
    simp [faceProj, hratio]
  have hw : residualWeight (fun _ : Fin (m + 1) => (0 : ℕ)) (equalExp (m + 1) κ)
      (lamStar (equalExp (m + 1) κ)) = fun _ => 1 := by
    funext u
    unfold residualWeight
    simp [hratio]
  have hamp : ∀ σ : Fin (m + 1) → Bool,
      amplitudeCoeff (fun _ : Fin (m + 1) => (0 : ℕ)) (equalExp (m + 1) κ)
        (lamStar (equalExp (m + 1) κ)) 1 (fun u => η (reflect σ u)) =
      Real.Gamma (1 / (2 * (κ : ℝ))) / ((m.factorial : ℝ) * (2 * (κ : ℝ)) ^ (m + 1)) * η 0 := by
    intro σ
    unfold amplitudeCoeff faceLeadConst
    rw [hmult, Nat.add_sub_cancel, hπ, hw]
    have hr : reflect σ (0 : Fin (m + 1) → ℝ) = 0 := by
      funext i
      simp [reflect]
    simp only [hr, mul_one, Real.one_rpow, hratio, if_true, equalExp]
    rw [setIntegral_const, measureReal_def, volume_unitBox, ENNReal.toReal_one, one_smul, hl,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : ((2 : ℝ) * κ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp
    rw [one_div, inv_pow]
    field_simp
  unfold monomialInsertion
  simp only [hamp, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Sanity: for `x²y²` the closed form is `√π η(0)`, agreeing with `x2y2_coeff_one_eq`. -/
theorem monomialInsertion_x2y2 (η : (Fin 2 → ℝ) → ℝ) :
    monomialInsertion (equalExp 2 1) η = Real.sqrt Real.pi * η 0 := by
  rw [monomialInsertion_equal (m := 1) 1 one_pos η]
  simp only [Nat.cast_one, mul_one, Nat.factorial_one]
  rw [Real.Gamma_one_half_eq]
  field_simp

end Mixed

end SmoothEngine

end Grammar
