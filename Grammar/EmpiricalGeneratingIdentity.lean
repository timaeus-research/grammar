/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalTailJets

/-!
# The all-orders generating identity, chart-wise (§20, coordinate-free programme)

For smooth `η, ζ` on the unit box the canonical empirical coefficients of the exponential field
family are the exponential generating series of *population* coefficients with the monomial
insertions `η ζ^r` at the half-integer shifted exponents:

★★★ `hasSum_empCoeff_population`:
`Σ_{r ≥ 0} (1/r!) · empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q = empCoeff η ζ h k μ q`
(unconditionally convergent), for every `μ ∈ Q⁻¹ℕ` and `q ≤ d − 1`; equivalently with the
insertion `η (u^k ζ)^r` and the unshifted monomial `h` (`hasSum_empCoeff_population_mono`).

Route (truncation, no series/integral interchange): `fieldFam = Σ_{r<R} (1/r!) expTermFam r +
tailFam R` pointwise; the family coefficients are linear (by uniqueness of cutoff expansions,
`empCoeffAtDepthFam_add/const_mul`) and `O(C)` for a family with jet bound `C`
(`exists_abs_empCoeffAtDepthFam_single_le`); the tails have jet bounds `K₀ (1/2)^R`
(`exists_famJetBound_tailFam`), so the tail coefficient tends to zero and the terms are
absolutely summable.  Each term is identified with a shifted population coefficient by
`empCoeffAtDepthFam_expTermFam_eq`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)

theorem expTermFam_inv_factorial_eq_tailFam_sub (R : ℕ) (τ : ℝ) (v : Fin d → ℝ) :
    (1 / (R.factorial : ℝ)) * expTermFam η ζ R τ v =
      tailFam η ζ R τ v + (-1) * tailFam η ζ (R + 1) τ v := by
  rw [tailFam_succ]
  ring

/-- ★★ **The generating identity at fixed depth**: the family coefficients of the exponential
field family are the (unconditionally convergent) exponential generating series of the family
coefficients of the monomial families `τ^r η ζ^r`. -/
theorem hasSum_empCoeffAtDepth_expTermFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) * empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q)
      (empCoeffAtDepth η ζ h k p μ q) := by
  obtain ⟨K₀, M', hK₀, hT⟩ := exists_famJetBound_tailFam hη hζ p
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepthFam_single_le h k p hk hp hp0 M'
  set c : ℕ → ℝ := fun r =>
    empCoeffAtDepthFam (fun τ v => (1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v) h k p μ q
    with hc
  set t : ℕ → ℝ := fun R => empCoeffAtDepthFam (tailFam η ζ R) h k p μ q with ht
  have hTj : ∀ R, ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => tailFam η ζ R z.1 z.2 :=
    contDiff_tailFam_joint hη hζ
  have hEeq : ∀ r : ℕ, (fun τ v => (1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v) =
      fun τ v => tailFam η ζ r τ v + (-1) * tailFam η ζ (r + 1) τ v := fun r => by
    funext τ v
    exact expTermFam_inv_factorial_eq_tailFam_sub r τ v
  have hE : ∀ r : ℕ, FamJetBound (fun τ v => (1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v) p 1
      (K₀ * (1 / 2) ^ r + |(-1 : ℝ)| * (K₀ * (1 / 2) ^ (r + 1))) M' := fun r => by
    rw [hEeq r]
    exact (hT r).add (hTj r) (contDiff_joint_const_mul (hTj (r + 1)) (-1))
      ((hT (r + 1)).const_mul (hTj (r + 1)) (-1))
  have hEj : ∀ r : ℕ, ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      (1 / (r.factorial : ℝ)) * expTermFam η ζ r z.1 z.2 := fun r =>
    contDiff_joint_const_mul (contDiff_expTermFam_joint hη hζ r) _
  -- partial sums
  have hpart : ∀ R : ℕ, empCoeffAtDepth η ζ h k p μ q = ∑ r ∈ range R, c r + t R := by
    intro R
    induction R with
    | zero =>
      rw [Finset.sum_range_zero, zero_add]
      change _ = empCoeffAtDepthFam (tailFam η ζ 0) h k p μ q
      rw [tailFam_zero]
      rfl
    | succ R ih =>
      rw [Finset.sum_range_succ, ih, add_assoc]
      congr 1
      have hfun : tailFam η ζ R = fun τ v =>
          (1 / (R.factorial : ℝ)) * expTermFam η ζ R τ v + tailFam η ζ (R + 1) τ v := by
        funext τ v
        rw [tailFam_succ]
        ring
      change empCoeffAtDepthFam (tailFam η ζ R) h k p μ q =
        empCoeffAtDepthFam (fun τ v => (1 / (R.factorial : ℝ)) * expTermFam η ζ R τ v) h k p μ q +
          empCoeffAtDepthFam (tailFam η ζ (R + 1)) h k p μ q
      rw [hfun]
      exact empCoeffAtDepthFam_add h k p (hEj R) (hTj (R + 1)) (hE R) (hT (R + 1)) hk hL hp hp0
        hμ hq
  -- the tail coefficient tends to zero
  have htail : Tendsto t atTop (𝓝 0) := by
    have hb : ∀ R, |t R| ≤ (K₀ * K₁) * (1 / 2) ^ R := fun R => by
      have := hK₁ _ (hTj R) _ (hT R) μ hμ q hq
      calc |t R| = |empCoeffAtDepthFam (tailFam η ζ R) h k p μ q| := rfl
        _ ≤ K₀ * (1 / 2) ^ R * K₁ := this
        _ = (K₀ * K₁) * (1 / 2) ^ R := by ring
    have hgeo : Tendsto (fun R : ℕ => (K₀ * K₁) * (1 / 2 : ℝ) ^ R) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (K₀ * K₁)
      simpa using this
    exact squeeze_zero_norm (fun R => by simpa only [Real.norm_eq_abs] using hb R) hgeo
  -- absolute summability
  have hsum : Summable fun r => ‖c r‖ := by
    have hg : Summable fun r : ℕ => (1 / 2 : ℝ) ^ r :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hg1 : Summable fun r : ℕ => (1 / 2 : ℝ) ^ (r + 1) := (summable_nat_add_iff 1).2 hg
    refine Summable.of_nonneg_of_le (f := fun r : ℕ =>
      (K₀ * (1 / 2) ^ r + |(-1 : ℝ)| * (K₀ * (1 / 2) ^ (r + 1))) * K₁)
      (fun r => norm_nonneg _) (fun r => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hK₁ _ (hEj r) _ (hE r) μ hμ q hq
    · exact ((hg.mul_left K₀).add ((hg1.mul_left K₀).mul_left _)).mul_right K₁
  -- identify the terms
  have hc' : ∀ r, c r = (1 / (r.factorial : ℝ)) * empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q :=
    fun r => by
    have hB : FamJetBound (expTermFam η ζ r) p 1
        (|(r.factorial : ℝ)| * (K₀ * (1 / 2) ^ r + |(-1 : ℝ)| * (K₀ * (1 / 2) ^ (r + 1)))) M' := by
      have h1 := (hE r).const_mul (hEj r) (r.factorial : ℝ)
      have h2 : (fun τ v => (r.factorial : ℝ) * ((1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v)) =
          expTermFam η ζ r := by
        funext τ v
        have : (r.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      rwa [h2] at h1
    exact empCoeffAtDepthFam_const_mul h k p (contDiff_expTermFam_joint hη hζ r) _ hB hk hL hp hp0
      hμ hq
  have hfun : (fun r : ℕ => (1 / (r.factorial : ℝ)) *
      empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q) = c := by
    funext r
    exact (hc' r).symm
  rw [hfun, hasSum_iff_tendsto_nat_of_summable_norm hsum]
  have hps : (fun n => ∑ i ∈ range n, c i) = fun n => empCoeffAtDepth η ζ h k p μ q - t n := by
    funext n
    rw [hpart n]
    ring
  rw [hps]
  simpa using (tendsto_const_nhds (x := empCoeffAtDepth η ζ h k p μ q)).sub htail

/-- `r/2 ∈ Q⁻¹ℕ` for `Q = Qamb k = 2 ∏ kᵢ`. -/
theorem half_mem_lattice (hk : ∀ i, 0 < k i) (r : ℕ) :
    ∃ m₀ : ℕ, (r : ℝ) / 2 = (m₀ : ℝ) / Qamb k := by
  refine ⟨r * ∏ i, k i, ?_⟩
  unfold Qamb
  have hprod : (0 : ℝ) < ∏ i, (k i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hk i
  push_cast
  field_simp

/-- ★★★ **The all-orders generating identity, chart-wise on the unit box**: for every
`μ ∈ Q⁻¹ℕ` and `q ≤ d − 1`,
`Σ_{r ≥ 0} (1/r!) · empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q = empCoeff η ζ h k μ q`
(unconditionally convergent). -/
theorem hasSum_empCoeff_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q)
      (empCoeff η ζ h k μ q) := by
  have hQ := Qamb_pos k hk
  have hL₀ : L₀ h ≤ cutoffOf h μ := L₀_le_cutoffOf h μ
  have hL : 0 < cutoffOf h μ := lt_of_lt_of_le (by unfold L₀; omega) hL₀
  have hμL : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
    (mem_latticeBelow_iff hQ).2 ⟨hμ, lt_cutoffOf h μ⟩
  have hp := depthOf_add hk hL₀ (k := k)
  have hp0 := depthOf_pos hk hL₀ (k := k)
  have key := hasSum_empCoeffAtDepth_expTermFam h k (depthOf h k (cutoffOf h μ)) hη hζ hk hL hp
    hp0 hμL hq
  have hfun : (fun r : ℕ => (1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q) =
      fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeffAtDepthFam (expTermFam η ζ r) h k (depthOf h k (cutoffOf h μ)) μ q := by
    funext r
    rw [empCoeffAtDepthFam_expTermFam_eq hη hζ hk hL hp hp0 r hμL hq]
  rw [hfun]
  exact key

/-- The `tsum` form of `hasSum_empCoeff_population`. -/
theorem empCoeff_eq_tsum_population (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff η ζ h k μ q = ∑' r : ℕ, (1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q :=
  (hasSum_empCoeff_population h k hη hζ hk hμ hq).tsum_eq.symm

/-- ★★★ **The generating identity with the resolved field `u^k ζ` inserted**: the population
coefficients of `η (u^k ζ)^r` at the unshifted monomial `h`. -/
theorem hasSum_empCoeff_population_mono (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    HasSum (fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k (μ + r / 2) q)
      (empCoeff η ζ h k μ q) := by
  have key := hasSum_empCoeff_population h k hη hζ hk hμ hq
  have hfun : (fun r : ℕ => (1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k (μ + r / 2) q) =
      fun r : ℕ => (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k
          (μ + r / 2) q := by
    funext r
    have hμr : ∃ m : ℕ, μ + (r : ℝ) / 2 = (m : ℝ) / Qamb k := by
      obtain ⟨m, hm⟩ := hμ
      obtain ⟨m₀, hm₀⟩ := half_mem_lattice k hk r
      refine ⟨m + m₀, ?_⟩
      rw [hm, hm₀]
      push_cast
      ring
    rw [empCoeff_monomial_absorb hη hζ hk r hμr hq]
  rw [hfun]
  exact key

end SmoothEngine

end Grammar
