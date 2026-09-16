/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.EmpiricalFamilyLinear
import Grammar.EmpiricalGeneratingRect
import Grammar.CubeJets
import Grammar.CoordinateFrechetBridge

/-!
# The population coefficient as a bounded linear functional of the amplitude jet

At fixed depth `p` (`p_i + h_i = 2 k_i L`), the zero-field coefficient `η ↦ empCoeff η 0 h k μ q`
is the family coefficient of the constant family `(τ, v) ↦ η v`
(`empCoeff_zero_eq_empCoeffAtDepthFam_const`, the `r = 0` case of the monomial-family
identification), hence

* linear in the amplitude (`empCoeff_zero_add`, `empCoeff_zero_smul`);
* bounded by the sup norm of the order-`R` jet of `η` on the closed unit box, `R ≥ Σ p_i`
  (`exists_abs_empCoeff_zero_le_norm_cubeJet`, from the family estimate
  `exists_abs_empCoeffAtDepthFam_le` and `famJetBound_const_of_cubeJet`);
* hence a function of that jet alone (`empCoeff_zero_eq_of_cubeJet_eq`).

These are the inputs for the continuous linear functional on the closed jet range
(`AmplitudeJetSpace`) and the Gaussian averaging theorem (consult #160, A3–A4).

Zero `sorry`/`axiom`.
-/

open Finset
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {h k p : Fin d → ℕ}

/-- The monomial family at `r = 0` is the constant family of the amplitude. -/
theorem expTermFam_zero (η ζ : (Fin d → ℝ) → ℝ) : expTermFam η ζ 0 = fun _ v => η v := by
  funext τ v
  simp [expTermFam]

/-- ★ **Constant-family compatibility**: the zero-field coefficient is the depth-`p` family
coefficient of the constant family. -/
theorem empCoeff_zero_eq_empCoeffAtDepthFam_const {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff η (fun _ => 0) h k μ q = empCoeffAtDepthFam (fun _ v => η v) h k p μ q := by
  have h0 := empCoeffAtDepthFam_expTermFam_eq hη (contDiff_const (c := (0 : ℝ))) hk hL hp hp0 0
    hμ hq
  rw [expTermFam_zero] at h0
  simpa using h0.symm

/-- The Fréchet jets of order `≤ R` on the closed box are bounded by the cube-jet norm. -/
theorem norm_iteratedFDeriv_le_norm_cubeJet {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    {R : ℕ} {b : ℝ} {r : ℕ} (hr : r ≤ R) {v : Fin d → ℝ} (hv : v ∈ closedBox d b) :
    ‖iteratedFDeriv ℝ r η v‖ ≤ ‖cubeJet R b η hη‖ :=
  calc ‖iteratedFDeriv ℝ r η v‖
      = ‖(cubeJet R b η hη).toPi ⟨r, Nat.lt_succ_of_le hr⟩ ⟨v, hv⟩‖ := rfl
    _ ≤ ‖(cubeJet R b η hη).toPi ⟨r, Nat.lt_succ_of_le hr⟩‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖(cubeJet R b η hη).toPi‖ := norm_le_pi_norm _ _
    _ = ‖cubeJet R b η hη‖ := rfl

/-- The constant family of `η` has the jet bound `‖cubeJet R 1 η‖` (envelope `M' = 0`) once
`R ≥ Σ p_i`. -/
theorem famJetBound_const_of_cubeJet {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {R : ℕ}
    (hR : ∑ i, p i ≤ R) : FamJetBound (fun _ v => η v) p 1 ‖cubeJet R 1 η hη‖ 0 := by
  intro m hm τ hτ v hv
  have hsum : ∑ i, m i ≤ R := (Finset.sum_le_sum fun i _ => hm i).trans hR
  have h1 : |pdMulti m (List.finRange d) η v| ≤ ‖cubeJet R 1 η hη‖ :=
    (abs_pdMulti_finRange_le_norm_iteratedFDeriv hη m v).trans
      (norm_iteratedFDeriv_le_norm_cubeJet hη hsum hv)
  have h2 : (1 : ℝ) ≤ (1 + τ) ^ (∑ i, p i) * Real.exp (0 * τ) := by
    rw [zero_mul, Real.exp_zero, mul_one]
    exact one_le_pow₀ (by linarith)
  calc |pdMulti m (List.finRange d) η v| ≤ ‖cubeJet R 1 η hη‖ := h1
    _ ≤ ‖cubeJet R 1 η hη‖ * ((1 + τ) ^ (∑ i, p i) * Real.exp (0 * τ)) :=
        le_mul_of_one_le_right (norm_nonneg _) h2
    _ = ‖cubeJet R 1 η hη‖ * (1 + τ) ^ (∑ i, p i) * Real.exp (0 * τ) := by ring

/-- ★★ **The zero-field coefficient is bounded by the jet norm of the amplitude**: there is
`K = K(h, k, p, L)` with `|empCoeff η 0 h k μ q| ≤ K ‖cubeJet R 1 η‖` for every smooth `η`, every
`μ` on the lattice below `L` and `q ≤ d − 1`, once `R ≥ Σ p_i`. -/
theorem exists_abs_empCoeff_zero_le_norm_cubeJet (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {R : ℕ} (hR : ∑ i, p i ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (η : (Fin d → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η),
      ∀ μ ∈ latticeBelow (Qamb k) L, ∀ q ≤ d - 1,
        |empCoeff η (fun _ => 0) h k μ q| ≤ K * ‖cubeJet R 1 η hη‖ := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepthFam_le h k p hk hp hp0 0
  refine ⟨K₁, hK₁0, fun η hη μ hμ q hq => ?_⟩
  rw [empCoeff_zero_eq_empCoeffAtDepthFam_const hη hk hL hp hp0 hμ hq]
  have hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => (fun _ v => η v) z.1 z.2 :=
    hη.comp contDiff_snd
  have hsum := hK₁ (fun _ v => η v) hA _ (famJetBound_const_of_cubeJet hη hR)
  have hq' : q ∈ range (d - 1 + 1) := mem_range.2 (Nat.lt_succ_of_le hq)
  calc |empCoeffAtDepthFam (fun _ v => η v) h k p μ q|
      ≤ ∑ q' ∈ range (d - 1 + 1), |empCoeffAtDepthFam (fun _ v => η v) h k p μ q'| :=
        Finset.single_le_sum (f := fun q' => |empCoeffAtDepthFam (fun _ v => η v) h k p μ q'|)
          (fun _ _ => abs_nonneg _) hq'
    _ ≤ ∑ μ' ∈ latticeBelow (Qamb k) L, ∑ q' ∈ range (d - 1 + 1),
          |empCoeffAtDepthFam (fun _ v => η v) h k p μ' q'| :=
        Finset.single_le_sum
          (f := fun μ' => ∑ q' ∈ range (d - 1 + 1),
            |empCoeffAtDepthFam (fun _ v => η v) h k p μ' q'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hμ
    _ ≤ ‖cubeJet R 1 η hη‖ * K₁ := hsum
    _ = K₁ * ‖cubeJet R 1 η hη‖ := mul_comm _ _

/-- ★ **Additivity in the amplitude** of the zero-field coefficient. -/
theorem empCoeff_zero_add {η ξ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff (fun v => η v + ξ v) (fun _ => 0) h k μ q =
      empCoeff η (fun _ => 0) h k μ q + empCoeff ξ (fun _ => 0) h k μ q := by
  rw [empCoeff_zero_eq_empCoeffAtDepthFam_const (hη.add hξ) hk hL hp hp0 hμ hq,
    empCoeff_zero_eq_empCoeffAtDepthFam_const hη hk hL hp hp0 hμ hq,
    empCoeff_zero_eq_empCoeffAtDepthFam_const hξ hk hL hp hp0 hμ hq]
  exact empCoeffAtDepthFam_add h k p (hη.comp contDiff_snd) (hξ.comp contDiff_snd)
    (famJetBound_const_of_cubeJet hη (R := ∑ i, p i) le_rfl)
    (famJetBound_const_of_cubeJet hξ (R := ∑ i, p i) le_rfl) hk hL hp hp0 hμ hq

/-- Homogeneity in the amplitude of the zero-field coefficient. -/
theorem empCoeff_zero_smul {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    (c : ℝ) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff (fun v => c * η v) (fun _ => 0) h k μ q = c * empCoeff η (fun _ => 0) h k μ q :=
  empCoeff_const_mul h k hη contDiff_const hk c hμ hq

/-- Jets of differences. -/
theorem cubeJet_sub (R : ℕ) (b : ℝ) {η ξ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hξ : ContDiff ℝ ∞ ξ) :
    cubeJet R b (fun v => η v - ξ v) (hη.sub hξ) = cubeJet R b η hη - cubeJet R b ξ hξ := by
  funext r
  refine ContinuousMap.ext fun x => ?_
  change iteratedFDeriv ℝ r.1 (fun v => η v - ξ v) x.1 =
    iteratedFDeriv ℝ r.1 η x.1 - iteratedFDeriv ℝ r.1 ξ x.1
  exact iteratedFDeriv_sub_apply (hη.contDiffAt.of_le (by exact_mod_cast le_top))
    (hξ.contDiffAt.of_le (by exact_mod_cast le_top))

/-- ★ **Jet-locality of the amplitude**: two smooth amplitudes with the same order-`R` jet on the
closed unit box have the same zero-field coefficients (`R ≥ Σ p_i`). -/
theorem empCoeff_zero_eq_of_cubeJet_eq (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {R : ℕ} (hR : ∑ i, p i ≤ R)
    {η ξ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ)
    (heq : cubeJet R 1 η hη = cubeJet R 1 ξ hξ) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L)
    {q : ℕ} (hq : q ≤ d - 1) :
    empCoeff η (fun _ => 0) h k μ q = empCoeff ξ (fun _ => 0) h k μ q := by
  have hQ := Qamb_pos k hk
  have hμ' : ∃ m : ℕ, μ = (m : ℝ) / Qamb k := ((mem_latticeBelow_iff hQ).1 hμ).1
  obtain ⟨K, -, hK⟩ := exists_abs_empCoeff_zero_le_norm_cubeJet hk hL hp hp0 hR
  have h1 := hK (fun v => η v - ξ v) (hη.sub hξ) μ hμ q hq
  rw [cubeJet_sub R 1 hη hξ, heq, sub_self, norm_zero, mul_zero] at h1
  have h2 : empCoeff (fun v => η v - ξ v) (fun _ => 0) h k μ q =
      empCoeff η (fun _ => 0) h k μ q - empCoeff ξ (fun _ => 0) h k μ q := by
    have hfun : (fun v => η v - ξ v) = fun v => η v + (-1) * ξ v := by
      funext v
      ring
    rw [hfun, empCoeff_zero_add hη (contDiff_const.mul hξ) hk hL hp hp0 hμ hq,
      empCoeff_zero_smul hξ hk (-1) hμ' hq]
    ring
  rw [h2] at h1
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _)))

end Grammar
