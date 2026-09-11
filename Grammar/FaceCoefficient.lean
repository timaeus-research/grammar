/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AdaptedPieceAtlas

/-!
# The face coefficient and decomposition-independence

Units 4–5 of consult #76 (`tide-log/gpt6_bigpicture_v76.md`), scoped as advised: first the explicit
face formula for the existing analytic coefficient, then representation-independence at a fixed
scale.

* **Uniqueness of certificates**: two leading-term certificates of the same function at the same
  pair have the same coefficient (`HasLeadingTerm.coeff_unique`, uniqueness of limits), and two
  certificates with NONZERO coefficients are at the same pair (`HasLeadingTerm.pair_unique`: the
  exponent-pair order is total, `PairDominates.total`, and a dominated certificate has coefficient
  zero at the dominating pair). Hence the summed tied coefficient of a scalar-unit atlas does not
  depend on the atlas (`FiniteScalarUnitAtlas.tiedCoeff_eq`): a **decomposition-independent
  coefficient** — this does not by itself identify an intrinsic face density or a transformation
  law.
* **The face formula when all ratios are minimal** (`∀ j, (h_j+1)/(2k_j) = λ`, the case of the
  paper's printed `eq:thm_leading_coeff`): the face projection zeroes every normal coordinate
  and the
  residual weight is `1`, so `amplitudeCoeff h k λ β η = faceLeadConst · η(0)`
  (`amplitudeCoeff_of_all_minimal`), with `faceLeadConst = Γ(λ) β^{−λ}/n! · ∏_j 1/(2k_j)`
  (`faceLeadConst_of_all_minimal`); the box and scalar face coefficients follow
  (`boxFaceCoeff_of_all_minimal`, `scalarBoxFaceCoeff_of_all_minimal`), and the coefficient of a
  scalar-unit cell is the **explicit face integral**
  `b^{Σh+n+1}(b^{2Σk})^{−λ} · Γ(λ)/n! ∏_j 1/(2k_j) · ∫_base β_w(z) q(z)^{−λ} A(z,0) dz`
  (`ScalarUnitCell.coeff_of_all_minimal`) — the paper's
  `Γ(λ)/(m−1)! · a_I · ∫_{S_I} (φ∘π)|_{S_I} c_0` with the tangential weight, the scalar unit and
  the amplitude at the normal origin identified.

Non-claims: for a non-minimal ratio the face integral keeps the noncritical normal coordinates
(the definition `amplitudeCoeff` is that integral; no reindexed product form is proved here); no
coordinate transformation law of the face density is proved; positivity is not inferred for signed
data.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Uniqueness of certificates -/

section Unique

variable {Z : ℝ → ℝ} {c₁ c₂ lam lam₁ lam₂ : ℝ} {k k₁ k₂ : ℕ}

/-- **Two certificates at the same pair have the same coefficient.** -/
theorem HasLeadingTerm.coeff_unique (h₁ : HasLeadingTerm Z c₁ lam k)
    (h₂ : HasLeadingTerm Z c₂ lam k) : c₁ = c₂ :=
  tendsto_nhds_unique h₁ h₂

/-- The exponent-pair order is total. -/
theorem PairDominates.total (hne : lam₁ ≠ lam₂ ∨ k₁ ≠ k₂) :
    PairDominates lam₁ k₁ lam₂ k₂ ∨ PairDominates lam₂ k₂ lam₁ k₁ := by
  unfold PairDominates
  rcases lt_trichotomy lam₁ lam₂ with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases hne with hne | hne
    · exact absurd heq hne
    · rcases lt_or_gt_of_ne hne with hk | hk
      · exact Or.inr (Or.inr ⟨heq.symm, hk⟩)
      · exact Or.inl (Or.inr ⟨heq, hk⟩)
  · exact Or.inr (Or.inl hgt)

/-- **Nonzero certificates identify the pair.** -/
theorem HasLeadingTerm.pair_unique (h₁ : HasLeadingTerm Z c₁ lam₁ k₁) (hc₁ : c₁ ≠ 0)
    (h₂ : HasLeadingTerm Z c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) : lam₁ = lam₂ ∧ k₁ = k₂ := by
  by_contra hne
  have hne' : lam₁ ≠ lam₂ ∨ k₁ ≠ k₂ := by
    rcases not_and_or.1 hne with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases PairDominates.total hne' with hd | hd
  · exact hc₁ (h₁.coeff_unique (h₂.of_dominated hd))
  · exact hc₂ (h₂.coeff_unique (h₁.of_dominated hd))

end Unique

/-- **Decomposition-independence**: two scalar-unit atlases of the same function, at a common pair
dominating all their cells, have the same summed tied coefficient. -/
theorem FiniteScalarUnitAtlas.tiedCoeff_eq {t₁ t₂ : ℕ} {Z : ℝ → ℝ}
    (A₁ : FiniteScalarUnitAtlas t₁ Z) (A₂ : FiniteScalarUnitAtlas t₂ Z) (lam₀ : ℝ) (k₀ : ℕ)
    (h₁ : ∀ i, lam₀ ≤ (A₁.cell i).lam)
    (h₁' : ∀ i, (A₁.cell i).lam = lam₀ → (A₁.cell i).mult - 1 ≤ k₀)
    (h₂ : ∀ i, lam₀ ≤ (A₂.cell i).lam)
    (h₂' : ∀ i, (A₂.cell i).lam = lam₀ → (A₂.cell i).mult - 1 ≤ k₀) :
    ∑ i ∈ A₁.tied lam₀ k₀, (A₁.cell i).coeff = ∑ i ∈ A₂.tied lam₀ k₀, (A₂.cell i).coeff :=
  (A₁.hasLeadingTerm_of_extremal lam₀ k₀ h₁ h₁').coeff_unique
    (A₂.hasLeadingTerm_of_extremal lam₀ k₀ h₂ h₂')

/-! ### The face formula when all ratios are minimal -/

section AllMinimal

variable {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (hall : ∀ i, ratioExp h k i = l)

include hall in
theorem faceProj_of_all_minimal (u : Fin d → ℝ) : faceProj h k l u = 0 := by
  funext i
  simp only [faceProj, hall i, if_true, Pi.zero_apply]

include hall in
theorem residualWeight_of_all_minimal (u : Fin d → ℝ) : residualWeight h k l u = 1 :=
  Finset.prod_eq_one fun i _ => by simp only [hall i, if_true]

include hall in
theorem multCount_of_all_minimal : multCount (ratioExp h k) l = d := by
  unfold multCount
  simp only [hall, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

include hall in
/-- The face constant when all ratios are minimal: `Γ(λ) β^{−λ}/(d−1)! · ∏_j 1/(2k_j)`. -/
theorem faceLeadConst_of_all_minimal :
    faceLeadConst h k l β = Real.Gamma l * β ^ (-l) / ((d - 1).factorial : ℝ) *
      ∏ i, 1 / (2 * (k i : ℝ)) := by
  unfold faceLeadConst
  rw [multCount_of_all_minimal h k l hall]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by simp only [hall i, if_true]

include hall in
/-- **The face formula when all ratios are minimal**: `amplitudeCoeff = faceLeadConst · η(0)`. -/
theorem amplitudeCoeff_of_all_minimal (η : (Fin d → ℝ) → ℝ) :
    amplitudeCoeff h k l β η = faceLeadConst h k l β * η 0 := by
  unfold amplitudeCoeff
  congr 1
  have : ∀ u ∈ unitBox d, η (faceProj h k l u) * residualWeight h k l u = η 0 := fun u _ => by
    rw [faceProj_of_all_minimal h k l hall, residualWeight_of_all_minimal h k l hall, mul_one]
  rw [setIntegral_congr_fun (measurableSet_unitBox d) this, setIntegral_const, measureReal_def,
    volume_unitBox, ENNReal.toReal_one, one_smul]

end AllMinimal

section Cells

variable {n : ℕ} (h k : Fin (n + 1) → ℕ) {l : ℝ} (hall : ∀ i, ratioExp h k i = l) (β b : ℝ) {t : ℕ}
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

include hall in
theorem boxFaceCoeff_of_all_minimal (z : Fin t → ℝ) :
    boxFaceCoeff n h k β b A l z =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) * (faceLeadConst h k l β * A z 0) := by
  unfold boxFaceCoeff
  rw [amplitudeCoeff_of_all_minimal h k l β hall, smul_zero]

include hall in
theorem scalarBoxFaceCoeff_of_all_minimal (q : (Fin t → ℝ) → ℝ) (z : Fin t → ℝ) :
    scalarBoxFaceCoeff n h k b q A l z =
      q z ^ (-l) * (b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        (faceLeadConst h k l 1 * A z 0)) := by
  unfold scalarBoxFaceCoeff
  rw [boxFaceCoeff_of_all_minimal h k hall 1 b A z]

end Cells

/-- **The explicit face integral of a scalar-unit cell when all ratios are minimal**:
`coeff = b^{Σh+n+1}(b^{2Σk})^{−λ} · Γ(λ)/n! ∏_j 1/(2k_j) · ∫_base β_w(z) q(z)^{−λ} A(z,0) dz`. -/
theorem ScalarUnitCell.coeff_of_all_minimal {t : ℕ} (c : ScalarUnitCell t)
    (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
    c.coeff = c.b ^ (∑ i, c.h i + (c.n + 1)) * (c.b ^ (2 * ∑ i, c.k i)) ^ (-c.lam) *
      (Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k i : ℝ))) *
        ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
  unfold ScalarUnitCell.coeff
  have hconst : faceLeadConst c.h c.k c.lam 1 =
      Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k i : ℝ)) := by
    rw [faceLeadConst_of_all_minimal c.h c.k c.lam 1 hall, Real.one_rpow, mul_one,
      Nat.add_sub_cancel]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  rw [scalarBoxFaceCoeff_of_all_minimal c.h c.k hall c.b c.A c.q z, hconst]
  ring

end Grammar
