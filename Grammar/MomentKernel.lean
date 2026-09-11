/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FaceCoefficient

/-!
# Normal moments of the box kernel: the exponent shift and certificate ratios

Unit D of consult #76 (`tide-log/gpt6_bigpicture_v76.md`), scoped as advised: on a positive orthant
the **monomial insertion** `u^α` in the amplitude is exactly the shift `h ↦ h + α` of the density
exponents (`boxKernel_shift`, `scalarBoxKernel_shift`), so the normal moment kernel
`∫_{(0,b]^{n+1}} A(z,u) u^α ∏u^h e^{−βN ∏u^{2k}} du` (`momentKernel`) has the certificate of
  CCXXIX at
the shifted pair `(λ_α, m_α − 1)`, `λ_α = min_j (h_j+α_j+1)/(2k_j) ≥ λ`
(`hasLeadingTerm_momentKernel`, `minRatio_le_minRatio_shift`) — the Mellin scaling of the
moments.
**Certificate ratios**: for two certificates with `c₂ ≠ 0` and `k₂ ≤ k₁`, the quotient has the
certificate `(c₁/c₂, λ₁ − λ₂, k₁ − k₂)` (`HasLeadingTerm.div`, from
`powLogScale λ₁ k₁ / powLogScale λ₂ k₂ = powLogScale (λ₁−λ₂) (k₁−k₂)`), so a **normalised moment**
`momentKernel/boxKernel` decays like `N^{−(λ_α−λ)} (log N)^{m_α−m}` when the partition kernel's
coefficient is nonzero and the log degrees are ordered (`hasLeadingTerm_normalisedMoment`).

Non-claims (consult #76): on a symmetric box the signed moments acquire orthant signs and can
cancel (only the positive orthant is treated); a normalised moment needs a nonzero denominator
coefficient; a drop of the log degree under the shift (`m_α < m`) is not a power–log scale of the
form used here; no identification with the tube fibre measures `condTubeNormalMeasure` is claimed
— that requires an explicit equality of measures.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### The exponent shift -/

section Shift

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {t : ℕ}
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **Monomial insertion is an exponent shift**: `u^α` in the amplitude equals `h ↦ h + α`. -/
theorem boxKernel_shift (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) (N : ℝ) :
    boxKernel n (fun i => h i + α i) k β b A z N =
      boxKernel n h k β b (fun z u => A z u * ∏ i, u i ^ α i) z N := by
  unfold boxKernel origPhaseIntegral
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : ∏ i, u i ^ (h i + α i) = (∏ i, u i ^ h i) * ∏ i, u i ^ α i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => pow_add _ _ _
  simp only [this]
  ring

theorem scalarBoxKernel_shift (q : (Fin t → ℝ) → ℝ) (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) (N : ℝ) :
    scalarBoxKernel n (fun i => h i + α i) k b q A z N =
      scalarBoxKernel n h k b q (fun z u => A z u * ∏ i, u i ^ α i) z N := by
  unfold scalarBoxKernel
  exact boxKernel_shift n h k 1 b A α z _

/-- The shifted exponent is at least the original one: moments decay at least as fast. -/
theorem minRatio_le_minRatio_shift (α : Fin (n + 1) → ℕ) :
    minRatio h k ≤ minRatio (fun i => h i + α i) k := by
  obtain ⟨i, hi⟩ := exists_ratioExp_eq_minRatio (fun i => h i + α i) k
  rw [← hi]
  refine (minRatio_le h k i).trans ?_
  unfold ratioExp
  simp only [Nat.cast_add]
  gcongr
  linarith [(Nat.cast_nonneg (α i) : (0 : ℝ) ≤ α i)]

/-- **The normal moment kernel** `∫ A(z,u) u^α ∏u^h e^{−βN∏u^{2k}} du`. -/
noncomputable def momentKernel (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  boxKernel n h k β b (fun z u => A z u * ∏ i, u i ^ α i) z N

theorem continuous_monomialAmp (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) :
    Continuous (Function.uncurry fun z u => A z u * ∏ i, u i ^ α i) := by
  have : Function.uncurry (fun z u => A z u * ∏ i, u i ^ α i) =
      fun p : (Fin t → ℝ) × (Fin (n + 1) → ℝ) => Function.uncurry A p * ∏ i, p.2 i ^ α i := by
    funext p
    rfl
  rw [this]
  fun_prop

variable {n h k β b}

/-- **The Mellin scaling of the normal moments**: the moment kernel has the certificate at the
shifted pair `(min_j (h_j+α_j+1)/(2k_j), #minimisers − 1)`. -/
theorem hasLeadingTerm_momentKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ) :
    HasLeadingTerm (momentKernel n h k β b A α z)
      (boxFaceCoeff n (fun i => h i + α i) k β b A (minRatio (fun i => h i + α i) k) z)
      (minRatio (fun i => h i + α i) k)
      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) := by
  have hcert := hasLeadingTerm_boxKernel A hk hβ hb (minRatio_le (fun i => h i + α i) k)
    (exists_ratioExp_eq_minRatio (fun i => h i + α i) k) hA z
  unfold momentKernel
  refine hcert.congr' (Eventually.of_forall fun N => ?_)
  exact boxKernel_shift n h k β b A α z N

end Shift

/-! ### Certificate ratios -/

section Ratio

variable {lam₁ lam₂ : ℝ} {k₁ k₂ : ℕ}

theorem powLogScale_div_powLogScale {N : ℝ} (hN : 1 < N) (hk : k₂ ≤ k₁) :
    powLogScale lam₁ k₁ N / powLogScale lam₂ k₂ N = powLogScale (lam₁ - lam₂) (k₁ - k₂) N := by
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  unfold powLogScale
  rw [mul_div_mul_comm, ← Real.rpow_sub hN0, show -lam₁ - -lam₂ = -(lam₁ - lam₂) by ring,
    pow_sub₀ _ hlog hk, div_eq_mul_inv]

/-- **Certificate ratios**: `Z₁/Z₂` has the certificate `(c₁/c₂, λ₁ − λ₂, k₁ − k₂)` when `c₂ ≠ 0`
and `k₂ ≤ k₁`. -/
theorem HasLeadingTerm.div {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ} (h₁ : HasLeadingTerm Z₁ c₁ lam₁ k₁)
    (h₂ : HasLeadingTerm Z₂ c₂ lam₂ k₂) (hc₂ : c₂ ≠ 0) (hk : k₂ ≤ k₁) :
    HasLeadingTerm (fun N => Z₁ N / Z₂ N) (c₁ / c₂) (lam₁ - lam₂) (k₁ - k₂) := by
  have h := Tendsto.div h₁ h₂ hc₂
  refine h.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  simp only [Pi.div_apply]
  rw [div_div_div_comm, powLogScale_div_powLogScale hN hk]

end Ratio

/-- **Normalised moments**: if the partition kernel has a nonzero coefficient and the log
  degrees are
ordered, `momentKernel/boxKernel` has the certificate `(c_α/c, λ_α − λ, m_α − m)`. -/
theorem hasLeadingTerm_normalisedMoment {n : ℕ} {h k : Fin (n + 1) → ℕ} {β b : ℝ} {t : ℕ}
    {A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hA : Continuous (Function.uncurry A)) (α : Fin (n + 1) → ℕ) (z : Fin t → ℝ)
    (hc : boxFaceCoeff n h k β b A (minRatio h k) z ≠ 0)
    (hdeg : multCount (ratioExp h k) (minRatio h k) - 1 ≤
      multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1) :
    HasLeadingTerm (fun N => momentKernel n h k β b A α z N / boxKernel n h k β b A z N)
      (boxFaceCoeff n (fun i => h i + α i) k β b A (minRatio (fun i => h i + α i) k) z /
        boxFaceCoeff n h k β b A (minRatio h k) z)
      (minRatio (fun i => h i + α i) k - minRatio h k)
      (multCount (ratioExp (fun i => h i + α i) k) (minRatio (fun i => h i + α i) k) - 1 -
        (multCount (ratioExp h k) (minRatio h k) - 1)) :=
  (hasLeadingTerm_momentKernel A hk hβ hb hA α z).div
    (hasLeadingTerm_boxKernel A hk hβ hb (minRatio_le h k) (exists_ratioExp_eq_minRatio h k) hA z)
    hc hdeg

end Grammar
