/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DressedFamily

/-!
# The explicit second coefficient of an analytic spatial phase (unit 368; Astra #45 unit 2)

For coefficient families `cξ, cη` representing continuous `ξ, η` on the unit box, the second
Taylor-tree coefficient `B(ξ,η) = A_{λ,m−2}(cξ,cη)` (`m ≥ 2`) is the **finite-part face
integral**
```
B(ξ,η) = (1/((m−2)! ∏_{i∈J} 2kᵢ)) [ ∫ η(P_J u) J_λ(ξ(P_J u)) w(u) L(u) du
        + ∫ η(P_J u) J̇_λ(ξ(P_J u)) w(u) du
        + ∑_{i₀∈J} 2k_{i₀} ∫ w(u) ∫₀¹ (H(P_J u + t e_{i₀}) − H(P_J u))/t dt du ]
```
with `H = η J_λ(ξ)`, `J_λ(b) = fluctMoment β b 0 λ 0`,
`J̇_λ(b) = fluctMoment β b 0 λ 1 = −∂_νJ_ν(b)`, `L(u) = ∑_{ℓ∉J} 2k_ℓ log u_ℓ`
(`spatialSecondFace`, `spatialSecondCoeff_eq`).  The route: the
coefficient series regroups into `Φ_{m−2}[g⁰] + (m−1) Φ_{m−1}[g¹]` for the dressed families
(`familySpectralCoeff_second_eq_dressed`), whose functionals are the face integrals of unit 366 and
363, evaluated with `g^{(i)} = η J^{(i)}_λ(ξ)` extended to the closed cube by continuity
(`evalF_eq_on_closedCube`).  The same route identifies the leading coefficient, giving the
**consistency check**
`spatialFace h k l β ξ η = (1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫ η(P_J u) J_λ(ξ(P_J u)) w` against the
analytic identification of Headline LXXII (`spatialFace_eq_faceIntegral`).  Headline:
`L (𝒵_N[η;ξ]/(N^{-λ}L^{m-1}) − F(ξ,η)) → B(ξ,η)` with `B` explicit
(`spatialPhase_twoTerm_explicit`, analytic data `spatialPhase_twoTerm_explicit_analytic`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

variable {d : ℕ}

/-! ### Representation identities extend to the closed cube -/

theorem closedCube_subset_closure_unitBox (d : ℕ) : closedCube d ⊆ closure (unitBox d) := by
  unfold unitBox closedCube
  rw [closure_pi_set]
  intro v hv i hi
  rw [closure_Ioc zero_ne_one]
  exact hv i hi

/-- A representation identity on the open box extends to the closed cube by continuity. -/
theorem evalF_eq_on_closedCube {c : CoeffFamily d} (hc : AbsSummable c) {ξ : (Fin d → ℝ) → ℝ}
    (hξc : Continuous ξ) (hev : ∀ u ∈ piBox d (Ioc 0 1), evalF c u = ξ u) {v : Fin d → ℝ}
    (hv : v ∈ closedCube d) : evalF c v = ξ v :=
  Set.EqOn.of_subset_closure (fun u hu => hev u hu) (continuousOn_evalF hc) hξc.continuousOn
    (unitBox_subset_closedCube d) (closedCube_subset_closure_unitBox d) hv

theorem update_faceProj_mem_closedCube (h k : Fin d → ℕ) (l : ℝ) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) (i₀ : Fin d) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    Function.update (faceProj h k l u) i₀ t ∈ closedCube d := by
  have hmem := faceProj_mem_closedCube h k l hu
  intro i _
  by_cases hi : i = i₀
  · subst hi
    rw [Function.update_self]
    exact ⟨ht.1.le, ht.2⟩
  · rw [Function.update_of_ne hi]
    exact hmem i (Set.mem_univ i)

/-! ### Regrouping the coefficient series -/

theorem abs_coeffFunctional_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (j : ℕ) {f : CoeffFamily (n + 1)} (hf : AbsSummable f) :
    |coeffFunctional n h k l j f| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * mass f := by
  unfold coeffFunctional
  rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => by positivity)
  have hs := summable_mul_coeffAt n h k hk hf l j
  refine (norm_tsum_le_tsum_norm (f := fun γ => f γ *
    PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l j)
    (hs.abs.congr fun γ => (Real.norm_eq_abs _).symm)).trans ?_
  unfold mass
  rw [← tsum_mul_left]
  refine (hs.abs.congr fun γ => by rw [Real.norm_eq_abs]).tsum_le_tsum (fun γ => ?_)
    (hf.mul_left _)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_coeffAt_stateDensityRep_le n (h + γ) k hk l j)
    (abs_nonneg _)

theorem summable_dressed_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {l : ℝ} (hl : 0 < l) (i j : ℕ) :
    Summable fun p => β ^ p / (p.factorial : ℝ) * fluctMoment β (cξ 0) p l i *
      coeffFunctional n h k l j (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p)) := by
  set K := (∏ i, 1 / (2 * (k i : ℝ))) * (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) with hK
  have hK0 : 0 ≤ K := by positivity
  have hmaj := ((summable_phaseLogMoment_series β (cξ 0) (mass (fluctFamily cξ)) l hβ hl
    (mass_nonneg _) i).mul_left (K * mass cη))
  refine Summable.of_norm_bounded hmaj fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / _)]
  have hfm := abs_fluctMoment_le β (cξ 0) hβ p hl (le_refl i)
  have hΦ := abs_coeffFunctional_le n h k hk l j (hη.conv (hξ.fluctFamily.convPow p))
  have hmass := (mass_conv_le hη (hξ.fluctFamily.convPow p)).trans
    (mul_le_mul_of_nonneg_left (mass_convPow_le hξ.fluctFamily le_rfl p) (mass_nonneg _))
  calc β ^ p / (p.factorial : ℝ) * |fluctMoment β (cξ 0) p l i| *
        |coeffFunctional n h k l j (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p))|
      ≤ β ^ p / (p.factorial : ℝ) * phaseLogMoment β (cξ 0) l i p *
        (K * (mass cη * mass (fluctFamily cξ) ^ p)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hfm (by positivity))
          (hΦ.trans (mul_le_mul_of_nonneg_left hmass hK0)) (abs_nonneg _)
          (mul_nonneg (by positivity) (phaseLogMoment_nonneg _ _ _ _ _))
    _ = K * mass cη * ((β * mass (fluctFamily cξ)) ^ p / (p.factorial : ℝ) *
        phaseLogMoment β (cξ 0) l i p) := by
        rw [mul_pow]
        ring

/-- **The leading coefficient is the top functional of the dressed family**
`A_{λ,m−1}(cξ,cη) = Φ_{m−1}[g⁰]`. -/
theorem familySpectralCoeff_top_eq_dressed (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    familySpectralCoeff n h k β cξ cη l (multCount (ratioExp h k) l - 1) =
      coeffFunctional n h k l (multCount (ratioExp h k) l - 1) (dressedFamily β cξ cη l 0) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [familySpectralCoeff_eq_series n h k hk β hβ hξ hη hl, coeffFunctional_dressedFamily n h k hk
    hβ hξ hη hl]
  unfold familyCoeffSeries
  refine tsum_congr fun p => ?_
  unfold familyCoeffTerm
  rw [kernelFunctional_top_eq n h k hk β (cξ 0) p hmin hatt]
  ring

/-- **The second coefficient regroups into the dressed functionals**
`A_{λ,m−2}(cξ,cη) = Φ_{m−2}[g⁰] + (m−1) Φ_{m−1}[g¹]`. -/
theorem familySpectralCoeff_second_eq_dressed (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    familySpectralCoeff n h k β cξ cη l (multCount (ratioExp h k) l - 2) =
      coeffFunctional n h k l (multCount (ratioExp h k) l - 2) (dressedFamily β cξ cη l 0) +
        ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) *
          coeffFunctional n h k l (multCount (ratioExp h k) l - 1) (dressedFamily β cξ cη l 1) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [familySpectralCoeff_eq_series n h k hk β hβ hξ hη hl, coeffFunctional_dressedFamily n h k hk
    hβ hξ hη hl, coeffFunctional_dressedFamily n h k hk hβ hξ hη hl, ← tsum_mul_left]
  unfold familyCoeffSeries
  rw [← (summable_dressed_coeff n h k hk hβ hξ hη hl 0 _).tsum_add
    ((summable_dressed_coeff n h k hk hβ hξ hη hl 1 _).mul_left _)]
  refine tsum_congr fun p => ?_
  unfold familyCoeffTerm
  rw [kernelFunctional_second_eq n h k hk β (cξ 0) p hmin hm (hη.conv (hξ.fluctFamily.convPow p))]
  ring

/-! ### The explicit second coefficient -/

/-- The dressed amplitude `η(v) · fluctMoment β ξ(v) 0 λ i` (`i = 0`: `η J_λ(ξ)`; `i = 1`:
`η J̇_λ(ξ)`). -/
noncomputable def dressedAmplitude (β l : ℝ) (i : ℕ) (ξ η : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) : ℝ :=
  η v * fluctMoment β (ξ v) 0 l i

/-- **The explicit second spatial coefficient** `B(ξ,η)` (the finite-part face integral). -/
noncomputable def spatialSecondFace (h k : Fin (d + 1) → ℕ) (l β : ℝ)
    (ξ η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 2).factorial : ℝ) * faceTwoK h k l)) *
    ((∫ u in unitBox (d + 1), dressedAmplitude β l 0 ξ η (faceProj h k l u) *
        residualWeight h k l u * logWeight h k l u) +
      (∫ u in unitBox (d + 1), dressedAmplitude β l 1 ξ η (faceProj h k l u) *
        residualWeight h k l u) +
      ∑ i₀, if ratioExp h k i₀ = l then
        2 * (k i₀ : ℝ) * ∫ u in unitBox (d + 1), residualWeight h k l u *
          ∫ t in Ioc (0 : ℝ) 1,
            (dressedAmplitude β l 0 ξ η (Function.update (faceProj h k l u) i₀ t) -
              dressedAmplitude β l 0 ξ η (faceProj h k l u)) / t
      else 0)

theorem evalF_dressedFamily_eq (n : ℕ) {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ} (hl : 0 < l) (i : ℕ)
    {v : Fin (n + 1) → ℝ} (hv : v ∈ closedCube (n + 1)) :
    evalF (dressedFamily β cξ cη l i) v = dressedAmplitude β l i ξ η v := by
  rw [evalF_dressedFamily hβ hξ hη hl i hv, evalF_eq_on_closedCube hξ hξc hevξ hv,
    evalF_eq_on_closedCube hη hηc hevη hv]
  rfl

/-- **Consistency check**: the analytically identified leading coefficient `F(ξ,η)` (Headline
LXXII, via uniqueness) equals the face integral of the dressed amplitude obtained from the
coefficient series, `(1/((m−1)! ∏_{i∈J} 2kᵢ)) ∫ η(P_J u) J_λ(ξ(P_J u)) w(u) du`. -/
theorem spatialFace_eq_faceIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    spatialFace h k l β ξ η =
      (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) * faceTwoK h k l)) *
        ∫ u in unitBox (n + 1), dressedAmplitude β l 0 ξ η (faceProj h k l u) *
          residualWeight h k l u := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [← (spatial_leadingCoeff n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt).2,
    familySpectralCoeff_top_eq_dressed n h k hk hβ hξ hη hmin hatt,
    coeffFunctional_top_eq n h k hk hmin hatt (absSummable_dressedFamily hβ hξ hη hl 0)]
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  rw [evalF_dressedFamily_eq n hβ hξ hη hξc hηc hevξ hevη hl 0
    (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))]

/-- **The second spatial coefficient is the finite-part face integral**:
`B(ξ,η) = spatialSecondFace h k l β ξ η` for `m ≥ 2`. -/
theorem spatialSecondCoeff_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    spatialSecondCoeff n h k β cξ cη l = spatialSecondFace h k l β ξ η := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hg : ∀ (i : ℕ) (v : Fin (n + 1) → ℝ), v ∈ closedCube (n + 1) →
      evalF (dressedFamily β cξ cη l i) v = dressedAmplitude β l i ξ η v := fun i v hv =>
    evalF_dressedFamily_eq n hβ hξ hη hξc hηc hevξ hevη hl i hv
  unfold spatialSecondCoeff
  rw [if_pos hm, familySpectralCoeff_second_eq_dressed n h k hk hβ hξ hη hmin hatt hm,
    coeffFunctional_second_eq n h k hk hmin hm (absSummable_dressedFamily hβ hξ hη hl 0),
    coeffFunctional_top_eq n h k hk hmin hatt (absSummable_dressedFamily hβ hξ hη hl 1)]
  set m := multCount (ratioExp h k) l with hm_def
  have hI₁ : (∫ u in unitBox (n + 1), evalF (dressedFamily β cξ cη l 0) (faceProj h k l u) *
      residualWeight h k l u * logWeight h k l u) =
      ∫ u in unitBox (n + 1), dressedAmplitude β l 0 ξ η (faceProj h k l u) *
        residualWeight h k l u * logWeight h k l u :=
    setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
      rw [hg 0 _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))]
  have hI₂ : (∫ u in unitBox (n + 1), evalF (dressedFamily β cξ cη l 1) (faceProj h k l u) *
      residualWeight h k l u) =
      ∫ u in unitBox (n + 1), dressedAmplitude β l 1 ξ η (faceProj h k l u) *
        residualWeight h k l u :=
    setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
      rw [hg 1 _ (faceProj_mem_closedCube h k l (unitBox_subset_closedCube _ hu))]
  have hI₃ : ∀ i₀, (∫ u in unitBox (n + 1), residualWeight h k l u * ∫ t in Ioc (0 : ℝ) 1,
      (evalF (dressedFamily β cξ cη l 0) (Function.update (faceProj h k l u) i₀ t) -
        evalF (dressedFamily β cξ cη l 0) (faceProj h k l u)) / t) =
      ∫ u in unitBox (n + 1), residualWeight h k l u * ∫ t in Ioc (0 : ℝ) 1,
        (dressedAmplitude β l 0 ξ η (Function.update (faceProj h k l u) i₀ t) -
          dressedAmplitude β l 0 ξ η (faceProj h k l u)) / t := fun i₀ =>
    setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
      have hmem := unitBox_subset_closedCube _ hu
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [hg 0 _ (update_faceProj_mem_closedCube h k l hmem i₀ ht),
        hg 0 _ (faceProj_mem_closedCube h k l hmem)]
  simp_rw [hI₃]
  rw [hI₁, hI₂]
  unfold spatialSecondFace
  rw [← hm_def]
  have hfac : ((m - 1).factorial : ℝ) = ((m - 1 : ℕ) : ℝ) * ((m - 2).factorial : ℝ) := by
    rw [show m - 1 = (m - 2) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hm1 : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ m - 1 := by omega
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  have hf2 : ((m - 2).factorial : ℝ) ≠ 0 := by positivity
  have hF : faceTwoK h k l ≠ 0 := (faceTwoK_pos h k hk l).ne'
  rw [hfac]
  field_simp
  ring

/-! ### The headline: explicit two-term asymptotics -/

/-- **Two-term asymptotics for an arbitrary spatial phase with explicit second coefficient**:
`L (𝒵_N[η;ξ]/(N^{-λ}L^{m-1}) − F(ξ,η)) → B(ξ,η)` with `B` the finite-part face integral
(`m ≥ 2`). -/
theorem spatialPhase_twoTerm_explicit (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hevξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cξ u = ξ u)
    (hevη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        spatialFace h k l β ξ η))
      atTop (𝓝 (spatialSecondFace h k l β ξ η)) := by
  rw [← spatialSecondCoeff_eq n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt hm]
  exact spatialPhase_twoTerm_chart n h k hk hβ hξ hη hξc hηc hevξ hevη hmin hatt

/-- The analytic-data version: holomorphic phase and amplitude on a polydisc of radius `> 1`. -/
theorem spatialPhase_twoTerm_explicit_analytic (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {r R : ℝ} (hr : 1 < r) (hrR : r < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hξc : Continuous ξ) (hηc : Continuous η) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hm : 2 ≤ multCount (ratioExp h k) l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 ξ η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        spatialFace h k l β ξ η))
      atTop (𝓝 (spatialSecondFace h k l β ξ η)) := by
  have hr0 : 0 < r := by linarith
  refine spatialPhase_twoTerm_explicit n h k hk hβ
    ((absSummableAt_one_iff _).1 (absSummableAt_polyRealCoeff hr0 hrR zero_le_one hr hFξ))
    ((absSummableAt_one_iff _).1 (absSummableAt_polyRealCoeff hr0 hrR zero_le_one hr hFη))
    hξc hηc (fun u hu => ?_) (fun u hu => ?_) hmin hatt hm
  · rw [evalF_polyRealCoeff hr0 hrR hr hFξ hu, hξ u hu]
  · rw [evalF_polyRealCoeff hr0 hrR hr hFη hu, hη u hu]

end Grammar
