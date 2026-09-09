/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.FaceFunctionalSecond

/-!
# The phase-dressed amplitude family (unit 367; Astra #45 unit 2, step 7)

The coefficient series `A_{λ,j}(cξ,cη) = ∑_p β^p/p! K_k ∑_γ (cη * J^{*p})_γ S_p(λ,j;γ)` sums, at
`j = m−1, m−2`, into the coefficient functionals `Φ_j` applied to the **phase-dressed family**
`g^{(i)} = ∑_p β^p/p! fluctMoment β a p λ i · (cη * J^{*p})`, `a = cξ(0)`, `J = cξ − a`
(`dressedFamily`).  This unit provides the analytic input for that regrouping:

* the Taylor expansion of the fluctuation moments in the phase,
  `∑_p (β(b−a))^p/p! fluctMoment β a p ν i = fluctMoment β b 0 ν i` (`hasSum_fluctMoment_taylor`);
* `evalF` of convolution powers and of the constant-free part (`evalF_convPow`,
  `evalF_fluctFamily`);
* absolute convergence of the dressed double series (`summable_dressedTerm_prod`), so that the
  dressed family is absolutely summable (`absSummable_dressedFamily`) and sums against any bounded
  weight may be exchanged (`tsum_dressedFamily_mul`);
* the evaluation `g^{(i)}(u) = η(u) · fluctMoment β ξ(u) 0 λ i` on the closed cube
  (`evalF_dressedFamily`) and `Φ_j[g^{(i)}] = ∑_p β^p/p! fluctMoment β a p λ i Φ_j[cη * J^{*p}]`
  (`coeffFunctional_dressedFamily`).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open MonoRep CoeffFamily

/-! ### Taylor expansion of the fluctuation moments in the phase -/

theorem integral_abs_fluct_integrand_le (β a : ℝ) (hβ : 0 < β) (p : ℕ) {ν : ℝ} (hν : 0 < ν)
    (i : ℕ) :
    ∫ t in Ioi (0 : ℝ), |t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t| ≤
      phaseLogMoment β a ν i p := by
  unfold phaseLogMoment
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _)
    (integrableOn_logMajorant β a ν hβ hν i p)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := mem_Ioi.1 ht
  beta_reduce
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _),
    abs_of_nonneg (phaseKernel_nonneg _ _ _ _), abs_pow, abs_neg]
  unfold logMajorant
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht0.le _))
    (phaseKernel_nonneg _ _ _ _)
  exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log t)]) i

/-- **Taylor expansion of the fluctuation moments in the phase**:
`∑_p (β(b−a))^p/p! · fluctMoment β a p ν i = fluctMoment β b 0 ν i`. -/
theorem hasSum_fluctMoment_taylor (β a b : ℝ) (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν) (i : ℕ) :
    HasSum (fun p : ℕ => (β * (b - a)) ^ p / (p.factorial : ℝ) * fluctMoment β a p ν i)
      (fluctMoment β b 0 ν i) := by
  set F : ℕ → ℝ → ℝ := fun p t => (β * (b - a)) ^ p / (p.factorial : ℝ) *
    (t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t) with hF
  have hint : ∀ p, Integrable (F p) (volume.restrict (Ioi 0)) := fun p =>
    (integrableOn_fluct β a hβ p hν i).const_mul _
  have hnorm : Summable fun p => ∫ t, ‖F p t‖ ∂(volume.restrict (Ioi 0)) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
      (fun p => ?_) (summable_phaseLogMoment_series β a |b - a| ν hβ hν (abs_nonneg _) i)
    have : (fun t => ‖F p t‖) = fun t => |(β * (b - a)) ^ p / (p.factorial : ℝ)| *
        |t ^ (ν - 1) * (-Real.log t) ^ i * phaseKernel β a p t| := by
      funext t
      simp only [hF, Real.norm_eq_abs, abs_mul]
    rw [this, integral_const_mul]
    have habs : |(β * (b - a)) ^ p / (p.factorial : ℝ)| =
        (β * |b - a|) ^ p / (p.factorial : ℝ) := by
      rw [abs_div, abs_pow, abs_mul, abs_of_pos hβ, Nat.abs_cast]
    rw [habs]
    exact mul_le_mul_of_nonneg_left (integral_abs_fluct_integrand_le β a hβ p hν i)
      (by positivity)
  have hsum := hasSum_integral_of_summable_integral_norm hint hnorm
  have hL : ∫ t, ∑' p, F p t ∂(volume.restrict (Ioi 0)) = fluctMoment β b 0 ν i := by
    unfold fluctMoment
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := mem_Ioi.1 ht
    have hpt : ∀ p : ℕ, F p t = (t ^ (ν - 1) * (-Real.log t) ^ i *
        Real.exp (-(β * t) + β * Real.sqrt t * a)) *
        ((β * (b - a) * Real.sqrt t) ^ p / (p.factorial : ℝ)) := by
      intro p
      simp only [hF, phaseKernel]
      rw [mul_pow (β * (b - a)) (Real.sqrt t) p]
      ring
    simp_rw [hpt]
    rw [tsum_mul_left, tsum_pow_div_factorial, phaseKernel, pow_zero, one_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  rw [hL] at hsum
  refine hsum.congr_fun fun p => ?_
  simp only [hF]
  rw [integral_const_mul]
  rfl

/-! ### Evaluation of convolution powers and of the constant-free part -/

variable {d : ℕ}

theorem evalF_convPow {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : ∀ p, evalF (CoeffFamily.convPow c p) u = (evalF c u) ^ p
  | 0 => by
    unfold evalF CoeffFamily.convPow
    have : ∀ γ : Fin d → ℕ, (if γ = 0 then (1 : ℝ) else 0) * mono γ u =
        if γ = 0 then mono γ u else 0 := fun γ => by split_ifs <;> simp
    simp_rw [this]
    rw [tsum_ite_eq, pow_zero]
    simp [mono]
  | p + 1 => by
    unfold CoeffFamily.convPow
    rw [evalF_conv hc (hc.convPow p) hu, evalF_convPow hc hu p, pow_succ']

theorem evalF_fluctFamily {c : CoeffFamily d} (hc : AbsSummable c) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) : evalF (fluctFamily c) u = evalF c u - c 0 := by
  unfold evalF fluctFamily
  have hs : Summable fun γ : Fin d → ℕ => if γ = 0 then c 0 * mono γ u else 0 :=
    (hasSum_ite_eq (0 : Fin d → ℕ) (c 0 * mono 0 u)).summable.congr fun γ => by
      split_ifs with hγ
      · subst hγ
        rfl
      · rfl
  have : ∀ γ : Fin d → ℕ, (if γ = 0 then (0 : ℝ) else c γ) * mono γ u =
      c γ * mono γ u - if γ = 0 then c 0 * mono γ u else 0 := fun γ => by
    split_ifs with hγ
    · subst hγ
      ring
    · ring
  simp_rw [this]
  rw [(summable_term hc hu).tsum_sub hs, tsum_ite_eq]
  simp [mono]

/-! ### The dressed family -/

/-- The `p`-th dressed term `β^p/p! fluctMoment β a p μ i · (cη * J^{*p})`. -/
noncomputable def dressedTerm (β : ℝ) (cξ cη : CoeffFamily d) (μ : ℝ) (i p : ℕ) :
    CoeffFamily d :=
  fun γ => β ^ p / (p.factorial : ℝ) * fluctMoment β (cξ 0) p μ i *
    CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p) γ

/-- The phase-dressed amplitude family `g^{(i)} = ∑_p dressedTerm p`. -/
noncomputable def dressedFamily (β : ℝ) (cξ cη : CoeffFamily d) (μ : ℝ) (i : ℕ) :
    CoeffFamily d :=
  fun γ => ∑' p, dressedTerm β cξ cη μ i p γ

theorem absSummable_dressedTerm {β : ℝ} {cξ cη : CoeffFamily d} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) (μ : ℝ) (i p : ℕ) : AbsSummable (dressedTerm β cξ cη μ i p) := by
  unfold dressedTerm AbsSummable
  have := ((hη.conv (hξ.fluctFamily.convPow p)).mul_left
    |β ^ p / (p.factorial : ℝ) * fluctMoment β (cξ 0) p μ i|)
  refine this.congr fun γ => ?_
  beta_reduce
  simp only [abs_mul]

/-- The Tonelli majorant of the dressed double series. -/
theorem summable_tsum_abs_dressedTerm {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    Summable fun p => ∑' γ, |dressedTerm β cξ cη μ i p γ| := by
  have hmaj := (summable_phaseLogMoment_series β (cξ 0) (mass (fluctFamily cξ)) μ hβ hμ
    (mass_nonneg _) i).mul_left (mass cη)
  refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun γ => abs_nonneg _) (fun p => ?_) hmaj
  have h1 : (∑' γ, |dressedTerm β cξ cη μ i p γ|) =
      |β ^ p / (p.factorial : ℝ) * fluctMoment β (cξ 0) p μ i| *
        mass (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p)) := by
    unfold mass dressedTerm
    rw [← tsum_mul_left]
    refine tsum_congr fun γ => ?_
    rw [abs_mul]
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ))]
  have hfm := abs_fluctMoment_le β (cξ 0) hβ p hμ (le_refl i)
  have hmass := (mass_conv_le hη (hξ.fluctFamily.convPow p)).trans
    (mul_le_mul_of_nonneg_left (mass_convPow_le hξ.fluctFamily le_rfl p) (mass_nonneg _))
  calc β ^ p / (p.factorial : ℝ) * |fluctMoment β (cξ 0) p μ i| *
        mass (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p))
      ≤ β ^ p / (p.factorial : ℝ) * phaseLogMoment β (cξ 0) μ i p *
        (mass cη * mass (fluctFamily cξ) ^ p) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfm (by positivity)) hmass (mass_nonneg _)
          (mul_nonneg (by positivity) (phaseLogMoment_nonneg _ _ _ _ _))
    _ = mass cη * ((β * mass (fluctFamily cξ)) ^ p / (p.factorial : ℝ) *
        phaseLogMoment β (cξ 0) μ i p) := by
        rw [mul_pow]
        ring

/-- Absolute convergence of the dressed double series over `(p, γ)`. -/
theorem summable_dressedTerm_prod {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    Summable fun q : ℕ × (Fin d → ℕ) => |dressedTerm β cξ cη μ i q.1 q.2| :=
  (summable_prod_of_nonneg fun _ => abs_nonneg _).2
    ⟨fun p => absSummable_dressedTerm hξ hη μ i p, summable_tsum_abs_dressedTerm hβ hξ hη hμ i⟩

theorem summable_dressedTerm_fiber {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) (γ : Fin d → ℕ) :
    Summable fun p => dressedTerm β cξ cη μ i p γ :=
  Summable.of_norm (by
    have := (summable_dressedTerm_prod hβ hξ hη hμ i).prod_symm.prod_factor γ
    simpa [Real.norm_eq_abs] using this)

/-- **The dressed family is absolutely summable.** -/
theorem absSummable_dressedFamily {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d}
    (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) :
    AbsSummable (dressedFamily β cξ cη μ i) := by
  have hcol : Summable fun γ : Fin d → ℕ => ∑' p, |dressedTerm β cξ cη μ i p γ| :=
    ((summable_prod_of_nonneg fun _ => abs_nonneg _).1
      (summable_dressedTerm_prod hβ hξ hη hμ i).prod_symm).2
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun γ => ?_) hcol
  unfold dressedFamily
  have := norm_tsum_le_tsum_norm (f := fun p => dressedTerm β cξ cη μ i p γ) (by
    have := (summable_dressedTerm_prod hβ hξ hη hμ i).prod_symm.prod_factor γ
    simpa [Real.norm_eq_abs] using this)
  simpa [Real.norm_eq_abs] using this

/-- **Exchange of the dressed sum with a bounded weight**:
`∑_γ g^{(i)}_γ φ_γ = ∑_p ∑_γ (dressedTerm p)_γ φ_γ` for `|φ| ≤ M`. -/
theorem tsum_dressedFamily_mul {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) {φ : (Fin d → ℕ) → ℝ} {M : ℝ}
    (hφ : ∀ γ, |φ γ| ≤ M) :
    ∑' γ, dressedFamily β cξ cη μ i γ * φ γ =
      ∑' p, ∑' γ, dressedTerm β cξ cη μ i p γ * φ γ := by
  have hprod := summable_dressedTerm_prod hβ hξ hη hμ i
  have hunc : Summable (Function.uncurry fun p γ => dressedTerm β cξ cη μ i p γ * φ γ) := by
    refine Summable.of_norm_bounded (hprod.mul_right M) fun q => ?_
    change ‖dressedTerm β cξ cη μ i q.1 q.2 * φ q.2‖ ≤ |dressedTerm β cξ cη μ i q.1 q.2| * M
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _)
  have h₁ : ∀ p, Summable fun γ => dressedTerm β cξ cη μ i p γ * φ γ := fun p =>
    hunc.prod_factor p
  have h₂ : ∀ γ, Summable fun p => dressedTerm β cξ cη μ i p γ * φ γ := fun γ =>
    hunc.prod_symm.prod_factor γ
  unfold dressedFamily
  rw [← Summable.tsum_comm' hunc h₁ h₂]
  refine tsum_congr fun γ => ?_
  rw [tsum_mul_right]

/-! ### Evaluation and coefficient functionals of the dressed family -/

/-- **Evaluation of the dressed family**: `g^{(i)}(u) = η(u) · fluctMoment β ξ(u) 0 μ i` on the
closed cube. -/
theorem evalF_dressedFamily {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily d} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) {μ : ℝ} (hμ : 0 < μ) (i : ℕ) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    evalF (dressedFamily β cξ cη μ i) u = evalF cη u * fluctMoment β (evalF cξ u) 0 μ i := by
  change (∑' γ, dressedFamily β cξ cη μ i γ * mono γ u) = _
  rw [tsum_dressedFamily_mul hβ hξ hη hμ i (φ := fun γ => mono γ u) (M := 1) fun γ => by
    rw [abs_of_nonneg (mono_nonneg hu)]; exact mono_le_one hu]
  have hp : ∀ p, (∑' γ, dressedTerm β cξ cη μ i p γ * mono γ u) =
      evalF cη u * ((β * (evalF cξ u - cξ 0)) ^ p / (p.factorial : ℝ) *
        fluctMoment β (cξ 0) p μ i) := by
    intro p
    unfold dressedTerm
    simp_rw [mul_assoc]
    rw [tsum_mul_left, tsum_mul_left]
    have : (∑' γ, CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p) γ * mono γ u) =
        evalF cη u * (evalF cξ u - cξ 0) ^ p := by
      change evalF (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p)) u = _
      rw [evalF_conv hη (hξ.fluctFamily.convPow p) hu, evalF_convPow hξ.fluctFamily hu,
        evalF_fluctFamily hξ hu]
    rw [this, mul_pow]
    ring
  simp_rw [hp]
  rw [tsum_mul_left, (hasSum_fluctMoment_taylor β (cξ 0) (evalF cξ u) hβ hμ i).tsum_eq]

/-- **Coefficient functionals of the dressed family**:
`Φ_j[g^{(i)}] = ∑_p β^p/p! fluctMoment β a p λ i · Φ_j[cη * J^{*p}]`. -/
theorem coeffFunctional_dressedFamily (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) (i j : ℕ) :
    coeffFunctional n h k l j (dressedFamily β cξ cη l i) =
      ∑' p, β ^ p / (p.factorial : ℝ) * fluctMoment β (cξ 0) p l i *
        coeffFunctional n h k l j
          (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily cξ) p)) := by
  unfold coeffFunctional
  rw [tsum_dressedFamily_mul hβ hξ hη hl i
    (φ := fun γ => PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) l j)
    (M := ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n)
    fun γ => abs_coeffAt_stateDensityRep_le n (h + γ) k hk l j, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  unfold dressedTerm
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left]
  ring

end Grammar
