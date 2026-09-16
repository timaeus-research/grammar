/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalTailJetUniform
import Grammar.EmpiricalGeneratingRect
import Grammar.EmpCoeffLipschitz

/-!
# The generating tail estimate, uniform on jet balls (§20, Stage E)

The truncation error of the generating identity is geometric UNIFORMLY over the fields in a jet
ball: for `JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ B`, one constant per
`(η, h, k, b, μ, q, B)`:

★ `exists_generatingTail_bound_jetBall_rect`:
`|empCoeffRect η ζ h k b μ q − Σ_{r<R} (1/r!) empCoeffRect (η (u^k ζ)^r) 0 h k b (μ + r/2) q|
   ≤ C (1/2)^R`  for every `R`.

Ingredients: the partial-sum identity `empCoeffAtDepth_eq_sum_add_tailCoeff` (coefficient =
finite generating sum + tail coefficient), the `O(C)` bound of the family coefficients with the
fixed envelope `M' = 3B`, the uniform tail jet bounds `famJetBound_tailFam_of_jetBoundOn`, and
jet transport under the dilation `diag b` (`jetBoundOn_comp_diag`).  This is the input for the
extension of the identity to the completed cube jets (Astra #157, Stage E).

Zero `sorry`/`axiom`.
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)

/-- The partial-sum identity: the coefficient is the finite generating sum plus the coefficient of
the tail family. -/
theorem empCoeffAtDepth_eq_sum_add_tailCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1)
    (R : ℕ) :
    empCoeffAtDepth η ζ h k p μ q =
      ∑ r ∈ range R, (1 / (r.factorial : ℝ)) * empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q +
        empCoeffAtDepthFam (tailFam η ζ R) h k p μ q := by
  obtain ⟨K₀, M', hK₀, hT⟩ := exists_famJetBound_tailFam hη hζ p
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
  have hc' : ∀ r : ℕ, empCoeffAtDepthFam (fun τ v => (1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v)
      h k p μ q = (1 / (r.factorial : ℝ)) * empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q :=
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
  induction R with
  | zero =>
    rw [Finset.sum_range_zero, zero_add, tailFam_zero]
    rfl
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, add_assoc, ← hc' R]
    congr 1
    have hfun : tailFam η ζ R = fun τ v =>
        (1 / (R.factorial : ℝ)) * expTermFam η ζ R τ v + tailFam η ζ (R + 1) τ v := by
      funext τ v
      rw [tailFam_succ]
      ring
    rw [hfun]
    exact empCoeffAtDepthFam_add h k p (hEj R) (hTj (R + 1)) (hE R) (hT (R + 1)) hk hL hp hp0
      hμ hq

/-- ★ **The generating tail estimate at fixed depth, uniform on jet balls.** -/
theorem exists_generatingTail_bound_jetBall (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {L : ℕ}
    (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (∑ i, p i) (closedBox d 1) ζ B →
      ∀ R : ℕ, ∀ μ ∈ latticeBelow (Qamb k) L, ∀ q ≤ d - 1,
        |empCoeffAtDepth η ζ h k p μ q - ∑ r ∈ range R,
          (1 / (r.factorial : ℝ)) * empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q| ≤
          C * (1 / 2) ^ R := by
  obtain ⟨C₀, hC₀, hT⟩ := famJetBound_tailFam_of_jetBoundOn hη p hB
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepthFam_single_le h k p hk hp hp0 (3 * B)
  refine ⟨C₀ * K₁, by positivity, fun ζ hζ hζB R μ hμ q hq => ?_⟩
  rw [empCoeffAtDepth_eq_sum_add_tailCoeff h k p hη hζ hk hL hp hp0 hμ hq R, add_sub_cancel_left]
  calc |empCoeffAtDepthFam (tailFam η ζ R) h k p μ q| ≤ C₀ * (1 / 2) ^ R * K₁ :=
        hK₁ _ (contDiff_tailFam_joint hη hζ R) _ (hT ζ hζ hζB R) μ hμ q hq
    _ = C₀ * K₁ * (1 / 2) ^ R := by ring

/-- ★ **The generating tail estimate for the canonical coefficients, uniform on jet balls of order
`cubeOrder h k μ`.** -/
theorem exists_generatingTail_bound_jetBall_empCoeff (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    (μ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (cubeOrder h k μ) (closedBox d 1) ζ B → (∃ m : ℕ, μ = (m : ℝ) / Qamb k) →
      ∀ q ≤ d - 1, ∀ R : ℕ,
        |empCoeff η ζ h k μ q - ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q|
          ≤ C * (1 / 2) ^ R := by
  have hQ := Qamb_pos k hk
  have hL₀ : L₀ h ≤ cutoffOf h μ := L₀_le_cutoffOf h μ
  have hL : 0 < cutoffOf h μ := lt_of_lt_of_le (by unfold L₀; omega) hL₀
  have hp := depthOf_add hk hL₀ (k := k)
  have hp0 := depthOf_pos hk hL₀ (k := k)
  obtain ⟨C, hC0, hC⟩ :=
    exists_generatingTail_bound_jetBall h k (depthOf h k (cutoffOf h μ)) hη hk hL hp hp0 hB
  refine ⟨C, hC0, fun ζ hζ hζB hμ q hq R => ?_⟩
  have hμL : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
    (mem_latticeBelow_iff hQ).2 ⟨hμ, lt_cutoffOf h μ⟩
  have hsum : ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
      empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k (μ + r / 2) q =
      ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
        empCoeffAtDepthFam (expTermFam η ζ r) h k (depthOf h k (cutoffOf h μ)) μ q :=
    Finset.sum_congr rfl fun r _ => by
      rw [empCoeffAtDepthFam_expTermFam_eq hη hζ hk hL hp hp0 r hμL hq]
  rw [hsum]
  exact hC ζ hζ hζB R μ hμL q hq

/-- Jet bounds of the dilated field on the unit box from jet bounds on the cube. -/
theorem jetBoundOn_comp_diag (hζ : ContDiff ℝ ∞ ζ) {b : ℝ} (hb : 0 < b) {P : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hbd : JetBoundOn P (closedBox d b) ζ B) :
    JetBoundOn P (closedBox d 1) (ζ ∘ diag (fun _ : Fin d => b)) ((max 1 b) ^ P * B) := by
  intro r hr x hx
  set g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := b • ContinuousLinearMap.id ℝ (Fin d → ℝ) with hg
  have hgn : ‖g‖ ≤ b := by
    calc ‖g‖ ≤ ‖b‖ * ‖ContinuousLinearMap.id ℝ (Fin d → ℝ)‖ := norm_smul_le _ _
      _ ≤ b * 1 := by
          rw [Real.norm_of_nonneg hb.le]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hb.le
      _ = b := mul_one b
  rw [diag_const_eq, ← hg,
    ContinuousLinearMap.iteratedFDeriv_comp_right g hζ x (natCast_le_infty r)]
  have hgx : g x ∈ closedBox d b := by
    have := diag_const_mem_closedBox hb.le hx
    rwa [diag_const_eq, ← hg] at this
  calc ‖(iteratedFDeriv ℝ r ζ (g x)).compContinuousLinearMap fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ r ζ (g x)‖ * ∏ _i : Fin r, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * (max 1 b) ^ P := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul (hbd r hr (g x) hgx) ?_ (by positivity) hB
        calc ‖g‖ ^ r ≤ (max 1 b) ^ r :=
              pow_le_pow_left₀ (norm_nonneg _) (hgn.trans (le_max_right _ _)) r
          _ ≤ (max 1 b) ^ P := pow_le_pow_right₀ (le_max_left _ _) hr
    _ = (max 1 b) ^ P * B := mul_comm _ _

/-- ★★ **The generating tail estimate on a cube, uniform on jet balls**: for every `(η, h, k, b, μ,
q, B)` one constant `C` with
`|empCoeffRect η ζ h k b μ q − Σ_{r<R} (1/r!) empCoeffRect (η (u^k ζ)^r) 0 h k b (μ + r/2) q|
  ≤ C (1/2)^R` for all smooth `ζ` with `JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ B`,
`μ ∈ Q⁻¹ℕ`, and all `R`. -/
theorem exists_generatingTail_bound_jetBall_rect (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    {b : ℝ} (hb : 0 < b) (μ : ℝ) (q : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ →
      JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ B → (∃ m : ℕ, μ = (m : ℝ) / Qamb k) →
      ∀ R : ℕ,
        |empCoeffRect η ζ h k (fun _ => b) μ q - ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k (fun _ => b)
            (μ + r / 2) q| ≤ C * (1 / 2) ^ R := by
  set bb : Fin d → ℝ := fun _ => b with hbb
  have hbb' : ∀ i, 0 < bb i := fun _ => hb
  set β : ℝ := mono (fun i => 2 * k i) bb with hβ
  set A : ℝ := (∏ i, bb i) * mono h bb with hA
  have hηd : ContDiff ℝ ∞ (η ∘ diag bb) := hη.comp (contDiff_diag bb)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_generatingTail_bound_jetBall_empCoeff h k hηd hk μ
    (B := (max 1 b) ^ cubeOrder h k μ * B) (by positivity)
  set W : ℝ := ∑ j ∈ Finset.Ico q (d - 1 + 1), |(j.choose q : ℝ) * Real.log β ^ (j - q)| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|A * β ^ (-μ)| * W * C₁, by positivity, fun ζ hζ hζB hμ R => ?_⟩
  have hζd : ContDiff ℝ ∞ (ζ ∘ diag bb) := hζ.comp (contDiff_diag bb)
  have hζdB : JetBoundOn (cubeOrder h k μ) (closedBox d 1) (ζ ∘ diag bb)
      ((max 1 b) ^ cubeOrder h k μ * B) := jetBoundOn_comp_diag hζ hb hB hζB
  have hterms : ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
      empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k bb (μ + r / 2) q =
      A * β ^ (-μ) * ∑ j ∈ Finset.Ico q (d - 1 + 1),
        ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag bb) v * (mono k v * (ζ ∘ diag bb) v) ^ r) (fun _ => 0) h k
            (μ + r / 2) j := by
    calc ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k bb (μ + r / 2) q
        = ∑ r ∈ range R, A * β ^ (-μ) * ∑ j ∈ Finset.Ico q (d - 1 + 1),
            ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ((1 / (r.factorial : ℝ)) *
              empCoeff (fun v => (η ∘ diag bb) v * (mono k v * (ζ ∘ diag bb) v) ^ r)
                (fun _ => 0) h k (μ + r / 2) j) :=
          Finset.sum_congr rfl fun r _ =>
            inv_factorial_mul_empCoeffRect_pow_eq h k hη hζ hk hbb' hμ q r
      _ = _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  rw [empCoeffRect_eq_scale_sum h k η ζ bb μ q, hterms, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul]
  have hj : ∀ j ∈ Finset.Ico q (d - 1 + 1),
      |((j.choose q : ℝ) * Real.log β ^ (j - q)) * empCoeff (η ∘ diag bb) (ζ ∘ diag bb) h k μ j -
        ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag bb) v * (mono k v * (ζ ∘ diag bb) v) ^ r) (fun _ => 0) h k
            (μ + r / 2) j| ≤ |(j.choose q : ℝ) * Real.log β ^ (j - q)| * (C₁ * (1 / 2) ^ R) := by
    intro j hj
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hqj : j ≤ d - 1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
    have := hC₁ (ζ ∘ diag bb) hζd hζdB hμ j hqj R
    -- transport the insertion form `η ζ^r` at `h + rk` to `η (u^k ζ)^r` at `h`
    have hsum : ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => (η ∘ diag bb) v * (mono k v * (ζ ∘ diag bb) v) ^ r) (fun _ => 0) h k
          (μ + r / 2) j = ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
        empCoeff (fun v => (η ∘ diag bb) v * (ζ ∘ diag bb) v ^ r) (fun _ => 0)
          (fun i => h i + r * k i) k (μ + r / 2) j := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have hμr : ∃ m : ℕ, μ + (r : ℝ) / 2 = (m : ℝ) / Qamb k := by
        obtain ⟨m, hm⟩ := hμ
        obtain ⟨m₀, hm₀⟩ := half_mem_lattice k hk r
        exact ⟨m + m₀, by rw [hm, hm₀]; push_cast; ring⟩
      rw [empCoeff_monomial_absorb hηd hζd hk r hμr hqj]
    rw [hsum]
    exact this
  calc |A * β ^ (-μ)| * |∑ j ∈ Finset.Ico q (d - 1 + 1), (((j.choose q : ℝ) *
        Real.log β ^ (j - q)) * empCoeff (η ∘ diag bb) (ζ ∘ diag bb) h k μ j -
        ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ∑ r ∈ range R, (1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag bb) v * (mono k v * (ζ ∘ diag bb) v) ^ r) (fun _ => 0) h k
            (μ + r / 2) j)|
      ≤ |A * β ^ (-μ)| * ∑ j ∈ Finset.Ico q (d - 1 + 1),
          |(j.choose q : ℝ) * Real.log β ^ (j - q)| * (C₁ * (1 / 2) ^ R) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hj))
          (abs_nonneg _)
    _ = |A * β ^ (-μ)| * W * C₁ * (1 / 2) ^ R := by
        rw [← Finset.sum_mul]
        ring

end Grammar
