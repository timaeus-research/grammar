/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneratingUniform
import Grammar.JetProductCalculus
import Grammar.CubeJetsGeneral

/-!
# The generating identity on the completed cube jets (§20, Stage E)

The generating terms `a_r(ζ) = (1/r!) c^pop_{μ+r/2,q}(η (u^k ζ)^r)` depend on the field only
through its jets of order `cubeOrder h k μ` on the cube — the SAME order for every `r` — because
they are family coefficients at the fixed depth `2kL − h` (`empCoeffAtDepthFam_expTermFam_eq`).
Here:

* `exists_empCoeffAtDepthFam_expTermFam_sub_le`: the family coefficient of `τ^r η ζ^r` is
  Lipschitz in the jets of `ζ` on jet balls (linearity by uniqueness, the `O(C)` bound, jet
  calculus for `η ζ^r`, and `τ^r ≤ r! e^τ` for the envelope);
* `exists_genTerm_sub_le`: the same on cubes for the generating terms;
* `genTermOnClosedJets η h k R b μ q r : ClosedCubeJets d R b → ℝ`, the continuous extension of
  `a_r` to the closed realizable cube jets (Lipschitz on bounded sets, `closureExtend`);
* ★★ `exists_generatingTail_bound_closedJets`: the geometric tail estimate on bounded sets of the
  closed jets;
* ★★★ `hasSum_genTermOnClosedJets`: on EVERY closed realizable cube jet `z`,
  `Σ_r genTermOnClosedJets … r z = cubeCoeffGenOnClosedJets η h k R b μ q z`
  (unconditionally convergent) — the jet-space generating identity (Astra #157, Stage E).

Zero `sorry`/`axiom`.
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} (h k p : Fin d → ℕ)

/-! ### Lipschitz dependence of the population terms on the jets, at fixed depth -/

/-- ★ The family coefficient of `τ^r η ζ^r` at fixed depth is Lipschitz in the jets of `ζ` of
order `|p|` on the unit box, uniformly on jet balls (`ε ≤ E`). -/
theorem exists_empCoeffAtDepthFam_expTermFam_sub_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i)
    {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (r : ℕ)
    {B E : ℝ} (hB : 0 ≤ B) (hE : 1 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (∑ i, p i) (closedBox d 1) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ E →
      JetClose (∑ i, p i) (closedBox d 1) ζ₁ ζ₂ ε → ∀ μ ∈ latticeBelow (Qamb k) L, ∀ q ≤ d - 1,
        |empCoeffAtDepthFam (expTermFam η ζ₁ r) h k p μ q -
          empCoeffAtDepthFam (expTermFam η ζ₂ r) h k p μ q| ≤ K * ε := by
  set P : ℕ := ∑ i, p i with hP
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepthFam_single_le h k p hk hp hp0 1
  obtain ⟨Bη, hBη0, hBη⟩ := exists_jetBoundOn hη P (isCompact_closedBox 1)
  obtain ⟨Cp, hCp0, hCp⟩ := exists_jetClose_pow P (closedBox d 1) (B := B + E) (by linarith) r
  refine ⟨(r.factorial : ℝ) * (2 ^ P * Bη * Cp) * K₁, by positivity,
    fun ζ₁ ζ₂ hζ₁ hζ₂ hζ₂B ε hε0 hεE hclose μ hμ q hq => ?_⟩
  have hζ₁B : JetBoundOn P (closedBox d 1) ζ₁ (B + E) :=
    (hζ₂B.of_jetClose hclose).mono_of_le (by linarith)
  have hζ₂B' : JetBoundOn P (closedBox d 1) ζ₂ (B + E) := hζ₂B.mono_of_le (by linarith)
  have hpow := hCp ζ₁ ζ₂ hζ₁ hζ₂ hζ₁B hζ₂B' ε hε0 hclose
  have hw : JetClose P (closedBox d 1) (fun v => η v * ζ₁ v ^ r) (fun v => η v * ζ₂ v ^ r)
      (2 ^ P * Bη * (Cp * ε)) :=
    JetClose.mul_left hη hBη hBη0 (hζ₁.pow r) (hζ₂.pow r) (by positivity) hpow
  have hdiff : ContDiff ℝ ∞ fun v => η v * ζ₁ v ^ r - η v * ζ₂ v ^ r :=
    (hη.mul (hζ₁.pow r)).sub (hη.mul (hζ₂.pow r))
  -- the difference family and its jet bound
  have hDj : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      expTermFam η ζ₁ r z.1 z.2 + (-1) * expTermFam η ζ₂ r z.1 z.2 :=
    contDiff_joint_add (A := expTermFam η ζ₁ r) (B := fun τ v => (-1) * expTermFam η ζ₂ r τ v)
      (contDiff_expTermFam_joint hη hζ₁ r)
      (contDiff_joint_const_mul (contDiff_expTermFam_joint hη hζ₂ r) (-1))
  have hDB : FamJetBound (fun τ v => expTermFam η ζ₁ r τ v + (-1) * expTermFam η ζ₂ r τ v) p 1
      ((r.factorial : ℝ) * (2 ^ P * Bη * (Cp * ε))) 1 := by
    intro m hm τ hτ v hv
    have hDeq : (fun v => expTermFam η ζ₁ r τ v + (-1) * expTermFam η ζ₂ r τ v) =
        fun v => τ ^ r * (η v * ζ₁ v ^ r - η v * ζ₂ v ^ r) := by
      funext v
      simp only [expTermFam]
      ring
    have hr : ∑ i, m i ≤ P := Finset.sum_le_sum fun i _ => hm i
    have h1 := congrFun (pdMulti_fun_const_mul (τ ^ r) hdiff m (List.finRange d)) v
    change |pdMulti m (List.finRange d)
      (fun v => expTermFam η ζ₁ r τ v + (-1) * expTermFam η ζ₂ r τ v) v| ≤ _
    rw [hDeq, h1, abs_mul, abs_of_nonneg (pow_nonneg hτ r)]
    have h2 : |pdMulti m (List.finRange d) (fun v => η v * ζ₁ v ^ r - η v * ζ₂ v ^ r) v| ≤
        2 ^ P * Bη * (Cp * ε) := by
      refine (abs_pdMulti_finRange_le_norm_iteratedFDeriv hdiff m v).trans ?_
      have hfun : (fun v => η v * ζ₁ v ^ r - η v * ζ₂ v ^ r) =
          (fun v => η v * ζ₁ v ^ r) - fun v => η v * ζ₂ v ^ r := rfl
      rw [hfun, iteratedFDeriv_sub_apply
        ((hη.mul (hζ₁.pow r)).of_le (natCast_le_infty _)).contDiffAt
        ((hη.mul (hζ₂.pow r)).of_le (natCast_le_infty _)).contDiffAt]
      exact hw _ hr v hv
    have h3 : τ ^ r ≤ r.factorial * exp (1 * τ) := by
      have := Real.pow_div_factorial_le_exp τ hτ r
      rw [one_mul]
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have h4 : (1 : ℝ) ≤ (1 + τ) ^ P := one_le_pow₀ (by linarith)
    calc τ ^ r * |pdMulti m (List.finRange d) (fun v => η v * ζ₁ v ^ r - η v * ζ₂ v ^ r) v|
        ≤ (r.factorial * exp (1 * τ)) * (2 ^ P * Bη * (Cp * ε)) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = (r.factorial : ℝ) * (2 ^ P * Bη * (Cp * ε)) * 1 * exp (1 * τ) := by ring
      _ ≤ (r.factorial : ℝ) * (2 ^ P * Bη * (Cp * ε)) * (1 + τ) ^ P * exp (1 * τ) := by
          gcongr
  -- linearity by uniqueness
  obtain ⟨C₁, hC₁⟩ := exists_famJetBound_expTermFam hη hζ₁ r p
  obtain ⟨C₂, hC₂⟩ := exists_famJetBound_expTermFam hη hζ₂ r p
  have hlin : empCoeffAtDepthFam
      (fun τ v => expTermFam η ζ₁ r τ v + (-1) * expTermFam η ζ₂ r τ v) h k p μ q =
      empCoeffAtDepthFam (expTermFam η ζ₁ r) h k p μ q +
        (-1) * empCoeffAtDepthFam (expTermFam η ζ₂ r) h k p μ q := by
    have := empCoeffAtDepthFam_add h k p (contDiff_expTermFam_joint hη hζ₁ r)
      (contDiff_joint_const_mul (contDiff_expTermFam_joint hη hζ₂ r) (-1)) hC₁
      (hC₂.const_mul (contDiff_expTermFam_joint hη hζ₂ r) (-1)) hk hL hp hp0 hμ hq
    rw [this, empCoeffAtDepthFam_const_mul h k p (contDiff_expTermFam_joint hη hζ₂ r) (-1) hC₂
      hk hL hp hp0 hμ hq]
  have hbound := hK₁ _ hDj _ hDB μ hμ q hq
  rw [hlin] at hbound
  calc |empCoeffAtDepthFam (expTermFam η ζ₁ r) h k p μ q -
        empCoeffAtDepthFam (expTermFam η ζ₂ r) h k p μ q|
      = |empCoeffAtDepthFam (expTermFam η ζ₁ r) h k p μ q +
          (-1) * empCoeffAtDepthFam (expTermFam η ζ₂ r) h k p μ q| := by ring_nf
    _ ≤ (r.factorial : ℝ) * (2 ^ P * Bη * (Cp * ε)) * K₁ := hbound
    _ = (r.factorial : ℝ) * (2 ^ P * Bη * Cp) * K₁ * ε := by ring

/-- ★ **The generating terms are Lipschitz in the jets of order `cubeOrder h k μ` on the cube,
uniformly on jet balls** (`ε ≤ 1`). -/
theorem exists_genTerm_sub_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (μ : ℝ) (q r : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ 1 →
      JetClose (cubeOrder h k μ) (closedBox d b) ζ₁ ζ₂ ε → (∃ m : ℕ, μ = (m : ℝ) / Qamb k) →
        |(1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ₁ v) ^ r)
            (fun _ => 0) h k (fun _ => b) (μ + r / 2) q -
          (1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ₂ v) ^ r)
            (fun _ => 0) h k (fun _ => b) (μ + r / 2) q| ≤ K * ε := by
  have hQ := Qamb_pos k hk
  have hL₀ : L₀ h ≤ cutoffOf h μ := L₀_le_cutoffOf h μ
  have hL : 0 < cutoffOf h μ := lt_of_lt_of_le (by unfold L₀; omega) hL₀
  have hp := depthOf_add hk hL₀ (k := k)
  have hp0 := depthOf_pos hk hL₀ (k := k)
  set P : ℕ := cubeOrder h k μ with hPdef
  have hPeq : P = ∑ i, depthOf h k (cutoffOf h μ) i := rfl
  have hηd : ContDiff ℝ ∞ (η ∘ diag (fun _ : Fin d => b)) := hη.comp (contDiff_diag _)
  have hE1 : (1 : ℝ) ≤ (max 1 b) ^ P := one_le_pow₀ (le_max_left _ _)
  obtain ⟨Ku, hKu0, hKu⟩ := exists_empCoeffAtDepthFam_expTermFam_sub_le h k
    (depthOf h k (cutoffOf h μ)) hηd hk hL hp hp0 r (B := (max 1 b) ^ P * B)
    (E := (max 1 b) ^ P) (by positivity) hE1
  set β : ℝ := mono (fun i => 2 * k i) (fun _ : Fin d => b) with hβ
  set A : ℝ := (∏ i : Fin d, (fun _ : Fin d => b) i) * mono h (fun _ : Fin d => b) with hA
  set W : ℝ := ∑ j ∈ Finset.Ico q (d - 1 + 1), |(j.choose q : ℝ) * Real.log β ^ (j - q)| with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|A * β ^ (-μ)| * W * ((1 / (r.factorial : ℝ)) * (Ku * (max 1 b) ^ P)), by positivity,
    fun ζ₁ ζ₂ hζ₁ hζ₂ hζ₂B ε hε0 hε1 hclose hμ => ?_⟩
  have hμL : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) :=
    (mem_latticeBelow_iff hQ).2 ⟨hμ, lt_cutoffOf h μ⟩
  have hζd₁ : ContDiff ℝ ∞ (ζ₁ ∘ diag (fun _ : Fin d => b)) := hζ₁.comp (contDiff_diag _)
  have hζd₂ : ContDiff ℝ ∞ (ζ₂ ∘ diag (fun _ : Fin d => b)) := hζ₂.comp (contDiff_diag _)
  have hζdB : JetBoundOn P (closedBox d 1) (ζ₂ ∘ diag (fun _ : Fin d => b))
      ((max 1 b) ^ P * B) := jetBoundOn_comp_diag hζ₂ hb hB hζ₂B
  have hζdc : JetClose P (closedBox d 1) (ζ₁ ∘ diag (fun _ : Fin d => b))
      (ζ₂ ∘ diag (fun _ : Fin d => b)) ((max 1 b) ^ P * ε) :=
    jetClose_comp_diag hζ₁ hζ₂ hb hε0 hclose
  have hεE : (max 1 b) ^ P * ε ≤ (max 1 b) ^ P := by
    calc (max 1 b) ^ P * ε ≤ (max 1 b) ^ P * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
      _ = _ := mul_one _
  have hμr : ∃ m : ℕ, μ + (r : ℝ) / 2 = (m : ℝ) / Qamb k := by
    obtain ⟨m, hm⟩ := hμ
    obtain ⟨m₀, hm₀⟩ := half_mem_lattice k hk r
    exact ⟨m + m₀, by rw [hm, hm₀]; push_cast; ring⟩
  -- the unit-box population terms as family coefficients at the fixed depth
  have hconv : ∀ ζ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ → ∀ j ≤ d - 1,
      empCoeff (fun v => (η ∘ diag (fun _ : Fin d => b)) v *
          (mono k v * (ζ ∘ diag (fun _ : Fin d => b)) v) ^ r) (fun _ => 0) h k (μ + r / 2) j =
      empCoeffAtDepthFam (expTermFam (η ∘ diag (fun _ : Fin d => b))
        (ζ ∘ diag (fun _ : Fin d => b)) r) h k (depthOf h k (cutoffOf h μ)) μ j := by
    intro ζ hζ j hj
    rw [empCoeff_monomial_absorb hηd (hζ.comp (contDiff_diag _)) hk r hμr hj,
      empCoeffAtDepthFam_expTermFam_eq hηd (hζ.comp (contDiff_diag _)) hk hL hp hp0 r hμL hj]
  rw [inv_factorial_mul_empCoeffRect_pow_eq h k hη hζ₁ hk (fun _ => hb) hμ q r,
    inv_factorial_mul_empCoeffRect_pow_eq h k hη hζ₂ hk (fun _ => hb) hμ q r, ← hβ, ← hA,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
  have hj : ∀ j ∈ Finset.Ico q (d - 1 + 1),
      |((j.choose q : ℝ) * Real.log β ^ (j - q)) * ((1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag (fun _ : Fin d => b)) v *
            (mono k v * (ζ₁ ∘ diag (fun _ : Fin d => b)) v) ^ r) (fun _ => 0) h k (μ + r / 2) j) -
        ((j.choose q : ℝ) * Real.log β ^ (j - q)) * ((1 / (r.factorial : ℝ)) *
          empCoeff (fun v => (η ∘ diag (fun _ : Fin d => b)) v *
            (mono k v * (ζ₂ ∘ diag (fun _ : Fin d => b)) v) ^ r) (fun _ => 0) h k (μ + r / 2) j)|
        ≤ |(j.choose q : ℝ) * Real.log β ^ (j - q)| *
          ((1 / (r.factorial : ℝ)) * (Ku * (max 1 b) ^ P) * ε) := by
    intro j hj
    have hqj : j ≤ d - 1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
    have hpos : (0 : ℝ) < 1 / r.factorial := by positivity
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul (1 / (r.factorial : ℝ)), abs_of_pos hpos,
      hconv ζ₁ hζ₁ j hqj, hconv ζ₂ hζ₂ j hqj]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    have := hKu _ _ hζd₁ hζd₂ hζdB _ (by positivity) hεE hζdc μ hμL j hqj
    calc _ ≤ Ku * ((max 1 b) ^ P * ε) := this
      _ = Ku * (max 1 b) ^ P * ε := by ring
  calc |A * β ^ (-μ)| * |∑ j ∈ Finset.Ico q (d - 1 + 1), _| ≤ |A * β ^ (-μ)| *
        ∑ j ∈ Finset.Ico q (d - 1 + 1), |(j.choose q : ℝ) * Real.log β ^ (j - q)| *
          ((1 / (r.factorial : ℝ)) * (Ku * (max 1 b) ^ P) * ε) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hj))
          (abs_nonneg _)
    _ = |A * β ^ (-μ)| * W * ((1 / (r.factorial : ℝ)) * (Ku * (max 1 b) ^ P)) * ε := by
        rw [← Finset.sum_mul]
        ring

/-! ### The generating terms on the closed realizable cube jets -/

/-- Two smooth fields with the same cube jets of order `≥ cubeOrder h k μ` have the same
generating terms. -/
theorem genTerm_eq_of_cubeJet_eq (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k)
    {ζ₁ ζ₂ : (Fin d → ℝ) → ℝ} (hζ₁ : ContDiff ℝ ∞ ζ₁) (hζ₂ : ContDiff ℝ ∞ ζ₂)
    (heq : cubeJet R b ζ₁ hζ₁ = cubeJet R b ζ₂ hζ₂) :
    (1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ₁ v) ^ r) (fun _ => 0) h k
        (fun _ => b) (μ + r / 2) q =
      (1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ₂ v) ^ r) (fun _ => 0)
        h k (fun _ => b) (μ + r / 2) q := by
  obtain ⟨K, -, hK⟩ := exists_genTerm_sub_le h k hη hk hb μ q r (norm_nonneg (cubeJet R b ζ₂ hζ₂))
  have hclose : JetClose (cubeOrder h k μ) (closedBox d b) ζ₁ ζ₂ 0 :=
    (jetClose_of_norm_cubeJet_sub_le (by rw [heq, sub_self, norm_zero])).of_le_order hR
  have hbound : JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ₂ ‖cubeJet R b ζ₂ hζ₂‖ :=
    (jetBoundOn_of_norm_cubeJet_le le_rfl).of_le_order hR
  have := hK ζ₁ ζ₂ hζ₁ hζ₂ hbound 0 le_rfl zero_le_one hclose hμ
  rw [mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

open Classical in
/-- The `r`-th generating term `(1/r!) c^pop_{μ+r/2,q}(η (u^k ζ)^r)` as a function of the cube
jets of `ζ` (`0` off the realizable jets). -/
noncomputable def genTermGen' (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ) (b μ : ℝ)
    (q r : ℕ) (z : CubeJetSpace d R b) : ℝ :=
  if hz : z ∈ cubeRealizable d R b then
    (1 / (r.factorial : ℝ)) * empCoeffRect
      (fun v => η v * (mono k v * (Classical.choose hz).1 v) ^ r) (fun _ => 0) h k (fun _ => b)
      (μ + r / 2) q
  else 0

theorem genTermGen'_cubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R) (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k)
    (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    genTermGen' η h k R b μ q r (cubeJet R b ζ hζ) =
      (1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k
        (fun _ => b) (μ + r / 2) q := by
  have hz := cubeJet_mem_cubeRealizable R b ζ hζ
  rw [genTermGen', dif_pos hz]
  exact genTerm_eq_of_cubeJet_eq h k hη hk hb μ q r hR hμ _ hζ (Classical.choose_spec hz)

theorem lipschitzOnBounded_genTermGen' (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) :
    LipschitzOnBounded (cubeRealizable d R b) (genTermGen' η h k R b μ q r) := by
  intro B hB
  obtain ⟨K, hK0, hK⟩ := exists_genTerm_sub_le h k hη hk hb μ q r hB
  refine ⟨K, hK0, ?_⟩
  rintro x ⟨ζ₁, rfl⟩ y ⟨ζ₂, rfl⟩ hy hxy
  rw [dist_eq_norm] at hxy ⊢
  rw [genTermGen'_cubeJet h k hη hk hb μ q r hR hμ, genTermGen'_cubeJet h k hη hk hb μ q r hR hμ]
  exact hK ζ₁.1 ζ₂.1 ζ₁.2 ζ₂.2 ((jetBoundOn_of_norm_cubeJet_le hy).of_le_order hR) _
    (norm_nonneg _) hxy ((jetClose_of_norm_cubeJet_sub_le le_rfl).of_le_order hR) hμ

/-- The `r`-th generating term extended to the closed realizable cube jets. -/
noncomputable def genTermOnClosedJets (η : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ) (R : ℕ) (b μ : ℝ)
    (q r : ℕ) (z : ClosedCubeJets d R b) : ℝ :=
  closureExtend (cubeRealizable d R b) (genTermGen' η h k R b μ q r) z

theorem genTermOnClosedJets_closedCubeJet (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (ζ : (Fin d → ℝ) → ℝ) (hζ : ContDiff ℝ ∞ ζ) :
    genTermOnClosedJets η h k R b μ q r (closedCubeJet R b ζ hζ) =
      (1 / (r.factorial : ℝ)) * empCoeffRect (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k
        (fun _ => b) (μ + r / 2) q := by
  rw [genTermOnClosedJets, closedCubeJet,
    (lipschitzOnBounded_genTermGen' h k hη hk hb μ q r hR hμ).closureExtend_of_mem
      (cubeJet_mem_cubeRealizable R b ζ hζ)]
  exact genTermGen'_cubeJet h k hη hk hb μ q r hR hμ ζ hζ

theorem continuous_genTermOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) : Continuous (genTermOnClosedJets η h k R b μ q r) :=
  (lipschitzOnBounded_genTermGen' h k hη hk hb μ q r hR hμ).continuous_closureExtend

theorem measurable_genTermOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q r : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) : Measurable (genTermOnClosedJets η h k R b μ q r) :=
  (continuous_genTermOnClosedJets h k hη hk hb μ q r hR hμ).measurable

/-- ★★ **The geometric tail estimate on bounded sets of the closed cube jets.** -/
theorem exists_generatingTail_bound_closedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ClosedCubeJets d R b, ‖z.1‖ ≤ B → ∀ R' : ℕ,
      |cubeCoeffGenOnClosedJets η h k R b μ q z -
        ∑ r ∈ range R', genTermOnClosedJets η h k R b μ q r z| ≤ C * (1 / 2) ^ R' := by
  obtain ⟨C, hC0, hC⟩ := exists_generatingTail_bound_jetBall_rect h k hη hk hb μ q (B := B + 1)
    (by linarith)
  refine ⟨C, hC0, fun z hz R' => ?_⟩
  obtain ⟨x, hxS, hxz⟩ := mem_closure_iff_seq_limit.1 z.2
  have hzn : Tendsto (fun n => (⟨x n, subset_closure (hxS n)⟩ : ClosedCubeJets d R b)) atTop
      (𝓝 z) := by
    rw [tendsto_subtype_rng]
    exact hxz
  have hF := ((continuous_cubeCoeffGenOnClosedJets hη hk hb μ q hR).tendsto z).comp hzn
  have hS : Tendsto (fun n => ∑ r ∈ range R', genTermOnClosedJets η h k R b μ q r
      (⟨x n, subset_closure (hxS n)⟩ : ClosedCubeJets d R b)) atTop
      (𝓝 (∑ r ∈ range R', genTermOnClosedJets η h k R b μ q r z)) :=
    tendsto_finsetSum _ fun r _ =>
      ((continuous_genTermOnClosedJets h k hη hk hb μ q r hR hμ).tendsto z).comp hzn
  have hnorm : ∀ᶠ n in atTop, ‖x n‖ < B + 1 :=
    hxz.norm.eventually (gt_mem_nhds (by linarith : ‖z.1‖ < B + 1))
  have hbound : ∀ᶠ n in atTop, |cubeCoeffGenOnClosedJets η h k R b μ q
      (⟨x n, subset_closure (hxS n)⟩ : ClosedCubeJets d R b) -
      ∑ r ∈ range R', genTermOnClosedJets η h k R b μ q r
        (⟨x n, subset_closure (hxS n)⟩ : ClosedCubeJets d R b)| ≤ C * (1 / 2) ^ R' := by
    filter_upwards [hnorm] with n hn
    obtain ⟨ζ, hζeq⟩ := hxS n
    have hζeq' : cubeJet R b ζ.1 ζ.2 = x n := hζeq
    have heq : (⟨x n, subset_closure (hxS n)⟩ : ClosedCubeJets d R b) =
        closedCubeJet R b ζ.1 ζ.2 := Subtype.ext hζeq'.symm
    rw [heq, cubeCoeffGenOnClosedJets_closedCubeJet hη hk hb μ q hR,
      Finset.sum_congr rfl fun r _ =>
        genTermOnClosedJets_closedCubeJet h k hη hk hb μ q r hR hμ ζ.1 ζ.2]
    have hxn : ‖cubeJet R b ζ.1 ζ.2‖ ≤ B + 1 := by
      rw [hζeq']
      exact hn.le
    have hζB : JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ.1 (B + 1) :=
      (jetBoundOn_of_norm_cubeJet_le hxn).of_le_order hR
    exact hC ζ.1 ζ.2 hζB hμ R'
  exact le_of_tendsto (hF.sub hS).abs hbound

/-- ★★★ **The jet-space generating identity**: on every closed realizable cube jet `z`,
`Σ_{r ≥ 0} genTermOnClosedJets η h k R b μ q r z = cubeCoeffGenOnClosedJets η h k R b μ q z`,
unconditionally convergent. -/
theorem hasSum_genTermOnClosedJets (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (q : ℕ) {R : ℕ} (hR : cubeOrder h k μ ≤ R)
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (z : ClosedCubeJets d R b) :
    HasSum (fun r => genTermOnClosedJets η h k R b μ q r z)
      (cubeCoeffGenOnClosedJets η h k R b μ q z) := by
  obtain ⟨C, hC0, hC⟩ := exists_generatingTail_bound_closedJets h k hη hk hb μ q hR hμ
    (norm_nonneg z.1)
  have hz := hC z le_rfl
  have hterm : ∀ r, |genTermOnClosedJets η h k R b μ q r z| ≤ 2 * C * (1 / 2) ^ r := fun r => by
    have h1 := hz r
    have h2 := hz (r + 1)
    have hsplit : genTermOnClosedJets η h k R b μ q r z =
        (cubeCoeffGenOnClosedJets η h k R b μ q z -
          ∑ i ∈ range r, genTermOnClosedJets η h k R b μ q i z) -
        (cubeCoeffGenOnClosedJets η h k R b μ q z -
          ∑ i ∈ range (r + 1), genTermOnClosedJets η h k R b μ q i z) := by
      rw [Finset.sum_range_succ]
      ring
    rw [hsplit]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ C * (1 / 2) ^ r + C * (1 / 2) ^ (r + 1) := add_le_add h1 h2
      _ ≤ 2 * C * (1 / 2) ^ r := by
          rw [pow_succ]
          nlinarith [hC0, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) r]
  have hsum : Summable fun r => ‖genTermOnClosedJets η h k R b μ q r z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hterm r)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (2 * C))
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsum, tendsto_iff_norm_sub_tendsto_zero]
  have hgeo : Tendsto (fun R' : ℕ => C * (1 / 2 : ℝ) ^ R') atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun R' => ?_) hgeo
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact hz R'

end Grammar
