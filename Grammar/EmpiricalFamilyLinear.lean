/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalMonomialFamily
import Grammar.EmpiricalUniform

/-!
# Linearity and bounds of the family coefficients (§20, generating identity)

* Linearity of the coordinate derivatives in the function (`pd_fun_add`, `pdMulti_fun_add`,
  `pdMulti_fun_sub`, `pdMulti_fun_const_mul`, `pdMulti_fun_sum`), hence jet bounds for sums of
  families.
* ★ `exists_abs_empCoeffAtDepthFam_le`: the family coefficients are `O(C)` for a family with jet
  bound `C` (the constant depends on `(h, k, p, L, M')` only) — the family version of
  `exists_abs_empCoeffAtDepth_le`.
* Linearity of the family coefficients in the family, BY UNIQUENESS of cutoff expansions
  (`empCoeffAtDepthFam_add`, `empCoeffAtDepthFam_const_mul`, `empCoeffAtDepthFam_sum`): both
  sides expand the same integral at the same cutoff, so they agree on the lattice.  No
  integrability bookkeeping through the face integrals is needed.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Linearity of the coordinate derivatives in the function -/

theorem pd_fun_add {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin d)
    (v : Fin d → ℝ) : pd i (fun v => f v + g v) v = pd i f v + pd i g v := by
  have h := (hasDerivAt_line hf i v (v i)).add (hasDerivAt_line hg i v (v i))
  have hl : line (fun v => f v + g v) i v = fun t => line f i v t + line g i v t := rfl
  unfold pd
  rw [hl]
  exact h.deriv

theorem pd_fun_const_mul (c : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (v : Fin d → ℝ) : pd i (fun v => c * f v) v = c * pd i f v := by
  have h := (hasDerivAt_line hf i v (v i)).const_mul c
  have hl : line (fun v => c * f v) i v = fun t => c * line f i v t := rfl
  unfold pd
  rw [hl]
  exact h.deriv

theorem pdPow_fun_add {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin d) (n : ℕ) :
    pdPow i n (fun v => f v + g v) = fun v => pdPow i n f v + pdPow i n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdPow_succ', pdPow_succ', pdPow_succ', ih]
    funext v
    exact pd_fun_add (contDiff_pdPow hf i n) (contDiff_pdPow hg i n) i v

theorem pdPow_fun_const_mul (c : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (n : ℕ) : pdPow i n (fun v => c * f v) = fun v => c * pdPow i n f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdPow_succ', pdPow_succ', ih]
    funext v
    exact pd_fun_const_mul c (contDiff_pdPow hf i n) i v

theorem pdMulti_fun_add {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => f v + g v) = fun v => pdMulti m l f v + pdMulti m l g v := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdMulti_cons, pdMulti_cons, ih]
    exact pdPow_fun_add (contDiff_pdMulti hf m l) (contDiff_pdMulti hg m l) i (m i)

theorem pdMulti_fun_const_mul (c : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => c * f v) = fun v => c * pdMulti m l f v := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [pdMulti_cons, pdMulti_cons, ih]
    exact pdPow_fun_const_mul c (contDiff_pdMulti hf m l) i (m i)

theorem pdMulti_fun_sub {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => f v - g v) = fun v => pdMulti m l f v - pdMulti m l g v := by
  have h1 : (fun v => f v - g v) = fun v => f v + (-1 : ℝ) * g v := by
    funext v; ring
  rw [h1, pdMulti_fun_add hf (contDiff_const.mul hg), pdMulti_fun_const_mul (-1) hg]
  funext v; ring

theorem pdMulti_fun_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin d → ℝ) → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (m : Fin d → ℕ) (l : List (Fin d)) :
    pdMulti m l (fun v => ∑ i ∈ s, f i v) = fun v => ∑ i ∈ s, pdMulti m l (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (fun _ : Fin d → ℝ => (0 : ℝ)) = fun v => (0 : ℝ) * (0 : ℝ) by funext; ring,
      pdMulti_fun_const_mul 0 contDiff_const]
    funext v; ring
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [pdMulti_fun_add (hf a (Finset.mem_insert_self a s))
      (ContDiff.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)) m l,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-! ### Jet bounds of sums of families -/

theorem FamJetBound.add {A B : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (hB : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => B z.1 z.2) {p : Fin d → ℕ} {b CA CB M' : ℝ}
    (hCA : FamJetBound A p b CA M') (hCB : FamJetBound B p b CB M') :
    FamJetBound (fun τ v => A τ v + B τ v) p b (CA + CB) M' := by
  intro m hm τ hτ v hv
  have h := congrFun (pdMulti_fun_add (contDiff_famSlice hA τ) (contDiff_famSlice hB τ) m
    (List.finRange d)) v
  change pdMulti m (List.finRange d) (fun v => A τ v + B τ v) v = _ at h
  rw [h]
  calc |pdMulti m (List.finRange d) (A τ) v + pdMulti m (List.finRange d) (B τ) v|
      ≤ |pdMulti m (List.finRange d) (A τ) v| + |pdMulti m (List.finRange d) (B τ) v| :=
        abs_add_le _ _
    _ ≤ CA * (1 + τ) ^ (∑ i, p i) * exp (M' * τ) + CB * (1 + τ) ^ (∑ i, p i) * exp (M' * τ) :=
        add_le_add (hCA m hm τ hτ v hv) (hCB m hm τ hτ v hv)
    _ = _ := by ring

theorem FamJetBound.const_mul {A : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) (c : ℝ) {p : Fin d → ℕ}
    {b C M' : ℝ} (hC : FamJetBound A p b C M') :
    FamJetBound (fun τ v => c * A τ v) p b (|c| * C) M' := by
  intro m hm τ hτ v hv
  have h := congrFun (pdMulti_fun_const_mul c (contDiff_famSlice hA τ) m (List.finRange d)) v
  change pdMulti m (List.finRange d) (fun v => c * A τ v) v = _ at h
  rw [h, abs_mul]
  calc |c| * |pdMulti m (List.finRange d) (A τ) v|
      ≤ |c| * (C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ)) :=
        mul_le_mul_of_nonneg_left (hC m hm τ hτ v hv) (abs_nonneg _)
    _ = _ := by ring

theorem contDiff_joint_add {A B : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (hB : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => B z.1 z.2) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2 + B z.1 z.2 := hA.add hB

theorem contDiff_joint_const_mul {A : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) (c : ℝ) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => c * A z.1 z.2 := contDiff_const.mul hA

/-! ### The coefficient bound -/

variable (h k p : Fin d → ℕ)

/-- ★ **The family coefficients are `O(C)`**: there is `K₁ = K₁(h,k,p,L,M')` such that for every
jointly smooth family with jet bound `C`,
`Σ_{μ ∈ Λ^Q_L} Σ_{j ≤ d−1} |empCoeffAtDepthFam A h k p μ j| ≤ C K₁`. -/
theorem exists_abs_empCoeffAtDepthFam_le (hk : ∀ i, 0 < k i) {L : ℕ}
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (A : ℝ → (Fin d → ℝ) → ℝ),
      ContDiff ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) →
      ∀ C : ℝ, FamJetBound A p 1 C M' →
        ∑ μ ∈ latticeBelow (Qamb k) L, ∑ j ∈ range (d - 1 + 1),
          |empCoeffAtDepthFam A h k p μ j| ≤ C * K₁ := by
  have hQ := Qamb_pos k hk
  choose Cc hCc0 hCc using fun (J : Finset (Fin d)) (e : Fin d → ℕ) =>
    exists_abs_empFaceCoef_le k (L : ℝ) J hk (∑ i, p i) M' e
  set P : Finset (Fin d) → ℝ := fun J => ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹
    with hP
  have hP0 : ∀ J, 0 ≤ P J := fun J => Finset.prod_nonneg fun i _ => by positivity
  set K₁ : ℝ := ∑ μ ∈ latticeBelow (Qamb k) L, ∑ q ∈ range (d - 1 + 1),
    ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q : ℝ) *
      (P x.1 * Cc x.1 (fun i => x.2 i + h i) *
        faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
          (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (faceW_nonneg _ _) (Finset.sum_nonneg fun j _ => ?_)
    have := hP0 x.1
    have := hCc0 x.1 (fun i => x.2 i + h i)
    have := faceMajorant_nonneg (fun i : {i // ¬ inJ x.1 i} => p i)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)
    positivity
  refine ⟨K₁, hK₁0, fun A hA C hC => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  rw [hK₁, Finset.mul_sum]
  refine Finset.sum_le_sum fun μ hμ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hμL : μ < L := ((mem_latticeBelow_iff hQ).1 hμ).2
  have hμ0 : 0 ≤ μ := by
    obtain ⟨m, rfl⟩ := ((mem_latticeBelow_iff hQ).1 hμ).1
    positivity
  unfold empCoeffAtDepthFam
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [abs_mul, abs_of_nonneg (faceW_nonneg _ _), mul_left_comm, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j hj => ?_)) (faceW_nonneg _ _)
  rw [abs_mul, Nat.abs_cast]
  have hjD : j ≤ DJ x.1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
  have hgrow : ∀ w ∈ box {i // ¬ inJ x.1 i} 1,
      GrowthLE (fun τ => faceAmp p x.1 (A τ) x.2 w)
        (P x.1 * C * mono (fun i : {i // ¬ inJ x.1 i} => p i) w) (∑ i, p i) M' :=
    fun w hw => growthLE_faceAmp_fam_of_bound p hA one_pos hC hp0 x.1 x.2
      (Finset.mem_sigma.1 hx).2 hw
  have hflat : ∀ w ∈ box {i // ¬ inJ x.1 i} 1,
      |empFaceCoef k x.1 (fun i => x.2 i + h i) (fun τ => faceAmp p x.1 (A τ) x.2 w)
          μ j| ≤ (C * (P x.1 * Cc x.1 (fun i => x.2 i + h i))) *
            mono (fun i : {i // ¬ inJ x.1 i} => p i) w := by
    intro w hw
    by_cases hμJ : μ ∈ empΛJ k (L : ℝ) x.1 (fun i => x.2 i + h i)
    · calc |empFaceCoef k x.1 (fun i => x.2 i + h i)
            (fun τ => faceAmp p x.1 (A τ) x.2 w) μ j|
          ≤ (P x.1 * C * mono (fun i : {i // ¬ inJ x.1 i} => p i) w) *
              Cc x.1 (fun i => x.2 i + h i) :=
            hCc _ _ _ _ (hgrow w hw) μ hμJ j (Finset.mem_range.2 (Nat.lt_succ_of_le hjD))
        _ = _ := by ring
    · rw [empFaceCoef_eq_zero k (L : ℝ) x.1 hk _ _ hμ hμJ j, abs_zero]
      have := hP0 x.1
      have := hCc0 x.1 (fun i => x.2 i + h i)
      have := (mono_pos (fun i : {i // ¬ inJ x.1 i} => p i) (pos_of_mem_box hw)).le
      positivity
  have hconv : ∀ i : {i // ¬ inJ x.1 i}, ((2 * k i : ℕ) : ℝ) * μ < (p i : ℝ) + h i + 1 := by
    intro i
    have h1 : ((2 * k i : ℕ) : ℝ) * L = (p i : ℝ) + h i := by exact_mod_cast (hp i).symm
    have h2 : (0 : ℝ) < (2 * k i : ℕ) := by exact_mod_cast Nat.mul_pos two_pos (hk i)
    nlinarith
  have hface : |faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
          (fun τ => faceAmp p x.1 (A τ) x.2 w) μ j)
        (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)|
      ≤ (C * (P x.1 * Cc x.1 (fun i => x.2 i + h i))) *
          faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
            (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q) :=
    abs_faceCoeffInt_le one_pos (measurable_empFaceCoef_comp k x.1 _
      (measurable_uncurry_faceAmp_fam p hA x.1 x.2) μ j).aestronglyMeasurable hflat
      hconv (j - q)
  exact le_of_le_of_eq (mul_le_mul_of_nonneg_left hface (Nat.cast_nonneg _)) (by ring)

/-- A single family coefficient is `O(C)`. -/
theorem exists_abs_empCoeffAtDepthFam_single_le (hk : ∀ i, 0 < k i) {L : ℕ}
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (A : ℝ → (Fin d → ℝ) → ℝ),
      ContDiff ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) →
      ∀ C : ℝ, FamJetBound A p 1 C M' → ∀ μ ∈ latticeBelow (Qamb k) L, ∀ j ≤ d - 1,
        |empCoeffAtDepthFam A h k p μ j| ≤ C * K₁ := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_empCoeffAtDepthFam_le h k p hk hp hp0 M'
  refine ⟨K₁, hK₁0, fun A hA C hC μ hμ j hj => ?_⟩
  refine le_trans ?_ (hK₁ A hA C hC)
  have h1 : |empCoeffAtDepthFam A h k p μ j| ≤
      ∑ j' ∈ range (d - 1 + 1), |empCoeffAtDepthFam A h k p μ j'| :=
    Finset.single_le_sum (f := fun j' => |empCoeffAtDepthFam A h k p μ j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  exact h1.trans (Finset.single_le_sum
    (f := fun μ' => ∑ j' ∈ range (d - 1 + 1), |empCoeffAtDepthFam A h k p μ' j'|)
    (fun μ' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) hμ)

/-! ### Linearity by uniqueness -/

theorem absSpectralSum_fam_add {Q D : ℕ} (c₁ c₂ : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ q => c₁ μ q + c₂ μ q) L N =
      absSpectralSum Q D c₁ L N + absSpectralSum Q D c₂ L N := by
  unfold absSpectralSum
  simp only [add_mul, mul_add, Finset.sum_add_distrib]

theorem absSpectralSum_fam_const_mul {Q D : ℕ} (a : ℝ) (c : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ q => a * c μ q) L N = a * absSpectralSum Q D c L N := by
  unfold absSpectralSum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun q _ => ?_
  ring

theorem integrableOn_famIntegrand {A : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) (N : ℝ) :
    IntegrableOn (fun v => A (coupling k N v) v * mono h v *
      exp (-N * mono (fun i => 2 * k i) v)) (box (Fin d) 1) := by
  refine integrableOn_box_of_continuous ?_ 1
  refine ((hA.continuous.comp ((continuous_coupling k N).prodMk continuous_id)).mul
    (continuous_mono h)).mul (continuous_exp.comp (continuous_const.mul (continuous_mono _)))

/-- ★ **Additivity of the family coefficients**, by uniqueness of cutoff expansions. -/
theorem empCoeffAtDepthFam_add {A B : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (hB : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => B z.1 z.2) {CA CB M' : ℝ}
    (hCA : FamJetBound A p 1 CA M') (hCB : FamJetBound B p 1 CB M') (hk : ∀ i, 0 < k i)
    {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeffAtDepthFam (fun τ v => A τ v + B τ v) h k p μ q =
      empCoeffAtDepthFam A h k p μ q + empCoeffAtDepthFam B h k p μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨KS, hKS⟩ := empirical_expansion_at_depth_fam h k p (contDiff_joint_add hA hB)
    (hCA.add hA hB hCB) hk hL hp hp0
  obtain ⟨KA, hKA⟩ := empirical_expansion_at_depth_fam h k p hA hCA hk hL hp hp0
  obtain ⟨KB, hKB⟩ := empirical_expansion_at_depth_fam h k p hB hCB hk hL hp hp0
  set Z : ℝ → ℝ := fun N => ∫ v in box (Fin d) 1, (A (coupling k N v) v + B (coupling k N v) v) *
    mono h v * exp (-N * mono (fun i => 2 * k i) v) with hZ
  have h₁ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (empCoeffAtDepthFam (fun τ v => A τ v + B τ v) h k p) L N| ≤
      KS * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact hKS N hN
  have h₂ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (fun μ q => empCoeffAtDepthFam A h k p μ q + empCoeffAtDepthFam B h k p μ q) L N| ≤
      (KA + KB) * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hsplit : Z N = (∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v)) + ∫ v in box (Fin d) 1, B (coupling k N v) v *
        mono h v * exp (-N * mono (fun i => 2 * k i) v) := by
      rw [hZ]
      simp only
      rw [← integral_add (integrableOn_famIntegrand h k hA N) (integrableOn_famIntegrand h k hB N)]
      refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
      ring
    rw [hsplit, absSpectralSum_fam_add, add_mul]
    calc |(∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
          exp (-N * mono (fun i => 2 * k i) v)) + (∫ v in box (Fin d) 1, B (coupling k N v) v *
          mono h v * exp (-N * mono (fun i => 2 * k i) v)) -
          (absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam A h k p) L N +
            absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam B h k p) L N)|
        ≤ |(∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
            exp (-N * mono (fun i => 2 * k i) v)) -
            absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam A h k p) L N| +
          |(∫ v in box (Fin d) 1, B (coupling k N v) v * mono h v *
            exp (-N * mono (fun i => 2 * k i) v)) -
            absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam B h k p) L N| := by
          rw [show ∀ a b c e : ℝ, a + b - (c + e) = (a - c) + (b - e) from fun _ _ _ _ => by ring]
          exact abs_add_le _ _
      _ ≤ _ := add_le_add (hKA N hN) (hKB N hN)
  exact finite_coeff_unique hQ h₁ h₂ μ hμ q hq

/-- ★ **Homogeneity of the family coefficients**, by uniqueness of cutoff expansions. -/
theorem empCoeffAtDepthFam_const_mul {A : ℝ → (Fin d → ℝ) → ℝ}
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) (c : ℝ) {C M' : ℝ}
    (hC : FamJetBound A p 1 C M') (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    empCoeffAtDepthFam (fun τ v => c * A τ v) h k p μ q = c * empCoeffAtDepthFam A h k p μ q := by
  have hQ := Qamb_pos k hk
  obtain ⟨KS, hKS⟩ := empirical_expansion_at_depth_fam h k p (contDiff_joint_const_mul hA c)
    (hC.const_mul hA c) hk hL hp hp0
  obtain ⟨KA, hKA⟩ := empirical_expansion_at_depth_fam h k p hA hC hk hL hp hp0
  set Z : ℝ → ℝ := fun N => ∫ v in box (Fin d) 1, (c * A (coupling k N v) v) *
    mono h v * exp (-N * mono (fun i => 2 * k i) v) with hZ
  have h₁ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (empCoeffAtDepthFam (fun τ v => c * A τ v) h k p) L N| ≤
      KS * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    exact hKS N hN
  have h₂ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (fun μ q => c * empCoeffAtDepthFam A h k p μ q) L N| ≤
      (|c| * KA) * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hsplit : Z N = c * ∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) := by
      rw [hZ]
      simp only
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
      ring
    rw [hsplit, absSpectralSum_fam_const_mul, ← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hKA N hN) (abs_nonneg _)
  exact finite_coeff_unique hQ h₁ h₂ μ hμ q hq

end SmoothEngine

end Grammar
