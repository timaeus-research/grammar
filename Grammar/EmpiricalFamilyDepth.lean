/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneralDepth

/-!
# The empirical expansion at depth for a general amplitude family (§20, generating identity)

The depth engine of `EmpiricalGeneralDepth` is stated for the exponential field family
`B_τ = η e^{τζ}`; its proof uses the family only through joint smoothness in `(τ, v)`, the jet
bound `|∂^m B_τ| ≤ C (1+τ)^{|p|} e^{M'τ}` and the resulting flat growth of the face amplitudes.
This file restates the engine for an ARBITRARY jointly smooth amplitude family
`A : ℝ → (Fin d → ℝ) → ℝ` with the same jet bound (`FamJetBound`):

* `empCoeffAtDepthFam A h k p μ q` — the coefficient system at depth `p` (face coefficient
  integrals of the Mellin moments of the face amplitudes of `A`); for `A = fieldFam η ζ` it is
  `empCoeffAtDepth η ζ h k p` definitionally (`empCoeffAtDepthFam_fieldFam`);
* ★★★ `empirical_expansion_at_depth_fam`: for `pᵢ + hᵢ = 2kᵢL`,
  `|∫_{(0,1]^d} A(√N v^k, v) v^h e^{−N v^{2k}} dv`
  `  − absSpectralSum Q (d−1) (empCoeffAtDepthFam A) L N| ≤ K N^{−L} (1 + log N)^{d−1}`
  for all `N ≥ 1`.

The point: the monomial families `A_r(τ, v) = τ^r η(v) ζ(v)^r` of the exponential series
`e^{τζ} = Σ_r τ^r ζ^r / r!` are amplitude families at the SAME depth `p`, so the half-integer
Mellin shift `μ ↦ μ + r/2` of the `r`-th term lives inside the Mellin moment and never changes the
integer cutoff — the mechanism behind the generating-series identity
`C_{μ,q}[η, ζ] = Σ_r C^{pop}_{μ+r/2,q}[η (u^k ζ)^r] / r!`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The jet bound of an amplitude family: `|∂^m A_τ| ≤ C (1+τ)^{|p|} e^{M'τ}` on the closed box for
`m ≤ p`, `τ ≥ 0`. -/
def FamJetBound (A : ℝ → (Fin d → ℝ) → ℝ) (p : Fin d → ℕ) (b C M' : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
    |pdMulti m (List.finRange d) (A τ) v| ≤ C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ)

theorem fieldJetBound_iff_famJetBound {η ζ : (Fin d → ℝ) → ℝ} {p : Fin d → ℕ} {b C M' : ℝ} :
    FieldJetBound η ζ p b C M' ↔ FamJetBound (fieldFam η ζ) p b C M' := Iff.rfl

theorem FamJetBound.nonneg {A : ℝ → (Fin d → ℝ) → ℝ} {p : Fin d → ℕ} {b C M' : ℝ} (hb : 0 ≤ b)
    (h : FamJetBound A p b C M') : 0 ≤ C := by
  have h0 := h 0 (fun i => Nat.zero_le _) 0 le_rfl 0 (mem_closedBox.2 fun i => by simp [hb])
  simp only [add_zero, one_pow, mul_one, mul_zero, exp_zero] at h0
  exact (abs_nonneg _).trans h0

variable {A : ℝ → (Fin d → ℝ) → ℝ}

/-- Slices of a jointly smooth family are smooth. -/
theorem contDiff_famSlice (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) (τ : ℝ) :
    ContDiff ℝ ∞ (A τ) :=
  hA.comp (contDiff_const.prodMk contDiff_id)

section Fam

variable (A) (h k p : Fin d → ℕ)

/-- The `(J, m)` empirical face integral of the family. -/
noncomputable def empFaceIntegralFam (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ w in box {i // ¬ inJ J i} 1, mono (fun i : {i // ¬ inJ J i} => h i) w *
    empFaceInner (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => m i + h i)
      (fun τ => faceAmp p J (A τ) m w)
      (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)

/-- The `(J, m)` summand of the face split at the pointwise coupling. -/
noncomputable def empSFam (J : Finset (Fin d)) (N : ℝ) (m : Fin d → ℕ) (v : Fin d → ℝ) : ℝ :=
  tayMono m v *
    remList p (lK J) (pdMulti m (lJ J) (A (coupling k N v))) (zeroL (lJ J) v) *
    mono h v * exp (-N * mono (fun i => 2 * k i) v)

variable {A}

theorem continuous_remList_pdMulti_fam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Continuous fun z : ℝ × (Fin d → ℝ) => remList p (lK J) (pdMulti m (lJ J) (A z.1)) z.2 := by
  have h1 : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      pdMulti m (lJ J) (fun v => A z.1 v) z.2 :=
    contDiff_pdMulti_slice hA m (lJ J)
  have h2 : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      remList p (lK J) (fun v => pdMulti m (lJ J) (fun v => A z.1 v) v) z.2 :=
    contDiff_remList_slice p h1 (lK J)
  exact h2.continuous

theorem continuous_empSFam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) (N : ℝ) (m : Fin d → ℕ) : Continuous (empSFam A h k p J N m) := by
  unfold empSFam
  refine (((continuous_tayMono m).mul ?_).mul (continuous_mono h)).mul
    (continuous_exp.comp (continuous_const.mul (continuous_mono _)))
  exact (continuous_remList_pdMulti_fam p hA J m).comp
    ((continuous_coupling k N).prodMk (continuous_zeroL _))

/-- The `J`-face term at the pointwise coupling is the sum of the `(J, m)` summands. -/
theorem empFaceTerm_pointwise_fam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) (N : ℝ) (v : Fin d → ℝ) :
    faceOp p J (List.finRange d) (A (coupling k N v)) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) =
      ∑ m ∈ idxL p (lJ J), empSFam A h k p J N m v := by
  have hdisj : ∀ i ∈ lJ J, i ∉ lK J := fun i hi h' => (mem_lK J).1 h' ((mem_lJ J).1 hi)
  have hF := contDiff_famSlice hA (coupling k N v)
  rw [faceOp_finRange_eq p J hF, tayList_eq_sum p (contDiff_remList p hF _) (nodup_lJ J),
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold empSFam
  rw [pdMulti_remList p hF m hdisj]

/-- ★ **The empirical face-term integral of the family.** -/
theorem empFaceTerm_integral_fam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) {N : ℝ} (hN : 0 ≤ N) :
    ∫ v in box (Fin d) 1, faceOp p J (List.finRange d) (A (coupling k N v)) v *
        mono h v * exp (-N * mono (fun i => 2 * k i) v) =
      ∑ m ∈ idxL p (lJ J), faceW J m * empFaceIntegralFam A h k p J m N := by
  have hSint : ∀ m, IntegrableOn (empSFam A h k p J N m) (box (Fin d) 1) := fun m =>
    integrableOn_box_of_continuous (continuous_empSFam h k p hA J N m) 1
  rw [setIntegral_congr_fun (measurableSet_box 1) fun v _ =>
    empFaceTerm_pointwise_fam h k p hA J N v, integral_finsetSum _ fun m _ => hSint m]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_box_split J 1 _ (hSint m)]
  unfold empFaceIntegralFam
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := {i // ¬ inJ J i}) 1) fun w hw => ?_
  have hwpos : ∀ i, 0 < w i := pos_of_mem_box hw
  have hmk : 0 ≤ mono (fun i : {i // ¬ inJ J i} => k i) w := (mono_pos _ hwpos).le
  have hsq : Real.sqrt (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) =
      Real.sqrt N * mono (fun i : {i // ¬ inJ J i} => k i) w := by
    have h2 : mono (fun i : {i // ¬ inJ J i} => 2 * k i) w =
        mono (fun i : {i // ¬ inJ J i} => k i) w * mono (fun i : {i // ¬ inJ J i} => k i) w := by
      rw [mono_mul_mono]
      congr 1
      funext i
      ring
    rw [h2, Real.sqrt_mul hN, Real.sqrt_mul_self hmk]
  unfold empFaceInner
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := {i // inJ J i}) 1) fun u _ => ?_
  unfold empSFam coupling faceAmp faceW
  rw [tayMono_glue p J hm, zeroL_lJ_glue, hsq]
  simp only [mono_glue]
  rw [← mono_mul_mono (fun i : {i // inJ J i} => m i) (fun i => h i) u]
  have harg1 : Real.sqrt N * (mono (fun i : {i // inJ J i} => k i) u *
      mono (fun i : {i // ¬ inJ J i} => k i) w) =
      Real.sqrt N * mono (fun i : {i // ¬ inJ J i} => k i) w *
        mono (fun i : {i // inJ J i} => k i) u := by
    ring
  have harg2 : -N * (mono (fun i : {i // inJ J i} => 2 * k i) u *
      mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) =
      -(N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) *
        mono (fun i : {i // inJ J i} => 2 * k i) u := by
    ring
  rw [harg1, harg2]
  ring

/-- The full integral at the pointwise coupling as a sum of face integrals over `faceIndex`. -/
theorem integral_eq_sum_empFaceIntegral_fam
    (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) {N : ℝ} (hN : 0 ≤ N) :
    ∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) =
      ∑ x ∈ faceIndex p, faceW x.1 x.2 * empFaceIntegralFam A h k p x.1 x.2 N := by
  have hpt : ∀ v : Fin d → ℝ, A (coupling k N v) v * mono h v *
      exp (-N * mono (fun i => 2 * k i) v) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))),
        faceOp p J (List.finRange d) (A (coupling k N v)) v * mono h v *
          exp (-N * mono (fun i => 2 * k i) v) := by
    intro v
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.powerset_univ, ← List.toFinset_finRange,
      ← sum_faceOp p (List.nodup_finRange d) _ v]
  have hint : ∀ J ∈ (univ : Finset (Finset (Fin d))), IntegrableOn
      (fun v => faceOp p J (List.finRange d) (A (coupling k N v)) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v)) (box (Fin d) 1) := fun J _ => by
    have hsum : IntegrableOn (fun v => ∑ m ∈ idxL p (lJ J), empSFam A h k p J N m v)
        (box (Fin d) 1) :=
      integrable_finsetSum _ fun m _ =>
        integrableOn_box_of_continuous (continuous_empSFam h k p hA J N m) 1
    exact hsum.congr
      (Eventually.of_forall fun v => (empFaceTerm_pointwise_fam h k p hA J N v).symm)
  rw [setIntegral_congr_fun (measurableSet_box 1) fun v _ => hpt v, integral_finsetSum _ hint,
    faceIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [empFaceTerm_integral_fam h k p hA J hN]

/-! ### The per-face bound -/

variable (A) in
/-- The face expansion of the `(J, m)` term of the family. -/
noncomputable def empFaceExpansionFam (L : ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) :
    ℝ :=
  ∑ μ ∈ empΛJ k L J (fun i => m i + h i), N ^ (-μ) * ∑ j ∈ range (DJ J + 1),
    ∑ q ∈ range (j + 1), (j.choose q) * log N ^ q *
      faceCoeffInt (fun w => empFaceCoef k J (fun i => m i + h i)
          (fun τ => faceAmp p J (A τ) m w) μ j)
        (fun i : {i // ¬ inJ J i} => h i) (fun i : {i // ¬ inJ J i} => 2 * k i) 1 μ (j - q)

omit h k in
/-- ★ Flat growth of the face amplitudes of the family under the jet bound. -/
theorem growthLE_faceAmp_fam_of_bound (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    {b C M' : ℝ} (hb : 0 < b) (hC : FamJetBound A p b C M') (hp0 : ∀ i, 0 < p i)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (hm : m ∈ idxL p (lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) :
    GrowthLE (fun τ => faceAmp p J (A τ) m w)
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
        mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M' := by
  intro τ hτ
  have h := faceAmp_bound p J (contDiff_famSlice hA τ) hb hp0
    (M := C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ))
    (fun m' hm' v hv => hC m' hm' τ hτ v (mem_closedBox.2 hv)) hm hw
  refine h.trans (le_of_eq ?_)
  ring

omit h k in
/-- The face amplitudes of the family are jointly continuous in `(τ, w)`. -/
theorem continuous_faceAmp_fam_joint (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Continuous fun z : ℝ × ({i // ¬ inJ J i} → ℝ) => faceAmp p J (A z.1) m z.2 :=
  (contDiff_faceAmp_slice (G := fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) hA p J m).continuous

omit h k in
theorem measurable_uncurry_faceAmp_fam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Measurable (Function.uncurry fun (w : {i // ¬ inJ J i} → ℝ) (τ : ℝ) =>
      faceAmp p J (A τ) m w) :=
  ((continuous_faceAmp_fam_joint p hA J m).comp continuous_swap).measurable

/-- ★ **The per-face bound, UNIFORM in the family**: the constant depends only on
`(h, k, p, L, M', J, m)`. -/
theorem empFace_bound_uniform_fam (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) (J : Finset (Fin d))
    (m : Fin d → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ → (Fin d → ℝ) → ℝ),
      ContDiff ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) →
      ∀ C : ℝ, FamJetBound A p 1 C M' → m ∈ idxL p (lJ J) → ∀ N : ℝ, 1 ≤ N →
        |empFaceIntegralFam A h k p J m N - empFaceExpansionFam A h k p L J m N| ≤
          C * K * (1 + log N) ^ DJ J * N ^ (-(L : ℝ)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨C₂, hC₂0, hC₂⟩ := empFace_two_regime k (L : ℝ) J hk (∑ i, p i) M' hL' (fun i => m i + h i)
  obtain ⟨Cc, hCc0, hCc⟩ :=
    exists_abs_empFaceCoef_le k (L : ℝ) J hk (∑ i, p i) M' (fun i => m i + h i)
  set P : ℝ := ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => by positivity
  set R : ℝ := faceRemWeight (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
    (fun i : {i // ¬ inJ J i} => 2 * k i) 1 L (DJ J) with hR
  have hR0 : 0 ≤ R := faceRemWeight_nonneg _ _ _ _ _ _
  refine ⟨C₂ * P * R, by positivity, fun A hA C hC hm N hN => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  have hCg : ∀ w ∈ box {i // ¬ inJ J i} 1, GrowthLE (fun τ => faceAmp p J (A τ) m w)
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
        mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M' :=
    fun w hw => growthLE_faceAmp_fam_of_bound p hA one_pos hC hp0 J m hm hw
  have hGm := measurable_uncurry_faceAmp_fam p hA J m
  have hT : Measurable fun w : {i // ¬ inJ J i} → ℝ =>
      N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w :=
    measurable_const.mul (measurable_mono _)
  have key := face_expansion_param (ι := {i // ¬ inJ J i})
    (Z := fun w t => empFaceInner (fun i : {i // inJ J i} => k i)
      (fun i : {i // inJ J i} => m i + h i) (fun τ => faceAmp p J (A τ) m w) t)
    (c := fun w => empFaceCoef k J (fun i => m i + h i) (fun τ => faceAmp p J (A τ) m w))
    (p := fun i => p i) (h := fun i => h i) (a := fun i => 2 * k i) (b := 1)
    (M := P * C * Cc) (C := C₂ * (P * C)) (L := (L : ℝ))
    (Λ := empΛJ k (L : ℝ) J (fun i => m i + h i)) (D := DJ J) one_pos (by positivity)
    (measurable_empFaceInner_comp _ _ hGm hT).aestronglyMeasurable
    (fun μ _ j _ => (measurable_empFaceCoef_comp k J _ hGm μ j).aestronglyMeasurable)
    (fun μ hμ j hj w hw => ?_) (fun w hw t ht => ?_)
    (fun μ hμ => le_of_mem_empΛJ k (L : ℝ) J _ hμ) (fun i => convergence_of_eq (hp i)) hN
  · unfold empFaceIntegralFam empFaceExpansionFam
    refine key.trans (le_of_eq ?_)
    rw [hR]
    ring
  · have hgrow := hCg w hw
    calc |empFaceCoef k J (fun i => m i + h i) (fun τ => faceAmp p J (A τ) m w) μ j|
        ≤ (P * C * mono (fun i : {i // ¬ inJ J i} => p i) w) * Cc :=
          hCc _ _ hgrow μ hμ j hj
      _ = _ := by ring
  · have hgrow := hCg w hw
    have h2 := hC₂ _ (hGm.comp measurable_prodMk_left) _ hgrow t ht
    refine h2.trans (le_of_eq ?_)
    ring

/-! ### The assembly -/

variable (A) in
/-- ★ **The coefficient system of the family at depth `p`** on the ambient lattice. -/
noncomputable def empCoeffAtDepthFam (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q) *
    faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (A τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)

/-- For the exponential field family the family coefficients are the engine's. -/
theorem empCoeffAtDepthFam_fieldFam (η ζ : (Fin d → ℝ) → ℝ) :
    empCoeffAtDepthFam (fieldFam η ζ) h k p = empCoeffAtDepth η ζ h k p := rfl

/-- The face expansions sum to the ambient `absSpectralSum` of `empCoeffAtDepthFam`. -/
theorem sum_empFaceExpansion_eq_fam (hk : ∀ i, 0 < k i) (L : ℕ) (N : ℝ) :
    ∑ x ∈ faceIndex p, faceW x.1 x.2 * empFaceExpansionFam A h k p L x.1 x.2 N =
      absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam A h k p) L N := by
  unfold empFaceExpansionFam empCoeffAtDepthFam
  exact reorganise' (faceIndex p) (fun x => faceW x.1 x.2)
    (fun x => empΛJ k (L : ℝ) x.1 (fun i => x.2 i + h i)) (fun x => DJ x.1)
    (fun x μ j q => faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (A τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q))
    (fun x _ => empΛJ_subset k (L : ℝ) x.1 hk _)
    (fun x _ μ hμ hμJ j q => faceCoeffInt_eq_zero_of_zero
      (fun w => empFaceCoef_eq_zero k (L : ℝ) x.1 hk _ _ hμ hμJ j) _ _ _ _ _)
    (fun x _ => DJ_le x.1)

/-- ★★★ **The empirical expansion at depth `p` for a general family, UNIFORMLY**: the constant
depends only on `(h, k, p, L, M')`. -/
theorem empirical_expansion_at_depth_uniform_fam (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (A : ℝ → (Fin d → ℝ) → ℝ),
      ContDiff ℝ ∞ (fun z : ℝ × (Fin d → ℝ) => A z.1 z.2) →
      ∀ C : ℝ, FamJetBound A p 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |(∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
            exp (-N * mono (fun i => 2 * k i) v)) -
          absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam A h k p) L N| ≤
          C * K₀ * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  choose K hK0 hK using fun (J : Finset (Fin d)) (m : Fin d → ℕ) =>
    empFace_bound_uniform_fam h k p hk hL hp hp0 M' J m
  refine ⟨∑ x ∈ faceIndex p, faceW x.1 x.2 * K x.1 x.2,
    Finset.sum_nonneg fun x _ => mul_nonneg (faceW_nonneg _ _) (hK0 _ _),
    fun A hA C hC N hN => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  have hlog : 0 ≤ log N := log_nonneg hN
  rw [integral_eq_sum_empFaceIntegral_fam h k p hA (by linarith),
    ← sum_empFaceExpansion_eq_fam h k p hk L N, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hb' := hK x.1 x.2 A hA C hC hm N hN
  have hpow : (1 + log N) ^ DJ x.1 ≤ (1 + log N) ^ (d - 1) :=
    pow_le_pow_right₀ (by linarith) (DJ_le x.1)
  have hW := faceW_nonneg x.1 x.2
  have hK0' := hK0 x.1 x.2
  rw [← mul_sub, abs_mul, abs_of_nonneg hW]
  calc faceW x.1 x.2 *
        |empFaceIntegralFam A h k p x.1 x.2 N - empFaceExpansionFam A h k p L x.1 x.2 N|
      ≤ faceW x.1 x.2 * (C * K x.1 x.2 * (1 + log N) ^ DJ x.1 * N ^ (-(L : ℝ))) :=
        mul_le_mul_of_nonneg_left hb' hW
    _ ≤ faceW x.1 x.2 * (C * K x.1 x.2 * (1 + log N) ^ (d - 1) * N ^ (-(L : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- ★★★ **The empirical expansion at depth `p` for a general amplitude family.** -/
theorem empirical_expansion_at_depth_fam (hA : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => A z.1 z.2)
    {C M' : ℝ} (hC : FamJetBound A p 1 C M') (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |(∫ v in box (Fin d) 1, A (coupling k N v) v * mono h v *
          exp (-N * mono (fun i => 2 * k i) v)) -
        absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepthFam A h k p) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  obtain ⟨K₀, _, hK₀⟩ := empirical_expansion_at_depth_uniform_fam h k p hk hL hp hp0 M'
  exact ⟨C * K₀, fun N hN => hK₀ A hA C hC N hN⟩

end Fam

end SmoothEngine

end Grammar
