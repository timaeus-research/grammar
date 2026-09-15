/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalInnerTwoRegime
import Grammar.SmoothFaceParam

/-!
# The empirical face theorem: outer integration of the parametrised inner kernel

The empirical inner kernel `empUnitInner k e (G w) t` with a `w`-parametrised field factor
`G(w;τ)` of flat growth `|G(w;τ)| ≤ M ∏ wᵢ^{pᵢ} (1+τ)^m e^{M'τ}` is integrated on the outer box
`(0,b]^ι` against `w^h` at the effective parameter `t = N w^a`. ★★ `empirical_face_expansion`:
there is `C = C(k,e,m,M',L)` such that for EVERY such family, every flatness constant `M`, every
box and every `N ≥ 1`,
`∫ w^h I_{G(w;·)}(N w^a) dw = ∑_{μ<L} N^{−μ} ∑_j ∑_q C(j,q)(log N)^q`
`  · ∫ empInnerCoeff k e G(w;·) μ j · w^h (w^a)^{−μ} S(w)^{j−q} dw + O(C M (1+log N)^n N^{−L})`
under `aᵢ L < pᵢ + hᵢ + 1`. The coefficient functions `w ↦ empInnerCoeff k e G(w;·) μ j` are
measurable and flat (`abs_empInnerCoeff_le`), so the parametrised face theorem applies with the
two-regime estimate of `EmpiricalInnerTwoRegime`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset

namespace Grammar

namespace SmoothEngine

variable {ι : Type*} {n : ℕ}

/-! ### Measurability in the outer point -/

/-- The inner kernel of a jointly measurable family, at a measurable parameter, is measurable in
the outer point. -/
theorem measurable_empUnitInner_comp {α : Type*} [MeasurableSpace α] (k e : Fin (n + 1) → ℕ)
    {G : α → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) {T : α → ℝ} (hT : Measurable T) :
    Measurable fun w => empUnitInner k e (G w) (T w) := by
  have h1 : Measurable fun p : α × (Fin (n + 1) → ℝ) =>
      G p.1 (Real.sqrt (T p.1) * ∏ i, p.2 i ^ k i) := by
    have : (fun p : α × (Fin (n + 1) → ℝ) =>
        G p.1 (Real.sqrt (T p.1) * ∏ i, p.2 i ^ k i)) =
        Function.uncurry G ∘ fun p => (p.1, Real.sqrt (T p.1) * ∏ i, p.2 i ^ k i) := rfl
    rw [this]
    exact hG.comp (measurable_fst.prodMk ((hT.comp measurable_fst).sqrt.mul (by fun_prop)))
  have hm : Measurable (Function.uncurry fun (w : α) (u : Fin (n + 1) → ℝ) =>
      (∏ i, u i ^ e i) *
        (G w (Real.sqrt (T w) * ∏ i, u i ^ k i) * exp (-T w * ∏ i, u i ^ (2 * k i)))) := by
    change Measurable fun p : α × (Fin (n + 1) → ℝ) =>
      (∏ i, p.2 i ^ e i) *
        (G p.1 (Real.sqrt (T p.1) * ∏ i, p.2 i ^ k i) * exp (-T p.1 * ∏ i, p.2 i ^ (2 * k i)))
    refine (by fun_prop : Measurable fun p : α × (Fin (n + 1) → ℝ) =>
      ∏ i, p.2 i ^ e i).mul (h1.mul ?_)
    exact ((hT.comp measurable_fst).neg.mul (by fun_prop)).exp
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (unitBox (n + 1)))).measurable

/-- The Mellin moments of a jointly measurable family are measurable in the outer point. -/
theorem measurable_mellinMom_comp {α : Type*} [MeasurableSpace α] {G : α → ℝ → ℝ}
    (hG : Measurable (Function.uncurry G)) (μ : ℝ) (ℓ : ℕ) :
    Measurable fun w => mellinMom (G w) μ ℓ := by
  have h1 : Measurable fun p : α × ℝ => G p.1 (Real.sqrt p.2) := by
    have : (fun p : α × ℝ => G p.1 (Real.sqrt p.2)) =
        Function.uncurry G ∘ fun p => (p.1, Real.sqrt p.2) := rfl
    rw [this]
    exact hG.comp (measurable_fst.prodMk measurable_snd.sqrt)
  have hm : Measurable (Function.uncurry fun (w : α) (s : ℝ) => momKernel (G w) μ ℓ s) := by
    change Measurable fun p : α × ℝ =>
      p.2 ^ (μ - 1) * (-log p.2) ^ ℓ * (G p.1 (Real.sqrt p.2) * exp (-p.2))
    exact ((measurable_snd.pow_const _).mul (measurable_snd.log.neg.pow_const _)).mul
      (h1.mul measurable_snd.neg.exp)
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

/-- The coefficient functions of a jointly measurable family are measurable. -/
theorem measurable_empInnerCoeff_comp {α : Type*} [MeasurableSpace α] (k e : Fin (n + 1) → ℕ)
    {G : α → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) (μ : ℝ) (q : ℕ) :
    Measurable fun w => empInnerCoeff k e (G w) μ q := by
  unfold empInnerCoeff
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact measurable_const.mul (measurable_mellinMom_comp hG μ (j - q))

/-! ### Flatness of the coefficient functions -/

theorem innerCoeffBound_le_total (k e : Fin (n + 1) → ℕ) (m : ℕ) (M : ℝ) {μ : ℝ}
    (hμ : μ ∈ innerSpectrum k e) {q : ℕ} (hq : q ∈ range (n + 1)) :
    innerCoeffBound k e m M μ q ≤ innerCoeffTotal k e m M := by
  unfold innerCoeffTotal
  calc innerCoeffBound k e m M μ q
      ≤ ∑ q' ∈ range (n + 1), innerCoeffBound k e m M μ q' :=
        Finset.single_le_sum (fun q' _ => innerCoeffBound_nonneg k e m M μ q') hq
    _ ≤ _ := Finset.single_le_sum
        (fun μ' _ => Finset.sum_nonneg fun q' _ => innerCoeffBound_nonneg k e m M μ' q') hμ

/-- For a flat family the coefficient functions are flat, with the constant
`M · innerCoeffTotal`. -/
theorem abs_empInnerCoeff_comp_le [Fintype ι] (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {G : (ι → ℝ) → ℝ → ℝ} {p : ι → ℕ} {b M : ℝ} {m : ℕ} {M' : ℝ}
    (hG : ∀ w ∈ box ι b, GrowthLE (G w) (M * mono p w) m M') {μ : ℝ}
    (hμ : μ ∈ innerSpectrumBelow k e L) {q : ℕ} (hq : q ∈ range (n + 1)) {w : ι → ℝ}
    (hw : w ∈ box ι b) :
    |empInnerCoeff k e (G w) μ q| ≤ M * innerCoeffTotal k e m M' * mono p w := by
  have hμ' := Finset.mem_filter.1 hμ
  have hμ0 : 0 < μ := mem_innerSpectrum_pos k e hk hμ'.1
  have hA : 0 ≤ M * mono p w := (hG w hw).nonneg
  calc |empInnerCoeff k e (G w) μ q|
      ≤ M * mono p w * innerCoeffBound k e m M' μ q := abs_empInnerCoeff_le k e (hG w hw) hμ0 q
    _ ≤ M * mono p w * innerCoeffTotal k e m M' :=
        mul_le_mul_of_nonneg_left (innerCoeffBound_le_total k e m M' hμ'.1 hq) hA
    _ = _ := by ring

/-! ### The empirical face theorem -/

/-- ★★ **The empirical face theorem**: for `k, e, m, M', L` there is `C ≥ 0` such that for every
jointly measurable family `G(w;·)` with flat growth `|G(w;τ)| ≤ M ∏ wᵢ^{pᵢ} (1+τ)^m e^{M'τ}` on
the box `(0,b]^ι`, every `N ≥ 1` and under `aᵢ L < pᵢ + hᵢ + 1`,
`|∫ w^h · empUnitInner k e G(w;·) (N w^a) dw − ∑_{μ ∈ spectrum, μ<L} N^{−μ} ∑_{j≤n} ∑_{q≤j}`
`  C(j,q)(log N)^q · faceCoeffInt (w ↦ empInnerCoeff k e G(w;·) μ j) h a b μ (j−q)|`
`  ≤ C M (1 + log N)^n N^{−L} faceRemWeight p h a b L n`. -/
theorem empirical_face_expansion [Fintype ι] (k e : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (m : ℕ)
    (M' : ℝ) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p h a : ι → ℕ} {b M : ℝ}, 0 < b → ∀ (G : (ι → ℝ) → ℝ → ℝ),
      Measurable (Function.uncurry G) → (∀ w ∈ box ι b, GrowthLE (G w) (M * mono p w) m M') →
      (∀ i, (a i : ℝ) * L < p i + h i + 1) → ∀ N : ℝ, 1 ≤ N →
      |(∫ w in box ι b, mono h w * empUnitInner k e (G w) (N * mono a w)) -
        ∑ μ ∈ innerSpectrumBelow k e L, N ^ (-μ) * ∑ j ∈ range (n + 1), ∑ q ∈ range (j + 1),
          (j.choose q) * log N ^ q *
            faceCoeffInt (fun w => empInnerCoeff k e (G w) μ j) h a b μ (j - q)| ≤
        C * M * (1 + log N) ^ n * N ^ (-L) * faceRemWeight p h a b L n := by
  obtain ⟨C, hC0, hC⟩ := empUnitInner_two_regime k e hk m M' hL
  refine ⟨C, hC0, fun {p h a b M} hb G hGm hG hA N hN => ?_⟩
  have hM : 0 ≤ M := by
    have h0 := (hG _ (const_mem_box hb)).nonneg
    exact (mul_nonneg_iff_of_pos_right (mono_pos p fun _ => hb)).1 h0
  have hT : Measurable fun w : ι → ℝ => N * mono a w := measurable_const.mul (measurable_mono a)
  have hZm : AEStronglyMeasurable (fun w => empUnitInner k e (G w) (N * mono a w))
      (volume.restrict (box ι b)) :=
    (measurable_empUnitInner_comp k e hGm hT).aestronglyMeasurable
  have hcm : ∀ μ ∈ innerSpectrumBelow k e L, ∀ j ∈ range (n + 1),
      AEStronglyMeasurable (fun w => empInnerCoeff k e (G w) μ j) (volume.restrict (box ι b)) :=
    fun μ _ j _ => (measurable_empInnerCoeff_comp k e hGm μ j).aestronglyMeasurable
  have hcM : ∀ μ ∈ innerSpectrumBelow k e L, ∀ j ∈ range (n + 1), ∀ w ∈ box ι b,
      |empInnerCoeff k e (G w) μ j| ≤ M * innerCoeffTotal k e m M' * mono p w :=
    fun μ hμ j hj w hw => abs_empInnerCoeff_comp_le k e hk hG hμ hj hw
  have hZ2 : ∀ w ∈ box ι b, ∀ t : ℝ, 0 < t →
      |empUnitInner k e (G w) t -
          powLog (innerSpectrumBelow k e L) n (empInnerCoeff k e (G w)) t| ≤
        C * M * mono p w * t ^ (-L) * (1 + |log t|) ^ n := by
    intro w hw t ht
    refine (hC (G w) (hGm.comp (measurable_prodMk_left)) (M * mono p w) (hG w hw) t ht).trans
      (le_of_eq ?_)
    ring
  have hΛ : ∀ μ ∈ innerSpectrumBelow k e L, μ ≤ L := fun μ hμ => (Finset.mem_filter.1 hμ).2.le
  exact face_expansion_param (Z := fun w t => empUnitInner k e (G w) t)
    (c := fun w => empInnerCoeff k e (G w)) hb (mul_nonneg hC0 hM) hZm hcm hcM hZ2 hΛ hA hN

end SmoothEngine

end Grammar
