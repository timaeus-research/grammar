/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartOrthantCore

/-!
# The orthant tiling of a centred hironaka chart and the local chart theorem

The `2^{n+1}` orthant charts of a centred hironaka chart (`orthantChart`, CCIII) tile the image of
the strip box `zBox σ A' b'` under the **strip chart** `g = φ(T⁻¹(·) + y₀)` (`stripChart`): their
images are pairwise disjoint (the strip chart is injective off the normal hyperplanes,
`injOn_stripChart`), lie in the **local region** `Ω = g(zBox)` (`localRegion`, compact, containing
`φ y₀`), and cover it up to the null image of the normal hyperplanes (`localRegion_sdiff_subset`,
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). This is a `CoreTiling`, so the
population integral over `Ω` has the full power–log cutoff expansion with **no series hypothesis**:
the joint series of every orthant amplitude exists at the origin (`analyticAt_orthantAmp_joint`)
and a common margin is chosen below the minimum of the `2^{n+1}` radii
(`chart_local_cutoffExpansion`).

Non-claims: local at one divisor point of one hironaka chart; the region `Ω` is the chart's own
strip box, not a neighbourhood of `φ y₀` in the ambient space; no cross-chart statement.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic Monomialize.VolumeScaling
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)} {h : Fin d →₀ ℕ}
  {y₀ : Fin d → ℝ} (C : CentredChartData K φ h y₀) {β : ℝ} {j₀ : Fin (C.n + 1)}
  {A : Set (Fin C.t → ℝ)} {b₁ : ℝ}
  (SD : StripData (nIdx C.σ j₀) C.V₀ (unitRoot β (2 * C.k j₀) C.unit₀) (stripBase C.σ A j₀ b₁))

/-! ### Joint analyticity of the orthant amplitude -/

section Amplitude

variable (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀)) {F : (Fin d → ℝ) → ℝ}
  (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (s : Fin (C.n + 1) → Bool)

include hβ in
theorem analyticAt_orthantJac {y : Fin d → ℝ} (hy : y ∈ orthantDomain C SD s) :
    AnalyticAt ℝ (orthantJac C SD s) y := by
  refine (analyticAt_orthantJacFun C SD hβ s hy).congr ?_
  filter_upwards [(isOpen_orthantDomain C SD s).mem_nhds hy] with z hz
  exact (orthantJac_eq C SD s hz).symm

include hβ hφ hF in
theorem analyticAt_orthantAmp {p : (Fin C.t → ℝ) × (Fin (C.n + 1) → ℝ)}
    (hp : prodToPi C.σ p ∈ orthantDomain C SD s) : AnalyticAt ℝ (orthantAmp C SD s F) p := by
  have h1 := analyticAt_orthantJac C SD hβ s hp
  have h2 : AnalyticAt ℝ (F ∘ orthantChart C SD s) (prodToPi C.σ p) :=
    AnalyticAt.comp (g := F) (f := orthantChart C SD s) (hF _ (inv_reflect_mem_V₀ C SD s hp))
      (analyticAt_orthantChart C SD hφ s hp)
  exact AnalyticAt.comp (g := fun y => orthantJac C SD s y * (F ∘ orthantChart C SD s) y)
    (f := prodToPi C.σ) (h1.mul h2) (analyticAt_prodToPi p)

include hβ hφ hF in
/-- **The joint series of the orthant amplitude** exists at every point over the orthant domain. -/
theorem analyticAt_orthantAmp_joint {w : Fin C.t ⊕ Fin (C.n + 1) → ℝ}
    (hw : prodToPi C.σ (w ∘ Sum.inl, w ∘ Sum.inr) ∈ orthantDomain C SD s) :
    AnalyticAt ℝ (fun w : Fin C.t ⊕ Fin (C.n + 1) → ℝ =>
      orthantAmp C SD s F (w ∘ Sum.inl, w ∘ Sum.inr)) w := by
  have hL : AnalyticAt ℝ (fun w : Fin C.t ⊕ Fin (C.n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr)) w := by
    have : (fun w : Fin C.t ⊕ Fin (C.n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr)) =
        ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)).prod
          (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)) :
            (Fin C.t ⊕ Fin (C.n + 1) → ℝ) →L[ℝ] (Fin C.t → ℝ) × (Fin (C.n + 1) → ℝ)) := by
      funext w
      rfl
    rw [this]
    exact ContinuousLinearMap.analyticAt _ w
  exact AnalyticAt.comp (g := orthantAmp C SD s F)
    (f := fun w : Fin C.t ⊕ Fin (C.n + 1) → ℝ => (w ∘ Sum.inl, w ∘ Sum.inr))
    (analyticAt_orthantAmp C SD hβ hφ hF s hw) hL

end Amplitude

/-! ### The strip chart and the local region -/

/-- The strip chart `g = φ(T⁻¹(·) + y₀)`. -/
noncomputable def stripChart (ζ : Fin d → ℝ) : Fin d → ℝ := translated φ y₀ (SD.inv ζ)

theorem orthantChart_eq (s : Fin (C.n + 1) → Bool) :
    orthantChart C SD s = stripChart C SD ∘ splitReflect C.σ s := rfl

/-- The image of the strip. -/
def stripImage : Set (Fin d → ℝ) := rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀) '' SD.S

theorem mem_orthantDomain_iff' (s : Fin (C.n + 1) → Bool) (y : Fin d → ℝ) :
    y ∈ orthantDomain C SD s ↔ splitReflect C.σ s y ∈ stripImage C SD := Iff.rfl

theorem isOpen_stripImage : IsOpen (stripImage C SD) := SD.image_open

theorem inv_mem_V₀ {ζ : Fin d → ℝ} (hζ : ζ ∈ stripImage C SD) : SD.inv ζ ∈ C.V₀ :=
  SD.S_sub (SD.inv_mem hζ)

theorem analyticAt_stripChart (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀)) {ζ : Fin d → ℝ}
    (hζ : ζ ∈ stripImage C SD) : AnalyticAt ℝ (stripChart C SD) ζ := by
  have h3 : AnalyticAt ℝ (fun w => w + y₀) (SD.inv ζ) := analyticAt_id.add analyticAt_const
  have h5 : AnalyticAt ℝ (φ ∘ fun w => w + y₀) (SD.inv ζ) :=
    AnalyticAt.comp (g := φ) (f := fun w => w + y₀) (hφ _ (inv_mem_V₀ C SD hζ)) h3
  exact AnalyticAt.comp (g := φ ∘ fun w => w + y₀) (f := SD.inv) h5 (SD.inv_analytic _ hζ)

/-- The points of the strip image with nonvanishing normal coordinates. -/
def stripImageOff : Set (Fin d → ℝ) := stripImage C SD ∩ {ζ | ∀ j, ζ (nIdx C.σ j) ≠ 0}

/-- **The strip chart is injective off the normal hyperplanes.** -/
theorem injOn_stripChart
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂) :
    InjOn (stripChart C SD) (stripImageOff C SD) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ heq
  have hm₁ := C.monomialEval_ne_zero _ (inv_mem_V₀ C SD hζ₁.1)
    fun j => SD.inv_apply_ne_zero hζ₁.1 (hζ₁.2 j)
  have hm₂ := C.monomialEval_ne_zero _ (inv_mem_V₀ C SD hζ₂.1)
    fun j => SD.inv_apply_ne_zero hζ₂.1 (hζ₂.2 j)
  exact SD.injOn_inv hζ₁.1 hζ₂.1
    (hinj _ (inv_mem_V₀ C SD hζ₁.1) _ (inv_mem_V₀ C SD hζ₂.1) hm₁ hm₂ heq)

/-- The reflected positive box lies in the strip box. -/
theorem splitReflect_mem_zBox (s : Fin (C.n + 1) → Bool) {A' : Set (Fin C.t → ℝ)} {b : ℝ}
    {y : Fin d → ℝ} (hy : y ∈ splitPosBox C.σ A' b) : splitReflect C.σ s y ∈ zBox C.σ A' b := by
  rw [splitPosBox] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [splitReflect_prodToPi]
  refine ⟨reflectChart s p, ⟨hp.1, fun j _ => ?_⟩, rfl⟩
  rw [reflectChart_apply]
  simp only [reflectEquiv_apply]
  have := hp.2 j (mem_univ j)
  rw [mem_Icc, ← abs_le, abs_mul, abs_boolSgn, one_mul]
  exact abs_le.2 ⟨by linarith [this.1, this.2], this.2⟩

/-- The reflected positive box has nonvanishing normal coordinates. -/
theorem splitReflect_apply_nIdx_ne_zero (s : Fin (C.n + 1) → Bool) {A' : Set (Fin C.t → ℝ)}
    {b : ℝ} {y : Fin d → ℝ} (hy : y ∈ splitPosBox C.σ A' b) (j : Fin (C.n + 1)) :
    splitReflect C.σ s y (nIdx C.σ j) ≠ 0 := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [splitReflect_apply]
  exact mul_ne_zero (splitSgn_ne_zero _ _ _) (prodToPi_apply_nIdx_pos C hp j).ne'

theorem zBox_subset_stripImage {A' : Set (Fin C.t → ℝ)} (hA'A : A' ⊆ A) {b' : ℝ}
    (hb'b₁ : b' ≤ b₁) (hb'SD : b' ≤ SD.b) : zBox C.σ A' b' ⊆ stripImage C SD :=
  (zBox_subset_cylinder hA'A hb'b₁ hb'SD).trans SD.cyl_sub_image

/-- **The local region** `Ω = g(zBox σ A' b')`. -/
def localRegion (A' : Set (Fin C.t → ℝ)) (b' : ℝ) : Set (Fin d → ℝ) :=
  stripChart C SD '' zBox C.σ A' b'

theorem isCompact_localRegion (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    {A' : Set (Fin C.t → ℝ)} (hA' : IsCompact A') (hA'A : A' ⊆ A) {b' : ℝ} (hb'b₁ : b' ≤ b₁)
    (hb'SD : b' ≤ SD.b) : IsCompact (localRegion C SD A' b') := by
  refine ((isCompact_twoSidedBox hA' b').image continuous_prodToPi).image_of_continuousOn ?_
  intro ζ hζ
  exact (analyticAt_stripChart C SD hφ
    (zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD hζ)).continuousAt.continuousWithinAt

/-- The local region lies in the translated chart of the centred neighbourhood. -/
theorem localRegion_subset {A' : Set (Fin C.t → ℝ)} (hA'A : A' ⊆ A) {b' : ℝ} (hb'b₁ : b' ≤ b₁)
    (hb'SD : b' ≤ SD.b) : localRegion C SD A' b' ⊆ translated φ y₀ '' C.V₀ := by
  rintro x ⟨ζ, hζ, rfl⟩
  exact ⟨SD.inv ζ, inv_mem_V₀ C SD (zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD hζ), rfl⟩

/-- The origin of the translated coordinates is a fixed point of the strip normalisation. -/
theorem inv_zero (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 ≤ b₁) : SD.inv 0 = 0 := by
  have hT : rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀) 0 = 0 := by
    funext x
    by_cases hx : x = nIdx C.σ j₀
    · subst hx
      rw [rescale_apply_self]
      simp
    · rw [rescale_apply_of_ne hx]
  have h0S : (0 : Fin d → ℝ) ∈ SD.S := by
    refine SD.cyl_sub ⟨?_, ?_⟩
    · refine ⟨((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)), ⟨h0, rfl, fun j => by simp [hb₁]⟩, ?_⟩
      funext x
      obtain ⟨z, rfl⟩ := C.σ.surjective x
      rcases z with i | j
      · rw [show C.σ (Sum.inl i) = tIdx C.σ i from rfl, prodToPi_apply_tIdx]
        by_cases hi : tIdx C.σ i = nIdx C.σ j₀
        · exact absurd hi (tIdx_ne_nIdx i j₀)
        · simp [baseProj, Function.update_of_ne hi]
      · rw [show C.σ (Sum.inr j) = nIdx C.σ j from rfl, prodToPi_apply_nIdx]
        by_cases hj : nIdx C.σ j = nIdx C.σ j₀
        · simp [baseProj, hj]
        · simp [baseProj, Function.update_of_ne hj]
    · show |(0 : Fin d → ℝ) (nIdx C.σ j₀)| ≤ SD.b₀ / 2
      simp only [Pi.zero_apply, abs_zero]
      exact (half_pos SD.b₀_pos).le
  have := SD.inv_apply h0S
  rwa [hT] at this

theorem mem_localRegion_zero {A' : Set (Fin C.t → ℝ)} (h0' : (0 : Fin C.t → ℝ) ∈ A')
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 ≤ b₁) {b' : ℝ} (hb' : 0 ≤ b') :
    φ y₀ ∈ localRegion C SD A' b' := by
  refine ⟨0, ⟨((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)),
    ⟨h0', fun j _ => by simp [hb']⟩, ?_⟩, ?_⟩
  · funext x
    obtain ⟨z, rfl⟩ := C.σ.surjective x
    rcases z with i | j
    · rw [show C.σ (Sum.inl i) = tIdx C.σ i from rfl, prodToPi_apply_tIdx]
      rfl
    · rw [show C.σ (Sum.inr j) = nIdx C.σ j from rfl, prodToPi_apply_nIdx]
      rfl
  · rw [stripChart, inv_zero C SD h0 hb₁, translated, zero_add]

/-- **The local region contains the chart image of an open source neighbourhood of `y₀`**: the
open coordinate box `{|ζ_{t_i}| < r, |ζ_{n_j}| < b'}` lies in the strip box, its inverse image
under the strip normalisation is open, and translating by `y₀` gives the neighbourhood. -/
theorem exists_isOpen_subset_localRegion (hβ : 0 < β) {A' : Set (Fin C.t → ℝ)} {r : ℝ} (hr : 0 < r)
    (hrA : Metric.ball (0 : Fin C.t → ℝ) r ⊆ A') (hA'A : A' ⊆ A) {b' : ℝ} (hb' : 0 < b')
    (hb'b₁ : b' ≤ b₁) (hb'SD : b' ≤ SD.b) (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 ≤ b₁) :
    ∃ V : Set (Fin d → ℝ), IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V, φ y ∈ localRegion C SD A' b' := by
  -- the open coordinate box
  set O : Set (Fin d → ℝ) :=
    (⋂ i, {ζ | |ζ (tIdx C.σ i)| < r}) ∩ ⋂ j, {ζ | |ζ (nIdx C.σ j)| < b'} with hO
  have hOopen : IsOpen O := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i =>
        isOpen_lt (continuous_abs.comp (continuous_apply (tIdx C.σ i))) continuous_const
    · exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (continuous_abs.comp (continuous_apply (nIdx C.σ j))) continuous_const
  have hOz : O ⊆ zBox C.σ A' b' := by
    intro ζ hζ
    refine ⟨((fun i => ζ (tIdx C.σ i)), fun j => ζ (nIdx C.σ j)), ⟨hrA ?_, fun j _ => ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
      intro i
      rw [Real.norm_eq_abs]
      exact mem_iInter.1 hζ.1 i
    · exact mem_Icc.2 (abs_le.1 (mem_iInter.1 hζ.2 j).le)
    · funext x
      obtain ⟨z, rfl⟩ := C.σ.surjective x
      rcases z with i | j
      · rw [show C.σ (Sum.inl i) = tIdx C.σ i from rfl, prodToPi_apply_tIdx]
      · rw [show C.σ (Sum.inr j) = nIdx C.σ j from rfl, prodToPi_apply_nIdx]
  have hOS : O ⊆ stripImage C SD := hOz.trans (zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD)
  have h0O : (0 : Fin d → ℝ) ∈ O :=
    ⟨mem_iInter.2 fun i => by simpa using hr, mem_iInter.2 fun j => by simpa using hb'⟩
  -- the inverse image of the box is open
  have hρ : AnalyticOnNhd ℝ (unitRoot β (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot hβ (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  have hinvO : SD.inv '' O =
      SD.S ∩ rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀) ⁻¹' O := by
    ext y
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨SD.inv_mem (hOS hζ), by rw [mem_preimage, SD.apply_inv (hOS hζ)]; exact hζ⟩
    · rintro ⟨hyS, hy⟩
      exact ⟨_, hy, SD.inv_apply hyS⟩
  have hcont : ContinuousOn (rescale (nIdx C.σ j₀) (unitRoot β (2 * C.k j₀) C.unit₀)) SD.S :=
    fun y hy => (analyticAt_rescale _ (hρ y (SD.S_sub hy))).continuousAt.continuousWithinAt
  have hVopen : IsOpen (SD.inv '' O) := by
    rw [hinvO]
    exact hcont.isOpen_inter_preimage SD.S_open hOopen
  refine ⟨(fun y => y - y₀) ⁻¹' (SD.inv '' O), hVopen.preimage (continuous_id.sub continuous_const),
    ?_, ?_⟩
  · change y₀ - y₀ ∈ SD.inv '' O
    rw [sub_self]
    exact ⟨0, h0O, inv_zero C SD h0 hb₁⟩
  · rintro y ⟨ζ, hζ, hy⟩
    refine ⟨ζ, hOz hζ, ?_⟩
    change translated φ y₀ (SD.inv ζ) = φ y
    rw [translated, hy, sub_add_cancel]

/-- The part of the local region off the orthant images lies in the image of the null set of the
strip box on the normal hyperplanes. -/
theorem localRegion_sdiff_subset {A' : Set (Fin C.t → ℝ)} {b' : ℝ} :
    localRegion C SD A' b' \
        (⋃ s : Fin (C.n + 1) → Bool, orthantChart C SD s '' splitPosBox C.σ A' b') ⊆
      stripChart C SD '' (zBox C.σ A' b' ∩ {ζ | ¬ ∀ j, ζ (nIdx C.σ j) ≠ 0}) := by
  rintro x ⟨⟨ζ, hζ, rfl⟩, hx⟩
  refine ⟨ζ, ⟨hζ, fun hne => hx ?_⟩, rfl⟩
  have := mem_iUnion_splitOrthant (σ := C.σ) hζ hne
  rw [mem_iUnion] at this ⊢
  obtain ⟨s, hs⟩ := this
  refine ⟨s, ?_⟩
  rw [orthantChart_eq, image_comp]
  exact ⟨_, hs, rfl⟩

/-- The strip box on the normal hyperplanes is null. -/
theorem volume_zBox_inter_hyperplanes (A' : Set (Fin C.t → ℝ)) (b' : ℝ) :
    volume (zBox C.σ A' b' ∩ {ζ | ¬ ∀ j, ζ (nIdx C.σ j) ≠ 0}) = 0 := by
  refine measure_mono_null inter_subset_right ?_
  exact ae_iff.1 (ae_apply_nIdx_ne_zero (σ := C.σ))

/-! ### The local chart theorem -/

/-! ### The orthant core tiling as data -/

section Tiling

variable (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
  (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀)) {D : LocalisationData (Fin d → ℝ)}
  {A' : Set (Fin C.t → ℝ)} {b' : ℝ} (hμ : D.μ = volume.restrict (localRegion C SD A' b'))
  (hA' : IsCompact A') (hA'A : A' ⊆ A) (hb' : 0 < b') (hb'b₁ : b' ≤ b₁) (hb'SD : b' ≤ SD.b)
  (X : (Fin (C.n + 1) → Bool) → SplitBoxChart C.σ D A' b' β)
  (hXΨ : ∀ s, (X s).Ψ = orthantChart C SD s)

/-- The sign patterns enumerated. -/
noncomputable def signIdx : (Fin (C.n + 1) → Bool) ≃ Fin (Fintype.card (Fin (C.n + 1) → Bool)) :=
  Fintype.equivFin _

include hXΨ in
theorem toCorePiece_image (s : Fin (C.n + 1) → Bool) :
    ((X s).toCorePiece hA' hb').image =
      stripChart C SD '' (splitReflect C.σ s '' splitPosBox C.σ A' b') := by
  change (X s).Ψ '' splitPosBox C.σ A' b' = _
  rw [hXΨ, orthantChart_eq, image_comp]

include hA'A hb'b₁ hb'SD in
theorem splitReflect_image_subset_stripImageOff (s : Fin (C.n + 1) → Bool) :
    splitReflect C.σ s '' splitPosBox C.σ A' b' ⊆ stripImageOff C SD := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD (splitReflect_mem_zBox C s hy),
    fun j => splitReflect_apply_nIdx_ne_zero C s hy j⟩

include hXΨ in
theorem iUnion_toCorePiece_image :
    (⋃ I, ((X ((signIdx C).symm I)).toCorePiece hA' hb').image) =
      ⋃ s : Fin (C.n + 1) → Bool, orthantChart C SD s '' splitPosBox C.σ A' b' := by
  ext x
  simp only [mem_iUnion, toCorePiece_image C SD hA' hb' X hXΨ]
  constructor
  · rintro ⟨I, hI⟩
    refine ⟨(signIdx C).symm I, ?_⟩
    rw [orthantChart_eq, image_comp]
    exact hI
  · rintro ⟨s, hs⟩
    refine ⟨signIdx C s, ?_⟩
    rw [Equiv.symm_apply_apply]
    rw [orthantChart_eq, image_comp] at hs
    exact hs

include hφ hA'A hb'b₁ hb'SD in
/-- The image under the strip chart of the strip box on the normal hyperplanes is null. -/
theorem volume_stripChart_image_hyperplanes :
    volume (stripChart C SD '' (zBox C.σ A' b' ∩ {ζ | ¬ ∀ j, ζ (nIdx C.σ j) ≠ 0})) = 0 := by
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (volume_zBox_inter_hyperplanes C A' b')
  intro ζ hζ
  exact (analyticAt_stripChart C SD hφ
    (zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD hζ.1)).differentiableAt.differentiableWithinAt

/-- **The orthant core tiling** of the local region by the `2^{n+1}` orthant split box charts. -/
noncomputable def orthantCoreTiling : CoreTiling D β where
  Ω := localRegion C SD A' b'
  μ_eq := hμ
  M := Fintype.card (Fin (C.n + 1) → Bool)
  piece I := (X ((signIdx C).symm I)).toCorePiece hA' hb'
  image_subset I := by
    rw [toCorePiece_image C SD hA' hb' X hXΨ]
    refine image_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact splitReflect_mem_zBox C _ hy
  aedisjoint I J hIJ := by
    rw [toCorePiece_image C SD hA' hb' X hXΨ, toCorePiece_image C SD hA' hb' X hXΨ,
      ← (injOn_stripChart C SD hinj).image_inter
        (splitReflect_image_subset_stripImageOff C SD hA'A hb'b₁ hb'SD _)
        (splitReflect_image_subset_stripImageOff C SD hA'A hb'b₁ hb'SD _),
      (disjoint_splitOrthant (σ := C.σ) (fun hs => hIJ ((signIdx C).symm.injective hs))
        A' b').inter_eq, image_empty, measure_empty]
  δ₀ := 1
  δ₀_pos := one_pos
  gap := by
    have hΩm : MeasurableSet (localRegion C SD A' b') :=
      (isCompact_localRegion C SD hφ hA' hA'A hb'b₁ hb'SD).isClosed.measurableSet
    rw [hμ, ae_iff, Measure.restrict_apply' hΩm]
    refine measure_mono_null ?_
      (volume_stripChart_image_hyperplanes C SD hφ hA'A hb'b₁ hb'SD)
    intro z hz
    rw [mem_inter_iff, mem_ofPred_eq, Classical.not_imp] at hz
    refine localRegion_sdiff_subset C SD ⟨hz.2, ?_⟩
    rw [← iUnion_toCorePiece_image C SD hA' hb' X hXΨ]
    exact hz.1.1

theorem orthantCoreTiling_piece (I) :
    (orthantCoreTiling C SD hinj hφ hμ hA' hA'A hb' hb'b₁ hb'SD X hXΨ).piece I =
      (X ((signIdx C).symm I)).toCorePiece hA' hb' := rfl

theorem orthantCoreTiling_M :
    (orthantCoreTiling C SD hinj hφ hμ hA' hA'A hb' hb'b₁ hb'SD X hXΨ).M =
      Fintype.card (Fin (C.n + 1) → Bool) := rfl

end Tiling

/-- **The orthant split box charts of the local region.** At a divisor point of a hironaka chart
with centred chart data `C` and strip data `SD`, for every analytic observable `F` near `φ y₀`,
every compact tangential base `A ∋ 0` and every open `U' ∋ φ y₀`, some compact region
`Ω = g(zBox σ (A ∩ B̄_B) b') ∋ φ y₀` inside `U'` carries, for every localisation datum on `Ω` with
phase `K` and observable `F`, the `2^{n+1}` orthant split box charts with Jacobian exponents
`h_{n_j}`, phase exponents `k` and box side `b'`. -/
theorem exists_orthantSplitBoxCharts (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    {F : (Fin d → ℝ) → ℝ} (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (hA : IsCompact A)
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 < b₁) {U' : Set (Fin d → ℝ)} (hU' : IsOpen U')
    (hy₀U' : φ y₀ ∈ U') :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧ b' ≤ b₁ ∧ b' ≤ SD.b ∧
      IsCompact (localRegion C SD (A ∩ Metric.closedBall 0 B) b') ∧
      φ y₀ ∈ localRegion C SD (A ∩ Metric.closedBall 0 B) b' ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ translated φ y₀ '' C.V₀ ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ U' ∧
      ∀ D : LocalisationData (Fin d → ℝ),
        (∀ w ∈ C.V₀, D.phase (translated φ y₀ w) = K (translated φ y₀ w)) →
        (∀ w ∈ C.V₀, D.obs (translated φ y₀ w) = F (translated φ y₀ w)) →
        ∃ X : (Fin (C.n + 1) → Bool) →
          SplitBoxChart C.σ D (A ∩ Metric.closedBall 0 B) b' β,
          ∀ s, (X s).Ψ = orthantChart C SD s ∧ (X s).h = (fun j => h (nIdx C.σ j)) ∧
            (X s).k = C.k ∧ (X s).jac = orthantJac C SD s ∧
            ∀ (v : ↥(A ∩ Metric.closedBall 0 B)) (u : Fin (C.n + 1) → ℝ), (∀ j, |u j| ≤ b') →
              evalF (toEta b' ((X s).amp v)) u = orthantAmp C SD s F (v.1, u) := by
  classical
  -- the joint series at the tangential origin, for every sign pattern
  set b₂ : ℝ := min b₁ SD.b with hb₂
  have hb₂pos : 0 < b₂ := lt_min hb₁ SD.b_pos
  have h0dom : ∀ s : Fin (C.n + 1) → Bool,
      prodToPi C.σ ((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)) ∈ orthantDomain C SD s := by
    intro s
    rw [mem_orthantDomain_iff', splitReflect_prodToPi, reflectChart_apply, map_zero]
    refine zBox_subset_stripImage C SD le_rfl (min_le_left _ _) (min_le_right _ _) ?_
    refine ⟨(0, 0), ⟨h0, fun j _ => ?_⟩, rfl⟩
    exact ⟨by simp only [Pi.zero_apply]; linarith, by simp only [Pi.zero_apply]; exact hb₂pos.le⟩
  have han : ∀ s : Fin (C.n + 1) → Bool,
      ∃ (P : FormalMultilinearSeries ℝ (Fin C.t ⊕ Fin (C.n + 1) → ℝ) ℝ) (R : ℝ≥0∞),
        HasFPowerSeriesOnBall
          (fun w => orthantAmp C SD s F (w ∘ Sum.inl, w ∘ Sum.inr)) P 0 R := fun s =>
    analyticAt_orthantAmp_joint C SD hβ hφ hF s (w := 0) (by simpa using h0dom s)
  choose P R hPR using han
  have hr : ∀ s, ∃ r : ℝ≥0, (0 : ℝ≥0∞) < r ∧ (r : ℝ≥0∞) < R s := fun s =>
    ENNReal.lt_iff_exists_nnreal_btwn.1 (hPR s).r_pos
  choose r hr0 hrR using hr
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
  set ρ : ℝ≥0 := r s₀ with hρ
  have hρR : ∀ s, (ρ : ℝ≥0∞) < R s := fun s =>
    (ENNReal.coe_le_coe.2 (hs₀ s (Finset.mem_univ s))).trans_lt (hrR s)
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast hr0 s₀
  -- the margin
  set B₀ : ℝ := ρ / ((C.t + (C.n + 1) : ℕ) + 2) with hB₀
  have hB₀pos : 0 < B₀ := by positivity
  have hB₀ρ : ((C.t + (C.n + 1) : ℕ) : ℝ) * B₀ < ρ := by
    rw [hB₀, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hB₀1 : B₀ < ρ := by
    rw [hB₀, div_lt_iff₀ (by positivity)]
    nlinarith
  -- the shrinking into `U'`: continuity of the strip chart in product coordinates at the origin
  have h00 : prodToPi C.σ ((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)) = 0 := by
    funext x
    obtain ⟨z, rfl⟩ := C.σ.surjective x
    rcases z with i | j
    · rw [show C.σ (Sum.inl i) = tIdx C.σ i from rfl, prodToPi_apply_tIdx]
      rfl
    · rw [show C.σ (Sum.inr j) = nIdx C.σ j from rfl, prodToPi_apply_nIdx]
      rfl
  have hg0 : stripChart C SD (prodToPi C.σ ((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ))) =
      φ y₀ := by
    rw [h00, stripChart, inv_zero C SD h0 hb₁.le, translated, zero_add]
  have hgc : ContinuousAt (stripChart C SD ∘ prodToPi C.σ)
      ((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)) := by
    have hmem0 : prodToPi C.σ ((0 : Fin C.t → ℝ), (0 : Fin (C.n + 1) → ℝ)) ∈
        stripImage C SD := by
      have := h0dom (fun _ => true)
      rw [mem_orthantDomain_iff', splitReflect_prodToPi, reflectChart_apply, map_zero] at this
      exact this
    exact (analyticAt_stripChart C SD hφ hmem0).continuousAt.comp
      continuous_prodToPi.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hgc.preimage_mem_nhds (by
    rw [Function.comp_apply, hg0]
    exact hU'.mem_nhds hy₀U'))
  set B : ℝ := min B₀ (ε / 2) with hB
  have hBpos : 0 < B := lt_min hB₀pos (half_pos hε)
  have hBB₀ : B ≤ B₀ := min_le_left _ _
  have hBε : B ≤ ε / 2 := min_le_right _ _
  have hBρ : ((C.t + (C.n + 1) : ℕ) : ℝ) * B < ρ :=
    (mul_le_mul_of_nonneg_left hBB₀ (by positivity)).trans_lt hB₀ρ
  have hB1 : B < ρ := hBB₀.trans_lt hB₀1
  set b' : ℝ := min B b₂ with hb'
  have hb'pos : 0 < b' := lt_min hBpos hb₂pos
  have hb'b₁ : b' ≤ b₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hb'SD : b' ≤ SD.b := (min_le_right _ _).trans (min_le_right _ _)
  set A' := A ∩ Metric.closedBall (0 : Fin C.t → ℝ) B with hA'
  have hA'c : IsCompact A' := hA.inter_right Metric.isClosed_closedBall
  have hA'A : A' ⊆ A := inter_subset_left
  have h0' : (0 : Fin C.t → ℝ) ∈ A' := ⟨h0, by simp [hBpos.le]⟩
  have hAB : ∀ v ∈ A', ∀ i, |v i| ≤ B := by
    intro v hv i
    have h1 : ‖v‖ ≤ B := by simpa using hv.2
    exact (norm_le_pi_norm v i).trans h1
  -- the region and the localisation data
  set Ω := localRegion C SD A' b' with hΩ
  have hΩc : IsCompact Ω := isCompact_localRegion C SD hφ hA'c hA'A hb'b₁ hb'SD
  have hΩm : MeasurableSet Ω := hΩc.isClosed.measurableSet
  have hzS : zBox C.σ A' b' ⊆ stripImage C SD := zBox_subset_stripImage C SD hA'A hb'b₁ hb'SD
  have hΩU' : Ω ⊆ U' := by
    rintro _ ⟨ζ, ⟨p, hp, rfl⟩, rfl⟩
    refine hball (?_ : p ∈ Metric.ball 0 ε)
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    have h1 : ‖p.1‖ ≤ B := by simpa using hp.1.2
    have h2 : ‖p.2‖ ≤ b' := by
      rw [pi_norm_le_iff_of_nonneg hb'pos.le]
      intro j
      have := hp.2 j (mem_univ j)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨this.1, this.2⟩
    have hb'B : b' ≤ B := min_le_left _ _
    exact (max_le h1 (h2.trans hb'B)).trans_lt (hBε.trans_lt (half_lt_self hε))
  refine ⟨B, b', hBpos, hb'pos, hb'b₁, hb'SD, hΩc,
    mem_localRegion_zero C SD h0' h0 hb₁.le hb'pos.le,
    localRegion_subset C SD hA'A hb'b₁ hb'SD, hΩU', ?_⟩
  intro D hphase hobs
  have hX : ∀ s : Fin (C.n + 1) → Bool, ∃ X : SplitBoxChart C.σ D A' b' β,
      X.Ψ = orthantChart C SD s ∧ X.h = (fun j => h (nIdx C.σ j)) ∧ X.k = C.k ∧
        X.jac = orthantJac C SD s ∧
        ∀ (v : A') (u : Fin (C.n + 1) → ℝ), (∀ j, |u j| ≤ b') →
          evalF (toEta b' (X.amp v)) u = orthantAmp C SD s F (v.1, u) := fun s =>
    exists_splitBoxChart_orthant C SD hβ hφ hinj (D := D) hphase hobs
      hA'c hA'A hb'pos hb'b₁ hb'SD (min_le_left _ _) hBpos hAB s (hPR s) (hρR s) hBρ hB1
  choose X hX using hX
  exact ⟨X, hX⟩

/-- **The orthant core tiling of the local region.** Every localisation datum on the region
`Ω` of `exists_orthantSplitBoxCharts` with phase `K` and observable `F` has a core tiling. -/
theorem chart_local_coreTiling (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    {F : (Fin d → ℝ) → ℝ} (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (hA : IsCompact A)
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 < b₁) :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧
      IsCompact (localRegion C SD (A ∩ Metric.closedBall 0 B) b') ∧
      φ y₀ ∈ localRegion C SD (A ∩ Metric.closedBall 0 B) b' ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ translated φ y₀ '' C.V₀ ∧
      ∀ D : LocalisationData (Fin d → ℝ),
        D.μ = volume.restrict (localRegion C SD (A ∩ Metric.closedBall 0 B) b') →
        (∀ w ∈ C.V₀, D.phase (translated φ y₀ w) = K (translated φ y₀ w)) →
        (∀ w ∈ C.V₀, D.obs (translated φ y₀ w) = F (translated φ y₀ w)) →
        Nonempty (CoreTiling D β) := by
  obtain ⟨B, b', hB, hb', hb'b₁, hb'SD, hΩc, hmem, hsub, -, hX⟩ :=
    exists_orthantSplitBoxCharts C SD hβ hφ hinj hF hA h0 hb₁ isOpen_univ (mem_univ _)
  refine ⟨B, b', hB, hb', hΩc, hmem, hsub, ?_⟩
  intro D hμ hphase hobs
  obtain ⟨X, hX⟩ := hX D hphase hobs
  exact ⟨orthantCoreTiling C SD hinj hφ hμ (hA.inter_right Metric.isClosed_closedBall)
    inter_subset_left hb' hb'b₁ hb'SD X fun s => (hX s).1⟩

/-- **The local chart theorem.** At a divisor point of a hironaka chart with centred chart data
`C` and strip data `SD` (both existing by CCII and `exists_stripData`), for every analytic
observable `F` near `φ y₀` and every compact tangential base `A ∋ 0`, some compact region
`Ω = g(zBox σ (A ∩ B̄_B) b') ∋ φ y₀` has the full power–log cutoff expansion of
`∫_Ω F e^{−NK}`, with no series hypothesis. -/
theorem chart_local_cutoffExpansion (hβ : 0 < β) (hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀))
    (hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂)
    (hKm : Measurable K) (hK0 : ∀ w ∈ C.V₀, 0 ≤ K (translated φ y₀ w)) {F : (Fin d → ℝ) → ℝ}
    (hF : ∀ w ∈ C.V₀, AnalyticAt ℝ F (translated φ y₀ w)) (hA : IsCompact A)
    (h0 : (0 : Fin C.t → ℝ) ∈ A) (hb₁ : 0 < b₁) :
    ∃ (B b' : ℝ), 0 < B ∧ 0 < b' ∧
      IsCompact (localRegion C SD (A ∩ Metric.closedBall 0 B) b') ∧
      φ y₀ ∈ localRegion C SD (A ∩ Metric.closedBall 0 B) b' ∧
      localRegion C SD (A ∩ Metric.closedBall 0 B) b' ⊆ translated φ y₀ '' C.V₀ ∧
      ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
        CutoffExpansion Q Dg (fun N => ∫ x in localRegion C SD (A ∩ Metric.closedBall 0 B) b',
          F x * Real.exp (-N * K x)) c := by
  obtain ⟨B, b', hB, hb', hΩc, hmem, hsub, hT⟩ :=
    chart_local_coreTiling C SD hβ hφ hinj hF hA h0 hb₁
  set Ω := localRegion C SD (A ∩ Metric.closedBall 0 B) b' with hΩ
  have hΩm : MeasurableSet Ω := hΩc.isClosed.measurableSet
  have hΩmem : ∀ x ∈ Ω, ∃ w ∈ C.V₀, x = translated φ y₀ w := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact ⟨w, hw, rfl⟩
  have hFc : ContinuousOn F Ω := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hΩmem x hx
    exact (hF w hw).continuousAt.continuousWithinAt
  let D : LocalisationData (Fin d → ℝ) :=
    ⟨volume.restrict Ω, K, F, hKm,
      ae_restrict_of_forall_mem hΩm fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hΩmem x hx
        exact hK0 w hw,
      hFc.integrableOn_compact hΩc, 1, one_pos⟩
  obtain ⟨T⟩ := hT D rfl (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨Q, Dg, c, hQ, hc⟩ := T.cutoffExpansion hβ
  exact ⟨B, b', hB, hb', hΩc, hmem, hsub, Q, Dg, c, hQ, hc⟩

/-! ### The theorem at a divisor point of a hironaka chart -/

/-- A small strip base around the origin lies in a given closed ball. -/
theorem stripBase_subset_closedBall {t n : ℕ} (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d) (j₀ : Fin (n + 1))
    {ε : ℝ} (hε : 0 ≤ ε) :
    stripBase σ (Metric.closedBall 0 ε) j₀ ε ⊆ Metric.closedBall (0 : Fin d → ℝ) ε := by
  rintro _ ⟨p, hp, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hε]
  intro x
  obtain ⟨z, rfl⟩ := σ.surjective x
  rcases z with i | j
  · rw [show σ (Sum.inl i) = tIdx σ i from rfl, prodToPi_apply_tIdx]
    have h1 : ‖p.1‖ ≤ ε := by simpa using hp.1
    exact (norm_le_pi_norm p.1 i).trans h1
  · rw [show σ (Sum.inr j) = nIdx σ j from rfl, prodToPi_apply_nIdx, Real.norm_eq_abs]
    exact hp.2.2 j

/-- **The local theorem at a divisor point of a hironaka monomial chart.** If the phase `K ≥ 0`
is analytic on an open `U ∋ φ y₀` with `K (φ y₀) = 0`, the Jacobian exponents lie within the phase
exponents, and `F` is analytic on `U`, then some compact region `Ω ∋ φ y₀` inside `φ(W) ∩ U` has
the full power–log cutoff expansion of `∫_Ω F e^{−NK}`. -/
theorem IsMonomialChart.local_cutoffExpansion {dom : Set (Fin d → ℝ)} {e : Fin d →₀ ℕ}
    {W : Set (Fin d → ℝ)} (hc : IsMonomialChart K φ dom e h W) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    (hhe : ∀ j, 0 < h j → 0 < e j) (hy₀W : y₀ ∈ W) (hy₀U : φ y₀ ∈ U) (hKy₀ : K (φ y₀) = 0)
    {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U) :
    ∃ Ω : Set (Fin d → ℝ), IsCompact Ω ∧ φ y₀ ∈ Ω ∧ Ω ⊆ φ '' W ∧ Ω ⊆ U ∧
      ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
        CutoffExpansion Q Dg (fun N => ∫ x in Ω, F x * Real.exp (-N * K x)) c := by
  obtain ⟨C, hC⟩ := exists_centredChartData hc hU hK hK0 hhe hy₀W hy₀U hKy₀
  -- a closed ball around the origin inside the centred neighbourhood
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 C.V₀_open 0 C.zero_mem
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := half_pos hε
  have hcball : Metric.closedBall (0 : Fin d → ℝ) ε' ⊆ C.V₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  -- the strip data for the unit-removal rescaling of the phase unit at the normal index `0`
  set j₀ : Fin (C.n + 1) := 0 with hj₀
  set A : Set (Fin C.t → ℝ) := Metric.closedBall 0 ε' with hA
  have hρ : AnalyticOnNhd ℝ (unitRoot 1 (2 * C.k j₀) C.unit₀) C.V₀ := fun w hw =>
    analyticAt_unitRoot one_pos (by have := C.k_pos j₀; omega) (C.unit₀_analytic w hw)
      (C.unit₀_pos w hw)
  have hQ₀ : IsCompact (stripBase C.σ A j₀ ε') :=
    isCompact_stripBase (isCompact_closedBall _ _) j₀ ε'
  have hQ₀V : stripBase C.σ A j₀ ε' ⊆ C.V₀ :=
    (stripBase_subset_closedBall C.σ j₀ hε'pos.le).trans hcball
  obtain ⟨SD⟩ := exists_stripData C.V₀_open hρ (fun w _ => unitRoot_pos _ _ _ _) hQ₀ hQ₀V
    fun y hy => stripBase_apply_nIdx hy
  -- the chart hypotheses from the hironaka chart
  have hφ : ∀ y ∈ C.V₀, AnalyticAt ℝ φ (y + y₀) := fun y hy => hc.analyticOnNhd _ (hC y hy).1
  have hinj : ∀ w₁ ∈ C.V₀, ∀ w₂ ∈ C.V₀, monomialEval (w₁ + y₀) h ≠ 0 →
      monomialEval (w₂ + y₀) h ≠ 0 → φ (w₁ + y₀) = φ (w₂ + y₀) → w₁ = w₂ := by
    intro w₁ hw₁ w₂ hw₂ hm₁ hm₂ heq
    have := hc.injOn ⟨(hC w₁ hw₁).1, hm₁⟩ ⟨(hC w₂ hw₂).1, hm₂⟩ heq
    exact add_right_cancel this
  obtain ⟨B, b', -, -, hΩc, hmem, hsub, Q, Dg, c, hQ, hexp⟩ :=
    chart_local_cutoffExpansion C SD one_pos hφ hinj hKm (fun w hw => hK0 _ (hC w hw).2)
      (fun w hw => hF _ (hC w hw).2) (isCompact_closedBall _ _) (by simp [hA, hε'pos.le]) hε'pos
  refine ⟨_, hΩc, hmem, ?_, ?_, Q, Dg, c, hQ, hexp⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact ⟨w + y₀, (hC w hw).1, rfl⟩
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hsub hx
    exact (hC w hw).2

end Grammar
