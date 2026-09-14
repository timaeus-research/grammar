/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothFaceDistributionAnalytic

/-!
# Locality, representative independence and the cutoff pairing of the chart-face functionals
(consult #125 tidy-up)

* **Neighbourhood congruence** (`faceFunctional_congr_of_eqOn_nhds`): two smooth functions
  agreeing on an open neighbourhood of the closed face box have the same chart-face functional
  (linearity and the locality theorem applied to the difference).
* **Closed-box congruence** (`faceFunctional_congr_of_eqOn_centeredFaceBox`): agreement on the
  closed centred face box `[−a,a]^{base} × [−a,a]^K` already suffices — the tangential jets of the
  cylinder extensions agree on the centred active box (one-sided derivatives at the boundary are
  determined by the values on the box, `pdMulti_eqOn_centeredBox`), which is all the renormalised
  functional sees.
* **Extension independence** (`faceFunctional_faceJetOf_eq`): the face jet may be built from any
  smooth extension `g` of `obs ∘ ψ` from the closed chart box — the chart-face functional of the
  resulting face jet does not depend on the extension. Agreement of the observables on the face
  alone would not suffice (normal derivatives); agreement on the full-dimensional closed box does.
* **Cutoff pairing** (`faceFunctional_eq_faceDistribution_mulCutoff`): for any test function `χ`
  equal to one near the face box, `faceFunctional u = faceDistribution (χ · u)`; such cutoffs exist
  (`exists_cutoff_faceBox`). So the smooth functional is the canonical action of the compactly
  supported distribution `faceDistribution` on smooth functions, and the reconstruction of the
  coefficient distribution is a pairing of compactly supported face distributions with normal jets.

Together with CDXXII–CDXXIV this closes the Theorem C project (consult #125): the coefficient
distribution is reconstructed from fixed chart-face functionals — compactly supported finite-order
distributions on the chart-face spaces — applied to the normal jets of the observable, with the
dependence on the chosen smooth extensions removed.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

namespace BridgeInputs

variable {d : ℕ} (X : BridgeInputs d)

/-! ### Neighbourhood congruence -/

/-- ★ **Neighbourhood congruence**: the chart-face functional depends only on the germ of its
argument along the closed face box. -/
theorem faceFunctional_congr_of_eqOn_nhds (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u u' : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) (hu' : ContDiff ℝ ∞ u') {U : Set (X.PieceFaceSpace P J)}
    (hUo : IsOpen U) (hKU : X.faceBox P J ⊆ U) (heq : EqOn u u' U) :
    X.faceFunctional P J a μ q u = X.faceFunctional P J a μ q u' := by
  have hsub : X.faceFunctional P J a μ q (fun z => u z + (-1) * u' z) = 0 := by
    refine X.faceFunctional_eq_zero_of_eqOn_zero P J a μ q (hu.add (contDiff_const.mul hu'))
      hUo hKU fun z hz => ?_
    simp only [Pi.zero_apply, heq hz]
    ring
  rw [X.faceFunctional_add P J a μ q hu (contDiff_const.mul hu'),
    X.faceFunctional_smul P J a μ q hu' (-1)] at hsub
  linarith

/-! ### Closed-box congruence -/

/-- The closed centred face box `[−a,a]^{base} × [−a,a]^K`. -/
def centeredFaceBox (P : X.PIdx) (J : Finset (Fin (X.da P))) : Set (X.PieceFaceSpace P J) :=
  {z | (∀ j, |z.1 j| ≤ X.T.a P.1) ∧ ∀ k, |z.2 k| ≤ X.T.a P.1}

theorem faceBox_subset_centeredFaceBox (P : X.PIdx) (J : Finset (Fin (X.da P))) :
    X.faceBox P J ⊆ X.centeredFaceBox P J := by
  rintro ⟨s, w⟩ ⟨hs, hw⟩
  refine ⟨fun j => ?_, fun k => ?_⟩
  · have := hs j (Set.mem_univ j)
    rw [abs_of_nonneg this.1]; exact this.2
  · have := hw k (Set.mem_univ k)
    rw [abs_of_nonneg this.1]; exact this.2

theorem mem_centeredFaceBox_of_mem_centeredBox (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (s : Base (X.act P.1) (X.T.a P.1)) {v : Fin (X.da P) → ℝ}
    (hv : v ∈ centeredBox (X.da P) (X.T.a P.1)) :
    ((s.1, tangProj J v) : X.PieceFaceSpace P J) ∈ X.centeredFaceBox P J := by
  refine ⟨fun j => ?_, fun k => ?_⟩
  · change |s.1 j| ≤ _
    rw [abs_of_nonneg (Base_val_nonneg _ _ s j)]; exact Base_val_le _ _ s j
  · change |tangProj J v k| ≤ _
    rw [tangProj_apply]; exact hv k.1

/-- ★ **Closed-box congruence**: agreement on the closed centred face box suffices. -/
theorem faceFunctional_congr_of_eqOn_centeredFaceBox (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u u' : X.PieceFaceSpace P J → ℝ}
    (hu : ContDiff ℝ ∞ u) (hu' : ContDiff ℝ ∞ u')
    (heq : EqOn u u' (X.centeredFaceBox P J)) :
    X.faceFunctional P J a μ q u = X.faceFunctional P J a μ q u' := by
  unfold faceFunctional
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have hcyl : EqOn (cyl J u s.1) (cyl J u' s.1) (centeredBox (X.da P) (X.T.a P.1)) :=
    fun v hv => heq (X.mem_centeredFaceBox_of_mem_centeredBox P J s hv)
  have hjets := pdMulti_eqOn_centeredBox (V := (Set.univ : Set (Fin (X.da P) → ℝ))) isOpen_univ
    (X.T.a_pos P.1) (subset_univ _) (contDiff_cyl (B := X.BaseSpace P) J hu s.1).contDiffOn
    (contDiff_cyl (B := X.BaseSpace P) J hu' s.1).contDiffOn hcyl
  exact renormFunctional_congr ((X.ρfam P).smooth s) (contDiff_cyl (B := X.BaseSpace P) J hu s.1)
    (contDiff_cyl (B := X.BaseSpace P) J hu' s.1) (X.T.a_pos P.1) J a q
    fun α _ v hv _ => hjets α (lK J) fun i => abs_le.2 ⟨by linarith [(hv i).1, (X.T.a_pos P.1)],
      (hv i).2⟩

/-! ### Extension independence of the face jet -/

/-- The face jet built from an arbitrary smooth function `g` in place of the extension `obsExt`. -/
noncomputable def faceJetOf (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (g : (Fin d → ℝ) → ℝ) (z : X.PieceFaceSpace P J) : ℝ :=
  pdMulti a (lJ J) (fun v => g (X.TmAmb P z.1 v)) (glue J 0 z.2)

theorem faceJetOf_obsExt (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ) :
    X.faceJetOf P J a (X.obsExt P.1) = X.faceJet P J a := rfl

theorem TmAmb_mem_centeredBox (P : X.PIdx) {s : X.BaseSpace P} (hs : ∀ j, |s j| ≤ X.T.a P.1)
    {v : Fin (X.da P) → ℝ} (hv : ∀ j, |v j| ≤ X.T.a P.1) :
    X.TmAmb P s v ∈ centeredBox d (X.T.a P.1) := by
  intro i
  unfold TmAmb
  by_cases hi : i ∈ X.act P.1
  · rw [affineMap_apply_of_mem _ _ _ _ hi, abs_mul, WaterFilling.abs_sgn, one_mul]
    exact hv _
  · rw [affineMap_apply_of_not_mem _ _ _ _ hi]
    unfold scAmb
    rw [abs_mul, WaterFilling.abs_sgn, one_mul]
    exact hs _

theorem contDiff_faceJetOf (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (X.faceJetOf P J a g) := by
  have hfun : X.faceJetOf P J a g = fun z : X.PieceFaceSpace P J =>
      ((lJ J).map fun j => WaterFilling.sgn P.2 ((X.eqv P) j).1 ^ a j).prod *
        pdMulti (extendIdx (X.eqv P) a) ((lJ J).map fun j => ((X.eqv P) j).1) g
          (affineMap (X.eqv P) P.2 (X.scAmb P z.1) (glue J 0 z.2)) := by
    funext z
    unfold faceJetOf TmAmb
    rw [pdMulti_comp_affineMap]
  rw [hfun]
  have hglue : ContDiff ℝ ∞ fun z : X.PieceFaceSpace P J =>
      ((fun j : {j // ¬ inJ (X.act P.1) j} => WaterFilling.sgn P.2 j.1 * z.1 j), glue J 0 z.2) := by
    refine ContDiff.prodMk ?_ ((contDiff_glue_zero J).comp contDiff_snd)
    rw [contDiff_pi]
    intro j
    exact contDiff_const.mul ((contDiff_apply _ _ _).comp contDiff_fst)
  have haff : ContDiff ℝ ∞ fun z : X.PieceFaceSpace P J =>
      affineMap (X.eqv P) P.2 (X.scAmb P z.1) (glue J 0 z.2) :=
    (contDiff_affineMap_pair (X.eqv P) P.2).comp hglue
  exact contDiff_const.mul ((contDiff_pdMulti hg (extendIdx (X.eqv P) a) _).comp haff)

/-- Two smooth functions agreeing on the closed chart box give face jets agreeing on the closed
centred face box. -/
theorem faceJetOf_eqOn (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    {g g' : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hg' : ContDiff ℝ ∞ g')
    (heq : EqOn g g' (centeredBox d (X.T.a P.1))) :
    EqOn (X.faceJetOf P J a g) (X.faceJetOf P J a g') (X.centeredFaceBox P J) := by
  rintro ⟨s, w⟩ ⟨hs, hw⟩
  unfold faceJetOf TmAmb
  simp only
  have hjets := pdMulti_eqOn_centeredBox (X.T.V_open P.1) (X.T.a_pos P.1) (X.T.box_subset_V P.1)
    hg.contDiffOn hg'.contDiffOn heq
  rw [pdMulti_comp_affineMap, pdMulti_comp_affineMap]
  have hmem : X.TmAmb P s (glue J 0 w) ∈ centeredBox d (X.T.a P.1) :=
    X.TmAmb_mem_centeredBox P hs fun j => ?_
  · unfold TmAmb at hmem
    beta_reduce
    rw [hjets _ _ hmem]
  by_cases hj : j ∈ J
  · rw [glue_apply_of_mem J _ _ hj]; simp [(X.T.a_pos P.1).le]
  · rw [glue_apply_of_not_mem J _ _ hj]; exact hw ⟨j, hj⟩

/-- ★★ **Extension independence**: the chart-face functional of the face jet does not depend on
the smooth extension of `obs ∘ ψ` from the closed chart box. -/
theorem faceFunctional_faceJetOf_eq (P : X.PIdx) (J : Finset (Fin (X.da P))) (a : Fin (X.da P) → ℕ)
    (μ : ℝ) (q : ℕ) {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (heq : EqOn g (X.obs ∘ X.T.ψ P.1) (centeredBox d (X.T.a P.1))) :
    X.faceFunctional P J a μ q (X.faceJetOf P J a g) =
      X.faceFunctional P J a μ q (X.faceJet P J a) := by
  rw [← X.faceJetOf_obsExt P J a]
  refine X.faceFunctional_congr_of_eqOn_centeredFaceBox P J a μ q (X.contDiff_faceJetOf P J a hg)
    (X.contDiff_faceJetOf P J a (X.contDiff_obsExt P.1)) ?_
  refine X.faceJetOf_eqOn P J a hg (X.contDiff_obsExt P.1) fun u hu => ?_
  rw [heq hu, X.obsExt_eq P.1 hu]
  rfl

/-! ### The cutoff pairing -/

/-- A test function times a smooth function is a test function. -/
noncomputable def mulCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ)) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    𝓓((⊤ : TopologicalSpace.Opens E), ℝ) where
  toFun := fun z => χ z * u z
  contDiff' := χ.contDiff.mul hu
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := subset_univ _

theorem mulCutoff_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ)) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (z : E) :
    mulCutoff χ hu z = χ z * u z := rfl

/-- ★ **Cutoff pairing**: for a test function equal to one near the face box, the chart-face
functional of `u` is the chart-face distribution applied to `χ · u`. -/
theorem faceFunctional_eq_faceDistribution_mulCutoff (P : X.PIdx) (J : Finset (Fin (X.da P)))
    (a : Fin (X.da P) → ℕ) (μ : ℝ) (q : ℕ) {u : X.PieceFaceSpace P J → ℝ} (hu : ContDiff ℝ ∞ u)
    (χ : 𝓓((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ))
    (hχ : ∀ᶠ z in 𝓝ˢ (X.faceBox P J), χ z = 1) :
    X.faceFunctional P J a μ q u = X.faceDistribution P J a μ q (mulCutoff χ hu) := by
  rw [faceDistribution_apply]
  obtain ⟨U, hUo, hKU, hU1⟩ := eventually_nhdsSet_iff_exists.mp hχ
  refine X.faceFunctional_congr_of_eqOn_nhds P J a μ q hu (mulCutoff χ hu).contDiff hUo hKU
    fun z hz => ?_
  rw [mulCutoff_apply, hU1 z hz, one_mul]

/-- Smooth cutoffs equal to one near the face box exist. -/
theorem exists_cutoff_faceBox (P : X.PIdx) (J : Finset (Fin (X.da P))) :
    ∃ χ : 𝓓((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ),
      ∀ᶠ z in 𝓝ˢ (X.faceBox P J), χ z = 1 := by
  obtain ⟨f, hf, h0, h1, -⟩ := exists_contDiff_zero_one_nhds
    (E := X.PieceFaceSpace P J) (s := (Metric.thickening 1 (X.faceBox P J))ᶜ)
    (t := X.faceBox P J) Metric.isOpen_thickening.isClosed_compl
    (X.isCompact_faceBox P J).isClosed
    (disjoint_compl_left_iff_subset.mpr (Metric.self_subset_thickening one_pos _))
  have hsupp : tsupport f ⊆ Metric.cthickening 1 (X.faceBox P J) := by
    refine closure_minimal ?_ Metric.isClosed_cthickening
    intro z hz
    by_contra hzc
    obtain ⟨V, hVo, hVs, hV0⟩ := eventually_nhdsSet_iff_exists.mp h0
    exact hz (hV0 z (hVs fun hzt => hzc (Metric.thickening_subset_cthickening _ _ hzt)))
  refine ⟨⟨f, hf, ?_, subset_univ _⟩, h1⟩
  exact ((X.isCompact_faceBox P J).cthickening (r := 1)).of_isClosed_subset (isClosed_tsupport f)
    hsupp

/-- ★★ **The reconstruction as a pairing of compactly supported face distributions with the normal
jets**, for any family of cutoffs equal to one near the face boxes. -/
theorem coeffDistribution_eq_sum_faceDistribution (μ : ℝ) (q : ℕ)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (Fin d → ℝ)), ℝ))
    (χ : ∀ P : X.PIdx, ∀ J : Finset (Fin (X.da P)),
      𝓓((⊤ : TopologicalSpace.Opens (X.PieceFaceSpace P J)), ℝ))
    (hχ : ∀ P J, ∀ᶠ z in 𝓝ˢ (X.faceBox P J), χ P J z = 1) :
    X.coeffDistribution μ q f = ∑ I : Fin (Fintype.card X.PIdx),
      ∑ J : Finset (Fin (X.da (X.en I))), ∑ a ∈ idxL (X.pieceDepth (X.en I) μ) (lJ J),
        faceW J a * X.faceDistribution (X.en I) J a μ q
          (mulCutoff (χ (X.en I) J) (X.contDiff_faceJetObs (X.en I) J a f f.contDiff)) := by
  rw [X.coeffDistribution_eq_sum_faceFunctional μ q f]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun a _ => ?_
  rw [X.faceFunctional_eq_faceDistribution_mulCutoff (X.en I) J a μ q
    (X.contDiff_faceJetObs (X.en I) J a f f.contDiff) (χ (X.en I) J) (hχ (X.en I) J)]

end BridgeInputs

end SmoothEngine

end Grammar
