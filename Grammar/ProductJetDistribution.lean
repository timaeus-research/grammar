/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffDistribution

/-!
# Jet-bounded functionals as distributions on a normed space and on a product (consult #124,
unit C5d-generic)

CDXVII (`SmoothCoeffDistribution`) turned a linear functional `T` on the test functions
`𝓓(ℝ^d, ℝ)` that is bounded by finitely many derivatives on a fixed set,

  `|T f| ≤ C · M`  whenever  `‖D^r f x‖ ≤ M` for all `r ≤ R` and all `x ∈ S`,

into a distribution `𝓓'(ℝ^d, ℝ)` in Mathlib's sense. The chart-face distributions of
consult #124 live on a **face space** `B × W` — base coordinates `s : B` along a face of the
resolved divisor and tangential coordinates `w : W` across it — and their natural estimates
involve only **tangential** derivatives: derivatives in `w` of the slice `w ↦ u (s, w)` at each
fixed `s`. This module supplies the generic infrastructure for that situation.

## The general normed space

Nothing in the LF argument of CDXVII uses finite dimensionality: Mathlib's `TestFunction` and
`Distribution` only ask for `[NormedAddCommGroup E] [NormedSpace ℝ E]`. We therefore restate

* `JetBoundOn R S f M := ∀ r ≤ R, ∀ x ∈ S, ‖iteratedFDeriv ℝ r f x‖ ≤ M` on an arbitrary normed
  space (definitionally the `JetBound` of CDXVI when `E = ℝ^d`: `jetBound_iff_jetBoundOn`);
* `continuous_of_jetBoundOn`: a jet-bounded linear functional is continuous on `𝓓(E, ℝ)` —
  on each `𝓓_K` it is dominated by the finite sup `max_{r ≤ R} N_{K,r}` of the defining
  seminorms (`Seminorm.IsBounded`, hence continuous by `WithSeminorms.continuous_of_isBounded`),
  and the LF topology is the finest making all the `𝓓_K ↪ 𝓓` continuous
  (`TestFunction.continuous_iff_continuous_comp`);
* `Distribution.ofJetBoundOn` packages this as a distribution, with `ofJetBoundOn_apply`;
* `Distribution.dsupport_subset_of_isVanishingOn'`: a distribution vanishing on the complement
  of a closed set is supported in that set.

## Tangential jet bounds on a product

For `u : B × W → ℝ` and `s : B` the slice `u_s := fun w => u (s, w)` is `u ∘ (inr + (s, 0))`,
the composition of `u` with a translation followed by the continuous linear inclusion
`inr : W →L[ℝ] B × W`. Translations do not change iterated derivatives
(`iteratedFDeriv_comp_add_right`) and composing with a continuous linear map on the right
composes the multilinear derivative with it (`ContinuousLinearMap.iteratedFDeriv_comp_right`);
since `‖inr‖ ≤ 1` for the sup norm on the product, the operator norm can only decrease:

  `‖D^r u_s (w)‖ ≤ ‖D^r u (s, w)‖`  (`norm_iteratedFDeriv_slice_le`).

Consequently a full jet bound on `Sb ×ˢ Sw` implies the tangential bound

  `TangentialJetBound R Sb Sw u M := ∀ s ∈ Sb, ∀ r ≤ R, ∀ w ∈ Sw, ‖D^r u_s (w)‖ ≤ M`

(`tangentialJetBound_of_jetBoundOn`), and a functional on `𝓓(B × W, ℝ)` bounded by tangential
jets is a fortiori bounded by full jets, hence a distribution
(`Distribution.ofTangentialJetBound`, with `ofTangentialJetBound_apply`). The reverse implication
fails — tangential bounds say nothing about `∂_s` — which is why the face functionals of
consult #124 are stated with `TangentialJetBound`.

## Compact support from neighbourhood vanishing

If `T f = 0` whenever `f` vanishes on an open neighbourhood of a compact `Kc`, then `T` vanishes
on `Kcᶜ` in Mathlib's sense (`tsupport f ⊆ Kcᶜ` makes `(tsupport f)ᶜ` an open neighbourhood of
`Kc` on which `f = 0`), so `dsupport T ⊆ Kc` and the support is compact
(`Distribution.dsupport_subset_of_forall_eqOn_zero`, `_of_forall_eventually_nhdsSet`,
`Distribution.isCompact_dsupport_of_forall_eqOn_zero`).

## Instances on the face space

For finite `ιb ιk` the face space `(ιb → ℝ) × (ιk → ℝ)` carries Mathlib's product instances
`Prod.normedAddCommGroup` and `Prod.normedSpace` with `‖(s, w)‖ = max ‖s‖ ‖w‖`
(`Prod.norm_def`), so everything above applies verbatim; the `example`s at the end record this.

Non-claims: no minimal order; no `C^R` test functions; no statement about the base derivatives
`∂_s`; the chart-face functionals themselves are the concrete units of consult #124.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff Distributions

namespace Grammar

namespace SmoothEngine

/-! ### Jet bounds on an arbitrary normed space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `‖D^r f x‖ ≤ M` for all `r ≤ R` and `x ∈ S`, on an arbitrary real normed space. -/
def JetBoundOn (R : ℕ) (S : Set E) (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ S, ‖iteratedFDeriv ℝ r f x‖ ≤ M

/-- On `ℝ^d` the general notion is the `JetBound` of CDXVI. -/
theorem jetBound_iff_jetBoundOn {d : ℕ} (R : ℕ) (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ)
    (M : ℝ) : JetBound R S f M ↔ JetBoundOn R S f M :=
  Iff.rfl

theorem JetBoundOn.mono {R R' : ℕ} {S S' : Set E} {f : E → ℝ} {M M' : ℝ}
    (h : JetBoundOn R S f M) (hR : R' ≤ R) (hS : S' ⊆ S) (hM : M ≤ M') : JetBoundOn R' S' f M' :=
  fun r hr x hx => (h r (hr.trans hR) x (hS hx)).trans hM

/-- The seminorm sum `max_{r ≤ R}` of a compactly supported test function dominates its jets. -/
theorem jetBoundOn_of_supSeminorm {K : TopologicalSpace.Compacts E} (R : ℕ) (S : Set E)
    (g : 𝓓_{K}(E, ℝ)) :
    JetBoundOn R S g
      ((Finset.range (R + 1)).sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K) g) := by
  intro r hr x _
  refine (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ le_top).trans ?_
  exact Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hr))

/-- ★ **Continuity from a jet bound** on an arbitrary normed space: a linear functional on
`𝓓(E, ℝ)` bounded by `C · max_{r ≤ R} sup_S ‖D^r f‖` is continuous for the LF topology. -/
theorem continuous_of_jetBoundOn {R : ℕ} {S : Set E} {C : ℝ}
    (T : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ)) (M : ℝ), 0 ≤ M →
      JetBoundOn R S f M → |T f| ≤ C * M) :
    Continuous T := by
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hK
  let L : 𝓓_{K}(E, ℝ) →ₗ[ℝ] ℝ := T.comp (TestFunction.ofSupportedInCLM ℝ hK).toLinearMap
  have hL : Continuous L := by
    refine WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) (norm_withSeminorms ℝ ℝ) L ?_
    refine Seminorm.IsBounded.of_real fun _ => ⟨Finset.range (R + 1), C, fun g => ?_⟩
    change ‖T (TestFunction.ofSupportedIn hK g)‖ ≤ C * _
    rw [Real.norm_eq_abs]
    exact hT _ _ (apply_nonneg _ _) (jetBoundOn_of_supSeminorm R S g)
  exact hL

/-- The linear functional underlying `Distribution.ofJetBoundOn`. -/
def Distribution.jetLinearMapOn (T : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) → ℝ)
    (hadd : ∀ f g, T (f + g) = T f + T g) (hsmul : ∀ (c : ℝ) f, T (c • f) = c * T f) :
    𝓓((⊤ : TopologicalSpace.Opens E), ℝ) →ₗ[ℝ] ℝ where
  toFun := T
  map_add' := hadd
  map_smul' c f := by simp only [hsmul, smul_eq_mul, RingHom.id_apply]

/-- ★ **A distribution from a jet-bounded linear functional** on an arbitrary normed space. -/
noncomputable def Distribution.ofJetBoundOn (R : ℕ) (S : Set E) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) → ℝ)
    (hadd : ∀ f g, T (f + g) = T f + T g) (hsmul : ∀ (c : ℝ) f, T (c • f) = c * T f)
    (hT : ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ)) (M : ℝ), 0 ≤ M →
      JetBoundOn R S f M → |T f| ≤ C * M) :
    𝓓'((⊤ : TopologicalSpace.Opens E), ℝ) where
  toLinearMap := Distribution.jetLinearMapOn T hadd hsmul
  cont := continuous_of_jetBoundOn (Distribution.jetLinearMapOn T hadd hsmul) hT

theorem Distribution.ofJetBoundOn_apply (R : ℕ) (S : Set E) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ) → ℝ) (hadd) (hsmul) (hT)
    (f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ)) :
    Distribution.ofJetBoundOn R S C T hadd hsmul hT f = T f := rfl

/-- The support of a distribution vanishing off a closed set lies in that set. -/
theorem Distribution.dsupport_subset_of_isVanishingOn'
    {T : 𝓓'((⊤ : TopologicalSpace.Opens E), ℝ)} {S : Set E}
    (hS : IsClosed S) (h : Distribution.IsVanishingOn T Sᶜ) :
    Distribution.dsupport T ⊆ S :=
  sInter_subset_of_mem ⟨h, hS⟩

/-! ### Compact support from neighbourhood vanishing -/

/-- A distribution killing every test function that vanishes on an open neighbourhood of `Kc`
vanishes on `Kcᶜ` in Mathlib's sense. -/
theorem Distribution.isVanishingOn_compl_of_forall_eqOn_zero
    {T : 𝓓'((⊤ : TopologicalSpace.Opens E), ℝ)} {Kc : Set E}
    (h : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ),
      (∃ U, IsOpen U ∧ Kc ⊆ U ∧ EqOn f 0 U) → T f = 0) :
    Distribution.IsVanishingOn T Kcᶜ := by
  intro f hf
  refine h f ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl, subset_compl_comm.1 hf, ?_⟩
  exact fun _ hx => image_eq_zero_of_notMem_tsupport hx

/-- ★ **Support from neighbourhood vanishing**: if `T f = 0` whenever `f = 0` on an open
neighbourhood of the closed set `Kc`, then `dsupport T ⊆ Kc`. -/
theorem Distribution.dsupport_subset_of_forall_eqOn_zero
    {T : 𝓓'((⊤ : TopologicalSpace.Opens E), ℝ)} {Kc : Set E} (hKc : IsClosed Kc)
    (h : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ),
      (∃ U, IsOpen U ∧ Kc ⊆ U ∧ EqOn f 0 U) → T f = 0) :
    Distribution.dsupport T ⊆ Kc :=
  Distribution.dsupport_subset_of_isVanishingOn' hKc
    (Distribution.isVanishingOn_compl_of_forall_eqOn_zero h)

/-- The filter form: `T f = 0` whenever `f x = 0` for `x` in a set-neighbourhood of `Kc`. -/
theorem Distribution.dsupport_subset_of_forall_eventually_nhdsSet
    {T : 𝓓'((⊤ : TopologicalSpace.Opens E), ℝ)} {Kc : Set E} (hKc : IsClosed Kc)
    (h : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ), (∀ᶠ x in 𝓝ˢ Kc, f x = 0) → T f = 0) :
    Distribution.dsupport T ⊆ Kc :=
  Distribution.dsupport_subset_of_forall_eqOn_zero hKc fun f ⟨U, hU, hKU, hfU⟩ =>
    h f (eventually_nhdsSet_iff_exists.2 ⟨U, hU, hKU, fun _ hx => hfU hx⟩)

/-- ★ **Compact support**: a distribution killing every test function vanishing near a compact
`Kc` has compact support (contained in `Kc`). -/
theorem Distribution.isCompact_dsupport_of_forall_eqOn_zero
    {T : 𝓓'((⊤ : TopologicalSpace.Opens E), ℝ)} {Kc : Set E} (hKc : IsCompact Kc)
    (h : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens E), ℝ),
      (∃ U, IsOpen U ∧ Kc ⊆ U ∧ EqOn f 0 U) → T f = 0) :
    IsCompact (Distribution.dsupport T) :=
  hKc.of_isClosed_subset Distribution.isClosed_dsupport
    (Distribution.dsupport_subset_of_forall_eqOn_zero hKc.isClosed h)

end General

/-! ### Tangential jet bounds on a product -/

section Product

variable {B W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `‖D^r_w u (s, w)‖ ≤ M` for all `s ∈ Sb`, `r ≤ R`, `w ∈ Sw`: a jet bound on the tangential
derivatives (in `w`, for each fixed base point `s`) only. -/
def TangentialJetBound (R : ℕ) (Sb : Set B) (Sw : Set W) (u : B × W → ℝ) (M : ℝ) : Prop :=
  ∀ s ∈ Sb, ∀ r ≤ R, ∀ w ∈ Sw, ‖iteratedFDeriv ℝ r (fun w => u (s, w)) w‖ ≤ M

/-- A tangential jet bound is a jet bound on every slice. -/
theorem tangentialJetBound_iff_forall_slice (R : ℕ) (Sb : Set B) (Sw : Set W) (u : B × W → ℝ)
    (M : ℝ) :
    TangentialJetBound R Sb Sw u M ↔ ∀ s ∈ Sb, JetBoundOn R Sw (fun w => u (s, w)) M :=
  Iff.rfl

theorem TangentialJetBound.mono {R R' : ℕ} {Sb Sb' : Set B} {Sw Sw' : Set W} {u : B × W → ℝ}
    {M M' : ℝ} (h : TangentialJetBound R Sb Sw u M) (hR : R' ≤ R) (hb : Sb' ⊆ Sb)
    (hw : Sw' ⊆ Sw) (hM : M ≤ M') : TangentialJetBound R' Sb' Sw' u M' :=
  fun s hs r hr w hw' => (h s (hb hs) r (hr.trans hR) w (hw hw')).trans hM

variable [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The slice `w ↦ u (s, w)` of a `C^n` function on the product is `C^n`. -/
theorem contDiff_slice {n : WithTop ℕ∞} {u : B × W → ℝ} (hu : ContDiff ℝ n u) (s : B) :
    ContDiff ℝ n (fun w => u (s, w)) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

/-- The slice is the composition of a translate of `u` with the inclusion `inr : W → B × W`. -/
theorem slice_eq_comp_inr (u : B × W → ℝ) (s : B) :
    (fun w => u (s, w)) = (fun z : B × W => u (z + (s, 0))) ∘ ContinuousLinearMap.inr ℝ B W := by
  ext w
  simp

/-- ★ **Tangential derivatives are dominated by full derivatives**: composing with the
norm-one inclusion `inr` after a translation can only shrink the operator norm. -/
theorem norm_iteratedFDeriv_slice_le {u : B × W → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℕ) (s : B)
    (w : W) :
    ‖iteratedFDeriv ℝ r (fun w => u (s, w)) w‖ ≤ ‖iteratedFDeriv ℝ r u (s, w)‖ := by
  have hshift : ContDiff ℝ ∞ (fun z : B × W => u (z + (s, 0))) :=
    hu.comp (contDiff_id.add contDiff_const)
  rw [slice_eq_comp_inr u s,
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ B W) hshift w
      (mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hpt : ContinuousLinearMap.inr ℝ B W w + (s, 0) = (s, w) := by simp
  rw [hpt]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ B W)

/-- ★ **Full jet bounds imply tangential jet bounds** on the product `Sb ×ˢ Sw`. -/
theorem tangentialJetBound_of_jetBoundOn {R : ℕ} {Sb : Set B} {Sw : Set W} {u : B × W → ℝ}
    {M : ℝ} (hu : ContDiff ℝ ∞ u) (h : JetBoundOn R (Sb ×ˢ Sw) u M) :
    TangentialJetBound R Sb Sw u M :=
  fun s hs r hr w hw => (norm_iteratedFDeriv_slice_le hu r s w).trans (h r hr (s, w) ⟨hs, hw⟩)

/-! ### Distributions on the product from a tangential bound -/

/-- ★ **A distribution on `B × W` from a tangentially jet-bounded linear functional**: a bound
by tangential derivatives on `Sb ×ˢ Sw` is a bound by full derivatives there. -/
noncomputable def Distribution.ofTangentialJetBound (R : ℕ) (Sb : Set B) (Sw : Set W) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ) → ℝ)
    (hadd : ∀ f g, T (f + g) = T f + T g) (hsmul : ∀ (c : ℝ) f, T (c • f) = c * T f)
    (hT : ∀ (f : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ)) (M : ℝ), 0 ≤ M →
      TangentialJetBound R Sb Sw f M → |T f| ≤ C * M) :
    𝓓'((⊤ : TopologicalSpace.Opens (B × W)), ℝ) :=
  Distribution.ofJetBoundOn R (Sb ×ˢ Sw) C T hadd hsmul fun f M hM hJ =>
    hT f M hM (tangentialJetBound_of_jetBoundOn f.contDiff hJ)

theorem Distribution.ofTangentialJetBound_apply (R : ℕ) (Sb : Set B) (Sw : Set W) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ) → ℝ) (hadd) (hsmul) (hT)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ)) :
    Distribution.ofTangentialJetBound R Sb Sw C T hadd hsmul hT f = T f := rfl

/-- The tangential estimate persists at the distribution level. -/
theorem Distribution.abs_ofTangentialJetBound_le (R : ℕ) (Sb : Set B) (Sw : Set W) (C : ℝ)
    (T : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ) → ℝ) (hadd) (hsmul) (hT)
    (f : 𝓓((⊤ : TopologicalSpace.Opens (B × W)), ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hJ : TangentialJetBound R Sb Sw f M) :
    |Distribution.ofTangentialJetBound R Sb Sw C T hadd hsmul hT f| ≤ C * M :=
  hT f M hM hJ

end Product

/-! ### The face space `(ιb → ℝ) × (ιk → ℝ)` -/

noncomputable example (ιb ιk : Type*) [Fintype ιb] [Fintype ιk] :
    NormedAddCommGroup ((ιb → ℝ) × (ιk → ℝ)) := inferInstance

noncomputable example (ιb ιk : Type*) [Fintype ιb] [Fintype ιk] :
    NormedSpace ℝ ((ιb → ℝ) × (ιk → ℝ)) := inferInstance

example {ιb ιk : Type*} [Fintype ιb] [Fintype ιk] (s : ιb → ℝ) (w : ιk → ℝ) :
    ‖((s, w) : (ιb → ℝ) × (ιk → ℝ))‖ = max ‖s‖ ‖w‖ := Prod.norm_def _

end SmoothEngine

end Grammar
