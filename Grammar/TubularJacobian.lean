/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularGlobalInstance

/-!
# The tubular change of variables with its Jacobian density

Over a model graph chart `C` of a compact analytic LCI stratum (`TubularGlobalInstance`), the tube
is parametrised in product coordinates by
`ψ (z, n) = emb z + J_i(emb z)ᵀ n` on `Ω = {(z, n) : z ∈ W, ‖J_i(emb z)ᵀ n‖ < ε}`
(`tubeChart`, `tubeChartDom`). This file proves the paper's tubular change of variables
`∫_V F |dy| = ∫_{Φ⁻¹V} (F ∘ Φ) Φ^*|dy|` for the ambient Lebesgue density, with the pulled-back
density computed as a Jacobian:

* `volumePreservingConcat` — the canonical volume-preserving linear identification
  `ℝ^m × ℝ^r ≃ ℝ^d` (`m + r = d`) by coordinate concatenation (`measurePreserving_concat`).
* `tubeChart_mem_U`, `injOn_tubeChart`, `image_tubeChart` — `ψ` is injective on `Ω` with image the
  tube over the graph piece `U ∩ proj⁻¹ V'`.
* `tubeJac p = |det D(ψ ∘ L⁻¹)(L p)|` — positive on `Ω` (`tubeJac_pos`, from the analytic left
  inverse `y ↦ (ft (proj y), (J Jᵀ)⁻¹ J (ncoord y))` and multiplicativity of the determinant) and
  real-analytic on `Ω` (`analyticAt_tubeJac`, from analyticity of the determinant of an operator,
  `analyticAt_det`, and local constancy of its sign).
* `integral_tubeChart_image` — for measurable `B ⊆ Ω`,
  `∫_{ψ(B)} F(y) dy = ∫_B tubeJac p • F(ψ p) dp` (Lebesgue measure on both sides, product
  Lebesgue measure on `ℝ^m × ℝ^r`).

Scope: this is the pull-back of the *ambient Lebesgue* density; for `|μ| = ρ |dy|` the density is
`ρ(ψ p) · tubeJac p` and inherits positivity/analyticity from `ρ`. The fibre-integrated
(pushforward) form is not in this file.
-/

open scoped Manifold ContDiff Matrix
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory

namespace Grammar

section Concat

variable {m r d : ℕ}

/-- The index identification `Fin d ≃ Fin m ⊕ Fin r` from `m + r = d`. -/
def concatIndex (hm : m + r = d) : Fin d ≃ Fin m ⊕ Fin r :=
  (finCongr hm.symm).trans finSumFinEquiv.symm

/-- **Coordinate concatenation** `ℝ^m × ℝ^r ≃L ℝ^d`, `(u, v) ↦ (Sum.elim u v) ∘ concatIndex`. -/
noncomputable def volumePreservingConcat (hm : m + r = d) :
    ((Fin m → ℝ) × (Fin r → ℝ)) ≃L[ℝ] (Fin d → ℝ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin r) ℝ ℝ).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ (concatIndex hm))).toContinuousLinearEquiv

theorem volumePreservingConcat_apply (hm : m + r = d) (p : (Fin m → ℝ) × (Fin r → ℝ)) (k : Fin d) :
    volumePreservingConcat hm p k = Sum.elim p.1 p.2 (concatIndex hm k) := rfl

/-- Coordinate concatenation preserves Lebesgue measure (product Lebesgue measure on the left). -/
theorem measurePreserving_concat (hm : m + r = d) :
    MeasurePreserving (volumePreservingConcat hm) volume volume := by
  have h1 := (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => ℝ)).symm
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ) (concatIndex hm).symm
  refine (h2.comp h1).congr (volumePreservingConcat hm).continuous.measurable
    (Filter.Eventually.of_forall fun p => ?_)
  funext k
  obtain ⟨j, rfl⟩ : ∃ j, k = (concatIndex hm).symm j :=
    ⟨concatIndex hm k, (Equiv.symm_apply_apply _ k).symm⟩
  rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply, volumePreservingConcat_apply,
    Equiv.apply_symm_apply]
  cases j <;> rfl

theorem measurableEmbedding_concat (hm : m + r = d) :
    MeasurableEmbedding (volumePreservingConcat hm) :=
  (volumePreservingConcat hm).toHomeomorph.measurableEmbedding

end Concat

section Det

/-- **The determinant of an operator on `ℝ^d` is real-analytic in the operator** (a polynomial in
the matrix entries, each a continuous linear functional of the operator). -/
theorem analyticAt_det (d : ℕ) (L₀ : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    AnalyticAt ℝ (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) L₀ := by
  have hentry : ∀ i j : Fin d,
      AnalyticAt ℝ (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L (Pi.single j 1) i) L₀ := fun i j =>
    ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single j (1 : ℝ)))).analyticAt L₀
  have hfun : (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det) =
      ∑ σ : Equiv.Perm (Fin d), fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) =>
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * ∏ i, L (Pi.single i 1) (σ i) := by
    funext L
    rw [Finset.sum_apply]
    change LinearMap.det (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = _
    rw [← LinearMap.det_toMatrix', Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [hfun]
  refine Finset.analyticAt_sum _ fun σ _ => ?_
  have hprod : AnalyticAt ℝ
      (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => ∏ i, L (Pi.single i 1) (σ i)) L₀ := by
    have : (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => ∏ i, L (Pi.single i 1) (σ i)) =
        ∏ i, fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L (Pi.single i 1) (σ i) := by
      funext L
      rw [Finset.prod_apply]
    rw [this]
    exact Finset.analyticAt_prod _ fun i _ => hentry (σ i) i
  exact analyticAt_const.mul hprod

end Det

section TubeChart

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}

/-- The codimension does not exceed the dimension (full row rank at a stratum point). -/
theorem codim_le (A : CompatibleAnalyticLCIAtlas r S) (i : A.ι) {s : Fin d → ℝ} (hs : s ∈ S)
    (hsi : s ∈ A.V i) : r ≤ d := by
  have h := LinearMap.finrank_range_add_finrank_ker (A.J i s).mulVecLin
  have hr : LinearMap.range (A.J i s).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 (fullRowRank_iff_surjective.1 (A.fullRank i hs hsi))
  rw [hr, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

theorem ModelGraphChart.concat_eq (C : ModelGraphChart A s) : d - r + r = d :=
  Nat.sub_add_cancel (codim_le A C.i C.s_mem.1 (C.V'_subset C.s_mem.2))

/-- The canonical identification `ℝ^{d−r} × ℝ^r ≃L ℝ^d` attached to a model graph chart. -/
noncomputable def ModelGraphChart.concat (C : ModelGraphChart A s) :
    ((Fin (d - r) → ℝ) × (Fin r → ℝ)) ≃L[ℝ] (Fin d → ℝ) :=
  volumePreservingConcat C.concat_eq

theorem ModelGraphChart.emb_mem_S (C : ModelGraphChart A s) {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    C.emb z ∈ S := (C.emb_mem z hz).1

theorem ModelGraphChart.emb_mem_V (C : ModelGraphChart A s) {z : Fin (d - r) → ℝ} (hz : z ∈ C.W) :
    C.emb z ∈ A.V C.i := C.V'_subset (C.emb_mem z hz).2

/-- **The tube chart in product coordinates**: `ψ (z, n) = emb z + J_i(emb z)ᵀ n`. -/
noncomputable def tubeChart (C : ModelGraphChart A s) :
    (Fin (d - r) → ℝ) × (Fin r → ℝ) → Fin d → ℝ :=
  fun p => C.emb p.1 + rowFrame A C.i (C.emb p.1) p.2

/-- **The certified domain** `Ω = {(z, n) : z ∈ W, ‖J_i(emb z)ᵀ n‖ < ε}`. -/
def tubeChartDom (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    Set ((Fin (d - r) → ℝ) × (Fin r → ℝ)) :=
  {p | p.1 ∈ C.W ∧ ‖rowFrame A C.i (C.emb p.1) p.2‖ < T.eps}

theorem rowFrame_mem_normal (C : ModelGraphChart A s) {z : Fin (d - r) → ℝ} (hz : z ∈ C.W)
    (n : Fin r → ℝ) : rowFrame A C.i (C.emb z) n ∈ A.normal (C.emb z) := by
  rw [← range_rowFrame A C.i (C.emb_mem_S hz) (C.emb_mem_V hz)]
  exact LinearMap.mem_range_self _ n

theorem rowFrame_injective (A : CompatibleAnalyticLCIAtlas r S) (i : A.ι) {x : Fin d → ℝ}
    (hx : x ∈ S) (hxi : x ∈ A.V i) : Injective (rowFrame A i x) := fun u v h => by
  rw [← rowCoframe_rowFrame A i hx hxi u, h, rowCoframe_rowFrame A i hx hxi v]

/-- The row frame inverts the row coframe on normal vectors. -/
theorem rowFrame_rowCoframe (A : CompatibleAnalyticLCIAtlas r S) (i : A.ι) {x : Fin d → ℝ}
    (hx : x ∈ S) (hxi : x ∈ A.V i) {v : Fin d → ℝ} (hv : v ∈ A.normal x) :
    rowFrame A i x (rowCoframe A i x v) = v := by
  rw [← range_rowFrame A i hx hxi] at hv
  obtain ⟨u, rfl⟩ := hv
  rw [ContinuousLinearMap.coe_coe, rowCoframe_rowFrame A i hx hxi u]

/-- Points of the certified domain land in the tube, with foot `emb z` and normal vector
`J_i(emb z)ᵀ n`. -/
theorem tubeChart_mem (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T C) :
    tubeChart C p ∈ T.U ∧ T.proj (tubeChart C p) = C.emb p.1 ∧
      T.ncoord (tubeChart C p) = rowFrame A C.i (C.emb p.1) p.2 := by
  have hU : tubeChart C p ∈ T.U := (T.mem_U_iff _).2
    ⟨C.emb p.1, C.emb_mem_S hp.1, _, rowFrame_mem_normal C hp.1 p.2, hp.2, rfl⟩
  exact ⟨hU, T.proj_eq_of_decomp hU (C.emb_mem_S hp.1) (rowFrame_mem_normal C hp.1 p.2) hp.2 rfl⟩

/-- **`ψ` is injective on the certified domain** (tube uniqueness, `ft ∘ emb = id`, injectivity of
the row frame). -/
theorem injOn_tubeChart (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    InjOn (tubeChart C) (tubeChartDom T C) := by
  intro p hp q hq h
  obtain ⟨-, hp1, hp2⟩ := tubeChart_mem T C hp
  obtain ⟨-, hq1, hq2⟩ := tubeChart_mem T C hq
  have h1 : C.emb p.1 = C.emb q.1 := by rw [← hp1, ← hq1, h]
  have hz : p.1 = q.1 := by rw [← C.ft_emb p.1 hp.1, h1, C.ft_emb q.1 hq.1]
  have h2 : rowFrame A C.i (C.emb p.1) p.2 = rowFrame A C.i (C.emb p.1) q.2 := by
    rw [← hp2, h, hq2, hz]
  exact Prod.ext hz (rowFrame_injective A C.i (C.emb_mem_S hp.1) (C.emb_mem_V hp.1) h2)

/-- **The image of the certified domain is the tube over the graph piece** `U ∩ proj⁻¹ V'`. -/
theorem image_tubeChart (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    tubeChart C '' tubeChartDom T C = T.U ∩ T.proj ⁻¹' C.V' := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hU, hproj, -⟩ := tubeChart_mem T C hp
    refine ⟨hU, ?_⟩
    change T.proj (tubeChart C p) ∈ C.V'
    rw [hproj]
    exact (C.emb_mem _ hp.1).2
  · rintro ⟨hU, hV⟩
    have hpS : T.proj y ∈ S ∩ C.V' := ⟨T.proj_mem hU, hV⟩
    have hz : C.ft (T.proj y) ∈ C.W := C.ft_mem _ hpS
    have hVi : T.proj y ∈ A.V C.i := C.V'_subset hV
    have hnc : T.ncoord y ∈ A.normal (T.proj y) := T.ncoord_mem hU
    refine ⟨(C.ft (T.proj y), rowCoframe A C.i (T.proj y) (T.ncoord y)), ⟨hz, ?_⟩, ?_⟩
    · change ‖rowFrame A C.i (C.emb (C.ft (T.proj y)))
        (rowCoframe A C.i (T.proj y) (T.ncoord y))‖ < T.eps
      rw [C.emb_ft _ hpS, rowFrame_rowCoframe A C.i hpS.1 hVi hnc]
      exact T.ncoord_norm_lt hU
    · change C.emb (C.ft (T.proj y)) + rowFrame A C.i (C.emb (C.ft (T.proj y)))
        (rowCoframe A C.i (T.proj y) (T.ncoord y)) = y
      rw [C.emb_ft _ hpS, rowFrame_rowCoframe A C.i hpS.1 hVi hnc]
      exact (T.decomp y).symm

theorem contDiffAt_normalPart (C : ModelGraphChart A s) {n : ℕ∞ω}
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p.1 ∈ C.W) :
    ContDiffAt ℝ n (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      rowFrame A C.i (C.emb q.1) q.2) p := by
  have hemb : ContDiffAt ℝ n C.emb p.1 :=
    (C.contDiffOn_emb.of_le le_top).contDiffAt (C.W.isOpen.mem_nhds hp)
  have h1 : ContDiffAt ℝ n (fun q : (Fin (d - r) → ℝ) × (Fin r → ℝ) => C.emb q.1) p :=
    hemb.comp p contDiffAt_fst
  exact ((contDiffAt_rowFrame A C.i _).comp p h1).clm_apply contDiffAt_snd

/-- The tube chart is `C^n` (indeed analytic) over `W`. -/
theorem contDiffAt_tubeChart (C : ModelGraphChart A s) {n : ℕ∞ω}
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p.1 ∈ C.W) : ContDiffAt ℝ n (tubeChart C) p := by
  have hemb : ContDiffAt ℝ n C.emb p.1 :=
    (C.contDiffOn_emb.of_le le_top).contDiffAt (C.W.isOpen.mem_nhds hp)
  exact (hemb.comp p contDiffAt_fst).add (contDiffAt_normalPart C hp)

theorem isOpen_tubeChartDom (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    IsOpen (tubeChartDom T C) := by
  have hW : IsOpen {p : (Fin (d - r) → ℝ) × (Fin r → ℝ) | p.1 ∈ C.W} :=
    C.W.isOpen.preimage continuous_fst
  have hcont : ContinuousOn (fun p : (Fin (d - r) → ℝ) × (Fin r → ℝ) =>
      ‖rowFrame A C.i (C.emb p.1) p.2‖) {p | p.1 ∈ C.W} := fun p hp =>
    ((contDiffAt_normalPart C (n := 1) hp).continuousAt.norm).continuousWithinAt
  exact hcont.isOpen_inter_preimage hW isOpen_Iio

/-- **The flattened tube chart** `ψ ∘ L⁻¹ : ℝ^d → ℝ^d`. -/
noncomputable def flatChart (C : ModelGraphChart A s) : (Fin d → ℝ) → Fin d → ℝ :=
  fun w => tubeChart C (C.concat.symm w)

/-- **The Jacobian density** `tubeJac p = |det D(ψ ∘ L⁻¹)(L p)|`. -/
noncomputable def tubeJac (C : ModelGraphChart A s) (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) : ℝ :=
  |(fderiv ℝ (flatChart C) (C.concat p)).det|

theorem flatChart_concat (C : ModelGraphChart A s) (p : (Fin (d - r) → ℝ) × (Fin r → ℝ)) :
    flatChart C (C.concat p) = tubeChart C p := by
  simp only [flatChart, ContinuousLinearEquiv.symm_apply_apply]

theorem contDiffAt_flatChart (C : ModelGraphChart A s) {n : ℕ∞ω}
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p.1 ∈ C.W) :
    ContDiffAt ℝ n (flatChart C) (C.concat p) := by
  have hp' : (C.concat.symm (C.concat p)).1 ∈ C.W := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hp
  exact (contDiffAt_tubeChart C (n := n) hp').comp (C.concat p) C.concat.symm.contDiff.contDiffAt

/-- **The tubular change of variables with the Jacobian density**: for measurable `B ⊆ Ω`,
`∫_{ψ(B)} F(y) dy = ∫_B tubeJac p • F(ψ p) dp` (Lebesgue measure on `ℝ^d`, product Lebesgue
measure on `ℝ^{d−r} × ℝ^r`). -/
theorem integral_tubeChart_image (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {B : Set ((Fin (d - r) → ℝ) × (Fin r → ℝ))} (hB : MeasurableSet B) (hBΩ : B ⊆ tubeChartDom T C)
    (F : (Fin d → ℝ) → ℝ) :
    ∫ y in tubeChart C '' B, F y = ∫ p in B, tubeJac C p • F (tubeChart C p) := by
  have hLemb : MeasurableEmbedding C.concat := measurableEmbedding_concat C.concat_eq
  have himg : tubeChart C '' B = flatChart C '' (C.concat '' B) := by
    rw [Set.image_image]
    exact Set.image_congr fun p _ => (flatChart_concat C p).symm
  have hmeas : MeasurableSet (C.concat '' B) := hLemb.measurableSet_image.2 hB
  have hderiv : ∀ w ∈ C.concat '' B,
      HasFDerivWithinAt (flatChart C) (fderiv ℝ (flatChart C) w) (C.concat '' B) w := by
    rintro w ⟨p, hp, rfl⟩
    exact ((contDiffAt_flatChart C (n := ω) (hBΩ hp).1).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (flatChart C) (C.concat '' B) := by
    refine ((injOn_tubeChart T C).mono hBΩ).comp C.concat.symm.injective.injOn ?_
    rintro w ⟨p, hp, rfl⟩
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hp
  have hmp : MeasurePreserving C.concat volume volume := measurePreserving_concat C.concat_eq
  rw [himg, integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hderiv hinj F,
    hmp.setIntegral_image_emb hLemb]
  refine setIntegral_congr_fun hB fun p _ => ?_
  simp only [tubeJac, flatChart_concat]

/-- The tubular change of variables over the whole graph piece: `∫_{U ∩ proj⁻¹ V'} F dy =
∫_Ω tubeJac • F ∘ ψ`. -/
theorem integral_tube_piece (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    (F : (Fin d → ℝ) → ℝ) :
    ∫ y in T.U ∩ T.proj ⁻¹' C.V', F y =
      ∫ p in tubeChartDom T C, tubeJac C p • F (tubeChart C p) := by
  rw [← image_tubeChart T C]
  exact integral_tubeChart_image T C (isOpen_tubeChartDom T C).measurableSet subset_rfl F

end TubeChart

section Jacobian

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}

/-- **The analytic left inverse** of the flattened chart on the tube:
`y ↦ L (ft (proj y), (J Jᵀ)⁻¹ J (ncoord y))`. -/
noncomputable def flatInv (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s) :
    (Fin d → ℝ) → Fin d → ℝ := fun y =>
  C.concat (C.ft (T.proj y), rowCoframe A C.i (T.proj y) (T.ncoord y))

theorem flatInv_flatChart (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {w : Fin d → ℝ} (hw : w ∈ C.concat '' tubeChartDom T C) : flatInv T C (flatChart C w) = w := by
  obtain ⟨p, hp, rfl⟩ := hw
  obtain ⟨-, hproj, hnc⟩ := tubeChart_mem T C hp
  rw [flatChart_concat, flatInv, hproj, hnc, C.ft_emb _ hp.1,
    rowCoframe_rowFrame A C.i (C.emb_mem_S hp.1) (C.emb_mem_V hp.1)]

theorem contDiffAt_flatInv (T : AnalyticNormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {y : Fin d → ℝ} (hy : y ∈ T.U) (hV : T.proj y ∈ C.V') :
    ContDiffAt ℝ ω (flatInv T.toNormalTubularChart C) y := by
  have hproj : ContDiffAt ℝ ω T.proj y := (T.analyticAt_proj hy).contDiffAt
  have hnc : ContDiffAt ℝ ω T.toNormalTubularChart.ncoord y := (T.analyticAt_ncoord hy).contDiffAt
  have h1 : ContDiffAt ℝ ω (fun y => C.ft (T.proj y)) y := C.contDiff_ft.contDiffAt.comp y hproj
  have h2 : ContDiffAt ℝ ω (fun y => rowCoframe A C.i (T.proj y) (T.toNormalTubularChart.ncoord y))
      y :=
    ((contDiffAt_rowCoframe A C.i (T.proj_mem hy) (C.V'_subset hV)).comp y hproj).clm_apply hnc
  exact (C.concat : ((Fin (d - r) → ℝ) × (Fin r → ℝ)) →L[ℝ] (Fin d → ℝ)).contDiff.contDiffAt.comp y
    (h1.prodMk h2)

/-- **The Jacobian does not vanish on the certified domain**: the flattened chart has a
differentiable left inverse there, so `det Dφ · det Dψ = 1`. -/
theorem det_fderiv_flatChart_ne_zero (T : AnalyticNormalTubularChart A.normal S)
    (C : ModelGraphChart A s) {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)}
    (hp : p ∈ tubeChartDom T.toNormalTubularChart C) :
    (fderiv ℝ (flatChart C) (C.concat p)).det ≠ 0 := by
  have hopen : IsOpen (C.concat '' tubeChartDom T.toNormalTubularChart C) :=
    C.concat.toHomeomorph.isOpenMap _ (isOpen_tubeChartDom _ C)
  have hwmem : C.concat p ∈ C.concat '' tubeChartDom T.toNormalTubularChart C := ⟨p, hp, rfl⟩
  have hflat : HasFDerivAt (flatChart C) (fderiv ℝ (flatChart C) (C.concat p)) (C.concat p) :=
    ((contDiffAt_flatChart C (n := ω) hp.1).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨hU, hproj, -⟩ := tubeChart_mem T.toNormalTubularChart C hp
  have hinv : HasFDerivAt (flatInv T.toNormalTubularChart C)
      (fderiv ℝ (flatInv T.toNormalTubularChart C) (flatChart C (C.concat p)))
      (flatChart C (C.concat p)) := by
    rw [flatChart_concat]
    exact ((contDiffAt_flatInv T C hU (by rw [hproj]; exact (C.emb_mem _ hp.1).2)).differentiableAt
      (by simp)).hasFDerivAt
  have hcomp := hinv.comp (C.concat p) hflat
  have hid : HasFDerivAt (flatInv T.toNormalTubularChart C ∘ flatChart C)
      (ContinuousLinearMap.id ℝ (Fin d → ℝ)) (C.concat p) := by
    refine (hasFDerivAt_id _).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hwmem] with w' hw'
    exact flatInv_flatChart T.toNormalTubularChart C hw'
  have heq := hcomp.unique hid
  have hmul : (fderiv ℝ (flatInv T.toNormalTubularChart C) (flatChart C (C.concat p)) ∘L
      fderiv ℝ (flatChart C) (C.concat p)).det =
      (fderiv ℝ (flatInv T.toNormalTubularChart C) (flatChart C (C.concat p))).det *
        (fderiv ℝ (flatChart C) (C.concat p)).det := LinearMap.det_comp _ _
  have hone : (ContinuousLinearMap.id ℝ (Fin d → ℝ)).det = 1 := LinearMap.det_id
  rw [heq, hone] at hmul
  exact right_ne_zero_of_mul_eq_one hmul.symm

/-- **The Jacobian density is positive on the certified domain.** -/
theorem tubeJac_pos (T : AnalyticNormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T.toNormalTubularChart C) :
    0 < tubeJac C p :=
  abs_pos.2 (det_fderiv_flatChart_ne_zero T C hp)

/-- **The Jacobian density is real-analytic on the certified domain** (the determinant of the
analytic derivative, with locally constant sign). -/
theorem analyticAt_tubeJac (T : AnalyticNormalTubularChart A.normal S) (C : ModelGraphChart A s)
    {p : (Fin (d - r) → ℝ) × (Fin r → ℝ)} (hp : p ∈ tubeChartDom T.toNormalTubularChart C) :
    AnalyticAt ℝ (tubeJac C) p := by
  have hflatA : AnalyticAt ℝ (flatChart C) (C.concat p) :=
    (contDiffAt_flatChart C (n := ω) hp.1).analyticAt
  have hdetA : AnalyticAt ℝ (fun w => (fderiv ℝ (flatChart C) w).det) (C.concat p) :=
    (analyticAt_det d _).comp (g := fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L.det)
      (f := fderiv ℝ (flatChart C)) hflatA.fderiv
  have hcompA : AnalyticAt ℝ (fun q => (fderiv ℝ (flatChart C) (C.concat q)).det) p :=
    hdetA.comp (g := fun w => (fderiv ℝ (flatChart C) w).det) (f := ⇑C.concat)
      ((C.concat : ((Fin (d - r) → ℝ) × (Fin r → ℝ)) →L[ℝ] (Fin d → ℝ)).analyticAt p)
  rcases lt_or_gt_of_ne (det_fderiv_flatChart_ne_zero T C hp) with hneg | hpos
  · refine hcompA.neg.congr ?_
    filter_upwards [hcompA.continuousAt.eventually_lt continuousAt_const hneg] with q hq
    simp only [Pi.neg_apply, tubeJac, abs_of_neg hq]
  · refine hcompA.congr ?_
    filter_upwards [continuousAt_const.eventually_lt hcompA.continuousAt hpos] with q hq
    simp only [tubeJac, abs_of_pos hq]

end Jacobian

end Grammar
