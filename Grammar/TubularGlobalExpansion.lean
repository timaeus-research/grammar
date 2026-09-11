/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TubularPushforward

/-!
# The per-stratum formula on the whole tube of a compact stratum

`TubularPushforward` proves the paper's `eq:per_stratum_expansion_coordfree` over one graph piece
of strucdual's tube. This file assembles the pieces over the **whole tube of a compact analytic LCI
stratum**: finitely many graph charts cover the stratum (`exists_graphCover`), their ambient
neighbourhoods are disjointified (`tubePiece`), the observable is truncated to each piece
(the truncation only rescales the fibre germs: `condContractionSeries_indicator`), and

`∫_{U} F dy = ∫_{U} G(proj y) dy`, `G = ∑_j 1_{P_j} · (∑_k ⟨D^k_⊥F, 𝖬^κ_{k,j}⟩)`

(`integral_tube_eq_integral_globalContraction`): the tube integral is the integral over the
stratum, against the pushforward of Lebesgue measure through the foot, of the piecewise
contraction series with the normalised fibre moments of the pieces.

Hypotheses: `F` integrable on the tube; on each chart, the fibre restrictions `n ↦ F(ψ_j(z,n))` have
power series at `0` whose balls lie in the certified fibres (`hRad`), carry the fibre measures and
dominate their moments — the paper's uniform-polydisc hypothesis, piece by piece.

Non-claims: the base density/moment data are those of the pieces (the disintegration of the
pulled-back density along the foot depends on the chart coordinate; only the product with the
base measure is intrinsic); ambient Lebesgue density.
-/

open scoped Manifold ContDiff Matrix ENNReal NNReal
open Bundle Set Function StrucDual.Geometry TopologicalSpace Topology MeasureTheory Filter

namespace Grammar

section Cover

variable {d r : ℕ} {S : Set (Fin d → ℝ)} (A : CompatibleAnalyticLCIAtlas r S)

/-- **A compact stratum is covered by finitely many graph pieces.** -/
theorem exists_graphCover (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ (n : ℕ) (Cs : ℕ → Σ x : Fin d → ℝ, ModelGraphChart A x),
      S ⊆ ⋃ j ∈ Finset.range n, (Cs j).2.V' := by
  classical
  obtain ⟨s₀, hs₀⟩ := hne
  let chart : ↥S → Σ x : Fin d → ℝ, ModelGraphChart A x := fun x =>
    ⟨x.1, Classical.choice (exists_modelGraphChart A x.2)⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : ↥S => (chart x).2.V')
    (fun x => (chart x).2.isOpen_V') (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (chart ⟨x, hx⟩).2.s_mem.2⟩)
  let L := t.toList
  refine ⟨L.length, fun j => if h : j < L.length then chart (L.get ⟨j, h⟩) else
    ⟨s₀, Classical.choice (exists_modelGraphChart A hs₀)⟩, fun x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (ht hx)
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hyt)
  refine mem_iUnion₂.2 ⟨j.1, Finset.mem_range.2 j.2, ?_⟩
  beta_reduce
  rw [dif_pos j.2]
  change x ∈ (chart (L.get j)).2.V'
  rw [hj]
  exact hxy

end Cover

section Pieces

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S}
  (T : NormalTubularChart A.normal S) (n : ℕ) (Cs : ℕ → Σ x : Fin d → ℝ, ModelGraphChart A x)

/-- The ambient neighbourhoods of the cover, padded by `∅`. -/
def coverSet (j : ℕ) : Set (Fin d → ℝ) := if j < n then (Cs j).2.V' else ∅

/-- The disjointified pieces of the cover. -/
def tubePiece (j : ℕ) : Set (Fin d → ℝ) := disjointed (coverSet n Cs) j

theorem isOpen_coverSet (j : ℕ) : IsOpen (coverSet n Cs j) := by
  unfold coverSet
  split_ifs
  · exact (Cs j).2.isOpen_V'
  · exact isOpen_empty

theorem measurableSet_tubePiece (j : ℕ) : MeasurableSet (tubePiece n Cs j) :=
  MeasurableSet.disjointed (fun j => (isOpen_coverSet n Cs j).measurableSet) j

theorem tubePiece_subset {j : ℕ} (hj : j < n) : tubePiece n Cs j ⊆ (Cs j).2.V' := by
  refine (disjointed_subset _ _).trans ?_
  unfold coverSet
  rw [if_pos hj]

theorem tubePiece_eq_empty {j : ℕ} (hj : ¬ j < n) : tubePiece n Cs j = ∅ := by
  refine subset_empty_iff.1 ((disjointed_subset _ _).trans ?_)
  unfold coverSet
  rw [if_neg hj]

theorem pairwise_disjoint_tubePiece : Pairwise (Disjoint on tubePiece n Cs) :=
  disjoint_disjointed _

theorem iUnion_tubePiece_of_cover (hcover : S ⊆ ⋃ j ∈ Finset.range n, (Cs j).2.V') :
    S ⊆ ⋃ j, tubePiece n Cs j := by
  intro x hx
  unfold tubePiece
  rw [iUnion_disjointed]
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 (hcover hx)
  refine mem_iUnion.2 ⟨j, ?_⟩
  unfold coverSet
  rw [if_pos (Finset.mem_range.1 hj)]
  exact hxj

/-- The tube over a measurable subset of the base is measurable (the foot is continuous on the
open tube). -/
theorem measurableSet_tube_preimage {P : Set (Fin d → ℝ)} (hP : MeasurableSet P) :
    MeasurableSet (T.U ∩ T.proj ⁻¹' P) := by
  classical
  have hf : Measurable (T.U.piecewise T.proj id) :=
    ContinuousOn.measurable_piecewise
      (fun y hy => (T.contDiffAt_proj hy).continuousAt.continuousWithinAt)
      continuous_id.continuousOn T.isOpen_U.measurableSet
  have : T.U ∩ T.proj ⁻¹' P = T.U ∩ (T.U.piecewise T.proj id) ⁻¹' P := by
    ext y
    constructor
    · rintro ⟨hU, hy⟩
      exact ⟨hU, by simpa [Set.piecewise, hU] using hy⟩
    · rintro ⟨hU, hy⟩
      exact ⟨hU, by simpa [Set.piecewise, hU] using hy⟩
  rw [this]
  exact T.isOpen_U.measurableSet.inter (hf hP)

/-- The tube over the `j`-th piece. -/
def tubeOverPiece (j : ℕ) : Set (Fin d → ℝ) := T.U ∩ T.proj ⁻¹' tubePiece n Cs j

theorem mem_tubeOverPiece_iff {j : ℕ} {y : Fin d → ℝ} :
    y ∈ tubeOverPiece T n Cs j ↔ y ∈ T.U ∧ T.proj y ∈ tubePiece n Cs j := Iff.rfl

theorem measurableSet_tubeOverPiece (j : ℕ) : MeasurableSet (tubeOverPiece T n Cs j) :=
  measurableSet_tube_preimage T (measurableSet_tubePiece n Cs j)

theorem pairwise_disjoint_tubeOverPiece : Pairwise (Disjoint on tubeOverPiece T n Cs) := by
  intro i j hij
  exact ((pairwise_disjoint_tubePiece n Cs hij).preimage T.proj).mono inter_subset_right
    inter_subset_right

theorem iUnion_tubeOverPiece (hcover : S ⊆ ⋃ j ∈ Finset.range n, (Cs j).2.V') :
    ⋃ j, tubeOverPiece T n Cs j = T.U := by
  ext y
  constructor
  · rintro hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy
    exact hj.1
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 (iUnion_tubePiece_of_cover n Cs hcover (T.proj_mem hy))
    exact mem_iUnion.2 ⟨j, hy, hj⟩

theorem tubeOverPiece_eq_empty {j : ℕ} (hj : ¬ j < n) : tubeOverPiece T n Cs j = ∅ := by
  unfold tubeOverPiece
  rw [tubePiece_eq_empty n Cs hj]
  simp

theorem tubeOverPiece_subset {j : ℕ} (hj : j < n) :
    tubeOverPiece T n Cs j ⊆ T.U ∩ T.proj ⁻¹' (Cs j).2.V' := fun _ hy =>
  ⟨hy.1, tubePiece_subset n Cs hj hy.2⟩

end Pieces

section Truncation

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S} {s : Fin d → ℝ}
  (T : NormalTubularChart A.normal S) (C : ModelGraphChart A s)

theorem normalContraction_eq_zero_of_measure_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {M : Type*}
    (N : (Fin d → ℝ) → Submodule ℝ E) (η : ∀ x, Measure (N x)) {k : ℕ}
    (hr : ∀ x, Integrable (fun ξ : N x => ‖ξ‖ ^ k) (η x)) (Φ : ∀ x, N x → M) (F : M → ℝ)
    {x : Fin d → ℝ} (h0 : η x = 0) : normalContraction N η hr Φ F x = 0 := by
  unfold normalContraction normalMoment
  rw [momentFunctional_congr_measure h0 (hr x) integrable_zero_measure, momentFunctional_apply,
    integral_zero_measure]

/-- Off `S ∩ V'` the normalised fibre measures vanish, so the contraction series vanishes. -/
theorem condContractionSeries_eq_zero_of_notMem (F : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ}
    (hx : x ∉ S ∩ C.V') : condContractionSeries T C F x = 0 := by
  have h0 : condTubeNormalMeasure T C x = 0 := by
    rw [condTubeNormalMeasure, tubeNormalMeasure, dif_neg hx, smul_zero]
  unfold condContractionSeries
  rw [tsum_congr fun k => normalContraction_eq_zero_of_measure_zero A.normal _
    (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) F h0, tsum_zero]

/-- Fibre germs: two observables agreeing on the tube fibre over `x` have the same normal jets at
`x`. -/
theorem eventuallyEq_fibre {x : Fin d → ℝ} (hx : x ∈ S) (G G' : (Fin d → ℝ) → ℝ)
    (hG : ∀ y ∈ T.U, T.proj y = x → G y = G' y) :
    (fun ξ : ↥(A.normal x) => G (additiveFamily A.normal x ξ)) =ᶠ[nhds 0]
      fun ξ => G' (additiveFamily A.normal x ξ) := by
  refine Metric.eventually_nhds_iff.2 ⟨T.eps, T.eps_pos, fun ξ hξ => ?_⟩
  rw [dist_zero_right] at hξ
  exact hG _ (additiveFamily_mem_tube T hx ξ hξ) (proj_additiveFamily T hx ξ hξ)

theorem normalContraction_congr_fibre {x : Fin d → ℝ} (hx : x ∈ S) (G G' : (Fin d → ℝ) → ℝ)
    (hG : ∀ y ∈ T.U, T.proj y = x → G y = G' y) (k : ℕ) :
    normalContraction A.normal (condTubeNormalMeasure T C)
        (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) G x =
      normalContraction A.normal (condTubeNormalMeasure T C)
        (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) G' x := by
  unfold normalContraction normalMoment
  congr 1
  unfold normalTaylorForm rawNormalJet
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (eventuallyEq_fibre T hx G G' hG) k).eq_of_nhds]

theorem normalContraction_eq_zero_of_fibre {x : Fin d → ℝ} (hx : x ∈ S) (G : (Fin d → ℝ) → ℝ)
    (hG : ∀ y ∈ T.U, T.proj y = x → G y = 0) (k : ℕ) :
    normalContraction A.normal (condTubeNormalMeasure T C)
        (integrable_norm_pow_condTubeNormalMeasure T C k) (additiveFamily A.normal) G x = 0 := by
  rw [normalContraction_congr_fibre T C hx G (fun _ => 0) hG k]
  unfold normalContraction normalMoment normalTaylorForm rawNormalJet
  rw [iteratedFDeriv_fun_zero, Pi.zero_apply, smul_zero, map_zero]

/-- **Truncation acts on fibre germs**: truncating the observable to the tube over a base set `P`
multiplies its contraction series by `1_P` (the normal jets at `x` only see the tube fibre over
`x`, on which the foot is `x`). -/
theorem condContractionSeries_indicator (F : (Fin d → ℝ) → ℝ) (P : Set (Fin d → ℝ))
    (x : Fin d → ℝ) :
    condContractionSeries T C ((T.U ∩ T.proj ⁻¹' P).indicator F) x =
      P.indicator (condContractionSeries T C F) x := by
  by_cases hx : x ∈ S ∩ C.V'
  · by_cases hxP : x ∈ P
    · rw [indicator_of_mem hxP]
      unfold condContractionSeries
      refine tsum_congr fun k => normalContraction_congr_fibre T C hx.1 _ F (fun y hy hp => ?_) k
      exact indicator_of_mem (Set.mem_inter hy
        (show y ∈ T.proj ⁻¹' P by rw [mem_preimage, hp]; exact hxP)) F
    · rw [indicator_of_notMem hxP]
      unfold condContractionSeries
      rw [tsum_congr fun k => normalContraction_eq_zero_of_fibre T C hx.1 _ (fun y hy hp => ?_) k,
        tsum_zero]
      exact indicator_of_notMem (fun h => hxP (by rw [← hp]; exact h.2)) F
  · rw [condContractionSeries_eq_zero_of_notMem T C _ hx]
    by_cases hxP : x ∈ P
    · rw [indicator_of_mem hxP, condContractionSeries_eq_zero_of_notMem T C F hx]
    · rw [indicator_of_notMem hxP]

end Truncation

section Assembly

variable {d r : ℕ} {S : Set (Fin d → ℝ)} {A : CompatibleAnalyticLCIAtlas r S}
  (T : NormalTubularChart A.normal S) (n : ℕ) (Cs : ℕ → Σ x : Fin d → ℝ, ModelGraphChart A x)

/-- **The global per-stratum integrand**: on the `j`-th piece, the contraction series of the
`j`-th chart with its normalised fibre moments. -/
noncomputable def globalContractionSeries (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (tubePiece n Cs j).indicator (condContractionSeries T (Cs j).2 F) x

theorem globalContractionSeries_of_mem {j : ℕ} (hj : j < n) {x : Fin d → ℝ}
    (hx : x ∈ tubePiece n Cs j) (F : (Fin d → ℝ) → ℝ) :
    globalContractionSeries T n Cs F x = condContractionSeries T (Cs j).2 F x := by
  unfold globalContractionSeries
  rw [Finset.sum_eq_single j (fun i _ hij => indicator_of_notMem (fun hxi =>
    Set.disjoint_left.1 (pairwise_disjoint_tubePiece n Cs hij) hxi hx) _)
    (fun h => absurd (Finset.mem_range.2 hj) h), indicator_of_mem hx]

/-- **The per-stratum formula on the whole tube of a compact stratum**: with finitely many graph
charts covering `S` and the paper's fibre power-series hypotheses on each chart,
`∫_{U} F dy = ∫_{U} G(proj y) dy` for the piecewise contraction series `G` with the normalised
fibre moments of the pieces — the tube integral is the integral over the stratum, against the
pushforward of Lebesgue measure through the foot, of the coordinate-free per-stratum integrand. -/
theorem integral_tube_eq_integral_globalContraction
    (hcover : S ⊆ ⋃ j ∈ Finset.range n, (Cs j).2.V') {F : (Fin d → ℝ) → ℝ}
    (hF : IntegrableOn F T.U)
    {q : ℕ → (Fin (d - r) → ℝ) → FormalMultilinearSeries ℝ (Fin r → ℝ) ℝ}
    {Rad : ℕ → (Fin (d - r) → ℝ) → ℝ≥0∞}
    (hq : ∀ j < n, ∀ z ∈ (Cs j).2.W,
      HasFPowerSeriesOnBall (fun m => F (tubeChart (Cs j).2 (z, m))) (q j z) 0 (Rad j z))
    (hRad : ∀ j < n, ∀ z ∈ (Cs j).2.W, ∀ m ∈ Metric.eball (0 : Fin r → ℝ) (Rad j z),
      (z, m) ∈ tubeChartDom T (Cs j).2)
    (hη : ∀ j < n, ∀ z ∈ (Cs j).2.W, ∀ᵐ m ∂fibreMeasure volume (tubeDensity T (Cs j).2) z,
      m ∈ Metric.eball (0 : Fin r → ℝ) (Rad j z))
    (hdom : ∀ j < n, ∀ z ∈ (Cs j).2.W, Summable fun k =>
      ‖q j z k‖ * ∫ m, ‖m‖ ^ k ∂fibreMeasure volume (tubeDensity T (Cs j).2) z) :
    ∫ y in T.U, F y = ∫ y in T.U, globalContractionSeries T n Cs F (T.proj y) := by
  classical
  have hU : T.U = ⋃ j, tubeOverPiece T n Cs j := (iUnion_tubeOverPiece T n Cs hcover).symm
  have hmeas : ∀ j, MeasurableSet (tubeOverPiece T n Cs j) := measurableSet_tubeOverPiece T n Cs
  have hdisj := pairwise_disjoint_tubeOverPiece T n Cs
  have hpiece : ∀ j < n,
      ∫ y in tubeOverPiece T n Cs j, F y =
        ∫ y in tubeOverPiece T n Cs j, globalContractionSeries T n Cs F (T.proj y) ∧
      IntegrableOn (fun y => globalContractionSeries T n Cs F (T.proj y))
        (tubeOverPiece T n Cs j) := by
    intro j hj
    have hsub : tubeOverPiece T n Cs j ⊆ T.U ∩ T.proj ⁻¹' (Cs j).2.V' :=
      tubeOverPiece_subset T n Cs hj
    have hU'meas : MeasurableSet (T.U ∩ T.proj ⁻¹' (Cs j).2.V') :=
      (restrictTube T (Cs j).2.V' (Cs j).2.isOpen_V').isOpen_U.measurableSet
    have hF'int : IntegrableOn ((tubeOverPiece T n Cs j).indicator F)
        (T.U ∩ T.proj ⁻¹' (Cs j).2.V') :=
      (hF.mono_set inter_subset_left).indicator (hmeas j)
    have hfib : ∀ z ∈ (Cs j).2.W, ∀ m ∈ Metric.eball (0 : Fin r → ℝ) (Rad j z),
        (tubeOverPiece T n Cs j).indicator F (tubeChart (Cs j).2 (z, m)) =
          (if (Cs j).2.emb z ∈ tubePiece n Cs j then (1 : ℝ) else 0) *
            F (tubeChart (Cs j).2 (z, m)) := by
      intro z hz m hm
      obtain ⟨hU'', hproj, -⟩ := tubeChart_mem T (Cs j).2 (hRad j hj z hz m hm)
      by_cases hz' : (Cs j).2.emb z ∈ tubePiece n Cs j
      · rw [if_pos hz', one_mul, indicator_of_mem]
        exact (mem_tubeOverPiece_iff T n Cs (j := j) (y := tubeChart (Cs j).2 (z, m))).2
          (And.intro hU'' (by rw [hproj]; exact hz'))
      · rw [if_neg hz', zero_mul, indicator_of_notMem]
        intro h
        exact hz' (by rw [← hproj]; exact ((mem_tubeOverPiece_iff T n Cs).1 h).2)
    have hq' : ∀ z ∈ (Cs j).2.W, HasFPowerSeriesOnBall
        (fun m => (tubeOverPiece T n Cs j).indicator F (tubeChart (Cs j).2 (z, m)))
        ((if (Cs j).2.emb z ∈ tubePiece n Cs j then (1 : ℝ) else 0) • q j z) 0 (Rad j z) := by
      intro z hz
      refine ((hq j hj z hz).const_smul).congr fun m hm => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (hfib z hz m hm).symm
    have hdom' : ∀ z ∈ (Cs j).2.W, Summable fun k =>
        ‖((if (Cs j).2.emb z ∈ tubePiece n Cs j then (1 : ℝ) else 0) • q j z) k‖ *
          ∫ m, ‖m‖ ^ k ∂fibreMeasure volume (tubeDensity T (Cs j).2) z := by
      intro z hz
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _)
        (integral_nonneg fun m => pow_nonneg (norm_nonneg _) _)) (fun k => ?_) (hdom j hj z hz)
      refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun m => pow_nonneg (norm_nonneg _) _)
      rw [show ((if (Cs j).2.emb z ∈ tubePiece n Cs j then (1 : ℝ) else 0) • q j z) k =
        (if (Cs j).2.emb z ∈ tubePiece n Cs j then (1 : ℝ) else 0) • q j z k from rfl, norm_smul]
      split_ifs <;> simp
    have h1 : ∫ y in tubeOverPiece T n Cs j, F y =
        ∫ y in T.U ∩ T.proj ⁻¹' (Cs j).2.V', (tubeOverPiece T n Cs j).indicator F y := by
      rw [setIntegral_indicator (hmeas j), inter_eq_right.2 hsub]
    have h2 := integral_tube_piece_eq_integral_condContraction T (Cs j).2 hF'int hq' (hη j hj) hdom'
    have h3 : ∀ y ∈ T.U ∩ T.proj ⁻¹' (Cs j).2.V',
        condContractionSeries T (Cs j).2 ((tubeOverPiece T n Cs j).indicator F) (T.proj y) =
          (tubeOverPiece T n Cs j).indicator
            (fun y => condContractionSeries T (Cs j).2 F (T.proj y)) y := by
      intro y hy
      rw [tubeOverPiece, condContractionSeries_indicator]
      by_cases hyP : T.proj y ∈ tubePiece n Cs j
      · rw [indicator_of_mem hyP, indicator_of_mem (Set.mem_inter hy.1 hyP)]
      · rw [indicator_of_notMem hyP, indicator_of_notMem (fun h => hyP h.2)]
    have h4 : ∫ y in T.U ∩ T.proj ⁻¹' (Cs j).2.V',
        condContractionSeries T (Cs j).2 ((tubeOverPiece T n Cs j).indicator F) (T.proj y) =
          ∫ y in tubeOverPiece T n Cs j, condContractionSeries T (Cs j).2 F (T.proj y) := by
      rw [setIntegral_congr_fun hU'meas h3, setIntegral_indicator (hmeas j), inter_eq_right.2 hsub]
    have h5 : ∀ y ∈ tubeOverPiece T n Cs j, condContractionSeries T (Cs j).2 F (T.proj y) =
        globalContractionSeries T n Cs F (T.proj y) :=
      fun _ hy => (globalContractionSeries_of_mem T n Cs hj hy.2 F).symm
    refine ⟨?_, ?_⟩
    · rw [h1, h2, h4, setIntegral_congr_fun (hmeas j) h5]
    · exact ((integrableOn_condContractionSeries_foot T (Cs j).2 (hF.mono_set inter_subset_left)
        (hq j hj) (hη j hj) (hdom j hj)).mono_set hsub).congr_fun h5 (hmeas j)
  have hfin : (⋃ j, tubeOverPiece T n Cs j) = ⋃ j ∈ Finset.range n, tubeOverPiece T n Cs j := by
    ext y
    simp only [mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨j, hj⟩
      by_cases h : j < n
      · exact ⟨j, h, hj⟩
      · rw [tubeOverPiece_eq_empty T n Cs h] at hj
        exact hj.elim
    · rintro ⟨j, -, hj⟩
      exact ⟨j, hj⟩
  have hint : IntegrableOn (fun y => globalContractionSeries T n Cs F (T.proj y)) T.U := by
    rw [hU, hfin]
    exact integrableOn_finset_iUnion.2 fun j hj => (hpiece j (Finset.mem_range.1 hj)).2
  have hFU : IntegrableOn F (⋃ j, tubeOverPiece T n Cs j) := hU ▸ hF
  have hintU : IntegrableOn (fun y => globalContractionSeries T n Cs F (T.proj y))
      (⋃ j, tubeOverPiece T n Cs j) := hU ▸ hint
  rw [hU, integral_iUnion hmeas hdisj hFU, integral_iUnion hmeas hdisj hintU,
    tsum_eq_sum (s := Finset.range n) (fun j hj => ?_),
    tsum_eq_sum (s := Finset.range n) (fun j hj => ?_)]
  · exact Finset.sum_congr rfl fun j hj => (hpiece j (Finset.mem_range.1 hj)).1
  · rw [tubeOverPiece_eq_empty T n Cs (by simpa using hj)]
    simp
  · rw [tubeOverPiece_eq_empty T n Cs (by simpa using hj)]
    simp

end Assembly

end Grammar
