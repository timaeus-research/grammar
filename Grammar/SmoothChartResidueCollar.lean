/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothStratumMeasure
import Grammar.SmoothStratumIntegrable
import Grammar.FaceRestrictionOperators

/-!
# The uniform collar and the joint integrability of the face integrand

Unit 1 of the chart-pushforward identity (consult #135). On a piece `p` of the resolved core
transport the amplitude of the observable `G` factors on the closed box as
`ρloc(Tm p s v) · G(divPt p s v)` (`amp_withF_eq`): the F-free part `ρloc = ω·|b|·prior∘ψ` is the
transport density, and `G` enters only through its value at the divisor point. The amplitude is
jointly continuous and bounded on `S × [0,b]^{da}` (`exists_bound_amp`). For a test `G` vanishing
near the deep zero fibre `D_{c+1}`, the amplitude of `withF G` vanishes on a UNIFORM collar of the
deep set `{v ∈ [0,b]^{da} : ≥ c+1 zero coordinates}` (`exists_collar`): at a deep face point the
divisor point either lies in `D_{c+1}` (so `G` vanishes nearby) or off the prior support (so
`ρloc` vanishes nearby), and the tube lemma over the compact base makes the collar uniform in the
base point. Consequently the face integrand `amp(s, glue J 0 w) · residueWeight(w)` of a size-`c`
face is JOINTLY integrable against `base ⊗ volume|box` (`integrable_faceIntegrand`): it vanishes
where some complementary coordinate is `< ε` and is bounded elsewhere. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

namespace SmoothEngine

/-! ### The deep set is compact -/

theorem isClosed_zeroCard (d : ℕ) (c : ℕ) :
    IsClosed {v : Fin d → ℝ | c + 1 ≤ ((univ : Finset (Fin d)).filter fun i => v i = 0).card} := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro v hv
  have hall : ∀ᶠ v' in 𝓝 v, ∀ i, v i ≠ 0 → v' i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : v i = 0
    · exact Eventually.of_forall fun _ h => absurd hi h
    · exact ((continuous_apply i).continuousAt.eventually_ne hi).mono fun v' hv' _ => hv'
  filter_upwards [hall] with v' hv'
  intro hcard
  apply hv
  refine hcard.trans (Finset.card_le_card fun i hi => ?_)
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra h
  exact hv' i h hi.2

theorem isCompact_deepSet (d : ℕ) (b : ℝ) (c : ℕ) : IsCompact (deepSet d b c) :=
  (isCompact_closedBox b).inter_right (isClosed_zeroCard d c)

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)
  (p : (Ξ.X Y).PIdx)

/-! ### The amplitude of a piece -/

/-- The amplitude of a piece is jointly continuous on `S × [0,b]^{da}`. -/
theorem continuousOn_amp_pair :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      (Ξ.amp Y p).amp z.1 z.2) (univ ×ˢ closedBox _ (Y.T.a p.1)) := by
  have h := (Ξ.amp Y p).deriv_cont 0
  simpa only [pdMulti_zero] using h

/-- The amplitude of a piece is bounded on `S × [0,b]^{da}`. -/
theorem exists_bound_amp : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ∀ v ∈ closedBox _ (Y.T.a p.1),
    |(Ξ.amp Y p).amp s v| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ.prod (isCompact_closedBox (d := (Ξ.X Y).da p)
    (Y.T.a p.1))).exists_bound_of_continuousOn (Ξ.continuousOn_amp_pair Y p)
  refine ⟨max M 0, le_max_right _ _, fun s v hv => ?_⟩
  have := hM (s, v) ⟨mem_univ _, hv⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- The amplitude family of the piece `p` for the observable `G`, typed over the data of `Ξ`
(the chart machinery `Ξ.X Y` does not depend on the observable). -/
noncomputable def ampObs {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1) :=
  (Ξ.withF G hG).amp Y p

theorem ampObs_amp {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) (v : Fin ((Ξ.X Y).da p) → ℝ) :
    (Ξ.ampObs Y p hG).amp s v = ((Ξ.withF G hG).amp Y p).amp s v := rfl

/-- The bound for the amplitude of an observable `G`, stated in the types of `Ξ`. -/
theorem exists_bound_amp_withF {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      ∀ v ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1), |(Ξ.ampObs Y p hG).amp s v| ≤ M :=
  (Ξ.withF G hG).exists_bound_amp Y p

/-- **The amplitude factorisation**: on the closed box the amplitude of the observable `G` is the
transport density `ρloc` at the chart point times `G` at the divisor point. -/
theorem amp_withF_eq {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    (Ξ.ampObs Y p hG).amp s v =
      (Ξ.X Y).ρloc p.1 ((Ξ.X Y).Tm p s v) * G (Ξ.divPt Y p s v) := by
  have hbox : (Ξ.X Y).Tm p s v ∈ centeredBox d (Y.T.a p.1) :=
    (Ξ.X Y).Tm_mem_box p s fun j => (mem_closedBox.1 hv) j
  rw [ampObs_amp]
  change (Ξ.withF G hG).G Y p.1 ((Ξ.X Y).Tm p s v) = _
  rw [(Ξ.withF G hG).G_eq Y p.1 hbox]
  change (Ξ.X Y).ρloc p.1 ((Ξ.X Y).Tm p s v) * G (Y.chartInv p.1 ((Ξ.X Y).Tm p s v)) = _
  rw [Y.chartInv_eq p.1 (Y.box_subset_target p.1 hbox)]
  rfl

/-- The divisor point is jointly continuous on `S × [0,b]^{da}`. -/
theorem continuousOn_divPt_pair :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      Ξ.divPt Y p z.1 z.2) (univ ×ˢ closedBox _ (Y.T.a p.1)) :=
  (Y.φ p.1).continuousOn_symm.comp ((Ξ.X Y).continuous_Tm p).continuousOn
    fun z hz => Ξ.facePt_mem_target Y p z.1 hz.2

/-- The base image `π(divPt)` is `ψ ∘ Tm`, jointly continuous on `S × [0,b]^{da}`. -/
theorem gv_divPt_eq (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) {v : Fin ((Ξ.X Y).da p) → ℝ}
    (hv : v ∈ closedBox _ (Y.T.a p.1)) :
    Ξ.R.gv (Ξ.divPt Y p s v) = Y.T.ψ p.1 ((Ξ.X Y).Tm p s v) := by
  have ht := Ξ.facePt_mem_target Y p s hv
  change Ξ.R.gv (Ξ.divPt Y p s v) = Y.T.ψ p.1 (Ξ.facePt Y p s v)
  rw [Y.ψ_eq_gv_chartInv p.1 ht, Y.chartInv_eq p.1 ht]
  rfl

theorem continuousOn_ψ_Tm :
    ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
      Y.T.ψ p.1 ((Ξ.X Y).Tm p z.1 z.2)) (univ ×ˢ closedBox _ (Y.T.a p.1)) :=
  (Y.T.ψ_analytic p.1).continuousOn.comp ((Ξ.X Y).continuous_Tm p).continuousOn
    fun z hz => (Ξ.X Y).Tm_mem_V p z.1 fun j => (mem_closedBox.1 hz.2) j

/-! ### The uniform collar -/

/-- At a deep face point, the amplitude of a test vanishing near `D_{c+1}` vanishes on a
neighbourhood (within the box). -/
theorem eventually_amp_zero_of_deep {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) (s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
    {v : Fin ((Ξ.X Y).da p) → ℝ} (hv : v ∈ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) :
    ∀ᶠ z in 𝓝 (s, v), z.2 ∈ closedBox _ (Y.T.a p.1) →
      (Ξ.ampObs Y p hG).amp z.1 z.2 = 0 := by
  classical
  obtain ⟨hvbox, hcard⟩ := hv
  set Jv := (univ : Finset (Fin ((Ξ.X Y).da p))).filter fun i => v i = 0 with hJv
  have hJvne : Jv.Nonempty := Finset.card_pos.1 (by omega)
  have hJ : ∀ i, v i = 0 ↔ i ∈ Jv := fun i => by simp [hJv]
  have hdepth : c + 1 ≤ depth Ξ.R Ξ.hK0 (Ξ.divPt Y p s v) := by
    rw [Ξ.depth_divPt_eq Y p s hvbox hJ]
    exact hcard
  have hK0 : Ξ.K (Ξ.R.gv (Ξ.divPt Y p s v)) = 0 :=
    Ξ.phase_divPt_eq_zero Y p s hvbox hJvne fun i hi => (hJ i).2 hi
  by_cases hdeep : Ξ.divPt Y p s v ∈ Ξ.deepZeroFibre c
  · obtain ⟨N, hN, hDN, hGN⟩ := eventually_nhdsSet_iff_exists.1 hG0
    have hcont := (Ξ.continuousOn_divPt_pair Y p) (s, v) ⟨mem_univ _, hvbox⟩
    have hev := eventually_nhdsWithin_iff.1 (hcont (hN.mem_nhds (hDN hdeep)))
    filter_upwards [hev] with z hz hzbox
    rw [Ξ.amp_withF_eq Y p hG z.1 hzbox, hGN _ (hz ⟨mem_univ _, hzbox⟩), mul_zero]
  · have hnot : Ξ.R.gv (Ξ.divPt Y p s v) ∉ tsupport Ξ.prior := fun hmem =>
      hdeep ⟨⟨hmem, hK0⟩, hdepth⟩
    have hcont := (Ξ.continuousOn_ψ_Tm Y p) (s, v) ⟨mem_univ _, hvbox⟩
    have hnot' : Y.T.ψ p.1 ((Ξ.X Y).Tm p s v) ∉ tsupport Ξ.prior := by
      rwa [Ξ.gv_divPt_eq Y p s hvbox] at hnot
    have hev := eventually_nhdsWithin_iff.1
      (hcont ((isClosed_tsupport Ξ.prior).isOpen_compl.mem_nhds hnot'))
    filter_upwards [hev] with z hz hzbox
    have h0 : Ξ.prior (Y.T.ψ p.1 ((Ξ.X Y).Tm p z.1 z.2)) = 0 :=
      image_eq_zero_of_notMem_tsupport (hz ⟨mem_univ _, hzbox⟩)
    rw [Ξ.amp_withF_eq Y p hG z.1 hzbox]
    unfold BridgeInputs.ρloc
    change Y.T.ω p.1 _ * |Y.T.jacUnit p.1 _| * Ξ.prior (Y.T.ψ p.1 _) * _ = 0
    rw [h0, mul_zero, zero_mul]

/-- ★★ **The uniform collar**: for a test `G` vanishing near `D_{c+1}`, there is `ε > 0` such
that the amplitude of `withF G` vanishes at every box point within `ε` of the deep set, uniformly
in the base point. -/
theorem exists_collar {c : ℕ} {G : Ξ.R.U → ℝ} (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Base ((Ξ.X Y).act p.1) (Y.T.a p.1),
      ∀ v ∈ closedBox ((Ξ.X Y).da p) (Y.T.a p.1),
      ∀ v' ∈ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c, dist v v' < ε →
        (Ξ.ampObs Y p hG).amp s v = 0 := by
  set O : Set (Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ)) :=
    {z | ∀ᶠ z' in 𝓝 z, z'.2 ∈ closedBox _ (Y.T.a p.1) →
      (Ξ.ampObs Y p hG).amp z'.1 z'.2 = 0} with hO
  have hOopen : IsOpen O :=
    isOpen_setOfPred_eventually_nhds
      (p := fun z' : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        z'.2 ∈ closedBox _ (Y.T.a p.1) → (Ξ.ampObs Y p hG).amp z'.1 z'.2 = 0)
  have hKO : (univ ×ˢ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) ⊆ O := fun z hz =>
    Ξ.eventually_amp_zero_of_deep Y p hG hG0 z.1 hz.2
  have hK : IsCompact (univ ×ˢ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) :=
    (isCompact_univ (X := Base ((Ξ.X Y).act p.1) (Y.T.a p.1))).prod
      (isCompact_deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c)
  obtain ⟨ε, hε, hsub⟩ := hK.exists_thickening_subset_open hOopen hKO
  refine ⟨ε, hε, fun s v hv v' hv' hdist => ?_⟩
  have hmem : (s, v) ∈ Metric.thickening ε (univ ×ˢ deepSet ((Ξ.X Y).da p) (Y.T.a p.1) c) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(s, v'), ⟨mem_univ _, hv'⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    exact max_lt hε hdist
  have := hsub hmem
  exact this.self_of_nhds hv

/-! ### Joint integrability of the face integrand -/

theorem continuous_mono' {ι : Type*} [Fintype ι] (a : ι → ℕ) : Continuous (mono a) := by
  unfold mono
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

/-- The residue weight is bounded on `[ε, b]^ι`. -/
theorem exists_bound_residueWeight {ι : Type*} [Fintype ι] (h k : ι → ℕ) (μ : ℝ) {ε : ℝ}
    (b : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ι → ℝ, (∀ i, ε ≤ w i ∧ w i ≤ b) → |residueWeight h k μ w| ≤ C := by
  have hK : IsCompact (Set.pi Set.univ fun _ : ι => Icc ε b) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : ContinuousOn (residueWeight h k μ) (Set.pi Set.univ fun _ : ι => Icc ε b) := by
    unfold residueWeight
    refine (continuous_mono' h).continuousOn.mul
      ((continuous_mono' _).continuousOn.rpow_const fun w hw => Or.inl ?_)
    exact (mono_pos _ fun i => hε.trans_le (hw i (Set.mem_univ i)).1).ne'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  have := hC w (Set.mem_univ_pi.2 fun i => hw i)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem volume_box_lt_top {ι : Type*} [Fintype ι] (b : ℝ) : volume (box ι b) < ⊤ := by
  refine (measure_mono fun w hw => Set.mem_univ_pi.2 fun i =>
    Set.Ioc_subset_Icc_self (Set.mem_univ_pi.1 hw i)).trans_lt ?_
  exact (isCompact_univ_pi fun _ : ι => isCompact_Icc).measure_lt_top

/-- ★★ **Joint integrability of the face integrand**: for a test `G` vanishing near `D_{c+1}` and
a face `J` of size `c`, `(s, w) ↦ amp(s, glue J 0 w) · residueWeight(w)` is integrable against
`base ⊗ volume|box`. -/
theorem integrable_faceIntegrand {c : ℕ} {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G)
    (hG0 : ∀ᶠ P in 𝓝ˢ (Ξ.deepZeroFibre c), G P = 0) (J : Finset (Fin ((Ξ.X Y).da p)))
    (hJc : J.card = c) (μ : ℝ) :
    Integrable (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ) =>
      (Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ
          z.2)
      ((Ξ.piecePresentation Y p).ν.prod
        (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1)))) := by
  obtain ⟨ε, hε, hcol⟩ := Ξ.exists_collar Y p hG hG0
  obtain ⟨M, hM0, hM⟩ := Ξ.exists_bound_amp_withF Y p hG
  obtain ⟨C, hC0, hC⟩ := exists_bound_residueWeight
    (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ (Y.T.a p.1) hε
  have hb : 0 < Y.T.a p.1 := Y.T.a_pos p.1
  have : IsFiniteMeasure (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1))) :=
    isFiniteMeasure_restrict.2 (volume_box_lt_top _).ne
  have hprod : (Ξ.piecePresentation Y p).ν.prod
      (volume.restrict (box {i // ¬ inJ J i} (Y.T.a p.1))) =
      ((Ξ.piecePresentation Y p).ν.prod volume).restrict
        (Set.univ ×ˢ box {i // ¬ inJ J i} (Y.T.a p.1)) := by
    rw [← Measure.restrict_univ (μ := (Ξ.piecePresentation Y p).ν), Measure.prod_restrict,
      Measure.restrict_univ]
  have hglue : ∀ w : {i // ¬ inJ J i} → ℝ, w ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
      glue J 0 w ∈ closedBox _ (Y.T.a p.1) := fun w hw =>
    glue_zero_mem_closedBox_of_mem_Icc hb.le fun i _ =>
      Set.Ioc_subset_Icc_self (hw i (Set.mem_univ i))
  have hbound : ∀ z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × ({i // ¬ inJ J i} → ℝ),
      z.2 ∈ box {i // ¬ inJ J i} (Y.T.a p.1) →
      ‖(Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) *
        residueWeight (fun i : {i // ¬ inJ J i} => (Ξ.X Y).hA p i) (fun i => (Ξ.X Y).kA p i) μ
          z.2‖ ≤ M * C := by
    intro z hz
    have hvbox := hglue z.2 hz
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hsmall : ∃ i, z.2 i < ε
    · obtain ⟨i, hi⟩ := hsmall
      have hi0 : 0 < z.2 i := pos_of_mem_box hz i
      have hamp : (Ξ.ampObs Y p hG).amp z.1 (glue J 0 z.2) = 0 := by
        have hvi : glue J 0 z.2 i.1 = z.2 i := glue_apply_of_not_mem (J := J) 0 z.2 i.2
        refine hcol z.1 _ hvbox (fun j => if j = i.1 then (0 : ℝ) else glue J 0 z.2 j) ?_ ?_
        · refine mem_deepSet_of_zeros ?_ (J := insert i.1 J) ?_ ?_
          · rw [mem_closedBox]
            intro j
            by_cases hj : j = i.1
            · simp only [if_pos hj]
              exact ⟨le_rfl, hb.le⟩
            · simp only [if_neg hj]
              exact (mem_closedBox.1 hvbox) j
          · rw [Finset.card_insert_of_notMem i.2, hJc]
          · intro j hj
            rw [Finset.mem_insert] at hj
            rcases hj with hj | hj
            · simp only [if_pos hj]
            · have hne : j ≠ i.1 := fun h => i.2 (h ▸ hj)
              simp only [if_neg hne]
              rw [glue_apply_of_mem (J := J) 0 z.2 (i := j) hj]
              rfl
        · refine lt_of_le_of_lt ((dist_pi_le_iff (abs_nonneg (z.2 i))).2 fun j => ?_) ?_
          · rw [Real.dist_eq]
            split_ifs with h
            · rw [sub_zero, h]
              exact le_of_eq (congrArg abs hvi)
            · exact (le_of_eq (show |glue J 0 z.2 j - glue J 0 z.2 j| = 0 by
                rw [sub_self, abs_zero])).trans (abs_nonneg _)
          · rwa [abs_of_pos hi0]
      rw [hamp, abs_zero, zero_mul]
      exact mul_nonneg hM0 hC0
    · have hall : ∀ i, ε ≤ z.2 i := fun i => not_lt.1 (not_exists.1 hsmall i)
      exact mul_le_mul (hM z.1 _ hvbox)
        (hC z.2 fun i => ⟨hall i, (hz i (Set.mem_univ i)).2⟩) (abs_nonneg _) hM0
  refine Integrable.mono' (integrable_const (M * C)) ?_ ?_
  · rw [hprod]
    refine ContinuousOn.aestronglyMeasurable ?_ (MeasurableSet.univ.prod (measurableSet_box _))
    refine ContinuousOn.mul ?_ ?_
    · have hc : ContinuousOn (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
          (Fin ((Ξ.X Y).da p) → ℝ) => (Ξ.ampObs Y p hG).amp z.1 z.2)
          (Set.univ ×ˢ closedBox ((Ξ.X Y).da p) (Y.T.a p.1)) :=
        (Ξ.withF G hG).continuousOn_amp_pair Y p
      refine hc.comp
        (continuous_fst.prodMk ((glueZeroCLM J).continuous.comp continuous_snd)).continuousOn
        fun z hz => ⟨Set.mem_univ _, hglue z.2 hz.2⟩
    · refine ((continuous_mono' _).continuousOn.mul
        ((continuous_mono' _).continuousOn.rpow_const fun w hw => Or.inl ?_)).comp
        continuous_snd.continuousOn fun z hz => hz.2
      exact (mono_pos _ fun i => pos_of_mem_box hw i).ne'
  · rw [hprod]
    exact (ae_restrict_mem (MeasurableSet.univ.prod (measurableSet_box _))).mono
      fun z hz => hbound z hz.2

end ResolvedData

end SmoothEngine

end Grammar
