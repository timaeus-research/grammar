/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SheetPieces
import Grammar.NormalReflectionTransport

/-!
# The resolved certificate of a domain-sector atlas on its sheet geometry (unit H, part 3)

The transported piece data of CCCLXXV are assembled: the piece data are summed into one
localisation datum on the sheet space (`datum`, phase `K ∘ π`, observable `obs ∘ π`), whose
measure pushes forward along `π` to the prior measure on the domain `W` (★ `datum_map_π`, from the
reflection push-forward of CCCLXXIV, the orthant decomposition of the sectors and the domain
transport of the atlas); the cores of all pieces are collected (`cores`, CCCLXXV's `sigma`), with
their normal-moment presentations transported (the fibre balls stay inside the chart box by the
per-chart collar level) and their frames the chart frames reflected onto the sheet normal spaces
(`frameS`), the tubular identity holding on the sheet (`Φ_eq`). The result is
★★★ `cert : ResolvedCertificate (Sheet.geometry A) (Sheet.normalData A) W K prior obs`, with its
coefficient certificate `coeffCert`, and the stopping theorem
★★★ `hasCoordFreeExpansion`: the domain integral `∫_W obs · prior · e^{−n K}` has the
coordinate-free expansion on the sheet strata with produced certificates, for every domain-sector
atlas with the stated (symmetric box, tangential unit, packet) hypotheses; charts with empty
active set (the phase is a unit there) contribute tails. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SheetAssembly

open Monomialize.VolumeScaling NormalisedBox WaterFilling CoordModel ChartCollar

variable {d : ℕ} (X : SheetInputs d)

namespace SheetInputs

/-! ### The fibre balls stay inside the symmetric box -/

/-- The chart core parametrisation is the frame translate. -/
theorem chart_Φ_eq (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1)))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ) :
    ((X.pieceCertP p hA).cores.chart I).Φ (s, u) = fun j => s.1.1 j +
      ((frameI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a (X.δ p.1)
        (X.δ_pos p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha (coreIdx (X.act p.1) I) s u :
          normalSpace d (amb (X.act p.1) (coreIdx (X.act p.1) I))) : Amb d).ofLp j := by
  change NormalisedBox.Φ (amb (X.act p.1) (coreIdx (X.act p.1) I)) (σI (X.act p.1) _)
    (eI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) _)
    (lamT (X.A.k p.1) (X.uP p) (amb (X.act p.1) (coreIdx (X.act p.1) I)) (X.δ p.1)) (s, u) = _
  rw [Φ_eq_frame (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a (X.δ p.1)
    (X.δ_pos p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha]
  rfl

/-- On the fibre balls the chart core parametrisation stays in the symmetric box. -/
theorem chart_Φ_mem_symBox (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1)))
    (v : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
    (hu : u ∈ Metric.eball (0 : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
      (((X.pieceCertP p hA).T I).R v)) :
    ((X.pieceCertP p hA).cores.chart I).Φ (v, u) ∈ piBox d (Icc (-X.a) X.a) := by
  change u ∈ Metric.eball (0 : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
    (ENNReal.ofReal (2 * side (X.A.k p.1) (amb (X.act p.1) (coreIdx (X.act p.1) I)) (X.δ p.1)))
    at hu
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hu
  have hn : ‖u‖ < 2 * side (X.A.k p.1) (amb (X.act p.1) (coreIdx (X.act p.1) I)) (X.δ p.1) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 hu
  change NormalisedBox.Φ (amb (X.act p.1) (coreIdx (X.act p.1) I)) (σI (X.act p.1) _)
    (eI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1) _)
    (lamT (X.A.k p.1) (X.uP p) (amb (X.act p.1) (coreIdx (X.act p.1) I)) (X.δ p.1)) (v, u) ∈ _
  rw [Φ_eq_originalNormalMapC (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a
    (X.δ p.1) (coreIdx (X.act p.1) I) v u]
  have hz := norm_widthsC_mul_lt (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1)
    (X.uP p) X.a (X.δ p.1) (X.δ_pos p.1) (X.c p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha
    (coreIdx (X.act p.1) I) X.ha (X.δ_ball' p.1 (coreIdx (X.act p.1) I)) v hn
  intro j _
  simp only [originalNormalMap]
  split_ifs with hj
  · rw [stratum_coord_zero (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) v.1 hj, zero_add]
    have := (pi_norm_lt_iff X.ha).1 hz ((σI (X.act p.1) (coreIdx (X.act p.1) I)).symm ⟨j, hj⟩)
    rw [Real.norm_eq_abs, abs_lt] at this
    exact ⟨this.1.le, this.2.le⟩
  · exact X.symBox_subset (X.base_mem_box p (coreIdx (X.act p.1) I) v) j (mem_univ _)

/-- On the fibre balls the transported observable is the piece's observable. -/
theorem obs_compat_ball (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1)))
    (v : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
    (hu : u ∈ Metric.eball (0 : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
      (((X.pieceCertP p hA).T I).R v)) :
    (X.obs ∘ Sheet.π X.SA) (X.Ψ p (((X.pieceCertP p hA).cores.chart I).Φ (v, u))) =
      (X.pieceCertP p hA).L.obs (((X.pieceCertP p hA).cores.chart I).Φ (v, u)) :=
  X.obs_compat p (X.chart_Φ_mem_symBox p hA I v u hu)

/-- The transported and reindexed normal-moment presentation of a piece core. -/
noncomputable def pieceT (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1))) :
    CoreNormalMomentPresentation ((X.pieceCores' p hA).chart I) :=
  (((X.pieceCertP p hA).T I).mapAmbient_ae (X.Ψ p) (X.measurable_Ψ p) (X.pieceDatum p)
    (X.chart_hp p hA I) (X.chart_ho p hA I) (X.obs_compat_ball p hA I)).reindex
    (X.baseHomeo p (coreIdx (X.act p.1) I))

/-! ### The frames on the sheet -/

/-- The frame at a sheet base point: the chart frame at the corresponding chart base point,
reflected by `R_σ` on the normal space. -/
noncomputable def frameS (p : X.PIdx) (I : Idx (X.act p.1)) (s : ↥(X.baseSetS p I)) :
    (Fin (nI (X.act p.1) I + 1) → ℝ) ≃L[ℝ] normalSpace d (Sheet.amb X.SA (X.J p I)) :=
  ((frameI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a (X.δ p.1)
    (X.δ_pos p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha I
    ((X.baseHomeo p I).symm s)).trans (reflNormal p.2.1 (amb (X.act p.1) I))).trans
    (LinearEquiv.ofEq _ _ (by rw [X.amb_J])).toContinuousLinearEquiv

theorem frameS_ofLp (p : X.PIdx) (I : Idx (X.act p.1)) (s : ↥(X.baseSetS p I))
    (u : Fin (nI (X.act p.1) I + 1) → ℝ) (j : Fin d) :
    ((X.frameS p I s u : normalSpace d (Sheet.amb X.SA (X.J p I))) : Amb d).ofLp j =
      WaterFilling.sgn p.2.1 j *
        ((frameI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.hk0 p.1) (X.uP p) X.a (X.δ p.1)
          (X.δ_pos p.1) (X.hc p.1) (unitR_lb (X.hu_lb p.1) p.2.1) X.ha I
          ((X.baseHomeo p I).symm s) u : normalSpace d (amb (X.act p.1) I)) : Amb d).ofLp j := by
  unfold frameS
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_ofEq_apply, reflNormal_ofLp]

/-- The sheet tubular germ at an included point is the inclusion of the translate. -/
theorem Φ_incl (i : X.A.ι) {y : Fin d → ℝ} (hy : y ∈ X.A.dom i)
    {J : Finset (Sheet.geometry X.SA).Component} (s : (Sheet.geometry X.SA).Stratum J)
    (hs : (s : Sheet.Space X.SA) = Sheet.incl X.SA i y)
    (ξ : normalSpace d (Sheet.amb X.SA J)) :
    (Sheet.normalData X.SA).Φ J s ξ = Sheet.incl X.SA i fun j => y j + (ξ : Amb d).ofLp j := by
  change (fun q : Sheet.Space X.SA => (⟨q.1, ⟨Sheet.clamp X.SA q.1
    (fun j => (q.2 : Fin d → ℝ) j + (ξ : CoordModel.Amb d) j), Sheet.clamp_mem X.SA _ _⟩⟩ :
      Sheet.Space X.SA)) (s : Sheet.Space X.SA) = _
  rw [hs]
  simp only [Sheet.incl, Sheet.clamp_of_mem X.SA i hy]

/-- ★ **The tubular identity on the sheet**: the transported chart core map is the sheet tubular
germ along the reflected frame at the transported base point. -/
theorem Φ_eq (p : X.PIdx) (hA : (X.act p.1).Nonempty) (I : Fin (numCores (X.act p.1)))
    (s : ↥(X.baseSetS p (coreIdx (X.act p.1) I)))
    (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ) :
    ((X.pieceCores' p hA).chart I).Φ (s, u) =
      (Sheet.normalData X.SA).Φ (X.J p (coreIdx (X.act p.1) I)) s.1
        (X.frameS p (coreIdx (X.act p.1) I) s u) := by
  have hs : (s.1 : Sheet.Space X.SA) = Sheet.incl X.SA p.1
      (refl p.2.1 ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s).1.1) :=
    congrArg Subtype.val (X.baseHomeo_symm_spec p (coreIdx (X.act p.1) I) s).symm
  rw [X.Φ_incl p.1 (X.mem_dom_of_mem_box p.1 p.2.1
    (X.base_mem_box p (coreIdx (X.act p.1) I) ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s)))
    s.1 hs, X.pieceCores'_chart_Φ,
    X.chart_Φ_eq p hA I ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s) u]
  change Sheet.incl X.SA p.1 (refl p.2.1 _) = _
  congr 1
  funext j
  rw [refl_apply, refl_apply, X.frameS_ofLp, mul_add]

/-! ### The assembled datum, cores and transport -/

/-- **The assembled localisation datum on the sheet space**: the sum of the transported piece
data over ALL pieces (active or not), phase `K ∘ π`, observable `obs ∘ π`, level `1`. -/
noncomputable def datum : LocalisationData (Sheet.Space X.SA) :=
  LocalisationData.finsum (fun p : X.PIdx => X.pieceDatum p) (X.K ∘ Sheet.π X.SA)
    (X.obs ∘ Sheet.π X.SA) X.measurable_Kπ (fun _ => rfl) (fun _ => rfl) 1 one_pos

theorem datum_μ :
    X.datum.μ = ∑ p : X.PIdx, (pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1).map (X.Ψ p) := rfl

/-- The active pieces: those whose chart has a nonempty active set. -/
abbrev APIdx : Type := {p : X.PIdx // (X.act p.1).Nonempty}

/-- The number of cores. -/
noncomputable abbrev N : ℕ := Fintype.card (Σ p : X.APIdx, Fin (numCores (X.act p.1.1)))

/-- The enumeration of the cores. -/
noncomputable def coreEnum : Fin X.N ≃ Σ p : X.APIdx, Fin (numCores (X.act p.1.1)) :=
  (Fintype.equivFin _).symm

/-- The piece of a core. -/
noncomputable abbrev pOf (k : Fin X.N) : X.PIdx := (X.coreEnum k).1.1

theorem act_pOf_nonempty (k : Fin X.N) : (X.act (X.pOf k).1).Nonempty := (X.coreEnum k).1.2

/-- The chart stratum of a core. -/
noncomputable abbrev IOf (k : Fin X.N) : Idx (X.act (X.pOf k).1) :=
  coreIdx (X.act (X.pOf k).1) (X.coreEnum k).2

/-- The datum of the active pieces. -/
noncomputable def activeDatum : LocalisationData (Sheet.Space X.SA) :=
  LocalisationData.finsum (fun p : X.APIdx => X.pieceDatum p.1) (X.K ∘ Sheet.π X.SA)
    (X.obs ∘ Sheet.π X.SA) X.measurable_Kπ (fun _ => rfl) (fun _ => rfl) 1 one_pos

/-- **The cores of the active pieces**, collected. -/
noncomputable def activeCores :
    AnalyticCoreDecomposition X.activeDatum X.N
      (fun k => ↥(X.baseSetS (X.pOf k) (X.IOf k))) (fun k => nI (X.act (X.pOf k).1) (X.IOf k)) 1 :=
  AnalyticCoreDecomposition.sigma (fun p : X.APIdx => X.pieceCores' p.1 p.2) X.coreEnum

/-- Adding a tail with a phase gap to a core decomposition (the datum's measure grows by the
tail, the phase and observable are unchanged). -/
noncomputable def _root_.Grammar.AnalyticCoreDecomposition.addTail {U : Type*}
    [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
    [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
    (A : AnalyticCoreDecomposition D M K n β) (D' : LocalisationData U) (ν : Measure U)
    (hμ : D'.μ = D.μ + ν) (hp : D'.phase = D.phase) (ho : D'.obs = D.obs) (δ' : ℝ)
    (hδ' : 0 < δ') (hgap : ∀ᵐ z ∂ν, δ' ≤ D.phase z) : AnalyticCoreDecomposition D' M K n β where
  core := A.core
  tail := A.tail + ν
  measure_eq := by rw [hμ, A.measure_eq, add_assoc]
  δ₀ := min A.δ₀ δ'
  δ₀_pos := lt_min A.δ₀_pos hδ'
  gap := by
    rw [hp, ae_add_measure_iff]
    exact ⟨A.gap.mono fun z hz => (min_le_left _ _).trans hz,
      hgap.mono fun z hz => (min_le_right _ _).trans hz⟩
  chart := fun I => (A.chart I).congrData D' hp ho

/-- The measure of the inactive pieces (charts with empty active set). -/
noncomputable def inactiveMeasure : Measure (Sheet.Space X.SA) :=
  ∑ p : {p : X.PIdx // ¬ (X.act p.1).Nonempty}, (X.pieceDatum p.1).μ

theorem datum_μ_split : X.datum.μ = X.activeDatum.μ + X.inactiveMeasure :=
  (Fintype.sum_subtype_add_sum_subtype (fun p : X.PIdx => (X.act p.1).Nonempty)
    fun p => (X.pieceDatum p).μ).symm

/-- The common lower bound of the units. -/
noncomputable def cmin : ℝ := Finset.univ.inf' (Finset.univ_nonempty_iff.2 X.ι_nonempty) X.c

theorem cmin_pos : 0 < X.cmin := (Finset.lt_inf'_iff _).2 fun i _ => X.hc i

theorem cmin_le (i : X.A.ι) : X.cmin ≤ X.c i := Finset.inf'_le _ (Finset.mem_univ i)

/-- **The inactive pieces are tails**: on a chart with empty active set the phase is the unit,
bounded below by `c_i`. -/
theorem inactive_gap : ∀ᵐ z ∂X.inactiveMeasure, X.cmin ≤ (X.K ∘ Sheet.π X.SA) z := by
  unfold inactiveMeasure
  rw [← Measure.sum_fintype, Measure.ae_sum_iff]
  intro p
  rw [pieceDatum_μ, ae_map_iff (X.measurable_Ψ p.1).aemeasurable
    (measurableSet_le measurable_const X.measurable_Kπ)]
  refine (X.ae_mem_box' p.1).mono fun z hz => ?_
  have hd := X.mem_dom_of_mem_box p.1.1 p.1.2.1 hz
  change X.cmin ≤ X.K (Sheet.π X.SA (X.Ψ p.1 z))
  rw [X.π_Ψ p.1 (X.symBox_subset hz), X.A.phase_eq p.1.1 _ (X.A.dom_subset_V p.1.1 hd)]
  have hk : ∀ j, X.A.k p.1.1 j = 0 := fun j => X.hk0 p.1.1 j fun hj => p.2 ⟨j, hj⟩
  have hprod : ∏ j, (refl p.1.2.1 z) j ^ (2 * X.A.k p.1.1 j) = 1 :=
    Finset.prod_eq_one fun j _ => by rw [hk j, mul_zero, pow_zero]
  rw [hprod, mul_one]
  exact (X.cmin_le p.1.1).trans (X.hu_lb p.1.1 _ (X.refl_mem_symBox _ (X.symBox_subset hz)))

/-- **The assembled core decomposition**: the cores of the active pieces, the inactive pieces
added to the tail. -/
noncomputable def cores :
    AnalyticCoreDecomposition X.datum X.N
      (fun k => ↥(X.baseSetS (X.pOf k) (X.IOf k))) (fun k => nI (X.act (X.pOf k).1) (X.IOf k)) 1 :=
  X.activeCores.addTail X.datum X.inactiveMeasure X.datum_μ_split rfl rfl X.cmin X.cmin_pos
    X.inactive_gap

theorem activeCores_chart (k : Fin X.N) :
    X.activeCores.chart k = ((X.pieceCores' (X.pOf k) (X.act_pOf_nonempty k)).chart
      (X.coreEnum k).2).congrData X.activeDatum rfl rfl := rfl

theorem cores_chart (k : Fin X.N) :
    X.cores.chart k = (X.activeCores.chart k).congrData X.datum rfl rfl := rfl

/-- The normal-moment presentations of the assembled cores. -/
noncomputable def T (k : Fin X.N) : CoreNormalMomentPresentation (X.cores.chart k) :=
  ((X.pieceT (X.pOf k) (X.act_pOf_nonempty k) (X.coreEnum k).2).congrData X.activeDatum rfl
    rfl).congrData X.datum rfl rfl

/-- The transported piece measure pushed to the domain is the weighted analytic prior on the
orthant box, pushed by the chart. -/
theorem map_Ψ_eq (p : X.PIdx) :
    ((pieceMeasure (X.A.h p.1) X.a (X.ϕw p.1) p.2.1).map (X.Ψ p)).map (Sheet.π X.SA) =
      ((volume.restrict (orthantBox p.2.1 X.a : Set (Fin d → ℝ))).withDensity fun w =>
        ENNReal.ofReal (wgt (X.A.h p.1) w * X.ϕw p.1 w)).map (X.A.φ p.1) := by
  rw [Measure.map_map (Sheet.continuous_π X.SA).measurable (X.measurable_Ψ p),
    ← map_refl_pieceMeasure, Measure.map_map (X.φ_m p.1) (measurable_refl _)]
  refine Measure.map_congr ?_
  exact (X.ae_mem_box' p).mono fun z hz => X.π_Ψ p (X.symBox_subset hz)

/-- The orthant pieces of a chart sum to the sector measure of the prior. -/
theorem sum_withDensity_orthant (i : X.A.ι) :
    ∑ σ : ↥(X.A.signs i), (volume.restrict (orthantBox σ.1 X.a : Set (Fin d → ℝ))).withDensity
      (fun w => ENNReal.ofReal (wgt (X.A.h i) w * X.ϕw i w)) =
      X.A.sectorMeasure (fun w => ENNReal.ofReal (X.prior w)) i := by
  rw [← X.withDensity_sector_eq i, X.restrict_sector_eq i,
    ← Finset.sum_coe_sort (X.A.signs i) fun σ =>
      volume.restrict (orthantBox σ X.a : Set (Fin d → ℝ)),
    ← Measure.sum_fintype fun σ : ↥(X.A.signs i) =>
      volume.restrict (orthantBox σ.1 X.a : Set (Fin d → ℝ)),
    withDensity_sum, Measure.sum_fintype]

/-- ★ **Transport**: the assembled measure pushes forward along `π` to the prior measure on the
domain `W`. -/
theorem datum_map_π :
    X.datum.μ.map (Sheet.π X.SA) =
      (volume.restrict X.A.W).withDensity fun w => ENNReal.ofReal (X.prior w) := by
  rw [datum_μ, map_finset_sum _ _ (Sheet.continuous_π X.SA).measurable]
  simp_rw [X.map_Ψ_eq]
  rw [Fintype.sum_sigma, ← X.A.weightedDomainTransport (a := fun w => ENNReal.ofReal (X.prior w))
    (ENNReal.measurable_ofReal.comp X.prior_m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← X.sum_withDensity_orthant i, map_finset_sum _ _ (X.φ_m i)]

/-! ### The certificate -/

/-- ★★★ **The resolved certificate of a domain-sector atlas on its sheet geometry**: the piece
certificates of all selected orthants of all charts, transported along the piece charts, based
on the sheet strata and summed; prior `prior`, observable `obs`, phase `K`, domain `W`. -/
noncomputable def cert :
    ResolvedCertificate (Sheet.geometry X.SA) (Sheet.normalData X.SA) X.A.W X.K X.prior X.obs where
  L := X.datum
  obs_eq := rfl
  phase_eq := rfl
  transport := X.datum_map_π
  M := X.N
  n := fun k => nI (X.act (X.pOf k).1) (X.IOf k)
  strat := fun k => X.J (X.pOf k) (X.IOf k)
  base := fun k => X.baseSetS (X.pOf k) (X.IOf k)
  isCompact_base := fun _ => X.isCompact_baseSetS _ _
  β := 1
  β_pos := one_pos
  cores := X.cores
  T := X.T
  frame := fun k s => X.frameS (X.pOf k) (X.IOf k) s
  Φ_eq := fun k s u => X.Φ_eq (X.pOf k) (X.act_pOf_nonempty k) (X.coreEnum k).2 s u

theorem cert_cores_b (k : Fin X.N) :
    X.cert.cores.b k = (X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).cores.b (X.coreEnum k).2 :=
  rfl

/-- ★★ **The coefficient certificate on the sheet**: the piece factorisation families and
observable jets, transported. -/
noncomputable def coeffCert : X.cert.CoefficientCertificate where
  cc := fun k s => (X.pieceCoeffP (X.pOf k) (X.act_pOf_nonempty k)).cc (X.coreEnum k).2
    ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
  cc_abs := fun k s => (X.pieceCoeffP (X.pOf k) (X.act_pOf_nonempty k)).cc_abs (X.coreEnum k).2 _
  jet_abs := fun k s => by
    change (jetFamily (nI (X.act (X.pOf k).1) (X.IOf k))
      ((X.cores.chart k).obsFibre s)).AbsSummableAt
        ((X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).cores.b (X.coreEnum k).2)
    rw [jetFamily_eq_monoFamily ((X.T k).analytic s)]
    have h := (X.pieceCoeffP (X.pOf k) (X.act_pOf_nonempty k)).jet_abs (X.coreEnum k).2
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
    rw [jetFamily_eq_monoFamily (((X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).T
      (X.coreEnum k).2).analytic ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s))] at h
    exact h
  datum_eq := fun k s => by
    change toEta ((X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).cores.b (X.coreEnum k).2)
      ((X.cores.chart k).x s) = CoeffFamily.conv _
        (jetFamily (nI (X.act (X.pOf k).1) (X.IOf k))
          ((X.cores.chart k).obsFibre s))
    rw [jetFamily_eq_monoFamily ((X.T k).analytic s)]
    have h := (X.pieceCoeffP (X.pOf k) (X.act_pOf_nonempty k)).datum_eq (X.coreEnum k).2
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
    rw [jetFamily_eq_monoFamily (((X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).T
      (X.coreEnum k).2).analytic ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s))] at h
    have hx : (X.cores.chart k).x s =
        ((X.pieceCertP (X.pOf k) (X.act_pOf_nonempty k)).cores.chart (X.coreEnum k).2).x
          ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s) :=
      CorePresentation.reindex_x _ _ _
    rw [hx]
    exact h

/-! ### The coordinate-free expansion -/

/-- ★★★ **The coordinate-free expansion of a domain integral through a domain-sector atlas**: for
a domain-sector atlas with symmetric chart boxes, positive tangential phase units and holomorphic
signed-box packets of the analytic prior factor and the observable, the
domain integral `∫_W obs · prior · e^{−n K}` has the coordinate-free expansion on the sheet strata
with produced certificates. -/
theorem hasCoordFreeExpansion :
    (Sheet.normalData X.SA).HasCoordFreeExpansion X.cert.stratumMeasure X.coeffCert.field
      (spectrumLe (commonQ X.cert.cores.k) (commonD X.cert.n)) X.A.W X.K X.prior X.obs :=
  X.coeffCert.hasCoordFreeExpansion_le X.K_m X.prior_m X.prior_nonneg X.obs_m

end SheetInputs

/-- ★★★ **Existence form**: a WEIGHTED domain atlas (chart weights constant along the active
coordinates near the divisor, exact weighted transport — no disjointness of the chart images) with
the sheet-assembly inputs produces a resolved certificate and a coefficient certificate on its
sheet geometry for which the coordinate-free expansion holds. -/
theorem hasCoordFreeExpansion_of_weightedDomainAtlas (X : SheetInputs d) :
    ∃ (C : ResolvedCertificate (Sheet.geometry X.SA) (Sheet.normalData X.SA) X.A.W X.K X.prior
        X.obs) (Cc : C.CoefficientCertificate),
      (Sheet.normalData X.SA).HasCoordFreeExpansion C.stratumMeasure Cc.field
        (spectrumLe (commonQ C.cores.k) (commonD C.n)) X.A.W X.K X.prior X.obs :=
  ⟨X.cert, X.coeffCert, X.hasCoordFreeExpansion⟩

/-! ### Integrability from continuity on a compact set -/

/-- A continuous observable is integrable for the measure with a continuous nonnegative density on
a subset of a compact set. -/
theorem integrable_of_continuous_of_subset_compact {d : ℕ} {p F : (Fin d → ℝ) → ℝ}
    (hp : Continuous p) (hF : Continuous F) {W Kc : Set (Fin d → ℝ)} (hKc : IsCompact Kc)
    (hW : W ⊆ Kc) (hWm : MeasurableSet W) :
    Integrable F ((volume.restrict W).withDensity fun w => ENNReal.ofReal (p w)) := by
  obtain ⟨Cp, hCp⟩ := hKc.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn hF.continuousOn
  have : IsFiniteMeasure ((volume.restrict W).withDensity fun w => ENNReal.ofReal (p w)) := by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ w, ENNReal.ofReal (p w) ∂(volume.restrict W)
        ≤ ∫⁻ _, ENNReal.ofReal Cp ∂(volume.restrict W) := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hWm]
          refine Eventually.of_forall fun w hw => ENNReal.ofReal_le_ofReal ?_
          have := hCp w (hW hw)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal Cp * volume W := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((measure_mono hW).trans_lt hKc.measure_lt_top)
  refine (integrable_const CF).mono' hF.measurable.aestronglyMeasurable ?_
  refine Filter.le_def.1 (withDensity_absolutelyContinuous _ _).ae_le _ ?_
  change ∀ᵐ w ∂volume.restrict W, ‖F w‖ ≤ CF
  rw [ae_restrict_iff' hWm]
  exact Eventually.of_forall fun w hw => hCF w (hW hw)

/-! ### Packet congruence -/

/-- Transport of a signed packet along equalities of the prior and observable. -/
def _root_.Grammar.WaterFilling.HolomorphicSignedBoxExtension.congr {d : ℕ} {a : ℝ}
    {ϕ φ ϕ' φ' : (Fin d → ℝ) → ℝ} (A : HolomorphicSignedBoxExtension a ϕ φ) (hϕ : ϕ' = ϕ)
    (hφ : φ' = φ) : HolomorphicSignedBoxExtension a ϕ' φ' := by
  subst hϕ
  subst hφ
  exact A

end SheetAssembly

end Grammar
