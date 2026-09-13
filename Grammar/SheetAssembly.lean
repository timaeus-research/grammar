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
atlas with the stated (symmetric box, tangential unit, packet) hypotheses. Zero `sorry`/`axiom`.
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
theorem chart_Φ_eq (p : X.PIdx) (I : Fin (numCores (X.act p.1)))
    (s : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ) :
    ((X.pieceCertP p).cores.chart I).Φ (s, u) = fun j => s.1.1 j +
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
theorem chart_Φ_mem_symBox (p : X.PIdx) (I : Fin (numCores (X.act p.1)))
    (v : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
    (hu : u ∈ Metric.eball (0 : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
      (((X.pieceCertP p).T I).R v)) :
    ((X.pieceCertP p).cores.chart I).Φ (v, u) ∈ piBox d (Icc (-X.a) X.a) := by
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
theorem obs_compat_ball (p : X.PIdx) (I : Fin (numCores (X.act p.1)))
    (v : KI (X.act p.1) (X.A.k p.1) (X.A.h p.1) (X.hkA p.1) (X.uP p) X.a (X.δ p.1)
      (coreIdx (X.act p.1) I)) (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
    (hu : u ∈ Metric.eball (0 : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ)
      (((X.pieceCertP p).T I).R v)) :
    (X.obs ∘ Sheet.π X.SA) (X.Ψ p (((X.pieceCertP p).cores.chart I).Φ (v, u))) =
      (X.pieceCertP p).L.obs (((X.pieceCertP p).cores.chart I).Φ (v, u)) :=
  X.obs_compat p (X.chart_Φ_mem_symBox p I v u hu)

/-- The transported and reindexed normal-moment presentation of a piece core. -/
noncomputable def pieceT (p : X.PIdx) (I : Fin (numCores (X.act p.1))) :
    CoreNormalMomentPresentation ((X.pieceCores' p).chart I) :=
  (((X.pieceCertP p).T I).mapAmbient_ae (X.Ψ p) (X.measurable_Ψ p) (X.pieceDatum p)
    (X.chart_hp p I) (X.chart_ho p I) (X.obs_compat_ball p I)).reindex
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
theorem Φ_eq (p : X.PIdx) (I : Fin (numCores (X.act p.1)))
    (s : ↥(X.baseSetS p (coreIdx (X.act p.1) I)))
    (u : Fin (nI (X.act p.1) (coreIdx (X.act p.1) I) + 1) → ℝ) :
    ((X.pieceCores' p).chart I).Φ (s, u) =
      (Sheet.normalData X.SA).Φ (X.J p (coreIdx (X.act p.1) I)) s.1
        (X.frameS p (coreIdx (X.act p.1) I) s u) := by
  have hs : (s.1 : Sheet.Space X.SA) = Sheet.incl X.SA p.1
      (refl p.2.1 ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s).1.1) :=
    congrArg Subtype.val (X.baseHomeo_symm_spec p (coreIdx (X.act p.1) I) s).symm
  rw [X.Φ_incl p.1 (X.mem_dom_of_mem_box p.1 p.2.1
    (X.base_mem_box p (coreIdx (X.act p.1) I) ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s)))
    s.1 hs, X.pieceCores'_chart_Φ,
    X.chart_Φ_eq p I ((X.baseHomeo p (coreIdx (X.act p.1) I)).symm s) u]
  change Sheet.incl X.SA p.1 (refl p.2.1 _) = _
  congr 1
  funext j
  rw [refl_apply, refl_apply, X.frameS_ofLp, mul_add]

/-! ### The assembled datum, cores and transport -/

/-- **The assembled localisation datum on the sheet space**: the sum of the transported piece
data, phase `K ∘ π`, observable `obs ∘ π`, level `1`. -/
noncomputable def datum : LocalisationData (Sheet.Space X.SA) :=
  LocalisationData.finsum (fun p : X.PIdx => X.pieceDatum p) (X.K ∘ Sheet.π X.SA)
    (X.obs ∘ Sheet.π X.SA) X.measurable_Kπ (fun _ => rfl) (fun _ => rfl) 1 one_pos

theorem datum_μ :
    X.datum.μ = ∑ p : X.PIdx, (pieceMeasure (X.A.h p.1) X.a (X.ϕ p.1) p.2.1).map (X.Ψ p) := rfl

/-- The number of cores. -/
noncomputable abbrev N : ℕ := Fintype.card (Σ p : X.PIdx, Fin (numCores (X.act p.1)))

/-- The enumeration of the cores. -/
noncomputable def coreEnum : Fin X.N ≃ Σ p : X.PIdx, Fin (numCores (X.act p.1)) :=
  (Fintype.equivFin _).symm

/-- The piece of a core. -/
noncomputable abbrev pOf (k : Fin X.N) : X.PIdx := (X.coreEnum k).1

/-- The chart stratum of a core. -/
noncomputable abbrev IOf (k : Fin X.N) : Idx (X.act (X.pOf k).1) :=
  coreIdx (X.act (X.pOf k).1) (X.coreEnum k).2

/-- **The assembled core decomposition**: all transported cores of all pieces. -/
noncomputable def cores :
    AnalyticCoreDecomposition X.datum X.N
      (fun k => ↥(X.baseSetS (X.pOf k) (X.IOf k))) (fun k => nI (X.act (X.pOf k).1) (X.IOf k)) 1 :=
  AnalyticCoreDecomposition.sigma (fun p => X.pieceCores' p) X.coreEnum

/-- The normal-moment presentations of the assembled cores. -/
noncomputable def T (k : Fin X.N) : CoreNormalMomentPresentation (X.cores.chart k) :=
  (X.pieceT (X.pOf k) (X.coreEnum k).2).congrData X.datum rfl rfl

/-- The transported piece measure pushed to the domain is the weighted analytic prior on the
orthant box, pushed by the chart. -/
theorem map_Ψ_eq (p : X.PIdx) :
    ((pieceMeasure (X.A.h p.1) X.a (X.ϕ p.1) p.2.1).map (X.Ψ p)).map (Sheet.π X.SA) =
      ((volume.restrict (orthantBox p.2.1 X.a : Set (Fin d → ℝ))).withDensity fun w =>
        ENNReal.ofReal (wgt (X.A.h p.1) w * X.ϕ p.1 w)).map (X.A.φ p.1) := by
  rw [Measure.map_map (Sheet.continuous_π X.SA).measurable (X.measurable_Ψ p),
    ← map_refl_pieceMeasure, Measure.map_map (X.φ_m p.1) (measurable_refl _)]
  refine Measure.map_congr ?_
  have h := X.ae_mem_box p
  rw [pieceCertP_L_μ] at h
  exact h.mono fun z hz => X.π_Ψ p (X.symBox_subset hz)

/-- The orthant pieces of a chart sum to the sector measure of the prior. -/
theorem sum_withDensity_orthant (i : X.A.ι) :
    ∑ σ : ↥(X.A.signs i), (volume.restrict (orthantBox σ.1 X.a : Set (Fin d → ℝ))).withDensity
      (fun w => ENNReal.ofReal (wgt (X.A.h i) w * X.ϕ i w)) =
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
  rw [Fintype.sum_sigma, ← X.A.domainTransport (a := fun w => ENNReal.ofReal (X.prior w))
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
  Φ_eq := fun k s u => X.Φ_eq (X.pOf k) (X.coreEnum k).2 s u

theorem cert_cores_b (k : Fin X.N) :
    X.cert.cores.b k = (X.pieceCertP (X.pOf k)).cores.b (X.coreEnum k).2 := rfl

/-- ★★ **The coefficient certificate on the sheet**: the piece factorisation families and
observable jets, transported. -/
noncomputable def coeffCert : X.cert.CoefficientCertificate where
  cc := fun k s => (X.pieceCoeffP (X.pOf k)).cc (X.coreEnum k).2
    ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
  cc_abs := fun k s => (X.pieceCoeffP (X.pOf k)).cc_abs (X.coreEnum k).2 _
  jet_abs := fun k s => by
    change (jetFamily (nI (X.act (X.pOf k).1) (X.IOf k))
      ((X.cores.chart k).obsFibre s)).AbsSummableAt
        ((X.pieceCertP (X.pOf k)).cores.b (X.coreEnum k).2)
    rw [jetFamily_eq_monoFamily ((X.T k).analytic s)]
    have h := (X.pieceCoeffP (X.pOf k)).jet_abs (X.coreEnum k).2
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
    rw [jetFamily_eq_monoFamily (((X.pieceCertP (X.pOf k)).T (X.coreEnum k).2).analytic
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s))] at h
    exact h
  datum_eq := fun k s => by
    change toEta ((X.pieceCertP (X.pOf k)).cores.b (X.coreEnum k).2)
      ((X.cores.chart k).x s) = CoeffFamily.conv _
        (jetFamily (nI (X.act (X.pOf k).1) (X.IOf k))
          ((X.cores.chart k).obsFibre s))
    rw [jetFamily_eq_monoFamily ((X.T k).analytic s)]
    have h := (X.pieceCoeffP (X.pOf k)).datum_eq (X.coreEnum k).2
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s)
    rw [jetFamily_eq_monoFamily (((X.pieceCertP (X.pOf k)).T (X.coreEnum k).2).analytic
      ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s))] at h
    have hx : (X.cores.chart k).x s =
        ((X.pieceCertP (X.pOf k)).cores.chart (X.coreEnum k).2).x
          ((X.baseHomeo (X.pOf k) (X.IOf k)).symm s) :=
      CorePresentation.reindex_x _ _ _
    rw [hx]
    exact h

/-! ### The coordinate-free expansion -/

/-- ★★★ **The coordinate-free expansion of a domain integral through a domain-sector atlas**: for
a domain-sector atlas with symmetric chart boxes, nonempty active sets, positive tangential phase
units and holomorphic signed-box packets of the analytic prior factor and the observable, the
domain integral `∫_W obs · prior · e^{−n K}` has the coordinate-free expansion on the sheet strata
with produced certificates. -/
theorem hasCoordFreeExpansion :
    (Sheet.normalData X.SA).HasCoordFreeExpansion X.cert.stratumMeasure X.coeffCert.field
      (spectrumLe (commonQ X.cert.cores.k) (commonD X.cert.n)) X.A.W X.K X.prior X.obs :=
  X.coeffCert.hasCoordFreeExpansion_le X.K_m X.prior_m X.prior_nonneg X.obs_m

end SheetInputs

/-- ★★★ **Existence form**: a domain-sector atlas with the sheet-assembly inputs produces a resolved
certificate and a coefficient certificate on its sheet geometry for which the coordinate-free
expansion holds. -/
theorem hasCoordFreeExpansion_of_domainSectorAtlas (X : SheetInputs d) :
    ∃ (C : ResolvedCertificate (Sheet.geometry X.SA) (Sheet.normalData X.SA) X.A.W X.K X.prior
        X.obs) (Cc : C.CoefficientCertificate),
      (Sheet.normalData X.SA).HasCoordFreeExpansion C.stratumMeasure Cc.field
        (spectrumLe (commonQ C.cores.k) (commonD C.n)) X.A.W X.K X.prior X.obs :=
  ⟨X.cert, X.coeffCert, X.hasCoordFreeExpansion⟩

end SheetAssembly

end Grammar
