/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpCubeBase
import Grammar.CoreFinsum

/-!
# The resolved certificate of the cube integral on the genuine blow-up (B4c)

The `d · 2^d` chart certificates of the cube blow-up (CCCXLVII) are transported along the piece
charts `Ψ_β ∘ R_σ` onto the genuine blow-up space `U` (CCCLXI), their bases reindexed onto their
images on the exceptional divisor (CCCLXVI), and summed (CCCLXIV) into ONE
`ResolvedCertificate (blowUpGeometry d) (blowUpNormalData d) (cube d) K p F` (`cubeCert`), with
its coefficient certificate (`cubeCoeffCert`). The `transport` field is the measure-level chart
decomposition of CCCLXV; the `Φ_eq` field is the tubular identity of CCCLXVI. This is the first
`ResolvedCertificate` on a space with a collapsing `π` and a nontrivial normal bundle.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace BlowUpCube

open WaterFilling SingletonChart NormalisedBox CoordModel

variable {d : ℕ} (β : Fin d) (σ : CoordSign d) {p F : (Fin d → ℝ) → ℝ}
  (A : HolomorphicSignedBoxExtension 1 p F)

/-! ### The observable, made measurable -/

omit β σ in
open scoped Classical in
/-- The observable, cut off outside the cube. -/
noncomputable def FM (_A : HolomorphicSignedBoxExtension 1 p F) : (Fin d → ℝ) → ℝ :=
  (cube d).piecewise F 0

omit β σ in
open scoped Classical in
theorem measurable_FM : Measurable (FM A) :=
  A.continuousOn_obs.measurable_piecewise continuousOn_const isCompact_cube.isClosed.measurableSet

omit β σ in
open scoped Classical in
theorem FM_of_mem {x : Fin d → ℝ} (hx : x ∈ cube d) : FM A x = F x := by
  unfold FM
  exact piecewise_eq_of_mem _ _ _ hx

/-! ### The piece chart into the blow-up and the compatibilities -/

/-- The piece chart `z ↦ Ψ_β(R_σ z)` into the blow-up. -/
noncomputable def Ψσ (z : Fin d → ℝ) : BlowUpSpace d := Ψ β (refl σ z)

theorem measurable_Ψσ : Measurable (Ψσ β σ) :=
  (measurable_Ψ β).comp (continuous_refl σ).measurable

theorem π_Ψσ (z : Fin d → ℝ) : π (Ψσ β σ z) = φ β (refl σ z) := rfl

theorem phase_compat (z : Fin d → ℝ) : K (π (Ψσ β σ z)) = Kc β (unit β) z := K_φ_refl β σ z

theorem obs_compat {z : Fin d → ℝ} (hz : z ∈ cube d) :
    FM A (π (Ψσ β σ z)) = (pieceExt β A σ).obsRep z := by
  rw [π_Ψσ, FM_of_mem A (φ_mem_cube β (refl_mem_cube σ hz)), obsRep_eq_of_mem_cube β A σ hz]

theorem lamS_eq (s : PieceBase β) :
    lamS β (unit β) 1 (d - 1) s = (Real.sqrt (unit β s.1.1))⁻¹ := by
  unfold lamS e
  rw [unitT_tan β (unit β) (unit_tan β)]

theorem lamS_le_one (s : PieceBase β) : lamS β (unit β) 1 (d - 1) s ≤ 1 := by
  rw [lamS_eq]
  have h : 1 ≤ Real.sqrt (unit β s.1.1) := by
    have := Real.sqrt_le_sqrt (one_le_unit β s.1.1)
    rwa [Real.sqrt_one] at this
  exact inv_le_one_of_one_le₀ h

/-- The chart core map lands in the cube whenever `|u₀| ≤ 1`. -/
theorem Φ_mem_cube {s : PieceBase β} {u : Fin (nI (Iβ β) + 1) → ℝ} (hu : |u 0| ≤ 1) :
    NormalisedBox.Φ (Iβ β).1 (σI (Iβ β)) (e β 1 (d - 1)) (lam β (unit β)) (s, u) ∈ cube d := by
  rw [Φ_eq_update, mem_cube]
  intro j
  by_cases hj : j = β
  · rw [hj, Function.update_self, abs_mul, abs_of_pos
      (lamS_pos β (unit β) 1 (d - 1) one_pos 1 one_pos (fun y _ => one_le_unit β y) s)]
    calc lamS β (unit β) 1 (d - 1) s * |u 0| ≤ 1 * 1 :=
          mul_le_mul (lamS_le_one β s) hu (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [Function.update_of_ne hj]
    have := pieceBase_mem_box β s j (mem_univ j)
    rw [mem_Icc] at this
    exact abs_le.2 ⟨by linarith [this.1], this.2⟩

/-! ### The transported piece datum and its core decomposition -/

variable (hp0 : ∀ x ∈ piBox d (Icc (-1) 1), 0 ≤ p x)

theorem measurable_K_π : Measurable (K ∘ π (d := d)) :=
  continuous_K.measurable.comp continuous_π.measurable

theorem ae_mem_box : ∀ᵐ z ∂(pieceCert β A σ hp0).L.μ, z ∈ piBox d (Icc 0 1) :=
  mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
    (mem_ae_iff.1 (ae_restrict_mem (measurableSet_W 1))))

/-- **The transported piece datum** on the blow-up: measure `μ_{βσ}.map (Ψ_β ∘ R_σ)`, phase
`K ∘ π`, observable `F ∘ π`. -/
noncomputable def pieceDatumU : LocalisationData (BlowUpSpace d) :=
  (pieceCert β A σ hp0).L.map (Ψσ β σ) (measurable_Ψσ β σ) (K ∘ π) (FM A ∘ π) measurable_K_π
    (phase_compat β σ) ((measurable_FM A).comp continuous_π.measurable).aestronglyMeasurable
    ((ae_mem_box β σ A hp0).mono fun _ hz => obs_compat β σ A (piBox_subset_cube hz))

theorem pieceDatumU_μ : (pieceDatumU β σ A hp0).μ = (pieceMeasure β A σ).map (Ψσ β σ) := rfl

theorem pieceDatumU_phase : (pieceDatumU β σ A hp0).phase = K ∘ π := rfl

theorem pieceDatumU_obs : (pieceDatumU β σ A hp0).obs = FM A ∘ π := rfl

/-- The unique core index of a piece certificate. -/
def piece0 : Fin (pieceCert β A σ hp0).M := ⟨0, Nat.one_pos⟩

theorem pieceCert_chart_Φ (I : Fin (pieceCert β A σ hp0).M) (q) :
    ((pieceCert β A σ hp0).cores.chart I).Φ q =
      NormalisedBox.Φ (Iβ β).1 (σI (Iβ β)) (e β 1 (d - 1)) (lam β (unit β)) q := rfl

theorem pieceCert_chart_b (I : Fin (pieceCert β A σ hp0).M) :
    ((pieceCert β A σ hp0).cores.chart I).b = pieceB β A σ := rfl

theorem pieceB_le_one : pieceB β A σ ≤ 1 := by
  have := pieceB_le β A σ
  rwa [Lb_one, one_mul] at this

theorem pieceB'_le_one : pieceB' β A σ ≤ 1 := min_le_right _ _

/-- On the chart box the transported observable is the piece's observable representative. -/
theorem obs_compat_chart (I : Fin (pieceCert β A σ hp0).M) :
    ∀ᵐ q ∂chartMeasure ((pieceCert β A σ hp0).cores.chart I).ν ((pieceCert β A σ hp0).n I)
      ((pieceCert β A σ hp0).cores.chart I).b,
      (FM A ∘ π) (Ψσ β σ (((pieceCert β A σ hp0).cores.chart I).Φ q)) =
        (pieceCert β A σ hp0).L.obs (((pieceCert β A σ hp0).cores.chart I).Φ q) := by
  filter_upwards [ae_snd_mem_box ((pieceCert β A σ hp0).cores.chart I).ν _ _] with q hq
  obtain ⟨s, u⟩ := q
  have hu : |u 0| ≤ 1 := by
    have := hq 0 (mem_univ _)
    rw [mem_Ioc] at this
    rw [abs_of_pos this.1]
    exact this.2.trans (pieceB_le_one β σ A)
  exact obs_compat β σ A (Φ_mem_cube β hu)

/-- The transported single-core decomposition of a piece (base still the chart face). -/
noncomputable def pieceCoresU :
    AnalyticCoreDecomposition (pieceDatumU β σ A hp0) 1 (fun _ => PieceBase β)
      (fun _ => nI (Iβ β)) 1 :=
  (pieceCert β A σ hp0).cores.mapAmbient (Ψσ β σ) (measurable_Ψσ β σ) (pieceDatumU β σ A hp0) rfl
    (phase_compat β σ) (obs_compat_chart β σ A hp0)

/-- Reindexing the single core of a decomposition along a homeomorphism of bases. -/
noncomputable def _root_.Grammar.AnalyticCoreDecomposition.reindexOne {U : Type*}
    [MeasurableSpace U] {D : LocalisationData U} {K K' : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [TopologicalSpace K'] [MeasurableSpace K'] [BorelSpace K']
    {n : ℕ} {β : ℝ} (A : AnalyticCoreDecomposition D 1 (fun _ => K) (fun _ => n) β)
    (e : K ≃ₜ K') : AnalyticCoreDecomposition D 1 (fun _ => K') (fun _ => n) β where
  core := A.core
  tail := A.tail
  measure_eq := A.measure_eq
  δ₀ := A.δ₀
  δ₀_pos := A.δ₀_pos
  gap := A.gap
  chart := fun I => (A.chart I).reindex e

/-- The transported single-core decomposition of a piece, based on its image in the divisor. -/
noncomputable def pieceCoresU' :
    AnalyticCoreDecomposition (pieceDatumU β σ A hp0) 1 (fun _ => ↥(baseSet β σ))
      (fun _ => nI (Iβ β)) 1 :=
  (pieceCoresU β σ A hp0).reindexOne (baseHomeo β σ)

theorem pieceCoresU'_chart_Φ (q : ↥(baseSet β σ) × (Fin (nI (Iβ β) + 1) → ℝ)) :
    ((pieceCoresU' β σ A hp0).chart 0).Φ q =
      Ψσ β σ (NormalisedBox.Φ (Iβ β).1 (σI (Iβ β)) (e β 1 (d - 1)) (lam β (unit β))
        ((baseHomeo β σ).symm q.1, q.2)) := by
  rw [show (pieceCoresU' β σ A hp0).chart 0 =
    ((pieceCoresU β σ A hp0).chart 0).reindex (baseHomeo β σ) from rfl, CorePresentation.reindex_Φ]
  rfl

/-! ### The assembled datum and core decomposition on the blow-up -/

variable [NeZero d]

omit β σ in
/-- The piece index set. -/
abbrev PieceIdx (d : ℕ) := Fin d × CoordSign d

omit β σ in
/-- The pieces, enumerated. -/
noncomputable def pieceEnum : Fin (Fintype.card (PieceIdx d)) ≃ PieceIdx d :=
  (Fintype.equivFin (PieceIdx d)).symm

omit β σ in
/-- **The assembled localisation datum on the blow-up**: the sum of the transported piece data,
phase `K ∘ π`, observable `F ∘ π`, level `1`. -/
noncomputable def cubeDatumU : LocalisationData (BlowUpSpace d) :=
  LocalisationData.finsum (fun i : PieceIdx d => pieceDatumU i.1 i.2 A hp0) (K ∘ π) (FM A ∘ π)
    measurable_K_π (fun _ => rfl) (fun _ => rfl) 1 one_pos

omit β σ [NeZero d] in
theorem cubeDatumU_μ :
    (cubeDatumU A hp0).μ = ∑ i : PieceIdx d, (pieceMeasure i.1 A i.2).map (Ψσ i.1 i.2) := rfl

omit β σ in
/-- **The assembled core decomposition**: the `d · 2^d` transported cores. -/
noncomputable def cubeCoresU :
    AnalyticCoreDecomposition (cubeDatumU A hp0) (Fintype.card (PieceIdx d))
      (fun k => ↥(baseSet (pieceEnum k).1 (pieceEnum k).2)) (fun k => nI (Iβ (pieceEnum k).1)) 1 :=
  AnalyticCoreDecomposition.finsum (fun i : PieceIdx d => pieceCoresU' i.1 i.2 A hp0) pieceEnum

omit β σ in
/-- Pushforward of a finite sum of measures. -/
theorem map_finset_sum {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] {ι : Type*}
    (s : Finset ι) (μ : ι → Measure α) {f : α → γ} (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

omit β σ in
/-- **Transport**: the assembled measure pushes forward along `π` to the prior measure on the
cube. -/
theorem cubeDatumU_map_π :
    (cubeDatumU A hp0).μ.map π =
      (volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (pM A x) := by
  rw [cubeDatumU_μ, map_finset_sum _ _ continuous_π.measurable]
  simp_rw [Measure.map_map continuous_π.measurable (measurable_Ψσ _ _)]
  rw [Fintype.sum_prod_type]
  exact sum_map_pieceMeasure A hp0

/-! ### The frames at the transported base points -/

omit [NeZero d] in
/-- The frame at a point of the divisor image, transported from the chart face along the base
homeomorphism. -/
noncomputable def frameAt (s : ↥(baseSet β σ)) :
    (Fin (nI (Iβ β) + 1) → ℝ) ≃L[ℝ] normalLine Finset.univ s.1.1 :=
  (frame β σ ((baseHomeo β σ).symm s)).trans
    (LinearEquiv.ofEq (normalLine Finset.univ (baseMap β σ ((baseHomeo β σ).symm s)).1)
      (normalLine Finset.univ s.1.1) (by rw [baseHomeo_symm_spec])).toContinuousLinearEquiv

omit [NeZero d] in
theorem frameAt_coe (s : ↥(baseSet β σ)) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    (frameAt β σ s u : EuclideanSpace ℝ (Fin d)) = (frame β σ ((baseHomeo β σ).symm s) u :
      EuclideanSpace ℝ (Fin d)) := rfl

omit [NeZero d] in
/-- The `Φ_eq` field: the transported chart core map is the genuine tubular germ along the
frame at the transported base point. -/
theorem Φ_eq_frameAt (s : ↥(baseSet β σ)) (u : Fin (nI (Iβ β) + 1) → ℝ) :
    ((pieceCoresU' β σ A hp0).chart 0).Φ (s, u) =
      tubular Finset.univ s.1.1 (frameAt β σ s u) := by
  rw [pieceCoresU'_chart_Φ]
  change Ψ β (refl σ _) = _
  rw [Ψ_Φ_eq_tubular]
  apply Subtype.ext
  apply Prod.ext
  · change π (baseMap β σ ((baseHomeo β σ).symm s)).1 +
      (frame β σ ((baseHomeo β σ).symm s) u : EuclideanSpace ℝ (Fin d)).ofLp =
      π s.1.1 + (frameAt β σ s u : EuclideanSpace ℝ (Fin d)).ofLp
    rw [frameAt_coe, show π (baseMap β σ ((baseHomeo β σ).symm s)).1 = π s.1.1 from
      congrArg (fun t : (blowUpGeometry d).Stratum Finset.univ => π t.1)
        (baseHomeo_symm_spec β σ s)]
  · change projOf (baseMap β σ ((baseHomeo β σ).symm s)).1 = projOf s.1.1
    rw [baseHomeo_symm_spec]

/-! ### The normal-moment presentations of the transported cores -/

omit [NeZero d] in
/-- On the fibre balls of the chart core the transported observable is the piece's observable
representative. -/
theorem obs_compat_ball (v : PieceBase β) (u : Fin (nI (Iβ β) + 1) → ℝ)
    (hu : u ∈ Metric.eball (0 : Fin (nI (Iβ β) + 1) → ℝ)
      (((pieceCert β A σ hp0).T (piece0 β σ A hp0)).R v)) :
    (FM A ∘ π) (Ψσ β σ (((pieceCert β A σ hp0).cores.chart (piece0 β σ A hp0)).Φ (v, u))) =
      (pieceCert β A σ hp0).L.obs
        (((pieceCert β A σ hp0).cores.chart (piece0 β σ A hp0)).Φ (v, u)) := by
  change u ∈ Metric.eball (0 : Fin (nI (Iβ β) + 1) → ℝ) (ENNReal.ofReal (pieceB' β A σ)) at hu
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hu
  have hn : ‖u‖ < pieceB' β A σ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 hu
  have hu0 : |u 0| ≤ 1 := by
    have h1 : |u 0| ≤ ‖u‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm u 0)
    exact h1.trans (hn.le.trans (pieceB'_le_one β σ A))
  exact obs_compat β σ A (Φ_mem_cube β hu0)

omit [NeZero d] in
/-- The transported and reindexed normal-moment presentation of a piece. -/
noncomputable def pieceTU :
    CoreNormalMomentPresentation ((pieceCoresU' β σ A hp0).chart 0) :=
  ((((pieceCert β A σ hp0).T (piece0 β σ A hp0)).mapAmbient (Ψσ β σ) (measurable_Ψσ β σ)
    (pieceDatumU β σ A hp0) (phase_compat β σ) (obs_compat_chart β σ A hp0 (piece0 β σ A hp0))
    (obs_compat_ball β σ A hp0)).reindex (baseHomeo β σ))

omit β σ in
/-- The normal-moment presentations of the assembled cores. -/
noncomputable def cubeT (k : Fin (Fintype.card (PieceIdx d))) :
    CoreNormalMomentPresentation ((cubeCoresU A hp0).chart k) :=
  (pieceTU (pieceEnum k).1 (pieceEnum k).2 A hp0).congrData (cubeDatumU A hp0) rfl rfl

omit β σ in
theorem cubeT_p (k : Fin (Fintype.card (PieceIdx d)))
    (s : ↥(baseSet (pieceEnum k).1 (pieceEnum k).2)) :
    (cubeT A hp0 k).p s = ((pieceCert (pieceEnum k).1 A (pieceEnum k).2 hp0).T
      (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)).p
      ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s) := rfl

/-! ### The certificate -/

omit β σ in
/-- ★★★ **The resolved certificate of the cube integral on the genuine blow-up**: the `d · 2^d`
chart certificates transported along the piece charts, based on the exceptional divisor and
summed; prior `p`, observable `F` (both cut off outside the cube), phase `K = |x|²`. -/
noncomputable def cubeCert :
    ResolvedCertificate (blowUpGeometry d) (blowUpNormalData d) (cube d) K (pM A) (FM A) where
  L := cubeDatumU A hp0
  obs_eq := rfl
  phase_eq := rfl
  transport := cubeDatumU_map_π A hp0
  M := Fintype.card (PieceIdx d)
  n := fun k => nI (Iβ (pieceEnum k).1)
  strat := fun _ => Finset.univ
  base := fun k => baseSet (pieceEnum k).1 (pieceEnum k).2
  isCompact_base := fun _ => isCompact_baseSet _ _
  β := 1
  β_pos := one_pos
  cores := cubeCoresU A hp0
  T := cubeT A hp0
  frame := fun k s => frameAt (pieceEnum k).1 (pieceEnum k).2 s
  Φ_eq := fun k s u => Φ_eq_frameAt (pieceEnum k).1 (pieceEnum k).2 A hp0 s u

omit β σ in
theorem cubeCert_cores_b (k : Fin (cubeCert A hp0).M) :
    (cubeCert A hp0).cores.b k = pieceB (pieceEnum k).1 A (pieceEnum k).2 := rfl

omit β σ in
/-- ★★ **The coefficient certificate on the genuine blow-up**: the piece factorisation families
and observable jets, transported. -/
noncomputable def cubeCoeffCert : (cubeCert A hp0).CoefficientCertificate where
  cc := fun k s => (pieceCoeff (pieceEnum k).1 A (pieceEnum k).2 hp0).cc
    (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)
    ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s)
  cc_abs := fun k s => (pieceCoeff (pieceEnum k).1 A (pieceEnum k).2 hp0).cc_abs
    (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0) _
  jet_abs := fun k s => by
    change (jetFamily (nI (Iβ (pieceEnum k).1))
      (((cubeCoresU A hp0).chart k).obsFibre s)).AbsSummableAt
        (pieceB (pieceEnum k).1 A (pieceEnum k).2)
    rw [jetFamily_eq_monoFamily ((cubeT A hp0 k).analytic s)]
    have h := (pieceCoeff (pieceEnum k).1 A (pieceEnum k).2 hp0).jet_abs
      (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)
      ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s)
    rw [jetFamily_eq_monoFamily (((pieceCert (pieceEnum k).1 A (pieceEnum k).2 hp0).T
      (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)).analytic
      ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s))] at h
    exact h
  datum_eq := fun k s => by
    change toEta (pieceB (pieceEnum k).1 A (pieceEnum k).2) (((cubeCoresU A hp0).chart k).x s) =
      CoeffFamily.conv _
        (jetFamily (nI (Iβ (pieceEnum k).1)) (((cubeCoresU A hp0).chart k).obsFibre s))
    rw [jetFamily_eq_monoFamily ((cubeT A hp0 k).analytic s)]
    have h := (pieceCoeff (pieceEnum k).1 A (pieceEnum k).2 hp0).datum_eq
      (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)
      ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s)
    rw [jetFamily_eq_monoFamily (((pieceCert (pieceEnum k).1 A (pieceEnum k).2 hp0).T
      (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)).analytic
      ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s))] at h
    have hx : ((cubeCoresU A hp0).chart k).x s =
        ((pieceCert (pieceEnum k).1 A (pieceEnum k).2 hp0).cores.chart
          (piece0 (pieceEnum k).1 (pieceEnum k).2 A hp0)).x
          ((baseHomeo (pieceEnum k).1 (pieceEnum k).2).symm s) :=
      CorePresentation.reindex_x _ _ _
    rw [hx]
    exact h

/-! ### The coordinate-free expansion on the genuine blow-up -/

omit β σ in
/-- ★★★ **The coordinate-free expansion of the cube integral on the genuine blow-up**: the
certificate theorem applied to `cubeCert`/`cubeCoeffCert`, on a resolved space with a collapsing
`π` and the tautological line bundle as normal bundle. -/
theorem cube_hasCoordFreeExpansion_blowUp :
    (blowUpNormalData d).HasCoordFreeExpansion (cubeCert A hp0).stratumMeasure
      (cubeCoeffCert A hp0).field
      (spectrumLe (commonQ (cubeCert A hp0).cores.k) (commonD (cubeCert A hp0).n)) (cube d) K
      (pM A) (FM A) :=
  (cubeCoeffCert A hp0).hasCoordFreeExpansion_le continuous_K.measurable (measurable_pM A)
    (pM_nonneg A hp0) (measurable_FM A)

end BlowUpCube

end Grammar
