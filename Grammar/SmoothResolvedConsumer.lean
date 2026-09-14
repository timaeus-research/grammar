/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothObservableCoeff
import Monomialize.Transport.ResolvedCoreTransport

/-!
# The resolved consumer: the expansion of `Z^U_N[F] = ∫_U F e^{−N K∘π} dμ_U`

Consult #126, Units D2–D3 (first half). The bridge consumer (`SmoothBridgeConsumer`) expands
`∫ prior · f · e^{−NK}` on `ℝ^d` from a normalised core transport. Here the same smooth engine
runs on the RESOLVED manifold `U` of a Watanabe modification `R : WatanabeModificationOn K W`:
the localisation datum is `(μ_U, K ∘ π, F)` with `μ_U = R.resolvedMeasure` the canonical
lift of `prior · vol` (hironaka `ResolvedMeasure`), `π = R.gv` the blow-down and
`F : U → ℝ` a smooth function on the manifold — NOT necessarily a pull-back along `π`. The
pieces are the lifted cores of a resolved core transport `Y` (hironaka
`ResolvedCoreTransport`), presented in the resolution charts `φ i` with amplitude
`ρ · (F ∘ φ_i⁻¹)`; the tail is the lifted tail with the same phase gap.

* `ResolvedData d`: the phase, the modification, the prior, the observable `F` on `U`.
* `ResolvedData.D Y`: the localisation datum on `U`; `Z Y N = ∫_U F e^{−N K∘π} dμ_U`.
* ★★★ `ResolvedData.decomp Y`: the smooth core decomposition of `D Y` — one smooth core
  presentation per resolution chart and orthant, the lifted tail as the tail.
* ★★★ `ResolvedData.hasSmoothCoordFreeExpansion`: `Z^U_N[F]` has the smooth coordinate-free
  expansion with coefficients `(decomp Y).coeff`, lattice `commonQ⁻¹ℕ`, log degree `≤ d − 1`.
* ★★ `ResolvedData.coeff_eq_of_transports`: the coefficients do not depend on the resolved core
  transport `Y` (uniqueness of expansion coefficients): the **resolved coefficient functional**
  `resolvedCoeff Ξ Y μ q` is intrinsic to `(U, π, μ_U, F)`.
* ★★★ `ResolvedData.coeff_comp_gv`: for a pull-back `F = f ∘ π`, the resolved coefficient is the
  observable coefficient `C_{μ,q}(f)` of Theorem C (`BridgeInputs.observableCoeff`): the
  resolved functional restricts to Theorem C's distribution on pull-backs.

The presentation reuses the Euclidean chart machinery of `BridgeInputs` (orthant boxes, the
active coordinates, the affine chart coordinate `Tm`, the extended transport density `ρf`)
through an auxiliary bridge input with zero observable; only the amplitude and the chart map
into `U` differ.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-- The resolved inputs: a phase with a Watanabe modification over `W`, a smooth compactly
supported nonnegative prior inside `W`, and a smooth observable `F` on the resolved manifold. -/
structure ResolvedData (d : ℕ) where
  /-- the phase -/
  K : (Fin d → ℝ) → ℝ
  /-- the open set carrying the modification -/
  W : TopologicalSpace.Opens (Fin d → ℝ)
  /-- the Watanabe modification -/
  R : WatanabeModificationOn K W
  hKc : ContinuousOn K (W : Set (Fin d → ℝ))
  hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x
  K_m : Measurable K
  /-- the prior -/
  prior : (Fin d → ℝ) → ℝ
  prior_smooth : ContDiff ℝ ∞ prior
  prior_nonneg : ∀ y, 0 ≤ prior y
  prior_compact : HasCompactSupport prior
  prior_W : tsupport prior ⊆ (W : Set (Fin d → ℝ))
  /-- the observable on the resolved manifold -/
  F : R.U → ℝ
  F_smooth : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ F

namespace ResolvedData

variable (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-- The resolved inputs with the observable replaced. -/
def withF (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) : ResolvedData d :=
  { Ξ with F := G, F_smooth := hG }

theorem withF_R (G : Ξ.R.U → ℝ) (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).R = Ξ.R := rfl

/-- The resolved measure `μ_U`. -/
noncomputable def μU : Measure Ξ.R.U := Ξ.R.resolvedMeasure Ξ.hKc Ξ.prior

/-- The pulled-back phase `K ∘ π`. -/
noncomputable def phaseU (P : Ξ.R.U) : ℝ := Ξ.K (Ξ.R.gv P)

theorem measurable_phaseU : Measurable Ξ.phaseU := Ξ.K_m.comp Ξ.R.measurable_gv

theorem phaseU_nonneg (P : Ξ.R.U) : 0 ≤ Ξ.phaseU P := Ξ.hK0 _ (Ξ.R.gv_mem P)

theorem integrable_prior : Integrable Ξ.prior :=
  Ξ.prior_smooth.continuous.integrable_of_hasCompactSupport Ξ.prior_compact

theorem isFiniteMeasure_μU : IsFiniteMeasure Ξ.μU :=
  Ξ.R.isFiniteMeasure_resolvedMeasure Ξ.hKc Ξ.prior Ξ.hK0 Ξ.prior_compact Ξ.prior_W
    Ξ.integrable_prior

theorem ae_μU_mem : ∀ᵐ P ∂Ξ.μU, Ξ.R.gv P ∈ tsupport Ξ.prior :=
  Ξ.R.ae_resolvedMeasure_mem_preimage_tsupport Ξ.hKc Ξ.prior Ξ.hK0 Ξ.prior_compact Ξ.prior_W

/-- A continuous function on `U` is integrable against `μ_U`: the measure is finite and carried
by the compact set `π⁻¹(supp prior)`. -/
theorem integrable_of_continuous {G : Ξ.R.U → ℝ} (hG : Continuous G) : Integrable G Ξ.μU := by
  have := Ξ.isFiniteMeasure_μU
  obtain ⟨B, hB⟩ := (Ξ.R.isCompact_gv_preimage_tsupport Ξ.prior Ξ.prior_compact
    Ξ.prior_W).exists_bound_of_continuousOn hG.continuousOn
  exact Integrable.of_bound hG.aestronglyMeasurable B (Ξ.ae_μU_mem.mono fun P hP => hB P hP)

theorem F_int : Integrable Ξ.F Ξ.μU := Ξ.integrable_of_continuous Ξ.F_smooth.continuous

/-- The localisation datum `(μ_U, K ∘ π, F)` on the resolved manifold. -/
noncomputable def D : LocalisationData Ξ.R.U where
  μ := Ξ.μU
  phase := Ξ.phaseU
  obs := Ξ.F
  phase_measurable := Ξ.measurable_phaseU
  phase_nonneg := Eventually.of_forall Ξ.phaseU_nonneg
  obs_integrable := Ξ.F_int
  δ := Y.T.δ
  δ_pos := Y.T.δ_pos

theorem D_μ : (Ξ.D Y).μ = Ξ.μU := rfl
theorem D_phase : (Ξ.D Y).phase = Ξ.phaseU := rfl
theorem D_obs : (Ξ.D Y).obs = Ξ.F := rfl

/-- `Z^U_N[F] = ∫_U F e^{−N K∘π} dμ_U`. -/
noncomputable def Z (N : ℝ) : ℝ := ∫ P, Ξ.F P * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU

theorem D_Z (N : ℝ) : (Ξ.D Y).Z N = Ξ.Z N := rfl

/-! ### The auxiliary Euclidean bridge input -/

/-- The Euclidean bridge input with zero observable: it carries the chart machinery (orthant
boxes, active coordinates, the affine chart coordinate, the extended transport density). -/
abbrev X : BridgeInputs d :=
  ⟨Ξ.K, Ξ.prior, fun _ => 0, Y.T, Ξ.K_m, Ξ.prior_smooth, Ξ.prior_nonneg, Ξ.prior_compact,
    contDiff_const⟩

/-! ### The chart amplitudes -/

/-- The local amplitude `ω · |b| · prior ∘ ψ · F ∘ φ⁻¹` of chart `i`, smooth on `V i`. -/
noncomputable def Gloc (i : Y.T.ι) (u : Fin d → ℝ) : ℝ :=
  (Ξ.X Y).ρloc i u * Ξ.F (Y.chartInv i u)

theorem contDiffOn_Gloc (i : Y.T.ι) : ContDiffOn ℝ ∞ (Ξ.Gloc Y i) (Y.T.V i) := by
  refine ((Ξ.X Y).contDiffOn_ρloc i).mul ?_
  rw [Y.V_eq i]
  exact Y.contDiffOn_comp_chartInv Ξ.F_smooth i

theorem exists_G (i : Y.T.ι) : ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
    EqOn g (Ξ.Gloc Y i) (centeredBox d (Y.T.a i)) := by
  obtain ⟨g, hg, heq, -⟩ := exists_contDiff_eqOn_of_contDiffOn (Y.T.V_open i)
    (isCompact_centeredBox d (Y.T.a i)).isClosed (Y.T.box_subset_V i) (Ξ.contDiffOn_Gloc Y i)
  exact ⟨g, hg, heq⟩

/-- The globally smooth amplitude of chart `i`, equal to `ω · |b| · prior ∘ ψ · F ∘ φ⁻¹` on the
box. -/
noncomputable def G (i : Y.T.ι) : (Fin d → ℝ) → ℝ := Classical.choose (Ξ.exists_G Y i)

theorem contDiff_G (i : Y.T.ι) : ContDiff ℝ ∞ (Ξ.G Y i) :=
  (Classical.choose_spec (Ξ.exists_G Y i)).1

theorem G_eq (i : Y.T.ι) {u : Fin d → ℝ} (hu : u ∈ centeredBox d (Y.T.a i)) :
    Ξ.G Y i u = Ξ.Gloc Y i u := (Classical.choose_spec (Ξ.exists_G Y i)).2 hu

/-! ### The lifted pieces -/

/-- The lifted core measure of a piece: the weighted orthant-box measure pushed into `U` along
the chart inverse. -/
noncomputable def coreMeasure (p : (Ξ.X Y).PIdx) : Measure Ξ.R.U :=
  ((volume.restrict (WaterFilling.orthantBox p.2 (Y.T.a p.1))).withDensity fun w =>
    ENNReal.ofReal (NormalisedBox.wgt (Y.T.h p.1) w * (Ξ.X Y).ρf p.1 w)).map (Y.chartInv p.1)

/-- The pieces of a chart exhaust its lifted core. -/
theorem sum_coreMeasure_chart (i : Y.T.ι) :
    ∑ σ : WaterFilling.CoordSign d, Ξ.coreMeasure Y ⟨i, σ⟩ = Y.coreU i := by
  unfold coreMeasure
  rw [Y.coreU_eq_map_chartInv, ← SmoothSheetInputs.map_finset_sum' _ _ (Y.measurable_chartInv i)]
  congr 1
  have h := (Ξ.X Y).coreSource_eq i
  rw [(Ξ.X Y).box_eq i, BridgeInputs.restrict_signedBox_eq, ← Measure.sum_fintype
    fun σ : WaterFilling.CoordSign d => volume.restrict (WaterFilling.orthantBox σ (Y.T.a i)),
    withDensity_sum, Measure.sum_fintype] at h
  exact h.symm

/-- ★ **The lifted pieces and the lifted tail exhaust the resolved measure** (the resolved
transport identity). -/
theorem sum_coreMeasure : ∑ p : (Ξ.X Y).PIdx, Ξ.coreMeasure Y p + Y.tailU = Ξ.μU := by
  rw [μU, ← Y.transport Ξ.hK0 Ξ.prior_compact Ξ.prior_W, Fintype.sum_sigma]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Ξ.sum_coreMeasure_chart Y i

/-! ### The smooth core presentation of a piece -/

/-- The amplitude family of a piece: the pull-back of the extended amplitude along the chart
coordinate. -/
noncomputable def amp (p : (Ξ.X Y).PIdx) :
    SmoothAmplitudeFamily (Base ((Ξ.X Y).act p.1) (Y.T.a p.1)) ((Ξ.X Y).da p) (Y.T.a p.1) :=
  SmoothAmplitudeFamily.ofAffine ((Ξ.X Y).continuous_sc p) ((Ξ.X Y).eqv p) p.2 (Ξ.contDiff_G Y p.1)
    (Y.T.a p.1)

/-- ★★ **The smooth core presentation of a lifted piece**: constant phase unit, transport density
`ρf`, amplitude `G`, chart map `φ⁻¹ ∘ Tm` into `U`. -/
noncomputable def piecePresentation (p : (Ξ.X Y).PIdx) :
    SmoothCorePresentation (Ξ.D Y) (Ξ.coreMeasure Y p) (Base ((Ξ.X Y).act p.1) (Y.T.a p.1))
      ((Ξ.X Y).da p) where
  ν := baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1)
  h := (Ξ.X Y).hA p
  k := (Ξ.X Y).kA p
  k_pos := (Ξ.X Y).kA_pos p
  b := Y.T.a p.1
  b_pos := Y.T.a_pos p.1
  βf _ := Y.T.phaseConst p.1
  β_cont := continuous_const
  β_pos _ := Y.T.phaseConst_pos p.1
  Φ z := Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_Φ := (Y.measurable_chartInv p.1).comp ((Ξ.X Y).continuous_Tm p).measurable
  ρ z := (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)
  measurable_ρ := (((Ξ.X Y).contDiff_ρf p.1).continuous.comp ((Ξ.X Y).continuous_Tm p)).measurable
  nonneg_ρ := Eventually.of_forall fun z => (Ξ.X Y).ρf_nonneg p.1 _
  amp := Ξ.amp Y p
  amplitude_eq := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    change Ξ.G Y p.1 ((Ξ.X Y).Tm p z.1 z.2) =
      (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2) * Ξ.F (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))
    rw [Ξ.G_eq Y p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv), (Ξ.X Y).ρf_eq p.1 ((Ξ.X Y).Tm_mem_box p z.1 hv)]
    rfl
  phase_normal := by
    refine (ae_snd_mem_box' ((Ξ.X Y).act p.1) (Y.T.a p.1)
      (baseMeasure ((Ξ.X Y).act p.1) (Y.T.a p.1) (Y.T.h p.1))).mono fun z hz => ?_
    have hv : ∀ j, z.2 j ∈ Icc 0 (Y.T.a p.1) := fun j => Ioc_subset_Icc_self (hz j (Set.mem_univ j))
    have hbox := (Ξ.X Y).Tm_mem_box p z.1 hv
    change Ξ.K (Ξ.R.gv (Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2))) = _
    rw [← Y.ψ_eq_gv_chartInv p.1 (Y.box_subset_target p.1 hbox),
      Y.T.phase_eq p.1 _ (Y.T.box_subset_V p.1 hbox)]
    congr 1
    exact (Ξ.X Y).prod_Tm_pow p z.1 z.2
  transport := by
    have hΦ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        Y.chartInv p.1 ((Ξ.X Y).Tm p z.1 z.2)) =
        (Y.chartInv p.1 ∘ WaterFilling.refl p.2) ∘
          glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) := by
      funext z
      simp only [Function.comp_apply, glueE']
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
    have hρ : (fun z : Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) =>
        ((mono ((Ξ.X Y).hA p) z.2 * (Ξ.X Y).ρf p.1 ((Ξ.X Y).Tm p z.1 z.2)).toNNReal : ℝ≥0∞)) =
        fun z => ENNReal.ofReal (mono (fun j => Y.T.h p.1 ((Ξ.X Y).eqv p j).1) z.2 *
          (Ξ.X Y).ρf p.1 (WaterFilling.refl p.2
            (glueE' ((Ξ.X Y).act p.1) (Y.T.a p.1) ((Ξ.X Y).eqv p) z))) := by
      funext z
      rw [(Ξ.X Y).Tm_eq_refl_glueE]
      rfl
    rw [hρ, hΦ, ← Measure.map_map ((Y.measurable_chartInv p.1).comp
      (WaterFilling.measurable_refl _)) (measurableEmbedding_glueE' _ _ _).measurable,
      ← Measure.map_map (Y.measurable_chartInv p.1) (WaterFilling.measurable_refl _)]
    unfold smoothChartMeasure
    rw [map_glueE'_pieceMeasure _ _ _ _ ((Ξ.X Y).measurable_ρf p.1),
      ChartCollar.map_refl_pieceMeasure]
    rfl

/-! ### The smooth core decomposition -/

/-- ★★★ **The smooth core decomposition of `Z^U_N[F]`**: one smooth core presentation per
resolution chart and orthant, the lifted tail as the tail. -/
noncomputable def decomp : SmoothCoreDecomposition (Ξ.D Y) (Fintype.card (Ξ.X Y).PIdx)
    (fun I => Base ((Ξ.X Y).act ((Ξ.X Y).en I).1) (Y.T.a ((Ξ.X Y).en I).1))
    (fun I => (Ξ.X Y).da ((Ξ.X Y).en I)) where
  core I := Ξ.coreMeasure Y ((Ξ.X Y).en I)
  tail := Y.tailU
  measure_eq := by
    rw [Ξ.D_μ, ← Ξ.sum_coreMeasure Y]
    congr 1
    exact (Equiv.sum_comp (Ξ.X Y).en (Ξ.coreMeasure Y)).symm
  δ₀ := Y.T.δ
  δ₀_pos := Y.T.δ_pos
  gap := Y.ae_tailU_gap Ξ.hK0 Ξ.prior_compact Ξ.prior_W
  chart I := Ξ.piecePresentation Y ((Ξ.X Y).en I)

/-- The logarithmic degree is at most `d − 1`. -/
theorem commonD_le : (Ξ.decomp Y).commonD ≤ d - 1 :=
  Finset.sup_le fun I _ => Nat.sub_le_sub_right ((Ξ.X Y).da_le ((Ξ.X Y).en I)) 1

/-- ★★★ **The smooth coordinate-free expansion of `Z^U_N[F]`** on the resolved manifold: for
every `A`, `∫_U F e^{−N K∘π} dμ_U − ∑_{exponent ≤ A} coeff · N^{−α}(log N)^j = o(N^{−A})`, on
the lattice `commonQ⁻¹ℕ` with logarithmic degree `≤ commonD ≤ d − 1`. -/
theorem hasSmoothCoordFreeExpansion :
    HasSmoothCoordFreeExpansion Ξ.Z (Ξ.decomp Y).coeff (Ξ.decomp Y).commonQ
      (Ξ.decomp Y).commonD :=
  (Ξ.decomp Y).hasSmoothCoordFreeExpansion

/-- The scalar expansion certificate of `Z^U_N[F]`. -/
noncomputable def certificate : SmoothExpansionCertificate Ξ.Z := (Ξ.decomp Y).toCertificate

/-- ★ **The resolved coefficient functional** `𝒯^U_{μ,q}[F]`: the coefficient of
`N^{−μ}(log N)^q` in the expansion of `∫_U F e^{−N K∘π} dμ_U`. -/
noncomputable def coeff (μ : ℝ) (q : ℕ) : ℝ := (Ξ.decomp Y).coeff μ q

/-- ★★ **Intrinsicness in the transport**: the resolved coefficients do not depend on the
resolved core transport. -/
theorem coeff_eq_of_transports (Y' : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) (μ : ℝ) (q : ℕ) :
    Ξ.coeff Y μ q = Ξ.coeff Y' μ q :=
  SmoothExpansionCertificate.coeff_eq (Ξ.certificate Y) (Ξ.certificate Y') μ q

/-! ### Pull-backs: the resolved functional restricts to Theorem C -/

/-- A smooth function on `ℝ^d` pulled back along the blow-down is smooth on `U`. -/
theorem contMDiff_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun P => f (Ξ.R.gv P)) :=
  hf.contMDiff.comp (Ξ.R.contMDiff_gv.of_le le_top)

/-- `Z^U_N[f ∘ π] = Z_N[f] = ∫ prior · f · e^{−NK}`: the observable identity of the resolved
measure. -/
theorem Z_withF_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (N : ℝ) :
    (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).Z N =
      partitionObs Ξ.K Ξ.prior f N := by
  unfold Z partitionObs
  change ∫ P, f (Ξ.R.gv P) * Real.exp (-N * Ξ.K (Ξ.R.gv P)) ∂Ξ.μU = _
  rw [μU, Ξ.R.integral_boltzmann_resolvedMeasure Ξ.hKc Ξ.prior Ξ.hK0 Ξ.prior_compact Ξ.prior_W
    Ξ.prior_smooth.continuous.measurable Ξ.prior_nonneg hf.continuous Ξ.K_m N]
  exact integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- ★★★ **The resolved functional restricts to Theorem C on pull-backs**: for `F = f ∘ π`, the
resolved coefficient equals the observable coefficient `C_{μ,q}(f)` of the Euclidean bridge
input built from the same transport. -/
theorem coeff_comp_gv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : ℝ) (q : ℕ) :
    (Ξ.withF (fun P => f (Ξ.R.gv P)) (Ξ.contMDiff_comp_gv hf)).coeff Y μ q =
      (Ξ.X Y).observableCoeff μ q f hf :=
  SmoothExpansionCertificate.coeff_eq
    (((Ξ.withF _ (Ξ.contMDiff_comp_gv hf)).certificate Y).congr
      (Eventually.of_forall fun N => Ξ.Z_withF_comp_gv hf N))
    ((Ξ.X Y).obsCertificate hf) μ q

end ResolvedData

end SmoothEngine

end Grammar
