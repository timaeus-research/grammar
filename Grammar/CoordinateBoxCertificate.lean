/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CollarDecomposition
import Grammar.CoordFreeExpansionCompletion

/-!
# The compact-box certificate on the coordinate model (CCCXXIV)

Consult #96 unit 5a: the general compact-box PRODUCER from uniform face-normal series. On the
coordinate model `ℝ^d` (components the coordinate hyperplanes, orders `k`, `h = 0`) with the
monomial phase `K = ∏ w_i^{2k_i}` on `W = [0,a]^d`, a measurable nonnegative prior `ϕ` and an
observable `φ`, the water-filling collar (CCCXXII–CCCXXIII) is assembled into a
`ResolvedCertificate` against the coordinate normal data:

* for every nonempty `I` the base `baseStratum I ⊆ S_I` is the compact set of stratum points whose
  tangential coordinates lie in `B_I` (`compactSpace_KI`: it is the continuous image of `B_I` under
  the lift `t ↦ (0, t)`), embedded by the tangential coordinates `eI` (`range_eI`);
* the frame `frameI s : ℝ^{|I|} ≃L[ℝ] N_I = span{e_i : i ∈ I}` is the reindexed diagonal scaling
  `u ↦ Σ_i λ_{I,i}(s) u_{σ⁻¹ i} e_i` (`coe_frameI_apply`), and the tubular identity `Φ_eq_frame`
  identifies the core parametrisation `s + Σ λ_i v_i e_i` with the coordinate model's tubular germ
  `s + ξ` along it;
* ★★ `certificate` and ★★ `coeffCertificate` (density family `J·fϕ`, jets `fφ` by
  `jetFamily_obsFibre`, datum identity `toEta_core_x`);
* ★★★ `hasCoordFreeExpansion_collar`: the coordinate-free expansion of `∫_{[0,a]^d} φ ϕ e^{−nK}`
  with strata integrals over ALL nonempty coordinate strata, from LOCAL normal series
  (`FaceSeries`: uniform series families over each base in the normalised normal variables at
  radius `2b_I`) — not a single series across the whole box.

Non-claims: the face series are hypotheses in the normalised normal variables (the rescaling
from series in the original variables is `UniformSeriesFamily.rescale`, to be applied in the
analytic-neighbourhood bridge); the spectrum is the common lattice `spectrumLe (commonQ …)
(commonD …)` of the cores. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open NormalisedBox CoeffFamily CoordModel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ)

/-- The Jacobian orders of the coordinate model with Lebesgue prior: all zero. -/
def zeroOrders (d : ℕ) : Fin d → ℕ := fun _ => 0

/-! ### The bases inside the strata -/

/-- The base of the stratum `I`: the stratum points whose tangential coordinates lie in `B_I`. -/
def baseStratum (I : Finset (Fin d)) : Set ((geometry d k (zeroOrders d) hk).Stratum I) :=
  {s | tan I s.1 ∈ baseSet k I a δ}

/-- The base type. -/
abbrev KI (I : Finset (Fin d)) := ↥(baseStratum k hk a δ I)

/-- The tangential coordinates of a base point. -/
def eI (I : Finset (Fin d)) : KI k hk a δ I → (Tan I → ℝ) := fun s => tan I s.1.1

theorem continuous_eI (I : Finset (Fin d)) : Continuous (eI k hk a δ I) :=
  continuous_pi fun j =>
    (continuous_apply j.1).comp (continuous_subtype_val.comp continuous_subtype_val)

omit a δ in
theorem stratum_coord_zero {I : Finset (Fin d)} (s : (geometry d k (zeroOrders d) hk).Stratum I)
    {i : Fin d} (hi : i ∈ I) : s.1 i = 0 :=
  ((mem_stratumSet_iff d k _ hk I s.1).1 s.2 i).2 hi

theorem eI_injective (I : Finset (Fin d)) : Function.Injective (eI k hk a δ I) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ I
  · rw [stratum_coord_zero k hk s.1 hj, stratum_coord_zero k hk t.1 hj]
  · exact congrFun hst ⟨j, hj⟩

omit k hk a δ in
/-- The lift of a tangential point to the coordinate plane of `I`. -/
noncomputable def liftPoint (I : Finset (Fin d)) (t : Tan I → ℝ) : Fin d → ℝ :=
  (split I).symm (0, t)

omit k hk a δ in
theorem liftPoint_apply (I : Finset (Fin d)) (t : Tan I → ℝ) (j : Fin d) :
    liftPoint I t j = if h : j ∈ I then 0 else t ⟨j, h⟩ := by
  unfold liftPoint
  rw [split_symm_apply]
  split_ifs <;> rfl

omit k hk a δ in
theorem tan_liftPoint (I : Finset (Fin d)) (t : Tan I → ℝ) : tan I (liftPoint I t) = t := by
  funext j
  rw [tan, liftPoint_apply, dif_neg j.2]

omit k hk a δ in
theorem continuous_liftPoint (I : Finset (Fin d)) : Continuous (liftPoint I) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j ∈ I
  · have : (fun t : Tan I → ℝ => liftPoint I t j) = fun _ => 0 := by
      funext t
      rw [liftPoint_apply, dif_pos hj]
    rw [this]
    exact continuous_const
  · have : (fun t : Tan I → ℝ => liftPoint I t j) = fun t => t ⟨j, hj⟩ := by
      funext t
      rw [liftPoint_apply, dif_neg hj]
    rw [this]
    exact continuous_apply _

theorem liftPoint_mem_stratum {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ)
    {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    liftPoint I t ∈ (geometry d k (zeroOrders d) hk).stratumSet I := by
  rw [mem_stratumSet_iff]
  intro i
  rw [liftPoint_apply]
  by_cases hi : i ∈ I
  · simp [hi]
  · rw [dif_neg hi]
    exact ⟨fun h => absurd h (pos_of_mem_baseSet k I a δ hk hI hδ ht ⟨i, hi⟩).ne',
      fun h => absurd h hi⟩

/-- The lift of the base `B_I` into the stratum. -/
noncomputable def liftBase {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ)
    (t : ↥(baseSet k I a δ)) : KI k hk a δ I :=
  ⟨⟨liftPoint I t.1, liftPoint_mem_stratum k hk a δ hI hδ t.2⟩, by
    change tan I (liftPoint I t.1) ∈ baseSet k I a δ
    rw [tan_liftPoint]
    exact t.2⟩

theorem continuous_liftBase {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ) :
    Continuous (liftBase k hk a δ hI hδ) :=
  (((continuous_liftPoint I).comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem eI_liftBase {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ) (t : ↥(baseSet k I a δ)) :
    eI k hk a δ I (liftBase k hk a δ hI hδ t) = t.1 :=
  tan_liftPoint I t.1

theorem range_eI (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    range (eI k hk a δ I) = baseSet k I a δ := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact s.2
  · intro ht
    exact ⟨liftBase k hk a δ hI hδ ⟨t, ht⟩, eI_liftBase k hk a δ hI hδ ⟨t, ht⟩⟩

theorem surjective_liftBase {I : Finset (Fin d)} (hI : I.Nonempty) (hδ : 0 < δ) :
    Function.Surjective (liftBase k hk a δ hI hδ) := by
  intro s
  refine ⟨⟨eI k hk a δ I s, s.2⟩, eI_injective k hk a δ I ?_⟩
  rw [eI_liftBase]

/-- The bases are compact. -/
theorem compactSpace_KI (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    CompactSpace (KI k hk a δ I) := by
  have : CompactSpace ↥(baseSet k I a δ) :=
    isCompact_iff_compactSpace.1 (isCompact_baseSet k I a δ)
  refine ⟨?_⟩
  rw [← (surjective_liftBase k hk a δ hI hδ).range_eq]
  exact isCompact_range (continuous_liftBase k hk a δ hI hδ)

theorem isCompact_baseStratum (I : Finset (Fin d)) (hI : I.Nonempty) (hδ : 0 < δ) :
    IsCompact (baseStratum k hk a δ I) :=
  isCompact_iff_compactSpace.2 (compactSpace_KI k hk a δ I hI hδ)

/-! ### Box coordinates and frames -/

omit k hk a δ in
/-- The normal dimension minus one of the stratum `I`. -/
abbrev nI (I : NonemptyIdx d) : ℕ := I.1.card - 1

omit k hk a δ in
/-- Box coordinates ↔ normal coordinates of the stratum `I`. -/
noncomputable def σI (I : NonemptyIdx d) : Fin (nI I + 1) ≃ Nrm I.1 :=
  (finCongr (Nat.sub_add_cancel I.2.card_pos)).trans (Finset.equivFin I.1).symm

variable (hδ : 0 < δ)

/-- The frame as a linear equivalence: `u ↦ Σ_i λ_{I,i}(s) u_{σ⁻¹ i} e_i`. -/
noncomputable def frameLin (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    (Fin (nI I + 1) → ℝ) ≃ₗ[ℝ] normalSpace d I.1 :=
  ((LinearEquiv.funCongrLeft ℝ ℝ (σI I)).symm.trans
    (LinearEquiv.piCongrRight fun j : Nrm I.1 =>
      LinearEquiv.smulOfNeZero ℝ ℝ (lamT k I.1 δ (eI k hk a δ I.1 s) j)
        (lamT_pos_of_mem_baseSet k I.1 a δ hk I.2 hδ
          (show eI k hk a δ I.1 s ∈ baseSet k I.1 a δ from s.2) j).ne')).trans
    (Module.Basis.span (linearIndependent_basisVec_restrict d I.1)).equivFun.symm

theorem frameLin_apply (I : NonemptyIdx d) (s : KI k hk a δ I.1) (u : Fin (nI I + 1) → ℝ) :
    frameLin k hk a δ hδ I s u =
      ∑ j : Nrm I.1, (lamT k I.1 δ (eI k hk a δ I.1 s) j * u ((σI I).symm j)) •
        Module.Basis.span (linearIndependent_basisVec_restrict d I.1) j := by
  change (Module.Basis.span (linearIndependent_basisVec_restrict d I.1)).equivFun.symm
    (fun j => lamT k I.1 δ (eI k hk a δ I.1 s) j * u ((σI I).symm j)) = _
  rw [Module.Basis.equivFun_symm_apply]

omit k hk a δ in
theorem basisVec_ofLp (j i : Fin d) : (basisVec d j).ofLp i = if i = j then 1 else 0 := by
  simp [basisVec]

theorem coe_frameLin_apply (I : NonemptyIdx d) (s : KI k hk a δ I.1) (u : Fin (nI I + 1) → ℝ)
    (i : Fin d) :
    ((frameLin k hk a δ hδ I s u : normalSpace d I.1) : Amb d).ofLp i =
      if h : i ∈ I.1 then lamT k I.1 δ (eI k hk a δ I.1 s) ⟨i, h⟩ * u ((σI I).symm ⟨i, h⟩)
      else 0 := by
  rw [frameLin_apply, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]
  have hterm : ∀ j : Nrm I.1,
      ((((lamT k I.1 δ (eI k hk a δ I.1 s) j * u ((σI I).symm j)) •
        Module.Basis.span (linearIndependent_basisVec_restrict d I.1) j : normalSpace d I.1) :
          Amb d)).ofLp i =
        (lamT k I.1 δ (eI k hk a δ I.1 s) j * u ((σI I).symm j)) * if i = j.1 then 1 else 0 := by
    intro j
    rw [Submodule.coe_smul, Module.Basis.span_apply]
    change ((lamT k I.1 δ (eI k hk a δ I.1 s) j * u ((σI I).symm j)) • basisVec d j.1).ofLp i = _
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  by_cases hi : i ∈ I.1
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      exact fun h => hj (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    exact fun h => hi (h ▸ j.2)

/-- The frame `ℝ^{|I|} ≃L N_I` at the base point `s`. -/
noncomputable def frameI (I : NonemptyIdx d) (s : KI k hk a δ I.1) :
    (Fin (nI I + 1) → ℝ) ≃L[ℝ] normalSpace d I.1 :=
  (frameLin k hk a δ hδ I s).toContinuousLinearEquiv

theorem coe_frameI_apply (I : NonemptyIdx d) (s : KI k hk a δ I.1) (u : Fin (nI I + 1) → ℝ)
    (i : Fin d) :
    ((frameI k hk a δ hδ I s u : normalSpace d I.1) : Amb d).ofLp i =
      if h : i ∈ I.1 then lamT k I.1 δ (eI k hk a δ I.1 s) ⟨i, h⟩ * u ((σI I).symm ⟨i, h⟩)
      else 0 :=
  coe_frameLin_apply k hk a δ hδ I s u i

/-- ★ **The tubular identity along the frame**: the core parametrisation `s + Σ λ_i v_i e_i` is the
coordinate model's tubular germ `s + ξ` at `ξ = frame u`. -/
theorem Φ_eq_frame (I : NonemptyIdx d) (s : KI k hk a δ I.1) (u : Fin (nI I + 1) → ℝ) :
    Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, u) =
      (normalData d k (zeroOrders d) hk).Φ I.1 s.1 (frameI k hk a δ hδ I s u) := by
  rw [normalData_Φ]
  funext j
  rw [Φ_apply, coe_frameI_apply]
  by_cases hj : j ∈ I.1
  · rw [dif_pos hj, dif_pos hj, stratum_coord_zero k hk s.1 hj, zero_add]
  · rw [dif_neg hj, dif_neg hj, add_zero]
    rfl

/-! ### The face series input and the certificate -/

variable (ϕ φ : (Fin d → ℝ) → ℝ)

/-- The local normal-series input at the stratum `I`: uniform series families over the base in the
normalised normal variables, at radius `2b_I`, agreeing with the prior on the box and with the
observable on the ball. -/
structure FaceSeries (I : NonemptyIdx d) where
  Fϕ : UniformSeriesFamily (KI k hk a δ I.1) (nI I + 1) (2 * side k I.1 δ)
  Fφ : UniformSeriesFamily (KI k hk a δ I.1) (nI I + 1) (2 * side k I.1 δ)
  hϕ_eq : ∀ s, ∀ v ∈ NormalisedBox.box (ι := Fin (nI I + 1)) (side k I.1 δ),
    ϕ (Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v)) = evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (nI I + 1) → ℝ), ‖v‖ < 2 * side k I.1 δ →
    φ (Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, v)) = evalF (Fφ.f s) v

/-- The stratum input of the collar from the face series. -/
noncomputable def FaceSeries.toStratumSeries {I : NonemptyIdx d} (F : FaceSeries k hk a δ ϕ φ I) :
    StratumSeries k a δ I.1 (nI I) (KI k hk a δ I.1) ϕ φ where
  σ := σI I
  e := eI k hk a δ I.1
  he := continuous_eI k hk a δ I.1
  he_inj := eI_injective k hk a δ I.1
  hre := range_eI k hk a δ I.1 I.2 hδ
  Fϕ := F.Fϕ
  Fφ := F.Fφ
  hϕ_eq := F.hϕ_eq
  hφ_eq := F.hφ_eq

variable (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφm : Measurable φ)
  (hφint : Integrable φ
    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))

/-- The localisation datum of the box problem. -/
noncomputable def locData : LocalisationData (Fin d → ℝ) where
  μ := (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)
  phase := CoordModel.phase d k
  obs := φ
  phase_measurable := measurable_phase d k
  phase_nonneg := Eventually.of_forall (phase_nonneg d k)
  obs_integrable := hφint
  δ := 1
  δ_pos := one_pos

variable (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
  (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I)

omit ϕ φ in
include hδ in
/-- The compactness instances of all the bases. -/
theorem instK : ∀ I : NonemptyIdx d, CompactSpace (KI k hk a δ I.1) := fun I =>
  compactSpace_KI k hk a δ I.1 I.2 hδ

/-- The stratum inputs of the collar from the face series. -/
noncomputable def stratumInputs (I : NonemptyIdx d) :
    StratumSeries k a δ I.1 (nI I) (KI k hk a δ I.1) ϕ φ :=
  (F I).toStratumSeries k hk a δ hδ ϕ φ

/-- ★★ **The resolved certificate of the compact box from face series**: the water-filling collar
against the coordinate normal data, with the diagonal frames. -/
noncomputable def certificate :
    ResolvedCertificate (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk)
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  have := instK k hk a δ hδ
  exact {
    L := locData k a ϕ φ hφint
    obs_eq := rfl
    phase_eq := rfl
    transport := by
      change Measure.map id _ = _
      rw [Measure.map_id]
      rfl
    M := numCores d
    n := fun i => nI (coreIdx i)
    strat := fun i => (coreIdx i).1
    base := fun i => baseStratum k hk a δ (coreIdx i).1
    isCompact_base := fun i => isCompact_baseStratum k hk a δ (coreIdx i).1 (coreIdx i).2 hδ
    β := 1
    β_pos := one_pos
    cores := collar k a δ hk hd ha hδ hδa hϕm (fun w _ => hϕ0 w) (locData k a ϕ φ hφint) rfl rfl
      rfl (stratumInputs k hk a δ hδ ϕ φ F)
    T := fun i => NormalisedBox.presentation hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData k a ϕ φ hφint) rfl rfl rfl
      ((stratumInputs k hk a δ hδ ϕ φ F (coreIdx i)).toData k a δ hk hd ha hδ hδa
        (coreIdx i).2)
    frame := fun i s => frameI k hk a δ hδ (coreIdx i) s
    Φ_eq := fun i s u => Φ_eq_frame k hk a δ hδ (coreIdx i) s u }

/-- The normalised box data of the core `i`. -/
noncomputable def coreData (i : Fin (numCores d)) :
    NormalisedBox.Data k (coreIdx i).1 (nI (coreIdx i)) (KI k hk a δ (coreIdx i).1)
      (piBox d (Icc 0 a)) ϕ φ :=
  (stratumInputs k hk a δ hδ ϕ φ F (coreIdx i)).toData k a δ hk hd ha hδ hδa (coreIdx i).2

include hδ hd ha hδa in
theorem cc_abs_aux (i : Fin (numCores d)) (s : KI k hk a δ (coreIdx i).1) :
    AbsSummableAt (fun γ => J (coreIdx i).1 (eI k hk a δ (coreIdx i).1) (lamT k (coreIdx i).1 δ) s *
      (F (coreIdx i)).Fϕ.f s γ) (side k (coreIdx i).1 δ) := by
  have := instK k hk a δ hδ
  exact ((F (coreIdx i)).Fϕ.smul (J (coreIdx i).1 (eI k hk a δ (coreIdx i).1)
      (lamT k (coreIdx i).1 δ))
    (continuous_J (coreIdx i).1 _ (continuous_eI k hk a δ _) _
      (coreData k hk a δ hδ ϕ φ hd ha hδa F i).hlam_cont) _
    (abs_J_le (coreIdx i).1 _ (continuous_eI k hk a δ _) _
      (coreData k hk a δ hδ ϕ φ hd ha hδa F i).hlam_cont)).absSummableAt_of_le
    (side_pos k _ δ hδ).le (by linarith [side_pos k (coreIdx i).1 δ hδ]) s

include hδ hd ha hδa in
theorem jet_abs_aux [∀ I : NonemptyIdx d, CompactSpace (KI k hk a δ I.1)] (i : Fin (numCores d))
    (s : KI k hk a δ (coreIdx i).1) :
    AbsSummableAt (jetFamily (nI (coreIdx i))
      ((NormalisedBox.core hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w) (locData k a ϕ φ hφint)
        rfl rfl rfl (coreData k hk a δ hδ ϕ φ hd ha hδa F i)).obsFibre s))
      (side k (coreIdx i).1 δ) := by
  have h := jetFamily_obsFibre hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData k a ϕ φ hφint) rfl rfl rfl (coreData k hk a δ hδ ϕ φ hd ha hδa F i) s
  exact (congrArg (fun f => AbsSummableAt f (side k (coreIdx i).1 δ)) h).mpr
    ((F (coreIdx i)).Fφ.absSummableAt_of_le (side_pos k _ δ hδ).le
      (by linarith [side_pos k (coreIdx i).1 δ hδ]) s)

include hδ hd ha hδa in
theorem datum_eq_aux [∀ I : NonemptyIdx d, CompactSpace (KI k hk a δ I.1)] (i : Fin (numCores d))
    (s : KI k hk a δ (coreIdx i).1) :
    toEta (side k (coreIdx i).1 δ)
      ((NormalisedBox.core hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w) (locData k a ϕ φ hφint)
        rfl rfl rfl (coreData k hk a δ hδ ϕ φ hd ha hδa F i)).x s) =
      CoeffFamily.conv (fun γ => J (coreIdx i).1 (eI k hk a δ (coreIdx i).1)
        (lamT k (coreIdx i).1 δ) s * (F (coreIdx i)).Fϕ.f s γ)
        (jetFamily (nI (coreIdx i))
          ((NormalisedBox.core hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
            (locData k a ϕ φ hφint) rfl rfl rfl
            (coreData k hk a δ hδ ϕ φ hd ha hδa F i)).obsFibre s)) := by
  have h := jetFamily_obsFibre hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData k a ϕ φ hφint) rfl rfl rfl (coreData k hk a δ hδ ϕ φ hd ha hδa F i) s
  have h1 := toEta_core_x hk (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData k a ϕ φ hφint) rfl rfl rfl (coreData k hk a δ hδ ϕ φ hd ha hδa F i) s
  exact h1.trans (congrArg (CoeffFamily.conv _) h.symm)

/-- ★★ **The coefficient certificate**: density family `J·fϕ`, observable jets `fφ`. -/
noncomputable def coeffCertificate :
    (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).CoefficientCertificate := by
  have := instK k hk a δ hδ
  exact {
    cc := fun i s γ =>
      J (coreIdx (d := d) i).1 (eI k hk a δ (coreIdx (d := d) i).1)
        (lamT k (coreIdx (d := d) i).1 δ) s * (F (coreIdx (d := d) i)).Fϕ.f s γ
    cc_abs := fun i s => cc_abs_aux k hk a δ hδ ϕ φ hd ha hδa F i s
    jet_abs := fun i s => jet_abs_aux k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F i s
    datum_eq := fun i s => datum_eq_aux k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F i s }

include hφm in
/-- ★★★ **The coordinate-free expansion of the compact box from local normal series**: for the
coordinate monomial phase on `[0,a]^d`, a measurable nonnegative prior and an observable given
near every nonempty coordinate stratum by uniform normal series, the original integral
`∫_{[0,a]^d} φ ϕ e^{−nK}` has the coordinate-free expansion with strata integrals over all
nonempty coordinate strata. -/
theorem hasCoordFreeExpansion_collar :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).stratumMeasure
      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).field
      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).cores.k)
        (commonD (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).n))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ :=
  (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).hasCoordFreeExpansion_le
    (measurable_phase d k) hϕm hϕ0 hφm

/-! ### The log degree of the collar -/

omit k hk a δ in
/-- The maximal normal dimension minus one over the collar is `d − 1`, attained at the deepest
stratum `I = univ`. -/
theorem commonD_collar (hd : 0 < d) :
    commonD (fun i : Fin (numCores d) => nI (coreIdx i)) = d - 1 := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    have h := Finset.card_le_univ (coreIdx i).1
    rw [Fintype.card_fin] at h
    exact Nat.sub_le_sub_right h 1
  · have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    unfold commonD
    have h := Finset.le_sup (f := fun i : Fin (numCores d) => nI (coreIdx i))
      (Finset.mem_univ ((coreIdx (d := d)).symm ⟨Finset.univ, hne⟩))
    simp only [Equiv.apply_symm_apply, nI, Finset.card_univ, Fintype.card_fin] at h
    exact h

include hφm in
/-- ★★★ The compact-box expansion with the explicit log degree `d − 1`: the spectrum is
`{(α, j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ d − 1}` for the cores' common lattice `Q`. -/
theorem hasCoordFreeExpansion_collar' :
    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
      (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).stratumMeasure
      (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).field
      (spectrumLe (commonQ (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).cores.k)
        (d - 1))
      (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ := by
  have h := hasCoordFreeExpansion_collar k hk a δ hδ ϕ φ hϕm hϕ0 hφm hφint hd ha hδa F
  have hD : commonD (certificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).n = d - 1 :=
    commonD_collar hd
  rwa [hD] at h

end WaterFilling

end Grammar
