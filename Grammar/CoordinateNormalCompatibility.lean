/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxInputs

/-!
# Coordinate normal compatibility (CCCXXVI)

Consult #97 §2: the FIRST compatibility slice, an exact coordinate specialisation rather than a
general SNC compatibility object. `CoordinateNormalCompatibility` connects, for a stratum `S_I` of
the coordinate model with ambient coordinates: the base points `base s` (normal coordinates zero,
tangential coordinates `e s`), the normal space `N` with its inclusion `inc` and the coordinate
conormals `du_j = inc(·)_j`, the fixed tubular map `tube s ξ = base s + inc ξ`, and the chosen
frame `frame s : ℝ^{n+1} ≃L N` whose conormal pairings are DIAGONAL with scale `λ_j(e s)`
(`frame_conormal`; `du_frame_single`: the diagonal entry is `λ_i(s)`, not `1`).

Consequences (theorems, not fields): the tubular parametrisation along the frame IS the normalised
box parametrisation (`tube_frame_eq_normalisedBox`), the phase along it is the normalised monomial
(`phase_tube_frame`), and — the CONSTRUCTIVE consumer — tubular-frame series together with the box
geometry packet `CoordinateBoxBounds` build a core presentation WITHOUT assuming transport or the
phase normal form (`produceCore_of_coordinateCompat`, `producePresentation`), whose observable
fibre is `φ ∘ tube_s ∘ frame_s` (`obsFibre_produceCore`, the acceptance test of consult #97 §2.5).
The water-filling certificate of CCCXXIV instantiates the structure (`waterFillingCompat`), with
`tube_frame_eq_normalisedBox` reproducing `Φ_eq_frame`.

The fixed-germ derivative consumer (normal jets of the fibre observable through the frame) is the
next unit. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open NormalisedBox CoeffFamily

/-- **Coordinate normal compatibility** at a stratum `S_I`: base points, normal space with
coordinate conormals, the fixed tubular map and a diagonal frame with scale `λ(e s)`. -/
structure CoordinateNormalCompatibility {d n : ℕ} (I : Finset (Fin d)) (K N : Type*)
    [NormedAddCommGroup N] [NormedSpace ℝ N] (base : K → (Fin d → ℝ)) (e : K → (Tan I → ℝ))
    (inc : N →L[ℝ] (Fin d → ℝ)) (du : Nrm I → (N →L[ℝ] ℝ)) (tube : K → N → (Fin d → ℝ))
    (lamT : (Tan I → ℝ) → (Nrm I → ℝ)) where
  /-- box coordinates ↔ the labels of the normal coordinates -/
  label : Fin (n + 1) ≃ Nrm I
  /-- the frame at each base point -/
  frame : K → ((Fin (n + 1) → ℝ) ≃L[ℝ] N)
  base_normal : ∀ s (j : Nrm I), base s j.1 = 0
  base_tangent : ∀ s (j : Tan I), base s j.1 = e s j
  inc_tangent : ∀ ξ (j : Tan I), inc ξ j.1 = 0
  du_coordinate : ∀ ξ (j : Nrm I), du j ξ = inc ξ j.1
  tubular_eq : ∀ s ξ, tube s ξ = base s + inc ξ
  frame_conormal : ∀ s u (j : Nrm I), du j (frame s u) = lamT (e s) j * u (label.symm j)

namespace CoordinateNormalCompatibility

variable {d n : ℕ} {I : Finset (Fin d)} {K N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  {base : K → (Fin d → ℝ)} {e : K → (Tan I → ℝ)} {inc : N →L[ℝ] (Fin d → ℝ)}
  {du : Nrm I → (N →L[ℝ] ℝ)} {tube : K → N → (Fin d → ℝ)} {lamT : (Tan I → ℝ) → (Nrm I → ℝ)}
  (C : CoordinateNormalCompatibility (n := n) I K N base e inc du tube lamT)

/-- The frame scale `λ_i(s)` in box coordinates. -/
def frameScale (s : K) (i : Fin (n + 1)) : ℝ := lamT (e s) (C.label i)

/-- The conormal pairings of the frame are diagonal with scale `λ_i(s)`. -/
theorem du_frame_single (s : K) (i j : Fin (n + 1)) :
    du (C.label i) (C.frame s (Pi.single j 1)) = if i = j then C.frameScale s i else 0 := by
  rw [C.frame_conormal, Equiv.symm_apply_apply, Pi.single_apply, frameScale]
  split_ifs with h <;> simp [h]

/-- ★ **The tubular parametrisation along the frame is the normalised box parametrisation.** -/
theorem tube_frame_eq_normalisedBox (s : K) (u : Fin (n + 1) → ℝ) :
    tube s (C.frame s u) = Φ I C.label e lamT (s, u) := by
  funext j
  rw [C.tubular_eq, Pi.add_apply, Φ_apply]
  by_cases hj : j ∈ I
  · rw [dif_pos hj, C.base_normal s ⟨j, hj⟩, zero_add, ← C.du_coordinate _ ⟨j, hj⟩,
      C.frame_conormal]
  · rw [dif_neg hj, C.inc_tangent _ ⟨j, hj⟩, add_zero, C.base_tangent s ⟨j, hj⟩]

/-- The phase along the tubular frame is the normalised monomial times the tangential unit. -/
theorem phase_tube_frame (k : Fin d → ℕ) (s : K) (u : Fin (n + 1) → ℝ) :
    CoordModel.phase d k (tube s (C.frame s u)) =
      (tanUnit k I (e s) * ∏ j : Nrm I, lamT (e s) j ^ (2 * k j.1)) *
        ∏ i, u i ^ (2 * kι k I C.label i) := by
  rw [C.tube_frame_eq_normalisedBox, phase_Φ]

end CoordinateNormalCompatibility

/-! ### The constructive consumer -/

namespace CoordinateNormalCompatibility

variable {d n : ℕ} (k : Fin d → ℕ) {I : Finset (Fin d)} {K N : Type*} [NormedAddCommGroup N]
  [NormedSpace ℝ N] {base : K → (Fin d → ℝ)} {e : K → (Tan I → ℝ)} {inc : N →L[ℝ] (Fin d → ℝ)}
  {du : Nrm I → (N →L[ℝ] ℝ)} {tube : K → N → (Fin d → ℝ)} {lamT : (Tan I → ℝ) → (Nrm I → ℝ)}
  [TopologicalSpace K] (W : Set (Fin d → ℝ))

/-- The box geometry packet: the remaining analytic/measurable fields of `NormalisedBox.Data`
(continuity, injectivity, positivity, the normalisation identity, the box sides, the image
bound). -/
structure BoxBounds where
  he : Continuous e
  he_inj : Function.Injective e
  hlamT : Measurable lamT
  hlam_cont : ContinuousOn lamT (range e)
  hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j
  β : ℝ
  hnorm : ∀ t ∈ range e, tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β
  b : ℝ
  b' : ℝ
  hb : 0 < b
  hbb' : b < b'
  hW : NormalisedBox.image I e lamT b ⊆ W

variable (ϕ φ : (Fin d → ℝ) → ℝ)
  (C : CoordinateNormalCompatibility (n := n) I K N base e inc du tube lamT)
  (B : BoxBounds k (e := e) (lamT := lamT) W)

/-- Series for the prior and the observable stated in TUBULAR-FRAME notation
`φ(tube_s(frame_s u))`. -/
structure TubularFrameSeries where
  Fϕ : UniformSeriesFamily K (n + 1) B.b'
  Fφ : UniformSeriesFamily K (n + 1) B.b'
  hϕ_eq : ∀ s, ∀ u ∈ NormalisedBox.box (ι := Fin (n + 1)) B.b,
    ϕ (tube s (C.frame s u)) = evalF (Fϕ.f s) u
  hφ_eq : ∀ s (u : Fin (n + 1) → ℝ), ‖u‖ < B.b' → φ (tube s (C.frame s u)) = evalF (Fφ.f s) u

variable (A : TubularFrameSeries k W ϕ φ C B)

/-- The normalised box data from compatibility, box geometry and tubular-frame series. -/
noncomputable def toNormalisedBoxData : NormalisedBox.Data k I n K W ϕ φ where
  σ := C.label
  e := e
  he := B.he
  he_inj := B.he_inj
  lamT := lamT
  hlamT := B.hlamT
  hlam_cont := B.hlam_cont
  hpos := B.hpos
  β := B.β
  hnorm := B.hnorm
  b := B.b
  b' := B.b'
  hb := B.hb
  hbb' := B.hbb'
  hW := B.hW
  Fϕ := A.Fϕ
  Fφ := A.Fφ
  hϕ_eq := fun s u hu => by rw [← C.tube_frame_eq_normalisedBox]; exact A.hϕ_eq s u hu
  hφ_eq := fun s u hu => by rw [← C.tube_frame_eq_normalisedBox]; exact A.hφ_eq s u hu

variable (hk : ∀ i, 0 < k i) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (hWm : MeasurableSet W) (hϕm : Measurable ϕ) (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w)
  (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ)

/-- ★★ **The constructive consumer**: a core presentation from compatibility, box geometry and
tubular-frame series — its inputs contain neither a core, nor a transport proof, nor a phase
normal form, nor a coefficient certificate. -/
noncomputable def produceCore_of_coordinateCompat :
    CorePresentation L (L.μ.restrict (NormalisedBox.image I e lamT B.b)) K n B.β :=
  NormalisedBox.core hk hWm hϕm hϕ0 L hLμ hLphase hLobs (toNormalisedBoxData k W ϕ φ C B A)

/-- The normal-moment presentation of the produced core. -/
noncomputable def producePresentation :
    CoreNormalMomentPresentation
      (produceCore_of_coordinateCompat k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase hLobs) :=
  NormalisedBox.presentation hk hWm hϕm hϕ0 L hLμ hLphase hLobs (toNormalisedBoxData k W ϕ φ C B A)

/-- Acceptance test (consult #97 §2.5): the observable fibre of the produced core is
`φ ∘ tube_s ∘ frame_s`. -/
theorem obsFibre_produceCore (s : K) (u : Fin (n + 1) → ℝ) :
    (produceCore_of_coordinateCompat k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase
      hLobs).obsFibre s u = φ (tube s (C.frame s u)) :=
  (NormalisedBox.core_obsFibre hk hWm hϕm hϕ0 L hLμ hLphase hLobs
    (toNormalisedBoxData k W ϕ φ C B A) s u).trans
    (congrArg φ (C.tube_frame_eq_normalisedBox s u).symm)

/-- The Taylor family of the produced fibre observable is the observable's series family. -/
theorem jetFamily_produceCore (s : K) :
    jetFamily n ((produceCore_of_coordinateCompat k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase
      hLobs).obsFibre s) = A.Fφ.f s :=
  NormalisedBox.jetFamily_obsFibre hk hWm hϕm hϕ0 L hLμ hLphase hLobs _ s

end CoordinateNormalCompatibility

/-! ### The fixed-germ derivative consumer -/

section FixedGerm

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
  [NormedSpace ℝ N]

/-- Iterated derivatives at `0` of `G ∘ F` for a continuous linear equivalence `F` and a function
`G` analytic on an open neighbourhood of `0`: `D^r(G∘F)(0) = D^rG(0) ∘ (F, …, F)`. -/
theorem iteratedFDeriv_comp_cle_zero (F : E ≃L[ℝ] N) {G : N → ℝ} {s : Set N} (hs : IsOpen s)
    (h0 : (0 : N) ∈ s) (hG : AnalyticOnNhd ℝ G s) (r : ℕ) :
    iteratedFDeriv ℝ r (fun u => G (F u)) 0 =
      (iteratedFDeriv ℝ r G 0).compContinuousLinearMap fun _ => (F : E →L[ℝ] N) := by
  have hF0 : (F : E →L[ℝ] N) 0 = 0 := map_zero _
  have hs' : IsOpen ((F : E →L[ℝ] N) ⁻¹' s) := hs.preimage (F : E →L[ℝ] N).continuous
  have h0' : (0 : E) ∈ (F : E →L[ℝ] N) ⁻¹' s := by
    rw [mem_preimage, hF0]
    exact h0
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (F : E →L[ℝ] N)
    (hG.contDiffOn (n := ⊤) hs.uniqueDiffOn) hs.uniqueDiffOn hs'.uniqueDiffOn (x := 0)
    (by rw [hF0]; exact h0) (le_top (a := (r : WithTop ℕ∞)))
  rw [iteratedFDerivWithin_of_isOpen r hs' h0', iteratedFDerivWithin_of_isOpen r hs
    (by rw [hF0]; exact h0), hF0] at h
  exact h

/-- The normal jets of `G ∘ F` from a series identity on the ball: if `G (F u) = evalF f u` for
`‖u‖ < b'` with `f` a `b'`-weighted ℓ¹ family, then
`normalJet (G ∘ F) r = normalJet G r ∘ (F,…,F)`. -/
theorem normalJet_comp_cle_of_series {n : ℕ} (F : (Fin (n + 1) → ℝ) ≃L[ℝ] N) (G : N → ℝ)
    {f : CoeffFamily (n + 1)} {b' : ℝ} (hb' : 0 < b') (hf : AbsSummableAt f b')
    (heq : ∀ u : Fin (n + 1) → ℝ, ‖u‖ < b' → G (F u) = evalF f u) (r : ℕ) :
    normalJet (fun u => G (F u)) r =
      (normalJet G r).compContinuousLinearMap fun _ => (F : (Fin (n + 1) → ℝ) →L[ℝ] N) := by
  have hball : HasFPowerSeriesOnBall (fun u => G (F u)) (polySeriesD f) 0 (ENNReal.ofReal b') :=
    (hasFPowerSeriesOnBall_evalF f hb' hf).congr fun u hu => by
      rw [Metric.eball_ofReal, Metric.mem_ball, dist_zero_right] at hu
      exact (heq u hu).symm
  have h1 : AnalyticOnNhd ℝ (fun u => G (F u)) (Metric.ball 0 b') := by
    have := hball.analyticOnNhd
    rwa [Metric.eball_ofReal] at this
  have hopen : IsOpen (F '' Metric.ball (0 : Fin (n + 1) → ℝ) b') :=
    F.isOpenMap _ Metric.isOpen_ball
  have h0 : (0 : N) ∈ F '' Metric.ball (0 : Fin (n + 1) → ℝ) b' :=
    ⟨0, Metric.mem_ball_self hb', map_zero _⟩
  have hG : AnalyticOnNhd ℝ G (F '' Metric.ball 0 b') := by
    have h2 : AnalyticOnNhd ℝ ((fun u => G (F u)) ∘ (F.symm : N →L[ℝ] (Fin (n + 1) → ℝ)))
        (F '' Metric.ball 0 b') :=
      h1.comp ((F.symm : N →L[ℝ] (Fin (n + 1) → ℝ)).analyticOnNhd _) fun ξ hξ => by
        obtain ⟨u, hu, rfl⟩ := hξ
        simpa using hu
    refine h2.congr hopen ?_
    rintro ξ ⟨u, -, rfl⟩
    simp
  unfold normalJet
  exact iteratedFDeriv_comp_cle_zero F hopen h0 hG r

end FixedGerm

namespace CoordinateNormalCompatibility

variable {d n : ℕ} (k : Fin d → ℕ) {I : Finset (Fin d)} {K N : Type*} [NormedAddCommGroup N]
  [NormedSpace ℝ N] {base : K → (Fin d → ℝ)} {e : K → (Tan I → ℝ)} {inc : N →L[ℝ] (Fin d → ℝ)}
  {du : Nrm I → (N →L[ℝ] ℝ)} {tube : K → N → (Fin d → ℝ)} {lamT : (Tan I → ℝ) → (Nrm I → ℝ)}
  [TopologicalSpace K] (W : Set (Fin d → ℝ)) (ϕ φ : (Fin d → ℝ) → ℝ)
  (C : CoordinateNormalCompatibility (n := n) I K N base e inc du tube lamT)
  (B : BoxBounds k (e := e) (lamT := lamT) W) (A : TubularFrameSeries k W ϕ φ C B)
  (hk : ∀ i, 0 < k i) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (hWm : MeasurableSet W) (hϕm : Measurable ϕ) (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w)
  (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ)

/-- ★ **Fixed-germ interpretation**: the normal jets of the produced fibre observable are the jets
of the fixed normal germ `G_s = φ ∘ tube_s` pulled back along the frame — no derivative in the
base point and none of the frame scale occurs. -/
theorem normalJet_produceCore (s : K) (r : ℕ) :
    normalJet ((produceCore_of_coordinateCompat k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase
      hLobs).obsFibre s) r =
      (normalJet (fun ξ => φ (tube s ξ)) r).compContinuousLinearMap
        fun _ => (C.frame s : (Fin (n + 1) → ℝ) →L[ℝ] N) := by
  have hfib : (produceCore_of_coordinateCompat k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase
      hLobs).obsFibre s = fun u => φ (tube s (C.frame s u)) :=
    funext fun u => obsFibre_produceCore k W ϕ φ C B A hk hWm hϕm hϕ0 L hLμ hLphase hLobs s u
  rw [hfib]
  exact normalJet_comp_cle_of_series (C.frame s) (fun ξ => φ (tube s ξ)) (B.hb.trans B.hbb')
    (A.Fφ.absSummableAt (B.hb.trans B.hbb').le s) (fun u hu => A.hφ_eq s u hu) r

end CoordinateNormalCompatibility

/-! ### The coordinate instance on the water-filling certificate -/

namespace WaterFilling

open CoordModel

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (a δ : ℝ) (hδ : 0 < δ)

/-- The inclusion of the normal space `N_I ⊆ ℝ^d` (Euclidean → plain coordinates). -/
noncomputable def normalInc (I : Finset (Fin d)) : normalSpace d I →L[ℝ] (Fin d → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : Amb d →L[ℝ] (Fin d → ℝ)).comp
    (normalSpace d I).subtypeL

theorem normalInc_apply (I : Finset (Fin d)) (ξ : normalSpace d I) (j : Fin d) :
    normalInc I ξ j = (ξ : Amb d).ofLp j := rfl

/-- The coordinate conormals as continuous linear functionals. -/
noncomputable def normalDu (I : Finset (Fin d)) (j : Nrm I) : normalSpace d I →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (CoordModel.du d I j)

theorem normalDu_apply (I : Finset (Fin d)) (j : Nrm I) (ξ : normalSpace d I) :
    normalDu I j ξ = (ξ : Amb d).ofLp j.1 := rfl

/-- Vectors of `N_I` have vanishing tangential coordinates. -/
theorem ofLp_eq_zero_of_notMem (I : Finset (Fin d)) (ξ : normalSpace d I) {j : Fin d} (hj : j ∉ I) :
    (ξ : Amb d).ofLp j = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ξ.2
  rw [← hc, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp, if_neg, mul_zero]
  exact fun h => hj (h ▸ i.2)

/-- ★ **The water-filling certificate is coordinate-normal compatible**: bases in the strata,
the coordinate normal space and conormals, the coordinate model's tubular germ `s + ξ`, and the
diagonal frames `frameI`. -/
noncomputable def waterFillingCompat (I : NonemptyIdx d) :
    CoordinateNormalCompatibility (n := nI I) I.1 (KI k hk a δ I.1) (normalSpace d I.1)
      (fun s => s.1.1) (eI k hk a δ I.1) (normalInc I.1) (normalDu I.1)
      (fun s ξ => (normalData d k (zeroOrders d) hk).Φ I.1 s.1 ξ) (lamT k I.1 δ) where
  label := σI I
  frame := frameI k hk a δ hδ I
  base_normal := fun s j => stratum_coord_zero k hk s.1 j.2
  base_tangent := fun _ _ => rfl
  inc_tangent := fun ξ j => ofLp_eq_zero_of_notMem I.1 ξ j.2
  du_coordinate := fun _ _ => rfl
  tubular_eq := fun s ξ => by
    rw [normalData_Φ]
    funext j
    rfl
  frame_conormal := fun s u j => by
    rw [normalDu_apply, coe_frameI_apply, dif_pos j.2]

/-- The generic tubular identity reproduces `Φ_eq_frame` on the water-filling certificate. -/
theorem waterFillingCompat_tube_frame (I : NonemptyIdx d) (s : KI k hk a δ I.1)
    (u : Fin (nI I + 1) → ℝ) :
    (normalData d k (zeroOrders d) hk).Φ I.1 s.1 (frameI k hk a δ hδ I s u) =
      Φ I.1 (σI I) (eI k hk a δ I.1) (lamT k I.1 δ) (s, u) :=
  (waterFillingCompat k hk a δ hδ I).tube_frame_eq_normalisedBox s u

variable (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ) (hϕ0 : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
  (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ) (hd : 0 < d) (ha : 0 < a)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (F : ∀ I : NonemptyIdx d, FaceSeries k hk a δ ϕ φ I)

/-- ★★ **The chart jets are the coordinate-free normal differentials pulled back along the
frame**: for every core of the water-filling certificate,
`normalJet (obsFibre_s) r = D^r_⊥(φ∘π)(s) ∘ (frameI s, …, frameI s)`. -/
theorem normalJet_stratumCore_eq_normalDifferential (i : Fin (numCores d))
    (s : KI k hk a δ (coreIdx i).1) (r : ℕ) :
    have := instK k hk a δ hδ
    normalJet ((stratumCore k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs
      (stratumInputs k hk a δ hδ ϕ φ F) (coreIdx i)).obsFibre s) r =
      ((normalData d k (zeroOrders d) hk).normalDifferential φ (coreIdx i).1 s.1
        r).compContinuousLinearMap fun _ => (frameI k hk a δ hδ (coreIdx i) s :
          (Fin (nI (coreIdx i) + 1) → ℝ) →L[ℝ] normalSpace d (coreIdx i).1) := by
  intro _
  have hfib : (stratumCore k a δ hk hd ha hδ hδa hϕm hϕ0 L hLμ hLphase hLobs
      (stratumInputs k hk a δ hδ ϕ φ F) (coreIdx i)).obsFibre s =
      fun u => φ ((normalData d k (zeroOrders d) hk).Φ (coreIdx i).1 s.1
        (frameI k hk a δ hδ (coreIdx i) s u)) := by
    funext u
    exact (NormalisedBox.core_obsFibre hk (measurableSet_W a) hϕm hϕ0 L hLμ hLphase hLobs
      ((stratumInputs k hk a δ hδ ϕ φ F (coreIdx i)).toData k a δ hk hd ha hδ hδa
        (coreIdx i).2) s u).trans (congrArg φ (Φ_eq_frame k hk a δ hδ (coreIdx i) s u))
  rw [hfib]
  exact normalJet_comp_cle_of_series (frameI k hk a δ hδ (coreIdx i) s)
    (fun ξ => φ ((normalData d k (zeroOrders d) hk).Φ (coreIdx i).1 s.1 ξ))
    (by linarith [side_pos k (coreIdx i).1 δ hδ])
    ((F (coreIdx i)).Fφ.absSummableAt (by linarith [side_pos k (coreIdx i).1 δ hδ]) s)
    (fun u hu => by
      rw [← Φ_eq_frame k hk a δ hδ (coreIdx i) s u]
      exact (F (coreIdx i)).hφ_eq s u hu) r

end WaterFilling

end Grammar
