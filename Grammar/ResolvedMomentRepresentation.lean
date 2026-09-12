/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedNormalData
import Grammar.GeometricMainTheorem
import Grammar.ChartNormalFamily

/-!
# The coordinate-free moment representation of the original integral (CCC)

Unit 4 of the coordinate-free programme (`tide-log/plan_coordinate_free_expansion.md`). The
library's conditional geometric main theorem
(`AdaptedStrataData.expectation_expansion_of_adaptedStrataData`) already writes a localised
resolved integral as a sum over pieces of base integrals of fibre Taylor–moment series, with the
pieces presented in box coordinates. This unit puts it on the resolved geometry of CCXCVIII–CCXCIX:

* `ResolvedCertificate R D W K ϕ φ` — the hypotheses of the final theorem: a localisation datum
  on the resolved space whose observable and phase are `φ∘π`, `K∘π` and whose measure pushes
  forward along `π` to the prior-weighted Lebesgue measure on `W` (`transport`); adapted strata
  data whose base spaces are the STRATA `S_I` of the resolved geometry, with normal-moment
  presentations (analytic fibre observables); and the compatibility of the box parametrisations
  with the tubular germs through linear frames `e_s : ℝ^{|I|} ≃ N_s` (`Φ_eq`). This is where the
  charts live; nothing below the line mentions them.
* `exactMoment I N s r : MomentTensor (N_s) r` — the exact normal fibre moment tensor
  `M̂_{I,r}(N)(s)`, the pushforward of the box fibre measure `c(s,u) u^h e^{−βN u^{2k}} du`
  along the frame; `pair_exactMoment_normalDifferential` identifies
  `⟨D^r_⊥(φ∘π)(s), M̂_{I,r}(N)(s)⟩` with the box moment pairing (frame covariance, no regularity
  needed).
* ★★★ `globalLaplace_eq_tsum_stratumContraction`: for `N ≥ 0`,
  `∫_W φ ϕ e^{−NK} = Σ_I ∫_{S_I} Σ'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), M̂_{I,r}(N)(s)⟩ dν_I(s) + tail(N)`
  with `|tail(N)| ≤ C e^{−δN}` — the paper's `eq:thm_coordfree` with the EXACT `n`-dependent
  moment tensors, for the ORIGINAL integral over `W`, with no coordinates in the statement.
* ★★ `cutoffExpansion_globalLaplace`: the original integral has the full power–log cutoff
  expansion with the assembled canonical coefficients `gCoeff` (`thm:expectation_expansion`,
  conditional form), and the moment series carries the same coefficients.

Not yet: the coefficient tensors `B_{I,r,α,j}` of the moment tensors' own asymptotics and the
termwise identity `gCoeff_{α,j} = Σ_I Σ'_r (1/r!) ∫ ⟨D^r_⊥, B_{I,r,α,j}⟩ dν_I` (the gates of units
9–10; normal order is not locally finite at tied crossings).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A]

/-- **A resolved certificate**: the localisation datum on the resolved space transporting the
original integral, adapted strata data on the strata with normal-moment presentations, and the
frames identifying the box parametrisations with the tubular germs. -/
structure ResolvedCertificate (R : ResolvedGeometry d U) (D : ResolvedNormalData R A)
    (W : Set (Fin d → ℝ)) (K ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- The localisation datum on the resolved space. -/
  L : LocalisationData U
  obs_eq : L.obs = φ ∘ R.π
  phase_eq : L.phase = K ∘ R.π
  /-- The resolved measure pushes forward to the prior-weighted Lebesgue measure on `W`. -/
  transport : L.μ.map R.π = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w)
  /-- The number of pieces. -/
  M : ℕ
  /-- The normal dimensions minus one. -/
  n : Fin M → ℕ
  /-- The stratum presented by each piece. -/
  strat : Fin M → Finset R.Component
  /-- The compact piece of the stratum carrying the base measure (the support of the adapted
  partition weight). -/
  base : ∀ I, Set (R.Stratum (strat I))
  isCompact_base : ∀ I, IsCompact (base I)
  /-- The inverse temperature of the normal form. -/
  β : ℝ
  β_pos : 0 < β
  /-- The adapted strata data, with the compact stratum pieces as base spaces. -/
  adapted : AdaptedStrataData L M (fun I => ↥(base I)) n β
  /-- The normal-moment presentations (analytic fibre observables). -/
  T : ∀ I, NormalMomentPresentation (adapted.chart I)
  /-- The frames `ℝ^{n_I+1} ≃ N_s` identifying box normal coordinates with the normal space. -/
  frame : ∀ I (s : ↥(base I)), (Fin (n I + 1) → ℝ) ≃L[ℝ] D.N (strat I) s.1
  /-- The box parametrisation is the tubular germ in the frame. -/
  Φ_eq : ∀ I (s : ↥(base I)) (u : Fin (n I + 1) → ℝ),
    (adapted.chart I).Φ (s, u) = D.Φ (strat I) s.1 (frame I s u)

namespace ResolvedCertificate

variable {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}
  (C : ResolvedCertificate R D W K ϕ φ)

instance (I : Fin C.M) : CompactSpace ↥(C.base I) := isCompact_iff_compactSpace.1
  (C.isCompact_base I)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The observable in the box fibre is the pulled-back observable through the tubular germ. -/
theorem obsFibre_eq (I : Fin C.M) (s : ↥(C.base I)) (u : Fin (C.n I + 1) → ℝ) :
    (C.adapted.chart I).obsFibre s u = φ (R.π (D.Φ (C.strat I) s.1 (C.frame I s u))) := by
  unfold ChartPresentation.obsFibre
  rw [C.obs_eq, C.Φ_eq]
  rfl

/-! ### The exact moment tensors -/

/-- The fibre measure transported to the normal space along the frame. -/
noncomputable def normalFibreMeasure (I : Fin C.M) (s : ↥(C.base I)) (N : ℝ) :
    Measure (D.N (C.strat I) s.1) :=
  ((C.adapted.chart I).fibreMeasure s N).map (C.frame I s : (Fin (C.n I + 1) → ℝ) →L[ℝ] _)

omit [T2Space U] [BorelSpace U] in
theorem integrable_norm_pow_normalFibreMeasure (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N)
    (s : ↥(C.base I)) (r : ℕ) :
    Integrable (fun ξ : D.N (C.strat I) s.1 => ‖ξ‖ ^ r) (C.normalFibreMeasure I s N) :=
  integrable_norm_pow_map' _ ((C.T I).integrable_norm_pow_fibre C.β_pos.le hN s r)

/-- **The exact moment tensor** `M̂_{I,r}(N)(s) : α ↦ ∫ α(ξ,…,ξ) dη_{s,N}` on the normal space. -/
noncomputable def exactMoment (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N) (s : ↥(C.base I))
    (r : ℕ) : MomentTensor (D.N (C.strat I) s.1) r :=
  normalMoment (fun s : ↥(C.base I) => D.N (C.strat I) s.1) (fun s => C.normalFibreMeasure I s N)
    (fun s => C.integrable_norm_pow_normalFibreMeasure I hN s r) s

omit [T2Space U] [BorelSpace U] in
/-- ★ **Frame covariance**: the pairing of the normal differential with the exact moment tensor is
the box moment pairing of the fibre observable. -/
theorem pair_exactMoment_normalDifferential (I : Fin C.M) {N : ℝ} (hN : 0 ≤ N)
    (s : ↥(C.base I)) (r : ℕ) :
    (C.exactMoment I hN s r).pair (D.normalDifferential φ (C.strat I) s.1 r) =
      ∫ u, normalJet ((C.adapted.chart I).obsFibre s) r (fun _ => u)
        ∂(C.adapted.chart I).fibreMeasure s N := by
  unfold exactMoment MomentTensor.pair
  rw [normalMoment_apply]
  unfold normalFibreMeasure
  have hm : Measurable (C.frame I s : (Fin (C.n I + 1) → ℝ) →L[ℝ] D.N (C.strat I) s.1) :=
    (C.frame I s : (Fin (C.n I + 1) → ℝ) →L[ℝ] D.N (C.strat I) s.1).continuous.measurable
  rw [integral_map hm.aemeasurable (continuous_diagEval _).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have h := rawNormalJet_comp_equiv (D.N (C.strat I)) (D.Φ (C.strat I)) (φ ∘ R.π) s.1
    (C.frame I s) r
  have hfun : (fun v : Fin (C.n I + 1) → ℝ => (φ ∘ R.π) (D.Φ (C.strat I) s.1 (C.frame I s v))) =
      (C.adapted.chart I).obsFibre s := by
    funext v
    rw [C.obsFibre_eq]
    rfl
  rw [hfun] at h
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential
  change (rawNormalJet (D.N (C.strat I)) (D.Φ (C.strat I)) (φ ∘ R.π) s.1 r)
    (fun _ => (C.frame I s : (Fin (C.n I + 1) → ℝ) →L[ℝ] D.N (C.strat I) s.1) u) = _
  rw [← ContinuousMultilinearMap.compContinuousLinearMap_apply, ← h]
  rfl

/-! ### The transport of the original integral -/

variable (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w) (hφ : Measurable φ)

omit [T2Space U] [MeasurableSpace A] [BorelSpace A] in
include hK hϕ hϕ0 hφ in
/-- **The original integral is the resolved integral**: `∫_W φ ϕ e^{−NK} = Z_L(N)`. -/
theorem globalLaplace_eq_Z (N : ℝ) :
    globalLaplace W K (fun w => φ w * ϕ w) N = C.L.Z N := by
  unfold globalLaplace LocalisationData.Z LocalisationData.integrand
  rw [C.obs_eq, C.phase_eq]
  simp only [Function.comp_apply]
  have h := integral_exp_eq_of_map (μX := (volume.restrict W).withDensity
      fun w => ENNReal.ofReal (ϕ w)) (μU := C.L.μ) (π := R.π) R.continuous_π.measurable
    C.transport (K := K) (F := φ) hK hφ.aestronglyMeasurable N
  rw [← h, integral_withDensity_eq_integral_toReal_smul hϕ.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (hϕ0 w), smul_eq_mul]
  ring

omit [T2Space U] in
include hK hϕ hϕ0 hφ in
/-- ★★★ **The coordinate-free moment representation of the original integral**: for `N ≥ 0`,
`∫_W φ ϕ e^{−NK} = Σ_I ∫_{S_I} Σ'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), M̂_{I,r}(N)(s)⟩ dν_I(s) + tail(N)`.
Only the strata, the normal differentials, the exact moment tensors, the stratum densities and
`π` occur. -/
theorem globalLaplace_eq_tsum_stratumContraction {N : ℝ} (hN : 0 ≤ N) :
    globalLaplace W K (fun w => φ w * ϕ w) N =
      ∑ I, (∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
        (C.exactMoment I hN s r).pair (D.normalDifferential φ (C.strat I) s.1 r) ∂C.adapted.ν I) +
      C.adapted.tail N := by
  rw [C.globalLaplace_eq_Z hK hϕ hϕ0 hφ N, C.adapted.Z_eq_moment_series C.T C.β_pos.le hN]
  congr 1
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae (Eventually.of_forall fun s => ?_)
  refine tsum_congr fun r => ?_
  rw [C.pair_exactMoment_normalDifferential I hN s r]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- **The tail is exponentially small.** -/
theorem abs_tail_le {N : ℝ} (hN : 0 ≤ N) :
    |C.adapted.tail N| ≤ (∫ z, |C.L.obs z| ∂C.L.μ) * Real.exp (-C.L.δ * N) :=
  C.adapted.tail_bound hN

omit [MeasurableSpace A] [BorelSpace A] in
include hK hϕ hϕ0 hφ in
/-- ★★ **The full power–log cutoff expansion of the original integral** with the assembled
canonical coefficients (`thm:expectation_expansion`, conditional form). -/
theorem cutoffExpansion_globalLaplace :
    CutoffExpansion (commonQ C.adapted.k) (commonD C.n) (globalLaplace W K fun w => φ w * ϕ w)
      (gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x) := by
  have h := C.adapted.cutoffExpansion C.β_pos
  have heq : (globalLaplace W K fun w => φ w * ϕ w) = C.L.Z :=
    funext fun N => C.globalLaplace_eq_Z hK hϕ hϕ0 hφ N
  rwa [heq]

omit [MeasurableSpace A] [BorelSpace A] in
/-- **The moment series carries the same canonical coefficients.** -/
theorem cutoffExpansion_stratumContraction :
    CutoffExpansion (commonQ C.adapted.k) (commonD C.n)
      (fun N => ∑ I, ∫ s, ∑' r : ℕ, (r.factorial : ℝ)⁻¹ *
        ∫ u, normalJet ((C.adapted.chart I).obsFibre s) r (fun _ => u)
          ∂(C.adapted.chart I).fibreMeasure s N ∂C.adapted.ν I)
      (gCoeff C.adapted.ν C.adapted.h C.adapted.k C.β C.adapted.b C.adapted.x) :=
  C.adapted.momentSeries_cutoffExpansion C.T C.β_pos

end ResolvedCertificate

end Grammar
