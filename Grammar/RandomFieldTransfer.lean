/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.GraphLawTransfer
import Grammar.PhaseSpace

/-!
# Random spatial phases: the finite-observable transfer

Let the random phases `X_m` have laws `μ_m` on the Polish space `C(K, ℝ)` with `μ_m ⇒ μ₀`, and
let `g_1, …, g_r` be bounded continuous tests on `ℝ × ℝ^d`.  With
`T_m(p) = (∫ g_i dQ_{N_m}(ext p))_i`
the finite-`N` conditional observables and `T(p) = (∫ g_i dQ̃(ext p))_i` their limits,

  `(X_m, T_m(X_m)) ⇒ (X, T(X))`

as laws on `C(K, ℝ) × ℝ^r` (`randomField_graphLaw_tendsto`): the deterministic moving-phase theorem
gives arbitrary-index sequential convergence of `T_m`, the sequential bridge upgrades it to
continuous convergence, and the graph-law transfer on the Polish phase space finishes.
Corollaries: the limit map `T` is continuous (`continuous_limitObservable`); the observable laws
converge (`randomField_observable_tendsto`); and the mixed annealed identity
`∫ φ(p) (∫ g dQ_{N_m}(ext p)) dμ_m(p) → ∫ φ(p) (∫ g dQ̃(ext p)) dμ₀(p)` for bounded continuous `φ`
(`randomField_annealed_tendsto`, by clipping the output coordinate to `[−‖g‖, ‖g‖]`).

Not claimed: almost-sure quenched convergence, stable convergence, or the joint law of the
environment together with a posterior draw.  The phase convergence `μ_m ⇒ μ₀` in `C(K, ℝ)` is an
external input (a scalar CLT for `X_m(0)` is not sufficient).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open BoundedContinuousFunction

section deterministic

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop) {r : ℕ}
  (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)

include hk hβ hηc hηnn hmin hatt hW hN1 hN in
/-- **Continuous convergence of the observable vectors**: `T_m → T` continuously on `C(K, ℝ)`. -/
theorem phaseObservable_continuouslyConverges :
    ContinuouslyConverges (fun m => phaseObservable n h k β (Nseq m) η g)
      (limitObservable h k l β η g) :=
  continuouslyConverges_of_seq fun p κ x hκ hx =>
    phaseObservable_tendsto_seq n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN g κ hκ x p hx

include hk hβ hηc hηnn hmin hatt hW in
/-- **Continuity of the limiting observables** `p ↦ (∫ g_i dQ̃(ext p))_i` on `C(K, ℝ)`. -/
theorem continuous_limitObservable : Continuous (limitObservable h k l β η g) :=
  (phaseObservable_continuouslyConverges n h k hk hβ hηc hηnn hmin hatt hW
    (fun m => (m : ℝ) + 2) (fun m => by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop) g).continuous_limit

end deterministic

section random

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u)
  (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop) {r : ℕ}
  (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)
  {μ : ℕ → ProbabilityMeasure C(PhaseDomain n, ℝ)} {μ₀ : ProbabilityMeasure C(PhaseDomain n, ℝ)}
  (hμ : Tendsto μ atTop (𝓝 μ₀))

include hk hβ hηc hηnn hmin hatt hW hN1 hN hμ in
/-- **Random-field finite-observable transfer**: if the random phases converge in law,
`X_m ⇒ X` in `C(K, ℝ)`, then jointly `(X_m, T_m(X_m)) ⇒ (X, T(X))`, where `T_m(p)` is the vector of
`Q_{N_m}(ext p)`-expectations of `g_1, …, g_r` and `T(p)` the vector of `Q̃(ext p)`-expectations. -/
theorem randomField_graphLaw_tendsto :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_phaseObservable n h k (Nseq m) hβ.le hηc hηnn hW g)) atTop
      (𝓝 (graphLaw μ₀
        (continuous_limitObservable n h k hk hβ hηc hηnn hmin hatt hW g).measurable)) :=
  tendsto_graphLaw_of_polish hμ
    (fun m => measurable_phaseObservable n h k (Nseq m) hβ.le hηc hηnn hW g)
    (phaseObservable_continuouslyConverges n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN g)

include hk hβ hηc hηnn hmin hatt hW hN1 hN hμ in
/-- The laws of the conditional observables converge: `T_m(X_m) ⇒ T(X)`. -/
theorem randomField_observable_tendsto :
    Tendsto (fun m => (μ m).map
        (measurable_phaseObservable n h k (Nseq m) hβ.le hηc hηnn hW g).aemeasurable) atTop
      (𝓝 (μ₀.map (continuous_limitObservable n h k hk hβ hηc hηnn hmin hatt hW
        g).measurable.aemeasurable)) := by
  have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (randomField_graphLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN g hμ)
    (continuous_snd (X := C(PhaseDomain n, ℝ)) (Y := Fin r → ℝ))
  have hmap : ∀ (ν : ProbabilityMeasure C(PhaseDomain n, ℝ)) {S : C(PhaseDomain n, ℝ) → Fin r → ℝ}
      (hS : Measurable S), (graphLaw ν hS).map (continuous_snd.measurable.aemeasurable) =
        ν.map hS.aemeasurable := fun ν S hS => by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, graphLaw]
    rw [Measure.map_map measurable_snd (measurable_id.prodMk hS)]
    rfl
  simpa only [hmap] using this

end random

/-! ### The mixed annealed corollary -/

/-- Clipping to `[−c, c]`. -/
def clipTo (c t : ℝ) : ℝ := max (-c) (min c t)

theorem clipTo_of_abs_le {c t : ℝ} (h : |t| ≤ c) : clipTo c t = t := by
  unfold clipTo
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

theorem continuous_clipTo (c : ℝ) : Continuous (clipTo c) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clipTo_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |clipTo c t| ≤ c :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

section annealed

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
  {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v)
  {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hW : 0 < ∫ u in unitBox (n + 1), faceWeight h k l η u) {r : ℕ}
  (g : Fin r → (ℝ × (Fin (n + 1) → ℝ)) →ᵇ ℝ)

include hβ hηc hηnn hW in
theorem abs_phaseObservable_le (N : ℝ) (p : C(PhaseDomain n, ℝ)) (i : Fin r) :
    |phaseObservable n h k β N η g p i| ≤ ‖g i‖ := by
  haveI := phaseJointLaw_isProbabilityMeasure n h k N hβ.le (continuous_extPhase p) hηc
    (fun u hu => hηnn u (unitBox_subset_closedCube _ hu))
    (origPhaseIntegral_pos n h k β N hηc hηnn hW (continuous_extPhase p))
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_norm _ (g i)

include hk hβ hηc hηnn hmin hatt hW in
theorem abs_limitObservable_le (p : C(PhaseDomain n, ℝ)) (i : Fin r) :
    |limitObservable h k l β η g p i| ≤ ‖g i‖ := by
  have hl0 : 0 < l := ratioExp_min_pos h k hk hatt
  haveI := spatialJointFaceLaw_isProbabilityMeasure h k hk hl0 hβ hmin (continuous_extPhase p) hηc
    hηnn (spatialMass_pos_of_face h k hk l β _ η (spatialFace_pos_of_faceWeight h k hk hl0 hβ hmin
      (continuous_extPhase p) hηc hηnn hW))
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_norm _ (g i)

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
  {μ : ℕ → ProbabilityMeasure C(PhaseDomain n, ℝ)} {μ₀ : ProbabilityMeasure C(PhaseDomain n, ℝ)}
  (hμ : Tendsto μ atTop (𝓝 μ₀))

include hk hβ hηc hηnn hmin hatt hW hN1 hN hμ in
/-- **Mixed annealed identity**: for bounded continuous `φ` on the phase space,
`∫ φ(p) E_{Q_{N_m}(ext p)}[g_i] dμ_m(p) → ∫ φ(p) E_{Q̃(ext p)}[g_i] dμ₀(p)`.  Proof: the graph-law
theorem applied to the bounded continuous test `(p, v) ↦ φ(p) · clip_{‖g_i‖}(v_i)`; the clipping is
the identity on the observables since `|E[g_i]| ≤ ‖g_i‖`. -/
theorem randomField_annealed_tendsto (φ : C(PhaseDomain n, ℝ) →ᵇ ℝ) (i : Fin r) :
    Tendsto (fun m => ∫ p, φ p * phaseObservable n h k β (Nseq m) η g p i ∂(μ m : Measure _))
      atTop (𝓝 (∫ p, φ p * limitObservable h k l β η g p i ∂(μ₀ : Measure _))) := by
  have hc : Continuous fun z : C(PhaseDomain n, ℝ) × (Fin r → ℝ) => φ z.1 * clipTo ‖g i‖ (z.2 i) :=
    (φ.continuous.comp continuous_fst).mul
      ((continuous_clipTo _).comp ((continuous_apply i).comp continuous_snd))
  have hbd : ∀ z : C(PhaseDomain n, ℝ) × (Fin r → ℝ),
      |φ z.1 * clipTo ‖g i‖ (z.2 i)| ≤ ‖φ‖ * ‖g i‖ := fun z => by
      rw [abs_mul]
      exact mul_le_mul ((Real.norm_eq_abs _).symm.trans_le (φ.norm_coe_le_norm _))
        (abs_clipTo_le (norm_nonneg _) _) (abs_nonneg _) (norm_nonneg _)
  let F : (C(PhaseDomain n, ℝ) × (Fin r → ℝ)) →ᵇ ℝ :=
    mkOfBound ⟨fun z => φ z.1 * clipTo ‖g i‖ (z.2 i), hc⟩ (2 * (‖φ‖ * ‖g i‖)) fun x y => by
      change dist (φ x.1 * clipTo ‖g i‖ (x.2 i)) (φ y.1 * clipTo ‖g i‖ (y.2 i)) ≤ _
      rw [Real.dist_eq]
      have := hbd x
      have := hbd y
      have := abs_sub (φ x.1 * clipTo ‖g i‖ (x.2 i)) (φ y.1 * clipTo ‖g i‖ (y.2 i))
      linarith
  have hFapp : ∀ (p : C(PhaseDomain n, ℝ)) (v : Fin r → ℝ), F (p, v) = φ p * clipTo ‖g i‖ (v i) :=
    fun _ _ => rfl
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (randomField_graphLaw_tendsto n h k hk hβ hηc hηnn hmin hatt hW Nseq hN1 hN g hμ) F
  simp_rw [integral_graphLaw, hFapp] at this
  have e1 : ∀ (m : ℕ) (p : C(PhaseDomain n, ℝ)),
      clipTo ‖g i‖ (phaseObservable n h k β (Nseq m) η g p i) =
        phaseObservable n h k β (Nseq m) η g p i :=
    fun m p => clipTo_of_abs_le (abs_phaseObservable_le n h k hβ hηc hηnn hW g (Nseq m) p i)
  have e2 : ∀ p : C(PhaseDomain n, ℝ),
      clipTo ‖g i‖ (limitObservable h k l β η g p i) = limitObservable h k l β η g p i :=
    fun p => clipTo_of_abs_le (abs_limitObservable_le n h k hk hβ hηc hηnn hmin hatt hW g p i)
  simp_rw [e1, e2] at this
  exact this

end annealed

end Grammar
