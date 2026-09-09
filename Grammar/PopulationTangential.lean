/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationDataBridge
import Grammar.TangentialRemainder

/-!
# Tangential integration of the first-candidate term (Astra #37 P3, unit 300)

One stratum, population data: `x : C(K, DataSpace (n+1))` with zero noise (`xiCoord (x v) = 0`
for every tangential point `v`; `K` compact, `ν` a finite measure carrying the tangential density
and cutoff exactly once), unit normal box. The integrated coefficients `𝒞_{μ,j}(x) = ∫_K
dataBoxCoeff (x v) μ j dν` inherit the pointwise facts of unit 299:

* `𝒞_{μ,j}(x) = 0` for `μ < λ` and for `μ = λ`, `j > m − 1` (`tanCoeff_eq_zero_of_lt_min`,
  `tanCoeff_population_eq_zero_of_gt`);
* `𝒞_{λ,m−1}(x) = ∫_K amplitudeCoeff h k λ β (η_v) dν(v)` — the paper's stratum integral of the
  face functional against the tangential measure (`tanCoeff_population_leading`; integral
  congruence, no interchange of the normal and tangential integrals is needed).

Hence the integrated predecessor sum at the target `(λ, m−1)` vanishes identically
(`tanPredSum_population_eq_zero`), and the **uniform-on-balls ordered-remainder theorem of
Programme S** (`tendstoUniformlyOn_tanRemainder`, the integrated `lemma:AsymInt`) gives
```
𝒵(N; x) / (N^{-λ} (log N)^{m−1}) → ∫_K amplitudeCoeff h k λ β (η_v) dν(v)
```
(`tanIntegral_population_tendsto`), with asymptotic equivalence when the integrated face
functional is nonzero and positivity when the pointwise face functionals are positive and `ν ≠ 0`.
This is Theorem A(c) for one stratum with tangential integration; the remainder control is the
Programme S majorant, not a pointwise-to-integrated inference. `(λ, m−1)` is the FIRST CANDIDATE;
it is the leading pair only when the integrated face functional is nonzero (tangential signed
cancellation is possible). "The represented amplitude" means `evalF (etaCoord (x v))`; that an
externally given amplitude is so represented is a hypothesis on the data, not proved here. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K]
variable (ν : Measure K) [IsFiniteMeasure ν]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- Integrated coefficients vanish below the minimal ratio (any data, any box). -/
theorem tanCoeff_eq_zero_of_lt_min (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {μ : ℝ} (hμ : μ < l) (j : ℕ) :
    tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_lt_min n h k hk β hβ hb _ hmin hμ]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- Zero-noise integrated coefficients at `λ` vanish above log degree `m − 1`. -/
theorem tanCoeff_population_eq_zero_of_gt (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {j : ℕ}
    (hj : multCount (ratioExp h k) l - 1 < j) : tanCoeff ν n h k β 1 x l j = 0 := by
  unfold tanCoeff
  simp [fun v => (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).1 j hj]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- **The integrated first-candidate coefficient is the stratum integral of the face
functional.** -/
theorem tanCoeff_population_leading (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    tanCoeff ν n h k β 1 x l (multCount (ratioExp h k) l - 1) =
      ∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν := by
  unfold tanCoeff
  congr 1
  funext v
  exact (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).2

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- The integrated predecessor sum at the first candidate vanishes identically. -/
theorem tanPredSum_population_eq_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (N : ℝ) :
    tanPredSum ν n h k β 1 x l (multCount (ratioExp h k) l - 1) N = 0 := by
  unfold tanPredSum
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨-, hprec⟩ := mem_predSet_iff.1 hp
  rcases hprec with hlt | ⟨heq, hgt⟩
  · rw [tanCoeff_eq_zero_of_lt_min ν n h k hk β hβ one_pos x hmin hlt, zero_mul]
  · have heq' : p.1 = l := heq
    rw [heq', tanCoeff_population_eq_zero_of_gt ν n h k hk β hβ x hx hmin hatt hgt, zero_mul]

/-- **Theorem A(c) with tangential integration**: for zero-noise tangential data the integrated
population integral, normalised by the first-candidate scale, converges to the stratum integral
of the face functional. -/
theorem tanIntegral_population_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => tanIntegral ν n h k β N 1 x /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν)) := by
  have hμ : ∃ m : ℕ, l = (m : ℝ) / latticeQ k := by
    obtain ⟨i, hi⟩ := hatt
    obtain ⟨m, -, hm⟩ := ratio_mem_lattice k hk i (h i)
    exact ⟨m, by rw [← hi]; exact hm⟩
  have hj : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  have hxmem : x ∈ Metric.closedBall (0 : TangentialData K (n + 1)) ‖x‖ :=
    Metric.mem_closedBall.2 (by rw [dist_zero_right])
  have hT := (tendstoUniformlyOn_tanRemainder ν n h k hk β hβ one_pos hμ hj ‖x‖).tendsto_at hxmem
  rw [tanCoeff_population_leading ν n h k hk β hβ x hx hmin hatt] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  unfold tanRemainder
  rw [tanPredSum_population_eq_zero ν n h k hk β hβ x hx hmin hatt, sub_zero]

/-- Asymptotic equivalence when the integrated face functional is nonzero. -/
theorem tanIntegral_population_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν) ≠ 0) :
    (fun N => tanIntegral ν n h k β N 1 x) ~[atTop]
      fun N => (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν) *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  have hT := (tanIntegral_population_tendsto ν n h k hk β hβ x hx hmin hatt).div_const
    (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν)
  rw [div_self hA] at hT
  refine isEquivalent_of_tendsto_one (hT.congr' (Eventually.of_forall fun N => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- The pointwise face functional is integrable over the tangential space. -/
theorem integrable_tanFace (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Integrable (fun v => amplitudeCoeff h k l β (dataAmplitude (x v))) ν := by
  have := integrable_dataBoxCoeff_tan ν n h k hk β hβ one_pos x l
    (multCount (ratioExp h k) l - 1)
  refine this.congr (Eventually.of_forall fun v => ?_)
  exact (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).2

/-- Positivity of the integrated face functional when the pointwise face functionals are
positive and the tangential measure is nonzero. -/
theorem tanCoeff_population_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hpos : ∀ v, 0 < amplitudeCoeff h k l β (dataAmplitude (x v))) (hν : ν ≠ 0) :
    0 < ∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν := by
  rw [integral_pos_iff_support_of_nonneg (fun v => (hpos v).le)
    (integrable_tanFace ν n h k hk β hβ x hx hmin hatt)]
  have hsupp : Function.support (fun v => amplitudeCoeff h k l β (dataAmplitude (x v))) = univ :=
    Set.eq_univ_of_forall fun v => (hpos v).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.2 hν

end Grammar
