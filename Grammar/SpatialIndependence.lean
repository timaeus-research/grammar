/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TwoDimRegression

/-!
# Product form of the limiting joint law for a face-constant phase (unit 374; Astra #46 unit 3)

The marginals of the limiting joint law `Q̃^ξ` of `(NK, u)` are the energy limit and the
face-location law (`spatialJointFaceLaw_fst`, `spatialJointFaceLaw_snd`).  If the phase is
constant on the face, `ξ∘P_J ≡ a`, the disintegration of Headline LXXXII factorises and
```
Q̃^ξ = ρ_a ⊗ ν^ξ
```
(`spatialJointFaceLaw_prod_of_const`): energy and face location are independent, the energy
marginal is the tilted law `ρ_a` (`spatialEnergyLimit_eq_phaseLaw_of_const`, consistent with the
constant-phase theory of Headline LXIV), and the face law is the evidence-weighted face measure.
The converse (independence forces a face-constant phase) is the next unit.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable {d : ℕ}

/-! ### Marginals of the limiting joint law -/

theorem spatialJointFaceLaw_snd (h k : Fin (d + 1) → ℕ) (l β : ℝ) (ξ η : (Fin (d + 1) → ℝ) → ℝ) :
    (spatialJointFaceLaw h k l β ξ η).map Prod.snd = faceLocationLimit h k l β ξ η := by
  unfold spatialJointFaceLaw faceLocationLimit
  rw [Measure.map_map measurable_snd (measurable_facePair h k l)]
  rfl

theorem spatialJointFaceLaw_fst (h k : Fin (d + 1) → ℕ) (l β : ℝ) (ξ η : (Fin (d + 1) → ℝ) → ℝ) :
    (spatialJointFaceLaw h k l β ξ η).map Prod.fst = spatialEnergyLimit h k l β ξ η := by
  unfold spatialJointFaceLaw spatialEnergyLimit
  rw [Measure.map_map measurable_fst (measurable_facePair h k l)]
  rfl

/-- The face-location law of a measurable set, from the disintegration:
`ν^ξ(t) = ∫ η(P_Ju) w(u) J_λ(ξ(P_Ju)) 1_t(P_Ju) du / Z_ξ`. -/
theorem faceLocationLimit_real_eq {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l β : ℝ}
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η)
    {t : Set (Fin (n + 1) → ℝ)} (ht : MeasurableSet t) :
    (faceLocationLimit h k l β ξ η).real t =
      (∫ u in unitBox (n + 1), faceWeight h k l η u * fluctMoment β (ξ (faceProj h k l u)) 0 l 0 *
        t.indicator 1 (faceProj h k l u)) / spatialMass h k l β ξ η := by
  have : Fact (0 < β) := ⟨hβ⟩
  have : Fact (0 < l) := ⟨hl⟩
  rw [← spatialJointFaceLaw_snd, ← integral_indicator_one ht,
    integral_map measurable_snd.aemeasurable (measurable_one.indicator ht).aestronglyMeasurable,
    spatialJointFaceLaw_integral_disintegration h k hk hl hβ hmin hξc hηc hηnn hZ
      (f := fun z => t.indicator 1 z.2) ((measurable_one.indicator ht).comp measurable_snd)
      (C := 1) (fun z => by
        simp only [Set.indicator, Pi.one_apply]
        split_ifs <;> simp)]
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  simp only [integral_const, probReal_univ, one_smul]

/-! ### The product form for a face-constant phase -/

/-- **Product form for a face-constant phase**: if `ξ(P_J u) = a` on the box, then
`Q̃^ξ = ρ_a ⊗ ν^ξ` — energy and face location are independent. -/
theorem spatialJointFaceLaw_prod_of_const {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) {a : ℝ}
    (ha : ∀ u ∈ unitBox (n + 1), ξ (faceProj h k l u) = a) :
    spatialJointFaceLaw h k l β ξ η = (phaseLaw β a l).prod (faceLocationLimit h k l β ξ η) := by
  have : Fact (0 < β) := ⟨hβ⟩
  have : Fact (0 < l) := ⟨hl⟩
  have := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  have := spatialJointFaceLaw_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul,
    ← measureReal_def, ← measureReal_def, ← measureReal_def, ← integral_indicator_one (hs.prod ht),
    spatialJointFaceLaw_integral_disintegration h k hk hl hβ hmin hξc hηc hηnn hZ
      (measurable_one.indicator (hs.prod ht)) (C := 1) (fun z => by
        simp only [Set.indicator, Pi.one_apply]
        split_ifs <;> simp),
    faceLocationLimit_real_eq h k hk hl hβ hmin hξc hηc hηnn hZ ht, ← mul_div_assoc,
    ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  simp only [Set.indicator_prod_one, ha u hu]
  rw [integral_mul_const, integral_indicator_one hs]
  ring

/-- For a face-constant phase the limiting energy law is the tilted law `ρ_a` (consistency with
the constant-phase theory). -/
theorem spatialEnergyLimit_eq_phaseLaw_of_const {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l β : ℝ} (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i)
    {ξ η : (Fin (n + 1) → ℝ) → ℝ} (hξc : Continuous ξ) (hηc : Continuous η)
    (hηnn : ∀ v ∈ closedCube (n + 1), 0 ≤ η v) (hZ : 0 < spatialMass h k l β ξ η) {a : ℝ}
    (ha : ∀ u ∈ unitBox (n + 1), ξ (faceProj h k l u) = a) :
    spatialEnergyLimit h k l β ξ η = phaseLaw β a l := by
  have := faceLocationLimit_isProbabilityMeasure h k hk hl hβ hmin hξc hηc hηnn hZ
  rw [← spatialJointFaceLaw_fst, spatialJointFaceLaw_prod_of_const h k hk hl hβ hmin hξc hηc hηnn
    hZ ha, Measure.map_fst_prod, measure_univ, one_smul]

end Grammar
