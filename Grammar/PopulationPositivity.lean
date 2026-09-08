/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingCoeff
import Grammar.LeadingCoeffNonzero

/-!
# Positivity of the face functional (grammar §3 rewrite, Astra #37 P2, unit 296)

The leading population coefficient `amplitudeCoeff h k λ β η = Γ(λ)β^{-λ}/(m−1)! ∏_J 1/(2kᵢ) ·
∫_{(0,1]^d} η(P_J u) ∏_{i∉J} uᵢ^{hᵢ−2kᵢλ} du` is **strictly positive** when the amplitude is
continuous, nonnegative on the minimal-ratio face (`η ∘ P_J ≥ 0` on the closed cube) and positive at
one point of the face (`amplitudeCoeff_pos`). This is the honest positivity criterion of Astra #37
(Theorem A(c)): positivity at an unrelated ambient point is insufficient, and the criterion is for
the **weighted** integrand, whose residual weight is positive on the open box but need not extend
continuously to the boundary. Route: the weighted integrand is nonnegative on the box and
integrable (integrable residual weight times a bounded continuous factor on the compact closed
cube); a positive value at a closed-cube point gives, by continuity, a positive value at an
interior point (`exists_interior_pos`), hence on an open ball inside the open box, where the
residual
weight is positive too; the ball has positive Lebesgue measure, so the support of the integrand has
positive measure and the integral is positive (`setIntegral_pos_iff_support_of_nonneg_ae`).

Consequence (`population_leadingCoeff_pos`): under the hypotheses of `population_leadingCoeff`,
the `(λ, m−1)` coefficient of the population Taylor tree is positive; for the partition function
(`η` = prior × Jacobian factor, positive) this is the denominator positivity of Corollary B.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The face projection is continuous. -/
theorem continuous_faceProj_pop {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) :
    Continuous (faceProj h k l) := by
  unfold faceProj
  refine continuous_pi fun i => ?_
  split_ifs
  · exact continuous_const
  · exact continuous_apply i

/-- The residual weight is positive on the open box. -/
theorem residualWeight_pos_of_openBox {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ)
    (hu : ∀ i, 0 < u i) : 0 < residualWeight h k l u := by
  unfold residualWeight
  refine Finset.prod_pos fun i _ => ?_
  split_ifs
  · exact one_pos
  · exact Real.rpow_pos_of_pos (hu i) _

/-- The weighted face integrand is integrable on the unit box for a continuous amplitude. -/
theorem faceIntegrand_integrableOn {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ)
    (hmin : ∀ i, l ≤ ratioExp h k i) (η : (Fin d → ℝ) → ℝ) (hηc : Continuous η) :
    IntegrableOn (fun u => η (faceProj h k l u) * residualWeight h k l u) (unitBox d) := by
  have h1 : IntegrableOn (fun u => residualWeight h k l u * η (faceProj h k l u)) (unitBox d) :=
    (residualWeight_integrableOn h k hk l hmin).mul_continuousOn_of_subset
      (hηc.comp (continuous_faceProj_pop h k l)).continuousOn (measurableSet_unitBox d)
      (isCompact_closedCube d) (unitBox_subset_closedCube d)
  exact h1.congr_fun (fun u _ => mul_comm _ _) (measurableSet_unitBox d)

/-- **Positivity of the face functional**: for a continuous amplitude that is nonnegative on the
minimal-ratio face and positive at one point of the (closed) face, `amplitudeCoeff > 0`. -/
theorem amplitudeCoeff_pos (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (η : (Fin (d + 1) → ℝ) → ℝ)
    (hηc : Continuous η) (hnn : ∀ u ∈ closedCube (d + 1), 0 ≤ η (faceProj h k l u))
    (u₁ : Fin (d + 1) → ℝ) (hu₁ : u₁ ∈ closedCube (d + 1)) (hpos : 0 < η (faceProj h k l u₁)) :
    0 < amplitudeCoeff h k l β η := by
  unfold amplitudeCoeff
  refine mul_pos (faceLeadConst_pos h k hk l β hl hβ) ?_
  have hnn' : 0 ≤ᵐ[volume.restrict (unitBox (d + 1))]
      fun u => η (faceProj h k l u) * residualWeight h k l u := by
    refine (ae_restrict_iff' (measurableSet_unitBox _)).2 (Eventually.of_forall fun u hu => ?_)
    exact mul_nonneg (hnn u (unitBox_subset_closedCube _ hu)) (residualWeight_nonneg h k l u hu)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn'
    (faceIntegrand_integrableOn h k hk l hmin η hηc)]
  have hcont : Continuous fun u => η (faceProj h k l u) :=
    hηc.comp (continuous_faceProj_pop h k l)
  obtain ⟨u₀, hu₀, hpos₀⟩ := exists_interior_pos 1 one_pos (fun u => η (faceProj h k l u)) hcont
    u₁ (fun i => Set.mem_univ_pi.1 hu₁ i) hpos
  have hopen : IsOpen ({u : Fin (d + 1) → ℝ | 0 < η (faceProj h k l u)} ∩
      Set.pi univ fun _ => Ioo (0 : ℝ) 1) :=
    (isOpen_lt continuous_const hcont).inter (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo)
  have hmem : u₀ ∈ {u : Fin (d + 1) → ℝ | 0 < η (faceProj h k l u)} ∩
      Set.pi univ fun _ => Ioo (0 : ℝ) 1 :=
    ⟨hpos₀, Set.mem_univ_pi.2 fun i => hu₀ i⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen u₀ hmem
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume u₀ hδ) (measure_mono fun u hu => ?_)
  obtain ⟨hu1, hu2⟩ := hball hu
  have hu2' : ∀ i, 0 < u i ∧ u i < 1 := fun i => Set.mem_univ_pi.1 hu2 i
  refine ⟨?_, Set.mem_univ_pi.2 fun i => ⟨(hu2' i).1, (hu2' i).2.le⟩⟩
  rw [Function.mem_support]
  exact (mul_pos hu1 (residualWeight_pos_of_openBox h k l u fun i => (hu2' i).1)).ne'

/-- **The leading population coefficient is positive** for an amplitude that is nonnegative on the
minimal-ratio face and positive at a point of it (in particular for a positive amplitude such as
prior × Jacobian factor): the coefficient system of `population_leadingCoeff` has
`0 < C(λ, m−1)`. -/
theorem population_leadingCoeff_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) (hnn : ∀ u ∈ closedCube (n + 1), 0 ≤ η (faceProj h k l u))
    (u₁ : Fin (n + 1) → ℝ) (hu₁ : u₁ ∈ closedCube (n + 1)) (hpos : 0 < η (faceProj h k l u₁)) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β 1 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      0 < C l (multCount (ratioExp h k) l - 1) := by
  obtain ⟨C, hC, hI, hzero, hlead⟩ := population_leadingCoeff n h k hk β hβ hR hFη hη hηc hmin hatt
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  refine ⟨C, hC, hI, hzero, ?_⟩
  rw [hlead]
  exact amplitudeCoeff_pos n h k hk l β hl hβ hmin η hηc hnn u₁ hu₁ hpos

end Grammar
