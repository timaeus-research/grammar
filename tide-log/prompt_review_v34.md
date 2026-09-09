# Fidelity review v34 — units 295–298 (grammar §3 rewrite, Programme P per Astra #37; unit-9 review)

Context: your #37 design (Theorem A/Corollary B, 20-unit cap) and your reviews v32 (u290–292 PASS) and v33 (u293–294 PASS, with P2 guidance: shift by re-presenting the integral with a distinct shift symbol; state regularity of the residual `ψ` explicitly; distinguish coefficient systems of the shifted and unshifted presentations; positivity criterion = `ψ` continuous, `≥ 0` on the projected face, `> 0` at a point of the face, via positivity on a positive-measure portion of the domain, integrability of the weighted integrand, `faceLeadConst_pos`; non-unit boxes deferred). Units 295–298 implement P2 (shift, positivity, first-candidate summary with `IsEquivalent`) and the two mandatory regression examples (§6). Everything compiles (branch `tide/population-normal-form`, 289 modules, no `sorry`, no added `axiom`).

Frozen interfaces (beyond those quoted in v32/v33):
```lean
theorem exists_interior_pos {d' : ℕ} (b : ℝ) (hb : 0 < b) (e : (Fin d' → ℝ) → ℝ) (hec : Continuous e) (v₁ : Fin d' → ℝ) (hv₁ : ∀ i, 0 ≤ v₁ i ∧ v₁ i ≤ b) (hpos : 0 < e v₁) : ∃ v₀ : Fin d' → ℝ, (∀ i, 0 < v₀ i ∧ v₀ i < b) ∧ 0 < e v₀
theorem residualWeight_integrableOn {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (hmin : ∀ i, l ≤ ratioExp h k i) : IntegrableOn (residualWeight h k l) (unitBox d)
theorem residualWeight_nonneg {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) (hu : u ∈ unitBox d) : 0 ≤ residualWeight h k l u
theorem faceLeadConst_pos {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) : 0 < faceLeadConst h k l β
def closedCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) 1   -- unitBox d ⊆ closedCube d, compact
theorem shift_min {d : ℕ} (h k γ : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (hmin : ∀ i, l ≤ ratioExp h k i) : ∀ i, l ≤ ratioExp (fun i => h i + γ i) k i
theorem face_moment_eq {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hmin : ∀ i, l ≤ ratioExp h k i) (γ : Fin d → ℕ) (hγ : ∀ i, ratioExp h k i = l → γ i = 0) :
    ∫ u in unitBox d, (∏ i, faceProj h k l u i ^ γ i) * (faceLeadConst h k l β * residualWeight h k l u) = monomialMixedConst (fun i => h i + γ i) k l β
theorem amplitudeCoeff_const {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hmin : ∀ i, l ≤ ratioExp h k i) (c : ℝ) : amplitudeCoeff h k l β (fun _ => c) = c * monomialMixedConst h k l β
theorem integrableOn_face_mul {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : ℝ) (hmin : ∀ i, l ≤ ratioExp h k i) (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) : IntegrableOn (fun u => f (faceProj h k l u) * residualWeight h k l u) (unitBox d)
-- MixedRatioCounterexample.lean (unit 206, reviewed): namespace Grammar.MixedCounterexample; hEx = ![0,2], kEx = ![1,1], ηEx u = 1 + u 1; hk, ratio0 : ratioExp hEx kEx 0 = 1/2, ratio1 : … 1 = 3/2, hmin, hatt, multCount_eq : multCount (ratioExp hEx kEx) (1/2) = 1, mixedConst_eq : monomialMixedConst hEx kEx (1/2) 1 = √π/4, mixedConst_shift_eq : monomialMixedConst (fun i => hEx i + ![0,1] i) kEx (1/2) 1 = √π/6, amplitudeCoeff_eq : amplitudeCoeff hEx kEx (1/2) 1 ηEx = 5√π/12, corner_evaluation_fails.
theorem isEquivalent_of_tendsto_one (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v   -- Mathlib, this pin
```

## The four units (complete files)

### Grammar/PopulationShift.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingCoeff
import Grammar.MonomialShiftedMoments

/-!
# Monomial factors shift the candidate support (grammar §3 rewrite, Astra #37 P2, unit 295)

The paper's "vanishing order" mechanism (`eq:lambda_I_f`, `eq:mu_I_phi`): if the amplitude
carries an admissible monomial factor, `η(u) = u^s ψ(u)` with `s : Fin (n+1) → ℕ`, then
`u^h η = u^{h+s} ψ`, so the population integral is the population integral of `ψ` with the
shifted weight `h + s` (`origPhaseIntegral_monomial_shift`). Applying the population Taylor tree
and Headline VIII to `(h + s, ψ)`:

* the coefficient system is supported on the shifted candidate set `Λ(h+s, k)`
  (`population_shift_vanish`);
* the first shifted candidate is `λ_s = min_i (hᵢ+sᵢ+1)/(2kᵢ) ≥ λ`, with multiplicity `m_s`; the
  coefficients at `λ_s` vanish above log degree `m_s − 1`, and the `(λ_s, m_s − 1)` coefficient is
  the face functional of the **residual** amplitude `ψ` for the shifted weight,
  `amplitudeCoeff (h+s) k λ_s β ψ` (`population_shift_leadingCoeff`) — not of `u^s ψ`
  (Astra #37: using `u^s ψ` after shifting the weight counts the vanishing twice).

The factorisation `η = u^s ψ` with `ψ` continuous and holomorphically extendable is the
hypothesis ("admissible monomial factor", not necessarily maximal); the implication from a
divisorial vanishing order to such a factorisation belongs to the geometric/analytic bridge and is
not formalised. The shifted system is a system for the shifted presentation; identifying it with an
unshifted system's coefficients requires uniqueness, not done here. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- **Monomial shift of the amplitude**: `∫ (u^s ψ) u^h e^{…} = ∫ ψ u^{h+s} e^{…}` for any phase. -/
theorem origPhaseIntegral_monomial_shift (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (ξ ψ : (Fin (n + 1) → ℝ) → ℝ) (s : Fin (n + 1) → ℕ) :
    origPhaseIntegral n h k β N b ξ (fun u => (∏ i, u i ^ s i) * ψ u) =
      origPhaseIntegral n (fun i => h i + s i) k β N b ξ ψ := by
  unfold origPhaseIntegral
  congr 1
  funext u
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

/-- Coefficient systems of the shifted presentation vanish off the shifted candidate set. -/
theorem population_shift_vanish (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (s : Fin (n + 1) → ℕ)
    {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n (fun i => h i + s i) k β 1 cξ cη C) (μ : ℝ) (j : ℕ)
    (hμ : ¬ candidateExp (fun i => h i + s i) k μ) : C μ j = 0 :=
  hC.vanish μ j hμ

/-- The shifted minimal ratio is at least the unshifted one. -/
theorem shift_min_le {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (s : Fin d → ℕ) {l ls : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt_s : ∃ i, ratioExp (fun i => h i + s i) k i = ls) :
    l ≤ ls := by
  obtain ⟨i, hi⟩ := hatt_s
  rw [← hi]
  exact shift_min h k s hk l hmin i

/-- **The leading coefficient after a monomial shift** (`eq:lambda_I_f` corrected, chart level,
`b = 1`): for `η = u^s ψ` with `ψ` continuous on `ℝ^{n+1}` and a holomorphic `Fψ` on the polydisc
of radius `R > 1`, `Re Fψ = ψ` on the box, and `λ_s = min_i (hᵢ+sᵢ+1)/(2kᵢ)` with multiplicity
`m_s`: there is a coefficient system `C` for the shifted weight `h + s` with the full Taylor-tree
conclusion whose family integral is the original population integral of `u^s ψ` with weight `h`,
supported on `Λ(h+s,k)`, with `C(λ_s, j) = 0` for `m_s − 1 < j ≤ n` and
`C(λ_s, m_s − 1) = amplitudeCoeff (h+s) k λ_s β ψ` (the face functional of the residual `ψ`). -/
theorem population_shift_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fψ : (Fin (n + 1) → ℂ) → ℂ}
    {ψ : (Fin (n + 1) → ℝ) → ℝ} (hFψ : DifferentiableOn ℂ Fψ (openPolydisc (n + 1) R))
    (hψ : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fψ fun i => (u i : ℂ)).re = ψ u)
    (hψc : Continuous ψ) (s : Fin (n + 1) → ℕ) {ls : ℝ}
    (hmin : ∀ i, ls ≤ ratioExp (fun i => h i + s i) k i)
    (hatt : ∃ i, ratioExp (fun i => h i + s i) k i = ls) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n (fun i => h i + s i) k β 1 0 (taylorFamily (n + 1) Fψ) C ∧
      (∀ N, familyPhaseIntegralBox n (fun i => h i + s i) k β N 1 0 (taylorFamily (n + 1) Fψ) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) (fun u => (∏ i, u i ^ s i) * ψ u)) ∧
      (∀ μ j, ¬ candidateExp (fun i => h i + s i) k μ → C μ j = 0) ∧
      (∀ j ∈ Finset.range (n + 1),
        multCount (ratioExp (fun i => h i + s i) k) ls - 1 < j → C ls j = 0) ∧
      C ls (multCount (ratioExp (fun i => h i + s i) k) ls - 1) =
        amplitudeCoeff (fun i => h i + s i) k ls β ψ := by
  obtain ⟨C, hC, hI, hzero, hlead⟩ :=
    population_leadingCoeff n (fun i => h i + s i) k hk β hβ hR hFψ hψ hψc hmin hatt
  refine ⟨C, hC, fun N => ?_, hC.vanish, hzero, hlead⟩
  rw [hI N, origPhaseIntegral_monomial_shift]

end Grammar
```

### Grammar/PopulationPositivity.lean
```lean
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
```

### Grammar/PopulationEquivalent.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingCoeff

/-!
# The first-candidate term of the population expansion (Astra #37 Theorem A(c), unit 297)

Collecting P1–P2 at chart level on the unit box: for `η` continuous with a holomorphic extension
on a polydisc of radius `R > 1` (real-part agreement on the box), `λ = min_i (hᵢ+1)/(2kᵢ)`, `m`
its multiplicity, `A = amplitudeCoeff h k λ β η` the face functional,

* there are no terms at exponents below `λ` (`population_coeff_eq_zero_of_lt`: candidates are
  `≥ λ`, and coefficients vanish off the candidate set);
* at exponent `λ` there are no terms of log degree above `m − 1`, and the `(λ, m−1)` coefficient
  is `A` (P1);
* if `A ≠ 0` the population integral is asymptotically equivalent to `A N^{-λ}(log N)^{m−1}`
  (`population_isEquivalent`, directly from Headline VIII).

`population_firstCandidate` packages these. If `A = 0` nothing is asserted about the actual
leading term: the next nonzero coefficient may sit at the same exponent with a smaller log degree.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

/-- Coefficients of a candidate-supported system vanish below the minimal ratio. -/
theorem population_coeff_eq_zero_of_lt {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    {C : ℝ → ℕ → ℝ} (hvan : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {μ : ℝ} (hμ : μ < l) (j : ℕ) : C μ j = 0 :=
  hvan μ j fun hc => absurd (le_of_candidateExp h k hk hmin hc) (not_le.2 hμ)

/-- **Asymptotic equivalence of the population integral** with its first-candidate term when the
face functional is nonzero: `∫ η u^h e^{-βN u^{2k}} ~ A N^{-λ}(log N)^{m−1}`. -/
theorem population_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (η : (Fin (n + 1) → ℝ) → ℝ) (hηc : Continuous η) (hA : amplitudeCoeff h k l β η ≠ 0) :
    (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop]
      fun N => amplitudeCoeff h k l β η *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hT := amplitude_tendsto n h k hk l β hl hβ hmin hatt η hηc
  have hT' : Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η /
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) / amplitudeCoeff h k l β η)
      atTop (𝓝 (amplitudeCoeff h k l β η / amplitudeCoeff h k l β η)) := by
    refine (hT.congr' (Eventually.of_forall fun N => ?_)).div_const _
    simp only [origPhaseIntegral_population_one]
  rw [div_self hA] at hT'
  refine isEquivalent_of_tendsto_one (hT'.congr' (Eventually.of_forall fun N => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- **Theorem A(c) at chart level (`b = 1`)**: the population Taylor tree has no terms below
`λ`, none at `λ` above log degree `m − 1`, its `(λ, m−1)` coefficient is the face functional
`A`, and when `A ≠ 0` the integral is asymptotically `A N^{-λ}(log N)^{m−1}`. -/
theorem population_firstCandidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β 1 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
      (∀ μ, μ < l → ∀ j, C μ j = 0) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η ∧
      (amplitudeCoeff h k l β η ≠ 0 →
        (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η) ~[atTop]
          fun N => amplitudeCoeff h k l β η *
            (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) := by
  obtain ⟨C, hC, hI, hzero, hlead⟩ := population_leadingCoeff n h k hk β hβ hR hFη hη hηc hmin hatt
  exact ⟨C, hC, hI, fun μ hμ j => population_coeff_eq_zero_of_lt h k hk hC.vanish hmin hμ j,
    hzero, hlead, fun hA => population_isEquivalent n h k hk β hβ hmin hatt η hηc hA⟩

end Grammar
```

### Grammar/PopulationRegression.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MixedRatioCounterexample
import Grammar.PopulationEquivalent

/-!
# Regression examples for the §3 rewrite (Astra #37 §6, unit 298)

Two examples in the mixed-ratio model `d = 2`, `h = (0,2)`, `k = (1,1)`, `β = 1` (ratios `1/2`,
`3/2`; `λ = 1/2`, `J = {0}`, `m = 1`; the face is `{u₀ = 0}` with residual weight `u₁`), which the
corrected §3 theorem must accommodate and the old one contradicts:

* **Face dependence** (`face_dependence`): the amplitudes `1` and `1 + u₁` have the same corner
  value `1` but different leading coefficients, `√π/4` and `5√π/12`. The general leading
  coefficient is the face integral, not a corner evaluation (this sharpens unit 206's
  `corner_evaluation_fails`).
* **Signed cancellation** (`signed_cancellation`): the amplitude `ψ = 1 − (3/2)u₁` has `ψ(0) = 1 ≠
0`
  yet its face functional vanishes, `∫₀¹ (1 − (3/2)v) v dv = 0`, so the first-candidate coefficient
  is zero although the deepest normal jet is nonzero. "Nonzero jet on the stratum ⇒ leading exponent
  `μ_I(φ)`" (`eq:lambda_I_f`) fails without a nonvanishing hypothesis on the face functional,
  and this happens within one chart, without cross-chart cancellation.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Real Set

namespace Grammar

namespace MixedCounterexample

/-- The signed amplitude `ψ(u) = 1 − (3/2) u₁`. -/
noncomputable def ψEx (u : Fin 2 → ℝ) : ℝ := 1 - 3 / 2 * u 1

theorem ψEx_zero : ψEx 0 = 1 := by simp [ψEx]

theorem continuous_ψEx : Continuous ψEx :=
  continuous_const.sub (continuous_const.mul (continuous_apply 1))

/-- The constant amplitude has face functional `√π/4`. -/
theorem amplitudeCoeff_one : amplitudeCoeff hEx kEx (1 / 2) 1 (fun _ => (1 : ℝ)) =
    Real.sqrt π / 4 := by
  rw [amplitudeCoeff_const hEx kEx hk (1 / 2) 1 hmin, mixedConst_eq, one_mul]

/-- **Face dependence**: `1` and `1 + u₁` agree at the corner but have different leading
coefficients. -/
theorem face_dependence :
    (fun _ : Fin 2 → ℝ => (1 : ℝ)) 0 = ηEx 0 ∧
      amplitudeCoeff hEx kEx (1 / 2) 1 (fun _ => (1 : ℝ)) ≠ amplitudeCoeff hEx kEx (1 / 2) 1 ηEx :=
by
  refine ⟨by simp [ηEx], ?_⟩
  rw [amplitudeCoeff_one, amplitudeCoeff_eq]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  intro h
  nlinarith

/-- **The face functional of `ψ = 1 − (3/2)u₁` vanishes.** -/
theorem amplitudeCoeff_ψEx : amplitudeCoeff hEx kEx (1 / 2) 1 ψEx = 0 := by
  have hA := face_moment_eq hEx kEx hk (1 / 2) 1 hmin (fun _ => 0) (fun _ _ => rfl)
  have hB := face_moment_eq hEx kEx hk (1 / 2) 1 hmin ![0, 1] (by
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => rfl, fun h => absurd h (by rw [ratio1]; norm_num)⟩)
  have hI : ∀ γ : Fin 2 → ℕ, IntegrableOn (fun u => (∏ i, faceProj hEx kEx (1 / 2) u i ^ γ i) *
      (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) (unitBox 2) := by
    intro γ
    refine (integrableOn_face_mul hEx kEx hk (1 / 2) hmin
      (fun x => faceLeadConst hEx kEx (1 / 2) 1 * ∏ i, x i ^ γ i)
      (continuous_const.mul (continuous_prod_pow γ))).congr_fun (fun u _ => ?_)
      (measurableSet_unitBox 2)
    ring
  have hsplit : amplitudeCoeff hEx kEx (1 / 2) 1 ψEx =
      (∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (fun _ : Fin 2 => 0) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u)) -
      3 / 2 * ∫ u in unitBox 2, (∏ i, faceProj hEx kEx (1 / 2) u i ^ (![0, 1] : Fin 2 → ℕ) i) *
        (faceLeadConst hEx kEx (1 / 2) 1 * residualWeight hEx kEx (1 / 2) u) := by
    unfold amplitudeCoeff
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hI _) ((hI _).const_mul _)]
    refine setIntegral_congr_fun (measurableSet_unitBox 2) fun u _ => ?_
    simp only [ψEx, Fin.prod_univ_two, pow_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      pow_one, one_mul]
    ring
  rw [hsplit, hA, hB, mixedConst_shift_eq]
  have : monomialMixedConst (fun i => hEx i + (fun _ : Fin 2 => 0) i) kEx (1 / 2) 1 =
      monomialMixedConst hEx kEx (1 / 2) 1 := by
    congr 1
  rw [this, mixedConst_eq]
  ring

/-- **Signed cancellation**: a nonzero deepest normal jet with a vanishing first-candidate
coefficient, within a single chart. -/
theorem signed_cancellation : ψEx 0 ≠ 0 ∧ amplitudeCoeff hEx kEx (1 / 2) 1 ψEx = 0 :=
  ⟨by rw [ψEx_zero]; exact one_ne_zero, amplitudeCoeff_ψEx⟩

/-- The population integral of `ψ` is `o(N^{-1/2})`: the first candidate carries no term. -/
theorem ψEx_normalised_tendsto_zero :
    Tendsto (fun N : ℝ => (∫ x in unitBox 2,
        ψEx x * ((∏ i, x i ^ hEx i) * Real.exp (-(1 * N * ∏ i, x i ^ (2 * kEx i))))) /
        N ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
  have hT := amplitude_tendsto 1 hEx kEx hk (1 / 2) 1 (by norm_num) one_pos hmin hatt ψEx
    continuous_ψEx
  rw [multCount_eq, Nat.sub_self, amplitudeCoeff_ψEx] at hT
  simpa using hT

end MixedCounterexample

end Grammar
```

## Questions
1. u295 (shift): is `origPhaseIntegral_monomial_shift` the right exact identity, and does `population_shift_leadingCoeff` state Theorem A(c) for `η = u^s ψ` correctly — shifted support `Λ(h+s,k)`, shifted `λ_s`, `m_s`, and the face functional of the **residual** `ψ` for the shifted weight? Is the regularity of `ψ` (continuous on `ℝ^{n+1}`, holomorphic `Fψ` with `Re Fψ = ψ` on the box) stated as a hypothesis and not inferred? Is the docstring's distinction between the shifted and unshifted coefficient systems adequate?
2. u296 (positivity): is `amplitudeCoeff_pos` the honest criterion (η continuous; `η ∘ P_J ≥ 0` on the closed cube = nonneg on the projected face; `> 0` at one closed-cube point), and is the proof sound (integrability via `mul_continuousOn_of_subset` on the compact closed cube; interior point via `exists_interior_pos`; open ball inside the open box where both factors are positive; `Metric.measure_ball_pos`; `setIntegral_pos_iff_support_of_nonneg_ae`)? Does `population_leadingCoeff_pos` correctly deliver the denominator positivity of Corollary B at chart level (positive prior × Jacobian amplitude)?
3. u297: is `population_isEquivalent` correctly derived from Headline VIII (`f/g → A`, `A ≠ 0` ⇒ `f ~ A·g`), and is `population_firstCandidate` a faithful chart-level (`b = 1`) rendering of Theorem A(c) including the "no terms below λ / none above log degree m−1 at λ" clauses and the absence of any claim when `A = 0`?
4. u298: do the two examples establish what §6 asked (face dependence: same corner value, different leading coefficients; signed cancellation: `ψ(0) ≠ 0` with vanishing face functional, and `𝒵_ψ(N) = o(N^{-1/2})`), in a single chart?
5. Any blocking/nonblocking fixes before P3 (deterministic tangential integration + finite chart assembly with exponentially small residual, reusing `TangentialData`/`gInt`/`CutoffExpansion`; Astra #37: "a fixed `JointData` need not have zero noise — construct data through a zero-noise embedding or include an explicit zero-noise condition"; ordered extraction with the min-exponent/max-log leading rule, assembled coefficient explicitly required nonzero) and P4/P5? In particular: how should "zero-noise data" be encoded — as `x : JointData` with `xiCoord (x I v) = 0` for all `I, v`, or by constructing `JointData` from continuous amplitude families `ψ_I : K_I → CoeffFamily` with the zero phase (`ofFamilies 0 (ψ_I v)`)? And for the tangential leading coefficient: is the natural P3 target `𝒞_{λ,m−1}(x) = ∫_K amplitudeCoeff h k λ β (η_v) dν(v)` (the paper's `∫_{S_I} … c_0 |dv|`), derived from u294's pointwise identification `dataBoxCoeff … (x v) λ (m−1) = amplitudeCoeff … (η_v)`, which needs `dataBoxCoeff` (the canonical coefficient of `StochasticData`, defined via `boxCoeff`/`familySpectralCoeff` of the box families) to be linked to the `TaylorTreeConclusion` coefficient `C` of u294 — is `C μ j = familySpectralCoeff … (scale cξ 1) (scale cη 1) μ j` (`coeff_eq`) plus `dataBoxCoeff = boxCoeff of the box families` enough, or is there a scaling/normalisation subtlety at `b = 1` I must check?

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
