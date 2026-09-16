/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AmplitudeJetSpace
import Grammar.GaussianEvenMoments

/-!
# Gaussian averaging of the population coefficient (§20, the Wick formula)

For a random smooth field `Y_ω` on the parameter cube whose one-point laws are centred Gaussian with
variance `V(x)` — no joint Gaussianity, no covariance structure — and a smooth amplitude `η`, if the
random jets `cubeJet R 1 (η Y_ω^{2j})` are Bochner integrable in the jet space, then

★★★ `integral_empCoeff_zero_pow_even`:
`E[empCoeff (η Y_ω^{2j}) 0 h k μ q] = (2j)!/(2^j j!) · empCoeff (η V^j) 0 h k μ q`,

★★ `integral_empCoeff_zero_pow_odd`: `E[empCoeff (η Y_ω^{2j+1}) 0 h k μ q] = 0`.

Route (consult #160, A1–A5): the coefficient is a continuous linear functional `Φ` of the jet
(`exists_popCoeffCLM`), so `E Φ(F) = Φ(E F)`; the Bochner integral `E F` lies in the closed jet
range and its zeroth-order evaluations are `η(x) E[Y_ω(x)^{2j}] = η(x) (2j)!/(2^j j!) V(x)^j`
(`GaussianEvenMoments`); holonomy of the closed jet range (`JetHolonomy`) identifies
`E F = (2j)!/(2^j j!) · cubeJet (η V^j)`.  No differentiation under the expectation is needed:
the analytic content sits in the Bochner integrability hypothesis.

Zero `sorry`/`axiom`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Grammar

open SmoothEngine

variable {d : ℕ}

/-- Zeroth-order evaluation at `x` as a continuous linear functional on the jet space. -/
noncomputable def jetEval0 (R : ℕ) (b : ℝ) (x : closedBox d b) : CubeJetSpace d R b →L[ℝ] ℝ :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Fin d → ℝ) ℝ (fun _ => 0)).comp
    ((ContinuousMap.evalCLM ℝ x).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun r : Fin (R + 1) =>
          ContinuousMap (closedBox d b)
            (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)) ⟨0, Nat.succ_pos R⟩)) :
    (∀ r : Fin (R + 1),
      ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ))
      →L[ℝ] ℝ)

theorem jetEval0_apply {R : ℕ} {b : ℝ} (x : closedBox d b) (z : CubeJetSpace d R b) :
    jetEval0 R b x z = z.toPi ⟨0, Nat.succ_pos R⟩ x (fun _ => 0) := rfl

theorem jetEval0_cubeJet {R : ℕ} {b : ℝ} (x : closedBox d b) {η : (Fin d → ℝ) → ℝ}
    (hη : ContDiff ℝ ∞ η) : jetEval0 R b x (cubeJet R b η hη) = η x.1 := by
  rw [jetEval0_apply]
  exact iteratedFDeriv_zero_apply _

/-- Holonomy in evaluation form: two elements of the closed jet range with the same zeroth-order
evaluations are equal. -/
theorem eq_of_mem_closure_jetRange_of_jetEval0_eq {R : ℕ} {b : ℝ} (hb : 0 < b)
    {z z' : CubeJetSpace d R b} (hz : z ∈ closure (jetSet d R b))
    (hz' : z' ∈ closure (jetSet d R b))
    (h : ∀ x : closedBox d b, jetEval0 R b x z = jetEval0 R b x z') : z = z' := by
  refine eq_of_mem_closure_jetRange_of_zero_eq hb hz hz' fun x => ?_
  refine ContinuousMultilinearMap.ext fun m => ?_
  rw [Subsingleton.elim m (fun _ => 0)]
  exact h x

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h k p : Fin d → ℕ}

/-- The Bochner integral of an integrable random jet lies in the closed jet range. -/
theorem integral_mem_closure_jetSet {R : ℕ} {F : Ω → CubeJetSpace d R 1}
    (hF : ∀ o, F o ∈ jetSet d R 1) (hint : Integrable F P) :
    ∫ o, F o ∂P ∈ closure (jetSet d R 1) := by
  have hconv : Convex ℝ (closure (jetSet d R 1)) := by
    rw [← coe_jetRange]
    exact (jetRange d R 1).convex.closure
  exact Convex.integral_mem hconv isClosed_closure
    (Filter.Eventually.of_forall fun o => subset_closure (hF o)) hint

/-- ★★★ **Gaussian averaging of the population coefficient, even powers.** -/
theorem integral_empCoeff_zero_pow_even (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {R : ℕ} (hR : ∑ i, p i ≤ R) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1)
    {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {Y : Ω → (Fin d → ℝ) → ℝ}
    (hY : ∀ o, ContDiff ℝ ∞ (Y o)) {V : (Fin d → ℝ) → ℝ} (hV : ContDiff ℝ ∞ V)
    (hV0 : ∀ x, 0 ≤ V x) (j : ℕ)
    (hint : Integrable (fun o => cubeJet R 1 (fun v => η v * Y o v ^ (2 * j))
      (hη.mul ((hY o).pow (2 * j)))) P)
    (hlaw : ∀ x ∈ closedBox d 1, HasLaw (fun o => Y o x) (gaussianReal 0 ⟨V x, hV0 x⟩) P) :
    ∫ o, empCoeff (fun v => η v * Y o v ^ (2 * j)) (fun _ => 0) h k μ q ∂P =
      ((2 * j).factorial / (2 ^ j * (j.factorial : ℝ))) *
        empCoeff (fun v => η v * V v ^ j) (fun _ => 0) h k μ q := by
  obtain ⟨Φ, hΦ⟩ := exists_popCoeffCLM hk hL hp hp0 hR hμ hq
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (2 * j).factorial / (2 ^ j * (j.factorial : ℝ)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Ω → CubeJetSpace d R 1, F = fun o =>
    cubeJet R 1 (fun v => η v * Y o v ^ (2 * j)) (hη.mul ((hY o).pow (2 * j))) := ⟨_, rfl⟩
  have hintF : Integrable F P := hF ▸ hint
  obtain ⟨u, hu⟩ : ∃ u : CubeJetSpace d R 1,
    u = cubeJet R 1 (fun v => η v * V v ^ j) (hη.mul (hV.pow j)) := ⟨_, rfl⟩
  -- the coefficient is `Φ` of the random jet
  have h1 : ∫ o, empCoeff (fun v => η v * Y o v ^ (2 * j)) (fun _ => 0) h k μ q ∂P =
      ∫ o, Φ (F o) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun o => ?_)
    rw [hF]
    exact (hΦ _ _).symm
  have h2 : ∫ o, Φ (F o) ∂P = Φ (∫ o, F o ∂P) := Φ.integral_comp_comm hintF
  -- identify the Bochner integral through the zeroth-order evaluations
  have hmem : ∫ o, F o ∂P ∈ closure (jetSet d R 1) :=
    integral_mem_closure_jetSet (fun o => by rw [hF]; exact cubeJet_mem_jetSet R 1 _) hintF
  have humem : κ • u ∈ closure (jetSet d R 1) := by
    rw [← coe_jetRange]
    exact subset_closure ((jetRange d R 1).smul_mem κ (hu ▸ cubeJet_mem_jetSet R 1 _))
  have heval : ∀ x : closedBox d 1, jetEval0 R 1 x (∫ o, F o ∂P) = jetEval0 R 1 x (κ • u) := by
    intro x
    rw [← (jetEval0 R 1 x).integral_comp_comm hintF, map_smul, smul_eq_mul, hu, jetEval0_cubeJet]
    have hpt : ∀ o, jetEval0 R 1 x (F o) = η x.1 * Y o x.1 ^ (2 * j) := fun o => by
      rw [hF]
      exact jetEval0_cubeJet x _
    simp_rw [hpt]
    rw [integral_const_mul]
    have hl : ∫ o, Y o x.1 ^ (2 * j) ∂P =
        ((2 * j).factorial / (2 ^ j * (j.factorial : ℝ))) * V x.1 ^ j := by
      have h1 : ∫ o, Y o x.1 ^ (2 * j) ∂P = ∫ y, y ^ (2 * j) ∂gaussianReal 0 ⟨V x.1, hV0 x.1⟩ :=
        (hlaw x.1 x.2).integral_comp (f := fun y : ℝ => y ^ (2 * j))
          (continuous_pow (2 * j)).aestronglyMeasurable
      rw [h1]
      exact integral_pow_even_gaussianReal' ⟨V x.1, hV0 x.1⟩ j
    rw [hl, hκ]
    ring
  have hFu : ∫ o, F o ∂P = κ • u :=
    eq_of_mem_closure_jetRange_of_jetEval0_eq one_pos hmem humem heval
  rw [h1, h2, hFu, map_smul, smul_eq_mul, hu, hΦ, hκ]

/-- ★★ **Gaussian averaging of the population coefficient, odd powers**: the expectation
vanishes. -/
theorem integral_empCoeff_zero_pow_odd (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {R : ℕ} (hR : ∑ i, p i ≤ R) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1)
    {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) {Y : Ω → (Fin d → ℝ) → ℝ}
    (hY : ∀ o, ContDiff ℝ ∞ (Y o)) {V : (Fin d → ℝ) → ℝ} (hV0 : ∀ x, 0 ≤ V x) (j : ℕ)
    (hint : Integrable (fun o => cubeJet R 1 (fun v => η v * Y o v ^ (2 * j + 1))
      (hη.mul ((hY o).pow (2 * j + 1)))) P)
    (hlaw : ∀ x ∈ closedBox d 1, HasLaw (fun o => Y o x) (gaussianReal 0 ⟨V x, hV0 x⟩) P) :
    ∫ o, empCoeff (fun v => η v * Y o v ^ (2 * j + 1)) (fun _ => 0) h k μ q ∂P = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_popCoeffCLM hk hL hp hp0 hR hμ hq
  obtain ⟨F, hF⟩ : ∃ F : Ω → CubeJetSpace d R 1, F = fun o =>
    cubeJet R 1 (fun v => η v * Y o v ^ (2 * j + 1)) (hη.mul ((hY o).pow (2 * j + 1))) := ⟨_, rfl⟩
  have hintF : Integrable F P := hF ▸ hint
  have h1 : ∫ o, empCoeff (fun v => η v * Y o v ^ (2 * j + 1)) (fun _ => 0) h k μ q ∂P =
      ∫ o, Φ (F o) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun o => ?_)
    rw [hF]
    exact (hΦ _ _).symm
  have h2 : ∫ o, Φ (F o) ∂P = Φ (∫ o, F o ∂P) := Φ.integral_comp_comm hintF
  have hmem : ∫ o, F o ∂P ∈ closure (jetSet d R 1) :=
    integral_mem_closure_jetSet (fun o => by rw [hF]; exact cubeJet_mem_jetSet R 1 _) hintF
  have h0mem : (0 : CubeJetSpace d R 1) ∈ closure (jetSet d R 1) := by
    rw [← coe_jetRange]
    exact subset_closure (jetRange d R 1).zero_mem
  have heval : ∀ x : closedBox d 1, jetEval0 R 1 x (∫ o, F o ∂P) = jetEval0 R 1 x 0 := by
    intro x
    rw [← (jetEval0 R 1 x).integral_comp_comm hintF, map_zero]
    have hpt : ∀ o, jetEval0 R 1 x (F o) = η x.1 * Y o x.1 ^ (2 * j + 1) := fun o => by
      rw [hF]
      exact jetEval0_cubeJet x _
    simp_rw [hpt]
    rw [integral_const_mul]
    have hl : ∫ o, Y o x.1 ^ (2 * j + 1) ∂P = 0 := by
      have h1 : ∫ o, Y o x.1 ^ (2 * j + 1) ∂P =
          ∫ y, y ^ (2 * j + 1) ∂gaussianReal 0 ⟨V x.1, hV0 x.1⟩ :=
        (hlaw x.1 x.2).integral_comp (f := fun y : ℝ => y ^ (2 * j + 1))
          (continuous_pow (2 * j + 1)).aestronglyMeasurable
      rw [h1]
      exact integral_pow_odd_gaussianReal ⟨V x.1, hV0 x.1⟩ j
    rw [hl, mul_zero]
  have hF0 : ∫ o, F o ∂P = 0 :=
    eq_of_mem_closure_jetRange_of_jetEval0_eq one_pos hmem h0mem heval
  rw [h1, h2, hF0, map_zero]

end Grammar
