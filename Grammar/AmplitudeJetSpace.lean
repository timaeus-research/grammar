/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.AmplitudeFunctional
import Grammar.JetHolonomy
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The population coefficient as a continuous linear functional on the jet space

The cube jets of smooth amplitudes form a submodule `jetRange d R b` of the Banach space
`CubeJetSpace d R b` (`cubeJet_add`, `cubeJet_smul`, `cubeJet_zero`).  On it the zero-field
coefficient `η ↦ empCoeff η 0 h k μ q` is a well-defined bounded linear functional
(`AmplitudeFunctional`: jet-locality, linearity, the jet-norm bound); Hahn–Banach extends it to
the whole jet space:

★★ `exists_popCoeffCLM`: there is `Φ : CubeJetSpace d R 1 →L[ℝ] ℝ` with
`Φ (cubeJet R 1 η hη) = empCoeff η 0 h k μ q` for every smooth `η` (`R ≥ Σ p_i`, `μ` on the
lattice below `L`, `q ≤ d − 1`).

Only the values of `Φ` on the closed jet range matter downstream (`GaussianAveraging`).

Zero `sorry`/`axiom`.
-/

open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ}

noncomputable instance instNormedSpaceCubeJetSpace (R : ℕ) (b : ℝ) :
    NormedSpace ℝ (CubeJetSpace d R b) :=
  inferInstanceAs (NormedSpace ℝ (∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

instance instCompleteSpaceCubeJetSpace (R : ℕ) (b : ℝ) : CompleteSpace (CubeJetSpace d R b) :=
  inferInstanceAs (CompleteSpace (∀ r : Fin (R + 1),
    ContinuousMap (closedBox d b) (ContinuousMultilinearMap ℝ (fun _ : Fin r.1 => Fin d → ℝ) ℝ)))

theorem cubeJet_add (R : ℕ) (b : ℝ) {η ξ : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hξ : ContDiff ℝ ∞ ξ) :
    cubeJet R b (fun v => η v + ξ v) (hη.add hξ) = cubeJet R b η hη + cubeJet R b ξ hξ := by
  funext r
  refine ContinuousMap.ext fun x => ?_
  change iteratedFDeriv ℝ r.1 (fun v => η v + ξ v) x.1 =
    iteratedFDeriv ℝ r.1 η x.1 + iteratedFDeriv ℝ r.1 ξ x.1
  exact iteratedFDeriv_add_apply (hη.contDiffAt.of_le (by exact_mod_cast le_top))
    (hξ.contDiffAt.of_le (by exact_mod_cast le_top))

theorem cubeJet_smul (R : ℕ) (b : ℝ) {η : (Fin d → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (c : ℝ) :
    cubeJet R b (fun v => c * η v) (contDiff_const.mul hη) = c • cubeJet R b η hη := by
  funext r
  refine ContinuousMap.ext fun x => ?_
  change iteratedFDeriv ℝ r.1 (fun v => c * η v) x.1 = c • iteratedFDeriv ℝ r.1 η x.1
  have hfun : (fun v => c * η v) = c • η := by
    funext v
    simp
  rw [hfun]
  exact iteratedFDeriv_const_smul_apply (hη.contDiffAt.of_le (by exact_mod_cast le_top))

theorem cubeJet_zero (R : ℕ) (b : ℝ) :
    cubeJet R b (fun _ => (0 : ℝ)) contDiff_const = (0 : CubeJetSpace d R b) := by
  funext r
  refine ContinuousMap.ext fun x => ?_
  change iteratedFDeriv ℝ r.1 (fun _ => (0 : ℝ)) x.1 = 0
  rw [iteratedFDeriv_fun_zero]
  rfl

/-- The submodule of cube jets of smooth amplitudes. -/
def jetRange (d R : ℕ) (b : ℝ) : Submodule ℝ (CubeJetSpace d R b) where
  carrier := jetSet d R b
  add_mem' := by
    rintro _ _ ⟨⟨η, hη⟩, rfl⟩ ⟨⟨ξ, hξ⟩, rfl⟩
    exact ⟨⟨fun v => η v + ξ v, hη.add hξ⟩, cubeJet_add R b hη hξ⟩
  zero_mem' := ⟨⟨fun _ => 0, contDiff_const⟩, cubeJet_zero R b⟩
  smul_mem' := by
    rintro c _ ⟨⟨η, hη⟩, rfl⟩
    exact ⟨⟨fun v => c * η v, contDiff_const.mul hη⟩, cubeJet_smul R b hη c⟩

theorem coe_jetRange (d R : ℕ) (b : ℝ) :
    (jetRange d R b : Set (CubeJetSpace d R b)) = jetSet d R b := rfl

/-- A smooth representative of an element of the jet range. -/
noncomputable def jetRep {R : ℕ} {b : ℝ} (z : jetRange d R b) :
    {η : (Fin d → ℝ) → ℝ // ContDiff ℝ ∞ η} :=
  Classical.choose z.2

theorem cubeJet_jetRep {R : ℕ} {b : ℝ} (z : jetRange d R b) :
    cubeJet R b (jetRep z).1 (jetRep z).2 = z.1 :=
  Classical.choose_spec z.2

variable {h k p : Fin d → ℕ}

/-- ★★ **The population coefficient extends to a continuous linear functional on the jet
space** taking the value `empCoeff η 0 h k μ q` on the jet of every smooth amplitude `η`. -/
theorem exists_popCoeffCLM (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {R : ℕ} (hR : ∑ i, p i ≤ R) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ} (hq : q ≤ d - 1) :
    ∃ Φ : CubeJetSpace d R 1 →L[ℝ] ℝ, ∀ (η : (Fin d → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η),
      Φ (cubeJet R 1 η hη) = empCoeff η (fun _ => 0) h k μ q := by
  have hQ := Qamb_pos k hk
  have hμ' : ∃ m : ℕ, μ = (m : ℝ) / Qamb k := ((mem_latticeBelow_iff hQ).1 hμ).1
  obtain ⟨K, hK0, hK⟩ := exists_abs_empCoeff_zero_le_norm_cubeJet hk hL hp hp0 hR
  -- the functional on the jet range, through representatives
  have hrep : ∀ (z : jetRange d R 1) (η : (Fin d → ℝ) → ℝ) (hη : ContDiff ℝ ∞ η),
      cubeJet R 1 η hη = z.1 →
        empCoeff (jetRep z).1 (fun _ => 0) h k μ q = empCoeff η (fun _ => 0) h k μ q :=
    fun z η hη hz => empCoeff_zero_eq_of_cubeJet_eq hk hL hp hp0 hR (jetRep z).2 hη
      ((cubeJet_jetRep z).trans hz.symm) hμ hq
  let f : jetRange d R 1 →ₗ[ℝ] ℝ :=
    { toFun := fun z => empCoeff (jetRep z).1 (fun _ => 0) h k μ q
      map_add' := by
        intro z₁ z₂
        have hz : cubeJet R 1 (fun v => (jetRep z₁).1 v + (jetRep z₂).1 v)
            ((jetRep z₁).2.add (jetRep z₂).2) = (z₁ + z₂).1 := by
          rw [cubeJet_add R 1 (jetRep z₁).2 (jetRep z₂).2, cubeJet_jetRep, cubeJet_jetRep]
          rfl
        change empCoeff (jetRep (z₁ + z₂)).1 (fun _ => 0) h k μ q =
          empCoeff (jetRep z₁).1 (fun _ => 0) h k μ q + empCoeff (jetRep z₂).1 (fun _ => 0) h k μ q
        rw [hrep (z₁ + z₂) _ _ hz]
        exact empCoeff_zero_add (jetRep z₁).2 (jetRep z₂).2 hk hL hp hp0 hμ hq
      map_smul' := by
        intro c z
        have hz : cubeJet R 1 (fun v => c * (jetRep z).1 v) (contDiff_const.mul (jetRep z).2) =
            (c • z).1 := by
          rw [cubeJet_smul R 1 (jetRep z).2 c, cubeJet_jetRep]
          rfl
        change empCoeff (jetRep (c • z)).1 (fun _ => 0) h k μ q =
          c * empCoeff (jetRep z).1 (fun _ => 0) h k μ q
        rw [hrep (c • z) _ _ hz]
        exact empCoeff_zero_smul (jetRep z).2 hk c hμ' hq }
  have hbound : ∀ z : jetRange d R 1, ‖f z‖ ≤ K * ‖z‖ := by
    intro z
    have h1 := hK (jetRep z).1 (jetRep z).2 μ hμ q hq
    rw [cubeJet_jetRep] at h1
    exact h1
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (jetRange d R 1) (f.mkContinuous K hbound)
  refine ⟨g, fun η hη => ?_⟩
  have hmem : cubeJet R 1 η hη ∈ jetRange d R 1 := cubeJet_mem_jetSet R 1 hη
  have := hg ⟨cubeJet R 1 η hη, hmem⟩
  rw [this]
  exact hrep ⟨cubeJet R 1 η hη, hmem⟩ η hη rfl

end Grammar
