/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SignedBoxPackets

/-!
# The orthant decomposition of the signed-box integral (CCCXXXVII; phase G, unit G2)

Consult #100 §3, §6. Almost every point of `ℝ^d` has all coordinates nonzero (`ae_coord_ne_zero`,
the coordinate hyperplanes are Lebesgue-null), so almost every point of the signed box
`[−a,a]^d` lies in exactly one orthant piece `orthantBox σ a = R_σ⁻¹ [0,a]^d`. Hence, for an
integrand integrable on the signed box, `∫_{[−a,a]^d} g = ∑_σ ∫_{orthantBox σ} g`
(`setIntegral_signedBox_eq_sum`, via an a.e. indicator identity and finite additivity), and each
piece is the positive-box integral of the reflected integrand (`setIntegral_orthantBox`). For a
phase even in every coordinate this gives the Laplace integral decomposition
`L_{[−a,a]^d}(K, f)(n) = ∑_σ L_{[0,a]^d}(K, f ∘ R_σ)(n)` (★ `globalLaplace_signedBox_eq_sum`), in
particular for the monomial phase (`globalLaplace_signedBox_phase`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace WaterFilling

open CoordModel

variable {d : ℕ}

/-- Almost every point has all coordinates nonzero. -/
theorem ae_coord_ne_zero : ∀ᵐ w : Fin d → ℝ ∂volume, ∀ i, w i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : (volume : Measure (Fin d → ℝ)) {w | w i = 0} = 0 := by
    rw [volume_pi]
    exact Measure.pi_hyperplane (μ := fun _ : Fin d => (volume : Measure ℝ)) i (0 : ℝ)
  rw [ae_iff]
  convert h using 2
  ext w
  simp

theorem measurableSet_signedBox (a : ℝ) : MeasurableSet (piBox d (Icc (-a) a)) :=
  measurableSet_piBox d _ measurableSet_Icc

variable (a : ℝ)

/-- **The orthant decomposition of a signed-box integral.** -/
theorem setIntegral_signedBox_eq_sum (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (piBox d (Icc (-a) a))) :
    ∫ w in piBox d (Icc (-a) a), g w = ∑ σ : CoordSign d, ∫ w in orthantBox σ a, g w := by
  have hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℝ)),
      (piBox d (Icc (-a) a)).indicator g w = ∑ σ : CoordSign d, (orthantBox σ a).indicator g w := by
    filter_upwards [ae_coord_ne_zero] with w hw
    by_cases hS : w ∈ piBox d (Icc (-a) a)
    · rw [indicator_of_mem hS, Finset.sum_eq_single (signOf w)]
      · rw [indicator_of_mem (mem_orthantBox_signOf hS)]
      · intro σ _ hσ
        rw [indicator_of_notMem]
        intro h
        exact hσ (eq_signOf_of_mem_orthantBox hw h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [indicator_of_notMem hS]
      symm
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [indicator_of_notMem]
      intro h
      exact hS (orthantBox_subset σ a h)
  calc ∫ w in piBox d (Icc (-a) a), g w
      = ∫ w, (piBox d (Icc (-a) a)).indicator g w :=
        (integral_indicator (measurableSet_signedBox a)).symm
    _ = ∫ w, ∑ σ : CoordSign d, (orthantBox σ a).indicator g w := integral_congr_ae hae
    _ = ∑ σ : CoordSign d, ∫ w, (orthantBox σ a).indicator g w :=
        integral_finsetSum _ fun σ _ =>
          (hg.mono_set (orthantBox_subset σ a)).integrable_indicator (measurableSet_orthantBox σ a)
    _ = ∑ σ : CoordSign d, ∫ w in orthantBox σ a, g w :=
        Finset.sum_congr rfl fun σ _ => integral_indicator (measurableSet_orthantBox σ a)

/-- An orthant-piece integral is the positive-box integral of the reflected integrand. -/
theorem setIntegral_orthantBox (σ : CoordSign d) (g : (Fin d → ℝ) → ℝ) :
    ∫ w in orthantBox σ a, g w = ∫ w in piBox d (Icc 0 a), g (refl σ w) := by
  rw [setIntegral_refl σ (fun w => g (refl σ w)) (piBox d (Icc 0 a))]
  simp only [refl_refl]
  rfl

/-- ★ **The Laplace integral over the signed box is the sum of the reflected positive-box
integrals**, for a phase even in every coordinate. -/
theorem globalLaplace_signedBox_eq_sum (K f : (Fin d → ℝ) → ℝ)
    (hK : ∀ (σ : CoordSign d) (w : Fin d → ℝ), K (refl σ w) = K w) (n : ℝ)
    (hf : IntegrableOn (fun w => f w * Real.exp (-n * K w)) (piBox d (Icc (-a) a))) :
    globalLaplace (piBox d (Icc (-a) a)) K f n =
      ∑ σ : CoordSign d, globalLaplace (piBox d (Icc 0 a)) K (f ∘ refl σ) n := by
  unfold globalLaplace
  rw [setIntegral_signedBox_eq_sum a _ hf]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [setIntegral_orthantBox a σ]
  simp only [Function.comp, hK]

/-- The Laplace decomposition for the monomial phase. -/
theorem globalLaplace_signedBox_phase (k : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) (n : ℝ)
    (hf : IntegrableOn (fun w => f w * Real.exp (-n * phase d k w)) (piBox d (Icc (-a) a))) :
    globalLaplace (piBox d (Icc (-a) a)) (phase d k) f n =
      ∑ σ : CoordSign d, globalLaplace (piBox d (Icc 0 a)) (phase d k) (f ∘ refl σ) n :=
  globalLaplace_signedBox_eq_sum a (phase d k) f (fun σ w => phase_refl k σ w) n hf

end WaterFilling

end Grammar
