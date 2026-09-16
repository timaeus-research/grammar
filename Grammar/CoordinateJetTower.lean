/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# A coordinate `C¹` tower is a `C^R` jet

A family `h k b : ℝ^d → ℝ` indexed by coordinate words `b : Fin k → Fin d`, `k ≤ R`, such that
each `h k b` (`k < R`) is differentiable on an open set `U` with
`D(h k b)(u) = ∑ⱼ h (k+1) (j :: b) u · dxⱼ`, is the tower of coordinate derivatives of its root:
`h 0 ∅` is `C^R` on `U` and `D^k (h 0 ∅)(u)[e_{b 0}, …, e_{b (k−1)}] = h k b u`. The representation
`D^m (h 0 ∅)(u) = ∑_b h m b u • (v ↦ ∏ᵢ vᵢ(bᵢ))` is proved by induction on `m` and the recursive
formula `iteratedFDeriv_succ_eq_comp_left`.

This is the deterministic input for synchronising samplewise first-derivative representatives of an
`Lˢ`-valued analytic kernel into one smooth representative (the grey-book bridge, Stage B).
-/

open Filter Topology

namespace Grammar

variable {d : ℕ}

/-- The linear form `v ↦ ∑ⱼ cⱼ vⱼ` on `ℝ^d`. -/
noncomputable def coordLinear (c : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j, c j • ContinuousLinearMap.proj j

theorem coordLinear_apply (c v : Fin d → ℝ) : coordLinear c v = ∑ j, c j * v j := by
  simp [coordLinear]

theorem coordLinear_single (c : Fin d → ℝ) (j : Fin d) :
    coordLinear c (Pi.single j 1) = c j := by
  rw [coordLinear_apply, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

/-- The coordinate monomial multilinear map `v ↦ ∏ᵢ vᵢ (bᵢ)`. -/
noncomputable def coordMono (k : ℕ) (b : Fin k → Fin d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
    fun i => ContinuousLinearMap.proj (b i)

theorem coordMono_apply (k : ℕ) (b : Fin k → Fin d) (v : Fin k → Fin d → ℝ) :
    coordMono k b v = ∏ i, v i (b i) := by
  simp [coordMono]

theorem coordMono_single (k : ℕ) (b b' : Fin k → Fin d) :
    coordMono k b' (fun i => Pi.single (b i) (1 : ℝ)) = if b = b' then 1 else 0 := by
  rw [coordMono_apply]
  simp only [Pi.single_apply]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies]
  exact propext ⟨fun h => (funext h).symm, fun h i => (congrFun h i).symm⟩

section Tower

variable {U : Set (Fin d → ℝ)} {R : ℕ} {h : (k : ℕ) → (Fin k → Fin d) → (Fin d → ℝ) → ℝ}

/-- The iterated derivatives of the root of a coordinate `C¹` tower are the coordinate sums of
the tower. -/
theorem iteratedFDeriv_eq_sum_coordMono (hU : IsOpen U)
    (hd : ∀ k < R, ∀ b, ∀ u ∈ U,
      HasFDerivAt (h k b) (coordLinear fun j => h (k + 1) (Fin.cons j b) u) u) :
    ∀ m ≤ R, ∀ u ∈ U,
      iteratedFDeriv ℝ m (h 0 Fin.elim0) u = ∑ b, h m b u • coordMono m b := by
  intro m
  induction m with
  | zero =>
    intro _ u _
    ext v
    rw [Fintype.sum_eq_single (Fin.elim0 : Fin 0 → Fin d) fun b hb =>
      absurd (funext fun i => i.elim0) hb]
    simp [coordMono_apply, iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro hm u hu
    have hm' : m ≤ R := (Nat.le_succ m).trans hm
    have hmR : m < R := hm
    have heq : iteratedFDeriv ℝ m (h 0 Fin.elim0) =ᶠ[𝓝 u]
        fun u' => ∑ b, h m b u' • coordMono m b :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hu) fun u' hu' => ih hm' u' hu'
    have hder : HasFDerivAt (fun u' => ∑ b, h m b u' • coordMono m b)
        (∑ b, (coordLinear fun j => h (m + 1) (Fin.cons j b) u).smulRight (coordMono m b)) u := by
      have := HasFDerivAt.sum (u := Finset.univ) fun b _ =>
        (hd m hmR b u hu).smul_const (coordMono m b)
      rwa [Finset.sum_fn] at this
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq, hder.fderiv]
    ext v
    rw [continuousMultilinearCurryLeftEquiv_symm_apply]
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
      coordMono_apply, coordLinear_apply]
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin d) _ _ fun _ => rfl,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.tail]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

/-- **A coordinate `C¹` tower is `C^R`.** -/
theorem contDiffOn_of_coordTower (hU : IsOpen U)
    (hc : ∀ k ≤ R, ∀ b, ContinuousOn (h k b) U)
    (hd : ∀ k < R, ∀ b, ∀ u ∈ U,
      HasFDerivAt (h k b) (coordLinear fun j => h (k + 1) (Fin.cons j b) u) u) :
    ContDiffOn ℝ R (h 0 Fin.elim0) U := by
  have hsum := iteratedFDeriv_eq_sum_coordMono hU hd
  have hcast : ∀ m : ℕ, (m : ℕ∞) ≤ (R : ℕ∞) ↔ m ≤ R := fun m => by exact_mod_cast Iff.rfl
  have hcast' : ∀ m : ℕ, (m : ℕ∞) < (R : ℕ∞) ↔ m < R := fun m => by exact_mod_cast Iff.rfl
  refine contDiffOn_of_continuousOn_differentiableOn (n := (R : ℕ∞)) ?_ ?_
  · intro m hm
    refine ContinuousOn.congr (f := fun u => ∑ b, h m b u • coordMono m b) ?_
      fun u hu => by rw [iteratedFDerivWithin_of_isOpen m hU hu, hsum m ((hcast m).1 hm) u hu]
    exact continuousOn_finsetSum _ fun b _ => (hc m ((hcast m).1 hm) b).smul continuousOn_const
  · intro m hm
    have hmR : m < R := (hcast' m).1 hm
    refine DifferentiableOn.congr (f := fun u => ∑ b, h m b u • coordMono m b) ?_
      fun u hu => by rw [iteratedFDerivWithin_of_isOpen m hU hu, hsum m hmR.le u hu]
    intro u hu
    have hder : HasFDerivAt (fun u' => ∑ b, h m b u' • coordMono m b)
        (∑ b, (coordLinear fun j => h (m + 1) (Fin.cons j b) u).smulRight (coordMono m b)) u := by
      have := HasFDerivAt.sum (u := Finset.univ) fun b _ =>
        (hd m hmR b u hu).smul_const (coordMono m b)
      rwa [Finset.sum_fn] at this
    exact hder.differentiableAt.differentiableWithinAt

/-- **The coordinate derivatives of the root are the tower**:
`D^m (h 0 ∅)(u)[e_{b 0}, …, e_{b (m−1)}] = h m b u`. -/
theorem iteratedFDeriv_coordTower_apply (hU : IsOpen U)
    (hd : ∀ k < R, ∀ b, ∀ u ∈ U,
      HasFDerivAt (h k b) (coordLinear fun j => h (k + 1) (Fin.cons j b) u) u)
    {m : ℕ} (hm : m ≤ R) (b : Fin m → Fin d) {u : Fin d → ℝ} (hu : u ∈ U) :
    iteratedFDeriv ℝ m (h 0 Fin.elim0) u (fun i => Pi.single (b i) (1 : ℝ)) = h m b u := by
  rw [iteratedFDeriv_eq_sum_coordMono hU hd m hm u hu, sum_apply]
  simp only [smul_apply, coordMono_single, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    simp [Ne.symm hb']
  · simp

end Tower

end Grammar
