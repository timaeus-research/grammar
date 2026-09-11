/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SplitBoxCore
import Grammar.ReflectedBoxExpansion

/-!
# Reflections of the normal coordinates along a splitting (towards the chart theorem)

The coordinate reflection `splitReflect σ s` of the ambient space `Fin d → ℝ` flips the normal
coordinates `nIdx σ j` according to the sign pattern `s` and fixes the tangential ones. It is a
continuous linear equivalence with `|det| = 1` (`abs_det_splitReflect`), an involution, and it
intertwines the product coordinates with the product-space reflection:
`splitReflect σ s ∘ prodToPi σ = prodToPi σ ∘ reflectChart s` (`splitReflect_prodToPi`). Hence the
`2^{n+1}` orthant images `splitReflect σ s '' splitPosBox σ A b` of the positive box are pairwise
disjoint (`disjoint_splitOrthant`) and cover the two-sided box `prodToPi σ '' (A × [-b,b]^{n+1})`
off the null coordinate hyperplanes (`ae_mem_iUnion_splitOrthant`, `ae_apply_nIdx_ne_zero`).

Non-claims: no chart composition yet.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

variable {t n d : ℕ} (σ : Fin t ⊕ Fin (n + 1) ≃ Fin d)

/-! ### The sign pattern on the ambient coordinates -/

/-- The sign pattern on the ambient coordinates: `boolSgn s` on the normal ones, `1` elsewhere. -/
def splitSgn (s : Fin (n + 1) → Bool) (x : Fin d) : ℝ :=
  Sum.elim (fun _ => (1 : ℝ)) (boolSgn s) (σ.symm x)

theorem splitSgn_nIdx (s : Fin (n + 1) → Bool) (j : Fin (n + 1)) :
    splitSgn σ s (nIdx σ j) = boolSgn s j := by
  simp [splitSgn, nIdx]

theorem splitSgn_tIdx (s : Fin (n + 1) → Bool) (i : Fin t) : splitSgn σ s (tIdx σ i) = 1 := by
  simp [splitSgn, tIdx]

theorem abs_splitSgn (s : Fin (n + 1) → Bool) (x : Fin d) : |splitSgn σ s x| = 1 := by
  unfold splitSgn
  rcases σ.symm x with i | j
  · simp
  · simp [abs_boolSgn]

theorem splitSgn_mul_self (s : Fin (n + 1) → Bool) (x : Fin d) :
    splitSgn σ s x * splitSgn σ s x = 1 := by
  unfold splitSgn
  rcases σ.symm x with i | j
  · simp
  · simp [boolSgn_mul_self]

theorem splitSgn_ne_zero (s : Fin (n + 1) → Bool) (x : Fin d) : splitSgn σ s x ≠ 0 := by
  intro h
  have := abs_splitSgn σ s x
  rw [h, abs_zero] at this
  exact zero_ne_one this

/-! ### The reflection -/

open scoped Classical in
/-- The reflection of the normal coordinates of the ambient space by the sign pattern `s`. -/
noncomputable def splitReflect (s : Fin (n + 1) → Bool) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun x =>
    if splitSgn σ s x = 1 then ContinuousLinearEquiv.refl ℝ ℝ else ContinuousLinearEquiv.neg ℝ

theorem splitSgn_eq_one_or_neg_one (s : Fin (n + 1) → Bool) (x : Fin d) :
    splitSgn σ s x = 1 ∨ splitSgn σ s x = -1 := by
  unfold splitSgn boolSgn
  rcases σ.symm x with i | j
  · simp
  · simp only [Sum.elim_inr]
    split_ifs <;> simp

theorem splitReflect_apply (s : Fin (n + 1) → Bool) (y : Fin d → ℝ) (x : Fin d) :
    splitReflect σ s y x = splitSgn σ s x * y x := by
  classical
  unfold splitReflect
  rw [ContinuousLinearEquiv.piCongrRight_apply]
  rcases splitSgn_eq_one_or_neg_one σ s x with h | h
  · simp [h]
  · rw [h, if_neg (by norm_num)]
    simp

theorem splitReflect_splitReflect (s : Fin (n + 1) → Bool) (y : Fin d → ℝ) :
    splitReflect σ s (splitReflect σ s y) = y := by
  funext x
  rw [splitReflect_apply, splitReflect_apply, ← mul_assoc, splitSgn_mul_self, one_mul]

/-- **The determinant of the reflection** is the product of the signs. -/
theorem det_splitReflect (s : Fin (n + 1) → Bool) :
    ((splitReflect σ s : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))).det = ∏ x, splitSgn σ s x := by
  have h : (((splitReflect σ s : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
      LinearMap.pi fun x => (splitSgn σ s x • LinearMap.id) ∘ₗ LinearMap.proj x := by
    apply LinearMap.ext
    intro y
    funext x
    simp [splitReflect_apply]
  unfold ContinuousLinearMap.det
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

theorem abs_det_splitReflect (s : Fin (n + 1) → Bool) :
    |((splitReflect σ s : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))).det| = 1 := by
  rw [det_splitReflect, Finset.abs_prod]
  simp [abs_splitSgn]

/-- The reflection intertwines the product coordinates with the product-space reflection. -/
theorem splitReflect_prodToPi (s : Fin (n + 1) → Bool) (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :
    splitReflect σ s (prodToPi σ p) = prodToPi σ (reflectChart s p) := by
  funext x
  obtain ⟨z, rfl⟩ := σ.surjective x
  rcases z with i | j
  · rw [splitReflect_apply, show σ (Sum.inl i) = tIdx σ i from rfl, splitSgn_tIdx, one_mul,
      prodToPi_apply_tIdx, prodToPi_apply_tIdx, reflectChart_apply]
  · rw [splitReflect_apply, show σ (Sum.inr j) = nIdx σ j from rfl, splitSgn_nIdx,
      prodToPi_apply_nIdx, prodToPi_apply_nIdx, reflectChart_apply]
    simp only [reflectEquiv_apply]

/-- The orthant images are the product coordinates of the reflected positive boxes. -/
theorem splitReflect_image_splitPosBox (s : Fin (n + 1) → Bool) (A : Set (Fin t → ℝ)) (b : ℝ) :
    splitReflect σ s '' splitPosBox σ A b =
      prodToPi σ '' (reflectChart s '' (A ×ˢ piBox (n + 1) (Ioc 0 b))) := by
  unfold splitPosBox
  rw [image_image, image_image]
  refine image_congr fun p _ => ?_
  exact splitReflect_prodToPi σ s p

/-- **Disjointness of the orthants.** -/
theorem disjoint_splitOrthant {s s' : Fin (n + 1) → Bool} (h : s ≠ s') (A : Set (Fin t → ℝ))
    (b : ℝ) :
    Disjoint (splitReflect σ s '' splitPosBox σ A b) (splitReflect σ s' '' splitPosBox σ A b) := by
  rw [splitReflect_image_splitPosBox, splitReflect_image_splitPosBox,
    Set.disjoint_image_iff (prodToPi σ).injective]
  exact disjoint_orthant h A b

/-- Almost every point of the ambient space has all normal coordinates nonzero. -/
theorem ae_apply_nIdx_ne_zero :
    ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), ∀ j, y (nIdx σ j) ≠ 0 := by
  rw [ae_all_iff]
  intro j
  rw [ae_iff]
  have h1 : {y : Fin d → ℝ | ¬ y (nIdx σ j) ≠ 0} = {y | y (nIdx σ j) = 0} := by
    ext y
    simp
  rw [h1, volume_pi]
  exact Measure.pi_hyperplane _ (nIdx σ j) 0

/-- **Coverage of the two-sided box by the orthants** off the null coordinate hyperplanes. -/
theorem mem_iUnion_splitOrthant {A : Set (Fin t → ℝ)} {b : ℝ} {y : Fin d → ℝ}
    (hy : y ∈ prodToPi σ '' twoSidedBox A b) (hne : ∀ j, y (nIdx σ j) ≠ 0) :
    y ∈ ⋃ s : Fin (n + 1) → Bool, splitReflect σ s '' splitPosBox σ A b := by
  obtain ⟨p, hp, rfl⟩ := hy
  set s : Fin (n + 1) → Bool := fun j => decide (0 < p.2 j) with hs
  refine mem_iUnion.2 ⟨s, ?_⟩
  rw [splitReflect_image_splitPosBox]
  refine ⟨p, ?_, rfl⟩
  rw [mem_reflectChart_image_iff]
  refine ⟨hp.1, fun j => ?_⟩
  have hpj := hp.2 j (mem_univ j)
  have hnz : p.2 j ≠ 0 := by
    have := hne j
    rwa [prodToPi_apply_nIdx] at this
  have hpos : 0 < boolSgn s j * p.2 j := by
    simp only [hs, boolSgn]
    by_cases h : 0 < p.2 j
    · simp [h]
    · have hlt : p.2 j < 0 := lt_of_le_of_ne (not_lt.1 h) hnz
      simp [h]
      linarith
  refine ⟨hpos, ?_⟩
  have habs : boolSgn s j * p.2 j = |p.2 j| := by
    rw [← abs_of_pos hpos, abs_mul, abs_boolSgn, one_mul]
  rw [habs, abs_le]
  exact ⟨hpj.1, hpj.2⟩

end Grammar
