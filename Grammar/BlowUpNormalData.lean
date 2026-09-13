/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BlowUpSpace
import Grammar.ResolvedNormalData

/-!
# Genuine normal data on the blow-up (B2)

The resolved normal data of the blow-up `U = {(x, P) : P x = x}` (`BlowUpSpace`): at a point
`s = (x, P)` of the stratum `S_I` the normal space is the span of the fixed line of `P` if `I` is
the divisor label and `⊥` if `I = ∅` (`normalLine`), the labelled conormal differential is the
inner product with the unit direction `u` of `P = u uᵀ` (`dirOf`), and the tubular germ is the
translation along the fibre, `Φ_s(w) = (x + w, P)` (`tubular`). This is an analytic tubular map
from the total normal bundle: the normal bundle of the exceptional divisor is the tautological
line bundle itself, and no global frame or global defining equation of `E` is used.

`blowUpNormalData d : ResolvedNormalData (blowUpGeometry d) (EuclideanSpace ℝ (Fin d))`.
-/

open Set Topology Filter

namespace Grammar

namespace BlowUpCube

variable {d : ℕ}

/-! ### The unit direction of a projector -/

/-- A unit vector `u` with `P = u uᵀ` (chosen). -/
noncomputable def dirOf (P : ↥(projBase d)) : Fin d → ℝ := Classical.choose P.2

theorem dirOf_mem (P : ↥(projBase d)) : dirOf P ∈ sphereSet d := (Classical.choose_spec P.2).1

theorem rankOneProj_dirOf (P : ↥(projBase d)) :
    rankOneProj (dirOf P) = (P : Matrix (Fin d) (Fin d) ℝ) := (Classical.choose_spec P.2).2

theorem sum_sq_dirOf (P : ↥(projBase d)) : ∑ k, dirOf P k ^ 2 = 1 := dirOf_mem P

theorem dirOf_ne_zero (P : ↥(projBase d)) : dirOf P ≠ 0 := by
  intro h
  have := sum_sq_dirOf P
  rw [h] at this
  simp at this

/-- The projector fixes its direction. -/
theorem mulVec_dirOf (P : ↥(projBase d)) :
    (P : Matrix (Fin d) (Fin d) ℝ).mulVec (dirOf P) = dirOf P := by
  rw [← rankOneProj_dirOf, rankOneProj_mulVec]
  have : ∑ j, dirOf P j * dirOf P j = 1 := by
    rw [← sum_sq_dirOf P]
    exact Finset.sum_congr rfl fun j _ => (sq _).symm
  rw [this, one_smul]

/-- The Euclidean unit direction. -/
noncomputable def edir (P : ↥(projBase d)) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (dirOf P)

theorem edir_ne_zero (P : ↥(projBase d)) : edir P ≠ 0 := by
  intro h
  apply dirOf_ne_zero P
  have := congrArg (fun w : EuclideanSpace ℝ (Fin d) => w.ofLp) h
  simpa [edir] using this

theorem inner_edir_self (P : ↥(projBase d)) : inner ℝ (edir P) (edir P) = 1 := by
  rw [← sum_sq_dirOf P]
  simp only [edir, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ => (sq _).symm

/-! ### The normal line and the tubular germ -/

/-- The projector of a point of the blow-up. -/
def projOf (s : BlowUpSpace d) : ↥(projBase d) := s.1.2

theorem mulVec_π (s : BlowUpSpace d) :
    (projOf s : Matrix (Fin d) (Fin d) ℝ).mulVec (π s) = π s := s.2

/-- The normal space of `S_I` at `s`: the span of the fixed line of `P_s`, indexed by the labels
in `I` (so `⊥` when `I = ∅`). -/
noncomputable def normalLine (I : Finset Unit) (s : BlowUpSpace d) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ (Set.range fun _ : ↥I => edir (projOf s))

theorem normalLine_empty (s : BlowUpSpace d) : normalLine ∅ s = ⊥ := by
  unfold normalLine
  rw [Set.range_eq_empty, Submodule.span_empty]

theorem normalLine_of_nonempty {I : Finset Unit} (hI : I.Nonempty) (s : BlowUpSpace d) :
    normalLine I s = Submodule.span ℝ {edir (projOf s)} := by
  unfold normalLine
  congr 1
  obtain ⟨i, hi⟩ := hI
  ext w
  constructor
  · rintro ⟨_, rfl⟩
    exact Set.mem_singleton _
  · intro h
    exact ⟨⟨i, hi⟩, (Set.mem_singleton_iff.1 h).symm⟩

theorem card_of_nonempty {I : Finset Unit} (hI : I.Nonempty) : I.card = 1 := by
  obtain ⟨i, hi⟩ := hI
  have : I = {()} := by
    ext j
    cases j
    cases i
    simp [hi]
  rw [this, Finset.card_singleton]

theorem finrank_normalLine (I : Finset Unit) (s : BlowUpSpace d) :
    Module.finrank ℝ (normalLine I s) = I.card := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · rw [normalLine_empty, finrank_bot, Finset.card_empty]
  · rw [normalLine_of_nonempty hI, finrank_span_singleton (edir_ne_zero _), card_of_nonempty hI]

/-- Points of the normal line are fixed by the projector. -/
theorem mulVec_of_mem_normalLine {I : Finset Unit} {s : BlowUpSpace d}
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ normalLine I s) :
    (projOf s : Matrix (Fin d) (Fin d) ℝ).mulVec w.ofLp = w.ofLp := by
  have hspan : normalLine I s ≤ Submodule.span ℝ {edir (projOf s)} := by
    unfold normalLine
    exact Submodule.span_mono (Set.range_subset_iff.2 fun _ => rfl)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hspan hw)
  simp only [edir, WithLp.ofLp_smul, Matrix.mulVec_smul, mulVec_dirOf]

/-- The tubular germ: translation along the fibre, `Φ_s(w) = (x + w, P)`. -/
def tubular (I : Finset Unit) (s : BlowUpSpace d) (w : normalLine I s) : BlowUpSpace d :=
  ⟨(π s + (w : EuclideanSpace ℝ (Fin d)).ofLp, projOf s), by
    rw [Matrix.mulVec_add, mulVec_π, mulVec_of_mem_normalLine w.2]⟩

theorem tubular_zero (I : Finset Unit) (s : BlowUpSpace d) : tubular I s 0 = s := by
  apply Subtype.ext
  apply Prod.ext
  · simp [tubular, π]
  · rfl

theorem continuous_tubular (I : Finset Unit) (s : BlowUpSpace d) : Continuous (tubular I s) :=
  Continuous.subtype_mk ((continuous_const.add ((PiLp.continuous_ofLp 2 _).comp
    continuous_subtype_val)).prodMk continuous_const) _

/-- The labelled conormal differential: the inner product with the unit direction. -/
noncomputable def conormal (I : Finset Unit) (s : BlowUpSpace d) (_ : ↥I) :
    Module.Dual ℝ (normalLine I s) :=
  (innerSL ℝ (edir (projOf s))).toLinearMap.domRestrict (normalLine I s)

theorem edir_mem_normalLine {I : Finset Unit} (hI : I.Nonempty) (s : BlowUpSpace d) :
    edir (projOf s) ∈ normalLine I s := by
  rw [normalLine_of_nonempty hI]
  exact Submodule.mem_span_singleton_self _

theorem linearIndependent_conormal (I : Finset Unit) (s : BlowUpSpace d) :
    LinearIndependent ℝ (conormal I s) := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · have : IsEmpty ↥(∅ : Finset Unit) := Finset.isEmpty_coe_sort.2 rfl
    exact linearIndependent_empty_type
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hI' : ∀ j : ↥I, j = i := fun j => Subtype.ext (Subsingleton.elim _ _)
    rw [Finset.sum_eq_single i (fun j _ hj => (hj (hI' j)).elim)
      (fun h => (h (Finset.mem_univ i)).elim)] at hg
    have := congrArg (fun f : Module.Dual ℝ (normalLine I s) => f ⟨_, edir_mem_normalLine hI s⟩) hg
    simp only [LinearMap.smul_apply, conormal, LinearMap.domRestrict_apply,
      ContinuousLinearMap.coe_coe, LinearMap.zero_apply, smul_eq_mul] at this
    have h1 : (innerSL ℝ (edir (projOf s))) (edir (projOf s)) = 1 := inner_edir_self _
    rw [h1, mul_one] at this
    exact this

/-- **The genuine normal data of the blow-up**: fixed lines of the projectors as normal spaces,
the inner product with the unit direction as conormal differential, fibre translation as tubular
germ. -/
noncomputable def blowUpNormalData (d : ℕ) :
    ResolvedNormalData (blowUpGeometry d) (EuclideanSpace ℝ (Fin d)) where
  N := fun I s => normalLine I s.1
  finrank_N := fun I s => finrank_normalLine I s.1
  finiteDimensional_N := fun _ _ => inferInstance
  du := fun I s => conormal I s.1
  du_linearIndependent := fun I s => linearIndependent_conormal I s.1
  Φ := fun I s => tubular I s.1
  Φ_zero := fun I s => tubular_zero I s.1
  continuousAt_Φ := fun I s => (continuous_tubular I s.1).continuousAt

theorem blowUpNormalData_N (I : Finset Unit) (s : (blowUpGeometry d).Stratum I) :
    (blowUpNormalData d).N I s = normalLine I s.1 := rfl

theorem blowUpNormalData_Φ (I : Finset Unit) (s : (blowUpGeometry d).Stratum I)
    (w : (blowUpNormalData d).N I s) : (blowUpNormalData d).Φ I s w = tubular I s.1 w := rfl

theorem π_tubular (I : Finset Unit) (s : BlowUpSpace d) (w : normalLine I s) :
    π (tubular I s w) = π s + (w : EuclideanSpace ℝ (Fin d)).ofLp := rfl

end BlowUpCube

end Grammar
