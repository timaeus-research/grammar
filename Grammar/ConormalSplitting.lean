import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Fibrewise conormal exactness and the labelled line splitting (Astra #63 unit 2)

The paper's `subsec:normal_crossing` splits the conormal bundle of a transverse intersection
`X = Y₁ ∩ ⋯ ∩ Y_k` of divisors as `N*X ≅ ⊕ᵢ 𝓛ᵢ` (`eq:decomp_nx`), where `𝓛ᵢ` is the line spanned by
`duᵢ` for any local defining equation `uᵢ` of `Yᵢ`. We formalise the **pointwise** linear algebra
at a point `p ∈ X`, with `ℓ i = (duᵢ)_p ∈ E*` the differentials of the defining equations:

* the tangent space `T_pX = ⋂ᵢ ker ℓᵢ` (`tangentOf`), the conormal space `N*_pX = (T_pX)^⊥ ⊆ E*`
  as the annihilator, i.e. the dual of the conormal sequence `eq:conormal_sequence`
  (`conormalOf`, `conormalOf_equiv_dual_quot`), and the labelled lines `𝓛ᵢ = ℝ·ℓᵢ` (`conormalLine`);
* **exactness**: the annihilator of `⋂ ker ℓᵢ` is the span of the `ℓᵢ` (`conormalOf_eq_span`), so
  `N*_pX = ⨆ᵢ 𝓛ᵢ` (`conormalOf_eq_iSup_conormalLine`);
* **the labelled splitting** `eq:decomp_nx`: for independent differentials the lines are independent
  (`iSupIndep_conormalLine`) and the sum map is a linear equivalence
  `⊕ᵢ 𝓛ᵢ ≃ N*_pX` (`conormalSplitting`, `conormalSplitting_of`); in coordinates `ℝ^k ≃ N*_pX`,
  `c ↦ ∑ cᵢ ℓᵢ` (`conormalCoordEquiv`, `conormalCoordEquiv_apply`); the normal space
  `N_pX = E / T_pX ≃ ℝ^k` through `(ℓᵢ)ᵢ` (`normalQuotEquiv`);
* **line invariance under units**: if `u'ᵢ = gᵢ uᵢ` with `gᵢ(p) ≠ 0` and `uᵢ(p) = 0` then
  `du'ᵢ(p) = gᵢ(p) duᵢ(p)` (`fderiv_mul_of_eq_zero`), so the lines, the tangent space and the
  conormal space are unchanged (`conormalLine_smul`, `tangentOf_smul`, `conormalOf_smul`,
  `conormalLine_unit_mul`);
* **orthogonal normal = annihilator**: in an inner product space `x ∈ Kᗮ ↔ ⟪x,·⟫ ∈ K^⊥`
  (`mem_orthogonal_iff_toDual_mem_dualAnnihilator`), and for gradient differentials
  `ℓᵢ = ⟪vᵢ,·⟫` the tangent space is `(span vᵢ)ᗮ` and its orthogonal complement is `span vᵢ`
  (`tangentOf_toDual`, `orthogonal_tangentOf_toDual`) — the Riesz normal space of the StrucDual
  presentation `normalSpaceOf J = range Jᵀ` is the conormal space read through the metric.

Non-claims: no quotient vector bundle, no regularity of the submodule field `p ↦ T_pX`, no
divisors or manifolds — everything is at a single point `p`, as `eq:decomp_nx` is a fibrewise
statement.
-/

open Module
open scoped DirectSum

namespace Grammar

section Pointwise

variable {ι : Type*} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The pointwise tangent space** `T_pX = ⋂ᵢ ker (duᵢ)_p` of the differentials `ℓ`. -/
def tangentOf (ℓ : ι → Dual ℝ E) : Submodule ℝ E := ⨅ i, LinearMap.ker (ℓ i)

/-- **The pointwise conormal space** `N*_pX = (T_pX)^⊥ ⊆ E*` (the annihilator of the tangent
space: the dual of the conormal sequence). -/
def conormalOf (ℓ : ι → Dual ℝ E) : Submodule ℝ (Dual ℝ E) := (tangentOf ℓ).dualAnnihilator

/-- **The labelled conormal line** `𝓛ᵢ = ℝ · (duᵢ)_p`. -/
def conormalLine (ℓ : ι → Dual ℝ E) (i : ι) : Submodule ℝ (Dual ℝ E) := ℝ ∙ ℓ i

variable (ℓ : ι → Dual ℝ E)

theorem mem_tangentOf {x : E} : x ∈ tangentOf ℓ ↔ ∀ i, ℓ i x = 0 := by
  simp [tangentOf, Submodule.mem_iInf]

theorem tangentOf_eq_ker_pi : tangentOf ℓ = LinearMap.ker (LinearMap.pi ℓ) :=
  (LinearMap.ker_pi ℓ).symm

theorem mem_conormalOf {φ : Dual ℝ E} : φ ∈ conormalOf ℓ ↔ ∀ x ∈ tangentOf ℓ, φ x = 0 :=
  Submodule.mem_dualAnnihilator φ

theorem conormalLine_le_conormalOf (i : ι) : conormalLine ℓ i ≤ conormalOf ℓ := by
  rw [conormalLine, Submodule.span_singleton_le_iff_mem, mem_conormalOf]
  intro x hx
  exact (mem_tangentOf ℓ).1 hx i

/-- **The dual conormal sequence**: `N*_pX = (E / T_pX)*`. -/
noncomputable def conormalOf_equiv_dual_quot : Dual ℝ (E ⧸ tangentOf ℓ) ≃ₗ[ℝ] conormalOf ℓ :=
  Submodule.dualQuotEquivDualAnnihilator _

/-- **Fibrewise exactness**: the annihilator of `⋂ᵢ ker ℓᵢ` is the span of the `ℓᵢ`. -/
theorem conormalOf_eq_span [Finite ι] : conormalOf ℓ = Submodule.span ℝ (Set.range ℓ) := by
  apply le_antisymm
  · intro φ hφ
    exact mem_span_of_iInf_ker_le_ker fun x hx => (mem_conormalOf ℓ).1 hφ x hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact conormalLine_le_conormalOf ℓ i (Submodule.mem_span_singleton_self _)

theorem conormalOf_eq_iSup_conormalLine [Finite ι] : conormalOf ℓ = ⨆ i, conormalLine ℓ i := by
  rw [conormalOf_eq_span, Submodule.span_range_eq_iSup]
  rfl

theorem iSupIndep_conormalLine (h : LinearIndependent ℝ ℓ) : iSupIndep (conormalLine ℓ) :=
  h.iSupIndep_span_singleton

section DirectSumSplitting

variable [DecidableEq ι]

theorem coeLinearMap_conormalLine_injective (h : LinearIndependent ℝ ℓ) :
    Function.Injective (DirectSum.coeLinearMap (conormalLine ℓ)) :=
  (iSupIndep_conormalLine ℓ h).dfinsupp_lsum_injective

/-- **`eq:decomp_nx`, pointwise**: for independent differentials the sum of the labelled lines is a
linear equivalence `⊕ᵢ 𝓛ᵢ ≃ N*_pX`. -/
noncomputable def conormalSplitting [Finite ι] (h : LinearIndependent ℝ ℓ) :
    (⨁ i, conormalLine ℓ i) ≃ₗ[ℝ] conormalOf ℓ :=
  (LinearEquiv.ofInjective _ (coeLinearMap_conormalLine_injective ℓ h)).trans
    (LinearEquiv.ofEq _ _ (by rw [DirectSum.range_coeLinearMap, conormalOf_eq_iSup_conormalLine]))

theorem conormalSplitting_apply [Finite ι] (h : LinearIndependent ℝ ℓ)
    (x : ⨁ i, conormalLine ℓ i) :
    (conormalSplitting ℓ h x : Dual ℝ E) = DirectSum.coeLinearMap (conormalLine ℓ) x := rfl

theorem conormalSplitting_of [Finite ι] (h : LinearIndependent ℝ ℓ) (i : ι) (v : conormalLine ℓ i) :
    (conormalSplitting ℓ h (DirectSum.of (fun i => conormalLine ℓ i) i v) : Dual ℝ E) = v := by
  rw [conormalSplitting_apply, DirectSum.coeLinearMap_of]

end DirectSumSplitting

/-- **Coordinates on the conormal space**: `ℝ^k ≃ N*_pX`, `c ↦ ∑ᵢ cᵢ ℓᵢ`. -/
noncomputable def conormalCoordEquiv [Fintype ι] (h : LinearIndependent ℝ ℓ) :
    (ι → ℝ) ≃ₗ[ℝ] conormalOf ℓ :=
  (Basis.span h).equivFun.symm.trans (LinearEquiv.ofEq _ _ (conormalOf_eq_span ℓ).symm)

theorem conormalCoordEquiv_apply [Fintype ι] (h : LinearIndependent ℝ ℓ) (c : ι → ℝ) :
    (conormalCoordEquiv ℓ h c : Dual ℝ E) = ∑ i, c i • ℓ i := by
  simp [conormalCoordEquiv, Basis.equivFun_symm_apply, Basis.span_apply]

end Pointwise

section Quotient

variable {ι : Type*} [Finite ι] {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable (ℓ : ι → Dual ℝ E)

/-- Independent differentials evaluate onto `ℝ^k`. -/
theorem surjective_pi_of_linearIndependent (h : LinearIndependent ℝ ℓ) :
    Function.Surjective (LinearMap.pi ℓ) := by
  have := Fintype.ofFinite ι
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi ℓ)
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (tangentOf ℓ)
  have h3 : finrank ℝ (tangentOf ℓ).dualAnnihilator = Fintype.card ι := by
    rw [← conormalOf, conormalOf_eq_span]
    exact finrank_span_eq_card h
  rw [← tangentOf_eq_ker_pi] at h1
  rw [Module.finrank_fintype_fun_eq_card]
  omega

/-- **The pointwise normal space** `N_pX = E / T_pX ≃ ℝ^k` through the differentials. -/
noncomputable def normalQuotEquiv (h : LinearIndependent ℝ ℓ) : (E ⧸ tangentOf ℓ) ≃ₗ[ℝ] (ι → ℝ) :=
  (Submodule.quotEquivOfEq _ _ (tangentOf_eq_ker_pi ℓ)).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_pi_of_linearIndependent ℓ h))

theorem normalQuotEquiv_mk (h : LinearIndependent ℝ ℓ) (x : E) :
    normalQuotEquiv ℓ h (Submodule.Quotient.mk x) = fun i => ℓ i x := rfl

end Quotient

section Units

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tangentOf_smul (ℓ : ι → Dual ℝ E) (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    tangentOf (fun i => c i • ℓ i) = tangentOf ℓ := by
  unfold tangentOf
  simp_rw [LinearMap.ker_smul _ _ (hc _)]

theorem conormalOf_smul (ℓ : ι → Dual ℝ E) (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    conormalOf (fun i => c i • ℓ i) = conormalOf ℓ := by
  unfold conormalOf
  rw [tangentOf_smul ℓ c hc]

theorem conormalLine_smul (ℓ : ι → Dual ℝ E) (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) (i : ι) :
    conormalLine (fun i => c i • ℓ i) i = conormalLine ℓ i :=
  Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (hc i)) _

/-- The product rule on the vanishing locus: `d(g·u)_p = g(p) du_p` when `u(p) = 0`. -/
theorem hasFDerivAt_mul_of_eq_zero {g u : E → ℝ} {g' u' : E →L[ℝ] ℝ} {p : E}
    (hg : HasFDerivAt g g' p) (hu : HasFDerivAt u u' p) (hu0 : u p = 0) :
    HasFDerivAt (fun x => g x * u x) (g p • u') p := by
  have h := hg.mul hu
  rw [hu0, zero_smul, add_zero] at h
  exact h

theorem fderiv_mul_of_eq_zero {g u : E → ℝ} {p : E} (hg : DifferentiableAt ℝ g p)
    (hu : DifferentiableAt ℝ u p) (hu0 : u p = 0) :
    fderiv ℝ (fun x => g x * u x) p = g p • fderiv ℝ u p :=
  (hasFDerivAt_mul_of_eq_zero hg.hasFDerivAt hu.hasFDerivAt hu0).fderiv

/-- **Line invariance under changes of defining equation by units**: the conormal line of
`u' = g · u` at a point of `{u = 0}` with `g(p) ≠ 0` is the conormal line of `u`. -/
theorem conormalLine_unit_mul {g u : E → ℝ} {p : E} (hg : DifferentiableAt ℝ g p)
    (hu : DifferentiableAt ℝ u p) (hu0 : u p = 0) (hg0 : g p ≠ 0) :
    (ℝ ∙ ((fderiv ℝ (fun x => g x * u x) p : E →L[ℝ] ℝ) : Dual ℝ E)) =
      ℝ ∙ ((fderiv ℝ u p : E →L[ℝ] ℝ) : Dual ℝ E) := by
  rw [fderiv_mul_of_eq_zero hg hu hu0, ContinuousLinearMap.toLinearMap_smul,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hg0)]

end Units

section Orthogonal

open InnerProductSpace

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Orthogonal complement = annihilator through Riesz**: `x ∈ Kᗮ ↔ ⟪x,·⟫ ∈ K^⊥`. -/
theorem mem_orthogonal_iff_toDual_mem_dualAnnihilator (K : Submodule ℝ E) (x : E) :
    x ∈ Kᗮ ↔ ((toDual ℝ E x : E →L[ℝ] ℝ) : Dual ℝ E) ∈ K.dualAnnihilator := by
  simp only [Submodule.mem_orthogonal', Submodule.mem_dualAnnihilator,
    ContinuousLinearMap.coe_coe, toDual_apply_apply]

/-- For gradient differentials `ℓᵢ = ⟪vᵢ,·⟫` the tangent space is the orthogonal complement of the
span of the gradients. -/
theorem tangentOf_toDual (v : ι → E) :
    tangentOf (fun i => ((toDual ℝ E (v i) : E →L[ℝ] ℝ) : Dual ℝ E)) =
      (Submodule.span ℝ (Set.range v))ᗮ := by
  ext x
  rw [mem_tangentOf, Submodule.span_range_eq_iSup, ← Submodule.iInf_orthogonal,
    Submodule.mem_iInf]
  simp only [ContinuousLinearMap.coe_coe, toDual_apply_apply,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- **The Riesz normal space is the span of the gradients** (the StrucDual presentation
`normalSpaceOf J = range Jᵀ`): `(T_pX)ᗮ = span vᵢ` in finite dimension. -/
theorem orthogonal_tangentOf_toDual [FiniteDimensional ℝ E] (v : ι → E) :
    (tangentOf (fun i => ((toDual ℝ E (v i) : E →L[ℝ] ℝ) : Dual ℝ E)))ᗮ =
      Submodule.span ℝ (Set.range v) := by
  rw [tangentOf_toDual, Submodule.orthogonal_orthogonal]

end Orthogonal

end Grammar
