import Grammar.NormalTaylorForm
import Grammar.TaylorMoment
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Symmetric weight decomposition and the factorial bridge (Astra #63 unit 3)

The paper decomposes the symmetric power of the conormal space by weights,
`Sym^r(N*X) ≅ ⊕_{|b|=r} ⊗ᵢ Sym^{bᵢ}(𝓛ᵢ)` (`eq:decomp_sym_nx`), and `lem:normal_deriv` asserts that
`D_b(F̃) = (1/b!) ∂^b F̃|_{u=0} (du)^b` is independent of the linear fibre coordinates. We formalise
this for `r`-forms on the fibre coordinates `ℝ^d` (`JetForm (Fin d → ℝ) r`):

* the **weight** of a component index `m : Fin r → Fin d` is the multi-index `b = (#m⁻¹(i))ᵢ`
  (`weightOf`), `|b| = r`; the weight fibres have multinomial cardinality
  `#{m : weightOf m = b} = r!/b!` (`card_weightFibre`, via the multinomial theorem in
  `MvPolynomial`);
* **monomial forms** `du_{m₀} ⊗ ⋯ ⊗ du_{m_{r-1}}` (`monomialForm`) are the dual basis to the
  components: every `r`-form is `∑_m A(e_m) du^{⊗m}` (`eq_sum_jetComponent_smul_monomialForm`);
* **symmetric forms** (`IsSymmForm`, the subspace `symmForms`; the jet of an analytic function is
  symmetric, `isSymmForm_normalJet`) have components depending only on the weight
  (`jetComponent_eq_of_weightOf_eq`: equal weights are conjugate by a permutation), so the
  **weight component** `∂^b A` (`weightComponentL`, `weightComponent_eq`) is well defined;
* the **weight forms** `(du)^b = ∑_{weightOf m = b} du^{⊗m}` (`weightForm`) are symmetric, have
  components `[weightOf m = b]` (`jetComponent_weightForm`), are linearly independent
  (`linearIndependent_weightForm`) and span the symmetric forms:
  `A = ∑_{|b|=r} ∂^b A · (du)^b` (`eq_sum_weightComponent_smul_weightForm`) — this is
  `eq:decomp_sym_nx` at a point, with the weight line `ℝ·(du)^b` as `⊗ᵢ Sym^{bᵢ}(𝓛ᵢ)`;
* the **factorial bridge**: with the normalised tensor `(du)^b/(r!/b!)` (`symMonomial`, diagonal
  value `u^b`, `symMonomial_apply_diag`), `(1/r!) A = ∑_{|b|=r} (∂^b A / b!) (du)^b`
  (`normalTaylorForm_eq_sum_multiIndex`) and on the diagonal
  `(1/r!) D^rF(0)(u,…,u) = ∑_{|b|=r} (∂^bF(0)/b!) u^b` (`homogeneousTaylor_eq_sum_multiIndex`);
  in a fibre frame the chosen-normal Taylor form of unit 1 is the paper's
  `D^r_⊥F = ∑_{|b|=r} ∂^b(F∘Φ)/b! (du)^b` (`normalTaylorForm_frame_apply_diag`);
* **canonical weight lines and `lem:normal_deriv`**: under the diagonal frame change `u' = g·u`
  the weight forms scale by `g^b` (`weightForm_compDiag`), so the lines `ℝ·(du)^b` are canonical
  (`span_weightForm_compDiag`), the weight components scale by `g^{-b}`
  (`weightComponent_compDiag`), and the tensors `∂^b A · (du)^b` are frame independent
  (`weightComponent_smul_weightForm_invariant`, `normalJet_weight_tensor_invariant`).

Non-claims: no symmetric-power bundle; the forms live on the fixed fibre coordinates `ℝ^d` and the
frame changes are the fibre-linear diagonal ones of `lem:normal_deriv`; symmetry of `C^r` jets is
used only where Mathlib provides it (analytic functions) or as a hypothesis.
-/

open scoped ContDiff
open Finset

namespace Grammar

open MonoRep

variable {d r : ℕ}

/-! ### Weights and weight fibres -/

/-- **The weight** `b = (#{j : m j = i})ᵢ` of a component index `m : Fin r → Fin d`. -/
def weightOf (m : Fin r → Fin d) : Fin d → ℕ := fun i => #{j | m j = i}

theorem sum_weightOf (m : Fin r → Fin d) : ∑ i, weightOf m i = r := by
  unfold weightOf
  rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (m j)), Finset.card_univ,
    Fintype.card_fin]

theorem weightOf_mem_antidiagonalTuple (m : Fin r → Fin d) :
    weightOf m ∈ Finset.Nat.antidiagonalTuple d r :=
  Finset.Nat.mem_antidiagonalTuple.2 (sum_weightOf m)

theorem weightOf_comp_perm (m : Fin r → Fin d) (τ : Equiv.Perm (Fin r)) :
    weightOf (m ∘ τ) = weightOf m := by
  funext i
  unfold weightOf
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (τ.subtypeEquiv fun j => Iff.rfl)

/-- Equal weights are conjugate by a permutation of the slots. -/
theorem exists_perm_of_weightOf_eq {m m' : Fin r → Fin d} (h : weightOf m = weightOf m') :
    ∃ σ : Equiv.Perm (Fin r), m' ∘ σ = m := by
  classical
  have hc : ∀ i, Fintype.card {j // m j = i} = Fintype.card {j // m' j = i} := by
    intro i
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrFun h i
  let e : ∀ i, {j // m j = i} ≃ {j // m' j = i} := fun i => Fintype.equivOfCardEq (hc i)
  let σ : Fin r ≃ Fin r := (Equiv.sigmaFiberEquiv m).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv m'))
  refine ⟨σ, funext fun j => ?_⟩
  exact (e (m j) ⟨j, rfl⟩).2

/-- The weight fibre `{m : weightOf m = b}`. -/
def weightFibre (b : Fin d → ℕ) : Finset (Fin r → Fin d) := {m | weightOf m = b}

theorem mem_weightFibre {b : Fin d → ℕ} {m : Fin r → Fin d} :
    m ∈ weightFibre b ↔ weightOf m = b := by
  simp [weightFibre]

open MvPolynomial in
/-- **The multinomial count**: `#{m : Fin r → Fin d | ∀ i, #{j : m j = i} = bᵢ} = r!/b!` for
`|b| = r`, by comparing coefficients in `(∑ Xᵢ)^r`. -/
theorem card_fibre_eq_multinomial (b : Fin d → ℕ) (hb : ∑ i, b i = r) :
    #{m : Fin r → Fin d | ∀ i, #{j | m j = i} = b i} = Nat.multinomial Finset.univ b := by
  classical
  let cF : (Fin r → Fin d) → (Fin d →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm fun i => #{j | m j = i}
  let bF : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm b
  have h1 : ((∑ i, X i : MvPolynomial (Fin d) ℕ)) ^ r =
      ∑ m : Fin r → Fin d, monomial (cF m) 1 := by
    calc ((∑ i, X i : MvPolynomial (Fin d) ℕ)) ^ r
        = ∏ _j : Fin r, ∑ i, (X i : MvPolynomial (Fin d) ℕ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ m : Fin r → Fin d, ∏ j, X (m j) := Fintype.prod_sum _
      _ = ∑ m : Fin r → Fin d, monomial (cF m) 1 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [monomial_eq, C_1, one_mul,
            Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun i _ => pow_zero _)]
          simp only [cF, Finsupp.coe_equivFunOnFinite_symm]
          calc ∏ j, X (m j)
              = ∏ j, ∏ i, (X i : MvPolynomial (Fin d) ℕ) ^ (if m j = i then 1 else 0) := by
                refine Finset.prod_congr rfl fun j _ => ?_
                rw [Finset.prod_eq_single (m j)]
                · simp
                · intro i _ hi
                  simp [Ne.symm hi]
                · simp
            _ = ∏ i, ∏ j, (X i : MvPolynomial (Fin d) ℕ) ^ (if m j = i then 1 else 0) :=
                Finset.prod_comm
            _ = ∏ i, X i ^ #{j | m j = i} := by
                refine Finset.prod_congr rfl fun i _ => ?_
                rw [Finset.prod_pow_eq_pow_sum, Finset.card_filter]
  have h2 := congrArg (coeff bF) h1
  rw [coeff_sum_X_pow_of_fintype, coeff_sum] at h2
  simp only [coeff_monomial] at h2
  have hsum : bF.sum (fun _ m => m) = r := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa [bF] using hb
  rw [if_pos hsum, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h2
  have h3 : ∑ m : Fin r → Fin d, (if cF m = bF then (1 : ℕ) else 0) =
      #{m : Fin r → Fin d | ∀ i, #{j | m j = i} = b i} := by
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cF, bF]
    rw [Equiv.apply_eq_iff_eq, _root_.funext_iff]
  rw [h3] at h2
  rw [← h2]
  rfl

theorem card_weightFibre (b : Fin d → ℕ) (hb : ∑ i, b i = r) :
    #(weightFibre (r := r) b) = Nat.multinomial Finset.univ b := by
  rw [← card_fibre_eq_multinomial b hb]
  congr 1
  ext m
  simp only [weightFibre, Finset.mem_filter, Finset.mem_univ, true_and, weightOf, _root_.funext_iff]

theorem card_weightFibre_pos (b : Fin d → ℕ) (hb : ∑ i, b i = r) :
    (0 : ℝ) < #(weightFibre (r := r) b) := by
  rw [card_weightFibre b hb]
  exact_mod_cast Nat.multinomial_pos _ _

/-- `∏_j u_{m_j} = u^{weightOf m}`. -/
theorem prod_comp_eq_mono_weightOf (m : Fin r → Fin d) (u : Fin d → ℝ) :
    ∏ j, u (m j) = mono (weightOf m) u := by
  unfold mono weightOf
  calc ∏ j, u (m j) = ∏ j, ∏ i, u i ^ (if m j = i then 1 else 0) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_eq_single (m j)]
        · simp
        · intro i _ hi
          simp [Ne.symm hi]
        · simp
    _ = ∏ i, ∏ j, u i ^ (if m j = i then 1 else 0) := Finset.prod_comm
    _ = ∏ i, u i ^ #{j | m j = i} := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_pow_eq_pow_sum, Finset.card_filter]

/-! ### Symmetric forms -/

section Symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A form is **symmetric** when it is invariant under permutations of its arguments. -/
def IsSymmForm (A : JetForm E r) : Prop :=
  ∀ (σ : Equiv.Perm (Fin r)) (v : Fin r → E), A (v ∘ σ) = A v

/-- The jet of a function analytic at `0` is symmetric. -/
theorem isSymmForm_normalJet {F : E → ℝ} (hF : ContDiffAt ℝ ω F 0) : IsSymmForm (normalJet F r) :=
  fun σ v => hF.iteratedFDeriv_comp_perm v σ

/-- **The subspace of symmetric `r`-forms**. -/
def symmForms (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) :
    Submodule ℝ (JetForm E r) where
  carrier := {A | IsSymmForm A}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {A B} hA hB σ v => by
    simp only [add_apply, hA σ v, hB σ v]
  smul_mem' := fun c {A} hA σ v => by
    simp only [smul_apply, hA σ v]

theorem mem_symmForms {A : JetForm E r} : A ∈ symmForms E r ↔ IsSymmForm A := Iff.rfl

end Symm

theorem jetComponent_comp_perm (A : JetForm (Fin d → ℝ) r) (hA : IsSymmForm A) (m : Fin r → Fin d)
    (σ : Equiv.Perm (Fin r)) : jetComponent A (m ∘ σ) = jetComponent A m :=
  hA σ fun j => Pi.single (m j) 1

/-- **Components of a symmetric form depend only on the weight** (`lem:normal_deriv`,
well-definedness of `∂^b`). -/
theorem jetComponent_eq_of_weightOf_eq (A : JetForm (Fin d → ℝ) r) (hA : IsSymmForm A)
    {m m' : Fin r → Fin d} (h : weightOf m = weightOf m') :
    jetComponent A m = jetComponent A m' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_weightOf_eq h
  exact jetComponent_comp_perm A hA m' σ

/-! ### Monomial forms -/

/-- **The monomial form** `du_{m₀} ⊗ ⋯ ⊗ du_{m_{r-1}}`. -/
noncomputable def monomialForm (m : Fin r → Fin d) : JetForm (Fin d → ℝ) r :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap fun j =>
    ContinuousLinearMap.proj (m j)

theorem monomialForm_apply (m : Fin r → Fin d) (v : Fin r → Fin d → ℝ) :
    monomialForm m v = ∏ j, v j (m j) := by
  simp [monomialForm]

theorem jetComponent_monomialForm (m m' : Fin r → Fin d) :
    jetComponent (monomialForm m) m' = if m' = m then 1 else 0 := by
  unfold jetComponent
  rw [monomialForm_apply]
  by_cases h : m' = m
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hj])

/-- **The monomial forms are the dual basis to the components**: every `r`-form on `ℝ^d` is
`∑_m A(e_{m₀},…,e_{m_{r-1}}) du^{⊗m}`. -/
theorem eq_sum_jetComponent_smul_monomialForm (A : JetForm (Fin d → ℝ) r) :
    A = ∑ m, jetComponent A m • monomialForm m := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin r => Pi.basisFun ℝ (Fin d))
  intro v
  simp only [Pi.basisFun_apply, ContinuousMultilinearMap.coe_coe]
  rw [_root_.sum_apply]
  have h : ∀ m, (jetComponent A m • monomialForm m) (fun i => Pi.single (v i) (1 : ℝ)) =
      jetComponent A m * (if v = m then 1 else 0) := fun m => by
    rw [smul_apply, smul_eq_mul, ← jetComponent_monomialForm]
    rfl
  simp_rw [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-! ### Weight components and weight forms -/

/-- **The weight component functional** `∂^b`: the average of the components over the weight fibre
(for a symmetric form, the common value). -/
noncomputable def weightComponentL (b : Fin d → ℕ) : JetForm (Fin d → ℝ) r →L[ℝ] ℝ :=
  (#(weightFibre (r := r) b) : ℝ)⁻¹ • ∑ m ∈ weightFibre b,
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Fin d → ℝ) ℝ fun j => Pi.single (m j) 1

/-- The weight component `∂^b A`. -/
noncomputable def weightComponent (A : JetForm (Fin d → ℝ) r) (b : Fin d → ℕ) : ℝ :=
  weightComponentL b A

theorem weightComponent_def (A : JetForm (Fin d → ℝ) r) (b : Fin d → ℕ) :
    weightComponent A b =
      (#(weightFibre (r := r) b) : ℝ)⁻¹ * ∑ m ∈ weightFibre b, jetComponent A m := by
  simp [weightComponent, weightComponentL, jetComponent]

/-- For a symmetric form the weight component is the component at any index of that weight. -/
theorem weightComponent_eq (A : JetForm (Fin d → ℝ) r) (hA : IsSymmForm A) (m : Fin r → Fin d) :
    weightComponent A (weightOf m) = jetComponent A m := by
  rw [weightComponent_def,
    Finset.sum_congr rfl fun m' hm' => jetComponent_eq_of_weightOf_eq A hA (mem_weightFibre.1 hm'),
    Finset.sum_const, nsmul_eq_mul]
  have hpos := card_weightFibre_pos (weightOf m) (sum_weightOf m)
  field_simp

/-- **The weight form** `(du)^b = ∑_{weightOf m = b} du^{⊗m}` (the paper's
`(du₁)^{⊗b₁} ⊗ ⋯ ⊗ (du_k)^{⊗b_k}` as a symmetric `r`-form, unnormalised). -/
noncomputable def weightForm (b : Fin d → ℕ) : JetForm (Fin d → ℝ) r :=
  ∑ m ∈ weightFibre b, monomialForm m

theorem jetComponent_weightForm (b : Fin d → ℕ) (m : Fin r → Fin d) :
    jetComponent (weightForm b) m = if weightOf m = b then 1 else 0 := by
  unfold jetComponent weightForm
  rw [_root_.sum_apply]
  have h : ∀ m', monomialForm m' (fun j => Pi.single (m j) (1 : ℝ)) = if m = m' then 1 else 0 :=
    fun m' => jetComponent_monomialForm m' m
  simp_rw [h, Finset.sum_ite_eq, mem_weightFibre]

theorem isSymmForm_weightForm (b : Fin d → ℕ) : IsSymmForm (weightForm (r := r) b) := by
  intro σ v
  unfold weightForm
  rw [_root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_nbij' (fun m => m ∘ σ.symm) (fun m => m ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_weightFibre, weightOf_comp_perm]
    exact mem_weightFibre.1 hm
  · intro m hm
    rw [mem_weightFibre, weightOf_comp_perm]
    exact mem_weightFibre.1 hm
  · intro m _
    funext j
    simp
  · intro m _
    funext j
    simp
  · intro m _
    rw [monomialForm_apply, monomialForm_apply]
    calc ∏ j, (v ∘ σ) j (m j) = ∏ j, v (σ j) (m (σ.symm (σ j))) := by simp
      _ = ∏ j, v j (m (σ.symm j)) := Equiv.prod_comp σ fun j => v j (m (σ.symm j))
      _ = ∏ j, v j ((m ∘ σ.symm) j) := rfl

theorem weightForm_mem_symmForms (b : Fin d → ℕ) :
    weightForm (r := r) b ∈ symmForms (Fin d → ℝ) r :=
  isSymmForm_weightForm b

theorem weightForm_apply_diag (b : Fin d → ℕ) (u : Fin d → ℝ) :
    weightForm (r := r) b (fun _ => u) = #(weightFibre (r := r) b) * mono b u := by
  unfold weightForm
  rw [_root_.sum_apply, Finset.sum_congr rfl fun m hm => ?_, Finset.sum_const, nsmul_eq_mul]
  rw [monomialForm_apply, prod_comp_eq_mono_weightOf, mem_weightFibre.1 hm]

theorem weightComponent_weightForm (b b' : Fin d → ℕ) (hb : ∑ i, b i = r) :
    weightComponent (weightForm (r := r) b') b = if b = b' then 1 else 0 := by
  rw [weightComponent_def]
  have h : ∀ m ∈ weightFibre (r := r) b,
      jetComponent (weightForm b') m = if b = b' then 1 else 0 := by
    intro m hm
    rw [jetComponent_weightForm, mem_weightFibre.1 hm]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  have hpos := card_weightFibre_pos b hb
  field_simp

/-- **`eq:decomp_sym_nx`, spanning part**: a symmetric `r`-form is the sum of its weight components
times the weight forms, `A = ∑_{|b|=r} ∂^b A · (du)^b`. -/
theorem eq_sum_weightComponent_smul_weightForm (A : JetForm (Fin d → ℝ) r) (hA : IsSymmForm A) :
    A = ∑ b ∈ Finset.Nat.antidiagonalTuple d r, weightComponent A b • weightForm b := by
  conv_lhs => rw [eq_sum_jetComponent_smul_monomialForm A]
  rw [← Finset.sum_fiberwise_of_maps_to (fun m _ => weightOf_mem_antidiagonalTuple m)]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold weightForm
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← mem_weightFibre.1 hm, weightComponent_eq A hA]

/-- **`eq:decomp_sym_nx`, independence part**: the weight forms of weight `r` are linearly
independent. -/
theorem linearIndependent_weightForm :
    LinearIndependent ℝ fun b : Finset.Nat.antidiagonalTuple d r =>
      weightForm (r := r) (b : Fin d → ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have h := congrArg (weightComponentL (r := r) (b : Fin d → ℕ)) hc
  rw [map_sum, map_zero] at h
  have hb := Finset.Nat.mem_antidiagonalTuple.1 b.2
  have h' : ∀ b' : Finset.Nat.antidiagonalTuple d r,
      weightComponentL (r := r) (b : Fin d → ℕ) (c b' • weightForm (b' : Fin d → ℕ)) =
        if b = b' then c b' else 0 := by
    intro b'
    rw [map_smul, smul_eq_mul]
    change c b' * weightComponent (weightForm (b' : Fin d → ℕ)) (b : Fin d → ℕ) = _
    rw [weightComponent_weightForm _ _ hb, mul_ite, mul_one, mul_zero]
    by_cases hbb : b = b'
    · subst hbb
      simp
    · rw [if_neg hbb, if_neg fun h => hbb (Subtype.ext h)]
  simp_rw [h', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h

/-! ### The factorial bridge -/

/-- **The paper's normalised symmetric tensor** `(du)^b / (r!/b!)`, with diagonal value `u^b`. -/
noncomputable def symMonomial (b : Fin d → ℕ) : JetForm (Fin d → ℝ) r :=
  (Nat.multinomial Finset.univ b : ℝ)⁻¹ • weightForm b

theorem symMonomial_apply_diag (b : Fin d → ℕ) (hb : ∑ i, b i = r) (u : Fin d → ℝ) :
    symMonomial (r := r) b (fun _ => u) = mono b u := by
  unfold symMonomial
  rw [smul_apply, weightForm_apply_diag, card_weightFibre b hb, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  exact_mod_cast (Nat.multinomial_pos _ _).ne'

/-- `(r!/b!) / r! = 1/b!`. -/
theorem multinomial_div_factorial (b : Fin d → ℕ) (hb : ∑ i, b i = r) :
    (Nat.multinomial Finset.univ b : ℝ) / r.factorial = (∏ i, ((b i).factorial : ℝ))⁻¹ := by
  have h := Nat.multinomial_spec Finset.univ b
  rw [hb] at h
  have h' : (∏ i, ((b i).factorial : ℝ)) * Nat.multinomial Finset.univ b = r.factorial := by
    exact_mod_cast h
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  have hp : (∏ i, ((b i).factorial : ℝ)) ≠ 0 := by positivity
  rw [div_eq_iff hf, ← h', ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- **The factorial bridge**: for a symmetric `r`-form,
`(1/r!) A = ∑_{|b|=r} (∂^b A / b!) (du)^b` with the normalised tensors `(du)^b`. -/
theorem normalTaylorForm_eq_sum_multiIndex (A : JetForm (Fin d → ℝ) r) (hA : IsSymmForm A) :
    (r.factorial : ℝ)⁻¹ • A = ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      ((∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent A b) • symMonomial b := by
  conv_lhs => rw [eq_sum_weightComponent_smul_weightForm A hA]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Finset.Nat.mem_antidiagonalTuple.1 hb
  unfold symMonomial
  rw [smul_smul, smul_smul, ← multinomial_div_factorial b hb']
  congr 1
  have hM : (Nat.multinomial Finset.univ b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  field_simp

/-- **The homogeneous Taylor term in multi-index form**: for `F` analytic at `0`,
`(1/r!) D^rF(0)(u,…,u) = ∑_{|b|=r} (∂^bF(0)/b!) u^b`. -/
theorem homogeneousTaylor_eq_sum_multiIndex {F : (Fin d → ℝ) → ℝ} (hF : ContDiffAt ℝ ω F 0)
    (r : ℕ) (u : Fin d → ℝ) :
    homogeneousTaylor F r u = ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet F r) b * mono b u := by
  have h : ((r.factorial : ℝ)⁻¹ • normalJet F r) (fun _ => u) =
      (∑ b ∈ Finset.Nat.antidiagonalTuple d r,
        ((∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet F r) b) • symMonomial b)
        (fun _ => u) :=
    congrArg (fun T : JetForm (Fin d → ℝ) r => T fun _ => u)
      (normalTaylorForm_eq_sum_multiIndex (normalJet F r) (isSymmForm_normalJet hF))
  rw [smul_apply, _root_.sum_apply, smul_eq_mul] at h
  unfold homogeneousTaylor
  rw [h]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [smul_apply, smul_eq_mul, symMonomial_apply_diag b (Finset.Nat.mem_antidiagonalTuple.1 hb)]

/-- **`defn:normal_diff` in a fibre frame**: for the chosen-normal Taylor form of unit 1 read
through a linear fibre frame `e : ℝ^d →L N s`, with `G = F ∘ Φ_s ∘ e` analytic at `0`,
`D^r_⊥F(s)(e u,…,e u) = ∑_{|b|=r} (∂^b G(0)/b!) u^b`. -/
theorem normalTaylorForm_frame_apply_diag {S : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
    (e : (Fin d → ℝ) →L[ℝ] N s) (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (hG : ContDiffAt ℝ ω (fun u : Fin d → ℝ => F (Φ s (e u))) 0) (u : Fin d → ℝ) :
    normalTaylorForm N Φ F s r (fun _ => e u) = ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ *
        weightComponent (normalJet (fun u : Fin d → ℝ => F (Φ s (e u))) r) b * mono b u := by
  have h := congrArg (fun T : JetForm (Fin d → ℝ) r => T fun _ => u)
    (normalTaylorForm_comp_frame N Φ F s hF e)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h
  rw [← h, ← homogeneousTaylor_eq_sum_multiIndex hG r u]
  rfl

/-! ### Canonical weight lines and the completion of `lem:normal_deriv` -/

theorem monomialForm_compDiag (m : Fin r → Fin d) (g : Fin d → ℝ) :
    (monomialForm m).compContinuousLinearMap (fun _ => diagScale g) =
      (∏ j, g (m j)) • monomialForm m := by
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, monomialForm_apply,
    diagScale_apply, smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- **The weight forms scale by `g^b` under the diagonal frame change** `u' = g·u`. -/
theorem weightForm_compDiag (b : Fin d → ℕ) (g : Fin d → ℝ) :
    (weightForm (r := r) b).compContinuousLinearMap (fun _ => diagScale g) =
      mono b g • weightForm b := by
  have hL : ∀ A : JetForm (Fin d → ℝ) r, A.compContinuousLinearMap (fun _ => diagScale g) =
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin r => diagScale g) A :=
    fun A => rfl
  unfold weightForm
  rw [hL, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← hL, monomialForm_compDiag, prod_comp_eq_mono_weightOf, mem_weightFibre.1 hm]

theorem mono_ne_zero {b : Fin d → ℕ} {g : Fin d → ℝ} (hg : ∀ i, g i ≠ 0) : mono b g ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hg i)

/-- **The weight lines are canonical**: `ℝ·(du')^b = ℝ·(du)^b` under `u' = g·u`, `gᵢ ≠ 0`. -/
theorem span_weightForm_compDiag (b : Fin d → ℕ) {g : Fin d → ℝ} (hg : ∀ i, g i ≠ 0) :
    (ℝ ∙ (weightForm (r := r) b).compContinuousLinearMap (fun _ => diagScale g)) =
      ℝ ∙ weightForm (r := r) b := by
  rw [weightForm_compDiag,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (mono_ne_zero hg))]

/-- **The weight components scale by `g^b`** under `A ↦ A ∘ diag(g)`. -/
theorem weightComponent_compDiag (A : JetForm (Fin d → ℝ) r) (g : Fin d → ℝ) (b : Fin d → ℕ) :
    weightComponent (A.compContinuousLinearMap fun _ => diagScale g) b =
      mono b g * weightComponent A b := by
  rw [weightComponent_def, weightComponent_def,
    Finset.sum_congr rfl fun m hm => (jetComponent_compDiag A g m).trans
      (by rw [prod_comp_eq_mono_weightOf, mem_weightFibre.1 hm]),
    ← Finset.mul_sum]
  ring

/-- **`lem:normal_deriv`, tensor form**: the tensor `∂^b A · (du)^b` is independent of the diagonal
fibre frame: in the frame `u' = g·u` the form is `A' = A ∘ diag(g)⁻¹`, the coframe is
`(du')^b = (du)^b ∘ diag(g)`, and `∂^b A' · (du')^b = ∂^b A · (du)^b`. -/
theorem weightComponent_smul_weightForm_invariant (A : JetForm (Fin d → ℝ) r) {g : Fin d → ℝ}
    (hg : ∀ i, g i ≠ 0) (b : Fin d → ℕ) :
    weightComponent (A.compContinuousLinearMap fun _ => diagScale g⁻¹) b •
        (weightForm (r := r) b).compContinuousLinearMap (fun _ => diagScale g) =
      weightComponent A b • weightForm b := by
  rw [weightComponent_compDiag, weightForm_compDiag, smul_smul]
  congr 1
  have h : mono b g⁻¹ * mono b g = 1 := by
    unfold mono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Pi.inv_apply, ← mul_pow, inv_mul_cancel₀ (hg i), one_pow]
  calc mono b g⁻¹ * weightComponent A b * mono b g
      = weightComponent A b * (mono b g⁻¹ * mono b g) := by ring
    _ = weightComponent A b := by rw [h, mul_one]

/-- **`lem:normal_deriv` for jets**: with `F'(u') = F(u)` in the coordinates `u' = g·u`
(`F' = F ∘ diag(g)⁻¹`), the tensors `∂^b F'(0) · (du')^b` and `∂^b F(0) · (du)^b` agree. -/
theorem normalJet_weight_tensor_invariant {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ r F)
    {g : Fin d → ℝ} (hg : ∀ i, g i ≠ 0) (b : Fin d → ℕ) :
    weightComponent (normalJet (F ∘ diagScale g⁻¹) r) b •
        (weightForm (r := r) b).compContinuousLinearMap (fun _ => diagScale g) =
      weightComponent (normalJet F r) b • weightForm b := by
  rw [normalJet_comp_linear hF]
  exact weightComponent_smul_weightForm_invariant (normalJet F r) hg b

end Grammar
