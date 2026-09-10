import Grammar.SymmetricWeights

/-!
# Normal-fibre moments and the invariant contraction (Astra #63 unit 4)

The paper's `eq:moment_tensor_defn` defines the `r`-th moment tensor `𝖬_r(v) ∈ Sym^r(N_vX)` by
its pairing with symmetric `r`-forms, `⟨α, 𝖬_r(v)⟩ = ∫_{D_v} α(ξ^{⊗r}) |u|^h e^{-nK} |μ|_v(ξ)`, and
contracts it with the normal differential `D^r_⊥F` of `defn:normal_diff`. We formalise this for a
chosen normal family `N : S → Submodule ℝ E` with a **weighted fibre measure** `η s` on each normal
space (the paper's `|u|^h e^{-nK_I}|μ_I|_v`, kept abstract here):

* the **normal-fibre moment functional** `⟨α, 𝖬_r(s)⟩ = ∫ α(ξ,…,ξ) dη_s` (`normalMoment`, a
  continuous linear functional on `r`-forms on `N s`, `normalMoment_apply`), with the norm bounds
  `‖𝖬_r(s)‖ ≤ ∫‖ξ‖^r dη_s` and `|⟨α, 𝖬_r(s)⟩| ≤ ‖α‖ ∫‖ξ‖^r dη_s` (`norm_normalMoment_le`,
  `abs_normalMoment_le`);
* **covariance under frame equivalences**: for a frame `e : V ≃L N s` and the frame measure
  `η_s^e = (e⁻¹)_* η_s` on `V`, `⟨α, 𝖬_r(η_s)⟩ = ⟨α ∘ (e,…,e), 𝖬_r(η_s^e)⟩`
  (`normalMoment_comp_equiv`; the general `moment_pairing_comp_equiv`);
* the **invariant contraction** `⟨D^r_⊥F(s), 𝖬_r(s)⟩ = ∫ (1/r!) D^r(F∘Φ_s)(0)(ξ,…,ξ) dη_s`
  (`normalContraction`, `normalContraction_eq_integral`), germ-local in `Φ`
  (`normalContraction_congr`), invariant under fibre-linear reparametrisations of the family with
  transported fibre measures (`normalContraction_reparam`), and equal in any fibre frame to the
  frame-coordinate contraction (`normalContraction_frame`);
* **the boxed bridge**: in a fibre frame `e : ℝ^d ≃L N s` with `G = F∘Φ_s∘e` analytic at `0`,
  `⟨D^r_⊥F(s), 𝖬_r(s)⟩ = ∑_{|b|=r} (∂^bG(0)/b!) M̃_b(s)` with the dressed moments
  `M̃_b(s) = ∫ u^b dη_s^e` (`normalContraction_eq_sum_dressedMoment`): the paper's
  `⟨D^r_⊥(φ∘π), 𝖬_{I,r}⟩ = ∑_{|γ|=r} D^γ_⊥(φ∘π) M̃_γ`.

Non-claims: no tensor-power implementation of `Sym^r(N_vX)` (the tensor is its pairing
functional), no smoothness of `s ↦ 𝖬_r(s)`, and the weighted fibre measure is a hypothesis — its
construction from the density factor and the phase is unit 5.
-/

open MeasureTheory Filter
open scoped ContDiff
open Finset

namespace Grammar

open MonoRep

section General

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] {r : ℕ}

/-- Finite `r`-th moments are preserved by continuous linear pushforward. -/
theorem integrable_norm_pow_map' (L : V →L[ℝ] W) {η : Measure V}
    (hr : Integrable (fun u => ‖u‖ ^ r) η) : Integrable (fun u => ‖u‖ ^ r) (η.map L) := by
  have hmeas : AEStronglyMeasurable (fun u : W => ‖u‖ ^ r) (η.map L) :=
    (by fun_prop : Continuous fun u : W => ‖u‖ ^ r).aestronglyMeasurable
  rw [integrable_map_measure hmeas L.continuous.measurable.aemeasurable]
  refine (hr.const_mul (‖L‖ ^ r)).mono'
    (by fun_prop : Continuous fun u : V => ‖L u‖ ^ r).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm u) r

/-- **Covariance of the moment pairing under a frame equivalence** `e : V ≃L W`: pairing `α` with
the moments of `η` equals pairing the pulled-back form `α ∘ (e,…,e)` with the moments of the frame
measure `(e⁻¹)_* η`. -/
theorem moment_pairing_comp_equiv (e : V ≃L[ℝ] W) {η : Measure W}
    (hr : Integrable (fun u => ‖u‖ ^ r) η) (α : JetForm W r) :
    momentFunctional (η.map (e.symm : W →L[ℝ] V)) (integrable_norm_pow_map' _ hr)
        (α.compContinuousLinearMap fun _ => (e : V →L[ℝ] W)) =
      momentFunctional η hr α := by
  simp only [momentFunctional_apply]
  rw [integral_map (e.symm : W →L[ℝ] V).continuous.measurable.aemeasurable
    (continuous_diagEval _).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

end General

section Family

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {M : Type*}

variable (N : S → Submodule ℝ E) (η : ∀ s, Measure (N s)) {r : ℕ}
  (hr : ∀ s, Integrable (fun ξ : N s => ‖ξ‖ ^ r) (η s))

/-- **The normal-fibre moment functional** `⟨α, 𝖬_r(s)⟩ = ∫ α(ξ,…,ξ) dη_s` (`eq:moment_tensor_defn`
as a functional on `r`-forms on the normal space). -/
noncomputable def normalMoment (s : S) : JetForm (N s) r →L[ℝ] ℝ := momentFunctional (η s) (hr s)

theorem normalMoment_apply (s : S) (α : JetForm (N s) r) :
    normalMoment N η hr s α = ∫ ξ, α (fun _ => ξ) ∂η s := rfl

theorem norm_normalMoment_le (s : S) : ‖normalMoment N η hr s‖ ≤ ∫ ξ, ‖ξ‖ ^ r ∂η s :=
  norm_momentFunctional_le _ _

theorem abs_normalMoment_le (s : S) (α : JetForm (N s) r) :
    |normalMoment N η hr s α| ≤ ‖α‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s := by
  rw [← Real.norm_eq_abs]
  calc ‖normalMoment N η hr s α‖ ≤ ‖normalMoment N η hr s‖ * ‖α‖ :=
        (normalMoment N η hr s).le_opNorm α
    _ ≤ (∫ ξ, ‖ξ‖ ^ r ∂η s) * ‖α‖ :=
        mul_le_mul_of_nonneg_right (norm_normalMoment_le N η hr s) (norm_nonneg _)
    _ = ‖α‖ * ∫ ξ, ‖ξ‖ ^ r ∂η s := mul_comm _ _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Frame covariance of the normal moments**: for a frame `e : V ≃L N s`,
`⟨α, 𝖬_r(s)⟩ = ⟨α ∘ (e,…,e), 𝖬_r((e⁻¹)_* η_s)⟩`. -/
theorem normalMoment_comp_equiv (s : S) (e : V ≃L[ℝ] N s) (α : JetForm (N s) r) :
    momentFunctional ((η s).map (e.symm : N s →L[ℝ] V)) (integrable_norm_pow_map' _ (hr s))
        (α.compContinuousLinearMap fun _ => (e : V →L[ℝ] N s)) =
      normalMoment N η hr s α :=
  moment_pairing_comp_equiv e (hr s) α

variable (Φ : ∀ s, N s → M) (F : M → ℝ)

/-- **The invariant contraction** `⟨D^r_⊥F(s), 𝖬_r(s)⟩` of the chosen-normal Taylor form with the
normal-fibre moment. -/
noncomputable def normalContraction (s : S) : ℝ :=
  normalMoment N η hr s (normalTaylorForm N Φ F s r)

theorem normalContraction_eq_integral (s : S) :
    normalContraction N η hr Φ F s =
      ∫ ξ, homogeneousTaylor (fun n : N s => F (Φ s n)) r ξ ∂η s := by
  unfold normalContraction
  rw [normalMoment_apply]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  exact normalTaylorForm_apply_diag N Φ F s r ξ

/-- Germ locality of the contraction in the fibre maps. -/
theorem normalContraction_congr {Φ' : ∀ s, N s → M} (s : S) (h : Φ s =ᶠ[nhds (0 : N s)] Φ' s) :
    normalContraction N η hr Φ F s = normalContraction N η hr Φ' F s := by
  unfold normalContraction
  rw [normalTaylorForm_congr N Φ F s h r]

/-- **The contraction in a fibre frame**: for `e : V ≃L N s`,
`⟨D^r_⊥F(s), 𝖬_r(s)⟩ = ⟨(1/r!) D^r(F∘Φ_s∘e)(0), 𝖬_r((e⁻¹)_* η_s)⟩`. -/
theorem normalContraction_frame (s : S) (e : V ≃L[ℝ] N s)
    (hF : ContDiff ℝ r (fun n : N s => F (Φ s n))) :
    normalContraction N η hr Φ F s =
      momentFunctional ((η s).map (e.symm : N s →L[ℝ] V)) (integrable_norm_pow_map' _ (hr s))
        ((r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => F (Φ s (e v))) 0) := by
  unfold normalContraction
  rw [← normalMoment_comp_equiv N η hr s e]
  have h := normalTaylorForm_comp_frame N Φ F s hF (e : V →L[ℝ] N s)
  simp only [ContinuousLinearEquiv.coe_coe] at h
  rw [h]

/-- **Invariance under fibre-linear reparametrisation of the family with transported fibre
measures**: for `L s : N s ≃L N s`, `Φ' s = Φ s ∘ L s` and `η' s = (L s)⁻¹_* η s`, the
contraction is unchanged. -/
theorem normalContraction_reparam (L : ∀ s, N s ≃L[ℝ] N s) (s : S)
    (hF : ContDiff ℝ r (fun n : N s => F (Φ s n))) :
    normalContraction N (fun s => (η s).map ((L s).symm : N s →L[ℝ] N s))
        (fun s => integrable_norm_pow_map' _ (hr s)) (fun s n => Φ s (L s n)) F s =
      normalContraction N η hr Φ F s := by
  unfold normalContraction normalMoment
  rw [← moment_pairing_comp_equiv (L s) (hr s) (normalTaylorForm N Φ F s r)]
  have h := normalTaylorForm_comp_frame N Φ F s hF ((L s) : N s →L[ℝ] N s)
  simp only [ContinuousLinearEquiv.coe_coe] at h
  rw [← h]
  rfl

end Family

section Bridge

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {M : Type*} {d r : ℕ}

variable (N : S → Submodule ℝ E) (η : ∀ s, Measure (N s))
  (hr : ∀ s, Integrable (fun ξ : N s => ‖ξ‖ ^ r) (η s)) (Φ : ∀ s, N s → M) (F : M → ℝ)

theorem integrable_mono_of_sum_eq {ν : Measure (Fin d → ℝ)} (hν : Integrable (fun u => ‖u‖ ^ r) ν)
    {b : Fin d → ℕ} (hb : ∑ i, b i = r) : Integrable (mono b) ν :=
  hν.mono' (continuous_mono b).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, ← hb]; exact abs_mono_le_norm_pow b u)

/-- **The boxed bridge**: in a fibre frame `e : ℝ^d ≃L N s` with `G = F∘Φ_s∘e` analytic at `0`,
`⟨D^r_⊥F(s), 𝖬_r(s)⟩ = ∑_{|b|=r} (∂^bG(0)/b!) M̃_b(s)`, where `M̃_b(s) = ∫ u^b dη_s^e` is the
dressed moment of the frame measure `η_s^e = (e⁻¹)_* η_s`. -/
theorem normalContraction_eq_sum_dressedMoment (s : S) (e : (Fin d → ℝ) ≃L[ℝ] N s)
    (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (hG : ContDiffAt ℝ ω (fun u : Fin d → ℝ => F (Φ s (e u))) 0) :
    normalContraction N η hr Φ F s = ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ *
        weightComponent (normalJet (fun u : Fin d → ℝ => F (Φ s (e u))) r) b *
          dressedMoment ((η s).map (e.symm : N s →L[ℝ] (Fin d → ℝ))) b := by
  rw [normalContraction_frame N η hr Φ F s e hF, momentFunctional_apply]
  have hν := integrable_norm_pow_map' (e.symm : N s →L[ℝ] (Fin d → ℝ)) (hr s)
  have h1 : ∀ u : Fin d → ℝ,
      ((r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : Fin d → ℝ => F (Φ s (e v))) 0)
          (fun _ => u) =
        ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
          (∏ i, ((b i).factorial : ℝ))⁻¹ *
            weightComponent (normalJet (fun u : Fin d → ℝ => F (Φ s (e u))) r) b * mono b u := by
    intro u
    rw [smul_apply, smul_eq_mul, ← homogeneousTaylor_eq_sum_multiIndex hG r u]
    rfl
  simp_rw [h1]
  rw [integral_finsetSum _ fun b hb => (integrable_mono_of_sum_eq hν
    (Finset.Nat.mem_antidiagonalTuple.1 hb)).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  rfl

end Bridge

end Grammar
