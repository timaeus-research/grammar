import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Grammar.NormalJet

/-!
# Normal Taylor forms of a chosen normal family (Astra #63 unit 1)

The paper's `defn:normal_diff` defines the normal `r`-th differential `D^r_⊥ F` of an observable
through a tubular neighbourhood `Φ : NX → M`. We formalise it for a **chosen normal family**: normal
spaces `N s ⊆ E` (submodules of a fixed normed space) and fibre maps `Φ s : N s → M`, of which only
the germ at `0` matters. The **raw normal jet** is `J_r(F)(s) = D^r (F ∘ Φ s)(0)`, a continuous
`r`-linear form on `N s` (`rawNormalJet`), and the **normal Taylor form** is
`T_r(F)(s) = J_r(F)(s)/r!` (`normalTaylorForm`); the paper's `D^r_⊥ F = ∑_{|b|=r} ∂^b F/b! (du)^b`
is `T_r`.

* degree zero is restriction to the stratum (`normalTaylorForm_zero_apply`);
* the diagonal values are the homogeneous Taylor terms (`normalTaylorForm_apply_diag`);
* **fibre-frame covariance** (`lem:normal_deriv`, full-form part): in a linear frame `L : V →L N s`
  the pulled-back jets are the compositions `J_r ∘ (L,…,L)` (`rawNormalJet_comp_frame`,
  `normalTaylorForm_comp_frame`), and for a frame equivalence the original jet is recovered from
  the pulled-back one (`rawNormalJet_eq_of_frame`);
* **germ locality**: fibre maps agreeing near `0` have the same jets (`rawNormalJet_congr`);
* **local smoothness of the coefficients**: for a jointly `C^∞` trivialised pullback `G : S × V → ℝ`
  the fibre Taylor forms `s ↦ D^r(G(s,·))(0)/r!` are `C^∞` in the base
  (`iteratedFDeriv_fibre_eq`, `contDiff_normalTaylorCoeff`);
* the **additive Euclidean realisation** `Φ s n = s + n`: the normal jet is the ambient jet
  restricted to `N s` (`rawNormalJet_additive`).

Non-claims: no tubular neighbourhood is constructed and no bundle of sections is built; the forms
are relative to the chosen family `Φ` and are invariant only under fibre-**linear** changes of frame
(the nonlinear caveat of `NormalJet.lean` stands); symmetric forms are not singled out here.
-/

open scoped ContDiff

namespace Grammar

section Family

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}

/-- **The raw normal jet** `J_r(F)(s) = D^r (F ∘ Φ_s)(0)` of the chosen normal family
`N : S → Submodule ℝ E`, `Φ : ∀ s, N s → M`. -/
noncomputable def rawNormalJet (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
    (r : ℕ) : JetForm (N s) r :=
  iteratedFDeriv ℝ r (fun n : N s => F (Φ s n)) 0

/-- **The normal Taylor form** `T_r(F)(s) = J_r(F)(s) / r!` (the paper's `D^r_⊥ F`). -/
noncomputable def normalTaylorForm (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ)
    (s : S) (r : ℕ) : JetForm (N s) r :=
  (r.factorial : ℝ)⁻¹ • rawNormalJet N Φ F s r

variable (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)

theorem rawNormalJet_eq_normalJet (r : ℕ) :
    rawNormalJet N Φ F s r = normalJet (fun n : N s => F (Φ s n)) r := rfl

/-- Degree zero is restriction to the stratum. -/
theorem normalTaylorForm_zero_apply (m : Fin 0 → N s) :
    normalTaylorForm N Φ F s 0 m = F (Φ s 0) := by
  simp [normalTaylorForm, rawNormalJet, iteratedFDeriv_zero_apply]

/-- The diagonal values of the normal Taylor form are the homogeneous Taylor terms. -/
theorem normalTaylorForm_apply_diag (r : ℕ) (n : N s) :
    normalTaylorForm N Φ F s r (fun _ => n) = homogeneousTaylor (fun n : N s => F (Φ s n)) r n := by
  simp [normalTaylorForm, rawNormalJet, homogeneousTaylor, normalJet]

/-! ### Fibre-frame covariance -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **`lem:normal_deriv`, full-form part**: in a linear frame `L : V →L N s` the jet of the
pulled-back function is `J_r ∘ (L,…,L)`. -/
theorem rawNormalJet_comp_frame {r : ℕ} (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (L : V →L[ℝ] N s) :
    iteratedFDeriv ℝ r (fun v : V => F (Φ s (L v))) 0 =
      (rawNormalJet N Φ F s r).compContinuousLinearMap fun _ => L := by
  have h := L.iteratedFDeriv_comp_right hF 0 le_rfl
  rw [map_zero] at h
  exact h

theorem normalTaylorForm_comp_frame {r : ℕ} (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (L : V →L[ℝ] N s) :
    (r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => F (Φ s (L v))) 0 =
      (normalTaylorForm N Φ F s r).compContinuousLinearMap fun _ => L := by
  rw [rawNormalJet_comp_frame N Φ F s hF L]
  ext m
  simp [normalTaylorForm]

/-- For a frame **equivalence** the original jet is recovered from the pulled-back jet by composing
with the inverse frame: frame independence of the jet as an object on `N s`. -/
theorem rawNormalJet_eq_of_frame {r : ℕ} (hF : ContDiff ℝ r (fun n : N s => F (Φ s n)))
    (e : V ≃L[ℝ] N s) :
    rawNormalJet N Φ F s r =
      (iteratedFDeriv ℝ r (fun v : V => F (Φ s ((e : V →L[ℝ] N s) v))) 0).compContinuousLinearMap
        fun _ => (e.symm : N s →L[ℝ] V) := by
  rw [rawNormalJet_comp_frame N Φ F s hF (e : V →L[ℝ] N s)]
  ext m
  simp

/-! ### Germ locality -/

/-- Fibre maps that agree near `0` have the same normal jets. -/
theorem rawNormalJet_congr {Φ' : ∀ s, N s → M} (h : Φ s =ᶠ[nhds (0 : N s)] Φ' s) (r : ℕ) :
    rawNormalJet N Φ F s r = rawNormalJet N Φ' F s r :=
  ((h.fun_comp F).iteratedFDeriv ℝ r).eq_of_nhds

theorem normalTaylorForm_congr {Φ' : ∀ s, N s → M} (h : Φ s =ᶠ[nhds (0 : N s)] Φ' s) (r : ℕ) :
    normalTaylorForm N Φ F s r = normalTaylorForm N Φ' F s r := by
  unfold normalTaylorForm
  rw [rawNormalJet_congr N Φ F s h r]

end Family

/-! ### Local smoothness of the coefficients in a trivialisation -/

section Smooth

variable {S V : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The fibre jet of a jointly smooth function is the full jet composed with the fibre inclusion. -/
theorem iteratedFDeriv_fibre_eq {G : S × V → ℝ} (hG : ContDiff ℝ ∞ G) (r : ℕ) (s : S) :
    iteratedFDeriv ℝ r (fun v : V => G (s, v)) 0 =
      (iteratedFDeriv ℝ r G (s, 0)).compContinuousLinearMap
        fun _ => ContinuousLinearMap.inr ℝ S V := by
  have e : (fun v : V => G (s, v)) =
      (fun z : S × V => G (z + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ S V) := by
    funext v
    simp
  have hG' : ContDiff ℝ ∞ fun z : S × V => G (z + (s, 0)) :=
    hG.comp (contDiff_id.add contDiff_const)
  rw [e, (ContinuousLinearMap.inr ℝ S V).iteratedFDeriv_comp_right hG' 0 (mod_cast le_top),
    iteratedFDeriv_comp_add_right, map_zero, zero_add]

/-- **Local smoothness of the normal Taylor coefficients**: for a jointly `C^∞` trivialised
pullback `G`, the fibre Taylor forms `s ↦ D^r(G(s,·))(0)/r!` are `C^∞` in the base point. -/
theorem contDiff_normalTaylorCoeff {G : S × V → ℝ} (hG : ContDiff ℝ ∞ G) (r : ℕ) :
    ContDiff ℝ ∞ fun s : S =>
      (r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => G (s, v)) 0 := by
  simp_rw [iteratedFDeriv_fibre_eq hG r]
  refine ContDiff.const_smul _ ?_
  have h1 : ContDiff ℝ ∞ fun s : S => iteratedFDeriv ℝ r G (s, 0) :=
    (hG.iteratedFDeriv_right (mod_cast le_top)).comp (contDiff_id.prodMk contDiff_const)
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin r => ContinuousLinearMap.inr ℝ S V)).contDiff.comp h1

end Smooth

/-! ### The additive Euclidean realisation -/

section Additive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The additive realisation** `Φ s n = s + n`: the normal jet is the ambient jet at `s`
restricted to the normal space `N s`. -/
theorem rawNormalJet_additive (N : E → Submodule ℝ E) {F : E → ℝ} {r : ℕ} (hF : ContDiff ℝ r F)
    (s : E) :
    rawNormalJet N (fun s (n : N s) => s + (n : E)) F s r =
      (iteratedFDeriv ℝ r F s).compContinuousLinearMap fun _ => (N s).subtypeL := by
  unfold rawNormalJet
  have e : (fun n : N s => F (s + (n : E))) = (fun z : E => F (z + s)) ∘ (N s).subtypeL := by
    funext n
    simp [add_comm]
  have hF' : ContDiff ℝ r fun z : E => F (z + s) := hF.comp (contDiff_id.add contDiff_const)
  rw [e, (N s).subtypeL.iteratedFDeriv_comp_right hF' 0 le_rfl, iteratedFDeriv_comp_add_right,
    map_zero, zero_add]

end Additive

end Grammar
