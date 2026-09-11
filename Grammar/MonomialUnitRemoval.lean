import Grammar.AnalyticCorePresentation
import Monomialize.Analytic.Structural.Terminal
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Analytic.Inverse

/-!
# Exact unit removal on a monomial chart (Astra #67 unit 2)

hironaka's monomial charts carry the phase in the form `K ∘ φ = u · y^e` with an analytic
nonvanishing unit `u`. The paper's normal form has no unit: `K = β u^{2k}`. This module removes a
**positive** analytic unit by the classical rescaling of one active coordinate,

  `T_i(y) = y_i · (u(y)/β)^{1/e_i}`, `T_j(y) = y_j` (`j ≠ i`)   (`rescale`, `unitRoot`),

so that `β · (T y)^e = u(y) · y^e = K(y)` **exactly** on the whole chart neighbourhood
(`monomialEval_rescale`, `exact_normal_form`). The rescaling is analytic (`analyticAt_rescale`)
and, at a point of the divisor `{y_i = 0}`, its derivative is the coordinate scaling by
`(u(y₀)/β)^{1/e_i} > 0` (`hasFDerivAt_rescale_of_zero`, `rescaleDeriv`), hence invertible; the
inverse function theorem gives an open partial homeomorphism `ψ` around `y₀` with `ψ = T`, whose
inverse is analytic at `ψ y₀` (Mathlib's `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`), and on
whose target the phase is the exact monomial: `K (ψ.symm z) = β z^e` (`LocalNormalForm`,
`exists_localNormalForm`).

Scope (Astra's stop rule): a **local** theorem near a divisor point — no injectivity of `T` on the
original chart box is asserted, and the positivity of the unit and the evenness of the exponents
are hypotheses here (they are proved from `K ≥ 0` in the parity lemma `even_of_nonneg`, unit 3).
The Jacobian and the orthant/box bookkeeping are unit 3.
-/

open Set Filter Topology Monomialize.Analytic
open scoped ContDiff

namespace Grammar

variable {d : ℕ}

/-! ### The monomial and coordinate rescaling -/

theorem monomialEval_eq_prod (y : Fin d → ℝ) (e : Fin d →₀ ℕ) :
    monomialEval y e = ∏ j, y j ^ e j :=
  Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- Rescaling of the `i`-th coordinate by the scalar field `r`. -/
def rescale (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  Function.update y i (y i * r y)

@[simp] theorem rescale_apply_self (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    rescale i r y i = y i * r y := by
  simp [rescale]

theorem rescale_apply_of_ne {i j : Fin d} (h : j ≠ i) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    rescale i r y j = y j := by
  simp [rescale, h]

/-- The rescaling as `y + e_i · (y_i (r y − 1))`. -/
theorem rescale_eq (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    rescale i r y = y + Pi.single i (y i * (r y - 1)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [rescale]; ring
  · simp [rescale_apply_of_ne h, h]

/-- **The monomial of a rescaled point**: `(T y)^e = (r y)^{e_i} · y^e`. -/
theorem monomialEval_rescale (i : Fin d) (r : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ)
    (e : Fin d →₀ ℕ) : monomialEval (rescale i r y) e = r y ^ e i * monomialEval y e := by
  classical
  rw [monomialEval_eq_prod, monomialEval_eq_prod]
  have h1 : (fun j => rescale i r y j ^ e j) =
      Function.update (fun j => y j ^ e j) i ((y i * r y) ^ e i) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [rescale_apply_of_ne h, Function.update_of_ne h]
  have h2 : (fun j => y j ^ e j) = Function.update (fun j => y j ^ e j) i (y i ^ e i) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, Finset.prod_update_of_mem (Finset.mem_univ i), mul_pow]
  conv_rhs => rw [h2, Finset.prod_update_of_mem (Finset.mem_univ i)]
  ring

/-- The positive `m`-th root of `u/β`, written through `exp` and `log` so that it is analytic
where `u/β > 0`. -/
noncomputable def unitRoot (β : ℝ) (m : ℕ) (u : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  Real.exp (Real.log (u y / β) / m)

theorem unitRoot_pos (β : ℝ) (m : ℕ) (u : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    0 < unitRoot β m u y := Real.exp_pos _

theorem unitRoot_pow {β : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) {u : (Fin d → ℝ) → ℝ}
    {y : Fin d → ℝ} (hu : 0 < u y) : unitRoot β m u y ^ m = u y / β := by
  unfold unitRoot
  rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hm.ne'),
    Real.exp_log (by positivity)]

theorem analyticAt_unitRoot {β : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 0 < m) {u : (Fin d → ℝ) → ℝ}
    {y : Fin d → ℝ} (hu : AnalyticAt ℝ u y) (hpos : 0 < u y) : AnalyticAt ℝ (unitRoot β m u) y := by
  have h1 : AnalyticAt ℝ (fun y => u y / β) y := hu.div analyticAt_const hβ.ne'
  have hlog : AnalyticAt ℝ Real.log (u y / β) := analyticAt_log (div_pos hpos hβ)
  have h2 : AnalyticAt ℝ (fun y => Real.log (u y / β)) y :=
    AnalyticAt.comp (g := Real.log) (f := fun y => u y / β) hlog h1
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h3 : AnalyticAt ℝ (fun y => Real.log (u y / β) / m) y := h2.div analyticAt_const hm'
  exact h3.rexp'

/-- **Exact normal form**: if `K = u · y^e` with `u > 0`, `β > 0` and `e_i > 0`, then
`K y = β · (T y)^e` for the rescaling `T = rescale i (unitRoot β e_i u)`. -/
theorem exact_normal_form {K u : (Fin d → ℝ) → ℝ} {e : Fin d →₀ ℕ} {β : ℝ} (hβ : 0 < β)
    {i : Fin d} (he : 0 < e i) {y : Fin d → ℝ} (hK : K y = u y * monomialEval y e)
    (hu : 0 < u y) : K y = β * monomialEval (rescale i (unitRoot β (e i) u) y) e := by
  rw [monomialEval_rescale, unitRoot_pow hβ he hu, hK]
  field_simp

/-! ### Analyticity and the derivative of the rescaling -/

/-- The rescaling is analytic where the scalar field is. -/
theorem analyticAt_rescale (i : Fin d) {r : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hr : AnalyticAt ℝ r y) : AnalyticAt ℝ (rescale i r) y := by
  have e : rescale i r = fun y => y + (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
      ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y * (r y - 1)) := by
    funext y
    rw [rescale_eq]
    rfl
  rw [e]
  exact analyticAt_id.add (((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).analyticAt _).comp
    (((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt y).mul
      (hr.sub analyticAt_const)))

/-- The coordinate scaling `v ↦ v + (c − 1) v_i e_i` (the derivative of the rescaling at a point of
`{y_i = 0}`), as a continuous linear map. -/
noncomputable def rescaleDeriv (i : Fin d) (c : ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.id ℝ _ +
    (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).comp
      ((c - 1) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))

theorem rescaleDeriv_apply (i : Fin d) (c : ℝ) (v : Fin d → ℝ) (j : Fin d) :
    rescaleDeriv i c v j = if j = i then c * v j else v j := by
  unfold rescaleDeriv
  by_cases h : j = i
  · subst h; simp; ring
  · simp [h]

/-- **The derivative of the rescaling at a divisor point**: at `y₀` with `y₀ i = 0`,
`D(rescale i r)(y₀) = rescaleDeriv i (r y₀)`. -/
theorem hasFDerivAt_rescale_of_zero (i : Fin d) {r : (Fin d → ℝ) → ℝ} {y₀ : Fin d → ℝ}
    (hr : AnalyticAt ℝ r y₀) (h0 : y₀ i = 0) :
    HasFDerivAt (rescale i r) (rescaleDeriv i (r y₀)) y₀ := by
  have e : rescale i r = fun y => y + (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
      ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y * (r y - 1)) := by
    funext y
    rw [rescale_eq]
    rfl
  rw [e]
  have hmul : HasFDerivAt (fun y => (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y *
      (r y - 1)) ((r y₀ - 1) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) y₀ := by
    have h := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul
      (hr.differentiableAt.hasFDerivAt.sub_const 1)
    have h0' : (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) y₀ = 0 := h0
    rw [h0', zero_smul, zero_add] at h
    exact h
  exact (hasFDerivAt_id y₀).add
    (((ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i).hasFDerivAt).comp y₀ hmul)

/-- The coordinate scaling by `c ≠ 0` as a continuous linear equivalence. -/
noncomputable def rescaleEquiv (i : Fin d) {c : ℝ} (hc : c ≠ 0) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun j =>
    if j = i then ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)
    else ContinuousLinearEquiv.refl ℝ ℝ

theorem coe_rescaleEquiv (i : Fin d) {c : ℝ} (hc : c ≠ 0) :
    (rescaleEquiv i hc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) = rescaleDeriv i c := by
  ext v j
  rw [rescaleDeriv_apply]
  simp only [ContinuousLinearEquiv.coe_coe, rescaleEquiv, ContinuousLinearEquiv.piCongrRight_apply]
  by_cases h : j = i
  · simp [h, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
  · simp [h]

/-! ### The local normal form -/

/-- **A local normal form** of the phase `K` at `y₀`: an open partial homeomorphism `ψ` around
`y₀`, analytic at `y₀` with inverse analytic at `ψ y₀`, on whose source `K = β · ψ(y)^e`. -/
structure LocalNormalForm (K : (Fin d → ℝ) → ℝ) (β : ℝ) (e : Fin d →₀ ℕ) (W : Set (Fin d → ℝ))
    (y₀ : Fin d → ℝ) where
  /-- the coordinate change -/
  ψ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)
  mem_source : y₀ ∈ ψ.source
  source_subset : ψ.source ⊆ W
  analyticAt : ∀ y ∈ ψ.source, AnalyticAt ℝ ψ y
  analyticAt_symm : AnalyticAt ℝ ψ.symm (ψ y₀)
  phase : ∀ y ∈ ψ.source, K y = β * monomialEval (ψ y) e

namespace LocalNormalForm

variable {K : (Fin d → ℝ) → ℝ} {β : ℝ} {e : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)} {y₀ : Fin d → ℝ}
  (N : LocalNormalForm K β e W y₀)

/-- On the target, the phase is the exact monomial: `K (ψ⁻¹ z) = β z^e`. -/
theorem phase_symm {z : Fin d → ℝ} (hz : z ∈ N.ψ.target) :
    K (N.ψ.symm z) = β * monomialEval z e := by
  rw [N.phase _ (N.ψ.map_target hz), N.ψ.right_inv hz]

end LocalNormalForm

/-- **Existence of the local normal form**: on an open `W` where `K = u · y^e` with `u` analytic
and positive, at a point `y₀ ∈ W` of the divisor `{y_i = 0}` with `e_i > 0`, the phase has a local
normal form at temperature `β > 0`. -/
theorem exists_localNormalForm {K u : (Fin d → ℝ) → ℝ} {e : Fin d →₀ ℕ} {W : Set (Fin d → ℝ)}
    (hW : IsOpen W) (hu : AnalyticOnNhd ℝ u W) (hupos : ∀ y ∈ W, 0 < u y)
    (hK : ∀ y ∈ W, K y = u y * monomialEval y e) {β : ℝ} (hβ : 0 < β) {i : Fin d}
    (he : 0 < e i) {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (h0 : y₀ i = 0) :
    Nonempty (LocalNormalForm K β e W y₀) := by
  set r : (Fin d → ℝ) → ℝ := unitRoot β (e i) u with hr_def
  have hr : ∀ y ∈ W, AnalyticAt ℝ r y := fun y hy =>
    analyticAt_unitRoot hβ he (hu y hy) (hupos y hy)
  have hT : ∀ y ∈ W, AnalyticAt ℝ (rescale i r) y := fun y hy => analyticAt_rescale i (hr y hy)
  have hc : r y₀ ≠ 0 := (unitRoot_pos β (e i) u y₀).ne'
  -- the derivative at `y₀` is the invertible coordinate scaling
  have hderiv : HasFDerivAt (rescale i r)
      (rescaleEquiv i hc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) y₀ := by
    rw [coe_rescaleEquiv]
    exact hasFDerivAt_rescale_of_zero i (hr y₀ hy₀) h0
  have hstrict : HasStrictFDerivAt (rescale i r)
      (rescaleEquiv i hc : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) y₀ := by
    have := (hT y₀ hy₀).hasStrictFDerivAt
    rwa [hderiv.fderiv] at this
  -- the inverse function theorem
  set ψ₀ := hstrict.toOpenPartialHomeomorph (rescale i r) with hψ₀
  have hcoe : (ψ₀ : (Fin d → ℝ) → (Fin d → ℝ)) = rescale i r := rfl
  have hmem : y₀ ∈ ψ₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- restrict the source to `W`
  set ψ := ψ₀.restrOpen W hW with hψ
  have hψcoe : (ψ : (Fin d → ℝ) → (Fin d → ℝ)) = rescale i r := by
    rw [hψ, OpenPartialHomeomorph.coe_restrOpen]
    exact hcoe
  have hsrc : ψ.source = ψ₀.source ∩ W := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hmemψ : y₀ ∈ ψ.source := by rw [hsrc]; exact ⟨hmem, hy₀⟩
  -- analyticity of the inverse at `ψ y₀`
  obtain ⟨p, hp⟩ := hT y₀ hy₀
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ (Fin d → ℝ) (Fin d → ℝ)).symm
      (rescaleEquiv i hc) := by
    have h1 := hp.fderiv_eq
    rw [hderiv.fderiv] at h1
    rw [h1]
    simp
  have hpψ : HasFPowerSeriesAt ψ p y₀ := by rw [hψcoe]; exact hp
  have hsymm : HasFPowerSeriesAt ψ.symm (p.leftInv (rescaleEquiv i hc) y₀) (ψ y₀) :=
    ψ.hasFPowerSeriesAt_symm hmemψ hpψ hp1
  refine ⟨⟨ψ, hmemψ, ?_, ?_, hsymm.analyticAt, ?_⟩⟩
  · rw [hsrc]; exact inter_subset_right
  · intro y hy
    rw [hψcoe]
    exact hT y (hsrc ▸ hy).2
  · intro y hy
    rw [hψcoe]
    exact exact_normal_form hβ he (hK y (hsrc ▸ hy).2) (hupos y (hsrc ▸ hy).2)

end Grammar
