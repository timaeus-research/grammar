/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MomentKernel
import Grammar.MonomialParity

/-!
# The scalar normal form of a monomial phase on a stratum

Unit 1 of consult #77 (`tide-log/gpt6_bigpicture_v77.md`): the algebra that turns a monomial chart
into the scalar normal form of CCXXXIII on a stratum `I`. In the coordinates
`Ψ(z, n) = planeSplit (stratumSplit I) (z, n)` of the stratum (tangential `z`, normal `n`):

* the coordinates of `Ψ(z,n)` in `I` are the normal coordinates `n_a`, those outside `I` do not
  depend on `n` (`planeSplit_stratum_inr`, `planeSplit_stratum_of_notMem`);
* a monomial splits as the **tangential monomial** times the normal monomial
  `y^e = (∏_{j∉I} Ψ(z,0)_j^{e_j}) · ∏_a n_a^{e_{ν(a)}}` (`monomialEval_planeSplit`,
  `tangentialMonomial`, `normalExp`), with the absolute-value version for Jacobians
  (`abs_monomialEval_planeSplit`);
* **parity**: on an open set where `K = u · y^e ≥ 0` with a continuous nonvanishing unit at a point
  `y₀` vanishing on `I`, every normal exponent is even (`normalExp_eq_two_mul_halfExp`, from
  `even_exponent_of_nonneg`), and positive when the coordinates of `I` are active
  (`normalHalfExp_pos`);
* **the scalar phase** `q(z) = u(Ψ(z,0)) · tangentialMonomial(z)` (`scalarPhase`): if the unit is
  independent of the normal coordinates on a region, `K(Ψ(z,n)) = q(z) ∏_a n_a^{2k_a}` there
  (`phase_scalarNormalForm`); `q` is **positive** where `K ≥ 0`, the unit is nonvanishing and the
  active tangential coordinates are nonzero, by evaluating at a normal point with all coordinates
  nonzero (`scalarPhase_pos` — NOT by evaluating at `n = 0`); and `q` is continuous on any set
  where the unit is continuous along `z ↦ Ψ(z,0)` (`continuousOn_scalarPhase`).

Non-claims: the normal-independence of the unit is a hypothesis (a constant chart unit is the
basic case); no compact base, allocation or atlas is built here (units 2–3); continuity is `On`
the relevant set — no silent global upgrade.
-/

open MeasureTheory Set Filter Topology Monomialize.Analytic
open scoped ENNReal

namespace Grammar

section Split

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty)

/-- The normal coordinates of the split point. -/
theorem planeSplit_stratum_inr (z : Fin (d - (I.card - 1 + 1)) → ℝ) (n : Fin (I.card - 1 + 1) → ℝ)
    (a : Fin (I.card - 1 + 1)) :
    planeSplit (stratumSplit I hne) (z, n) ((stratumSplit I hne).symm (Sum.inr a)) = n a := by
  rw [planeSplit_apply, coordCLE_apply_inr]

/-- The coordinates outside `I` of the split point do not depend on the normal coordinates. -/
theorem planeSplit_stratum_of_notMem (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (n : Fin (I.card - 1 + 1) → ℝ) {j : Fin d} (hj : j ∉ I) :
    planeSplit (stratumSplit I hne) (z, n) j = planeSplit (stratumSplit I hne) (z, 0) j := by
  rcases h : stratumSplit I hne j with i | a
  · rw [planeSplit_apply, planeSplit_apply, coordCLE_apply, coordCLE_apply, h]
    rfl
  · exfalso
    apply hj
    have := stratumSplit_symm_inr_mem I hne a
    rwa [← h, Equiv.symm_apply_apply] at this

/-- **The tangential monomial** `∏_{j ∈ supp e, j ∉ I} Ψ(z,0)_j^{e_j}`. -/
noncomputable def tangentialMonomial (e : Fin d →₀ ℕ) (z : Fin (d - (I.card - 1 + 1)) → ℝ) : ℝ :=
  ∏ j ∈ e.support.filter (fun j => j ∉ I), planeSplit (stratumSplit I hne) (z, 0) j ^ e j

theorem continuous_tangentialMonomial (e : Fin d →₀ ℕ) :
    Continuous (tangentialMonomial I hne e) := by
  unfold tangentialMonomial
  fun_prop

/-- The normal exponents `e_{ν(a)}` on the stratum. -/
noncomputable def normalExp (e : Fin d →₀ ℕ) (a : Fin (I.card - 1 + 1)) : ℕ :=
  e ((stratumSplit I hne).symm (Sum.inr a))

/-- **The monomial splits** into the tangential monomial and the normal monomial. -/
theorem monomialEval_planeSplit (e : Fin d →₀ ℕ) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (n : Fin (I.card - 1 + 1) → ℝ) :
    monomialEval (planeSplit (stratumSplit I hne) (z, n)) e =
      tangentialMonomial I hne e z * ∏ a, n a ^ normalExp I hne e a := by
  classical
  have hmono : monomialEval (planeSplit (stratumSplit I hne) (z, n)) e =
      ∏ j ∈ e.support, planeSplit (stratumSplit I hne) (z, n) j ^ e j := rfl
  rw [hmono, ← Finset.prod_filter_mul_prod_filter_not e.support (fun j => j ∉ I)]
  congr 1
  · unfold tangentialMonomial
    exact Finset.prod_congr rfl fun j hj => by
      rw [planeSplit_stratum_of_notMem I hne z n (Finset.mem_filter.1 hj).2]
  · have hsub : e.support.filter (fun j => ¬ j ∉ I) ⊆ I := fun j hj =>
      not_not.1 (Finset.mem_filter.1 hj).2
    rw [Finset.prod_subset hsub fun j hj hnot => by
      have : e j = 0 := by
        by_contra h0
        exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h0, not_not.2 hj⟩)
      rw [this, pow_zero]]
    symm
    refine Finset.prod_nbij (fun a => (stratumSplit I hne).symm (Sum.inr a))
      (fun a _ => stratumSplit_symm_inr_mem I hne a) ?_ ?_ ?_
    · intro a _ b _ hab
      exact Sum.inr_injective ((stratumSplit I hne).symm.injective hab)
    · intro j hj
      obtain ⟨a, ha⟩ := exists_inr_of_mem I hne hj
      exact ⟨a, Finset.mem_coe.2 (Finset.mem_univ a), ha.symm⟩
    · intro a _
      rw [planeSplit_stratum_inr]
      rfl

/-- The absolute monomial splits likewise (Jacobian exponents). -/
theorem abs_monomialEval_planeSplit (e : Fin d →₀ ℕ) (z : Fin (d - (I.card - 1 + 1)) → ℝ)
    (n : Fin (I.card - 1 + 1) → ℝ) :
    |monomialEval (planeSplit (stratumSplit I hne) (z, n)) e| =
      |tangentialMonomial I hne e z| * ∏ a, |n a| ^ normalExp I hne e a := by
  rw [monomialEval_planeSplit, abs_mul, Finset.abs_prod]
  congr 1
  exact Finset.prod_congr rfl fun a _ => abs_pow _ _

end Split

/-! ### Parity of the normal exponents -/

section Parity

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty) (e : Fin d →₀ ℕ)

/-- The half exponents `k_a = e_{ν(a)}/2` on the stratum. -/
noncomputable def normalHalfExp (a : Fin (I.card - 1 + 1)) : ℕ := normalExp I hne e a / 2

/-- **Parity**: on an open set where `K = u · y^e ≥ 0` with a continuous nonvanishing unit at a
  point
vanishing on `I`, every normal exponent is even. -/
theorem normalExp_eq_two_mul_halfExp {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    {K u : (Fin d → ℝ) → ℝ} (hK : ∀ y ∈ W, K y = u y * monomialEval y e)
    (hK0 : ∀ y ∈ W, 0 ≤ K y) {y₀ : Fin d → ℝ} (hy₀ : y₀ ∈ W) (hu : ContinuousAt u y₀)
    (hu0 : u y₀ ≠ 0) (hI : ∀ j ∈ I, y₀ j = 0) (a : Fin (I.card - 1 + 1)) :
    normalExp I hne e a = 2 * normalHalfExp I hne e a := by
  unfold normalHalfExp
  rw [Nat.two_mul_div_two_of_even]
  exact even_exponent_of_nonneg hW hK hK0 hy₀ hu hu0 (hI _ (stratumSplit_symm_inr_mem I hne a))

/-- Active normal coordinates have positive half exponents. -/
theorem normalHalfExp_pos (he : ∀ j ∈ I, 0 < e j)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a) (a : Fin (I.card - 1 + 1)) :
    0 < normalHalfExp I hne e a := by
  have h : 0 < normalExp I hne e a := he _ (stratumSplit_symm_inr_mem I hne a)
  rcases Nat.eq_zero_or_pos (normalHalfExp I hne e a) with h0 | h0
  · exfalso
    have := hpar a
    rw [h0, mul_zero] at this
    exact h.ne' this
  · exact h0

end Parity

/-! ### The scalar phase -/

section ScalarPhase

variable {d : ℕ} (I : Finset (Fin d)) (hne : I.Nonempty) (u : (Fin d → ℝ) → ℝ) (e : Fin d →₀ ℕ)

/-- The tangential unit `u_T(z) = u(Ψ(z,0))`. -/
noncomputable def tangentialUnit (z : Fin (d - (I.card - 1 + 1)) → ℝ) : ℝ :=
  u (planeSplit (stratumSplit I hne) (z, 0))

/-- **The scalar phase** `q(z) = u_T(z) · tangentialMonomial(z)`. -/
noncomputable def scalarPhase (z : Fin (d - (I.card - 1 + 1)) → ℝ) : ℝ :=
  tangentialUnit I hne u z * tangentialMonomial I hne e z

variable {K : (Fin d → ℝ) → ℝ}
  {S : Set ((Fin (d - (I.card - 1 + 1)) → ℝ) × (Fin (I.card - 1 + 1) → ℝ))}

/-- **The scalar normal form of the phase**: where `K = u · y^e` and the unit is independent of the
normal coordinates, `K(Ψ(z,n)) = q(z) ∏_a n_a^{2k_a}`. -/
theorem phase_scalarNormalForm
    (hK : ∀ p ∈ S, K (planeSplit (stratumSplit I hne) p) =
      u (planeSplit (stratumSplit I hne) p) * monomialEval (planeSplit (stratumSplit I hne) p) e)
    (hind : ∀ p ∈ S, u (planeSplit (stratumSplit I hne) p) = tangentialUnit I hne u p.1)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a) {p} (hp : p ∈ S) :
    K (planeSplit (stratumSplit I hne) p) =
      scalarPhase I hne u e p.1 * ∏ a, p.2 a ^ (2 * normalHalfExp I hne e a) := by
  obtain ⟨z, n⟩ := p
  rw [hK _ hp, hind _ hp, monomialEval_planeSplit]
  unfold scalarPhase
  simp only [hpar]
  ring

/-- **Positivity of the scalar phase**, from `K ≥ 0` at a normal point with all coordinates nonzero,
a nonvanishing unit and nonzero active tangential coordinates. -/
theorem scalarPhase_pos
    (hK : ∀ p ∈ S, K (planeSplit (stratumSplit I hne) p) =
      u (planeSplit (stratumSplit I hne) p) * monomialEval (planeSplit (stratumSplit I hne) p) e)
    (hind : ∀ p ∈ S, u (planeSplit (stratumSplit I hne) p) = tangentialUnit I hne u p.1)
    (hpar : ∀ a, normalExp I hne e a = 2 * normalHalfExp I hne e a)
    (hK0 : ∀ p ∈ S, 0 ≤ K (planeSplit (stratumSplit I hne) p))
    (hu0 : ∀ p ∈ S, u (planeSplit (stratumSplit I hne) p) ≠ 0)
    {z : Fin (d - (I.card - 1 + 1)) → ℝ} {n : Fin (I.card - 1 + 1) → ℝ} (hmem : (z, n) ∈ S)
    (hn : ∀ a, n a ≠ 0)
    (hz : ∀ j ∈ e.support, j ∉ I → planeSplit (stratumSplit I hne) (z, 0) j ≠ 0) :
    0 < scalarPhase I hne u e z := by
  have hq0 : scalarPhase I hne u e z ≠ 0 := by
    unfold scalarPhase
    refine mul_ne_zero ?_ ?_
    · rw [← hind _ hmem]
      exact hu0 _ hmem
    · unfold tangentialMonomial
      exact Finset.prod_ne_zero_iff.2 fun j hj =>
        pow_ne_zero _ (hz j (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2)
  have hP : 0 < ∏ a, n a ^ (2 * normalHalfExp I hne e a) :=
    Finset.prod_pos fun a _ => (even_two_mul _).pow_pos (hn a)
  have h0 := hK0 _ hmem
  rw [phase_scalarNormalForm I hne u e hK hind hpar hmem] at h0
  rcases lt_or_gt_of_ne hq0 with hlt | hgt
  · exfalso
    have := mul_neg_of_neg_of_pos hlt hP
    linarith
  · exact hgt

/-- The scalar phase is continuous where the unit is continuous along `z ↦ Ψ(z,0)`. -/
theorem continuousOn_scalarPhase {W' : Set (Fin d → ℝ)} (hu : ContinuousOn u W')
    {T : Set (Fin (d - (I.card - 1 + 1)) → ℝ)}
    (hT : ∀ z ∈ T, planeSplit (stratumSplit I hne) (z, 0) ∈ W') :
    ContinuousOn (scalarPhase I hne u e) T := by
  unfold scalarPhase tangentialUnit
  refine ContinuousOn.mul ?_ (continuous_tangentialMonomial I hne e).continuousOn
  exact hu.comp ((planeSplit (stratumSplit I hne)).continuous.comp
    (continuous_id.prodMk continuous_const)).continuousOn fun z hz => hT z hz

end ScalarPhase

end Grammar
