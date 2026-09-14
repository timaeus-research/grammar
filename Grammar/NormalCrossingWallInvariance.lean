/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Sum

/-!
# Local wall invariance of normal-crossing monomial normal forms

A resolution of singularities presents the phase near a point of the exceptional divisor, in
local coordinates `x ∈ ℝ^d` centred at the point, as a **monomial normal form**
`a(x) · ∏_{j ∈ J} x_j^{2 k_j}` with `a` analytic, `a 0 ≠ 0`, and `k_j ≥ 1` on the finite set
`J ⊆ Fin d` of **walls** through the point (`MonomialForm`, `MonomialForm.phase`); the Jacobian
density is `b(x) · ∏_{j ∈ J} x_j^{h_j}` with `b 0 ≠ 0`. Two such coordinate systems at the same
point differ by a local analytic diffeomorphism `H` (given here by both directions `H`, `G` with
`G ∘ H = id` and `H ∘ G = id` near `0`, exactly the data of two charts of an atlas). This module
proves that the walls, their phase exponents `k` and their Jacobian exponents `h` are
chart-independent:

* `exists_wall_equiv` (★★★): a bijection `σ : J ≃ J'` with `k j = k' (σ j)` such that the linear
  form `v ↦ (fderiv ℝ H 0 v) (σ j)` has the same kernel as `v ↦ v j` — the tangent hyperplane of
  the wall `j` is carried to that of the wall `σ j`;
* `exponent_eq_of_unit_monomial_eq` (★★): the exponent-matching engine, free of `k`: given the
  tangent matching and the fact that `H` carries the wall `j` into the union of the target walls,
  ANY identity `c x ∏_J x_i^{e_i} = c' x ∏_{J'} (H x)_ℓ^{e'_ℓ}` with units `c, c'` (continuous
  near `0`, nonzero at `0`) forces `e j = e' (σ j)`;
* `exists_wall_equiv_jac` (★★): the same `σ` matches the Jacobian exponents `h`, for a Jacobian
  transformation law with an abstract unit `u` in place of `det (fderiv ℝ H x)`;
  `exists_wall_equiv_jac_det` instantiates `u` with the determinant itself (continuous near `0`
  by analyticity of `fderiv ℝ H`, nonzero at `0` because `G ∘ H = id`);
* `card_eq_of_phase_eq`, `multiset_pairs_eq_of_phase_eq`: the depth `|J|` and the multiset of
  pairs `(k j, h j)` over the walls are invariants of the point.

## Why no irreducible decomposition is needed

The classical argument compares the irreducible components of the zero set `{phase = 0}` in the
two charts. Everything here is instead read off along **lines**, so that only one-variable facts
about analytic functions enter.

*Tangent matching.* For `v` in the hyperplane `{v_j = 0}` the phase vanishes identically along
`t ↦ t v`, so `∏_{ℓ ∈ J'} (H (t v))_ℓ^{2 k'_ℓ} ≡ 0` near `t = 0`. A finite product of one-variable
analytic functions vanishing near `0` has a factor vanishing near `0` (isolated zeros:
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`), whose derivative at `0`, namely
`(L v)_ℓ` with `L = fderiv ℝ H 0`, is then `0`. Hence the hyperplane `{v_j = 0}` is covered by the
finitely many kernels `ker (v ↦ (L v)_ℓ)`, `ℓ ∈ J'`. A real vector space is not covered by
finitely many proper subspaces (`exists_forall_ne_zero_of_forall_exists`, proved by moving along
a line `v + t u` and avoiding finitely many bad `t`), so one kernel contains the hyperplane, and
since `L` is injective the two hyperplanes coincide. Distinct walls have distinct hyperplanes, so
`j ↦ ℓ` is injective; the reverse chart gives the reverse injection and hence a bijection.

*Exponent matching.* Choose a generic point `w` on the wall `{x_j = 0}` near `0`: its other
`J`-coordinates are nonzero, the other target coordinates `(H w)_ℓ`, `ℓ ≠ σ j`, are nonzero
(their derivatives along the chosen direction are nonzero by the tangent matching), and the
transversal derivative `(fderiv ℝ H w e_j) (σ j)` is nonzero by continuity. Along the transversal
line `s ↦ w + s e_j` the left side is `s^{e_j} · (unit)` while the right side is
`s^{e'_{σ j}} · (unit)`, because `s ↦ (H (w + s e_j))_{σ j}` vanishes at `s = 0` with nonzero
derivative and so factors as `s · ψ(s)` with `ψ 0 ≠ 0` (`dslope`). Two functions
`s^e g(s) = s^{e'} G(s)` with continuous `g, G` nonzero at `0` force `e = e'`
(`eq_of_pow_mul_eventuallyEq`). No power series is manipulated in more than one variable.

Everything is Euclidean and local; there are no manifolds.
-/

open Filter Topology Function

namespace Grammar.NormalCrossing

variable {d : ℕ}

/-- A monomial normal form at the origin of `ℝ^d`: the phase is `a x * ∏ j ∈ J, x j ^ (2 * k j)`
with `a` analytic and nonzero at `0` and `0 < k j` on the walls `J`. -/
structure MonomialForm (d : ℕ) where
  /-- the walls through the point -/
  J : Finset (Fin d)
  /-- phase half-exponents (only the values on `J` matter) -/
  k : Fin d → ℕ
  /-- the unit -/
  a : (Fin d → ℝ) → ℝ
  a_analytic : AnalyticAt ℝ a 0
  a_ne : a 0 ≠ 0
  k_pos : ∀ j ∈ J, 0 < k j

/-- The phase `a x * ∏ j ∈ J, x j ^ (2 * k j)` of a monomial normal form. -/
def MonomialForm.phase (F : MonomialForm d) (x : Fin d → ℝ) : ℝ :=
  F.a x * ∏ j ∈ F.J, x j ^ (2 * F.k j)

theorem MonomialForm.phase_eq_zero (F : MonomialForm d) {j : Fin d} (hj : j ∈ F.J)
    {x : Fin d → ℝ} (hx : x j = 0) : F.phase x = 0 := by
  unfold MonomialForm.phase
  rw [Finset.prod_eq_zero hj (by rw [hx]; exact zero_pow (by have := F.k_pos j hj; omega)),
    mul_zero]

/-! ### One-variable analytic tools -/

/-- Pigeonhole for analytic zeros: if near `0` at least one of finitely many one-variable
analytic functions vanishes, one of them vanishes identically near `0`. -/
theorem exists_eventually_eq_zero_of_eventually_exists {ι : Type*} {f : ι → ℝ → ℝ}
    {s : Finset ι} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ i ∈ s, f i t = 0) :
    ∃ i ∈ s, ∀ᶠ t in 𝓝 (0 : ℝ), f i t = 0 := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hne : ∀ i ∈ s, ∀ᶠ t in 𝓝[≠] (0 : ℝ), f i t ≠ 0 := fun i hi =>
    ((hf i hi).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hcon i hi)
  have hall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i ∈ s, f i t ≠ 0 := (eventually_all_finset s).mpr hne
  obtain ⟨t, ht1, i, hi, hti⟩ := (hall.and (h.filter_mono nhdsWithin_le_nhds)).exists
  exact ht1 i hi hti

theorem eq_zero_of_hasDerivAt_of_eventually_zero {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), f t = 0) : f' = 0 :=
  hf.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq h)

/-- If `s ^ e * g s = s ^ e' * G s` near `0` with `g, G` continuous and nonzero at `0`, then
`e = e'` (comparison of orders of vanishing). -/
theorem eq_of_pow_mul_eventuallyEq {g G : ℝ → ℝ} {e e' : ℕ} (hg : ContinuousAt g 0)
    (hG : ContinuousAt G 0) (hg0 : g 0 ≠ 0) (hG0 : G 0 ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), s ^ e * g s = s ^ e' * G s) : e = e' := by
  have key : ∀ {g G : ℝ → ℝ} {e e' : ℕ}, ContinuousAt g 0 → ContinuousAt G 0 → g 0 ≠ 0 →
      e < e' → (∀ᶠ s in 𝓝 (0 : ℝ), s ^ e * g s = s ^ e' * G s) → False := by
    intro g G e e' hg hG hg0 hlt h
    have h1 : ∀ᶠ s in 𝓝[≠] (0 : ℝ), g s = s ^ (e' - e) * G s := by
      filter_upwards [h.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with s hs hs0
      have hs0' : s ≠ 0 := hs0
      have hpow : s ^ e' = s ^ e * s ^ (e' - e) := by rw [← pow_add, Nat.add_sub_of_le hlt.le]
      rw [hpow, mul_assoc] at hs
      exact mul_left_cancel₀ (pow_ne_zero e hs0') hs
    have h2 : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun s : ℝ => s ^ (e' - e) * G s) (𝓝[≠] (0 : ℝ))
        (𝓝 ((0 : ℝ) ^ (e' - e) * G 0)) :=
      ((continuousAt_id.pow _).mul hG).tendsto.mono_left nhdsWithin_le_nhds
    rw [zero_pow (by omega), zero_mul] at h3
    exact hg0 (tendsto_nhds_unique (h2.congr' h1) h3)
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exact (key hg hG hg0 hlt h).elim
  · exact heq
  · exact (key hG hg hG0 hgt (h.mono fun s hs => hs.symm)).elim

/-! ### Lines through the origin -/

theorem analyticAt_smul_const (v : Fin d → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => t • v) t₀ :=
  analyticAt_id.smul analyticAt_const

theorem analyticAt_line_coord {H : (Fin d → ℝ) → (Fin d → ℝ)} (hH : AnalyticAt ℝ H 0)
    (v : Fin d → ℝ) (ℓ : Fin d) : AnalyticAt ℝ (fun t : ℝ => H (t • v) ℓ) 0 := by
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ℓ).analyticAt _).comp
    (hH.comp_of_eq (analyticAt_smul_const v 0) (by simp))

theorem hasDerivAt_line_coord {H : (Fin d → ℝ) → (Fin d → ℝ)} (hH : DifferentiableAt ℝ H 0)
    (v : Fin d → ℝ) (ℓ : Fin d) :
    HasDerivAt (fun t : ℝ => H (t • v) ℓ) (fderiv ℝ H 0 v ℓ) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 :=
    HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
  have h2 : HasFDerivAt H (fderiv ℝ H 0) ((fun t : ℝ => t • v) 0) := by
    simpa using hH.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  rw [one_smul] at h3
  exact hasDerivAt_pi.mp h3 ℓ

theorem tendsto_smul_const_zero (v : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : Fin d → ℝ)) := by
  have : Continuous (fun t : ℝ => t • v) := by fun_prop
  simpa using this.tendsto 0

/-! ### A vector space is not a finite union of proper subspaces -/

/-- Finitely many linear forms, each nonzero somewhere on a subspace `P`, have a common
non-root in `P`. -/
theorem exists_forall_ne_zero_of_forall_exists {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : Submodule ℝ V) {ι : Type*} (φ : ι → V →ₗ[ℝ] ℝ) (s : Finset ι)
    (h : ∀ i ∈ s, ∃ u ∈ P, φ i u ≠ 0) : ∃ v ∈ P, ∀ i ∈ s, φ i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, P.zero_mem, fun i hi => by simp at hi⟩
  | insert a s ha ih =>
    obtain ⟨v, hvP, hv⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨u, huP, hu⟩ := h a (Finset.mem_insert_self a s)
    have h1 : ∀ i ∈ s, ∀ᶠ t in 𝓝[≠] (0 : ℝ), φ i (v + t • u) ≠ 0 := by
      intro i hi
      have hc : ContinuousAt (fun t : ℝ => φ i v + t * φ i u) 0 := by fun_prop
      have := hc.eventually_ne (by simpa using hv i hi)
      refine (this.filter_mono nhdsWithin_le_nhds).mono fun t ht => ?_
      simpa [map_add, map_smul, smul_eq_mul] using ht
    have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), φ a (v + t • u) ≠ 0 := by
      have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ -(φ a v) / φ a u := by
        by_cases hc : -(φ a v) / φ a u = 0
        · rw [hc]; exact eventually_mem_nhdsWithin.mono fun t ht => ht
        · exact (eventually_ne_nhds (Ne.symm hc)).filter_mono nhdsWithin_le_nhds
      refine hne.mono fun t ht => ?_
      rw [map_add, map_smul, smul_eq_mul]
      intro h0
      apply ht
      field_simp
      linarith
    have hall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ i ∈ insert a s, φ i (v + t • u) ≠ 0 := by
      refine (((eventually_all_finset s).mpr h1).and h2).mono fun t ht i hi => ?_
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ht.2
      · exact ht.1 i hi
    obtain ⟨t, ht⟩ := hall.exists
    exact ⟨v + t • u, P.add_mem hvP (P.smul_mem t huP), ht⟩

/-! ### Tangent matching (T1) -/

/-- From the phase identity: near `0`, `H` carries the wall `x j = 0` into the union of the
target walls. -/
theorem eventually_exists_wall_zero (F F' : MonomialForm d) {H : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : ContinuousAt H 0) (hH0 : H 0 = 0)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x)) {j : Fin d}
    (hj : j ∈ F.J) :
    ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ F'.J, H x ℓ = 0 := by
  have ha : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F'.a (H x) ≠ 0 := by
    have : ContinuousAt (fun x => F'.a (H x)) 0 :=
      F'.a_analytic.continuousAt.comp_of_eq hH hH0
    exact this.eventually_ne (by simp only [hH0]; exact F'.a_ne)
  filter_upwards [hphase, ha] with x hx hax hxj
  have h0 : F'.phase (H x) = 0 := by rw [← hx]; exact F.phase_eq_zero hj hxj
  unfold MonomialForm.phase at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hax
  · obtain ⟨ℓ, hℓ, hℓ0⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨ℓ, hℓ, (pow_eq_zero_iff (by have := F'.k_pos ℓ hℓ; omega)).mp hℓ0⟩

/-- Tangent matching for one wall: if `H` carries the wall `x j = 0` into the union of the
target walls, some target wall `ℓ` has `(fderiv ℝ H 0 v) ℓ = 0 ↔ v j = 0`. -/
theorem exists_tangent_wall {H : (Fin d → ℝ) → (Fin d → ℝ)} (hH : AnalyticAt ℝ H 0)
    (hL : Injective (fderiv ℝ H 0)) {J' : Finset (Fin d)} {j : Fin d}
    (hwall : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ J', H x ℓ = 0) :
    ∃ ℓ ∈ J', ∀ v : Fin d → ℝ, fderiv ℝ H 0 v ℓ = 0 ↔ v j = 0 := by
  set L := fderiv ℝ H 0 with hLdef
  have step1 : ∀ v : Fin d → ℝ, v j = 0 → ∃ ℓ ∈ J', L v ℓ = 0 := by
    intro v hv
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ ℓ ∈ J', H (t • v) ℓ = 0 := by
      filter_upwards [(tendsto_smul_const_zero v).eventually hwall] with t ht
      exact ht (by simp [hv])
    obtain ⟨ℓ, hℓ, hℓ0⟩ := exists_eventually_eq_zero_of_eventually_exists
      (fun ℓ _ => analyticAt_line_coord hH v ℓ) hev
    exact ⟨ℓ, hℓ, eq_zero_of_hasDerivAt_of_eventually_zero
      (hasDerivAt_line_coord hH.differentiableAt v ℓ) hℓ0⟩
  let P : Submodule ℝ (Fin d → ℝ) := LinearMap.ker (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ)
  have hmemP : ∀ u : Fin d → ℝ, u ∈ P ↔ u j = 0 := fun u => by simp [P, LinearMap.mem_ker]
  have step2 : ∃ ℓ ∈ J', ∀ v : Fin d → ℝ, v j = 0 → L v ℓ = 0 := by
    by_contra hcon
    have hcon' : ∀ ℓ ∈ J', ∃ u ∈ P,
        ((LinearMap.proj ℓ).comp (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) u ≠ 0 := by
      intro ℓ hℓ
      by_contra h'
      apply hcon
      refine ⟨ℓ, hℓ, fun v hv => ?_⟩
      by_contra hne
      exact h' ⟨v, (hmemP v).mpr hv, by simpa using hne⟩
    obtain ⟨v, hvP, hv⟩ := exists_forall_ne_zero_of_forall_exists P _ J' hcon'
    obtain ⟨ℓ, hℓ, hℓ0⟩ := step1 v ((hmemP v).mp hvP)
    exact hv ℓ hℓ (by simpa using hℓ0)
  obtain ⟨ℓ, hℓ, hker⟩ := step2
  refine ⟨ℓ, hℓ, fun v => ⟨fun hv => ?_, hker v⟩⟩
  have hdec : ∀ u : Fin d → ℝ, L u ℓ = u j * L (Pi.single j 1) ℓ := by
    intro u
    have hmem : ((u - u j • Pi.single j (1 : ℝ) : Fin d → ℝ)) j = 0 := by simp
    have : L u = L (u j • Pi.single j 1) + L (u - u j • Pi.single j 1) := by
      rw [← map_add]; congr 1; abel
    rw [this, Pi.add_apply, hker _ hmem, add_zero, map_smul, Pi.smul_apply, smul_eq_mul]
  have hLe : L (Pi.single j 1) ℓ ≠ 0 := by
    intro he
    have hsurj : Surjective L :=
      (LinearMap.injective_iff_surjective (f := (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)))).mp hL
    obtain ⟨u, hu⟩ := hsurj (Pi.single ℓ 1)
    have := hdec u
    rw [hu, he, mul_zero] at this
    simp at this
  rw [hdec v] at hv
  exact (mul_eq_zero.mp hv).resolve_right hLe

/-- Distinct walls have distinct tangent hyperplanes: the target wall matched to `j` determines
`j`. -/
theorem tangent_wall_unique {L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {j j' ℓ : Fin d}
    (h : ∀ v : Fin d → ℝ, L v ℓ = 0 ↔ v j = 0) (h' : ∀ v : Fin d → ℝ, L v ℓ = 0 ↔ v j' = 0) :
    j = j' := by
  by_contra hne
  have h1 : (Pi.single j (1 : ℝ) : Fin d → ℝ) j' = 0 := Pi.single_eq_of_ne (Ne.symm hne) 1
  have h3 := (h _).mp ((h' _).mpr h1)
  simp at h3

/-- One direction of the wall correspondence: an injection `J → J'` matching tangent
hyperplanes. -/
theorem exists_wall_embedding {H : (Fin d → ℝ) → (Fin d → ℝ)} (hH : AnalyticAt ℝ H 0)
    (hL : Injective (fderiv ℝ H 0)) {J J' : Finset (Fin d)}
    (hwall : ∀ j ∈ J, ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ J', H x ℓ = 0) :
    ∃ f : J → J', Injective f ∧
      ∀ (j : J) (v : Fin d → ℝ), fderiv ℝ H 0 v (f j) = 0 ↔ v j = 0 := by
  have := fun j : J => exists_tangent_wall hH hL (hwall j j.2)
  choose ℓ hℓ hprop using this
  refine ⟨fun j => ⟨ℓ j, hℓ j⟩, fun j j' hjj' => ?_, hprop⟩
  have h1 : ℓ j = ℓ j' := congrArg Subtype.val hjj'
  have h2 := hprop j'
  rw [← h1] at h2
  exact Subtype.ext (tangent_wall_unique (hprop j) h2)

theorem exists_wall_equiv_of_embeddings {J J' : Finset (Fin d)}
    {L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} (f : J → J') (hf : Injective f) (g : J' → J)
    (hg : Injective g) (hprop : ∀ (j : J) (v : Fin d → ℝ), L v (f j) = 0 ↔ v j = 0) :
    ∃ σ : J ≃ J', ∀ (j : J) (v : Fin d → ℝ), L v (σ j) = 0 ↔ v j = 0 := by
  have hcard : Fintype.card J = Fintype.card J' :=
    le_antisymm (Fintype.card_le_of_injective f hf) (Fintype.card_le_of_injective g hg)
  have hbij : Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  exact ⟨Equiv.ofBijective f hbij, hprop⟩

/-- A left inverse near `0` makes the derivative injective. -/
theorem fderiv_injective_of_leftInverse {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : DifferentiableAt ℝ H 0) (hG : DifferentiableAt ℝ G (H 0))
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x) : Injective (fderiv ℝ H 0) := by
  have h1 : fderiv ℝ (G ∘ H) 0 = (fderiv ℝ G (H 0)).comp (fderiv ℝ H 0) := fderiv_comp 0 hG hH
  have h2 : fderiv ℝ (G ∘ H) 0 = fderiv ℝ id 0 := Filter.EventuallyEq.fderiv_eq hGH
  rw [fderiv_id] at h2
  have hid : ∀ v, fderiv ℝ G (H 0) (fderiv ℝ H 0 v) = v := by
    intro v
    have := congrArg (fun T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => T v) (h1.symm.trans h2)
    simpa using this
  intro v w hvw
  rw [← hid v, ← hid w, hvw]

/-! ### Exponent matching (T2) -/

/-- The one-variable core of exponent matching: at a generic wall point `w`, restriction to the
transversal line `s ↦ w + s • e_j` compares orders of vanishing. -/
theorem exponent_eq_of_line {H : (Fin d → ℝ) → (Fin d → ℝ)} {c c' : (Fin d → ℝ) → ℝ}
    {J J' : Finset (Fin d)} {e e' : Fin d → ℕ} {j ℓ₀ : Fin d} (hj : j ∈ J) (hℓ₀ : ℓ₀ ∈ J')
    {w : Fin d → ℝ} (hwj : w j = 0) (hw : ∀ i ∈ J, i ≠ j → w i ≠ 0)
    (hHw : ∀ ℓ ∈ J', ℓ ≠ ℓ₀ → H w ℓ ≠ 0) (hHw0 : H w ℓ₀ = 0)
    (hder : fderiv ℝ H w (Pi.single j 1) ℓ₀ ≠ 0) (hH : AnalyticAt ℝ H w)
    (hc : ContinuousAt c w) (hc0 : c w ≠ 0) (hc' : ContinuousAt c' w) (hc'0 : c' w ≠ 0)
    (hid : ∀ᶠ x in 𝓝 w, c x * ∏ i ∈ J, x i ^ e i = c' x * ∏ ℓ ∈ J', H x ℓ ^ e' ℓ) :
    e j = e' ℓ₀ := by
  classical
  set ej : Fin d → ℝ := Pi.single j (1 : ℝ) with hej
  set γ : ℝ → (Fin d → ℝ) := fun s => w + s • ej with hγ
  have hγ0 : γ 0 = w := by simp [hγ]
  have hγcont : Continuous γ := by rw [hγ]; fun_prop
  have hγtend : Tendsto γ (𝓝 0) (𝓝 w) := by
    have := hγcont.tendsto 0
    rwa [hγ0] at this
  have hγj : ∀ s, γ s j = s := by intro s; simp [hγ, hej, hwj]
  have hγi : ∀ s i, i ≠ j → γ s i = w i := by
    intro s i hi; simp [hγ, hej, Pi.single_eq_of_ne hi]
  -- the transversal coordinate `φ s = H (γ s) ℓ₀` and its slope
  have hγan : AnalyticAt ℝ γ 0 := by
    rw [hγ]; exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hHγ : AnalyticAt ℝ H (γ 0) := by rw [hγ0]; exact hH
  have hφan : AnalyticAt ℝ (fun s => H (γ s) ℓ₀) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ℓ₀).analyticAt _).comp
      (hHγ.comp hγan)
  have hγ' : HasDerivAt γ ej 0 := by
    have := (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) ej).const_add w
    rw [hγ]; simpa using this
  have hHfd : HasFDerivAt H (fderiv ℝ H w) (γ 0) := by
    rw [hγ0]; exact hH.differentiableAt.hasFDerivAt
  have hφ' : HasDerivAt (fun s => H (γ s) ℓ₀) (fderiv ℝ H w ej ℓ₀) 0 :=
    hasDerivAt_pi.mp (hHfd.comp_hasDerivAt 0 hγ') ℓ₀
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℝ, ψ = dslope (fun s => H (γ s) ℓ₀) 0 := ⟨_, rfl⟩
  have hψan : AnalyticAt ℝ ψ 0 := by
    obtain ⟨p, hp⟩ := hφan
    rw [hψdef]
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  have hφ0 : H (γ 0) ℓ₀ = 0 := by rw [hγ0]; exact hHw0
  have hφψ : ∀ s, H (γ s) ℓ₀ = s * ψ s := by
    intro s
    have := sub_smul_dslope (fun s => H (γ s) ℓ₀) 0 s
    rw [sub_zero, hφ0, sub_zero, smul_eq_mul] at this
    rw [hψdef]; exact this.symm
  have hψ0 : ψ 0 ≠ 0 := by
    rw [hψdef, dslope_same, hφ'.deriv]; exact hder
  -- restrict the identity to the line
  have hid' : ∀ᶠ s in 𝓝 (0 : ℝ),
      c (γ s) * ∏ i ∈ J, γ s i ^ e i = c' (γ s) * ∏ ℓ ∈ J', H (γ s) ℓ ^ e' ℓ :=
    hγtend.eventually hid
  have hprodL : ∀ s, ∏ i ∈ J.erase j, γ s i ^ e i = ∏ i ∈ J.erase j, w i ^ e i := fun s =>
    Finset.prod_congr rfl fun i hi => by rw [hγi s i (Finset.ne_of_mem_erase hi)]
  have hL : ∀ s, c (γ s) * ∏ i ∈ J, γ s i ^ e i =
      s ^ e j * (c (γ s) * ∏ i ∈ J.erase j, w i ^ e i) := by
    intro s
    rw [← Finset.mul_prod_erase J _ hj, hγj, hprodL]
    ring
  have hR : ∀ s, c' (γ s) * ∏ ℓ ∈ J', H (γ s) ℓ ^ e' ℓ =
      s ^ e' ℓ₀ * (c' (γ s) * ψ s ^ e' ℓ₀ * ∏ ℓ ∈ J'.erase ℓ₀, H (γ s) ℓ ^ e' ℓ) := by
    intro s
    rw [← Finset.mul_prod_erase J' _ hℓ₀, hφψ s, mul_pow]
    ring
  have hkey : ∀ᶠ s in 𝓝 (0 : ℝ), s ^ e j * (c (γ s) * ∏ i ∈ J.erase j, w i ^ e i) =
      s ^ e' ℓ₀ * (c' (γ s) * ψ s ^ e' ℓ₀ * ∏ ℓ ∈ J'.erase ℓ₀, H (γ s) ℓ ^ e' ℓ) :=
    hid'.mono fun s hs => by rw [← hL, ← hR]; exact hs
  -- continuity and nonvanishing of the two units
  have hcγ : ContinuousAt (fun s => c (γ s)) 0 := hc.comp_of_eq hγcont.continuousAt hγ0
  have hHγc : ContinuousAt (fun s => H (γ s)) 0 :=
    hH.continuousAt.comp_of_eq hγcont.continuousAt hγ0
  have hg : ContinuousAt (fun s => c (γ s) * ∏ i ∈ J.erase j, w i ^ e i) 0 :=
    hcγ.mul continuousAt_const
  have hG : ContinuousAt
      (fun s => c' (γ s) * ψ s ^ e' ℓ₀ * ∏ ℓ ∈ J'.erase ℓ₀, H (γ s) ℓ ^ e' ℓ) 0 := by
    refine ((hc'.comp_of_eq hγcont.continuousAt hγ0).mul (hψan.continuousAt.pow _)).mul ?_
    have hP : Continuous (fun y : Fin d → ℝ => ∏ ℓ ∈ J'.erase ℓ₀, y ℓ ^ e' ℓ) :=
      continuous_finsetProd _ fun ℓ _ => (continuous_apply ℓ).pow _
    exact hP.continuousAt.comp hHγc
  have hg0 : (fun s => c (γ s) * ∏ i ∈ J.erase j, w i ^ e i) 0 ≠ 0 := by
    change c (γ 0) * ∏ i ∈ J.erase j, w i ^ e i ≠ 0
    rw [hγ0]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (hw i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)))
  have hG0 : (fun s => c' (γ s) * ψ s ^ e' ℓ₀ * ∏ ℓ ∈ J'.erase ℓ₀, H (γ s) ℓ ^ e' ℓ) 0 ≠ 0 := by
    change c' (γ 0) * ψ 0 ^ e' ℓ₀ * ∏ ℓ ∈ J'.erase ℓ₀, H (γ 0) ℓ ^ e' ℓ ≠ 0
    rw [hγ0]
    exact mul_ne_zero (mul_ne_zero hc'0 (pow_ne_zero _ hψ0))
      (Finset.prod_ne_zero_iff.mpr fun ℓ hℓ =>
        pow_ne_zero _ (hHw ℓ (Finset.mem_of_mem_erase hℓ) (Finset.ne_of_mem_erase hℓ)))
  exact eq_of_pow_mul_eventuallyEq hg hG hg0 hG0 hkey

/-- Existence of a generic wall point: on the wall `x j = 0` near `0` there is `w` whose other
`J`-coordinates and other target coordinates are nonzero, with `H w ℓ₀ = 0`, nonzero transversal
derivative, and at which all the local data are available. -/
theorem exists_generic_wall_point {H : (Fin d → ℝ) → (Fin d → ℝ)} (hH : AnalyticAt ℝ H 0)
    {c c' : (Fin d → ℝ) → ℝ}
    (hc : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt c x) (hc0 : c 0 ≠ 0)
    (hc' : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt c' x) (hc'0 : c' 0 ≠ 0)
    {J J' : Finset (Fin d)} {j ℓ₀ : Fin d}
    (htan : ∀ v : Fin d → ℝ, fderiv ℝ H 0 v ℓ₀ = 0 ↔ v j = 0)
    (hother : ∀ ℓ ∈ J', ℓ ≠ ℓ₀ → ∃ u : Fin d → ℝ, u j = 0 ∧ fderiv ℝ H 0 u ℓ ≠ 0)
    (hwall : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ J', H x ℓ = 0) {e e' : Fin d → ℕ}
    (hid : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      c x * ∏ i ∈ J, x i ^ e i = c' x * ∏ ℓ ∈ J', H x ℓ ^ e' ℓ) :
    ∃ w : Fin d → ℝ, w j = 0 ∧ (∀ i ∈ J, i ≠ j → w i ≠ 0) ∧ (∀ ℓ ∈ J', ℓ ≠ ℓ₀ → H w ℓ ≠ 0) ∧
      H w ℓ₀ = 0 ∧ fderiv ℝ H w (Pi.single j 1) ℓ₀ ≠ 0 ∧ AnalyticAt ℝ H w ∧
      ContinuousAt c w ∧ c w ≠ 0 ∧ ContinuousAt c' w ∧ c' w ≠ 0 ∧
      ∀ᶠ x in 𝓝 w, c x * ∏ i ∈ J, x i ^ e i = c' x * ∏ ℓ ∈ J', H x ℓ ^ e' ℓ := by
  classical
  set L := fderiv ℝ H 0 with hLdef
  -- a generic direction in the hyperplane `v j = 0`
  let P : Submodule ℝ (Fin d → ℝ) := LinearMap.ker (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ)
  have hmemP : ∀ u : Fin d → ℝ, u ∈ P ↔ u j = 0 := fun u => by simp [P, LinearMap.mem_ker]
  let Φ : Fin d ⊕ Fin d → (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    Sum.elim (fun i => LinearMap.proj i)
      (fun ℓ => (LinearMap.proj ℓ).comp (L : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)))
  obtain ⟨v, hvP, hv⟩ := exists_forall_ne_zero_of_forall_exists P Φ
    ((J.erase j).disjSum (J'.erase ℓ₀)) (by
      intro i hi
      rcases Finset.mem_disjSum.mp hi with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · refine ⟨Pi.single a 1,
          (hmemP _).mpr (Pi.single_eq_of_ne (Finset.ne_of_mem_erase ha).symm _), ?_⟩
        simp [Φ]
      · obtain ⟨u, huj, hu⟩ := hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
        exact ⟨u, (hmemP _).mpr huj, by simpa [Φ] using hu⟩)
  have hvj : v j = 0 := (hmemP v).mp hvP
  have hvi : ∀ i ∈ J, i ≠ j → v i ≠ 0 := fun i hi hij => by
    have := hv (Sum.inl i) (Finset.inl_mem_disjSum.mpr (Finset.mem_erase.mpr ⟨hij, hi⟩))
    simpa [Φ] using this
  have hvℓ : ∀ ℓ ∈ J', ℓ ≠ ℓ₀ → L v ℓ ≠ 0 := fun ℓ hℓ hne => by
    have := hv (Sum.inr ℓ) (Finset.inr_mem_disjSum.mpr (Finset.mem_erase.mpr ⟨hne, hℓ⟩))
    simpa [Φ] using this
  -- eventual properties along `t ↦ t • v`
  have htend := tendsto_smul_const_zero v
  have hW3 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ ℓ ∈ J'.erase ℓ₀, H (t • v) ℓ ≠ 0 := by
    refine (eventually_all_finset _).mpr fun ℓ hℓ => ?_
    rcases (analyticAt_line_coord hH v ℓ).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exact absurd (eq_zero_of_hasDerivAt_of_eventually_zero
        (hasDerivAt_line_coord hH.differentiableAt v ℓ) h0)
        (hvℓ ℓ (Finset.mem_of_mem_erase hℓ) (Finset.ne_of_mem_erase hℓ))
    · exact h0
  have hW4 : ∀ᶠ t in 𝓝 (0 : ℝ), fderiv ℝ H (t • v) (Pi.single j 1) ℓ₀ ≠ 0 := by
    have hcont : ContinuousAt (fun x : Fin d → ℝ => fderiv ℝ H x (Pi.single j 1) ℓ₀) 0 := by
      have h1 : ContinuousAt (fderiv ℝ H) 0 := hH.fderiv.continuousAt
      have h2 : Continuous (fun T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => T (Pi.single j 1) ℓ₀) :=
        (continuous_apply ℓ₀).comp (continuous_id.clm_apply continuous_const)
      exact h2.continuousAt.comp h1
    have hne : fderiv ℝ H 0 (Pi.single j 1) ℓ₀ ≠ 0 := by
      intro h0
      have := (htan _).mp h0
      simp at this
    exact htend.eventually (hcont.eventually_ne hne)
  have hW5 : ∀ᶠ t in 𝓝 (0 : ℝ), c (t • v) ≠ 0 ∧ ContinuousAt c (t • v) :=
    htend.eventually ((hc.self_of_nhds.eventually_ne hc0).and hc)
  have hW5' : ∀ᶠ t in 𝓝 (0 : ℝ), c' (t • v) ≠ 0 ∧ ContinuousAt c' (t • v) :=
    htend.eventually ((hc'.self_of_nhds.eventually_ne hc'0).and hc')
  have hW6 : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ H (t • v) := htend.eventually hH.eventually_analyticAt
  have hW7 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᶠ x in 𝓝 (t • v),
      c x * ∏ i ∈ J, x i ^ e i = c' x * ∏ ℓ ∈ J', H x ℓ ^ e' ℓ :=
    htend.eventually (eventually_eventually_nhds.mpr hid)
  have hW8 : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ ℓ ∈ J', H (t • v) ℓ = 0 :=
    (htend.eventually hwall).mono fun t ht => ht (by simp [hvj])
  have hall := ((((((hW4.and hW5).and hW5').and hW6).and hW7).and hW8).filter_mono
    nhdsWithin_le_nhds).and (hW3.and eventually_mem_nhdsWithin)
  obtain ⟨t, ⟨⟨⟨⟨⟨h4, h5a, h5b⟩, h5c, h5d⟩, h6⟩, h7⟩, h8⟩, h3, ht0⟩ := hall.exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨t • v, by simp [hvj], fun i hi hij => ?_,
    fun ℓ hℓ hne => h3 ℓ (Finset.mem_erase.mpr ⟨hne, hℓ⟩), ?_, h4, h6, h5b, h5a, h5d, h5c, h7⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero ht0' (hvi i hi hij)
  · obtain ⟨ℓ, hℓ, hℓ0⟩ := h8
    by_cases hne : ℓ = ℓ₀
    · rwa [hne] at hℓ0
    · exact absurd hℓ0 (h3 ℓ (Finset.mem_erase.mpr ⟨hne, hℓ⟩))

/-- **Exponent matching** (k-free). Let `σ : J ≃ J'` match tangent hyperplanes
(`fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0`) and let `H` carry each wall `x j = 0` into the union of
the target walls near `0`. Then any unit-monomial identity
`c x * ∏_{i ∈ J} x_i^{e i} = c' x * ∏_{ℓ ∈ J'} (H x)_ℓ^{e' ℓ}` near `0`, with `c, c'` continuous
near `0` and nonzero at `0`, forces `e j = e' (σ j)`. -/
theorem exponent_eq_of_unit_monomial_eq {H : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) {J J' : Finset (Fin d)} (σ : J ≃ J')
    (htan : ∀ (j : J) (v : Fin d → ℝ), fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0)
    (hwall : ∀ j : J, ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ J', H x ℓ = 0)
    {c c' : (Fin d → ℝ) → ℝ} (hc : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt c x) (hc0 : c 0 ≠ 0)
    (hc' : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt c' x) (hc'0 : c' 0 ≠ 0) {e e' : Fin d → ℕ}
    (hid : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      c x * ∏ i ∈ J, x i ^ e i = c' x * ∏ ℓ ∈ J', H x ℓ ^ e' ℓ) (j : J) :
    e j = e' (σ j) := by
  have hother : ∀ ℓ ∈ J', ℓ ≠ (σ j : Fin d) →
      ∃ u : Fin d → ℝ, u j = 0 ∧ fderiv ℝ H 0 u ℓ ≠ 0 := by
    intro ℓ hℓ hne
    obtain ⟨j', hj'⟩ := σ.surjective ⟨ℓ, hℓ⟩
    have hjj' : (j' : Fin d) ≠ j := by
      intro h
      apply hne
      have : j' = j := Subtype.ext h
      rw [← this, hj']
    refine ⟨Pi.single j' 1, Pi.single_eq_of_ne hjj'.symm _, fun h0 => ?_⟩
    have := (htan j' _).mp (by rw [hj']; exact h0)
    simp at this
  obtain ⟨w, hwj, hw, hHw, hHw0, hder, hHan, hcw, hcw0, hc'w, hc'w0, hidw⟩ :=
    exists_generic_wall_point hH hc hc0 hc' hc'0 (htan j) hother (hwall j) hid
  exact exponent_eq_of_line j.2 (σ j).2 hwj hw hHw hHw0 hder hHan hcw hcw0 hc'w hc'w0 hidw

/-! ### The wall correspondence -/

/-- **Local wall invariance.** Two monomial normal forms `F, F'` of the same phase at a point,
related by a local analytic diffeomorphism given by both directions `H, G` (`G ∘ H = id` and
`H ∘ G = id` near `0`), have wall sets in bijection `σ : F.J ≃ F'.J`, with matching phase
exponents `F.k j = F'.k (σ j)` and matching tangent hyperplanes:
`fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0`. -/
theorem exists_wall_equiv (F F' : MonomialForm d) {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hH0 : H 0 = 0)
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x)
    (hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), H (G y) = y)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x)) :
    ∃ σ : F.J ≃ F'.J, (∀ j : F.J, F.k j = F'.k (σ j)) ∧
      ∀ (j : F.J) (v : Fin d → ℝ), fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0 := by
  have hG0 : G 0 = 0 := by
    have := hGH.self_of_nhds
    rwa [hH0] at this
  have hL : Injective (fderiv ℝ H 0) :=
    fderiv_injective_of_leftInverse hH.differentiableAt (by rw [hH0]; exact hG.differentiableAt)
      hGH
  have hM : Injective (fderiv ℝ G 0) :=
    fderiv_injective_of_leftInverse hG.differentiableAt (by rw [hG0]; exact hH.differentiableAt)
      hHG
  have hGt : Tendsto G (𝓝 0) (𝓝 (0 : Fin d → ℝ)) := by
    have := hG.continuousAt.tendsto
    rwa [hG0] at this
  have hphase' : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), F'.phase y = F.phase (G y) := by
    filter_upwards [hHG, hGt.eventually hphase] with y h1 h2
    rw [h2, h1]
  have hwall : ∀ j ∈ F.J, ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ F'.J, H x ℓ = 0 :=
    fun j hj => eventually_exists_wall_zero F F' hH.continuousAt hH0 hphase hj
  have hwall' : ∀ ℓ ∈ F'.J, ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), y ℓ = 0 → ∃ j ∈ F.J, G y j = 0 :=
    fun ℓ hℓ => eventually_exists_wall_zero F' F hG.continuousAt hG0 hphase' hℓ
  obtain ⟨f, hf, hfprop⟩ := exists_wall_embedding hH hL hwall
  obtain ⟨g, hg, -⟩ := exists_wall_embedding hG hM hwall'
  obtain ⟨σ, hσ⟩ := exists_wall_equiv_of_embeddings f hf g hg hfprop
  refine ⟨σ, fun j => ?_, hσ⟩
  have hc : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt F.a x :=
    F.a_analytic.eventually_analyticAt.mono fun _ h => h.continuousAt
  have hc' : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt (fun x => F'.a (H x)) x := by
    have h1 : AnalyticAt ℝ F'.a (H 0) := by rw [hH0]; exact F'.a_analytic
    exact (h1.comp hH).eventually_analyticAt.mono fun _ h => h.continuousAt
  have hc'0 : (fun x => F'.a (H x)) 0 ≠ 0 := by
    change F'.a (H 0) ≠ 0
    rw [hH0]; exact F'.a_ne
  have hid : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.a x * ∏ i ∈ F.J, x i ^ (2 * F.k i) =
      (fun x => F'.a (H x)) x * ∏ ℓ ∈ F'.J, H x ℓ ^ (2 * F'.k ℓ) := hphase
  have := exponent_eq_of_unit_monomial_eq hH σ hσ (fun j => hwall j j.2) hc F.a_ne hc' hc'0 hid j
  omega

/-- **Jacobian exponents are chart-independent.** With the hypotheses of `exists_wall_equiv`
and a Jacobian transformation law `b x ∏_J x_j^{h j} = b' (H x) ∏_{J'} (H x)_ℓ^{h' ℓ} · u x`
near `0` (units `b, b', u` continuous near `0` and nonzero at `0`; `u` stands for the Jacobian
determinant `det (fderiv ℝ H x)`), the bijection `σ` of the phase also matches `h j = h' (σ j)`. -/
theorem exists_wall_equiv_jac (F F' : MonomialForm d) {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hH0 : H 0 = 0)
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x)
    (hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), H (G y) = y)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x))
    {b b' u : (Fin d → ℝ) → ℝ} {h h' : Fin d → ℕ}
    (hb : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt b x) (hb0 : b 0 ≠ 0)
    (hb' : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ContinuousAt b' y) (hb'0 : b' 0 ≠ 0)
    (hu : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt u x) (hu0 : u 0 ≠ 0)
    (hjac : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      b x * ∏ j ∈ F.J, x j ^ h j = b' (H x) * (∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ) * u x) :
    ∃ σ : F.J ≃ F'.J, (∀ j : F.J, F.k j = F'.k (σ j)) ∧ (∀ j : F.J, h j = h' (σ j)) ∧
      ∀ (j : F.J) (v : Fin d → ℝ), fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0 := by
  obtain ⟨σ, hk, hσ⟩ := exists_wall_equiv F F' hH hG hH0 hGH hHG hphase
  refine ⟨σ, hk, fun j => ?_, hσ⟩
  have hwall : ∀ j : F.J, ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x j = 0 → ∃ ℓ ∈ F'.J, H x ℓ = 0 :=
    fun j => eventually_exists_wall_zero F F' hH.continuousAt hH0 hphase j.2
  have hHt : Tendsto H (𝓝 0) (𝓝 (0 : Fin d → ℝ)) := by
    have := hH.continuousAt.tendsto
    rwa [hH0] at this
  have hc' : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt (fun x => b' (H x) * u x) x := by
    filter_upwards [hu, hH.eventually_analyticAt, hHt.eventually hb'] with x h1 h2 h3
    exact (h3.comp h2.continuousAt).mul h1
  have hc'0 : (fun x => b' (H x) * u x) 0 ≠ 0 := by
    change b' (H 0) * u 0 ≠ 0
    rw [hH0]; exact mul_ne_zero hb'0 hu0
  have hid : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), b x * ∏ i ∈ F.J, x i ^ h i =
      (fun x => b' (H x) * u x) x * ∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ :=
    hjac.mono fun x hx => by
      change b x * ∏ i ∈ F.J, x i ^ h i = b' (H x) * u x * ∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ
      rw [hx]; ring
  exact exponent_eq_of_unit_monomial_eq hH σ hσ hwall hb hb0 hc' hc'0 hid j

/-! ### The Jacobian determinant as a unit -/

/-- A left inverse near `0` makes the Jacobian determinant at `0` nonzero. -/
theorem det_fderiv_ne_zero_of_leftInverse {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : DifferentiableAt ℝ H 0) (hG : DifferentiableAt ℝ G (H 0))
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x) : (fderiv ℝ H 0).det ≠ 0 := by
  have h1 : fderiv ℝ (G ∘ H) 0 = (fderiv ℝ G (H 0)).comp (fderiv ℝ H 0) := fderiv_comp 0 hG hH
  have h2 : fderiv ℝ (G ∘ H) 0 = fderiv ℝ id 0 := Filter.EventuallyEq.fderiv_eq hGH
  rw [fderiv_id] at h2
  have h3 : (fderiv ℝ G (H 0)).det * (fderiv ℝ H 0).det = 1 := by
    have := congrArg ContinuousLinearMap.det (h1.symm.trans h2)
    have hc : (((fderiv ℝ G (H 0)).comp (fderiv ℝ H 0) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
        ((fderiv ℝ G (H 0) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)).comp
          (fderiv ℝ H 0 : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) := rfl
    rw [ContinuousLinearMap.det, hc, LinearMap.det_comp] at this
    simpa [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] using this
  exact right_ne_zero_of_mul_eq_one h3

/-- The Jacobian determinant of an analytic map is continuous near `0`. -/
theorem eventually_continuousAt_det_fderiv {H : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) :
    ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt (fun x => (fderiv ℝ H x).det) x :=
  hH.fderiv.eventually_analyticAt.mono fun _ hx =>
    ContinuousLinearMap.continuous_det.continuousAt.comp hx.continuousAt

/-- `exists_wall_equiv_jac` with the Jacobian determinant `det (fderiv ℝ H x)` itself as the
transformation unit. -/
theorem exists_wall_equiv_jac_det (F F' : MonomialForm d) {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hH0 : H 0 = 0)
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x)
    (hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), H (G y) = y)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x))
    {b b' : (Fin d → ℝ) → ℝ} {h h' : Fin d → ℕ}
    (hb : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt b x) (hb0 : b 0 ≠ 0)
    (hb' : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ContinuousAt b' y) (hb'0 : b' 0 ≠ 0)
    (hjac : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), b x * ∏ j ∈ F.J, x j ^ h j =
      b' (H x) * (∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ) * (fderiv ℝ H x).det) :
    ∃ σ : F.J ≃ F'.J, (∀ j : F.J, F.k j = F'.k (σ j)) ∧ (∀ j : F.J, h j = h' (σ j)) ∧
      ∀ (j : F.J) (v : Fin d → ℝ), fderiv ℝ H 0 v (σ j) = 0 ↔ v j = 0 :=
  exists_wall_equiv_jac F F' hH hG hH0 hGH hHG hphase hb hb0 hb' hb'0
    (eventually_continuousAt_det_fderiv hH)
    (det_fderiv_ne_zero_of_leftInverse hH.differentiableAt
      (by rw [hH0]; exact hG.differentiableAt) hGH) hjac

/-! ### Invariants of the point -/

/-- The depth `|J|` (number of walls through the point) is chart-independent. -/
theorem card_eq_of_phase_eq (F F' : MonomialForm d) {H G : (Fin d → ℝ) → (Fin d → ℝ)}
    (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0) (hH0 : H 0 = 0)
    (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x)
    (hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), H (G y) = y)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x)) :
    F.J.card = F'.J.card := by
  obtain ⟨σ, -, -⟩ := exists_wall_equiv F F' hH hG hH0 hGH hHG hphase
  exact Finset.card_eq_of_equiv σ

/-- The multiset of exponent pairs `(k j, h j)` over the walls is chart-independent. -/
theorem multiset_pairs_eq_of_phase_eq (F F' : MonomialForm d)
    {H G : (Fin d → ℝ) → (Fin d → ℝ)} (hH : AnalyticAt ℝ H 0) (hG : AnalyticAt ℝ G 0)
    (hH0 : H 0 = 0) (hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), G (H x) = x)
    (hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), H (G y) = y)
    (hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), F.phase x = F'.phase (H x))
    {b b' u : (Fin d → ℝ) → ℝ} {h h' : Fin d → ℕ}
    (hb : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt b x) (hb0 : b 0 ≠ 0)
    (hb' : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ContinuousAt b' y) (hb'0 : b' 0 ≠ 0)
    (hu : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt u x) (hu0 : u 0 ≠ 0)
    (hjac : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      b x * ∏ j ∈ F.J, x j ^ h j = b' (H x) * (∏ ℓ ∈ F'.J, H x ℓ ^ h' ℓ) * u x) :
    F.J.val.map (fun j => (F.k j, h j)) = F'.J.val.map (fun ℓ => (F'.k ℓ, h' ℓ)) := by
  obtain ⟨σ, hk, hh, -⟩ :=
    exists_wall_equiv_jac F F' hH hG hH0 hGH hHG hphase hb hb0 hb' hb'0 hu hu0 hjac
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ F.J.nodup F'.J.nodup
    (fun j hj => (σ ⟨j, hj⟩ : Fin d)) (fun j hj => (σ ⟨j, hj⟩).2) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ hEq
    exact congrArg Subtype.val (σ.injective (Subtype.ext hEq))
  · intro b hb
    obtain ⟨a, ha⟩ := σ.surjective ⟨b, hb⟩
    exact ⟨a, a.2, by change (σ a : Fin d) = b; rw [ha]⟩
  · intro a ha
    rw [hk ⟨a, ha⟩, hh ⟨a, ha⟩]

end Grammar.NormalCrossing
