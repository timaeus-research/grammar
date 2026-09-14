/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.NormalCrossingWallInvariance
import Monomialize.Transport.ResolvedJacobian

/-!
# Intrinsic depth and resonance data on the resolved manifold

Consult #127, Units D5a–D5b. At every point `P` of the exceptional divisor `D = {K ∘ π = 0}` of
a Watanabe modification `R`, hironaka supplies an even chart box centred at `P`
(`exists_evenChartBox`): a chart `φ` of the maximal analytic atlas with `φ P = 0`, in which the
phase is the even monomial `∏ u_j^{2 k_j}` and the Jacobian of the blow-down is
`b(u) ∏ u_j^{h_j}` with an analytic nonvanishing unit `b`. The **pair data** of the box is the
multiset of `(k_j, h_j)` over the active coordinates `k_j > 0`.

* `EvenChartBox.pairData_eq_of_centered` (**the atlas adapter, D5a**): two even chart boxes
  centred at the same point have the same pair data. The transition `H = φ' ∘ φ⁻¹` is analytic
  near `0` with analytic inverse (both charts lie in the maximal atlas), the two phases agree,
  and the two Jacobian laws are related by the chain rule `det Dψ = det Dψ'(H) · det DH`; the
  inactive Jacobian exponents vanish (hironaka `h_eq_zero_of_k_eq_zero`), so the wall-invariance
  lemma `multiset_pairs_eq_of_phase_eq` (CDXXVII) applies with the Jacobian monomial indexed by
  the active walls.
* `pairs R hK0 P` (**D5b**): the intrinsic pair multiset of a point of `U` (empty
  off the divisor), `depth = card`, the resonance relation `Resonates μ (k, h) ↔ ∃ m, 2kμ = h+1+m`
  and the resonance count `resonanceCount μ P`; `pairs_eq_pairData` (any centred box computes
  it), `depth_le_dim`, `resonanceCount_le_depth`, `depth_pos_iff` (positive exactly on the
  divisor), `resonanceCount_eq_zero_of_nonpos`, `fst_pos_of_mem_pairs`.

Non-claims: no local coordinate formula for the pairs of nearby points yet (D5c), hence no
closedness of the depth filtration here; the resonance count is an upper bound on the possible
logarithmic multiplicity, not a nonvanishing invariant.
-/

open Set Filter Topology Function
open scoped Manifold ContDiff
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open IsManifold (maximalAtlas)

namespace Grammar

namespace NormalCrossing

variable {d : ℕ} {K : (Fin d → ℝ) → ℝ} {W : TopologicalSpace.Opens (Fin d → ℝ)}
  {R : WatanabeModificationOn K W}

namespace EvenChartBoxDepth

variable (E : EvenChartBox R)

/-- The active coordinates of an even chart box. -/
def active : Finset (Fin d) := Finset.univ.filter fun j => 0 < E.k j

theorem mem_active {j : Fin d} : j ∈ active E ↔ 0 < E.k j := by simp [active]

/-- The pair data `{(k_j, h_j) : j active}` of an even chart box. -/
def pairData : Multiset (ℕ × ℕ) := (active E).val.map fun j => (E.k j, E.h j)

/-- The monomial normal form of an even chart box (unit `1`). -/
noncomputable def monomialForm : MonomialForm d where
  J := active E
  k := E.k
  a := fun _ => 1
  a_analytic := analyticAt_const
  a_ne := one_ne_zero
  k_pos := fun _ hj => (mem_active E).1 hj

/-- The phase of the monomial form is the phase `K ∘ ψ` on the chart target. -/
theorem phase_monomialForm {u : Fin d → ℝ} (hu : u ∈ E.φ.target) :
    (monomialForm E).phase u = K (watanabeRep R.g E.φ u) := by
  rw [E.phase_eq u hu, MonomialForm.phase]
  change 1 * ∏ j ∈ active E, u j ^ (2 * E.k j) = ∏ j, u j ^ (2 * E.k j)
  rw [one_mul, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => 0 < E.k j)]
  have : ∏ j ∈ Finset.univ.filter (fun j => ¬ 0 < E.k j), u j ^ (2 * E.k j) = 1 :=
    Finset.prod_eq_one fun j hj => by
      rw [Nat.eq_zero_of_not_pos (Finset.mem_filter.1 hj).2]; simp
  rw [this, mul_one]
  rfl

theorem zero_mem_target : (0 : Fin d → ℝ) ∈ E.φ.target := E.zero_mem.1

theorem symm_zero_eq {P : R.U} (hP : P ∈ E.φ.source) (hP0 : E.φ P = 0) : E.φ.symm 0 = P := by
  rw [← hP0]; exact E.φ.left_inv hP

/-- The transition domain from `E` to `E'`: the part of the target of `E` carried into the
source of `E'`. -/
def transDomain (E' : EvenChartBox R) : Set (Fin d → ℝ) := E.φ.target ∩ E.φ.symm ⁻¹' E'.φ.source

theorem isOpen_transDomain (E' : EvenChartBox R) : IsOpen (transDomain E E') :=
  E.φ.continuousOn_symm.isOpen_inter_preimage E.φ.open_target E'.φ.open_source

/-- The transition map between two charts of the maximal atlas is analytic on the transition
domain. -/
theorem analyticOnNhd_trans (E' : EvenChartBox R) :
    AnalyticOnNhd ℝ (E'.φ ∘ E.φ.symm) (transDomain E E') := by
  have h : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (E'.φ ∘ E.φ.symm) (transDomain E E') :=
    (contMDiffOn_of_mem_maximalAtlas E'.mem).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas E.mem).mono inter_subset_left) fun _ hx => hx.2
  exact (isOpen_transDomain E E').analyticOn_iff_analyticOnNhd.mp
    ((contDiffOn_omega_iff_analyticOn (isOpen_transDomain E E').uniqueDiffOn).mp
      (contMDiffOn_iff_contDiffOn.mp h))

/-- The chart representatives of the blow-down are compatible with the transition. -/
theorem rep_comp_trans (E' : EvenChartBox R) {u : Fin d → ℝ} (hu : u ∈ transDomain E E') :
    watanabeRep R.g E'.φ (E'.φ (E.φ.symm u)) = watanabeRep R.g E.φ u := by
  change R.gv (E'.φ.symm (E'.φ (E.φ.symm u))) = R.gv (E.φ.symm u)
  rw [E'.φ.left_inv hu.2]

theorem trans_mem_target (E' : EvenChartBox R) {u : Fin d → ℝ} (hu : u ∈ transDomain E E') :
    E'.φ (E.φ.symm u) ∈ E'.φ.target := E'.φ.map_source hu.2

/-- The Jacobian chain rule along the transition. -/
theorem det_fderiv_rep_eq (E' : EvenChartBox R) {u : Fin d → ℝ} (hu : u ∈ transDomain E E') :
    (fderiv ℝ (watanabeRep R.g E.φ) u).det =
      (fderiv ℝ (watanabeRep R.g E'.φ) (E'.φ (E.φ.symm u))).det *
        (fderiv ℝ (E'.φ ∘ E.φ.symm) u).det := by
  have heq : watanabeRep R.g E.φ =ᶠ[𝓝 u] watanabeRep R.g E'.φ ∘ (E'.φ ∘ E.φ.symm) :=
    eventually_of_mem ((isOpen_transDomain E E').mem_nhds hu) fun v hv =>
      (rep_comp_trans E E' hv).symm
  rw [heq.fderiv_eq,
    fderiv_comp u (E'.analyticOnNhd_rep _ (trans_mem_target E E' hu)).differentiableAt
      (analyticOnNhd_trans E E' u hu).differentiableAt]
  exact LinearMap.det_comp _ _

/-- ★★★ **The atlas adapter**: two even chart boxes centred at the same point have the same pair
data. -/
theorem pairData_eq_of_centered (E' : EvenChartBox R) {P : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) (hP' : P ∈ E'.φ.source) (hP0' : E'.φ P = 0) :
    pairData E = pairData E' := by
  have hs0 : E.φ.symm 0 = P := symm_zero_eq E hP hP0
  have hs0' : E'.φ.symm 0 = P := symm_zero_eq E' hP' hP0'
  have h0 : (0 : Fin d → ℝ) ∈ transDomain E E' :=
    ⟨zero_mem_target E, by rw [mem_preimage, hs0]; exact hP'⟩
  have h0' : (0 : Fin d → ℝ) ∈ transDomain E' E :=
    ⟨zero_mem_target E', by rw [mem_preimage, hs0']; exact hP⟩
  have hnhds : transDomain E E' ∈ 𝓝 (0 : Fin d → ℝ) := (isOpen_transDomain E E').mem_nhds h0
  have hnhds' : transDomain E' E ∈ 𝓝 (0 : Fin d → ℝ) := (isOpen_transDomain E' E).mem_nhds h0'
  have hH : AnalyticAt ℝ (E'.φ ∘ E.φ.symm) 0 := analyticOnNhd_trans E E' 0 h0
  have hG : AnalyticAt ℝ (E.φ ∘ E'.φ.symm) 0 := analyticOnNhd_trans E' E 0 h0'
  have hH0 : (E'.φ ∘ E.φ.symm) 0 = 0 := by
    change E'.φ (E.φ.symm 0) = 0
    rw [hs0, hP0']
  have hGH : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), (E.φ ∘ E'.φ.symm) ((E'.φ ∘ E.φ.symm) x) = x :=
    eventually_of_mem hnhds fun x hx => by
      change E.φ (E'.φ.symm (E'.φ (E.φ.symm x))) = x
      rw [E'.φ.left_inv hx.2, E.φ.right_inv hx.1]
  have hHG : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), (E'.φ ∘ E.φ.symm) ((E.φ ∘ E'.φ.symm) y) = y :=
    eventually_of_mem hnhds' fun y hy => by
      change E'.φ (E.φ.symm (E.φ (E'.φ.symm y))) = y
      rw [E.φ.left_inv hy.2, E'.φ.right_inv hy.1]
  have hphase : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      (monomialForm E).phase x = (monomialForm E').phase ((E'.φ ∘ E.φ.symm) x) :=
    eventually_of_mem hnhds fun x hx => by
      rw [phase_monomialForm E hx.1, Function.comp_apply,
        phase_monomialForm E' (trans_mem_target E E' hx)]
      exact (congrArg K (rep_comp_trans E E' hx)).symm
  have hb : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), ContinuousAt E.b x :=
    eventually_of_mem (E.φ.open_target.mem_nhds (zero_mem_target E)) fun x hx =>
      (E.b_analytic x hx).continuousAt
  have hb' : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ContinuousAt E'.b y :=
    eventually_of_mem (E'.φ.open_target.mem_nhds (zero_mem_target E')) fun y hy =>
      (E'.b_analytic y hy).continuousAt
  have hjac : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ),
      E.b x * ∏ j ∈ (monomialForm E).J, x j ^ E.h j =
        E'.b ((E'.φ ∘ E.φ.symm) x) * (∏ ℓ ∈ (monomialForm E').J, (E'.φ ∘ E.φ.symm) x ℓ ^ E'.h ℓ) *
          (fderiv ℝ (E'.φ ∘ E.φ.symm) x).det :=
    eventually_of_mem hnhds fun x hx => by
      have h1 := E.jac_eq x hx.1
      have h2 := E'.jac_eq _ (trans_mem_target E E' hx)
      rw [E.prod_pow_h_eq_active] at h1
      rw [E'.prod_pow_h_eq_active] at h2
      change E.b x * ∏ j ∈ Finset.univ.filter (fun j => 0 < E.k j), x j ^ E.h j =
        E'.b (E'.φ (E.φ.symm x)) *
          (∏ ℓ ∈ Finset.univ.filter (fun ℓ => 0 < E'.k ℓ), (E'.φ (E.φ.symm x)) ℓ ^ E'.h ℓ) *
          (fderiv ℝ (E'.φ ∘ E.φ.symm) x).det
      rw [← h1, ← h2, det_fderiv_rep_eq E E' hx]
  exact multiset_pairs_eq_of_phase_eq (monomialForm E) (monomialForm E') hH hG hH0 hGH hHG hphase
    hb (E.b_ne_zero 0 (zero_mem_target E)) hb' (E'.b_ne_zero 0 (zero_mem_target E'))
    (eventually_continuousAt_det_fderiv hH)
    (det_fderiv_ne_zero_of_leftInverse hH.differentiableAt
      (by rw [hH0]; exact hG.differentiableAt) hGH) hjac

end EvenChartBoxDepth

open EvenChartBoxDepth

section Intrinsic

variable (R)

/-- The exceptional divisor `{K ∘ π = 0}`. -/
def divisor : Set R.U := {P | K (R.gv P) = 0}

theorem exists_centeredEvenChartBox (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x) {P : R.U}
    (hP : P ∈ divisor R) : ∃ E : EvenChartBox R, P ∈ E.φ.source ∧ E.φ P = 0 :=
  exists_evenChartBox R hK0 hP

open Classical in
/-- ★ **The intrinsic pair data** of a point of the resolved manifold: the pair data of any even
chart box centred at the point (empty off the divisor). -/
noncomputable def pairs (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x) (P : R.U) :
    Multiset (ℕ × ℕ) :=
  if hP : P ∈ divisor R then pairData (Classical.choose (exists_centeredEvenChartBox R hK0 hP))
  else 0

/-- A centred even chart box has its centre on the divisor. -/
theorem mem_divisor_of_centered (E : EvenChartBox R) {P : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) : P ∈ divisor R := by
  have : K (watanabeRep R.g E.φ 0) = 0 := E.zero_mem.2
  change K (R.gv P) = 0
  rwa [← symm_zero_eq E hP hP0]

variable (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)

/-- Every even chart box centred at `P` computes the intrinsic pair data. -/
theorem pairs_eq_pairData (E : EvenChartBox R) {P : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) : pairs R hK0 P = pairData E := by
  have hD := mem_divisor_of_centered R E hP hP0
  unfold pairs
  rw [dif_pos hD]
  obtain ⟨hs, h0⟩ := Classical.choose_spec (exists_centeredEvenChartBox R hK0 hD)
  exact pairData_eq_of_centered _ E hs h0 hP hP0

theorem pairs_eq_zero_of_not_mem_divisor {P : R.U} (hP : P ∉ divisor R) : pairs R hK0 P = 0 := by
  unfold pairs; rw [dif_neg hP]

/-- The intrinsic depth `d_D(P)`: the number of walls through `P`. -/
noncomputable def depth (P : R.U) : ℕ := (pairs R hK0 P).card

/-- Resonance of an exponent `μ` with a wall of data `(k, h)`: `2kμ ∈ h + 1 + ℕ`. -/
def Resonates (μ : ℝ) (p : ℕ × ℕ) : Prop := ∃ m : ℕ, 2 * (p.1 : ℝ) * μ = (p.2 : ℝ) + 1 + m

open Classical in
/-- The resonance count `r_μ(P)`: the number of walls through `P` resonant with `μ`. -/
noncomputable def resonanceCount (μ : ℝ) (P : R.U) : ℕ :=
  ((pairs R hK0 P).filter (Resonates μ)).card

theorem depth_eq_card_active (E : EvenChartBox R) {P : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) : depth R hK0 P = (active E).card := by
  rw [depth, pairs_eq_pairData R hK0 E hP hP0, pairData, Multiset.card_map, Finset.card_val]

theorem depth_le_dim (P : R.U) : depth R hK0 P ≤ d := by
  by_cases hP : P ∈ divisor R
  · obtain ⟨E, hs, h0⟩ := exists_centeredEvenChartBox R hK0 hP
    rw [depth_eq_card_active R hK0 E hs h0]
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [depth, pairs_eq_zero_of_not_mem_divisor R hK0 hP]; simp

open Classical in
theorem resonanceCount_le_depth (μ : ℝ) (P : R.U) :
    resonanceCount R hK0 μ P ≤ depth R hK0 P :=
  Multiset.card_le_card (Multiset.filter_le _ _)

theorem fst_pos_of_mem_pairs {P : R.U} {p : ℕ × ℕ} (hp : p ∈ pairs R hK0 P) : 0 < p.1 := by
  by_cases hP : P ∈ divisor R
  · obtain ⟨E, hs, h0⟩ := exists_centeredEvenChartBox R hK0 hP
    rw [pairs_eq_pairData R hK0 E hs h0, pairData, Multiset.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact (mem_active E).1 hj
  · rw [pairs_eq_zero_of_not_mem_divisor R hK0 hP] at hp
    exact absurd hp (Multiset.notMem_zero p)

/-- The depth is positive exactly on the divisor. -/
theorem depth_pos_iff (P : R.U) : 0 < depth R hK0 P ↔ P ∈ divisor R := by
  constructor
  · intro h
    by_contra hP
    rw [depth, pairs_eq_zero_of_not_mem_divisor R hK0 hP] at h
    simp at h
  · intro hP
    obtain ⟨E, hs, h0⟩ := exists_centeredEvenChartBox R hK0 hP
    rw [depth_eq_card_active R hK0 E hs h0, Finset.card_pos]
    obtain ⟨j, hj⟩ := E.k_active
    exact ⟨j, (mem_active E).2 hj⟩

theorem resonanceCount_eq_zero_of_nonpos {μ : ℝ} (hμ : μ ≤ 0) (P : R.U) :
    resonanceCount R hK0 μ P = 0 := by
  classical
  unfold resonanceCount
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro p - ⟨m, hm⟩
  have h1 : 2 * (p.1 : ℝ) * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hμ
  have h2 : (0 : ℝ) < (p.2 : ℝ) + 1 + m := by positivity
  linarith

end Intrinsic

end NormalCrossing

end Grammar
