/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedDepth

/-!
# The local coordinate formula for the pair data; the closed depth and resonance filtrations

Consult #127, Unit D5c. In an even chart box `E` (centred anywhere), the intrinsic pair data of a
point `Q` of the chart source is read off from its chart coordinate `u₀ = φ Q`:

  `pairs Q = {(k_j, h_j) : j active, u₀_j = 0}`   (`pairs_eq_of_mem_source`).

Proof: translating the chart by `u₀`, the phase becomes `a(v) ∏_{j : u₀_j = 0} v_j^{2k_j}` with the
analytic nonvanishing unit `a(v) = ∏_{j : u₀_j ≠ 0} (v_j + u₀_j)^{2k_j}` (`translatedForm`), and the
Jacobian becomes `b_T(v) ∏_{j : u₀_j = 0} v_j^{h_j}` with the unit
`b_T(v) = b(v + u₀) ∏_{j : u₀_j ≠ 0} (v_j + u₀_j)^{h_j}` (the inactive exponents vanish, hironaka
`h_eq_zero_of_k_eq_zero`); comparing with any even chart box centred at `Q` through the
translated transition `H v = φ' (φ⁻¹ (v + u₀))` (analytic near `0` with analytic inverse), the
wall-invariance lemma `multiset_pairs_eq_of_phase_eq` (CDXXVII) identifies the two multisets.
Off the divisor both sides are empty.

Consequences: the pairs of nearby points are sub-multisets of the pairs of the centre
(`pairs_le_of_mem_source`), so depth and every resonance count are upper semicontinuous: the
filtrations `depthGE c = {depth ≥ c}` and `resonanceGE μ c = {r_μ ≥ c}` are CLOSED
(`isClosed_depthGE`, `isClosed_resonanceGE`; `K` continuous on `W` for the complement of the
divisor), the shallow loci `shallowOpen c = U ∖ depthGE (c+1)` are open, `depthGE 1 = divisor`,
`depthGE (d+1) = ∅`, and in a chart centred at a point of depth `c` the locus `depthGE c` is the
coordinate subspace `{u_j = 0, j active}` while `depthGE (c+1)` is absent
(`mem_depthGE_iff_of_centered`, `not_mem_depthGE_succ_of_mem_source`).

Non-claims: no bundled submanifold structure on the strata, no Whitney conditions, no
comparison across resolutions.
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

/-- The walls through the chart point `u₀`: the active coordinates vanishing at `u₀`. -/
noncomputable def wallsAt (u₀ : Fin d → ℝ) : Finset (Fin d) := (active E).filter fun j => u₀ j = 0

/-- The active coordinates not vanishing at `u₀`. -/
noncomputable def offWallsAt (u₀ : Fin d → ℝ) : Finset (Fin d) :=
  (active E).filter fun j => ¬ u₀ j = 0

theorem u₀_ne_zero_of_mem_offWallsAt {u₀ : Fin d → ℝ} {j : Fin d} (hj : j ∈ offWallsAt E u₀) :
    u₀ j ≠ 0 := (Finset.mem_filter.1 hj).2

/-- Splitting a translated monomial with exponents vanishing on the inactive coordinates. -/
theorem prod_pow_translate (u₀ v : Fin d → ℝ) {e : Fin d → ℕ} (he : ∀ j, E.k j = 0 → e j = 0) :
    ∏ j, (v j + u₀ j) ^ e j =
      (∏ j ∈ wallsAt E u₀, v j ^ e j) * ∏ j ∈ offWallsAt E u₀, (v j + u₀ j) ^ e j := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => 0 < E.k j)]
  have hin : ∏ j ∈ Finset.univ.filter (fun j => ¬ 0 < E.k j), (v j + u₀ j) ^ e j = 1 :=
    Finset.prod_eq_one fun j hj => by
      rw [he j (Nat.eq_zero_of_not_pos (Finset.mem_filter.1 hj).2), pow_zero]
  rw [hin, mul_one]
  change ∏ j ∈ active E, (v j + u₀ j) ^ e j = _
  rw [← Finset.prod_filter_mul_prod_filter_not (active E) (fun j => u₀ j = 0)]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2, add_zero]

/-- The translated monomial normal form of the chart at `u₀`. -/
noncomputable def translatedForm (u₀ : Fin d → ℝ) : MonomialForm d where
  J := wallsAt E u₀
  k := E.k
  a := fun v => ∏ j ∈ offWallsAt E u₀, (v j + u₀ j) ^ (2 * E.k j)
  a_analytic := by
    refine (Finset.analyticAt_prod (offWallsAt E u₀) (f := fun j v => (v j + u₀ j) ^ (2 * E.k j))
      (c := 0) fun j _ => ?_).congr (Eventually.of_forall fun v => ?_)
    · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).analyticAt _).add
        analyticAt_const).pow _
    · simp only [Finset.prod_apply]
  a_ne := by
    refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_
    rw [Pi.zero_apply, zero_add]
    exact u₀_ne_zero_of_mem_offWallsAt E hj
  k_pos := fun _ hj => (mem_active E).1 (Finset.mem_filter.1 hj).1

theorem phase_translatedForm (u₀ v : Fin d → ℝ) (hv : v + u₀ ∈ E.φ.target) :
    (translatedForm E u₀).phase v = K (watanabeRep R.g E.φ (v + u₀)) := by
  rw [E.phase_eq _ hv, MonomialForm.phase]
  change (∏ j ∈ offWallsAt E u₀, (v j + u₀ j) ^ (2 * E.k j)) *
    ∏ j ∈ wallsAt E u₀, v j ^ (2 * E.k j) = ∏ j, (v + u₀) j ^ (2 * E.k j)
  simp only [Pi.add_apply]
  rw [prod_pow_translate E u₀ v (fun j hj => by rw [hj, mul_zero]), mul_comm]

/-- The translated Jacobian unit. -/
noncomputable def jacUnitAt (u₀ v : Fin d → ℝ) : ℝ :=
  E.b (v + u₀) * ∏ j ∈ offWallsAt E u₀, (v j + u₀ j) ^ E.h j

theorem det_fderiv_rep_translate (u₀ v : Fin d → ℝ) (hv : v + u₀ ∈ E.φ.target) :
    (fderiv ℝ (watanabeRep R.g E.φ) (v + u₀)).det =
      jacUnitAt E u₀ v * ∏ j ∈ wallsAt E u₀, v j ^ E.h j := by
  rw [E.jac_eq _ hv, jacUnitAt]
  have : ∏ j, (v + u₀) j ^ E.h j = ∏ j, (v j + u₀ j) ^ E.h j := rfl
  rw [this, prod_pow_translate E u₀ v (fun j hj => E.h_eq_zero_of_k_eq_zero hj)]
  ring

theorem continuousAt_jacUnitAt (u₀ v : Fin d → ℝ) (hv : v + u₀ ∈ E.φ.target) :
    ContinuousAt (jacUnitAt E u₀) v := by
  refine ContinuousAt.mul ?_ ?_
  · exact ContinuousAt.comp (g := E.b) (f := fun w => w + u₀) (E.b_analytic _ hv).continuousAt
      (continuous_id.add continuous_const).continuousAt
  · exact (continuous_finsetProd _ fun j _ =>
      ((continuous_apply j).add continuous_const).pow _).continuousAt

theorem jacUnitAt_zero_ne_zero (u₀ : Fin d → ℝ) (hu₀ : u₀ ∈ E.φ.target) :
    jacUnitAt E u₀ 0 ≠ 0 := by
  unfold jacUnitAt
  rw [zero_add]
  refine mul_ne_zero (E.b_ne_zero u₀ hu₀) (Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  rw [Pi.zero_apply, zero_add]
  exact pow_ne_zero _ (u₀_ne_zero_of_mem_offWallsAt E hj)

/-- Off the divisor no active coordinate vanishes. -/
theorem wallsAt_eq_empty_of_ne_zero {u₀ : Fin d → ℝ} (hu₀ : u₀ ∈ E.φ.target)
    (hK : K (watanabeRep R.g E.φ u₀) ≠ 0) : wallsAt E u₀ = ∅ := by
  rw [E.phase_eq u₀ hu₀] at hK
  unfold wallsAt
  rw [Finset.filter_eq_empty_iff]
  intro j hj h0
  refine hK (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [h0]
  exact zero_pow (by have := (mem_active E).1 hj; omega)

/-- The translated transition to a chart `E'`: `v ↦ φ' (φ⁻¹ (v + u₀))`. -/
def transAt (E' : EvenChartBox R) (u₀ v : Fin d → ℝ) : Fin d → ℝ := E'.φ (E.φ.symm (v + u₀))

/-- Its inverse `w ↦ φ (φ'⁻¹ w) − u₀`. -/
def transAtInv (E' : EvenChartBox R) (u₀ w : Fin d → ℝ) : Fin d → ℝ := E.φ (E'.φ.symm w) - u₀

theorem analyticAt_transAt (E' : EvenChartBox R) {u₀ : Fin d → ℝ} (hu₀ : u₀ ∈ transDomain E E') :
    AnalyticAt ℝ (transAt E E' u₀) 0 :=
  (analyticOnNhd_trans E E' u₀ hu₀).comp_of_eq (analyticAt_id.add analyticAt_const)
    (by simp)

theorem analyticAt_transAtInv (E' : EvenChartBox R) (u₀ : Fin d → ℝ)
    (h0 : (0 : Fin d → ℝ) ∈ transDomain E' E) : AnalyticAt ℝ (transAtInv E E' u₀) 0 :=
  (analyticOnNhd_trans E' E 0 h0).sub analyticAt_const

theorem fderiv_transAt (E' : EvenChartBox R) (u₀ v : Fin d → ℝ) :
    fderiv ℝ (transAt E E' u₀) v = fderiv ℝ (E'.φ ∘ E.φ.symm) (v + u₀) :=
  fderiv_comp_add_right (f := E'.φ ∘ E.φ.symm) u₀

end EvenChartBoxDepth

open EvenChartBoxDepth

section Local

variable (R) (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)

/-- ★★★ **The local coordinate formula**: in any even chart box, the intrinsic pair data of a
point of the chart source is the pair data of the active coordinates vanishing at its chart
coordinate. -/
theorem pairs_eq_of_mem_source (E : EvenChartBox R) {Q : R.U} (hQ : Q ∈ E.φ.source) :
    pairs R hK0 Q = (wallsAt E (E.φ Q)).val.map fun j => (E.k j, E.h j) := by
  set u₀ := E.φ Q with hu₀def
  have hu₀ : u₀ ∈ E.φ.target := E.φ.map_source hQ
  have hsymm : E.φ.symm u₀ = Q := E.φ.left_inv hQ
  have hrep : watanabeRep R.g E.φ u₀ = R.gv Q := by
    change R.gv (E.φ.symm u₀) = R.gv Q
    rw [hsymm]
  by_cases hQD : Q ∈ divisor R
  · obtain ⟨E', hQ', hQ0'⟩ := exists_centeredEvenChartBox R hK0 hQD
    rw [pairs_eq_pairData R hK0 E' hQ' hQ0']
    have hu₀T : u₀ ∈ transDomain E E' := ⟨hu₀, by rw [mem_preimage, hsymm]; exact hQ'⟩
    have h0' : (0 : Fin d → ℝ) ∈ transDomain E' E :=
      ⟨zero_mem_target E', by rw [mem_preimage, symm_zero_eq E' hQ' hQ0']; exact hQ⟩
    -- neighbourhoods of `0` on which the translated identities hold
    have hnhds : {v : Fin d → ℝ | v + u₀ ∈ transDomain E E'} ∈ 𝓝 (0 : Fin d → ℝ) := by
      refine ((isOpen_transDomain E E').preimage
        (continuous_id.add continuous_const : Continuous fun v : Fin d → ℝ => v + u₀)).mem_nhds ?_
      change (0 : Fin d → ℝ) + u₀ ∈ transDomain E E'
      rw [zero_add]
      exact hu₀T
    have hnhds' : transDomain E' E ∈ 𝓝 (0 : Fin d → ℝ) := (isOpen_transDomain E' E).mem_nhds h0'
    have hH : AnalyticAt ℝ (transAt E E' u₀) 0 := analyticAt_transAt E E' hu₀T
    have hG : AnalyticAt ℝ (transAtInv E E' u₀) 0 := analyticAt_transAtInv E E' u₀ h0'
    have hH0 : transAt E E' u₀ 0 = 0 := by
      change E'.φ (E.φ.symm (0 + u₀)) = 0
      rw [zero_add, hsymm, hQ0']
    have hGH : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ), transAtInv E E' u₀ (transAt E E' u₀ v) = v :=
      eventually_of_mem hnhds fun v hv => by
        change E.φ (E'.φ.symm (E'.φ (E.φ.symm (v + u₀)))) - u₀ = v
        rw [E'.φ.left_inv hv.2, E.φ.right_inv hv.1, add_sub_cancel_right]
    have hHG : ∀ᶠ w in 𝓝 (0 : Fin d → ℝ), transAt E E' u₀ (transAtInv E E' u₀ w) = w :=
      eventually_of_mem hnhds' fun w hw => by
        change E'.φ (E.φ.symm (E.φ (E'.φ.symm w) - u₀ + u₀)) = w
        rw [sub_add_cancel, E.φ.left_inv hw.2, E'.φ.right_inv hw.1]
    have hphase : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ),
        (translatedForm E u₀).phase v = (monomialForm E').phase (transAt E E' u₀ v) :=
      eventually_of_mem hnhds fun v hv => by
        rw [phase_translatedForm E u₀ v hv.1, transAt,
          phase_monomialForm E' (trans_mem_target E E' hv)]
        exact (congrArg K (rep_comp_trans E E' hv)).symm
    have hb : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ), ContinuousAt (jacUnitAt E u₀) v :=
      eventually_of_mem hnhds fun v hv => continuousAt_jacUnitAt E u₀ v hv.1
    have hb' : ∀ᶠ w in 𝓝 (0 : Fin d → ℝ), ContinuousAt E'.b w :=
      eventually_of_mem (E'.φ.open_target.mem_nhds (zero_mem_target E')) fun w hw =>
        (E'.b_analytic w hw).continuousAt
    have hjac : ∀ᶠ v in 𝓝 (0 : Fin d → ℝ),
        jacUnitAt E u₀ v * ∏ j ∈ (translatedForm E u₀).J, v j ^ E.h j =
          E'.b (transAt E E' u₀ v) *
            (∏ ℓ ∈ (monomialForm E').J, transAt E E' u₀ v ℓ ^ E'.h ℓ) *
            (fderiv ℝ (transAt E E' u₀) v).det :=
      eventually_of_mem hnhds fun v hv => by
        have h1 := det_fderiv_rep_translate E u₀ v hv.1
        have h2 := E'.jac_eq _ (trans_mem_target E E' hv)
        rw [E'.prod_pow_h_eq_active] at h2
        change jacUnitAt E u₀ v * ∏ j ∈ wallsAt E u₀, v j ^ E.h j =
          E'.b (E'.φ (E.φ.symm (v + u₀))) *
            (∏ ℓ ∈ Finset.univ.filter (fun ℓ => 0 < E'.k ℓ),
              (E'.φ (E.φ.symm (v + u₀))) ℓ ^ E'.h ℓ) *
            (fderiv ℝ (transAt E E' u₀) v).det
        rw [← h1, ← h2, fderiv_transAt, det_fderiv_rep_eq E E' hv]
    exact (multiset_pairs_eq_of_phase_eq (translatedForm E u₀) (monomialForm E') hH hG hH0 hGH hHG
      hphase hb (jacUnitAt_zero_ne_zero E u₀ hu₀) hb' (E'.b_ne_zero 0 (zero_mem_target E'))
      (eventually_continuousAt_det_fderiv hH)
      (det_fderiv_ne_zero_of_leftInverse hH.differentiableAt
        (by rw [hH0]; exact hG.differentiableAt) hGH) hjac).symm
  · rw [pairs_eq_zero_of_not_mem_divisor R hK0 hQD,
      wallsAt_eq_empty_of_ne_zero E hu₀ (by rw [hrep]; exact hQD)]
    rfl

/-- The pairs of a point of the chart source are a sub-multiset of the pairs of the centre. -/
theorem pairs_le_of_mem_source (E : EvenChartBox R) {P Q : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) (hQ : Q ∈ E.φ.source) : pairs R hK0 Q ≤ pairs R hK0 P := by
  rw [pairs_eq_of_mem_source R hK0 E hQ, pairs_eq_pairData R hK0 E hP hP0, pairData]
  exact Multiset.map_le_map (Finset.val_le_iff.2 (Finset.filter_subset _ _))

theorem depth_le_of_mem_source (E : EvenChartBox R) {P Q : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) (hQ : Q ∈ E.φ.source) : depth R hK0 Q ≤ depth R hK0 P :=
  Multiset.card_le_card (pairs_le_of_mem_source R hK0 E hP hP0 hQ)

open Classical in
theorem resonanceCount_le_of_mem_source (E : EvenChartBox R) {P Q : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) (hQ : Q ∈ E.φ.source) (μ : ℝ) :
    resonanceCount R hK0 μ Q ≤ resonanceCount R hK0 μ P :=
  Multiset.card_le_card (Multiset.filter_le_filter _ (pairs_le_of_mem_source R hK0 E hP hP0 hQ))

theorem depth_eq_card_wallsAt (E : EvenChartBox R) {Q : R.U} (hQ : Q ∈ E.φ.source) :
    depth R hK0 Q = (wallsAt E (E.φ Q)).card := by
  rw [depth, pairs_eq_of_mem_source R hK0 E hQ, Multiset.card_map, Finset.card_val]

/-! ### The closed filtrations -/

/-- The locus of depth at least `c`. -/
def depthGE (c : ℕ) : Set R.U := {P | c ≤ depth R hK0 P}

/-- The locus of resonance count at least `c`. -/
def resonanceGE (μ : ℝ) (c : ℕ) : Set R.U := {P | c ≤ resonanceCount R hK0 μ P}

/-- The shallow locus `U ∖ D_{≥ c+1}`. -/
def shallowOpen (c : ℕ) : Set R.U := (depthGE R hK0 (c + 1))ᶜ

/-- The depth stratum `{depth = c}`. -/
def depthStratum (c : ℕ) : Set R.U := {P | depth R hK0 P = c}

/-- Off the divisor the depth is zero. -/
theorem depth_eq_zero_of_not_mem_divisor {P : R.U} (hP : P ∉ divisor R) : depth R hK0 P = 0 := by
  rw [depth, pairs_eq_zero_of_not_mem_divisor R hK0 hP, Multiset.card_zero]

theorem resonanceCount_eq_zero_of_not_mem_divisor (μ : ℝ) {P : R.U} (hP : P ∉ divisor R) :
    resonanceCount R hK0 μ P = 0 :=
  Nat.eq_zero_of_le_zero ((resonanceCount_le_depth R hK0 μ P).trans
    (depth_eq_zero_of_not_mem_divisor R hK0 hP).le)

/-- A monotone-under-restriction invariant (bounded by the value at the centre of every centred
chart, zero off the divisor) has closed superlevel sets. -/
theorem isClosed_superlevel (hK0 : ∀ x ∈ (W : Set (Fin d → ℝ)), 0 ≤ K x)
    (hKc : ContinuousOn K (W : Set (Fin d → ℝ))) (f : R.U → ℕ)
    (hf0 : ∀ P, P ∉ divisor R → f P = 0)
    (hmono : ∀ (E : EvenChartBox R) {P Q : R.U}, P ∈ E.φ.source → E.φ P = 0 → Q ∈ E.φ.source →
      f Q ≤ f P) (c : ℕ) : IsClosed {P | c ≤ f P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro P hP
  change ¬ c ≤ f P at hP
  rw [not_le] at hP
  by_cases hPD : P ∈ divisor R
  · obtain ⟨E, hs, h0⟩ := exists_centeredEvenChartBox R hK0 hPD
    refine ⟨E.φ.source, fun Q hQ => ?_, E.φ.open_source, hs⟩
    change ¬ c ≤ f Q
    rw [not_le]
    exact (hmono E hs h0 hQ).trans_lt hP
  · refine ⟨R.offDivisor, fun Q hQ => ?_, R.isOpen_offDivisor hKc, hPD⟩
    change ¬ c ≤ f Q
    rw [not_le, hf0 Q hQ]
    exact (Nat.zero_le _).trans_lt hP

/-- ★★ **The depth filtration is closed.** -/
theorem isClosed_depthGE (hKc : ContinuousOn K (W : Set (Fin d → ℝ))) (c : ℕ) :
    IsClosed (depthGE R hK0 c) :=
  isClosed_superlevel R hK0 hKc _ (fun _ hP => depth_eq_zero_of_not_mem_divisor R hK0 hP)
    (fun E _ _ hP hP0 hQ => depth_le_of_mem_source R hK0 E hP hP0 hQ) c

/-- ★★ **The resonance filtration is closed.** -/
theorem isClosed_resonanceGE (hKc : ContinuousOn K (W : Set (Fin d → ℝ))) (μ : ℝ) (c : ℕ) :
    IsClosed (resonanceGE R hK0 μ c) :=
  isClosed_superlevel R hK0 hKc _
    (fun _ hP => resonanceCount_eq_zero_of_not_mem_divisor R hK0 μ hP)
    (fun E _ _ hP hP0 hQ => resonanceCount_le_of_mem_source R hK0 E hP hP0 hQ μ) c

theorem isOpen_shallowOpen (hKc : ContinuousOn K (W : Set (Fin d → ℝ))) (c : ℕ) :
    IsOpen (shallowOpen R hK0 c) :=
  (isClosed_depthGE R hK0 hKc (c + 1)).isOpen_compl

theorem depthGE_one : depthGE R hK0 1 = divisor R := by
  ext P
  exact depth_pos_iff R hK0 P

theorem depthGE_succ_dim : depthGE R hK0 (d + 1) = ∅ := by
  ext P
  refine ⟨fun h => ?_, fun h => h.elim⟩
  change d + 1 ≤ depth R hK0 P at h
  exact absurd (depth_le_dim R hK0 P) (by omega)

theorem depthGE_antitone {c c' : ℕ} (h : c ≤ c') : depthGE R hK0 c' ⊆ depthGE R hK0 c :=
  fun _ hP => h.trans hP

theorem resonanceGE_subset_depthGE (μ : ℝ) (c : ℕ) :
    resonanceGE R hK0 μ c ⊆ depthGE R hK0 c :=
  fun P hP => hP.trans (resonanceCount_le_depth R hK0 μ P)

/-- ★★ **Coordinate description of the depth locus**: in a chart centred at a point `P` of depth
`c`, the locus `depthGE c` is the coordinate subspace of the active walls. -/
theorem mem_depthGE_iff_of_centered (E : EvenChartBox R) {P Q : R.U} (hP : P ∈ E.φ.source)
    (hP0 : E.φ P = 0) (hQ : Q ∈ E.φ.source) :
    Q ∈ depthGE R hK0 (depth R hK0 P) ↔ ∀ j ∈ active E, E.φ Q j = 0 := by
  change depth R hK0 P ≤ depth R hK0 Q ↔ _
  rw [depth_eq_card_active R hK0 E hP hP0, depth_eq_card_wallsAt R hK0 E hQ, wallsAt,
    ← Finset.card_filter_eq_iff]
  exact ⟨fun h => le_antisymm (Finset.card_filter_le _ _) h, fun h => h.ge⟩

/-- In a chart centred at a point of depth `c`, no point has depth `c + 1` or more. -/
theorem not_mem_depthGE_succ_of_mem_source (E : EvenChartBox R) {P Q : R.U}
    (hP : P ∈ E.φ.source) (hP0 : E.φ P = 0) (hQ : Q ∈ E.φ.source) :
    Q ∉ depthGE R hK0 (depth R hK0 P + 1) := by
  change ¬ depth R hK0 P + 1 ≤ depth R hK0 Q
  have := depth_le_of_mem_source R hK0 E hP hP0 hQ
  omega

end Local

end NormalCrossing

end Grammar
