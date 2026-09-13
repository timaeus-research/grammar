/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateBoxCertificate
import Grammar.ChartModelGeometry

/-!
# The water-filling collar of a chart with a tangential unit (consult #111, unit D)

The chart model (CCCXLIII) has an active set `A ⊆ Fin d` of divisor coordinates, orders `k`
(`k_i > 0` on `A`, `k_i = 0` off `A`) and the phase `u(y) · ∏_{i∈A} y_i^{2k_i}` with a positive
unit `u` depending only on the INACTIVE coordinates. This module redoes the water-filling collar
of CCCXXII for such a chart on the box `[0,a]^d`: for every nonempty `I ⊆ A` the water level is
taken at the UNIT-CORRECTED tangential factor `U_I(t) = u(t) · ∏_{j∉I} t_j^{2k_j}` (the inactive
coordinates contribute the factor `1`, so this is the active tangential monomial times the unit),
`q_I(t) = (δ / U_I(t))^{1/|I|}`; the base `B_I` constrains only the ACTIVE tangential coordinates
(`δ ≤ U_I(t) · (t_j^{2k_j})^{|I|}` for `j ∈ A ∖ I`), the inactive ones being free parameters in
`[0,a]`; the widths `ℓ_{I,i} = q_I^{1/(2k_i)}`, the side `b_I = δ^{1/(2Σ_I k)}` and
`λ = ℓ / b_I` satisfy the NORMALISATION IDENTITY `u(t) · (t_I(t) · ∏_{i∈I} λ_i^{2k_i}) = 1` —
exactly the shape `WData.hnorm` of the weighted core (E2, CCCXLV). The covering and the
disjointness off the thresholds are the arguments of CCCXXII run on the active coordinates at the
level `δ / u(w)`; the bound on the water level is `q_I ≤ (δ/c)^{1/|A|}` for a lower bound `c` of
the unit on the box. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace ChartCollar

open NormalisedBox WaterFilling

variable {d : ℕ} (A : Finset (Fin d)) (k : Fin d → ℕ) (u : (Fin d → ℝ) → ℝ) (I : Finset (Fin d))
  (a δ : ℝ)

/-- The unit read on the tangential coordinates (the normal coordinates set to `0`). -/
noncomputable def uT (t : Tan I → ℝ) : ℝ := u (liftPoint I t)

/-- The unit-corrected tangential factor `U_I(t) = u(t) · t_I(t)`. -/
noncomputable def U (t : Tan I → ℝ) : ℝ := uT u I t * tanUnit k I t

/-- The water level `q_I(t) = (δ / U_I(t))^{1/|I|}`. -/
noncomputable def q (t : Tan I → ℝ) : ℝ := (δ / U k u I t) ^ ((I.card : ℝ)⁻¹)

/-- The base `B_I`: `0 ≤ t_j ≤ a` for every tangential `j`, and
`δ ≤ U_I(t) · (t_j^{2k_j})^{|I|}` for the ACTIVE tangential `j`. -/
def baseSet : Set (Tan I → ℝ) :=
  {t | ∀ j : Tan I, 0 ≤ t j ∧ t j ≤ a ∧
    (j.1 ∈ A → δ ≤ U k u I t * (t j ^ (2 * k j.1)) ^ I.card)}

/-- The physical normal width `ℓ_{I,i}(t) = q_I(t)^{1/(2k_i)}`. -/
noncomputable def ell (t : Tan I → ℝ) (i : Nrm I) : ℝ := q k u I δ t ^ (((2 * k i.1 : ℕ) : ℝ)⁻¹)

/-- The normalised widths `λ_{I,i}(t) = ℓ_{I,i}(t) / b_I`. -/
noncomputable def lamT (t : Tan I → ℝ) (i : Nrm I) : ℝ := ell k u I δ t i / side k I δ

/-! ### The unit and the tangential factor -/

section Basic

variable (hk0 : ∀ i, i ∉ A → k i = 0) (hIA : I ⊆ A)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')

include hIA hu_tan in
/-- The unit depends only on the inactive coordinates, which are tangential: `u(t(w)) = u(w)`. -/
theorem uT_tan (w : Fin d → ℝ) : uT u I (tan I w) = u w := by
  unfold uT
  refine hu_tan _ _ fun j hj => ?_
  rw [liftPoint_apply, dif_neg fun hjI => hj (hIA hjI)]
  rfl

theorem liftPoint_mem_box (ha : 0 ≤ a) {t : Tan I → ℝ} (ht : ∀ j, 0 ≤ t j ∧ t j ≤ a) :
    liftPoint I t ∈ piBox d (Icc 0 a) := by
  intro j _
  rw [liftPoint_apply]
  split_ifs with hj
  · exact ⟨le_rfl, ha⟩
  · exact ht ⟨j, hj⟩

include hk0 in
/-- The tangential factor is the product over the active tangential coordinates. -/
theorem tanUnit_eq_prod_sdiff (w : Fin d → ℝ) :
    tanUnit k I (tan I w) = ∏ j ∈ A \ I, w j ^ (2 * k j) := by
  rw [tanUnit_eq_prod_compl]
  refine (Finset.prod_subset (fun j hj => ?_) fun j hj hj' => ?_).symm
  · exact Finset.mem_compl.2 (Finset.mem_sdiff.1 hj).2
  · have hjA : j ∉ A := fun hA => hj' (Finset.mem_sdiff.2 ⟨hA, Finset.mem_compl.1 hj⟩)
    rw [hk0 j hjA, mul_zero, pow_zero]

include hk0 in
theorem tanUnit_eq_prod_sdiff' (t : Tan I → ℝ) :
    tanUnit k I t = ∏ j ∈ A \ I, liftPoint I t j ^ (2 * k j) := by
  conv_lhs => rw [← tan_liftPoint I t]
  exact tanUnit_eq_prod_sdiff A k I hk0 _

end Basic

/-! ### The base -/

section Base

variable (hkA : ∀ i ∈ A, 0 < k i) (hk0 : ∀ i, i ∉ A → k i = 0) (hI : I.Nonempty) (hIA : I ⊆ A)
  (hδ : 0 < δ) {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 ≤ a)

include hu_lb ha in
theorem uT_ge_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) : c ≤ uT u I t :=
  hu_lb _ (liftPoint_mem_box I a ha fun j => ⟨(ht j).1, (ht j).2.1⟩)

include hu_lb ha hc in
theorem uT_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) : 0 < uT u I t :=
  hc.trans_le (uT_ge_of_mem_baseSet A k u I a δ hu_lb ha ht)

include hkA hI hδ in
/-- The active tangential coordinates of a base point are positive. -/
theorem pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) (j : Tan I)
    (hj : j.1 ∈ A) : 0 < t j := by
  rcases (ht j).1.lt_or_eq with h | h
  · exact h
  · exfalso
    have h3 := (ht j).2.2 hj
    rw [← h, zero_pow (by have := hkA j.1 hj; omega), zero_pow hI.card_pos.ne', mul_zero] at h3
    exact absurd h3 (not_le.2 hδ)

include hkA hk0 hI hδ in
theorem tanUnit_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) :
    0 < tanUnit k I t := by
  refine Finset.prod_pos fun j _ => ?_
  by_cases hj : j.1 ∈ A
  · exact pow_pos (pos_of_mem_baseSet A k u I a δ hkA hI hδ ht j hj) _
  · rw [hk0 j.1 hj, mul_zero, pow_zero]
    exact one_pos

include hkA hk0 hI hδ hc hu_lb ha in
theorem U_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) : 0 < U k u I t :=
  mul_pos (uT_pos_of_mem_baseSet A k u I a δ hc hu_lb ha ht)
    (tanUnit_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ ht)

include hkA hk0 hI hδ hc hu_lb ha in
theorem q_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) :
    0 < q k u I δ t :=
  Real.rpow_pos_of_pos
    (div_pos hδ (U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht)) _

include hkA hk0 hI hδ hc hu_lb ha in
theorem q_pow_card_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) :
    q k u I δ t ^ I.card = δ / U k u I t :=
  Real.rpow_inv_natCast_pow
    (div_pos hδ (U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht)).le
    hI.card_pos.ne'

include hkA hk0 hI hδ hc hu_lb ha in
/-- On the base the water level is below every active tangential coordinate. -/
theorem q_le_pow_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) (j : Tan I)
    (hj : j.1 ∈ A) : q k u I δ t ≤ t j ^ (2 * k j.1) := by
  have hU := U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht
  have hq0 := (q_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht).le
  have h3 := (ht j).2.2 hj
  rw [← pow_le_pow_iff_left₀ hq0 (even_pow_nonneg _ _) hI.card_pos.ne',
    q_pow_card_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht, div_le_iff₀ hU, mul_comm]
  exact h3

include hkA hk0 hI hIA hδ hc hu_lb ha in
/-- ★ On the base the water level is at most `(δ/c)^{1/|A|}`. -/
theorem q_le_rpow {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) :
    q k u I δ t ≤ (δ / c) ^ ((A.card : ℝ)⁻¹) := by
  have hA : 0 < A.card := (hI.mono hIA).card_pos
  have hq0 := (q_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht).le
  have hδc : 0 ≤ δ / c := (div_pos hδ hc).le
  rw [Real.le_rpow_inv_iff_of_pos hq0 hδc (by exact_mod_cast hA), Real.rpow_natCast]
  have hcard : I.card ≤ A.card := Finset.card_le_card hIA
  have hsplit : q k u I δ t ^ A.card = q k u I δ t ^ I.card * q k u I δ t ^ (A \ I).card := by
    rw [← pow_add, add_comm, Finset.card_sdiff_add_card_eq_card hIA]
  have hT : q k u I δ t ^ (A \ I).card ≤ tanUnit k I t := by
    rw [tanUnit_eq_prod_sdiff' A k I hk0 t, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => hq0) fun j hj => ?_
    have hjI : j ∉ I := (Finset.mem_sdiff.1 hj).2
    have := q_le_pow_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht ⟨j, hjI⟩
      (Finset.mem_sdiff.1 hj).1
    rwa [show t ⟨j, hjI⟩ = liftPoint I t j by rw [liftPoint_apply, dif_neg hjI]] at this
  have hU := U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht
  have huT := uT_pos_of_mem_baseSet A k u I a δ hc hu_lb ha ht
  have hTpos := tanUnit_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ ht
  rw [hsplit, q_pow_card_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht]
  calc δ / U k u I t * q k u I δ t ^ (A \ I).card
      ≤ δ / U k u I t * tanUnit k I t :=
        mul_le_mul_of_nonneg_left hT (div_pos hδ hU).le
    _ = δ / uT u I t := by
        unfold U
        field_simp
    _ ≤ δ / c := div_le_div_of_nonneg_left hδ.le hc (uT_ge_of_mem_baseSet A k u I a δ hu_lb ha ht)

include hkA hk0 hI hδ hc hu_lb ha in
theorem ell_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) (i : Nrm I) :
    0 < ell k u I δ t i :=
  Real.rpow_pos_of_pos (q_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht) _

include hkA hk0 hI hIA hδ hc hu_lb ha in
/-- On the base every physical width is smaller than the box side. -/
theorem ell_lt_of_mem_baseSet (ha' : 0 < a)
    (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i))
    {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) (i : Nrm I) : ell k u I δ t i < a := by
  have hq0 := (q_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht).le
  have hki : (0 : ℝ) < ((2 * k i.1 : ℕ) : ℝ) := by
    have := hkA i.1 (hIA i.2)
    exact_mod_cast (by omega : 0 < 2 * k i.1)
  unfold ell
  rw [Real.rpow_inv_lt_iff_of_pos hq0 ha'.le hki, Real.rpow_natCast]
  exact (q_le_rpow A k u I a δ hkA hk0 hI hIA hδ hc hu_lb ha ht).trans_lt (hδa i.1 (hIA i.2))

include hkA hk0 hI hδ hc hu_lb ha in
theorem lamT_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) (i : Nrm I) :
    0 < lamT k u I δ t i :=
  div_pos (ell_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht i) (side_pos k I δ hδ)

include hδ in
theorem lamT_mul_side (t : Tan I → ℝ) (i : Nrm I) :
    lamT k u I δ t i * side k I δ = ell k u I δ t i :=
  div_mul_cancel₀ _ (side_pos k I δ hδ).ne'

include hkA hk0 hI hIA hδ hc hu_lb ha in
/-- ★ **The normalisation identity with the unit**:
`u(t) · (t_I(t) · ∏_{i∈I} λ_{I,i}(t)^{2k_i}) = 1` on the base — the shape `WData.hnorm`. -/
theorem unit_mul_prod_lamT {t : Tan I → ℝ} (ht : t ∈ baseSet A k u I a δ) :
    uT u I t * (tanUnit k I t * ∏ i : Nrm I, lamT k u I δ t i ^ (2 * k i.1)) = 1 := by
  have hU := U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht
  have hq0 := (q_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht).le
  have h1 : ∀ i : Nrm I, lamT k u I δ t i ^ (2 * k i.1) =
      q k u I δ t / side k I δ ^ (2 * k i.1) := by
    intro i
    rw [lamT, div_pow, ell, Real.rpow_inv_natCast_pow hq0 (by have := hkA i.1 (hIA i.2); omega)]
  simp_rw [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.prod_pow_eq_pow_sum, q_pow_card_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht]
  have hsum : ∑ i : Nrm I, 2 * k i.1 = 2 * ∑ i ∈ I, k i := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort I k
  have hside : side k I δ ^ (2 * ∑ i ∈ I, k i) = δ := by
    unfold side
    exact Real.rpow_inv_natCast_pow hδ.le (by
      obtain ⟨i, hi⟩ := hI
      have := hkA i (hIA hi)
      have : 0 < ∑ i ∈ I, k i := Finset.sum_pos (fun j hj => hkA j (hIA hj)) ⟨i, hi⟩
      omega)
  rw [hsum, hside]
  unfold U at hU ⊢
  field_simp
  exact div_self hU.ne'

end Base

/-! ### Regularity of the base data -/

section Regularity

variable (hu_cont : Continuous u)

include hu_cont in
theorem continuous_uT : Continuous (uT u I) := hu_cont.comp (continuous_liftPoint I)

include hu_cont in
theorem continuous_U : Continuous (U k u I) :=
  (continuous_uT u I hu_cont).mul (continuous_tanUnit k I)

include hu_cont in
theorem isClosed_baseSet : IsClosed (baseSet A k u I a δ) := by
  have : baseSet A k u I a δ = ⋂ j : Tan I, {t | 0 ≤ t j} ∩ {t | t j ≤ a} ∩
      {t | j.1 ∈ A → δ ≤ U k u I t * (t j ^ (2 * k j.1)) ^ I.card} := by
    ext t
    simp only [baseSet, mem_ofPred_eq, mem_iInter, mem_inter_iff, and_assoc]
  rw [this]
  refine isClosed_iInter fun j => ((isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_apply j) continuous_const)).inter ?_
  by_cases hj : j.1 ∈ A
  · have : {t : Tan I → ℝ | j.1 ∈ A → δ ≤ U k u I t * (t j ^ (2 * k j.1)) ^ I.card} =
        {t | δ ≤ U k u I t * (t j ^ (2 * k j.1)) ^ I.card} := by
      ext t; simp [hj]
    rw [this]
    exact isClosed_le continuous_const ((continuous_U k u I hu_cont).mul
      (((continuous_apply j).pow _).pow _))
  · have : {t : Tan I → ℝ | j.1 ∈ A → δ ≤ U k u I t * (t j ^ (2 * k j.1)) ^ I.card} = univ := by
      ext t; simp [hj]
    rw [this]
    exact isClosed_univ

include hu_cont in
theorem isCompact_baseSet : IsCompact (baseSet A k u I a δ) := by
  refine (isCompact_univ_pi fun _ : Tan I =>
    isCompact_Icc (a := (0 : ℝ)) (b := a)).of_isClosed_subset (isClosed_baseSet A k u I a δ hu_cont)
    fun t ht j _ => ⟨(ht j).1, (ht j).2.1⟩

include hu_cont in
theorem measurable_U : Measurable (U k u I) := (continuous_U k u I hu_cont).measurable

include hu_cont in
theorem measurable_q : Measurable (q k u I δ) :=
  (measurable_const.div (measurable_U k u I hu_cont)).pow_const _

include hu_cont in
theorem measurable_ell (i : Nrm I) : Measurable fun t => ell k u I δ t i :=
  (measurable_q k u I δ hu_cont).pow_const _

include hu_cont in
theorem measurable_lamT : Measurable (lamT k u I δ) :=
  measurable_pi_lambda _ fun i => (measurable_ell k u I δ hu_cont i).div_const _

variable (hkA : ∀ i ∈ A, 0 < k i) (hk0 : ∀ i, i ∉ A → k i = 0) (hI : I.Nonempty) (hδ : 0 < δ)
  {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 ≤ a)

include hu_cont hkA hk0 hI hδ hc hu_lb ha in
theorem continuousOn_q : ContinuousOn (q k u I δ) (baseSet A k u I a δ) := by
  refine ContinuousOn.rpow_const (continuousOn_const.div (continuous_U k u I hu_cont).continuousOn
    fun t ht => (U_pos_of_mem_baseSet A k u I a δ hkA hk0 hI hδ hc hu_lb ha ht).ne')
    fun _ _ => Or.inr ?_
  positivity

include hu_cont hkA hk0 hI hδ hc hu_lb ha in
theorem continuousOn_lamT : ContinuousOn (lamT k u I δ) (baseSet A k u I a δ) := by
  refine continuousOn_pi.2 fun i => ContinuousOn.div_const ?_ _
  refine ContinuousOn.rpow_const (continuousOn_q A k u I a δ hu_cont hkA hk0 hI hδ hc hu_lb ha)
    fun _ _ => Or.inr ?_
  positivity

end Regularity

/-! ### The core images -/

section Image

variable {K : Type*} (e : K → (Tan I → ℝ)) (hre : range e = baseSet A k u I a δ) (hδ : 0 < δ)
include hre hδ

theorem mem_image_iff (w : Fin d → ℝ) :
    w ∈ NormalisedBox.image I e (lamT k u I δ) (side k I δ) ↔
      tan I w ∈ baseSet A k u I a δ ∧
        ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k u I δ (tan I w) i := by
  unfold NormalisedBox.image fibre
  rw [hre]
  simp only [mem_ofPred_eq, split_apply, lamT_mul_side k u I δ hδ]
  exact Iff.rfl

/-- The core image lies in the box `[0,a]^d`. -/
theorem image_subset_box (hkA : ∀ i ∈ A, 0 < k i) (hk0 : ∀ i, i ∉ A → k i = 0) (hI : I.Nonempty)
    (hIA : I ⊆ A) {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 < a)
    (hδa : ∀ i ∈ A, (δ / c) ^ ((A.card : ℝ)⁻¹) < a ^ (2 * k i)) :
    NormalisedBox.image I e (lamT k u I δ) (side k I δ) ⊆ piBox d (Icc 0 a) := by
  intro w hw
  rw [mem_image_iff A k u I a δ e hre hδ] at hw
  rw [piBox, mem_univ_pi]
  intro j
  by_cases hj : j ∈ I
  · have h := hw.2 ⟨j, hj⟩
    exact ⟨h.1.le, (h.2.trans_lt (ell_lt_of_mem_baseSet A k u I a δ hkA hk0 hI hIA hδ hc hu_lb
      ha.le ha hδa hw.1 ⟨j, hj⟩)).le⟩
  · have h := hw.1 ⟨j, hj⟩
    exact ⟨h.1, h.2.1⟩

end Image

/-! ### Covering by water-filling -/

section Covering

variable (hkA : ∀ i ∈ A, 0 < k i) (hk0 : ∀ i, i ∉ A → k i = 0) (hA : A.Nonempty)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w)

include hkA hk0 hA hu_tan hc hu_lb in
/-- ★ **Covering**: a point of the box with positive ACTIVE coordinates and phase `< δ` lies in
the core image of the set `I ⊆ A` of active coordinates below the water level. -/
theorem covering {w : Fin d → ℝ} (hw : w ∈ piBox d (Icc 0 a)) (hpos : ∀ i ∈ A, 0 < w i)
    (hK : ChartModel.phase d A k u w < δ) :
    ∃ I : Finset (Fin d), I.Nonempty ∧ I ⊆ A ∧ tan I w ∈ baseSet A k u I a δ ∧
      ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k u I δ (tan I w) i := by
  classical
  have huw : 0 < u w := hc.trans_le (hu_lb w hw)
  have hδpos : 0 < δ :=
    lt_of_le_of_lt (mul_nonneg huw.le (ChartModel.monoPhase_nonneg d A k w)) hK
  set y : Fin d → ℝ := fun i => w i ^ (2 * k i) with hy
  have hypos : ∀ i ∈ A, 0 < y i := fun i hi => pow_pos (hpos i hi) _
  obtain ⟨i₀, hi₀A, hi₀⟩ := Finset.exists_min_image A y hA
  set H : ℝ → ℝ := fun r => ∏ i ∈ A, max (y i) r with hH
  have hHc : Continuous H := continuous_finsetProd _ fun _ _ => continuous_const.max continuous_id
  have hHm : H (y i₀) = ChartModel.monoPhase d A k w := by
    simp only [hH, ChartModel.monoPhase]
    exact Finset.prod_congr rfl fun i hi => max_eq_left (hi₀ i hi)
  set δ' := δ / u w with hδ'
  have hδ'pos : 0 < δ' := div_pos hδpos huw
  have hK' : H (y i₀) < δ' := by
    rw [hHm, hδ', lt_div_iff₀ huw, mul_comm]
    exact hK
  set Q := max (y i₀) (max 1 δ') with hQ
  have hmQ : y i₀ ≤ Q := le_max_left _ _
  have hQ1 : 1 ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQδ : δ' ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
  have hHQ : δ' ≤ H Q := by
    calc δ' ≤ Q := hQδ
      _ ≤ Q ^ A.card := le_self_pow₀ hQ1 hA.card_pos.ne'
      _ = ∏ _i ∈ A, Q := by rw [Finset.prod_const]
      _ ≤ H Q := Finset.prod_le_prod (fun _ _ => by linarith) fun i _ => le_max_right _ _
  obtain ⟨r, hr, hHr⟩ := intermediate_value_Icc hmQ hHc.continuousOn ⟨hK'.le, hHQ⟩
  have hrm : y i₀ < r := lt_of_le_of_ne hr.1 fun h => by
    rw [← h] at hHr
    exact hK'.ne hHr
  have hr0 : 0 < r := (hypos i₀ hi₀A).trans hrm
  set I := A.filter fun i => y i < r with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∈ A ∧ y i < r := fun i => by simp [hI]
  have hIA : I ⊆ A := Finset.filter_subset _ _
  have hIne : I.Nonempty := ⟨i₀, (hmemI i₀).2 ⟨hi₀A, hrm⟩⟩
  have hfilt : A.filter (fun i => ¬ y i < r) = A \ I := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, hmemI, not_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 h1⟩
  have hT : 0 < tanUnit k I (tan I w) := by
    rw [tanUnit_eq_prod_sdiff A k I hk0 w]
    exact Finset.prod_pos fun j hj => pow_pos (hpos j (Finset.mem_sdiff.1 hj).1) _
  have huT : uT u I (tan I w) = u w := uT_tan A u I hIA hu_tan w
  -- the water level identity `r^{|I|} t_I = δ'`
  have hHr' : H r = r ^ I.card * tanUnit k I (tan I w) := by
    simp only [hH]
    rw [← Finset.prod_filter_mul_prod_filter_not A (fun i => y i < r), ← hI, hfilt,
      tanUnit_eq_prod_sdiff A k I hk0 w]
    congr 1
    · rw [Finset.prod_congr rfl fun i hi => max_eq_right ((hmemI i).1 hi).2.le, Finset.prod_const]
    · refine Finset.prod_congr rfl fun j hj => max_eq_left (not_lt.1 fun h => ?_)
      exact (Finset.mem_sdiff.1 hj).2 ((hmemI j).2 ⟨(Finset.mem_sdiff.1 hj).1, h⟩)
  have hδT : r ^ I.card * tanUnit k I (tan I w) = δ' := hHr'.symm.trans hHr
  have hq : q k u I δ (tan I w) = r := by
    have h1 : δ / U k u I (tan I w) = r ^ I.card := by
      have h2 : δ = u w * (r ^ I.card * tanUnit k I (tan I w)) := by
        rw [hδT, hδ', mul_div_cancel₀ _ huw.ne']
      rw [U, huT]
      conv_lhs => rw [h2]
      field_simp
    unfold q
    rw [h1, Real.pow_rpow_inv_natCast hr0.le hIne.card_pos.ne']
  refine ⟨I, hIne, hIA, fun j => ⟨(hw j.1 (Set.mem_univ _)).1, (hw j.1 (Set.mem_univ _)).2,
    fun hjA => ?_⟩, fun i => ⟨hpos i.1 (hIA i.2), ?_⟩⟩
  · have hyj : r ≤ y j.1 := not_lt.1 fun h => j.2 ((hmemI j.1).2 ⟨hjA, h⟩)
    have hU : U k u I (tan I w) = u w * tanUnit k I (tan I w) := by rw [U, huT]
    calc δ = u w * (tanUnit k I (tan I w) * r ^ I.card) := by
          rw [mul_comm (tanUnit _ _ _), hδT, hδ', mul_div_cancel₀ _ huw.ne']
      _ ≤ u w * (tanUnit k I (tan I w) * (tan I w j ^ (2 * k j.1)) ^ I.card) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hyj _) hT.le) huw.le
      _ = U k u I (tan I w) * (tan I w j ^ (2 * k j.1)) ^ I.card := by rw [hU, mul_assoc]
  · have hyi : y i.1 < r := ((hmemI i.1).1 i.2).2
    rw [ell, hq]
    have hki : (0 : ℝ) < ((2 * k i.1 : ℕ) : ℝ) := by
      have := hkA i.1 (hIA i.2)
      exact_mod_cast (by omega : 0 < 2 * k i.1)
    exact ((Real.lt_rpow_inv_iff_of_pos (hpos i.1 (hIA i.2)).le hr0.le hki).2
      (by rw [Real.rpow_natCast]; exact hyi)).le

end Covering

/-! ### Disjointness off the thresholds -/

section Disjoint

variable (hkA : ∀ i ∈ A, 0 < k i) (hk0 : ∀ i, i ∉ A → k i = 0) (hδ : 0 < δ)
  (hu_tan : ∀ w w' : Fin d → ℝ, (∀ j, j ∉ A → w j = w' j) → u w = u w')
  {c : ℝ} (hc : 0 < c) (hu_lb : ∀ w ∈ piBox d (Icc 0 a), c ≤ u w) (ha : 0 ≤ a)

include hkA hk0 hδ hu_tan hc hu_lb ha in
/-- ★ **Disjointness off the thresholds**: a point in two core images `C_I ∩ C_J`, `I ≠ J`, has a
normal coordinate on its upper boundary. -/
theorem disjoint_or_threshold {I J : Finset (Fin d)} (hI : I.Nonempty) (hIA : I ⊆ A)
    (hJ : J.Nonempty) (hJA : J ⊆ A) (hIJ : I ≠ J) {w : Fin d → ℝ}
    (hwI : tan I w ∈ baseSet A k u I a δ ∧
      ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k u I δ (tan I w) i)
    (hwJ : tan J w ∈ baseSet A k u J a δ ∧
      ∀ i : Nrm J, 0 < w i.1 ∧ w i.1 ≤ ell k u J δ (tan J w) i) :
    (∃ i : Nrm I, w i.1 = ell k u I δ (tan I w) i) ∨
      (∃ i : Nrm J, w i.1 = ell k u J δ (tan J w) i) := by
  classical
  set y : Fin d → ℝ := fun i => w i ^ (2 * k i) with hy
  have hposA : ∀ i ∈ A, 0 < w i := fun i hi => by
    by_cases hiI : i ∈ I
    · exact (hwI.2 ⟨i, hiI⟩).1
    · exact pos_of_mem_baseSet A k u I a δ hkA hI hδ hwI.1 ⟨i, hiI⟩ hi
  have hypos : ∀ i, 0 < y i := fun i => by
    by_cases hi : i ∈ A
    · exact pow_pos (hposA i hi) _
    · simp only [hy, hk0 i hi, mul_zero, pow_zero]
      exact one_pos
  have hki : ∀ i ∈ A, (0 : ℝ) < ((2 * k i : ℕ) : ℝ) := fun i hi => by
    have := hkA i hi
    exact_mod_cast (by omega : 0 < 2 * k i)
  have huw : 0 < u w := by
    rw [← uT_tan A u I hIA hu_tan w]
    exact uT_pos_of_mem_baseSet A k u I a δ hc hu_lb ha hwI.1
  set δ' := δ / u w with hδ'
  -- the facts for a set `L`, symmetric in `I` and `J`
  have hA : ∀ (L : Finset (Fin d)), L.Nonempty → L ⊆ A →
      (tan L w ∈ baseSet A k u L a δ ∧
        ∀ i : Nrm L, 0 < w i.1 ∧ w i.1 ≤ ell k u L δ (tan L w) i) →
      (∀ i (hi : i ∈ L), y i ≤ q k u L δ (tan L w)) ∧
      (∀ j, j ∉ L → j ∈ A → q k u L δ (tan L w) ≤ y j) ∧
      q k u L δ (tan L w) ^ L.card * ∏ j ∈ Lᶜ, y j = δ' := by
    intro L hL hLA hwL
    refine ⟨fun i hi => ?_, fun j hj hjA =>
      q_le_pow_of_mem_baseSet A k u L a δ hkA hk0 hL hδ hc hu_lb ha hwL.1 ⟨j, hj⟩ hjA, ?_⟩
    · have h := (hwL.2 ⟨i, hi⟩).2
      rw [ell] at h
      have := (Real.le_rpow_inv_iff_of_pos (hposA i (hLA hi)).le
        (q_pos_of_mem_baseSet A k u L a δ hkA hk0 hL hδ hc hu_lb ha hwL.1).le
        (hki i (hLA hi))).1 h
      rwa [Real.rpow_natCast] at this
    · have hT := tanUnit_pos_of_mem_baseSet A k u L a δ hkA hk0 hL hδ hwL.1
      rw [q_pow_card_of_mem_baseSet A k u L a δ hkA hk0 hL hδ hc hu_lb ha hwL.1, U,
        uT_tan A u L hLA hu_tan w, ← tanUnit_eq_prod_compl, hδ']
      field_simp
  -- the water levels coincide
  have key : ∀ (L M : Finset (Fin d)), L.Nonempty → L ⊆ A → M.Nonempty → M ⊆ A →
      (tan L w ∈ baseSet A k u L a δ ∧
        ∀ i : Nrm L, 0 < w i.1 ∧ w i.1 ≤ ell k u L δ (tan L w) i) →
      (tan M w ∈ baseSet A k u M a δ ∧
        ∀ i : Nrm M, 0 < w i.1 ∧ w i.1 ≤ ell k u M δ (tan M w) i) →
      ¬ q k u L δ (tan L w) < q k u M δ (tan M w) := by
    intro L M hL hLA hM hMA hwL hwM hlt
    obtain ⟨hAL, hBL, hCL⟩ := hA L hL hLA hwL
    obtain ⟨hAM, hBM, hCM⟩ := hA M hM hMA hwM
    have hqL0 := (q_pos_of_mem_baseSet A k u L a δ hkA hk0 hL hδ hc hu_lb ha hwL.1).le
    have hqM0 := (q_pos_of_mem_baseSet A k u M a δ hkA hk0 hM hδ hc hu_lb ha hwM.1).le
    have hsub : L ⊆ M := fun i hi => by
      by_contra hiM
      exact absurd ((hBM i hiM (hLA hi)).trans (hAL i hi)) (not_le.2 hlt)
    have hcompl : Mᶜ ⊆ Lᶜ := Finset.compl_subset_compl.2 hsub
    have hsdiff : Lᶜ \ Mᶜ = M \ L := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_compl]
      tauto
    have hTL : ∏ j ∈ Lᶜ, y j = (∏ j ∈ M \ L, y j) * ∏ j ∈ Mᶜ, y j := by
      rw [← Finset.prod_sdiff hcompl, hsdiff]
    have hTM : 0 < ∏ j ∈ Mᶜ, y j := Finset.prod_pos fun j _ => hypos j
    have hbound : ∏ j ∈ M \ L, y j ≤ q k u M δ (tan M w) ^ (M \ L).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun j _ => (hypos j).le) fun j hj =>
        hAM j (Finset.mem_sdiff.1 hj).1
    have hcard : (M \ L).card + L.card = M.card := Finset.card_sdiff_add_card_eq_card hsub
    have h1 : q k u L δ (tan L w) ^ L.card * ∏ j ∈ Lᶜ, y j ≤
        q k u L δ (tan L w) ^ L.card * q k u M δ (tan M w) ^ (M \ L).card * ∏ j ∈ Mᶜ, y j := by
      rw [hTL, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbound (pow_nonneg hqL0 _)) hTM.le
    rw [hCL] at h1
    have h2 : q k u L δ (tan L w) ^ L.card * q k u M δ (tan M w) ^ (M \ L).card *
        ∏ j ∈ Mᶜ, y j < q k u M δ (tan M w) ^ M.card * ∏ j ∈ Mᶜ, y j := by
      rw [← hcard, pow_add, mul_comm (q k u M δ (tan M w) ^ (M \ L).card)]
      refine mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ?_
        (pow_pos (hqL0.trans_lt hlt) _)) hTM
      exact pow_lt_pow_left₀ hlt hqL0 hL.card_pos.ne'
    rw [hCM] at h2
    exact absurd (h1.trans_lt h2) (lt_irrefl δ')
  have hq : q k u I δ (tan I w) = q k u J δ (tan J w) := by
    rcases lt_trichotomy (q k u I δ (tan I w)) (q k u J δ (tan J w)) with h | h | h
    · exact absurd h (key I J hI hIA hJ hJA hwI hwJ)
    · exact h
    · exact absurd h (key J I hJ hJA hI hIA hwJ hwI)
  obtain ⟨hAI, hBI, -⟩ := hA I hI hIA hwI
  obtain ⟨hAJ, hBJ, -⟩ := hA J hJ hJA hwJ
  -- a coordinate separating `I` and `J`
  have hex : ∃ i, (i ∈ I ∧ i ∉ J) ∨ (i ∈ J ∧ i ∉ I) := by
    by_contra hcon
    push Not at hcon
    exact hIJ (Finset.ext fun i => ⟨fun hi => (hcon i).1 hi, fun hi => (hcon i).2 hi⟩)
  obtain ⟨i, hi | hi⟩ := hex
  · left
    refine ⟨⟨i, hi.1⟩, ?_⟩
    have hyi : y i = q k u I δ (tan I w) :=
      le_antisymm (hAI i hi.1) (hq ▸ hBJ i hi.2 (hIA hi.1))
    rw [ell, ← hyi]
    exact (Real.pow_rpow_inv_natCast (hposA i (hIA hi.1)).le
      (by have := hkA i (hIA hi.1); omega)).symm
  · right
    refine ⟨⟨i, hi.1⟩, ?_⟩
    have hyi : y i = q k u J δ (tan J w) :=
      le_antisymm (hAJ i hi.1) (hq ▸ hBI i hi.2 (hJA hi.1))
    rw [ell, ← hyi]
    exact (Real.pow_rpow_inv_natCast (hposA i (hJA hi.1)).le
      (by have := hkA i (hJA hi.1); omega)).symm

end Disjoint

end ChartCollar

end Grammar
