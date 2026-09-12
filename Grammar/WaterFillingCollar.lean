/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.NormalisedBoxCore

/-!
# The water-filling collar of the coordinate monomial phase (CCCXXII)

Consult #96 §3 (unit 4, geometry). On the box `W = [0,a]^d` with the phase `K(w) = ∏ w_i^{2k_i}`,
fix a level `δ > 0` with `δ^{1/d} < a^{2k_i}` for every `i`. For every nonempty `I ⊆ Fin d`
(`m = |I|`) define, on the tangential coordinates `t ∈ ℝ^{Iᶜ}`:

* the tangential unit `t_I(t) = ∏_{j∉I} t_j^{2k_j}` and the **water level**
  `q_I(t) = (δ / t_I(t))^{1/m}`;
* the **base** `B_I = {t : 0 ≤ t_j ≤ a, δ ≤ t_I(t)·(t_j^{2k_j})^m}` — compact, contained in the
  exact stratum (every `t_j > 0`), and on it `q_I(t) ≤ t_j^{2k_j}` and `q_I(t) ≤ δ^{1/d}`;
* the physical widths `ℓ_{I,i}(t) = q_I(t)^{1/(2k_i)} < a`, the common normalised side
  `b_I = δ^{1/(2Σ_{i∈I} k_i)}` and the widths `λ_{I,i}(t) = ℓ_{I,i}(t)/b_I`, with the
  NORMALISATION IDENTITY `t_I(t) ∏_i λ_{I,i}(t)^{2k_i} = 1` (all cores have `β = 1` and the
  fixed side `b_I`).

The core images `C_I = {w : tan_I w ∈ B_I, 0 < w_i ≤ ℓ_{I,i}(tan_I w) (i ∈ I)}` (the `image` of
CCCXX/CCCXXI with `range e = B_I`) lie in `W ∩ {K ≤ δ}` and

* ★ **cover**: every `w ∈ W` with all coordinates positive and `K(w) < δ` lies in some `C_I`
  (`covering`; water-filling: raise the small coordinates `y_i = w_i^{2k_i}` to a common level `q`
  until `∏ max(y_i, q) = δ`, by the intermediate value theorem);
* ★ **are disjoint off the thresholds**: `w ∈ C_I ∩ C_J`, `I ≠ J`, forces some normal coordinate
  onto its upper boundary `w_i = ℓ_{I,i}` or `w_i = ℓ_{J,i}` (`disjoint_or_threshold`; the two water
  levels coincide by a strict product comparison).

The measure-theoretic assembly (null thresholds, exact decomposition `μ = Σ_I μ|_{C_I} + tail`,
gap `K ≥ δ` on the tail) is the next unit. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace WaterFilling

open NormalisedBox

variable {d : ℕ} (k : Fin d → ℕ) (I : Finset (Fin d)) (a δ : ℝ)

/-- The tangential coordinates of a point. -/
def tan (w : Fin d → ℝ) : Tan I → ℝ := fun j => w j.1

/-- The water level `q_I(t) = (δ / t_I(t))^{1/|I|}`. -/
noncomputable def q (t : Tan I → ℝ) : ℝ := (δ / tanUnit k I t) ^ ((I.card : ℝ)⁻¹)

/-- The base `B_I`: `0 ≤ t_j ≤ a` and `δ ≤ t_I(t)·(t_j^{2k_j})^{|I|}` for every `j ∉ I`. -/
def baseSet : Set (Tan I → ℝ) :=
  {t | ∀ j, 0 ≤ t j ∧ t j ≤ a ∧ δ ≤ tanUnit k I t * (t j ^ (2 * k j.1)) ^ I.card}

/-- The physical normal width `ℓ_{I,i}(t) = q_I(t)^{1/(2k_i)}`. -/
noncomputable def ell (t : Tan I → ℝ) (i : Nrm I) : ℝ := q k I δ t ^ (((2 * k i.1 : ℕ) : ℝ)⁻¹)

/-- The common normalised side `b_I = δ^{1/(2Σ_{i∈I} k_i)}`. -/
noncomputable def side : ℝ := δ ^ (((2 * ∑ i ∈ I, k i : ℕ) : ℝ)⁻¹)

/-- The normalised widths `λ_{I,i}(t) = ℓ_{I,i}(t) / b_I`. -/
noncomputable def lamT (t : Tan I → ℝ) (i : Nrm I) : ℝ := ell k I δ t i / side k I δ

theorem tanUnit_tan (w : Fin d → ℝ) :
    tanUnit k I (tan I w) = ∏ j : Tan I, w j.1 ^ (2 * k j.1) := rfl

theorem tanUnit_eq_prod_compl (w : Fin d → ℝ) :
    tanUnit k I (tan I w) = ∏ j ∈ Iᶜ, w j ^ (2 * k j) := by
  rw [tanUnit_tan]
  exact (Finset.prod_subtype (p := fun x => ¬ x ∈ I) (F := inferInstance) Iᶜ
    (fun x => Finset.mem_compl) fun j => w j ^ (2 * k j)).symm

theorem even_pow_nonneg (x : ℝ) (m : ℕ) : 0 ≤ x ^ (2 * m) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem tanUnit_nonneg (t : Tan I → ℝ) : 0 ≤ tanUnit k I t :=
  Finset.prod_nonneg fun _ _ => even_pow_nonneg _ _

section Base

variable (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hδ : 0 < δ)
include hk hI hδ

theorem pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (j : Tan I) : 0 < t j := by
  rcases (ht j).1.lt_or_eq with h | h
  · exact h
  · exfalso
    have h3 := (ht j).2.2
    rw [← h, zero_pow (by have := hk j.1; omega), zero_pow hI.card_pos.ne', mul_zero] at h3
    exact absurd h3 (not_le.2 hδ)

theorem tanUnit_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    0 < tanUnit k I t :=
  Finset.prod_pos fun j _ => pow_pos (pos_of_mem_baseSet k I a δ hk hI hδ ht j) _

theorem q_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) : 0 < q k I δ t :=
  Real.rpow_pos_of_pos (div_pos hδ (tanUnit_pos_of_mem_baseSet k I a δ hk hI hδ ht)) _

omit hk hI hδ in
theorem q_nonneg (t : Tan I → ℝ) (hδ : 0 ≤ δ) : 0 ≤ q k I δ t :=
  Real.rpow_nonneg (div_nonneg hδ (tanUnit_nonneg k I t)) _

omit hk hδ in
theorem q_pow_card (t : Tan I → ℝ) (hδ : 0 ≤ δ) : q k I δ t ^ I.card = δ / tanUnit k I t :=
  Real.rpow_inv_natCast_pow (div_nonneg hδ (tanUnit_nonneg k I t)) hI.card_pos.ne'

theorem q_le_pow_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (j : Tan I) :
    q k I δ t ≤ t j ^ (2 * k j.1) := by
  have hT := tanUnit_pos_of_mem_baseSet k I a δ hk hI hδ ht
  have h3 := (ht j).2.2
  rw [← pow_le_pow_iff_left₀ (q_nonneg k I δ t hδ.le) (even_pow_nonneg _ _) hI.card_pos.ne',
    q_pow_card k I δ hI t hδ.le, div_le_iff₀ hT, mul_comm]
  exact h3

/-- On the base the water level is at most `δ^{1/d}`. -/
theorem q_le_rpow (hd : 0 < d) {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    q k I δ t ≤ δ ^ ((d : ℝ)⁻¹) := by
  have hq0 := q_nonneg k I δ t hδ.le
  rw [Real.le_rpow_inv_iff_of_pos hq0 hδ.le (by exact_mod_cast hd), Real.rpow_natCast]
  have hcard : I.card ≤ d := by
    have := Finset.card_le_univ I
    rwa [Fintype.card_fin] at this
  have hsplit : q k I δ t ^ d = q k I δ t ^ I.card * q k I δ t ^ (d - I.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hcard]
  have hT : q k I δ t ^ (d - I.card) ≤ tanUnit k I t := by
    have h1 : q k I δ t ^ (d - I.card) = ∏ _j : Tan I, q k I δ t := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_fin,
        Fintype.card_coe]
    rw [h1]
    exact Finset.prod_le_prod (fun _ _ => hq0) fun j _ =>
      q_le_pow_of_mem_baseSet k I a δ hk hI hδ ht j
  rw [hsplit, q_pow_card k I δ hI t hδ.le,
    div_mul_eq_mul_div, div_le_iff₀ (tanUnit_pos_of_mem_baseSet k I a δ hk hI hδ ht)]
  exact mul_le_mul_of_nonneg_left hT hδ.le

theorem ell_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (i : Nrm I) :
    0 < ell k I δ t i :=
  Real.rpow_pos_of_pos (q_pos_of_mem_baseSet k I a δ hk hI hδ ht) _

/-- On the base every physical width is smaller than the box side. -/
theorem ell_lt_of_mem_baseSet (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
    {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (i : Nrm I) : ell k I δ t i < a := by
  have hq0 := q_nonneg k I δ t hδ.le
  have hki : (0 : ℝ) < ((2 * k i.1 : ℕ) : ℝ) := by
    have := hk i.1
    exact_mod_cast (by omega : 0 < 2 * k i.1)
  unfold ell
  rw [Real.rpow_inv_lt_iff_of_pos hq0 ha.le hki, Real.rpow_natCast]
  exact (q_le_rpow k I a δ hk hI hδ hd ht).trans_lt (hδa i.1)

omit hk hI in
theorem side_pos : 0 < side k I δ := Real.rpow_pos_of_pos hδ _

theorem lamT_pos_of_mem_baseSet {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) (i : Nrm I) :
    0 < lamT k I δ t i :=
  div_pos (ell_pos_of_mem_baseSet k I a δ hk hI hδ ht i) (side_pos k I δ hδ)

omit hk hI in
theorem lamT_mul_side (t : Tan I → ℝ) (i : Nrm I) :
    lamT k I δ t i * side k I δ = ell k I δ t i :=
  div_mul_cancel₀ _ (side_pos k I δ hδ).ne'

/-- ★ **The normalisation identity**: `t_I(t) ∏_{i∈I} λ_{I,i}(t)^{2k_i} = 1` on the base. -/
theorem tanUnit_mul_prod_lamT {t : Tan I → ℝ} (ht : t ∈ baseSet k I a δ) :
    tanUnit k I t * ∏ i : Nrm I, lamT k I δ t i ^ (2 * k i.1) = 1 := by
  have hT := tanUnit_pos_of_mem_baseSet k I a δ hk hI hδ ht
  have hq0 := q_nonneg k I δ t hδ.le
  have h1 : ∀ i : Nrm I, lamT k I δ t i ^ (2 * k i.1) = q k I δ t / side k I δ ^ (2 * k i.1) := by
    intro i
    rw [lamT, div_pow, ell, Real.rpow_inv_natCast_pow hq0 (by have := hk i.1; omega)]
  simp_rw [h1]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.prod_pow_eq_pow_sum, q_pow_card k I δ hI t hδ.le]
  have hsum : ∑ i : Nrm I, 2 * k i.1 = 2 * ∑ i ∈ I, k i := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort I k
  have hside : side k I δ ^ (2 * ∑ i ∈ I, k i) = δ := by
    unfold side
    exact Real.rpow_inv_natCast_pow hδ.le (by
      have := hI
      obtain ⟨i, hi⟩ := hI
      have := hk i
      have : 0 < ∑ i ∈ I, k i := Finset.sum_pos (fun j _ => hk j) ⟨i, hi⟩
      omega)
  rw [hsum, hside]
  field_simp

end Base

/-! ### Compactness and regularity of the base data -/

theorem continuous_tanUnit : Continuous (tanUnit k I) :=
  continuous_finsetProd _ fun j _ => (continuous_apply j).pow _

theorem isClosed_baseSet : IsClosed (baseSet k I a δ) := by
  have : baseSet k I a δ = ⋂ j : Tan I, {t | 0 ≤ t j} ∩ {t | t j ≤ a} ∩
      {t | δ ≤ tanUnit k I t * (t j ^ (2 * k j.1)) ^ I.card} := by
    ext t
    simp only [baseSet, mem_ofPred_eq, mem_iInter, mem_inter_iff, and_assoc]
  rw [this]
  refine isClosed_iInter fun j => ((isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_apply j) continuous_const)).inter
    (isClosed_le continuous_const ((continuous_tanUnit k I).mul
      (((continuous_apply j).pow _).pow _)))

theorem isCompact_baseSet : IsCompact (baseSet k I a δ) := by
  refine (isCompact_univ_pi fun _ : Tan I =>
    isCompact_Icc (a := (0 : ℝ)) (b := a)).of_isClosed_subset (isClosed_baseSet k I a δ)
    fun t ht j _ => ⟨(ht j).1, (ht j).2.1⟩

theorem measurable_tanUnit : Measurable (tanUnit k I) := (continuous_tanUnit k I).measurable

theorem measurable_q : Measurable (q k I δ) :=
  (measurable_const.div (measurable_tanUnit k I)).pow_const _

theorem measurable_ell (i : Nrm I) : Measurable fun t => ell k I δ t i :=
  (measurable_q k I δ).pow_const _

theorem measurable_lamT : Measurable (lamT k I δ) :=
  measurable_pi_lambda _ fun i => (measurable_ell k I δ i).div_const _

theorem continuousOn_q (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hδ : 0 < δ) :
    ContinuousOn (q k I δ) (baseSet k I a δ) := by
  refine ContinuousOn.rpow_const (continuousOn_const.div (continuous_tanUnit k I).continuousOn
    fun t ht => (tanUnit_pos_of_mem_baseSet k I a δ hk hI hδ ht).ne') fun _ _ => Or.inr ?_
  positivity

theorem continuousOn_lamT (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hδ : 0 < δ) :
    ContinuousOn (lamT k I δ) (baseSet k I a δ) := by
  refine continuousOn_pi.2 fun i => ContinuousOn.div_const ?_ _
  refine ContinuousOn.rpow_const (continuousOn_q k I a δ hk hI hδ) fun _ _ => Or.inr ?_
  positivity

/-! ### The core images -/

section Image

variable {K : Type*} (e : K → (Tan I → ℝ)) (hre : range e = baseSet k I a δ) (hδ : 0 < δ)
include hre hδ

/-- Membership in the core image: tangential part in the base, normal coordinates in
`(0, ℓ_{I,i}]`. -/
theorem mem_image_iff (w : Fin d → ℝ) :
    w ∈ NormalisedBox.image I e (lamT k I δ) (side k I δ) ↔
      tan I w ∈ baseSet k I a δ ∧ ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k I δ (tan I w) i := by
  unfold NormalisedBox.image fibre
  rw [hre]
  simp only [mem_ofPred_eq, split_apply, lamT_mul_side k I δ hδ]
  exact Iff.rfl

/-- The core image lies in the box `[0,a]^d`. -/
theorem image_subset_box (hk : ∀ i, 0 < k i) (hI : I.Nonempty) (hd : 0 < d) (ha : 0 < a)
    (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) :
    NormalisedBox.image I e (lamT k I δ) (side k I δ) ⊆ piBox d (Icc 0 a) := by
  intro w hw
  rw [mem_image_iff k I a δ e hre hδ] at hw
  rw [piBox, mem_univ_pi]
  intro j
  by_cases hj : j ∈ I
  · have h := hw.2 ⟨j, hj⟩
    exact ⟨h.1.le,
      (h.2.trans_lt (ell_lt_of_mem_baseSet k I a δ hk hI hδ hd ha hδa hw.1 ⟨j, hj⟩)).le⟩
  · have h := hw.1 ⟨j, hj⟩
    exact ⟨h.1, h.2.1⟩

end Image

/-! ### Covering by water-filling -/

/-- ★ **Covering**: a point of the box with positive coordinates and `K(w) < δ` lies in the core
image of the set `I` of coordinates below the water level. -/
theorem covering (hk : ∀ i, 0 < k i) (hd : 0 < d) {w : Fin d → ℝ}
    (hw : w ∈ piBox d (Icc 0 a)) (hpos : ∀ i, 0 < w i) (hK : CoordModel.phase d k w < δ) :
    ∃ I : Finset (Fin d), I.Nonempty ∧ tan I w ∈ baseSet k I a δ ∧
      ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k I δ (tan I w) i := by
  set y : Fin d → ℝ := fun i => w i ^ (2 * k i) with hy
  have hypos : ∀ i, 0 < y i := fun i => pow_pos (hpos i) _
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ y Finset.univ_nonempty
  set H : ℝ → ℝ := fun r => ∏ i, max (y i) r with hH
  have hHc : Continuous H := continuous_finsetProd _ fun _ _ => continuous_const.max continuous_id
  have hHm : H (y i₀) = CoordModel.phase d k w := by
    simp only [hH, CoordModel.phase]
    exact Finset.prod_congr rfl fun i _ => max_eq_left (hi₀ i (Finset.mem_univ i))
  set Q := max (y i₀) (max 1 δ) with hQ
  have hmQ : y i₀ ≤ Q := le_max_left _ _
  have hQ1 : 1 ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQδ : δ ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
  have hHQ : δ ≤ H Q := by
    calc δ ≤ Q := hQδ
      _ ≤ Q ^ d := le_self_pow₀ hQ1 hd.ne'
      _ = ∏ _i : Fin d, Q := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ H Q := Finset.prod_le_prod (fun _ _ => by linarith) fun i _ => le_max_right _ _
  obtain ⟨r, hr, hHr⟩ := intermediate_value_Icc hmQ hHc.continuousOn ⟨hHm ▸ hK.le, hHQ⟩
  have hrm : y i₀ < r := lt_of_le_of_ne hr.1 fun h => by
    rw [← h, hHm] at hHr
    exact hK.ne hHr
  have hr0 : 0 < r := (hypos i₀).trans hrm
  set I := Finset.univ.filter fun i => y i < r with hI
  have hmemI : ∀ i, i ∈ I ↔ y i < r := fun i => by simp [hI]
  have hIne : I.Nonempty := ⟨i₀, (hmemI i₀).2 hrm⟩
  have hT : 0 < tanUnit k I (tan I w) := Finset.prod_pos fun j _ => pow_pos (hpos j.1) _
  -- the water level identity `r^{|I|} t_I = δ`
  have hHr' : H r = r ^ I.card * tanUnit k I (tan I w) := by
    simp only [hH]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => y i < r), ← hI,
      tanUnit_tan]
    congr 1
    · rw [Finset.prod_congr rfl fun i hi => max_eq_right ((hmemI i).1 hi).le, Finset.prod_const]
    · rw [Finset.prod_subtype (p := fun x => ¬ x ∈ I) (F := inferInstance)
        (Finset.univ.filter fun i => ¬ y i < r) (fun x => by simp [hmemI]) fun i => max (y i) r]
      exact Finset.prod_congr rfl fun j _ => max_eq_left (not_lt.1 ((hmemI j.1).not.1 j.2))
  have hδT : r ^ I.card * tanUnit k I (tan I w) = δ := hHr'.symm.trans hHr
  have hq : q k I δ (tan I w) = r := by
    unfold q
    rw [← hδT, mul_div_cancel_right₀ _ hT.ne', Real.pow_rpow_inv_natCast hr0.le hIne.card_pos.ne']
  refine ⟨I, hIne, fun j => ⟨(hw j.1 (Set.mem_univ _)).1, (hw j.1 (Set.mem_univ _)).2, ?_⟩,
    fun i => ⟨hpos i.1, ?_⟩⟩
  · have hyj : r ≤ y j.1 := not_lt.1 ((hmemI j.1).not.1 j.2)
    calc δ = tanUnit k I (tan I w) * r ^ I.card := by rw [← hδT, mul_comm]
      _ ≤ tanUnit k I (tan I w) * (tan I w j ^ (2 * k j.1)) ^ I.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hyj _) hT.le
  · have hyi : y i.1 < r := (hmemI i.1).1 i.2
    rw [ell, hq]
    have hki : (0 : ℝ) < ((2 * k i.1 : ℕ) : ℝ) := by
      have := hk i.1
      exact_mod_cast (by omega : 0 < 2 * k i.1)
    exact ((Real.lt_rpow_inv_iff_of_pos (hpos i.1).le hr0.le hki).2
      (by rw [Real.rpow_natCast]; exact hyi)).le

/-! ### Disjointness off the thresholds -/

/-- ★ **Disjointness off the thresholds**: a point in two core images `C_I ∩ C_J`, `I ≠ J`, has a
normal coordinate on its upper boundary `w_i = ℓ_{I,i}` or `w_i = ℓ_{J,i}`. -/
theorem disjoint_or_threshold (hk : ∀ i, 0 < k i) (hδ : 0 < δ) {I J : Finset (Fin d)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hIJ : I ≠ J) {w : Fin d → ℝ}
    (hwI : tan I w ∈ baseSet k I a δ ∧ ∀ i : Nrm I, 0 < w i.1 ∧ w i.1 ≤ ell k I δ (tan I w) i)
    (hwJ : tan J w ∈ baseSet k J a δ ∧ ∀ i : Nrm J, 0 < w i.1 ∧ w i.1 ≤ ell k J δ (tan J w) i) :
    (∃ i : Nrm I, w i.1 = ell k I δ (tan I w) i) ∨
      (∃ i : Nrm J, w i.1 = ell k J δ (tan J w) i) := by
  classical
  set y : Fin d → ℝ := fun i => w i ^ (2 * k i) with hy
  have hpos : ∀ i, 0 < w i := fun i => by
    by_cases hi : i ∈ I
    · exact (hwI.2 ⟨i, hi⟩).1
    · exact pos_of_mem_baseSet k I a δ hk hI hδ hwI.1 ⟨i, hi⟩
  have hypos : ∀ i, 0 < y i := fun i => pow_pos (hpos i) _
  have hki : ∀ i, (0 : ℝ) < ((2 * k i : ℕ) : ℝ) := fun i => by
    have := hk i
    exact_mod_cast (by omega : 0 < 2 * k i)
  -- the two sets of facts, symmetric in `I` and `J`
  have hA : ∀ (L : Finset (Fin d)), L.Nonempty →
      (tan L w ∈ baseSet k L a δ ∧ ∀ i : Nrm L, 0 < w i.1 ∧ w i.1 ≤ ell k L δ (tan L w) i) →
      (∀ i (hi : i ∈ L), y i ≤ q k L δ (tan L w)) ∧
      (∀ j, j ∉ L → q k L δ (tan L w) ≤ y j) ∧
      q k L δ (tan L w) ^ L.card * ∏ j ∈ Lᶜ, y j = δ := by
    intro L hL hwL
    refine ⟨fun i hi => ?_, fun j hj => q_le_pow_of_mem_baseSet k L a δ hk hL hδ hwL.1 ⟨j, hj⟩, ?_⟩
    · have h := (hwL.2 ⟨i, hi⟩).2
      rw [ell] at h
      have := (Real.le_rpow_inv_iff_of_pos (hpos i).le
        (q_nonneg k L δ _ hδ.le) (hki i)).1 h
      rwa [Real.rpow_natCast] at this
    · rw [q_pow_card k L δ hL _ hδ.le, ← tanUnit_eq_prod_compl,
        div_mul_cancel₀ _ (tanUnit_pos_of_mem_baseSet k L a δ hk hL hδ hwL.1).ne']
  -- the water levels coincide
  have key : ∀ (L M : Finset (Fin d)), L.Nonempty → M.Nonempty →
      (tan L w ∈ baseSet k L a δ ∧ ∀ i : Nrm L, 0 < w i.1 ∧ w i.1 ≤ ell k L δ (tan L w) i) →
      (tan M w ∈ baseSet k M a δ ∧ ∀ i : Nrm M, 0 < w i.1 ∧ w i.1 ≤ ell k M δ (tan M w) i) →
      ¬ q k L δ (tan L w) < q k M δ (tan M w) := by
    intro L M hL hM hwL hwM hlt
    obtain ⟨hAL, hBL, hCL⟩ := hA L hL hwL
    obtain ⟨hAM, hBM, hCM⟩ := hA M hM hwM
    have hqL0 := q_nonneg k L δ (tan L w) hδ.le
    have hqM0 := q_nonneg k M δ (tan M w) hδ.le
    have hsub : L ⊆ M := fun i hi => by
      by_contra hiM
      exact absurd ((hBM i hiM).trans (hAL i hi)) (not_le.2 hlt)
    have hcompl : Mᶜ ⊆ Lᶜ := Finset.compl_subset_compl.2 hsub
    have hsdiff : Lᶜ \ Mᶜ = M \ L := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_compl]
      tauto
    have hTL : ∏ j ∈ Lᶜ, y j = (∏ j ∈ M \ L, y j) * ∏ j ∈ Mᶜ, y j := by
      rw [← Finset.prod_sdiff hcompl, hsdiff]
    have hTM : 0 < ∏ j ∈ Mᶜ, y j := Finset.prod_pos fun j _ => hypos j
    have hbound : ∏ j ∈ M \ L, y j ≤ q k M δ (tan M w) ^ (M \ L).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun j _ => (hypos j).le) fun j hj =>
        hAM j (Finset.mem_sdiff.1 hj).1
    have hcard : (M \ L).card + L.card = M.card := Finset.card_sdiff_add_card_eq_card hsub
    have h1 : q k L δ (tan L w) ^ L.card * ∏ j ∈ Lᶜ, y j ≤
        q k L δ (tan L w) ^ L.card * q k M δ (tan M w) ^ (M \ L).card * ∏ j ∈ Mᶜ, y j := by
      rw [hTL, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbound (pow_nonneg hqL0 _)) hTM.le
    rw [hCL] at h1
    have h2 : q k L δ (tan L w) ^ L.card * q k M δ (tan M w) ^ (M \ L).card * ∏ j ∈ Mᶜ, y j <
        q k M δ (tan M w) ^ M.card * ∏ j ∈ Mᶜ, y j := by
      rw [← hcard, pow_add, mul_comm (q k M δ (tan M w) ^ (M \ L).card)]
      refine mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ?_
        (pow_pos (hqL0.trans_lt hlt) _)) hTM
      exact pow_lt_pow_left₀ hlt hqL0 hL.card_pos.ne'
    rw [hCM] at h2
    exact absurd (h1.trans_lt h2) (lt_irrefl δ)
  have hq : q k I δ (tan I w) = q k J δ (tan J w) := by
    rcases lt_trichotomy (q k I δ (tan I w)) (q k J δ (tan J w)) with h | h | h
    · exact absurd h (key I J hI hJ hwI hwJ)
    · exact h
    · exact absurd h (key J I hJ hI hwJ hwI)
  obtain ⟨hAI, hBI, -⟩ := hA I hI hwI
  obtain ⟨hAJ, hBJ, -⟩ := hA J hJ hwJ
  -- a coordinate separating `I` and `J`
  have hex : ∃ i, (i ∈ I ∧ i ∉ J) ∨ (i ∈ J ∧ i ∉ I) := by
    by_contra hcon
    push Not at hcon
    exact hIJ (Finset.ext fun i => ⟨fun hi => (hcon i).1 hi, fun hi => (hcon i).2 hi⟩)
  obtain ⟨i, hi | hi⟩ := hex
  · left
    refine ⟨⟨i, hi.1⟩, ?_⟩
    have hyi : y i = q k I δ (tan I w) :=
      le_antisymm (hAI i hi.1) (hq ▸ hBJ i hi.2)
    rw [ell, ← hyi]
    exact (Real.pow_rpow_inv_natCast (hpos i).le (by have := hk i; omega)).symm
  · right
    refine ⟨⟨i, hi.1⟩, ?_⟩
    have hyi : y i = q k J δ (tan J w) :=
      le_antisymm (hAJ i hi.1) (hq ▸ hBI i hi.2)
    rw [ell, ← hyi]
    exact (Real.pow_rpow_inv_natCast (hpos i).le (by have := hk i; omega)).symm

end WaterFilling

end Grammar
