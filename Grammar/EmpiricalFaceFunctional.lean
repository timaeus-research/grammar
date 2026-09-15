/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalBoxLeading
import Grammar.SmoothFaceSplit
import Grammar.SmoothResolvedResidue
import Grammar.LeadingCoeffGaussianMoment
import Grammar.PhasePosterior
import Grammar.FluctuationLipschitz

/-!
# The empirical face functional and its identification with the spatial face functional

`faceFunctional h k l b ξ η = 1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J, w) S_l(ξ(0_J, w)) ·
∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−l} dw` is the limit of the empirical box integral on
`(0,b]^d` in the form of the empirical stratum measure (`J` the coordinates of ratio `l`,
`m = |J|`).
This module shows that the dilated spatial face functional of Headline XIX equals it
(`spatialFace_dilated_eq_faceFunctional`), by scaling the unit box to `(0,b]^d`, splitting the
coordinates into `J` and `Jᶜ`, and converting `phaseMoment` to the fluctuation function. Zero
`sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open SmoothEngine in
section

variable {d : ℕ}

/-- The resonant coordinates `J_l = {i | (h_i+1)/(2k_i) = l}`. -/
noncomputable def resSet (h k : Fin d → ℕ) (l : ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => ratioExp h k i = l

theorem mem_resSet {h k : Fin d → ℕ} {l : ℝ} {i : Fin d} :
    i ∈ resSet h k l ↔ ratioExp h k i = l := by
  simp [resSet]

theorem card_resSet (h k : Fin d → ℕ) (l : ℝ) :
    (resSet h k l).card = multCount (ratioExp h k) l := by
  rw [multCount_eq_card]
  rfl

theorem faceProj_glue (h k : Fin d → ℕ) (l : ℝ) (u : {i // inJ (resSet h k l) i} → ℝ)
    (w : {i // ¬ inJ (resSet h k l) i} → ℝ) :
    faceProj h k l (glue (resSet h k l) u w) = glue (resSet h k l) 0 w := by
  funext i
  unfold faceProj
  by_cases hi : ratioExp h k i = l
  · rw [if_pos hi, glue_apply_of_mem _ _ _ (mem_resSet.2 hi), Pi.zero_apply]
  · rw [if_neg hi, glue_apply_of_not_mem _ _ _ (fun h' => hi (mem_resSet.1 h')),
      glue_apply_of_not_mem _ _ _ (fun h' => hi (mem_resSet.1 h'))]

theorem faceProj_smul (h k : Fin d → ℕ) (l b : ℝ) (u : Fin d → ℝ) :
    faceProj h k l (b • u) = b • faceProj h k l u := by
  funext i
  unfold faceProj
  by_cases hi : ratioExp h k i = l
  · simp [hi]
  · simp [hi]

/-- The residual weight of a glued point depends only on the complementary coordinates, where it is
the residue weight `∏_{i∉J} w_i^{h_i}(∏_{i∉J} w_i^{2k_i})^{−l}`. -/
theorem residualWeight_glue (h k : Fin d → ℕ) (l : ℝ) (u : {i // inJ (resSet h k l) i} → ℝ)
    {b : ℝ} {w : {i // ¬ inJ (resSet h k l) i} → ℝ}
    (hw : w ∈ SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b) :
    residualWeight h k l (glue (resSet h k l) u w) =
      residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w := by
  unfold residualWeight residueWeight mono
  rw [← Fintype.prod_subtype_mul_prod_subtype (inJ (resSet h k l))]
  have hJ : ∏ i : {i // inJ (resSet h k l) i},
      (if ratioExp h k i.1 = l then 1
        else glue (resSet h k l) u w i.1 ^ ((h i.1 : ℝ) - 2 * k i.1 * l)) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [if_pos (mem_resSet.1 i.2)]
  rw [hJ, one_mul, ← Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (pos_of_mem_box hw i).le _,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : ¬ ratioExp h k i.1 = l := fun h' => i.2 (mem_resSet.2 h')
  have hwi : 0 < w i := pos_of_mem_box hw i
  rw [if_neg hi, glue_apply_subtype', Real.rpow_sub hwi, ← Real.rpow_natCast,
    ← Real.rpow_natCast (w i) (2 * k i.1), ← Real.rpow_mul hwi.le, div_eq_mul_inv,
    ← Real.rpow_neg hwi.le]
  push_cast
  ring_nf

/-- Scaling of the residue weight: for positive coordinates and `b > 0`,
`residueWeight (b • w) = b^{Σ h_i − 2l Σ k_i} · residueWeight w`. -/
theorem residueWeight_smul {ι : Type*} [Fintype ι] (h k : ι → ℕ) (l : ℝ) {b : ℝ} (hb : 0 < b)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    residueWeight h k l (b • w) =
      b ^ ((∑ i, (h i : ℝ)) - 2 * l * ∑ i, (k i : ℝ)) * residueWeight h k l w := by
  unfold residueWeight mono
  have h1 : ∏ i, (b • w) i ^ h i = b ^ (∑ i, h i) * ∏ i, w i ^ h i := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  have h2 : ∏ i, (b • w) i ^ (2 * k i) = b ^ (2 * ∑ i, k i) * ∏ i, w i ^ (2 * k i) := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  have hm : 0 ≤ ∏ i, w i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hw i).le _
  rw [h1, h2, Real.mul_rpow (pow_nonneg hb.le _) hm, ← Real.rpow_natCast b (∑ i, h i),
    ← Real.rpow_natCast b (2 * ∑ i, k i), ← Real.rpow_mul hb.le, Real.rpow_sub hb,
    div_eq_mul_inv, ← Real.rpow_neg hb.le]
  push_cast
  ring_nf

/-- Dilation of a box integral to the unit box, for an arbitrary finite index type. -/
theorem integral_unitBox_comp_smul {ι : Type*} [Fintype ι] {b : ℝ} (hb : 0 < b)
    (G : (ι → ℝ) → ℝ) :
    ∫ u in (Set.pi univ fun _ : ι => Ioc (0 : ℝ) 1), G (b • u) =
      (b ^ Fintype.card ι)⁻¹ * ∫ w in (Set.pi univ fun _ : ι => Ioc (0 : ℝ) b), G w := by
  have hmem : ∀ u : ι → ℝ, b • u ∈ (Set.pi univ fun _ : ι => Ioc (0 : ℝ) b) ↔
      u ∈ (Set.pi univ fun _ : ι => Ioc (0 : ℝ) 1) := by
    intro u
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply, smul_eq_mul, mem_Ioc]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hb.le, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hb h1, by nlinarith⟩
  have hind : ∀ u, (Set.pi univ fun _ : ι => Ioc (0 : ℝ) b).indicator G (b • u) =
      (Set.pi univ fun _ : ι => Ioc (0 : ℝ) 1).indicator (fun u => G (b • u)) u := by
    intro u
    by_cases hu : u ∈ (Set.pi univ fun _ : ι => Ioc (0 : ℝ) 1)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hmem u).2 hu)]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h' => hu ((hmem u).1 h'))]
  have hscale := Measure.integral_comp_smul (volume : Measure (ι → ℝ))
    ((Set.pi univ fun _ : ι => Ioc (0 : ℝ) b).indicator G) b
  rw [Module.finrank_fintype_fun_eq_card, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.2 (pow_nonneg hb.le _)),
    integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)] at hscale
  simp_rw [hind] at hscale
  rw [integral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)] at hscale
  exact hscale

/-- The empirical face functional on the box `(0,b]^d` at temperature one:
`1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J,w) S_l(ξ(0_J,w)) residueWeight(w) dw`. -/
noncomputable def faceFunctional (h k : Fin d → ℕ) (l b : ℝ) (ξ η : (Fin d → ℝ) → ℝ) : ℝ :=
  (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i ∈ resSet h k l, (2 * (k i : ℝ)))) *
    ∫ w in SmoothEngine.box {i // ¬ inJ (resSet h k l) i} b,
      η (glue (resSet h k l) 0 w) * fluctuation 1 l (ξ (glue (resSet h k l) 0 w)) *
        residueWeight (fun i : {i // ¬ inJ (resSet h k l) i} => h i) (fun i => k i) l w

theorem glue_zero_smul (J : Finset (Fin d)) (b : ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    glue J 0 (b • w) = b • glue J 0 w := by
  funext i
  by_cases hi : i ∈ J
  · simp only [Pi.smul_apply, glue_apply_of_mem _ _ _ hi, Pi.zero_apply, smul_zero]
  · simp only [Pi.smul_apply, glue_apply_of_not_mem _ _ _ hi]

/-- On the resonant coordinates `2 k_i l = h_i + 1`. -/
theorem two_mul_k_mul_l_of_mem_resSet {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {l : ℝ} {i : Fin d}
    (hi : i ∈ resSet h k l) : 2 * (k i : ℝ) * l = h i + 1 := by
  have := mem_resSet.1 hi
  unfold ratioExp at this
  have hk' : (0 : ℝ) < 2 * k i := by
    have := Nat.cast_pos (α := ℝ) |>.2 (hk i)
    positivity
  rw [div_eq_iff hk'.ne'] at this
  linarith

/-- The unit box is the box of side one. -/
theorem unitBox_eq_box (d : ℕ) : unitBox d = SmoothEngine.box (Fin d) 1 := rfl

theorem card_subtype_inJ (J : Finset (Fin d)) : Fintype.card {i // inJ J i} = J.card :=
  Fintype.card_of_subtype J fun _ => inJ_iff.symm

/-- ★★ **The dilated spatial face functional is the empirical face functional**: on `(0,b]^{n+1}`
the limit of Headline XIX is `1/((m−1)! ∏_{j∈J} 2k_j) ∫_{(0,b]^{Jᶜ}} η(0_J,w) S_l(ξ(0_J,w))
residueWeight(w) dw`. -/
theorem spatialFace_dilated_eq_faceFunctional (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {b : ℝ} (hb : 0 < b)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) (hξc : Continuous ξ) (hηc : Continuous η) :
    b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
      spatialFace h k l 1 (fun v => ξ (b • v)) (fun v => η (b • v)) =
        faceFunctional h k l b ξ η := by
  set J := resSet h k l with hJ
  set m := multCount (ratioExp h k) l with hm
  have hmJ : m = J.card := (card_resSet h k l).symm
  have hm1 : 1 ≤ m := by
    obtain ⟨i, hi⟩ := hatt
    rw [hmJ]
    exact Finset.card_pos.2 ⟨i, mem_resSet.2 hi⟩
  -- the integrand on the unit box, and its face form
  set g : ({i // ¬ inJ J i} → ℝ) → Fin (n + 1) → ℝ := fun w => glue J 0 w with hg
  set F : ({i // ¬ inJ J i} → ℝ) → ℝ := fun w => η (g w) * fluctuation 1 l (ξ (g w)) *
    residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) l w with hF
  -- Step B: split the unit-box integral along `J`
  have hcont : Continuous fun u : Fin (n + 1) → ℝ =>
      η (b • faceProj h k l u) * (fluctuation 1 l (ξ (b • faceProj h k l u)) / 2) :=
    (hηc.comp ((continuous_faceProj h k l).const_smul b)).mul
      (((differentiable_fluctuation 1 l one_pos (by
        obtain ⟨i, hi⟩ := hatt
        rw [← hi]
        exact ratioExp_pos h k hk i)).continuous.comp
          (hξc.comp ((continuous_faceProj h k l).const_smul b))).div_const 2)
  have hint : IntegrableOn (fun u : Fin (n + 1) → ℝ =>
      η (b • faceProj h k l u) * (fluctuation 1 l (ξ (b • faceProj h k l u)) / 2) *
        residualWeight h k l u) (unitBox (n + 1)) := by
    obtain ⟨C, hC⟩ := (isCompact_closedCube (n + 1)).exists_bound_of_continuousOn hcont.continuousOn
    refine (residualWeight_integrableOn h k hk l hmin).bdd_mul (c := C)
      hcont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' (measurableSet_unitBox _)]
    exact Eventually.of_forall fun u hu => hC u (unitBox_subset_closedCube _ hu)
  have hsplit : ∫ u in unitBox (n + 1),
      η (b • faceProj h k l u) * (fluctuation 1 l (ξ (b • faceProj h k l u)) / 2) *
        residualWeight h k l u =
      ∫ w in SmoothEngine.box {i // ¬ inJ J i} 1,
        η (b • g w) * (fluctuation 1 l (ξ (b • g w)) / 2) *
          residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) l w := by
    rw [unitBox_eq_box] at hint ⊢
    rw [integral_box_split (J := J) 1 _ hint]
    refine setIntegral_congr_fun (measurableSet_box _) fun w hw => ?_
    have hval : ∀ u ∈ SmoothEngine.box {i // inJ J i} 1,
        η (b • faceProj h k l (glue J u w)) *
          (fluctuation 1 l (ξ (b • faceProj h k l (glue J u w))) / 2) *
            residualWeight h k l (glue J u w) =
        η (b • g w) * (fluctuation 1 l (ξ (b • g w)) / 2) *
          residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) l w := fun u _ => by
      rw [faceProj_glue, residualWeight_glue h k l u hw]
    rw [setIntegral_congr_fun (measurableSet_box _) hval, setIntegral_const]
    have hvol : (volume (SmoothEngine.box {i // inJ J i} 1)).toReal = 1 := by
      unfold SmoothEngine.box
      rw [volume_pi_Ioc_toReal (fun _ => zero_le_one)]
      simp
    rw [measureReal_def, hvol, one_smul]
  -- Step C: scale the complementary integral to the box of side `b`
  have hscale : ∫ w in SmoothEngine.box {i // ¬ inJ J i} 1,
      η (b • g w) * (fluctuation 1 l (ξ (b • g w)) / 2) *
        residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) l w =
      b ^ (-((∑ i : {i // ¬ inJ J i}, (h i : ℝ)) - 2 * l * ∑ i : {i // ¬ inJ J i}, (k i : ℝ))) *
        ((b ^ Fintype.card {i // ¬ inJ J i})⁻¹ *
        ∫ w in SmoothEngine.box {i // ¬ inJ J i} b, F w / 2) := by
    have hpt : ∀ w ∈ SmoothEngine.box {i // ¬ inJ J i} 1,
        η (b • g w) * (fluctuation 1 l (ξ (b • g w)) / 2) *
          residueWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) l w =
        b ^ (-((∑ i : {i // ¬ inJ J i}, (h i : ℝ)) - 2 * l * ∑ i : {i // ¬ inJ J i}, (k i : ℝ))) *
          (F (b • w) / 2) := fun w hw => by
      have hw0 : ∀ i, 0 < w i := fun i => pos_of_mem_box hw i
      simp only [hF, hg]
      rw [glue_zero_smul, residueWeight_smul _ _ l hb hw0, Real.rpow_neg hb.le]
      have hbE : b ^ ((∑ i : {i // ¬ inJ J i}, (h i : ℝ)) -
          2 * l * ∑ i : {i // ¬ inJ J i}, (k i : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
      field_simp
    rw [setIntegral_congr_fun (measurableSet_box _) hpt, integral_const_mul]
    unfold SmoothEngine.box
    rw [integral_unitBox_comp_smul hb (fun w => F w / 2)]
  -- Step D: constants
  have hprodk : (∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) = ∏ i ∈ J, (k i : ℝ) := by
    rw [hJ, resSet, Finset.prod_filter]
  have hprod2k : ∏ i ∈ J, (2 * (k i : ℝ)) = 2 ^ m * ∏ i ∈ J, (k i : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hmJ]
  have hcardc : (Fintype.card {i // ¬ inJ J i} : ℝ) = (n + 1 : ℝ) - m := by
    rw [Fintype.card_subtype_compl, card_subtype_inJ, Fintype.card_fin, hmJ]
    have := (Finset.card_le_univ J).trans (le_of_eq (Fintype.card_fin (n + 1)))
    push_cast [Nat.cast_sub this]
    ring
  -- the resonant sum identity `∑_{i∈J} 2 k_i l = ∑_{i∈J} h_i + m`
  have hres : ∑ i : {i // inJ J i}, 2 * (k i.1 : ℝ) * l = ∑ i : {i // inJ J i}, ((h i.1 : ℝ) + 1) :=
    Finset.sum_congr rfl fun i _ => two_mul_k_mul_l_of_mem_resSet hk i.2
  have hsumh : ∑ i, (h i : ℝ) = ∑ i : {i // inJ J i}, (h i.1 : ℝ) +
      ∑ i : {i // ¬ inJ J i}, (h i.1 : ℝ) :=
    (Fintype.sum_subtype_add_sum_subtype (inJ J) fun i => (h i : ℝ)).symm
  have hsumk : ∑ i, (k i : ℝ) = ∑ i : {i // inJ J i}, (k i.1 : ℝ) +
      ∑ i : {i // ¬ inJ J i}, (k i.1 : ℝ) :=
    (Fintype.sum_subtype_add_sum_subtype (inJ J) fun i => (k i : ℝ)).symm
  have hcardJ : ((Fintype.card {i // inJ J i} : ℕ) : ℝ) = m := by
    rw [card_subtype_inJ, hmJ]
  have hsum1 : ∑ i : {i // inJ J i}, (1 : ℝ) = m := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardJ]
  have hexp : ((∑ i, h i + (n + 1) : ℕ) : ℝ) + (2 * (∑ i, k i : ℕ) : ℝ) * (-l) +
      -((∑ i : {i // ¬ inJ J i}, (h i : ℝ)) - 2 * l * ∑ i : {i // ¬ inJ J i}, (k i : ℝ)) +
      -(Fintype.card {i // ¬ inJ J i} : ℝ) = 0 := by
    rw [hcardc]
    push_cast
    rw [hsumh, hsumk]
    have hres' : ∑ i : {i // inJ J i}, 2 * (k i.1 : ℝ) * l =
        ∑ i : {i // inJ J i}, (h i.1 : ℝ) + m := by
      rw [hres, Finset.sum_add_distrib, hsum1]
    have : 2 * l * ∑ i : {i // inJ J i}, (k i.1 : ℝ) =
        ∑ i : {i // inJ J i}, 2 * (k i.1 : ℝ) * l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    linear_combination (-1 : ℝ) * hres' + (-1 : ℝ) * this
  -- assemble
  unfold spatialFace faceFunctional
  simp only [phaseMoment_eq_half_fluctuation, ← hm]
  have h2m : (2 : ℝ) ^ (m - 1) * 2 = 2 ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm1]
  rw [hsplit, hscale, hprodk, hprod2k, ← h2m]
  have hb1 : (b ^ (∑ i, h i + (n + 1)) : ℝ) = b ^ ((∑ i, h i + (n + 1) : ℕ) : ℝ) :=
    (Real.rpow_natCast b _).symm
  have hb2 : ((b ^ (2 * ∑ i, k i)) ^ (-l) : ℝ) = b ^ ((2 * (∑ i, k i : ℕ) : ℝ) * (-l)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    push_cast
    ring_nf
  have hb3 : ((b ^ Fintype.card {i // ¬ inJ J i})⁻¹ : ℝ) =
      b ^ (-(Fintype.card {i // ¬ inJ J i} : ℝ)) := by
    rw [Real.rpow_neg hb.le, Real.rpow_natCast]
  rw [hb1, hb2, hb3]
  have hall : b ^ ((∑ i, h i + (n + 1) : ℕ) : ℝ) * b ^ ((2 * (∑ i, k i : ℕ) : ℝ) * (-l)) *
      b ^ (-((∑ i : {i // ¬ inJ J i}, (h i : ℝ)) - 2 * l * ∑ i : {i // ¬ inJ J i}, (k i : ℝ))) *
      b ^ (-(Fintype.card {i // ¬ inJ J i} : ℝ)) = 1 := by
    rw [← Real.rpow_add hb, ← Real.rpow_add hb, ← Real.rpow_add hb, hexp, Real.rpow_zero]
  rw [integral_div]
  push_cast at hall ⊢
  linear_combination ((∫ w in SmoothEngine.box {i // ¬ inJ J i} b, F w) /
    (((m - 1).factorial : ℝ) * (2 ^ (m - 1) * 2 * ∏ i ∈ J, (k i : ℝ)))) * hall

end

end Grammar
