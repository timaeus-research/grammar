/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.BoxGeneralOrder

/-!
# The monomial orthant-box integral with inactive coordinates

The monomial integral `I(N) = ∫_{(0,ε]^d} ∏ u^h e^{−N ∏ u^{2k}} du` of a chart with possibly
INACTIVE coordinates (`k_j = 0`, which forces `h_j = 0`) has the leading asymptotics
`N^{λ}(log N)^{−(m−1)} I(N) → C > 0`, where `λ` is the common value `(h_j+1)/(2k_j)` of the
`m ≥ 1` active coordinates attaining the minimum and every other active coordinate has a larger
ratio (★ `exists_tendsto_monoBoxIntegral`). The inactive coordinates split off as the volume
factor `ε^{#inactive}` (Fubini along `MeasurableEquiv.piEquivPiSubtypeProd`,
`monoBoxIntegral_eq`), the active coordinates are relabelled to `Fin n`
(`measurePreserving_piCongrLeft`, `activeIntegral_eq_boxIntegralGen`), and the general
multiplicity theorem of the state-density programme (`boxIntegralGen_isEquivalent_general`)
gives the equivalence with `C N^{−λ}(log N)^{m−1}`. This is the lower-bound input of the
positivity half of the RLCT identification on the resolved manifold. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

variable {d : ℕ}

/-- The monomial integral over the orthant box `(0, ε]^d`. -/
noncomputable def monoBoxIntegral (k h : Fin d → ℕ) (ε N : ℝ) : ℝ :=
  ∫ u in Set.pi univ fun _ : Fin d => Ioc 0 ε,
    (∏ j, u j ^ h j) * exp (-N * ∏ j, u j ^ (2 * k j))

theorem restrict_orthantPi (ε : ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (Set.pi univ fun _ => Ioc 0 ε) =
      Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 ε) := by
  rw [volume_pi, Measure.restrict_pi_pi]

/-- The active coordinates of a chart. -/
abbrev Active (k : Fin d → ℕ) : Type := {j : Fin d // 0 < k j}

/-- The enumeration of the active coordinates. -/
noncomputable abbrev actEquiv (k : Fin d → ℕ) : Fin (Fintype.card (Active k)) ≃ Active k :=
  (Fintype.equivFin (Active k)).symm

/-- The active phase exponents in the enumeration. -/
noncomputable abbrev actK (k : Fin d → ℕ) (i : Fin (Fintype.card (Active k))) : ℕ :=
  k (actEquiv k i).1

/-- The active Jacobian exponents in the enumeration. -/
noncomputable abbrev actH (k h : Fin d → ℕ) (i : Fin (Fintype.card (Active k))) : ℕ :=
  h (actEquiv k i).1

theorem actK_pos (k : Fin d → ℕ) (i : Fin (Fintype.card (Active k))) : 0 < actK k i :=
  (actEquiv k i).2

/-- The monomial integral over the active coordinates. -/
noncomputable def activeIntegral (k h : Fin d → ℕ) (ε N : ℝ) : ℝ :=
  ∫ v : Active k → ℝ, (∏ j, v j ^ h j.1) * exp (-N * ∏ j, v j ^ (2 * k j.1))
    ∂Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 ε)

/-- The inactive volume factor `ε^{#inactive}`. -/
noncomputable def inactiveVolume (k : Fin d → ℕ) (ε : ℝ) : ℝ :=
  (Measure.pi fun _ : {j : Fin d // ¬ 0 < k j} => (volume : Measure ℝ).restrict (Ioc 0 ε)).real
    univ

theorem inactiveVolume_pos (k : Fin d → ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < inactiveVolume k ε := by
  unfold inactiveVolume
  rw [measureReal_def, Measure.pi_univ]
  simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, Finset.prod_const]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le]
  exact pow_pos hε _

/-- **Fubini for the inactive coordinates**: the monomial integral is the active integral times
the inactive volume. -/
theorem monoBoxIntegral_eq (k h : Fin d → ℕ) (hh0 : ∀ j, k j = 0 → h j = 0) (ε N : ℝ) :
    monoBoxIntegral k h ε N = activeIntegral k h ε N * inactiveVolume k ε := by
  unfold monoBoxIntegral activeIntegral inactiveVolume
  rw [restrict_orthantPi]
  set μ₀ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 ε) with hμ₀
  have hmp := measurePreserving_piEquivPiSubtypeProd (α := fun _ : Fin d => ℝ) (μ := fun _ => μ₀)
    (fun j => 0 < k j)
  have hpt : ∀ u : Fin d → ℝ, (∏ j, u j ^ h j) * exp (-N * ∏ j, u j ^ (2 * k j)) =
      ((∏ j : Active k, (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
          (fun j => 0 < k j) u).1 j ^ h j.1) *
        exp (-N * ∏ j : Active k, (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
          (fun j => 0 < k j) u).1 j ^ (2 * k j.1))) * (1 : ℝ) := by
    intro u
    have h1 : ∏ j : {j : Fin d // ¬ 0 < k j}, u j.1 ^ h j.1 = 1 :=
      Finset.prod_eq_one fun j _ => by rw [hh0 j.1 (Nat.eq_zero_of_not_pos j.2), pow_zero]
    have h2 : ∏ j : {j : Fin d // ¬ 0 < k j}, u j.1 ^ (2 * k j.1) = 1 :=
      Finset.prod_eq_one fun j _ => by rw [Nat.eq_zero_of_not_pos j.2, mul_zero, pow_zero]
    rw [mul_one, ← Fintype.prod_subtype_mul_prod_subtype (fun j => 0 < k j) (fun j => u j ^ h j),
      ← Fintype.prod_subtype_mul_prod_subtype (fun j => 0 < k j) (fun j => u j ^ (2 * k j)), h1,
      h2, mul_one, mul_one]
    rfl
  rw [integral_congr_ae (Eventually.of_forall hpt),
    hmp.integral_comp' (fun z : (Active k → ℝ) × ({j : Fin d // ¬ 0 < k j} → ℝ) =>
      ((∏ j, z.1 j ^ h j.1) * exp (-N * ∏ j, z.1 j ^ (2 * k j.1))) * (1 : ℝ)),
    integral_prod_mul
      (fun v : Active k → ℝ => (∏ j, v j ^ h j.1) * exp (-N * ∏ j, v j ^ (2 * k j.1)))
      (fun _ : {j : Fin d // ¬ 0 < k j} → ℝ => (1 : ℝ)),
    integral_const, smul_eq_mul, mul_one]

theorem prod_pow_two {n : ℕ} (w : Fin n → ℝ) (K : Fin n → ℕ) :
    (∏ i, w i ^ K i) ^ 2 = ∏ i, w i ^ (2 * K i) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]

/-- **Relabelling**: the active integral is the state-density box integral with zero shift and
unit amplitude at `c = √N`. -/
theorem activeIntegral_eq_boxIntegralGen (k h : Fin d → ℕ) (ε : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    activeIntegral k h ε N =
      boxIntegralGen 1 ε (Real.sqrt N) (actK k) (actH k h) (fun _ => 0) (fun _ => 1) := by
  set μ₀ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 ε) with hμ₀
  have hmp := measurePreserving_piCongrLeft (α := fun _ : Active k => ℝ) (μ := fun _ => μ₀)
    (actEquiv k)
  unfold activeIntegral boxIntegralGen boxMeasure
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  have h1 : ∏ j : Active k, (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ h j.1 =
      ∏ i, w i ^ actH k h i := by
    refine (Fintype.prod_equiv (actEquiv k) (fun i => w i ^ actH k h i)
      (fun j => (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ h j.1)
      fun i => ?_).symm
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  have h2 : ∏ j : Active k,
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ (2 * k j.1) =
      ∏ i, w i ^ (2 * actK k i) := by
    refine (Fintype.prod_equiv (actEquiv k) (fun i => w i ^ (2 * actK k i))
      (fun j => (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ (2 * k j.1))
      fun i => ?_).symm
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  change (∏ j : Active k, (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ h j.1) *
      exp (-N * ∏ j : Active k,
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (actEquiv k) w) j ^ (2 * k j.1)) =
    (∏ i, w i ^ actH k h i) * (1 : ℝ) *
      exp (-1 * (Real.sqrt N * ∏ i, w i ^ actK k i) ^ 2 +
        1 * (Real.sqrt N * ∏ i, w i ^ actK k i) * 0)
  rw [h1, h2, mul_one, mul_zero, add_zero, neg_one_mul, mul_pow, Real.sq_sqrt hN, prod_pow_two,
    neg_mul]

/-- ★ **The leading asymptotics of the monomial orthant-box integral**: if the active
coordinates have ratio `(h_j+1)/(2k_j) ≥ λ` with equality for exactly `m ≥ 1` of them, then
`N^{λ}(log N)^{−(m−1)} I(N) → C` for some `C > 0`. -/
theorem exists_tendsto_monoBoxIntegral (k h : Fin d → ℕ) (hh0 : ∀ j, k j = 0 → h j = 0)
    {ε : ℝ} (hε : 0 < ε) {lam : ℝ} {m : ℕ}
    (hlam : ∀ j, 0 < k j → 2 * (k j : ℝ) * lam ≤ h j + 1)
    (hm : (Finset.univ.filter fun j => 0 < k j ∧ 2 * (k j : ℝ) * lam = h j + 1).card = m)
    (hm1 : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun N : ℝ => N ^ lam / Real.log N ^ (m - 1) * monoBoxIntegral k h ε N) atTop
        (𝓝 C) := by
  have hmin : ∀ i, 2 * lam ≤ finExp (actK k) (actH k h) i := by
    intro i
    unfold finExp
    rw [le_div_iff₀ (Nat.cast_pos.2 (actK_pos k i))]
    have := hlam (actEquiv k i).1 (actEquiv k i).2
    change 2 * lam * (k (actEquiv k i).1 : ℝ) ≤ (h (actEquiv k i).1 : ℝ) + 1
    linarith
  have hM : (Finset.univ.filter fun i => finExp (actK k) (actH k h) i = 2 * lam).card =
      (m - 1) + 1 := by
    rw [Nat.sub_add_cancel hm1, ← hm]
    refine Finset.card_bij (fun i _ => (actEquiv k i).1) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, (actEquiv k i).2, ?_⟩
      have hk : (actK k i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (actK_pos k i).ne'
      have := hi.2
      unfold finExp at this
      rw [div_eq_iff hk] at this
      change (h (actEquiv k i).1 : ℝ) + 1 = 2 * lam * (k (actEquiv k i).1 : ℝ) at this
      linarith
    · intro i₁ _ i₂ _ heq
      exact (actEquiv k).injective (Subtype.ext heq)
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨(actEquiv k).symm ⟨j, hj.2.1⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        unfold finExp
        have hk : (actK k ((actEquiv k).symm ⟨j, hj.2.1⟩) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.2 (actK_pos k _).ne'
        rw [div_eq_iff hk]
        have := hj.2.2
        change (h (actEquiv k ((actEquiv k).symm ⟨j, hj.2.1⟩)).1 : ℝ) + 1 =
          2 * lam * (k (actEquiv k ((actEquiv k).symm ⟨j, hj.2.1⟩)).1 : ℝ)
        rw [Equiv.apply_symm_apply]
        linarith
      · rw [Equiv.apply_symm_apply]
  obtain ⟨C, hC, hequiv⟩ := boxIntegralGen_isEquivalent_general 1 ε one_pos hε (actK k)
    (actH k h) (actK_pos k) (2 * lam) hmin (m - 1) hM (fun _ => 0) (fun _ => 1) continuous_const
    continuous_const (fun _ _ _ => one_pos)
  refine ⟨inactiveVolume k ε * C, mul_pos (inactiveVolume_pos k hε) hC, ?_⟩
  have hv : ∀ᶠ n : ℝ in atTop, C * (n ^ (-(2 * lam / 2)) * Real.log n ^ (m - 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact (mul_pos hC (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (pow_pos (Real.log_pos hn) _))).ne'
  have hlim := ((isEquivalent_iff_tendsto_one hv).1 hequiv).const_mul (inactiveVolume k ε * C)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn0 : 0 ≤ n := by linarith
  rw [monoBoxIntegral_eq k h hh0, activeIntegral_eq_boxIntegralGen k h ε hn0]
  simp only [Pi.div_apply]
  rw [mul_div_cancel_left₀ lam two_ne_zero, Real.rpow_neg hn0]
  have hA : (n ^ lam : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hL : (Real.log n ^ (m - 1) : ℝ) ≠ 0 := (pow_pos (Real.log_pos hn) _).ne'
  have hC' : C ≠ 0 := hC.ne'
  field_simp

end Grammar
