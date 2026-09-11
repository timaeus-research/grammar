/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MonomialBoxExpansion

/-!
# The two-sided exact-monomial box: reflections as tiling pieces (Astra #69 B0, orthants)

The box `A × [-b,b]^{n+1}` is tiled by its `2^{n+1}` orthants. Each orthant is the image of the
positive box under a coordinate reflection `Ψ_σ(v,u) = (v, σ·u)` (`reflectEquiv`, a continuous
linear equivalence with `|det| = 1`, `det_reflectEquiv`), the phase is invariant (even exponents,
`monomialPhase_reflect`), and the amplitude of the reflected piece is the joint series composed
with the coordinate reflection of the joint space, a linear isometry, so the series margin is
preserved (`jointReflect`, `hasFPowerSeriesOnBall_comp_jointReflect`). The orthants are pairwise
disjoint (`disjoint_orthant`) and cover the box up to the null faces, so the reflected positive box
charts form an exact-normal tiling and the two-sided box integral

  `∫_{A × [-b,b]^{n+1}} F(v,u) e^{−Nβ∏ u_i^{2k_i}} dv du`

has the full power–log cutoff expansion (`twoSidedBox_cutoffExpansion`). This is the two-sided
`N(x₀x₁,1)`-type box of the paper with an arbitrary jointly analytic amplitude, unconditionally.

Non-claims: one joint-series centre; the identity chart (no analytic unit); reflections are the
only geometry.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily

variable {t n : ℕ}

/-! ### Sign patterns and coordinate reflections -/

/-- The sign of a boolean pattern at a coordinate. -/
def boolSgn (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ℝ := if σ i then 1 else -1

theorem boolSgn_mul_self (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    boolSgn σ i * boolSgn σ i = 1 := by
  unfold boolSgn
  split_ifs <;> norm_num

theorem abs_boolSgn (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) : |boolSgn σ i| = 1 := by
  unfold boolSgn
  split_ifs <;> simp

theorem boolSgn_pow_two_mul (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) (m : ℕ) :
    boolSgn σ i ^ (2 * m) = 1 := by
  rw [pow_mul, sq, boolSgn_mul_self, one_pow]

theorem boolSgn_ne_zero (σ : Fin (n + 1) → Bool) (i : Fin (n + 1)) : boolSgn σ i ≠ 0 := by
  unfold boolSgn
  split_ifs <;> norm_num

/-- The coordinate reflection of the normal space by the sign pattern `σ`. -/
noncomputable def reflectEquiv (σ : Fin (n + 1) → Bool) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun i =>
    if σ i then ContinuousLinearEquiv.refl ℝ ℝ else ContinuousLinearEquiv.neg ℝ

theorem reflectEquiv_apply (σ : Fin (n + 1) → Bool) (u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    reflectEquiv σ u i = boolSgn σ i * u i := by
  unfold reflectEquiv boolSgn
  rw [ContinuousLinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

theorem reflectEquiv_reflectEquiv (σ : Fin (n + 1) → Bool) (u : Fin (n + 1) → ℝ) :
    reflectEquiv σ (reflectEquiv σ u) = u := by
  funext i
  rw [reflectEquiv_apply, reflectEquiv_apply, ← mul_assoc, boolSgn_mul_self, one_mul]

/-- **The determinant of a coordinate reflection** is the product of the signs. -/
theorem det_reflectEquiv (σ : Fin (n + 1) → Bool) :
    ((reflectEquiv σ : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))).det = ∏ i, boolSgn σ i := by
  have h : (((reflectEquiv σ : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))) :
      (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) =
      LinearMap.pi fun i => (boolSgn σ i • LinearMap.id) ∘ₗ LinearMap.proj i := by
    apply LinearMap.ext
    intro u
    funext i
    simp [reflectEquiv_apply]
  unfold ContinuousLinearMap.det
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

theorem abs_det_reflectEquiv (σ : Fin (n + 1) → Bool) :
    |((reflectEquiv σ : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))).det| = 1 := by
  rw [det_reflectEquiv, Finset.abs_prod]
  simp [abs_boolSgn]

/-- The reflected product chart `(v, u) ↦ (v, σ·u)`. -/
noncomputable def reflectChart (σ : Fin (n + 1) → Bool) :
    ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) ≃L[ℝ] ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) :=
  (ContinuousLinearEquiv.refl ℝ (Fin t → ℝ)).prodCongr (reflectEquiv σ)

theorem reflectChart_apply (σ : Fin (n + 1) → Bool) (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :
    reflectChart σ p = (p.1, reflectEquiv σ p.2) := rfl

theorem abs_det_reflectChart (σ : Fin (n + 1) → Bool) :
    |((reflectChart (t := t) σ : ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) →L[ℝ] _)).det| = 1 := by
  unfold reflectChart
  rw [ContinuousLinearEquiv.coe_prodCongr]
  unfold ContinuousLinearMap.det
  rw [ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
  have h1 : LinearMap.det ((ContinuousLinearEquiv.refl ℝ (Fin t → ℝ) :
      (Fin t → ℝ) →L[ℝ] (Fin t → ℝ)) : (Fin t → ℝ) →ₗ[ℝ] (Fin t → ℝ)) = 1 := by
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have h2 := det_reflectEquiv σ
  unfold ContinuousLinearMap.det at h2
  rw [h1, h2, one_mul, Finset.abs_prod]
  simp [abs_boolSgn]

theorem monomialPhase_reflect (k : Fin (n + 1) → ℕ) (β : ℝ) (σ : Fin (n + 1) → Bool)
    (p : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :
    monomialPhase k β (reflectChart σ p) = monomialPhase k β p := by
  unfold monomialPhase
  rw [reflectChart_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [reflectEquiv_apply]
  rw [mul_pow, boolSgn_pow_two_mul, one_mul]

/-! ### The reflection of the joint space -/

/-- The joint sign pattern: `1` on the tangential coordinates, `boolSgn σ` on the normal ones. -/
def jointBoolSgn (σ : Fin (n + 1) → Bool) : Fin t ⊕ Fin (n + 1) → ℝ :=
  Sum.elim (fun _ => 1) (boolSgn σ)

theorem abs_jointBoolSgn (σ : Fin (n + 1) → Bool) (x : Fin t ⊕ Fin (n + 1)) :
    |jointBoolSgn (t := t) σ x| = 1 := by
  rcases x with i | j
  · simp [jointBoolSgn]
  · simp [jointBoolSgn, abs_boolSgn]

/-- The coordinate reflection of the joint space. -/
noncomputable def jointReflect (σ : Fin (n + 1) → Bool) :
    (Fin t ⊕ Fin (n + 1) → ℝ) →L[ℝ] (Fin t ⊕ Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun x => jointBoolSgn σ x • ContinuousLinearMap.proj x

theorem jointReflect_apply (σ : Fin (n + 1) → Bool) (w : Fin t ⊕ Fin (n + 1) → ℝ)
    (x : Fin t ⊕ Fin (n + 1)) : jointReflect σ w x = jointBoolSgn σ x * w x := by
  simp [jointReflect]

theorem jointReflect_sum_elim (σ : Fin (n + 1) → Bool) (v : Fin t → ℝ) (u : Fin (n + 1) → ℝ) :
    jointReflect σ (Sum.elim v u) = Sum.elim v (reflectEquiv σ u) := by
  funext x
  rcases x with i | j
  · simp [jointReflect_apply, jointBoolSgn]
  · simp [jointReflect_apply, jointBoolSgn, reflectEquiv_apply]

theorem norm_jointReflect (σ : Fin (n + 1) → Bool) (w : Fin t ⊕ Fin (n + 1) → ℝ) :
    ‖jointReflect σ w‖ = ‖w‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun x => ?_
    rw [jointReflect_apply, Real.norm_eq_abs, abs_mul, abs_jointBoolSgn, one_mul,
      ← Real.norm_eq_abs]
    exact norm_le_pi_norm w x
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun x => ?_
    have := norm_le_pi_norm (jointReflect σ w) x
    rwa [jointReflect_apply, Real.norm_eq_abs, abs_mul, abs_jointBoolSgn, one_mul,
      ← Real.norm_eq_abs] at this

theorem enorm_jointReflect_le (σ : Fin (n + 1) → Bool) : ‖jointReflect (t := t) σ‖ₑ ≤ 1 := by
  have h : ‖jointReflect (t := t) σ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by rw [norm_jointReflect, one_mul]
  rw [enorm_eq_nnnorm]
  exact ENNReal.coe_le_one_iff.2 (by exact_mod_cast h)

/-- **The joint series of the reflected amplitude** keeps its radius. -/
theorem hasFPowerSeriesOnBall_comp_jointReflect {G : (Fin t ⊕ Fin (n + 1) → ℝ) → ℝ}
    {P : FormalMultilinearSeries ℝ (Fin t ⊕ Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall G P 0 R) (σ : Fin (n + 1) → Bool) :
    HasFPowerSeriesOnBall (G ∘ jointReflect σ) (P.compContinuousLinearMap (jointReflect σ)) 0
      R := by
  have hG' : HasFPowerSeriesOnBall G P (jointReflect σ 0) R := by simpa using hG
  have h := hG'.compContinuousLinearMap
  refine h.mono hG.r_pos ?_
  calc R = R / 1 := (div_one R).symm
    _ ≤ R / ‖jointReflect (t := t) σ‖ₑ := ENNReal.div_le_div_left (enorm_jointReflect_le σ) R

/-! ### The orthant pieces -/

/-- Membership in the `σ`-orthant image of the positive box. -/
theorem mem_reflectChart_image_iff (σ : Fin (n + 1) → Bool) (A : Set (Fin t → ℝ)) (b : ℝ)
    (z : (Fin t → ℝ) × (Fin (n + 1) → ℝ)) :
    z ∈ reflectChart σ '' (A ×ˢ piBox (n + 1) (Ioc 0 b)) ↔
      z.1 ∈ A ∧ ∀ i, boolSgn σ i * z.2 i ∈ Ioc (0 : ℝ) b := by
  constructor
  · rintro ⟨⟨v, u⟩, ⟨hv, hu⟩, rfl⟩
    refine ⟨hv, fun i => ?_⟩
    rw [reflectChart_apply]
    simp only [reflectEquiv_apply, ← mul_assoc, boolSgn_mul_self, one_mul]
    exact hu i (mem_univ i)
  · rintro ⟨hz1, hz2⟩
    refine ⟨(z.1, reflectEquiv σ z.2), ⟨hz1, fun i _ => ?_⟩, ?_⟩
    · change reflectEquiv σ z.2 i ∈ Ioc (0 : ℝ) b
      rw [reflectEquiv_apply]
      exact hz2 i
    · rw [reflectChart_apply, reflectEquiv_reflectEquiv]

theorem disjoint_orthant {σ σ' : Fin (n + 1) → Bool} (h : σ ≠ σ') (A : Set (Fin t → ℝ)) (b : ℝ) :
    Disjoint (reflectChart σ '' (A ×ˢ piBox (n + 1) (Ioc 0 b)))
      (reflectChart σ' '' (A ×ˢ piBox (n + 1) (Ioc 0 b))) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_reflectChart_image_iff] at hz hz'
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ σ' i := by
    by_contra hcon
    push Not at hcon
    exact h (funext hcon)
  have h1 := (hz.2 i).1
  have h2 := (hz'.2 i).1
  have hs : boolSgn σ i = -boolSgn σ' i := by
    unfold boolSgn
    cases hσ : σ i <;> cases hσ' : σ' i <;> simp_all
  rw [hs] at h1
  linarith

/-- The two-sided box `A × [-b,b]^{n+1}`. -/
def twoSidedBox (A : Set (Fin t → ℝ)) (b : ℝ) : Set ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) :=
  A ×ˢ piBox (n + 1) (Icc (-b) b)

theorem isCompact_twoSidedBox {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b : ℝ) :
    IsCompact (twoSidedBox (n := n) A b) :=
  hA.prod (isCompact_univ_pi fun _ => isCompact_Icc)

theorem measurableSet_twoSidedBox {A : Set (Fin t → ℝ)} (hA : IsCompact A) (b : ℝ) :
    MeasurableSet (twoSidedBox (n := n) A b) :=
  hA.isClosed.measurableSet.prod (measurableSet_piBox _ _ measurableSet_Icc)

/-- The localisation datum of the two-sided box integral. -/
noncomputable def twoSidedBoxData (k : Fin (n + 1) → ℕ) {β : ℝ} (hβ : 0 < β) {A : Set (Fin t → ℝ)}
    (hA : IsCompact A) (b : ℝ) {F : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContinuousOn F (twoSidedBox A b)) {δ : ℝ} (hδ : 0 < δ) :
    LocalisationData ((Fin t → ℝ) × (Fin (n + 1) → ℝ)) where
  μ := volume.restrict (twoSidedBox A b)
  phase := monomialPhase k β
  obs := F
  phase_measurable := (continuous_monomialPhase k β).measurable
  phase_nonneg := Eventually.of_forall (monomialPhase_nonneg hβ.le)
  obs_integrable := hF.integrableOn_compact (isCompact_twoSidedBox hA b)
  δ := δ
  δ_pos := hδ

/-- **The unconditional expansion of the two-sided exact-monomial box integral.** -/
theorem twoSidedBox_cutoffExpansion (k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β)
    {A : Set (Fin t → ℝ)} (hA : IsCompact A) {B b : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hB : 0 < B)
    (hAB : ∀ v ∈ A, ∀ i, |v i| ≤ B) {F : (Fin t → ℝ) × (Fin (n + 1) → ℝ) → ℝ}
    (hF : ContinuousOn F (twoSidedBox A b))
    {P : FormalMultilinearSeries ℝ (Fin t ⊕ Fin (n + 1) → ℝ) ℝ} {R : ℝ≥0∞}
    (hG : HasFPowerSeriesOnBall (fun w => F (w ∘ Sum.inl, w ∘ Sum.inr)) P 0 R) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < R) (hBρ : ((t + (n + 1) : ℕ) : ℝ) * B < ρ) (hB1 : B < ρ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (Q Dg : ℕ) (c : ℝ → ℕ → ℝ), 0 < Q ∧
      CutoffExpansion Q Dg
        (fun N => ∫ z in twoSidedBox A b, F z * Real.exp (-N * monomialPhase k β z)) c := by
  classical
  set D := twoSidedBoxData k hβ hA b hF hδ with hD
  have : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have hcard : (Fintype.card (Fin t ⊕ Fin (n + 1)) : ℝ) * B < ρ := by
    simpa [Fintype.card_sum] using hBρ
  -- the orthant pieces
  have hpiece : ∀ σ : Fin (n + 1) → Bool, ∃ Pc : TilingPiece D β,
      Pc.image = reflectChart σ '' (A ×ˢ piBox (n + 1) (Ioc 0 b)) := by
    intro σ
    have hGσ := hasFPowerSeriesOnBall_comp_jointReflect hG σ
    set Pσ := P.compContinuousLinearMap (jointReflect σ) with hPσ
    have hW : Summable (jointWeight Pσ B) :=
      summable_jointWeight Pσ B (summable_monoFamily_mul_pow Pσ (hρ.trans_le hGσ.r_le) hB.le hcard)
    set x : TangentialData A (n + 1) := jointTangentialData Pσ B hb hbB hB hW A hAB with hx
    let chart : PositiveBoxChart (D.comapEquiv (MeasurableEquiv.refl _)) A b β :=
      ⟨fun _ => 0, k, hk, reflectChart σ, univ, isOpen_univ, subset_univ _,
        (reflectChart (t := t) σ).contDiff.contDiffOn,
        (reflectChart σ).injective.injOn, fun _ => 1, measurable_const, fun _ _ => zero_le_one,
        fun p _ => by
          rw [← ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.fderiv, abs_det_reflectChart]
          simp,
        fun p _ => by
          change monomialPhase k β (reflectChart σ p) = _
          rw [monomialPhase_reflect]
          rfl,
        x, fun v => xiCoord_jointTangentialData Pσ B hb hbB hB hW A hAB v,
        fun v u hu => by
          have hu' : ∀ j, |u j| ≤ b := fun j => by
            have := hu j (mem_univ j)
            rw [abs_le]
            constructor <;> linarith [this.1, this.2]
          rw [hx, evalF_toEta_jointTangentialData Pσ B hb hbB hB hW A hAB hGσ hρ hBρ hB1 v hu',
            one_mul]
          simp only [Function.comp, jointReflect_sum_elim, LocalisationData.comapEquiv_obs,
            MeasurableEquiv.refl_apply, hD, twoSidedBoxData, reflectChart_apply, Sum.elim_comp_inl,
            Sum.elim_comp_inr]⟩
    let Pc : TilingPiece D β :=
      { t := t, n := n, e := MeasurableEquiv.refl _, e_vol := MeasurePreserving.id _, A := A,
        A_compact := hA, b := b, b_pos := hb, chart := chart }
    refine ⟨Pc, ?_⟩
    simp [TilingPiece.image, TilingPiece.box, Pc, chart]
  choose piece himage using hpiece
  set eσ := Fintype.equivFin (Fin (n + 1) → Bool) with heσ
  let T : ExactNormalTiling D β :=
    { Ω := twoSidedBox A b, μ_eq := rfl, M := Fintype.card (Fin (n + 1) → Bool),
      piece := fun I => piece (eσ.symm I),
      image_subset := fun I => by
        rw [himage]
        rintro z hz
        rw [mem_reflectChart_image_iff] at hz
        refine ⟨hz.1, fun i _ => ?_⟩
        have h := hz.2 i
        have habs : |z.2 i| = boolSgn (eσ.symm I) i * z.2 i := by
          rw [← abs_of_pos h.1, abs_mul, abs_boolSgn, one_mul]
        rw [mem_Icc, ← abs_le, habs]
        exact h.2,
      aedisjoint := fun I J hIJ => by
        rw [himage, himage]
        have hne : eσ.symm I ≠ eσ.symm J := fun h => hIJ (eσ.symm.injective h)
        rw [Set.disjoint_iff_inter_eq_empty.1 (disjoint_orthant hne A b), measure_empty],
      δ₀ := 1, δ₀_pos := one_pos,
      gap := by
        have hΩ : MeasurableSet (twoSidedBox (n := n) A b) := measurableSet_twoSidedBox hA b
        change ∀ᵐ z ∂(volume.restrict (twoSidedBox A b)), _
        filter_upwards [ae_restrict_mem hΩ, ae_restrict_of_ae (ae_ne_zero_snd (t := t) (n := n))]
          with z hz hz0 hnot
        exfalso
        set σ : Fin (n + 1) → Bool := fun i => decide (0 < z.2 i) with hσ
        refine hnot (mem_iUnion.2 ⟨eσ σ, ?_⟩)
        simp only [Equiv.symm_apply_apply]
        rw [himage, mem_reflectChart_image_iff]
        refine ⟨hz.1, fun i => ?_⟩
        have hzi := hz.2 i (mem_univ i)
        have hpos : 0 < boolSgn σ i * z.2 i := by
          simp only [hσ, boolSgn]
          by_cases h : 0 < z.2 i
          · simp [h]
          · have hlt : z.2 i < 0 := lt_of_le_of_ne (not_lt.1 h) (hz0 i)
            simp [h]
            linarith
        refine ⟨hpos, ?_⟩
        have habs : boolSgn σ i * z.2 i = |z.2 i| := by
          rw [← abs_of_pos hpos, abs_mul, abs_boolSgn, one_mul]
        rw [habs, abs_le]
        exact ⟨hzi.1, hzi.2⟩ }
  exact T.cutoffExpansion hβ

end Grammar
