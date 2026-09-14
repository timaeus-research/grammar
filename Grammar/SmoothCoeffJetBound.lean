/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothObservableCoeff
import Grammar.SmoothCoeffBound
import Grammar.SmoothRenormalisedStrata
import Grammar.CoordinateFrechetBridge

/-!
# The finite-order bound on the observable coefficient functional (consult #123, units C1b–C1c)

The observable coefficient functional `observableCoeff X μ q` of the resolution bridge is bounded
by finitely many derivatives of the observable on the compact core image:

  `|observableCoeff X μ q f| ≤ C · M`  whenever  `‖D^r f‖ ≤ M` on `coreImage X` for all `r ≤ R`,

with `R = engineOrder X μ` the maximum over the chart pieces of the SUM of the engine's canonical
depths (the rectangular derivative bound `RectBound` can require mixed derivatives of total order
`∑ pᵢ`), and `C` independent of `f`. The chain is:

* **Leibniz** (`RectBound.mul`): a rectangular bound for a product `D · f` from bounds for the
  factors, with the constant `2^{∑ p}`;
* **affine transfer** (`abs_pdMulti_comp_affineMap_finRange`): coordinate derivatives of a
  pull-back along the orthant glue `affineMap` are, up to sign, coordinate derivatives of the
  original function at the image point;
* the **piece bound** — the engine's quantitative bound `abs_smoothCoeff_le` applied to the
  product amplitude `ρfam · obsfam` (equal to the piece amplitude on the box,
  `smoothCoeff_congr_box`), with the uniform rectangular bound of the density family
  (`exists_uniform_rect_bound`) and the chain-rule bound for `f ∘ ψᵢ` on the chart box;
* summation over the pieces and integration over the compact bases.

`engineOrder_le_chartJetTotal` compares the order with the jet order of finite-jet
determination (CDIX): `engineOrder X μ ≤ max_i chartJetTotal X i μ`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff
open Monomialize.VolumeScaling

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Derivative bounds on a compact set -/

/-- `‖D^r f x‖ ≤ M` for all `r ≤ R` and `x ∈ S`. -/
def JetBound (R : ℕ) (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) (M : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ S, ‖iteratedFDeriv ℝ r f x‖ ≤ M

theorem JetBound.mono {R R' : ℕ} {S S' : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} {M M' : ℝ}
    (h : JetBound R S f M) (hR : R' ≤ R) (hS : S' ⊆ S) (hM : M ≤ M') : JetBound R' S' f M' :=
  fun r hr x hx => (h r (hr.trans hR) x (hS hx)).trans hM

/-! ### Leibniz for rectangular bounds -/

theorem RectBound.nonneg {F : (Fin d → ℝ) → ℝ} {p : Fin d → ℕ} {b M : ℝ} (hb : 0 ≤ b)
    (h : RectBound F p b M) : 0 ≤ M :=
  (abs_nonneg _).trans (h 0 (fun _ => Nat.zero_le _) (fun _ => 0) fun _ => ⟨le_rfl, hb⟩)

/-- The binomial sum over the multi-indices below `m`: `∑_{a ≤ m} ∏ C(mᵢ, aᵢ) = 2^{∑ mᵢ}`. -/
theorem sum_idxL_prod_choose (m : Fin d → ℕ) :
    ∑ a ∈ idxL (fun j => m j + 1) (List.finRange d),
      (∏ i ∈ (List.finRange d).toFinset, ((m i).choose (a i) : ℝ)) = 2 ^ (∑ i, m i) := by
  unfold idxL
  simp only [List.mem_finRange, if_true, List.toFinset_finRange]
  have h := Finset.prod_univ_sum (fun i => Finset.range (m i + 1))
    (fun i c => ((m i).choose c : ℝ))
  beta_reduce at h
  rw [← h, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact_mod_cast Nat.sum_range_choose (m i)

/-- ★ **Leibniz for rectangular bounds**: `|∂^m(D f)| ≤ 2^{∑ p} M_D M_f` on the box for `m ≤ p`. -/
theorem RectBound.mul {D f : (Fin d → ℝ) → ℝ} (hD : ContDiff ℝ ∞ D) (hf : ContDiff ℝ ∞ f)
    {p : Fin d → ℕ} {b MD Mf : ℝ} (hb : 0 ≤ b) (hDb : RectBound D p b MD)
    (hfb : RectBound f p b Mf) :
    RectBound (fun v => D v * f v) p b (2 ^ (∑ i, p i) * MD * Mf) := by
  have hMD := hDb.nonneg hb
  have hMf := hfb.nonneg hb
  intro m hm v hv
  rw [pdMulti_mul_choose hD hf m (List.nodup_finRange d)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ a ∈ idxL (fun j => m j + 1) (List.finRange d),
      |(∏ i ∈ (List.finRange d).toFinset, ((m i).choose (a i) : ℝ)) *
        (pdMulti (m - a) (List.finRange d) D v * pdMulti a (List.finRange d) f v)| ≤
      (∏ i ∈ (List.finRange d).toFinset, ((m i).choose (a i) : ℝ)) * (MD * Mf) := by
    intro a ha
    have hale : ∀ i, a i ≤ m i := fun i => by
      have := (Fintype.mem_piFinset.1 ha) i
      simp only [List.mem_finRange, if_true, Finset.mem_range] at this
      omega
    rw [abs_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
    exact mul_le_mul (hDb _ (fun i => (Nat.sub_le _ _).trans (hm i)) v hv)
      (hfb _ (fun i => (hale i).trans (hm i)) v hv) (abs_nonneg _) hMD
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, sum_idxL_prod_choose, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hMD hMf)
  exact pow_le_pow_right₀ (by norm_num) (Finset.sum_le_sum fun i _ => hm i)

/-! ### Affine transfer -/

variable {da : ℕ} {J : Finset (Fin d)}

/-- Coordinate derivatives of a pull-back along the orthant glue are, in absolute value,
coordinate derivatives of the original function at the image point. -/
theorem abs_pdMulti_comp_affineMap_finRange (e : Fin da ≃ {i // inJ J i})
    (σ : WaterFilling.CoordSign d) (sc : {i // ¬ inJ J i} → ℝ) {G : (Fin d → ℝ) → ℝ}
    (hG : ContDiff ℝ ∞ G) (m : Fin da → ℕ) (v : Fin da → ℝ) :
    |pdMulti m (List.finRange da) (fun v => G (affineMap e σ sc v)) v| =
      |pdMulti (extendIdx e m) (List.finRange d) G (affineMap e σ sc v)| := by
  rw [pdMulti_finRange_comp_affineMap]
  have hnd : ((List.finRange da).map fun j => (e j).1).Nodup :=
    (List.nodup_finRange da).map fun j j' hjj' => e.injective (Subtype.val_injective hjj')
  have hsupp : ∀ i, i ∉ (List.finRange da).map (fun j => (e j).1) → extendIdx e m i = 0 := by
    intro i hi
    refine extendIdx_of_not_mem e m fun hiJ => hi ?_
    exact List.mem_map.2 ⟨e.symm ⟨i, hiJ⟩, List.mem_finRange _, by simp⟩
  rw [pdMulti_eq_finRange_of_nodup hG hnd hsupp, abs_mul]
  have hsgn : |∏ j, WaterFilling.sgn σ (e j).1 ^ m j| = 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [abs_pow, WaterFilling.abs_sgn, one_pow]
  rw [hsgn, one_mul]

/-- The total order of the extended multi-index. -/
theorem sum_extendIdx (e : Fin da ≃ {i // inJ J i}) (m : Fin da → ℕ) :
    ∑ i, extendIdx e m i = ∑ j, m j := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin d => inJ J i)]
  have h1 : ∑ i : {i // inJ J i}, extendIdx e m i = ∑ j, m j :=
    (Fintype.sum_equiv e _ _ fun j => (extendIdx_face e m j).symm).symm
  have h2 : ∑ i : {i // ¬ inJ J i}, extendIdx e m i = 0 :=
    Finset.sum_eq_zero fun i _ => extendIdx_of_not_mem e m i.2
  rw [h1, h2, add_zero]

/-! ### The engine order of the bridge -/

namespace BridgeInputs

variable (X : BridgeInputs d)

/-- The canonical engine depth of a piece at the exponent `μ`. -/
noncomputable def pieceDepth (p : X.PIdx) (μ : ℝ) : Fin (X.da p) → ℕ :=
  depthOf (X.hA p) (X.kA p) (cutoffOf (X.hA p) μ)

/-- ★ **The engine order**: the maximum over the pieces of the total canonical depth. -/
noncomputable def engineOrder (μ : ℝ) : ℕ :=
  Finset.univ.sup fun p : X.PIdx => ∑ j, X.pieceDepth p μ j

theorem sum_pieceDepth_le_engineOrder (p : X.PIdx) (μ : ℝ) :
    ∑ j, X.pieceDepth p μ j ≤ X.engineOrder μ :=
  Finset.le_sup (f := fun p : X.PIdx => ∑ j, X.pieceDepth p μ j) (Finset.mem_univ p)

/-- ★ The engine order is at most the maximal chart jet total of finite-jet determination. -/
theorem engineOrder_le_chartJetTotal (μ : ℝ) :
    X.engineOrder μ ≤ Finset.univ.sup fun i : X.T.ι => X.chartJetTotal i μ := by
  refine Finset.sup_le fun p _ => ?_
  refine le_trans ?_ (Finset.le_sup (f := fun i : X.T.ι => X.chartJetTotal i μ)
    (Finset.mem_univ p.1))
  unfold chartJetTotal
  rw [← sum_extendIdx (X.eqv p)]
  exact Finset.sum_le_sum fun j _ => X.extendIdx_depthOf_le p μ j

/-! ### The piece bound -/

/-- The bound constant of a piece (density and observable bounds still to be supplied). -/
noncomputable def pieceConst (p : X.PIdx) (μ : ℝ) (q : ℕ) : ℝ :=
  coeffBoundConstant (X.hA p) (X.kA p) (X.pieceDepth p μ) (X.T.phaseConst p.1) (X.T.a p.1) μ q *
    2 ^ (∑ j, X.pieceDepth p μ j)

theorem pieceConst_nonneg (p : X.PIdx) (μ : ℝ) (q : ℕ) : 0 ≤ X.pieceConst p μ q :=
  mul_nonneg (coeffBoundConstant_nonneg _ _ _ _ _ _ _) (pow_nonneg (by norm_num) _)

/-- ★ **The piece bound**: the canonical coefficient of the piece amplitude `ρfam · obsfam` is
bounded by the piece constant times the rectangular bounds of the density and of the observable
families. -/
theorem abs_smoothCoeff_amp_le (p : X.PIdx) (μ : ℝ) (q : ℕ) {Mρ Mf : ℝ}
    (s : Base (X.act p.1) (X.T.a p.1))
    (hρ : RectBound (X.ρfam p s) (X.pieceDepth p μ) (X.T.a p.1) Mρ)
    (hf : RectBound (X.obsfam p s) (X.pieceDepth p μ) (X.T.a p.1) Mf) :
    |smoothCoeff (X.amp p s) (X.hA p) (X.kA p) (X.T.phaseConst p.1) (X.T.a p.1) μ q| ≤
      X.pieceConst p μ q * (Mρ * Mf) := by
  have hcongr : smoothCoeff (X.amp p s) (X.hA p) (X.kA p) (X.T.phaseConst p.1) (X.T.a p.1) μ q =
      smoothCoeff (((X.ρfam p).mul (X.obsfam p)) s) (X.hA p) (X.kA p) (X.T.phaseConst p.1)
        (X.T.a p.1) μ q := by
    refine smoothCoeff_congr_box ((X.amp p).smooth s) (((X.ρfam p).mul (X.obsfam p)).smooth s)
      (X.kA_pos p) (X.T.phaseConst_pos p.1) (X.T.a_pos p.1) (fun v hv => ?_) μ q
    rw [SmoothAmplitudeFamily.mul_apply]
    exact X.amp_eq_mul p s fun j => Ioc_subset_Icc_self (hv j (Set.mem_univ j))
  rw [hcongr, SmoothAmplitudeFamily.mul_apply]
  have hmul := RectBound.mul ((X.ρfam p).smooth s) ((X.obsfam p).smooth s) (X.T.a_pos p.1).le
    hρ hf
  have := abs_smoothCoeff_le (β := X.T.phaseConst p.1) (((X.ρfam p).mul (X.obsfam p)).smooth s)
    (X.kA_pos p) (X.T.a_pos p.1) hmul q
  rw [SmoothAmplitudeFamily.mul_apply] at this
  refine this.trans (le_of_eq ?_)
  unfold pieceConst pieceDepth
  ring

/-- The family (base-integrated) bound of a piece. -/
theorem abs_familyCoeff_amp_le (p : X.PIdx) (μ : ℝ) (q : ℕ) {Mρ Mf : ℝ}
    (hρ : ∀ s, RectBound (X.ρfam p s) (X.pieceDepth p μ) (X.T.a p.1) Mρ)
    (hf : ∀ s, RectBound (X.obsfam p s) (X.pieceDepth p μ) (X.T.a p.1) Mf) :
    |familyCoeff (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)) (X.amp p) (X.hA p) (X.kA p)
        (fun _ => X.T.phaseConst p.1) (X.T.a p.1) μ q| ≤
      X.pieceConst p μ q * (Mρ * Mf) *
        (baseMeasure (X.act p.1) (X.T.a p.1) (X.T.h p.1)).real univ := by
  unfold familyCoeff
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs]
  exact X.abs_smoothCoeff_amp_le p μ q s (hρ s) (hf s)

/-- The uniform rectangular bound of the density family of a piece. -/
theorem exists_rectBound_ρfam (p : X.PIdx) (μ : ℝ) :
    ∃ Mρ : ℝ, 0 ≤ Mρ ∧ ∀ s, RectBound (X.ρfam p s) (X.pieceDepth p μ) (X.T.a p.1) Mρ :=
  (X.ρfam p).exists_uniform_rect_bound (X.pieceDepth p μ)

/-- The density bound of a piece. -/
noncomputable def densityBound (p : X.PIdx) (μ : ℝ) : ℝ :=
  Classical.choose (X.exists_rectBound_ρfam p μ)

theorem densityBound_nonneg (p : X.PIdx) (μ : ℝ) : 0 ≤ X.densityBound p μ :=
  (Classical.choose_spec (X.exists_rectBound_ρfam p μ)).1

theorem rectBound_ρfam (p : X.PIdx) (μ : ℝ) (s : Base (X.act p.1) (X.T.a p.1)) :
    RectBound (X.ρfam p s) (X.pieceDepth p μ) (X.T.a p.1) (X.densityBound p μ) :=
  (Classical.choose_spec (X.exists_rectBound_ρfam p μ)).2 s

/-! ### The observable bound through the chart -/

theorem image_box_subset_coreImage (i : X.T.ι) :
    X.T.ψ i '' centeredBox d (X.T.a i) ⊆ X.coreImage :=
  subset_iUnion (fun i => X.T.ψ i '' centeredBox d (X.T.a i)) i

theorem exists_chartConst (i : X.T.ι) (μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ X.engineOrder μ, ∀ y ∈ X.T.ψ i '' centeredBox d (X.T.a i),
        ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      ∀ r ≤ X.engineOrder μ, ∀ u ∈ centeredBox d (X.T.a i),
        ‖iteratedFDeriv ℝ r (f ∘ X.T.ψ i) u‖ ≤ C * M :=
  exists_chart_jet_bound_centeredBox (X.T.V_open i) (X.T.box_subset_V i) (X.contDiffOn_ψ i)
    (X.engineOrder μ)

/-- The chain-rule constant of a chart at the engine order. -/
noncomputable def chartConst (i : X.T.ι) (μ : ℝ) : ℝ := Classical.choose (X.exists_chartConst i μ)

theorem chartConst_nonneg (i : X.T.ι) (μ : ℝ) : 0 ≤ X.chartConst i μ :=
  (Classical.choose_spec (X.exists_chartConst i μ)).1

theorem chartConst_spec (i : X.T.ι) (μ : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {M : ℝ}
    (hM : 0 ≤ M) (hJ : JetBound (X.engineOrder μ) X.coreImage f M) :
    ∀ r ≤ X.engineOrder μ, ∀ u ∈ centeredBox d (X.T.a i),
      ‖iteratedFDeriv ℝ r (f ∘ X.T.ψ i) u‖ ≤ X.chartConst i μ * M :=
  (Classical.choose_spec (X.exists_chartConst i μ)).2 f hf M hM
    fun r hr y hy => hJ r hr y (X.image_box_subset_coreImage i hy)

/-- ★ **The rectangular bound of the observable family** from a Fréchet jet bound of the
observable on the core image. -/
theorem rectBound_obsfam (p : X.PIdx) (μ : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.engineOrder μ) X.coreImage X.obs M) (s : Base (X.act p.1) (X.T.a p.1)) :
    RectBound (X.obsfam p s) (X.pieceDepth p μ) (X.T.a p.1) (X.chartConst p.1 μ * M) := by
  intro m hm v hv
  have hvbox : ∀ j, v j ∈ Icc 0 (X.T.a p.1) := hv
  have hu : X.Tm p s v ∈ centeredBox d (X.T.a p.1) := X.Tm_mem_box p s hvbox
  have huV : X.Tm p s v ∈ X.T.V p.1 := X.T.box_subset_V p.1 hu
  change |pdMulti m (List.finRange (X.da p))
    (fun v => X.obsExt p.1 (affineMap (X.eqv p) p.2 (X.sc p s) v)) v| ≤ _
  rw [abs_pdMulti_comp_affineMap_finRange (X.eqv p) p.2 (X.sc p s) (X.contDiff_obsExt p.1) m v]
  change |pdMulti (extendIdx (X.eqv p) m) (List.finRange d) (X.obsExt p.1) (X.Tm p s v)| ≤ _
  have hψ : ContDiffOn ℝ ∞ (X.obs ∘ X.T.ψ p.1) (X.T.V p.1) :=
    X.obs_smooth.comp_contDiffOn (X.contDiffOn_ψ p.1)
  rw [pdMulti_eqOn_centeredBox (X.T.V_open p.1) (X.T.a_pos p.1) (X.T.box_subset_V p.1)
    (X.contDiff_obsExt p.1).contDiffOn hψ (fun u hu => X.obsExt_eq p.1 hu) _ _ hu]
  refine (abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem (X.T.V_open p.1) hψ _ huV).trans ?_
  refine X.chartConst_spec p.1 μ X.obs_smooth hM hJ _ ?_ _ hu
  rw [sum_extendIdx]
  exact (Finset.sum_le_sum fun j _ => hm j).trans (X.sum_pieceDepth_le_engineOrder p μ)

/-! ### The global bound -/

/-- ★ **The jet-bound constant** of the bridge at `(μ, q)`. -/
noncomputable def jetConst (μ : ℝ) (q : ℕ) : ℝ :=
  ∑ I : Fin (Fintype.card X.PIdx), X.pieceConst (X.en I) μ q *
    (X.densityBound (X.en I) μ * X.chartConst (X.en I).1 μ) *
      (baseMeasure (X.act (X.en I).1) (X.T.a (X.en I).1) (X.T.h (X.en I).1)).real univ

theorem jetConst_nonneg (μ : ℝ) (q : ℕ) : 0 ≤ X.jetConst μ q :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (X.pieceConst_nonneg _ μ q)
    (mul_nonneg (X.densityBound_nonneg _ μ) (X.chartConst_nonneg _ μ))) measureReal_nonneg

/-- ★★★ **The finite-order bound on the intrinsic coefficients**: `|coeff μ q| ≤ jetConst · M`
whenever `‖D^r obs‖ ≤ M` on the core image for all `r ≤ engineOrder μ`. -/
theorem abs_coeff_le (μ : ℝ) (q : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hJ : JetBound (X.engineOrder μ) X.coreImage X.obs M) :
    |X.decomp.coeff μ q| ≤ X.jetConst μ q * M := by
  unfold jetConst
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  refine (X.abs_familyCoeff_amp_le (X.en I) μ q (X.rectBound_ρfam (X.en I) μ)
    (X.rectBound_obsfam (X.en I) μ hM hJ)).trans (le_of_eq ?_)
  ring

/-- ★★★ **The finite-order bound on the observable coefficient functional**. -/
theorem abs_observableCoeff_le (μ : ℝ) (q : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : 0 ≤ M) (hJ : JetBound (X.engineOrder μ) X.coreImage f M) :
    |X.observableCoeff μ q f hf| ≤ X.jetConst μ q * M :=
  (X.withObs f hf).abs_coeff_le μ q hM hJ

end BridgeInputs

end SmoothEngine

end Grammar
