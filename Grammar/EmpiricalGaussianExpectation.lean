/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFieldLimit
import Grammar.GaussianFluctuationScalar

/-!
# The expected limiting coefficient for a Gaussian branch field

Rank 5a of the empirical programme. For a random continuous branch tuple `G` whose one-point laws
are all `N(0, v)` with `v < 2` (no independence across points or pieces is assumed), the summed
face limit `T(G)` is integrable and

  `E T(G) = (1 − v/2)^{−λ} · T(0)`,

where `T(0)` is the population face limit (the zero-field value). The proof integrates the
Gaussian one-point identity `E S_λ(G(z)) = Γ(λ)(1 − v/2)^{−λ}` against the face weights
(`integral_integral_fluctuation_of_gaussian_marginals`), face by face. This is a statement about
the expectation of the *limit* `T(G)` of rank 4; it is not an annealed limit theorem for
`E[Z^{emp}_n/s_n]`, which would need uniform integrability. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal ContDiff Manifold
open Monomialize.VolumeScaling Monomialize.Transport Monomialize.Manifold
open Grammar.NormalCrossing Grammar.NormalCrossing.EvenChartBoxDepth

namespace Grammar

/-! ### Integrability of the residue weight at a chart-leading pair -/

/-- On the box, `residueWeight h k l w = ∏ wᵢ^{hᵢ − 2kᵢl}`. -/
theorem SmoothEngine.residueWeight_eq_prod_rpow {ι : Type*} [Fintype ι] (h k : ι → ℕ) (l : ℝ)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    SmoothEngine.residueWeight h k l w = ∏ i, w i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l) := by
  unfold SmoothEngine.residueWeight SmoothEngine.mono
  rw [← Real.finsetProd_rpow _ _ fun i _ => pow_nonneg (hw i).le _, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (w i) (2 * k i), ← Real.rpow_mul (hw i).le,
    ← Real.rpow_add (hw i)]
  congr 1
  push_cast
  ring

/-- The residue weight is integrable on the box when every exponent exceeds `−1`, i.e. when
`2kᵢl < hᵢ + 1` for all `i`. -/
theorem SmoothEngine.integrableOn_residueWeight_box {ι : Type*} [Fintype ι] (h k : ι → ℕ) (l : ℝ)
    (hlt : ∀ i, 2 * (k i : ℝ) * l < h i + 1) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (SmoothEngine.residueWeight h k l) (SmoothEngine.box ι b) := by
  have hc : ∀ i, (-1 : ℝ) < (h i : ℝ) - 2 * (k i : ℝ) * l := fun i => by linarith [hlt i]
  have h0 := integrableOn_prod_rpow_mul_log_pow hc (fun _ => 0) 0 hb
  simp only [pow_zero, mul_one] at h0
  exact h0.congr_fun (fun w hw => (SmoothEngine.residueWeight_eq_prod_rpow h k l fun i =>
    SmoothEngine.pos_of_mem_box hw i).symm) (SmoothEngine.measurableSet_box b)

/-- Off the resonant set, at a chart-leading pair realising the multiplicity, the ratio exceeds
`λ` strictly: `2kᵢλ < hᵢ + 1`. -/
theorem two_mul_lt_of_not_mem_resSet {d : ℕ} {h k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {lam : ℝ}
    (hmin : ∀ i, lam ≤ ratioExp h k i) {i : Fin d} (hi : i ∉ resSet h k lam) :
    2 * (k i : ℝ) * lam < h i + 1 := by
  have hne : ratioExp h k i ≠ lam := fun heq => hi (mem_resSet.2 heq)
  have hlt : lam < ratioExp h k i := lt_of_le_of_ne (hmin i) (Ne.symm hne)
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
    have := hk i
    positivity
  unfold ratioExp at hlt
  rw [lt_div_iff₀ hk'] at hlt
  linarith

namespace SmoothEngine

namespace ResolvedData

variable {d : ℕ} (Ξ : ResolvedData d) (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior)

/-! ### The face weight and face measure of a piece -/

/-- The free-coordinate parameter space of the resonant face of a piece. -/
abbrev FaceDom (p : (Ξ.X Y).PIdx) (lam : ℝ) : Type :=
  Base ((Ξ.X Y).act p.1) (Y.T.a p.1) ×
    ({i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} → ℝ)

/-- The face measure: base measure times Lebesgue measure on the free box. -/
noncomputable def faceProdMeasure (p : (Ξ.X Y).PIdx) (lam : ℝ) : Measure (Ξ.FaceDom Y p lam) :=
  (Ξ.piecePresentation Y p).ν.prod (volume.restrict
    (SmoothEngine.box {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} (Y.T.a p.1)))

instance (p : (Ξ.X Y).PIdx) (lam : ℝ) : SFinite (Ξ.faceProdMeasure Y p lam) := by
  unfold faceProdMeasure
  exact Measure.prod.instSFinite

/-- The glued face point `(s, glue J 0 w)` in the parameter space of the piece. -/
noncomputable def facePoint (p : (Ξ.X Y).PIdx) (lam : ℝ) (z : Ξ.FaceDom Y p lam) :
    Base ((Ξ.X Y).act p.1) (Y.T.a p.1) × (Fin ((Ξ.X Y).da p) → ℝ) :=
  (z.1, glue (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) 0 z.2)

theorem continuous_facePoint (p : (Ξ.X Y).PIdx) (lam : ℝ) : Continuous (Ξ.facePoint Y p lam) :=
  continuous_fst.prodMk
    ((SmoothEngine.continuous_glue_zero (J := resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam)).comp
      continuous_snd)

/-- The face weight `c_p · amp(s, glue J 0 w) · residueWeight(w)` of a piece. -/
noncomputable def faceWeight (p : (Ξ.X Y).PIdx) (lam : ℝ) (m : ℕ) (z : Ξ.FaceDom Y p lam) : ℝ :=
  (1 / (((m - 1).factorial : ℝ) *
      ∏ i ∈ resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam, (2 * ((Ξ.X Y).kA p i : ℝ)))) *
    (Ξ.amp Y p).amp (Ξ.facePoint Y p lam z).1 (Ξ.facePoint Y p lam z).2 *
    SmoothEngine.residueWeight
      (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} => (Ξ.X Y).hA p i)
      (fun i => (Ξ.X Y).kA p i) lam z.2

theorem measurable_faceWeight (p : (Ξ.X Y).PIdx) (lam : ℝ) (m : ℕ) :
    Measurable (Ξ.faceWeight Y p lam m) := by
  unfold faceWeight
  have h1 : Measurable fun z : Ξ.FaceDom Y p lam =>
      (Ξ.amp Y p).amp (Ξ.facePoint Y p lam z).1 (Ξ.facePoint Y p lam z).2 :=
    (Ξ.continuous_amp_uncurry Y p).measurable.comp (Ξ.continuous_facePoint Y p lam).measurable
  have h2 : Measurable fun z : Ξ.FaceDom Y p lam => SmoothEngine.residueWeight
      (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} => (Ξ.X Y).hA p i)
      (fun i => (Ξ.X Y).kA p i) lam z.2 := by
    unfold SmoothEngine.residueWeight
    have hm1 : Measurable fun z : Ξ.FaceDom Y p lam => SmoothEngine.mono
        (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} => (Ξ.X Y).hA p i) z.2 :=
      (SmoothEngine.continuous_mono _).measurable.comp measurable_snd
    have hm2 : Measurable fun z : Ξ.FaceDom Y p lam => SmoothEngine.mono
        (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} =>
          2 * (Ξ.X Y).kA p i) z.2 :=
      (SmoothEngine.continuous_mono _).measurable.comp measurable_snd
    exact hm1.mul (hm2.pow_const _)
  exact (measurable_const.mul h1).mul h2

/-- The face weight is integrable at a chart-leading pair. -/
theorem integrable_faceWeight (p : (Ξ.X Y).PIdx) {lam : ℝ} {m : ℕ}
    (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    Integrable (Ξ.faceWeight Y p lam m) (Ξ.faceProdMeasure Y p lam) := by
  obtain ⟨A, hA⟩ := Ξ.exists_amp_bound Y p
  have hb : 0 < Y.T.a p.1 := Y.T.a_pos p.1
  have hw : IntegrableOn (SmoothEngine.residueWeight
      (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} => (Ξ.X Y).hA p i)
      (fun i => (Ξ.X Y).kA p i) lam)
      (SmoothEngine.box {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} (Y.T.a p.1)) :=
    SmoothEngine.integrableOn_residueWeight_box _ _ lam
      (fun i => two_mul_lt_of_not_mem_resSet ((Ξ.X Y).kA_pos p) hlead.1 i.2) hb.le
  set c : ℝ := 1 / (((m - 1).factorial : ℝ) *
      ∏ i ∈ resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam, (2 * ((Ξ.X Y).kA p i : ℝ))) with hc
  have hdom : Integrable (fun z : Ξ.FaceDom Y p lam => |c| * |A| *
      |SmoothEngine.residueWeight
        (fun i : {i // ¬ inJ (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) i} => (Ξ.X Y).hA p i)
        (fun i => (Ξ.X Y).kA p i) lam z.2|) (Ξ.faceProdMeasure Y p lam) := by
    unfold faceProdMeasure
    exact (hw.abs.comp_snd _).const_mul _
  refine hdom.mono' (Ξ.measurable_faceWeight Y p lam m).aestronglyMeasurable ?_
  unfold faceProdMeasure
  rw [← Measure.restrict_univ (μ := (Ξ.piecePresentation Y p).ν), Measure.prod_restrict,
    ae_restrict_iff' (MeasurableSet.univ.prod (SmoothEngine.measurableSet_box _))]
  refine Eventually.of_forall fun z hz => ?_
  have hw' : z.2 ∈ SmoothEngine.box _ (Y.T.a p.1) := hz.2
  have hglue : glue (resSet ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam) 0 z.2 ∈
      closedBox ((Ξ.X Y).da p) (Y.T.a p.1) :=
    glue_zero_mem_closedBox_of_mem_Icc hb.le fun i _ => Ioc_subset_Icc_self (hw' i (Set.mem_univ i))
  have hamp : |(Ξ.amp Y p).amp (Ξ.facePoint Y p lam z).1 (Ξ.facePoint Y p lam z).2| ≤ |A| :=
    (hA _ _ hglue).trans (le_abs_self _)
  unfold faceWeight
  rw [Real.norm_eq_abs, abs_mul, abs_mul, ← hc]
  gcongr

/-! ### The face integral of a tuple as a product integral -/

/-- The field of a tuple at the glued face point. -/
noncomputable def faceField (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (lam : ℝ)
    (z : Ξ.FaceDom Y p lam) : ℝ :=
  Ξ.tupleField Y f p (Ξ.facePoint Y p lam z)

theorem continuous_faceField (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (lam : ℝ) :
    Continuous (Ξ.faceField Y f p lam) :=
  (Ξ.continuous_tupleField Y f p).comp (Ξ.continuous_facePoint Y p lam)

theorem abs_faceField_le (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) (lam : ℝ)
    (z : Ξ.FaceDom Y p lam) : |Ξ.faceField Y f p lam z| ≤ ‖f‖ :=
  Ξ.abs_tupleField_le Y f p _

theorem faceField_zero (p : (Ξ.X Y).PIdx) (lam : ℝ) (z : Ξ.FaceDom Y p lam) :
    Ξ.faceField Y 0 p lam z = 0 := by
  unfold faceField tupleField
  simp

/-- The face integrand of a tuple is integrable on the face measure. -/
theorem integrable_faceWeight_mul_fluctuation (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {lam : ℝ}
    (hlam : 0 < lam) {m : ℕ} (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    Integrable (fun z => Ξ.faceWeight Y p lam m z * fluctuation 1 lam (Ξ.faceField Y f p lam z))
      (Ξ.faceProdMeasure Y p lam) := by
  refine ((Ξ.integrable_faceWeight Y p hlead).abs.mul_const (fluctuation 1 lam ‖f‖)).mono'
    ((Ξ.measurable_faceWeight Y p lam m).aestronglyMeasurable.mul
      ((continuous_fluctuation 1 lam one_pos hlam).comp
        (Ξ.continuous_faceField Y f p lam)).measurable.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (fluctuation_pos 1 lam _ one_pos hlam)]
  exact mul_le_mul_of_nonneg_left
    (fluctuation_mono_of_abs_le 1 lam one_pos hlam (Ξ.abs_faceField_le Y f p lam z))
    (abs_nonneg _)

/-- **The face limit of a piece as a product integral**: when the piece realises the multiplicity,
`∫_{Base} boxFaceLimit(f_p(s,·), amp s) dν(s) = ∫ faceWeight · S_λ(faceField f) d(ν ⊗ vol|box)`;
otherwise it is `0`. -/
theorem integral_tupleFaceLimit_eq (f : Ξ.BranchTuple Y) (p : (Ξ.X Y).PIdx) {lam : ℝ}
    (hlam : 0 < lam) {m : ℕ} (hlead : BoxLeading ((Ξ.X Y).hA p) ((Ξ.X Y).kA p) lam m) :
    ∫ s, Ξ.tupleFaceLimit Y f p lam m s ∂(Ξ.piecePresentation Y p).ν =
      if multCount (ratioExp ((Ξ.X Y).hA p) ((Ξ.X Y).kA p)) lam = m then
        ∫ z, Ξ.faceWeight Y p lam m z * fluctuation 1 lam (Ξ.faceField Y f p lam z)
          ∂(Ξ.faceProdMeasure Y p lam)
      else 0 := by
  unfold tupleFaceLimit boxFaceLimit
  split_ifs with hmc
  · unfold faceFunctional
    have hint := Ξ.integrable_faceWeight_mul_fluctuation Y f p hlam hlead
    unfold faceProdMeasure at hint ⊢
    rw [integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (SmoothEngine.measurableSet_box _) fun w _ => ?_
    simp only [faceWeight, faceField, facePoint, hmc]
    ring
  · simp

/-! ### The expected face limit for a Gaussian branch field -/

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem measurable_faceField_uncurry {G : Ω' → Ξ.BranchTuple Y} (hG : Measurable G)
    (p : (Ξ.X Y).PIdx) (lam : ℝ) :
    Measurable fun q : Ω' × Ξ.FaceDom Y p lam => Ξ.faceField Y (G q.1) p lam q.2 := by
  have heval : Continuous fun r : Ξ.BranchTuple Y × Ξ.PieceDom Y p => r.1 p r.2 := by fun_prop
  have hpt : Continuous fun z : Ξ.FaceDom Y p lam =>
      ((Ξ.facePoint Y p lam z).1, (⟨clampBox (Y.T.a p.1) (Ξ.facePoint Y p lam z).2,
        clampBox_mem_closedBox (Y.T.a_pos p.1).le _⟩ : ↥(closedBox ((Ξ.X Y).da p) (Y.T.a p.1)))) :=
    (continuous_fst.comp (Ξ.continuous_facePoint Y p lam)).prodMk
      (((continuous_clampBox _).comp
        (continuous_snd.comp (Ξ.continuous_facePoint Y p lam))).subtype_mk _)
  exact heval.measurable.comp ((hG.comp measurable_fst).prodMk (hpt.measurable.comp measurable_snd))

omit [IsProbabilityMeasure P'] in
/-- The one-point law of the face field is the one-point law of the tuple. -/
theorem map_faceField_eq {G : Ω' → Ξ.BranchTuple Y} {v : ℝ≥0}
    (hlaw : ∀ (p : (Ξ.X Y).PIdx) (z : Ξ.PieceDom Y p),
      P'.map (fun w => G w p z) = gaussianReal 0 v) (p : (Ξ.X Y).PIdx) (lam : ℝ)
    (z : Ξ.FaceDom Y p lam) :
    P'.map (fun w => Ξ.faceField Y (G w) p lam z) = gaussianReal 0 v :=
  hlaw p _

/-- ★★★ **The expected limiting coefficient for a Gaussian branch field**: if every one-point law
of the random tuple `G` is `N(0, v)` with `v < 2`, then `T(G)` is integrable and
`E T(G) = (1 − v/2)^{−λ} · T(0)`, `T(0)` the population face limit. -/
theorem integral_tupleLimit_gaussian {lam : ℝ} (hlam : 0 < lam) {m : ℕ}
    (hlead : Ξ.ChartLeading Y lam m) {G : Ω' → Ξ.BranchTuple Y} (hG : Measurable G) {v : ℝ≥0}
    (hv : (v : ℝ) < 2)
    (hlaw : ∀ (p : (Ξ.X Y).PIdx) (z : Ξ.PieceDom Y p),
      P'.map (fun w => G w p z) = gaussianReal 0 v) :
    Integrable (fun w => Ξ.tupleLimit Y (G w) lam m) P' ∧
    ∫ w, Ξ.tupleLimit Y (G w) lam m ∂P' =
      (1 - (v : ℝ) / 2) ^ (-lam) * Ξ.tupleLimit Y 0 lam m := by
  have hΓ : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  -- the piece functionals
  have hpiece : ∀ (p : (Ξ.X Y).PIdx),
      Integrable (fun w => ∫ s, Ξ.tupleFaceLimit Y (G w) p lam m s ∂(Ξ.piecePresentation Y p).ν)
        P' ∧
      ∫ w, ∫ s, Ξ.tupleFaceLimit Y (G w) p lam m s ∂(Ξ.piecePresentation Y p).ν ∂P' =
        (1 - (v : ℝ) / 2) ^ (-lam) *
          ∫ s, Ξ.tupleFaceLimit Y 0 p lam m s ∂(Ξ.piecePresentation Y p).ν := by
    intro p
    simp_rw [Ξ.integral_tupleFaceLimit_eq Y _ p hlam (hlead p)]
    split_ifs with hmc
    · have hfam := integral_integral_fluctuation_of_gaussian_marginals (P := P')
        (ρ := Ξ.faceProdMeasure Y p lam) (Ξ.integrable_faceWeight Y p (hlead p))
        (X := fun q : Ω' × Ξ.FaceDom Y p lam => Ξ.faceField Y (G q.1) p lam q.2)
        (Ξ.measurable_faceField_uncurry Y hG p lam) (v := v)
        (fun z => Ξ.map_faceField_eq Y hlaw p lam z) lam hlam hv
      refine ⟨hfam.1.integral_prod_left, ?_⟩
      rw [hfam.2]
      have hzero : ∫ z, Ξ.faceWeight Y p lam m z * fluctuation 1 lam (Ξ.faceField Y 0 p lam z)
          ∂(Ξ.faceProdMeasure Y p lam) = Real.Gamma lam * ∫ z, Ξ.faceWeight Y p lam m z
            ∂(Ξ.faceProdMeasure Y p lam) := by
        simp_rw [Ξ.faceField_zero, fluctuation_zero 1 lam one_pos hlam, Real.one_rpow, one_mul]
        rw [integral_mul_const, mul_comm]
      rw [hzero]
      unfold gaussianFluctConst
      ring
    · simp
  refine ⟨?_, ?_⟩
  · unfold tupleLimit
    exact integrable_finsetSum _ fun p _ => (hpiece p).1
  · unfold tupleLimit
    rw [integral_finsetSum _ fun p _ => (hpiece p).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => (hpiece p).2

end ResolvedData

end SmoothEngine

end Grammar
