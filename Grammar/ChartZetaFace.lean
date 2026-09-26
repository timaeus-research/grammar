/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ChartZetaStrip
import Grammar.SmoothGeneralDepth

/-!
# The zeta face-term identity and the subset formula (polar-distribution programme, unit 3)

Consult #167 (A1, expression (3); `tide-log/plan_polar_distribution.md`). The Laplace-side face
construction of the smooth engine (`sum_faceOp`, `faceTerm_integral`, `integral_eq_sum_faceIntegral`)
is mirrored on the zeta side. The inner monomial integral is explicit,
  `∫_{(0,1]^ι} ∏ uᵢ^{eᵢ − 2kᵢ s} du = ∏ᵢ 1/(eᵢ + 1 − 2kᵢ s)`   (`integral_box_cpowWeight`),
and the face term of the Taylor-subtracted amplitude `faceOp p J F` splits into the inner
rational factor times the complementary chart zeta functional of the flat face amplitude
(★ `zeta_faceTerm_integral`). Summing over the faces gives the **subset formula on the strip**:
  `chartZeta F h k s = Σ_{(J,m) ∈ faceIndex p} faceW J m · ∏_{i∈J} (mᵢ+hᵢ+1−2kᵢs)⁻¹ ·
     chartZeta (faceAmp p J F m) h_{Jᶜ} k_{Jᶜ} s`   (★★ `chartZeta_eq_sum_faces`),
for `s` in the strip `2kᵢ Re s < hᵢ + 1`. The right side is defined for all `s` and, by the flat
bound on `faceAmp` and unit 2, meromorphic on the enlarged strip `2kᵢ Re s < pᵢ + hᵢ + 1`, which is
the continuation of unit 4. Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset
open scoped ContDiff

namespace Grammar

open SmoothEngine

section Inner

variable {ι : Type*} [Fintype ι]

/-- One coordinate: `∫_0^1 t^r dt = 1/(r+1)` for `Re r > −1`. -/
theorem integral_Ioc_cpow {r : ℂ} (hr : -1 < r.re) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr)]
  have hr1 : r + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow hr1, sub_zero]

/-- The inner monomial zeta integral: `∫_{(0,1]^ι} ∏ uᵢ^{eᵢ−2kᵢs} du = ∏ᵢ 1/(eᵢ+1−2kᵢs)`. -/
theorem integral_box_cpowWeight (e k : ι → ℕ) {s : ℂ} (hs : ZetaStrip e k s) :
    ∫ u in SmoothEngine.box ι 1, cpowWeight e k s u =
      ∏ i, 1 / ((e i : ℂ) - 2 * (k i : ℂ) * s + 1) := by
  have hpt : ∀ u ∈ SmoothEngine.box ι 1, cpowWeight e k s u =
      ∏ i, ((u i : ℂ) ^ ((e i : ℂ) - 2 * (k i : ℂ) * s)) := fun u hu =>
    cpowWeight_eq_prod_cpow e k s fun i => SmoothEngine.pos_of_mem_box hu i
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) hpt]
  have hbox : SmoothEngine.box ι 1 = Set.pi univ fun _ : ι => Ioc (0 : ℝ) 1 := rfl
  rw [hbox, MeasureTheory.volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i (t : ℝ) => (t : ℂ) ^ ((e i : ℂ) - 2 * (k i : ℂ) * s))]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine integral_Ioc_cpow ?_
  have := hs i
  have hre : ((e i : ℂ) - 2 * (k i : ℂ) * s).re = (e i : ℝ) - 2 * (k i : ℝ) * s.re := by
    simp [Complex.mul_re, Complex.sub_re]
  rw [hre]
  linarith

/-- The monomial weight absorbs a natural monomial: `mono m u · weight(h) = weight(m+h)`. -/
theorem mono_mul_cpowWeight (m h k : ι → ℕ) (s : ℂ) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    (mono m u : ℂ) * cpowWeight h k s u = cpowWeight (fun i => m i + h i) k s u := by
  unfold cpowWeight
  have hm : (mono m u : ℂ) = Complex.exp (logSum m u : ℂ) := by
    have : mono m u = Real.exp (logSum m u) := by
      unfold mono logSum
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.exp_nat_mul, Real.exp_log (hu i)]
    rw [this, Complex.ofReal_exp]
  rw [hm, ← Complex.exp_add]
  congr 1
  have : logSum (fun i => m i + h i) u = logSum m u + logSum h u := by
    unfold logSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [this]
  push_cast
  ring

end Inner

section Face

variable {d : ℕ} (p : Fin d → ℕ) (J : Finset (Fin d))

/-- The logarithmic sum splits along a face. -/
theorem logSum_glue (a : Fin d → ℕ) (u : {i // inJ J i} → ℝ) (w : {i // ¬ inJ J i} → ℝ) :
    logSum a (glue J u w) =
      logSum (fun i : {i // inJ J i} => a i) u + logSum (fun i : {i // ¬ inJ J i} => a i) w := by
  unfold logSum
  rw [← Fintype.sum_subtype_add_sum_subtype (inJ J)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by rw [glue_apply_subtype]
  · exact Finset.sum_congr rfl fun i _ => by rw [glue_apply_subtype']

/-- The complex weight splits along a face. -/
theorem cpowWeight_glue (h k : Fin d → ℕ) (s : ℂ) (u : {i // inJ J i} → ℝ)
    (w : {i // ¬ inJ J i} → ℝ) :
    cpowWeight h k s (glue J u w) =
      cpowWeight (fun i : {i // inJ J i} => h i) (fun i => k i) s u *
        cpowWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s w := by
  unfold cpowWeight
  rw [logSum_glue, logSum_glue, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The complex-valued box split along a face (the codomain-`ℂ` form of `integral_box_split`). -/
theorem integral_box_split_complex (b : ℝ) (f : (Fin d → ℝ) → ℂ)
    (hf : IntegrableOn f (SmoothEngine.box (Fin d) b)) :
    ∫ v in SmoothEngine.box (Fin d) b, f v =
      ∫ w in SmoothEngine.box {i // ¬ inJ J i} b,
        ∫ u in SmoothEngine.box {i // inJ J i} b, f (glue J u w) := by
  have hmp := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) (inJ J)).symm
  have hemb := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
    (inJ J)).symm.measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb f (SmoothEngine.box (Fin d) b)
  rw [box_split_preimage] at h
  rw [← h]
  have hint' : IntegrableOn (f ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
      (inJ J)).symm)
      (SmoothEngine.box {i // inJ J i} b ×ˢ SmoothEngine.box {i // ¬ inJ J i} b) := by
    rw [← box_split_preimage]
    exact (hmp.integrableOn_comp_preimage hemb).2 hf
  have hint : Integrable (f ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ)
      (inJ J)).symm) ((volume.restrict (SmoothEngine.box {i // inJ J i} b)).prod
        (volume.restrict (SmoothEngine.box {i // ¬ inJ J i} b))) := by
    rw [Measure.prod_restrict]
    exact hint'
  have h2 := integral_prod_symm _ hint
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h2
  simp only [Function.comp_def] at h2
  exact h2

variable {F : (Fin d → ℝ) → ℝ}

/-- ★ **The zeta face-term identity**: on the strip, the face-`J` term of the subset formula is
the sum over the face multi-indices of the inner rational factor times the complementary chart
zeta functional of the flat face amplitude. -/
theorem zeta_faceTerm_integral (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ}
    (hs : ZetaStrip h k s) :
    ∫ v in SmoothEngine.box (Fin d) 1,
        ((SmoothEngine.faceOp p J (List.finRange d) F v : ℝ) : ℂ) * cpowWeight h k s v =
      ∑ m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J),
        ((∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        (∏ i : {i // inJ J i},
          1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) *
        chartZeta (SmoothEngine.faceAmp p J F m) (fun i : {i // ¬ inJ J i} => h i)
          (fun i => k i) s := by
  have hdisj : ∀ i ∈ SmoothEngine.lJ J, i ∉ SmoothEngine.lK J := fun i hi h' =>
    (mem_lK J).1 h' ((mem_lJ J).1 hi)
  set S : (Fin d → ℕ) → (Fin d → ℝ) → ℝ := fun m v =>
    SmoothEngine.tayMono m v * SmoothEngine.remList p (SmoothEngine.lK J)
      (SmoothEngine.pdMulti m (SmoothEngine.lJ J) F) (SmoothEngine.zeroL (SmoothEngine.lJ J) v)
    with hS
  have hSc : ∀ m, Continuous (S m) := fun m => by
    simp only [hS]
    exact (continuous_tayMono m).mul
      ((contDiff_remList p (contDiff_pdMulti hF m _) _).continuous.comp (continuous_zeroL _))
  have hpt : ∀ v, SmoothEngine.faceOp p J (List.finRange d) F v =
      ∑ m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J), S m v := by
    intro v
    rw [faceOp_finRange_eq p J hF, tayList_eq_sum p (contDiff_remList p hF _) (nodup_lJ J)]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hS]
    rw [pdMulti_remList p hF m hdisj]
  have hpt' : ∀ v, ((SmoothEngine.faceOp p J (List.finRange d) F v : ℝ) : ℂ) * cpowWeight h k s v =
      ∑ m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J), (S m v : ℂ) * cpowWeight h k s v := fun v => by
    rw [hpt v]; push_cast; rw [Finset.sum_mul]
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v _ => hpt' v,
    integral_finsetSum _ fun m _ => integrableOn_chartZeta_integrand (hSc m) h k hs]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_box_split_complex J 1 _ (integrableOn_chartZeta_integrand (hSc m) h k hs)]
  have hsJ : ZetaStrip (fun i : {i // inJ J i} => m i + h i) (fun i => k i) s := fun i => by
    have := hs i
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) (m i)]
  have hinner : ∀ w : {i // ¬ inJ J i} → ℝ,
      ∫ u in SmoothEngine.box {i // inJ J i} 1, (S m (glue J u w) : ℂ) *
        cpowWeight h k s (glue J u w) =
      (((∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        (∏ i : {i // inJ J i},
          1 / (((m i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1))) *
        (((SmoothEngine.faceAmp p J F m w : ℝ) : ℂ) *
          cpowWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s w) := by
    intro w
    have hpt : ∀ u ∈ SmoothEngine.box {i // inJ J i} 1,
        (S m (glue J u w) : ℂ) * cpowWeight h k s (glue J u w) =
        ((((∏ i : {i // inJ J i}, ((m i).factorial : ℝ)⁻¹ : ℝ) : ℂ) *
          (((SmoothEngine.faceAmp p J F m w : ℝ) : ℂ) *
            cpowWeight (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) s w)) *
          cpowWeight (fun i : {i // inJ J i} => m i + h i) (fun i => k i) s u) := by
      intro u hu
      have hu' : ∀ i, 0 < u i := fun i => SmoothEngine.pos_of_mem_box hu i
      simp only [hS]
      rw [tayMono_glue p J hm, zeroL_lJ_glue, cpowWeight_glue,
        ← mono_mul_cpowWeight (fun i : {i // inJ J i} => m i) (fun i => h i) (fun i => k i) s hu']
      unfold SmoothEngine.faceAmp
      push_cast
      ring
    rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box (ι := {i // inJ J i}) 1) hpt,
      MeasureTheory.integral_const_mul, integral_box_cpowWeight _ _ hsJ]
    ring
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box (ι := {i // ¬ inJ J i}) 1)
    fun w _ => hinner w, MeasureTheory.integral_const_mul]
  rfl

/-- ★★ **The subset formula on the strip**: the chart zeta functional is the sum over the faces
of the inner rational factors times the complementary chart zeta functionals of the flat face
amplitudes. -/
theorem chartZeta_eq_sum_faces (hF : ContDiff ℝ ∞ F) (h k : Fin d → ℕ) {s : ℂ}
    (hs : ZetaStrip h k s) :
    chartZeta F h k s =
      ∑ x ∈ SmoothEngine.faceIndex p, ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) *
        (∏ i : {i // inJ x.1 i},
          1 / (((x.2 i.1 + h i.1 : ℕ) : ℂ) - 2 * ((k i.1 : ℕ) : ℂ) * s + 1)) *
        chartZeta (SmoothEngine.faceAmp p x.1 F x.2) (fun i : {i // ¬ inJ x.1 i} => h i)
          (fun i => k i) s := by
  have hpt : ∀ v : Fin d → ℝ, (F v : ℂ) * cpowWeight h k s v =
      ∑ J ∈ (univ : Finset (Finset (Fin d))),
        ((SmoothEngine.faceOp p J (List.finRange d) F v : ℝ) : ℂ) * cpowWeight h k s v := by
    intro v
    rw [← Finset.sum_mul, ← Finset.powerset_univ, ← List.toFinset_finRange]
    congr 1
    exact_mod_cast sum_faceOp p (List.nodup_finRange d) F v
  have hint : ∀ J ∈ (univ : Finset (Finset (Fin d))), IntegrableOn
      (fun v => ((SmoothEngine.faceOp p J (List.finRange d) F v : ℝ) : ℂ) * cpowWeight h k s v)
      (SmoothEngine.box (Fin d) 1) := fun J _ =>
    integrableOn_chartZeta_integrand (contDiff_faceOp p hF J _).continuous h k hs
  unfold chartZeta
  rw [setIntegral_congr_fun (SmoothEngine.measurableSet_box 1) fun v _ => hpt v,
    integral_finsetSum _ hint, SmoothEngine.faceIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [zeta_faceTerm_integral p J hF h k hs]
  rfl

end Face

end Grammar
