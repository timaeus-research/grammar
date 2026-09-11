/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.AdaptedPieceDensity
import Grammar.PhaseUniform
import Grammar.BoxDilation

/-!
# The constant-unit box kernel over a compact base

The first version of module 2 of the adapted-density programme
(`tide-log/gpt6_bigpicture_v75.md`): the **constant-unit box kernel**
`L_N(z) = ∫_{(0,b]^{n+1}} A(z,u) ∏ u_i^{h_i} e^{-βN ∏ u_i^{2k_i}} du`
on a PRESCRIBED cube `(0,b]^{n+1}` (the library's normal form: phase unit the constant `β`,
integer normal exponents), with a jointly continuous amplitude `A(z,u)` depending on a tangential
parameter `z`. Three statements:

* the **pointwise certificate** `HasLeadingTerm (L_· z) (faceCoeff z) λ (m−1)` for every `z`, with
  the explicit face coefficient `b^{Σh+n+1} (b^{2Σk})^{−λ} · amplitudeCoeff(A(z, b·))`
  (`hasLeadingTerm_boxKernel`, from the prescribed-box theorem `population_box_tendsto`);
* the **eventual normalised bound uniform on a compact base** `T`:
  `∃ C, ∀ᶠ N, ∀ z ∈ T, |L_N(z)| / (N^{−λ}(log N)^{m−1}) ≤ C`
  (`eventually_abs_boxKernel_div_le`, from the uniform convergence of the normalised chart
  integral on compact input sets, `tendstoUniformlyOn_normChart`, transported through the
  dilation `origPhaseIntegral_dilation` and the square-root reparametrisation of the chart
  variable);
* the **integrated certificate** against an integrable base weight `β_w` on `T`:
  `∫_T β_w(z) L_N(z) dz ⟶ (∫_T β_w(z) faceCoeff(z) dz) · N^{−λ}(log N)^{m−1}`
  (`hasLeadingTerm_integral_boxKernel`, via CCXXVII).

Non-claims: the phase unit is the constant `β` (a non-constant unit is handled by the library only
through the strip normalisation, whose region is existential); the box is a cube; the exponents
are integers.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

section Kernel

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {t : ℕ}
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **The constant-unit box kernel** `L_N(z) = ∫_{(0,b]^{n+1}} A(z,u) ∏ u^h e^{-βN ∏ u^{2k}} du`. -/
noncomputable def boxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  origPhaseIntegral n h k β N b (fun _ => 0) (A z)

/-- **The face coefficient of the box kernel**
`b^{Σh+n+1} (b^{2Σk})^{−λ} · amplitudeCoeff h k λ β (A(z, b·))`. -/
noncomputable def boxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
    amplitudeCoeff h k l β fun v => A z (b • v)

variable {n h k β b}

theorem continuous_amp_of_uncurry (hA : Continuous (Function.uncurry A)) (z : Fin t → ℝ) :
    Continuous (A z) :=
  hA.comp (continuous_const.prodMk continuous_id)

/-- **The pointwise certificate** at every base point. -/
theorem hasLeadingTerm_boxKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) (z : Fin t → ℝ) :
    HasLeadingTerm (boxKernel n h k β b A z) (boxFaceCoeff n h k β b A l z) l
      (multCount (ratioExp h k) l - 1) :=
  population_box_tendsto n h k hk β hβ hb hmin hatt (A z) (continuous_amp_of_uncurry A hA z)

end Kernel

/-! ### The input pair of the kernel and the reparametrised chart integral -/

section Input

variable (n : ℕ) (b : ℝ) {t : ℕ} (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
  (hA : Continuous (Function.uncurry A))

/-- The dilated amplitude `A(z, b·)` on the closed cube, as a continuous map on the product. -/
noncomputable def dilatedAmp : C((Fin t → ℝ) × closedCube (n + 1), ℝ) :=
  ⟨fun p => A p.1 (b • (p.2 : Fin (n + 1) → ℝ)),
    hA.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).const_smul b))⟩

/-- **The input pair of the box kernel at `z`**: zero fluctuation and the dilated amplitude. -/
noncomputable def boxInput (z : Fin t → ℝ) : InputSpace (n + 1) :=
  ((0 : C(closedCube (n + 1), ℝ)), (dilatedAmp n b A hA).curry z)

theorem continuous_boxInput : Continuous (boxInput n b A hA) :=
  continuous_const.prodMk (dilatedAmp n b A hA).curry.continuous

theorem extCube_boxInput_fst (z : Fin t → ℝ) (u : Fin (n + 1) → ℝ) :
    extCube (boxInput n b A hA z).1 u = 0 := by
  simp [extCube, boxInput]

theorem extCube_boxInput_snd (z : Fin t → ℝ) {u : Fin (n + 1) → ℝ} (hu : u ∈ closedCube (n + 1)) :
    extCube (boxInput n b A hA z).2 u = A z (b • u) := by
  simp only [extCube, boxInput, ContinuousMap.curry_apply]
  change A z (b • ((clampCube (n + 1) u : closedCube (n + 1)) : Fin (n + 1) → ℝ)) = A z (b • u)
  rw [clampCube_of_mem hu]

variable (h k : Fin (n + 1) → ℕ) (β : ℝ)

/-- The unit-box population integral is the chart integral at the square root of the sample size. -/
theorem origPhaseIntegral_one_eq_chartIntegral {M : ℝ} (hM : 0 ≤ M) (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β M 1 (fun _ => 0) η =
      chartIntegral (n + 1) h k β (Real.sqrt M) (fun _ => 0) η := by
  rw [chartIntegral_eq]
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [Real.sq_sqrt hM]
  ring

/-- **The box kernel through the input pair**: dilation to the unit box and reparametrisation
`N ↦ √(N b^{2Σk})` of the chart variable. -/
theorem boxKernel_eq_chartIntegral (hb : 0 < b) (z : Fin t → ℝ) {N : ℝ} (hN : 0 ≤ N) :
    boxKernel n h k β b A z N =
      b ^ (∑ i, h i + (n + 1)) * chartIntegral (n + 1) h k β
        (Real.sqrt (N * b ^ (2 * ∑ i, k i))) (extCube (boxInput n b A hA z).1)
        (extCube (boxInput n b A hA z).2) := by
  unfold boxKernel
  rw [origPhaseIntegral_dilation n h k β hb,
    origPhaseIntegral_one_eq_chartIntegral n h k β (mul_nonneg hN (pow_nonneg hb.le _))]
  congr 1
  rw [chartIntegral_eq, chartIntegral_eq]
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
  rw [extCube_boxInput_snd n b A hA z (unitBox_subset_closedCube _ hu),
    extCube_boxInput_fst n b A hA z u]

end Input

/-! ### The scale reparametrisation -/

section Scale

variable {n : ℕ} (h k : Fin (n + 1) → ℕ) (l : ℝ)

theorem leadScale_sqrt_mul {c N : ℝ} (hc : 0 < c) (hN : 0 < N) :
    leadScale h k l (Real.sqrt (N * c)) =
      N ^ (-l) * c ^ (-l) * ((Real.log N + Real.log c) / 2) ^ (multCount (ratioExp h k) l - 1) := by
  have hNc : 0 ≤ N * c := mul_nonneg hN.le hc.le
  have h1 : Real.sqrt (N * c) ^ (-(2 * l)) = N ^ (-l) * c ^ (-l) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNc, show (1 / 2 : ℝ) * (-(2 * l)) = -l by ring,
      Real.mul_rpow hN.le hc.le]
  have h2 : Real.log (Real.sqrt (N * c)) = (Real.log N + Real.log c) / 2 := by
    rw [Real.log_sqrt hNc, Real.log_mul hN.ne' hc.ne']
  unfold leadScale
  rw [h1, h2]

theorem leadScale_sqrt_mul_div_powLogScale {c N : ℝ} (hc : 0 < c) (hN : 1 < N) :
    leadScale h k l (Real.sqrt (N * c)) / powLogScale l (multCount (ratioExp h k) l - 1) N =
      c ^ (-l) * ((Real.log N + Real.log c) / (2 * Real.log N)) ^
        (multCount (ratioExp h k) l - 1) := by
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hNl : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [leadScale_sqrt_mul h k l hc hN0]
  unfold powLogScale
  rw [show (Real.log N + Real.log c) / (2 * Real.log N) =
    (Real.log N + Real.log c) / 2 / Real.log N by rw [div_div], mul_assoc,
    mul_div_mul_left _ _ hNl, mul_div_assoc]
  simp only [div_pow]

/-- The reparametrised log factor is bounded once `log N ≥ 1`. -/
theorem abs_log_ratio_le {c N : ℝ} (hN : 1 ≤ Real.log N) :
    |(Real.log N + Real.log c) / (2 * Real.log N)| ≤ (1 + |Real.log c|) / 2 := by
  have hpos : 0 < Real.log N := by linarith
  rw [abs_div, abs_of_pos (by linarith : 0 < 2 * Real.log N), div_le_div_iff₀ (by linarith)
    two_pos]
  calc |Real.log N + Real.log c| * 2 ≤ (Real.log N + |Real.log c|) * 2 := by
        have := abs_add_le (Real.log N) (Real.log c)
        rw [abs_of_pos hpos] at this
        linarith
    _ ≤ (1 + |Real.log c|) * (2 * Real.log N) := by nlinarith [abs_nonneg (Real.log c)]

end Scale

/-! ### The eventual normalised bound on a compact base -/

section Uniform

variable {n : ℕ} {h k : Fin (n + 1) → ℕ} {β b : ℝ} {t : ℕ}
  {A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}

/-- The limit functional is bounded on a compact set of inputs. -/
theorem exists_bound_limChart (hk : ∀ i, 0 < k i) {l : ℝ} (hl : 0 < l) (hβ : 0 < β)
    (hmin : ∀ i, l ≤ ratioExp h k i) {K : Set (InputSpace (n + 1))} (hK : IsCompact K) :
    ∃ M, ∀ x ∈ K, |limChart h k l β x| ≤ M := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : InputSpace (n + 1))
  obtain ⟨L, hL0, hL⟩ := limChart_lipschitz n h k hk l β R hl hβ hmin
  rcases K.eq_empty_or_nonempty with hne | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => absurd hx (by rw [hne]; exact notMem_empty x)⟩
  refine ⟨|limChart h k l β x₀| + L * (2 * R), fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
  have hx₀R : ‖x₀‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx₀)
  have hd : dist x x₀ ≤ 2 * R := by
    calc dist x x₀ ≤ ‖x‖ + ‖x₀‖ := dist_le_norm_add_norm x x₀
      _ ≤ 2 * R := by linarith
  calc |limChart h k l β x|
      ≤ |limChart h k l β x₀| + |limChart h k l β x - limChart h k l β x₀| := by
        have := abs_add_le (limChart h k l β x₀) (limChart h k l β x - limChart h k l β x₀)
        rwa [add_sub_cancel] at this
    _ ≤ |limChart h k l β x₀| + L * dist x x₀ := by
        linarith [hL x x₀ (hR hx) (hR hx₀)]
    _ ≤ |limChart h k l β x₀| + L * (2 * R) := by nlinarith

/-- **The eventual normalised bound, uniform on a compact base.** -/
theorem eventually_abs_boxKernel_div_le (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T) :
    ∃ C, ∀ᶠ N in atTop, ∀ z ∈ T,
      |boxKernel n h k β b A z N / powLogScale l (multCount (ratioExp h k) l - 1) N| ≤ C := by
  have hc : 0 < b ^ (2 * ∑ i, k i) := pow_pos hb _
  have hK : IsCompact (boxInput n b A hA '' T) := hT.image (continuous_boxInput n b A hA)
  obtain ⟨M, hM⟩ := exists_bound_limChart hk hl hβ hmin hK
  have hU := tendstoUniformlyOn_normChart n h k hk l β hl hβ hmin hatt _ hK
  have h1 := (Metric.tendstoUniformlyOn_iff.1 hU) 1 one_pos
  have hsq : Tendsto (fun N : ℝ => Real.sqrt (N * b ^ (2 * ∑ i, k i))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_mul_const hc)
  refine ⟨b ^ (∑ i, h i + (n + 1)) * (M + 1) * ((b ^ (2 * ∑ i, k i)) ^ (-l) *
    ((1 + |Real.log (b ^ (2 * ∑ i, k i))|) / 2) ^ (multCount (ratioExp h k) l - 1)), ?_⟩
  filter_upwards [hsq.eventually (h1.and (eventually_gt_atTop 1)),
    eventually_ge_atTop (Real.exp 1)] with N hN hNe z hz
  obtain ⟨hdist, hN'⟩ := hN
  have hN1 : 1 < N := lt_of_lt_of_le (Real.one_lt_exp_iff.2 one_pos) hNe
  have hN0 : 0 < N := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hNe
  have hxK : boxInput n b A hA z ∈ boxInput n b A hA '' T := ⟨z, hz, rfl⟩
  have hls : leadScale h k l (Real.sqrt (N * b ^ (2 * ∑ i, k i))) ≠ 0 := by
    unfold leadScale
    exact (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (Real.log_pos hN') _)).ne'
  have hchart : chartIntegral (n + 1) h k β (Real.sqrt (N * b ^ (2 * ∑ i, k i)))
      (extCube (boxInput n b A hA z).1) (extCube (boxInput n b A hA z).2) =
      normChart h k l β (Real.sqrt (N * b ^ (2 * ∑ i, k i))) (boxInput n b A hA z) *
        leadScale h k l (Real.sqrt (N * b ^ (2 * ∑ i, k i))) := by
    unfold normChart
    rw [div_mul_cancel₀ _ hls]
  have hnorm : |normChart h k l β (Real.sqrt (N * b ^ (2 * ∑ i, k i))) (boxInput n b A hA z)| ≤
      M + 1 := by
    have hd := hdist _ hxK
    rw [dist_eq_norm, Real.norm_eq_abs] at hd
    have := abs_sub_abs_le_abs_sub
      (normChart h k l β (Real.sqrt (N * b ^ (2 * ∑ i, k i))) (boxInput n b A hA z))
      (limChart h k l β (boxInput n b A hA z))
    rw [abs_sub_comm] at this
    linarith [hM _ hxK]
  have hM1 : 0 ≤ M + 1 := (abs_nonneg _).trans hnorm
  rw [boxKernel_eq_chartIntegral n b A hA h k β hb z hN0.le, hchart, mul_div_assoc,
    mul_div_assoc, leadScale_sqrt_mul_div_powLogScale h k l hc hN1, abs_mul,
    abs_of_pos (pow_pos hb _), abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc _), abs_pow,
    mul_assoc (b ^ (∑ i, h i + (n + 1)))]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos hb _).le
  refine mul_le_mul hnorm (mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hc _).le)
    (mul_nonneg (Real.rpow_pos_of_pos hc _).le (pow_nonneg (abs_nonneg _) _)) hM1
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_log_ratio_le hlog) _

/-- The box kernel is strongly measurable in the base point (a parametrised integral of a jointly
continuous integrand). -/
theorem stronglyMeasurable_boxKernel (hA : Continuous (Function.uncurry A)) (N : ℝ) :
    StronglyMeasurable fun z => boxKernel n h k β b A z N := by
  unfold boxKernel origPhaseIntegral
  refine StronglyMeasurable.integral_prod_right' (f := fun p : (Fin t → ℝ) × (Fin (n + 1) → ℝ) =>
    A p.1 p.2 * (∏ i, p.2 i ^ h i) * Real.exp (-(β * N * ∏ i, p.2 i ^ (2 * k i)) +
      β * (Real.sqrt N * ∏ i, p.2 i ^ k i) * 0)) ?_
  refine Continuous.stronglyMeasurable ?_
  fun_prop

/-- **The integrated certificate over a compact base**: for an integrable base weight `β_w` on `T`,
`∫_T β_w(z) L_N(z) dz ⟶ (∫_T β_w(z) faceCoeff(z) dz) · N^{−λ}(log N)^{m−1}`. -/
theorem hasLeadingTerm_integral_boxKernel (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    {βw : (Fin t → ℝ) → ℝ} (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * boxKernel n h k β b A z N)
      (∫ z in T, βw z * boxFaceCoeff n h k β b A l z) l (multCount (ratioExp h k) l - 1) := by
  obtain ⟨C, hC⟩ := eventually_abs_boxKernel_div_le hk hβ hb hl hmin hatt hA hT
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  refine hasLeadingTerm_setIntegral_of_dominated_kernel (G := fun _ => C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N => hβw.aestronglyMeasurable.mul
      (stronglyMeasurable_boxKernel hA N).aestronglyMeasurable
  · exact Eventually.of_forall fun z => hasLeadingTerm_boxKernel A hk hβ hb hmin hatt hA z
  · exact hC.mono fun N hN => (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz => hN z hz)
  · exact hβw.abs.mul_const C

end Uniform

end Grammar
