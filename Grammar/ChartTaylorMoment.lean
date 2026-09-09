/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TaylorMoment
import Grammar.ChartPresentation

/-!
# The chart integral as a Taylor–moment series

The repository's chart standard integral `dataBoxIntegral` at zero fluctuation is the integral of
the amplitude against the **dressed measure** `η_N = u^h e^{−βN u^{2k}} du` on the normal box
(`dataBoxIntegral_eq_integral_dressed`).  For an observable `F` analytic on a ball containing the
box and agreeing with the amplitude on the box, the chart integral is therefore the absolutely
convergent Taylor–moment series
`Z(N) = ∑_r (1/r!) ⟨Moment_{η_N,r}, D^r F(0)⟩` (`dataBoxIntegral_eq_tsum_moment`), and in
coordinates `Z(N) = ∑_r ∑_{|γ|=r} c_γ M̃_γ(N)` with the dressed moments
`M̃_γ(N) = ∫ u^γ u^h e^{−βN u^{2k}} du` (`dataBoxIntegral_eq_tsum_coeff_moment`) — the paper's
`eq:tubular_expansion` in its Taylor-tensor form, now an exact identity.

**Compatibility with the canonical coefficients**: the Taylor–moment series is the same function of
`N` as the chart integral, so it has exactly the chart theorem's power–log expansion with the chart
theorem's coefficients (`taylorMomentSeries_cutoffExpansion`).  No coefficient is defined by an
unjustified interchange of the degree sum with the asymptotic expansion.

Non-claims: degree truncation is not asymptotic truncation; the fluctuation term is absent
(population case); analyticity of the observable on a neighbourhood of the closed box is assumed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Grammar

open MonoRep CoeffFamily

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)

/-- The dressed measure `u^h e^{−βN u^{2k}} du` on the normal box `(0,b]^{n+1}`. -/
noncomputable def dressedMeasure : Measure (Fin (n + 1) → ℝ) :=
  (volume.restrict (piBox (n + 1) (Ioc 0 b))).withDensity fun u =>
    ENNReal.ofReal ((∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i))))

theorem measurable_dressedDensity :
    Measurable fun u : Fin (n + 1) → ℝ =>
      (∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i))) :=
  (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).mul
    ((measurable_const.mul (Finset.measurable_prod _ fun i _ =>
      (measurable_pi_apply i).pow_const _)).neg.exp)

theorem dressedMeasure_ae_mem_box :
    ∀ᵐ u ∂dressedMeasure n h k β N b, u ∈ piBox (n + 1) (Ioc 0 b) :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (measurableSet_piBox _ _ measurableSet_Ioc))

theorem dressedMeasure_ae_norm_le (hb : 0 < b) : ∀ᵐ u ∂dressedMeasure n h k β N b, ‖u‖ ≤ b := by
  filter_upwards [dressedMeasure_ae_mem_box n h k β N b] with u hu
  rw [pi_norm_le_iff_of_nonneg hb.le]
  intro i
  have hi : u i ∈ Ioc 0 b := hu i (mem_univ i)
  rw [Real.norm_eq_abs, abs_of_pos hi.1]
  exact hi.2

theorem isFiniteMeasure_dressedMeasure (hβ : 0 ≤ β) (hN : 0 ≤ N) :
    IsFiniteMeasure (dressedMeasure n h k β N b) := by
  refine isFiniteMeasure_withDensity ?_
  have hle : ∀ᵐ u ∂volume.restrict (piBox (n + 1) (Ioc 0 b)),
      ENNReal.ofReal ((∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)))) ≤
        ENNReal.ofReal (b ^ ∑ i, h i) := by
    filter_upwards [ae_restrict_mem (measurableSet_piBox _ _ measurableSet_Ioc)] with u hu
    have hpos : ∀ i, 0 < u i := fun i => (hu i (mem_univ i)).1
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ∏ i, u i ^ h i ≤ b ^ ∑ i, h i := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun i _ => pow_nonneg (hpos i).le _) fun i _ =>
        pow_le_pow_left₀ (hpos i).le (hu i (mem_univ i)).2 _
    have h2 : Real.exp (-(β * N * ∏ i, u i ^ (2 * k i))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (mul_nonneg hβ hN)
        (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _)))
    calc (∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i))) ≤ (∏ i, u i ^ h i) * 1 :=
          mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _)
      _ ≤ b ^ ∑ i, h i := by rw [mul_one]; exact h1
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hle)
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  unfold piBox
  rw [Real.volume_pi_Ioc]
  exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top

theorem integrable_norm_pow_dressed (hβ : 0 ≤ β) (hN : 0 ≤ N) (hb : 0 < b) (r : ℕ) :
    Integrable (fun u => ‖u‖ ^ r) (dressedMeasure n h k β N b) :=
  haveI := isFiniteMeasure_dressedMeasure n h k β N b hβ hN
  integrable_norm_pow_of_ae_le _ (dressedMeasure_ae_norm_le n h k β N b hb) r

/-- **The chart integral is the amplitude integrated against the dressed measure** (zero
fluctuation). -/
theorem dataBoxIntegral_eq_integral_dressed (x : DataSpace (n + 1)) (hx : xiCoord x = 0) :
    dataBoxIntegral n h k β N b x = ∫ u, evalF (toEta b x) u ∂dressedMeasure n h k β N b := by
  unfold dressedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_dressedDensity n h k β N).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold dataBoxIntegral familyPhaseIntegralBox
  refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Ioc) fun u hu => ?_
  have hpos : ∀ i, 0 < u i := fun i => (hu i (mem_univ i)).1
  rw [toXi_eq_zero hx, evalF_zero, mul_zero, add_zero, ENNReal.toReal_ofReal
    (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _) (Real.exp_pos _).le),
    smul_eq_mul]
  ring

variable {n h k β N b}

theorem dressedMeasure_ae_mem_eball (hb : 0 < b) {R : ℝ≥0∞} (hbR : ENNReal.ofReal b < R) :
    ∀ᵐ u ∂dressedMeasure n h k β N b, u ∈ Metric.eball (0 : Fin (n + 1) → ℝ) R := by
  filter_upwards [dressedMeasure_ae_norm_le n h k β N b hb] with u hu
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu) hbR

theorem dressedMeasure_ae_norm_le_toNNReal (hb : 0 < b) :
    ∀ᵐ u ∂dressedMeasure n h k β N b, ‖u‖ ≤ (b.toNNReal : ℝ) := by
  filter_upwards [dressedMeasure_ae_norm_le n h k β N b hb] with u hu
  rwa [Real.coe_toNNReal', max_eq_left hb.le]

variable {F : (Fin (n + 1) → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (Fin (n + 1) → ℝ) ℝ}
  {R : ℝ≥0∞}

/-- **The chart integral as a Taylor–moment series**: for an observable `F` analytic on a ball
containing the box and equal to the amplitude on the box,
`Z(N) = ∑_r (1/r!) ⟨Moment_{η_N,r}, D^r F(0)⟩`, absolutely convergent. -/
theorem dataBoxIntegral_eq_tsum_moment (hβ : 0 ≤ β) (hN : 0 ≤ N) (hb : 0 < b)
    (x : DataSpace (n + 1)) (hx : xiCoord x = 0) (hp : HasFPowerSeriesOnBall F p 0 R)
    (hbR : ENNReal.ofReal b < R) (hF : ∀ u ∈ piBox (n + 1) (Ioc 0 b), F u = evalF (toEta b x) u) :
    dataBoxIntegral n h k β N b x = ∑' r, (r.factorial : ℝ)⁻¹ *
      momentFunctional (dressedMeasure n h k β N b)
        (integrable_norm_pow_dressed n h k β N b hβ hN hb r) (normalJet F r) := by
  have := isFiniteMeasure_dressedMeasure n h k β N b hβ hN
  rw [dataBoxIntegral_eq_integral_dressed n h k β N b x hx]
  have hFη : ∫ u, evalF (toEta b x) u ∂dressedMeasure n h k β N b =
      ∫ u, F u ∂dressedMeasure n h k β N b := by
    refine integral_congr_ae ?_
    filter_upwards [dressedMeasure_ae_mem_box n h k β N b] with u hu
    exact (hF u hu).symm
  rw [hFη]
  refine integral_eq_tsum_moment hp _ (dressedMeasure_ae_mem_eball hb hbR) _
    (summable_norm_mul_integral_of_ae_le _ (dressedMeasure_ae_norm_le_toNNReal hb) ?_)
  exact lt_of_lt_of_le hbR hp.r_le

/-- The same series with plain integrals (no dependent integrability proof). -/
theorem dataBoxIntegral_eq_tsum_moment' (hβ : 0 ≤ β) (hN : 0 ≤ N) (hb : 0 < b)
    (x : DataSpace (n + 1)) (hx : xiCoord x = 0) (hp : HasFPowerSeriesOnBall F p 0 R)
    (hbR : ENNReal.ofReal b < R) (hF : ∀ u ∈ piBox (n + 1) (Ioc 0 b), F u = evalF (toEta b x) u) :
    dataBoxIntegral n h k β N b x = ∑' r, (r.factorial : ℝ)⁻¹ *
      ∫ u, normalJet F r (fun _ => u) ∂dressedMeasure n h k β N b :=
  dataBoxIntegral_eq_tsum_moment hβ hN hb x hx hp hbR hF

/-- **`eq:tubular_expansion` in Taylor-tensor form**: in coordinates, with the series realising the
box amplitude family `c_γ = η_γ b^{−|γ|}`, `Z(N) = ∑_r ∑_{|γ|=r} c_γ M̃_γ(N)` with the dressed
moments `M̃_γ(N) = ∫ u^γ u^h e^{−βN u^{2k}} du`. -/
theorem dataBoxIntegral_eq_tsum_coeff_moment (hβ : 0 ≤ β) (hN : 0 ≤ N) (hb : 0 < b)
    (x : DataSpace (n + 1)) (hx : xiCoord x = 0) (hp : HasFPowerSeriesOnBall F p 0 R)
    (hpc : RealisesCoeff p (toEta b x)) (hbR : ENNReal.ofReal b < R)
    (hF : ∀ u ∈ piBox (n + 1) (Ioc 0 b), F u = evalF (toEta b x) u) :
    dataBoxIntegral n h k β N b x = ∑' r, ∑ γ ∈ Finset.Nat.antidiagonalTuple (n + 1) r,
      toEta b x γ * dressedMoment (dressedMeasure n h k β N b) γ := by
  rw [dataBoxIntegral_eq_tsum_moment hβ hN hb x hx hp hbR hF]
  exact tsum_congr fun r =>
    moment_contraction_coeff _ hp hpc (integrable_norm_pow_dressed n h k β N b hβ hN hb) r

/-! ### Compatibility with the canonical chart coefficients -/

theorem CutoffExpansion.congr_eventually {Q D : ℕ} {Z₁ Z₂ : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hZ : CutoffExpansion Q D Z₁ c) (h12 : Z₁ =ᶠ[atTop] Z₂) : CutoffExpansion Q D Z₂ c := by
  intro L hL
  obtain ⟨K, hK⟩ := hZ L hL
  refine ⟨K, ?_⟩
  filter_upwards [hK, h12] with N h1 h2
  rwa [← h2]

/-- **The Taylor–moment series has the chart theorem's expansion**: on the unit box, the function
`N ↦ ∑_r (1/r!) ⟨Moment_{η_N,r}, D^r F(0)⟩` is a `CutoffExpansion` with the Taylor-tree coefficients
of the chart datum — the same coefficients `C_{μ,j}` (the family spectral coefficients, equal to the
paper's Cauchy-product series) that the chart theorem attaches to `Z`. -/
theorem taylorMomentSeries_cutoffExpansion (hk : ∀ i, 0 < k i) (hβ : 0 < β) (x : DataSpace (n + 1))
    (hx : xiCoord x = 0) (hp : HasFPowerSeriesOnBall F p 0 R) (h1R : ENNReal.ofReal 1 < R)
    (hF : ∀ u ∈ piBox (n + 1) (Ioc 0 1), F u = evalF (toEta 1 x) u) :
    ∃ C : ℝ → ℕ → ℝ, TaylorTreeConclusion n h k β 1 (toXi 1 x) (toEta 1 x) C ∧
      CutoffExpansion (latticeQ k) n (fun N => ∑' r, (r.factorial : ℝ)⁻¹ *
        ∫ u, normalJet F r (fun _ => u) ∂dressedMeasure n h k β N 1) C := by
  obtain ⟨C, hC⟩ := taylorTree_data n h k hk β hβ one_pos x
  refine ⟨C, hC, (cutoffExpansion_of_conclusion n h k β hC).congr_eventually ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  exact dataBoxIntegral_eq_tsum_moment' hβ.le hN one_pos x hx hp h1R hF

end Grammar
