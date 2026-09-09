/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PosteriorEnergyLaw

/-!
# The assembled posterior energy law (unit 350; Astra #42 unit 1)

Laplace-transform assembly of laws on `[0,∞)`: given finitely many unnormalised chart energy
measures `V_{N,I}` with `V_{N,I}(ℝ)/b_N → A_I > 0` and normalised Laplace transforms converging to
those of laws `ρ_I`, and an assembled finite measure `U_N` carried by `[0,∞)` whose Laplace
transform differs from `∑_I ∫ e^{-ty} dV_{N,I}` by `o(b_N)` at every `t ≥ 0`, the normalised
assembled measure converges weakly to the mixture `∑_I (A_I/A_*) ρ_I`, `A_* = ∑_I A_I`
(`tendsto_normalize_of_laplace_assembly`, via the Laplace continuity theorem).  Instantiated with
the constant-phase chart energy laws: the assembled posterior law of `NK` over charts of common
`(λ, m)` with constant phases `a_I` converges to `∑_I (A_I(a_I)/A_*) ρ_{a_I}`
(`assembled_energyLaw_tendsto`); at zero phases this is the Gamma law of shape `λ`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-! ### Normalisation and mixtures -/

/-- Normalisation of a finite nonzero measure. -/
noncomputable def normalize (μ : Measure ℝ) : Measure ℝ := (μ univ)⁻¹ • μ

theorem measure_univ_ne_zero_of_real_pos (μ : Measure ℝ) (h : 0 < μ.real univ) : μ univ ≠ 0 := by
  intro h0
  rw [measureReal_def, h0, ENNReal.toReal_zero] at h
  exact lt_irrefl _ h

theorem normalize_isProbabilityMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (h : 0 < μ.real univ) :
    IsProbabilityMeasure (normalize μ) := by
  constructor
  rw [normalize, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (measure_univ_ne_zero_of_real_pos μ h) (measure_ne_top _ _)]

theorem normalize_apply (μ : Measure ℝ) (s : Set ℝ) : normalize μ s = (μ univ)⁻¹ * μ s := by
  rw [normalize, Measure.smul_apply, smul_eq_mul]

theorem integral_normalize (μ : Measure ℝ) (f : ℝ → ℝ) :
    ∫ y, f y ∂(normalize μ) = (∫ y, f y ∂μ) / μ.real univ := by
  rw [normalize, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, measureReal_def,
    div_eq_inv_mul]

/-- The mixture `∑_I w_I ρ_I` of finitely many laws. -/
noncomputable def mixture {M : Type*} [Fintype M] (w : M → ℝ) (ρ : M → Measure ℝ) : Measure ℝ :=
  ∑ I, ENNReal.ofReal (w I) • ρ I

theorem mixture_isProbabilityMeasure {M : Type*} [Fintype M] (w : M → ℝ) (ρ : M → Measure ℝ)
    [∀ I, IsProbabilityMeasure (ρ I)] (hw : ∀ I, 0 ≤ w I) (hsum : ∑ I, w I = 1) :
    IsProbabilityMeasure (mixture w ρ) := by
  constructor
  rw [mixture, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun I _ => hw I, hsum, ENNReal.ofReal_one]

theorem mixture_apply_Iio {M : Type*} [Fintype M] (w : M → ℝ) (ρ : M → Measure ℝ)
    (h0 : ∀ I, ρ I (Iio 0) = 0) : mixture w ρ (Iio 0) = 0 := by
  rw [mixture, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, h0, smul_zero, Finset.sum_const_zero]

theorem integrable_exp_neg_mul_of_measure_Iio (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h0 : ν (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun y => Real.exp (-(t * y))) ν :=
  (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous fun y => Real.exp (-(t * y))).aestronglyMeasurable
    ((ae_nonneg_of_measure_Iio h0).mono fun y hy => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ t * y := mul_nonneg ht hy
      linarith)

theorem integral_mixture {M : Type*} [Fintype M] (w : M → ℝ) (ρ : M → Measure ℝ)
    (hw : ∀ I, 0 ≤ w I) (f : ℝ → ℝ) (hf : ∀ I, Integrable f (ρ I)) :
    ∫ y, f y ∂(mixture w ρ) = ∑ I, w I * ∫ y, f y ∂(ρ I) := by
  rw [mixture, integral_finsetSum_measure fun I _ => (hf I).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hw I), smul_eq_mul]

theorem integral_exp_zero_mul (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∫ y, Real.exp (-(0 * y)) ∂μ = μ.real univ := by
  simp only [zero_mul, neg_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one]

/-! ### Laplace-transform assembly -/

/-- **Laplace-transform assembly**: the normalised assembled measure converges weakly to the
mixture `∑_I (A_I/A_*) ρ_I`. -/
theorem tendsto_normalize_of_laplace_assembly {M : Type*} [Fintype M] [Nonempty M]
    (U : ℕ → Measure ℝ) [∀ m, IsFiniteMeasure (U m)] (V : M → ℕ → Measure ℝ)
    [∀ I m, IsFiniteMeasure (V I m)] (b : ℕ → ℝ) (hb : ∀ m, 0 < b m) (A : M → ℝ)
    (hA : ∀ I, 0 < A I) (ρ : M → Measure ℝ) [∀ I, IsProbabilityMeasure (ρ I)]
    (h0 : ∀ m, U m (Iio 0) = 0) (h0ρ : ∀ I, ρ I (Iio 0) = 0)
    (hmass : ∀ I, Tendsto (fun m => (V I m).real univ / b m) atTop (𝓝 (A I)))
    (hlap : ∀ I, ∀ t : ℝ, 0 ≤ t → Tendsto (fun m =>
      (∫ y, Real.exp (-(t * y)) ∂(V I m)) / (V I m).real univ) atTop
      (𝓝 (∫ y, Real.exp (-(t * y)) ∂(ρ I))))
    (hres : ∀ t : ℝ, 0 ≤ t → Tendsto (fun m =>
      ((∫ y, Real.exp (-(t * y)) ∂(U m)) - ∑ I, ∫ y, Real.exp (-(t * y)) ∂(V I m)) / b m) atTop
      (𝓝 0))
    (hU : ∀ m, 0 < (U m).real univ) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun m => ⟨normalize (U m), normalize_isProbabilityMeasure _ (hU m)⟩) atTop
      (𝓝 ⟨mixture (fun I => A I / ∑ J, A J) ρ, mixture_isProbabilityMeasure _ _
        (fun I => div_nonneg (hA I).le (Finset.sum_nonneg fun J _ => (hA J).le))
        (by rw [← Finset.sum_div, div_self (Finset.sum_pos (fun J _ => hA J)
          Finset.univ_nonempty).ne'])⟩) := by
  have hAs : 0 < ∑ J, A J := Finset.sum_pos (fun J _ => hA J) Finset.univ_nonempty
  have hw : ∀ I, 0 ≤ A I / ∑ J, A J := fun I => div_nonneg (hA I).le hAs.le
  -- the Laplace transform of `U_m/b_m` converges to `∑ A_I L_I(t)`
  have hF : ∀ t : ℝ, 0 ≤ t → Tendsto (fun m => (∫ y, Real.exp (-(t * y)) ∂(U m)) / b m) atTop
      (𝓝 (∑ I, A I * ∫ y, Real.exp (-(t * y)) ∂(ρ I))) := by
    intro t ht
    have hV : ∀ I, Tendsto (fun m => (∫ y, Real.exp (-(t * y)) ∂(V I m)) / b m) atTop
        (𝓝 (A I * ∫ y, Real.exp (-(t * y)) ∂(ρ I))) := fun I => by
      have := (hmass I).mul (hlap I t ht)
      refine this.congr' (Eventually.of_forall fun m => ?_)
      dsimp only
      by_cases hz : (V I m).real univ = 0
      · -- a chart of vanishing mass is the zero measure: both sides vanish
        have hz' : V I m = 0 := by
          rw [measureReal_def] at hz
          refine Measure.measure_univ_eq_zero.1 ?_
          rcases (ENNReal.toReal_eq_zero_iff _).1 hz with h | h
          · exact h
          · exact absurd h (measure_ne_top _ _)
        rw [hz']
        simp
      · field_simp
    have hsum := tendsto_finsetSum Finset.univ fun I _ => hV I
    have := (hres t ht).add hsum
    rw [zero_add] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    dsimp only
    rw [← Finset.sum_div, ← add_div, sub_add_cancel]
  -- the total mass `U_m/b_m → A_*`
  have hF0 : Tendsto (fun m => (U m).real univ / b m) atTop (𝓝 (∑ J, A J)) := by
    have := hF 0 le_rfl
    simp only [integral_exp_zero_mul, probReal_univ, mul_one] at this
    exact this
  refine tendsto_of_laplace _ _ (fun m => ?_) (mixture_apply_Iio _ _ h0ρ) fun t ht => ?_
  · change normalize (U m) (Iio 0) = 0
    rw [normalize_apply, h0 m, mul_zero]
  change Tendsto (fun m => ∫ y, Real.exp (-(t * y)) ∂(normalize (U m))) atTop
    (𝓝 (∫ y, Real.exp (-(t * y)) ∂(mixture (fun I => A I / ∑ J, A J) ρ)))
  rw [integral_mixture _ _ hw _ fun I => integrable_exp_neg_mul_of_measure_Iio _ (h0ρ I) ht]
  have hlim := (hF t ht).div hF0 hAs.ne'
  refine hlim.congr' (Eventually.of_forall fun m => ?_) |>.trans ?_
  · simp only [Pi.div_apply]
    rw [integral_normalize, div_div_div_cancel_right₀ (hb m).ne']
  · rw [show (∑ I, A I * ∫ y, Real.exp (-(t * y)) ∂(ρ I)) / ∑ J, A J =
      ∑ I, A I / (∑ J, A J) * ∫ y, Real.exp (-(t * y)) ∂(ρ I) by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun I _ => ?_
        ring]

/-! ### The constant-phase chart instantiation -/

/-- The unnormalised constant-phase chart energy measure `𝒵_N · energyLaw`. -/
noncomputable def chartEnergyMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) (a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (origPhaseIntegral n h k β N 1 (fun _ => a) η) • energyLaw n h k β N η a

theorem chartEnergyMeasure_real_univ (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) :
    (chartEnergyMeasure n h k β N η a).real univ =
      origPhaseIntegral n h k β N 1 (fun _ => a) η := by
  have := energyLaw_isProbabilityMeasure n h k β N hηc hηnn a hZ
  rw [chartEnergyMeasure, measureReal_ennreal_smul_apply, probReal_univ, mul_one,
    ENNReal.toReal_ofReal hZ.le]

theorem chartEnergyMeasure_isFiniteMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) :
    IsFiniteMeasure (chartEnergyMeasure n h k β N η a) := by
  have := energyLaw_isProbabilityMeasure n h k β N hηc hηnn a hZ
  refine ⟨?_⟩
  rw [chartEnergyMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem integral_chartEnergyMeasure (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η) (hηnn : ∀ u ∈ unitBox (n + 1), 0 ≤ η u)
    (a : ℝ) (hZ : 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) (t : ℝ) :
    (∫ y, Real.exp (-(t * y)) ∂(chartEnergyMeasure n h k β N η a)) /
        (chartEnergyMeasure n h k β N η a).real univ =
      constPhaseLaplace n h k β N η a t := by
  rw [chartEnergyMeasure_real_univ n h k β N hηc hηnn a hZ, chartEnergyMeasure,
    integral_smul_measure, ENNReal.toReal_ofReal hZ.le, smul_eq_mul, mul_div_assoc, mul_comm,
    div_mul_cancel₀ _ hZ.ne', energyLaw_laplace n h k β N hηc hηnn a hZ t]

/-- **Assembled posterior law of `NK` at constant phases**: over finitely many charts with common
`(λ, m)`, positive leading coefficients `A_I(a_I)` and an externally supplied assembled energy
measure whose Laplace transform matches the chart sum up to `o(N^{-λ}L^{m-1})`, the normalised
assembled law converges weakly to `∑_I (A_I/A_*) ρ_{a_I}`. -/
theorem assembled_energyLaw_tendsto {M : Type*} [Fintype M] [Nonempty M] (n : ℕ)
    (h k : M → Fin (n + 1) → ℕ) (hk : ∀ I i, 0 < k I i) {β : ℝ} (hβ : 0 < β) (a : M → ℝ)
    (cη : M → CoeffFamily (n + 1)) (hη : ∀ I, AbsSummable (cη I))
    (η : M → (Fin (n + 1) → ℝ) → ℝ) (hηc : ∀ I, Continuous (η I))
    (hηnn : ∀ I, ∀ u ∈ unitBox (n + 1), 0 ≤ η I u)
    (hev : ∀ I, ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF (cη I) u = η I u) {l : ℝ}
    (hmin : ∀ I i, l ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = l)
    {mstar : ℕ} (hmult : ∀ I, multCount (ratioExp (h I) (k I)) l = mstar)
    (hA : ∀ I, 0 < familySpectralCoeff n (h I) (k I) β (constFamily (a I)) (cη I) l (mstar - 1))
    (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)
    (hZ : ∀ I m, 0 < origPhaseIntegral n (h I) (k I) β (Nseq m) 1 (fun _ => a I) (η I))
    (U : ℕ → Measure ℝ) [∀ m, IsFiniteMeasure (U m)] (h0 : ∀ m, U m (Iio 0) = 0)
    (hU : ∀ m, 0 < (U m).real univ)
    (hres : ∀ t : ℝ, 0 ≤ t → Tendsto (fun m =>
      ((∫ y, Real.exp (-(t * y)) ∂(U m)) -
        ∑ I, ∫ y, Real.exp (-(t * y)) ∂(chartEnergyMeasure n (h I) (k I) β (Nseq m) (η I) (a I))) /
      (Nseq m ^ (-l) * Real.log (Nseq m) ^ (mstar - 1))) atTop (𝓝 0)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun m => ⟨normalize (U m), normalize_isProbabilityMeasure _ (hU m)⟩) atTop
      (𝓝 ⟨mixture (fun I => familySpectralCoeff n (h I) (k I) β (constFamily (a I)) (cη I) l
          (mstar - 1) / ∑ J, familySpectralCoeff n (h J) (k J) β (constFamily (a J)) (cη J) l
          (mstar - 1)) (fun I => phaseLaw β (a I) l),
        @mixture_isProbabilityMeasure M _ (fun I => familySpectralCoeff n (h I) (k I) β
          (constFamily (a I)) (cη I) l (mstar - 1) / ∑ J, familySpectralCoeff n (h J) (k J) β
          (constFamily (a J)) (cη J) l (mstar - 1)) (fun I => phaseLaw β (a I) l)
          (fun I => @phaseLaw_isProbabilityMeasure β (a I) l ⟨hβ⟩
            ⟨ratioExp_min_pos (h I) (k I) (hk I) (hatt I)⟩)
          (fun I => div_nonneg (hA I).le (Finset.sum_nonneg fun J _ => (hA J).le))
          (by rw [← Finset.sum_div, div_self (Finset.sum_pos (fun J _ => hA J)
            Finset.univ_nonempty).ne'])⟩) := by
  have hl0 : 0 < l := ratioExp_min_pos (h (Classical.arbitrary M)) (k (Classical.arbitrary M))
    (hk _) (hatt _)
  have : Fact (0 < β) := ⟨hβ⟩
  have : Fact (0 < l) := ⟨hl0⟩
  have : ∀ I m, IsFiniteMeasure (chartEnergyMeasure n (h I) (k I) β (Nseq m) (η I) (a I)) :=
    fun I m => chartEnergyMeasure_isFiniteMeasure n (h I) (k I) β (Nseq m) (hηc I) (hηnn I) (a I)
      (hZ I m)
  have hb : ∀ m, 0 < Nseq m ^ (-l) * Real.log (Nseq m) ^ (mstar - 1) := fun m =>
    mul_pos (Real.rpow_pos_of_pos (lt_trans one_pos (hN1 m)) _)
      (pow_pos (Real.log_pos (hN1 m)) _)
  refine tendsto_normalize_of_laplace_assembly U _ _ hb _ hA (fun I => phaseLaw β (a I) l) h0
    (fun I => phaseLaw_Iio β (a I) l) (fun I => ?_) (fun I t ht => ?_) hres hU
  · -- chart masses
    have := constPhase_tendsto n (h I) (k I) (hk I) l β hl0 hβ (hmin I) (hatt I) (a I) (η I)
      (hηc I)
    rw [← (constPhase_leadingCoeff n (h I) (k I) (hk I) hβ (a I) (hη I) (hηc I) (hev I) (hmin I)
      (hatt I)).2, hmult I] at this
    refine (this.comp hN).congr' (Eventually.of_forall fun m => ?_)
    simp only [Function.comp_def]
    rw [chartEnergyMeasure_real_univ n (h I) (k I) β (Nseq m) (hηc I) (hηnn I) (a I) (hZ I m)]
  · -- chart Laplace transforms
    have := (constPhaseLaplace_tendsto_law n (h I) (k I) (hk I) hβ ht (a I) (hη I) (hηc I)
      (hev I) (hmin I) (hatt I) (hmult I ▸ (hA I).ne')).comp hN
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp only [Function.comp_def]
    rw [integral_chartEnergyMeasure n (h I) (k I) β (Nseq m) (hηc I) (hηnn I) (a I) (hZ I m) t]

end Grammar
