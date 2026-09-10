import Grammar.SampleDatumLimit
import Grammar.JointSample

/-!
# The multi-chart field limit for the joint sample datum and the assembled annealed theorem

Finitely many certified box charts `I : Fin J` (common dimension `n + 1`, radii `b_I`, coefficient
maps `c_I`, zero-phase amplitude data `A_I`) are read from the same i.i.d. sample. Their chart
data are the components of the **joint sample datum** (`JointSample.lean`), which converges in
distribution on `∀ I, DataSpace` to the unpacked stacked `ℓ¹` Gaussian limit
(`jointSampleDatum_apply_eq_sampleDatum`, `jointSampleDatum_tendstoInDistribution`).

At the global scale `A_n = n^λ/(log n)^{m−1}` with every chart exponent pair dominating `(λ, m)`:
the charts with `(λ_I, m_I) = (λ, m)` contribute their leading coefficients (the ordered remainder
at the leading pair is the scaled core, CLXII, and `R_I − C_I → 0` in probability); the strictly
dominated charts contribute `A_n Z_I = r_I(n) · R_I` with a deterministic `r_I(n) → 0`
(`tendsto_scaleA_div_scaleA`) and `R_I` uniformly bounded on data balls, hence `→ 0` in
probability by tightness (`tendstoInMeasure_zero_of_uniform_on_balls`). Slutsky then gives **the
joint field limit** `A_n coreSum_n ⇒ ∑_{I leading} C_I(unpack_I Z + A_I)`
(`tendstoInDistribution_scaled_coreSum_sampleDatum`), and with CLX–CLXI **the assembled annealed
sample-datum theorem** `E[A_n(coreSum_n + Rem_n)] → E_ν[∑_{I leading} C_I(unpack_I Z + A_I)]`
(`tendsto_integral_scaled_coreSum_sampleDatum`), conditional only on `E|A_n Rem_n| → 0`.

Non-claims: the Gaussian identification of the limiting expectation is not made; bounded chart
phase observations are a hypothesis on the sampling law; the external remainder is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

section InMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem tendstoInMeasure_congr_eventually {ι : Type*} {l : Filter ι} {f f' : ι → Ω → ℝ}
    {g : Ω → ℝ} (h : TendstoInMeasure μ f l g) (hff' : ∀ᶠ i in l, f i = f' i) :
    TendstoInMeasure μ f' l g := fun ε hε =>
  (h ε hε).congr' (hff'.mono fun i hi => by rw [hi])

theorem tendstoInMeasure_zero_add {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0)) (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => f i ω + g i ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h1 := hf (ε / 2) (half_pos hε)
  have h2 := hg (ε / 2) (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using h1.add h2) (fun _ => zero_le) fun i => ?_
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, sub_zero, mem_union, Real.norm_eq_abs] at hω ⊢
  by_contra hcon
  rw [not_or] at hcon
  have h1' := not_le.1 hcon.1
  have h2' := not_le.1 hcon.2
  have := norm_add_le (f i ω) (g i ω)
  simp only [Real.norm_eq_abs] at this
  linarith

theorem tendstoInMeasure_zero_finset_sum {J : Type*} (s : Finset J) {f : J → ℕ → Ω → ℝ}
    (hf : ∀ I ∈ s, TendstoInMeasure μ (f I) atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun i ω => ∑ I ∈ s, f I i ω) atTop (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simp only [Finset.sum_empty, sub_zero, norm_zero]
    have : {x : Ω | ε ≤ (0 : ℝ)} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => absurd hx (not_le.2 hε)
    simp [this]
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact tendstoInMeasure_zero_add (hf a (Finset.mem_insert_self a s))
      (ih fun I hI => hf I (Finset.mem_insert_of_mem hI))

end InMeasure

section Ratio

/-- The scale ratio `A_n(λ,m)/A_n(λ',m') → 0` when `(λ', m')` strictly dominates `(λ, m)`. -/
theorem tendsto_scaleA_div_scaleA {lam lam' : ℝ} {m m' : ℕ}
    (hdom : lam < lam' ∨ (lam = lam' ∧ m' - 1 < m - 1)) :
    Tendsto (fun N : ℕ => scaleA lam m N / scaleA lam' m' N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  rcases hdom with hlt | ⟨heq, hm⟩
  · have hε : 0 < lam' - lam := sub_pos.2 hlt
    have hlo : Tendsto (fun N : ℕ => Real.log N ^ ((m' - 1 : ℕ) : ℝ) / (N : ℝ) ^ (lam' - lam))
        atTop (𝓝 0) :=
      ((isLittleO_log_rpow_rpow_atTop ((m' - 1 : ℕ) : ℝ) hε).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero
    refine squeeze_zero_norm' ?_ hlo
    filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop 2] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hl1 : 0 < Real.log N := by linarith
    rw [scaleA_of_two_le lam m hN, scaleA_of_two_le lam' m' hN, Real.norm_eq_abs, abs_of_nonneg
      (by positivity), Real.rpow_natCast]
    rw [div_div_div_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : (N : ℝ) ^ lam' = (N : ℝ) ^ lam * (N : ℝ) ^ (lam' - lam) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hpow : 1 ≤ Real.log N ^ (m - 1) := one_le_pow₀ h1
    rw [hA]
    have hnn : 0 ≤ (N : ℝ) ^ lam * (N : ℝ) ^ (lam' - lam) * Real.log N ^ (m' - 1) := by positivity
    nlinarith [hnn, hpow, mul_nonneg hnn (sub_nonneg.2 hpow)]
  · subst heq
    obtain ⟨d, hd0, hd⟩ : ∃ d : ℕ, 0 < d ∧ m - 1 = (m' - 1) + d :=
      ⟨m - 1 - (m' - 1), by omega, by omega⟩
    have hlim : Tendsto (fun N : ℕ => (Real.log N ^ d)⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop hd0.ne').comp hlog).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop 2] with N h1 hN
    have hl : Real.log N ≠ 0 := by linarith
    have hNl : (N : ℝ) ^ lam ≠ 0 :=
      (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) lam).ne'
    rw [scaleA_of_two_le lam m hN, scaleA_of_two_le lam m' hN, hd, pow_add]
    field_simp

end Ratio

section Joint

variable {n : ℕ} {J : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (bJ : Fin J → ℝ) (hb : ∀ I, 0 < bJ I)
  (c : Fin J → 𝓧 → CoeffFamily (n + 1)) (hc : ∀ I x, AbsSummableAt (c I x) (bJ I))
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)
variable (h k : Fin J → Fin (n + 1) → ℕ)

/-- The chart observations of the joint sample. -/
noncomputable abbrev chartObs : ∀ _ : Fin J, 𝓧 → L1Seq (DataIdx (n + 1)) :=
  fun I => phaseObs (bJ I) (hb I) (c I) (hc I)

/-- The chart component of the joint sample datum is the chart's own sample datum. -/
theorem jointSampleDatum_apply_eq_sampleDatum (hcm : ∀ I γ, Measurable fun x => c I x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ I γ, MemLp (fun ω => c I (X 0 ω) γ) 2 P)
    (hsum : ∀ I, Summable fun γ : Fin (n + 1) → ℕ =>
      bJ I ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c I (X 0 ω) γ) ^ 2 ∂P))
    (A : Fin J → DataSpace (n + 1)) (N : ℕ) (ω : Ω) (I : Fin J) :
    jointSampleDatum P (chartObs bJ hb c hc) X A N ω I =
      sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω := by
  have hint : Integrable (fun ω => stackObs (chartObs bJ hb c hc) (X 0 ω)) P :=
    integrable_of_summableCoordL2 P (summableCoordL2_stackObs P _ X (hXm 0)
      (fun I => measurable_phaseObs (bJ I) (hb I) (c I) (hc I) (hcm I))
      (fun I => summableCoordL2_sampleObs (bJ I) (hb I) (c I) (hc I) P X (hcm I) (hXm 0) (hc2 I)
        (hsum I)))
  unfold jointSampleDatum
  rw [Pi.add_apply, unpackAll_apply, unpack_empiricalSum_stack P _ X hint I N ω]
  rfl

open scoped Classical in
/-- The joint leading coefficient at the global scale: the charts with `(λ_I, m_I) = (λ, m)`
contribute `C_I(y_I)`, the others contribute zero. -/
noncomputable def jointLeadingCoeff (β lam : ℝ) (mult : ℕ)
    (y : ∀ _ : Fin J, DataSpace (n + 1)) : ℝ :=
  ∑ I, if lam = minRatio (h I) (k I) ∧
      multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 = mult - 1 then
    dataBoxCoeff n (h I) (k I) β (bJ I) (y I) (minRatio (h I) (k I))
      (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1)
  else 0

include hb in
theorem continuous_jointLeadingCoeff (hk : ∀ I i, 0 < k I i) {β : ℝ} (hβ : 0 < β) (lam : ℝ)
    (mult : ℕ) : Continuous (jointLeadingCoeff bJ h k β lam mult) := by
  classical
  unfold jointLeadingCoeff
  refine continuous_finsetSum _ fun I _ => ?_
  split_ifs
  · exact (continuous_taylorTree_coeff n (h I) (k I) (hk I) β hβ (hb I) _ _).comp
      (continuous_apply I)
  · exact continuous_const

/-- **The joint field limit for the sample datum**: at a global scale dominated by every chart
exponent pair, `A_n coreSum_n(sampleDatum) ⇒ ∑_{I leading} C_I(unpack_I Z + A_I)` with `Z ~ ν`
the stacked `ℓ¹` Gaussian limit of the chart observations. -/
theorem tendstoInDistribution_scaled_coreSum_sampleDatum (hk : ∀ I i, 0 < k I i) {β : ℝ}
    (hβ : 0 < β) {lam : ℝ} {mult : ℕ}
    (hdom : ∀ I, lam < minRatio (h I) (k I) ∨
      (lam = minRatio (h I) (k I) ∧
        multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 ≤ mult - 1))
    (hcm : ∀ I γ, Measurable fun x => c I x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ I γ, MemLp (fun ω => c I (X 0 ω) γ) 2 P)
    (hsum : ∀ I, Summable fun γ : Fin (n + 1) → ℕ =>
      bJ I ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c I (X 0 ω) γ) ^ 2 ∂P))
    (A : Fin J → DataSpace (n + 1)) :
    ∃ ν : ProbabilityMeasure (L1Seq (StackIdx fun _ : Fin J => n)),
      (∀ F : Finset (StackIdx fun _ : Fin J => n),
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (stackObs (chartObs bJ hb c hc) (X 0 ω))) P) ∧
      TendstoInDistribution (fun N ω => scaleA lam mult N *
          coreSum n h k bJ β (fun N => (N : ℝ))
            (fun I N => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N) N ω) atTop
        (fun z => jointLeadingCoeff bJ h k β lam mult (unpackAll z + A)) (fun _ => P)
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))) := by
  classical
  obtain ⟨ν, hν, hmarg⟩ := jointSampleDatum_tendstoInDistribution P (chartObs bJ hb c hc) X
    (fun I => measurable_phaseObs (bJ I) (hb I) (c I) (hc I) (hcm I)) hXm hXind hXid
    (fun I => summableCoordL2_sampleObs (bJ I) (hb I) (c I) (hc I) P X (hcm I) (hXm 0) (hc2 I)
      (hsum I)) A
  refine ⟨ν, hmarg, ?_⟩
  have hjoint : ∀ N ω, jointSampleDatum P (chartObs bJ hb c hc) X A N ω =
      fun I => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω :=
    fun N ω => funext fun I =>
      jointSampleDatum_apply_eq_sampleDatum bJ hb c hc P X hcm hXm hc2 hsum A N ω I
  have hXIm : ∀ I N, Measurable (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N) :=
    fun I N => measurable_sampleDatum P (bJ I) (hb I) (c I) (hc I) X (hcm I) hXm (hc2 I) (hsum I)
      (A I) N
  -- each chart datum converges in distribution
  have hXIconv : ∀ I, TendstoInDistribution (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I))
      atTop (fun z => unpack I z + A I) (fun _ => P)
      (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))) := by
    intro I
    have h1 := hν.continuous_comp (g := fun y : ∀ _ : Fin J, DataSpace (n + 1) => y I)
      (continuous_apply I)
    have e1 : (fun N => (fun y : ∀ _ : Fin J, DataSpace (n + 1) => y I) ∘
        jointSampleDatum P (chartObs bJ hb c hc) X A N) =
        sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) := by
      funext N ω
      change jointSampleDatum P (chartObs bJ hb c hc) X A N ω I = _
      rw [hjoint]
    have e2 : ((fun y : ∀ _ : Fin J, DataSpace (n + 1) => y I) ∘ fun z => unpackAll z + A) =
        fun z => unpack I z + A I := by
      funext z
      simp only [Function.comp, Pi.add_apply, unpackAll_apply]
    rw [e1, e2] at h1
    exact h1
  -- the leading-coefficient functional converges by continuous mapping
  have hG : TendstoInDistribution (fun N ω => jointLeadingCoeff bJ h k β lam mult
      (fun I => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω)) atTop
      (fun z => jointLeadingCoeff bJ h k β lam mult (unpackAll z + A)) (fun _ => P)
      (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))) := by
    have h1 := hν.continuous_comp (continuous_jointLeadingCoeff bJ hb h k hk hβ lam mult)
    have e1 : (fun N => jointLeadingCoeff bJ h k β lam mult ∘
        jointSampleDatum P (chartObs bJ hb c hc) X A N) = fun N ω =>
        jointLeadingCoeff bJ h k β lam mult
          (fun I => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω) := by
      funext N ω
      change jointLeadingCoeff bJ h k β lam mult
        (jointSampleDatum P (chartObs bJ hb c hc) X A N ω) = _
      rw [hjoint]
    rw [e1] at h1
    exact h1
  -- the per-chart differences tend to zero in probability
  have hT : ∀ I, TendstoInMeasure P (fun N ω =>
      scaleA lam mult N * dataBoxIntegral n (h I) (k I) β N (bJ I)
        (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω) -
      (if lam = minRatio (h I) (k I) ∧
          multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 = mult - 1 then
        dataBoxCoeff n (h I) (k I) β (bJ I) (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω)
          (minRatio (h I) (k I)) (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1)
      else 0)) atTop (fun _ => 0) := by
    intro I
    have hmin := minRatio_le (h I) (k I)
    have hatt := exists_ratioExp_eq_minRatio (h I) (k I)
    have hμ : ∃ m' : ℕ, minRatio (h I) (k I) = (m' : ℝ) / latticeQ (k I) :=
      exists_latticeQ_eq n (h I) (k I) (hk I) hatt
    have hj : multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 ≤ n := by
      have := multCount_le_card (ratioExp (h I) (k I)) (minRatio (h I) (k I))
      omega
    by_cases hlead : lam = minRatio (h I) (k I) ∧
        multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 = mult - 1
    · -- leading chart: the ordered remainder minus the coefficient
      have hsc : ∀ N, scaleA lam mult N =
          scaleA (minRatio (h I) (k I))
            (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I))) N := by
        intro N
        unfold scaleA
        rw [hlead.1, hlead.2]
      refine tendstoInMeasure_congr_eventually (tendstoInMeasure_orderedRemainder_sub n (h I) (k I)
        (hk I) β hβ (hb I) hμ hj _ _ (hXIconv I) (fun N : ℕ => (N : ℝ))
        tendsto_natCast_atTop_atTop) ?_
      filter_upwards [eventually_ge_atTop 2] with N hN
      funext ω
      rw [if_pos hlead, hsc, scaleA_mul_dataBoxIntegral_eq_orderedRemainder n (h I) (k I) (hk I) hβ
        (hb I) hmin hatt _ hN]
    · -- strictly dominated chart: a vanishing scale ratio times a ball-bounded remainder
      have hstrict : lam < minRatio (h I) (k I) ∨ (lam = minRatio (h I) (k I) ∧
          multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 < mult - 1) := by
        rcases hdom I with hlt | ⟨heq, hle⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, lt_of_le_of_ne hle fun hcontra => hlead ⟨heq, hcontra⟩⟩
      have hr : Tendsto (fun N : ℕ => ‖scaleA lam mult N / scaleA (minRatio (h I) (k I))
          (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I))) N‖) atTop (𝓝 0) := by
        simpa using (tendsto_scaleA_div_scaleA hstrict).norm
      simp only [if_neg hlead, sub_zero]
      refine tendstoInMeasure_zero_of_uniform_on_balls _ _ (fun M hM ε hε => ?_)
        (dataNormBounded_of_tendstoInDistribution _ _ (hXIconv I))
      set B : ℝ := coeffBallBound n (h I) (k I) β (bJ I) (minRatio (h I) (k I))
        (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1) M + 1 with hB
      have hB0 : 0 < B := by
        have := abs_dataBoxCoeff_le_ballBound n (h I) (k I) (hk I) β hβ (hb I)
          (minRatio (h I) (k I)) (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1)
          (x := 0) (by simpa using hM)
        have h0 := abs_nonneg (dataBoxCoeff n (h I) (k I) β (bJ I) 0 (minRatio (h I) (k I))
          (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1))
        rw [hB]; linarith
      have hunif := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_orderedRemainder n (h I)
        (k I) (hk I) β hβ (hb I) hμ hj M) 1 one_pos
      filter_upwards [eventually_ge_atTop 2, tendsto_natCast_atTop_atTop.eventually hunif,
        hr.eventually (gt_mem_nhds (div_pos hε hB0))] with N hN hu hrN ω hω
      rw [← div_mul_cancel₀ (scaleA lam mult N) (scaleA_pos (minRatio (h I) (k I)) _ N).ne',
        mul_assoc, scaleA_mul_dataBoxIntegral_eq_orderedRemainder n (h I) (k I) (hk I) hβ (hb I)
        hmin hatt _ hN, abs_mul]
      have hx : sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω ∈ Metric.closedBall 0 M := by
        rw [mem_closedBall_zero_iff]; exact hω
      have hR : |orderedRemainder n (h I) (k I) β (bJ I)
          (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω) (minRatio (h I) (k I))
          (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1) N| ≤ B := by
        have h1 := hu _ hx
        rw [Real.dist_eq] at h1
        have h2 := abs_dataBoxCoeff_le_ballBound n (h I) (k I) (hk I) β hβ (hb I)
          (minRatio (h I) (k I)) (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1) hω
        rw [hB]
        have := abs_sub_abs_le_abs_sub (orderedRemainder n (h I) (k I) β (bJ I)
          (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω) (minRatio (h I) (k I))
          (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1) N)
          (dataBoxCoeff n (h I) (k I) β (bJ I)
            (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω)
            (minRatio (h I) (k I)) (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1))
        rw [abs_sub_comm] at h1
        linarith
      have hrN' : |scaleA lam mult N / scaleA (minRatio (h I) (k I))
          (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I))) N| ≤ ε / B := by
        rw [← Real.norm_eq_abs]
        exact hrN.le
      calc _ ≤ ε / B * B := mul_le_mul hrN' hR (abs_nonneg _) (by positivity)
        _ = ε := div_mul_cancel₀ ε hB0.ne'
  -- assemble
  have hdiff := tendstoInMeasure_zero_finset_sum Finset.univ fun I _ => hT I
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hG ?_ fun N => ?_
  · have e : ((fun N ω => scaleA lam mult N * coreSum n h k bJ β (fun N => (N : ℝ))
        (fun I N => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N) N ω) -
        fun N ω => jointLeadingCoeff bJ h k β lam mult
          (fun I => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω)) = fun N ω =>
        ∑ I, (scaleA lam mult N * dataBoxIntegral n (h I) (k I) β N (bJ I)
          (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω) -
        (if lam = minRatio (h I) (k I) ∧
            multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 = mult - 1 then
          dataBoxCoeff n (h I) (k I) β (bJ I) (sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) N ω)
            (minRatio (h I) (k I)) (multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1)
        else 0)) := by
      funext N ω
      simp only [Pi.sub_apply, coreSum, jointLeadingCoeff, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [e]
    exact hdiff
  · exact (Finset.measurable_sum _ fun I _ => (measurable_dataBoxIntegral n (h I) (k I) hβ.le
      (Nat.cast_nonneg N) (hb I)).comp (hXIm I N)).const_mul _ |>.aemeasurable

variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **The assembled annealed sample-datum theorem**: for finitely many certified box charts read
from one i.i.d. sample with bounded chart phase observations (`pβM₀² < 2`, `p > 1`), the `ℓ¹` CLT
certificates, zero-phase amplitude data of amplitude mass `≤ M`, and box exponent pairs dominating
the scale `(λ, m)`: `E[A_n(coreSum_n + Rem_n)] → E_ν[∑_{I leading} C_I(unpack_I Z + A_I)]`
whenever `E|A_n Rem_n| → 0`; the limiting functional is `ν`-integrable. -/
theorem tendsto_integral_scaled_coreSum_sampleDatum (hk : ∀ I i, 0 < k I i) {β p M M₀ : ℝ}
    (hβ : 0 < β) (hp : 1 < p) (hpc : p * β * M₀ ^ 2 < 2) (hM : 0 ≤ M) (hM0 : 0 ≤ M₀)
    {lam : ℝ} {mult : ℕ}
    (hdom : ∀ I, lam < minRatio (h I) (k I) ∨
      (lam = minRatio (h I) (k I) ∧
        multCount (ratioExp (h I) (k I)) (minRatio (h I) (k I)) - 1 ≤ mult - 1))
    (hcm : ∀ I γ, Measurable fun x => c I x γ) (hXm : ∀ i, Measurable (X i))
    (hXind : iIndepFun X P) (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hc2 : ∀ I γ, MemLp (fun ω => c I (X 0 ω) γ) 2 P)
    (hsum : ∀ I, Summable fun γ : Fin (n + 1) → ℕ =>
      bJ I ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c I (X 0 ω) γ) ^ 2 ∂P))
    (hobs : ∀ I x, ‖phaseObs (bJ I) (hb I) (c I) (hc I) x‖ ≤ M₀)
    (A : Fin J → DataSpace (n + 1)) (hA : ∀ I, xiCoord (A I) = 0)
    (hAM : ∀ I, mass (etaCoord (A I)) ≤ M) {R : ℕ → Ω → ℝ}
    (hRint : ∀ m, Integrable (fun ω => scaleA lam mult m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA lam mult m * R m ω| ∂P) atTop (𝓝 0)) :
    ∃ ν : ProbabilityMeasure (L1Seq (StackIdx fun _ : Fin J => n)),
      (∀ F : Finset (StackIdx fun _ : Fin J => n),
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))).map (finiteCoords F) =
          gaussianTarget (fun ω => finiteCoords F (stackObs (chartObs bJ hb c hc) (X 0 ω))) P) ∧
      Integrable (fun z => jointLeadingCoeff bJ h k β lam mult (unpackAll z + A))
        (ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))) ∧
      Tendsto (fun m => ∫ ω, scaleA lam mult m *
          (coreSum n h k bJ β (fun m => (m : ℝ))
            (fun I m => sampleDatum (bJ I) (hb I) (c I) (hc I) P X (A I) m) m ω + R m ω) ∂P)
        atTop (𝓝 (∫ z, jointLeadingCoeff bJ h k β lam mult (unpackAll z + A)
          ∂(ν : Measure (L1Seq (StackIdx fun _ : Fin J => n))))) := by
  obtain ⟨ν, hmarg, hcore⟩ := tendstoInDistribution_scaled_coreSum_sampleDatum bJ hb c hc P X h k
    hk hβ hdom hcm hXm hXind hXid hc2 hsum A
  obtain ⟨hint, htend⟩ := tendsto_integral_scaled_assembly_sampleDatum P n h k bJ X hk hβ hp hpc
    hM hM0 hb hdom c hc hcm hXm hXind hXid hobs A hA hAM hcore hRint hrem
  exact ⟨ν, hmarg, hint, htend⟩

end Joint

end Grammar
