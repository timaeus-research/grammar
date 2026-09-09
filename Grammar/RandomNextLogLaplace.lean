/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DataTilt
import Grammar.DataSpaceSeparable

/-!
# Random next-log posterior Laplace transforms

For `s ≥ 0` the posterior Laplace transform `E_{Q_N(x)}[e^{−sNK}]` is the quotient of the chart
integral of the tilted datum at temperature `β + s` by the chart integral of `x`
(`laplaceStat_eq`).  The uniform two-term theorem for the tilted data at temperature `β + s`
(`tendstoUniformlyOn_laplaceNum`, via the Lipschitz tilt), the uniform quotient theorem on compact
admissible sets (`tendstoUniformlyOn_nextLog_div_compact`, positive minimum of `F`), the
compact-uniform bridge and the graph-law transfer on the Polish admissible domain give the **random
next-log posterior Laplace transform**: for random admissible data `X_m ⇒ X` and `N_m → ∞`,
`(X_m, log N_m (E_{Q_{N_m}(X_m)}[e^{−sN_mK}] − P_s(X_m))) ⇒ (X, C_s(X))`
(`randomLaplace_graphLaw_tendsto`), with `P_s = A_s/F`, `C_s = (B_s F − A_s B)/F²`.  At `s = 0` the
leading ratio is `1` and the correction is `0` (`laplaceLead_zero`, `laplaceCorrection_zero`).

Fixed `s` only: no locally uniform statement in `s` is claimed.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-! ### Uniform next-log quotients on compact admissible sets -/

/-- The uniform quotient theorem on a compact set where `F > 0`, from ball-uniform two-term
expansions of numerator and denominator with continuous coefficients. -/
theorem tendstoUniformlyOn_nextLog_div_compact {P : Type*} [SeminormedAddCommGroup P]
    {a z : ℝ → P → ℝ} {A F BA BZ : P → ℝ}
    (hA : ∀ R : ℝ, TendstoUniformlyOn (fun N x => Real.log N * (a N x - A x)) BA atTop
      (Metric.closedBall 0 R))
    (hZ : ∀ R : ℝ, TendstoUniformlyOn (fun N x => Real.log N * (z N x - F x)) BZ atTop
      (Metric.closedBall 0 R))
    (hAc : Continuous A) (hFc : Continuous F) (hBAc : Continuous BA) (hBZc : Continuous BZ)
    {K : Set P} (hK : IsCompact K) (hKpos : ∀ x ∈ K, 0 < F x) :
    TendstoUniformlyOn (fun N x => Real.log N * (a N x / z N x - A x / F x))
      (fun x => (BA x * F x - A x * BZ x) / F x ^ 2) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    simp [TendstoUniformlyOn]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn hBAc.continuousOn
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn hBZc.continuousOn
  obtain ⟨x₀, hx₀, hmin₀⟩ := hK.exists_isMinOn hKne hFc.continuousOn
  exact tendstoUniformlyOn_nextLog_div (S := K) ((hA R).mono hR) ((hZ R).mono hR)
    (MA := max M1 M2) (MB := max M3 M4)
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM1 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM2 x hx).trans (le_max_right _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM3 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM4 x hx).trans (le_max_right _ _)))
    (hKpos x₀ hx₀) fun x hx => hmin₀ hx

/-! ### The Laplace statistic -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)
  (s : ℝ)

/-- The normalised Laplace numerator `Z^{β+s}_N(tilt x)/(N^{−λ} log^{m−1} N)`. -/
noncomputable def laplaceNum (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  dataBoxIntegral n h k (β + s) N 1 (dataTilt (β / (β + s)) x) /
    (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))

/-- The posterior Laplace transform `E_{Q_N(x)}[e^{−sNK}]` as a quotient of normalised chart
integrals. -/
noncomputable def laplaceStat (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  laplaceNum n h k (β := β) l s N x / energyDen n h k (β := β) l N x

/-- The leading Laplace coefficient `A_s(x) = F_{β+s}(tilt x)`. -/
noncomputable def laplaceLead (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n h k (β + s) 1 (dataTilt (β / (β + s)) x) l (multCount (ratioExp h k) l - 1)

/-- The second Laplace coefficient `B_s(x) = B_{β+s}(tilt x)`. -/
noncomputable def laplaceSecond (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n h k (β + s) 1 (dataTilt (β / (β + s)) x) l (multCount (ratioExp h k) l - 2)

/-- The next-log Laplace correction `C_s(x) = (B_s F − A_s B)/F²`. -/
noncomputable def laplaceCorrection (x : DataSpace (n + 1)) : ℝ :=
  (laplaceSecond n h k (β := β) l s x * dataLead n h k (β := β) l x -
    laplaceLead n h k (β := β) l s x * dataSecond n h k (β := β) l x) /
      dataLead n h k (β := β) l x ^ 2

include hβ in
/-- **The statistic is the posterior Laplace transform** of the represented phase and amplitude. -/
theorem laplaceStat_eq (hs : 0 ≤ s) {N : ℝ} (hN : 1 < N) (x : DataSpace (n + 1)) :
    laplaceStat n h k (β := β) l s N x =
      spatialLaplace n h k β N (dataPhase x) (dataAmplitude x) (fun _ => 1) s := by
  unfold laplaceStat laplaceNum energyDen spatialLaplace
  rw [dataBoxIntegral_dataTilt n h k hβ hs, dataBoxIntegral_one]
  simp only [one_mul]
  have hden : N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  rw [div_div_div_cancel_right₀ hden]

include hk hβ in
theorem continuous_laplaceLead (hs : 0 ≤ s) : Continuous (laplaceLead n h k (β := β) l s) :=
  (continuous_dataBoxCoeff_one n h k hk (by linarith) l _).comp (continuous_dataTilt _)

include hk hβ in
theorem continuous_laplaceSecond (hs : 0 ≤ s) : Continuous (laplaceSecond n h k (β := β) l s) :=
  (continuous_dataBoxCoeff_one n h k hk (by linarith) l _).comp (continuous_dataTilt _)

include hβ in
theorem measurable_laplaceStat (hs : 0 ≤ s) {N : ℝ} (hN : 0 ≤ N) :
    Measurable (laplaceStat n h k (β := β) l s N) := by
  unfold laplaceStat laplaceNum energyDen
  exact (((measurable_dataBoxIntegral n h k (by linarith) hN one_pos).comp
    (continuous_dataTilt _).measurable).div_const _).div
    ((measurable_dataBoxIntegral n h k hβ.le hN one_pos).div_const _)

theorem laplaceLead_zero (x : DataSpace (n + 1)) (hβ : 0 < β) :
    laplaceLead n h k (β := β) l 0 x = dataLead n h k (β := β) l x := by
  unfold laplaceLead dataLead
  rw [add_zero, div_self hβ.ne', dataTilt_one]

theorem laplaceSecond_zero (x : DataSpace (n + 1)) (hβ : 0 < β) :
    laplaceSecond n h k (β := β) l 0 x = dataSecond n h k (β := β) l x := by
  unfold laplaceSecond dataSecond
  rw [add_zero, div_self hβ.ne', dataTilt_one]

/-- At `s = 0` the next-log Laplace correction vanishes. -/
theorem laplaceCorrection_zero (x : DataSpace (n + 1)) (hβ : 0 < β) :
    laplaceCorrection n h k (β := β) l 0 x = 0 := by
  unfold laplaceCorrection
  rw [laplaceLead_zero n h k l x hβ, laplaceSecond_zero n h k l x hβ, mul_comm, sub_self, zero_div]

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l)

include hk hβ hmin hatt hm in
/-- The uniform two-term expansion of the Laplace numerator on data balls (tilted data at
temperature `β + s`). -/
theorem tendstoUniformlyOn_laplaceNum (hs : 0 ≤ s) (R : ℝ) :
    TendstoUniformlyOn (fun N x => Real.log N * (laplaceNum n h k (β := β) l s N x -
        laplaceLead n h k (β := β) l s x)) (laplaceSecond n h k (β := β) l s) atTop
      (Metric.closedBall 0 R) := by
  have hβs : 0 < β + s := by linarith
  have h1 := (tendstoUniformlyOn_spatialTwoTerm n h k hk hβs hmin hatt hm
    (max 1 |β / (β + s)| * R)).comp (dataTilt (β / (β + s)))
  have hsub : Metric.closedBall (0 : DataSpace (n + 1)) R ⊆
      dataTilt (β / (β + s)) ⁻¹' Metric.closedBall 0 (max 1 |β / (β + s)| * R) := fun x hx => by
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hx ⊢
    exact (norm_dataTilt_le _ x).trans (mul_le_mul_of_nonneg_left hx (by positivity))
  have h2 := h1.mono hsub
  simp only [laplaceNum, laplaceLead, laplaceSecond]
  exact h2

include hk hβ hmin hatt hm in
/-- **Uniform next-log expansion of the posterior Laplace transform on compact admissible sets.** -/
theorem tendstoUniformlyOn_laplaceStat (hs : 0 ≤ s) {K : Set (DataSpace (n + 1))}
    (hK : IsCompact K) (hKpos : ∀ x ∈ K, 0 < dataLead n h k (β := β) l x) :
    TendstoUniformlyOn (fun N x => Real.log N * (laplaceStat n h k (β := β) l s N x -
        laplaceLead n h k (β := β) l s x / dataLead n h k (β := β) l x))
      (laplaceCorrection n h k (β := β) l s) atTop K :=
  tendstoUniformlyOn_nextLog_div_compact
    (tendstoUniformlyOn_laplaceNum n h k hk hβ l s hmin hatt hm hs)
    (tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm)
    (continuous_laplaceLead n h k hk hβ l s hs) (continuous_dataLead n h k hk hβ l)
    (continuous_laplaceSecond n h k hk hβ l s hs) (continuous_dataSecond n h k hk hβ l) hK hKpos

/-! ### The random theorem on the admissible domain -/

/-- The centred, log-amplified Laplace statistic on the admissible domain. -/
noncomputable def laplaceStatU (N : ℝ) (x : AdmissibleData n h k (β := β) l) : ℝ :=
  Real.log N * (laplaceStat n h k (β := β) l s N x.1 -
    laplaceLead n h k (β := β) l s x.1 / dataLead n h k (β := β) l x.1)

include hk hβ in
theorem measurable_laplaceStatU (hs : 0 ≤ s) {N : ℝ} (hN : 0 ≤ N) :
    Measurable (laplaceStatU n h k (β := β) l s N) := by
  unfold laplaceStatU
  exact (measurable_const.mul ((measurable_laplaceStat n h k hβ l s hs hN).sub
    ((continuous_laplaceLead n h k hk hβ l s hs).measurable.div
      (continuous_dataLead n h k hk hβ l).measurable))).comp measurable_subtype_coe

include hk hβ in
theorem continuous_laplaceCorrectionU (hs : 0 ≤ s) :
    Continuous fun x : AdmissibleData n h k (β := β) l =>
      laplaceCorrection n h k (β := β) l s x.1 := by
  unfold laplaceCorrection
  have hF : Continuous fun x : AdmissibleData n h k (β := β) l => dataLead n h k (β := β) l x.1 :=
    (continuous_dataLead n h k hk hβ l).comp continuous_subtype_val
  refine Continuous.div ?_ (hF.pow 2) fun x => pow_ne_zero _ x.2.ne'
  exact (((continuous_laplaceSecond n h k hk hβ l s hs).comp continuous_subtype_val).mul hF).sub
    (((continuous_laplaceLead n h k hk hβ l s hs).comp continuous_subtype_val).mul
      ((continuous_dataSecond n h k hk hβ l).comp continuous_subtype_val))

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hm hN in
theorem continuouslyConverges_laplaceStatU (hs : 0 ≤ s) :
    ContinuouslyConverges (fun m => laplaceStatU n h k (β := β) l s (Nseq m))
      fun x : AdmissibleData n h k (β := β) l => laplaceCorrection n h k (β := β) l s x.1 := by
  refine continuouslyConverges_of_tendstoUniformlyOn_compacts
    (continuous_laplaceCorrectionU n h k hk hβ l s hs) fun K hK => ?_
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hpos : ∀ x ∈ Subtype.val '' K, 0 < dataLead n h k (β := β) l x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h1 := tendstoUniformlyOn_comp_seq
    (tendstoUniformlyOn_laplaceStat n h k hk hβ l s hmin hatt hm hs hK' hpos) hN
  exact (h1.comp Subtype.val).mono (Set.subset_preimage_image _ _)

include hk hβ hmin hatt hm hN1 hN in
/-- **Random next-log posterior Laplace transform, jointly with its data**: for random admissible
data `X_m ⇒ X` and `N_m → ∞`,
`(X_m, log N_m (E_{Q_{N_m}(X_m)}[e^{−sN_mK}] − P_s(X_m))) ⇒ (X, C_s(X))`. -/
theorem randomLaplace_graphLaw_tendsto (hs : 0 ≤ s)
    {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_laplaceStatU n h k hk hβ l s hs (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_laplaceCorrectionU n h k hk hβ l s hs).measurable)) :=
  haveI := polishSpace_admissibleData n h k hk hβ l
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto_polish hμ)
    (fun m => measurable_laplaceStatU n h k hk hβ l s hs (zero_le_one.trans (hN1 m).le))
    (continuouslyConverges_laplaceStatU n h k hk hβ l s hmin hatt hm Nseq hN hs)

end Grammar
