/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomNextLogEvidence
import Grammar.SpatialEnergyCorrection

/-!
# Random next-log posterior statistics: the energy mean

On the admissible data domain `U = {x | F(x) > 0}` (open, since `F` is continuous) the posterior
energy mean `E_{Q_N(x)}[NK] = N Z^{h+2k}_N(x)/Z^h_N(x)` (`energyStat_eq`) has the uniform next-log
expansion `log N (E_{Q_N(x)}[NK] − A(x)/F(x)) → c₂(x) = (B_A F − A B_Z)/F²` on every compact subset
of `U` (`tendstoUniformlyOn_energyStat`: the uniform two-term theorem for the shifted weight
`h + 2k` at exponent `λ + 1`, the quotient theorem, and the positive minimum of `F` on the compact
set).  Hence the statistic converges continuously on `U` (`continuouslyConverges_energyStat`) and
for random admissible data `X_m ⇒ X` (uniformly tight laws on `U`) and `N_m → ∞`,
`(X_m, log N_m (E_{Q_{N_m}(X_m)}[N_m K] − μ(X_m))) ⇒ (X, c₂(X))`
(`randomEnergyMean_graphLaw_tendsto`) — the random next-log posterior energy correction.

No common deterministic floor is needed: compactness supplies it on each compact subset of `U`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)

/-- The leading coefficient `F(x) = C_{λ,m−1}(x)` of a datum. -/
noncomputable def dataLead (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1)

/-- The admissible data domain `U = {x | F(x) > 0}`. -/
def AdmissibleData : Type := {x : DataSpace (n + 1) // 0 < dataLead n h k (β := β) l x}

noncomputable instance : MetricSpace (AdmissibleData n h k (β := β) l) := Subtype.metricSpace
noncomputable instance : MeasurableSpace (AdmissibleData n h k (β := β) l) :=
  Subtype.instMeasurableSpace
instance : BorelSpace (AdmissibleData n h k (β := β) l) := Subtype.borelSpace _

/-- The normalised numerator family `Z^{h+2k}_N(x)/(N^{−(λ+1)} log^{m−1} N)`. -/
noncomputable def energyNum (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  dataBoxIntegral n (fun i => h i + 2 * k i) k β N 1 x /
    (N ^ (-(l + 1)) * Real.log N ^ (multCount (ratioExp h k) l - 1))

/-- The normalised denominator family `Z^h_N(x)/(N^{−λ} log^{m−1} N)`. -/
noncomputable def energyDen (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  dataBoxIntegral n h k β N 1 x / (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))

/-- The posterior energy mean of a datum, `E_{Q_N(x)}[NK]`. -/
noncomputable def energyStat (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  energyNum n h k (β := β) l N x / energyDen n h k (β := β) l N x

/-- The shifted leading coefficient `A(x) = C^{h+2k}_{λ+1,m−1}(x)`. -/
noncomputable def energyLead (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n (fun i => h i + 2 * k i) k β 1 x (l + 1) (multCount (ratioExp h k) l - 1)

/-- The shifted second coefficient `B_A(x) = C^{h+2k}_{λ+1,m−2}(x)`. -/
noncomputable def energySecond (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n (fun i => h i + 2 * k i) k β 1 x (l + 1) (multCount (ratioExp h k) l - 2)

/-- The second coefficient `B(x) = C_{λ,m−2}(x)` of the evidence. -/
noncomputable def dataSecond (x : DataSpace (n + 1)) : ℝ :=
  dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 2)

/-- The next-log energy correction `c₂(x) = (B_A F − A B)/F²`. -/
noncomputable def energyCorrection (x : DataSpace (n + 1)) : ℝ :=
  (energySecond n h k (β := β) l x * dataLead n h k (β := β) l x -
    energyLead n h k (β := β) l x * dataSecond n h k (β := β) l x) / dataLead n h k (β := β) l x ^ 2

/-- **The statistic is the posterior energy mean** of the represented phase and amplitude
(`N > 0`, `log N ≠ 0`). -/
theorem energyStat_eq {N : ℝ} (hN : 1 < N) (x : DataSpace (n + 1)) :
    energyStat n h k (β := β) l N x =
      spatialEnergyMean n h k β N (dataPhase x) (dataAmplitude x) := by
  unfold energyStat energyNum energyDen
  rw [spatialEnergyMean_eq, ← dataBoxIntegral_one, ← dataBoxIntegral_one]
  have hN0 : 0 < N := by linarith
  have hL : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hN).ne'
  have h1 : N ^ (-(l + 1)) = N ^ (-l) * N⁻¹ := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  rw [h1]
  have hNl : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  field_simp

include hk hβ in
theorem continuous_dataLead : Continuous (dataLead n h k (β := β) l) :=
  continuous_dataBoxCoeff_one n h k hk hβ l _

include hk hβ in
theorem continuous_energyLead : Continuous (energyLead n h k (β := β) l) :=
  continuous_taylorTree_coeff n _ k hk β hβ one_pos _ _

include hk hβ in
theorem continuous_energySecond : Continuous (energySecond n h k (β := β) l) :=
  continuous_taylorTree_coeff n _ k hk β hβ one_pos _ _

include hk hβ in
theorem continuous_dataSecond : Continuous (dataSecond n h k (β := β) l) :=
  continuous_dataBoxCoeff_one n h k hk hβ l _

include hβ in
theorem measurable_energyStat {N : ℝ} (hN : 0 ≤ N) :
    Measurable (energyStat n h k (β := β) l N) := by
  unfold energyStat energyNum energyDen
  exact ((measurable_dataBoxIntegral n _ k hβ.le hN one_pos).div_const _).div
    ((measurable_dataBoxIntegral n h k hβ.le hN one_pos).div_const _)

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l)

include hk hβ hmin hatt hm in
/-- The uniform two-term expansion of the shifted numerator on data balls. -/
theorem tendstoUniformlyOn_energyNum (R : ℝ) :
    TendstoUniformlyOn (fun N x => Real.log N * (energyNum n h k (β := β) l N x -
        energyLead n h k (β := β) l x)) (energySecond n h k (β := β) l) atTop
      (Metric.closedBall 0 R) := by
  have := tendstoUniformlyOn_spatialTwoTerm n (fun i => h i + 2 * k i) k hk hβ
    (hmin_shift h k hk hmin) (hatt_shift h k hk hatt) (by rwa [multCount_shift h k hk l]) R
  rw [multCount_shift h k hk l] at this
  exact this

include hk hβ hmin hatt hm in
/-- **Uniform next-log expansion of the posterior energy mean on compact admissible sets**:
on a compact `K ⊆ {F > 0}`, `log N (E_{Q_N(x)}[NK] − A(x)/F(x)) → c₂(x)` uniformly. -/
theorem tendstoUniformlyOn_energyStat {K : Set (DataSpace (n + 1))} (hK : IsCompact K)
    (hKpos : ∀ x ∈ K, 0 < dataLead n h k (β := β) l x) :
    TendstoUniformlyOn (fun N x => Real.log N * (energyStat n h k (β := β) l N x -
        energyLead n h k (β := β) l x / dataLead n h k (β := β) l x))
      (energyCorrection n h k (β := β) l) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    simp [TendstoUniformlyOn]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hA := (tendstoUniformlyOn_energyNum n h k hk hβ l hmin hatt hm R).mono hR
  have hZ := (tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm R).mono hR
  -- bounds on the compact set
  obtain ⟨M1, hM1⟩ :=
    hK.exists_bound_of_continuousOn (continuous_energyLead n h k hk hβ l).continuousOn
  obtain ⟨M2, hM2⟩ :=
    hK.exists_bound_of_continuousOn (continuous_dataLead n h k hk hβ l).continuousOn
  obtain ⟨M3, hM3⟩ :=
    hK.exists_bound_of_continuousOn (continuous_energySecond n h k hk hβ l).continuousOn
  obtain ⟨M4, hM4⟩ :=
    hK.exists_bound_of_continuousOn (continuous_dataSecond n h k hk hβ l).continuousOn
  -- the positive floor
  obtain ⟨x₀, hx₀, hmin₀⟩ :=
    hK.exists_isMinOn hKne (continuous_dataLead n h k hk hβ l).continuousOn
  have hfloor : ∀ x ∈ K, dataLead n h k (β := β) l x₀ ≤ dataLead n h k (β := β) l x :=
    fun x hx => hmin₀ hx
  have := tendstoUniformlyOn_nextLog_div (S := K) hA hZ (MA := max M1 M2) (MB := max M3 M4)
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM1 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM2 x hx).trans (le_max_right _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM3 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM4 x hx).trans (le_max_right _ _)))
    (hKpos x₀ hx₀) hfloor
  exact this

/-! ### The admissible domain and the random theorem -/

/-- The centred, log-amplified energy statistic on the admissible domain. -/
noncomputable def energyStatU (N : ℝ) (x : AdmissibleData n h k (β := β) l) : ℝ :=
  Real.log N * (energyStat n h k (β := β) l N x.1 -
    energyLead n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1)

include hk hβ in
theorem measurable_energyStatU {N : ℝ} (hN : 0 ≤ N) :
    Measurable (energyStatU n h k (β := β) l N) := by
  unfold energyStatU
  exact (measurable_const.mul (((measurable_energyStat n h k hβ l hN).sub
    ((continuous_energyLead n h k hk hβ l).measurable.div
      (continuous_dataLead n h k hk hβ l).measurable)))).comp measurable_subtype_coe

include hk hβ in
/-- The energy correction is continuous on the admissible domain (`F > 0` there). -/
theorem continuous_energyCorrectionU :
    Continuous fun x : AdmissibleData n h k (β := β) l =>
      energyCorrection n h k (β := β) l x.1 := by
  unfold energyCorrection
  have hF : Continuous fun x : AdmissibleData n h k (β := β) l => dataLead n h k (β := β) l x.1 :=
    (continuous_dataLead n h k hk hβ l).comp continuous_subtype_val
  refine Continuous.div ?_ (hF.pow 2) fun x => pow_ne_zero _ x.2.ne'
  exact (((continuous_energySecond n h k hk hβ l).comp continuous_subtype_val).mul hF).sub
    (((continuous_energyLead n h k hk hβ l).comp continuous_subtype_val).mul
      ((continuous_dataSecond n h k hk hβ l).comp continuous_subtype_val))

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hm hN in
/-- **Continuous convergence of the energy statistic on the admissible domain**. -/
theorem continuouslyConverges_energyStatU :
    ContinuouslyConverges (fun m => energyStatU n h k (β := β) l (Nseq m))
      fun x : AdmissibleData n h k (β := β) l => energyCorrection n h k (β := β) l x.1 := by
  refine continuouslyConverges_of_tendstoUniformlyOn_compacts
    (continuous_energyCorrectionU n h k hk hβ l) fun K hK => ?_
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hpos : ∀ x ∈ Subtype.val '' K, 0 < dataLead n h k (β := β) l x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h1 := tendstoUniformlyOn_comp_seq
    (tendstoUniformlyOn_energyStat n h k hk hβ l hmin hatt hm hK' hpos) hN
  exact (h1.comp Subtype.val).mono (Set.subset_preimage_image _ _)

variable {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
  {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀))

include hk hβ hmin hatt hm hN1 hN hμ in
/-- **Random next-log posterior energy correction, jointly with its data**: for random admissible
data `X_m ⇒ X` (uniformly tight laws on `{F > 0}`) and `N_m → ∞`,
`(X_m, log N_m (E_{Q_{N_m}(X_m)}[N_m K] − A(X_m)/F(X_m))) ⇒ (X, c₂(X))`. -/
theorem randomEnergyMean_graphLaw_tendsto
    (htight : ∀ δ : ℝ, 0 < δ → ∃ C : Set (AdmissibleData n h k (β := β) l), IsCompact C ∧
      ∀ m, ((μ m : Measure (AdmissibleData n h k (β := β) l)) Cᶜ).toReal ≤ δ) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_energyCorrectionU n h k hk hβ l).measurable)) :=
  tendsto_graphLaw_of_continuouslyConverges hμ htight
    (fun m => measurable_energyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le))
    (continuouslyConverges_energyStatU n h k hk hβ l hmin hatt hm Nseq hN)

/-! ### Identification with the explicit coefficients -/

include hk hβ hmin hatt in
/-- `A(x)/F(x)` is the limiting posterior energy mean `μ(ξ_x, η_x)` of LXXXI. -/
theorem energyLead_div_dataLead_eq (x : DataSpace (n + 1)) :
    energyLead n h k (β := β) l x / dataLead n h k (β := β) l x =
      spatialFace (fun i => h i + 2 * k i) k (l + 1) β (dataPhase x) (dataAmplitude x) /
        spatialFace h k l β (dataPhase x) (dataAmplitude x) := by
  unfold energyLead dataLead
  rw [(dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).2]
  have := (dataBoxCoeff_spatialFace n (fun i => h i + 2 * k i) k hk hβ (hmin_shift h k hk hmin)
    (hatt_shift h k hk hatt) x).2
  rw [multCount_shift h k hk l] at this
  rw [this]

include hk hβ hmin hatt hm in
/-- `c₂(x)` is the explicit next-log energy correction of LXXXI. -/
theorem energyCorrection_eq (x : DataSpace (n + 1)) :
    energyCorrection n h k (β := β) l x =
      (spatialFace h k l β (dataPhase x) (dataAmplitude x) *
          spatialSecondFace (fun i => h i + 2 * k i) k (l + 1) β (dataPhase x) (dataAmplitude x) -
        spatialFace (fun i => h i + 2 * k i) k (l + 1) β (dataPhase x) (dataAmplitude x) *
          spatialSecondFace h k l β (dataPhase x) (dataAmplitude x)) /
        spatialFace h k l β (dataPhase x) (dataAmplitude x) ^ 2 := by
  unfold energyCorrection energyLead dataLead energySecond dataSecond
  rw [(dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).2,
    dataBoxCoeff_spatialSecondFace n h k hk hβ hmin hatt hm x]
  have h1 := (dataBoxCoeff_spatialFace n (fun i => h i + 2 * k i) k hk hβ (hmin_shift h k hk hmin)
    (hatt_shift h k hk hatt) x).2
  have h2 := dataBoxCoeff_spatialSecondFace n (fun i => h i + 2 * k i) k hk hβ
    (hmin_shift h k hk hmin) (hatt_shift h k hk hatt) (by rwa [multCount_shift h k hk l]) x
  rw [multCount_shift h k hk l] at h1 h2
  rw [h1, h2]
  ring

end Grammar
