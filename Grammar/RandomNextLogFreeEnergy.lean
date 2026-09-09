/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.RandomNextLogLaplace

/-!
# Random next-log free energy

The **uniform logarithmic lemma** (`tendstoUniformlyOn_nextLog_log`): if `log N (g_N − F) → B`
uniformly on `S` with `B` bounded and `F ≥ δ > 0`, then `log N (log g_N − log F) → B/F` uniformly
on `S` (via `|log(1+t) − t| ≤ 2t²` for `|t| ≤ 1/2`).  Applied to the normalised evidence
`z_N(x) = Z_N(x)/(N^{−λ} log^{m−1} N)` on compact admissible sets, with
`−log Z_N(x) − λ log N + (m−1) log log N + log F(x) = −(log z_N(x) − log F(x))`
(`freeEnergyStat_eq`), this gives the **uniform next-log free energy**
`log N (−log Z_N(x) − λ log N + (m−1) log log N + log F(x)) → −B(x)/F(x)`
(`tendstoUniformlyOn_freeEnergyStat`), continuous convergence on `{F > 0}`, and for random
admissible data `X_m ⇒ X` the random next-log free energy jointly with its data
(`randomFreeEnergy_graphLaw_tendsto`).

Positivity of `Z_N(x)` is not assumed: it holds eventually, uniformly on compact admissible sets,
which is all the asymptotic statement needs (`Real.log` is total).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-! ### The logarithmic lemma -/

/-- `|log(1+t) − t| ≤ 2t²` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le_two_sq {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have ht' := abs_le.1 ht
  have hpos : 0 < 1 + t := by linarith
  have hup : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : t / (1 + t) ≤ Real.log (1 + t) := by
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h1
    have : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have h2 : t - t / (1 + t) = t ^ 2 / (1 + t) := by field_simp; ring
  have h3 : t ^ 2 / (1 + t) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg t]
  linarith

variable {ι : Type*} {S : Set ι}

/-- **Uniform logarithmic lemma**: `log N (g_N − F) → B` uniformly, `B` bounded, `F ≥ δ > 0` ⇒
`log N (log g_N − log F) → B/F` uniformly. -/
theorem tendstoUniformlyOn_nextLog_log {g : ℝ → ι → ℝ} {F B : ι → ℝ}
    (hnext : TendstoUniformlyOn (fun N x => Real.log N * (g N x - F x)) B atTop S) {MB : ℝ}
    (hB : ∀ x ∈ S, |B x| ≤ MB) {δ : ℝ} (hδ : 0 < δ) (hfloor : ∀ x ∈ S, δ ≤ F x) :
    TendstoUniformlyOn (fun N x => Real.log N * (Real.log (g N x) - Real.log (F x)))
      (fun x => B x / F x) atTop S := by
  rcases S.eq_empty_or_nonempty with hS | ⟨x₁, hx₁⟩
  · subst hS
    simp [TendstoUniformlyOn]
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hB x₁ hx₁)
  set M := MB + 1 with hM
  have hM0 : 0 < M := by positivity
  rw [Metric.tendstoUniformlyOn_iff] at hnext ⊢
  intro ε hε
  have hrate : Tendsto (fun N : ℝ => 2 * M ^ 2 / δ ^ 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [hnext 1 one_pos, hnext (ε * δ / 2) (by positivity),
    hrate.eventually (gt_mem_nhds (half_pos hε)),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * M / δ + 1)] with N h1 h2 h3 hL x hx
  have hL0 : 0 < Real.log N := by
    have : 0 < 2 * M / δ + 1 := by positivity
    linarith
  have hFx := hfloor x hx
  have hF0 : 0 < F x := by linarith
  -- the normalised increment
  set u := Real.log N * (g N x - F x) with hu
  have hu1 : |u| ≤ M := by
    have := h1 x hx
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub u (B x)
    rw [abs_sub_comm] at this
    linarith [hB x hx]
  set t := (g N x - F x) / F x with ht
  have htu : t = u / (Real.log N * F x) := by
    rw [hu, ht]
    field_simp
  have ht_le : |t| ≤ 1 / 2 := by
    rw [htu, abs_div, abs_of_pos (mul_pos hL0 hF0), div_le_iff₀ (mul_pos hL0 hF0)]
    have : 2 * M / δ + 1 ≤ Real.log N := hL
    have : M ≤ 1 / 2 * (Real.log N * δ) := by
      rw [div_add_one (hδ.ne'), div_le_iff₀ hδ] at this
      linarith
    calc |u| ≤ M := hu1
      _ ≤ 1 / 2 * (Real.log N * δ) := this
      _ ≤ 1 / 2 * (Real.log N * F x) := by gcongr
  have hg0 : 0 < g N x := by
    have : g N x = F x * (1 + t) := by rw [ht]; field_simp; ring
    rw [this]
    have := (abs_le.1 ht_le).1
    exact mul_pos hF0 (by linarith)
  -- decomposition
  have hlog : Real.log (g N x) - Real.log (F x) = Real.log (1 + t) := by
    rw [← Real.log_div hg0.ne' hF0.ne']
    congr 1
    rw [ht]
    field_simp
    ring
  have hdec : Real.log N * (Real.log (g N x) - Real.log (F x)) - B x / F x =
      Real.log N * (Real.log (1 + t) - t) + (u - B x) / F x := by
    rw [hlog, hu, ht]
    field_simp
    ring
  rw [Real.dist_eq, abs_sub_comm, hdec]
  have hterm1 : |Real.log N * (Real.log (1 + t) - t)| ≤ 2 * M ^ 2 / δ ^ 2 / Real.log N := by
    rw [abs_mul, abs_of_pos hL0]
    calc Real.log N * |Real.log (1 + t) - t| ≤ Real.log N * (2 * t ^ 2) := by
          gcongr
          exact abs_log_one_add_sub_le_two_sq ht_le
      _ = 2 * u ^ 2 / (Real.log N * F x ^ 2) := by
          rw [htu]
          field_simp
      _ ≤ 2 * M ^ 2 / (Real.log N * δ ^ 2) := by
          have hu2 : u ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.1 hu1).1 (abs_le.1 hu1).2
          exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hu2 (by norm_num))
            (by positivity) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hFx 2) hL0.le)
      _ = 2 * M ^ 2 / δ ^ 2 / Real.log N := by
          field_simp
  have hterm2 : |(u - B x) / F x| < ε / 2 := by
    have := h2 x hx
    rw [Real.dist_eq, abs_sub_comm] at this
    rw [abs_div, abs_of_pos hF0, div_lt_iff₀ hF0]
    calc |u - B x| < ε * δ / 2 := this
      _ ≤ ε / 2 * F x := by
          rw [show ε * δ / 2 = ε / 2 * δ by ring]
          gcongr
  calc |Real.log N * (Real.log (1 + t) - t) + (u - B x) / F x|
      ≤ |Real.log N * (Real.log (1 + t) - t)| + |(u - B x) / F x| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        have h3' : 2 * M ^ 2 / δ ^ 2 / Real.log N < ε / 2 := h3
        linarith
    _ = ε := add_halves ε

/-! ### The free-energy statistic -/

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) (l : ℝ)

/-- The normalised next-log free-energy statistic
`log N (−log Z_N(x) − λ log N + (m−1) log log N + log F(x))`. -/
noncomputable def freeEnergyStat (N : ℝ) (x : DataSpace (n + 1)) : ℝ :=
  Real.log N * (-Real.log (dataBoxIntegral n h k β N 1 x) - l * Real.log N +
    ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log N) +
    Real.log (dataLead n h k (β := β) l x))

/-- For `N > 1` and positive normalised evidence, the free-energy statistic is
`−log N (log z_N(x) − log F(x))`. -/
theorem freeEnergyStat_eq {N : ℝ} (hN : 1 < N) (x : DataSpace (n + 1))
    (hz : 0 < energyDen n h k (β := β) l N x) :
    freeEnergyStat n h k (β := β) l N x =
      -(Real.log N * (Real.log (energyDen n h k (β := β) l N x) -
        Real.log (dataLead n h k (β := β) l x))) := by
  have hN0 : 0 < N := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos hN
  have hden : 0 < N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) := by positivity
  have hZ : dataBoxIntegral n h k β N 1 x = energyDen n h k (β := β) l N x *
      (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
    unfold energyDen
    rw [div_mul_cancel₀ _ hden.ne']
  unfold freeEnergyStat
  rw [hZ, Real.log_mul hz.ne' hden.ne', Real.log_mul (Real.rpow_pos_of_pos hN0 _).ne'
    (pow_pos hL0 _).ne', Real.log_rpow hN0, Real.log_pow]
  ring

variable (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
  (hm : 2 ≤ multCount (ratioExp h k) l)

include hk hβ hmin hatt hm in
/-- **Uniform next-log free energy on compact admissible sets**:
`log N (−log Z_N(x) − λ log N + (m−1) log log N + log F(x)) → −B(x)/F(x)` uniformly. -/
theorem tendstoUniformlyOn_freeEnergyStat {K : Set (DataSpace (n + 1))} (hK : IsCompact K)
    (hKpos : ∀ x ∈ K, 0 < dataLead n h k (β := β) l x) :
    TendstoUniformlyOn (fun N x => freeEnergyStat n h k (β := β) l N x)
      (fun x => -(dataSecond n h k (β := β) l x / dataLead n h k (β := β) l x)) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    simp [TendstoUniformlyOn]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hZ : TendstoUniformlyOn (fun N x => Real.log N * (energyDen n h k (β := β) l N x -
      dataLead n h k (β := β) l x)) (dataSecond n h k (β := β) l) atTop K :=
    (tendstoUniformlyOn_spatialTwoTerm n h k hk hβ hmin hatt hm R).mono hR
  obtain ⟨MB, hMB⟩ :=
    hK.exists_bound_of_continuousOn (continuous_dataSecond n h k hk hβ l).continuousOn
  obtain ⟨x₀, hx₀, hmin₀⟩ :=
    hK.exists_isMinOn hKne (continuous_dataLead n h k hk hβ l).continuousOn
  have hfloor : ∀ x ∈ K, dataLead n h k (β := β) l x₀ ≤ dataLead n h k (β := β) l x :=
    fun x hx => hmin₀ hx
  have hMB' : ∀ x ∈ K, |dataSecond n h k (β := β) l x| ≤ MB := fun x hx =>
    (Real.norm_eq_abs _).symm.trans_le (hMB x hx)
  have hlog := tendstoUniformlyOn_nextLog_log hZ hMB' (hKpos x₀ hx₀) hfloor
  refine (hlog.neg).congr ?_
  filter_upwards [eventually_floor_of_nextLog hZ hMB' (hKpos x₀ hx₀) hfloor,
    eventually_gt_atTop (1 : ℝ)] with N hN hN1 x hx
  simp only [Pi.neg_apply]
  rw [freeEnergyStat_eq n h k l hN1 x (by linarith [hN x hx, hKpos x₀ hx₀])]

/-! ### The random theorem on the admissible domain -/

/-- The free-energy statistic on the admissible domain. -/
noncomputable def freeEnergyStatU (N : ℝ) (x : AdmissibleData n h k (β := β) l) : ℝ :=
  freeEnergyStat n h k (β := β) l N x.1

include hk hβ in
theorem measurable_freeEnergyStatU {N : ℝ} (hN : 0 ≤ N) :
    Measurable (freeEnergyStatU n h k (β := β) l N) := by
  unfold freeEnergyStatU freeEnergyStat
  refine (measurable_const.mul (((Real.measurable_log.comp
    (measurable_dataBoxIntegral n h k hβ.le hN one_pos)).neg.sub measurable_const).add
    measurable_const |>.add (Real.measurable_log.comp
      (continuous_dataLead n h k hk hβ l).measurable))).comp measurable_subtype_coe

include hk hβ in
theorem continuous_freeEnergyCorrectionU :
    Continuous fun x : AdmissibleData n h k (β := β) l =>
      -(dataSecond n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1) := by
  have hF : Continuous fun x : AdmissibleData n h k (β := β) l => dataLead n h k (β := β) l x.1 :=
    (continuous_dataLead n h k hk hβ l).comp continuous_subtype_val
  exact (Continuous.div ((continuous_dataSecond n h k hk hβ l).comp continuous_subtype_val) hF
    fun x => x.2.ne').neg

variable (Nseq : ℕ → ℝ) (hN1 : ∀ m, 1 < Nseq m) (hN : Tendsto Nseq atTop atTop)

include hk hβ hmin hatt hm hN in
theorem continuouslyConverges_freeEnergyStatU :
    ContinuouslyConverges (fun m => freeEnergyStatU n h k (β := β) l (Nseq m))
      fun x : AdmissibleData n h k (β := β) l =>
        -(dataSecond n h k (β := β) l x.1 / dataLead n h k (β := β) l x.1) := by
  refine continuouslyConverges_of_tendstoUniformlyOn_compacts
    (continuous_freeEnergyCorrectionU n h k hk hβ l) fun K hK => ?_
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hpos : ∀ x ∈ Subtype.val '' K, 0 < dataLead n h k (β := β) l x := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h1 := tendstoUniformlyOn_comp_seq
    (tendstoUniformlyOn_freeEnergyStat n h k hk hβ l hmin hatt hm hK' hpos) hN
  exact (h1.comp Subtype.val).mono (Set.subset_preimage_image _ _)

include hk hβ hmin hatt hm hN1 hN in
/-- **Random next-log free energy, jointly with its data**: for random admissible data `X_m ⇒ X`
and `N_m → ∞`,
`(X_m, log N_m (−log Z_{N_m}(X_m) − λ log N_m + (m−1) log log N_m + log F(X_m)))
  ⇒ (X, −B(X)/F(X))`. -/
theorem randomFreeEnergy_graphLaw_tendsto
    {μ : ℕ → ProbabilityMeasure (AdmissibleData n h k (β := β) l)}
    {μ₀ : ProbabilityMeasure (AdmissibleData n h k (β := β) l)} (hμ : Tendsto μ atTop (𝓝 μ₀)) :
    Tendsto (fun m => graphLaw (μ m)
        (measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le))) atTop
      (𝓝 (graphLaw μ₀ (continuous_freeEnergyCorrectionU n h k hk hβ l).measurable)) :=
  haveI := polishSpace_admissibleData n h k hk hβ l
  tendsto_graphLaw_of_continuouslyConverges hμ (tight_of_tendsto_polish hμ)
    (fun m => measurable_freeEnergyStatU n h k hk hβ l (zero_le_one.trans (hN1 m).le))
    (continuouslyConverges_freeEnergyStatU n h k hk hβ l hmin hatt hm Nseq hN)

end Grammar
