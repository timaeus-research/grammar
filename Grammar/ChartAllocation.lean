/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.UniformAssembly

/-!
# First corrections to chart allocations and assembled quotients

Generic finite-chart setting of `UniformAssembly`.  Each chart's globally normalised evidence
`g_i = Z_i/(N^{−λ} log^{m−1} N)` has the uniform two-term expansion `log N (g_i − a_i) → d_i`
with `a_i = F_i` on the dominant charts `I₀` (else `0`) and `d_i = B_i` on `I₀`, `F_i` on the
one-log-lower charts `I₁`, `0` otherwise (`tendstoUniformlyOn_chart_global`).  On compact
subsets of `{A > 0}`:

* **chart allocations** `p_{i,N} = Z_i/∑_j Z_j` satisfy
  `log N (p_{i,N} − a_i/A) → h_i = (d_i A − a_i D₁)/A²` uniformly, jointly in `i`
  (`tendstoUniformlyOn_chartAlloc`, `tendstoUniformlyOn_chartAlloc_pi`); `∑ a_i/A = 1`,
  `∑ h_i = 0`; the dominant charts get `B_i/A − F_i D₁/A²`, the one-log-lower charts
  `log N p_{i,N} → F_i/A`, all others `log N p_{i,N} → 0`;
* **assembled quotients** `R_N = ∑ Y_i/∑ Z_i` with coefficient-family numerators satisfy
  `log N (R_N − C/A) → E/A − C D₁/A²` uniformly (`tendstoUniformlyOn_assembledQuotient`), in
  particular finite chart marks `∑ c_i p_{i,N}` (`tendstoUniformlyOn_chartMarks`).

Non-claims: the allocations are probabilities only when the chart contributions are nonnegative
with positive total; with overlapping charts they describe the label of the chosen decomposition,
not intrinsic component probabilities; nothing is claimed when the total leading coefficient
vanishes.
-/

open Set Filter Topology

namespace Grammar

section generic

variable {P : Type*} [TopologicalSpace P] {K : Set P}

/-- The uniform quotient theorem on a compact set from uniform two-term expansions **on `K`**. -/
theorem tendstoUniformlyOn_nextLog_div_compact' {a z : ℝ → P → ℝ} {A F BA BZ : P → ℝ}
    (hA : TendstoUniformlyOn (fun N x => Real.log N * (a N x - A x)) BA atTop K)
    (hZ : TendstoUniformlyOn (fun N x => Real.log N * (z N x - F x)) BZ atTop K)
    (hAc : Continuous A) (hFc : Continuous F) (hBAc : Continuous BA) (hBZc : Continuous BZ)
    (hK : IsCompact K) (hKpos : ∀ x ∈ K, 0 < F x) :
    TendstoUniformlyOn (fun N x => Real.log N * (a N x / z N x - A x / F x))
      (fun x => (BA x * F x - A x * BZ x) / F x ^ 2) atTop K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    simp [TendstoUniformlyOn]
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn hBAc.continuousOn
  obtain ⟨M4, hM4⟩ := hK.exists_bound_of_continuousOn hBZc.continuousOn
  obtain ⟨x₀, hx₀, hmin₀⟩ := hK.exists_isMinOn hKne hFc.continuousOn
  exact tendstoUniformlyOn_nextLog_div (S := K) hA hZ (MA := max M1 M2) (MB := max M3 M4)
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM1 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM2 x hx).trans (le_max_right _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM3 x hx).trans (le_max_left _ _)))
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le ((hM4 x hx).trans (le_max_right _ _)))
    (hKpos x₀ hx₀) fun x hx => hmin₀ hx

/-- Uniform convergence of finite vectors is coordinatewise. -/
theorem tendstoUniformlyOn_pi_of_forall {ι : Type*} [Fintype ι] {F : ℝ → P → ι → ℝ}
    {f : P → ι → ℝ} (h : ∀ i, TendstoUniformlyOn (fun N x => F N x i) (fun x => f x i) atTop K) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have := fun i => Metric.tendstoUniformlyOn_iff.1 (h i) ε hε
  filter_upwards [Filter.eventually_all.2 this] with N hN x hx
  exact (dist_pi_lt_iff hε).2 fun i => hN i x hx

end generic

section allocation

variable {ι : Type*} [Fintype ι] {P : Type*} [TopologicalSpace P] {K : Set P}
  (Z : ι → ℝ → P → ℝ) (lam : ι → ℝ) (mult : ι → ℕ) (F B : ι → P → ℝ) {l : ℝ} {m : ℕ}

/-- The globally normalised chart evidence `g_i = Z_i/(N^{−λ} log^{m−1} N)`. -/
noncomputable def chartScaled (i : ι) (N : ℝ) (x : P) : ℝ :=
  Z i N x / (N ^ (-l) * Real.log N ^ (m - 1))

/-- The chart's leading coefficient at the global scale: `F_i` on the dominant charts, else `0`. -/
noncomputable def chartLead (i : ι) (x : P) : ℝ :=
  if lam i = l ∧ mult i = m then F i x else 0

/-- The chart's next-log coefficient at the global scale: `B_i` on `I₀`, `F_i` on `I₁`, else `0`. -/
noncomputable def chartSecond (i : ι) (x : P) : ℝ :=
  if lam i = l ∧ mult i = m then B i x else if lam i = l ∧ mult i = m - 1 then F i x else 0

theorem sum_chartLead (x : P) :
    ∑ i, chartLead lam mult F (l := l) (m := m) i x = assembledLead lam mult F l m x := rfl

theorem sum_chartSecond (x : P) :
    ∑ i, chartSecond lam mult F B (l := l) (m := m) i x =
      assembledCorrection lam mult F B l m x := rfl

theorem continuous_chartLead {F : ι → P → ℝ} (hF : ∀ i, Continuous (F i)) (i : ι) :
    Continuous (chartLead lam mult F (l := l) (m := m) i) := by
  unfold chartLead
  split_ifs
  · exact hF i
  · exact continuous_const

theorem continuous_chartSecond {F B : ι → P → ℝ} (hF : ∀ i, Continuous (F i))
    (hB : ∀ i, Continuous (B i)) (i : ι) :
    Continuous (chartSecond lam mult F B (l := l) (m := m) i) := by
  unfold chartSecond
  split_ifs
  · exact hB i
  · exact hF i
  · exact continuous_const

variable (hl : ∀ i, l ≤ lam i) (hm : ∀ i, lam i = l → mult i ≤ m) (hm1 : ∀ i, 1 ≤ mult i)
  (hFc : ∀ i, Continuous (F i)) (hK : IsCompact K)
  (hlead : ∀ i, TendstoUniformlyOn (fun N x => Z i N x /
    (N ^ (-lam i) * Real.log N ^ (mult i - 1))) (F i) atTop K)
  (htwo : ∀ i, lam i = l → mult i = m → TendstoUniformlyOn (fun N x => Real.log N *
    (Z i N x / (N ^ (-l) * Real.log N ^ (m - 1)) - F i x)) (B i) atTop K)

include hl hm hm1 hFc hK hlead htwo in
/-- **Per-chart two-term expansion at the global scale**: `log N (g_i − a_i) → d_i` uniformly. -/
theorem tendstoUniformlyOn_chart_global (i : ι) :
    TendstoUniformlyOn (fun N x => Real.log N * (chartScaled Z (l := l) (m := m) i N x -
        chartLead lam mult F (l := l) (m := m) i x))
      (chartSecond lam mult F B (l := l) (m := m) i) atTop K := by
  unfold chartScaled chartLead chartSecond
  by_cases h0 : lam i = l ∧ mult i = m
  · simp only [if_pos h0]
    exact htwo i h0.1 h0.2
  · simp only [if_neg h0]
    by_cases h1 : lam i = l ∧ mult i = m - 1
    · simp only [if_pos h1]
      have hm2 : 2 ≤ m := by have := hm1 i; omega
      obtain ⟨q, hq⟩ : ∃ q, m - 1 = q + 1 := ⟨m - 2, by omega⟩
      have := hlead i
      rw [h1.1, h1.2, hq, Nat.add_sub_cancel] at this
      refine this.congr ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN x _
      have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      simp only
      rw [sub_zero, hq, pow_succ]
      field_simp
    · simp only [if_neg h1]
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hFc i).continuousOn
      have hMabs : ∀ x ∈ K, |F i x| ≤ M := fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM x hx)
      have hrate : Tendsto (fun N : ℝ => Real.log N * (N ^ (-lam i) * Real.log N ^ (mult i - 1)) /
          (N ^ (-l) * Real.log N ^ (m - 1))) atTop (𝓝 0) := by
        by_cases hlam : lam i = l
        · have hmi : mult i + 2 ≤ m := by
            have := hm i hlam
            have h0' : mult i ≠ m := fun h' => h0 ⟨hlam, h'⟩
            have h1' : mult i ≠ m - 1 := fun h' => h1 ⟨hlam, h'⟩
            omega
          obtain ⟨q, hq, hq1⟩ : ∃ q, m - 1 = mult i + q ∧ 1 ≤ q :=
            ⟨m - 1 - mult i, by omega, by omega⟩
          have h2 : Tendsto (fun N : ℝ => (Real.log N)⁻¹ ^ q) atTop (𝓝 0) := by
            have := tendsto_inv_log.pow q
            rwa [zero_pow (by omega)] at this
          refine h2.congr' ?_
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
          have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
          have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
          obtain ⟨r, hr⟩ : ∃ r, mult i = r + 1 := ⟨mult i - 1, by have := hm1 i; omega⟩
          rw [hlam, hq, hr, Nat.add_sub_cancel, pow_add, pow_succ]
          field_simp
          rw [div_pow, one_pow, div_mul_cancel₀ _ (pow_ne_zero q hL)]
        · have hlt : l < lam i := lt_of_le_of_ne (hl i) (Ne.symm hlam)
          have := tendsto_shift_ratio hlt (hm1 i) m
          refine this.congr fun N => ?_
          ring
      have hcomp := tendstoUniformlyOn_scalar_mul_zero_of_bounded hrate (hlead i) hMabs
      refine hcomp.congr ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN x _
      have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
      have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      have hpow' : N ^ (-lam i) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
      have hLm : Real.log N ^ (mult i - 1) ≠ 0 := pow_ne_zero _ hL
      simp only
      rw [sub_zero]
      field_simp

/-! ### Chart allocations -/

/-- The chart allocation `p_{i,N} = Z_i/∑_j Z_j`. -/
noncomputable def chartAlloc (i : ι) (N : ℝ) (x : P) : ℝ := Z i N x / ∑ j, Z j N x

/-- The limiting allocation `a_i/A`. -/
noncomputable def chartAllocLead (i : ι) (x : P) : ℝ :=
  chartLead lam mult F (l := l) (m := m) i x / assembledLead lam mult F l m x

/-- The first allocation correction `h_i = (d_i A − a_i D₁)/A²`. -/
noncomputable def chartAllocCorrection (i : ι) (x : P) : ℝ :=
  (chartSecond lam mult F B (l := l) (m := m) i x * assembledLead lam mult F l m x -
    chartLead lam mult F (l := l) (m := m) i x * assembledCorrection lam mult F B l m x) /
      assembledLead lam mult F l m x ^ 2

theorem chartAlloc_eq {N : ℝ} (hN : 1 < N) (i : ι) (x : P) :
    chartAlloc Z i N x = chartScaled Z (l := l) (m := m) i N x / assembledScaled Z l m N x := by
  unfold chartAlloc chartScaled assembledScaled
  have hden : N ^ (-l) * Real.log N ^ (m - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  rw [div_div_div_cancel_right₀ hden]

/-- The limiting allocations sum to `1` on `{A > 0}`. -/
theorem sum_chartAllocLead {x : P} (hx : assembledLead lam mult F l m x ≠ 0) :
    ∑ i, chartAllocLead lam mult F (l := l) (m := m) i x = 1 := by
  unfold chartAllocLead
  rw [← Finset.sum_div, sum_chartLead, div_self hx]

/-- The allocation corrections sum to `0`. -/
theorem sum_chartAllocCorrection (x : P) :
    ∑ i, chartAllocCorrection lam mult F B (l := l) (m := m) i x = 0 := by
  unfold chartAllocCorrection
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_chartLead, sum_chartSecond, mul_comm, sub_self, zero_div]

variable (hBc : ∀ i, Continuous (B i)) (hKpos : ∀ x ∈ K, 0 < assembledLead lam mult F l m x)

include hl hm hm1 hFc hK hlead htwo hBc hKpos in
/-- **First correction to chart allocations**, uniformly on compact subsets of `{A > 0}`:
`log N (p_{i,N} − a_i/A) → (d_i A − a_i D₁)/A²`. -/
theorem tendstoUniformlyOn_chartAlloc (i : ι) :
    TendstoUniformlyOn (fun N x => Real.log N * (chartAlloc Z i N x -
        chartAllocLead lam mult F (l := l) (m := m) i x))
      (chartAllocCorrection lam mult F B (l := l) (m := m) i) atTop K := by
  have h := tendstoUniformlyOn_nextLog_div_compact'
    (tendstoUniformlyOn_chart_global Z lam mult F B hl hm hm1 hFc hK hlead htwo i)
    (tendstoUniformlyOn_assembled Z lam mult F B hl hm hm1 hFc hK hlead htwo)
    (continuous_chartLead lam mult hFc i) (continuous_assembledLead lam mult hFc l m)
    (continuous_chartSecond lam mult hFc hBc i)
    (continuous_assembledCorrection lam mult hFc hBc l m) hK hKpos
  refine h.congr ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN x _
  simp only
  rw [chartAlloc_eq Z hN]
  rfl

include hl hm hm1 hFc hK hlead htwo hBc hKpos in
/-- The allocation corrections, jointly in the chart index. -/
theorem tendstoUniformlyOn_chartAlloc_pi :
    TendstoUniformlyOn (fun N x i => Real.log N * (chartAlloc Z i N x -
        chartAllocLead lam mult F (l := l) (m := m) i x))
      (fun x i => chartAllocCorrection lam mult F B (l := l) (m := m) i x) atTop K :=
  tendstoUniformlyOn_pi_of_forall fun i =>
    tendstoUniformlyOn_chartAlloc Z lam mult F B hl hm hm1 hFc hK hlead htwo hBc hKpos i

/-! ### Assembled quotients and chart marks -/

variable (Y : ι → ℝ → P → ℝ) (U V : ι → P → ℝ) (hUc : ∀ i, Continuous (U i))
  (hVc : ∀ i, Continuous (V i))
  (hleadY : ∀ i, TendstoUniformlyOn (fun N x => Y i N x /
    (N ^ (-lam i) * Real.log N ^ (mult i - 1))) (U i) atTop K)
  (htwoY : ∀ i, lam i = l → mult i = m → TendstoUniformlyOn (fun N x => Real.log N *
    (Y i N x / (N ^ (-l) * Real.log N ^ (m - 1)) - U i x)) (V i) atTop K)

/-- The assembled ratio `∑ Y_i/∑ Z_i`. -/
noncomputable def assembledRatio (N : ℝ) (x : P) : ℝ := (∑ i, Y i N x) / ∑ i, Z i N x

theorem assembledRatio_eq {N : ℝ} (hN : 1 < N) (x : P) :
    assembledRatio Z Y N x = assembledScaled Y l m N x / assembledScaled Z l m N x := by
  unfold assembledRatio assembledScaled
  have hden : N ^ (-l) * Real.log N ^ (m - 1) ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by linarith) _).ne' (pow_ne_zero _ (Real.log_pos hN).ne')
  rw [div_div_div_cancel_right₀ hden]

include hl hm hm1 hFc hK hlead htwo hBc hKpos hUc hVc hleadY htwoY in
/-- **Assembled quotients at the next logarithmic order**: with `C = ∑_{I₀} U_i`,
`E = ∑_{I₀} V_i + ∑_{I₁} U_i`, `log N (∑Y_i/∑Z_i − C/A) → (E A − C D₁)/A²` uniformly on compact
subsets of `{A > 0}`. -/
theorem tendstoUniformlyOn_assembledQuotient :
    TendstoUniformlyOn (fun N x => Real.log N * (assembledRatio Z Y N x -
        assembledLead lam mult U l m x / assembledLead lam mult F l m x))
      (fun x => (assembledCorrection lam mult U V l m x * assembledLead lam mult F l m x -
        assembledLead lam mult U l m x * assembledCorrection lam mult F B l m x) /
          assembledLead lam mult F l m x ^ 2) atTop K := by
  have h := tendstoUniformlyOn_nextLog_div_compact'
    (tendstoUniformlyOn_assembled Y lam mult U V hl hm hm1 hUc hK hleadY htwoY)
    (tendstoUniformlyOn_assembled Z lam mult F B hl hm hm1 hFc hK hlead htwo)
    (continuous_assembledLead lam mult hUc l m) (continuous_assembledLead lam mult hFc l m)
    (continuous_assembledCorrection lam mult hUc hVc l m)
    (continuous_assembledCorrection lam mult hFc hBc l m) hK hKpos
  refine h.congr ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN x _
  simp only
  rw [assembledRatio_eq Z Y hN]

include hl hm hm1 hFc hK hlead htwo hBc hKpos in
/-- **Chart marks**: for continuous marks `c_i`, `∑ c_i p_{i,N}` is the assembled ratio with
numerators `c_i Z_i`, hence `log N (∑ c_i p_{i,N} − ∑ c_i a_i/A) → ∑ c_i h_i`. -/
theorem tendstoUniformlyOn_chartMarks (c : ι → P → ℝ) (hc : ∀ i, Continuous (c i)) :
    TendstoUniformlyOn (fun N x => Real.log N * (∑ i, c i x * chartAlloc Z i N x -
        ∑ i, c i x * chartAllocLead lam mult F (l := l) (m := m) i x))
      (fun x => ∑ i, c i x * chartAllocCorrection lam mult F B (l := l) (m := m) i x) atTop K := by
  have h := tendstoUniformlyOn_finset_sum (K := K) Finset.univ (F := fun i N x =>
      c i x * (Real.log N * (chartAlloc Z i N x - chartAllocLead lam mult F (l := l) (m := m) i x)))
    (f := fun i x => c i x * chartAllocCorrection lam mult F B (l := l) (m := m) i x)
    fun i _ => by
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc i).continuousOn
      obtain ⟨M', hM'⟩ := hK.exists_bound_of_continuousOn
        (f := chartAllocCorrection lam mult F B (l := l) (m := m) i) (by
          unfold chartAllocCorrection
          exact ContinuousOn.div (((continuous_chartSecond lam mult hFc hBc i).mul
            (continuous_assembledLead lam mult hFc l m)).sub
            ((continuous_chartLead lam mult hFc i).mul
              (continuous_assembledCorrection lam mult hFc hBc l m))).continuousOn
            ((continuous_assembledLead lam mult hFc l m).pow 2).continuousOn
            fun x hx => pow_ne_zero _ (hKpos x hx).ne')
      exact tendstoUniformlyOn_mul_of_bounded (tendstoUniformlyOn_const' (c i))
        (tendstoUniformlyOn_chartAlloc Z lam mult F B hl hm hm1 hFc hK hlead htwo hBc hKpos i)
        (fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM x hx))
        (fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM' x hx))
  refine h.congr (Eventually.of_forall fun N x _ => ?_)
  simp only
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end allocation

end Grammar
