/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.UniformNextLogQuotient
import Grammar.SpatialAssembly

/-!
# Uniform finite-chart assembly at the next logarithmic order

Generic over a finite chart index `ι` and a common data space `P`.  Each chart `i` has an
unnormalised evidence family `Z i N x`, exponent `lam i`, multiplicity `mult i`, and coefficients
`F i`, `B i` with the compact-uniform two-term expansion
`log N (Z i N x/(N^{−lam i} log^{mult i − 1} N) − F i x) → B i x` on `K`.  With the global dominant
pair `λ = min lam`, `m = max multiplicity at λ`:

* **uniform scale separation** (`tendstoUniformlyOn_scalar_mul_zero_of_bounded`): charts with a
  larger exponent, or the same exponent and multiplicity `≤ m−2`, are uniformly `o(1/log N)` after
  the global rescaling;
* the **compact-uniform assembled two-term theorem** (`tendstoUniformlyOn_assembled`):
  `log N ((∑ Z_i)/(N^{−λ} log^{m−1} N) − A) → D₁` uniformly on `K`, with
  `A = ∑_{I₀} F_i`, `D₁ = ∑_{I₀} B_i + ∑_{I₁} F_i` (`assembledLead`, `assembledCorrection`), both
  continuous; the multiplicity-`(m−1)` charts feed the global `1/log N` term.

No positivity of individual leading coefficients is needed; on compact subsets of `{A > 0}` the
assembled normalised evidence is eventually uniformly positive (`eventually_assembled_pos`).
-/

open Set Filter Topology

namespace Grammar

section generic

variable {P : Type*} [TopologicalSpace P] {K : Set P}

/-- Finite sums of uniformly convergent real families converge uniformly. -/
theorem tendstoUniformlyOn_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → P → ℝ}
    {f : ι → P → ℝ} (h : ∀ i ∈ s, TendstoUniformlyOn (F i) (f i) atTop K) :
    TendstoUniformlyOn (fun N x => ∑ i ∈ s, F i N x) (fun x => ∑ i ∈ s, f i x) atTop K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendstoUniformlyOn_const' (fun _ : P => (0 : ℝ))
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Uniform scale separation**: a scalar sequence tending to `0` times a uniformly convergent
family with bounded limit tends to `0` uniformly. -/
theorem tendstoUniformlyOn_scalar_mul_zero_of_bounded {a : ℝ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {E : ℝ → P → ℝ} {f : P → ℝ} (hE : TendstoUniformlyOn E f atTop K) {M : ℝ}
    (hf : ∀ x ∈ K, |f x| ≤ M) :
    TendstoUniformlyOn (fun N x => a N * E N x) (fun _ => (0 : ℝ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hE ⊢
  intro ε hε
  have hM : 0 ≤ M ∨ K = ∅ := by
    by_cases hK : K = ∅
    · exact Or.inr hK
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hK
      exact Or.inl ((abs_nonneg _).trans (hf x hx))
  rcases hM with hM | hK
  · filter_upwards [hE 1 one_pos, (Metric.tendsto_nhds.1 ha) (ε / (M + 2)) (by positivity)]
      with N h1 h2 x hx
    have hEb : |E N x| ≤ M + 1 := by
      have hd := h1 x hx
      rw [Real.dist_eq, abs_sub_comm] at hd
      have hab := abs_sub_abs_le_abs_sub (E N x) (f x)
      linarith [hf x hx]
    rw [dist_zero_right] at h2
    rw [Real.dist_eq, zero_sub, abs_neg, abs_mul, Real.norm_eq_abs] at *
    calc |a N| * |E N x| ≤ |a N| * (M + 1) := mul_le_mul_of_nonneg_left hEb (abs_nonneg _)
      _ < ε / (M + 2) * (M + 1) := by gcongr
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  · subst hK
    simp

end generic

/-! ### The assembled coefficients -/

section assembly

variable {ι : Type*} [Fintype ι] {P : Type*} [TopologicalSpace P]

/-- The assembled leading coefficient `A = ∑_{λ_i = λ, m_i = m} F_i`. -/
noncomputable def assembledLead (lam : ι → ℝ) (mult : ι → ℕ) (F : ι → P → ℝ) (l : ℝ) (m : ℕ)
    (x : P) : ℝ :=
  ∑ i, if lam i = l ∧ mult i = m then F i x else 0

/-- The assembled next-log coefficient `D₁ = ∑_{I₀} B_i + ∑_{I₁} F_i`. -/
noncomputable def assembledCorrection (lam : ι → ℝ) (mult : ι → ℕ) (F B : ι → P → ℝ) (l : ℝ)
    (m : ℕ) (x : P) : ℝ :=
  ∑ i, if lam i = l ∧ mult i = m then B i x else if lam i = l ∧ mult i = m - 1 then F i x else 0

theorem continuous_assembledLead (lam : ι → ℝ) (mult : ι → ℕ) {F : ι → P → ℝ}
    (hF : ∀ i, Continuous (F i)) (l : ℝ) (m : ℕ) : Continuous (assembledLead lam mult F l m) := by
  unfold assembledLead
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact hF i
  · exact continuous_const

theorem continuous_assembledCorrection (lam : ι → ℝ) (mult : ι → ℕ) {F B : ι → P → ℝ}
    (hF : ∀ i, Continuous (F i)) (hB : ∀ i, Continuous (B i)) (l : ℝ) (m : ℕ) :
    Continuous (assembledCorrection lam mult F B l m) := by
  unfold assembledCorrection
  refine continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact hB i
  · exact hF i
  · exact continuous_const

/-- The globally normalised assembled evidence `(∑ Z_i)/(N^{−λ} log^{m−1} N)`. -/
noncomputable def assembledScaled (Z : ι → ℝ → P → ℝ) (l : ℝ) (m : ℕ) (N : ℝ) (x : P) : ℝ :=
  (∑ i, Z i N x) / (N ^ (-l) * Real.log N ^ (m - 1))

variable {K : Set P} (Z : ι → ℝ → P → ℝ) (lam : ι → ℝ) (mult : ι → ℕ) (F B : ι → P → ℝ)
  {l : ℝ} {m : ℕ} (hl : ∀ i, l ≤ lam i) (hm : ∀ i, lam i = l → mult i ≤ m) (hm1 : ∀ i, 1 ≤ mult i)
  (hFc : ∀ i, Continuous (F i)) (hK : IsCompact K)
  (hlead : ∀ i, TendstoUniformlyOn (fun N x => Z i N x /
    (N ^ (-lam i) * Real.log N ^ (mult i - 1))) (F i) atTop K)
  (htwo : ∀ i, lam i = l → mult i = m → TendstoUniformlyOn (fun N x => Real.log N *
    (Z i N x / (N ^ (-l) * Real.log N ^ (m - 1)) - F i x)) (B i) atTop K)

include hl hm hm1 hFc hK hlead htwo in
/-- **The compact-uniform assembled two-term theorem**:
`log N ((∑ Z_i)/(N^{−λ} log^{m−1} N) − A) → D₁` uniformly on `K`. -/
theorem tendstoUniformlyOn_assembled :
    TendstoUniformlyOn (fun N x => Real.log N * (assembledScaled Z l m N x -
        assembledLead lam mult F l m x)) (assembledCorrection lam mult F B l m) atTop K := by
  classical
  have hsum : ∀ N x, Real.log N * (assembledScaled Z l m N x - assembledLead lam mult F l m x) =
      ∑ i, Real.log N * (Z i N x / (N ^ (-l) * Real.log N ^ (m - 1)) -
        if lam i = l ∧ mult i = m then F i x else 0) := by
    intro N x
    unfold assembledScaled assembledLead
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [hsum]
  unfold assembledCorrection
  refine tendstoUniformlyOn_finset_sum _ fun i _ => ?_
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
      -- negligible chart: scalar rate times the normalised chart evidence
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

include hl hm hm1 hFc hK hlead htwo in
/-- The assembled normalised evidence converges uniformly to `A` on `K`. -/
theorem tendstoUniformlyOn_assembledScaled (hBc : ∀ i, Continuous (B i)) :
    TendstoUniformlyOn (assembledScaled Z l m) (assembledLead lam mult F l m) atTop K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_assembledCorrection lam mult hFc hBc l m).continuousOn
  exact tendstoUniformlyOn_of_nextLog
    (tendstoUniformlyOn_assembled Z lam mult F B hl hm hm1 hFc hK hlead htwo)
    fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM x hx)

include hl hm hm1 hFc hK hlead htwo in
/-- On compact subsets of `{A > 0}` the assembled normalised evidence is eventually uniformly
positive. -/
theorem eventually_assembled_pos (hBc : ∀ i, Continuous (B i)) (hKne : K.Nonempty)
    (hKpos : ∀ x ∈ K, 0 < assembledLead lam mult F l m x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, ∀ x ∈ K, δ / 2 ≤ assembledScaled Z l m N x := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_assembledCorrection lam mult hFc hBc l m).continuousOn
  obtain ⟨x₀, hx₀, hmin₀⟩ :=
    hK.exists_isMinOn hKne (continuous_assembledLead lam mult hFc l m).continuousOn
  exact ⟨_, hKpos x₀ hx₀, eventually_floor_of_nextLog
    (tendstoUniformlyOn_assembled Z lam mult F B hl hm hm1 hFc hK hlead htwo)
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM x hx)) (hKpos x₀ hx₀) fun x hx => hmin₀ hx⟩

end assembly

end Grammar
