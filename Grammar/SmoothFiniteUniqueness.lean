/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FirstNonzero
import Grammar.SmoothFaceTheorem

/-!
# Finite-cutoff uniqueness of power–log coefficients (smooth engine, unit 3c)

A single cutoff bound `|Z N − ∑_{μ∈Λ^Q_L} N^{-μ} ∑_{j≤D} c_{μ,j} (log N)^j| ≤ K N^{-L}(1+log N)^D`
(eventually in `N`) already determines the coefficients `c_{μ,j}` for `μ ∈ Λ^Q_L`, `j ≤ D` — no
family of cutoffs (`CutoffExpansion`) is needed. The route is the abstract ordered remainder of
`AbstractExpansion` with the cutoff `μ + 1` replaced by an arbitrary cutoff `L' > μ`
(`abs_abstractRemainder_sub_le'`, `tendsto_abstractRemainder_of_bound`): at the first nonzero
pair the predecessor sum vanishes, so the remainder is identically `0` and its limit `c_{μ,j}`
must be `0` (★ `finite_coeff_eq_zero`); two coefficient systems with the same cutoff bound agree
(★ `finite_coeff_unique`). The smooth engine's `powLog` on the lattice below `L` is
`absSpectralSum` (`powLog_eq_absSpectralSum`), which is how the face-monomial two-regime estimate
feeds this uniqueness. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-! ### The ordered remainder at an arbitrary cutoff -/

/-- The retained terms below the cutoff `L'` other than the predecessors and the target. -/
noncomputable def restSetAt (D Q : ℕ) (L' μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) :=
  indexSet D Q L' \ (predSet D Q μ j ∪ {(μ, j)})

open scoped Classical in
theorem mem_restSetAt {D Q : ℕ} (hQ : 0 < Q) {L' μ : ℝ} (hμL : μ < L') {j : ℕ} {p : ℝ × ℕ}
    (hp : p ∈ restSetAt D Q L' μ j) :
    p ∈ indexSet D Q L' ∧ μ ≤ p.1 ∧ (p.1 = μ → p.2 < j) := by
  unfold restSetAt at hp
  rw [predSet_eq_filter hQ hμL j, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
    Finset.mem_singleton] at hp
  obtain ⟨hi, hnot⟩ := hp
  refine ⟨hi, ?_, ?_⟩
  · by_contra hlt
    exact hnot (Or.inl ⟨hi, Or.inl (lt_of_not_ge hlt)⟩)
  · intro heq
    by_contra hge
    rcases lt_or_eq_of_le (le_of_not_gt hge) with hlt | heq2
    · exact hnot (Or.inl ⟨hi, Or.inr ⟨heq, hlt⟩⟩)
    · exact hnot (Or.inr (Prod.ext heq heq2.symm))

open scoped Classical in
/-- **The abstract quantitative ordered-remainder estimate at an arbitrary cutoff `L' > μ`.** -/
theorem abs_abstractRemainder_sub_le' {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) {L' K C : ℝ} (hμL : μ < L') {N : ℝ}
    (hNe : Real.exp 1 ≤ N)
    (hcut : |Z N - absSpectralSum Q D c L' N| ≤ K * (N ^ (-L') * (1 + Real.log N) ^ D))
    (hC : ∀ p ∈ indexSet D Q L', |c p.1 p.2| ≤ C) :
    |abstractRemainder Q D Z c μ j N - c μ j| ≤
      K * (N ^ (-L') * (1 + Real.log N) ^ D / N ^ (-μ)) +
        C * ∑ p ∈ restSetAt D Q L' μ j, termMajorant D μ p N := by
  obtain ⟨m, hm⟩ := hμ
  have htarget : (μ, j) ∈ indexSet D Q L' := by
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.lt_succ_of_le hj)⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; exact hμL)
  have hpred_sub : predSet D Q μ j ⊆ indexSet D Q L' := by
    rw [predSet_eq_filter hQ hμL j]; exact Finset.filter_subset _ _
  have htarget_notin : (μ, j) ∉ predSet D Q μ j := by
    unfold predSet
    rw [Finset.mem_filter]
    exact fun hcontra => precedes_irrefl _ hcontra.2
  have hsub : predSet D Q μ j ∪ {(μ, j)} ⊆ indexSet D Q L' :=
    Finset.union_subset hpred_sub (Finset.singleton_subset_iff.2 htarget)
  have hdecomp : Z N - absPredSum Q D c μ j N - c μ j * (N ^ (-μ) * Real.log N ^ j) =
      (Z N - absSpectralSum Q D c L' N) + ∑ p ∈ restSetAt D Q L' μ j, absTerm c N p := by
    unfold restSetAt absPredSum
    rw [absSpectralSum_eq_sum_indexSet, ← Finset.sum_sdiff hsub,
      Finset.sum_union (Finset.disjoint_singleton_right.2 htarget_notin), Finset.sum_singleton]
    unfold absTerm
    ring
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hRN : abstractRemainder Q D Z c μ j N - c μ j =
      (Z N - absPredSum Q D c μ j N - c μ j * (N ^ (-μ) * Real.log N ^ j)) /
        (N ^ (-μ) * Real.log N ^ j) := by
    unfold abstractRemainder
    have hD' := hD.ne'
    field_simp
  rw [hRN, hdecomp, add_div, Finset.sum_div]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    refine hcut.trans ?_
    have h3 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hK0 : 0 ≤ K * (N ^ (-L') * (1 + Real.log N) ^ D) := (abs_nonneg _).trans hcut
    have hr : 0 < N ^ (-μ) := Real.rpow_pos_of_pos hN0 _
    calc K * (N ^ (-L') * (1 + Real.log N) ^ D)
        = K * (N ^ (-L') * (1 + Real.log N) ^ D / N ^ (-μ)) * (N ^ (-μ) * 1) := by
          field_simp
      _ ≤ K * (N ^ (-L') * (1 + Real.log N) ^ D / N ^ (-μ)) *
          (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hr.le) ?_
          have : K * (N ^ (-L') * (1 + Real.log N) ^ D / N ^ (-μ)) =
              K * (N ^ (-L') * (1 + Real.log N) ^ D) / N ^ (-μ) := by ring
          rw [this]; exact div_nonneg hK0 hr.le
  · rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨hpi, hpμ, hpq⟩ := mem_restSetAt hQ hμL hp
    exact abs_absTerm_div_le (hC p hpi) hpμ hpq (mem_indexSet_snd_le hpi) hNe

/-- The abstract majorant at cutoff `L' > μ` tends to zero. -/
theorem tendsto_abstract_majorant' {Q : ℕ} (hQ : 0 < Q) (D : ℕ) {L' μ : ℝ} (hμL : μ < L') (j : ℕ)
    (K C : ℝ) :
    Tendsto (fun N : ℝ => K * (N ^ (-L') * (1 + Real.log N) ^ D / N ^ (-μ)) +
      C * ∑ p ∈ restSetAt D Q L' μ j, termMajorant D μ p N) atTop (𝓝 0) := by
  have h1 := (tendsto_cutoff_ratio D hμL).const_mul K
  have h2 := (tendsto_finsetSum (restSetAt D Q L' μ j) fun p hp =>
    tendsto_termMajorant D (mem_restSetAt hQ hμL hp).2.1).const_mul C
  simpa using h1.add h2

/-- **A single eventual cutoff bound at `L'` gives convergent ordered normalised remainders** at
every `μ ∈ Λ^Q_{L'}`, `j ≤ D`. -/
theorem tendsto_abstractRemainder_of_bound {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    {L' K : ℝ}
    (h : ∀ᶠ N in atTop,
      |Z N - absSpectralSum Q D c L' N| ≤ K * (N ^ (-L') * (1 + Real.log N) ^ D))
    {μ : ℝ} (hμ : μ ∈ latticeBelow Q L') {j : ℕ} (hj : j ≤ D) :
    Tendsto (fun N => abstractRemainder Q D Z c μ j N) atTop (𝓝 (c μ j)) := by
  obtain ⟨hμm, hμL⟩ := (mem_latticeBelow_iff hQ).1 hμ
  set C : ℝ := ∑ p ∈ indexSet D Q L', |c p.1 p.2| with hCdef
  have hC : ∀ p ∈ indexSet D Q L', |c p.1 p.2| ≤ C := fun p hp =>
    Finset.single_le_sum (fun q _ => abs_nonneg (c q.1 q.2)) hp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_abstract_majorant' hQ D hμL j K C)
  filter_upwards [h, eventually_ge_atTop (Real.exp 1)] with N hN hNe
  simp only [Real.norm_eq_abs, abs_abs]
  exact abs_abstractRemainder_sub_le' hQ hμm hj hμL hNe hN hC

/-! ### Uniqueness from a single cutoff bound -/

/-- ★ **A power–log sum bounded by its own cutoff error vanishes identically**: if
`|∑_{μ∈Λ^Q_L} N^{-μ} ∑_{j≤D} c_{μ,j} (log N)^j| ≤ K N^{-L}(1+log N)^D` eventually, then
`c_{μ,j} = 0` for every `μ ∈ Λ^Q_L`, `j ≤ D`. -/
theorem finite_coeff_eq_zero {Q D : ℕ} (hQ : 0 < Q) {c : ℝ → ℕ → ℝ} {L K : ℝ}
    (h : ∀ᶠ N in atTop, |absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)) :
    ∀ μ ∈ latticeBelow Q L, ∀ j ≤ D, c μ j = 0 := by
  intro μ hμ j hj
  by_contra hcμ
  have hmem : (μ, j) ∈ indexSet D Q L := mem_indexSet_iff.2 ⟨hμ, Nat.lt_succ_of_le hj⟩
  obtain ⟨p, hp, hcp, hfirst⟩ :=
    exists_first_nonzero_finset (indexSet D Q L) c ⟨(μ, j), hmem, hcμ⟩
  obtain ⟨hp1, hp2⟩ := mem_indexSet_iff.1 hp
  have h0 : ∀ᶠ N in atTop, |(fun _ : ℝ => (0 : ℝ)) N - absSpectralSum Q D c L N| ≤
      K * (N ^ (-L) * (1 + Real.log N) ^ D) := by
    filter_upwards [h] with N hN
    rw [zero_sub, abs_neg]; exact hN
  have hlim := tendsto_abstractRemainder_of_bound hQ h0 hp1 (Nat.lt_succ_iff.1 hp2)
  have hfirst' : ∀ q ∈ admissible D Q, precedes q p → c q.1 q.2 = 0 := fun q hq hqp =>
    hfirst q (indexSet_pred_closed hQ hp hq hqp) hqp
  have hzero : (fun N => abstractRemainder Q D (fun _ => 0) c p.1 p.2 N) = fun _ => 0 := by
    funext N
    unfold abstractRemainder
    rw [absPredSum_eq_zero_of_first hQ c hfirst' N]
    simp
  rw [hzero] at hlim
  exact hcp (tendsto_nhds_unique hlim tendsto_const_nhds)

theorem absSpectralSum_sub (Q D : ℕ) (c₁ c₂ : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => c₁ μ j - c₂ μ j) L N =
      absSpectralSum Q D c₁ L N - absSpectralSum Q D c₂ L N := by
  unfold absSpectralSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- ★ **Finite-cutoff uniqueness**: two coefficient systems with the same eventual cutoff bound
at `L` for the same function agree at every `μ ∈ Λ^Q_L`, `j ≤ D`. -/
theorem finite_coeff_unique {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
    {L K₁ K₂ : ℝ}
    (h₁ : ∀ᶠ N in atTop,
      |Z N - absSpectralSum Q D c₁ L N| ≤ K₁ * (N ^ (-L) * (1 + Real.log N) ^ D))
    (h₂ : ∀ᶠ N in atTop,
      |Z N - absSpectralSum Q D c₂ L N| ≤ K₂ * (N ^ (-L) * (1 + Real.log N) ^ D)) :
    ∀ μ ∈ latticeBelow Q L, ∀ j ≤ D, c₁ μ j = c₂ μ j := by
  have h : ∀ᶠ N in atTop, |absSpectralSum Q D (fun μ j => c₁ μ j - c₂ μ j) L N| ≤
      (K₁ + K₂) * (N ^ (-L) * (1 + Real.log N) ^ D) := by
    filter_upwards [h₁, h₂] with N h1 h2
    rw [absSpectralSum_sub]
    calc |absSpectralSum Q D c₁ L N - absSpectralSum Q D c₂ L N|
        ≤ |absSpectralSum Q D c₁ L N - Z N| + |Z N - absSpectralSum Q D c₂ L N| :=
          abs_sub_le _ _ _
      _ = |Z N - absSpectralSum Q D c₁ L N| + |Z N - absSpectralSum Q D c₂ L N| := by
          rw [abs_sub_comm (absSpectralSum Q D c₁ L N)]
      _ ≤ K₁ * (N ^ (-L) * (1 + Real.log N) ^ D) + K₂ * (N ^ (-L) * (1 + Real.log N) ^ D) :=
          add_le_add h1 h2
      _ = (K₁ + K₂) * (N ^ (-L) * (1 + Real.log N) ^ D) := by ring
  intro μ hμ j hj
  exact sub_eq_zero.1 (finite_coeff_eq_zero hQ h μ hμ j hj)

/-! ### The smooth engine's power–log sum is the abstract spectral sum -/

/-- `powLog` on the lattice below `L` is `absSpectralSum`. -/
theorem powLog_eq_absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) :
    SmoothEngine.powLog (latticeBelow Q L) D c N = absSpectralSum Q D c L N := by
  unfold SmoothEngine.powLog absSpectralSum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Grammar
