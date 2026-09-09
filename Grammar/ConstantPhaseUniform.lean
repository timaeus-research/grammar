/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseCorrection
import Grammar.DataCutoff

/-!
# Constant-phase two-term data, uniformly on compact phase sets (unit 340; Astra #40 unit 5a)

The quantitative Taylor-tree remainder of the constant-phase family has a cutoff constant
`cutoffBound n k β L a (mass cη) |a|`, monotone in `|a|` (`cutoffBound_mono`), hence uniform on
`|a| ≤ R` (`constPhase_remainder_uniform`); the constant-phase coefficients are continuous in the
phase, hence bounded on compacts (`constPhase_coeff_bounded`); and a quantitative two-term split of
the log polynomial (`twoTerm_split_bound`) controls the lower log degrees by `1/log N`. Together:
```
sup_{|a| ≤ R} | log N (𝒵_N[η;a]/(N^{-λ}L^{m−1}) − A(a)) − B(a) | → 0
```
(`constPhase_twoTerm_uniform`), the compact-uniform two-term remainder needed for a phase moving
with `N`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

theorem CoeffFamily.mass_constFamily {d : ℕ} (a : ℝ) :
    mass (constFamily a : CoeffFamily d) = |a| := by
  unfold mass constFamily
  rw [tsum_eq_single 0]
  · simp
  · intro γ hγ
    simp [hγ]

/-- **Quantitative two-term split**: with `c q = 0` above `r + 1` and `L ≥ 1`,
`|(∑_{q≤n} c q L^q)/L^r − c(r+1) L − c r| ≤ (∑_{q<r} |c q|)/L`. -/
theorem twoTerm_split_bound (c : ℕ → ℝ) (n r : ℕ) (hr : r + 1 ≤ n) (hz : ∀ q, r + 1 < q → c q = 0)
    {L : ℝ} (hL : 1 ≤ L) :
    |(∑ q ∈ Finset.range (n + 1), c q * L ^ q) / L ^ r - c (r + 1) * L - c r| ≤
      (∑ q ∈ Finset.range r, |c q|) / L := by
  have hL0 : 0 < L := by linarith
  have hsum : ∑ q ∈ Finset.range (n + 1), c q * L ^ q =
      ∑ q ∈ Finset.range (r + 2), c q * L ^ q := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega : r + 2 ≤ n + 1)) fun q hq hq' => ?_
    rw [Finset.mem_range] at hq hq'
    rw [hz q (by omega), zero_mul]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ]
  have hLr : L ^ r ≠ 0 := pow_ne_zero _ hL0.ne'
  have e : (∑ q ∈ Finset.range r, c q * L ^ q + c r * L ^ r + c (r + 1) * L ^ (r + 1)) / L ^ r -
      c (r + 1) * L - c r = (∑ q ∈ Finset.range r, c q * L ^ q) / L ^ r := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (pow_pos hL0 r), div_le_div_iff₀ (pow_pos hL0 r) hL0]
  calc |∑ q ∈ Finset.range r, c q * L ^ q| * L
      ≤ (∑ q ∈ Finset.range r, |c q| * L ^ q) * L := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [abs_mul, abs_of_pos (pow_pos hL0 q)]
    _ ≤ (∑ q ∈ Finset.range r, |c q| * L ^ (r - 1)) * L := by
        gcongr with q hq
        rw [Finset.mem_range] at hq
        omega
    _ = (∑ q ∈ Finset.range r, |c q|) * L ^ r := by
        rw [← Finset.sum_mul]
        rcases Nat.eq_zero_or_pos r with hr0 | hr0
        · subst hr0
          simp
        · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr0]

/-- **Uniform cutoff remainder on compact phase sets**: for `|a| ≤ R` and `N ≥ 1`,
`|𝒵_N[η;a] − N^{-λ} ∑_{q≤n} C(λ,q;a) L^q| ≤ K_R N^{-(λ+1/Q)}(1 + L)^n`. -/
theorem constPhase_remainder_uniform (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, ∀ a : ℝ, |a| ≤ R → ∀ N : ℝ, 1 ≤ N →
      |origPhaseIntegral n h k β N 1 (fun _ => a) η - N ^ (-l) * ∑ q ∈ Finset.range (n + 1),
          familySpectralCoeff n h k β (constFamily a) cη l q * Real.log N ^ q| ≤
        K * (N ^ (-(l + 1 / latticeQ k)) * (1 + Real.log N) ^ n) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hL0 : 0 < l + 1 / latticeQ k := by positivity
  refine ⟨cutoffBound n k β (l + 1 / latticeQ k) R (mass cη) R, fun a ha N hN => ?_⟩
  have hN0 : 0 ≤ N := by linarith
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    ((absSummableAt_one_iff _).2 (absSummable_constFamily a)) ((absSummableAt_one_iff _).2 hη)
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β (constFamily a) cη μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  have hI : familyPhaseIntegralBox n h k β N 1 (constFamily a) cη =
      origPhaseIntegral n h k β N 1 (fun _ => a) η :=
    familyPhaseIntegralBox_eq_orig n h k β N 1 (fun u _ => evalF_constFamily a u) hev
  have hrem := hC.remainder (l + 1 / latticeQ k) hL0 N hN0 (by rw [boxScale_one]; exact hN)
  rw [boxScale_one, one_pow, one_mul, one_mul, scale_one, scale_one, constFamily_zero_apply,
    mass_constFamily] at hrem
  -- the isolated spectral sum
  obtain ⟨i₀, hi₀⟩ := hatt
  obtain ⟨a₀, -, ha₀⟩ := ratio_mem_lattice k hk i₀ (h i₀)
  have hla : l = (a₀ : ℝ) / latticeQ k := by rw [← hi₀]; exact ha₀
  have hpred : ∀ m' : ℕ, m' < a₀ → ∀ j, C ((m' : ℝ) / latticeQ k) j = 0 := by
    intro m' hm' j
    apply hC.vanish
    intro hcand
    have hle := le_of_candidateExp h k hk hmin hcand
    rw [hla, div_le_div_iff_of_pos_right hQ'] at hle
    have : a₀ ≤ m' := by exact_mod_cast hle
    omega
  have hiso := absSpectralSum_isolated (D := n) hQ C hpred N
  unfold absSpectralSum at hiso
  rw [hla] at hrem
  rw [hiso, ← hla, hI] at hrem
  simp only [hCeq] at hrem
  refine hrem.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg hN0 _)
    (pow_nonneg (by linarith [Real.log_nonneg hN]) _)))
  exact cutoffBound_mono n k β hβ hL0 (by rw [abs_of_nonneg hR]; exact ha) (mass_nonneg _) le_rfl
    (abs_nonneg a) ha

/-- Constant-phase coefficients are bounded on compact phase sets. -/
theorem constPhase_coeff_bounded (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) (j : ℕ)
    (R : ℝ) :
    ∃ M : ℝ, ∀ a : ℝ, |a| ≤ R → |familySpectralCoeff n h k β (constFamily a) cη l j| ≤ M := by
  have hcont : Continuous fun a => familySpectralCoeff n h k β (constFamily a) cη l j :=
    continuous_iff_continuousAt.2 fun a =>
      (hasDerivAt_constPhase_coeff n h k hk hβ hη hl j a).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M, fun a ha => ?_⟩
  have := hM a (by rw [mem_Icc]; constructor <;> linarith [abs_le.1 ha])
  simpa [Real.norm_eq_abs] using this

/-- **Compact-uniform constant-phase two-term remainder**:
`sup_{|a| ≤ R} |log N (𝒵_N[η;a]/(N^{-λ}L^{m−1}) − A(a)) − B(a)| → 0`. -/
theorem constPhase_twoTerm_uniform (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ a : ℝ, |a| ≤ R →
      |Real.log N * (origPhaseIntegral n h k β N 1 (fun _ => a) η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) -
        constPhaseSecondCoeff n h k β cη a l| ≤ ε := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  have h1Q : (0 : ℝ) < 1 / latticeQ k := by positivity
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  set m := multCount (ratioExp h k) l with hm
  have hm1 : 1 ≤ m := multCount_pos _ _ hatt
  have hmn : m ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  obtain ⟨K, hK⟩ := constPhase_remainder_uniform n h k hk hβ hη hev hmin hatt hR
  -- coefficient bounds
  obtain ⟨Mq, hMq⟩ : ∃ Mq : ℕ → ℝ, ∀ q, ∀ a : ℝ, |a| ≤ R →
      |familySpectralCoeff n h k β (constFamily a) cη l q| ≤ Mq q :=
    ⟨fun q => Classical.choose (constPhase_coeff_bounded n h k hk hβ hη hl0 q R),
      fun q => Classical.choose_spec (constPhase_coeff_bounded n h k hk hβ hη hl0 q R)⟩
  set M : ℝ := ∑ q ∈ Finset.range (m - 2), |Mq q| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ a : ℝ, |a| ≤ R →
      ∑ q ∈ Finset.range (m - 2), |familySpectralCoeff n h k β (constFamily a) cη l q| ≤ M :=
    fun a ha => Finset.sum_le_sum fun q _ => (hMq q a ha).trans (le_abs_self _)
  -- the deterministic majorant
  have hrate : Tendsto (fun N : ℝ => |K| * (N ^ (-(1 / (latticeQ k : ℝ))) *
      (1 + Real.log N) ^ (n + 1)) + M / Real.log N) atTop (𝓝 0) := by
    have h1 := (tendsto_cutoff_ratio (n + 1) (μ := 0) (L := 1 / latticeQ k) h1Q).const_mul |K|
    have h2 := tendsto_inv_log.const_mul M
    simp only [neg_zero, Real.rpow_zero, div_one, mul_zero] at h1 h2
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [div_eq_mul_inv]
  filter_upwards [hrate.eventually (gt_mem_nhds hε), eventually_ge_atTop (Real.exp 1)] with N hN hNe
  intro a ha
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) hNe
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    exact hNe
  have hL0 : 0 < Real.log N := by linarith
  have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  have hLm : Real.log N ^ (m - 1) ≠ 0 := pow_ne_zero _ hL0.ne'
  -- vanishing above `m − 1` and the leading identification
  obtain ⟨hzero, -⟩ := constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt
  -- split: remainder part and polynomial part
  set Z := origPhaseIntegral n h k β N 1 (fun _ => a) η with hZ
  set P := ∑ q ∈ Finset.range (n + 1),
    familySpectralCoeff n h k β (constFamily a) cη l q * Real.log N ^ q with hP
  set A := familySpectralCoeff n h k β (constFamily a) cη l (m - 1) with hA
  set B := constPhaseSecondCoeff n h k β cη a l with hB
  have hsplit : Real.log N * (Z / (N ^ (-l) * Real.log N ^ (m - 1)) - A) - B =
      (Z - N ^ (-l) * P) * Real.log N / (N ^ (-l) * Real.log N ^ (m - 1)) +
        (Real.log N * (P / Real.log N ^ (m - 1) - A) - B) := by
    field_simp
    ring
  -- the remainder part
  have hrem : |(Z - N ^ (-l) * P) * Real.log N / (N ^ (-l) * Real.log N ^ (m - 1))| ≤
      |K| * (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1)) := by
    have hb := hK a ha N hN1.le
    have hsplitpow : N ^ (-(l + 1 / latticeQ k)) = N ^ (-l) * N ^ (-(1 / (latticeQ k : ℝ))) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    rw [hsplitpow] at hb
    have hden : 0 < N ^ (-l) * Real.log N ^ (m - 1) := by positivity
    rw [abs_div, abs_of_pos hden, abs_mul, abs_of_pos hL0, div_le_iff₀ hden]
    have hLm1 : 1 ≤ Real.log N ^ (m - 1) := one_le_pow₀ hL1
    calc |Z - N ^ (-l) * P| * Real.log N
        ≤ K * (N ^ (-l) * N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ n) * Real.log N :=
          mul_le_mul_of_nonneg_right hb hL0.le
      _ ≤ |K| * (N ^ (-l) * N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ n) *
          (1 + Real.log N) := by
          gcongr <;> first | exact le_abs_self K | linarith
      _ = |K| * (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1)) * N ^ (-l) := by
          rw [pow_succ]
          ring
      _ ≤ |K| * (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1)) *
          (N ^ (-l) * Real.log N ^ (m - 1)) := by
          gcongr
          exact le_mul_of_one_le_right (by positivity) hLm1
  -- the polynomial part
  have hpoly : |Real.log N * (P / Real.log N ^ (m - 1) - A) - B| ≤ M / Real.log N := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1' : m = 1 := by omega
      have hP1 : P = A := by
        rw [hP, hA, hm1', Nat.sub_self]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro q _ hq
          rw [hzero q (by rw [← hm]; omega), zero_mul]
        · intro h0
          exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h0
      have hB0 : B = 0 := by
        rw [hB]
        unfold constPhaseSecondCoeff
        rw [← hm, if_neg (by omega)]
      rw [hP1, hB0, hm1', Nat.sub_self, pow_zero, div_one, sub_self, mul_zero, sub_zero, abs_zero]
      exact div_nonneg hM0 hL0.le
    · obtain ⟨r, hr⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
      have hr1 : r + 1 ≤ n := by omega
      have e1 : r + 2 - 1 = r + 1 := by omega
      have e2 : r + 2 - 2 = r := by omega
      have hBr : B = familySpectralCoeff n h k β (constFamily a) cη l r := by
        rw [hB]
        unfold constPhaseSecondCoeff
        rw [← hm, hr, if_pos (by omega), e2]
      have hAr : A = familySpectralCoeff n h k β (constFamily a) cη l (r + 1) := by
        rw [hA, hr, e1]
      have hz : ∀ q, r + 1 < q → familySpectralCoeff n h k β (constFamily a) cη l q = 0 := by
        intro q hq
        exact hzero q (by rw [← hm, hr, e1]; exact hq)
      have hbound := twoTerm_split_bound
        (fun q => familySpectralCoeff n h k β (constFamily a) cη l q) n r hr1 hz hL1
      have hLr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hL0.ne'
      have e : Real.log N * (P / Real.log N ^ (m - 1) - A) - B =
          P / Real.log N ^ r - A * Real.log N - B := by
        rw [hr, e1, pow_succ]
        field_simp
        try ring
      rw [e, hBr, hAr]
      rw [hr, e2] at hM
      exact hbound.trans (div_le_div_of_nonneg_right (hM a ha) hL0.le)
  rw [hsplit]
  calc |(Z - N ^ (-l) * P) * Real.log N / (N ^ (-l) * Real.log N ^ (m - 1)) +
        (Real.log N * (P / Real.log N ^ (m - 1) - A) - B)|
      ≤ |(Z - N ^ (-l) * P) * Real.log N / (N ^ (-l) * Real.log N ^ (m - 1))| +
        |Real.log N * (P / Real.log N ^ (m - 1) - A) - B| := abs_add_le _ _
    _ ≤ |K| * (N ^ (-(1 / (latticeQ k : ℝ))) * (1 + Real.log N) ^ (n + 1)) + M / Real.log N :=
        add_le_add hrem hpoly
    _ ≤ ε := hN.le

end Grammar
