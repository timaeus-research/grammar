/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.DataIntegralContinuity

/-!
# Ordered normalised remainders, uniformly on data balls (Stage S6 — the deterministic core of A2)

Unit 275 (review v27 should-fix 4–5). Order the index pairs `(ν, q)` of the Taylor-tree expansion
by `(ν, q) ≺ (μ, j) ↔ ν < μ ∨ (ν = μ ∧ j < q)` — smaller exponent first, and at equal exponent the
**larger** log power first (`precedes`). For a target `(μ, j)` with `μ` on the exponent lattice
`Q⁻¹ℕ` (`Q = 2∏kᵢ`) and `j ≤ n`, the predecessors form the finite set `predSet` and the **ordered
normalised remainder** is

`R_N^{μ,j}(x) = (Z(N; x) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(x) N^{-ν} (log N)^q) / (N^{-μ} (log N)^j)`

(`orderedRemainder`). **Theorem** (`tendstoUniformlyOn_orderedRemainder`): on every data ball
`‖x‖ ≤ R`, `R_N^{μ,j}(x) → C_{μ,j}(x)` uniformly as `N → ∞`. Proof: with the cutoff `L = μ + 1`,
`Z − ∑_{≺} − C_{μ,j} N^{-μ}(log N)^j` is the cutoff error plus the finitely many retained terms
with `ν > μ` or `(ν = μ, q < j)`; after division by `N^{-μ}(log N)^j` the cutoff error is
`O(N^{-(L-μ)} (1 + log N)^n)` (`dataTaylorTree_cutoff_bound`, uniform on the ball), the
terms with `ν > μ` are `O(N^{-(ν-μ)} (1 + log N)^n)`, and the terms with `ν = μ, q < j` are
`O(1/log N)`, all with constants uniform on the ball (the coefficients are bounded on the ball by
Headline XXXIV). Thresholds: `N ≥ e` and `N b^{2|k|} ≥ 1`. This is the deterministic input for the
convergence in distribution of the remainders (A2); no probability enters here.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

open scoped Classical

/-- The asymptotic ordering: `(ν, q) ≺ (μ, j)` iff `ν < μ`, or `ν = μ` and `q > j`. -/
def precedes (p q : ℝ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)

theorem precedes_irrefl (p : ℝ × ℕ) : ¬ precedes p p := by
  unfold precedes; simp

/-- The finite index set of the truncation below `L`: `Λ_L × {0, …, n}`. -/
noncomputable def indexSet (n Q : ℕ) (L : ℝ) : Finset (ℝ × ℕ) :=
  latticeBelow Q L ×ˢ Finset.range (n + 1)

open scoped Classical in
/-- The predecessors of the target `(μ, j)`. -/
noncomputable def predSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) :=
  (indexSet n Q (μ + 1)).filter fun p => precedes p (μ, j)

/-- One term `C_{ν,q}(x) N^{-ν} (log N)^q` of the expansion. -/
noncomputable def expTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1))
    (N : ℝ) (p : ℝ × ℕ) : ℝ :=
  dataBoxCoeff n h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)

/-- The sum of the predecessor terms. -/
noncomputable def predSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1))
    (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  ∑ p ∈ predSet n (latticeQ k) μ j, expTerm n h k β b x N p

/-- **The ordered normalised remainder** at the target `(μ, j)`. -/
noncomputable def orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  (dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N) / (N ^ (-μ) * Real.log N ^ j)

/-- The spectral sum as a sum over the index set. -/
theorem spectralSum_eq_sum_indexSet (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (L N : ℝ) :
    ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b x μ j * Real.log N ^ j =
      ∑ p ∈ indexSet n (latticeQ k) L, expTerm n h k β b x N p := by
  unfold indexSet expTerm
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A uniform bound for a coefficient on the data ball of radius `R`. -/
noncomputable def coeffBallBound (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) :
    ℝ :=
  |dataBoxCoeff n h k β b 0 μ j| + dataLipConst n h k β b μ j R * R

theorem abs_dataBoxCoeff_le_ballBound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) {R : ℝ} {x : DataSpace (n + 1)}
    (hx : ‖x‖ ≤ R) : |dataBoxCoeff n h k β b x μ j| ≤ coeffBallBound n h k β b μ j R := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have h0 : ‖(0 : DataSpace (n + 1))‖ ≤ R := by simpa using hR0
  have := abs_dataBoxCoeff_sub_le n h k hk β hβ hb h0 hx μ j
  rw [sub_zero] at this
  unfold coeffBallBound
  have hL := dataLipConst_nonneg n h k β hβ hb μ j hR0
  calc |dataBoxCoeff n h k β b x μ j|
      ≤ |dataBoxCoeff n h k β b 0 μ j| +
          |dataBoxCoeff n h k β b x μ j - dataBoxCoeff n h k β b 0 μ j| := by
        have := abs_sub_abs_le_abs_sub (dataBoxCoeff n h k β b x μ j) (dataBoxCoeff n h k β b 0 μ j)
        linarith
    _ ≤ _ := add_le_add le_rfl (this.trans (mul_le_mul_of_nonneg_left hx hL))

/-! ### Scalar asymptotics -/

/-- `N^{-s} (1 + log N)^n → 0` for `s > 0`. -/
theorem tendsto_rpow_neg_mul_one_add_log_pow (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℝ => N ^ (-s) * (1 + Real.log N) ^ n) atTop (𝓝 0) := by
  have h := (rpow_neg_mul_log_pow_isLittleO n (L := s) (L' := 0) hs).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [neg_zero, Real.rpow_zero, div_one]

/-- `N^{-L} (1 + log N)^n / N^{-μ} → 0` for `μ < L`. -/
theorem tendsto_cutoff_ratio (n : ℕ) {L μ : ℝ} (hμL : μ < L) :
    Tendsto (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-μ)) atTop (𝓝 0) :=
  (rpow_neg_mul_log_pow_isLittleO n hμL).tendsto_div_nhds_zero

/-- `1 / log N → 0`. -/
theorem tendsto_inv_log : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop

/-- The majorant of a retained term `(ν, q)` after normalisation at `(μ, j)`. -/
noncomputable def termMajorant (n : ℕ) (μ : ℝ) (p : ℝ × ℕ) (N : ℝ) : ℝ :=
  if p.1 = μ then (Real.log N)⁻¹ else N ^ (-(p.1 - μ)) * (1 + Real.log N) ^ n

theorem tendsto_termMajorant (n : ℕ) {μ : ℝ} {p : ℝ × ℕ} (hp : μ ≤ p.1) :
    Tendsto (termMajorant n μ p) atTop (𝓝 0) := by
  unfold termMajorant
  split_ifs with h
  · exact tendsto_inv_log
  · exact tendsto_rpow_neg_mul_one_add_log_pow n (by
      rcases lt_or_eq_of_le hp with h' | h'
      · linarith
      · exact absurd h'.symm h)

/-- The normalised retained term is at most its majorant times the ball bound (for `N ≥ e`). -/
theorem abs_expTerm_div_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) {μ : ℝ}
    {j : ℕ} {p : ℝ × ℕ} (hp : μ ≤ p.1) (hpq : p.1 = μ → p.2 < j) (hpn : p.2 ≤ n) {N : ℝ}
    (hN : Real.exp 1 ≤ N) :
    |expTerm n h k β b x N p / (N ^ (-μ) * Real.log N ^ j)| ≤
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N := by
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hN
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  have hlog0 : 0 < Real.log N := by linarith
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hC := abs_dataBoxCoeff_le_ballBound n h k hk β hβ hb p.1 p.2 hx
  have hC0 : 0 ≤ |dataBoxCoeff n h k β b x p.1 p.2| := abs_nonneg _
  unfold expTerm termMajorant
  rw [abs_div, abs_of_pos hD, abs_mul, div_le_iff₀ hD]
  have hpow : 0 < N ^ (-p.1) * Real.log N ^ p.2 := by positivity
  rw [abs_of_pos hpow]
  split_ifs with heq
  · -- equal exponent, lower log power: `(log N)^q ≤ (log N)^j / log N`
    have hq : p.2 + 1 ≤ j := hpq heq
    rw [heq] at hpow hC hC0 ⊢
    have h1 : Real.log N ^ p.2 * Real.log N ≤ Real.log N ^ j := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hlog1 hq
    calc |dataBoxCoeff n h k β b x μ p.2| * (N ^ (-μ) * Real.log N ^ p.2)
        ≤ coeffBallBound n h k β b μ p.2 R * (N ^ (-μ) * Real.log N ^ p.2) :=
          mul_le_mul_of_nonneg_right hC hpow.le
      _ = coeffBallBound n h k β b μ p.2 R * (Real.log N)⁻¹ *
            (N ^ (-μ) * (Real.log N ^ p.2 * Real.log N)) := by
          field_simp
      _ ≤ coeffBallBound n h k β b μ p.2 R * (Real.log N)⁻¹ * (N ^ (-μ) * Real.log N ^ j) := by
          have hB : 0 ≤ coeffBallBound n h k β b μ p.2 R := hC0.trans hC
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB (inv_nonneg.2 hlog0.le))
          exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
  · -- larger exponent: `N^{-ν} (log N)^q ≤ N^{-(ν-μ)} (1+log N)^n · N^{-μ} (log N)^j`
    have h1 : Real.log N ^ p.2 ≤ (1 + Real.log N) ^ n := by
      calc Real.log N ^ p.2 ≤ (1 + Real.log N) ^ p.2 :=
            pow_le_pow_left₀ hlog0.le (by linarith) _
        _ ≤ (1 + Real.log N) ^ n := pow_le_pow_right₀ (by linarith) hpn
    have h2 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have h3 : N ^ (-p.1) = N ^ (-(p.1 - μ)) * N ^ (-μ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hB : 0 ≤ coeffBallBound n h k β b p.1 p.2 R := hC0.trans hC
    have hr : 0 ≤ N ^ (-(p.1 - μ)) := Real.rpow_nonneg hN0.le _
    calc |dataBoxCoeff n h k β b x p.1 p.2| * (N ^ (-p.1) * Real.log N ^ p.2)
        ≤ coeffBallBound n h k β b p.1 p.2 R * (N ^ (-p.1) * Real.log N ^ p.2) :=
          mul_le_mul_of_nonneg_right hC hpow.le
      _ = coeffBallBound n h k β b p.1 p.2 R * (N ^ (-(p.1 - μ)) * Real.log N ^ p.2) *
            (N ^ (-μ) * 1) := by rw [h3]; ring
      _ ≤ coeffBallBound n h k β b p.1 p.2 R * (N ^ (-(p.1 - μ)) * (1 + Real.log N) ^ n) *
            (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hB)
            (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)) (by positivity)
            (mul_nonneg hB (mul_nonneg hr (by positivity)))

/-- The retained terms other than the predecessors and the target. -/
noncomputable def restSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) :=
  indexSet n Q (μ + 1) \ (predSet n Q μ j ∪ {(μ, j)})

theorem mem_restSet {n Q : ℕ} {μ : ℝ} {j : ℕ} {p : ℝ × ℕ} (hp : p ∈ restSet n Q μ j) :
    p ∈ indexSet n Q (μ + 1) ∧ μ ≤ p.1 ∧ (p.1 = μ → p.2 < j) := by
  unfold restSet predSet at hp
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hp
  obtain ⟨hi, hnot⟩ := hp
  refine ⟨hi, ?_, ?_⟩
  · by_contra hlt
    exact hnot (Or.inl ⟨hi, Or.inl (lt_of_not_ge hlt)⟩)
  · intro heq
    by_contra hge
    rcases lt_or_eq_of_le (le_of_not_gt hge) with hlt | heq2
    · exact hnot (Or.inl ⟨hi, Or.inr ⟨heq, hlt⟩⟩)
    · exact hnot (Or.inr (Prod.ext heq heq2.symm))

theorem mem_indexSet_snd_le {n Q : ℕ} {L : ℝ} {p : ℝ × ℕ} (hp : p ∈ indexSet n Q L) : p.2 ≤ n := by
  unfold indexSet at hp
  rw [Finset.mem_product] at hp
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hp.2)

/-- The uniform majorant of `|R_N^{μ,j}(x) − C_{μ,j}(x)|` on the ball of radius `R`. -/
noncomputable def remainderMajorant (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ)
    (N : ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
      ((b ^ (2 * ∑ i, k i)) ^ (-(μ + 1)) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n) *
      (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) +
    ∑ p ∈ restSet n (latticeQ k) μ j,
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N

theorem tendsto_remainderMajorant (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) :
    Tendsto (remainderMajorant n h k β b μ j R) atTop (𝓝 0) := by
  unfold remainderMajorant
  have h1 := (tendsto_cutoff_ratio n (L := μ + 1) (μ := μ) (by linarith)).const_mul
    (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
      ((b ^ (2 * ∑ i, k i)) ^ (-(μ + 1)) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n))
  rw [mul_zero] at h1
  have h2 : Tendsto (fun N => ∑ p ∈ restSet n (latticeQ k) μ j,
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N) atTop (𝓝 0) := by
    have := tendsto_finset_sum (restSet n (latticeQ k) μ j) fun p hp =>
      (tendsto_termMajorant n (mem_restSet hp).2.1).const_mul (coeffBallBound n h k β b p.1 p.2 R)
    simpa using this
  simpa using h1.add h2

/-- **The explicit majorant estimate**: for `‖x‖ ≤ R`, `N ≥ e` and `N b^{2|k|} ≥ 1`,
`|R_N^{μ,j}(x) − C_{μ,j}(x)| ≤ remainderMajorant n h k β b μ j R N`. -/
theorem abs_orderedRemainder_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) {N : ℝ}
    (hNe : Real.exp 1 ≤ N) (hNb : 1 ≤ boxScale k b N) :
    |orderedRemainder n h k β b x μ j N - dataBoxCoeff n h k β b x μ j| ≤
      remainderMajorant n h k β b μ j R N := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  obtain ⟨m, hm⟩ := hμ
  have hμ0 : 0 ≤ μ := by rw [hm]; positivity
  set Q := latticeQ k with hQdef
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  -- the target lies in the index set of the cutoff `μ + 1`
  have htarget : (μ, j) ∈ indexSet n Q (μ + 1) := by
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.lt_succ_of_le hj)⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; linarith)
  have hpred_sub : predSet n Q μ j ⊆ indexSet n Q (μ + 1) := Finset.filter_subset _ _
  have htarget_notin : (μ, j) ∉ predSet n Q μ j := by
    unfold predSet
    rw [Finset.mem_filter]
    exact fun hcontra => precedes_irrefl _ hcontra.2
  have hsub : predSet n Q μ j ∪ {(μ, j)} ⊆ indexSet n Q (μ + 1) :=
    Finset.union_subset hpred_sub (Finset.singleton_subset_iff.2 htarget)
  -- the key algebraic decomposition
  have hdecomp :
      dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
          dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j) =
        (dataBoxIntegral n h k β N b x -
          ∑ p ∈ indexSet n Q (μ + 1), expTerm n h k β b x N p) +
        ∑ p ∈ restSet n Q μ j, expTerm n h k β b x N p := by
    unfold restSet predSum
    rw [← Finset.sum_sdiff hsub, Finset.sum_union (Finset.disjoint_singleton_right.2 htarget_notin),
      Finset.sum_singleton]
    unfold expTerm
    ring
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  -- `R_N − C = (Z − pred − C D)/D`
  have hRN : orderedRemainder n h k β b x μ j N - dataBoxCoeff n h k β b x μ j =
      (dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
        dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j)) /
          (N ^ (-μ) * Real.log N ^ j) := by
    unfold orderedRemainder
    have hD' := hD.ne'
    field_simp
  rw [hRN, hdecomp, add_div, Finset.sum_div]
  unfold remainderMajorant
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the cutoff error
    have hcut := dataTaylorTree_cutoff_bound n h k hk β hβ (L := μ + 1) (by linarith) hb hN0 hNb hx
    rw [spectralSum_eq_sum_indexSet] at hcut
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    refine hcut.trans ?_
    have hK0 : 0 ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R :=
      mul_nonneg (by positivity) (dataCutoffConst_nonneg n k β hβ _ ((norm_nonneg x).trans hx))
    have hbs : boxScale k b N = N * c := by unfold boxScale; rw [hc]
    have h1 : boxScale k b N ^ (-(μ + 1)) = N ^ (-(μ + 1)) * c ^ (-(μ + 1)) := by
      rw [hbs, Real.mul_rpow hN0.le hc0.le]
    have h2 : (1 + Real.log (boxScale k b N)) ^ n ≤
        (1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n := by
      rw [hbs, ← mul_pow]
      exact pow_le_pow_left₀ (by have := Real.log_nonneg (show 1 ≤ N * c by rwa [← hbs]); linarith)
        (one_add_log_mul_le hN1.le hc0) n
    have h3 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hr0 : 0 ≤ N ^ (-(μ + 1)) := Real.rpow_nonneg hN0.le _
    have hcr0 : 0 ≤ c ^ (-(μ + 1)) := Real.rpow_nonneg hc0.le _
    have hlogN : 0 ≤ 1 + Real.log N := by linarith
    calc b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (boxScale k b N ^ (-(μ + 1)) * (1 + Real.log (boxScale k b N)) ^ n)
        ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (N ^ (-(μ + 1)) * c ^ (-(μ + 1)) * ((1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n)) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hcr0)) hK0
      _ = b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * 1) := by
          field_simp
      _ ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3
            (Real.rpow_nonneg hN0.le _)) ?_
          have : 0 ≤ N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ) := by positivity
          exact mul_nonneg (mul_nonneg hK0 (mul_nonneg hcr0 (by positivity))) this
  · -- the retained terms
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨hpi, hpμ, hpq⟩ := mem_restSet hp
    exact abs_expTerm_div_le n h k hk β hβ hb hx hpμ hpq (mem_indexSet_snd_le hpi) hNe

/-- **Ordered normalised remainders converge uniformly on data balls**: for a target `(μ, j)` with
`μ ∈ Q⁻¹ℕ` and `j ≤ n`, `R_N^{μ,j}(x) → C_{μ,j}(x)` uniformly in `‖x‖ ≤ R` as `N → ∞`. -/
theorem tendstoUniformlyOn_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => orderedRemainder n h k β b x μ j N)
      (fun x => dataBoxCoeff n h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := tendsto_remainderMajorant n h k β b μ j R
  have hev : ∀ᶠ N in atTop, remainderMajorant n h k β b μ j R N < ε :=
    hmaj.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 / c)] with N hNε hNe
    hNc x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_orderedRemainder_sub_le n h k hk β hβ hb hμ hj hx' hNe hscale) hNε

end Grammar
