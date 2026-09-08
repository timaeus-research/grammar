/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticTangential

/-!
# Abstract finite-cutoff expansions: sums, lattice refinement, ordered remainders (Stage S12)

Unit 281 (Astra #34 / review v29, assembly prerequisites). A real function `Z` of the sample size
has a **finite-cutoff expansion** on the lattice `Q⁻¹ℕ` with log degrees `≤ D`
(`CutoffExpansion Q D Z c`) if for every cutoff `L > 0` there is a constant `K` with
`|Z N − ∑_{μ ∈ Λ^Q_L} N^{-μ} ∑_{j ≤ D} c μ j (log N)^j| ≤ K N^{-L} (1 + log N)^D` eventually in `N`.
The chart-level Taylor tree provides such expansions (unit 282). This unit develops the purely
spectral bookkeeping needed to assemble charts: expansions add (`CutoffExpansion.add`,
`CutoffExpansion.sum`), a coefficient system supported on a coarser lattice `Q⁻¹ℕ ⊂ Q'⁻¹ℕ`
(`Q ∣ Q'`) gives an expansion on the finer lattice (`CutoffExpansion.refine`), a coefficient system
vanishing above degree `D` gives an expansion with any larger degree bound
(`CutoffExpansion.pad`), and the **abstract quantitative ordered-remainder estimate**
(`abs_abstractRemainder_sub_le`): if the cutoff bound at `L = μ + 1` holds with constant `K` and all
coefficients on the index set are bounded by `C`, then for `N ≥ e`
`|R_N^{μ,j} − c μ j| ≤ K · N^{-(μ+1)}(1+log N)^D / N^{-μ} + C · ∑_{rest} termMajorant`, with the
same finite predecessor/rest sets and majorants as unit 275. Hence every finite-cutoff expansion has
convergent ordered normalised remainders (`tendsto_abstractRemainder`), and uniformity over a family
follows from uniform `K`, `C` — which is how the global (assembled) remainders are treated.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

/-- One term `c_{ν,q} N^{-ν} (log N)^q` of an abstract expansion. -/
noncomputable def absTerm (c : ℝ → ℕ → ℝ) (N : ℝ) (p : ℝ × ℕ) : ℝ :=
  c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)

/-- The spectral sum of an abstract coefficient system below the cutoff `L`. -/
noncomputable def absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) : ℝ :=
  ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j

theorem absSpectralSum_eq_sum_indexSet (Q D : ℕ) (c : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D c L N = ∑ p ∈ indexSet D Q L, absTerm c N p := by
  unfold absSpectralSum indexSet absTerm
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Finite-cutoff expansion** of `Z` on the lattice `Q⁻¹ℕ` with log degrees `≤ D` and
coefficients `c`. -/
def CutoffExpansion (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ K : ℝ, ∀ᶠ N in atTop,
    |Z N - absSpectralSum Q D c L N| ≤ K * (N ^ (-L) * (1 + Real.log N) ^ D)

theorem CutoffExpansion.add {Q D : ℕ} {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ : ℝ → ℕ → ℝ}
    (h₁ : CutoffExpansion Q D Z₁ c₁) (h₂ : CutoffExpansion Q D Z₂ c₂) :
    CutoffExpansion Q D (fun N => Z₁ N + Z₂ N) (fun μ j => c₁ μ j + c₂ μ j) := by
  intro L hL
  obtain ⟨K₁, hK₁⟩ := h₁ L hL
  obtain ⟨K₂, hK₂⟩ := h₂ L hL
  refine ⟨K₁ + K₂, ?_⟩
  filter_upwards [hK₁, hK₂] with N h1 h2
  have hsum : absSpectralSum Q D (fun μ j => c₁ μ j + c₂ μ j) L N =
      absSpectralSum Q D c₁ L N + absSpectralSum Q D c₂ L N := by
    unfold absSpectralSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  calc |Z₁ N + Z₂ N - (absSpectralSum Q D c₁ L N + absSpectralSum Q D c₂ L N)|
      = |(Z₁ N - absSpectralSum Q D c₁ L N) + (Z₂ N - absSpectralSum Q D c₂ L N)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

theorem CutoffExpansion.zero (Q D : ℕ) : CutoffExpansion Q D (fun _ => 0) (fun _ _ => 0) := by
  intro L hL
  refine ⟨0, Eventually.of_forall fun N => ?_⟩
  simp [absSpectralSum]

/-- Finite sums of expansions. -/
theorem CutoffExpansion.sum {ι : Type*} (s : Finset ι) {Q D : ℕ} {Z : ι → ℝ → ℝ}
    {c : ι → ℝ → ℕ → ℝ} (h : ∀ i ∈ s, CutoffExpansion Q D (Z i) (c i)) :
    CutoffExpansion Q D (fun N => ∑ i ∈ s, Z i N) (fun μ j => ∑ i ∈ s, c i μ j) := by
  induction s using Finset.induction_on with
  | empty => simpa using CutoffExpansion.zero Q D
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := h1.add h2
    simpa [Finset.sum_insert ha] using this

theorem latticeBelow_subset_of_dvd {Q Q' : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (hQQ : Q ∣ Q')
    (L : ℝ) : latticeBelow Q L ⊆ latticeBelow Q' L := by
  intro μ hμ
  obtain ⟨⟨m, rfl⟩, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
  obtain ⟨c, hc⟩ := hQQ
  refine (mem_latticeBelow_iff hQ').2 ⟨⟨m * c, ?_⟩, hlt⟩
  have hc0 : (c : ℝ) ≠ 0 := by
    rintro h0
    have : c = 0 := by exact_mod_cast h0
    subst this; simp at hc; omega
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [hc]
  push_cast
  field_simp

/-- **Lattice refinement**: a coefficient system supported on `Q⁻¹ℕ` has an expansion on any finer
lattice `Q'⁻¹ℕ` (`Q ∣ Q'`, `Q' > 0`). -/
theorem CutoffExpansion.refine {Q Q' D : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (hQQ : Q ∣ Q')
    {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0)
    (h : CutoffExpansion Q D Z c) : CutoffExpansion Q' D Z c := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨K, hK.mono fun N hN => ?_⟩
  have hsum : absSpectralSum Q' D c L N = absSpectralSum Q D c L N := by
    unfold absSpectralSum
    symm
    refine Finset.sum_subset (latticeBelow_subset_of_dvd hQ hQ' hQQ L) fun μ hμ' hμ => ?_
    have hzero : ∀ j, c μ j = 0 := by
      refine hc μ fun m hm => hμ ?_
      exact (mem_latticeBelow_iff hQ).2 ⟨⟨m, hm⟩, lt_of_mem_latticeBelow hQ' hμ'⟩
    simp [hzero]
  rw [hsum]; exact hN

/-- **Degree padding**: a coefficient system vanishing above degree `D` has an expansion with any
degree bound `D' ≥ D`. -/
theorem CutoffExpansion.pad {Q D D' : ℕ} (hD : D ≤ D') {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ j, D < j → c μ j = 0) (h : CutoffExpansion Q D Z c) : CutoffExpansion Q D' Z c := by
  intro L hL
  obtain ⟨K, hK⟩ := h L hL
  refine ⟨|K|, ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  have hsum : absSpectralSum Q D' c L N = absSpectralSum Q D c L N := by
    unfold absSpectralSum
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    symm
    refine Finset.sum_subset (fun j hj => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))) fun j _ hj => ?_
    have hDj : D < j := by
      by_contra hcon
      exact hj (Finset.mem_range.2 (by omega))
    simp [hc μ j hDj]
  rw [hsum]
  refine hN.trans ?_
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have h1 : (1 + Real.log N) ^ D ≤ (1 + Real.log N) ^ D' := pow_le_pow_right₀ hlog hD
  have h2 : 0 ≤ N ^ (-L) := Real.rpow_nonneg (by linarith) _
  calc K * (N ^ (-L) * (1 + Real.log N) ^ D)
      ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ D) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ D') :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h2) (abs_nonneg _)

/-! ### The abstract ordered remainder -/

/-- The abstract predecessor sum. -/
noncomputable def absPredSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  ∑ p ∈ predSet D Q μ j, absTerm c N p

/-- The abstract ordered normalised remainder at the target `(μ, j)`. -/
noncomputable def abstractRemainder (Q D : ℕ) (Z : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ)
    (N : ℝ) : ℝ :=
  (Z N - absPredSum Q D c μ j N) / (N ^ (-μ) * Real.log N ^ j)

/-- A normalised retained term is at most `C · termMajorant` when `|c_{ν,q}| ≤ C` (for `N ≥ e`). -/
theorem abs_absTerm_div_le {c : ℝ → ℕ → ℝ} {C : ℝ} {D : ℕ} {μ : ℝ} {j : ℕ} {p : ℝ × ℕ}
    (hC : |c p.1 p.2| ≤ C) (hp : μ ≤ p.1) (hpq : p.1 = μ → p.2 < j) (hpn : p.2 ≤ D) {N : ℝ}
    (hN : Real.exp 1 ≤ N) :
    |absTerm c N p / (N ^ (-μ) * Real.log N ^ j)| ≤ C * termMajorant D μ p N := by
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hN
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  have hlog0 : 0 < Real.log N := by linarith
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  unfold absTerm termMajorant
  rw [abs_div, abs_of_pos hD, abs_mul, div_le_iff₀ hD]
  have hpow : 0 < N ^ (-p.1) * Real.log N ^ p.2 := by positivity
  rw [abs_of_pos hpow]
  split_ifs with heq
  · have hq : p.2 + 1 ≤ j := hpq heq
    rw [heq] at hpow hC ⊢
    have h1 : Real.log N ^ p.2 * Real.log N ≤ Real.log N ^ j := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hlog1 hq
    calc |c μ p.2| * (N ^ (-μ) * Real.log N ^ p.2)
        ≤ C * (N ^ (-μ) * Real.log N ^ p.2) := mul_le_mul_of_nonneg_right hC hpow.le
      _ = C * (Real.log N)⁻¹ * (N ^ (-μ) * (Real.log N ^ p.2 * Real.log N)) := by
          field_simp
      _ ≤ C * (Real.log N)⁻¹ * (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (inv_nonneg.2 hlog0.le))
          exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
  · have h1 : Real.log N ^ p.2 ≤ (1 + Real.log N) ^ D := by
      calc Real.log N ^ p.2 ≤ (1 + Real.log N) ^ p.2 :=
            pow_le_pow_left₀ hlog0.le (by linarith) _
        _ ≤ (1 + Real.log N) ^ D := pow_le_pow_right₀ (by linarith) hpn
    have h2 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have h3 : N ^ (-p.1) = N ^ (-(p.1 - μ)) * N ^ (-μ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hr : 0 ≤ N ^ (-(p.1 - μ)) := Real.rpow_nonneg hN0.le _
    calc |c p.1 p.2| * (N ^ (-p.1) * Real.log N ^ p.2)
        ≤ C * (N ^ (-p.1) * Real.log N ^ p.2) := mul_le_mul_of_nonneg_right hC hpow.le
      _ = C * (N ^ (-(p.1 - μ)) * Real.log N ^ p.2) * (N ^ (-μ) * 1) := by rw [h3]; ring
      _ ≤ C * (N ^ (-(p.1 - μ)) * (1 + Real.log N) ^ D) * (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hC0)
            (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)) (by positivity)
            (mul_nonneg hC0 (mul_nonneg hr (by positivity)))

/-- **The abstract quantitative ordered-remainder estimate.** If the cutoff bound at `L = μ + 1`
holds with constant `K` at `N`, and `|c_{ν,q}| ≤ C` on the index set, then for `N ≥ e`
`|R_N^{μ,j} − c_{μ,j}| ≤ K · N^{-(μ+1)}(1+log N)^D / N^{-μ} + C ∑_{rest} termMajorant`. -/
theorem abs_abstractRemainder_sub_le {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ} {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) {K C : ℝ} {N : ℝ}
    (hNe : Real.exp 1 ≤ N)
    (hcut : |Z N - absSpectralSum Q D c (μ + 1) N| ≤ K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D))
    (hC : ∀ p ∈ indexSet D Q (μ + 1), |c p.1 p.2| ≤ C) :
    |abstractRemainder Q D Z c μ j N - c μ j| ≤
      K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D / N ^ (-μ)) +
        C * ∑ p ∈ restSet D Q μ j, termMajorant D μ p N := by
  obtain ⟨m, hm⟩ := hμ
  have hμ0 : 0 ≤ μ := by rw [hm]; positivity
  have htarget : (μ, j) ∈ indexSet D Q (μ + 1) := by
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.lt_succ_of_le hj)⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; linarith)
  have hpred_sub : predSet D Q μ j ⊆ indexSet D Q (μ + 1) := Finset.filter_subset _ _
  have htarget_notin : (μ, j) ∉ predSet D Q μ j := by
    unfold predSet
    rw [Finset.mem_filter]
    exact fun hcontra => precedes_irrefl _ hcontra.2
  have hsub : predSet D Q μ j ∪ {(μ, j)} ⊆ indexSet D Q (μ + 1) :=
    Finset.union_subset hpred_sub (Finset.singleton_subset_iff.2 htarget)
  have hdecomp : Z N - absPredSum Q D c μ j N - c μ j * (N ^ (-μ) * Real.log N ^ j) =
      (Z N - absSpectralSum Q D c (μ + 1) N) + ∑ p ∈ restSet D Q μ j, absTerm c N p := by
    unfold restSet absPredSum
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
    have hK0 : 0 ≤ K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D) :=
      (abs_nonneg _).trans hcut
    have hr : 0 < N ^ (-μ) := Real.rpow_pos_of_pos hN0 _
    calc K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D)
        = K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D / N ^ (-μ)) * (N ^ (-μ) * 1) := by
          field_simp
      _ ≤ K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D / N ^ (-μ)) *
          (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hr.le) ?_
          have : K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D / N ^ (-μ)) =
              K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D) / N ^ (-μ) := by ring
          rw [this]; exact div_nonneg hK0 hr.le
  · rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨hpi, hpμ, hpq⟩ := mem_restSet hp
    exact abs_absTerm_div_le (hC p hpi) hpμ hpq (mem_indexSet_snd_le hpi) hNe

/-- The abstract majorant tends to zero. -/
theorem tendsto_abstract_majorant (Q D : ℕ) (μ : ℝ) (j : ℕ) (K C : ℝ) :
    Tendsto (fun N : ℝ => K * (N ^ (-(μ + 1)) * (1 + Real.log N) ^ D / N ^ (-μ)) +
      C * ∑ p ∈ restSet D Q μ j, termMajorant D μ p N) atTop (𝓝 0) := by
  have h1 := (tendsto_cutoff_ratio D (L := μ + 1) (μ := μ) (by linarith)).const_mul K
  have h2 := (tendsto_finset_sum (restSet D Q μ j) fun p hp =>
    tendsto_termMajorant D (mem_restSet hp).2.1).const_mul C
  simpa using h1.add h2

/-- **Every finite-cutoff expansion has convergent ordered normalised remainders**: for
`μ ∈ Q⁻¹ℕ`, `j ≤ D`, `R_N^{μ,j} → c_{μ,j}`. -/
theorem tendsto_abstractRemainder {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ} {c : ℝ → ℕ → ℝ}
    (h : CutoffExpansion Q D Z c) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) {j : ℕ} (hj : j ≤ D) :
    Tendsto (fun N => abstractRemainder Q D Z c μ j N) atTop (𝓝 (c μ j)) := by
  obtain ⟨K, hK⟩ := h (μ + 1) (by obtain ⟨m, hm⟩ := hμ; rw [hm]; positivity)
  set C : ℝ := ∑ p ∈ indexSet D Q (μ + 1), |c p.1 p.2| with hCdef
  have hC : ∀ p ∈ indexSet D Q (μ + 1), |c p.1 p.2| ≤ C := fun p hp =>
    Finset.single_le_sum (fun q _ => abs_nonneg (c q.1 q.2)) hp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_abstract_majorant Q D μ j K C)
  filter_upwards [hK, eventually_ge_atTop (Real.exp 1)] with N hN hNe
  simp only [Real.norm_eq_abs, abs_abs]
  exact abs_abstractRemainder_sub_le hQ hμ hj hNe hN hC

end Grammar
