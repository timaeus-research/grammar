# Fidelity review v30 — Programme S tranche A3, units 281–284: abstract expansions, chart expansion, finite chart assembly, Headline XXXVII

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (repository `timaeus-research/grammar`, branch `tide/stochastic-taylor-tree`, pin `d92e2fb`) of the grammar paper's §4.3 (`thm:strataempiricalexpansion`). Reviews v27–v29 passed units 270–280: the weighted-ℓ¹ data space `DataSpace d`, canonical coefficients `dataBoxCoeff` (Lipschitz on balls, Headline XXXIV), the ordered normalised remainder with ordering `(ν,q) ≺ (μ,j) ↔ ν < μ ∨ (ν = μ ∧ j < q)` and index set `indexSet D Q L = latticeBelow Q L ×ˢ range (D+1)`, `predSet D Q μ j` (filter of `indexSet D Q (μ+1)` by `≺ (μ,j)`), `restSet`, `termMajorant D μ p N = if p.1 = μ then (log N)⁻¹ else N^{-(p.1−μ)}(1+log N)^D`, `mem_restSet`, `mem_indexSet_snd_le`, `tendsto_cutoff_ratio`, `tendsto_termMajorant`; Headline XXXV (one chart, no tangential variable) and Headline XXXVI (one stratum with tangential integration over a compact `K` with finite measure `ν`: `TangentialData K d = C(K, DataSpace d)`, `tanIntegral ν … x N = ∫_K Z(N; x v) dν`, `tanCoeff ν … x μ j = ∫_K C_{μ,j}(x v) dν`, `tanTaylorTree_cutoff_bound`, `dataCutoffConst`, `coeffBallBound`, `abs_dataBoxCoeff_le_ballBound`). Review v29's blocking prerequisites for assembly: common-lattice inclusion with padding SUPPORT theorems; global-target estimates for charts whose local target hypotheses fail; predecessor-sum compatibility; joint chart-data convergence; residual normalised at the target. Units 281–284 implement these. Please review the STATEMENTS (mechanical excerpts, docstring + statement up to `:=`; the extractor may truncate/duplicate — the source has exactly one of each; everything compiles with zero `sorry` and no additional axioms) and the two proofs reproduced in full.

## Statements

### Grammar/AbstractExpansion.lean

Ambient `variable` lines (as written in the file):
```lean

```

```lean
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

```
### Grammar/ChartExpansion.lean

Ambient `variable` lines (as written in the file):
```lean
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
  (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
```

```lean
/-!
# The chart-level Taylor tree as an abstract expansion (Stage S13)

Unit 282 (Astra #34 / review v29, assembly prerequisites). Padding support theorems for the
canonical coefficients — `C_{μ,j} = 0` for `j > n` (`dataBoxCoeff_eq_zero_of_lt`), for `μ` off
the candidate set (`dataBoxCoeff_eq_zero_of_not_candidate`), hence for `μ ∉ Q⁻¹ℕ`
(`dataBoxCoeff_eq_zero_of_not_lattice`), and the same for the integrated coefficients `𝒞_{μ,j}` —
and the **uniform chart cutoff bound in the sample size** (`tanCutoff_bound_N`): for `‖x‖ ≤ R`,
`N ≥ 1`, `N b^{2|k|} ≥ 1`,
`|𝒵(N;x) − ∑_{Λ_L} N^{-μ} ∑_j 𝒞_{μ,j}(x)(log N)^j| ≤ chartCutoffConst · N^{-L}(1+log N)^n`
with `chartCutoffConst n h k β b ν L R = ν(K) b^{|h|+d} dataCutoffConst(R) c^{-L} (1+|log c|)^n`,
`c = b^{2|k|}`. Consequently the integrated chart integral of every tangential datum is a
finite-cutoff expansion on its own lattice `Q⁻¹ℕ = (2∏kᵢ)⁻¹ℕ` with degrees `≤ n`
(`cutoffExpansion_tan`), which is what the chart assembly of the next unit sums.
-/

theorem dataBoxCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) : dataBoxCoeff n h k β b x μ j = 0 := by
  unfold dataBoxCoeff boxCoeff
  have : Finset.Ico j (n + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
  simp [this]

theorem dataBoxCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {μ : ℝ}
    (hμ : ¬ candidateExp h k μ) (j : ℕ) : dataBoxCoeff n h k β b x μ j = 0 := by
  rw [dataBoxCoeff_eq n h k β hb]
  have hz : ∀ q, familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q = 0 := fun q =>
    familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ (absSummable_xiCoord x)
      (absSummable_etaCoord x) hμ q
  simp [hz]

/-- The canonical coefficients vanish off the lattice `(2∏kᵢ)⁻¹ℕ`. -/
theorem dataBoxCoeff_eq_zero_of_not_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ k) (j : ℕ) : dataBoxCoeff n h k β b x μ j = 0 := by
  refine dataBoxCoeff_eq_zero_of_not_candidate n h k hk β hβ hb x (fun hc => ?_) j
  obtain ⟨m, hm⟩ := candidateExp_mem_lattice hk hc
  exact hμ m hm

section Tangential

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]

theorem tanCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : TangentialData K (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) :
    tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_lt n h k β b _ μ hj]

theorem tanCoeff_eq_zero_of_not_lattice (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) {μ : ℝ}
    (hμ : ∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ k) (j : ℕ) : tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_not_lattice n h k hk β hβ hb _ hμ j]

/-! ### The chart cutoff bound in the sample size -/

/-- The chart cutoff constant in the sample size: `ν(K) b^{|h|+d} dataCutoffConst(R) c^{-L}
(1+|log c|)^n`, `c = b^{2|k|}`. -/
noncomputable def chartCutoffConst (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (L R : ℝ) : ℝ :=
  (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
    ((b ^ (2 * ∑ i, k i)) ^ (-L) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n)

theorem chartCutoffConst_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {b : ℝ}
    (hb : 0 < b) (L : ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ chartCutoffConst ν n h k β b L R := by
  unfold chartCutoffConst
  have h1 := dataCutoffConst_nonneg n k β hβ L hR
  have h2 : 0 ≤ (b ^ (2 * ∑ i, k i)) ^ (-L) := Real.rpow_nonneg (by positivity) _
  have h3 := ENNReal.toReal_nonneg (a := ν univ)
  positivity

/-- **The uniform chart cutoff bound in the sample size**: for `‖x‖ ≤ R`, `N ≥ 1`,
`N b^{2|k|} ≥ 1`, `L > 0`. -/
theorem tanCutoff_bound_N (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 1 ≤ N)
    (hN' : 1 ≤ boxScale k b N) {R : ℝ} {x : TangentialData K (n + 1)} (hx : ‖x‖ ≤ R) :
    |tanIntegral ν n h k β N b x - absSpectralSum (latticeQ k) n (tanCoeff ν n h k β b x) L N| ≤
      chartCutoffConst ν n h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ n) := by
  have hN0 : 0 < N := by linarith
  have hcut := tanTaylorTree_cutoff_bound ν n h k hk β hβ hL hb hN0 hN' hx
  unfold absSpectralSum
  refine hcut.trans ?_
  unfold chartCutoffConst
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  have hbs : boxScale k b N = N * c := by unfold boxScale; rw [hc]
  have hK0 : 0 ≤ (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) :=
    mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by positivity) (dataCutoffConst_nonneg n k β hβ L ((norm_nonneg x).trans hx)))
  have h1 : boxScale k b N ^ (-L) = N ^ (-L) * c ^ (-L) := by
    rw [hbs, Real.mul_rpow hN0.le hc0.le]
  have h2 : (1 + Real.log (boxScale k b N)) ^ n ≤
      (1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n := by
    rw [hbs, ← mul_pow]
    exact pow_le_pow_left₀ (by have := Real.log_nonneg (show 1 ≤ N * c by rwa [← hbs]); linarith)
      (one_add_log_mul_le hN hc0) n
  have hr0 : 0 ≤ N ^ (-L) := Real.rpow_nonneg hN0.le _
  have hcr0 : 0 ≤ c ^ (-L) := Real.rpow_nonneg hc0.le _
  calc (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n))
      = (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by ring
    _ ≤ (ν univ).toReal * (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R) *
        (N ^ (-L) * c ^ (-L) * ((1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n)) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hcr0)) hK0
    _ = _ := by ring

/-- **Every chart integral is a finite-cutoff expansion** on the chart lattice with degrees `≤ n`,
with coefficients the integrated canonical coefficients. -/
theorem cutoffExpansion_tan (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) :
    CutoffExpansion (latticeQ k) n (fun N => tanIntegral ν n h k β N b x)
      (tanCoeff ν n h k β b x) := by
  intro L hL
  refine ⟨chartCutoffConst ν n h k β b L ‖x‖, ?_⟩
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / c)] with N hN1 hNc
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  exact tanCutoff_bound_N ν n h k hk β hβ hL hb hN1 hscale le_rfl

end Tangential

end Grammar

```
### Grammar/ChartAssemblyGlobal.lean

Ambient `variable` lines (as written in the file):
```lean
variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ}
variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
```

```lean
/-!
# Finite chart assembly of the Taylor tree (Stage S14 — deterministic)

Unit 283 (Astra #34 / review v29). Finitely many charts `I : Fin M`, each with its own normal
dimension `n I + 1`, exponents `h I, k I`, box radius `b I`, compact tangential space `K I` and
finite measure `ν I`. The **joint tangential data** is the dependent product
`JointData K n = ∀ I, C(K I, DataSpace (n I + 1))` (sup norm over charts, Borel σ-algebra; a type
synonym so that the Borel structure is the one used, not the product σ-algebra). The **global
integral** is `𝒵^{glob}(N; x) = ∑_I 𝒵^I(N; x_I)` and the **global coefficients** are
`C^{glob}_{μ,j}(x) = ∑_I 𝒞^I_{μ,j}(x_I)` on the common lattice `Q = ∏_I Q_I` with the common degree
bound `D = max_I n_I`; charts contribute zero off their own lattice and above their own degree
(support theorems of unit 282 — the padding is a theorem, not a convention).

Results: the global cutoff bound uniform on joint balls (`gCutoff_bound`), the ballwise bound on
the global coefficients (`abs_gCoeff_le`), continuity/measurability of the global functionals, and
the **uniform convergence of the global ordered normalised remainder** on joint data balls
(`tendstoUniformlyOn_gRemainder`), for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ D` — including
targets that lie on no single chart's lattice or exceed a chart's degree, handled by the abstract
estimate of unit 281 (every chart is expanded through the common cutoff `L = μ + 1`, the
predecessors are subtracted globally, and the non-target terms vanish). The paper's spectrum
`Λ^*` is a subset of the common lattice; nothing is claimed about which coefficients are nonzero
(chart contributions may cancel).
-/

structure is the one used, not the product σ-algebra). The **global
integral** is `𝒵^{glob}(N; x) = ∑_I 𝒵^I(N; x_I)` and the **global coefficients** are
`C^{glob}_{μ,j}(x) = ∑_I 𝒞^I_{μ,j}(x_I)` on the common lattice `Q = ∏_I Q_I` with the common degree
bound `D = max_I n_I`; charts contribute zero off their own lattice and above their own degree
(support theorems of unit 282 — the padding is a theorem, not a convention).

Results: the global cutoff bound uniform on joint balls (`gCutoff_bound`), the ballwise bound on
the global coefficients (`abs_gCoeff_le`), continuity/measurability of the global functionals, and
the **uniform convergence of the global ordered normalised remainder** on joint data balls
(`tendstoUniformlyOn_gRemainder`), for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ D` — including
targets that lie on no single chart's lattice or exceed a chart's degree, handled by the abstract
estimate of unit 281 (every chart is expanded through the common cutoff `L = μ + 1`, the
predecessors are subtracted globally, and the non-target terms vanish). The paper's spectrum
`Λ^*` is a subset of the common lattice; nothing is claimed about which coefficients are nonzero
(chart contributions may cancel).
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open scoped Classical

/-! ### Abstract equalities for refinement and padding -/

theorem absSpectralSum_refine_eq {Q Q' D : ℕ} (hQ : 0 < Q) (hQ' : 0 < Q') (hQQ : Q ∣ Q')
    {c : ℝ → ℕ → ℝ} (hc : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / Q) → ∀ j, c μ j = 0) (L N : ℝ) :
    absSpectralSum Q' D c L N = absSpectralSum Q D c L N := by
  unfold absSpectralSum
  symm
  refine Finset.sum_subset (latticeBelow_subset_of_dvd hQ hQ' hQQ L) fun μ hμ' hμ => ?_
  have hzero : ∀ j, c μ j = 0 := by
    refine hc μ fun m hm => hμ ?_
    exact (mem_latticeBelow_iff hQ).2 ⟨⟨m, hm⟩, lt_of_mem_latticeBelow hQ' hμ'⟩
  simp [hzero]

theorem absSpectralSum_pad_eq {Q D D' : ℕ} (hD : D ≤ D') {c : ℝ → ℕ → ℝ}
    (hc : ∀ μ j, D < j → c μ j = 0) (L N : ℝ) :
    absSpectralSum Q D' c L N = absSpectralSum Q D c L N := by
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

theorem absSpectralSum_add (Q D : ℕ) (c₁ c₂ : ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => c₁ μ j + c₂ μ j) L N =
      absSpectralSum Q D c₁ L N + absSpectralSum Q D c₂ L N := by
  unfold absSpectralSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem absSpectralSum_sum {ι : Type*} (s : Finset ι) (Q D : ℕ) (c : ι → ℝ → ℕ → ℝ) (L N : ℝ) :
    absSpectralSum Q D (fun μ j => ∑ i ∈ s, c i μ j) L N =
      ∑ i ∈ s, absSpectralSum Q D (c i) L N := by
  induction s using Finset.induction_on with

def JointData (K : Fin M → Type*) [∀ I, TopologicalSpace (K I)] (n : Fin M → ℕ) :=
  ∀ I, TangentialData (K I) (n I + 1)

noncomputable instance : NormedAddCommGroup (JointData K n) :=
  inferInstanceAs (NormedAddCommGroup (∀ I, TangentialData (K I) (n I + 1)))

noncomputable instance : MeasurableSpace (JointData K n) := borel (JointData K n)
instance : BorelSpace (JointData K n) := ⟨rfl⟩

/-- The chart component of a joint datum. -/
def JointData.chart (x : JointData K n) (I : Fin M) : TangentialData (K I) (n I + 1) := x I

theorem continuous_chart (I : Fin M) : Continuous fun x : JointData K n => x.chart I :=
  continuous_apply (A := fun I => TangentialData (K I) (n I + 1)) I

theorem norm_chart_le (x : JointData K n) (I : Fin M) : ‖x.chart I‖ ≤ ‖x‖ :=
  norm_le_pi_norm (f := (x : ∀ I, TangentialData (K I) (n I + 1))) I

theorem norm_chart_sub_le (x y : JointData K n) (I : Fin M) :
    ‖x.chart I - y.chart I‖ ≤ ‖x - y‖ :=
  norm_le_pi_norm (f := ((x - y : JointData K n) : ∀ I, TangentialData (K I) (n I + 1))) I

variable (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)

/-- The common lattice denominator `Q = ∏_I Q_I`. -/
def commonQ (k : (I : Fin M) → Fin (n I + 1) → ℕ) : ℕ := ∏ I, latticeQ (k I)

theorem commonQ_pos (hk : ∀ I i, 0 < k I i) : 0 < commonQ k :=
  Finset.prod_pos fun I _ => latticeQ_pos (k I) (hk I)

theorem latticeQ_dvd_commonQ (I : Fin M) : latticeQ (k I) ∣ commonQ k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ I)

/-- The common log-degree bound `D = max_I n_I`. -/
def commonD (n : Fin M → ℕ) : ℕ := Finset.univ.sup n

theorem le_commonD (I : Fin M) : n I ≤ commonD n := Finset.le_sup (Finset.mem_univ I)

/-- The global integral `∑_I 𝒵^I(N; x_I)`. -/
noncomputable def gInt (x : JointData K n) (N : ℝ) : ℝ :=
  ∑ I, tanIntegral (ν I) (n I) (h I) (k I) β N (b I) (x.chart I)

/-- The global coefficients `∑_I 𝒞^I_{μ,j}(x_I)`. -/
noncomputable def gCoeff (x : JointData K n) (μ : ℝ) (j : ℕ) : ℝ :=
  ∑ I, tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j

/-- The global ordered normalised remainder. -/
noncomputable def gRemainder (x : JointData K n) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  abstractRemainder (commonQ k) (commonD n) (gInt ν h k β b x) (gCoeff ν h k β b x) μ j N

theorem continuous_gCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ : ℝ)
    (j : ℕ) : Continuous fun x : JointData K n => gCoeff ν h k β b x μ j := by
  unfold gCoeff
  exact continuous_finset_sum _ fun I _ =>
    (continuous_tanCoeff (ν I) (n I) (h I) (k I) (hk I) β hβ (hb I) μ j).comp (continuous_chart I)

theorem measurable_gInt (hβ : 0 < β) (hb : ∀ I, 0 < b I) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : JointData K n => gInt ν h k β b x N := by
  unfold gInt
  exact Finset.measurable_sum _ fun I _ =>
    ((continuous_tanIntegral (ν I) (n I) (h I) (k I) hβ.le hN (hb I)).comp
      (continuous_chart I)).measurable

theorem measurable_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (μ : ℝ)
    (j : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : JointData K n => gRemainder ν h k β b x μ j N := by
  unfold gRemainder abstractRemainder absPredSum absTerm
  refine Measurable.div_const (Measurable.sub (measurable_gInt ν h k β b hβ hb hN) ?_) _
  exact Finset.measurable_sum _ fun p _ =>
    ((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).mul_const _

/-! ### The global cutoff bound, uniform on joint balls -/

/-- The global cutoff constant on the joint ball of radius `R`. -/
noncomputable def gCutoffConst (L R : ℝ) : ℝ :=
  ∑ I, chartCutoffConst (ν I) (n I) (h I) (k I) β (b I) L R

/-- **The global cutoff bound**: for `‖x‖ ≤ R`, `N ≥ 1` and `N b_I^{2|k_I|} ≥ 1` for every chart,
`|𝒵^{glob}(N;x) − ∑_{Λ^Q_L} N^{-μ} ∑_{j≤D} C^{glob}_{μ,j}(x)(log N)^j| ≤ gCutoffConst L R ·
N^{-L}(1+log N)^D`. -/
theorem gCutoff_bound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {L : ℝ}
    (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) :
    |gInt ν h k β b x N -
        absSpectralSum (commonQ k) (commonD n) (gCoeff ν h k β b x) L N| ≤
      gCutoffConst ν h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ (commonD n)) := by
  have hQ := commonQ_pos k hk
  unfold gInt gCoeff gCutoffConst
  rw [absSpectralSum_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  -- reduce the chart's sum on the common lattice/degree to its own
  have hI := hk I
  have hsupp1 : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ (k I)) → ∀ j,
      tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 := fun μ hμ j =>
    tanCoeff_eq_zero_of_not_lattice (ν I) (n I) (h I) (k I) hI β hβ (hb I) _ hμ j
  have hsupp2 : ∀ μ j, n I < j → tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 :=
    fun μ j hj => tanCoeff_eq_zero_of_lt (ν I) (n I) (h I) (k I) β (b I) _ μ hj
  rw [absSpectralSum_refine_eq (latticeQ_pos (k I) hI) hQ (latticeQ_dvd_commonQ k I) hsupp1,
    absSpectralSum_pad_eq (le_commonD I) hsupp2]
  have hchart := tanCutoff_bound_N (ν I) (n I) (h I) (k I) hI β hβ hL (hb I) hN (hN' I)
    ((norm_chart_le x I).trans hx)
  refine hchart.trans ?_
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have h1 : (1 + Real.log N) ^ (n I) ≤ (1 + Real.log N) ^ (commonD n) :=
    pow_le_pow_right₀ hlog (le_commonD I)
  have hC0 := chartCutoffConst_nonneg (ν I) (n I) (h I) (k I) β hβ (hb I) L
    ((norm_nonneg x).trans hx)
  have hr : 0 ≤ N ^ (-L) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hC0

/-! ### Bounds on the global coefficients -/

theorem abs_tanCoeff_le {K' : Type*} [TopologicalSpace K'] [CompactSpace K'] [T2Space K']
    [MeasurableSpace K'] [OpensMeasurableSpace K'] (ν' : Measure K') [IsFiniteMeasure ν'] (n' : ℕ)
    (h' k' : Fin (n' + 1) → ℕ) (hk' : ∀ i, 0 < k' i) (hβ : 0 < β) {b' : ℝ} (hb' : 0 < b')
    {R : ℝ} {x : TangentialData K' (n' + 1)} (hx : ‖x‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |tanCoeff ν' n' h' k' β b' x μ j| ≤ (ν' univ).toReal * coeffBallBound n' h' k' β b' μ j R := by
  unfold tanCoeff
  have hbound : ∀ v,
      ‖dataBoxCoeff n' h' k' β b' (x v) μ j‖ ≤ coeffBallBound n' h' k' β b' μ j R := by
    intro v
    rw [Real.norm_eq_abs]
    exact abs_dataBoxCoeff_le_ballBound n' h' k' hk' β hβ hb' μ j ((norm_tan_apply_le x v).trans hx)
  have := norm_integral_le_of_norm_le_const (μ := ν') (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [measureReal_def]; ring

/-- The ballwise bound on a global coefficient. -/
noncomputable def gCoeffBound (R μ : ℝ) (j : ℕ) : ℝ :=
  ∑ I, ((ν I) univ).toReal * coeffBallBound (n I) (h I) (k I) β (b I) μ j R

theorem abs_gCoeff_le (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |gCoeff ν h k β b x μ j| ≤ gCoeffBound ν h k β b R μ j := by
  unfold gCoeff gCoeffBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  exact abs_tanCoeff_le β (ν I) (n I) (h I) (k I) (hk I) hβ (hb I) ((norm_chart_le x I).trans hx)
    μ j

/-- The uniform bound on all global coefficients of the index set below `μ + 1`. -/
noncomputable def gIndexBound (R μ : ℝ) : ℝ :=
  ∑ p ∈ indexSet (commonD n) (commonQ k) (μ + 1), gCoeffBound ν h k β b R p.1 p.2

theorem gCoeffBound_nonneg (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    (hR : 0 ≤ R) (μ : ℝ) (j : ℕ) : 0 ≤ gCoeffBound ν h k β b R μ j := by
  have h0 : ‖(0 : JointData K n)‖ ≤ R := by simpa using hR
  exact (abs_nonneg _).trans (abs_gCoeff_le ν h k β b hk hβ hb h0 μ j)

theorem abs_gCoeff_le_indexBound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {R : ℝ}
    (hR : 0 ≤ R) {x : JointData K n} (hx : ‖x‖ ≤ R) {μ : ℝ} {p : ℝ × ℕ}
    (hp : p ∈ indexSet (commonD n) (commonQ k) (μ + 1)) :
    |gCoeff ν h k β b x p.1 p.2| ≤ gIndexBound ν h k β b R μ :=
  (abs_gCoeff_le ν h k β b hk hβ hb hx p.1 p.2).trans
    (Finset.single_le_sum (fun q _ => gCoeffBound_nonneg ν h k β b hk hβ hb hR q.1 q.2) hp)

/-! ### The global ordered remainder, uniformly on joint balls -/

/-- **The global majorant estimate**: for `‖x‖ ≤ R`, `N ≥ e`, `N b_I^{2|k_I|} ≥ 1` for all charts,
`|R^{glob}_N(x) − C^{glob}_{μ,j}(x)| ≤ gCutoffConst(μ+1, R)·N^{-(μ+1)}(1+log N)^D/N^{-μ} +
gIndexBound(R, μ)·∑_{rest} termMajorant`. -/
theorem abs_gRemainder_sub_le (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) {N : ℝ} (hNe : Real.exp 1 ≤ N)
    (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) :
    |gRemainder ν h k β b x μ j N - gCoeff ν h k β b x μ j| ≤
      gCutoffConst ν h k β b (μ + 1) R *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ (commonD n) / N ^ (-μ)) +
        gIndexBound ν h k β b R μ *
          ∑ p ∈ restSet (commonD n) (commonQ k) μ j, termMajorant (commonD n) μ p N := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have hN1 : 1 ≤ N := le_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hNe
  have hμ0 : 0 ≤ μ := by obtain ⟨m, hm⟩ := hμ; rw [hm]; positivity
  exact abs_abstractRemainder_sub_le (commonQ_pos k hk) hμ hj hNe
    (gCutoff_bound ν h k β b hk hβ hb (by linarith) hN1 hN' hx)
    fun p hp => abs_gCoeff_le_indexBound ν h k β b hk hβ hb hR0 hx hp

/-- **Global ordered normalised remainders converge uniformly on joint data balls.** -/
theorem tendstoUniformlyOn_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => gRemainder ν h k β b x μ j N)
      (fun x => gCoeff ν h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := tendsto_abstract_majorant (commonQ k) (commonD n) μ j
    (gCutoffConst ν h k β b (μ + 1) R) (gIndexBound ν h k β b R μ)
  have hev := hmaj.eventually (gt_mem_nhds hε)
  have hthr : ∀ᶠ N : ℝ in atTop, ∀ I, 1 ≤ boxScale (k I) (b I) N := by
    rw [Filter.eventually_all]
    intro I
    have hc0 : 0 < (b I) ^ (2 * ∑ i, k I i) := by have := hb I; positivity
    filter_upwards [eventually_ge_atTop (1 / (b I) ^ (2 * ∑ i, k I i))] with N hN
    unfold boxScale
    rwa [div_le_iff₀ hc0] at hN
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), hthr] with N hNε hNe hN' x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (abs_gRemainder_sub_le ν h k β b hk hβ hb hμ hj hx' hNe hN') hNε

end Grammar

```
### Grammar/StochasticAssembly.lean

Ambient `variable` lines (as written in the file):
```lean
variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {l : Filter ι}
variable [l.IsCountablyGenerated]
```

```lean
/-!
# The stochastic Taylor tree after finite chart assembly (Stage S15 — Headline XXXVII)

Unit 284 (Astra #34, tranche A3). Let `X_ℓ : Ω → JointData K n` be measurable random joint
tangential Taylor data of finitely many charts converging in distribution to `X`, let
`N_ℓ → ∞` (`N_ℓ ≥ 0`), and let the **external chart decomposition** hold: the global normalised
partition function `Z^0_ℓ` equals `∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` with a residual `E_ℓ` that is
`o_p(N_ℓ^{-μ}(log N_ℓ)^j)` at the target. Then for every target `(μ, j)` with `μ` on the common
lattice `Q⁻¹ℕ` and `j ≤ D`:

* the global coefficients converge in distribution, `C^{glob}_{μ,j}(X_ℓ) ⇒ C^{glob}_{μ,j}(X)`
  (`tendstoInDistribution_gCoeff`; joint finite vectors likewise);
* the global ordered normalised remainder of the assembled integral converges in distribution
  to the limiting global coefficient (`tendstoInDistribution_gRemainder`), and so does the ordered
  normalised remainder of `Z^0_ℓ` itself (`tendstoInDistribution_assembled`, **Headline XXXVII**):
  `(Z^0_ℓ − ∑_{(ν,q) ≺ (μ,j)} C^{glob}_{ν,q}(X_ℓ) N_ℓ^{-ν}(log N_ℓ)^q) / (N_ℓ^{-μ}(log N_ℓ)^j)`
  `  ⇒ C^{glob}_{μ,j}(X)`.

This is the convergence-in-distribution clause of `thm:strataempiricalexpansion` assembled over
finitely many charts in arbitrary normal dimensions, conditional on (i) joint convergence in
distribution of the chart data in `∏_I C(K_I, E_{b_I} × E_{b_I})`, and (ii) the external
decomposition with a residual negligible at the target scale. Non-claims: (i) and (ii) are not
derived (the resolution, the partition of unity, the away-from-minimum contribution, the
empirical-process convergence and the standard-form identity are external inputs); the common
lattice is an indexing superset of the paper's `Λ^*` (coefficients may cancel across charts); no
Gaussianity; `N_ℓ` deterministic.
-/

/-- **Global coefficients converge in distribution** when the joint chart data do. -/
theorem tendstoInDistribution_gCoeff (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    (μ₀ : ℝ) (j : ℕ) (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => gCoeff ν h k β b (X i ω) μ₀ j) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  hX.continuous_comp (g := fun x => gCoeff ν h k β b x μ₀ j)
    (continuous_gCoeff ν h k β b hk hβ hb μ₀ j)

/-- A finite vector of global coefficients. -/
noncomputable def gCoeffVec {m : ℕ} (F : Fin m → ℝ × ℕ) (x : JointData K n) : Fin m → ℝ :=
  fun i => gCoeff ν h k β b x (F i).1 (F i).2

theorem tendstoInDistribution_gCoeffVec (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {m : ℕ} (F : Fin m → ℝ × ℕ) (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i => gCoeffVec ν h k β b F ∘ X i) l (gCoeffVec ν h k β b F ∘ Z)
      (fun _ => μ) μ' :=
  hX.continuous_comp (continuous_pi fun i => continuous_gCoeff ν h k β b hk hβ hb (F i).1 (F i).2)

/-- The global remainder minus the global coefficient tends to zero in probability. -/
theorem tendstoInMeasure_gRemainder_sub (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i) -
      gCoeff ν h k β b (X i ω) μ₀ j) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun R hR ε hε => ?_)
    (normBounded_of_tendstoInDistribution' X Z hX)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_gRemainder ν h k β b hk hβ hb hμ hj R) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have := hi (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  simpa [Real.norm_eq_abs] using this.le

variable [l.IsCountablyGenerated]

/-- **The assembled ordered remainder converges in distribution** to the limiting global
coefficient. -/
theorem tendstoInDistribution_gRemainder (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_gCoeff ν h k β b hk hβ hb μ₀ j X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_gRemainder ν h k β b hk hβ hb μ₀ j (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_gRemainder_sub ν h k β b hk hβ hb hμ hj X Z hX Nseq hN

/-- **Headline XXXVII — the stochastic Taylor tree after finite chart assembly.** Under the
external decomposition `Z^0_ℓ = ∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` with the residual `E_ℓ` negligible in
probability at the target scale `N_ℓ^{-μ}(log N_ℓ)^j`, the ordered normalised remainder of `Z^0_ℓ`
converges in distribution to the limiting global coefficient `C^{glob}_{μ,j}(X)`. -/
theorem tendstoInDistribution_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ) (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun _ => 0)) :
    TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hR := tendstoInDistribution_gRemainder ν h k β b hk hβ hb hμ hj X hXm Z hX Nseq hN0 hN
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hR ?_ fun i => ?_
  · -- the difference is the normalised residual
    have heq : (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) -
        (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i)) =
        fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j) := by
      funext i ω
      simp only [Pi.sub_apply]
      unfold gRemainder abstractRemainder
      rw [hdecomp i ω]
      ring
    rw [heq]; exact hE
  · -- measurability of the normalised remainder of `Z^0`
    refine Measurable.aemeasurable (Measurable.div_const (Measurable.sub (hZm i) ?_) _)
    unfold absPredSum absTerm
    exact Finset.measurable_sum _ fun p _ =>
      (((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).comp (hXm i)).mul_const _

end Grammar

```


## Full proof of the global cutoff bound (unit 283)

```lean
/-- **The global cutoff bound**: for `‖x‖ ≤ R`, `N ≥ 1` and `N b_I^{2|k_I|} ≥ 1` for every chart,
`|𝒵^{glob}(N;x) − ∑_{Λ^Q_L} N^{-μ} ∑_{j≤D} C^{glob}_{μ,j}(x)(log N)^j| ≤ gCutoffConst L R ·
N^{-L}(1+log N)^D`. -/
theorem gCutoff_bound (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {L : ℝ}
    (hL : 0 < L) {N : ℝ} (hN : 1 ≤ N) (hN' : ∀ I, 1 ≤ boxScale (k I) (b I) N) {R : ℝ}
    {x : JointData K n} (hx : ‖x‖ ≤ R) :
    |gInt ν h k β b x N -
        absSpectralSum (commonQ k) (commonD n) (gCoeff ν h k β b x) L N| ≤
      gCutoffConst ν h k β b L R * (N ^ (-L) * (1 + Real.log N) ^ (commonD n)) := by
  have hQ := commonQ_pos k hk
  unfold gInt gCoeff gCutoffConst
  rw [absSpectralSum_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  -- reduce the chart's sum on the common lattice/degree to its own
  have hI := hk I
  have hsupp1 : ∀ μ, (∀ m : ℕ, μ ≠ (m : ℝ) / latticeQ (k I)) → ∀ j,
      tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 := fun μ hμ j =>
    tanCoeff_eq_zero_of_not_lattice (ν I) (n I) (h I) (k I) hI β hβ (hb I) _ hμ j
  have hsupp2 : ∀ μ j, n I < j → tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j = 0 :=
    fun μ j hj => tanCoeff_eq_zero_of_lt (ν I) (n I) (h I) (k I) β (b I) _ μ hj
  rw [absSpectralSum_refine_eq (latticeQ_pos (k I) hI) hQ (latticeQ_dvd_commonQ k I) hsupp1,
    absSpectralSum_pad_eq (le_commonD I) hsupp2]
  have hchart := tanCutoff_bound_N (ν I) (n I) (h I) (k I) hI β hβ hL (hb I) hN (hN' I)
    ((norm_chart_le x I).trans hx)
  refine hchart.trans ?_
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have h1 : (1 + Real.log N) ^ (n I) ≤ (1 + Real.log N) ^ (commonD n) :=
    pow_le_pow_right₀ hlog (le_commonD I)
  have hC0 := chartCutoffConst_nonneg (ν I) (n I) (h I) (k I) β hβ (hb I) L
    ((norm_nonneg x).trans hx)
  have hr : 0 ≤ N ^ (-L) := Real.rpow_nonneg (by linarith) _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hC0


```

## Full proof of Headline XXXVII (unit 284)

```lean
/-- **Headline XXXVII — the stochastic Taylor tree after finite chart assembly.** Under the
external decomposition `Z^0_ℓ = ∑_I 𝒵^I(N_ℓ; X_{ℓ,I}) + E_ℓ` with the residual `E_ℓ` negligible in
probability at the target scale `N_ℓ^{-μ}(log N_ℓ)^j`, the ordered normalised remainder of `Z^0_ℓ`
converges in distribution to the limiting global coefficient `C^{glob}_{μ,j}(X)`. -/
theorem tendstoInDistribution_assembled (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I)
    {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (X : ι → Ω → JointData K n) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → JointData K n)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) (Zg E : ι → Ω → ℝ) (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (X i ω) (Nseq i) + E i ω)
    (hE : TendstoInMeasure μ (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun _ => 0)) :
    TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) l
      (fun ω => gCoeff ν h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hR := tendstoInDistribution_gRemainder ν h k β b hk hβ hb hμ hj X hXm Z hX Nseq hN0 hN
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hR ?_ fun i => ?_
  · -- the difference is the normalised residual
    have heq : (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b (X i ω)) μ₀ j (Nseq i)) /
          (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) -
        (fun i ω => gRemainder ν h k β b (X i ω) μ₀ j (Nseq i)) =
        fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j) := by
      funext i ω
      simp only [Pi.sub_apply]
      unfold gRemainder abstractRemainder
      rw [hdecomp i ω]
      ring
    rw [heq]; exact hE
  · -- measurability of the normalised remainder of `Z^0`
    refine Measurable.aemeasurable (Measurable.div_const (Measurable.sub (hZm i) ?_) _)
    unfold absPredSum absTerm
    exact Finset.measurable_sum _ fun p _ =>
      (((continuous_gCoeff ν h k β b hk hβ hb p.1 p.2).measurable).comp (hXm i)).mul_const _

end Grammar

```

## Questions
1. **u281 (abstract expansions).** Is `CutoffExpansion Q D Z c` the right abstraction (eventual bound `K N^{-L}(1+log N)^D` for every `L > 0`)? Check `add`/`sum`, `refine` (`Q ∣ Q'`, `Q' > 0`, coefficients supported on `Q⁻¹ℕ`), `pad`, and the abstract quantitative estimate `abs_abstractRemainder_sub_le` (hypotheses: cutoff bound at `L = μ+1` at the given `N`, `|c| ≤ C` on `indexSet D Q (μ+1)`, `N ≥ e`, `μ ∈ Q⁻¹ℕ`, `j ≤ D`).
2. **u282–283 (assembly).** Are the support theorems (`dataBoxCoeff = 0` for `j > n`, for `μ ∉ Λ(h,k)`, for `μ ∉ Q_I⁻¹ℕ`) the right padding justification? Is the common lattice `Q = ∏_I Q_I` (each `Q_I ∣ Q`), the degree `D = max n_I`, and the global coefficient `∑_I 𝒞^I_{μ,j}` correct? In `gCutoff_bound`, each chart's sum on the common lattice/degree is rewritten to its own by `absSpectralSum_refine_eq`/`_pad_eq` — is this the correct handling of "targets off a chart's lattice / above its degree"? Is the joint data type `JointData K n = ∀ I, C(K_I, DataSpace (n_I+1))` with sup norm and BOREL σ-algebra (a `def` synonym, so the Borel structure is used rather than the product σ-algebra) sound for the probability statements (continuous maps are measurable; evaluation `x ↦ x_I` continuous)? Does `tendstoUniformlyOn_gRemainder` handle global targets correctly (all charts expanded through `L = μ+1`, thresholds `N ≥ e` and `N b_I^{2|k_I|} ≥ 1` for all `I`, coefficient bound `gIndexBound`)?
3. **u284 (Headline XXXVII).** Is the external decomposition hypothesis `hdecomp : ∀ i ω, Zg i ω = gInt (X i ω) (Nseq i) + E i ω` with `hE : E_ℓ/(N_ℓ^{-μ}(log N_ℓ)^j) → 0` in probability (`TendstoInMeasure … 0`) the right formal shape, and is the conclusion `(Zg − absPredSum (gCoeff (X_ℓ)) μ j N_ℓ)/(N_ℓ^{-μ}(log N_ℓ)^j) ⇒ C^{glob}_{μ,j}(X)` a faithful rendering of the paper's convergence-in-distribution clause for `Z^0_n` assembled over strata? (The predecessor sum uses the GLOBAL coefficients of the data `X_ℓ`, as in the paper's `∑_{(μ,m)<(μ',m')} C_{μ,m}(ξ_n) n^{-μ}(log n)^{m-1}`.) Is the a.e./everywhere decomposition a reasonable hypothesis form (the paper: `Z^0_n = ∑_I Z_n[β;ξ_n,η;I] + R_n`, `R_n = o_p(e^{-ε'n})`), and should we add the lemma "exponentially small in probability ⇒ negligible at every target scale"?
4. **Non-claims** for XXXVII (what remains external: resolution atlas, partition of unity and its absorption into amplitudes, the away-from-minimum contribution, empirical-process convergence in the function space, Gaussian identification, `Λ^*` vs common lattice, cancellations).
5. Verdict per unit, overall, should-fix (blocking / nonblocking) before freezing tranche A3.
