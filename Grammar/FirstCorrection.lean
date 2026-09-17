/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalGeneral
import Grammar.EmpiricalOneDim
import Grammar.EmpiricalLeadingConsistency
import Grammar.FirstNonzeroAsymptotic
import Grammar.SmoothLogIntegrable
import Grammar.PopulationDerivative
import Grammar.GaussianQuartetDet

/-!
# The first correction of the empirical integral in the generic case

For the empirical integral `Z_N = ∫_{[0,1]^{n+1}} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv` with a
single resonant coordinate `i₀` whose first two exponents `λ = (h₀+1)/2k₀` and
`μ₁ = λ + 1/(2k₀)` both lie strictly below every other ratio `(h_l+1)/2k_l`, the two leading
coefficients of the canonical cutoff expansion are **readable face integrals**: writing
`w` for the complementary coordinates, `η_w(u) = η(u, w)`, `ζ_w(u) = ζ(u, w)` and
`p(w) = w^{2k_L}`,
```
c(λ, 0)  = ∫_{[0,1]^n} w^{h_L} p(w)^{−λ}  · η_w(0) S_λ(ζ_w(0)) / (2k₀) dw
c(μ₁, 0) = ∫_{[0,1]^n} w^{h_L} p(w)^{−μ₁} · [∂_{i₀}η(0,w) S_{μ₁}(ζ(0,w))
                                            + η(0,w) ∂_{i₀}ζ(0,w) S_{μ₁+1/2}(ζ(0,w))] / (2k₀) dw,
```
there are no logarithms at `λ` or `μ₁`, and every coefficient at a lattice exponent `< μ₁` other
than `c(λ,0)` vanishes (`empCoeff_generic`, `empCoeff_firstCorrection`, `empCoeff_leading_generic`).

The route: Fubini along `i₀` (`empIntegral_eq_slice`) writes `Z_N` as the `w`-integral of the
one-dimensional integral at the effective sample size `T = N p(w)`; the one-dimensional expansion
with an explicit constant (`empOneDim_expansion_of_bounds`) is uniform in `w` because the jets of
the slices are restrictions of smooth functions (`exists_jetCoeff_slice`), which gives a bounded
two-term remainder `B(T, w) = T^{μ₁}(I(T,w) − a₀(w) T^{−λ})` converging to `a₁(w)`; dominated
convergence with the integrable weight `w^{h_L} p(w)^{−μ₁}` (the gap hypothesis) yields
★★ `tendsto_firstCorrection`; finally the abstract reading-off lemma
★ `CutoffExpansion.coeff_eq_of_twoTerm` (from the first-nonzero theory) identifies the
coefficients. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics
open scoped ContDiff

namespace Grammar

/-! ### Reading off a two-term asymptotic from a cutoff expansion -/

/-- A single power `A N^{−λ}` at a lattice point has the obvious cutoff expansion. -/
theorem cutoffExpansion_single {Q D : ℕ} (hQ : 0 < Q) {lam : ℝ}
    (hlam : ∃ m : ℕ, lam = (m : ℝ) / Q) (A : ℝ) :
    CutoffExpansion Q D (fun N => A * N ^ (-lam))
      (fun μ j => if μ = lam ∧ j = 0 then A else 0) := by
  intro L hL
  by_cases hLl : L ≤ lam
  · refine ⟨|A|, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsum : absSpectralSum Q D (fun μ j => if μ = lam ∧ j = 0 then A else 0) L N = 0 := by
      unfold absSpectralSum
      refine Finset.sum_eq_zero fun μ hμ => ?_
      have hμL : μ < L := ((mem_latticeBelow_iff hQ).1 hμ).2
      have hne : μ ≠ lam := by intro h; rw [h] at hμL; linarith
      simp [hne]
    rw [hsum, sub_zero, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    have h1 : N ^ (-lam) ≤ N ^ (-L) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have h2 : (1 : ℝ) ≤ (1 + Real.log N) ^ D := one_le_pow₀ (by linarith [Real.log_nonneg hN])
    calc |A| * N ^ (-lam) ≤ |A| * N ^ (-L) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |A| * (N ^ (-L) * 1) := by ring
      _ ≤ |A| * (N ^ (-L) * (1 + Real.log N) ^ D) := by gcongr
  · rw [not_le] at hLl
    refine ⟨0, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N _
    have hmem : lam ∈ latticeBelow Q L := (mem_latticeBelow_iff hQ).2 ⟨hlam, hLl⟩
    have hsum : absSpectralSum Q D (fun μ j => if μ = lam ∧ j = 0 then A else 0) L N =
        A * N ^ (-lam) := by
      unfold absSpectralSum
      rw [Finset.sum_eq_single lam]
      · rw [Finset.sum_eq_single 0]
        · simp [mul_comm]
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos D)) h
      · intro μ _ hμ
        have : ∀ j, (if μ = lam ∧ j = 0 then A else 0) = 0 := fun j => by simp [hμ]
        simp [this]
      · intro h; exact absurd hmem h
    rw [hsum, sub_self, abs_zero, zero_mul]

/-- **Vanishing below the little-o scale**: if `N^{μ₁} Z(N) → 0` then every coefficient of a
cutoff expansion of `Z` at a lattice exponent `μ ≤ μ₁` vanishes (via the first-nonzero
asymptotic equivalence). -/
theorem CutoffExpansion.coeff_eq_zero_of_tendsto_zero {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {μ₁ : ℝ}
    (hZ : Tendsto (fun N => N ^ μ₁ * Z N) atTop (𝓝 0)) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q)
    (hμμ₁ : μ ≤ μ₁) {j : ℕ} (hj : j ≤ D) : c μ j = 0 := by
  by_contra hc
  have hmem : (μ, j) ∈ indexSet D Q (μ + 1) := by
    obtain ⟨m, hm⟩ := hμ
    refine mem_indexSet_iff.2 ⟨?_, Nat.lt_succ_of_le hj⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; linarith)
  obtain ⟨p, hp, hcp, hfirst⟩ := exists_first_nonzero hQ c ⟨(μ, j), hmem, hc⟩
  have hpμ : p.1 ≤ μ := by
    have hadm : (μ, j) ∈ admissible D Q := ⟨hμ, hj⟩
    by_cases hpe : p = (μ, j)
    · rw [hpe]
    · rcases precedes_or_precedes_of_ne hpe with hlt | hlt
      · rcases hlt with h1 | ⟨h1, _⟩
        · exact h1.le
        · exact h1.le
      · exact absurd (hfirst _ hadm hlt) hc
  have hequiv := isEquivalent_first_nonzero_of_cutoffExpansion hQ h hp hcp hfirst
  obtain ⟨φ, hφ, hZφ⟩ := hequiv.exists_eq_mul
  have hφne : ∀ᶠ N in atTop, φ N ≠ 0 := hφ.eventually_ne one_ne_zero
  have hg : Tendsto (fun N => c p.1 p.2 * (N ^ (μ₁ - p.1) * Real.log N ^ p.2)) atTop (𝓝 0) := by
    have := hZ.div hφ one_ne_zero
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hZφ, hφne, eventually_gt_atTop 1] with N hN hφN hN1
    have hN0 : 0 < N := by linarith
    have := (Real.rpow_pos_of_pos hN0 p.1).ne'
    simp only [Pi.div_apply]
    rw [hN, Pi.mul_apply, Real.rpow_sub hN0, Real.rpow_neg hN0.le]
    field_simp
  have hge : ∀ᶠ N in atTop,
      |c p.1 p.2| ≤ |c p.1 p.2 * (N ^ (μ₁ - p.1) * Real.log N ^ p.2)| := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
    have hN1 : 1 ≤ N := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hlog : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
    have h1 : 1 ≤ N ^ (μ₁ - p.1) := Real.one_le_rpow hN1 (by linarith)
    have h2 : 1 ≤ Real.log N ^ p.2 := one_le_pow₀ hlog
    have hpos : 0 < N ^ (μ₁ - p.1) * Real.log N ^ p.2 :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos (by linarith) _)
    rw [abs_mul, abs_of_pos hpos]
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_mul_of_one_le_of_one_le h1 h2)
  have hlt := hg.eventually (Metric.ball_mem_nhds (0 : ℝ) (abs_pos.2 hcp))
  obtain ⟨N, hN1, hN2⟩ := (hge.and hlt).exists
  rw [Real.dist_eq, sub_zero] at hN2
  linarith

/-- ★ **Reading off a two-term asymptotic**: if `Z` has a cutoff expansion and
`N^{μ₁}(Z(N) − A N^{−λ}) → B` for lattice points `λ < μ₁`, then `c(λ,0) = A`, `c(μ₁,0) = B` and
every other coefficient at a lattice exponent `μ ≤ μ₁` vanishes. -/
theorem CutoffExpansion.coeff_eq_of_twoTerm {Q D : ℕ} (hQ : 0 < Q) {Z : ℝ → ℝ}
    {c : ℝ → ℕ → ℝ} (h : CutoffExpansion Q D Z c) {lam μ₁ A B : ℝ}
    (hlam : ∃ m : ℕ, lam = (m : ℝ) / Q) (hμ₁ : ∃ m : ℕ, μ₁ = (m : ℝ) / Q)
    (hlim : Tendsto (fun N => N ^ μ₁ * (Z N - A * N ^ (-lam))) atTop (𝓝 B))
    {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Q) (hμμ₁ : μ ≤ μ₁) {j : ℕ} (hj : j ≤ D) :
    c μ j = (if μ = lam ∧ j = 0 then A else 0) + (if μ = μ₁ ∧ j = 0 then B else 0) := by
  have h' := (h.sub (cutoffExpansion_single hQ hlam A)).sub (cutoffExpansion_single hQ hμ₁ B)
  have hZ' : Tendsto (fun N => N ^ μ₁ * ((Z N - A * N ^ (-lam)) - B * N ^ (-μ₁))) atTop
      (𝓝 0) := by
    have h2 : Tendsto (fun N : ℝ => N ^ μ₁ * (B * N ^ (-μ₁))) atTop (𝓝 B) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have := (Real.rpow_pos_of_pos hN μ₁).ne'
      rw [Real.rpow_neg hN.le]; field_simp
    have := hlim.sub h2
    rw [sub_self] at this
    refine this.congr' (Eventually.of_forall fun N => ?_)
    ring
  have := h'.coeff_eq_zero_of_tendsto_zero hQ hZ' hμ hμμ₁ hj
  linarith

namespace SmoothEngine

/-! ### The jet form of the one-dimensional coefficients -/

section OneDim

variable {η ξ : ℝ → ℝ}

/-- The fluctuation-jet integral is a finite sum of fluctuation functions on the ladder:
`∫ s^{μ−1} e^{−s} P_j(v,√s) e^{√s ξ(v)} ds = ∑_r p_{j,r}(v) S_{μ+r/2}(ξ(v))`. -/
theorem fluctJet_eq_sum {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (v : ℝ) :
    fluctJet η ξ μ j v =
      ∑ r ∈ Finset.range (j + 1), jetCoeff η ξ j r v * fluctuation 1 (μ + r / 2) (ξ v) := by
  unfold fluctJet
  have hint : ∀ r ∈ Finset.range (j + 1), IntegrableOn
      (fun s => jetCoeff η ξ j r v * fluctIntegrandFn 1 (μ + r / 2) (ξ v) s) (Ioi 0) :=
    fun r _ => (integrableOn_fluctIntegrandFn one_pos (by positivity) (ξ v)).const_mul _
  calc ∫ s in Ioi (0 : ℝ), s ^ (μ - 1) * exp (-s) *
        (jetPoly η ξ j v (Real.sqrt s) * exp (Real.sqrt s * ξ v))
      = ∫ s in Ioi (0 : ℝ), ∑ r ∈ Finset.range (j + 1),
          jetCoeff η ξ j r v * fluctIntegrandFn 1 (μ + r / 2) (ξ v) s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        have hs0 : 0 < s := hs
        simp only [jetPoly, Finset.sum_mul, Finset.mul_sum, fluctIntegrandFn]
        refine Finset.sum_congr rfl fun r _ => ?_
        have h1 : Real.sqrt s ^ r = s ^ ((r : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
          congr 1; ring
        have h2 : s ^ (μ - 1) * s ^ ((r : ℝ) / 2) = s ^ (μ + r / 2 - 1) := by
          rw [← Real.rpow_add hs0]; congr 1; ring
        rw [h1, ← h2, show -1 * s + 1 * ξ v * Real.sqrt s = -s + Real.sqrt s * ξ v by ring,
          Real.exp_add]
        ring
    _ = ∑ r ∈ Finset.range (j + 1),
          ∫ s in Ioi (0 : ℝ), jetCoeff η ξ j r v * fluctIntegrandFn 1 (μ + r / 2) (ξ v) s :=
        integral_finsetSum _ hint
    _ = _ := Finset.sum_congr rfl fun r _ => by rw [integral_const_mul]; rfl

/-- The one-dimensional coefficients in jet form:
`C_j = ∑_{r ≤ j} p_{j,r}(0) S_{μ_j + r/2}(ξ(0)) / (j! · 2k)`. -/
theorem empOneDimCoeff_eq_sum (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) (j : ℕ) :
    empOneDimCoeff η ξ h k j = (∑ r ∈ Finset.range (j + 1),
      jetCoeff η ξ j r 0 * fluctuation 1 (lam k (j + h) + r / 2) (ξ 0)) /
        ((j.factorial : ℝ) * (2 * k)) := by
  unfold empOneDimCoeff
  rw [iteratedDeriv_mul_fluctuation hη hξ (lam_pos hk _) j, fluctJet_eq_sum (lam_pos hk _) j 0]

/-! ### The two-term remainder of the one-dimensional integral -/

/-- The cutoff order used for the two-term estimate: the first integer above `μ₁`. -/
noncomputable def firstL (h k : ℕ) : ℕ := ⌊lam k (1 + h)⌋₊ + 1

/-- The number of retained terms, `q = 2k · firstL`. -/
noncomputable def firstQ (h k : ℕ) : ℕ := 2 * k * firstL h k

theorem lam_lt_firstL (h k : ℕ) : lam k (1 + h) < (firstL h k : ℕ) := by
  unfold firstL
  push_cast
  exact Nat.lt_floor_add_one _

theorem two_le_firstQ (h : ℕ) {k : ℕ} (hk : 0 < k) : 2 ≤ firstQ h k := by
  unfold firstQ firstL
  nlinarith [hk]

theorem lam_lt_lam_succ (h : ℕ) {k : ℕ} (hk : 0 < k) : lam k h < lam k (1 + h) := by
  unfold lam
  push_cast
  have : (0 : ℝ) < 2 * k := by positivity
  rw [div_lt_div_iff_of_pos_right this]
  linarith

theorem lam_le_lam_of_le {k : ℕ} (hk : 0 < k) {e e' : ℕ} (he : e ≤ e') : lam k e ≤ lam k e' := by
  unfold lam
  have : (0 : ℝ) < 2 * k := by positivity
  rw [div_le_div_iff_of_pos_right this]
  exact_mod_cast Nat.add_le_add_right he 1

/-- The two-term normalised remainder `B(T) = T^{μ₁}(I(T) − C_0 T^{−λ})` of the one-dimensional
integral on `[0,1]`. -/
noncomputable def twoTermRem (η ξ : ℝ → ℝ) (h k : ℕ) (T : ℝ) : ℝ :=
  T ^ lam k (1 + h) * (empOneDim η ξ h k 1 T - empOneDimCoeff η ξ h k 0 * T ^ (-lam k h))

theorem oneDimExpConst_nonneg (h k q L : ℕ) {b M : ℝ} (hb : 0 < b) {Cj : ℕ → ℝ}
    (hCj : ∀ j, 0 ≤ Cj j) : 0 ≤ oneDimExpConst h k q L b M Cj := by
  unfold oneDimExpConst
  have h1 : 0 ≤ ∑ j ∈ Finset.range (q + 1),
      2 * Cj j * kernelConst (h + 2 * j) M / (j.factorial : ℝ) :=
    Finset.sum_nonneg fun j _ => by
      have := hCj j; have := kernelConst_nonneg (h + 2 * j) M; positivity
  have h2 : 0 ≤ ∫ x in Ioi (0 : ℝ), exp (-x ^ (2 * k) / 2) :=
    setIntegral_nonneg measurableSet_Ioi fun x _ => (exp_pos _).le
  have := hCj (q + 1)
  have := kernelConst_nonneg (h + 2 * q + 2) M
  positivity

/-- **The two-term estimate for `T ≥ 1`**: with `q = firstQ`, `L = firstL`,
`|B(T) − C_1 − ∑_{2 ≤ j ≤ q} C_j T^{−(μ_j−μ₁)}| ≤ oneDimExpConst · T^{−(L−μ₁)}`. -/
theorem twoTermRem_sub_le (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) {M : ℝ} (hM' : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ≤ M) {Cj : ℕ → ℝ}
    (hCj : ∀ j, 0 ≤ Cj j ∧ ∀ v ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 0 ≤ τ →
      |jetPoly η ξ j v τ| ≤ Cj j * (1 + τ) ^ j) {T : ℝ} (hT : 1 ≤ T) :
    |twoTermRem η ξ h k T - empOneDimCoeff η ξ h k 1 -
        ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
          empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h)))| ≤
      oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj *
        T ^ (-((firstL h k : ℝ) - lam k (1 + h))) := by
  have hT0 : 0 < T := by linarith
  have hqL : 2 * k * firstL h k ≤ firstQ h k + 1 + h := by unfold firstQ; omega
  have hX : 1 ≤ 1 * T ^ (1 / (2 * (k : ℝ))) := by
    rw [one_mul]; exact Real.one_le_rpow hT (by positivity)
  have key := empOneDim_expansion_of_bounds hη hξ h hk one_pos (firstQ h k) (firstL h k) hqL hM'
    hCj hT hX
  set A := empOneDimCoeff η ξ h k with hA
  set μ₁ := lam k (1 + h) with hμ₁
  have h2q : 2 ≤ firstQ h k + 1 := by have := two_le_firstQ h hk; omega
  have hsplit : ∑ j ∈ Finset.range (firstQ h k + 1), A j * T ^ (-lam k (j + h)) =
      A 0 * T ^ (-lam k h) + A 1 * T ^ (-μ₁) +
        ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), A j * T ^ (-lam k (j + h)) := by
    rw [← Finset.sum_range_add_sum_Ico _ h2q, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [zero_add, hμ₁]
  have h1 : T ^ μ₁ * (A 1 * T ^ (-μ₁)) = A 1 := by
    have := (Real.rpow_pos_of_pos hT0 μ₁).ne'
    rw [Real.rpow_neg hT0.le]; field_simp
  have h2 : ∀ j, T ^ μ₁ * (A j * T ^ (-lam k (j + h))) = A j * T ^ (-(lam k (j + h) - μ₁)) :=
    fun j => by
      rw [neg_sub, Real.rpow_sub hT0, Real.rpow_neg hT0.le]; ring
  have hid : twoTermRem η ξ h k T - A 1 -
      ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), A j * T ^ (-(lam k (j + h) - μ₁)) =
      T ^ μ₁ * (empOneDim η ξ h k 1 T -
        ∑ j ∈ Finset.range (firstQ h k + 1), A j * T ^ (-lam k (j + h))) := by
    rw [hsplit]
    unfold twoTermRem
    rw [← hA, ← hμ₁, mul_sub, mul_sub, mul_add, mul_add, Finset.mul_sum, h1]
    simp only [h2]
    ring
  rw [hid, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hT0 _)]
  calc T ^ μ₁ * |empOneDim η ξ h k 1 T -
        ∑ j ∈ Finset.range (firstQ h k + 1), A j * T ^ (-lam k (j + h))|
      ≤ T ^ μ₁ * (oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj *
          T ^ (-((firstL h k : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_pos_of_pos hT0 _).le
    _ = _ := by
        rw [neg_sub, Real.rpow_sub hT0, Real.rpow_neg hT0.le]; ring

/-- The uniform bound on the two-term remainder (all `T > 0`). -/
noncomputable def twoTermBound (h k : ℕ) (M : ℝ) (Cj Aj : ℕ → ℝ) : ℝ :=
  Cj 0 * exp (max M 0) + Aj 0 + Aj 1 + ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), Aj j +
    oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj

/-- **The two-term remainder is bounded, uniformly in the data**: given `ξ ≤ M` on `[0,1]`, jet
bounds `C_j` and coefficient bounds `|C_j| ≤ A_j`, `|B(T)| ≤ twoTermBound` for every `T > 0`. -/
theorem abs_twoTermRem_le (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) {M : ℝ} (hM' : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ≤ M) {Cj : ℕ → ℝ}
    (hCj : ∀ j, 0 ≤ Cj j ∧ ∀ v ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 0 ≤ τ →
      |jetPoly η ξ j v τ| ≤ Cj j * (1 + τ) ^ j) {Aj : ℕ → ℝ}
    (hA : ∀ j, |empOneDimCoeff η ξ h k j| ≤ Aj j) {T : ℝ} (hT : 0 < T) :
    |twoTermRem η ξ h k T| ≤ twoTermBound h k M Cj Aj := by
  have hA0 : ∀ j, 0 ≤ Aj j := fun j => (abs_nonneg _).trans (hA j)
  have hK0 := oneDimExpConst_nonneg h k (firstQ h k) (firstL h k) one_pos (M := M)
    fun j => (hCj j).1
  have hS0 : 0 ≤ ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), Aj j := Finset.sum_nonneg fun j _ => hA0 j
  have hC0 : 0 ≤ Cj 0 * exp (max M 0) := mul_nonneg (hCj 0).1 (exp_pos _).le
  have hlt := lam_lt_lam_succ h hk
  unfold twoTermBound
  rcases le_or_gt T 1 with hT1 | hT1
  · -- small `T`: the crude bound
    have hη1 : ∀ u ∈ Icc (0 : ℝ) 1, |η u| ≤ Cj 0 := fun u hu => by
      have := (hCj 0).2 u hu 0 le_rfl
      simpa [jetPoly, jetCoeff_zero_zero] using this
    have hI : |empOneDim η ξ h k 1 T| ≤ Cj 0 * exp (max M 0) := by
      unfold empOneDim
      have hb : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
          ‖η u * u ^ h * exp (-T * u ^ (2 * k) + Real.sqrt T * u ^ k * ξ u)‖ ≤
            Cj 0 * exp (max M 0) := by
        intro u hu
        rw [Set.uIoc_of_le zero_le_one] at hu
        have hu0 : 0 < u := hu.1
        have hu1 : u ≤ 1 := hu.2
        have hs0 : 0 ≤ Real.sqrt T * u ^ k := by positivity
        have hs1 : Real.sqrt T * u ^ k ≤ 1 := by
          have h1 : Real.sqrt T ≤ 1 := Real.sqrt_le_one.2 hT1
          have h2 : u ^ k ≤ 1 := pow_le_one₀ hu0.le hu1
          exact mul_le_one₀ h1 (pow_nonneg hu0.le k) h2
        have hexp : -T * u ^ (2 * k) + Real.sqrt T * u ^ k * ξ u ≤ max M 0 := by
          have h1 : -T * u ^ (2 * k) ≤ 0 := by
            have := pow_pos hu0 (2 * k); nlinarith
          have h2 : Real.sqrt T * u ^ k * ξ u ≤ Real.sqrt T * u ^ k * M :=
            mul_le_mul_of_nonneg_left (hM' u ⟨hu0.le, hu1⟩) hs0
          have h3 : Real.sqrt T * u ^ k * M ≤ max M 0 := by
            rcases le_or_gt 0 M with hM | hM
            · calc Real.sqrt T * u ^ k * M ≤ 1 * M := by gcongr
                _ = M := one_mul M
                _ ≤ max M 0 := le_max_left _ _
            · exact (mul_nonpos_of_nonneg_of_nonpos hs0 hM.le).trans (le_max_right _ _)
          linarith
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _),
          abs_of_pos (pow_pos hu0 h)]
        have h4 : u ^ h ≤ 1 := pow_le_one₀ hu0.le hu1
        calc |η u| * u ^ h * exp (-T * u ^ (2 * k) + Real.sqrt T * u ^ k * ξ u)
            ≤ Cj 0 * 1 * exp (max M 0) :=
              mul_le_mul (mul_le_mul (hη1 u ⟨hu0.le, hu1⟩) h4 (pow_pos hu0 h).le (hCj 0).1)
                (exp_le_exp.2 hexp) (exp_pos _).le (mul_nonneg (hCj 0).1 zero_le_one)
          _ = Cj 0 * exp (max M 0) := by ring
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      simpa using this
    have hp1 : T ^ lam k (1 + h) ≤ 1 := Real.rpow_le_one hT.le hT1 (lam_pos hk _).le
    have hp2 : T ^ (lam k (1 + h) - lam k h) ≤ 1 := Real.rpow_le_one hT.le hT1 (by linarith)
    have hp0 : 0 ≤ T ^ lam k (1 + h) := (Real.rpow_pos_of_pos hT _).le
    unfold twoTermRem
    rw [abs_mul, abs_of_nonneg hp0]
    have hprod : T ^ lam k (1 + h) * (|empOneDimCoeff η ξ h k 0| * T ^ (-lam k h)) =
        |empOneDimCoeff η ξ h k 0| * T ^ (lam k (1 + h) - lam k h) := by
      rw [Real.rpow_sub hT, Real.rpow_neg hT.le]; ring
    calc T ^ lam k (1 + h) * |empOneDim η ξ h k 1 T - empOneDimCoeff η ξ h k 0 * T ^ (-lam k h)|
        ≤ T ^ lam k (1 + h) * (|empOneDim η ξ h k 1 T| +
            |empOneDimCoeff η ξ h k 0| * T ^ (-lam k h)) := by
          gcongr
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hT _)]
      _ = T ^ lam k (1 + h) * |empOneDim η ξ h k 1 T| +
            |empOneDimCoeff η ξ h k 0| * T ^ (lam k (1 + h) - lam k h) := by rw [mul_add, hprod]
      _ ≤ 1 * (Cj 0 * exp (max M 0)) + Aj 0 * 1 :=
          add_le_add (mul_le_mul hp1 hI (abs_nonneg _) zero_le_one)
            (mul_le_mul (hA 0) hp2 (Real.rpow_pos_of_pos hT _).le (hA0 0))
      _ ≤ _ := by nlinarith [hA0 1]
  · -- large `T`: the expansion
    have hT1' : 1 ≤ T := hT1.le
    have key := twoTermRem_sub_le hη hξ h hk hM' hCj hT1'
    have hL := lam_lt_firstL h k
    have hpow : T ^ (-((firstL h k : ℝ) - lam k (1 + h))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hT1' (by linarith)
    have hsum : |∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
        empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h)))| ≤
        ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), Aj j := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hj2 : 2 ≤ j := (Finset.mem_Ico.1 hj).1
      have hle : lam k (1 + h) ≤ lam k (j + h) := lam_le_lam_of_le hk (by omega)
      have hp : T ^ (-(lam k (j + h) - lam k (1 + h))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hT1' (by linarith)
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hT _)]
      calc |empOneDimCoeff η ξ h k j| * T ^ (-(lam k (j + h) - lam k (1 + h))) ≤ Aj j * 1 :=
            mul_le_mul (hA j) hp (Real.rpow_pos_of_pos hT _).le (hA0 j)
        _ = Aj j := mul_one _
    have hK : oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj *
        T ^ (-((firstL h k : ℝ) - lam k (1 + h))) ≤
        oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj := by
      calc _ ≤ oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj * 1 := by gcongr
        _ = _ := mul_one _
    have htri := abs_sub_abs_le_abs_sub (twoTermRem η ξ h k T)
      (empOneDimCoeff η ξ h k 1 + ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
        empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h))))
    have habs : |empOneDimCoeff η ξ h k 1 + ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
        empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h)))| ≤
        Aj 1 + ∑ j ∈ Finset.Ico 2 (firstQ h k + 1), Aj j :=
      (abs_add_le _ _).trans (add_le_add (hA 1) hsum)
    have hkey' : |twoTermRem η ξ h k T - (empOneDimCoeff η ξ h k 1 +
        ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
          empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h))))| ≤
        oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj := by
      rw [← sub_sub]; exact key.trans hK
    have := hA0 0
    linarith

/-- **The two-term remainder converges to the first correction**: `B(T) → C_1` as `T → ∞`. -/
theorem tendsto_twoTermRem (hη : ContDiff ℝ ∞ η) (hξ : ContDiff ℝ ∞ ξ) (h : ℕ) {k : ℕ}
    (hk : 0 < k) :
    Tendsto (twoTermRem η ξ h k) atTop (𝓝 (empOneDimCoeff η ξ h k 1)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hξ.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  have hM' : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ≤ M := fun t ht =>
    (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM t ht)
  choose Cj hCj using fun j => exists_jetPoly_bound hη hξ j 0 1
  set S : ℝ → ℝ := fun T => ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
    empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h))) with hS
  have hStend : Tendsto S atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => ∑ j ∈ Finset.Ico 2 (firstQ h k + 1),
        empOneDimCoeff η ξ h k j * T ^ (-(lam k (j + h) - lam k (1 + h)))) atTop
        (𝓝 (∑ j ∈ Finset.Ico 2 (firstQ h k + 1), empOneDimCoeff η ξ h k j * 0)) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hj2 : 2 ≤ j := (Finset.mem_Ico.1 hj).1
      have hlt : lam k (1 + h) < lam k (j + h) := by
        have := lam_le_lam_of_le hk (show 2 + h ≤ j + h by omega)
        have := lam_lt_lam_succ (1 + h) hk
        rw [show 1 + (1 + h) = 2 + h by ring] at this
        linarith
      exact (tendsto_rpow_neg_atTop (by linarith)).const_mul _
    rw [show (∑ j ∈ Finset.Ico 2 (firstQ h k + 1), empOneDimCoeff η ξ h k j * (0 : ℝ)) = 0 by
      simp] at this
    exact this
  have hE : Tendsto (fun T => twoTermRem η ξ h k T - empOneDimCoeff η ξ h k 1 - S T) atTop
      (𝓝 0) := by
    have hL := lam_lt_firstL h k
    have hmaj : Tendsto (fun T : ℝ => oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj *
        T ^ (-((firstL h k : ℝ) - lam k (1 + h)))) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := (firstL h k : ℝ) - lam k (1 + h))
        (by linarith)).const_mul (oneDimExpConst h k (firstQ h k) (firstL h k) 1 M Cj)
      simpa using this
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [Real.norm_eq_abs]
    exact twoTermRem_sub_le hη hξ h hk hM' hCj hT
  have hc : Tendsto (fun _ : ℝ => empOneDimCoeff η ξ h k 1) atTop
      (𝓝 (empOneDimCoeff η ξ h k 1)) := tendsto_const_nhds
  have := (hE.add hStend).add hc
  rw [add_zero, zero_add] at this
  refine this.congr fun T => ?_
  ring

end OneDim

/-! ### Coordinate slices of a smooth function -/

variable {n : ℕ}

/-- The one-variable slice of `G` along the coordinate `i₀` through the complementary point
`w`: `u ↦ G(insertNth i₀ u w)`. -/
def coordSlice (i₀ : Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ) (w : Fin n → ℝ) : ℝ → ℝ :=
  fun u => G (Fin.insertNth i₀ u w)

theorem line_insertNth (G : (Fin (n + 1) → ℝ) → ℝ) (i₀ : Fin (n + 1)) (v : ℝ) (w : Fin n → ℝ) :
    line G i₀ (Fin.insertNth i₀ v w) = coordSlice i₀ G w := by
  funext t
  simp only [line, coordSlice, Fin.update_insertNth]

theorem contDiff_coordSlice {G : (Fin (n + 1) → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (i₀ : Fin (n + 1))
    (w : Fin n → ℝ) : ContDiff ℝ ∞ (coordSlice i₀ G w) := by
  rw [← line_insertNth G i₀ 0 w]
  exact contDiff_line hG i₀ _

theorem continuous_coordSlice {G : (Fin (n + 1) → ℝ) → ℝ} (hG : Continuous G) (i₀ : Fin (n + 1))
    (w : Fin n → ℝ) : Continuous (coordSlice i₀ G w) :=
  hG.comp (continuous_id.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i₀ continuous_const)

/-- The derivative of a slice is the coordinate derivative. -/
theorem deriv_coordSlice (G : (Fin (n + 1) → ℝ) → ℝ) (i₀ : Fin (n + 1)) (w : Fin n → ℝ)
    (v : ℝ) : deriv (coordSlice i₀ G w) v = pd i₀ G (Fin.insertNth i₀ v w) := by
  simp only [pd, line_insertNth, Fin.insertNth_apply_same]

theorem insertNth_mem_closedBox {i₀ : Fin (n + 1)} {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    {w : Fin n → ℝ} (hw : w ∈ closedBox n 1) : Fin.insertNth i₀ v w ∈ closedBox (n + 1) 1 := by
  intro i _
  rcases Fin.eq_self_or_eq_succAbove i₀ i with hi | ⟨j, hj⟩
  · subst hi; simpa using hv
  · subst hj; simpa using hw j (mem_univ j)

/-- **The jets of the slices are restrictions of smooth functions**: for each `(j, r)` there is a
smooth `G_{j,r}` on `ℝ^{n+1}` with `p_{j,r}[η_w, ζ_w](v) = G_{j,r}(insertNth i₀ v w)`. -/
theorem exists_jetCoeff_coordSlice {η ζ : (Fin (n + 1) → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (i₀ : Fin (n + 1)) :
    ∀ j r : ℕ, ∃ G : (Fin (n + 1) → ℝ) → ℝ, ContDiff ℝ ∞ G ∧
      ∀ (w : Fin n → ℝ) (v : ℝ),
        jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j r v = G (Fin.insertNth i₀ v w)
  | 0, 0 => ⟨η, hη, fun _ _ => rfl⟩
  | 0, _ + 1 => ⟨fun _ => 0, contDiff_const, fun _ _ => rfl⟩
  | j + 1, 0 => by
    obtain ⟨G, hG, hGe⟩ := exists_jetCoeff_coordSlice hη hζ i₀ j 0
    refine ⟨pd i₀ G, contDiff_pd hG i₀, fun w v => ?_⟩
    rw [jetCoeff_succ_zero]
    have : jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j 0 = coordSlice i₀ G w :=
      funext fun v => hGe w v
    rw [this, deriv_coordSlice]
  | j + 1, r + 1 => by
    obtain ⟨G₁, hG₁, hG₁e⟩ := exists_jetCoeff_coordSlice hη hζ i₀ j (r + 1)
    obtain ⟨G₂, hG₂, hG₂e⟩ := exists_jetCoeff_coordSlice hη hζ i₀ j r
    refine ⟨fun v => pd i₀ G₁ v + pd i₀ ζ v * G₂ v,
      (contDiff_pd hG₁ i₀).add ((contDiff_pd hζ i₀).mul hG₂), fun w v => ?_⟩
    rw [jetCoeff_succ_succ]
    have h1 : jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j (r + 1) = coordSlice i₀ G₁ w :=
      funext fun v => hG₁e w v
    simp only [h1, deriv_coordSlice, hG₂e]

/-- **Uniform jet bounds over the face**: the field-derivative polynomials of the slices satisfy
`|P_j(v, τ)| ≤ C_j (1+τ)^j` with `C_j` independent of `w ∈ [0,1]^n`. -/
theorem exists_jetPoly_coordSlice_bound {η ζ : (Fin (n + 1) → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (i₀ : Fin (n + 1)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ closedBox n 1, ∀ v ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 0 ≤ τ →
      |jetPoly (coordSlice i₀ η w) (coordSlice i₀ ζ w) j v τ| ≤ C * (1 + τ) ^ j := by
  have hbd : ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ closedBox n 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j r v| ≤ C := fun r => by
    obtain ⟨G, hG, hGe⟩ := exists_jetCoeff_coordSlice hη hζ i₀ j r
    obtain ⟨C, hC⟩ := (isCompact_closedBox (d := n + 1) 1).exists_bound_of_continuousOn
      hG.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun w hw v hv => ?_⟩
    rw [hGe]
    exact (Real.norm_eq_abs _ ▸ hC _ (insertNth_mem_closedBox hv hw)).trans (le_max_left _ _)
  choose Cf hCf using hbd
  refine ⟨∑ r ∈ Finset.range (j + 1), Cf r, Finset.sum_nonneg fun r _ => (hCf r).1,
    fun w hw v hv τ hτ => ?_⟩
  unfold jetPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg hτ r)]
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have hτr : τ ^ r ≤ (1 + τ) ^ j :=
    (pow_le_pow_left₀ hτ (by linarith) r).trans (pow_le_pow_right₀ (by linarith) hr')
  exact mul_le_mul ((hCf r).2 w hw v hv) hτr (pow_nonneg hτ r) (hCf r).1

/-- The one-dimensional coefficients of the slices depend continuously on the face point. -/
theorem continuous_coordSlice_coeff {η ζ : (Fin (n + 1) → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (i₀ : Fin (n + 1)) (h : ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    Continuous fun w : Fin n → ℝ =>
      empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h k j := by
  have heq : ∀ w : Fin n → ℝ, empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h k j =
      (∑ r ∈ Finset.range (j + 1), jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j r 0 *
        fluctuation 1 (lam k (j + h) + r / 2) (ζ (Fin.insertNth i₀ 0 w))) /
        ((j.factorial : ℝ) * (2 * k)) := fun w =>
    empOneDimCoeff_eq_sum (contDiff_coordSlice hη i₀ w) (contDiff_coordSlice hζ i₀ w) h hk j
  simp only [heq]
  refine Continuous.div_const ?_ _
  refine continuous_finsetSum _ fun r _ => ?_
  obtain ⟨G, hG, hGe⟩ := exists_jetCoeff_coordSlice hη hζ i₀ j r
  have h1 : ∀ w : Fin n → ℝ, jetCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) j r 0 =
      G (Fin.insertNth i₀ 0 w) := fun w => hGe w 0
  simp only [h1]
  have hins : Continuous fun w : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i₀ (0 : ℝ) w :=
    continuous_const.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i₀ continuous_id
  have hμ : 0 < lam k (j + h) + r / 2 := by have := lam_pos hk (j + h); positivity
  exact (hG.continuous.comp hins).mul
    ((continuous_fluctuation 1 _ one_pos hμ).comp (hζ.continuous.comp hins))

/-- The one-dimensional integral of the slices at a continuously varying effective sample size
is continuous in the face point. -/
theorem continuous_empOneDim_coordSlice {η ζ : (Fin (n + 1) → ℝ) → ℝ} (hη : Continuous η)
    (hζ : Continuous ζ) (i₀ : Fin (n + 1)) (h k : ℕ) {T : (Fin n → ℝ) → ℝ} (hT : Continuous T) :
    Continuous fun w : Fin n → ℝ =>
      empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h k 1 (T w) := by
  unfold empOneDim coordSlice
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 1
  have hins : Continuous fun p : (Fin n → ℝ) × ℝ => Fin.insertNth (α := fun _ => ℝ) i₀ p.2 p.1 :=
    continuous_snd.finInsertNth (A := fun _ : Fin (n + 1) => ℝ) i₀ continuous_fst
  have h1 : Continuous fun p : (Fin n → ℝ) × ℝ => T p.1 := hT.comp continuous_fst
  fun_prop

/-! ### Fubini along one coordinate -/

theorem restrict_box_eq_pi (d : ℕ) (b : ℝ) :
    (volume : Measure (Fin d → ℝ)).restrict (box (Fin d) b) =
      Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 b) := by
  rw [box, volume_pi, Measure.restrict_pi_pi]

/-- **Fubini along the coordinate `i₀`** on the unit box. -/
theorem integral_box_insertNth (i₀ : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : IntegrableOn F (box (Fin (n + 1)) 1)) :
    ∫ v in box (Fin (n + 1)) 1, F v =
      ∫ w in box (Fin n) 1, ∫ u in Ioc (0 : ℝ) 1, F (Fin.insertNth i₀ u w) := by
  have hmp := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure ℝ).restrict (Ioc 0 1)) i₀
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀ with he
  have hsymm : ∀ y : ℝ × (Fin n → ℝ), e.symm y = Fin.insertNth i₀ y.1 y.2 := fun y => rfl
  unfold IntegrableOn at hF
  rw [restrict_box_eq_pi] at hF ⊢
  rw [restrict_box_eq_pi]
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  have hint : Integrable (fun y => F (e.symm y))
      (((volume : Measure ℝ).restrict (Ioc 0 1)).prod
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Ioc 0 1))) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hF
  change ∫ y, F (e.symm y) ∂(((volume : Measure ℝ).restrict (Ioc 0 1)).prod
    (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Ioc 0 1))) = _
  rw [integral_prod_symm _ hint]
  simp only [hsymm]

theorem mono_insertNth (γ : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1)) (u : ℝ) (w : Fin n → ℝ) :
    mono γ (Fin.insertNth i₀ u w) = u ^ γ i₀ * mono (fun j => γ (i₀.succAbove j)) w := by
  unfold mono
  rw [Fin.prod_univ_succAbove _ i₀]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

variable (η ζ : (Fin (n + 1) → ℝ) → ℝ) (h k : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1))

/-- The exponent data of the complementary coordinates. -/
def sliceExp (γ : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1)) : Fin n → ℕ := fun j => γ (i₀.succAbove j)

/-- ★ **The empirical integral as a face integral of one-dimensional integrals**: for `N > 0`,
`Z_N = ∫_{[0,1]^n} w^{h_L} · I_w(N w^{2k_L}) dw` with `I_w` the one-dimensional empirical integral
of the slices `(η_w, ζ_w)` with exponents `(h_{i₀}, k_{i₀})`. -/
theorem empIntegral_eq_slice (hη : Continuous η) (hζ : Continuous ζ) {N : ℝ} (hN : 0 < N) :
    empIntegral η ζ h k N = ∫ w in box (Fin n) 1, mono (sliceExp h i₀) w *
      empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) (h i₀) (k i₀) 1
        (N * mono (fun j => 2 * sliceExp k i₀ j) w) := by
  have hc1 := continuous_mono h
  have hc2 := continuous_mono (fun i => 2 * k i)
  have hc3 := continuous_mono k
  rw [empIntegral_eq, integral_box_insertNth i₀ _ (integrableOn_box_one_of_continuous
    (by fun_prop))]
  refine setIntegral_congr_fun (measurableSet_box 1) fun w hw => ?_
  unfold empOneDim
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  have hw0 : ∀ j, 0 < w j := fun j => (hw j (mem_univ j)).1
  have hP : mono (fun j => 2 * sliceExp k i₀ j) w = mono (sliceExp k i₀) w ^ 2 := by
    unfold mono
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hsq : Real.sqrt (N * mono (fun j => 2 * sliceExp k i₀ j) w) =
      Real.sqrt N * mono (sliceExp k i₀) w := by
    rw [hP, Real.sqrt_mul hN.le, Real.sqrt_sq (mono_pos _ hw0).le]
  rw [hsq]
  simp only [coordSlice, mono_insertNth]
  unfold sliceExp
  have hexp : -N * (u ^ (2 * k i₀) * mono (fun j => 2 * k (i₀.succAbove j)) w) +
      Real.sqrt N * (u ^ k i₀ * mono (fun j => k (i₀.succAbove j)) w) * ζ (Fin.insertNth i₀ u w) =
      -(N * mono (fun j => 2 * k (i₀.succAbove j)) w) * u ^ (2 * k i₀) +
        Real.sqrt N * mono (fun j => k (i₀.succAbove j)) w * u ^ k i₀ *
          ζ (Fin.insertNth i₀ u w) := by ring
  rw [hexp]
  ring

/-! ### The face weight -/

/-- The face weight `w^{h_L} (w^{2k_L})^{−μ}`. -/
noncomputable def faceWt (μ : ℝ) (w : Fin n → ℝ) : ℝ :=
  mono (sliceExp h i₀) w * mono (fun j => 2 * sliceExp k i₀ j) w ^ (-μ)

theorem faceWt_eq_prod (μ : ℝ) {w : Fin n → ℝ} (hw : ∀ j, 0 < w j) :
    faceWt h k i₀ μ w =
      ∏ j, w j ^ ((sliceExp h i₀ j : ℝ) - 2 * (sliceExp k i₀ j : ℝ) * μ) := by
  unfold faceWt mono
  rw [← Real.finsetProd_rpow _ _ (fun j _ => pow_nonneg (hw j).le _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hw j).le,
    ← Real.rpow_add (hw j)]
  congr 1
  push_cast
  ring

theorem faceWt_nonneg (μ : ℝ) {w : Fin n → ℝ} (hw : ∀ j, 0 < w j) : 0 ≤ faceWt h k i₀ μ w := by
  unfold faceWt
  have := mono_pos (sliceExp h i₀) hw
  have := mono_pos (fun j => 2 * sliceExp k i₀ j) hw
  positivity

theorem measurable_faceWt (μ : ℝ) : Measurable (faceWt h k i₀ μ) :=
  (continuous_mono _).measurable.mul ((continuous_mono _).measurable.pow_const _)

/-- The face weight is integrable on the box when `2k_l μ < h_l + 1` for every complementary
coordinate. -/
theorem integrableOn_faceWt {μ : ℝ}
    (hμ : ∀ j : Fin n, 2 * (sliceExp k i₀ j : ℝ) * μ < sliceExp h i₀ j + 1) :
    IntegrableOn (faceWt h k i₀ μ) (box (Fin n) 1) := by
  have hc : ∀ j : Fin n, -1 < (sliceExp h i₀ j : ℝ) - 2 * (sliceExp k i₀ j : ℝ) * μ :=
    fun j => by linarith [hμ j]
  have := integrableOn_prod_rpow_mul_log_pow hc (fun _ => 0) 0 zero_le_one
  simp only [pow_zero, mul_one] at this
  exact this.congr_fun (fun w hw => (faceWt_eq_prod h k i₀ μ fun j =>
    (hw j (mem_univ j)).1).symm) (measurableSet_box 1)

/-! ### The first correction in dimension `n + 1` -/

/-- The face coefficients `∫_{[0,1]^n} w^{h_L} (w^{2k_L})^{−μ_j} · C_j[η_w, ζ_w] dw`
of the resonant coordinate `i₀`, `μ_j = (h_{i₀} + j + 1)/(2k_{i₀})`. -/
noncomputable def genericFaceCoeff (j : ℕ) : ℝ :=
  ∫ w in box (Fin n) 1, faceWt h k i₀ (lam (k i₀) (j + h i₀)) w *
    empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) (h i₀) (k i₀) j

/-- The gap condition on the complementary coordinates gives the weight-integrability inequality
at every `μ ≤ μ₁`. -/
theorem gap_weight {hk : ∀ i, 0 < k i}
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) {μ : ℝ}
    (hμ : μ ≤ lam (k i₀) (1 + h i₀)) (j : Fin n) :
    2 * (sliceExp k i₀ j : ℝ) * μ < sliceExp h i₀ j + 1 := by
  have h1 := lt_of_le_of_lt hμ (hgap j)
  unfold ratioExp at h1
  have hk' : (0 : ℝ) < 2 * (k (i₀.succAbove j) : ℝ) := by
    have := hk (i₀.succAbove j); positivity
  rw [lt_div_iff₀ hk'] at h1
  unfold sliceExp
  linarith

/-- ★★ **The first correction of the empirical integral (generic case)**: if the resonant
coordinate `i₀` has `μ₁ = (h_{i₀}+2)/(2k_{i₀})` strictly below every other ratio, then
`N^{μ₁} (Z_N − C_λ N^{−λ}) → C_{μ₁}` with `C_λ = genericFaceCoeff 0`,
`C_{μ₁} = genericFaceCoeff 1`. -/
theorem tendsto_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    Tendsto (fun N : ℝ => N ^ lam (k i₀) (1 + h i₀) *
        (empIntegral η ζ h k N - genericFaceCoeff η ζ h k i₀ 0 * N ^ (-lam (k i₀) (h i₀))))
      atTop (𝓝 (genericFaceCoeff η ζ h k i₀ 1)) := by
  set h₀ := h i₀ with hh₀
  set k₀ := k i₀ with hk₀
  have hk0 : 0 < k₀ := hk i₀
  set lam₀ := lam k₀ h₀ with hlam₀
  set μ₁ := lam k₀ (1 + h₀) with hμ₁
  have hlt : lam₀ < μ₁ := lam_lt_lam_succ h₀ hk0
  set P : (Fin n → ℝ) → ℝ := mono (fun j => 2 * sliceExp k i₀ j) with hP
  have hPc : Continuous P := continuous_mono _
  -- uniform data over the face
  obtain ⟨M, hM⟩ := (isCompact_closedBox (d := n + 1) 1).exists_bound_of_continuousOn
    hζ.continuous.continuousOn
  have hM' : ∀ w ∈ closedBox n 1, ∀ t ∈ Icc (0 : ℝ) 1, coordSlice i₀ ζ w t ≤ M :=
    fun w hw t ht => (le_abs_self _).trans
      (Real.norm_eq_abs _ ▸ hM _ (insertNth_mem_closedBox ht hw))
  choose Cj hCj using fun j => exists_jetPoly_coordSlice_bound hη hζ i₀ j
  have hAj : ∀ j : ℕ, ∃ A : ℝ, ∀ w ∈ closedBox n 1,
      |empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ j| ≤ A := fun j => by
    obtain ⟨A, hA⟩ := (isCompact_closedBox (d := n) 1).exists_bound_of_continuousOn
      (continuous_coordSlice_coeff hη hζ i₀ h₀ hk0 j).continuousOn
    exact ⟨A, fun w hw => Real.norm_eq_abs _ ▸ hA w hw⟩
  choose Aj hAj using hAj
  set K := twoTermBound h₀ k₀ M Cj Aj with hK
  have hbox : ∀ w ∈ box (Fin n) 1, w ∈ closedBox n 1 := fun w hw => box_subset_closedBox 1 hw
  have hwpos : ∀ w ∈ box (Fin n) 1, ∀ j, 0 < w j := fun w hw j => (hw j (mem_univ j)).1
  have hPpos : ∀ w ∈ box (Fin n) 1, 0 < P w := fun w hw => mono_pos _ (hwpos w hw)
  -- the remainder integrand and its bound
  set F : ℝ → (Fin n → ℝ) → ℝ := fun N w => faceWt h k i₀ μ₁ w *
    twoTermRem (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ (N * P w) with hF
  have hwt := integrableOn_faceWt h k i₀ (gap_weight h k i₀ (hk := hk) hgap le_rfl)
  have hwt₀ := integrableOn_faceWt h k i₀ (gap_weight h k i₀ (hk := hk) hgap hlt.le)
  have hbound : ∀ N : ℝ, 0 < N → ∀ w ∈ box (Fin n) 1, |F N w| ≤ K * faceWt h k i₀ μ₁ w := by
    intro N hN w hw
    have hR := abs_twoTermRem_le (contDiff_coordSlice hη i₀ w) (contDiff_coordSlice hζ i₀ w) h₀
      hk0 (hM' w (hbox w hw)) (fun j => ⟨(hCj j).1, (hCj j).2 w (hbox w hw)⟩)
      (fun j => hAj j w (hbox w hw)) (mul_pos hN (hPpos w hw))
    simp only [hF]
    rw [abs_mul, abs_of_nonneg (faceWt_nonneg h k i₀ μ₁ (hwpos w hw)), mul_comm]
    exact mul_le_mul_of_nonneg_right hR (faceWt_nonneg h k i₀ μ₁ (hwpos w hw))
  have hFmeas : ∀ N : ℝ, Measurable (F N) := by
    intro N
    have h1 : Measurable fun w : Fin n → ℝ =>
        empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 1 (N * P w) :=
      (continuous_empOneDim_coordSlice hη.continuous hζ.continuous i₀ h₀ k₀
        (continuous_const.mul hPc)).measurable
    have h2 : Measurable fun w : Fin n → ℝ =>
        empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0 :=
      (continuous_coordSlice_coeff hη hζ i₀ h₀ hk0 0).measurable
    have h3 : Measurable fun w : Fin n → ℝ => N * P w := continuous_const.mul hPc |>.measurable
    simp only [hF, twoTermRem]
    exact (measurable_faceWt h k i₀ μ₁).mul
      ((h3.pow_const _).mul (h1.sub (h2.mul (h3.pow_const _))))
  have hFint : ∀ N : ℝ, 0 < N → IntegrableOn (F N) (box (Fin n) 1) := fun N hN =>
    Integrable.mono' (hwt.const_mul K) (hFmeas N).aestronglyMeasurable
      ((ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun w hw => by
        rw [Real.norm_eq_abs]; exact hbound N hN w hw))
  have hg0 : genericFaceCoeff η ζ h k i₀ 0 = ∫ w in box (Fin n) 1, faceWt h k i₀ lam₀ w *
      empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0 := by
    unfold genericFaceCoeff
    simp only [Nat.zero_add]
    rfl
  -- the identity `N^{μ₁}(Z_N − C₀ N^{−λ}) = ∫ F N`
  have hident : ∀ N : ℝ, 0 < N → N ^ μ₁ *
      (empIntegral η ζ h k N - genericFaceCoeff η ζ h k i₀ 0 * N ^ (-lam₀)) =
      ∫ w in box (Fin n) 1, F N w := by
    intro N hN
    have hA₀ : IntegrableOn (fun w => faceWt h k i₀ lam₀ w *
        empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0) (box (Fin n) 1) := by
      have hb : ∀ᵐ w ∂(volume.restrict (box (Fin n) 1)),
          ‖empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0‖ ≤ Aj 0 :=
        (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun w hw => by
          rw [Real.norm_eq_abs]; exact hAj 0 w (hbox w hw))
      exact (Integrable.bdd_mul hwt₀
        (continuous_coordSlice_coeff hη hζ i₀ h₀ hk0 0).measurable.aestronglyMeasurable hb).congr
        (Eventually.of_forall fun w => mul_comm _ _)
    have hpt : ∀ w ∈ box (Fin n) 1, F N w = N ^ μ₁ * (mono (sliceExp h i₀) w *
        empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 1 (N * P w)) -
        N ^ (μ₁ - lam₀) * (faceWt h k i₀ lam₀ w *
          empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0) := by
      intro w hw
      have hPw := hPpos w hw
      simp only [hF, twoTermRem, faceWt, ← hP]
      rw [← hμ₁, ← hlam₀, Real.mul_rpow hN.le hPw.le, Real.mul_rpow hN.le hPw.le,
        Real.rpow_neg hPw.le, Real.rpow_neg hN.le, Real.rpow_neg hPw.le, Real.rpow_sub hN]
      have := (Real.rpow_pos_of_pos hPw μ₁).ne'
      have := (Real.rpow_pos_of_pos hPw lam₀).ne'
      have := (Real.rpow_pos_of_pos hN lam₀).ne'
      field_simp
    have hZ := empIntegral_eq_slice η ζ h k i₀ hη.continuous hζ.continuous hN
    have hZint : IntegrableOn (fun w => N ^ μ₁ * (mono (sliceExp h i₀) w *
        empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 1 (N * P w)))
        (box (Fin n) 1) := by
      have := (hFint N hN).add (hA₀.const_mul (N ^ (μ₁ - lam₀)))
      refine this.congr_fun (fun w hw => ?_) (measurableSet_box 1)
      simp only [Pi.add_apply]
      rw [hpt w hw]; ring
    calc N ^ μ₁ * (empIntegral η ζ h k N - genericFaceCoeff η ζ h k i₀ 0 * N ^ (-lam₀))
        = N ^ μ₁ * empIntegral η ζ h k N - N ^ (μ₁ - lam₀) * genericFaceCoeff η ζ h k i₀ 0 := by
          rw [Real.rpow_sub hN, Real.rpow_neg hN.le]; ring
      _ = (∫ w in box (Fin n) 1, N ^ μ₁ * (mono (sliceExp h i₀) w *
            empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 1 (N * P w))) -
          ∫ w in box (Fin n) 1, N ^ (μ₁ - lam₀) * (faceWt h k i₀ lam₀ w *
            empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0) := by
          rw [hZ, integral_const_mul, integral_const_mul, hg0]
      _ = ∫ w in box (Fin n) 1, (N ^ μ₁ * (mono (sliceExp h i₀) w *
            empOneDim (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 1 (N * P w)) -
          N ^ (μ₁ - lam₀) * (faceWt h k i₀ lam₀ w *
            empOneDimCoeff (coordSlice i₀ η w) (coordSlice i₀ ζ w) h₀ k₀ 0)) :=
          (integral_sub hZint (hA₀.const_mul _)).symm
      _ = ∫ w in box (Fin n) 1, F N w :=
          setIntegral_congr_fun (measurableSet_box 1) fun w hw => (hpt w hw).symm
  -- dominated convergence
  have hlim : Tendsto (fun N : ℝ => ∫ w in box (Fin n) 1, F N w) atTop
      (𝓝 (genericFaceCoeff η ζ h k i₀ 1)) := by
    unfold genericFaceCoeff
    refine tendsto_integral_filter_of_dominated_convergence (fun w => K * faceWt h k i₀ μ₁ w)
      (Eventually.of_forall fun N => (hFmeas N).aestronglyMeasurable) ?_ (hwt.const_mul K) ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun w hw => by
        rw [Real.norm_eq_abs]; exact hbound N hN w hw)
    · refine (ae_restrict_iff' (measurableSet_box 1)).2 (Eventually.of_forall fun w hw => ?_)
      have hT : Tendsto (fun N : ℝ => N * P w) atTop atTop :=
        tendsto_id.atTop_mul_const (hPpos w hw)
      exact ((tendsto_twoTermRem (contDiff_coordSlice hη i₀ w) (contDiff_coordSlice hζ i₀ w) h₀
        hk0).comp hT).const_mul _
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hident N hN).symm

/-- The leading term recovered from the two-term limit: `N^{λ} Z_N → C_λ = genericFaceCoeff 0`. -/
theorem tendsto_leading_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    Tendsto (fun N : ℝ => N ^ lam (k i₀) (h i₀) * empIntegral η ζ h k N) atTop
      (𝓝 (genericFaceCoeff η ζ h k i₀ 0)) := by
  have h1 := tendsto_firstCorrection η ζ h k i₀ hη hζ hk hgap
  have hlt := lam_lt_lam_succ (h i₀) (hk i₀)
  have h2 : Tendsto (fun N : ℝ => N ^ (-(lam (k i₀) (1 + h i₀) - lam (k i₀) (h i₀)))) atTop
      (𝓝 0) := tendsto_rpow_neg_atTop (by linarith)
  have hc : Tendsto (fun _ : ℝ => genericFaceCoeff η ζ h k i₀ 0) atTop
      (𝓝 (genericFaceCoeff η ζ h k i₀ 0)) := tendsto_const_nhds
  have := (h1.mul h2).add hc
  rw [mul_zero, zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have := (Real.rpow_pos_of_pos hN (lam (k i₀) (h i₀))).ne'
  have := (Real.rpow_pos_of_pos hN (lam (k i₀) (1 + h i₀))).ne'
  rw [neg_sub, Real.rpow_sub hN, Real.rpow_neg hN.le]
  field_simp
  ring

/-! ### Identification of the canonical coefficients -/

theorem lam_succ_eq_div_Qamb (hk : ∀ i, 0 < k i) :
    ∃ m : ℕ, lam (k i₀) (1 + h i₀) = (m : ℝ) / Qamb k := by
  obtain ⟨m, hm⟩ := ratioExp_eq_div_Qamb (Function.update h i₀ (h i₀ + 1)) k hk i₀
  refine ⟨m, ?_⟩
  rw [← hm]
  unfold ratioExp lam
  simp only [Function.update_self]
  push_cast
  ring

/-- ★★★ **The two leading canonical coefficients in the generic case**: for every lattice exponent
`μ ≤ μ₁ = λ + 1/(2k_{i₀})` and every log degree `q ≤ n`,
`empCoeff η ζ h k μ q = [μ = λ, q = 0] · C_λ + [μ = μ₁, q = 0] · C_{μ₁}`
with the readable face integrals `C_λ = genericFaceCoeff 0`, `C_{μ₁} = genericFaceCoeff 1`. In
particular there are no logarithms at `λ` or `μ₁`, and no terms strictly between them. -/
theorem empCoeff_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ₁ : μ ≤ lam (k i₀) (1 + h i₀)) {q : ℕ}
    (hq : q ≤ n) :
    empCoeff η ζ h k μ q =
      (if μ = ratioExp h k i₀ ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 0 else 0) +
      (if μ = lam (k i₀) (1 + h i₀) ∧ q = 0 then genericFaceCoeff η ζ h k i₀ 1 else 0) := by
  have hexp := emp_cutoffExpansion (h := h) hη hζ hk
  rw [show n + 1 - 1 = n from rfl] at hexp
  have hlam : lam (k i₀) (h i₀) = ratioExp h k i₀ := rfl
  have hlim := tendsto_firstCorrection η ζ h k i₀ hη hζ hk hgap
  rw [hlam] at hlim
  exact hexp.coeff_eq_of_twoTerm (Qamb_pos k hk) (ratioExp_eq_div_Qamb h k hk i₀)
    (lam_succ_eq_div_Qamb h k i₀ hk) hlim hμ hμ₁ hq

/-- The leading canonical coefficient is the face integral `C_λ`. -/
theorem empCoeff_leading_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    empCoeff η ζ h k (ratioExp h k i₀) 0 = genericFaceCoeff η ζ h k i₀ 0 := by
  have hlt := lam_lt_lam_succ (h i₀) (hk i₀)
  rw [empCoeff_generic η ζ h k i₀ hη hζ hk hgap (ratioExp_eq_div_Qamb h k hk i₀) hlt.le
    (Nat.zero_le n)]
  have hne : ratioExp h k i₀ ≠ lam (k i₀) (1 + h i₀) := ne_of_lt hlt
  simp [hne]

/-- ★★★ **The first correction coefficient is the face integral `C_{μ₁}`** at
`μ₁ = λ + 1/(2k_{i₀})`. -/
theorem empCoeff_firstCorrection (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) :
    empCoeff η ζ h k (ratioExp h k i₀ + 1 / (2 * (k i₀ : ℝ))) 0 =
      genericFaceCoeff η ζ h k i₀ 1 := by
  have hlt := lam_lt_lam_succ (h i₀) (hk i₀)
  have heq : ratioExp h k i₀ + 1 / (2 * (k i₀ : ℝ)) = lam (k i₀) (1 + h i₀) := by
    unfold ratioExp lam
    have : (0 : ℝ) < 2 * (k i₀ : ℝ) := by have := hk i₀; positivity
    push_cast
    field_simp
    ring
  rw [heq, empCoeff_generic η ζ h k i₀ hη hζ hk hgap (lam_succ_eq_div_Qamb h k i₀ hk) le_rfl
    (Nat.zero_le n)]
  have hne : lam (k i₀) (1 + h i₀) ≠ ratioExp h k i₀ := ne_of_gt hlt
  simp [hne]

/-- **No logarithms and no intermediate terms**: every canonical coefficient at a lattice
exponent `μ ≤ μ₁` other than `(λ, 0)` and `(μ₁, 0)` vanishes. -/
theorem empCoeff_eq_zero_generic (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hgap : ∀ j : Fin n, lam (k i₀) (1 + h i₀) < ratioExp h k (i₀.succAbove j)) {μ : ℝ}
    (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) (hμ₁ : μ ≤ lam (k i₀) (1 + h i₀)) {q : ℕ}
    (hq : q ≤ n) (h₁ : ¬ (μ = ratioExp h k i₀ ∧ q = 0))
    (h₂ : ¬ (μ = lam (k i₀) (1 + h i₀) ∧ q = 0)) : empCoeff η ζ h k μ q = 0 := by
  rw [empCoeff_generic η ζ h k i₀ hη hζ hk hgap hμ hμ₁ hq, if_neg h₁, if_neg h₂, add_zero]

/-- **The readable form of the first correction**: with `μ₁ = (h_{i₀}+2)/(2k_{i₀})`,
`C_{μ₁} = (1/2k_{i₀}) ∫_{[0,1]^n} w^{h_L} (w^{2k_L})^{−μ₁}`
`  [∂_{i₀}η(0,w) S_{μ₁}(ζ(0,w)) + η(0,w) ∂_{i₀}ζ(0,w) S_{μ₁+1/2}(ζ(0,w))] dw`. -/
theorem genericFaceCoeff_one_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) :
    genericFaceCoeff η ζ h k i₀ 1 = ∫ w in box (Fin n) 1,
      faceWt h k i₀ (lam (k i₀) (1 + h i₀)) w *
        ((pd i₀ η (Fin.insertNth i₀ 0 w) *
            fluctuation 1 (lam (k i₀) (1 + h i₀)) (ζ (Fin.insertNth i₀ 0 w)) +
          η (Fin.insertNth i₀ 0 w) * pd i₀ ζ (Fin.insertNth i₀ 0 w) *
            fluctuation 1 (lam (k i₀) (1 + h i₀) + 1 / 2) (ζ (Fin.insertNth i₀ 0 w))) /
          (2 * (k i₀ : ℝ))) := by
  unfold genericFaceCoeff
  refine setIntegral_congr_fun (measurableSet_box 1) fun w _ => ?_
  rw [empOneDimCoeff_one (contDiff_coordSlice hη i₀ w) (contDiff_coordSlice hζ i₀ w) (h i₀)
    (hk i₀), deriv_coordSlice, deriv_coordSlice]
  rfl

/-- **The readable form of the leading coefficient**:
`C_λ = (1/2k_{i₀}) ∫_{[0,1]^n} w^{h_L} (w^{2k_L})^{−λ} η(0,w) S_λ(ζ(0,w)) dw`. -/
theorem genericFaceCoeff_zero_eq :
    genericFaceCoeff η ζ h k i₀ 0 = ∫ w in box (Fin n) 1,
      faceWt h k i₀ (lam (k i₀) (h i₀)) w *
        (η (Fin.insertNth i₀ 0 w) * fluctuation 1 (lam (k i₀) (h i₀)) (ζ (Fin.insertNth i₀ 0 w)) /
          (2 * (k i₀ : ℝ))) := by
  unfold genericFaceCoeff
  refine setIntegral_congr_fun (measurableSet_box 1) fun w _ => ?_
  rw [empOneDimCoeff_zero]
  simp only [Nat.zero_add, coordSlice]

end SmoothEngine

end Grammar
