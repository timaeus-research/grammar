/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.StochasticData
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Monomial coefficients of a real power series (Astra #68 unit 6a)

A formal multilinear series `p` on `ι → ℝ` has **monomial coefficients**: for a word
`r : Fin n → ι` with multiplicity vector `wordMult r : ι → ℕ`, the coefficient of the monomial
`u^γ` in the degree-`n` homogeneous term `p n (u, …, u)` is
`monoCoeff p n γ = ∑_{wordMult r = γ} p n (e_{r 0}, …, e_{r (n-1)})` (`apply_const_eq_sum`,
`sum_monoCoeff_mul_mono`). The ℓ¹ control is the **dimension-loss estimate** (Astra #68): the
number of words of length `n` is `(card ι)^n`, so
`∑_{|γ| = n} |monoCoeff p n γ| ≤ (card ι)^n ‖p n‖` (`sum_abs_monoCoeff_le`) and the weighted family
`|monoFamily p γ| b^{|γ|}` is summable as soon as `card ι · b < ρ < radius p`
(`summable_monoFamily_mul_pow`). On the closed cube `|u_j| ≤ b` the monomial series then converges
absolutely to the function represented by `p` (`hasSum_monoFamily_mul_mono`, by regrouping along
degrees with `HasSum.sigma`).

For `ι = Fin d` this produces the data-space element `amplitudeDatum` (zero phase family, amplitude
family `monoFamily p`) with `evalF (toEta b (amplitudeDatum …)) u = f u` on the box
(`evalF_toEta_amplitudeDatum`, `xiCoord_amplitudeDatum`) — the analytic amplitude of one fibre as
a point of the coefficient space of the Taylor-tree programme.

Non-claims: no continuity in a tangential parameter yet (unit 6b/6c, via the joint series); the
margin `card ι · b < ρ` is sufficient, not sharp.
-/

open Set Filter Topology
open scoped NNReal ENNReal

namespace Grammar

open CoeffFamily

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Words and multiplicities -/

/-- The multiplicity vector of a word `r : Fin n → ι`. -/
def wordMult {n : ℕ} (r : Fin n → ι) : ι → ℕ := fun j => (Finset.univ.filter fun i => r i = j).card

theorem sum_wordMult {n : ℕ} (r : Fin n → ι) : ∑ j, wordMult r j = n := by
  unfold wordMult
  rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

theorem prod_pow_wordMult {n : ℕ} (r : Fin n → ι) (u : ι → ℝ) :
    ∏ j, u j ^ wordMult r j = ∏ i, u (r i) := by
  unfold wordMult
  rw [← Finset.prod_fiberwise Finset.univ r (fun i => u (r i))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl fun i hi => (by rw [(Finset.mem_filter.1 hi).2] : u (r i) = u j),
    Finset.prod_const]

/-- The multiplicity vectors of the words of length `n`. -/
def multSet (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) : Finset (ι → ℕ) :=
  Finset.univ.image (wordMult : (Fin n → ι) → ι → ℕ)

theorem wordMult_mem_multSet {n : ℕ} (r : Fin n → ι) : wordMult r ∈ multSet ι n :=
  Finset.mem_image_of_mem _ (Finset.mem_univ r)

theorem sum_eq_of_mem_multSet {n : ℕ} {γ : ι → ℕ} (h : γ ∈ multSet ι n) : ∑ j, γ j = n := by
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 h
  exact sum_wordMult r

/-! ### The homogeneous expansion -/

/-- **The homogeneous expansion**: `p (u, …, u) = ∑_r (∏_i u_{r i}) p (e_{r 0}, …, e_{r (n-1)})`. -/
theorem apply_const_eq_sum {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ)
    (u : ι → ℝ) :
    p (fun _ => u) = ∑ r : Fin n → ι, (∏ i, u (r i)) * p (fun i => Pi.single (r i) 1) := by
  have hu : u = ∑ j, u j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [p.map_sum_finset (fun _ j => u j • (Pi.single j (1 : ℝ) : ι → ℝ)) (fun _ => Finset.univ),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [p.map_smul_univ (fun i => u (r i)) (fun i => Pi.single (r i) 1), smul_eq_mul]

/-- The monomial coefficient of degree `n` at the multi-index `γ`. -/
noncomputable def monoCoeff (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (n : ℕ) (γ : ι → ℕ) : ℝ :=
  ∑ r ∈ (Finset.univ : Finset (Fin n → ι)).filter (fun r => wordMult r = γ),
    p n (fun i => Pi.single (r i) 1)

theorem monoCoeff_eq_zero_of_notMem (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) {n : ℕ}
    {γ : ι → ℕ} (h : γ ∉ multSet ι n) : monoCoeff p n γ = 0 := by
  unfold monoCoeff
  refine Finset.sum_eq_zero fun r hr => ?_
  exact absurd ((Finset.mem_filter.1 hr).2 ▸ wordMult_mem_multSet r) h

/-- **The degree-`n` part in monomials**: `∑_{|γ|=n} monoCoeff p n γ · u^γ = p n (u, …, u)`. -/
theorem sum_monoCoeff_mul_mono (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (n : ℕ) (u : ι → ℝ) :
    ∑ γ ∈ multSet ι n, monoCoeff p n γ * ∏ j, u j ^ γ j = p n (fun _ => u) := by
  rw [apply_const_eq_sum, ← Finset.sum_fiberwise_of_maps_to (g := wordMult) (t := multSet ι n)
    (fun r _ => wordMult_mem_multSet r)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  unfold monoCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← (Finset.mem_filter.1 hr).2, prod_pow_wordMult]
  ring

/-! ### The dimension-loss estimate -/

theorem abs_apply_single_le {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => ι → ℝ) ℝ)
    (r : Fin n → ι) : |p (fun i => Pi.single (r i) 1)| ≤ ‖p‖ := by
  have := p.le_opNorm (fun i => (Pi.single (r i) (1 : ℝ) : ι → ℝ))
  simpa [Pi.norm_single] using this

theorem sum_abs_monoCoeff_le (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (n : ℕ) :
    ∑ γ ∈ multSet ι n, |monoCoeff p n γ| ≤ (Fintype.card ι : ℝ) ^ n * ‖p n‖ := by
  calc ∑ γ ∈ multSet ι n, |monoCoeff p n γ|
      ≤ ∑ γ ∈ multSet ι n, ∑ r ∈ (Finset.univ : Finset (Fin n → ι)).filter
          (fun r => wordMult r = γ), |p n (fun i => Pi.single (r i) 1)| :=
        Finset.sum_le_sum fun γ _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r : Fin n → ι, |p n (fun i => Pi.single (r i) 1)| :=
        Finset.sum_fiberwise_of_maps_to (fun r _ => wordMult_mem_multSet r) _
    _ ≤ ∑ _r : Fin n → ι, ‖p n‖ := Finset.sum_le_sum fun r _ => abs_apply_single_le _ r
    _ = (Fintype.card ι : ℝ) ^ n * ‖p n‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The monomial coefficient family of `p`: `γ ↦ monoCoeff p |γ| γ`. -/
noncomputable def monoFamily (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (γ : ι → ℕ) : ℝ :=
  monoCoeff p (∑ j, γ j) γ

/-- The degree fibration of multi-indices. -/
noncomputable def degreeEquiv (ι : Type*) [Fintype ι] :
    (Σ n : ℕ, {γ : ι → ℕ // ∑ j, γ j = n}) ≃ (ι → ℕ) :=
  Equiv.sigmaFiberEquiv fun γ : ι → ℕ => ∑ j, γ j

/-- The finite set of degree-`n` multi-indices realised by words, as a finset of the fibre. -/
def degSet (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    Finset {γ : ι → ℕ // ∑ j, γ j = n} :=
  (multSet ι n).subtype fun γ : ι → ℕ => ∑ j, γ j = n

theorem notMem_multSet_of_notMem_degSet {n : ℕ} {γ : {γ : ι → ℕ // ∑ j, γ j = n}}
    (hγ : γ ∉ degSet ι n) : γ.1 ∉ multSet ι n :=
  fun h => hγ (Finset.mem_subtype.2 h)

theorem sum_degSet_eq (n : ℕ) (F : (ι → ℕ) → ℝ) :
    ∑ γ ∈ degSet ι n, F γ.1 = ∑ γ ∈ multSet ι n, F γ := by
  rw [degSet, Finset.sum_subtype_eq_sum_filter,
    Finset.filter_true_of_mem fun γ hγ => sum_eq_of_mem_multSet hγ]

/-- **ℓ¹ summability of the monomial family**: if `card ι · b < ρ < radius p` then
`∑_γ |monoFamily p γ| b^{|γ|} < ∞`. -/
theorem summable_monoFamily_mul_pow (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < p.radius) {b : ℝ} (hb : 0 ≤ b) (hbρ : (Fintype.card ι : ℝ) * b < ρ) :
    Summable fun γ : ι → ℕ => |monoFamily p γ| * b ^ (∑ j, γ j) := by
  set F : (ι → ℕ) → ℝ := fun γ => |monoFamily p γ| * b ^ (∑ j, γ j) with hF
  have hFnn : ∀ γ, 0 ≤ F γ := fun γ => by positivity
  rw [← (degreeEquiv ι).summable_iff]
  have hnn : ∀ x : Σ n : ℕ, {γ : ι → ℕ // ∑ j, γ j = n}, 0 ≤ (F ∘ degreeEquiv ι) x :=
    fun x => hFnn _
  rw [summable_sigma_of_nonneg hnn]
  -- the fibres are finite sums
  have hfib : ∀ n : ℕ, ∀ γ : {γ : ι → ℕ // ∑ j, γ j = n},
      (F ∘ degreeEquiv ι) ⟨n, γ⟩ = |monoCoeff p n γ.1| * b ^ n := by
    intro n γ
    simp only [Function.comp, degreeEquiv, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, hF, monoFamily]
    rw [γ.2]
  have hzero : ∀ n : ℕ, ∀ γ : {γ : ι → ℕ // ∑ j, γ j = n},
      γ ∉ degSet ι n → (F ∘ degreeEquiv ι) ⟨n, γ⟩ = 0 := by
    intro n γ hγ
    rw [hfib, monoCoeff_eq_zero_of_notMem p (notMem_multSet_of_notMem_degSet hγ), abs_zero,
      zero_mul]
  refine ⟨fun n => summable_of_ne_finset_zero (hzero n), ?_⟩
  -- the degree sums are dominated by a geometric series
  obtain ⟨C, hC, hpC⟩ := p.norm_mul_pow_le_of_lt_radius hρ
  have hρpos : (0 : ℝ) < ρ := lt_of_le_of_lt (by positivity) hbρ
  set q : ℝ := (Fintype.card ι : ℝ) * b / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hρpos).2 hbρ
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun γ => hnn ⟨n, γ⟩) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
  rw [tsum_eq_sum (hzero n)]
  calc ∑ γ ∈ degSet ι n, (F ∘ degreeEquiv ι) ⟨n, γ⟩
      = ∑ γ ∈ multSet ι n, |monoCoeff p n γ| * b ^ n := by
        rw [Finset.sum_congr rfl fun γ _ => hfib n γ]
        exact sum_degSet_eq n fun γ => |monoCoeff p n γ| * b ^ n
    _ = (∑ γ ∈ multSet ι n, |monoCoeff p n γ|) * b ^ n := by rw [Finset.sum_mul]
    _ ≤ (Fintype.card ι : ℝ) ^ n * ‖p n‖ * b ^ n :=
        mul_le_mul_of_nonneg_right (sum_abs_monoCoeff_le p n) (by positivity)
    _ = ‖p n‖ * (ρ : ℝ) ^ n * q ^ n := by
        rw [hq, div_pow, mul_pow]
        field_simp
    _ ≤ C * q ^ n := mul_le_mul_of_nonneg_right (hpC n) (by positivity)

/-- **Absolute convergence of the monomial series on the cube**: for `|u_j| ≤ b` with
`card ι · b < ρ < R`, `∑_γ monoFamily p γ · u^γ = f u`. -/
theorem hasSum_monoFamily_mul_mono {f : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 R) {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) {b : ℝ}
    (hb : 0 ≤ b) (hbρ : (Fintype.card ι : ℝ) * b < ρ) (hb1 : b < ρ) {u : ι → ℝ}
    (hu : ∀ j, |u j| ≤ b) :
    HasSum (fun γ : ι → ℕ => monoFamily p γ * ∏ j, u j ^ γ j) (f u) := by
  set F : (ι → ℕ) → ℝ := fun γ => monoFamily p γ * ∏ j, u j ^ γ j with hF
  -- absolute summability from the ℓ¹ bound
  have hsum : Summable F := by
    refine Summable.of_norm_bounded (summable_monoFamily_mul_pow p (hρ.trans_le hf.r_le) hb hbρ)
      fun γ => ?_
    rw [hF, Real.norm_eq_abs, abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun j _ => by positivity)
      fun j _ => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hu j) _
  -- the degree fibres
  have hfib : ∀ n : ℕ, HasSum (fun γ : {γ : ι → ℕ // ∑ j, γ j = n} => F γ.1) (p n fun _ => u) := by
    intro n
    have hzero : ∀ γ : {γ : ι → ℕ // ∑ j, γ j = n}, γ ∉ degSet ι n → F γ.1 = 0 := by
      intro γ hγ
      simp only [hF, monoFamily, γ.2]
      rw [monoCoeff_eq_zero_of_notMem p (notMem_multSet_of_notMem_degSet hγ), zero_mul]
    have h : HasSum (fun γ : {γ : ι → ℕ // ∑ j, γ j = n} => F γ.1) (∑ γ ∈ degSet ι n, F γ.1) :=
      hasSum_sum_of_ne_finset_zero hzero
    have heq : ∑ γ ∈ degSet ι n, F γ.1 = p n fun _ => u := by
      rw [sum_degSet_eq n F, ← sum_monoCoeff_mul_mono p n u]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [hF, monoFamily, sum_eq_of_mem_multSet hγ]
    rwa [heq] at h
  -- regroup along degrees
  have hsigma : HasSum (F ∘ degreeEquiv ι) (∑' γ, F γ) := by
    rw [← (degreeEquiv ι).tsum_eq F]
    exact ((degreeEquiv ι).summable_iff.2 hsum).hasSum
  have hdeg : HasSum (fun n => p n fun _ => u) (∑' γ, F γ) :=
    hsigma.sigma fun n => hfib n
  -- the power series converges to `f u`
  have hu' : u ∈ Metric.eball (0 : ι → ℝ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    have h1 : ‖u‖ ≤ b := (pi_norm_le_iff_of_nonneg hb).2 fun j => by
      rw [Real.norm_eq_abs]; exact hu j
    have h2 : (‖u‖₊ : ℝ≥0∞) < ρ := by
      rw [ENNReal.coe_lt_coe]
      exact lt_of_le_of_lt (show ‖u‖₊ ≤ ⟨b, hb⟩ from h1) hb1
    exact h2.trans hρ
  have hpow : HasSum (fun n => p n fun _ => u) (f u) := by
    have := hf.hasSum hu'
    rwa [zero_add] at this
  have hval : ∑' γ, F γ = f u := hdeg.unique hpow
  have := hsum.hasSum
  rwa [hval] at this

end General

/-! ### The data-space element of an analytic amplitude -/

variable {d : ℕ}

theorem absSummableAt_monoFamily (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < p.radius) {b : ℝ} (hb : 0 ≤ b) (hbρ : (d : ℝ) * b < ρ) :
    AbsSummableAt (monoFamily p) b := by
  unfold AbsSummableAt
  have := summable_monoFamily_mul_pow p hρ hb (by simpa using hbρ)
  exact this

/-- The data-space element of an analytic amplitude: zero phase family, amplitude family the
monomial coefficients of `p`. -/
noncomputable def amplitudeDatum {b : ℝ} (hb : 0 < b) (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : AbsSummableAt (monoFamily p) b) : DataSpace d :=
  ofFamilies b hb 0 (monoFamily p) (by simp [AbsSummableAt]) hp

theorem xiCoord_amplitudeDatum {b : ℝ} (hb : 0 < b) (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : AbsSummableAt (monoFamily p) b) : xiCoord (amplitudeDatum hb p hp) = 0 := by
  funext γ
  simp [xiCoord, amplitudeDatum, ofFamilies]

theorem toEta_amplitudeDatum {b : ℝ} (hb : 0 < b) (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ)
    (hp : AbsSummableAt (monoFamily p) b) : toEta b (amplitudeDatum hb p hp) = monoFamily p :=
  toEta_ofFamilies b hb 0 (monoFamily p) _ hp

/-- **The amplitude identity**: on the box `|u_j| ≤ b`, the data-space element of `p` evaluates to
the function `f` represented by `p` (`d · b < ρ < R`). -/
theorem evalF_toEta_amplitudeDatum {f : (Fin d → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ} {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 R)
    {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < R) {b : ℝ}
    (hb : 0 < b) (hbρ : (d : ℝ) * b < ρ) (hb1 : b < ρ) (hp : AbsSummableAt (monoFamily p) b)
    {u : Fin d → ℝ} (hu : ∀ j, |u j| ≤ b) :
    evalF (toEta b (amplitudeDatum hb p hp)) u = f u := by
  rw [toEta_amplitudeDatum]
  exact (hasSum_monoFamily_mul_mono hf hρ hb.le (by simpa using hbρ) hb1 hu).tsum_eq

end Grammar
