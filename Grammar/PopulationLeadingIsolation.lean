/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationTaylorTree
import Grammar.OrderedRemainder
import Grammar.StochasticTaylorTreeJoint
import Grammar.MonomialMixedAsymptotic
import Mathlib.Analysis.Polynomial.Basic

/-!
# Isolating the leading exponent of the population expansion (Astra #37 P1, unit 293)

Two tools for identifying the first-candidate coefficient of the population Taylor tree with the
face functional of Headline VIII (review v32 §5, route A–D):

* **Polynomial growth uniqueness** (`coeff_eq_of_tendsto_div_pow`): if a finite polynomial
  `P(x) = ∑_{j≤n} a_j x^j` satisfies `P(x(N))/x(N)^r → A` along `x(N) → ∞`, then `a_j = 0` for
  `r < j ≤ n` and `a_r = A` (with `A = 0` when `r > n`). Proof through Mathlib's polynomial
  asymptotics: a degree above `r` forces `|P/X^r| → ∞`; degree `r` gives the leading coefficient;
  degree below `r` gives `0`.
* **Isolation of the first candidate** (`spectralSum_isolated`): with `λ = min_i (hᵢ+1)/(2kᵢ)`
  and the cutoff `L = λ + 1/Q`, `Q = 2∏kᵢ`, the lattice `Q⁻¹ℕ ∩ [0,L)` contains no candidate
  exponent other than `λ` (candidates lie in `Q⁻¹ℕ` and are `≥ λ`, so a candidate `> λ` is
  `≥ λ + 1/Q`), and every coefficient vanishes off the candidate set; hence the spectral sum below
  `L` is the single term `N^{-λ} ∑_j C(λ,j)(log N)^j`.
* **Normalised remainder** (`population_remainder_tendsto`): for the population Taylor tree on the
  unit box (`b = 1`), `(𝒵(N) − N^{-λ} ∑_j C(λ,j)(log N)^j)/(N^{-λ}(log N)^{m−1}) → 0`, where
  `m = |{i : (hᵢ+1)/(2kᵢ) = λ}|`; the cutoff remainder is `O(N^{-L}(1+log N)^n)` with `L > λ`,
  and `(log N)^{m−1} ≥ 1` for `N ≥ e`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- **Polynomial growth uniqueness**: if `∑_{j≤n} a_j x(N)^j / x(N)^r → A` with `x(N) → ∞`, then
`a_j = 0` for `r < j ≤ n`, `a_r = A` when `r ≤ n`, and `A = 0` when `n < r`. -/
theorem coeff_eq_of_tendsto_div_pow {n r : ℕ} {a : ℕ → ℝ} {A : ℝ} {x : ℝ → ℝ}
    (hx : Tendsto x atTop atTop)
    (h : Tendsto (fun N => (∑ j ∈ Finset.range (n + 1), a j * x N ^ j) / x N ^ r) atTop (𝓝 A)) :
    (∀ j ∈ Finset.range (n + 1), r < j → a j = 0) ∧ (r ≤ n → a r = A) ∧ (n < r → A = 0) := by
  classical
  set P : Polynomial ℝ := ∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j
    with hP
  have hcoeff : ∀ j, P.coeff j = if j ∈ Finset.range (n + 1) then a j else 0 := by
    intro j
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq]
  have heval : ∀ y, P.eval y = ∑ j ∈ Finset.range (n + 1), a j * y ^ j := by
    intro y
    simp [hP, Polynomial.eval_finsetSum]
  have hQ : (Polynomial.X ^ r : Polynomial ℝ) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hQdeg : (Polynomial.X ^ r : Polynomial ℝ).degree = r := Polynomial.degree_X_pow r
  have h' : Tendsto (fun N => P.eval (x N) / (Polynomial.X ^ r : Polynomial ℝ).eval (x N)) atTop
      (𝓝 A) := by
    refine h.congr' (Eventually.of_forall fun N => ?_)
    simp [heval, Polynomial.eval_pow]
  have hdeg : P.degree ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt P (Polynomial.X ^ r)
      (by rwa [hQdeg]) hQ
    exact not_tendsto_atTop_of_tendsto_nhds h'.abs (h1.comp hx)
  have hA : A = P.coeff r := by
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · have h0 := Polynomial.div_tendsto_atTop_zero_of_degree_lt P (Polynomial.X ^ r)
        (by rwa [hQdeg])
      rw [tendsto_nhds_unique h' (h0.comp hx), Polynomial.coeff_eq_zero_of_degree_lt hlt]
    · have h1 := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P (Polynomial.X ^ r)
        (by rw [heq, hQdeg])
      rw [tendsto_nhds_unique h' (h1.comp hx), Polynomial.leadingCoeff_X_pow, div_one,
        ← Polynomial.coeff_natDegree, Polynomial.natDegree_eq_of_degree_eq_some heq]
  refine ⟨fun j hj hrj => ?_, fun hrn => ?_, fun hnr => ?_⟩
  · have hz : P.coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by exact_mod_cast hrj))
    rwa [hcoeff, if_pos hj] at hz
  · rw [hA, hcoeff, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hrn))]
  · rw [hA, hcoeff, if_neg]
    simp [Finset.mem_range]
    omega

/-- Every candidate exponent is at least the minimal ratio. -/
theorem le_of_candidateExp {d : ℕ} (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {l μ : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hμ : candidateExp h k μ) : l ≤ μ := by
  obtain ⟨i, r, rfl⟩ := hμ
  refine (hmin i).trans ?_
  unfold ratioExp
  have hk' : (0 : ℝ) < 2 * (k i : ℝ) := by
    have := hk i
    positivity
  apply div_le_div_of_nonneg_right _ hk'.le
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  linarith

/-- **Isolation of the first candidate**: below the cutoff `L = λ + 1/Q` the spectral sum of a
coefficient system supported on the candidate set is the single term at `λ`. -/
theorem spectralSum_isolated (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (C : ℝ → ℕ → ℝ)
    (hC : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0) (N : ℝ) :
    ∑ μ ∈ latticeBelow (latticeQ k) (l + 1 / latticeQ k),
        N ^ (-μ) * ∑ j ∈ Finset.range (n + 1), C μ j * Real.log N ^ j =
      N ^ (-l) * ∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨i₀, hi₀⟩ := hatt
  obtain ⟨m', -, hm'⟩ := ratio_mem_lattice k hk i₀ (h i₀)
  have hl : l = (m' : ℝ) / latticeQ k := by rw [← hi₀]; exact hm'
  rw [Finset.sum_eq_single l]
  · intro μ hμ hne
    obtain ⟨⟨m, hm⟩, hμL⟩ := (mem_latticeBelow_iff hQ).1 hμ
    have hzero : ∀ j ∈ Finset.range (n + 1), C μ j * Real.log N ^ j = 0 := by
      intro j _
      rw [hC μ j, zero_mul]
      intro hcand
      have hle : l ≤ μ := le_of_candidateExp h k hk hmin hcand
      have hlt : l < μ := lt_of_le_of_ne hle (Ne.symm hne)
      rw [hl, hm, div_lt_div_iff_of_pos_right hQ'] at hlt
      have hmm : (m' : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.cast_lt.1 hlt : m' < m)
      rw [hm, hl, ← add_div, div_lt_div_iff_of_pos_right hQ'] at hμL
      linarith
    rw [Finset.sum_eq_zero hzero, mul_zero]
  · intro hl'
    exfalso
    apply hl'
    rw [hl]
    refine mem_latticeBelow hQ ?_
    rw [← hl]
    have : (0 : ℝ) < 1 / latticeQ k := by positivity
    linarith

/-- On the unit box the box scale is the sample size. -/
theorem boxScale_one {d : ℕ} (k : Fin d → ℕ) (N : ℝ) : boxScale k 1 N = N := by
  simp [boxScale]

/-- **Normalised remainder of the population expansion on the unit box**: with `λ` the minimal
ratio and `m` its multiplicity, `(𝒵(N) − N^{-λ} ∑_j C(λ,j)(log N)^j)/(N^{-λ}(log N)^{m−1}) → 0`
for any coefficient system satisfying the Taylor-tree conclusion at `b = 1`. -/
theorem population_remainder_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => (familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j) /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop (𝓝 0) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < 1 / latticeQ k := by
    have : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
    positivity
  set L : ℝ := l + 1 / latticeQ k with hLdef
  have hlL : l < L := by rw [hLdef]; linarith
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hL : 0 < L := hl0.trans hlL
  set K : ℝ := cutoffBound n k β L (scale cξ 1 0) (mass (scale cη 1)) (mass (scale cξ 1)) with hK
  -- the cutoff estimate at `b = 1`, with the spectral sum isolated
  have hbound : ∀ N : ℝ, 1 ≤ N →
      |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j| ≤
        |K| * (N ^ (-L) * (1 + Real.log N) ^ n) := by
    intro N hN
    have hrem := hC.remainder L hL N (by linarith) (by rw [boxScale_one]; exact hN)
    rw [boxScale_one, one_pow, one_mul, one_mul,
      spectralSum_isolated n h k hk hmin hatt C hC.vanish N] at hrem
    refine hrem.trans (mul_le_mul_of_nonneg_right (le_abs_self K) ?_)
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
    positivity
  -- squeeze
  have hmaj : Tendsto (fun N : ℝ => |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l))) atTop
      (𝓝 0) := by
    simpa using (tendsto_cutoff_ratio n hlL).const_mul |K|
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with N hN
  have hN1 : 1 ≤ N := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hN
  have hNpos : 0 < N := by linarith
  have hpow : 0 < N ^ (-l) := Real.rpow_pos_of_pos hNpos _
  have hlogpow : 1 ≤ Real.log N ^ (multCount (ratioExp h k) l - 1) := one_le_pow₀ hlog
  have hden : 0 < N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1) :=
    mul_pos hpow (by linarith)
  have hX : 0 ≤ N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |familyPhaseIntegralBox n h k β N 1 cξ cη -
        N ^ (-l) * ∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j|
      ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n) := hbound N hN1
    _ = |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l)) * N ^ (-l) := by
        rw [mul_assoc, div_mul_cancel₀ _ hpow.ne']
    _ ≤ |K| * (N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-l)) *
          (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
        apply mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hpow.le hlogpow)
        positivity

end Grammar
