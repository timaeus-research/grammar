# Fidelity review v33 — units 293–294 (grammar §3 rewrite, Programme P per Astra #37; unit-5 review)

Context as in review v32 (which you gave: u290–292 PASS ×3; route A–D for the leading-coefficient identification: isolate the exponent with `L = λ + 1/(2Q)` or similar, show the normalised remainder → 0, transfer Headline VIII's normalised limit to the polynomial `P(log N)/(log N)^r`, and apply a finite-polynomial growth uniqueness lemma). Units 293–294 implement exactly that route. Everything compiles (`timaeus-research/grammar`, branch `tide/population-normal-form`, 285 modules, no `sorry`, no added `axiom`). This completes work package P1 of Astra #37 (5 units, budget 5).

Frozen interfaces used (reviewed earlier):
```lean
-- Headline VIII (MonomialAmplitudeAsymptotic.lean):
noncomputable def ratioExp {d : ℕ} (h k : Fin d → ℕ) (i : Fin d) : ℝ := ((h i : ℝ) + 1) / (2 * (k i : ℝ))
noncomputable def multCount {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : ℕ := ∑ i, if ℓ i = l then 1 else 0
noncomputable def faceProj {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : Fin d → ℝ := fun i => if ratioExp h k i = l then 0 else u i
noncomputable def residualWeight {d : ℕ} (h k : Fin d → ℕ) (l : ℝ) (u : Fin d → ℝ) : ℝ := ∏ i, if ratioExp h k i = l then 1 else u i ^ ((h i : ℝ) - 2 * (k i : ℝ) * l)
noncomputable def faceLeadConst {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) : ℝ := Real.Gamma l * β ^ (-l) / ((multCount (ratioExp h k) l - 1).factorial : ℝ) * ∏ i, if ratioExp h k i = l then 1 / (2 * (k i : ℝ)) else 1
noncomputable def amplitudeCoeff {d : ℕ} (h k : Fin d → ℕ) (l β : ℝ) (η : (Fin d → ℝ) → ℝ) : ℝ := faceLeadConst h k l β * ∫ u in unitBox d, η (faceProj h k l u) * residualWeight h k l u
theorem amplitude_tendsto (d : ℕ) (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β : ℝ) (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (η : (Fin (d + 1) → ℝ) → ℝ) (hη : Continuous η) :
    Tendsto (fun N => (∫ x in unitBox (d + 1), η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i))))) / (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop (𝓝 (amplitudeCoeff h k l β η))
-- lattice (SpectralLattice.lean / StochasticTaylorTreeJoint.lean):
def latticeQ {d : ℕ} (k : Fin d → ℕ) : ℕ := 2 * ∏ i, k i
noncomputable def latticeBelow (Q : ℕ) (L : ℝ) : Finset ℝ := (Finset.range ⌈L * Q⌉₊).image fun m : ℕ => (m : ℝ) / Q
theorem mem_latticeBelow {Q : ℕ} (hQ : 0 < Q) {L : ℝ} {m : ℕ} (hm : (m : ℝ) / Q < L) : (m : ℝ) / Q ∈ latticeBelow Q L
theorem mem_latticeBelow_iff {Q : ℕ} (hQ : 0 < Q) {L ν : ℝ} : ν ∈ latticeBelow Q L ↔ (∃ m : ℕ, ν = (m : ℝ) / Q) ∧ ν < L
theorem ratio_mem_lattice {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) (e : ℕ) : ∃ m : ℕ, 0 < m ∧ ((e : ℝ) + 1) / (2 * (k i : ℝ)) = (m : ℝ) / latticeQ k
def candidateExp {d : ℕ} (h k : Fin d → ℕ) (μ : ℝ) : Prop := ∃ (i : Fin d) (r : ℕ), μ = ((h i : ℝ) + r + 1) / (2 * (k i : ℝ))
noncomputable def boxScale {d : ℕ} (k : Fin d → ℕ) (b N : ℝ) : ℝ := N * b ^ (2 * ∑ i, k i)
theorem tendsto_cutoff_ratio (n : ℕ) {L μ : ℝ} (hμL : μ < L) : Tendsto (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-μ)) atTop (𝓝 0)
-- TaylorTreeConclusion fields used: `vanish : ∀ μ j, ¬ candidateExp h k μ → C μ j = 0`;
-- `remainder : ∀ L, 0 < L → ∀ N, 0 ≤ N → 1 ≤ boxScale k b N → |familyPhaseIntegralBox n h k β N b cξ cη − b^(∑h+(n+1)) * ∑ μ ∈ latticeBelow (latticeQ k) L, boxScale k b N ^ (-μ) * ∑ j ∈ range (n+1), C μ j * log(boxScale k b N)^j| ≤ b^(…) * cutoffBound n k β L (scale cξ b 0) (mass (scale cη b)) (mass (scale cξ b)) * (boxScale k b N ^ (-L) * (1 + log (boxScale k b N))^n)`
-- origPhaseIntegral n h k β N b ξ η = ∫ u in piBox (n+1) (Ioc 0 b), η u * (∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * ξ u);  unitBox d = Set.pi univ fun _ => Ioc 0 1 = piBox d (Ioc 0 1) (rfl)
-- u290': population_TaylorTree_taylor' … (hR : 1 < R) … : ∃ C, TaylorTreeConclusion n h k β 1 0 (taylorFamily (n+1) Fη) C ∧ ∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n+1) Fη) = origPhaseIntegral n h k β N 1 (fun _ => 0) η
```

## The two units (complete files)

### Grammar/PopulationLeadingIsolation.lean
```lean
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
```

### Grammar/PopulationLeadingCoeff.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationLeadingIsolation
import Grammar.HeadlineAmplitude

/-!
# The first-candidate coefficient of the population expansion is the face functional
(grammar §3 rewrite, Astra #37 P1, unit 294)

For the population Taylor tree on the unit box (`ξ = 0`, `b = 1`) with a continuous amplitude
`η` admitting a holomorphic `Fη` on a polydisc of radius `R > 1` with `Re Fη = η` on the box, let
`λ = min_i (hᵢ+1)/(2kᵢ)` and `m = |{i : (hᵢ+1)/(2kᵢ) = λ}|`. Then the canonical Taylor-tree
coefficients at the exponent `λ` satisfy
```
C(λ, j) = 0  for m − 1 < j ≤ n,        C(λ, m − 1) = amplitudeCoeff h k λ β η,
```
where `amplitudeCoeff h k λ β η = Γ(λ)β^{-λ}/(m−1)! ∏_{i∈J} 1/(2kᵢ) ·
∫_{(0,1]^{n+1}} η(P_J u) ∏_{i∉J} uᵢ^{hᵢ−2kᵢλ} du` is the face-supported functional of Headline VIII
(`P_J` zeroes the minimal-ratio coordinates). This is the corrected form of the paper's
`eq:thm_leading_coeff` at chart level (Astra #37 Theorem A(c)): the coefficient lives on the
minimal-ratio face, and evaluation at the corner is the answer only when every ratio is minimal
(`amplitudeCoeff_equal`). No nonvanishing is asserted: `C(λ, m−1)` may be zero for a signed `η`.

Route (review v32 §5): the isolated cutoff expansion gives `𝒵(N) = N^{-λ} P(log N) + o(N^{-λ}
(log N)^{m−1})` with `P(x) = ∑_{j≤n} C(λ,j) x^j`; Headline VIII gives `𝒵(N)/(N^{-λ}(log N)^{m−1})
→ A`; hence `P(log N)/(log N)^{m−1} → A`, and polynomial growth uniqueness reads off the
coefficients. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

/-- The population integral on the unit box in the form of Headline VIII. -/
theorem origPhaseIntegral_population_one (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (η : (Fin (n + 1) → ℝ) → ℝ) :
    origPhaseIntegral n h k β N 1 (fun _ => 0) η =
      ∫ x in unitBox (n + 1),
        η x * ((∏ i, x i ^ h i) * Real.exp (-(β * N * ∏ i, x i ^ (2 * k i)))) := by
  unfold origPhaseIntegral
  have hset : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hset]
  congr 1
  funext u
  simp [mul_assoc]

/-- The multiplicity is at most the dimension. -/
theorem multCount_le_card {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) : multCount ℓ l ≤ d := by
  unfold multCount
  calc (∑ i, if ℓ i = l then 1 else 0) ≤ ∑ _i : Fin d, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = d := by simp

/-- **Identification of the first-candidate coefficient** for any coefficient system satisfying
the Taylor-tree conclusion on the unit box whose family integral is the population integral of a
continuous amplitude: the coefficients at `λ` vanish above log degree `m − 1`, and the coefficient
at `(λ, m − 1)` is the face functional of Headline VIII. -/
theorem population_leadingCoeff_of_conclusion (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} {C : ℝ → ℕ → ℝ}
    (hC : TaylorTreeConclusion n h k β 1 cξ cη C) {η : (Fin (n + 1) → ℝ) → ℝ}
    (hηc : Continuous η)
    (hI : ∀ N, familyPhaseIntegralBox n h k β N 1 cξ cη =
      origPhaseIntegral n h k β N 1 (fun _ => 0) η)
    {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η := by
  set m := multCount (ratioExp h k) l with hm
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- Headline VIII: the normalised integral converges to the face functional
  have hA : Tendsto (fun N => origPhaseIntegral n h k β N 1 (fun _ => 0) η /
      (N ^ (-l) * Real.log N ^ (m - 1))) atTop (𝓝 (amplitudeCoeff h k l β η)) := by
    have := amplitude_tendsto n h k hk l β hl0 hβ hmin hatt η hηc
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [origPhaseIntegral_population_one, hm]
  -- the isolated remainder tends to zero
  have hR := population_remainder_tendsto n h k hk β hC hmin hatt
  -- hence the normalised polynomial tends to the face functional
  have hP : Tendsto (fun N => (∑ j ∈ Finset.range (n + 1), C l j * Real.log N ^ j) /
      Real.log N ^ (m - 1)) atTop (𝓝 (amplitudeCoeff h k l β η)) := by
    have hsub := hA.sub hR
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    rw [← hI N, ← sub_div, sub_sub_cancel, mul_div_mul_left _ _ hpow]
  have hm_le : m - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  obtain ⟨hzero, hlead, -⟩ := coeff_eq_of_tendsto_div_pow (a := fun j => C l j)
    Real.tendsto_log_atTop hP
  exact ⟨hzero, hlead hm_le⟩

/-- **Headline (P1): the leading population coefficient is the face functional.** For a
continuous amplitude `η` on `(0,1]^{n+1}` with a holomorphic `Fη` on the polydisc of radius
`R > 1`, `Re Fη = η` on the box: there is a coefficient system `C` with the full Taylor-tree
conclusion for the population integral `∫ η u^h e^{-βN u^{2k}}`, whose coefficients at the
minimal ratio `λ` vanish above log degree `m − 1` and whose `(λ, m − 1)` coefficient is
`Γ(λ)β^{-λ}/(m−1)! ∏_{J} 1/(2kᵢ) ∫ η(P_J u) ∏_{∉J} uᵢ^{hᵢ−2kᵢλ} du`. -/
theorem population_leadingCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {R : ℝ} (hR : 1 < R) {Fη : (Fin (n + 1) → ℂ) → ℂ}
    {η : (Fin (n + 1) → ℝ) → ℝ} (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 1), (Fη fun i => (u i : ℂ)).re = η u)
    (hηc : Continuous η) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i)
    (hatt : ∃ i, ratioExp h k i = l) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β 1 0 (taylorFamily (n + 1) Fη) C ∧
      (∀ N, familyPhaseIntegralBox n h k β N 1 0 (taylorFamily (n + 1) Fη) =
        origPhaseIntegral n h k β N 1 (fun _ => 0) η) ∧
      (∀ j ∈ Finset.range (n + 1), multCount (ratioExp h k) l - 1 < j → C l j = 0) ∧
      C l (multCount (ratioExp h k) l - 1) = amplitudeCoeff h k l β η := by
  obtain ⟨C, hC, hI⟩ := population_TaylorTree_taylor' n h k hk β hβ one_pos hR hFη hη
  obtain ⟨hzero, hlead⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC hηc hI hmin hatt
  exact ⟨C, hC, hI, hzero, hlead⟩

end Grammar
```

## Questions
1. `coeff_eq_of_tendsto_div_pow`: is the statement the right reusable uniqueness lemma (your §5 D), and is the proof through Mathlib's `Polynomial` asymptotics sound (degree > r contradiction via `abs_div_tendsto_atTop_atTop_of_degree_gt`; degree = r via the leading-coefficient quotient; degree < r via the zero limit)?
2. `spectralSum_isolated`: the cutoff is `L = λ + 1/Q` with `Q = 2∏kᵢ` (not `λ + 1/(2Q)`): is the gap argument (candidates and `λ` lie in `Q⁻¹ℕ`, so a candidate `> λ` is `≥ λ + 1/Q`, hence not `< L`) complete, including the use of `vanish` for non-candidates and the sub-`λ` elimination (candidates are `≥ λ` by `le_of_candidateExp`)?
3. `population_remainder_tendsto`: correct handling of `b = 1` (`boxScale_one`, `one_pow`), the sign-free constant (`|K|`), the threshold `N ≥ e` for `(log N)^{m−1} ≥ 1`, and the squeeze via `tendsto_cutoff_ratio`?
4. `population_leadingCoeff_of_conclusion` / `population_leadingCoeff`: is the identification `C(λ, m−1) = amplitudeCoeff h k λ β η` and `C(λ, j) = 0` for `m−1 < j ≤ n` faithful to your Theorem A(c) at chart level, `b = 1`, tangential integration aside? Are the hypotheses honest (`Continuous η` on all of `ℝ^{n+1}` is used for Headline VIII — a mild extra hypothesis beyond real-part agreement on the box; the theorem asserts nothing about nonvanishing)? Is `m − 1 ≤ n` (from `multCount ≤ n+1`) correctly used to read off the `(λ, m−1)` coefficient?
5. Non-claims to record, and any blocking/nonblocking fixes before P2 (monomial shift `η = u^l ψ` by re-presenting the integral, shifted support on `Λ(h+l,k)`, shifted min/multiplicity, face limit for `ψ`, positivity criterion for `amplitudeCoeff` from `ψ ≥ 0` on the face and `> 0` at a point — via `faceLeadConst_pos` and a positive set integral of a nonnegative continuous integrand)? Anything in the planned P2 statements you would change? Should `amplitudeCoeff` at `b ≠ 1` be handled now (the box rescaling `Z_b(N) = b^{|h|+d} Z_1(N b^{2|k|}; η(b·))` with binomial re-expansion of `log`) or left to P3/P5 as you said ("start at b = 1")?

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
