/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.TiedCrossingInstance
import Grammar.OneDimExplicitCoefficients

/-!
# The logarithmic coefficient at the tied crossing: `√π/4 · P(0)` (CCCXV)

The regression test of consult #94 F for the logarithm: for the tied instance of CCCXIV,
`∫_{[0,b]²} P(x,y) e^{−n x²y²} dx dy`, the coordinate-free coefficient of `n^{−1/2} log n` is
`(√π/4)·P(0)`, the classical value (`∫_0^b∫_0^b e^{−n x²y²} = (√π/4) n^{−1/2} log n + O(n^{−1/2})`).

Through the kernels of CCCI–CCCII: the two-variable state-density representation is the basis
convolution of the one-variable one (`stateDensityRep_two`); for a **tied** monomial
(`γ_0 = γ_1`) it is the single term `((γ_0+1)/2, 1, 1)` with a logarithm, for an untied monomial
it has log degree `0` (`coeffAt_stateDensityRep_half_one`), so only `γ = 0` contributes at
`(1/2, 1)`; the monomial kernel is `√π/4` (`monoKernel_tied_half_one`), the box side cancels
(`boxSpectralKernel_tied_half_one`), hence

* ★★ `expansionCoefficient_log_tied`: the coordinate-free coefficient at `⟨1/2, 1⟩` equals
  `√π/4 · f_0 = √π/4 · P(0)`;
* ★★ `hasLeadingTerm_log_tied`: `∫_{[0,b]²} P e^{−nx²y²} / (n^{−1/2} log n) → √π/4 · P(0)` (the
  exponent-`0` coefficients vanish, and no admissible index has log degree `> 1`), so when
  `P(0) ≠ 0` the integral is asymptotically `(√π/4) P(0) n^{−1/2} log n`.

The logarithm is produced by the tied state density, exactly as in the paper's multiplicity
analysis, and it reaches the final formula through the strata/normal-tensor representation.
-/

open Set Filter Topology MeasureTheory Asymptotics

namespace Grammar

namespace TiedCrossing

open CoeffFamily MonoRep CoordModel

/-! ### The two-variable state density -/

theorem stateDensityRep_two (w : Fin 2 → ℝ) :
    stateDensityRep 1 w = PowLogRep.basisConv (w 0) (w 1 + 1, 0, 1) := by
  rw [stateDensityRep_succ 0 w, stateDensityRep_zero]
  unfold PowLogRep.conv
  rw [List.flatMap_singleton]
  rfl

theorem coeffAt_eq_zero_of_forall_deg_ne (c : PowLogRep) {j : ℕ} (hc : ∀ t ∈ c, t.2.1 ≠ j)
    (μ : ℝ) : PowLogRep.coeffAt c μ j = 0 := by
  induction c with
  | nil => rfl
  | cons t c ih =>
    rw [PowLogRep.coeffAt_cons, if_neg (fun h => hc t (List.mem_cons.2 (Or.inl rfl)) h.2),
      zero_add]
    exact ih fun s hs => hc s (List.mem_cons.2 (Or.inr hs))

theorem deg_zero_of_mem_shift_smul_gRep {α s r : ℝ} {t : ℝ × ℕ × ℝ}
    (ht : t ∈ PowLogRep.smul r (PowLogRep.shift s (gRep α 0))) : t.2.1 = 0 := by
  unfold PowLogRep.smul PowLogRep.shift at ht
  simp only [List.mem_map] at ht
  obtain ⟨t₁, ⟨t₂, ht₂, rfl⟩, rfl⟩ := ht
  rcases gRep_mem 0 t₂ ht₂ with ⟨_, h⟩ | ⟨_, h⟩
  · exact Nat.le_zero.1 h
  · exact h

theorem monoWeights_tied (γ : Fin 2 → ℕ) (i : Fin 2) :
    monoWeights (hh + γ) kk i + 1 = ((γ i : ℝ) + 1) / 2 := by
  unfold monoWeights hh kk
  simp only [Pi.add_apply, zero_add, Nat.cast_one, mul_one]
  ring

/-- **The tied state density at `(1/2, 1)`**: only the constant monomial carries the logarithm. -/
theorem coeffAt_stateDensityRep_half_one (γ : Fin 2 → ℕ) :
    PowLogRep.coeffAt (stateDensityRep 1 (monoWeights (hh + γ) kk)) (1 / 2) 1 =
      if γ = 0 then 1 else 0 := by
  rw [stateDensityRep_two]
  set w := monoWeights (hh + γ) kk with hw
  have hw0 : w 0 + 1 = ((γ 0 : ℝ) + 1) / 2 := monoWeights_tied γ 0
  have hw1 : w 1 + 1 = ((γ 1 : ℝ) + 1) / 2 := monoWeights_tied γ 1
  unfold PowLogRep.basisConv
  by_cases htied : w 1 + 1 = w 0 + 1
  · rw [if_pos htied]
    simp only
    rw [PowLogRep.coeffAt_cons, PowLogRep.coeffAt_nil, add_zero]
    have hγ : γ 0 = γ 1 := by
      rw [hw0, hw1] at htied
      exact_mod_cast (by linarith : (γ 0 : ℝ) = γ 1)
    by_cases h0 : γ = 0
    · subst h0
      rw [if_pos rfl, if_pos]
      · norm_num
      · rw [hw1]
        norm_num
    · rw [if_neg h0, if_neg]
      rintro ⟨h1, -⟩
      rw [hw1] at h1
      have : (γ 1 : ℝ) = 0 := by linarith
      apply h0
      funext i
      fin_cases i
      · simpa [hγ] using (by exact_mod_cast this : γ 1 = 0)
      · exact_mod_cast this
  · rw [if_neg htied]
    have h0 : γ ≠ 0 := by
      rintro rfl
      exact htied (by rw [hw0, hw1]; simp)
    rw [if_neg h0]
    exact coeffAt_eq_zero_of_forall_deg_ne _
      (fun t ht => by rw [deg_zero_of_mem_shift_smul_gRep ht]; exact zero_ne_one) _

/-! ### The kernels -/

theorem monoKernel_tied_half_one (γ : Fin 2 → ℕ) :
    monoKernel 1 hh kk 1 (1 / 2) 1 γ = if γ = 0 then Real.sqrt Real.pi / 4 else 0 := by
  unfold monoKernel
  rw [show Finset.Ico 1 (1 + 1) = {1} by decide, Finset.sum_singleton,
    coeffAt_stateDensityRep_half_one, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    OneDim.fluctMoment_one_zero (by norm_num), Real.Gamma_one_half_eq]
  have hprod : (∏ i : Fin (1 + 1), 1 / (2 * (kk i : ℝ))) = 1 / 4 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_one]
    unfold kk
    norm_num
  rw [hprod]
  split_ifs <;> ring

theorem boxSpectralKernel_tied_half_one {b : ℝ} (hb : 0 < b) (γ : Fin 2 → ℕ) :
    boxSpectralKernel 1 hh kk 1 b (1 / 2) 1 γ = if γ = 0 then Real.sqrt Real.pi / 4 else 0 := by
  unfold boxSpectralKernel
  have hsh : (∑ i : Fin (1 + 1), hh i) = 0 := by simp [hh]
  have hsk : (∑ i : Fin (1 + 1), kk i) = 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_one]
    rfl
  rw [hsh, hsk, show Finset.Ico 1 (1 + 1) = {1} by decide, Finset.sum_singleton,
    monoKernel_tied_half_one, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one,
    mul_one]
  by_cases h0 : γ = 0
  · subst h0
    rw [if_pos rfl]
    have hsγ : (∑ i : Fin (1 + 1), (0 : Fin 2 → ℕ) i) = 0 := by simp
    rw [hsγ, pow_zero, one_mul]
    have h1 : ((b ^ (2 * 2) : ℝ)) ^ (-(1 / 2 : ℝ)) = b ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      congr 1
      push_cast
      ring
    rw [h1, zero_add, ← Real.rpow_natCast b (1 + 1), ← Real.rpow_add hb]
    push_cast
    rw [show (2 : ℝ) + -2 = 0 by ring, Real.rpow_zero, one_mul]
  · rw [if_neg h0]
    ring

/-! ### The coefficient -/

variable (f : CoeffFamily 2) {supp : Finset (Fin 2 → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0) {b : ℝ}
  (hb : 0 < b)
include hf hb

theorem boxCoeff_tied_half_one :
    boxCoeff 1 hh kk 1 b 0 f (1 / 2) 1 = Real.sqrt Real.pi / 4 * f 0 := by
  rw [boxCoeff_zero_eq_tsum 1 _ _ 1 _ _ kk_pos one_pos hb (absSummableAt_of_finite_support f hf b)]
  rw [tsum_eq_single 0]
  · rw [boxSpectralKernel_tied_half_one hb, if_pos rfl]
    ring
  · intro γ hγ
    rw [boxSpectralKernel_tied_half_one hb, if_neg hγ, mul_zero]

theorem expansionCoefficient_eq_boxCoeff (μ : ℝ) (j : ℕ) :
    normalData.expansionCoefficient (certificate f hf b hb).stratumMeasure
        (coeffCertificate f hf b hb).field (polyD f) ⟨μ, j⟩ =
      boxCoeff 1 hh kk 1 b 0 f μ j := by
  rw [(coeffCertificate f hf b hb).expansionCoefficient_eq_gCoeff]
  unfold gCoeff
  have hM : Subsingleton (Fin (certificate f hf b hb).M) :=
    Fin.subsingleton_iff_le_one.2 (by change 1 ≤ 1; exact le_rfl)
  rw [Fintype.sum_subsingleton _ (⟨0, by change 0 < 1; exact one_pos⟩ :
    Fin (certificate f hf b hb).M)]
  change ∫ v, dataBoxCoeff 1 hh kk 1 b ((chart f hf b hb).x v) μ j ∂(Measure.dirac basePt) = _
  rw [integral_dirac]
  change dataBoxCoeff 1 hh kk 1 b (datum f hf b hb) μ j = _
  unfold dataBoxCoeff
  rw [toEta_datum, toXi_datum]

/-- ★★ **The logarithmic coefficient at the tied crossing**: the coordinate-free coefficient of
`n^{−1/2} log n` for `∫_{[0,b]²} P e^{−nx²y²}` is `√π/4 · P(0)`. -/
theorem expansionCoefficient_log_tied :
    normalData.expansionCoefficient (certificate f hf b hb).stratumMeasure
        (coeffCertificate f hf b hb).field (polyD f) ⟨1 / 2, 1⟩ =
      Real.sqrt Real.pi / 4 * f 0 := by
  rw [expansionCoefficient_eq_boxCoeff f hf hb, boxCoeff_tied_half_one f hf hb]

/-- The coefficients at the exponent `0` vanish (not a candidate exponent). -/
theorem expansionCoefficient_tied_zero (j : ℕ) :
    normalData.expansionCoefficient (certificate f hf b hb).stratumMeasure
        (coeffCertificate f hf b hb).field (polyD f) ⟨0, j⟩ = 0 := by
  rw [expansionCoefficient_eq_boxCoeff f hf hb,
    boxCoeff_zero_eq_tsum 1 _ _ 1 _ _ kk_pos one_pos hb (absSummableAt_of_finite_support f hf b)]
  have hK : ∀ γ, boxSpectralKernel 1 hh kk 1 b 0 j γ = 0 := by
    intro γ
    unfold boxSpectralKernel
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun q _ => ?_)
    rw [monoKernel_eq_zero_of_not_candidate 1 hh kk 1 0 q (fun hc =>
      absurd (candidateExp_pos kk_pos hc) (lt_irrefl 0)) γ]
    ring
  simp_rw [hK, mul_zero, tsum_zero]

/-- ★★ **The leading term `(√π/4) P(0) n^{−1/2} log n`** through the coordinate-free machinery. -/
theorem hasLeadingTerm_log_tied :
    HasLeadingTerm (globalLaplace (region b) phase fun w => polyD f w * 1)
      (Real.sqrt Real.pi / 4 * f 0) (1 / 2) 1 := by
  rw [← expansionCoefficient_log_tied f hf hb]
  refine ResolvedCertificate.CoefficientCertificate.hasLeadingTerm_expansionCoefficient
    (coeffCertificate f hf b hb) (measurable_phase 2 kk) measurable_const (fun _ => zero_le_one)
    (continuous_polyD f hf).measurable ⟨1 / 2, 1⟩ ?_ ?_
  · refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [commonQ_certificate]
      norm_num
    · rw [commonD_certificate]
  · intro q' hq' hpre
    obtain ⟨⟨m, hm⟩, hj⟩ := hq'
    rw [commonQ_certificate] at hm
    rw [commonD_certificate] at hj
    rcases hpre with hlt | ⟨heq, hgt⟩
    · change q'.exponent < 1 / 2 at hlt
      have hm0 : m = 0 := by
        rw [hm] at hlt
        have : (m : ℝ) < 1 := by
          push_cast at hlt
          linarith
        exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
      subst hm0
      have hq0 : q' = ⟨0, q'.logDegree⟩ := by
        cases q' with
        | mk e j => simp only at hm; rw [hm]; simp
      rw [hq0]
      exact expansionCoefficient_tied_zero f hf hb _
    · change 1 < q'.logDegree at hgt
      omega

/-- When `P(0) ≠ 0` the integral is asymptotically `(√π/4) P(0) n^{−1/2} log n`. -/
theorem isEquivalent_log_tied (hf0 : f 0 ≠ 0) :
    (globalLaplace (region b) phase fun w => polyD f w * 1) ~[atTop] fun N =>
      Real.sqrt Real.pi / 4 * f 0 * powLogScale (1 / 2) 1 N :=
  (hasLeadingTerm_log_tied f hf hb).isEquivalent (mul_ne_zero (by positivity) hf0)

end TiedCrossing

end Grammar
