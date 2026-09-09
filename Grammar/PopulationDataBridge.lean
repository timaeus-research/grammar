/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationEquivalent
import Grammar.DataIntegralContinuity
import Grammar.ChartExpansion

/-!
# Zero-noise data and the canonical population coefficient (Astra #37 P3, unit 299)

The stochastic-data interface of Programme S represents a chart datum as
`x : DataSpace (n+1) = ℓ¹` with raw phase coordinates `xiCoord x` and amplitude coordinates
`etaCoord x`; its canonical coefficient of `N^{-μ}(log N)^j` is `dataBoxCoeff n h k β b x μ j`,
defined through `boxCoeff` of the box families. This file supplies the two bridges review v34
required before P3 can proceed:

* **zero noise means zero phase**: on the unit box the box families are the raw coordinates
  (`toXi_one`, `toEta_one`), so `xiCoord x = 0` makes the represented integral the population
  integral of the amplitude family (`dataBoxIntegral_population`);
* **canonical coefficient at `b = 1`**: `boxCoeff n h k β 1 cξ cη μ j = familySpectralCoeff n h k β
  cξ cη μ j` for `j ≤ n` (`boxCoeff_one`; the box prefactors are `1` and `log 1 = 0` kills every
  term of the binomial re-expansion except `q = j`), hence `dataBoxCoeff n h k β 1 x μ j` is the
  Taylor-tree coefficient of `(0, etaCoord x)` (`dataBoxCoeff_population`).

Combining with P1/P2: for zero-noise data the canonical coefficients vanish below `λ` and above
log degree `m − 1` at `λ`, and `dataBoxCoeff n h k β 1 x λ (m−1) = amplitudeCoeff h k λ β η_x`,
where `η_x = evalF (etaCoord x)` is the represented amplitude, extended continuously to `ℝ^{n+1}`
by clamping to the closed cube (`dataAmplitude`; it agrees with `evalF (etaCoord x)` on the closed
cube, which is all the face functional and the box integral see). No holomorphic hypothesis is
needed here: absolute summability of the amplitude family at the unit box radius is the
admissibility hypothesis of the coefficient-family Taylor tree (`thm_TaylorTree_coeffFamily`).
"Represented amplitude" means `evalF (etaCoord x)`: that an externally supplied chart amplitude is
represented by some `x` (admissibility) is a hypothesis on the data, not established here.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- Scaling by `1` is the identity on coefficient families. -/
theorem scale_one (c : CoeffFamily d) : scale c 1 = c := by
  funext γ
  simp [scale]

/-- Absolute summability at radius `1` is absolute summability. -/
theorem absSummableAt_one_iff (c : CoeffFamily d) : AbsSummableAt c 1 ↔ AbsSummable c := by
  unfold AbsSummableAt AbsSummable
  simp

/-- The zero family is absolutely summable at every radius. -/
theorem absSummableAt_zero (b : ℝ) : AbsSummableAt (0 : CoeffFamily d) b := by
  unfold AbsSummableAt
  simp

theorem toXi_one (x : DataSpace d) : toXi 1 x = xiCoord x := by
  funext γ
  simp [toXi, xiCoord]

theorem toEta_one (x : DataSpace d) : toEta 1 x = etaCoord x := by
  funext γ
  simp [toEta, etaCoord]

/-- The evaluation of the zero family is zero. -/
theorem evalF_zero (u : Fin d → ℝ) : evalF (0 : CoeffFamily d) u = 0 := by
  simp [evalF]

/-- Clamping to the closed cube. -/
def cubeClamp (u : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min 1 (u i))

theorem continuous_cubeClamp : Continuous (cubeClamp (d := d)) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

theorem cubeClamp_mem_closedCube (u : Fin d → ℝ) : cubeClamp u ∈ closedCube d := by
  refine Set.mem_univ_pi.2 fun i => ⟨le_max_left _ _, ?_⟩
  simp only [cubeClamp]
  exact max_le zero_le_one (min_le_left _ _)

theorem cubeClamp_eq_of_mem {u : Fin d → ℝ} (hu : u ∈ closedCube d) : cubeClamp u = u := by
  funext i
  have hi := Set.mem_univ_pi.1 hu i
  simp only [cubeClamp]
  rw [min_eq_right hi.2, max_eq_right hi.1]

/-- The represented amplitude of a datum, extended continuously by clamping. -/
noncomputable def dataAmplitude (x : DataSpace d) (u : Fin d → ℝ) : ℝ :=
  evalF (etaCoord x) (cubeClamp u)

theorem continuous_dataAmplitude (x : DataSpace d) : Continuous (dataAmplitude x) :=
  (continuousOn_evalF (absSummable_etaCoord x)).comp_continuous continuous_cubeClamp
    cubeClamp_mem_closedCube

theorem dataAmplitude_eq_of_mem (x : DataSpace d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataAmplitude x u = evalF (etaCoord x) u := by
  unfold dataAmplitude
  rw [cubeClamp_eq_of_mem hu]

/-- **Zero noise is zero phase**: for `xiCoord x = 0` the represented unit-box integral is the
population integral of the amplitude. -/
theorem dataBoxIntegral_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (x : DataSpace (n + 1)) (hx : xiCoord x = 0) :
    dataBoxIntegral n h k β N 1 x =
      origPhaseIntegral n h k β N 1 (fun _ => 0) (dataAmplitude x) := by
  unfold dataBoxIntegral origPhaseIntegral familyPhaseIntegralBox
  rw [toXi_one, toEta_one, hx]
  refine setIntegral_congr_fun (measurableSet_unitBox (n + 1)) fun u hu => ?_
  rw [dataAmplitude_eq_of_mem x (unitBox_subset_closedCube _ hu), evalF_zero]

/-- **The box coefficient at `b = 1` is the family spectral coefficient** (`j ≤ n`). -/
theorem boxCoeff_one (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1)) (μ : ℝ)
    {j : ℕ} (hj : j ≤ n) :
    boxCoeff n h k β 1 cξ cη μ j = familySpectralCoeff n h k β cξ cη μ j := by
  unfold boxCoeff
  simp only [one_pow, Real.one_rpow, one_mul, Real.log_one, scale_one]
  rw [Finset.sum_eq_single j]
  · simp
  · intro q hq hne
    have hlt : j < q := lt_of_le_of_ne (Finset.mem_Ico.1 hq).1 (Ne.symm hne)
    simp [Nat.sub_ne_zero_of_lt hlt]
  · intro hj'
    exact absurd (Finset.mem_Ico.2 ⟨le_rfl, Nat.lt_succ_of_le hj⟩) hj'

/-- **The canonical coefficient of zero-noise data** is the Taylor-tree coefficient of
`(0, etaCoord x)`. -/
theorem dataBoxCoeff_population (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (x : DataSpace (n + 1))
    (hx : xiCoord x = 0) (μ : ℝ) {j : ℕ} (hj : j ≤ n) :
    dataBoxCoeff n h k β 1 x μ j = familySpectralCoeff n h k β 0 (etaCoord x) μ j := by
  unfold dataBoxCoeff
  rw [toXi_one, toEta_one, hx, boxCoeff_one n h k β _ _ μ hj]

/-- Below the minimal ratio the canonical coefficients vanish (any data). -/
theorem dataBoxCoeff_eq_zero_of_lt_min (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {μ : ℝ} (hμ : μ < l) (j : ℕ) :
    dataBoxCoeff n h k β b x μ j = 0 :=
  dataBoxCoeff_eq_zero_of_not_candidate n h k hk β hβ hb x
    (fun hc => absurd (le_of_candidateExp h k hk hmin hc) (not_le.2 hμ)) j

/-- **The first-candidate canonical coefficient of zero-noise data is the face functional**:
for `xiCoord x = 0`, `λ` the minimal ratio with multiplicity `m`, `dataBoxCoeff … 1 x λ j = 0`
for every `j > m − 1`, and `dataBoxCoeff … 1 x λ (m−1) = amplitudeCoeff h k λ β (dataAmplitude x)`.
-/
theorem dataBoxCoeff_population_leading (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : DataSpace (n + 1)) (hx : xiCoord x = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    (∀ j, multCount (ratioExp h k) l - 1 < j → dataBoxCoeff n h k β 1 x l j = 0) ∧
      dataBoxCoeff n h k β 1 x l (multCount (ratioExp h k) l - 1) =
        amplitudeCoeff h k l β (dataAmplitude x) := by
  -- the coefficient-family Taylor tree for `(0, etaCoord x)` on the unit box
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    (absSummableAt_zero (d := n + 1) 1)
    ((absSummableAt_one_iff _).2 (absSummable_etaCoord x))
  have hI : ∀ N, familyPhaseIntegralBox n h k β N 1 0 (etaCoord x) =
      origPhaseIntegral n h k β N 1 (fun _ => 0) (dataAmplitude x) := by
    intro N
    rw [← dataBoxIntegral_population n h k β N x hx]
    unfold dataBoxIntegral
    rw [toXi_one, toEta_one, hx]
  obtain ⟨hzero, hlead⟩ := population_leadingCoeff_of_conclusion n h k hk β hβ hC
    (continuous_dataAmplitude x) hI hmin hatt
  have hCeq : ∀ μ j, j ≤ n → C μ j = dataBoxCoeff n h k β 1 x μ j := by
    intro μ j hj
    rw [hC.coeff_eq, scale_one, scale_one, dataBoxCoeff_population n h k β x hx μ hj]
  have hm_le : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases hjn : j ≤ n
    · rw [← hCeq l j hjn]
      exact hzero j (Finset.mem_range.2 (Nat.lt_succ_of_le hjn)) hj
    · exact dataBoxCoeff_eq_zero_of_lt n h k β 1 x l (not_le.1 hjn)
  · rw [← hCeq l _ hm_le, hlead]

end Grammar
