# Fidelity review v35 — units 299–301 (grammar §3 rewrite, Programme P per Astra #37; unit-12 review, work package P3)

Context: your #37 design and reviews v32–v34 (all PASS). Your v34 §5 named the P3 obligations: (A) an explicit zero-noise-to-zero-phase bridge with a generic condition `∀ v, xiCoord (x v) = 0`; (B) the tangential target `𝒞_{λ,m−1}(x) = ∫_K amplitudeCoeff(h,k,λ,β,η_v) dν(v)` by pointwise identification + integral congruence, with remainder control from the `TangentialData`/`gInt` machinery, not a pointwise-to-integrated inference; (C) the canonical `dataBoxCoeff` identification at `b = 1` as a Lean lemma checking `scale c 1 = c`, box prefactors `= 1`, no extra normalisation in `boxCoeff`; (D) assembly: sum coefficients first then select the leading pair, order by increasing exponent / decreasing log degree, require the assembled coefficient nonzero, permit cancellation, prove the exponential residual negligible. Units 299–301 implement A–D. Everything compiles (branch `tide/population-normal-form`, 292 modules, no `sorry`, no added `axiom`).

Frozen interfaces (beyond v32–v34):
```lean
abbrev DataSpace (d : ℕ) : Type := lp (fun _ : (Fin d → ℕ) ⊕ (Fin d → ℕ) => ℝ) 1
def xiCoord (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inl γ)
def etaCoord (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inr γ)
noncomputable def toXi (b : ℝ) (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inl γ) / b ^ (∑ i, γ i)   -- toEta likewise with Sum.inr
theorem absSummable_etaCoord (x : DataSpace d) : AbsSummable (etaCoord x)
noncomputable def dataBoxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1)) (μ : ℝ) (j : ℕ) : ℝ := boxCoeff n h k β b (toXi b x) (toEta b x) μ j
noncomputable def dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ) (x : DataSpace (n + 1)) : ℝ := familyPhaseIntegralBox n h k β N b (toXi b x) (toEta b x)
noncomputable def boxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) * ∑ q ∈ Finset.Ico j (n + 1), familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ q * (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j)
noncomputable def familyPhaseIntegralBox (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ) (cξ cη : CoeffFamily (n + 1)) : ℝ :=
  ∫ u in piBox (n + 1) (Ioc 0 b), evalF cη u * (∏ i, u i ^ h i) * Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)
noncomputable def evalF (c : CoeffFamily d) (u : Fin d → ℝ) : ℝ := ∑' γ, c γ * mono γ u
theorem continuousOn_evalF {c : CoeffFamily d} (hc : AbsSummable c) : ContinuousOn (evalF c) (closedCube d)
def AbsSummableAt (c : CoeffFamily d) (b : ℝ) : Prop := Summable fun γ => |c γ| * b ^ (∑ i, γ i)
theorem thm_TaylorTree_coeffFamily (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummableAt cξ b) (hη : AbsSummableAt cη b) : ∃ C : ℝ → ℕ → ℝ, TaylorTreeConclusion n h k β b cξ cη C
theorem dataBoxCoeff_eq_zero_of_lt (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1)) (μ : ℝ) {j : ℕ} (hj : n < j) : dataBoxCoeff n h k β b x μ j = 0
theorem dataBoxCoeff_eq_zero_of_not_candidate (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) {μ : ℝ} (hμ : ¬ candidateExp h k μ) (j : ℕ) : dataBoxCoeff n h k β b x μ j = 0
-- tangential (K compact T2, OpensMeasurableSpace, ν finite):
abbrev TangentialData (K) (d : ℕ) := C(K, DataSpace d)
noncomputable def tanIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ) (x : TangentialData K (n + 1)) : ℝ := ∫ v, dataBoxIntegral n h k β N b (x v) ∂ν
noncomputable def tanCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) : ℝ := ∫ v, dataBoxCoeff n h k β b (x v) μ j ∂ν
noncomputable def tanPredSum … (x) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := ∑ p ∈ predSet n (latticeQ k) μ j, tanCoeff ν n h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)
noncomputable def tanRemainder … (x) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := (tanIntegral ν n h k β N b x - tanPredSum ν n h k β b x μ j N) / (N ^ (-μ) * Real.log N ^ j)
theorem tendstoUniformlyOn_tanRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => tanRemainder ν n h k β b x μ j N) (fun x => tanCoeff ν n h k β b x μ j) atTop (Metric.closedBall 0 R)
theorem integrable_dataBoxCoeff_tan … (x : TangentialData K (n + 1)) (μ : ℝ) (j : ℕ) : Integrable (fun v => dataBoxCoeff n h k β b (x v) μ j) ν
def precedes (p q : ℝ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)
noncomputable def predSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) := (indexSet n Q (μ + 1)).filter fun p => precedes p (μ, j)
theorem mem_predSet_iff {n Q : ℕ} {μ : ℝ} {j : ℕ} {p : ℝ × ℕ} : p ∈ predSet n Q μ j ↔ p ∈ indexSet n Q (μ + 1) ∧ precedes p (μ, j)
-- assembly (M charts; K I compact T2 …; ν I finite; h k : (I : Fin M) → Fin (n I + 1) → ℕ; b : Fin M → ℝ):
def JointData (K) (n : Fin M → ℕ) := ∀ I, TangentialData (K I) (n I + 1);  def JointData.chart (x : JointData K n) (I : Fin M) := x I
def commonQ (k) : ℕ := ∏ I, latticeQ (k I);  def commonD (n : Fin M → ℕ) : ℕ := Finset.univ.sup n;  theorem latticeQ_dvd_commonQ (I) : latticeQ (k I) ∣ commonQ k;  theorem le_commonD (I) : n I ≤ commonD n
noncomputable def gInt (x : JointData K n) (N : ℝ) : ℝ := ∑ I, tanIntegral (ν I) (n I) (h I) (k I) β N (b I) (x.chart I)
noncomputable def gCoeff (x : JointData K n) (μ : ℝ) (j : ℕ) : ℝ := ∑ I, tanCoeff (ν I) (n I) (h I) (k I) β (b I) (x.chart I) μ j
noncomputable def absTerm (c : ℝ → ℕ → ℝ) (N : ℝ) (p : ℝ × ℕ) : ℝ := c p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)
noncomputable def absPredSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ := ∑ p ∈ predSet D Q μ j, absTerm c N p
theorem tendsto_normalForm_pop (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) (x : JointData K n) {μ₀ : ℝ} (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n) (Zpop E : ℝ → ℝ) (hdecomp : ∀ N, Zpop N = gInt ν h k β b x N + E N) (hE : Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0)) :
    Tendsto (fun N => (Zpop N - absPredSum (commonQ k) (commonD n) (gCoeff ν h k β b x) μ₀ j N) / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 (gCoeff ν h k β b x μ₀ j))
theorem isEquivalent_normalForm_pop … (hpred : ∀ N, absPredSum … = 0) (hc : gCoeff ν h k β b x μ₀ j ≠ 0) : Zpop ~[atTop] fun N => gCoeff ν h k β b x μ₀ j * (N ^ (-μ₀) * Real.log N ^ j)
theorem multCount_pos {d : ℕ} (ℓ : Fin d → ℝ) (l : ℝ) (hatt : ∃ i, ℓ i = l) : 0 < multCount ℓ l
theorem ratio_mem_lattice {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i : Fin d) (e : ℕ) : ∃ m : ℕ, 0 < m ∧ ((e : ℝ) + 1) / (2 * (k i : ℝ)) = (m : ℝ) / latticeQ k
```
From P1/P2 (reviewed): `population_leadingCoeff_of_conclusion` (any `TaylorTreeConclusion n h k β 1 cξ cη C` whose family integral equals `origPhaseIntegral … 1 0 η` with `η` continuous gives `C(λ, j) = 0` for `m−1 < j ≤ n` and `C(λ, m−1) = amplitudeCoeff h k λ β η`), `multCount_le_card`, `le_of_candidateExp`, `origPhaseIntegral`, `TaylorTreeConclusion.coeff_eq : C μ j = familySpectralCoeff n h k β (scale cξ b) (scale cη b) μ j`.

## The three units (complete files)

### Grammar/PopulationDataBridge.lean
```lean
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
def clampCube (u : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min 1 (u i))

theorem continuous_clampCube : Continuous (clampCube (d := d)) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

theorem clampCube_mem_closedCube (u : Fin d → ℝ) : clampCube u ∈ closedCube d := by
  refine Set.mem_univ_pi.2 fun i => ⟨le_max_left _ _, ?_⟩
  simp only [clampCube]
  exact max_le zero_le_one (min_le_left _ _)

theorem clampCube_eq_of_mem {u : Fin d → ℝ} (hu : u ∈ closedCube d) : clampCube u = u := by
  funext i
  have hi := Set.mem_univ_pi.1 hu i
  simp only [clampCube]
  rw [min_eq_right hi.2, max_eq_right hi.1]

/-- The represented amplitude of a datum, extended continuously by clamping. -/
noncomputable def dataAmplitude (x : DataSpace d) (u : Fin d → ℝ) : ℝ :=
  evalF (etaCoord x) (clampCube u)

theorem continuous_dataAmplitude (x : DataSpace d) : Continuous (dataAmplitude x) :=
  (continuousOn_evalF (absSummable_etaCoord x)).comp_continuous continuous_clampCube
    clampCube_mem_closedCube

theorem dataAmplitude_eq_of_mem (x : DataSpace d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataAmplitude x u = evalF (etaCoord x) u := by
  unfold dataAmplitude
  rw [clampCube_eq_of_mem hu]

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
```

### Grammar/PopulationTangential.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationDataBridge
import Grammar.TangentialRemainder

/-!
# Tangential integration of the first-candidate term (Astra #37 P3, unit 300)

One stratum, population data: `x : C(K, DataSpace (n+1))` with zero noise (`xiCoord (x v) = 0`
for every tangential point `v`; `K` compact, `ν` a finite measure carrying the tangential density
and cutoff exactly once), unit normal box. The integrated coefficients `𝒞_{μ,j}(x) = ∫_K
dataBoxCoeff (x v) μ j dν` inherit the pointwise facts of unit 299:

* `𝒞_{μ,j}(x) = 0` for `μ < λ` and for `μ = λ`, `j > m − 1` (`tanCoeff_eq_zero_of_lt_min`,
  `tanCoeff_population_eq_zero_of_gt`);
* `𝒞_{λ,m−1}(x) = ∫_K amplitudeCoeff h k λ β (η_v) dν(v)` — the paper's stratum integral of the
  face functional against the tangential measure (`tanCoeff_population_leading`; integral
  congruence, no interchange of the normal and tangential integrals is needed).

Hence the integrated predecessor sum at the target `(λ, m−1)` vanishes identically
(`tanPredSum_population_eq_zero`), and the **uniform-on-balls ordered-remainder theorem of
Programme S** (`tendstoUniformlyOn_tanRemainder`, the integrated `lemma:AsymInt`) gives
```
𝒵(N; x) / (N^{-λ} (log N)^{m−1}) → ∫_K amplitudeCoeff h k λ β (η_v) dν(v)
```
(`tanIntegral_population_tendsto`), with asymptotic equivalence when the integrated face
functional is nonzero and positivity when the pointwise face functionals are positive and `ν ≠ 0`.
This is Theorem A(c) for one stratum with tangential integration; the remainder control is the
Programme S majorant, not a pointwise-to-integrated inference. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [OpensMeasurableSpace K]
variable (ν : Measure K) [IsFiniteMeasure ν]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- Integrated coefficients vanish below the minimal ratio (any data, any box). -/
theorem tanCoeff_eq_zero_of_lt_min (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (x : TangentialData K (n + 1)) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) {μ : ℝ} (hμ : μ < l) (j : ℕ) :
    tanCoeff ν n h k β b x μ j = 0 := by
  unfold tanCoeff
  simp [dataBoxCoeff_eq_zero_of_lt_min n h k hk β hβ hb _ hmin hμ]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- Zero-noise integrated coefficients at `λ` vanish above log degree `m − 1`. -/
theorem tanCoeff_population_eq_zero_of_gt (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) {j : ℕ}
    (hj : multCount (ratioExp h k) l - 1 < j) : tanCoeff ν n h k β 1 x l j = 0 := by
  unfold tanCoeff
  simp [fun v => (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).1 j hj]

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- **The integrated first-candidate coefficient is the stratum integral of the face
functional.** -/
theorem tanCoeff_population_leading (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    tanCoeff ν n h k β 1 x l (multCount (ratioExp h k) l - 1) =
      ∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν := by
  unfold tanCoeff
  congr 1
  funext v
  exact (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).2

omit [CompactSpace K] [T2Space K] [OpensMeasurableSpace K] [IsFiniteMeasure ν] in
/-- The integrated predecessor sum at the first candidate vanishes identically. -/
theorem tanPredSum_population_eq_zero (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) (N : ℝ) :
    tanPredSum ν n h k β 1 x l (multCount (ratioExp h k) l - 1) N = 0 := by
  unfold tanPredSum
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨-, hprec⟩ := mem_predSet_iff.1 hp
  rcases hprec with hlt | ⟨heq, hgt⟩
  · rw [tanCoeff_eq_zero_of_lt_min ν n h k hk β hβ one_pos x hmin hlt, zero_mul]
  · have heq' : p.1 = l := heq
    rw [heq', tanCoeff_population_eq_zero_of_gt ν n h k hk β hβ x hx hmin hatt hgt, zero_mul]

/-- **Theorem A(c) with tangential integration**: for zero-noise tangential data the integrated
population integral, normalised by the first-candidate scale, converges to the stratum integral
of the face functional. -/
theorem tanIntegral_population_tendsto (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => tanIntegral ν n h k β N 1 x /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1))) atTop
      (𝓝 (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν)) := by
  have hμ : ∃ m : ℕ, l = (m : ℝ) / latticeQ k := by
    obtain ⟨i, hi⟩ := hatt
    obtain ⟨m, -, hm⟩ := ratio_mem_lattice k hk i (h i)
    exact ⟨m, by rw [← hi]; exact hm⟩
  have hj : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  have hxmem : x ∈ Metric.closedBall (0 : TangentialData K (n + 1)) ‖x‖ :=
    Metric.mem_closedBall.2 (by rw [dist_zero_right])
  have hT := (tendstoUniformlyOn_tanRemainder ν n h k hk β hβ one_pos hμ hj ‖x‖).tendsto_at hxmem
  rw [tanCoeff_population_leading ν n h k hk β hβ x hx hmin hatt] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  unfold tanRemainder
  rw [tanPredSum_population_eq_zero ν n h k hk β hβ x hx hmin hatt, sub_zero]

/-- Asymptotic equivalence when the integrated face functional is nonzero. -/
theorem tanIntegral_population_isEquivalent (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν) ≠ 0) :
    (fun N => tanIntegral ν n h k β N 1 x) ~[atTop]
      fun N => (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν) *
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) := by
  have hT := (tanIntegral_population_tendsto ν n h k hk β hβ x hx hmin hatt).div_const
    (∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν)
  rw [div_self hA] at hT
  refine isEquivalent_of_tendsto_one (hT.congr' (Eventually.of_forall fun N => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- Positivity of the integrated face functional when the pointwise face functionals are
positive and the tangential measure is nonzero. -/
theorem tanCoeff_population_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (x : TangentialData K (n + 1)) (hx : ∀ v, xiCoord (x v) = 0) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hpos : ∀ v, 0 < amplitudeCoeff h k l β (dataAmplitude (x v))) (hν : ν ≠ 0) :
    0 < ∫ v, amplitudeCoeff h k l β (dataAmplitude (x v)) ∂ν := by
  have hint : Integrable (fun v => amplitudeCoeff h k l β (dataAmplitude (x v))) ν := by
    have := integrable_dataBoxCoeff_tan ν n h k hk β hβ one_pos x l
      (multCount (ratioExp h k) l - 1)
    refine this.congr (Eventually.of_forall fun v => ?_)
    exact (dataBoxCoeff_population_leading n h k hk β hβ (x v) (hx v) hmin hatt).2
  rw [integral_pos_iff_support_of_nonneg (fun v => (hpos v).le) hint]
  have hsupp : Function.support (fun v => amplitudeCoeff h k l β (dataAmplitude (x v))) = univ :=
    Set.eq_univ_of_forall fun v => (hpos v).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.2 hν

end Grammar
```

### Grammar/PopulationAssembly.lean
```lean
/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PopulationTangential
import Grammar.ClosingCorollaries

/-!
# Finite chart assembly of the population expansion (Astra #37 Theorem A(d), unit 301)

Finitely many normal-form charts `I : Fin M`, each with compact tangential space `K I`, finite
measure `ν I`, exponents `h I, k I`, unit normal box, and zero-noise tangential data
`x.chart I` (`xiCoord (x.chart I v) = 0`). Write `λ_I` for the minimal ratio of chart `I`, `m_I`
for its multiplicity, `A_I = ∫_{K_I} amplitudeCoeff (h I) (k I) λ_I β (η_{I,v}) dν_I(v)` for its
integrated face functional, and
```
μ_* = min_I λ_I,      m_* = max {m_I : λ_I = μ_*},      A_* = ∑_{λ_I = μ_*, m_I = m_*} A_I.
```
(all supplied as hypotheses on a candidate `μ_*`, `m_*`, so no `Finset.min'` bookkeeping). Then

* the assembled coefficient at the global target is `A_*` (`gCoeff_population_leading`): charts with
  `λ_I > μ_*` contribute nothing at `μ_*` (below their first candidate), charts with `λ_I = μ_*` but
  `m_I < m_*` contribute nothing at log degree `m_* − 1` (above their `m_I − 1`);
* every predecessor of `(μ_*, m_* − 1)` has zero assembled coefficient
  (`absPredSum_population_eq_zero`), so the ordered remainder of Programme S is the normalised
  integral itself;
* for `𝒵_pop(N) = ∑_I 𝒵^I(N; x_I) + E(N)` with `E` negligible at the target scale,
  `𝒵_pop(N)/(N^{-μ_*}(log N)^{m_*−1}) → A_*` (`population_assembled_tendsto`, via the frozen
  `tendsto_normalForm_pop`), asymptotic equivalence when `A_* ≠ 0`
  (`population_assembled_isEquivalent`), and the exponentially small residual of the paper
  (`E(N) e^{εN} → 0`) is negligible at every power-log scale (`tendsto_target_of_exp`,
  `population_assembled_tendsto_exp`).

The decomposition `𝒵_pop = ∑_I 𝒵^I + E` is an external hypothesis (Steps 1–3 of §3.5 and the
analytic admissibility of the chart amplitudes); sums of face functionals may cancel across charts,
which is why `A_* ≠ 0` is a hypothesis of the equivalence. If `A_* = 0` the theorem asserts only the
zero limit at this scale; the true leading term must be sought among later ordered coefficients.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Asymptotics

namespace Grammar

open CoeffFamily

/-- **Exponentially small residuals are negligible at every power-log scale** (deterministic
form of `tendstoInMeasure_target_of_exp`). -/
theorem tendsto_target_of_exp (E : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) (μ₀ : ℝ) (j : ℕ) :
    Tendsto (fun N => E N / (N ^ (-μ₀) * Real.log N ^ j)) atTop (𝓝 0) := by
  have hdet : ∀ᶠ N : ℝ in atTop, 1 ≤ N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero μ₀ ε hε
    have h2 : ∀ᶠ N : ℝ in atTop, N ^ μ₀ * Real.exp (-ε * N) < 1 :=
      h1.eventually (gt_mem_nhds one_pos)
    filter_upwards [h2, eventually_ge_atTop (Real.exp 1)] with N hN1 hNe
    have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos 1) hNe
    have hlog1 : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
    have hlj : 1 ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hpos : 0 < N ^ μ₀ * Real.exp (-ε * N) := by positivity
    have hinv : 1 ≤ N ^ (-μ₀) * Real.exp (ε * N) := by
      have : N ^ (-μ₀) * Real.exp (ε * N) = (N ^ μ₀ * Real.exp (-ε * N))⁻¹ := by
        rw [Real.rpow_neg hN0.le, mul_inv, ← Real.exp_neg]
        congr 1; congr 1; ring
      rw [this]
      exact one_le_inv_iff₀.2 ⟨hpos, hN1.le⟩
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (N ^ (-μ₀) * Real.exp (ε * N)) * Real.log N ^ j :=
          mul_le_mul hinv hlj zero_le_one (by positivity)
      _ = _ := by ring
  refine squeeze_zero_norm' ?_ (tendsto_norm_zero.comp hE)
  filter_upwards [hdet] with N hN
  have hD : 0 < N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) := by linarith
  have hexp : 0 < Real.exp (ε * N) := Real.exp_pos _
  have hden : 0 < N ^ (-μ₀) * Real.log N ^ j := by
    by_contra hle
    rw [not_lt] at hle
    have : N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hexp.le
    linarith
  simp only [Function.comp, Real.norm_eq_abs, abs_div, abs_of_pos hden, abs_mul,
    abs_of_pos hexp]
  rw [div_le_iff₀ hden]
  calc |E N| = |E N| * 1 := (mul_one _).symm
    _ ≤ |E N| * (N ^ (-μ₀) * Real.log N ^ j * Real.exp (ε * N)) :=
        mul_le_mul_of_nonneg_left hN (abs_nonneg _)
    _ = |E N| * Real.exp (ε * N) * (N ^ (-μ₀) * Real.log N ^ j) := by ring

variable {M : ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)] [∀ I, CompactSpace (K I)]
  [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)] [∀ I, OpensMeasurableSpace (K I)]
  {n : Fin M → ℕ} (ν : (I : Fin M) → Measure (K I)) [∀ I, IsFiniteMeasure (ν I)]
  (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ)

/-- The integrated face functional of chart `I` at its own first candidate `λ_I`. -/
noncomputable def chartFace (x : JointData K n) (lam : Fin M → ℝ) (I : Fin M) : ℝ :=
  ∫ v, amplitudeCoeff (h I) (k I) (lam I) β (dataAmplitude (x.chart I v)) ∂(ν I)

/-- The assembled first-candidate coefficient `∑_{λ_I = μ_*, m_I = m_*} A_I`. -/
noncomputable def assembledFace (x : JointData K n) (lam : Fin M → ℝ) (μs : ℝ) (ms : ℕ) : ℝ :=
  ∑ I, if lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms then chartFace ν h k β x lam I
    else 0

/-- **The assembled coefficient at the global target is the assembled face functional.** -/
theorem gCoeff_population_leading (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) :
    gCoeff ν h k β (fun _ => 1) x μs (ms - 1) = assembledFace ν h k β x lam μs ms := by
  unfold gCoeff assembledFace
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · obtain ⟨hIμ, hIm⟩ := hI
    unfold chartFace
    rw [← hIμ, ← hIm]
    exact tanCoeff_population_leading (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I) (hx I)
      (hmin I) (hatt I)
  · by_cases hIμ : lam I = μs
    · have hlt : multCount (ratioExp (h I) (k I)) (lam I) < ms :=
        lt_of_le_of_ne (hm I hIμ) fun hE => hI ⟨hIμ, hE⟩
      have hpos := multCount_pos (ratioExp (h I) (k I)) (lam I) (hatt I)
      rw [← hIμ]
      exact tanCoeff_population_eq_zero_of_gt (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I)
        (hx I) (hmin I) (hatt I) (by omega)
    · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
        (hmin I) (lt_of_le_of_ne (hμ I) (Ne.symm hIμ)) _

/-- Every assembled coefficient at a predecessor of the global target vanishes. -/
theorem gCoeff_population_pred_eq_zero (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) {p : ℝ × ℕ}
    (hp : precedes p (μs, ms - 1)) : gCoeff ν h k β (fun _ => 1) x p.1 p.2 = 0 := by
  unfold gCoeff
  refine Finset.sum_eq_zero fun I _ => ?_
  rcases hp with hlt | ⟨heq, hgt⟩
  · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
      (hmin I) (lt_of_lt_of_le hlt (hμ I)) _
  · have heq' : p.1 = μs := heq
    have hgt' : ms - 1 < p.2 := hgt
    rw [heq']
    by_cases hIμ : lam I = μs
    · rw [← hIμ]
      exact tanCoeff_population_eq_zero_of_gt (ν I) (n I) (h I) (k I) (hk I) β hβ (x.chart I)
        (hx I) (hmin I) (hatt I) (by have := hm I hIμ; omega)
    · exact tanCoeff_eq_zero_of_lt_min (ν I) (n I) (h I) (k I) (hk I) β hβ one_pos (x.chart I)
        (hmin I) (lt_of_le_of_ne (hμ I) (Ne.symm hIμ)) _

/-- The assembled predecessor sum at the global target vanishes identically. -/
theorem absPredSum_population_eq_zero (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms) (N : ℝ) :
    absPredSum (commonQ k) (commonD n) (gCoeff ν h k β (fun _ => 1) x) μs (ms - 1) N = 0 := by
  unfold absPredSum
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨-, hprec⟩ := mem_predSet_iff.1 hp
  unfold absTerm
  rw [gCoeff_population_pred_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm hprec, zero_mul]

/-- The global first candidate lies on the common lattice. -/
theorem global_target_mem_lattice (hk : ∀ I i, 0 < k I i) (lam : Fin M → ℝ)
    (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I) {μs : ℝ} (hμatt : ∃ I, lam I = μs) :
    ∃ m : ℕ, μs = (m : ℝ) / commonQ k := by
  obtain ⟨I, hI⟩ := hμatt
  obtain ⟨i, hi⟩ := hatt I
  obtain ⟨m', -, hm'⟩ := ratio_mem_lattice (k I) (hk I) i (h I i)
  obtain ⟨c, hc⟩ := latticeQ_dvd_commonQ k I
  have hQ : (0 : ℝ) < latticeQ (k I) := by exact_mod_cast latticeQ_pos (k I) (hk I)
  have hcQ : (0 : ℝ) < commonQ k := by exact_mod_cast commonQ_pos k hk
  have hc0 : (0 : ℝ) < c := by
    have : (commonQ k : ℝ) = latticeQ (k I) * c := by exact_mod_cast hc
    nlinarith
  refine ⟨m' * c, ?_⟩
  rw [← hI, ← hi]
  unfold ratioExp
  rw [hm']
  push_cast
  rw [hc]
  push_cast
  field_simp

/-- The global multiplicity index is within the common degree. -/
theorem global_target_le_commonD (lam : Fin M → ℝ) {μs : ℝ} {ms : ℕ}
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) :
    ms - 1 ≤ commonD n := by
  obtain ⟨I, -, hI⟩ := hmatt
  have h1 := multCount_le_card (ratioExp (h I) (k I)) (lam I)
  have h2 := le_commonD (n := n) I
  omega

/-- **Theorem A(d): the assembled population expansion at the global first candidate.** For
`𝒵_pop(N) = ∑_I 𝒵^I(N; x_I) + E(N)` with `E` negligible at the scale `N^{-μ_*}(log N)^{m_*−1}`,
`𝒵_pop(N)/(N^{-μ_*}(log N)^{m_*−1}) → A_* = ∑_{λ_I = μ_*, m_I = m_*} A_I`. -/
theorem population_assembled_tendsto (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (x : JointData K n)
    (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0)) :
    Tendsto (fun N => Zpop N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (assembledFace ν h k β x lam μs ms)) := by
  have hT := tendsto_normalForm_pop ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
    (global_target_mem_lattice h k hk lam hatt hμatt) (global_target_le_commonD h k lam hmatt)
    Zpop E hdecomp hE
  rw [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  rw [absPredSum_population_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm, sub_zero]

/-- Asymptotic equivalence of the assembled population integral when `A_* ≠ 0`. -/
theorem population_assembled_isEquivalent (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N)
    (hE : Tendsto (fun N => E N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop (𝓝 0))
    (hA : assembledFace ν h k β x lam μs ms ≠ 0) :
    Zpop ~[atTop] fun N => assembledFace ν h k β x lam μs ms *
      (N ^ (-μs) * Real.log N ^ (ms - 1)) := by
  have := isEquivalent_normalForm_pop ν h k β (fun _ => 1) hk hβ (fun _ => one_pos) x
    (global_target_mem_lattice h k hk lam hatt hμatt) (global_target_le_commonD h k lam hmatt)
    Zpop E hdecomp hE (absPredSum_population_eq_zero ν h k β hk hβ x hx lam hmin hatt hμ hm)
    (by rwa [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm])
  rwa [gCoeff_population_leading ν h k β hk hβ x hx lam hmin hatt hμ hm] at this

/-- **Theorem A(d) with the paper's exponentially small residual** `E(N) e^{εN} → 0`. -/
theorem population_assembled_tendsto_exp (hk : ∀ I i, 0 < k I i) (hβ : 0 < β)
    (x : JointData K n) (hx : ∀ I v, xiCoord (x.chart I v) = 0) (lam : Fin M → ℝ)
    (hmin : ∀ I i, lam I ≤ ratioExp (h I) (k I) i) (hatt : ∀ I, ∃ i, ratioExp (h I) (k I) i = lam I)
    {μs : ℝ} (hμ : ∀ I, μs ≤ lam I) (hμatt : ∃ I, lam I = μs) {ms : ℕ}
    (hm : ∀ I, lam I = μs → multCount (ratioExp (h I) (k I)) (lam I) ≤ ms)
    (hmatt : ∃ I, lam I = μs ∧ multCount (ratioExp (h I) (k I)) (lam I) = ms) (Zpop E : ℝ → ℝ)
    (hdecomp : ∀ N, Zpop N = gInt ν h k β (fun _ => 1) x N + E N) {ε : ℝ} (hε : 0 < ε)
    (hE : Tendsto (fun N => E N * Real.exp (ε * N)) atTop (𝓝 0)) :
    Tendsto (fun N => Zpop N / (N ^ (-μs) * Real.log N ^ (ms - 1))) atTop
      (𝓝 (assembledFace ν h k β x lam μs ms)) :=
  population_assembled_tendsto ν h k β hk hβ x hx lam hmin hatt hμ hμatt hm hmatt Zpop E hdecomp
    (tendsto_target_of_exp E hε hE μs (ms - 1))

end Grammar
```

## Questions
1. u299: is the zero-noise bridge honest and complete — `xiCoord x = 0` ⇒ the represented integral is the population integral of `dataAmplitude x` (the amplitude `evalF (etaCoord x)` clamped to the closed cube; it agrees with the true amplitude on the closed cube, which is all the box integral and the face functional see)? Is `boxCoeff_one` right (`j ≤ n`; prefactors `1`, `log 1 = 0` kills `q ≠ j`) and is the identification `dataBoxCoeff … 1 x λ (m−1) = amplitudeCoeff h k λ β (dataAmplitude x)` a faithful canonical-coefficient bridge with no scaling/normalisation slip (`scale_one` used twice in `coeff_eq`)? Note this version needs NO holomorphic hypothesis — only `AbsSummable (etaCoord x)`, automatic for ℓ¹ data — is that legitimate given `thm_TaylorTree_coeffFamily`'s hypotheses?
2. u300: are the tangential statements the right Theorem A(c)-with-integration, and is the remainder control genuinely inherited from `tendstoUniformlyOn_tanRemainder` (uniform on the ball of radius `‖x‖`, evaluated at `x`) rather than inferred pointwise? Is `tanPredSum_population_eq_zero` complete for the ordering `precedes p (λ, m−1)` (`p.1 < λ` or `p.1 = λ ∧ m−1 < p.2`)? Is `tanCoeff_population_pos` the right positivity statement (pointwise positive face functionals, `ν ≠ 0`)?
3. u301: is the min-exponent/max-log rule correctly encoded by the hypothesis pattern (`hμ : ∀ I, μ* ≤ λ_I`, `hμatt`, `hm : ∀ I, λ_I = μ* → m_I ≤ m*`, `hmatt`), is `gCoeff_population_leading` correct (charts with `λ_I > μ*` contribute `0` at `μ*`; charts with `λ_I = μ*`, `m_I < m*` contribute `0` at log degree `m* − 1` — note the `omega` step uses `0 < m_I` from `multCount_pos`), are the predecessor vanishing, the common-lattice membership (`μ* = m'c/commonQ`) and the degree bound correct, and is Theorem A(d) faithfully rendered by `population_assembled_tendsto`/`_isEquivalent`/`_tendsto_exp` (conditional on the external decomposition `𝒵_pop = ∑_I 𝒵^I + E`, `A_* ≠ 0` a hypothesis, cross-chart cancellation permitted)? Is `tendsto_target_of_exp` (deterministic exponential-residual bridge) sound?
4. Non-claims to record for P3, and blocking/nonblocking fixes before P4 (Corollary B: leading quotient `E_n[φ] ∼ (C_φ/C) n^{-(μ−λ)}(log n)^{r−m}` with the three cases; bounded-observable inequality as a bridge lemma) and P5 (`φ = K`: `amplitudeCoeff (h+2k) k (λ+1) β ψ = (λ/β) amplitudeCoeff h k λ β ψ` and `N·E_N[K∘π] → λ/β` at chart level; assembled version with the same charts). For P4, how should the log exponent `r − m ∈ ℤ` be represented — as `Real.log N ^ (r−1) / Real.log N ^ (m−1)` (natural powers, quotient), as `zpow`, or as `Real.log N ^ ((r:ℝ) − m)` (rpow)? Prefer the form that composes with `IsEquivalent.div` and the existing natural-power statements.

Verdict per unit (PASS / qualified / FAIL), blocking fixes, nonblocking should-fixes. The files above are complete, not extractor output.
