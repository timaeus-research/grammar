/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateResolvedGeometry
import Grammar.PolynomialTaylorFamily
import Grammar.OneDimCoordFreeInstance

/-!
# The tied normal crossing: `∫_{[0,b]²} P(x,y) e^{−n x² y²} dx dy` (CCCXIV)

Consult #94 F — the two-variable instance of the coordinate-free expansion at a **tied**
crossing: the phase `K = x² y²` vanishes on both coordinate axes with equal orders, so the
deepest stratum `S_{12} = {0}` has normal space `ℝ²`, the lattice is `½ℕ` and the log degree
bound is `1`: logarithms appear (`n^{−1/2} log n`), unlike the one-dimensional instance.

The square `[0,b]²` is taken inside the sublevel set `{x²y² < b⁴ + 1}`, so ONE chart at the tied
stratum presents the whole region: base the origin with the Dirac measure, normal box `(0,b]²`,
`Φ(s,u) = u`, `c = 1`, `h = (0,0)`, `k = (1,1)`, amplitude datum the coefficient family of `P`.

* `locData`, `partition`, `chart`, `presentation` (from `polySeriesD`), `certificate`,
  `coeffCertificate` (`jetFamily_polyD`);
* ★★ `hasCoordFreeExpansion_tied`: the coordinate-free expansion of `∫_{[0,b]²} P e^{−n x²y²}` with
  spectrum `spectrumLe 2 1 = {(α, j) : α ∈ ½ℕ, α ≤ A, j ≤ 1}` — the certified theorem holds at a
  tied crossing with logarithmic terms.

Non-claims: the explicit value of the `n^{−1/2} log n` coefficient (`√π/4 · P(0)`) is the next
unit; for a fixed polynomial only finitely many normal orders contribute (the infinite
normal-order phenomenon is about the family of all observables, consult #94).
-/

open Set Filter Topology MeasureTheory

namespace Grammar

namespace TiedCrossing

open CoeffFamily MonoRep CoordModel

/-- The orders: `k = (1,1)`. -/
def kk : Fin 2 → ℕ := fun _ => 1

/-- The Jacobian orders: `h = (0,0)`. -/
def hh : Fin 2 → ℕ := fun _ => 0

theorem kk_pos : ∀ i, 0 < kk i := fun _ => one_pos

/-- The geometry `ℝ²` with the two axes as components. -/
noncomputable abbrev geometry : ResolvedGeometry 2 (Fin 2 → ℝ) := CoordModel.geometry 2 kk hh kk_pos

/-- The normal data. -/
noncomputable abbrev normalData : ResolvedNormalData geometry (Amb 2) :=
  CoordModel.normalData 2 kk hh kk_pos

/-- The phase `x² y²`. -/
abbrev phase : (Fin 2 → ℝ) → ℝ := CoordModel.phase 2 kk

theorem phase_eq (w : Fin 2 → ℝ) : phase w = w 0 ^ 2 * w 1 ^ 2 := by
  unfold phase CoordModel.phase kk
  rw [Fin.prod_univ_two]

variable (f : CoeffFamily 2) {supp : Finset (Fin 2 → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0) (b : ℝ)
  (hb : 0 < b)

/-! ### The region and the localisation datum -/

/-- The square `W = [0,b]²`. -/
def region : Set (Fin 2 → ℝ) := piBox 2 (Icc 0 b)

omit hf hb in
theorem isCompact_region : IsCompact (region b) := isCompact_univ_pi fun _ => isCompact_Icc

omit hf hb in
theorem measurableSet_region : MeasurableSet (region b) := measurableSet_piBox 2 _ measurableSet_Icc

omit hf hb in
theorem mem_region {w : Fin 2 → ℝ} : w ∈ region b ↔ ∀ i, 0 ≤ w i ∧ w i ≤ b := by
  simp only [region, piBox, Set.mem_univ_pi, Set.mem_Icc]

include hf in
theorem continuous_polyD : Continuous (polyD f) := by
  have : polyD f = fun u => ∑ γ ∈ supp, f γ * mono γ u :=
    funext fun u => tsum_eq_sum fun γ hγ => by rw [hf γ hγ, zero_mul]
  rw [this]
  refine continuous_finsetSum _ fun γ _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

include hf hb in
/-- The localisation datum: Lebesgue measure on the square, phase `x²y²`, observable `P`, level
`b⁴ + 1` (so the whole square lies in the sublevel set). -/
noncomputable def locData : LocalisationData (Fin 2 → ℝ) where
  μ := volume.restrict (region b)
  phase := phase
  obs := polyD f
  phase_measurable := measurable_phase 2 kk
  phase_nonneg := Eventually.of_forall (phase_nonneg 2 kk)
  obs_integrable := (continuous_polyD f hf).continuousOn.integrableOn_compact (isCompact_region b)
  δ := b ^ 4 + 1
  δ_pos := by positivity

/-- The square lies in the sublevel set. -/
theorem region_subset_sublevel : region b ⊆ (locData f hf b hb).sublevel := by
  intro w hw
  rw [mem_region] at hw
  change phase w < b ^ 4 + 1
  rw [phase_eq]
  have h0 := hw 0
  have h1 := hw 1
  have : w 0 ^ 2 * w 1 ^ 2 ≤ b ^ 2 * b ^ 2 := by
    apply mul_le_mul <;> first | exact pow_le_pow_left₀ (by linarith) (by linarith) 2 | positivity
  nlinarith

/-- The one-piece partition. -/
noncomputable def partition : (locData f hf b hb).FiniteSublevelPartition (Fin 1) where
  ρ := fun _ _ => 1
  measurable_ρ := fun _ => measurable_const
  nonneg_ρ := fun _ => Eventually.of_forall fun _ => zero_le_one
  sum_eq_one := Eventually.of_forall fun _ => by simp

/-! ### The base and the null axes -/

/-- The base of the chart: the tied stratum point. -/
abbrev Base := ↥(Set.univ : Set (geometry.Stratum Finset.univ))

/-- The base point. -/
def basePt : Base := ⟨origin 2 kk hh kk_pos, trivial⟩

omit hf hb in
theorem volume_coord_eq_zero (i : Fin 2) (c : ℝ) : volume {w : Fin 2 → ℝ | w i = c} = 0 :=
  Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i c

omit hf hb in
/-- The closed square and the half-open box differ by the null axes. -/
theorem region_ae_eq_box : (region b : Set (Fin 2 → ℝ)) =ᵐ[volume] (piBox 2 (Ioc 0 b) : Set _) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun w hw => ?_)
      (measure_union_null (volume_coord_eq_zero 0 0) (volume_coord_eq_zero 1 0))
    obtain ⟨hin, hnot⟩ := hw
    rw [mem_region] at hin
    simp only [piBox, Set.mem_univ_pi, Set.mem_Ioc, not_forall, not_and, not_le] at hnot
    obtain ⟨i, hi⟩ := hnot
    have hi' : w i = 0 := by
      by_contra hne
      have hpos : 0 < w i := lt_of_le_of_ne (hin i).1 (Ne.symm hne)
      exact absurd (hi hpos) (not_lt.2 (hin i).2)
    fin_cases i
    · exact Or.inl hi'
    · exact Or.inr hi'
  · refine measure_mono_null (fun w hw => ?_) (measure_empty (μ := volume))
    obtain ⟨hin, hnot⟩ := hw
    simp only [piBox, Set.mem_univ_pi, Set.mem_Ioc] at hin
    exact hnot ((mem_region b).2 fun i => ⟨(hin i).1.le, (hin i).2⟩)

/-! ### The chart -/

include hf in
/-- The amplitude datum: the coefficient family `f`. -/
noncomputable def datum : DataSpace 2 :=
  ofFamilies b hb 0 f (summable_of_ne_finset_zero (s := ∅) fun _ _ => by simp)
    (absSummableAt_of_finite_support f hf b)

theorem toEta_datum : toEta b (datum f hf b hb) = f := toEta_ofFamilies _ _ _ _ _ _

theorem toXi_datum : toXi b (datum f hf b hb) = 0 := toXi_ofFamilies _ _ _ _ _ _

theorem xiCoord_datum : xiCoord (datum f hf b hb) = 0 := by
  funext γ
  have h := congrFun (toXi_datum f hf b hb) γ
  simp only [toXi, Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff', hb.ne', false_and,
    or_false] at h
  exact h

theorem transport_chart :
    ((chartMeasure (Measure.dirac basePt) 1 b).withDensity fun p =>
        ((chartDensity hh (fun _ => (1 : ℝ)) p).toNNReal : ENNReal)).map
      (Prod.snd : Base × (Fin 2 → ℝ) → Fin 2 → ℝ) =
    ((locData f hf b hb).μ.restrict (locData f hf b hb).sublevel).withDensity fun _ =>
      (((1 : ℝ)).toNNReal : ENNReal) := by
  have hdens : (fun p : Base × (Fin 2 → ℝ) =>
      ((chartDensity hh (fun _ => (1 : ℝ)) p).toNNReal : ENNReal)) = 1 := by
    funext p
    simp [chartDensity, hh]
  rw [hdens, withDensity_one]
  have hone : (fun _ : Fin 2 → ℝ => (((1 : ℝ)).toNNReal : ENNReal)) = 1 := by
    funext _
    simp
  rw [hone, withDensity_one]
  unfold chartMeasure
  rw [Measure.dirac_prod, Measure.map_map measurable_snd measurable_prodMk_left]
  have hid : (Prod.snd ∘ Prod.mk basePt : (Fin 2 → ℝ) → Fin 2 → ℝ) = id := rfl
  rw [hid, Measure.map_id]
  change _ = (volume.restrict (region b)).restrict (locData f hf b hb).sublevel
  rw [Measure.restrict_restrict (locData f hf b hb).measurableSet_sublevel,
    Set.inter_eq_right.2 (region_subset_sublevel f hf b hb)]
  exact (Measure.restrict_congr_set (region_ae_eq_box b)).symm

/-- **The chart presentation at the tied stratum**: Dirac base, box `(0,b]²`, `Φ(s,u) = u`,
`c = 1`, `h = (0,0)`, `k = (1,1)`, amplitude datum `f`. -/
noncomputable def chart : ChartPresentation (locData f hf b hb) ((partition f hf b hb).ρ 0) Base 1 1
    where
  ν := Measure.dirac basePt
  isFiniteMeasure_ν := inferInstance
  h := hh
  k := kk
  k_pos := kk_pos
  b := b
  b_pos := hb
  Φ := Prod.snd
  measurable_Φ := measurable_snd
  c := fun _ => 1
  measurable_c := measurable_const
  nonneg_c := Eventually.of_forall fun _ => zero_le_one
  x := ContinuousMap.const Base (datum f hf b hb)
  transport := transport_chart f hf b hb
  phase_normal := Eventually.of_forall fun p => (one_mul _).symm
  amplitude_eq := Eventually.of_forall fun p => by
    rw [ContinuousMap.const_apply, toEta_datum]
    change evalF f p.2 = 1 * polyD f p.2
    rw [one_mul]
    rfl
  fluct_zero := fun _ => by
    rw [ContinuousMap.const_apply]
    exact xiCoord_datum f hf b hb

theorem chart_obsFibre (v : Base) : (chart f hf b hb).obsFibre v = polyD f := rfl

/-- The normal-moment presentation from the polynomial series. -/
noncomputable def presentation : NormalMomentPresentation (chart f hf b hb) where
  p := fun _ => polySeriesD f
  R := fun _ => ⊤
  analytic := fun v => by
    rw [chart_obsFibre]
    exact hasFPowerSeriesOnBall_polyD f hf
  radius := fun _ => ENNReal.ofReal_lt_top
  cBound := 1
  c_le := fun _ => le_rfl

/-! ### The certificates -/

/-- **The resolved certificate** for `∫_{[0,b]²} P(x,y) e^{−n x²y²} dx dy`. -/
noncomputable def certificate :
    ResolvedCertificate geometry normalData (region b) phase (fun _ => (1 : ℝ)) (polyD f) where
  L := locData f hf b hb
  obs_eq := rfl
  phase_eq := rfl
  transport := by
    change Measure.map id (volume.restrict (region b)) = _
    rw [Measure.map_id]
    have : (fun _ : Fin 2 → ℝ => ENNReal.ofReal (1 : ℝ)) = 1 := by
      funext _
      simp
    rw [this, withDensity_one]
  M := 1
  n := fun _ => 1
  strat := fun _ => Finset.univ
  base := fun _ => Set.univ
  isCompact_base := fun _ => isCompact_univ
  β := 1
  β_pos := one_pos
  adapted := ⟨partition f hf b hb, fun _ => chart f hf b hb⟩
  T := fun _ => presentation f hf b hb
  frame := fun _ _ => frameUniv 2
  Φ_eq := fun _ s u => by
    change u = normalData.Φ Finset.univ s.1 (frameUniv 2 u)
    rw [Stratum_univ_eq 2 kk hh kk_pos s.1, Φ_frameUniv_origin]

/-- **The coefficient certificate**: density family `δ_0`, observable Taylor family `f`. -/
noncomputable def coeffCertificate : (certificate f hf b hb).CoefficientCertificate where
  cc := fun _ _ => OneDim.deltaFamily 2
  cc_abs := fun _ _ => OneDim.absSummableAt_deltaFamily 2 b
  jet_abs := fun _ s => by
    change AbsSummableAt (jetFamily 1 (polyD f)) b
    rw [jetFamily_polyD f hf]
    exact absSummableAt_of_finite_support f hf b
  datum_eq := fun _ s => by
    change toEta b (datum f hf b hb) =
      CoeffFamily.conv (OneDim.deltaFamily 2) (jetFamily 1 (polyD f))
    rw [toEta_datum, jetFamily_polyD f hf, OneDim.conv_deltaFamily]

theorem commonQ_certificate : commonQ (certificate f hf b hb).adapted.k = 2 := by
  change ∏ _ : Fin 1, (2 * ∏ _ : Fin 2, (1 : ℕ)) = 2
  simp

theorem commonD_certificate : commonD (certificate f hf b hb).n = 1 := by
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (1 : ℕ)) = 1
  simp

/-- ★★ **The coordinate-free expansion at the tied crossing**: for
`∫_{[0,b]²} P(x,y) e^{−n x²y²} dx dy`, with spectrum `{(α,j) : α ∈ ½ℕ, α ≤ A, j ≤ 1}` —
logarithmic terms `n^{−α} log n` are admitted, and the coefficients are the stratum integrals on
`S_{12} = {0}` (normal space `ℝ²`) of the normal-order series. -/
theorem hasCoordFreeExpansion_tied :
    normalData.HasCoordFreeExpansion (certificate f hf b hb).stratumMeasure
      (coeffCertificate f hf b hb).field (spectrumLe 2 1) (region b) phase
      (fun _ => (1 : ℝ)) (polyD f) := by
  have h := (coeffCertificate f hf b hb).hasCoordFreeExpansion_le (measurable_phase 2 kk)
    measurable_const (fun _ => zero_le_one) (continuous_polyD f hf).measurable
  rwa [commonQ_certificate, commonD_certificate] at h

/-- The original integral in this instance. -/
theorem globalLaplace_region (n : ℝ) :
    globalLaplace (region b) phase (fun w => polyD f w * 1) n =
      ∫ w in region b, polyD f w * Real.exp (-n * (w 0 ^ 2 * w 1 ^ 2)) := by
  unfold globalLaplace
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [mul_one, phase_eq]

end TiedCrossing

end Grammar
