/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordFreeExpansionCompletion
import Grammar.OneDimPolynomialSeries

/-!
# The first instance of the coordinate-free expansion: `∫_0^ρ P(x) e^{−n x²} dx` (CCCVII)

Plan unit 8c (consult #93 A, the acceptance gate): both certificates of CCCIII are constructed
for the half-interval `W = [0, ρ]`, the phase `K = x²`, the uniform prior and a polynomial
observable `P = ∑_γ f_γ x^γ`, on the one-dimensional resolved geometry of CCCV.

* `locData` — the localisation datum (Lebesgue measure on `[0, ρ]`, phase `x²`, observable `P`,
  level `δ = b²`, `0 < b ≤ ρ`); `partition` — the one-piece partition;
* `chart` — the single chart presentation: base the divisor point `{0}` with the Dirac measure,
  normal box `(0, b]`, `Φ(s, u) = u`, density `c = 1`, exponents `h = 0`, `k = 1`, amplitude datum
  the coefficient family `f`; the transport identity is
  `Lebesgue on (0, b] = (Lebesgue on [0,ρ]) restricted to {x² < b²}` up to the null set `{0, b}`
  (`transport_aux`);
* `presentation` — the normal-moment presentation from `polySeries` (CCCVI);
* `certificate : ResolvedCertificate geometry normalData (region ρ) phase 1 P` and
  `coeffCertificate : certificate.CoefficientCertificate` (density family `δ_0`, Taylor family
  `f` by `jetFamily_poly`);
* ★★ `hasCoordFreeExpansion_poly` — the coordinate-free expansion theorem for
  `∫_0^ρ P(x) e^{−n x²} dx`, with the spectrum `spectrumLe 2 0 A = {α ∈ ½ℕ : α ≤ A}` (no logs).

So the certified theorem is inhabited: on the point stratum `S_• = {0}` with normal space `ℝ`, the
coefficient of `n^{−α}` is `∑_r (1/r!) ⟨D^r P(0), B_{r,α}⟩` with the tensors of CCCII.

Non-claims: the coefficients are not evaluated in closed form here (that is the kernel
computation `monoKernel`, a separate unit); only the half-interval is treated (two charts are
needed for a two-sided interval).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

namespace OneDim

open CoeffFamily MonoRep

variable (f : CoeffFamily 1) {supp : Finset (Fin 1 → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0)
  (ρ b : ℝ) (hb : 0 < b) (hbρ : b ≤ ρ)

/-! ### The region and the localisation datum -/

/-- The region `W = [0, ρ]`. -/
def region (ρ : ℝ) : Set Space := {w | 0 ≤ w 0 ∧ w 0 ≤ ρ}

omit hf hb hbρ in
theorem region_eq_piBox : region ρ = piBox 1 (Icc 0 ρ) := by
  ext w
  simp only [region, piBox, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, Fin.forall_fin_one]

omit hf hb hbρ in
theorem isCompact_region : IsCompact (region ρ) := by
  rw [region_eq_piBox]
  exact isCompact_univ_pi fun _ => isCompact_Icc

omit hf hb hbρ in
theorem measurableSet_region : MeasurableSet (region ρ) :=
  (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    (measurableSet_le (measurable_pi_apply 0) measurable_const)

include hf hb in
/-- The localisation datum: Lebesgue measure on `[0, ρ]`, phase `x²`, observable `P`, level `b²`. -/
noncomputable def locData : LocalisationData Space where
  μ := volume.restrict (region ρ)
  phase := phase
  obs := poly f
  phase_measurable := measurable_phase
  phase_nonneg := Eventually.of_forall phase_nonneg
  obs_integrable := (continuous_poly f hf).continuousOn.integrableOn_compact (isCompact_region ρ)
  δ := b ^ 2
  δ_pos := by positivity

omit hbρ in
theorem locData_sublevel : (locData f hf ρ b hb).sublevel = {w : Space | w 0 ^ 2 < b ^ 2} := rfl

omit hbρ in
/-- The one-piece partition of the sublevel set. -/
noncomputable def partition : (locData f hf ρ b hb).FiniteSublevelPartition (Fin 1) where
  ρ := fun _ _ => 1
  measurable_ρ := fun _ => measurable_const
  nonneg_ρ := fun _ => Eventually.of_forall fun _ => zero_le_one
  sum_eq_one := Eventually.of_forall fun _ => by simp

/-! ### The base and the null coordinate hyperplanes -/

/-- The base of the chart: the divisor point. -/
abbrev Base := ↥(Set.univ : Set (geometry.Stratum Finset.univ))

/-- The base point. -/
def basePt : Base := ⟨origin, trivial⟩

theorem volume_coord_eq_zero (c : ℝ) : volume {w : Space | w 0 = c} = 0 := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage
    (measurableSet_singleton c).nullMeasurableSet
  have hpre : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {c} = {w : Space | w 0 = c} := by
    ext w
    simp [MeasurableEquiv.funUnique, MeasurableEquiv.piUnique]
  rw [hpre] at h
  exact h.trans Real.volume_singleton

include hb hbρ in
/-- The chart box `(0, b]` and the localised region `[0, ρ] ∩ {x² < b²}` differ by a null set. -/
theorem transport_aux :
    (({w : Space | w 0 ^ 2 < b ^ 2} : Set Space) ∩ region ρ : Set Space) =ᵐ[volume]
      (piBox 1 (Ioc 0 b) : Set Space) := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun w hw => ?_) (volume_coord_eq_zero 0)
    obtain ⟨⟨hlt, h0, _⟩, hnot⟩ := hw
    have hlt' : w 0 ^ 2 < b ^ 2 := hlt
    simp only [piBox, Set.mem_univ_pi, Set.mem_Ioc, Fin.forall_fin_one, not_and, not_le] at hnot
    have hwb : w 0 < b := by nlinarith
    by_contra hne
    exact absurd (hnot (lt_of_le_of_ne h0 (Ne.symm hne))) (not_lt.2 hwb.le)
  · refine measure_mono_null (fun w hw => ?_) (volume_coord_eq_zero b)
    obtain ⟨hin, hnot⟩ := hw
    simp only [piBox, Set.mem_univ_pi, Set.mem_Ioc, Fin.forall_fin_one] at hin
    by_contra hne
    have hlt : w 0 < b := lt_of_le_of_ne hin.2 hne
    refine hnot ⟨?_, hin.1.le, hin.2.trans hbρ⟩
    exact sq_lt_sq' (by linarith) hlt

/-! ### The chart presentation -/

theorem absSummableAt_zero (b : ℝ) : AbsSummableAt (0 : CoeffFamily 1) b :=
  summable_of_ne_finset_zero (s := ∅) fun γ _ => by simp

include hf in
/-- The amplitude datum of the chart: the coefficient family `f` (zero phase family). -/
noncomputable def datum : DataSpace 1 :=
  ofFamilies b hb 0 f (absSummableAt_zero b) (absSummableAt_of_support f hf b)

omit hbρ in
theorem toEta_datum : toEta b (datum f hf b hb) = f := toEta_ofFamilies _ _ _ _ _ _

omit hbρ in
theorem xiCoord_datum : xiCoord (datum f hf b hb) = 0 := by
  funext γ
  have h := congrFun (toXi_ofFamilies b hb 0 f (absSummableAt_zero b)
    (absSummableAt_of_support f hf b)) γ
  simp only [toXi, Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff', hb.ne', false_and,
    or_false] at h
  exact h

include hbρ in
theorem transport_chart :
    ((chartMeasure (Measure.dirac basePt) 0 b).withDensity fun p =>
        ((chartDensity (fun _ : Fin 1 => (0 : ℕ)) (fun _ => (1 : ℝ)) p).toNNReal : ENNReal)).map
      (Prod.snd : Base × Space → Space) =
    ((locData f hf ρ b hb).μ.restrict (locData f hf ρ b hb).sublevel).withDensity fun _ =>
      (((1 : ℝ)).toNNReal : ENNReal) := by
  have hdens : (fun p : Base × Space =>
      ((chartDensity (fun _ : Fin 1 => (0 : ℕ)) (fun _ => (1 : ℝ)) p).toNNReal : ENNReal)) = 1 := by
    funext p
    simp [chartDensity]
  rw [hdens, withDensity_one]
  have hone : (fun _ : Space => (((1 : ℝ)).toNNReal : ENNReal)) = 1 := by
    funext _
    simp
  rw [hone, withDensity_one]
  unfold chartMeasure
  rw [Measure.dirac_prod, Measure.map_map measurable_snd measurable_prodMk_left]
  have hid : (Prod.snd ∘ Prod.mk basePt : Space → Space) = id := rfl
  rw [hid, Measure.map_id]
  change _ = ((volume.restrict (region ρ)).restrict {w : Space | w 0 ^ 2 < b ^ 2})
  rw [Measure.restrict_restrict (measurableSet_lt (f := fun w : Space => w 0 ^ 2)
    ((measurable_pi_apply 0).pow_const 2) measurable_const)]
  exact (Measure.restrict_congr_set (transport_aux ρ b hb hbρ)).symm

include hbρ in
/-- **The chart presentation**: base the divisor point, normal box `(0, b]`, `Φ(s, u) = u`,
`c = 1`, `h = 0`, `k = 1`, amplitude datum `f`. -/
noncomputable def chart :
    ChartPresentation (locData f hf ρ b hb) ((partition f hf ρ b hb).ρ 0) Base 0 1 where
  ν := Measure.dirac basePt
  isFiniteMeasure_ν := inferInstance
  h := fun _ => 0
  k := fun _ => 1
  k_pos := fun _ => one_pos
  b := b
  b_pos := hb
  Φ := Prod.snd
  measurable_Φ := measurable_snd
  c := fun _ => 1
  measurable_c := measurable_const
  nonneg_c := Eventually.of_forall fun _ => zero_le_one
  x := ContinuousMap.const Base (datum f hf b hb)
  transport := transport_chart f hf ρ b hb hbρ
  phase_normal := Eventually.of_forall fun p => by
    change p.2 0 ^ 2 = 1 * ∏ i : Fin 1, p.2 i ^ (2 * 1)
    rw [Fin.prod_univ_one, one_mul, mul_one]
  amplitude_eq := Eventually.of_forall fun p => by
    rw [ContinuousMap.const_apply, toEta_datum]
    change evalF f p.2 = 1 * poly f p.2
    rw [one_mul]
    rfl
  fluct_zero := fun _ => by
    rw [ContinuousMap.const_apply]
    exact xiCoord_datum f hf b hb

theorem chart_obsFibre (v : Base) : (chart f hf ρ b hb hbρ).obsFibre v = poly f := rfl

/-- The normal-moment presentation from the polynomial series. -/
noncomputable def presentation : NormalMomentPresentation (chart f hf ρ b hb hbρ) where
  p := fun _ => polySeries f
  R := fun _ => ⊤
  analytic := fun v => by
    rw [chart_obsFibre]
    exact hasFPowerSeriesOnBall_poly f hf
  radius := fun _ => ENNReal.ofReal_lt_top
  cBound := 1
  c_le := fun _ => le_rfl

/-! ### The certificates -/

/-- **The resolved certificate** for `∫_0^ρ P(x) e^{−n x²} dx`. -/
noncomputable def certificate :
    ResolvedCertificate geometry normalData (region ρ) phase (fun _ => (1 : ℝ)) (poly f) where
  L := locData f hf ρ b hb
  obs_eq := rfl
  phase_eq := rfl
  transport := by
    change Measure.map id (volume.restrict (region ρ)) = _
    rw [Measure.map_id]
    have : (fun _ : Space => ENNReal.ofReal (1 : ℝ)) = 1 := by
      funext _
      simp
    rw [this, withDensity_one]
  M := 1
  n := fun _ => 0
  strat := fun _ => Finset.univ
  base := fun _ => Set.univ
  isCompact_base := fun _ => isCompact_univ
  β := 1
  β_pos := one_pos
  cores := (⟨partition f hf ρ b hb, fun _ => chart f hf ρ b hb hbρ⟩ :
    AdaptedStrataData (locData f hf ρ b hb) 1 (fun _ => Base) (fun _ => 0) 1).toCoreDecomposition
  T := fun _ => (presentation f hf ρ b hb hbρ).toCore
  frame := fun _ _ => frameUniv
  Φ_eq := fun _ s u => by
    change u = normalData.Φ Finset.univ s.1 (frameUniv u)
    rw [Φ_frameUniv, Stratum_univ_eq s.1, origin_val_zero]
    funext i
    rw [Fin.fin_one_eq_zero i, zero_add]

/-- **The coefficient certificate**: density family `δ_0`, observable Taylor family `f`. -/
noncomputable def coeffCertificate : (certificate f hf ρ b hb hbρ).CoefficientCertificate where
  cc := fun _ _ => deltaFamily 1
  cc_abs := fun _ _ => absSummableAt_deltaFamily 1 b
  jet_abs := fun _ s => by
    change AbsSummableAt (jetFamily 0 (poly f)) b
    rw [jetFamily_poly f hf]
    exact absSummableAt_of_support f hf b
  datum_eq := fun _ s => by
    change toEta b (datum f hf b hb) = CoeffFamily.conv (deltaFamily 1) (jetFamily 0 (poly f))
    rw [toEta_datum, jetFamily_poly f hf, conv_deltaFamily]

theorem commonQ_certificate : commonQ (certificate f hf ρ b hb hbρ).cores.k = 2 := by
  change ∏ _ : Fin 1, (2 * ∏ _ : Fin 1, (1 : ℕ)) = 2
  simp

theorem commonD_certificate : commonD (certificate f hf ρ b hb hbρ).n = 0 := by
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (0 : ℕ)) = 0
  simp

/-- ★★ **The coordinate-free expansion of `∫_0^ρ P(x) e^{−n x²} dx`**: the certified theorem of
CCCIII–CCCIV is inhabited. The spectrum is `{α ∈ ½ℕ : α ≤ A}` with no logarithms. -/
theorem hasCoordFreeExpansion_poly :
    normalData.HasCoordFreeExpansion (certificate f hf ρ b hb hbρ).stratumMeasure
      (coeffCertificate f hf ρ b hb hbρ).field (spectrumLe 2 0) (region ρ) phase
      (fun _ => (1 : ℝ)) (poly f) := by
  have h := (coeffCertificate f hf ρ b hb hbρ).hasCoordFreeExpansion_le measurable_phase
    measurable_const (fun _ => zero_le_one) (continuous_poly f hf).measurable
  rwa [commonQ_certificate, commonD_certificate] at h

/-- The original integral in this instance is `∫_{[0,ρ]} P(w) e^{−n w²} dw`. -/
theorem globalLaplace_region (n : ℝ) :
    globalLaplace (region ρ) phase (fun w => poly f w * 1) n =
      ∫ w in region ρ, poly f w * Real.exp (-n * w 0 ^ 2) := by
  unfold globalLaplace phase
  simp only [mul_one]


end OneDim

end Grammar
