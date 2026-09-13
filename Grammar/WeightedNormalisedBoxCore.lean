/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.NormalisedBoxCore
import Grammar.WaterFillingCollar

/-!
# The weighted normalised box core: Jacobian orders and a tangential unit (CCCXLV; phase E, unit E2)

Consult #102 §2, §5. The normalised box core of CCCXXI transports the prior-weighted Lebesgue
measure; a resolution chart carries in addition the **Jacobian weight** `∏_i |y_i|^{h_i}` and a
positive **tangential unit** in the phase, `K = u(y_tan) · ∏_i y_i^{2k_i}`. On the normal box
`y_i = λ_i(s) v_i` (`v_i > 0`) the weight factors as
`∏_{j∉I} |t_j|^{h_j} · ∏_{i∈I} λ_i(s)^{h_i} · ∏_i v_i^{h_i}` (`wgt_Φ`): the tangential factor
`H_I(s)` and the normal scaling `L_I(s)` go into the amplitude `c_h = J·H_I·L_I·fϕ` (`JW`, `cw`) and
the datum `x = (J H L · fϕ) ⋆ fφ` (`xDataW`), while `∏ v^{h}` is the chart density's own factor
(`chartDensity (hι h I σ) c_h`). The unit enters the normalisation `u(t)·t_I(t)·∏λ^{2k} = β`
(`WData.hnorm`). The core `wcore` records the orders `h` (`wcore.h = hι h I σ`), with exact
weighted transport (`densityW_ae` + the generic `map_Φ`), the normalised phase and the scaled
product amplitude; `wpresentation`, `jetFamily_obsFibre_w`, `toEta_wcore_x` as in CCCXXI.
Recovery: with `h = 0` the weight, the tangential factor and the normal scaling are `1`
(`wgt_zero`, `Hw_zero`, `Lw_zero`, `JW_zero`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

namespace NormalisedBox

variable {d : ℕ} (k h : Fin d → ℕ) (I : Finset (Fin d)) {n : ℕ} (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (lamT : (Tan I → ℝ) → (Nrm I → ℝ))

/-! ### The weight and its factorisation on the normal box -/

/-- The normal orders in box coordinates. -/
def hι (i : Fin (n + 1)) : ℕ := h (σ i).1

/-- The ambient Jacobian weight `∏_i |w_i|^{h_i}`. -/
noncomputable def wgt (w : Fin d → ℝ) : ℝ := ∏ i, |w i| ^ h i

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem wgt_nonneg (w : Fin d → ℝ) : 0 ≤ wgt h w :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem continuous_wgt : Continuous (wgt h) :=
  continuous_finsetProd _ fun i _ => (continuous_abs.comp (continuous_apply i)).pow _

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem measurable_wgt : Measurable (wgt h) := (continuous_wgt h).measurable

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem wgt_zero (w : Fin d → ℝ) : wgt (fun _ => 0) w = 1 := by
  unfold wgt
  simp

/-- The tangential weight `H_I(s) = ∏_{j∉I} |t_j|^{h_j}`. -/
noncomputable def Hw (s : K) : ℝ := ∏ j : Tan I, |e s j| ^ h j.1

/-- The normal scaling `L_I(s) = ∏_{j∈I} λ_j(s)^{h_j}`. -/
noncomputable def Lw (s : K) : ℝ := ∏ j : Nrm I, lamT (e s) j ^ h j.1

/-- The weighted Jacobian factor `J(s) H_I(s) L_I(s)`. -/
noncomputable def JW (s : K) : ℝ := J I e lamT s * Hw h I e s * Lw h I e lamT s

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Hw_zero (s : K) : Hw (fun _ => 0) I e s = 1 := by
  unfold Hw
  simp

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Lw_zero (s : K) : Lw (fun _ => 0) I e lamT s = 1 := by
  unfold Lw
  simp

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem JW_zero (s : K) : JW (fun _ => 0) I e lamT s = J I e lamT s := by
  rw [JW, Hw_zero, Lw_zero, mul_one, mul_one]

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Hw_nonneg (s : K) : 0 ≤ Hw h I e s :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Lw_nonneg (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K) : 0 ≤ Lw h I e lamT s :=
  Finset.prod_nonneg fun j _ => pow_nonneg (hpos (e s) (mem_range_self s) j).le _

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem JW_nonneg (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K) : 0 ≤ JW h I e lamT s :=
  mul_nonneg (mul_nonneg (J_pos I e lamT hpos s).le (Hw_nonneg h I e s))
    (Lw_nonneg h I e lamT hpos s)

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- ★ **The weight on the normal box**: `wgt(Φ(s,v)) = H_I(s) L_I(s) ∏_i v_i^{h_i}` for `v > 0`. -/
theorem wgt_Φ (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K) {v : Fin (n + 1) → ℝ}
    (hv : ∀ i, 0 < v i) :
    wgt h (Φ I σ e lamT (s, v)) = Hw h I e s * Lw h I e lamT s * ∏ i, v i ^ hι h I σ i := by
  unfold wgt
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I),
    Finset.prod_subtype (p := (· ∈ I)) (F := inferInstance) (Finset.univ.filter (· ∈ I))
      (fun x => by simp) _,
    Finset.prod_subtype (p := fun x => ¬ x ∈ I) (F := inferInstance)
      (Finset.univ.filter fun x => ¬ x ∈ I) (fun x => by simp) _]
  have h1 : ∀ j : Nrm I, |Φ I σ e lamT (s, v) j.1| ^ h j.1 =
      lamT (e s) j ^ h j.1 * v (σ.symm j) ^ h j.1 := fun j => by
    rw [Φ_apply, dif_pos j.2, abs_of_pos (mul_pos (hpos (e s) (mem_range_self s) j) (hv _)),
      mul_pow]
  have h2 : ∀ j : Tan I, |Φ I σ e lamT (s, v) j.1| ^ h j.1 = |e s j| ^ h j.1 := fun j => by
    rw [Φ_apply, dif_neg j.2]
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_congr rfl fun j _ => h2 j,
    Finset.prod_mul_distrib]
  have h3 : ∏ j : Nrm I, v (σ.symm j) ^ h j.1 = ∏ i, v i ^ hι h I σ i :=
    (Fintype.prod_equiv σ _ _ fun i => by rw [hι, Equiv.symm_apply_apply]).symm
  rw [h3]
  unfold Hw Lw
  ring

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- The tangential coordinates of a point of the normal box are the base point. -/
theorem tan_Φ (s : K) (v : Fin (n + 1) → ℝ) : WaterFilling.tan I (Φ I σ e lamT (s, v)) = e s := by
  funext j
  change Φ I σ e lamT (s, v) j.1 = e s j
  rw [Φ_apply, dif_neg j.2]

end NormalisedBox

namespace NormalisedBox

variable {d : ℕ} (k h : Fin d → ℕ) (I : Finset (Fin d)) {n : ℕ} (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (he : Continuous e) (he_inj : Function.Injective e)
  (lamT : (Tan I → ℝ) → (Nrm I → ℝ)) (hlamT : Measurable lamT)
  (hlam_cont : ContinuousOn lamT (range e)) (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j)
  (ϕ : (Fin d → ℝ) → ℝ) (b b' : ℝ) (hb : 0 < b) (hbb' : b < b')
  (Fϕ Fφ : UniformSeriesFamily K (n + 1) b')
  (hϕ_eq : ∀ s, ∀ v ∈ box (ι := Fin (n + 1)) b, ϕ (Φ I σ e lamT (s, v)) = evalF (Fϕ.f s) v)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he in
theorem continuous_Hw : Continuous (Hw h I e) :=
  continuous_finsetProd _ fun j _ => (continuous_abs.comp ((continuous_apply j).comp he)).pow _

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
theorem continuous_Lw : Continuous (Lw h I e lamT) :=
  continuous_finsetProd _ fun j _ =>
    ((continuous_apply j).comp (hlam_cont.comp_continuous he fun s => mem_range_self s)).pow _

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
theorem continuous_JW : Continuous (JW h I e lamT) :=
  ((continuous_J I e he lamT hlam_cont).mul (continuous_Hw h I e he)).mul
    (continuous_Lw h I e he lamT hlam_cont)

omit [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
theorem exists_JW_bound : ∃ C, ∀ s, |JW h I e lamT s| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_JW h I e he lamT hlam_cont).continuousOn
  exact ⟨C, fun s => by simpa using hC s (mem_univ s)⟩

omit [MeasurableSpace K] [BorelSpace K] in
/-- The weighted Jacobian bound. -/
noncomputable def JWb : ℝ := (exists_JW_bound h I e he lamT hlam_cont).choose

omit [MeasurableSpace K] [BorelSpace K] in
theorem abs_JW_le (s : K) : |JW h I e lamT s| ≤ JWb h I e he lamT hlam_cont :=
  (exists_JW_bound h I e he lamT hlam_cont).choose_spec s

/-- The weighted density amplitude `c_h(s,v) = J(s) H_I(s) L_I(s) · ϕ̃(v)`. -/
noncomputable def cw (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  JW h I e lamT p.1 * evalF (Fϕ.f p.1) (clamp b hb.le p.2)

/-- The weighted amplitude datum `(J H L · fϕ) ⋆ fφ`. -/
noncomputable def xDataW : TangentialData K (n + 1) :=
  ((Fϕ.smul (JW h I e lamT) (continuous_JW h I e he lamT hlam_cont) _
    (abs_JW_le h I e he lamT hlam_cont)).conv (hb.le.trans hbb'.le) Fφ).datumC hb hbb'.le

omit [MeasurableSpace K] [BorelSpace K] in
theorem toEta_xDataW (s : K) :
    toEta b (xDataW h I e he lamT hlam_cont b b' hb hbb' Fϕ Fφ s) =
      CoeffFamily.conv (fun γ => JW h I e lamT s * Fϕ.f s γ) (Fφ.f s) :=
  UniformSeriesFamily.toEta_datumC _ _ _ _

omit [MeasurableSpace K] [BorelSpace K] in
theorem xiCoord_xDataW (s : K) :
    xiCoord (xDataW h I e he lamT hlam_cont b b' hb hbb' Fϕ Fφ s) = 0 :=
  UniformSeriesFamily.xiCoord_datumC _ _ _ _

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hϕ_eq in
theorem cw_eq_of_mem_box (s : K) {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) b) :
    cw h I e lamT b b' hb Fϕ (s, v) = JW h I e lamT s * ϕ (Φ I σ e lamT (s, v)) := by
  have hcl : clamp b hb.le v = v := clamp_eq_self hb.le fun i => by
    have := hv i (mem_univ _)
    rw [mem_Ioc] at this
    exact abs_le.2 ⟨by linarith, this.2⟩
  rw [cw, hcl, hϕ_eq s v hv]

include he he_inj hpos hϕ_eq in
/-- ★ **The weighted chart density is the Jacobian-weighted prior with the weight**, a.e. -/
theorem densityW_ae :
    (fun p : K × (Fin (n + 1) → ℝ) =>
      ((chartDensity (hι h I σ) (cw h I e lamT b b' hb Fϕ) p).toNNReal : ℝ≥0∞)) =ᵐ[chartMeasure
        (baseMeasure I e) n b]
      fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) *
        ENNReal.ofReal (wgt h (Φ I σ e lamT p) * ϕ (Φ I σ e lamT p)) := by
  have := isFiniteMeasure_baseMeasure I e he he_inj
  filter_upwards [ae_snd_mem_box (baseMeasure I e) n b] with p hp
  have hc := cw_eq_of_mem_box h I σ e lamT ϕ b b' hb Fϕ hϕ_eq p.1 hp
  have hv : ∀ i, 0 < p.2 i := fun i => by
    have := hp i (mem_univ _)
    rw [mem_Ioc] at this
    exact this.1
  change ENNReal.ofReal (chartDensity (hι h I σ) (cw h I e lamT b b' hb Fϕ) p) = _
  rw [chartDensity]
  rw [show (p.1, p.2) = p from rfl] at hc
  rw [hc, show Φ I σ e lamT p = Φ I σ e lamT (p.1, p.2) from rfl, wgt_Φ h I σ e lamT hpos p.1 hv,
    show (∏ j, lamT (e p.1) j) = J I e lamT p.1 from rfl,
    ← ENNReal.ofReal_mul (J_pos I e lamT hpos p.1).le]
  congr 1
  unfold JW
  ring

end NormalisedBox

namespace NormalisedBox

/-! ### The bundled weighted data and the weighted core -/

/-- The data of a weighted normalised box core: the data of CCCXXI together with a tangential
unit `u` normalised with the widths, `u(t)·t_I(t)·∏λ^{2k} = β`. -/
structure WData (k : Fin d → ℕ) (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
    (W : Set (Fin d → ℝ)) (ϕ φ : (Fin d → ℝ) → ℝ) where
  /-- the identification of box coordinates with the normal coordinates -/
  σ : Fin (n + 1) ≃ Nrm I
  /-- the tangential coordinates of the base -/
  e : K → (Tan I → ℝ)
  he : Continuous e
  he_inj : Function.Injective e
  /-- the normal widths -/
  lamT : (Tan I → ℝ) → (Nrm I → ℝ)
  hlamT : Measurable lamT
  hlam_cont : ContinuousOn lamT (range e)
  hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j
  /-- the tangential phase unit and the normalised constant -/
  unit : (Tan I → ℝ) → ℝ
  β : ℝ
  hnorm : ∀ t ∈ range e, unit t * (tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1)) = β
  /-- the box side and the series radius -/
  b : ℝ
  b' : ℝ
  hb : 0 < b
  hbb' : b < b'
  hW : image I e lamT b ⊆ W
  /-- the prior and observable series in the normalised normal variables -/
  Fϕ : UniformSeriesFamily K (n + 1) b'
  Fφ : UniformSeriesFamily K (n + 1) b'
  hϕ_eq : ∀ s, ∀ v ∈ box (ι := Fin (n + 1)) b, ϕ (Φ I σ e lamT (s, v)) = evalF (Fϕ.f s) v
  hφ_eq : ∀ s (v : Fin (n + 1) → ℝ), ‖v‖ < b' → φ (Φ I σ e lamT (s, v)) = evalF (Fφ.f s) v

variable {d : ℕ} {k h : Fin d → ℕ} {I : Finset (Fin d)} (hkI : ∀ j : Nrm I, 0 < k j.1) {n : ℕ}
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {W : Set (Fin d → ℝ)} (hWm : MeasurableSet W) {ϕ φ : (Fin d → ℝ) → ℝ} (hϕm : Measurable ϕ)
  (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w) (L : LocalisationData (Fin d → ℝ)) (D : WData k I n K W ϕ φ)
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (wgt h w * ϕ w))
  (hLphase : ∀ y, L.phase y = D.unit (WaterFilling.tan I y) * CoordModel.phase d k y)
  (hLobs : L.obs = φ)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem WData.b'_pos : 0 < D.b' := D.hb.trans D.hbb'

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem WData.norm_lt_of_mem_box {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) D.b) :
    ‖v‖ < D.b' := by
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg D.hb.le).2 fun i => ?_) D.hbb'
  have := hv i (mem_univ _)
  rw [mem_Ioc] at this
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith, this.2⟩

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- ★★ **The weighted normalised box core**: orders `h` recorded (`h = hι h I σ`), density
`c_h = J H_I L_I · ϕ`, exact transport of the weighted measure, normalised phase with the unit,
scaled product amplitude. -/
noncomputable def wcore : CorePresentation L (L.μ.restrict (image I D.e D.lamT D.b)) K n D.β where
  ν := baseMeasure I D.e
  isFiniteMeasure_ν := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
  h := hι h I D.σ
  k := kι k I D.σ
  k_pos := fun i => hkI (D.σ i)
  b := D.b
  b_pos := D.hb
  Φ := Φ I D.σ D.e D.lamT
  measurable_Φ := measurable_Φ I D.σ (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT
  c := cw h I D.e D.lamT D.b D.b' D.hb D.Fϕ
  measurable_c :=
    (((continuous_JW h I D.e D.he D.lamT D.hlam_cont).comp continuous_fst).mul
      (D.Fϕ.continuous_evalF_clamp D.hb.le D.hbb'.le)).measurable
  nonneg_c := by
    have := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
    filter_upwards [ae_snd_mem_box (baseMeasure I D.e) n D.b]
    rintro ⟨s, v⟩ hv
    rw [cw_eq_of_mem_box h I D.σ D.e D.lamT ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq s hv]
    exact mul_nonneg (JW_nonneg h I D.e D.lamT D.hpos s)
      (hϕ0 _ (D.hW (mem_image_Φ I D.σ D.e D.lamT D.hpos s hv)))
  x := xDataW h I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ
  transport := by
    have hmap := map_Φ I D.σ D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT D.hpos
      ((measurable_wgt h).mul hϕm).ennreal_ofReal
    rw [show (baseMeasure I D.e).prod (volume.restrict (box (ι := Fin (n + 1)) D.b)) =
      chartMeasure (baseMeasure I D.e) n D.b from rfl] at hmap
    rw [withDensity_congr_ae
      (densityW_ae h I D.σ D.e D.he D.he_inj D.lamT D.hpos ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq), hLμ,
     ← restrict_withDensity hWm, Measure.restrict_restrict
      (measurableSet_image I D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT),
      inter_eq_left.2 D.hW]
    exact hmap
  phase_normal := Eventually.of_forall fun p => by
    obtain ⟨s, v⟩ := p
    rw [hLphase, tan_Φ, phase_Φ, ← mul_assoc, D.hnorm (D.e s) (mem_range_self _)]
  amplitude_eq := by
    have := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
    filter_upwards [ae_snd_mem_box (baseMeasure I D.e) n D.b]
    rintro ⟨s, v⟩ hv
    rw [toEta_xDataW, hLobs]
    have hv' : ∀ i, 0 ≤ v i ∧ v i ≤ D.b := fun i => by
      have := hv i (mem_univ _)
      rw [mem_Ioc] at this
      exact ⟨this.1.le, this.2⟩
    rw [evalF_conv_of_absSummableAt (f := fun γ => JW h I D.e D.lamT s * D.Fϕ.f s γ) D.hb
      ((D.Fϕ.smul (JW h I D.e D.lamT) (continuous_JW h I D.e D.he D.lamT D.hlam_cont) _
        (abs_JW_le h I D.e D.he D.lamT D.hlam_cont)).absSummableAt_of_le D.hb.le D.hbb'.le s)
      (D.Fφ.absSummableAt_of_le D.hb.le D.hbb'.le s) hv',
      evalF_const_mul, cw_eq_of_mem_box h I D.σ D.e D.lamT ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq s hv,
      D.hφ_eq s v (D.norm_lt_of_mem_box hv), D.hϕ_eq s v hv]
  fluct_zero := xiCoord_xDataW h I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
theorem wcore_h (i : Fin (n + 1)) :
    (wcore hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs (h := h)).h i = h (D.σ i).1 := rfl

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
theorem wcore_obsFibre (s : K) (v : Fin (n + 1) → ℝ) :
    (wcore hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs (h := h)).obsFibre s v =
      φ (Φ I D.σ D.e D.lamT (s, v)) := by
  change L.obs _ = _
  rw [hLobs]
  rfl

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- ★ **The normal-moment presentation of the weighted core.** -/
noncomputable def wpresentation :
    CoreNormalMomentPresentation (wcore hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs (h := h)) where
  p := fun s => polySeriesD (D.Fφ.f s)
  R := fun _ => ENNReal.ofReal D.b'
  analytic := fun s => by
    refine (hasFPowerSeriesOnBall_evalF (D.Fφ.f s) D.b'_pos
      (D.Fφ.absSummableAt D.b'_pos.le s)).congr fun v hv => ?_
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hv
    rw [wcore_obsFibre, D.hφ_eq s v ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 hv)]
  radius := fun _ => (ENNReal.ofReal_lt_ofReal_iff D.b'_pos).2 D.hbb'
  cBound := JWb h I D.e D.he D.lamT D.hlam_cont * ∑' γ, D.Fϕ.M γ * D.b ^ (∑ i, γ i)
  c_le := fun q => by
    refine (le_abs_self _).trans ?_
    change |JW h I D.e D.lamT q.1 * evalF (D.Fϕ.f q.1) (clamp D.b D.hb.le q.2)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_JW_le h I D.e D.he D.lamT D.hlam_cont q.1)
      (D.Fϕ.abs_evalF_le D.hb.le D.hbb'.le q.1 _ (abs_clamp_le D.hb.le q.2)) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_JW_le h I D.e D.he D.lamT D.hlam_cont q.1))

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- The Taylor family of the fibre observable is the observable's coefficient family. -/
theorem jetFamily_obsFibre_w (s : K) :
    jetFamily n ((wcore hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs (h := h)).obsFibre s) = D.Fφ.f s := by
  rw [jetFamily_eq_monoFamily ((wpresentation hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs).analytic s)]
  exact monoFamily_polySeriesD (D.Fφ.f s)

include hkI hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- The amplitude datum of the weighted core: `(J H L · fϕ) ⋆ fφ`. -/
theorem toEta_wcore_x (s : K) :
    toEta D.b ((wcore hkI hWm hϕm hϕ0 L D hLμ hLphase hLobs (h := h)).x s) =
      CoeffFamily.conv (fun γ => JW h I D.e D.lamT s * D.Fϕ.f s γ) (D.Fφ.f s) :=
  toEta_xDataW h I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ s

end NormalisedBox

end Grammar
