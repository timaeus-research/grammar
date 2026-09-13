/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.WeightedNormalisedBoxCore
import Grammar.ChartModelGeometry
import Grammar.CoordinateBoxInputs
import Grammar.ComplexNormalInsertion
import Grammar.OrthantDecomposition
import Grammar.CoordFreeExpansionCompletion

/-!
# The singleton tangential-unit producer (CCCXLVI; phase E, unit E3)

Consult #102 §4. A resolution chart with ONE active coordinate `β`, phase `u(y) · y_β²` with a
positive tangential unit `u` (`u ≥ c > 0` on the box, depending only on the coordinates `≠ β`) and
Jacobian order `h₀` on `y_β`: on the positive box `[0,a]^d` the whole closed face `{y_β = 0}` is the
compact base, the normal width is `λ(s) = u(s)^{-1/2}` (so `u · λ² = 1`), the normal box `(0, b]`
is a phase collar (`u y_β² = v²`), and off it the phase is `≥ b²`. From face series of the prior and
the observable in the original normal variable (`OriginalFaceSeries` at radius `ρ`, rescaled by
`λ ≤ (√c)⁻¹` to the normalised variable) we build the weighted core (CCCXLV, orders recorded), a
one-core `ResolvedCertificate` for the chart geometry (CCCXLIII, active `{β}`, orders `(1, h₀)`)
with the frame `v ↦ λ(s) v e_β`, and its coefficient certificate; hence ★★★
`hasCoordFreeExpansion_singleton`: the weighted integral `∫_{[0,a]^d} φ · |y_β|^{h₀} ϕ · e^{−n
u y_β²}`
has the coordinate-free expansion on the chart strata (the deepest stratum `{y_β = 0} ≅ ℝ^{d−1}`
carries the face measure), with the spectrum of one normal coordinate of exponent `1`. This is the
producer for each orthant piece of a blow-up chart of the cube (E4). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

namespace SingletonChart

open NormalisedBox WaterFilling CoordModel CoeffFamily

variable {d : ℕ} (β : Fin d)

/-! ### The singleton index data -/

/-- The singleton index. -/
def Iβ : NonemptyIdx d := ⟨{β}, Finset.singleton_nonempty β⟩

/-- The phase exponents: `1` at `β`, `0` elsewhere. -/
def kS : Fin d → ℕ := Pi.single β 1

/-- The Jacobian orders: `h₀` at `β`, `0` elsewhere. -/
def hS (h₀ : ℕ) : Fin d → ℕ := Pi.single β h₀

theorem kS_self : kS β β = 1 := Pi.single_eq_same _ _

theorem kS_ne {j : Fin d} (hj : j ≠ β) : kS β j = 0 := Pi.single_eq_of_ne hj _

theorem hS_self (h₀ : ℕ) : hS β h₀ β = h₀ := Pi.single_eq_same _ _

theorem hS_ne (h₀ : ℕ) {j : Fin d} (hj : j ≠ β) : hS β h₀ j = 0 := Pi.single_eq_of_ne hj _

theorem hkS : ∀ i ∈ ({β} : Finset (Fin d)), 0 < kS β i := fun i hi => by
  rw [Finset.mem_singleton.1 hi, kS_self]
  exact one_pos

theorem hkI : ∀ j : Nrm (Iβ β).1, 0 < kS β j.1 := fun j => hkS β j.1 j.2

theorem tan_ne (j : Tan (Iβ β).1) : j.1 ≠ β := fun h => j.2 (Finset.mem_singleton.2 h)

instance : Unique (Nrm (Iβ β).1) :=
  ⟨⟨⟨β, Finset.mem_singleton_self β⟩⟩, fun x => Subtype.ext (Finset.mem_singleton.1 x.2)⟩

theorem coordPhase_kS (y : Fin d → ℝ) : CoordModel.phase d (kS β) y = y β ^ 2 := by
  unfold CoordModel.phase
  rw [Finset.prod_eq_single β]
  · rw [kS_self, mul_one]
  · intro i _ hi
    rw [kS_ne β hi, mul_zero, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wgt_hS (h₀ : ℕ) (y : Fin d → ℝ) : wgt (hS β h₀) y = |y β| ^ h₀ := by
  unfold wgt
  rw [Finset.prod_eq_single β]
  · rw [hS_self]
  · intro i _ hi
    rw [hS_ne β h₀ hi, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The chart phase `u(y) · y_β²`. -/
def Kc (u : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ := u y * y β ^ 2

theorem Kc_eq_chartPhase (u : (Fin d → ℝ) → ℝ) : Kc β u = ChartModel.phase d {β} (kS β) u := by
  funext y
  unfold Kc ChartModel.phase ChartModel.monoPhase
  rw [Finset.prod_singleton, kS_self, mul_one]

/-- The chart geometry of the singleton model. -/
noncomputable abbrev G (h₀ : ℕ) : ResolvedGeometry d (Fin d → ℝ) :=
  ChartModel.geometry d {β} (kS β) (hS β h₀) (hkS β)

/-- Its normal data. -/
noncomputable abbrev N (h₀ : ℕ) : ResolvedNormalData (G β h₀) (Amb d) :=
  ChartModel.normalData d {β} (kS β) (hS β h₀) (hkS β)

/-! ### The tangential unit and the widths -/

variable (u : (Fin d → ℝ) → ℝ)

/-- The unit as a function of the tangential coordinates (the point with `y_β = 0`). -/
noncomputable def unitT (t : Tan (Iβ β).1 → ℝ) : ℝ := u (liftPoint (Iβ β).1 t)

/-- The normal width `λ(t) = (√u(t))⁻¹`. -/
noncomputable def lam (t : Tan (Iβ β).1 → ℝ) : Nrm (Iβ β).1 → ℝ := fun _ => (Real.sqrt (unitT β
u t))⁻¹

/-- The width bound `(√c)⁻¹`. -/
noncomputable def Lb (c : ℝ) : ℝ := (Real.sqrt c)⁻¹

omit β u in
theorem continuous_liftPoint (I : Finset (Fin d)) : Continuous (liftPoint I) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j ∈ I
  · simp only [liftPoint_apply, dif_pos hj]
    exact continuous_const
  · simp only [liftPoint_apply, dif_neg hj]
    exact continuous_apply _

theorem liftPoint_tan_apply (y : Fin d → ℝ) {j : Fin d} (hj : j ≠ β) :
    liftPoint (Iβ β).1 (tan (Iβ β).1 y) j = y j := by
  have hj' : j ∉ (Iβ β).1 := fun h => hj (Finset.mem_singleton.1 h)
  rw [liftPoint_apply, dif_neg hj']
  rfl

variable (hu_tan : ∀ y y' : Fin d → ℝ, (∀ j, j ≠ β → y j = y' j) → u y = u y')

include hu_tan in
theorem unitT_tan (y : Fin d → ℝ) : unitT β u (tan (Iβ β).1 y) = u y :=
  hu_tan _ _ fun _ hj => liftPoint_tan_apply β y hj

/-! ### The base: the closed face -/

variable (a : ℝ) (h₀ : ℕ)

/-- The face as a subset of the deepest stratum of the chart geometry. -/
def base : Set ((G β h₀).Stratum Finset.univ) := {s | (s : Fin d → ℝ) ∈ WaterFilling.faceSet a {β}}

theorem mem_stratumSet_univ_of_mem_faceSet {w : Fin d → ℝ} (hw : w ∈ WaterFilling.faceSet a {β}) :
    w ∈ (G β h₀).stratumSet Finset.univ :=
  (ChartModel.mem_stratumSet_univ_iff d {β} (kS β) (hS β h₀) (hkS β) w).2 fun i hi => hw.2 i hi

theorem stratum_coord_zero (s : (G β h₀).Stratum Finset.univ) : (s : Fin d → ℝ) β = 0 :=
  (ChartModel.mem_stratumSet_univ_iff d {β} (kS β) (hS β h₀) (hkS β) _).1 s.2 β
    (Finset.mem_singleton_self β)

theorem isCompact_base : IsCompact (base β a h₀) := by
  have : base β a h₀ = range fun w : ↥(WaterFilling.faceSet a {β}) =>
      (⟨w.1, mem_stratumSet_univ_of_mem_faceSet β a h₀ w.2⟩ : (G β h₀).Stratum Finset.univ) := by
    ext s
    constructor
    · intro hs
      exact ⟨⟨s.1, hs⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  rw [this]
  have := isCompact_iff_compactSpace.1 (WaterFilling.isCompact_faceSet a {β})
  exact isCompact_range (continuous_subtype_val.subtype_mk _)

/-- The base type. -/
abbrev K := ↥(base β a h₀)

instance : CompactSpace (K β a h₀) := isCompact_iff_compactSpace.1 (isCompact_base β a h₀)

/-- The tangential embedding of the base. -/
def e (s : K β a h₀) : Tan (Iβ β).1 → ℝ := tan (Iβ β).1 s.1.1

theorem continuous_e : Continuous (e β a h₀) :=
  continuous_pi fun j =>
    (continuous_apply j.1).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem e_injective : Function.Injective (e β a h₀) := by
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hj : j = β
  · subst hj
    rw [stratum_coord_zero, stratum_coord_zero]
  · exact congrFun hst ⟨j, fun h => hj (Finset.mem_singleton.1 h)⟩

theorem mem_faceSet_liftPoint {t : Tan (Iβ β).1 → ℝ} (ht : ∀ j, t j ∈ Icc 0 a) (ha : 0 ≤ a) :
    liftPoint (Iβ β).1 t ∈ WaterFilling.faceSet a {β} := by
  refine ⟨fun j _ => ?_, fun i hi => ?_⟩
  · rw [liftPoint_apply]
    split_ifs with h
    · exact ⟨le_rfl, ha⟩
    · exact ht ⟨j, h⟩
  · have hi' : i ∈ (Iβ β).1 := hi
    rw [liftPoint_apply, dif_pos hi']

theorem mem_range_e_iff (ha : 0 ≤ a) (t : Tan (Iβ β).1 → ℝ) :
    t ∈ range (e β a h₀) ↔ ∀ j, t j ∈ Icc 0 a := by
  constructor
  · rintro ⟨s, rfl⟩ j
    exact s.2.1 j.1 (mem_univ _)
  · intro ht
    refine ⟨⟨⟨liftPoint (Iβ β).1 t, mem_stratumSet_univ_of_mem_faceSet β a h₀
      (mem_faceSet_liftPoint β a ht ha)⟩, mem_faceSet_liftPoint β a ht ha⟩, ?_⟩
    exact tan_liftPoint _ _

variable (ha : 0 < a) (hu_cont : Continuous u) (c : ℝ) (hc : 0 < c)
  (hu_lb : ∀ y ∈ piBox d (Icc 0 a), c ≤ u y)

include ha hu_lb in
theorem unitT_ge {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) : c ≤ unitT β u t :=
  hu_lb _ (mem_faceSet_liftPoint β a ((mem_range_e_iff β a h₀ ha.le t).1 ht) ha.le).1

include ha hu_lb hc in
theorem unitT_pos {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) : 0 < unitT β u t :=
  hc.trans_le (unitT_ge β u a h₀ ha c hu_lb ht)

include ha hu_lb hc in
theorem lam_pos {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) (j : Nrm (Iβ β).1) :
    0 < lam β u t j :=
  inv_pos.2 (Real.sqrt_pos.2 (unitT_pos β u a h₀ ha c hc hu_lb ht))

include hc in
theorem Lb_pos : 0 < Lb c := inv_pos.2 (Real.sqrt_pos.2 hc)

include ha hu_lb hc in
theorem lam_le_Lb {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) (j : Nrm (Iβ β).1) :
    lam β u t j ≤ Lb c :=
  inv_anti₀ (Real.sqrt_pos.2 hc) (Real.sqrt_le_sqrt (unitT_ge β u a h₀ ha c hu_lb ht))

include ha hu_lb hc in
theorem lam_sq {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) (j : Nrm (Iβ β).1) :
    lam β u t j ^ 2 = (unitT β u t)⁻¹ := by
  unfold lam
  rw [inv_pow, Real.sq_sqrt (unitT_pos β u a h₀ ha c hc hu_lb ht).le]

include hu_cont in
theorem continuous_unitT : Continuous (unitT β u) := hu_cont.comp (continuous_liftPoint _)

include hu_cont in
theorem measurable_lam : Measurable (lam β u) :=
  measurable_pi_lambda _ fun _ =>
    (Real.continuous_sqrt.comp (continuous_unitT β u hu_cont)).measurable.inv

include ha hu_cont hc hu_lb in
theorem continuousOn_lam : ContinuousOn (lam β u) (range (e β a h₀)) := by
  refine continuousOn_pi.2 fun _ => ?_
  refine ContinuousOn.inv₀ (Real.continuous_sqrt.comp (continuous_unitT β u hu_cont)).continuousOn
    fun t ht => ?_
  exact (Real.sqrt_pos.2 (unitT_pos β u a h₀ ha c hc hu_lb ht)).ne'

/-! ### The series from the face series -/

variable (ϕ φ : (Fin d → ℝ) → ℝ) (O : OriginalFaceSeries a ϕ φ (Iβ β)) (b b' : ℝ) (hb : 0 < b)
  (hbb' : b < b') (hb'ρ : Lb c * b' ≤ O.ρ) (hba : Lb c * b ≤ a)
  (ϕ' : (Fin d → ℝ) → ℝ) (hϕ'eq : ∀ w ∈ piBox d (Icc 0 a), ϕ' w = ϕ w)

/-- The base point as a point of the closed face. -/
def toFaceK (s : K β a h₀) : ↥(WaterFilling.faceSet a (Iβ β).1) := ⟨s.1.1, s.2⟩

theorem continuous_toFaceK : Continuous (toFaceK β a h₀) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The widths in box coordinates. -/
noncomputable def wid (s : K β a h₀) (i : Fin (nI (Iβ β) + 1)) : ℝ :=
  lam β u (e β a h₀ s) (σI (Iβ β) i)

include ha hu_cont hc hu_lb in
theorem continuous_wid (i : Fin (nI (Iβ β) + 1)) : Continuous fun s => wid β u a h₀ s i :=
  (continuous_apply _).comp
    ((continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb).comp_continuous (continuous_e β a h₀)
      fun s => mem_range_self s)

include ha hc hu_lb in
theorem abs_wid_le (s : K β a h₀) (i : Fin (nI (Iβ β) + 1)) : |wid β u a h₀ s i| ≤ Lb c := by
  unfold wid
  rw [abs_of_pos (lam_pos β u a h₀ ha c hc hu_lb (mem_range_self s) _)]
  exact lam_le_Lb β u a h₀ ha c hc hu_lb (mem_range_self s) _

include hc in
theorem norm_wid_mul_le (hwid : ∀ (s : K β a h₀) i, |wid β u a h₀ s i| ≤ Lb c) (s : K β a h₀)
    (v : Fin (nI (Iβ β) + 1) → ℝ) : ‖fun i => wid β u a h₀ s i * v i‖ ≤ Lb c * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Lb_pos c hc).le (norm_nonneg _))).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hwid s i) ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm v i))
    (abs_nonneg _) (Lb_pos c hc).le

include hb in
theorem norm_le_of_mem_box {v : Fin (nI (Iβ β) + 1) → ℝ}
    (hv : v ∈ NormalisedBox.box (ι := Fin (nI (Iβ β) + 1)) b) :
    ‖v‖ ≤ b := by
  refine (pi_norm_le_iff_of_nonneg hb.le).2 fun i => ?_
  have := hv i (mem_univ _)
  rw [mem_Ioc] at this
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith, this.2⟩

/-- The core parametrisation is the original normal map at the scaled normal variable. -/
theorem Φ_eq_orig (s : K β a h₀) (v : Fin (nI (Iβ β) + 1) → ℝ) :
    Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u) (s, v) =
      originalNormalMap (Iβ β) s.1.1 fun i => wid β u a h₀ s i * v i := by
  funext j
  rw [Φ_apply]
  unfold originalNormalMap
  by_cases hj : j ∈ (Iβ β).1
  · rw [dif_pos hj, dif_pos hj]
    have hjβ : j = β := Finset.mem_singleton.1 hj
    have h0 : s.1.1 j = 0 := by rw [hjβ]; exact stratum_coord_zero β h₀ s.1
    rw [h0, zero_add]
    simp only [wid, Equiv.apply_symm_apply]
  · rw [dif_neg hj, dif_neg hj]
    rfl

include ha hu_cont hc hu_lb hbb' hb'ρ in
/-- The prior series in the normalised normal variable. -/
noncomputable def Fϕ : UniformSeriesFamily (K β a h₀) (nI (Iβ β) + 1) b' :=
  (O.Fϕ.precomp (toFaceK β a h₀) (continuous_toFaceK β a h₀)).rescale (wid β u a h₀)
    (continuous_wid β u a h₀ ha hu_cont c hc hu_lb) (fun _ => Lb c)
    (abs_wid_le β u a h₀ ha c hc hu_lb) (fun _ => (Lb_pos c hc).le) (hb.le.trans hbb'.le)
    fun _ => hb'ρ

include ha hu_cont hc hu_lb hbb' hb'ρ in
/-- The observable series in the normalised normal variable. -/
noncomputable def Fφ : UniformSeriesFamily (K β a h₀) (nI (Iβ β) + 1) b' :=
  (O.Fφ.precomp (toFaceK β a h₀) (continuous_toFaceK β a h₀)).rescale (wid β u a h₀)
    (continuous_wid β u a h₀ ha hu_cont c hc hu_lb) (fun _ => Lb c)
    (abs_wid_le β u a h₀ ha c hc hu_lb) (fun _ => (Lb_pos c hc).le) (hb.le.trans hbb'.le)
    fun _ => hb'ρ

include ha hu_cont hc hu_lb hbb' hb'ρ in
theorem hϕ_eq (s : K β a h₀) {v : Fin (nI (Iβ β) + 1) → ℝ}
    (hv : v ∈ NormalisedBox.box (ι := Fin (nI (Iβ β) + 1)) b) :
    ϕ (Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u) (s, v)) =
      evalF ((Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).f s) v := by
  rw [Φ_eq_orig, Fϕ, UniformSeriesFamily.rescale_f, evalF_rescale, UniformSeriesFamily.precomp_f]
  refine O.hϕ_eq (toFaceK β a h₀ s) _ ?_
  calc ‖fun i => wid β u a h₀ s i * v i‖
      ≤ Lb c * ‖v‖ := norm_wid_mul_le β u a h₀ c hc (abs_wid_le β u a h₀ ha c hc hu_lb) s v
    _ ≤ Lb c * b := mul_le_mul_of_nonneg_left (norm_le_of_mem_box β b hb hv) (Lb_pos c hc).le
    _ < Lb c * b' := mul_lt_mul_of_pos_left hbb' (Lb_pos c hc)
    _ ≤ O.ρ := hb'ρ

include ha hu_cont hc hu_lb hbb' hb'ρ in
theorem hφ_eq (s : K β a h₀) {v : Fin (nI (Iβ β) + 1) → ℝ} (hv : ‖v‖ < b') :
    φ (Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u) (s, v)) =
      evalF ((Fφ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).f s) v := by
  rw [Φ_eq_orig, Fφ, UniformSeriesFamily.rescale_f, evalF_rescale, UniformSeriesFamily.precomp_f]
  refine O.hφ_eq (toFaceK β a h₀ s) _ ?_
  calc ‖fun i => wid β u a h₀ s i * v i‖
      ≤ Lb c * ‖v‖ := norm_wid_mul_le β u a h₀ c hc (abs_wid_le β u a h₀ ha c hc hu_lb) s v
    _ < Lb c * b' := mul_lt_mul_of_pos_left hv (Lb_pos c hc)
    _ ≤ O.ρ := hb'ρ

include ha hc hu_lb hb hba in
theorem image_subset_box :
    image (Iβ β).1 (e β a h₀) (lam β u) b ⊆ piBox d (Icc 0 a) := by
  intro w hw
  obtain ⟨ht, hf⟩ := hw
  rw [split_apply] at ht hf
  intro j _
  by_cases hj : j ∈ (Iβ β).1
  · have := hf ⟨j, hj⟩
    refine ⟨this.1.le, this.2.trans ?_⟩
    calc lam β u (fun i : Tan (Iβ β).1 => w i.1) ⟨j, hj⟩ * b
        ≤ Lb c * b := mul_le_mul_of_nonneg_right (lam_le_Lb β u a h₀ ha c hc hu_lb ht _) hb.le
      _ ≤ a := hba
  · exact (mem_range_e_iff β a h₀ ha.le _).1 ht ⟨j, hj⟩

include ha hc hu_lb in
theorem hnorm {t : Tan (Iβ β).1 → ℝ} (ht : t ∈ range (e β a h₀)) :
    unitT β u t * (tanUnit (kS β) (Iβ β).1 t *
      ∏ j : Nrm (Iβ β).1, lam β u t j ^ (2 * kS β j.1)) = 1 := by
  have h1 : tanUnit (kS β) (Iβ β).1 t = 1 := by
    unfold tanUnit
    refine Finset.prod_eq_one fun j _ => ?_
    rw [kS_ne β (tan_ne β j), mul_zero, pow_zero]
  have h2 : ∏ j : Nrm (Iβ β).1, lam β u t j ^ (2 * kS β j.1) = (unitT β u t)⁻¹ := by
    rw [Fintype.prod_unique]
    have hd : (default : Nrm (Iβ β).1).1 = β := rfl
    rw [hd, kS_self, mul_one, lam_sq β u a h₀ ha c hc hu_lb ht]
  rw [h1, h2, one_mul, mul_inv_cancel₀ (unitT_pos β u a h₀ ha c hc hu_lb ht).ne']

include ha hu_cont hc hu_lb hbb' hb'ρ hba hϕ'eq in
/-- ★ **The weighted data of the singleton chart**, for a prior `ϕ'` agreeing with the series'
prior `ϕ` on the box. -/
noncomputable def data :
    WData (kS β) (Iβ β).1 (nI (Iβ β)) (K β a h₀) (piBox d (Icc 0 a)) ϕ' φ where
  σ := σI (Iβ β)
  e := e β a h₀
  he := continuous_e β a h₀
  he_inj := e_injective β a h₀
  lamT := lam β u
  hlamT := measurable_lam β u hu_cont
  hlam_cont := continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb
  hpos := fun _ ht j => lam_pos β u a h₀ ha c hc hu_lb ht j
  unit := unitT β u
  β := 1
  hnorm := fun _ ht => hnorm β u a h₀ ha c hc hu_lb ht
  b := b
  b' := b'
  hb := hb
  hbb' := hbb'
  hW := image_subset_box β u a h₀ ha c hc hu_lb b hb hba
  Fϕ := Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ
  Fφ := Fφ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ
  hϕ_eq := fun s _ hv =>
    (hϕ'eq _ (image_subset_box β u a h₀ ha c hc hu_lb b hb hba
      (mem_image_Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u)
        (fun _ ht j => lam_pos β u a h₀ ha c hc hu_lb ht j) s hv))).trans
      (hϕ_eq β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ s hv)
  hφ_eq := fun s _ hv => hφ_eq β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ s hv

/-! ### The localisation datum, the core and the core decomposition -/

variable (hϕm : Measurable ϕ') (hϕ0 : ∀ w, 0 ≤ ϕ' w) (hφm : Measurable φ)
  (hφint : Integrable φ ((volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt (hS β h₀) w * ϕ' w)))

include hu_cont hc hu_lb hφint in
/-- The localisation datum: the weighted prior measure on the box, the chart phase, the
observable. -/
noncomputable def locData : LocalisationData (Fin d → ℝ) where
  μ := (volume.restrict (piBox d (Icc 0 a))).withDensity
    fun w => ENNReal.ofReal (wgt (hS β h₀) w * ϕ' w)
  phase := Kc β u
  obs := φ
  phase_measurable := hu_cont.measurable.mul ((measurable_pi_apply β).pow_const 2)
  phase_nonneg := by
    have h1 : ∀ᵐ y ∂((volume.restrict (piBox d (Icc 0 a))).withDensity
        fun w => ENNReal.ofReal (wgt (hS β h₀) w * ϕ' w)), y ∈ piBox d (Icc 0 a) :=
      mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
        (mem_ae_iff.1 (ae_restrict_mem (measurableSet_W a))))
    exact h1.mono fun y hy => mul_nonneg (hc.le.trans (hu_lb y hy)) (sq_nonneg _)
  obs_integrable := hφint
  δ := 1
  δ_pos := one_pos

include hu_cont hc hu_lb hφint hu_tan in
theorem locData_phase (y : Fin d → ℝ) :
    (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).phase y =
      unitT β u (tan (Iβ β).1 y) * CoordModel.phase d (kS β) y := by
  change Kc β u y = _
  rw [unitT_tan β u hu_tan, coordPhase_kS]
  rfl

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- The weighted core of the singleton chart. -/
noncomputable def core :=
  NormalisedBox.wcore (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
    (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
    (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl

include ha hu_cont hc hu_lb hu_tan hb hφint in
/-- Off the collar the phase is at least `b²`, a.e. -/
theorem gap_aux :
    ∀ᵐ z ∂(locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ.restrict
      (image (Iβ β).1 (e β a h₀) (lam β u) b)ᶜ,
      b ^ 2 ≤ (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).phase z := by
  rw [ae_restrict_iff' (measurableSet_image (Iβ β).1 b
    (measurableEmbedding_e (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (e_injective β a h₀))
    (measurable_lam β u hu_cont)).compl]
  have h1 : ∀ᵐ y ∂(locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ, y ∈ piBox d (Icc 0 a) :=
    mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
      (mem_ae_iff.1 (ae_restrict_mem (measurableSet_W a))))
  have h2 : ∀ᵐ y ∂(locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ, y β ≠ 0 :=
    mem_ae_iff.2 ((withDensity_absolutelyContinuous _ _)
      (mem_ae_iff.1 (ae_restrict_of_ae (ae_coord_ne_zero.mono fun y hy => hy β))))
  filter_upwards [h1, h2] with y hy hyβ hnot
  have hyb : 0 < y β := lt_of_le_of_ne (hy β (mem_univ _)).1 (Ne.symm hyβ)
  have htan : tan (Iβ β).1 y ∈ range (e β a h₀) :=
    (mem_range_e_iff β a h₀ ha.le _).2 fun j => hy j.1 (mem_univ _)
  have hgt : lam β u (tan (Iβ β).1 y) default * b < y β := by
    by_contra hle
    push Not at hle
    refine hnot ⟨htan, fun j => ?_⟩
    have hj : j = default := Unique.eq_default j
    subst hj
    exact ⟨hyb, hle⟩
  have hu_pos : 0 < u y := hc.trans_le (hu_lb y hy)
  have hlam : lam β u (tan (Iβ β).1 y) default ^ 2 = (u y)⁻¹ := by
    rw [lam_sq β u a h₀ ha c hc hu_lb htan, unitT_tan β u hu_tan]
  have key : (lam β u (tan (Iβ β).1 y) default * b) ^ 2 < y β ^ 2 :=
    pow_lt_pow_left₀ hgt (mul_pos (lam_pos β u a h₀ ha c hc hu_lb htan default) hb).le two_ne_zero
  rw [mul_pow, hlam] at key
  change b ^ 2 ≤ u y * y β ^ 2
  have := mul_lt_mul_of_pos_left key hu_pos
  rw [← mul_assoc, mul_inv_cancel₀ hu_pos.ne', one_mul] at this
  exact this.le

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- The one-core decomposition: the collar and the phase-gap tail. -/
noncomputable def cores :
    AnalyticCoreDecomposition (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint) 1
      (fun _ => K β a h₀) (fun _ => nI (Iβ β)) 1 where
  core := fun _ => (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ.restrict
    (image (Iβ β).1 (e β a h₀) (lam β u) b)
  tail := (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint).μ.restrict
    (image (Iβ β).1 (e β a h₀) (lam β u) b)ᶜ
  measure_eq := by
    rw [Fin.sum_univ_one, Measure.restrict_add_restrict_compl (measurableSet_image (Iβ β).1 b
      (measurableEmbedding_e (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (e_injective β a h₀))
      (measurable_lam β u hu_cont))]
  δ₀ := b ^ 2
  δ₀_pos := pow_pos hb 2
  gap := gap_aux β u hu_tan a h₀ ha hu_cont c hc hu_lb φ b hb ϕ' hφint
  chart := fun _ => core β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ'
     hϕ'eq hϕm hϕ0
    hφint

/-! ### The frame -/

theorem mem_amb_singleton_univ (j : Fin d) :
    j ∈ ChartModel.amb d {β} Finset.univ ↔ j ∈ (Iβ β).1 := by
  rw [ChartModel.mem_amb]
  constructor
  · rintro ⟨hj, _⟩
    exact hj
  · intro hj
    exact ⟨hj, Finset.mem_univ _⟩

/-- The box coordinates as the ambient index set of the deepest stratum. -/
noncomputable def σ' : Fin (nI (Iβ β) + 1) ≃ ↥(ChartModel.amb d {β} Finset.univ) :=
  (σI (Iβ β)).trans (Equiv.subtypeEquivRight fun j => (mem_amb_singleton_univ β j).symm)

/-- The scalar width at a base point. -/
noncomputable def lamS (s : K β a h₀) : ℝ := (Real.sqrt (unitT β u (e β a h₀ s)))⁻¹

include ha hc hu_lb in
theorem lamS_pos (s : K β a h₀) : 0 < lamS β u a h₀ s :=
  lam_pos β u a h₀ ha c hc hu_lb (mem_range_self s) default

include ha hc hu_lb in
/-- The frame `v ↦ λ(s) v e_β`, as a linear equivalence. -/
noncomputable def frameLin (s : K β a h₀) :
    (Fin (nI (Iβ β) + 1) → ℝ) ≃ₗ[ℝ] normalSpace d (ChartModel.amb d {β} Finset.univ) :=
  ((LinearEquiv.funCongrLeft ℝ ℝ (σ' β)).symm.trans
    (LinearEquiv.piCongrRight fun _ : ↥(ChartModel.amb d {β} Finset.univ) =>
      LinearEquiv.smulOfNeZero ℝ ℝ (lamS β u a h₀ s) (lamS_pos β u a h₀ ha c hc hu_lb s).ne')).trans
    (Module.Basis.span
      (linearIndependent_basisVec_restrict d (ChartModel.amb d {β} Finset.univ))).equivFun.symm

include ha hc hu_lb in
theorem frameLin_apply (s : K β a h₀) (v : Fin (nI (Iβ β) + 1) → ℝ) :
    frameLin β u a h₀ ha c hc hu_lb s v =
      ∑ j : ↥(ChartModel.amb d {β} Finset.univ), (lamS β u a h₀ s * v ((σ' β).symm j)) •
        Module.Basis.span (linearIndependent_basisVec_restrict d (ChartModel.amb d {β} Finset.univ))
          j := by
  change (Module.Basis.span
    (linearIndependent_basisVec_restrict d (ChartModel.amb d {β} Finset.univ))).equivFun.symm
      (fun j => lamS β u a h₀ s * v ((σ' β).symm j)) = _
  rw [Module.Basis.equivFun_symm_apply]

include ha hc hu_lb in
theorem coe_frameLin_apply (s : K β a h₀) (v : Fin (nI (Iβ β) + 1) → ℝ) (i : Fin d) :
    ((frameLin β u a h₀ ha c hc hu_lb s v : normalSpace d (ChartModel.amb d {β} Finset.univ)) :
      Amb d).ofLp i =
      if h : i ∈ ChartModel.amb d {β} Finset.univ then lamS β u a h₀ s * v ((σ' β).symm ⟨i, h⟩)
      else 0 := by
  rw [frameLin_apply, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply]
  have hterm : ∀ j : ↥(ChartModel.amb d {β} Finset.univ),
      ((((lamS β u a h₀ s * v ((σ' β).symm j)) • Module.Basis.span
        (linearIndependent_basisVec_restrict d (ChartModel.amb d {β} Finset.univ)) j :
          normalSpace d (ChartModel.amb d {β} Finset.univ)) : Amb d)).ofLp i =
        (lamS β u a h₀ s * v ((σ' β).symm j)) * if i = j.1 then 1 else 0 := by
    intro j
    rw [Submodule.coe_smul, Module.Basis.span_apply]
    change ((lamS β u a h₀ s * v ((σ' β).symm j)) • basisVec d j.1).ofLp i = _
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, basisVec_ofLp]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  by_cases hi : i ∈ ChartModel.amb d {β} Finset.univ
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      exact fun h => hj (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    exact fun h => hi (h ▸ j.2)

include ha hc hu_lb in
/-- The frame `ℝ ≃L N_β` at a base point. -/
noncomputable def frame (s : K β a h₀) :
    (Fin (nI (Iβ β) + 1) → ℝ) ≃L[ℝ] normalSpace d (ChartModel.amb d {β} Finset.univ) :=
  (frameLin β u a h₀ ha c hc hu_lb s).toContinuousLinearEquiv

include ha hc hu_lb in
theorem coe_frame_apply (s : K β a h₀) (v : Fin (nI (Iβ β) + 1) → ℝ) (i : Fin d) :
    ((frame β u a h₀ ha c hc hu_lb s v : normalSpace d (ChartModel.amb d {β} Finset.univ)) :
      Amb d).ofLp i =
      if h : i ∈ ChartModel.amb d {β} Finset.univ then lamS β u a h₀ s * v ((σ' β).symm ⟨i, h⟩)
      else 0 :=
  coe_frameLin_apply β u a h₀ ha c hc hu_lb s v i

include ha hc hu_lb in
/-- ★ **The tubular identity along the frame.** -/
theorem Φ_eq_frame (s : K β a h₀) (v : Fin (nI (Iβ β) + 1) → ℝ) :
    Φ (Iβ β).1 (σI (Iβ β)) (e β a h₀) (lam β u) (s, v) =
      (N β h₀).Φ Finset.univ s.1 (frame β u a h₀ ha c hc hu_lb s v) := by
  change _ = fun i => s.1.1 i + ((frame β u a h₀ ha c hc hu_lb s v :
    normalSpace d (ChartModel.amb d {β} Finset.univ)) : Amb d).ofLp i
  funext j
  rw [Φ_apply, coe_frame_apply]
  by_cases hj : j ∈ (Iβ β).1
  · have hj' : j ∈ ChartModel.amb d {β} Finset.univ := (mem_amb_singleton_univ β j).2 hj
    rw [dif_pos hj, dif_pos hj']
    have h0 : s.1.1 j = 0 := by
      rw [Finset.mem_singleton.1 hj]
      exact stratum_coord_zero β h₀ s.1
    rw [h0, zero_add]
    rfl
  · have hj' : j ∉ ChartModel.amb d {β} Finset.univ := fun h => hj ((mem_amb_singleton_univ β
     j).1 h)
    rw [dif_neg hj, dif_neg hj', add_zero]
    rfl

/-! ### The certificate and the expansion -/

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- ★★ **The resolved certificate of the singleton chart**: one core on the closed face, the
phase-gap tail, the frame `v ↦ λ(s) v e_β`; prior `|y_β|^{h₀} ϕ`. -/
noncomputable def cert :
    ResolvedCertificate (G β h₀) (N β h₀) (piBox d (Icc 0 a)) (Kc β u)
      (fun w => wgt (hS β h₀) w * ϕ' w) φ where
  L := locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint
  obs_eq := rfl
  phase_eq := rfl
  transport := Measure.map_id
  M := 1
  n := fun _ => nI (Iβ β)
  strat := fun _ => Finset.univ
  base := fun _ => base β a h₀
  isCompact_base := fun _ => isCompact_base β a h₀
  β := 1
  β_pos := one_pos
  cores := cores β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm
     hϕ0 hφint
  T := fun _ => NormalisedBox.wpresentation (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
    (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
    (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
    (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl
  frame := fun _ s => frame β u a h₀ ha c hc hu_lb s
  Φ_eq := fun _ s v => Φ_eq_frame β u a h₀ ha c hc hu_lb s v

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφint in
/-- ★★ **The coefficient certificate**: density family `J H L · fϕ`, observable jets `fφ`. -/
noncomputable def coeffCert :
    (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
      hφint).CoefficientCertificate where
  cc := fun _ s γ => JW (hS β h₀) (Iβ β).1 (e β a h₀) (lam β u) s *
    (Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).f s γ
  cc_abs := fun _ s =>
    ((Fϕ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).smul
      (JW (hS β h₀) (Iβ β).1 (e β a h₀) (lam β u))
      (continuous_JW (hS β h₀) (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (lam β u)
        (continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb)) _
      (abs_JW_le (hS β h₀) (Iβ β).1 (e β a h₀) (continuous_e β a h₀) (lam β u)
        (continuousOn_lam β u a h₀ ha hu_cont c hc hu_lb))).absSummableAt_of_le hb.le hbb'.le s
  jet_abs := fun _ s => by
    have h := NormalisedBox.jetFamily_obsFibre_w (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    exact (congrArg (fun f => AbsSummableAt f b) h).mpr
      ((Fφ β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ).absSummableAt_of_le hb.le
        hbb'.le s)
  datum_eq := fun _ s => by
    have h := NormalisedBox.jetFamily_obsFibre_w (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    have h1 := NormalisedBox.toEta_wcore_x (hkI β) (measurableSet_W a) hϕm (fun w _ => hϕ0 w)
      (locData β u a h₀ hu_cont c hc hu_lb φ ϕ' hφint)
      (data β u a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq) (h := hS β h₀) rfl
      (locData_phase β u hu_tan a h₀ hu_cont c hc hu_lb φ ϕ' hφint) rfl s
    exact h1.trans (congrArg (CoeffFamily.conv _) h.symm)

include ha hu_cont hc hu_lb hu_tan hbb' hb'ρ hba hϕ'eq hϕm hϕ0 hφm hφint in
/-- ★★★ **The coordinate-free expansion of the singleton chart**: the weighted integral
`∫_{[0,a]^d} φ · |y_β|^{h₀} ϕ · e^{−n u(y) y_β²}` has the coordinate-free expansion on the chart
strata, with produced certificates and the spectrum of one normal coordinate. -/
theorem hasCoordFreeExpansion_singleton :
    (N β h₀).HasCoordFreeExpansion
      (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
        hφint).stratumMeasure
      (coeffCert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
        hφint).field
      (spectrumLe (commonQ (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba
        ϕ' hϕ'eq hϕm hϕ0 hφint).cores.k) (commonD (cert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ
     φ O b b'
        hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0 hφint).n))
      (piBox d (Icc 0 a)) (Kc β u) (fun w => wgt (hS β h₀) w * ϕ' w) φ :=
  (coeffCert β u hu_tan a h₀ ha hu_cont c hc hu_lb ϕ φ O b b' hb hbb' hb'ρ hba ϕ' hϕ'eq hϕm hϕ0
    hφint).hasCoordFreeExpansion_le (hu_cont.measurable.mul ((measurable_pi_apply β).pow_const 2))
    ((measurable_wgt _).mul hϕm) (fun w => mul_nonneg (wgt_nonneg _ _) (hϕ0 w)) hφm

end SingletonChart

end Grammar
