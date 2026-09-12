/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.DiagonalBoxTransport
import Grammar.ParameterisedSeriesDatum
import Grammar.CoordinateResolvedGeometry
import Grammar.CoreNormalMomentRepresentation

/-!
# The normalised box core at a coordinate stratum (CCCXXI)

Consult #96 unit 3b: the parameterised normal-rescaling PRODUCER. On the coordinate model
`ℝ^d` with phase `K(w) = ∏_j w_j^{2k_j}`, a compact base `B = range e` inside the stratum
`S_I` (tangential coordinates `e : K → ℝ^{Iᶜ}`), positive normal widths `λ(t) = lamT t` with
the normalisation `t_I(t) ∏_{j∈I} λ_j(t)^{2k_j} = β` (`t_I(t) = ∏_{j∉I} t_j^{2k_j}`), and
prior/observable given near the base by uniform normal-series families in the NORMALISED normal
variables, we construct

* `NormalisedBox.core : CorePresentation L (L.μ.restrict image) K n β` — Dirac-free base
  measure `ν_B` (coordinate Lebesgue on `B`), normal box `(0,b]^{n+1}`,
  `Φ(s,v) = s + Σ λ_j(s) v_j e_j`,
  density `c(s,v) = J(s)·ϕ(Φ(s,v))` with the normal Jacobian `J(s) = ∏_j λ_j(s)` (realised through a
  bounded clamped representative), amplitude datum `(J·fϕ) ⋆ fφ`; the `transport` field is the
  exact identity of CCCXX, `phase_normal` is the normalisation identity, `amplitude_eq` the scaled
  product rule;
* `NormalisedBox.presentation : CoreNormalMomentPresentation core` from the observable's series
  (radius `b' > b`, bound `cBound = J_max · Σ M_γ b^{|γ|}`);
* the coefficient identities `toEta_x` and `jetFamily_obsFibre` (Taylor family = observable family).

Also the rescaling adapter from series in the ORIGINAL normal variables (`CoeffFamily.rescale`,
`UniformSeriesFamily.rescale`, `UniformSeriesFamily.smul`): `(rescale a f)_γ = f_γ ∏ a_j^{γ_j}` is
the coefficient family of `v ↦ f(a·v)`, with majorant `M_γ ∏ L_j^{γ_j}` summable at `b'` when
`L_j b' ≤ ρ` — the radius shrink of consult #96 §2.4.

This unit does not yet assemble a `ResolvedCertificate`: the collar decomposition (unit 4) sums
such cores with a phase-gap tail. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

/-! ### Rescaling coefficient families -/

namespace CoeffFamily

variable {d : ℕ}

/-- `(rescale a f)_γ = f_γ ∏ a_i^{γ_i}`: the coefficient family of `v ↦ f(a·v)`. -/
noncomputable def rescale (a : Fin d → ℝ) (f : CoeffFamily d) : CoeffFamily d :=
  fun γ => f γ * ∏ i, a i ^ γ i

theorem evalF_const_mul (a : ℝ) (f : CoeffFamily d) (v : Fin d → ℝ) :
    evalF (fun γ => a * f γ) v = a * evalF f v := by
  unfold evalF
  simp_rw [mul_assoc]
  exact tsum_mul_left

theorem evalF_rescale (a : Fin d → ℝ) (f : CoeffFamily d) (v : Fin d → ℝ) :
    evalF (rescale a f) v = evalF f fun i => a i * v i := by
  unfold evalF rescale mono
  refine tsum_congr fun γ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _).symm

theorem abs_rescale_le {a L : Fin d → ℝ} (hL : ∀ i, |a i| ≤ L i) (f : CoeffFamily d)
    (γ : Fin d → ℕ) : |rescale a f γ| ≤ |f γ| * ∏ i, L i ^ γ i := by
  unfold rescale
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_)
    (abs_nonneg _)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hL i) _

theorem absSummableAt_rescale {f : CoeffFamily d} {ρ : ℝ} (hρ : AbsSummableAt f ρ)
    {a L : Fin d → ℝ} (hL : ∀ i, |a i| ≤ L i) (hL0 : ∀ i, 0 ≤ L i) {b : ℝ} (hb : 0 ≤ b)
    (hbL : ∀ i, L i * b ≤ ρ) : AbsSummableAt (rescale a f) b := by
  unfold AbsSummableAt at hρ ⊢
  refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) hρ
  calc |rescale a f γ| * b ^ (∑ i, γ i)
      ≤ (|f γ| * ∏ i, L i ^ γ i) * b ^ (∑ i, γ i) :=
        mul_le_mul_of_nonneg_right (abs_rescale_le hL f γ) (pow_nonneg hb _)
    _ = |f γ| * ∏ i, (L i * b) ^ γ i := by
        rw [← Finset.prod_pow_eq_pow_sum, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _).symm
    _ ≤ |f γ| * ρ ^ (∑ i, γ i) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => by
          exact pow_nonneg (mul_nonneg (hL0 i) hb) _) fun i _ => ?_) (abs_nonneg _)
        exact pow_le_pow_left₀ (mul_nonneg (hL0 i) hb) (hbL i) _

end CoeffFamily

namespace UniformSeriesFamily

variable {X : Type*} [TopologicalSpace X] {d : ℕ} {ρ : ℝ} (F : UniformSeriesFamily X d ρ)

/-- Rescaling a uniform family by parameter-dependent widths `a x`, bounded by `L`: a uniform
family at every scale `b'` with `L_i b' ≤ ρ`. -/
noncomputable def rescale (a : X → Fin d → ℝ) (ha : ∀ i, Continuous fun x => a x i) (L : Fin d → ℝ)
    (hL : ∀ x i, |a x i| ≤ L i) (hL0 : ∀ i, 0 ≤ L i) {b' : ℝ} (hb' : 0 ≤ b')
    (hbL : ∀ i, L i * b' ≤ ρ) : UniformSeriesFamily X d b' where
  f x := CoeffFamily.rescale (a x) (F.f x)
  M γ := F.M γ * ∏ i, L i ^ γ i
  continuous_coeff γ :=
    (F.continuous_coeff γ).mul (continuous_finsetProd _ fun i _ => (ha i).pow _)
  abs_le x γ := (abs_rescale_le (hL x) _ γ).trans
    (mul_le_mul_of_nonneg_right (F.abs_le x γ) (Finset.prod_nonneg fun i _ => pow_nonneg (hL0 i) _))
  M_abs := by
    have h := F.M_abs
    unfold AbsSummableAt at h ⊢
    refine Summable.of_nonneg_of_le (fun γ => by positivity) (fun γ => ?_) h
    calc |F.M γ * ∏ i, L i ^ γ i| * b' ^ (∑ i, γ i)
        = |F.M γ| * ∏ i, (L i * b') ^ γ i := by
          rw [abs_mul, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum, mul_assoc,
            ← Finset.prod_mul_distrib]
          congr 1
          exact Finset.prod_congr rfl fun i _ => by rw [abs_pow, abs_of_nonneg (hL0 i), mul_pow]
      _ ≤ |F.M γ| * ρ ^ (∑ i, γ i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
          refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ =>
            pow_nonneg (mul_nonneg (hL0 i) hb') _) fun i _ => ?_) (abs_nonneg _)
          exact pow_le_pow_left₀ (mul_nonneg (hL0 i) hb') (hbL i) _

theorem rescale_f (a : X → Fin d → ℝ) (ha : ∀ i, Continuous fun x => a x i) (L : Fin d → ℝ)
    (hL : ∀ x i, |a x i| ≤ L i) (hL0 : ∀ i, 0 ≤ L i) {b' : ℝ} (hb' : 0 ≤ b')
    (hbL : ∀ i, L i * b' ≤ ρ) (x : X) :
    (F.rescale a ha L hL hL0 hb' hbL).f x = CoeffFamily.rescale (a x) (F.f x) := rfl

/-- Multiplying a uniform family by a bounded continuous scalar function. -/
noncomputable def smul (J : X → ℝ) (hJ : Continuous J) (Jb : ℝ) (hJb : ∀ x, |J x| ≤ Jb) :
    UniformSeriesFamily X d ρ where
  f x γ := J x * F.f x γ
  M γ := Jb * F.M γ
  continuous_coeff γ := hJ.mul (F.continuous_coeff γ)
  abs_le x γ := by
    rw [abs_mul]
    exact mul_le_mul (hJb x) (F.abs_le x γ) (abs_nonneg _) ((abs_nonneg _).trans (hJb x))
  M_abs := by
    have h := F.M_abs
    unfold AbsSummableAt at h ⊢
    refine (h.mul_left |Jb|).congr fun γ => ?_
    rw [abs_mul]
    ring

theorem smul_f (J : X → ℝ) (hJ : Continuous J) (Jb : ℝ) (hJb : ∀ x, |J x| ≤ Jb) (x : X)
    (γ : Fin d → ℕ) :
    (F.smul J hJ Jb hJb).f x γ = J x * F.f x γ := rfl

theorem evalF_smul_f (J : X → ℝ) (hJ : Continuous J) (Jb : ℝ) (hJb : ∀ x, |J x| ≤ Jb) (x : X)
    (v : Fin d → ℝ) :
    evalF ((F.smul J hJ Jb hJb).f x) v = J x * evalF (F.f x) v := by
  unfold evalF
  simp_rw [smul_f, mul_assoc]
  exact tsum_mul_left

end UniformSeriesFamily

/-! ### The normalised box core -/

namespace NormalisedBox

variable {d : ℕ} (k : Fin d → ℕ) (I : Finset (Fin d)) {n : ℕ} (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (lamT : (Tan I → ℝ) → (Nrm I → ℝ))

/-- The normal exponents in box coordinates. -/
def kι (i : Fin (n + 1)) : ℕ := k (σ i).1

/-- The normal Jacobian `J(s) = ∏_j λ_j(s)`. -/
noncomputable def J (s : K) : ℝ := ∏ j, lamT (e s) j

/-- The tangential phase unit `t_I(t) = ∏_{j∉I} t_j^{2k_j}`. -/
noncomputable def tanUnit (t : Tan I → ℝ) : ℝ := ∏ j : Tan I, t j ^ (2 * k j.1)

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem mem_image_Φ {b : ℝ} (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j) (s : K)
    {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) b) :
    Φ I σ e lamT (s, v) ∈ image I e lamT b := by
  rw [Φ, mem_image_symm]
  refine ⟨mem_range_self s, fun j => ?_⟩
  have hvj := hv (σ.symm j) (mem_univ _)
  rw [mem_Ioc] at hvj
  have hl := hpos (e s) (mem_range_self s) j
  exact ⟨mul_pos hl hvj.1, mul_le_mul_of_nonneg_left hvj.2 hl.le⟩

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- The phase identity along the parametrisation:
`K(Φ(s,v)) = t_I(e s) ∏_j λ_j^{2k_j} ∏_i v_i^{2kι_i}`. -/
theorem phase_Φ (s : K) (v : Fin (n + 1) → ℝ) :
    CoordModel.phase d k (Φ I σ e lamT (s, v)) =
      (tanUnit k I (e s) * ∏ j : Nrm I, lamT (e s) j ^ (2 * k j.1)) *
        ∏ i, v i ^ (2 * kι k I σ i) := by
  unfold CoordModel.phase
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ I),
    Finset.prod_subtype (p := (· ∈ I)) (F := inferInstance) (Finset.univ.filter (· ∈ I))
      (fun x => by simp) _,
    Finset.prod_subtype (p := fun x => ¬ x ∈ I) (F := inferInstance)
      (Finset.univ.filter fun x => ¬ x ∈ I) (fun x => by simp) _]
  have h1 : ∀ j : Nrm I, Φ I σ e lamT (s, v) j.1 ^ (2 * k j.1) =
      lamT (e s) j ^ (2 * k j.1) * v (σ.symm j) ^ (2 * k j.1) := fun j => by
    rw [Φ_apply, dif_pos j.2, mul_pow]
  have h2 : ∀ j : Tan I, Φ I σ e lamT (s, v) j.1 ^ (2 * k j.1) = e s j ^ (2 * k j.1) := fun j => by
    rw [Φ_apply, dif_neg j.2]
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_congr rfl fun j _ => h2 j,
    Finset.prod_mul_distrib]
  have h3 : ∏ j : Nrm I, v (σ.symm j) ^ (2 * k j.1) = ∏ i, v i ^ (2 * kι k I σ i) :=
    (Fintype.prod_equiv σ _ _ fun i => by rw [kι, Equiv.symm_apply_apply]).symm
  rw [h3, tanUnit]
  ring

end NormalisedBox

namespace NormalisedBox

variable {d : ℕ} (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (I : Finset (Fin d)) {n : ℕ}
  (σ : Fin (n + 1) ≃ Nrm I)
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (e : K → (Tan I → ℝ)) (he : Continuous e) (he_inj : Function.Injective e)
  (lamT : (Tan I → ℝ) → (Nrm I → ℝ)) (hlamT : Measurable lamT)
  (hlam_cont : ContinuousOn lamT (range e)) (hpos : ∀ t ∈ range e, ∀ j, 0 < lamT t j)
  (β : ℝ) (hnorm : ∀ t ∈ range e, tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β)
  (W : Set (Fin d → ℝ)) (hWm : MeasurableSet W) (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ)
  (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ)
  (b b' : ℝ) (hb : 0 < b) (hbb' : b < b')
  (hW : image I e lamT b ⊆ W) (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w)
  (Fϕ Fφ : UniformSeriesFamily K (n + 1) b')
  (hϕ_eq : ∀ s, ∀ v ∈ box (ι := Fin (n + 1)) b, ϕ (Φ I σ e lamT (s, v)) = evalF (Fϕ.f s) v)
  (hφ_eq : ∀ s (v : Fin (n + 1) → ℝ), ‖v‖ < b' → φ (Φ I σ e lamT (s, v)) = evalF (Fφ.f s) v)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
theorem continuous_J : Continuous (J I e lamT) :=
  continuous_finsetProd _ fun j _ =>
    (continuous_apply j).comp (hlam_cont.comp_continuous he fun s => mem_range_self s)

omit [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hpos in
theorem J_pos (s : K) : 0 < J I e lamT s :=
  Finset.prod_pos fun j _ => hpos (e s) (mem_range_self s) j

omit [MeasurableSpace K] [BorelSpace K] in
include he hlam_cont in
theorem exists_J_bound : ∃ C, ∀ s, |J I e lamT s| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_J I e he lamT hlam_cont).continuousOn
  exact ⟨C, fun s => by simpa using hC s (mem_univ s)⟩

omit [MeasurableSpace K] [BorelSpace K] in
/-- The Jacobian bound. -/
noncomputable def Jb : ℝ := (exists_J_bound I e he lamT hlam_cont).choose

omit [MeasurableSpace K] [BorelSpace K] in
theorem abs_J_le (s : K) : |J I e lamT s| ≤ Jb I e he lamT hlam_cont :=
  (exists_J_bound I e he lamT hlam_cont).choose_spec s

include he he_inj in
theorem measurableEmbedding_e : MeasurableEmbedding e :=
  (he.isClosedEmbedding he_inj).measurableEmbedding

include he he_inj in
theorem isFiniteMeasure_baseMeasure : IsFiniteMeasure (baseMeasure I e) := by
  refine ⟨?_⟩
  rw [baseMeasure, (measurableEmbedding_e I e he he_inj).comap_apply, image_univ,
    Measure.restrict_apply (measurableEmbedding_e I e he he_inj).measurableSet_range, inter_self]
  exact (isCompact_range he).measure_lt_top

/-- The density `c(s,v) = J(s) · ϕ̃(v)`, with the prior realised by its clamped series
representative (so that `c` is globally bounded; on the box it equals `J(s) ϕ(Φ(s,v))`). -/
noncomputable def c (p : K × (Fin (n + 1) → ℝ)) : ℝ :=
  J I e lamT p.1 * evalF (Fϕ.f p.1) (clamp b hb.le p.2)

/-- The amplitude datum `(J · fϕ) ⋆ fφ` as a continuous map into the data space. -/
noncomputable def xData : TangentialData K (n + 1) :=
  ((Fϕ.smul (J I e lamT) (continuous_J I e he lamT hlam_cont) _
    (abs_J_le I e he lamT hlam_cont)).conv (hb.le.trans hbb'.le) Fφ).datumC hb hbb'.le

omit [MeasurableSpace K] [BorelSpace K] in
theorem toEta_xData (s : K) :
    toEta b (xData I e he lamT hlam_cont b b' hb hbb' Fϕ Fφ s) =
      CoeffFamily.conv (fun γ => J I e lamT s * Fϕ.f s γ) (Fφ.f s) :=
  UniformSeriesFamily.toEta_datumC _ _ _ _

omit [MeasurableSpace K] [BorelSpace K] in
theorem toXi_xData (s : K) : toXi b (xData I e he lamT hlam_cont b b' hb hbb' Fϕ Fφ s) = 0 :=
  UniformSeriesFamily.toXi_datumC _ _ _ _

omit [MeasurableSpace K] [BorelSpace K] in
theorem xiCoord_xData (s : K) :
    xiCoord (xData I e he lamT hlam_cont b b' hb hbb' Fϕ Fφ s) = 0 :=
  UniformSeriesFamily.xiCoord_datumC _ _ _ _

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hϕ_eq in
theorem c_eq_of_mem_box (s : K) {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) b) :
    c I e lamT b b' hb Fϕ (s, v) = J I e lamT s * ϕ (Φ I σ e lamT (s, v)) := by
  have hcl : clamp b hb.le v = v := clamp_eq_self hb.le fun i => by
    have := hv i (mem_univ _)
    rw [mem_Ioc] at this
    exact abs_le.2 ⟨by linarith, this.2⟩
  rw [c, hcl, hϕ_eq s v hv]

include he he_inj hpos hϕ_eq in
/-- The chart density of the core is the Jacobian-weighted prior, chart-measure a.e. -/
theorem density_ae :
    (fun p : K × (Fin (n + 1) → ℝ) =>
      ((chartDensity (fun _ => 0) (c I e lamT b b' hb Fϕ) p).toNNReal : ℝ≥0∞)) =ᵐ[chartMeasure
        (baseMeasure I e) n b]
      fun p => ENNReal.ofReal (∏ j, lamT (e p.1) j) * ENNReal.ofReal (ϕ (Φ I σ e lamT p)) := by
  have := isFiniteMeasure_baseMeasure I e he he_inj
  filter_upwards [ae_snd_mem_box (baseMeasure I e) n b] with p hp
  have hc := c_eq_of_mem_box I σ e lamT ϕ b b' hb Fϕ hϕ_eq p.1 hp
  change ENNReal.ofReal (chartDensity (fun _ => 0) (c I e lamT b b' hb Fϕ) p) = _
  rw [chartDensity]
  simp only [pow_zero, Finset.prod_const_one, one_mul]
  rw [show (p.1, p.2) = p from rfl] at hc
  rw [hc, ENNReal.ofReal_mul (J_pos I e lamT hpos p.1).le]
  rfl

end NormalisedBox

namespace NormalisedBox

/-! ### The bundled data and the core -/

/-- The data of a normalised box core at the coordinate stratum `S_I`: tangential embedding of a
compact base, positive normal widths with the normalisation identity, and uniform normal-series
families for the prior and the observable in the normalised normal variables. -/
structure Data (k : Fin d → ℕ) (I : Finset (Fin d)) (n : ℕ) (K : Type*) [TopologicalSpace K]
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
  /-- the normalised unit -/
  β : ℝ
  hnorm : ∀ t ∈ range e, tanUnit k I t * ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β
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

variable {d : ℕ} {k : Fin d → ℕ} (hk : ∀ i, 0 < k i) {I : Finset (Fin d)} {n : ℕ}
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {W : Set (Fin d → ℝ)} (hWm : MeasurableSet W) {ϕ φ : (Fin d → ℝ) → ℝ} (hϕm : Measurable ϕ)
  (hϕ0 : ∀ w ∈ W, 0 ≤ ϕ w) (L : LocalisationData (Fin d → ℝ))
  (hLμ : L.μ = (volume.restrict W).withDensity fun w => ENNReal.ofReal (ϕ w))
  (hLphase : L.phase = CoordModel.phase d k) (hLobs : L.obs = φ) (D : Data k I n K W ϕ φ)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Data.b'_pos : 0 < D.b' := D.hb.trans D.hbb'

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem Data.norm_lt_of_mem_box {v : Fin (n + 1) → ℝ} (hv : v ∈ box (ι := Fin (n + 1)) D.b) :
    ‖v‖ < D.b' := by
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg D.hb.le).2 fun i => ?_) D.hbb'
  have := hv i (mem_univ _)
  rw [mem_Ioc] at this
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith, this.2⟩

include hk hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- ★★ **The normalised box core**: base measure `ν_B`, normal box `(0,b]^{n+1}`,
`Φ(s,v) = s + Σ λ_j(s) v_j e_j`, density `J(s)·ϕ`, amplitude datum `(J·fϕ) ⋆ fφ`; exact transport
onto `L.μ|_{image}`, normalised phase, scaled product amplitude identity. -/
noncomputable def core : CorePresentation L (L.μ.restrict (image I D.e D.lamT D.b)) K n D.β where
  ν := baseMeasure I D.e
  isFiniteMeasure_ν := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
  h := fun _ => 0
  k := kι k I D.σ
  k_pos := fun _ => hk _
  b := D.b
  b_pos := D.hb
  Φ := Φ I D.σ D.e D.lamT
  measurable_Φ := measurable_Φ I D.σ (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT
  c := c I D.e D.lamT D.b D.b' D.hb D.Fϕ
  measurable_c :=
    (((continuous_J I D.e D.he D.lamT D.hlam_cont).comp continuous_fst).mul
      (D.Fϕ.continuous_evalF_clamp D.hb.le D.hbb'.le)).measurable
  nonneg_c := by
    have := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
    filter_upwards [ae_snd_mem_box (baseMeasure I D.e) n D.b]
    rintro ⟨s, v⟩ hv
    rw [c_eq_of_mem_box I D.σ D.e D.lamT ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq s hv]
    exact mul_nonneg (J_pos I D.e D.lamT D.hpos s).le
      (hϕ0 _ (D.hW (mem_image_Φ I D.σ D.e D.lamT D.hpos s hv)))
  x := xData I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ
  transport := by
    have h := map_Φ I D.σ D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT D.hpos
      hϕm.ennreal_ofReal
    rw [show (baseMeasure I D.e).prod (volume.restrict (box (ι := Fin (n + 1)) D.b)) =
      chartMeasure (baseMeasure I D.e) n D.b from rfl] at h
    rw [withDensity_congr_ae
      (density_ae I D.σ D.e D.he D.he_inj D.lamT D.hpos ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq), hLμ,
      ← restrict_withDensity hWm, Measure.restrict_restrict
      (measurableSet_image I D.b (measurableEmbedding_e I D.e D.he D.he_inj) D.hlamT),
      inter_eq_left.2 D.hW]
    exact h
  phase_normal := Eventually.of_forall fun p => by
    obtain ⟨s, v⟩ := p
    rw [hLphase, phase_Φ, D.hnorm (D.e s) (mem_range_self _)]
  amplitude_eq := by
    have := isFiniteMeasure_baseMeasure I D.e D.he D.he_inj
    filter_upwards [ae_snd_mem_box (baseMeasure I D.e) n D.b]
    rintro ⟨s, v⟩ hv
    rw [toEta_xData, hLobs]
    have hv' : ∀ i, 0 ≤ v i ∧ v i ≤ D.b := fun i => by
      have := hv i (mem_univ _)
      rw [mem_Ioc] at this
      exact ⟨this.1.le, this.2⟩
    rw [evalF_conv_of_absSummableAt (f := fun γ => J I D.e D.lamT s * D.Fϕ.f s γ) D.hb
      ((D.Fϕ.smul (J I D.e D.lamT) (continuous_J I D.e D.he D.lamT D.hlam_cont) _
        (abs_J_le I D.e D.he D.lamT D.hlam_cont)).absSummableAt_of_le D.hb.le D.hbb'.le s)
      (D.Fφ.absSummableAt_of_le D.hb.le D.hbb'.le s) hv',
      evalF_const_mul, c_eq_of_mem_box I D.σ D.e D.lamT ϕ D.b D.b' D.hb D.Fϕ D.hϕ_eq s hv,
      D.hφ_eq s v (D.norm_lt_of_mem_box hv), D.hϕ_eq s v hv]
  fluct_zero := xiCoord_xData I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ

include hk hWm hϕm hϕ0 hLμ hLphase hLobs in
theorem core_obsFibre (s : K) (v : Fin (n + 1) → ℝ) :
    (core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).obsFibre s v = φ (Φ I D.σ D.e D.lamT (s, v)) := by
  change L.obs _ = _
  rw [hLobs]
  rfl

include hk hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- ★ **The normal-moment presentation of the core** from the observable's series. -/
noncomputable def presentation :
    CoreNormalMomentPresentation (core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D) where
  p := fun s => polySeriesD (D.Fφ.f s)
  R := fun _ => ENNReal.ofReal D.b'
  analytic := fun s => by
    refine (hasFPowerSeriesOnBall_evalF (D.Fφ.f s) D.b'_pos
      (D.Fφ.absSummableAt D.b'_pos.le s)).congr fun v hv => ?_
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hv
    rw [core_obsFibre, D.hφ_eq s v ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 hv)]
  radius := fun _ => (ENNReal.ofReal_lt_ofReal_iff D.b'_pos).2 D.hbb'
  cBound := Jb I D.e D.he D.lamT D.hlam_cont * ∑' γ, D.Fϕ.M γ * D.b ^ (∑ i, γ i)
  c_le := fun q => by
    refine (le_abs_self _).trans ?_
    change |J I D.e D.lamT q.1 * evalF (D.Fϕ.f q.1) (clamp D.b D.hb.le q.2)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_J_le I D.e D.he D.lamT D.hlam_cont q.1)
      (D.Fϕ.abs_evalF_le D.hb.le D.hbb'.le q.1 _ (abs_clamp_le D.hb.le q.2)) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_J_le I D.e D.he D.lamT D.hlam_cont q.1))

include hk hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- The Taylor family of the fibre observable is the observable's coefficient family. -/
theorem jetFamily_obsFibre (s : K) :
    jetFamily n ((core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).obsFibre s) = D.Fφ.f s := by
  rw [jetFamily_eq_monoFamily ((presentation hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).analytic s)]
  exact monoFamily_polySeriesD (D.Fφ.f s)

include hk hWm hϕm hϕ0 hLμ hLphase hLobs in
/-- The amplitude datum of the core: `(J·fϕ) ⋆ fφ`. -/
theorem toEta_core_x (s : K) :
    toEta D.b ((core hk hWm hϕm hϕ0 L hLμ hLphase hLobs D).x s) =
      CoeffFamily.conv (fun γ => J I D.e D.lamT s * D.Fϕ.f s γ) (D.Fφ.f s) :=
  toEta_xData I D.e D.he D.lamT D.hlam_cont D.b D.b' D.hb D.hbb' D.Fϕ D.Fφ s

end NormalisedBox

end Grammar
