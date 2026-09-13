/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoordinateKernel

/-!
# Linearity of the jet functional (CCCLII; programme J-min, unit J3)

The jet functional of a kernel, `coefficient Kd ψ q = ∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥(ψ∘π), B⟩ dν_I`,
is linear in the observable: the normal differentials are additive and homogeneous where the
observable is smooth along the normal germ (`normalDifferential_add`, `normalDifferential_smul`),
and the pairing with the kernel's field only sees the compact bases, where certified observables
are analytic (`contDiffAt_obs_base`, from the normal-moment presentations;
`field_eq_zero_of_not_covered` off the bases). Hence ★ `expansionCoefficient_add`/`_smul`
(pointwise pairing hypotheses, convergent series, integrable sums) and, for two observables
certified with the SAME kernel,
★★ `MomentKernelData.coefficient_add`, ★★ `coefficient_smul`. The coordinate instance (the linear
map on the observables with a holomorphic extension on a fixed neighbourhood) is CCCLIII.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A}

/-! ### Linearity of the normal differentials and of the coordinate-free coefficient -/

namespace ResolvedNormalData

variable (D)

omit [T2Space U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem normalDifferential_add {ψ₁ ψ₂ : (Fin d → ℝ) → ℝ} (I : Finset R.Component)
    (s : R.Stratum I) (r : ℕ)
    (h₁ : ContDiffAt ℝ r (fun v : D.N I s => ψ₁ (R.π (D.Φ I s v))) 0)
    (h₂ : ContDiffAt ℝ r (fun v : D.N I s => ψ₂ (R.π (D.Φ I s v))) 0) :
    D.normalDifferential (ψ₁ + ψ₂) I s r =
      D.normalDifferential ψ₁ I s r + D.normalDifferential ψ₂ I s r := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential rawNormalJet
  exact iteratedFDeriv_add_apply h₁ h₂

omit [T2Space U] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem normalDifferential_smul {ψ : (Fin d → ℝ) → ℝ} (c : ℝ) (I : Finset R.Component)
    (s : R.Stratum I) (r : ℕ)
    (h : ContDiffAt ℝ r (fun v : D.N I s => ψ (R.π (D.Φ I s v))) 0) :
    D.normalDifferential (c • ψ) I s r = c • D.normalDifferential ψ I s r := by
  unfold ResolvedNormalData.normalDifferential Grammar.normalDifferential rawNormalJet
  exact iteratedFDeriv_const_smul_apply h

variable (ν : ∀ I : Finset R.Component, Measure (R.Stratum I)) (B : D.MomentCoefficientField)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
/-- ★ **Additivity of the coordinate-free coefficient in the observable**, from the pointwise
additivity of the pairing, convergence of both series and integrability of their sums. -/
theorem expansionCoefficient_add {ψ₁ ψ₂ : (Fin d → ℝ) → ℝ} (q : PowerLogIndex)
    (hpair : ∀ I (s : R.Stratum I) (r : ℕ),
      (B I r q s).pair (D.normalDifferential (ψ₁ + ψ₂) I s r) =
        (B I r q s).pair (D.normalDifferential ψ₁ I s r) +
          (B I r q s).pair (D.normalDifferential ψ₂ I s r))
    (hs₁ : ∀ I (s : R.Stratum I), Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential ψ₁ I s r))
    (hs₂ : ∀ I (s : R.Stratum I), Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential ψ₂ I s r))
    (hi₁ : ∀ I, Integrable (fun s : R.Stratum I => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential ψ₁ I s r)) (ν I))
    (hi₂ : ∀ I, Integrable (fun s : R.Stratum I => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (B I r q s).pair (D.normalDifferential ψ₂ I s r)) (ν I)) :
    D.expansionCoefficient ν B (ψ₁ + ψ₂) q =
      D.expansionCoefficient ν B ψ₁ q + D.expansionCoefficient ν B ψ₂ q := by
  unfold ResolvedNormalData.expansionCoefficient
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← integral_add (hi₁ I) (hi₂ I)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [← (hs₁ I s).tsum_add (hs₂ I s)]
  refine tsum_congr fun r => ?_
  rw [hpair I s r, mul_add]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Homogeneity of the coordinate-free coefficient in the observable.** -/
theorem expansionCoefficient_smul {ψ : (Fin d → ℝ) → ℝ} (c : ℝ) (q : PowerLogIndex)
    (hpair : ∀ I (s : R.Stratum I) (r : ℕ),
      (B I r q s).pair (D.normalDifferential (c • ψ) I s r) =
        c * (B I r q s).pair (D.normalDifferential ψ I s r)) :
    D.expansionCoefficient ν B (c • ψ) q = c * D.expansionCoefficient ν B ψ q := by
  unfold ResolvedNormalData.expansionCoefficient
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [← tsum_mul_left]
  refine tsum_congr fun r => ?_
  rw [hpair I s r]
  ring

end ResolvedNormalData

/-! ### Kernels: smoothness of an observable along the bases, vanishing of the field off them -/

namespace MomentKernelData

variable (Kd : MomentKernelData R D)

/-- The point of `S_{strat J}` underlying a point of `S_I`, `strat J = I`. -/
def ofStratum {J : Fin Kd.M} {I : Finset R.Component} (hJ : Kd.strat J = I) (s : R.Stratum I) :
    R.Stratum (Kd.strat J) := ⟨s.1, hJ ▸ s.2⟩

/-- A stratum point is **covered** if it lies in the base of a chart presenting its stratum. -/
def Covered (I : Finset R.Component) (s : R.Stratum I) : Prop :=
  ∃ (J : Fin Kd.M) (hJ : Kd.strat J = I), Kd.ofStratum hJ s ∈ Kd.base J

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The field vanishes at uncovered points. -/
theorem field_eq_zero_of_not_covered {I : Finset R.Component} {s : R.Stratum I}
    (hs : ¬ Kd.Covered I s) (r : ℕ) (q : PowerLogIndex) : Kd.field I r q s = 0 := by
  unfold field
  refine Finset.sum_eq_zero fun J _ => ?_
  split_ifs with hJ
  · subst hJ
    change Kd.weight rfl s • Kd.chartTensorExt J s r q = 0
    unfold chartTensorExt
    rw [dif_neg (fun hmem : s ∈ Kd.base J => hs ⟨J, rfl, hmem⟩), smul_zero]
  · rfl

/-- **An observable is smooth along the bases** of the kernel: at every base point, the observable
along the normal germ is smooth at `0`. -/
def SmoothObs (ψ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)),
    ContDiffAt ℝ ⊤ (fun v : D.N (Kd.strat J) t.1 => ψ (R.π (D.Φ (Kd.strat J) t.1 v))) 0

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
theorem SmoothObs.contDiffAt_of_covered {ψ : (Fin d → ℝ) → ℝ} (hψ : Kd.SmoothObs ψ)
    {I : Finset R.Component} {s : R.Stratum I} (hs : Kd.Covered I s) (r : ℕ) :
    ContDiffAt ℝ r (fun v : D.N I s => ψ (R.π (D.Φ I s v))) 0 := by
  obtain ⟨J, hJ, hmem⟩ := hs
  subst hJ
  exact (hψ J ⟨s, hmem⟩).of_le le_top

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
theorem SmoothObs.add {ψ₁ ψ₂ : (Fin d → ℝ) → ℝ} (h₁ : Kd.SmoothObs ψ₁) (h₂ : Kd.SmoothObs ψ₂) :
    Kd.SmoothObs (ψ₁ + ψ₂) := fun J t => (h₁ J t).add (h₂ J t)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
theorem SmoothObs.smul {ψ : (Fin d → ℝ) → ℝ} (c : ℝ) (h : Kd.SmoothObs ψ) :
    Kd.SmoothObs (c • ψ) := fun J t => (h J t).const_smul c

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
theorem SmoothObs.congr {ψ ψ' : (Fin d → ℝ) → ℝ} (h : Kd.SmoothObs ψ)
    (hψ : ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)), ψ' =ᶠ[𝓝 (R.π (t.1 : U))] ψ) : Kd.SmoothObs ψ' :=
  fun J t => (h J t).congr_of_eventuallyEq (by
    have hc : Tendsto (fun v : D.N (Kd.strat J) t.1 => R.π (D.Φ (Kd.strat J) t.1 v)) (𝓝 0)
        (𝓝 (R.π (t.1 : U))) := by
      have := R.continuous_π.continuousAt.comp (D.continuousAt_Φ (Kd.strat J) t.1)
      rw [ContinuousAt, Function.comp_apply, D.Φ_zero] at this
      exact this
    exact (hψ J t).comp_tendsto hc)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
/-- The pairing with the field is additive in the observable for smooth observables. -/
theorem field_pair_add {ψ₁ ψ₂ : (Fin d → ℝ) → ℝ} (h₁ : Kd.SmoothObs ψ₁) (h₂ : Kd.SmoothObs ψ₂)
    (I : Finset R.Component) (s : R.Stratum I) (r : ℕ) (q : PowerLogIndex) :
    (Kd.field I r q s).pair (D.normalDifferential (ψ₁ + ψ₂) I s r) =
      (Kd.field I r q s).pair (D.normalDifferential ψ₁ I s r) +
        (Kd.field I r q s).pair (D.normalDifferential ψ₂ I s r) := by
  by_cases hs : Kd.Covered I s
  · rw [D.normalDifferential_add I s r (h₁.contDiffAt_of_covered hs r)
      (h₂.contDiffAt_of_covered hs r), MomentTensor.pair_add]
  · rw [Kd.field_eq_zero_of_not_covered hs]
    simp [MomentTensor.pair]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
theorem field_pair_smul {ψ : (Fin d → ℝ) → ℝ} (h : Kd.SmoothObs ψ) (c : ℝ)
    (I : Finset R.Component) (s : R.Stratum I) (r : ℕ) (q : PowerLogIndex) :
    (Kd.field I r q s).pair (D.normalDifferential (c • ψ) I s r) =
      c * (Kd.field I r q s).pair (D.normalDifferential ψ I s r) := by
  by_cases hs : Kd.Covered I s
  · rw [D.normalDifferential_smul c I s r (h.contDiffAt_of_covered hs r), MomentTensor.pair_smul]
  · rw [Kd.field_eq_zero_of_not_covered hs]
    simp [MomentTensor.pair]

/-- **A certified observable of the kernel**: smooth along the bases, with convergent pairing
series and integrable sums (supplied by any coefficient certificate with this kernel). -/
structure Certified (ψ : (Fin d → ℝ) → ℝ) : Prop where
  smooth : Kd.SmoothObs ψ
  summable : ∀ (I : Finset R.Component) (q : PowerLogIndex) (s : R.Stratum I),
    Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (Kd.field I r q s).pair (D.normalDifferential ψ I s r)
  integrable : ∀ (I : Finset R.Component) (q : PowerLogIndex),
    Integrable (fun s : R.Stratum I => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (Kd.field I r q s).pair (D.normalDifferential ψ I s r))
      (Kd.stratumMeasure I)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
/-- ★★ **Additivity of the jet functional** on observables certified with the kernel. -/
theorem coefficient_add {ψ₁ ψ₂ : (Fin d → ℝ) → ℝ} (h₁ : Kd.Certified ψ₁) (h₂ : Kd.Certified ψ₂)
    (q : PowerLogIndex) : Kd.coefficient (ψ₁ + ψ₂) q = Kd.coefficient ψ₁ q + Kd.coefficient ψ₂ q :=
  D.expansionCoefficient_add Kd.stratumMeasure Kd.field q
    (fun I s r => Kd.field_pair_add h₁.smooth h₂.smooth I s r q) (fun I s => h₁.summable I q s)
    (fun I s => h₂.summable I q s) (fun I => h₁.integrable I q) (fun I => h₂.integrable I q)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
variable {Kd} in
/-- ★★ **Homogeneity of the jet functional.** -/
theorem coefficient_smul {ψ : (Fin d → ℝ) → ℝ} (h : Kd.SmoothObs ψ) (c : ℝ) (q : PowerLogIndex) :
    Kd.coefficient (c • ψ) q = c * Kd.coefficient ψ q :=
  D.expansionCoefficient_smul Kd.stratumMeasure Kd.field c q
    fun I s r => Kd.field_pair_smul h c I s r q

end MomentKernelData

/-! ### Certificates supply the hypotheses -/

namespace ResolvedCertificate

variable {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ} (C : ResolvedCertificate R D W K ϕ φ)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **The observable is analytic along the normal germ at every base point** (from the
normal-moment presentation of the chart). -/
theorem contDiffAt_obs_base (J : Fin C.M) (s : ↥(C.base J)) :
    ContDiffAt ℝ ⊤ (fun v : D.N (C.strat J) s.1 => φ (R.π (D.Φ (C.strat J) s.1 v))) 0 := by
  have hfib : ContDiffAt ℝ ⊤ ((C.cores.chart J).obsFibre s) 0 :=
    ((C.T J).analytic s).analyticAt.contDiffAt
  have heq : (fun v : D.N (C.strat J) s.1 => φ (R.π (D.Φ (C.strat J) s.1 v))) =
      (C.cores.chart J).obsFibre s ∘ (C.frame J s).symm := by
    funext v
    rw [Function.comp_apply, C.obsFibre_eq J s, ContinuousLinearEquiv.apply_symm_apply]
  rw [heq]
  refine ContDiffAt.comp (0 : D.N (C.strat J) s.1) ?_ (C.frame J s).symm.contDiff.contDiffAt
  rw [map_zero]
  exact hfib

namespace CoefficientCertificate

variable {C} (Cc : C.CoefficientCertificate)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem smoothObs : Cc.kernelData.SmoothObs φ := fun J t => C.contDiffAt_obs_base J t

omit [MeasurableSpace A] [BorelSpace A] in
/-- ★ **A coefficient certificate certifies its observable for its kernel.** -/
theorem certified : Cc.kernelData.Certified φ where
  smooth := Cc.smoothObs
  summable := fun I q s => by
    have h := Cc.summable_field_pair I q s
    rwa [Cc.field_eq_kernelData] at h
  integrable := fun I q => by
    have h := Cc.integrable_tsum_field_pair I q
    rwa [Cc.field_eq_kernelData, Cc.stratumMeasure_eq_kernelData] at h

end CoefficientCertificate

end ResolvedCertificate

end Grammar
