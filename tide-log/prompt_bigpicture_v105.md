# Consult #105 — closure of J-min, the paper-claim closure check, and the transition to the companion note

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 654 modules, zero sorry/axiom, headline theorems axiom-clean). Your consult #104
closed E4F and opened J-min (five units, "close at the jet-functional theorem if distribution packaging
becomes infrastructure"), to be followed by a paper-claim closure check and, absent a concrete unsupported
claim, the transition to the companion note `averaging_dataset.tex`. Here is what landed and what we found.

## 1. J-min as landed (main `fbbccc2`)

**J0 finding.** In a coefficient certificate the field `B_{I,r,q}` is built from `M, n, strat, base, ν_J, h, k,
β, b, frame, cc` (the prior's density families) — the observable enters the coefficients ONLY through
`D^r_⊥(φ∘π)` paired against the field, and this is definitional. The abstract certificate does entangle the
observable with the prior in the amplitude datum (`amplitude_eq : evalF (x s) u = c(s,u) · obs(Φ(s,u))`, with
no separate density identity), so an abstract certificate cannot be "re-observabled"; the route was the
producer level with a fixed extension domain.

* **J1** (CCCL `MomentKernelData`): the observable-free kernel structure with its own `stratumMeasure`,
  `weight`, `chartTensor`, `field`; `Cc.kernelData`; ★ `field_eq_kernelData : Cc.field = Cc.kernelData.field`
  and `stratumMeasure_eq_kernelData` — by `rfl`; the jet functional `coefficient Kd ψ q :=
  expansionCoefficient Kd.stratumMeasure Kd.field ψ q` for EVERY `ψ`.
* **J2** (CCCLI `CoordinateKernel`): the explicit `coordKernelData k hk a δ hδ f` and
  ★ `kernelData_coeffCertificate : (coeffCertificate … F).kernelData = coordKernelData … (fun I => (F I).Fϕ.f)`
  by `rfl`; `HolomorphicBoxExtension.withObs A H' hol' eq'` (same `Ω`, same prior extension, new observable
  extension); ★ `producedKernel_withObs` (the produced kernel is unchanged — the prior's face-series
  coefficients are `rfl`-independent of the observable's extension; the packet's `bound` constant does depend on
  it, but only the `.f` coefficients enter the kernel); ★★ `hasCoordFreeExpansion_withObs`: every `φ'` with a
  holomorphic extension on `A.Ω` has the expansion with the prior's produced stratum measures and field,
  spectrum `spectrumLe (coordQ k) (d−1)`.
* **J3** (CCCLII `JetFunctionalLinear`, CCCLIII `CoordinateJetFunctional`): `normalDifferential_add/smul`
  (ContDiffAt along the normal germ), ★ `expansionCoefficient_add/smul`; kernels: `Covered`,
  `field_eq_zero_of_not_covered`, `SmoothObs`, `Certified` (smooth along the bases + convergent pairing series
  + integrable sums), ★★ `coefficient_add/smul`; certificates: ★ `contDiffAt_obs_base` (from the normal-moment
  presentation's `HasFPowerSeriesOnBall` for the fibre observable, composed with the frame), ★ `certified`;
  `Certified.congr` (transport along germs at the bases); `obsSpace Ω : Submodule ℝ ((Fin d → ℝ) → ℝ)` (the
  observables with a holomorphic extension on `Ω`); ★ `certified_of_mem`;
  ★★★ `jetFunctional A k hk δ hδ hd ha hδa hϕ0W hsmall q : obsSpace A.Ω →ₗ[ℝ] ℝ` (value
  `∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥ψ, B_{I,r,q}⟩ dν_I` against the prior's kernel);
  ★★★ `hasCoordFreeExpansion_obsSpace : ∀ ψ ∈ obsSpace A.Ω, ∀ A', (fun n => ∫_{[0,a]^d} ψ ϕ e^{−nK} −
  ∑_{q ∈ spectrumLe (coordQ k) (d−1) A'} (L_q ψ) q.scale n) =o(n^{−A'})`.
* **J4 — NOT done, structural obstruction.** Your J-min statement asked for a finite order `R_A` independent
  of the observable. For the exact-moment kernel this is FALSE at strata of codimension ≥ 2: the box kernel
  `boxSpectralKernel μ j γ` at a fixed exponent `μ` is nonzero exactly when `min_i (h_i+γ_i+1)/(2k_i) = μ`
  (candidate exponents), and the other normal coordinates' orders `γ_j` are unconstrained — e.g. for
  `∫∫ u₁^a u₂^b e^{−N u₁²u₂²}` the coefficient of `N^{−(a+1)/2}` receives every `b ≥ a`. So the field
  `B_{I,r,q}` has infinite normal order in `r` (the certificate's series over `r` is a genuine `tsum`,
  ℓ¹-weighted by `b^r/r!`), and the functional is an ANALYTIC jet functional. We stopped J-min at the
  jet-functional theorem per your stopping rule; the mirror says "analytic jet functional … not of finite
  order … no continuity on a smooth test space asserted".

Mirror/plan/memory are updated (pin `fbbccc2`); Overleaf still not pushed.

## 2. Questions

1. **J-min closure.** Do you accept J-min as closed at J3 with the J4 finding? Is the "infinite normal order"
   reading right, and is "analytic jet functional" the correct paper terminology, or should we state a
   weighted-ℓ¹ continuity estimate `|L_q ψ| ≤ ∑_I ∫ ∑_r (b^r/r!)‖B_{I,r,q}‖ ‖D^r_⊥ψ‖ dν_I` (the constants are
   the certificate's `AbsSummableAt` majorants) as a bounded follow-up? Would that be worth a unit for the
   paper?
2. **Paper-claim closure check.** The paper's Lean-facing claims are mirrored in `grammar_lean.tex` with
   leanref dots (1083 dots at pin `fbbccc2`, 0 audit mismatches). The coordinate-free expansion theorem (§4 of
   the paper; CCCIII) is conditional on `ResolvedCertificate` + `CoefficientCertificate`; producers exist for
   the coordinate monomial model (one-sided and two-sided boxes from holomorphic packets, all orders `k`,
   trivial Jacobian orders) and for the cube blow-up chart model (singleton charts with unit and order `d−1`,
   assembled into the original cube integral, all orders, support `(d+ℓ)/2`, leading coefficient for `d ≥ 2`,
   packet independence, linear jet functional). Non-claims stated in the mirror: no SNC atlas / general
   resolved geometry with `π ≠ id`; no intrinsic gluing; no parity cancellation; no Gamma formula; `d = 1`
   leading value; no tensor-field packet independence; no automatic complexification; no distribution.
   Please give the closure-check LIST: which claims of a paper with this content are (a) supported, (b)
   supported only under the stated qualifications, (c) unsupported and must be reworded or dropped. In
   particular: (i) "the expansion coefficients are distributions supported on the exceptional divisor" (paper
   language) vs our analytic jet functional; (ii) "the expectation functional `E_n[φ]`" if the paper means a
   NORMALISED expectation (ratio by the partition function) — we have the numerator functional only; (iii) the
   statement of the main theorem for a general resolution (Hironaka) — we have the theorem conditional on
   certificates, with certificates produced for the coordinate and cube chart models only.
3. **Transition to the companion note.** `averaging_dataset.tex` (the user's directive: after the paper's Lean
   side is finished, formalise the note; we MAY edit the note's tex — move wrong material to appendices,
   shape it with you). Its §4 fluctuation content is already fully formalised (the note's mirror has 222
   dots). What is the right first consult for the note: a survey of its remaining claims (dataset-averaging
   statistics: the empirical-vs-population expansion, the CLT-type fluctuation of the coefficients over the
   dataset) against the library (`EmpiricalConcentration`, `GibbsJointRatio`, `PosteriorTransfer`,
   `L1Seq`…), and the same unit/gate discipline? Please state what you need from us to design it (we can
   send the note's tex and the list of its `\leanref` dots).

## 3. Material — CCCL, CCCLII, CCCLIII (full sources); CCCLI (statements)

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedCoordFreeExpansion

/-!
# The observable-independent moment kernel of a certificate (CCCL; programme J-min, unit J1)

Consult #104 §3. The coefficient field `B_{I,r,q}` of a coefficient certificate (CCCII) is built
from the chart bases and base measures, the orders `h, k`, the box sides `b`, the frames and the
density families `cc`; the observable enters the certificate only through the amplitude datum
and the jet bounds, and enters the coefficients only through the normal differentials
`D^r_⊥(φ∘π)` paired against the field. This file isolates the observable-free data as a
structure `MomentKernelData` with its own stratum measures and field, and records the directed
identities `Cc.field = Cc.kernelData.field`, `C.stratumMeasure = Cc.kernelData.stratumMeasure`
(by `rfl`). The **jet functional** of a kernel is
`coefficient K ψ q = ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(ψ∘π), B_{I,r,q}⟩ dν_I`, defined for every
observable `ψ`; the certificate's coefficients are its values at the certificate's observable
(`expansionCoefficient_eq_coefficient`). Linearity, the transfer of the expansion to other
observables and the coordinate producer's explicit kernel follow in the next units.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A}

/-- **The observable-independent moment kernel data**: chart bases with base measures, orders,
box sides, frames and density families. -/
structure MomentKernelData (R : ResolvedGeometry d U) (D : ResolvedNormalData R A) where
  /-- the number of charts -/
  M : ℕ
  /-- the normal dimensions minus one -/
  n : Fin M → ℕ
  /-- the stratum presented by each chart -/
  strat : Fin M → Finset R.Component
  /-- the compact base of each chart -/
  base : ∀ J, Set (R.Stratum (strat J))
  isCompact_base : ∀ J, IsCompact (base J)
  /-- the base measures -/
  ν : ∀ J, Measure ↥(base J)
  [isFiniteMeasure_ν : ∀ J, IsFiniteMeasure (ν J)]
  /-- the Jacobian and phase orders -/
  h : ∀ J, Fin (n J + 1) → ℕ
  k : ∀ J, Fin (n J + 1) → ℕ
  /-- the inverse temperature -/
  β : ℝ
  /-- the box sides -/
  b : Fin M → ℝ
  /-- the frames -/
  frame : ∀ J (s : ↥(base J)), (Fin (n J + 1) → ℝ) ≃L[ℝ] D.N (strat J) s.1
  /-- the density families -/
  cc : ∀ J, ↥(base J) → CoeffFamily (n J + 1)

attribute [instance] MomentKernelData.isFiniteMeasure_ν

namespace MomentKernelData

variable (Kd : MomentKernelData R D)

instance (J : Fin Kd.M) : CompactSpace ↥(Kd.base J) :=
  isCompact_iff_compactSpace.1 (Kd.isCompact_base J)

omit [MeasurableSpace A] [BorelSpace A] in
theorem measurableSet_base (J : Fin Kd.M) : MeasurableSet (Kd.base J) :=
  (Kd.isCompact_base J).isClosed.measurableSet

/-- The pushforward of the base measure to the stratum. -/
noncomputable def pushedMeasure (J : Fin Kd.M) : Measure (R.Stratum (Kd.strat J)) :=
  (Kd.ν J).map Subtype.val

instance (J : Fin Kd.M) : IsFiniteMeasure (Kd.pushedMeasure J) := Measure.isFiniteMeasure_map _ _

/-- Transport of a measure along an identification of strata. -/
def transportMeasure {J : Fin Kd.M} {I : Finset R.Component} (hJ : Kd.strat J = I)
    (μ : Measure (R.Stratum (Kd.strat J))) : Measure (R.Stratum I) := by
  subst hJ
  exact μ

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem transportMeasure_univ {J : Fin Kd.M} {I : Finset R.Component} (hJ : Kd.strat J = I)
    (μ : Measure (R.Stratum (Kd.strat J))) : Kd.transportMeasure hJ μ univ = μ univ := by
  subst hJ
  rfl

/-- The stratum measure `ν_I = ∑_{J : strat J = I} (ι_J)_* ν_J`. -/
noncomputable def stratumMeasure (I : Finset R.Component) : Measure (R.Stratum I) :=
  ∑ J, if hJ : Kd.strat J = I then Kd.transportMeasure hJ (Kd.pushedMeasure J) else 0

instance (I : Finset R.Component) : IsFiniteMeasure (Kd.stratumMeasure I) := by
  refine ⟨?_⟩
  unfold stratumMeasure
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun J _ => ?_
  split_ifs with hJ
  · rw [Kd.transportMeasure_univ]
    exact measure_lt_top _ _
  · simp

/-- The Radon–Nikodym weight of a chart in its stratum measure. -/
noncomputable def weight {J : Fin Kd.M} {I : Finset R.Component} (hJ : Kd.strat J = I)
    (s : R.Stratum I) : ℝ :=
  ((Kd.transportMeasure hJ (Kd.pushedMeasure J)).rnDeriv (Kd.stratumMeasure I) s).toReal

/-- Transport of a tensor field along an identification of strata. -/
def transportTensor {J : Fin Kd.M} {I : Finset R.Component} (hJ : Kd.strat J = I) (r : ℕ)
    (T : ∀ s : R.Stratum (Kd.strat J), MomentTensor (D.N (Kd.strat J) s) r) :
    ∀ s : R.Stratum I, MomentTensor (D.N I s) r := by
  subst hJ
  exact T

/-- The chart coefficient tensor at a base point, in the normal space along the frame. -/
noncomputable def chartTensor (J : Fin Kd.M) (s : ↥(Kd.base J)) (r : ℕ) (q : PowerLogIndex) :
    MomentTensor (D.N (Kd.strat J) s.1) r :=
  (chartMomentCoeff (Kd.n J) (Kd.h J) (Kd.k J) Kd.β (Kd.b J) q.exponent q.logDegree (Kd.cc J s)
    r).pushFrame (Kd.frame J s : (Fin (Kd.n J + 1) → ℝ) →L[ℝ] D.N (Kd.strat J) s.1)

open Classical in
/-- The chart coefficient tensor extended by zero off the compact base. -/
noncomputable def chartTensorExt (J : Fin Kd.M) (s : R.Stratum (Kd.strat J)) (r : ℕ)
    (q : PowerLogIndex) : MomentTensor (D.N (Kd.strat J) s) r :=
  if hs : s ∈ Kd.base J then Kd.chartTensor J ⟨s, hs⟩ r q else 0

/-- **The moment coefficient field** of the kernel data. -/
noncomputable def field : D.MomentCoefficientField := fun I r q s =>
  ∑ J, if hJ : Kd.strat J = I then
    Kd.weight hJ s • Kd.transportTensor hJ r (fun s' => Kd.chartTensorExt J s' r q) s else 0

/-- ★ **The jet functional** of the kernel: the coordinate-free coefficient of an arbitrary
observable `ψ` against the kernel's stratum measures and field. -/
noncomputable def coefficient (ψ : (Fin d → ℝ) → ℝ) (q : PowerLogIndex) : ℝ :=
  D.expansionCoefficient Kd.stratumMeasure Kd.field ψ q

end MomentKernelData

namespace ResolvedCertificate.CoefficientCertificate

variable {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ} {C : ResolvedCertificate R D W K ϕ φ}
  (Cc : C.CoefficientCertificate)

/-- ★ **The kernel data of a coefficient certificate**: everything but the observable. -/
noncomputable def kernelData : MomentKernelData R D where
  M := C.M
  n := C.n
  strat := C.strat
  base := C.base
  isCompact_base := C.isCompact_base
  ν := fun J => C.cores.ν J
  h := C.cores.h
  k := C.cores.k
  β := C.β
  b := C.cores.b
  frame := C.frame
  cc := Cc.cc

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
theorem stratumMeasure_eq_kernelData : C.stratumMeasure = Cc.kernelData.stratumMeasure := rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **The coefficient field is the kernel's field**: the observable does not enter it. -/
theorem field_eq_kernelData : Cc.field = Cc.kernelData.field := rfl

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The certificate's coefficients are the jet functional of its kernel at its observable. -/
theorem expansionCoefficient_eq_coefficient (q : PowerLogIndex) :
    D.expansionCoefficient C.stratumMeasure Cc.field φ q = Cc.kernelData.coefficient φ q := rfl

end ResolvedCertificate.CoefficientCertificate

end Grammar
```

```lean
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
```

```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.JetFunctionalLinear

/-!
# The linear jet functional of the coordinate box (CCCLIII; programme J-min, unit J3 endpoint)

For a fixed prior packet (complex neighbourhood `Ω` of the box, holomorphic extension of the prior)
the observables with a holomorphic extension on `Ω` form a real vector space `obsSpace Ω`
(closed under sums and real scalars). Every such observable is certified for the prior's produced
kernel (`certified_of_mem`: the certificate of the packet with the observable's extension has the
same kernel, and the representative agrees with the observable on a neighbourhood of every base
point, `Certified.congr`). Hence the **linear jet functional**
★★★ `jetFunctional A … q : obsSpace A.Ω →ₗ[ℝ] ℝ`,
`ψ ↦ ∑_I ∫_{S_I} ∑'_r (1/r!)⟨D^r_⊥ψ, B_{I,r,q}⟩ dν_I` with the prior's stratum measures and
coefficient field, and ★★★ `hasCoordFreeExpansion_obsSpace`: for every `ψ ∈ obsSpace A.Ω`,
`∫_{[0,a]^d} ψ ϕ e^{−nK} = ∑_q (jetFunctional q ψ) · q.scale n + o(n^{−A})` on the coordinate
lattice — the observable-independent finite-order coefficient functional of
consult #104 §3 (J3 gate: one kernel, a linear functional on a genuine vector space of observables;
canonicity of its scalar values across certificates is CCCVIII). Not included: the continuity
(finite-order seminorm) bound and the smooth test-function extension (J4).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### Transport of certification along germs at the bases -/

namespace MomentKernelData

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {Kd : MomentKernelData R D}

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- The pairing with the field only sees the germs of the observable at the base points. -/
theorem field_pair_congr {ψ ψ' : (Fin d → ℝ) → ℝ}
    (hψ : ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)), ψ' =ᶠ[𝓝 (R.π (t.1 : U))] ψ)
    (I : Finset R.Component) (s : R.Stratum I) (r : ℕ) (q : PowerLogIndex) :
    (Kd.field I r q s).pair (D.normalDifferential ψ' I s r) =
      (Kd.field I r q s).pair (D.normalDifferential ψ I s r) := by
  by_cases hs : Kd.Covered I s
  · obtain ⟨J, hJ, hmem⟩ := hs
    subst hJ
    rw [D.normalDifferential_congr _ s (hψ J ⟨s, hmem⟩) r]
  · rw [Kd.field_eq_zero_of_not_covered hs]
    simp [MomentTensor.pair]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Certification transports along germs at the bases.** -/
theorem Certified.congr {ψ ψ' : (Fin d → ℝ) → ℝ} (h : Kd.Certified ψ)
    (hψ : ∀ (J : Fin Kd.M) (t : ↥(Kd.base J)), ψ' =ᶠ[𝓝 (R.π (t.1 : U))] ψ) : Kd.Certified ψ' where
  smooth := h.smooth.congr hψ
  summable := fun I q s => by
    have := h.summable I q s
    refine this.congr fun r => ?_
    rw [field_pair_congr hψ I s r q]
  integrable := fun I q => by
    have := h.integrable I q
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [field_pair_congr hψ I s _ q]

end MomentKernelData

namespace WaterFilling

open NormalisedBox CoeffFamily CoordModel

/-! ### The vector space of observables with a holomorphic extension on a fixed neighbourhood -/

variable {d : ℕ}

/-- **The observables with a holomorphic extension on `Ω`**, as a real subspace of the functions
on `ℝ^d`. -/
def obsSpace (Ω : Set (Fin d → ℂ)) : Submodule ℝ ((Fin d → ℝ) → ℝ) where
  carrier := {ψ | ∃ H : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ H Ω ∧
    ∀ w, complexify w ∈ Ω → ψ w = (H (complexify w)).re}
  add_mem' := by
    rintro ψ₁ ψ₂ ⟨H₁, h₁, e₁⟩ ⟨H₂, h₂, e₂⟩
    exact ⟨H₁ + H₂, h₁.add h₂, fun w hw => by
      simp only [Pi.add_apply, e₁ w hw, e₂ w hw, Complex.add_re]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, fun w _ => by simp⟩
  smul_mem' := by
    rintro c ψ ⟨H, h, e⟩
    exact ⟨fun z => (c : ℂ) * H z, h.const_mul _, fun w hw => by
      simp only [Pi.smul_apply, smul_eq_mul, e w hw, Complex.re_ofReal_mul]⟩

theorem mem_obsSpace {Ω : Set (Fin d → ℂ)} {ψ : (Fin d → ℝ) → ℝ} :
    ψ ∈ obsSpace Ω ↔ ∃ H : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ H Ω ∧
      ∀ w, complexify w ∈ Ω → ψ w = (H (complexify w)).re := Iff.rfl

namespace HolomorphicBoxExtension

variable {a : ℝ} {ϕ φ : (Fin d → ℝ) → ℝ} (A : HolomorphicBoxExtension a ϕ φ)
  (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (δ : ℝ) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)

/-- The observable's extension of a packet lies in the observable space of its neighbourhood. -/
theorem obs_mem_obsSpace : φ ∈ obsSpace A.Ω := ⟨A.Hφ, A.holφ, A.eqφ⟩

/-- ★ **Every observable with an extension on the packet's neighbourhood is certified for the
prior's produced kernel.** -/
theorem certified_of_mem {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ obsSpace A.Ω) :
    (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).Certified ψ := by
  obtain ⟨H, hH, e⟩ := hψ
  have hsmall' : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
        ((A.withObs H hH e).toRep.faceSeries a I).ρ := fun I i => by
    rw [withObs_faceSeries_ρ]
    exact hsmall I i
  have hcert := (producedCoeffCertificate k hk (A.withObs H hH e) hd ha hϕ0W δ hδ hδa
    hsmall').certified
  have hK : (producedCoeffCertificate k hk (A.withObs H hH e) hd ha hϕ0W δ hδ hδa
      hsmall').kernelData = producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall :=
    producedKernel_withObs A H hH e k hk δ hδ hd ha hδa hϕ0W hsmall hsmall'
  rw [hK] at hcert
  refine hcert.congr fun J t => ?_
  have hbox : (t.1 : Fin d → ℝ) ∈ piBox d (Icc 0 a) :=
    mem_box_of_mem_baseStratum k hk a δ ha _ t
  exact eventually_of_mem ((A.withObs H hH e).isOpen_realDomain.mem_nhds
    ((A.withObs H hH e).box_subset_realDomain hbox))
    fun w hw => ((A.withObs H hH e).obsRep_eq_of_mem hw).symm

/-- ★★★ **The linear jet functional** of the prior's produced kernel on the observables with a
holomorphic extension on the packet's neighbourhood. -/
noncomputable def jetFunctional (q : PowerLogIndex) : obsSpace A.Ω →ₗ[ℝ] ℝ where
  toFun ψ := (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).coefficient ψ.1 q
  map_add' ψ₁ ψ₂ := MomentKernelData.coefficient_add
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ₁.2)
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ₂.2) q
  map_smul' c ψ := MomentKernelData.coefficient_smul
    (certified_of_mem A k hk δ hδ hd ha hδa hϕ0W hsmall ψ.2).smooth c q

theorem jetFunctional_apply (q : PowerLogIndex) (ψ : obsSpace A.Ω) :
    jetFunctional A k hk δ hδ hd ha hδa hϕ0W hsmall q ψ =
      (normalData d k (zeroOrders d) hk).expansionCoefficient
        (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).stratumMeasure
        (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).field ψ.1 q := rfl

/-- ★★★ **The expansion with the functional's values as coefficients**: for every observable
with a holomorphic extension on the packet's neighbourhood,
`∫_{[0,a]^d} ψ ϕ e^{−nK} − ∑_{q} (L_q ψ) · q.scale n = o(n^{−A})` on the coordinate lattice with
log degree `d − 1`, with ONE kernel for all `ψ`. -/
theorem hasCoordFreeExpansion_obsSpace (ψ : obsSpace A.Ω) (Ac : ℝ) :
    (fun n : ℝ => globalLaplace (piBox d (Icc 0 a)) (CoordModel.phase d k)
      (fun w => ψ.1 w * ϕ w) n -
      ∑ q ∈ spectrumLe (coordQ k) (d - 1) Ac,
        jetFunctional A k hk δ hδ hd ha hδa hϕ0W hsmall q ψ * q.scale n) =o[atTop]
      fun n : ℝ => n ^ (-Ac) := by
  obtain ⟨H, hH, e⟩ := ψ.2
  exact hasCoordFreeExpansion_withObs A H hH e k hk δ hδ hd ha hδa hϕ0W hsmall Ac

end HolomorphicBoxExtension

end WaterFilling

end Grammar
```

```lean
40-/-! ### The explicit coordinate kernel -/
41-
42-/-- ★ **The explicit kernel of the coordinate box collar** for prior face series `f`. -/
43:noncomputable def coordKernelData
44-    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
45-    MomentKernelData (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk) where
46-  M := numCores d
47-  n := fun i => nI (coreIdx i)
48-  strat := fun i => (coreIdx i).1
49-  base := fun i => baseStratum k hk a δ (coreIdx i).1
62-    f (coreIdx i) s γ
63-
64-/-- The common lattice of the coordinate kernel. -/
65:noncomputable def coordQ : ℕ :=
66-  commonQ fun i : Fin (numCores d) => kι k (coreIdx i).1 (σI (coreIdx i))
67-
68-variable (ϕ φ : (Fin d → ℝ) → ℝ) (hϕm : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
69-  (hφint : Integrable φ
70-    ((volume.restrict (piBox d (Icc 0 a))).withDensity fun w => ENNReal.ofReal (ϕ w)))
71-  (hd : 0 < d) (ha : 0 < a) (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i))
73-
74-/-- ★ **The kernel data of the coordinate certificate is the explicit kernel** of the prior's
75-face series: the observable does not enter. -/
76:theorem kernelData_coeffCertificate :
77-    (coeffCertificate k hk a δ hδ ϕ φ hϕm hϕ0 hφint hd ha hδa F).kernelData =
78-      coordKernelData k hk a δ hδ (fun I => (F I).Fϕ.f) := rfl
79-
80:theorem commonQ_coordKernelData
81-    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
82-    commonQ (coordKernelData k hk a δ hδ f).k = coordQ k := rfl
83-
84:theorem commonD_coordKernelData (hd : 0 < d)
85-    (f : ∀ I : NonemptyIdx d, KI k hk a δ I.1 → CoeffFamily (nI I + 1)) :
86-    commonD (coordKernelData k hk a δ hδ f).n = d - 1 := commonD_collar hd
87-
88-end CoordKernel
89-
90-/-! ### Packets with the observable's extension replaced -/
98-  (eq' : ∀ w, complexify w ∈ A.Ω → φ' w = (H' (complexify w)).re)
99-
100-/-- The packet with the observable's extension replaced (same neighbourhood, same prior). -/
101:def withObs : HolomorphicBoxExtension a ϕ φ' where
102-  Ω := A.Ω
103-  isOpen_Ω := A.isOpen_Ω
104-  box_subset := A.box_subset
105-  Hϕ := A.Hϕ
106-  Hφ := H'
107-  holϕ := A.holϕ
109-  eqϕ := A.eqϕ
110-  eqφ := eq'
111-
112:theorem withObs_Ω : (A.withObs H' hol' eq').Ω = A.Ω := rfl
113-
114:theorem withObs_radius : (A.withObs H' hol' eq').radius a = A.radius a := rfl
115-
116:theorem withObs_faceSeries_ρ (I : NonemptyIdx d) :
117-    ((A.withObs H' hol' eq').toRep.faceSeries a I).ρ = (A.toRep.faceSeries a I).ρ := rfl
118-
119:theorem withObs_faceSeries_Fϕ_f (I : NonemptyIdx d) :
120-    ((A.withObs H' hol' eq').toRep.faceSeries a I).Fϕ.f = (A.toRep.faceSeries a I).Fϕ.f := rfl
121-
122-variable (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (δ : ℝ) (hδ : 0 < δ) (hd : 0 < d) (ha : 0 < a)
123-  (hδa : ∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) (hϕ0W : ∀ w ∈ piBox d (Icc 0 a), 0 ≤ ϕ w)
124-  (hsmall : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
125-    2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) < (A.toRep.faceSeries a I).ρ)
128-      ((A.withObs H' hol' eq').toRep.faceSeries a I).ρ)
129-
130-/-- The produced kernel of a packet. -/
131:noncomputable def producedKernel :
132-    MomentKernelData (geometry d k (zeroOrders d) hk) (normalData d k (zeroOrders d) hk) :=
133-  (producedCoeffCertificate k hk A hd ha hϕ0W δ hδ hδa hsmall).kernelData
134-
135-/-- The prior's normalised face-series coefficients of the produced certificate. -/
136:noncomputable def producedPriorCoeff (I : NonemptyIdx d) :
137-    KI k hk a δ I.1 → CoeffFamily (nI I + 1) :=
138-  (((A.toRep.faceSeries a I).toFaceSeries k hk a δ hδ hd ha (hsmall I)).toPosPart k hk a δ hδ hd ha
139-    hδa (A.priorRep_nonneg_on hϕ0W)).Fϕ.f
140-
141:theorem producedKernel_eq :
142-    producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall =
143-      coordKernelData k hk a δ hδ (producedPriorCoeff A k hk δ hδ hd ha hδa hϕ0W hsmall) := rfl
144-
145-/-- The prior's face-series coefficients do not depend on the observable's extension. -/
146:theorem producedPriorCoeff_withObs :
147-    producedPriorCoeff (A.withObs H' hol' eq') k hk δ hδ hd ha hδa hϕ0W hsmall' =
148-      producedPriorCoeff A k hk δ hδ hd ha hδa hϕ0W hsmall := rfl
149-
150-/-- ★ **The produced kernel does not depend on the observable's extension.** -/
151:theorem producedKernel_withObs :
152-    producedKernel (A.withObs H' hol' eq') k hk δ hδ hd ha hδa hϕ0W hsmall' =
153-      producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall := by
154-  rw [producedKernel_eq, producedKernel_eq, producedPriorCoeff_withObs]
155-
156-/-! ### The transfer of the expansion to any observable with an extension on the packet's
157-neighbourhood -/
161-extension on the packet's neighbourhood has the coordinate-free expansion with the stratum
162-measures and the coefficient field of the PRIOR's produced kernel, on the coordinate lattice with
163-log degree `d − 1`. -/
164:theorem hasCoordFreeExpansion_withObs :
165-    (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
166-      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).stratumMeasure
167-      (producedKernel A k hk δ hδ hd ha hδa hϕ0W hsmall).field
168-      (spectrumLe (coordQ k) (d - 1)) (piBox d (Icc 0 a)) (CoordModel.phase d k) ϕ φ' := by
169-  have hsmall' : ∀ (I : NonemptyIdx d) (i : Fin (nI I + 1)),
170-      2 * δ ^ ((d : ℝ)⁻¹ * ((2 * k (σI I i).1 : ℕ) : ℝ)⁻¹) <
```
