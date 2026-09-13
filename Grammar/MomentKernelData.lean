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
