/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedCoordFreeExpansion
import Grammar.ExpansionCongruence

/-!
# Regularity of the normal-order series of a coefficient certificate (CCCXXXIX; phase G, unit G5)

Consult #100 §3C, §7 (G5). The assembly of expansions over several pieces exchanges the
normal-order series `∑_r (1/r!)⟨B_r(s), D^r_⊥ φ(s)⟩` with finite sums and integrates it against
summed measures, which needs its **summability at every stratum point** and its **integrability**
against the stratum measures — for the certificate's own observable and for any observable with
the same germs at the base points. Both follow from the chart-level facts already in the library
(`summable_field_pair`, `integrable_weight_mul`): the field pairing depends on the observable
only through its germs at the compact bases (`chartTensorExt_pair_congr`, `field_pair_congr`, via
`normalDifferential_congr`), so `summable_field_pair_of_germ`, `integrable_field_series` and
`integrable_field_series_of_germ`. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology

namespace Grammar

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)}
  {K ϕ φ : (Fin d → ℝ) → ℝ}

namespace ResolvedCertificate

variable (C : ResolvedCertificate R D W K ϕ φ)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
/-- Transport pairing for an arbitrary observable. -/
theorem transportTensor_pair' (ψ : (Fin d → ℝ) → ℝ) {J : Fin C.M} {I : Finset R.Component}
    (hJ : C.strat J = I) (r : ℕ)
    (T : ∀ s : R.Stratum (C.strat J), MomentTensor (D.N (C.strat J) s) r) (s : R.Stratum I) :
    (C.transportTensor hJ r T s).pair (D.normalDifferential ψ I s r) =
      (T (C.ofStratum hJ s)).pair (D.normalDifferential ψ (C.strat J) (C.ofStratum hJ s) r) := by
  subst hJ
  rfl

namespace CoefficientCertificate

variable {C} (Cc : C.CoefficientCertificate) (ψ : (Fin d → ℝ) → ℝ)
  (hψ : ∀ (J : Fin C.M) (s : ↥(C.base J)), ψ =ᶠ[𝓝 (R.π (s.1 : U))] φ)

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
include hψ in
/-- The chart tensors pair with the jets of any observable with the same germs at the base. -/
theorem chartTensorExt_pair_congr (J : Fin C.M) (s : R.Stratum (C.strat J)) (r : ℕ)
    (q : PowerLogIndex) :
    (Cc.chartTensorExt J s r q).pair (D.normalDifferential ψ (C.strat J) s r) =
      (Cc.chartTensorExt J s r q).pair (D.normalDifferential φ (C.strat J) s r) := by
  by_cases hs : s ∈ C.base J
  · rw [D.normalDifferential_congr (C.strat J) s (hψ J ⟨s, hs⟩) r]
  · unfold ResolvedCertificate.CoefficientCertificate.chartTensorExt MomentTensor.pair
    rw [dif_neg hs, zero_apply, zero_apply]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
include hψ in
/-- ★ **The field pairing depends on the observable only through its germs at the bases.** -/
theorem field_pair_congr (I : Finset R.Component) (r : ℕ) (q : PowerLogIndex) (s : R.Stratum I) :
    (Cc.field I r q s).pair (D.normalDifferential ψ I s r) =
      (Cc.field I r q s).pair (D.normalDifferential φ I s r) := by
  unfold ResolvedCertificate.CoefficientCertificate.field MomentTensor.pair
  rw [sum_apply, sum_apply]
  refine Finset.sum_congr rfl fun J _ => ?_
  split_ifs with hJ
  · rw [smul_apply, smul_apply]
    congr 1
    have h1 := C.transportTensor_pair' ψ hJ r (fun s' => Cc.chartTensorExt J s' r q) s
    have h2 := C.transportTensor_pair' φ hJ r (fun s' => Cc.chartTensorExt J s' r q) s
    have h3 := Cc.chartTensorExt_pair_congr ψ hψ J (C.ofStratum hJ s) r q
    unfold MomentTensor.pair at h1 h2 h3
    rw [h1, h2, h3]
  · rw [zero_apply, zero_apply]

omit [T2Space U] [BorelSpace U] [MeasurableSpace A] [BorelSpace A] in
include hψ in
theorem summable_field_pair_of_germ (I : Finset R.Component) (q : PowerLogIndex)
    (s : R.Stratum I) :
    Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential ψ I s r) :=
  (Cc.summable_field_pair I q s).congr fun r => by rw [Cc.field_pair_congr ψ hψ I r q s]

omit [MeasurableSpace A] [BorelSpace A] in
/-- ★ **Integrability of the normal-order series of the field against the stratum measure.** -/
theorem integrable_field_series (I : Finset R.Component) (q : PowerLogIndex) :
    Integrable (fun s => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r))
      (C.stratumMeasure I) := by
  have heq : (fun s : R.Stratum I => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)) =
      fun s => ∑ J, if hJ : C.strat J = I then
        C.weight hJ s * C.transportFun hJ (Cc.chartSeries J q) s else 0 :=
    funext fun s => Cc.tsum_field_pair I q s
  rw [heq]
  refine integrable_finsetSum _ fun J _ => ?_
  split_ifs with hJ
  · exact Cc.integrable_weight_mul I q J hJ
  · exact integrable_zero _ _ _

omit [MeasurableSpace A] [BorelSpace A] in
include hψ in
theorem integrable_field_series_of_germ (I : Finset R.Component) (q : PowerLogIndex) :
    Integrable (fun s => ∑' r : ℕ,
      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential ψ I s r))
      (C.stratumMeasure I) :=
  (Cc.integrable_field_series I q).congr (Eventually.of_forall fun s =>
    tsum_congr fun r => by rw [Cc.field_pair_congr ψ hψ I r q s])

end CoefficientCertificate

end ResolvedCertificate

end Grammar
