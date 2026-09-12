/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ResolvedCoordFreeExpansion

/-!
# Completion of the coordinate-free expansion theorem (CCCIV)

The small completion tasks of consult #93 for CCCIII:

* **scalar convergence and integrability behind the totalised operations**: the normal-order
  series `∑_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,q}(s)⟩` of the assembled field is summable at EVERY
  point
  of every stratum (`summable_field_pair`), and its sum is integrable against the stratum density
  (`integrable_tsum_field_pair`) — so `∫ ∑' r` in `expansionCoefficient` is an honest integral of an
  honest series;
* **the truncation to exponents `≤ A`** (`hasCoordFreeExpansion_le`): the terms of the certified
  envelope with exponent `> A` are individually `o(n^{−A})` (`isLittleO_scale_of_lt`), so the public
  formula may be stated with the index set `{(α, j) : α ∈ Q⁻¹ℕ, α ≤ A, j ≤ D}` (`spectrumLe`) and no
  artificial cutoff `max (A+1) 1`.

Non-claims: nothing about interchanging the normal-order sum with the stratum integral (that needs
`∑_r ∫ |f_r| < ∞`, not continuity), and nothing about the intrinsic spectrum.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

variable {d : ℕ} {U : Type*} [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [BorelSpace U]
  {R : ResolvedGeometry d U} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  {D : ResolvedNormalData R A} {W : Set (Fin d → ℝ)} {K ϕ φ : (Fin d → ℝ) → ℝ}

namespace ResolvedCertificate.CoefficientCertificate

variable {C : ResolvedCertificate R D W K ϕ φ} (Cc : C.CoefficientCertificate)

omit [T2Space U] [BorelSpace U] in
/-- **The normal-order series of the assembled field converges at every point.** -/
theorem summable_field_pair (I : Finset R.Component) (q : PowerLogIndex) (s : R.Stratum I) :
    Summable fun r : ℕ =>
      (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r) := by
  have hterm : ∀ r : ℕ, (r.factorial : ℝ)⁻¹ * (Cc.field I r q s).pair (D.normalDifferential φ I s r)
      = ∑ J, if hJ : C.strat J = I then C.weight hJ s * ((r.factorial : ℝ)⁻¹ *
          (Cc.chartTensorExt J (C.ofStratum hJ s) r q).pair
            (D.normalDifferential φ (C.strat J) (C.ofStratum hJ s) r)) else 0 := by
    intro r
    unfold field MomentTensor.pair
    rw [sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    split_ifs with hJ
    · rw [smul_apply, smul_eq_mul]
      have := C.transportTensor_pair hJ r (fun s' => Cc.chartTensorExt J s' r q) s
      unfold MomentTensor.pair at this
      rw [this]
      ring
    · rw [zero_apply, mul_zero]
  refine (summable_sum fun J _ => ?_).congr fun r => (hterm r).symm
  split_ifs with hJ
  · exact (Cc.summable_chartTensorExt_pair J (C.ofStratum hJ s) q).mul_left _
  · exact summable_zero

/-- **The sum of the normal-order series is integrable against the stratum density.** -/
theorem integrable_tsum_field_pair (I : Finset R.Component) (q : PowerLogIndex) :
    Integrable (fun s : R.Stratum I => ∑' r : ℕ,
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

end ResolvedCertificate.CoefficientCertificate

/-! ### Truncation to exponents `≤ A` -/

/-- The certified spectrum truncated to exponents `≤ A`. -/
noncomputable def spectrumLe (Q Dg : ℕ) (A : ℝ) : Finset PowerLogIndex :=
  (spectrumBelow Q Dg A).filter fun q => q.exponent ≤ A

/-- A power–log term with exponent `α > A` is `o(n^{−A})`, whatever its log degree. -/
theorem isLittleO_scale_of_lt {A α : ℝ} (hα : A < α) (j : ℕ) :
    (fun n : ℝ => n ^ (-α) * Real.log n ^ j) =o[atTop] fun n : ℝ => n ^ (-A) := by
  have hlog : (fun n : ℝ => Real.log n ^ j) =o[atTop] fun n : ℝ => n ^ (α - A) := by
    have h := isLittleO_log_rpow_rpow_atTop (j : ℝ) (sub_pos.2 hα)
    refine h.congr_left fun n => ?_
    rw [Real.rpow_natCast]
  have h := (isBigO_refl (fun n : ℝ => n ^ (-α)) atTop).mul_isLittleO hlog
  refine h.trans_isBigO (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [one_mul, ← Real.rpow_add hn, show -α + (α - A) = -A by ring]

omit [T2Space U] [BorelSpace U] in
theorem PowerLogIndex.scale_def (q : PowerLogIndex) (n : ℝ) :
    q.scale n = n ^ (-q.exponent) * Real.log n ^ q.logDegree := rfl

namespace ResolvedCertificate.CoefficientCertificate

variable {C : ResolvedCertificate R D W K ϕ φ} (Cc : C.CoefficientCertificate)

/-- ★★★ **The coordinate-free expansion, truncated at the cutoff**: for every `A`,
`∫_W φ ϕ e^{−nK} − ∑_{α ∈ Q⁻¹ℕ, α ≤ A, j ≤ D} n^{−α}(log n)^j
  ∑_I ∫_{S_I} ∑'_r (1/r!) ⟨D^r_⊥(φ∘π)(s), B_{I,r,α,j}(s)⟩ dν_I(s) = o(n^{−A})`. -/
theorem hasCoordFreeExpansion_le (hK : Measurable K) (hϕ : Measurable ϕ) (hϕ0 : ∀ w, 0 ≤ ϕ w)
    (hφ : Measurable φ) :
    D.HasCoordFreeExpansion C.stratumMeasure Cc.field
      (spectrumLe (commonQ C.adapted.k) (commonD C.n)) W K ϕ φ := by
  intro Ac
  have h := Cc.hasCoordFreeExpansion hK hϕ hϕ0 hφ Ac
  set c : PowerLogIndex → ℝ := fun q => D.expansionCoefficient C.stratumMeasure Cc.field φ q
    with hc
  have hsplit : ∀ n : ℝ, ∑ q ∈ spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac,
      c q * q.scale n =
      ∑ q ∈ spectrumLe (commonQ C.adapted.k) (commonD C.n) Ac, c q * q.scale n +
      ∑ q ∈ (spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac).filter
        (fun q => ¬ q.exponent ≤ Ac), c q * q.scale n := fun n =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have htail : (fun n : ℝ => ∑ q ∈ (spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac).filter
      (fun q => ¬ q.exponent ≤ Ac), c q * q.scale n) =o[atTop] fun n : ℝ => n ^ (-Ac) := by
    have hsum := IsLittleO.sum (l := atTop) (g' := fun n : ℝ => n ^ (-Ac))
      (A := fun q : PowerLogIndex => fun n : ℝ => c q * q.scale n)
      (s := (spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac).filter
        fun q => ¬ q.exponent ≤ Ac) fun q hq => by
      have hq' : Ac < q.exponent := not_le.1 (Finset.mem_filter.1 hq).2
      exact ((isLittleO_scale_of_lt hq' q.logDegree).congr_left fun n =>
        (PowerLogIndex.scale_def q n).symm).const_mul_left (c q)
    refine hsum.congr_left fun n => ?_
    rw [Finset.sum_apply]
  have hfun : (fun n : ℝ => globalLaplace W K (fun w => φ w * ϕ w) n -
      ∑ q ∈ spectrumLe (commonQ C.adapted.k) (commonD C.n) Ac, c q * q.scale n) =
      fun n : ℝ => (globalLaplace W K (fun w => φ w * ϕ w) n -
        ∑ q ∈ spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac, c q * q.scale n) +
      ∑ q ∈ (spectrumBelow (commonQ C.adapted.k) (commonD C.n) Ac).filter
        (fun q => ¬ q.exponent ≤ Ac), c q * q.scale n := by
    funext n
    rw [hsplit n]
    ring
  rw [hfun]
  exact h.add htail

end ResolvedCertificate.CoefficientCertificate

end Grammar
