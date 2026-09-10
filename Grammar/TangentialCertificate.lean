/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TangentialReconstruct

/-!
# The bi-indexed Cauchy-envelope certificate and the tangential stochastic expansion

A tangential certificate (`TanCertificate`) is a measurable family of bi-indexed chart coefficients
`c_{γ,α}(x)` with a measurable envelope `|c_{γ,α}(x)| ≤ M(x) R_n^{-|γ|} R_t^{-|α|}`, the paper's
joint Cauchy estimate on the product polydisc.  With normal weight `b < R_n` and tangential weight
`ρ < R_t` the weighted coefficients `b^{|γ|} ρ^{|α|} c_{γ,α}(x)` form an `ℓ¹` datum on the latent
index `TanIdx` (`tanObs`), and an `L²` envelope `M(X₀) ∈ L²` gives the moment hypothesis of the
`ℓ¹` CLT (`summableCoordL2_tanObs`).  The tangential reconstruction of this datum is the paper's
tangentially analytic chart amplitude: its `γ`-th normal coefficient at the base point `v` is
`b^{|γ|} ∑_α c_{γ,α}(x) θ(v)^α` (`tanReconstruct_tanObs`).

Stacking finitely many charts (`sigmaStack`) and applying the reconstruction interface of
`JointSample.lean` yields the **assembled stochastic expansion with concrete tangential data**
(`assembled_expansion_of_tangential`): the joint chart data are `T(S_N) + A` with `T` the explicit
joint tangential reconstruction, and the normalised remainders of the assembled expansion converge
in distribution to the assembled coefficients at the reconstructed Gaussian limit.

Non-claim: the certificates are hypotheses; producing them from the resolution presentation is the
deferred geometric input.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily MonoRep

/-! ### The geometric envelope on the latent index -/

section Envelope

variable {m d : ℕ}

/-- The geometric envelope `M₀ (b/R_n)^γ (ρ/R_t)^α` on the phase slots, `0` on the amplitude
slots. -/
noncomputable def tanEnvelope (M₀ b Rn ρ Rt : ℝ) : TanIdx m d → ℝ
  | (Sum.inl γ, α) => M₀ * (∏ i, (b / Rn) ^ γ i) * ∏ i, (ρ / Rt) ^ α i
  | (Sum.inr _, _) => 0

theorem tanEnvelope_eq_mul (M₀ b Rn ρ Rt : ℝ) (p : TanIdx m d) :
    tanEnvelope M₀ b Rn ρ Rt p = M₀ * tanEnvelope 1 b Rn ρ Rt p := by
  obtain ⟨γ | γ, α⟩ := p
  · simp only [tanEnvelope, one_mul]; ring
  · simp [tanEnvelope]

theorem tanEnvelope_nonneg {M₀ b Rn ρ Rt : ℝ} (hM : 0 ≤ M₀) (hb : 0 ≤ b) (hRn : 0 < Rn) (hρ : 0 ≤ ρ)
    (hRt : 0 < Rt) (p : TanIdx m d) : 0 ≤ tanEnvelope M₀ b Rn ρ Rt p := by
  obtain ⟨γ | γ, α⟩ := p
  · exact mul_nonneg
      (mul_nonneg hM (Finset.prod_nonneg fun i _ => pow_nonneg (div_nonneg hb hRn.le) _))
      (Finset.prod_nonneg fun i _ => pow_nonneg (div_nonneg hρ hRt.le) _)
  · exact le_rfl

theorem summable_tanEnvelope_one {b Rn ρ Rt : ℝ} (hb : 0 ≤ b) (hbR : b < Rn) (hρ : 0 ≤ ρ)
    (hρR : ρ < Rt) : Summable (tanEnvelope (m := m) (d := d) 1 b Rn ρ Rt) := by
  have hRn : 0 < Rn := hb.trans_lt hbR
  have hRt : 0 < Rt := hρ.trans_lt hρR
  have hf : Summable (Sum.elim (fun γ : Fin d → ℕ => ∏ i, (b / Rn) ^ γ i)
      fun _ : Fin d → ℕ => (0 : ℝ)) := by
    refine Summable.sum _ ?_ ?_
    · exact (summable_prodGeom d (q := fun _ => b / Rn) (fun _ => div_nonneg hb hRn.le)
        fun _ => (div_lt_one hRn).2 hbR).congr fun γ => by simp
    · exact summable_zero.congr fun γ => by simp
  have hg := summable_prodGeom m (q := fun _ => ρ / Rt) (fun _ => div_nonneg hρ hRt.le)
    fun _ => (div_lt_one hRt).2 hρR
  have hf0 : ∀ j, 0 ≤ Sum.elim (fun γ : Fin d → ℕ => ∏ i, (b / Rn) ^ γ i)
      (fun _ : Fin d → ℕ => (0 : ℝ)) j := by
    rintro (γ | γ)
    · exact Finset.prod_nonneg fun i _ => pow_nonneg (div_nonneg hb hRn.le) _
    · exact le_rfl
  refine (hf.mul_of_nonneg hg hf0
    fun α => Finset.prod_nonneg fun i _ => pow_nonneg (div_nonneg hρ hRt.le) _).congr fun p => ?_
  obtain ⟨γ | γ, α⟩ := p <;> simp [tanEnvelope]

theorem summable_tanEnvelope (M₀ : ℝ) {b Rn ρ Rt : ℝ} (hb : 0 ≤ b) (hbR : b < Rn) (hρ : 0 ≤ ρ)
    (hρR : ρ < Rt) : Summable (tanEnvelope (m := m) (d := d) M₀ b Rn ρ Rt) :=
  ((summable_tanEnvelope_one hb hbR hρ hρR).mul_left M₀).congr fun p =>
    (tanEnvelope_eq_mul M₀ b Rn ρ Rt p).symm

end Envelope

/-! ### Tangential certificates -/

/-- **A tangential certificate**: measurable bi-indexed chart coefficients with a measurable joint
Cauchy envelope `|c_{γ,α}(x)| ≤ M(x) R_n^{-|γ|} R_t^{-|α|}`. -/
structure TanCertificate (𝓧 : Type*) [MeasurableSpace 𝓧] (d m : ℕ) (Rn Rt : ℝ) where
  /-- the bi-indexed coefficients: normal index `γ`, tangential index `α` -/
  c : 𝓧 → (Fin d → ℕ) → (Fin m → ℕ) → ℝ
  /-- the envelope constant -/
  M : 𝓧 → ℝ
  Rn_pos : 0 < Rn
  Rt_pos : 0 < Rt
  measurable_c : ∀ γ α, Measurable fun x => c x γ α
  measurable_M : Measurable M
  M_nonneg : ∀ x, 0 ≤ M x
  envelope : ∀ x γ α, |c x γ α| ≤ M x * Rn⁻¹ ^ (∑ i, γ i) * Rt⁻¹ ^ (∑ i, α i)

namespace TanCertificate

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {d m : ℕ} {Rn Rt : ℝ} (C : TanCertificate 𝓧 d m Rn Rt)
  (b ρ : ℝ)

/-- The weighted latent coefficients `b^{|γ|} ρ^{|α|} c_{γ,α}(x)` on the phase slots. -/
noncomputable def wcoeff (x : 𝓧) : TanIdx m d → ℝ
  | (Sum.inl γ, α) => b ^ (∑ i, γ i) * ρ ^ (∑ i, α i) * C.c x γ α
  | (Sum.inr _, _) => 0

theorem abs_wcoeff_le (hb : 0 ≤ b) (hρ : 0 ≤ ρ) (x : 𝓧) (p : TanIdx m d) :
    |C.wcoeff b ρ x p| ≤ C.M x * tanEnvelope 1 b Rn ρ Rt p := by
  obtain ⟨γ | γ, α⟩ := p
  · simp only [wcoeff, tanEnvelope, one_mul]
    have hw : 0 ≤ b ^ (∑ i, γ i) * ρ ^ (∑ i, α i) := mul_nonneg (pow_nonneg hb _) (pow_nonneg hρ _)
    rw [abs_mul, abs_of_nonneg hw]
    calc b ^ (∑ i, γ i) * ρ ^ (∑ i, α i) * |C.c x γ α|
        ≤ b ^ (∑ i, γ i) * ρ ^ (∑ i, α i) * (C.M x * Rn⁻¹ ^ (∑ i, γ i) * Rt⁻¹ ^ (∑ i, α i)) :=
          mul_le_mul_of_nonneg_left (C.envelope x γ α) hw
      _ = C.M x * ((∏ i, (b / Rn) ^ γ i) * ∏ i, (ρ / Rt) ^ α i) := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
          simp only [div_eq_mul_inv, inv_pow]; ring
  · simp [wcoeff, tanEnvelope]

theorem measurable_wcoeff (p : TanIdx m d) : Measurable fun x => C.wcoeff b ρ x p := by
  obtain ⟨γ | γ, α⟩ := p
  · exact (C.measurable_c γ α).const_mul _
  · exact measurable_const

variable (hb : 0 < b) (hbR : b < Rn) (hρ : 0 < ρ) (hρR : ρ < Rt)
include hb hbR hρ hρR

/-- **The tangential observation**: the weighted bi-indexed coefficients as an `ℓ¹` datum on the
latent index. -/
noncomputable def tanObs (x : 𝓧) : L1Seq (TanIdx m d) :=
  ⟨C.wcoeff b ρ x, by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    exact (summable_tanEnvelope (C.M x) hb.le hbR hρ.le hρR).of_nonneg_of_le
      (fun _ => abs_nonneg _) fun p => by
        rw [tanEnvelope_eq_mul]; exact C.abs_wcoeff_le b ρ hb.le hρ.le x p⟩

@[simp] theorem tanObs_apply (x : 𝓧) (p : TanIdx m d) :
    C.tanObs b ρ hb hbR hρ hρR x p = C.wcoeff b ρ x p := rfl

theorem measurable_tanObs : Measurable (C.tanObs b ρ hb hbR hρ hρR) :=
  measurable_of_coords fun p => C.measurable_wcoeff b ρ p

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → 𝓧) (hX₀ : Measurable X₀)
  (hM : MemLp (fun ω => C.M (X₀ ω)) 2 P)
include hX₀ hM

omit hbR hρR in
/-- The weighted coefficients of the sample are in `L²`. -/
theorem memLp_wcoeff (p : TanIdx m d) : MemLp (fun ω => C.wcoeff b ρ (X₀ ω) p) 2 P := by
  refine (hM.mul_const (tanEnvelope 1 b Rn ρ Rt p)).mono'
    ((C.measurable_wcoeff b ρ p).comp hX₀).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact C.abs_wcoeff_le b ρ hb.le hρ.le (X₀ ω) p

/-- The `L²` envelope of the sample coefficients: `‖w_p(X₀)‖_{L²} ≤ ‖M(X₀)‖_{L²} e_p`. -/
theorem coordL2_tanObs_le (p : TanIdx m d) :
    coordL2 P (fun ω => C.tanObs b ρ hb hbR hρ hρR (X₀ ω)) p ≤
      tanEnvelope (Real.sqrt (∫ ω, (C.M (X₀ ω)) ^ 2 ∂P)) b Rn ρ Rt p := by
  have he : 0 ≤ tanEnvelope 1 b Rn ρ Rt p :=
    tanEnvelope_nonneg zero_le_one hb.le C.Rn_pos hρ.le C.Rt_pos p
  rw [tanEnvelope_eq_mul, coordL2]
  simp only [tanObs_apply]
  have h1 : ∫ ω, (C.wcoeff b ρ (X₀ ω) p) ^ 2 ∂P ≤
      ∫ ω, (C.M (X₀ ω) * tanEnvelope 1 b Rn ρ Rt p) ^ 2 ∂P := by
    refine integral_mono_ae (C.memLp_wcoeff b ρ hb hρ P X₀ hX₀ hM p).integrable_sq
      (hM.mul_const _).integrable_sq (Eventually.of_forall fun ω => ?_)
    calc (C.wcoeff b ρ (X₀ ω) p) ^ 2 = |C.wcoeff b ρ (X₀ ω) p| ^ 2 := (sq_abs _).symm
      _ ≤ (C.M (X₀ ω) * tanEnvelope 1 b Rn ρ Rt p) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (C.abs_wcoeff_le b ρ hb.le hρ.le (X₀ ω) p) 2
  calc Real.sqrt (∫ ω, (C.wcoeff b ρ (X₀ ω) p) ^ 2 ∂P)
      ≤ Real.sqrt (∫ ω, (C.M (X₀ ω) * tanEnvelope 1 b Rn ρ Rt p) ^ 2 ∂P) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (∫ ω, (C.M (X₀ ω)) ^ 2 ∂P) * tanEnvelope 1 b Rn ρ Rt p := by
        simp_rw [mul_pow]
        rw [integral_mul_const, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq he]

/-- **The chart moment certificate** for the tangential observation. -/
theorem summableCoordL2_tanObs : SummableCoordL2 P fun ω => C.tanObs b ρ hb hbR hρ hρR (X₀ ω) where
  measurable := (C.measurable_tanObs b ρ hb hbR hρ hρR).comp hX₀
  memLp_coord := fun p => by
    simp only [tanObs_apply]
    exact C.memLp_wcoeff b ρ hb hρ P X₀ hX₀ hM p
  summable :=
    (summable_tanEnvelope _ hb.le hbR hρ.le hρR).of_nonneg_of_le (fun p => coordL2_nonneg P _ p)
      fun p => C.coordL2_tanObs_le b ρ hb hbR hρ hρR P X₀ hX₀ hM p

end Sample

/-! ### Identification with the tangentially analytic chart amplitude -/

section Identify

omit hρ hρR
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] (T : TanChart K m) (hTR : T.ρ < Rt)
include hTR

/-- **The reconstructed datum is the tangential power series**: the `γ`-th normal coefficient of
the reconstructed chart amplitude at the base point `v` is `b^{|γ|} ∑_α c_{γ,α}(x) θ(v)^α`. -/
theorem tanReconstruct_tanObs_inl (x : 𝓧) (v : K) (γ : Fin d → ℕ) :
    T.tanReconstruct (C.tanObs b T.ρ hb hbR T.ρ_pos hTR x) v (Sum.inl γ) =
      b ^ (∑ i, γ i) * ∑' α, C.c x γ α * mono α (T.θ v) := by
  rw [TanChart.tanReconstruct_apply, ← tsum_mul_left]
  refine tsum_congr fun α => ?_
  simp only [tanObs_apply, wcoeff, TanChart.w, mono_smul]
  have : T.ρ ^ (∑ i, α i) * T.ρ⁻¹ ^ (∑ i, α i) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ T.ρ_pos.ne', one_pow]
  linear_combination (b ^ (∑ i, γ i) * C.c x γ α * mono α (T.θ v)) * this

theorem tanReconstruct_tanObs_inr (x : 𝓧) (v : K) (γ : Fin d → ℕ) :
    T.tanReconstruct (C.tanObs b T.ρ hb hbR T.ρ_pos hTR x) v (Sum.inr γ) = 0 := by
  rw [TanChart.tanReconstruct_apply]
  simp [wcoeff]

end Identify

end TanCertificate

/-! ### Stacking finitely many `ℓ¹` data over a sigma type -/

section Sigma

variable {ι : Type*} [Fintype ι] {κ : ι → Type*}

/-- Stacking finitely many `ℓ¹` data into `ℓ¹` over the disjoint union. -/
noncomputable def sigmaStack (y : ∀ i, L1Seq (κ i)) : L1Seq (Σ i, κ i) :=
  ⟨fun j => y j.1 j.2, by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    refine (summable_sigma_of_nonneg fun _ => abs_nonneg _).2 ⟨fun i => ?_, Summable.of_finite⟩
    exact L1Seq.summable_abs (y i)⟩

@[simp] theorem sigmaStack_apply (y : ∀ i, L1Seq (κ i)) (j : Σ i, κ i) :
    sigmaStack y j = y j.1 j.2 := rfl

@[simp] theorem sigmaUnpack_sigmaStack (y : ∀ i, L1Seq (κ i)) (i : ι) :
    sigmaUnpack i (sigmaStack y) = y i := by
  ext j; rfl

variable [∀ i, Countable (κ i)] {𝓧 : Type*} [MeasurableSpace 𝓧]

theorem measurable_sigmaStack_comp {Y : ∀ i, 𝓧 → L1Seq (κ i)} (hY : ∀ i, Measurable (Y i)) :
    Measurable fun x => sigmaStack fun i => Y i x :=
  measurable_of_coords fun j => (measurable_coord j.2).comp (hY j.1)

/-- The moment hypothesis stacks. -/
theorem summableCoordL2_sigmaStack {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {Y : ∀ i, 𝓧 → L1Seq (κ i)} (X₀ : Ω → 𝓧) (hX₀ : Measurable X₀) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, SummableCoordL2 P fun ω => Y i (X₀ ω)) :
    SummableCoordL2 P fun ω => sigmaStack fun i => Y i (X₀ ω) where
  measurable := (measurable_sigmaStack_comp hYm).comp hX₀
  memLp_coord := fun j => (hY j.1).memLp_coord j.2
  summable := by
    refine (summable_sigma_of_nonneg fun j => coordL2_nonneg P _ j).2
      ⟨fun i => ?_, Summable.of_finite⟩
    exact (hY i).summable

end Sigma

/-! ### The assembled stochastic expansion with concrete tangential data -/

section Assembled

variable {M : ℕ} {n m : Fin M → ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)]
  [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)]
  [∀ I, OpensMeasurableSpace (K I)] {𝓧 : Type*} [MeasurableSpace 𝓧] {Rn Rt : Fin M → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The joint tangential observation: the stacked weighted coefficients of all charts. -/
noncomputable def jointTanObs (C : ∀ I, TanCertificate 𝓧 (n I + 1) (m I) (Rn I) (Rt I))
    (Tc : ∀ I, TanChart (K I) (m I)) (b : Fin M → ℝ) (hb : ∀ I, 0 < b I) (hbR : ∀ I, b I < Rn I)
    (hρR : ∀ I, (Tc I).ρ < Rt I) (x : 𝓧) : L1Seq (JointTanIdx m n) :=
  sigmaStack fun I => (C I).tanObs (b I) (Tc I).ρ (hb I) (hbR I) (Tc I).ρ_pos (hρR I) x

/-- **The assembled stochastic expansion with concrete tangential data.**  With bi-indexed
Cauchy-envelope certificates for the chart coefficients of an i.i.d. sample, the joint chart data
`T(S_N) + A` reconstructed by the explicit tangential reconstruction `T` satisfy the assembled
stochastic expansion: the normalised remainders converge in distribution to the assembled
coefficients at the reconstructed Gaussian limit. -/
theorem assembled_expansion_of_tangential (ν : (I : Fin M) → Measure (K I))
    [∀ I, IsFiniteMeasure (ν I)] (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)
    (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (C : ∀ I, TanCertificate 𝓧 (n I + 1) (m I) (Rn I) (Rt I)) (Tc : ∀ I, TanChart (K I) (m I))
    (hbR : ∀ I, b I < Rn I) (hρR : ∀ I, (Tc I).ρ < Rt I) (X : ℕ → Ω → 𝓧)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hM : ∀ I, MemLp (fun ω => (C I).M (X 0 ω)) 2 P) (A : JointData K n) (Nseq : ℕ → ℝ)
    (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq atTop atTop) (Zg E : ℕ → Ω → ℝ)
    (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (jointTanReconstruct Tc
      (empiricalSum (fun i ω => jointTanObs C Tc b hb hbR hρR (X i ω)) P i ω) + A) (Nseq i) + E i ω)
    (hE : TendstoInMeasure P (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
      (fun _ => 0)) :
    ∃ Λ : ProbabilityMeasure (L1Seq (JointTanIdx m n)),
      TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n)
          (gCoeff ν h k β b (jointTanReconstruct Tc
            (empiricalSum (fun i ω => jointTanObs C Tc b hb hbR hρR (X i ω)) P i ω) + A)) μ₀ j
            (Nseq i)) / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
        (fun z => gCoeff ν h k β b (jointTanReconstruct Tc z + A) μ₀ j) (fun _ => P)
        (Λ : Measure (L1Seq (JointTanIdx m n))) := by
  have hYm : Measurable (jointTanObs C Tc b hb hbR hρR) :=
    measurable_sigmaStack_comp fun I => (C I).measurable_tanObs _ _ _ _ _ _
  have hV : SummableCoordL2 P fun ω => jointTanObs C Tc b hb hbR hρR (X 0 ω) :=
    summableCoordL2_sigmaStack P (X 0) (hXm 0) (fun I => (C I).measurable_tanObs _ _ _ _ _ _)
      fun I => (C I).summableCoordL2_tanObs _ _ _ _ _ _ P (X 0) (hXm 0) (hM I)
  exact assembled_expansion_of_reconstruction ν h k β b hk hβ hb hμ hj hV
    (hXind.comp (fun _ => jointTanObs C Tc b hb hbR hρR) fun _ => hYm)
    (fun i => (hXid i).comp hYm) (fun i => hYm.comp (hXm i)) (jointTanReconstruct Tc) A Nseq hN0 hN
    Zg E hZm hdecomp hE

end Assembled

end Grammar
