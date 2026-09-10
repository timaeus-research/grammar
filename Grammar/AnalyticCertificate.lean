/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.TorusCertificate
import Grammar.AnalyticFamilyData

/-!
# The Hypothesis-I division bridge and the identification of the empirical phase

* `TorusCertificate.ofDivision`: if the pulled-back log-likelihood ratio factors on the torus of
  radius `r` as `f x (π_ℂ w) = w^k · a x w` (Watanabe's division by the monomial), the complexified
  torus lies in a region where `‖f x z‖ ≤ H x`, and `H` is measurable — Hypothesis I's order-zero
  `L²` envelope after the resolution — then `a` carries a torus certificate with envelope
  `H x · r^{−|k|}`: on the torus `‖a x w‖ = ‖f x (π_ℂ w)‖ r^{−|k|}` exactly.  Only the order-zero
  envelope of Hypothesis I enters.
* `AnalyticCertificate`: a torus certificate at radius `r` whose chart functions are holomorphic on
  the open polydisc of radius `R > r`; then the chart coefficients reconstruct the real part of
  `a x` at every real point of the polydisc of radius `r` (`evalF_coeff`).
* The **phase evaluation functional** `phaseEval u : ℓ¹ →L[ℝ] ℝ`, `x ↦ ∑_γ x_{inl γ} u^γ`, bounded
  by `‖x‖` on the closed unit cube, with `dataPhase x u = phaseEval u x`; being continuous linear it
  commutes with the finite sums and the Bochner integral in the sample datum, so
  `dataPhase (D_n) u = n^{−1/2} ∑_{i<n} (Re a(X_i, b·u) − E Re a(X, b·u)) + dataPhase A u`
  (`dataPhase_sampleDatum`): the phase of the sample datum **is** the paper's empirical process
  `ξ_n` in unit-box coordinates.
* `sample_stochastic_expansion_of_division`: the chart stochastic expansion under the division
  bridge and Hypothesis I's order-zero envelope.

External (explicit hypotheses, not proved): the complexified chart `π_ℂ` and its torus inclusion in
the Hypothesis-I neighbourhood, the analytically divisible measurable representative `a`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Grammar

open CoeffFamily MonoRep

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {d : ℕ}

/-! ### The division bridge -/

/-- **Hypothesis-I division bridge**: `f x (π_ℂ w) = w^k a x w` on the torus and an envelope
`‖f x z‖ ≤ H x` on a region containing the complexified torus give a torus certificate for `a`
with envelope `H x · r^{−|k|}`. -/
noncomputable def TorusCertificate.ofDivision {W : Type*} {r : ℝ} (hr : 0 < r)
    (a : 𝓧 → (Fin d → ℂ) → ℂ) (ha : Measurable fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2)
    (f : 𝓧 → W → ℂ) (πC : (Fin d → ℂ) → W) (k : Fin d → ℕ) (Wallowed : Set W)
    (hdiv : ∀ x w, w ∈ torusSet d r → f x (πC w) = (∏ i, w i ^ k i) * a x w)
    (himage : ∀ w ∈ torusSet d r, πC w ∈ Wallowed) (H : 𝓧 → ℝ) (hHm : Measurable H)
    (hH0 : ∀ x, 0 ≤ H x) (hfbound : ∀ x z, z ∈ Wallowed → ‖f x z‖ ≤ H x) :
    TorusCertificate 𝓧 d r where
  a := a
  M := fun x => H x * r⁻¹ ^ (∑ i, k i)
  R_pos := hr
  measurable_a := ha
  measurable_M := hHm.mul_const _
  M_nonneg := fun x => mul_nonneg (hH0 x) (pow_nonneg (inv_nonneg.2 hr.le) _)
  torus_bound := fun x w hw => by
    have hnorm : ‖∏ i, w i ^ k i‖ = r ^ (∑ i, k i) := by
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun i _ => by rw [norm_pow, (mem_torusSet.1 hw) i]
    have h := hfbound x (πC w) (himage w hw)
    rw [hdiv x w hw, norm_mul, hnorm] at h
    have hpos : 0 < r ^ (∑ i, k i) := pow_pos hr _
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact h

@[simp] theorem TorusCertificate.ofDivision_a {W : Type*} {r : ℝ} (hr : 0 < r)
    (a : 𝓧 → (Fin d → ℂ) → ℂ) (ha : Measurable fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2)
    (f : 𝓧 → W → ℂ) (πC : (Fin d → ℂ) → W) (k : Fin d → ℕ) (Wallowed : Set W)
    (hdiv : ∀ x w, w ∈ torusSet d r → f x (πC w) = (∏ i, w i ^ k i) * a x w)
    (himage : ∀ w ∈ torusSet d r, πC w ∈ Wallowed) (H : 𝓧 → ℝ) (hHm : Measurable H)
    (hH0 : ∀ x, 0 ≤ H x) (hfbound : ∀ x z, z ∈ Wallowed → ‖f x z‖ ≤ H x) :
    (TorusCertificate.ofDivision hr a ha f πC k Wallowed hdiv himage H hHm hH0 hfbound).a = a := rfl

/-! ### Analytic certificates and reconstruction -/

/-- A torus certificate whose chart functions are holomorphic on a larger polydisc. -/
structure AnalyticCertificate (𝓧 : Type*) [MeasurableSpace 𝓧] (d : ℕ) (r R : ℝ) extends
    TorusCertificate 𝓧 d r where
  r_lt_R : r < R
  holo : ∀ x, DifferentiableOn ℂ (a x) (openPolydisc d R)

namespace AnalyticCertificate

variable {r R : ℝ} (C : AnalyticCertificate 𝓧 d r R)

/-- **Reconstruction**: the chart coefficients recover the real part of `a x` at every real point
of the polydisc of radius `r`. -/
theorem evalF_coeff (x : 𝓧) {v : Fin d → ℝ} (hv : ∀ i, |v i| < r) :
    evalF (C.toTorusCertificate.coeff x) v = (C.a x fun i => (v i : ℂ)).re :=
  evalF_polyRealCoeff_of_lt C.R_pos C.r_lt_R (C.holo x) fun i => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hv i

end AnalyticCertificate

/-! ### The phase evaluation functional -/

theorem summable_phaseTerm (x : L1Seq (DataIdx d)) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    Summable fun γ : Fin d → ℕ => x (Sum.inl γ) * mono γ u := by
  have h1 : Summable fun γ : Fin d → ℕ => |x (Sum.inl γ)| :=
    (L1Seq.summable_abs x).comp_injective Sum.inl_injective
  refine Summable.of_norm_bounded h1 fun γ => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mono_nonneg hu)]
  exact mul_le_of_le_one_right (abs_nonneg _) (mono_le_one hu)

theorem tsum_abs_inl_le (x : L1Seq (DataIdx d)) :
    ∑' γ : Fin d → ℕ, |x (Sum.inl γ)| ≤ ‖x‖ := by
  rw [L1Seq.norm_eq_tsum, Summable.tsum_sum (f := fun j : DataIdx d => |x j|)
    ((L1Seq.summable_abs x).comp_injective Sum.inl_injective)
    ((L1Seq.summable_abs x).comp_injective Sum.inr_injective)]
  exact le_add_of_nonneg_right (tsum_nonneg fun γ => abs_nonneg _)

/-- The phase evaluation functional `x ↦ ∑_γ x_{inl γ} u^γ` at a point of the closed unit cube. -/
noncomputable def phaseEval {u : Fin d → ℝ} (hu : u ∈ closedCube d) : L1Seq (DataIdx d) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' γ : Fin d → ℕ, x (Sum.inl γ) * mono γ u
      map_add' := fun x y => by
        simp only [lp.coeFn_add, Pi.add_apply, add_mul]
        exact Summable.tsum_add (summable_phaseTerm x hu) (summable_phaseTerm y hu)
      map_smul' := fun c x => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact tsum_mul_left } 1 fun x => by
    rw [one_mul, Real.norm_eq_abs]
    calc |∑' γ : Fin d → ℕ, x (Sum.inl γ) * mono γ u|
        ≤ ∑' γ : Fin d → ℕ, |x (Sum.inl γ) * mono γ u| :=
          (norm_tsum_le_tsum_norm (summable_phaseTerm x hu).norm)
      _ ≤ ∑' γ : Fin d → ℕ, |x (Sum.inl γ)| := by
          refine Summable.tsum_le_tsum (fun γ => ?_) (summable_phaseTerm x hu).abs
            ((L1Seq.summable_abs x).comp_injective Sum.inl_injective)
          rw [abs_mul, abs_of_nonneg (mono_nonneg hu)]
          exact mul_le_of_le_one_right (abs_nonneg _) (mono_le_one hu)
      _ ≤ ‖x‖ := tsum_abs_inl_le x

@[simp] theorem phaseEval_apply {u : Fin d → ℝ} (hu : u ∈ closedCube d) (x : L1Seq (DataIdx d)) :
    phaseEval hu x = ∑' γ : Fin d → ℕ, x (Sum.inl γ) * mono γ u := rfl

/-- `dataPhase` is the phase evaluation functional on the closed cube. -/
theorem dataPhase_eq_phaseEval (x : DataSpace d) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataPhase x u = phaseEval hu x := by
  rw [dataPhase_eq_of_mem x hu, phaseEval_apply]
  rfl

omit [MeasurableSpace 𝓧] in
/-- The phase evaluation of a phase observation is the amplitude family at the rescaled point. -/
theorem phaseEval_phaseObs (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
    (hc : ∀ x, AbsSummableAt (c x) b) (x : 𝓧) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    phaseEval hu (phaseObs b hb c hc x) = evalF (c x) (b • u) := by
  rw [phaseEval_apply]
  unfold evalF
  refine tsum_congr fun γ => ?_
  rw [phaseObs_inl, mono_smul]
  ring

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d) (hc : ∀ x, AbsSummableAt (c x) b) (X : ℕ → Ω → 𝓧)

/-- **The phase of the sample datum is the empirical process**: in unit-box coordinates,
`dataPhase D_n u = n^{−1/2} ∑_{i<n} (η(X_i, b·u) − E η(X, b·u)) + dataPhase A u` where
`η(x, ·) = evalF (c x)` is the chart function represented by the coefficients. -/
theorem dataPhase_sampleDatum (hcm : ∀ γ, Measurable fun x => c x γ) (hX0 : Measurable (X 0))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (A : DataSpace d) (n : ℕ) (ω : Ω) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataPhase (sampleDatum b hb c hc P X A n ω) u =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        (evalF (c (X i ω)) (b • u) - ∫ ω, evalF (c (X 0 ω)) (b • u) ∂P) + dataPhase A u := by
  have hint := integrable_of_summableCoordL2 P
    (summableCoordL2_sampleObs b hb c hc P X hcm hX0 hc2 hsum)
  rw [dataPhase_eq_phaseEval _ hu, dataPhase_eq_phaseEval A hu]
  unfold sampleDatum empiricalSum
  rw [map_add, map_smul, map_sum, smul_eq_mul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, ← (phaseEval hu).integral_comp_comm hint]
  simp only [sampleObs, phaseEval_phaseObs]

end Sample

/-- **The empirical phase is the paper's `ξ_n`**: for an analytic certificate and `b < r`, the phase
of the sample datum at `u ∈ [0,1]^d` is `n^{−1/2} ∑_{i<n} (Re a(X_i, b·u) − E Re a(X, b·u))` plus
the phase of the amplitude datum. -/
theorem dataPhase_sampleDatum_analytic {r R : ℝ} (C : AnalyticCertificate 𝓧 d r R)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {b : ℝ} (hb : 0 < b)
    (hbr : b < r) (X : ℕ → Ω → 𝓧) (hX0 : Measurable (X 0))
    (hM : MemLp (fun ω => C.M (X 0 ω)) 2 P) (A : DataSpace d) (n : ℕ) (ω : Ω) {u : Fin d → ℝ}
    (hu : u ∈ closedCube d) :
    dataPhase (sampleDatum b hb C.toTorusCertificate.coeff
        (C.toTorusCertificate.absSummableAt_coeff hb hbr) P X A n ω) u =
      (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n,
        ((C.a (X i ω) fun j => ((b * u j : ℝ) : ℂ)).re -
          ∫ ω, (C.a (X 0 ω) fun j => ((b * u j : ℝ) : ℂ)).re ∂P) + dataPhase A u := by
  have hv : ∀ j, |(b • u) j| < r := fun j => by
    have := hu j (Set.mem_univ j)
    rw [Pi.smul_apply, smul_eq_mul, abs_of_nonneg (mul_nonneg hb.le this.1)]
    calc b * u j ≤ b * 1 := mul_le_mul_of_nonneg_left this.2 hb.le
      _ < r := by linarith
  rw [dataPhase_sampleDatum P b hb _ _ X C.toTorusCertificate.measurable_coeff hX0
    (C.toTorusCertificate.memLp_coeff P (X 0) hX0 hM)
    (C.toTorusCertificate.summable_coeff P (X 0) hX0 hM hb hbr) A n ω hu]
  simp_rw [C.evalF_coeff _ hv]
  rfl

/-- **The chart stochastic expansion under the Hypothesis-I division bridge**: a measurable
divisible representative `f x (π_ℂ w) = w^k a x w` on the torus, the torus inclusion in the region
of Hypothesis I's order-zero envelope `H`, and `H ∘ X₀ ∈ L²` give the conclusions of
`sample_stochastic_expansion` for the chart coefficients of `a`. -/
theorem sample_stochastic_expansion_of_division {n : ℕ} {W : Type*} {r : ℝ} (hr : 0 < r)
    (a : 𝓧 → (Fin (n + 1) → ℂ) → ℂ) (ha : Measurable fun p : 𝓧 × (Fin (n + 1) → ℂ) => a p.1 p.2)
    (f : 𝓧 → W → ℂ) (πC : (Fin (n + 1) → ℂ) → W) (k : Fin (n + 1) → ℕ) (Wallowed : Set W)
    (hdiv : ∀ x w, w ∈ torusSet (n + 1) r → f x (πC w) = (∏ i, w i ^ k i) * a x w)
    (himage : ∀ w ∈ torusSet (n + 1) r, πC w ∈ Wallowed) (H : 𝓧 → ℝ) (hHm : Measurable H)
    (hH0 : ∀ x, 0 ≤ H x) (hfbound : ∀ x z, z ∈ Wallowed → ‖f x z‖ ≤ H x)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {b : ℝ} (hb : 0 < b)
    (hbr : b < r) (X : ℕ → Ω → 𝓧) (h : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P) (hH2 : MemLp (fun ω => H (X 0 ω)) 2 P)
    (A : DataSpace (n + 1)) :
    let C := TorusCertificate.ofDivision hr a ha f πC k Wallowed hdiv himage H hHm hH0 hfbound
    ∃ ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1))),
      TendstoInDistribution (sampleDatum b hb C.coeff (C.absSummableAt_coeff hb hbr) P X A) atTop
        (fun x => x + A) (fun _ => P) (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      (∀ {m : ℕ} (F : Fin m → ℝ × ℕ),
        (∀ i, (∃ m : ℕ, (F i).1 = (m : ℝ) / latticeQ k) ∧ (F i).2 ≤ n) →
        ∀ (Nseq : ℕ → ℝ), (∀ i, 0 ≤ Nseq i) → Tendsto Nseq atTop atTop →
        TendstoInDistribution (fun i ω => orderedRemainderVec n h k β b F
            (sampleDatum b hb C.coeff (C.absSummableAt_coeff hb hbr) P X A i ω) (Nseq i))
          atTop (fun x => dataCoeffVec n h k β b F (x + A)) (fun _ => P)
          (ν : Measure (L1Seq (DataIdx (n + 1))))) := by
  intro C
  have hM : MemLp (fun ω => C.M (X 0 ω)) 2 P := by
    change MemLp (fun ω => H (X 0 ω) * r⁻¹ ^ (∑ i, k i)) 2 P
    exact hH2.mul_const _
  obtain ⟨ν, h1, -, h3, -⟩ :=
    sample_stochastic_expansion_of_torus C P hb hbr X h k hk β hβ hXm hXind hXid hM A
  exact ⟨ν, h1, h3⟩

end Grammar
