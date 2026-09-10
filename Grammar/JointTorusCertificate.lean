import Grammar.TangentialCertificate
import Grammar.AnalyticCertificate

/-!
# Tangential certificates from a joint torus envelope

The bi-indexed tangential certificate (`TanCertificate`: coefficients `c_{γ,α}(x)` with the joint
Cauchy envelope `|c_{γ,α}(x)| ≤ M(x) R_n^{−|γ|} R_t^{−|α|}`) was a hypothesis. Here it is
*derived* from a single torus envelope on the product torus of all `d + m` chart variables
(normal `v`, tangential `w`): a `TorusCertificate` in dimension `d + m` gives, through the Cauchy
coefficients indexed by `γ ⧺ α`, a tangential certificate with `R_n = R_t = R`
(`TorusCertificate.toTanCertificate`). Everything downstream applies: the weighted `ℓ¹` datum, the
`ℓ¹` CLT moment certificate, and the assembled stochastic expansion with concrete tangential data
(`assembled_expansion_of_jointTorus`).

When the joint chart function is moreover holomorphic on a larger polydisc
(`AnalyticCertificate` in dimension `d + m`), the reconstructed chart amplitude is the chart
function itself: the phase of the reconstructed datum at the tangential point `v` and the normal
point `u` is `Re a(x, b·u ⧺ θ(v))` (`dataPhase_tanReconstruct_eq_re`). The double series over
`(γ, α)` is absolutely convergent by the joint Cauchy envelope, so the rearrangement into the
`γ`-coefficients `b^{|γ|} ∑_α c_{γ,α} θ(v)^α` is legitimate (`evalF_coeff_append`).

Non-claims: producing the joint torus envelope from the resolution presentation (the complexified
chart, its torus inclusion, the divisible representative) remains the deferred geometric input;
two different radii `R_n ≠ R_t` are not treated (take the smaller one).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace Grammar

open CoeffFamily MonoRep

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {d m : ℕ}

/-! ### Multi-indices on `Fin (d + m)` -/

theorem sum_append (γ : Fin d → ℕ) (α : Fin m → ℕ) :
    ∑ i, Fin.append γ α i = ∑ i, γ i + ∑ i, α i := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem mono_append (γ : Fin d → ℕ) (α : Fin m → ℕ) (w : Fin d → ℝ) (θ : Fin m → ℝ) :
    mono (Fin.append γ α) (Fin.append w θ) = mono γ w * mono α θ := by
  unfold mono
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The multi-index splitting `(Fin d → ℕ) × (Fin m → ℕ) ≃ (Fin (d + m) → ℕ)`. -/
def appendIdxEquiv (d m : ℕ) : (Fin d → ℕ) × (Fin m → ℕ) ≃ (Fin (d + m) → ℕ) where
  toFun p := Fin.append p.1 p.2
  invFun f := (fun i => f (Fin.castAdd m i), fun i => f (Fin.natAdd d i))
  left_inv p := by
    ext i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  right_inv f := Fin.append_castAdd_natAdd

theorem appendIdxEquiv_apply (p : (Fin d → ℕ) × (Fin m → ℕ)) :
    appendIdxEquiv d m p = Fin.append p.1 p.2 := rfl

/-- `|∏ wᵢ^{γᵢ}| ≤ b^{|γ|}` when `|wᵢ| ≤ b`. -/
theorem abs_mono_le_pow {b : ℝ} {w : Fin d → ℝ} (hw : ∀ i, |w i| ≤ b)
    (γ : Fin d → ℕ) : |mono γ w| ≤ b ^ (∑ i, γ i) := by
  unfold mono
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw i) _

/-! ### The joint torus certificate gives a tangential certificate -/

/-- **From a joint torus envelope to a tangential certificate**: the Cauchy coefficients of the
`(d + m)`-variable chart function, indexed by `γ ⧺ α`, satisfy the joint envelope
`M x R^{−|γ|} R^{−|α|}`. -/
noncomputable def TorusCertificate.toTanCertificate {R : ℝ} (C : TorusCertificate 𝓧 (d + m) R) :
    TanCertificate 𝓧 d m R R where
  c x γ α := C.coeff x (Fin.append γ α)
  M := C.M
  Rn_pos := C.R_pos
  Rt_pos := C.R_pos
  measurable_c γ α := C.measurable_coeff _
  measurable_M := C.measurable_M
  M_nonneg := C.M_nonneg
  envelope x γ α := by
    have h := C.abs_coeff_le x (Fin.append γ α)
    rwa [sum_append, pow_add, ← mul_assoc] at h

theorem TorusCertificate.toTanCertificate_c {R : ℝ} (C : TorusCertificate 𝓧 (d + m) R) (x : 𝓧)
    (γ : Fin d → ℕ) (α : Fin m → ℕ) : C.toTanCertificate.c x γ α = C.coeff x (Fin.append γ α) :=
  rfl

/-! ### The reconstructed amplitude is the chart function -/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

set_option maxHeartbeats 800000 in
-- the double-series bound elaborates slowly (products over two multi-index types)
/-- **Rearrangement of the joint Cauchy series.** For `|wᵢ| ≤ b < R` and `|θⱼ| ≤ ρ < R`,
`evalF (coeff x) (w ⧺ θ) = ∑_γ (∑_α c_{γ⧺α}(x) θ^α) w^γ`. -/
theorem TorusCertificate.evalF_coeff_append {R : ℝ} (C : TorusCertificate 𝓧 (d + m) R) (x : 𝓧)
    {b ρ : ℝ} (hb : 0 ≤ b) (hbR : b < R) (hρ : 0 ≤ ρ) (hρR : ρ < R) {w : Fin d → ℝ}
    (hw : ∀ i, |w i| ≤ b) {θ : Fin m → ℝ} (hθ : ∀ j, |θ j| ≤ ρ) :
    evalF (C.coeff x) (Fin.append w θ) =
      ∑' γ : Fin d → ℕ, (∑' α : Fin m → ℕ, C.coeff x (Fin.append γ α) * mono α θ) * mono γ w := by
  have hR := C.R_pos
  -- absolute summability of the double series
  have hsum : Summable fun p : (Fin d → ℕ) × (Fin m → ℕ) =>
      C.coeff x (Fin.append p.1 p.2) * mono p.2 θ * mono p.1 w := by
    have hgeo1 : Summable fun γ : Fin d → ℕ => C.M x * ∏ i, (b / R) ^ γ i :=
      (summable_prodGeom d (q := fun _ => b / R) (fun _ => div_nonneg hb hR.le)
        (fun _ => (div_lt_one hR).2 hbR)).mul_left (C.M x)
    have hgeo2 : Summable fun α : Fin m → ℕ => ∏ j, (ρ / R) ^ α j :=
      summable_prodGeom m (q := fun _ => ρ / R) (fun _ => div_nonneg hρ hR.le)
        (fun _ => (div_lt_one hR).2 hρR)
    have hnn1 : ∀ γ : Fin d → ℕ, 0 ≤ C.M x * ∏ i, (b / R) ^ γ i := fun γ =>
      mul_nonneg (C.M_nonneg x) (Finset.prod_nonneg fun i _ => pow_nonneg (div_nonneg hb hR.le) _)
    have hnn2 : ∀ α : Fin m → ℕ, 0 ≤ ∏ j, (ρ / R) ^ α j := fun α =>
      Finset.prod_nonneg fun j _ => pow_nonneg (div_nonneg hρ hR.le) _
    have hg : Summable fun p : (Fin d → ℕ) × (Fin m → ℕ) =>
        (C.M x * ∏ i, (b / R) ^ p.1 i) * ∏ j, (ρ / R) ^ p.2 j :=
      hgeo1.mul_of_nonneg hgeo2 hnn1 hnn2
    refine Summable.of_norm_bounded hg fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |C.coeff x (Fin.append p.1 p.2)| * |mono p.2 θ| * |mono p.1 w|
        ≤ (C.M x * R⁻¹ ^ (∑ i, Fin.append p.1 p.2 i)) * ρ ^ (∑ j, p.2 j) * b ^ (∑ i, p.1 i) :=
          mul_le_mul (mul_le_mul (C.abs_coeff_le x _) (abs_mono_le_pow hθ _) (abs_nonneg _)
            (mul_nonneg (C.M_nonneg x) (pow_nonneg (inv_nonneg.2 hR.le) _)))
            (abs_mono_le_pow hw _) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (C.M_nonneg x) (pow_nonneg (inv_nonneg.2 hR.le) _))
              (pow_nonneg hρ _))
      _ = (C.M x * ∏ i, (b / R) ^ p.1 i) * ∏ j, (ρ / R) ^ p.2 j := by
          rw [sum_append, pow_add, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
            div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]
          ring
  unfold evalF
  rw [← (appendIdxEquiv d m).tsum_eq]
  simp_rw [appendIdxEquiv_apply, mono_append]
  have hsum' : Summable fun p : (Fin d → ℕ) × (Fin m → ℕ) =>
      C.coeff x (Fin.append p.1 p.2) * (mono p.1 w * mono p.2 θ) := by
    refine hsum.congr fun p => ?_
    ring
  rw [hsum'.tsum_prod]
  refine tsum_congr fun γ => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun α => ?_
  ring

/-- **The reconstructed chart amplitude is the chart function.** For a joint analytic certificate
in the `d + m` variables (torus radius `r`, holomorphic on the polydisc of radius `R > r`), the
phase of the datum reconstructed from the sample point `x` at the tangential point `v` and the
normal point `u` of the closed unit cube is `Re a(x, b·u ⧺ θ(v))`, for `b < r` and `ρ < r`. -/
theorem AnalyticCertificate.dataPhase_tanReconstruct_eq_re {r R : ℝ}
    (C : AnalyticCertificate 𝓧 (d + m) r R) (T : TanChart K m) {b : ℝ} (hb : 0 < b) (hbr : b < r)
    (hρr : T.ρ < r) (x : 𝓧) (v : K) {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    dataPhase (T.tanReconstruct (C.toTorusCertificate.toTanCertificate.tanObs b T.ρ hb hbr T.ρ_pos
      hρr x) v) u =
      (C.a x (Fin.append (fun i => ((b * u i : ℝ) : ℂ)) fun j => ((T.θ v j : ℝ) : ℂ))).re := by
  have hcube : ∀ i, |u i| ≤ 1 := fun i => by
    have := (Set.mem_pi.1 hu) i (Set.mem_univ i)
    rw [Set.mem_Icc] at this
    rw [abs_le]
    exact ⟨by linarith [this.1], this.2⟩
  have hbu : ∀ i, |(b • u) i| ≤ b := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hb]
    exact mul_le_of_le_one_right hb.le (hcube i)
  rw [dataPhase_eq_phaseEval _ hu, phaseEval_apply]
  simp_rw [TanCertificate.tanReconstruct_tanObs_inl, TorusCertificate.toTanCertificate_c]
  have hre := C.evalF_coeff (x := x) (v := Fin.append (b • u) (T.θ v)) fun i => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact lt_of_le_of_lt (hbu i) hbr
    · rw [Fin.append_right]
      exact lt_of_le_of_lt (T.bound v j) hρr
  rw [C.toTorusCertificate.evalF_coeff_append x hb.le hbr T.ρ_pos.le hρr hbu (T.bound v)] at hre
  have hpt : ∀ γ : Fin d → ℕ,
      (b ^ (∑ i, γ i) * ∑' α, C.coeff x (Fin.append γ α) * mono α (T.θ v)) * mono γ u =
      (∑' α, C.coeff x (Fin.append γ α) * mono α (T.θ v)) * mono γ (b • u) := fun γ => by
    rw [mono_smul]
    ring
  simp_rw [hpt]
  rw [hre]
  congr 2
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left, Fin.append_left]
    rfl
  · rw [Fin.append_right, Fin.append_right]


/-! ### The assembled stochastic expansion from joint torus envelopes -/

section Assembled

variable {M : ℕ} {n m : Fin M → ℕ} {K : Fin M → Type*} [∀ I, TopologicalSpace (K I)]
  [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, MeasurableSpace (K I)]
  [∀ I, OpensMeasurableSpace (K I)] {R : Fin M → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The assembled stochastic expansion from joint torus envelopes**: with a torus certificate
for each chart in all its `nᵢ + 1 + mᵢ` variables (normal and tangential), the assembled
stochastic expansion with concrete tangential data holds — the bi-indexed certificates are no
longer hypotheses. -/
theorem assembled_expansion_of_jointTorus (ν : (I : Fin M) → Measure (K I))
    [∀ I, IsFiniteMeasure (ν I)] (h k : (I : Fin M) → Fin (n I + 1) → ℕ) (β : ℝ) (b : Fin M → ℝ)
    (hk : ∀ I i, 0 < k I i) (hβ : 0 < β) (hb : ∀ I, 0 < b I) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / commonQ k) {j : ℕ} (hj : j ≤ commonD n)
    (C : ∀ I, TorusCertificate 𝓧 (n I + 1 + m I) (R I)) (Tc : ∀ I, TanChart (K I) (m I))
    (hbR : ∀ I, b I < R I) (hρR : ∀ I, (Tc I).ρ < R I) (X : ℕ → Ω → 𝓧)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hM : ∀ I, MemLp (fun ω => (C I).M (X 0 ω)) 2 P) (A : JointData K n) (Nseq : ℕ → ℝ)
    (hN0 : ∀ i, 0 ≤ Nseq i) (hN : Tendsto Nseq atTop atTop) (Zg E : ℕ → Ω → ℝ)
    (hZm : ∀ i, Measurable (Zg i))
    (hdecomp : ∀ i ω, Zg i ω = gInt ν h k β b (jointTanReconstruct Tc
      (empiricalSum (fun i ω => jointTanObs (fun I => (C I).toTanCertificate) Tc b hb hbR hρR (X i ω)) P i ω) + A) (Nseq i) + E i ω)
    (hE : TendstoInMeasure P (fun i ω => E i ω / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
      (fun _ => 0)) :
    ∃ Λ : ProbabilityMeasure (L1Seq (JointTanIdx m n)),
      TendstoInDistribution (fun i ω =>
        (Zg i ω - absPredSum (commonQ k) (commonD n)
          (gCoeff ν h k β b (jointTanReconstruct Tc
            (empiricalSum (fun i ω => jointTanObs (fun I => (C I).toTanCertificate) Tc b hb hbR hρR (X i ω)) P i ω) + A)) μ₀ j
            (Nseq i)) / (Nseq i ^ (-μ₀) * Real.log (Nseq i) ^ j)) atTop
        (fun z => gCoeff ν h k β b (jointTanReconstruct Tc z + A) μ₀ j) (fun _ => P)
        (Λ : Measure (L1Seq (JointTanIdx m n))) :=
  assembled_expansion_of_tangential ν h k β b hk hβ hb hμ hj (fun I => (C I).toTanCertificate) Tc
    hbR hρR X hXm hXind hXid hM A Nseq hN0 hN Zg E hZm hdecomp hE

end Assembled

end Grammar
