import Grammar.SubgaussianAssembly

/-!
# The effective-temperature corollary and the normal-location normalisation check
(Astra #62 unit 5)

CLXV/unit 4 identify the limiting expectation of the leading coefficient as the population face
integral with the temperature `β` replaced **pointwise** by `β(1 − βσ²(π u)/2)`. When the face
variance is constant, `σ²(π u) = v₀` for almost every `u` in the box (`βv₀ < 2`), the pointwise
temperature is a single scalar and the limit is **the zero-phase population coefficient with the
same geometric data and amplitude at the effective temperature** `β_eff = β(1 − βv₀/2)`:

`E_ν[C^b_{λ,m−1}(Z + A)] = C^b_{λ,m−1}(A; β_eff)`
(`integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance`),

using the zero-phase evaluation of the leading coefficient `C^b_{λ,m−1}(A; β) = b^{|h|+d} c^{−λ}
K_face (Γ(λ) β^{−λ}/2) ∫ η_A(π u) w(u) du / 2^{m−1}` (`dataBoxCoeff_leading_zero_phase`, from
`S_λ(0) = β^{−λ}Γ(λ)`). Almost-everywhere constancy suffices; no converse is asserted.

**Normal-location check.** For `X ~ N(0,1)` and the negative log-likelihood ratio
`g_a(x) = a²/2 − a x`: `∑_{i<n} g_a(X_i) = na²/2 − a∑X_i` (`sum_normalLocation`); in the standard
form with core coordinate `ρ = a/√2`, `g_a(x) = ρ(ρ − √2 x)` (`normalLocation_standard_form`), so
the sampling phase is `ξ_n = −ζ_n = √2 n^{−1/2}∑_{i<n} X_i` (`neg_zetaEmp_normalLocation`) with
variance `2`, not `1` (`variance_phase_normalLocation`, for independent unit-variance observations).
This is a normalisation check of the sampling convention only; it certifies neither the
resolution presentation nor the remainder.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace Grammar

open CoeffFamily

section ZeroPhase

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)

theorem dataPhase_eq_zero_of_xiCoord_eq_zero {d : ℕ} (A : DataSpace d) (hA : xiCoord A = 0) :
    dataPhase A = fun _ => 0 := by
  funext u
  unfold dataPhase
  rw [hA]
  exact evalF_zero _

include hk hβ hb hmin hatt in
/-- **The zero-phase population leading coefficient**: for a zero-phase datum `A`,
`C^b_{λ,m−1}(A) = b^{|h|+d} c^{−λ} K_face (Γ(λ) β^{−λ}/2) ∫ η_A(π u) w(u) du / 2^{m−1}`. -/
theorem dataBoxCoeff_leading_zero_phase (A : DataSpace (n + 1)) (hA : xiCoord A = 0) :
    dataBoxCoeff n h k β b A l (multCount (ratioExp h k) l - 1) =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
            ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
          (∫ u in unitBox (n + 1), faceWeight h k l (dataAmplitude A) u *
            (Real.Gamma l * β ^ (-l) / 2)) /
          2 ^ (multCount (ratioExp h k) l - 1)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [dataBoxCoeff_leading_eq_spatialFace n h k hk hβ hb hmin hatt, spatialFace_eq_faceWeight,
    dataPhase_eq_zero_of_xiCoord_eq_zero A hA]
  congr 3
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  rw [phaseMoment_eq_half_fluctuation, fluctuation_zero β l hβ hl]
  ring

variable {𝓧 : Type*} [MeasurableSpace 𝓧] (c : 𝓧 → CoeffFamily (n + 1))
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

include hk hβ hb hmin hatt in
/-- **The effective-temperature corollary**: if the face variance is constant,
`σ²(π u) = v₀` for almost every `u` in the box, with `βv₀ < 2`, then the limiting expectation of
the leading coefficient is the zero-phase population coefficient with the same geometric data and
amplitude at the effective temperature `β_eff = β(1 − βv₀/2)`:
`E_ν[C^b_{λ,m−1}(Z + A)] = C^b_{λ,m−1}(A; β_eff)`. -/
theorem integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance
    (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    (hM2 : MemLp (sampleObs b hb c hc X 0) 2 P) {κ : ℝ≥0}
    (hκ : UniformSubgaussianPhase b hb c hc P X κ) (hβκ : β * κ < 2)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    (A : DataSpace (n + 1)) (hA : xiCoord A = 0) {v₀ : ℝ} (hv₀ : β * v₀ < 2)
    (hconst : ∀ᵐ u ∂volume, u ∈ unitBox (n + 1) →
      phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) = v₀) :
    ∫ Z, dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)
        ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
      dataBoxCoeff n h k (β * (1 - β * v₀ / 2)) b A l (multCount (ratioExp h k) l - 1) := by
  have hβeff : 0 < β * (1 - β * v₀ / 2) := mul_pos hβ (by linarith)
  rw [(integral_dataBoxCoeff_leading_eq_subgaussian n h k hk hβ hb hmin hatt c hc P X hcm hXm hc2
    hsum hM2 hκ hβκ hmarg htail A hA).2,
    dataBoxCoeff_leading_zero_phase n h k hk hβeff hb hmin hatt A hA]
  congr 3
  refine setIntegral_congr_ae (measurableSet_unitBox _) (hconst.mono fun u hu hmem => ?_)
  rw [hu hmem]

end ZeroPhase

/-! ### The normal-location check -/

section NormalLocation

/-- `∑_{i<n} (a²/2 − a x_i) = n a²/2 − a ∑_{i<n} x_i`. -/
theorem sum_normalLocation (n : ℕ) (a : ℝ) (x : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, (a ^ 2 / 2 - a * x i) =
      n * (a ^ 2 / 2) - a * ∑ i ∈ Finset.range n, x i := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]

/-- The standard form of the normal-location log-likelihood ratio with core coordinate
`ρ = a/√2`: `a²/2 − a x = ρ (ρ − √2 x)`. -/
theorem normalLocation_standard_form (a x : ℝ) :
    a ^ 2 / 2 - a * x = (a / Real.sqrt 2) * (a / Real.sqrt 2 - Real.sqrt 2 * x) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [h2]
  ring

/-- The sampling phase of the normal-location model: `ξ_n = −ζ_n = √2 n^{−1/2} ∑_{i<n} x_i`. -/
theorem neg_zetaEmp_normalLocation (n : ℕ) (a : ℝ) (x : ℕ → ℝ) :
    -zetaEmp n (fun i => a / Real.sqrt 2 - Real.sqrt 2 * x i) (a / Real.sqrt 2) =
      Real.sqrt 2 * ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, x i) := by
  unfold zetaEmp
  simp only [sub_sub_cancel_left, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- **The variance of the normal-location phase is `2`**: for independent observations of unit
variance, `Var[√2 n^{−1/2} ∑_{i<n} X_i] = 2`. -/
theorem variance_phase_normalLocation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (x : ℕ → Ω → ℝ) (hind : iIndepFun x P)
    (hx : ∀ i, MemLp (x i) 2 P) (hvar : ∀ i, Var[x i; P] = 1) {n : ℕ} (hn : 0 < n) :
    Var[fun ω => Real.sqrt 2 * ((Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, x i ω); P] = 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [variance_const_mul, variance_const_mul]
  have hsum : Var[fun ω => ∑ i ∈ Finset.range n, x i ω; P] = n := by
    have e : (fun ω => ∑ i ∈ Finset.range n, x i ω) = ∑ i ∈ Finset.range n, x i := by
      funext ω
      simp [Finset.sum_apply]
    rw [e, IndepFun.variance_sum (fun i _ => hx i) fun i _ j _ hij => hind.indepFun hij]
    simp [hvar]
  rw [hsum, inv_pow, Real.sq_sqrt hn'.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

end NormalLocation

end Grammar
