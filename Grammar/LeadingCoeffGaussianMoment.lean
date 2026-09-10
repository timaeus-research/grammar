import Grammar.L1GaussianFunctional
import Grammar.JointSampleLimit
import Grammar.SpatialEnergyLaw
import Grammar.PhaseLaplaceLaw
import Grammar.GaussianInsertion
import Grammar.GaussianPMoment

/-!
# The Gaussian first moment of the leading coefficient at the `ℓ¹` Gaussian limit

The limiting expectation `E_ν[C_{λ₀,m₀−1}(Z + A)]` of the annealed sample-datum theorem
(CLXII–CLXIII) is identified as a **covariance-modified population integral over the leading face**.
The leading coefficient at box radius `b` is the face functional of the represented phase and
amplitude (`dataBoxCoeff_leading_eq_spatialFace`); under the `ℓ¹` Gaussian limit `ν` of the phase
observations the amplitude coordinates vanish almost surely (`ae_etaCoord_eq_zero`), the phase
evaluation at every face point is `N(0, σ²(v))` with `σ²(v) = Var[ξ_{Y₀}(v)]` (CLXIV), and the
Gaussian first moment of the phase-dressed moment is `E J_{2λ}(N(0,σ²)) = Γ(λ)(β(1 − βσ²/2))^{−λ}/2`
(`phaseMoment_eq_half_fluctuation`, `integral_fluctuation_gaussianReal`). Fubini over the face then
gives

`E_ν[C^b_{λ₀,m₀−1}(Z + A)] = b^{|h|+d} c^{−λ₀} K_face · (Γ(λ₀)/2) ∫_{(0,1]^d} η_A(π u)
  (β(1 − βσ²(π u)/2))^{−λ₀} w(u) du / 2^{m₀−1}`

(`integral_dataBoxCoeff_leading_eq`), with `π` the face projection and `w` the residual weight:
the population face integral with the temperature `β` replaced pointwise by
`β(1 − βσ²(π u)/2)` — a single scalar temperature only if `σ²` is constant on the face. Requires
`βM₀² < 2` for bounded observations `‖Y₀‖_{ℓ¹} ≤ M₀`.

Non-claims: no identification with a single-temperature population coefficient; the field limit and
the external remainder of the annealed theorem are as before.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Grammar

open CoeffFamily

/-! ### The phase-dressed moment and its Gaussian first moment -/

/-- `J_{2λ}^{(β)}(a) = S_λ(a)/2`: the phase-dressed moment is half the fluctuation function. -/
theorem phaseMoment_eq_half_fluctuation (β l a : ℝ) :
    phaseMoment β (2 * l) a = fluctuation β l a / 2 := by
  have h := fluctMoment_eq_two_mul_phaseMoment β a l
  have e : fluctMoment β a 0 l 0 = fluctuation β l a := by
    unfold fluctMoment fluctuation
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [pow_zero, mul_one, phaseKernel, one_mul]
    congr 2
    ring
  rw [e] at h
  linarith

/-- **The Gaussian first moment of the fluctuation function on the real line**:
`E S_λ(N(0,v)) = Γ(λ)(β(1 − βv/2))^{−λ}` for `βv < 2`. -/
theorem integral_fluctuation_gaussianReal (β lam v : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (hv : 0 ≤ v) (h : β * v < 2) :
    Integrable (fluctuation β lam) (gaussianReal 0 v.toNNReal) ∧
      ∫ a, fluctuation β lam a ∂gaussianReal 0 v.toNNReal =
        Real.Gamma lam * (β * (1 - β * v / 2)) ^ (-lam) := by
  set A : Matrix (Fin 1) (Fin (0 + 1)) ℝ := !![Real.sqrt v] with hAdef
  have hAA : (A * A.transpose : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = v := by
    simp [hAdef, Matrix.mul_apply, Real.mul_self_sqrt hv]
  have hmap := gaussianVector_map_eval A 0
  rw [hAA] at hmap
  have hδ : 0 < 1 - β * (A * A.transpose : Matrix (Fin 1) (Fin 1) ℝ) 0 0 / 2 := by
    rw [hAA]; linarith
  obtain ⟨hint, hval⟩ := integral_fluctuation_gaussianVector A β lam hβ hlam 0 hδ
  rw [hAA] at hval
  have hfm : Measurable (fluctuation β lam) := (continuous_fluctuation β lam hβ hlam).measurable
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact (integrable_map_measure hfm.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).2 hint
  · rw [← hmap, integral_map (measurable_pi_apply 0).aemeasurable hfm.aestronglyMeasurable]
    exact hval

/-- The variance of a bounded variable is at most the square of the bound. -/
theorem variance_le_sq_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) {M : ℝ}
    (hM : ∀ ω, |X ω| ≤ M) : Var[X; P] ≤ M ^ 2 := by
  refine (variance_le_expectation_sq hX).trans ?_
  calc ∫ ω, (X ^ 2) ω ∂P ≤ ∫ _ω, M ^ 2 ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          (integrable_const _) (Eventually.of_forall fun ω => ?_)
        simp only [Pi.pow_apply]
        exact (sq_abs (X ω)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hM ω) 2
    _ = M ^ 2 := by simp

/-! ### The amplitude coordinates of the `ℓ¹` Gaussian limit vanish -/

section Amplitude

variable {d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧] (b : ℝ) (hb : 0 < b) (c : 𝓧 → CoeffFamily d)
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

/-- The variance of the phase evaluation of the phase observation at `v`. -/
noncomputable def phaseVar (v : Fin d → ℝ) : ℝ :=
  Var[fun ω => evalF (xiCoord (phaseObs b hb c hc (X 0 ω))) v; P]

omit [MeasurableSpace 𝓧] [IsProbabilityMeasure P] in
theorem phaseVar_nonneg (v : Fin d → ℝ) : 0 ≤ phaseVar b hb c hc P X v := variance_nonneg _ _

theorem phaseVar_le (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) {v : Fin d → ℝ} (hv : v ∈ closedCube d) :
    phaseVar b hb c hc P X v ≤ M₀ ^ 2 := by
  refine variance_le_sq_of_abs_le ?_ fun ω => ?_
  · exact ((continuous_evalF_xiCoord hv).measurable.comp
      ((measurable_phaseObs b hb c hc hcm).comp (hXm 0))).aestronglyMeasurable
  · exact (abs_evalF_le (absSummable_xiCoord _) hv).trans ((mass_xiCoord_le _).trans (hM _))

/-- **The amplitude coordinates of the `ℓ¹` Gaussian limit of the phase observations vanish
almost surely.** -/
theorem ae_etaCoord_eq_zero (hcm : ∀ γ, Measurable fun x => c x γ) (hXm : ∀ i, Measurable (X i))
    (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin d → ℕ => b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) {ν : ProbabilityMeasure (L1Seq (DataIdx d))}
    (hmarg : ∀ F : Finset (DataIdx d), (ν : Measure (L1Seq (DataIdx d))).map (finiteCoords F) =
      gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx d),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx d))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F)) :
    ∀ᵐ Z ∂(ν : Measure (L1Seq (DataIdx d))), etaCoord Z = 0 := by
  have hY := summableCoordL2_sampleObs b hb c hc P X hcm (hXm 0) hc2 hsum
  have key : ∀ γ : Fin d → ℕ, ∀ᵐ Z ∂(ν : Measure (L1Seq (DataIdx d))), Z (Sum.inr γ) = 0 := by
    intro γ
    have hL := map_eq_gaussianReal_of_marginals hY hmarg htail (coordCLM (Sum.inr γ))
      (fun ω => hM (X 0 ω))
    have hvar : Var[fun ω => coordCLM (Sum.inr γ) (sampleObs b hb c hc X 0 ω); P] = 0 := by
      have e : (fun ω => coordCLM (Sum.inr γ) (sampleObs b hb c hc X 0 ω)) = fun _ => (0 : ℝ) := by
        funext ω
        simp [sampleObs, phaseObs_inr]
      rw [e]
      exact variance_zero P
    rw [hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hL
    have hs : MeasurableSet {x : ℝ | ¬ x = 0} := by
      convert (measurableSet_singleton (0 : ℝ)).compl using 1
      ext x
      simp
    rw [ae_iff]
    change (ν : Measure (L1Seq (DataIdx d))) (coordCLM (Sum.inr γ) ⁻¹' {x : ℝ | ¬ x = 0}) = 0
    rw [← Measure.map_apply (coordCLM (Sum.inr γ)).continuous.measurable hs, hL,
      Measure.dirac_apply' _ hs, Set.indicator_of_notMem]
    simp
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with Z hZ
  funext γ
  exact hZ γ

end Amplitude

/-! ### The leading coefficient as a face functional and its Gaussian first moment -/

section Moment

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ} (hβ : 0 < β) {b : ℝ}
  (hb : 0 < b) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)

include hk hβ hb hmin hatt in
/-- **The leading coefficient at box radius `b` is the face functional of the represented phase and
amplitude**: `C^b_{λ,m−1}(x) = b^{|h|+d} c^{−λ} · spatialFace(ξ_x, η_x)`. -/
theorem dataBoxCoeff_leading_eq_spatialFace (x : DataSpace (n + 1)) :
    dataBoxCoeff n h k β b x l (multCount (ratioExp h k) l - 1) =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
        spatialFace h k l β (dataPhase x) (dataAmplitude x) := by
  have hm_le : multCount (ratioExp h k) l - 1 ≤ n := by
    have := multCount_le_card (ratioExp h k) l
    omega
  rw [dataBoxCoeff_eq n h k β hb x l _]
  congr 1
  rw [Finset.sum_eq_single (multCount (ratioExp h k) l - 1)]
  · rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one, mul_one,
      ← dataBoxCoeff_one n h k β x l hm_le]
    exact (dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).2
  · intro q hq hne
    rw [Finset.mem_Ico] at hq
    have hlt : multCount (ratioExp h k) l - 1 < q := lt_of_le_of_ne hq.1 (Ne.symm hne)
    rw [← dataBoxCoeff_one n h k β x l (by omega),
      (dataBoxCoeff_spatialFace n h k hk hβ hmin hatt x).1 q hlt, zero_mul, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) hnot

theorem xiCoord_add {d : ℕ} (x y : DataSpace d) :
    xiCoord (x + y) = fun γ => xiCoord x γ + xiCoord y γ := by
  funext γ
  simp [xiCoord]

theorem etaCoord_add {d : ℕ} (x y : DataSpace d) :
    etaCoord (x + y) = fun γ => etaCoord x γ + etaCoord y γ := by
  funext γ
  simp [etaCoord]

theorem dataPhase_add_of_xiCoord_eq_zero {d : ℕ} (Z A : DataSpace d) (hA : xiCoord A = 0) :
    dataPhase (Z + A) = dataPhase Z := by
  funext u
  unfold dataPhase
  rw [xiCoord_add, hA]
  simp

theorem dataAmplitude_add_of_etaCoord_eq_zero {d : ℕ} (Z A : DataSpace d)
    (hZ : etaCoord Z = 0) : dataAmplitude (Z + A) = dataAmplitude A := by
  funext u
  unfold dataAmplitude
  rw [etaCoord_add, hZ]
  simp

variable {𝓧 : Type*} [MeasurableSpace 𝓧] (c : 𝓧 → CoeffFamily (n + 1))
  (hc : ∀ x, AbsSummableAt (c x) b)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → 𝓧)

include hβ in
/-- The Gaussian first moment of the phase-dressed moment of the `ℓ¹` limit at a face point:
`E_ν J_{2λ}(ξ_Z(v)) = Γ(λ)(β(1 − βσ²(v)/2))^{−λ}/2`. -/
theorem integral_phaseMoment_evalF (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) (hβM : β * M₀ ^ 2 < 2) (hl : 0 < l)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    {v : Fin (n + 1) → ℝ} (hv : v ∈ closedCube (n + 1)) :
    Integrable (fun Z : DataSpace (n + 1) => phaseMoment β (2 * l) (evalF (xiCoord Z) v))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, phaseMoment β (2 * l) (evalF (xiCoord Z) v) ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X v / 2)) ^ (-l) / 2 := by
  have hσ : β * phaseVar b hb c hc P X v < 2 := by
    have h1 := phaseVar_le b hb c hc P X hcm hXm hM hv
    have : β * phaseVar b hb c hc P X v ≤ β * M₀ ^ 2 := mul_le_mul_of_nonneg_left h1 hβ.le
    linarith
  have hL := map_phaseEvalCLM_eq_gaussianReal b hb c hc P X hcm hXm hc2 hsum hM hmarg htail hv
  obtain ⟨hint, hval⟩ := integral_fluctuation_gaussianReal β l _ hβ hl
    (phaseVar_nonneg b hb c hc P X v) hσ
  have hfm : Measurable (fluctuation β l) := (continuous_fluctuation β l hβ hl).measurable
  have hLm : Measurable (phaseEvalCLM v hv) := (phaseEvalCLM v hv).continuous.measurable
  have e : (fun Z : DataSpace (n + 1) => phaseMoment β (2 * l) (evalF (xiCoord Z) v)) =
      fun Z => fluctuation β l (phaseEvalCLM v hv Z) / 2 := by
    funext Z
    rw [phaseMoment_eq_half_fluctuation, phaseEvalCLM_apply]
  rw [e]
  have hint' : Integrable (fun Z : DataSpace (n + 1) => fluctuation β l (phaseEvalCLM v hv Z))
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := by
    have := (integrable_map_measure hfm.aestronglyMeasurable hLm.aemeasurable).1 (hL ▸ hint)
    exact this
  refine ⟨hint'.div_const 2, ?_⟩
  unfold phaseVar at hval ⊢
  rw [integral_div, ← integral_map hLm.aemeasurable hfm.aestronglyMeasurable, hL, hval]

include hk hβ hb hmin hatt in
/-- **The Gaussian first moment of the leading coefficient at the `ℓ¹` Gaussian limit**: for
bounded phase observations (`βM₀² < 2`) and a zero-phase amplitude datum `A`,
`E_ν[C^b_{λ,m−1}(Z + A)] = b^{|h|+d} c^{−λ} K_face (Γ(λ)/2) ∫_{(0,1]^d} η_A(π u)
(β(1 − βσ²(π u)/2))^{−λ} w(u) du / 2^{m−1}` — the population face integral with the temperature
`β` replaced pointwise by `β(1 − βσ²(π u)/2)`, `σ²(v) = Var[ξ_{Y₀}(v)]`; the leading coefficient
is `ν`-integrable. -/
theorem integral_dataBoxCoeff_leading_eq (hcm : ∀ γ, Measurable fun x => c x γ)
    (hXm : ∀ i, Measurable (X i)) (hc2 : ∀ γ, MemLp (fun ω => c (X 0 ω) γ) 2 P)
    (hsum : Summable fun γ : Fin (n + 1) → ℕ =>
      b ^ (∑ i, γ i) * Real.sqrt (∫ ω, (c (X 0 ω) γ) ^ 2 ∂P))
    {M₀ : ℝ} (hM : ∀ x, ‖phaseObs b hb c hc x‖ ≤ M₀) (hβM : β * M₀ ^ 2 < 2)
    {ν : ProbabilityMeasure (L1Seq (DataIdx (n + 1)))}
    (hmarg : ∀ F : Finset (DataIdx (n + 1)),
      (ν : Measure (L1Seq (DataIdx (n + 1)))).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (sampleObs b hb c hc X 0 ω)) P)
    (htail : ∀ F : Finset (DataIdx (n + 1)),
      ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) ≤
        ENNReal.ofReal (sigmaTail P (sampleObs b hb c hc X 0) F))
    (A : DataSpace (n + 1)) (hA : xiCoord A = 0) :
    Integrable (fun Z : DataSpace (n + 1) =>
        dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1))
        (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)
          ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) *
          (1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
              ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
            (∫ u in unitBox (n + 1), faceWeight h k l (dataAmplitude A) u *
              (Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X
                (cubeClamp (faceProj h k l u)) / 2)) ^ (-l) / 2)) /
            2 ^ (multCount (ratioExp h k) l - 1)) := by
  have hl : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  set K₁ : ℝ := b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) with hK₁
  set K₂ : ℝ := 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
    ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) with hK₂
  set F : (Fin (n + 1) → ℝ) → DataSpace (n + 1) → ℝ := fun u Z =>
    faceWeight h k l (dataAmplitude A) u *
      phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u))) with hF
  -- the pointwise identity for data with vanishing amplitude
  have hae := ae_etaCoord_eq_zero b hb c hc P X hcm hXm hc2 hsum hM hmarg htail
  have hpt : ∀ Z : DataSpace (n + 1), etaCoord Z = 0 →
      dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1) =
        K₁ * (K₂ * (∫ u in unitBox (n + 1), F u Z) / 2 ^ (multCount (ratioExp h k) l - 1)) := by
    intro Z hZ
    rw [dataBoxCoeff_leading_eq_spatialFace n h k hk hβ hb hmin hatt,
      dataPhase_add_of_xiCoord_eq_zero Z A hA, dataAmplitude_add_of_etaCoord_eq_zero Z A hZ,
      spatialFace_eq_faceWeight]
    rfl
  -- joint measurability
  have hξ : Measurable (fun p : (Fin (n + 1) → ℝ) × DataSpace (n + 1) =>
      evalF (xiCoord p.2) (cubeClamp (faceProj h k l p.1))) :=
    (measurable_uncurry_xiField measurable_id).comp
      (measurable_snd.prodMk ((measurable_faceProj h k l).comp measurable_fst))
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_faceWeight h k l (continuous_dataAmplitude A)).comp measurable_fst).mul
      ((continuous_phaseMoment β (2 * l) hβ (by linarith)).measurable.comp hξ)
  -- the inner Gaussian moment
  have hinner : ∀ u : Fin (n + 1) → ℝ,
      Integrable (fun Z => F u Z) (ν : Measure (L1Seq (DataIdx (n + 1)))) ∧
      ∫ Z, F u Z ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) =
        faceWeight h k l (dataAmplitude A) u *
          (Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X
            (cubeClamp (faceProj h k l u)) / 2)) ^ (-l) / 2) := by
    intro u
    obtain ⟨hint, hval⟩ := integral_phaseMoment_evalF n hβ hb c hc P X hcm hXm hc2 hsum hM hβM
      hl hmarg htail (cubeClamp_mem_closedCube (faceProj h k l u))
    refine ⟨hint.const_mul _, ?_⟩
    change ∫ Z, faceWeight h k l (dataAmplitude A) u *
      phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u)))
        ∂(ν : Measure (L1Seq (DataIdx (n + 1)))) = _
    rw [integral_const_mul, hval]
  -- the uniform bound on the Gaussian moment
  have hC₀ : ∀ u : Fin (n + 1) → ℝ,
      |Real.Gamma l * (β * (1 - β * phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) / 2))
        ^ (-l) / 2| ≤ Real.Gamma l * (β * (1 - β * M₀ ^ 2 / 2)) ^ (-l) / 2 := by
    intro u
    have hσle := phaseVar_le b hb c hc P X hcm hXm hM (cubeClamp_mem_closedCube (faceProj h k l u))
    have hσ0 := phaseVar_nonneg b hb c hc P X (cubeClamp (faceProj h k l u))
    have hpos : 0 < β * (1 - β * M₀ ^ 2 / 2) := mul_pos hβ (by linarith)
    have hσβ : β * phaseVar b hb c hc P X (cubeClamp (faceProj h k l u)) ≤ β * M₀ ^ 2 :=
      mul_le_mul_of_nonneg_left hσle hβ.le
    have hG := Real.Gamma_pos_of_pos hl
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hG.le (Real.rpow_nonneg
      (mul_nonneg hβ.le (by linarith)) _)) two_pos.le)]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hG.le) two_pos.le
    exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith) (by linarith)
  -- product integrability in the order (u, Z)
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (unitBox (n + 1))).prod (ν : Measure (L1Seq (DataIdx (n + 1))))) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun u => (hinner u).1, ?_⟩
    have hbound : ∀ u, ‖∫ Z, ‖F u Z‖ ∂(ν : Measure (L1Seq (DataIdx (n + 1))))‖ ≤
        ‖faceWeight h k l (dataAmplitude A) u‖ *
          (Real.Gamma l * (β * (1 - β * M₀ ^ 2 / 2)) ^ (-l) / 2) := by
      intro u
      have h1 : ∀ Z, ‖F u Z‖ = ‖faceWeight h k l (dataAmplitude A) u‖ *
          phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u))) := by
        intro Z
        change ‖faceWeight h k l (dataAmplitude A) u *
          phaseMoment β (2 * l) (evalF (xiCoord Z) (cubeClamp (faceProj h k l u)))‖ = _
        rw [norm_mul, Real.norm_eq_abs (phaseMoment _ _ _),
          abs_of_pos (phaseMoment_pos β (2 * l) _ hβ (by linarith))]
      simp_rw [h1]
      rw [integral_const_mul, norm_mul, norm_norm]
      obtain ⟨-, hval⟩ := integral_phaseMoment_evalF n hβ hb c hc P X hcm hXm hc2 hsum hM hβM
        hl hmarg htail (cubeClamp_mem_closedCube (faceProj h k l u))
      rw [hval, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC₀ u) (abs_nonneg _)
    exact Integrable.mono'
      ((integrableOn_faceWeight h k hk hmin (continuous_dataAmplitude A)).norm.mul_const _)
      hFm.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall hbound)
  -- Fubini and assembly
  have hswap := integral_integral_swap hprod
  have hintZ : Integrable (fun Z => ∫ u in unitBox (n + 1), F u Z)
      (ν : Measure (L1Seq (DataIdx (n + 1)))) := hprod.integral_prod_right
  have hae' : (fun Z : DataSpace (n + 1) =>
      dataBoxCoeff n h k β b (Z + A) l (multCount (ratioExp h k) l - 1)) =ᵐ[
        (ν : Measure (L1Seq (DataIdx (n + 1))))]
      fun Z => K₁ * (K₂ * (∫ u in unitBox (n + 1), F u Z) / 2 ^ (multCount (ratioExp h k) l - 1)) :=
    hae.mono fun Z hZ => hpt Z hZ
  refine ⟨(((hintZ.const_mul K₂).div_const _).const_mul K₁).congr hae'.symm, ?_⟩
  rw [integral_congr_ae hae', integral_const_mul, integral_div, integral_const_mul, ← hswap]
  congr 3
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
  exact (hinner u).2

end Moment

end Grammar
