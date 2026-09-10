import Grammar.CoordFreeTaylorMoment
import Grammar.GeometricMainTheorem

/-!
# Certified finite box reduction and the grammar application (Astra #63 unit 7)

The coordinate-free objects of units 1–6 applied to the certified chart presentations of the
conditional geometric main theorem (CXIII):

* **unconditional frame covariance**: for a fibre-frame *equivalence* the chosen-normal jets and
  Taylor forms transform by composition with no regularity hypothesis on `F ∘ Φ_s`
  (`rawNormalJet_comp_equiv`, `normalTaylorForm_comp_equiv`), so the frame-coordinate reduction of
  the invariant contraction and its reparametrisation invariance hold unconditionally
  (`normalContraction_frame'`, `normalContraction_reparam'`);
* **`rem:reduce_to_box`, corrected**: the fibre pairing of a fibrewise supported density restricts
  to the fixed box (`integral_mul_eq_setIntegral_of_support`) and admits the insertion of a cutoff
  `κ ≡ 1` on the support (`integral_mul_cutoff_insert`), giving
  `⟨α, 𝖬_r(v)⟩ = ∫_{box} α(u,…,u) w(u) κ(u) g(v,u) du` (`pairing_eq_box_cutoff`);
* **the chart normal family**: a trivialised tube `S × ℝ^d` with fibre maps `Φ₀ s` and weighted
  fibre measures `η₀ s` is a chosen normal family with `N s = ℝ^d` (`chartNormal`,
  `chartFibreMap`, `chartFibreMeasure`, frame `topFrame`), and its invariant contraction is the
  chart moment pairing `(1/r!)⟨Moment_{η₀ s,r}, D^r(F∘Φ₀ s)(0)⟩` (`normalContraction_chart`);
* **the grammar application**: for a localisation datum with adapted strata data and normal-moment
  presentations, the resolved population integral is the finite sum over the trivialised cover of
  the base integrals of the **coordinate-free contraction series** plus the exponentially small
  tail, `Z(N) = ∑_I ∫_{K_I} ∑_r ⟨D^r_⊥F, 𝖬_{I,r}(N)⟩ dν_I + tail(N)`
  (`Z_eq_tsum_normalContraction`), equivalently in multi-index form with the dressed moments of
  the raw fibre measures (`Z_eq_tsum_multiIndex`), and the contraction series is a
  `CutoffExpansion` with the assembled canonical coefficients
  (`normalContractionSeries_cutoffExpansion`) — the corrected `eq:per_stratum_expansion_coordfree`
  and `eq:tubular_expansion` for the actual grammar integral, with the asymptotic content carried
  by CXIII's `AdaptedStrataData.cutoffExpansion`.

Non-claims: production of adapted charts or analytic cutoffs, absorption of phase units, and any
asymptotic ordering by normal degree beyond what CXIII proves.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal

namespace Grammar

open MonoRep

/-! ### Unconditional frame covariance under fibre-frame equivalences -/

section Equiv

variable {S : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
  (N : S → Submodule ℝ E) (Φ : ∀ s, N s → M) (F : M → ℝ) (s : S)
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Frame covariance for a frame equivalence needs no regularity**:
`J_r(F∘Φ_s∘e) = J_r ∘ (e,…,e)`. -/
theorem rawNormalJet_comp_equiv (e : V ≃L[ℝ] N s) (r : ℕ) :
    iteratedFDeriv ℝ r (fun v : V => F (Φ s (e v))) 0 =
      (rawNormalJet N Φ F s r).compContinuousLinearMap fun _ => (e : V →L[ℝ] N s) := by
  have h := e.iteratedFDerivWithin_comp_right (fun n : N s => F (Φ s n)) uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) r
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at h
  exact h

theorem normalTaylorForm_comp_equiv (e : V ≃L[ℝ] N s) (r : ℕ) :
    (r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => F (Φ s (e v))) 0 =
      (normalTaylorForm N Φ F s r).compContinuousLinearMap fun _ => (e : V →L[ℝ] N s) := by
  rw [rawNormalJet_comp_equiv N Φ F s e r]
  ext m
  simp [normalTaylorForm]

variable [MeasurableSpace E] [BorelSpace E] (η : ∀ s, Measure (N s)) {r : ℕ}
  (hr : ∀ s, Integrable (fun ξ : N s => ‖ξ‖ ^ r) (η s))

/-- The contraction in a fibre frame, unconditionally. -/
theorem normalContraction_frame' [MeasurableSpace V] [BorelSpace V] (e : V ≃L[ℝ] N s) :
    normalContraction N η hr Φ F s =
      momentFunctional ((η s).map (e.symm : N s →L[ℝ] V)) (integrable_norm_pow_map' _ (hr s))
        ((r.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ r (fun v : V => F (Φ s (e v))) 0) := by
  unfold normalContraction
  rw [← normalMoment_comp_equiv N η hr s e, normalTaylorForm_comp_equiv N Φ F s e r]

/-- Reparametrisation invariance of the contraction, unconditionally. -/
theorem normalContraction_reparam' (L : ∀ s, N s ≃L[ℝ] N s) :
    normalContraction N (fun s => (η s).map ((L s).symm : N s →L[ℝ] N s))
        (fun s => integrable_norm_pow_map' _ (hr s)) (fun s n => Φ s (L s n)) F s =
      normalContraction N η hr Φ F s := by
  unfold normalContraction normalMoment
  rw [← moment_pairing_comp_equiv (L s) (hr s) (normalTaylorForm N Φ F s r),
    ← normalTaylorForm_comp_equiv N Φ F s (L s) r]
  rfl

end Equiv

/-! ### `rem:reduce_to_box`: support restriction and cutoff insertion -/

section Box

variable {E : Type*} [MeasurableSpace E] (μ : Measure E)

/-- A fibrewise supported density restricts the pairing to the box. -/
theorem integral_mul_eq_setIntegral_of_support {g : E → ℝ} {B : Set E} (hg : ∀ u ∉ B, g u = 0)
    (f : E → ℝ) : ∫ u, f u * g u ∂μ = ∫ u in B, f u * g u ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by rw [hg u hu, mul_zero]).symm

/-- A cutoff equal to `1` on the support of the density can be inserted. -/
theorem integral_mul_cutoff_insert {g κ : E → ℝ} {B : Set E} (hB : MeasurableSet B)
    (hκ : ∀ u, g u ≠ 0 → κ u = 1) (f : E → ℝ) :
    ∫ u in B, f u * g u ∂μ = ∫ u in B, f u * κ u * g u ∂μ := by
  refine setIntegral_congr_fun hB fun u _ => ?_
  by_cases hgu : g u = 0
  · simp [hgu]
  · rw [hκ u hgu, mul_one]

/-- **`rem:reduce_to_box`, corrected**: for a fibre density `g(v,·)` supported in the box `B` and a
cutoff `κ ≡ 1` on that support, the fibre pairing is the box integral
`⟨α, 𝖬_r(v)⟩ = ∫_B α(u,…,u) w(u) κ(u) g(v,u) du`. -/
theorem pairing_eq_box_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) {r : ℕ} (α : JetForm E r) (w g κ : E → ℝ) {B : Set E}
    (hB : MeasurableSet B) (hg : ∀ u ∉ B, g u = 0) (hκ : ∀ u, g u ≠ 0 → κ u = 1) :
    ∫ u, α (fun _ => u) * w u * g u ∂μ = ∫ u in B, α (fun _ => u) * w u * κ u * g u ∂μ := by
  rw [integral_mul_eq_setIntegral_of_support μ hg, integral_mul_cutoff_insert μ hB hκ]

end Box

/-! ### The chart normal family -/

section Chart

variable {S : Type*} {M : Type*} {d : ℕ}

/-- The normal spaces of a trivialised tube: all of `ℝ^d`. -/
abbrev chartNormal (S : Type*) (d : ℕ) : S → Submodule ℝ (Fin d → ℝ) := fun _ => ⊤

/-- The frame `ℝ^d ≃L ⊤`. -/
noncomputable def topFrame (d : ℕ) : (Fin d → ℝ) ≃L[ℝ] ↥(⊤ : Submodule ℝ (Fin d → ℝ)) :=
  (Submodule.topEquiv (R := ℝ) (M := Fin d → ℝ)).symm.toContinuousLinearEquiv

@[simp] theorem topFrame_apply_coe (u : Fin d → ℝ) :
    ((topFrame d u : ↥(⊤ : Submodule ℝ (Fin d → ℝ))) : Fin d → ℝ) = u := rfl

@[simp] theorem topFrame_symm_apply (n : ↥(⊤ : Submodule ℝ (Fin d → ℝ))) :
    (topFrame d).symm n = (n : Fin d → ℝ) := rfl

/-- The fibre maps of the chart family. -/
def chartFibreMap (Φ₀ : S → (Fin d → ℝ) → M) : ∀ s, chartNormal S d s → M :=
  fun s n => Φ₀ s (n : Fin d → ℝ)

/-- The fibre measures of the chart family, transported to `⊤`. -/
noncomputable def chartFibreMeasure (η₀ : S → Measure (Fin d → ℝ)) :
    ∀ s, Measure (chartNormal S d s) :=
  fun s => (η₀ s).map (topFrame d : (Fin d → ℝ) →L[ℝ] ↥(⊤ : Submodule ℝ (Fin d → ℝ)))

theorem chartFibreMeasure_map_symm (η₀ : S → Measure (Fin d → ℝ)) (s : S) :
    (chartFibreMeasure η₀ s).map
        ((topFrame d).symm : ↥(⊤ : Submodule ℝ (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ)) = η₀ s :=
  MeasurableEquiv.map_symm_map (μ := η₀ s) (topFrame d).toHomeomorph.toMeasurableEquiv

theorem integrable_norm_pow_chartFibreMeasure {η₀ : S → Measure (Fin d → ℝ)} {r : ℕ}
    (hr : ∀ s, Integrable (fun u => ‖u‖ ^ r) (η₀ s)) (s : S) :
    Integrable (fun ξ : chartNormal S d s => ‖ξ‖ ^ r) (chartFibreMeasure η₀ s) :=
  integrable_norm_pow_map' _ (hr s)

/-- **The invariant contraction of the chart family is the chart moment pairing**
`(1/r!) ⟨Moment_{η₀ s, r}, D^r(F∘Φ₀ s)(0)⟩`. -/
theorem normalContraction_chart (Φ₀ : S → (Fin d → ℝ) → M) (η₀ : S → Measure (Fin d → ℝ)) {r : ℕ}
    (hr : ∀ s, Integrable (fun u => ‖u‖ ^ r) (η₀ s)) (F : M → ℝ) (s : S) :
    normalContraction (chartNormal S d) (chartFibreMeasure η₀)
        (integrable_norm_pow_chartFibreMeasure hr) (chartFibreMap Φ₀) F s =
      (r.factorial : ℝ)⁻¹ * ∫ u, normalJet (fun u => F (Φ₀ s u)) r (fun _ => u) ∂η₀ s := by
  rw [normalContraction_frame' (chartNormal S d) (chartFibreMap Φ₀) F s (chartFibreMeasure η₀)
    (integrable_norm_pow_chartFibreMeasure hr) (topFrame d), momentFunctional_apply,
    chartFibreMeasure_map_symm, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  beta_reduce
  rw [smul_apply, smul_eq_mul]
  rfl

end Chart

/-! ### The grammar application -/

section Grammar

/-- The multi-index form of a chart moment term for an analytic observable. -/
theorem moment_term_eq_sum_multiIndex {d : ℕ} {G : (Fin d → ℝ) → ℝ} (hG : ContDiffAt ℝ ω G 0)
    (η : Measure (Fin d → ℝ)) {r : ℕ} (hr : Integrable (fun u => ‖u‖ ^ r) η) :
    (r.factorial : ℝ)⁻¹ * ∫ u, normalJet G r (fun _ => u) ∂η =
      ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
        (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet G r) b * dressedMoment η b := by
  rw [← integral_const_mul]
  have h1 : ∀ u, (r.factorial : ℝ)⁻¹ * normalJet G r (fun _ => u) =
      ∑ b ∈ Finset.Nat.antidiagonalTuple d r,
        (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet G r) b * mono b u :=
    fun u => homogeneousTaylor_eq_sum_multiIndex hG r u
  simp_rw [h1]
  rw [integral_finsetSum _ fun b hb => (integrable_mono_of_sum_eq hr
    (Finset.Nat.mem_antidiagonalTuple.1 hb)).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]
  rfl

namespace AdaptedStrataData

variable {U : Type*} [MeasurableSpace U] {D : LocalisationData U} {M : ℕ} {K : Fin M → Type*}
  [∀ I, TopologicalSpace (K I)] [∀ I, MeasurableSpace (K I)] {n : Fin M → ℕ} {β : ℝ}
  (A : AdaptedStrataData D M K n β)

/-- The chart fibre maps of the `I`-th chart. -/
def fibreMap (I : Fin M) : K I → (Fin (n I + 1) → ℝ) → U := fun v u => (A.chart I).Φ (v, u)

/-- The raw fibre measures of the `I`-th chart at sample size `N`. -/
noncomputable def fibreMeasures (I : Fin M) (N : ℝ) : K I → Measure (Fin (n I + 1) → ℝ) :=
  fun v => (A.chart I).fibreMeasure v N

/-- **The resolved population integral as the finite sum over the trivialised cover of base
integrals of the coordinate-free contraction series**, `Z(N) = ∑_I ∫_{K_I} ∑_r ⟨D^r_⊥F, 𝖬_{I,r}(N)⟩
dν_I + tail(N)`, for the chart normal families of the certified presentation. -/
theorem Z_eq_tsum_normalContraction (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = ∑ I, (∫ v, ∑' r, normalContraction (chartNormal (K I) (n I + 1))
      (chartFibreMeasure (A.fibreMeasures I N))
      (integrable_norm_pow_chartFibreMeasure fun v => (T I).integrable_norm_pow_fibre hβ hN v r)
      (chartFibreMap (A.fibreMap I)) D.obs v ∂(A.chart I).ν) + A.tail N := by
  rw [A.Z_eq_moment_series T hβ hN]
  congr 1
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae (Eventually.of_forall fun v => ?_)
  refine tsum_congr fun r => ?_
  rw [normalContraction_chart (A.fibreMap I) (A.fibreMeasures I N)
    (fun v => (T I).integrable_norm_pow_fibre hβ hN v r) D.obs v]
  rfl

/-- **The multi-index form**:
`Z(N) = ∑_I ∫_{K_I} ∑_r ∑_{|b|=r} (∂^b(F∘Φ_I(v,·))(0)/b!) M̃_b(v,N) dν_I + tail(N)` with the dressed
moments of the raw fibre measures. -/
theorem Z_eq_tsum_multiIndex (T : ∀ I, NormalMomentPresentation (A.chart I)) (hβ : 0 ≤ β)
    {N : ℝ} (hN : 0 ≤ N) :
    D.Z N = ∑ I, (∫ v, ∑' r, ∑ b ∈ Finset.Nat.antidiagonalTuple (n I + 1) r,
      (∏ i, ((b i).factorial : ℝ))⁻¹ * weightComponent (normalJet ((A.chart I).obsFibre v) r) b *
        dressedMoment ((A.chart I).fibreMeasure v N) b ∂(A.chart I).ν) + A.tail N := by
  rw [A.Z_eq_moment_series T hβ hN]
  congr 1
  refine Finset.sum_congr rfl fun I _ => integral_congr_ae (Eventually.of_forall fun v => ?_)
  refine tsum_congr fun r => ?_
  exact moment_term_eq_sum_multiIndex ((T I).analytic v).analyticAt.contDiffAt _
    ((T I).integrable_norm_pow_fibre hβ hN v r)

variable [∀ I, CompactSpace (K I)] [∀ I, T2Space (K I)] [∀ I, OpensMeasurableSpace (K I)]

/-- **Canonical compatibility of the coordinate-free contraction series**: it is a
`CutoffExpansion` with the assembled canonical coefficients of CXIII. -/
theorem normalContractionSeries_cutoffExpansion (T : ∀ I, NormalMomentPresentation (A.chart I))
    (hβ : 0 < β) :
    CutoffExpansion (commonQ A.k) (commonD n) (fun N => ∑ I, ∫ v, ∑' r,
      normalContraction (chartNormal (K I) (n I + 1))
        (chartFibreMeasure (A.fibreMeasures I (max N 0)))
        (integrable_norm_pow_chartFibreMeasure fun v =>
          (T I).integrable_norm_pow_fibre hβ.le (le_max_right N 0) v r)
        (chartFibreMap (A.fibreMap I)) D.obs v ∂(A.chart I).ν) (gCoeff A.ν A.h A.k β A.b A.x) := by
  refine (A.momentSeries_cutoffExpansion T hβ).congr_eventually ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
  have h : ∀ (I : Fin M) (v : K I) (r : ℕ),
      normalContraction (chartNormal (K I) (n I + 1))
        (chartFibreMeasure (A.fibreMeasures I (max N 0)))
        (integrable_norm_pow_chartFibreMeasure fun v =>
          (T I).integrable_norm_pow_fibre hβ.le (le_max_right N 0) v r)
        (chartFibreMap (A.fibreMap I)) D.obs v =
      (r.factorial : ℝ)⁻¹ * ∫ u, normalJet ((A.chart I).obsFibre v) r (fun _ => u)
        ∂(A.chart I).fibreMeasure v N := by
    intro I v r
    rw [normalContraction_chart (A.fibreMap I) (A.fibreMeasures I (max N 0))
      (fun v => (T I).integrable_norm_pow_fibre hβ.le (le_max_right N 0) v r) D.obs v]
    unfold fibreMeasures
    rw [max_eq_left hN]
    rfl
  simp only [h]

end AdaptedStrataData

end Grammar

end Grammar
