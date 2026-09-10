import Grammar.FiniteWeightMoment
import Grammar.DataIntegralContinuity

/-!
# Uniform moments of the certified box model from the population mass at a reduced temperature

For random data `x : Ω → DataSpace (n+1)` (Borel measurable, `‖x‖ ≤ M`), the finite-`n` box
integral `dataBoxIntegral n h k β N b (x ω)` is, after the box scaling, the unit-box integral of the
raw coordinates with amplitude `evalF (etaCoord x) u` (bounded by `‖x‖`) and phase field
`ξ(ω,u) = evalF (xiCoord (x ω)) u`. If the phase field satisfies the pointwise exponential-moment
bound `E e^{tξ(·,u)} ≤ e^{ct²/2}` (`t ≥ 0`) at every point of the unit box, then for `p ≥ 1`,
`pβc < 2`, `α = β(1 − pβc/2)`:

**`E|A · dataBoxIntegral(β, N)|^p ≤ (M · A b^{|h|+d} · Z^pop_α(N'))^p`**,
`Z^pop_α(N') = ∫_{(0,1]^d} u^h e^{−αN' u^{2k}} du`, `N' = N b^{2|k|}`

(`moment_scaled_dataBoxIntegral_le`). Under a certified deterministic bound
`sup_{n ≥ n₀} A_n Z^pop_α(N'_n) ≤ C_α` the moments are bounded uniformly in `n`
(`uniform_moment_scaled_dataBoxIntegral`). Joint measurability of the phase field is obtained by
clipping to the closed cube (`clipCube`), where `evalF` is continuous, and Carathéodory.

Non-claims: the exponential-moment bound for the finite-`n` field throughout the box is a hypothesis
(bounded original observations do not automatically bound the normalised chart coefficients); the
deterministic population bound at temperature `α` is an input (it follows from a population core
theorem at that temperature, which is not invoked here); this is a sufficient bound.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

open CoeffFamily

section Clip

variable {d : ℕ}

/-- Clipping to the closed unit cube. -/
def clipCube (u : Fin d → ℝ) : Fin d → ℝ := fun i => max 0 (min 1 (u i))

theorem continuous_clipCube : Continuous (clipCube (d := d)) :=
  continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))

theorem clipCube_mem_closedCube (u : Fin d → ℝ) : clipCube u ∈ closedCube d := by
  intro i _
  simp only [clipCube, mem_Icc]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clipCube_eq_self_of_mem {u : Fin d → ℝ} (hu : u ∈ unitBox d) : clipCube u = u := by
  funext i
  have hi := hu i (mem_univ i)
  simp only [mem_Ioc] at hi
  simp only [clipCube]
  rw [min_eq_right hi.2, max_eq_right hi.1.le]

/-- The clipped phase field is continuous in the point. -/
theorem continuous_evalF_clip {c : CoeffFamily d} (hc : AbsSummable c) :
    Continuous fun u => evalF c (clipCube u) :=
  (continuousOn_evalF hc).comp_continuous continuous_clipCube clipCube_mem_closedCube

/-- On the closed cube the phase evaluation is `1`-Lipschitz in the data, hence continuous. -/
theorem continuous_evalF_xiCoord {u : Fin d → ℝ} (hu : u ∈ closedCube d) :
    Continuous fun x : DataSpace d => evalF (xiCoord x) u := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  have hs := absSummable_xiCoord (x - y)
  have e : xiCoord (x - y) = xiCoord x - xiCoord y := by
    funext γ
    simp [xiCoord]
  rw [← evalF_sub (absSummable_xiCoord x) (absSummable_xiCoord y) hu, ← e]
  exact (abs_evalF_le hs hu).trans (mass_xiCoord_le _)

/-- **Joint measurability of the clipped phase field** of measurable random data. -/
theorem measurable_uncurry_xiField {Ω : Type*} [MeasurableSpace Ω] {x : Ω → DataSpace d}
    (hx : Measurable x) :
    Measurable (Function.uncurry fun ω u => evalF (xiCoord (x ω)) (clipCube u)) := by
  have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun (u : Fin d → ℝ) ω => evalF (xiCoord (x ω)) (clipCube u))
    (fun ω => continuous_evalF_clip (absSummable_xiCoord (x ω)))
    (fun u => ((continuous_evalF_xiCoord (clipCube_mem_closedCube u)).measurable.comp
      hx).stronglyMeasurable)
  exact h.measurable.comp measurable_swap

end Clip

section Box

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (n : ℕ) (h k : Fin (n + 1) → ℕ)

/-- The population unit-box mass at temperature `α` and scale `N'`:
`∫_{(0,1]^d} u^h e^{−αN'u^{2k}} du`, written with `r(u) = √N' ∏u^k`. -/
noncomputable def popBoxMass (α N' : ℝ) : ℝ :=
  ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) *
    Real.exp (-α * (Real.sqrt N' * ∏ i, u i ^ k i) ^ 2)

theorem popBoxMass_eq (α N' : ℝ) (hN' : 0 ≤ N') :
    popBoxMass n h k α N' =
      ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * Real.exp (-(α * N' * ∏ i, u i ^ (2 * k i))) := by
  unfold popBoxMass
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  beta_reduce
  have hprod : ∏ i, (u i ^ k i) ^ 2 = ∏ i, u i ^ (2 * k i) :=
    Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  rw [mul_pow, Real.sq_sqrt hN', ← Finset.prod_pow, hprod]
  ring_nf

theorem integrableOn_popBoxIntegrand (α N' : ℝ) :
    IntegrableOn (fun u : Fin (n + 1) → ℝ => (∏ i, u i ^ h i) *
      Real.exp (-α * (Real.sqrt N' * ∏ i, u i ^ k i) ^ 2)) (unitBox (n + 1)) := by
  have hc : Continuous fun u : Fin (n + 1) → ℝ => (∏ i, u i ^ h i) *
      Real.exp (-α * (Real.sqrt N' * ∏ i, u i ^ k i) ^ 2) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedCube _)).mono_set
    (unitBox_subset_closedCube _)

/-- **Uniform `p`-th moment of the scaled box integral from the population mass at the reduced
temperature**: with amplitude mass `mass (etaCoord (x ω)) ≤ M` (e.g. `‖x ω‖ ≤ M`), the
pointwise exponential-moment bound on the phase field over
the unit box, `p ≥ 1`, `pβc < 2` and `α = β(1 − pβc/2)`,
`E|A · dataBoxIntegral(β,N,b)(x)|^p ≤ (M · A b^{|h|+d} · popBoxMass α (N b^{2|k|}))^p`. -/
theorem moment_scaled_dataBoxIntegral_le {β c p A M N b : ℝ} (hβ : 0 < β) (hp : 1 ≤ p)
    (hc : p * β * c < 2) (hA : 0 ≤ A) (hM : 0 ≤ M) (hN : 0 ≤ N) (hb : 0 < b)
    (x : Ω → DataSpace (n + 1)) (hx : Measurable x) (hxM : ∀ ω, mass (etaCoord (x ω)) ≤ M)
    (hmgf : ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * evalF (xiCoord (x ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2))) :
    ∫⁻ ω, ENNReal.ofReal (|A * dataBoxIntegral n h k β N b (x ω)| ^ p) ∂P ≤
      ENNReal.ofReal (M * (A * b ^ (∑ i, h i + (n + 1)) *
        popBoxMass n h k (β * (1 - p * β * c / 2)) (boxScale k b N))) ^ p := by
  set N' : ℝ := boxScale k b N with hN'
  have hN'0 : 0 ≤ N' := by rw [hN']; unfold boxScale; positivity
  set A' : ℝ := A * b ^ (∑ i, h i + (n + 1)) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  set μ : Measure (Fin (n + 1) → ℝ) := volume.restrict (unitBox (n + 1)) with hμ
  set w : (Fin (n + 1) → ℝ) → ℝ := fun u => ∏ i, u i ^ h i with hw
  set r : (Fin (n + 1) → ℝ) → ℝ := fun u => Real.sqrt N' * ∏ i, u i ^ k i with hr
  set ξ : Ω → (Fin (n + 1) → ℝ) → ℝ := fun ω u => evalF (xiCoord (x ω)) (clipCube u) with hξ
  set a : Ω → (Fin (n + 1) → ℝ) → ℝ := fun ω u => evalF (etaCoord (x ω)) u with ha
  have hbox : ∀ u ∈ unitBox (n + 1), u ∈ closedCube (n + 1) := fun u hu =>
    unitBox_subset_closedCube _ hu
  -- the box integral as `∫ w a e^{−βr² + βrξ} dμ` scaled by `b^{|h|+d}`
  have hZ : ∀ ω, A * dataBoxIntegral n h k β N b (x ω) =
      A' * ∫ u, w u * a ω u * Real.exp (-β * r u ^ 2 + β * r u * ξ ω u) ∂μ := by
    intro ω
    rw [dataBoxIntegral_eq n h k β hN hb, hA', mul_assoc, hμ]
    refine congrArg (fun z => A * (b ^ (∑ i, h i + (n + 1)) * z)) ?_
    unfold familyPhaseIntegral
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => ?_
    rw [← hN']
    simp only [hw, ha, hr, hξ, clipCube_eq_self_of_mem hu]
    have hsq : (Real.sqrt N' * ∏ i, u i ^ k i) ^ 2 = N' * ∏ i, u i ^ (2 * k i) := by
      rw [mul_pow, Real.sq_sqrt hN'0, ← Finset.prod_pow]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
    rw [hsq]
    ring_nf
  simp_rw [hZ]
  -- hypotheses of the generic bound
  have hwm : Measurable w := by fun_prop
  have hrm : Measurable r := by fun_prop
  have hw0 : ∀ᵐ u ∂μ, 0 ≤ w u := by
    rw [hμ]
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu => ?_
    exact Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _
  have hr0 : ∀ᵐ u ∂μ, 0 ≤ r u := by
    rw [hμ]
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu => ?_
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
  have haM : ∀ ω, ∀ᵐ u ∂μ, |a ω u| ≤ M := by
    intro ω
    rw [hμ]
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu => ?_
    exact (abs_evalF_le (absSummable_etaCoord (x ω)) (hbox u hu)).trans (hxM ω)
  have hξm : Measurable (Function.uncurry ξ) := measurable_uncurry_xiField hx
  have hmgf' : ∀ᵐ u ∂μ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ξ ω u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) := by
    rw [hμ]
    refine ae_restrict_of_forall_mem (measurableSet_unitBox _) fun u hu t ht => ?_
    change ∫⁻ ω, ENNReal.ofReal (Real.exp (t * evalF (xiCoord (x ω)) (clipCube u))) ∂P ≤ _
    rw [clipCube_eq_self_of_mem hu]
    exact hmgf u hu t ht
  have hint : Integrable (fun u => w u * Real.exp (-(β * (1 - p * β * c / 2)) * r u ^ 2)) μ :=
    integrableOn_popBoxIntegrand n h k _ N'
  have := moment_scaled_integral_le_population_mass P μ hβ hp hc hA'0 hM hwm hrm hw0 haM hr0 ξ hξm
    hmgf' hint
  refine this.trans (le_of_eq ?_)
  rw [hA']
  rfl

/-- **Uniform in `n`**: under a certified deterministic bound on the scaled population mass at the
reduced temperature, `sup_{n ≥ n₀} E|A_n Z_n|^p ≤ (M b^{|h|+d} C_α)^p`. -/
theorem uniform_moment_scaled_dataBoxIntegral {β c p M b : ℝ} (hβ : 0 < β) (hp : 1 ≤ p)
    (hc : p * β * c < 2) (hM : 0 ≤ M) (hb : 0 < b) {A Nn : ℕ → ℝ} (hA : ∀ m, 0 ≤ A m)
    (hNn : ∀ m, 0 ≤ Nn m) (x : ℕ → Ω → DataSpace (n + 1)) (hx : ∀ m, Measurable (x m))
    (hxM : ∀ m ω, mass (etaCoord (x m ω)) ≤ M)
    (hmgf : ∀ m, ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * evalF (xiCoord (x m ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    {n₀ : ℕ} {Cα : ℝ}
    (hpop : ∀ m, n₀ ≤ m →
      A m * popBoxMass n h k (β * (1 - p * β * c / 2)) (boxScale k b (Nn m)) ≤ Cα) :
    ∀ m, n₀ ≤ m → ∫⁻ ω, ENNReal.ofReal (|A m * dataBoxIntegral n h k β (Nn m) b (x m ω)| ^ p) ∂P ≤
      ENNReal.ofReal (M * b ^ (∑ i, h i + (n + 1)) * Cα) ^ p := by
  intro m hm
  refine (moment_scaled_dataBoxIntegral_le P n h k hβ hp hc (hA m) hM (hNn m) hb (x m) (hx m)
    (hxM m) (hmgf m)).trans ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by linarith)
  have hpm := hpop m hm
  have hpos : 0 ≤ popBoxMass n h k (β * (1 - p * β * c / 2)) (boxScale k b (Nn m)) :=
    setIntegral_nonneg (measurableSet_unitBox _) fun u hu =>
      mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
        (Real.exp_pos _).le
  calc M * (A m * b ^ (∑ i, h i + (n + 1)) *
        popBoxMass n h k (β * (1 - p * β * c / 2)) (boxScale k b (Nn m)))
      = M * b ^ (∑ i, h i + (n + 1)) *
        (A m * popBoxMass n h k (β * (1 - p * β * c / 2)) (boxScale k b (Nn m))) := by ring
    _ ≤ M * b ^ (∑ i, h i + (n + 1)) * Cα :=
        mul_le_mul_of_nonneg_left hpm (by positivity)

end Box

end Grammar
