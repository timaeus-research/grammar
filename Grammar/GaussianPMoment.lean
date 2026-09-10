import Grammar.FluctuationSharpBounds
import Grammar.GaussianQuartetDet
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Strict `p`-moment thresholds for the fluctuation function of a Gaussian

For `X ~ N(0,v)` with `v > 0` and `p > 0`, the sharp bounds of `FluctuationSharpBounds.lean`
(`S_λ(a) = e^{βa²/4 + O(log a)}`) and the Gaussian integral `E e^{κX²} < ∞ ⇔ 2κv < 1` give

* **`pβv < 2 ⇒ E[S_λ(X)^p] < ∞`** (`integrable_fluctuation_rpow_gaussianReal`);
* **`pβv > 2 ⇒ E₊[S_λ(X)^p] = ∞`** (`lintegral_fluctuation_rpow_gaussianReal_eq_top`).

The coordinate `g_j` of the Gaussian vector `G = AZ` has law `N(0, (AAᵀ)_{jj})`
(`gaussianVector_map_eval`, via Mathlib's `IsGaussian`), so for the finite mixture
`D(G) = ∑ᵢ ρᵢ S_λ(Gᵢ)` with `ρᵢ > 0`: `E[D(G)^p] < ∞` when `pβ Bᵢᵢ < 2` for every `i`
(`integrable_quartetD_rpow`, Jensen `(∑ρᵢxᵢ)^p ≤ (∑ρ)^{p−1}∑ρᵢxᵢ^p`) and `E₊[D(G)^p] = ∞` as
soon as `pβ Bᵢᵢ > 2` for one `i` (`lintegral_quartetD_rpow_eq_top`) — correlations play no role,
the threshold is `c* = maxᵢ Bᵢᵢ`. The boundary `pβv = 2` is not classified. These thresholds
identify plausible uniform-integrability regimes; they do not by themselves give a uniform
`p`-moment bound for empirical approximants.
-/

open Real MeasureTheory ProbabilityTheory Set

namespace Grammar

/-! ### Gaussian integrals of `e^{κx²}` -/

/-- `E e^{κX²} < ∞` for `X ~ N(0,v)` when `2κv < 1`. -/
theorem integrable_exp_mul_sq_gaussianReal {v : NNReal} (hv : 0 < (v : ℝ)) {κ : ℝ}
    (hκ : 2 * κ * v < 1) :
    Integrable (fun x => Real.exp (κ * x ^ 2)) (gaussianReal 0 v) := by
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  rw [gaussianReal_of_var_ne_zero 0 hv0, integrable_withDensity_iff (measurable_gaussianPDF 0 v)
    (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)]
  have hb : 0 < 1 / (2 * v) - κ := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]
    linarith
  refine ((integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (2 * Real.pi * v))⁻¹).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [toReal_gaussianPDF, gaussianPDFReal_def, sub_zero]
  rw [mul_comm (Real.exp (κ * x ^ 2))]
  simp only [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **A divergent Gaussian integral**: for `2εv > 1`, any real `r`, and `A ≥ 1`,
`∫_{x ≥ A} x^r e^{εx²} dN(0,v) = ∞`. -/
theorem lintegral_indicator_rpow_mul_exp_gaussianReal_eq_top {v : NNReal} (hv : 0 < (v : ℝ))
    {ε : ℝ} (hε : 1 < 2 * ε * v) (r A : ℝ) (hA : 1 ≤ A) :
    ∫⁻ x, ENNReal.ofReal ((Set.Ici A).indicator (fun x => x ^ r * Real.exp (ε * x ^ 2)) x)
      ∂gaussianReal 0 v = ⊤ := by
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  set δ : ℝ := ε - 1 / (2 * v) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos, div_lt_iff₀ (by positivity)]
    linarith
  set c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set k : ℕ := ⌈|r| / 2⌉₊ with hk
  have hrk : 0 ≤ r + 2 * k := by
    have := Nat.le_ceil (|r| / 2)
    have := neg_abs_le r
    rw [← hk] at *
    linarith
  set m : ℝ := c * (δ ^ k / (k.factorial : ℝ)) with hm
  have hm0 : 0 < m := by positivity
  -- pointwise lower bound on `Ici A`
  have hpt : ∀ x ∈ Set.Ici A, ENNReal.ofReal m ≤
      gaussianPDF 0 v x * ENNReal.ofReal ((Set.Ici A).indicator
        (fun x => x ^ r * Real.exp (ε * x ^ 2)) x) := by
    intro x hx
    have hx1 : 1 ≤ x := hA.trans hx
    have hx0 : 0 < x := by linarith
    rw [Set.indicator_of_mem hx, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal_def, sub_zero]
    -- `c e^{-x²/(2v)} x^r e^{εx²} = c x^r e^{δx²} ≥ c x^r (δx²)^k/k! = c δ^k/k! x^{r+2k} ≥ m`
    have hexp : Real.exp (-x ^ 2 / (2 * v)) * Real.exp (ε * x ^ 2) = Real.exp (δ * x ^ 2) := by
      rw [← Real.exp_add, hδ]
      congr 1
      field_simp
      ring
    have hpk : (δ * x ^ 2) ^ k / (k.factorial : ℝ) ≤ Real.exp (δ * x ^ 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) k
    have hxr : 1 ≤ x ^ (r + 2 * k) := Real.one_le_rpow hx1 hrk
    calc m = c * (δ ^ k / (k.factorial : ℝ)) * 1 := by rw [hm, mul_one]
      _ ≤ c * (δ ^ k / (k.factorial : ℝ)) * x ^ (r + 2 * k) :=
          mul_le_mul_of_nonneg_left hxr (by positivity)
      _ = c * (x ^ r * ((δ * x ^ 2) ^ k / (k.factorial : ℝ))) := by
          rw [Real.rpow_add hx0, mul_pow, ← Real.rpow_natCast (x ^ 2) k, ← Real.rpow_natCast x 2,
            ← Real.rpow_mul hx0.le]
          push_cast
          ring
      _ ≤ c * (x ^ r * Real.exp (δ * x ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpk
            (Real.rpow_nonneg hx0.le _)) hc0.le
      _ = c * Real.exp (-x ^ 2 / (2 * v)) * (x ^ r * Real.exp (ε * x ^ 2)) := by
          rw [← hexp]; ring
  rw [gaussianReal_of_var_ne_zero 0 hv0, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF 0 v) (by
      refine ENNReal.measurable_ofReal.comp (Measurable.indicator ?_ measurableSet_Ici)
      fun_prop)]
  refine top_unique ?_
  calc (⊤ : ENNReal) = ∫⁻ x in Set.Ici A, ENNReal.ofReal m := by
        rw [setLIntegral_const, Real.volume_Ici, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.2 hm0).ne'
    _ ≤ ∫⁻ x in Set.Ici A, (gaussianPDF 0 v * fun x => ENNReal.ofReal
          ((Set.Ici A).indicator (fun x => x ^ r * Real.exp (ε * x ^ 2)) x)) x :=
        setLIntegral_mono ((measurable_gaussianPDF 0 v).mul (ENNReal.measurable_ofReal.comp
          (Measurable.indicator (by fun_prop) measurableSet_Ici))) hpt
    _ ≤ ∫⁻ x, (gaussianPDF 0 v * fun x => ENNReal.ofReal
          ((Set.Ici A).indicator (fun x => x ^ r * Real.exp (ε * x ^ 2)) x)) x :=
        setLIntegral_le_lintegral _ _

/-! ### The scalar thresholds -/

theorem fluctuation_rpow_le_eta (β a lam η p : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hη : 0 < η)
    (hη1 : η < 1) (hp : 0 ≤ p) :
    fluctuation β lam a ^ p ≤
      (Real.Gamma lam * (β * η) ^ (-lam)) ^ p * Real.exp (p * β / (4 * (1 - η)) * a ^ 2) := by
  have hS := fluctuation_pos β lam a hβ hlam
  have hC : 0 ≤ Real.Gamma lam * (β * η) ^ (-lam) :=
    mul_nonneg (Real.Gamma_pos_of_pos hlam).le (Real.rpow_nonneg (by positivity) _)
  calc fluctuation β lam a ^ p
      ≤ (Real.Gamma lam * (β * η) ^ (-lam) * Real.exp (β * max a 0 ^ 2 / (4 * (1 - η)))) ^ p :=
        Real.rpow_le_rpow hS.le (fluctuation_le_eta β a lam η hβ hlam hη hη1) hp
    _ = (Real.Gamma lam * (β * η) ^ (-lam)) ^ p *
          Real.exp (p * (β * max a 0 ^ 2 / (4 * (1 - η)))) := by
        rw [Real.mul_rpow hC (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
    _ ≤ (Real.Gamma lam * (β * η) ^ (-lam)) ^ p * Real.exp (p * β / (4 * (1 - η)) * a ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hC _)
        have hmax : max a 0 ^ 2 ≤ a ^ 2 := by
          rcases le_total a 0 with h | h
          · rw [max_eq_right h, zero_pow two_ne_zero]; positivity
          · rw [max_eq_left h]
        have h1η : 0 < 1 - η := by linarith
        calc p * (β * max a 0 ^ 2 / (4 * (1 - η))) = p * β / (4 * (1 - η)) * max a 0 ^ 2 := by ring
          _ ≤ p * β / (4 * (1 - η)) * a ^ 2 :=
              mul_le_mul_of_nonneg_left hmax (div_nonneg (by positivity) (by linarith))

/-- **Finite `p`-moment below threshold**: `pβv < 2 ⇒ E[S_λ(X)^p] < ∞` for `X ~ N(0,v)`. -/
theorem integrable_fluctuation_rpow_gaussianReal (β lam p : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (hp : 0 ≤ p) {v : NNReal} (hv : 0 < (v : ℝ)) (h : p * β * v < 2) :
    Integrable (fun x => fluctuation β lam x ^ p) (gaussianReal 0 v) := by
  set δ : ℝ := 1 - p * β * v / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    have : 0 ≤ p * β * v := by positivity
    linarith
  set η : ℝ := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by rw [hη]; linarith
  set κ : ℝ := p * β / (4 * (1 - η)) with hκ
  have hκv : 2 * κ * v < 1 := by
    rw [hκ, hη]
    have h1 : 0 < 4 * (1 - δ / 2) := by linarith
    rw [show 2 * (p * β / (4 * (1 - δ / 2))) * v = (p * β * v) / (2 * (1 - δ / 2)) by
      field_simp; ring, div_lt_one (by linarith)]
    have : p * β * v = 2 * (1 - δ) := by rw [hδ]; ring
    rw [this]
    linarith
  have hexp := integrable_exp_mul_sq_gaussianReal hv hκv
  have hmeas : Measurable fun x : ℝ => fluctuation β lam x ^ p :=
    ((continuous_fluctuation β lam hβ hlam).rpow_const fun x => Or.inr hp).measurable
  refine (hexp.const_mul ((Real.Gamma lam * (β * η) ^ (-lam)) ^ p)).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (fluctuation_pos β lam x hβ hlam).le _)]
  exact fluctuation_rpow_le_eta β x lam η p hβ hlam hη0 hη1 hp

/-- **Infinite `p`-moment above threshold**: `pβv > 2 ⇒ E₊[S_λ(X)^p] = ∞` for `X ~ N(0,v)`. -/
theorem lintegral_fluctuation_rpow_gaussianReal_eq_top (β lam p : ℝ) (hβ : 0 < β)
    (hlam : 0 < lam) (hp : 0 < p) {v : NNReal} (hv : 0 < (v : ℝ)) (h : 2 < p * β * v) :
    ∫⁻ x, ENNReal.ofReal (fluctuation β lam x ^ p) ∂gaussianReal 0 v = ⊤ := by
  set C : ℝ := Real.exp (-β) * (4 : ℝ) ^ (-(max (lam - 1) 0)) with hC
  have hC0 : 0 < C := by positivity
  have hε : 1 < 2 * (p * β / 4) * v := by
    have : 2 * (p * β / 4) * v = p * β * v / 2 := by ring
    rw [this]; linarith
  have hlow := lintegral_indicator_rpow_mul_exp_gaussianReal_eq_top hv hε (p * (2 * lam - 1)) 2
    (by norm_num)
  have hm : Measurable fun x : ℝ => ENNReal.ofReal ((Set.Ici 2).indicator
      (fun x => x ^ (p * (2 * lam - 1)) * Real.exp (p * β / 4 * x ^ 2)) x) :=
    ENNReal.measurable_ofReal.comp (Measurable.indicator (by fun_prop) measurableSet_Ici)
  refine top_unique ?_
  calc (⊤ : ENNReal) = ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((Set.Ici 2).indicator
        (fun x => x ^ (p * (2 * lam - 1)) * Real.exp (p * β / 4 * x ^ 2)) x) ∂gaussianReal 0 v := by
        rw [hlow, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hC0 p)).ne'
    _ = ∫⁻ x, ENNReal.ofReal (C ^ p * (Set.Ici 2).indicator
        (fun x => x ^ (p * (2 * lam - 1)) * Real.exp (p * β / 4 * x ^ 2)) x) ∂gaussianReal 0 v := by
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]
    _ ≤ ∫⁻ x, ENNReal.ofReal (fluctuation β lam x ^ p) ∂gaussianReal 0 v := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        by_cases hx : x ∈ Set.Ici (2 : ℝ)
        · rw [Set.indicator_of_mem hx]
          have hx2 : (2 : ℝ) ≤ x := hx
          have hx0 : 0 < x := by linarith
          have hle := le_fluctuation_of_two_le β lam hβ hlam hx2
          calc C ^ p * (x ^ (p * (2 * lam - 1)) * Real.exp (p * β / 4 * x ^ 2))
              = (C * x ^ (2 * lam - 1) * Real.exp (β * x ^ 2 / 4)) ^ p := by
                rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
                  Real.mul_rpow hC0.le (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le,
                  ← Real.exp_mul]
                ring_nf
            _ ≤ fluctuation β lam x ^ p := by
                refine Real.rpow_le_rpow (by positivity) ?_ hp.le
                rw [hC]
                linarith [hle]
        · rw [Set.indicator_of_notMem hx, mul_zero]
          exact Real.rpow_nonneg (fluctuation_pos β lam x hβ hlam).le _

/-! ### The marginal law of a coordinate of the Gaussian vector -/

section Marginal

variable {m n : ℕ}

instance isGaussian_stdGaussianPi (k : ℕ) : IsGaussian (stdGaussianPi k) := by
  rw [← isGaussian_map_equiv_iff (EuclideanSpace.equiv (Fin k) ℝ).symm]
  have : (stdGaussianPi k).map ⇑(EuclideanSpace.equiv (Fin k) ℝ).symm =
      stdGaussian (EuclideanSpace ℝ (Fin k)) := map_pi_eq_stdGaussian
  rw [this]
  infer_instance

/-- The coordinate functional `z ↦ (A z)_j` as a continuous linear map. -/
noncomputable def coordFunctional (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj j).comp (Matrix.mulVecLin A))

@[simp] theorem coordFunctional_apply (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m)
    (z : Fin (n + 1) → ℝ) : coordFunctional A j z = A.mulVec z j := rfl

theorem integral_coordFunctional (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m) :
    ∫ z, coordFunctional A j z ∂stdGaussianPi (n + 1) = 0 := by
  have hint : ∀ k : Fin (n + 1),
      Integrable (fun z : Fin (n + 1) → ℝ => A j k * z k) (stdGaussianPi (n + 1)) := fun k =>
    (integrable_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1) (i := k)
      IsGaussian.integrable_id).const_mul (A j k)
  have hz : ∀ k : Fin (n + 1), ∫ z : Fin (n + 1) → ℝ, z k ∂stdGaussianPi (n + 1) = 0 := fun k => by
    rw [stdGaussianPi, integral_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1),
      integral_id_gaussianReal]
  simp only [coordFunctional_apply, Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, hz k, mul_zero]

theorem variance_coordFunctional (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m) :
    Var[coordFunctional A j; stdGaussianPi (n + 1)] =
      (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j := by
  have hfun : (coordFunctional A j : (Fin (n + 1) → ℝ) → ℝ) =
      ∑ k, fun z : Fin (n + 1) → ℝ => A j k * id (z k) := by
    funext z
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  have hv : Var[id; gaussianReal 0 1] = (1 : ℝ) := by
    rw [variance_id_gaussianReal, NNReal.coe_one]
  rw [hfun, stdGaussianPi, variance_sum_pi (fun k => IsGaussian.memLp_two_id.const_mul _)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [variance_const_mul, hv, mul_one, sq]

/-- **The marginal law of a coordinate**: `g_j ~ N(0, (AAᵀ)_{jj})` under `gaussianVector A`. -/
theorem gaussianVector_map_eval (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m) :
    (gaussianVector A).map (fun g => g j) =
      gaussianReal 0 ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j).toNNReal := by
  have h1 : (gaussianVector A).map (fun g => g j) =
      (stdGaussianPi (n + 1)).map (coordFunctional A j) := by
    rw [gaussianVector, Measure.map_map (measurable_pi_apply j) (measurable_mulVec A)]
    rfl
  rw [h1, IsGaussian.eq_gaussianReal ((stdGaussianPi (n + 1)).map (coordFunctional A j))
    inferInstance, integral_map (coordFunctional A j).continuous.aemeasurable
    aestronglyMeasurable_id, variance_map aemeasurable_id
    (coordFunctional A j).continuous.aemeasurable, Function.id_comp]
  simp only [id_eq]
  rw [integral_coordFunctional, variance_coordFunctional]

/-! ### The finite mixture -/

variable {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
include hβ hlam hρ

/-- Jensen: `D(g)^p ≤ (∑ρ)^{p−1} ∑ᵢ ρᵢ S_λ(gᵢ)^p` for `p ≥ 1`. -/
theorem quartetD_rpow_le {p : ℝ} (hp : 1 ≤ p) (g : Fin m → ℝ) :
    quartetD β lam ρ g ^ p ≤
      (∑ i, ρ i) ^ (p - 1) * ∑ i, ρ i * fluctuation β lam (g i) ^ p := by
  have hsum : 0 < ∑ i, ρ i := Finset.sum_pos (fun i _ => hρ i) Finset.univ_nonempty
  have hw1 : ∑ i, ρ i / ∑ i, ρ i = 1 := by rw [← Finset.sum_div, div_self hsum.ne']
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun i => ρ i / ∑ i, ρ i)
    (fun i => fluctuation β lam (g i)) (fun i _ => div_nonneg (hρ i).le hsum.le) hw1
    (fun i _ => (fluctuation_pos β lam _ hβ hlam).le) hp
  have hD : quartetD β lam ρ g = (∑ i, ρ i) * ∑ i, ρ i / (∑ i, ρ i) * fluctuation β lam (g i) := by
    unfold quartetD
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hD, Real.mul_rpow hsum.le (Finset.sum_nonneg fun i _ =>
    mul_nonneg (div_nonneg (hρ i).le hsum.le) (fluctuation_pos β lam _ hβ hlam).le)]
  calc (∑ i, ρ i) ^ p * (∑ i, ρ i / (∑ i, ρ i) * fluctuation β lam (g i)) ^ p
      ≤ (∑ i, ρ i) ^ p * ∑ i, ρ i / (∑ i, ρ i) * fluctuation β lam (g i) ^ p :=
        mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hsum.le _)
    _ = (∑ i, ρ i) ^ (p - 1) * ∑ i, ρ i * fluctuation β lam (g i) ^ p := by
        have hp' : (∑ i, ρ i) ^ p = (∑ i, ρ i) ^ (p - 1) * (∑ i, ρ i) := by
          rw [← Real.rpow_add_one hsum.ne']
          congr 1
          ring
        rw [hp', mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp

omit hρ [Nonempty (Fin m)] in
theorem integrable_fluctuation_rpow_coord {p : ℝ} (hp : 0 ≤ p) (i : Fin m)
    (hi : 0 < (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i)
    (h : p * β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i < 2) :
    Integrable (fun g : Fin m → ℝ => fluctuation β lam (g i) ^ p) (gaussianVector A) := by
  have hmeas : Measurable fun x : ℝ => fluctuation β lam x ^ p :=
    ((continuous_fluctuation β lam hβ hlam).rpow_const fun x => Or.inr hp).measurable
  have := integrable_fluctuation_rpow_gaussianReal β lam p hβ hlam hp
    (v := ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i).toNNReal)
    (by rw [Real.coe_toNNReal _ hi.le]; exact hi) (by rw [Real.coe_toNNReal _ hi.le]; exact h)
  rw [← gaussianVector_map_eval A i] at this
  exact (integrable_map_measure hmeas.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1
    this

/-- **Finite `p`-moment of the mixture below threshold**: if `pβBᵢᵢ < 2` for every `i`, then
`E[D(G)^p] < ∞`. -/
theorem integrable_quartetD_rpow {p : ℝ} (hp : 1 ≤ p)
    (hpos : ∀ i, 0 < (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i)
    (h : ∀ i, p * β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i < 2) :
    Integrable (fun g => quartetD β lam ρ g ^ p) (gaussianVector A) := by
  have hint : Integrable (fun g : Fin m → ℝ =>
      (∑ i, ρ i) ^ (p - 1) * ∑ i, ρ i * fluctuation β lam (g i) ^ p) (gaussianVector A) :=
    (integrable_finsetSum _ fun i _ =>
      (integrable_fluctuation_rpow_coord hβ hlam A (by linarith) i (hpos i) (h i)).const_mul
        (ρ i)).const_mul _
  refine hint.mono' ((continuous_quartetD hβ hlam).rpow_const
    (fun g => Or.inr (by linarith))).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (quartetD_pos hβ hlam hρ g).le _)]
  exact quartetD_rpow_le hβ hlam hρ hp g

omit [Nonempty (Fin m)] in
/-- **Infinite `p`-moment of the mixture above threshold**: if `pβBᵢᵢ > 2` for one `i`, then
`E₊[D(G)^p] = ∞`, whatever the correlations. -/
theorem lintegral_quartetD_rpow_eq_top {p : ℝ} (hp : 0 < p) (i : Fin m)
    (hi : 2 < p * β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i) :
    ∫⁻ g, ENNReal.ofReal (quartetD β lam ρ g ^ p) ∂gaussianVector A = ⊤ := by
  have hBpos : 0 < (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i := by
    by_contra hneg
    have hneg' : (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i ≤ 0 := le_of_not_gt hneg
    have : p * β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg'
    linarith
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (fluctuation β lam x ^ p) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_fluctuation β lam hβ hlam).rpow_const fun x => Or.inr hp.le).measurable
  have htop := lintegral_fluctuation_rpow_gaussianReal_eq_top β lam p hβ hlam hp
    (v := ((A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i).toNNReal)
    (by rw [Real.coe_toNNReal _ hBpos.le]; exact hBpos)
    (by rw [Real.coe_toNNReal _ hBpos.le]; exact hi)
  rw [← gaussianVector_map_eval A i, lintegral_map hmeas (measurable_pi_apply i)] at htop
  have hm2 : Measurable fun g : Fin m → ℝ => ENNReal.ofReal (fluctuation β lam (g i) ^ p) :=
    hmeas.comp (measurable_pi_apply i)
  refine top_unique ?_
  calc (⊤ : ENNReal) = ENNReal.ofReal (ρ i ^ p) *
        ∫⁻ g, ENNReal.ofReal (fluctuation β lam (g i) ^ p) ∂gaussianVector A := by
        rw [htop, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (hρ i) p)).ne'
    _ = ∫⁻ g, ENNReal.ofReal ((ρ i * fluctuation β lam (g i)) ^ p) ∂gaussianVector A := by
        rw [← lintegral_const_mul _ hm2]
        refine lintegral_congr fun g => ?_
        rw [Real.mul_rpow (hρ i).le (fluctuation_pos β lam _ hβ hlam).le,
          ENNReal.ofReal_mul (Real.rpow_nonneg (hρ i).le _)]
    _ ≤ ∫⁻ g, ENNReal.ofReal (quartetD β lam ρ g ^ p) ∂gaussianVector A :=
        lintegral_mono fun g => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (mul_pos (hρ i) (fluctuation_pos β lam _ hβ hlam)).le
          (single_le_quartetD hβ hlam hρ i g) hp.le)

end Marginal

end Grammar
