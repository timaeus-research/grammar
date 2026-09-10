import Grammar.CovarianceInterpolation

/-!
# The Gaussian quartet with a general covariance diagonal

`GaussianQuartet.lean` and `CovarianceInterpolation.lean` assume the covariance `b = A Aᵀ` has a
constant diagonal `b_{ii} = c`, so that the connected two-point function is `V = c M₂ − Q`. For a
covariance kernel on a compact base the diagonal `C(x,x)` is not constant, and the correct object
is

`Vgen(g) = ∑ᵢ bᵢᵢ Rᵢ(g) − Q(g) = quartetDiag − quartetQ`.

This file re-derives the finite-resolution theory for `Vgen`: `Q ≤ ∑ᵢ bᵢᵢ Rᵢ`
(`quartetQ_le_quartetDiag`, Cauchy–Schwarz column by column), `0 ≤ Vgen ≤ Diag`
(`quartetVgen_nonneg`), Gaussian integration by parts **`E H(G) = β E Vgen(G)`**
(`integral_quartetH_eq_gen`), the scaled identity `E H(√s G) = β s E Vgen(√s G)`
(`integral_quartetH_scaled_gen`), the derivative `L'(s) = (β²/2) E Vgen(√s G)` of
`L(s) = E log D(√s G)` (`hasDerivAt_interpL_gen`), the **covariance interpolation identity**
`E log D(G) = log D(0) + (β²/2)∫₀¹ E Vgen(√s G) ds` (`integral_log_quartetD_eq_gen`) and
`E log D(G) ≥ log D(0)` (`log_quartetD_zero_le_integral_gen`), all without any diagonal
hypothesis. With a constant diagonal `Vgen = V` (`quartetVgen_eq_quartetV`).
-/

open Real MeasureTheory Set

namespace Grammar

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ)

/-- The diagonal term `∑ᵢ bᵢᵢ Rᵢ(g)`. -/
noncomputable def quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, b i i * quartetR β lam ρ i g

/-- The connected two-point function with a general diagonal: `Vgen = ∑ᵢ bᵢᵢ Rᵢ − Q`. -/
noncomputable def quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  quartetDiag β lam ρ b g - quartetQ β lam ρ b g

theorem quartetDiag_eq_of_const {b : Matrix (Fin m) (Fin m) ℝ} {c : ℝ} (hc : ∀ i, b i i = c)
    (g : Fin m → ℝ) : quartetDiag β lam ρ b g = c * quartetM2 β lam ρ g := by
  unfold quartetDiag quartetM2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem quartetVgen_eq_quartetV {b : Matrix (Fin m) (Fin m) ℝ} {c : ℝ} (hc : ∀ i, b i i = c)
    (g : Fin m → ℝ) : quartetVgen β lam ρ b g = quartetV β lam ρ b c g := by
  unfold quartetVgen quartetV
  rw [quartetDiag_eq_of_const β lam ρ hc]

theorem quartetDiag_smul (b : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (g : Fin m → ℝ) :
    quartetDiag β lam ρ (s • b) g = s * quartetDiag β lam ρ b g := by
  simp only [quartetDiag, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem quartetVgen_smul (b : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (g : Fin m → ℝ) :
    quartetVgen β lam ρ (s • b) g = s * quartetVgen β lam ρ b g := by
  unfold quartetVgen
  rw [quartetDiag_smul, quartetQ_smul]
  ring

variable {β lam ρ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

/-- **`Q ≤ ∑ᵢ bᵢᵢ Rᵢ`** for `b = A Aᵀ` (Cauchy–Schwarz column by column). -/
theorem quartetQ_le_quartetDiag {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
    quartetQ β lam ρ (A * A.transpose) g ≤ quartetDiag β lam ρ (A * A.transpose) g := by
  rw [quartetQ_eq_sum_sq]
  calc ∑ k, (∑ i, A i k * quartetW β lam ρ i g) ^ 2
      ≤ ∑ k, ∑ i, A i k ^ 2 * quartetR β lam ρ i g :=
        Finset.sum_le_sum fun k _ => sq_sum_mul_quartetW_le hβ hlam hρ A k g
    _ = ∑ i, (∑ k, A i k ^ 2) * quartetR β lam ρ i g := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ = quartetDiag β lam ρ (A * A.transpose) g := by
        unfold quartetDiag
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.mul_apply, Matrix.transpose_apply, ← sq]

theorem quartetDiag_nonneg (b : Matrix (Fin m) (Fin m) ℝ) (hb : ∀ i, 0 ≤ b i i)
    (g : Fin m → ℝ) : 0 ≤ quartetDiag β lam ρ b g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (quartetR_nonneg hβ hlam hρ i g)

/-- **`0 ≤ Vgen ≤ Diag`** for `b = A Aᵀ`. -/
theorem quartetVgen_nonneg {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : Fin m → ℝ) :
    0 ≤ quartetVgen β lam ρ (A * A.transpose) g ∧
      quartetVgen β lam ρ (A * A.transpose) g ≤ quartetDiag β lam ρ (A * A.transpose) g := by
  unfold quartetVgen
  constructor
  · linarith [quartetQ_le_quartetDiag hβ hlam hρ A g]
  · linarith [quartetQ_nonneg (β := β) (lam := lam) (ρ := ρ) A g]

theorem continuous_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (quartetDiag β lam ρ b) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_quartetR hβ hlam hρ i)

theorem continuous_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (quartetVgen β lam ρ b) :=
  (continuous_quartetDiag hβ hlam hρ b).sub (by
    unfold quartetQ
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
        (continuous_quartetW hβ hlam hρ j))

theorem polyBoundedPi_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
    PolyBoundedPi (quartetDiag β lam ρ b) :=
  PolyBoundedPi.finset_sum _ fun i =>
    (PolyBoundedPi.const (b i i)).mul (polyBoundedPi_quartetR hβ hlam hρ i)

theorem polyBoundedPi_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
    PolyBoundedPi (quartetVgen β lam ρ b) :=
  (polyBoundedPi_quartetDiag hβ hlam hρ b).sub (polyBoundedPi_quartetQ hβ hlam hρ b)

end Det

section Quartet

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
include hβ hlam hρ

theorem integrable_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetDiag β lam ρ b) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ => (integrable_quartetR hβ hlam hρ A i).const_mul (b i i)

theorem integrable_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetVgen β lam ρ b) (gaussianVector A) :=
  (integrable_quartetDiag hβ hlam hρ A b).sub (integrable_quartetQ hβ hlam hρ A b)

/-- **Gaussian integration by parts, general diagonal**: `E[H(G)] = β E[Vgen(G)]`. -/
theorem integral_quartetH_eq_gen :
    ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      β * ∫ g, quartetVgen β lam ρ (A * A.transpose) g ∂gaussianVector A := by
  set b : Matrix (Fin m) (Fin m) ℝ := A * A.transpose with hb
  have hH : ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A := by
    unfold quartetH
    rw [integral_finsetSum _ fun i _ => integrable_coord_mul_quartetW hβ hlam hρ A i]
    exact Finset.sum_congr rfl fun i _ => integral_coord_mul_quartetW hβ hlam hρ A i
  have hW' : ∀ i j, ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A =
      β * (if i = j then ∫ g, quartetR β lam ρ i g ∂gaussianVector A else 0) -
        β * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    intro i j
    unfold quartetW'
    have h1 : Integrable (fun g => β * (if i = j then quartetR β lam ρ i g else 0))
        (gaussianVector A) := by
      by_cases h : i = j
      · simp only [h, if_true]; exact (integrable_quartetR hβ hlam hρ A j).const_mul β
      · simp only [h, if_false, mul_zero]; exact integrable_const 0
    have h2 : Integrable (fun g => β * quartetW β lam ρ i g * quartetW β lam ρ j g)
        (gaussianVector A) := by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul β
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring
    rw [integral_sub h1 h2]
    congr 1
    · by_cases h : i = j
      · simp only [h, if_true, integral_const_mul]
      · simp only [h, if_false, mul_zero, integral_zero]
    · rw [← integral_const_mul]
      congr 1; funext g; ring
  rw [hH]
  simp_rw [hW']
  have hQ : ∫ g, quartetQ β lam ρ b g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    unfold quartetQ
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g => ?_); ring]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1; funext g; ring
  have hM : ∫ g, quartetDiag β lam ρ b g ∂gaussianVector A =
      ∑ i, b i i * ∫ g, quartetR β lam ρ i g ∂gaussianVector A := by
    unfold quartetDiag
    rw [integral_finsetSum _ fun i _ => (integrable_quartetR hβ hlam hρ A i).const_mul (b i i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  unfold quartetVgen
  rw [integral_sub (integrable_quartetDiag hβ hlam hρ A b) (integrable_quartetQ hβ hlam hρ A b),
    hQ, hM, mul_sub, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **Scaled integration by parts**: `E H(√s G) = β s E Vgen(√s G)`, `Vgen` with the original
covariance. -/
theorem integral_quartetH_scaled_gen {s : ℝ} (hs : 0 ≤ s) :
    ∫ g, quartetH β lam ρ g ∂gaussianVector (Real.sqrt s • A) =
      β * s * ∫ g, quartetVgen β lam ρ (A * A.transpose) g ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_quartetH_eq_gen hβ hlam hρ (Real.sqrt s • A)]
  simp_rw [scaled_cov A hs, quartetVgen_smul]
  rw [integral_const_mul]
  ring

end Quartet

section Interp

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}

/-- `E[Vgen(√s G)]`, `Vgen` with the original covariance `A Aᵀ`. -/
noncomputable def interpVgen (β lam : ℝ) (ρ : Fin m → ℝ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (s : ℝ) : ℝ :=
  ∫ z, quartetVgen β lam ρ (A * A.transpose) (Real.sqrt s • A.mulVec z) ∂stdGaussianPi (n + 1)

variable (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)]
include hβ hlam hρ

theorem interpVgen_eq (s : ℝ) :
    interpVgen β lam ρ A s =
      ∫ g, quartetVgen β lam ρ (A * A.transpose) g ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_gaussianVector _ _ (continuous_quartetVgen hβ hlam hρ _).measurable]
  simp_rw [Matrix.smul_mulVec]
  rfl

/-- **`L'(s) = (β²/2) E[Vgen(√s G)]` on `(0,1)`**, no diagonal hypothesis. -/
theorem hasDerivAt_interpL_gen {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (interpL β lam ρ A) (β ^ 2 / 2 * interpVgen β lam ρ A s₀) s₀ := by
  obtain ⟨hs₀0, hs₀1⟩ := hs₀
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_quartetH hβ hlam hρ).smul_bound
  have hnhds : Ioo (s₀ / 2) 2 ∈ nhds s₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_int : Integrable (fun z : Fin (n + 1) → ℝ =>
      Real.log (quartetD β lam ρ (Real.sqrt s₀ • A.mulVec z))) (stdGaussianPi (n + 1)) := by
    obtain ⟨C', k', hC'⟩ := (polyBoundedPi_log_quartetD hβ hlam hρ).smul_bound
    exact integrable_of_polyBoundedPi (measurable_log_quartetD_sqrt A hβ hlam s₀)
      (polyBoundedPi_comp_mulVec A
        (F := fun g : Fin m → ℝ => Real.log (quartetD β lam ρ (Real.sqrt s₀ • g)))
        ⟨C', k', fun g => hC' _ (sqrt_abs_le_two (by linarith)) g⟩)
  have hHm : ∀ s : ℝ, Measurable fun z : Fin (n + 1) → ℝ =>
      quartetH β lam ρ (Real.sqrt s • A.mulVec z) := fun s =>
    ((continuous_quartetH hβ hlam hρ).comp
      ((continuous_const (y := Real.sqrt s)).smul (continuous_mulVec A))).measurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s (z : Fin (n + 1) → ℝ) => Real.log (quartetD β lam ρ (Real.sqrt s • A.mulVec z)))
    (F' := fun s (z : Fin (n + 1) → ℝ) =>
      β / (2 * s) * quartetH β lam ρ (Real.sqrt s • A.mulVec z))
    (bound := fun z => β / s₀ * (C * (1 + ‖A.mulVec z‖) ^ k)) hnhds
    (Filter.Eventually.of_forall fun s =>
      (measurable_log_quartetD_sqrt A hβ hlam s).aestronglyMeasurable)
    hF_int (measurable_const.mul (hHm s₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z s hs => ?_) (integrable_polyBound A C k _)
    (Filter.Eventually.of_forall fun z s hs =>
      hasDerivAt_log_quartetD_sqrt_smul hβ hlam hρ (A.mulVec z) (by linarith [hs.1]))
  · refine key.2.congr_deriv ?_
    have hHint : ∫ z, quartetH β lam ρ (Real.sqrt s₀ • A.mulVec z) ∂stdGaussianPi (n + 1) =
        ∫ g, quartetH β lam ρ g ∂gaussianVector (Real.sqrt s₀ • A) := by
      rw [integral_gaussianVector _ _ (continuous_quartetH hβ hlam hρ).measurable]
      simp_rw [Matrix.smul_mulVec]
    rw [integral_const_mul, hHint, integral_quartetH_scaled_gen hβ hlam hρ A hs₀0.le,
      ← interpVgen_eq A hβ hlam hρ s₀]
    field_simp
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hβ (by linarith [hs.1] : 0 < 2 * s))]
    have h1 : β / (2 * s) ≤ β / s₀ :=
      div_le_div_of_nonneg_left hβ.le hs₀0 (by linarith [hs.1])
    exact mul_le_mul h1 (hCk _ (sqrt_abs_le_two hs.2.le) _) (abs_nonneg _) (div_pos hβ hs₀0).le

theorem continuousOn_interpVgen : ContinuousOn (interpVgen β lam ρ A) (Icc 0 1) := by
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_quartetVgen hβ hlam hρ (A * A.transpose)).smul_bound
  refine continuousOn_of_dominated
    (F := fun s (z : Fin (n + 1) → ℝ) =>
      quartetVgen β lam ρ (A * A.transpose) (Real.sqrt s • A.mulVec z))
    (bound := fun z => 1 * (C * (1 + ‖A.mulVec z‖) ^ k))
    (fun s _ => ((continuous_quartetVgen hβ hlam hρ _).comp
      ((continuous_const (y := Real.sqrt s)).smul
        (continuous_mulVec A))).measurable.aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_polyBound A C k 1)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, one_mul]
    exact hCk _ (sqrt_abs_le_two (by linarith [hs.2])) _
  · exact ((continuous_quartetVgen hβ hlam hρ _).comp
      (Real.continuous_sqrt.smul continuous_const)).continuousOn

theorem interpVgen_nonneg (s : ℝ) : 0 ≤ interpVgen β lam ρ A s :=
  integral_nonneg fun _ => (quartetVgen_nonneg hβ hlam hρ A _).1

/-- **Covariance interpolation, general diagonal**:
`E log D(G) = log(β^{−λ} Γ(λ) ∑ᵢ ρᵢ) + (β²/2) ∫₀¹ E[Vgen(√s G)] ds`. -/
theorem integral_log_quartetD_eq_gen :
    ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector A =
      Real.log (β ^ (-lam) * Real.Gamma lam * ∑ i, ρ i) +
        ∫ s in (0 : ℝ)..1, β ^ 2 / 2 * interpVgen β lam ρ A s := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_interpL A hβ hlam hρ) (fun s hs => hasDerivAt_interpL_gen A hβ hlam hρ hs) ?_
  · rw [hFTC, interpL_one A hβ hlam, interpL_zero A hβ hlam]
    ring
  · have h := (continuousOn_const (c := β ^ 2 / 2)).mul (continuousOn_interpVgen A hβ hlam hρ)
    rw [← Set.uIcc_of_le (zero_le_one' ℝ)] at h
    exact h.intervalIntegrable

/-- **`E log D(G) ≥ log D(0)`** for every centred Gaussian vector. -/
theorem log_quartetD_zero_le_integral_gen :
    Real.log (β ^ (-lam) * Real.Gamma lam * ∑ i, ρ i) ≤
      ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector A := by
  rw [integral_log_quartetD_eq_gen A hβ hlam hρ]
  have : 0 ≤ ∫ s in (0 : ℝ)..1, β ^ 2 / 2 * interpVgen β lam ρ A s :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ =>
      mul_nonneg (by positivity) (interpVgen_nonneg A hβ hlam hρ s)
  linarith

end Interp

end Grammar
