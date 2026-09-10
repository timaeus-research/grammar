import Grammar.GaussianQuartet
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Covariance interpolation for the expected log-evidence

For the finite-resolution quartet with Gaussian vector `G = AZ` of constant covariance diagonal
`c`, let `L(s) = E log D(√s G)` and let `V_s(g) = V(√s g)` be the connected two-point function at
`√s g` with the original covariance `b = AAᵀ`. Then

* `L` is continuous on `[0,1]` (`continuousOn_interpL`);
* `L` is differentiable on `(0,1)` with `L'(s) = (β²/2) E[V_s(G)] ≥ 0` (`hasDerivAt_interpL`,
  `interpV_nonneg`);
* hence **`E log D(G) = log(β^{−λ} Γ(λ) ∑ᵢ ρᵢ) + (β²/2) ∫₀¹ E[V_s(G)] ds`**
  (`integral_log_quartetD_eq`) and **`E log D(G) ≥ log D(0)`** (`log_quartetD_zero_le_integral`).

The route: `√s G` is the Gaussian vector with matrix `√s A`, whose covariance is `s b`; the
pathwise derivative `∂_s log D(√s g) = (β/2s) H(√s g)` is dominated on `(s₀/2, 2)` by a
polynomial in `‖A z‖`, so differentiation under the integral is legitimate for `s₀ > 0`; Gaussian
integration by parts at scale `√s` (`integral_quartetH_scaled`) turns `E H(√s G)` into
`β s E V(√s G)`; and the quadratic bound on `|log D|` gives the domination needed for continuity
down to `s = 0`. Pathwise differentiability at `s = 0` is never asserted. Exact for every `β > 0`.
-/

open MeasureTheory Set

namespace Grammar

/-! ### Closure lemmas for polynomial bounds -/

namespace PolyBoundedPi

variable {m : ℕ}

theorem of_abs_le {F G : (Fin m → ℝ) → ℝ} (hG : PolyBoundedPi G) (h : ∀ g, |F g| ≤ G g) :
    PolyBoundedPi F := by
  obtain ⟨C, k, hC⟩ := hG
  exact ⟨C, k, fun g => (h g).trans ((le_abs_self _).trans (hC g))⟩

theorem abs {F : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) : PolyBoundedPi fun g => |F g| := by
  obtain ⟨C, k, hC⟩ := hF
  exact ⟨C, k, fun g => by rw [abs_abs]; exact hC g⟩

/-- Scaling the argument by `t` with `|t| ≤ 2` keeps a polynomial bound, uniformly in `t`. -/
theorem smul_bound {F : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) :
    ∃ (C : ℝ) (k : ℕ), ∀ t : ℝ, |t| ≤ 2 → ∀ g, |F (t • g)| ≤ C * (1 + ‖g‖) ^ k := by
  obtain ⟨C, k, hC⟩ := hF
  refine ⟨C * 2 ^ k, k, fun t ht g => ?_⟩
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h0
    exact (abs_nonneg _).trans h0
  calc |F (t • g)| ≤ C * (1 + ‖t • g‖) ^ k := hC _
    _ ≤ C * (2 * (1 + ‖g‖)) ^ k := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs]
        nlinarith [norm_nonneg g, abs_nonneg t]
    _ = C * 2 ^ k * (1 + ‖g‖) ^ k := by rw [mul_pow]; ring

end PolyBoundedPi

theorem sqrt_abs_le_two {s : ℝ} (hs : s ≤ 2) : |Real.sqrt s| ≤ 2 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}

/-! ### Polynomial bounds for `log D`, `H`, `V` -/

/-- `|log S_λ(a)| ≤ K + (β/2) a² + 2λ|a|`. -/
theorem abs_log_fluctuation_le' (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    |Real.log (fluctuation β lam a)| ≤
      (|Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)| + 2 * β + |Real.log lam|) +
        β / 2 * (a * a) + 2 * lam * |a| := by
  have h := abs_log_fluctuation_le hβ hlam a
  have hlog : Real.log (1 + |a|) ≤ |a| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |a|)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * lam)]

theorem polyBoundedPi_log_fluctuation_coord (hβ : 0 < β) (hlam : 0 < lam) (i : Fin m) :
    PolyBoundedPi fun g : Fin m → ℝ => Real.log (fluctuation β lam (g i)) :=
  PolyBoundedPi.of_abs_le
    (G := fun g => (|Real.log ((β / 2) ^ (-lam) * Real.Gamma lam)| + 2 * β + |Real.log lam|) +
        β / 2 * (g i * g i) + 2 * lam * |g i|)
    (((PolyBoundedPi.const _).add
      (((PolyBoundedPi.coord i).mul (PolyBoundedPi.coord i)).const_mul _)).add
        ((PolyBoundedPi.coord i).abs.const_mul _))
    fun g => abs_log_fluctuation_le' hβ hlam (g i)

/-- `|log D(g)| ≤ |log ∑ρ| + |log ρ_j| + ∑_i |log S_λ(g_i)|` for any fixed index `j`. -/
theorem abs_log_quartetD_le (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (g : Fin m → ℝ) :
    |Real.log (quartetD β lam ρ g)| ≤
      |Real.log (∑ i, ρ i)| + |Real.log (ρ (Classical.arbitrary (Fin m)))| +
        ∑ i, |Real.log (fluctuation β lam (g i))| := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j = Classical.arbitrary (Fin m) := ⟨_, rfl⟩
  rw [← hj]
  have hD := quartetD_pos hβ hlam hρ g
  have hsum : 0 < ∑ i, ρ i := Finset.sum_pos (fun i _ => hρ i) Finset.univ_nonempty
  have hup : Real.log (quartetD β lam ρ g) ≤
      Real.log (∑ i, ρ i) + ∑ i, |Real.log (fluctuation β lam (g i))| := by
    have h1 : quartetD β lam ρ g ≤
        (∑ i, ρ i) * Real.exp (∑ i, |Real.log (fluctuation β lam (g i))|) := by
      unfold quartetD
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hρ i).le
      rw [← Real.exp_log (fluctuation_pos β lam (g i) hβ hlam)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun k => |Real.log (fluctuation β lam (g k))|)
          (fun k _ => abs_nonneg _) (Finset.mem_univ i)))
    calc Real.log (quartetD β lam ρ g)
        ≤ Real.log ((∑ i, ρ i) * Real.exp (∑ i, |Real.log (fluctuation β lam (g i))|)) :=
          Real.log_le_log hD h1
      _ = Real.log (∑ i, ρ i) + ∑ i, |Real.log (fluctuation β lam (g i))| := by
          rw [Real.log_mul hsum.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlow : Real.log (ρ j) - ∑ i, |Real.log (fluctuation β lam (g i))| ≤
      Real.log (quartetD β lam ρ g) := by
    have h1 : ρ j * fluctuation β lam (g j) ≤ quartetD β lam ρ g := by
      unfold quartetD
      exact Finset.single_le_sum
        (fun i _ => (mul_pos (hρ i) (fluctuation_pos β lam (g i) hβ hlam)).le) (Finset.mem_univ j)
    have h2 : |Real.log (fluctuation β lam (g j))| ≤
        ∑ i, |Real.log (fluctuation β lam (g i))| :=
      Finset.single_le_sum (f := fun k => |Real.log (fluctuation β lam (g k))|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    calc Real.log (ρ j) - ∑ i, |Real.log (fluctuation β lam (g i))|
        ≤ Real.log (ρ j) + Real.log (fluctuation β lam (g j)) := by
          linarith [neg_abs_le (Real.log (fluctuation β lam (g j)))]
      _ = Real.log (ρ j * fluctuation β lam (g j)) :=
          (Real.log_mul (hρ j).ne' (fluctuation_pos β lam (g j) hβ hlam).ne').symm
      _ ≤ Real.log (quartetD β lam ρ g) :=
          Real.log_le_log (mul_pos (hρ j) (fluctuation_pos β lam (g j) hβ hlam)) h1
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (ρ j)), abs_nonneg (Real.log (∑ i, ρ i))]
  · linarith [le_abs_self (Real.log (∑ i, ρ i)), abs_nonneg (Real.log (ρ j))]

theorem polyBoundedPi_log_quartetD (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] : PolyBoundedPi fun g => Real.log (quartetD β lam ρ g) :=
  PolyBoundedPi.of_abs_le
    (G := fun g => |Real.log (∑ i, ρ i)| + |Real.log (ρ (Classical.arbitrary (Fin m)))| +
      ∑ i, |Real.log (fluctuation β lam (g i))|)
    ((PolyBoundedPi.const _).add (PolyBoundedPi.finset_sum _ fun i =>
      (polyBoundedPi_log_fluctuation_coord hβ hlam i).abs))
    (abs_log_quartetD_le hβ hlam hρ)

theorem polyBoundedPi_quartetH (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] : PolyBoundedPi (quartetH β lam ρ) :=
  PolyBoundedPi.finset_sum _ fun i =>
    (PolyBoundedPi.coord i).mul (polyBoundedPi_quartetW hβ hlam hρ i)

theorem polyBoundedPi_quartetQ (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (b : Matrix (Fin m) (Fin m) ℝ) : PolyBoundedPi (quartetQ β lam ρ b) :=
  PolyBoundedPi.finset_sum _ fun i => PolyBoundedPi.finset_sum _ fun j =>
    ((PolyBoundedPi.const (b i j)).mul (polyBoundedPi_quartetW hβ hlam hρ i)).mul
      (polyBoundedPi_quartetW hβ hlam hρ j)

theorem polyBoundedPi_quartetV (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (b : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    PolyBoundedPi (quartetV β lam ρ b c) :=
  ((polyBoundedPi_quartetM2 hβ hlam hρ).const_mul c).sub (polyBoundedPi_quartetQ hβ hlam hρ b)

theorem continuous_quartetH (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] : Continuous (quartetH β lam ρ) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_quartetW hβ hlam hρ i)

theorem continuous_quartetV (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (b : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    Continuous (quartetV β lam ρ b c) := by
  unfold quartetV quartetM2 quartetQ
  refine (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_quartetR hβ hlam hρ i)).sub (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
    (continuous_quartetW hβ hlam hρ j)

/-! ### The interpolation functions -/

section Defs

variable (β lam : ℝ) (ρ : Fin m → ℝ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- `L(s) = E log D(√s G)`. -/
noncomputable def interpL (s : ℝ) : ℝ :=
  ∫ z, Real.log (quartetD β lam ρ (Real.sqrt s • A.mulVec z)) ∂stdGaussianPi (n + 1)

/-- `E[V_s(G)]`: the connected two-point function at `√s G` with the original covariance. -/
noncomputable def interpV (c : ℝ) (s : ℝ) : ℝ :=
  ∫ z, quartetV β lam ρ (A * A.transpose) c (Real.sqrt s • A.mulVec z) ∂stdGaussianPi (n + 1)

end Defs

variable (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

theorem continuous_mulVec : Continuous A.mulVec :=
  (Matrix.mulVecLin A).continuous_of_finiteDimensional

theorem measurable_log_quartetD (hβ : 0 < β) (hlam : 0 < lam) :
    Measurable fun g : Fin m → ℝ => Real.log (quartetD β lam ρ g) :=
  Real.measurable_log.comp (continuous_quartetD hβ hlam).measurable

/-- `L(s)` is the expectation of `log D` under the Gaussian vector with matrix `√s A`. -/
theorem interpL_eq (hβ : 0 < β) (hlam : 0 < lam) (s : ℝ) :
    interpL β lam ρ A s =
      ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_gaussianVector _ _ (measurable_log_quartetD hβ hlam)]
  simp_rw [Matrix.smul_mulVec]
  rfl

theorem interpV_eq (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
    (c s : ℝ) :
    interpV β lam ρ A c s =
      ∫ g, quartetV β lam ρ (A * A.transpose) c g ∂gaussianVector (Real.sqrt s • A) := by
  rw [integral_gaussianVector _ _ (continuous_quartetV hβ hlam hρ _ c).measurable]
  simp_rw [Matrix.smul_mulVec]
  rfl

/-- The covariance of `√s A` is `s AAᵀ`. -/
theorem scaled_cov {s : ℝ} (hs : 0 ≤ s) :
    (Real.sqrt s • A) * (Real.sqrt s • A).transpose = s • (A * A.transpose) := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hs]

theorem quartetQ_smul (b : Matrix (Fin m) (Fin m) ℝ) (s : ℝ) (g : Fin m → ℝ) :
    quartetQ β lam ρ (s • b) g = s * quartetQ β lam ρ b g := by
  simp only [quartetQ, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quartetV_smul (b : Matrix (Fin m) (Fin m) ℝ) (c s : ℝ) (g : Fin m → ℝ) :
    quartetV β lam ρ (s • b) (s * c) g = s * quartetV β lam ρ b c g := by
  unfold quartetV
  rw [quartetQ_smul]
  ring

/-- **Gaussian integration by parts at scale `√s`**: `E H(√s G) = β s E V(√s G)`, `V` with the
original covariance. -/
theorem integral_quartetH_scaled (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) {s : ℝ} (hs : 0 ≤ s) :
    ∫ g, quartetH β lam ρ g ∂gaussianVector (Real.sqrt s • A) =
      β * s * ∫ g, quartetV β lam ρ (A * A.transpose) c g ∂gaussianVector (Real.sqrt s • A) := by
  have hc' : ∀ i, ((Real.sqrt s • A) * (Real.sqrt s • A).transpose :
      Matrix (Fin m) (Fin m) ℝ) i i = s * c := by
    intro i
    rw [scaled_cov A hs, Matrix.smul_apply, smul_eq_mul, hc]
  rw [integral_quartetH_eq hβ hlam hρ (Real.sqrt s • A) hc']
  simp_rw [scaled_cov A hs, quartetV_smul]
  rw [integral_const_mul]
  ring

/-- **Pathwise derivative**: `∂_s log D(√s g) = (β / 2s) H(√s g)` for `s > 0`. -/
theorem hasDerivAt_log_quartetD_sqrt_smul (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (g : Fin m → ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => Real.log (quartetD β lam ρ (Real.sqrt s • g)))
      (β / (2 * s) * quartetH β lam ρ (Real.sqrt s • g)) s := by
  have hin : HasDerivAt (fun s => Real.sqrt s • g) ((1 / (2 * Real.sqrt s)) • g) s :=
    (Real.hasDerivAt_sqrt hs.ne').smul_const g
  have hD : HasDerivAt (fun s => quartetD β lam ρ (Real.sqrt s • g))
      ((∑ i, (ρ i * (β * fluctuation β (lam + 1 / 2) ((Real.sqrt s • g) i))) • coordProj i :
        (Fin m → ℝ) →L[ℝ] ℝ) ((1 / (2 * Real.sqrt s)) • g)) s :=
    (hasFDerivAt_quartetD hβ hlam (Real.sqrt s • g)).comp_hasDerivAt
      (f := fun s => Real.sqrt s • g) s hin
  have hpos := quartetD_pos hβ hlam hρ (Real.sqrt s • g)
  refine (hD.log hpos.ne').congr_deriv ?_
  simp only [sum_apply, smul_apply, coordProj_apply, Pi.smul_apply, smul_eq_mul, quartetH,
    quartetW, quartetN]
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hDne := hpos.ne'
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show β / (2 * s) = β / (2 * (Real.sqrt s * Real.sqrt s)) by rw [hss]]
  field_simp

/-! ### Differentiation under the integral -/

theorem measurable_log_quartetD_sqrt (hβ : 0 < β) (hlam : 0 < lam) (s : ℝ) :
    Measurable fun z : Fin (n + 1) → ℝ =>
      Real.log (quartetD β lam ρ (Real.sqrt s • A.mulVec z)) :=
  Real.measurable_log.comp ((continuous_quartetD hβ hlam).comp
    ((continuous_const (y := Real.sqrt s)).smul (continuous_mulVec A))).measurable

theorem integrable_polyBound (C : ℝ) (k : ℕ) (r : ℝ) :
    Integrable (fun z : Fin (n + 1) → ℝ => r * (C * (1 + ‖A.mulVec z‖) ^ k))
      (stdGaussianPi (n + 1)) := by
  refine integrable_of_polyBoundedPi ?_ ((polyBoundedPi_comp_mulVec A
    (F := fun g : Fin m → ℝ => C * (1 + ‖g‖) ^ k) ⟨|C|, k, fun g => ?_⟩).const_mul r)
  · exact (continuous_const.mul (continuous_const.mul ((continuous_const.add
      (continuous_norm.comp (continuous_mulVec A))).pow k))).measurable
  · rw [abs_mul, abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖g‖) k)]

/-- **`L'(s) = (β²/2) E[V_s(G)]` on `(0,1)`.** -/
theorem hasDerivAt_interpL (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (interpL β lam ρ A) (β ^ 2 / 2 * interpV β lam ρ A c s₀) s₀ := by
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
    rw [integral_const_mul, hHint, integral_quartetH_scaled A hβ hlam hρ hc hs₀0.le,
      ← interpV_eq A hβ hlam hρ c s₀]
    field_simp
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hβ (by linarith [hs.1] : 0 < 2 * s))]
    have h1 : β / (2 * s) ≤ β / s₀ :=
      div_le_div_of_nonneg_left hβ.le hs₀0 (by linarith [hs.1])
    exact mul_le_mul h1 (hCk _ (sqrt_abs_le_two hs.2.le) _) (abs_nonneg _) (div_pos hβ hs₀0).le

/-! ### Continuity on `[0,1]` -/

theorem continuousOn_interpL (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] : ContinuousOn (interpL β lam ρ A) (Icc 0 1) := by
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_log_quartetD hβ hlam hρ).smul_bound
  refine continuousOn_of_dominated
    (F := fun s (z : Fin (n + 1) → ℝ) => Real.log (quartetD β lam ρ (Real.sqrt s • A.mulVec z)))
    (bound := fun z => 1 * (C * (1 + ‖A.mulVec z‖) ^ k))
    (fun s _ => (measurable_log_quartetD_sqrt A hβ hlam s).aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_polyBound A C k 1)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, one_mul]
    exact hCk _ (sqrt_abs_le_two (by linarith [hs.2])) _
  · exact (((continuous_quartetD hβ hlam).comp
      (Real.continuous_sqrt.smul continuous_const)).log
        fun s => (quartetD_pos hβ hlam hρ _).ne').continuousOn

theorem continuousOn_interpV (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] (c : ℝ) : ContinuousOn (interpV β lam ρ A c) (Icc 0 1) := by
  obtain ⟨C, k, hCk⟩ := (polyBoundedPi_quartetV hβ hlam hρ (A * A.transpose) c).smul_bound
  refine continuousOn_of_dominated
    (F := fun s (z : Fin (n + 1) → ℝ) =>
      quartetV β lam ρ (A * A.transpose) c (Real.sqrt s • A.mulVec z))
    (bound := fun z => 1 * (C * (1 + ‖A.mulVec z‖) ^ k))
    (fun s _ => ((continuous_quartetV hβ hlam hρ _ c).comp
      ((continuous_const (y := Real.sqrt s)).smul
        (continuous_mulVec A))).measurable.aestronglyMeasurable)
    (fun s hs => Filter.Eventually.of_forall fun z => ?_) (integrable_polyBound A C k 1)
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, one_mul]
    exact hCk _ (sqrt_abs_le_two (by linarith [hs.2])) _
  · exact ((continuous_quartetV hβ hlam hρ _ c).comp
      (Real.continuous_sqrt.smul continuous_const)).continuousOn

theorem interpV_nonneg (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
    {c : ℝ} (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) (s : ℝ) :
    0 ≤ interpV β lam ρ A c s :=
  integral_nonneg fun _ => (quartetV_nonneg hβ hlam hρ A hc _).1

/-! ### The interpolation identity -/

theorem interpL_one (hβ : 0 < β) (hlam : 0 < lam) :
    interpL β lam ρ A 1 = ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector A := by
  rw [interpL_eq A hβ hlam 1, Real.sqrt_one, one_smul]

theorem interpL_zero (hβ : 0 < β) (hlam : 0 < lam) :
    interpL β lam ρ A 0 = Real.log (β ^ (-lam) * Real.Gamma lam * ∑ i, ρ i) := by
  unfold interpL
  simp only [Real.sqrt_zero, zero_smul]
  rw [integral_const, probReal_univ, one_smul]
  congr 1
  unfold quartetD
  simp only [Pi.zero_apply, fluctuation_zero β lam hβ hlam]
  rw [← Finset.sum_mul]
  ring

/-- **Covariance interpolation.** For the Gaussian vector `G = AZ` with constant covariance
diagonal `c`: `E log D(G) = log(β^{−λ} Γ(λ) ∑ᵢ ρᵢ) + (β²/2) ∫₀¹ E[V_s(G)] ds`. -/
theorem integral_log_quartetD_eq (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) :
    ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector A =
      Real.log (β ^ (-lam) * Real.Gamma lam * ∑ i, ρ i) +
        ∫ s in (0 : ℝ)..1, β ^ 2 / 2 * interpV β lam ρ A c s := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_interpL A hβ hlam hρ) (fun s hs => hasDerivAt_interpL A hβ hlam hρ hc hs) ?_
  · rw [hFTC, interpL_one A hβ hlam, interpL_zero A hβ hlam]
    ring
  · have h := (continuousOn_const (c := β ^ 2 / 2)).mul (continuousOn_interpV A hβ hlam hρ c)
    rw [← Set.uIcc_of_le (zero_le_one' ℝ)] at h
    exact h.intervalIntegrable

/-- **`E log D(G) ≥ log D(0)`**: the expected log-evidence of the Gaussian model is at least its
value at the deterministic centre `D(0) = β^{−λ} Γ(λ) ∑ᵢ ρᵢ`. -/
theorem log_quartetD_zero_le_integral (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) :
    Real.log (β ^ (-lam) * Real.Gamma lam * ∑ i, ρ i) ≤
      ∫ g, Real.log (quartetD β lam ρ g) ∂gaussianVector A := by
  rw [integral_log_quartetD_eq A hβ hlam hρ hc]
  have : 0 ≤ ∫ s in (0 : ℝ)..1, β ^ 2 / 2 * interpV β lam ρ A c s :=
    intervalIntegral.integral_nonneg zero_le_one fun s _ =>
      mul_nonneg (by positivity) (interpV_nonneg A hβ hlam hρ hc s)
  linarith

end Grammar
