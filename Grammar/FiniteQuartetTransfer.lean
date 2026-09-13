/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GaussianQuartet
import Grammar.GaussianQuartetGeneral
import Grammar.CovarianceInterpolation
import Grammar.ExpectationBridge

/-!
# Finite-resolution quartet expectation transfer (CCCLIV; companion note, consult #106 Rank 1)

For finite-dimensional empirical phase vectors `g_n ⇒ G` (convergence in distribution) with
uniformly bounded moments of every order, and every continuous polynomially bounded observable
`F`, `𝔼 F(g_n) → 𝔼 F(G)` (★ `tendsto_integral_polyBounded_of_tendstoInDistribution`: the
continuous mapping theorem plus the expectation bridge with a uniform second moment of `F(g_n)`).
Applied to the self-normalised Gaussian quartet `W_i, M₂, H, V, log D` (all continuous and
polynomially bounded for EVERY `β, λ > 0` — no raw-evidence threshold `βκ < 2`), with the
Gaussian limit law `gaussianVector A`: ★★ `tendsto_integral_quartet_of_tendstoInDistribution`
and the four Bayes combinations ★★ `tendsto_integral_bayes_quartet` converging to
`(λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν)` with `ν = 𝔼H(G)/2` (constant covariance diagonal
`c`). The hypotheses are the finite-dimensional distributional convergence and the uniform moments
of the empirical phase vectors — NOT the identification of `F(g_n)` with an actual model error
coefficient (Rank 2), nor the continuum sup-norm moment bounds (stopping rule of #106).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace Grammar

section General

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {m : ℕ}

/-- **Uniform moments of every order** of a sequence of random vectors. -/
def UniformMoments (μ : ∀ n, Measure (Ω n)) (g : ∀ n, Ω n → Fin m → ℝ) : Prop :=
  ∀ q : ℕ, ∃ M : ℝ, ∀ n, Integrable (fun ω => ‖g n ω‖ ^ q) (μ n) ∧ ∫ ω, ‖g n ω‖ ^ q ∂μ n ≤ M

theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : (1 + x) ^ j ≤ 2 ^ j * (1 + x ^ j) := by
  have h1 : 1 + x ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 x) ^ j ≤ 1 + x ^ j := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1) j]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hx j]
  calc (1 + x) ^ j ≤ (2 * max 1 x) ^ j :=
        pow_le_pow_left₀ (by linarith) h1 j
    _ = 2 ^ j * (max 1 x) ^ j := mul_pow _ _ _
    _ ≤ 2 ^ j * (1 + x ^ j) := by gcongr

/-- ★ **Expectation transfer for polynomially bounded continuous observables**: if `g_n ⇒ G` with
uniform moments of every order, then `𝔼 F(g_n) → 𝔼 F(G)` and `F(G)` is integrable. -/
theorem tendsto_integral_polyBounded_of_tendstoInDistribution {g : ∀ n, Ω n → Fin m → ℝ}
    {G : Ω' → Fin m → ℝ} (hg : TendstoInDistribution g atTop G μ μ') (hmom : UniformMoments μ g)
    {F : (Fin m → ℝ) → ℝ} (hF : Continuous F) (hFb : PolyBoundedPi F) :
    Integrable (fun ω => F (G ω)) μ' ∧
      Tendsto (fun n => ∫ ω, F (g n ω) ∂μ n) atTop (𝓝 (∫ ω, F (G ω) ∂μ')) := by
  obtain ⟨C, k, hCk⟩ := hFb
  have hC : 0 ≤ C := by
    have := hCk 0
    have hpos : (0 : ℝ) < (1 + ‖(0 : Fin m → ℝ)‖) ^ k := by positivity
    nlinarith [abs_nonneg (F 0)]
  have hX : TendstoInDistribution (fun n => F ∘ g n) atTop (F ∘ G) μ μ' := hg.continuous_comp hF
  obtain ⟨M, hM⟩ := hmom (2 * k)
  have hbound : ∀ z : Fin m → ℝ, |F z| ^ (2 : ℝ) ≤ C ^ 2 * 2 ^ (2 * k) * (1 + ‖z‖ ^ (2 * k)) := by
    intro z
    rw [Real.rpow_two]
    have h1 : |F z| ^ 2 ≤ (C * (1 + ‖z‖) ^ k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCk z) 2
    have h2 : (C * (1 + ‖z‖) ^ k) ^ 2 = C ^ 2 * (1 + ‖z‖) ^ (2 * k) := by ring
    have h3 := one_add_pow_le (norm_nonneg z) (2 * k)
    calc |F z| ^ 2 ≤ C ^ 2 * (1 + ‖z‖) ^ (2 * k) := h2 ▸ h1
      _ ≤ C ^ 2 * (2 ^ (2 * k) * (1 + ‖z‖ ^ (2 * k))) := by gcongr
      _ = C ^ 2 * 2 ^ (2 * k) * (1 + ‖z‖ ^ (2 * k)) := by ring
  have hdom : ∀ n, Integrable (fun ω => C ^ 2 * 2 ^ (2 * k) * (1 + ‖g n ω‖ ^ (2 * k))) (μ n) :=
    fun n => ((integrable_const (1 : ℝ)).add (hM n).1).const_mul _
  have hint : ∀ n, Integrable (fun ω => |(F ∘ g n) ω| ^ (2 : ℝ)) (μ n) := fun n => by
    refine (hdom n).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact ((hF.measurable.comp_aemeasurable (hg.forall_aemeasurable n)).norm.pow_const
        _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact hbound _
  have hMb : ∀ n, ∫ ω, |(F ∘ g n) ω| ^ (2 : ℝ) ∂μ n ≤ C ^ 2 * 2 ^ (2 * k) * (1 + M) := fun n => by
    calc ∫ ω, |(F ∘ g n) ω| ^ (2 : ℝ) ∂μ n
        ≤ ∫ ω, C ^ 2 * 2 ^ (2 * k) * (1 + ‖g n ω‖ ^ (2 * k)) ∂μ n :=
          integral_mono (hint n) (hdom n) fun ω => hbound _
      _ = C ^ 2 * 2 ^ (2 * k) * (1 + ∫ ω, ‖g n ω‖ ^ (2 * k) ∂μ n) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hM n).1, integral_const]
          simp
      _ ≤ C ^ 2 * 2 ^ (2 * k) * (1 + M) := by gcongr; exact (hM n).2
  exact tendsto_integral_of_tendstoInDistribution_of_moment hX one_lt_two hint hMb

end General

/-! ### The self-normalised quartet -/

section Quartet

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {m k : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}
  (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
  {g : ∀ n, Ω n → Fin m → ℝ} {G : Ω' → Fin m → ℝ}
  (hg : TendstoInDistribution g atTop G μ μ') (hmom : UniformMoments μ g)
  (A : Matrix (Fin m) (Fin (k + 1)) ℝ) (hG : μ'.map G = gaussianVector A)

omit [Nonempty (Fin m)] in
include hg hmom hG in
/-- Expectation transfer for one quartet observable, with the limit written against the Gaussian
vector law. -/
theorem tendsto_integral_quartetObs {F : (Fin m → ℝ) → ℝ} (hF : Continuous F)
    (hFb : PolyBoundedPi F) :
    Tendsto (fun n => ∫ ω, F (g n ω) ∂μ n) atTop (𝓝 (∫ z, F z ∂gaussianVector A)) := by
  have h := tendsto_integral_polyBounded_of_tendstoInDistribution hg hmom hF hFb
  have he : ∫ ω, F (G ω) ∂μ' = ∫ z, F z ∂gaussianVector A := by
    rw [← hG, integral_map hg.aemeasurable_limit hF.aestronglyMeasurable]
  rw [he] at h
  exact h.2

include hβ hlam hρ hg hmom hG

/-- ★★ **Finite-resolution quartet expectation transfer**: for `g_n ⇒ G ~ N(0, AAᵀ)` with uniform
moments, the expectations of `W_i, M₂, H, V_gen, log D` converge to their Gaussian values, for every
`β, λ > 0`. -/
theorem tendsto_integral_quartet_of_tendstoInDistribution (b : Matrix (Fin m) (Fin m) ℝ) :
    (∀ i, Tendsto (fun n => ∫ ω, quartetW β lam ρ i (g n ω) ∂μ n) atTop
      (𝓝 (∫ z, quartetW β lam ρ i z ∂gaussianVector A))) ∧
    Tendsto (fun n => ∫ ω, quartetM2 β lam ρ (g n ω) ∂μ n) atTop
      (𝓝 (∫ z, quartetM2 β lam ρ z ∂gaussianVector A)) ∧
    Tendsto (fun n => ∫ ω, quartetH β lam ρ (g n ω) ∂μ n) atTop
      (𝓝 (∫ z, quartetH β lam ρ z ∂gaussianVector A)) ∧
    Tendsto (fun n => ∫ ω, quartetVgen β lam ρ b (g n ω) ∂μ n) atTop
      (𝓝 (∫ z, quartetVgen β lam ρ b z ∂gaussianVector A)) ∧
    Tendsto (fun n => ∫ ω, Real.log (quartetD β lam ρ (g n ω)) ∂μ n) atTop
      (𝓝 (∫ z, Real.log (quartetD β lam ρ z) ∂gaussianVector A)) := by
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_integral_quartetObs hg hmom A hG (continuous_quartetW hβ hlam hρ i)
      (polyBoundedPi_quartetW hβ hlam hρ i)
  · exact tendsto_integral_quartetObs hg hmom A hG (F := quartetM2 β lam ρ)
      (continuous_finsetSum _ fun i _ => continuous_quartetR hβ hlam hρ i)
      (polyBoundedPi_quartetM2 hβ hlam hρ)
  · exact tendsto_integral_quartetObs hg hmom A hG (continuous_quartetH hβ hlam hρ)
      (polyBoundedPi_quartetH hβ hlam hρ)
  · exact tendsto_integral_quartetObs hg hmom A hG
      (continuous_quartetVgen hβ hlam hρ b) (polyBoundedPi_quartetVgen hβ hlam hρ b)
  · refine tendsto_integral_quartetObs hg hmom A hG ?_ (polyBoundedPi_log_quartetD hβ hlam hρ)
    exact Real.continuousOn_log.comp_continuous (continuous_quartetD (ρ := ρ) hβ hlam)
      fun z => (quartetD_pos hβ hlam hρ z).ne'

/-- ★★ **The four Bayes combinations** `M₂, M₂ − H, M₂ − V/2, M₂ − H − V/2` converge in expectation
to `λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν` with `ν = 𝔼H(G)/2`, for a constant covariance
diagonal `c` (`V = c M₂ − Q`), every `β, λ > 0`. -/
theorem tendsto_integral_bayes_quartet {c : ℝ}
    (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c) :
    let ν := (∫ z, quartetH β lam ρ z ∂gaussianVector A) / 2
    Tendsto (fun n => ∫ ω, quartetM2 β lam ρ (g n ω) ∂μ n) atTop (𝓝 (lam / β + ν)) ∧
    Tendsto (fun n => ∫ ω, (quartetM2 β lam ρ (g n ω) - quartetH β lam ρ (g n ω)) ∂μ n) atTop
      (𝓝 (lam / β - ν)) ∧
    Tendsto (fun n => ∫ ω, (quartetM2 β lam ρ (g n ω) -
        quartetV β lam ρ (A * A.transpose) c (g n ω) / 2) ∂μ n) atTop
      (𝓝 ((lam - ν) / β + ν)) ∧
    Tendsto (fun n => ∫ ω, (quartetM2 β lam ρ (g n ω) - quartetH β lam ρ (g n ω) -
        quartetV β lam ρ (A * A.transpose) c (g n ω) / 2) ∂μ n) atTop
      (𝓝 ((lam - ν) / β - ν)) := by
  intro ν
  obtain ⟨-, hV, hM2⟩ := quartet_identities hβ hlam hρ A hc
  have hH : ∫ z, quartetH β lam ρ z ∂gaussianVector A = 2 * ν := by
    simp only [ν]
    ring
  set b : Matrix (Fin m) (Fin m) ℝ := A * A.transpose with hb
  have hcM2 : Continuous (quartetM2 β lam ρ) :=
    continuous_finsetSum _ fun i _ => continuous_quartetR hβ hlam hρ i
  have hbM2 := polyBoundedPi_quartetM2 hβ hlam hρ
  have hcH := continuous_quartetH hβ hlam hρ
  have hbH := polyBoundedPi_quartetH hβ hlam hρ
  have hcV := continuous_quartetV hβ hlam hρ b c
  have hbV := polyBoundedPi_quartetV hβ hlam hρ b c
  have hiM2 := integrable_quartetM2 hβ hlam hρ A
  have hiH := integrable_quartetH hβ hlam hρ A
  have hiV := integrable_quartetV hβ hlam hρ A b c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := tendsto_integral_quartetObs hg hmom A hG hcM2 hbM2
    rwa [hM2] at h
  · have h := tendsto_integral_quartetObs hg hmom A hG
      (F := fun z => quartetM2 β lam ρ z - quartetH β lam ρ z) (hcM2.sub hcH) (hbM2.sub hbH)
    rw [integral_sub hiM2 hiH, hM2, hH] at h
    convert h using 2
    ring
  · have hb3 : PolyBoundedPi fun z => quartetM2 β lam ρ z - quartetV β lam ρ b c z / 2 := by
      have e : (fun z => quartetM2 β lam ρ z - quartetV β lam ρ b c z / 2) =
          fun z => quartetM2 β lam ρ z - (1 / 2) * quartetV β lam ρ b c z :=
        funext fun z => by ring
      rw [e]
      exact hbM2.sub (hbV.const_mul _)
    have h := tendsto_integral_quartetObs hg hmom A hG
      (F := fun z => quartetM2 β lam ρ z - quartetV β lam ρ b c z / 2) (hcM2.sub (hcV.div_const 2))
      hb3
    rw [integral_sub hiM2 (hiV.div_const 2), integral_div, hM2, hV] at h
    convert h using 2
    ring
  · have hb4 : PolyBoundedPi fun z =>
        quartetM2 β lam ρ z - quartetH β lam ρ z - quartetV β lam ρ b c z / 2 := by
      have e : (fun z => quartetM2 β lam ρ z - quartetH β lam ρ z - quartetV β lam ρ b c z / 2) =
          fun z => quartetM2 β lam ρ z - quartetH β lam ρ z - (1 / 2) * quartetV β lam ρ b c z :=
        funext fun z => by ring
      rw [e]
      exact (hbM2.sub hbH).sub (hbV.const_mul _)
    have h := tendsto_integral_quartetObs hg hmom A hG
      (F := fun z => quartetM2 β lam ρ z - quartetH β lam ρ z - quartetV β lam ρ b c z / 2)
      ((hcM2.sub hcH).sub (hcV.div_const 2)) hb4
    have hiMH : Integrable (fun z => quartetM2 β lam ρ z - quartetH β lam ρ z) (gaussianVector A) :=
      hiM2.sub hiH
    rw [integral_sub hiMH (hiV.div_const 2), integral_sub hiM2 hiH, integral_div, hM2, hH, hV] at h
    convert h using 2
    ring

end Quartet

end Grammar
