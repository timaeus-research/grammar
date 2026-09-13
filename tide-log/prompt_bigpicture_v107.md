# Consult #107 — companion note: Ranks 1–3 landed; the controlled model test, Rank 5, and closure

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 657 modules, zero sorry/axiom, headline theorems axiom-clean). Your consult #106
delivered the claim ledger for `averaging_dataset.tex` and authorised, after G0: (1) finite-resolution
self-normalised moment and expectation transfer, (2) an explicit expected-quartet endpoint consuming actual-observable
`L¹` transfer certificates, (3) a narrowly stated predictive Taylor-remainder lemma followed by one controlled model
test, (4) only if missing: packaging the coordinate CLT/tail closure and the Taylor-law-to-compact-field adapter.

## 1. Landed since #106 (main `d84dc9d`)

* **G0** (`tide-log/g0_signature_sheet.md`): the ℓ¹ CLT and the `ClosureEndpoint` theorems CONSTRUCT the limit
  law with its Gaussian marginals and tail bound from the coordinate certificate (`hc2`, `hsum`, i.i.d.); consumed
  are the certified chart data (the model-to-chart coefficient family), the sub-Gaussian proxy, `p>1` with
  `pβκ<2`, the bounded amplitude mass of the deterministic datum, and `𝔼|A_n Rem_n| → 0`. §6.10 reconciled.
* **Ten mandatory tex repairs** applied to the note (CLT conditionalised; scaled-assembly `L¹` condition; Hironaka
  existence vs comparison vs transport; §6.9 three inputs; `p ≥ 1`, nonnegative scale; "at most 1"; interface
  table rows incl. a new "Expected errors" row; annealed identity as an extended integral; `Q(g)` defined;
  `β_eff ≤ β` with strictness conditional).
* **Rank 1** CCCLIV `FiniteQuartetTransfer`: `UniformMoments μ g` (uniform moments of every order),
  ★ `tendsto_integral_polyBounded_of_tendstoInDistribution` (`g_n ⇒ G`, uniform moments, `F` continuous and
  polynomially bounded ⇒ `F(G)` integrable and `𝔼F(g_n) → 𝔼F(G)`; continuous mapping + the expectation bridge
  with a uniform second moment), ★★ `tendsto_integral_quartet_of_tendstoInDistribution` (`W_i, M₂, H, V_gen,
  log D` for every `β, λ > 0`), ★★ `tendsto_integral_bayes_quartet` (the four Bayes combinations →
  `λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν`, `ν = 𝔼H(G)/2`, constant diagonal).
* **Rank 2** CCCLV `QuartetObservableTransfer`: ★★ `tendsto_integral_of_L1_transfer`, `bayesCombination`,
  `bayesValue`, ★★★ `expected_quartet_of_L1_transfer` (integrable actual observables `B_{n,j}` with
  `𝔼|B_{n,j} − 𝓠_j(g_n)| → 0` ⇒ `𝔼B_{n,j} → bayesValue β λ ν j`).
* **Rank 3, first half** CCCLVI `PredictiveRemainder`: with `ℓ = cgf X μ` (Mathlib), `tiltMoment X μ k t =
  μ[X^k e^{tX}]`, `tiltMean`, `tiltKappa3 = m₃/m₀ − 3m₁m₂/m₀² + 2m₁³/m₀³`; `iteratedDeriv_three_cgf`
  (`ℓ''' = κ₃`), `tiltKappa3_eq_centred` (`κ₃(t) = μ_t[(X − ⟨X⟩_t)³]`), ★ `abs_tiltKappa3_le` (`|κ₃(t)| ≤
  tiltAbsThird X μ t := μ_t[|X − ⟨X⟩_t|³]`), ★ `cgf_taylor` (`ℓ(1) = μ[X] + Var(X)/2 + κ₃(u)/6`, some
  `u ∈ (0,1)`), `predictiveRemainder X μ := ℓ(1) − μ[X] − Var(X)/2`, ★★ `abs_predictiveRemainder_le : |R| ≤ S/6`
  when `tiltAbsThird ≤ S` on `[0,1]`, `neg_log_integral_exp_neg_eq` (`X = −f`), ★★
  `tendsto_mul_integral_abs_remainder` (`|R_n| ≤ S_n/6`, `n𝔼S_n → 0 ⇒ n𝔼|R_n| → 0`). The note has two new
  propositions with dots (`prop:finite_transfer`, `prop:predictive_remainder`), stating what remains: the `L¹`
  transfer of the ACTUAL scaled normalised observables, and the model-level discharge
  `n·𝔼 sup_{t∈[0,1]} Π_{n,t}[|f − ⟨f⟩_t|³] → 0`; the sub-Gaussian ⇒ uniform-moments bridge is not formalised.

## 2. Questions

1. **Acceptance and wording** of Ranks 1–3 as landed (statements below). Anything to change? In particular the
   bound is in terms of the tilted CENTRED absolute third moment (constant `1/6`); the passage to the raw
   `μ_t[|X|³]` (constant `8/6`) was not done — needed?
2. **The controlled model test** (second half of Rank 3). Which finite-resolution model should discharge the
   tilted-third-moment certificate, narrowly? Candidates: (a) the normal location model
   `f(x,w) = (x−w)²/2 − x²/2` with a Gaussian prior — the posterior is Gaussian, `f(x,·)` is quadratic in `w`,
   the tilted laws are Gaussian, and `Π_{n,t}[|f − ⟨f⟩_t|³]` is explicit and `O(n^{−3/2})` for fixed `x`; (b)
   the divisor model of the note's §2 examples; (c) a purely finite-resolution Gaussian-quartet model (the
   `g`-vector as the parameter). Please specify the target theorem for your choice, its hypothesis list, the
   reusable declarations (`EffectiveTemperature:sum_normalLocation`, `normalLocation_standard_form`, …), the
   gate and the stopping rule. What expectation over `x` (fresh test point vs training average) should the
   certificate use, and how does it feed `expected_quartet_of_L1_transfer` (what are the `B_{n,j}`)?
3. **Rank 5 (`GaussianField.ofL1TaylorLimit`).** G0 found the CLT/tail law constructed; the compact-base
   results consume a `GaussianField` adapter (`CompactBaseFinite`). Is the adapter already instantiated from the
   Taylor-data law somewhere (constructors below), or is the pushforward along a bounded evaluation map
   `ℓ¹ → C(K)` still to be built? If needed, the target statement and what continuity of the evaluation map
   requires.
4. **Closure criteria for the note programme.** After Rank 3's model test (and Rank 5 if needed), is the note's
   Lean programme closed at your stopping point? What remains as explicit non-claims in the tex, and what should
   the final wording pass check (as in #105)?

## 3. Material

### A. `GaussianField` constructors and consumers in the library
```
Grammar/CompactBaseFinite.lean:209:structure GaussianField {K : Type*} [TopologicalSpace K] [CompactSpace K] (𝒞 : PSDKernel K)
Grammar/CompactBaseFinite.lean:222:  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)
Grammar/CompactBaseFirstMoment.lean:41:  (Γ : GaussianField 𝒞 P)
Grammar/CompactBaseGaussian.lean:191:  [IsProbabilityMeasure P] (Γ : GaussianField 𝒞 P)
Grammar/GaussianFieldFernique.lean:14:the evaluations supplies their measurability. The constructor `GaussianField.ofIsGaussian` builds
Grammar/GaussianFieldFernique.lean:61:noncomputable def GaussianField.ofIsGaussian (𝒞 : PSDKernel K) (P : Measure Ω) (G : Ω → C(K, ℝ))
Grammar/GaussianFieldFernique.lean:72:@[simp] theorem GaussianField.ofIsGaussian_G (𝒞 : PSDKernel K) (P : Measure Ω)
Grammar/GaussianFieldFernique.lean:74:    (GaussianField.ofIsGaussian 𝒞 P G hG law).G = G := rfl
Grammar/GaussianLinearCombination.lean:21:`GaussianField.ofIsGaussian` by mean/covariance certificates:
Grammar/GaussianLinearCombination.lean:22:`GaussianField.ofIsGaussianCertificates`.
Grammar/GaussianLinearCombination.lean:307:noncomputable def GaussianField.ofIsGaussianCertificates (𝒞 : PSDKernel K) (P : Measure Ω)
Grammar/GaussianLinearCombination.lean:311:  GaussianField.ofIsGaussian 𝒞 P G hG fun m x =>
Grammar/GaussianLinearCombination.lean:315:@[simp] theorem GaussianField.ofIsGaussianCertificates_G (𝒞 : PSDKernel K) (P : Measure Ω)
Grammar/GaussianLinearCombination.lean:317:    (GaussianField.ofIsGaussianCertificates 𝒞 P G hG hmean hcov).G = G := rfl
```

### B. CCCLIV (full)
```lean
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
```

### C. CCCLV (full)
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FiniteQuartetTransfer

/-!
# Expected quartet coefficients from an `L¹` observable-transfer certificate
(CCCLV; companion note, consult #106 Rank 2)

The honest statistical interface for the expected-error coefficients: let `B_{n,j}` be the actual
scaled model observables and `𝓠_j(g_n)` the four Bayes combinations of the finite-resolution
quartet at the empirical phase vector. If `𝔼|B_{n,j} − 𝓠_j(g_n)| → 0` (`L¹` observable transfer)
and the empirical phase vectors converge in distribution to the Gaussian vector with uniform
moments, then `𝔼B_{n,j} → (λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν)_j` with `ν = 𝔼H(G)/2`
(★★ `tendsto_integral_of_L1_transfer` for one observable, ★★★ `expected_quartet_of_L1_transfer`
for the four). The residual must be `o_{L¹}(1)`: an `o_P(1)` residual would need a separate uniform
integrability certificate for the actual `B_{n,j}` (not supplied here). The identification of the
`B_{n,j}` with a statistical model's error coefficients, and the predictive remainder, are the
model-facing inputs (Ranks 2–3 of #106).
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace Grammar

section L1Transfer

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}

/-- ★★ **`L¹` transfer of expectations**: if `𝔼|B_n − Q_n| → 0` and `𝔼Q_n → L`, then `𝔼B_n → L`. -/
theorem tendsto_integral_of_L1_transfer {B Q : ∀ n, Ω n → ℝ} {L : ℝ}
    (hBint : ∀ n, Integrable (B n) (μ n)) (hQint : ∀ n, Integrable (Q n) (μ n))
    (hL1 : Tendsto (fun n => ∫ ω, |B n ω - Q n ω| ∂μ n) atTop (𝓝 0))
    (hQ : Tendsto (fun n => ∫ ω, Q n ω ∂μ n) atTop (𝓝 L)) :
    Tendsto (fun n => ∫ ω, B n ω ∂μ n) atTop (𝓝 L) := by
  have hdiff : Tendsto (fun n => ∫ ω, B n ω ∂μ n - ∫ ω, Q n ω ∂μ n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hL1
    rw [← integral_sub (hBint n) (hQint n), Real.norm_eq_abs]
    exact (abs_integral_le_integral_abs).trans (le_of_eq rfl)
  have := hdiff.add hQ
  simpa using this

end L1Transfer

section Endpoint

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (μ n)] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {m k : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}
  (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
  {g : ∀ n, Ω n → Fin m → ℝ} {G : Ω' → Fin m → ℝ}
  (hg : TendstoInDistribution g atTop G μ μ') (hmom : UniformMoments μ g)
  (A : Matrix (Fin m) (Fin (k + 1)) ℝ) (hG : μ'.map G = gaussianVector A) {c : ℝ}
  (hc : ∀ i, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i = c)

/-- The four Bayes combinations of the finite-resolution quartet at a phase vector. -/
noncomputable def bayesCombination (β lam : ℝ) (ρ : Fin m → ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) : Fin 4 → (Fin m → ℝ) → ℝ
  | 0 => fun z => quartetM2 β lam ρ z
  | 1 => fun z => quartetM2 β lam ρ z - quartetH β lam ρ z
  | 2 => fun z => quartetM2 β lam ρ z - quartetV β lam ρ b c z / 2
  | 3 => fun z => quartetM2 β lam ρ z - quartetH β lam ρ z - quartetV β lam ρ b c z / 2

/-- The four Bayes values `λ/β + ν, λ/β − ν, (λ−ν)/β + ν, (λ−ν)/β − ν`. -/
noncomputable def bayesValue (β lam ν : ℝ) : Fin 4 → ℝ
  | 0 => lam / β + ν
  | 1 => lam / β - ν
  | 2 => (lam - ν) / β + ν
  | 3 => (lam - ν) / β - ν

include hβ hlam hρ hg hmom hG hc in
/-- ★★★ **Expected quartet coefficients from `L¹` observable transfer**: for actual scaled
observables `B_{n,j}` with `𝔼|B_{n,j} − 𝓠_j(g_n)| → 0`, `𝔼B_{n,j} → bayesValue β λ ν j`,
`ν = 𝔼H(G)/2`. -/
theorem expected_quartet_of_L1_transfer {B : Fin 4 → ∀ n, Ω n → ℝ}
    (hBint : ∀ j n, Integrable (B j n) (μ n))
    (hL1 : ∀ j, Tendsto (fun n => ∫ ω, |B j n ω -
      bayesCombination β lam ρ (A * A.transpose) c j (g n ω)| ∂μ n) atTop (𝓝 0)) (j : Fin 4) :
    Tendsto (fun n => ∫ ω, B j n ω ∂μ n) atTop
      (𝓝 (bayesValue β lam ((∫ z, quartetH β lam ρ z ∂gaussianVector A) / 2) j)) := by
  have hQ := tendsto_integral_bayes_quartet hβ hlam hρ hg hmom A hG hc
  -- integrability of the quartet combinations along the sequence
  have hcM2 : Continuous (quartetM2 β lam ρ) :=
    continuous_finsetSum _ fun i _ => continuous_quartetR hβ hlam hρ i
  have hbM2 := polyBoundedPi_quartetM2 hβ hlam hρ
  have hcH := continuous_quartetH hβ hlam hρ
  have hbH := polyBoundedPi_quartetH hβ hlam hρ
  have hcV := continuous_quartetV hβ hlam hρ (A * A.transpose) c
  have hbV := polyBoundedPi_quartetV hβ hlam hρ (A * A.transpose) c
  have hint : ∀ (F : (Fin m → ℝ) → ℝ), Continuous F → PolyBoundedPi F →
      ∀ n, Integrable (fun ω => F (g n ω)) (μ n) := fun F hF hFb n => by
    obtain ⟨C, kk, hCk⟩ := hFb
    obtain ⟨M, hM⟩ := hmom kk
    have hC : 0 ≤ C := by
      have := hCk 0
      have hpos : (0 : ℝ) < (1 + ‖(0 : Fin m → ℝ)‖) ^ kk := by positivity
      nlinarith [abs_nonneg (F 0)]
    refine (((integrable_const (1 : ℝ)).add (hM n).1).const_mul (C * 2 ^ kk)).mono'
      ((hF.measurable.comp_aemeasurable (hg.forall_aemeasurable n)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    calc |F (g n ω)| ≤ C * (1 + ‖g n ω‖) ^ kk := hCk _
      _ ≤ C * (2 ^ kk * (1 + ‖g n ω‖ ^ kk)) := by gcongr; exact one_add_pow_le (norm_nonneg _) kk
      _ = C * 2 ^ kk * (1 + ‖g n ω‖ ^ kk) := by ring
  have hV2 : PolyBoundedPi fun z => quartetV β lam ρ (A * A.transpose) c z / 2 := by
    have e : (fun z => quartetV β lam ρ (A * A.transpose) c z / 2) =
        fun z => (1 / 2) * quartetV β lam ρ (A * A.transpose) c z := funext fun z => by ring
    rw [e]
    exact hbV.const_mul _
  fin_cases j
  · exact tendsto_integral_of_L1_transfer (hBint 0) (hint _ hcM2 hbM2) (hL1 0) hQ.1
  · exact tendsto_integral_of_L1_transfer (hBint 1) (hint _ (hcM2.sub hcH) (hbM2.sub hbH)) (hL1 1)
      hQ.2.1
  · exact tendsto_integral_of_L1_transfer (hBint 2) (hint _ (hcM2.sub (hcV.div_const 2))
      (hbM2.sub hV2)) (hL1 2) hQ.2.2.1
  · exact tendsto_integral_of_L1_transfer (hBint 3) (hint _ ((hcM2.sub hcH).sub (hcV.div_const 2))
      ((hbM2.sub hbH).sub hV2)) (hL1 3) hQ.2.2.2

end Endpoint

end Grammar
```

### D. CCCLVI (full)
```lean
/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Calculus.Taylor

/-!
# The predictive Taylor remainder from the tilted third moment
(CCCLVI; companion note, consult #106 Rank 3)

For a probability measure `μ` (a posterior) and an observable `X` (`X = −f` for a loss `f`) whose
exponential moments exist on a neighbourhood of `[0,1]`, the log-normaliser `ℓ(t) = log μ[e^{tX}]`
(Mathlib's `cgf`) satisfies
`ℓ(1) = μ[X] + Var(X)/2 + κ₃(u)/6` for some `u ∈ (0,1)` (★ `cgf_taylor`), where
`κ₃(t) = m₃/m₀ − 3m₁m₂/m₀² + 2m₁³/m₀³` is the third derivative of `ℓ` — the third cumulant of the
`t`-tilted law (`iteratedDeriv_three_cgf`, `tiltKappa3_eq_centred`: it is the tilted centred third
moment `μ_t[(X − ⟨X⟩_t)³]`). Hence the **predictive remainder**
`R = ℓ(1) − μ[X] − Var(X)/2` obeys ★★ `abs_predictiveRemainder_le : |R| ≤ S/6` whenever the tilted
absolute centred third moments `μ_t[|X − ⟨X⟩_t|³]` are bounded by `S` on `[0,1]`, and
★★ `tendsto_mul_integral_abs_remainder`: `n·𝔼 sup_t μ_t[|X − ⟨X⟩_t|³] → 0 ⇒ n·𝔼|R_n| → 0`. With
`X = −f`: `−ℓ(1) = ⟨f⟩ − ½Var(f) − R`. Not included: the discharge of the tilted-third-moment
certificate in a statistical model (the second half of Rank 3).
-/

open MeasureTheory ProbabilityTheory Filter Set Real Topology

namespace Grammar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

/-! ### Tilted raw moments and the third cumulant -/

/-- The raw tilted moments `m_k(t) = μ[X^k e^{tX}]`. -/
noncomputable def tiltMoment (X : Ω → ℝ) (μ : Measure Ω) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, X ω ^ k * exp (t * X ω) ∂μ

/-- The tilted mean `m₁/m₀`. -/
noncomputable def tiltMean (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  tiltMoment X μ 1 t / tiltMoment X μ 0 t

/-- The third cumulant of the tilted law, `m₃/m₀ − 3m₁m₂/m₀² + 2m₁³/m₀³`. -/
noncomputable def tiltKappa3 (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  tiltMoment X μ 3 t / tiltMoment X μ 0 t -
    3 * tiltMoment X μ 1 t * tiltMoment X μ 2 t / tiltMoment X μ 0 t ^ 2 +
    2 * tiltMoment X μ 1 t ^ 3 / tiltMoment X μ 0 t ^ 3

theorem tiltMoment_zero_eq_mgf : tiltMoment X μ 0 t = mgf X μ t := by
  simp [tiltMoment, mgf]

theorem tiltMoment_zero_pos [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    0 < tiltMoment X μ 0 t := by
  rw [tiltMoment_zero_eq_mgf]
  exact mgf_pos (interior_subset (s := integrableExpSet X μ) ht)

theorem hasDerivAt_tiltMoment (ht : t ∈ interior (integrableExpSet X μ)) (k : ℕ) :
    HasDerivAt (tiltMoment X μ k) (tiltMoment X μ (k + 1) t) t :=
  hasDerivAt_integral_pow_mul_exp_real ht k

theorem integrable_tilt (ht : t ∈ interior (integrableExpSet X μ)) (k : ℕ) :
    Integrable (fun ω => X ω ^ k * exp (t * X ω)) μ :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht k

theorem deriv_cgf_eq (ht : t ∈ interior (integrableExpSet X μ)) :
    deriv (cgf X μ) t = tiltMean X μ t := by
  rw [deriv_cgf ht]
  simp [tiltMean, tiltMoment, mgf]

theorem iteratedDeriv_two_cgf_eq (ht : t ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) t =
      tiltMoment X μ 2 t / tiltMoment X μ 0 t - (tiltMoment X μ 1 t / tiltMoment X μ 0 t) ^ 2 := by
  rw [iteratedDeriv_two_cgf ht, deriv_cgf_eq ht]
  simp [tiltMean, tiltMoment, mgf]

/-- The third derivative of the log-normaliser is the third tilted cumulant. -/
theorem hasDerivAt_iteratedDeriv_two_cgf [IsProbabilityMeasure μ]
    (ht : t ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (iteratedDeriv 2 (cgf X μ)) (tiltKappa3 X μ t) t := by
  have hev : iteratedDeriv 2 (cgf X μ) =ᶠ[𝓝 t] fun u =>
      tiltMoment X μ 2 u / tiltMoment X μ 0 u - (tiltMoment X μ 1 u / tiltMoment X μ 0 u) ^ 2 := by
    filter_upwards [isOpen_interior.eventually_mem ht] with u hu
    exact iteratedDeriv_two_cgf_eq hu
  rw [hev.hasDerivAt_iff]
  have hm0 : tiltMoment X μ 0 t ≠ 0 := (tiltMoment_zero_pos ht).ne'
  have h := ((hasDerivAt_tiltMoment ht 2).div (hasDerivAt_tiltMoment ht 0) hm0).sub
    (((hasDerivAt_tiltMoment ht 1).div (hasDerivAt_tiltMoment ht 0) hm0).pow 2)
  simp only [Pi.div_apply] at h
  convert h using 1
  · funext u
    rfl
  · unfold tiltKappa3
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    ring

theorem iteratedDeriv_three_cgf [IsProbabilityMeasure μ]
    (ht : t ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv 3 (cgf X μ) t = tiltKappa3 X μ t := by
  rw [iteratedDeriv_succ]
  exact (hasDerivAt_iteratedDeriv_two_cgf ht).deriv

/-- The third cumulant is the tilted centred third moment. -/
theorem integrable_centred_cube (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ) :
    Integrable (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) μ := by
  have e : (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) = fun ω =>
      X ω ^ 3 * exp (t * X ω) - 3 * p * (X ω ^ 2 * exp (t * X ω)) +
        3 * p ^ 2 * (X ω ^ 1 * exp (t * X ω)) - p ^ 3 * (X ω ^ 0 * exp (t * X ω)) :=
    funext fun ω => by ring
  rw [e]
  exact (((integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)).add
    ((integrable_tilt ht 1).const_mul _)).sub ((integrable_tilt ht 0).const_mul _)

theorem tiltKappa3_eq_centred [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    tiltKappa3 X μ t =
      (∫ ω, (X ω - tiltMean X μ t) ^ 3 * exp (t * X ω) ∂μ) / tiltMoment X μ 0 t := by
  set p := tiltMean X μ t with hp
  have e : (fun ω => (X ω - p) ^ 3 * exp (t * X ω)) = fun ω =>
      X ω ^ 3 * exp (t * X ω) - 3 * p * (X ω ^ 2 * exp (t * X ω)) +
        3 * p ^ 2 * (X ω ^ 1 * exp (t * X ω)) - p ^ 3 * (X ω ^ 0 * exp (t * X ω)) :=
    funext fun ω => by ring
  rw [e, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · have hm0 : (∫ ω, exp (t * X ω) ∂μ) ≠ 0 := by
      have := (tiltMoment_zero_pos ht).ne'
      simpa [tiltMoment] using this
    simp only [tiltKappa3, hp, tiltMean, tiltMoment, pow_zero, one_mul, pow_one]
    field_simp
    ring
  · exact integrable_tilt ht 3
  · exact (integrable_tilt ht 2).const_mul _
  · exact (integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)
  · exact (integrable_tilt ht 1).const_mul _
  · exact ((integrable_tilt ht 3).sub ((integrable_tilt ht 2).const_mul _)).add
      ((integrable_tilt ht 1).const_mul _)
  · exact (integrable_tilt ht 0).const_mul _

/-- The tilted absolute centred third moment `μ_t[|X − ⟨X⟩_t|³]`. -/
noncomputable def tiltAbsThird (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  (∫ ω, |X ω - tiltMean X μ t| ^ 3 * exp (t * X ω) ∂μ) / tiltMoment X μ 0 t

/-- ★ **The third cumulant is bounded by the tilted absolute centred third moment.** -/
theorem abs_tiltKappa3_le [IsProbabilityMeasure μ] (ht : t ∈ interior (integrableExpSet X μ)) :
    |tiltKappa3 X μ t| ≤ tiltAbsThird X μ t := by
  rw [tiltKappa3_eq_centred ht, tiltAbsThird, abs_div, abs_of_pos (tiltMoment_zero_pos ht)]
  refine div_le_div_of_nonneg_right ?_ (tiltMoment_zero_pos ht).le
  refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (Eventually.of_forall
    fun ω => ?_)))
  simp only [abs_mul, abs_pow, abs_of_pos (exp_pos _)]

/-! ### Taylor at order two on `[0,1]` -/

theorem cgf_taylor [IsProbabilityMeasure μ] (hs : Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet X μ)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      cgf X μ 1 = μ[X] + variance X μ / 2 + tiltKappa3 X μ u / 6 := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc one_pos
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X μ) := hs ⟨le_rfl, zero_le_one⟩
  have hcont : ContDiffOn ℝ 3 (cgf X μ) (Icc (0 : ℝ) 1) := (analyticOn_cgf.mono hs).contDiffOn hu
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 (cgf X μ) (uIcc (0 : ℝ) 1))
      (uIoo (0 : ℝ) 1) := by
    rw [uIcc_of_lt one_pos, uIoo_of_lt one_pos]
    exact (hcont.differentiableOn_iteratedDerivWithin (mod_cast (by norm_num : (2 : ℕ) < 3))
      hu).mono Ioo_subset_Icc_self
  obtain ⟨u, hu', hTay⟩ := taylor_mean_remainder_lagrange (f := cgf X μ) (x₀ := (0 : ℝ)) (x := 1)
    (n := 2) zero_ne_one (by rw [uIcc_of_lt one_pos]; exact hcont.of_le (by norm_num)) hf'
  rw [uIoo_of_lt one_pos] at hu'
  rw [uIcc_of_lt one_pos] at hTay
  refine ⟨u, hu', ?_⟩
  have hXint : Integrable X μ := by
    have := integrable_tilt h0 1
    simpa using this
  -- the Taylor polynomial: `ℓ(0) + ℓ'(0) + ℓ''(0)/2`
  have hpoly : taylorWithinEval (cgf X μ) 2 (Icc (0 : ℝ) 1) 0 1 = μ[X] + variance X μ / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, sub_zero, one_pow,
      smul_eq_mul, iteratedDerivWithin_zero, zero_add]
    have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hca : ∀ n : ℕ, ContDiffAt ℝ n (cgf X μ) 0 := fun n => (analyticAt_cgf h0).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hca 1) hmem,
      iteratedDerivWithin_eq_iteratedDeriv hu (hca 2) hmem, iteratedDeriv_one, deriv_cgf_zero h0,
      iteratedDeriv_two_cgf_eq_integral h0, cgf_zero, deriv_cgf_zero h0]
    simp only [probReal_univ, div_one, zero_mul, exp_zero, mul_one, mgf_zero]
    rw [variance_eq_integral hXint.aemeasurable]
    push_cast
    ring
  have hthird : iteratedDerivWithin 3 (cgf X μ) (Icc (0 : ℝ) 1) u = tiltKappa3 X μ u := by
    have hu'' : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu'
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (analyticAt_cgf (hs hu'')).contDiffAt hu'',
      iteratedDeriv_three_cgf (hs hu'')]
  rw [hpoly, hthird] at hTay
  have h3 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at hTay
  linarith

/-! ### The predictive remainder -/

/-- The predictive remainder `R = ℓ(1) − μ[X] − Var(X)/2`. -/
noncomputable def predictiveRemainder (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  cgf X μ 1 - μ[X] - variance X μ / 2

/-- ★★ **The predictive remainder is bounded by the tilted absolute centred third moments**:
`|R| ≤ S/6` when `μ_t[|X − ⟨X⟩_t|³] ≤ S` for all `t ∈ [0,1]`. -/
theorem abs_predictiveRemainder_le [IsProbabilityMeasure μ]
    (hs : Icc (0 : ℝ) 1 ⊆ interior (integrableExpSet X μ)) {S : ℝ}
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, tiltAbsThird X μ t ≤ S) :
    |predictiveRemainder X μ| ≤ S / 6 := by
  obtain ⟨u, hu, hT⟩ := cgf_taylor hs
  have hR : predictiveRemainder X μ = tiltKappa3 X μ u / 6 := by
    unfold predictiveRemainder
    linarith
  rw [hR, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  gcongr
  exact (abs_tiltKappa3_le (hs (Ioo_subset_Icc_self hu))).trans (hS u (Ioo_subset_Icc_self hu))

/-- With `X = −f`: `−ℓ(1) = ⟨f⟩ − Var(f)/2 − R` where `ℓ(1) = log μ[e^{−f}]`. -/
theorem neg_log_integral_exp_neg_eq [IsProbabilityMeasure μ] {f : Ω → ℝ} :
    -Real.log (∫ ω, exp (-f ω) ∂μ) =
      μ[f] - variance f μ / 2 - predictiveRemainder (fun ω => -f ω) μ := by
  have h1 : cgf (fun ω => -f ω) μ 1 = Real.log (∫ ω, exp (-f ω) ∂μ) := by
    simp [cgf, mgf]
  have h2 : ∫ ω, -f ω ∂μ = -∫ ω, f ω ∂μ := integral_neg f
  have h3 : variance (fun ω => -f ω) μ = variance f μ := by
    simp only [variance, evariance, integral_neg]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [show -f ω - -∫ a, f a ∂μ = -(f ω - ∫ a, f a ∂μ) by ring, enorm_neg]
  unfold predictiveRemainder
  rw [h1, h2, h3]
  ring

/-- ★★ **The annealed remainder estimate**: if `|R_n(ω)| ≤ S_n(ω)/6` and `n·𝔼S_n → 0`, then
`n·𝔼|R_n| → 0`. -/
theorem tendsto_mul_integral_abs_remainder {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {R S : ℕ → Ω' → ℝ} (hRm : ∀ n, AEStronglyMeasurable (R n) P)
    (hSint : ∀ n, Integrable (S n) P) (hRS : ∀ n ω, |R n ω| ≤ S n ω / 6)
    (hS : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, S n ω ∂P) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, |R n ω| ∂P) atTop (𝓝 0) := by
  have hRint : ∀ n, Integrable (fun ω => |R n ω|) P := fun n =>
    ((hSint n).div_const 6).mono' (hRm n).norm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]
      exact hRS n ω)
  have hS0 : ∀ n ω, 0 ≤ S n ω := fun n ω => by linarith [abs_nonneg (R n ω), hRS n ω]
  refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n)
    (integral_nonneg fun ω => abs_nonneg _)) (fun n => ?_) hS
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  calc ∫ ω, |R n ω| ∂P ≤ ∫ ω, S n ω / 6 ∂P :=
        integral_mono (hRint n) ((hSint n).div_const 6) fun ω => hRS n ω
    _ ≤ ∫ ω, S n ω ∂P := by
        rw [integral_div]
        have : 0 ≤ ∫ ω, S n ω ∂P := integral_nonneg fun ω => hS0 n ω
        linarith [div_le_self this (by norm_num : (1 : ℝ) ≤ 6)]

end Grammar
```

### E. The two new propositions of the note (tex)
```latex

\begin{prop}[Finite-resolution quartet expectation transfer]\label{prop:finite_transfer}
Fix the finite-resolution data (positive weights $\rho_i$, covariance $b=AA^{\mathsf T}$ with constant diagonal $c$) and $\beta,\lambda>0$. Let $g_n$ be empirical phase vectors converging in distribution to $G\sim N(0,b)$ with uniformly bounded moments of every order. Then for every continuous polynomially bounded observable $F$ the expectations converge, $\mathbb EF(g_n)\to\mathbb EF(G)$⟦dot⟧; in particular the expectations of $W_i$, $M_2$, $H$, $V$ and $\log D$ converge to their Gaussian values⟦dot⟧, and the four Bayes combinations $M_2$, $M_2-H$, $M_2-V/2$, $M_2-H-V/2$ converge to $\lambda/\beta+\nu$, $\lambda/\beta-\nu$, $(\lambda-\nu)/\beta+\nu$, $(\lambda-\nu)/\beta-\nu$ with $\nu=\mathbb EH(G)/2$⟦dot⟧. No raw-evidence threshold $\beta\kappa<2$ enters: the self-normalised observables are polynomially bounded for every $\beta>0$. If moreover $B_{n,j}$ are integrable observables with $\mathbb E|B_{n,j}-\mathcal Q_j(g_n)|\to0$ ($L^1$ observable transfer), then $\mathbb EB_{n,j}$ converges to the corresponding Bayes value⟦dot⟧.
\end{prop}

The proposition isolates what the expected-error formulas still need at finite resolution: the $L^1$ transfer of the \emph{actual} scaled normalised observables to the quartet at the empirical phase (not merely convergence in probability, which would additionally require uniform integrability of the $B_{n,j}$), and the predictive remainder estimate; the uniform moments of the empirical phase vectors follow from a uniform sub-Gaussian proxy but this bridge is not formalised.

\begin{prop}[The predictive remainder]\label{prop:predictive_remainder}
Let $\Pi$ be a probability measure (a posterior) and $X$ an observable ($X=-f$ for a loss $f$) whose exponential moments exist on a neighbourhood of $[0,1]$, and write $\ell(t)=\log\Pi[e^{tX}]$ for the log-normaliser and $\Pi_t\propto e^{tX}\Pi$ for the tilted law. Then $\ell^{(3)}(t)$ is the third cumulant of $\Pi_t$, the tilted centred third moment $\Pi_t[(X-\langle X\rangle_t)^3]$⟦dot⟧⟦dot⟧, and $\ell(1)=\Pi[X]+\tfrac12\operatorname{Var}_\Pi(X)+\tfrac16\ell^{(3)}(u)$ for some $u\in(0,1)$⟦dot⟧. Hence the predictive remainder $R=\ell(1)-\Pi[X]-\tfrac12\operatorname{Var}_\Pi(X)$ satisfies $|R|\le S/6$ whenever $\Pi_t[|X-\langle X\rangle_t|^3]\le S$ for all $t\in[0,1]$⟦dot⟧; with $X=-f$ this reads $-\log\Pi[e^{-f}]=\langle f\rangle-\tfrac12\operatorname{Var}(f)-R$⟦dot⟧, and if $|R_n|\le S_n/6$ pathwise with $n\,\mathbb ES_n\to0$ then $n\,\mathbb E|R_n|\to0$⟦dot⟧.
\end{prop}

The proposition reduces the predictive-remainder input of the expected-error formulas to a certificate on the tilted absolute centred third moments of the loss under the posterior, uniformly over the tilt; its discharge in a statistical model (a bound $n\,\mathbb E\sup_{t\in[0,1]}\Pi_{n,t}[|f-\langle f\rangle_t|^3]\to0$) is not formalised. For training error the data expectation is the empirical average over the observed sample, not a fresh test point.

\subsection{Interfaces}\label{subsec:interfaces}

The following table records, for each formal interface, what is supplied as hypothesis, what is proved, and what is not supplied.
```

### F. The normal-location example declarations (EffectiveTemperature.lean)
```lean
41:theorem dataPhase_eq_zero_of_xiCoord_eq_zero {d : ℕ} (A : DataSpace d) (hA : xiCoord A = 0) :
51:theorem dataBoxCoeff_leading_zero_phase (A : DataSpace (n + 1)) (hA : xiCoord A = 0) :
80:theorem integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance
115:theorem sum_normalLocation (n : ℕ) (a : ℝ) (x : ℕ → ℝ) :
122:theorem normalLocation_standard_form (a x : ℝ) :
131:theorem neg_zetaEmp_normalLocation (n : ℕ) (a : ℝ) (x : ℕ → ℝ) :
140:theorem variance_phase_normalLocation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
```
