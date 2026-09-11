/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.GlobalExponentHironaka
import Grammar.HironakaUnconditional

/-!
# The resolution formula is the Laplace exponent pair of the small balls

hironaka's chart form gives, for `K ≥ 0` analytic near a zero `w` and not identically zero there,
a pair `(λ_H, θ_H)` with `∫_{B̄(w,r)} e^{−NK} = Θ(N^{−λ_H}(log N)^{θ_H−1})` for every small `r`
(`laplaceTheta_of_analyticOnNhd_nonneg`, CLXXXV) — the population Laplace exponent pair of `K` at
`w`, without identification. The resolution theorem `exponent_of_analytic` (CCVIII) gives, for some
compact neighbourhood `Ω` of `w` inside a small ball and any positive analytic observable `F`,
`∫_Ω F e^{−NK} = Θ(N^{−λ_*}(log N)^{m_*−1})` with `(λ_*, m_*)` the extremal divisor-point chart
pair of a monomial resolution. Sandwiching `∫_Ω F e^{−NK}` between constant multiples of the
integrals over a small ball inside `Ω` and the ball containing `Ω`, both of the hironaka order, and
using the uniqueness of power–log orders (`powerLogRate_pair_eq_of_isTheta_nat`), the two pairs
coincide: **`(λ_H, θ_H − 1) = (λ_*, m_* − 1)`** (`laplace_pair_eq_resolution_pair`). In particular
the extremal chart pair does not depend on the resolution, the finite cover or the observable, and
the small-ball Laplace exponent of `K` at `w` is the minimum over divisor points of the charts of
`min_j (h_{n_j}+1)/(2k_j)`, with multiplicity the maximal number of minimisers.

Non-claims: the identification is with hironaka's small-ball pair for the pure Laplace integral;
the region `Ω` is one compact neighbourhood (every sufficiently small ball has the same pair by
hironaka's theorem, so the pair is the germ invariant at `w`, but a general region containing other
zeros of `K` may have a different pair); leading order only.
-/

open MeasureTheory Set Filter Topology Asymptotics Monomialize.VolumeScaling

namespace Grammar

/-! ### Θ-sandwich and uniqueness of the pair along the reals -/

/-- A function squeezed between two functions of the same order (all eventually nonnegative) has
that order. -/
theorem isTheta_of_le_of_le {f g h φ : ℝ → ℝ} (hfg : ∀ᶠ N in atTop, f N ≤ g N)
    (hgh : ∀ᶠ N in atTop, g N ≤ h N) (hf0 : ∀ᶠ N in atTop, 0 ≤ f N) (hfΘ : f =Θ[atTop] φ)
    (hhΘ : h =Θ[atTop] φ) : g =Θ[atTop] φ := by
  refine ⟨(IsBigO.of_bound 1 ?_).trans hhΘ.1, hfΘ.2.trans (IsBigO.of_bound 1 ?_)⟩
  · filter_upwards [hfg, hgh, hf0] with N h1 h2 h3
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h3.trans h1),
      abs_of_nonneg ((h3.trans h1).trans h2)]
    exact h2
  · filter_upwards [hfg, hf0] with N h1 h3
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3, abs_of_nonneg (h3.trans h1)]
    exact h1

/-- **Uniqueness of the power–log pair** along the reals. -/
theorem pair_eq_of_powLogScale_isTheta {l l' : ℝ} {r r' : ℕ}
    (h : powLogScale l r =Θ[atTop] powLogScale l' r') : l = l' ∧ r = r' := by
  have h1 : (fun n : ℕ => powerLogRate l r n) =O[atTop] fun n : ℕ => powerLogRate l' r' n :=
    h.1.comp_tendsto tendsto_natCast_atTop_atTop
  have h2 : (fun n : ℕ => powerLogRate l' r' n) =O[atTop] fun n : ℕ => powerLogRate l r n :=
    h.2.comp_tendsto tendsto_natCast_atTop_atTop
  exact powerLogRate_pair_eq_of_isTheta_nat ⟨h1, h2⟩

/-! ### The identification -/

variable {d : ℕ}

/-- **The small-ball Laplace exponent pair is the resolution pair.** For `K ≥ 0` analytic on an
open `U ∋ w`, `K w = 0`, `K` not identically zero near `w`, `K` measurable, and `F > 0` analytic
on `U`: hironaka's pair `(λ_H, θ_H)` of the small balls
(`∫_{B̄(w,r)} e^{−NK} ≍ N^{−λ_H}(log N)^{θ_H−1}` for all `0 < r ≤ r₀`) and the resolution data of
`exponent_of_analytic` — a monomial resolution
`R`, a compact neighbourhood `Ω ⊆ B̄(w,r₀) ∩ U` of `w`, finitely many divisor-point chart pairs with
extremal pair `(λ_*, m_*)` and `∫_Ω F e^{−NK} ≍ N^{−λ_*}(log N)^{m_*−1}` — satisfy
`λ_* = λ_H` and `m_* − 1 = θ_H − 1`. -/
theorem laplace_pair_eq_resolution_pair {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    {w : Fin d → ℝ} (hw : w ∈ U) (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x) :
    ∃ (lamH : ℚ) (thetaH : ℕ) (r₀ : ℝ), 0 < lamH ∧ 1 ≤ thetaH ∧ thetaH ≤ d ∧ 0 < r₀ ∧
      (∀ r : ℝ, 0 < r → r ≤ r₀ →
        LaplaceTheta ((volume : Measure (Fin d → ℝ)).restrict (Metric.closedBall w r)) K
          (lamH : ℝ) (thetaH - 1)) ∧
      ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
        ∃ Rg : Set (Fin d → ℝ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ Metric.closedBall w r₀ ∧ Rg ⊆ U ∧
          ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
            (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
              (C : CentredChartData K (R.φ i) h y₀),
              y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
            (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
            regionIntegral volume Rg F K =Θ[atTop] powLogScale (lam i₀) (m i₀ - 1) ∧
            lam i₀ = lamH ∧ m i₀ - 1 = thetaH - 1 := by
  -- hironaka's pair on the small balls
  have hK0ev : ∀ᶠ x in 𝓝 w, 0 ≤ K x := Filter.eventually_of_mem (hU.mem_nhds hw) hK0
  obtain ⟨lamH, thetaH, r₀', hlam, h1, hd, hr₀', hLT⟩ :=
    laplaceTheta_of_analyticOnNhd_nonneg hU hK hw hKw hne hK0ev
  -- a radius inside `U`
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hw)
  set r₀ : ℝ := min r₀' (rU / 2) with hr₀def
  have hr₀ : 0 < r₀ := lt_min hr₀' (half_pos hrU)
  have hr₀le : r₀ ≤ r₀' := min_le_left _ _
  have hcballU : Metric.closedBall w r₀ ⊆ U :=
    (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hrU))).trans
      hballU
  -- the resolution data inside the ball of radius `r₀`
  obtain ⟨N, R, hR, Rg, hRgc, hRgn, hRgball, hRgU, ι, hι, lam, m, i₀, hpieces, hmin, hmax, hΘ⟩ :=
    exponent_of_analytic hU hK hK0 hKm hw hKw hne hF hFpos hr₀
  refine ⟨lamH, thetaH, r₀, hlam, h1, hd, hr₀, fun r hr hrr₀ => hLT r hr (hrr₀.trans hr₀le), N, R,
    hR, Rg, hRgc, hRgn, hRgball, hRgU, ι, hι, lam, m, i₀, hpieces, hmin, hmax, hΘ, ?_⟩
  -- a small closed ball inside the region
  obtain ⟨ρ, hρ, hρRg⟩ := Metric.mem_nhds_iff.1 hRgn
  set ρ' : ℝ := min (ρ / 2) r₀ with hρ'def
  have hρ' : 0 < ρ' := lt_min (half_pos hρ) hr₀
  have hρ'Rg : Metric.closedBall w ρ' ⊆ Rg :=
    (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ))).trans hρRg
  -- bounds of `F` on the compact region
  have hFc : ContinuousOn F Rg := hF.continuousOn.mono hRgU
  have hRgne : Rg.Nonempty := ⟨w, mem_of_mem_nhds hRgn⟩
  obtain ⟨xmin, hxmin, hmin'⟩ := hRgc.exists_isMinOn hRgne hFc
  obtain ⟨xmax, hxmax, hmax'⟩ := hRgc.exists_isMaxOn hRgne hFc
  set c₁ := F xmin with hc₁
  set c₂ := F xmax with hc₂
  have hc₁pos : 0 < c₁ := hFpos _ (hRgU hxmin)
  have hc₂pos : 0 < c₂ := hFpos _ (hRgU hxmax)
  -- the pure Laplace integrals
  set Z : Set (Fin d → ℝ) → ℝ → ℝ := fun S N => ∫ x in S, Real.exp (-N * K x) with hZ
  have hKc : ContinuousOn K U := hK.continuousOn
  have hexpc : ∀ (S : Set (Fin d → ℝ)), S ⊆ U → ∀ N : ℝ,
      ContinuousOn (fun x => Real.exp (-N * K x)) S := fun S hSU N =>
    Real.continuous_exp.comp_continuousOn ((hKc.mono hSU).const_smul (-N))
  have hZint : ∀ S, IsCompact S → S ⊆ U → ∀ N : ℝ,
      IntegrableOn (fun x => Real.exp (-N * K x)) S := fun S hS hSU N =>
    (hexpc S hSU N).integrableOn_compact hS
  have hFKint : ∀ N : ℝ, IntegrableOn (fun x => F x * Real.exp (-N * K x)) Rg := fun N =>
    (hFc.mul (hexpc Rg hRgU N)).integrableOn_compact hRgc
  have hZnn : ∀ S N, 0 ≤ Z S N := fun S N =>
    setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x => (Real.exp_pos _).le)
  have hRgm : MeasurableSet Rg := hRgc.isClosed.measurableSet
  -- the sandwich `c₁ Z(B̄(w,ρ')) ≤ ∫_Rg F e^{−NK} ≤ c₂ Z(B̄(w,r₀))`
  have hlow : ∀ N : ℝ, c₁ * Z (Metric.closedBall w ρ') N ≤ regionIntegral volume Rg F K N := by
    intro N
    have h1 : Z (Metric.closedBall w ρ') N ≤ Z Rg N :=
      setIntegral_mono_set (hZint Rg hRgc hRgU N)
        (Eventually.of_forall fun x => (Real.exp_pos _).le) (Eventually.of_forall hρ'Rg)
    have h2 : c₁ * Z Rg N ≤ regionIntegral volume Rg F K N := by
      simp only [hZ, regionIntegral]
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((hZint Rg hRgc hRgU N).const_mul _) (hFKint N) hRgm
        fun x hx => ?_
      exact mul_le_mul_of_nonneg_right (hmin' hx) (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_left h1 hc₁pos.le).trans h2
  have hup : ∀ N : ℝ, regionIntegral volume Rg F K N ≤ c₂ * Z (Metric.closedBall w r₀) N := by
    intro N
    have h1 : Z Rg N ≤ Z (Metric.closedBall w r₀) N :=
      setIntegral_mono_set (hZint _ (isCompact_closedBall _ _) hcballU N)
        (Eventually.of_forall fun x => (Real.exp_pos _).le) (Eventually.of_forall hRgball)
    have h2 : regionIntegral volume Rg F K N ≤ c₂ * Z Rg N := by
      simp only [hZ, regionIntegral]
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFKint N) ((hZint Rg hRgc hRgU N).const_mul _) hRgm
        fun x hx => ?_
      exact mul_le_mul_of_nonneg_right (hmax' hx) (Real.exp_pos _).le
    exact h2.trans (mul_le_mul_of_nonneg_left h1 hc₂pos.le)
  -- both bounds have hironaka's order
  have hΘlow : (fun N => c₁ * Z (Metric.closedBall w ρ') N) =Θ[atTop]
      powerLogRate (lamH : ℝ) (thetaH - 1) :=
    (hLT ρ' hρ' ((min_le_right _ _).trans hr₀le)).const_mul_left hc₁pos.ne'
  have hΘup : (fun N => c₂ * Z (Metric.closedBall w r₀) N) =Θ[atTop]
      powerLogRate (lamH : ℝ) (thetaH - 1) :=
    (hLT r₀ hr₀ hr₀le).const_mul_left hc₂pos.ne'
  have hΘF : regionIntegral volume Rg F K =Θ[atTop] powerLogRate (lamH : ℝ) (thetaH - 1) :=
    isTheta_of_le_of_le (Eventually.of_forall hlow) (Eventually.of_forall hup)
      (Eventually.of_forall fun N => mul_nonneg hc₁pos.le (hZnn _ N)) hΘlow hΘup
  have hpair : powLogScale (lam i₀) (m i₀ - 1) =Θ[atTop] powLogScale (lamH : ℝ) (thetaH - 1) :=
    hΘ.symm.trans hΘF
  exact pair_eq_of_powLogScale_isTheta hpair

/-! ### The resolution pair in the population and empirical exponent theorems -/

/-- **The resolution pair is the exponent of every certified population core theorem on the small
balls, and the empirical exponent.** For `K ≥ 0` analytic on an open `U ∋ w`, `K w = 0`, `K` not
identically zero near `w`, `K` measurable: there are a monomial resolution `R` of `K` near `w`,
finitely many divisor-point chart pairs with extremal pair `(λ_*, m_*)`, and `r₀ > 0` such that on
every ball `B̄(w,r)`, `0 < r ≤ r₀`, (i) a certified population core theorem
`A_k ∫_{B̄(w,r)} e^{−kK} → L₀ > 0` at the pair `(λ, m)` forces `λ = λ_*` and `m − 1 = m_* − 1`;
(ii) if moreover the scaled empirical evidence converges in distribution to an almost surely
positive limit at that pair, then `log Z_k^{emp}/log k → −λ_*` in probability. -/
theorem resolution_pair_of_population_comparison {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K)
    {w : Fin d → ℝ} (hw : w ∈ U) (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
      ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
        (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
        (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
          ∀ (lam' : ℝ) (m' : ℕ) (L₀ : ℝ), 0 < L₀ →
            Tendsto (fun k : ℕ => scaleA lam' m' k *
              ∫ x in Metric.closedBall w r, Real.exp (-(k : ℝ) * K x)) atTop (𝓝 L₀) →
            (lam' = lam i₀ ∧ m' - 1 = m i₀ - 1) ∧
            ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
              {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
              {Z : ℕ → Ω → ℝ} {L : Ω' → ℝ},
              TendstoInDistribution (fun k ω => scaleA lam' m' k * Z k ω) atTop L (fun _ => μ) μ' →
              (∀ k ω, 0 < Z k ω) → (∀ᵐ ω ∂μ', 0 < L ω) →
              TendstoInMeasure μ (fun k ω => Real.log (Z k ω) / Real.log k) atTop
                (fun _ => -lam i₀) := by
  -- the identification with the observable `F = 1`
  obtain ⟨lamH, thetaH, r₀, -, -, -, hr₀, hLT, N, R, hR, -, -, -, -, -, ι, hι, lam, m, i₀, hpieces,
    hmin, hmax, -, hlamEq, hmEq⟩ :=
    laplace_pair_eq_resolution_pair hU hK hK0 hKm hw hKw hne (F := fun _ => (1 : ℝ))
      analyticOnNhd_const (fun _ _ => one_pos)
  refine ⟨N, R, hR, ι, hι, lam, m, i₀, hpieces, hmin, hmax, r₀, hr₀, fun r hr hrr₀ lam' m' L₀ hL₀
    hconv => ?_⟩
  have hcmp := exponentPair_eq_of_population_comparison (hLT r hr hrr₀) lam' m' hL₀ hconv
  have hlam' : lam' = lam i₀ := hcmp.1.trans hlamEq.symm
  refine ⟨⟨hlam', hcmp.2.trans hmEq.symm⟩, ?_⟩
  intro Ω _ μ _ Ω' _ μ' _ Z L hdist hZpos hLpos
  exact tendstoInMeasure_log_div_log_of_population_comparison m' hlam' hdist hZpos hLpos

/-! ### The free energy of the region integral -/

/-- The region integral of a positive continuous observable over a compact neighbourhood is
positive. -/
theorem regionIntegral_pos_of_mem_nhds {U : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ}
    (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} {F : (Fin d → ℝ) → ℝ} (hF : AnalyticOnNhd ℝ F U)
    (hFpos : ∀ x ∈ U, 0 < F x) {Rg : Set (Fin d → ℝ)} (hRgc : IsCompact Rg) (hRgn : Rg ∈ 𝓝 w)
    (hRgU : Rg ⊆ U) (N : ℝ) : 0 < regionIntegral volume Rg F K N := by
  have hint : IntegrableOn (fun x => F x * Real.exp (-N * K x)) Rg :=
    ((hF.continuousOn.mono hRgU).mul (Real.continuous_exp.comp_continuousOn
      ((hK.continuousOn.mono hRgU).const_smul (-N)))).integrableOn_compact hRgc
  have hnn : 0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict Rg]
      fun x => F x * Real.exp (-N * K x) :=
    ae_restrict_of_forall_mem hRgc.isClosed.measurableSet fun x hx =>
      mul_nonneg (hFpos x (hRgU hx)).le (Real.exp_pos _).le
  rw [regionIntegral, setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hRgn
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume w hρ) (measure_mono fun x hx => ?_)
  exact ⟨(mul_pos (hFpos x (hRgU (hball hx))) (Real.exp_pos _)).ne', hball hx⟩

/-- **The free energy of the Laplace integral near a zero, unconditionally**:
`−log ∫_Ω F e^{−NK} = λ_* log N − (m_* − 1) log log N + O(1)` with `(λ_*, m_*)` the resolution
pair (the extremal divisor-point chart pair, equal to hironaka's small-ball pair). -/
theorem freeEnergy_of_analytic {U : Set (Fin d → ℝ)} (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ}
    (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K) {w : Fin d → ℝ}
    (hw : w ∈ U) (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) {F : (Fin d → ℝ) → ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hFpos : ∀ x ∈ U, 0 < F x) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
      ∃ Rg : Set (Fin d → ℝ), IsCompact Rg ∧ Rg ∈ 𝓝 w ∧ Rg ⊆ Metric.closedBall w ρ₀ ∧ Rg ⊆ U ∧
        ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
          (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ)
            (C : CentredChartData K (R.φ i) h y₀),
            y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
          (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
          (fun N => -Real.log (regionIntegral volume Rg F K N) -
            (lam i₀ * Real.log N - ((m i₀ - 1 : ℕ) : ℝ) * Real.log (Real.log N))) =O[atTop]
            fun _ : ℝ => (1 : ℝ) := by
  obtain ⟨N, R, hR, Rg, hRgc, hRgn, hRgball, hRgU, ι, hι, lam, m, i₀, hpieces, hmin, hmax, hΘ⟩ :=
    exponent_of_analytic hU hK hK0 hKm hw hKw hne hF hFpos hρ₀
  refine ⟨N, R, hR, Rg, hRgc, hRgn, hRgball, hRgU, ι, hι, lam, m, i₀, hpieces, hmin, hmax, ?_⟩
  exact freeEnergy_asymptotic (Eventually.of_forall fun N =>
    regionIntegral_pos_of_mem_nhds hK hF hFpos hRgc hRgn hRgU N) hΘ

/-! ### Intrinsic properties of the resolution pair -/

theorem CentredChartData.one_le_mult {K : (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → (Fin d → ℝ)}
    {h : Fin d →₀ ℕ} {y₀ : Fin d → ℝ} (C : CentredChartData K φ h y₀) : 1 ≤ C.mult :=
  multCount_pos _ _ C.exists_ratioExp_eq_lam

/-- **The resolution pair is intrinsic**: `λ_*` is a positive rational, `1 ≤ m_* ≤ d`, and every
sufficiently small closed ball around `w`, weighted by any continuous positive observable, has the
Laplace order `N^{−λ_*}(log N)^{m_*−1}`. -/
theorem resolution_pair_intrinsic {U : Set (Fin d → ℝ)} (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ}
    (hK : AnalyticOnNhd ℝ K U) (hK0 : ∀ x ∈ U, 0 ≤ K x) (hKm : Measurable K) {w : Fin d → ℝ}
    (hw : w ∈ U) (hKw : K w = 0) (hne : ¬ K =ᶠ[𝓝 w] 0) :
    ∃ (N : Set (Fin d → ℝ)) (R : PartialResolution d K N), R.IsMonomial ∧
      ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (m : ι → ℕ) (i₀ : ι),
        (∀ p, ∃ (i : R.ι) (y₀ : Fin d → ℝ) (h : Fin d →₀ ℕ) (C : CentredChartData K (R.φ i) h y₀),
          y₀ ∈ R.dom i ∧ K (R.φ i y₀) = 0 ∧ lam p = C.lam ∧ m p = C.mult) ∧
        (∀ p, lam i₀ ≤ lam p) ∧ (∀ p, lam p = lam i₀ → m p ≤ m i₀) ∧
        (∃ q : ℚ, lam i₀ = q) ∧ 0 < lam i₀ ∧ 1 ≤ m i₀ ∧ m i₀ ≤ d ∧
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
          ∀ F : (Fin d → ℝ) → ℝ, ContinuousOn F (Metric.closedBall w r) →
            (∀ x ∈ Metric.closedBall w r, 0 < F x) →
            regionIntegral volume (Metric.closedBall w r) F K =Θ[atTop]
              powLogScale (lam i₀) (m i₀ - 1) := by
  obtain ⟨lamH, thetaH, r₀, hlam, h1, hd, hr₀, hLT, N, R, hR, -, -, -, -, -, ι, hι, lam, m, i₀,
    hpieces, hmin, hmax, -, hlamEq, hmEq⟩ :=
    laplace_pair_eq_resolution_pair hU hK hK0 hKm hw hKw hne (F := fun _ => (1 : ℝ))
      analyticOnNhd_const (fun _ _ => one_pos)
  -- `1 ≤ m_*`
  have hm1 : 1 ≤ m i₀ := by
    obtain ⟨_, _, _, C, -, -, -, hmC⟩ := hpieces i₀
    rw [hmC]
    exact C.one_le_mult
  -- a radius inside `U`
  obtain ⟨rU, hrU, hballU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hw)
  set r₁ : ℝ := min r₀ (rU / 2) with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr₀ (half_pos hrU)
  refine ⟨N, R, hR, ι, hι, lam, m, i₀, hpieces, hmin, hmax, ⟨lamH, hlamEq⟩,
    hlamEq ▸ (by exact_mod_cast hlam), hm1, by omega, r₁, hr₁, fun r hr hrr₁ F hFc hFpos => ?_⟩
  have hrU' : Metric.closedBall w r ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hballU
    exact lt_of_le_of_lt (hrr₁.trans (min_le_right _ _)) (half_lt_self hrU)
  have hBc : IsCompact (Metric.closedBall w r) := isCompact_closedBall _ _
  have hBne : (Metric.closedBall w r).Nonempty := ⟨w, Metric.mem_closedBall_self hr.le⟩
  obtain ⟨xmin, hxmin, hmin'⟩ := hBc.exists_isMinOn hBne hFc
  obtain ⟨xmax, hxmax, hmax'⟩ := hBc.exists_isMaxOn hBne hFc
  have hc₁pos : 0 < F xmin := hFpos _ hxmin
  have hc₂pos : 0 < F xmax := hFpos _ hxmax
  have hKc : ContinuousOn K (Metric.closedBall w r) := hK.continuousOn.mono hrU'
  have hZint : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N * K x)) (Metric.closedBall w r) :=
    fun N => (Real.continuous_exp.comp_continuousOn (hKc.const_smul (-N))).integrableOn_compact hBc
  have hFKint : ∀ N : ℝ,
      IntegrableOn (fun x => F x * Real.exp (-N * K x)) (Metric.closedBall w r) := fun N =>
    (hFc.mul (Real.continuous_exp.comp_continuousOn (hKc.const_smul (-N)))).integrableOn_compact
      hBc
  have hBm : MeasurableSet (Metric.closedBall w r) := Metric.isClosed_closedBall.measurableSet
  set Z : ℝ → ℝ := fun N => ∫ x in Metric.closedBall w r, Real.exp (-N * K x) with hZ
  have hlow : ∀ N : ℝ, F xmin * Z N ≤ regionIntegral volume (Metric.closedBall w r) F K N := by
    intro N
    simp only [hZ, regionIntegral]
    rw [← integral_const_mul]
    exact setIntegral_mono_on ((hZint N).const_mul _) (hFKint N) hBm fun x hx =>
      mul_le_mul_of_nonneg_right (hmin' hx) (Real.exp_pos _).le
  have hup : ∀ N : ℝ, regionIntegral volume (Metric.closedBall w r) F K N ≤ F xmax * Z N := by
    intro N
    simp only [hZ, regionIntegral]
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hFKint N) ((hZint N).const_mul _) hBm fun x hx =>
      mul_le_mul_of_nonneg_right (hmax' hx) (Real.exp_pos _).le
  have hZnn : ∀ N, 0 ≤ Z N := fun N =>
    setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x => (Real.exp_pos _).le)
  have hΘZ : Z =Θ[atTop] powerLogRate (lamH : ℝ) (thetaH - 1) :=
    hLT r hr (hrr₁.trans (min_le_left _ _))
  have hΘF : regionIntegral volume (Metric.closedBall w r) F K =Θ[atTop]
      powerLogRate (lamH : ℝ) (thetaH - 1) :=
    isTheta_of_le_of_le (Eventually.of_forall hlow) (Eventually.of_forall hup)
      (Eventually.of_forall fun N => mul_nonneg hc₁pos.le (hZnn N))
      (hΘZ.const_mul_left hc₁pos.ne') (hΘZ.const_mul_left hc₂pos.ne')
  rw [hlamEq, hmEq]
  exact hΘF

end Grammar
