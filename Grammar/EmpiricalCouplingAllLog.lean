/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CoupledPolarInterchange

/-!
# The empirical all-log formula in coupling-average form (route B, unit B13b)

The integrated polar coefficients of unit B12 are rearranged into the coupling average of the
population polar coefficients of the tilted amplitudes `η e^{√t ζ}` (Astra #168, (B4)):

  ★★★ `empIntegratedPolarCoeff_eq_couplingPolarCoeff`:
  `empIntegratedPolarCoeff p η ζ h k μ q
     = Σ_{j ∈ Ico q d} ((j−q)!)⁻¹ ∫_0^∞ t^{μ−1} (log t)^{j−q} e^{−t}
         chartPolarCoeff p (η e^{√t ζ}) h k μ j dt`

(`couplingPolarCoeff`), hence (B12) for lattice points `0 < μ < L`, `q ≤ d − 1`,

  ★★★ `ofReal_empCoeff_eq_couplingPolarCoeff`:
  `empCoeff η ζ h k μ q = (−1)^{q+1}/q! · couplingPolarCoeff (depthOf h k L) η ζ h k μ q`.

The proof is the normalised Taylor-coefficient convolution: per face `x = (J, m)` with holomorphic
factors `R_x = regularFactor` and `Φ_x = coupledFaceZeta`, the Taylor coefficients of `Φ_x` at `μ`
are the binomially split log moments (unit B13a and the derivative identity of unit B9), those of
`R_x · Φ_x` and of `R_x · ζ_{x,t}` (`ζ_{x,t} = chartZeta (faceAmp p J (η e^{√tζ}) m)`) are Cauchy
products (`taylorCoeff_mul`), so that

  `taylorCoeff (R_x Φ_x) μ n
     = Σ_{a ≤ n} (a!)⁻¹ ∫_0^∞ t^{μ−1}e^{−t}(log t)^a taylorCoeff (R_x ζ_{x,t}) μ (n−a) dt`

(`taylorCoeff_empFaceHolo_eq`), and the face sum with `n = c_x − 1 − q` regroups over `j = q + a`
into the population coefficients `chartPolarCoeff … j` inside the `t`-integral.  For `ζ = 0` the
inner coefficient is `t`-independent and the `t`-integrals are `Γ^{(j−q)}(μ)`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff Nat

namespace Grammar

open SmoothEngine

variable {d : ℕ}

section Face

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-! ### Taylor coefficients of the face factors -/

/-- The Taylor coefficients of a coupled face zeta function are the split log moments. -/
theorem taylorCoeff_coupledFaceZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (n : ℕ) :
    taylorCoeff (coupledFaceZeta p η ζ h k J m) μ n = ∑ a ∈ range (n + 1),
      ((a ! : ℂ)⁻¹ * ((n - a)! : ℂ)⁻¹) *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
          chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
            (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - a) μ := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  unfold taylorCoeff coupledFaceZeta
  rw [iteratedDeriv_coupledChartZeta hcont hC (hflat J m hm) _ _ n hμ0' hμ',
    coupledLogMoment_eq_sum hcont hC (hflat J m hm) _ _ n hμ0' hμ', Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have han : a ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  have hfac : (n.choose a : ℂ) * (a ! : ℂ) * ((n - a)! : ℂ) = (n ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial han
  have ha0 : (a ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hna0 : ((n - a)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - a)
  have hn0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hch : (n.choose a : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos han).ne'
  rw [← hfac]
  field_simp

/-- The Taylor coefficients of the chart zeta function of a tilted face amplitude are its box
log moments. -/
theorem taylorCoeff_chartZeta_faceAmp (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) (n : ℕ) :
    taylorCoeff (chartZeta (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
      (fun i : {i // ¬ inJ J i} => h i) (fun i => k i)) μ n =
      chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
        (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) n μ / (n ! : ℂ) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hτ : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hC' : 0 ≤ C * (1 + Real.sqrt t) ^ (∑ i, p i) * Real.exp (M * Real.sqrt t) := by positivity
  unfold taylorCoeff
  rw [iteratedDeriv_chartZeta_eq_logMoment
    (continuous_faceAmp p J (contDiff_fieldFam hη hζ _) m).continuousOn hC'
    (hflat J m hm _ hτ) _ _ n (flatStrip_subtype J hμ)]

theorem analyticAt_regularFactor (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) {μ : ℝ}
    (hμ : FlatStrip p h k (μ : ℂ)) : AnalyticAt ℂ (regularFactor h k J m μ) (μ : ℂ) :=
  (differentiableOn_regularFactor h k J m μ fun _ hs => hs.2).analyticAt
    (faceRegSet_mem_nhds p h k J m hμ)

theorem analyticAt_coupledFaceZeta (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) : AnalyticAt ℂ (coupledFaceZeta p η ζ h k J m) (μ : ℂ) :=
  (differentiableOn_coupledFaceZeta hη hζ p hp0 h k J hm).analyticAt
    ((isOpen_posFlatStrip p h k).mem_nhds ⟨by simpa using hμ0, hμ⟩)

theorem analyticAt_chartZeta_faceAmp (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) :
    AnalyticAt ℂ (chartZeta (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
      (fun i : {i // ¬ inJ J i} => h i) (fun i => k i)) (μ : ℂ) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hτ : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hC' : 0 ≤ C * (1 + Real.sqrt t) ^ (∑ i, p i) * Real.exp (M * Real.sqrt t) := by positivity
  exact (differentiableOn_chartZeta_flat
    (continuous_faceAmp p J (contDiff_fieldFam hη hζ _) m).continuousOn hC' (hflat J m hm _ hτ)
    _ _).analyticAt ((FlatStrip.isOpen _ _ _).mem_nhds (flatStrip_subtype J hμ))

/-- The Taylor coefficients of the population face factor `faceHolo` of a tilted amplitude. -/
theorem taylorCoeff_faceHolo_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ : FlatStrip p h k (μ : ℂ))
    (t : ℝ) (n : ℕ) :
    taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n =
      ∑ i ∈ range (n + 1), taylorCoeff (regularFactor h k J m μ) μ i *
        (chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
          (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - i) μ / ((n - i)! : ℂ)) := by
  have := taylorCoeff_mul (analyticAt_regularFactor p J m hμ)
    (analyticAt_chartZeta_faceAmp hη hζ p hp0 J hm hμ t) n
  unfold faceHolo
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [taylorCoeff_chartZeta_faceAmp hη hζ p hp0 J hm hμ t]

/-- Integrability of the coupling kernel with a log power against the Taylor coefficients of the
tilted face factors. -/
theorem integrable_coupKernel_logpow_mul_taylorCoeff_faceHolo (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d))
    {m : Fin d → ℕ} (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (a n : ℕ) :
    Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n)
      (volume.restrict (Ioi 0)) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ n) =
      fun t => ∑ i ∈ range (n + 1), (taylorCoeff (regularFactor h k J m μ) μ i / ((n - i)! : ℂ)) *
        (coupKernel μ t * (Real.log t : ℂ) ^ a *
          chartZetaLogMoment (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
            (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) (n - i) μ) := by
    funext t
    rw [taylorCoeff_faceHolo_eq hη hζ p hp0 J hm hμ t n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_coupKernel_logpow_mul_logMoment hcont hC (hflat J m hm) _ _ a (n - i) hμ0'
      hμ').const_mul _

/-- ★★ **The Taylor coefficients of the empirical face factor are the coupling averages of those
of the population face factors of the tilted amplitudes.** -/
theorem taylorCoeff_empFaceHolo_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ)
    (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d)) {m : Fin d → ℕ}
    (hm : m ∈ SmoothEngine.idxL p (SmoothEngine.lJ J)) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (n : ℕ) :
    taylorCoeff (empFaceHolo p η ζ h k J m μ) μ n = ∑ a ∈ range (n + 1), (a ! : ℂ)⁻¹ *
      ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
        taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a) := by
  obtain ⟨C, M, hC, hflat⟩ := flatOn_faceAmp_fieldFam hη hζ p hp0
  have hcont := continuous_faceAmp_fieldFam_joint hη hζ p J m
  have hμ' : FlatStrip (fun i : {i // ¬ inJ J i} => p i) (fun i => h i) (fun i => k i) (μ : ℂ) :=
    flatStrip_subtype J hμ
  have hμ0' : (0 : ℝ) < (μ : ℂ).re := by simpa using hμ0
  -- abbreviations
  set R := fun i => taylorCoeff (regularFactor h k J m μ) μ i with hR
  set LM := fun (t : ℝ) (j : ℕ) => chartZetaLogMoment
    (SmoothEngine.faceAmp p J (fieldFam η ζ (Real.sqrt t)) m)
    (fun i : {i // ¬ inJ J i} => h i) (fun i => k i) j μ with hLM
  have hint : ∀ a j : ℕ, Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a * LM t j)
      (volume.restrict (Ioi 0)) := fun a j =>
    integrable_coupKernel_logpow_mul_logMoment hcont hC (hflat J m hm) _ _ a j hμ0' hμ'
  -- the left-hand side by Leibniz and the split log moments
  have hL : taylorCoeff (empFaceHolo p η ζ h k J m μ) μ n =
      ∑ i ∈ range (n + 1), ∑ a ∈ range (n - i + 1), R i * ((a ! : ℂ)⁻¹ * ((n - i - a)! : ℂ)⁻¹) *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - i - a) := by
    unfold empFaceHolo
    rw [taylorCoeff_mul (analyticAt_regularFactor p J m hμ)
      (analyticAt_coupledFaceZeta hη hζ p hp0 J hm hμ0 hμ) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [taylorCoeff_coupledFaceZeta hη hζ p hp0 J hm hμ0 hμ (n - i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  -- the right-hand side by Leibniz for the population factors
  have hRt : ∀ a : ℕ, (∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a *
      taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a)) =
      ∑ i ∈ range (n - a + 1), R i * ((n - a - i)! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - a - i) := by
    intro a
    have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a *
        taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k J m μ) μ (n - a)) =
        fun t => ∑ i ∈ range (n - a + 1), R i * ((n - a - i)! : ℂ)⁻¹ *
          (coupKernel μ t * (Real.log t : ℂ) ^ a * LM t (n - a - i)) := by
      funext t
      rw [taylorCoeff_faceHolo_eq hη hζ p hp0 J hm hμ t (n - a), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hR, hLM]
      ring
    rw [hfun, integral_finsetSum _ fun i _ => (hint a (n - a - i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  simp_rw [hRt, Finset.mul_sum]
  rw [hL]
  -- interchange the double sum over `i + a ≤ n`
  rw [Finset.sum_comm' (t' := range (n + 1)) (s' := fun a => range (n - a + 1))
    (fun i a => by
      simp only [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun i hi => ?_
  have hia : n - i - a = n - a - i := by omega
  rw [hia]
  ring

end Face

/-! ### The coupling-average polar coefficients -/

section Coupling

variable {η ζ : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-- ★ **The coupling-average polar coefficients** (B4, zero-based):
`Σ_{j ∈ Ico q d} ((j−q)!)⁻¹ ∫_0^∞ t^{μ−1}(log t)^{j−q} e^{−t}
   chartPolarCoeff p (η e^{√tζ}) h k μ j dt`. -/
noncomputable def couplingPolarCoeff (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (q : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico q d, ((j - q)! : ℂ)⁻¹ *
    ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
      chartPolarCoeff p (fieldFam η ζ (Real.sqrt t)) h k μ j

/-- The population polar coefficient of a tilted amplitude, written with `taylorCoeff`. -/
theorem chartPolarCoeff_fieldFam_eq (p : Fin d → ℕ) (η ζ : (Fin d → ℝ) → ℝ) (h k : Fin d → ℕ)
    (μ : ℝ) (t : ℝ) (j : ℕ) :
    chartPolarCoeff p (fieldFam η ζ (Real.sqrt t)) h k μ j =
      ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ poleOrder h k x.1 x.2 μ),
        ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ *
          ((-1) ^ poleOrder h k x.1 x.2 μ *
            taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k x.1 x.2 μ) μ
              (poleOrder h k x.1 x.2 μ - 1 - j)) := by
  unfold chartPolarCoeff taylorCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- ★★★ **The integrated polar coefficients are the coupling averages of the population polar
coefficients of the tilted amplitudes** (B4). -/
theorem empIntegratedPolarCoeff_eq_couplingPolarCoeff (hη : ContDiff ℝ ∞ η)
    (hζ : ContDiff ℝ ∞ ζ) (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ : FlatStrip p h k (μ : ℂ)) (q : ℕ) :
    empIntegratedPolarCoeff p η ζ h k μ q = couplingPolarCoeff p η ζ h k μ q := by
  -- per-face data
  set c := fun x : (Σ _ : Finset (Fin d), Fin d → ℕ) => poleOrder h k x.1 x.2 μ with hc
  set w := fun x : (Σ _ : Finset (Fin d), Fin d → ℕ) =>
    ((SmoothEngine.faceW x.1 x.2 : ℝ) : ℂ) * resConst h k x.1 x.2 μ with hw
  set T := fun (x : (Σ _ : Finset (Fin d), Fin d → ℕ)) (t : ℝ) (n : ℕ) =>
    taylorCoeff (faceHolo p (fieldFam η ζ (Real.sqrt t)) h k x.1 x.2 μ) μ n with hT
  have hintT : ∀ x ∈ SmoothEngine.faceIndex p, ∀ a n : ℕ,
      Integrable (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ a * T x t n)
        (volume.restrict (Ioi 0)) := fun x hx a n =>
    integrable_coupKernel_logpow_mul_taylorCoeff_faceHolo hη hζ p hp0 x.1
      (Finset.mem_sigma.1 hx).2 hμ0 hμ a n
  -- the left-hand side as a double sum over faces and `a < c x − q`
  have hL : empIntegratedPolarCoeff p η ζ h k μ q =
      ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
        ∑ a ∈ range (c x - q), w x * (-1) ^ c x * (a ! : ℂ)⁻¹ *
          ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * T x t (c x - 1 - q - a) := by
    have hL0 : empIntegratedPolarCoeff p η ζ h k μ q =
        ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
          w x * (-1) ^ c x * taylorCoeff (empFaceHolo p η ζ h k x.1 x.2 μ) μ (c x - 1 - q) := by
      unfold empIntegratedPolarCoeff finiteFacePolarCoeff taylorCoeff
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hw, hc]
      ring
    rw [hL0]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_filter.1 hx)
    have hqc : q + 1 ≤ c x := hx'.2
    have hrange : range (c x - 1 - q + 1) = range (c x - q) := by congr 1; omega
    rw [taylorCoeff_empFaceHolo_eq hη hζ p hp0 x.1 (Finset.mem_sigma.1 hx'.1).2 hμ0 hμ
      (c x - 1 - q), hrange, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hT]
    ring
  -- the right-hand side as a double sum over `j` and faces
  have hR : couplingPolarCoeff p η ζ h k μ q =
      ∑ j ∈ Finset.Ico q d, ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
        w x * (-1) ^ c x * ((j - q)! : ℂ)⁻¹ *
          ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
            T x t (c x - 1 - j) := by
    unfold couplingPolarCoeff
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [chartPolarCoeff_fieldFam_eq]
    have hfun : (fun t : ℝ => coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
        ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
          w x * ((-1) ^ c x * T x t (c x - 1 - j))) =
        fun t => ∑ x ∈ (SmoothEngine.faceIndex p).filter (fun x => j + 1 ≤ c x),
          w x * (-1) ^ c x * (coupKernel μ t * (Real.log t : ℂ) ^ (j - q) *
            T x t (c x - 1 - j)) := by
      funext t
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [hfun, integral_finsetSum _ fun x hx =>
      (hintT x (Finset.mem_filter.1 hx).1 (j - q) (c x - 1 - j)).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_const_mul]
    ring
  rw [hL, hR]
  -- reindex the inner sum of the left-hand side by `j = q + a`
  have hL' : ∀ x ∈ (SmoothEngine.faceIndex p).filter (fun x => q + 1 ≤ c x),
      (∑ a ∈ range (c x - q), w x * (-1) ^ c x * (a ! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ a * T x t (c x - 1 - q - a)) =
      ∑ j ∈ Finset.Ico q (c x), w x * (-1) ^ c x * ((j - q)! : ℂ)⁻¹ *
        ∫ t in Ioi (0 : ℝ), coupKernel μ t * (Real.log t : ℂ) ^ (j - q) * T x t (c x - 1 - j) := by
    intro x _
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : q + a - q = a := by omega
    have h2 : c x - 1 - (q + a) = c x - 1 - q - a := by omega
    rw [h1, h2]
  rw [Finset.sum_congr rfl hL']
  -- interchange the sums over faces and `j`
  refine Finset.sum_comm' fun x j => ?_
  simp only [Finset.mem_filter, Finset.mem_Ico]
  have hcd : c x ≤ d := poleOrder_le h k x.1 x.2 μ
  exact ⟨fun ⟨⟨hx, h1⟩, h2, h3⟩ => ⟨⟨hx, by omega⟩, h2, by omega⟩,
    fun ⟨⟨hx, h1⟩, h2, h3⟩ => ⟨⟨hx, by omega⟩, h2, by omega⟩⟩

/-- ★★★ **The empirical all-log formula in coupling-average form**: for lattice points
`0 < μ < L` and `q ≤ d − 1`,
`empCoeff η ζ h k μ q = (−1)^{q+1}/q! · couplingPolarCoeff (depthOf h k L) η ζ h k μ q`. -/
theorem ofReal_empCoeff_eq_couplingPolarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    (empCoeff η ζ h k μ q : ℂ) =
      (-1) ^ (q + 1) * couplingPolarCoeff (depthOf h k L) η ζ h k μ q / (q ! : ℂ) := by
  rw [ofReal_empCoeff_eq_empIntegratedPolarCoeff hη hζ hk hL hμlat hμL hμ0 hq,
    empIntegratedPolarCoeff_eq_couplingPolarCoeff hη hζ _ (depthOf_pos hk hL) hμ0
      (flatStrip_depthOf hk hL hμL)]

/-- The coupling-average coefficients are the polar data of the empirical coefficients. -/
theorem couplingPolarCoeff_eq_polarCoeff (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : L₀ h ≤ L) {μ : ℝ}
    (hμlat : μ ∈ latticeBelow (Qamb k) L) (hμL : μ < L) (hμ0 : 0 < μ) {q : ℕ}
    (hq : q ≤ d - 1) :
    couplingPolarCoeff (depthOf h k L) η ζ h k μ q = polarCoeff (empCoeff η ζ h k) μ q := by
  rw [← empIntegratedPolarCoeff_eq_couplingPolarCoeff hη hζ _ (depthOf_pos hk hL) hμ0
    (flatStrip_depthOf hk hL hμL)]
  exact empIntegratedPolarCoeff_eq_polarCoeff hη hζ hk hL hμlat hμL hμ0 hq

end Coupling

end Grammar
