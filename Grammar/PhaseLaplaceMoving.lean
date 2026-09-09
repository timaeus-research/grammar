/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.PhaseLaplaceLaw
import Grammar.ConstantPhaseMoving

/-!
# Posterior Laplace transform of `NK` with a moving random phase (unit 348; Astra #41 unit 2)

For random phases `X_N ⇒ X` (with `A > 0` everywhere) and fixed `t ≥ 0`, the posterior Laplace
transform `T_N(X_N, t) = 𝒵_{β+t}(N; X_N/r)/𝒵_β(N; X_N)` converges in distribution to
`T(X, t) = A_{β+t}(X/r)/A_β(X)`, and the next-log statistic `log N (T_N(X_N,t) − T(X_N,t))`
converges in distribution to `S(X,t) = (A_β B_{β+t} − A_{β+t} B_β)/A_β²` evaluated at `(X, X/r)`.
Same four-statistics argument as for the energy: the numerator is the constant-phase family at
temperature `β+t` and phase `aβ/(β+t)`, with the same normaliser `N^{-λ}L^{m-1}`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-- The limit `T(a,t) = A_{β+t}(aβ/(β+t))/A_β(a)` of the posterior Laplace transform. -/
noncomputable def constPhaseT (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cη : CoeffFamily (n + 1))
    (l t a : ℝ) : ℝ :=
  familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
      (multCount (ratioExp h k) l - 1) /
    familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)

/-- The next-log coefficient `S(a,t) = (A_β B_{β+t} − A_{β+t} B_β)/A_β²` at `(a, aβ/(β+t))`. -/
noncomputable def constPhaseS (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cη : CoeffFamily (n + 1))
    (l t a : ℝ) : ℝ :=
  (familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) *
      constPhaseSecondCoeff n h k (β + t) cη (a * (β / (β + t))) l -
    familySpectralCoeff n h k (β + t) (constFamily (a * (β / (β + t)))) cη l
      (multCount (ratioExp h k) l - 1) * constPhaseSecondCoeff n h k β cη a l) /
  familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2

theorem continuous_constPhaseT (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη) {l : ℝ} (hl : 0 < l) {t : ℝ}
    (ht : 0 ≤ t)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) :
    Continuous (constPhaseT n h k β cη l t) := by
  have hβt : 0 < β + t := by linarith
  unfold constPhaseT
  exact ((continuous_constPhaseCoeff n h k hk hβt hη hl _).comp
    (continuous_id.mul continuous_const)).div (continuous_constPhaseCoeff n h k hk hβ hη hl _)
    fun a => (hApos a).ne'

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {F : Filter ι}
  [F.IsCountablyGenerated]

/-- **Moving random phase, posterior Laplace transform, next-log order**:
`log N (T_N(X_N,t) − T(X_N,t)) ⇒ S(X,t)`. -/
theorem constPhaseLaplace_correction_moving (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ) (hXzm : Measurable Xz)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
        (constPhaseLaplace n h k β (Nseq i) η (X i ω) t - constPhaseT n h k β cη l t (X i ω))) F
      (fun ω => constPhaseS n h k β cη l t (Xz ω)) (fun _ => μ) μ' := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hβt : 0 < β + t := by linarith
  have hc0 : 0 < β / (β + t) := by positivity
  have hc1 : β / (β + t) ≤ 1 := by rw [div_le_one hβt]; linarith
  -- the four coefficient functions
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ a, A a =
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, ∀ a, B a = constPhaseSecondCoeff n h k β cη a l :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, ∀ a, E a = familySpectralCoeff n h k (β + t)
      (constFamily (a * (β / (β + t)))) cη l (multCount (ratioExp h k) l - 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : ℝ → ℝ, ∀ a, Dc a =
      constPhaseSecondCoeff n h k (β + t) cη (a * (β / (β + t))) l := ⟨_, fun _ => rfl⟩
  have hAc : Continuous A := by
    rw [funext hA]
    exact continuous_constPhaseCoeff n h k hk hβ hη hl0 _
  have hBc : Continuous B := by
    rw [funext hB]
    exact continuous_constPhaseSecondCoeff n h k hk hβ hη hl0
  have hEc : Continuous E := by
    rw [funext hE]
    exact (continuous_constPhaseCoeff n h k hk hβt hη hl0 _).comp
      (continuous_id.mul continuous_const)
  have hDcc : Continuous Dc := by
    rw [funext hDc]
    exact (continuous_constPhaseSecondCoeff n h k hk hβt hη hl0).comp
      (continuous_id.mul continuous_const)
  -- sample size, logarithm, normaliser
  have hN0 : ∀ i, 0 < Nseq i := fun i => lt_trans one_pos (hN1 i)
  have hL : ∀ i, 0 < Real.log (Nseq i) := fun i => Real.log_pos (hN1 i)
  obtain ⟨D, hD⟩ : ∃ D : ι → ℝ, ∀ i, D i = Nseq i ^ (-l) *
      Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) / Real.log (Nseq i) := ⟨_, fun _ => rfl⟩
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD]
    exact div_ne_zero (mul_ne_zero (Real.rpow_pos_of_pos (hN0 i) _).ne'
      (pow_ne_zero _ (hL i).ne')) (hL i).ne'
  -- the two integrals
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : ι → Ω → ℝ, ∀ i ω,
      Z1 i ω = origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Zφ, hZφ⟩ : ∃ Zφ : ι → Ω → ℝ, ∀ i ω, Zφ i ω =
      origPhaseIntegral n h k (β + t) (Nseq i) 1 (fun _ => X i ω * (β / (β + t))) η :=
    ⟨_, fun _ _ => rfl⟩
  -- the two remainder statistics
  obtain ⟨R, hR⟩ : ∃ R : ι → Ω → ℝ, ∀ i ω, R i ω = Real.log (Nseq i) *
      (Z1 i ω / (Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)) -
        A (X i ω)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ι → Ω → ℝ, ∀ i ω, R' i ω = Real.log (Nseq i) *
      (Zφ i ω / (Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)) -
        E (X i ω)) := ⟨_, fun _ _ => rfl⟩
  -- measurability
  have hZ1m : ∀ i, Measurable (Z1 i) := fun i => by
    rw [show Z1 i = (fun a => origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a) η) ∘ X i from
      funext (hZ1 i)]
    exact (continuous_constPhase_integral n h k hβ (hN0 i).le η hηc).measurable.comp (hXm i)
  have hZφm : ∀ i, Measurable (Zφ i) := fun i => by
    rw [show Zφ i = (fun a => origPhaseIntegral n h k (β + t) (Nseq i) 1 (fun _ => a) η) ∘
      (fun ω => X i ω * (β / (β + t))) from funext (hZφ i)]
    exact (continuous_constPhase_integral n h k hβt (hN0 i).le η hηc).measurable.comp
      ((hXm i).mul_const _)
  have hAm : ∀ i, Measurable fun ω => A (X i ω) := fun i => hAc.measurable.comp (hXm i)
  have hEm : ∀ i, Measurable fun ω => E (X i ω) := fun i => hEc.measurable.comp (hXm i)
  have hRm : ∀ i, Measurable (R i) := fun i => by
    rw [show R i = fun ω => _ from funext (hR i)]
    exact (((hZ1m i).div_const _).sub (hAm i)).const_mul _
  have hR'm : ∀ i, Measurable (R' i) := fun i => by
    rw [show R' i = fun ω => _ from funext (hR' i)]
    exact (((hZφm i).div_const _).sub (hEm i)).const_mul _
  -- the structural identities `Z = D (A log N + R)`
  have hZ1eq : ∀ i ω, Z1 i ω = D i * (A (X i ω) * Real.log (Nseq i) + R i ω) := fun i ω => by
    have h1 : Nseq i ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (hN0 i) _).ne'
    have h2 := (hL i).ne'
    have h3 : Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ h2
    rw [hR, hD]
    field_simp
    ring
  have hZφeq : ∀ i ω, Zφ i ω = D i * (E (X i ω) * Real.log (Nseq i) + R' i ω) := fun i ω => by
    have h1 : Nseq i ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (hN0 i) _).ne'
    have h2 := (hL i).ne'
    have h3 : Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ h2
    rw [hR', hD]
    field_simp
    ring
  -- the remainders vanish in measure
  have htight := normBounded_of_tendstoInDistribution' X Xz hX
  have hRsub : TendstoInMeasure μ (fun i ω => R i ω - B (X i ω)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_) htight
    filter_upwards [hN.eventually
      (constPhase_twoTerm_uniform n h k hk hβ hη hηc hev hmin hatt hM hε)] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [hR, hB, hA, hZ1]
    exact hi _ hω
  have hR'sub : TendstoInMeasure μ (fun i ω => R' i ω - Dc (X i ω)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_) htight
    filter_upwards [hN.eventually
      (constPhase_twoTerm_uniform n h k hk hβt hη hηc hev hmin hatt hM hε)] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [hR', hDc, hE, hZφ]
    refine hi _ ?_
    rw [abs_mul, abs_of_pos hc0]
    exact (mul_le_of_le_one_right (abs_nonneg _) hc1).trans hω
  -- continuous mapping of the coefficient vector
  have hC : TendstoInDistribution
      (fun i ω => (![B (X i ω), A (X i ω), Dc (X i ω), E (X i ω)] : Fin 4 → ℝ)) F
      (fun ω => (![B (Xz ω), A (Xz ω), Dc (Xz ω), E (Xz ω)] : Fin 4 → ℝ)) (fun _ => μ) μ' :=
    hX.continuous_comp (continuous_vec4 hBc hAc hDcc hEc)
  have hVm : ∀ i, Measurable fun ω => (![R i ω, A (X i ω), R' i ω, E (X i ω)] : Fin 4 → ℝ) :=
    fun i => measurable_vec4 (hRm i) (hAm i) (hR'm i) (hEm i)
  have hV : TendstoInDistribution
      (fun i ω => (![R i ω, A (X i ω), R' i ω, E (X i ω)] : Fin 4 → ℝ)) F
      (fun ω => (![B (Xz ω), A (Xz ω), Dc (Xz ω), E (Xz ω)] : Fin 4 → ℝ)) (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => (hVm i).aemeasurable
    have hzero : TendstoInMeasure μ (fun i ω => (0 : ℝ)) F (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto (fun _ => (0 : ℝ)) 0 tendsto_const_nhds
    have hpi := tendstoInMeasure_pi_zero (μ := μ) (L := F) (κ := Fin 4) (E := ℝ)
      ![fun i ω => R i ω - B (X i ω), fun _ _ => (0 : ℝ), fun i ω => R' i ω - Dc (X i ω),
        fun _ _ => (0 : ℝ)]
      (fun a => by fin_cases a <;> simp <;> first | exact hRsub | exact hR'sub | exact hzero)
    refine hpi.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    funext a
    simp only [Pi.sub_apply]
    fin_cases a <;> simp
  -- the limit denominator never vanishes
  have hBz : μ' {ω | A (Xz ω) = 0} = 0 := by
    have : {ω | A (Xz ω) = 0} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rw [hA]
      exact (hApos _).ne'
    rw [this, measure_empty]
  -- the four-statistics interface
  have hmain := tendstoInDistribution_secondOrder_of_stats Nseq hN1 hN (fun i ω => A (X i ω)) R
    (fun i ω => E (X i ω)) R' Zφ Z1 D D hDne hDne hAm hRm hEm hR'm hZφm hZ1m hZ1eq hZφeq
    (fun ω => A (Xz ω)) (fun ω => B (Xz ω)) (fun ω => E (Xz ω)) (fun ω => Dc (Xz ω))
    (hAc.measurable.comp hXzm) (hBc.measurable.comp hXzm) (hEc.measurable.comp hXzm)
    (hDcc.measurable.comp hXzm) hV hBz
  -- identify the statistic and the limit
  have hfun : (fun i ω => Real.log (Nseq i) *
      (constPhaseLaplace n h k β (Nseq i) η (X i ω) t - constPhaseT n h k β cη l t (X i ω))) =
      fun i ω => Real.log (Nseq i) * (Zφ i ω / Z1 i ω * (D i / D i) - E (X i ω) / A (X i ω)) := by
    funext i ω
    rw [constPhaseLaplace_eq n h k hβ ht, div_self (hDne i), mul_one, ← hZφ i ω, ← hZ1 i ω]
    unfold constPhaseT
    rw [← hE, ← hA]
  have hlim : (fun ω => constPhaseS n h k β cη l t (Xz ω)) =
      fun ω => (A (Xz ω) * Dc (Xz ω) - E (Xz ω) * B (Xz ω)) / A (Xz ω) ^ 2 := by
    funext ω
    unfold constPhaseS
    rw [← hA, ← hB, ← hE, ← hDc]
  rw [hfun, hlim]
  exact hmain

/-- **Moving random phase, posterior Laplace transform, leading order**: `T_N(X_N,t) ⇒ T(X,t)`. -/
theorem constPhaseLaplace_moving (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ) (hXzm : Measurable Xz)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => constPhaseLaplace n h k β (Nseq i) η (X i ω) t) F
      (fun ω => constPhaseT n h k β cη l t (Xz ω)) (fun _ => μ) μ' := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hβt : 0 < β + t := by linarith
  have hY := constPhaseLaplace_correction_moving n h k hk hβ ht hη hηc hev hmin hatt hApos Nseq
    hN1 hN X hXm Xz hXzm hX
  have hC1 : TendstoInDistribution (fun i ω => constPhaseT n h k β cη l t (X i ω)) F
      (fun ω => constPhaseT n h k β cη l t (Xz ω)) (fun _ => μ) μ' :=
    hX.continuous_comp (g := constPhaseT n h k β cη l t)
      (continuous_constPhaseT n h k hk hβ hη hl0 ht hApos)
  have hN0 : ∀ i, 0 < Nseq i := fun i => lt_trans one_pos (hN1 i)
  have hL : ∀ i, 0 < Real.log (Nseq i) := fun i => Real.log_pos (hN1 i)
  have hQm : ∀ i, Measurable fun ω => constPhaseLaplace n h k β (Nseq i) η (X i ω) t := fun i => by
    have e : (fun ω => constPhaseLaplace n h k β (Nseq i) η (X i ω) t) = fun ω =>
        origPhaseIntegral n h k (β + t) (Nseq i) 1 (fun _ => X i ω * (β / (β + t))) η /
          origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η :=
      funext fun ω => constPhaseLaplace_eq n h k hβ ht _ η _
    rw [e]
    exact ((continuous_constPhase_integral n h k hβt (hN0 i).le η hηc).measurable.comp
      ((hXm i).mul_const _)).div
      ((continuous_constPhase_integral n h k hβ (hN0 i).le η hηc).measurable.comp (hXm i))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC1 ?_ fun i => (hQm i).aemeasurable
  have htight := normBounded_of_tendstoInDistribution' _ _ hY
  have hsub : TendstoInMeasure μ (fun i ω => Real.log (Nseq i) *
      (constPhaseLaplace n h k β (Nseq i) η (X i ω) t - constPhaseT n h k β cη l t (X i ω)) /
        Real.log (Nseq i)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ _ (fun M hM ε hε => ?_) htight
    have hLinf : Tendsto (fun i => Real.log (Nseq i)) F atTop := Real.tendsto_log_atTop.comp hN
    filter_upwards [hLinf.eventually (eventually_ge_atTop (M / ε))] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [abs_div, abs_of_pos (hL i), div_le_iff₀ (hL i)]
    calc _ ≤ M := hω
      _ = ε * (M / ε) := by field_simp
      _ ≤ ε * Real.log (Nseq i) := mul_le_mul_of_nonneg_left hi hε.le
  refine hsub.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun _ => rfl)
  simp only [Pi.sub_apply]
  exact mul_div_cancel_left₀ _ (hL i).ne'

end Grammar
