/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseMoving
import Grammar.FreeEnergyCorrection

/-!
# Constant-phase free energy, deterministic and with a moving random phase (unit 345; Astra #41
unit 8)

`F_N(a) = −log 𝒵_N[η; a] = λ log N − (m−1) log log N − log A(a) − (B(a)/A(a))/log N + o(1/log N)`:
the phase enters the constant term through `−log A(a) = −log J_{2λ}(a) − log H` and the `1/log N`
correction through `B/A`.  For random phases `X_N ⇒ X` (with `A > 0` everywhere) the centred and
rescaled free energy `log N (F_N(X_N) − λ log N + (m−1) log log N + log A(X_N)) ⇒ −B(X)/A(X)`: the
statistic equals `−R_N/A(X_N)` up to the error `−L(log(1+x) − x)`, `x = R_N/(A(X_N) L)`, which is
uniformly small on norm balls of `(X_N, R_N)`, and `(X_N, R_N) ⇒ (X, B(X))`.
-/

namespace Grammar

open MeasureTheory Filter Topology Set CoeffFamily

/-- **Constant-phase free energy (deterministic)**. -/
theorem constPhase_free_energy_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : 0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)) :
    (∀ᶠ N in atTop, 0 < origPhaseIntegral n h k β N 1 (fun _ => a) η) ∧
    Tendsto (fun N => Real.log N * (-Real.log (origPhaseIntegral n h k β N 1 (fun _ => a) η) -
      (l * Real.log N - ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log N) -
        Real.log (familySpectralCoeff n h k β (constFamily a) cη l
          (multCount (ratioExp h k) l - 1))))) atTop
      (𝓝 (-constPhaseSecondCoeff n h k β cη a l /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))) :=
  neg_log_twoTerm hA (constPhase_twoTerm_chart n h k hk hβ a hη hηc hev hmin hatt)

/-! ### The free-energy statistic in terms of the remainder statistic -/

/-- `L(−log Z − (λL − p log L − log A)) = −R/A − L(log(1+x) − x)`, `x = R/(AL)`, when
`Z = N^{-λ} L^p (A + R/L)`. -/
theorem freeEnergy_stat_eq {N Z A R l : ℝ} {p : ℕ} (hN : 1 < N) (hA : 0 < A)
    (hZ : Z = N ^ (-l) * Real.log N ^ p * (A + R / Real.log N))
    (hx : -1 < R / (A * Real.log N)) :
    Real.log N * (-Real.log Z - (l * Real.log N - p * Real.log (Real.log N) - Real.log A)) =
      -(R / A) - Real.log N * (Real.log (1 + R / (A * Real.log N)) - R / (A * Real.log N)) := by
  have hL : 0 < Real.log N := Real.log_pos hN
  have hN0 : 0 < N := by linarith
  have h1x : 0 < 1 + R / (A * Real.log N) := by linarith
  have hAR : A + R / Real.log N = A * (1 + R / (A * Real.log N)) := by field_simp
  have hAR0 : 0 < A + R / Real.log N := by rw [hAR]; positivity
  rw [hZ, Real.log_mul (mul_pos (Real.rpow_pos_of_pos hN0 _) (pow_pos hL p)).ne' hAR0.ne',
    Real.log_mul (Real.rpow_pos_of_pos hN0 _).ne' (pow_pos hL p).ne', Real.log_rpow hN0,
    Real.log_pow, hAR, Real.log_mul hA.ne' h1x.ne']
  field_simp
  ring

/-- The error term of the free-energy statistic is `O(M²/(A² L))` on `|R| ≤ M` once `2M ≤ AL`. -/
theorem freeEnergy_err_bound {A R L M : ℝ} (hA : 0 < A) (hL : 0 < L) (hR : |R| ≤ M)
    (hM : 2 * M ≤ A * L) :
    |L * (Real.log (1 + R / (A * L)) - R / (A * L))| ≤ 2 * M ^ 2 / (A ^ 2 * L) := by
  have hAL : 0 < A * L := mul_pos hA hL
  have hxM : |R / (A * L)| ≤ M / (A * L) := by
    rw [abs_div, abs_of_pos hAL]
    exact div_le_div_of_nonneg_right hR hAL.le
  have hhalf : M / (A * L) ≤ 1 / 2 := by
    rw [div_le_iff₀ hAL]
    linarith
  have hxabs : |R / (A * L)| ≤ 1 / 2 := hxM.trans hhalf
  have hx1 : -1 < R / (A * L) := by
    have := (abs_le.1 hxabs).1
    linarith
  have h1x : 1 / 2 ≤ 1 + R / (A * L) := by
    have := (abs_le.1 hxabs).1
    linarith
  rw [abs_mul, abs_of_pos hL]
  calc L * |Real.log (1 + R / (A * L)) - R / (A * L)|
      ≤ L * ((R / (A * L)) ^ 2 / (1 + R / (A * L))) :=
        mul_le_mul_of_nonneg_left (abs_log_one_add_sub_le hx1) hL.le
    _ ≤ L * ((R / (A * L)) ^ 2 / (1 / 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) h1x) hL.le
    _ = 2 * L * |R / (A * L)| ^ 2 := by
        rw [sq_abs]
        ring
    _ ≤ 2 * L * (M / (A * L)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxM 2) (by positivity)
    _ = 2 * M ^ 2 / (A ^ 2 * L) := by
        field_simp

/-! ### Moving random phase -/

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {F : Filter ι}
  [F.IsCountablyGenerated]

theorem continuous_vec2 {X : Type*} [TopologicalSpace X] {f₀ f₁ : X → ℝ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) :
    Continuous fun x => (![f₀ x, f₁ x] : Fin 2 → ℝ) := by
  refine continuous_pi fun a => ?_
  fin_cases a <;> simpa

theorem measurable_vec2 {X : Type*} [MeasurableSpace X] {f₀ f₁ : X → ℝ}
    (h₀ : Measurable f₀) (h₁ : Measurable f₁) :
    Measurable fun x => (![f₀ x, f₁ x] : Fin 2 → ℝ) := by
  refine measurable_pi_lambda _ fun a => ?_
  fin_cases a <;> simpa

/-- **Constant-phase free energy with a moving random phase**: for `X_N ⇒ X` and `A > 0`
everywhere, `log N (F_N(X_N) − λ log N + (m−1) log log N + log A(X_N)) ⇒ −B(X)/A(X)`. -/
theorem constPhase_free_energy_moving (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hApos : ∀ a,
      0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))
    (Nseq : ι → ℝ) (hN1 : ∀ i, 1 < Nseq i) (hN : Tendsto Nseq F atTop)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (Xz : Ω' → ℝ)
    (hX : TendstoInDistribution X F Xz (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => Real.log (Nseq i) *
        (-Real.log (origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η) -
          (l * Real.log (Nseq i) -
            ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log (Nseq i)) -
            Real.log (familySpectralCoeff n h k β (constFamily (X i ω)) cη l
              (multCount (ratioExp h k) l - 1))))) F
      (fun ω => -(constPhaseSecondCoeff n h k β cη (Xz ω) l /
        familySpectralCoeff n h k β (constFamily (Xz ω)) cη l (multCount (ratioExp h k) l - 1)))
      (fun _ => μ) μ' := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  -- named coefficient functions
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ a, A a =
      familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, ∀ a, B a = constPhaseSecondCoeff n h k β cη a l :=
    ⟨_, fun _ => rfl⟩
  have hApos' : ∀ a, 0 < A a := fun a => by rw [hA]; exact hApos a
  have hAc : Continuous A := by
    rw [funext hA]
    exact continuous_constPhaseCoeff n h k hk hβ hη hl0 _
  have hBc : Continuous B := by
    rw [funext hB]
    exact continuous_constPhaseSecondCoeff n h k hk hβ hη hl0
  simp only [← hA, ← hB]
  have hN0 : ∀ i, 0 < Nseq i := fun i => lt_trans one_pos (hN1 i)
  have hL : ∀ i, 0 < Real.log (Nseq i) := fun i => Real.log_pos (hN1 i)
  have hP : ∀ i, Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
    fun i => mul_ne_zero (Real.rpow_pos_of_pos (hN0 i) _).ne' (pow_ne_zero _ (hL i).ne')
  -- the integral and the remainder statistic
  obtain ⟨Z1, hZ1⟩ : ∃ Z1 : ι → Ω → ℝ, ∀ i ω,
      Z1 i ω = origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η := ⟨_, fun _ _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ι → Ω → ℝ, ∀ i ω, R i ω = Real.log (Nseq i) *
      (Z1 i ω / (Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)) -
        A (X i ω)) := ⟨_, fun _ _ => rfl⟩
  have hZ1m : ∀ i, Measurable (Z1 i) := fun i => by
    rw [show Z1 i = (fun a => origPhaseIntegral n h k β (Nseq i) 1 (fun _ => a) η) ∘ X i from
      funext (hZ1 i)]
    exact (continuous_constPhase_integral n h k hβ (hN0 i).le η hηc).measurable.comp (hXm i)
  have hAm : ∀ i, Measurable fun ω => A (X i ω) := fun i => hAc.measurable.comp (hXm i)
  have hRm : ∀ i, Measurable (R i) := fun i => by
    rw [show R i = fun ω => _ from funext (hR i)]
    exact (((hZ1m i).div_const _).sub (hAm i)).const_mul _
  have hZeq : ∀ i ω, Z1 i ω = Nseq i ^ (-l) * Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1)
      * (A (X i ω) + R i ω / Real.log (Nseq i)) := fun i ω => by
    have h1 : Nseq i ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (hN0 i) _).ne'
    have h2 := (hL i).ne'
    have h3 : Real.log (Nseq i) ^ (multCount (ratioExp h k) l - 1) ≠ 0 := pow_ne_zero _ h2
    rw [hR]
    field_simp
    ring
  -- the remainder vanishes in measure
  have htightX := normBounded_of_tendstoInDistribution' X Xz hX
  have hRsub : TendstoInMeasure μ (fun i ω => R i ω - B (X i ω)) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ X (fun M hM ε hε => ?_) htightX
    filter_upwards [hN.eventually
      (constPhase_twoTerm_uniform n h k hk hβ hη hηc hev hmin hatt hM hε)] with i hi
    intro ω hω
    simp only [Real.norm_eq_abs] at hω ⊢
    rw [hR, hB, hA, hZ1]
    exact hi _ hω
  -- the vector `(X, R)` converges to `(X, B(X))`
  have hC : TendstoInDistribution (fun i ω => (![X i ω, B (X i ω)] : Fin 2 → ℝ)) F
      (fun ω => (![Xz ω, B (Xz ω)] : Fin 2 → ℝ)) (fun _ => μ) μ' :=
    hX.continuous_comp (continuous_vec2 continuous_id hBc)
  have hVm : ∀ i, Measurable fun ω => (![X i ω, R i ω] : Fin 2 → ℝ) := fun i =>
    measurable_vec2 (hXm i) (hRm i)
  have hV : TendstoInDistribution (fun i ω => (![X i ω, R i ω] : Fin 2 → ℝ)) F
      (fun ω => (![Xz ω, B (Xz ω)] : Fin 2 → ℝ)) (fun _ => μ) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i => (hVm i).aemeasurable
    have hzero : TendstoInMeasure μ (fun i ω => (0 : ℝ)) F (fun _ => 0) :=
      tendstoInMeasure_const_of_tendsto (fun _ => (0 : ℝ)) 0 tendsto_const_nhds
    have hpi := tendstoInMeasure_pi_zero (μ := μ) (L := F) (κ := Fin 2) (E := ℝ)
      ![fun _ _ => (0 : ℝ), fun i ω => R i ω - B (X i ω)]
      (fun a => by fin_cases a <;> simp <;> first | exact hRsub | exact hzero)
    refine hpi.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun _ => rfl)
    funext a
    simp only [Pi.sub_apply]
    fin_cases a <;> simp
  have htight := normBounded_of_tendstoInDistribution' _ _ hV
  -- the statistic
  obtain ⟨S, hS⟩ : ∃ S : ι → Ω → ℝ, ∀ i ω, S i ω = Real.log (Nseq i) *
      (-Real.log (Z1 i ω) - (l * Real.log (Nseq i) -
        ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log (Nseq i)) -
        Real.log (A (X i ω)))) := ⟨_, fun _ _ => rfl⟩
  have hSm : ∀ i, Measurable (S i) := fun i => by
    rw [show S i = fun ω => _ from funext (hS i)]
    exact ((Real.measurable_log.comp (hZ1m i)).neg.sub
      (measurable_const.sub (Real.measurable_log.comp (hAm i)))).const_mul _
  -- the main term `−R/A(X)` converges by continuous mapping
  have hg : TendstoInDistribution (fun i ω => -(R i ω / A (X i ω))) F
      (fun ω => -(B (Xz ω) / A (Xz ω))) (fun _ => μ) μ' := by
    have hgc : Continuous fun v : Fin 2 → ℝ => -(v 1 / A (v 0)) :=
      ((continuous_apply 1).div (hAc.comp (continuous_apply 0))
        fun v => (hApos' _).ne').neg
    have := hV.continuous_comp hgc
    convert this using 2 <;> simp [Function.comp_def]
  -- the error is uniformly small on norm balls of `(X, R)`
  have herr : TendstoInMeasure μ (fun i ω => S i ω - -(R i ω / A (X i ω))) F (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_uniform_on_balls'' _ _ (fun M hM ε hε => ?_) htight
    obtain ⟨a₀, -, hmin'⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.2 (by linarith : -M ≤ M)) hAc.continuousOn
    have hAmin : 0 < A a₀ := hApos' a₀
    have hLinf : Tendsto (fun i => Real.log (Nseq i)) F atTop := Real.tendsto_log_atTop.comp hN
    filter_upwards [hLinf.eventually (eventually_ge_atTop (2 * M / A a₀)),
      hLinf.eventually (eventually_ge_atTop (2 * M ^ 2 / (A a₀ ^ 2 * ε)))] with i hi1 hi2
    intro ω hω
    have h0 := (pi_norm_le_iff_of_nonneg hM).1 hω 0
    have h1 := (pi_norm_le_iff_of_nonneg hM).1 hω 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs] at h0 h1
    have hAX : A a₀ ≤ A (X i ω) := isMinOn_iff.1 hmin' _ (abs_le.1 h0)
    have hAX0 : 0 < A (X i ω) := lt_of_lt_of_le hAmin hAX
    have hLi := hL i
    have hAL : 2 * M ≤ A (X i ω) * Real.log (Nseq i) := by
      have : 2 * M ≤ A a₀ * Real.log (Nseq i) :=
        ((div_le_iff₀ hAmin).1 hi1).trans_eq (mul_comm _ _)
      exact this.trans (mul_le_mul_of_nonneg_right hAX hLi.le)
    have hx1 : -1 < R i ω / (A (X i ω) * Real.log (Nseq i)) := by
      have hALpos : 0 < A (X i ω) * Real.log (Nseq i) := mul_pos hAX0 hLi
      rw [lt_div_iff₀ hALpos]
      have := (abs_le.1 h1).1
      linarith
    rw [hS, freeEnergy_stat_eq (hN1 i) hAX0 (hZeq i ω) hx1, sub_sub_cancel_left, norm_neg,
      Real.norm_eq_abs]
    calc |Real.log (Nseq i) * (Real.log (1 + R i ω / (A (X i ω) * Real.log (Nseq i))) -
          R i ω / (A (X i ω) * Real.log (Nseq i)))|
        ≤ 2 * M ^ 2 / (A (X i ω) ^ 2 * Real.log (Nseq i)) :=
          freeEnergy_err_bound hAX0 hLi h1 hAL
      _ ≤ 2 * M ^ 2 / (A a₀ ^ 2 * Real.log (Nseq i)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAmin.le hAX 2) hLi.le)
      _ ≤ ε := by
          rw [div_le_iff₀ (by positivity)]
          calc 2 * M ^ 2 ≤ Real.log (Nseq i) * (A a₀ ^ 2 * ε) := (div_le_iff₀ (by positivity)).1 hi2
            _ = ε * (A a₀ ^ 2 * Real.log (Nseq i)) := by ring
  -- conclude
  have hfun : (fun i ω => Real.log (Nseq i) *
      (-Real.log (origPhaseIntegral n h k β (Nseq i) 1 (fun _ => X i ω) η) -
        (l * Real.log (Nseq i) -
          ((multCount (ratioExp h k) l - 1 : ℕ) : ℝ) * Real.log (Real.log (Nseq i)) -
          Real.log (A (X i ω))))) = S := by
    funext i ω
    rw [hS, hZ1]
  rw [hfun]
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hg ?_ fun i => (hSm i).aemeasurable
  refine herr.congr' (Eventually.of_forall fun i => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun _ => rfl)
  simp only [Pi.sub_apply]

end Grammar
