/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableUnitKernel

/-!
# The leading-term certificate of the variable-unit box kernel

Unit 2b of consult #81 (`tide-log/gpt6_bigpicture_v81.md`): **the phase unit may depend on the
normal coordinates.** For a positive continuous unit `u(z, v)` and a continuous amplitude `A`, the
variable-unit kernel has the certificate

`varBoxKernel u A z N / (N^{−λ} log^{m−1} N) → varBoxFaceCoeff u A λ z = boxFaceCoeff (A · u^{−λ})`

(`hasLeadingTerm_varBoxKernel`, pointwise in the base point;
`hasLeadingTerm_integral_varBoxKernel` integrated against any integrable base weight over a compact
base), with **no sign condition on the amplitude or the base weight**. The unit is frozen on the
minimal face by `faceProj` — for a non-all-minimal stratum the residual normal coordinates remain
integration variables in the coefficient, as required.

**Proof (Astra #81's range comparison).** At a fixed base point bound `0 < a ≤ u ≤ B` on the
closed box; for `δ > 0` cut the range `[a, B]` by the telescoping ramp partition `χ_j` of CCLIII
into pieces of multiplicative width `≤ 1 + δ` and set `A_j = A · χ_j(u)` (continuous). For `A ≥ 0`
and `N ≥ 0`, `A_j e^{−N r_j P} ≤ A_j e^{−N u P} ≤ A_j e^{−N ℓ_j P}` on the support of `A_j`
(`varBoxKernel_anti_unit`), and the constant-unit kernels have the certificates of CCXXXI with
coefficients `r_j^{−λ} bFC(A_j)`, `ℓ_j^{−λ} bFC(A_j)`, which bound `bFC(A_j u^{−λ})` from below and
above (`boxFaceCoeff_mono`, the frozen unit lies in `[ℓ_j, r_j]` on the support) within the factor
`(1+δ)^λ`; the approximate squeeze (`hasLeadingTerm_of_approx_squeeze`) with `δ → 0` gives the
certificate at the target coefficient. Signed amplitudes split as `A = max A 0 − max (−A) 0`
(`HasLeadingTerm.sub`, `varBoxKernel_sub`, `boxFaceCoeff_sub`); the integrated version is dominated
convergence (`hasLeadingTerm_setIntegral_of_dominated_kernel`) with the uniform bound of the
constant-unit kernel at the lower unit bound (`abs_varBoxKernel_le_of_le`).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-- Difference of certificates. -/
theorem HasLeadingTerm.sub {Z₁ Z₂ : ℝ → ℝ} {c₁ c₂ lam : ℝ} {k : ℕ} (h₁ : HasLeadingTerm Z₁ c₁ lam k)
    (h₂ : HasLeadingTerm Z₂ c₂ lam k) : HasLeadingTerm (fun N => Z₁ N - Z₂ N) (c₁ - c₂) lam k := by
  have := h₁.add (h₂.const_mul (-1))
  simp only [neg_one_mul, ← sub_eq_add_neg] at this
  exact this

section Certificate

variable {n : ℕ} {h k : Fin (n + 1) → ℕ} {b : ℝ} {t : ℕ}

/-! ### Congruence and subtraction -/

theorem varBoxKernel_congr {u A₁ A₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    (hAB : ∀ v ∈ piBox (n + 1) (Ioc 0 b), A₁ z v = A₂ z v) (N : ℝ) :
    varBoxKernel n h k b u A₁ z N = varBoxKernel n h k b u A₂ z N := by
  unfold varBoxKernel
  refine setIntegral_congr_fun measurableSet_piBox_Ioc_pos fun v hv => ?_
  rw [hAB v hv]

theorem smul_faceProj_mem_piBox {l : ℝ} (hb : 0 ≤ b) {w : Fin (n + 1) → ℝ}
    (hw : w ∈ unitBox (n + 1)) : b • faceProj h k l w ∈ piBox (n + 1) (Icc 0 b) := by
  intro i _
  have hf := faceProj_mapsTo h k l hw i (mem_univ i)
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ⟨mul_nonneg hb hf.1, by nlinarith [hf.2]⟩

theorem boxFaceCoeff_congr {A₁ A₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    {β l : ℝ} (hb : 0 ≤ b) (hAB : ∀ v ∈ piBox (n + 1) (Icc 0 b), A₁ z v = A₂ z v) :
    boxFaceCoeff n h k β b A₁ l z = boxFaceCoeff n h k β b A₂ l z := by
  unfold boxFaceCoeff amplitudeCoeff
  congr 1
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun w hw => ?_
  dsimp only
  rw [hAB _ (smul_faceProj_mem_piBox hb hw)]

theorem varBoxKernel_sub {u A₁ A₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hA₁ : Continuous (Function.uncurry A₁)) (hA₂ : Continuous (Function.uncurry A₂))
    (hu : Continuous (Function.uncurry u)) (z : Fin t → ℝ) (N : ℝ) :
    varBoxKernel n h k b u (fun z v => A₁ z v - A₂ z v) z N =
      varBoxKernel n h k b u A₁ z N - varBoxKernel n h k b u A₂ z N := by
  unfold varBoxKernel
  have h1 := continuous_amp_of_uncurry A₁ hA₁ z
  have h2 := continuous_amp_of_uncurry A₂ hA₂ z
  have huz := continuous_amp_of_uncurry u hu z
  rw [← integral_sub (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop))
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop))]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  ring

theorem boxFaceCoeff_sub (hk : ∀ i, 0 < k i) {l : ℝ} (hmin : ∀ i, l ≤ ratioExp h k i) (hb : 0 ≤ b)
    {A₁ A₂ : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {z : Fin t → ℝ}
    (h1 : ContinuousOn (A₁ z) (piBox (n + 1) (Icc 0 b)))
    (h2 : ContinuousOn (A₂ z) (piBox (n + 1) (Icc 0 b))) (β : ℝ) :
    boxFaceCoeff n h k β b (fun z v => A₁ z v - A₂ z v) l z =
      boxFaceCoeff n h k β b A₁ l z - boxFaceCoeff n h k β b A₂ l z := by
  unfold boxFaceCoeff amplitudeCoeff
  rw [← mul_sub, ← mul_sub]
  congr 1
  congr 1
  rw [← integral_sub (integrableOn_faceIntegrand hk hmin (continuousOn_dilate hb h1))
    (integrableOn_faceIntegrand hk hmin (continuousOn_dilate hb h2))]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  ring

/-- Comparison of the kernel with the constant-unit kernel of a lower unit bound. -/
theorem abs_varBoxKernel_le_of_le {u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) {z : Fin t → ℝ}
    {a : ℝ} (hle : ∀ v ∈ piBox (n + 1) (Ioc 0 b), a ≤ u z v) {N : ℝ} (hN : 0 ≤ N) :
    |varBoxKernel n h k b u A z N| ≤
      varBoxKernel n h k b (fun _ _ => a) (fun z v => |A z v|) z N := by
  unfold varBoxKernel
  have hAz := continuous_amp_of_uncurry A hA z
  have huz := continuous_amp_of_uncurry u hu z
  refine abs_integral_le_integral_abs.trans (setIntegral_mono_on
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop))
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ (by fun_prop)) measurableSet_piBox_Ioc_pos
    fun v hv => ?_)
  have hv0 : ∀ i, 0 < v i := fun i => (hv i (mem_univ i)).1
  have hP : 0 ≤ ∏ i, v i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hv0 i).le _
  have hQ : 0 ≤ ∏ i, v i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hv0 i).le _
  rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) hP)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hle v hv) hN) hQ

/-! ### The range pieces -/

/-- The range pieces `A · χ_j(u)` of the amplitude. -/
noncomputable def rangePiece (a w : ℝ) (j : ℕ) (u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ :=
  fun z v => A z v * chi a w j (u z v)

theorem continuous_rangePiece {u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) (a w : ℝ)
    (j : ℕ) : Continuous (Function.uncurry (rangePiece a w j u A)) :=
  hA.mul ((continuous_chi a w j).comp hu)

/-! ### The pointwise certificate -/

variable {u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ}

/-- **The variable-unit certificate at a base point, nonnegative amplitude.** -/
theorem hasLeadingTerm_varBoxKernel_of_nonneg (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) {z : Fin t → ℝ}
    {a B : ℝ} (ha : 0 < a) (hab : ∀ v ∈ piBox (n + 1) (Icc 0 b), a ≤ u z v ∧ u z v ≤ B)
    (hA0 : ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 ≤ A z v) :
    HasLeadingTerm (varBoxKernel n h k b u A z) (varBoxFaceCoeff n h k b u A l z) l
      (multCount (ratioExp h k) l - 1) := by
  have hbox_sub : piBox (n + 1) (Ioc 0 b) ⊆ piBox (n + 1) (Icc 0 b) :=
    pi_mono fun _ _ => Ioc_subset_Icc_self
  have h0mem : (fun _ => (0 : ℝ)) ∈ piBox (n + 1) (Icc (0 : ℝ) b) := fun i _ => ⟨le_rfl, hb.le⟩
  have haB : a ≤ B := (hab _ h0mem).1.trans (hab _ h0mem).2
  have hu_pos : ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 < u z v := fun v hv => ha.trans_le (hab v hv).1
  have huz : ContinuousOn (u z) (piBox (n + 1) (Icc 0 b)) :=
    (continuous_amp_of_uncurry u hu z).continuousOn
  have hAz : ContinuousOn (A z) (piBox (n + 1) (Icc 0 b)) :=
    (continuous_amp_of_uncurry A hA z).continuousOn
  have hupow : ContinuousOn (fun v => u z v ^ (-l)) (piBox (n + 1) (Icc 0 b)) :=
    huz.rpow_const fun v hv => Or.inl (hu_pos v hv).ne'
  have hC0 : 0 ≤ varBoxFaceCoeff n h k b u A l z :=
    boxFaceCoeff_nonneg' hk hmin hl one_pos hb (A := fun z v => A z v * u z v ^ (-l))
      (hAz.mul hupow) fun v hv => mul_nonneg (hA0 v hv) (Real.rpow_nonneg (hu_pos v hv).le _)
  refine hasLeadingTerm_of_approx_squeeze fun ε hε => ?_
  -- the multiplicative tolerance
  have hcont : ContinuousAt (fun d : ℝ => (1 + d) ^ l * varBoxFaceCoeff n h k b u A l z) 0 :=
    (((continuous_const.add continuous_id).rpow_const fun _ => Or.inr hl.le).mul
      continuous_const).continuousAt
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousAt_iff.1 hcont ε hε
  have hδpos : 0 < δ₀ / 2 := half_pos hδ₀
  have hclose : (1 + δ₀ / 2) ^ l * varBoxFaceCoeff n h k b u A l z ≤
      varBoxFaceCoeff n h k b u A l z + ε := by
    have := hδ (x := δ₀ / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]; exact half_lt_self hδ₀)
    rw [Real.dist_eq, add_zero, Real.one_rpow, one_mul] at this
    linarith [le_abs_self ((1 + δ₀ / 2) ^ l * varBoxFaceCoeff n h k b u A l z -
      varBoxFaceCoeff n h k b u A l z)]
  have h1le : 1 ≤ (1 + δ₀ / 2) ^ l := Real.one_le_rpow (by linarith) hl.le
  -- the range partition
  obtain ⟨m, hm⟩ := exists_nat_ge ((B + 1 - a) / (a * (δ₀ / 2) / 2))
  have hnum : 0 < B + 1 - a := by linarith
  have hden : 0 < a * (δ₀ / 2) / 2 := by positivity
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (div_pos hnum hden) hm
  have hw : 0 < (B + 1 - a) / m := div_pos hnum hmpos
  have hwδ : 2 * ((B + 1 - a) / m) / a ≤ δ₀ / 2 := by
    rw [div_le_iff₀ ha]
    have : (B + 1 - a) / m ≤ a * (δ₀ / 2) / 2 := by
      rw [div_le_iff₀ hmpos]
      rw [div_le_iff₀ hden] at hm
      linarith
    linarith
  have hsum : a + m * ((B + 1 - a) / m) = B + 1 := by
    field_simp
    ring
  have hule : ∀ v ∈ piBox (n + 1) (Icc 0 b), u z v ≤ a + m * ((B + 1 - a) / m) := fun v hv => by
    rw [hsum]; linarith [(hab v hv).2]
  -- the pieces
  have hAj : ∀ j, Continuous (Function.uncurry (rangePiece a ((B + 1 - a) / m) j u A)) :=
    fun j => continuous_rangePiece hA hu a ((B + 1 - a) / m) j
  have hAj0 : ∀ j, ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 ≤ rangePiece a ((B + 1 - a) / m) j u A z v :=
    fun j v hv => mul_nonneg (hA0 v hv) (chi_nonneg hw j _)
  have hAj_on : ∀ j, ContinuousOn (rangePiece a ((B + 1 - a) / m) j u A z)
      (piBox (n + 1) (Icc 0 b)) :=
    fun j => (continuous_amp_of_uncurry _ (hAj j) z).continuousOn
  have hsplit : ∀ v ∈ piBox (n + 1) (Icc 0 b),
      A z v = ∑ j ∈ Finset.range (m + 1), rangePiece a ((B + 1 - a) / m) j u A z v := fun v hv => by
    unfold rangePiece
    rw [← Finset.mul_sum, sum_chi hw m (hule v hv), mul_one]
  have hup_pos : ∀ j : ℕ, 0 < upperPt a ((B + 1 - a) / m) j := fun j => by
    unfold upperPt
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hlow_pos : ∀ j : ℕ, 0 < lowerPt a ((B + 1 - a) / m) j := fun j => lowerPt_pos ha j
  -- support facts
  have hsupp_up : ∀ j, ∀ v ∈ piBox (n + 1) (Icc 0 b),
      rangePiece a ((B + 1 - a) / m) j u A z v ≠ 0 → u z v ≤ upperPt a ((B + 1 - a) / m) j :=
    fun j v _ hne => (lt_upperPt_of_chi_ne_zero hw (right_ne_zero_of_mul hne)).le
  have hsupp_low : ∀ j, ∀ v ∈ piBox (n + 1) (Icc 0 b),
      rangePiece a ((B + 1 - a) / m) j u A z v ≠ 0 → lowerPt a ((B + 1 - a) / m) j ≤ u z v :=
    fun j v hv hne => lowerPt_le_of_chi_ne_zero hw (hab v hv).1 (right_ne_zero_of_mul hne)
  -- the bounding kernels and their certificates
  refine ⟨fun N => ∑ j ∈ Finset.range (m + 1),
      varBoxKernel n h k b (fun _ _ => upperPt a ((B + 1 - a) / m) j)
        (rangePiece a ((B + 1 - a) / m) j u A) z N,
    fun N => ∑ j ∈ Finset.range (m + 1),
      varBoxKernel n h k b (fun _ _ => lowerPt a ((B + 1 - a) / m) j)
        (rangePiece a ((B + 1 - a) / m) j u A) z N,
    ∑ j ∈ Finset.range (m + 1), upperPt a ((B + 1 - a) / m) j ^ (-l) *
      boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z,
    ∑ j ∈ Finset.range (m + 1), lowerPt a ((B + 1 - a) / m) j ^ (-l) *
      boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z, ?_, ?_, ?_, ?_, ?_⟩
  · -- the sandwich
    refine (eventually_ge_atTop 0).mono fun N hN => ?_
    have hZ : varBoxKernel n h k b u A z N = ∑ j ∈ Finset.range (m + 1),
        varBoxKernel n h k b u (rangePiece a ((B + 1 - a) / m) j u A) z N := by
      rw [← varBoxKernel_sum u (Finset.range (m + 1))
        (fun j => rangePiece a ((B + 1 - a) / m) j u A) (fun j _ => hAj j) hu z N]
      exact varBoxKernel_congr (fun v hv => hsplit v (hbox_sub hv)) N
    rw [hZ]
    constructor
    · refine Finset.sum_le_sum fun j _ => ?_
      exact varBoxKernel_anti_unit (rangePiece a ((B + 1 - a) / m) j u A) (u₁ := u)
        (u₂ := fun _ _ => upperPt a ((B + 1 - a) / m) j) (hAj j) hu continuous_const
        (fun v hv => hAj0 j v (hbox_sub hv)) (fun v hv hne => hsupp_up j v (hbox_sub hv) hne) hN
    · refine Finset.sum_le_sum fun j _ => ?_
      exact varBoxKernel_anti_unit (rangePiece a ((B + 1 - a) / m) j u A)
        (u₁ := fun _ _ => lowerPt a ((B + 1 - a) / m) j) (u₂ := u) (hAj j) continuous_const hu
        (fun v hv => hAj0 j v (hbox_sub hv)) (fun v hv hne => hsupp_low j v (hbox_sub hv) hne) hN
  · -- lower certificate
    refine HasLeadingTerm.sum _ fun j _ => ?_
    exact (hasLeadingTerm_scalarBoxKernel (fun _ => upperPt a ((B + 1 - a) / m) j) _ hk hb hmin
      hatt (hAj j) (z := z) (hup_pos j)).congr' (Eventually.of_forall fun N =>
        scalarBoxKernel_const_eq _ _ z N)
  · -- upper certificate
    refine HasLeadingTerm.sum _ fun j _ => ?_
    exact (hasLeadingTerm_scalarBoxKernel (fun _ => lowerPt a ((B + 1 - a) / m) j) _ hk hb hmin
      hatt (hAj j) (z := z) (hlow_pos j)).congr' (Eventually.of_forall fun N =>
        scalarBoxKernel_const_eq _ _ z N)
  all_goals
    -- coefficient comparisons
    have hCsum : varBoxFaceCoeff n h k b u A l z = ∑ j ∈ Finset.range (m + 1),
        boxFaceCoeff n h k 1 b (fun z v => rangePiece a ((B + 1 - a) / m) j u A z v * u z v ^ (-l))
          l z := by
      unfold varBoxFaceCoeff
      rw [← boxFaceCoeff_sum hk hmin _ (fun j z v => rangePiece a ((B + 1 - a) / m) j u A z v *
        u z v ^ (-l)) hb.le (fun j _ => (hAj_on j).mul hupow) 1]
      refine boxFaceCoeff_congr hb.le fun v hv => ?_
      rw [← Finset.sum_mul, hsplit v hv]
    have hlo_j : ∀ j ∈ Finset.range (m + 1), upperPt a ((B + 1 - a) / m) j ^ (-l) *
        boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z ≤
        boxFaceCoeff n h k 1 b
          (fun z v => rangePiece a ((B + 1 - a) / m) j u A z v * u z v ^ (-l)) l z := fun j _ => by
      rw [← boxFaceCoeff_const_mul (h := h) (k := k) (l := l) (b := b)]
      refine boxFaceCoeff_mono hk hmin hl one_pos hb (continuousOn_const.mul (hAj_on j))
        ((hAj_on j).mul hupow) fun v hv => ?_
      by_cases hne : rangePiece a ((B + 1 - a) / m) j u A z v = 0
      · simp [hne]
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (hu_pos v hv)
          (hsupp_up j v hv hne) (neg_nonpos.2 hl.le)) (hAj0 j v hv)
    have hhi_j : ∀ j ∈ Finset.range (m + 1),
        boxFaceCoeff n h k 1 b
          (fun z v => rangePiece a ((B + 1 - a) / m) j u A z v * u z v ^ (-l)) l z ≤
        lowerPt a ((B + 1 - a) / m) j ^ (-l) *
          boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z := fun j _ => by
      rw [← boxFaceCoeff_const_mul (h := h) (k := k) (l := l) (b := b)]
      refine boxFaceCoeff_mono hk hmin hl one_pos hb ((hAj_on j).mul hupow)
        (continuousOn_const.mul (hAj_on j)) fun v hv => ?_
      by_cases hne : rangePiece a ((B + 1 - a) / m) j u A z v = 0
      · simp [hne]
      · rw [mul_comm (lowerPt a ((B + 1 - a) / m) j ^ (-l))]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (hlow_pos j)
          (hsupp_low j v hv hne) (neg_nonpos.2 hl.le)) (hAj0 j v hv)
    have hbFC0 : ∀ j, 0 ≤ boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z :=
      fun j => boxFaceCoeff_nonneg' hk hmin hl one_pos hb (hAj_on j) (hAj0 j)
    have hratio : ∀ j : ℕ, lowerPt a ((B + 1 - a) / m) j ^ (-l) ≤
        (1 + δ₀ / 2) ^ l * upperPt a ((B + 1 - a) / m) j ^ (-l) := fun j => by
      have hle : upperPt a ((B + 1 - a) / m) j ≤ (1 + δ₀ / 2) * lowerPt a ((B + 1 - a) / m) j :=
        (upperPt_le_mul_lowerPt ha hw j).trans
          (mul_le_mul_of_nonneg_right (by linarith) (hlow_pos j).le)
      have h1 := Real.rpow_le_rpow_of_nonpos (hup_pos j) hle (neg_nonpos.2 hl.le)
      rw [Real.mul_rpow (by linarith) (hlow_pos j).le] at h1
      have hpos : 0 < (1 + δ₀ / 2) ^ l := Real.rpow_pos_of_pos (by linarith) _
      have hinv : (1 + δ₀ / 2) ^ l * (1 + δ₀ / 2) ^ (-l) = 1 := by
        rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ hpos.ne']
      calc lowerPt a ((B + 1 - a) / m) j ^ (-l)
          = (1 + δ₀ / 2) ^ l * ((1 + δ₀ / 2) ^ (-l) * lowerPt a ((B + 1 - a) / m) j ^ (-l)) := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ (1 + δ₀ / 2) ^ l * upperPt a ((B + 1 - a) / m) j ^ (-l) :=
            mul_le_mul_of_nonneg_left h1 hpos.le
    have hclo_le : ∑ j ∈ Finset.range (m + 1), upperPt a ((B + 1 - a) / m) j ^ (-l) *
        boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z ≤
        varBoxFaceCoeff n h k b u A l z := by
      rw [hCsum]; exact Finset.sum_le_sum hlo_j
    have hle_chi : varBoxFaceCoeff n h k b u A l z ≤ ∑ j ∈ Finset.range (m + 1),
        lowerPt a ((B + 1 - a) / m) j ^ (-l) *
          boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z := by
      rw [hCsum]; exact Finset.sum_le_sum hhi_j
    have hchi_le : ∑ j ∈ Finset.range (m + 1), lowerPt a ((B + 1 - a) / m) j ^ (-l) *
        boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z ≤
        (1 + δ₀ / 2) ^ l * ∑ j ∈ Finset.range (m + 1), upperPt a ((B + 1 - a) / m) j ^ (-l) *
          boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hratio j) (hbFC0 j)
    have hclo0 : 0 ≤ ∑ j ∈ Finset.range (m + 1), upperPt a ((B + 1 - a) / m) j ^ (-l) *
        boxFaceCoeff n h k 1 b (rangePiece a ((B + 1 - a) / m) j u A) l z :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (hup_pos j).le _) (hbFC0 j)
    nlinarith

/-- **The variable-unit certificate at a base point** (signed amplitude). -/
theorem hasLeadingTerm_varBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) (hu : Continuous (Function.uncurry u)) {z : Fin t → ℝ}
    {a B : ℝ} (ha : 0 < a) (hab : ∀ v ∈ piBox (n + 1) (Icc 0 b), a ≤ u z v ∧ u z v ≤ B) :
    HasLeadingTerm (varBoxKernel n h k b u A z) (varBoxFaceCoeff n h k b u A l z) l
      (multCount (ratioExp h k) l - 1) := by
  have hu_pos : ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 < u z v := fun v hv => ha.trans_le (hab v hv).1
  have hupow : ContinuousOn (fun v => u z v ^ (-l)) (piBox (n + 1) (Icc 0 b)) :=
    (continuous_amp_of_uncurry u hu z).continuousOn.rpow_const fun v hv => Or.inl (hu_pos v hv).ne'
  have hAp : Continuous (Function.uncurry fun z v => max (A z v) 0) := hA.max continuous_const
  have hAm : Continuous (Function.uncurry fun z v => max (-A z v) 0) := hA.neg.max continuous_const
  have hsplit : ∀ z v, A z v = max (A z v) 0 - max (-A z v) 0 := fun z v =>
    (max_zero_sub_max_neg_zero_eq_self (A z v)).symm
  have h1 := hasLeadingTerm_varBoxKernel_of_nonneg hk hb hl hmin hatt hAp hu ha hab
    fun v _ => le_max_right _ _
  have h2 := hasLeadingTerm_varBoxKernel_of_nonneg hk hb hl hmin hatt hAm hu ha hab
    fun v _ => le_max_right _ _
  have hker : ∀ N, varBoxKernel n h k b u A z N =
      varBoxKernel n h k b u (fun z v => max (A z v) 0) z N -
        varBoxKernel n h k b u (fun z v => max (-A z v) 0) z N := fun N => by
    rw [← varBoxKernel_sub hAp hAm hu z N]
    exact varBoxKernel_congr (fun v _ => hsplit z v) N
  have hcoef : varBoxFaceCoeff n h k b u A l z =
      varBoxFaceCoeff n h k b u (fun z v => max (A z v) 0) l z -
        varBoxFaceCoeff n h k b u (fun z v => max (-A z v) 0) l z := by
    unfold varBoxFaceCoeff
    rw [← boxFaceCoeff_sub hk hmin hb.le
      ((continuous_amp_of_uncurry _ hAp z).continuousOn.mul hupow)
      ((continuous_amp_of_uncurry _ hAm z).continuousOn.mul hupow) 1]
    refine boxFaceCoeff_congr hb.le fun v _ => ?_
    rw [hsplit z v, sub_mul]
  rw [hcoef]
  exact (h1.sub h2).congr' (Eventually.of_forall fun N => (hker N).symm)

/-! ### The integrated certificate -/

/-- ★ **The leading-term certificate of the variable-unit kernel integrated over a compact base**:
for a positive continuous unit `u(z,v)` on the compact base times the closed box, a continuous
(signed) amplitude and an integrable (signed) base weight,
`∫_T β(z) varBoxKernel u A z N dz ⟶ (∫_T β(z) boxFaceCoeff(A·u^{−λ}) z dz) · N^{−λ} (log N)^{m−1}`.
-/
theorem hasLeadingTerm_integral_varBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ} (hl : 0 < l)
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hu : Continuous (Function.uncurry u))
    (hu_pos : ∀ z ∈ T, ∀ v ∈ piBox (n + 1) (Icc 0 b), 0 < u z v) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * varBoxKernel n h k b u A z N)
      (∫ z in T, βw z * varBoxFaceCoeff n h k b u A l z) l (multCount (ratioExp h k) l - 1) := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp only [Measure.restrict_empty, integral_zero_measure]
    exact hasLeadingTerm_zero _ _
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  have hboxc : IsCompact (piBox (n + 1) (Icc (0 : ℝ) b)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h0mem : (fun _ => (0 : ℝ)) ∈ piBox (n + 1) (Icc (0 : ℝ) b) := fun i _ => ⟨le_rfl, hb.le⟩
  obtain ⟨a, B, ha, hab⟩ := exists_pos_bounds_of_continuousOn (hT.prod hboxc)
    (hTne.prod ⟨_, h0mem⟩) hu.continuousOn (fun p hp => hu_pos p.1 hp.1 p.2 hp.2)
  have hbox_sub : piBox (n + 1) (Ioc 0 b) ⊆ piBox (n + 1) (Icc 0 b) :=
    pi_mono fun _ _ => Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := eventually_abs_scalarBoxKernel_div_le (fun _ => a) (fun z v => |A z v|) hk hb
    hl hmin hatt (continuous_abs.comp hA) hT ha (fun _ _ => le_rfl)
  refine hasLeadingTerm_setIntegral_of_dominated_kernel
    (L := fun N z => varBoxKernel n h k b u A z N) (ℓ := fun z => varBoxFaceCoeff n h k b u A l z)
    (β := βw) (G := fun _ => C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N => hβw.aestronglyMeasurable.mul
      (stronglyMeasurable_varBoxKernel u A hA hu N).aestronglyMeasurable
  · exact (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz =>
      hasLeadingTerm_varBoxKernel hk hb hl hmin hatt hA hu ha fun v hv => hab (z, v) ⟨hz, hv⟩)
  · filter_upwards [hC, eventually_ge_atTop 0] with N hN hN0
    refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz => ?_)
    rw [abs_div]
    calc |varBoxKernel n h k b u A z N| / |powLogScale l (multCount (ratioExp h k) l - 1) N|
        ≤ |scalarBoxKernel n h k b (fun _ => a) (fun z v => |A z v|) z N| /
            |powLogScale l (multCount (ratioExp h k) l - 1) N| := by
          refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
          refine (abs_varBoxKernel_le_of_le hA hu (fun v hv => (hab (z, v) ⟨hz, hbox_sub hv⟩).1)
            hN0).trans ?_
          rw [scalarBoxKernel_const_eq]
          exact le_abs_self _
      _ = |scalarBoxKernel n h k b (fun _ => a) (fun z v => |A z v|) z N /
            powLogScale l (multCount (ratioExp h k) l - 1) N| := (abs_div _ _).symm
      _ ≤ C := hN z hz
  · exact hβw.abs.mul_const C

end Certificate

end Grammar
