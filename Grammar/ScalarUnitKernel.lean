/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ConstantUnitAtlas
import Grammar.SignedReflectionGeneral

/-!
# The box kernel with a tangentially varying scalar phase unit

Unit A of consult #76 (`tide-log/gpt6_bigpicture_v76.md`): on a chart–stratum piece the phase's
tangential monomial factor makes the effective phase unit depend on the base point `z` even when the
chart unit is constant. The **scalar-unit box kernel**
`L_N^{q}(z) = ∫_{(0,b]^{n+1}} A(z,u) ∏u^h e^{−N q(z) ∏u^{2k}} du`
is the constant-unit kernel at the rescaled time `N q(z)` (`scalarBoxKernel`,
`scalarBoxKernel_eq_origPhaseIntegral`). A **positive time change** carries leading-term
certificates: `Z(N a)` has the certificate of `Z` with coefficient `a^{−λ} c`
(`HasLeadingTerm.comp_mul_const`, from `powLogScale(Na)/powLogScale(N) → a^{−λ}`), so the kernel has
the pointwise certificate with face coefficient `q(z)^{−λ} · boxFaceCoeff` at every base point where
`q(z) > 0` — no continuity of `q` needed (`hasLeadingTerm_scalarBoxKernel`). The eventual
normalised bound uniform on a compact base is obtained by **comparison**, not by uniform logarithm
algebra: for `N ≥ 0` and `q(z) ≥ q₀ > 0`, `|L_N^{q}(z)| ≤ L_N^{q₀}[|A|](z)`, a constant-unit kernel
covered by CCXXIX (`abs_scalarBoxKernel_le`, `eventually_abs_scalarBoxKernel_div_le`); hence the
**integrated certificate** against an integrable base weight on a compact base where `q` is
continuous and positive (`hasLeadingTerm_integral_scalarBoxKernel`).

Non-claims: `q` is a function of the base point only — an `n`-dependent unit is not handled; the
box is a positive cube (two-sided assembly is the next unit).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Positive time changes of leading-term certificates -/

section TimeChange

variable {lam : ℝ} {k : ℕ}

theorem powLogScale_mul_div {a N : ℝ} (ha : 0 < a) (hN : 1 < N) :
    powLogScale lam k (N * a) / powLogScale lam k N =
      a ^ (-lam) * (1 + Real.log a / Real.log N) ^ k := by
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hNl : N ^ (-lam) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  unfold powLogScale
  rw [Real.mul_rpow hN0.le ha.le, Real.log_mul hN0.ne' ha.ne', mul_assoc,
    mul_div_mul_left _ _ hNl, mul_div_assoc, ← div_pow, add_div, div_self hlog]

/-- The ratio of the power–log scales at `N a` and `N` tends to `a^{−λ}`. -/
theorem tendsto_powLogScale_mul_div {a : ℝ} (ha : 0 < a) (lam : ℝ) (k : ℕ) :
    Tendsto (fun N => powLogScale lam k (N * a) / powLogScale lam k N) atTop
      (𝓝 (a ^ (-lam))) := by
  have h1 : Tendsto (fun N : ℝ => 1 + Real.log a / Real.log N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  rw [add_zero] at h1
  have h2 := (tendsto_const_nhds (x := a ^ (-lam))).mul (h1.pow k)
  rw [one_pow, mul_one] at h2
  exact h2.congr' ((eventually_gt_atTop 1).mono fun N hN => (powLogScale_mul_div ha hN).symm)

/-- **Positive time change**: `Z(N a)` has the certificate of `Z` with coefficient `a^{−λ} c`. -/
theorem HasLeadingTerm.comp_mul_const {Z : ℝ → ℝ} {c : ℝ} (hZ : HasLeadingTerm Z c lam k) {a : ℝ}
    (ha : 0 < a) : HasLeadingTerm (fun N => Z (N * a)) (a ^ (-lam) * c) lam k := by
  have h1 : Tendsto (fun N => Z (N * a) / powLogScale lam k (N * a)) atTop (𝓝 c) :=
    hZ.comp (tendsto_id.atTop_mul_const ha)
  have h2 := h1.mul (tendsto_powLogScale_mul_div ha lam k)
  rw [mul_comm c] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 1, (tendsto_id.atTop_mul_const ha).eventually
    (eventually_gt_atTop (1 : ℝ))] with N hN hNa
  have hNa' : 1 < N * a := by simpa using hNa
  have hs := (powLogScale_pos lam k hNa').ne'
  rw [div_mul_div_comm, mul_comm (Z (N * a)), mul_div_mul_left _ _ hs]

end TimeChange

/-! ### The scalar-unit kernel -/

section Kernel

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (b : ℝ) {t : ℕ} (q : (Fin t → ℝ) → ℝ)
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **The scalar-unit box kernel**: the constant-unit kernel at the rescaled time `N q(z)`. -/
noncomputable def scalarBoxKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  boxKernel n h k 1 b A z (N * q z)

/-- The scalar-unit kernel is the prescribed-box integral with phase coefficient `q(z)`. -/
theorem scalarBoxKernel_eq_origPhaseIntegral (z : Fin t → ℝ) (N : ℝ) :
    scalarBoxKernel n h k b q A z N = origPhaseIntegral n h k (q z) N b (fun _ => 0) (A z) := by
  unfold scalarBoxKernel boxKernel origPhaseIntegral
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [mul_zero, add_zero, one_mul, mul_comm N (q z)]

/-- The scalar-unit face coefficient `q(z)^{−λ} · boxFaceCoeff`. -/
noncomputable def scalarBoxFaceCoeff (l : ℝ) (z : Fin t → ℝ) : ℝ :=
  q z ^ (-l) * boxFaceCoeff n h k 1 b A l z

variable {n h k b}

/-- **The pointwise certificate** at every base point with positive unit (no continuity of `q`). -/
theorem hasLeadingTerm_scalarBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {z : Fin t → ℝ} (hqz : 0 < q z) :
    HasLeadingTerm (scalarBoxKernel n h k b q A z) (scalarBoxFaceCoeff n h k b q A l z) l
      (multCount (ratioExp h k) l - 1) :=
  (hasLeadingTerm_boxKernel A hk one_pos hb hmin hatt hA z).comp_mul_const hqz

theorem measurableSet_piBox_Ioc_pos : MeasurableSet (piBox (n + 1) (Ioc (0 : ℝ) b)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- **Comparison with a constant-unit kernel**: for `N ≥ 0` and `q(z) ≥ q₀ > 0`,
`|L_N^{q}(z)| ≤ L_N^{q₀}[|A|](z)`. -/
theorem abs_scalarBoxKernel_le (hA : Continuous (Function.uncurry A)) {q₀ : ℝ}
    {z : Fin t → ℝ} (hqz : q₀ ≤ q z) {N : ℝ} (hN : 0 ≤ N) :
    |scalarBoxKernel n h k b q A z N| ≤ boxKernel n h k q₀ b (fun z u => |A z u|) z N := by
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  unfold boxKernel origPhaseIntegral
  have hAz : Continuous (A z) := continuous_amp_of_uncurry A hA z
  have hf : Continuous fun u : Fin (n + 1) → ℝ => |A z u * (∏ i, u i ^ h i) *
      Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i)) + q z * (Real.sqrt N * ∏ i, u i ^ k i) * 0)| := by
    fun_prop
  have hg : Continuous fun u : Fin (n + 1) → ℝ => |A z u| * (∏ i, u i ^ h i) *
      Real.exp (-(q₀ * N * ∏ i, u i ^ (2 * k i)) + q₀ * (Real.sqrt N * ∏ i, u i ^ k i) * 0) := by
    fun_prop
  refine abs_integral_le_integral_abs.trans (setIntegral_mono_on
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ hf)
    (integrableOn_piBox_Ioc_of_continuous _ _ _ _ hg) measurableSet_piBox_Ioc_pos fun u hu => ?_)
  have hu0 : ∀ i, 0 < u i := fun i => (hu i (mem_univ i)).1
  have hP : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
  have hQ : 0 ≤ ∏ i, u i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
  simp only [mul_zero, add_zero]
  rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) hP)
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqz hN) hQ

/-- **The eventual normalised bound, uniform on a compact base**, by comparison with the
constant-unit kernel of the lower unit bound `q₀` and the amplitude `|A|`. -/
theorem eventually_abs_scalarBoxKernel_div_le (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T) {q₀ : ℝ}
    (hq0 : 0 < q₀) (hq_lower : ∀ z ∈ T, q₀ ≤ q z) :
    ∃ C, ∀ᶠ N in atTop, ∀ z ∈ T,
      |scalarBoxKernel n h k b q A z N / powLogScale l (multCount (ratioExp h k) l - 1) N| ≤ C := by
  obtain ⟨C, hC⟩ := eventually_abs_boxKernel_div_le (A := fun z u => |A z u|) hk hq0 hb hl hmin hatt
    (continuous_abs.comp hA) hT
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 0] with N hN hN0 z hz
  rw [abs_div]
  calc |scalarBoxKernel n h k b q A z N| / |powLogScale l (multCount (ratioExp h k) l - 1) N|
      ≤ |boxKernel n h k q₀ b (fun z u => |A z u|) z N| /
          |powLogScale l (multCount (ratioExp h k) l - 1) N| :=
        div_le_div_of_nonneg_right
          ((abs_scalarBoxKernel_le q A hA (hq_lower z hz) hN0).trans (le_abs_self _))
          (abs_nonneg _)
    _ = |boxKernel n h k q₀ b (fun z u => |A z u|) z N /
          powLogScale l (multCount (ratioExp h k) l - 1) N| := (abs_div _ _).symm
    _ ≤ C := hN z hz

/-- The scalar-unit kernel is strongly measurable in the base point for a continuous unit. -/
theorem stronglyMeasurable_scalarBoxKernel (hA : Continuous (Function.uncurry A))
    (hq : Continuous q) (N : ℝ) :
    StronglyMeasurable fun z => scalarBoxKernel n h k b q A z N := by
  unfold scalarBoxKernel boxKernel origPhaseIntegral
  refine StronglyMeasurable.integral_prod_right' (f := fun p : (Fin t → ℝ) × (Fin (n + 1) → ℝ) =>
    A p.1 p.2 * (∏ i, p.2 i ^ h i) * Real.exp (-(1 * (N * q p.1) * ∏ i, p.2 i ^ (2 * k i)) +
      1 * (Real.sqrt (N * q p.1) * ∏ i, p.2 i ^ k i) * 0)) ?_
  refine Continuous.stronglyMeasurable ?_
  fun_prop

/-- **The integrated certificate over a compact base** with a continuous positive scalar unit:
`∫_T β_w(z) L_N^{q}(z) dz ⟶ (∫_T β_w(z) q(z)^{−λ} faceCoeff(z) dz) · N^{−λ}(log N)^{m−1}`. -/
theorem hasLeadingTerm_integral_scalarBoxKernel (hk : ∀ i, 0 < k i) (hb : 0 < b) {l : ℝ}
    (hl : 0 < l) (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : Continuous (Function.uncurry A)) {T : Set (Fin t → ℝ)} (hT : IsCompact T)
    (hq : Continuous q) (hq_pos : ∀ z ∈ T, 0 < q z) {βw : (Fin t → ℝ) → ℝ}
    (hβw : IntegrableOn βw T) :
    HasLeadingTerm (fun N => ∫ z in T, βw z * scalarBoxKernel n h k b q A z N)
      (∫ z in T, βw z * scalarBoxFaceCoeff n h k b q A l z) l
      (multCount (ratioExp h k) l - 1) := by
  rcases T.eq_empty_or_nonempty with hT0 | hne
  · simp only [hT0, Measure.restrict_empty, integral_zero_measure]
    exact hasLeadingTerm_zero _ _
  obtain ⟨z₀, hz₀, hmin₀⟩ := hT.exists_isMinOn hne hq.continuousOn
  have hq0 : 0 < q z₀ := hq_pos z₀ hz₀
  have hlower : ∀ z ∈ T, q z₀ ≤ q z := fun z hz => isMinOn_iff.1 hmin₀ z hz
  obtain ⟨C, hC⟩ := eventually_abs_scalarBoxKernel_div_le q A hk hb hl hmin hatt hA hT hq0 hlower
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  refine hasLeadingTerm_setIntegral_of_dominated_kernel (G := fun _ => C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N => hβw.aestronglyMeasurable.mul
      (stronglyMeasurable_scalarBoxKernel q A hA hq N).aestronglyMeasurable
  · exact (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz =>
      hasLeadingTerm_scalarBoxKernel q A hk hb hmin hatt hA (hq_pos z hz))
  · exact hC.mono fun N hN => (ae_restrict_iff' hTm).2 (Eventually.of_forall fun z hz => hN z hz)
  · exact hβw.abs.mul_const C

end Kernel

end Grammar
