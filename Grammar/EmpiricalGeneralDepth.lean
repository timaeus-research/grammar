/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFaceInner
import Grammar.EmpiricalFieldFamilyJets

/-!
# The empirical expansion in general dimension at a fixed depth (§20 Stage 5)

For smooth `η, ζ` on the closed unit box with `|ζ| ≤ M'`, the EMPIRICAL integrand
`η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}}` is split by the subset formula applied to the field family
`B_τ = η e^{τζ}` at the pointwise coupling `τ = √N v^k` (`empFaceTerm_pointwise`); the `J`-face term
integrates, after the `u/w` split of the box and the identity `√N (uw)^k = √(N w^{2k_K}) u^{k_J}`,
to a finite sum of empirical face integrals
`∫_w w^{h_K} · empFaceInner k_J (m+h_J) (τ ↦ G_{J,m}(τ; w)) (N w^{2k_K}) dw`
(★ `empFaceTerm_integral`, `integral_eq_sum_empFaceIntegral`). Each is expanded by the
parametrised face theorem with the two-regime estimate of `EmpiricalFaceInner` and the flat growth
of `EmpiricalFieldFamilyJets` (★ `empFace_bound`), and `reorganise'` collects everything into ONE
coefficient system `empCoeffAtDepth` on the ambient lattice `(2∏kᵢ)⁻¹ℕ` of logarithmic degree
`≤ d−1`:
★★★ `empirical_expansion_at_depth`:
`|∫_{(0,1]^d} η e^{√N v^k ζ} v^h e^{−N v^{2k}} − absSpectralSum Q (d−1) (empCoeffAtDepth) L N|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` for all `N ≥ 1`, under `pᵢ + hᵢ = 2kᵢL`.
The coefficients are face coefficient integrals of the Mellin moments of the face amplitudes of
`B_τ` — the paper's "derivatives of the fluctuation functions". Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Face data: spectrum and coefficients of the `J`-face -/

section FaceData

variable (k : Fin d → ℕ) (L : ℝ) (J : Finset (Fin d))

/-- The empirical face spectrum below the cutoff (empty for the empty face). -/
noncomputable def empΛJ (e : Fin d → ℕ) : Finset ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceSpectrum (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) L
  else ∅

/-- The empirical face coefficients of a field factor `G` (zero for the empty face). -/
noncomputable def empFaceCoef (e : Fin d → ℕ) (G : ℝ → ℝ) : ℝ → ℕ → ℝ :=
  if hJ : J.Nonempty then
    haveI := nonempty_subtype_inJ hJ
    faceInnerCoeff (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) G
  else fun _ _ => 0

theorem empΛJ_subset (hk : ∀ i, 0 < k i) (e : Fin d → ℕ) :
    empΛJ k L J e ⊆ latticeBelow (Qamb k) L := by
  unfold empΛJ
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    refine (faceSpectrum_subset (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i)
      (fun i => hk i) L).trans ?_
    exact latticeBelow_subset_of_dvd (QJ_pos k J hk) (Qamb_pos k hk) (QJ_dvd_Qamb k J) L
  · exact Finset.empty_subset _

theorem le_of_mem_empΛJ (e : Fin d → ℕ) {μ : ℝ} (hμ : μ ∈ empΛJ k L J e) : μ ≤ L := by
  unfold empΛJ at hμ
  split_ifs at hμ with hJ
  · have := nonempty_subtype_inJ hJ
    exact mem_faceSpectrum_le _ _ hμ
  · exact absurd hμ (Finset.notMem_empty μ)

/-- The face coefficients vanish on ambient lattice points outside the face spectrum. -/
theorem empFaceCoef_eq_zero (hk : ∀ i, 0 < k i) (e : Fin d → ℕ) (G : ℝ → ℝ) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) (hμJ : μ ∉ empΛJ k L J e) (j : ℕ) :
    empFaceCoef k J e G μ j = 0 := by
  have hlt : μ < L := ((mem_latticeBelow_iff (Qamb_pos k hk)).1 hμ).2
  unfold empFaceCoef
  unfold empΛJ at hμJ
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    rw [dif_pos hJ] at hμJ
    exact faceInnerCoeff_eq_zero _ _ G hlt hμJ j
  · rfl

/-- ★ The two-regime estimate for every face (empty spectrum and zero coefficients for the empty
face), with remainder linear in the growth constant. -/
theorem empFace_two_regime (hk : ∀ i, 0 < k i) (m : ℕ) (M' : ℝ) (hL : 0 < L) (e : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → ℝ), Measurable G → ∀ (A : ℝ), GrowthLE G A m M' →
      ∀ t : ℝ, 0 < t →
        |empFaceInner (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) G t -
            powLog (empΛJ k L J e) (DJ J) (empFaceCoef k J e G) t| ≤
          A * C * (t ^ (-L) * (1 + |log t|) ^ DJ J) := by
  by_cases hJ : J.Nonempty
  · have := nonempty_subtype_inJ hJ
    obtain ⟨C, hC0, hC⟩ := empFaceInner_two_regime (fun i : {i // inJ J i} => k i)
      (fun i : {i // inJ J i} => e i) (fun i => hk i) m M' hL
    refine ⟨C, hC0, fun G hGm A hG t ht => ?_⟩
    have h := hC G hGm A hG t ht
    have hΛ : empΛJ k L J e = faceSpectrum (fun i : {i // inJ J i} => k i)
        (fun i : {i // inJ J i} => e i) L := by unfold empΛJ; rw [dif_pos hJ]
    have hc : empFaceCoef k J e G = faceInnerCoeff (fun i : {i // inJ J i} => k i)
        (fun i : {i // inJ J i} => e i) G := by unfold empFaceCoef; rw [dif_pos hJ]
    rw [hΛ, hc]
    exact h
  · have := isEmpty_subtype_inJ_of_empty hJ
    obtain ⟨C, hC0, hC⟩ := empFaceInner_isEmpty_two_regime (fun i : {i // inJ J i} => k i)
      (fun i : {i // inJ J i} => e i) m M' hL
    refine ⟨C, hC0, fun G _ A hG t ht => ?_⟩
    have h := hC G A hG t ht
    unfold empΛJ empFaceCoef
    rw [dif_neg hJ, dif_neg hJ]
    simp only [powLog, Finset.sum_empty, sub_zero]
    have hA := hG.nonneg
    have h1 : (1 : ℝ) ≤ (1 + |log t|) ^ DJ J := one_le_pow₀ (by linarith [abs_nonneg (log t)])
    calc |empFaceInner (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i) G t|
        ≤ A * C * t ^ (-L) := h
      _ = A * C * (t ^ (-L) * 1) := by ring
      _ ≤ A * C * (t ^ (-L) * (1 + |log t|) ^ DJ J) := by
          gcongr

/-- The face coefficients are bounded by `A` times a constant. -/
theorem exists_abs_empFaceCoef_le (hk : ∀ i, 0 < k i) (m : ℕ) (M' : ℝ) (e : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → ℝ) (A : ℝ), GrowthLE G A m M' →
      ∀ μ ∈ empΛJ k L J e, ∀ j ∈ range (DJ J + 1), |empFaceCoef k J e G μ j| ≤ A * C := by
  by_cases hJ : J.Nonempty
  · have := nonempty_subtype_inJ hJ
    refine ⟨innerCoeffTotal ((fun i : {i // inJ J i} => k i) ∘ (faceEquiv _).symm)
      ((fun i : {i // inJ J i} => e i) ∘ (faceEquiv _).symm) m M', innerCoeffTotal_nonneg _ _ _ _,
      fun G A hG μ hμ j hj => ?_⟩
    unfold empΛJ at hμ
    rw [dif_pos hJ] at hμ
    unfold empFaceCoef
    rw [dif_pos hJ]
    exact abs_faceInnerCoeff_le (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => e i)
      (fun i => hk i) hG hμ hj
  · refine ⟨0, le_rfl, fun G A hG μ hμ j _ => ?_⟩
    unfold empΛJ at hμ
    rw [dif_neg hJ] at hμ
    exact absurd hμ (Finset.notMem_empty μ)

theorem measurable_empFaceCoef_comp {α : Type*} [MeasurableSpace α] (e : Fin d → ℕ)
    {G : α → ℝ → ℝ} (hG : Measurable (Function.uncurry G)) (μ : ℝ) (j : ℕ) :
    Measurable fun w => empFaceCoef k J e (G w) μ j := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    exact measurable_faceInnerCoeff_comp _ _ hG μ j
  · exact measurable_const

end FaceData

/-! ### The face-term integral -/

variable (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ)

/-- The pointwise coupling `τ = √N v^k`. -/
noncomputable def coupling (k : Fin d → ℕ) (N : ℝ) (v : Fin d → ℝ) : ℝ := Real.sqrt N * mono k v

theorem continuous_coupling (k : Fin d → ℕ) (N : ℝ) : Continuous (coupling k N) :=
  continuous_const.mul (continuous_mono k)

/-- The `(J, m)` empirical face integral. -/
noncomputable def empFaceIntegral (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∫ w in box {i // ¬ inJ J i} 1, mono (fun i : {i // ¬ inJ J i} => h i) w *
    empFaceInner (fun i : {i // inJ J i} => k i) (fun i : {i // inJ J i} => m i + h i)
      (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
      (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w)

/-- The `(J, m)` summand of the face split at the pointwise coupling. -/
noncomputable def empS (J : Finset (Fin d)) (N : ℝ) (m : Fin d → ℕ) (v : Fin d → ℝ) : ℝ :=
  tayMono m v *
    remList p (lK J) (pdMulti m (lJ J) (fieldFam η ζ (coupling k N v))) (zeroL (lJ J) v) *
    mono h v * exp (-N * mono (fun i => 2 * k i) v)

variable {η ζ}

theorem continuous_remList_pdMulti_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Continuous fun z : ℝ × (Fin d → ℝ) =>
      remList p (lK J) (pdMulti m (lJ J) (fieldFam η ζ z.1)) z.2 := by
  have h1 : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      pdMulti m (lJ J) (fun v => fieldFam η ζ z.1 v) z.2 :=
    contDiff_pdMulti_slice (contDiff_fieldFam_joint hη hζ) m (lJ J)
  have h2 : ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) =>
      remList p (lK J) (fun v => pdMulti m (lJ J) (fun v => fieldFam η ζ z.1 v) v) z.2 :=
    contDiff_remList_slice p h1 (lK J)
  exact h2.continuous

theorem continuous_empS (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (J : Finset (Fin d)) (N : ℝ)
    (m : Fin d → ℕ) : Continuous (empS η ζ h k p J N m) := by
  unfold empS
  refine (((continuous_tayMono m).mul ?_).mul (continuous_mono h)).mul
    (continuous_exp.comp (continuous_const.mul (continuous_mono _)))
  exact (continuous_remList_pdMulti_fieldFam p hη hζ J m).comp
    ((continuous_coupling k N).prodMk (continuous_zeroL _))

/-- The `J`-face term at the pointwise coupling is the sum of the `(J, m)` summands. -/
theorem empFaceTerm_pointwise (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (J : Finset (Fin d))
    (N : ℝ) (v : Fin d → ℝ) :
    faceOp p J (List.finRange d) (fieldFam η ζ (coupling k N v)) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) =
      ∑ m ∈ idxL p (lJ J), empS η ζ h k p J N m v := by
  have hdisj : ∀ i ∈ lJ J, i ∉ lK J := fun i hi h' => (mem_lK J).1 h' ((mem_lJ J).1 hi)
  have hF := contDiff_fieldFam hη hζ (coupling k N v)
  rw [faceOp_finRange_eq p J hF, tayList_eq_sum p (contDiff_remList p hF _) (nodup_lJ J),
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold empS
  rw [pdMulti_remList p hF m hdisj]

/-- ★ **The empirical face-term integral**: the `J`-face term of the subset formula at the
pointwise coupling integrates to the weighted sum of the `(J, m)` empirical face integrals. -/
theorem empFaceTerm_integral (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (J : Finset (Fin d))
    {N : ℝ} (hN : 0 ≤ N) :
    ∫ v in box (Fin d) 1, faceOp p J (List.finRange d) (fieldFam η ζ (coupling k N v)) v *
        mono h v * exp (-N * mono (fun i => 2 * k i) v) =
      ∑ m ∈ idxL p (lJ J), faceW J m * empFaceIntegral η ζ h k p J m N := by
  have hSint : ∀ m, IntegrableOn (empS η ζ h k p J N m) (box (Fin d) 1) := fun m =>
    integrableOn_box_of_continuous (continuous_empS h k p hη hζ J N m) 1
  rw [setIntegral_congr_fun (measurableSet_box 1) fun v _ =>
    empFaceTerm_pointwise h k p hη hζ J N v, integral_finsetSum _ fun m _ => hSint m]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [integral_box_split J 1 _ (hSint m)]
  unfold empFaceIntegral
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := {i // ¬ inJ J i}) 1) fun w hw => ?_
  have hwpos : ∀ i, 0 < w i := pos_of_mem_box hw
  have hmk : 0 ≤ mono (fun i : {i // ¬ inJ J i} => k i) w := (mono_pos _ hwpos).le
  have hsq : Real.sqrt (N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) =
      Real.sqrt N * mono (fun i : {i // ¬ inJ J i} => k i) w := by
    have h2 : mono (fun i : {i // ¬ inJ J i} => 2 * k i) w =
        mono (fun i : {i // ¬ inJ J i} => k i) w * mono (fun i : {i // ¬ inJ J i} => k i) w := by
      rw [mono_mul_mono]
      congr 1
      funext i
      ring
    rw [h2, Real.sqrt_mul hN, Real.sqrt_mul_self hmk]
  unfold empFaceInner
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box (ι := {i // inJ J i}) 1) fun u _ => ?_
  unfold empS coupling faceAmp faceW
  rw [tayMono_glue p J hm, zeroL_lJ_glue, hsq]
  simp only [mono_glue]
  rw [← mono_mul_mono (fun i : {i // inJ J i} => m i) (fun i => h i) u]
  have harg1 : Real.sqrt N * (mono (fun i : {i // inJ J i} => k i) u *
      mono (fun i : {i // ¬ inJ J i} => k i) w) =
      Real.sqrt N * mono (fun i : {i // ¬ inJ J i} => k i) w *
        mono (fun i : {i // inJ J i} => k i) u := by
    ring
  have harg2 : -N * (mono (fun i : {i // inJ J i} => 2 * k i) u *
      mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) =
      -(N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w) *
        mono (fun i : {i // inJ J i} => 2 * k i) u := by
    ring
  rw [harg1, harg2]
  ring

/-- The full integral at the pointwise coupling as a sum of empirical face integrals over
`faceIndex`. -/
theorem integral_eq_sum_empFaceIntegral (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {N : ℝ}
    (hN : 0 ≤ N) :
    ∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) =
      ∑ x ∈ faceIndex p, faceW x.1 x.2 * empFaceIntegral η ζ h k p x.1 x.2 N := by
  have hpt : ∀ v : Fin d → ℝ, fieldFam η ζ (coupling k N v) v * mono h v *
      exp (-N * mono (fun i => 2 * k i) v) =
      ∑ J ∈ (univ : Finset (Finset (Fin d))),
        faceOp p J (List.finRange d) (fieldFam η ζ (coupling k N v)) v * mono h v *
          exp (-N * mono (fun i => 2 * k i) v) := by
    intro v
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.powerset_univ, ← List.toFinset_finRange,
      ← sum_faceOp p (List.nodup_finRange d) _ v]
  have hint : ∀ J ∈ (univ : Finset (Finset (Fin d))), IntegrableOn
      (fun v => faceOp p J (List.finRange d) (fieldFam η ζ (coupling k N v)) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v)) (box (Fin d) 1) := fun J _ => by
    have hsum : IntegrableOn (fun v => ∑ m ∈ idxL p (lJ J), empS η ζ h k p J N m v)
        (box (Fin d) 1) :=
      integrable_finsetSum _ fun m _ =>
        integrableOn_box_of_continuous (continuous_empS h k p hη hζ J N m) 1
    exact hsum.congr (Eventually.of_forall fun v => (empFaceTerm_pointwise h k p hη hζ J N v).symm)
  rw [setIntegral_congr_fun (measurableSet_box 1) fun v _ => hpt v, integral_finsetSum _ hint,
    faceIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [empFaceTerm_integral h k p hη hζ J hN]

/-! ### The per-face bound -/

/-- The face expansion of the `(J, m)` term: exponents `μ ∈ empΛJ`, log degree `DJ`. -/
noncomputable def empFaceExpansion (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (L : ℕ)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (N : ℝ) : ℝ :=
  ∑ μ ∈ empΛJ k L J (fun i => m i + h i), N ^ (-μ) * ∑ j ∈ range (DJ J + 1),
    ∑ q ∈ range (j + 1), (j.choose q) * log N ^ q *
      faceCoeffInt (fun w => empFaceCoef k J (fun i => m i + h i)
          (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j)
        (fun i : {i // ¬ inJ J i} => h i) (fun i : {i // ¬ inJ J i} => 2 * k i) 1 μ (j - q)

/-- ★ **The per-face bound, UNIFORM in the field data**: the constant depends only on
`(h, k, p, L, M', J, m)`; for every smooth `(η, ζ)` with the jet bound of constant `C` the `(J, m)`
face integral is within `C · K (1 + log N)^{DJ} N^{−L}` of its face expansion. -/
theorem empFace_bound_uniform (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) (J : Finset (Fin d))
    (m : Fin d → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ p 1 C M' → m ∈ idxL p (lJ J) → ∀ N : ℝ, 1 ≤ N →
        |empFaceIntegral η ζ h k p J m N - empFaceExpansion η ζ h k p L J m N| ≤
          C * K * (1 + log N) ^ DJ J * N ^ (-(L : ℝ)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨C₂, hC₂0, hC₂⟩ := empFace_two_regime k (L : ℝ) J hk (∑ i, p i) M' hL' (fun i => m i + h i)
  obtain ⟨Cc, hCc0, hCc⟩ :=
    exists_abs_empFaceCoef_le k (L : ℝ) J hk (∑ i, p i) M' (fun i => m i + h i)
  set P : ℝ := ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => by positivity
  set R : ℝ := faceRemWeight (fun i : {i // ¬ inJ J i} => p i) (fun i : {i // ¬ inJ J i} => h i)
    (fun i : {i // ¬ inJ J i} => 2 * k i) 1 L (DJ J) with hR
  have hR0 : 0 ≤ R := faceRemWeight_nonneg _ _ _ _ _ _
  refine ⟨C₂ * P * R, by positivity, fun η ζ hη hζ C hC hm N hN => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  have hCg : ∀ w ∈ box {i // ¬ inJ J i} 1, GrowthLE (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
        mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M' :=
    fun w hw => growthLE_faceAmp_fieldFam_of_bound hη hζ one_pos hC hp0 J m hm hw
  have hGm := measurable_uncurry_faceAmp_fieldFam hη hζ p J m
  have hT : Measurable fun w : {i // ¬ inJ J i} → ℝ =>
      N * mono (fun i : {i // ¬ inJ J i} => 2 * k i) w :=
    measurable_const.mul (measurable_mono _)
  have key := face_expansion_param (ι := {i // ¬ inJ J i})
    (Z := fun w t => empFaceInner (fun i : {i // inJ J i} => k i)
      (fun i : {i // inJ J i} => m i + h i) (fun τ => faceAmp p J (fieldFam η ζ τ) m w) t)
    (c := fun w => empFaceCoef k J (fun i => m i + h i) (fun τ => faceAmp p J (fieldFam η ζ τ) m w))
    (p := fun i => p i) (h := fun i => h i) (a := fun i => 2 * k i) (b := 1)
    (M := P * C * Cc) (C := C₂ * (P * C)) (L := (L : ℝ))
    (Λ := empΛJ k (L : ℝ) J (fun i => m i + h i)) (D := DJ J) one_pos (by positivity)
    (measurable_empFaceInner_comp _ _ hGm hT).aestronglyMeasurable
    (fun μ _ j _ => (measurable_empFaceCoef_comp k J _ hGm μ j).aestronglyMeasurable)
    (fun μ hμ j hj w hw => ?_) (fun w hw t ht => ?_)
    (fun μ hμ => le_of_mem_empΛJ k (L : ℝ) J _ hμ) (fun i => convergence_of_eq (hp i)) hN
  · unfold empFaceIntegral empFaceExpansion
    refine key.trans (le_of_eq ?_)
    rw [hR]
    ring
  · have hgrow := hCg w hw
    calc |empFaceCoef k J (fun i => m i + h i) (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j|
        ≤ (P * C * mono (fun i : {i // ¬ inJ J i} => p i) w) * Cc :=
          hCc _ _ hgrow μ hμ j hj
      _ = _ := by ring
  · have hgrow := hCg w hw
    have h2 := hC₂ _ (hGm.comp measurable_prodMk_left) _ hgrow t ht
    refine h2.trans (le_of_eq ?_)
    ring

/-- ★ **The per-face bound** (existential form, fixed field data). -/
theorem empFace_bound (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {M' : ℝ}
    (hζM : ∀ v ∈ closedBox d 1, |ζ v| ≤ M') (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (J : Finset (Fin d))
    (m : Fin d → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ (m ∈ idxL p (lJ J) → ∀ N : ℝ, 1 ≤ N →
      |empFaceIntegral η ζ h k p J m N - empFaceExpansion η ζ h k p L J m N| ≤
        K * (1 + log N) ^ DJ J * N ^ (-(L : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldJetBound hη hζ hζM p
  obtain ⟨K, hK0, hK⟩ := empFace_bound_uniform h k p hk hL hp hp0 M' J m
  refine ⟨C * K, by positivity, fun hm N hN => hK η ζ hη hζ C hC hm N hN⟩

/-! ### The assembly -/

/-- The reorganisation of the face sums into one coefficient system, for face coefficient data
`I s μ j q` depending on both the logarithmic degree `j` and the power `q`. -/
theorem reorganise' {σ : Type*} (S : Finset σ) (w : σ → ℝ) (Λ : σ → Finset ℝ) (Ds : σ → ℕ)
    (I : σ → ℝ → ℕ → ℕ → ℝ) {Q D : ℕ} {L N : ℝ}
    (hΛ : ∀ s ∈ S, Λ s ⊆ latticeBelow Q L)
    (hI : ∀ s ∈ S, ∀ μ ∈ latticeBelow Q L, μ ∉ Λ s → ∀ j q, I s μ j q = 0)
    (hD : ∀ s ∈ S, Ds s ≤ D) :
    ∑ s ∈ S, w s * ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        (j.choose q) * log N ^ q * I s μ j q =
      absSpectralSum Q D (fun μ q => ∑ s ∈ S, w s * ∑ j ∈ Finset.Ico q (Ds s + 1),
        (j.choose q) * I s μ j q) L N := by
  unfold absSpectralSum
  have hext : ∀ s ∈ S, ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
      (j.choose q) * log N ^ q * I s μ j q =
      ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        (j.choose q) * log N ^ q * I s μ j q := by
    intro s hs
    refine Finset.sum_subset (hΛ s hs) fun μ hμ hμ' => ?_
    simp [hI s hs μ hμ hμ']
  have htri : ∀ s ∈ S, ∀ μ : ℝ, ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
      (j.choose q) * log N ^ q * I s μ j q =
      ∑ q ∈ range (D + 1), (∑ j ∈ Finset.Ico q (Ds s + 1), (j.choose q) * I s μ j q) *
        log N ^ q := by
    intro s hs μ
    rw [sum_triangle]
    have hsub : range (Ds s + 1) ⊆ range (D + 1) :=
      Finset.range_mono (Nat.succ_le_succ (hD s hs))
    rw [Finset.sum_subset hsub fun q _ hq => ?_]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · have : Ds s + 1 ≤ q := by simpa using hq
      simp [Finset.Ico_eq_empty_of_le this]
  calc ∑ s ∈ S, w s * ∑ μ ∈ Λ s, N ^ (-μ) * ∑ j ∈ range (Ds s + 1), ∑ q ∈ range (j + 1),
        (j.choose q) * log N ^ q * I s μ j q
      = ∑ s ∈ S, ∑ μ ∈ latticeBelow Q L, w s * (N ^ (-μ) * ∑ q ∈ range (D + 1),
          (∑ j ∈ Finset.Ico q (Ds s + 1), (j.choose q) * I s μ j q) * log N ^ q) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hext s hs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [htri s hs μ]
    _ = ∑ μ ∈ latticeBelow Q L, N ^ (-μ) * ∑ q ∈ range (D + 1),
          (∑ s ∈ S, w s * ∑ j ∈ Finset.Ico q (Ds s + 1), (j.choose q) * I s μ j q) *
            log N ^ q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        have hx : ∀ x ∈ S, w x * (N ^ (-μ) * ∑ q ∈ range (D + 1),
            (∑ j ∈ Finset.Ico q (Ds x + 1), (j.choose q) * I x μ j q) * log N ^ q) =
            ∑ q ∈ range (D + 1), N ^ (-μ) * ((w x * ∑ j ∈ Finset.Ico q (Ds x + 1),
              (j.choose q) * I x μ j q) * log N ^ q) := by
          intro x _
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          ring
        rw [Finset.sum_congr rfl hx, Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]

/-- ★ **The empirical coefficient system at depth `p`** on the ambient lattice: for each face
`(J, m)`, the binomially reindexed face coefficient integrals of the empirical face coefficients of
the face amplitude family. -/
noncomputable def empCoeffAtDepth (η ζ : (Fin d → ℝ) → ℝ) (h k p : Fin d → ℕ) (μ : ℝ) (q : ℕ) :
    ℝ :=
  ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1), (j.choose q) *
    faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)

theorem faceCoeffInt_eq_zero_of_zero {ι : Type*} [Fintype ι] {G : (ι → ℝ) → ℝ} (hG : ∀ w, G w = 0)
    (h a : ι → ℕ) (b μ : ℝ) (e : ℕ) : faceCoeffInt G h a b μ e = 0 := by
  unfold faceCoeffInt
  rw [setIntegral_congr_fun (measurableSet_box b) (g := fun _ => (0 : ℝ)) fun w _ => by
    rw [hG w, zero_mul, zero_mul, zero_mul]]
  simp

/-- The face expansions sum to the ambient `absSpectralSum` of `empCoeffAtDepth`. -/
theorem sum_empFaceExpansion_eq (hk : ∀ i, 0 < k i) (L : ℕ) (N : ℝ) :
    ∑ x ∈ faceIndex p, faceW x.1 x.2 * empFaceExpansion η ζ h k p L x.1 x.2 N =
      absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepth η ζ h k p) L N := by
  unfold empFaceExpansion empCoeffAtDepth
  exact reorganise' (faceIndex p) (fun x => faceW x.1 x.2)
    (fun x => empΛJ k (L : ℝ) x.1 (fun i => x.2 i + h i)) (fun x => DJ x.1)
    (fun x μ j q => faceCoeffInt (fun w => empFaceCoef k x.1 (fun i => x.2 i + h i)
        (fun τ => faceAmp p x.1 (fieldFam η ζ τ) x.2 w) μ j)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q))
    (fun x _ => empΛJ_subset k (L : ℝ) x.1 hk _)
    (fun x _ μ hμ hμJ j q => faceCoeffInt_eq_zero_of_zero
      (fun w => empFaceCoef_eq_zero k (L : ℝ) x.1 hk _ _ hμ hμJ j) _ _ _ _ _)
    (fun x _ => DJ_le x.1)

/-- ★★★ **The empirical expansion at depth `p`, UNIFORMLY in the field data**: the constant
depends only on `(h, k, p, L, M')`; for every smooth `(η, ζ)` with the jet bound
`|∂^m(η e^{τζ})| ≤ C (1+τ)^{|p|} e^{M'τ}` (`m ≤ p`),
`|∫_{(0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`
`  − absSpectralSum Q (d−1) (empCoeffAtDepth η ζ h k p) L N|`
`  ≤ C K₀ N^{−L} (1 + log N)^{d−1}` for all `N ≥ 1`. -/
theorem empirical_expansion_at_depth_uniform (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) (M' : ℝ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (η ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ η → ContDiff ℝ ∞ ζ →
      ∀ C : ℝ, FieldJetBound η ζ p 1 C M' → ∀ N : ℝ, 1 ≤ N →
        |(∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
            exp (-N * mono (fun i => 2 * k i) v)) -
          absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepth η ζ h k p) L N| ≤
          C * K₀ * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  choose K hK0 hK using fun (J : Finset (Fin d)) (m : Fin d → ℕ) =>
    empFace_bound_uniform h k p hk hL hp hp0 M' J m
  refine ⟨∑ x ∈ faceIndex p, faceW x.1 x.2 * K x.1 x.2,
    Finset.sum_nonneg fun x _ => mul_nonneg (faceW_nonneg _ _) (hK0 _ _),
    fun η ζ hη hζ C hC N hN => ?_⟩
  have hC0 : 0 ≤ C := hC.nonneg zero_le_one
  have hlog : 0 ≤ log N := log_nonneg hN
  rw [integral_eq_sum_empFaceIntegral h k p hη hζ (by linarith),
    ← sum_empFaceExpansion_eq h k p hk L N, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  have hb' := hK x.1 x.2 η ζ hη hζ C hC hm N hN
  have hpow : (1 + log N) ^ DJ x.1 ≤ (1 + log N) ^ (d - 1) :=
    pow_le_pow_right₀ (by linarith) (DJ_le x.1)
  have hW := faceW_nonneg x.1 x.2
  have hK0' := hK0 x.1 x.2
  rw [← mul_sub, abs_mul, abs_of_nonneg hW]
  calc faceW x.1 x.2 *
        |empFaceIntegral η ζ h k p x.1 x.2 N - empFaceExpansion η ζ h k p L x.1 x.2 N|
      ≤ faceW x.1 x.2 * (C * K x.1 x.2 * (1 + log N) ^ DJ x.1 * N ^ (-(L : ℝ))) :=
        mul_le_mul_of_nonneg_left hb' hW
    _ ≤ faceW x.1 x.2 * (C * K x.1 x.2 * (1 + log N) ^ (d - 1) * N ^ (-(L : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- ★★★ **The empirical expansion in general dimension at depth `p`**: for smooth `η, ζ` on the
closed unit box with `|ζ| ≤ M'`, `kᵢ > 0`, Jacobian exponents `h`, cutoff `L ≥ 1` and depths
`pᵢ + hᵢ = 2kᵢL`,
`|∫_{(0,1]^d} η(v) e^{√N v^k ζ(v)} v^h e^{−N v^{2k}} dv`
`  − ∑_{μ ∈ Λ^Q_L} N^{−μ} ∑_{q ≤ d−1} C_{μ,q} (log N)^q|`
`  ≤ K N^{−L} (1 + log N)^{d−1}` for all `N ≥ 1`, `Q = 2∏kᵢ`, with the explicit coefficient system
`C = empCoeffAtDepth η ζ h k p` (face coefficient integrals of the Mellin-moment coefficients of
the face amplitudes of the field family). -/
theorem empirical_expansion_at_depth (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {M' : ℝ}
    (hζM : ∀ v ∈ closedBox d 1, |ζ v| ≤ M') (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) :
    ∃ K : ℝ, ∀ N : ℝ, 1 ≤ N →
      |(∫ v in box (Fin d) 1, fieldFam η ζ (coupling k N v) v * mono h v *
          exp (-N * mono (fun i => 2 * k i) v)) -
        absSpectralSum (Qamb k) (d - 1) (empCoeffAtDepth η ζ h k p) L N| ≤
        K * (N ^ (-(L : ℝ)) * (1 + log N) ^ (d - 1)) := by
  obtain ⟨C, _, hC⟩ := exists_fieldJetBound hη hζ hζM p
  obtain ⟨K₀, _, hK₀⟩ := empirical_expansion_at_depth_uniform h k p hk hL hp hp0 M'
  exact ⟨C * K₀, fun N hN => hK₀ η ζ hη hζ C hC N hN⟩

end SmoothEngine

end Grammar
