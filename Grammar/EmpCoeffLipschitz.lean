/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FieldJetDifference
import Grammar.EmpiricalUniform
import Grammar.RectRemainderUniform
import Grammar.CubeJets
import Grammar.SmoothStratumJetDependence
import Grammar.EmpiricalPieceExpansion

/-!
# Every empirical cube coefficient is Lipschitz on jet balls

`CubeCoeffLipschitz` proved the bounded-jet Lipschitz estimate for the TOP coefficient
`empCoeffRect η ζ h k b μ (c−1)` through its identification with a population coefficient
(replacement rule, deep vanishing). Here the estimate is proved for EVERY canonical coefficient
`empCoeffRect η ζ h k b μ q`, directly from the face formula
`empCoeffAtDepth = Σ_faces faceW · Σ_j C(j,q) · faceCoeffInt G_j`,
`G_j w = empFaceCoef (τ ↦ faceAmp (η e^{τζ}) w) μ j` (see `EmpiricalGeneralDepth`):
every ingredient is linear in the field family (`faceAmp_sub`, `empFaceCoef_sub` through the
Mellin moments, `faceCoeffInt_sub`), and the difference family `η e^{τζ₁} − η e^{τζ₂}` has the
uniform envelope `C ε (1+τ)^{2|p|+1} e^{(B+E)τ}` of `FieldJetDifference`, so the coefficient bound
`exists_abs_empFaceCoef_le` (linear in the growth constant) applied to the difference gives
★★ `exists_empCoeffRect_sub_le`: one Lipschitz constant per `(μ, q)` on every jet ball. No deep
vanishing and no positivity of `μ` is needed (consult #153, programme 1, Stages 1–2).
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η : (Fin d → ℝ) → ℝ} {h k : Fin d → ℕ}

/-! ### Linearity of the face ingredients -/

theorem GrowthLE.mono_exp {G : ℝ → ℝ} {A : ℝ} {m m' : ℕ} {M : ℝ} (h : GrowthLE G A m M)
    (hm : m ≤ m') : GrowthLE G A m' M := by
  intro τ hτ
  refine (h τ hτ).trans ?_
  have hA := h.nonneg
  have : (1 + τ) ^ m ≤ (1 + τ) ^ m' := pow_le_pow_right₀ (by linarith) hm
  gcongr

theorem mellinMom_sub {G₁ G₂ : ℝ → ℝ} (hG₁m : Measurable G₁) (hG₂m : Measurable G₂) {A₁ A₂ : ℝ}
    {m : ℕ} {M : ℝ} (hG₁ : GrowthLE G₁ A₁ m M) (hG₂ : GrowthLE G₂ A₂ m M) {μ : ℝ} (hμ : 0 < μ)
    (ℓ : ℕ) : mellinMom (fun τ => G₁ τ - G₂ τ) μ ℓ = mellinMom G₁ μ ℓ - mellinMom G₂ μ ℓ := by
  unfold mellinMom
  rw [← integral_sub (integrableOn_momKernel hG₁m hG₁ hμ ℓ) (integrableOn_momKernel hG₂m hG₂ hμ ℓ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  unfold momKernel
  beta_reduce
  ring

theorem empInnerCoeff_sub {n : ℕ} (k e : Fin (n + 1) → ℕ) {G₁ G₂ : ℝ → ℝ} (hG₁m : Measurable G₁)
    (hG₂m : Measurable G₂) {A₁ A₂ : ℝ} {m : ℕ} {M : ℝ} (hG₁ : GrowthLE G₁ A₁ m M)
    (hG₂ : GrowthLE G₂ A₂ m M) {μ : ℝ} (hμ : 0 < μ) (q : ℕ) :
    empInnerCoeff k e (fun τ => G₁ τ - G₂ τ) μ q =
      empInnerCoeff k e G₁ μ q - empInnerCoeff k e G₂ μ q := by
  unfold empInnerCoeff
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mellinMom_sub hG₁m hG₂m hG₁ hG₂ hμ]
  ring

theorem faceInnerCoeff_sub {ι : Type*} [Fintype ι] [Nonempty ι] (k e : ι → ℕ) {G₁ G₂ : ℝ → ℝ}
    (hG₁m : Measurable G₁) (hG₂m : Measurable G₂) {A₁ A₂ : ℝ} {m : ℕ} {M : ℝ}
    (hG₁ : GrowthLE G₁ A₁ m M) (hG₂ : GrowthLE G₂ A₂ m M) {μ : ℝ} (hμ : 0 < μ) (q : ℕ) :
    faceInnerCoeff k e (fun τ => G₁ τ - G₂ τ) μ q =
      faceInnerCoeff k e G₁ μ q - faceInnerCoeff k e G₂ μ q := by
  unfold faceInnerCoeff
  exact empInnerCoeff_sub _ _ hG₁m hG₂m hG₁ hG₂ hμ q

theorem empFaceCoef_sub (k : Fin d → ℕ) (J : Finset (Fin d)) (e : Fin d → ℕ) {G₁ G₂ : ℝ → ℝ}
    (hG₁m : Measurable G₁) (hG₂m : Measurable G₂) {A₁ A₂ : ℝ} {m : ℕ} {M : ℝ}
    (hG₁ : GrowthLE G₁ A₁ m M) (hG₂ : GrowthLE G₂ A₂ m M) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    empFaceCoef k J e (fun τ => G₁ τ - G₂ τ) μ j =
      empFaceCoef k J e G₁ μ j - empFaceCoef k J e G₂ μ j := by
  unfold empFaceCoef
  split_ifs with hJ
  · have := nonempty_subtype_inJ hJ
    exact faceInnerCoeff_sub _ _ hG₁m hG₂m hG₁ hG₂ hμ j
  · simp

theorem pos_of_mem_empΛJ (hk : ∀ i, 0 < k i) {L : ℝ} {J : Finset (Fin d)} {e : Fin d → ℕ} {μ : ℝ}
    (hμ : μ ∈ empΛJ k L J e) : 0 < μ := by
  unfold empΛJ at hμ
  split_ifs at hμ with hJ
  · have := nonempty_subtype_inJ hJ
    unfold faceSpectrum innerSpectrumBelow at hμ
    exact mem_innerSpectrum_pos _ _ (fun _ => hk _) (Finset.mem_filter.1 hμ).1
  · exact absurd hμ (Finset.notMem_empty _)

theorem faceAmp_sub (p : Fin d → ℕ) (J : Finset (Fin d)) {F G : (Fin d → ℝ) → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (m : Fin d → ℕ) (w : {i // ¬ inJ J i} → ℝ) :
    faceAmp p J (fun v => F v - G v) m w = faceAmp p J F m w - faceAmp p J G m w := by
  unfold faceAmp
  rw [pdMulti_sub hF hG m (lJ J)]
  have h := remList_add_smul p (contDiff_pdMulti hF m (lJ J)) (contDiff_pdMulti hG m (lJ J)) 1 (-1)
    (lK J)
  have hfun : (fun v => (1 : ℝ) * pdMulti m (lJ J) F v + (-1) * pdMulti m (lJ J) G v) =
      fun v => pdMulti m (lJ J) F v - pdMulti m (lJ J) G v := funext fun v => by ring
  rw [hfun] at h
  rw [h]
  ring

theorem faceCoeffInt_sub {ι : Type*} [Fintype ι] {G₁ G₂ : (ι → ℝ) → ℝ} (h a : ι → ℕ) (b μ : ℝ)
    (e : ℕ)
    (h₁ : IntegrableOn (fun w => G₁ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b))
    (h₂ : IntegrableOn (fun w => G₂ w * mono h w * mono a w ^ (-μ) * logSum a w ^ e) (box ι b)) :
    faceCoeffInt (fun w => G₁ w - G₂ w) h a b μ e =
      faceCoeffInt G₁ h a b μ e - faceCoeffInt G₂ h a b μ e := by
  have hs := faceCoeffInt_add_smul (1 : ℝ) (-1) h a b μ e h₁ h₂
  have hfun : (fun w => (1 : ℝ) * G₁ w + (-1) * G₂ w) = fun w => G₁ w - G₂ w :=
    funext fun w => by ring
  rw [hfun] at hs
  rw [hs]
  ring

/-! ### The Lipschitz estimate on the unit box -/

/-- ★★ **Every coefficient at an admissible depth is Lipschitz on jet balls** (unit box): for
`μ ∈ Λ^Q_L` and every `q`, one constant `K` with
`|empCoeffAtDepth η ζ₁ h k p μ q − empCoeffAtDepth η ζ₂ h k p μ q| ≤ K ε` whenever the jets of
`ζ₂` of order `≤ |p|` are bounded by `B` and those of `ζ₁, ζ₂` are `ε`-close (`ε ≤ E`). -/
theorem exists_empCoeffAtDepth_sub_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {L : ℕ}
    {p : Fin d → ℕ} (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i) {μ : ℝ}
    (hμ : μ ∈ latticeBelow (Qamb k) L) (q : ℕ) {B E : ℝ} (hB : 0 ≤ B) (hE : 1 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (∑ i, p i) (closedBox d 1) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ E →
      JetClose (∑ i, p i) (closedBox d 1) ζ₁ ζ₂ ε →
      |empCoeffAtDepth η ζ₁ h k p μ q - empCoeffAtDepth η ζ₂ h k p μ q| ≤ K * ε := by
  have hQ := Qamb_pos k hk
  set P2 : ℕ := 2 * ∑ i, p i + 1 with hP2
  obtain ⟨Cd, hCd0, hCd⟩ := exists_fieldFam_sub_bound hη p (b := 1) hB hE
  obtain ⟨Cf, hCf0, hCf⟩ := fieldJetBound_of_jetBoundOn hη p (b := 1) (B := B + E) (by linarith)
  choose Cc hCc0 hCc using fun (J : Finset (Fin d)) (e : Fin d → ℕ) =>
    exists_abs_empFaceCoef_le k (L : ℝ) J hk P2 (B + E) e
  set Pf : Finset (Fin d) → ℝ := fun J => ∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹
    with hPf
  have hPf0 : ∀ J, 0 ≤ Pf J := fun J => Finset.prod_nonneg fun i _ => by positivity
  set K : ℝ := ∑ x ∈ faceIndex p, faceW x.1 x.2 * ∑ j ∈ Finset.Ico q (DJ x.1 + 1),
    (j.choose q : ℝ) * (Pf x.1 * Cd * Cc x.1 (fun i => x.2 i + h i) *
      faceMajorant (fun i : {i // ¬ inJ x.1 i} => p i) (fun i : {i // ¬ inJ x.1 i} => h i)
        (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)) with hK
  have hK0 : 0 ≤ K := by
    refine Finset.sum_nonneg fun x _ => mul_nonneg (faceW_nonneg _ _)
      (Finset.sum_nonneg fun j _ => ?_)
    have := hPf0 x.1
    have := hCc0 x.1 (fun i => x.2 i + h i)
    have := faceMajorant_nonneg (fun i : {i // ¬ inJ x.1 i} => p i)
      (fun i : {i // ¬ inJ x.1 i} => h i) (fun i : {i // ¬ inJ x.1 i} => 2 * k i) 1 μ (j - q)
    positivity
  refine ⟨K, hK0, fun ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hεE hclose => ?_⟩
  have hζ₁B : JetBoundOn (∑ i, p i) (closedBox d 1) ζ₁ (B + E) :=
    (hζB.of_jetClose hclose).mono_of_le (by linarith)
  have hζ₂B : JetBoundOn (∑ i, p i) (closedBox d 1) ζ₂ (B + E) := hζB.mono_of_le (by linarith)
  have hF₁ := hCf ζ₁ hζ₁ hζ₁B
  have hF₂ := hCf ζ₂ hζ₂ hζ₂B
  have hconv : ∀ J : Finset (Fin d), ∀ i : {i // ¬ inJ J i},
      ((2 * k i : ℕ) : ℝ) * μ < (p i : ℝ) + h i + 1 := by
    intro J i
    have hμL : μ < L := ((mem_latticeBelow_iff hQ).1 hμ).2
    have h1 : ((2 * k i : ℕ) : ℝ) * L = (p i : ℝ) + h i := by exact_mod_cast (hp i).symm
    have h2 : (0 : ℝ) < (2 * k i : ℕ) := by exact_mod_cast Nat.mul_pos two_pos (hk i)
    nlinarith
  unfold empCoeffAtDepth
  rw [← Finset.sum_sub_distrib, hK, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hm : x.2 ∈ idxL p (lJ x.1) := (Finset.mem_sigma.1 hx).2
  rw [← mul_sub, abs_mul, abs_of_nonneg (faceW_nonneg _ _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (faceW_nonneg _ _)
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hjD : j ≤ DJ x.1 := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hj).2
  rw [← mul_sub, abs_mul, Nat.abs_cast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  set J := x.1 with hJ
  set m := x.2 with hmdef
  set e : Fin d → ℕ := fun i => m i + h i with he
  -- growth of the face amplitudes of each field and of the difference
  have hgrow : ∀ (ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ζ → FieldJetBound η ζ p 1 Cf (B + E) →
      ∀ w ∈ box {i // ¬ inJ J i} 1, GrowthLE (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
        (Pf J * Cf * mono (fun i : {i // ¬ inJ J i} => p i) w) P2 (B + E) :=
    fun ζ hζ hF w hw =>
      (growthLE_faceAmp_fieldFam_of_bound hη hζ one_pos hF hp0 J m hm hw).mono_exp (by omega)
  have hgrow_diff : ∀ w ∈ box {i // ¬ inJ J i} 1,
      GrowthLE (fun τ => faceAmp p J (fieldFam η ζ₁ τ) m w - faceAmp p J (fieldFam η ζ₂ τ) m w)
        (Pf J * (Cd * ε) * mono (fun i : {i // ¬ inJ J i} => p i) w) P2 (B + E) := by
    intro w hw τ hτ
    beta_reduce
    rw [← faceAmp_sub p J (contDiff_fieldFam hη hζ₁ τ) (contDiff_fieldFam hη hζ₂ τ) m w]
    have hb := faceAmp_bound p J ((contDiff_fieldFam hη hζ₁ τ).sub (contDiff_fieldFam hη hζ₂ τ))
      one_pos hp0 (M := Cd * ε * (1 + τ) ^ P2 * exp ((B + E) * τ))
      (fun m' hm' v hv =>
        hCd ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hεE hclose m' hm' τ hτ v (mem_closedBox.2 hv)) hm hw
    exact hb.trans (le_of_eq (by ring))
  have hmeas : ∀ (ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ζ → ∀ w : {i // ¬ inJ J i} → ℝ,
      Measurable fun τ => faceAmp p J (fieldFam η ζ τ) m w :=
    fun ζ hζ w => ((continuous_faceAmp_fieldFam_joint hη hζ p J m).comp
      (continuous_id.prodMk continuous_const)).measurable
  have hGm : ∀ (ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ζ →
      Measurable fun w => empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j :=
    fun ζ hζ => measurable_empFaceCoef_comp k J e (measurable_uncurry_faceAmp_fieldFam hη hζ p J m)
      μ j
  have hGb : ∀ (ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ζ → FieldJetBound η ζ p 1 Cf (B + E) →
      ∀ w ∈ box {i // ¬ inJ J i} 1,
      |empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j| ≤
        (Pf J * Cf * Cc J e) * mono (fun i : {i // ¬ inJ J i} => p i) w := by
    intro ζ hζ hF w hw
    by_cases hμJ : μ ∈ empΛJ k (L : ℝ) J e
    · calc |empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j|
          ≤ (Pf J * Cf * mono (fun i : {i // ¬ inJ J i} => p i) w) * Cc J e :=
            hCc J e _ _ (hgrow ζ hζ hF w hw) μ hμJ j (Finset.mem_range.2 (Nat.lt_succ_of_le hjD))
        _ = _ := by ring
    · rw [empFaceCoef_eq_zero k (L : ℝ) J hk e _ hμ hμJ j, abs_zero]
      have := hPf0 J
      have := hCc0 J e
      have := (mono_pos (fun i : {i // ¬ inJ J i} => p i) (pos_of_mem_box hw)).le
      positivity
  have hdiffb : ∀ w ∈ box {i // ¬ inJ J i} 1,
      |empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ₁ τ) m w) μ j -
          empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ₂ τ) m w) μ j| ≤
        (Pf J * Cd * Cc J e * ε) * mono (fun i : {i // ¬ inJ J i} => p i) w := by
    intro w hw
    by_cases hμJ : μ ∈ empΛJ k (L : ℝ) J e
    · have hμ0 : 0 < μ := pos_of_mem_empΛJ hk hμJ
      rw [← empFaceCoef_sub k J e (hmeas ζ₁ hζ₁ w) (hmeas ζ₂ hζ₂ w) (hgrow ζ₁ hζ₁ hF₁ w hw)
        (hgrow ζ₂ hζ₂ hF₂ w hw) hμ0 j]
      calc |empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ₁ τ) m w -
              faceAmp p J (fieldFam η ζ₂ τ) m w) μ j|
          ≤ (Pf J * (Cd * ε) * mono (fun i : {i // ¬ inJ J i} => p i) w) * Cc J e :=
            hCc J e _ _ (hgrow_diff w hw) μ hμJ j (Finset.mem_range.2 (Nat.lt_succ_of_le hjD))
        _ = _ := by ring
    · rw [empFaceCoef_eq_zero k (L : ℝ) J hk e _ hμ hμJ j,
        empFaceCoef_eq_zero k (L : ℝ) J hk e _ hμ hμJ j, sub_zero, abs_zero]
      have := hPf0 J
      have := hCc0 J e
      have := (mono_pos (fun i : {i // ¬ inJ J i} => p i) (pos_of_mem_box hw)).le
      positivity
  have hint : ∀ (ζ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ζ → FieldJetBound η ζ p 1 Cf (B + E) →
      IntegrableOn (fun w => empFaceCoef k J e (fun τ => faceAmp p J (fieldFam η ζ τ) m w) μ j *
        mono (fun i : {i // ¬ inJ J i} => h i) w *
        mono (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (-μ) *
        logSum (fun i : {i // ¬ inJ J i} => 2 * k i) w ^ (j - q)) (box {i // ¬ inJ J i} 1) :=
    fun ζ hζ hF => integrable_faceCoeff one_pos (hGm ζ hζ).aestronglyMeasurable (hGb ζ hζ hF)
      (hconv J) le_rfl
  rw [← faceCoeffInt_sub _ _ _ _ _ (hint ζ₁ hζ₁ hF₁) (hint ζ₂ hζ₂ hF₂)]
  have hface := abs_faceCoeffInt_le one_pos ((hGm ζ₁ hζ₁).sub (hGm ζ₂ hζ₂)).aestronglyMeasurable
    hdiffb (hconv J) (j - q)
  exact hface.trans (le_of_eq (by ring))

/-- ★★ **Every canonical empirical coefficient is Lipschitz on jet balls** (unit box): for every
`μ` and `q`, one constant `K` with `|empCoeff η ζ₁ h k μ q − empCoeff η ζ₂ h k μ q| ≤ K ε`
whenever the jets of order `≤ cubeOrder h k μ` of `ζ₂` are bounded by `B` and those of `ζ₁, ζ₂`
are `ε`-close on the closed unit box (`ε ≤ E`). -/
theorem exists_empCoeff_sub_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) (μ : ℝ) (q : ℕ)
    {B E : ℝ} (hB : 0 ≤ B) (hE : 1 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (cubeOrder h k μ) (closedBox d 1) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ E →
      JetClose (cubeOrder h k μ) (closedBox d 1) ζ₁ ζ₂ ε →
      |empCoeff η ζ₁ h k μ q - empCoeff η ζ₂ h k μ q| ≤ K * ε := by
  have hQ := Qamb_pos k hk
  by_cases hlat : ∀ n : ℕ, μ ≠ (n : ℝ) / Qamb k
  · refine ⟨0, le_rfl, fun ζ₁ ζ₂ _ _ _ ε _ _ _ => ?_⟩
    rw [empCoeff_eq_zero_of_not_lattice hk hlat q, empCoeff_eq_zero_of_not_lattice hk hlat q,
      sub_zero, abs_zero, zero_mul]
  · have hμ : μ ∈ latticeBelow (Qamb k) (cutoffOf h μ) := by
      rw [mem_latticeBelow_iff hQ]
      refine ⟨?_, lt_cutoffOf h μ⟩
      obtain ⟨n, hn⟩ := not_forall.1 hlat
      exact ⟨n, not_not.1 hn⟩
    have hL₀ : L₀ h ≤ cutoffOf h μ := le_max_right _ _
    obtain ⟨K, hK0, hK⟩ := exists_empCoeffAtDepth_sub_le hη hk (depthOf_add hk hL₀)
      (depthOf_pos hk hL₀) hμ q hB hE
    exact ⟨K, hK0, fun ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hεE hclose =>
      hK ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hεE hclose⟩

/-! ### Transport to the cube -/

/-- Jet closeness of the dilated fields on the unit box from jet closeness on the cube. -/
theorem jetClose_comp_diag {ζ₁ ζ₂ : (Fin d → ℝ) → ℝ} (hζ₁ : ContDiff ℝ ∞ ζ₁)
    (hζ₂ : ContDiff ℝ ∞ ζ₂) {b : ℝ} (hb : 0 < b) {P : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : JetClose P (closedBox d b) ζ₁ ζ₂ ε) :
    JetClose P (closedBox d 1) (ζ₁ ∘ diag (fun _ : Fin d => b)) (ζ₂ ∘ diag (fun _ : Fin d => b))
      ((max 1 b) ^ P * ε) := by
  intro r hr x hx
  set g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := b • ContinuousLinearMap.id ℝ (Fin d → ℝ) with hg
  have hgn : ‖g‖ ≤ b := by
    calc ‖g‖ ≤ ‖b‖ * ‖ContinuousLinearMap.id ℝ (Fin d → ℝ)‖ := norm_smul_le _ _
      _ ≤ b * 1 := by
          rw [Real.norm_of_nonneg hb.le]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hb.le
      _ = b := mul_one b
  rw [diag_const_eq, ← hg,
    ContinuousLinearMap.iteratedFDeriv_comp_right g hζ₁ x (natCast_le_infty r),
    ContinuousLinearMap.iteratedFDeriv_comp_right g hζ₂ x (natCast_le_infty r)]
  have hgx : g x ∈ closedBox d b := by
    have := diag_const_mem_closedBox hb.le hx
    rwa [diag_const_eq, ← hg] at this
  have hsub : (iteratedFDeriv ℝ r ζ₁ (g x)).compContinuousLinearMap (fun _ => g) -
      (iteratedFDeriv ℝ r ζ₂ (g x)).compContinuousLinearMap (fun _ => g) =
      (iteratedFDeriv ℝ r ζ₁ (g x) - iteratedFDeriv ℝ r ζ₂ (g x)).compContinuousLinearMap
        (fun _ => g) := by
    ext v
    simp
  rw [hsub]
  calc ‖(iteratedFDeriv ℝ r ζ₁ (g x) - iteratedFDeriv ℝ r ζ₂ (g x)).compContinuousLinearMap
        fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ r ζ₁ (g x) - iteratedFDeriv ℝ r ζ₂ (g x)‖ * ∏ _i : Fin r, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ε * (max 1 b) ^ P := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul (hclose r hr (g x) hgx) ?_ (by positivity) hε
        calc ‖g‖ ^ r ≤ (max 1 b) ^ r :=
              pow_le_pow_left₀ (norm_nonneg _) (hgn.trans (le_max_right _ _)) r
          _ ≤ (max 1 b) ^ P := pow_le_pow_right₀ (le_max_left _ _) hr
    _ = (max 1 b) ^ P * ε := mul_comm _ _

/-- ★★ **Every empirical cube coefficient is Lipschitz on jet balls**: for every `μ`, `q` and jet
bound `B`, one constant `K` with
`|empCoeffRect η ζ₁ h k b μ q − empCoeffRect η ζ₂ h k b μ q| ≤ K ε` whenever the jets of order
`≤ cubeOrder h k μ` of `ζ₂` are bounded by `B` on the closed cube and those of `ζ₁, ζ₂` are
`ε`-close there (`ε ≤ 1`). -/
theorem exists_empCoeffRect_sub_le (hη : ContDiff ℝ ∞ η) (hk : ∀ i, 0 < k i) {b : ℝ} (hb : 0 < b)
    (μ : ℝ) (q : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (cubeOrder h k μ) (closedBox d b) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ 1 →
      JetClose (cubeOrder h k μ) (closedBox d b) ζ₁ ζ₂ ε →
      |empCoeffRect η ζ₁ h k (fun _ => b) μ q - empCoeffRect η ζ₂ h k (fun _ => b) μ q| ≤
        K * ε := by
  set E : ℝ := (max 1 b) ^ cubeOrder h k μ with hEdef
  have hE : 1 ≤ E := one_le_pow₀ (le_max_left _ _)
  have hE0 : 0 ≤ E := by linarith
  have hηD : ContDiff ℝ ∞ (η ∘ diag (fun _ : Fin d => b)) := hη.comp (contDiff_diag _)
  choose Kj hKj0 hKj using fun j : ℕ =>
    exists_empCoeff_sub_le hηD hk μ j (B := E * B) (mul_nonneg hE0 hB) hE
  set A : ℝ := (∏ _i : Fin d, b) * mono h (fun _ : Fin d => b)
  set β : ℝ := mono (fun i => 2 * k i) (fun _ : Fin d => b)
  have hβ0 : 0 < β := mono_pos _ fun _ => hb
  set S : ℝ := ∑ j ∈ Finset.Ico q (d - 1 + 1),
    Kj j * E * (j.choose q : ℝ) * |Real.log β| ^ (j - q) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by have := hKj0 j; positivity
  refine ⟨|A| * β ^ (-μ) * S, by positivity, fun ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hε1 hclose => ?_⟩
  have hζ₂D := jetBoundOn_comp_diag hζ₂ hb hB hζB
  have hcD := jetClose_comp_diag hζ₁ hζ₂ hb hε0 hclose
  have hεE : (max 1 b) ^ cubeOrder h k μ * ε ≤ E := by
    rw [hEdef]
    exact mul_le_of_le_one_right (by positivity) hε1
  have hterm : ∀ j : ℕ,
      |empCoeff (η ∘ diag fun _ : Fin d => b) (ζ₁ ∘ diag fun _ : Fin d => b) h k μ j -
        empCoeff (η ∘ diag fun _ : Fin d => b) (ζ₂ ∘ diag fun _ : Fin d => b) h k μ j| ≤
        Kj j * E * ε := by
    intro j
    have := hKj j (ζ₁ ∘ diag fun _ : Fin d => b) (ζ₂ ∘ diag fun _ : Fin d => b)
      (hζ₁.comp (contDiff_diag _)) (hζ₂.comp (contDiff_diag _)) hζ₂D _
      (by positivity) hεE hcD
    calc _ ≤ Kj j * ((max 1 b) ^ cubeOrder h k μ * ε) := this
      _ = Kj j * E * ε := by rw [hEdef]; ring
  have hrect : ∀ ζ : (Fin d → ℝ) → ℝ, empCoeffRect η ζ h k (fun _ => b) μ q =
      A * (β ^ (-μ) * ∑ j ∈ Finset.Ico q (d - 1 + 1),
        empCoeff (η ∘ diag fun _ : Fin d => b) (ζ ∘ diag fun _ : Fin d => b) h k μ j *
          (j.choose q : ℝ) * Real.log β ^ (j - q)) := fun ζ => rfl
  clear_value A β
  rw [hrect ζ₁, hrect ζ₂, ← mul_sub, abs_mul, ← mul_sub, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hβ0.le _), ← Finset.sum_sub_distrib]
  calc |A| * (β ^ (-μ) * |∑ j ∈ Finset.Ico q (d - 1 + 1),
        (empCoeff (η ∘ diag fun _ : Fin d => b) (ζ₁ ∘ diag fun _ : Fin d => b) h k μ j *
            (j.choose q : ℝ) * Real.log β ^ (j - q) -
          empCoeff (η ∘ diag fun _ : Fin d => b) (ζ₂ ∘ diag fun _ : Fin d => b) h k μ j *
            (j.choose q : ℝ) * Real.log β ^ (j - q))|)
      ≤ |A| * (β ^ (-μ) * (S * ε)) := by
        gcongr
        rw [hS, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, Nat.abs_cast, abs_pow]
        calc _ ≤ Kj j * E * ε * (j.choose q : ℝ) * |Real.log β| ^ (j - q) := by
              gcongr
              exact hterm j
          _ = _ := by ring
    _ = |A| * β ^ (-μ) * S * ε := by ring

end SmoothEngine

end Grammar
