/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ParametricFaceAmplitude
import Grammar.SmoothAmplitudeFamily
import Grammar.EmpiricalInnerKernel

/-!
# Jets of the empirical field family `B_τ(v) = η(v) e^{τ ζ(v)}` (§20 Stage 4)

The empirical integrand is the population amplitude `η` times the exponential of the root field
`ζ` at the effective coupling `τ = √N v^k`. Its coordinate derivatives are JETS: polynomials in
`τ` with smooth coefficient functions times `e^{τ ζ}` (`IsJet`; `∂_i` raises the degree by one,
`IsJet.pd`, so `∂^m` has degree `|m|`, `IsJet.pdMulti`). On the closed box a jet of degree `R`
is bounded by `C (1+τ)^R e^{M'τ}` when `|ζ| ≤ M'` (`IsJet.bound`), uniformly over all
multi-indices `m ≤ p` (★ `exists_pdMulti_fieldFam_bound`). Consequently the face amplitudes
`G_{J,m}(τ; w) = (R_K^p ∂^m B_τ)(0_J, w)` satisfy the FLAT GROWTH bound
`|G_{J,m}(τ; w)| ≤ (∏_K 1/(pᵢ−1)!) · C · w^{p_K} · (1+τ)^{|p|} e^{M'τ}`
(★ `growthLE_faceAmp_fieldFam`, the hypothesis of the empirical face theorem) and are jointly
measurable in `(w, τ)`
(`measurable_uncurry_faceAmp_fieldFam`, from the joint smoothness of `ParametricFaceAmplitude`).
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### The field family -/

/-- The empirical field family `B_τ(v) = η(v) e^{τ ζ(v)}`. -/
noncomputable def fieldFam (η ζ : (Fin d → ℝ) → ℝ) (τ : ℝ) (v : Fin d → ℝ) : ℝ :=
  η v * exp (τ * ζ v)

variable {η ζ : (Fin d → ℝ) → ℝ}

theorem contDiff_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (τ : ℝ) :
    ContDiff ℝ ∞ (fieldFam η ζ τ) :=
  hη.mul (contDiff_exp.comp (contDiff_const.mul hζ))

theorem contDiff_fieldFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => fieldFam η ζ z.1 z.2 :=
  (hη.comp contDiff_snd).mul (contDiff_exp.comp (contDiff_fst.mul (hζ.comp contDiff_snd)))

/-! ### Coordinate-derivative calculus -/

theorem hasDerivAt_line {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) (v : Fin d → ℝ)
    (t : ℝ) : HasDerivAt (line f i v) (deriv (line f i v) t) t :=
  (((contDiff_line hf i v).differentiable (by simp)) t).hasDerivAt

theorem pd_mul_apply {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin d)
    (v : Fin d → ℝ) : pd i (fun v => f v * g v) v = pd i f v * g v + f v * pd i g v := by
  have h := (hasDerivAt_line hf i v (v i)).fun_mul (hasDerivAt_line hg i v (v i))
  have hl : line (fun v => f v * g v) i v = fun t => line f i v t * line g i v t := rfl
  unfold pd
  rw [hl, h.deriv, line_apply_self, line_apply_self]

theorem pd_exp_mul (hζ : ContDiff ℝ ∞ ζ) (τ : ℝ) (i : Fin d) (v : Fin d → ℝ) :
    pd i (fun v => exp (τ * ζ v)) v = τ * pd i ζ v * exp (τ * ζ v) := by
  have h := ((hasDerivAt_line hζ i v (v i)).const_mul τ).exp
  have hl : line (fun v => exp (τ * ζ v)) i v = fun t => exp (τ * line ζ i v t) := rfl
  unfold pd
  rw [hl, h.deriv, line_apply_self]
  ring

theorem pd_sum_mul_const {P : ℕ → (Fin d → ℝ) → ℝ} (hP : ∀ r, ContDiff ℝ ∞ (P r)) (s : Finset ℕ)
    (c : ℕ → ℝ) (i : Fin d) (v : Fin d → ℝ) :
    pd i (fun v => ∑ r ∈ s, P r v * c r) v = ∑ r ∈ s, pd i (P r) v * c r := by
  have h : HasDerivAt (fun t => ∑ r ∈ s, line (P r) i v t * c r)
      (∑ r ∈ s, deriv (line (P r) i v) (v i) * c r) (v i) :=
    HasDerivAt.fun_sum fun r _ => (hasDerivAt_line (hP r) i v (v i)).mul_const (c r)
  have hl : line (fun v => ∑ r ∈ s, P r v * c r) i v = fun t => ∑ r ∈ s, line (P r) i v t * c r :=
    rfl
  unfold pd
  rw [hl, h.deriv]

/-! ### Jets -/

/-- `H τ v = (∑_{r ≤ R} P_r(v) τ^r) e^{τ ζ(v)}` with smooth coefficient functions `P_r`. -/
def IsJet (ζ : (Fin d → ℝ) → ℝ) (R : ℕ) (H : ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ P : ℕ → (Fin d → ℝ) → ℝ, (∀ r, ContDiff ℝ ∞ (P r)) ∧
    ∀ τ v, H τ v = (∑ r ∈ range (R + 1), P r v * τ ^ r) * exp (τ * ζ v)

theorem isJet_fieldFam (hη : ContDiff ℝ ∞ η) : IsJet ζ 0 (fieldFam η ζ) :=
  ⟨fun _ => η, fun _ => hη, fun τ v => by simp [fieldFam]⟩

theorem IsJet.contDiff (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ}
    (h : IsJet ζ R H) (τ : ℝ) : ContDiff ℝ ∞ (H τ) := by
  obtain ⟨P, hP, hH⟩ := h
  have : H τ = fun v => (∑ r ∈ range (R + 1), P r v * τ ^ r) * exp (τ * ζ v) := funext (hH τ)
  rw [this]
  exact (ContDiff.sum fun r _ => (hP r).mul contDiff_const).mul
    (contDiff_exp.comp (contDiff_const.mul hζ))

/-- A coordinate derivative raises the jet degree by one. -/
theorem IsJet.pd (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ} (h : IsJet ζ R H)
    (i : Fin d) : IsJet ζ (R + 1) fun τ => pd i (H τ) := by
  obtain ⟨P, hP, hH⟩ := h
  refine ⟨fun r v => (if r < R + 1 then SmoothEngine.pd i (P r) v else 0) +
    (if 0 < r then P (r - 1) v * SmoothEngine.pd i ζ v else 0), fun r => ?_, fun τ v => ?_⟩
  · refine ContDiff.add ?_ ?_
    · split_ifs
      · exact contDiff_pd (hP r) i
      · exact contDiff_const
    · split_ifs
      · exact (hP (r - 1)).mul (contDiff_pd hζ i)
      · exact contDiff_const
  · have hHτ : H τ = fun v => (∑ r ∈ range (R + 1), P r v * τ ^ r) * exp (τ * ζ v) :=
      funext (hH τ)
    have hf : ContDiff ℝ ∞ fun v => ∑ r ∈ range (R + 1), P r v * τ ^ r :=
      ContDiff.sum fun r _ => (hP r).mul contDiff_const
    have hg : ContDiff ℝ ∞ fun v => exp (τ * ζ v) := contDiff_exp.comp (contDiff_const.mul hζ)
    simp only
    rw [hHτ, pd_mul_apply hf hg, pd_sum_mul_const hP, pd_exp_mul hζ]
    have hsum : ∑ r ∈ range (R + 1 + 1), ((if r < R + 1 then SmoothEngine.pd i (P r) v else 0) +
        (if 0 < r then P (r - 1) v * SmoothEngine.pd i ζ v else 0)) * τ ^ r =
        ∑ r ∈ range (R + 1), SmoothEngine.pd i (P r) v * τ ^ r +
          τ * ((∑ r ∈ range (R + 1), P r v * τ ^ r) * SmoothEngine.pd i ζ v) := by
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_range_succ, if_neg (lt_irrefl _), zero_mul, add_zero]
        exact Finset.sum_congr rfl fun r hr => by rw [if_pos (Finset.mem_range.1 hr)]
      · rw [Finset.sum_range_succ', if_neg (lt_irrefl 0), zero_mul, add_zero, Finset.sum_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [if_pos (Nat.succ_pos r), Nat.add_sub_cancel]
        ring
    rw [hsum]
    ring

theorem IsJet.pdPow (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ} (h : IsJet ζ R H)
    (i : Fin d) (n : ℕ) : IsJet ζ (R + n) fun τ => pdPow i n (H τ) := by
  induction n with
  | zero => simpa [pdPow_zero] using h
  | succ n ih =>
    have := ih.pd hζ i
    rw [← Nat.add_assoc]
    simp only [pdPow_succ']
    exact this

theorem IsJet.pdMulti (hζ : ContDiff ℝ ∞ ζ) {R : ℕ} {H : ℝ → (Fin d → ℝ) → ℝ} (h : IsJet ζ R H)
    (m : Fin d → ℕ) (l : List (Fin d)) : IsJet ζ (R + wordLen m l) fun τ => pdMulti m l (H τ) := by
  induction l with
  | nil => simpa [pdMulti_nil, wordLen] using h
  | cons i l ih =>
    have := ih.pdPow hζ i (m i)
    simp only [wordLen, pdMulti_cons]
    rwa [← Nat.add_assoc]

/-- ★ A jet of degree `R` on the closed box grows at most like `C (1+τ)^R e^{M'τ}` when
`|ζ| ≤ M'`. -/
theorem IsJet.bound {b M' : ℝ} (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') {R : ℕ}
    {H : ℝ → (Fin d → ℝ) → ℝ} (h : IsJet ζ R H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
      |H τ v| ≤ C * (1 + τ) ^ R * exp (M' * τ) := by
  obtain ⟨P, hP, hH⟩ := h
  have hb : ∀ r, ∃ C : ℝ, ∀ v ∈ closedBox d b, |P r v| ≤ C := fun r => by
    obtain ⟨C, hC⟩ := (isCompact_closedBox b).exists_bound_of_continuousOn
      (hP r).continuous.continuousOn
    exact ⟨C, fun v hv => by simpa [Real.norm_eq_abs] using hC v hv⟩
  choose C hC using hb
  refine ⟨∑ r ∈ range (R + 1), |C r|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun τ hτ v hv => ?_⟩
  rw [hH τ v, abs_mul, abs_of_pos (exp_pos _)]
  have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith
  have h1 : |∑ r ∈ range (R + 1), P r v * τ ^ r| ≤ (∑ r ∈ range (R + 1), |C r|) * (1 + τ) ^ R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => ?_
    rw [abs_mul, abs_pow, abs_of_nonneg hτ]
    have hr' : r ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hpow : τ ^ r ≤ (1 + τ) ^ R :=
      (pow_le_pow_left₀ hτ (by linarith) r).trans (pow_le_pow_right₀ h1τ hr')
    exact mul_le_mul ((hC r v hv).trans (le_abs_self _)) hpow (by positivity) (abs_nonneg _)
  have h2 : exp (τ * ζ v) ≤ exp (M' * τ) := by
    rw [exp_le_exp]
    calc τ * ζ v ≤ τ * |ζ v| := mul_le_mul_of_nonneg_left (le_abs_self _) hτ
      _ ≤ τ * M' := mul_le_mul_of_nonneg_left (hζM v hv) hτ
      _ = M' * τ := mul_comm _ _
  calc |∑ r ∈ range (R + 1), P r v * τ ^ r| * exp (τ * ζ v)
      ≤ ((∑ r ∈ range (R + 1), |C r|) * (1 + τ) ^ R) * exp (M' * τ) :=
        mul_le_mul h1 h2 (exp_pos _).le (by positivity)
    _ = _ := by ring

/-- ★ **Uniform jet bound**: the coordinate derivatives `∂^m B_τ`, `m ≤ p`, are bounded on the
closed box by `C (1+τ)^{|p|} e^{M'τ}` with ONE constant `C`. -/
theorem exists_pdMulti_fieldFam_bound (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b M' : ℝ}
    (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ →
      ∀ v ∈ closedBox d b, |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤
        C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ) := by
  have hbd : ∀ m : Fin d → ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
      |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤
        C * (1 + τ) ^ (0 + wordLen m (List.finRange d)) * exp (M' * τ) :=
    fun m => ((isJet_fieldFam hη).pdMulti hζ m (List.finRange d)).bound hζM
  choose C hC0 hC using hbd
  refine ⟨∑ m ∈ Fintype.piFinset (fun i => range (p i + 1)), C m,
    Finset.sum_nonneg fun m _ => hC0 m, fun m hm τ hτ v hv => ?_⟩
  have hmem : m ∈ Fintype.piFinset (fun i => range (p i + 1)) :=
    Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hm i))
  have hdeg : 0 + wordLen m (List.finRange d) ≤ ∑ i, p i := by
    rw [zero_add, wordLen_eq_sum_toFinset m (List.nodup_finRange d), List.toFinset_finRange]
    exact Finset.sum_le_sum fun i _ => hm i
  have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith
  calc |pdMulti m (List.finRange d) (fieldFam η ζ τ) v|
      ≤ C m * (1 + τ) ^ (0 + wordLen m (List.finRange d)) * exp (M' * τ) := hC m τ hτ v hv
    _ ≤ (∑ m' ∈ Fintype.piFinset (fun i => range (p i + 1)), C m') * (1 + τ) ^ (∑ i, p i) *
          exp (M' * τ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul
          (Finset.single_le_sum (fun m' _ => hC0 m') hmem) (pow_le_pow_right₀ h1τ hdeg)
          (by positivity) (Finset.sum_nonneg fun m' _ => hC0 m')) (exp_pos _).le

/-! ### The face amplitudes of the field family -/

/-- The rectangular jet bound of the field family: `|∂^m B_τ(v)| ≤ C (1+τ)^{|p|} e^{M'τ}` for all
`m ≤ p`, `τ ≥ 0` and `v` in the closed box. This is the only way `(η, ζ)` enter the constants of
the empirical expansion. -/
def FieldJetBound (η ζ : (Fin d → ℝ) → ℝ) (p : Fin d → ℕ) (b C M' : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
    |pdMulti m (List.finRange d) (fieldFam η ζ τ) v| ≤ C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ)

theorem exists_fieldJetBound (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b M' : ℝ}
    (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ FieldJetBound η ζ p b C M' :=
  exists_pdMulti_fieldFam_bound hη hζ hζM p

theorem FieldJetBound.nonneg {p : Fin d → ℕ} {b C M' : ℝ} (hb : 0 ≤ b)
    (h : FieldJetBound η ζ p b C M') :
    0 ≤ C := by
  have h0 := h 0 (fun i => Nat.zero_le _) 0 le_rfl 0 (mem_closedBox.2 fun i => by simp [hb])
  simp only [add_zero, one_pow, mul_one, mul_zero, exp_zero] at h0
  exact (abs_nonneg _).trans h0

/-- ★ **Flat growth of the empirical face amplitudes under a jet bound**: for `w` in the
complementary box, `τ ↦ G_{J,m}(τ; w) = (R_K^p ∂^m B_τ)(0_J, w)` has growth
`(∏_K 1/(pᵢ−1)!) C w^{p_K} (1+τ)^{|p|} e^{M'τ}`. -/
theorem growthLE_faceAmp_fieldFam_of_bound (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    {b C M' : ℝ} (hb : 0 < b) {p : Fin d → ℕ} (hC : FieldJetBound η ζ p b C M') (hp0 : ∀ i, 0 < p i)
    (J : Finset (Fin d)) (m : Fin d → ℕ) (hm : m ∈ idxL p (lJ J)) {w : {i // ¬ inJ J i} → ℝ}
    (hw : w ∈ box {i // ¬ inJ J i} b) :
    GrowthLE (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
      ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
        mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M' := by
  intro τ hτ
  have h := faceAmp_bound p J (contDiff_fieldFam hη hζ τ) hb hp0
    (M := C * (1 + τ) ^ (∑ i, p i) * exp (M' * τ))
    (fun m' hm' v hv => hC m' hm' τ hτ v (mem_closedBox.2 hv)) hm hw
  refine h.trans (le_of_eq ?_)
  ring

/-- ★ **Flat growth of the empirical face amplitudes** (existential form). -/
theorem growthLE_faceAmp_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {b M' : ℝ}
    (hb : 0 < b) (hζM : ∀ v ∈ closedBox d b, |ζ v| ≤ M') (p : Fin d → ℕ) (hp0 : ∀ i, 0 < p i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Finset (Fin d)) (m : Fin d → ℕ), m ∈ idxL p (lJ J) →
      ∀ w ∈ box {i // ¬ inJ J i} b,
        GrowthLE (fun τ => faceAmp p J (fieldFam η ζ τ) m w)
          ((∏ i : {i // ¬ inJ J i}, ((p i - 1).factorial : ℝ)⁻¹) * C *
            mono (fun i : {i // ¬ inJ J i} => p i) w) (∑ i, p i) M' := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldJetBound hη hζ hζM p
  exact ⟨C, hC0, fun J m hm w hw => growthLE_faceAmp_fieldFam_of_bound hη hζ hb hC hp0 J m hm hw⟩

/-- The face amplitudes of the field family are jointly continuous in `(τ, w)`. -/
theorem continuous_faceAmp_fieldFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Continuous fun z : ℝ × ({i // ¬ inJ J i} → ℝ) => faceAmp p J (fieldFam η ζ z.1) m z.2 :=
  (contDiff_faceAmp_slice (G := fun z : ℝ × (Fin d → ℝ) => fieldFam η ζ z.1 z.2)
    (contDiff_fieldFam_joint hη hζ) p J m).continuous

/-- The face amplitudes of the field family are jointly measurable in `(w, τ)`. -/
theorem measurable_uncurry_faceAmp_fieldFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) (J : Finset (Fin d)) (m : Fin d → ℕ) :
    Measurable (Function.uncurry fun (w : {i // ¬ inJ J i} → ℝ) (τ : ℝ) =>
      faceAmp p J (fieldFam η ζ τ) m w) :=
  ((continuous_faceAmp_fieldFam_joint hη hζ p J m).comp continuous_swap).measurable

end SmoothEngine

end Grammar
