/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalExpTail

/-!
# Tail jets of the exponential field family (§20, generating identity)

The tail families `tailFam η ζ R τ v = η(v) · expTail R (τ ζ(v))` interpolate between the
exponential field family (`R = 0`) and its Taylor truncations:
`fieldFam = Σ_{r<R} (1/r!) expTermFam r + tailFam R`.

Their coordinate derivatives have the *tail jet* structure
`pdMulti m l (tailFam R τ) = Σ_{j ≤ |m|} P_j(v) τ^j expTail (R − j) (τ ζ(v))`
with smooth `P_j` independent of `R` (`IsTailJet`, closed under `pd`, `pdPow`, `pdMulti`), and
the geometric decay of `expTail` gives

★ `exists_famJetBound_tailFam : ∃ K₀ M', ∀ R, FamJetBound (tailFam η ζ R) p 1 (K₀ (1/2)^R) M'`,

a jet bound whose constant is summable and tends to zero in `R`.

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ}

/-- The tail family `η(v) · expTail R (τ ζ(v))`. -/
noncomputable def tailFam (η ζ : (Fin d → ℝ) → ℝ) (R : ℕ) (τ : ℝ) (v : Fin d → ℝ) : ℝ :=
  η v * expTail R (τ * ζ v)

theorem tailFam_zero (η ζ : (Fin d → ℝ) → ℝ) : tailFam η ζ 0 = fieldFam η ζ := by
  funext τ v
  simp [tailFam, fieldFam, expTail_zero]

theorem tailFam_succ (R : ℕ) (τ : ℝ) (v : Fin d → ℝ) :
    tailFam η ζ (R + 1) τ v =
      tailFam η ζ R τ v - (1 / (R.factorial : ℝ)) * expTermFam η ζ R τ v := by
  simp only [tailFam, expTermFam, expTail_succ, mul_pow]
  ring

/-- `fieldFam = Σ_{r<R} (1/r!) expTermFam r + tailFam R`. -/
theorem fieldFam_eq_sum_add_tailFam (R : ℕ) (τ : ℝ) (v : Fin d → ℝ) :
    fieldFam η ζ τ v =
      ∑ r ∈ range R, (1 / (r.factorial : ℝ)) * expTermFam η ζ r τ v + tailFam η ζ R τ v := by
  induction R with
  | zero => rw [Finset.sum_range_zero, zero_add, tailFam_zero]
  | succ R ih =>
    rw [Finset.sum_range_succ, tailFam_succ, ih]
    ring

theorem contDiff_tailFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (R : ℕ) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => tailFam η ζ R z.1 z.2 :=
  (hη.comp contDiff_snd).mul
    (((contDiff_expTail R).of_le le_top).comp (contDiff_fst.mul (hζ.comp contDiff_snd)))

theorem pd_fun_zero (i : Fin d) : pd i (fun _ : Fin d → ℝ => (0 : ℝ)) = fun _ => 0 := by
  funext v
  change deriv (fun _ : ℝ => (0 : ℝ)) (v i) = 0
  exact deriv_const _ _

/-! ### Tail jets -/

/-- `P` is a tail jet of length `W` for `G : ℕ → ℝ → (Fin d → ℝ) → ℝ`:
`G R τ v = Σ_{j ≤ W} P_j(v) τ^j expTail (R − j) (τ ζ(v))` with smooth `P_j`, vanishing above `W`. -/
def IsTailJet (ζ : (Fin d → ℝ) → ℝ) (W : ℕ) (P : ℕ → (Fin d → ℝ) → ℝ)
    (G : ℕ → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ j, ContDiff ℝ ∞ (P j)) ∧ (∀ j, W < j → P j = fun _ => 0) ∧
    ∀ R τ v, G R τ v = ∑ j ∈ range (W + 1), P j v * τ ^ j * expTail (R - j) (τ * ζ v)

theorem isTailJet_tailFam (hη : ContDiff ℝ ∞ η) :
    IsTailJet ζ 0 (fun j => if j = 0 then η else fun _ => 0) (tailFam η ζ) := by
  refine ⟨fun j => ?_, fun j hj => ?_, fun R τ v => ?_⟩
  · change ContDiff ℝ ∞ (if j = 0 then η else fun _ => (0 : ℝ))
    split_ifs
    · exact hη
    · exact contDiff_const
  · change (if j = 0 then η else fun _ => (0 : ℝ)) = fun _ => 0
    rw [if_neg (Nat.pos_iff_ne_zero.1 hj)]
  · simp [tailFam]

theorem IsTailJet.pd (hζ : ContDiff ℝ ∞ ζ) {W : ℕ} {P : ℕ → (Fin d → ℝ) → ℝ}
    {G : ℕ → ℝ → (Fin d → ℝ) → ℝ} (h : IsTailJet ζ W P G) (i : Fin d) :
    IsTailJet ζ (W + 1)
      (fun j v => SmoothEngine.pd i (P j) v +
        if j = 0 then 0 else P (j - 1) v * SmoothEngine.pd i ζ v)
      (fun R τ => SmoothEngine.pd i (G R τ)) := by
  obtain ⟨hP, hvan, hG⟩ := h
  refine ⟨fun j => ?_, fun j hj => ?_, fun R τ v => ?_⟩
  · refine (contDiff_pd (hP j) i).add ?_
    split_ifs
    · exact contDiff_const
    · exact (hP _).mul (contDiff_pd hζ i)
  · funext v
    change SmoothEngine.pd i (P j) v +
      (if j = 0 then (0 : ℝ) else P (j - 1) v * SmoothEngine.pd i ζ v) = 0
    have h1 : P j = fun _ => 0 := hvan j (by omega)
    have h2 : P (j - 1) = fun _ => 0 := hvan (j - 1) (by omega)
    rw [h1, h2, pd_fun_zero, if_neg (by omega)]
    simp
  · change SmoothEngine.pd i (G R τ) v = _
    have hGf : G R τ = fun v => ∑ j ∈ range (W + 1), P j v * τ ^ j * expTail (R - j) (τ * ζ v) :=
      funext (hG R τ)
    rw [hGf]
    have hl : line (fun v => ∑ j ∈ range (W + 1), P j v * τ ^ j * expTail (R - j) (τ * ζ v)) i v =
        fun t => ∑ j ∈ range (W + 1),
          line (P j) i v t * τ ^ j * expTail (R - j) (τ * line ζ i v t) := rfl
    have hd : HasDerivAt (fun t => ∑ j ∈ range (W + 1),
          line (P j) i v t * τ ^ j * expTail (R - j) (τ * line ζ i v t))
        (∑ j ∈ range (W + 1),
          (deriv (line (P j) i v) (v i) * τ ^ j * expTail (R - j) (τ * line ζ i v (v i)) +
            line (P j) i v (v i) * τ ^ j *
              (expTail (R - j - 1) (τ * line ζ i v (v i)) * (τ * deriv (line ζ i v) (v i)))))
        (v i) := by
      refine HasDerivAt.fun_sum fun j _ => ?_
      exact ((hasDerivAt_line (hP j) i v (v i)).mul_const (τ ^ j)).mul
        ((hasDerivAt_expTail (R - j) _).comp (v i) ((hasDerivAt_line hζ i v (v i)).const_mul τ))
    have hpd : SmoothEngine.pd i
        (fun v => ∑ j ∈ range (W + 1), P j v * τ ^ j * expTail (R - j) (τ * ζ v)) v =
        ∑ j ∈ range (W + 1), (SmoothEngine.pd i (P j) v * τ ^ j * expTail (R - j) (τ * ζ v) +
          P j v * τ ^ j * (expTail (R - j - 1) (τ * ζ v) * (τ * SmoothEngine.pd i ζ v))) := by
      unfold SmoothEngine.pd
      rw [hl, hd.deriv]
      simp only [line_apply_self]
    rw [hpd, Finset.sum_add_distrib]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_range_succ _ (W + 1), hvan (W + 1) (Nat.lt_succ_self W), pd_fun_zero]
      simp
    · rw [Finset.sum_range_succ' _ (W + 1)]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_mul, add_zero,
        Nat.sub_sub]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem IsTailJet.pdPow (hζ : ContDiff ℝ ∞ ζ) {W : ℕ} {P : ℕ → (Fin d → ℝ) → ℝ}
    {G : ℕ → ℝ → (Fin d → ℝ) → ℝ} (h : IsTailJet ζ W P G) (i : Fin d) (n : ℕ) :
    ∃ P' : ℕ → (Fin d → ℝ) → ℝ, IsTailJet ζ (W + n) P' fun R τ => pdPow i n (G R τ) := by
  induction n with
  | zero => exact ⟨P, by simpa [pdPow_zero] using h⟩
  | succ n ih =>
    obtain ⟨P', hP'⟩ := ih
    refine ⟨fun j v => SmoothEngine.pd i (P' j) v +
      if j = 0 then 0 else P' (j - 1) v * SmoothEngine.pd i ζ v, ?_⟩
    have := hP'.pd hζ i
    simp only [pdPow_succ']
    exact this

theorem IsTailJet.pdMulti (hζ : ContDiff ℝ ∞ ζ) {W : ℕ} {P : ℕ → (Fin d → ℝ) → ℝ}
    {G : ℕ → ℝ → (Fin d → ℝ) → ℝ} (h : IsTailJet ζ W P G) (m : Fin d → ℕ)
    (l : List (Fin d)) :
    ∃ P' : ℕ → (Fin d → ℝ) → ℝ,
      IsTailJet ζ (W + wordLen m l) P' fun R τ => pdMulti m l (G R τ) := by
  induction l with
  | nil => exact ⟨P, by simpa [pdMulti_nil, wordLen_nil] using h⟩
  | cons i l ih =>
    obtain ⟨P', hP'⟩ := ih
    obtain ⟨P'', hP''⟩ := hP'.pdPow hζ i (m i)
    refine ⟨P'', ?_⟩
    rw [wordLen_cons, ← add_assoc]
    simpa only [pdMulti_cons] using hP''

/-- The coordinate derivatives of the tail families have tail jets of length `Σ m`. -/
theorem exists_isTailJet_pdMulti_tailFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (m : Fin d → ℕ) :
    ∃ P : ℕ → (Fin d → ℝ) → ℝ, IsTailJet ζ (wordLen m (List.finRange d)) P
      fun R τ => pdMulti m (List.finRange d) (tailFam η ζ R τ) := by
  obtain ⟨P, hP⟩ := (isTailJet_tailFam (ζ := ζ) hη).pdMulti hζ m (List.finRange d)
  exact ⟨P, by simpa only [zero_add] using hP⟩

/-! ### The geometric bound -/

/-- A tail jet with coefficients bounded by `Pm` and `|ζ| ≤ B` on the closed box is bounded by
`(W+1) Pm 2^W (1+τ)^W (1/2)^R e^{3Bτ}`. -/
theorem IsTailJet.abs_le {W : ℕ} {P : ℕ → (Fin d → ℝ) → ℝ} {G : ℕ → ℝ → (Fin d → ℝ) → ℝ}
    (h : IsTailJet ζ W P G) {b Pm B : ℝ}
    (hPm : ∀ j ∈ range (W + 1), ∀ v ∈ closedBox d b, |P j v| ≤ Pm)
    (hB : ∀ v ∈ closedBox d b, |ζ v| ≤ B) (R : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) {v : Fin d → ℝ}
    (hv : v ∈ closedBox d b) :
    |G R τ v| ≤ ((W : ℝ) + 1) * (Pm * 2 ^ W) * (1 + τ) ^ W *
      ((1 / 2) ^ R * Real.exp (3 * B * τ)) := by
  obtain ⟨_, _, hG⟩ := h
  rw [hG]
  have hPm0 : 0 ≤ Pm :=
    (abs_nonneg _).trans (hPm 0 (Finset.mem_range.2 (Nat.succ_pos W)) v hv)
  have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith
  calc |∑ j ∈ range (W + 1), P j v * τ ^ j * expTail (R - j) (τ * ζ v)|
      ≤ ∑ j ∈ range (W + 1), |P j v * τ ^ j * expTail (R - j) (τ * ζ v)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (W + 1),
          Pm * (1 + τ) ^ W * (2 ^ W * (1 / 2) ^ R * Real.exp (3 * B * τ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ W := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hτ]
        have h1 : |P j v| ≤ Pm := hPm j hj v hv
        have h2 : τ ^ j ≤ (1 + τ) ^ W :=
          (pow_le_pow_left₀ hτ (by linarith) j).trans (pow_le_pow_right₀ h1τ hj')
        have h3 : |expTail (R - j) (τ * ζ v)| ≤ 2 ^ W * (1 / 2) ^ R * Real.exp (3 * B * τ) := by
          calc |expTail (R - j) (τ * ζ v)|
              ≤ (1 / 2) ^ (R - j) * Real.exp (3 * |τ * ζ v|) := abs_expTail_le_half _ _
            _ ≤ (2 ^ W * (1 / 2) ^ R) * Real.exp (3 * B * τ) := by
                refine mul_le_mul (half_pow_sub_le hj' R) ?_ (Real.exp_nonneg _) (by positivity)
                refine Real.exp_le_exp.2 ?_
                rw [abs_mul, abs_of_nonneg hτ]
                have := mul_le_mul_of_nonneg_left (hB v hv) hτ
                linarith
        exact mul_le_mul (mul_le_mul h1 h2 (pow_nonneg hτ j) hPm0) h3 (abs_nonneg _)
          (mul_nonneg hPm0 (pow_nonneg (by linarith) W))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- ★ **Uniform jet bounds for the tails, with geometric constants**: there are `K₀ ≥ 0` and
`M'` (depending on `η, ζ, p` only) with `FamJetBound (tailFam η ζ R) p 1 (K₀ (1/2)^R) M'` for
every `R`. -/
theorem exists_famJetBound_tailFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (p : Fin d → ℕ) :
    ∃ K₀ M' : ℝ, 0 ≤ K₀ ∧ ∀ R : ℕ, FamJetBound (tailFam η ζ R) p 1 (K₀ * (1 / 2) ^ R) M' := by
  classical
  choose P hP using fun m : Fin d → ℕ => exists_isTailJet_pdMulti_tailFam hη hζ m
  set Wp : ℕ := ∑ i, p i with hWp
  set S : Finset (Fin d → ℕ) := Fintype.piFinset fun i => Finset.range (p i + 1) with hS
  have hbd : ∀ (m : Fin d → ℕ) (j : ℕ), ∃ C : ℝ, ∀ v ∈ closedBox d 1, |P m j v| ≤ C := by
    intro m j
    obtain ⟨C, hC⟩ := (isCompact_closedBox (d := d) 1).exists_bound_of_continuousOn
      ((hP m).1 j).continuous.continuousOn
    exact ⟨C, fun v hv => by simpa only [Real.norm_eq_abs] using hC v hv⟩
  choose Cb hCb using hbd
  obtain ⟨B, hB⟩ := (isCompact_closedBox (d := d) 1).exists_bound_of_continuousOn
    hζ.continuous.continuousOn
  set Pm : ℝ := ∑ m ∈ S, ∑ j ∈ range (Wp + 1), |Cb m j| with hPm
  have hPm0 : 0 ≤ Pm := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨((Wp : ℝ) + 1) * (Pm * 2 ^ Wp), 3 * |B|,
    mul_nonneg (by positivity) (mul_nonneg hPm0 (by positivity)), fun R m hm τ hτ v hv => ?_⟩
  have hW : wordLen m (List.finRange d) ≤ Wp := by
    rw [wordLen_finRange]
    exact Finset.sum_le_sum fun i _ => hm i
  have hmS : m ∈ S :=
    Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hm i))
  have hPmj : ∀ j ∈ range (wordLen m (List.finRange d) + 1), ∀ v ∈ closedBox d 1,
      |P m j v| ≤ Pm := by
    intro j hj v hv
    have hj' : j ∈ range (Wp + 1) :=
      Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))
    calc |P m j v| ≤ Cb m j := hCb m j v hv
      _ ≤ |Cb m j| := le_abs_self _
      _ ≤ ∑ j ∈ range (Wp + 1), |Cb m j| :=
          Finset.single_le_sum (f := fun j => |Cb m j|) (fun _ _ => abs_nonneg _) hj'
      _ ≤ Pm :=
          Finset.single_le_sum (f := fun m => ∑ j ∈ range (Wp + 1), |Cb m j|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hmS
  have hBv : ∀ v ∈ closedBox d 1, |ζ v| ≤ |B| := by
    intro v hv
    have := hB v hv
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self B)
  have key := (hP m).abs_le hPmj hBv R hτ hv
  refine key.trans ?_
  have h1τ : (1 : ℝ) ≤ 1 + τ := by linarith
  have hW' : (wordLen m (List.finRange d) : ℝ) + 1 ≤ (Wp : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hW
  have h2 : (2 : ℝ) ^ wordLen m (List.finRange d) ≤ 2 ^ Wp := pow_le_pow_right₀ (by norm_num) hW
  have h3 : (1 + τ) ^ wordLen m (List.finRange d) ≤ (1 + τ) ^ Wp := pow_le_pow_right₀ h1τ hW
  calc ((wordLen m (List.finRange d) : ℝ) + 1) * (Pm * 2 ^ wordLen m (List.finRange d)) *
        (1 + τ) ^ wordLen m (List.finRange d) * ((1 / 2) ^ R * Real.exp (3 * |B| * τ))
      ≤ ((Wp : ℝ) + 1) * (Pm * 2 ^ Wp) * (1 + τ) ^ Wp * ((1 / 2) ^ R * Real.exp (3 * |B| * τ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul (mul_le_mul hW' (mul_le_mul_of_nonneg_left h2 hPm0)
          (mul_nonneg hPm0 (by positivity)) (by positivity)) h3
          (pow_nonneg (by linarith) _)
          (mul_nonneg (by positivity) (mul_nonneg hPm0 (by positivity)))
    _ = _ := by ring

end SmoothEngine

end Grammar
