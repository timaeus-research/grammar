/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.FieldJetUniform

/-!
# Jet bounds for differences of field families

The difference counterpart of `FieldJetUniform`: for smooth fields `ζ₁, ζ₂` whose jets of order
`≤ |p|` are `ε`-close on the closed box (`ε ≤ 1`), with the jets of `ζ₂` bounded by `B`, the
coordinate jets of the difference of the field families `η e^{τζ₁} − η e^{τζ₂}` are bounded by
`C ε (1 + τ)^{2|p|+1} e^{(B+E)τ}` with ONE constant `C` for the whole jet ball. The proof writes the
difference as `η e^{τζ₂} (e^{τ(ζ₁−ζ₂)} − 1)`, bounds the second factor by Faà di Bruno with the
smallness `‖D^i(τ(ζ₁−ζ₂))‖ ≤ τε` (choosing `D = (τε)^{1/n}` when `τε ≤ 1`), and applies Leibniz.
The closeness parameter is allowed up to a fixed `E ≥ 1` (the cube-to-unit-box transport dilates
jets by `(max 1 b)^{|p|}`), at the price of the factor `E^{|p|}` and the rate `B + E`.
This is the envelope the Lipschitz estimate for the lower cube coefficients needs (consult #153).
-/

open Filter Topology Set Finset Real
open scoped ContDiff

namespace Grammar

open SmoothEngine

variable {d : ℕ} {η ζ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ}

/-- **Faà di Bruno with smallness**: if the jets of `δ` of orders `≤ n` at `v` are bounded by
`ε ≤ E` (`1 ≤ E`), then `‖D^n (e^{τδ} − 1)(v)‖ ≤ n! e^{τε} · τε · (E (1 + τ))^n`. -/
theorem norm_iteratedFDeriv_exp_mul_sub_one_le {δ : (Fin d → ℝ) → ℝ} (hδ : ContDiff ℝ ∞ δ)
    {ε E : ℝ} (hε : 0 ≤ ε) (hE : 1 ≤ E) (hε1 : ε ≤ E) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ)
    {v : Fin d → ℝ} (hbound : ∀ r ≤ n, ‖iteratedFDeriv ℝ r δ v‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (fun v => exp (τ * δ v) - 1) v‖ ≤
      n.factorial * exp (τ * ε) * (τ * ε) * (E * (1 + τ)) ^ n := by
  have hδv : |δ v| ≤ ε := by
    have := hbound 0 (Nat.zero_le _)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hf : ContDiff ℝ ∞ fun v => τ * δ v := contDiff_const.mul hδ
  have hexp : ContDiff ℝ ∞ fun v => exp (τ * δ v) := contDiff_exp.comp hf
  have hτδ : |τ * δ v| ≤ τ * ε := by
    rw [abs_mul, abs_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left hδv hτ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one]
    calc |exp (τ * δ v) - 1| ≤ |τ * δ v| * exp |τ * δ v| := abs_exp_sub_one_le_abs_mul_exp _
      _ ≤ (τ * ε) * exp (τ * ε) :=
          mul_le_mul hτδ (exp_le_exp.2 hτδ) (exp_pos _).le (by positivity)
      _ = exp (τ * ε) * (τ * ε) := mul_comm _ _
  · have hconst : iteratedFDeriv ℝ n (fun v => exp (τ * δ v) - 1) v =
        iteratedFDeriv ℝ n (fun v => exp (τ * δ v)) v := by
      have heq : (fun v => exp (τ * δ v) - 1) = (fun v => exp (τ * δ v)) - fun _ => (1 : ℝ) := rfl
      rw [heq, iteratedFDeriv_sub_apply (hexp.of_le (natCast_le_infty n)).contDiffAt
        contDiffAt_const, iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply, sub_zero]
    rw [hconst]
    have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i exp ((fun v => τ * δ v) v)‖ ≤ exp (τ * ε) := by
      intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
        Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.2 ((le_abs_self _).trans hτδ)
    have hDi : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (fun v => τ * δ v) v‖ ≤ τ * ε := by
      intro i _ hin
      have heq : (fun v => τ * δ v) = τ • δ := rfl
      rw [heq, iteratedFDeriv_const_smul_apply ((hδ.of_le (natCast_le_infty i)).contDiffAt),
        norm_smul, Real.norm_of_nonneg hτ]
      exact mul_le_mul_of_nonneg_left (hbound i hin) hτ
    set t : ℝ := τ * ε with ht
    have ht0 : 0 ≤ t := by positivity
    have hEτ : (1 : ℝ) ≤ E * (1 + τ) := by nlinarith
    have hpow1 : (1 : ℝ) ≤ (E * (1 + τ)) ^ n := one_le_pow₀ hEτ
    rcases le_or_gt t 1 with ht1 | ht1
    · set D : ℝ := t ^ ((n : ℝ)⁻¹) with hDdef
      have hDn : D ^ n = t := Real.rpow_inv_natCast_pow ht0 hn.ne'
      have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (fun v => τ * δ v) v‖ ≤ D ^ i := by
        intro i hi hin
        refine (hDi i hi hin).trans ?_
        rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · rw [← h0]
          exact Real.rpow_nonneg le_rfl _
        · have hexp1 : (n : ℝ)⁻¹ * i ≤ 1 := by
            rw [inv_mul_le_iff₀ (by exact_mod_cast hn), mul_one]
            exact_mod_cast hin
          calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
            _ ≤ t ^ ((n : ℝ)⁻¹ * i) := Real.rpow_le_rpow_of_exponent_ge h0 ht1 hexp1
      have h := norm_iteratedFDeriv_comp_le (g := exp) (f := fun v => τ * δ v) contDiff_exp hf
        (natCast_le_infty n) v hC hD
      rw [hDn] at h
      refine h.trans ?_
      calc (n.factorial : ℝ) * exp (τ * ε) * t
          ≤ (n.factorial : ℝ) * exp (τ * ε) * t * (E * (1 + τ)) ^ n :=
            le_mul_of_one_le_right (by positivity) hpow1
        _ = _ := by rw [ht]
    · have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (fun v => τ * δ v) v‖ ≤ t ^ i :=
        fun i hi hin => (hDi i hi hin).trans (le_self_pow₀ ht1.le (by omega))
      have h := norm_iteratedFDeriv_comp_le (g := exp) (f := fun v => τ * δ v) contDiff_exp hf
        (natCast_le_infty n) v hC hD
      refine h.trans ?_
      have ht_le : t ≤ E * (1 + τ) := by rw [ht]; nlinarith
      have h1 : t ^ n ≤ t * (E * (1 + τ)) ^ n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [pow_succ, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ ht0
        calc t ^ m ≤ (E * (1 + τ)) ^ m := pow_le_pow_left₀ ht0 ht_le m
          _ ≤ (E * (1 + τ)) ^ (m + 1) := pow_le_pow_right₀ hEτ (Nat.le_succ m)
      calc (n.factorial : ℝ) * exp (τ * ε) * t ^ n
          ≤ (n.factorial : ℝ) * exp (τ * ε) * (t * (E * (1 + τ)) ^ n) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by rw [ht]; ring

/-- The Fréchet jets of the field family `η e^{τζ}` at a point where the jets of `η` are bounded by
`Bη` and those of `ζ` by `B`. -/
theorem norm_iteratedFDeriv_fieldFam_le (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) {B Bη : ℝ}
    (hB : 0 ≤ B) (hBη0 : 0 ≤ Bη) {τ : ℝ} (hτ : 0 ≤ τ) (r : ℕ) {v : Fin d → ℝ}
    (hηB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i η v‖ ≤ Bη) (hζB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i ζ v‖ ≤ B) :
    ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖ ≤
      2 ^ r * r.factorial * Bη * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r := by
  have hexp : ContDiff ℝ ∞ fun v => exp (τ * ζ v) := contDiff_exp.comp (contDiff_const.mul hζ)
  have h2 : ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖ ≤ ∑ i ∈ range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
        ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ :=
    norm_iteratedFDeriv_mul_le hη hexp v (natCast_le_infty r)
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have h3 : ∀ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
      ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ ≤
      (r.choose i : ℝ) * (Bη * (r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r)) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hηi : ‖iteratedFDeriv ℝ i η v‖ ≤ Bη := hηB i hi'
    have hexpi := norm_iteratedFDeriv_exp_mul_le hζ hB hτ (r - i) (v := v)
      fun s hs => hζB s (hs.trans (Nat.sub_le r i))
    have hfac : ((r - i).factorial : ℝ) ≤ r.factorial := by
      exact_mod_cast Nat.factorial_le (Nat.sub_le r i)
    have hpow : ((1 + τ) * (1 + B)) ^ (r - i) ≤ ((1 + τ) * (1 + B)) ^ r :=
      pow_le_pow_right₀ hD1 (Nat.sub_le r i)
    have hexpi' : ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ ≤
        r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r :=
      hexpi.trans (by gcongr)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hηi hexpi' (norm_nonneg _) hBη0
  have h4 : ∑ i ∈ range (r + 1), (r.choose i : ℝ) *
      (Bη * (r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r)) =
      2 ^ r * (Bη * (r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r)) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose r
  calc ‖iteratedFDeriv ℝ r (fieldFam η ζ τ) v‖
      ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η v‖ *
          ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * ζ v)) v‖ := h2
    _ ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) *
          (Bη * (r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r)) := Finset.sum_le_sum h3
    _ = 2 ^ r * (Bη * (r.factorial * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r)) := h4
    _ = _ := by ring

/-- The difference of two field families factors through `e^{τ(ζ₁−ζ₂)} − 1`. -/
theorem fieldFam_sub_eq (η ζ₁ ζ₂ : (Fin d → ℝ) → ℝ) (τ : ℝ) :
    (fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v) =
      fun v => fieldFam η ζ₂ τ v * (exp (τ * (ζ₁ v - ζ₂ v)) - 1) := by
  funext v
  unfold fieldFam
  have h : exp (τ * ζ₂ v) * exp (τ * (ζ₁ v - ζ₂ v)) = exp (τ * ζ₁ v) := by
    rw [← exp_add]
    congr 1
    ring
  rw [mul_sub, mul_one, mul_assoc, h]

/-- **Fréchet jets of the difference of two field families** at a point where the jets of `η` are
bounded by `Bη`, those of `ζ₂` by `B`, and those of `ζ₁ − ζ₂` by `ε ≤ E` (`1 ≤ E`). -/
theorem norm_iteratedFDeriv_fieldFam_sub_le (hη : ContDiff ℝ ∞ η) (hζ₁ : ContDiff ℝ ∞ ζ₁)
    (hζ₂ : ContDiff ℝ ∞ ζ₂) {B Bη ε E : ℝ} (hB : 0 ≤ B) (hBη0 : 0 ≤ Bη) (hε : 0 ≤ ε) (hE : 1 ≤ E)
    (hε1 : ε ≤ E) {τ : ℝ} (hτ : 0 ≤ τ) (r : ℕ) {v : Fin d → ℝ}
    (hηB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i η v‖ ≤ Bη)
    (hζB : ∀ i ≤ r, ‖iteratedFDeriv ℝ i ζ₂ v‖ ≤ B)
    (hclose : ∀ i ≤ r, ‖iteratedFDeriv ℝ i ζ₁ v - iteratedFDeriv ℝ i ζ₂ v‖ ≤ ε) :
    ‖iteratedFDeriv ℝ r (fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v) v‖ ≤
      2 ^ r * (2 ^ r * r.factorial * Bη * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r) *
        (r.factorial * exp (τ * ε) * (τ * ε) * (E * (1 + τ)) ^ r) := by
  set G : ℝ := 2 ^ r * r.factorial * Bη * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r with hG
  set W : ℝ := r.factorial * exp (τ * ε) * (τ * ε) * (E * (1 + τ)) ^ r with hW
  have hEτ : (1 : ℝ) ≤ E * (1 + τ) := by nlinarith
  have hG0 : 0 ≤ G := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hδ : ContDiff ℝ ∞ fun v => ζ₁ v - ζ₂ v := hζ₁.sub hζ₂
  have hδclose : ∀ i ≤ r, ‖iteratedFDeriv ℝ i (fun v => ζ₁ v - ζ₂ v) v‖ ≤ ε := by
    intro i hi
    have heq : (fun v => ζ₁ v - ζ₂ v) = ζ₁ - ζ₂ := rfl
    rw [heq, iteratedFDeriv_sub_apply (hζ₁.of_le (natCast_le_infty i)).contDiffAt
      (hζ₂.of_le (natCast_le_infty i)).contDiffAt]
    exact hclose i hi
  have hfam : ContDiff ℝ ∞ (fieldFam η ζ₂ τ) := contDiff_fieldFam hη hζ₂ τ
  have hw : ContDiff ℝ ∞ fun v => exp (τ * (ζ₁ v - ζ₂ v)) - 1 :=
    (contDiff_exp.comp (contDiff_const.mul hδ)).sub contDiff_const
  rw [fieldFam_sub_eq]
  have h2 := norm_iteratedFDeriv_mul_le hfam hw v (natCast_le_infty r)
  refine h2.trans ?_
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have h3 : ∀ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fieldFam η ζ₂ τ) v‖ *
      ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * (ζ₁ v - ζ₂ v)) - 1) v‖ ≤
      (r.choose i : ℝ) * (G * W) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hGi : ‖iteratedFDeriv ℝ i (fieldFam η ζ₂ τ) v‖ ≤ G := by
      refine (norm_iteratedFDeriv_fieldFam_le hη hζ₂ hB hBη0 hτ i (fun s hs => hηB s (hs.trans hi'))
        (fun s hs => hζB s (hs.trans hi'))).trans ?_
      rw [hG]
      have hfac : (i.factorial : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_le hi'
      have hp2 : (2 : ℝ) ^ i ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hi'
      have hpow : ((1 + τ) * (1 + B)) ^ i ≤ ((1 + τ) * (1 + B)) ^ r := pow_le_pow_right₀ hD1 hi'
      gcongr
    have hWi : ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * (ζ₁ v - ζ₂ v)) - 1) v‖ ≤ W := by
      refine (norm_iteratedFDeriv_exp_mul_sub_one_le hδ hε hE hε1 hτ (r - i)
        fun s hs => hδclose s (hs.trans (Nat.sub_le r i))).trans ?_
      rw [hW]
      have hfac : ((r - i).factorial : ℝ) ≤ r.factorial := by
        exact_mod_cast Nat.factorial_le (Nat.sub_le r i)
      have hpow : (E * (1 + τ)) ^ (r - i) ≤ (E * (1 + τ)) ^ r :=
        pow_le_pow_right₀ hEτ (Nat.sub_le r i)
      gcongr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hGi hWi (norm_nonneg _) hG0) (by positivity)
  calc ∑ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fieldFam η ζ₂ τ) v‖ *
        ‖iteratedFDeriv ℝ (r - i) (fun v => exp (τ * (ζ₁ v - ζ₂ v)) - 1) v‖
      ≤ ∑ i ∈ range (r + 1), (r.choose i : ℝ) * (G * W) := Finset.sum_le_sum h3
    _ = 2 ^ r * (G * W) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose r
    _ = _ := by rw [hG, hW]; ring

/-- ★★ **The difference envelope is uniform on jet balls**: one constant `C` such that for all
smooth `ζ₁, ζ₂` with `JetBoundOn |p| (closedBox d b) ζ₂ B` and
`JetClose |p| (closedBox d b) ζ₁ ζ₂ ε` (`ε ≤ E`, `1 ≤ E`), the coordinate jets of
`η e^{τζ₁} − η e^{τζ₂}` of orders `≤ p` on the closed box are bounded by
`C ε (1 + τ)^{2|p|+1} e^{(B+E)τ}`. -/
theorem exists_fieldFam_sub_bound (hη : ContDiff ℝ ∞ η) (p : Fin d → ℕ) {b B : ℝ} (hB : 0 ≤ B)
    {E : ℝ} (hE : 1 ≤ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ₁ ζ₂ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ ζ₁ → ContDiff ℝ ∞ ζ₂ →
      JetBoundOn (∑ i, p i) (closedBox d b) ζ₂ B → ∀ ε, 0 ≤ ε → ε ≤ E →
      JetClose (∑ i, p i) (closedBox d b) ζ₁ ζ₂ ε →
      ∀ m : Fin d → ℕ, (∀ i, m i ≤ p i) → ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ closedBox d b,
        |pdMulti m (List.finRange d) (fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v) v| ≤
          C * ε * (1 + τ) ^ (2 * ∑ i, p i + 1) * exp ((B + E) * τ) := by
  set P : ℕ := ∑ i, p i with hP
  obtain ⟨Bη, hBη0, hBη⟩ := exists_jetBoundOn hη P (isCompact_closedBox b)
  have hE0 : 0 ≤ E := by linarith
  refine ⟨2 ^ P * (2 ^ P * P.factorial * Bη * (1 + B) ^ P) * P.factorial * E ^ P, by positivity,
    fun ζ₁ ζ₂ hζ₁ hζ₂ hζB ε hε0 hε1 hclose m hm τ hτ v hv => ?_⟩
  have hr : ∑ i, m i ≤ P := Finset.sum_le_sum fun i _ => hm i
  set r : ℕ := ∑ i, m i with hr'
  have hdiff : ContDiff ℝ ∞ fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v :=
    (contDiff_fieldFam hη hζ₁ τ).sub (contDiff_fieldFam hη hζ₂ τ)
  have h1 : |pdMulti m (List.finRange d) (fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v) v| ≤
      ‖iteratedFDeriv ℝ r (fun v => fieldFam η ζ₁ τ v - fieldFam η ζ₂ τ v) v‖ := by
    have := abs_pdMulti_le_norm_iteratedFDeriv hdiff m (List.finRange d) v
    rwa [wordLen_finRange] at this
  have h2 := norm_iteratedFDeriv_fieldFam_sub_le hη hζ₁ hζ₂ hB hBη0 hε0 hE hε1 hτ r
    (fun i hi => hBη i (hi.trans hr) v hv) (fun i hi => hζB i (hi.trans hr) v hv)
    (fun i hi => hclose i (hi.trans hr) v hv)
  refine h1.trans (h2.trans ?_)
  have hD1 : (1 : ℝ) ≤ (1 + τ) * (1 + B) := by nlinarith
  have hτ1 : (1 : ℝ) ≤ 1 + τ := by linarith
  have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
  have hfac : (r.factorial : ℝ) ≤ P.factorial := by exact_mod_cast Nat.factorial_le hr
  have hp2 : (2 : ℝ) ^ r ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) hr
  have hpowτB : ((1 + τ) * (1 + B)) ^ r ≤ (1 + τ) ^ P * (1 + B) ^ P := by
    rw [← mul_pow]
    exact pow_le_pow_right₀ hD1 hr
  have hEτ : (1 : ℝ) ≤ E * (1 + τ) := by nlinarith
  have hpowτ : (E * (1 + τ)) ^ r ≤ E ^ P * (1 + τ) ^ P := by
    rw [← mul_pow]
    exact pow_le_pow_right₀ hEτ hr
  have hτle : τ ≤ 1 + τ := by linarith
  have hexp : exp (τ * B) * exp (τ * ε) ≤ exp ((B + E) * τ) := by
    rw [← exp_add]
    exact exp_le_exp.2 (by nlinarith)
  calc 2 ^ r * (2 ^ r * r.factorial * Bη * exp (τ * B) * ((1 + τ) * (1 + B)) ^ r) *
        (r.factorial * exp (τ * ε) * (τ * ε) * (E * (1 + τ)) ^ r)
      ≤ 2 ^ P * (2 ^ P * P.factorial * Bη * exp (τ * B) * ((1 + τ) ^ P * (1 + B) ^ P)) *
        (P.factorial * exp (τ * ε) * ((1 + τ) * ε) * (E ^ P * (1 + τ) ^ P)) := by gcongr
    _ = 2 ^ P * (2 ^ P * P.factorial * Bη * (1 + B) ^ P) * P.factorial * E ^ P * ε *
        (1 + τ) ^ (2 * P + 1) * (exp (τ * B) * exp (τ * ε)) := by ring
    _ ≤ 2 ^ P * (2 ^ P * P.factorial * Bη * (1 + B) ^ P) * P.factorial * E ^ P * ε *
        (1 + τ) ^ (2 * P + 1) * exp ((B + E) * τ) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

end Grammar
