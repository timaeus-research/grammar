/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.JetCloseness

/-!
# Products and powers in the jet calculus

`JetClose.trans`, `JetBoundOn.mul`, `JetClose.mul` (two varying factors), `JetBoundOn.pow`, and
the finite-order stability of powers `exists_jetClose_pow` (one constant per `(R, K, B, r)`).

Zero `sorry`/`axiom`.
-/

open Filter Topology Set Finset
open scoped ContDiff

namespace Grammar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem JetClose.refl (R : ℕ) (K : Set E) (f : E → ℝ) : JetClose R K f f 0 :=
  fun _ _ _ _ => by simp

theorem JetClose.trans {R : ℕ} {K : Set E} {f₁ f₂ f₃ : E → ℝ} {ε₁ ε₂ : ℝ}
    (h₁ : JetClose R K f₁ f₂ ε₁) (h₂ : JetClose R K f₂ f₃ ε₂) : JetClose R K f₁ f₃ (ε₁ + ε₂) := by
  intro r hr x hx
  calc ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₃ x‖
      = ‖(iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x) +
          (iteratedFDeriv ℝ r f₂ x - iteratedFDeriv ℝ r f₃ x)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x‖ +
          ‖iteratedFDeriv ℝ r f₂ x - iteratedFDeriv ℝ r f₃ x‖ := norm_add_le _ _
    _ ≤ ε₁ + ε₂ := add_le_add (h₁ r hr x hx) (h₂ r hr x hx)

theorem jetBoundOn_const_fun (R : ℕ) (K : Set E) (c : ℝ) :
    JetBoundOn R K (fun _ : E => c) ‖c‖ := by
  intro r _ x _
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hr.ne']
    simp

/-- Leibniz: jets of a product are bounded by `2^R Bf Bg`. -/
theorem JetBoundOn.mul {R : ℕ} {K : Set E} {f g : E → ℝ} {Bf Bg : ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfB : JetBoundOn R K f Bf) (hgB : JetBoundOn R K g Bg) (hBf : 0 ≤ Bf)
    (hBg : 0 ≤ Bg) : JetBoundOn R K (fun x => f x * g x) (2 ^ R * Bf * Bg) := by
  intro r hr x hx
  refine (norm_iteratedFDeriv_mul_le hf hg x (natCast_le_infty r)).trans ?_
  have hterm : ∀ i ∈ range (r + 1), (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (r - i) g x‖ ≤ (r.choose i : ℝ) * (Bf * Bg) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hfB i (hi'.trans hr) x hx)
      (hgB (r - i) ((Nat.sub_le r i).trans hr) x hx) (norm_nonneg _) hBf) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, show ∑ i ∈ range (r + 1), (r.choose i : ℝ) = 2 ^ r by
    exact_mod_cast Nat.sum_range_choose r, mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hr) (mul_nonneg hBf hBg)

/-- Products with two varying factors: `f₁g₁ − f₂g₂ = (f₁ − f₂)g₁ + f₂(g₁ − g₂)`. -/
theorem JetClose.mul {R : ℕ} {K : Set E} {f₁ f₂ g₁ g₂ : E → ℝ} {Bf Bg εf εg : ℝ}
    (hf₁ : ContDiff ℝ ∞ f₁) (hf₂ : ContDiff ℝ ∞ f₂) (hg₁ : ContDiff ℝ ∞ g₁)
    (hg₂ : ContDiff ℝ ∞ g₂) (hg₁B : JetBoundOn R K g₁ Bg) (hBg : 0 ≤ Bg)
    (hf₂B : JetBoundOn R K f₂ Bf) (hBf : 0 ≤ Bf) (hεf : 0 ≤ εf) (hεg : 0 ≤ εg)
    (hf : JetClose R K f₁ f₂ εf) (hg : JetClose R K g₁ g₂ εg) :
    JetClose R K (fun x => f₁ x * g₁ x) (fun x => f₂ x * g₂ x)
      (2 ^ R * Bg * εf + 2 ^ R * Bf * εg) := by
  have h1 : JetClose R K (fun x => g₁ x * f₁ x) (fun x => g₁ x * f₂ x) (2 ^ R * Bg * εf) :=
    JetClose.mul_left hg₁ hg₁B hBg hf₁ hf₂ hεf hf
  have h2 : JetClose R K (fun x => f₂ x * g₁ x) (fun x => f₂ x * g₂ x) (2 ^ R * Bf * εg) :=
    JetClose.mul_left hf₂ hf₂B hBf hg₁ hg₂ hεg hg
  have e1 : (fun x => g₁ x * f₁ x) = fun x => f₁ x * g₁ x := funext fun x => mul_comm _ _
  have e2 : (fun x => g₁ x * f₂ x) = fun x => f₂ x * g₁ x := funext fun x => mul_comm _ _
  rw [e1, e2] at h1
  exact h1.trans h2

theorem JetBoundOn.pow {R : ℕ} {K : Set E} {f : E → ℝ} {B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hfB : JetBoundOn R K f B) (hB : 0 ≤ B) (r : ℕ) :
    JetBoundOn R K (fun x => f x ^ r) ((2 ^ R * B) ^ r) := by
  induction r with
  | zero =>
    have := jetBoundOn_const_fun R K (1 : ℝ)
    simpa using this
  | succ r ih =>
    have h := JetBoundOn.mul (hf.pow r) hf ih hfB (by positivity) hB
    have e : (fun x => f x ^ (r + 1)) = fun x => f x ^ r * f x := funext fun x => pow_succ _ _
    rw [e, show (2 ^ R * B) ^ (r + 1) = 2 ^ R * (2 ^ R * B) ^ r * B by ring]
    exact h

/-- ★ **Powers are finite-order stable**: for every `r` one constant `C` with
`JetClose R K f₁ f₂ ε → JetClose R K (f₁^r) (f₂^r) (C ε)` on the jet ball of radius `B`. -/
theorem exists_jetClose_pow (R : ℕ) (K : Set E) {B : ℝ} (hB : 0 ≤ B) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f₁ f₂ : E → ℝ, ContDiff ℝ ∞ f₁ → ContDiff ℝ ∞ f₂ →
      JetBoundOn R K f₁ B → JetBoundOn R K f₂ B → ∀ ε, 0 ≤ ε → JetClose R K f₁ f₂ ε →
        JetClose R K (fun x => f₁ x ^ r) (fun x => f₂ x ^ r) (C * ε) := by
  induction r with
  | zero =>
    refine ⟨0, le_rfl, fun f₁ f₂ _ _ _ _ ε _ _ => ?_⟩
    rw [zero_mul]
    simpa using JetClose.refl R K (fun _ : E => (1 : ℝ))
  | succ r ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨2 ^ R * B * C + 2 ^ R * (2 ^ R * B) ^ r, by positivity,
      fun f₁ f₂ hf₁ hf₂ hf₁B hf₂B ε hε hc => ?_⟩
    have h := JetClose.mul (hf₁.pow r) (hf₂.pow r) hf₁ hf₂ hf₁B hB
      (JetBoundOn.pow hf₂ hf₂B hB r) (by positivity) (by positivity) hε
      (hC f₁ f₂ hf₁ hf₂ hf₁B hf₂B ε hε hc) hc
    have e1 : (fun x => f₁ x ^ r * f₁ x) = fun x => f₁ x ^ (r + 1) :=
      funext fun x => (pow_succ _ _).symm
    have e2 : (fun x => f₂ x ^ r * f₂ x) = fun x => f₂ x ^ (r + 1) :=
      funext fun x => (pow_succ _ _).symm
    rw [e1, e2, show 2 ^ R * B * (C * ε) + 2 ^ R * (2 ^ R * B) ^ r * ε =
      (2 ^ R * B * C + 2 ^ R * (2 ^ R * B) ^ r) * ε by ring] at h
    exact h

end Grammar
