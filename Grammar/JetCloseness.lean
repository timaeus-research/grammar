/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothCoeffContinuity
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Finite-order closeness of smooth maps and its stability (§20, consult #144 unit B, analytic core)

`JetClose R K f₁ f₂ ε`: the `iteratedFDeriv` of orders `≤ R` of `f₁` and `f₂` differ by at most
`ε` on `K` (closeness in `C^R(K)`); `JetBoundOn R K f B`: the jets of orders `≤ R` are bounded by
`B` on `K`. Stability: scalar multiples (`JetClose.const_smul`), products with a fixed smooth
factor (★ `JetClose.mul_left`, Leibniz `norm_iteratedFDeriv_mul_le`), and composition with a
fixed smooth outer map (★★ `exists_jetClose_comp`): for `g` smooth and a jet bound `B` of the
limit, there is `C` with `JetClose R K f₁ f₂ ε → JetClose R K (g ∘ f₁) (g ∘ f₂) (C·ε)` for
`ε ≤ 1`. The composition step is Mathlib's Faà di Bruno formula (`HasFTaylorSeriesUpToOn.comp`):
`D^r(g∘f)(x) = Σ_{c ∈ OrderedFinpartition r} c.comp (D^{|c|}g(f x)) (D^{cᵢ} f x)`, with the
difference bound `norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le`, the
outer jets bounded and Lipschitz on the compact ball `‖y‖ ≤ B + 1`. Bridge to the engine:
`rectBound_of_jetClose`, ★★ `tendsto_smoothCoeff_of_jetClose` (population coefficients are
continuous for `C^{|p|}` closeness on the closed box). Zero `sorry`/`axiom`.
-/

open Set Filter Topology Finset Metric
open scoped ContDiff

namespace Grammar

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem natCast_le_infty (r : ℕ) : (r : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- Closeness of the jets of orders `≤ R` on `K`. -/
def JetClose (R : ℕ) (K : Set E) (f₁ f₂ : E → F) (ε : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x‖ ≤ ε

/-- A bound on the jets of orders `≤ R` on `K`. -/
def JetBoundOn (R : ℕ) (K : Set E) (f : E → F) (B : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f x‖ ≤ B

theorem JetClose.mono_eps {R : ℕ} {K : Set E} {f₁ f₂ : E → F} {ε ε' : ℝ}
    (h : JetClose R K f₁ f₂ ε) (hε : ε ≤ ε') : JetClose R K f₁ f₂ ε' :=
  fun r hr x hx => (h r hr x hx).trans hε

theorem JetClose.symm {R : ℕ} {K : Set E} {f₁ f₂ : E → F} {ε : ℝ} (h : JetClose R K f₁ f₂ ε) :
    JetClose R K f₂ f₁ ε := fun r hr x hx => by rw [norm_sub_rev]; exact h r hr x hx

theorem JetClose.nonneg {R : ℕ} {K : Set E} {f₁ f₂ : E → F} {ε : ℝ} (h : JetClose R K f₁ f₂ ε)
    (hK : K.Nonempty) : 0 ≤ ε := by
  obtain ⟨x, hx⟩ := hK
  exact (norm_nonneg _).trans (h 0 (Nat.zero_le _) x hx)

theorem JetBoundOn.mono_of_le {R : ℕ} {K : Set E} {f : E → F} {B B' : ℝ}
    (h : JetBoundOn R K f B) (hB : B ≤ B') : JetBoundOn R K f B' :=
  fun r hr x hx => (h r hr x hx).trans hB

/-- The jets of a smooth map are bounded on a compact set. -/
theorem exists_jetBoundOn {f : E → F} (hf : ContDiff ℝ ∞ f) (R : ℕ) {K : Set E}
    (hK : IsCompact K) : ∃ B, 0 ≤ B ∧ JetBoundOn R K f B := by
  have h : ∀ r : ℕ, ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r f x‖ ≤ B := fun r =>
    hK.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (natCast_le_infty r)).continuousOn
  choose Bf hBf using h
  refine ⟨∑ r ∈ range (R + 1), |Bf r|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro r hr x hx
  refine (hBf r x hx).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun r => |Bf r|) (fun _ _ => abs_nonneg _)
    (mem_range.2 (Nat.lt_succ_of_le hr))

theorem JetBoundOn.of_jetClose {R : ℕ} {K : Set E} {f₁ f₂ : E → F} {B ε : ℝ}
    (hB : JetBoundOn R K f₂ B) (hc : JetClose R K f₁ f₂ ε) : JetBoundOn R K f₁ (B + ε) := by
  intro r hr x hx
  calc ‖iteratedFDeriv ℝ r f₁ x‖
      = ‖iteratedFDeriv ℝ r f₂ x + (iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x)‖ := by
        rw [add_sub_cancel]
    _ ≤ ‖iteratedFDeriv ℝ r f₂ x‖ + ‖iteratedFDeriv ℝ r f₁ x - iteratedFDeriv ℝ r f₂ x‖ :=
        norm_add_le _ _
    _ ≤ B + ε := add_le_add (hB r hr x hx) (hc r hr x hx)

/-! ### Scalar multiples and products -/

theorem JetClose.const_smul {R : ℕ} {K : Set E} {f₁ f₂ : E → F} {ε : ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₂ : ContDiff ℝ ∞ f₂) (hc : JetClose R K f₁ f₂ ε) (a : ℝ) :
    JetClose R K (fun x => a • f₁ x) (fun x => a • f₂ x) (|a| * ε) := by
  intro r hr x hx
  have h1 : (fun x => a • f₁ x) = a • f₁ := rfl
  have h2 : (fun x => a • f₂ x) = a • f₂ := rfl
  rw [h1, h2, iteratedFDeriv_const_smul_apply (hf₁.of_le (natCast_le_infty r)).contDiffAt,
    iteratedFDeriv_const_smul_apply (hf₂.of_le (natCast_le_infty r)).contDiffAt, ← smul_sub,
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hc r hr x hx) (abs_nonneg a)

/-- ★ **Products with a fixed smooth factor**: `‖D^r(η(f₁ − f₂))‖ ≤ 2^r · Bη · ε` by Leibniz. -/
theorem JetClose.mul_left {R : ℕ} {K : Set E} {η f₁ f₂ : E → ℝ} {Bη ε : ℝ} (hη : ContDiff ℝ ∞ η)
    (hηB : JetBoundOn R K η Bη) (hBη : 0 ≤ Bη) (hf₁ : ContDiff ℝ ∞ f₁) (hf₂ : ContDiff ℝ ∞ f₂)
    (hε : 0 ≤ ε) (hc : JetClose R K f₁ f₂ ε) :
    JetClose R K (fun x => η x * f₁ x) (fun x => η x * f₂ x) (2 ^ R * Bη * ε) := by
  intro r hr x hx
  have hsub : (fun x => η x * f₁ x) - (fun x => η x * f₂ x) = fun x => η x * (f₁ x - f₂ x) := by
    funext y
    simp [mul_sub]
  rw [← iteratedFDeriv_sub_apply ((hη.mul hf₁).of_le (natCast_le_infty r)).contDiffAt
    ((hη.mul hf₂).of_le (natCast_le_infty r)).contDiffAt, hsub]
  have hd : ContDiff ℝ ∞ fun y => f₁ y - f₂ y := hf₁.sub hf₂
  refine (norm_iteratedFDeriv_mul_le hη hd x (natCast_le_infty r)).trans ?_
  have hterm : ∀ i ∈ range (r + 1),
      (r.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ *
        ‖iteratedFDeriv ℝ (r - i) (fun y => f₁ y - f₂ y) x‖ ≤ (r.choose i : ℝ) * (Bη * ε) := by
    intro i hi
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hη' := hηB i (hi'.trans hr) x hx
    have hf' : ‖iteratedFDeriv ℝ (r - i) (fun y => f₁ y - f₂ y) x‖ ≤ ε := by
      have hfun : (fun y => f₁ y - f₂ y) = f₁ - f₂ := rfl
      rw [hfun, iteratedFDeriv_sub_apply (hf₁.of_le (natCast_le_infty _)).contDiffAt
        (hf₂.of_le (natCast_le_infty _)).contDiffAt]
      exact hc (r - i) ((Nat.sub_le r i).trans hr) x hx
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hη' hf' (norm_nonneg _) hBη) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hchoose : ∑ i ∈ range (r + 1), (r.choose i : ℝ) = 2 ^ r := by
    exact_mod_cast Nat.sum_range_choose r
  rw [hchoose, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hε
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hr) hBη

/-! ### Composition with a fixed smooth outer map -/

/-- Faà di Bruno: the iterated derivative of a composition as the ordered-finpartition sum. -/
theorem iteratedFDeriv_comp_eq_sum {g : F → G} {f : E → F} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E) :
    iteratedFDeriv ℝ r (g ∘ f) x = ∑ c : OrderedFinpartition r,
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f x))
        (fun m => iteratedFDeriv ℝ (c.partSize m) f x) := by
  have hT := (hasFTaylorSeriesUpToOn_univ_iff.2 hg.ftaylorSeries).comp
    (hasFTaylorSeriesUpToOn_univ_iff.2 hf.ftaylorSeries) (Set.mapsTo_univ _ _)
  rw [hasFTaylorSeriesUpToOn_univ_iff] at hT
  rw [← hT.eq_iteratedFDeriv (natCast_le_infty r) x]
  rfl

/-- ★★ **Composition is finite-order stable**: for `g` smooth and a jet bound `B` of the limit
`f₂` on `K`, there is `C` such that `ε`-closeness of `f₁, f₂` in `C^R(K)` (`ε ≤ 1`) gives
`C·ε`-closeness of `g ∘ f₁, g ∘ f₂`. -/
theorem exists_jetClose_comp [ProperSpace F] {g : F → G} (hg : ContDiff ℝ ∞ g) (R : ℕ)
    (K : Set E) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ f₁ f₂ : E → F, ContDiff ℝ ∞ f₁ → ContDiff ℝ ∞ f₂ → JetBoundOn R K f₂ B →
      ∀ ε, 0 ≤ ε → ε ≤ 1 → JetClose R K f₁ f₂ ε → JetClose R K (g ∘ f₁) (g ∘ f₂) (C * ε) := by
  set L : Set F := closedBall 0 (B + 1) with hL
  have hLc : IsCompact L := isCompact_closedBall 0 (B + 1)
  have hLconv : Convex ℝ L := convex_closedBall 0 (B + 1)
  -- bounds and Lipschitz constants of the outer jets on `L`
  have hbnd : ∀ j : ℕ, ∃ Cj : ℝ, ∀ y ∈ L, ‖iteratedFDeriv ℝ j g y‖ ≤ Cj := fun j =>
    hLc.exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (natCast_le_infty j)).continuousOn
  choose Cf hCf using hbnd
  have hlip : ∀ j : ℕ, ∃ Kj : NNReal, LipschitzOnWith Kj (iteratedFDeriv ℝ j g) L := fun j =>
    (hg.iteratedFDeriv_right (m := 1) (i := j) (by exact_mod_cast le_top)).contDiffOn
      |>.exists_lipschitzOnWith one_ne_zero hLconv hLc
  choose Kf hKf using hlip
  set Cg : ℝ := ∑ j ∈ range (R + 1), |Cf j| with hCg
  set Lip : ℝ := ∑ j ∈ range (R + 1), (Kf j : ℝ) with hLip
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hLip0 : 0 ≤ Lip := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCg_le : ∀ j ≤ R, ∀ y ∈ L, ‖iteratedFDeriv ℝ j g y‖ ≤ Cg := fun j hj y hy =>
    (hCf j y hy).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cf j|)
      (fun _ _ => abs_nonneg _) (mem_range.2 (Nat.lt_succ_of_le hj))))
  have hLip_le : ∀ j ≤ R, (Kf j : ℝ) ≤ Lip := fun j hj =>
    Finset.single_le_sum (f := fun j => (Kf j : ℝ)) (fun _ _ => NNReal.coe_nonneg _)
      (mem_range.2 (Nat.lt_succ_of_le hj))
  -- the per-order constant
  set P : ℝ := (B + 1) ^ R with hP
  have hP0 : 0 ≤ P := pow_nonneg (by linarith) R
  have hB1 : 1 ≤ B + 1 := by linarith
  set Cr : ℕ → ℝ := fun r => (Fintype.card (OrderedFinpartition r) : ℝ) * (Cg * R * P + Lip * P)
    with hCr
  have hCr0 : ∀ r, 0 ≤ Cr r := fun r => mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (mul_nonneg (mul_nonneg hCg0 (Nat.cast_nonneg _)) hP0) (mul_nonneg hLip0 hP0))
  refine ⟨∑ r ∈ range (R + 1), Cr r, Finset.sum_nonneg fun r _ => hCr0 r, ?_⟩
  intro f₁ f₂ hf₁ hf₂ hB₂ ε hε0 hε1 hc r hr x hx
  have hCr_le : Cr r ≤ ∑ r ∈ range (R + 1), Cr r :=
    Finset.single_le_sum (f := Cr) (fun r _ => hCr0 r) (mem_range.2 (Nat.lt_succ_of_le hr))
  -- the values lie in `L`
  have hB₁ : JetBoundOn R K f₁ (B + ε) := hB₂.of_jetClose hc
  have hy₂ : f₂ x ∈ L := by
    rw [hL, mem_closedBall_zero_iff, ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (hB₂ 0 (Nat.zero_le _) x hx).trans (by linarith)
  have hy₁ : f₁ x ∈ L := by
    rw [hL, mem_closedBall_zero_iff, ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact (hB₁ 0 (Nat.zero_le _) x hx).trans (by linarith)
  have hval : ‖f₁ x - f₂ x‖ ≤ ε := by
    have h0 := hc 0 (Nat.zero_le _) x hx
    rw [← iteratedFDeriv_sub_apply (hf₁.of_le (natCast_le_infty 0)).contDiffAt
      (hf₂.of_le (natCast_le_infty 0)).contDiffAt, norm_iteratedFDeriv_zero] at h0
    exact h0
  -- Faà di Bruno on both sides
  rw [iteratedFDeriv_comp_eq_sum hg hf₁, iteratedFDeriv_comp_eq_sum hg hf₂,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ c : OrderedFinpartition r,
      ‖c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f₁ x))
          (fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x) -
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f₂ x))
          (fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x)‖ ≤ (Cg * R * P + Lip * P) * ε := by
    intro c
    refine (c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le _ _ _ _).trans
      ?_
    have hlen : c.length ≤ R := c.length_le.trans hr
    have hq₁ : ‖iteratedFDeriv ℝ c.length g (f₁ x)‖ ≤ Cg := hCg_le _ hlen _ hy₁
    have hg₁ : ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x‖ ≤ B + 1 := by
      rw [pi_norm_le_iff_of_nonneg (by linarith)]
      intro m
      exact (hB₁ _ ((c.partSize_le m).trans hr) x hx).trans (by linarith)
    have hg₂ : ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x‖ ≤ B + 1 := by
      rw [pi_norm_le_iff_of_nonneg (by linarith)]
      intro m
      exact (hB₂ _ ((c.partSize_le m).trans hr) x hx).trans (by linarith)
    have hmax : max ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x‖
        ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x‖ ^ (c.length - 1) ≤ P := by
      refine (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) (max_le hg₁ hg₂) _).trans ?_
      exact pow_le_pow_right₀ hB1 ((Nat.sub_le _ _).trans hlen)
    have hdiff : ‖(fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x) -
        fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x‖ ≤ ε := by
      rw [pi_norm_le_iff_of_nonneg hε0]
      intro m
      exact hc _ ((c.partSize_le m).trans hr) x hx
    have hqdiff : ‖iteratedFDeriv ℝ c.length g (f₁ x) - iteratedFDeriv ℝ c.length g (f₂ x)‖ ≤
        Lip * ε := by
      have := (hKf c.length).dist_le_mul _ hy₁ _ hy₂
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this.trans (mul_le_mul (hLip_le _ hlen) hval (norm_nonneg _) hLip0)
    have hprod : ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) f₂ x‖ ≤ P := by
      calc ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) f₂ x‖
          ≤ ∏ _m : Fin c.length, (B + 1) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ =>
              (hB₂ _ ((c.partSize_le m).trans hr) x hx).trans (by linarith)
        _ = (B + 1) ^ c.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ P := pow_le_pow_right₀ hB1 hlen
    have hlenR : (c.length : ℝ) ≤ R := by exact_mod_cast hlen
    calc ‖iteratedFDeriv ℝ c.length g (f₁ x)‖ * c.length *
          max ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x‖
            ‖fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x‖ ^ (c.length - 1) *
          ‖(fun m => iteratedFDeriv ℝ (c.partSize m) f₁ x) -
            fun m => iteratedFDeriv ℝ (c.partSize m) f₂ x‖ +
        ‖iteratedFDeriv ℝ c.length g (f₁ x) - iteratedFDeriv ℝ c.length g (f₂ x)‖ *
          ∏ m, ‖iteratedFDeriv ℝ (c.partSize m) f₂ x‖
        ≤ Cg * R * P * ε + Lip * ε * P := by
          gcongr
      _ = (Cg * R * P + Lip * P) * ε := by ring
  refine (Finset.sum_le_sum fun c _ => hterm c).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hCr_le hε0

/-! ### Bridge to the population coefficients -/

namespace SmoothEngine

variable {d : ℕ}

/-- `C^{Σp}` closeness on the closed box gives the rectangular bound of the difference at depth
`p`. -/
theorem rectBound_of_jetClose {f₁ f₂ : (Fin d → ℝ) → ℝ} (hf₁ : ContDiff ℝ ∞ f₁)
    (hf₂ : ContDiff ℝ ∞ f₂) (p : Fin d → ℕ) {b ε : ℝ}
    (hc : JetClose (∑ i, p i) (closedBox d b) f₁ f₂ ε) :
    RectBound (fun v => f₁ v - f₂ v) p b ε := by
  refine rectBound_of_iteratedFDeriv (hf₁.sub hf₂) p fun r hr v hv => ?_
  have hfun : (fun v => f₁ v - f₂ v) = f₁ - f₂ := rfl
  rw [hfun, iteratedFDeriv_sub_apply (hf₁.of_le (natCast_le_infty r)).contDiffAt
    (hf₂.of_le (natCast_le_infty r)).contDiffAt]
  exact hc r hr v hv

/-- ★★ **Continuity of a canonical coefficient for `C^{|p|}` closeness on the closed box**, with
the closeness only required eventually. -/
theorem tendsto_smoothCoeff_of_jetClose {F : ℕ → (Fin d → ℝ) → ℝ} {G : (Fin d → ℝ) → ℝ}
    {h k : Fin d → ℕ} {β b : ℝ} (hF : ∀ n, ContDiff ℝ ∞ (F n)) (hG : ContDiff ℝ ∞ G)
    (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b) {μ : ℝ} {M : ℕ → ℝ}
    (hM : ∀ᶠ n in atTop,
      JetClose (∑ i, depthOf h k (cutoffOf h μ) i) (closedBox d b) (F n) G (M n))
    (hM0 : Tendsto M atTop (𝓝 0)) (q : ℕ) :
    Tendsto (fun n => smoothCoeff (F n) h k β b μ q) atTop (𝓝 (smoothCoeff G h k β b μ q)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) (hM.mono fun n hn => ?_)
    (by simpa using hM0.const_mul (coeffBoundConstant h k (depthOf h k (cutoffOf h μ)) β b μ q))
  rw [Real.norm_eq_abs]
  exact abs_smoothCoeff_sub_le (hF n) hG hk hβ hb (rectBound_of_jetClose (hF n) hG _ hn) q

end SmoothEngine

end Grammar
