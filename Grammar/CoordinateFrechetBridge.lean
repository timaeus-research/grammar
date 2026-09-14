/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothAmplitudeFamily
import Grammar.SmoothExtension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Coordinate partials versus Fréchet derivatives (consult #123 unit C0c)

The smooth engine differentiates amplitudes `G : ℝ^d → ℝ` with COORDINATE partial derivatives:
`pd i G v = d/dt G(v with v_i := t)|_{t = v_i}`, iterated `pdPow i k`, and along a list of
coordinates `pdMulti m l G = ∂_{l₀}^{m l₀} ∂_{l₁}^{m l₁} ⋯ G`. Mathlib's distribution theory and
its chain rule bounds are phrased with the Fréchet derivatives `iteratedFDeriv ℝ n G x`, which are
continuous multilinear maps on `n` vectors. This module is the bridge between the two.

## The word of basis vectors

The `n`-th Fréchet derivative evaluated on a word `w : Fin n → ℝ^d` of basis vectors
`e_i = Pi.single i 1` IS the corresponding coordinate partial: `∂_i G x = D G x (e_i)` is
`pd_eq_fderiv`; one more coordinate derivative of `y ↦ D^n G y (w)` prepends a letter to the word
(`pd_iteratedFDeriv_apply`, from `iteratedFDeriv_succ_apply_left` and the derivative of the
evaluation of a multilinear-map-valued function). Iterating, `pdPow i k` prepends `k` copies of
`e_i` (`consPow`), and `pdMulti m l` builds the word `coordWord m l` of length
`wordLen m l = Σ_{i ∈ l} m i` in the order of `pdMulti`'s recursion:

★ `pdMulti_eqOn_iteratedFDeriv` / `pdMulti_eq_iteratedFDeriv`:
  `∂^m_l G x = D^{|m|} G x (coordWord m l)`,

for `G` smooth on an open set containing `x` (no `Nodup` hypothesis is needed: a repeated
coordinate simply repeats its letters). The words have entries of sup-norm one
(`norm_coordWord`), so the multilinear operator-norm inequality gives the bound that matters
downstream:

★★ `abs_pdMulti_le_norm_iteratedFDeriv`: `|∂^m_l G x| ≤ ‖D^{|m|} G x‖`,

and, for `l = List.finRange d` with `|m| = Σ_i m i`, the rectangular bound of the engine
(`RectBound F p b M`, the hypothesis of the family theorems) follows from a bound on the Fréchet
jets of order `≤ Σ_i p i` on the closed box (★ `rectBound_of_jetBound`).

## The local chain rule for a chart map

For a chart map `ψ` smooth on an open `V` containing a compact `B`, the derivatives of `f ∘ ψ` on
`B` are controlled by those of `f` on `ψ '' B`: by compactness and continuity of the iterated
derivatives of `ψ`, there is `D ≥ 1` with `‖D^i ψ‖ ≤ D^i` on `B` for `1 ≤ i ≤ R`, and Mathlib's
Faà di Bruno type bound `norm_iteratedFDerivWithin_comp_le` (on `V`, where the within-derivatives
are the plain ones by openness) gives `‖D^r (f ∘ ψ) u‖ ≤ r! · M · D^r`. The constant
`C_ψ = Σ_{r ≤ R} r! D^r` depends on `ψ, V, B, R` only:

★ `exists_chart_jet_bound`: `∃ C_ψ ≥ 0, ∀ f smooth, ∀ M ≥ 0, (∀ r ≤ R, ‖D^r f‖ ≤ M on ψ '' B) →
  ∀ r ≤ R, ‖D^r (f ∘ ψ) u‖ ≤ C_ψ · M` for `u ∈ B`,

with the analytic-chart form `exists_chart_jet_bound_of_analyticOnNhd`, the chart box
`centeredBox d a` specialisation, and the composite `exists_rectBound_comp`: a Fréchet jet bound
for the observable on the image of the closed box gives `RectBound (f ∘ ψ) p b (C_ψ · M)`.
Zero `sorry`/`axiom`.
-/

open Set Filter Topology
open scoped ContDiff
open Monomialize.VolumeScaling (centeredBox isCompact_centeredBox)

namespace Grammar

namespace SmoothEngine

variable {d : ℕ}

/-! ### Words of coordinate vectors -/

/-- Prepend `k` copies of `v` to a word `w` of length `n`, giving a word of length `n + k`. -/
def consPow {α : Type*} {n : ℕ} (v : α) : (k : ℕ) → (Fin n → α) → Fin (n + k) → α
  | 0, w => w
  | k + 1, w => Fin.cons v (consPow v k w)

theorem consPow_zero {α : Type*} {n : ℕ} (v : α) (w : Fin n → α) : consPow v 0 w = w := rfl

theorem consPow_succ {α : Type*} {n : ℕ} (v : α) (k : ℕ) (w : Fin n → α) :
    consPow v (k + 1) w = Fin.cons v (consPow v k w) := rfl

theorem norm_consPow_eq_one {n : ℕ} {v : Fin d → ℝ} (hv : ‖v‖ = 1) {w : Fin n → Fin d → ℝ}
    (hw : ∀ j, ‖w j‖ = 1) (k : ℕ) : ∀ j, ‖consPow v k w j‖ = 1 := by
  induction k with
  | zero => exact hw
  | succ k ih =>
    intro j
    rw [consPow_succ]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cons_zero]; exact hv
    · rw [Fin.cons_succ]; exact ih j

/-- The length `Σ_{i ∈ l} m i` of the coordinate word, accumulated in `pdMulti`'s order. -/
def wordLen (m : Fin d → ℕ) : List (Fin d) → ℕ
  | [] => 0
  | i :: l => wordLen m l + m i

/-- The word of basis vectors `e_i = Pi.single i 1`, repeated `m i` times for each `i ∈ l`, in
the order in which `pdMulti m l` applies the coordinate derivatives. -/
def coordWord (m : Fin d → ℕ) : (l : List (Fin d)) → Fin (wordLen m l) → Fin d → ℝ
  | [] => Fin.elim0
  | i :: l => consPow (Pi.single i 1) (m i) (coordWord m l)

theorem wordLen_nil (m : Fin d → ℕ) : wordLen m [] = 0 := rfl

theorem wordLen_cons (m : Fin d → ℕ) (i : Fin d) (l : List (Fin d)) :
    wordLen m (i :: l) = wordLen m l + m i := rfl

theorem coordWord_cons (m : Fin d → ℕ) (i : Fin d) (l : List (Fin d)) :
    coordWord m (i :: l) = consPow (Pi.single i 1) (m i) (coordWord m l) := rfl

theorem wordLen_eq_sum_map (m : Fin d → ℕ) (l : List (Fin d)) : wordLen m l = (l.map m).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [wordLen_cons, List.map_cons, List.sum_cons, ih, add_comm]

theorem wordLen_finRange (m : Fin d → ℕ) : wordLen m (List.finRange d) = ∑ i, m i := by
  rw [wordLen_eq_sum_map, Fin.sum_univ_def]

theorem wordLen_eq_sum_toFinset (m : Fin d → ℕ) {l : List (Fin d)} (hl : l.Nodup) :
    wordLen m l = ∑ i ∈ l.toFinset, m i := by
  rw [wordLen_eq_sum_map, List.sum_toFinset m hl]

theorem norm_coordWord (m : Fin d → ℕ) (l : List (Fin d)) (j : Fin (wordLen m l)) :
    ‖coordWord m l j‖ = 1 := by
  induction l with
  | nil => exact j.elim0
  | cons i l ih => exact norm_consPow_eq_one (by rw [Pi.norm_single, norm_one]) ih (m i) j

theorem prod_norm_coordWord (m : Fin d → ℕ) (l : List (Fin d)) :
    ∏ j, ‖coordWord m l j‖ = 1 :=
  Finset.prod_eq_one fun j _ => norm_coordWord m l j

/-! ### Locality of the coordinate derivative -/

variable {V : Set (Fin d → ℝ)}

theorem pd_eq_fderiv_of_differentiableAt' {G : (Fin d → ℝ) → ℝ} {v : Fin d → ℝ}
    (hG : DifferentiableAt ℝ G v) (i : Fin d) : pd i G v = fderiv ℝ G v (Pi.single i 1) := by
  unfold pd line
  have hG' : DifferentiableAt ℝ G (Function.update v i (v i)) := by
    rwa [Function.update_eq_self]
  have h := hG'.hasFDerivAt.comp_hasDerivAt (v i) (hasDerivAt_update v i (v i))
  rw [Function.update_eq_self] at h
  exact h.deriv

/-- The coordinate derivative on an open set depends only on the values there. -/
theorem pd_congr_eqOn_open (hV : IsOpen V) {G H : (Fin d → ℝ) → ℝ} (h : EqOn G H V) (i : Fin d) :
    EqOn (pd i G) (pd i H) V := by
  intro x hx
  have hcont : Continuous fun t : ℝ => Function.update x i t :=
    continuous_const.update i continuous_id
  have hmem : ∀ᶠ t in 𝓝 (x i), Function.update x i t ∈ V :=
    hcont.continuousAt.eventually_mem (by rw [Function.update_eq_self]; exact hV.mem_nhds hx)
  exact Filter.EventuallyEq.deriv_eq (hmem.mono fun t ht => h ht)

theorem pdPow_congr_eqOn_open (hV : IsOpen V) {G H : (Fin d → ℝ) → ℝ} (h : EqOn G H V)
    (i : Fin d) (k : ℕ) : EqOn (pdPow i k G) (pdPow i k H) V := by
  induction k with
  | zero => exact h
  | succ k ih => rw [pdPow_succ', pdPow_succ']; exact pd_congr_eqOn_open hV ih i

/-! ### The bridge: coordinate partials are Fréchet derivatives on coordinate words -/

/-- One coordinate derivative of the evaluated `n`-th derivative prepends the basis vector. -/
theorem pd_iteratedFDeriv_apply_eqOn (hV : IsOpen V) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) (i : Fin d) (n : ℕ) (w : Fin n → Fin d → ℝ) :
    EqOn (pd i fun y => iteratedFDeriv ℝ n f y w)
      (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.cons (Pi.single i 1) w)) V := by
  intro x hx
  beta_reduce
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
    ((hf.contDiffAt (hV.mem_nhds hx)).iteratedFDeriv_right (m := 1)
      (mod_cast le_top)).differentiableAt one_ne_zero
  rw [pd_eq_fderiv_of_differentiableAt' (hdiff.continuousMultilinear_apply_const w) i,
    fderiv_continuousMultilinear_apply_const_apply hdiff w, iteratedFDeriv_succ_apply_left,
    Fin.cons_zero, Fin.tail_cons]

theorem pdPow_iteratedFDeriv_apply_eqOn (hV : IsOpen V) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) (i : Fin d) (n : ℕ) (w : Fin n → Fin d → ℝ) (k : ℕ) :
    EqOn (pdPow i k fun y => iteratedFDeriv ℝ n f y w)
      (fun y => iteratedFDeriv ℝ (n + k) f y (consPow (Pi.single i 1) k w)) V := by
  induction k with
  | zero => exact fun x _ => rfl
  | succ k ih =>
    rw [pdPow_succ', consPow_succ]
    exact (pd_congr_eqOn_open hV ih i).trans (pd_iteratedFDeriv_apply_eqOn hV hf i (n + k) _)

/-- ★ The coordinate partials of a function smooth on an open set are its Fréchet derivatives
evaluated on the word of basis vectors. -/
theorem pdMulti_eqOn_iteratedFDeriv (hV : IsOpen V) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) (m : Fin d → ℕ) (l : List (Fin d)) :
    EqOn (pdMulti m l f) (fun y => iteratedFDeriv ℝ (wordLen m l) f y (coordWord m l)) V := by
  induction l with
  | nil => exact fun x _ => rfl
  | cons i l ih =>
    rw [pdMulti_cons, coordWord_cons]
    exact (pdPow_congr_eqOn_open hV ih i (m i)).trans
      (pdPow_iteratedFDeriv_apply_eqOn hV hf i (wordLen m l) _ (m i))

/-- ★ Global form: for `f` smooth, `∂^m_l f = D^{|m|} f (coordWord m l)` as functions. -/
theorem pdMulti_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (m : Fin d → ℕ)
    (l : List (Fin d)) :
    pdMulti m l f = fun y => iteratedFDeriv ℝ (wordLen m l) f y (coordWord m l) :=
  funext fun x => pdMulti_eqOn_iteratedFDeriv isOpen_univ hf.contDiffOn m l (mem_univ x)

theorem pdPow_eq_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (k : ℕ) : pdPow i k f = fun y => iteratedFDeriv ℝ k f y fun _ => Pi.single i 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pdPow_succ', ih]
    funext y
    rw [pd_iteratedFDeriv_apply_eqOn isOpen_univ hf.contDiffOn i k _ (mem_univ y)]
    exact congrArg _
      (funext fun j => Fin.cases (Fin.cons_zero _ _) (fun j => Fin.cons_succ _ _ _) j)

/-! ### The norm bound -/

/-- ★★ `|∂^m_l f x| ≤ ‖D^{|m|} f x‖` for `f` smooth on an open set containing `x`. -/
theorem abs_pdMulti_le_norm_iteratedFDeriv_of_mem (hV : IsOpen V) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f V) (m : Fin d → ℕ) (l : List (Fin d)) {x : Fin d → ℝ} (hx : x ∈ V) :
    |pdMulti m l f x| ≤ ‖iteratedFDeriv ℝ (wordLen m l) f x‖ := by
  rw [pdMulti_eqOn_iteratedFDeriv hV hf m l hx, ← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ (wordLen m l) f x (coordWord m l)‖
      ≤ ‖iteratedFDeriv ℝ (wordLen m l) f x‖ * ∏ j, ‖coordWord m l j‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (wordLen m l) f x‖ := by rw [prod_norm_coordWord, mul_one]

/-- ★★ `|∂^m_l f x| ≤ ‖D^{|m|} f x‖` for smooth `f`. -/
theorem abs_pdMulti_le_norm_iteratedFDeriv {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : Fin d → ℕ) (l : List (Fin d)) (x : Fin d → ℝ) :
    |pdMulti m l f x| ≤ ‖iteratedFDeriv ℝ (wordLen m l) f x‖ :=
  abs_pdMulti_le_norm_iteratedFDeriv_of_mem isOpen_univ hf.contDiffOn m l (mem_univ x)

/-- Over all coordinates, the order is `Σ_i m i`. -/
theorem abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem (hV : IsOpen V)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f V) (m : Fin d → ℕ) {x : Fin d → ℝ}
    (hx : x ∈ V) : |pdMulti m (List.finRange d) f x| ≤ ‖iteratedFDeriv ℝ (∑ i, m i) f x‖ := by
  rw [← wordLen_finRange]
  exact abs_pdMulti_le_norm_iteratedFDeriv_of_mem hV hf m _ hx

theorem abs_pdMulti_finRange_le_norm_iteratedFDeriv {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (m : Fin d → ℕ) (x : Fin d → ℝ) :
    |pdMulti m (List.finRange d) f x| ≤ ‖iteratedFDeriv ℝ (∑ i, m i) f x‖ :=
  abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem isOpen_univ hf.contDiffOn m (mem_univ x)

/-- ★ A bound on the Fréchet jets of order `≤ Σ_i p i` on the closed box gives the engine's
rectangular mixed-derivative bound, for `F` smooth on an open set containing the box. -/
theorem rectBound_of_jetBound_of_isOpen (hV : IsOpen V) {b : ℝ} (hBV : closedBox d b ⊆ V)
    {F : (Fin d → ℝ) → ℝ} (hF : ContDiffOn ℝ ∞ F V) (p : Fin d → ℕ) {M : ℝ}
    (h : ∀ r ≤ ∑ i, p i, ∀ v ∈ closedBox d b, ‖iteratedFDeriv ℝ r F v‖ ≤ M) :
    RectBound F p b M := by
  intro m hm v hv
  have hv' : v ∈ closedBox d b := mem_closedBox.2 hv
  exact (abs_pdMulti_finRange_le_norm_iteratedFDeriv_of_mem hV hF m (hBV hv')).trans
    (h _ (Finset.sum_le_sum fun i _ => hm i) v hv')

/-- ★ A bound on the Fréchet jets of order `≤ Σ_i p i` on the closed box gives the engine's
rectangular mixed-derivative bound `RectBound F p b M`. -/
theorem rectBound_of_jetBound {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (p : Fin d → ℕ)
    {b M : ℝ} (h : ∀ r ≤ ∑ i, p i, ∀ v ∈ closedBox d b, ‖iteratedFDeriv ℝ r F v‖ ≤ M) :
    RectBound F p b M :=
  rectBound_of_jetBound_of_isOpen isOpen_univ (subset_univ _) hF.contDiffOn p h

/-! ### The local chain rule for a chart map -/

/-- Uniform bounds `‖D^i ψ u‖ ≤ D^i` (`1 ≤ i ≤ R`, `u ∈ B`) for a map smooth on an open
neighbourhood of a compact set, from compactness and continuity of the iterated derivatives. -/
theorem exists_iteratedFDerivWithin_pow_bound (hV : IsOpen V) {B : Set (Fin d → ℝ)}
    (hB : IsCompact B) (hBV : B ⊆ V) {ψ : (Fin d → ℝ) → Fin d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ V)
    (R : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i, 1 ≤ i → i ≤ R → ∀ u ∈ B, ‖iteratedFDerivWithin ℝ i ψ V u‖ ≤ D ^ i := by
  have hbd : ∀ i : ℕ, ∃ Ci : ℝ, ∀ u ∈ B, ‖iteratedFDerivWithin ℝ i ψ V u‖ ≤ Ci := fun i =>
    hB.exists_bound_of_continuousOn
      ((hψ.continuousOn_iteratedFDerivWithin (mod_cast le_top) hV.uniqueDiffOn).mono hBV)
  choose Ci hCi using hbd
  have hsum : 0 ≤ ∑ i ∈ Finset.range (R + 1), |Ci i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨1 + ∑ i ∈ Finset.range (R + 1), |Ci i|, by linarith, fun i hi1 hiR u hu => ?_⟩
  calc ‖iteratedFDerivWithin ℝ i ψ V u‖ ≤ Ci i := hCi i u hu
    _ ≤ |Ci i| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (R + 1), |Ci j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (Ci j))
          (Finset.mem_range.2 (Nat.lt_succ_of_le hiR))
    _ ≤ 1 + ∑ j ∈ Finset.range (R + 1), |Ci j| := by linarith
    _ ≤ (1 + ∑ j ∈ Finset.range (R + 1), |Ci j|) ^ i :=
        le_self_pow₀ (by linarith) (by omega)

/-- ★ The local chain-rule bound for a chart map: for `ψ` smooth on an open `V ⊇ B`, `B` compact,
there is `C_ψ ≥ 0` (depending on `ψ, V, B, R` only) such that every smooth `f` whose Fréchet jets
of order `≤ R` are bounded by `M` on `ψ '' B` has `‖D^r (f ∘ ψ) u‖ ≤ C_ψ · M` on `B` for
`r ≤ R`. -/
theorem exists_chart_jet_bound (hV : IsOpen V) {B : Set (Fin d → ℝ)} (hB : IsCompact B)
    (hBV : B ⊆ V) {ψ : (Fin d → ℝ) → Fin d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ V) (R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ R, ∀ y ∈ ψ '' B, ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      ∀ r ≤ R, ∀ u ∈ B, ‖iteratedFDeriv ℝ r (f ∘ ψ) u‖ ≤ C * M := by
  obtain ⟨D, hD1, hD⟩ := exists_iteratedFDerivWithin_pow_bound hV hB hBV hψ R
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hterm : ∀ r : ℕ, 0 ≤ (r.factorial : ℝ) * D ^ r := fun r =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD0 r)
  refine ⟨∑ r ∈ Finset.range (R + 1), (r.factorial : ℝ) * D ^ r,
    Finset.sum_nonneg fun r _ => hterm r, ?_⟩
  intro f hf M hM hfM r hr u hu
  have hu' : u ∈ V := hBV hu
  have key : ‖iteratedFDerivWithin ℝ r (f ∘ ψ) V u‖ ≤ (r.factorial : ℝ) * M * D ^ r :=
    norm_iteratedFDerivWithin_comp_le (t := univ) hf.contDiffOn hψ (mod_cast le_top)
      uniqueDiffOn_univ hV.uniqueDiffOn (mapsTo_univ _ _) hu'
      (fun i hi => by
        rw [iteratedFDerivWithin_univ]
        exact hfM i (hi.trans hr) _ (mem_image_of_mem ψ hu))
      (fun i hi1 hir => hD i hi1 (hir.trans hr) u hu)
  rw [← iteratedFDerivWithin_of_isOpen r hV hu']
  calc ‖iteratedFDerivWithin ℝ r (f ∘ ψ) V u‖ ≤ (r.factorial : ℝ) * M * D ^ r := key
    _ = ((r.factorial : ℝ) * D ^ r) * M := by ring
    _ ≤ (∑ r ∈ Finset.range (R + 1), (r.factorial : ℝ) * D ^ r) * M :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
          hM

/-- The chain-rule bound for an analytic chart map. -/
theorem exists_chart_jet_bound_of_analyticOnNhd (hV : IsOpen V) {B : Set (Fin d → ℝ)}
    (hB : IsCompact B) (hBV : B ⊆ V) {ψ : (Fin d → ℝ) → Fin d → ℝ} (hψ : AnalyticOnNhd ℝ ψ V)
    (R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ R, ∀ y ∈ ψ '' B, ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      ∀ r ≤ R, ∀ u ∈ B, ‖iteratedFDeriv ℝ r (f ∘ ψ) u‖ ≤ C * M :=
  exists_chart_jet_bound hV hB hBV (hψ.contDiffOn hV.uniqueDiffOn) R

/-- The chain-rule bound on the chart box `[−a, a]^d`. -/
theorem exists_chart_jet_bound_centeredBox (hV : IsOpen V) {a : ℝ} (hBV : centeredBox d a ⊆ V)
    {ψ : (Fin d → ℝ) → Fin d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ V) (R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ R, ∀ y ∈ ψ '' centeredBox d a, ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      ∀ r ≤ R, ∀ u ∈ centeredBox d a, ‖iteratedFDeriv ℝ r (f ∘ ψ) u‖ ≤ C * M :=
  exists_chart_jet_bound hV (isCompact_centeredBox d a) hBV hψ R

/-- ★ Composite: a Fréchet jet bound for the observable on the image of the closed box `[0,b]^d`
under a chart map gives the engine's rectangular bound for the pulled-back amplitude
`f ∘ ψ`, with a constant depending on the chart only. -/
theorem exists_rectBound_comp (hV : IsOpen V) {b : ℝ} (hBV : closedBox d b ⊆ V)
    {ψ : (Fin d → ℝ) → Fin d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ V) (p : Fin d → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f → ∀ M : ℝ, 0 ≤ M →
      (∀ r ≤ ∑ i, p i, ∀ y ∈ ψ '' closedBox d b, ‖iteratedFDeriv ℝ r f y‖ ≤ M) →
      RectBound (f ∘ ψ) p b (C * M) := by
  obtain ⟨C, hC0, hC⟩ := exists_chart_jet_bound hV (isCompact_closedBox b) hBV hψ (∑ i, p i)
  exact ⟨C, hC0, fun f hf M hM hfM =>
    rectBound_of_jetBound_of_isOpen hV hBV (hf.comp_contDiffOn hψ) p (hC f hf M hM hfM)⟩

end SmoothEngine

end Grammar
