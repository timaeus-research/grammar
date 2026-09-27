/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConeExample
import Grammar.EmpiricalMonomialFamily

/-!
# The tie formula for polynomial amplitudes on the blow-up chart

The blow-up chart of the paper's example `x²(x² + y²)` carries the unequal wall data
`h = (1, 0)`, `k = (2, 1)` (exceptional curve and strict transform), both of ratio `½`: a tie of
order two.  For a polynomial amplitude `η(u) = Σ_γ c_γ u^γ` the chart zeta functional is the
finite sum `Σ_γ c_γ / ((γ₀ + 2 − 4s)(γ₁ + 1 − 2s))`, and its polar data at `½` are

  `C_{½,2}[η] = c_{00}/8`,   `C_{½,1}[η] = −Σ_{γ₀ ≥ 1} c_{γ₀ 0}/(2γ₀) − Σ_{γ₁ ≥ 1} c_{0 γ₁}/(4γ₁)`,

i.e. in the paper's `A`-convention `A_{½,2}[η] = η(0,0)/8` and
`A_{½,1}[η] = ½∫₀¹ (η(u,0) − η(0,0))/u du + ¼∫₀¹ (η(0,v) − η(0,0))/v dv`: the finite parts of the
amplitude along the two walls with the residue factors `1/(2k)`, the lower polar datum of an
unequal-wall tie (★★★ `chartPolarCoeff_polyAmp_half`; examples_slop §4).
The route is that of the cone example: the strip values of the chart zeta functional determine
the face sum near `½`, and the principal part is read off by the uniqueness theorem.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Filter Topology Set Finset Asymptotics
open scoped ContDiff

namespace Grammar

open SmoothEngine

/-- The blow-up chart data: `h = (1, 0)`. -/
def tieH : Fin 2 → ℕ := ![1, 0]

/-- The blow-up chart data: `k = (2, 1)`. -/
def tieK : Fin 2 → ℕ := ![2, 1]

theorem tieK_pos : ∀ i, 0 < tieK i := by
  intro i; fin_cases i <;> simp [tieK]

/-- A polynomial amplitude `Σ_{γ ∈ S} c_γ u^γ`. -/
noncomputable def polyAmp (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  ∑ γ ∈ S, c γ * mono γ u

theorem contDiff_polyAmp (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) :
    ContDiff ℝ ∞ (polyAmp S c) :=
  ContDiff.sum fun γ _ => contDiff_const.mul (contDiff_mono γ)

/-- The rational term of one monomial: `1/((γ₀ + 2 − 4s)(γ₁ + 1 − 2s))`. -/
noncomputable def monoTerm (γ : Fin 2 → ℕ) (s : ℂ) : ℂ :=
  1 / (((γ 0 : ℂ) + 2 - 4 * s) * ((γ 1 : ℂ) + 1 - 2 * s))

/-- The chart zeta functional of a monomial on the strip. -/
theorem chartZeta_mono (γ : Fin 2 → ℕ) {s : ℂ} (hs : ZetaStrip tieH tieK s) :
    chartZeta (fun u => mono γ u) tieH tieK s = monoTerm γ s := by
  have hs' : ZetaStrip (fun i => γ i + tieH i) tieK s := fun i => by
    have := hs i
    have h0 : (0 : ℝ) ≤ γ i := Nat.cast_nonneg _
    push_cast
    linarith
  unfold chartZeta
  rw [show (fun u : Fin 2 → ℝ => ((mono γ u : ℝ) : ℂ) * cpowWeight tieH tieK s u) =
      fun u => (mono γ u : ℂ) * cpowWeight tieH tieK s u from rfl]
  rw [setIntegral_congr_fun (measurableSet_box 1) fun u hu =>
    mono_mul_cpowWeight γ tieH tieK s fun i => pos_of_mem_box hu i,
    integral_box_cpowWeight _ _ hs', Fin.prod_univ_two, monoTerm]
  simp only [tieH, tieK, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [one_div_mul_one_div]
  congr 2 <;> ring

/-- The chart zeta functional of a polynomial amplitude on the strip: a finite sum of rational
terms. -/
theorem chartZeta_polyAmp (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) {s : ℂ}
    (hs : ZetaStrip tieH tieK s) :
    chartZeta (polyAmp S c) tieH tieK s = ∑ γ ∈ S, (c γ : ℂ) * monoTerm γ s := by
  unfold chartZeta polyAmp
  have e : ∀ u : Fin 2 → ℝ, ((∑ γ ∈ S, c γ * mono γ u : ℝ) : ℂ) * cpowWeight tieH tieK s u =
      ∑ γ ∈ S, (c γ : ℂ) * ((mono γ u : ℂ) * cpowWeight tieH tieK s u) := by
    intro u
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_const_mul, ← chartZeta_mono γ hs]
    rfl
  · intro γ _
    have := integrableOn_chartZeta_integrand (G := fun u => mono γ u)
      ((contDiff_mono γ).continuous) tieH tieK hs
    exact this.const_mul _

/-- The polar data at `½` of one monomial term: a double pole `c/8` for `γ = 0`, a simple pole
`−c/(2γ₀)` on the exceptional wall (`γ₁ = 0`), `−c/(4γ₁)` on the strict transform (`γ₀ = 0`),
nothing otherwise. -/
noncomputable def monoA (γ : Fin 2 → ℕ) (c : ℝ) : ℕ → ℂ := fun q =>
  if q = 1 then (if γ 0 = 0 ∧ γ 1 = 0 then (c : ℂ) / 8 else 0)
  else if q = 0 then
    (if γ 1 = 0 ∧ γ 0 ≠ 0 then -(c : ℂ) / (2 * γ 0)
      else if γ 0 = 0 ∧ γ 1 ≠ 0 then -(c : ℂ) / (4 * γ 1) else 0)
  else 0

/-- The polar part of one monomial term, written out. -/
theorem polarPart_monoA (γ : Fin 2 → ℕ) (c : ℝ) (s : ℂ) :
    polarPart 1 (monoA γ c) ((1 / 2 : ℝ) : ℂ) s =
      monoA γ c 0 / (s - (1 / 2 : ℝ)) + monoA γ c 1 / (s - (1 / 2 : ℝ)) ^ 2 := by
  unfold polarPart
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

/-- Near `½`, the monomial term minus its polar part is bounded. -/
theorem monoTerm_sub_polarPart_isBigO (γ : Fin 2 → ℕ) (c : ℝ) :
    (fun s => (c : ℂ) * monoTerm γ s - polarPart 1 (monoA γ c) ((1 / 2 : ℝ) : ℂ) s)
      =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
  -- the two non-resonant denominators are nonzero at `½` unless the exponent vanishes
  have hne0 : ∀ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), s ≠ ((1 / 2 : ℝ) : ℂ) := self_mem_nhdsWithin
  -- case analysis on the exponents
  rcases Nat.eq_zero_or_pos (γ 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (γ 1) with h1 | h1
  · -- `γ = 0`: the term is exactly its polar part
    refine (isBigO_const_const (0 : ℂ) one_ne_zero _).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hne0] with s hs
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    rw [polarPart_monoA, monoTerm]
    simp only [monoA, h0, h1, and_self, if_true, ne_eq, not_true_eq_false, and_false, if_false,
      zero_ne_one]
    push_cast at hs' ⊢
    have hden : ((0 : ℂ) + 2 - 4 * s) * ((0 : ℂ) + 1 - 2 * s) = 8 * (s - 1 / 2) ^ 2 := by ring
    rw [hden]
    field_simp
    ring
  · -- `γ₀ = 0`, `γ₁ ≥ 1`: simple pole `−c/(4γ₁)`, bounded remainder `−c/(2γ₁(γ₁ + 1 − 2s))`
    have hγ : (γ 1 : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    have hr : Tendsto (fun s : ℂ => -(c : ℂ) / (2 * γ 1 * ((γ 1 : ℂ) + 1 - 2 * s)))
        (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) (𝓝 (-(c : ℂ) / (2 * γ 1 * ((γ 1 : ℂ) + 1 - 2 * ((1 / 2 : ℝ) :
          ℂ))))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
      refine continuousAt_const.div ((continuousAt_const.mul continuousAt_const).mul
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))) ?_
      push_cast
      have : ((γ 1 : ℂ) + 1 - 2 * (1 / 2 : ℂ)) = γ 1 := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hγ) hγ
    refine (hr.isBigO_one (F := ℂ)).congr' ?_ (EventuallyEq.refl _ _)
    have hne1 : ∀ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), (γ 1 : ℂ) + 1 - 2 * s ≠ 0 := by
      refine nhdsWithin_le_nhds (ContinuousAt.eventually_ne ?_ ?_)
      · exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
      · push_cast
        have : ((γ 1 : ℂ) + 1 - 2 * (1 / 2 : ℂ)) = γ 1 := by ring
        rw [this]; exact hγ
    filter_upwards [hne0, hne1] with s hs hs1
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    rw [polarPart_monoA, monoTerm]
    simp only [monoA, h0, h1.ne', and_true, if_true, ne_eq, not_true_eq_false, and_false,
      if_false, zero_ne_one, not_false_eq_true]
    push_cast at hs' hs1 ⊢
    have e4 : (0 : ℂ) + 2 - 4 * s = -4 * (s - 1 / 2) := by ring
    rw [e4, zero_div, add_zero]
    have h4 : (-4 : ℂ) * (s - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) hs'
    have h2s : (-1 : ℂ) + s * 2 ≠ 0 := by intro h; apply hs'; linear_combination h / 2
    field_simp
    have hi := inv_mul_cancel₀ h2s
    linear_combination (4 * (c : ℂ)) * hi
  · -- `γ₀ ≥ 1`, `γ₁ = 0`: simple pole `−c/(2γ₀)`, bounded remainder `−2c/(γ₀(γ₀ + 2 − 4s))`
    have hγ : (γ 0 : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hr : Tendsto (fun s : ℂ => -2 * (c : ℂ) / (γ 0 * ((γ 0 : ℂ) + 2 - 4 * s)))
        (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) (𝓝 (-2 * (c : ℂ) / (γ 0 * ((γ 0 : ℂ) + 2 - 4 * ((1 / 2 : ℝ) :
          ℂ))))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
      refine continuousAt_const.div (continuousAt_const.mul
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))) ?_
      push_cast
      have : ((γ 0 : ℂ) + 2 - 4 * (1 / 2 : ℂ)) = γ 0 := by ring
      rw [this]
      exact mul_ne_zero hγ hγ
    refine (hr.isBigO_one (F := ℂ)).congr' ?_ (EventuallyEq.refl _ _)
    have hne1 : ∀ᶠ s in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), (γ 0 : ℂ) + 2 - 4 * s ≠ 0 := by
      refine nhdsWithin_le_nhds (ContinuousAt.eventually_ne ?_ ?_)
      · exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
      · push_cast
        have : ((γ 0 : ℂ) + 2 - 4 * (1 / 2 : ℂ)) = γ 0 := by ring
        rw [this]; exact hγ
    filter_upwards [hne0, hne1] with s hs hs1
    have hs' : s - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.2 hs
    rw [polarPart_monoA, monoTerm]
    simp only [monoA, h1, h0.ne', and_true, if_true, ne_eq, not_true_eq_false, and_false,
      if_false, zero_ne_one, not_false_eq_true]
    push_cast at hs' hs1 ⊢
    have e2 : (0 : ℂ) + 1 - 2 * s = -2 * (s - 1 / 2) := by ring
    rw [e2, zero_div, add_zero]
    have h2 : (-2 : ℂ) * (s - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) hs'
    have h2s : (-1 : ℂ) + s * 2 ≠ 0 := by intro h; apply hs'; linear_combination h / 2
    field_simp
    have hi := inv_mul_cancel₀ h2s
    linear_combination (2 * (c : ℂ)) * hi
  · -- both exponents positive: the term is holomorphic at `½`
    have hγ0 : (γ 0 : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hγ1 : (γ 1 : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    have hr : Tendsto (fun s : ℂ => (c : ℂ) * monoTerm γ s) (𝓝[≠] ((1 / 2 : ℝ) : ℂ))
        (𝓝 ((c : ℂ) * monoTerm γ ((1 / 2 : ℝ) : ℂ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto ?_)
      refine continuousAt_const.mul ?_
      unfold monoTerm
      refine continuousAt_const.div ((continuousAt_const.sub (continuousAt_const.mul
        continuousAt_id)).mul (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))) ?_
      push_cast
      have e0 : ((γ 0 : ℂ) + 2 - 4 * (1 / 2 : ℂ)) = γ 0 := by ring
      have e1 : ((γ 1 : ℂ) + 1 - 2 * (1 / 2 : ℂ)) = γ 1 := by ring
      rw [e0, e1]
      exact mul_ne_zero hγ0 hγ1
    refine (hr.isBigO_one (F := ℂ)).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with s
    rw [polarPart_monoA]
    simp [monoA, h0.ne', h1.ne']

/-- The tie polar data of a polynomial amplitude: the sum of the monomial data. -/
noncomputable def tieA (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) : ℕ → ℂ :=
  fun q => ∑ γ ∈ S, monoA γ (c γ) q

theorem polarPart_tieA (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (μ s : ℂ) :
    polarPart 1 (tieA S c) μ s = ∑ γ ∈ S, polarPart 1 (monoA γ (c γ)) μ s := by
  unfold polarPart tieA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_div]

theorem differentiableOn_polyTerms (S : Finset (Fin 2 → ℕ)) (c : (Fin 2 → ℕ) → ℝ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun s : ℂ => ∑ γ ∈ S, (c γ : ℂ) * monoTerm γ s)
      (U \ (S.image (fun γ => (((γ 0 : ℂ) + 2) / 4)) ∪
        S.image (fun γ => (((γ 1 : ℂ) + 1) / 2)) : Set ℂ)) := by
  have h : ∀ γ ∈ S, DifferentiableOn ℂ (fun s : ℂ => (c γ : ℂ) * monoTerm γ s)
      (U \ (S.image (fun γ => (((γ 0 : ℂ) + 2) / 4)) ∪
        S.image (fun γ => (((γ 1 : ℂ) + 1) / 2)) : Set ℂ)) := by
    intro γ hγ
    refine (differentiableOn_const _).mul ?_
    unfold monoTerm
    refine (differentiableOn_const _).div (((differentiableOn_const _).sub
      ((differentiableOn_const _).mul differentiableOn_id)).mul
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)))
      fun s hs => ?_
    refine mul_ne_zero ?_ ?_
    · intro h
      apply hs.2
      refine Or.inl ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨γ, hγ, by linear_combination h / 4⟩
    · intro h
      apply hs.2
      refine Or.inr ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨γ, hγ, by linear_combination h / 2⟩
  have hsum := DifferentiableOn.sum h
  refine hsum.congr fun s _ => ?_
  simp [Finset.sum_apply]

theorem tie_seed' (S : Finset (Fin 2 → ℕ)) : ((-1 / 2 : ℝ) : ℂ) ∉
    (S.image (fun γ => (((γ 0 : ℂ) + 2) / 4)) ∪ S.image (fun γ => (((γ 1 : ℂ) + 1) / 2)) : Set
      ℂ) := by
  simp only [Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe, not_or, not_exists,
    not_and]
  constructor
  · intro γ _ h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ γ 0 := Nat.cast_nonneg _
    linarith
  · intro γ _ h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ γ 1 := Nat.cast_nonneg _
    linarith

/-- ★★★ **The tie formula for polynomial amplitudes on the blow-up chart**: at `μ = ½`, the
polar coefficients of `η = Σ_γ c_γ u^γ` on the chart `h = (1,0)`, `k = (2,1)` are
`C_{½,2}[η] = c_{00}/8` and `C_{½,1}[η] = −Σ_{γ₀≥1} c_{γ₀0}/(2γ₀) − Σ_{γ₁≥1} c_{0γ₁}/(4γ₁)`. -/
theorem chartPolarCoeff_polyAmp_half (p : Fin 2 → ℕ) (hp0 : ∀ i, 0 < p i)
    (hμ : FlatStrip p tieH tieK ((1 / 2 : ℝ) : ℂ)) (S : Finset (Fin 2 → ℕ))
    (c : (Fin 2 → ℕ) → ℝ) :
    ∀ q ≤ 1, chartPolarCoeff p (polyAmp S c) tieH tieK (1 / 2) q = tieA S c q := by
  have hF := contDiff_polyAmp S c
  have hev := chartZetaAtDepth_eventuallyEq_of_eqOn_strip p hF tieH tieK tieK_pos hp0
    (Set.toFinite _) (differentiableOn_polyTerms S c _)
    (fun s hs _ => chartZeta_polyAmp S c hs) (tie_seed' S) hμ (by norm_num)
  have ha : (fun s => (∑ γ ∈ S, (c γ : ℂ) * monoTerm γ s) -
      polarPart 1 (tieA S c) ((1 / 2 : ℝ) : ℂ) s) =O[𝓝[≠] ((1 / 2 : ℝ) : ℂ)] fun _ => (1 : ℂ) := by
    have e : (fun s => (∑ γ ∈ S, (c γ : ℂ) * monoTerm γ s) -
        polarPart 1 (tieA S c) ((1 / 2 : ℝ) : ℂ) s) =
        ∑ γ ∈ S, fun s => (c γ : ℂ) * monoTerm γ s -
          polarPart 1 (monoA γ (c γ)) ((1 / 2 : ℝ) : ℂ) s := by
      funext s
      rw [polarPart_tieA, ← Finset.sum_sub_distrib]
      simp
    rw [e]
    exact IsBigO.sum fun γ _ => monoTerm_sub_polarPart_isBigO γ (c γ)
  exact chartPolarCoeff_eq_of_eventuallyEq p hF tieH tieK hp0 hμ
    (fun x _ => poleOrder_le _ _ x.1 x.2 _) hev ha

end Grammar
