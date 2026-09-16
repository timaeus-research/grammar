/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.MellinRegularization

/-!
# Uniqueness of bounded principal parts and the polar coefficients of a cutoff expansion

`polarPart D a μ s = Σ_{q≤D} a_q/(s−μ)^{q+1}`.  If the difference of two polar parts is bounded
on a punctured neighbourhood of `μ` then the coefficients agree
(`polarPart_eq_of_sub_isBigO_one`; descending induction on the pole order: multiply by
`(s−μ)^{D+1}`, the product tends to `a_D − b_D` and to `0`).

Applied to the continuation expression `F_U = mellin R_U + principalParts U` of a cutoff
expansion (`MellinRegularization`): at a retained exponent `0 < μ₀ < U`,
`F_U − polarPart D (polarCoeff c μ₀) μ₀` is bounded near `μ₀`
(`mellinContinuation_sub_polarPart_isBigO_one`) with `polarCoeff c μ₀ q = (−1)^{q+1} q! c_{μ₀,q}`,
and ANY polar part with this property has these coefficients (`polarCoeff_unique`).  So the
coefficients `c_{μ₀,q}` of `N^{−μ₀}(log N)^q` are the unique local principal-part data of the
continued Mellin transform at `μ₀`: `c_{μ₀,q} = (−1)^{q+1}/q! · a_q` (`ofReal_coeff_eq_polarCoeff`)
— the intrinsic characterisation of every log order (consult #159, C1–C2), without a
Laurent-series API.

Zero `sorry`/`axiom`.
-/

open Filter Topology Asymptotics Set MeasureTheory

namespace Grammar

/-- The polar part `Σ_{q≤D} a_q/(s−μ)^{q+1}`. -/
noncomputable def polarPart (D : ℕ) (a : ℕ → ℂ) (μ s : ℂ) : ℂ :=
  ∑ q ∈ Finset.range (D + 1), a q / (s - μ) ^ (q + 1)

theorem polarPart_sub (D : ℕ) (a b : ℕ → ℂ) (μ s : ℂ) :
    polarPart D a μ s - polarPart D b μ s = polarPart D (a - b) μ s := by
  unfold polarPart
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.sub_apply, sub_div]

theorem polarPart_succ_of_eq_zero (D : ℕ) (a : ℕ → ℂ) (μ s : ℂ) (h : a (D + 1) = 0) :
    polarPart (D + 1) a μ s = polarPart D a μ s := by
  unfold polarPart
  rw [Finset.sum_range_succ, h, zero_div, add_zero]

/-- `(s−μ)^{D+1} · polarPart D a μ s → a_D` as `s → μ`, `s ≠ μ`. -/
theorem tendsto_pow_mul_polarPart (D : ℕ) (a : ℕ → ℂ) (μ : ℂ) :
    Tendsto (fun s => (s - μ) ^ (D + 1) * polarPart D a μ s) (𝓝[≠] μ) (𝓝 (a D)) := by
  have hterm : ∀ q ∈ Finset.range (D + 1),
      Tendsto (fun s => (s - μ) ^ (D + 1) * (a q / (s - μ) ^ (q + 1))) (𝓝[≠] μ)
        (𝓝 (if q = D then a q else 0)) := by
    intro q hq
    have hqD : q ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have heq : EqOn (fun s : ℂ => a q * (s - μ) ^ (D - q))
        (fun s => (s - μ) ^ (D + 1) * (a q / (s - μ) ^ (q + 1))) {μ}ᶜ := by
      intro s hs
      have hs' : s - μ ≠ 0 := sub_ne_zero.2 hs
      have hpow : (s - μ) ^ (D + 1) = (s - μ) ^ (D - q) * (s - μ) ^ (q + 1) := by
        rw [← pow_add]
        congr 1
        omega
      simp only
      rw [hpow, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hs'), mul_comm]
    have hlim : Tendsto (fun s : ℂ => a q * (s - μ) ^ (D - q)) (𝓝 μ)
        (𝓝 (a q * (μ - μ) ^ (D - q))) :=
      ((tendsto_id.sub_const μ).pow (D - q)).const_mul (a q)
    rw [sub_self] at hlim
    refine (tendsto_nhdsWithin_of_tendsto_nhds ?_).congr' (eventuallyEq_nhdsWithin_of_eqOn heq)
    by_cases hqD' : q = D
    · subst hqD'
      simp
    · have hne : D - q ≠ 0 := by omega
      rw [if_neg hqD']
      simpa [zero_pow hne] using hlim
  have hsum := tendsto_finsetSum (Finset.range (D + 1)) hterm
  rw [Finset.sum_ite_eq' (Finset.range (D + 1)) D a,
    if_pos (Finset.mem_range.2 (Nat.lt_succ_self D))] at hsum
  refine hsum.congr fun s => ?_
  unfold polarPart
  rw [Finset.mul_sum]

/-- The top coefficient of a bounded polar part vanishes. -/
theorem polarPart_top_eq_zero_of_isBigO_one {D : ℕ} {a : ℕ → ℂ} {μ : ℂ}
    (h : (fun s => polarPart D a μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ)) : a D = 0 := by
  have hpow : Tendsto (fun s : ℂ => (s - μ) ^ (D + 1)) (𝓝[≠] μ) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℂ => (s - μ) ^ (D + 1)) (𝓝 μ) (𝓝 ((μ - μ) ^ (D + 1))) :=
      (tendsto_id.sub_const μ).pow (D + 1)
    rw [sub_self, zero_pow (Nat.succ_ne_zero D)] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  have h2 : (fun s => (s - μ) ^ (D + 1) * polarPart D a μ s) =O[𝓝[≠] μ]
      fun s => (s - μ) ^ (D + 1) * (1 : ℂ) := (isBigO_refl _ _).mul h
  simp only [mul_one] at h2
  exact tendsto_nhds_unique (tendsto_pow_mul_polarPart D a μ) (h2.trans_tendsto hpow)

/-- ★ **A bounded polar part has vanishing coefficients.** -/
theorem polarPart_coeff_eq_zero_of_isBigO_one {D : ℕ} {a : ℕ → ℂ} {μ : ℂ}
    (h : (fun s => polarPart D a μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ)) : ∀ q ≤ D, a q = 0 := by
  induction D generalizing a with
  | zero =>
    intro q hq
    rw [Nat.le_zero.1 hq]
    exact polarPart_top_eq_zero_of_isBigO_one h
  | succ D ih =>
    have htop : a (D + 1) = 0 := polarPart_top_eq_zero_of_isBigO_one h
    have h' : (fun s => polarPart D a μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ) :=
      h.congr_left fun s => polarPart_succ_of_eq_zero D a μ s htop
    intro q hq
    rcases Nat.lt_or_ge q (D + 1) with hlt | hge
    · exact ih h' q (Nat.lt_succ_iff.1 hlt)
    · rw [le_antisymm hq hge]
      exact htop

/-- ★★ **Uniqueness of bounded principal parts**: if `polarPart a − polarPart b` is bounded on a
punctured neighbourhood of `μ`, the coefficients agree. -/
theorem polarPart_eq_of_sub_isBigO_one {D : ℕ} {a b : ℕ → ℂ} {μ : ℂ}
    (h : (fun s => polarPart D a μ s - polarPart D b μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = b q := by
  have h' : (fun s => polarPart D (a - b) μ s) =O[𝓝[≠] μ] fun _ => (1 : ℂ) :=
    h.congr_left fun s => polarPart_sub D a b μ s
  intro q hq
  have := polarPart_coeff_eq_zero_of_isBigO_one h' q hq
  rwa [Pi.sub_apply, sub_eq_zero] at this

/-! ### The polar coefficients of a cutoff expansion -/

variable {Q D : ℕ} {E : ℝ → ℝ} {c : ℝ → ℕ → ℝ}

/-- The continuation expression `F_U = mellin R_U + principalParts U` (`MellinRegularization`). -/
noncomputable def mellinContinuation (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) :
    ℂ :=
  mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s

/-- The polar coefficients at `μ₀` in the standard `(s−μ₀)^{−(q+1)}` convention:
`a_q = (−1)^{q+1} q! c_{μ₀,q}`. -/
noncomputable def polarCoeff (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) : ℂ :=
  (-1) ^ (q + 1) * (q.factorial : ℂ) * (c μ₀ q : ℂ)

/-- `c_{μ₀,q} = (−1)^{q+1}/q! · a_q`. -/
theorem ofReal_coeff_eq_polarCoeff (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) (q : ℕ) :
    (c μ₀ q : ℂ) = (-1) ^ (q + 1) * polarCoeff c μ₀ q / (q.factorial : ℂ) := by
  unfold polarCoeff
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hneg : ((-1 : ℂ) ^ (q + 1)) * (-1) ^ (q + 1) = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨q + 1, rfl⟩]
  rw [eq_div_iff hq]
  linear_combination (-(q.factorial : ℂ) * (c μ₀ q : ℂ)) * hneg

/-- One principal term in the polar convention. -/
theorem principalTerm_eq_polar (μ₀ : ℝ) (q : ℕ) (x : ℝ) {s : ℂ} (hs : s ≠ μ₀) :
    (x : ℂ) * ((q.factorial : ℂ) / ((μ₀ : ℂ) - s) ^ (q + 1)) =
      ((-1) ^ (q + 1) * (q.factorial : ℂ) * (x : ℂ)) / (s - μ₀) ^ (q + 1) := by
  have hY : (s - μ₀) ^ (q + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hs)
  have hN : (-1 : ℂ) ^ (q + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have hneg : ((-1 : ℂ) ^ (q + 1)) * (-1) ^ (q + 1) = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨q + 1, rfl⟩]
  have key : (q.factorial : ℂ) / ((-1) ^ (q + 1) * (s - μ₀) ^ (q + 1)) =
      (-1) ^ (q + 1) * (q.factorial : ℂ) / (s - μ₀) ^ (q + 1) := by
    rw [div_eq_div_iff (mul_ne_zero hN hY) hY]
    linear_combination (-(q.factorial : ℂ) * (s - μ₀) ^ (q + 1)) * hneg
  rw [show (μ₀ : ℂ) - s = -(s - μ₀) by ring, neg_pow, key]
  ring

/-- The principal terms at `μ₀` are the polar part with coefficients `polarCoeff c μ₀`. -/
theorem sum_principalTerm_eq_polarPart (c : ℝ → ℕ → ℝ) (μ₀ : ℝ) {s : ℂ} (hs : s ≠ μ₀) :
    ∑ q ∈ Finset.range (D + 1), (c μ₀ q : ℂ) * ((q.factorial : ℂ) / ((μ₀ : ℂ) - s) ^ (q + 1)) =
      polarPart D (polarCoeff c μ₀) (μ₀ : ℂ) s := by
  unfold polarPart polarCoeff
  exact Finset.sum_congr rfl fun q _ => principalTerm_eq_polar μ₀ q (c μ₀ q) hs

/-- The principal terms at the other retained exponents are continuous at `μ₀`. -/
theorem tendsto_principalParts_erase (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) (μ₀ : ℝ) :
    Tendsto (fun s => ∑ μ ∈ (latticeBelow Q U).erase μ₀, ∑ q ∈ Finset.range (D + 1),
      (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))) (𝓝 (μ₀ : ℂ))
      (𝓝 (∑ μ ∈ (latticeBelow Q U).erase μ₀, ∑ q ∈ Finset.range (D + 1),
      (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - μ₀) ^ (q + 1)))) := by
  refine tendsto_finsetSum _ fun μ hμ => tendsto_finsetSum _ fun q _ => ?_
  have hne : (μ : ℂ) - μ₀ ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast Finset.ne_of_mem_erase hμ
  exact ((tendsto_const_nhds.sub tendsto_id).pow (q + 1)).inv₀ (pow_ne_zero _ hne)
    |>.const_mul _ |>.const_mul _ |>.congr fun s => by rw [div_eq_mul_inv]; rfl

/-- ★★ **The continuation expression minus the polar part at a retained exponent is bounded
near it**: for `μ₀ ∈ latticeBelow Q U`, `0 < μ₀`,
`F_U − Σ_q (−1)^{q+1} q! c_{μ₀,q}/(s−μ₀)^{q+1} = O(1)` on a punctured neighbourhood of `μ₀`. -/
theorem mellinContinuation_sub_polarPart_isBigO_one (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) :
    (fun s => mellinContinuation Q D E c U s - polarPart D (polarCoeff c μ₀) (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ) := by
  have hR : Tendsto (mellin (cutoffRemainderFun Q D E c U)) (𝓝 (μ₀ : ℂ))
      (𝓝 (mellin (cutoffRemainderFun Q D E c U) μ₀)) :=
    (differentiableAt_mellin_cutoffRemainderFun hexp hE hE0 (by simpa using hpos)
      (by simpa using hμU)).continuousAt
  have hT := hR.add (tendsto_principalParts_erase Q D c U μ₀)
  have hbdd := (tendsto_nhdsWithin_of_tendsto_nhds (s := {(μ₀ : ℂ)}ᶜ) hT).isBigO_one ℂ
  refine hbdd.congr' (eventuallyEq_nhdsWithin_of_eqOn fun s hs => ?_) EventuallyEq.rfl
  have hs' : s ≠ (μ₀ : ℂ) := hs
  unfold mellinContinuation principalParts
  rw [← Finset.add_sum_erase _ _ hμ₀, sum_principalTerm_eq_polarPart c μ₀ hs']
  ring

/-- ★★★ **Uniqueness of the polar coefficients of a cutoff expansion**: any polar part `a` at a
retained exponent `0 < μ₀ < U` with `F_U − polarPart D a μ₀ = O(1)` near `μ₀` has
`a_q = (−1)^{q+1} q! c_{μ₀,q}` — the coefficients of `N^{−μ₀}(log N)^q` are the unique local
principal-part data of the continued Mellin transform. -/
theorem polarCoeff_unique (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ latticeBelow Q U) (hμU : μ₀ < U) (hpos : 0 < μ₀) {a : ℕ → ℂ}
    (ha : (fun s => mellinContinuation Q D E c U s - polarPart D a (μ₀ : ℂ) s)
      =O[𝓝[≠] (μ₀ : ℂ)] fun _ => (1 : ℂ)) :
    ∀ q ≤ D, a q = polarCoeff c μ₀ q := by
  have h := (mellinContinuation_sub_polarPart_isBigO_one hexp hE hE0 hμ₀ hμU hpos).sub ha
  refine polarPart_eq_of_sub_isBigO_one (h.congr_left fun s => ?_)
  ring

end Grammar
