/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.MellinPowerLog
import Grammar.AbstractExpansion
import Grammar.StochasticTaylorTreeJoint

/-!
# The regularised Mellin transform of a cutoff expansion (§20, the fluctuation zeta function)

For `E : ℝ → ℝ` with a cutoff expansion `E(N) = Σ_{μ<U} Σ_{q≤D} c_{μ,q} N^{−μ} (log N)^q +
O(N^{−U}(1+log N)^D)` on the lattice `Q⁻¹ℕ`, subtract the principal polynomial on `[1,∞)`:
`R_U(N) = E(N) − 𝟙_{[1,∞)}(N) Σ_{μ<U} Σ_q c_{μ,q} N^{−μ} (log N)^q`.  Then

* `mellinConvergent_cutoffRemainderFun`, `differentiableAt_mellin_cutoffRemainderFun`: the Mellin
  transform of `R_U` converges and is complex-differentiable on the strip `0 < Re s < U`;
* `mellin_eq_mellin_cutoffRemainderFun_add_principalParts`: on the initial strip `0 < Re s < a`
  (where `E = O(N^{−a})` and every retained exponent is `≥ a`),
  `mellin E s = mellin R_U s + Σ_{μ<U} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`;
* `mellin_cutoffRemainderFun_compat`: for `U ≤ V`,
  `mellin R_U s = mellin R_V s + Σ_{U≤μ<V} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}` on `0 < Re s < U`,
  so `F_U := mellin R_U + principalParts U` is a coherent continuation to `Re s < U` for every `U`.

This states the meromorphic continuation of the Mellin transform with prescribed principal
parts — the coefficients of `N^{−μ}(log N)^q` are `(−1)^{q+1}/q!` times the Laurent coefficients
of `(s−μ)^{−(q+1)}` — without a meromorphic-function API (consult #158, item 1).

Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics Real

namespace Grammar

variable {Q D : ℕ} {E : ℝ → ℝ} {c : ℝ → ℕ → ℝ}

/-- The principal parts `Σ_{μ<U} Σ_{q≤D} c_{μ,q} · q!/(μ − s)^{q+1}`. -/
noncomputable def principalParts (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
    (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))

/-- The regularised function `E − 𝟙_{[1,∞)} P_U`, complexified. -/
noncomputable def cutoffRemainderFun (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) (N : ℝ) :
    ℂ :=
  (E N : ℂ) - ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N

/-- The principal polynomial on `[1,∞)` is the spectral sum. -/
theorem sum_powLogIci_eq_absSpectralSum (Q D : ℕ) (c : ℝ → ℕ → ℝ) (U : ℝ) {N : ℝ} (hN : 1 ≤ N) :
    ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N =
      ((absSpectralSum Q D c U N : ℝ) : ℂ) := by
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  unfold absSpectralSum
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold powLogIci
  rw [indicator_of_mem (show N ∈ Ici (1 : ℝ) from hN), Complex.ofReal_cpow hN0 (-μ),
    Complex.ofReal_neg]
  ring

theorem cutoffRemainderFun_eq_of_le (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) {N : ℝ}
    (hN : 1 ≤ N) :
    cutoffRemainderFun Q D E c U N = ((E N - absSpectralSum Q D c U N : ℝ) : ℂ) := by
  unfold cutoffRemainderFun
  rw [sum_powLogIci_eq_absSpectralSum Q D c U hN]
  push_cast
  ring

theorem cutoffRemainderFun_eq_of_lt (Q D : ℕ) (E : ℝ → ℝ) (c : ℝ → ℕ → ℝ) (U : ℝ) {N : ℝ}
    (hN : N < 1) : cutoffRemainderFun Q D E c U N = (E N : ℂ) := by
  unfold cutoffRemainderFun powLogIci
  have hnot : N ∉ Ici (1 : ℝ) := not_le.2 hN
  simp [indicator_of_notMem hnot]

/-- `N^{−U} (1 + log N)^D = O(N^{−a})` for every `a < U`. -/
theorem isBigO_rpow_neg_mul_one_add_log_pow {U a : ℝ} (ha : a < U) (D : ℕ) :
    (fun N : ℝ => N ^ (-U) * (1 + Real.log N) ^ D) =O[atTop] fun N : ℝ => N ^ (-a) := by
  set δ : ℝ := (U - a) / (D + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hlog := (isLittleO_log_rpow_atTop hδ0).bound one_pos
  refine IsBigO.of_bound (2 ^ D) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog] with N hN hl
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hl
  rw [abs_of_nonneg (Real.rpow_nonneg hN0.le _)] at hl
  have h1 : 1 ≤ N ^ δ := Real.one_le_rpow hN hδ0.le
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have h2 : 1 + Real.log N ≤ 2 * N ^ δ := by
    have := (le_abs_self (Real.log N)).trans hl
    linarith
  have h3 : (1 + Real.log N) ^ D ≤ (2 * N ^ δ) ^ D := pow_le_pow_left₀ (by linarith) h2 D
  have h4 : (N ^ δ) ^ D = N ^ (δ * D) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  have h5 : N ^ (δ * D) ≤ N ^ (U - a) := by
    refine Real.rpow_le_rpow_of_exponent_le hN ?_
    rw [hδ]
    have : (D : ℝ) / (D + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc (U - a) / (D + 1) * D = (U - a) * (D / (D + 1)) := by ring
      _ ≤ (U - a) * 1 := mul_le_mul_of_nonneg_left this (by linarith)
      _ = U - a := mul_one _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0.le _),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (pow_nonneg (by linarith) D))]
  calc N ^ (-U) * (1 + Real.log N) ^ D ≤ N ^ (-U) * (2 * N ^ δ) ^ D :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hN0.le _)
    _ = 2 ^ D * (N ^ (-U) * N ^ (δ * D)) := by rw [mul_pow, h4]; ring
    _ ≤ 2 ^ D * (N ^ (-U) * N ^ (U - a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hN0.le _))
          (by positivity)
    _ = 2 ^ D * N ^ (-a) := by rw [← Real.rpow_add hN0]; congr 2; ring

theorem cutoffRemainderFun_isBigO_atTop (hexp : CutoffExpansion Q D E c) {U : ℝ} (hU : 0 < U)
    {a : ℝ} (ha : a < U) :
    cutoffRemainderFun Q D E c U =O[atTop] fun N : ℝ => N ^ (-a) := by
  obtain ⟨K, hK⟩ := hexp U hU
  have h1 : cutoffRemainderFun Q D E c U =O[atTop]
      fun N : ℝ => N ^ (-U) * (1 + Real.log N) ^ D := by
    refine IsBigO.of_bound K ?_
    filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with N hN hN1
    rw [cutoffRemainderFun_eq_of_le Q D E c U hN1, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hN1) _)
        (pow_nonneg (by linarith [Real.log_nonneg hN1]) D))]
    exact hN
  exact h1.trans (isBigO_rpow_neg_mul_one_add_log_pow ha D)

theorem cutoffRemainderFun_isBigO_zero (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ))
    (U : ℝ) : cutoffRemainderFun Q D E c U =O[𝓝[>] 0] fun N : ℝ => N ^ (-(0 : ℝ)) := by
  have h : cutoffRemainderFun Q D E c U =ᶠ[𝓝[>] 0] fun N => (E N : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with N hN
    exact cutoffRemainderFun_eq_of_lt Q D E c U hN.2
  refine (hE0.congr' h.symm (Eventually.of_forall fun _ => rfl)).trans ?_
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with N hN
  simp [Real.rpow_zero]

theorem locallyIntegrableOn_cutoffRemainderFun
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0)) (U : ℝ) :
    LocallyIntegrableOn (cutoffRemainderFun Q D E c U) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed] at hE ⊢
  intro K hK hKc
  unfold cutoffRemainderFun
  refine (hE K hK hKc).sub (integrable_finsetSum _ fun μ _ => integrable_finsetSum _ fun q _ =>
    ?_)
  have := (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).1 (locallyIntegrableOn_powLogIci μ q)
    K hK hKc
  exact this.const_mul _

/-- ★ The Mellin transform of the regularised function converges on the strip `0 < Re s < U`. -/
theorem mellinConvergent_cutoffRemainderFun (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hsU : s.re < U) : MellinConvergent (cutoffRemainderFun Q D E c U) s :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_cutoffRemainderFun hE U)
    (cutoffRemainderFun_isBigO_atTop hexp (hs0.trans hsU) (a := (s.re + U) / 2) (by linarith))
    (by linarith) (cutoffRemainderFun_isBigO_zero hE0 U) (by simpa using hs0)

/-- ★★ **Complex differentiability of the regularised Mellin transform on the strip
`0 < Re s < U`.** -/
theorem differentiableAt_mellin_cutoffRemainderFun (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U : ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hsU : s.re < U) :
    DifferentiableAt ℂ (mellin (cutoffRemainderFun Q D E c U)) s :=
  mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_cutoffRemainderFun hE U)
    (cutoffRemainderFun_isBigO_atTop hexp (hs0.trans hsU) (a := (s.re + U) / 2) (by linarith))
    (by linarith) (cutoffRemainderFun_isBigO_zero hE0 U) (by simpa using hs0)

/-- The Mellin transform of one principal term, allowing a vanishing coefficient. -/
theorem hasMellin_const_mul_powLogIci (μ : ℝ) (q : ℕ) (a : ℝ) {s : ℂ}
    (h : a ≠ 0 → s.re < μ) :
    HasMellin (fun N => (a : ℂ) * powLogIci μ q N) s
      ((a : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))) := by
  by_cases ha : a = 0
  · subst ha
    refine ⟨?_, ?_⟩
    · simp [MellinConvergent]
    · simp [mellin]
  · have hm := hasMellin_powLogIci μ q (h ha)
    have := hasMellin_const_smul hm.1 (a : ℂ)
    rw [hm.2] at this
    simpa only [smul_eq_mul] using this

theorem hasMellin_finset_sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℂ} {m : ι → ℂ} {s : ℂ}
    (h : ∀ i ∈ S, HasMellin (f i) s (m i)) :
    HasMellin (fun N => ∑ i ∈ S, f i N) s (∑ i ∈ S, m i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp [MellinConvergent]
    · simp [mellin]
  | insert a S ha ih =>
    have hS := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hA := h a (Finset.mem_insert_self a S)
    simp only [Finset.sum_insert ha]
    have := hasMellin_add hA.1 hS.1
    rw [hA.2, hS.2] at this
    exact this

/-- The Mellin transform of the principal polynomial on the strip below every retained exponent.
-/
theorem hasMellin_principalPolynomial (U : ℝ) {s : ℂ}
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → s.re < μ) :
    HasMellin (fun N => ∑ μ ∈ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
      (c μ q : ℂ) * powLogIci μ q N) s (principalParts Q D c U s) := by
  unfold principalParts
  refine hasMellin_finset_sum _ fun μ hμ => ?_
  refine hasMellin_finset_sum _ fun q hq => ?_
  exact hasMellin_const_mul_powLogIci μ q (c μ q) (hlow μ hμ q hq)

/-- ★★ **The Mellin transform of `E` with its principal parts on the initial strip**: for
`0 < Re s < a`, where `E = O(N^{−a})` at infinity and every retained exponent with a nonzero
coefficient is `≥ a`,
`mellin E s = mellin R_U s + Σ_{μ<U} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`. -/
theorem mellin_eq_mellin_cutoffRemainderFun_add_principalParts (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U a : ℝ} (haU : a ≤ U)
    (hlow : ∀ μ ∈ latticeBelow Q U, ∀ q ∈ Finset.range (D + 1), c μ q ≠ 0 → a ≤ μ) {s : ℂ}
    (hs0 : 0 < s.re) (hsa : s.re < a) :
    mellin (fun N => (E N : ℂ)) s =
      mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s := by
  have hR := mellinConvergent_cutoffRemainderFun hexp hE hE0 hs0 (hsa.trans_le haU)
  have hP := hasMellin_principalPolynomial (Q := Q) (D := D) (c := c) U
    fun μ hμ q hq hc => hsa.trans_le (hlow μ hμ q hq hc)
  have hsum := hasMellin_add hR hP.1
  rw [hP.2] at hsum
  have hfun : (fun N => cutoffRemainderFun Q D E c U N + ∑ μ ∈ latticeBelow Q U,
      ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N) = fun N => (E N : ℂ) := by
    funext N
    unfold cutoffRemainderFun
    ring
  rw [hfun] at hsum
  exact hsum.2

/-- ★★ **Cutoff compatibility**: for `U ≤ V` and `0 < Re s < U`,
`mellin R_U s = mellin R_V s + Σ_{U ≤ μ < V} Σ_q c_{μ,q} · q!/(μ − s)^{q+1}`; hence
`mellin R_U + principalParts U = mellin R_V + principalParts V` there. -/
theorem mellin_cutoffRemainderFun_compat (hQ : 0 < Q) (hexp : CutoffExpansion Q D E c)
    (hE : LocallyIntegrableOn (fun N => (E N : ℂ)) (Ioi 0))
    (hE0 : (fun N => (E N : ℂ)) =O[𝓝[>] 0] fun _ : ℝ => (1 : ℂ)) {U V : ℝ} (hUV : U ≤ V) {s : ℂ}
    (hs0 : 0 < s.re) (hsU : s.re < U) :
    mellin (cutoffRemainderFun Q D E c U) s + principalParts Q D c U s =
      mellin (cutoffRemainderFun Q D E c V) s + principalParts Q D c V s := by
  have hsub : latticeBelow Q U ⊆ latticeBelow Q V := fun μ hμ =>
    (mem_latticeBelow_iff hQ).2 ⟨((mem_latticeBelow_iff hQ).1 hμ).1,
      lt_of_lt_of_le ((mem_latticeBelow_iff hQ).1 hμ).2 hUV⟩
  have hRV := mellinConvergent_cutoffRemainderFun hexp hE hE0 hs0 (hsU.trans_le hUV)
  -- the transform of the terms with `U ≤ μ < V`
  have hP : HasMellin (fun N => ∑ μ ∈ latticeBelow Q V \ latticeBelow Q U,
      ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N) s
      (∑ μ ∈ latticeBelow Q V \ latticeBelow Q U, ∑ q ∈ Finset.range (D + 1),
        (c μ q : ℂ) * ((q.factorial : ℂ) / ((μ : ℂ) - s) ^ (q + 1))) := by
    refine hasMellin_finset_sum _ fun μ hμ => hasMellin_finset_sum _ fun q _ =>
      hasMellin_const_mul_powLogIci μ q (c μ q) fun _ => ?_
    rw [Finset.mem_sdiff] at hμ
    have h1 := (mem_latticeBelow_iff hQ).1 hμ.1
    have h2 : ¬ μ < U := fun hlt => hμ.2 ((mem_latticeBelow_iff hQ).2 ⟨h1.1, hlt⟩)
    linarith [not_lt.1 h2]
  have hsum := hasMellin_add hRV hP.1
  rw [hP.2] at hsum
  have hfun : (fun N => cutoffRemainderFun Q D E c V N + ∑ μ ∈ latticeBelow Q V \ latticeBelow Q U,
      ∑ q ∈ Finset.range (D + 1), (c μ q : ℂ) * powLogIci μ q N) =
      cutoffRemainderFun Q D E c U := by
    funext N
    unfold cutoffRemainderFun
    rw [← Finset.sum_sdiff hsub]
    ring
  rw [hfun] at hsum
  rw [hsum.2]
  unfold principalParts
  rw [← Finset.sum_sdiff hsub]
  ring

end Grammar
