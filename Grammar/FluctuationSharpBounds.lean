import Grammar.GaussianBound

/-!
# Sharp Gaussian bounds on the fluctuation function

`GaussianBound.lean` proves `S_λ(a) ≤ e^{βa²/2}(β/2)^{−λ}Γ(λ)` by completing the square at the
midpoint. This file records the two bounds that decide the `p`-moment thresholds of `S_λ(G)` for a
Gaussian `G`:

* **the `η`-family of upper bounds**: for `0 < η < 1`,
  `S_λ(a) ≤ Γ(λ)(βη)^{−λ} exp(β a₊²/(4(1−η)))` (`fluctuation_le_eta`), from the weighted AM–GM
  inequality `a√t ≤ (1−η)t + a₊²/(4(1−η))`; the Gaussian growth rate `βa²/4` is approached as
  `η → 0`;
* **the matching lower bound**: for `a ≥ 2`,
  `S_λ(a) ≥ e^{−β} 4^{−max(λ−1,0)} a^{2λ−1} e^{βa²/4}` (`le_fluctuation_of_two_le`), by restricting
  the integral to `t ∈ [a²/4, (a/2+1)²]`, where `√t − a/2 ∈ [0,1]` and the exponent is at least
  `βa²/4 − β`.

Consequently `S_λ(a) = e^{βa²/4 + O(log a)}` as `a → ∞`, and `S_λ(X)^p` for `X ~ N(0,v)` is
integrable when `pβv < 2` and has infinite positive expectation when `pβv > 2`
(`GaussianPMoment.lean`).
-/

open Real MeasureTheory Set

namespace Grammar

/-- Weighted AM–GM: `a√t ≤ εt + a₊²/(4ε)` for `ε > 0`, `t ≥ 0`. -/
theorem mul_sqrt_le_weighted (a t ε : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) :
    a * Real.sqrt t ≤ ε * t + max a 0 ^ 2 / (4 * ε) := by
  have hs := Real.sqrt_nonneg t
  have h1 : a * Real.sqrt t ≤ max a 0 * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  have h2 : 4 * ε * (max a 0 * Real.sqrt t) ≤ 4 * ε ^ 2 * t + max a 0 ^ 2 := by
    nlinarith [sq_nonneg (2 * ε * Real.sqrt t - max a 0), Real.sq_sqrt ht]
  have h3 : max a 0 * Real.sqrt t ≤ ε * t + max a 0 ^ 2 / (4 * ε) := by
    have := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 4 * ε)
    rw [mul_div_cancel_left₀ _ (by positivity)] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  exact h1.trans h3

/-- The `η`-domination of the fluctuation integrand: for `0 < η < 1`, `t ≥ 0`,
`e^{−βt + βa√t} ≤ e^{−βηt + βa₊²/(4(1−η))}`. -/
theorem fluctuation_integrand_le_eta (β a t η : ℝ) (hβ : 0 < β) (hη1 : η < 1) (ht : 0 ≤ t) :
    Real.exp (-β * t + β * a * Real.sqrt t) ≤
      Real.exp (-(β * η) * t + β * max a 0 ^ 2 / (4 * (1 - η))) := by
  apply Real.exp_le_exp.2
  have h := mul_sqrt_le_weighted a t (1 - η) (by linarith) ht
  have : β * a * Real.sqrt t ≤ β * ((1 - η) * t + max a 0 ^ 2 / (4 * (1 - η))) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h hβ.le
  have e : β * max a 0 ^ 2 / (4 * (1 - η)) = β * (max a 0 ^ 2 / (4 * (1 - η))) := by ring
  rw [e]
  nlinarith

/-- **The `η`-family of Gaussian upper bounds**: for `0 < η < 1`,
`S_λ(a) ≤ Γ(λ)(βη)^{−λ} exp(βa₊²/(4(1−η)))`. -/
theorem fluctuation_le_eta (β a lam η : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hη : 0 < η)
    (hη1 : η < 1) :
    fluctuation β lam a ≤
      Real.Gamma lam * (β * η) ^ (-lam) * Real.exp (β * max a 0 ^ 2 / (4 * (1 - η))) := by
  have hβη : 0 < β * η := mul_pos hβ hη
  set c : ℝ := Real.exp (β * max a 0 ^ 2 / (4 * (1 - η))) with hc
  have hmaj : IntegrableOn
      (fun t : ℝ => c * (t ^ (lam - 1) * Real.exp (-(β * η) * t ^ (1 : ℝ)))) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hβη).const_mul _
  have hval : (∫ t in Set.Ioi (0 : ℝ), c * (t ^ (lam - 1) * Real.exp (-(β * η) * t ^ (1 : ℝ))))
      = Real.Gamma lam * (β * η) ^ (-lam) * c := by
    rw [integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by linarith) hβη]
    simp only [div_one]
    rw [show lam - 1 + 1 = lam by ring]
    ring
  have hle : fluctuation β lam a
      ≤ ∫ t in Set.Ioi (0 : ℝ), c * (t ^ (lam - 1) * Real.exp (-(β * η) * t ^ (1 : ℝ))) := by
    rw [fluctuation]
    refine setIntegral_mono_on (fluctuation_integrableOn β lam hβ hlam a) hmaj measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htpow : (0 : ℝ) ≤ t ^ (lam - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.rpow_one]
    calc t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)
        ≤ t ^ (lam - 1) * Real.exp (-(β * η) * t + β * max a 0 ^ 2 / (4 * (1 - η))) :=
          mul_le_mul_of_nonneg_left (fluctuation_integrand_le_eta β a t η hβ hη1 ht0.le) htpow
      _ = c * (t ^ (lam - 1) * Real.exp (-(β * η) * t)) := by
          rw [hc, Real.exp_add]; ring
  exact hle.trans_eq hval

/-- **The matching lower bound**: for `a ≥ 2`,
`S_λ(a) ≥ e^{−β} 4^{−max(λ−1,0)} a^{2λ−1} e^{βa²/4}`. -/
theorem le_fluctuation_of_two_le (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) {a : ℝ} (ha : 2 ≤ a) :
    Real.exp (-β) * (4 : ℝ) ^ (-(max (lam - 1) 0)) * a ^ (2 * lam - 1) * Real.exp (β * a ^ 2 / 4) ≤
      fluctuation β lam a := by
  have ha0 : 0 < a := by linarith
  set l : ℝ := a ^ 2 / 4 with hl
  set r : ℝ := (a / 2 + 1) ^ 2 with hr
  have hl0 : 0 < l := by positivity
  have hlr : l ≤ r := by rw [hl, hr]; nlinarith
  have hIcc : Set.Icc l r ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le hl0 ht.1
  set f : ℝ → ℝ := fun t => t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) with hf
  have hfint : IntegrableOn f (Set.Ioi 0) := fluctuation_integrableOn β lam hβ hlam a
  have hf0 : ∀ t ∈ Set.Ioi (0 : ℝ), (0 : ℝ → ℝ) t ≤ f t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  have h1 : ∫ t in Set.Icc l r, f t ≤ fluctuation β lam a := by
    rw [fluctuation]
    exact setIntegral_mono_set hfint (ae_restrict_of_forall_mem measurableSet_Ioi hf0)
      (Filter.Eventually.of_forall hIcc)
  set m : ℝ := (4 : ℝ) ^ (-(max (lam - 1) 0)) * a ^ (2 * lam - 2) *
    (Real.exp (-β) * Real.exp (β * a ^ 2 / 4)) with hm
  have hm0 : 0 ≤ m := by positivity
  have hpt : ∀ t ∈ Set.Icc l r, m ≤ f t := by
    intro t ht
    have ht0 : 0 < t := hIcc ht
    have e1 : Real.sqrt l = a / 2 := by
      rw [hl, show a ^ 2 / 4 = (a / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    have e2 : Real.sqrt r = a / 2 + 1 := by rw [hr, Real.sqrt_sq (by linarith)]
    have hs1 : a / 2 ≤ Real.sqrt t := e1 ▸ Real.sqrt_le_sqrt ht.1
    have hs2 : Real.sqrt t ≤ a / 2 + 1 := e2 ▸ Real.sqrt_le_sqrt ht.2
    have hexp : -β + β * a ^ 2 / 4 ≤ -β * t + β * a * Real.sqrt t := by
      have hsq := Real.sq_sqrt ht0.le
      have hd : (Real.sqrt t - a / 2) ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hd hβ.le]
    have hpow : (4 : ℝ) ^ (-(max (lam - 1) 0)) * a ^ (2 * lam - 2) ≤ t ^ (lam - 1) := by
      have hsq2 : (a ^ 2 : ℝ) ^ (lam - 1) = a ^ (2 * lam - 2) := by
        rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha0.le]
        norm_num
        ring_nf
      rcases le_or_gt 1 lam with hl1 | hl1
      · rw [max_eq_left (by linarith)]
        calc (4 : ℝ) ^ (-(lam - 1)) * a ^ (2 * lam - 2) = (a ^ 2 / 4) ^ (lam - 1) := by
              rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num), hsq2]
              ring
          _ ≤ t ^ (lam - 1) := Real.rpow_le_rpow hl0.le ht.1 (by linarith)
      · rw [max_eq_right (by linarith), neg_zero, Real.rpow_zero, one_mul]
        have hra : r ≤ a ^ 2 := by rw [hr]; nlinarith
        calc a ^ (2 * lam - 2) = (a ^ 2) ^ (lam - 1) := hsq2.symm
          _ ≤ r ^ (lam - 1) := Real.rpow_le_rpow_of_nonpos (by positivity) hra (by linarith)
          _ ≤ t ^ (lam - 1) := Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by linarith)
    calc m = ((4 : ℝ) ^ (-(max (lam - 1) 0)) * a ^ (2 * lam - 2)) *
          Real.exp (-β + β * a ^ 2 / 4) := by rw [hm, Real.exp_add]
      _ ≤ t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) :=
          mul_le_mul hpow (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le
            (Real.rpow_nonneg ht0.le _)
  have h2 : m * (r - l) ≤ ∫ t in Set.Icc l r, f t := by
    have := setIntegral_ge_of_const_le measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hpt (hfint.mono_set hIcc)
    rwa [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
      mul_comm] at this
  have hrl : r - l = a + 1 := by rw [hr, hl]; ring
  have hapow : a ^ (2 * lam - 1) = a ^ (2 * lam - 2) * a := by
    rw [← Real.rpow_add_one ha0.ne']
    ring_nf
  calc Real.exp (-β) * (4 : ℝ) ^ (-(max (lam - 1) 0)) * a ^ (2 * lam - 1) *
        Real.exp (β * a ^ 2 / 4) = m * a := by rw [hapow, hm]; ring
    _ ≤ m * (a + 1) := mul_le_mul_of_nonneg_left (by linarith) hm0
    _ = m * (r - l) := by rw [hrl]
    _ ≤ ∫ t in Set.Icc l r, f t := h2
    _ ≤ fluctuation β lam a := h1

end Grammar
