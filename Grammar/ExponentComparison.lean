import Grammar.ScaledAssembly
import Grammar.HironakaAdapter

/-!
# Conditional identification of the exponent pair with the population Laplace order

Two descriptions of the **same** population integral `Z^pop(N) = ∫ e^{−NK} dμ` fix its exponent
pair: if the certified core theorem gives `A_n Z^pop(n) → L₀ > 0` with `A_n = n^λ/(log n)^{m−1}`
along the integers, and hironaka's theorem gives `Z^pop(N) ≍ N^{−λ_H}(log N)^{θ_H−1}`
(`LaplaceTheta`), then `λ = λ_H` and `m − 1 = θ_H − 1`. The ingredient is the uniqueness of
power–log orders along the integers (`powerLogRate_pair_eq_of_isTheta_nat`): if
`n^{−λ}(log n)^q ≍ n^{−λ'}(log n)^{q'}` then `λ = λ'` (else the ratio `n^{|λ−λ'|}(log n)^{…}`
is unbounded, since `(log n)^{q'} = o(n^s)`) and then `q = q'` (else `(log n)^{|q−q'|}` is
unbounded).

Consequences: `exponentPair_eq_of_population_comparison`; with hironaka's `Q n` explicit,
`exists_exponentPair_of_Q` — the exponent pair of every certified population core theorem on a
small closed cube is hironaka's pair; and the empirical exponent statement of CXLVIII transports:
`log Z_n^{emp}/log n → −λ_H` in probability
(`tendstoInMeasure_log_div_log_of_population_comparison`).

Non-claims: the two exponent theorems must describe the same integral — nothing here identifies
the empirical presentation with the population one, constructs a certified presentation, or
removes analytic units; the logarithmic empirical conclusion identifies `λ` only, `m` comes from
the deterministic comparison.
-/

open Filter Topology Asymptotics MeasureTheory

namespace Grammar

/-! ### Uniqueness of power–log orders along the integers -/

theorem powerLogRate_pos_nat {lam : ℝ} {q : ℕ} {n : ℕ} (hn : 2 ≤ n) :
    0 < powerLogRate lam q n :=
  powerLogRate_pos (by exact_mod_cast (by omega : 1 < n))

/-- An `O`-comparison of power–log rates along the integers, with the norms removed. -/
theorem exists_eventually_le_of_isBigO_powerLogRate {lam lam' : ℝ} {q q' : ℕ}
    (h : (fun n : ℕ => powerLogRate lam q n) =O[atTop] fun n : ℕ => powerLogRate lam' q' n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, powerLogRate lam q n ≤ C * powerLogRate lam' q' n := by
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 2] with n hn hn2
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [Real.norm_of_nonneg (powerLogRate_nonneg h1), Real.norm_of_nonneg (powerLogRate_nonneg h1)]
    at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (powerLogRate_nonneg h1))

/-- `n^{−λ}(log n)^q = O(n^{−λ'}(log n)^{q'})` along the integers forces `λ' ≤ λ`. -/
theorem le_of_isBigO_powerLogRate {lam lam' : ℝ} {q q' : ℕ}
    (h : (fun n : ℕ => powerLogRate lam q n) =O[atTop] fun n : ℕ => powerLogRate lam' q' n) :
    lam' ≤ lam := by
  by_contra hlt
  have hs : 0 < lam' - lam := by linarith [not_le.1 hlt]
  obtain ⟨C, hC0, hC⟩ := exists_eventually_le_of_isBigO_powerLogRate h
  set c : ℝ := 1 / (2 * (C + 1)) with hc
  have hc0 : 0 < c := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (q' : ℝ) hs).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := ho.bound hc0
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hC, hb, eventually_ge_atTop 3] with n hn hbn hn3
    simp only [Function.comp_apply] at hbn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 1 ≤ Real.log n := one_le_log_nat hn3
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _), Real.rpow_natCast] at hbn
    set A : ℝ := (n : ℝ) ^ (-lam) with hA
    have hApos : 0 < A := Real.rpow_pos_of_pos hn0 _
    have e1 : (n : ℝ) ^ (-lam') * (n : ℝ) ^ (lam' - lam) = A := by
      rw [hA, ← Real.rpow_add hn0]
      congr 1
      ring
    have key : A ≤ C * c * A := by
      calc A = A * 1 := (mul_one A).symm
        _ ≤ A * Real.log n ^ q := mul_le_mul_of_nonneg_left (one_le_pow₀ hlog) hApos.le
        _ = powerLogRate lam q n := rfl
        _ ≤ C * powerLogRate lam' q' n := hn
        _ ≤ C * ((n : ℝ) ^ (-lam') * (c * (n : ℝ) ^ (lam' - lam))) := by
            unfold powerLogRate
            gcongr
        _ = C * c * A := by rw [← e1]; ring
    have h1 : 1 ≤ C * c := le_of_mul_le_mul_right (by simpa using key) hApos
    have h2 : C * c < 1 := by
      rw [hc, mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  exact hcontra.exists.choose_spec

/-- With equal power exponents, `(log n)^q = O((log n)^{q'})` forces `q ≤ q'`. -/
theorem le_of_isBigO_powerLogRate_same {lam : ℝ} {q q' : ℕ}
    (h : (fun n : ℕ => powerLogRate lam q n) =O[atTop] fun n : ℕ => powerLogRate lam q' n) :
    q ≤ q' := by
  by_contra hlt
  have hq : q' + 1 ≤ q := not_le.1 hlt
  obtain ⟨C, hC0, hC⟩ := exists_eventually_le_of_isBigO_powerLogRate h
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hC, hlogtop.eventually (eventually_gt_atTop C), eventually_ge_atTop 3]
      with n hn hCn hn3
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 1 ≤ Real.log n := one_le_log_nat hn3
    have hApos : 0 < (n : ℝ) ^ (-lam) := Real.rpow_pos_of_pos hn0 _
    have hlq' : 0 < Real.log n ^ q' := pow_pos (by linarith) _
    unfold powerLogRate at hn
    have h1 : Real.log n ^ q ≤ C * Real.log n ^ q' := by
      rw [mul_left_comm] at hn
      exact le_of_mul_le_mul_left hn hApos
    have h2 : Real.log n ^ q' * Real.log n ^ (q - q') = Real.log n ^ q := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : Real.log n ^ (q - q') ≤ C := by
      have : Real.log n ^ q' * Real.log n ^ (q - q') ≤ Real.log n ^ q' * C := by
        rw [h2, mul_comm (Real.log (n : ℝ) ^ q') C]
        exact h1
      exact le_of_mul_le_mul_left this hlq'
    have h4 : Real.log n ≤ Real.log n ^ (q - q') := le_self_pow₀ hlog (by omega)
    linarith
  exact hcontra.exists.choose_spec

/-- **Uniqueness of power–log orders along the integers**:
`n^{−λ}(log n)^q ≍ n^{−λ'}(log n)^{q'}` forces `λ = λ'` and `q = q'`. -/
theorem powerLogRate_pair_eq_of_isTheta_nat {lam lam' : ℝ} {q q' : ℕ}
    (h : (fun n : ℕ => powerLogRate lam q n) =Θ[atTop] fun n : ℕ => powerLogRate lam' q' n) :
    lam = lam' ∧ q = q' := by
  have h1 := le_of_isBigO_powerLogRate h.isBigO
  have h2 := le_of_isBigO_powerLogRate h.symm.isBigO
  have hl : lam = lam' := le_antisymm h2 h1
  subst hl
  exact ⟨rfl, le_antisymm (le_of_isBigO_powerLogRate_same h.isBigO)
    (le_of_isBigO_powerLogRate_same h.symm.isBigO)⟩

/-! ### From the scaled limit to the power–log order -/

theorem scaleA_inv (lam : ℝ) (m : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (scaleA lam m n)⁻¹ = powerLogRate lam (m - 1) n := by
  rw [scaleA_of_two_le lam m hn, powerLogRate, inv_div,
    Real.rpow_neg (by exact_mod_cast (by omega : 0 ≤ n)), div_eq_mul_inv, mul_comm]

/-- `A_n Z_n → L₀ > 0` gives `Z_n ≍ n^{−λ}(log n)^{m−1}` along the integers. -/
theorem isTheta_powerLogRate_of_tendsto_scaleA {Z : ℕ → ℝ} (lam : ℝ) (m : ℕ) {L₀ : ℝ}
    (hL : 0 < L₀) (h : Tendsto (fun n => scaleA lam m n * Z n) atTop (𝓝 L₀)) :
    (fun n : ℕ => Z n) =Θ[atTop] fun n : ℕ => powerLogRate lam (m - 1) n := by
  have hev : ∀ᶠ n : ℕ in atTop, L₀ / 2 ≤ scaleA lam m n * Z n ∧ scaleA lam m n * Z n ≤ 2 * L₀ := by
    have h1 := h.eventually (Icc_mem_nhds (by linarith : L₀ / 2 < L₀) (by linarith : L₀ < 2 * L₀))
    filter_upwards [h1] with n hn
    exact hn
  have hZ : ∀ᶠ n : ℕ in atTop, Z n = (scaleA lam m n * Z n) * powerLogRate lam (m - 1) n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [← scaleA_inv lam m hn, mul_comm (scaleA lam m n) (Z n), mul_assoc,
      mul_inv_cancel₀ (scaleA_pos lam m n).ne', mul_one]
  constructor
  · refine IsBigO.of_bound (2 * L₀) ?_
    filter_upwards [hev, hZ, eventually_ge_atTop 2] with n hn hZn hn2
    have hp := powerLogRate_pos_nat (lam := lam) (q := m - 1) hn2
    rw [hZn, Real.norm_of_nonneg (mul_nonneg (by linarith [hn.1]) hp.le),
      Real.norm_of_nonneg hp.le]
    exact mul_le_mul_of_nonneg_right hn.2 hp.le
  · refine IsBigO.of_bound (2 / L₀) ?_
    filter_upwards [hev, hZ, eventually_ge_atTop 2] with n hn hZn hn2
    have hp := powerLogRate_pos_nat (lam := lam) (q := m - 1) hn2
    rw [hZn, Real.norm_of_nonneg (mul_nonneg (by linarith [hn.1]) hp.le),
      Real.norm_of_nonneg hp.le]
    have hL0 : L₀ ≠ 0 := hL.ne'
    calc powerLogRate lam (m - 1) n = 2 / L₀ * ((L₀ / 2) * powerLogRate lam (m - 1) n) := by
          field_simp
      _ ≤ 2 / L₀ * (scaleA lam m n * Z n * powerLogRate lam (m - 1) n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn.1 hp.le) (by positivity)

/-! ### The comparison theorems -/

/-- **Conditional exponent identification**: if the same population integral satisfies
`A_n Z^pop(n) → L₀ > 0` (certified core theorem) and `Z^pop(N) ≍ N^{−λ_H}(log N)^{q_H}`
(hironaka), then `(λ, m − 1) = (λ_H, q_H)`. -/
theorem exponentPair_eq_of_population_comparison {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {lamH : ℝ} {qH : ℕ} (hΘ : LaplaceTheta μ f lamH qH) (lam : ℝ) (m : ℕ) {L₀ : ℝ}
    (hL : 0 < L₀)
    (hconv : Tendsto (fun n : ℕ => scaleA lam m n * ∫ x, Real.exp (-(n : ℝ) * f x) ∂μ) atTop
      (𝓝 L₀)) :
    lam = lamH ∧ m - 1 = qH := by
  have h1 := isTheta_powerLogRate_of_tendsto_scaleA lam m hL hconv
  have h2 : (fun n : ℕ => ∫ x, Real.exp (-(n : ℝ) * f x) ∂μ) =Θ[atTop]
      fun n : ℕ => powerLogRate lamH qH n :=
    ⟨hΘ.isBigO.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ)),
      hΘ.symm.isBigO.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))⟩
  exact powerLogRate_pair_eq_of_isTheta_nat (h1.symm.trans h2)

/-- **With hironaka's `Q n` explicit**: for a real-analytic nonnegative phase there is an exponent
pair `(λ_H, θ_H)` such that on every small closed cube, any certified population core theorem
`A_n Z^pop(n) → L₀ > 0` has `λ = λ_H` and `m − 1 = θ_H − 1`. -/
theorem exists_exponentPair_of_Q {n : ℕ} (hQ : Monomialize.Analytic.Q n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {K : (Fin n → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U)
    {w : Fin n → ℝ} (hw : w ∈ U) (h0 : K w = 0) (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0)
    (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lamH : ℚ) (thetaH : ℕ) (r₀ : ℝ), 0 < lamH ∧ 1 ≤ thetaH ∧ thetaH ≤ n ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (lam : ℝ) (m : ℕ) (L₀ : ℝ), 0 < L₀ →
        Tendsto (fun k : ℕ => scaleA lam m k *
          ∫ x in Metric.closedBall w r, Real.exp (-(k : ℝ) * K x)) atTop (𝓝 L₀) →
        lam = lamH ∧ m - 1 = thetaH - 1 := by
  obtain ⟨lamH, thetaH, r₀, hlam, h1, hn, hr₀, hΘ⟩ :=
    laplaceTheta_of_analyticOnNhd_nonneg_of_Q hQ hU hK hw h0 hne hK0
  exact ⟨lamH, thetaH, r₀, hlam, h1, hn, hr₀, fun r hr hrle lam m L₀ hL hconv =>
    exponentPair_eq_of_population_comparison (hΘ r hr hrle) lam m hL hconv⟩

/-- **The empirical exponent with the identified `λ_H`**: if `A_n Z_n^{emp} ⇒ L` with `L > 0`,
`Z_n^{emp} > 0`, and the pair has been identified with hironaka's, then
`log Z_n^{emp}/log n → −λ_H` in probability. -/
theorem tendstoInMeasure_log_div_log_of_population_comparison {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {L : Ω' → ℝ} {lam lamH : ℝ} (m : ℕ)
    (hcmp : lam = lamH)
    (hdist : TendstoInDistribution (fun n ω => scaleA lam m n * Z n ω) atTop L (fun _ => μ) μ')
    (hZpos : ∀ n ω, 0 < Z n ω) (hL : ∀ᵐ ω ∂μ', 0 < L ω) :
    TendstoInMeasure μ (fun n ω => Real.log (Z n ω) / Real.log n) atTop (fun _ => -lamH) :=
  hcmp ▸ tendstoInMeasure_log_div_log lam m hdist hZpos hL

end Grammar
