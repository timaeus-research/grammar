import Grammar.ExpectationBridge
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Conditional empirical assembly at the polynomial–logarithmic scale

Let `A_n = n^λ/(log n)^{m−1}` (`scaleA`, set to `1` for `n < 2`) and suppose the certified
empirical core theorem gives `A_n Z_n^core ⇒ L` for the assembled Gaussian coefficient `L`, while
the remainder is negligible at that scale. This file records the assembly wrapper with every
probabilistic hypothesis visible:

* **Slutsky**: `A_n Z_n^core ⇒ L` and `A_n Rem_n → 0` in probability give `A_n Z_n ⇒ L`
  (`tendstoInDistribution_scaled_assembly`); `E|A_n Rem_n| → 0` suffices for the second hypothesis
  (`tendstoInMeasure_zero_of_tendsto_integral_abs`), and `A_n e^{−cn} → 0` for every `c > 0`
  (`tendsto_scaleA_mul_exp_neg`) makes it automatic for exponentially small remainders;
* **expectations**: with a uniform `p`-th moment bound (`p > 1`) on `A_n Z_n^core` and
  `E|A_n Rem_n| → 0`, `E[A_n Z_n] → E L` (`tendsto_integral_scaled_assembly`, through the landed
  law-level bridge `tendsto_integral_of_tendstoInDistribution_of_moment`), and
  `E Z_n ∼ E L · n^{−λ}(log n)^{m−1}` when `E L > 0` (`isEquivalent_integral_scaled`);
* **exponents**: if `0 < L` a.s. and `Z_n > 0`, then `log Z_n / log n → −λ` in probability
  (`tendstoInMeasure_log_div_log`), by the portmanteau inequality for the closed sets
  `[M,∞)` and `(−∞,1/M]` (`tendsto_measure_log_of_tendstoInDistribution`).

Non-claims: `E L` is the expectation of the **limiting empirical coefficient**, not the population
coefficient (they differ in general — the denominator formula already exhibits the Gaussian
inflation); no geometric existence statement, no CLT, and no exponent identification are proved
here — those are inputs.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Grammar

/-! ### The scale `A_n = n^λ/(log n)^{m−1}` -/

/-- `A_n = n^λ/(log n)^{m−1}` for `n ≥ 2`, and `1` for `n < 2`. -/
noncomputable def scaleA (lam : ℝ) (m : ℕ) (n : ℕ) : ℝ :=
  if n < 2 then 1 else (n : ℝ) ^ lam / Real.log n ^ (m - 1)

theorem scaleA_of_two_le (lam : ℝ) (m : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    scaleA lam m n = (n : ℝ) ^ lam / Real.log n ^ (m - 1) := if_neg (not_lt.2 hn)

theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n :=
  Real.log_pos (by exact_mod_cast hn)

theorem scaleA_pos (lam : ℝ) (m n : ℕ) : 0 < scaleA lam m n := by
  unfold scaleA
  split_ifs with h
  · exact one_pos
  · exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _)
      (pow_pos (log_nat_pos (not_lt.1 h)) _)

theorem one_le_log_nat {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < n))]
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [Real.exp_one_lt_d9]

/-- `A_n e^{−cn} → 0` for every `c > 0`: the scale is polynomial–logarithmic. -/
theorem tendsto_scaleA_mul_exp_neg (lam : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => scaleA lam m n * Real.exp (-c * n)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam c hc).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 3] with n hn
  simp only [Function.comp_apply]
  rw [scaleA_of_two_le lam m (by omega), Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : 1 ≤ Real.log n ^ (m - 1) := one_le_pow₀ (one_le_log_nat hn)
  calc (n : ℝ) ^ lam / Real.log n ^ (m - 1) * Real.exp (-c * n)
      ≤ (n : ℝ) ^ lam / 1 * Real.exp (-c * n) := by gcongr
    _ = (n : ℝ) ^ lam * Real.exp (-c * n) := by rw [div_one]

/-- `log A_n / log n − λ → 0`. -/
theorem tendsto_log_scaleA_div_log (lam : ℝ) (m : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scaleA lam m n) / Real.log n - lam) atTop (𝓝 0) := by
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log n) / Real.log n) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).tendsto_div_nhds_zero
  have h := hll.const_mul (-((m - 1 : ℕ) : ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hlog := log_nat_pos (by omega : 2 ≤ n)
  rw [scaleA_of_two_le lam m (by omega), Real.log_div (Real.rpow_pos_of_pos
    (by exact_mod_cast (by omega : 0 < n)) _).ne' (pow_pos hlog _).ne',
    Real.log_rpow (by exact_mod_cast (by omega : 0 < n)), Real.log_pow]
  field_simp
  ring

/-! ### Slutsky assembly -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- **Slutsky assembly**: `A_n Z_n^core ⇒ L` and `A_n Rem_n → 0` in probability give
`A_n (Z_n^core + Rem_n) ⇒ L`. -/
theorem tendstoInDistribution_scaled_assembly {Zc R : ℕ → Ω → ℝ} {A : ℕ → ℝ} {L : Ω' → ℝ}
    (hcore : TendstoInDistribution (fun n ω => A n * Zc n ω) atTop L (fun _ => μ) μ')
    (hrem : TendstoInMeasure μ (fun n ω => A n * R n ω) atTop (fun _ => 0))
    (hRm : ∀ n, AEMeasurable (R n) μ) :
    TendstoInDistribution (fun n ω => A n * (Zc n ω + R n ω)) atTop L (fun _ => μ) μ' := by
  have h := hcore.add_of_tendstoInMeasure_const hrem (fun n => (hRm n).const_mul (A n))
  have e1 : (fun n ω => A n * (Zc n ω + R n ω)) =
      fun n => (fun ω => A n * Zc n ω) + fun ω => A n * R n ω := by
    funext n ω
    simp [mul_add]
  simp only [add_zero] at h
  rw [e1]
  exact h

omit [IsProbabilityMeasure μ] in
/-- `E|Y_n| → 0` gives `Y_n → 0` in probability. -/
theorem tendstoInMeasure_zero_of_tendsto_integral_abs {Y : ℕ → Ω → ℝ}
    (hY : ∀ n, Integrable (Y n) μ) (h : Tendsto (fun n => ∫ ω, |Y n ω| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ Y atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n => (hY n).aestronglyMeasurable)
    aestronglyMeasurable_const ?_
  have e : ∀ n, eLpNorm (Y n - fun _ => (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ ω, |Y n ω| ∂μ) := by
    intro n
    have : (Y n - fun _ => (0 : ℝ)) = Y n := by funext ω; simp
    rw [this, eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hY n)]
    simp only [Real.norm_eq_abs]
  simp_rw [e]
  simpa using ENNReal.tendsto_ofReal h

/-- **Expectations under a uniform `p`-th moment bound**: `E[A_n Z_n] → E L`. -/
theorem tendsto_integral_scaled_assembly {Zc R : ℕ → Ω → ℝ} {A : ℕ → ℝ} {L : Ω' → ℝ}
    (hcore : TendstoInDistribution (fun n ω => A n * Zc n ω) atTop L (fun _ => μ) μ')
    {p M : ℝ} (hp : 1 < p) (hint : ∀ n, Integrable (fun ω => |A n * Zc n ω| ^ p) μ)
    (hM : ∀ n, ∫ ω, |A n * Zc n ω| ^ p ∂μ ≤ M)
    (hRint : ∀ n, Integrable (fun ω => A n * R n ω) μ)
    (hrem : Tendsto (fun n => ∫ ω, |A n * R n ω| ∂μ) atTop (𝓝 0)) :
    Integrable L μ' ∧
      Tendsto (fun n => ∫ ω, A n * (Zc n ω + R n ω) ∂μ) atTop (𝓝 (∫ ω, L ω ∂μ')) := by
  obtain ⟨hL, hconv⟩ := tendsto_integral_of_tendstoInDistribution_of_moment (μ := fun _ => μ)
    hcore hp hint hM
  refine ⟨hL, ?_⟩
  have hZint : ∀ n, Integrable (fun ω => A n * Zc n ω) μ := fun n =>
    integrable_of_integrable_rpow_abs (hcore.forall_aemeasurable n).aestronglyMeasurable hp.le
      (hint n)
  have hR0 : Tendsto (fun n => ∫ ω, A n * R n ω ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hrem
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [Real.norm_eq_abs]
  have := hconv.add hR0
  rw [add_zero] at this
  refine this.congr fun n => ?_
  rw [← integral_add (hZint n) (hRint n)]
  congr 1
  funext ω
  ring

omit [IsProbabilityMeasure μ] in
/-- **The expectation asymptotics**: if `E[A_n Z_n] → E L > 0` then
`E Z_n ∼ E L · n^{−λ}(log n)^{m−1}`. -/
theorem isEquivalent_integral_scaled {Z : ℕ → Ω → ℝ} (lam : ℝ) (m : ℕ) {EL : ℝ} (hEL : 0 < EL)
    (h : Tendsto (fun n => ∫ ω, scaleA lam m n * Z n ω ∂μ) atTop (𝓝 EL)) :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => ∫ ω, Z n ω ∂μ)
      (fun n : ℕ => EL * ((n : ℝ) ^ (-lam) * Real.log n ^ (m - 1))) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h1 := h.div_const EL
  rw [div_self hEL.ne'] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog := log_nat_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  simp only [Pi.div_apply]
  rw [integral_const_mul, scaleA_of_two_le lam m hn, Real.rpow_neg hn0.le]
  field_simp

/-! ### Exponents -/

/-- **Tightness in logarithmic scale**: if `X_n ⇒ L` with `L > 0` a.s. and `X_n > 0`, then
`a_n log X_n → 0` in probability for every positive `a_n → 0`. -/
theorem tendsto_measure_log_of_tendstoInDistribution {X : ℕ → Ω → ℝ} {L : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop L (fun _ => μ) μ') (hXpos : ∀ n ω, 0 < X n ω)
    (hL : ∀ᵐ ω ∂μ', 0 < L ω) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε ≤ a n * |Real.log (X n ω)|}) atTop (𝓝 0) := by
  set ν : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩ with hν
  set ν₀ : ProbabilityMeasure ℝ :=
    ⟨μ'.map L, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩ with hν₀
  have hνlim : Tendsto ν atTop (𝓝 ν₀) := hX.tendsto
  have hLm : NullMeasurable L μ' := hX.aemeasurable_limit.nullMeasurable
  -- both tail probabilities of `L` vanish as `M → ∞`
  have hup : Tendsto (fun M : ℕ => μ' {ω | ((M : ℝ) + 1) ≤ L ω}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ') (s := fun M : ℕ => {ω | ((M : ℝ) + 1) ≤ L ω})
      (fun M => hLm measurableSet_Ici) (fun M M' hMM' ω hω => le_trans
        (by exact_mod_cast (Nat.succ_le_succ hMM' : M + 1 ≤ M' + 1) :
          ((M : ℝ) + 1 ≤ (M' : ℝ) + 1)) hω) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ M : ℕ, {ω | ((M : ℝ) + 1) ≤ L ω}) = ∅ := by
      ext ω
      simp only [mem_iInter, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨M, hM⟩ := exists_nat_gt (L ω)
      exact ⟨M, by linarith⟩
    rw [hempty, measure_empty] at this
    exact this
  have hdown : Tendsto (fun M : ℕ => μ' {ω | L ω ≤ 1 / ((M : ℝ) + 1)}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ')
      (s := fun M : ℕ => {ω | L ω ≤ 1 / ((M : ℝ) + 1)})
      (fun M => hLm measurableSet_Iic) (fun M M' hMM' ω hω => le_trans hω
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (M : ℝ) + 1)
          (by exact_mod_cast (Nat.succ_le_succ hMM' : M + 1 ≤ M' + 1) :
            ((M : ℝ) + 1 ≤ (M' : ℝ) + 1))))
      ⟨0, measure_ne_top _ _⟩
    have hsub : (⋂ M : ℕ, {ω | L ω ≤ 1 / ((M : ℝ) + 1)}) ⊆ {ω | ¬ 0 < L ω} := by
      intro ω hω
      simp only [mem_iInter, Set.mem_ofPred_eq] at hω
      simp only [Set.mem_ofPred_eq, not_lt]
      exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun M => hω M
    have hnull : μ' (⋂ M : ℕ, {ω | L ω ≤ 1 / ((M : ℝ) + 1)}) = 0 :=
      measure_mono_null hsub (ae_iff.1 hL)
    rw [hnull] at this
    exact this
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδtop | hδtop
  · exact Filter.Eventually.of_forall fun n => hδtop ▸ le_top
  have hq : (0 : ENNReal) < δ / 2 / 2 := ENNReal.half_pos (ENNReal.half_pos hδ.ne').ne'
  have hqtop : δ / 2 / 2 ≠ ⊤ := ENNReal.div_ne_top (ENNReal.div_ne_top hδtop (by norm_num))
    (by norm_num)
  have hlt : δ / 2 / 2 < δ / 2 / 2 + δ / 2 / 2 := ENNReal.lt_add_right hqtop hq.ne'
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, μ' {ω | ((M : ℝ) + 1) ≤ L ω} ≤ δ / 2 / 2 ∧
      μ' {ω | L ω ≤ 1 / ((M : ℝ) + 1)} ≤ δ / 2 / 2 :=
    ((ENNReal.tendsto_nhds_zero.1 hup _ hq).and (ENNReal.tendsto_nhds_zero.1 hdown _ hq)).exists
  have hM1' : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)]
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  -- portmanteau for the two closed sets
  have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hνlim
    (isClosed_Ici (a := (M : ℝ) + 1))
  have h2 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hνlim
    (isClosed_Iic (a := 1 / ((M : ℝ) + 1)))
  have e1 : ∀ n, (ν n : Measure ℝ) (Ici ((M : ℝ) + 1)) = μ {ω | ((M : ℝ) + 1) ≤ X n ω} :=
    fun n => Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) measurableSet_Ici
  have e2 : ∀ n, (ν n : Measure ℝ) (Iic (1 / ((M : ℝ) + 1))) =
      μ {ω | X n ω ≤ 1 / ((M : ℝ) + 1)} :=
    fun n => Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) measurableSet_Iic
  have e1' : (ν₀ : Measure ℝ) (Ici ((M : ℝ) + 1)) = μ' {ω | ((M : ℝ) + 1) ≤ L ω} :=
    Measure.map_apply_of_aemeasurable hX.aemeasurable_limit measurableSet_Ici
  have e2' : (ν₀ : Measure ℝ) (Iic (1 / ((M : ℝ) + 1))) = μ' {ω | L ω ≤ 1 / ((M : ℝ) + 1)} :=
    Measure.map_apply_of_aemeasurable hX.aemeasurable_limit measurableSet_Iic
  simp only [e1, e1'] at h1
  simp only [e2, e2'] at h2
  have hev1 : ∀ᶠ n in atTop, μ {ω | ((M : ℝ) + 1) ≤ X n ω} < δ / 2 / 2 + δ / 2 / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt h1 (lt_of_le_of_lt hM1 hlt))
  have hev2 : ∀ᶠ n in atTop, μ {ω | X n ω ≤ 1 / ((M : ℝ) + 1)} < δ / 2 / 2 + δ / 2 / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt h2 (lt_of_le_of_lt hM2 hlt))
  have hsmall : ∀ᶠ n in atTop, a n * Real.log ((M : ℝ) + 1) < ε := by
    have := ha0.mul_const (Real.log ((M : ℝ) + 1))
    rw [zero_mul] at this
    exact this.eventually_lt_const hε
  filter_upwards [hev1, hev2, hsmall] with n hn1 hn2 hn
  calc μ {ω | ε ≤ a n * |Real.log (X n ω)|}
      ≤ μ ({ω | ((M : ℝ) + 1) ≤ X n ω} ∪ {ω | X n ω ≤ 1 / ((M : ℝ) + 1)}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, mem_union] at hω ⊢
        have hXn := hXpos n ω
        rcases le_or_gt 0 (Real.log (X n ω)) with hl | hl
        · left
          rw [abs_of_nonneg hl] at hω
          have hlt' : Real.log ((M : ℝ) + 1) < Real.log (X n ω) := by
            by_contra hcon
            have := mul_le_mul_of_nonneg_left (not_lt.1 hcon) (ha n).le
            linarith
          exact ((Real.log_lt_log_iff hM0 hXn).1 hlt').le
        · right
          rw [abs_of_neg hl] at hω
          have hlt' : Real.log ((M : ℝ) + 1) < Real.log (X n ω)⁻¹ := by
            rw [Real.log_inv]
            by_contra hcon
            have := mul_le_mul_of_nonneg_left (not_lt.1 hcon) (ha n).le
            linarith
          have := (Real.log_lt_log_iff hM0 (inv_pos.2 hXn)).1 hlt'
          rw [lt_inv_comm₀ hM0 hXn] at this
          rw [one_div]
          exact this.le
    _ ≤ μ {ω | ((M : ℝ) + 1) ≤ X n ω} + μ {ω | X n ω ≤ 1 / ((M : ℝ) + 1)} :=
        measure_union_le _ _
    _ ≤ (δ / 2 / 2 + δ / 2 / 2) + (δ / 2 / 2 + δ / 2 / 2) := add_le_add hn1.le hn2.le
    _ = δ := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- **The exponent in probability**: if `A_n Z_n ⇒ L` with `0 < L` a.s. and `Z_n > 0`, then
`log Z_n / log n → −λ` in probability. -/
theorem tendstoInMeasure_log_div_log {Z : ℕ → Ω → ℝ} {L : Ω' → ℝ} (lam : ℝ) (m : ℕ)
    (hdist : TendstoInDistribution (fun n ω => scaleA lam m n * Z n ω) atTop L (fun _ => μ) μ')
    (hZpos : ∀ n ω, 0 < Z n ω) (hL : ∀ᵐ ω ∂μ', 0 < L ω) :
    TendstoInMeasure μ (fun n ω => Real.log (Z n ω) / Real.log n) atTop (fun _ => -lam) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · have hempty : ∀ n, {ω | ε ≤ edist (Real.log (Z n ω) / Real.log n) (-lam)} = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      rw [hεtop]
      exact edist_lt_top _ _
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds
  set ε' : ℝ := ε.toReal with hε'
  have hε'pos : 0 < ε' := ENNReal.toReal_pos hε.ne' hεtop
  have hdet := tendsto_log_scaleA_div_log lam m
  set a : ℕ → ℝ := fun n => (max (Real.log n) 1)⁻¹ with ha
  have ha0 : ∀ n, 0 < a n := fun n => inv_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hatop : Tendsto a atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => le_max_left _ _)
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  have hkey := tendsto_measure_log_of_tendstoInDistribution hdist
    (fun n ω => mul_pos (scaleA_pos lam m n) (hZpos n ω)) hL ha0 hatop (half_pos hε'pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hkey
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  have hsmall : ∀ᶠ n in atTop, |Real.log (scaleA lam m n) / Real.log n - lam| < ε' / 2 := by
    have := hdet.abs
    rw [abs_zero] at this
    exact this.eventually_lt_const (half_pos hε'pos)
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hn hn3
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hω' : ε' ≤ |Real.log (Z n ω) / Real.log n + lam| := by
    rw [edist_dist, Real.dist_eq, sub_neg_eq_add] at hω
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this
  have hlog1 := one_le_log_nat hn3
  have hlogpos : 0 < Real.log n := by linarith
  have hA := scaleA_pos lam m n
  have hZ := hZpos n ω
  have hamax : a n = (Real.log n)⁻¹ := by
    rw [ha]
    simp only
    rw [max_eq_left hlog1]
  rw [hamax, Real.log_mul hA.ne' hZ.ne']
  have hid : Real.log (Z n ω) / Real.log n + lam =
      (Real.log (scaleA lam m n) + Real.log (Z n ω)) / Real.log n -
        (Real.log (scaleA lam m n) / Real.log n - lam) := by
    field_simp
    ring
  rw [hid] at hω'
  have htri := abs_sub ((Real.log (scaleA lam m n) + Real.log (Z n ω)) / Real.log n)
    (Real.log (scaleA lam m n) / Real.log n - lam)
  have : ε' / 2 ≤ |(Real.log (scaleA lam m n) + Real.log (Z n ω)) / Real.log n| := by linarith
  rw [abs_div, abs_of_pos hlogpos] at this
  rw [inv_mul_eq_div]
  exact this

end Grammar
