import Grammar.CertifiedCoreAssembly
import Grammar.MonomialMixedAsymptotic

/-!
# Discharging the reduced-temperature population bound

The uniform-moment theorems of `BoxMomentBound.lean` and the certified-core expectation assembly
of `CertifiedCoreAssembly.lean` take as a hypothesis the *certified population bound*
`sup_{n ≥ n₀} A_n Z^pop_α(n b^{2|k|}) ≤ C_α` at the reduced temperature `α = β(1 − pβc/2)`.
The population box mass is the paper's monomial box integral
`Z^pop_α(N') = ∫_{(0,1]^d} u^h e^{−αN'u^{2k}} du = monomialBoxReal d h k α N'`
(`popBoxMass_eq_monomialBoxReal`), whose exact leading asymptotics
`∼ K · N'^{−λ₀} (log N')^{m₀−1}` with `λ₀ = min_i (h_i+1)/(2k_i)` and `m₀` the multiplicity are
`monomialBoxReal_minRatio_isEquivalent`. Hence at the scale `A_n = n^λ/(log n)^{m−1}` the scaled
population mass is eventually bounded whenever the box's exponent pair dominates the assembly
scale, `λ < λ₀` or (`λ = λ₀` and `m₀ ≤ m`) (`exists_population_bound_scaleA`), and the
population-bound hypothesis is discharged in the uniform moment bound
(`uniform_moment_scaled_dataBoxIntegral_of_dominated`) and in the expectation assembly
(`tendsto_integral_scaled_assembly_of_dominated_cores`).

Non-claims: the full-box exponential-moment bound of the finite-`n` phase field and the field
limit `A_n Z^core_n ⇒ L` remain hypotheses; the domination condition is on the box exponent
pairs, which for the assembled core at its own leading scale holds by definition of that scale.
-/

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Set

namespace Grammar

/-- The population box mass is the monomial box integral at temperature `α`. -/
theorem popBoxMass_eq_monomialBoxReal (n : ℕ) (h k : Fin (n + 1) → ℕ) (α N' : ℝ)
    (hN' : 0 ≤ N') : popBoxMass n h k α N' = monomialBoxReal (n + 1) h k α N' := by
  rw [popBoxMass_eq n h k α N' hN']
  rfl

/-- **Eventual boundedness of the scaled power–log profile** under domination of the exponent
pair: `A_n · (nc)^{−λ₀} log(nc)^{q₀} ≤ c^{−λ₀} 2^{q₀}` eventually when `λ < λ₀`, or `λ = λ₀` and
`q₀ ≤ m − 1`. -/
theorem eventually_scaleA_mul_powerLog_le {lam lam₀ : ℝ} {mult q₀ : ℕ} {c : ℝ} (hc : 0 < c)
    (hdom : lam < lam₀ ∨ (lam = lam₀ ∧ q₀ ≤ mult - 1)) :
    ∀ᶠ m : ℕ in atTop, 0 ≤ Real.log ((m : ℝ) * c) ∧
      scaleA lam mult m * (((m : ℝ) * c) ^ (-lam₀) * Real.log ((m : ℝ) * c) ^ q₀) ≤
        c ^ (-lam₀) * 2 ^ q₀ := by
  have hlog : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀) * Real.log m ^ q₀ ≤ Real.log m ^ (mult - 1) := by
    rcases hdom with hlt | ⟨heq, hq⟩
    · have hε : 0 < lam₀ - lam := sub_pos.2 hlt
      have hlo := ((isLittleO_log_rpow_rpow_atTop (q₀ : ℝ) hε).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).def one_pos
      filter_upwards [hlo, hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with m hm h1 hm1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hlpow : Real.log m ^ q₀ ≤ (m : ℝ) ^ (lam₀ - lam) := by
        have := hm
        simp only [Function.comp, Real.norm_eq_abs, one_mul, Real.rpow_natCast] at this
        rwa [abs_of_nonneg (pow_nonneg (by linarith) _),
          abs_of_nonneg (Real.rpow_nonneg hm0.le _)] at this
      calc (m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀) * Real.log m ^ q₀
          ≤ (m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀) * (m : ℝ) ^ (lam₀ - lam) :=
            mul_le_mul_of_nonneg_left hlpow
              (mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hm0.le _))
        _ = 1 := by
            rw [← Real.rpow_add hm0, ← Real.rpow_add hm0,
              show lam + -lam₀ + (lam₀ - lam) = 0 by ring, Real.rpow_zero]
        _ ≤ Real.log m ^ (mult - 1) := one_le_pow₀ h1
    · subst heq
      filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with m h1 hm1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      rw [Real.rpow_neg hm0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hm0 _).ne', one_mul]
      exact pow_le_pow_right₀ h1 hq
  filter_upwards [hratio, hlog.eventually_ge_atTop (max 1 |Real.log c|), eventually_ge_atTop 2]
    with m hr hm hm2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogm : 1 ≤ Real.log m := le_trans (le_max_left _ _) hm
  have habs : |Real.log c| ≤ Real.log m := le_trans (le_max_right _ _) hm
  have hlmc : Real.log ((m : ℝ) * c) = Real.log m + Real.log c := Real.log_mul hm0.ne' hc.ne'
  have h0 : 0 ≤ Real.log ((m : ℝ) * c) := by
    rw [hlmc]
    linarith [neg_abs_le (Real.log c)]
  have h2 : Real.log ((m : ℝ) * c) ≤ 2 * Real.log m := by
    rw [hlmc]
    linarith [le_abs_self (Real.log c)]
  refine ⟨h0, ?_⟩
  rw [scaleA_of_two_le lam mult hm2, Real.mul_rpow hm0.le hc.le]
  have hpow : Real.log ((m : ℝ) * c) ^ q₀ ≤ 2 ^ q₀ * Real.log m ^ q₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h2 q₀
  have hlpos : 0 < Real.log m ^ (mult - 1) := pow_pos (by linarith) _
  have hcn : 0 ≤ c ^ (-lam₀) := Real.rpow_nonneg hc.le _
  have hmn : 0 ≤ (m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀) :=
    mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hm0.le _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hlpos]
  calc (m : ℝ) ^ lam * ((m : ℝ) ^ (-lam₀) * c ^ (-lam₀) * Real.log ((m : ℝ) * c) ^ q₀)
      = c ^ (-lam₀) * ((m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀)) * Real.log ((m : ℝ) * c) ^ q₀ := by
        ring
    _ ≤ c ^ (-lam₀) * ((m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀)) * (2 ^ q₀ * Real.log m ^ q₀) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hcn hmn)
    _ = c ^ (-lam₀) * 2 ^ q₀ * ((m : ℝ) ^ lam * (m : ℝ) ^ (-lam₀) * Real.log m ^ q₀) := by ring
    _ ≤ c ^ (-lam₀) * 2 ^ q₀ * Real.log m ^ (mult - 1) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg hcn (by positivity))

/-- **The certified population bound is a theorem** at the scale `A_n = n^λ/(log n)^{m−1}` whenever
the box exponent pair `(λ₀, m₀) = (min_i (h_i+1)/(2k_i), multiplicity)` dominates `(λ, m)`:
`λ < λ₀`, or `λ = λ₀` and `m₀ ≤ m`. -/
theorem exists_population_bound_scaleA (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {α : ℝ} (hα : 0 < α) {b : ℝ} (hb : 0 < b) {lam : ℝ} {mult : ℕ}
    (hdom : lam < minRatio h k ∨
      (lam = minRatio h k ∧ multCount (ratioExp h k) (minRatio h k) - 1 ≤ mult - 1)) :
    ∃ (n₀ : ℕ) (Cα : ℝ), ∀ m : ℕ, n₀ ≤ m →
      scaleA lam mult m * popBoxMass n h k α (boxScale k b m) ≤ Cα := by
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := pow_pos hb _
  obtain ⟨C, hC⟩ := (monomialBoxReal_minRatio_isEquivalent n h k hk α hα).isBigO.bound
  have htend : Tendsto (fun m : ℕ => (m : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc0
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((htend.eventually hC).and (eventually_scaleA_mul_powerLog_le (lam := lam) (mult := mult)
      (lam₀ := minRatio h k) (q₀ := multCount (ratioExp h k) (minRatio h k) - 1) hc0 hdom))
  refine ⟨n₀, max C 0 * |monomialMixedConst h k (minRatio h k) α| * (c ^ (-(minRatio h k)) *
    2 ^ (multCount (ratioExp h k) (minRatio h k) - 1)), fun m hm => ?_⟩
  obtain ⟨h1, h0, h2⟩ := hn₀ m hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hbs : boxScale k b (m : ℝ) = (m : ℝ) * c := rfl
  rw [hbs, popBoxMass_eq_monomialBoxReal n h k α _ (mul_nonneg hm0 hc0.le)]
  have hsA : 0 ≤ scaleA lam mult m := (scaleA_pos lam mult m).le
  have hX : 0 ≤ ((m : ℝ) * c) ^ (-(minRatio h k)) := Real.rpow_nonneg (mul_nonneg hm0 hc0.le) _
  have hY : 0 ≤ Real.log ((m : ℝ) * c) ^ (multCount (ratioExp h k) (minRatio h k) - 1) :=
    pow_nonneg h0 _
  calc scaleA lam mult m * monomialBoxReal (n + 1) h k α ((m : ℝ) * c)
      ≤ scaleA lam mult m * (max C 0 * (|monomialMixedConst h k (minRatio h k) α| *
          (((m : ℝ) * c) ^ (-(minRatio h k)) *
            Real.log ((m : ℝ) * c) ^ (multCount (ratioExp h k) (minRatio h k) - 1)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hsA
        calc monomialBoxReal (n + 1) h k α ((m : ℝ) * c)
            ≤ ‖monomialBoxReal (n + 1) h k α ((m : ℝ) * c)‖ :=
              (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
          _ ≤ C * ‖monomialMixedConst h k (minRatio h k) α * ((m : ℝ) * c) ^ (-(minRatio h k)) *
                Real.log ((m : ℝ) * c) ^ (multCount (ratioExp h k) (minRatio h k) - 1)‖ := h1
          _ ≤ max C 0 * ‖monomialMixedConst h k (minRatio h k) α *
                ((m : ℝ) * c) ^ (-(minRatio h k)) *
                Real.log ((m : ℝ) * c) ^ (multCount (ratioExp h k) (minRatio h k) - 1)‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
          _ = _ := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hX, abs_of_nonneg hY,
                mul_assoc]
    _ = max C 0 * |monomialMixedConst h k (minRatio h k) α| *
          (scaleA lam mult m * (((m : ℝ) * c) ^ (-(minRatio h k)) *
            Real.log ((m : ℝ) * c) ^ (multCount (ratioExp h k) (minRatio h k) - 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_max_right _ _) (abs_nonneg _))

section Discharge

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- **Uniform `p`-th moments of the scaled certified box core with the population bound
discharged**: at the scale `A_n = n^λ/(log n)^{m−1}` dominated by the box exponent pair, bounded
Borel data with full-box exponential moments have eventually uniformly bounded scaled moments. -/
theorem uniform_moment_scaled_dataBoxIntegral_of_dominated (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) {β c p M b : ℝ} (hβ : 0 < β) (hp : 1 ≤ p) (hc : p * β * c < 2)
    (hM : 0 ≤ M) (hb : 0 < b) {lam : ℝ} {mult : ℕ}
    (hdom : lam < minRatio h k ∨
      (lam = minRatio h k ∧ multCount (ratioExp h k) (minRatio h k) - 1 ≤ mult - 1))
    (x : ℕ → Ω → DataSpace (n + 1)) (hx : ∀ m, Measurable (x m))
    (hxM : ∀ m ω, CoeffFamily.mass (etaCoord (x m ω)) ≤ M)
    (hmgf : ∀ m, ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * CoeffFamily.evalF (xiCoord (x m ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2))) :
    ∃ (n₀ : ℕ) (M' : ℝ), ∀ m, n₀ ≤ m →
      ∫⁻ ω, ENNReal.ofReal (|scaleA lam mult m * dataBoxIntegral n h k β m b (x m ω)| ^ p) ∂P ≤
        ENNReal.ofReal M' ^ p := by
  have hα : 0 < β * (1 - p * β * c / 2) := mul_pos hβ (by linarith)
  obtain ⟨n₀, Cα, hpop⟩ := exists_population_bound_scaleA n h k hk hα hb (lam := lam)
    (mult := mult) hdom
  exact ⟨n₀, M * b ^ (∑ i, h i + (n + 1)) * Cα,
    uniform_moment_scaled_dataBoxIntegral P n h k hβ hp hc hM hb (A := scaleA lam mult)
      (Nn := fun m => (m : ℝ)) (fun m => (scaleA_pos lam mult m).le) (fun m => Nat.cast_nonneg m)
      x hx hxM hmgf hpop⟩

variable (n : ℕ) {J : ℕ} (h k : Fin J → Fin (n + 1) → ℕ) (b : Fin J → ℝ)
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- A common eventual population bound for finitely many dominated boxes. -/
theorem exists_population_bound_scaleA_finite (hk : ∀ j i, 0 < k j i) {α : ℝ} (hα : 0 < α)
    (hb : ∀ j, 0 < b j) {lam : ℝ} {mult : ℕ}
    (hdom : ∀ j, lam < minRatio (h j) (k j) ∨
      (lam = minRatio (h j) (k j) ∧
        multCount (ratioExp (h j) (k j)) (minRatio (h j) (k j)) - 1 ≤ mult - 1)) :
    ∃ (n₀ : ℕ) (Cα : Fin J → ℝ), ∀ j m, n₀ ≤ m →
      scaleA lam mult m * popBoxMass n (h j) (k j) α (boxScale (k j) (b j) m) ≤ Cα j := by
  choose n₀ Cα hC using fun j =>
    exists_population_bound_scaleA n (h j) (k j) (hk j) hα (hb j) (lam := lam) (mult := mult)
      (hdom j)
  refine ⟨Finset.univ.sup n₀, Cα, fun j m hm => hC j m (le_trans ?_ hm)⟩
  exact Finset.le_sup (Finset.mem_univ j)

/-- **The expectation assembly for dominated certified sub-Gaussian cores**: the reduced-temperature
population bound of `tendsto_integral_scaled_assembly_of_certified_subgaussian_cores` is discharged
by the monomial box asymptotics when every box exponent pair dominates the assembly scale
`A_n = n^λ/(log n)^{m−1}`. Remaining hypotheses: the field limit `A_n Z^core_n ⇒ L`, bounded
Borel data, full-box exponential moments, and `E|A_n Rem_n| → 0`. -/
theorem tendsto_integral_scaled_assembly_of_dominated_cores (hk : ∀ j i, 0 < k j i)
    {β c p M : ℝ} (hβ : 0 < β) (hp : 1 < p) (hc : p * β * c < 2) (hM : 0 ≤ M)
    (hb : ∀ j, 0 < b j) {lam : ℝ} {mult : ℕ}
    (hdom : ∀ j, lam < minRatio (h j) (k j) ∨
      (lam = minRatio (h j) (k j) ∧
        multCount (ratioExp (h j) (k j)) (minRatio (h j) (k j)) - 1 ≤ mult - 1))
    (x : Fin J → ℕ → Ω → DataSpace (n + 1)) (hx : ∀ j m, Measurable (x j m))
    (hxM : ∀ j m ω, CoeffFamily.mass (etaCoord (x j m ω)) ≤ M)
    (hmgf : ∀ j m, ∀ u ∈ unitBox (n + 1), ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * CoeffFamily.evalF (xiCoord (x j m ω)) u)) ∂P ≤
        ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    {L : Ω' → ℝ}
    (hcore : TendstoInDistribution
      (fun m ω => scaleA lam mult m * coreSum n h k b β (fun m => (m : ℝ)) x m ω) atTop L
      (fun _ => P) μ')
    {R : ℕ → Ω → ℝ} (hRint : ∀ m, Integrable (fun ω => scaleA lam mult m * R m ω) P)
    (hrem : Tendsto (fun m => ∫ ω, |scaleA lam mult m * R m ω| ∂P) atTop (𝓝 0)) :
    Integrable L μ' ∧ Tendsto (fun m => ∫ ω, scaleA lam mult m *
      (coreSum n h k b β (fun m => (m : ℝ)) x m ω + R m ω) ∂P) atTop (𝓝 (∫ ω, L ω ∂μ')) := by
  have hα : 0 < β * (1 - p * β * c / 2) := mul_pos hβ (by linarith)
  obtain ⟨n₀, Cα, hpop⟩ := exists_population_bound_scaleA_finite n h k b hk hα hb
    (lam := lam) (mult := mult) hdom
  exact tendsto_integral_scaled_assembly_of_certified_subgaussian_cores P n h k b hβ hp hc hM hb
    (A := scaleA lam mult) (Nn := fun m => (m : ℝ)) (fun m => (scaleA_pos lam mult m).le)
    (fun m => Nat.cast_nonneg m) x hx hxM hmgf hpop hcore hRint hrem

end Discharge

end Grammar
