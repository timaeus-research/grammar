/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.StochasticData
import Grammar.CoeffStability
import Grammar.FluctuationDerivativeMu

/-!
# Ballwise Lipschitz continuity of the Taylor-tree coefficients (Stage S2 — the gate)

Unit 271 (Astra #33, unit 2 of Programme S). The canonical unit-box coefficients
`A_{μ,j}(cξ, cη) = familySpectralCoeff` are Lipschitz on every ball of the weighted-ℓ¹ data:
for absolutely summable families with `mass cξ, mass cξ', mass cη, mass cη' ≤ R`,

`|A_{μ,j}(cξ', cη') − A_{μ,j}(cξ, cη)| ≤ familyLipConst · (mass(cξ' − cξ) + mass(cη' − cη))`
(`abs_familySpectralCoeff_sub_le`, constant `familyLipConst n k β μ R`). The new ingredient
compared with the Stage 4 stability gate
(`abs_spectralCoeff_sub_le`, fixed constant phase) is the **varying constant phase**
`a = ξ(0)`: by the mean value theorem and `∂_a fluctMoment = β fluctMoment(p+1)`
(`hasDerivAt_fluctMoment`),
`|fluctMoment β a p μ i − fluctMoment β a' p μ i| ≤ β M_{μ,n,p+1}(R) |a − a'|`
on `|a|, |a'| ≤ R` (`abs_fluctMoment_sub_le`), which propagates through the kernel `S_p` and the
kernel functional `T_p` (`abs_kernelFunctional_sub_phase_le`). The other two perturbations
(amplitude and constant-free phase `J`) go through the linearity of `T_p` and the mass algebra of
the Cauchy product (`mass_convPow_sub_le`), and the three resulting series in `p` are summed in
closed form by the Tonelli identity `∑_p (βR)^p/p! M_{ν,n,p}(R) = M_{ν,n,0}(2R)` and its shifted
forms. The constant depends on the data only through the ball radius `R`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The fluctuation moments are Lipschitz in the constant phase on `[-R, R]`, with constant
`β M_{μ,n,p+1}(R)`. -/
theorem abs_fluctMoment_sub_le (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) {R a a' : ℝ} (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |fluctMoment β a p μ i - fluctMoment β a' p μ i| ≤
      β * phaseLogMoment β R μ n (p + 1) * |a - a'| := by
  set f' : ℝ → ℝ := fun c => β * fluctMoment β c (p + 1) μ i with hf'
  have hf : ∀ c ∈ Icc (-R) R, HasDerivWithinAt (fun c => fluctMoment β c p μ i) (f' c)
      (Icc (-R) R) c :=
    fun c _ => (hasDerivAt_fluctMoment β hβ p hμ i c).hasDerivWithinAt
  have hbound : ∀ c ∈ Icc (-R) R, ‖f' c‖ ≤ β * phaseLogMoment β R μ n (p + 1) := by
    intro c hc
    rw [hf', Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    exact (abs_fluctMoment_le β c hβ (p + 1) hμ hi).trans
      (phaseLogMoment_mono β hβ hc.2 hμ n (p + 1))
  have key := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (abs_le.1 ha') (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using key

/-- The kernel `S_p(μ,j;γ)` is Lipschitz in the constant phase, uniformly in `γ`. -/
theorem abs_kernelS_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) {R a a' : ℝ}
    (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |kernelS n h k β a p μ j γ - kernelS n h k β a' p μ j γ| ≤
      kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) * |a - a'| := by
  unfold kernelS kernelBudget
  rw [← Finset.sum_sub_distrib]
  set M := β * phaseLogMoment β R μ n (p + 1) * |a - a'| with hM
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg hβ.le (phaseLogMoment_nonneg _ _ _ _ _)) (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a p μ (q - j) -
        PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a' p μ (q - j)| ≤
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
    intro q hq
    have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
    rw [← mul_sub, abs_mul, abs_mul, Nat.abs_cast]
    refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n (h + γ) k hk μ q) ?_
      (by positivity) (by positivity)) (abs_fluctMoment_sub_le β hβ p hμ (by omega) ha ha')
      (abs_nonneg _) (by positivity)
    calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
      _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Ico]
  have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
  have hpos : 0 ≤ (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M :=
    mul_nonneg (by positivity) hM0
  calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
      ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hM]; ring

/-- The kernel functional is Lipschitz in the constant phase: `|T_p(a; f) − T_p(a'; f)| ≤
K_k D β M_{μ,n,p+1}(R) · mass f · |a − a'|`. -/
theorem abs_kernelFunctional_sub_phase_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) {R a a' : ℝ} (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |kernelFunctional n h k β a p μ j f - kernelFunctional n h k β a' p μ j f| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) *
        mass f * |a - a'| := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  unfold kernelFunctional
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  have hs1 : Summable fun γ => f γ * kernelS n h k β a p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a hβ p hμ j hf)
  have hs2 : Summable fun γ => f γ * kernelS n h k β a' p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a' hβ p hμ j hf)
  rw [← hs1.tsum_sub hs2]
  set C := kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) * |a - a'| with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (mul_nonneg (kernelBudget_nonneg n k)
      (mul_nonneg hβ.le (phaseLogMoment_nonneg _ _ _ _ _))) (abs_nonneg _)
  have hterm : ∀ γ, |f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ| ≤
      |f γ| * C := by
    intro γ
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_kernelS_sub_le n h k hk β hβ p hμ j γ ha ha')
      (abs_nonneg _)
  have hsum : Summable fun γ =>
      |f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm (hf.mul_right C)
  have h1 : |∑' γ, (f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)| ≤
      ∑' γ, |f γ| * C := by
    have hn := norm_tsum_le_tsum_norm
      (f := fun γ => f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)
      (by simpa [Real.norm_eq_abs] using hsum)
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (Summable.tsum_le_tsum hterm hsum (hf.mul_right C))
  rw [tsum_mul_right] at h1
  calc (∏ i, 1 / (2 * (k i : ℝ))) *
        |∑' γ, (f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)|
      ≤ (∏ i, 1 / (2 * (k i : ℝ))) * (mass f * C) := mul_le_mul_of_nonneg_left h1 hK
    _ = _ := by rw [hC]; ring

theorem fluctFamily_sub {d : ℕ} (c c' : CoeffFamily d) :
    fluctFamily (c - c') = fluctFamily c - fluctFamily c' := by
  funext γ
  simp only [fluctFamily, Pi.sub_apply]
  split_ifs <;> simp

theorem abs_apply_le_mass {d : ℕ} {c : CoeffFamily d} (hc : AbsSummable c) (γ : Fin d → ℕ) :
    |c γ| ≤ mass c :=
  hc.le_tsum γ fun _ _ => abs_nonneg _

/-- The Lipschitz constant of the unit-box coefficients on the data ball of radius `R`. -/
noncomputable def familyLipConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β μ R : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k *
    (2 * β * R * phaseLogMoment β (R + R) (μ + 1 / 2) n 0 + phaseLogMoment β (R + R) μ n 0)

theorem familyLipConst_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) (μ : ℝ) {R : ℝ}
    (hR : 0 ≤ R) : 0 ≤ familyLipConst n k β μ R := by
  unfold familyLipConst
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  refine mul_nonneg (mul_nonneg hK (kernelBudget_nonneg n k)) ?_
  have := phaseLogMoment_nonneg β (R + R) (μ + 1 / 2) n 0
  have := phaseLogMoment_nonneg β (R + R) μ n 0
  positivity

/-- **The coefficient series is Lipschitz on data balls** (`μ > 0`): for masses `≤ R`,
`|A_{μ,j}(cξ', cη') − A_{μ,j}(cξ, cη)| ≤ familyLipConst · (mass (cξ' − cξ) + mass (cη' − cη))`. -/
theorem abs_familyCoeffSeries_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) (hRη' : mass cη' ≤ R) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    |familyCoeffSeries n h k β cξ' cη' μ j - familyCoeffSeries n h k β cξ cη μ j| ≤
      familyLipConst n k β μ R * (mass (cξ' - cξ) + mass (cη' - cη)) := by
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  set K₀ := (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg hK (kernelBudget_nonneg n k)
  -- data
  set a := cξ 0 with ha_def
  set a' := cξ' 0 with ha'_def
  set J := fluctFamily cξ with hJ
  set J' := fluctFamily cξ' with hJ'
  have hJs : AbsSummable J := hξ.fluctFamily
  have hJ's : AbsSummable J' := hξ'.fluctFamily
  have hJR : mass J ≤ R := (mass_fluctFamily_le hξ).trans hRξ
  have hJ'R : mass J' ≤ R := (mass_fluctFamily_le hξ').trans hRξ'
  have haR : |a| ≤ R := (abs_apply_le_mass hξ 0).trans hRξ
  have ha'R : |a'| ≤ R := (abs_apply_le_mass hξ' 0).trans hRξ'
  have ha'R' : a' ≤ R := (le_abs_self _).trans ha'R
  set Δξ := mass (cξ' - cξ) with hΔξ
  set Δη := mass (cη' - cη) with hΔη
  have hΔξ0 : 0 ≤ Δξ := mass_nonneg _
  have hΔη0 : 0 ≤ Δη := mass_nonneg _
  have haa : |a' - a| ≤ Δξ := by
    have := abs_apply_le_mass (hξ'.sub hξ) 0
    simpa [Pi.sub_apply] using this
  have hJJ : mass (J' - J) ≤ Δξ := by
    rw [hJ, hJ', ← fluctFamily_sub]
    exact mass_fluctFamily_le (hξ'.sub hξ)
  -- the three majorant series
  set M := phaseLogMoment β (R + R) μ n 0 with hM
  set M' := phaseLogMoment β (R + R) (μ + 1 / 2) n 0 with hM'
  have hb : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1))) (β * R * M') := by
    have hs := (summable_phaseLogMoment_series β R R (μ + 1 / 2) hβ (by linarith) hR0 n).hasSum
    rw [tsum_phaseLogMoment_series β R R (μ + 1 / 2) hβ (by linarith) hR0 n] at hs
    refine (hs.mul_left (β * R)).congr_fun fun p => ?_
    rw [phaseLogMoment_succ, mul_pow, pow_succ]
    ring
  have hc : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p))
      M := by
    have hs := (summable_phaseLogMoment_series β R R μ hβ hμ hR0 n).hasSum
    rw [tsum_phaseLogMoment_series β R R μ hβ hμ hR0 n] at hs
    refine hs.congr_fun fun p => ?_
    rw [mul_pow]; ring
  have hd : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1))))) (R * (β * M')) := by
    have hs := hasSum_phase_series_shift β R R μ hβ hμ hR0 n
    refine (hs.mul_left R).congr_fun fun p => ?_
    ring
  -- termwise bound
  have hterm : ∀ p : ℕ,
      |familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p| ≤
      K₀ * (β ^ p / (p.factorial : ℝ) * (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1)) * Δξ +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p) * Δη +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1)))) *
          Δξ) := by
    intro p
    unfold familyCoeffTerm
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ))]
    set f := CoeffFamily.conv cη (CoeffFamily.convPow J p) with hf
    set f' := CoeffFamily.conv cη' (CoeffFamily.convPow J' p) with hf'
    have hfs : AbsSummable f := hη.conv (hJs.convPow p)
    have hf's : AbsSummable f' := hη'.conv (hJ's.convPow p)
    have hfR : mass f' ≤ R * R ^ p :=
      (mass_conv_le hη' (hJ's.convPow p)).trans
        (mul_le_mul hRη' (mass_convPow_le hJ's hJ'R p) (mass_nonneg _) hR0)
    -- split the difference: phase at `f'`, then family difference at `a`
    have hsplit : kernelFunctional n h k β a' p μ j f' - kernelFunctional n h k β a p μ j f =
        (kernelFunctional n h k β a' p μ j f' - kernelFunctional n h k β a p μ j f') +
          kernelFunctional n h k β a p μ j (f' - f) := by
      rw [← kernelFunctional_sub n h k hk β a hβ p hμ j hf's hfs]; ring
    have h1 := abs_kernelFunctional_sub_phase_le n h k hk β hβ p hμ j hf's ha'R haR
    have h2 := abs_kernelFunctional_le n h k hk β a hβ p hμ j (hf's.sub hfs)
    -- mass of the family difference
    have hff : f' - f = CoeffFamily.conv (cη' - cη) (CoeffFamily.convPow J' p) +
        CoeffFamily.conv cη (CoeffFamily.convPow J' p - CoeffFamily.convPow J p) := by
      rw [CoeffFamily.conv_sub_left, CoeffFamily.conv_sub_right, hf, hf']; abel
    have hmass : mass (f' - f) ≤ Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ) := by
      rw [hff]
      have hA : AbsSummable (CoeffFamily.conv (cη' - cη) (CoeffFamily.convPow J' p)) :=
        (hη'.sub hη).conv (hJ's.convPow p)
      have hB : AbsSummable (CoeffFamily.conv cη
          (CoeffFamily.convPow J' p - CoeffFamily.convPow J p)) :=
        hη.conv ((hJ's.convPow p).sub (hJs.convPow p))
      refine (mass_add_le hA hB).trans (add_le_add ?_ ?_)
      · exact (mass_conv_le (hη'.sub hη) (hJ's.convPow p)).trans
          (mul_le_mul_of_nonneg_left (mass_convPow_le hJ's hJ'R p) (mass_nonneg _))
      · refine (mass_conv_le hη ((hJ's.convPow p).sub (hJs.convPow p))).trans ?_
        refine mul_le_mul hRη ?_ (mass_nonneg _) hR0
        exact (mass_convPow_sub_le hJ's hJs hJ'R hJR p).trans
          (mul_le_mul_of_nonneg_left hJJ (by positivity))
    have hMa : phaseLogMoment β a μ n p ≤ phaseLogMoment β R μ n p :=
      phaseLogMoment_mono β hβ ((le_abs_self a).trans haR) hμ n p
    have hM0 : 0 ≤ phaseLogMoment β R μ n p := phaseLogMoment_nonneg _ _ _ _ _
    have hM1 : 0 ≤ phaseLogMoment β R μ n (p + 1) := phaseLogMoment_nonneg _ _ _ _ _
    rw [hsplit]
    refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2))
      (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ))).trans ?_
    have hmassf : mass f' * |a' - a| ≤ R * R ^ p * Δξ :=
      mul_le_mul hfR haa (abs_nonneg _) (by positivity)
    have hfam : phaseLogMoment β a μ n p * mass (f' - f) ≤
        phaseLogMoment β R μ n p * (Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ)) :=
      mul_le_mul hMa hmass (mass_nonneg _) hM0
    have hKD : 0 ≤ K₀ * (β * phaseLogMoment β R μ n (p + 1)) := by positivity
    calc β ^ p / (p.factorial : ℝ) *
          (K₀ * (β * phaseLogMoment β R μ n (p + 1)) * mass f' * |a' - a| +
            K₀ * phaseLogMoment β a μ n p * mass (f' - f))
        ≤ β ^ p / (p.factorial : ℝ) *
          (K₀ * (β * phaseLogMoment β R μ n (p + 1)) * (R * R ^ p * Δξ) +
            K₀ * (phaseLogMoment β R μ n p * (Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ)))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
          · rw [mul_assoc (K₀ * (β * phaseLogMoment β R μ n (p + 1)))]
            exact mul_le_mul_of_nonneg_left hmassf hKD
          · rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hfam hK₀0
      _ = _ := by rw [pow_succ]; ring
  -- sum the termwise bounds
  have hbound : HasSum (fun p : ℕ =>
      K₀ * (β ^ p / (p.factorial : ℝ) * (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1)) * Δξ +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p) * Δη +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1)))) *
          Δξ))
      (K₀ * (β * R * M' * Δξ + M * Δη + R * (β * M') * Δξ)) :=
    (((hb.mul_right Δξ).add (hc.mul_right Δη)).add (hd.mul_right Δξ)).mul_left K₀
  have hs := summable_familyCoeffSeries_terms n h k hk β hβ hξ hη hμ j
  have hs' := summable_familyCoeffSeries_terms n h k hk β hβ hξ' hη' hμ j
  have hsum : Summable fun p =>
      |familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hbound.summable
  unfold familyCoeffSeries
  rw [← (Summable.of_norm (by simpa [Real.norm_eq_abs] using hs')).tsum_sub
    (Summable.of_norm (by simpa [Real.norm_eq_abs] using hs))]
  have hn := norm_tsum_le_tsum_norm (f := fun p =>
    familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p)
    (by simpa [Real.norm_eq_abs] using hsum)
  simp only [Real.norm_eq_abs] at hn
  refine hn.trans ((Summable.tsum_le_tsum hterm hsum hbound.summable).trans ?_)
  rw [hbound.tsum_eq]
  unfold familyLipConst
  rw [← hK₀, ← hM, ← hM']
  have : K₀ * (β * R * M' * Δξ + M * Δη + R * (β * M') * Δξ) =
      K₀ * (2 * β * R * M' * Δξ + M * Δη) := by ring
  rw [this]
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg _ _ _ _ _
  have hM'0 : 0 ≤ M' := phaseLogMoment_nonneg _ _ _ _ _
  have hin : 2 * β * R * M' * Δξ + M * Δη ≤ (2 * β * R * M' + M) * (Δξ + Δη) := by
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * β * R) hM'0) hΔη0,
      mul_nonneg hM0 hΔξ0]
  calc K₀ * (2 * β * R * M' * Δξ + M * Δη) ≤ K₀ * ((2 * β * R * M' + M) * (Δξ + Δη)) :=
        mul_le_mul_of_nonneg_left hin hK₀0
    _ = _ := by ring

/-- **Ballwise Lipschitz continuity of the canonical unit-box coefficients** (every real `μ`). -/
theorem abs_familySpectralCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) (hRη' : mass cη' ≤ R) (μ : ℝ)
    (j : ℕ) :
    |familySpectralCoeff n h k β cξ' cη' μ j - familySpectralCoeff n h k β cξ cη μ j| ≤
      familyLipConst n k β μ R * (mass (cξ' - cξ) + mass (cη' - cη)) := by
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  by_cases hc : candidateExp h k μ
  · rw [familySpectralCoeff_eq_series' n h k hk β hβ hξ' hη', familySpectralCoeff_eq_series' n h k
      hk β hβ hξ hη]
    exact abs_familyCoeffSeries_sub_le n h k hk β hβ hξ hξ' hη hη' hRξ hRξ' hRη hRη'
      (candidateExp_pos hk hc) j
  · rw [familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ' hη' hc j,
      familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ hη hc j, sub_zero, abs_zero]
    exact mul_nonneg (familyLipConst_nonneg n k β hβ μ hR0)
      (add_nonneg (mass_nonneg _) (mass_nonneg _))

end Grammar
