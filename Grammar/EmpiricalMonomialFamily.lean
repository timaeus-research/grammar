/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.EmpiricalFamilyDepth
import Grammar.EmpiricalLeadingConsistency
import Grammar.SmoothFiniteUniqueness

/-!
# The monomial amplitude families and the shifted population coefficients (§20, generating identity)

The `r`-th term of the exponential series `η e^{τζ} = Σ_r τ^r η ζ^r / r!` is the monomial family
`A_r(τ, v) = τ^r η(v) ζ(v)^r` (`expTermFam`).  It is a jointly smooth amplitude family with the jet
bound `|∂^m A_r(τ, ·)| ≤ C r! (1+τ)^{|p|} e^{τ}` (`exists_famJetBound_expTermFam`), so the family
depth engine applies at the SAME depth `p` as the empirical coefficient.  Its integral is the
population integral with the monomial absorbed into the weight, times `N^{r/2}`
(`integral_expTermFam`), and by uniqueness of cutoff expansions its depth-`p` coefficient at
`(μ, q)`
is the canonical population coefficient at the shifted exponent `μ + r/2`
(★★ `empCoeffAtDepthFam_expTermFam_eq`):

  `empCoeffAtDepthFam (τ^r η ζ^r) h k p μ q = empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q`.

The half-integer shift lives inside the Mellin moment and never changes the integer cutoff `L`.
Also: the exponent shift of a spectral sum (`absSpectralSum_shift`), the vanishing of the
population coefficients below `r/2` for the shifted weight, and monomial absorption for the
canonical coefficients (`empCoeff_monomial_absorb`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

variable {d : ℕ} {η ζ : (Fin d → ℝ) → ℝ} {h k p : Fin d → ℕ}

/-! ### The monomial family -/

theorem contDiff_prod_pow (k : Fin d → ℕ) (s : Finset (Fin d)) :
    ContDiff ℝ ∞ fun v : Fin d → ℝ => ∏ i ∈ s, v i ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact contDiff_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((contDiff_apply ℝ ℝ a).pow _).mul ih

/-- The monomial `v ↦ v^k` is smooth. -/
theorem contDiff_mono (k : Fin d → ℕ) : ContDiff ℝ ∞ (mono k) :=
  contDiff_prod_pow k Finset.univ

/-- The monomial amplitude family `τ^r η ζ^r`. -/
noncomputable def expTermFam (η ζ : (Fin d → ℝ) → ℝ) (r : ℕ) (τ : ℝ) (v : Fin d → ℝ) : ℝ :=
  τ ^ r * (η v * ζ v ^ r)

theorem contDiff_expTermFam_joint (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (r : ℕ) :
    ContDiff ℝ ∞ fun z : ℝ × (Fin d → ℝ) => expTermFam η ζ r z.1 z.2 :=
  (contDiff_fst.pow r).mul ((hη.comp contDiff_snd).mul ((hζ.comp contDiff_snd).pow r))

/-- The monomial family satisfies the jet bound with `M' = 1`: `τ^r ≤ r! e^τ`. -/
theorem exists_famJetBound_expTermFam (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ) (r : ℕ)
    (p : Fin d → ℕ) : ∃ C : ℝ, FamJetBound (expTermFam η ζ r) p 1 C 1 := by
  obtain ⟨M, hM⟩ := exists_rect_bound (hη.mul (hζ.pow r)) p 1
  refine ⟨|M| * r.factorial, fun m hm τ hτ v hv => ?_⟩
  have hpd : pdMulti m (List.finRange d) (expTermFam η ζ r τ) v =
      τ ^ r * pdMulti m (List.finRange d) (fun v => η v * ζ v ^ r) v :=
    congrFun (pdMulti_const_mul (τ ^ r) (fun v => η v * ζ v ^ r) m (List.finRange d)) v
  rw [hpd, abs_mul, abs_of_nonneg (pow_nonneg hτ r)]
  have h1 : |pdMulti m (List.finRange d) (fun v => η v * ζ v ^ r) v| ≤ |M| :=
    (hM m hm v (mem_closedBox.1 hv)).trans (le_abs_self M)
  have h2 : τ ^ r ≤ r.factorial * exp τ := by
    have := Real.pow_div_factorial_le_exp τ hτ r
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h3 : (1 : ℝ) ≤ (1 + τ) ^ (∑ i, p i) := one_le_pow₀ (by linarith)
  calc τ ^ r * |pdMulti m (List.finRange d) (fun v => η v * ζ v ^ r) v|
      ≤ (r.factorial * exp τ) * |M| := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    _ = |M| * r.factorial * 1 * exp (1 * τ) := by rw [one_mul]; ring
    _ ≤ |M| * r.factorial * (1 + τ) ^ (∑ i, p i) * exp (1 * τ) := by gcongr

/-- The integral of the monomial family at the coupling is `N^{r/2}` times the population integral
with the monomial absorbed into the weight `h + r k`. -/
theorem integral_expTermFam (r : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    ∫ v in box (Fin d) 1, expTermFam η ζ r (coupling k N v) v * mono h v *
        exp (-N * mono (fun i => 2 * k i) v) =
      N ^ ((r : ℝ) / 2) *
        empIntegral (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k N := by
  unfold empIntegral
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
  have hs : Real.sqrt N ^ r = N ^ ((r : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN]
    congr 1
    ring
  have hm : mono k v ^ r * mono h v = mono (fun i => h i + r * k i) v := by
    rw [mono_pow, mono_mul_mono]
    congr 1
    funext i
    ring
  unfold expTermFam fieldFam coupling
  simp only [mul_zero, exp_zero, mul_one]
  rw [mul_pow, hs, ← hm]
  ring

/-! ### The exponent shift of a spectral sum -/

/-- `N^s · Σ_{μ < L+s} c_μ N^{−μ} P_μ(log N) = Σ_{μ < L} c_{μ+s} N^{−μ} P_{μ+s}(log N)` for a
lattice shift `s` when the coefficients vanish below `s`. -/
theorem absSpectralSum_shift {Q D : ℕ} (hQ : 0 < Q) {c : ℝ → ℕ → ℝ} {s : ℝ}
    (hs : ∃ m₀ : ℕ, s = (m₀ : ℝ) / Q) (hvan : ∀ μ, μ < s → ∀ q, c μ q = 0) (L : ℝ) {N : ℝ}
    (hN : 0 < N) :
    N ^ s * absSpectralSum Q D c (L + s) N =
      absSpectralSum Q D (fun μ q => c (μ + s) q) L N := by
  obtain ⟨m₀, rfl⟩ := hs
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  unfold absSpectralSum
  have hsub : (latticeBelow Q L).image (· + (m₀ : ℝ) / Q) ⊆ latticeBelow Q (L + m₀ / Q) := by
    intro μ hμ
    obtain ⟨μ', hμ', rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨⟨m, hm⟩, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ'
    have heq : μ' + (m₀ : ℝ) / Q = ((m + m₀ : ℕ) : ℝ) / Q := by
      rw [hm]; push_cast; ring
    rw [heq]
    exact mem_latticeBelow hQ (by rw [← heq]; linarith)
  have hzero : ∀ μ ∈ latticeBelow Q (L + m₀ / Q),
      μ ∉ (latticeBelow Q L).image (· + (m₀ : ℝ) / Q) →
      N ^ (-μ) * ∑ j ∈ Finset.range (D + 1), c μ j * Real.log N ^ j = 0 := by
    intro μ hμ hnot
    obtain ⟨⟨m, hm⟩, hlt⟩ := (mem_latticeBelow_iff hQ).1 hμ
    by_cases hlt' : μ < (m₀ : ℝ) / Q
    · rw [Finset.sum_eq_zero fun j _ => by rw [hvan μ hlt' j, zero_mul], mul_zero]
    · exfalso
      apply hnot
      push Not at hlt'
      have hmm : m₀ ≤ m := by
        have : (m₀ : ℝ) ≤ m := (div_le_div_iff_of_pos_right hQ').1 (hm ▸ hlt')
        exact_mod_cast this
      refine Finset.mem_image.2 ⟨((m - m₀ : ℕ) : ℝ) / Q, mem_latticeBelow hQ ?_, ?_⟩
      · rw [Nat.cast_sub hmm, sub_div]
        rw [hm] at hlt
        linarith
      · rw [Nat.cast_sub hmm, sub_div, hm]
        ring
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun x _ y _ hxy => add_right_cancel hxy), Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← mul_assoc, ← Real.rpow_add hN]
  congr 2
  ring

/-! ### Vanishing below `r/2` for the shifted weight -/

/-- The shifted weight `h + r k` is box-leading at `r/2` with multiplicity `0`. -/
theorem boxLeading_shift (h k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℕ) :
    BoxLeading (fun i => h i + r * k i) k ((r : ℝ) / 2) 0 := by
  have hlt : ∀ i, (r : ℝ) / 2 < ratioExp (fun i => h i + r * k i) k i := by
    intro i
    unfold ratioExp
    have hki : (0 : ℝ) < k i := by exact_mod_cast hk i
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    nlinarith [hki]
  refine ⟨fun i => (hlt i).le, ?_⟩
  unfold multCount
  rw [Finset.sum_eq_zero fun i _ => by rw [if_neg (hlt i).ne']]

theorem empCoeff_shift_eq_zero_of_lt (hk : ∀ i, 0 < k i) (r : ℕ) {μ : ℝ} (hμ : μ < (r : ℝ) / 2)
    (q : ℕ) :
    empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k μ q = 0 :=
  empCoeff_eq_zero_of_boxLeading_lt (fun i => h i + r * k i) k hk (boxLeading_shift h k hk r) hμ q

/-! ### The identification -/

/-- ★★ **The depth-`p` coefficient of the monomial family is the canonical population coefficient
at the shifted exponent**: for `μ` on the lattice below the cutoff `L` and `q ≤ d − 1`,
`empCoeffAtDepthFam (τ^r η ζ^r) h k p μ q = empCoeff (η ζ^r) 0 (h + r k) k (μ + r/2) q`. -/
theorem empCoeffAtDepthFam_expTermFam_eq (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) {L : ℕ} (hL : 0 < L) (hp : ∀ i, p i + h i = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i) (r : ℕ) {μ : ℝ} (hμ : μ ∈ latticeBelow (Qamb k) L) {q : ℕ}
    (hq : q ≤ d - 1) :
    empCoeffAtDepthFam (expTermFam η ζ r) h k p μ q =
      empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k
        (μ + r / 2) q := by
  have hQ := Qamb_pos k hk
  obtain ⟨C, hC⟩ := exists_famJetBound_expTermFam hη hζ r p
  obtain ⟨K, hK⟩ := empirical_expansion_at_depth_fam h k p (contDiff_expTermFam_joint hη hζ r) hC
    hk hL hp hp0
  set Z : ℝ → ℝ := fun N => N ^ ((r : ℝ) / 2) *
    empIntegral (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k N with hZ
  have h₁ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (empCoeffAtDepthFam (expTermFam η ζ r) h k p) L N| ≤
      K * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    rw [hZ]
    simp only
    rw [← integral_expTermFam r (by linarith)]
    exact hK N hN
  have hcut := emp_cutoffExpansion (η := fun v => η v * ζ v ^ r) (ζ := fun _ => 0)
    (h := fun i => h i + r * k i) (hη.mul (hζ.pow r)) contDiff_const hk
  obtain ⟨K', hK'⟩ := hcut ((L : ℝ) + r / 2) (by positivity)
  have hr2 : ∃ m₀ : ℕ, (r : ℝ) / 2 = (m₀ : ℝ) / Qamb k := by
    refine ⟨r * ∏ i, k i, ?_⟩
    unfold Qamb
    have : (0 : ℝ) < ∏ i, (k i : ℝ) := Finset.prod_pos fun i _ => by exact_mod_cast hk i
    push_cast
    field_simp
  have h₂ : ∀ᶠ N in atTop, |Z N - absSpectralSum (Qamb k) (d - 1)
      (fun μ' q' => empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k
        (μ' + r / 2) q') L N| ≤
      K' * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
    filter_upwards [hK', eventually_ge_atTop (1 : ℝ)] with N hN hN1
    have hN0 : 0 < N := by linarith
    rw [← absSpectralSum_shift hQ hr2 (fun μ' hμ' q' => empCoeff_shift_eq_zero_of_lt hk r hμ' q')
      L hN0, hZ]
    simp only
    rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
    calc N ^ ((r : ℝ) / 2) * |empIntegral (fun v => η v * ζ v ^ r) (fun _ => 0)
          (fun i => h i + r * k i) k N - absSpectralSum (Qamb k) (d - 1)
            (empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k)
            (L + r / 2) N|
        ≤ N ^ ((r : ℝ) / 2) *
            (K' * (N ^ (-((L : ℝ) + r / 2)) * (1 + Real.log N) ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hN0.le _)
      _ = K' * (N ^ (-(L : ℝ)) * (1 + Real.log N) ^ (d - 1)) := by
          rw [show N ^ ((r : ℝ) / 2) *
              (K' * (N ^ (-((L : ℝ) + r / 2)) * (1 + Real.log N) ^ (d - 1))) =
              K' * ((N ^ ((r : ℝ) / 2) * N ^ (-((L : ℝ) + r / 2))) *
                (1 + Real.log N) ^ (d - 1)) by ring, ← Real.rpow_add hN0]
          congr 3
          ring
  exact finite_coeff_unique hQ h₁ h₂ μ hμ q hq

/-- **Monomial absorption for the canonical population coefficients**: the coefficient of the
amplitude `η (u^k ζ)^r` at weight `h` is the coefficient of `η ζ^r` at weight `h + r k`. -/
theorem empCoeff_monomial_absorb (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i) (r : ℕ) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / Qamb k) {q : ℕ}
    (hq : q ≤ d - 1) :
    empCoeff (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k μ q =
      empCoeff (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k μ q := by
  have hint : empIntegral (fun v => η v * (mono k v * ζ v) ^ r) (fun _ => 0) h k =
      empIntegral (fun v => η v * ζ v ^ r) (fun _ => 0) (fun i => h i + r * k i) k := by
    funext N
    unfold empIntegral
    refine setIntegral_congr_fun (measurableSet_box 1) fun v _ => ?_
    have hm : mono k v ^ r * mono h v = mono (fun i => h i + r * k i) v := by
      rw [mono_pow, mono_mul_mono]
      congr 1
      funext i
      ring
    unfold fieldFam
    simp only [mul_zero, exp_zero, mul_one]
    rw [mul_pow, ← hm]
    ring
  have hcut := emp_cutoffExpansion (η := fun v => η v * ζ v ^ r) (ζ := fun _ => 0)
    (h := fun i => h i + r * k i) (hη.mul (hζ.pow r)) contDiff_const hk
  rw [← hint] at hcut
  have hηζ : ContDiff ℝ ∞ fun v => η v * (mono k v * ζ v) ^ r :=
    hη.mul (((contDiff_mono k).mul hζ).pow r)
  exact (empCoeff_unique hηζ contDiff_const hk hcut hμ hq).symm

end SmoothEngine

end Grammar
