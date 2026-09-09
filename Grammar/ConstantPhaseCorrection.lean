/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.ConstantPhaseLeading
import Grammar.SecondOrderQuotient
import Grammar.PopulationPositivity
import Grammar.PhasePosterior

/-!
# The constant-phase energy correction (unit 337; Astra #40 units 1–3)

For a constant fluctuation `ξ ≡ a`, write `A(a) = C(λ, m−1; a)` for the leading constant-phase
coefficient and `B(a) = C(λ, m−2; a)` (zero for `m = 1`) for the next one. The constant-phase
chart integral has two-term data uniformly in the multiplicity,
`log N (𝒵_N[η;a]/(N^{-λ}L^{m−1}) − A(a)) → B(a)` (`constPhase_twoTerm_chart`; isolated remainders of
the constant-phase Taylor tree), and the energy insertion transports `(A, B)` to
`(E, D) = ((λA + (a/2)A')/β, (λB − (m−1)A + (a/2)B')/β)` by the constant-phase transport in
derivative form. Hence (`constPhase_energy_correction_chart`)
```
log N · ( N 𝒵_N[K∘π η;a]/𝒵_N[η;a] − c₁(a) ) → c₂(a),
c₁(a) = λ/β + (a/2β) A'(a)/A(a),   c₂(a) = −(m−1)/β + (a/2β) (B'A − BA')(a)/A(a)²,
```
i.e. `c₂ = −(m−1)/β + (a/2β)(B/A)'(a)`: at `a = 0` this is the zero-phase correction `−(m−1)/β`, and
for `m = 1` it is `0`. The face factorisation `A(a) = J_{2λ}(a) · H` with `H` the phase-independent
face factor (`phaseFace_eq_mul`) and `J_{2λ}(a) > 0` give `A(a) > 0` under a positive face witness
(`phaseFace_pos`, `constPhase_coeff_pos`), so the division hypothesis is structural
(`constPhase_energy_correction_chart_of_witness`). Nothing is obtained by differentiating an
asymptotic expansion. Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The constant-phase second coefficient `C(λ, m−2; a)` (zero for `m = 1`). -/
noncomputable def constPhaseSecondCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cη : CoeffFamily (n + 1)) (a l : ℝ) : ℝ :=
  if 2 ≤ multCount (ratioExp h k) l then
    familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 2)
  else 0

/-- **Constant-phase two-term data**, uniformly in the multiplicity. -/
theorem constPhase_twoTerm_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l) :
    Tendsto (fun N => Real.log N * (origPhaseIntegral n h k β N 1 (fun _ => a) η /
        (N ^ (-l) * Real.log N ^ (multCount (ratioExp h k) l - 1)) -
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1)))
      atTop (𝓝 (constPhaseSecondCoeff n h k β cη a l)) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  obtain ⟨C, hC⟩ := thm_TaylorTree_coeffFamily n h k hk β hβ one_pos
    ((absSummableAt_one_iff _).2 (absSummable_constFamily a)) ((absSummableAt_one_iff _).2 hη)
  have hCeq : ∀ μ q, C μ q = familySpectralCoeff n h k β (constFamily a) cη μ q :=
    fun μ q => by rw [hC.coeff_eq, scale_one, scale_one]
  have hI : ∀ N, familyPhaseIntegralBox n h k β N 1 (constFamily a) cη =
      origPhaseIntegral n h k β N 1 (fun _ => a) η := fun N =>
    familyPhaseIntegralBox_eq_orig n h k β N 1 (fun u _ => evalF_constFamily a u) hev
  obtain ⟨hzero, hlead⟩ := constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt
  have hCz : ∀ q, multCount (ratioExp h k) l - 1 < q → C l q = 0 := fun q hq => by
    rw [hCeq]
    exact hzero q hq
  have hcut := cutoffExpansion_of_conclusion n h k β hC
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨i₀, hi₀⟩ := hatt
  obtain ⟨a₀, -, ha₀⟩ := ratio_mem_lattice k hk i₀ (h i₀)
  have hla : l = (a₀ : ℝ) / latticeQ k := by rw [← hi₀]; exact ha₀
  have hpred : ∀ m' : ℕ, m' < a₀ → ∀ j, C ((m' : ℝ) / latticeQ k) j = 0 := by
    intro m' hm' j
    apply hC.vanish
    intro hcand
    have hle := le_of_candidateExp h k hk hmin hcand
    rw [hla, div_le_div_iff_of_pos_right hQ'] at hle
    have : a₀ ≤ m' := by exact_mod_cast hle
    omega
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ ⟨i₀, hi₀⟩
  have hmn : multCount (ratioExp h k) l ≤ n + 1 := by
    have := multCount_le_card (ratioExp h k) l
    simpa using this
  rcases Nat.lt_or_ge (multCount (ratioExp h k) l) 2 with hm | hm
  · have hm1' : multCount (ratioExp h k) l = 1 := by omega
    have hz0 : ∀ q, 0 < q → C ((a₀ : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hCz q (by omega)
    have h1 := oneTerm_of_isolated hQ hcut hpred hz0
    rw [← hla] at h1
    unfold constPhaseSecondCoeff
    rw [hm1', if_neg (by omega)]
    refine h1.congr' (Eventually.of_forall fun N => ?_)
    dsimp only
    rw [hI N, hCeq, Nat.sub_self, pow_zero, mul_one]
  · obtain ⟨r, hr⟩ : ∃ r, multCount (ratioExp h k) l = r + 2 :=
      ⟨multCount (ratioExp h k) l - 2, by omega⟩
    have hr1 : r + 1 ≤ n := by omega
    have hz : ∀ q, r + 1 < q → C ((a₀ : ℝ) / latticeQ k) q = 0 := by
      intro q hq
      rw [← hla]
      exact hCz q (by omega)
    have h2 := twoTerm_of_isolated hQ hcut hpred hr1 hz
    rw [← hla] at h2
    have e1 : r + 2 - 1 = r + 1 := by omega
    have e2 : r + 2 - 2 = r := by omega
    unfold constPhaseSecondCoeff
    rw [hr, if_pos (by omega), e1, e2, ← hCeq, ← hCeq]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
    have hlogr : Real.log N ^ r ≠ 0 := pow_ne_zero _ hlog
    rw [hI N]
    field_simp
    ring

/-- **The constant-phase first logarithmic energy correction**: with `A(a) = C(λ,m−1;a) ≠ 0` and
`B(a) = C(λ,m−2;a)`,
`log N (N 𝒵_N[K∘π η;a]/𝒵_N[η;a] − (λ/β + (a/2β) A'/A)) → −(m−1)/β + (a/2β)(B'A − BA')/A²`. -/
theorem constPhase_energy_correction_chart (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hA : familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ≠ 0) :
    Tendsto (fun N => Real.log N * (N * (origPhaseIntegral n h k β N 1 (fun _ => a)
        (fun u => (∏ i, u i ^ (2 * k i)) * η u) /
          origPhaseIntegral n h k β N 1 (fun _ => a) η) -
        (l / β + a / (2 * β) *
          deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
            (multCount (ratioExp h k) l - 1)) a /
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1))))
      atTop (𝓝 (-((multCount (ratioExp h k) l : ℝ) - 1) / β + a / (2 * β) *
        (deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a *
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) -
          constPhaseSecondCoeff n h k β cη a l *
          deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
            (multCount (ratioExp h k) l - 1)) a) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2))
          := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  have hm1 : 1 ≤ multCount (ratioExp h k) l := multCount_pos _ _ hatt
  have hβ0 : β ≠ 0 := hβ.ne'
  obtain ⟨hzero, -⟩ := constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt
  -- two-term data for the denominator and the energy numerator
  have hZ := constPhase_twoTerm_chart n h k hk hβ a hη hηc hev hmin hatt
  have hminK := hmin_add_two_k h k hk hmin
  have hattK := hatt_add_two_k h k hk hatt
  have hmK : multCount (ratioExp (fun i => h i + 2 * k i) k) (l + 1) = multCount (ratioExp h k) l :=
    multCount_add_two_k h k hk l
  have hZK := constPhase_twoTerm_chart n (fun i => h i + 2 * k i) k hk hβ a hη hηc hev hminK hattK
  rw [hmK] at hZK
  -- transported coefficients
  have hAK := population_coeff_add_two_k_phase_deriv n h k hk hβ a hη hl0
    (multCount (ratioExp h k) l - 1)
  rw [hzero (multCount (ratioExp h k) l - 1 + 1) (by omega), mul_zero, sub_zero] at hAK
  have hBK : constPhaseSecondCoeff n (fun i => h i + 2 * k i) k β cη a (l + 1) =
      (l * constPhaseSecondCoeff n h k β cη a l -
        ((multCount (ratioExp h k) l : ℝ) - 1) *
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) +
        a / 2 * deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a) / β := by
    rcases Nat.lt_or_ge (multCount (ratioExp h k) l) 2 with hm2 | hm2
    · have hm1' : multCount (ratioExp h k) l = 1 := by omega
      simp only [constPhaseSecondCoeff, hmK, hm1', (by norm_num : ¬ (2 ≤ 1)), if_false, deriv_const]
      simp
    · obtain ⟨s, hs⟩ : ∃ s, multCount (ratioExp h k) l = s + 2 :=
        ⟨multCount (ratioExp h k) l - 2, by omega⟩
      have e1 : s + 2 - 1 = s + 1 := by omega
      have e2 : s + 2 - 2 = s := by omega
      simp only [constPhaseSecondCoeff, hmK, hs, e1, e2, (by omega : 2 ≤ s + 2), if_true]
      rw [population_coeff_add_two_k_phase_deriv n h k hk hβ a hη hl0 s]
      push_cast
      ring
  -- the quotient
  have hq := quotient_second_order hA hZ hZK
  rw [hAK, hBK] at hq
  refine (hq.congr' ?_).trans ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hpow : N ^ (-l) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hlog : Real.log N ^ (multCount (ratioExp h k) l - 1) ≠ 0 :=
      pow_ne_zero _ (Real.log_pos hN).ne'
    rw [origPhaseIntegral_monomial_shift n h k β N 1 (fun _ => a) η (fun i => 2 * k i),
      show l + 1 - l = (1 : ℝ) by ring, Real.rpow_one, mul_div_assoc, div_self hlog, mul_one]
    congr 2 <;> first | ring1 | linear_combination (l / β) * mul_inv_cancel₀ hA
  · rw [show (-((multCount (ratioExp h k) l : ℝ) - 1) / β + a / (2 * β) *
        (deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a *
          familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) -
          constPhaseSecondCoeff n h k β cη a l *
          deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
            (multCount (ratioExp h k) l - 1)) a) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2) =
        (familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) *
          ((l * constPhaseSecondCoeff n h k β cη a l -
            ((multCount (ratioExp h k) l : ℝ) - 1) *
              familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) +
            a / 2 * deriv (fun a => constPhaseSecondCoeff n h k β cη a l) a) / β) -
          (l * familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) +
            a / 2 * deriv (fun a => familySpectralCoeff n h k β (constFamily a) cη l
              (multCount (ratioExp h k) l - 1)) a) / β *
          constPhaseSecondCoeff n h k β cη a l) /
        familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) ^ 2 by
      linear_combination (((multCount (ratioExp h k) l : ℝ) - 1) / β) *
        mul_inv_cancel₀ (pow_ne_zero 2 hA)]

/-! ### Positivity of the constant-phase face functional -/

/-- The phase-independent face factor: `phaseFace = J_{2λ}(a) · phaseFaceFactor`. -/
noncomputable def phaseFaceFactor {d : ℕ} (h k : Fin (d + 1) → ℕ) (l : ℝ)
    (η : (Fin (d + 1) → ℝ) → ℝ) : ℝ :=
  1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) *
    (∫ u in unitBox (d + 1), η (faceProj h k l u) * residualWeight h k l u) /
    2 ^ (multCount (ratioExp h k) l - 1)

theorem phaseFace_eq_mul {d : ℕ} (h k : Fin (d + 1) → ℕ) (l β a : ℝ)
    (η : (Fin (d + 1) → ℝ) → ℝ) :
    phaseFace h k l β a η = phaseMoment β (2 * l) a * phaseFaceFactor h k l η := by
  unfold phaseFace phaseFaceFactor
  have : ∫ u in unitBox (d + 1), (η (faceProj h k l u) * phaseMoment β (2 * l) a) *
      residualWeight h k l u =
      phaseMoment β (2 * l) a *
        ∫ u in unitBox (d + 1), η (faceProj h k l u) * residualWeight h k l u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_unitBox _) fun u _ => ?_
    ring
  rw [this]
  ring

/-- **Positivity of the constant-phase face functional** under a positive face witness: the phase
moment is positive and the phase-independent factor is a positive multiple of the zero-phase face
functional. -/
theorem phaseFace_pos {d : ℕ} (h k : Fin (d + 1) → ℕ) (hk : ∀ i, 0 < k i) (l β a : ℝ)
    (hl : 0 < l) (hβ : 0 < β) (hmin : ∀ i, l ≤ ratioExp h k i) (η : (Fin (d + 1) → ℝ) → ℝ)
    (hηc : Continuous η) (hnn : ∀ u ∈ closedCube (d + 1), 0 ≤ η (faceProj h k l u))
    (u₁ : Fin (d + 1) → ℝ) (hu₁ : u₁ ∈ closedCube (d + 1)) (hpos : 0 < η (faceProj h k l u₁)) :
    0 < phaseFace h k l β a η := by
  rw [phaseFace_eq_mul]
  refine mul_pos (phaseMoment_pos β (2 * l) a hβ (by linarith)) ?_
  unfold phaseFaceFactor
  have hint : 0 < ∫ u in unitBox (d + 1), η (faceProj h k l u) * residualWeight h k l u := by
    have := amplitudeCoeff_pos d h k hk l β hl hβ hmin η hηc hnn u₁ hu₁ hpos
    unfold amplitudeCoeff at this
    exact pos_of_mul_pos_right this (faceLeadConst_pos h k hk l β hl hβ).le
  have hfac : (0 : ℝ) < 1 / (((multCount (ratioExp h k) l - 1).factorial : ℝ) *
      ∏ i, if ratioExp h k i = l then (k i : ℝ) else 1) := by
    refine one_div_pos.2 (mul_pos (by positivity) (Finset.prod_pos fun i _ => ?_))
    split_ifs
    · exact_mod_cast hk i
    · exact one_pos
  positivity

/-- The constant-phase leading coefficient is positive under a positive face witness. -/
theorem constPhase_coeff_pos (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {β : ℝ}
    (hβ : 0 < β) (a : ℝ) {cη : CoeffFamily (n + 1)} (hη : AbsSummable cη)
    {η : (Fin (n + 1) → ℝ) → ℝ} (hηc : Continuous η)
    (hev : ∀ u ∈ piBox (n + 1) (Ioc 0 1), evalF cη u = η u) {l : ℝ}
    (hmin : ∀ i, l ≤ ratioExp h k i) (hatt : ∃ i, ratioExp h k i = l)
    (hnn : ∀ u ∈ closedCube (n + 1), 0 ≤ η (faceProj h k l u))
    (u₁ : Fin (n + 1) → ℝ) (hu₁ : u₁ ∈ closedCube (n + 1)) (hpos : 0 < η (faceProj h k l u₁)) :
    0 < familySpectralCoeff n h k β (constFamily a) cη l (multCount (ratioExp h k) l - 1) := by
  have hl0 : 0 < l := by
    obtain ⟨i, hi⟩ := hatt
    rw [← hi]
    exact ratioExp_pos h k hk i
  rw [(constPhase_leadingCoeff n h k hk hβ a hη hηc hev hmin hatt).2]
  exact phaseFace_pos h k hk l β a hl0 hβ hmin η hηc hnn u₁ hu₁ hpos

end Grammar
