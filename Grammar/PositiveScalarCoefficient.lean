/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SingleChartScalarAtlas

/-!
# Positive leading coefficients

Unit 4 of consult #77 (`tide-log/gpt6_bigpicture_v77.md`): a leading-term certificate may have
coefficient zero; the paper's theorem asserts a POSITIVE leading coefficient for the partition
function. When all ratios `(h_j+1)/(2k_j)` are minimal the box prefactor
`b^{Σh+n+1}(b^{2Σk})^{−λ}` equals `1` (`box_prefactor_of_all_minimal`), so a scalar-unit cell's
coefficient is `Γ(λ)/n! · ∏_j 1/(2k_j) · ∫_base β_w(z) q(z)^{−λ} A(z,0) dz`
(`ScalarUnitCell.coeff_of_all_minimal'`), and it is **strictly positive** as soon as `β_w ≥ 0` and
`A(·,0) ≥ 0` a.e. on the base and both are positive on a set of positive measure
(`ScalarUnitCell.coeff_pos_of_all_minimal`; positivity at one point is not enough for a measurable
base weight). For a symmetric cell every reflected orthant cell has the same coefficient
(`ScalarUnitCell.reflected_coeff_of_all_minimal`), so the two-sided integral has the certificate
with coefficient `2^{n+1}` times the orthant coefficient
  (`ScalarUnitCell.hasLeadingTerm_symIntegral`)
and, under the positivity hypotheses, the **genuine leading asymptotic**
`∫_base β_w · symScalarKernel ~ 2^{n+1} c · N^{−λ}(log N)^{m−1}` with `c > 0`
(`ScalarUnitCell.symIntegral_isEquivalent_of_all_minimal`). At atlas level, nonnegative tied
coefficients with one positive give a positive tied sum (`FiniteScalarUnitAtlas.tiedCoeff_pos`).

Non-claims: positivity is proved in the all-minimal case (the general face integral retains the
noncritical normal coordinates); nonnegativity of the data is a hypothesis (signed observables
excluded).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace Grammar

/-! ### The box prefactor in the all-minimal case -/

theorem box_prefactor_of_all_minimal {n : ℕ} (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) {l : ℝ}
    (hall : ∀ i, ratioExp h k i = l) {b : ℝ} (hb : 0 < b) :
    b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-l) = 1 := by
  have hi : ∀ i, ((h i : ℝ) + 1) = l * (2 * (k i : ℝ)) := fun i => by
    have := hall i
    unfold ratioExp at this
    have hk' : (2 * (k i : ℝ)) ≠ 0 := by
      have := hk i
      positivity
    rwa [div_eq_iff hk'] at this
  have hsum : ((∑ i, h i + (n + 1) : ℕ) : ℝ) = l * (2 * ∑ i, (k i : ℝ)) := by
    push_cast
    have : ∑ i, ((h i : ℝ) + 1) = ∑ i, (h i : ℝ) + (n + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    rw [← this, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hi i
  rw [← Real.rpow_natCast b (∑ i, h i + (n + 1)), ← Real.rpow_natCast b (2 * ∑ i, k i),
    ← Real.rpow_mul hb.le, ← Real.rpow_add hb, hsum]
  push_cast
  rw [show l * (2 * ∑ i, (k i : ℝ)) + 2 * (∑ i, (k i : ℝ)) * -l = 0 by ring, Real.rpow_zero]

/-! ### Positivity of the cell coefficient -/

namespace ScalarUnitCell

variable {t : ℕ} (c : ScalarUnitCell t)

/-- The face constant of a cell. -/
noncomputable def faceConst : ℝ := Real.Gamma c.lam / (c.n.factorial : ℝ) * ∏ i, 1 / (2 * (c.k
  i : ℝ))

theorem faceConst_pos : 0 < c.faceConst := by
  unfold faceConst
  refine mul_pos (div_pos (Real.Gamma_pos_of_pos c.lam_pos) (by exact_mod_cast c.n.factorial_pos))
    (Finset.prod_pos fun i _ => ?_)
  have := c.k_pos i
  positivity

/-- **The all-minimal coefficient with the prefactor removed**:
`coeff = Γ(λ)/n! ∏_j 1/(2k_j) · ∫_base β_w q^{−λ} A(·,0)`. -/
theorem coeff_of_all_minimal' (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
    c.coeff = c.faceConst * ∫ z in c.base, c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
  rw [c.coeff_of_all_minimal hall, box_prefactor_of_all_minimal c.h c.k c.k_pos hall c.b_pos,
    one_mul]
  rfl

/-- The coefficient integrand `β_w · q^{−λ} A(·,0)` is integrable on the base. -/
theorem integrable_coeffIntegrand :
    IntegrableOn (fun z => c.βw z * (c.q z ^ (-c.lam) * c.A z 0)) c.base := by
  have hbaseM : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
  have hcont : ContinuousOn (fun z => c.q z ^ (-c.lam) * c.A z 0) c.base := by
    refine ContinuousOn.mul (c.q_cont.continuousOn.rpow_const fun z hz => Or.inl (c.q_pos z hz).ne')
      ?_
    exact (c.A_cont.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨M, hM⟩ := c.base_compact.exists_bound_of_continuousOn hcont
  refine c.βw_int.bdd_mul (c := M) (hcont.aestronglyMeasurable hbaseM) ?_ |>.congr
    (Eventually.of_forall fun z => mul_comm _ _)
  exact (ae_restrict_iff' hbaseM).2 (Eventually.of_forall fun z hz => hM z hz)

/-- **Positivity of the coefficient** (all ratios minimal): nonnegative `β_w` and `A(·,0)` a.e.
  on the
base, both positive on a set of positive measure. -/
theorem coeff_pos_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
    (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.A z 0)
    (hpos : 0 < volume (c.base ∩ {z | 0 < c.βw z ∧ 0 < c.A z 0})) : 0 < c.coeff := by
  rw [c.coeff_of_all_minimal' hall]
  refine mul_pos c.faceConst_pos ?_
  have hbaseM : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
  have hnn : 0 ≤ᵐ[volume.restrict c.base] fun z => c.βw z * (c.q z ^ (-c.lam) * c.A z 0) := by
    filter_upwards [hβ, hA, (ae_restrict_iff' hbaseM).2
      (Eventually.of_forall fun z (hz : z ∈ c.base) => c.q_pos z hz)] with z h1 h2 h3
    exact mul_nonneg h1 (mul_nonneg (Real.rpow_pos_of_pos h3 _).le h2)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn c.integrable_coeffIntegrand]
  refine lt_of_lt_of_le hpos (measure_mono fun z hz => ?_)
  refine ⟨?_, hz.1⟩
  have hq := c.q_pos z hz.1
  exact (mul_pos hz.2.1 (mul_pos (Real.rpow_pos_of_pos hq _) hz.2.2)).ne'

/-! ### The symmetric cell -/

theorem reflect_zero {r : ℕ} (σ : Fin r → Bool) : reflect σ (0 : Fin r → ℝ) = 0 := by
  funext i
  simp [reflect]

/-- Every reflected orthant cell has the same all-minimal coefficient. -/
theorem reflected_coeff_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
    (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).coeff = c.coeff := by
  have hall' : ∀ i, ratioExp (c.reflected σ).h (c.reflected σ).k i = (c.reflected σ).lam := hall
  rw [(c.reflected σ).coeff_of_all_minimal' hall', c.coeff_of_all_minimal' hall]
  congr 1
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  change c.βw z * (c.q z ^ (-c.lam) * c.A z (reflect σ 0)) = _
  rw [reflect_zero]

theorem reflected_lam (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).lam = c.lam := rfl

theorem reflected_mult (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).mult = c.mult := rfl

/-- **The certificate of the symmetric integral**: `2^{n+1}` times the orthant coefficient. -/
theorem hasLeadingTerm_symIntegral (hall : ∀ i, ratioExp c.h c.k i = c.lam) :
    HasLeadingTerm c.symIntegral ((2 : ℝ) ^ (c.n + 1) * c.coeff) c.lam (c.mult - 1) := by
  have h := c.symAtlas.hasLeadingTerm_of_extremal c.lam (c.mult - 1) (fun _ => le_rfl)
    (fun _ _ => le_rfl)
  have htied : c.symAtlas.tied c.lam (c.mult - 1) = Finset.univ :=
    Finset.filter_true_of_mem fun _ _ => ⟨rfl, rfl⟩
  rw [htied] at h
  have hcard : Fintype.card c.symAtlas.ι = 2 ^ (c.n + 1) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Fin (c.n + 1) → Bool) = _
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hsum : ∑ σ : c.symAtlas.ι, (c.symAtlas.cell σ).coeff = (2 : ℝ) ^ (c.n + 1) * c.coeff := by
    have : ∀ σ : c.symAtlas.ι, (c.symAtlas.cell σ).coeff = c.coeff := fun σ =>
      c.reflected_coeff_of_all_minimal hall σ
    simp only [this, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  rwa [hsum] at h

/-- **The genuine leading asymptotic of a symmetric all-minimal cell** with nonnegative, somewhere
positive data: `∫_base β_w · symScalarKernel ~ 2^{n+1} c · N^{−λ}(log N)^{m−1}`, `c > 0`. -/
theorem symIntegral_isEquivalent_of_all_minimal (hall : ∀ i, ratioExp c.h c.k i = c.lam)
    (hβ : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.βw z)
    (hA : ∀ᵐ z ∂volume.restrict c.base, 0 ≤ c.A z 0)
    (hpos : 0 < volume (c.base ∩ {z | 0 < c.βw z ∧ 0 < c.A z 0})) :
    0 < (2 : ℝ) ^ (c.n + 1) * c.coeff ∧
      c.symIntegral ~[atTop] fun N => (2 : ℝ) ^ (c.n + 1) * c.coeff *
        powLogScale c.lam (c.mult - 1) N := by
  have hc : 0 < (2 : ℝ) ^ (c.n + 1) * c.coeff :=
    mul_pos (by positivity) (c.coeff_pos_of_all_minimal hall hβ hA hpos)
  exact ⟨hc, (c.hasLeadingTerm_symIntegral hall).isEquivalent hc.ne'⟩

end ScalarUnitCell

/-- **Positive tied sums**: nonnegative tied coefficients with one positive. -/
theorem FiniteScalarUnitAtlas.tiedCoeff_pos {t : ℕ} {Z : ℝ → ℝ} (At : FiniteScalarUnitAtlas t Z)
    (lam₀ : ℝ) (k₀ : ℕ) (hnn : ∀ i ∈ At.tied lam₀ k₀, 0 ≤ (At.cell i).coeff)
    (hex : ∃ i ∈ At.tied lam₀ k₀, 0 < (At.cell i).coeff) :
    0 < ∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff :=
  Finset.sum_pos' hnn hex

end Grammar
