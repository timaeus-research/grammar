/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ChartCoefficientTensors
import Grammar.OneDimResolvedGeometry

/-!
# Polynomial observables on the line: series, jets and Taylor families (CCCVI)

Plan unit 8b (consult #93 A). A polynomial observable on `ℝ¹` is given by a finitely supported
coefficient family `f : CoeffFamily 1`, `P(u) = evalF f u = ∑_γ f_γ u^γ`. This unit supplies the
analytic data the certificates ask for:

* `polySeries f` — the formal power series `m ↦ f_m • (du)^{⊗m}` of `P`, with infinite radius, and
  `hasFPowerSeriesOnBall_poly : HasFPowerSeriesOnBall P (polySeries f) 0 ⊤`;
* `jetFamily_poly : jetFamily 0 P = f` — **the observable's Taylor family is its coefficient
  family** (in one variable every word has the same weight, so the weight component is the diagonal
  jet, and `HasFPowerSeriesOnBall.factorial_smul` identifies `D^mP(0)(e,…,e) = m!·f_m`);
* `absSummableAt_of_support` — finitely supported families are `b`-weighted ℓ¹;
* `deltaFamily`, `conv_deltaFamily` — the constant density `c = 1` has Taylor family `δ_0`, the
  unit for the Cauchy product.

Non-claims: nothing beyond polynomials; no measures or charts here.
-/

open Set Filter Topology

namespace Grammar

namespace OneDim

open CoeffFamily MonoRep

variable (f : CoeffFamily 1)

/-- The polynomial `P(u) = ∑_γ f_γ u^γ` on `ℝ¹`. -/
noncomputable def poly : Space → ℝ := evalF f

theorem mono_eq_pow (γ : Fin 1 → ℕ) (y : Space) : mono γ y = y 0 ^ γ 0 := by
  unfold mono
  rw [Fin.prod_univ_one]

/-- Multi-indices on `Fin 1` are natural numbers. -/
def degreeEquivOne : (Fin 1 → ℕ) ≃ ℕ where
  toFun γ := γ 0
  invFun m := fun _ => m
  left_inv γ := funext fun i => by rw [Fin.fin_one_eq_zero i]
  right_inv _ := rfl

variable {supp : Finset (Fin 1 → ℕ)} (hf : ∀ γ ∉ supp, f γ = 0)
include hf

theorem summable_term (u : Space) : Summable fun γ => f γ * mono γ u :=
  summable_of_ne_finset_zero (s := supp) fun γ hγ => by rw [hf γ hγ, zero_mul]

theorem poly_eq_sum (u : Space) : poly f u = ∑ γ ∈ supp, f γ * mono γ u :=
  tsum_eq_sum fun γ hγ => by rw [hf γ hγ, zero_mul]

theorem continuous_poly : Continuous (poly f) := by
  have : poly f = fun u => ∑ γ ∈ supp, f γ * mono γ u := funext (poly_eq_sum f hf)
  rw [this]
  refine continuous_finsetSum _ fun γ _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

theorem absSummableAt_of_support (b : ℝ) : AbsSummableAt f b :=
  summable_of_ne_finset_zero (s := supp) fun γ hγ => by rw [hf γ hγ, abs_zero, zero_mul]

omit hf

/-! ### The power series -/

/-- The formal power series of `P`: `m ↦ f_m • du^{⊗m}`. -/
noncomputable def polySeries : FormalMultilinearSeries ℝ Space ℝ :=
  fun m => f (fun _ => m) • monomialForm (fun _ : Fin m => (0 : Fin 1))

theorem polySeries_apply_diag (m : ℕ) (y : Space) :
    polySeries f m (fun _ => y) = f (fun _ => m) * y 0 ^ m := by
  unfold polySeries
  rw [smul_apply, monomialForm_apply, smul_eq_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

include hf in
theorem polySeries_eq_zero (m : ℕ) : polySeries f (m + (supp.sup fun γ => γ 0) + 1) = 0 := by
  unfold polySeries
  rw [hf, zero_smul]
  intro hmem
  have : m + (supp.sup fun γ => γ 0) + 1 ≤ supp.sup fun γ => γ 0 :=
    Finset.le_sup (f := fun γ : Fin 1 → ℕ => γ 0) hmem
  omega

include hf in
theorem radius_polySeries : (polySeries f).radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _
    ((supp.sup fun γ => γ 0) + 1) fun m => by
      rw [← add_assoc]
      exact polySeries_eq_zero f hf m

include hf in
/-- **The polynomial is represented by its series on the whole line.** -/
theorem hasFPowerSeriesOnBall_poly : HasFPowerSeriesOnBall (poly f) (polySeries f) 0 ⊤ where
  r_le := by rw [radius_polySeries f hf]
  r_pos := ENNReal.zero_lt_top
  hasSum := by
    intro y _
    rw [zero_add]
    have h := (summable_term f hf y).hasSum
    have h2 := (degreeEquivOne.symm.hasSum_iff).2 h
    refine h2.congr_fun fun m => ?_
    rw [polySeries_apply_diag]
    simp only [Function.comp, degreeEquivOne, Equiv.coe_fn_symm_mk, mono_eq_pow]

/-! ### The Taylor family -/

theorem weightOf_eq_const {m : ℕ} (w : Fin m → Fin 1) : weightOf w = fun _ => m := by
  funext i
  unfold weightOf
  rw [Finset.filter_true_of_mem fun j _ => Subsingleton.elim _ _, Finset.card_univ,
    Fintype.card_fin]

theorem weightFibre_eq_univ (m : ℕ) :
    weightFibre (r := m) (fun _ : Fin 1 => m) = Finset.univ := by
  ext w
  simp only [mem_weightFibre, Finset.mem_univ, iff_true]
  exact weightOf_eq_const w

theorem single_zero_one_eq : (Pi.single (0 : Fin 1) (1 : ℝ) : Space) = fun _ => 1 := by
  funext i
  rw [Fin.fin_one_eq_zero i, Pi.single_eq_same]

/-- In one variable the weight component is the diagonal jet at `e = 1`. -/
theorem weightComponent_eq_diag {m : ℕ} (A : JetForm Space m) :
    weightComponent A (fun _ => m) = A fun _ => fun _ => (1 : ℝ) := by
  rw [weightComponent_def, weightFibre_eq_univ, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, one_pow, Nat.cast_one, inv_one, one_mul,
    Fintype.sum_unique]
  unfold jetComponent
  congr 1
  funext j
  exact single_zero_one_eq

include hf in
/-- ★ **The Taylor family of the polynomial is its coefficient family.** -/
theorem jetFamily_poly : jetFamily 0 (poly f) = f := by
  funext bb
  obtain ⟨m, rfl⟩ : ∃ m, bb = fun _ => m := ⟨bb 0, funext fun i => by rw [Fin.fin_one_eq_zero i]⟩
  unfold jetFamily
  rw [Fin.prod_univ_one, Fin.sum_univ_one, weightComponent_eq_diag]
  have h := (hasFPowerSeriesOnBall_poly f hf).factorial_smul (fun _ => (1 : ℝ)) m
  rw [polySeries_apply_diag, one_pow, mul_one] at h
  unfold normalJet
  rw [← h, nsmul_eq_mul]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The constant density -/

/-- The Taylor family `δ_0` of the constant `1`. -/
noncomputable def deltaFamily (d : ℕ) : CoeffFamily d := fun γ => if γ = 0 then 1 else 0

theorem absSummableAt_deltaFamily (d : ℕ) (b : ℝ) : AbsSummableAt (deltaFamily d) b :=
  summable_of_ne_finset_zero (s := {0}) fun γ hγ => by
    rw [deltaFamily, if_neg (by simpa using hγ), abs_zero, zero_mul]

theorem conv_deltaFamily {d : ℕ} (e : CoeffFamily d) : CoeffFamily.conv (deltaFamily d) e = e := by
  funext γ
  unfold CoeffFamily.conv deltaFamily
  rw [Finset.sum_eq_single 0]
  · simp
  · intro α _ hα
    rw [if_neg hα, zero_mul]
  · intro h
    exact absurd (Finset.mem_Iic.2 fun i => Nat.zero_le (γ i)) h

theorem evalF_deltaFamily {d : ℕ} (u : Fin d → ℝ) : evalF (deltaFamily d) u = 1 := by
  unfold evalF
  rw [tsum_eq_single 0]
  · simp [deltaFamily, mono]
  · intro γ hγ
    rw [deltaFamily, if_neg hγ, zero_mul]

end OneDim

end Grammar
