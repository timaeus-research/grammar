/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SymmetricVariableUnitCells
import Grammar.MixedExponentExample

/-!
# Variable-unit cell regressions (CCLVII)

Direct smoke tests of the variable-unit cells (CCLVI) on hand-built cells with a one-point base
and amplitude one:

* `∫_{[−1,1]²} e^{−N (1+y²) x² y⁴} ~ 2Γ(1/4) N^{−1/4}`: the unit `1+y²` frozen on the minimal face
  `y = 0` is `1`, so the constant of the plain `x²y⁴` example (CCLI) is unchanged
  (`VarRegression.A.integral_isEquivalent`);
* `∫_{[−1,1]²} e^{−N (1+x²+y²) x² y⁴} ~ Γ(1/4) · I · N^{−1/4}` with
  `I = ∫₀¹ x^{−1/2} (1+x²)^{−1/4} dx ≈ 1.9234`: the unit frozen on the minimal face keeps its
  dependence on the residual coordinate `x`, so the constant `Γ(1/4) I ≈ 6.97` differs from the
  value `2Γ(1/4) ≈ 7.25` that freezing the unit at the origin would give
  (`VarRegression.B.integral_isEquivalent`, `VarRegression.B.I_pos`);
* `∫_{[−1,1]³} e^{−N x² y⁴ z⁴} ~ Γ(1/4) N^{−1/4} log N`: multiplicity two
  (`VarRegression.C.integral_isEquivalent`).

The cells are `pointCell`: base `Fin 0 → ℝ` (a point of volume one), weight one, amplitude one,
and a continuous positive unit of the normal coordinates; the symmetric integral of the cell is the
integral over the box `(−b,b]^{r}` and its coefficient is the reflection sum of the residual face
coefficients (`pointCell_symIntegral`, `pointCell_reflected_coeff`).
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-! ### Boxes and the one-point base -/

/-- `(−b,b]^r` and `[−b,b]^r` agree almost everywhere. -/
theorem piBox_Ioc_ae_eq_Icc (r : ℕ) (b : ℝ) :
    (piBox r (Ioc (-b) b) : Set (Fin r → ℝ)) =ᵐ[volume] piBox r (Icc (-b) b) := by
  unfold piBox
  rw [volume_pi]
  exact Measure.pi_Ioc_ae_eq_pi_Icc

/-- The one-point space `Fin 0 → ℝ` has volume one. -/
theorem volume_univ_fin_zero : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
  rw [volume_pi]
  exact Measure.pi_empty_univ _

/-- Integration over the one-point space evaluates at the point. -/
theorem integral_fin_zero (f : (Fin 0 → ℝ) → ℝ) :
    ∫ z in (univ : Set (Fin 0 → ℝ)), f z = f default := by
  rw [Measure.restrict_univ, integral_unique, measureReal_def, volume_univ_fin_zero,
    ENNReal.toReal_one, one_smul]
  congr 1
  exact Subsingleton.elim _ _

/-! ### The point cell -/

section PointCell

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ j, 0 < k j) (b : ℝ) (hb : 0 < b)
  (u : (Fin (n + 1) → ℝ) → ℝ) (hu : Continuous u)
  (hu_pos : ∀ v ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) b, 0 < u v)

/-- **A variable-unit cell over a one-point base** with amplitude one and weight one. -/
noncomputable def pointCell : VarUnitCell 0 where
  n := n
  h := h
  k := k
  k_pos := hk
  b := b
  b_pos := hb
  A := fun _ _ => 1
  A_cont := continuous_const
  base := univ
  base_compact := isCompact_univ
  βw := fun _ => 1
  βw_int := integrableOn_const (C := (1 : ℝ))
    (by rw [volume_univ_fin_zero]; exact ENNReal.one_ne_top)
  u := fun _ v => u v
  u_cont := hu.comp continuous_snd
  u_pos := fun _ _ v hv => hu_pos v hv

theorem pointCell_lam : (pointCell n h k hk b hb u hu hu_pos).lam = minRatio h k := rfl

theorem pointCell_mult :
    (pointCell n h k hk b hb u hu hu_pos).mult = multCount (ratioExp h k) (minRatio h k) := rfl

/-- The symmetric integral of the point cell is the box integral. -/
theorem pointCell_symIntegral (N : ℝ) :
    (pointCell n h k hk b hb u hu hu_pos).symIntegral N =
      ∫ v in piBox (n + 1) (Ioc (-b) b),
        (∏ i, |v i| ^ h i) * Real.exp (-(u v * N * ∏ i, v i ^ (2 * k i))) := by
  change ∫ z in (univ : Set (Fin 0 → ℝ)),
    (1 : ℝ) * symVarKernel n h k b (fun _ v => u v) (fun _ _ => 1) z N = _
  rw [integral_fin_zero, one_mul]
  unfold symVarKernel
  simp only [one_mul]

/-- The reflected coefficients of the point cell: the residual face integral of `u^{−λ}`. -/
theorem pointCell_reflected_coeff (σ : Fin (n + 1) → Bool) :
    ((pointCell n h k hk b hb u hu hu_pos).reflected σ).coeff =
      b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp h k a = minRatio h k),
          (residualExponent h k (minRatio h k) a + 1)) *
        (faceLeadConst h k (minRatio h k) 1 *
          ∫ w in unitBox (n + 1),
            u (reflect σ (b • faceProj h k (minRatio h k) w)) ^ (-(minRatio h k)) *
              residualWeight h k (minRatio h k) w) := by
  refine (VarUnitCell.reflected_coeff_eq (pointCell n h k hk b hb u hu hu_pos) σ).trans ?_
  change ∫ z in (univ : Set (Fin 0 → ℝ)), (1 : ℝ) *
    (b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp h k a = minRatio h k),
        (residualExponent h k (minRatio h k) a + 1)) *
      (faceLeadConst h k (minRatio h k) 1 *
        ∫ w in unitBox (n + 1),
          (1 : ℝ) * u (reflect σ (b • faceProj h k (minRatio h k) w)) ^ (-(minRatio h k)) *
            residualWeight h k (minRatio h k) w)) = _
  rw [integral_fin_zero, one_mul]
  simp only [one_mul]

end PointCell

namespace VarRegression

/-! ### Shared exponent data for `K = x² y⁴` -/

/-- The Jacobian exponents `(0, 0)`. -/
def hexp : Fin 2 → ℕ := ![0, 0]

/-- The phase half-exponents `(1, 2)`: `x² y⁴`. -/
def kexp : Fin 2 → ℕ := ![1, 2]

theorem kexp_pos : ∀ j, 0 < kexp j := by
  intro j
  fin_cases j <;> simp [kexp]

theorem ratioExp_zero : ratioExp hexp kexp 0 = 1 / 2 := by norm_num [ratioExp, hexp, kexp]

theorem ratioExp_one : ratioExp hexp kexp 1 = 1 / 4 := by norm_num [ratioExp, hexp, kexp]

theorem minRatio_eq : minRatio hexp kexp = 1 / 4 := by
  apply le_antisymm
  · exact (Finset.inf'_le (ratioExp hexp kexp) (Finset.mem_univ 1)).trans_eq ratioExp_one
  · refine Finset.le_inf' _ _ fun i _ => ?_
    fin_cases i <;> norm_num [ratioExp, hexp, kexp]

theorem multCount_eq : multCount (ratioExp hexp kexp) (1 / 4) = 1 := by
  unfold multCount
  rw [Fin.sum_univ_two, ratioExp_zero, ratioExp_one]
  norm_num

/-- The face constant `Γ(1/4)/0! · 1/(2·2)`. -/
theorem faceLeadConst_eq : faceLeadConst hexp kexp (1 / 4) 1 = Real.Gamma (1 / 4) / 4 := by
  unfold faceLeadConst
  rw [multCount_eq, Fin.prod_univ_two, ratioExp_zero, ratioExp_one]
  norm_num [kexp]
  ring

theorem faceProj_zero (w : Fin 2 → ℝ) : faceProj hexp kexp (1 / 4) w 0 = w 0 := by
  unfold faceProj
  rw [if_neg]
  rw [ratioExp_zero]
  norm_num

theorem faceProj_one (w : Fin 2 → ℝ) : faceProj hexp kexp (1 / 4) w 1 = 0 := by
  unfold faceProj
  rw [if_pos ratioExp_one]

/-- The residual weight `x^{−1/2}`. -/
theorem residualWeight_eq (w : Fin 2 → ℝ) :
    residualWeight hexp kexp (1 / 4) w = w 0 ^ (-(1 / 2 : ℝ)) := by
  unfold residualWeight
  rw [Fin.prod_univ_two, if_neg (by rw [ratioExp_zero]; norm_num), if_pos ratioExp_one, mul_one]
  norm_num [hexp, kexp]

theorem integral_Ioc_one : ∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp

/-! ### `K = (1 + y²) x² y⁴`: the face unit is `1` -/

namespace A

/-- The unit `1 + y²`. -/
def uA (v : Fin 2 → ℝ) : ℝ := 1 + v 1 ^ 2

theorem uA_cont : Continuous uA := continuous_const.add ((continuous_apply 1).pow 2)

theorem uA_pos (v : Fin 2 → ℝ) : 0 < uA v := by
  unfold uA
  positivity

/-- The unit on the minimal face `y = 0` is `1`. -/
theorem uA_face (σ : Fin 2 → Bool) (w : Fin 2 → ℝ) :
    uA (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) = 1 := by
  unfold uA reflect
  simp only [one_smul]
  rw [faceProj_one, mul_zero]
  norm_num

theorem face_integral (σ : Fin 2 → Bool) :
    ∫ w in unitBox 2, uA (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) ^ (-(1 / 4 : ℝ)) *
      residualWeight hexp kexp (1 / 4) w = 2 := by
  have hpt : ∀ w ∈ unitBox 2,
      uA (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) ^ (-(1 / 4 : ℝ)) *
        residualWeight hexp kexp (1 / 4) w =
      ∏ a, (![fun t : ℝ => t ^ (-(1 / 2 : ℝ)), fun _ => (1 : ℝ)] : Fin 2 → ℝ → ℝ) a (w a) := by
    intro w _
    rw [uA_face, Real.one_rpow, one_mul, residualWeight_eq, Fin.prod_univ_two]
    simp
  rw [setIntegral_congr_fun (measurableSet_unitBox 2) hpt, integral_unitBox_prod,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_Ioc_rpow (by norm_num), integral_Ioc_one]
  norm_num

/-- The cell. -/
noncomputable def cell : VarUnitCell 0 :=
  pointCell 1 hexp kexp kexp_pos 1 one_pos uA uA_cont fun v _ => uA_pos v

theorem cell_lam : cell.lam = 1 / 4 := minRatio_eq

theorem cell_mult : cell.mult = 1 := by
  change multCount (ratioExp hexp kexp) (minRatio hexp kexp) = 1
  rw [minRatio_eq, multCount_eq]

theorem coeff_sum :
    ∑ σ : Fin (cell.n + 1) → Bool, (cell.reflected σ).coeff = 2 * Real.Gamma (1 / 4) := by
  have hσ : ∀ σ : Fin (cell.n + 1) → Bool,
      (cell.reflected σ).coeff = Real.Gamma (1 / 4) / 4 * 2 := by
    intro σ
    refine (pointCell_reflected_coeff 1 hexp kexp kexp_pos 1 one_pos uA uA_cont
      (fun v _ => uA_pos v) σ).trans ?_
    rw [minRatio_eq, Real.one_rpow, one_mul, faceLeadConst_eq]
    congr 1
    exact face_integral σ
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, show cell.n = 1 from rfl]
  push_cast
  ring

/-- ★ `∫_{[−1,1]²} e^{−N (1+y²) x² y⁴} ~ 2Γ(1/4) N^{−1/4}`: the unit frozen on the minimal face
`y = 0` is `1`, and the constant of the plain `x²y⁴` example is unchanged. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ v in piBox 2 (Icc (-1) 1),
        Real.exp (-N * ((1 + v 1 ^ 2) * (v 0 ^ 2 * v 1 ^ 4)))) ~[atTop]
      fun N => 2 * Real.Gamma (1 / 4) * N ^ (-(1 / 4 : ℝ)) := by
  have h := cell.hasLeadingTerm_symIntegral
  rw [coeff_sum, cell_lam, cell_mult, Nat.sub_self] at h
  have hZ : cell.symIntegral = fun N => ∫ v in piBox 2 (Icc (-1) 1),
        Real.exp (-N * ((1 + v 1 ^ 2) * (v 0 ^ 2 * v 1 ^ 4))) := by
    funext N
    refine (pointCell_symIntegral 1 hexp kexp kexp_pos 1 one_pos uA uA_cont
      (fun v _ => uA_pos v) N).trans ?_
    rw [setIntegral_congr_set (piBox_Ioc_ae_eq_Icc _ 1)]
    refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Icc) fun v _ => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [hexp, kexp, uA, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul]
    congr 1
    ring
  rw [hZ] at h
  refine (h.isEquivalent (mul_pos two_pos (Real.Gamma_pos_of_pos (by norm_num))).ne').congr_right
    (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end A

/-! ### `K = (1 + x² + y²) x² y⁴`: the face unit is `1 + x²` -/

namespace B

/-- The unit `1 + x² + y²`. -/
def uB (v : Fin 2 → ℝ) : ℝ := 1 + v 0 ^ 2 + v 1 ^ 2

theorem uB_cont : Continuous uB :=
  (continuous_const.add ((continuous_apply 0).pow 2)).add ((continuous_apply 1).pow 2)

theorem uB_pos (v : Fin 2 → ℝ) : 0 < uB v := by
  unfold uB
  positivity

/-- The unit on the minimal face `y = 0` is `1 + x²` (independent of the signs). -/
theorem uB_face (σ : Fin 2 → Bool) (w : Fin 2 → ℝ) :
    uB (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) = 1 + w 0 ^ 2 := by
  unfold uB reflect
  simp only [one_smul]
  rw [faceProj_zero, faceProj_one]
  simp [mul_pow, sgn_sq]

/-- The residual integral `I = ∫₀¹ x^{−1/2} (1+x²)^{−1/4} dx` (≈ 1.9234). -/
noncomputable def I : ℝ := ∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))

theorem integrableOn_rpow_half : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

theorem integrableOn_integrand :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) (Ioc 0 1) := by
  refine Integrable.mono' integrableOn_rpow_half ?_
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (continuousOn_id.rpow_const fun t ht => Or.inl ht.1.ne').mul ?_
    exact (continuousOn_const.add (continuousOn_id.pow 2)).rpow_const fun t _ =>
      Or.inl (ne_of_gt (by change (0 : ℝ) < 1 + t ^ 2; positivity))
  · rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by positivity) _))]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by norm_num))

theorem I_pos : 0 < I := by
  have hle : ∀ t ∈ Ioc (0 : ℝ) 1,
      (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ)) ≤
        t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
    intro t ht
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.1.le _)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [ht.2, ht.1]) (by norm_num)
  have hlow : ∫ t in Ioc (0 : ℝ) 1, (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ)) =
      (2 : ℝ) ^ (-(1 / 4 : ℝ)) * 2 := by
    rw [integral_const_mul, integral_Ioc_rpow (by norm_num)]
    norm_num
  calc (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) * 2 := by positivity
    _ = ∫ t in Ioc (0 : ℝ) 1, (2 : ℝ) ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := hlow.symm
    _ ≤ I := setIntegral_mono_on (integrableOn_rpow_half.const_mul _) integrableOn_integrand
      measurableSet_Ioc hle

theorem face_integral (σ : Fin 2 → Bool) :
    ∫ w in unitBox 2, uB (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) ^ (-(1 / 4 : ℝ)) *
      residualWeight hexp kexp (1 / 4) w = I := by
  have hpt : ∀ w ∈ unitBox 2,
      uB (reflect σ ((1 : ℝ) • faceProj hexp kexp (1 / 4) w)) ^ (-(1 / 4 : ℝ)) *
        residualWeight hexp kexp (1 / 4) w =
      ∏ a, (![fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)), fun _ => (1 : ℝ)] :
        Fin 2 → ℝ → ℝ) a (w a) := by
    intro w _
    rw [uB_face, residualWeight_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    ring
  unfold I
  rw [setIntegral_congr_fun (measurableSet_unitBox 2) hpt, integral_unitBox_prod,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_Ioc_one, mul_one]

/-- The cell. -/
noncomputable def cell : VarUnitCell 0 :=
  pointCell 1 hexp kexp kexp_pos 1 one_pos uB uB_cont fun v _ => uB_pos v

theorem cell_lam : cell.lam = 1 / 4 := minRatio_eq

theorem cell_mult : cell.mult = 1 := by
  change multCount (ratioExp hexp kexp) (minRatio hexp kexp) = 1
  rw [minRatio_eq, multCount_eq]

theorem coeff_sum :
    ∑ σ : Fin (cell.n + 1) → Bool, (cell.reflected σ).coeff = Real.Gamma (1 / 4) * I := by
  have hσ : ∀ σ : Fin (cell.n + 1) → Bool,
      (cell.reflected σ).coeff = Real.Gamma (1 / 4) / 4 * I := by
    intro σ
    refine (pointCell_reflected_coeff 1 hexp kexp kexp_pos 1 one_pos uB uB_cont
      (fun v _ => uB_pos v) σ).trans ?_
    rw [minRatio_eq, Real.one_rpow, one_mul, faceLeadConst_eq]
    congr 1
    exact face_integral σ
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, show cell.n = 1 from rfl]
  push_cast
  ring

/-- ★ `∫_{[−1,1]²} e^{−N (1+x²+y²) x² y⁴} ~ Γ(1/4) (∫₀¹ x^{−1/2}(1+x²)^{−1/4} dx) N^{−1/4}`: the
unit frozen on the minimal face `y = 0` keeps its dependence on the residual coordinate `x`. -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ v in piBox 2 (Icc (-1) 1),
        Real.exp (-N * ((1 + v 0 ^ 2 + v 1 ^ 2) * (v 0 ^ 2 * v 1 ^ 4)))) ~[atTop]
      fun N => Real.Gamma (1 / 4) * I * N ^ (-(1 / 4 : ℝ)) := by
  have h := cell.hasLeadingTerm_symIntegral
  rw [coeff_sum, cell_lam, cell_mult, Nat.sub_self] at h
  have hZ : cell.symIntegral = fun N => ∫ v in piBox 2 (Icc (-1) 1),
        Real.exp (-N * ((1 + v 0 ^ 2 + v 1 ^ 2) * (v 0 ^ 2 * v 1 ^ 4))) := by
    funext N
    refine (pointCell_symIntegral 1 hexp kexp kexp_pos 1 one_pos uB uB_cont
      (fun v _ => uB_pos v) N).trans ?_
    rw [setIntegral_congr_set (piBox_Ioc_ae_eq_Icc _ 1)]
    refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Icc) fun v _ => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [hexp, kexp, uB, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul]
    congr 1
    ring
  rw [hZ] at h
  refine (h.isEquivalent (mul_pos (Real.Gamma_pos_of_pos (by norm_num)) I_pos).ne').congr_right
    (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end B

/-! ### `K = x² y⁴ z⁴`: multiplicity two -/

namespace C

/-- The Jacobian exponents `(0, 0, 0)`. -/
def h3 : Fin 3 → ℕ := ![0, 0, 0]

/-- The phase half-exponents `(1, 2, 2)`: `x² y⁴ z⁴`. -/
def k3 : Fin 3 → ℕ := ![1, 2, 2]

theorem k3_pos : ∀ j, 0 < k3 j := by
  intro j
  fin_cases j <;> simp [k3]

theorem ratioExp_zero : ratioExp h3 k3 0 = 1 / 2 := by norm_num [ratioExp, h3, k3]

theorem ratioExp_one : ratioExp h3 k3 1 = 1 / 4 := by norm_num [ratioExp, h3, k3]

theorem ratioExp_two : ratioExp h3 k3 2 = 1 / 4 := by
  norm_num [ratioExp, h3, k3, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem minRatio_eq : minRatio h3 k3 = 1 / 4 := by
  apply le_antisymm
  · exact (Finset.inf'_le (ratioExp h3 k3) (Finset.mem_univ 1)).trans_eq ratioExp_one
  · refine Finset.le_inf' _ _ fun i _ => ?_
    fin_cases i <;> norm_num [ratioExp, h3, k3]

theorem multCount_eq : multCount (ratioExp h3 k3) (1 / 4) = 2 := by
  unfold multCount
  rw [Fin.sum_univ_three, ratioExp_zero, ratioExp_one, ratioExp_two]
  norm_num

/-- The face constant `Γ(1/4)/1! · 1/(2·2) · 1/(2·2)`. -/
theorem faceLeadConst_eq : faceLeadConst h3 k3 (1 / 4) 1 = Real.Gamma (1 / 4) / 16 := by
  unfold faceLeadConst
  rw [multCount_eq, Fin.prod_univ_three, ratioExp_zero, ratioExp_one, ratioExp_two]
  norm_num [k3, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The residual weight `x^{−1/2}`. -/
theorem residualWeight_eq (w : Fin 3 → ℝ) :
    residualWeight h3 k3 (1 / 4) w = w 0 ^ (-(1 / 2 : ℝ)) := by
  unfold residualWeight
  rw [Fin.prod_univ_three, if_neg (by rw [ratioExp_zero]; norm_num), if_pos ratioExp_one,
    if_pos ratioExp_two, mul_one, mul_one]
  norm_num [h3, k3]

theorem face_integral : ∫ w in unitBox 3, residualWeight h3 k3 (1 / 4) w = 2 := by
  have hpt : ∀ w ∈ unitBox 3, residualWeight h3 k3 (1 / 4) w =
      ∏ a, (![fun t : ℝ => t ^ (-(1 / 2 : ℝ)), fun _ => (1 : ℝ), fun _ => (1 : ℝ)] :
        Fin 3 → ℝ → ℝ) a (w a) := by
    intro w _
    rw [residualWeight_eq, Fin.prod_univ_three]
    simp
  rw [setIntegral_congr_fun (measurableSet_unitBox 3) hpt, integral_unitBox_prod,
    Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [integral_Ioc_rpow (by norm_num), integral_Ioc_one]
  norm_num

/-- The cell (constant unit `1`). -/
noncomputable def cell : VarUnitCell 0 :=
  pointCell 2 h3 k3 k3_pos 1 one_pos (fun _ => 1) continuous_const fun _ _ => one_pos

theorem cell_lam : cell.lam = 1 / 4 := minRatio_eq

theorem cell_mult : cell.mult = 2 := by
  change multCount (ratioExp h3 k3) (minRatio h3 k3) = 2
  rw [minRatio_eq, multCount_eq]

theorem coeff_sum :
    ∑ σ : Fin (cell.n + 1) → Bool, (cell.reflected σ).coeff = Real.Gamma (1 / 4) := by
  have hσ : ∀ σ : Fin (cell.n + 1) → Bool,
      (cell.reflected σ).coeff = Real.Gamma (1 / 4) / 16 * 2 := by
    intro σ
    refine (pointCell_reflected_coeff 2 h3 k3 k3_pos 1 one_pos (fun _ => 1) continuous_const
      (fun _ _ => one_pos) σ).trans ?_
    rw [minRatio_eq]
    simp only [Real.one_rpow, one_mul]
    rw [faceLeadConst_eq]
    congr 1
    exact face_integral
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, show cell.n = 2 from rfl]
  push_cast
  ring

/-- ★ `∫_{[−1,1]³} e^{−N x² y⁴ z⁴} ~ Γ(1/4) N^{−1/4} log N` (multiplicity two). -/
theorem integral_isEquivalent :
    (fun N : ℝ => ∫ v in piBox 3 (Icc (-1) 1),
        Real.exp (-N * (v 0 ^ 2 * v 1 ^ 4 * v 2 ^ 4))) ~[atTop]
      fun N => Real.Gamma (1 / 4) * (N ^ (-(1 / 4 : ℝ)) * Real.log N) := by
  have h := cell.hasLeadingTerm_symIntegral
  rw [coeff_sum, cell_lam, cell_mult, show (2 : ℕ) - 1 = 1 from rfl] at h
  have hZ : cell.symIntegral =
      fun N => ∫ v in piBox 3 (Icc (-1) 1), Real.exp (-N * (v 0 ^ 2 * v 1 ^ 4 * v 2 ^ 4)) := by
    funext N
    refine (pointCell_symIntegral 2 h3 k3 k3_pos 1 one_pos (fun _ => 1) continuous_const
      (fun _ _ => one_pos) N).trans ?_
    rw [setIntegral_congr_set (piBox_Ioc_ae_eq_Icc _ 1)]
    refine setIntegral_congr_fun (measurableSet_piBox _ _ measurableSet_Icc) fun v _ => ?_
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [h3, k3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, pow_zero, one_mul]
    congr 1
    ring
  rw [hZ] at h
  refine (h.isEquivalent (Real.Gamma_pos_of_pos (by norm_num)).ne').congr_right
    (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end C

end VarRegression

end Grammar
