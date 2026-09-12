/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.VariableUnitCertificate
import Grammar.ResidualFaceCoefficient

/-!
# Variable-unit cells

Unit 3 of consult #81 (`tide-log/gpt6_bigpicture_v81.md`): the cell packaging of the variable-unit
certificate CCLV.

* `symVarKernel`: the symmetric variable-unit kernel over `(−b,b]^{n+1}`; it is the sum over the
  `2^{n+1}` orthants of variable-unit kernels with the amplitude AND the unit reflected
  (`symVarKernel_eq_sum`, mirroring `symScalarKernel_eq_sum`).
* `VarUnitCell`: the scalar-unit cell data with the phase unit `u z v` depending on the normal
  coordinates (positive on the base times the closed normal ball). It carries the pair
  `(lam, mult)`, the orthant integral, the coefficient `∫_base β · boxFaceCoeff(A·u^{−λ})`, and the
  certificate `hasLeadingTerm` (CCLV); reflected cells reflect both `A` and `u`; the symmetric
  integral is the sum of the reflected orthant integrals (`symIntegral_eq_sum`) and has the
  certificate with coefficient the sum of the reflected coefficients (`hasLeadingTerm_symIntegral`).
* **Specialisation**: a scalar-unit cell is a variable-unit cell with `u z v = q z`
  (`ScalarUnitCell.toVar`), with the same integral and coefficient (`toVar_integral`,
  `toVar_coeff`).
* **Residual-face form and reflection reduction**: the reflected coefficient is an explicit
  projected face integral with the unit frozen on the minimal face (`reflected_coeff_eq`), depends
  only on the residual signs (`reflected_coeff_congr`), and the reflection sum reduces to
  `2^{|J|}` times the sum over residual sign classes (`sum_reflected_coeff`).
-/

open MeasureTheory Set Filter Topology

namespace Grammar

/-! ### The symmetric variable-unit kernel -/

section SymKernel

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (b : ℝ) {t : ℕ}
  (u A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- The symmetric variable-unit kernel over `(−b,b]^{n+1}`. -/
noncomputable def symVarKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ v in piBox (n + 1) (Ioc (-b) b),
    A z v * (∏ i, |v i| ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i)))

variable {n h k b}

/-- **The symmetric kernel is the sum of the reflected orthant kernels** (amplitude and unit
reflected). -/
theorem symVarKernel_eq_sum (hb : 0 < b) (hA : Continuous (Function.uncurry A))
    (hu : Continuous (Function.uncurry u)) (z : Fin t → ℝ) (N : ℝ) :
    symVarKernel n h k b u A z N = ∑ σ : Fin (n + 1) → Bool,
      varBoxKernel n h k b (reflectAmp n u σ) (reflectAmp n A σ) z N := by
  have hAz : Continuous (A z) := continuous_amp_of_uncurry A hA z
  have huz : Continuous (u z) := continuous_amp_of_uncurry u hu z
  set G : (Fin (n + 1) → ℝ) → ℝ := fun v =>
    A z v * (∏ i, |v i| ^ h i) * Real.exp (-(u z v * N * ∏ i, v i ^ (2 * k i))) with hG
  have hGc : Continuous G := by
    rw [hG]
    fun_prop
  unfold symVarKernel
  rw [integral_piBox_dilation hb measurableSet_Ioc measurableSet_Ioc (mul_mem_Ioc_symm_iff hb) G]
  have hsym : piBox (n + 1) (Ioc (-1 : ℝ) 1) = symBox (n + 1) := rfl
  rw [hsym, integral_symBox_eq_sum_reflect (n + 1) (fun v => G (b • v))
    (hGc.comp (continuous_const_smul b)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold varBoxKernel
  rw [integral_piBox_dilation hb measurableSet_Ioc measurableSet_Ioc (mul_mem_Ioc_pos_iff hb)]
  have hu' : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hu']
  congr 1
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun v hv => ?_
  have hv0 : ∀ i, 0 < v i := fun i => (hv i (mem_univ i)).1
  have h1 : ∏ i, |reflect σ (b • v) i| ^ h i = ∏ i, (b • v) i ^ h i :=
    Finset.prod_congr rfl fun i _ => by
      rw [abs_reflect_apply, abs_of_pos (by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_pos hb (hv0 i))]
  have h2 : ∏ i, reflect σ (b • v) i ^ (2 * k i) = ∏ i, (b • v) i ^ (2 * k i) :=
    Finset.prod_congr rfl fun i _ => reflect_apply_pow_even n σ _ i _
  rw [← reflect_smul, hG]
  simp only [reflectAmp]
  rw [h1, h2]

end SymKernel

/-! ### Variable-unit cells -/

/-- **A variable-unit cell**: the scalar-unit cell data with a phase unit `u z v` depending on the
normal coordinates, positive on the base times the closed normal ball. -/
structure VarUnitCell (t : ℕ) where
  /-- The normal dimension minus one. -/
  n : ℕ
  /-- The Jacobian exponents. -/
  h : Fin (n + 1) → ℕ
  /-- The phase half-exponents. -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ j, 0 < k j
  /-- The normal radius. -/
  b : ℝ
  b_pos : 0 < b
  /-- The amplitude. -/
  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  A_cont : Continuous (Function.uncurry A)
  /-- The compact base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The base weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_int : IntegrableOn βw base
  /-- The phase unit. -/
  u : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  u_cont : Continuous (Function.uncurry u)
  u_pos : ∀ z ∈ base, ∀ v ∈ Metric.closedBall (0 : Fin (n + 1) → ℝ) b, 0 < u z v

theorem piBox_Icc_subset_closedBall {r : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    piBox r (Icc 0 b) ⊆ Metric.closedBall (0 : Fin r → ℝ) b := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hb).2 fun i => ?_
  have := hv i (mem_univ i)
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

namespace VarUnitCell

variable {t : ℕ} (c : VarUnitCell t)

/-- The cell's exponent `min_a (h_a+1)/(2k_a)`. -/
noncomputable def lam : ℝ := minRatio c.h c.k

/-- The cell's multiplicity. -/
noncomputable def mult : ℕ := multCount (ratioExp c.h c.k) c.lam

theorem lam_pos : 0 < c.lam := minRatio_pos c.h c.k c.k_pos

theorem lam_le (i : Fin (c.n + 1)) : c.lam ≤ ratioExp c.h c.k i := minRatio_le c.h c.k i

theorem exists_ratioExp_eq_lam : ∃ i, ratioExp c.h c.k i = c.lam :=
  exists_ratioExp_eq_minRatio c.h c.k

theorem u_pos_box {z : Fin t → ℝ} (hz : z ∈ c.base) {v : Fin (c.n + 1) → ℝ}
    (hv : v ∈ piBox (c.n + 1) (Icc 0 c.b)) : 0 < c.u z v :=
  c.u_pos z hz v (piBox_Icc_subset_closedBall c.b_pos.le hv)

/-- The orthant integral `∫_base β_w(z) varBoxKernel(z, N) dz`. -/
noncomputable def integral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * varBoxKernel c.n c.h c.k c.b c.u c.A z N

/-- The cell coefficient `∫_base β_w(z) boxFaceCoeff(A·u^{−λ})(z) dz`. -/
noncomputable def coeff : ℝ :=
  ∫ z in c.base, c.βw z * varBoxFaceCoeff c.n c.h c.k c.b c.u c.A c.lam z

/-- **The cell certificate** (CCLV). -/
theorem hasLeadingTerm : HasLeadingTerm c.integral c.coeff c.lam (c.mult - 1) :=
  hasLeadingTerm_integral_varBoxKernel c.k_pos c.b_pos c.lam_pos c.lam_le c.exists_ratioExp_eq_lam
    c.A_cont c.base_compact c.u_cont (fun _ hz _ hv => c.u_pos_box hz hv) c.βw_int

/-! ### Reflected cells and the symmetric integral -/

/-- The reflected cell: amplitude and unit composed with the reflection `σ`. -/
def reflected (σ : Fin (c.n + 1) → Bool) : VarUnitCell t where
  n := c.n
  h := c.h
  k := c.k
  k_pos := c.k_pos
  b := c.b
  b_pos := c.b_pos
  A := reflectAmp c.n c.A σ
  A_cont := continuous_reflectAmp c.n c.A c.A_cont σ
  base := c.base
  base_compact := c.base_compact
  βw := c.βw
  βw_int := c.βw_int
  u := reflectAmp c.n c.u σ
  u_cont := continuous_reflectAmp c.n c.u c.u_cont σ
  u_pos := fun z hz v hv =>
    c.u_pos z hz _ ((ScalarUnitCell.reflect_mem_closedBall_iff σ c.b_pos.le v).2 hv)

theorem reflected_lam (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).lam = c.lam := rfl
theorem reflected_mult (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).mult = c.mult := rfl
theorem reflected_n (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).n = c.n := rfl
theorem reflected_h (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).h = c.h := rfl
theorem reflected_k (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).k = c.k := rfl
theorem reflected_b (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).b = c.b := rfl
theorem reflected_base (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).base = c.base := rfl
theorem reflected_βw (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).βw = c.βw := rfl
theorem reflected_A (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).A = reflectAmp c.n c.A σ := rfl
theorem reflected_u (σ : Fin (c.n + 1) → Bool) : (c.reflected σ).u = reflectAmp c.n c.u σ := rfl

/-- The symmetric (two-sided) integral of the cell. -/
noncomputable def symIntegral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * symVarKernel c.n c.h c.k c.b c.u c.A z N

theorem integrable_reflected (σ : Fin (c.n + 1) → Bool) {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun z => c.βw z * varBoxKernel c.n c.h c.k c.b (reflectAmp c.n c.u σ)
      (reflectAmp c.n c.A σ) z N) c.base :=
  integrableOn_mul_varBoxKernel _ _ c.b_pos (continuous_reflectAmp c.n c.A c.A_cont σ)
    (continuous_reflectAmp c.n c.u c.u_cont σ) c.base_compact
    (fun z hz v hv => ((c.reflected σ).u_pos z hz v (piBox_Ioc_subset_closedBall c.b_pos hv)).le)
    c.βw_int hN

/-- **The symmetric integral is the sum of the reflected orthant integrals.** -/
theorem symIntegral_eq_sum {N : ℝ} (hN : 0 ≤ N) :
    c.symIntegral N = ∑ σ : Fin (c.n + 1) → Bool, (c.reflected σ).integral N := by
  unfold symIntegral
  have h : ∀ z, c.βw z * symVarKernel c.n c.h c.k c.b c.u c.A z N =
      ∑ σ : Fin (c.n + 1) → Bool, c.βw z *
        varBoxKernel c.n c.h c.k c.b (reflectAmp c.n c.u σ) (reflectAmp c.n c.A σ) z N :=
    fun z => by
    rw [symVarKernel_eq_sum c.u c.A c.b_pos c.A_cont c.u_cont, Finset.mul_sum]
  simp_rw [h]
  rw [integral_finsetSum _ fun σ _ => c.integrable_reflected σ hN]
  rfl

/-- **The certificate of the symmetric integral**: the sum of the reflected coefficients. -/
theorem hasLeadingTerm_symIntegral :
    HasLeadingTerm c.symIntegral (∑ σ : Fin (c.n + 1) → Bool, (c.reflected σ).coeff) c.lam
      (c.mult - 1) := by
  have h := HasLeadingTerm.sum (Finset.univ : Finset (Fin (c.n + 1) → Bool))
    (Z := fun σ N => (c.reflected σ).integral N) (c := fun σ => (c.reflected σ).coeff)
    (lam := c.lam) (k := c.mult - 1) fun σ _ => (c.reflected σ).hasLeadingTerm
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN => (c.symIntegral_eq_sum hN).symm)

/-! ### The residual-face form of the coefficient and the reflection reduction -/

/-- **The reflected coefficient in projected face form** with the unit frozen on the minimal face.
-/
theorem reflected_coeff_eq (σ : Fin (c.n + 1) → Bool) :
    (c.reflected σ).coeff = ∫ z in c.base, c.βw z *
      (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
          (residualExponent c.h c.k c.lam a + 1)) *
        (faceLeadConst c.h c.k c.lam 1 *
          ∫ w in unitBox (c.n + 1),
            c.A z (reflect σ (c.b • faceProj c.h c.k c.lam w)) *
              c.u z (reflect σ (c.b • faceProj c.h c.k c.lam w)) ^ (-c.lam) *
              residualWeight c.h c.k c.lam w)) := by
  unfold coeff varBoxFaceCoeff
  simp only [reflected_n, reflected_h, reflected_k, reflected_b, reflected_base, reflected_βw,
    reflected_A, reflected_u, reflected_lam]
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  rw [boxFaceCoeff_eq_residual c.h c.k c.k_pos c.lam 1 c.b c.b_pos]
  rfl

/-- Reflected cells whose signs agree off the minimal coordinates have equal coefficients. -/
theorem reflected_coeff_congr {σ σ' : Fin (c.n + 1) → Bool}
    (hσ : ∀ a, ¬ ratioExp c.h c.k a = c.lam → σ a = σ' a) :
    (c.reflected σ).coeff = (c.reflected σ').coeff := by
  rw [reflected_coeff_eq, reflected_coeff_eq]
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  refine congrArg (fun x => c.βw z *
    (c.b ^ (∑ a ∈ Finset.univ.filter (fun a => ¬ ratioExp c.h c.k a = c.lam),
      (residualExponent c.h c.k c.lam a + 1)) * (faceLeadConst c.h c.k c.lam 1 * x))) ?_
  refine setIntegral_congr_fun (measurableSet_unitBox _) fun w _ => ?_
  rw [reflect_congr fun a ha => hσ a fun hmin => ha ?_]
  simp only [Pi.smul_apply, faceProj, hmin, if_true, smul_zero]

/-- **The reflection sum of a variable-unit cell reduces to the residual signs.** -/
theorem sum_reflected_coeff :
    ∑ σ, (c.reflected σ).coeff =
      2 ^ (minimalCoords c.h c.k c.lam).card *
        ∑ τ : {a : Fin (c.n + 1) // a ∉ minimalCoords c.h c.k c.lam} → Bool,
          (c.reflected (extendFalse _ τ)).coeff :=
  sum_reduce_of_indep _ _ fun _ _ hσσ' => c.reflected_coeff_congr fun a ha =>
    hσσ' a fun hmem => ha ((mem_minimalCoords c.h c.k c.lam).1 hmem)

end VarUnitCell

/-! ### Specialisation: scalar-unit cells -/

/-- A scalar-unit cell as a variable-unit cell with the unit `u z v = q z`. -/
def ScalarUnitCell.toVar {t : ℕ} (c : ScalarUnitCell t) : VarUnitCell t where
  n := c.n
  h := c.h
  k := c.k
  k_pos := c.k_pos
  b := c.b
  b_pos := c.b_pos
  A := c.A
  A_cont := c.A_cont
  base := c.base
  base_compact := c.base_compact
  βw := c.βw
  βw_int := c.βw_int
  u := fun z _ => c.q z
  u_cont := c.q_cont.comp continuous_fst
  u_pos := fun z hz _ _ => c.q_pos z hz

theorem scalarBoxKernel_eq_varBoxKernel {n : ℕ} {h k : Fin (n + 1) → ℕ} {b : ℝ} {t : ℕ}
    (q : (Fin t → ℝ) → ℝ) (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (z : Fin t → ℝ) (N : ℝ) :
    scalarBoxKernel n h k b q A z N = varBoxKernel n h k b (fun z _ => q z) A z N := by
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  unfold origPhaseIntegral varBoxKernel
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [mul_zero, add_zero]

theorem ScalarUnitCell.toVar_integral {t : ℕ} (c : ScalarUnitCell t) (N : ℝ) :
    c.toVar.integral N = c.integral N := by
  unfold VarUnitCell.integral ScalarUnitCell.integral
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  rw [scalarBoxKernel_eq_varBoxKernel]
  rfl

theorem ScalarUnitCell.toVar_coeff {t : ℕ} (c : ScalarUnitCell t) : c.toVar.coeff = c.coeff := by
  unfold VarUnitCell.coeff ScalarUnitCell.coeff varBoxFaceCoeff scalarBoxFaceCoeff
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  change c.βw z * boxFaceCoeff c.n c.h c.k 1 c.b (fun z v => c.A z v * c.q z ^ (-c.lam)) c.lam z =
    c.βw z * (c.q z ^ (-c.lam) * boxFaceCoeff c.n c.h c.k 1 c.b c.A c.lam z)
  congr 1
  rw [boxFaceCoeff_congr c.b_pos.le (A₂ := fun z' v => c.q z ^ (-c.lam) * c.A z' v)
    (fun v _ => mul_comm _ _), boxFaceCoeff_const_mul]

end Grammar
