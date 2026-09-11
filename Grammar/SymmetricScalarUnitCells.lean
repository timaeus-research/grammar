/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.ScalarUnitKernel

/-!
# Two-sided assembly and scalar-unit cells

Unit B of consult #76 (`tide-log/gpt6_bigpicture_v76.md`). The chart–stratum pieces have a
TWO-SIDED normal box `(−b, b)^{n+1}` and the Jacobian carries `∏|u_i|^{h_i}`; the analytic normal
form of the library lives on the positive cube. The **symmetric scalar-unit kernel**
`∫_{(−b,b]^{n+1}} A(z,u) ∏|u_i|^{h_i} e^{−N q(z) ∏u_i^{2k_i}} du` is the sum over the `2^{n+1}`
orthants of the positive-cube scalar-unit kernels of the **reflected amplitudes** `A(z, σ·u)`
(`symScalarKernel_eq_sum`: dilation of the box to side one, `integral_piBox_dilation`; the
signed-reflection identity `integral_symBox_eq_sum_reflect`; invariance of `|u_j|^{h_j}` and
`u_j^{2k_j}` under reflection; dilation back).

**Scalar-unit cells** (`ScalarUnitCell`: the constant-unit cell data with a continuous phase unit
`q(z)`, positive on the compact base) carry the certificate of CCXXXI at their own pair
(`ScalarUnitCell.hasLeadingTerm`); constant-unit cells embed (`ConstantUnitCell.toScalar`, with the
same integrals). A **finite scalar-unit atlas** (`FiniteScalarUnitAtlas`) has the leading term at
any dominating pair with the tied coefficients summed (`hasLeadingTerm_of_extremal`), and the
resolved Boltzmann integral of a cover of monomial charts whose nonempty chart–stratum pieces admit
scalar-unit atlases has the leading term with the summed tied cell coefficients
(`hasLeadingTerm_boltzmannIntegral_of_scalarAtlases`). Finally **a symmetric cell has an orthant
atlas**: the two-sided integral `∫_base β_w · symScalarKernel` is a `FiniteScalarUnitAtlas` with the
`2^{n+1}` reflected cells (`ScalarUnitCell.symAtlas`; the exact decomposition needs the
integrability of each orthant term on the base, from a uniform bound of the kernel,
`abs_scalarBoxKernel_le_const`).

Non-claims: the unit `q` depends on the base point only; the half-open box `(−b,b]` is used (the
open box of a piece differs by a null set, handled where the piece is bridged).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Grammar

/-! ### Dilation of box integrals -/

section Dilation

variable {d : ℕ}

theorem smul_mem_piBox_iff {b : ℝ} {S T : Set ℝ} (hST : ∀ x, b * x ∈ T ↔ x ∈ S)
    (v : Fin d → ℝ) : b • v ∈ piBox d T ↔ v ∈ piBox d S := by
  unfold piBox
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun i => hST (v i)

/-- **Dilation of a box integral**: `∫_{piBox T} G = b^d ∫_{piBox S} G(b·)` when `b · S = T`. -/
theorem integral_piBox_dilation {b : ℝ} (hb : 0 < b) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : ∀ x, b * x ∈ T ↔ x ∈ S) (G : (Fin d → ℝ) → ℝ) :
    ∫ u in piBox d T, G u = b ^ d * ∫ v in piBox d S, G (b • v) := by
  have hind : ∀ v, (piBox d T).indicator G (b • v) =
      (piBox d S).indicator (fun v => G (b • v)) v := by
    intro v
    by_cases hv : v ∈ piBox d S
    · rw [indicator_of_mem hv, indicator_of_mem ((smul_mem_piBox_iff hST v).2 hv)]
    · rw [indicator_of_notMem hv,
        indicator_of_notMem fun h' => hv ((smul_mem_piBox_iff hST v).1 h')]
  have hscale := Measure.integral_comp_smul (volume : Measure (Fin d → ℝ))
    ((piBox d T).indicator G) b
  rw [Module.finrank_fin_fun, smul_eq_mul, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hb.le _)),
    integral_indicator (measurableSet_piBox _ _ hT)] at hscale
  simp_rw [hind] at hscale
  rw [integral_indicator (measurableSet_piBox _ _ hS)] at hscale
  rw [hscale, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb.ne'), one_mul]

end Dilation

/-! ### The symmetric scalar-unit kernel -/

section Symmetric

variable (n : ℕ) (h k : Fin (n + 1) → ℕ) (b : ℝ) {t : ℕ} (q : (Fin t → ℝ) → ℝ)
  (A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ)

/-- **The symmetric scalar-unit kernel** on the two-sided box `(−b, b]^{n+1}`. -/
noncomputable def symScalarKernel (z : Fin t → ℝ) (N : ℝ) : ℝ :=
  ∫ u in piBox (n + 1) (Ioc (-b) b),
    A z u * (∏ i, |u i| ^ h i) * Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i)))

/-- The reflected amplitude `A(z, σ·u)`. -/
def reflectAmp (σ : Fin (n + 1) → Bool) (z : Fin t → ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  A z (reflect σ u)

theorem continuous_reflectAmp (hA : Continuous (Function.uncurry A)) (σ : Fin (n + 1) → Bool) :
    Continuous (Function.uncurry (reflectAmp n A σ)) :=
  hA.comp (continuous_fst.prodMk ((continuous_reflect σ).comp continuous_snd))

theorem abs_sgn' (s : Bool) : |sgn s| = 1 := by cases s <;> simp [sgn]

theorem reflect_smul (σ : Fin (n + 1) → Bool) (c : ℝ) (v : Fin (n + 1) → ℝ) :
    reflect σ (c • v) = c • reflect σ v := by
  funext i
  simp only [reflect, Pi.smul_apply, smul_eq_mul]
  ring

theorem abs_reflect_apply (σ : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    |reflect σ v i| = |v i| := by
  simp only [reflect, abs_mul, abs_sgn', one_mul]

theorem reflect_apply_pow_even (σ : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (m : ℕ) : reflect σ v i ^ (2 * m) = v i ^ (2 * m) := by
  simp only [reflect, mul_pow, sgn_pow_even, one_mul]

theorem mul_mem_Ioc_symm_iff {b : ℝ} (hb : 0 < b) (x : ℝ) :
    b * x ∈ Ioc (-b) b ↔ x ∈ Ioc (-1 : ℝ) 1 := by
  simp only [mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem mul_mem_Ioc_pos_iff {b : ℝ} (hb : 0 < b) (x : ℝ) :
    b * x ∈ Ioc 0 b ↔ x ∈ Ioc (0 : ℝ) 1 := by
  simp only [mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- **Orthant assembly**: the symmetric kernel is the sum over the `2^{n+1}` orthants of the
positive-cube scalar-unit kernels of the reflected amplitudes. -/
theorem symScalarKernel_eq_sum (hb : 0 < b) (hA : Continuous (Function.uncurry A))
    (z : Fin t → ℝ) (N : ℝ) :
    symScalarKernel n h k b q A z N =
      ∑ σ : Fin (n + 1) → Bool, scalarBoxKernel n h k b q (reflectAmp n A σ) z N := by
  have hAz : Continuous (A z) := continuous_amp_of_uncurry A hA z
  set G : (Fin (n + 1) → ℝ) → ℝ := fun u =>
    A z u * (∏ i, |u i| ^ h i) * Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i))) with hG
  have hGc : Continuous G := by
    rw [hG]
    fun_prop
  unfold symScalarKernel
  rw [integral_piBox_dilation hb measurableSet_Ioc measurableSet_Ioc (mul_mem_Ioc_symm_iff hb) G]
  have hsym : piBox (n + 1) (Ioc (-1 : ℝ) 1) = symBox (n + 1) := rfl
  rw [hsym, integral_symBox_eq_sum_reflect (n + 1) (fun v => G (b • v))
    (hGc.comp (continuous_const_smul b)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  unfold origPhaseIntegral
  rw [integral_piBox_dilation hb measurableSet_Ioc measurableSet_Ioc (mul_mem_Ioc_pos_iff hb)]
  have hu : piBox (n + 1) (Ioc (0 : ℝ) 1) = unitBox (n + 1) := rfl
  rw [hu]
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
  simp only [reflectAmp, mul_zero, add_zero]
  rw [h1, h2]

/-- A uniform bound of the amplitude on the box bounds the scalar-unit kernel by
`M · b^{Σh} · b^{n+1}` (`N ≥ 0`, `q(z) ≥ 0`). -/
theorem abs_scalarBoxKernel_le_const (hb : 0 < b) {z : Fin t → ℝ} {M : ℝ}
    (hM : ∀ u ∈ piBox (n + 1) (Ioc 0 b), |A z u| ≤ M) (hqz : 0 ≤ q z) {N : ℝ} (hN : 0 ≤ N) :
    |scalarBoxKernel n h k b q A z N| ≤ M * b ^ (∑ i, h i) * b ^ (n + 1) := by
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  unfold origPhaseIntegral
  have hvol : (volume : Measure (Fin (n + 1) → ℝ)) (piBox (n + 1) (Ioc 0 b)) < ⊤ :=
    lt_of_le_of_lt (measure_mono (pi_mono fun _ _ => Ioc_subset_Icc_self))
      ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top)
  have hreal : (volume : Measure (Fin (n + 1) → ℝ)).real (piBox (n + 1) (Ioc 0 b)) =
      b ^ (n + 1) := by
    rw [measureReal_def]
    unfold piBox
    rw [Real.volume_pi_Ioc, ENNReal.toReal_prod]
    simp only [sub_zero, ENNReal.toReal_ofReal hb.le, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hbound : ∀ u ∈ piBox (n + 1) (Ioc 0 b), ‖A z u * (∏ i, u i ^ h i) *
      Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i)) + q z * (Real.sqrt N * ∏ i, u i ^ k i) * 0)‖ ≤
        M * b ^ (∑ i, h i) := by
    intro u hu
    have hu0 : ∀ i, 0 < u i := fun i => (hu i (mem_univ i)).1
    have hub : ∀ i, u i ≤ b := fun i => (hu i (mem_univ i)).2
    have hP : 0 ≤ ∏ i, u i ^ h i := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
    have hPb : ∏ i, u i ^ h i ≤ b ^ (∑ i, h i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod (fun i _ => pow_nonneg (hu0 i).le _) fun i _ =>
        pow_le_pow_left₀ (hu0 i).le (hub i) _
    have hQ : 0 ≤ ∏ i, u i ^ (2 * k i) := Finset.prod_nonneg fun i _ => pow_nonneg (hu0 i).le _
    have hexp : Real.exp (-(q z * N * ∏ i, u i ^ (2 * k i)) +
        q z * (Real.sqrt N * ∏ i, u i ^ k i) * 0) ≤ 1 := by
      rw [mul_zero, add_zero, Real.exp_le_one_iff]
      exact neg_nonpos.2 (mul_nonneg (mul_nonneg hqz hN) hQ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hP, abs_of_pos (Real.exp_pos _)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM u hu)
    calc |A z u| * (∏ i, u i ^ h i) * Real.exp _ ≤ M * b ^ (∑ i, h i) * 1 :=
          mul_le_mul (mul_le_mul (hM u hu) hPb hP hM0) hexp (Real.exp_pos _).le
            (mul_nonneg hM0 (pow_nonneg hb.le _))
      _ = M * b ^ (∑ i, h i) := mul_one _
  have h := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [Real.norm_eq_abs, hreal] at h
  exact h

end Symmetric

/-! ### Scalar-unit cells and finite atlases -/

/-- **A scalar-unit cell**: the constant-unit cell data with a continuous phase unit `q`, positive
on the compact base. -/
structure ScalarUnitCell (t : ℕ) where
  /-- The normal dimension is `n + 1`. -/
  n : ℕ
  /-- The density exponents. -/
  h : Fin (n + 1) → ℕ
  /-- The half phase exponents. -/
  k : Fin (n + 1) → ℕ
  k_pos : ∀ i, 0 < k i
  /-- The box side. -/
  b : ℝ
  b_pos : 0 < b
  /-- The amplitude. -/
  A : (Fin t → ℝ) → (Fin (n + 1) → ℝ) → ℝ
  A_cont : Continuous (Function.uncurry A)
  /-- The tangential base. -/
  base : Set (Fin t → ℝ)
  base_compact : IsCompact base
  /-- The tangential weight. -/
  βw : (Fin t → ℝ) → ℝ
  βw_int : IntegrableOn βw base
  /-- The scalar phase unit. -/
  q : (Fin t → ℝ) → ℝ
  q_cont : Continuous q
  q_pos : ∀ z ∈ base, 0 < q z

namespace ScalarUnitCell

variable {t : ℕ} (c : ScalarUnitCell t)

/-- The cell's exponent `λ = min_j (h_j+1)/(2k_j)`. -/
noncomputable def lam : ℝ := minRatio c.h c.k

/-- The cell's multiplicity. -/
noncomputable def mult : ℕ := multCount (ratioExp c.h c.k) c.lam

theorem lam_pos : 0 < c.lam := minRatio_pos c.h c.k c.k_pos

theorem lam_le (i : Fin (c.n + 1)) : c.lam ≤ ratioExp c.h c.k i := minRatio_le c.h c.k i

theorem exists_ratioExp_eq_lam : ∃ i, ratioExp c.h c.k i = c.lam :=
  exists_ratioExp_eq_minRatio c.h c.k

/-- The cell integral `∫_base β_w(z) L_N^{q}(z) dz`. -/
noncomputable def integral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * scalarBoxKernel c.n c.h c.k c.b c.q c.A z N

/-- The cell coefficient `∫_base β_w(z) q(z)^{−λ} faceCoeff(z) dz`. -/
noncomputable def coeff : ℝ :=
  ∫ z in c.base, c.βw z * scalarBoxFaceCoeff c.n c.h c.k c.b c.q c.A c.lam z

/-- **The cell certificate** (CCXXXI). -/
theorem hasLeadingTerm : HasLeadingTerm c.integral c.coeff c.lam (c.mult - 1) :=
  hasLeadingTerm_integral_scalarBoxKernel c.q c.A c.k_pos c.b_pos c.lam_pos c.lam_le
    c.exists_ratioExp_eq_lam c.A_cont c.base_compact c.q_cont c.q_pos c.βw_int

end ScalarUnitCell

/-- A constant-unit cell as a scalar-unit cell. -/
def ConstantUnitCell.toScalar {t : ℕ} (c : ConstantUnitCell t) : ScalarUnitCell t :=
  { c with q := fun _ => c.β, q_cont := continuous_const, q_pos := fun _ _ => c.β_pos }

theorem ConstantUnitCell.toScalar_integral {t : ℕ} (c : ConstantUnitCell t) (N : ℝ) :
    c.toScalar.integral N = c.integral N := by
  unfold ScalarUnitCell.integral ConstantUnitCell.integral
  refine setIntegral_congr_fun c.base_compact.isClosed.measurableSet fun z _ => ?_
  congr 1
  rw [scalarBoxKernel_eq_origPhaseIntegral]
  rfl

/-- **A finite scalar-unit atlas** of `Z`. -/
structure FiniteScalarUnitAtlas (t : ℕ) (Z : ℝ → ℝ) where
  /-- The cell index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The cells. -/
  cell : ι → ScalarUnitCell t
  /-- The exact decomposition. -/
  eq : ∀ N : ℝ, 0 ≤ N → Z N = ∑ i, (cell i).integral N

namespace FiniteScalarUnitAtlas

variable {t : ℕ} {Z : ℝ → ℝ} (At : FiniteScalarUnitAtlas t Z)

attribute [instance] FiniteScalarUnitAtlas.fintype

/-- The tied cells at a nominated pair. -/
noncomputable def tied (lam₀ : ℝ) (k₀ : ℕ) : Finset At.ι :=
  Finset.univ.filter fun i => (At.cell i).lam = lam₀ ∧ (At.cell i).mult - 1 = k₀

/-- **The leading term of a scalar-unit atlas at a pair dominating every cell.** -/
theorem hasLeadingTerm_of_extremal (lam₀ : ℝ) (k₀ : ℕ) (hlam : ∀ i, lam₀ ≤ (At.cell i).lam)
    (hk : ∀ i, (At.cell i).lam = lam₀ → (At.cell i).mult - 1 ≤ k₀) :
    HasLeadingTerm Z (∑ i ∈ At.tied lam₀ k₀, (At.cell i).coeff) lam₀ k₀ := by
  have h := hasLeadingTerm_sum_of_extremal Finset.univ (fun i N => (At.cell i).integral N)
    (fun i => (At.cell i).coeff) (fun i => (At.cell i).lam) (fun i => (At.cell i).mult - 1) lam₀ k₀
    (fun i _ => (At.cell i).hasLeadingTerm) (fun i _ => hlam i) (fun i _ => hk i)
  exact h.congr' ((eventually_ge_atTop 0).mono fun N hN => (At.eq N hN).symm)

end FiniteScalarUnitAtlas

/-! ### The orthant atlas of a symmetric cell -/

namespace ScalarUnitCell

variable {t : ℕ} (c : ScalarUnitCell t)

/-- The reflected cell. -/
def reflected (σ : Fin (c.n + 1) → Bool) : ScalarUnitCell t :=
  { c with A := reflectAmp c.n c.A σ, A_cont := continuous_reflectAmp c.n c.A c.A_cont σ }

/-- The symmetric (two-sided) integral of the cell. -/
noncomputable def symIntegral (N : ℝ) : ℝ :=
  ∫ z in c.base, c.βw z * symScalarKernel c.n c.h c.k c.b c.q c.A z N

/-- A uniform bound of the reflected amplitudes on the base and the box. -/
theorem exists_bound_reflectAmp : ∃ M, ∀ (σ : Fin (c.n + 1) → Bool), ∀ z ∈ c.base,
    ∀ u ∈ piBox (c.n + 1) (Ioc 0 c.b), |reflectAmp c.n c.A σ z u| ≤ M := by
  have hK : IsCompact (c.base ×ˢ (Set.pi univ fun _ : Fin (c.n + 1) => Icc (-c.b) c.b)) :=
    c.base_compact.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn c.A_cont.continuousOn
  refine ⟨M, fun σ z hz u hu => ?_⟩
  have hmem : (z, reflect σ u) ∈
      c.base ×ˢ (Set.pi univ fun _ : Fin (c.n + 1) => Icc (-c.b) c.b) := by
    refine ⟨hz, fun i _ => ?_⟩
    have h1 := (hu i (mem_univ i)).1
    have h2 := (hu i (mem_univ i)).2
    have := abs_reflect_apply c.n σ u i
    rw [abs_of_pos h1] at this
    exact abs_le.1 (this.le.trans h2)
  have := hM _ hmem
  rwa [Real.norm_eq_abs] at this

/-- Each orthant term is integrable on the base. -/
theorem integrable_reflected (σ : Fin (c.n + 1) → Bool) {N : ℝ} (hN : 0 ≤ N) :
    Integrable (fun z => c.βw z * scalarBoxKernel c.n c.h c.k c.b c.q (reflectAmp c.n c.A σ) z N)
      (volume.restrict c.base) := by
  obtain ⟨M, hM⟩ := c.exists_bound_reflectAmp
  have hbase : MeasurableSet c.base := c.base_compact.isClosed.measurableSet
  have h := c.βw_int.bdd_mul (c := M * c.b ^ (∑ i, c.h i) * c.b ^ (c.n + 1))
    (stronglyMeasurable_scalarBoxKernel c.q (reflectAmp c.n c.A σ)
      (continuous_reflectAmp c.n c.A c.A_cont σ) c.q_cont N).aestronglyMeasurable
    ((ae_restrict_iff' hbase).2 (Eventually.of_forall fun z hz => by
      rw [Real.norm_eq_abs]
      exact abs_scalarBoxKernel_le_const c.n c.h c.k c.b c.q _ c.b_pos (hM σ z hz)
        (c.q_pos z hz).le hN))
  exact h.congr (Eventually.of_forall fun z => mul_comm _ _)

/-- **The symmetric integral is the sum of the orthant cell integrals** (`N ≥ 0`). -/
theorem symIntegral_eq_sum {N : ℝ} (hN : 0 ≤ N) :
    c.symIntegral N = ∑ σ : Fin (c.n + 1) → Bool, (c.reflected σ).integral N := by
  unfold symIntegral
  have h : ∀ z, c.βw z * symScalarKernel c.n c.h c.k c.b c.q c.A z N =
      ∑ σ : Fin (c.n + 1) → Bool,
        c.βw z * scalarBoxKernel c.n c.h c.k c.b c.q (reflectAmp c.n c.A σ) z N := fun z => by
    rw [symScalarKernel_eq_sum c.n c.h c.k c.b c.q c.A c.b_pos c.A_cont, Finset.mul_sum]
  simp_rw [h]
  rw [integral_finsetSum _ fun σ _ => c.integrable_reflected σ hN]
  rfl

/-- **The orthant atlas of a symmetric scalar-unit cell.** -/
noncomputable def symAtlas : FiniteScalarUnitAtlas t c.symIntegral where
  ι := Fin (c.n + 1) → Bool
  cell := c.reflected
  eq := fun _ hN => c.symIntegral_eq_sum hN

end ScalarUnitCell

/-! ### The conditional global theorem with scalar-unit atlases -/

namespace ResolutionCover

open Monomialize.Analytic Monomialize.VolumeScaling

variable {d : ℕ} {ι : Type*} [Fintype ι] (R : ResolutionCover d ι)

/-- The coefficient contributed by the chart–stratum pair `(i, I)` from its scalar-unit atlas. -/
noncomputable def scalarAtlasPieceCoeff {e : ι → Fin d →₀ ℕ} {Z : ι → Finset (Fin d) → ℝ → ℝ}
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas d (Z i I))
    (lam₀ : ℝ) (k₀ : ℕ) (i : ι) (I : Finset (Fin d)) : ℝ :=
  open scoped Classical in
  if hI : I ⊆ (e i).support ∧ I.Nonempty then
    ∑ j ∈ (At i I hI.1 hI.2).tied lam₀ k₀, ((At i I hI.1 hI.2).cell j).coeff
  else 0

/-- **The conditional global leading coefficient with scalar-unit atlases.** -/
theorem hasLeadingTerm_boltzmannIntegral_of_scalarAtlases (e h : ι → Fin d →₀ ℕ)
    (W : ι → Set (Fin d → ℝ)) {K : (Fin d → ℝ) → ℝ}
    (hc : ∀ i, IsMonomialChart K (R.chart i).φ (R.chart i).dom (e i) (h i) (W i)) {ε : ℝ}
    (hε : 0 < ε) {F : (Fin d → ℝ) → ℝ} {p : TubeWeight d} (hFm : Measurable F)
    (hF : Integrable (fun x => F x * p.w x) (volume.restrict (⋃ i, R.image i)))
    (hK : Measurable K) (hK0 : ∀ x, 0 ≤ K x)
    (At : ∀ (i : ι) (I : Finset (Fin d)), I ⊆ (e i).support → I.Nonempty →
      FiniteScalarUnitAtlas d (R.pieceIntegral (fun i => (e i).support) ε i I F K p))
    (lam₀ : ℝ) (k₀ : ℕ)
    (hlam : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι), lam₀ ≤ ((At i I hI hne).cell j).lam)
    (hk : ∀ (i : ι) (I : Finset (Fin d)) (hI : I ⊆ (e i).support) (hne : I.Nonempty)
      (j : (At i I hI hne).ι),
      ((At i I hI hne).cell j).lam = lam₀ → ((At i I hI hne).cell j).mult - 1 ≤ k₀) :
    HasLeadingTerm (R.boltzmannIntegral F K p)
      (∑ i, ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff At lam₀ k₀ i I) lam₀ k₀ := by
  have hmain := R.hasLeadingTerm_boltzmannIntegral_of_monomial e h W hc hε hFm hF hK hK0
    (scalarAtlasPieceCoeff At lam₀ k₀) (fun _ _ => lam₀) (fun _ _ => k₀) lam₀ k₀
    (fun i I hI => by
      obtain ⟨hpow, hne⟩ := Finset.mem_filter.1 hI
      have hsub : I ⊆ (e i).support := Finset.mem_powerset.1 hpow
      unfold scalarAtlasPieceCoeff
      rw [dif_pos ⟨hsub, hne⟩]
      exact (At i I hsub hne).hasLeadingTerm_of_extremal lam₀ k₀ (hlam i I hsub hne)
        (hk i I hsub hne))
    (fun _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
  have hcoef : ∀ i : ι, (∑ I ∈ ((e i).support.powerset.filter (fun I => I.Nonempty)).filter
      (fun _ => lam₀ = lam₀ ∧ k₀ = k₀), scalarAtlasPieceCoeff At lam₀ k₀ i I) =
      ∑ I ∈ (e i).support.powerset.filter (fun I => I.Nonempty),
        scalarAtlasPieceCoeff At lam₀ k₀ i I :=
    fun i => by rw [Finset.filter_true_of_mem fun _ _ => ⟨rfl, rfl⟩]
  beta_reduce at hmain
  rw [Finset.sum_congr rfl fun i _ => hcoef i] at hmain
  exact hmain

end ResolutionCover

end Grammar
