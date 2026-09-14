/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.SmoothInnerMonomial
import Grammar.SmoothCoordTaylor

/-!
# The two-dimensional tensor expansion of the smooth engine (consult #116, third milestone)

For a smooth amplitude `F` on `[0,b]²`, Jacobian exponents `h`, the phase `Nβ v₀^{2k₀} v₁^{2k₁}`
and a natural cutoff `L` with Taylor depths `pᵢ + hᵢ = 2kᵢL`, the tensor decomposition
`F = T₀T₁F + T₀R₁F + T₁R₀F + R₀R₁F` (`tensor_decomp`) splits the integral into
* the CORNER term: the Taylor jets `∂₀^{m₀}∂₁^{m₁}F(0)/(m₀!m₁!)` times the monomial box integrals
  `∫∫ v^{m+h} e^{−Nβ v^{2k}}` (exact; their power–log expansion with logarithmic degree `≤ 1` is
  the analytic box engine's),
* two EDGE terms, each a one-variable face integral: the inner monomial integral in the Taylor
  coordinate (`innerMono`, two-regime estimate) against the flat remainder
  `R₁^{p₁}(∂₀^{m₀}F)(0, y)` in the other coordinate, giving the coefficients
  `Γ(λ)/(2k₀ β^λ) ∫_0^b R₁^{p₁}(∂₀^{m₀}F)(0,y) y^{h₁} (y^{2k₁})^{−λ} dy · N^{−λ}`,
  `λ = (m₀+h₀+1)/(2k₀)`, with NO logarithms (`face_expansion_one`),
* the fully FLAT term `R₀R₁F`, which is `O(N^{−L})` by the elementary bound `e^{−x} ≤ C_L x^{−L}`.
★★ `twoDim_smooth`: `|∫ F v^h e^{−Nβ v^{2k}} − corner − edge₀ − edge₁| ≤ C/N^L` for `N ≥ 1`,
with an explicit constant. This is the first compatibility test of the facewise engine (Astra
#114 §1.1, #116 §6): the degree-one logarithm can only come from the corner term, and the edge
coefficients are face integrals against the flat remainders, not corner jets
(cf. `SmoothFaceRegression`). Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Real Filter Topology Finset intervalIntegral
open scoped ContDiff

namespace Grammar

namespace SmoothEngine

/-! ### Two-vector helpers -/

theorem update_vec_zero (x y t : ℝ) : Function.update ![x, y] 0 t = ![t, y] := by
  funext i; fin_cases i <;> simp

theorem update_vec_one (x y t : ℝ) : Function.update ![x, y] 1 t = ![x, t] := by
  funext i; fin_cases i <;> simp

theorem update_update_eq_zero (v : Fin 2 → ℝ) :
    Function.update (Function.update v 0 0) 1 0 = 0 := by
  funext i; fin_cases i <;> simp

theorem mono_vec (e : Fin 2 → ℕ) (x y : ℝ) : mono e ![x, y] = x ^ e 0 * y ^ e 1 := by
  simp [mono, Fin.prod_univ_two]

theorem continuous_mono {ι : Type*} [Fintype ι] (a : ι → ℕ) : Continuous (mono a) :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).pow _

theorem continuous_vec_right : Continuous fun y : ℝ => ![(0 : ℝ), y] := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using continuous_const
  · simpa using continuous_id'

theorem continuous_vec_left : Continuous fun x : ℝ => ![x, (0 : ℝ)] := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simpa using continuous_id'
  · simpa using continuous_const

theorem vec_mem_Icc {b x y : ℝ} (hx : x ∈ Icc 0 b) (hy : y ∈ Icc 0 b) :
    ∀ i, (![x, y] : Fin 2 → ℝ) i ∈ Icc 0 b := by
  intro i; fin_cases i
  · simpa using hx
  · simpa using hy

theorem mono_pow {ι : Type*} [Fintype ι] (a : ι → ℕ) (v : ι → ℝ) (L : ℕ) :
    mono a v ^ L = mono (fun i => a i * L) v := by
  simp only [mono, ← Finset.prod_pow, pow_mul]

theorem mono_mul_mono {ι : Type*} [Fintype ι] (a c : ι → ℕ) (v : ι → ℝ) :
    mono a v * mono c v = mono (fun i => a i + c i) v := by
  simp only [mono, ← Finset.prod_mul_distrib, pow_add]

theorem measureReal_box_two {b : ℝ} (hb : 0 ≤ b) : volume.real (box (Fin 2) b) = b ^ 2 := by
  rw [Measure.real, box, volume_pi_pi]
  simp [Real.volume_Ioc, ENNReal.toReal_ofReal hb]

theorem volume_box_lt_top {ι : Type*} [Fintype ι] (b : ℝ) : volume (box ι b) < ⊤ :=
  (measure_mono (show box ι b ⊆ Set.pi univ fun _ => Icc 0 b from
    fun _ hw i _ => Ioc_subset_Icc_self (hw i (Set.mem_univ i)))).trans_lt
    (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := b)).measure_lt_top

/-! ### The integral and the three explicit pieces -/

variable (F : (Fin 2 → ℝ) → ℝ) (h k p : Fin 2 → ℕ) (β b N : ℝ)

/-- The two-dimensional integral `∫_{(0,b]²} F(v) v^h e^{−Nβ v^{2k}} dv`. -/
noncomputable def twoDimIntegral : ℝ :=
  ∫ v in box (Fin 2) b, F v * mono h v * exp (-(N * β) * mono (fun i => 2 * k i) v)

/-- The monomial box integral `∫_{(0,b]²} v^e e^{−Nβ v^{2k}} dv`. -/
noncomputable def cornerMono (e : Fin 2 → ℕ) : ℝ :=
  ∫ v in box (Fin 2) b, mono e v * exp (-(N * β) * mono (fun i => 2 * k i) v)

/-- The corner term: Taylor jets at the origin times monomial box integrals. -/
noncomputable def cornerSum : ℝ :=
  ∑ m₀ ∈ range (p 0), ∑ m₁ ∈ range (p 1),
    ((m₀.factorial : ℝ)⁻¹ * (m₁.factorial : ℝ)⁻¹ * pdPow 1 m₁ (pdPow 0 m₀ F) 0) *
      cornerMono k β b N (fun i => ![m₀, m₁] i + h i)

/-- The flat edge amplitude `R₁^{p₁}(∂₀^{m₀}F)(0, y)`. -/
noncomputable def edgeAmp₀ (m₀ : ℕ) (y : ℝ) : ℝ := coordRem 1 (p 1) (pdPow 0 m₀ F) ![0, y]

/-- The flat edge amplitude `R₀^{p₀}(∂₁^{m₁}F)(x, 0)`. -/
noncomputable def edgeAmp₁ (m₁ : ℕ) (x : ℝ) : ℝ := coordRem 0 (p 0) (pdPow 1 m₁ F) ![x, 0]

/-- The edge coefficient on the face `{v₀ = 0}`:
`(1/m₀!) Γ(λ)/(2k₀) β^{−λ} ∫_0^b R₁^{p₁}(∂₀^{m₀}F)(0,y) y^{h₁} (y^{2k₁})^{−λ} dy`. -/
noncomputable def edgeCoeff₀ (m₀ : ℕ) : ℝ :=
  (m₀.factorial : ℝ)⁻¹ * (innerCoeff (k 0) (m₀ + h 0) * β ^ (-lam (k 0) (m₀ + h 0)) *
    ∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 * (y ^ (2 * k 1)) ^ (-lam (k 0) (m₀ + h 0)))

noncomputable def edgeCoeff₁ (m₁ : ℕ) : ℝ :=
  (m₁.factorial : ℝ)⁻¹ * (innerCoeff (k 1) (m₁ + h 1) * β ^ (-lam (k 1) (m₁ + h 1)) *
    ∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 * (x ^ (2 * k 0)) ^ (-lam (k 1) (m₁ + h 1)))

noncomputable def edgeSum₀ : ℝ :=
  ∑ m₀ ∈ range (p 0), N ^ (-lam (k 0) (m₀ + h 0)) * edgeCoeff₀ F h k p β b m₀

noncomputable def edgeSum₁ : ℝ :=
  ∑ m₁ ∈ range (p 1), N ^ (-lam (k 1) (m₁ + h 1)) * edgeCoeff₁ F h k p β b m₁

/-! ### The constants -/

variable (M : ℝ) (L : ℕ)

/-- The remainder constant of the edge `{v₀ = 0}` at Taylor index `m₀`. -/
noncomputable def edgeConst₀ (m₀ : ℕ) : ℝ :=
  (m₀.factorial : ℝ)⁻¹ * (innerConst (k 0) (m₀ + h 0) b L * β ^ (-(L : ℝ)) *
    (M / ((p 1 - 1).factorial : ℝ)) *
    ∫ y in Ioc 0 b, y ^ ((p 1 + h 1 : ℝ) - (2 * k 1 : ℕ) * (L : ℝ)))

noncomputable def edgeConst₁ (m₁ : ℕ) : ℝ :=
  (m₁.factorial : ℝ)⁻¹ * (innerConst (k 1) (m₁ + h 1) b L * β ^ (-(L : ℝ)) *
    (M / ((p 0 - 1).factorial : ℝ)) *
    ∫ x in Ioc 0 b, x ^ ((p 0 + h 0 : ℝ) - (2 * k 0 : ℕ) * (L : ℝ)))

/-- The remainder constant of the fully flat term. -/
noncomputable def flatConst : ℝ :=
  M / (((p 0 - 1).factorial : ℝ) * ((p 1 - 1).factorial : ℝ)) * max 1 (L.factorial : ℝ) / β ^ L *
    b ^ 2

/-- The total remainder constant. -/
noncomputable def twoDimConst : ℝ :=
  ∑ m₀ ∈ range (p 0), edgeConst₀ h k p β b M L m₀ +
    ∑ m₁ ∈ range (p 1), edgeConst₁ h k p β b M L m₁ + flatConst p β b M L

variable {F h k p β b N M L}

/-! ### Integrability on the square -/

theorem integrableOn_phase_mul {G : (Fin 2 → ℝ) → ℝ} (hG : Continuous G) (e : Fin 2 → ℕ) :
    IntegrableOn (fun v => G v * mono e v * exp (-(N * β) * mono (fun i => 2 * k i) v))
      (box (Fin 2) b) :=
  integrableOn_box_of_continuous
    ((hG.mul (continuous_mono e)).mul (continuous_exp.comp
      (continuous_const.mul (continuous_mono _)))) b

/-! ### The corner term -/

theorem corner_eq (hF : ContDiff ℝ ∞ F) :
    ∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) = cornerSum F h k p β b N := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hpt : ∀ v : Fin 2 → ℝ, coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
      ∑ m₀ ∈ range (p 0), ∑ m₁ ∈ range (p 1),
        ((m₀.factorial : ℝ)⁻¹ * (m₁.factorial : ℝ)⁻¹ * pdPow 1 m₁ (pdPow 0 m₀ F) 0) *
          (mono (fun i => ![m₀, m₁] i + h i) v * exp (-(N * β) * mono (fun i => 2 * k i) v)) := by
    intro v
    rw [coordTaylor_coordTaylor_apply hF h01, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₀ _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [update_update_eq_zero]
    have hm : v 0 ^ m₀ * v 1 ^ m₁ * mono h v = mono (fun i => ![m₀, m₁] i + h i) v := by
      simp only [mono, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_add]
      ring
    rw [← hm]
    ring
  rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v]
  unfold cornerSum cornerMono
  have hint : ∀ e : Fin 2 → ℕ, IntegrableOn
      (fun v => mono e v * exp (-(N * β) * mono (fun i => 2 * k i) v)) (box (Fin 2) b) :=
    fun e => integrableOn_box_of_continuous
      ((continuous_mono e).mul (continuous_exp.comp (continuous_const.mul (continuous_mono _)))) b
  rw [integral_finsetSum _ fun m₀ _ => integrable_finsetSum _ fun m₁ _ => (hint _).const_mul _]
  refine Finset.sum_congr rfl fun m₀ _ => ?_
  rw [integral_finsetSum _ fun m₁ _ => (hint _).const_mul _]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  exact MeasureTheory.integral_const_mul _ _

/-! ### The flat term -/

theorem flat_two (hF : ContDiff ℝ ∞ F) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) → |pdPow 0 (p 0) (pdPow 1 (p 1) F) v| ≤ M)
    (hN : 1 ≤ N) :
    |∫ v in box (Fin 2) b, coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v)| ≤ flatConst p β b M L / N ^ L := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 fun i => by simp [hb.le])
  have hNβ : 0 < N * β := by positivity
  set C : ℝ := M / (((p 0 - 1).factorial : ℝ) * ((p 1 - 1).factorial : ℝ)) *
    max 1 (L.factorial : ℝ) / (N * β) ^ L with hC
  have hbound : ∀ v ∈ box (Fin 2) b,
      ‖coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
        exp (-(N * β) * mono (fun i => 2 * k i) v)‖ ≤ C := by
    intro v hv
    have hpos := pos_of_mem_box hv
    have hvI : ∀ i, v i ∈ Icc 0 b := fun i => Ioc_subset_Icc_self (hv i (Set.mem_univ i))
    have hrem := remList_bound p hF hb hp0 [0, 1] (by decide) (M := M)
      (fun w hw => by simpa [pdList] using hM w hw) v hvI
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hrem
    have hrem' : |coordRem 0 (p 0) (coordRem 1 (p 1) F) v| ≤
        v 0 ^ p 0 / ((p 0 - 1).factorial : ℝ) * (v 1 ^ p 1 / ((p 1 - 1).factorial : ℝ)) * M :=
      hrem
    have hx : 0 < N * β * mono (fun i => 2 * k i) v := mul_pos hNβ (mono_pos _ hpos)
    have hexp : exp (-(N * β) * mono (fun i => 2 * k i) v) ≤
        max 1 (L.factorial : ℝ) / (N * β * mono (fun i => 2 * k i) v) ^ L := by
      rw [neg_mul, le_div_iff₀ (pow_pos hx L), mul_comm]
      exact pow_mul_exp_neg_le L hx
    have hmono : v 0 ^ p 0 * v 1 ^ p 1 * mono h v = mono (fun i => 2 * k i) v ^ L := by
      rw [mono_pow]
      have : (fun i => 2 * k i * L) = fun i => p i + h i := funext fun i => (hp i).symm
      rw [this, ← mono_mul_mono]
      simp only [mono, Fin.prod_univ_two]
    have hmh : 0 < mono h v := mono_pos h hpos
    have hE : 0 < exp (-(N * β) * mono (fun i => 2 * k i) v) := exp_pos _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hmh, abs_of_pos hE]
    have hf0 : (0 : ℝ) < (p 0 - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hf1 : (0 : ℝ) < (p 1 - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    calc |coordRem 0 (p 0) (coordRem 1 (p 1) F) v| * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)
        ≤ (v 0 ^ p 0 / ((p 0 - 1).factorial : ℝ) * (v 1 ^ p 1 / ((p 1 - 1).factorial : ℝ)) * M) *
            mono h v * (max 1 (L.factorial : ℝ) / (N * β * mono (fun i => 2 * k i) v) ^ L) := by
          have h0 := hpos 0
          have h1 := hpos 1
          gcongr
      _ = M / (((p 0 - 1).factorial : ℝ) * ((p 1 - 1).factorial : ℝ)) * max 1 (L.factorial : ℝ) *
            ((v 0 ^ p 0 * v 1 ^ p 1 * mono h v) / (N * β * mono (fun i => 2 * k i) v) ^ L) := by
          ring
      _ = C := by
          rw [hmono, mul_pow, hC]
          have : mono (fun i => 2 * k i) v ^ L ≠ 0 := (pow_pos (mono_pos _ hpos) L).ne'
          field_simp
  have hvol := volume_box_lt_top (ι := Fin 2) b
  have := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [Real.norm_eq_abs, measureReal_box_two hb.le] at this
  refine this.trans (le_of_eq ?_)
  rw [hC, flatConst, mul_pow]
  field_simp


/-! ### The edge terms -/

theorem continuous_edgeAmp₀ (hF : ContDiff ℝ ∞ F) (m₀ : ℕ) : Continuous (edgeAmp₀ F p m₀) :=
  (contDiff_coordRem (contDiff_pdPow hF 0 m₀) 1 (p 1)).continuous.comp continuous_vec_right

theorem continuous_edgeAmp₁ (hF : ContDiff ℝ ∞ F) (m₁ : ℕ) : Continuous (edgeAmp₁ F p m₁) :=
  (contDiff_coordRem (contDiff_pdPow hF 1 m₁) 0 (p 0)).continuous.comp continuous_vec_left

/-- The inner integral in the first coordinate is the inner monomial integral at `β N y^{2k₁}`. -/
theorem inner_first (hb : 0 < b) (e : ℕ) (y : ℝ) :
    ∫ x in Ioc 0 b, x ^ e * exp (-(N * β) * (x ^ (2 * k 0) * y ^ (2 * k 1))) =
      innerMono (k 0) e b (β * (N * y ^ (2 * k 1))) := by
  unfold innerMono
  rw [intervalIntegral.integral_of_le hb.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  congr 2
  ring

theorem inner_second (hb : 0 < b) (e : ℕ) (x : ℝ) :
    ∫ y in Ioc 0 b, y ^ e * exp (-(N * β) * (x ^ (2 * k 0) * y ^ (2 * k 1))) =
      innerMono (k 1) e b (β * (N * x ^ (2 * k 0))) := by
  unfold innerMono
  rw [intervalIntegral.integral_of_le hb.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  congr 2
  ring

/-- The edge term on `{v₀ = 0}` as a sum of one-variable face integrals. -/
theorem edge₀_eq (hF : ContDiff ℝ ∞ F) (hb : 0 < b) :
    ∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
    ∑ m₀ ∈ range (p 0), (m₀.factorial : ℝ)⁻¹ *
      ∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
        innerMono (k 0) (m₀ + h 0) b (β * (N * y ^ (2 * k 1))) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  set G : ℕ → (Fin 2 → ℝ) → ℝ := fun m₀ v =>
    v 0 ^ m₀ * coordRem 1 (p 1) (pdPow 0 m₀ F) (Function.update v 0 0) * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) with hG
  have hGc : ∀ m₀, Continuous (G m₀) := fun m₀ => by
    simp only [hG]
    exact (((continuous_apply 0).pow _).mul
      ((contDiff_coordRem (contDiff_pdPow hF 0 m₀) 1 (p 1)).continuous.comp
        (contDiff_setZero 0).continuous)).mul (continuous_mono h) |>.mul
      (continuous_exp.comp (continuous_const.mul (continuous_mono _)))
  have hpt : ∀ v : Fin 2 → ℝ, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
      ∑ m₀ ∈ range (p 0), (m₀.factorial : ℝ)⁻¹ * G m₀ v := by
    intro v
    rw [coordTaylor_apply, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₀ _ => ?_
    rw [pdPow_coordRem hF h01]
    simp only [hG]
    ring
  rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v,
    integral_finsetSum _ fun m₀ _ => (integrableOn_box_of_continuous (hGc m₀) b).const_mul _]
  refine Finset.sum_congr rfl fun m₀ _ => ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_box_two' b (G m₀) (integrableOn_box_of_continuous (hGc m₀) b)]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  simp only [hG, update_vec_zero, mono_vec, Matrix.cons_val_zero]
  rw [← inner_first hb, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only [edgeAmp₀]
  rw [pow_add]
  ring

/-- The edge term on `{v₁ = 0}` as a sum of one-variable face integrals. -/
theorem edge₁_eq (hF : ContDiff ℝ ∞ F) (hb : 0 < b) :
    ∫ v in box (Fin 2) b, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
    ∑ m₁ ∈ range (p 1), (m₁.factorial : ℝ)⁻¹ *
      ∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
        innerMono (k 1) (m₁ + h 1) b (β * (N * x ^ (2 * k 0))) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set G : ℕ → (Fin 2 → ℝ) → ℝ := fun m₁ v =>
    v 1 ^ m₁ * coordRem 0 (p 0) (pdPow 1 m₁ F) (Function.update v 1 0) * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) with hG
  have hGc : ∀ m₁, Continuous (G m₁) := fun m₁ => by
    simp only [hG]
    exact (((continuous_apply 1).pow _).mul
      ((contDiff_coordRem (contDiff_pdPow hF 1 m₁) 0 (p 0)).continuous.comp
        (contDiff_setZero 1).continuous)).mul (continuous_mono h) |>.mul
      (continuous_exp.comp (continuous_const.mul (continuous_mono _)))
  have hpt : ∀ v : Fin 2 → ℝ, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v *
      exp (-(N * β) * mono (fun i => 2 * k i) v) =
      ∑ m₁ ∈ range (p 1), (m₁.factorial : ℝ)⁻¹ * G m₁ v := by
    intro v
    rw [coordTaylor_apply, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [pdPow_coordRem hF h10]
    simp only [hG]
    ring
  rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v,
    integral_finsetSum _ fun m₁ _ => (integrableOn_box_of_continuous (hGc m₁) b).const_mul _]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_box_two b (G m₁) (integrableOn_box_of_continuous (hGc m₁) b)]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only [hG, update_vec_one, mono_vec, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [← inner_second hb, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  simp only [edgeAmp₁]
  rw [pow_add]
  ring

/-- The flatness of the edge amplitude: `|R₁^{p₁}(∂₀^{m₀}F)(0,y)| ≤ M/(p₁−1)! · y^{p₁}`. -/
theorem edgeAmp₀_bound (hF : ContDiff ℝ ∞ F) (hb : 0 < b) (hp0 : 0 < p 1) {m₀ : ℕ}
    (hM : ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) → |pdPow 1 (p 1) (pdPow 0 m₀ F) v| ≤ M) :
    ∀ y ∈ Ioc 0 b, |edgeAmp₀ F p m₀ y| ≤ M / ((p 1 - 1).factorial : ℝ) * y ^ p 1 := by
  intro y hy
  have hy' : y ∈ Icc 0 b := Ioc_subset_Icc_self hy
  obtain ⟨q, hq⟩ : ∃ q, p 1 = q + 1 := ⟨p 1 - 1, (Nat.sub_add_cancel hp0).symm⟩
  have hC : ∀ t ∈ Icc 0 b,
      |pdPow 1 (q + 1) (pdPow 0 m₀ F) (Function.update ![(0 : ℝ), y] 1 t)| ≤ M := fun t ht => by
    rw [update_vec_one, ← hq]
    exact hM _ (vec_mem_Icc ⟨le_rfl, hb.le⟩ ht)
  have key := coordRem_bound (contDiff_pdPow hF 0 m₀) 1 q hb (v := ![0, y]) (by simpa using hy') hC
  unfold edgeAmp₀
  rw [hq, Nat.add_sub_cancel]
  calc |coordRem 1 (q + 1) (pdPow 0 m₀ F) ![0, y]| ≤ M * y ^ (q + 1) / (q.factorial : ℝ) := by
        simpa using key
    _ = M / (q.factorial : ℝ) * y ^ (q + 1) := by ring

theorem edgeAmp₁_bound (hF : ContDiff ℝ ∞ F) (hb : 0 < b) (hp0 : 0 < p 0) {m₁ : ℕ}
    (hM : ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) → |pdPow 0 (p 0) (pdPow 1 m₁ F) v| ≤ M) :
    ∀ x ∈ Ioc 0 b, |edgeAmp₁ F p m₁ x| ≤ M / ((p 0 - 1).factorial : ℝ) * x ^ p 0 := by
  intro x hx
  have hx' : x ∈ Icc 0 b := Ioc_subset_Icc_self hx
  obtain ⟨q, hq⟩ : ∃ q, p 0 = q + 1 := ⟨p 0 - 1, (Nat.sub_add_cancel hp0).symm⟩
  have hC : ∀ t ∈ Icc 0 b,
      |pdPow 0 (q + 1) (pdPow 1 m₁ F) (Function.update ![x, (0 : ℝ)] 0 t)| ≤ M := fun t ht => by
    rw [update_vec_zero, ← hq]
    exact hM _ (vec_mem_Icc ht ⟨le_rfl, hb.le⟩)
  have key := coordRem_bound (contDiff_pdPow hF 1 m₁) 0 q hb (v := ![x, 0]) (by simpa using hx') hC
  unfold edgeAmp₁
  rw [hq, Nat.add_sub_cancel]
  calc |coordRem 0 (q + 1) (pdPow 1 m₁ F) ![x, 0]| ≤ M * x ^ (q + 1) / (q.factorial : ℝ) := by
        simpa using key
    _ = M / (q.factorial : ℝ) * x ^ (q + 1) := by ring

/-- `λ_{m+h} ≤ L` for `m < p` when `p + h = 2kL`. -/
theorem lam_le_of_lt {k p h L m : ℕ} (hk : 0 < k) (hp : p + h = 2 * k * L) (hm : m < p) :
    lam k (m + h) ≤ L := by
  unfold lam
  rw [div_le_iff₀ (by positivity)]
  have hnat : m + h + 1 ≤ 2 * k * L := by rw [← hp]; omega
  have hreal : ((m + h + 1 : ℕ) : ℝ) ≤ ((2 * k * L : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hreal ⊢
  linarith

/-- The convergence condition `a L < p + h + 1` for `p + h = aL`. -/
theorem convergence_of_eq {k p h L : ℕ} (hp : p + h = 2 * k * L) :
    ((2 * k : ℕ) : ℝ) * (L : ℝ) < (p : ℝ) + h + 1 := by
  have : ((2 * k : ℕ) : ℝ) * L = (p : ℝ) + h := by exact_mod_cast hp.symm
  linarith

/-- ★ One edge integral: the face theorem with the inner monomial integral. -/
theorem edge₀_face (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ m₀ ≤ p 0, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 1 (p 1) (pdPow 0 m₀ F) v| ≤ M)
    (hN : 1 ≤ N) {m₀ : ℕ} (hm₀ : m₀ < p 0) :
    |(∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
        innerMono (k 0) (m₀ + h 0) b (β * (N * y ^ (2 * k 1)))) -
      N ^ (-lam (k 0) (m₀ + h 0)) * (innerCoeff (k 0) (m₀ + h 0) * β ^ (-lam (k 0) (m₀ + h 0)) *
        ∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 * (y ^ (2 * k 1)) ^ (-lam (k 0) (m₀ + h 0)))| ≤
      innerConst (k 0) (m₀ + h 0) b L * β ^ (-(L : ℝ)) * (M / ((p 1 - 1).factorial : ℝ)) *
        N ^ (-(L : ℝ)) * ∫ y in Ioc 0 b, y ^ ((p 1 + h 1 : ℝ) - (2 * k 1 : ℕ) * (L : ℝ)) := by
  have hL : lam (k 0) (m₀ + h 0) ≤ L := lam_le_of_lt (hk 0) (hp 0) hm₀
  have key := face_expansion_one (G := edgeAmp₀ F p m₀)
    (Z' := fun t => innerMono (k 0) (m₀ + h 0) b (β * t)) (p := p 1) (h := h 1) (a := 2 * k 1)
    (Λ := {lam (k 0) (m₀ + h 0)}) (D := 0) (c := fun μ _ => innerCoeff (k 0) (m₀ + h 0) * β ^ (-μ))
    (C := innerConst (k 0) (m₀ + h 0) b L * β ^ (-(L : ℝ))) (L := (L : ℝ))
    (M := M / ((p 1 - 1).factorial : ℝ)) hb (continuous_edgeAmp₀ hF m₀)
    (edgeAmp₀_bound hF hb (hp0 1) (hM m₀ hm₀.le))
    ((continuous_innerMono _ _ _).comp (continuous_const.mul continuous_id)).measurable
    (fun t ht => innerMono_two_regime_beta (hk 0) (m₀ + h 0) hb hβ L hL ht)
    (fun μ hμ => (Finset.mem_singleton.1 hμ) ▸ hL) (convergence_of_eq (hp 1)) hN
  simpa only [Finset.sum_singleton, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, Nat.sub_zero] using key

theorem edge₁_face (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ m₁ ≤ p 1, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 0 (p 0) (pdPow 1 m₁ F) v| ≤ M)
    (hN : 1 ≤ N) {m₁ : ℕ} (hm₁ : m₁ < p 1) :
    |(∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
        innerMono (k 1) (m₁ + h 1) b (β * (N * x ^ (2 * k 0)))) -
      N ^ (-lam (k 1) (m₁ + h 1)) * (innerCoeff (k 1) (m₁ + h 1) * β ^ (-lam (k 1) (m₁ + h 1)) *
        ∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 * (x ^ (2 * k 0)) ^ (-lam (k 1) (m₁ + h 1)))| ≤
      innerConst (k 1) (m₁ + h 1) b L * β ^ (-(L : ℝ)) * (M / ((p 0 - 1).factorial : ℝ)) *
        N ^ (-(L : ℝ)) * ∫ x in Ioc 0 b, x ^ ((p 0 + h 0 : ℝ) - (2 * k 0 : ℕ) * (L : ℝ)) := by
  have hL : lam (k 1) (m₁ + h 1) ≤ L := lam_le_of_lt (hk 1) (hp 1) hm₁
  have key := face_expansion_one (G := edgeAmp₁ F p m₁)
    (Z' := fun t => innerMono (k 1) (m₁ + h 1) b (β * t)) (p := p 0) (h := h 0) (a := 2 * k 0)
    (Λ := {lam (k 1) (m₁ + h 1)}) (D := 0) (c := fun μ _ => innerCoeff (k 1) (m₁ + h 1) * β ^ (-μ))
    (C := innerConst (k 1) (m₁ + h 1) b L * β ^ (-(L : ℝ))) (L := (L : ℝ))
    (M := M / ((p 0 - 1).factorial : ℝ)) hb (continuous_edgeAmp₁ hF m₁)
    (edgeAmp₁_bound hF hb (hp0 0) (hM m₁ hm₁.le))
    ((continuous_innerMono _ _ _).comp (continuous_const.mul continuous_id)).measurable
    (fun t ht => innerMono_two_regime_beta (hk 1) (m₁ + h 1) hb hβ L hL ht)
    (fun μ hμ => (Finset.mem_singleton.1 hμ) ▸ hL) (convergence_of_eq (hp 0)) hN
  simpa only [Finset.sum_singleton, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, Nat.sub_zero] using key

theorem rpow_neg_natCast_eq {N : ℝ} (hN : 1 ≤ N) (L : ℕ) : N ^ (-(L : ℝ)) = 1 / N ^ L := by
  rw [rpow_neg (by linarith), rpow_natCast, one_div]

/-- The edge `{v₀ = 0}`: integral minus its expansion is `O(N^{−L})`. -/
theorem edge₀_bound (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ m₀ ≤ p 0, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 1 (p 1) (pdPow 0 m₀ F) v| ≤ M)
    (hN : 1 ≤ N) :
    |(∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
        exp (-(N * β) * mono (fun i => 2 * k i) v)) - edgeSum₀ F h k p β b N| ≤
      (∑ m₀ ∈ range (p 0), edgeConst₀ h k p β b M L m₀) / N ^ L := by
  rw [edge₀_eq hF hb, edgeSum₀, ← Finset.sum_sub_distrib, div_eq_mul_one_div,
    ← rpow_neg_natCast_eq hN, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m₀ hm₀ => ?_)
  have hface := edge₀_face hF hk hβ hb hp hp0 hM hN (mem_range.1 hm₀)
  have hfac : (0 : ℝ) ≤ (m₀.factorial : ℝ)⁻¹ := by positivity
  rw [edgeCoeff₀, edgeConst₀]
  calc |(m₀.factorial : ℝ)⁻¹ * (∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
          innerMono (k 0) (m₀ + h 0) b (β * (N * y ^ (2 * k 1)))) -
        N ^ (-lam (k 0) (m₀ + h 0)) * ((m₀.factorial : ℝ)⁻¹ *
          (innerCoeff (k 0) (m₀ + h 0) * β ^ (-lam (k 0) (m₀ + h 0)) *
            ∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
              (y ^ (2 * k 1)) ^ (-lam (k 0) (m₀ + h 0))))|
        = (m₀.factorial : ℝ)⁻¹ * |(∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
            innerMono (k 0) (m₀ + h 0) b (β * (N * y ^ (2 * k 1)))) -
          N ^ (-lam (k 0) (m₀ + h 0)) * (innerCoeff (k 0) (m₀ + h 0) *
            β ^ (-lam (k 0) (m₀ + h 0)) * ∫ y in Ioc 0 b, edgeAmp₀ F p m₀ y * y ^ h 1 *
              (y ^ (2 * k 1)) ^ (-lam (k 0) (m₀ + h 0)))| := by
          rw [← abs_of_nonneg hfac, ← abs_mul, abs_of_nonneg hfac]
          congr 1
          ring
      _ ≤ (m₀.factorial : ℝ)⁻¹ * (innerConst (k 0) (m₀ + h 0) b L * β ^ (-(L : ℝ)) *
            (M / ((p 1 - 1).factorial : ℝ)) * N ^ (-(L : ℝ)) *
            ∫ y in Ioc 0 b, y ^ ((p 1 + h 1 : ℝ) - (2 * k 1 : ℕ) * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hface hfac
      _ = _ := by ring

theorem edge₁_bound (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ m₁ ≤ p 1, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 0 (p 0) (pdPow 1 m₁ F) v| ≤ M)
    (hN : 1 ≤ N) :
    |(∫ v in box (Fin 2) b, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v *
        exp (-(N * β) * mono (fun i => 2 * k i) v)) - edgeSum₁ F h k p β b N| ≤
      (∑ m₁ ∈ range (p 1), edgeConst₁ h k p β b M L m₁) / N ^ L := by
  rw [edge₁_eq hF hb, edgeSum₁, ← Finset.sum_sub_distrib, div_eq_mul_one_div,
    ← rpow_neg_natCast_eq hN, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m₁ hm₁ => ?_)
  have hface := edge₁_face hF hk hβ hb hp hp0 hM hN (mem_range.1 hm₁)
  have hfac : (0 : ℝ) ≤ (m₁.factorial : ℝ)⁻¹ := by positivity
  rw [edgeCoeff₁, edgeConst₁]
  calc |(m₁.factorial : ℝ)⁻¹ * (∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
          innerMono (k 1) (m₁ + h 1) b (β * (N * x ^ (2 * k 0)))) -
        N ^ (-lam (k 1) (m₁ + h 1)) * ((m₁.factorial : ℝ)⁻¹ *
          (innerCoeff (k 1) (m₁ + h 1) * β ^ (-lam (k 1) (m₁ + h 1)) *
            ∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
              (x ^ (2 * k 0)) ^ (-lam (k 1) (m₁ + h 1))))|
        = (m₁.factorial : ℝ)⁻¹ * |(∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
            innerMono (k 1) (m₁ + h 1) b (β * (N * x ^ (2 * k 0)))) -
          N ^ (-lam (k 1) (m₁ + h 1)) * (innerCoeff (k 1) (m₁ + h 1) *
            β ^ (-lam (k 1) (m₁ + h 1)) * ∫ x in Ioc 0 b, edgeAmp₁ F p m₁ x * x ^ h 0 *
              (x ^ (2 * k 0)) ^ (-lam (k 1) (m₁ + h 1)))| := by
          rw [← abs_of_nonneg hfac, ← abs_mul, abs_of_nonneg hfac]
          congr 1
          ring
      _ ≤ (m₁.factorial : ℝ)⁻¹ * (innerConst (k 1) (m₁ + h 1) b L * β ^ (-(L : ℝ)) *
            (M / ((p 0 - 1).factorial : ℝ)) * N ^ (-(L : ℝ)) *
            ∫ x in Ioc 0 b, x ^ ((p 0 + h 0 : ℝ) - (2 * k 0 : ℕ) * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hface hfac
      _ = _ := by ring

/-! ### The two-dimensional smooth expansion -/

/-- ★★ **The two-dimensional smooth expansion**: for smooth `F` with rectangular mixed-derivative
bound `|∂₀^{m₀}∂₁^{m₁}F| ≤ M` on `[0,b]²` (`m₀ ≤ p₀`, `m₁ ≤ p₁`), Jacobian exponents `h`, phase
`Nβ v₀^{2k₀} v₁^{2k₁}` and depths `pᵢ + hᵢ = 2kᵢL`: the integral equals the corner term (Taylor
jets × monomial box integrals) plus the two edge terms (face integrals against the flat
remainders, exponents `λ = (m+h+1)/(2k)`, no logarithms) up to `C/N^L`, for `N ≥ 1`. -/
theorem twoDim_smooth (hF : ContDiff ℝ ∞ F) (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hp : ∀ i, p i + h i = 2 * k i * L) (hp0 : ∀ i, 0 < p i)
    (hM : ∀ m₀ ≤ p 0, ∀ m₁ ≤ p 1, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 1 m₁ (pdPow 0 m₀ F) v| ≤ M)
    (hN : 1 ≤ N) :
    |twoDimIntegral F h k β b N - cornerSum F h k p β b N - edgeSum₀ F h k p β b N -
        edgeSum₁ F h k p β b N| ≤ twoDimConst h k p β b M L / N ^ L := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  set E : (Fin 2 → ℝ) → ℝ := fun v => exp (-(N * β) * mono (fun i => 2 * k i) v) with hE
  have hEc : Continuous E := continuous_exp.comp (continuous_const.mul (continuous_mono _))
  have hint : ∀ G : (Fin 2 → ℝ) → ℝ, Continuous G →
      IntegrableOn (fun v => G v * mono h v * E v) (box (Fin 2) b) := fun G hG =>
    integrableOn_box_of_continuous ((hG.mul (continuous_mono h)).mul hEc) b
  have hTT := contDiff_coordTaylor (contDiff_coordTaylor hF 1 (p 1)) 0 (p 0)
  have hTR := contDiff_coordTaylor (contDiff_coordRem hF 1 (p 1)) 0 (p 0)
  have hRT := contDiff_coordTaylor (contDiff_coordRem hF 0 (p 0)) 1 (p 1)
  have hRR := contDiff_coordRem (contDiff_coordRem hF 1 (p 1)) 0 (p 0)
  have hsplit : twoDimIntegral F h k β b N =
      (∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v * E v) +
      (∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v) +
      (∫ v in box (Fin 2) b, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v * E v) +
      ∫ v in box (Fin 2) b, coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v := by
    have hpt : ∀ v : Fin 2 → ℝ, F v * mono h v * E v =
        coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v * E v +
        coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v +
        coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v * E v +
        coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v := fun v => by
      rw [tensor_decomp hF h01 (p 1) (p 0) v]
      ring
    have hAB : IntegrableOn (fun v => coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v *
        E v + coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v) (box (Fin 2) b) :=
      (hint _ hTT.continuous).add (hint _ hTR.continuous)
    have hABC : IntegrableOn (fun v => coordTaylor 0 (p 0) (coordTaylor 1 (p 1) F) v * mono h v *
        E v + coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v * E v +
        coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v * E v) (box (Fin 2) b) :=
      hAB.add (hint _ hRT.continuous)
    unfold twoDimIntegral
    rw [setIntegral_congr_fun (measurableSet_box b) fun v _ => hpt v,
      integral_add hABC (hint _ hRR.continuous), integral_add hAB (hint _ hRT.continuous),
      integral_add (hint _ hTT.continuous) (hint _ hTR.continuous)]
  have hM' : ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 0 (p 0) (pdPow 1 (p 1) F) v| ≤ M := fun v hv => by
    rw [pdPow_comm hF]; exact hM _ le_rfl _ le_rfl v hv
  have hM₁ : ∀ m₁ ≤ p 1, ∀ v : Fin 2 → ℝ, (∀ i, v i ∈ Icc 0 b) →
      |pdPow 0 (p 0) (pdPow 1 m₁ F) v| ≤ M := fun m₁ hm₁ v hv => by
    rw [pdPow_comm hF]; exact hM _ le_rfl _ hm₁ v hv
  have hflat := flat_two hF hβ hb hp hp0 hM' hN
  have hedge₀ := edge₀_bound hF hk hβ hb hp hp0 (fun m₀ hm₀ => hM m₀ hm₀ _ le_rfl) hN
  have hedge₁ := edge₁_bound hF hk hβ hb hp hp0 hM₁ hN
  have hcorner := corner_eq (h := h) (k := k) (p := p) (β := β) (b := b) (N := N) hF
  rw [hsplit]
  simp only [hE] at hcorner hflat hedge₀ hedge₁ ⊢
  rw [hcorner, twoDimConst, add_div, add_div]
  calc |cornerSum F h k p β b N +
        (∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)) +
        (∫ v in box (Fin 2) b, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)) +
        (∫ v in box (Fin 2) b, coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)) -
        cornerSum F h k p β b N - edgeSum₀ F h k p β b N - edgeSum₁ F h k p β b N|
      = |((∫ v in box (Fin 2) b, coordTaylor 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)) - edgeSum₀ F h k p β b N) +
        ((∫ v in box (Fin 2) b, coordTaylor 1 (p 1) (coordRem 0 (p 0) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)) - edgeSum₁ F h k p β b N) +
        ∫ v in box (Fin 2) b, coordRem 0 (p 0) (coordRem 1 (p 1) F) v * mono h v *
          exp (-(N * β) * mono (fun i => 2 * k i) v)| := by
        congr 1; ring
    _ ≤ _ := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans (add_le_add hedge₀ hedge₁)) hflat

end SmoothEngine

end Grammar
