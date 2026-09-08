/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Grammar.BoxTaylorTree
import Grammar.TaylorTreeWrapper

/-!
# The weighted-ℓ¹ data space for the stochastic Taylor tree (Stage S1 — statement lock)

Unit 270 (Astra #33, unit 1 of the §4.3 programme). The paper's coefficient functionals
`C_{μ,m}(ξ, η)` are functions of the Taylor data of the phase `ξ` and the amplitude `η`. The
natural Banach space of such data at box radius `b` is
`E_b = {c : ℕ^d → ℝ | ‖c‖_b = ∑_γ |c_γ| b^{|γ|} < ∞}`, and the pair `(cξ, cη) ∈ E_b × E_b`. We
represent it through the isometry `c ↦ (γ ↦ b^{|γ|} c_γ)` as ordinary real `ℓ¹` over the disjoint
union `DataIdx d = (Fin d → ℕ) ⊕ (Fin d → ℕ)`: `DataSpace d = lp (fun _ => ℝ) 1`. Its coordinates
`xiCoord x`, `etaCoord x` are exactly the *rescaled unit-box families* `scale cξ b`, `scale cη b`
of the Taylor tree, and `toXi b x`, `toEta b x` recover the box families `cξ, cη`
(`scale_toXi`). The norm is the sum of the two masses (`norm_eq_mass_add_mass`), coordinate
evaluation is 1-Lipschitz (`lipschitzWith_coord`; in particular the constant phase
`constPhase x = ξ(0)` is continuous), and `ofFamilies` embeds any pair of weighted-summable
families.

The canonical paper-facing coefficient map on the data space is
`dataBoxCoeff n h k β b x μ j = boxCoeff n h k β b (toXi b x) (toEta b x) μ j`, the actual
coefficient of `N^{-μ} (log N)^j` in the expansion of the original box integral
`dataBoxIntegral n h k β N b x = Z(N; ξ, η)`; `taylorTree_data` transports Headline XXVIII/★ to
data-space elements, and `dataBoxCoeff_eq` expresses the map through the unit-box spectral
coefficients of the raw coordinates (`familySpectralCoeff … (xiCoord x) (etaCoord x)`), which is
the form the continuity estimates of the following units address.

**Programme statements (locked here, proved in later units).** A1: for fixed `μ > 0`, `j`, and
every `R`, `x ↦ dataBoxCoeff … x μ j` is Lipschitz on the ball `‖x‖ ≤ R` and hence continuous
and measurable; finite vectors of coefficients are continuous. A2: if `X_n ⇒ X` in distribution
as `DataSpace`-valued random elements, every finite coefficient vector converges in distribution,
and for `N_n → ∞` the ordered normalised remainders
`(Z(N_n; X_n) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(X_n) N_n^{-ν} (log N_n)^q) / (N_n^{-μ} (log N_n)^j)`
converge in distribution to `C_{μ,j}(X)`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

variable {d : ℕ}

/-- Index of the pair (phase, amplitude) of coefficient families. -/
abbrev DataIdx (d : ℕ) : Type := (Fin d → ℕ) ⊕ (Fin d → ℕ)

/-- The weighted-ℓ¹ data space `E_b × E_b` in rescaled coordinates: `ℓ¹(DataIdx d, ℝ)`. -/
abbrev DataSpace (d : ℕ) : Type := lp (fun _ : DataIdx d => ℝ) 1

noncomputable instance : MeasurableSpace (DataSpace d) := borel (DataSpace d)
instance : BorelSpace (DataSpace d) := ⟨rfl⟩

/-- The rescaled unit-box phase family: the raw phase coordinates. -/
def xiCoord (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inl γ)

/-- The rescaled unit-box amplitude family: the raw amplitude coordinates. -/
def etaCoord (x : DataSpace d) : CoeffFamily d := fun γ => x (Sum.inr γ)

/-- The box phase family `cξ_γ = x(inl γ) b^{-|γ|}`. -/
noncomputable def toXi (b : ℝ) (x : DataSpace d) : CoeffFamily d :=
  fun γ => x (Sum.inl γ) / b ^ (∑ i, γ i)

/-- The box amplitude family `cη_γ = x(inr γ) b^{-|γ|}`. -/
noncomputable def toEta (b : ℝ) (x : DataSpace d) : CoeffFamily d :=
  fun γ => x (Sum.inr γ) / b ^ (∑ i, γ i)

/-- The constant phase `ξ(0)`. -/
def constPhase (x : DataSpace d) : ℝ := x (Sum.inl 0)

theorem summable_abs_coord (x : DataSpace d) : Summable fun i => |x i| := by
  have h := (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp x)
  simpa using h

theorem dataNorm_eq_tsum_abs (x : DataSpace d) : ‖x‖ = ∑' i, |x i| := by
  rw [lp.norm_eq_tsum_rpow (by simp) x]
  simp

theorem absSummable_xiCoord (x : DataSpace d) : AbsSummable (xiCoord x) :=
  (summable_abs_coord x).comp_injective Sum.inl_injective

theorem absSummable_etaCoord (x : DataSpace d) : AbsSummable (etaCoord x) :=
  (summable_abs_coord x).comp_injective Sum.inr_injective

/-- The norm is the sum of the two masses. -/
theorem norm_eq_mass_add_mass (x : DataSpace d) :
    ‖x‖ = mass (xiCoord x) + mass (etaCoord x) := by
  rw [dataNorm_eq_tsum_abs]
  have h1 : HasSum ((fun i : DataIdx d => |x i|) ∘ Sum.inl) (mass (xiCoord x)) :=
    (absSummable_xiCoord x).hasSum
  have h2 : HasSum ((fun i : DataIdx d => |x i|) ∘ Sum.inr) (mass (etaCoord x)) :=
    (absSummable_etaCoord x).hasSum
  exact (HasSum.sum h1 h2).tsum_eq

theorem mass_xiCoord_le (x : DataSpace d) : mass (xiCoord x) ≤ ‖x‖ := by
  rw [norm_eq_mass_add_mass]; linarith [mass_nonneg (etaCoord x)]

theorem mass_etaCoord_le (x : DataSpace d) : mass (etaCoord x) ≤ ‖x‖ := by
  rw [norm_eq_mass_add_mass]; linarith [mass_nonneg (xiCoord x)]

theorem xiCoord_sub (x y : DataSpace d) : xiCoord (x - y) = fun γ => xiCoord x γ - xiCoord y γ := by
  funext γ; simp [xiCoord]

theorem etaCoord_sub (x y : DataSpace d) :
    etaCoord (x - y) = fun γ => etaCoord x γ - etaCoord y γ := by
  funext γ; simp [etaCoord]

theorem mass_xiCoord_sub_le (x y : DataSpace d) :
    mass (fun γ => xiCoord x γ - xiCoord y γ) ≤ ‖x - y‖ := by
  rw [← xiCoord_sub]; exact mass_xiCoord_le _

theorem mass_etaCoord_sub_le (x y : DataSpace d) :
    mass (fun γ => etaCoord x γ - etaCoord y γ) ≤ ‖x - y‖ := by
  rw [← etaCoord_sub]; exact mass_etaCoord_le _

/-- Coordinate evaluation is 1-Lipschitz. -/
theorem lipschitzWith_coord (i : DataIdx d) : LipschitzWith 1 fun x : DataSpace d => x i := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have := lp.norm_apply_le_norm (p := 1) (by simp) (x - y) i
  simpa using this

theorem continuous_coord (i : DataIdx d) : Continuous fun x : DataSpace d => x i :=
  (lipschitzWith_coord i).continuous

theorem abs_coord_sub_le (x y : DataSpace d) (i : DataIdx d) : |x i - y i| ≤ ‖x - y‖ := by
  have := (lipschitzWith_coord i).dist_le_mul x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at this
  exact this

theorem continuous_constPhase : Continuous fun x : DataSpace d => constPhase x :=
  continuous_coord _

theorem measurable_constPhase : Measurable fun x : DataSpace d => constPhase x :=
  continuous_constPhase.measurable

/-- The rescaled box family is the raw coordinate family. -/
theorem scale_toXi {b : ℝ} (hb : b ≠ 0) (x : DataSpace d) : scale (toXi b x) b = xiCoord x := by
  funext γ
  simp only [scale, toXi, xiCoord]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hb)

theorem scale_toEta {b : ℝ} (hb : b ≠ 0) (x : DataSpace d) : scale (toEta b x) b = etaCoord x := by
  funext γ
  simp only [scale, toEta, etaCoord]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hb)

theorem absSummableAt_toXi {b : ℝ} (hb : 0 < b) (x : DataSpace d) : AbsSummableAt (toXi b x) b := by
  unfold AbsSummableAt
  refine (absSummable_xiCoord x).congr fun γ => ?_
  simp only [xiCoord, toXi]
  rw [abs_div, abs_of_pos (pow_pos hb _), div_mul_cancel₀ _ (pow_pos hb _).ne']

theorem absSummableAt_toEta {b : ℝ} (hb : 0 < b) (x : DataSpace d) :
    AbsSummableAt (toEta b x) b := by
  unfold AbsSummableAt
  refine (absSummable_etaCoord x).congr fun γ => ?_
  simp only [etaCoord, toEta]
  rw [abs_div, abs_of_pos (pow_pos hb _), div_mul_cancel₀ _ (pow_pos hb _).ne']

theorem toXi_zero (b : ℝ) (x : DataSpace d) : toXi b x 0 = constPhase x := by
  simp [toXi, constPhase]

/-- The data-space element representing a pair of weighted-summable families. -/
noncomputable def ofFamilies (b : ℝ) (hb : 0 < b) (cξ cη : CoeffFamily d) (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) : DataSpace d :=
  ⟨Sum.elim (fun γ => cξ γ * b ^ (∑ i, γ i)) (fun γ => cη γ * b ^ (∑ i, γ i)), by
    change Memℓp _ 1
    rw [memℓp_gen_iff (p := 1) (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
    unfold AbsSummableAt at hξ hη
    have hξ' : Summable fun γ : Fin d → ℕ => |cξ γ * b ^ (∑ i, γ i)| :=
      hξ.congr fun γ => by rw [abs_mul, abs_of_pos (pow_pos hb _)]
    have hη' : Summable fun γ : Fin d → ℕ => |cη γ * b ^ (∑ i, γ i)| :=
      hη.congr fun γ => by rw [abs_mul, abs_of_pos (pow_pos hb _)]
    refine Summable.sum _ ?_ ?_
    · exact hξ'.congr fun γ => by simp
    · exact hη'.congr fun γ => by simp⟩

theorem toXi_ofFamilies (b : ℝ) (hb : 0 < b) (cξ cη : CoeffFamily d) (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) : toXi b (ofFamilies b hb cξ cη hξ hη) = cξ := by
  funext γ
  simp only [toXi, ofFamilies]
  change cξ γ * b ^ (∑ i, γ i) / b ^ (∑ i, γ i) = cξ γ
  exact mul_div_cancel_right₀ _ (pow_pos hb _).ne'

theorem toEta_ofFamilies (b : ℝ) (hb : 0 < b) (cξ cη : CoeffFamily d) (hξ : AbsSummableAt cξ b)
    (hη : AbsSummableAt cη b) : toEta b (ofFamilies b hb cξ cη hξ hη) = cη := by
  funext γ
  simp only [toEta, ofFamilies]
  change cη γ * b ^ (∑ i, γ i) / b ^ (∑ i, γ i) = cη γ
  exact mul_div_cancel_right₀ _ (pow_pos hb _).ne'

/-- **The canonical coefficient map** on the data space: the coefficient of `N^{-μ} (log N)^j` in
the expansion of the original box integral. -/
noncomputable def dataBoxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1))
    (μ : ℝ) (j : ℕ) : ℝ :=
  boxCoeff n h k β b (toXi b x) (toEta b x) μ j

/-- The original box integral `Z(N; ξ, η)` of a data-space element. -/
noncomputable def dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (x : DataSpace (n + 1)) : ℝ :=
  familyPhaseIntegralBox n h k β N b (toXi b x) (toEta b x)

/-- The Taylor tree for data-space elements (Headline ★ transported). -/
theorem taylorTree_data (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β)
    {b : ℝ} (hb : 0 < b) (x : DataSpace (n + 1)) :
    ∃ C : ℝ → ℕ → ℝ, TaylorTreeConclusion n h k β b (toXi b x) (toEta b x) C :=
  thm_TaylorTree_coeffFamily n h k hk β hβ hb (absSummableAt_toXi hb x) (absSummableAt_toEta hb x)

/-- The canonical coefficient map through the unit-box spectral coefficients of the raw
coordinates. -/
theorem dataBoxCoeff_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {b : ℝ} (hb : 0 < b)
    (x : DataSpace (n + 1)) (μ : ℝ) (j : ℕ) :
    dataBoxCoeff n h k β b x μ j =
      b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
        ∑ q ∈ Finset.Ico j (n + 1), familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q *
          (q.choose j : ℝ) * (Real.log (b ^ (2 * ∑ i, k i))) ^ (q - j) := by
  unfold dataBoxCoeff boxCoeff
  rw [scale_toXi hb.ne', scale_toEta hb.ne']

end Grammar
