import Grammar.BilocalDivergence
import Grammar.GammaLogAsymptotic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The bilocal integral on the critical line

For `a, b > 0` and `λ > 0` the bilocal integral
`I_λ(a,b,h) = ∫₀^∞∫₀^∞ t^{λ−1}s^{λ−1} e^{−at − bs + h√(ts)} dt ds` is finite for `h < 2√(ab)`
(`lintegral_bilocalIntegrand_lt_top`) and infinite for `h > 2√(ab)`
(`lintegral_bilocalIntegrand_eq_top`). On the critical line `h = 2√(ab)` the exponent is the
perfect square `−(√(at) − √(bs))²` and the answer depends on `λ`:

`I_λ(a, b, 2√(ab)) < ∞ ⟺ λ < 1/4` (`bilocal_lintegral_lt_top_iff_of_critical`).

The proof substitutes `s = (a/b) t z` for each `t`, integrates out `t` with the Gamma integral
(for `z ≠ 1`) and reduces everything to the one-dimensional critical profile
`z^{λ−1} |1 − √z|^{−4λ}` (`lintegral_bilocalIntegrand_critical_eq`), which is integrable near
`0` (`λ > 0`) and near `∞` (`z^{−λ−1}`) and, near `z = 1`, comparable to `|z − 1|^{−4λ}`, whose
integrability is exactly `4λ < 1` (`lintegral_criticalProfile_lt_top_iff`). The Gaussian
corollary `lintegral_fluctuation_mul_fluctuation_lt_top_iff_of_critical` classifies
`E₊[S_λ(G_i) S_λ(G_j)]` on the critical line `β²B_ij = 2√(ab)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Grammar

/-! ### One-dimensional power tests -/

theorem lintegral_Ioo_rpow_lt_top_iff {t : ℝ} (ht : 0 < t) (r : ℝ) :
    (∫⁻ z in Ioo (0 : ℝ) t, ENNReal.ofReal (z ^ r)) < ⊤ ↔ -1 < r := by
  rw [← intervalIntegral.integrableOn_Ioo_rpow_iff ht]
  constructor
  · intro h
    refine ⟨(measurable_id.pow_const r).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioo
      fun z hz => Real.rpow_nonneg hz.1.le r)).2 h
  · exact fun h => h.lintegral_lt_top

theorem lintegral_Ioi_rpow_lt_top {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : r < -1) :
    (∫⁻ z in Ioi t, ENNReal.ofReal (z ^ r)) < ⊤ :=
  ((integrableOn_Ioi_rpow_iff ht).2 hr).lintegral_lt_top

/-- The singularity at `1` from the right: `∫₁³ (z−1)^r dz < ∞ ⟺ r > −1`. -/
theorem lintegral_Ioo_sub_one_rpow_lt_top_iff (r : ℝ) :
    (∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal ((z - 1) ^ r)) < ⊤ ↔ -1 < r := by
  have h := setLIntegral_map (μ := volume) (g := fun u : ℝ => u + 1)
    (f := fun z : ℝ => ENNReal.ofReal ((z - 1) ^ r)) (s := Ioo 1 3) measurableSet_Ioo
    (by fun_prop) (measurable_add_const 1)
  rw [map_add_right_eq_self, preimage_add_const_Ioo] at h
  simp only [add_sub_cancel_right, sub_self, show (3 : ℝ) - 1 = 2 by norm_num] at h
  rw [h]
  exact lintegral_Ioo_rpow_lt_top_iff two_pos r

/-- The singularity at `1` from the left: `∫_{1/2}^1 (1−z)^r dz < ∞` for `r > −1`. -/
theorem lintegral_Ioo_one_sub_rpow_lt_top {r : ℝ} (hr : -1 < r) :
    (∫⁻ z in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal ((1 - z) ^ r)) < ⊤ := by
  have h := setLIntegral_map (μ := volume) (g := fun u : ℝ => 1 - u)
    (f := fun z : ℝ => ENNReal.ofReal ((1 - z) ^ r)) (s := Ioo (1 / 2) 1) measurableSet_Ioo
    (by fun_prop) (measurable_const.sub measurable_id)
  rw [(Measure.measurePreserving_sub_left volume (1 : ℝ)).map_eq, preimage_const_sub_Ioo] at h
  simp only [sub_sub_cancel, sub_self, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  rw [h]
  exact (lintegral_Ioo_rpow_lt_top_iff (by norm_num) r).2 hr

/-- Domination by a constant multiple of a comparison integrand. -/
theorem lintegral_ofReal_le_ofReal_mul {s : Set ℝ} (hs : MeasurableSet s) {F g : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ z ∈ s, F z ≤ C * g z) :
    ∫⁻ z in s, ENNReal.ofReal (F z) ≤ ENNReal.ofReal C * ∫⁻ z in s, ENNReal.ofReal (g z) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hs fun z hz => ?_
  calc ENNReal.ofReal (F z) ≤ ENNReal.ofReal (C * g z) := ENNReal.ofReal_le_ofReal (h z hz)
    _ = ENNReal.ofReal C * ENNReal.ofReal (g z) := ENNReal.ofReal_mul hC

/-! ### The critical profile `z^{λ−1} ((1−√z)²)^{−2λ}` -/

/-- The critical profile `z^{λ−1} ((1 − √z)²)^{−2λ}`. -/
noncomputable def criticalProfile (lam z : ℝ) : ℝ :=
  z ^ (lam - 1) * ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam))

theorem one_sub_sqrt_sq_mul (z : ℝ) (hz : 0 ≤ z) :
    (1 - Real.sqrt z) ^ 2 * (1 + Real.sqrt z) ^ 2 = (1 - z) ^ 2 := by
  have hs := Real.sq_sqrt hz
  rw [← mul_pow]
  congr 1
  linear_combination -hs

/-- `(1−z)²/9 ≤ (1−√z)² ≤ (1−z)²` for `0 ≤ z ≤ 3`. -/
theorem one_sub_sqrt_sq_bounds {z : ℝ} (hz : 0 ≤ z) (hz3 : z ≤ 3) :
    (1 - z) ^ 2 / 9 ≤ (1 - Real.sqrt z) ^ 2 ∧ (1 - Real.sqrt z) ^ 2 ≤ (1 - z) ^ 2 := by
  have hkey := one_sub_sqrt_sq_mul z hz
  have hs0 := Real.sqrt_nonneg z
  have hs2 : Real.sqrt z ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hp : 0 < (1 + Real.sqrt z) ^ 2 := by positivity
  have h9 : (1 + Real.sqrt z) ^ 2 ≤ 9 := by nlinarith
  have h1 : 1 ≤ (1 + Real.sqrt z) ^ 2 := by nlinarith
  have e : (1 - Real.sqrt z) ^ 2 = (1 - z) ^ 2 / (1 + Real.sqrt z) ^ 2 := by
    rw [eq_div_iff hp.ne']
    exact hkey
  constructor
  · rw [e]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hp h9
  · rw [e]
    exact div_le_self (sq_nonneg _) h1

/-- Middle region, upper bound: for `1/2 < z < 3`, `z ≠ 1`. -/
theorem criticalProfile_le_mid (lam : ℝ) (hlam : 0 < lam) {z : ℝ} (hz : 1 / 2 < z) (hz3 : z < 3)
    (hz1 : z ≠ 1) :
    criticalProfile lam z ≤
      (2 * 3 ^ lam * (1 / 9 : ℝ) ^ (-(2 * lam))) * ((1 - z) ^ 2) ^ (-(2 * lam)) := by
  have hz0 : 0 < z := by linarith
  have h3 : z ^ lam ≤ 3 ^ lam := Real.rpow_le_rpow hz0.le hz3.le hlam.le
  have hA : z ^ (lam - 1) ≤ 2 * 3 ^ lam := by
    rw [Real.rpow_sub_one hz0.ne', div_le_iff₀ hz0]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) lam)
      (by linarith : (0 : ℝ) ≤ 2 * z - 1)]
  have hsq : 0 < (1 - z) ^ 2 / 9 := by
    have : 0 < (1 - z) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hz1.symm)))
    positivity
  have hB : ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam)) ≤ ((1 - z) ^ 2 / 9) ^ (-(2 * lam)) :=
    Real.rpow_le_rpow_of_nonpos hsq (one_sub_sqrt_sq_bounds hz0.le hz3.le).1 (by linarith)
  have hC : ((1 - z) ^ 2 / 9) ^ (-(2 * lam)) =
      ((1 - z) ^ 2) ^ (-(2 * lam)) * (1 / 9 : ℝ) ^ (-(2 * lam)) := by
    rw [div_eq_mul_one_div, Real.mul_rpow (sq_nonneg _) (by norm_num)]
  calc criticalProfile lam z = z ^ (lam - 1) * ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam)) := rfl
    _ ≤ (2 * 3 ^ lam) * (((1 - z) ^ 2) ^ (-(2 * lam)) * (1 / 9 : ℝ) ^ (-(2 * lam))) := by
        rw [← hC]
        exact mul_le_mul hA hB (Real.rpow_nonneg (sq_nonneg _) _) (by positivity)
    _ = _ := by ring

/-- Middle region, lower bound: for `1 < z < 3`. -/
theorem le_criticalProfile_mid (lam : ℝ) (hlam : 0 < lam) {z : ℝ} (hz : 1 < z) (hz3 : z < 3) :
    (1 / 3 : ℝ) * ((1 - z) ^ 2) ^ (-(2 * lam)) ≤ criticalProfile lam z := by
  have hz0 : 0 < z := by linarith
  have hA : (1 / 3 : ℝ) ≤ z ^ (lam - 1) := by
    rw [Real.rpow_sub_one hz0.ne', le_div_iff₀ hz0]
    have := Real.one_le_rpow hz.le hlam.le
    linarith
  have hpos : 0 < (1 - Real.sqrt z) ^ 2 := by
    have : Real.sqrt z ≠ 1 := fun h => (ne_of_gt hz) (Real.sqrt_eq_one.1 h)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 this.symm)))
  have hB : ((1 - z) ^ 2) ^ (-(2 * lam)) ≤ ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam)) :=
    Real.rpow_le_rpow_of_nonpos hpos (one_sub_sqrt_sq_bounds hz0.le hz3.le).2 (by linarith)
  exact mul_le_mul hA hB (Real.rpow_nonneg (sq_nonneg _) _) (Real.rpow_nonneg hz0.le _)

/-- Left region: for `0 < z < 1/2`. -/
theorem criticalProfile_le_left (lam : ℝ) (hlam : 0 < lam) {z : ℝ} (hz : 0 < z)
    (hz2 : z < 1 / 2) :
    criticalProfile lam z ≤ (1 / 16 : ℝ) ^ (-(2 * lam)) * z ^ (lam - 1) := by
  have hs : Real.sqrt z ≤ 3 / 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have h16 : (1 / 16 : ℝ) ≤ (1 - Real.sqrt z) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 4 - Real.sqrt z)
      (by linarith : (0 : ℝ) ≤ 5 / 4 - Real.sqrt z), Real.sqrt_nonneg z]
  have hB : ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam)) ≤ (1 / 16 : ℝ) ^ (-(2 * lam)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h16 (by linarith)
  rw [criticalProfile, mul_comm]
  exact mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hz.le _)

/-- Right region: for `z > 3`. -/
theorem criticalProfile_le_right (lam : ℝ) (hlam : 0 < lam) {z : ℝ} (hz : 3 < z) :
    criticalProfile lam z ≤ (1 / 9 : ℝ) ^ (-(2 * lam)) * z ^ (-lam - 1) := by
  have hz0 : 0 < z := by linarith
  have hs : 3 / 2 ≤ Real.sqrt z := (Real.le_sqrt (by norm_num) hz0.le).2 (by nlinarith)
  have hs2 := Real.sq_sqrt hz0.le
  have h9 : z / 9 ≤ (1 - Real.sqrt z) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt z / 3 - 1)
      (by linarith : (0 : ℝ) ≤ 4 * Real.sqrt z / 3 - 1)]
  have hB : ((1 - Real.sqrt z) ^ 2) ^ (-(2 * lam)) ≤ (z / 9) ^ (-(2 * lam)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h9 (by linarith)
  have hC : (z / 9) ^ (-(2 * lam)) = z ^ (-(2 * lam)) * (1 / 9 : ℝ) ^ (-(2 * lam)) := by
    rw [div_eq_mul_one_div, Real.mul_rpow hz0.le (by norm_num)]
  calc criticalProfile lam z
      ≤ z ^ (lam - 1) * (z ^ (-(2 * lam)) * (1 / 9 : ℝ) ^ (-(2 * lam))) := by
        rw [← hC]
        exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hz0.le _)
    _ = (1 / 9 : ℝ) ^ (-(2 * lam)) * z ^ (-lam - 1) := by
        rw [← mul_assoc, ← Real.rpow_add hz0, show lam - 1 + -(2 * lam) = -lam - 1 by ring,
          mul_comm]

/-- **The critical profile is integrable on `(0, ∞)` iff `λ < 1/4`.** -/
theorem lintegral_criticalProfile_lt_top_iff (lam : ℝ) (hlam : 0 < lam) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (criticalProfile lam z)) < ⊤ ↔ lam < 1 / 4 := by
  constructor
  · intro hK
    by_contra hge
    have hge' : 1 / 4 ≤ lam := le_of_not_gt hge
    have htop : ∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal ((z - 1) ^ (-(4 * lam))) = ⊤ := by
      by_contra h
      have := (lintegral_Ioo_sub_one_rpow_lt_top_iff _).1 (lt_top_iff_ne_top.2 h)
      linarith
    have hlow : ∀ z ∈ Ioo (1 : ℝ) 3,
        (1 / 3 : ℝ) * (z - 1) ^ (-(4 * lam)) ≤ criticalProfile lam z := by
      intro z hz
      have e : (z - 1) ^ (-(4 * lam)) = ((1 - z) ^ 2) ^ (-(2 * lam)) := by
        rw [show (1 - z) ^ 2 = (z - 1) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
          ← Real.rpow_mul (by linarith [hz.1])]
        congr 1
        ring
      rw [e]
      exact le_criticalProfile_mid lam hlam hz.1 hz.2
    have h1 : ∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal ((1 / 3 : ℝ) * (z - 1) ^ (-(4 * lam))) ≤
        ∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal (criticalProfile lam z) :=
      setLIntegral_mono' measurableSet_Ioo fun z hz => ENNReal.ofReal_le_ofReal (hlow z hz)
    have h2 : ∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal ((1 / 3 : ℝ) * (z - 1) ^ (-(4 * lam))) = ⊤ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htop,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (by norm_num)).ne']
    have h3 : ∫⁻ z in Ioo (1 : ℝ) 3, ENNReal.ofReal (criticalProfile lam z) ≤
        ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (criticalProfile lam z) :=
      lintegral_mono_set (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))
    exact absurd ((h2 ▸ h1).trans h3) (not_le.2 hK)
  · intro hlt
    have hcover : Ioi (0 : ℝ) ⊆ Ioo 0 (1 / 2) ∪ Icc (1 / 2) 1 ∪ Icc 1 3 ∪ Ioi 3 := by
      intro z hz
      have hz0 : 0 < z := hz
      by_cases h1 : z < 1 / 2
      · exact Or.inl (Or.inl (Or.inl ⟨hz0, h1⟩))
      by_cases h2 : z ≤ 1
      · exact Or.inl (Or.inl (Or.inr ⟨not_lt.1 h1, h2⟩))
      by_cases h3 : z ≤ 3
      · exact Or.inl (Or.inr ⟨(not_le.1 h2).le, h3⟩)
      · exact Or.inr (not_le.1 h3)
    have hP1 : ∫⁻ z in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (criticalProfile lam z) < ⊤ :=
      (lintegral_ofReal_le_ofReal_mul measurableSet_Ioo (Real.rpow_nonneg (by norm_num) _)
        fun z hz => criticalProfile_le_left lam hlam hz.1 hz.2).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((lintegral_Ioo_rpow_lt_top_iff (by norm_num) _).2 (by linarith)))
    have hP2 : ∫⁻ z in Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (criticalProfile lam z) < ⊤ := by
      rw [← setLIntegral_congr Ioo_ae_eq_Icc]
      refine (lintegral_ofReal_le_ofReal_mul (C := 2 * 3 ^ lam * (1 / 9 : ℝ) ^ (-(2 * lam)))
        measurableSet_Ioo (by positivity) fun z hz => ?_).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_Ioo_one_sub_rpow_lt_top (r := -(4 * lam)) (by linarith)))
      have e : ((1 - z) ^ 2) ^ (-(2 * lam)) = (1 - z) ^ (-(4 * lam)) := by
        rw [← Real.rpow_two, ← Real.rpow_mul (by linarith [hz.2])]
        congr 1
        ring
      rw [← e]
      exact criticalProfile_le_mid lam hlam hz.1 (by linarith [hz.2]) (ne_of_lt hz.2)
    have hP3 : ∫⁻ z in Icc (1 : ℝ) 3, ENNReal.ofReal (criticalProfile lam z) < ⊤ := by
      rw [← setLIntegral_congr Ioo_ae_eq_Icc]
      refine (lintegral_ofReal_le_ofReal_mul (C := 2 * 3 ^ lam * (1 / 9 : ℝ) ^ (-(2 * lam)))
        measurableSet_Ioo (by positivity) fun z hz => ?_).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((lintegral_Ioo_sub_one_rpow_lt_top_iff (-(4 * lam))).2 (by linarith)))
      have e : ((1 - z) ^ 2) ^ (-(2 * lam)) = (z - 1) ^ (-(4 * lam)) := by
        rw [show (1 - z) ^ 2 = (z - 1) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
          ← Real.rpow_mul (by linarith [hz.1])]
        congr 1
        ring
      rw [← e]
      exact criticalProfile_le_mid lam hlam (by linarith [hz.1]) hz.2 (ne_of_gt hz.1)
    have hP4 : ∫⁻ z in Ioi (3 : ℝ), ENNReal.ofReal (criticalProfile lam z) < ⊤ :=
      (lintegral_ofReal_le_ofReal_mul measurableSet_Ioi (Real.rpow_nonneg (by norm_num) _)
        fun z hz => criticalProfile_le_right lam hlam hz).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_Ioi_rpow_lt_top (by norm_num) (by linarith)))
    calc ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (criticalProfile lam z)
        ≤ ∫⁻ z in Ioo (0 : ℝ) (1 / 2) ∪ Icc (1 / 2) 1 ∪ Icc 1 3 ∪ Ioi 3,
            ENNReal.ofReal (criticalProfile lam z) := lintegral_mono_set hcover
      _ ≤ ((∫⁻ z in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (criticalProfile lam z)) +
            ∫⁻ z in Icc (1 / 2 : ℝ) 1, ENNReal.ofReal (criticalProfile lam z)) +
            (∫⁻ z in Icc (1 : ℝ) 3, ENNReal.ofReal (criticalProfile lam z)) +
            ∫⁻ z in Ioi (3 : ℝ), ENNReal.ofReal (criticalProfile lam z) :=
          (lintegral_union_le _ _ _).trans (add_le_add ((lintegral_union_le _ _ _).trans
            (add_le_add (lintegral_union_le _ _ _) le_rfl)) le_rfl)
      _ < ⊤ := ENNReal.add_lt_top.2
          ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hP1, hP2⟩, hP3⟩, hP4⟩

/-! ### Reduction of the critical bilocal integral to the profile -/

/-- On the critical line `h = 2√(ab)` the exponent is the perfect square `−(√(at) − √(bs))²`. -/
theorem bilocalIntegrand_critical (lam a b t s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hs : 0 ≤ s) :
    bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s =
      t ^ (lam - 1) * (s ^ (lam - 1) *
        Real.exp (-(Real.sqrt (a * t) - Real.sqrt (b * s)) ^ 2)) := by
  have e1 : Real.sqrt (a * t) * Real.sqrt (b * s) = Real.sqrt (a * b) * Real.sqrt (t * s) := by
    rw [← Real.sqrt_mul (mul_nonneg ha ht), ← Real.sqrt_mul (mul_nonneg ha hb)]
    congr 1
    ring
  have e2 := Real.sq_sqrt (mul_nonneg ha ht)
  have e3 := Real.sq_sqrt (mul_nonneg hb hs)
  have e : -a * t - b * s + 2 * Real.sqrt (a * b) * Real.sqrt (t * s) =
      -(Real.sqrt (a * t) - Real.sqrt (b * s)) ^ 2 := by
    linear_combination e2 + e3 - 2 * e1
  rw [bilocalIntegrand, e, mul_assoc]

/-- Positive scaling of `(0, ∞)` for `lintegral`. -/
theorem lintegral_Ioi_comp_mul_left (f : ℝ → ℝ≥0∞) (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    ∫⁻ s in Ioi (0 : ℝ), f s = ENNReal.ofReal c * ∫⁻ z in Ioi (0 : ℝ), f (c * z) := by
  have h := setLIntegral_map (μ := volume) (g := fun z : ℝ => c * z) (s := Ioi 0)
    measurableSet_Ioi hf (measurable_const_mul c)
  rw [Real.map_volume_mul_left hc.ne', Measure.restrict_smul, lintegral_smul_measure] at h
  have hpre : (fun z : ℝ => c * z) ⁻¹' Ioi 0 = Ioi 0 := by
    ext z
    simp [mul_pos_iff_of_pos_left hc]
  rw [hpre] at h
  rw [← h, smul_eq_mul, ← mul_assoc, abs_of_pos (inv_pos.2 hc), ← ENNReal.ofReal_mul hc.le,
    mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

/-- The inner substitution `s = (a/b) t z`. -/
theorem lintegral_inner_critical (lam a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (lam - 1) *
        Real.exp (-(Real.sqrt (a * t) - Real.sqrt (b * s)) ^ 2)) =
      ENNReal.ofReal ((a / b * t) ^ lam) * ∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (z ^ (lam - 1) * Real.exp (-(a * t * (1 - Real.sqrt z) ^ 2))) := by
  have hc : 0 < a / b * t := mul_pos (div_pos ha hb) ht
  rw [lintegral_Ioi_comp_mul_left _ (by fun_prop) hc]
  have hinner : ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal ((a / b * t * z) ^ (lam - 1) *
      Real.exp (-(Real.sqrt (a * t) - Real.sqrt (b * (a / b * t * z))) ^ 2)) =
      ENNReal.ofReal ((a / b * t) ^ (lam - 1)) * ∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (z ^ (lam - 1) * Real.exp (-(a * t * (1 - Real.sqrt z) ^ 2))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    have hz : 0 < z := hz
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
    congr 1
    have e1 : b * (a / b * t * z) = a * t * z := by
      field_simp
    have e2 : (Real.sqrt (a * t) - Real.sqrt (a * t * z)) ^ 2 =
        a * t * (1 - Real.sqrt z) ^ 2 := by
      rw [Real.sqrt_mul (mul_nonneg ha.le ht.le), show Real.sqrt (a * t) -
        Real.sqrt (a * t) * Real.sqrt z = Real.sqrt (a * t) * (1 - Real.sqrt z) by ring,
        mul_pow, Real.sq_sqrt (mul_nonneg ha.le ht.le)]
    rw [e1, e2, Real.mul_rpow hc.le hz.le]
    ring
  rw [hinner, ← mul_assoc, ← ENNReal.ofReal_mul hc.le]
  congr 2
  rw [Real.rpow_sub_one hc.ne']
  field_simp

/-- The kernel after the inner substitution: `t^{2λ−1} z^{λ−1} e^{−a(1−√z)² t}`. -/
noncomputable def criticalKernel (lam a t z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (2 * lam - 1) * z ^ (lam - 1) *
    Real.exp (-(a * (1 - Real.sqrt z) ^ 2) * t))

/-- **Reduction to the critical profile**:
`I_λ(a, b, 2√(ab)) = (a/b)^λ Γ(2λ) a^{−2λ} ∫₀^∞ z^{λ−1} ((1−√z)²)^{−2λ} dz`. -/
theorem lintegral_bilocalIntegrand_critical_eq (lam a b : ℝ) (hlam : 0 < lam) (ha : 0 < a)
    (hb : 0 < b) :
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s) =
      ENNReal.ofReal ((a / b) ^ lam * (Real.Gamma (2 * lam) * a ^ (-(2 * lam)))) *
        ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (criticalProfile lam z) := by
  have step1 : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s) =
      ENNReal.ofReal ((a / b) ^ lam) * ∫⁻ z in Ioi (0 : ℝ), criticalKernel lam a t z := by
    intro t ht
    have ht : 0 < t := ht
    have e : ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s) =
        ENNReal.ofReal (t ^ (lam - 1)) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (lam - 1) *
            Real.exp (-(Real.sqrt (a * t) - Real.sqrt (b * s)) ^ 2)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      have hs : 0 < s := hs
      rw [bilocalIntegrand_critical lam a b t s ha.le hb.le ht.le hs.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    rw [e, lintegral_inner_critical lam a b t ha hb ht, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.mul_rpow (div_pos ha hb).le ht.le,
      show t ^ (lam - 1) * ((a / b) ^ lam * t ^ lam) = (a / b) ^ lam * t ^ (2 * lam - 1) by
        rw [mul_left_comm, ← Real.rpow_add ht]; congr 2; ring,
      ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos ha hb).le _), mul_assoc,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    rw [criticalKernel, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    congr 1
    rw [show -(a * (1 - Real.sqrt z) ^ 2) * t = -(a * t * (1 - Real.sqrt z) ^ 2) by ring]
    ring
  have hmeas : Measurable (Function.uncurry (criticalKernel lam a)) := by
    unfold criticalKernel Function.uncurry
    fun_prop
  have step2 : ∀ z ∈ Ioi (0 : ℝ), z ≠ 1 →
      ∫⁻ t in Ioi (0 : ℝ), criticalKernel lam a t z =
        ENNReal.ofReal (Real.Gamma (2 * lam) * a ^ (-(2 * lam))) *
          ENNReal.ofReal (criticalProfile lam z) := by
    intro z hz hz1
    have hz : 0 < z := hz
    have hκ : 0 < a * (1 - Real.sqrt z) ^ 2 := by
      have : Real.sqrt z ≠ 1 := fun h => hz1 (Real.sqrt_eq_one.1 h)
      exact mul_pos ha
        (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 this.symm))))
    have e : ∫⁻ t in Ioi (0 : ℝ), criticalKernel lam a t z =
        ENNReal.ofReal (z ^ (lam - 1)) * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (2 * lam - 1) * Real.exp (-(a * (1 - Real.sqrt z) ^ 2 * t))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [criticalKernel, ← ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _)]
      congr 1
      rw [neg_mul]
      ring
    have hint : IntegrableOn (fun t : ℝ => t ^ (2 * lam - 1) *
        Real.exp (-(a * (1 - Real.sqrt z) ^ 2 * t))) (Ioi 0) := by
      simpa only [neg_mul] using integrableOn_rpow_mul_exp_neg_mul' (2 * lam) _ (by linarith) hκ
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le),
      integral_rpow_mul_exp_neg_mul (2 * lam) _ (by linarith) hκ,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hz.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le
        (Real.rpow_nonneg ha.le _))]
    congr 1
    rw [criticalProfile, Real.mul_rpow ha.le (sq_nonneg _)]
    ring
  calc ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s)
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((a / b) ^ lam) * ∫⁻ z in Ioi (0 : ℝ),
          criticalKernel lam a t z := setLIntegral_congr_fun measurableSet_Ioi step1
    _ = ENNReal.ofReal ((a / b) ^ lam) * ∫⁻ z in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
          criticalKernel lam a t z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap hmeas.aemeasurable]
    _ = ENNReal.ofReal ((a / b) ^ lam) * ∫⁻ z in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.Gamma (2 * lam) * a ^ (-(2 * lam))) *
            ENNReal.ofReal (criticalProfile lam z) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi,
          ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (μ := volume) (1 : ℝ)))]
          with z hz hz1
        exact step2 z hz hz1
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos ha hb).le _)]

/-- **The bilocal integral on the critical line `h = 2√(ab)` is finite iff `λ < 1/4`.** -/
theorem bilocal_lintegral_lt_top_iff_of_critical (lam a b : ℝ) (hlam : 0 < lam) (ha : 0 < a)
    (hb : 0 < b) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (bilocalIntegrand lam a b (2 * Real.sqrt (a * b)) t s)) < ⊤ ↔
      lam < 1 / 4 := by
  rw [lintegral_bilocalIntegrand_critical_eq lam a b hlam ha hb,
    ← lintegral_criticalProfile_lt_top_iff lam hlam]
  have hc : 0 < (a / b) ^ lam * (Real.Gamma (2 * lam) * a ^ (-(2 * lam))) :=
    mul_pos (Real.rpow_pos_of_pos (div_pos ha hb) _)
      (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.rpow_pos_of_pos ha _))
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_right h.ne (ENNReal.ofReal_pos.2 hc).ne',
    fun h => ENNReal.mul_lt_top ENNReal.ofReal_lt_top h⟩

variable {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ)

/-- **`E₊[S_λ(G_i) S_λ(G_j)]` on the critical line `β²B_ij = 2√(ab)` is finite iff `λ < 1/4`**,
where `a = β(1 − βB_ii/2)`, `b = β(1 − βB_jj/2)` and `B = AAᵀ`. -/
theorem lintegral_fluctuation_mul_fluctuation_lt_top_iff_of_critical (β lam : ℝ) (hβ : 0 < β)
    (hlam : 0 < lam) (i j : Fin m)
    (hi : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)
    (hj : 0 < 1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)
    (hh : β ^ 2 * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j =
      2 * Real.sqrt ((β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i i / 2)) *
        (β * (1 - β * (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) j j / 2)))) :
    (∫⁻ g, ENNReal.ofReal (fluctuation β lam (g i) * fluctuation β lam (g j))
        ∂gaussianVector A) < ⊤ ↔ lam < 1 / 4 := by
  rw [lintegral_fluctuation_mul_fluctuation A β lam hβ hlam i j, hh]
  exact bilocal_lintegral_lt_top_iff_of_critical lam _ _ hlam (mul_pos hβ hi) (mul_pos hβ hj)

end Grammar
