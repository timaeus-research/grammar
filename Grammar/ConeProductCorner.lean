/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.BlowUpBesselClosedForm

/-!
# The corner of the cone's Leray density for a product-radial prior

For a prior `F(u) = f(|z₁|²) g(|z₂|²)` on `ℝ⁴ = ℂ × ℂ` the Leray density of
`q(u) = (|z₁|² − |z₂|²)/2` is, in the bipolar variables `(p, t) = (|z₁|², |z₂|²)`, `q = min(p, t)`,

  `L_{f,g}(v) = 2π² ∫₀^∞ f(q + 2 max(v,0)) g(q + 2 max(−v,0)) dq`   (`coneProductDensity`),

a fixed-domain integral.  For Lipschitz profiles with an upper cutoff `R` the symmetric second
difference has the EXACT form

  `L(t) + L(−t) − 2L(0) = −2π² ∫₀^{2t} fg − 2π² ∫₀^R Δ_{2t}f · Δ_{2t}g`
  (`coneProductDensity_corner_eq`),

from `f(q+a)g(q) + f(q)g(q+a) − 2f(q)g(q) = Δ_a(fg)(q) − Δ_af(q)Δ_ag(q)` and the half-line shift
`∫₀^∞ h(q+a) − ∫₀^∞ h = −∫₀^a h` — no derivative is interchanged with the integral — whence

  ★★ `coneProductDensity_corner_bound : |L(t) + L(−t) − 2L(0) + 4π² f(0)g(0) t| ≤ 24π² R L_f L_g t²`

and the corner limit
★★★ `tendsto_coneProductDensity_corner : (L(t) + L(−t) − 2L(0))/t → −4π² f(0)g(0)` as `t → 0⁺`:
the derivative jump of the Leray density at the vertex is `−4π²F(0)`, i.e. the coefficient of `|v|`
is `−2π²F(0)` (examples_slop Proposition `prop:cone_leray`, product-radial case; Astra round 31).
The identification with the pushforward of `F du` along `q` is the next unit.
Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace Grammar

/-! ### Profiles -/

/-- A Lipschitz radial profile with an upper cutoff `R`. -/
structure ConeProfile (f : ℝ → ℝ) (R : ℝ) (L : NNReal) : Prop where
  lip : LipschitzWith L f
  cut : ∀ x, R ≤ x → f x = 0

namespace ConeProfile

variable {f : ℝ → ℝ} {R : ℝ} {L : NNReal}

theorem continuous (hf : ConeProfile f R L) : Continuous f := hf.lip.continuous

theorem abs_sub_le (hf : ConeProfile f R L) (x y : ℝ) : |f x - f y| ≤ L * |x - y| := by
  have := hf.lip.dist_le_mul x y
  rwa [Real.dist_eq, Real.dist_eq] at this

theorem abs_le (hf : ConeProfile f R L) (hR : 0 ≤ R) {x : ℝ} (hx : 0 ≤ x) : |f x| ≤ L * R := by
  rcases le_or_gt R x with h | h
  · rw [hf.cut x h, abs_zero]
    exact mul_nonneg L.2 hR
  · have := hf.abs_sub_le x R
    rw [hf.cut R le_rfl, sub_zero, abs_of_neg (sub_neg.2 h)] at this
    calc |f x| ≤ L * (-(x - R)) := this
      _ ≤ L * R := mul_le_mul_of_nonneg_left (by linarith) L.2

end ConeProfile

/-! ### Cutoff integrals on the half-line -/

theorem integrableOn_Ioi_of_cutoff {F : ℝ → ℝ} (hF : Continuous F) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ q, R ≤ q → F q = 0) : IntegrableOn F (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  refine IntegrableOn.union ?_ ?_
  · rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    exact hF.intervalIntegrable _ _
  · exact integrableOn_zero.congr_fun (fun q hq => (hv q (le_of_lt hq)).symm) measurableSet_Ioi

theorem integral_Ioi_eq_of_cutoff {F : ℝ → ℝ} (hF : Continuous F) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ q, R ≤ q → F q = 0) : ∫ q in Ioi (0 : ℝ), F q = ∫ q in (0 : ℝ)..R, F q := by
  rw [← Ioc_union_Ioi_eq_Ioi hR, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1 (hF.intervalIntegrable _ _))
    (integrableOn_zero.congr_fun (fun q hq => (hv q (le_of_lt hq)).symm) measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun q hq => hv q (le_of_lt hq)), integral_zero, add_zero, integral_of_le hR]

/-- The half-line shift: `∫₀^R h(q + a) = ∫₀^R h − ∫₀^a h` for `h` vanishing beyond `R`. -/
theorem intervalIntegral_comp_add_cutoff {h : ℝ → ℝ} (hh : Continuous h) {R : ℝ}
    (hv : ∀ q, R ≤ q → h q = 0) {a : ℝ} (ha : 0 ≤ a) :
    ∫ q in (0 : ℝ)..R, h (q + a) = (∫ q in (0 : ℝ)..R, h q) - ∫ q in (0 : ℝ)..a, h q := by
  rw [integral_comp_add_right, zero_add]
  have hi : ∀ x y : ℝ, IntervalIntegrable h volume x y := fun x y => hh.intervalIntegrable x y
  have h1 : ∫ q in a..R + a, h q = (∫ q in a..R, h q) + ∫ q in R..R + a, h q :=
    (integral_add_adjacent_intervals (hi a R) (hi R (R + a))).symm
  have h2 : ∫ q in R..R + a, h q = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) fun q hq => ?_, intervalIntegral.integral_zero]
    rw [uIcc_of_le (by linarith)] at hq
    exact hv q hq.1
  have h3 : ∫ q in (0 : ℝ)..R, h q = (∫ q in (0 : ℝ)..a, h q) + ∫ q in a..R, h q :=
    (integral_add_adjacent_intervals (hi 0 a) (hi a R)).symm
  linarith

/-! ### The product-radial Leray density -/

/-- `L_{f,g}(v) = 2π² ∫₀^∞ f(q + 2 max(v,0)) g(q + 2 max(−v,0)) dq`. -/
noncomputable def coneProductDensity (f g : ℝ → ℝ) (v : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * ∫ q in Ioi (0 : ℝ), f (q + 2 * max v 0) * g (q + 2 * max (-v) 0)

variable {f g : ℝ → ℝ} {R : ℝ} {Lf Lg : NNReal}

theorem coneProductDensity_of_nonneg (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg)
    (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    coneProductDensity f g t = 2 * Real.pi ^ 2 * ∫ q in (0 : ℝ)..R, f (q + 2 * t) * g q := by
  unfold coneProductDensity
  rw [max_eq_left ht, max_eq_right (by linarith)]
  simp only [mul_zero, add_zero]
  rw [integral_Ioi_eq_of_cutoff (by have := hf.continuous; have := hg.continuous; fun_prop) hR
      fun q hq => by rw [hg.cut q hq, mul_zero]]

theorem coneProductDensity_of_nonpos (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg)
    (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    coneProductDensity f g (-t) = 2 * Real.pi ^ 2 * ∫ q in (0 : ℝ)..R, f q * g (q + 2 * t) := by
  unfold coneProductDensity
  rw [max_eq_right (by linarith), neg_neg, max_eq_left ht]
  simp only [mul_zero, add_zero]
  rw [integral_Ioi_eq_of_cutoff (by have := hf.continuous; have := hg.continuous; fun_prop) hR
      fun q hq => by rw [hf.cut q hq, zero_mul]]

theorem coneProductDensity_zero (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg) (hR : 0 ≤ R) :
    coneProductDensity f g 0 = 2 * Real.pi ^ 2 * ∫ q in (0 : ℝ)..R, f q * g q := by
  have := coneProductDensity_of_nonneg hf hg hR le_rfl
  simpa using this

/-- ★★ **The exact symmetric-corner identity**:
`L(t) + L(−t) − 2L(0) = −2π² ∫₀^{2t} fg − 2π² ∫₀^R (f(q+2t) − f q)(g(q+2t) − g q)`. -/
theorem coneProductDensity_corner_eq (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg)
    (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    coneProductDensity f g t + coneProductDensity f g (-t) - 2 * coneProductDensity f g 0 =
      -(2 * Real.pi ^ 2) * (∫ q in (0 : ℝ)..2 * t, f q * g q) -
        2 * Real.pi ^ 2 * ∫ q in (0 : ℝ)..R, (f (q + 2 * t) - f q) * (g (q + 2 * t) - g q) := by
  rw [coneProductDensity_of_nonneg hf hg hR ht, coneProductDensity_of_nonpos hf hg hR ht,
    coneProductDensity_zero hf hg hR]
  have hfc := hf.continuous
  have hgc := hg.continuous
  have hshift := intervalIntegral_comp_add_cutoff (h := fun q => f q * g q) (by fun_prop)
    (fun q hq => by rw [hf.cut q hq, zero_mul]) (by linarith : 0 ≤ 2 * t)
  have hA : IntervalIntegrable (fun q : ℝ => f (q + 2 * t) * g (q + 2 * t)) volume 0 R :=
    (by fun_prop : Continuous fun q : ℝ => f (q + 2 * t) * g (q + 2 * t)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun q : ℝ => f q * g q) volume 0 R :=
    (by fun_prop : Continuous fun q : ℝ => f q * g q).intervalIntegrable _ _
  have hC : IntervalIntegrable (fun q : ℝ => f (q + 2 * t) * g q) volume 0 R :=
    (by fun_prop : Continuous fun q : ℝ => f (q + 2 * t) * g q).intervalIntegrable _ _
  have hD : IntervalIntegrable (fun q : ℝ => f q * g (q + 2 * t)) volume 0 R :=
    (by fun_prop : Continuous fun q : ℝ => f q * g (q + 2 * t)).intervalIntegrable _ _
  have hAC : IntervalIntegrable (fun q : ℝ => f (q + 2 * t) * g (q + 2 * t) -
      f (q + 2 * t) * g q) volume 0 R := hA.sub hC
  have hACD : IntervalIntegrable (fun q : ℝ => f (q + 2 * t) * g (q + 2 * t) -
      f (q + 2 * t) * g q - f q * g (q + 2 * t)) volume 0 R := hAC.sub hD
  have e : (∫ q in (0 : ℝ)..R, f (q + 2 * t) * g (q + 2 * t)) -
      (∫ q in (0 : ℝ)..R, f (q + 2 * t) * g q) - (∫ q in (0 : ℝ)..R, f q * g (q + 2 * t)) +
      (∫ q in (0 : ℝ)..R, f q * g q) =
      ∫ q in (0 : ℝ)..R, (f (q + 2 * t) - f q) * (g (q + 2 * t) - g q) := by
    rw [← intervalIntegral.integral_sub hA hC, ← intervalIntegral.integral_sub hAC hD,
      ← intervalIntegral.integral_add hACD hB]
    exact integral_congr fun q _ => by ring
  rw [← e, hshift]
  set I1 := ∫ q in (0 : ℝ)..R, f (q + 2 * t) * g q with hI1
  set I2 := ∫ q in (0 : ℝ)..R, f q * g (q + 2 * t) with hI2
  set I0 := ∫ q in (0 : ℝ)..R, f q * g q with hI0
  set I3 := ∫ q in (0 : ℝ)..2 * t, f q * g q with hI3
  clear_value I1 I2 I0 I3
  ring

/-- ★★ **The corner bound**: `|L(t) + L(−t) − 2L(0) + 4π² f(0)g(0) t| ≤ 24π² R L_f L_g t²`. -/
theorem coneProductDensity_corner_bound (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg)
    (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    |coneProductDensity f g t + coneProductDensity f g (-t) - 2 * coneProductDensity f g 0 +
      4 * Real.pi ^ 2 * f 0 * g 0 * t| ≤ 24 * Real.pi ^ 2 * R * Lf * Lg * t ^ 2 := by
  rw [coneProductDensity_corner_eq hf hg hR ht]
  have hfc := hf.continuous
  have hgc := hg.continuous
  -- the boundary term: `∫₀^{2t} fg = 2t f(0)g(0) + ∫₀^{2t} (fg − f(0)g(0))`
  have e1 : ∫ q in (0 : ℝ)..2 * t, f q * g q =
      2 * t * (f 0 * g 0) + ∫ q in (0 : ℝ)..2 * t, (f q * g q - f 0 * g 0) := by
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun q : ℝ => f q * g q).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun _ : ℝ => f 0 * g 0).intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hb1 : |∫ q in (0 : ℝ)..2 * t, (f q * g q - f 0 * g 0)| ≤ 8 * R * Lf * Lg * t ^ 2 := by
    have := norm_integral_le_of_norm_le_const (a := 0) (b := 2 * t)
      (f := fun q => f q * g q - f 0 * g 0) (C := 4 * R * Lf * Lg * t) fun q hq => by
        rw [uIoc_of_le (by linarith)] at hq
        have hq0 : 0 < q := hq.1
        have hq1 : q ≤ 2 * t := hq.2
        rw [Real.norm_eq_abs]
        have hf1 := hf.abs_sub_le q 0
        have hg1 := hg.abs_sub_le q 0
        have hf2 := hf.abs_le hR (le_refl 0)
        have hg2 := hg.abs_le hR hq0.le
        rw [sub_zero, abs_of_pos hq0] at hf1 hg1
        calc |f q * g q - f 0 * g 0| = |(f q - f 0) * g q + f 0 * (g q - g 0)| := by ring_nf
          _ ≤ |(f q - f 0) * g q| + |f 0 * (g q - g 0)| := abs_add_le _ _
          _ = |f q - f 0| * |g q| + |f 0| * |g q - g 0| := by rw [abs_mul, abs_mul]
          _ ≤ (Lf * q) * (Lg * R) + (Lf * R) * (Lg * q) := by gcongr
          _ = 2 * R * Lf * Lg * q := by ring
          _ ≤ 4 * R * Lf * Lg * t := by
              have : (0 : ℝ) ≤ R * Lf * Lg := by positivity
              nlinarith
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * t)] at this
    calc |∫ q in (0 : ℝ)..2 * t, (f q * g q - f 0 * g 0)| ≤ 4 * R * Lf * Lg * t * (2 * t) := this
      _ = 8 * R * Lf * Lg * t ^ 2 := by ring
  -- the increment term
  have hb2 : |∫ q in (0 : ℝ)..R, (f (q + 2 * t) - f q) * (g (q + 2 * t) - g q)| ≤
      4 * R * Lf * Lg * t ^ 2 := by
    have := norm_integral_le_of_norm_le_const (a := 0) (b := R)
      (f := fun q => (f (q + 2 * t) - f q) * (g (q + 2 * t) - g q)) (C := 4 * Lf * Lg * t ^ 2)
      fun q _ => by
        rw [Real.norm_eq_abs, abs_mul]
        have hf1 := hf.abs_sub_le (q + 2 * t) q
        have hg1 := hg.abs_sub_le (q + 2 * t) q
        rw [add_sub_cancel_left, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * t)] at hf1 hg1
        calc |f (q + 2 * t) - f q| * |g (q + 2 * t) - g q| ≤ (Lf * (2 * t)) * (Lg * (2 * t)) := by
              gcongr
          _ = 4 * Lf * Lg * t ^ 2 := by ring
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hR] at this
    calc |∫ q in (0 : ℝ)..R, (f (q + 2 * t) - f q) * (g (q + 2 * t) - g q)|
        ≤ 4 * Lf * Lg * t ^ 2 * R := this
      _ = 4 * R * Lf * Lg * t ^ 2 := by ring
  rw [e1]
  have hπ : 0 ≤ Real.pi ^ 2 := by positivity
  rw [abs_le] at hb1 hb2 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb1.1 hπ, mul_le_mul_of_nonneg_left hb1.2 hπ,
    mul_le_mul_of_nonneg_left hb2.1 hπ, mul_le_mul_of_nonneg_left hb2.2 hπ]

/-- ★★★ **The corner limit**: `(L(t) + L(−t) − 2L(0))/t → −4π² f(0) g(0)` as `t → 0⁺` — the
derivative of the product-radial Leray density jumps by `−4π²F(0)` at the vertex. -/
theorem tendsto_coneProductDensity_corner (hf : ConeProfile f R Lf) (hg : ConeProfile g R Lg)
    (hR : 0 ≤ R) :
    Tendsto (fun t : ℝ => (coneProductDensity f g t + coneProductDensity f g (-t) -
      2 * coneProductDensity f g 0) / t) (𝓝[>] 0) (𝓝 (-(4 * Real.pi ^ 2 * f 0 * g 0))) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun t : ℝ => 24 * Real.pi ^ 2 * R * Lf * Lg * t) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hb := coneProductDensity_corner_bound hf hg hR ht0.le
    rw [Real.norm_eq_abs, show (coneProductDensity f g t + coneProductDensity f g (-t) -
      2 * coneProductDensity f g 0) / t - -(4 * Real.pi ^ 2 * f 0 * g 0) =
      (coneProductDensity f g t + coneProductDensity f g (-t) - 2 * coneProductDensity f g 0 +
        4 * Real.pi ^ 2 * f 0 * g 0 * t) / t by field_simp; ring, abs_div, abs_of_pos ht0,
      div_le_iff₀ ht0]
    exact hb.trans (le_of_eq (by ring))
  · exact tendsto_nhdsWithin_of_tendsto_nhds (by
      have : Tendsto (fun t : ℝ => 24 * Real.pi ^ 2 * R * Lf * Lg * t) (𝓝 0)
          (𝓝 (24 * Real.pi ^ 2 * R * Lf * Lg * 0)) := (continuous_const.mul continuous_id).tendsto 0
      simpa using this)

end Grammar
