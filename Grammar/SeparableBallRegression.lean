/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus Research
-/
import Grammar.CoefficientLocality
import Grammar.BlowUpCubeGaussian

/-!
# The separable-ball regression (CCLXXXVI)

The third unit of the locality programme (consult #86, B3): for the separable phase
`K(x) = ∑ x_i^{2k_i}` (`k_i ≥ 1`) and any compact region `Rg` squeezed between two cubes centred at
the isolated zero `0` — a Euclidean ball, a sup-ball, any such neighbourhood — and any continuous
nonnegative amplitude `f` with `f(0) > 0`,
`∫_{Rg} f e^{−N K} ~ f(0) · ∏_i Γ(1/(2k_i))/k_i · N^{−∑_i 1/(2k_i)}`
(★★ `hasLeadingTerm_region`, `region_isEquivalent`):

* the one-dimensional truncated integral `∫_{−r}^{r} e^{−N t^{2k}} dt` is
  `Γ(1/(2k))/k · N^{−1/(2k)}` minus an exponentially small tail (Mathlib's
  `integral_rpow_mul_exp_neg_mul_rpow` on the half-line and the tail bound
  `e^{−N t^{2k}} ≤ e^{−(N−1) r^{2k}} e^{−t^{2k}}` for `t ≥ r`), hence a leading-term certificate
  (`hasLeadingTerm_oneDim`);
* Fubini on the cube and the product of certificates (`IsEquivalent.finsetProd`) give the cube
  (`hasLeadingTerm_cube`); coefficient locality (CCLXXXV) transfers the certificate to any region
  between two cubes (the phase has a gap off any cube around the isolated zero);
* the amplitude is handled by the sandwich `(f(0) − ε) ∫_{cube η} e^{−NK} ≤ ∫_{Rg} f e^{−NK} ≤
  (f(0) + ε) ∫_{cube η} e^{−NK} + (exponentially small)` on a small cube `η` from the continuity of
  `f` at `0` (`tendsto_div_of_approx_squeeze`).

The exponent `∑ 1/(2k_i)` is the RLCT of the separable phase at its isolated zero; the constant is
the product of the one-dimensional constants — the Newton-polyhedron additivity, here by Fubini.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

namespace Separable

/-! ### Exponentially small remainders, eventual form -/

/-- An eventual exponential bound gives `o` of every power–log scale. -/
theorem isLittleO_powLogScale_of_eventually_exp_le {r : ℝ → ℝ} {C κ : ℝ} (hκ : 0 < κ)
    (h : ∀ᶠ N in atTop, |r N| ≤ C * Real.exp (-κ * N)) (lam : ℝ) (k : ℕ) :
    r =o[atTop] powLogScale lam k := by
  have h1 : r =O[atTop] fun N => Real.exp (-κ * N) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [h] with N hN
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h2 : (fun N : ℝ => Real.exp (-κ * N)) =o[atTop] fun N : ℝ => N ^ (-lam) :=
    isLittleO_exp_neg_mul_rpow_atTop hκ (-lam)
  exact (h1.trans_isLittleO h2).trans_isBigO (rpow_neg_isBigO_powLogScale lam k)

/-- An exact power is its own certificate. -/
theorem hasLeadingTerm_const_mul_rpow (c lam : ℝ) :
    HasLeadingTerm (fun N : ℝ => c * N ^ (-lam)) c lam 0 := by
  refine tendsto_const_nhds.congr' ((eventually_gt_atTop 1).mono fun N hN => ?_)
  beta_reduce
  unfold powLogScale
  rw [pow_zero, mul_one, mul_div_assoc, div_self (Real.rpow_pos_of_pos (by linarith) _).ne',
    mul_one]

/-! ### The one-dimensional truncated integral -/

variable {k : ℕ} (hk : 0 < k)

/-- The one-dimensional constant `Γ(1/(2k))/k`. -/
noncomputable def oneDimConst (k : ℕ) : ℝ := Real.Gamma (1 / (2 * k)) / k

include hk in
theorem oneDimConst_pos : 0 < oneDimConst k :=
  div_pos (Real.Gamma_pos_of_pos (by positivity)) (by exact_mod_cast hk)

include hk in
/-- The half-line integral (Mathlib's Gamma integral). -/
theorem integral_Ioi_exp_neg_pow {N : ℝ} (hN : 0 < N) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-N * t ^ (2 * k)) =
      N ^ (-(1 / (2 * k : ℝ))) * (Real.Gamma (1 / (2 * k)) / (2 * k)) := by
  have hp : (0 : ℝ) < 2 * k := by positivity
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2 * k) (q := 0) hp neg_one_lt_zero hN
  have heq : (fun t : ℝ => Real.exp (-N * t ^ (2 * k))) =ᵐ[volume.restrict (Ioi 0)]
      fun x => x ^ (0 : ℝ) * Real.exp (-N * x ^ (2 * k : ℝ)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x _ => ?_)
    show Real.exp (-N * x ^ (2 * k)) = x ^ (0 : ℝ) * Real.exp (-N * x ^ (2 * k : ℝ))
    rw [Real.rpow_zero, one_mul, show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [integral_congr_ae heq, h, show -(0 + 1) / (2 * (k : ℝ)) = -(1 / (2 * k)) by ring,
    show (0 + 1) / (2 * (k : ℝ)) = 1 / (2 * k) by ring]
  ring

include hk in
theorem integrableOn_exp_neg_pow_Ioi {N : ℝ} (hN : 0 < N) :
    IntegrableOn (fun t : ℝ => Real.exp (-N * t ^ (2 * k))) (Ioi 0) := by
  have hp : (0 : ℝ) < 2 * k := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2 * k) (s := 0) neg_one_lt_zero hp hN
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show x ^ (0 : ℝ) * Real.exp (-N * x ^ (2 * k : ℝ)) = Real.exp (-N * x ^ (2 * k))
  rw [Real.rpow_zero, one_mul, show (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

include hk in
theorem integrableOn_exp_neg_pow_Ioi' :
    IntegrableOn (fun t : ℝ => Real.exp (-t ^ (2 * k))) (Ioi 0) :=
  (integrableOn_exp_neg_pow_Ioi hk one_pos).congr_fun (fun x _ => by
    show Real.exp (-1 * x ^ (2 * k)) = Real.exp (-x ^ (2 * k))
    rw [neg_one_mul]) measurableSet_Ioi

include hk in
/-- **The tail bound**: for `N ≥ 1`,
`∫_{t ≥ r} e^{−N t^{2k}} ≤ e^{−(N−1) r^{2k}} ∫_{t ≥ r} e^{−t^{2k}}`. -/
theorem tail_le {r : ℝ} (hr : 0 < r) {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k)) ≤
      Real.exp (-(N - 1) * r ^ (2 * k)) * ∫ t in Ioi r, Real.exp (-t ^ (2 * k)) := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on
    ((integrableOn_exp_neg_pow_Ioi hk (by linarith : (0 : ℝ) < N)).mono_set (Ioi_subset_Ioi hr.le))
    (((integrableOn_exp_neg_pow_Ioi' hk).mono_set (Ioi_subset_Ioi hr.le)).const_mul _)
    measurableSet_Ioi fun t ht => ?_
  have ht' : r ^ (2 * k) ≤ t ^ (2 * k) := pow_le_pow_left₀ hr.le (le_of_lt ht) _
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [ht', sub_nonneg.2 hN]

include hk in
/-- The symmetric truncated integral is twice the one-sided one. -/
theorem integral_Icc_eq_two_mul {r : ℝ} (hr : 0 < r) (N : ℝ) :
    ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * k)) =
      2 * ∫ t in Ioc 0 r, Real.exp (-N * t ^ (2 * k)) := by
  have heven : ∀ t : ℝ, Real.exp (-N * |t| ^ (2 * k)) = Real.exp (-N * t ^ (2 * k)) := fun t => by
    rw [(even_two_mul k).pow_abs]
  have hind : ∀ t : ℝ, (Icc (-r) r).indicator (fun t => Real.exp (-N * t ^ (2 * k))) t =
      (Icc 0 r).indicator (fun s => Real.exp (-N * s ^ (2 * k))) |t| := fun t => by
    by_cases ht : t ∈ Icc (-r) r
    · rw [indicator_of_mem ht,
        indicator_of_mem (show |t| ∈ Icc 0 r from ⟨abs_nonneg t, abs_le.2 ⟨ht.1, ht.2⟩⟩), heven]
    · rw [indicator_of_notMem ht, indicator_of_notMem]
      intro h
      exact ht (abs_le.1 h.2)
  have hset : Ioi (0 : ℝ) ∩ Icc 0 r = Ioc 0 r := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h1.le, h2⟩
  rw [← integral_indicator measurableSet_Icc, integral_congr_ae (Eventually.of_forall hind),
    integral_comp_abs (f := fun s => (Icc 0 r).indicator (fun s => Real.exp (-N * s ^ (2 * k))) s),
    setIntegral_indicator measurableSet_Icc, hset]

include hk in
/-- ★ **The one-dimensional truncated integral**: `∫_{−r}^{r} e^{−N t^{2k}} dt` has the leading term
`Γ(1/(2k))/k · N^{−1/(2k)}`. -/
theorem hasLeadingTerm_oneDim {r : ℝ} (hr : 0 < r) :
    HasLeadingTerm (fun N : ℝ => ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * k)))
      (oneDimConst k) (1 / (2 * k)) 0 := by
  set T : ℝ → ℝ := fun N => -2 * ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k)) with hT
  have hsplit : ∀ N : ℝ, 0 < N → ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * k)) =
      oneDimConst k * N ^ (-(1 / (2 * k : ℝ))) + T N := fun N hN => by
    rw [integral_Icc_eq_two_mul hk hr]
    have hu : ∫ t in Ioi 0, Real.exp (-N * t ^ (2 * k)) =
        (∫ t in Ioc 0 r, Real.exp (-N * t ^ (2 * k))) +
          ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k)) := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((integrableOn_exp_neg_pow_Ioi hk hN).mono_set Ioc_subset_Ioi_self)
        ((integrableOn_exp_neg_pow_Ioi hk hN).mono_set (Ioi_subset_Ioi hr.le)),
        Ioc_union_Ioi_eq_Ioi hr.le]
    rw [integral_Ioi_exp_neg_pow hk hN] at hu
    simp only [hT, oneDimConst]
    have : (2 * ∫ t in Ioc 0 r, Real.exp (-N * t ^ (2 * k))) =
        2 * (N ^ (-(1 / (2 * k : ℝ))) * (Real.Gamma (1 / (2 * k)) / (2 * k)) -
          ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k))) := by
      rw [hu]
      ring
    rw [this]
    field_simp
    ring
  have hTail : T =o[atTop] powLogScale (1 / (2 * k)) 0 := by
    refine isLittleO_powLogScale_of_eventually_exp_le (r := T)
      (C := 2 * Real.exp (r ^ (2 * k)) * ∫ t in Ioi r, Real.exp (-t ^ (2 * k)))
      (κ := r ^ (2 * k)) (by positivity) ?_ _ _
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
    have hint := (integrableOn_exp_neg_pow_Ioi hk (by linarith : (0 : ℝ) < N)).mono_set
      (Ioi_subset_Ioi hr.le)
    have hnn : 0 ≤ ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k)) :=
      setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le
    rw [hT]
    simp only
    rw [abs_mul, abs_of_nonneg hnn, abs_neg, abs_two]
    have htl := tail_le hk hr hN
    have hexp : Real.exp (-(N - 1) * r ^ (2 * k)) =
        Real.exp (r ^ (2 * k)) * Real.exp (-r ^ (2 * k) * N) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at htl
    calc 2 * ∫ t in Ioi r, Real.exp (-N * t ^ (2 * k))
        ≤ 2 * (Real.exp (r ^ (2 * k)) * Real.exp (-r ^ (2 * k) * N) *
          ∫ t in Ioi r, Real.exp (-t ^ (2 * k))) := by gcongr
      _ = 2 * Real.exp (r ^ (2 * k)) * (∫ t in Ioi r, Real.exp (-t ^ (2 * k))) *
          Real.exp (-r ^ (2 * k) * N) := by ring
  exact ((hasLeadingTerm_const_mul_rpow (oneDimConst k) (1 / (2 * k))).add_isLittleO
    hTail).congr' ((eventually_gt_atTop 0).mono fun N hN => (hsplit N hN).symm)

/-! ### The separable phase on the cube -/

variable {d : ℕ} (ks : Fin d → ℕ) (hks : ∀ i, 0 < ks i)

/-- The separable phase `K(x) = ∑ x_i^{2 k_i}`. -/
noncomputable def K (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ (2 * ks i)

theorem K_nonneg (x : Fin d → ℝ) : 0 ≤ K ks x :=
  Finset.sum_nonneg fun i _ => ((even_two_mul (ks i)).pow_abs (x i)) ▸ pow_nonneg (abs_nonneg _) _

theorem continuous_K : Continuous (K ks) := by
  unfold K
  fun_prop

include hks in
/-- The origin is the unique zero. -/
theorem eq_zero_of_K_eq_zero {x : Fin d → ℝ} (hx : K ks x = 0) : x = 0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    ((even_two_mul (ks i)).pow_abs (x i)) ▸ pow_nonneg (abs_nonneg _) _).1 hx
  funext i
  have := h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (by have := hks i; omega) |>.1 this

/-- The exponent `λ = ∑ 1/(2k_i)`. -/
noncomputable def lam : ℝ := ∑ i, (1 / (2 * ks i) : ℝ)

/-- The constant `∏ Γ(1/(2k_i))/k_i`. -/
noncomputable def const : ℝ := ∏ i, oneDimConst (ks i)

include hks in
theorem const_pos : 0 < const ks := Finset.prod_pos fun i _ => oneDimConst_pos (hks i)

/-- The cube `[−r, r]^d`. -/
def cube (r : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Icc (-r) r

theorem mem_cube {r : ℝ} {x : Fin d → ℝ} : x ∈ cube r ↔ ∀ i, |x i| ≤ r := by
  simp only [cube, Set.mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem isCompact_cube (r : ℝ) : IsCompact (cube (d := d) r) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem cube_eq_closedBall {r : ℝ} (hr : 0 ≤ r) : cube (d := d) r = Metric.closedBall 0 r := by
  ext x
  rw [mem_cube, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  simp only [Real.norm_eq_abs]

theorem cube_mono {r r' : ℝ} (h : r' ≤ r) : cube (d := d) r' ⊆ cube r := fun _ hx =>
  mem_cube.2 fun i => (mem_cube.1 hx i).trans h

/-- **Fubini on the cube**: the separable integral is the product of the one-dimensional ones. -/
theorem integral_cube_eq_prod (r : ℝ) (N : ℝ) :
    ∫ x in cube r, Real.exp (-N * K ks x) =
      ∏ i, ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * ks i)) := by
  have h1 : ∀ x : Fin d → ℝ, Real.exp (-N * K ks x) = ∏ i, Real.exp (-N * x i ^ (2 * ks i)) :=
    fun x => by rw [K, Finset.mul_sum, Real.exp_sum]
  have h2 : ∀ x : Fin d → ℝ, (cube r).indicator (fun x => ∏ i, Real.exp (-N * x i ^ (2 * ks i))) x
      = ∏ i, (Icc (-r) r).indicator (fun t => Real.exp (-N * t ^ (2 * ks i))) (x i) := fun x => by
    by_cases hx : x ∈ cube r
    · rw [indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem]
      have := mem_cube.1 hx i
      rw [abs_le] at this
      exact ⟨this.1, this.2⟩
    · rw [indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ Icc (-r) r := by
        by_contra hcon
        have hall : ∀ j, x j ∈ Icc (-r) r := fun j => Classical.not_not.1 fun h => hcon ⟨j, h⟩
        exact hx (mem_cube.2 fun j => abs_le.2 ⟨(hall j).1, (hall j).2⟩)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [setIntegral_congr_fun (isCompact_cube r).isClosed.measurableSet fun x _ => h1 x,
    ← integral_indicator (isCompact_cube r).isClosed.measurableSet,
    integral_congr_ae (Eventually.of_forall h2),
    integral_fintype_prod_volume_eq_prod (fun (i : Fin d) (t : ℝ) =>
      (Icc (-r) r).indicator (fun t => Real.exp (-N * t ^ (2 * ks i))) t)]
  exact Finset.prod_congr rfl fun i _ => integral_indicator measurableSet_Icc

include hks in
/-- ★ **The cube certificate**: `∫_{[−r,r]^d} e^{−N K} = const · N^{−λ} + o(·)`. -/
theorem hasLeadingTerm_cube {r : ℝ} (hr : 0 < r) :
    HasLeadingTerm (fun N : ℝ => ∫ x in cube r, Real.exp (-N * K ks x)) (const ks) (lam ks) 0 := by
  have h : (fun N : ℝ => ∏ i, ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * ks i))) ~[atTop]
      fun N => ∏ i, oneDimConst (ks i) * N ^ (-(1 / (2 * ks i) : ℝ)) :=
    IsEquivalent.finsetProd fun i _ => (hasLeadingTerm_oneDim (hks i) hr).isEquivalent
      (oneDimConst_pos (hks i)).ne' |>.congr_right (Eventually.of_forall fun N => by
        simp [powLogScale])
  have hZ : (fun N : ℝ => ∫ x in cube r, Real.exp (-N * K ks x)) =
      fun N => ∏ i, ∫ t in Icc (-r) r, Real.exp (-N * t ^ (2 * ks i)) :=
    funext fun N => integral_cube_eq_prod ks r N
  rw [hZ]
  refine hasLeadingTerm_of_isEquivalent (h.congr_right ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hN]
  simp only [const, lam, powLogScale, pow_zero, mul_one, Finset.sum_neg_distrib]

/-! ### Any region between two cubes -/

variable {r' r : ℝ} (hr' : 0 < r') (hrr : r' ≤ r) {Rg : Set (Fin d → ℝ)} (hRg : MeasurableSet Rg)
  (hsub₁ : cube r' ⊆ Rg) (hsub₂ : Rg ⊆ cube r)

include hks hr' hsub₂ in
/-- The phase has a gap on the region off the inner cube. -/
theorem exists_gap : ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ Rg \ cube r', κ ≤ K ks x := by
  obtain ⟨κ, hκ, h⟩ := exists_gap_of_isolatedZero (isCompact_cube r) (continuous_K ks).continuousOn
    (K_nonneg ks) (w := 0) (fun x _ hx => eq_zero_of_K_eq_zero ks hks hx) hr'
  refine ⟨κ, hκ, fun x hx => h x ⟨hsub₂ hx.1, fun hb => hx.2 ?_⟩⟩
  rw [cube_eq_closedBall hr'.le]
  exact Metric.ball_subset_closedBall hb

include hks hr' hrr hRg hsub₁ hsub₂ in
/-- ★★ **The region certificate for the unit amplitude**: any region between two cubes around the
isolated zero carries the cube leading term. -/
theorem hasLeadingTerm_region_one :
    HasLeadingTerm (fun N : ℝ => ∫ x in Rg, Real.exp (-N * K ks x)) (const ks) (lam ks) 0 := by
  obtain ⟨κ, hκ, hgap⟩ := exists_gap ks hks hr' hsub₂
  have h := hasLeadingTerm_cube ks hks hr'
  have hZ : ∀ S : Set (Fin d → ℝ), (fun N : ℝ => ∫ x in S, Real.exp (-N * K ks x)) =
      targetIntegral S (fun _ => (1 : ℝ)) (K ks) (TubeWeight.one d) := fun S => funext fun N => by
    unfold targetIntegral
    simp
  rw [hZ] at h ⊢
  refine h.targetIntegral_of_locality (isCompact_cube r').isClosed.measurableSet hRg ?_
    (continuous_K ks).measurable (K_nonneg ks) hκ ?_ ?_
  · refine (integrableOn_const (C := (1 : ℝ)) (isCompact_cube r).measure_lt_top.ne).mono_set
      (union_subset (cube_mono hrr) hsub₂) |>.congr (Eventually.of_forall fun x => ?_)
    simp
  · rw [sdiff_eq_empty.2 hsub₁]
    simp
  · exact ae_restrict_of_forall_mem (hRg.diff (isCompact_cube r').isClosed.measurableSet) hgap

/-! ### A continuous amplitude -/

variable {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hfpos : 0 < f 0)

include hks hr' hrr hRg hsub₁ hsub₂ hf hf0 in
/-- ★★ **The separable-ball regression**: for a continuous nonnegative amplitude positive at the
isolated zero, `∫_{Rg} f e^{−N K} = f(0) · ∏ Γ(1/(2k_i))/k_i · N^{−∑ 1/(2k_i)} + o(·)`. -/
theorem hasLeadingTerm_region :
    HasLeadingTerm (fun N : ℝ => ∫ x in Rg, f x * Real.exp (-N * K ks x)) (f 0 * const ks)
      (lam ks) 0 := by
  unfold HasLeadingTerm
  refine tendsto_div_of_approx_squeeze ((eventually_gt_atTop 1).mono fun N hN =>
    powLogScale_pos _ _ hN) fun ε hε => ?_
  -- the continuity window
  set ε₁ : ℝ := ε / (const ks + 1) with hε₁
  have hε₁pos : 0 < ε₁ := div_pos hε (by linarith [const_pos ks hks])
  obtain ⟨η₀, hη₀, hη⟩ := Metric.continuousAt_iff.1 hf.continuousAt ε₁ hε₁pos
  set η : ℝ := min (η₀ / 2) r' with hηdef
  have hηpos : 0 < η := lt_min (half_pos hη₀) hr'
  have hηr' : η ≤ r' := min_le_right _ _
  have hclose : ∀ x ∈ cube (d := d) η, |f x - f 0| ≤ ε₁ := fun x hx => by
    have hx' : dist x 0 < η₀ := by
      rw [cube_eq_closedBall hηpos.le] at hx
      exact lt_of_le_of_lt (Metric.mem_closedBall.1 hx) (lt_of_le_of_lt (min_le_left _ _)
        (half_lt_self hη₀))
    have := hη hx'
    rw [Real.dist_eq] at this
    exact this.le
  have hcubeη : cube η ⊆ Rg := (cube_mono hηr').trans hsub₁
  have hηmeas : MeasurableSet (cube (d := d) η) := (isCompact_cube η).isClosed.measurableSet
  -- the gap off the small cube
  obtain ⟨κ, hκ, hgap⟩ := exists_gap ks hks hηpos hsub₂
  -- integrability
  have hfint : IntegrableOn f (cube r) := hf.continuousOn.integrableOn_compact (isCompact_cube r)
  have hfp : IntegrableOn (fun x => f x * (TubeWeight.one d).w x) Rg :=
    (hfint.mono_set hsub₂).congr (Eventually.of_forall fun x => by simp)
  have hgN : ∀ N : ℝ, 0 ≤ N → IntegrableOn (fun x => f x * Real.exp (-N * K ks x)) Rg :=
    fun N hN =>
    (integrableOn_boltzmann_of_integrableOn hfp (continuous_K ks).measurable (K_nonneg ks)
      hN).congr (Eventually.of_forall fun x => by simp)
  have hexpint : ∀ N : ℝ, IntegrableOn (fun x => Real.exp (-N * K ks x)) (cube η) := fun N =>
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_K ks))).continuousOn.integrableOn_compact (isCompact_cube η)
  -- the small-cube certificate and the remainder
  have hcube := hasLeadingTerm_cube ks hks hηpos
  have hrem : HasExponentialBound fun N => ∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x) :=
    hasExponentialBound_setIntegral (hfint.mono_set (sdiff_subset.trans hsub₂)) hκ
      (ae_restrict_of_forall_mem (hRg.diff hηmeas) hgap)
  have hremo : (fun N => ∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x)) =o[atTop]
      powLogScale (lam ks) 0 := hrem.isLittleO_powLogScale _ _
  have hrem0 : Tendsto (fun N => (∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x)) /
      powLogScale (lam ks) 0 N) atTop (𝓝 0) := hremo.tendsto_div_nhds_zero
  refine ⟨fun N => (f 0 - ε₁) * ∫ x in cube η, Real.exp (-N * K ks x),
    fun N => (f 0 + ε₁) * (∫ x in cube η, Real.exp (-N * K ks x)) +
      ∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x),
    (f 0 - ε₁) * const ks, (f 0 + ε₁) * const ks, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with N hN
    have hsplit : ∫ x in Rg, f x * Real.exp (-N * K ks x) =
        (∫ x in cube η, f x * Real.exp (-N * K ks x)) +
          ∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x) := by
      rw [← setIntegral_union disjoint_sdiff_right (hRg.diff hηmeas)
        ((hgN N hN).mono_set hcubeη) ((hgN N hN).mono_set sdiff_subset),
        union_sdiff_cancel hcubeη]
    have hlo : (f 0 - ε₁) * ∫ x in cube η, Real.exp (-N * K ks x) ≤
        ∫ x in cube η, f x * Real.exp (-N * K ks x) := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((hexpint N).const_mul _) ((hgN N hN).mono_set hcubeη) hηmeas
        fun x hx => ?_
      have := hclose x hx
      rw [abs_le] at this
      exact mul_le_mul_of_nonneg_right (by linarith [this.1]) (Real.exp_pos _).le
    have hhi : ∫ x in cube η, f x * Real.exp (-N * K ks x) ≤
        (f 0 + ε₁) * ∫ x in cube η, Real.exp (-N * K ks x) := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((hgN N hN).mono_set hcubeη) ((hexpint N).const_mul _) hηmeas
        fun x hx => ?_
      have := hclose x hx
      rw [abs_le] at this
      exact mul_le_mul_of_nonneg_right (by linarith [this.2]) (Real.exp_pos _).le
    have hnn : 0 ≤ ∫ x in Rg \ cube η, f x * Real.exp (-N * K ks x) :=
      setIntegral_nonneg (hRg.diff hηmeas) fun x _ => mul_nonneg (hf0 x) (Real.exp_pos _).le
    rw [hsplit]
    constructor
    · linarith
    · linarith
  · have := hcube.const_mul (f 0 - ε₁)
    exact this
  · have h1 := hcube.const_mul (f 0 + ε₁)
    have h2 := (Tendsto.add h1 hrem0)
    rw [add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun N => ?_)
    simp only [add_div]
  · rw [hε₁]
    have hc := const_pos ks hks
    rw [sub_mul]
    have : ε / (const ks + 1) * const ks ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [hε₁]
    have hc := const_pos ks hks
    rw [add_mul]
    have : ε / (const ks + 1) * const ks ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith

include hks hr' hrr hRg hsub₁ hsub₂ hf hf0 hfpos in
/-- ★★ `∫_{Rg} f e^{−N ∑ x_i^{2k_i}} ~ f(0) ∏ Γ(1/(2k_i))/k_i · N^{−∑ 1/(2k_i)}`. -/
theorem region_isEquivalent :
    (fun N : ℝ => ∫ x in Rg, f x * Real.exp (-N * K ks x)) ~[atTop]
      fun N => f 0 * const ks * N ^ (-lam ks) := by
  refine ((hasLeadingTerm_region ks hks hr' hrr hRg hsub₁ hsub₂ hf hf0).isEquivalent
    (mul_pos hfpos (const_pos ks hks)).ne').congr_right (Eventually.of_forall fun N => ?_)
  simp [powLogScale]

end Separable

end Grammar
