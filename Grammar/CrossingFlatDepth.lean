/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammar.CrossingFlatAllOrders
import Grammar.ConeClosedForm
import Grammar.StateDensityPolar

/-!
# The deep linear network with flat prior at general depth: the one-dimensional reduction

The state density of the depth-`L` scalar deep linear network with flat prior on `[−1, 1]^L` is
`(2^m/m!) log^m(1/|t|)` with `m = L − 1` (examples_slop §2, the derivative of the volume identity
`eq:dln_volume`), so its partition function is the reduced integral

  `D_m(N) = 2 ∫_0^1 e^{−N t²/2} (2^m/m!) log^m(1/t) dt`  (`depthInt`).

The substitution `x = N t²/2` (`integral_image_eq_integral_abs_deriv_smul`) turns it into the
truncated Gamma-type integral `√2/(m! √N) ∫_0^{N/2} e^{−x} x^{−1/2} (log N − log 2 − log x)^m dx`,
and the binomial expansion of the last factor gives (★★★ `depth_flat_allOrders`)

  `D_m(N) = √2/(m! √N) · P_m(log N − log 2) − R_m(N)`,
  `P_m(X) = Σ_j C(m,j) X^j (−1)^{m−j} H_{m−j}`,   `H_j = ∫_0^∞ e^{−x} x^{−1/2} log^j x dx`,

with the tail `|R_m(N)| ≤ (2/N)^{m+1} e^{−N/2}` (`depthTail_abs_le`, from `log(2x/N) ≤ 2(x−N/2)/N`
and `∫_{N/2}^∞ e^{−x}(x − N/2)^m = m! e^{−N/2}`): the complete polynomial-in-`log N` expansion of
eq. (dln_flat) at every depth, with an exponentially small remainder, as an exact identity.  The
Gamma log-moments `H_j = Γ^{(j)}(½)` are left as constants; `H_0 = √π` and
`H_1 = −√π(γ + 2 log 2)` are evaluated (`gammaLogMoment_zero/one`), and at `m = 1` the formula
reproduces the depth-two expansion `√(2π)/√N (log N + γ + log 2)` of `crossing_flat_allOrders`
(`depthInt_one`).  Astra next-round target 3.  Zero `sorry`/`axiom`.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace Grammar

/-- The Gamma log-moment `H_j = ∫_0^∞ e^{−x} x^{−1/2} log^j x dx` (`= Γ^{(j)}(½)`). -/
noncomputable def gammaLogMoment (j : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ j

/-- `P_m(X) = ∫_0^∞ e^{−x} x^{−1/2} (X − log x)^m dx = Σ_j C(m,j) X^j (−1)^{m−j} H_{m−j}`
(`= √π Q_m(X)` in the note's normalisation). -/
noncomputable def depthPoly (m : ℕ) (X : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), X ^ j * ((-1) ^ (m - j) * gammaLogMoment (m - j)) * (m.choose j)

/-- The reduced partition function at depth `m + 1`:
`2 ∫_0^1 e^{−N t²/2} (2^m/m!) log^m(1/t) dt`. -/
noncomputable def depthInt (m : ℕ) (N : ℝ) : ℝ :=
  2 * ∫ t in Ioc (0 : ℝ) 1, Real.exp (-N * t ^ 2 / 2) * (2 ^ m / m.factorial) * Real.log (1 / t) ^ m

/-- The tail `R_m(N) = √2/(m!√N) ∫_{N/2}^∞ e^{−x} x^{−1/2} (log N − log 2 − log x)^m dx`. -/
noncomputable def depthTail (m : ℕ) (N : ℝ) : ℝ :=
  Real.sqrt 2 / (m.factorial * Real.sqrt N) *
    ∫ x in Ioi (N / 2), Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) *
      (Real.log N - Real.log 2 - Real.log x) ^ m

/-! ### Integrability of the Gamma log-moments -/

theorem measurable_wt_log_pow (j : ℕ) :
    Measurable fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ j := by
  fun_prop

/-- `e^{−x} x^{−1/2} log^j x` is integrable on `(0, ∞)`. -/
theorem integrableOn_wt_log_pow (j : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ j) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- near zero: `|log t|^j ≤ (t^{−δ}/δ)^j`
    set δ : ℝ := 1 / (4 * (j + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hjδ : (j : ℝ) * δ ≤ 1 / 4 := by
      rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      nlinarith
    refine ((integrableOn_rpow_Ioc (c := -(1 / 2 : ℝ) - j * δ) (by linarith)).const_mul
      (1 / δ ^ j)).mono' (measurable_wt_log_pow j).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_pow]
    have hlog : |Real.log t| ^ j ≤ (t ^ (-δ) / δ) ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_rpow_div hδpos ht) j
    have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * |Real.log t| ^ j
        ≤ 1 * t ^ (-(1 / 2 : ℝ)) * (t ^ (-δ) / δ) ^ j := by
          gcongr
      _ = 1 / δ ^ j * t ^ (-(1 / 2 : ℝ) - j * δ) := by
          rw [div_pow, ← Real.rpow_natCast (t ^ (-δ)), ← Real.rpow_mul ht0.le,
            show -(1 / 2 : ℝ) - j * δ = -(1 / 2) + -δ * j by ring, Real.rpow_add ht0]
          field_simp
  · -- at infinity: `|log x|^j ≤ x^j`
    have hint : IntegrableOn (fun x : ℝ => x ^ ((j : ℝ) - 1 / 2) * Real.exp (-x ^ (1 : ℝ)))
        (Ioi 0) := integrableOn_rpow_mul_exp_neg_rpow (by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
          linarith) one_pos
    refine (hint.mono_set (Ioi_subset_Ioi zero_le_one)).mono'
      (measurable_wt_log_pow j).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_pow, abs_of_nonneg (Real.log_nonneg ht1.le),
      Real.rpow_one]
    have hlog : Real.log t ^ j ≤ t ^ j :=
      pow_le_pow_left₀ (Real.log_nonneg ht1.le) (by linarith [Real.log_le_sub_one_of_pos ht0]) j
    calc Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * Real.log t ^ j
        ≤ Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) * t ^ j := by gcongr
      _ = t ^ ((j : ℝ) - 1 / 2) * Real.exp (-t) := by
          rw [← Real.rpow_natCast t j, show (j : ℝ) - 1 / 2 = -(1 / 2) + j by ring,
            Real.rpow_add ht0]
          ring

/-! ### The binomial expansion and the full integral -/

theorem sub_log_pow_expand (X x : ℝ) (m : ℕ) :
    Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (X - Real.log x) ^ m =
      ∑ j ∈ Finset.range (m + 1), (X ^ j * (-1) ^ (m - j) * (m.choose j)) *
        (Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ (m - j)) := by
  rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow]
  ring

theorem integrableOn_wt_sub_log_pow (X : ℝ) (m : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (X - Real.log x) ^ m)
      (Ioi 0) := by
  simp_rw [sub_log_pow_expand]
  exact integrable_finsetSum _ fun j _ => (integrableOn_wt_log_pow (m - j)).const_mul _

/-- `∫_0^∞ e^{−x} x^{−1/2} (X − log x)^m dx = P_m(X)`. -/
theorem integral_wt_sub_log_pow (X : ℝ) (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (X - Real.log x) ^ m =
      depthPoly m X := by
  simp_rw [sub_log_pow_expand]
  rw [integral_finsetSum _ fun j _ => (integrableOn_wt_log_pow (m - j)).const_mul _]
  unfold depthPoly gammaLogMoment
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

/-! ### The substitution `x = N t²/2` -/

theorem image_sq_scale {r : ℝ} (hr : 0 < r) :
    (fun t : ℝ => r ^ 2 * t ^ 2 / 2) '' Ioo 0 1 = Ioo 0 (r ^ 2 / 2) := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨by positivity, ?_⟩
    have : t ^ 2 < 1 := by nlinarith
    have hr2 : 0 < r ^ 2 := by positivity
    nlinarith
  · rintro ⟨hx0, hx1⟩
    refine ⟨Real.sqrt (2 * x) / r, ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one hr, Real.sqrt_lt' hr]
      linarith
    · simp only
      rw [div_pow, Real.sq_sqrt (by positivity)]
      field_simp

theorem injOn_sq_scale {r : ℝ} (hr : 0 < r) :
    InjOn (fun t : ℝ => r ^ 2 * t ^ 2 / 2) (Ioo 0 1) := by
  intro a ha b hb h
  simp only at h
  have h2 : a ^ 2 = b ^ 2 := by
    have hr2 : (0 : ℝ) < r ^ 2 := by positivity
    have : r ^ 2 * a ^ 2 = r ^ 2 * b ^ 2 := by linarith
    exact mul_left_cancel₀ hr2.ne' this
  exact (sq_eq_sq₀ ha.1.le hb.1.le).1 h2

/-- The substitution `x = r² t²/2` on `(0,1)`, `N = r²`. -/
theorem integral_Ioo_half_eq (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioo (0 : ℝ) (r ^ 2 / 2), Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) *
        (Real.log (r ^ 2) - Real.log 2 - Real.log x) ^ m =
      Real.sqrt 2 * r * ∫ t in Ioo (0 : ℝ) 1,
        Real.exp (-r ^ 2 * t ^ 2 / 2) * (2 ^ m * Real.log (1 / t) ^ m) := by
  rw [← image_sq_scale hr, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (f' := fun t => r ^ 2 * t) (fun t _ => by
      have := ((hasDerivAt_pow 2 t).const_mul (r ^ 2)).div_const 2
      refine this.hasDerivWithinAt.congr_deriv ?_
      push_cast
      ring) (injOn_sq_scale hr), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [smul_eq_mul, abs_of_pos (by positivity)]
  have hlog : Real.log (r ^ 2) - Real.log 2 - Real.log (r ^ 2 * t ^ 2 / 2) =
      2 * Real.log (1 / t) := by
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring
  have hpow : (r ^ 2 * t ^ 2 / 2) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 / (r * t) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show r ^ 2 * t ^ 2 / 2 = (r * t / Real.sqrt 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)],
      Real.sqrt_sq (by positivity), inv_div]
  rw [hlog, hpow, mul_pow]
  field_simp

/-! ### The main identity -/

/-- ★★★ **The flat-prior partition function at general depth**:
`D_m(N) = √2/(m!√N) · P_m(log N − log 2) − R_m(N)` for every `N > 0`. -/
theorem depth_flat_allOrders (m : ℕ) {N : ℝ} (hN : 0 < N) :
    depthInt m N = Real.sqrt 2 / (m.factorial * Real.sqrt N) *
      depthPoly m (Real.log N - Real.log 2) - depthTail m N := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ N = r ^ 2 :=
    ⟨Real.sqrt N, Real.sqrt_pos.2 hN, (Real.sq_sqrt hN.le).symm⟩
  have hrr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  set X := Real.log (r ^ 2) - Real.log 2 with hX
  set W : ℝ → ℝ := fun x => Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (X - Real.log x) ^ m with hW
  have hint : IntegrableOn W (Ioi 0) := integrableOn_wt_sub_log_pow X m
  have hsplit : ∫ x in Ioi (0 : ℝ), W x =
      (∫ x in Ioo (0 : ℝ) (r ^ 2 / 2), W x) + ∫ x in Ioi (r ^ 2 / 2), W x := by
    rw [← Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ r ^ 2 / 2),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint.mono_set (Ioc_subset_Ioi_self)) (hint.mono_set (Ioi_subset_Ioi (by positivity))),
      integral_Ioc_eq_integral_Ioo]
  have hfull : ∫ x in Ioi (0 : ℝ), W x = depthPoly m X := integral_wt_sub_log_pow X m
  have hsub := integral_Ioo_half_eq m hr
  unfold depthInt depthTail
  rw [hrr, integral_Ioc_eq_integral_Ioo]
  have hfac : (0 : ℝ) < m.factorial := by positivity
  have e1 : ∫ t in Ioo (0 : ℝ) 1, Real.exp (-r ^ 2 * t ^ 2 / 2) * (2 ^ m / m.factorial) *
      Real.log (1 / t) ^ m = (1 / m.factorial) * ∫ t in Ioo (0 : ℝ) 1,
        Real.exp (-r ^ 2 * t ^ 2 / 2) * (2 ^ m * Real.log (1 / t) ^ m) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    ring
  rw [e1]
  have e2 : ∫ t in Ioo (0 : ℝ) 1, Real.exp (-r ^ 2 * t ^ 2 / 2) * (2 ^ m * Real.log (1 / t) ^ m) =
      (∫ x in Ioo (0 : ℝ) (r ^ 2 / 2), W x) / (Real.sqrt 2 * r) := by
    rw [hsub, mul_div_cancel_left₀ _ (by positivity)]
  rw [e2, show (∫ x in Ioo (0 : ℝ) (r ^ 2 / 2), W x) =
      depthPoly m X - ∫ x in Ioi (r ^ 2 / 2), W x by linarith [hsplit, hfull]]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination (-(depthPoly m X - ∫ x in Ioi (r ^ 2 / 2), W x)) * hs2

/-! ### The tail bound -/

/-- `∫_{c}^∞ e^{−x} (x − c)^m dx = m! e^{−c}`. -/
theorem integral_Ioi_exp_sub_pow (m : ℕ) (c : ℝ) :
    ∫ x in Ioi c, Real.exp (-x) * (x - c) ^ m = m.factorial * Real.exp (-c) := by
  rw [integral_Ioi_comp_add_right]
  simp only [add_sub_cancel_right]
  have hpt : ∀ x : ℝ, Real.exp (-(x + c)) * x ^ m =
      Real.exp (-c) * (Real.exp (-x) * x ^ (((m : ℝ) + 1) - 1)) := fun x => by
    rw [show ((m : ℝ) + 1) - 1 = (m : ℝ) by ring, Real.rpow_natCast, neg_add, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← Real.Gamma_eq_integral (by positivity), Real.Gamma_nat_eq_factorial]
  ring

/-- The pointwise tail bound: for `x ≥ N/2`,
`|e^{−x} x^{−1/2} (log N − log 2 − log x)^m| ≤ (N/2)^{−1/2} (2/N)^m e^{−x} (x − N/2)^m`. -/
theorem tail_pointwise_bound (m : ℕ) {N x : ℝ} (hN : 0 < N) (hx : N / 2 < x) :
    |Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (Real.log N - Real.log 2 - Real.log x) ^ m| ≤
      (N / 2) ^ (-(1 / 2 : ℝ)) * (2 / N) ^ m * (Real.exp (-x) * (x - N / 2) ^ m) := by
  have hN2 : 0 < N / 2 := by positivity
  have hx0 : 0 < x := by linarith
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hx0 _),
    abs_pow]
  have hlog : |Real.log N - Real.log 2 - Real.log x| ≤ 2 / N * (x - N / 2) := by
    have h1 : Real.log N - Real.log 2 - Real.log x = -Real.log (2 * x / N) := by
      rw [Real.log_div (by positivity) hN.ne', Real.log_mul two_ne_zero hx0.ne']
      ring
    have h2 : 0 ≤ Real.log (2 * x / N) :=
      Real.log_nonneg (by rw [le_div_iff₀ hN]; linarith)
    rw [h1, abs_neg, abs_of_nonneg h2]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * x / N)
    calc Real.log (2 * x / N) ≤ 2 * x / N - 1 := this
      _ = 2 / N * (x - N / 2) := by field_simp
  have hrp : x ^ (-(1 / 2 : ℝ)) ≤ (N / 2) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hN2 hx.le (by norm_num)
  calc Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * |Real.log N - Real.log 2 - Real.log x| ^ m
      ≤ Real.exp (-x) * (N / 2) ^ (-(1 / 2 : ℝ)) * (2 / N * (x - N / 2)) ^ m := by
        gcongr
    _ = (N / 2) ^ (-(1 / 2 : ℝ)) * (2 / N) ^ m * (Real.exp (-x) * (x - N / 2) ^ m) := by
        rw [mul_pow]
        ring

/-- ★★ **The tail is exponentially small**: `|R_m(N)| ≤ (2/N)^{m+1} e^{−N/2}`. -/
theorem depthTail_abs_le (m : ℕ) {N : ℝ} (hN : 0 < N) :
    |depthTail m N| ≤ (2 / N) ^ (m + 1) * Real.exp (-N / 2) := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ N = r ^ 2 :=
    ⟨Real.sqrt N, Real.sqrt_pos.2 hN, (Real.sq_sqrt hN.le).symm⟩
  have hrr : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  have hfac : (0 : ℝ) < m.factorial := by positivity
  unfold depthTail
  rw [hrr, abs_mul, abs_of_pos (by positivity)]
  have hpow : (r ^ 2 / 2) ^ (-(1 / 2 : ℝ)) = Real.sqrt 2 / r := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show r ^ 2 / 2 = (r / Real.sqrt 2) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)],
      Real.sqrt_sq (by positivity), inv_div]
  have hg0 : IntegrableOn (fun x : ℝ => Real.exp (-x) * (x - r ^ 2 / 2) ^ m) (Ioi (r ^ 2 / 2)) := by
    have h := (integrableOn_rpow_mul_exp_neg_rpow (s := m) (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith) one_pos)
    have h' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ m) (Ioi 0) := by
      refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only
      rw [Real.rpow_one, Real.rpow_natCast]
      ring
    refine (h'.mono_set (Ioi_subset_Ioi (by positivity))).mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx' : r ^ 2 / 2 < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have : 0 ≤ x - r ^ 2 / 2 := by linarith
      positivity)]
    gcongr
    linarith [show 0 < r ^ 2 / 2 by positivity]
  have hg : Integrable (fun x : ℝ => (r ^ 2 / 2) ^ (-(1 / 2 : ℝ)) * (2 / r ^ 2) ^ m *
      (Real.exp (-x) * (x - r ^ 2 / 2) ^ m)) (volume.restrict (Ioi (r ^ 2 / 2))) :=
    hg0.const_mul _
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioi (r ^ 2 / 2))),
      ‖Real.exp (-x) * x ^ (-(1 / 2 : ℝ)) * (Real.log (r ^ 2) - Real.log 2 - Real.log x) ^ m‖ ≤
        (r ^ 2 / 2) ^ (-(1 / 2 : ℝ)) * (2 / r ^ 2) ^ m * (Real.exp (-x) * (x - r ^ 2 / 2) ^ m) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun x hx => tail_pointwise_bound m (by positivity) hx
  have hle := norm_integral_le_of_norm_le hg hbound
  rw [Real.norm_eq_abs] at hle
  calc Real.sqrt 2 / (m.factorial * r) * |∫ x in Ioi (r ^ 2 / 2), Real.exp (-x) *
        x ^ (-(1 / 2 : ℝ)) * (Real.log (r ^ 2) - Real.log 2 - Real.log x) ^ m|
      ≤ Real.sqrt 2 / (m.factorial * r) * ∫ x in Ioi (r ^ 2 / 2),
          (r ^ 2 / 2) ^ (-(1 / 2 : ℝ)) * (2 / r ^ 2) ^ m *
            (Real.exp (-x) * (x - r ^ 2 / 2) ^ m) := by gcongr
    _ = (2 / r ^ 2) ^ (m + 1) * Real.exp (-r ^ 2 / 2) := by
        rw [integral_const_mul, integral_Ioi_exp_sub_pow, hpow, pow_succ]
        have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hkey : Real.sqrt 2 / (m.factorial * r) * (Real.sqrt 2 / r * (m.factorial : ℝ)) =
            2 / r ^ 2 := by
          field_simp
          linear_combination hs2
        calc Real.sqrt 2 / (m.factorial * r) * (Real.sqrt 2 / r * (2 / r ^ 2) ^ m *
              ((m.factorial : ℝ) * Real.exp (-(r ^ 2 / 2))))
            = (Real.sqrt 2 / (m.factorial * r) * (Real.sqrt 2 / r * (m.factorial : ℝ))) *
                ((2 / r ^ 2) ^ m * Real.exp (-(r ^ 2 / 2))) := by ring
          _ = (2 / r ^ 2) ^ m * (2 / r ^ 2) * Real.exp (-r ^ 2 / 2) := by
              rw [hkey, neg_div]
              ring

/-! ### The asymptotic form and the depth-two regression -/

/-- ★★ The asymptotic form: `D_m(N) − √2/(m!√N) P_m(log N − log 2) = O(e^{−N/2})`. -/
theorem depthInt_sub_isBigO (m : ℕ) :
    (fun N : ℝ => depthInt m N - Real.sqrt 2 / (m.factorial * Real.sqrt N) *
      depthPoly m (Real.log N - Real.log 2)) =O[atTop] fun N => Real.exp (-N / 2) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  rw [depth_flat_allOrders m hN0, Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
    abs_of_pos (Real.exp_pos _)]
  have h1 : (2 / N) ^ (m + 1) ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one₀ hN0).2 hN)
  calc |Real.sqrt 2 / (m.factorial * Real.sqrt N) * depthPoly m (Real.log N - Real.log 2) -
          depthTail m N -
        Real.sqrt 2 / (m.factorial * Real.sqrt N) * depthPoly m (Real.log N - Real.log 2)|
        = |depthTail m N| := by rw [sub_sub_cancel_left, abs_neg]
    _ ≤ (2 / N) ^ (m + 1) * Real.exp (-N / 2) := depthTail_abs_le m hN0
    _ ≤ 1 * Real.exp (-N / 2) := by gcongr
    _ = Real.exp (-N / 2) := one_mul _

/-- `H_0 = Γ(½) = √π`. -/
theorem gammaLogMoment_zero : gammaLogMoment 0 = Real.sqrt Real.pi := by
  unfold gammaLogMoment
  rw [← Real.Gamma_one_half_eq, Real.Gamma_eq_integral (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, pow_zero, mul_one]

/-- `H_1 = Γ'(½) = −√π(γ + 2 log 2)`. -/
theorem gammaLogMoment_one :
    gammaLogMoment 1 = -Real.sqrt Real.pi * (Real.eulerMascheroniConstant + 2 * Real.log 2) := by
  unfold gammaLogMoment
  rw [← integral_rpow_log_exp_half]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- `P_1(X) = √π (X + γ + 2 log 2)`. -/
theorem depthPoly_one (X : ℝ) :
    depthPoly 1 X = Real.sqrt Real.pi * (X + Real.eulerMascheroniConstant + 2 * Real.log 2) := by
  simp [depthPoly, Finset.sum_range_succ, gammaLogMoment_zero, gammaLogMoment_one]
  ring

/-- ★★ **Depth-two regression**: at `m = 1` the general formula is the expansion of
`crossing_flat_allOrders`, `D_1(N) = √(2π)/√N (log N + γ + log 2) − R_1(N)`. -/
theorem depthInt_one {N : ℝ} (hN : 0 < N) :
    depthInt 1 N = Real.sqrt (2 * Real.pi) / Real.sqrt N *
      (Real.log N + Real.eulerMascheroniConstant + Real.log 2) - depthTail 1 N := by
  rw [depth_flat_allOrders 1 hN, depthPoly_one, Real.sqrt_mul (by norm_num)]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul]
  have : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  field_simp
  ring

end Grammar
