You are Astra, design consultant for the Lean 4 formalisation (repo timaeus-research/grammar, namespace Grammar, main 9a7eea6, 958 modules, zero sorry/axiom) accompanying the examples note `examples_slop.tex` of the grammar paper (Gerraty–Murfet, "Expectations and the Exceptional Divisor"). Your round-8 targets ALL landed, including the stretch target: (1) DCXXI the monomial renormalised constant `(log 2 − γ)/k`; the fidelity bridge DCXXII (invariant tangent projection, `‖P_{x,y}Ξ‖² = crossNormSq(UᵀΞV)`); (2) DCXXIII the depth-three second coefficient with bounded residual (`|Z_3 − [(log N)² + 4(2 log 2 − γ) log N]/(4π√N)| ≤ 12/√N`; numerics: `√N·residual → 0.9938`, the Mellin-predicted constant `((4 log 2 − 2γ)² + π²)/(4π)` to four digits); (3) DCXXIV the all-depth leading asymptotic by the propagation step `gaussianStep_bound` and induction (`|Z_{m+2}(N) − (log N)^{m+1}/((m+1)!√(2π)^{m+1}√N)| ≤ C_m(1 + log N)^m/√N`, and the limit). This is round 9.

## HEADLINES rows DCXXI–DCXXIV
| **DCXXI** | ★★ **THE MONOMIAL RENORMALISED CONSTANT `∫₀^∞ (e^{−u^{2k}/2} − 1_{(0,1]})·2/u = (log 2 − γ)/k` (u955; examples_slop §4, the family `K = x²(x^{2k−2}+y²)/2`; Astra round-8 target 1)**: `monoAmp k u = e^{−u^{2k}/2}`; `integral_renormalised_sq_cut` (DCXII's `−γ` with the indicator cut at `b ∈ (0,1]`: `−γ − 2 log b`); `ampRenorm_monoAmp_one` (`k = 1`: `log 2 − γ`, by `u = √2 w`); ★★ `ampRenorm_monoAmp` (`v = u^k` via `integral_comp_rpow_Ioi_of_pos`, reducing to `k = 1`); `monoAmp_ampData` (`A = ½`, tail `e^{−u^{2k}/2} ≤ e^{−u/2}`); `monomial_renorm_constant` (the split form without indicators, the consult's interface). With the amplitude engine this is the constant term of the two-term expansion of every model in the family (`k = 2` is DCXV; the family theorem with the `x`-Gaussian scaling is a follow-up). Lean gotchas: `mul_left_cancel₀ (inv_ne_zero …)` to extract an integral from `c⁻¹ * X = c⁻¹ * ∫ g`; `pow_le_pow_of_le_one`, `pow_le_pow_right₀`, `one_lt_pow₀ h hk.ne'`. | MonomialRenormalised.lean |
| **DCXXII** | ★★★ **RANK-ONE: THE INVARIANT TANGENT PROJECTION `P_{x,y}(B) = P_xB + BP_y − P_xBP_y` (u956; examples_slop §5; Astra round-8 fidelity bridge)**: `projMat x = xxᵀ/‖x‖²`, `tanProj x y B`; `sum_sq_mulVec` (`‖Ua‖² = ‖a‖²` for `UᵀU = 1`, by `dotProduct_mulVec` + `mulVec_transpose`), `projMat_mulVec` (`P_{Ua} = U P_a Uᵀ`), `tanProj_conj` (`P_{Ua,Vb}(UBVᵀ) = U P_{a,b}(B) Vᵀ`), `projMat_axisVec` (`P_{αe₀} = E₀₀`), `tanProj_axis` (at the aligned point the tangent projection IS the cross restriction), ★★ `tanProj_conj_axis` (`P_{x,y}(Ξ) = U·cross(UᵀΞV)·Vᵀ` at `x = U(αe₀)`, `y = V(βe₀)`, `α,β ≠ 0`, using `mul_eq_one_comm` for `UUᵀ = 1`), ★★★ `frobSq_tanProj_eq_crossNormSq : ‖P_{x,y}Ξ‖²_F = crossNormSq(UᵀΞV)`: the tilt of DCXX's `integral_rankOne_normal_tilt_general` is `e^{‖P_{x,y}Ξ‖²/2}` in coordinate-free form. Lean gotchas: the generic `mul_eq_one_comm` (Dedekind-finite monoids) replaces the old `Matrix.mul_eq_one_comm`; rewrite the longest product identity first (`rw [h3, h1, h2]`) since later rewrites destroy the earlier patterns; `simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]` normalises both sides. | RankOneProjection.lean |
| **DCXXIII** | ★★★ **THE DEPTH-THREE GAUSSIAN DLN: THE SECOND LOGARITHMIC COEFFICIENT `(2 log 2 − γ)/π` (u957; examples_slop §2 eq. dln_gauss at `L = 3`; Astra round-8 target 2)**: `gaussH x = e^{−x²/2} − 1_{(0,1]}(x)` with `integral_gaussH_div : R₀ = ∫₀^∞ h/x = (log 2 − γ)/2` (from DCXXI at `k = 1`), `integrableOn_gaussH_div`, the cutoff piece `abs_integral_gaussH_div_Ioc_le` (`|∫₀^a h/x| ≤ a²/2`), the logarithmic piece `abs_integral_gaussH_log_le` (`|∫_a^∞ h log x/x| ≤ 3`, with `integrableOn_gaussH_log`); `log_le_two_sqrt`; the refined remainder `depthThree_rem_pointwise`/`depthThree_rem_le` (`∫_{N^{−1/2}}^∞ |F − gL| ≤ 1/(π√N)`, keeping `log(2Nx²)` and using `log y ≤ 2√y`, `∫_a^∞ x^{−3}`, `∫_a^∞ x^{−2}` by `integral_Ioi_rpow_of_lt`); the main term with the Gaussian kept on the whole outer region: `depthThree_gL_eq` (`gL = (1/(2π√N))(1_{(a,1]}P + (log N + c) h/x + 2 h log x/x)`), `integral_depthThreeP`, ★★ `integral_depthThree_main` (`∫_a^∞ gL = (1/(2π√N))((log N)²/4 + (c/2)log N + (log N + c)(R₀ − I_a) + 2J_a)`); ★★★ `gaussLaplaceL_three_two_term_bound : |Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π√N)| ≤ 12/√N` for `N ≥ 1` (the coefficient is `c/2 + R₀ = (3 log 2 − γ)/2 + (log 2 − γ)/2 = 2 log 2 − γ`); ★★★ `gaussLaplaceL_three_two_term` (`O(N^{−1/2})`). The constant term `((4 log 2 − 2γ)² + π²)/(4π)` stays a derivation. Lean gotchas: `Integrable.add` witnesses must be typed single lambdas before `integral_add`; `clear` the `set … with` equations of big integrals before `linarith` (whnf timeouts); `abs_sub a b` with explicit arguments; `← add_div` for `a/c + b/c`; `Ioc_disjoint_Ioi le_rfl`. | GaussianDepthThreeTwoTerm.lean |
| **DCXXIV** | ★★★ **THE GAUSSIAN DLN AT EVERY DEPTH: THE LEADING ASYMPTOTIC `(log N)^{L−1}/((L−1)!(2π)^{(L−1)/2}√N)` (u958; examples_slop §2 eq. dln_gauss, the leading coefficient at every depth; Astra round-8 target 3 — the stretch target, landed)**: `integral_pi_succ` (Bochner peel, first coordinate integrated FIRST), ★★ `gaussLaplaceL_succ_scalar : Z_{L+1}(N) = ∫ g(x) Z_L(N x²) dx` (`N ≥ 0`), `gaussLaplaceL_nonneg/zero_eq_one/le_one`, `integrable_density_mul_gaussLaplaceL` (Fubini on the pi space, no measurability of `Z_L` in `N` needed); the elementary estimates `intervalIntegrable_pow_log_div`/`integral_pow_log_div` (`∫_a^1 (b + 2 log x)^n/x = (b^{n+1} − (b + 2 log a)^{n+1})/(2(n+1))`), `mul_pow_one_add_log_le` (`x(1 + 2|log x|)^{n+1} ≤ (2n+3)^{n+1}` on `(0,1]`, from `|log x| ≤ (n+1)x^{−1/(n+1)}`), `pow_mul_exp_neg_half_sq_le` (`x^n e^{−x²/2} ≤ n! e² e^{−x/2}`); the hypothesis structure `LeadingData f A C m` (`0 ≤ f ≤ 1`, `|f(t) − A(log t)^{m+1}/√t| ≤ C(1+log t)^m/√t` for `t ≥ 1`); the three pieces `step_inner_le`, `step_middle_le` (main term by the FTC lemma at `b = log N` — `(log N + 2 log a)^{m+2} = 0` — plus the induction error and the Gaussian replacement `|g − 1/√(2π)| ≤ x²/(2√(2π))`), `step_tail_le` (Gaussian moments via `x^m e^{−x²/2} ≤ m! e² e^{−x/2}`); ★★ `gaussianStep_bound` (`A' = A/((m+2)√(2π))`, `C' = 1 + (C + A(2m+3)^{m+1})/2 + 16(A+C)3^{m+1}m!`); `gaussLaplaceL_two` (`Z_2 = gaussLaplace2`), `leadingData_two` (`A = 1/√(2π)`, `C = 5/2`); ★★★ `gaussLaplaceL_leading_bound : ∀ m, ∃ C, LeadingData Z_{m+2} (1/((m+1)!√(2π)^{m+1})) C m` (induction on the depth through the scalar recursion); ★★★ `gaussLaplaceL_leading : √N Z_{m+2}(N)/(log N)^{m+1} → 1/((m+1)!√(2π)^{m+1})`. The leading coefficient of eq. (dln_gauss) is a theorem at EVERY depth; the lower coefficients for `L ≥ 4` stay derivations. Lean gotchas: `ring` does not distribute `(uvw)^{m+1}` with symbolic `m` — `rw [mul_pow, mul_pow]` first; `set K₂ := 8·…` does not fold `16·…` — rewrite `16·… = 2 K₂` explicitly; a mechanical line-wrap must not split `--` comment lines containing backticks. | GaussianDepthAllLeading.lean |

## Public statements of the four new files (verbatim signatures)
### Grammar/MonomialRenormalised.lean
```lean
/-- The monomial amplitude `e^{−u^{2k}/2}`. -/
noncomputable def monoAmp (k : ℕ) (u : ℝ) : ℝ

/-- `∫₀^∞ (e^{−w²} − 1_{(0,b]}(w))·2/w dw = −γ − 2 log b` for `0 < b ≤ 1`. -/
theorem integral_renormalised_sq_cut {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∫ w in Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 b).indicator 1 w) * (2 / w) =
      -Real.eulerMascheroniConstant - 2 * Real.log b := by
  have e : ∀ w ∈ Ioi (0 : ℝ), (Real.exp (-w ^ 2) - (Ioc 0 b).indicator 1 w) * (2 / w) =
      (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w) +
        (Ioc b 1).indicator (fun w => 2 / w) w := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    by_cases h1 : w ≤ b
    · have hm1 : w ∈ Ioc (0 : ℝ) b := ⟨hw0, h1⟩
      have hm2 : w ∈ Ioc (0 : ℝ) 1 := ⟨hw0, by linarith⟩
      have hm3 : w ∉ Ioc b 1 := fun h => absurd h.1 (not_lt.2 h1)
      rw [indicator_of_mem hm1, indicator_of_mem hm2, indicator_of_notMem hm3, add_zero]
    · have h1' := not_le.1 h1
      have hm1 : w ∉ Ioc (0 : ℝ) b := fun h => absurd h.2 (not_le.2 h1')
      rw [indicator_of_notMem hm1]
      by_cases h2 : w ≤ 1
      · have hm2 : w ∈ Ioc (0 : ℝ) 1 := ⟨hw0, h2⟩
        have hm3 : w ∈ Ioc b 1 := ⟨h1', h2⟩
        rw [indicator_of_mem hm2, indicator_of_mem hm3, Pi.one_apply, sub_zero]
        ring
      · have h2' := not_le.1 h2
        have hm2 : w ∉ Ioc (0 : ℝ) 1 := fun h => absurd h.2 (not_le.2 h2')
        have hm3 : w ∉ Ioc b 1 := fun h => absurd h.2 (not_le.2 h2')
        rw [indicator_of_notMem hm2, indicator_of_notMem hm3, add_zero]
  have hint : IntegrableOn (fun w : ℝ => (Real.exp (-w ^ 2) - (Ioc 0 1).indicator 1 w) * (2 / w))
      (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact integrableOn_renorm_inner.union integrableOn_renorm_outer
  have hind : IntegrableOn ((Ioc b 1).indicator fun w : ℝ => 2 / w) (Ioi 0) := by
    have : IntegrableOn (fun w : ℝ => 2 / w) (Ioc b 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb1]
      refine ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id fun x hx => ?_)
      rw [uIcc_of_le hb1] at hx
      exact ne_of_gt (lt_of_lt_of_le hb0 hx.1)
    exact (this.integrable_indicator measurableSet_Ioc).integrableOn
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add hint hind, integral_renormalised_sq,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc b 1 = Ioc b 1 from
      inter_eq_right.2 fun w hw => show (0 : ℝ) < w by linarith [hw.1],
    ← intervalIntegral.integral_of_le hb1]
  have : ∫ w in b..1, 2 / w = 2 * ∫ w in b..1, w⁻¹

/-- The case `k = 1`: `∫₀^∞ (e^{−u²/2} − 1_{(0,1]}(u))·2/u du = log 2 − γ` (rescale `u = √2 w`). -/
theorem ampRenorm_monoAmp_one :
    ampRenorm (monoAmp 1) = Real.log 2 - Real.eulerMascheroniConstant := by
  unfold ampRenorm monoAmp
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set g : ℝ → ℝ := fun u => (Real.exp (-u ^ (2 * 1) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u)
    with hg
  have h := integral_comp_mul_left_Ioi g 0 (b := Real.sqrt 2) hs
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ w ∈ Ioi (0 : ℝ), g (Real.sqrt 2 * w) = (Real.sqrt 2)⁻¹ *
      ((Real.exp (-w ^ 2) - (Ioc 0 (1 / Real.sqrt 2)).indicator 1 w) * (2 / w)) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (Real.sqrt 2 * w) =
        (Ioc 0 (1 / Real.sqrt 2)).indicator 1 w := by
      by_cases hle : w ≤ 1 / Real.sqrt 2
      · have hm : Real.sqrt 2 * w ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by
          rw [le_div_iff₀ hs] at hle; linarith⟩
        have hm' : w ∈ Ioc (0 : ℝ) (1 / Real.sqrt 2) := ⟨hw0, hle⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have hle' := not_le.1 hle
        have hm : Real.sqrt 2 * w ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 (by
          rw [div_lt_iff₀ hs] at hle'; linarith))
        have hm' : w ∉ Ioc (0 : ℝ) (1 / Real.sqrt 2) := fun hm => absurd hm.2 (not_le.2 hle')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg]
    rw [hI, show -(Real.sqrt 2 * w) ^ (2 * 1) / 2 = -w ^ 2 by rw [mul_pow, mul_one, hs2]; ring]
    field_simp
  have hb1 : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one hs]; exact Real.one_le_sqrt.2 (by norm_num)
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    integral_renormalised_sq_cut (by positivity) hb1] at h
  have hlog : Real.log (1 / Real.sqrt 2) = -(Real.log 2 / 2) := by
    rw [one_div, Real.log_inv, Real.log_sqrt (by norm_num)]
  rw [hlog] at h
  have hX

/-- ★★ **The monomial renormalised constant**:
`∫₀^∞ (e^{−u^{2k}/2} − 1_{(0,1]}(u))·2/u du = (log 2 − γ)/k` for `k ≥ 1`. -/
theorem ampRenorm_monoAmp {k : ℕ} (hk : 0 < k) :
    ampRenorm (monoAmp k) = (Real.log 2 - Real.eulerMascheroniConstant) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold ampRenorm monoAmp
  set g : ℝ → ℝ := fun v => (Real.exp (-v ^ 2 / 2) - (Ioc 0 1).indicator 1 v) * (2 / v) with hg
  have h := integral_comp_rpow_Ioi_of_pos (g := fun v => g v / k) (p := (k : ℝ)) hk'
  have e : ∀ u ∈ Ioi (0 : ℝ), ((k : ℝ) * u ^ ((k : ℝ) - 1)) • (g (u ^ (k : ℝ)) / k) =
      (Real.exp (-u ^ (2 * k) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have hI : (Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) (u ^ k) = (Ioc 0 1).indicator 1 u := by
      by_cases hle : u ≤ 1
      · have hm : u ^ k ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, pow_le_one₀ hu0.le hle⟩
        have hm' : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, hle⟩
        rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply, Pi.one_apply]
      · have hle' := not_le.1 hle
        have hm : u ^ k ∉ Ioc (0 : ℝ) 1 := fun hm =>
          absurd hm.2 (not_le.2 (one_lt_pow₀ hle' hk.ne'))
        have hm' : u ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.2 hle')
        rw [indicator_of_notMem hm, indicator_of_notMem hm']
    simp only [hg, smul_eq_mul]
    rw [Real.rpow_natCast, Real.rpow_sub hu0, Real.rpow_natCast, Real.rpow_one, hI,
      show (u ^ k) ^ 2 = u ^ (2 * k) by ring]
    field_simp
  rw [← setIntegral_congr_fun measurableSet_Ioi e, h, integral_div]
  have h1

/-- The amplitude data of `e^{−u^{2k}/2}`, `k ≥ 1`: `A = 1/2`. -/
theorem monoAmp_ampData {k : ℕ} (hk : 0 < k) : AmpData (monoAmp k) (1 / 2) where
  meas := by unfold monoAmp; fun_prop
  nonneg u := by unfold monoAmp; positivity
  le_one u := by
    unfold monoAmp
    exact Real.exp_le_one_iff.2 (by
      have : 0 ≤ u ^ (2 * k) := by rw [pow_mul]; positivity
      linarith)
  A_nonneg := by norm_num
  near u hu := by
    unfold monoAmp
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hpow : u ^ (2 * k) ≤ u ^ 2 := by
      rw [pow_mul]
      calc (u ^ 2) ^ k ≤ (u ^ 2) ^ 1 := pow_le_pow_of_le_one (by positivity) hu2 hk
        _ = u ^ 2 := pow_one _
    have := Real.add_one_le_exp (-u ^ (2 * k) / 2)
    linarith
  tail u hu := by
    unfold monoAmp
    have h1 : u ≤ u ^ (2 * k) := by
      calc u = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ (2 * k)

/-- The split form: `2(∫₀¹ (e^{−u^{2k}/2} − 1)/u + ∫₁^∞ e^{−u^{2k}/2}/u) = (log 2 − γ)/k`. -/
theorem monomial_renorm_constant {k : ℕ} (hk : 0 < k) :
    2 * ((∫ u in Ioc (0 : ℝ) 1, (Real.exp (-u ^ (2 * k) / 2) - 1) / u) +
      ∫ u in Ioi (1 : ℝ), Real.exp (-u ^ (2 * k) / 2) / u) =
      (Real.log 2 - Real.eulerMascheroniConstant) / k := by
  have h
```
### Grammar/RankOneProjection.lean
```lean
/-- The rank-one projection `x xᵀ/‖x‖²`. -/
noncomputable def projMat {m : ℕ} (x : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ

/-- The tangent projection `P_{x,y}(B) = P_x B + B P_y − P_x B P_y`. -/
noncomputable def tanProj (x : Fin (M + 1) → ℝ) (y : Fin (N + 1) → ℝ)
    (B : Fin (M + 1) → Fin (N + 1) → ℝ) : Fin (M + 1) → Fin (N + 1) → ℝ

/-- `‖Ua‖² = ‖a‖²` for `UᵀU = 1`. -/
theorem sum_sq_mulVec {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ} (hU : Uᵀ * U = 1)
    (a : Fin m → ℝ) : ∑ i, (U.mulVec a) i ^ 2 = ∑ k, a k ^ 2 := by
  have h : ∑ i, (U.mulVec a) i ^ 2 = dotProduct (U.mulVec a) (U.mulVec a)

/-- `P_{Ua} = U P_a Uᵀ` for `UᵀU = 1`. -/
theorem projMat_mulVec {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ} (hU : Uᵀ * U = 1)
    (a : Fin m → ℝ) : projMat (U.mulVec a) = U * projMat a * Uᵀ

/-- `P_{Ua,Vb}(U B Vᵀ) = U P_{a,b}(B) Vᵀ` for orthogonal `U, V`. -/
theorem tanProj_conj {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (a : Fin (M + 1) → ℝ) (b : Fin (N + 1) → ℝ) (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (U.mulVec a) (V.mulVec b) (conjMat U V B) = conjMat U V (tanProj a b B) := by
  funext i j
  simp only [tanProj, conjMat, of_conjMat, projMat_mulVec hU, projMat_mulVec hV]
  have e : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) +
      U * Matrix.of B * Vᵀ * (V * projMat b * Vᵀ) -
      U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) * (V * projMat b * Vᵀ) =
      U * (projMat a * Matrix.of B + Matrix.of B * projMat b -
        projMat a * Matrix.of B * projMat b) * Vᵀ := by
    have h1 : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) = U * (projMat a * Matrix.of B) * Vᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    have h2 : U * Matrix.of B * Vᵀ * (V * projMat b * Vᵀ) = U * (Matrix.of B * projMat b) * Vᵀ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V, hV, Matrix.one_mul]
    have h3 : U * projMat a * Uᵀ * (U * Matrix.of B * Vᵀ) * (V * projMat b * Vᵀ) =
        U * (projMat a * Matrix.of B * projMat b) * Vᵀ

/-- `P_{αe₀} = E₀₀` for `α ≠ 0`. -/
theorem projMat_axisVec {α : ℝ} (hα : α ≠ 0) :
    projMat (axisVec (M := M) α) = Matrix.of fun i j => if i = 0 ∧ j = 0 then (1 : ℝ) else 0 := by
  ext i j
  have hsum : ∑ k, axisVec (M := M) α k ^ 2 = α ^ 2

/-- At the aligned point the tangent projection is the cross restriction. -/
theorem tanProj_axis {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (B : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (axisVec α) (axisVec β) B = cross B

/-- ★★ `P_{x,y}(Ξ) = U · cross(UᵀΞV) · Vᵀ` at `x = U(αe₀)`, `y = V(βe₀)`. -/
theorem tanProj_conj_axis {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    tanProj (U.mulVec (axisVec α)) (V.mulVec (axisVec β)) Ξ =
      conjMat U V (cross (conjMat Uᵀ Vᵀ Ξ)) := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.1 hU
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.1 hV
  have hΞ : Ξ = conjMat U V (conjMat Uᵀ Vᵀ Ξ)

/-- ★★★ **The invariant tilt norm**: `‖P_{x,y}Ξ‖²_F = crossNormSq(UᵀΞV)` at `x = U(αe₀)`,
`y = V(βe₀)`, `α, β ≠ 0`. -/
theorem frobSq_tanProj_eq_crossNormSq {U : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ}
    {V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (Ξ : Fin (M + 1) → Fin (N + 1) → ℝ) :
    frobSq (tanProj (U.mulVec (axisVec α)) (V.mulVec (axisVec β)) Ξ) =
      crossNormSq (conjMat Uᵀ Vᵀ Ξ)
```
### Grammar/GaussianDepthThreeTwoTerm.lean
```lean
/-- `h(x) = e^{−x²/2} − 1_{(0,1]}(x)`. -/
noncomputable def gaussH (x : ℝ) : ℝ

/-- `R₀ = ∫₀^∞ h(x)/x dx = (log 2 − γ)/2`. -/
theorem integral_gaussH_div :
    ∫ x in Ioi (0 : ℝ), gaussH x / x = (Real.log 2 - Real.eulerMascheroniConstant) / 2 := by
  have h := ampRenorm_monoAmp_one
  unfold ampRenorm monoAmp at h
  have e : ∀ u ∈ Ioi (0 : ℝ), (Real.exp (-u ^ (2 * 1) / 2) - (Ioc 0 1).indicator 1 u) * (2 / u) =
      2 * (gaussH u / u)

theorem measurable_gaussH : Measurable gaussH

theorem gaussH_inner {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    -(x ^ 2 / 2) ≤ gaussH x ∧ gaussH x ≤ 0

theorem gaussH_outer {x : ℝ} (hx : 1 < x) :
    0 ≤ gaussH x ∧ gaussH x ≤ Real.exp (-x / 2)

/-- `∫₀^∞ h/x` is integrable on `(0, ∞)`. -/
theorem integrableOn_gaussH_div : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi 0) := by
  have h1 := integrableOn_ampRenorm_inner (monoAmp_ampData one_pos)
  have h2 := integrableOn_ampRenorm_outer (monoAmp_ampData one_pos)
  have e : ∀ x : ℝ, gaussH x / x = 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)) := by
    intro x; unfold gaussH monoAmp; ring
  simp_rw [e]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  have h1' : IntegrableOn (fun x : ℝ => 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)))
      (Ioc 0 1) := h1.const_mul _
  have h2' : IntegrableOn (fun x : ℝ => 1 / 2 * ((monoAmp 1 x - (Ioc 0 1).indicator 1 x) * (2 / x)))
      (Ioi 1)

/-- The cutoff piece `|∫₀^a h/x| ≤ a²/2` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_div_Ioc_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioc (0 : ℝ) a, gaussH x / x| ≤ a ^ 2 / 2 := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussH x / x) (C := a / 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x hx => by
      have hx0 : 0 < x := hx.1
      obtain ⟨h1, h2⟩ := gaussH_inner ⟨hx0, hx.2.trans ha1⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_of_nonpos h2, div_le_iff₀ hx0]
      nlinarith [hx.2])
  have hv : volume.real (Ioc (0 : ℝ) a) = a

theorem measurable_gaussH_log : Measurable fun x : ℝ => gaussH x * Real.log x / x

/-- On `(0, 1]`, `|h(x) log x/x| ≤ 1/2`. -/
theorem norm_gaussH_log_inner {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖gaussH x * Real.log x / x‖ ≤ 1 / 2 := by
  have hx0 : 0 < x := hx.1
  obtain ⟨h1, h2⟩ := gaussH_inner hx
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx.2
  have hxlog : -(x * Real.log x) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hx0)
    rw [Real.log_inv] at this
    have h

/-- On `(1, ∞)`, `|h(x) log x/x| ≤ e^{−x/2}`. -/
theorem norm_gaussH_log_outer {x : ℝ} (hx : 1 < x) :
    ‖gaussH x * Real.log x / x‖ ≤ Real.exp (-x / 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨h1, h2⟩ := gaussH_outer hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hlx : Real.log x ≤ x

theorem integrableOn_exp_neg_half_Ioi_one :
    IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Ioi 1) := by
  refine IntegrableOn.congr_fun (s

theorem integrableOn_gaussH_log_Ioc {a : ℝ} (ha0 : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioc a 1) := by
  refine Measure.integrableOn_of_bounded (M

theorem integrableOn_gaussH_log_Ioi_one :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioi 1)

theorem integrableOn_gaussH_log {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IntegrableOn (fun x : ℝ => gaussH x * Real.log x / x) (Ioi a)

/-- The logarithmic piece `|∫_a^∞ h(x) log x/x dx| ≤ 3` for `0 ≤ a ≤ 1`. -/
theorem abs_integral_gaussH_log_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |∫ x in Ioi a, gaussH x * Real.log x / x| ≤ 3 := by
  have hbound_in : |∫ x in Ioc a 1, gaussH x * Real.log x / x| ≤ 1 / 2 := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a 1)
      (f := fun x => gaussH x * Real.log x / x) (C := 1 / 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun x hx => norm_gaussH_log_inner ⟨lt_of_le_of_lt ha0 hx.1, hx.2⟩)
    have hv : volume.real (Ioc a 1) = 1 - a := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [Real.norm_eq_abs, hv] at h
    nlinarith
  have hbound_out : |∫ x in Ioi 1, gaussH x * Real.log x / x| ≤ 2 := by
    have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
      (f := fun x => gaussH x * Real.log x / x) integrableOn_exp_neg_half_Ioi_one (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Eventually.of_forall fun x hx => norm_gaussH_log_outer hx)
    rw [Real.norm_eq_abs, integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)] at h
    have := Real.exp_le_one_iff.2 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    nlinarith [Real.exp_pos (-1 / 2)]
  rw [← Ioc_union_Ioi_eq_Ioi ha1, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (integrableOn_gaussH_log_Ioc ha0) integrableOn_gaussH_log_Ioi_one]
  calc |(∫ x in Ioc a 1, gaussH x * Real.log x / x) + ∫ x in Ioi 1, gaussH x * Real.log x / x|
      ≤ |∫ x in Ioc a 1, gaussH x * Real.log x / x| + |∫ x in Ioi 1, gaussH x * Real.log x / x| :=
        abs_add_le _ _
    _ ≤ 1 / 2 + 2 := add_le_add hbound_in hbound_out
    _ ≤ 3

/-- `log y ≤ 2√y` for `y > 0`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h

/-- The pointwise bound `|F(x) − g(x)L(x)| ≤ x^{−3}/(πN^{3/2}) + x^{−2}/(2πN)` for `x ≥ N^{−1/2}`,
where `L(x) = (log N + 2 log x + c)/(√(2π)√N x)`. -/
theorem depthThree_rem_pointwise {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N ≤ x) :
    |depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))| ≤
      1 / (Real.pi * (N * Real.sqrt N)) * x ^ (-3 : ℝ) + 1 / (2 * Real.pi * N) * x ^ (-2 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hNx : 1 ≤ N * x ^ 2 := by
    have h2 : 1 / Real.sqrt N * Real.sqrt N = 1 := by field_simp
    have h3 : (1 / Real.sqrt N) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
    have h4 : (1 / Real.sqrt N) ^ 2 * N = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt hN0.le]; field_simp
    nlinarith
  obtain ⟨hb, -⟩ := gaussLaplace2_bounds hNx
  have hsqrt : Real.sqrt (N * x ^ 2) = Real.sqrt N * x := by
    rw [Real.sqrt_mul hN0.le, Real.sqrt_sq hx0.le]
  have hlog : Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x := by
    rw [Real.log_mul hN0.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [hsqrt, hlog] at hb
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  -- the numerator of the remainder: `log(2Nx²) + 3 ≤ 4 + 2√N x`
  have hnum : Real.log (2 * (N * x ^ 2)) + 3 ≤ 4 + 2 * (Real.sqrt N * x) := by
    have h1 : Real.log (2 * (N * x ^ 2)) = Real.log 2 + Real.log (N * x ^ 2) :=
      Real.log_mul two_ne_zero (by positivity)
    have h2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 := log_le_two_sqrt (by positivity : 0 < N * x ^ 2)
    rw [hsqrt] at h3
    linarith
  have hnum0 : 0 ≤ Real.log (2 * (N * x ^ 2)) + 3 := by
    have : 0 ≤ Real.log (2 * (N * x ^ 2)) := Real.log_nonneg (by nlinarith)
    linarith
  have hg : gaussDensity x ≤ 1 / Real.sqrt (2 * Real.pi) := by
    unfold gaussDensity
    exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le
  have hg0 : 0 ≤ gaussDensity x := gaussDensity_nonneg x
  have hrpow3 : x ^ (-3 : ℝ) = 1 / x ^ 3 := by
    rw [Real.rpow_neg hx0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hrpow2 : x ^ (-2 : ℝ) = 1 / x ^ 2 := by
    rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [hrpow3, hrpow2]
  unfold depthThreeF
  rw [← mul_sub, abs_mul, abs_of_nonneg hg0]
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hb hs hsq hg ⊢
  have hpi : Real.pi = s * s / 2 := by linarith
  calc gaussDensity x * |gaussLaplace2 (N * x ^ 2) -
        (Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (s * (Real.sqrt N * x))|
      ≤ 1 / s *
          ((Real.log (2 * (N * x ^ 2)) + 3) / (2 * (N * x ^ 2) * (s * (Real.sqrt N * x)))) :=
        mul_le_mul hg hb (abs_nonneg _) (by positivity)
    _ ≤ 1 / s * ((4 + 2 * (Real.sqrt N * x)) / (2 * (N * x ^ 2) * (s * (Real.sqrt N * x)))) := by
        gcongr
    _ = 1 / (Real.pi * (N * Real.sqrt N)) * (1 / x ^ 3) + 1 / (2 * Real.pi * N) * (1 / x ^ 2)

/-- `∫_{N^{−1/2}}^∞ |F − gL| ≤ 1/(π√N)`. -/
theorem depthThree_rem_le {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))))| ≤ 1 / (Real.pi * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have h3 : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have h2 : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have hmaj : IntegrableOn (fun x : ℝ => 1 / (Real.pi * (N * Real.sqrt N)) * x ^ (-3 : ℝ) +
      1 / (2 * Real.pi * N) * x ^ (-2 : ℝ)) (Ioi (1 / Real.sqrt N)) :=
    (h3.const_mul _).add (h2.const_mul _)
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 / Real.sqrt N)))
    (f := fun x => depthThreeF N x - gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) hmaj ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [integral_add (h3.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) ha0, integral_Ioi_rpow_of_lt (by norm_num) ha0]
    have e3 : (1 / Real.sqrt N) ^ (-3 + 1 : ℝ) = N := by
      rw [show (-3 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg (by positivity), one_div,
        Real.inv_rpow hsN.le, inv_inv, Real.rpow_two, Real.sq_sqrt hN0.le]
    have e2 : (1 / Real.sqrt N) ^ (-2 + 1 : ℝ) = Real.sqrt N := by
      rw [show (-2 + 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div, inv_inv]
    rw [e3, e2]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsq : Real.sqrt N ^ 2 = N

/-- The `(a, 1]`-integrand `P(x) = (log N + 2 log x + c)/x`. -/
noncomputable def depthThreeP (N x : ℝ) : ℝ

theorem integrableOn_depthThreeP {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (depthThreeP N) (Ioc (1 / Real.sqrt N) 1) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
  refine ContinuousOn.intervalIntegrable ?_
  unfold depthThreeP
  have hlogc : ContinuousOn Real.log (uIcc (1 / Real.sqrt N) 1)

/-- `∫_a^1 P = (log N)²/4 + (c/2) log N` (from `integral_depthThreeM`). -/
theorem integral_depthThreeP {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioc (1 / Real.sqrt N) 1, depthThreeP N x =
      (Real.log N) ^ 2 / 4 + (3 * Real.log 2 - Real.eulerMascheroniConstant) / 2 * Real.log N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have e : ∀ x ∈ Ioc (1 / Real.sqrt N) 1, depthThreeP N x =
      2 * Real.pi * Real.sqrt N * depthThreeM N x := by
    intro x hx
    have hx0 : 0 < x

/-- The pointwise decomposition of the main-term integrand on `(a, ∞)`:
`g(x) L(x) = (1/(2π√N)) (1_{(a,1]} P(x) + (log N + c) h(x)/x + 2 h(x) log x/x)`. -/
theorem depthThree_gL_eq {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N < x) :
    gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))) =
      1 / (2 * Real.pi * Real.sqrt N) * ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N) x +
        ((Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
          2 * (gaussH x * Real.log x / x))) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hx0 : 0 < x := lt_trans (by positivity) hx
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  unfold gaussDensity gaussH depthThreeP
  generalize hsdef : Real.sqrt (2 * Real.pi) = s at hs hsq ⊢
  have hpi : Real.pi = s * s / 2 := by linarith
  rw [hpi]
  by_cases h1 : x ≤ 1
  · have hm : x ∈ Ioc (1 / Real.sqrt N) 1 := ⟨hx, h1⟩
    have hm' : x ∈ Ioc (0 : ℝ) 1 := ⟨hx0, h1⟩
    rw [indicator_of_mem hm, indicator_of_mem hm', Pi.one_apply]
    field_simp
    ring
  · have h1'

theorem integrableOn_depthThree_gL {N : ℝ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) (Ioi (1 / Real.sqrt N)) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hP₁ : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N))
      (Ioi (1 / Real.sqrt N)) :=
    ((integrableOn_depthThreeP hN).integrable_indicator measurableSet_Ioc).integrableOn
  have hQ1 : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)
  have hQ2 := integrableOn_gaussH_log ha0.le ha1
  have h : IntegrableOn (fun x : ℝ => 1 / (2 * Real.pi * Real.sqrt N) *
      ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N) x +
        ((Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
          2 * (gaussH x * Real.log x / x)))) (Ioi (1 / Real.sqrt N))

/-- ★★ **The main term**: with `I_a = ∫₀^a h/x` and `J_a = ∫_a^∞ h log x/x`, `a = N^{−1/2}`,
`∫_a^∞ g L = (1/(2π√N)) ((log N)²/4 + (c/2) log N + (log N + c)(R₀ − I_a) + 2 J_a)`. -/
theorem integral_depthThree_main {N : ℝ} (hN : 1 ≤ N) :
    ∫ x in Ioi (1 / Real.sqrt N), gaussDensity x *
      ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x))) =
      1 / (2 * Real.pi * Real.sqrt N) * ((Real.log N) ^ 2 / 4 +
        (3 * Real.log 2 - Real.eulerMascheroniConstant) / 2 * Real.log N +
        (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) *
          ((Real.log 2 - Real.eulerMascheroniConstant) / 2 -
            ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x) +
        2 * ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hP₁ : IntegrableOn ((Ioc (1 / Real.sqrt N) 1).indicator (depthThreeP N))
      (Ioi (1 / Real.sqrt N)) :=
    ((integrableOn_depthThreeP hN).integrable_indicator measurableSet_Ioc).integrableOn
  have hQ1 : IntegrableOn (fun x : ℝ => gaussH x / x) (Ioi (1 / Real.sqrt N)) :=
    integrableOn_gaussH_div.mono_set (Ioi_subset_Ioi ha0.le)
  have hQ2 := integrableOn_gaussH_log ha0.le ha1
  have hQ1' : IntegrableOn (fun x : ℝ =>
      (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x))
      (Ioi (1 / Real.sqrt N)) := hQ1.const_mul _
  have hQ2' : IntegrableOn (fun x : ℝ => 2 * (gaussH x * Real.log x / x))
      (Ioi (1 / Real.sqrt N)) := hQ2.const_mul _
  have hQ : IntegrableOn (fun x : ℝ =>
      (Real.log N + (3 * Real.log 2 - Real.eulerMascheroniConstant)) * (gaussH x / x) +
        2 * (gaussH x * Real.log x / x)) (Ioi (1 / Real.sqrt N)) := hQ1'.add hQ2'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => depthThree_gL_eq hN hx),
    integral_const_mul, integral_add hP₁ hQ, integral_add hQ1' hQ2', integral_const_mul,
    integral_const_mul,
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (1 / Real.sqrt N) ∩ Ioc (1 / Real.sqrt N) 1 = Ioc (1 / Real.sqrt N) 1 from
      inter_eq_right.2 fun x hx => hx.1,
    integral_depthThreeP hN]
  -- `∫_a^∞ h/x = R₀ − ∫₀^a h/x`
  have hsplit : ∫ x in Ioi (1 / Real.sqrt N), gaussH x / x =
      (Real.log 2 - Real.eulerMascheroniConstant) / 2 -
        ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x

/-- ★★★ **The depth-three Gaussian DLN, two terms with bounded residual**: for `N ≥ 1`,
`|Z_3(N) − [(log N)² + 4(2 log 2 − γ) log N]/(4π√N)| ≤ 12/√N`. -/
theorem gaussLaplaceL_three_two_term_bound {N : ℝ} (hN : 1 ≤ N) :
    |gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) /
        (4 * Real.pi * Real.sqrt N)| ≤ 12 / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN
  have hsNN : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le]
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact hsN1
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hℓ2 : Real.log N ≤ 2 * Real.sqrt N := log_le_two_sqrt hN0
  have hpi := Real.pi_gt_three
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
  have hR0 : 0 < Real.log 2 - Real.eulerMascheroniConstant ∧
      Real.log 2 - Real.eulerMascheroniConstant < 1 := by
    have := Real.log_two_gt_d9
    have := Real.eulerMascheroniConstant_lt_two_thirds
    have := Real.one_half_lt_eulerMascheroniConstant
    have h4 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    constructor <;> linarith
  -- the split of the recursion integral
  have hF := integrable_depthThreeF hN0.le
  have hsplit : ∫ x in Ioi (0 : ℝ), depthThreeF N x =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x) +
        ∫ x in Ioi (1 / Real.sqrt N), depthThreeF N x := by
    rw [← Ioc_union_Ioi_eq_Ioi ha0.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hF.integrableOn hF.integrableOn]
  have hgL := integrableOn_depthThree_gL hN
  have hmid : ∫ x in Ioi (1 / Real.sqrt N), depthThreeF N x =
      (∫ x in Ioi (1 / Real.sqrt N), gaussDensity x *
        ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
          (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) +
        ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
          ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
            (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) := by
    rw [integral_sub hF.integrableOn hgL]; ring
  have h0 := depthThree_inner_le hN0.le ha0.le
  have hE := depthThree_rem_le hN
  have hI := abs_integral_gaussH_div_Ioc_le ha0.le ha1
  have hJ := abs_integral_gaussH_log_le ha0.le ha1
  have hmain := integral_depthThree_main hN
  rw [gaussLaplaceL_three hN0.le]
  change |(∫ x, depthThreeF N x) - _| ≤ _
  rw [integral_depthThreeF_eq_two_mul, hsplit, hmid, hmain]
  set I₀ := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), depthThreeF N x with hI₀
  set E := ∫ x in Ioi (1 / Real.sqrt N), (depthThreeF N x - gaussDensity x *
    ((Real.log N + 2 * Real.log x + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
      (Real.sqrt (2 * Real.pi) * (Real.sqrt N * x)))) with hEdef
  set Ia := ∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussH x / x with hIa
  set Ja := ∫ x in Ioi (1 / Real.sqrt N), gaussH x * Real.log x / x with hJa
  clear_value I₀ E Ia Ja
  set c := 3 * Real.log 2 - Real.eulerMascheroniConstant with hc
  set d := Real.log 2 - Real.eulerMascheroniConstant with hd
  have hcd : 2 * Real.log 2 - Real.eulerMascheroniConstant = c / 2 + d / 2 := by rw [hc, hd]; ring
  rw [hcd]
  clear_value c d
  set ℓ := Real.log N with hℓdef
  clear_value ℓ
  clear hI₀ hEdef hIa hJa hc hd hℓdef hsplit hmid hmain hgL hF
  have hkey : 2 * (I₀ + (1 / (2 * Real.pi * Real.sqrt N) * (ℓ ^ 2 / 4 + c / 2 * ℓ +
      (ℓ + c) * (d / 2 - Ia) + 2 * Ja) + E)) -
      (ℓ ^ 2 + 4 * (c / 2 + d / 2) * ℓ) / (4 * Real.pi * Real.sqrt N) =
      2 * I₀ + 2 * E + 1 / (Real.pi * Real.sqrt N) * (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) := by
    field_simp
    ring
  rw [hkey]
  rw [abs_le] at h0 hE hI hJ ⊢
  -- the bracket is bounded by 10
  have hIa2 : (1 / Real.sqrt N) ^ 2 = 1 / N := by
    rw [div_pow, one_pow, Real.sq_sqrt hN0.le]
  rw [hIa2] at hI
  have hbr : |c * (d / 2) - (ℓ + c) * Ia + 2 * Ja| ≤ 10 := by
    have h1 : |c * (d / 2)| ≤ 3 / 2 := by
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have h2 : |(ℓ + c) * Ia| ≤ 5 / 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      have hIabs : |Ia| ≤ 1 / N / 2 := abs_le.2 hI
      calc (ℓ + c) * |Ia| ≤ (2 * Real.sqrt N + 3) * (1 / N / 2) :=
            mul_le_mul (by linarith) hIabs (abs_nonneg _) (by positivity)
        _ ≤ 5 / 2 := by
            rw [show (2 * Real.sqrt N + 3) * (1 / N / 2) = (2 * Real.sqrt N + 3) / (2 * N) by ring,
              div_le_iff₀ (by positivity)]
            nlinarith
    have h3 : |2 * Ja| ≤ 6 := by rw [abs_mul, abs_of_pos two_pos]; linarith [abs_le.2 hJ]
    calc |c * (d / 2) - (ℓ + c) * Ia + 2 * Ja| ≤ |c * (d / 2) - (ℓ + c) * Ia| + |2 * Ja| :=
          abs_add_le _ _
      _ ≤ |c * (d / 2)| + |(ℓ + c) * Ia| + |2 * Ja| := by
          linarith [abs_sub (c * (d / 2)) ((ℓ + c) * Ia)]
      _ ≤ 10 := by linarith
  rw [abs_le] at hbr
  have hT0 : 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) ≤ 1 / Real.sqrt N := by
    rw [show 2 * (1 / Real.sqrt (2 * Real.pi) * (1 / Real.sqrt N)) =
      (2 / Real.sqrt (2 * Real.pi)) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by linarith)]; linarith
  have hT1 : 2 * (1 / (Real.pi * Real.sqrt N)) ≤ 1 / Real.sqrt N := by
    rw [show 2 * (1 / (Real.pi * Real.sqrt N)) = (2 / Real.pi) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]; linarith
  have hT2 : 1 / (Real.pi * Real.sqrt N) * 10 ≤ 4 / Real.sqrt N := by
    rw [show 1 / (Real.pi * Real.sqrt N) * 10 = (10 / Real.pi) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    rw [div_le_iff₀ (by positivity)]; linarith
  have hT2' : 1 / (Real.pi * Real.sqrt N) * (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) ≤
      4 / Real.sqrt N := by
    have : 0 ≤ 1 / (Real.pi * Real.sqrt N) := by positivity
    nlinarith
  have hT2'' : -(4 / Real.sqrt N) ≤ 1 / (Real.pi * Real.sqrt N) *
      (c * (d / 2) - (ℓ + c) * Ia + 2 * Ja) := by
    have : 0 ≤ 1 / (Real.pi * Real.sqrt N) := by positivity
    nlinarith
  have hsum : 1 / Real.sqrt N + 1 / Real.sqrt N + 4 / Real.sqrt N ≤ 12 / Real.sqrt N

/-- ★★★ `Z_3(N) = [(log N)² + 4(2 log 2 − γ) log N]/(4π√N) + O(N^{−1/2})`: the second coefficient
of the depth-three expansion is `(2 log 2 − γ)/π`. -/
theorem gaussLaplaceL_three_two_term :
    (fun N : ℝ => gaussLaplaceL 3 N - ((Real.log N) ^ 2 +
      4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.log N) /
        (4 * Real.pi * Real.sqrt N)) =O[atTop] fun N => (Real.sqrt N)⁻¹ := by
  refine Asymptotics.IsBigO.of_bound 12 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  have hsN : 0 < Real.sqrt N
```
### Grammar/GaussianDepthAllLeading.lean
```lean
/-- **Bochner peel of the first coordinate, integrated first**:
`∫ F = ∫ a, ∫ b, F (a, b)` on `Fin (d+1) → ℝ`. -/
theorem integral_pi_succ (d : ℕ) (F : (Fin (d + 1) → ℝ) → ℝ) (hF : Integrable F) :
    ∫ x, F x = ∫ a : ℝ, ∫ b : Fin d → ℝ, F (Fin.cons a b) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin d → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  rw [← (hmp.symm e).integral_comp e.symm.measurableEmbedding F]
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin d → ℝ)))

/-- ★★ **The scalar recursion**: `Z_{L+1}(N) = ∫ g(x) Z_L(N x²) dx` for `N ≥ 0`. -/
theorem gaussLaplaceL_succ_scalar (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    gaussLaplaceL (L + 1) N = ∫ x : ℝ, gaussDensity x * gaussLaplaceL L (N * x ^ 2)

/-- `Z_L(N) ∈ [0, 1]` for `N ≥ 0`. -/
theorem gaussLaplaceL_nonneg (L : ℕ) (N : ℝ) : 0 ≤ gaussLaplaceL L N

theorem gaussLaplaceL_zero_eq_one (L : ℕ) : gaussLaplaceL L 0 = 1 := by
  unfold gaussLaplaceL
  simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, one_mul]
  rw [volume_pi, integral_fintype_prod_eq_pow (fun x : ℝ => gaussDensity x)]
  have h1 : ∫ x : ℝ, gaussDensity x = 1 := by
    have

theorem gaussLaplaceL_le_one (L : ℕ) {N : ℝ} (hN : 0 ≤ N) : gaussLaplaceL L N ≤ 1

/-- The recursion integrand is integrable (Fubini on the pi space). -/
theorem integrable_density_mul_gaussLaplaceL (L : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Integrable fun x : ℝ => gaussDensity x * gaussLaplaceL L (N * x ^ 2) := by
  have hF := integrable_gaussLaplaceL (L + 1) hN
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L + 1) => ℝ) 0 with he
  have hsymm : ∀ y : ℝ × (Fin L → ℝ), e.symm y = Fin.cons y.1 y.2 := by
    intro y
    change Fin.insertNth (α := fun _ : Fin (L + 1) => ℝ) 0 y.1 y.2 = _
    exact Fin.insertNth_zero' y.1 y.2
  set F : (Fin (L + 1) → ℝ) → ℝ := fun w =>
    Real.exp (-N * (∏ i, w i) ^ 2 / 2) * ∏ i, gaussDensity (w i) with hFdef
  have hint : Integrable (fun y => F (e.symm y)) (volume : Measure (ℝ × (Fin L → ℝ)))

theorem intervalIntegrable_pow_log_div {a : ℝ} (b : ℝ) (n : ℕ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (fun x => (b + 2 * Real.log x) ^ n / x) volume a 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hlogc : ContinuousOn Real.log (uIcc a 1)

/-- `∫_a^1 (b + 2 log x)^n / x dx = (b^{n+1} − (b + 2 log a)^{n+1})/(2(n+1))` for `0 < a ≤ 1`. -/
theorem integral_pow_log_div {a : ℝ} (b : ℝ) (n : ℕ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫ x in Ioc a 1, (b + 2 * Real.log x) ^ n / x =
      (b ^ (n + 1) - (b + 2 * Real.log a) ^ (n + 1)) / (2 * (n + 1)) := by
  have hn : (0 : ℝ) < 2 * (n + 1) := by positivity
  have hderiv : ∀ x ∈ uIcc a 1, HasDerivAt (fun x => (b + 2 * Real.log x) ^ (n + 1) / (2 * (n + 1)))
      ((b + 2 * Real.log x) ^ n / x) x := by
    intro x hx
    rw [uIcc_of_le ha1] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hin : HasDerivAt (fun x : ℝ => b + 2 * Real.log x) (2 * x⁻¹) x :=
      ((Real.hasDerivAt_log hx0.ne').const_mul 2).const_add b
    have hout := (hasDerivAt_pow (n + 1) (b + 2 * Real.log x)).comp x hin
    have h := hout.div_const (2 * (n + 1))
    refine h.congr_deriv ?_
    push_cast
    field_simp
  have hint

/-- `x (1 + 2|log x|)^{n+1} ≤ (2n + 3)^{n+1}` on `(0, 1]`. -/
theorem mul_pow_one_add_log_le {x : ℝ} (n : ℕ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    x * (1 + 2 * |Real.log x|) ^ (n + 1) ≤ (2 * n + 3) ^ (n + 1) := by
  have hx0 : 0 < x := hx.1
  have hδ : (0 : ℝ) < 1 / (n + 1) := by positivity
  have hlog := abs_log_le_rpow_div hδ hx
  have hpow1 : 1 ≤ x ^ (-(1 / (n + 1) : ℝ)) := by
    rw [Real.rpow_neg hx0.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hx0 _) |>.2 (Real.rpow_le_one hx0.le hx.2 hδ.le)
  have h1 : 1 + 2 * |Real.log x| ≤ (2 * n + 3) * x ^ (-(1 / (n + 1) : ℝ)) := by
    have : |Real.log x| ≤ (n + 1) * x ^ (-(1 / (n + 1) : ℝ)) := by
      rw [div_div_eq_mul_div, div_one] at hlog
      linarith [hlog]
    nlinarith
  have h2 : (1 + 2 * |Real.log x|) ^ (n + 1) ≤
      ((2 * n + 3) * x ^ (-(1 / (n + 1) : ℝ))) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (x ^ (-(1 / (n + 1) : ℝ))) ^ (n + 1) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show (-(1 / (n + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ)) = -1 by push_cast; field_simp,
      Real.rpow_neg_one]
  rw [mul_pow, h3] at h2
  calc x * (1 + 2 * |Real.log x|) ^ (n + 1) ≤ x * ((2 * n + 3) ^ (n + 1) * x⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hx0.le
    _ = (2 * n + 3) ^ (n + 1)

/-- `x^n e^{−x²/2} ≤ n! e² e^{−x/2}` for `x ≥ 0`. -/
theorem pow_mul_exp_neg_half_sq_le {x : ℝ} (n : ℕ) (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x ^ 2 / 2) ≤ (n.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2) := by
  have h1 : x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx n
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : Real.exp x * Real.exp (-x ^ 2 / 2) ≤ Real.exp 2 * Real.exp (-x / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (x - 3 / 2)])
  calc x ^ n * Real.exp (-x ^ 2 / 2) ≤ (n.factorial : ℝ) * Real.exp x * Real.exp (-x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (Real.exp x * Real.exp (-x ^ 2 / 2)) := by ring
    _ ≤ (n.factorial : ℝ) * (Real.exp 2 * Real.exp (-x / 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (n.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)

/-- The hypotheses of the propagation step: `0 ≤ f ≤ 1` on `t ≥ 0` and the leading asymptotic
`|f(t) − A (log t)^{m+1}/√t| ≤ C (1 + log t)^m/√t` for `t ≥ 1`. -/
structure LeadingData (f : ℝ → ℝ) (A C : ℝ) (m : ℕ) : Prop

/-- The inner piece `(0, a]`: `|∫₀^a g f(Nx²)| ≤ a/√(2π)`. -/
theorem step_inner_le (h : LeadingData f A C m) {N a : ℝ} (hN : 0 ≤ N) (ha : 0 ≤ a) :
    |∫ x in Ioc (0 : ℝ) a, gaussDensity x * f (N * x ^ 2)| ≤ 1 / Real.sqrt (2 * Real.pi) * a := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) a)
    (f := fun x => gaussDensity x * f (N * x ^ 2)) (C := 1 / Real.sqrt (2 * Real.pi))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun x _ => by
      have h0 := h.f_nonneg (N * x ^ 2) (by positivity)
      have h1 := h.f_le_one (N * x ^ 2) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussDensity_nonneg _) h0)]
      unfold gaussDensity
      calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * f (N * x ^ 2)
          ≤ 1 / Real.sqrt (2 * Real.pi) * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right
              (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])) hs.le) h1 h0 (by positivity)
        _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _)
  have hv : volume.real (Ioc (0 : ℝ) a) = a

/-- At `t = N x² ≥ 1`: `log t = log N + 2 log x`, `√t = √N x`. -/
theorem log_sqrt_mul_sq {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    Real.log (N * x ^ 2) = Real.log N + 2 * Real.log x ∧ Real.sqrt (N * x ^ 2) = Real.sqrt N * x

theorem one_le_mul_sq_of_le {N x : ℝ} (hN : 1 ≤ N) (hx : 1 / Real.sqrt N ≤ x) : 1 ≤ N * x ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h3 : (1 / Real.sqrt N) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
  have h4 : (1 / Real.sqrt N) ^ 2 * N = 1

/-- The middle piece: with `P(x) = (log N + 2 log x)^{m+1}/(√N x)`,
`|∫_a^1 (g f(Nx²) − A P/√(2π))| ≤ (C + A(2m+3)^{m+1})(1 + log N)^{m+1}/(4√N)`. -/
theorem step_middle_le (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioc (1 / Real.sqrt N) 1, (gaussDensity x * f (N * x ^ 2) -
      1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))))| ≤
      (C + A * (2 * m + 3) ^ (m + 1)) * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  set K₁ : ℝ := (2 * m + 3) ^ (m + 1) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- the majorant
  set D : ℝ → ℝ := fun x => C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
    ((1 + Real.log N + 2 * Real.log x) ^ m / x) +
    A * K₁ * (1 + Real.log N) ^ (m + 1) / (2 * Real.sqrt (2 * Real.pi) * Real.sqrt N) with hD
  have hDint : IntegrableOn D (Ioc (1 / Real.sqrt N) 1) := by
    rw [hD, ← intervalIntegrable_iff_integrableOn_Ioc_of_le ha1]
    exact ((intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1).const_mul _).add
      intervalIntegrable_const
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (1 / Real.sqrt N) 1))
    (f := fun x => gaussDensity x * f (N * x ^ 2) - 1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) hDint ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [hD, integral_add ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1
        ((intervalIntegrable_pow_log_div (1 + Real.log N) m ha0 ha1).const_mul _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha1).1 intervalIntegrable_const),
      integral_const_mul, integral_pow_log_div (1 + Real.log N) m ha0 ha1, setIntegral_const]
    have hloga : Real.log (1 / Real.sqrt N) = -(Real.log N / 2) := by
      rw [one_div, Real.log_inv, Real.log_sqrt hN0.le]
    have hv : volume.real (Ioc (1 / Real.sqrt N) 1) = 1 - 1 / Real.sqrt N := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [hloga, hv, smul_eq_mul, show 1 + Real.log N + 2 * -(Real.log N / 2) = 1 by ring, one_pow]
    have hp1 : 1 ≤ (1 + Real.log N) ^ (m + 1) := one_le_pow₀ (by linarith)
    have hp0 : 0 ≤ (1 + Real.log N) ^ (m + 1) := by positivity
    have h1 : C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) ≤
        C * (1 + Real.log N) ^ (m + 1) / (4 * Real.sqrt N) := by
      have hm1 : (1 : ℝ) ≤ 2 * (m + 1) := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [show C / (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
        (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) =
        C * (((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1))) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : ((1 + Real.log N) ^ (m + 1) - 1) / (2 * (m + 1)) ≤ (1 + Real.log N) ^ (m + 1) / 2

/-- The tail `(1, ∞)`: `|∫₁^∞ g f(Nx²)| ≤ 8 (A + C) 3^{m+1} m! (1 + log N)^{m+1}/√N`. -/
theorem step_tail_le (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N) :
    |∫ x in Ioi (1 : ℝ), gaussDensity x * f (N * x ^ 2)| ≤
      8 * (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  have he : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  set K : ℝ := (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * m.factorial * Real.exp 2 /
    (Real.sqrt (2 * Real.pi) * Real.sqrt N) with hK
  have hK0 : 0 ≤ K := by positivity
  have hmaj : IntegrableOn (fun x : ℝ => K * Real.exp (-x / 2)) (Ioi 1) := by
    refine IntegrableOn.congr_fun (s := Ioi 1)
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K) (fun w _ => ?_)
      measurableSet_Ioi
    congr 2
    ring
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (f := fun x => gaussDensity x * f (N * x ^ 2)) hmaj ?_
  · rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    rw [integral_const_mul, integral_exp_neg_div_Ioi_one (by norm_num : (0 : ℝ) < 2)]
    have he2 : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have hKle : K * (2 * Real.exp (-1 / 2)) ≤ K * 2 := by
      have := Real.exp_pos (-1 / 2)
      nlinarith
    refine hKle.trans ?_
    rw [hK, show (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * m.factorial * Real.exp 2 /
      (Real.sqrt (2 * Real.pi) * Real.sqrt N) * 2 =
      (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) *
        (2 * Real.exp 2 / Real.sqrt (2 * Real.pi)) / Real.sqrt N by field_simp]
    refine div_le_div_of_nonneg_right ?_ hsN.le
    have hq : 2 * Real.exp 2 / Real.sqrt (2 * Real.pi) ≤ 8 := by
      rw [div_le_iff₀ hs]; nlinarith
    have hbase : 0 ≤ (A + C) * 3 ^ (m + 1) * m.factorial * (1 + Real.log N) ^ (m + 1) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hq hbase]
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    have hx : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
    have ht := one_le_mul_sq_of_le (x := x) hN (ha1.trans hx.le)
    obtain ⟨hlog, hsqrt⟩ := log_sqrt_mul_sq hN0 hx0
    have hbd := (abs_le.1 (h.bound (N * x ^ 2) ht)).2
    rw [hlog, hsqrt] at hbd
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
    have hf0 := h.f_nonneg (N * x ^ 2) (by positivity)
    have hg0 := gaussDensity_nonneg x
    -- `f(Nx²) ≤ (A + C)(1 + log N + 2 log x)^{m+1}/(√N x) ≤ (A + C)(1 + log N)^{m+1} 3^{m+1}
    -- x^m/√N`
    have hbase : 0 ≤ Real.log N + 2 * Real.log x := by linarith
    have h1 : (Real.log N + 2 * Real.log x) ^ (m + 1) ≤
        (1 + Real.log N + 2 * Real.log x) ^ (m + 1) :=
      pow_le_pow_left₀ hbase (by linarith) _
    have h2 : (1 + (Real.log N + 2 * Real.log x)) ^ m ≤
        (1 + Real.log N + 2 * Real.log x) ^ (m + 1) := by
      rw [show 1 + (Real.log N + 2 * Real.log x) = 1 + Real.log N + 2 * Real.log x by ring]
      exact pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have h3 : 1 + Real.log N + 2 * Real.log x ≤ (1 + Real.log N) * (3 * x) := by
      nlinarith
    have h4 : (1 + Real.log N + 2 * Real.log x) ^ (m + 1) ≤
        (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1) := by
      calc (1 + Real.log N + 2 * Real.log x) ^ (m + 1) ≤ ((1 + Real.log N) * (3 * x)) ^ (m + 1) :=
            pow_le_pow_left₀ (by linarith) h3 _
        _ = (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1) := by
            rw [mul_pow, mul_pow]; ring
    have hf : f (N * x ^ 2) ≤ (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m /
        Real.sqrt N := by
      calc f (N * x ^ 2) ≤ A * (Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) +
            C * (1 + (Real.log N + 2 * Real.log x)) ^ m / (Real.sqrt N * x) := by linarith
        _ ≤ A * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) +
            C * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) := by
            gcongr
        _ = (A + C) * (1 + Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x) := by ring
        _ ≤ (A + C) * ((1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ (m + 1)) /
            (Real.sqrt N * x) := by gcongr
        _ = (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m / Real.sqrt N := by
            field_simp
            ring
    have hxm := pow_mul_exp_neg_half_sq_le m hx0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hf0)]
    unfold gaussDensity
    calc Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) * f (N * x ^ 2)
        ≤ Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi) *
          ((A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) * x ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) * (x ^ m * Real.exp (-x ^ 2 / 2)) := by
          field_simp
      _ ≤ (A + C) * (1 + Real.log N) ^ (m + 1) * 3 ^ (m + 1) /
          (Real.sqrt (2 * Real.pi) * Real.sqrt N) *
          ((m.factorial : ℝ) * Real.exp 2 * Real.exp (-x / 2)) :=
          mul_le_mul_of_nonneg_left hxm (by positivity)
      _ = K * Real.exp (-x / 2)

/-- ★★ **The propagation step**: if `f` has the leading asymptotic `A (log t)^{m+1}/√t` with error
`C (1 + log t)^m/√t`, then `F(N) = ∫ g(x) f(N x²) dx` has the leading asymptotic
`A/((m+2)√(2π)) · (log N)^{m+2}/√N` with error `C' (1 + log N)^{m+1}/√N`,
`C' = 1 + (C + A(2m+3)^{m+1})/2 + 16(A + C)3^{m+1} m!`. -/
theorem gaussianStep_bound (h : LeadingData f A C m) {N : ℝ} (hN : 1 ≤ N)
    (hint : Integrable fun x => gaussDensity x * f (N * x ^ 2)) :
    |(∫ x, gaussDensity x * f (N * x ^ 2)) -
      A / ((m + 2) * Real.sqrt (2 * Real.pi)) * (Real.log N) ^ (m + 2) / Real.sqrt N| ≤
      (1 + (C + A * (2 * m + 3) ^ (m + 1)) / 2 + 16 * (A + C) * 3 ^ (m + 1) * m.factorial) *
        (1 + Real.log N) ^ (m + 1) / Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have ha0 : 0 < 1 / Real.sqrt N := by positivity
  have ha1 : 1 / Real.sqrt N ≤ 1 := by rw [div_le_one hsN]; exact Real.one_le_sqrt.2 hN
  have hℓ : 0 ≤ Real.log N := Real.log_nonneg hN
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  have hA := h.A_nonneg
  have hC := h.C_nonneg
  -- evenness
  have heven : ∫ x, gaussDensity x * f (N * x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) := by
    rw [← integral_comp_abs (f := fun x => gaussDensity x * f (N * x ^ 2))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [gaussDensity, sq_abs]
  -- the split
  have hsplit : ∫ x in Ioi (0 : ℝ), gaussDensity x * f (N * x ^ 2) =
      (∫ x in Ioc (0 : ℝ) (1 / Real.sqrt N), gaussDensity x * f (N * x ^ 2)) +
        (∫ x in Ioc (1 / Real.sqrt N) 1, gaussDensity x * f (N * x ^ 2)) +
        ∫ x in Ioi (1 : ℝ), gaussDensity x * f (N * x ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
        hint.integrableOn,
      ← Ioc_union_Ioc_eq_Ioc ha0.le ha1,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hint.integrableOn
        hint.integrableOn]
  -- the main term on `(a, 1]`
  have hM : IntegrableOn (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi) *
      (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x)))) (Ioc (1 / Real.sqrt N)
          1) := by
    have e : ∀ x : ℝ, 1 / Real.sqrt (2 * Real.pi) *
        (A * ((Real.log N + 2 * Real.log x) ^ (m + 1) / (Real.sqrt N * x))) =
        A / (Real.sqrt (2 * Real.pi) * Real.sqrt N) * ((Real.log N + 2 * Real.log x) ^ (m + 1) / x)

/-- `Z_2 = gaussLaplace2` (the pair transported to `Fin 2 → ℝ`). -/
theorem gaussLaplaceL_two (N : ℝ) : gaussLaplaceL 2 N = gaussLaplace2 N := by
  unfold gaussLaplaceL gaussLaplace2
  have hmp := volume_preserving_finTwoArrow ℝ
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) with he
  set G : ℝ × ℝ → ℝ := fun p => Real.exp (-N * (p.1 * p.2) ^ 2 / 2) *
    (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) / (2 * Real.pi)) with hG
  have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  have hcomp : ∀ b : Fin 2 → ℝ, Real.exp (-N * (∏ i, b i) ^ 2 / 2) * ∏ i, gaussDensity (b i) =
      G (e b)

/-- The depth-two base of the induction: `A = 1/√(2π)`, `C = 5/2`, `m = 0`. -/
theorem leadingData_two : LeadingData gaussLaplace2 (1 / Real.sqrt (2 * Real.pi)) (5 / 2) 0 where
  A_nonneg := by positivity
  C_nonneg := by norm_num
  f_nonneg t ht := gaussLaplace2_nonneg ht
  f_le_one t ht := gaussLaplace2_le_one ht
  bound t ht := by
    have ht0 : 0 < t := by linarith
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hs2 : 2 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
    obtain ⟨hb, -⟩ := gaussLaplace2_bounds ht
    obtain ⟨hc1, hc3⟩ := three_log_two_sub_gamma_bounds
    have hrem : (Real.log (2 * t) + 3) / (2 * t * (Real.sqrt (2 * Real.pi) * Real.sqrt t)) ≤
        2 / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by
      have hlog : Real.log (2 * t) ≤ 2 * t - 1 := by
        linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hs hst]
    have hb2 := (abs_le.1 hb)
    simp only [zero_add, pow_one, pow_zero, mul_one]
    rw [abs_le]
    have e1 : 1 / Real.sqrt (2 * Real.pi) * Real.log t / Real.sqrt t =
        Real.log t / (Real.sqrt (2 * Real.pi) * Real.sqrt t) := by field_simp
    have e2 : (Real.log t + 3 * Real.log 2 - Real.eulerMascheroniConstant) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt t) = Real.log t / (Real.sqrt (2 * Real.pi) * Real.sqrt
            t) +
        (3 * Real.log 2 - Real.eulerMascheroniConstant) / (Real.sqrt (2 * Real.pi) * Real.sqrt t)

/-- ★★★ **The leading asymptotic at every depth**: for every `m`, there is `C_m` with
`|Z_{m+2}(N) − (log N)^{m+1}/((m+1)! √(2π)^{m+1} √N)| ≤ C_m (1 + log N)^m/√N` for all `N ≥ 1`
(packaged as the leading data of `Z_{m+2}`). -/
theorem gaussLaplaceL_leading_bound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    LeadingData (gaussLaplaceL (m + 2))
      (1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1))) C m := by
  induction m with
  | zero =>
    refine ⟨5 / 2, by norm_num, ?_⟩
    have e : gaussLaplaceL 2 = gaussLaplace2 := funext gaussLaplaceL_two
    rw [e]
    simpa using leadingData_two
  | succ m ih =>
    obtain ⟨C, hC, hd⟩ := ih
    set A := 1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)) with hA
    have hA0 : 0 ≤ A := hd.A_nonneg
    refine ⟨1 + (C + A * (2 * m + 3) ^ (m + 1)) / 2 + 16 * (A + C) * 3 ^ (m + 1) * m.factorial,
      by positivity, ?_⟩
    have hA' : 1 / ((m + 1 + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1 + 1)) =
        A / ((m + 2) * Real.sqrt (2 * Real.pi)) := by
      rw [hA, Nat.factorial_succ]
      have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
      push_cast
      field_simp
      ring
    refine ⟨by rw [hA']; positivity, by positivity, fun t _ => gaussLaplaceL_nonneg _ t,
      fun t ht => gaussLaplaceL_le_one _ ht, fun t ht => ?_⟩
    have hint := integrable_density_mul_gaussLaplaceL (m + 2) (by linarith : (0 : ℝ) ≤ t)
    have h

/-- ★★★ `√N Z_L(N)/(log N)^{L−1} → 1/((L−1)! (2π)^{(L−1)/2})` for every depth `L = m + 2 ≥ 2`. -/
theorem gaussLaplaceL_leading (m : ℕ) :
    Tendsto (fun N : ℝ => Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1)) atTop
      (𝓝 (1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)))) := by
  obtain ⟨C, hC, hd⟩ := gaussLaplaceL_leading_bound m
  set A := 1 / ((m + 1).factorial * Real.sqrt (2 * Real.pi) ^ (m + 1)) with hA
  clear_value A
  have hbound : ∀ᶠ N : ℝ in atTop,
      |Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1) - A| ≤
        C * 2 ^ m / Real.log N := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with N hN3
    have hN : 1 ≤ N := by linarith
    have hN0 : 0 < N := by linarith
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have hℓ : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hℓ0 : 0 < Real.log N := by linarith
    have h := hd.bound N hN
    have e : Real.sqrt N * gaussLaplaceL (m + 2) N / (Real.log N) ^ (m + 1) - A =
        (Real.sqrt N / (Real.log N) ^ (m + 1)) *
          (gaussLaplaceL (m + 2) N - A * (Real.log N) ^ (m + 1) / Real.sqrt N) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hpow : (1 + Real.log N) ^ m ≤ (2 * Real.log N) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    calc Real.sqrt N / (Real.log N) ^ (m + 1) *
          |gaussLaplaceL (m + 2) N - A * (Real.log N) ^ (m + 1) / Real.sqrt N|
        ≤ Real.sqrt N / (Real.log N) ^ (m + 1) * (C * (1 + Real.log N) ^ m / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C * (1 + Real.log N) ^ m / (Real.log N) ^ (m + 1) := by field_simp
      _ ≤ C * (2 * Real.log N) ^ m / (Real.log N) ^ (m + 1) := by gcongr
      _ = C * 2 ^ m / Real.log N := by
          rw [mul_pow, pow_succ]
          field_simp
  have hlim : Tendsto (fun N : ℝ => C * 2 ^ m / Real.log N) atTop (𝓝 0) := by
    have
```

## State of the note (pinned to grammar 9a7eea6)
Formal: §2 DLN flat prior at every depth; 1D polar dictionaries; Gaussian product zeta and pole; the depth-two Gaussian two-term expansion with explicit remainder; the crossing corollary; all-depth conditional reduction, `ζ_K = 2^s ζ_L` and its leading coefficient; depth-three two-term expansion with bounded residual; the all-depth leading asymptotic with explicit-shape error. §3 cone: exact Leray closed form with Gaussian tails. §4 blow-up: tie formulas (polynomial / smooth / arbitrary smooth), Laurent data, the two-term Laplace expansion of the model, the monomial renormalised constant. §5 rank-one: normal integral and tilt at aligned and general orbit points, the invariant tangent projection. §6 naive Bayes: pushforward density, surrogate exactness, fibre polar distributions, averaged theorem on a ball, domination adapter, envelope certificate, basepoint adapter.
Derivation-only (checked numerically): the depth-three constant term `((4 log 2 − 2γ)² + π²)/(4π)` and the lower coefficients for `L ≥ 4`; the Bessel closed form at `L = 2`; `H₃`, `ζ(3)`; the naive Bayes envelope `M_±(λ)` facewise integrability and the joint measurability of the fibre family, KL-vs-surrogate remainder, `m₂`; the cone averaged posterior and the exact expansion prefactors; the family `K = x²(x^{2k−2} + y²)/2` beyond `k = 2`; the blow-up higher poles and the observable expansions of §4; the Morse–Bott passage for rank-one; the smooth-amplitude tie remainder beyond `O(1)`; an abstract Mellin transfer theorem.

## Library facts
Everything of rounds 1–8: the general-amplitude engine `ampJ_two_term`, the monomial constants, the depth-two explicit bounds `gaussLaplace2_bounds`, the propagation structure `LeadingData`/`gaussianStep_bound`, the scalar recursion at every depth, Bochner peels in both orders, `volume_preserving_finTwoArrow`, the Mellin engine, `Convex.norm_image_sub_le_of_norm_deriv_le`, matrix trace identities, Gamma values at ½ and 1. Mathlib pin v4.33.1.

## Questions
1. Fidelity check (brief) of DCXXI–DCXXIV against the note's claims and your round-8 specifications; in particular (a) DCXXIV's error shape `(1 + log N)^m/√N` at depth `m+2` (is the `1 +` needed, and is the constant recursion `C' = 1 + (C + A(2m+3)^{m+1})/2 + 16(A+C)3^{m+1}m!` sensible); (b) DCXXIII's constant 12 and the coefficient identification `c/2 + R₀ = 2 log 2 − γ`; (c) whether `LeadingData` is the right reusable interface or should carry the second coefficient too.
2. Rank the next three day-sized formal targets by value-per-effort (concrete Lean statements + routes). Candidates: (a) a two-term propagation step (carrying the second coefficient: from `f(t) = A(log t)^{m+1}/√t + B(log t)^m/√t + O((1+log t)^{m−1}/√t)` to `F`), giving the second coefficient at every depth — what is the recursion for `B` (does it match the note's `P_{L−1}` polynomials' subleading coefficient, and what is the role of `R₀ = (log 2 − γ)/2` at each step); (b) the family theorem `K = x²(x^{2k−2} + y²)/2` for all `k ≥ 2` with the monomial constant (the scaling `N = m^{2k}`, `x = u/m`, `ε = m^{2−2k}`, and `|R_{a_m} − R_∞| = O(1/m²)` as in DCXV): `Z_k(N) = √(2π)N^{−1/2}[((k−1)/k) log N + 2 log 2 + (log 2 − γ)/k] + O(N^{−1/2}(1 + …))` — what remainder order is honest; (c) the depth-three constant term by a refined DCXXIII (the `O(1/√N)` residual identified as `((4 log 2 − 2γ)² + π²)/(4π)`: which pieces contribute — the cutoff `∫₀^a h/x`, the induction error integrated exactly, the tail, and `∫ h log x/x = ?` (is `∫₀^∞ h(x) log x/x dx` a known constant, e.g. from `Γ''(1)` or `∫ e^{−x²/2} log² x`)); (d) the naive Bayes envelope on one face as a template (we can supply the density formula next round); (e) the cone averaged posterior (we can supply the integrand); (f) the Bessel closed form at `L = 2`, `Z_2(N) = e^{1/4N}K₀(1/4N)/√(2πN)` — Mathlib has no Bessel functions; is a self-contained definition of `K₀` by its integral representation and the identity worth a day? Say which are honest day-sized targets and give the Lean-facing interface for the top three.
3. Convention hazards in the four new files (the `LeadingData` fields, the `(m+2)` indexing of the depth, `ampRenorm` with the indicator vs the split form, the `12` and `18` constants, `tanProj` argument order).
Answer concisely with Lean-facing detail.
