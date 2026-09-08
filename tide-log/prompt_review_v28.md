# Fidelity review v28 — Programme S units 273–276: canonical cutoff on data balls, continuity of the integral, ordered normalised remainders, Headline XXXV (the stochastic Taylor tree)

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (repository `timaeus-research/grammar`, branch `tide/stochastic-taylor-tree`, pin `11930df`) of the grammar paper's §4.3 (`thm:strataempiricalexpansion`). Review v27 passed units 270–272 (weighted-ℓ¹ data space `DataSpace d = ℓ¹((Fin d → ℕ) ⊕ (Fin d → ℕ))`, the canonical box coefficient `dataBoxCoeff n h k β b x μ j` = coefficient of `N^{-μ}(log N)^j` in the expansion of the original box integral `dataBoxIntegral n h k β N b x = Z(N; ξ, η)`, ballwise Lipschitz continuity of `dataBoxCoeff` = Headline XXXIV) and listed should-fixes for A2: (1) canonical cutoff interface stated with `dataBoxCoeff`; (3) measurability of `x ↦ Z(N; x)` and of the remainders; (4) lock the finite predecessor set and the ordering `(ν,q) ≺ (μ,j) ↔ ν < μ ∨ (ν = μ ∧ q > j)`; (5) uniform normalised-remainder convergence on data balls with thresholds; (6) boundedness in probability and Slutsky. Units 273–276 implement these. Please review the STATEMENTS (mechanically extracted excerpts: docstring + statement up to `:=`; the extractor sometimes truncates/duplicates — the source has exactly one of each; everything compiles with zero `sorry` and no additional axioms) and the one proof reproduced in full.

## Frozen background (reviewed earlier)
- `boxTaylorTree_cutoff_bound` (Headline XXVIII): for `N ≥ 0`, `N b^{2|k|} ≥ 1`, `L > 0`: `|Z(N) − boxSpectralSum L N| ≤ b^{|h|+d} cutoffBound n k β L (ξ(0)) (mass η_b) (mass ξ_b) · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^n` where `ξ_b, η_b` are the rescaled unit-box families (= raw ℓ¹ coordinates `xiCoord x, etaCoord x`); `boxSpectralSum_eq` (for `N > 0`): `boxSpectralSum L N = ∑_{μ ∈ latticeBelow Q L} N^{-μ} ∑_{j ≤ n} boxCoeff μ j (log N)^j`, `latticeBelow Q L = {m/Q : m ∈ ℕ, m/Q < L}` (finite), `Q = latticeQ k = 2∏kᵢ`; the coefficients vanish off the candidate set `Λ(h,k) ⊂ Q⁻¹ℕ`.
- `cutoffBound n k β L a E B = K_k E ((n+1)! Q^n) (M_{L,n,0}(|a|+B) + tailConst β (|a|+B) 0 L n (4/β)(⌈L⌉! (4/β)^⌈L⌉))`, `M_{ν,r,p}(b) = ∫₀^∞ t^{ν−1}(1+|log t|)^r (√t)^p e^{−βt+βb√t} dt` monotone in the signed `b`; `tailConst β a p ν i = e^{βa²/2}(⌈ν⌉+i+p)!(4/β)^{⌈ν⌉+i+p}` monotone in `|a|`.
- `rpow_neg_mul_log_pow_isLittleO n (hL' : L' < L) : (N ↦ N^{-L}(1+log N)^n) =o[atTop] (N ↦ N^{-L'})`; `one_add_log_mul_le (1 ≤ N) (0 < c) : 1 + log(Nc) ≤ (1+|log c|)(1+log N)`.
- Mathlib: `TendstoInDistribution X l Z μ μ'` (structure: a.e.-measurability of `X i` and `Z`, weak convergence of the laws in `ProbabilityMeasure`); `TendstoInDistribution.continuous_comp` (continuous mapping); `tendstoInDistribution_of_tendstoInMeasure_sub (Y Z) (hXZ : X ⇒ Z) (hXY : TendstoInMeasure μ (Y − X) l 0) (hY : ∀ i, AEMeasurable (Y i)) : Y ⇒ Z` (Slutsky, needs `l.IsCountablyGenerated`); `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` (portmanteau); `TendstoInMeasure μ f l g ↔ ∀ ε > 0, Tendsto (μ {ε ≤ dist (f i ·) (g ·)}) l (𝓝 0)`.

## Statements

### Grammar/DataCutoff.lean

```lean
/-!
# The canonical cutoff theorem on the data space, uniform on balls (Stage S4)

Unit 273 (Astra #33 / review v27 should-fix 1 and 5a). The Taylor-tree cutoff theorem is restated
with the canonical coefficient map: for a data-space element `x` with `‖x‖ ≤ R`, every cutoff
`L > 0`, and `N > 0` with `N b^{2|k|} ≥ 1`,

`|Z(N; x) − ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} C_{μ,j}(x) (log N)^j|`
`  ≤ b^{|h|+d} · dataCutoffConst n k β L R · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^n`

(`dataTaylorTree_cutoff_bound`), where `Λ_L = latticeBelow (2∏kᵢ) L` is the finite candidate
lattice below `L`, `C_{μ,j} = dataBoxCoeff`, `Z = dataBoxIntegral`, and the constant
`dataCutoffConst n k β L R = cutoffBound n k β L R R R` depends on the data only through the ball
radius `R` (`cutoffBound_mono`: the uniform cutoff constant is monotone in `|ξ(0)|` and the two
masses). This is the deterministic input for the ordered normalised remainders of A2: on a data
ball the cutoff error is `O((N b^{2|k|})^{-L} (log N)^n)` uniformly.
-/

theorem on the data space, uniform on balls (Stage S4)

Unit 273 (Astra #33 / review v27 should-fix 1 and 5a). The Taylor-tree cutoff theorem is restated
with the canonical coefficient map: for a data-space element `x` with `‖x‖ ≤ R`, every cutoff
`L > 0`, and `N > 0` with `N b^{2|k|} ≥ 1`,

`|Z(N; x) − ∑_{μ ∈ Λ_L} N^{-μ} ∑_{j ≤ n} C_{μ,j}(x) (log N)^j|`
`  ≤ b^{|h|+d} · dataCutoffConst n k β L R · (N b^{2|k|})^{-L} (1 + log(N b^{2|k|}))^n`

(`dataTaylorTree_cutoff_bound`), where `Λ_L = latticeBelow (2∏kᵢ) L` is the finite candidate
lattice below `L`, `C_{μ,j} = dataBoxCoeff`, `Z = dataBoxIntegral`, and the constant
`dataCutoffConst n k β L R = cutoffBound n k β L R R R` depends on the data only through the ball
radius `R` (`cutoffBound_mono`: the uniform cutoff constant is monotone in `|ξ(0)|` and the two
masses). This is the deterministic input for the ordered normalised remainders of A2: on a data
ball the cutoff error is `O((N b^{2|k|})^{-L} (log N)^n)` uniformly.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The uniform cutoff constant is monotone in `|ξ(0)|` and the two masses. -/
theorem cutoffBound_mono (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ} (hL : 0 < L)
    {a E B a' E' B' : ℝ} (ha : |a| ≤ |a'|) (hE0 : 0 ≤ E) (hE : E ≤ E') (hB0 : 0 ≤ B)
    (hB : B ≤ B') :
    cutoffBound n k β L a E B ≤ cutoffBound n k β L a' E' B' := by
  unfold cutoffBound
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  have hD : (0 : ℝ) ≤ ((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n := by positivity
  have hab : |a| + B ≤ |a'| + B' := add_le_add ha hB
  have habs : |(|a| + B)| ≤ |(|a'| + B')| := by
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hB0),
      abs_of_nonneg (add_nonneg (abs_nonneg _) (hB0.trans hB))]
    exact hab
  have hM := phaseLogMoment_mono β hβ hab hL n 0
  have hT := tailConst_mono β hβ habs 0 L n
  have h4 : (0 : ℝ) ≤ 4 / β := by positivity
  have h5 : (0 : ℝ) ≤ (⌈L⌉₊.factorial : ℝ) * (4 / β) ^ ⌈L⌉₊ := by positivity
  have hM0 := phaseLogMoment_nonneg β (|a'| + B') L n 0
  have hT0 := tailConst_nonneg β (|a'| + B') hβ 0 L n
  refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hK) hD) ?_
    (add_nonneg (phaseLogMoment_nonneg _ _ _ _ _)
      (mul_nonneg (mul_nonneg (tailConst_nonneg β _ hβ 0 L n) h4) h5))
    (mul_nonneg (mul_nonneg hK (hE0.trans hE)) hD)
  exact add_le_add hM (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT h4) h5)

/-- The cutoff constant on the data ball of radius `R`. -/
noncomputable def dataCutoffConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β L R : ℝ) : ℝ :=
  cutoffBound n k β L R R R

theorem dataCutoffConst_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) (L : ℝ)
    {R : ℝ} (hR : 0 ≤ R) : 0 ≤ dataCutoffConst n k β L R :=
  cutoffBound_nonneg n k β hβ L R hR R

/-- The cutoff constant of a data-space element is at most the ball constant. -/
theorem cutoffBound_data_le (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {L : ℝ}
    (hL : 0 < L) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) :
    cutoffBound n k β L (constPhase x) (mass (etaCoord x)) (mass (xiCoord x)) ≤
      dataCutoffConst n k β L R := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  unfold dataCutoffConst
  refine cutoffBound_mono n k β hβ hL ?_ (mass_nonneg _) ((mass_etaCoord_le x).trans hx)
    (mass_nonneg _) ((mass_xiCoord_le x).trans hx)
  rw [abs_of_nonneg hR0]
  exact (abs_coord_sub_le x 0 (Sum.inl 0)).trans_eq' (by simp [constPhase]) |>.trans
    (by simpa using hx)

/-- **The canonical cutoff theorem on the data space, uniform on balls.** -/
theorem dataTaylorTree_cutoff_bound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {L b : ℝ} (hL : 0 < L) (hb : 0 < b) {N : ℝ} (hN : 0 < N)
    (hN' : 1 ≤ boxScale k b N) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) :
    |dataBoxIntegral n h k β N b x - ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b x μ j * (Real.log N) ^ j| ≤
      b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β L R *
        (boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n) := by
  have hbox := boxTaylorTree_cutoff_bound n h k hk β hβ hL hb hN.le hN' (absSummableAt_toXi hb x)
    (absSummableAt_toEta hb x)
  rw [boxSpectralSum_eq n h k β L hb _ _ hN, scale_toXi hb.ne', scale_toEta hb.ne'] at hbox
  have hc : (xiCoord x) 0 = constPhase x := rfl
  rw [hc] at hbox
  refine hbox.trans ?_
  have hpos : 0 ≤ boxScale k b N ^ (-L) * (1 + Real.log (boxScale k b N)) ^ n := by
    have h1 : 0 ≤ Real.log (boxScale k b N) := Real.log_nonneg hN'
    have h2 : 0 ≤ boxScale k b N ^ (-L) := Real.rpow_nonneg (by linarith) _
    positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hb.le _)) hpos
  exact cutoffBound_data_le n k β hβ hL hx

end Grammar

```
### Grammar/DataIntegralContinuity.lean

```lean
/-!
# Continuity and measurability of the standard integral in the data (Stage S5)

Unit 274 (review v27 should-fix 3). For fixed sample size `N ≥ 0`, the original box integral
`Z(N; ·) = dataBoxIntegral n h k β N b` is Lipschitz on every ball of the data space
(`abs_dataBoxIntegral_sub_le`), hence continuous (`continuous_dataBoxIntegral`) and Borel
measurable (`measurable_dataBoxIntegral`). Ingredients: on the closed unit cube the evaluation
`u ↦ evalF c u` is continuous (Weierstrass M-test with majorant `|c_γ|`, `continuousOn_evalF`) and
linear in `c` (`evalF_sub`), so the unit-box integrand is continuous in `u`, integrable on the
unit box, bounded by `mass cη · e^{β√N mass cξ}`, and Lipschitz in the data with constant
`e^{β√N R}(1 + β√N R)` on the ball of radius `R`; the unit box has volume one. The box integral is
the rescaled unit-box integral (`familyPhaseIntegralBox_eq`, `scale_toXi`). Together with the
measurability of the coefficients (Headline XXXIV) this makes every normalised remainder of A2 a
random variable.
-/

/-- The evaluation of an absolutely summable family is continuous on the closed unit cube. -/
theorem continuousOn_evalF {c : CoeffFamily d} (hc : AbsSummable c) :
    ContinuousOn (evalF c) (closedCube d) := by
  unfold evalF
  refine continuousOn_tsum (fun γ => ?_) hc fun γ u hu => ?_
  · exact (continuous_const.mul (continuous_finsetProd _ fun i _ =>
      (continuous_apply i).pow _)).continuousOn
  · rw [Real.norm_eq_abs]; exact abs_term_le hu γ

theorem evalF_sub {c c' : CoeffFamily d} (hc : AbsSummable c) (hc' : AbsSummable c')
    {u : Fin d → ℝ} (hu : u ∈ closedCube d) : evalF (c - c') u = evalF c u - evalF c' u := by
  unfold evalF
  rw [← (summable_term hc hu).tsum_sub (summable_term hc' hu)]
  refine tsum_congr fun γ => ?_
  simp only [Pi.sub_apply]; ring

/-- The unit-box integrand of the standard integral. -/
noncomputable def boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (u : Fin (n + 1) → ℝ) : ℝ :=
  evalF cη u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * evalF cξ u)

theorem familyPhaseIntegral_eq_integral_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (cξ cη : CoeffFamily (n + 1)) :
    familyPhaseIntegral n h k β N cξ cη = ∫ u in unitBox (n + 1), boxIntegrand n h k β N cξ cη u :=
  rfl

theorem continuousOn_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    ContinuousOn (boxIntegrand n h k β N cξ cη) (closedCube (n + 1)) := by
  unfold boxIntegrand
  have hp : ∀ e : Fin (n + 1) → ℕ, Continuous fun u : Fin (n + 1) → ℝ => ∏ i, u i ^ e i :=
    fun e => continuous_finsetProd _ fun i _ => (continuous_apply i).pow _
  refine ((continuousOn_evalF hη).mul (hp h).continuousOn).mul
    (Real.continuous_exp.comp_continuousOn ?_)
  exact ((continuous_const.mul (hp _)).neg.continuousOn).add
    ((continuous_const.mul (continuous_const.mul (hp k))).continuousOn.mul (continuousOn_evalF hξ))

theorem integrableOn_boxIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) :
    IntegrableOn (boxIntegrand n h k β N cξ cη) (unitBox (n + 1)) :=
  ((continuousOn_boxIntegrand n h k β N hξ hη).integrableOn_compact
    (isCompact_closedCube _)).mono_set (unitBox_subset_closedCube _)

/-- On the unit box, `|Δ integrand| ≤ e^{β√N R} (mass Δη + R β √N mass Δξ)` for data of mass
`≤ R` (`β ≥ 0`, `N ≥ 0`). -/
theorem abs_boxIntegrand_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) {u : Fin (n + 1) → ℝ}
    (hu : u ∈ unitBox (n + 1)) :
    |boxIntegrand n h k β N cξ' cη' u - boxIntegrand n h k β N cξ cη u| ≤
      Real.exp (β * Real.sqrt N * R) *
        (mass (cη' - cη) + R * (β * Real.sqrt N) * mass (cξ' - cξ)) := by
  have hu' : u ∈ closedCube (n + 1) := unitBox_subset_closedCube _ hu
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  have hτ := prod_pow_mem_Icc (fun i => 2 * k i) hu
  have hh := prod_pow_mem_Icc h hu
  have hK := prod_pow_mem_Icc k hu
  set s : ℝ := β * (Real.sqrt N * ∏ i, u i ^ k i) with hs
  have hs0 : 0 ≤ s := by have := Real.sqrt_nonneg N; have := hK.1; positivity
  have hs1 : s ≤ β * Real.sqrt N := by
    rw [hs]
    have : Real.sqrt N * ∏ i, u i ^ k i ≤ Real.sqrt N * 1 :=
      mul_le_mul_of_nonneg_left hK.2 (Real.sqrt_nonneg N)
    nlinarith [Real.sqrt_nonneg N]
  set A : ℝ := -(β * N * ∏ i, u i ^ (2 * k i)) with hA
  have hA0 : A ≤ 0 := by
    rw [hA]
    have h0 := hτ.1
    have : 0 ≤ β * N * ∏ i, u i ^ (2 * k i) := by positivity
    linarith
  have heξ : |evalF cξ u| ≤ R := (abs_evalF_le hξ hu').trans hRξ
  have heξ' : |evalF cξ' u| ≤ R := (abs_evalF_le hξ' hu').trans hRξ'
  have heη : |evalF cη u| ≤ R := (abs_evalF_le hη hu').trans hRη
  have hexp_le : ∀ c : CoeffFamily (n + 1), AbsSummable c → mass c ≤ R →
      Real.exp (A + s * evalF c u) ≤ Real.exp (β * Real.sqrt N * R) := by
    intro c hc hcR
    refine Real.exp_le_exp.2 ?_
    have h1 : s * evalF c u ≤ s * R :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((abs_evalF_le hc hu').trans hcR)) hs0
    nlinarith
  -- the exponential difference
  have hexp_sub : |Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u)| ≤
      Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N) * |evalF cξ' u - evalF cξ u| := by
    -- `|e^x − e^y| ≤ e^{max x y} |x − y|` via the mean value theorem
    have key : ∀ x y : ℝ, x ≤ y → |Real.exp y - Real.exp x| ≤ Real.exp y * |y - x| := by
      intro x y hxy
      rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hxy)), abs_of_nonneg (sub_nonneg.2 hxy)]
      have := Real.add_one_le_exp (x - y)
      have hey : 0 < Real.exp y := Real.exp_pos y
      have hxy' : Real.exp x = Real.exp y * Real.exp (x - y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hxy']
      nlinarith [Real.exp_pos (x - y)]
    have hM : ∀ c : CoeffFamily (n + 1), AbsSummable c → mass c ≤ R →
        A + s * evalF c u ≤ β * Real.sqrt N * R := fun c hc hcR =>
      Real.exp_le_exp.1 (hexp_le c hc hcR)
    rcases le_total (A + s * evalF cξ u) (A + s * evalF cξ' u) with hle | hle
    · refine (key _ _ hle).trans ?_
      have h1 := hexp_le cξ' hξ' hRξ'
      have h2 : |A + s * evalF cξ' u - (A + s * evalF cξ u)| = s * |evalF cξ' u - evalF cξ u| := by
        rw [show A + s * evalF cξ' u - (A + s * evalF cξ u) = s * (evalF cξ' u - evalF cξ u) by
          ring, abs_mul, abs_of_nonneg hs0]
      rw [h2]
      have h3 : s * |evalF cξ' u - evalF cξ u| ≤ β * Real.sqrt N * |evalF cξ' u - evalF cξ u| :=
        mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      calc Real.exp (A + s * evalF cξ' u) * (s * |evalF cξ' u - evalF cξ u|)
          ≤ Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N * |evalF cξ' u - evalF cξ u|) :=
            mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
    · rw [abs_sub_comm]
      refine (key _ _ hle).trans ?_
      have h1 := hexp_le cξ hξ hRξ
      have h2 : |A + s * evalF cξ u - (A + s * evalF cξ' u)| = s * |evalF cξ' u - evalF cξ u| := by
        rw [show A + s * evalF cξ u - (A + s * evalF cξ' u) = s * (evalF cξ u - evalF cξ' u) by
          ring, abs_mul, abs_of_nonneg hs0, abs_sub_comm]
      rw [h2]
      have h3 : s * |evalF cξ' u - evalF cξ u| ≤ β * Real.sqrt N * |evalF cξ' u - evalF cξ u| :=
        mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      calc Real.exp (A + s * evalF cξ u) * (s * |evalF cξ' u - evalF cξ u|)
          ≤ Real.exp (β * Real.sqrt N * R) * (β * Real.sqrt N * |evalF cξ' u - evalF cξ u|) :=
            mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
  have hdξ : |evalF cξ' u - evalF cξ u| ≤ mass (cξ' - cξ) := by
    rw [← evalF_sub hξ' hξ hu']; exact abs_evalF_le (hξ'.sub hξ) hu'
  have hdη : |evalF cη' u - evalF cη u| ≤ mass (cη' - cη) := by
    rw [← evalF_sub hη' hη hu']; exact abs_evalF_le (hη'.sub hη) hu'
  -- assemble: F' G' − F G = (F' − F) G' + F (G' − G) with `F = evalF cη · u^h`, `G = exp(…)`
  unfold boxIntegrand
  have hmono : |∏ i, u i ^ h i| ≤ 1 := by rw [abs_of_nonneg hh.1]; exact hh.2
  set E := Real.exp (β * Real.sqrt N * R) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hG' : |Real.exp (A + s * evalF cξ' u)| ≤ E := by
    rw [abs_of_pos (Real.exp_pos _)]; exact hexp_le cξ' hξ' hRξ'
  have hsplit : evalF cη' u * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u) -
      evalF cη u * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ u) =
      (evalF cη' u - evalF cη u) * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u) +
        evalF cη u * (∏ i, u i ^ h i) *
          (Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(evalF cη' u - evalF cη u) * (∏ i, u i ^ h i) * Real.exp (A + s * evalF cξ' u)| ≤
      mass (cη' - cη) * E := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul (mul_le_mul hdη hmono (abs_nonneg _) (mass_nonneg _)) hG' (abs_nonneg _)
      (mul_nonneg (mass_nonneg _) zero_le_one)
    simpa using this
  have h2 : |evalF cη u * (∏ i, u i ^ h i) *
      (Real.exp (A + s * evalF cξ' u) - Real.exp (A + s * evalF cξ u))| ≤
      R * 1 * (E * (β * Real.sqrt N) * mass (cξ' - cξ)) := by
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul heη hmono (abs_nonneg _) hR0) (hexp_sub.trans ?_)
      (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hdξ (by positivity)
  calc _ ≤ mass (cη' - cη) * E + R * 1 * (E * (β * Real.sqrt N) * mass (cξ' - cξ)) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **Lipschitz continuity of the unit-box family integral in the data**, on data balls. -/
theorem abs_familyPhaseIntegral_coord_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N : ℝ}
    (hβ : 0 ≤ β) (hN : 0 ≤ N) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |familyPhaseIntegral n h k β N (xiCoord y) (etaCoord y) -
        familyPhaseIntegral n h k β N (xiCoord x) (etaCoord x)| ≤
      Real.exp (β * Real.sqrt N * R) * (1 + R * (β * Real.sqrt N)) * ‖y - x‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  rw [familyPhaseIntegral_eq_integral_boxIntegrand, familyPhaseIntegral_eq_integral_boxIntegrand,
    ← integral_sub (integrableOn_boxIntegrand n h k β N (absSummable_xiCoord y)
      (absSummable_etaCoord y)) (integrableOn_boxIntegrand n h k β N (absSummable_xiCoord x)
      (absSummable_etaCoord x))]
  have hvol : volume (unitBox (n + 1)) < ⊤ := by rw [volume_unitBox]; exact ENNReal.one_lt_top
  have hbound : ∀ u ∈ unitBox (n + 1),
      ‖boxIntegrand n h k β N (xiCoord y) (etaCoord y) u -
        boxIntegrand n h k β N (xiCoord x) (etaCoord x) u‖ ≤
      Real.exp (β * Real.sqrt N * R) * (1 + R * (β * Real.sqrt N)) * ‖y - x‖ := by
    intro u hu
    rw [Real.norm_eq_abs]
    refine (abs_boxIntegrand_sub_le n h k hβ hN (absSummable_xiCoord x) (absSummable_xiCoord y)
      (absSummable_etaCoord x) (absSummable_etaCoord y) ((mass_xiCoord_le x).trans hx)
      ((mass_xiCoord_le y).trans hy) ((mass_etaCoord_le x).trans hx) hu).trans ?_
    have h1 : mass (xiCoord y - xiCoord x) ≤ ‖y - x‖ := by
      have := mass_xiCoord_sub_le y x; simpa [Pi.sub_def] using this
    have h2 : mass (etaCoord y - etaCoord x) ≤ ‖y - x‖ := by
      have := mass_etaCoord_sub_le y x; simpa [Pi.sub_def] using this
    have hE0 : 0 ≤ Real.exp (β * Real.sqrt N * R) := (Real.exp_pos _).le
    have hc : 0 ≤ R * (β * Real.sqrt N) := by have := Real.sqrt_nonneg N; positivity
    calc Real.exp (β * Real.sqrt N * R) *
          (mass (etaCoord y - etaCoord x) + R * (β * Real.sqrt N) * mass (xiCoord y - xiCoord x))
        ≤ Real.exp (β * Real.sqrt N * R) * (‖y - x‖ + R * (β * Real.sqrt N) * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 (mul_le_mul_of_nonneg_left h1 hc)) hE0
      _ = _ := by ring
  have := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [Real.norm_eq_abs] at this
  simpa [MeasureTheory.measureReal_def, volume_unitBox] using this

/-- The box integral is the rescaled unit-box integral of the raw coordinates. -/
theorem dataBoxIntegral_eq (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N b : ℝ} (hN : 0 ≤ N)
    (hb : 0 < b) (x : DataSpace (n + 1)) :
    dataBoxIntegral n h k β N b x = b ^ (∑ i, h i + (n + 1)) *
      familyPhaseIntegral n h k β (boxScale k b N) (xiCoord x) (etaCoord x) := by
  unfold dataBoxIntegral
  rw [familyPhaseIntegralBox_eq n h k β hN hb, scale_toXi hb.ne', scale_toEta hb.ne']
  rfl

/-- **Lipschitz continuity of the standard integral in the data**, on data balls (fixed
`N ≥ 0`). -/
theorem abs_dataBoxIntegral_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |dataBoxIntegral n h k β N b y - dataBoxIntegral n h k β N b x| ≤
      b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
        (1 + R * (β * Real.sqrt (boxScale k b N)))) * ‖y - x‖ := by
  rw [dataBoxIntegral_eq n h k β hN hb, dataBoxIntegral_eq n h k β hN hb, ← mul_sub, abs_mul,
    abs_of_nonneg (pow_nonneg hb.le _), mul_assoc]
  have hN' : 0 ≤ boxScale k b N := by unfold boxScale; positivity
  exact mul_le_mul_of_nonneg_left (abs_familyPhaseIntegral_coord_sub_le n h k hβ hN' hx hy)
    (pow_nonneg hb.le _)

/-- **The standard integral is continuous in the data** (fixed `N ≥ 0`). -/
theorem continuous_dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Continuous fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R := ‖x‖ + 1 with hR
  have hmem : Metric.closedBall (0 : DataSpace (n + 1)) R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp [hR])
  set C := b ^ (∑ i, h i + (n + 1)) * (Real.exp (β * Real.sqrt (boxScale k b N) * R) *
    (1 + R * (β * Real.sqrt (boxScale k b N)))) with hC
  have hC0 : 0 ≤ C := by
    have := Real.sqrt_nonneg (boxScale k b N)
    have := Real.exp_pos (β * Real.sqrt (boxScale k b N) * R)
    have : 0 ≤ R := by rw [hR]; positivity
    positivity
  have hlip : LipschitzOnWith (Real.toNNReal C)
      (fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x) (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' : ‖y‖ ≤ R := by simpa using hy
    have hz' : ‖z‖ ≤ R := by simpa using hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC0]
    exact abs_dataBoxIntegral_sub_le n h k hβ hN hb hz' hy'
  exact hlip.continuousOn.continuousAt hmem

theorem measurable_dataBoxIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) {β N b : ℝ} (hβ : 0 ≤ β)
    (hN : 0 ≤ N) (hb : 0 < b) :
    Measurable fun x : DataSpace (n + 1) => dataBoxIntegral n h k β N b x :=
  (continuous_dataBoxIntegral n h k hβ hN hb).measurable

end Grammar

```
### Grammar/OrderedRemainder.lean

```lean
/-!
# Ordered normalised remainders, uniformly on data balls (Stage S6 — the deterministic core of A2)

Unit 275 (review v27 should-fix 4–5). Order the index pairs `(ν, q)` of the Taylor-tree expansion
by `(ν, q) ≺ (μ, j) ↔ ν < μ ∨ (ν = μ ∧ j < q)` — smaller exponent first, and at equal exponent the
**larger** log power first (`precedes`). For a target `(μ, j)` with `μ` on the exponent lattice
`Q⁻¹ℕ` (`Q = 2∏kᵢ`) and `j ≤ n`, the predecessors form the finite set `predSet` and the **ordered
normalised remainder** is

`R_N^{μ,j}(x) = (Z(N; x) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(x) N^{-ν} (log N)^q) / (N^{-μ} (log N)^j)`

(`orderedRemainder`). **Theorem** (`tendstoUniformlyOn_orderedRemainder`): on every data ball
`‖x‖ ≤ R`, `R_N^{μ,j}(x) → C_{μ,j}(x)` uniformly as `N → ∞`. Proof: with the cutoff `L = μ + 1`,
`Z − ∑_{≺} − C_{μ,j} N^{-μ}(log N)^j` is the cutoff error plus the finitely many retained terms
with `ν > μ` or `(ν = μ, q < j)`; after division by `N^{-μ}(log N)^j` the cutoff error is
`O(N^{-(L-μ)} (1 + log N)^n)` (`dataTaylorTree_cutoff_bound`, uniform on the ball), the
terms with `ν > μ` are `O(N^{-(ν-μ)} (1 + log N)^n)`, and the terms with `ν = μ, q < j` are
`O(1/log N)`, all with constants uniform on the ball (the coefficients are bounded on the ball by
Headline XXXIV). Thresholds: `N ≥ e` and `N b^{2|k|} ≥ 1`. This is the deterministic input for the
convergence in distribution of the remainders (A2); no probability enters here.
-/

/-- The asymptotic ordering: `(ν, q) ≺ (μ, j)` iff `ν < μ`, or `ν = μ` and `q > j`. -/
def precedes (p q : ℝ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)

theorem precedes_irrefl (p : ℝ × ℕ) : ¬ precedes p p := by
  unfold precedes; simp

/-- The finite index set of the truncation below `L`: `Λ_L × {0, …, n}`. -/
noncomputable def indexSet (n Q : ℕ) (L : ℝ) : Finset (ℝ × ℕ) :=
  latticeBelow Q L ×ˢ Finset.range (n + 1)

open scoped Classical in
/-- The predecessors of the target `(μ, j)`. -/
noncomputable def predSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) :=
  (indexSet n Q (μ + 1)).filter fun p => precedes p (μ, j)

/-- One term `C_{ν,q}(x) N^{-ν} (log N)^q` of the expansion. -/
noncomputable def expTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1))
    (N : ℝ) (p : ℝ × ℕ) : ℝ :=
  dataBoxCoeff n h k β b x p.1 p.2 * (N ^ (-p.1) * Real.log N ^ p.2)

/-- The sum of the predecessor terms. -/
noncomputable def predSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) (x : DataSpace (n + 1))
    (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  ∑ p ∈ predSet n (latticeQ k) μ j, expTerm n h k β b x N p

/-- **The ordered normalised remainder** at the target `(μ, j)`. -/
noncomputable def orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (μ : ℝ) (j : ℕ) (N : ℝ) : ℝ :=
  (dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N) / (N ^ (-μ) * Real.log N ^ j)

/-- The spectral sum as a sum over the index set. -/
theorem spectralSum_eq_sum_indexSet (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ)
    (x : DataSpace (n + 1)) (L N : ℝ) :
    ∑ μ ∈ latticeBelow (latticeQ k) L, N ^ (-μ) *
        ∑ j ∈ Finset.range (n + 1), dataBoxCoeff n h k β b x μ j * Real.log N ^ j =
      ∑ p ∈ indexSet n (latticeQ k) L, expTerm n h k β b x N p := by
  unfold indexSet expTerm
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A uniform bound for a coefficient on the data ball of radius `R`. -/
noncomputable def coeffBallBound (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) :
    ℝ :=
  |dataBoxCoeff n h k β b 0 μ j| + dataLipConst n h k β b μ j R * R

theorem abs_dataBoxCoeff_le_ballBound (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) {R : ℝ} {x : DataSpace (n + 1)}
    (hx : ‖x‖ ≤ R) : |dataBoxCoeff n h k β b x μ j| ≤ coeffBallBound n h k β b μ j R := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have h0 : ‖(0 : DataSpace (n + 1))‖ ≤ R := by simpa using hR0
  have := abs_dataBoxCoeff_sub_le n h k hk β hβ hb h0 hx μ j
  rw [sub_zero] at this
  unfold coeffBallBound
  have hL := dataLipConst_nonneg n h k β hβ hb μ j hR0
  calc |dataBoxCoeff n h k β b x μ j|
      ≤ |dataBoxCoeff n h k β b 0 μ j| +
          |dataBoxCoeff n h k β b x μ j - dataBoxCoeff n h k β b 0 μ j| := by
        have := abs_sub_abs_le_abs_sub (dataBoxCoeff n h k β b x μ j) (dataBoxCoeff n h k β b 0 μ j)
        linarith
    _ ≤ _ := add_le_add le_rfl (this.trans (mul_le_mul_of_nonneg_left hx hL))

/-! ### Scalar asymptotics -/

/-- `N^{-s} (1 + log N)^n → 0` for `s > 0`. -/
theorem tendsto_rpow_neg_mul_one_add_log_pow (n : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℝ => N ^ (-s) * (1 + Real.log N) ^ n) atTop (𝓝 0) := by
  have h := (rpow_neg_mul_log_pow_isLittleO n (L := s) (L' := 0) hs).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  rw [neg_zero, Real.rpow_zero, div_one]

/-- `N^{-L} (1 + log N)^n / N^{-μ} → 0` for `μ < L`. -/
theorem tendsto_cutoff_ratio (n : ℕ) {L μ : ℝ} (hμL : μ < L) :
    Tendsto (fun N : ℝ => N ^ (-L) * (1 + Real.log N) ^ n / N ^ (-μ)) atTop (𝓝 0) :=
  (rpow_neg_mul_log_pow_isLittleO n hμL).tendsto_div_nhds_zero

/-- `1 / log N → 0`. -/
theorem tendsto_inv_log : Tendsto (fun N : ℝ => (Real.log N)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop

/-- The majorant of a retained term `(ν, q)` after normalisation at `(μ, j)`. -/
noncomputable def termMajorant (n : ℕ) (μ : ℝ) (p : ℝ × ℕ) (N : ℝ) : ℝ :=
  if p.1 = μ then (Real.log N)⁻¹ else N ^ (-(p.1 - μ)) * (1 + Real.log N) ^ n

theorem tendsto_termMajorant (n : ℕ) {μ : ℝ} {p : ℝ × ℕ} (hp : μ ≤ p.1) :
    Tendsto (termMajorant n μ p) atTop (𝓝 0) := by
  unfold termMajorant
  split_ifs with h
  · exact tendsto_inv_log
  · exact tendsto_rpow_neg_mul_one_add_log_pow n (by
      rcases lt_or_eq_of_le hp with h' | h'
      · linarith
      · exact absurd h'.symm h)

/-- The normalised retained term is at most its majorant times the ball bound (for `N ≥ e`). -/
theorem abs_expTerm_div_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) {μ : ℝ}
    {j : ℕ} {p : ℝ × ℕ} (hp : μ ≤ p.1) (hpq : p.1 = μ → p.2 < j) (hpn : p.2 ≤ n) {N : ℝ}
    (hN : Real.exp 1 ≤ N) :
    |expTerm n h k β b x N p / (N ^ (-μ) * Real.log N ^ j)| ≤
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N := by
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hN
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hN
  have hlog0 : 0 < Real.log N := by linarith
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hC := abs_dataBoxCoeff_le_ballBound n h k hk β hβ hb p.1 p.2 hx
  have hC0 : 0 ≤ |dataBoxCoeff n h k β b x p.1 p.2| := abs_nonneg _
  unfold expTerm termMajorant
  rw [abs_div, abs_of_pos hD, abs_mul, div_le_iff₀ hD]
  have hpow : 0 < N ^ (-p.1) * Real.log N ^ p.2 := by positivity
  rw [abs_of_pos hpow]
  split_ifs with heq
  · -- equal exponent, lower log power: `(log N)^q ≤ (log N)^j / log N`
    have hq : p.2 + 1 ≤ j := hpq heq
    rw [heq] at hpow hC hC0 ⊢
    have h1 : Real.log N ^ p.2 * Real.log N ≤ Real.log N ^ j := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hlog1 hq
    calc |dataBoxCoeff n h k β b x μ p.2| * (N ^ (-μ) * Real.log N ^ p.2)
        ≤ coeffBallBound n h k β b μ p.2 R * (N ^ (-μ) * Real.log N ^ p.2) :=
          mul_le_mul_of_nonneg_right hC hpow.le
      _ = coeffBallBound n h k β b μ p.2 R * (Real.log N)⁻¹ *
            (N ^ (-μ) * (Real.log N ^ p.2 * Real.log N)) := by
          field_simp
      _ ≤ coeffBallBound n h k β b μ p.2 R * (Real.log N)⁻¹ * (N ^ (-μ) * Real.log N ^ j) := by
          have hB : 0 ≤ coeffBallBound n h k β b μ p.2 R := hC0.trans hC
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB (inv_nonneg.2 hlog0.le))
          exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hN0.le _)
  · -- larger exponent: `N^{-ν} (log N)^q ≤ N^{-(ν-μ)} (1+log N)^n · N^{-μ} (log N)^j`
    have h1 : Real.log N ^ p.2 ≤ (1 + Real.log N) ^ n := by
      calc Real.log N ^ p.2 ≤ (1 + Real.log N) ^ p.2 :=
            pow_le_pow_left₀ hlog0.le (by linarith) _
        _ ≤ (1 + Real.log N) ^ n := pow_le_pow_right₀ (by linarith) hpn
    have h2 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have h3 : N ^ (-p.1) = N ^ (-(p.1 - μ)) * N ^ (-μ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hB : 0 ≤ coeffBallBound n h k β b p.1 p.2 R := hC0.trans hC
    have hr : 0 ≤ N ^ (-(p.1 - μ)) := Real.rpow_nonneg hN0.le _
    calc |dataBoxCoeff n h k β b x p.1 p.2| * (N ^ (-p.1) * Real.log N ^ p.2)
        ≤ coeffBallBound n h k β b p.1 p.2 R * (N ^ (-p.1) * Real.log N ^ p.2) :=
          mul_le_mul_of_nonneg_right hC hpow.le
      _ = coeffBallBound n h k β b p.1 p.2 R * (N ^ (-(p.1 - μ)) * Real.log N ^ p.2) *
            (N ^ (-μ) * 1) := by rw [h3]; ring
      _ ≤ coeffBallBound n h k β b p.1 p.2 R * (N ^ (-(p.1 - μ)) * (1 + Real.log N) ^ n) *
            (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hr) hB)
            (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)) (by positivity)
            (mul_nonneg hB (mul_nonneg hr (by positivity)))

/-- The retained terms other than the predecessors and the target. -/
noncomputable def restSet (n Q : ℕ) (μ : ℝ) (j : ℕ) : Finset (ℝ × ℕ) :=
  indexSet n Q (μ + 1) \ (predSet n Q μ j ∪ {(μ, j)})

theorem mem_restSet {n Q : ℕ} {μ : ℝ} {j : ℕ} {p : ℝ × ℕ} (hp : p ∈ restSet n Q μ j) :
    p ∈ indexSet n Q (μ + 1) ∧ μ ≤ p.1 ∧ (p.1 = μ → p.2 < j) := by
  unfold restSet predSet at hp
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hp
  obtain ⟨hi, hnot⟩ := hp
  refine ⟨hi, ?_, ?_⟩
  · by_contra hlt
    exact hnot (Or.inl ⟨hi, Or.inl (lt_of_not_ge hlt)⟩)
  · intro heq
    by_contra hge
    rcases lt_or_eq_of_le (le_of_not_gt hge) with hlt | heq2
    · exact hnot (Or.inl ⟨hi, Or.inr ⟨heq, hlt⟩⟩)
    · exact hnot (Or.inr (Prod.ext heq heq2.symm))

theorem mem_indexSet_snd_le {n Q : ℕ} {L : ℝ} {p : ℝ × ℕ} (hp : p ∈ indexSet n Q L) : p.2 ≤ n := by
  unfold indexSet at hp
  rw [Finset.mem_product] at hp
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hp.2)

/-- The uniform majorant of `|R_N^{μ,j}(x) − C_{μ,j}(x)|` on the ball of radius `R`. -/
noncomputable def remainderMajorant (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ)
    (N : ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
      ((b ^ (2 * ∑ i, k i)) ^ (-(μ + 1)) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n) *
      (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) +
    ∑ p ∈ restSet n (latticeQ k) μ j,
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N

theorem tendsto_remainderMajorant (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) :
    Tendsto (remainderMajorant n h k β b μ j R) atTop (𝓝 0) := by
  unfold remainderMajorant
  have h1 := (tendsto_cutoff_ratio n (L := μ + 1) (μ := μ) (by linarith)).const_mul
    (b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
      ((b ^ (2 * ∑ i, k i)) ^ (-(μ + 1)) * (1 + |Real.log (b ^ (2 * ∑ i, k i))|) ^ n))
  rw [mul_zero] at h1
  have h2 : Tendsto (fun N => ∑ p ∈ restSet n (latticeQ k) μ j,
      coeffBallBound n h k β b p.1 p.2 R * termMajorant n μ p N) atTop (𝓝 0) := by
    have := tendsto_finset_sum (restSet n (latticeQ k) μ j) fun p hp =>
      (tendsto_termMajorant n (mem_restSet hp).2.1).const_mul (coeffBallBound n h k β b p.1 p.2 R)
    simpa using this
  simpa using h1.add h2

/-- **Ordered normalised remainders converge uniformly on data balls**: for a target `(μ, j)` with
`μ ∈ Q⁻¹ℕ` and `j ≤ n`, `R_N^{μ,j}(x) → C_{μ,j}(x)` uniformly in `‖x‖ ≤ R` as `N → ∞`. -/
theorem tendstoUniformlyOn_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => orderedRemainder n h k β b x μ j N)
      (fun x => dataBoxCoeff n h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨m, hm⟩ := hμ
  have hμ0 : 0 ≤ μ := by rw [hm]; positivity
  set Q := latticeQ k with hQdef
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  -- the target lies in the index set of the cutoff `μ + 1`
  have htarget : (μ, j) ∈ indexSet n Q (μ + 1) := by
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.lt_succ_of_le hj)⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; linarith)
  have hpred_sub : predSet n Q μ j ⊆ indexSet n Q (μ + 1) := Finset.filter_subset _ _
  have htarget_notin : (μ, j) ∉ predSet n Q μ j := by
    unfold predSet
    rw [Finset.mem_filter]
    exact fun hcontra => precedes_irrefl _ hcontra.2
  have hsub : predSet n Q μ j ∪ {(μ, j)} ⊆ indexSet n Q (μ + 1) :=
    Finset.union_subset hpred_sub (Finset.singleton_subset_iff.2 htarget)
  -- the key algebraic decomposition
  have hdecomp : ∀ (x : DataSpace (n + 1)) (N : ℝ),
      dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
          dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j) =
        (dataBoxIntegral n h k β N b x -
          ∑ p ∈ indexSet n Q (μ + 1), expTerm n h k β b x N p) +
        ∑ p ∈ restSet n Q μ j, expTerm n h k β b x N p := by
    intro x N
    unfold restSet predSum
    rw [← Finset.sum_sdiff hsub, Finset.sum_union (Finset.disjoint_singleton_right.2 htarget_notin),
      Finset.sum_singleton]
    unfold expTerm
    ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := tendsto_remainderMajorant n h k β b μ j R
  have hev : ∀ᶠ N in atTop, remainderMajorant n h k β b μ j R N < ε :=
    hmaj.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 / c)] with N hNε hNe
    hNc x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  rw [Real.dist_eq]
  -- `C − R_N = −(Z − pred − C D)/D`
  have hRN : dataBoxCoeff n h k β b x μ j - orderedRemainder n h k β b x μ j N =
      -((dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
        dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j)) /
          (N ^ (-μ) * Real.log N ^ j)) := by
    unfold orderedRemainder
    have hD' := hD.ne'
    field_simp
    ring
  rw [hRN, abs_neg, hdecomp, add_div, Finset.sum_div]
  refine lt_of_le_of_lt ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hNε
  · -- the cutoff error
    have hcut := dataTaylorTree_cutoff_bound n h k hk β hβ (L := μ + 1) (by linarith) hb hN0 hscale
      hx'
    rw [spectralSum_eq_sum_indexSet] at hcut
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    refine hcut.trans ?_
    -- `(Nc)^{-L}(1+log(Nc))^n ≤ c^{-L}(1+|log c|)^n N^{-L}(1+log N)^n` and `(log N)^j ≥ 1`
    have hK0 : 0 ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R :=
      mul_nonneg (by positivity) (dataCutoffConst_nonneg n k β hβ _ ((norm_nonneg x).trans hx'))
    have hbs : boxScale k b N = N * c := by unfold boxScale; rw [hc]
    have h1 : boxScale k b N ^ (-(μ + 1)) = N ^ (-(μ + 1)) * c ^ (-(μ + 1)) := by
      rw [hbs, Real.mul_rpow hN0.le hc0.le]
    have h2 : (1 + Real.log (boxScale k b N)) ^ n ≤
        (1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n := by
      rw [hbs, ← mul_pow]
      exact pow_le_pow_left₀ (by have := Real.log_nonneg (show 1 ≤ N * c by rwa [← hbs]); linarith)
        (one_add_log_mul_le hN1.le hc0) n
    have h3 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hr0 : 0 ≤ N ^ (-(μ + 1)) := Real.rpow_nonneg hN0.le _
    have hcr0 : 0 ≤ c ^ (-(μ + 1)) := Real.rpow_nonneg hc0.le _
    have hlogN : 0 ≤ 1 + Real.log N := by linarith
    calc b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (boxScale k b N ^ (-(μ + 1)) * (1 + Real.log (boxScale k b N)) ^ n)
        ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (N ^ (-(μ + 1)) * c ^ (-(μ + 1)) * ((1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n)) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hcr0)) hK0
      _ = b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * 1) := by
          field_simp
      _ ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3
            (Real.rpow_nonneg hN0.le _)) ?_
          have : 0 ≤ N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ) := by positivity
          exact mul_nonneg (mul_nonneg hK0 (mul_nonneg hcr0 (by positivity))) this
  · -- the retained terms
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨hpi, hpμ, hpq⟩ := mem_restSet hp
    exact abs_expTerm_div_le n h k hk β hβ hb hx' hpμ hpq (mem_indexSet_snd_le hpi) hNe

end Grammar

```
### Grammar/StochasticTaylorTree.lean

```lean
/-!
# The stochastic Taylor tree, one chart, every positive dimension (Stage S7 — Headline XXXV)

Unit 276 (Astra #33 A2). Let `X_n : Ω → DataSpace (n+1)` be measurable random Taylor data
(phase and amplitude, weighted-ℓ¹ at the box radius `b`) converging in distribution to `Z`, and
let `N_n → ∞` be sample sizes. Then

* **coefficients**: every finite vector of canonical coefficients converges in distribution,
  `(C_{μ_i,j_i}(X_n))_i ⇒ (C_{μ_i,j_i}(Z))_i` (`tendstoInDistribution_dataCoeffVec`; continuous
  mapping with Headline XXXIV);
* **ordered normalised remainders**: for every target `(μ, j)` with `μ ∈ Q⁻¹ℕ`, `j ≤ n`,
  `R_{N_n}^{μ,j}(X_n) − C_{μ,j}(X_n) → 0` in probability (`tendstoInMeasure_orderedRemainder_sub`)
  and hence `R_{N_n}^{μ,j}(X_n) ⇒ C_{μ,j}(Z)` (`tendstoInDistribution_orderedRemainder`,
  **Headline XXXV**): the uniform-on-balls convergence of unit 275, the boundedness in
  probability of `‖X_n‖` (portmanteau on the closed sets `{‖·‖ ≥ m}`,
  `dataNormBounded_of_tendstoInDistribution`), and Slutsky's lemma
  (`tendstoInDistribution_of_tendstoInMeasure_sub`).

This is `thm:strataempiricalexpansion` at chart level in arbitrary normal dimension, conditional
on convergence in distribution of the weighted Taylor data. Non-claims: no derivation from
Hypothesis I (resolution, empirical-process convergence and the standard-form identity are
external); the data are `E_b`-valued by hypothesis (no common analytic radius is manufactured);
the limit need not be Gaussian; `N` is the paper's sample size; sample sizes are taken `≥ 0`.
-/

/-- The tail probabilities of the norm of a random data element tend to zero. -/
theorem tendsto_measure_dataNorm_ge_atTop (Z : Ω' → DataSpace d) (hZ : AEMeasurable Z μ') :
    Tendsto (fun m : ℕ => μ' ((fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ))) atTop (𝓝 0) := by
  have hnull : ∀ m : ℕ, NullMeasurableSet ((fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ)) μ' :=
    fun m => hZ.norm.nullMeasurableSet_preimage measurableSet_Ici
  have hanti : Antitone fun m : ℕ => (fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ) := by
    intro m m' hmm' ω hω
    simp only [mem_preimage, mem_Ici] at hω ⊢
    exact le_trans (by exact_mod_cast hmm') hω
  have h := tendsto_measure_iInter_atTop (μ := μ') hnull hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ m : ℕ, (fun ω => ‖Z ω‖) ⁻¹' Ici (m : ℝ)) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_nat_gt _
  rw [hempty, measure_empty] at h
  exact h

/-- **Norm-boundedness in probability** of random data converging in distribution. -/
theorem dataNormBounded_of_tendstoInDistribution (X : ι → Ω → DataSpace d) (Z : Ω' → DataSpace d)
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η := by
  intro η hη
  by_cases hηtop : η = ⊤
  · exact ⟨0, le_rfl, Eventually.of_forall fun n => by rw [hηtop]; exact le_top⟩
  have hZ : AEMeasurable Z μ' := hX.aemeasurable_limit
  have hhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨m, hm⟩ :=
    ((tendsto_measure_dataNorm_ge_atTop Z hZ).eventually (gt_mem_nhds hhalf)).exists
  set F : Set (DataSpace d) := {a | (m : ℝ) ≤ ‖a‖} with hFdef
  have hF : IsClosed F := isClosed_le continuous_const continuous_norm
  have hFm : MeasurableSet F := hF.measurableSet
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hX.tendsto hF
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hmap : ∀ n, (μ.map (X n)) F = μ (X n ⁻¹' F) := fun n =>
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hFm
  simp only [hmap, Measure.map_apply_of_aemeasurable hZ hFm] at hport
  have hZF : μ' (Z ⁻¹' F) < η / 2 := hm
  have hlt : limsup (fun n => μ (X n ⁻¹' F)) l < η :=
    lt_of_le_of_lt hport (lt_of_lt_of_le hZF ENNReal.half_le_self)
  refine ⟨m, Nat.cast_nonneg m, (eventually_lt_of_limsup_lt hlt).mono fun n hn => ?_⟩
  refine le_trans (measure_mono ?_) hn.le
  intro ω hω
  exact le_of_lt (show (m : ℝ) < ‖X n ω‖ from hω)

/-- **Uniform smallness on balls plus norm-boundedness in probability gives convergence in
probability to zero.** -/
theorem tendstoInMeasure_zero_of_uniform_on_balls (f : ι → Ω → ℝ) (X : ι → Ω → DataSpace d)
    (hf : ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ ω, ‖X n ω‖ ≤ M → |f n ω| ≤ ε)
    (htight : ∀ η : ENNReal, 0 < η → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, μ {ω | M < ‖X n ω‖} ≤ η) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hev⟩ := htight η hη
  filter_upwards [hev, hf M hM (ε / 2) (half_pos hε)] with n hn hfn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  simp only [mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra hcon
  have := hfn ω (not_lt.1 hcon)
  linarith

end NormBounded

/-- **Headline XXXV (coefficients)**: finite vectors of canonical coefficients converge in
distribution when the data do. -/
theorem tendstoInDistribution_dataCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ)
    (X : ι → Ω → DataSpace (n + 1)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i => dataCoeffVec n h k β b F ∘ X i) l
      (dataCoeffVec n h k β b F ∘ Z) (fun _ => μ) μ' :=
  hX.continuous_comp (continuous_taylorTree_coeffVec n h k hk β hβ hb F)

/-- A single canonical coefficient converges in distribution. -/
theorem tendstoInDistribution_dataBoxCoeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ) (X : ι → Ω → DataSpace (n + 1))
    (Z : Ω' → DataSpace (n + 1)) (hX : TendstoInDistribution X l Z (fun _ => μ) μ') :
    TendstoInDistribution (fun i ω => dataBoxCoeff n h k β b (X i ω) μ₀ j) l
      (fun ω => dataBoxCoeff n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' :=
  hX.continuous_comp (g := fun x => dataBoxCoeff n h k β b x μ₀ j)
    (continuous_taylorTree_coeff n h k hk β hβ hb μ₀ j)

/-- The ordered remainder is a measurable function of the data (`N ≥ 0`). -/
theorem measurable_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ₀ : ℝ) (j : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    Measurable fun x : DataSpace (n + 1) => orderedRemainder n h k β b x μ₀ j N := by
  unfold orderedRemainder predSum expTerm
  refine Measurable.div_const (Measurable.sub (measurable_dataBoxIntegral n h k hβ.le hN hb) ?_) _
  exact Finset.measurable_sum _ fun p _ =>
    (measurable_taylorTree_coeff n h k hk β hβ hb p.1 p.2).mul_const _

/-- **The remainder minus the coefficient tends to zero in probability.** -/
theorem tendstoInMeasure_orderedRemainder_sub (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ)
    (hN : Tendsto Nseq l atTop) :
    TendstoInMeasure μ (fun i ω => orderedRemainder n h k β b (X i ω) μ₀ j (Nseq i) -
      dataBoxCoeff n h k β b (X i ω) μ₀ j) l (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_uniform_on_balls _ X (fun M hM ε hε => ?_)
    (dataNormBounded_of_tendstoInDistribution X Z hX)
  have hu := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_orderedRemainder n h k hk β hβ hb hμ hj M) ε hε
  filter_upwards [hN.eventually hu] with i hi ω hω
  have := hi (X i ω) (by simpa using hω)
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this.le

variable [l.IsCountablyGenerated]

/-- **Headline XXXV — the stochastic Taylor tree, one chart, every positive dimension.** If the
random weighted Taylor data `X_n ⇒ Z` in `E_b × E_b` and `N_n → ∞` (`N_n ≥ 0`), then for every
target `(μ, j)` with `μ ∈ Q⁻¹ℕ` and `j ≤ n` the ordered normalised remainder converges in
distribution to the limiting coefficient:
`(Z(N_n; X_n) − ∑_{(ν,q) ≺ (μ,j)} C_{ν,q}(X_n) N_n^{-ν} (log N_n)^q) / (N_n^{-μ} (log N_n)^j)`
`  ⇒ C_{μ,j}(Z)`. -/
theorem tendstoInDistribution_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ)
    (hk : ∀ i, 0 < k i) (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ₀ : ℝ}
    (hμ : ∃ m : ℕ, μ₀ = (m : ℝ) / latticeQ k) {j : ℕ} (hj : j ≤ n)
    (X : ι → Ω → DataSpace (n + 1)) (hXm : ∀ i, Measurable (X i)) (Z : Ω' → DataSpace (n + 1))
    (hX : TendstoInDistribution X l Z (fun _ => μ) μ') (Nseq : ι → ℝ) (hN0 : ∀ i, 0 ≤ Nseq i)
    (hN : Tendsto Nseq l atTop) :
    TendstoInDistribution (fun i ω => orderedRemainder n h k β b (X i ω) μ₀ j (Nseq i)) l
      (fun ω => dataBoxCoeff n h k β b (Z ω) μ₀ j) (fun _ => μ) μ' := by
  have hC := tendstoInDistribution_dataBoxCoeff n h k hk β hβ hb μ₀ j X Z hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ fun i =>
    ((measurable_orderedRemainder n h k hk β hβ hb μ₀ j (hN0 i)).comp (hXm i)).aemeasurable
  exact tendstoInMeasure_orderedRemainder_sub n h k hk β hβ hb hμ hj X Z hX Nseq hN

end Grammar

```


## Full proof of the uniform ordered-remainder theorem (unit 275)

```lean
/-- **Ordered normalised remainders converge uniformly on data balls**: for a target `(μ, j)` with
`μ ∈ Q⁻¹ℕ` and `j ≤ n`, `R_N^{μ,j}(x) → C_{μ,j}(x)` uniformly in `‖x‖ ≤ R` as `N → ∞`. -/
theorem tendstoUniformlyOn_orderedRemainder (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : ∃ m : ℕ, μ = (m : ℝ) / latticeQ k)
    {j : ℕ} (hj : j ≤ n) (R : ℝ) :
    TendstoUniformlyOn (fun N x => orderedRemainder n h k β b x μ j N)
      (fun x => dataBoxCoeff n h k β b x μ j) atTop (Metric.closedBall 0 R) := by
  have hQ : 0 < latticeQ k := latticeQ_pos k hk
  have hQ' : (0 : ℝ) < latticeQ k := by exact_mod_cast hQ
  obtain ⟨m, hm⟩ := hμ
  have hμ0 : 0 ≤ μ := by rw [hm]; positivity
  set Q := latticeQ k with hQdef
  set c : ℝ := b ^ (2 * ∑ i, k i) with hc
  have hc0 : 0 < c := by positivity
  -- the target lies in the index set of the cutoff `μ + 1`
  have htarget : (μ, j) ∈ indexSet n Q (μ + 1) := by
    unfold indexSet
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_range.2 (Nat.lt_succ_of_le hj)⟩
    rw [hm]; exact mem_latticeBelow hQ (by rw [← hm]; linarith)
  have hpred_sub : predSet n Q μ j ⊆ indexSet n Q (μ + 1) := Finset.filter_subset _ _
  have htarget_notin : (μ, j) ∉ predSet n Q μ j := by
    unfold predSet
    rw [Finset.mem_filter]
    exact fun hcontra => precedes_irrefl _ hcontra.2
  have hsub : predSet n Q μ j ∪ {(μ, j)} ⊆ indexSet n Q (μ + 1) :=
    Finset.union_subset hpred_sub (Finset.singleton_subset_iff.2 htarget)
  -- the key algebraic decomposition
  have hdecomp : ∀ (x : DataSpace (n + 1)) (N : ℝ),
      dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
          dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j) =
        (dataBoxIntegral n h k β N b x -
          ∑ p ∈ indexSet n Q (μ + 1), expTerm n h k β b x N p) +
        ∑ p ∈ restSet n Q μ j, expTerm n h k β b x N p := by
    intro x N
    unfold restSet predSum
    rw [← Finset.sum_sdiff hsub, Finset.sum_union (Finset.disjoint_singleton_right.2 htarget_notin),
      Finset.sum_singleton]
    unfold expTerm
    ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hmaj := tendsto_remainderMajorant n h k β b μ j R
  have hev : ∀ᶠ N in atTop, remainderMajorant n h k β b μ j R N < ε :=
    hmaj.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (1 / c)] with N hNε hNe
    hNc x hx
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hN1 : 1 < N := lt_of_lt_of_le (by have := Real.add_one_lt_exp one_ne_zero; linarith) hNe
  have hN0 : 0 < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hNe
  have hD : 0 < N ^ (-μ) * Real.log N ^ j := by positivity
  have hscale : 1 ≤ boxScale k b N := by
    unfold boxScale; rw [← hc]
    rwa [div_le_iff₀ hc0] at hNc
  rw [Real.dist_eq]
  -- `C − R_N = −(Z − pred − C D)/D`
  have hRN : dataBoxCoeff n h k β b x μ j - orderedRemainder n h k β b x μ j N =
      -((dataBoxIntegral n h k β N b x - predSum n h k β b x μ j N -
        dataBoxCoeff n h k β b x μ j * (N ^ (-μ) * Real.log N ^ j)) /
          (N ^ (-μ) * Real.log N ^ j)) := by
    unfold orderedRemainder
    have hD' := hD.ne'
    field_simp
    ring
  rw [hRN, abs_neg, hdecomp, add_div, Finset.sum_div]
  refine lt_of_le_of_lt ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hNε
  · -- the cutoff error
    have hcut := dataTaylorTree_cutoff_bound n h k hk β hβ (L := μ + 1) (by linarith) hb hN0 hscale
      hx'
    rw [spectralSum_eq_sum_indexSet] at hcut
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    refine hcut.trans ?_
    -- `(Nc)^{-L}(1+log(Nc))^n ≤ c^{-L}(1+|log c|)^n N^{-L}(1+log N)^n` and `(log N)^j ≥ 1`
    have hK0 : 0 ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R :=
      mul_nonneg (by positivity) (dataCutoffConst_nonneg n k β hβ _ ((norm_nonneg x).trans hx'))
    have hbs : boxScale k b N = N * c := by unfold boxScale; rw [hc]
    have h1 : boxScale k b N ^ (-(μ + 1)) = N ^ (-(μ + 1)) * c ^ (-(μ + 1)) := by
      rw [hbs, Real.mul_rpow hN0.le hc0.le]
    have h2 : (1 + Real.log (boxScale k b N)) ^ n ≤
        (1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n := by
      rw [hbs, ← mul_pow]
      exact pow_le_pow_left₀ (by have := Real.log_nonneg (show 1 ≤ N * c by rwa [← hbs]); linarith)
        (one_add_log_mul_le hN1.le hc0) n
    have h3 : (1 : ℝ) ≤ Real.log N ^ j := one_le_pow₀ hlog1
    have hr0 : 0 ≤ N ^ (-(μ + 1)) := Real.rpow_nonneg hN0.le _
    have hcr0 : 0 ≤ c ^ (-(μ + 1)) := Real.rpow_nonneg hc0.le _
    have hlogN : 0 ≤ 1 + Real.log N := by linarith
    calc b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (boxScale k b N ^ (-(μ + 1)) * (1 + Real.log (boxScale k b N)) ^ n)
        ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (N ^ (-(μ + 1)) * c ^ (-(μ + 1)) * ((1 + |Real.log c|) ^ n * (1 + Real.log N) ^ n)) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (mul_nonneg hr0 hcr0)) hK0
      _ = b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * 1) := by
          field_simp
      _ ≤ b ^ (∑ i, h i + (n + 1)) * dataCutoffConst n k β (μ + 1) R *
          (c ^ (-(μ + 1)) * (1 + |Real.log c|) ^ n) *
          (N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ)) * (N ^ (-μ) * Real.log N ^ j) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3
            (Real.rpow_nonneg hN0.le _)) ?_
          have : 0 ≤ N ^ (-(μ + 1)) * (1 + Real.log N) ^ n / N ^ (-μ) := by positivity
          exact mul_nonneg (mul_nonneg hK0 (mul_nonneg hcr0 (by positivity))) this
  · -- the retained terms
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    obtain ⟨hpi, hpμ, hpq⟩ := mem_restSet hp
    exact abs_expTerm_div_le n h k hk β hβ hb hx' hpμ hpq (mem_indexSet_snd_le hpi) hNe

end Grammar

```

## Questions
1. **u273.** Is `cutoffBound_mono` correctly hypothesised (`|a| ≤ |a'|`, `0 ≤ E ≤ E'`, `0 ≤ B ≤ B'`) and is `dataTaylorTree_cutoff_bound` the faithful data-space restatement of Headline XXVIII with `dataCutoffConst n k β L R = cutoffBound n k β L R R R` (using `|ξ(0)| ≤ ‖x‖ ≤ R`, both masses `≤ ‖x‖ ≤ R`)? Hypotheses `N > 0`, `N b^{2|k|} ≥ 1`, `L > 0`.
2. **u274.** Is the Lipschitz constant `b^{|h|+d} e^{β√(Nb^{2|k|}) R}(1 + Rβ√(Nb^{2|k|}))` for `x ↦ Z(N;x)` on `‖x‖ ≤ R` correct (integrand on the unit box: `|evalF η| ≤ mass η ≤ R`, `u^h ≤ 1`, `|e^{A+sξ} − e^{A+sξ'}| ≤ e^{β√N R} β√N |ξ − ξ'|` with `A ≤ 0`, `0 ≤ s ≤ β√N`; unit-box volume 1)? Any measurability gap (the integrand is continuous on the closed cube by the Weierstrass M-test, integrable on the box)?
3. **u275.** Is the ordering `precedes p q := p.1 < q.1 ∨ (p.1 = q.1 ∧ q.2 < p.2)` the paper's `(μ,m) < (μ',m')` (larger log power first at equal exponent)? `predSet` is the filter of `latticeBelow Q (μ+1) × {0..n}` by `≺ (μ,j)` — is taking the index set at cutoff `μ + 1` legitimate (all predecessors have exponent `≤ μ < μ+1`, so the set is independent of any larger cutoff)? Check the decomposition `Z − pred − C_{μ,j} D = (Z − S_{μ+1}) + ∑_{rest}`, `rest = indexSet \ (pred ∪ {(μ,j)})` = terms with `ν > μ` or `(ν = μ, q < j)`; the majorants `termMajorant` (`1/log N` at equal exponent, `N^{-(ν−μ)}(1+log N)^n` otherwise) and `abs_expTerm_div_le` (for `N ≥ e`); the cutoff ratio bound with `c = b^{2|k|}`: `(Nc)^{-(μ+1)}(1+log(Nc))^n/(N^{-μ}(log N)^j) ≤ c^{-(μ+1)}(1+|log c|)^n · N^{-(μ+1)}(1+log N)^n/N^{-μ}`; and the `TendstoUniformlyOn` statement (uniform in `x` on the closed ball). The hypothesis `μ ∈ Q⁻¹ℕ` (`∃ m, μ = m/Q`) with `j ≤ n`: right? (If `μ` is not a candidate exponent the coefficient is zero and the statement is still meaningful.) Any missing threshold?
4. **u276 / Headline XXXV.** Is `tendstoInDistribution_orderedRemainder` a faithful chart-level rendering of the convergence-in-distribution clause of `thm:strataempiricalexpansion` (for arbitrary normal dimension `d = n+1`, conditional on `X_n ⇒ Z` in `E_b × E_b`, with `N_n → ∞`, `N_n ≥ 0`, `X_n` measurable)? Is the proof route (uniform-on-balls ⇒ in probability via norm-boundedness by portmanteau ⇒ Slutsky) sound as stated in `tendstoInMeasure_zero_of_uniform_on_balls` (hypothesis form `∀ M ≥ 0, ∀ ε > 0, ∀ᶠ n, ∀ ω, ‖X n ω‖ ≤ M → |f n ω| ≤ ε`)? What non-claims must accompany XXXV (Hypothesis I, common analytic radius, Gaussianity, joint convergence of several remainders, sample-size convention)?
5. Verdict per unit, overall verdict, should-fix list before (a) freezing tranche A1–A2 and (b) starting A3 (tangential integration / chart assembly).
