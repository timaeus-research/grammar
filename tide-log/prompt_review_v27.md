# Fidelity review v27 — Programme S (§4.3 stochastic Taylor tree), units 270–272: data space, ballwise Lipschitz continuity, Headline XXXIV

You are an independent statement-level reviewer of a Lean 4 / Mathlib formalisation (repository `timaeus-research/grammar`, branch `tide/stochastic-taylor-tree`, pin `1ecc05f`) of the grammar paper's §4 (Gerraty–Murfet). Previous reviews v18–v26 covered the Taylor-tree programme (Headlines XXII–XXXIII: `thm:TaylorTree` / `cor:standardintegralexp` in every positive dimension with coefficient families `Re(∂^γ F(0)/γ!)`). Programme S (Astra consult #33) now targets `thm:strataempiricalexpansion` at chart level in arbitrary normal dimension `d = n + 1`: (A1) the canonical coefficient functionals are continuous on the weighted-ℓ¹ data space; (A2) convergence in distribution of coefficient vectors and ordered normalised remainders under convergence in distribution of the data. Units 270–272 are the first tranche (A1); Astra required a hard review after unit 3. Please review the STATEMENTS (excerpts extracted mechanically: docstring + statement up to `:=`; the extractor sometimes truncates or duplicates — the source has exactly one of each; everything compiles with zero `sorry` and no additional axioms) and the one proof reproduced in full.

## Background definitions (frozen, reviewed earlier)
- `CoeffFamily d = (Fin d → ℕ) → ℝ`; `AbsSummable c ↔ Summable (|c ·|)`; `mass c = ∑' γ |c γ|`; `scale c b γ = c γ b^{|γ|}`; `AbsSummableAt c b ↔ Summable (|c γ| b^{|γ|})`.
- `familySpectralCoeff n h k β cξ cη μ j` = the canonical unit-box coefficient `A_{μ,j}` (limit of polynomial truncation coefficients; equals the paper's series `∑_p β^p/p! T_p(cη * J^{*p})`, `J = fluctFamily cξ` the constant-free part, `T_p(f) = K_k ∑_γ f_γ S_p(μ,j;γ)`, `S_p(μ,j;γ) = ∑_{q=j}^{n} c_{μ,q}(u^{h+γ}) C(q,j) fluctMoment β (cξ 0) p μ (q−j)`, `fluctMoment β a p μ i = ∫₀^∞ t^{μ−1}(−log t)^i (√t)^p e^{−βt+β√t a} dt`; zero off the candidate set `Λ(h,k)`).
- `boxCoeff n h k β b cξ cη μ j = b^{|h|+d} (b^{2|k|})^{-μ} ∑_{q=j}^{n} familySpectralCoeff (scale cξ b) (scale cη b) μ q · C(q,j) · (log b^{2|k|})^{q−j}` — the coefficient of `N^{-μ}(log N)^j` in the expansion of the box integral `familyPhaseIntegralBox = ∫_{(0,b]^d} evalF cη u · u^h · exp(−βN u^{2k} + β√N u^k evalF cξ u) du` (`boxSpectralSum_eq`, Headline XXVIII).
- `phaseLogMoment β b ν r p = ∫₀^∞ t^{ν−1} (1+|log t|)^r (√t)^p e^{−βt+βb√t} dt` (`M_{ν,r,p}(b)`); `tsum_phaseLogMoment_series : ∑_p (βB)^p/p! M_{ν,r,p}(b) = M_{ν,r,0}(b+B)`; `phaseLogMoment_succ : M_{ν,r,p+1} = M_{ν+1/2,r,p}`; `hasSum_phase_series_shift : ∑_p β^p/p! · p B^{p−1} · M_{ν,r,p}(a) = β M_{ν+1/2,r,0}(a+B)`; `abs_fluctMoment_le : |fluctMoment β a p μ i| ≤ M_{μ,n,p}(a)` for `i ≤ n`; `phaseLogMoment_mono` (monotone in `b`); `hasDerivAt_fluctMoment : HasDerivAt (a ↦ fluctMoment β a p μ i) (β fluctMoment β a (p+1) μ i) a`; `abs_kernelFunctional_le : |T_p f| ≤ K_k D M_{μ,n,p}(a) mass f`; `kernelBudget D = (n+1)(n+1)! Q^n 2^n`.

## Statements

### Grammar/StochasticData.lean

```lean
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

```
### Grammar/FamilyCoeffLipschitz.lean

```lean
/-!
# Ballwise Lipschitz continuity of the Taylor-tree coefficients (Stage S2 — the gate)

Unit 271 (Astra #33, unit 2 of Programme S). The canonical unit-box coefficients
`A_{μ,j}(cξ, cη) = familySpectralCoeff` are Lipschitz on every ball of the weighted-ℓ¹ data:
for absolutely summable families with `mass cξ, mass cξ', mass cη, mass cη' ≤ R`,

`|A_{μ,j}(cξ', cη') − A_{μ,j}(cξ, cη)| ≤ familyLipConst · (mass(cξ' − cξ) + mass(cη' − cη))`
(`abs_familySpectralCoeff_sub_le`, constant `familyLipConst n k β μ R`). The new ingredient
compared with the Stage 4 stability gate
(`abs_spectralCoeff_sub_le`, fixed constant phase) is the **varying constant phase**
`a = ξ(0)`: by the mean value theorem and `∂_a fluctMoment = β fluctMoment(p+1)`
(`hasDerivAt_fluctMoment`),
`|fluctMoment β a p μ i − fluctMoment β a' p μ i| ≤ β M_{μ,n,p+1}(R) |a − a'|`
on `|a|, |a'| ≤ R` (`abs_fluctMoment_sub_le`), which propagates through the kernel `S_p` and the
kernel functional `T_p` (`abs_kernelFunctional_sub_phase_le`). The other two perturbations
(amplitude and constant-free phase `J`) go through the linearity of `T_p` and the mass algebra of
the Cauchy product (`mass_convPow_sub_le`), and the three resulting series in `p` are summed in
closed form by the Tonelli identity `∑_p (βR)^p/p! M_{ν,n,p}(R) = M_{ν,n,0}(2R)` and its shifted
forms. The constant depends on the data only through the ball radius `R`.
-/

theorem and `∂_a fluctMoment = β fluctMoment(p+1)`
(`hasDerivAt_fluctMoment`),
`|fluctMoment β a p μ i − fluctMoment β a' p μ i| ≤ β M_{μ,n,p+1}(R) |a − a'|`
on `|a|, |a'| ≤ R` (`abs_fluctMoment_sub_le`), which propagates through the kernel `S_p` and the
kernel functional `T_p` (`abs_kernelFunctional_sub_phase_le`). The other two perturbations
(amplitude and constant-free phase `J`) go through the linearity of `T_p` and the mass algebra of
the Cauchy product (`mass_convPow_sub_le`), and the three resulting series in `p` are summed in
closed form by the Tonelli identity `∑_p (βR)^p/p! M_{ν,n,p}(R) = M_{ν,n,0}(2R)` and its shifted
forms. The constant depends on the data only through the ball radius `R`.
-/

open MeasureTheory Set Real Filter Topology

namespace Grammar

open CoeffFamily

/-- The fluctuation moments are Lipschitz in the constant phase on `[-R, R]`, with constant
`β M_{μ,n,p+1}(R)`. -/
theorem abs_fluctMoment_sub_le (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) {R a a' : ℝ} (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |fluctMoment β a p μ i - fluctMoment β a' p μ i| ≤
      β * phaseLogMoment β R μ n (p + 1) * |a - a'| := by
  set f' : ℝ → ℝ := fun c => β * fluctMoment β c (p + 1) μ i with hf'
  have hf : ∀ c ∈ Icc (-R) R, HasDerivWithinAt (fun c => fluctMoment β c p μ i) (f' c)
      (Icc (-R) R) c :=
    fun c _ => (hasDerivAt_fluctMoment β hβ p hμ i c).hasDerivWithinAt
  have hbound : ∀ c ∈ Icc (-R) R, ‖f' c‖ ≤ β * phaseLogMoment β R μ n (p + 1) := by
    intro c hc
    rw [hf', Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    exact (abs_fluctMoment_le β c hβ (p + 1) hμ hi).trans
      (phaseLogMoment_mono β hβ hc.2 hμ n (p + 1))
  have key := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (abs_le.1 ha') (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using key

/-- The kernel `S_p(μ,j;γ)` is Lipschitz in the constant phase, uniformly in `γ`. -/
theorem abs_kernelS_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) (γ : Fin (n + 1) → ℕ) {R a a' : ℝ}
    (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |kernelS n h k β a p μ j γ - kernelS n h k β a' p μ j γ| ≤
      kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) * |a - a'| := by
  unfold kernelS kernelBudget
  rw [← Finset.sum_sub_distrib]
  set M := β * phaseLogMoment β R μ n (p + 1) * |a - a'| with hM
  have hM0 : 0 ≤ M :=
    mul_nonneg (mul_nonneg hβ.le (phaseLogMoment_nonneg _ _ _ _ _)) (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a p μ (q - j) -
        PowLogRep.coeffAt (stateDensityRep n (monoWeights (h + γ) k)) μ q * (q.choose j : ℝ) *
          fluctMoment β a' p μ (q - j)| ≤
      (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M := by
    intro q hq
    have hqn : q ≤ n := Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hq).2
    rw [← mul_sub, abs_mul, abs_mul, Nat.abs_cast]
    refine mul_le_mul (mul_le_mul (abs_coeffAt_stateDensityRep_le n (h + γ) k hk μ q) ?_
      (by positivity) (by positivity)) (abs_fluctMoment_sub_le β hβ p hμ (by omega) ha ha')
      (abs_nonneg _) (by positivity)
    calc (q.choose j : ℝ) ≤ (2 ^ q : ℕ) := by exact_mod_cast Nat.choose_le_two_pow q j
      _ ≤ 2 ^ n := by exact_mod_cast Nat.pow_le_pow_right two_pos hqn
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Ico]
  have hcard : ((n + 1 - j : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast Nat.sub_le (n + 1) j
  have hpos : 0 ≤ (((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M :=
    mul_nonneg (by positivity) hM0
  calc ((n + 1 - j : ℕ) : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M)
      ≤ (n + 1 : ℝ) * ((((n + 1).factorial : ℝ) * (latticeQ k : ℝ) ^ n) * 2 ^ n * M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hM]; ring

/-- The kernel functional is Lipschitz in the constant phase: `|T_p(a; f) − T_p(a'; f)| ≤
K_k D β M_{μ,n,p+1}(R) · mass f · |a − a'|`. -/
theorem abs_kernelFunctional_sub_phase_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f : CoeffFamily (n + 1)}
    (hf : AbsSummable f) {R a a' : ℝ} (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |kernelFunctional n h k β a p μ j f - kernelFunctional n h k β a' p μ j f| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) *
        mass f * |a - a'| := by
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  unfold kernelFunctional
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  have hs1 : Summable fun γ => f γ * kernelS n h k β a p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a hβ p hμ j hf)
  have hs2 : Summable fun γ => f γ * kernelS n h k β a' p μ j γ :=
    Summable.of_norm
      (by simpa [Real.norm_eq_abs] using summable_kernel_term n h k hk β a' hβ p hμ j hf)
  rw [← hs1.tsum_sub hs2]
  set C := kernelBudget n k * (β * phaseLogMoment β R μ n (p + 1)) * |a - a'| with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (mul_nonneg (kernelBudget_nonneg n k)
      (mul_nonneg hβ.le (phaseLogMoment_nonneg _ _ _ _ _))) (abs_nonneg _)
  have hterm : ∀ γ, |f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ| ≤
      |f γ| * C := by
    intro γ
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_kernelS_sub_le n h k hk β hβ p hμ j γ ha ha')
      (abs_nonneg _)
  have hsum : Summable fun γ =>
      |f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm (hf.mul_right C)
  have h1 : |∑' γ, (f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)| ≤
      ∑' γ, |f γ| * C := by
    have hn := norm_tsum_le_tsum_norm
      (f := fun γ => f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)
      (by simpa [Real.norm_eq_abs] using hsum)
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (Summable.tsum_le_tsum hterm hsum (hf.mul_right C))
  rw [tsum_mul_right] at h1
  calc (∏ i, 1 / (2 * (k i : ℝ))) *
        |∑' γ, (f γ * kernelS n h k β a p μ j γ - f γ * kernelS n h k β a' p μ j γ)|
      ≤ (∏ i, 1 / (2 * (k i : ℝ))) * (mass f * C) := mul_le_mul_of_nonneg_left h1 hK
    _ = _ := by rw [hC]; ring

theorem fluctFamily_sub {d : ℕ} (c c' : CoeffFamily d) :
    fluctFamily (c - c') = fluctFamily c - fluctFamily c' := by
  funext γ
  simp only [fluctFamily, Pi.sub_apply]
  split_ifs <;> simp

theorem abs_apply_le_mass {d : ℕ} {c : CoeffFamily d} (hc : AbsSummable c) (γ : Fin d → ℕ) :
    |c γ| ≤ mass c :=
  hc.le_tsum γ fun _ _ => abs_nonneg _

/-- The Lipschitz constant of the unit-box coefficients on the data ball of radius `R`. -/
noncomputable def familyLipConst (n : ℕ) (k : Fin (n + 1) → ℕ) (β μ R : ℝ) : ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k *
    (2 * β * R * phaseLogMoment β (R + R) (μ + 1 / 2) n 0 + phaseLogMoment β (R + R) μ n 0)

theorem familyLipConst_nonneg (n : ℕ) (k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) (μ : ℝ) {R : ℝ}
    (hR : 0 ≤ R) : 0 ≤ familyLipConst n k β μ R := by
  unfold familyLipConst
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  refine mul_nonneg (mul_nonneg hK (kernelBudget_nonneg n k)) ?_
  have := phaseLogMoment_nonneg β (R + R) (μ + 1 / 2) n 0
  have := phaseLogMoment_nonneg β (R + R) μ n 0
  positivity

/-- **The coefficient series is Lipschitz on data balls** (`μ > 0`): for masses `≤ R`,
`|A_{μ,j}(cξ', cη') − A_{μ,j}(cξ, cη)| ≤ familyLipConst · (mass (cξ' − cξ) + mass (cη' − cη))`. -/
theorem abs_familyCoeffSeries_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) (hRη' : mass cη' ≤ R) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    |familyCoeffSeries n h k β cξ' cη' μ j - familyCoeffSeries n h k β cξ cη μ j| ≤
      familyLipConst n k β μ R * (mass (cξ' - cξ) + mass (cη' - cη)) := by
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  have hK : 0 ≤ ∏ i, 1 / (2 * (k i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  set K₀ := (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg hK (kernelBudget_nonneg n k)
  -- data
  set a := cξ 0 with ha_def
  set a' := cξ' 0 with ha'_def
  set J := fluctFamily cξ with hJ
  set J' := fluctFamily cξ' with hJ'
  have hJs : AbsSummable J := hξ.fluctFamily
  have hJ's : AbsSummable J' := hξ'.fluctFamily
  have hJR : mass J ≤ R := (mass_fluctFamily_le hξ).trans hRξ
  have hJ'R : mass J' ≤ R := (mass_fluctFamily_le hξ').trans hRξ'
  have haR : |a| ≤ R := (abs_apply_le_mass hξ 0).trans hRξ
  have ha'R : |a'| ≤ R := (abs_apply_le_mass hξ' 0).trans hRξ'
  have ha'R' : a' ≤ R := (le_abs_self _).trans ha'R
  set Δξ := mass (cξ' - cξ) with hΔξ
  set Δη := mass (cη' - cη) with hΔη
  have hΔξ0 : 0 ≤ Δξ := mass_nonneg _
  have hΔη0 : 0 ≤ Δη := mass_nonneg _
  have haa : |a' - a| ≤ Δξ := by
    have := abs_apply_le_mass (hξ'.sub hξ) 0
    simpa [Pi.sub_apply] using this
  have hJJ : mass (J' - J) ≤ Δξ := by
    rw [hJ, hJ', ← fluctFamily_sub]
    exact mass_fluctFamily_le (hξ'.sub hξ)
  -- the three majorant series
  set M := phaseLogMoment β (R + R) μ n 0 with hM
  set M' := phaseLogMoment β (R + R) (μ + 1 / 2) n 0 with hM'
  have hb : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1))) (β * R * M') := by
    have hs := (summable_phaseLogMoment_series β R R (μ + 1 / 2) hβ (by linarith) hR0 n).hasSum
    rw [tsum_phaseLogMoment_series β R R (μ + 1 / 2) hβ (by linarith) hR0 n] at hs
    refine (hs.mul_left (β * R)).congr_fun fun p => ?_
    rw [phaseLogMoment_succ, mul_pow, pow_succ]
    ring
  have hc : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p))
      M := by
    have hs := (summable_phaseLogMoment_series β R R μ hβ hμ hR0 n).hasSum
    rw [tsum_phaseLogMoment_series β R R μ hβ hμ hR0 n] at hs
    refine hs.congr_fun fun p => ?_
    rw [mul_pow]; ring
  have hd : HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1))))) (R * (β * M')) := by
    have hs := hasSum_phase_series_shift β R R μ hβ hμ hR0 n
    refine (hs.mul_left R).congr_fun fun p => ?_
    ring
  -- termwise bound
  have hterm : ∀ p : ℕ,
      |familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p| ≤
      K₀ * (β ^ p / (p.factorial : ℝ) * (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1)) * Δξ +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p) * Δη +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1)))) *
          Δξ) := by
    intro p
    unfold familyCoeffTerm
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ))]
    set f := CoeffFamily.conv cη (CoeffFamily.convPow J p) with hf
    set f' := CoeffFamily.conv cη' (CoeffFamily.convPow J' p) with hf'
    have hfs : AbsSummable f := hη.conv (hJs.convPow p)
    have hf's : AbsSummable f' := hη'.conv (hJ's.convPow p)
    have hfR : mass f' ≤ R * R ^ p :=
      (mass_conv_le hη' (hJ's.convPow p)).trans
        (mul_le_mul hRη' (mass_convPow_le hJ's hJ'R p) (mass_nonneg _) hR0)
    -- split the difference: phase at `f'`, then family difference at `a`
    have hsplit : kernelFunctional n h k β a' p μ j f' - kernelFunctional n h k β a p μ j f =
        (kernelFunctional n h k β a' p μ j f' - kernelFunctional n h k β a p μ j f') +
          kernelFunctional n h k β a p μ j (f' - f) := by
      rw [← kernelFunctional_sub n h k hk β a hβ p hμ j hf's hfs]; ring
    have h1 := abs_kernelFunctional_sub_phase_le n h k hk β hβ p hμ j hf's ha'R haR
    have h2 := abs_kernelFunctional_le n h k hk β a hβ p hμ j (hf's.sub hfs)
    -- mass of the family difference
    have hff : f' - f = CoeffFamily.conv (cη' - cη) (CoeffFamily.convPow J' p) +
        CoeffFamily.conv cη (CoeffFamily.convPow J' p - CoeffFamily.convPow J p) := by
      rw [CoeffFamily.conv_sub_left, CoeffFamily.conv_sub_right, hf, hf']; abel
    have hmass : mass (f' - f) ≤ Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ) := by
      rw [hff]
      have hA : AbsSummable (CoeffFamily.conv (cη' - cη) (CoeffFamily.convPow J' p)) :=
        (hη'.sub hη).conv (hJ's.convPow p)
      have hB : AbsSummable (CoeffFamily.conv cη
          (CoeffFamily.convPow J' p - CoeffFamily.convPow J p)) :=
        hη.conv ((hJ's.convPow p).sub (hJs.convPow p))
      refine (mass_add_le hA hB).trans (add_le_add ?_ ?_)
      · exact (mass_conv_le (hη'.sub hη) (hJ's.convPow p)).trans
          (mul_le_mul_of_nonneg_left (mass_convPow_le hJ's hJ'R p) (mass_nonneg _))
      · refine (mass_conv_le hη ((hJ's.convPow p).sub (hJs.convPow p))).trans ?_
        refine mul_le_mul hRη ?_ (mass_nonneg _) hR0
        exact (mass_convPow_sub_le hJ's hJs hJ'R hJR p).trans
          (mul_le_mul_of_nonneg_left hJJ (by positivity))
    have hMa : phaseLogMoment β a μ n p ≤ phaseLogMoment β R μ n p :=
      phaseLogMoment_mono β hβ ((le_abs_self a).trans haR) hμ n p
    have hM0 : 0 ≤ phaseLogMoment β R μ n p := phaseLogMoment_nonneg _ _ _ _ _
    have hM1 : 0 ≤ phaseLogMoment β R μ n (p + 1) := phaseLogMoment_nonneg _ _ _ _ _
    rw [hsplit]
    refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2))
      (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ))).trans ?_
    have hmassf : mass f' * |a' - a| ≤ R * R ^ p * Δξ :=
      mul_le_mul hfR haa (abs_nonneg _) (by positivity)
    have hfam : phaseLogMoment β a μ n p * mass (f' - f) ≤
        phaseLogMoment β R μ n p * (Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ)) :=
      mul_le_mul hMa hmass (mass_nonneg _) hM0
    have hKD : 0 ≤ K₀ * (β * phaseLogMoment β R μ n (p + 1)) := by positivity
    calc β ^ p / (p.factorial : ℝ) *
          (K₀ * (β * phaseLogMoment β R μ n (p + 1)) * mass f' * |a' - a| +
            K₀ * phaseLogMoment β a μ n p * mass (f' - f))
        ≤ β ^ p / (p.factorial : ℝ) *
          (K₀ * (β * phaseLogMoment β R μ n (p + 1)) * (R * R ^ p * Δξ) +
            K₀ * (phaseLogMoment β R μ n p * (Δη * R ^ p + R * ((p : ℝ) * R ^ (p - 1) * Δξ)))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
          · rw [mul_assoc (K₀ * (β * phaseLogMoment β R μ n (p + 1)))]
            exact mul_le_mul_of_nonneg_left hmassf hKD
          · rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hfam hK₀0
      _ = _ := by rw [pow_succ]; ring
  -- sum the termwise bounds
  have hbound : HasSum (fun p : ℕ =>
      K₀ * (β ^ p / (p.factorial : ℝ) * (β * phaseLogMoment β R μ n (p + 1) * R ^ (p + 1)) * Δξ +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * R ^ p) * Δη +
        β ^ p / (p.factorial : ℝ) * (phaseLogMoment β R μ n p * (R * ((p : ℝ) * R ^ (p - 1)))) *
          Δξ))
      (K₀ * (β * R * M' * Δξ + M * Δη + R * (β * M') * Δξ)) :=
    (((hb.mul_right Δξ).add (hc.mul_right Δη)).add (hd.mul_right Δξ)).mul_left K₀
  have hs := summable_familyCoeffSeries_terms n h k hk β hβ hξ hη hμ j
  have hs' := summable_familyCoeffSeries_terms n h k hk β hβ hξ' hη' hμ j
  have hsum : Summable fun p =>
      |familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hbound.summable
  unfold familyCoeffSeries
  rw [← (Summable.of_norm (by simpa [Real.norm_eq_abs] using hs')).tsum_sub
    (Summable.of_norm (by simpa [Real.norm_eq_abs] using hs))]
  have hn := norm_tsum_le_tsum_norm (f := fun p =>
    familyCoeffTerm n h k β cξ' cη' μ j p - familyCoeffTerm n h k β cξ cη μ j p)
    (by simpa [Real.norm_eq_abs] using hsum)
  simp only [Real.norm_eq_abs] at hn
  refine hn.trans ((Summable.tsum_le_tsum hterm hsum hbound.summable).trans ?_)
  rw [hbound.tsum_eq]
  unfold familyLipConst
  rw [← hK₀, ← hM, ← hM']
  have : K₀ * (β * R * M' * Δξ + M * Δη + R * (β * M') * Δξ) =
      K₀ * (2 * β * R * M' * Δξ + M * Δη) := by ring
  rw [this]
  have hM0 : 0 ≤ M := phaseLogMoment_nonneg _ _ _ _ _
  have hM'0 : 0 ≤ M' := phaseLogMoment_nonneg _ _ _ _ _
  have hin : 2 * β * R * M' * Δξ + M * Δη ≤ (2 * β * R * M' + M) * (Δξ + Δη) := by
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * β * R) hM'0) hΔη0,
      mul_nonneg hM0 hΔξ0]
  calc K₀ * (2 * β * R * M' * Δξ + M * Δη) ≤ K₀ * ((2 * β * R * M' + M) * (Δξ + Δη)) :=
        mul_le_mul_of_nonneg_left hin hK₀0
    _ = _ := by ring

/-- **Ballwise Lipschitz continuity of the canonical unit-box coefficients** (every real `μ`). -/
theorem abs_familySpectralCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cξ' cη cη' : CoeffFamily (n + 1)} (hξ : AbsSummable cξ)
    (hξ' : AbsSummable cξ') (hη : AbsSummable cη) (hη' : AbsSummable cη') {R : ℝ}
    (hRξ : mass cξ ≤ R) (hRξ' : mass cξ' ≤ R) (hRη : mass cη ≤ R) (hRη' : mass cη' ≤ R) (μ : ℝ)
    (j : ℕ) :
    |familySpectralCoeff n h k β cξ' cη' μ j - familySpectralCoeff n h k β cξ cη μ j| ≤
      familyLipConst n k β μ R * (mass (cξ' - cξ) + mass (cη' - cη)) := by
  have hR0 : 0 ≤ R := (mass_nonneg cξ).trans hRξ
  by_cases hc : candidateExp h k μ
  · rw [familySpectralCoeff_eq_series' n h k hk β hβ hξ' hη', familySpectralCoeff_eq_series' n h k
      hk β hβ hξ hη]
    exact abs_familyCoeffSeries_sub_le n h k hk β hβ hξ hξ' hη hη' hRξ hRξ' hRη hRη'
      (candidateExp_pos hk hc) j
  · rw [familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ' hη' hc j,
      familySpectralCoeff_eq_zero_of_not_candidate n h k hk β hβ hξ hη hc j, sub_zero, abs_zero]
    exact mul_nonneg (familyLipConst_nonneg n k β hβ μ hR0)
      (add_nonneg (mass_nonneg _) (mass_nonneg _))

end Grammar

```
### Grammar/DataCoeffContinuity.lean

```lean
/-!
# Continuity of the canonical coefficient functionals on the data space (Stage S3 — A1)

Unit 272 (Astra #33, unit 3 of Programme S). **Headline XXXIV**: the paper-facing canonical
coefficient `C_{μ,j} = dataBoxCoeff n h k β b · μ j` — the coefficient of `N^{-μ} (log N)^j` in the
Taylor-tree expansion of the original box integral `Z(N; ξ, η)` — is Lipschitz on every ball of
the weighted-ℓ¹ data space `E_b × E_b` (`taylorTree_coeff_lipschitzOn_ball`), hence continuous
(`continuous_taylorTree_coeff`) and Borel measurable, for every real `μ` and every `j`; finite
vectors of coefficients are continuous (`continuous_taylorTree_coeffVec`). This is a precise
sufficient replacement for the paper's cited-but-unstated `prop:convergence` (continuity of
`ξ ↦ C_{μ,m}(ξ)`), in the weighted-ℓ¹ topology at the box radius `b`; the identification with a
topology on `C^ω([0,b]^d)` is not claimed. The Lipschitz constant on the ball of radius `R` is
`dataLipConst = b^{|h|+d} (b^{2|k|})^{-μ} (∑_{q=j}^{d-1} C(q,j) |log b^{2|k|}|^{q-j}) · 2L`,
`L = familyLipConst`.
-/

/-- The Lipschitz constant of the canonical box coefficient on the data ball of radius `R`. -/
noncomputable def dataLipConst (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b μ : ℝ) (j : ℕ) (R : ℝ) : ℝ :=
  b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) *
    (∑ q ∈ Finset.Ico j (n + 1), (q.choose j : ℝ) * |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j)) *
    (2 * familyLipConst n k β μ R)

theorem dataLipConst_nonneg (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 < β) {b : ℝ}
    (hb : 0 < b) (μ : ℝ) (j : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ dataLipConst n h k β b μ j R := by
  unfold dataLipConst
  have h1 := familyLipConst_nonneg n k β hβ μ hR
  have h2 : 0 ≤ ∑ q ∈ Finset.Ico j (n + 1),
      (q.choose j : ℝ) * |Real.log (b ^ (2 * ∑ i, k i))| ^ (q - j) :=
    Finset.sum_nonneg fun q _ => by positivity
  have h3 : 0 ≤ (b ^ (2 * ∑ i, k i)) ^ (-μ) := Real.rpow_nonneg (by positivity) _
  positivity

/-- The unit-box coefficients of the raw coordinates are Lipschitz on data balls. -/
theorem abs_familySpectralCoeff_coord_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (μ : ℝ)
    (q : ℕ) :
    |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q -
        familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q| ≤
      familyLipConst n k β μ R * (2 * ‖y - x‖) := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have h := abs_familySpectralCoeff_sub_le n h k hk β hβ (absSummable_xiCoord x)
    (absSummable_xiCoord y) (absSummable_etaCoord x) (absSummable_etaCoord y)
    ((mass_xiCoord_le x).trans hx) ((mass_xiCoord_le y).trans hy) ((mass_etaCoord_le x).trans hx)
    ((mass_etaCoord_le y).trans hy) μ q
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (familyLipConst_nonneg n k β hβ μ hR0))
  have h1 : mass (xiCoord y - xiCoord x) ≤ ‖y - x‖ := by
    have := mass_xiCoord_sub_le y x
    simpa [Pi.sub_def] using this
  have h2 : mass (etaCoord y - etaCoord x) ≤ ‖y - x‖ := by
    have := mass_etaCoord_sub_le y x
    simpa [Pi.sub_def] using this
  linarith

/-- **Headline XXXIV (quantitative form)**: the canonical box coefficient is Lipschitz on the
data ball of radius `R`. -/
theorem abs_dataBoxCoeff_sub_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {R : ℝ} {x y : DataSpace (n + 1)} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) (μ : ℝ) (j : ℕ) :
    |dataBoxCoeff n h k β b y μ j - dataBoxCoeff n h k β b x μ j| ≤
      dataLipConst n h k β b μ j R * ‖y - x‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  rw [dataBoxCoeff_eq n h k β hb, dataBoxCoeff_eq n h k β hb]
  set P := b ^ (∑ i, h i + (n + 1)) * (b ^ (2 * ∑ i, k i)) ^ (-μ) with hP
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  set ℓ := Real.log (b ^ (2 * ∑ i, k i)) with hℓ
  set L := familyLipConst n k β μ R with hL
  have hL0 : 0 ≤ L := familyLipConst_nonneg n k β hβ μ hR0
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hP0]
  have hterm : ∀ q ∈ Finset.Ico j (n + 1),
      |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q * (q.choose j : ℝ) * ℓ ^ (q - j) -
        familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q * (q.choose j : ℝ) *
          ℓ ^ (q - j)| ≤
      (q.choose j : ℝ) * |ℓ| ^ (q - j) * (L * (2 * ‖y - x‖)) := by
    intro q _
    rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have := abs_familySpectralCoeff_coord_sub_le n h k hk β hβ hx hy μ q
    calc |familySpectralCoeff n h k β (xiCoord y) (etaCoord y) μ q -
            familySpectralCoeff n h k β (xiCoord x) (etaCoord x) μ q| *
          (q.choose j : ℝ) * |ℓ| ^ (q - j)
        ≤ L * (2 * ‖y - x‖) * (q.choose j : ℝ) * |ℓ| ^ (q - j) := by
          gcongr
      _ = _ := by ring
  refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum hterm)) hP0).trans ?_
  rw [← Finset.sum_mul]
  unfold dataLipConst
  rw [← hP, ← hℓ, ← hL]
  apply le_of_eq
  ring

/-- **Headline XXXIV**: the canonical coefficient map is Lipschitz on every closed data ball. -/
theorem taylorTree_coeff_lipschitzOn_ball (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) (R : ℝ) :
    LipschitzOnWith (Real.toNNReal (dataLipConst n h k β b μ j R))
      (fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hy' : ‖y‖ ≤ R := by simpa using hy
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx'
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (dataLipConst_nonneg n h k β hβ hb μ j hR0)]
  exact abs_dataBoxCoeff_sub_le n h k hk β hβ hb hy' hx' μ j

/-- **Headline XXXIV**: the canonical coefficient map is continuous on the data space (the
paper's `prop:convergence`, in the weighted-ℓ¹ topology). -/
theorem continuous_taylorTree_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Continuous fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : Metric.closedBall (0 : DataSpace (n + 1)) (‖x‖ + 1) ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem (by simp)
  exact (taylorTree_coeff_lipschitzOn_ball n h k hk β hβ hb μ j (‖x‖ + 1)).continuousOn.continuousAt
    hmem

theorem measurable_taylorTree_coeff (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) (μ : ℝ) (j : ℕ) :
    Measurable fun x : DataSpace (n + 1) => dataBoxCoeff n h k β b x μ j :=
  (continuous_taylorTree_coeff n h k hk β hβ hb μ j).measurable

/-- A finite vector of canonical coefficients `(C_{μ_i, j_i})_i`. -/
noncomputable def dataCoeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (β b : ℝ) {m : ℕ}
    (F : Fin m → ℝ × ℕ) (x : DataSpace (n + 1)) : Fin m → ℝ :=
  fun i => dataBoxCoeff n h k β b x (F i).1 (F i).2

/-- **Headline XXXIV (finite vectors)**: every finite vector of canonical coefficients is
continuous on the data space. -/
theorem continuous_taylorTree_coeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) :
    Continuous (dataCoeffVec n h k β b F) :=
  continuous_pi fun i => continuous_taylorTree_coeff n h k hk β hβ hb (F i).1 (F i).2

theorem measurable_taylorTree_coeffVec (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b : ℝ} (hb : 0 < b) {m : ℕ} (F : Fin m → ℝ × ℕ) :
    Measurable (dataCoeffVec n h k β b F) :=
  (continuous_taylorTree_coeffVec n h k hk β hβ hb F).measurable

end Grammar

```


## Full proof of the mean-value step (unit 271)

```lean
/-- The fluctuation moments are Lipschitz in the constant phase on `[-R, R]`, with constant
`β M_{μ,n,p+1}(R)`. -/
theorem abs_fluctMoment_sub_le (β : ℝ) (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) {i n : ℕ}
    (hi : i ≤ n) {R a a' : ℝ} (ha : |a| ≤ R) (ha' : |a'| ≤ R) :
    |fluctMoment β a p μ i - fluctMoment β a' p μ i| ≤
      β * phaseLogMoment β R μ n (p + 1) * |a - a'| := by
  set f' : ℝ → ℝ := fun c => β * fluctMoment β c (p + 1) μ i with hf'
  have hf : ∀ c ∈ Icc (-R) R, HasDerivWithinAt (fun c => fluctMoment β c p μ i) (f' c)
      (Icc (-R) R) c :=
    fun c _ => (hasDerivAt_fluctMoment β hβ p hμ i c).hasDerivWithinAt
  have hbound : ∀ c ∈ Icc (-R) R, ‖f' c‖ ≤ β * phaseLogMoment β R μ n (p + 1) := by
    intro c hc
    rw [hf', Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    exact (abs_fluctMoment_le β c hβ (p + 1) hμ hi).trans
      (phaseLogMoment_mono β hβ hc.2 hμ n (p + 1))
  have key := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (abs_le.1 ha') (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using key


```

## Questions
1. **Data space (u270).** Is `DataSpace d = ℓ¹((Fin d → ℕ) ⊕ (Fin d → ℕ))` with `toXi b x γ = x(inl γ)/b^{|γ|}` a faithful model of `E_b × E_b` (`‖(cξ,cη)‖ = ∑|cξ_γ| b^{|γ|} + ∑|cη_γ| b^{|γ|}`)? Is `dataBoxCoeff` really the paper's `C_{μ,m}` (with `m = j+1`), i.e. the coefficient of `N^{-μ}(log N)^j` for the ORIGINAL box integral in the paper's sample size `N`? Any convention slip (rescaled unit-box vs box coefficients, `log b^{2|k|}` binomial conversion)?
2. **Lipschitz estimate (u271).** Check `abs_fluctMoment_sub_le` (mean value on `[−R,R]`, bound `β M_{μ,n,p+1}(R)`; is the use of `phaseLogMoment_mono` with `c ≤ R` correct given `M` is monotone in the *signed* phase `b`, and `abs_fluctMoment_le` gives `M(c)` at the signed `c`?), `abs_kernelS_sub_le`, `abs_kernelFunctional_sub_phase_le`, and the assembly `abs_familyCoeffSeries_sub_le`: the split `T(a';f') − T(a;f) = [T(a';f') − T(a;f')] + T(a; f' − f)`, `mass(f'−f) ≤ Δη R^p + R·p R^{p−1} Δξ` with `f = cη * J^{*p}`, the three series and their closed forms, and the final constant `familyLipConst = K_k D (2βR M_{μ+1/2,n,0}(2R) + M_{μ,n,0}(2R))`. Is the hypothesis set (all four masses `≤ R`, hence `|ξ(0)|, |ξ'(0)| ≤ R`) right, and is the estimate for all real `μ` (zero off `Λ(h,k)`) sound?
3. **Headline XXXIV (u272).** Is `taylorTree_coeff_lipschitzOn_ball` / `continuous_taylorTree_coeff` an honest formal replacement for the paper's cited-but-missing `prop:convergence` ("`C_{μ,m} : C^ω([0,b]^d,ℝ) → ℝ` is continuous")? What exact wording/non-claims should accompany it (topology on `C^ω`, dependence of the constant on `R`, the amplitude also varying, `η` deterministic in the paper)?
4. **Readiness for A2.** With XXXIV, A2 = continuous mapping (`TendstoInDistribution.continuous_comp`) for finite coefficient vectors, plus the ordered normalised remainders: `R_n^{μ,j} − C_{μ,j}(X_n) → 0` in probability from the uniform cutoff bound `cutoffBound n k β L (ξ(0)) (mass η) (mass ξ)` (monotone in its arguments) on data balls and tightness of `‖X_n‖`. Any statement-level trap you foresee (measurability of `x ↦ Z(N; x)`, the ordering `≺` of `(μ,j)`, the role of `log N` powers at equal exponent, `N b^{2|k|} ≥ 1` threshold)?
5. Verdict per unit (pass / qualified pass / fail), overall verdict, and should-fix list before continuing to A2.
