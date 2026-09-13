# Consult #108 — companion note: the model test and Rank 5 landed; the thin quartet instantiation; closure

You are Astra, our formalisation-strategy consultant for the Lean 4/Mathlib library `Grammar`
(timaeus-research/grammar, 661 modules, zero sorry/axiom, headline theorems axiom-clean). Your consult #107
accepted Ranks 1–3 of the companion-note programme (`averaging_dataset.tex`), specified the controlled model test
(normal location), authorised Rank 5 after a call-site audit, and gave the closure criteria and the final wording
checklist (§4). Everything below landed on main `a19cc7e`; both documents are repinned there.

## 1. The model test (CCCLVII–CCCLVIII)

Definitions (`Grammar/NormalLocationRemainder.lean`, `Grammar/GaussianQuadraticTilt.lean`):
`negLoss x w = −(w²/2 − x w)`; `priorVar a = toNNReal a⁻¹`, `normalPrior a = gaussianReal 0 (priorVar a)`;
`nll β x w = β ∑ᵢ (xᵢ − w)²/2` (full squared loss, `x : Fin n → ℝ`); `normalPartition a β x = ∫ e^{−nll} dprior`;
`normalPosterior a β x = (ofReal Z)⁻¹ • prior.withDensity (ofReal ∘ e^{−nll})`; `postPrec a β n = a + βn`;
`postVar a β n = tiltVar (priorVar a) (βn)` with `(postVar : ℝ) = (a+βn)⁻¹`; `postMean a β x = (a+βn)⁻¹ β∑xᵢ`;
`remainder a β n X Y ω = predictiveRemainder (negLoss (Y ω)) (normalPosterior a β fun i : Fin n => X i ω)`
(`predictiveRemainder X μ = cgf X μ 1 − μ[X] − Var/2`, CCCLVI);
`envelope v m x = 4 (absMom3 |x−m|³ (√v)³ + absMomSq3 (v/2)³)` with `absMom3 = ∫|z|³ dN(0,1)`,
`absMomSq3 = ∫|z²−1|³ dN(0,1)` kept SYMBOLIC (only integrability is used);
`remainderBound a β n = (32 absMom3² (√(a+βn)⁻¹)³ + absMomSq3 ((a+βn)⁻¹)³/2)/6`.

Theorems (all axiom-clean):
```lean
theorem gaussianReal_withDensity_quadratic (hv : v ≠ 0) (hc : 0 < (v : ℝ)⁻¹ + c) :
    (gaussianReal m v).withDensity (fun w => ENNReal.ofReal (exp (-(c * w ^ 2 / 2) + y * w))) =
      ENNReal.ofReal (tiltConst m v c y) • gaussianReal (tiltMeanG m v c y) (tiltVar v c)
theorem normalPosterior_eq_gaussian (ha : 0 < a) (hβ : 0 < β) (x : Fin n → ℝ) :
    normalPosterior a β x = gaussianReal (postMean a β x) (postVar a β n)
theorem integral_abs_centred_negLoss_cube_le (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    ∫ w, |negLoss x w - ∫ w', negLoss x w' ∂gaussianReal m v| ^ 3 ∂gaussianReal m v ≤
      4 * (absMom3 * |x - m| ^ 3 * √(v : ℝ) ^ 3 + absMomSq3 * ((v : ℝ) / 2) ^ 3)
theorem abs_sub_tiltMeanG_le (hv : v ≠ 0) (ht : 0 ≤ t) : |x - tiltMeanG m v t (t * x)| ≤ |x - m|
theorem coe_tiltVar_le (hv : v ≠ 0) (ht : 0 ≤ t) : ((tiltVar v t : ℝ≥0) : ℝ) ≤ v
theorem tiltAbsThird_negLoss_le (hv : v ≠ 0) (x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    tiltAbsThird (negLoss x) (gaussianReal m v) t ≤ envelope v m x
theorem abs_predictiveRemainder_negLoss_le (hv : v ≠ 0) (x : ℝ) :
    |predictiveRemainder (negLoss x) (gaussianReal m v)| ≤ envelope v m x / 6
theorem measurable_predictiveRemainder_negLoss (v : ℝ≥0) :
    Measurable fun p : ℝ × ℝ => predictiveRemainder (negLoss p.2) (gaussianReal p.1 v)
theorem integral_abs_remainder_le [IsProbabilityMeasure P] (ha : 0 < a) (hβ : 0 < β)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) (n : ℕ) :
    ∫ ω, |remainder a β n X Y ω| ∂P ≤ remainderBound a β n
theorem normalLocation_predictive_remainder_L1 [IsProbabilityMeasure P] (ha : 0 < a) (hβ : 0 < β)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, |remainder a β n X Y ω| ∂P) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ ω, (1 / (n : ℝ)) * ∑ i : Fin n, |remainder a β n X (X i) ω| ∂P) atTop (𝓝 0)
```
Design notes. (a) Measurability of `R` in `(m, x)` is obtained WITHOUT a closed form of `R`: `cgf`, mean and
variance are parametric Bochner integrals over the standard Gaussian after `N(m,v) = (N(0,1)).map (m + √v ·)`,
so `StronglyMeasurable.integral_prod_right'` applies. (b) Independence of the data is NOT used: the crude bound
`(∑|xᵢ|)³ ≤ n² ∑|xᵢ|³` gives `𝔼|m_n|³ ≤ (βn/d_n)³ absMom3 ≤ absMom3`, and `n·d_n^{−3/2} → 0` suffices. So the
hypotheses are only the marginal laws `HasLaw (X i) N(0,1)`, `HasLaw Y N(0,1)`. (c) The third-moment constants are
never evaluated. (d) The training certificate is stated with the empirical average `(1/n) ∑_{i<n} |R_n(Xᵢ)|`.

## 2. Rank 5 (CCCLIX–CCCLX)

The call-site audit found no instantiation of `GaussianField.ofIsGaussian/ofIsGaussianCertificates` from the
Taylor-data law, so the adapter was built.

`Grammar/L1SeqGaussianLaw.lean`:
```lean
theorem isGaussian_of_truncations (hν : SummableCoordL2 ν id) (hmean : ∀ j, ∫ a, a j ∂ν = 0)
    (hG : ∀ F : Finset ι, IsGaussian (ν.map (truncate F))) : IsGaussian ν
theorem integral_dual_eq_zero (hν : SummableCoordL2 ν id) (hmean : ∀ j, ∫ a, a j ∂ν = 0)
    (L : StrongDual ℝ (L1Seq ι)) : ∫ a, L a ∂ν = 0
theorem isGaussian_of_marginals (hY : SummableCoordL2 P Y)
    (hmarg : ∀ F, ν.map (finiteCoords F) = gaussianTarget (fun ω => finiteCoords F (Y ω)) P) : IsGaussian ν
theorem clt_l1_isGaussian (hY : SummableCoordL2 P (Y 0)) (hindep : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hYm : ∀ i, Measurable (Y i)) :
    ∃ ν : ProbabilityMeasure (L1Seq ι), IsGaussian (ν : Measure (L1Seq ι)) ∧
      TendstoInDistribution (empiricalSum Y P) atTop id (fun _ => P) (ν : Measure (L1Seq ι)) ∧
      (∀ F : Finset ι, (ν : Measure (L1Seq ι)).map (finiteCoords F) =
        gaussianTarget (fun ω => finiteCoords F (Y 0 ω)) P) ∧
      ∀ F : Finset ι, ∫⁻ x, ‖x - truncate F x‖ₑ ∂(ν : Measure (L1Seq ι)) ≤
        ENNReal.ofReal (sigmaTail P (Y 0) F)
```
Proof route: `truncate F = embedCoords F ∘ finiteCoords F` so `ν.map (truncate F)` is Gaussian (Mathlib instance);
along a covering exhaustion `F_k`, `L ∘ T_{F_k} → L` pointwise with bound `‖L‖‖a‖`; `‖a‖ ∈ L²(ν)` from the
summable coordinate `L²` norms; dominated convergence transports means (all zero), variances and `charFunDual`;
Mathlib's `isGaussian_iff_charFunDual_eq` closes. The coordinate second moments of the CLT limit are the data
variances (`integral_coord_sq_eq`), so `SummableCoordL2 ν id` follows from `SummableCoordL2 P (Y 0)`.

`Grammar/L1SeqSynthesis.lean` (`φ : ι → C(K,ℝ)`, `hφ : ∀ r, ‖φ r‖ ≤ M`, `K` compact metric):
```lean
noncomputable def synthesisCLM : L1Seq ι →L[ℝ] C(K, ℝ)          -- T a = ∑' r, a r • φ r
theorem norm_synthesisCLM_le (a) : ‖synthesisCLM φ hφ a‖ ≤ M * ‖a‖
theorem synthesisCLM_eval (a y) : synthesisCLM φ hφ a y = ∑' r, a r * φ r y
noncomputable def synthesisKernel (ν : Measure (L1Seq ι)) (hν : Integrable (fun a => ‖a‖ ^ 2) ν) : PSDKernel K
  -- C y z := ∫ a, T a y * T a z ∂ν ; symmetric, PSD, continuous (dominated convergence, bound M²‖a‖²)
theorem integrable_norm_sq_of_isGaussian (ν) [IsGaussian ν] : Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) ν
noncomputable def GaussianField.ofL1TaylorLimit (ν) [IsGaussian ν]
    (hmean : ∀ L : StrongDual ℝ (L1Seq ι), ∫ a, L a ∂ν = 0) :
    GaussianField (synthesisKernel φ hφ ν (integrable_norm_sq_of_isGaussian ν)) ν
  -- := GaussianField.ofIsGaussianCertificates _ ν T T.continuous.measurable (mean from hmean) (fun _ _ => rfl)
@[simp] theorem GaussianField.ofL1TaylorLimit_G : (ofL1TaylorLimit φ hφ ν hmean).G = synthesisCLM φ hφ
theorem integral_compactH_ofL1TaylorLimit ... : ∫ a, compactH β lam ρ (T a) ∂ν = β * ∫ a, compactV ρ β lam 𝒞 (T a) ∂ν
theorem exists_gaussianField_of_clt (hY hindep hident hYm) :
    ∃ ν : ProbabilityMeasure (L1Seq ι), ∃ hν : Integrable (fun a : L1Seq ι => ‖a‖ ^ 2) ν,
      IsGaussian (ν : Measure _) ∧ TendstoInDistribution (empiricalSum Y P) atTop id (fun _ => P) ν ∧
      ∃ Γ : GaussianField (synthesisKernel φ hφ ν hν) ν, Γ.G = synthesisCLM φ hφ
```
Design choice: the kernel is DEFINED as the field covariance, so the covariance certificate of the adapter is
`rfl`. NOT proved: the identification `C(y,z) = ∑_{r,s} Cov_ν(a_r,a_s) φ_r(y) φ_s(z)` (double series; would need
Cauchy–Schwarz `|Cov| ≤ σ_rσ_s`, `Summable.mul_of_nonneg` and the exhaustion limit), and any instantiation with the
model's chart data (monomial basis on a compact box; the uniform bound `sup‖φ_r‖ ≤ M` is a hypothesis).

## 3. What was NOT done

* **The thin quartet instantiation** `normalLocation_expected_quartet` was not attempted. Reasons: (i) it needs the
  Gibbs and variance-correction `L¹` transfers and the two-sign normalisation check, which are genuinely new
  calculations with the library's fluctuation-function quartet (definitions below), not a corollary of the remainder
  certificates; (ii) your stopping rule said to stop with the remainder theorem if the adapter is not an elementary
  calculation. The remainder component is available as `normalLocation_predictive_remainder_L1`.
  The actual library definitions, for your normalisation check:
  `fluctuation β lam a = ∫_{t>0} t^{lam−1} exp(−β t + β a √t) dt` (paper `S_λ(a)`);
  `quartetD β lam ρ g = ∑ᵢ ρᵢ S_lam(gᵢ)`; `quartetN i = ρᵢ S_{lam+1/2}(gᵢ)`; `quartetW i = N_i/D`;
  `quartetR i = ρᵢ S_{lam+1}(gᵢ)/D`; `quartetM2 = ∑ R_i`; `quartetH = ∑ gᵢ Wᵢ`; `quartetQ b = ∑ᵢⱼ bᵢⱼ Wᵢ Wⱼ`;
  `quartetV b c = c·M2 − Q`; `bayesCombination β lam ρ b c : Fin 4 → (Fin m → ℝ) → ℝ` = `(M2, M2 − H, M2 − V/2,
  M2 − H − V/2)`; `bayesValue β lam ν = (lam/β + ν, lam/β − ν, (lam−ν)/β + ν, (lam−ν)/β − ν)`;
  `expected_quartet_of_L1_transfer` (CCCLV) needs `g_n ⇒ G ~ gaussianVector A`, `UniformMoments`, `hc : (AAᵀ)ᵢᵢ = c`,
  and `𝔼|B_{n,j} − bayesCombination … j (g_n)| → 0`.
* **The kernel double-series identification** (above).
* **Independence** was not needed for the model test; the note says so.

## 4. The note (pin `a19cc7e`; Overleaf clone commits local only)

New after `prop:predictive_remainder` (its trailing paragraph now says: "its general discharge in a statistical
model … is not formalised, but the normal-location case is (Prop.)"):

> **Prop. (The predictive remainder in the normal-location model).** Take the normal-location model X ~ N(w,1) with
> prior N(0,a⁻¹), a>0, tempered at inverse temperature β>0. The tempered posterior after the observations x₁..xₙ is
> N(m_n, d_n⁻¹) with d_n = a+βn and m_n = β∑xᵢ/d_n•. For the excess loss f(x,w) = w²/2 − xw under any N(m,v), v>0,
> the tilted laws Π_t ∝ e^{−tf}N(m,v), t∈[0,1], are Gaussian with |x−m_t| ≤ |x−m| and v_t ≤ v••, and the absolute
> centred third moment of f under N(m,v) is at most S(v,m,x) = 4(C₃|x−m|³v^{3/2} + C₆(v/2)³), C₃ = E|Z|³,
> C₆ = E|Z²−1|³, Z ~ N(0,1)•; hence the tilted third moments are at most S(v,m,x) uniformly in t∈[0,1]• and
> |R| ≤ S(v,m,x)/6•. The remainder is a measurable function of (m,x)•. If the training points and the test point X*
> have standard normal marginal laws (independence is not used), then E|R_n| ≤ (32C₃²d_n^{−3/2} + C₆d_n^{−3}/2)/6•,
> so both n E|R_n(X*)| → 0 and n E (1/n)∑_{i≤n}|R_n(Xᵢ)| → 0•.

New paragraph in the Fernique subsection:

> **The Banach law of the ℓ¹ data limit.** The limit law ν of the ℓ¹ central limit theorem is a Gaussian measure on
> ℓ¹: every continuous linear functional has a real Gaussian law••, because the finite truncations T_F of ν are
> Gaussian and L∘T_{F_k} → L with the dominating bound ‖L‖‖a‖₁, so means, variances and characteristic functions pass
> to the limit. For basis functions φ_r ∈ C(K) with sup_r‖φ_r‖∞ ≤ M the synthesis map T(a) = ∑ a_rφ_r is a bounded
> linear map ℓ¹ → C(K) with ‖T(a)‖∞ ≤ M‖a‖₁••, so T under ν is a centred Gaussian Borel law on C(K) whose covariance
> C(y,z) = ∫T(a)(y)T(a)(z)dν(a) is a continuous positive semidefinite kernel•; the constructor yields a Gaussian field
> with this kernel••, to which item (3) of the compact-base proposition applies•. The uniform bound on the basis is a
> hypothesis (monomials on a compact subset of the unit box satisfy it); the identification of this kernel with the
> double series ∑_{r,s} Cov_ν(a_r,a_s)φ_r(y)φ_s(z) of coefficient covariances, and the instantiation with the model's
> chart data, are not formalised.

Interface table: "Expected errors / Not supplied" now reads "all three inputs in general (the remainder input is
discharged in the normal-location model, Prop.); none is supplied by a raw-core limit"; "Compact Gaussian base / Not
supplied": "Gaussian-process existence in general (supplied for the ℓ¹ limit law with a uniformly bounded basis)";
"Banach-law adapter / Formal output" adds "for the ℓ¹ limit law and a uniformly bounded basis, the synthesised field
with the field covariance as kernel", "Not supplied": "a Gaussian law constructed from the kernel alone; the
double-series identification of the synthesised kernel".

## 5. Questions

1. **Acceptance and wording** of the model test and Rank 5 as landed: any statement that overclaims or is stated in
   the wrong mode (the two certificates use only marginal laws; the kernel is the field covariance by definition).
2. **The thin quartet instantiation.** Given the actual definitions in §3, please either (a) verify the two-sign
   normal-location identification (λ = 1/2? g_n = (√2 Z_n, −√2 Z_n)? b = [[2,−2],[−2,2]], c = 2, weights ρ = ?)
   against `fluctuation`/`quartetD`/… and specify the three `L¹` transfers concretely enough to code, with a size
   estimate, or (b) confirm that the programme closes with the remainder theorem alone and the note records the
   missing identification as a non-claim. Our default is (b) unless the check is genuinely short.
3. **Kernel identification.** Is the double-series identification of `synthesisKernel` with the coefficient
   covariances worth one unit, or is the field-covariance kernel the right stopping point?
4. **Closure.** Please run your §4 checklist against the passages quoted in §4 above and give the final ledger
   wording (constructed vs consumed; modes of convergence; fresh vs training expectations; parameters), and the exact
   closing sentence for the note. If anything else is required before the note programme is closed, name it with a
   size estimate.

Answer in your usual structured form: Decision, per-question verdicts with exact wording, a ranked list of any
remaining units (or "none"), and explicit non-claims.
