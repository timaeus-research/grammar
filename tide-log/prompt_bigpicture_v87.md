# Consult #87 — grammar Lean: #86 programmes A and B landed; designing C (statistical transfer) against the library's empirical layer

Context: Lean 4 (Mathlib) autoformalisation of the Gerraty–Murfet "grammar" paper (library `Grammar`,
587 modules, axiom-clean). Since #86:

* **A (derived certificates), 4 units, complete**: CCLXXXI `WholeBoxSourceCertificate`
  (`boxSourceIntegral G p N = ∫_{productBox e y₀ ρ} G |det Dφ| (p∘φ) e^{−NK∘φ}`, the remainder-zero
  one-chart certificate from the box package alone, ★ `hasLeadingTerm_boxSourceIntegral`,
  `sourceDominantFace_pos`, ★★ `boxSourceIntegral_isEquivalent` for `G`, `p∘φ` positive on the
  closed box); CCLXXXII `BoxFamilyAssembly` (★ `IsMonomialChart.volume_image_inter_eq_zero` — the
  a.e.-disjointness criterion within one chart, via off-exceptional injectivity and
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`; `sourceCoeff_eq_of_cutoff`;
  `exists_mem_tiedCharts'`; `BoxFamily` with ★★ `targetIntegral_isEquivalent` for regions covered
  a.e. by the images of boxes with null pairwise intersections); CCLXXXIII `BlowUpCubeCharts`
  (hironaka's `blowUpChart` with the full block in dimension `d ≥ 2` on `[−1,1]^d` for `K = ∑ x_i²`:
  hand-built monomial charts, `cube = productBox e 0 1 = closedBall 0 1` (sup metric), wedges
  covering the cube exactly via hironaka's `blowUpChartBox_cover`, null diagonals, pair `(d/2, 0)`,
  ★★ `cubeIntegral_isEquivalent` for positive `F`, `p`); CCLXXXIV `BlowUpCubeGaussian`
  (★★★ `coeff_eq_pi_rpow`: the sum of the `d` whole-box coefficients is `π^{d/2}`, by uniqueness of
  certificates against the Gaussian factorisation `(∫_{−1}^{1} e^{−Nt²})^d` with the 1-D integral
  transported from CCLXXII; `cubeIntegral_isEquivalent_pi : ∫_{[−1,1]^d} e^{−N∑x_i²} ~ π^{d/2} N^{−d/2}`).
* **B (locality), 2 units, complete**: CCLXXXV `CoefficientLocality` (regions differing on a
  phase-gap set have exponentially close target integrals, ★ `HasLeadingTerm.targetIntegral_of_locality`,
  ★ `hasLeadingTerm_closedBall_iff_of_isolatedZero`); CCLXXXVI `SeparableBallRegression`
  (`∫_{−r}^{r} e^{−N t^{2k}} = Γ(1/(2k))/k · N^{−1/(2k)} − 2·tail` with Mathlib's Gamma integral and the
  tail bound `e^{−Nt^{2k}} ≤ e^{−(N−1)r^{2k}} e^{−t^{2k}}`; Fubini + `IsEquivalent.finsetProd` on the
  cube; locality to any region between two cubes; the continuity sandwich for a continuous
  nonnegative amplitude via `tendsto_div_of_approx_squeeze`: ★★ `Separable.region_isEquivalent :
  ∫_{Rg} f e^{−N∑x_i^{2k_i}} ~ f(0) ∏ Γ(1/(2k_i))/k_i · N^{−∑ 1/(2k_i)}`).
* The mirror's not-yet-formalised clause now also names "the transfer of the population coefficients
  to the empirical posterior (which does not hold in general: the empirical fluctuation survives at
  order one on the shrinking neighbourhoods)" — your #86 guardrail, recorded.

## The library's empirical layer (what exists; please read before designing C)
Objects: a coefficient family / chart phase `φ(v) = v^k` in a monomial box chart with amplitude
`η_A(v) v^h`; the **sample datum** with the paper's empirical Taylor coefficients `ξ_n` as phase
coordinates; the sampling identity `−β∑_{i<n} f(X_i, b·u) = −βn φ(u)² + β√n φ(u) ξ_n(u)` (`N = n`,
`ξ_n = −ζ_n`, the centred empirical process of the coefficient); the certified box core
`Z(n; sampleDatum) = ∫_{(0,b]^d} η_A(v) v^h e^{−β∑_{i<n} f(X_i,v)} dv` (CLXXXI). Results:
* **Empirical-process CLT in `ℓ¹`** (CXIV–CXVIII): under a Cauchy envelope on the coefficient family,
  `S_n ⇒ ν` (Gaussian) and hence `thm:strataempiricalexpansion` with the data premise discharged:
  canonical coefficients and normalised remainders at the sample datum converge IN DISTRIBUTION to
  those at the Gaussian limit.
* **Conditional empirical assembly at the scale `A_n = n^λ/(log n)^{m−1}`** (CXLVIII): Slutsky
  assembly `A_n Z_n^core ⇒ L`, `A_n Rem_n → 0` in probability ⇒ `A_n Z_n ⇒ L`; with uniform
  `p`-moments, `E[A_n Z_n] → E L` and `E Z_n ∼ E L · n^{−λ}(log n)^{m−1}` when `E L > 0`;
  **`log Z_n/log n → −λ` in probability**. Non-claim recorded: `E L` is the expectation of the
  LIMITING EMPIRICAL coefficient, not the population coefficient.
* **Uniform `p`-moments from sub-Gaussian phases** (CXLIX–CL, CLVII, CLXXXII): `E[D_ρ(ξ_n)^p] ≤ B^p`
  uniformly in `n` for bounded/sub-Gaussian observations; the annealed compact-base denominator
  `E D_ρ(G) = Γ(λ)∫_K [β(1−βC(x,x)/2)]^{−λ} dρ` (divergence at `2 ≤ βC`); the expectation assembly
  `E[A_n(Z^core_n + Rem_n)] → E L` for certified sub-Gaussian cores; the uniform full-box
  sub-Gaussian hypothesis inherited by the normalised empirical phase with the same proxy.
* **Positive-gap remainders for the empirical phase** (CXXXV, CXXXIX): on `{K ≥ κ}`, under
  `sup|ξ_n| ≤ ½√(nκ)` the remainder is `≤ e^{−nκ/4}·∫|F|`-type; the EXPECTED remainder from pointwise
  annealed exponential moments `E‖Rem‖ ≤ e^{−(1−θ)βnκ}∫g` (sub-Gaussian threshold `βc < 2`, Hoeffding
  for bounded i.i.d. coefficients) — not from the pathwise bound alone.
* **Gaussian averaging (the companion note)**: Schwinger–Dyson, Gaussian integration by parts
  `E[H] = βE[V]`, the Bayes quartet, the exact annealed identity `E₊Z_n(β) = ∫(E e^{−βf})^n dπ`, tilted
  Gaussian moments, insertion formulas, the bilocal two-point function with its critical line.
Population side (the deterministic theorems of #82–#86): `E_n[φ] → c_φ/c_1` for the Gibbs
population posterior `Z_n[φ]/Z_n[1]` with the explicit resolution coefficients; nothing is claimed
about `E_{w|D_n}`.

## Questions

**Q1 (C, the honest minimal programme).** Your #86 proposal: (C1) abstract perturbation transfer —
for the population posterior `μ_n` and the empirical unnormalised ratio `R_n = e^{−n(K̂_n − K)}`, if
`δ_n = ∫|R_n/A_n − 1| dμ_n → 0` for positive random scalars `A_n` then `|μ̂_n(φ) − μ_n(φ)| ≤
2‖φ‖_∞ δ_n/(1−δ_n)`; (C2) concentration of the empirical posterior near `K^{−1}(0)` from uniform
loss convergence + a compact phase gap + prior mass near minimisers; (C3) constant-on-minimisers
observables `φ ≡ φ₀` on `K^{−1}(0)` have `E_{w|D_n}[φ] → φ₀`; (C4) the exact Gaussian companion
result under its hypotheses. Given the layer above:
 (a) C1 is a generic measure-theoretic lemma (I can land it today: probability measure `μ`, `R ≥ 0`
     integrable, `A > 0`, `δ := ∫|R/A − 1|dμ < 1`, then `∫ R dμ/A ∈ [1−δ, 1+δ]` and the bound). Confirm
     the statement and the right generality (bounded measurable `φ`; is the `2` sharp / is
     `‖φ‖_∞ δ_n/(1−δ_n)` cleaner with `φ` centred?).
 (b) C2: what is the honest hypothesis set? In the library's coordinates the empirical exponent is
     `−n K̂_n(w)` with `K̂_n = K − n^{−1/2}(√n φ ξ_n)·(…)`; the natural ULLN hypothesis is
     `sup_w |K̂_n(w) − K(w)| → 0` a.s. (bounded i.i.d. losses on a compact parameter space). Then on
     `{K ≥ κ}`: `K̂_n ≥ κ/2` eventually, so the empirical mass there is `≤ e^{−nκ/2}·prior mass`; on the
     complement `{K < κ}` near the zero set the empirical normaliser is `≥ e^{−n(κ+o(1))}·prior({K<κ}) `…
     this gives concentration `μ̂_n({K ≥ κ}) → 0` only if the normaliser is not itself exponentially
     smaller than `e^{−nκ/2}` — i.e. need `Ẑ_n ≥ e^{−n κ/4}` eventually, from the population lower
     bound `Z_n[1] ≥ c n^{−λ}` (CCLXXVI/CCLXXVIII give `Z_n[1] ~ c n^{−λ}`!) times `e^{−n·sup|K̂_n−K|}`
     — that needs `n·sup|K̂_n − K| = o(n)` i.e. just the ULLN ✓. So: **ULLN + the population
     certificate ⇒ empirical concentration `μ̂_n({K ≥ κ}) → 0` a.s.** Is this the theorem to state?
     Its inputs: `K ≥ 0`, `K̂_n` measurable in `(ω, w)`, `sup_w |K̂_n(ω,w) − K(w)| → 0` for a.e. `ω`
     (hypothesis; the library has Hoeffding/sub-Gaussian machinery but a UNIFORM law needs a
     covering/continuity argument — is `sup_w` uniform convergence an acceptable hypothesis, or
     should I derive it for bounded i.i.d. losses Lipschitz in `w` on a compact set?).
 (c) C3 follows from C2 + continuity of `φ` + `φ ≡ φ₀` on the zero set: `|E_{w|D_n}[φ] − φ₀| ≤
     sup_{K<κ}|φ − φ₀| + 2‖φ‖ μ̂_n({K ≥ κ})`, and `sup_{K<κ}|φ − φ₀| → 0` as `κ → 0` needs uniform
     continuity + `{K < κ}` shrinking to the zero set (compactness). Confirm.
 (d) The population limit `c_φ/c_1` vs `φ₀`: for `φ` constant on the zero set they coincide — a
     consistency theorem (`c_φ = φ₀ c_1`), provable from linearity of the coefficient
     (`productCoeffD_add/const` exist for the scalar package; for the Var/source packages?) plus
     "the coefficient of an observable vanishing on the zero set is zero"? The latter is FALSE in
     general (the coefficient sees the residual face, e.g. `E_n[x²] → J/I ≠ 0` in CCLXVIII where
     `x² = 0` on the zero set `{x = 0} ∪ {y = 0}`… no wait, `x²` does not vanish on `{y = 0}`; take
     `φ = x²y²` for `K = x²y⁴`: coefficient at the extremal pair… positive-dimensional zero sets make
     "constant on the zero set" the only safe hypothesis). Please state the correct consistency
     theorem (I suspect: `φ` continuous, `φ ≡ φ₀` on `K^{−1}(0) ∩ Rg` ⇒ `c_φ = φ₀ c_1`, via locality:
     `|c_φ − φ₀ c_1| ≤ sup_{K<κ}|φ−φ₀| · c_1`-type squeeze at each `κ` — the coefficient of `|φ − φ₀|`
     is `≤ sup_{K<κ}|φ−φ₀|·c_1 + 0`), and whether it is worth a unit.
 (e) C4: which exact Gaussian statement from the companion note is the honest "specialisation"?
     The library has the annealed identity and the tilted moments; the QUENCHED empirical
     posterior expectation is not there. Your #86 example (`m(a,b) = (a, ab)`) shows the empirical
     limit is random. Is there a clean theorem "the empirical posterior expectation of `b`-observables
     converges IN DISTRIBUTION to the random Gaussian-weighted functional" derivable from
     CXLVIII's Slutsky assembly (numerator and denominator jointly)? I.e. `E_{w|D_n}[φ] ⇒ L_φ/L_1`
     jointly — the ratio of the joint limit — as the honest empirical counterpart of
     `E_n[φ] → c_φ/c_1`. That seems the most valuable and is within reach IF the joint convergence
     `(A_n Z_n[φ], A_n Z_n[1]) ⇒ (L_φ, L_1)` is available (the field CLT gives joint convergence of
     the coefficients as functionals of the same Gaussian limit; `L_1 > 0` a.s.). Rank this against
     C2/C3.

**Q2 (D and E).** With A and B done, rank: C (as above), D (the exact constant-unit rectangular
kernel's log-polynomial: second coefficient ratio `(m−1)(log(uB) − Γ'(λ)/Γ(λ))`), E (the semantic
audit of the mirror: population vs empirical, intrinsic pair vs region coefficient, existence of a
resolution vs production of a certificate, normalised coefficient functionals vs pointwise
evaluation — I can do a pass adding explicit qualifiers). Recommend the order and the stopping point.

**Q3 (Mathlib).** For C1/C2: `MeasureTheory.integral_mono`, `norm_integral_le_of_norm_le`,
`IsProbabilityMeasure`; for the a.s. ULLN hypothesis, `∀ᵐ ω, Tendsto (fun n => ⨆ w, |…|) atTop (𝓝 0)`
with `⨆` over a compact set (or `sSup` of the image) — is `iSup` over a type the right form, or a
`∀ ε, ∀ᶠ n, ∀ w ∈ S, |…| ≤ ε` statement (which avoids suprema entirely)? Flag anything you believe
is missing.
