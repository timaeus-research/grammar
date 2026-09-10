# grammar

A Lean 4 + Mathlib formalisation of Sections 3–4 of *Grammar (Expectations and the
Exceptional Divisor)* (Ben Gerraty, Daniel Murfet, 2026): the fluctuation
function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt + βa√t} dt`, the normal-crossing block
programme, the Taylor-tree asymptotic expansion `thm:TaylorTree` /
`cor:standardintegralexp` of the standard integral

    Z(β, n; ξ, η) = ∫_{(0,b]^d} η(u) u^h exp(−βn u^{2k} + β√n u^k ξ(u)) du

in every positive dimension (under the paper's holomorphic-polydisc hypothesis and
with the paper's coefficient data `Re(∂^γ F(0)/γ!)`), the population expansion of §3
with its first-nonzero selection and flatness, the spatial-phase and random-data
programme (leading and next-logarithmic order, posterior laws, random fields,
uniform finite-chart assembly), the geometric bridge to the paper's main theorem
`thm:expectation_expansion`, conditional on a certified resolution presentation, and
the central limit theorem in `ℓ¹` for the empirical fluctuation data that discharges
the data premise of the stochastic theorem `thm:strataempiricalexpansion`, with the
chart moment certificate derived from the order-zero envelope of the paper's
Hypothesis I under the division bridge, and all charts treated jointly from one sample.

The library `Grammar` has 420 modules and no `sorry` or additional axioms. The
headline theorems, their gates, the independent statement-level reviews and the
explicit non-claims are indexed in [`Grammar/HEADLINES.md`](Grammar/HEADLINES.md);
a one-page layer map of the spatial, random-data and geometric-bridge programmes is
[`Grammar/THEOREM_MAP.md`](Grammar/THEOREM_MAP.md). Per-stage retrospectives are in
[`retrospectives/`](retrospectives/); the direction consults and review logs in
[`tide-log/`](tide-log/).

## Main results

| | Theorem | File |
|---|---|---|
| CXXV | **the hironaka adapter**: grammar depends on `timaeus-research/hironaka` (Lean/Mathlib `v4.33.1`), consumed through axiom-clean declarations; hironaka's sublevel asymptotics are grammar's two-sided sublevel growth, so **the population Laplace exponent pair of a real-analytic nonnegative phase** holds on every small cube around a zero, conditional on Bierstone–Milman's Theorem 3.2 in chart form (`Q n`); partial-resolution charts are resolution charts covering a.e.; orthant reflection as a weighted measure identity | `Grammar/HironakaAdapter.lean` (`laplaceTheta_of_analyticOnNhd_nonneg_of_Q`), `OrthantReflection.lean` |
| CXXIII–CXXIV | **what the resolution input available today determines** (the chart form of `timaeus-research/hironaka`, continuous units): two-sided sublevel growth `μ{K ≤ t} ≍ t^λ(−log t)^q` implies two-sided Laplace growth `∫ e^{−NK} dμ ≍ N^{−λ}(log N)^q`, weighted and for the population integral; the dominant exponent pair of a finite positive family; the exact chart transport of a partial-resolution chart and the normalised-indicator partition, assembling to the restricted measure; the localisation obstruction (a chart-exact analytic amplitude cannot absorb an exact sublevel cutoff) | `Grammar/LaplaceExponentBounds.lean`, `DominantExponentPair.lean`, `ResolutionTransport.lean`, `LocalisationObstruction.lean` |
| CXXII | **the concrete tangential reconstruction**: `(T z)(v)_j = ∑_α z_{(j,α)} (θ(v)/ρ)^α` is a continuous linear map of norm `≤ 1` from `ℓ¹` over the latent index into `C(K, DataSpace d)`, joint version into `JointData K n`; tangential certificates (bi-indexed joint Cauchy envelope) give the weighted `ℓ¹` datum, the chart moment certificate and the identification with the tangential power series; the assembled stochastic expansion with concrete tangential data | `Grammar/TangentialReconstruct.lean`, `TangentialCertificate.lean` (`assembled_expansion_of_tangential`) |
| CXIX–CXXI | **Hypothesis I and joint charts**: measurable Cauchy coefficients in the sample point, the torus `L²` certificate and the division bridge `f(x,π_ℂw) = w^k a(x,w)` giving the chart moment certificate from Hypothesis I's order-zero envelope, the phase of the sample datum identified with the empirical process `ξ_n`, and joint convergence of all chart data from one sample with the cross-chart covariance | `Grammar/PolyCoeffMeasurable.lean`, `TorusCertificate.lean`, `AnalyticCertificate.lean`, `JointSample.lean` |
| CXVIII | **stochastic expansion with the data premise discharged**: for an i.i.d. sample whose chart Taylor coefficients satisfy the chart moment certificate, the canonical coefficients and ordered normalised remainders at the sample datum converge in distribution to those at the `ℓ¹` Gaussian limit | `Grammar/SampleExpansion.lean` (`sample_stochastic_expansion`) |
| CXIV–CXVII | **the CLT in `ℓ¹`** under summable coordinate `L²` norms (finite-dimensional Cramér–Wold CLT with the explicit Gaussian target, uniform empirical tails, compactness and tightness in `ℓ¹`, Gaussian limit by Prokhorov, the `ℓ¹` upgrade), and the sample datum with the paper's empirical Taylor coefficients | `Grammar/CLTFiniteDim.lean`, `EmpiricalTail.lean`, `L1SeqTight.lean`, `L1SeqGaussianLimit.lean`, `L1SeqCLT.lean` (`clt_l1`), `SampleDatum.lean` |
| CXIII | **conditional geometric main theorem**: the resolved population integral `∫ F e^{−NK} dμ` of a localisation datum with adapted strata data is a cutoff expansion with the assembled canonical coefficients (`thm:expectation_expansion`), with an exponentially small residual, the Taylor–moment form of the tubular expansion, and fibre-linear invariance of the moment–jet contractions | `Grammar/GeometricMainTheorem.lean` (`expectation_expansion_of_adaptedStrataData`) |
| CVII–CXII | measured localisation, weighted chart presentations with measure-transport certificates (`chart_integral_eq_tanIntegral`), normal jets and `lem:normal_deriv`, moment functionals and `eq:pushforward_local`, the absolutely convergent Taylor–moment representation and `eq:tubular_expansion` | `Grammar/Localisation.lean`, `ChartPresentation.lean`, `NormalJet.lean`, `MomentFunctional.lean`, `TaylorMoment.lean`, `ChartTaylorMoment.lean` |
| CIV–CVI | uniform finite-chart assembly at the next logarithmic order, chart-allocation corrections, the joint random assembled law | `Grammar/UniformAssembly.lean`, `ChartAllocation.lean`, `RandomAssembled.lean` |
| XCV–CII | uniform spatial two-term theorem on coefficient balls; random next-log evidence, posterior energy, Laplace transforms, free energy and evidence ratios jointly with the data on the Polish admissible domain | `Grammar/UniformSpatialTwoTerm.lean`, `RandomNextLogEvidence.lean`, `RandomNextLogPosterior.lean`, `RandomMixedVector.lean` |
| LXXII–XCIV | arbitrary continuous spatial phases: only the face restriction survives at leading order; explicit finite-part second coefficient `B`; transverse sensitivity; joint weak convergence of `(NK, u)`; independence iff face-constant phase; moving phases; graph-law and kernel-law transfer; random phase fields | `Grammar/SpatialPhaseLeading.lean`, `SpatialSecondCoeffExplicit.lean`, `SpatialJointConvergence.lean`, `GraphLawTransfer.lean`, `RandomFieldTransfer.lean` |
| XLIV–LXXI | §3 rewritten and formalised: population Taylor tree at `ξ = 0`, face functional, first nonzero term after cancellation, superpolynomial flatness, energy identity and first logarithmic corrections, constant-phase posterior law of `NK` and its Gamma-tilt limit | `Grammar/PopulationTaylorTree.lean`, `FirstNonzeroAsymptotic.lean`, `Flatness.lean`, `EnergyCorrection.lean`, `AssembledEnergyLaw.lean` |
| XXXIII | `thm:TaylorTree` with Taylor-derivative coefficient families, every positive dimension | `Grammar/TaylorTreeDerivatives.lean` (`thm_TaylorTree_taylor`) |
| XXXII | `thm:TaylorTree` under the holomorphic-polydisc hypothesis with the original integral | `Grammar/AnalyticTaylorTree.lean` |
| XXVII–XXX | Taylor tree for coefficient families: cutoff bound, `O(N^{-L}(log N)^{d-1})`, explicit coefficient series, derivative dictionary | `Grammar/FamilyTaylorTree.lean`, `BoxTaylorTree.lean`, `FamilyCoeffSeries.lean`, `FluctuationDerivativeMu.lean` |
| XXXIV–XXXVII | the stochastic Taylor tree: coefficients Lipschitz on the weighted-`ℓ¹` data space, convergence in distribution of coefficients and ordered normalised remainders, tangential integration, finite chart assembly | `Grammar/CoeffLipschitz.lean`, `StochasticTaylorTreeJoint.lean`, `TangentialData.lean`, `ChartAssemblyGlobal.lean` |
| XX–XXI | normal-crossing model `N(x₀x₁,1)`: posterior MGF of `√n x₀x₁` converges to `e^{zθ+θ²/2}`; leading Mellin (zeta) coefficient as a real-axis Abelian limit | `Grammar/NormalCrossingModel.lean`, `NormalCrossingLaw.lean`, `MellinCoefficient.lean` |
| I–XIX | fluctuation ladder, state densities, chart assembly, stochastic posterior quotients | see `HEADLINES.md` |

What is **not** formalised: resolution of singularities itself (Hironaka — proved leaf-wise in
the dependency `timaeus-research/hironaka`, whose chart form with continuous units feeds
CXXIII–CXXV through `Grammar/HironakaAdapter.lean` with `Q n` as an explicit hypothesis) and the existence of
the certified chart presentation and adapted partition of unity, including the
complexified chart, its torus inclusion in the Hypothesis-I neighbourhood and the
analytic divisibility of the pulled-back log-likelihood ratio, and the joint product-polydisc
Cauchy estimate behind the tangential certificates; all-orders division of asymptotic
expansions. The
mirror `grammar_lean.tex` (Overleaf) records every formalised statement with a dot and
the non-claims in Lean remarks.

## Building

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`; `timaeus-research/hironaka` is a pinned
lake dependency (only its import closure is built). `lake exe cache get && lake build`.

```bash
lake exe cache get
lake build
scripts/sorries
```

Toolchain `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0`.

## Provenance

Factored out of [`timaeus-research/laplace`](https://github.com/timaeus-research/laplace)
(directory `Laplace/Grammar` on branch `tide/grammar-normal-crossing-model`, pin `b48bc6f`)
on 2026-09-07 with `git subtree split`; the namespace `Laplace.Grammar` became `Grammar`.
Retrospectives and consult logs predating the split refer to the old paths.
