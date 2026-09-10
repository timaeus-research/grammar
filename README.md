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
uniform finite-chart assembly), and the geometric bridge to the paper's main theorem
`thm:expectation_expansion`, conditional on a certified resolution presentation.

The library `Grammar` has 402 modules and no `sorry` or additional axioms. The
headline theorems, their gates, the independent statement-level reviews and the
explicit non-claims are indexed in [`Grammar/HEADLINES.md`](Grammar/HEADLINES.md);
a one-page layer map of the spatial, random-data and geometric-bridge programmes is
[`Grammar/THEOREM_MAP.md`](Grammar/THEOREM_MAP.md). Per-stage retrospectives are in
[`retrospectives/`](retrospectives/); the direction consults and review logs in
[`tide-log/`](tide-log/).

## Main results

| | Theorem | File |
|---|---|---|
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

In progress (Astra #53): the central limit theorem in `ℓ¹` for the empirical fluctuation
data — `ℓ¹` coordinate infrastructure and the summable-coordinate-`L²` moment hypothesis
(`Grammar/L1Seq.lean`), and the `ℓ¹` upgrade from finite-dimensional convergence with
uniform tails (`Grammar/L1SeqUpgrade.lean`).

What is **not** formalised: resolution of singularities (Hironaka) and the existence of
the certified chart presentation and adapted partition of unity; the empirical-process
CLT bridge from the paper's Hypothesis I to the data-space convergence assumed by the
stochastic theorems (in progress); all-orders division of asymptotic expansions. The
mirror `grammar_lean.tex` (Overleaf) records every formalised statement with a dot and
the non-claims in Lean remarks.

## Building

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
