# grammar

A Lean 4 + Mathlib formalisation of Section 4 of *Grammar (Expectations and the
Exceptional Divisor)* (Ben Gerraty, Daniel Murfet, 2026): the fluctuation
function `S_μ(a) = ∫₀^∞ t^{μ-1} e^{-βt + βa√t} dt`, the normal-crossing block
programme, and the Taylor-tree asymptotic expansion `thm:TaylorTree` /
`cor:standardintegralexp` of the standard integral

    Z(β, n; ξ, η) = ∫_{(0,b]^d} η(u) u^h exp(−βn u^{2k} + β√n u^k ξ(u)) du

in every positive dimension, under the paper's own hypothesis (holomorphic
extensions of `ξ, η` to a polydisc of radius `R > b`) and with the paper's
coefficient data `Re(∂^γ F(0)/γ!)`.

The library `Grammar` has 261 modules and no `sorry` or additional axioms. The
headline theorems, their gates, the independent statement-level reviews and the
explicit non-claims are indexed in [`Grammar/HEADLINES.md`](Grammar/HEADLINES.md).
Per-stage retrospectives are in [`retrospectives/`](retrospectives/); the consult
and review logs in [`tide-log/`](tide-log/).

## Main results

| | Theorem | File |
|---|---|---|
| XXXIII | `thm:TaylorTree` with Taylor-derivative coefficient families, every positive dimension | `Grammar/TaylorTreeDerivatives.lean` (`thm_TaylorTree_taylor`) |
| XXXII | `thm:TaylorTree` under the holomorphic-polydisc hypothesis with the original integral | `Grammar/AnalyticTaylorTree.lean` |
| XXVII–XXX | Taylor tree for coefficient families: cutoff bound, `O(N^{-L}(log N)^{d-1})`, explicit coefficient series, derivative dictionary | `Grammar/FamilyTaylorTree.lean`, `BoxTaylorTree.lean`, `FamilyCoeffSeries.lean`, `FluctuationDerivativeMu.lean` |
| XX–XX'' | normal-crossing model `N(x₀x₁,1)`: posterior MGF of `√n x₀x₁` converges to `e^{zθ+θ²/2}` | `Grammar/NormalCrossingModel.lean`, `NormalCrossingLaw.lean` |
| XXI | leading Mellin (zeta) coefficient as a real-axis Abelian limit | `Grammar/MellinCoefficient.lean` |
| I–XIX | fluctuation ladder, state densities, chart assembly, stochastic posterior quotients | see `HEADLINES.md` |

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
