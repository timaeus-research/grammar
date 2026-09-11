## First three modules: proposed contracts

The declarations below are **new API proposals**, not claimed upstream declaration names. Use the dependency’s actual ambient Euclidean type for `X`; notation `ℝ^I` means the corresponding finite-dimensional Euclidean coordinate space.

### 1. `ResolvedSpace.ChartTransport` — priority 1

Package `PartialResolution`, its monomial-chart certificates, and a compatible `ResolutionCover`. Do **not** introduce gluing data.

```lean
theorem integral_eq_sum_chart_integrals
    (hf : IntegrableOn f K)
    (hchart : ∀ i, IntegrableOn
      (fun y => ρ i (φ i y) * f (φ i y) *
        |detJacobian (φ i) y|) (dom i)) :
    (∫ w in K, f w) =
      ∑ i, ∫ y in dom i,
        ρ i (φ i y) * f (φ i y) *
          |detJacobian (φ i) y|
```

The bundled hypotheses must include **the existing `ResolutionCover` normalization and measurability conditions**, not merely a multiplicity bound. Obtain this theorem from Grammar’s existing weighted cover/change-of-variables theorem.

Specialize to
\[
f(w)=a(w)e^{-nK(w)}p(w).
\]
Then prove the chart integrand agrees, on `dom i`, with
\[
\rho_i(\phi_i y)a(\phi_i y)p(\phi_i y)
 e^{-n\,u_i(y)y^{e_i}}\,|v_i(y)|\prod_j|y_j|^{h_{ij}}.
\]

Use `IsMonomialChart` and CXCIX’s analytic-unit upgrade. The absolute Jacobian uses **`|v_i|`**, not `v_i` without a positivity certificate. Neither even exponents nor removal of the phase unit follows automatically.

The target integral is over **`K`**, not all `W`: extending it requires support in `K` or a separately handled complement.

### 2. `ResolvedSpace.CoordinateDivisorTube` — priority 2

For `I ⊆ {j | e j > 0}`, construct the orthogonal coordinate splitting
\[
X \simeq \mathbb R^{I^c}\times\mathbb R^I,
\qquad J_I(v,z)=\text{coordinate insertion}.
\]

New contracts:

```lean
theorem coordinateSplit_measurePreserving :
    MeasurePreserving split volume (volume.prod volume)

theorem coordinateTube_integral
    (hF : Integrable F) :
    (∫ y, F y) = ∫ v, ∫ z, F (join v z)
```

Also certify:

* the plane `P_I = {y | ∀ j ∈ I, y j = 0}` has the coordinate LCI atlas;
* its tubular map is `join`, normal projection is `join v 0`;
* its ambient Jacobian density is `1`;
* the radius-`R` tube corresponds to `‖z‖ < R`.

Use `CoordinateStratumBundle`, strucdual’s `stratum_tube`, and Mathlib’s product-measure/Fubini API (`MeasureTheory.integral_prod`).

Crucially,
\[
S_{I,i}=P_I\cap W_i\cap
 \{y:\forall j\notin I,\ e_{ij}>0\Rightarrow y_j\ne0\}
\]
is an **open subset of the plane**, not the whole plane. An arbitrary fixed-radius tube over it need not lie in `W_i`. Work in the global coordinate-plane tube, with measurable restrictions recording the actual allowed points.

### 3. `ResolvedSpace.WeightedTubularMoments` — priority 3

Let `A(v,z)` be the observable, `c(v,z) ≥ 0` the entire remaining weight, and `T_r(v,z)` its certified normal Taylor terms, including factorial conventions.

A precise sufficient contract is:

* `c` measurable and integrable against product Lebesgue measure;
* a positive radius `R(v)` and a fibre power-series certificate for `A(v,·)` at zero;
* `c(v,z) ≠ 0` implies `‖z‖ < R(v)`, almost everywhere;
* that certificate gives `HasSum (fun r => T_r(v,z)) (A(v,z))` there;
* each `c * T_r` is integrable;
* `Summable (fun r => ∫ v, ∫ z, |c(v,z) * T_r(v,z)|)`.

Then prove:

```lean
theorem weighted_tube_series :
    (∫ v, ∫ z, c (v,z) * A (v,z)) =
      ∑' r, ∫ v, ∫ z, c (v,z) * T r (v,z)
```

These hypotheses imply integrability of `c*A`; alternatively require it explicitly for easier downstream use. A single integrable dominator of `c * ∑' r, |T_r|` is a convenient constructor for the summability certificate.

Use CLXXI/CLXXII’s certified normal-moment presentation and CCXIX’s tube identity; discharge integration/interchange obligations using Mathlib’s integrable-series and Fubini results. Radius certificates alone are **not** sufficient.

Define
\[
d\nu_v(z)=c(v,z)\,dz,\quad q(v)=\nu_v(1).
\]
Prove the projection pushforward has density `q(v)`. Thus one may use either raw moments with base measure `dv`, or normalized moments with base measure `q(v)dv`, defining the zero-mass case separately. Do not count the marginal density twice.

## What “resolved space” means

Use **A as the theorem architecture, C as optional packaging**:

```lean
ChartResolutionSpace := Σ i, {y // y ∈ W i}
```

This is a disjoint union of open Euclidean manifolds, with the chartwise analytic map `π(i,y)=φ_i(y)`. Integration is restricted to the compact `dom i` and weighted by `ρ_i ∘ φ_i`.

Do not call the disjoint union of the **compact domains** a boundary-free manifold. Nor does the open disjoint union automatically give a proper resolution map to `W`.

C introduces no extra geometry over A; it supplies a convenient ambient object on which to state theorems “on the chart resolution.” The honest replacement for the paper’s term is
\[
Z_{n;i,I}[a]
=\int_{\text{chart piece }P_{i,I}}
 \rho_i(\phi_i y)\,a(\phi_i y)e^{-nK(\phi_i y)}
 p(\phi_i y)|\det D\phi_i(y)|\,dy.
\]
The global answer is a sum over **chart–stratum pairs**, not intrinsic global strata.

Option B is unavailable: off-exceptional inverse branches do not supply analytic transition extensions across the divisor.

## Density and the tubular contribution

For the desired expansion, choose
\[
A=a\circ\phi_i,\qquad
c=\mathbf1_{P_{i,I}}\,
(\rho_i\circ\phi_i)(p\circ\phi_i)
e^{-nK\circ\phi_i}|\det D\phi_i|.
\]
Assume these density factors are nonnegative; signed amplitudes need an appropriate signed formulation.

Keep cutoffs, cover weights, Jacobian units and prior **in the measure**, so Taylor derivatives act only on `a∘φ_i`. Putting everything into `F` gives an integration identity but generally the wrong derivative expansion; indicators and `ρ_i` need not be analytic.

Tangential monomial factors enter `c`. The phase remains the actual `u_i(y)y^{e_i}` unless an additional adapted-normal-form theorem removes its unit.

Beyond CLXXI/CLXXII, the tube machinery supplies:

1. the **derivation** of the fibre measure from ambient Lebesgue integration;
2. the identification of the weighted projection pushforward;
3. the base integral on `Stratum A` and compatibility with the coordinate-free contraction notation.

It does not manufacture new moment asymptotics.

## Remaining modules

### 4. `ResolvedSpace.MeasurableStratumPieces` — priority 4

Fix `ε>0`. Partition each `dom i` by
\[
I(y)=\{j:e_{ij}>0,\ |y_j|<\varepsilon\}.
\]
Assign equality to the complementary condition `≥ ε`.

Prove measurable, pairwise-disjoint, finite exhaustive pieces. Projecting an `I`-piece to `P_I` preserves nonzero complementary divisor coordinates. To ensure its base lies in `W_i`, require a certified projection/tube containment condition, obtainable using suitably small thresholds near compact `dom i`.

Each piece becomes a measurable subset of a coordinate tube, with possibly irregular fibre slices. No product-box assertion is needed.

The resulting integral decomposition is **exact**, including `I=∅`. Calling that last term exponentially small additionally requires a positive lower bound for `K∘φ_i` there and integrable amplitude.

### 5. `ResolvedSpace.PerChartStratumFormula` — priority 5

Combine modules 1–4 with CCXIX. State the weighted contraction-series formula on every certified chart–stratum piece, both in coordinates and on its LCI stratum. Radius/domination certificates are explicit arguments.

### 6. `ResolvedSpace.GlobalWeightedExpansion` — priority 6

Sum over `(i,I)`. Prove the exact resolved-chart formula for `Z_n[a]`, and connect it to existing chart asymptotics **only when each new weighted piece satisfies their hypotheses**.

Measurable tilings suffice for exact fibre integration; they do not automatically preserve analytic amplitude hypotheses or power–log asymptotics.

### 7. `ResolvedSpace.LeadingCoefficientInterface` — priority 7

Package leading-term certificates per piece and sum their coefficients, handling ties and possible cancellation. Reuse the unconditional exponent formula where its hypotheses and decomposition match. Do not infer positivity for signed observables.

## Explicit non-claims

This programme constructs neither a glued resolution nor intrinsic global divisor components, componentwise canonical `(k_i,h_i)`, global stratum tubes, or the paper’s smooth adapted partition of unity. It proves no analytic extension of transitions and no cover-independence of individual moments or coefficients. The **total integral** is cover-independent because each certified construction transports back to the same target integral; stronger geometric invariance needs additional data.
