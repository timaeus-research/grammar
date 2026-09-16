## Recommendation

**Proceed through cube jets, without waiting for E6.** I would rank the routes:

1. **Extract a small, generic “coefficient on closed realizable jets” layer**, then instantiate it for a cube. Reuse the architecture of the resolved implementation, not its geometry.
2. **Implement the cube specialization directly** if extracting that abstraction would disturb landed code.
3. **Try the monomial resolved-data route only after a short definitional audit.** Being a resolution of a monomial phase does not imply that its pieces, amplitudes, coefficient normalization, and jet domains are your single cube.

There are three important corrections to the proposed argument:

- **Continuity on realizable jets alone does not justify extension to their closure.** You need a uniform-continuity/Cauchy-continuity estimate, normally a Lipschitz estimate on bounded jet sets.
- **Expansion uniqueness proves locality between globally smooth extensions.** It does not, by itself, identify the raw `empCoeffRect` applied to a merely locally smooth field with that extension-defined coefficient.
- **A coefficient law is not yet a stochastic asymptotic expansion of the empirical evidence.** The fixed-field expansion theorem does not automatically control the diagonal remainder with field `ζ_n` and asymptotic parameter `N = n`.

Also check that the atlas supplies **`∀ i, 0 < k α i`**. Resolution exponents can have zero components; that hypothesis is not automatic from being a charted resolution.

I use existing names exactly as supplied below. Proposed declarations are explicitly marked **new**. Without the repositories in view, I cannot responsibly supply additional exact greybook names or claim a particular current Mathlib signature has been verified.

---

## E2. Identify the representatives before doing probability

### Cheapest route: first make the equality simultaneous in \(u\) under \(\mu\)

Fix a chart and write \(K_\alpha\) for its closed box. Prove:

```lean
-- NEW; schematic
theorem ae_fa_eq_smoothRep_on_box :
    ∀ᵐ x ∂μ, ∀ u ∈ K α,
      D.fa α x u = (Rp α).f x u
```

The proof is precisely the countable-dense-set argument:

1. Choose a countable dense subset of the subtype `K α`.
2. Intersect the pointwise representative equalities over that subset.
3. For each surviving `x`, extend equality by continuity on `K α`.

This is preferable to repeating the dense-set argument on the sample space for every `n`. It also gives a reusable data-level representative comparison.

Use the order-zero representative equality from `ChartKernelRep`, after simplifying the zero-order iterated derivative. Check that the greybook representative represents **the same** `Q.a α u`: if it was constructed using a different analytic kernel witness, that identification is a prerequisite.

Then pull this conull event back through every `X i`. The only probabilistic input needed here is

```lean
∀ i, P.map (X i) = μ
```

together with the needed measurability. Independence is irrelevant. Countably intersect over `i`; intersect over charts as well if the chart index is finite/countable.

### Desired empirical equality

```lean
-- NEW; schematic
theorem ae_chartXi_eq_empField :
    ∀ᵐ ω ∂P, ∀ n α, ∀ u ∈ K α,
      chartXi X D.fa α n ω u =
        empField Q Rp α n ω u
```

On the resulting event, this is finite-sum congruence, using

```lean
chartMean Q α u = u ^ (A.k α)   -- schematic monomial notation
```

on the box. The mean identity is essential: agreement of representatives alone only identifies the uncentered sums.

Handle `n = 0` through the actual definitions rather than dividing by `√n` manually.

### Evidence equality

The next lemma should be a **deterministic congruence lemma** for the box integral, followed by the a.s. application:

```lean
-- NEW; schematic
theorem ae_chartEvidence_eq_empIntegralRect :
    ∀ᵐ ω ∂P, ∀ n α,
      chartEvidence X D α n ω =
        empIntegralRect
          (A.unitWt α) (empField Q Rp α n ω)
          (A.h α) (A.k α) (fun _ => rb α) n
```

Consume the already-landed greybook identity with `empBoxIntegral`, and then the grammar identity between the two integral presentations. If `rect` and `closedBox` differ on their boundary, use the existing integral convention/identity; do not silently treat the sets as definitionally equal.

### `unitWt` and `DeepVanishing`

These are separate issues:

- **Smoothness:** if `hAw` gives global \(C^\infty\) regularity of `unitWt`, it supplies the amplitude hypothesis. No additional extension of the weight is needed.
- **Deep vanishing:** ordinary resolution cutoffs do **not** automatically supply `DeepVanishing η b c`.

In particular, cutoffs can be nonzero on exceptional-divisor intersections—the very strata that produce leading poles. Being supported away from an outer chart boundary is not the same as vanishing near a deep coordinate stratum.

For some choices of `c`, the deep set might be empty, making the condition automatic. That must be proved from the actual definition and chart combinatorics. Therefore:

> Treat `DeepVanishing (A.unitWt α) b c` as an explicit Stage E hypothesis until a separate atlas lemma discharges it.

Do not infer it merely because `(μ,c)` is called “the top index.”

---

## E3. Globalize the field, but distinguish two locality claims

Let `K = closedBox d b`, with `K ⊆ U` and `U` open. Compactness gives a smooth cutoff with

\[
\chi=1\text{ on a neighborhood of }K,
\qquad
\operatorname{tsupport}\chi\subset U.
\]

Set
\[
\operatorname{globalize}_\chi(\zeta)(u)=\chi(u)\zeta(u).
\]

Even if `ζ` is arbitrary outside `U`, this is globally smooth: on `U` use the product rule; outside the support use local equality to zero. Merely having `support χ ⊆ U`, without the appropriate neighborhood/support argument, is not the proof you want.

For the empirical fields, one cutoff per chart works for **all** `n, ω`.

```lean
-- NEW; schematic
theorem contDiff_globalize
    (hζ : ContDiffOn ℝ ∞ ζ U) :
    ContDiff ℝ ∞ (globalize χ ζ)

-- NEW; schematic
theorem iteratedFDeriv_globalize_eq
    (hζ : ContDiffOn ℝ ∞ ζ U) :
    ∀ r, ∀ u ∈ K,
      iteratedFDeriv ℝ r (globalize χ ζ) u =
        iteratedFDeriv ℝ r ζ u
```

The second statement follows from equality on a neighborhood, including at the boundary of `K`.

### Locality statement 1: globally smooth fields agreeing on the box

This is the clean use of expansion uniqueness:

```lean
-- NEW; schematic; restrict (μ,q) to the uniqueness theorem's admissible indices
theorem empCoeffRect_congr_box
    (hζ₁ : ContDiff ℝ ∞ ζ₁)
    (hζ₂ : ContDiff ℝ ∞ ζ₂)
    (heq : Set.EqOn ζ₁ ζ₂ (closedBox d b))
    ... :
    empCoeffRect η ζ₁ h k (fun _ => b) μ q =
      empCoeffRect η ζ₂ h k (fun _ => b) μ q
```

Proof:

1. The integral sequences agree.
2. Apply `empRect_cutoffExpansion` to both fields.
3. Apply `empCoeffRect_unique`, within its precise uniqueness range.

This avoids unfolding the coefficient construction.

### Locality statement 2: the raw coefficient of a locally smooth field

The preceding proof **does not establish**

```lean
empCoeffRect η ζ ... = empCoeffRect η (globalize χ ζ) ...
```

when `ζ` is only smooth on `U`: you cannot apply the global expansion theorem to its left-hand side.

There are two sound interfaces:

1. **Recommended initially:** define the local-field coefficient using a global extension, and prove extension independence by `empCoeffRect_congr_box`.
2. Prove a direct germ-locality lemma for the raw `empCoeffRect` definition, or generalize the top-coefficient theorem to fields smooth near the box.

Thus your exact raw-expression target needs one additional locality theorem. This is likely a small obligation, but it is a real one.

For the top coefficient, `empCoeffRect_top_eq_smoothCoeff` offers a second proof route: show that the relevant `smoothCoeff` expression only sees the required jets on the box. That still requires a locality lemma; the displayed equality alone is not that lemma.

---

## E4. Cube jets and the missing closure estimate

Fix the chart and coefficient parameters. Put

\[
R_0=\sum_i \operatorname{depthOf}(h,k,\operatorname{cutoffOf}(h,\mu),i).
\]

Use any `R ≥ R₀`.

### Jet space

Your proposed definition is appropriate:

```lean
-- NEW
def CubeJetSpace (R : ℕ) (b : ℝ) :=
  ∀ r : Fin (R + 1),
    C(closedBox d b,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin r.1 => Fin d → ℝ) ℝ)
```

Here `closedBox d b` denotes the subtype in the `ContinuousMap` domain.

Use the finite dependent-product norm. With `ε ≥ 0`, the desired equivalence is

```lean
JetClose R K ζ₁ ζ₂ ε ↔
  ‖cubeJet R b ζ₁ - cubeJet R b ζ₂‖ ≤ ε
```

after aligning the exact smoothness and jet-domain conventions. The nonnegativity premise is useful for the standard sup-norm lemmas.

Define realizable jets as the range of a jet map whose domain packages global smoothness:

```lean
-- NEW; schematic
def SmoothCubeField := {ζ : V → ℝ // ContDiff ℝ ∞ ζ}

def cubeJet : SmoothCubeField → CubeJetSpace R b := ...

def cubeRealizable : Set (CubeJetSpace R b) := Set.range cubeJet
def cubeClosedJets := ↥(closure (cubeRealizable R b))
```

### Descent and continuity on realizable jets

Define the coefficient on `cubeRealizable` by choosing a realization. You must prove it is well-defined.

Interestingly, `tendsto_empCoeffRect_top` can prove this:

- If two smooth fields have identical order-`R₀` jets, take the constant sequence equal to the first field, with limit field the second and `M n = 0`.
- The theorem gives convergence of a constant coefficient sequence to the second coefficient.
- Uniqueness of limits gives equality.

The same theorem gives sequential continuity on realizable jets, hence continuity in this metric space.

### But continuity does not give extension to the closure

This is the main gap in the proposed E4.

A continuous function on a dense subset can fail to extend continuously to its closure: \(x\mapsto 1/x\) on \((0,\infty)\) is enough to illustrate the issue.

You need something like:

```lean
-- NEW; schematic sufficient estimate
theorem cubeCoeff_lipschitz_on_bounded_jets
    (B : ℝ) :
    ∃ L ≥ 0, ∀ ζ₁ ζ₂ : SmoothCubeField,
      ‖cubeJet R b ζ₁‖ ≤ B →
      ‖cubeJet R b ζ₂‖ ≤ B →
      |cubeCoeff ζ₁ - cubeCoeff ζ₂| ≤
        L * ‖cubeJet R b ζ₁ - cubeJet R b ζ₂‖
```

A slightly different uniform estimate is fine. What matters is that its constants remain controlled along **every convergent sequence of realizable jets**, including sequences with nonrealizable limits.

Then:

- coefficient values along approximating jet sequences are Cauchy;
- the limit is independent of the approximating sequence;
- the extension is continuous on the closure.

A `limUnder` definition by itself supplies none of those facts.

### Where to get that estimate

The resolved declarations

- `exists_pieceCoeff_top_bound`,
- `exists_resolvedCoeff_top_bound`

are useful **proof templates**, but are not directly applicable to a cube without their geometric inputs.

For the cube, the likely shortest proof is through

```lean
empCoeffRect_top_eq_smoothCoeff
```

and the finite-jet estimates already used in proving `tendsto_empCoeffRect_top`. Audit that proof: if it already produces a constant depending only on a bound for the two fields’ required jets, package that estimate rather than reproving continuity.

If its constants depend on uncontrolled information about a chosen smooth realization, more work is needed.

### What to abstract

I would extract a geometry-free lemma with roughly this interface:

> A real-valued function on a subset of a normed space, Lipschitz on each bounded part of that subset, extends uniquely and continuously to its closure.

Then instantiate it for both branch jets and cube jets. This is preferable to copying 600 lines of resolved-specific infrastructure.

---

## E5. Transport the law and identify the limit

### Coordinate reconstruction is exactly the right map

For a fixed chart, define a continuous linear map from the Stage C process space to cube jets:

```lean
-- NEW; schematic
def chartJetReconstruct :
    C(chartUnion d radii, ℝ) →L[ℝ] CubeJetSpace R b
```

Its `r` component is

\[
u\longmapsto
\sum_{b:\operatorname{Fin}r\to\operatorname{Fin}d}
  Z((\alpha,\langle r,b\rangle),u)\,\operatorname{coordMono}(r,b).
\]

Build it from:

1. restriction to a chart/word component;
2. scalar multiplication by a fixed CMM;
3. a finite sum;
4. the finite product over `r`.

Consume `iteratedFDeriv_eq_sum_coordMono`.

No symmetry constraints need to be imposed on arbitrary inputs. Reconstruction is defined on every coordinate field; realizability constraints will be imposed by support of the limit.

Combining reconstruction with Stage D and globalization gives

```lean
-- NEW; schematic
theorem ae_reconstruct_eq_cubeJet :
    ∀ᵐ ω ∂P, ∀ n,
      chartJetReconstruct
        (chartProcessCM X (jetKernel Rp) (jetMean Rp) ... n ω)
      =
      cubeJet R b ⟨globalEmpField α n ω, globalEmpField_smooth ...⟩
```

The order-zero component is included.

### Borel structure

Yes: use the norm topology and its Borel measurable space, just as for `BranchJetSpace`.

The relevant spaces are finite products of continuous-map spaces on compact metric domains, with finite-dimensional CMM codomains. They are separable Banach spaces under the usual hypotheses here.

A practical point: use the reconstructed Stage C process as the **primary measurable jet random variable**. Then prove it agrees a.s. with the actual field jets. This avoids making the initial distribution argument depend on a separate path-valued measurability proof for `empField`.

Do not install conflicting measurable-space instances on the same `def`; mirror the landed branch-jet convention.

### Closed support

Let

```lean
C := closure (Set.range (cubeJet R b))
νn := law of reconstructed empirical jets
ν  := pushforward of μlim by chartJetReconstruct
```

The preceding a.s. equality gives `νn Cᶜ = 0`. Since `Cᶜ` is open, Portmanteau gives

\[
\nu(C^c)\le \liminf_n\nu_n(C^c)=0.
\]

So yes: the limiting law is concentrated on closed realizable jets.

`ProbabilityMeasure.le_liminf_measure_open_of_tendsto` is the Mathlib declaration to check first, as you suggest. I have not verified its current argument order/signature. The required mathematical lemma is exactly the open-set inequality above; it is worth packaging a local wrapper:

```lean
-- NEW; schematic
theorem ae_mem_isClosed_of_tendsto_probabilityMeasure
    (hν : Tendsto νn atTop (𝓝 ν))
    (hC : IsClosed C)
    (hn : ∀ n, ∀ᵐ z ∂(νn n), z ∈ C) :
    ∀ᵐ z ∂ν, z ∈ C
```

### Applying continuous mapping

You have two clean implementations:

- **Reuse the landed closed-jet strategy:** lift the laws to the closed subtype and apply continuous mapping there.
- **Real-valued shortcut:** continuously extend the closed-jet coefficient from the closed subset to the whole metric jet space by Tietze, then use ordinary ambient-space continuous mapping. Closed support makes the answer independent of the chosen extension.

The first is more aligned with your current architecture. The second can avoid subtype-law transport, though it adds a topological extension dependency.

The limit is:

> the continuous closed-jet coefficient functional evaluated at the reconstructed Gaussian jet field.

It need not be Gaussian. Nor should you claim that the limiting finite-order jet field comes from a globally smooth sample field.

### Recommended theorem shapes

First prove the geometry-free distribution theorem:

```lean
-- NEW; schematic
theorem tendstoInDistribution_cubeCoeff_top_closed
    (hZ : TendstoInDistribution Z atTop Zlim)
    (hZn : ∀ n, ∀ᵐ ω ∂Pn n, Z n ω ∈ cubeRealizable R b)
    (hη : ContDiff ℝ ∞ η)
    (hk : ∀ i, 0 < k i)
    (hb : 0 < b)
    (hμ : 0 < μ)
    (hc : 1 ≤ c)
    (hdeep : DeepVanishing η b c)
    (hR : requiredOrder h k μ ≤ R)
    ... :
    TendstoInDistribution
      (fun n ω => cubeCoeffOnClosedJets ... (liftJet (Z n ω)))
      atTop
      (fun ω => cubeCoeffOnClosedJets ... (liftJet (Zlim ω)))
```

The exact `TendstoInDistribution` binder order should follow the landed resolved theorem.

Then the bridge theorem should preferably be stated as convergence of pushforward probability measures, matching `jointJetLaw`:

```lean
-- NEW; schematic
theorem chartTopCoeffLaw
    (hdeep : DeepVanishing (A.unitWt α) (rb α) c)
    (hk : ∀ i, 0 < A.k α i)
    (hμpos : 0 < μ)
    (hc : 1 ≤ c)
    ... :
    ∃ νlim : ProbabilityMeasure ℝ,
      Tendsto
        (fun n => law P
          (fun ω => localChartTopCoeff Q Rp α μ c n ω))
        atTop (𝓝 νlim)
      ∧
      νlim = closedCubeCoeffPushforward
        (reconstructedJointGaussianLaw ...)
```

Finally identify `localChartTopCoeff` with your requested raw `empCoeffRect` expression using the additional local-field locality theorem from E3.

---

## Is the trivial resolved-data route actually free?

Only if the following audit succeeds:

1. The resolved source integral is exactly the cube integral, including its amplitude and measure.
2. There is one relevant piece, or the resolved coefficient is proved equal to the single-cube coefficient after summing pieces.
3. The transported phase, monomial exponents, and fluctuation normalization agree.
4. `chartImage`, `pieceOrder`, and the closed domains require no more jet information than Stage C provides.
5. The resolved deep-vanishing/admissibility assumptions follow from your cube hypotheses.
6. There is an exact coefficient comparison, with the same \(\Gamma\)- and logarithmic normalizations.

`MonomialResolvedData`/`MonomialModification` may supply the phase-resolution part while leaving several of these obligations untouched. Thus I would time-box that audit, not base the Stage E plan on it.

---

## E6. The greybook atlas can support a multi-chart theorem directly

**Yes: the coefficient-level multi-chart law does not intrinsically require grammar’s resolved core transport.**

Assuming finitely many charts, exact evidence decomposition, and the needed cube hypotheses, define the total coefficients chartwise and sum them.

For a finite list of admissible chart coefficients:

1. Choose one `R` dominating all required orders.
2. Use the **joint** Stage C law.
3. Reconstruct all chart jets simultaneously.
4. Apply the vector of closed coefficient functionals.
5. Apply the finite sum.

Do not combine separate marginal convergence statements. Cross-chart dependence matters and is already retained by `jointJetLaw`.

### Three qualifications

**1. Align the coefficient indices.**  
For rational monomial exponents, use a common refinement of the chart lattices and extend coefficients by zero at absent indices. Prove the required finite-sum stability of `CutoffExpansion`.

**2. The landed continuity theorem covers qualifying top coefficients, not every subleading coefficient automatically.**  
To handle a requested coefficient with log degree `q`, you need the theorem with `c = q + 1`, hence the corresponding `DeepVanishing` condition, or a more general continuity theorem. Charts with different pole structures require explicit zero/comparison lemmas.

**3. Separate coefficient laws from evidence asymptotics.**  
`empRect_cutoffExpansion` says, for a fixed smooth `ζ`, something about the limit as `N → ∞`. Substituting `ζ = ζ_n` and `N = n` requires a uniform remainder estimate, for example one controlled on bounded sets of sufficiently high jets. Tightness from `jointJetLaw` can then turn that estimate into an `o_P` remainder. It cannot replace the uniform estimate.

### What may honestly be claimed

You can establish:

> An empirical joint subleading coefficient theorem for the greybook charted-atlas evidence, with canonical cube coefficients and a Gaussian-jet pushforward limit.

With uniform remainder control and the appropriate index hypotheses, this can become an empirical evidence expansion theorem on that data model.

Whether it is **the paper’s exact Theorem E** depends on its statement. If it is an atlas-independent assertion about the evidence integral and these canonical coefficients, a direct proof through greybook’s exact `decomp` is mathematically sufficient. Walls and branch representatives can be proof infrastructure rather than theorem-level necessities.

If the theorem explicitly identifies grammar’s resolved branch coefficients or its `ResolvedCoreTransport` construction, that identification remains E6. Do not claim that interface theorem has been instantiated before proving it.

---

## Concrete next milestones

| Priority | Deliverable | Main existing inputs |
|---|---|---|
| 1 | Simultaneous representative equality and evidence congruence | `ChartKernelRep.represents`, greybook representative identity and continuity, `chartMean` identity |
| 2 | Globalization and extension-independent local coefficients | `ContDiffBump`, `empRect_cutoffExpansion`, `empCoeffRect_unique` |
| 3 | Cube coefficient bounded-jet estimate | `empCoeffRect_top_eq_smoothCoeff`, proof ingredients of `tendsto_empCoeffRect_top` |
| 4 | Generic closed-realizable-jet extension | Architecture of `coeffOnJets` / `coeffOnClosedJets` |
| 5 | Coordinate reconstruction and cube law | `iteratedFDeriv_eq_sum_coordMono`, `jointJetLaw`, `ae_iteratedFDeriv_empField_eq`, Portmanteau, continuous mapping |
| 6 | Joint finite-chart coefficient law | Same joint jet law, finite products and sums, greybook `decomp` |
| Separate | Raw local-field coefficient comparison; zero exponent cases; uniform stochastic remainders; resolved-model identification | Additional explicit lemmas |

**Bottom line:** E2 is routine. E3 needs a carefully stated locality interface. E4’s substantive analytic obligation is the bounded-jet extension estimate. E5 is then standard transport of the joint law. A useful multi-chart coefficient theorem is available directly on greybook’s atlas without first solving the resolved-core identification.