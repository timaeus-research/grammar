**Recommendation:** use greybook’s **joint \(C^0\)-valued law** for (L), and build a **finite-jet extension of that law** for (S). Keep grammar’s interfaces dependency-free; instantiate them in a thin glue repository. A single-chart bridge is a sound first milestone, but not a discharge of the resolved theorem’s hypotheses.

The assessment below uses the supplied survey; dependency compatibility still needs a build test.

## 1. Finite jets: mathematically sound, with four qualifications

### A. “Apply Theorem 5.9 on \(K\times\{\alpha\}\)” needs an implementation step

The disjoint union is compact metrizable, but it is **not itself the open Euclidean domain** expected by an analytic-input theorem.

The clean implementation is:

1. Work on an open neighbourhood \(U\) of the closed chart box \(K\).
2. For each required derivative coordinate \(\alpha\), establish analyticity of
   \[
   u\longmapsto D^\alpha a(\cdot,u)\in L^s(\mu).
   \]
3. Obtain tightness for each coordinate process.
4. Obtain **joint** fidi convergence, using the same samples across all coordinates and charts.
5. Use finite-product tightness and fidi uniqueness to obtain the joint law.

Alternatively, establish a joint `CoeffExpansion` on the disjoint union and invoke the generic coefficient-form theorem directly. This requires an explicit combined expansion and summability proof—not just a change of parameter-space notation.

**Important:** verify that the normalized chart kernel \(a\), not merely the original model \(F\), has the needed \(L^s\)-analyticity on an open neighbourhood. Analytic division must come from the standard-form construction; it does not follow by naively dividing by \(u^k\) at the divisor.

Boundary derivatives are then ambient derivatives restricted to \(K\). No derivative-at-the-boundary convention is needed. Shrinking analytic radii may be necessary for derivative coefficient estimates. **Higher derivative order need not require higher \(s\)** if the \(s=2\) law theorem applies to each derivative kernel.

### B. Representatives are a real theorem, not bookkeeping

The identity needed is
\[
D^\alpha\xi_n(u)
 =-\frac1{\sqrt n}\sum_{i<n}
 \bigl(D^\alpha a(X_i,u)-D^\alpha m(u)\bigr),
\qquad m(u)=u^k.
\]

An analytic map into \(L^s\) consists of equivalence classes. It does **not** immediately establish this identity for the chosen raw kernel, simultaneously for every \(u\).

Prove a representative-selection lemma giving:

- jointly measurable derivative kernels;
- one measurable full-measure set of observations on which paths are analytic on an open neighbourhood of \(K\);
- simultaneous pointwise derivative identities there;
- agreement with the original chart kernel in the sense required for the empirical-integrand identity.

Use coefficient domination on suitably smaller neighbourhoods, followed by a countable cover. Do **not** intersect parameter-indexed null sets.

Then countability of samples and finiteness of charts give one probability-one event on which **all \(n\), all charts, all required derivatives** work. IID assumptions transfer the observation-level good set to each sample.

### C. Identify the correct jet space explicitly

There are continuous linear identifications
\[
C(K\times A,\mathbb R)\simeq \prod_{\alpha\in A}C(K,\mathbb R),
\]
and, in finite-dimensional chart coordinates, derivative tensors are reconstructed continuously from finitely many scalar coordinates.

For grammar, construct the actual map to `BranchJetSpace μ`; include the tensor-coordinate and chart-coordinate conventions. It is generally a **finite-coordinate norm equivalence**, not an isometry without checking the chosen norms.

The joint Gaussian covariance is
\[
\operatorname{Cov}\bigl(D^\alpha a(X,u),D^\beta a(X,v)\bigr),
\]
including cross-chart covariances. The two minus signs in \(\xi_n=-\mathrm{preEmpiricalProcess}\) cancel.

“Gaussian jet field” can mean precisely a law on the jet space with Gaussian finite-coordinate evaluations. **No additional GP construction is needed for (S).**

### D. Target closed realizable jets, not a smooth Gaussian realization

Use:
- **a.e. smooth realizability of each approximating field**;
- a limit law on the **closure of grammar’s realizable jets**.

Closed-set support passes to the weak limit. There is no need to prove the limit has a \(C^\infty\) realization.

Best Lean arrangement: export an everywhere-defined measurable, realizable modification, plus a.e. equality with the raw empirical jets. Fill the complement of the common good event with the zero smooth field. If modifying grammar’s theorem is cheap, an a.e.-realizability wrapper is also useful.

**Crucial distinction:** chartwise smoothness does not imply realizability by one grammar root field. That needs overlap/transport compatibility. Until this is proved, the result is a chart-jet law, not yet (S).

## 2. Interface for (L), and the geometry bridge

Consume **`AtlasData`’s joint \(C(\mathcal M)\)-valued `ξCM` and its limiting law**.

Why:

- It already supplies joint convergence and tightness.
- Continuous restriction/transport gives the grammar branch-tuple law.
- Tightness of the sup norm gives the relevant \(O_p(1)\) bounds, provided the transport controls grammar’s global bound.
- Applying per-chart results separately does not determine cross-chart dependence.

Use `ChartFieldData` as an auxiliary interface when first-derivative bounds are actually needed. It is neither the primary joint-law interface for (L) nor sufficient for higher jets in (S).

The geometry adapter should expose, rather than hide:

1. Chart-domain identifications or restrictions.
2. Matching monomial exponents, densities/Jacobians and cutoffs.
3. The empirical exponent identity with `ζ := chartXi`.
4. A continuous map from the joint chart-field space to `BranchTuple`.
5. A root-field realization/compatibility witness and global-bound control.
6. For (S), the corresponding continuous finite-jet transport.

The shared hironaka core is encouraging, but does not supply these identifications automatically.

**Paper scope:** a single-box theorem is an acceptable explicit first result: “the stochastic inputs are instantiated for a standard-form chart.” It must not be described as discharging the full resolved stochastic hypotheses. That requires assembly—or an independently proved construction of a compatible resolution.

## 3. Dependency architecture

**Prefer (b), with small semantic hypothesis structures in grammar.**

- **grammar:** generic deterministic/stochastic bridge contracts and conditional consequences.
- **glue repo:** depends on grammar and greybook; constructs those contracts from greybook.
- **later:** consider a direct grammar dependency once build and maintenance costs are known.

Do not copy Ch5 proofs. Also do not mirror every theorem signature literally: mirror the **mathematical outputs grammar consumes**. Use structure fields/theorem parameters, not new axioms or unproved instances.

The glue repository isolates build cost and integration churn; **it does not eliminate the hironaka dependency diamond**.

Do not assume “root pin wins.” Test a minimal workspace with:

- one explicit hironaka source/revision;
- imports from greybook’s law theorem;
- imports from grammar’s fork-only transport modules;
- a clean dependency resolution and build.

Inspect the resulting manifests and actual checked-out revision. Ancestor/superset status reduces risk but does not certify Lake resolution or build compatibility. Prefer converging on a shared upstream pin when practical.

## 4. Ranked deliverables

The following are **schematic statement shapes**, not claims about existing declaration signatures.

### 1. Single-chart \(C^0\) data-model bridge

Deliver the sign-correct exponent identity, a continuous-field modification, its joint law, and Gaussian marginals. Keep the identity separately reusable.

```lean
-- Proposed output contract; P is a probability measure.
structure ChartC0Law (P : Measure Ω) (K : Type*) where
  field       : ℕ → Ω → C(K, ℝ)
  measurable  : ∀ n, Measurable (field n)
  limitLaw    : ProbabilityMeasure C(K, ℝ)
  law_tendsto :
    Tendsto
      (fun n => (⟨P, ‹IsProbabilityMeasure P›⟩).map
        (measurable n).aemeasurable)
      atTop (𝓝 limitLaw)
  -- Explicit Gaussian-evaluation specification.
  -- A.e. agreement with raw chartXi, simultaneously in u.
```

```lean
theorem exists_chartC0Law_of_standardForm
    (h : ChartAnalyticSamplingData ...) :
    ∃ B : ChartC0Law P K,
      ∀ n, ∀ᵐ ω ∂P, ∀ u,
        B.field n ω u = chartXi ... n ω u := ...
```

Attach the `nKn_standardForm` identity and instantiate grammar’s box result with `B.field`. This is useful before resolving atlas compatibility.

**Pitfall:** pointwise a.e. equality for each \(u\) is insufficient; obtain a.e. equality of the entire continuous path.

### 2. Joint finite-chart, finite-jet law

Make the probabilistic theorem independent of grammar geometry. Index coordinates by **chart and derivative coordinate**, retaining common samples.

```lean
theorem exists_finiteJetLaw_of_chartAnalyticSampling
    (h : ChartAnalyticSamplingData ...)
    (R : ChartIndex → ℕ) :
    ∃ J : ℕ → Ω → FiniteChartJetSpace R,
      ∃ ν : ProbabilityMeasure (FiniteChartJetSpace R),
        (∀ n, Measurable (J n)) ∧
        LawsTendsto P J ν ∧
        (∀ n, ∀ᵐ ω ∂P,
          IsJetOfSmoothChartPaths R (J n ω)) ∧
        HasCenteredGaussianEvaluations ν (derivativeCovariance h R) := ...
```

Here `LawsTendsto` and the other predicates are proposed helper contracts. Include a.e. agreement with the raw differentiated empirical process.

Then transport to grammar:

```lean
theorem grammar_closedJetLaw_of_finiteJetLaw
    (B : FiniteJetLawData ...)
    (T : CompatibleGrammarJetTransport ... μ) :
    ClosedRealizableJetLawData ... μ := ...
```

`T` must include continuous transport and **actual root-field realizability**, not merely chartwise smoothness.

### 3. Resolved leading assembly

Construct the continuous `C(𝓜) → BranchTuple` adapter, global-bound control, and integrand/measure matching. Apply `tendstoInDistribution_empZ_div`.

### 4. Resolved subleading assembly

Construct the finite-jet transport, package a.e. modifications/closed support, and apply `tendstoInDistribution_resolvedCoeff_top_closed`.

### 5. Dependency consolidation

Only after the two chart-level units build, decide whether the glue should remain separate.

**Bottom line:** the probabilistic route is sound and can avoid the envelope-based jet-tightness argument. The remaining substantive obligations are **simultaneous analytic representatives, joint derivative laws, and geometry-compatible realizability**—not a stronger Gaussian-process object.