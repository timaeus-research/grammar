## Recommendation: **(c) > (a) ≫ (b)**

Close **this arc** as *deterministic + conditional*. The missing jet convergence is a substantive statistical hypothesis, not unfinished deterministic bookkeeping. An abstract tightness theorem would be useful independent infrastructure, but would **not** supply finite-dimensional convergence or connect the root field to data.

I would close #147 with that decision, preserving (a) as a separately scoped follow-up—not introduce a `JetLaw` hierarchy now.

### 1. Final interface and paper wording

The interface should remain:

- measurable random branch jets;
- convergence in distribution in `BranchJetSpace μ`, **not merely in `BranchTuple`**;
- a limiting random element in the closed realizable jets;
- continuous mapping through `coeffOnClosedJets`.

Equivalently, formulate convergence directly in the closed-realizable-jet subtype. Schematically:

```lean
X : ℕ → Ω → ClosedRealizableJet μ
G : Ω' → ClosedRealizableJet μ
hconv : TendstoInDistribution X ... G ...

-- Existing closed-jet CMT:
TendstoInDistribution
  (fun n ω => coeffOnClosedJets μ (X n ω)) ...
  (fun ω => coeffOnClosedJets μ (G ω)) ...
```

Use the landed theorem rather than adding another wrapper unless downstream applications need one. Different source probability spaces for `X` and `G` should remain allowed.

**Paper scope paragraph:**

> The formalisation treats the random root field as an abstract input: it establishes the leading-term limit under the stated field-level convergence and tightness hypotheses, and transfers convergence of branch jets to convergence of the top resolved coefficient through its continuous extension to the closed realizable jets. It neither constructs the field from sampled losses nor proves an empirical-process or jet-level central limit theorem; these stochastic convergence assumptions remain hypotheses of the results.

No further deterministic theorem is needed to justify closing.

## 2. If (a) is pursued: prove one envelope-to-tightness theorem

Do **not** start with iid samples, Kolmogorov continuity, or `SmoothRootField`. Start with random elements of the **existing jet space**.

For \(X_n\in\prod_{p,r}C(K_p,E_{p,r})\), assume measurable nonnegative \(A_n\) such that, almost surely, simultaneously for every coordinate,
\[
 \|X_{n,p,r}\|_\infty\le A_n,\qquad
 \operatorname{Lip}(X_{n,p,r})\le A_n,
 \qquad \sup_n\mathbb E[A_n^2]\le C<\infty.
\]

Then the laws of \(X_n\) are tight.

A schematic Lean interface is:

```lean
theorem isTightMeasureSet_of_jetEnvelope
    (X : ℕ → Ω → BranchJetSpace μ)
    (hX : ∀ n, Measurable (X n))
    (A : ℕ → Ω → ℝ≥0)
    (hA : ∀ n, Measurable (A n))
    (C : ℝ≥0)
    (hmoment :
      ∀ n, ∫⁻ ω, (A n ω : ℝ≥0∞)^2 ∂P ≤ (C : ℝ≥0∞))
    (hbound : ∀ n, ∀ᵐ ω ∂P, -- all coordinate sup norms ≤ A n ω
      ...)
    (hlip : ∀ n, ∀ᵐ ω ∂P, -- all coordinates LipschitzWith (A n ω)
      ...) :
    IsTightMeasureSet (Set.range (fun n => P.map (X n)))
```

Assume `[IsProbabilityMeasure P]` and the required compactness/finite-dimensionality instances explicitly.

**Proof architecture:**

1. Define
   \[
   B_M=\{z:\forall p,r,\ \|z_{p,r}\|_\infty\le M,\
                            \operatorname{Lip}(z_{p,r})\le M\}.
   \]
2. Prove `IsCompact B_M`: Arzelà–Ascoli coordinatewise, closedness of the constraints, finite products.
3. Markov:
   \[
   P(X_n\notin B_M)\le P(A_n>M)\le C/M^2.
   \]
4. Choose \(M\) for each \(\varepsilon\).

This needs **no Prokhorov theorem**. Indeed, uniform tightness of the scalar envelopes is enough; the second moment is a convenient corollary.

### Derivative-envelope corollary

Your proposed bounds through order \(R_p+1\) imply this criterion **provided the derivative bounds give uniform Lipschitz bounds on the actual domains**.

Important qualifications:

- A convex box is sufficient, with derivative bounds on the segments joining points.
- Bounds only on an arbitrary compact chart image are **not** sufficient to infer Lipschitz control there. Use a convex containing domain, controlled extensions, or explicit equicontinuity assumptions.
- Include sup-norm control, or anchor-value control plus a diameter bound. Equicontinuity alone does not give compact containment.
- The derivative targets must have compact bounded sets—here supplied by finite-dimensionality. This argument fails for unrestricted infinite-dimensional Banach targets.
- Pathwise smoothness plus measurability of the `C⁰` root field does not **by itself discharge the Lean measurability obligation** for its jet-valued map.
- Use `lintegral` for the moment assumption, or explicitly assume integrability. An unqualified bound on a real Bochner integral is unsafe.
- No independence is needed for this theorem.

## 3. Mathlib status and the remaining probability gap

I cannot certify the Mathlib API at your pin from the repository commit alone; inspect `lake-manifest.json`. In particular, I would **not promise** an available Polish-space Prokhorov/subsequence theorem without checking its actual statement.

Reuse/search targets:

- `BoundedContinuousFunction.arzela_ascoli`, and the compact-domain bridge from `ContinuousMap` to bounded continuous maps;
- compactness of finite dependent products;
- the nonnegative-integral Markov inequality;
- `IsTightMeasureSet` and measurable pushforwards.

Treat those as API targets, not a checked list of exact theorem signatures at this pin.

For **fd convergence + tightness ⇒ jet convergence**, additionally verify availability of:

1. relative compactness of tight probability laws;
2. identification of laws by evaluations on countable dense subsets;
3. the subsequence argument yielding convergence of the entire sequence.

Here “fd convergence” must include **derivative-jet evaluations**, not just root-field values. Compact metric domains, finite-dimensional targets, and finitely many coordinates make the jet space Polish; that is mathematically sufficient, but does not establish the required library coverage.

## 4. Optional deterministic illustration: a genuine two-dimensional log

A useful example is
\[
K(x,y)=x^2y^2,\qquad h=(0,0),\qquad (x,y)\in[0,1]^2.
\]
The equal ratios \((h_i+1)/(2k_i)=1/2\) give \(\lambda=1/2\), multiplicity \(2\).

With constant fluctuation \(a\), explicitly adopting
\[
S_\nu(a)=\int_0^\infty t^{\nu-1}e^{-t-a\sqrt t}\,dt,
\]
one obtains
\[
\int_0^1\!\!\int_0^1 e^{-nx^2y^2-a\sqrt n\,xy}\,dx\,dy
=
\frac{n^{-1/2}}4
\int_0^n t^{-1/2}e^{-t-a\sqrt t}(\log n-\log t)\,dt.
\]
Thus, for fixed \(a\),
\[
=\frac{n^{-1/2}}4
\left[
S_{1/2}(a)\log n-
\left.\partial_\nu S_\nu(a)\right|_{\nu=1/2}
\right]
+\text{exponentially small remainder}.
\]

At \(a=0\), these are \(\Gamma(1/2)\) and \(\Gamma'(1/2)\). Translate the sign/normalisation to the repository’s `S` convention.

The exact formula uses integration over the unit box. If the chart package demands a smooth ambient cutoff, take a tensor cutoff equal to one near the origin and supported inside the chart: the displayed log coefficient and derivative contribution persist, but cutoff-dependent non-log terms must also be recorded.

**Worth adding as exposition; not a condition for closing #147.**