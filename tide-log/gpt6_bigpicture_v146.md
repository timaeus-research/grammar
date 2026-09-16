**Verdict:** close the package as stated, with two scope qualifications: continuity is for the **specified top coefficient under `hc hF hμ`**, and the distributional theorem uses **realizable-jet-valued limits**, not arbitrary ambient Gaussian jets. My preferred next step is a small extension-to-closure package; it removes a genuine obstacle to the stochastic programme.

This is an audit of the supplied statements, not an independent inspection of `c8ed17a`.

## 1. Closure audit

### (1) Lipschitz and jet interface: approved

The asymmetric bound—bounded jets for `ξ₂`, closeness of `ξ₁` to `ξ₂`—is sufficient for both descent and continuity. Restricting `ε ≤ 1` is harmless for those purposes.

Check that the exported headlines retain:

```lean
(hc : 1 ≤ c) (hF : VanishesNearStratum F (c + 1)) (hμ : 0 < μ)
```

including `continuous_coeffOnJets` and its descendants.

**Scope correction:** this does not, by itself, establish simultaneous continuity of every lower-log coefficient in a fixed expansion. Applying the theorem at a smaller `c` changes the vanishing hypothesis. Say “continuity of the top coefficient under the stated stratum-vanishing hypothesis,” unless another theorem covers the whole vector.

### (2) `iteratedDeriv`: approved

Global `iteratedDeriv`, evaluated at `ν > 0`, is the right object. Derivatives are local; behavior of the totalized integral at nonpositive parameters is irrelevant after proving neighborhood agreement inside `(0,∞)`.

Paper wording:

> Here \(\partial_\nu^\ell S_\nu(a)\) denotes differentiation with respect to \(\nu\) on the open half-line \(\nu>0\).

No need to replace the formal object by iterated within-derivatives.

The normalization is correct:

\[
M_{\mu,\ell}[\tau^r e^{a\tau}]
=(-1)^\ell\partial_\nu^\ell S_\nu(a)\big|_{\nu=\mu+r/2}.
\]

There is no additional substitution factor: the defining integration variable is already \(s\).

### (3) Conditional distributional theorem: approved, with explicit target space

Publish:

> If the realizable branch-jet random elements converge in distribution in the range of the branch-jet map, equipped with its inherited metric, then the corresponding top coefficients converge in distribution.

Also state:

> This is a conditional continuous-mapping theorem; convergence of the empirical jets and realizability of a proposed limiting field are not established.

Do not identify that range with a closed jet space. In particular, a limit of jets of smooth fields need not be the jet of a smooth field in your specified class. A finite-regularity Gaussian limit makes this distinction practically important.

## 2. Ranked direction

1. **Extend the coefficient to the closure of realizable jets.** Highest immediate leverage: the existing bounded-jet Lipschitz estimate should suffice, and this removes the unnecessary smooth-realizability requirement on stochastic limits.
2. **Low-dimensional closed coefficient formulas.** Best next paper-facing mathematical deliverable. Start with the next two one-dimensional exponents.
3. **Full stochastic jet programme.** Important, but substantially larger: differentiability of the field construction, function-space tightness, and empirical-process hypotheses remain real work.
4. **Additional population machinery.** No specific gap in C–E follows from this audit. Do not build general Faà di Bruno/topology infrastructure without a theorem that needs it.

**Consolidation report:** do it now as a short parallel task, not as a competing research programme. Record hypothesis dependencies and distinguish “top coefficient,” “all coefficients,” and “conditional limit theorem.”

## 3. Top pick: closure extension

The following are statement shapes; names and argument order are schematic.

```lean
def ClosedRealizableJets (μ : ℝ) :=
  ↥(closure (Set.range (branchJet μ)))

def closedRealizableJet (μ : ℝ) (ξ : SmoothRootField) :
    ClosedRealizableJets μ := ...
```

### A. Export the actual quantitative property on the range

First turn the existing estimate into a bounded-ball estimate:

```lean
theorem coeffOnJets_dist_le
    (hc ...) (hF ...) (hμ ...) (hB : 0 ≤ B)
    (x y : RealizableJets μ)
    (hy : ‖(y : BranchJetSpace μ)‖ ≤ B)
    (hxy : dist x y ≤ 1) :
    dist (coeffOnJets μ c x) (coeffOnJets μ c y)
      ≤ K B * dist x y := ...
```

Here `K B` can be a chosen witness from the existing existential theorem. Reuse:

- `exists_resolvedCoeff_top_bound`;
- the norm/`JetClose` equivalence;
- the corresponding norm-to-`JetBoundOn` implication;
- `resolvedCoeff_eq_of_branchJet_eq`.

If convenient, keep `∃ K ≥ 0, ...` instead of defining `K`.

### B. Extend by limits

```lean
noncomputable def coeffOnClosedJets
    (hc ...) (hF ...) (hμ ...) :
    ClosedRealizableJets μ → ℝ := ...

theorem continuous_coeffOnClosedJets ... :
    Continuous (coeffOnClosedJets hc hF hμ) := ...

@[simp] theorem coeffOnClosedJets_closedRealizableJet ... :
    coeffOnClosedJets hc hF hμ (closedRealizableJet μ ξ)
      = ξ.resolvedCoeff μ (c - 1) := ...
```

Proof mechanism:

1. Approximate a closure point by realizable jets.
2. Every convergent approximating sequence is bounded.
3. The bounded-jet estimate makes its coefficient sequence Cauchy.
4. Completeness of `ℝ` gives a limit.
5. The same estimate gives independence of approximation and continuity.

A reusable metric-space lemma for **maps uniformly continuous on bounded subsets** would be reasonable. Do not demand global uniform continuity: your constants depend on the jet bound.

**Pitfalls:**

- At a boundary point of a radius-`B` ball, use a larger ball for approximants.
- The `dist ≤ 1` restriction is enough for Cauchy arguments.
- This extension needs completeness of the **codomain** `ℝ`; completeness of the ambient jet space is not needed merely to extend to its closure.
- Prove uniqueness by density. That makes the extension mathematically canonical.

### C. Upgrade the conditional theorem

```lean
theorem tendstoInDistribution_resolvedCoeff_top_closed
    (hc ...) (hF ...) (hμ ...)
    {G : Ω' → ClosedRealizableJets μ}
    (hLG :
      TendstoInDistribution
        (fun n w => closedRealizableJet μ (ξ n w))
        atTop G (fun _ => P) P') :
    TendstoInDistribution
      (fun n w => (ξ n w).resolvedCoeff μ (c - 1))
      atTop
      (fun w' => coeffOnClosedJets hc hF hμ (G w'))
      (fun _ => P) P' := ...
```

Again, reuse `TendstoInDistribution.continuous_comp`.

For a genuinely **ambient-space formulation**, an optional second step is a continuous real-valued extension from the closed subset to the metric ambient space via Tietze. Values outside the closure are noncanonical, but irrelevant when the limit is supported on the closure.

### Stochastic hypotheses to target afterward

For finitely many compact branch domains and required order `m`, a useful sufficient regime is:

- centered iid random fields with pathwise `C^(m+1)` regularity;
- square-integrable uniform envelopes for derivatives through order `m+1`;
- finite-dimensional CLTs for derivative evaluations;
- tightness of the derivative processes.

The extra derivative plus an envelope supplies increment control; establish tightness using an appropriate entropy or stronger moment criterion. Pointwise second moments alone are not enough. If empirical root fields are nonlinear transforms, additionally prove differentiability/stability of that transformation in the required jet topology.

## 4. Low-dimensional follow-up and paper edits

For the explicit-formula project, first prove a finite normal form:

```lean
empOneDimCoeff ... =
  ∑ i ∈ terms,
    weight i *
      mellinMom
        (fun τ => τ ^ power i * Real.exp (amplitude i * τ))
        μ (logOrder i)
```

Then rewrite with `mellinMom_pow_mul_exp_eq_iteratedDeriv`. Keep coefficient extraction separate from Mellin evaluation.

**Important:** do not promise `∂ν S` in the one-dimensional examples before inspecting the extracted `logOrder`s. In the ordinary log-free one-dimensional monomial setting they may all be zero. Differentiation in the amplitude produces shifted \(S\)-parameters, not automatically parameter derivatives.

Suggested present paper wording:

> Under the stated stratum-vanishing hypothesis, the top coefficient descends continuously to the realizable branch-jet space. Consequently, convergence in distribution in that metric space implies convergence in distribution of the coefficient. No empirical jet convergence theorem is asserted.

Retain the existing non-claim about individual lower coefficients. Add the closure extension to the paper only after it lands.