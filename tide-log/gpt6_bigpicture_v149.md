## Recommendation

**Make (ii) the next substantive target, but split it at the analytic-division interface and use that as a go/no-go gate.** Do not start by building a general finite-chart leading-order transfer theorem.

My ranking is:

1. **(ii), staged:** analytic quotient and derivative-kernel interface first; joint jet law second; resolved coefficient law third.
2. **(i):** valuable as a consistency check, but first audit the formulas below. As written, the proposed identity has a normalization discrepancy.
3. **(iv):** the right stopping point if the analytic-division interface cannot be obtained economically.
4. **(iii):** only for a specific low-order coefficient consumer. The stated gradient results do not by themselves give tightness of first-order jets.
5. **(v):** defer until a consumer actually needs it. GreyBook’s leading-order assembly is not that consumer.

This is a priority ranking, not execution order: I would do the short sign/normalization audit before committing weeks to (ii).

I am reasoning from the declarations and formulas supplied here, not from an inspection of their implementations. In particular, the exact strength of the existing standard-form construction remains the decisive source-level question.

---

## 1. Two immediate audits

### 1.1 The displayed essential-coordinate count and `boxGamma` do not agree

Write \(q\) for the number of essential coordinates. Under
\[
h_i+1=2k_i\lambda,
\]
the grammar leading prefactor is
\[
\frac{1}{(q-1)!\prod_i 2k_i}.
\]

The corresponding cutoff power must cancel:
\[
b^{\sum_i h_i+q-2\lambda\sum_i k_i}=1.
\]

But the supplied GreyBook formulas have:

- \(q=r+2\);
- factorial \(r!\);
- cutoff exponent \(\sum h_i+r+1-2\lambda\sum k_i\).

Consequently, the displayed `boxGamma` becomes
\[
\frac{b^{-1}}{r!\prod_i2k_i},
\]
whereas grammar gives
\[
\frac{1}{(r+1)!\prod_i2k_i}.
\]
Their ratio is \((r+1)/b\).

**Thus candidate (i), literally as stated, is false unless some omitted normalization compensates for this.** Taking `s = 0` and constant field and unit eliminates most possible coordinate-change explanations.

Likely possibilities are:

- the essential coordinate type is really `Fin (r+1)`;
- the formula for `boxGamma` was transcribed with an index shift;
- the theorem’s scale or normal form contains an additional factor.

Use a neutral parameter `q` in the bridge identification theorem, rather than inheriting `r` before this is settled. Also check the `q = 1` case: the quoted `Fin (r+2)` interface does not cover it.

### 1.2 The displayed sign needs an explanation

You have both:

```lean
chartField ... = −chartXi ...
```

and an integral identification with `empBoxIntegral ... chartFieldExt ...`, but the displayed limit for `chartZ` uses `boxExt ... (−φ)` under `chartLaw`, which is already the law of `chartField`.

If `chartZ` is the evidence in that integral identity, the direct application of grammar’s theorem gives the functional at **`φ`**, not `−φ`.

This need not invalidate a distributional conclusion: a centered Gaussian law on the continuous-function space is invariant under negation, once that is proved from the fidis and the function-space Borel structure. But it is not the same pathwise constant identification or joint coupling.

Record explicitly one of:

- `chartZ` uses the opposite field convention;
- the limit is first obtained at `φ`, then rewritten in law by Gaussian symmetry;
- the displayed sign is a transcription error.

For the joint jet project, fix one sign convention once. Do not repair individual chart limits by separate symmetry arguments.

---

## 2. The key mathematical question: analytic division, not differentiation

`AnalyticOnNhd.fderiv` and analytic composition help **after** obtaining an analytic \(L^s\)-valued quotient
\[
\mathcal A_\alpha(u)
  = \frac{F(g_\alpha(u))}{u^{k_\alpha}}.
\]

They do not establish that quotient across the coordinate divisor.

### What follows immediately

From suitable neighborhood hypotheses on `F` and `gα`, composition gives analyticity of
\[
H_\alpha(u)=F(g_\alpha(u))
\]
as an \(L^s\)-valued map.

Away from \(u^{k_\alpha}=0\), its quotient by the monomial is analytic.

### What is missing

You need **Banach-valued monomial divisibility** across the divisor. Merely naming a continuous standard-form representative `aα` does not make the formal conclusion available.

There are two viable proofs.

#### Route A: extract divisibility from the resolution construction

If the hironaka/chart proof already factors the relevant analytic coefficient family by \(u^{k_\alpha}\), expose that factorization at the \(L^s\)-valued level.

This is the preferred route. Inspect the construction of `fa`, not just the signature of Theorem 6.1.

#### Route B: prove removability from the existing standard form

Suppose the existing construction supplies:

1. analytic \(H_\alpha\) on a neighborhood of the box;
2. for each parameter \(u\), the correct a.e. identification of \(H_\alpha(u)\) with the scalar kernel;
3. a coherent, samplewise continuous quotient `aα` on the box;
4. the standard-form equality, including an adequate common-null-set interpretation.

Then monomial removability is mathematically provable. One can successively show that the forbidden Taylor coefficients vanish. \(L^s\)-convergence implies convergence in measure, while samplewise continuity of the quotient rules out a nonzero pole.

**A dominated \(L^s\) bound on the given quotient is not necessarily required for that removability argument.** It would simplify it, but it should not be assumed to be a new indispensable hypothesis.

What is not justified from the summary alone is that all four items are already exposed in precisely the required form, especially at chart boundaries.

### My answer to “is it provable from present hypotheses?”

- **From `IsLpValuedAnalytic F U₀` plus analytic charts alone: no.** Arbitrary analytic functions are not divisible by a specified monomial.
- **With the coherent continuous standard form described for Theorem 6.1: plausibly yes, without a new statistical smoothness assumption**, subject to checking the neighborhood and representative identifications above.
- **The existing declaration only exposes continuity of `fa`; it does not expose this conclusion.** It is unsafe to describe derivative analyticity as already available.

That distinction should govern the first milestone.

---

## 3. Top project, designed to statement level

The following are proposed interfaces, not claims about existing declaration names.

### Stage A — analytic standard-form kernels

Put the GreyBook-specific extraction in the bridge. A generic Banach-valued divisibility lemma can later be upstreamed to the appropriate dependency.

The desired output is essentially:

```lean
-- Schematic: retain GreyBook's actual exponent and analyticity predicates.
structure AnalyticChartKernelData (...) where
  U : Chart → Set (Fin d → ℝ)
  isOpen_U : ∀ α, IsOpen (U α)
  box_subset_U : ∀ α, closedBox d (rb α) ⊆ U α

  kernelLp : Chart → (Fin d → ℝ) → Lp ℝ s ν
  analytic : ∀ α, AnalyticOnNhd ℝ (kernelLp α) (U α)

  -- On the box, this is the Lp class of the standard-form kernel.
  kernel_eq_fa : ...

  -- Analytic factorization on a suitable neighborhood.
  factorization :
    ∀ α, ∀ u ∈ U α,
      F (g α u) = monomial (A.k α) u • kernelLp α u
```

The first concrete theorem should be:

```lean
theorem analyticChartKernelData_of_standardForm
    (hF : IsLpValuedAnalytic F U₀)
    (hcharts : ...)
    (hstandard : ...) :
    Nonempty (AnalyticChartKernelData ...)
```

Do not make `AtlasData` itself carry this extra data initially. Produce it alongside `D`, with an explicit compatibility theorem for `D.fa`.

**Go/no-go criterion:** this theorem is proved from the book’s existing hypotheses, or the bridge records exactly the additional divisibility hypothesis it needs. Everything downstream can meanwhile be conditional on this interface.

### Stage B — one coherent smooth representative

Analyticity in \(L^s\) is not yet a pathwise jet of the empirical field.

The selection interface should produce a **single** representative family, with derivatives compatible across all orders through the chosen finite order:

```lean
structure ChartKernelRep (R : ℕ) (...) where
  a : Chart → Sample → (Fin d → ℝ) → ℝ
  jointMeasurable : ...
  ae_contDiff :
    ∀ α, ∀ᵐ x ∂ν, ContDiffOn ℝ (R + 1) (a α x) (U α)

  represents :
    ∀ α, ∀ u ∈ U α, ... -- a α · u represents kernelLp α u

  represents_derivative :
    ∀ α γ, |γ| ≤ R + 1 → ∀ u ∈ U α,
      ... -- D^γ(a α ·)(u) represents D^γ(kernelLp α)(u)

  compatible_fa :
    ∀ α, ∀ᵐ x ∂ν,
      ∀ u ∈ closedBox d (rb α), a α x u = D.fa α x u
```

The last quantifier order matters: equality a.e. **simultaneously in `u`**, not just a.e. separately at every `u`.

A countable dense set plus samplewise continuity is the natural way to upgrade parameterwise representative equality.

For the envelope route, also extract, on the compact boxes,

\[
\sup_{u,\ |\gamma|\le R+1}
  |\partial^\gamma a_\alpha(x,u)|\le B_{\alpha,R}(x),
\qquad B_{\alpha,R}\in L^s.
\]

A locally convergent Banach-valued power series, smaller neighborhoods, and a finite cover are a plausible source of such envelopes. This is another real lemma, not a consequence Lean will obtain merely from `fderiv`.

### Stage C — derivative kernels are admissible for Theorem 5.9

For each finite multiindex, define the kernel
\[
a_{\alpha,\gamma}(x,u)=\partial^\gamma_u a_\alpha(x,u).
\]

The required declarations are:

1. derivative kernels represent the analytic \(L^s\)-derivatives;
2. those maps satisfy the actual `CoeffExpansion` / `IsLpValuedAnalytic` input consumed by `theorem_5_9_law`;
3. differentiation commutes with expectation;
4. the centered derivative empirical process is the derivative of the original centered empirical process.

For the bridge’s chosen sign \(\sigma\),
\[
J_{n,\alpha,\gamma}(u)
 =\frac{\sigma}{\sqrt n}\sum_{i<n}
   \bigl(a_{\alpha,\gamma}(X_i,u)
        -\mathbb E a_{\alpha,\gamma}(X_i,u)\bigr).
\]

Use the repo’s convention at `n = 0`; it has no asymptotic significance.

**Do not apply Theorem 5.9 separately and then infer a joint law.** Apply its proof/interface to the finite block family, or prove a finite-block version retaining all cross-covariances. If its parameter domain cannot directly accommodate a finite disjoint union, that adaptation is an explicit missing statement.

### Stage D — joint continuous jet law

A convenient bridge model is:

```lean
def JetIdx (d R : ℕ) :=
  {γ : Fin d → ℕ // ∑ i, γ i ≤ R}

def ChartJetSpace (R : ℕ) :=
  ∀ α : Chart, ∀ γ : JetIdx d R,
    C(closedBox d (rb α), ℝ)
```

Use finite `Chart`; later allow chart-dependent orders if useful.

The primary probability theorem should have this shape:

```lean
theorem exists_jointChartJetLimit
    (hker : AnalyticChartKernelData ...)
    (hrep : ChartKernelRep R ...)
    (hprocess : ...) :
    ∃ μJ : ProbabilityMeasure (ChartJetSpace R),
      TendstoInDistribution
        (empiricalChartJets hrep)
        atTop
        (fun J => J)
        (fun _ => P)
        (μJ : Measure (ChartJetSpace R))
      ∧ JointJetGaussianFidis μJ ...
```

The Gaussian covariance must include different charts and derivative indices:
\[
\operatorname{Cov}\!\left(
 a_{\alpha,\gamma}(X,u),
 a_{\alpha',\delta}(X,v)
\right).
\]

Two compatibility theorems are important:

```lean
theorem empiricalChartJets_zero_ae :
  ∀ n, ∀ᵐ ω ∂P, ∀ α,
    zeroJet (empiricalChartJets hrep n ω α) =
      chartField D α n ω
```

and

```lean
theorem jointJetLimit_map_zero :
  μJ.map zeroProjection =
    D.μlim.map restrictCharts
```

The latter follows by uniqueness of the weak limit once the two zero-order processes agree a.e. It prevents construction of an unrelated Gaussian extension with merely correct chart marginals.

### Stage E — feed grammar’s existing coefficient theorem

Now adapt the joint chart jets to the exact branch-jet space required by grammar:

```lean
def toClosedBranchJets :
  ChartJetSpace R → GrammarClosedBranchJetSpace ...
```

Prove the required continuity/measurability and the a.e. identification with the actual empirical branch jets. Then consume:

```lean
tendstoInDistribution_resolvedCoeff_top_closed
```

rather than rebuilding its probability argument in the bridge.

There is an important wording correction here:

> `coeffOnClosedJets` being **Borel** does not imply that convergence in distribution transfers through it.

Use the existing conditional theorem and its exact regularity hypotheses. If a particular finite-jet coefficient functional is continuous, prove or cite that separately. Do not treat “Borel function of jets” as a continuous-mapping theorem.

Also, a jet-to-coefficient law alone is not yet an unconditional **subleading evidence expansion in distribution**. That final claim additionally needs grammar’s expansion hypotheses and an appropriate remainder estimate after the relevant normalization.

---

## 4. What to do with constant identification

After correcting the count/sign audit, this is a good bounded task.

State the essential-coordinate count as `q`, with `0 < q`, and prove the algebraic identifications before the integral equality:

```lean
resSet_eq_essential
multCount_eq_q
fluctuation_eq_fluctuationFunction_beta_one
residueWeight_eq_splitWeight
faceIntegral_eq_splitIntegral
```

Then:

```lean
theorem boxFaceLimit_eq_splitLeading
    (e : Fin q ⊕ Fin s ≃ Fin d)
    (hq : 0 < q)
    (hess : ∀ i, ratioExp h k (e (.inl i)) = lam)
    (hnon : ∀ j, lam < ratioExp h k (e (.inr j)))
    (hξ : ...)
    (hη : ...) :
    boxFaceLimit h k lam q b ξ η =
      splitLeadingConstant ... (splitPullback e ξ) (splitPullback e η)
```

Only then rewrite `splitLeadingConstant` as GreyBook’s actual `boxGamma * limitY`.

Additional scope checks:

- GreyBook may allow **zero nonessential exponents** `k' j = 0`; grammar’s quoted stochastic theorem assumes positivity in every coordinate. Do not silently equate their full scopes.
- Verify whether `scaledBox` means physical coordinates, unit-box coordinates, or a box with the endpoint convention changed. A genuine dilation requires its Jacobian.
- With a pure coordinate permutation, there is no scaling Jacobian.
- The lower-endpoint inclusion differences should be handled by a.e. equality of integration domains.

This theorem belongs in the bridge. It is an excellent cross-check, but should not be sold as new leading-order probability.

---

## 5. Why (iii) is weaker than suggested

There is an order shift:

| Desired tightness | Typical deterministic envelope needed |
|---|---|
| field in `C⁰` | sup field + bound on first derivatives |
| first-order jets in a product of `C⁰` spaces | sup field and first derivatives + modulus of continuity of first derivatives |
| order-`R` jets | sup order-`R` jets + their Lipschitz/modulus control |

Thus gradient bounds give equicontinuity of the **field**, not of its gradient. A Hessian bound is a standard sufficient input for first-order jet tightness.

Also:

- `O_p(1)` bounds do not imply the `∫ Aₙ² ≤ C` hypothesis of `isTightMeasureSet_of_jetEnvelope`.
- Nevertheless, bounded-in-probability sup/Lipschitz envelopes can support a different Arzelà–Ascoli tightness proof. The moment hypothesis is sufficient, not logically necessary.
- Tightness alone does not identify the joint derivative limit; derivative fidis and compatibility are still needed.

So I would not undertake (iii) unless a named coefficient has sufficiently low required order and the available bounds match that order exactly.

---

## 6. Do not build (v) speculatively

The finite-product transfer theorem is mathematically natural, but GreyBook already has the leading-order consumer covered. Separate marginal laws would not suffice for assembly anyway; the useful input is a genuinely joint field.

If grammar later needs a finite-product asymptotic continuous-mapping lemma, prefer an **abstract finite-product result for varying maps** over another box-specific theorem. Its immediate consumer should be the resolved coefficient assembly or a second application, not a reconstruction of GreyBook 6.7.

For now:

- keep grammar dependency-free;
- put analytic extraction, representatives, and GreyBook-specific process adaptation in the bridge;
- change GreyBook only for genuinely book-relevant API exposure or corrections;
- extract generic grammar contracts when the joint-jet proof has revealed their actual shape.

## Suggested next ticket

**“Expose an analytic \(L^s\)-valued standard-form quotient compatible with `AtlasData.fa`, on neighborhoods of the chart boxes.”**

Acceptance criteria:

1. normalization and sign audits recorded;
2. precise factorization and representative compatibility statements;
3. proof from existing hypotheses, or an explicit conditional theorem identifying the missing hypothesis;
4. one derivative-kernel admissibility theorem as a test.

That ticket decides whether the bridge becomes a substantive route from the book’s analytic model to grammar’s subleading laws—or closes cleanly as a verified leading-order interoperability check.