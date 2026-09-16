## Recommendation

**Make the next programme the joint law of all coefficients in a fixed finite truncation**, not just the leading coefficients. Start with the deterministic continuity theorem for lower coefficients, then reuse the bridge’s existing joint jet convergence.

This is the largest mathematical upgrade available from the machinery already built:

> The evidence has a finite expansion with a jointly convergent vector of random coefficients, and a negligible remainder at the prescribed scale.

At present you have the remainder half of that statement. The grey book already supplies a leading evidence law, so leading-constant identification is important reconciliation, but is not, by itself, as large a new probabilistic theorem.

I have not inspected the repository. Below, names marked **new** are proposed declarations; names from your message are treated as existing. The Lean statements are interface sketches, not claims about the current implicit arguments.

---

# 1. Ranked programme

### 1. Joint finite-cutoff coefficient laws — principally (c), with an easy part of (b)

For a finite atlas and fixed cutoffs \(U_\alpha\), collect the coefficients actually appearing in the chart spectral sums:
\[
C_n=\left(
  \operatorname{empCoeffRect}
  (\eta_\alpha)(-\mathrm{globalField}_{\alpha,n})
  h_\alpha k_\alpha b_\alpha\,\mu\,q
\right)_{(\alpha,\mu,q)\in I}.
\]

Prove
\[
C_n\Rightarrow C_\infty,
\]
where \(C_\infty\) is an explicitly defined continuous functional of the **joint limiting realizable jet**.

Combine this with the landed expansion:
\[
n^A\left(E_n-\sum_{(\alpha,\mu,q)\in I}
 C_{n,\alpha,\mu,q}\,\psi_{\mu,q}(n)\right)
 \longrightarrow 0
\quad\text{in probability}.
\]

Here \(\psi_{\mu,q}\) must be taken from the actual definition of `absSpectralSum`, rather than reconstructed from a convention about logarithms.

**What is new:** all retained coefficient laws, their dependence across orders and charts, and a distributionally identified finite random expansion.

**Important terminology:** this is a coefficient *limit theorem*, generally not a coefficient CLT. Exponentials of Gaussian fields and their coefficient functionals need not be Gaussian.

Do not make intrinsic lattice vanishing a prerequisite. Chart-labelled indices already give a valid finite expansion; zero-padding gives a common ambient index set.

### 2. Identify the leading functional and recover the grey-book leading law — (a)

Prove a deterministic identity, with all normalisations explicit, between
\[
\operatorname{boxFaceLimit}(\operatorname{boxExt}G)
\quad\text{and}\quad
\operatorname{boxGamma}\cdot\operatorname{limitY}.
\]

Ideally prove this for every continuous field for which both constructions make sense. Otherwise prove it on the closed realizable support of the limiting field.

Then identify the globally aggregated leading coefficient, including charts with the same dominant exponent/logarithmic order, and show that the expansion recovers `theorem_6_7_of_process`.

**Value:** an excellent mathematical consistency theorem and the cleanest certification that the two formalisations use the same constants. It should follow soon after, or run as a small parallel deterministic task.

### 3. Observable insertion, then posterior ratios — (f)

First prove the expansion and coefficient laws for
\[
E_n(f)=\int f\,e^{-nK_n}\,d\nu.
\]

For smooth chart pullbacks, this should replace the chart weight by
\[
\eta_{\alpha,f}=\eta_\alpha(f\circ g_\alpha).
\]

Then prove joint numerator/denominator convergence and, under almost-sure positivity of the limiting denominator, a posterior expectation limit:
\[
\frac{E_n(f)}{E_n(1)}\Rightarrow
\frac{C_\infty(f)}{C_\infty(1)}.
\]

Start with bounded \(f\), so the evidence tail estimate controls the inserted tail. Unbounded observables require genuinely new tail hypotheses.

### 4. Intrinsic spectral support and canonical aggregation — the substantive part of (b)

Prove
\[
\mu\notin\Lambda(h,k)
\implies
\operatorname{empCoeffRect}\eta\zeta hkb\,\mu\,q=0,
\]
together with any sharper multiplicity/log-degree restrictions justified by the coefficient construction.

Then aggregate charts into canonical global coefficients. The useful theorem is not merely “there is a common denominator”; it is that the total coefficients have **identified intrinsic support**.

Common ambient reindexing is much cheaper and should be done whenever convenient, without waiting for this theorem.

### 5. Derive analytic chart hypotheses from geometric data — (d), selectively

A theorem extracting the required weight regularity, vanishing and box-containment properties from a sufficiently strong resolution/partition-of-unity construction is valuable.

Merely introducing an `AtlasDataPlus` record containing the missing assumptions is not the next mathematical milestone. It is acceptable scaffolding for programmes 1–3, but should not become the headline.

Also, strict positivity of every \(k_i\) is not a harmless bookkeeping assumption: zero-exponent directions may require separation from exceptional directions rather than an extraction lemma.

### Small opportunistic theorem: spectral-gap strengthening

If increasing \(U\) to \(V>U\) adds no terms to the actual truncation, then the remainder theorem at \(V\) strengthens the remainder for the truncation at \(U\).

This can turn a boundary-scale estimate into an \(o_P\) estimate without identifying an error constant. The precise result depends on whether `absSpectralSum` uses `< U` or `≤ U`, and on having enough jets for \(V\).

---

# 2. Concrete Lean plan for programme 1

## Stage 0 — Fix a finite family of coefficient queries

Use the index set already underlying `absSpectralSum`; do not first redesign the spectrum API.

For the deterministic theorem, a convenient interface is a finite family:

```lean
variable {ι : Type*} [Fintype ι]
variable (μ : ι → ℝ) (q : ι → ℕ)
```

Require that each query is in the retained spectral range at cutoff `U`. This can initially be expressed using membership in the existing spectral-sum finset.

For the atlas theorem use a finite dependent sum:

```lean
-- Conceptual index:
-- I := Σ α, CoeffIndex α
```

This retains chart labels and avoids every cross-chart lattice issue.

**First audit:** unfold `empCoeffRect` and identify the derivative order needed by each retained coefficient. Try to prove that

```lean
requiredOrder h k U ≤ R
```

suffices. Do not assume this merely because it suffices for the remainder. If a boundary coefficient needs a safety margin, state the theorem using a cutoff `V > U` and `requiredOrder h k V ≤ R`.

That distinction should be resolved before launching the probability work.

## Stage 1 — Prove a linear coefficient estimate for the amplitude

The likely best route is through the deterministic coefficient operator applied to
\[
a=\eta e^{-\zeta}.
\]

Below the top order, the new analytic issue is usually continuity of finite-part/Taylor-subtracted integrals, not continuity of exponentiation.

Target a theorem of the following form:

```lean
-- NEW; schematic
theorem rectCoeff_sub_le_jetNorm
    (hR : coefficientOrder ... ≤ R)
    (hμq : admissibleCoefficient ... μ q)
    (ha : admissibleAmplitude a)
    (ha' : admissibleAmplitude a') :
    |rectCoeff a ... μ q - rectCoeff a' ... μ q|
      ≤ C * ‖cubeJet R b a - cubeJet R b a'‖
```

If the underlying coefficient operator is linear in the amplitude, formalise that first. It makes the estimate a bound on one difference rather than two expansions.

### What should carry the proof

* The actual finite decomposition used to define `empCoeffRect`.
* Existing Taylor-remainder estimates used by `RectRemainderUniform`.
* Integrable majorants for the endpoint-singular terms after Taylor subtraction.
* Finite-sum norm bounds and evaluation bounds for continuous multilinear maps.

For integral estimates, useful Mathlib declarations to inspect include:

* `norm_integral_le_integral_norm`
* `MeasureTheory.Integrable.mono'`

The exact imported variants may differ. The core proof should be an explicit domination argument, not a broad appeal to continuity under the integral.

### Crucial trap

Do **not** separate a convergent Taylor-subtracted integral into divergent summands. Establish continuity for the cancellation-preserving expression.

Also, a uniform bound
\[
|c(a)|\le C
\]
does not establish continuity. What you need is the corresponding estimate for \(a-a'\), or an equivalent dominated-convergence proof.

## Stage 2 — Prove local Lipschitz continuity in the field jet

Add the difference counterpart of `FieldJetUniform`:

```lean
-- NEW; schematic
theorem cubeJet_mul_exp_neg_sub_le
    (hζ : ContDiff ℝ ⊤ ζ)
    (hζ' : ContDiff ℝ ⊤ ζ')
    (hB : ‖cubeJet R b ζ‖ ≤ B)
    (hB' : ‖cubeJet R b ζ'‖ ≤ B) :
    ‖cubeJet R b (fun x => η x * Real.exp (-ζ x))
      - cubeJet R b (fun x => η x * Real.exp (-ζ' x))‖
      ≤ Cη R B * ‖cubeJet R b ζ - cubeJet R b ζ'‖
```

The constant may grow exponentially in `B`; probability only needs a finite constant on each ball.

Combine Stages 1–2 to get:

```lean
-- NEW; schematic
theorem empCoeffRect_sub_le_on_jetBall
    (hR : requiredOrder h k V ≤ R)
    (hindex : retainedCoefficient ... U μ q)
    (hUV : U < V)
    (hζ : ContDiff ℝ ⊤ ζ)
    (hζ' : ContDiff ℝ ⊤ ζ')
    (hB : ‖cubeJet R b ζ‖ ≤ B)
    (hB' : ‖cubeJet R b ζ'‖ ≤ B) :
    |empCoeffRect η ζ h k b μ q
      - empCoeffRect η ζ' h k b μ q|
      ≤ C * ‖cubeJet R b ζ - cubeJet R b ζ'‖
```

Remove `V` if the order audit shows that `U` itself suffices.

For a finite query family, take the maximum of the constants or prove the vector estimate directly.

## Stage 3 — Descend to realizable jets and extend to their closure

There are two distinct descent steps.

### 3a. Dependence only on the finite jet

The difference estimate immediately proves:

```lean
-- NEW
theorem empCoeffRect_eq_of_cubeJet_eq
    (hjet : cubeJet R b ζ = cubeJet R b ζ') :
    empCoeffRect η ζ h k b μ q
      = empCoeffRect η ζ' h k b μ q
```

This allows the coefficient to be defined on the image of smooth fields under `cubeJet`.

### 3b. Define the coefficient at the limiting jet

If the existing “closed realizable cube jets” are a closure of smooth jets, use the locally Lipschitz estimate to extend the coefficient uniquely to that closure.

This matters: a limiting finite-order jet need not be the jet of a smooth field. A definition that chooses a smooth representative for every limit jet is generally unavailable.

The headline should be:

```lean
-- NEW; S is the existing closed realizable-jet subtype
def rectCoeffOnRealizableJets : S → ℝ

theorem continuous_rectCoeffOnRealizableJets :
    Continuous (rectCoeffOnRealizableJets ...)

theorem rectCoeffOnRealizableJets_cubeJet :
    rectCoeffOnRealizableJets ... ⟨cubeJet R b ζ, ...⟩
      = empCoeffRect η ζ h k b μ q
```

**Reuse the construction behind `chartTopCoeffLaw` if it already solves this extension problem.** Generalise the analytic input, rather than building a second support/extension framework.

An alternative is to define the Taylor-subtraction coefficient directly on the ambient jet tuple, including non-realizable tuples. That can yield a globally continuous map without a support-extension argument. It is attractive only if the existing formula naturally supports it.

Do not use an arbitrary “choose a representative” definition: jet invariance alone does not provide continuity or measurability of such a choice.

## Stage 4 — Apply the continuous mapping theorem jointly

Use exactly the joint jet-valued convergence that carries `jointChartTopCoeffLaw`.

The required input is conceptually:

```lean
-- Y n : Ω → JointJetSpace
-- Ylim : Ωlim → JointJetSpace
hY : TendstoInDistribution Y atTop Ylim ...
hYn : ∀ n, ∀ᵐ ω ∂P, Y n ω ∈ jointRealizableSet
hYlim : ∀ᵐ ω ∂Plim, Ylim ω ∈ jointRealizableSet
```

The output is:

```lean
-- NEW; argument order schematic
theorem jointChartCoeffLaw :
    TendstoInDistribution
      (fun n ω i =>
        empCoeffRect
          (unitWt i.chart)
          (-globalField i.chart n ω)
          ... i.μ i.q)
      atTop
      (fun ω i => limitCoeff i (Ylim ω))
      ...
```

For exact Mathlib names, grep the `TendstoInDistribution` namespace for its continuous-mapping and a.e.-congruence lemmas. Copying the invocation in `jointChartTopCoeffLaw` is safer than guessing a newer API spelling.

### Probability traps

1. **Marginal convergence is insufficient.** Preserve the common limiting process and cross-chart dependence.
2. **A \(C(K)\) CLT does not generically give derivative convergence.** Use the bridge’s actual `chartJetReconstruct` construction and its established convergence. Do not introduce a silent \(C^R\) CLT.
3. **A.e. identification is not literal measurability.** Define coefficients using the measurable jet representative, then transfer to the raw field formula by a.e. equality using the existing conventions.
4. **Closed support alone does not make an ambient extension continuous.** Either work correctly with subtype-valued laws or reuse the existing continuous-extension mechanism.

## Stage 5 — State the stochastic expansion as a theorem, not just a bundle of lemmas

The final theorem should expose two conclusions:

1. the retained coefficient vector converges in distribution;
2. the scaled residual converges to zero in probability.

An optional stronger presentation is joint convergence:
\[
(C_n,\;n^A R_n)\Rightarrow(C_\infty,0).
\]

That is a Slutsky-type consequence, not an independence assertion. It provides a particularly useful API for subsequent leading-term extraction and observable ratios.

The remainder conclusion should be supplied directly by `tendstoZeroInProb_evidence_expansion`. No new evidence decomposition should be needed.

### Hypothesis packaging

Use a small chart-analytic record extending or referring to the existing M6b data, containing only the genuinely extra assumptions:

* box geometry and positivity assumptions required by the deterministic theorem;
* `0 < k α i`;
* smooth unit weights;
* the exact vanishing/support hypothesis needed by Stage 1;
* `g_α(box) ⊆ K₀`;
* the jet-order inequality.

Do **not** put “coefficient map is continuous” into the public hypothesis record. That is the new theorem to prove.

Likewise, do not inherit `DeepVanishing` automatically from the top-coefficient law: check whether all lower coefficients need the same condition, a stronger one, or none because the rectangular coefficient construction already handles the boundary.

---

# 3. Corrections and qualifications to the landed-results description

## A. The stated `FieldJetUniform` constant needs checking

As literally written, a jet bound on \(\zeta\) cannot give an unweighted bound on \(\eta e^{-\zeta}\) with constant
\[
2^{|p|}|p|!\,B_\eta(1+B)^{|p|}
\]
and no exponential factor.

At \(p=0\), take \(\eta=1\) and \(\zeta=-B\). The left side is \(e^B\), while the quoted constant is \(1\).

The actual theorem presumably has one of:

* an \(e^{-\zeta(x)}\) factor retained on the right;
* a lower bound such as \(\zeta\ge0\);
* an additional \(e^B\) factor;
* a convention in which \(B_\eta\) already absorbs that factor.

This is a correction to the **summary**, not a claim that the checked theorem is wrong. Inspect that statement first. A derivative bound excluding order zero would not control the exponential at all without a separate lower bound.

## B. “At every polynomial rate” is conditional on available jet orders

With one fixed `R`, you only obtain the cutoffs satisfying
\[
\operatorname{requiredOrder}(h_\alpha,k_\alpha,U_\alpha)\le R.
\]

The theorem is available at every polynomial rate **provided the corresponding higher-order jet convergence/tightness hypotheses are available at each rate**.

Do not turn a theorem schema quantified over `R` into an all-orders conclusion from one fixed finite-order CLT.

## C. “Only \(O_P\) at the cutoff” needs its logarithmic scale

The immediate tightness consequence is
\[
R_n=O_P\!\left(n^{-U}(1+\log n)^{d-1}\right).
\]

It is not generally
\[
n^U R_n=O_P(1)
\]
when \(d>1\).

At the natural boundary normalisation
\[
s_n=\frac{n^U}{(1+\log n)^{d-1}},
\]
the deterministic estimate plus uniform jet tails gives boundedness in probability. The landed vanishing theorem, whose hypothesis is `s n * rate n → 0`, does not itself assert this boundary result.

Also, the cutoff obstruction is not always intrinsic: spectral gaps and a higher available cutoff can improve it.

## D. Common-index expansion does not require intrinsic lattice vanishing

You can already take the finite union of the chart ambient index sets and define
\[
C_{\mu,q,n}
=
\sum_\alpha
\mathbf 1_{\{(\mu,q)\in I_\alpha\}}\,
c_{\alpha,\mu,q,n}.
\]

This gives an exact common-index expansion. A common denominator can similarly be obtained by an appropriate multiple of the `Qamb` values, subject to the actual lattice convention.

What remains open is identifying this zero-padded coefficient with an unrestricted sum of `empCoeffRect` values, or proving support on the intrinsic lattices. Those are stronger statements.

## E. Lack of error constants does not prevent an asymptotic expansion

A Poincaré asymptotic expansion does not require identified leading constants for its remainder.

Your genuinely missing feature is better described as:

> a coherent, distributionally identified coefficient hierarchy, with canonical spectral support and controlled truncations.

The landed theorem is already a substantial **finite-cutoff stochastic spectral expansion**. Programme 1 turns it into the corresponding expansion with joint coefficient laws.

---

**Suggested next headline:**  
`jointChartCoeffLaw` plus `evidence_expansion_with_jointCoeffLaw`.

The first hard theorem should be the lower-coefficient **difference estimate on jet balls**. Everything after it should deliberately reuse the top-coefficient support machinery and the landed evidence remainder theorem.