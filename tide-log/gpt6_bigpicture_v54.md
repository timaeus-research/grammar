**Recommended scope:** finish (2) and the finite-chart version of (3), then discharge the compact-base version through a **bounded linear reconstruction interface**. Implement a concrete tangential Taylor reconstruction only when the chart presentation already supplies a common product polydisc and radius margins.

Two qualifications are important:

- Separate the **coefficient moment argument**, which needs only measurable torus data and an envelope, from **analytic reconstruction**, which needs holomorphy and appropriate boundary regularity.
- Hypothesis I as an `L²`-valued analytic statement does **not by itself furnish a jointly measurable, pointwise analytic representative after division**. That representative, analytic divisibility, and the complexified-chart inclusion must remain explicit chart-presentation assumptions unless separately proved.

Below, theorem signatures are proposed interfaces, not claims about existing identifier names.

## 1. First: measurable Cauchy coefficients

This is the highest-leverage technical lemma. Prove it for complex coefficients; obtain real coefficients by composition with `Complex.re`.

Suggested interface:

```lean
theorem measurable_polyCoeff_param
    (hR : 0 < R)
    (hA : Measurable (fun p : 𝓧 × (Fin d → ℂ) => a p.1 p.2))
    (hcont : ∀ x, ContinuousOn (a x) (torusSet d R)) :
    Measurable (fun x => polyCoeff d R (a x) γ)
```

You may be able to omit `hcont` for measurability because the Bochner integral is totalized. Nevertheless, continuity on the torus gives integrability at every parameter and is useful for all subsequent identities. **Do not spend time optimizing away this assumption initially.**

### Implementation route

Rewrite each circle average using its angle parametrization and prove measurability recursively through `iterOp`.

At each step:

1. the circle insertion map is continuous;
2. multiplication by the inverse-power kernel is measurable;
3. integration against the fixed angle measure preserves parameter measurability;
4. the intermediate function remains jointly measurable in the sample parameter and the remaining circle variables.

Keep the “remaining variables” in the measurable parameter throughout the induction. A theorem merely asserting measurability in `x` at a fixed intermediate point is not enough for the next integration.

**Mathlib inputs to grep:** the stated `StronglyMeasurable.integral_prod_right'`, the corresponding measurable/AEStronglyMeasurable integral lemmas, the angle-integral definition of `circleIntegral`, and measurable products/compositions. Since the codomain is `ℂ`, separability removes the usual measurable-versus-strongly-measurable obstacle.

**Trap:** separate measurability alone is insufficient. Separate measurability in `x` plus continuity in the finite-dimensional complex variable is a viable Carathéodory route, but use joint measurability as the initial interface rather than formalizing that theorem here.

---

## 2. The torus-envelope moment certificate

Make the central theorem weaker than `AnalyticChartCertificate`. Holomorphy is not needed to bound these coefficients.

A useful sampling-independent package is relative to the observation law `q`:

```lean
structure TorusL2Certificate (q : Measure 𝓧) (d : ℕ) (R : ℝ) where
  a : 𝓧 → (Fin d → ℂ) → ℂ
  envelope : 𝓧 → ℝ
  radius_pos : 0 < R
  measurable_a : Measurable (fun p => a p.1 p.2)
  continuous_torus : ∀ x, ContinuousOn (a x) (torusSet d R)
  envelope_nonneg : ∀ x, 0 ≤ envelope x
  envelope_L2 : MemLp envelope 2 q
  torus_bound :
    ∀ x w, w ∈ torusSet d R → ‖a x w‖ ≤ envelope x
```

Add measurability of the envelope explicitly if convenient; `MemLp` supplies only the corresponding a.e. strong measurability.

For

```lean
c x γ := polyRealCoeff d R (C.a x) γ
```

prove:

```lean
∀ γ, Measurable (fun x => c x γ)
∀ γ, MemLp (fun x => c x γ) 2 q
∀ γ,
  Real.sqrt (∫ x, (c x γ)^2 ∂q)
    ≤ Real.sqrt (∫ x, (C.envelope x)^2 ∂q)
        * (R⁻¹) ^ totalDegree γ
```

Then, assuming the existing hypotheses on `b` and `b < R`:

```lean
∀ x, AbsSummableAt (c x) b

Summable (fun γ =>
  b ^ totalDegree γ *
    Real.sqrt (∫ x, (c x γ)^2 ∂q))
```

The proof should stay close to the existing API:

- `Complex.abs_re_le_norm` or the corresponding norm lemma;
- `norm_polyCoeff_le`;
- `MemLp` domination and scalar multiplication;
- monotonicity of `eLpNorm`, or direct square-integral comparison;
- identification of the real `L²` norm with `sqrt (∫ f²)`;
- `summable_of_cauchy_envelope`.

**Important:** establish `MemLp` before manipulating the real integral of the square. Otherwise the totalized integral can conceal missing integrability.

Finally transfer these assertions to `P` along `X 0`, using `Measure.map (X 0) P = q` or `IdentDistrib`, and invoke `summableCoordL2_sampleObs`.

**No centering factor is needed here:** your CLT accepts uncentered observations and centers inside `empiricalSum`. Only a separate certificate for already-centered coefficients would introduce an extra estimate.

---

## 3. Hypothesis-I division bridge, then analytic identification

This is where the “derived from Hypothesis I” claim should be located.

Keep the original parameter-space function distinct from its pullback:

```lean
f : 𝓧 → WComplex → ℂ
πC : (Fin d → ℂ) → WComplex
a : 𝓧 → (Fin d → ℂ) → ℂ
```

The bridge assumes:

```lean
hdiv :
  ∀ x w, w ∈ torusSet d R →
    f x (πC w) = (∏ i, w i ^ k i) * a x w

himage :
  ∀ w ∈ torusSet d R, πC w ∈ Wallowed

hfbound :
  ∀ x z, z ∈ Wallowed → ‖f x z‖ ≤ H x

hH2 : MemLp H 2 q
```

Together with the representative/measurability/regularity assumptions needed in Unit 2, conclude a torus certificate with

```lean
M x := H x * (R⁻¹) ^ (∑ i, k i)
```

Prove the norm identity on the torus first:

\[
\|a(x,w)\|
 = \|f(x,\pi_{\mathbb C}(w))\|\,R^{-\sum_i k_i}.
\]

Here `R > 0` guarantees every divisor factor is nonzero. No estimate near the exceptional divisor is required.

### What is external?

Explicitly retain:

- the existence of the complexified chart;
- its torus inclusion in the Hypothesis-I neighbourhood;
- the analytic divisible representative `a`;
- enough measurable-representative compatibility to use the pointwise formulas.

On the torus, measurability of `a` can alternatively be obtained from the measurable pullback divided by the nonvanishing monomial. Thus a **torus-restricted measurability variant** may ultimately be more faithful and weaker than global joint measurability of `a`.

### Which part of Hypothesis I?

**Only the order-zero `L²` envelope is needed for this argument.** Neither the `Q ≥ 1` derivative envelopes nor the additional likelihood moment condition enters this coefficient CLT certificate.

Do not literally define the envelope using an arbitrary uncountable supremum unless its existence and measurability have already been established. Accept the paper’s measurable `L²` envelope as the input.

### Analytic identification

Extend the moment certificate by hypotheses sufficient for the existing reconstruction theorem:

- `SliceHolo d r (a x)`;
- the closed-polydisc bound required by `hasSum_polyCoeff`;
- real-valuedness on the real reconstruction domain.

Prefer the radius convention

\[
0<b<r<R,
\]

where `R` is a holomorphic-neighbourhood radius and `r` is the **Cauchy integration radius**. Apply Units 1–2 with radius `r`.

A torus bound alone should not silently be passed as a closed-polydisc bound. Either:

1. use the division estimate on the torus plus an iterated maximum-modulus argument, with the required continuity/holomorphy; or
2. prove the reconstruction theorem with torus boundary data.

The first route is more compatible with your present API.

Prove the real reconstruction without first proving every complex coefficient is real:

\[
\sum_\gamma \operatorname{Re}(c_\gamma^{\mathbb C}(x))u^\gamma
 = \operatorname{Re}(a(x,u)).
\]

Then real-valuedness identifies the right side with the paper’s `a`. Taking real parts through an absolutely convergent series is enough.

---

## 4. Close (2): the paper-facing chart stochastic theorem

Add one wrapper around `sample_stochastic_expansion`:

```lean
theorem sample_stochastic_expansion_of_analytic_chart
    (C : AnalyticChartCertificate q ...)
    (hXmeas : ∀ i, Measurable (X i))
    (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = q)
    ... :
    -- existing chart stochastic-expansion conclusion
```

The certificate should provide the conclusions from Units 2–3, not require the user to re-enter `hc2` and `hsum`.

Also prove an identification lemma for the empirical phase:

\[
\operatorname{phase}(D_n)(u)
 = n^{-1/2}\sum_{i<n}
       \bigl(a(X_i,u)-\mathbb E_q a(X,u)\bigr)
   + \operatorname{phase}(A)(u).
\]

For the paper’s amplitude-only `A`, the last term vanishes.

**Best proof:** use the bounded linear evaluation functional on the weighted coefficient space. It commutes with finite sums and Bochner integration. This also explains the scaling: a slot stores `b^{|γ|} c_γ`, so evaluation uses the corresponding normalized monomial. Check this against the actual `dataPhase` convention rather than asserting `evalF c` and `dataPhase` are definitionally the same.

**Stop checkpoint:** (2) is complete once this wrapper and the exact empirical-phase identification compile. Analytic divisibility remains an assumption, not an unproved theorem hidden in the headline.

---

## 5. Joint charts over point bases: one stacked observation

This is the unconditional next target for (3).

Let

```lean
J := Σ I : Fin M, DataIdx (n I + 1)
```

and define, from a **single observation** `x`,

```lean
V x : L1Seq J
```

by stacking all chart `phaseObs` values.

Prove a generic finite stacking lemma:

```lean
theorem summableCoordL2_stack
    (h : ∀ I, SummableCoordL2 q (Y I)) :
    SummableCoordL2 q (stack Y)
```

Its content is finite summation of the coordinate `L²` sums. Membership in `ℓ¹` is also finite summation of the chart norms.

Construct

```lean
unpack :
  L1Seq J →L[ℝ] (∀ I : Fin M, DataSpace (n I + 1))
```

and prove its coordinate formulas. Coordinate restriction is contractive; finite-product assembly is continuous.

Apply `clt_l1` once to `V ∘ X`, then `continuous_comp` with `unpack` and deterministic translation by the amplitude data.

**Do not combine separately obtained chart limits.** Marginal convergence cannot recover the common-sample coupling.

### Cross-chart covariance

Include a finite-coordinate target theorem. For phase coordinates:

\[
\operatorname{Cov}(G_{I,\gamma},G_{J,\delta})
 =
 b_I^{|\gamma|}b_J^{|\delta|}
 \int
 (c_{I,\gamma}-\mathbb E_q c_{I,\gamma})
 (c_{J,\delta}-\mathbb E_q c_{J,\delta})\,dq.
\]

Amplitude coordinates have zero random covariance when their data are deterministic. The translated limit is generally **not centered**, though its Gaussian fluctuation is.

**Instances:** finite `Fin M`, finite multiindices, sum indices, and dependent sigma indices should synthesize `Countable`; use `classical` for `DecidableEq` if no computable index manipulation is required.

---

## 6. Compact bases: finish the joint theorem through a reconstruction interface

This is bounded and should be included now. Make concrete tangential analyticity a later constructor of this interface.

Use a countable latent coefficient index `J` and assume

```lean
T : L1Seq J →L[ℝ] JointData K n
A : JointData K n
V : 𝓧 → L1Seq J
hV : SummableCoordL2 q V
```

Define

```lean
D N ω := T (empiricalSum (fun i ω => V (X i ω)) P N ω) + A
```

Then prove:

```lean
∃ Λ : ProbabilityMeasure (JointData K n),
  TendstoInDistribution D atTop id (fun _ => P) Λ
```

with `Λ` explicitly the pushforward of the latent CLT law by `z ↦ T z + A`.

Compose this immediately with `tendstoInDistribution_assembled`, retaining its decomposition, residual, and asymptotic-scale hypotheses.

### Topology audit

`JointData` must carry the existing topology:

- sup-norm topology on each `C(K I, DataSpace ...)`;
- finite product topology across charts.

For finite products of Banach spaces, this agrees with the usual product norm topology. Do not introduce a coordinatewise-in-`K` topology: that would be too weak for the assembled theorem.

Evaluation at a base point and extraction of a coefficient are continuous linear maps. Consequently the same common-sample covariance formula applies across **different charts and different base points**, using the corresponding reconstructed observable.

### Concrete constructor: narrowly scoped

Your proposed tangential expansion is sound if you already have **joint holomorphic extension in tangential and normal variables**, common product polydiscs, and an `L²` envelope on their product torus.

Use weighted coefficients

\[
d_{\alpha,\gamma}
  = \rho^{|\alpha|}b^{|\gamma|}c_{\alpha,\gamma},
\]

with `‖t_i‖ ≤ ρ` on `K` and Cauchy radii strictly larger than `ρ` and `b`. Reconstruction into the normal-data space uses `(t/ρ)^α`, giving

\[
\sup_{t\in K}\|Tz(t)\|_{\ell^1}\le \|z\|_{\ell^1}.
\]

Uniform convergence of polynomial partial sums gives continuity for **every** `z ∈ ℓ¹`. This is stronger than merely applying `continuous_dataSpace_of_majorant` to a particular analytic family.

A normalized `1 < r < R` formulation is fine after rescaling. The factors `ρ^{|α|}` and `b^{|γ|}` must be visible in the coefficient definition; do not reconcile the APIs by inequalities alone.

**Boundary of scope:** separate chartwise normal analyticity plus compactness of `K` is not sufficient for this constructor. If product-polydisc hypotheses are unavailable, stop at the precise `T` interface.

---

## 7. Final integration audit and stop rule

Do these small checks, but do not let them expand into another programme:

1. **Set `Nseq n = n` explicitly** when the paper uses the sample size as its asymptotic parameter. Supply eventual positivity/divergence; `n = 0` is irrelevant to `atTop`.
2. Verify the paper’s sign and centering convention against `empiricalSum`.
3. Keep deterministic amplitude data and random phase data distinct.
4. Record which assumptions remain external in the final headline.

### Non-claims

This work does **not** establish:

- existence of the resolved analytic chart presentation;
- pointwise analytic representatives from abstract `L²` analyticity alone;
- chart independence;
- a compact-base CLT from coordinatewise normal moment bounds alone;
- the off-minimum `Z^{(2)}` tail estimate.

The chart CLT can yield `O_p(1)` sup norms on compact reconstruction domains by continuous mapping. It does **not** by itself control `sup_{K≥ε}|ψ_n|` on an uncovered/global parameter region. That needs its own uniform law or tail argument.

### Stop rule

Declare this consult’s implementation complete when:

- Hypothesis-I order-zero envelopes plus explicit resolution-presentation assumptions produce the chart moment certificate;
- the sample phase is identified with the paper’s `ξ_n`;
- one stacked CLT gives finite-chart convergence and cross-chart covariance;
- the compact-base assembled theorem is discharged under a stated bounded linear reconstruction hypothesis.

Only implement the concrete tangential constructor if the required joint product-polydisc presentation is already present. Otherwise it is a clean additional analytic task—not a reason to delay completion of (2) and the common-sample joint theorem.
