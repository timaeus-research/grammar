## Recommendation

**Yes: the two-sided population-integral theorem is worth a headline.** It is a substantial, coefficient-free consequence of the resolution input, and continuous units suffice.

But I would **not** make `MonomialResolutionData → AdaptedStrataData` the next target. Two distinct issues intervene:

1. Analyticity of the units is not exported, although it may be **recoverable from the exported equations**.
2. More seriously, a finite chart cover does not automatically supply the **normal-analytic, chart-exact localisation** required by grammar. Analytic units alone do not fix that.

The clean immediate route is

\[
\text{hironaka E5}
\;\longrightarrow\;
\text{two-sided sublevel estimate}
\;\longrightarrow\;
\text{two-sided Laplace estimate}.
\]

That last arrow is an elementary **Abelian** estimate, not a Tauberian theorem. It should not require reopening grammar’s exact Mellin coefficient machinery.

I have not independently checked the repositories or their builds. Below, Lean statements involving new definitions are proposed interfaces, not claims about existing declarations.

---

## Corrections to the proposed gaps

### 1. Continuous unit absorption is not even automatically a homeomorphism

The substitution
\[
z_j=y_j\,|u(y)|^{1/e_j}
\]
with a merely continuous positive unit need not be locally injective. It certainly does not supply a continuous Jacobian.

With an **analytic** positive unit, at a centre where \(y_j=0\), the derivative of this map has determinant
\[
u(y)^{1/e_j}>0.
\]
The analytic inverse-function theorem then applies locally. Both “at a zero coordinate” and “locally, after shrinking” matter.

Also, the substitution generally sends a box to a **curved domain**. Shrinking to a box in the new coordinates changes what part of the old chart is represented. That is another localisation issue, not merely a coordinate-change lemma.

### 2. The analytic-unit information may not actually be lost

There is a plausible independent recovery theorem:

> If \(g\) is real analytic on an open set and
> \[
> g(y)=u(y)\prod_i y_i^{e_i}
> \]
> there, with \(u\) continuous, then \(u\) is real analytic.

This is removable division by coordinate monomials: divide analytic power series by the coordinate factors, then identify the quotient with \(u\) on the dense complement of the coordinate hyperplanes.

Consequently:

- For the phase unit, one additionally needs \(F\circ\phi\) analytic on the relevant neighbourhood.
- For the Jacobian unit, one needs analyticity of \(y\mapsto\det D\phi(y)\).

This is a nontrivial Lean library project, but it means “continuous units in the frozen record” is not necessarily a mathematical obstruction. Requesting the stronger record is still the cheapest route.

### 3. The exponent-pair aggregation needs a precise convention

For a relevant chart with normal indices \(S=\{i:e_i>0\}\),
\[
\lambda_\alpha=\min_{i\in S}\frac{h_i+1}{e_i},
\qquad
m_\alpha=\#\left\{i\in S:\frac{h_i+1}{e_i}=\lambda_\alpha\right\}.
\]

When \(e_i=2k_i\), this is grammar’s normalisation.

Across positive contributions:

- take the **smallest** \(\lambda_\alpha\);
- among charts attaining that minimum, take the **largest** \(m_\alpha\).

It is not the ordinary lexicographic minimum of \((\lambda,m)\).

Orthant reflection does not change these ratios. Nor should every formal chart necessarily enter the minimum: one needs the charts that genuinely contribute, with the lower-bound/nondegeneracy assumptions used by the readout.

### 4. A signed observable invalidates the proposed sandwich

Resolution of the phase determines the exponent pair of the **unweighted volume** or a suitably positive weighted integral. It does not determine it for arbitrary analytic `obs`.

Examples include `obs = 0`, cancellation between charts, and observables vanishing on the dominant exceptional locus.

For the immediate theorem use either:

- `obs = 1`; or
- a nonnegative weight bounded above globally and bounded below by a positive constant near the zero locus.

Strictly positive continuous prior and observable on an appropriate compact neighbourhood suffice. Merely “analytic prior and observable” does not.

---

# Ranked plan: eight theorem units

The first three constitute the recommended headline. Units 4–7 are reusable geometry. Unit 8 formalises why the exact bridge must not yet be claimed.

## Unit 1 — Two-sided sublevel growth implies two-sided Laplace growth

Introduce a small, resolution-independent interface:

```lean
def powerLogRate (λ : ℝ) (q : ℕ) (N : ℝ) : ℝ :=
  Real.rpow N (-λ) * Real.log N ^ q

def HasSmallSublevelBounds
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (λ : ℝ) (q : ℕ) : Prop :=
  ∃ a b ε : ℝ,
    0 < a ∧ 0 < b ∧ 0 < ε ∧ ε < 1 ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) ε,
      a * Real.rpow t λ * Real.log (1 / t) ^ q
        ≤ μ.real {x | f x < t} ∧
      μ.real {x | f x < t}
        ≤ b * Real.rpow t λ * Real.log (1 / t) ^ q

def HasLaplaceBounds
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (λ : ℝ) (q : ℕ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ᶠ N : ℝ in Filter.atTop,
      a * powerLogRate λ q N
        ≤ ∫ x, Real.exp (-N * f x) ∂μ ∧
      (∫ x, Real.exp (-N * f x) ∂μ)
        ≤ b * powerLogRate λ q N
```

Target:

```lean
theorem HasSmallSublevelBounds.hasLaplaceBounds
    [IsFiniteMeasure μ]
    (hf : Measurable f)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hλ : 0 < λ)
    (hsub : HasSmallSublevelBounds μ f λ q) :
    HasLaplaceBounds μ f λ q
```

### Proof

Lower bound:
\[
L(N)\ge e^{-1}\,\mu\{f<1/N\}.
\]

Upper bound: either layer cake,
\[
L(N)=N\int_0^\infty e^{-Nt}\,\mu\{f<t\}\,dt,
\]
or a dyadic decomposition of the sublevels. Beyond the small-sublevel threshold, finite mass gives an exponentially small term.

**Recommendation:** use layer cake if the relevant Mathlib infrastructure is convenient; otherwise a dyadic proof is perfectly adequate and avoids exact Gamma evaluations.

**Mathlib inputs:** `MeasureTheory.lintegral_lintegral_swap`, measurable indicator/restriction lemmas, exponential integrability, `Real.rpow` identities, and elementary exponential-versus-power limits. Grep for `layercake`, `integral_exp`, and `exp_neg_mul`.

**Non-claims:** no leading coefficient, no asymptotic equivalence, no converse Tauberian theorem, no signed-observable result.

---

## Unit 2 — Stability under a locally positive weight, and the E5 adapter

First prove a generic weighting theorem. For example, define

```lean
def weightedMeasure (μ : Measure X) (w : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))
```

Then:

```lean
theorem HasSmallSublevelBounds.withDensity_of_local_bounds
    [IsFiniteMeasure μ]
    (hf : Measurable f)
    (hw : Measurable w)
    (hsub : HasSmallSublevelBounds μ f λ q)
    (hw_nonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hupper : ∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂μ, w x ≤ C)
    (hlower :
      ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
        ∀ᵐ x ∂μ.restrict {x | f x < δ}, c ≤ w x) :
    HasSmallSublevelBounds (weightedMeasure μ w) f λ q
```

Combine with Unit 1 and a `withDensity` integral identity to obtain bounds for
\[
\int w(x)e^{-Nf(x)}\,d\mu(x).
\]

Then write the **smallest possible adapter from E5** to `HasSmallSublevelBounds`.

I would not invent a precise `HasLLCExponentsOn` application before inspecting its definition. In particular, check:

- which restricted measure/neighbourhood its bounds concern;
- whether its logarithmic parameter is \(m\) or \(m-1\);
- whether it provides eventual bounds or explicit constants;
- whether \(\lambda>0\) is included or must be supplied;
- whether its phase is `|K|`.

For `K ≥ 0` on the relevant neighbourhood, the last conversion is straightforward.

**Important scope restriction:** the quoted `exists_monomialResolution_at` is a theorem about a compact neighbourhood of one point. It does not itself resolve an arbitrary global `LocalisationData`. A global population theorem still needs localisation around the whole relevant zero set and control of the complement.

**Headline suggestion:**

> Certified two-sided resolution data determine the population Laplace exponent pair.

This is stronger and more precise than announcing an exact resolution-to-expansion bridge.

---

## Unit 3 — Dominant pair for a finite positive family

Make the aggregation rule a reusable theorem rather than burying it in the resolution adapter.

Using the same eventual-bounds predicate for functions, prove:

```lean
theorem finite_sum_hasPowerLogBounds
    [Fintype ι] [Nonempty ι]
    (L : ι → ℝ → ℝ)
    (λ : ι → ℝ) (q : ι → ℕ)
    (hL : ∀ i, HasPowerLogBounds (L i) (λ i) (q i))
    (hλmin : ∀ i, λ₀ ≤ λ i)
    (hqmax : ∀ i, λ i = λ₀ → q i ≤ q₀)
    (hattain : ∃ i, λ i = λ₀ ∧ q i = q₀) :
    HasPowerLogBounds (fun N => ∑ i, L i N) λ₀ q₀
```

Here `HasPowerLogBounds` is the obvious function-level version of Unit 1’s conclusion.

This avoids unnecessary `Finset.min'` machinery in the public theorem. A separate finite-order lemma can construct `λ₀,q₀`.

**Inputs:** finite sums of eventual inequalities; positive powers dominate logarithms. Grep asymptotic lemmas involving `log`, `rpow`, and `isLittleO`.

**Traps:**

- Taking a sum of integrals over overlapping chart images is not the original integral.
- It can nevertheless give comparable bounds under controlled coverage and multiplicity.
- Positivity/noncancellation is essential.
- If E5 already supplies the global pair, consume it directly; do not independently reconstruct a possibly different chart minimum.

**Non-claim:** identification with grammar’s first nonzero canonical `gCoeff` pair.

**Recommended stop after this unit for the first PR/headline.**

---

## Unit 4 — Orthant reflection as a weighted measure identity

Prove the measure identity first. The phase and integral versions then become corollaries.

For signs `s : Fin d → ℝ` with `|s i| = 1`, define
\[
R_s(y)_i=s_i y_i,\quad
B_+=(0,b]^d,\quad
B_s=R_s(B_+).
\]

Target:

```lean
theorem map_weighted_posBox_reflection
    (hb : 0 < b)
    (hs : ∀ i, |s i| = 1) :
    ((volume.restrict (posBox b)).withDensity
      (fun y => ENNReal.ofReal (∏ i, y i ^ h i))).map (reflect s)
      =
    (volume.restrict (orthantBox s b)).withDensity
      (fun y => ENNReal.ofReal (∏ i, |y i| ^ h i))
```

Also prove:

```lean
theorem monomialEval_reflect_of_even
    (hs : ∀ i, |s i| = 1)
    (he : ∀ i, Even (e i)) :
    monomialEval (reflect s y) e = monomialEval y e
```

Definitions here can use ordinary functions `Fin d → ℕ`, with a separate `Finsupp` conversion.

**Inputs:** coordinate reflection as a linear isometry equivalence; invariance of Lebesgue measure; `Measure.map_apply`, `Measure.ext`, `lintegral_map`; coordinate hyperplanes are null.

**Trap:** an arbitrary box centred at the readout’s `b` is not a box centred at the normal-crossings origin. First separate coordinates where `b i = 0` from those where `b i ≠ 0`, shrink to keep the latter nonzero, and absorb their factors into units. The readout already reflects this distinction in its exponent formula.

**Non-claim:** any partition of overlapping target images.

---

## Unit 5 — Tangential/normal splitting of weighted boxes

Let
\[
S=\{i:e_i>0\},\qquad T=\{i:e_i=0\}.
\]

Use the coordinate equivalence
\[
\mathbb R^d \simeq \mathbb R^T\times\mathbb R^S
\]
to prove:

1. the monomial phase depends only on the \(S\)-coordinates;
2. the Jacobian monomial factors;
3. the corresponding weighted box measure becomes a product measure.

The main measure statement should have the shape

```lean
theorem map_weightedBox_split :
    (weightedBoxMeasure h b).map (splitCoords S)
      =
    (tangentialBoxMeasure h S b).prod
      (normalBoxMeasure h S b)
```

with the restrictions and densities included in those definitions.

For signed tangential coordinates, use
\[
d\nu(v)=
1_{[-b,b]^T}(v)\prod_{i\in T}|v_i|^{h_i}\,dv.
\]
This is finite. It is usually cleaner to put these fixed tangential monomial factors into `ν`, rather than require them in `c`.

**Inputs:** finite product-coordinate equivalences, product Lebesgue measure, `Measure.prod`, Tonelli/Fubini, finite products.

**Traps:**

- `ChartPresentation` requires `n + 1` normal variables. Prove `S.Nonempty` for a chart centred over a phase zero with a nonvanishing phase unit.
- Charts with no positive phase exponent belong to a different case, usually a region separated from phase zero.
- Shrinking and unit absorption must preserve positivity and bounds uniformly on the chosen compact product.

**Non-claim:** continuous amplitudes become Taylor-series amplitudes. This unit only rearranges geometry and measure.

---

## Unit 6 — Exact single-chart transport from `PartialResolution`

This is provable now and is valuable independently of the expansion bridge.

For a compact chart domain `B`, aim at:

```lean
theorem map_absDet_restrict_eq_restrict_image
    (hB : IsCompact B)
    (hU : IsOpen U)
    (hBU : B ⊆ U)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hE_closed : IsClosed E)
    (hEB : E ⊆ B)
    (hE_null : volume E = 0)
    (hinj : Set.InjOn φ (B \ E))
    (hdet :
      ∀ x ∈ B \ E, (fderiv ℝ φ x).det ≠ 0) :
    ((volume.restrict B).withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ φ x).det|)).map φ
      =
    volume.restrict (φ '' B)
```

The assumptions can later be weakened.

**Inputs:** the change-of-variables family containing
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`; the corresponding nonnegative-integral statements if available; measure extensionality.

**Critical proof obligation:** `volume E = 0` alone does not imply `volume (φ '' E) = 0` for an arbitrary map. Here smoothness on a neighbourhood provides local Lipschitzness, hence null-image preservation. Do not silently drop this step.

Compactness also helps establish measurability of the images. Handle the exceptional-set removal explicitly.

Then add a weighted version:

\[
\phi_*\!\left((r\circ\phi)|\det D\phi|\,dy\big|_B\right)
=
r\,dx\big|_{\phi(B)}
\]
for measurable nonnegative `r`.

**Non-claim:** summing these identities gives transport to the target measure. It gives transport to the target measure multiplied by chart multiplicity.

---

## Unit 7 — Measurable overlap correction, deliberately without analyticity

This supplies an honest answer to “what does finite multiplicity buy us?”

Let \(A_i=\phi_i(B_i)\), and define
\[
m(z)=\sum_i 1_{A_i}(z),\qquad
\rho_i(z)=
\begin{cases}
1_{A_i}(z)/m(z),&m(z)>0,\\
0,&m(z)=0.
\end{cases}
\]

Prove a generic measure lemma:

```lean
theorem finite_cover_normalized_indicators
    [Fintype ι]
    (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, A i) :
    (∀ i, Measurable (coverWeight A i)) ∧
    (∀ i x, 0 ≤ coverWeight A i x) ∧
    (∀ᵐ x ∂μ, ∑ i, coverWeight A i x = 1)
```

Combined with Unit 6:

\[
\sum_i
(\phi_i)_*
\left[
(\rho_i\circ\phi_i)|\det D\phi_i|\,
dy\big|_{B_i}
\right]
=\mu
\]
when \(\mu\) is the covered restricted volume measure.

This gives a measurable `FiniteSublevelPartition` when the target measure really is the required sublevel-restricted measure.

**Useful distinction:** for this finite-image construction, the number of images already bounds `m`. The stronger `PartialResolution.mult_bound` controls preimages and can be useful elsewhere, but is not needed merely to normalise a finite image cover.

**Trap:** if the original images are not contained in `D.sublevel`, restriction introduces
\[
1_{\{\mathrm{phase}<\delta\}}\circ\phi_i
\]
into the source density. That is another normal-variable cutoff.

**Non-claim:** `amplitude_eq`, `NormalMomentPresentation`, or `AdaptedStrataData`. These weights are generally not analytic in normal variables.

This theorem is still useful for inequalities and exact measurable integral decompositions.

---

## Unit 8 — A localisation obstruction lemma

I would spend the final unit making the exact-cutoff obstruction explicit, rather than attempting a misleading “almost adapter.”

A simple real-analytic uniqueness lemma suffices:

```lean
theorem analytic_eq_zero_of_ae_zero_on_terminal_interval
    (hb : 0 < b)
    (ht : t ∈ Set.Ioo (0 : ℝ) b)
    (hA : AnalyticOnNhd ℝ A (Set.Ioo (0 : ℝ) b))
    (hzero :
      ∀ᵐ x ∂volume.restrict (Set.Ioo t b), A x = 0) :
    Set.EqOn A (fun _ => 0) (Set.Ioo (0 : ℝ) b)
```

Proof: continuity upgrades a.e. vanishing on an open interval to pointwise vanishing; analytic uniqueness propagates it across the connected interval.

**Application:** take one normal coordinate, `obs = 1`, and exact phase
\[
\beta u^{2k}.
\]
If the box crosses the sublevel boundary,
\[
0<(\delta/\beta)^{1/(2k)}<b,
\]
the transport identity forces its nonnegative source density to vanish above that boundary. `amplitude_eq` and analyticity then force the amplitude to vanish throughout the connected normal interval.

The same obstruction applies to an open upper-corner region in several normal variables.

**Conclusion:** a nontrivial chart-exact analytic amplitude cannot simply absorb an arbitrary exact sublevel cutoff.

This is not a claim that `AdaptedStrataData` is unrealizable. It identifies a necessary geometric compatibility that the supplied resolution theorem does not establish.

**Inputs:** analytic identity/unique-continuation lemmas and continuous a.e.-equality lemmas; grep exact names before committing the interface.

---

# What to request from hironaka

## Minimal analytic enhancement

Request an additional theorem or witness structure, without changing frozen records:

```lean
structure AnalyticMonomialWitness
    (F : E → ℝ) (φ : E → E)
    (e h : Fin d →₀ ℕ) (W : Set E) where
  phaseUnit : E → ℝ
  jacUnit : E → ℝ
  phaseUnit_analytic : AnalyticOnNhd ℝ phaseUnit W
  jacUnit_analytic : AnalyticOnNhd ℝ jacUnit W
  phaseUnit_ne_zero : ∀ y ∈ W, phaseUnit y ≠ 0
  jacUnit_ne_zero : ∀ y ∈ W, jacUnit y ≠ 0
  phase_eq :
    ∀ y ∈ W, F (φ y) = phaseUnit y * monomialEval y e
  jac_eq :
    ∀ y ∈ W,
      (fderiv ℝ φ y).det = jacUnit y * monomialEval y h
```

Also request, on suitably shrunk neighbourhoods over a nonnegative phase:

- `MapsTo φ W U`, where `F` is analytic and nonnegative;
- evenness of the relevant phase exponents;
- positivity of `phaseUnit`;
- a centre over the phase zero, with at least one positive exponent whose coordinate vanishes there;
- preferably a connected neighbourhood, making the sign of `jacUnit` fixed.

`0 < phaseUnit` is locally derivable from even exponents, phase nonnegativity, continuity, and nonvanishing, but exporting it saves work. There is no need to demand a positive **signed** Jacobian unit: fixed sign lets its absolute value be analytic locally.

## What this does **not** buy

It does **not** make `expectation_expansion_of_adaptedStrataData` unconditional.

For that, someone must additionally supply a **compatible localisation theorem**:

- product domains after unit absorption;
- finite coverage of the relevant region;
- exact weighted transport;
- partition pullbacks analytic in normal variables;
- uniform normal analyticity radii and coefficient control;
- compatibility with the exact sublevel restriction.

A general smooth partition of unity does not satisfy the normal power-series requirement. A general analytic partition subordinate to arbitrary chart supports is unavailable.

The realistic alternatives are:

1. construct special tangent-only localisation from stronger geometry;
2. prove an **exact analytic-core decomposition modulo an exponentially small remainder**;
3. generalise grammar’s analytic-amplitude interface to smooth amplitudes with finite-order Taylor remainder estimates.

None is a consequence merely of adding `AnalyticOnNhd` fields.

For Hypothesis I, chart complexification is only one ingredient. Divisibility of the statistical function, joint complex neighbourhoods, and uniform product-polydisc bounds need their own hypotheses and proofs. Phase monomialisation alone does not export them.

---

# Dependency and trust recommendation

Use two layers:

1. **Grammar core:** resolution-independent sublevel/Laplace theorems and minimal transport/box interfaces.
2. **Integration adapter:** imports hironaka and constructs those interfaces from its actual declarations.

Do not transcribe 2400 files or duplicate the whole resolution API. Transcribe only the small consumer-facing structures needed by the new theorems. Later integration is a **fieldwise constructor/adapter**, not generally a `hironaka_type_eq` theorem.

Before claiming the Hironaka input is certified:

- finish a clean build at a pinned commit;
- inspect `#print axioms` for `Q_all`, the concrete readout endpoint, and the adapter endpoint;
- ensure no reachable `sorryAx` or extra assumption declarations enter through `Statements`;
- distinguish repository-wide syntactic cleanliness from the dependency closure of the theorem actually consumed.

Ordinary Lean foundational dependencies are a separate matter from introduced axioms or `sorryAx`.

I would isolate the `.0` → `.1` toolchain/Mathlib bump in its own branch or PR. A dependency with many files does not necessarily compile every file: the import closure and Lake targets determine that.

## Stop rule

**Ship Units 1–3 first.** Continue with Units 4–7 only as independent reusable lemmas. Unit 8 records the exact-bridge limitation. Then stop.

Do not claim an `AdaptedStrataData` constructor until both **analytic normalisation** and **compatible analytic localisation** are certified. The second is currently the larger conceptual gap.
