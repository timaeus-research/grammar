## Recommendation

Use **(a) a new scalar smooth coefficient functional, plus (b) compatibility with the analytic coefficient functional by uniqueness**.

The shortest route is:

1. uniformise the fixed-depth theorem;
2. integrate smooth amplitude families over a finite compact base;
3. handle tangential phase units by **rescaling the Laplace parameter**, not the coordinates;
4. assemble charts and a gapped tail with the existing `CutoffExpansion` API;
5. convert to the paper’s little‑\(o\) statement;
6. adapt the weighted-atlas producer.

Do **not** introduce smooth analogues of `TangentialData`, `toEta`, `fluct_zero`, or the Cauchy-product certificate. Those are representations specific to the analytic engine.

There are three important qualifications:

- the signed amplitude must not itself be used as a `withDensity` density;
- coefficient canonicity holds on the spectral lattice and within the degree bound, unless coefficients are explicitly zero-normalised elsewhere;
- changing \(\beta\) produces **log-degree mixing**, not just a factor \(\beta^{-\mu}\).

---

# 1. Brief review of U1–U3

The landed statements provide the right mathematical foundation.

### The depth condition is sufficient

The equality
\[
p_i+h_i=2k_iL
\]
makes the face integrability condition
\[
2k_iL<p_i+h_i+1
\]
automatic. Integer cutoffs above `L₀ h` provide positive natural depths. Arbitrary real cutoffs can then be obtained by truncating an expansion at a larger integer cutoff.

Thus the equality restriction in `smooth_expansion_at_depth` is not an obstacle.

### The degree bound is right

`d - 1` is the expected maximum logarithmic degree for `d ≥ 1`. For `d = 0`, natural subtraction gives degree zero, and the integral is a constant amplitude times `exp (-β * N)`. Its coefficient family should be identically zero. Keep this as an explicit regression test.

### The main missing strengthening

The statement

```lean
∀ s, ∃ K, ∀ N ≥ 1, ...
```

cannot be integrated uniformly merely because the parameter space is compact. You need either an explicit bound or a theorem whose existential constant precedes the amplitude quantifier.

That is the first remaining landing.

### Canonical coefficients

`cutoffOf` is a sound stabilisation device. However, prove and expose:

```lean
smoothCoeff_eq_zero_of_not_mem_lattice
smoothCoeff_eq_zero_of_degree_gt
smoothCoeff_eq_zero_of_neg
```

or introduce a masked coefficient interface. `CutoffExpansion` alone does not constrain values off its lattice or above its degree bound.

---

# 2. U4: uniform families and base integration

## 2.1 First strengthen the existing depth theorem

A useful strengthening is the following schematic statement. All casts in `hp` should be made explicit in the implementation.

```lean
theorem smooth_expansion_at_depth_uniform
    (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) (hL : 0 < L)
    (hp : ∀ i, (p i + h i : ℝ) = 2 * k i * L)
    (hp0 : ∀ i, 0 < p i)
    {M : ℝ} (hM0 : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : (Fin d → ℝ) → ℝ,
        ContDiff ℝ ∞ F →
        RectBound F p b M →
        ∀ N : ℝ, 1 ≤ N →
          |smoothIntegral F h k β b N -
              absSpectralSum (Qamb k) (d - 1)
                (smoothCoeffAtDepth F h k p β b) L N|
          ≤ C * (N ^ (-L) * (1 + log N) ^ (d - 1))
```

Here:

```lean
def RectBound (F : (Fin d → ℝ) → ℝ)
    (p : Fin d → ℕ) (b M : ℝ) : Prop :=
  ∀ m, (∀ i, m i ≤ p i) →
    ∀ v, (∀ i, v i ∈ Icc 0 b) →
      |pdMulti m (List.finRange d) F v| ≤ M
```

The constant may depend on `M`; it must not depend on `F`.

**Implementation:** refactor the existing proof so the face two-regime constants are chosen before `F`. The remaining dependence on `F` is through `M`. There is no need initially to expose a closed-form `C`.

A stronger linear estimate `Cgeom * M` is useful but not necessary for U6.

## 2.2 The smooth family structure

Separate the analytic payload from chart transport.

For the first implementation, use compact Euclidean subtypes as bases, or otherwise assume a compact metrizable space with its Borel measurable structure. This avoids distracting product-measurability generality.

```lean
def closedBox (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 b)

structure SmoothAmplitudeFamily
    (S : Type*) (d : ℕ) (b : ℝ) where
  amp : S → (Fin d → ℝ) → ℝ
  smooth : ∀ s, ContDiff ℝ ∞ (amp s)
  deriv_cont :
    ∀ m : Fin d → ℕ,
      ContinuousOn
        (fun z : S × (Fin d → ℝ) =>
          pdMulti m (List.finRange d) (amp z.1) z.2)
        (Set.univ ×ˢ closedBox d b)
```

A `CoeFun` instance is convenient.

This exactly supplies:

- a common rectangular derivative bound at every finite depth;
- joint continuity of face amplitudes on the closed face box;
- measurability and integrability of the chart integrands.

It does not require differentiating in `s`.

### Global versus local smoothness

Your landed theorem requires global `ContDiff`. A chart amplitude given only on a neighbourhood of the closed box does not meet that hypothesis verbatim.

For the shortest path, add a producer helper:

> A function smooth on an open neighbourhood of a compact box has a globally smooth extension agreeing with it on a neighbourhood of that box.

Prove it by multiplying by a smooth cutoff supported inside the smoothness neighbourhood and extending by zero. Add a parameterised version only if needed; atlas amplitudes smooth jointly in all original chart variables can usually be extended **before** splitting variables into base and active coordinates.

Alternatively, a future version of the engine can use smoothness on a neighbourhood of the closed box. Do not block U4 on that refactor.

## 2.3 Uniform compact bounds

Prove:

```lean
theorem SmoothAmplitudeFamily.exists_uniform_rect_bound
    [CompactSpace S]
    (F : SmoothAmplitudeFamily S d b)
    (p : Fin d → ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, RectBound (F s) p b M
```

The index set `{m | ∀ i, m i ≤ p i}` is finite. Each derivative is continuous on the compact set `univ ×ˢ closedBox d b`.

Then prove the uniform canonical-coefficient version:

```lean
theorem SmoothAmplitudeFamily.uniform_cutoff
    [CompactSpace S]
    (F : SmoothAmplitudeFamily S d b)
    (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s N, 1 ≤ N →
        |smoothIntegral (F s) h k β b N -
            absSpectralSum (Qamb k) (d - 1)
              (smoothCoeff (F s) h k β b) L N|
        ≤ C * (N ^ (-L) * (1 + log N) ^ (d - 1))
```

For arbitrary real `L`:

1. choose a common integer cutoff above `L` and `L₀ h`;
2. apply the uniform depth theorem;
3. replace depth coefficients by canonical coefficients;
4. bound the finitely many removed terms uniformly in `s`.

Step 4 can use the coefficient continuity theorem below. Proving integer-cutoff uniformity first avoids circularity.

## 2.4 Coefficient continuity: choose a deeper representative

The key public theorem is:

```lean
theorem SmoothAmplitudeFamily.continuous_smoothCoeff
    [CompactSpace S]
    (F : SmoothAmplitudeFamily S d b)
    (hk : ∀ i, 0 < k i) (hβ : 0 < β) (hb : 0 < b)
    (μ : ℝ) (q : ℕ) :
    Continuous
      (fun s => smoothCoeff (F s) h k β b μ q)
```

A robust proof does not need to use the literal `cutoffOf h μ` expression throughout.

For a supported `μ`:

1. choose an admissible integer cutoff strictly above `μ`;
2. replace `smoothCoeff` by `smoothCoeffAtDepth` at that cutoff;
3. expand the finite face sum;
4. show joint continuity of each `faceAmp`;
5. dominate each face integral by the uniform rectangular bound times a power–log weight.

The strict margin
\[
p_i+h_i-2k_i\mu>-1
\]
provides integrability. Terms outside the lattice or degree range are handled by zero-support lemmas.

Useful subordinate lemmas:

```lean
continuousOn_faceAmp_family
integrable_faceCoeff_majorant
continuous_parameter_faceCoeffInt
```

You do not need an abstract theory of parameterised improper integrals: Mathlib’s dominated-continuity theorem, expressed by an integrable pointwise norm majorant, is sufficient.

## 2.5 Integrate once, then expose `CutoffExpansion`

Define:

```lean
noncomputable def familyIntegral
    (ν : Measure S) (F : SmoothAmplitudeFamily S d b)
    (h k : Fin d → ℕ) (β b N : ℝ) : ℝ :=
  ∫ s, smoothIntegral (F s) h k β b N ∂ν

noncomputable def familyCoeff
    (ν : Measure S) (F : SmoothAmplitudeFamily S d b)
    (h k : Fin d → ℕ) (β b μ : ℝ) (q : ℕ) : ℝ :=
  ∫ s, smoothCoeff (F s) h k β b μ q ∂ν
```

Assume `[IsFiniteMeasure ν]`.

First prove a generic integration lemma:

```lean
theorem cutoffExpansion_integral_of_uniform_bound
    -- integrability of Z s N and c s μ q
    -- ∀ L > 0, ∃ C ≥ 0, ∀ s, ∀ N ≥ 1, uniform cutoff estimate
    :
    CutoffExpansion Q D
      (fun N => ∫ s, Z s N ∂ν)
      (fun μ q => ∫ s, c s μ q ∂ν)
```

Its proof is finite-sum/integral interchange plus
\[
\left|\int E_s\,d\nu\right|
\le \int |E_s|\,d\nu
\le C\,(\nu(\mathrm{univ})).\mathrm{toReal}\,R(N).
\]

Then:

```lean
theorem SmoothAmplitudeFamily.cutoffExpansion_integral
    ...
    : CutoffExpansion (Qamb k) (d - 1)
        (familyIntegral ν F h k β b)
        (familyCoeff ν F h k β b)
```

That is the promised “one-liner” used by chart presentations.

---

# 3. Q2: tangential phase units — rescale time

Yes: make `β : S → ℝ` continuous and positive. On a compact base this gives both a positive lower bound and a finite upper bound.

But I recommend **not** first proving uniformity of the analytic box engine’s `cutoffBound` in `β`.

Use the exact identity
\[
\operatorname{smoothIntegral}(F,h,k,\beta,b,N)
=
\operatorname{smoothIntegral}(F,h,k,1,b,\beta N).
\]

## 3.1 The coefficient rescaling operator

Define:

```lean
noncomputable def scaleCoeff
    (D : ℕ) (β : ℝ) (c : ℝ → ℕ → ℝ)
    (μ : ℝ) (q : ℕ) : ℝ :=
  β ^ (-μ) *
    ∑ j ∈ Finset.Ico q (D + 1),
      c μ j * (j.choose q) * Real.log β ^ (j - q)
```

This comes from
\[
(\beta N)^{-\mu}\log(\beta N)^j
=
N^{-\mu}\beta^{-\mu}
\sum_{q=0}^j {j\choose q}(\log N)^q(\log\beta)^{j-q}.
\]

Prove:

```lean
absSpectralSum_mul_pos
CutoffExpansion.comp_mul_pos
smoothIntegral_beta_eq
```

and, by uniqueness on the supported indices:

```lean
theorem smoothCoeff_beta_eq_scaleCoeff
    (hF : ContDiff ℝ ∞ F)
    (hk : ∀ i, 0 < k i)
    (hβ : 0 < β) (hb : 0 < b) :
    smoothCoeff F h k β b μ q =
      scaleCoeff (d - 1) β
        (smoothCoeff F h k 1 b) μ q
```

For an all-`μ,q` statement, use the zero-support lemmas on both sides.

## 3.2 Uniform parameter rescaling

Assume
\[
0<\beta_0\le\beta(s)\le\beta_1.
\]
Apply the fixed-`β = 1` uniform theorem at `β s * N`, for
\[
N\ge \max(1,\beta_0^{-1}).
\]

Then bound:

- `β s ^ (-L)` uniformly;
- `|log (β s)|` uniformly;
- `1 + log (β s * N)` by a constant times `1 + log N`.

This gives the variable-unit family theorem without revisiting the face engine:

```lean
theorem SmoothAmplitudeFamily.cutoffExpansion_integral_variable_beta
    (hβ : Continuous β)
    (hβpos : ∀ s, 0 < β s)
    ...
    : CutoffExpansion (Qamb k) (d - 1)
        (fun N => ∫ s,
          smoothIntegral (F s) h k (β s) b N ∂ν)
        (fun μ q => ∫ s,
          smoothCoeff (F s) h k (β s) b μ q ∂ν)
```

Coefficient continuity follows from fixed-unit continuity and `scaleCoeff`.

**Recommendation:** retain the monomial unit as `β(s)` whenever it is tangential. Coordinate rescaling would introduce parameter-dependent boxes and extra geometric bookkeeping for no asymptotic benefit.

If a unit depends on active coordinates, this argument does not absorb it. In that case reuse unit removal or provide a separate normalisation theorem.

---

# 4. Q1: the actual `SmoothCorePresentation`

Use two layers.

## 4.1 Analytic payload

```lean
structure SmoothCoreData
    (S : Type*) (d : ℕ) where
  ν : Measure S
  finite_ν : IsFiniteMeasure ν
  b : ℝ
  b_pos : 0 < b
  h k : Fin d → ℕ
  k_pos : ∀ i, 0 < k i
  β : S → ℝ
  β_cont : Continuous β
  β_pos : ∀ s, 0 < β s
  amplitude : SmoothAmplitudeFamily S d b
```

Define its `Z` and `coeff` by the variable-`β` base integrals. Its expansion theorem is the family theorem above.

For `d = 0`, either permit this structure and prove its coefficient family is zero, or route such pieces directly to a gapped-tail constructor.

## 4.2 Geometry and transport

Do not call the whole signed amplitude a measure density. With insertions, it can change sign.

A geometric presentation should retain a separate nonnegative transport density:

```lean
structure SmoothCorePresentation
    (D : LaplaceData U) (target : Measure U)
    (S : Type*) (d : ℕ)
    extends SmoothCoreData S d where
  Φ : S × (Fin d → ℝ) → U
  Φ_measurable : Measurable Φ

  ρ : S × (Fin d → ℝ) → ℝ
  ρ_measurable : Measurable ρ
  ρ_nonneg : ∀ᵐ z ∂chartMeasure ν d b, 0 ≤ ρ z

  amplitude_eq :
    ∀ᵐ z ∂chartMeasure ν d b,
      amplitude z.1 z.2 = ρ z * D.obs (Φ z)

  phase_normal :
    ∀ᵐ z ∂chartMeasure ν d b,
      D.phase (Φ z) =
        β z.1 * mono (fun i => 2 * k i) z.2

  transport :
    ((chartMeasure ν d b).withDensity
      (fun z => ENNReal.ofReal (mono h z.2 * ρ z))).map Φ
        = target
```

Adapt the density expression to the repository’s `chartDensity` convention.

Then prove:

```lean
theorem SmoothCorePresentation.integral_eq
    (hN : 1 ≤ N) :
    (∫ u, D.obs u * Real.exp (-N * D.phase u) ∂target) =
      toSmoothCoreData.Z N
```

Use map/with-density integration and Fubini. Integrability follows on the source from compact bounded amplitude and bounded monomial weights.

**Important distinction:** the old analytic `amplitude_eq` involving `evalF (toEta ...)` disappears. A simple equality relating the smooth amplitude to transport density times observable remains necessary if transport is the chosen interface. `fluct_zero` and `x : TangentialData` disappear completely.

An even smaller algebraic interface can carry `integral_eq` directly and leave `Φ`, phase and transport in a producer-side certificate.

---

# 5. U5: finite assembly and tails

Define:

```lean
structure SmoothCoreDecomposition (D : LaplaceData U) where
  Chart : Type*
  chart_fintype : Fintype Chart
  Base : Chart → Type*
  dim : Chart → ℕ
  core : Chart → Measure U
  tail : Measure U
  measure_eq : D.μ = (∑ i, core i) + tail
  chart : ∀ i,
    SmoothCorePresentation D (core i) (Base i) (dim i)

  tail_integrable : Integrable D.obs tail
  δ : ℝ
  δ_pos : 0 < δ
  gap : ∀ᵐ u ∂tail, δ ≤ D.phase u
```

Supply base compactness/Borel instances in the usual repository style.

For the tail,
\[
|Z_{\mathrm{tail}}(N)|
\le \left(\int |\mathrm{obs}|\,d\mathrm{tail}\right)e^{-\delta N}.
\]

Thus:

```lean
tail_cutoffExpansion_zero
```

for every positive denominator and every log degree.

Define `commonQ` as any positive common multiple of the chart denominators and `commonD` as the maximum chart degree. Reuse `.refine`, `.pad`, `.sum`, and `.add`.

Define global coefficients using the **same refinement and padding convention** as those combinators. They can be written as a raw sum of chart coefficients once the chart zero-support lemmas are established.

The public theorem is:

```lean
theorem SmoothCoreDecomposition.cutoffExpansion
    (A : SmoothCoreDecomposition D) :
    CutoffExpansion A.commonQ A.commonD D.Z A.coeff
```

This should contain no Taylor or face-integral proof.

---

# 6. U6: what “coordinate-free” should mean

## 6.1 Headline: intrinsic scalar coefficients

Do not initially claim that the smooth theorem produces the old moment coefficient field `B`. Uniqueness gives intrinsic **scalar coefficients**, not automatically an intrinsic field representing them.

Use:

```lean
structure SmoothExpansionCertificate (Z : ℝ → ℝ) where
  Q : ℕ
  Q_pos : 0 < Q
  D : ℕ
  coeff : ℝ → ℕ → ℝ
  coeff_support :
    ∀ μ q, coeff μ q ≠ 0 →
      (∃ m : ℕ, μ = (m : ℝ) / Q) ∧ q ≤ D
  expansion : CutoffExpansion Q D Z coeff
```

Then:

```lean
theorem SmoothCoreDecomposition.toExpansionCertificate :
  SmoothExpansionCertificate D.Z
```

For two decompositions, refine both certificates to a common denominator and pad to a common degree, then apply uniqueness:

```lean
theorem smoothCoeff_independent_of_presentation
    (A B : SmoothCoreDecomposition D) :
    ∀ μ q, A.coeff μ q = B.coeff μ q
```

The all-index statement uses normalised support and positivity of the denominators. Without that normalisation, state equality only on the common lattice and within the common degree range.

## 6.2 Exact shape of the little‑\(o\) theorem

A minimal new predicate is:

```lean
def HasSmoothCoordFreeExpansion
    (Z : ℝ → ℝ)
    (c : ℝ → ℕ → ℝ)
    (Q D : ℕ) : Prop :=
  ∀ A : ℝ,
    (fun N =>
      Z N -
        ∑ q ∈ spectrumLe Q D A,
          c q.exponent q.logDegree * q.scale N)
      =o[atTop] (fun N => N ^ (-A))
```

Use the actual repository spectral term type and its accessors. Here `spectrumLe` must include all terms with exponent **at most** `A`.

Prove the generic conversion:

```lean
theorem CutoffExpansion.hasSmoothCoordFreeExpansion
    (hQ : 0 < Q)
    (hc : CutoffExpansion Q D Z c) :
    HasSmoothCoordFreeExpansion Z c Q D
```

Proof: expand at a cutoff `L > max A 0`. Terms of exponent greater than `A`, as well as the remainder, are little‑\(o(N^{-A})\). Keeping terms at exponent exactly `A` is essential.

The requested final theorem can then have the shape:

```lean
theorem hasSmoothCoordFreeExpansion
    (A : SmoothCoreDecomposition D) :
    HasSmoothCoordFreeExpansion
      D.Z A.coeff A.commonQ A.commonD
```

For the paper-facing function:

```lean
theorem hasSmoothCoordFreeExpansion_of_weightedDomainAtlas
    (atlas : WeightedDomainAtlas ...)
    (inputs : SmoothSheetInputs atlas prior obs) :
    ∃ C : SmoothExpansionCertificate
        (fun N => globalLaplace W K (prior * obs) N),
      HasSmoothCoordFreeExpansion
        (fun N => globalLaplace W K (prior * obs) N)
        C.coeff C.Q C.D
```

An equivalent output is the assembled decomposition together with this conclusion.

## 6.3 Analytic compatibility

Prove compatibility at the easiest available level first:

```lean
theorem smoothCoeff_eq_analyticCoeff
    -- both expansions describe exactly the same Z
    -- denominators refined and degrees padded
    :
    smoothScalarCoeff μ q = analyticScalarCoeff μ q
```

This is an application of `CutoffExpansion.coeff_unique`, not a comparison of face remainders with infinite jets.

Then derive:

```lean
smoothExpansionCoefficient_eq_expansionCoefficient
```

under the existing `ResolvedCertificate` and `CoefficientCertificate`.

This makes the smooth theorem a generalisation of the scalar asymptotic theorem. It does **not** assert a smooth infinite-jet representation.

Option (c), “jet functional plus remainder functional”, should not be on the critical path. It requires choices and gives no additional existence result.

If the paper-facing API should emphasise insertions, add later:

```lean
smoothExpansionCoefficient_add
smoothExpansionCoefficient_smul
```

Linearity follows either directly from `smoothCoeffAtDepth` or from uniqueness and linearity of the integral. A formal continuous-linear-functional interface would additionally require choosing a topology and proving seminorm bounds.

---

# 7. Q4: weighted-atlas closure

For a rectangular atlas with tangential units, the smooth route can be substantially shorter than the analytic producer.

## Step 1: isolate genuine smooth hypotheses

Replace the holomorphic packet and stratum-adaptation hypotheses by smoothness on neighbourhoods of the closed chart boxes.

Schematic input:

```lean
structure SmoothSheetInputs (atlas : WeightedDomainAtlas ...) where
  weight_nonneg : ...
  weight_smooth : ...
  prior_pullback_smooth : ...
  obs_pullback_smooth : ...
  jacUnit_smooth : ...
  jacUnit_ne_zero : ...
  phaseUnit_cont : ...
  phaseUnit_pos : ...
  phaseUnit_tangential : ...
```

Do not require smoothness of `|jac_i|` as an unfactored expression. Factor
\[
|\operatorname{jac}_i(y)|=|j_i(y)|\prod_r |y_r|^{h_r},
\]
put the monomial part into `h`, and use smoothness of `|j_i|` from nonvanishing of the unit.

Analytic prior and observable are sufficient but no longer necessary.

## Step 2: extend amplitudes if needed

Construct globally smooth representatives agreeing with
\[
\omega_i(y)|j_i(y)|\,\mathrm{prior}(\phi_i y)\,
\mathrm{obs}(\phi_i y)
\]
near the closed integration box.

Agreement on a neighbourhood, rather than only pointwise on the box, is convenient for all face derivative identities.

## Step 3: split active and tangential coordinates

Let
\[
A_i=\{r:k_{i,r}>0\}.
\]

Only active coordinates belong to `Fin d` in `SmoothCoreData`, because the engine assumes positive `k`.

The remaining coordinates form the compact base. Tangential monomial Jacobian factors may be placed in the base measure, leaving a smooth active amplitude.

Prove a reusable coordinate-permutation/gluing integral identity, using the existing `Sheet.*` reindexing lemmas.

## Step 4: split active orthants

Reflect active coordinates to positive ones:

```lean
Fσ s v := F (glueTangentialActive s (refl σ v))
```

Then:

- active `k` and `h` remain unchanged;
- absolute Jacobian monomials become `mono h v`;
- the smooth amplitude retains the reflected weight;
- the tangential unit remains `β s`.

Coordinate hyperplanes are null for the source Lebesgue measure; hence replacing positive/negative closed pieces by `Ioc 0 b` creates no extra chart contribution.

Reflection of tangential coordinates is optional. Reusing an existing full-orthant decomposition is also valid.

## Step 5: build smooth amplitude families

Joint smoothness before splitting implies the required joint continuity of all active derivatives. No coordinate-independence of the weight is used.

This is the decisive replacement for `ω_indep`.

## Step 6: transport

Reuse the weighted-atlas measure identity and its orthant/reindexing consequences. Define core measures as the pushforwards of nonnegative weight × prior × Jacobian densities, with the observable kept outside the density.

If signed priors are intended, use a nonnegative geometric transport measure and put the prior into the amplitude; do not encode a signed prior through `ENNReal.ofReal`.

## Step 7: no-active-coordinate charts

A positive tangential unit on a compact base has a positive minimum. A chart with no active variables is therefore gapped. Send it to the tail or use the `d = 0` smooth theorem.

## Step 8: assemble

Apply `SmoothCoreDecomposition.cutoffExpansion`, then the little‑\(o\) conversion.

### What survives?

| Existing component | Smooth route |
|---|---|
| Weighted change-of-variables identity | Reuse |
| Orthant reflections and null-boundary lemmas | Reuse |
| Active/tangential reindexing | Reuse |
| Jacobian monomial factorisation | Reuse |
| Finite/sigma assembly of measures | Reuse |
| Gapped-tail estimates | Reuse |
| Compactness and finite-base-measure proofs | Reuse |
| `ChartCollar`, water-level geometry | Reuse if already needed geometrically; otherwise bypass |
| `MonomialUnitRemoval` / `StripNormalisation` | Unnecessary for tangential units; retain for genuinely active-dependent units |
| Analytic `pieceDatum`, `toEta`, holomorphic packets | Replace by `SmoothAmplitudeFamily` construction |
| Analytic coefficient/Cauchy-product assembly | Replace by integrated `smoothCoeff` |
| `ω_indep` | Delete |
| Separate `ω_contOn` | Delete as an assumption; its continuity consequence follows from smoothness |

One caution: if an existing collar changes the integration region to a sublevel domain, do not turn its characteristic function into a smooth amplitude. Either retain its valid normalised-box presentation or integrate the original rectangular atlas box directly. The latter is preferable when the tangential-unit hypothesis holds on that whole box.

---

# 8. Next ten landings

| Landing | Module-sized goal | Exit test |
|---|---|---|
| **1 — U4a** | Uniform fixed-depth theorem, with constant preceding `F` | Two amplitudes sharing one rectangular bound share one remainder constant |
| **2 — U4b** | `SmoothAmplitudeFamily`; compact derivative bounds; continuity of face coefficient integrals | Constant and polynomial parameter families |
| **3 — U4c** | Canonical coefficient continuity/support; uniform arbitrary cutoff | Family containing a nonanalytic smooth bump |
| **4 — U4d** | Generic integration lemma and fixed-unit family expansion | Finite discrete base agrees with `.sum`; singleton base recovers U3 |
| **5 — U4e** | Time rescaling, `scaleCoeff`, variable tangential unit | Nonconstant positive `β(s)`; explicit log-degree mixing in dimension two |
| **6 — U5a** | `SmoothCoreData`/`SmoothCorePresentation`, transport-to-integral theorem | One reflected weighted box |
| **7 — U5b** | Smooth decomposition, tails, denominator refinement and padding | Two charts with different denominators, plus a gapped tail |
| **8 — U6a** | Scalar certificate, presentation independence, little‑\(o\) conversion, analytic compatibility | Analytic monomial amplitude agrees with old coefficients |
| **9 — U6b** | Smooth weighted-atlas producer using reused `Sheet.*` geometry | Arbitrary active-dependent smooth weight accepted |
| **10 — U6c** | End-to-end regression module | Overlapping shifted boxes with a genuinely smooth active-dependent ramp |

If landing 9 becomes too large, move the local smooth-extension and orthant-family helper into landing 6 and keep the transport wrapper small.

## Recommended definitive regression

Use **the overlapping shifted boxes with a smooth ramp** first.

Require the example to establish explicitly that:

1. the weights are smooth and subordinate;
2. the weighted change-of-variables identity holds;
3. at least one weight depends nontrivially on an active coordinate, so the old `ω_indep` condition fails;
4. the new producer yields `HasSmoothCoordFreeExpansion`;
5. changing the ramp leaves the scalar coefficients unchanged, by presentation independence.

That tests both closure of the producer gap and the intended meaning of “coordinate-free”.

The cube blow-up is an excellent second test. For a radial weight, prefer
\[
\omega(x)=\chi(\|x\|^2)
\]
rather than `ρ (‖x‖)` unless smoothness at the origin is separately ensured.

---

## Bottom line

The remaining engine work is **uniformity, parameter continuity, and integration**—not another asymptotic argument. Tangential units can be handled entirely by time rescaling. The weighted-atlas producer should feed arbitrary smooth reflected amplitudes directly into this family engine.

The minimal theorem that closes the paper’s expansion gap is:

> Every admissible smooth weighted atlas yields a lattice power–log expansion with intrinsic scalar coefficients; whenever the analytic jet certificate also applies, these scalar coefficients equal its `expansionCoefficient`.

That is precisely (a)+(b), and it avoids both the stratum-adapted-weight restriction and an unjustified smooth infinite-jet representation.
