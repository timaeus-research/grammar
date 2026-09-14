## 1. Audit of Target A

**Verdict:** the displayed interfaces and the bridge argument are mathematically coherent. Target A proves the intended **smooth, compactly supported, interior-domain case**, subject to the nontrivial-phase normalisation inherited from the resolution theorem. The deviations listed in §2 are harmless.

This is an interface-level audit, not an independent check of the cited commits.

### What the landed result really provides

You now have three distinct layers, with a good separation of responsibilities:

1. **Resolution-to-transport:** finitely many smooth weighted monomial charts, plus a positive-gap residual measure.
2. **Transport-to-expansion:** an asymptotic expansion for the original integral, not merely for a chartwise surrogate.
3. **Uniqueness:** independence of the coefficients from the chosen transport presentation.

In particular, the residual is not an informal “contribution away from the singularity”: it is an actual measure in an exact measure identity, with an a.e. positive phase gap. That is the right strength.

The important qualifications are:

- This is not yet the compact semianalytic-domain theorem.
- The final analytic existence theorem currently excludes positive phases without a zero at the chosen origin, and identically zero phases.
- The displayed existential conclusion hides the already-proved logarithmic-degree bound.
- Unless separately proved, this does not assert that some coefficient is nonzero, identify the leading coefficient, or identify the leading exponent with an independently defined RLCT.

### The bridge proof

The described proof has the right ingredients:

- properness gives compactness of the lifted supported zero fibre;
- chart cutoffs sum to one on a neighbourhood of that fibre;
- injectivity away from the phase zero set gives the target-weight sum estimates;
- images of active walls account for the supported phase-zero set and show it is null;
- the complement of the cutoff neighbourhood inside the lifted support is compact and has strictly positive phase.

Two details are worth preserving explicitly in the implementation documentation:

1. **Target-zero-set nullity uses coverage and surjectivity**, not merely nullity of walls in individual charts.
2. If the compact complement is empty, choose an arbitrary positive gap. No minimum-on-a-nonempty-set argument should leak into the public assumptions.

Nothing in your summary suggests either is missing.

### The six deviations

| Deviation | Assessment |
|---|---|
| Per-chart radii | Better than unnecessary rescaling. Finiteness is enough for the consumer. |
| A.e. gap in `assemble` | Exactly right. Pointwise gap would be needlessly strong. |
| Phase unit already normalised to `1` | Harmless, provided this is the actual whole-target resolution export, as displayed. Document that the unit-normalisation obligation was discharged upstream, rather than omitted. |
| Cutoffs without `IsManifold` | Good assumption minimisation. You use only the transition regularity supplied by maximal-atlas membership. |
| Zero totalisations | Harmless because the analytic, Jacobian, and smoothness assertions are confined to the open target containing the source box. |
| Explicit `Measurable K` | Harmless but removable from the public analytic theorem. It should remain in the generic transport consumer. |

One useful explanatory sentence: **the smooth weights are on the source; the target weights need only be measurable.** No smoothness claim about `targetWeight` is needed or expected.

---

## 2. Removing normalisations and measurability

### 2.1 Remove global measurability without changing the user’s integral

Do not expose a modified phase in the final theorem. Use it internally.

Given an open set `U` and `ContinuousOn K U`, define
```lean
Kₘ := U.indicator K
```
and prove:

```lean
Measurable Kₘ
EqOn Kₘ K U
```

The measurable statement follows from measurability of the restriction and measurability of `U`; it does **not** follow from global measurability of `K`.

Then establish the elementary locality lemma:
```lean
(∀ y, prior y ≠ 0 → K₁ y = K₂ y) →
  (fun N => ∫ y, prior y * obs y * Real.exp (-N * K₁ y))
    =
  (fun N => ∫ y, prior y * obs y * Real.exp (-N * K₂ y))
```
by pointwise equality of the integrands. This needs no preliminary integrability argument.

Apply the existing theorem to `Kₘ` and rewrite the resulting integral back to the original `K`. Since `U` is open, equality on `U` also preserves the required local analyticity and germ hypotheses there.

**Recommendation:** keep `Measurable K` in `BridgeInputs` and the generic consumer; remove it from the public analytic corollary through this localisation wrapper.

### 2.2 The origin assumption is a presentation restriction

For a connected open analytic region, there are three cases.

#### Nontrivial phase with a zero

Choose any zero `p ∈ W`, translate `p` to the origin, and use the existing theorem. Analytic identity on connected open sets supplies nonzero germ at `p` from nontriviality on `W`.

This requires a translation wrapper, not new resolution mathematics.

#### Strictly positive phase

On the compact support of the prior, continuity gives a positive minimum, unless that support is empty. Use:
```lean
ι := Empty
tail := volume.withDensity (fun y => ofReal (prior y))
```
with the positive gap.

All asymptotic coefficients are zero. Thus you do not lose this case in the transport abstraction; only the current analytic existence entry point omits it. Landing `ofEmptyCores` closes this gap.

More generally, this shortcut applies whenever the phase is positive on the supported region, even if it has zeros elsewhere.

#### Identically zero phase

Here
\[
Z(N)=\int \mathrm{prior}(y)\,\mathrm{obs}(y)\,dy
\]
is constant.

This is **not** representable by the current active-core/positive-gap transport unless the prior measure is zero: active monomial cores have positive phase a.e., and the tail has positive phase a.e.

Whether the constant integral fits `HasSmoothCoordFreeExpansion` depends on its definition:

- if exponent `0` is permitted, add a constant certificate;
- if it describes only decaying expansions, state a separate constant case, or formulate the general conclusion for `Z - C`.

Do not claim that `ofEmptyCores` handles the identically zero case.

### 2.3 Clean final form

For the current decaying-expansion engine, the clean analytic theorem is schematically:

```lean
theorem exists_smoothExpansionCertificate_of_analyticOnNhd
    (hW : IsOpen W)
    (hWconn : IsConnected W)
    (hK : AnalyticOnNhd ℝ K W)
    (hK0 : ∀ x ∈ W, 0 ≤ K x)
    (hKnt : ∃ x ∈ W, K x ≠ 0)
    (hprior : ContDiff ℝ ∞ prior)
    (hp0 : ∀ x, 0 ≤ prior x)
    (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ W)
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ C : SmoothExpansionCertificate
        (fun N => ∫ y, prior y * obs y * Real.exp (-N * K y)),
      C.logDegree ≤ d - 1
```

Field names are schematic. Include positive denominator data if it is not already part of the certificate.

This removes:

- the distinguished origin;
- the requirement that a zero exist;
- global measurability of the original phase;
- the redundant outer analytic set, if you formulate analyticity directly on `W`.

Keep the current anchored theorem as the low-level wrapper. Add the constant-phase alternative separately.

---

## 3. Coefficient canonicity and public packaging

**Yes: make a certificate-producing theorem the principal public theorem**, while retaining the existential `c Q D` theorem as a convenience corollary.

In Lean, this can still be a proposition:
```lean
Nonempty (SmoothExpansionCertificate Z)
```
or an existential certificate carrying the dimension bound. There is no need to expose a globally chosen transport or make a noncanonical computational construction appear canonical.

The useful distinction is:

- **canonical:** coefficients, after your certificate’s normalisation conventions;
- **not canonical:** chart family, radii, denominator chosen as a common multiple, and an upper bound for log degree.

`SmoothExpansionCertificate.coeff_eq` should be the normal downstream uniqueness theorem. The transport-specific equality remains useful as an intermediate API.

I would expose now:

1. certificate existence;
2. coefficient uniqueness;
3. `logDegree ≤ d - 1`;
4. positivity of the lattice denominator and coefficient vanishing off that lattice;
5. the all-zero coefficient certificate in the positive-gap case.

### Do not advertise the proposed raw product as the canonical lattice

The expression
\[
Q=\prod_i 2\prod_j k_{ij}
\]
is problematic as written: inactive coordinates may have `kᵢⱼ = 0`.

The natural denominators come from the **positive phase exponents**. For the even charts, a positive common multiple of all `2 * k i j` with `k i j > 0` is suitable; an lcm is cleaner mathematically, a product of positive factors may be easier computationally. For an empty active family, use `Q = 1`.

Unless the exact formula matters downstream, expose existence and divisibility properties, not the implementation’s product.

---

## 4. Target B: two issues to settle before designing the export

There are two separate resolution questions:

1. simultaneous monomialisation of the phase and boundary functions;
2. parity of the phase when nonnegativity holds only on the domain.

The second is essential.

### 4.1 Domain nonnegativity does not give an even ambient phase

For example:
\[
W_{\rm dom}=[0,1],\qquad K(x)=x.
\]
The phase is nonnegative on the domain but has odd order at its boundary zero.

Therefore:

> If Target B assumes only `K ≥ 0` on `W_dom`, an export with an even phase on an entire open chart target is generally impossible for an unramified resolution map.

If the paper’s hypotheses give `K ≥ 0` on an ambient neighbourhood, your current even phase interface remains appropriate. Otherwise Target B needs either:

- arbitrary natural phase exponents on selected orthants, with sectorwise positivity; or
- a later orthantwise power substitution converting them to even exponents.

Do not silently strengthen the paper’s domain nonnegativity to ambient nonnegativity.

### 4.2 The correct product-factorisation statement

Your warning about real zero sets is correct. The condition
\[
Z(f)\subseteq \bigcup_j Z(x_j)
\]
does not imply that `f` is a unit times a monomial. At the origin, `x² + y²` is a counterexample.

The correct hypothesis is **analytic divisibility**, not real zero-set containment.

In the local ring of real-analytic germs at the chart centre, if
\[
f_0f_1\cdots f_r
   =u\,x_1^{a_1}\cdots x_d^{a_d},
\qquad u\text{ a unit},
\]
then each factor has the form
\[
f_\ell=u_\ell\,x_1^{a_{\ell1}}\cdots x_d^{a_{\ell d}},
\]
where `uℓ` is a unit and the exponents sum to the product exponents.

One proof uses the factoriality of the convergent real power-series local ring. A more targeted formal proof can avoid a general UFD development:

- coordinate germs are prime, using restriction to a coordinate hyperplane;
- vanishing on that hyperplane gives analytic divisibility by its coordinate;
- distribute the coordinate factors inductively;
- when the remaining product is a unit, each remaining factor is a unit.

After shrinking the chart neighbourhood, these germ factorizations become analytic equalities with nowhere-zero units. Shrink to a connected neighbourhood to make each real unit’s sign constant.

Thus **resolving the product can suffice mathematically**, provided the product is not identically zero and you export actual product monomialisation. It does not suffice merely to know that the real zero set has normal crossings.

Two qualifications:

- Remove identically zero boundary functions from non-strict inequalities: `0 ≥ 0` is redundant.
- Monomialising the ideal generated by the family is not automatically simultaneous monomialisation of every member. Ask for individual factorizations explicitly.

Using the square of the product can supply a nonnegative resolution input, but still requires the factor-divisor theorem and does **not** force the individual phase to have even exponents.

---

## 5. The exact hironaka export to request

I recommend an explicit simultaneous-modification interface rather than making grammar consume `AnalyticQChartPacket` directly.

Let `U` be an open ambient neighbourhood, and let
```lean
F 0 := K
F (j + 1) := π j
```
include **every domain-defining inequality**, including the closed-ball inequality.

### 5.1 Global part

Export:

- an analytic manifold `M` and analytic map `g : M → U`;
- properness and surjectivity;
- injectivity over
  \[
  U\setminus E,\qquad E=\bigcup_\ell\{F_\ell=0\};
  \]
  an analytic isomorphism there is stronger and useful, but injectivity is what this bridge needs.

For product resolution, do **not** demand injectivity merely off `{K = 0}`. Boundary resolution can modify points with `K ≠ 0`.

### 5.2 Finite-chart extraction around the relevant zero fibre

For every compact
\[
C_0\subseteq g^{-1}(W_{\rm dom}\cap\{K=0\}),
\]
export finitely many centred charts with nested boxes and:

\[
F_\ell(\operatorname{rep}_i(u))
  = b_{i\ell}(u)\prod_j u_j^{m_{i\ell j}},
\]
\[
\det D\operatorname{rep}_i(u)
  = b_{iJ}(u)\prod_j u_j^{h_{ij}},
\]
where:

- all units are analytic and nowhere zero on an open neighbourhood of the outer box;
- all factor units have a specified constant sign there;
- the phase exponent vector is active;
- the inner chart neighbourhoods cover `C₀`.

For the phase, ideally supply a **second-stage normalised version**:
\[
K(\operatorname{rep}_i(u))=c_i\prod_j u_j^{m_{ij}},
\qquad c_i\ne0.
\]

If ambient nonnegativity is available, strengthen this to your current even form with `cᵢ > 0`.

The unit-removal coordinate change must preserve coordinate signs. Then it preserves the selected-orthant description of the boundary inequalities, though it changes their units and the Jacobian unit.

### 5.3 Selected-orthant theorem

For `s : Fin d → {−1,+1}`, let `O_s` be the corresponding **open** orthant. Define admissibility by:
\[
\forall\ell\text{ a boundary index},\quad
\operatorname{sign}(b_{i\ell})
       \prod_j s_j^{m_{i\ell j}}=+1.
\]

Then export:
\[
\operatorname{box}_i\cap\operatorname{rep}_i^{-1}(W_{\rm dom})
=^{\rm a.e.}
\operatorname{box}_i\cap
\bigcup_{s\in S_i}O_s.
\]

On coordinate walls, non-strict inequalities can behave differently. That is precisely why a.e. equality is the correct interface.

Your existing `DomainSectorAtlasBoundary.ofBoundaryMonomials` and `WeightedDomainAtlas.domain_ae` look like the right consumers of this export.

### What is blocked by the BM disjunction?

The precise missing theorem is:

> For the nontrivial analytic phase/boundary family, construct one proper, surjective modification, injective away from the family’s zero divisor, with jointly monomial factor and Jacobian chart forms on a finite neighbourhood cover of each compact relevant zero fibre.

An `IsAnalyticQChart` disjunction is not itself this theorem. The extraction must show that each selected chart either:

- supplies the needed simultaneous forms; or
- is demonstrably irrelevant to the chosen zero fibre, or has a positive phase gap and is assigned to the tail.

Without inspecting the disjunction’s clauses, one cannot responsibly claim that this is only repackaging.

If the existing infrastructure already constructs one modification with individual factor forms, the work is substantial interface assembly. If it supplies only weaker local packets or ideal principalisation, this is the main mathematical/formalisation blocker.

---

## 6. Target B transport interface and bridge

### 6.1 Keep Target A stable; add a sibling interface

For the ambient-even case, define something like:

```lean
structure NormalisedDomainCoreTransport
    (d : ℕ) (K prior : E → ℝ) (Wdom : Set E) where
  -- existing analytic chart, phase, Jacobian, and weight fields
  sectors : ι → Finset (OrthantSign d)
  tail : Measure E
  δ : ℝ
  δ_pos : 0 < δ
  tail_gap : ∀ᵐ y ∂tail, δ ≤ K y
  transport :
    ∑ i,
      ((volume.restrict
          (centeredBox d (a i) ∩ selectedOrthants (sectors i))).withDensity
        (fun u =>
          ofReal (prior (ψ i u) * ω i u) * absDet (ψ i) u)).map (ψ i)
      + tail
      =
      (volume.restrict Wdom).withDensity (fun y => ofReal (prior y))
```

Put `domain_ae`, injectivity, and auxiliary exceptional-set information in the **assembly input**, not necessarily in the final consumer interface. The consumer needs the exact transport identity and the sector source geometry.

For domain-only nonnegativity, use arbitrary phase exponents or an adapter that produces even sector cores.

### 6.2 Bridge changes

The cutoffs remain unchanged: construct them on the full resolution manifold, not on a manifold with corners.

Set
\[
C_0=g^{-1}\!\left(
   W_{\rm dom}\cap\operatorname{tsupport}(\mathrm{prior})\cap\{K=0\}
\right).
\]

Assuming the domain is compact, or at least its intersection with the prior support is compact:

1. extract joint charts around `C₀`;
2. construct the same source cutoffs;
3. restrict source measures to domain preimages;
4. use `domain_ae` to replace these by selected orthants;
5. assemble against `volume.restrict Wdom`.

The significant change is the exceptional set:

> Target B must generally discard the zero sets of all resolved factors, not only the phase zero set.

Use a null source set containing the relevant coordinate walls—taking all coordinate walls is often simplest—and remove the target family-zero divisor in the a.e. argument. Nontrivial analytic boundary functions have null zero sets on a connected ambient region.

Away from this divisor:

- `g` is injective;
- lifts land in the selected sectors;
- the same target-weight sum argument works;
- a residual point lifts outside the cutoff neighbourhood.

The compact positive-gap argument is then unchanged.

### 6.3 Non-even phases: the compatibility adapter

If the consumer already handles arbitrary positive monomial phases on positive orthants, use that directly.

Otherwise split into selected orthants and use
\[
u_j=s_jv_j^2,\qquad v_j>0.
\]
After phase-unit normalisation,
\[
K(\psi(sv^2))=c_s\prod_j v_j^{2m_j},
\qquad c_s>0
\]
on an admissible sector.

The additional Jacobian changes
\[
h_j\longmapsto 2h_j+1,
\]
with the constant and sign incorporated into the new Jacobian unit. Smooth amplitudes remain smooth after composition.

Important: this is injective on the positive orthant, **not** on the full centred box. Therefore implement it as a sector/positive-box adapter. Do not force it into Target A’s full-box injectivity field.

### 6.4 Consumer changes

Your existing per-`(chart, selected orthant)` presentations should make this the smaller part of Target B:

- finite-sum splitting over open orthants;
- sign-flip pullbacks to positive boxes;
- smooth amplitude construction;
- monomial expansion;
- the existing finite-sum lattice and coefficient machinery;
- the same positive-gap tail estimate.

Do **not** multiply the smooth amplitude by a domain indicator. The domain indicator belongs in the source measure restriction.

---

## 7. Suggested implementation order and sizes

These are relative sizes, not calendar estimates.

| Unit | Size | Acceptance test |
|---|---:|---|
| Finish genuine-tail and empty-core regressions | S | Nonzero tail; strictly positive phase; zero prior |
| Phase-localisation wrapper removing `Measurable K` | S | Nonmeasurable behaviour allowed outside the analytic neighbourhood |
| Certificate-facing theorem and bounds | S | Downstream coefficient equality uses certificate uniqueness |
| Abstract selected-orthant transport and assembly | M | Handwritten identity chart on a half-box |
| Consumer adapter | S–M | Half-line even monomial and multiple selected sectors |
| Domain-only nonnegative phase adapter | M | `K(x)=x` on `[0,1]` |
| Joint resolution export | M–XL | Depends on what the BM disjunction actually yields |
| Resolution-to-domain bridge | M | Closed-ball inequality included; boundary exceptional divisor handled |
| Final paper-facing theorem | S after dependencies | Smooth prior on a neighbourhood of the compact domain |

**Parallelise the abstract sector transport/consumer work with the resolution-export audit.** There is no reason to block the former on the latter.

---

## 8. Cheap additions and paper wording

### Worth adding now

- **Locality of the integral in the phase on the prior support.**
- A pure-tail coefficient-vanishing theorem.
- A certificate wrapper exposing `D ≤ d - 1`.
- Translation invariance sufficient to replace the origin by an arbitrary zero.
- Regressions for empty support and empty core families.
- An explicit note that Target A’s target weights are measurable, not smooth.

Keep the smooth prior hypothesis. A merely continuous prior does not support an arbitrary-order smooth expansion.

For Target B, “smooth up to the boundary” should initially mean:

> the prior is the restriction of a smooth function on an open neighbourhood of the compact domain.

Then an ambient compactly supported cutoff equal to one near the domain reduces to your current smooth compact-support API. Do not take “smooth on the interior and continuous on the closure” as an equivalent hypothesis.

### Suggested paper-mirror paragraph

> We formalise the interior compact-support case by constructing, from resolution data, a finite smooth weighted atlas whose chart phases and Jacobians are monomial. The resulting chart measures satisfy an exact transport identity for the prior measure, with a residual measure supported almost everywhere where the phase has a uniform positive lower bound. Applying the smooth monomial expansion engine yields a coordinate-independent asymptotic expansion, with logarithmic degree at most \(d-1\); uniqueness makes its coefficients independent of the chosen resolution charts and weights. The compact semianalytic-domain case additionally requires simultaneous control of the boundary functions and selected-orthant source domains.

**Bottom line:** Target A has landed in the right form. For Target B, the critical export is simultaneous **factor** monomialisation on one proper modification, and the critical hypothesis distinction is **ambient nonnegativity versus nonnegativity only on the domain**. Settle those two points before committing to an “even charts” boundary interface.
