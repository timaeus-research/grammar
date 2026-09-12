## Recommendation

Run two programmes, and keep their claims distinct:

1. **In `grammar`, now:** prove a global leading-*measure* theorem for the original integral over a specified `W`, under an explicit **source-assembly certificate**. Its coefficient is
   \[
   C(\phi,\varphi)=\int_W \phi\,\varphi\,d\sigma,
   \]
   where \(\sigma\) is a finite measure supported on \(W_0=\{w\in W:K(w)=0\}\), computed by pushing forward the existing chart-face densities. Prove that the **total measure** is independent of any certificate producing the same normalized asymptotics.

2. **Separately, upstream:** obtain either stronger assembly data or an actual resolved space. The latter is needed for a theorem genuinely indexed by geometric strata \(S_I\), with intrinsic stratum measures and transition-invariant fibre integration.

Do **not** claim that the current `PartialResolution` produces either certificate automatically. In particular, replacing “chart coefficients” by “stratum integrals” in the name of a declaration would not solve the problem.

---

# 1. The global theorem to target now

Below are proposed new declarations, not claims about existing declaration signatures. Write:

```lean
namespace Grammar

abbrev Euclidean (d : ℕ) := Fin d → ℝ

noncomputable def globalLaplace
    {d : ℕ} (W : Set (Euclidean d))
    (K a : Euclidean d → ℝ) (t : ℝ) : ℝ :=
  ∫ w in W, a w * Real.exp (-t * K w)

noncomputable def laplaceScale (λ : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  Real.rpow t (-λ) * (Real.log t) ^ q
```

Here `q = m - 1`. Using `q : ℕ` avoids subtraction side conditions throughout assembly.

## 1.1 The primary result should be a scaled limit

For a compact region `W`, continuous nonnegative `K` on `W`, and a certified finite assembly, prove

```lean
theorem globalLaplace_tendsto_of_faceCertificate
    (hW : IsCompact W)
    (hK : Continuous K)
    (hK_nonneg : ∀ w ∈ W, 0 ≤ K w)
    (P : GlobalFaceCertificate W K)
    {a : Euclidean d → ℝ}
    (ha : Continuous a) :
    Tendsto
      (fun t : ℝ =>
        globalLaplace W K a t / laplaceScale P.lambda P.logPower t)
      atTop
      (𝓝 (∫ w, a w ∂P.leadingMeasure))
```

The certificate must contain *geometric/source integration data*, not this conclusion as a field. Its content is described below.

Also prove:

```lean
theorem GlobalFaceCertificate.leadingMeasure_finite
    (P : GlobalFaceCertificate W K) :
    IsFiniteMeasure P.leadingMeasure

theorem GlobalFaceCertificate.leadingMeasure_concentrated
    (P : GlobalFaceCertificate W K) :
    P.leadingMeasure ((W ∩ K ⁻¹' {0})ᶜ) = 0
```

“Concentrated on” is the precise property needed. For compact `W` and continuous `K`, it also gives the corresponding topological support containment.

Apply the scaled-limit theorem with `a = fun w => φ w * prior w`. Thus the theorem is about **exactly**
\[
\int_W\phi(w)\varphi(w)e^{-tK(w)}\,dw,
\]
not a replacement neighbourhood.

The continuity assumptions can subsequently be weakened to `ContinuousOn … W`, using extensions or direct restricted-measure arguments. Start with global continuity to avoid obscuring the assembly proof. Analyticity of the observable is **not needed** for this leading-measure theorem.

## 1.2 Asymptotic equivalence requires a nonzero coefficient

Define

```lean
noncomputable def globalLeadingCoeff
    (σ : Measure (Euclidean d))
    (φ prior : Euclidean d → ℝ) : ℝ :=
  ∫ w, φ w * prior w ∂σ
```

Then the desired equivalence is:

```lean
theorem globalLaplace_isEquivalent_of_faceCertificate
    (hW : IsCompact W)
    (hK : Continuous K)
    (hK_nonneg : ∀ w ∈ W, 0 ≤ K w)
    (P : GlobalFaceCertificate W K)
    (hφ : Continuous φ)
    (hprior : Continuous prior)
    (hC : globalLeadingCoeff P.leadingMeasure φ prior ≠ 0) :
    (fun t : ℝ => globalLaplace W K (fun w => φ w * prior w) t)
      ~[atTop]
    (fun t : ℝ =>
      globalLeadingCoeff P.leadingMeasure φ prior *
        laplaceScale P.lambda P.logPower t)
```

For a clean positive version, assume:

- `P.leadingMeasure ≠ 0`;
- `φ ≥ 0` and `prior ≥ 0` on `W`;
- `φ > 0` and `prior > 0` on `W₀`.

Then \(C>0\).

For **signed** analytic \(\phi\), retain the scaled-limit theorem unconditionally under the certificate. Cancellation can make \(C=0\). One cannot then claim equivalence to \(0\), or identify the next exponent from the leading-measure theorem.

Likewise, a nonnegative observable vanishing on the leading face may kill this term. The paper’s orders \(l_i\) belong to a further observable-sensitive analysis, not to the fixed leading measure constructed for the unweighted problem.

## 1.3 What is unconditional?

There are three different meanings to separate:

- All proposed proofs are ordinary, axiom-clean theorems.
- The theorem above is **conditional on `GlobalFaceCertificate`**.
- Production of that certificate from arbitrary
  ```lean
  R : PartialResolution d K W
  hR : R.IsMonomial
  ```
  is **not available** from the present interface.

Certificate-producing instances already within reach are:

- the existing a.e.-disjoint assembly, with supplied source product packages;
- certified box families;
- the concrete blow-up cube examples;
- enlargements of certified regions across a positive-\(K\) gap.

These give real global theorems over their specified regions. They are not a theorem for every compact `W` supplied to a partial resolution.

---

# 2. What the coefficient means

## 2.1 Use chart-face measures first

For each localized source piece \(a\), package the existing face functional as a finite measure \(\nu_a\) on its face-coordinate space and a face map
\[
q_a:\text{Face}_a\longrightarrow W.
\]

The measure includes all geometric factors in the existing leading coefficient:

- the gamma/factorial normalization;
- normal monomial constants;
- tangential monomial weights;
- the Jacobian unit;
- localization weights;
- any phase-unit contribution required by the actual local theorem.

Keep \(\phi\) and, preferably, the prior out of this measure. They become test functions \((\phi\varphi)\circ q_a\).

For mixed ratios, the face coordinates include the noncritical normal variables. The map is the chart map composed with \(P_J\), **not** evaluation at the deepest corner.

A small proposed structure is:

```lean
structure LeadingFacePiece (d : ℕ) where
  dim : ℕ
  measure : Measure (Euclidean dim)
  finite : IsFiniteMeasure measure
  toTarget : Euclidean dim → Euclidean d
  measurable_toTarget : Measurable toTarget

attribute [instance] LeadingFacePiece.finite

noncomputable def LeadingFacePiece.targetMeasure
    (a : LeadingFacePiece d) : Measure (Euclidean d) :=
  Measure.map a.toTarget a.measure
```

For the finite set \(T\) of pieces tied at the global dominant pair, define
\[
\sigma=\sum_{a\in T}(q_a)_*\nu_a.
\]

Then prove, by `integral_map` and finite-sum integration,
\[
\int_W\phi\varphi\,d\sigma
 =
 \sum_{a\in T}
 \int_{\text{Face}_a}
    (\phi\varphi)(q_a(v))\,d\nu_a(v).
\]

This is a genuine integral coefficient over the original target. It is also a precise repackaging of the library’s established face functional.

## 2.2 Do not call every summand an intrinsic stratum measure

The honest terminology is initially:

- `leadingMeasure`;
- `faceContributionMeasure`;
- optionally `stratumContributionMeasure` **relative to a supplied labelled atlas**.

The present interface has no globally identified divisor components. Consequently it has no canonical index type corresponding to the paper’s \(I\).

Even after grouping chart pieces by arbitrary labels, only the sum is intrinsically justified. Different exceptional strata can map to the same point of `W`; the pushforward total cannot recover their separate contributions.

In the all-ratios-tied situation, the local face is the normal corner, and the chart formula can reproduce
\[
\frac{\Gamma(\lambda)}{(m-1)!}\,
a_I\int (\phi\circ\pi)c_0\,|dv|
\]
with localization factors and the actual local unit conventions included.

In mixed-ratio situations, the existing face functional is the right formula. It is generally **not** an integral over the deepest intersection \(S_I\).

## 2.3 Canonicality comes from asymptotics, not from ownership

Suppose two certificates, with the same scale, give finite measures \(\sigma,\tau\), and each proves the scaled limit for **every continuous test function**. Then
\[
\int a\,d\sigma=\int a\,d\tau
\quad\text{for all continuous }a.
\]
Since both measures are concentrated on compact `W`, uniqueness of finite Borel measures gives \(\sigma=\tau\).

The Lean target is:

```lean
theorem leadingMeasure_unique
    (hW : IsCompact W)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσW : σ Wᶜ = 0)
    (hτW : τ Wᶜ = 0)
    (hσ : ∀ a : C(Euclidean d, ℝ),
      Tendsto
        (fun t : ℝ => globalLaplace W K a t / laplaceScale λ q t)
        atTop (𝓝 (∫ w, a w ∂σ)))
    (hτ : ∀ a : C(Euclidean d, ℝ),
      Tendsto
        (fun t : ℝ => globalLaplace W K a t / laplaceScale λ q t)
        atTop (𝓝 (∫ w, a w ∂τ))) :
    σ = τ
```

Use Mathlib’s measure-extensionality machinery through continuous or compactly supported continuous test functions; choose the exact route after checking the pinned version.

This proves **certificate independence of the total measure**. It does not prove existence of a certificate, and does not prove independence of separately labelled stratum summands.

If two positive, nonzero certificates initially have different pairs, comparing the test function `1` and the power–log scales first forces equality of their pairs.

---

# 3. Overlaps: which route is right?

## Immediate route: certified source transport

The right near-term abstraction is not specifically A, B, or C. It is an exact **source transport certificate** admitting any of them when justified.

For source charts \(\psi_i\), domains \(D_i\), and nonnegative weights \(\rho_i\), define
\[
\eta_i
=
\bigl(\rho_i\,|\det D\psi_i|\bigr)\,
(\operatorname{vol}|_{D_i}).
\]

Require a finite nonnegative target remainder measure \(\tau\) such that
\[
\operatorname{vol}|_W
=
\sum_i(\psi_i)_*\eta_i+\tau,
\qquad
\tau(\{K<\kappa\})=0
\]
for some \(\kappa>0\).

In Lean, the central certificate field has the form

```lean
transport :
  volume.restrict W =
    (∑ i, Measure.map (ψ i) (sourceMeasure i)) + tailMeasure
```

with finiteness, measurability, target-support and gap fields. The source measures are defined from the domains, weights and absolute Jacobians; they are not arbitrary measures.

The other substantive fields are the existing local source-decomposition/product data for these weighted source domains, organized so that continuous target test functions can be inserted without changing the geometry.

This is stronger and more reusable than an identity for one observable. It also exposes the overlap obligation exactly.

### Current a.e.-disjoint adapter

From `AEDisjointImages` plus supplied one-chart packages, prove this certificate with weight \(1\). This is the first implementation route.

### C: target continuous partitions

Do not use this as the generic solution. The image interiors need not cover the relevant target set.

A target partition subordinate to some *other* genuine open cover can be useful, but it does not by itself solve the remaining overlap problem inside each partial resolution.

### B: inverse multiplicity

This gives an exact measurable assembly after careful treatment of null exceptional images. It does not supply the regularity required by existing local leading-term results.

Moreover, inverse multiplicity is not magically compatible with evaluation on a dominant face. Its asymptotic trace must be proved. This route has essentially the same analytic obstruction as A.

### D: upstream refinement

An a.e.-disjoint refinement is useful, but **not sufficient on its own**. One still needs source domains and weights covered by the local integration theorem. Arbitrary measurable refinements of compact chart domains merely move the obstruction into the domains.

The minimum useful upstream deliverable is:

> a finite assembly with exact measure transport and source domains admitting certified normal-face asymptotics.

For genuine geometric strata, request a common resolved space, compatible charts, a proper resolution map, and globally identified divisor data. That is a larger programme.

---

# 4. If pursuing ownership, use a Laplace normal density

A measurable ownership partition is easy compared with its asymptotics.

After choosing an order,
\[
A_i=\operatorname{image}_i\setminus\bigcup_{j<i}\operatorname{image}_j,
\qquad
D_i=\operatorname{dom}_i\cap\psi_i^{-1}(A_i).
\]

Compact images are measurable. Change of variables can establish exact assembly, using chartwise injectivity off the exceptional set and nullity of its image. Smoothness near a compact domain provides the local Lipschitz/null-image argument where needed.

But `PartialResolution.dom` is only compact. Therefore:

- the resulting \(D_i\) need not be semianalytic;
- even with analytic maps and box domains, projected images naturally lead to **subanalytic**, not automatically semianalytic, sets;
- arbitrary measurable ownership domains need not have a leading term at the original chart scale.

## 4.1 Ordinary Lebesgue normal density is wrong

The relevant concentration is logarithmic.

For example, with two equal critical ratios on \((0,1)^2\), consider
\[
D=\{x<y^r\},\qquad r>1.
\]
Its ordinary two-dimensional density at the corner is zero. Nevertheless it occupies a positive fraction of the leading logarithmic mass: in logarithmic coordinates the condition cuts a positive-length portion of the dominant simplex.

Thus a theorem based solely on ordinary density at the corner would miss a nonzero coefficient.

## 4.2 A concrete sufficient density hypothesis

First prove the masked theorem for an exact positive monomial phase on a product box:
\[
M(x,z)=
\prod_{j\in J}x_j^{p_j}
\prod_{i\notin J}z_i^{p_i},
\quad
\lambda=\min_{p_i>0}\frac{h_i+1}{p_i},
\quad
J=\left\{i:\frac{h_i+1}{p_i}=\lambda\right\}.
\]

For fixed noncritical coordinates \(z\), define
\[
R_D(t,z)=
\int_{B_J}
1_D(x,z)e^{-tM(x,z)}
\prod_{j\in J}x_j^{h_j}\,dx,
\]
and \(R_{\mathrm{full}}\) by omitting \(1_D\).

A useful sufficient hypothesis is:

\[
\frac{R_D(t,z)}{R_{\mathrm{full}}(t,z)}
\longrightarrow \theta(z)
\quad\text{for face-density-a.e. }z,
\qquad 0\le\theta\le1.
\tag{LD}
\]

Call this `HasLaplaceNormalDensity`, not `HasLebesgueDensity`.

For continuous amplitudes \(G\), the target theorem is
\[
\frac{\int_D G(x,z)e^{-tM(x,z)}
               x^{h_J}z^{h_{J^c}}\,dx\,dz}
     {t^{-\lambda}(\log t)^{|J|-1}}
\longrightarrow
\frac{\Gamma(\lambda)}{(|J|-1)!}
\prod_{j\in J}\frac1{p_j}
\int
G(0,z)\theta(z)
\prod_{i\notin J}z_i^{h_i-p_i\lambda}\,dz.
\]

Tangential coordinates with \(p_i=0\) remain among the face coordinates.

A Lean-level predicate can expose precisely the density condition:

```lean
def HasLaplaceNormalDensity
    (M : NormalMomentData)
    (D : Set M.Source)
    (θ : M.Face → ℝ) : Prop :=
  MeasurableSet D ∧
  Measurable θ ∧
  (∀ᵐ z ∂M.faceMeasure, θ z ∈ Set.Icc 0 1) ∧
  ∀ᵐ z ∂M.faceMeasure,
    Tendsto
      (fun t : ℝ => M.maskedNormalMass D t z / M.normalMass t z)
      atTop (𝓝 (θ z))
```

`NormalMomentData` is a new packaging of the existing monomial box data. Its definitions must specify the normal and face measures explicitly.

The proof needs two reusable facts:

1. normalized unmasked fibre masses converge in an integrable sense to the known face density;
2. leading mass concentrates at \(x_J=0\), so a continuous amplitude can be replaced by its face trace, even after multiplying by \(1_D\).

Then the bound \(0\le R_D/R_{\mathrm{full}}\le1\) handles the mask by dominated/Vitali-style integration.

A continuous positive phase unit requires a further stability argument; it must not be silently dropped. One can use concentration and local squeezing by facewise values of the unit, together with the density limit under fixed positive rescalings of \(t\).

### Important limitation

This is a **sufficient hypothesis**, not a theorem that all ownership regions satisfy it.

Fibre-saturated ownership near the face is an easy certified case: \(\theta\) is the indicator of the owned face region. More general logarithmic cones allow fractional \(\theta\).

Proving (LD) for arbitrary subanalytic ownership domains would require substantial tame-geometry/rectilinearization machinery absent from the stated interface. It is not an eight-small-unit follow-up.

---

# 5. Why transition maps cannot be recovered where needed

Off the exceptional loci, inverse branches can recover transitions on appropriate overlapping regular images.

That is useful for ordinary change of variables. It is insufficient for stratum integration because:

- the dominant faces lie precisely in the exceptional locus;
- injectivity may fail there;
- the target can collapse an entire exceptional component to a point;
- inverse branches need not extend to faces;
- no compatibility of such extensions is supplied.

Thus candidate (i) cannot presently prove intrinsic exceptional-stratum measures.

Candidate (ii) is the right global object, with one correction:

> A sum of pushforwards is not chart-independent “by construction.” It becomes independent after proving the universal test-function asymptotic and invoking uniqueness.

An ownership partition is also not canonical merely because an ordering was chosen.

---

# 6. What can be said for arbitrary regions without a certificate?

A useful additional theorem is a **global Θ theorem**, obtained by compactness from the existing local Θ result.

Assume:

- `W` compact;
- `W₀` nonempty and `W₀ ⊆ interior W`;
- `K` analytic on an open neighbourhood of `W`;
- `K ≥ 0` on `W`;
- at every `w ∈ W₀`, `¬ K =ᶠ[𝓝 w] 0`;
- `φ`, `prior` continuous;
- both nonnegative on `W` and strictly positive on `W₀`.

Then prove the existence of \(\lambda>0\), \(q\in\mathbb N\) with
\[
\int_W\phi\varphi e^{-tK}
=
\Theta\!\left(t^{-\lambda}(\log t)^q\right).
\]

The exponent pair is extremal over a finite family of local resolution neighbourhoods, each with its existing local extremal pair.

Proof:

1. choose local compact neighbourhoods contained in `interior W`;
2. extract finitely many whose interiors cover `W₀`;
3. use a sum for the upper bound and one extremal neighbourhood for the lower bound;
4. on the remaining compact region, obtain \(K\ge\kappa>0\);
5. compare the positive continuous amplitude with constants near `W₀`.

This does **not** need disjointness. It should be derivable without an upstream change, subject to checking that the existing local theorem’s neighbourhood can be chosen within the requested ambient open set.

Do not state this for completely arbitrary compact `W` meeting the zero set only on its boundary. Pathological boundary geometry can change or destroy power–log asymptotics.

For a bounded open `W`, a clean extension is available when `K` and the amplitudes extend continuously to compact `closure W`, the zeros in the closure lie inside `W`, and the relevant integrability bounds hold. Choose a compact core containing those zeros; the rest has a positive-\(K\) gap.

---

# 7. Eight-unit implementation plan

These are **certificate-route units**, not a promise to solve arbitrary ownership densities in 3,000 lines. Line estimates exclude large new upstream mathematics.

| # | Proposed unit | Main content and gate | Estimate |
|---|---|---|---:|
| 1 | **`GlobalLaplaceMeasureBasic`** | Define `globalLaplace`, `laplaceScale`, `LeadingFacePiece`, finite sums of pushforward face measures. Prove finiteness, concentration, and integral-of-test-function formula. Tools: `Measure.map`, `withDensity`, `integral_map`, finite-sum integration. **Gate:** one existing source coefficient is represented exactly, with all constants. | 250–350 |
| 2 | `SourceFaceMeasureAdapter` | Turn each existing source-face functional into Unit 1 data; use `sourceDominantFace`, including mixed-ratio coordinates. **Gate:** recover `sourceCoeff` and `sourceDecompCoeff`, not a corner-evaluation substitute. | 300–400 |
| 3 | `SourceTestFunctionStability` | Show fixed source-localization/product data work uniformly when the amplitude is multiplied by a continuous target test function. Extend positive results to signed tests by continuous positive/negative parts or bounded shifts. **Gate:** no dependence of the geometry on the chosen observable. | 300–400 |
| 4 | `GlobalSourceTransportCertificate` | Define exact measure-transport, tail-gap and local-package fields. Build an adapter from `AEDisjointSourceAssembly` plus supplied packages. **Gate:** derive the original target integral identity; no hidden “sum of overlapping charts” step. | 300–400 |
| 5 | `GlobalLeadingMeasure` | Prove the scaled-limit theorem, discard subdominant pairs, and bound the tail exponentially. **Gate:** conclusion contains `globalLaplace W K a`, for the supplied `W`. | 300–400 |
| 6 | `GlobalLeadingMeasureCanonical` | Prove uniqueness from continuous tests, nonzero-coefficient equivalence, positivity criteria, and prior insertion. **Gate:** independence of total measure only; no unsupported claim about labelled strata. | 250–400 |
| 7 | `GlobalLeadingMeasureLocality` | Transfer certificates/results across regions differing in a positive-\(K\) region; add bounded-open-region corollaries. Reprove cube/separable regressions as target-measure statements. **Gate:** coefficient agrees with existing explicit constants. | 250–350 |
| 8 | `GlobalCompactLaplaceTheta` | Finite-cover globalization of the local Θ theorem under the interior-zero-set hypotheses above. **Gate:** no assembly certificate or a.e.-disjointness assumption. | 300–400 |

If Unit 3 exposes that the existing packages are genuinely observable-specific, stop and refactor that interface before proceeding. A certificate for one scalar coefficient is not enough to prove measure canonicality.

Mathlib supplies the measure transport, restricted measures, Bochner integration, compactness, continuous-function separation of finite measures, and asymptotic limit machinery. The existing grammar modules must supply the normal-moment analysis. Mathlib should not be expected to supply semianalytic ownership asymptotics or a resolved-space tubular-neighbourhood theorem.

---

# 8. End-state and explicit non-claims

At the end of this programme:

### Proved

- A theorem for the **original integral over the specified `W`**.
- A coefficient expressed as a finite sum of face integrals, equivalently
  \[
  C(\phi,\varphi)=\int_W\phi\varphi\,d\sigma.
  \]
- Concentration of \(\sigma\) on `W₀`.
- Canonicality of the **total** \(\sigma\) among valid certificates.
- Signed-observable scaled limits; equivalence when the coefficient is nonzero.
- Unconditional certificate adapters for the currently certified geometric examples.
- A general compact-region Θ theorem under the stated interior and nontriviality assumptions.

### Still hypotheses

- Exact source assembly and admissible local source packages in the general leading-term theorem.
- In the current adapter: a.e.-disjointness and the supplied product packages.
- In a future ownership adapter: the appropriate Laplace normal-density condition.
- Positivity/nonvanishing when claiming a positive leading coefficient.

Analyticity of \(\phi\) need not remain a hypothesis.

### Not proved

- Certificate production from an arbitrary current `PartialResolution`.
- Canonical individual measures indexed by the paper’s geometric \(S_I\).
- The full asymptotic series.
- Observable-dependent next terms after leading cancellation.
- The paper’s literal deepest-corner coefficient in mixed-ratio cases.

No upstream change is needed for the eight-unit certificate programme. An upstream change—or a substantial independent tame-region analysis—is needed to remove its assembly hypotheses. A common resolved space with compatible divisor geometry is needed to justify the paper’s intrinsic stratum formulation.

**The first deliverable should therefore be named `GlobalLaplaceMeasureBasic`, and the programme’s headline should be “global leading measure for the original integral,” not yet “global intrinsic strata expansion.”**
