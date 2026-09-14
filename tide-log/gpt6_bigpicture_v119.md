## Recommendation

**Approve Target A, but change the bridge’s output.** The first construction should produce a **finite, smooth, normalised core presentation of the prior-weighted measure, plus a phase-gap tail**. It should not initially promise an inhabitant of the existing `WeightedDomainAtlas`.

The reason is structural: the existing atlas transports **unweighted volume on a compact target set**, with every chart box mapping into that set. A partition constructed near `g⁻¹(tsupport prior)` naturally transports the **prior-weighted measure**. Its partition need not sum to one at all points in the images of the outer chart boxes.

Adding a third or fourth nested box does not resolve that mismatch.

My preferred implementation is:

1. use **only zero charts**;
2. construct smooth cutoffs on the resolution space, whose sum is at most one everywhere and equals one near the relevant exceptional fibre;
3. transport their contributions chart by chart;
4. put the remaining prior-weighted measure into a **weighted residual tail**.

This avoids off-zero chart infrastructure, domain rectification, a global manifold integration theory, and the restrictive compact-target bookkeeping of `PartialResolution`.

---

## 1. Audit of the proposed plan

### 1.1 Properness gives the compact set you need

Write
```lean
S := tsupport prior
```
and regard `S`, using `S ⊆ W`, as a compact subset of the subtype `W`. Then
```lean
C := g ⁻¹' S
C₀ := {P ∈ C | K (inclusion W (g P)) = 0}
```
are compact.

There will be some subtype bookkeeping here: properness is into `W`, not into all of `ℝ^d`. No global properness assertion about `inclusion W ∘ g` should be introduced.

The continuity needed to make `C₀` closed in `C` follows from analyticity of `K` on `W`.

### 1.2 The exact phase normalisation really is already available

For every zero chart, after `even_of_nonneg`,
\[
K(\psi_i(u))=\prod_j u_j^{2k_{ij}},\qquad
\det D\psi_i(u)=b_i(u)\prod_j u_j^{h_{ij}}.
\]

At the chart centre, the left side is zero. Therefore at least one `k i j` is positive. In particular, the phase-zero set in the chart is precisely
\[
H_i^K=\bigcup_{j:\,0<k_{ij}}\{u:u_j=0\},
\]
and is null.

Do not define “walls” ambiguously. Distinguish:

- phase walls `Hᵏ`, needed for `isoOff` and inverse-branch identification;
- Jacobian walls `Hʰ`, needed if proving `jac_ne_zero` directly from the determinant formula.

For a `PartialResolution` construction, the safe exceptional set is
```lean
E i := box i ∩ (phaseWalls (k i) ∪ jacWalls (h i))
```
rather than silently assuming that phase walls contain all Jacobian walls. Such containment may be provable from `isoOff`, but it is unnecessary for the bridge.

### 1.3 A finite local null-set argument replaces the analytic zero-set theorem

**Do not make a general analytic-zero-set-null theorem a dependency of Target A.**

The resolution already supplies a shorter proof of
```lean
volume (S ∩ {y | K y = 0}) = 0.
```

Indeed:

1. cover `C₀` by finitely many zero-chart inner boxes;
2. use surjectivity to lift every point of `S ∩ {K = 0}`;
3. in each chart, its lift lies on the phase walls;
4. those walls are null;
5. the chart map into `ℝ^d` is smooth on a neighbourhood of the box, so its image of the wall portion is null.

The available
```lean
addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
```
is the relevant tool, with whatever localisation its exact signature requires.

This proves exactly the target-null statement needed for the prior-weighted measure. It also avoids claiming that Mathlib already contains the general analytic theorem.

A general analytic-zero-set-null theorem remains a worthwhile independent export, but not a prerequisite here.

### 1.4 Step 4 must use an a.e. representative—not equality by continuity

Define, on the regular target,
\[
\chi_i(y)=\rho_i(g^{-1}y),
\]
and set it to zero elsewhere.

Then on a zero chart,
\[
\chi_i(\psi_i(u))=\rho_i(\varphi_i^{-1}(u))
\]
**off the phase walls**. On the phase walls, the left side is zero by definition, whereas the right side can be positive.

Consequently:

> The target pullback does not become equal everywhere to the smooth representative “by continuity”.

Instead define
```lean
ω i u := ρ i (chart i).symm u
```
on the chart neighbourhood and prove
```lean
(fun u => χ i (ψ i u)) =ᵐ[volume.restrict (box i)] ω i
```
using nullity of the phase walls.

That is the correct use of `HasWeightedTransport.congr_ae`, or of the corresponding direct change-of-variables lemma.

### 1.5 Measurability of `χ` requires a small inverse-branch lemma

`BijOn` alone is insufficient. Use both parts of `isoOff`:

- bijectivity on the regular locus;
- local diffeomorphism, hence local homeomorphism, there.

Together they give a continuous inverse between the regular-locus subspaces. Thus `χ i` is continuous on the open regular target and measurable after extension by zero.

This should become a named helper theorem. It is not a reason to construct target-side smooth partitions.

For total Euclidean chart maps, also settle measurability explicitly. An `OpenPartialHomeomorph.symm` evaluated outside its target should not silently be treated as a globally continuous function. One inexpensive solution is a measurable totalisation:
```lean
ψ i u := if u ∈ V i then watanabeRep ... u else 0
```
where `V i` is open and contains the box. It agrees with the original analytic map on `V i`, including derivatives there.

### 1.6 The compact-target box problem is real

Let `L` be the union of lifted inner boxes, and `D` the union of lifted integration boxes.

A partition summing to one on `L` need not sum to one on `D`. If you enlarge its equality set to `D`, its subordinate supports generally require larger chart domains. Taking the images of those larger domains as the compact target repeats the problem.

Thus the proposed construction does **not** establish the existing `WeightedDomainAtlas` by a finite nesting trick.

This is not a failure of resolution geometry. It is a mismatch between:

- a support-local partition;
- transport of all volume on the union of full box images.

For compactly supported prior, transport the prior-weighted measure instead.

---

## 2. The preferred bridge: zero charts plus a weighted residual tail

### 2.1 Two boxes are enough

For each selected zero chart choose symmetric boxes
\[
B_i\subset \operatorname{int}D_i,\qquad D_i\subset \varphi_i.target,
\]
with
\[
C_0\subset\bigcup_i\varphi_i^{-1}(\operatorname{int}B_i).
\]

Choose Euclidean smooth bumps `β i` satisfying:

- `0 ≤ β i ≤ 1`;
- `β i = 1` on `B i`;
- `tsupport (β i) ⊆ int (D i)`.

Lift them by the chart and extend by zero on the resolution space:
\[
b_i(P)=
\begin{cases}
\beta_i(\varphi_i(P))&P\in\varphi_i.source,\\
0&\text{otherwise}.
\end{cases}
\]
Let \(s=\sum_i b_i\).

Choose a smooth scalar normaliser `q` such that, for `t ≥ 0`,
\[
q(t)\ge0,\qquad tq(t)\le1,\qquad tq(t)=1\quad(t\ge\tfrac12).
\]
For example, use a smooth cutoff `η`, zero near zero and one for `t ≥ 1/2`, and smoothly define `q(t)=η(t)/t`.

Set
\[
\rho_i=b_i\,q(s).
\]

Then:

- `ρ i ≥ 0`;
- `∑ i, ρ i ≤ 1`;
- each `ρ i` is supported in its lifted integration box interior;
- `∑ i, ρ i = 1` on the open set
  \[
  O=\{P:s(P)>\tfrac12\},
  \]
  which contains `C₀`.

This normalisation is globally smooth. Do not simply divide by `s` and assign zero at `s = 0`: that extension need not be smooth.

### 2.2 Define the residual on the target

On the regular target put
\[
\alpha(y)=\sum_i\chi_i(y),
\]
and put `α = 0` elsewhere. Then `α` is measurable and `0 ≤ α ≤ 1`.

Define
```lean
μ := volume.withDensity (fun y => ENNReal.ofReal (prior y))

tail := volume.withDensity
  (fun y => ENNReal.ofReal (prior y * (1 - α y)))
```

For each chart define the source measure
\[
\nu_i=
\left(
  \operatorname{ofReal}\bigl(
    prior(\psi_i(u))\,\omega_i(u)\,|\det D\psi_i(u)|
  \bigr)
\right)\,du\big|_{D_i}.
\]

The central bridge identity is
\[
\boxed{\quad \sum_i(\psi_i)_*\nu_i+\mathrm{tail}=\mu.\quad}
\]

Prove it first for nonnegative measurable test functions, or directly as a measure identity.

On the target zero set within `S`, `α` was assigned zero, but that set is null by §1.3. Thus this arbitrary assignment does not obstruct the identity or the tail-gap proof.

### 2.3 The residual has a uniform phase gap

The compact set
\[
F=C\setminus O
\]
contains no zero of `K ∘ g`. Hence, if nonempty, it has a positive minimum:
\[
\delta\le K(g(P))\qquad(P\in F).
\]

For regular `y ∈ S`, if `1 - α y > 0`, its unique lift cannot belong to `O`. Therefore
\[
\forall^\mathrm{ae}y\ \partial\mathrm{tail},\quad \delta\le K(y).
\]

If `F` is empty, take any positive `δ`; the residual is zero a.e.

This is the cleanest tail for Target A. It is **not generally**
```lean
(volume.restrict T).withDensity ...
```
for a target region `T`: it has a fractional residual density.

Accordingly, if introducing a new transport structure, allow a tail **measure**, not only a tail region.

### 2.4 What about the proposed sharp-region option?

Your concern that `g` need not be open is correct, but properness repairs the neighbourhood argument.

If `O` is open and contains the entire fibre over every point in `S ∩ {K = 0}`, then, using closedness of the proper map under the relevant Hausdorff hypotheses,
\[
W\setminus g(U\setminus O)
\]
is an open neighbourhood of those target zeros, contained in `g(O)`.

So one can obtain a target neighbourhood and a phase gap for a sharp complement without assuming `g` is open.

However, this **does not repair the `WeightedDomainAtlas` full-box transport problem**. The weighted residual construction avoids both issues and is the better first implementation.

---

## 3. `PartialResolution` or direct transport?

### Recommended first route: direct chart transport

Use
```lean
lintegral_image_eq_lintegral_abs_det_fderiv_mul
```
on each integration box with its exceptional walls removed.

The proof uses:

1. injectivity from `isoOff` and chart injectivity;
2. source exceptional-set nullity;
3. image exceptional-set nullity;
4. the source-weight/target-weight a.e. identification;
5. support subordination, which makes `χ i` vanish outside the chart image;
6. finite summation and the residual-density identity.

This is still a finite Euclidean change-of-variables argument. It does **not** require integration on `U`.

The `mult` fields are not the major mathematical difficulty—off the exceptional target, multiplicity is at most the number of charts. But constructing them gives no benefit for this support-weighted theorem, and the existing `mapsTo`/compact-target requirements are the wrong shape.

### Retain `PartialResolution` as a later adapter

If later work supplies an actual compact target and compatible full-box cover, an adapter can recover its fields and use `hasWeightedTransport_of_partition`.

Do not make that adapter the critical path for Target A.

---

## 4. Risk 1: construct chartwise cutoffs, not a manifold PoU dependency

First inspect the instances and compatibility lemmas carried by `AnalyticManifold`. The quoted signatures do not establish `T2Space`, `SigmaCompactSpace`, or a Mathlib `IsManifold` instance by themselves.

The cheapest robust fallback is exactly the finite chart-bump construction, with one refinement:

> Formalise only the chartwise smoothness you actually consume.

You need:

- continuity of the lifted bumps on `U`;
- compactness/closedness of their lifted supports;
- smoothness of every expression
  ```lean
  fun u => liftedBump j ((chart i).symm u)
  ```
  on `chart i.target`.

On an overlap this follows from analytic, hence smooth, transition maps. Away from the compact lifted support, the expression is locally zero. Hausdorffness is important for that compact-support argument.

You do not need a global Mathlib predicate `ContMDiff ... ρ i` if the output interface only asks for these coordinate representatives to be smooth.

Thus:

- **necessary investigation:** topology of `U`, atlas transition regularity, local smoothness of `watanabeRep`;
- **avoidable investigation:** global `SigmaCompactSpace U` and a complete Mathlib manifold adapter.

If the adapter is already almost available, use it. Otherwise do not build an entire adapter merely to obtain a finite partition near a compact set.

---

## 5. Local smoothness and normalisation

### 5.1 Extend the amplitude, not the atlas

Choose the second option in step 7.

Keep the original chart maps and exact phase/Jacobian identities on open neighbourhoods of the boxes. For each chart, form the local amplitude
\[
G_i(u)=
\omega_i(u)\,|b_i(u)|\,
prior(\psi_i(u))\,obs(\psi_i(u)).
\]

It is smooth on that neighbourhood:

- `|b i|` is smooth because `b i` is nonvanishing there;
- no globally fixed sign of `b i` is required.

Use `exists_contDiff_eqOn_of_contDiffOn` to extend **this one scalar function**, agreeing on the closed integration box. Feed the extension to `ofAffine`.

Do not rebuild the atlas with `V := int dom`: that would violate `dom_subset_V`, since the closed box includes its boundary.

A grammar-side local-amplitude constructor is cleaner than extending `φ`, `ω`, and `jacUnit` separately and trying to preserve analytic record fields.

### 5.2 Rescaling changes `phaseUnit = 1` into a positive constant

If
\[
u_j=r_{ij}v_j,\qquad r_{ij}>0,
\]
normalises the box to `[-1,1]^d`, then
\[
K(\widetilde\psi_i(v))
=
\left(\prod_j r_{ij}^{2k_{ij}}\right)
\prod_j v_j^{2k_{ij}}.
\]

So after box normalisation:

- `phaseUnit` is a positive constant, not necessarily `1`;
- `hu_tan` remains immediate;
- the new Jacobian unit is
  \[
  \widetilde b_i(v)
  =b_i(r_i v)\prod_j r_{ij}^{h_{ij}+1}.
  \]

There is no remaining variable-unit normalisation problem.

---

## 6. Proposed output interfaces and final theorem

The following are **proposed interfaces**, not claims about existing identifiers or immediately compiling code.

### 6.1 Geometry-side output

A useful structure is a `SmoothWeightedNormalisedCoreTransport K prior` with:

```lean
-- Schematic fields
ι : Type
[fin : Fintype ι]

ψ : ι → E → E
V : ι → Set E
V_open : ∀ i, IsOpen (V i)
box_subset_V : ∀ i, unitBox ⊆ V i
ψ_measurable : ∀ i, Measurable (ψ i)
ψ_analytic : ∀ i, AnalyticOnNhd ℝ (ψ i) (V i)

k h : ι → Fin d → ℕ
k_active : ∀ i, ∃ j, 0 < k i j
phaseConst : ι → ℝ
phaseConst_pos : ∀ i, 0 < phaseConst i
phase_eq : ∀ i, ∀ u ∈ V i,
  K (ψ i u) = phaseConst i * ∏ j, u j ^ (2 * k i j)

jacUnit : ι → E → ℝ
jacUnit_analytic : ...
jacUnit_ne_zero : ...
jac_eq : ...

ω : ι → E → ℝ
ω_smoothOn : ∀ i, ContDiffOn ℝ ∞ (ω i) (V i)
ω_nonneg : ...
ω_le_one : ...

tail : Measure E
δ : ℝ
δ_pos : 0 < δ
tail_gap : ∀ᵐ y ∂tail, δ ≤ K y

transport :
  (∑ i, (sourceMeasure prior i).map (ψ i)) + tail
    = volume.withDensity (fun y => ENNReal.ofReal (prior y))
```

Include, or derive, the finiteness and support facts needed by the consumer. A finite empty chart family must be allowed.

The bridge theorem should first accept a modification explicitly:
```lean
theorem WatanabeModificationOn.exists_smoothWeightedNormalisedCoreTransport
    (R : WatanabeModificationOn K W)
    (hK_nonneg : ∀ y ∈ W, 0 ≤ K y)
    (hp : ContDiff ℝ ∞ prior)
    (hp0 : ∀ y, 0 ≤ prior y)
    (hpc : HasCompactSupport prior)
    (hpW : tsupport prior ⊆ (W : Set E))
    ... :
    Nonempty (SmoothWeightedNormalisedCoreTransport K prior)
```

Include local continuity/analyticity assumptions on `K` if they are not recoverable from the modification’s fields.

### 6.2 Grammar-side consumer

Add a constructor of the form
```lean
def SmoothWeightedNormalisedCoreTransport.toSmoothCoreDecomposition
    (T : SmoothWeightedNormalisedCoreTransport K prior)
    (hobs : ContDiff ℝ ∞ obs)
    ... :
    SmoothCoreDecomposition ...
```

Its responsibilities are:

- extend the local scalar amplitudes;
- build normalised signed-sector presentations;
- retain `T.tail`;
- transfer the phase gap;
- establish observable integrability.

Since `obs` is continuous and the original prior has compact support, the required absolute integrability follows from compactness. The transport identity also gives domination of each transported core and the tail by the original prior measure.

### 6.3 Target A theorem

A Lean-ready theorem shape is:

```lean
theorem exists_hasSmoothCoordFreeExpansion_of_analytic_compactSupport
    (hU₀ : IsOpen U₀)
    (hK : AnalyticOnNhd ℝ K U₀)
    (W : Opens E)
    (hW : IsConnected (W : Set E))
    (h0W : (0 : E) ∈ W)
    (hWU₀ : (W : Set E) ⊆ U₀)
    (hK0 : K 0 = 0)
    (hKne : ¬ ∀ᶠ x in 𝓝 (0 : E), K x = 0)
    (hKnonneg : ∀ x ∈ W, 0 ≤ K x)
    (hprior : ContDiff ℝ ∞ prior)
    (hprior0 : ∀ x, 0 ≤ prior x)
    (hpriorCompact : HasCompactSupport prior)
    (hpriorW : tsupport prior ⊆ (W : Set E))
    (hobs : ContDiff ℝ ∞ obs) :
    ∃ c Q D,
      HasSmoothCoordFreeExpansion
        (globalLaplace Set.univ K (fun x => prior x * obs x))
        c Q D
```

One bookkeeping issue: analyticity on `U₀` does not imply global `Measurable K`. For the final theorem, avoid an unnecessary global hypothesis by replacing `K` outside `W` with a measurable constant-valued extension. The prior-weighted integral is unchanged pointwise. A lower-level consumer may reasonably require the measurable representative.

---

## 7. Ordered implementation units

Sizes below are rough planning ranges, not estimates based on inspecting the source files.

| Unit | Side | Statement/output | Inputs | Size / risk |
|---|---|---|---|---|
| **0. API probes** | hironaka | Check topology, atlas-transition smoothness, regular-locus inverse, local analyticity of `watanabeRep` | Existing exports | Small; high leverage |
| **1. Supported one-chart transport** | hironaka | A prior-weighted source measure maps to `μ.withDensity (ofReal ∘ χ)` | Compact box, local smooth map, injectivity off a null set, null exceptional image, target support condition, a.e. weight pullback | 200–450 lines; medium |
| **2. Finite residual transport** | hironaka | `∑ mapped pieces + residual = μ` | Unit 1, measurable nonnegative `χ`, `∑ χ ≤ 1` μ-a.e. | 100–250 lines; low–medium |
| **3. Local-amplitude consumer** | grammar | Local smooth normalised core data plus a gap tail gives `SmoothCoreDecomposition` | Exact monomials, local smooth amplitudes, measure identity | 200–450 lines; medium |
| **4. Finite chart cutoff system** | hironaka | Cutoffs with chartwise smooth representatives, subordinate supports, sum ≤1, sum =1 near a compact set | Finite nested chart boxes, Hausdorffness, smooth transition maps | 300–700 lines; medium–high |
| **5. Compact Watanabe zero-chart extraction** | hironaka | Finite inner/outer symmetric boxes covering `C₀`, exact even monomials, local Jacobian units | Modification, compact support, nonnegative phase | 250–600 lines; medium |
| **6. Local zero-image nullity and inverse weights** | hironaka | `volume (S ∩ {K=0}) = 0`; measurable `χ`; a.e. smooth pullback representatives | Units 4–5, `isoOff`, null-image theorem | 200–500 lines; medium |
| **7. Residual phase gap** | hironaka | Positive gap for the residual tail | Compact `C`, cutoff equality near `C₀`, regular inverse | 100–250 lines; low–medium |
| **8. Normalised core-transport constructor** | hironaka | `Nonempty (SmoothWeightedNormalisedCoreTransport K prior)` | Units 2, 4–7; diagonal rescaling | 200–450 lines; medium |
| **9. Target A assembly** | grammar | Final existential expansion theorem | Resolution existence, Unit 8, Unit 3, existing expansion theorem | 100–250 lines; low–medium |
| **10. Optional strict-atlas adapters** | either | Convert compatible compact-domain data into existing atlas interfaces | Additional geometric/domain hypotheses | Separate scope |

### First unit to land

**Land Unit 1 first**, after the small API probes. It is the reusable resolution-space-to-weighted-transport kernel and does not depend on solving manifold PoU.

Its theorem should be stated in terms of arbitrary measurable target density, rather than only a smooth prior, so that later boundary work can reuse it.

### First regression

Use `d = 1`, `K x = x²`, and the identity chart/modification.

Run two cases:

1. **No-tail case:** prior support lies in the region where the cutoff is one. The tail vanishes and the coefficient formula agrees with the existing one-dimensional/CD-style certificate, using the appropriate coefficient-uniqueness theorem.
2. **Genuine-tail case:** prior support extends beyond that region. The residual is nonzero but has an explicit phase gap, for example `x² ≥ r²` wherever the residual density is nonzero.

The second test is essential: it prevents accidentally rebuilding a tail-zero-only interface.

Also test an empty core family: prior supported away from zero should produce a purely exponential tail.

---

## 8. Target B

Target B should begin only after Target A’s support-weighted transport kernel lands.

The required geometric export is a **simultaneous exact chart packet** for the phase and the finite list of functions defining the semianalytic domain:

- exact normalised even monomial phase;
- exact Jacobian monomial with nonvanishing analytic unit;
- for each boundary function, an exact monomial times a nonvanishing analytic unit, or an explicitly handled identically-zero case;
- all identities on one common chart neighbourhood;
- enough sign control to turn the domain’s Boolean formula into selected orthants, up to null walls.

After shrinking to a connected box neighbourhood, each nonvanishing boundary unit has constant sign. That is what makes orthant selection possible.

The existing `AnalyticQChartPacket` should be audited branch by branch. Its phase disjunction must be discharged or classified into:

- genuine normalised phase cores;
- positive-gap pieces;
- excluded or separately handled degenerate cases.

Do not assume that auxiliary-function support alone supplies the exact joint packet needed by `ofBoundaryMonomials`. Corners themselves are not the main problem; simultaneous exact identities and branch elimination are.

---

## 9. Acceptance criterion and non-claims

### Acceptance criterion

The project is complete when, without new axioms:

1. a `WatanabeModificationOn K W` and a nonnegative smooth compactly supported prior inside `W` construct the **normalised smooth prior-weighted core transport with a gap tail**, with no residual atlas-existence hypothesis;
2. composing with `exists_watanabeModificationOn` proves Target A’s existential `HasSmoothCoordFreeExpansion`;
3. the identity-chart regressions cover both zero and nonzero tails.

The project should document explicitly that its “atlas exists” theorem refers to this **support-weighted core-and-tail interface**. An inhabitant of today’s strict `WeightedDomainAtlas` is not the first milestone.

### Non-claims

This does not yet establish:

- a smooth `WeightedDomainAtlas` transporting all unweighted volume on an arbitrary compact target;
- rectification of compact semianalytic domains;
- general joint resolution of phase and boundary functions;
- a global measure-theoretic change-of-variables theorem on hironaka’s resolved manifold;
- global smoothness or analyticity of arbitrary totalised chart maps;
- a general analytic-zero-set-null theorem;
- positivity or nonvanishing of the leading coefficient for signed observables;
- an effective algorithm computing the selected charts or expansion coefficients;
- independence of intermediate atlases or decompositions beyond the existing intrinsic-certificate/uniqueness results.

**Bottom line:** the exact Watanabe export is strong enough geometrically for Target A. The missing bridge is finite, support-weighted Euclidean transport with smooth source representatives—not another phase normalisation theorem, and not a finite-box repair of the current compact-domain atlas interface.
