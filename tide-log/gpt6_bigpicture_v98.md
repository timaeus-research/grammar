## Recommendation

Keep CCCXXV unchanged. Add a **radius-parametric Cauchy-to-`UniformSeriesFamily` adapter**, then a **compact complex-neighbourhood producer**, and finally compose it with CCCXXV.

The natural output of the neighbourhood producer is a **common radius**. Per-face radii remain the right general interface for `OriginalFaceSeries`: they admit sharper inputs and already work downstream.

There is one essential logical distinction:

> An identity with the holomorphic extension only on the box does **not** produce `OriginalFaceSeries` for the original globally defined functions. Its evaluation identities inspect points outside the box.

Make that distinction explicit in both the formal API and the paper-facing claim.

---

# 1. Accepted bridge statements

Write
\[
E_{\mathbb R}=\operatorname{Fin}(d)\to\mathbb R,\qquad
E_{\mathbb C}=\operatorname{Fin}(d)\to\mathbb C,
\]
and let
\[
\iota(w)_j=(w_j:\mathbb C),\qquad W=[0,a]^d.
\]

## 1.1 The clean primary hypothesis

I recommend a packet whose content is:

```lean
-- Schematic API: names and namespaces to be chosen locally.
structure HolomorphicBoxExtension
    (a : ℝ) (ϕ φ : (Fin d → ℝ) → ℝ) where
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset : ∀ w ∈ piBox d (Icc 0 a), complexify w ∈ Ω
  Hϕ Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ : ∀ w, complexify w ∈ Ω → ϕ w = (Hϕ (complexify w)).re
  eqφ : ∀ w, complexify w ∈ Ω → φ w = (Hφ (complexify w)).re
```

This asks for agreement on the real slice of the chosen complex neighbourhood—not globally on \(\mathbb R^d\).

The bridge should produce a package, not disconnected facewise existence claims:

```lean
theorem exists_originalFaceSeries_of_holomorphicBoxExtension
    (ha : 0 < a)
    (A : HolomorphicBoxExtension a ϕ φ) :
    ∃ (ρ : ℝ), 0 < ρ ∧
      ∃ O : ∀ I : NonemptyIdx d, OriginalFaceSeries a ϕ φ I,
        ∀ I, (O I).ρ = ρ
```

For convenient downstream use, put this output in a small structure with fields `ρ`, `hρ`, `O`, and `radius_eq`, and provide a noncomputable producer.

**No \(k\), no \(\delta\), and no \(k_i>0\) belong in this theorem.** Strictly speaking, `0 < d` is unnecessary too: when there are no nonempty faces the facewise output is vacuous. Retaining `ha : 0 < a` for consistency with the consumer is harmless, although compactness itself needs no positivity.

## 1.2 Agreement on a separate real neighbourhood

Also provide a wrapper with:

- `V : Set Eℝ`, open;
- `W ⊆ V`;
- agreement with `Re Hϕ` and `Re Hφ` on `V`.

Reduce it to the primary packet by replacing \(\Omega\) with
\[
\Omega'=\Omega\cap\{z:\operatorname{ReVec}(z)\in V\}.
\]
This is open, contains the embedded box, and its real slice lies in \(V\).

Thus “agreement on the real slice of \(\Omega\)” is a **normal form**, not a substantive strengthening of “agreement on some real neighbourhood of the box.”

## 1.3 Box-only agreement: a different theorem

If agreement is known only on \(W\), the correct conclusion is:

1. construct suitable real extensions \(\widetilde\varphi,\widetilde\phi\);
2. produce `OriginalFaceSeries a ϕ̃ φ̃ I`;
3. obtain the expansion for these extensions;
4. transport the box integral—and, with the appropriate theorem, the expansion statement—to the original functions using agreement on \(W\).

You cannot conclude `OriginalFaceSeries a ϕ φ I` for arbitrary original functions.

For example, take \(H=0\), let \(f=0\) on the box, and let \(f=1\) immediately outside a coordinate face. Every positive-radius normal ball samples those exterior values, so no convergent normal series representing this \(f\) can exist.

For this phase, I would make the **real-neighbourhood theorem mandatory** and the box-only extension wrapper optional. The latter requires a clean congruence theorem for the final expansion predicate, not merely a congruence theorem for each Laplace integral.

## 1.4 `Re H` versus complexification

`Re H` is exactly compatible with `polyRealCoeff`; there is no need to assume that \(H\) is real-valued on the real slice.

For the paper, distinguish:

- **formalised input:** real functions represented as real parts of holomorphic functions on a common complex neighbourhood;
- **stronger analytic input theorem:** real analyticity near the compact box supplies such a complex neighbourhood and extensions.

The second statement is mathematically standard, but constructing and gluing complexifications is **not part of the proposed cheap phase** unless separately formalised. Do not title the result simply “real analyticity implies…” while that step remains an assumption.

---

# 2. First unit: arbitrary-radius analytic uniform series

This should be the first unit, independent of coordinate geometry.

## Proposed name

`Grammar/AnalyticUniformSeries.lean`

## Exact mathematical contract

For any topological parameter space \(X\), normal dimension \(m\), and
\[
0<\rho<r<R,\qquad 0\le M,
\]
assume:

- `F : X → (Fin m → ℂ) → ℂ`;
- every `F x` is holomorphic on `openPolydisc m R`;
- joint continuity on `univ ×ˢ closedPolydisc m r`;
- `‖F x z‖ ≤ M` on that set.

Construct
```lean
UniformSeriesFamily X m ρ
```
with
```lean
f x = polyRealCoeff m r (F x)
```
and majorant
\[
M_\gamma=M(r^{-1})^{|\gamma|}.
\]

A suggested signature is:

```lean
noncomputable def analyticUniformSeries
    {X : Type*} [TopologicalSpace X]
    {m : ℕ} {ρ r R M : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hrR : r < R)
    (hM0 : 0 ≤ M)
    (F : X → (Fin m → ℂ) → ℂ)
    (hhol : ∀ x, DifferentiableOn ℂ (F x) (openPolydisc m R))
    (hcont :
      ContinuousOn (fun p : X × (Fin m → ℂ) => F p.1 p.2)
        (univ ×ˢ closedPolydisc m r))
    (hbound : ∀ x, ∀ z ∈ closedPolydisc m r, ‖F x z‖ ≤ M) :
    UniformSeriesFamily X m ρ
```

Export:

```lean
theorem analyticUniformSeries_f ... (x : X) :
    (analyticUniformSeries ...).f x = polyRealCoeff m r (F x)
```

and

```lean
theorem evalF_analyticUniformSeries ... (x : X)
    {u : Fin m → ℝ} (hu : ‖u‖ < ρ) :
    evalF ((analyticUniformSeries ...).f x) u =
      (F x (fun i => (u i : ℂ))).re
```

An additional reconstruction lemma for `‖u‖ < r` is essentially free and useful.

### Proof ingredients

Reuse verbatim:

1. `continuous_polyRealCoeff_param`;
2. `norm_polyCoeff_le`;
3. `evalF_polyRealCoeff_of_lt`.

For the coefficient bound:
\[
|\operatorname{Re} c_\gamma|
 \le \|c_\gamma\|
 \le M(r^{-1})^{|\gamma|}.
\]

For summability:
\[
|M_\gamma|\rho^{|\gamma|}
 =M(\rho/r)^{|\gamma|}
 =M\prod_i(\rho/r)^{\gamma_i}.
\]
Use the existing multivariate geometric summability result underlying `summable_geomMajorant`.

**Do not prove the closed-form sum unless another consumer needs it.** Summability is the entire obligation here.

### What to generalise

Generalise the **weighted geometric summability helper**, not `DataSpace` or `analyticDatum`.

The useful extracted lemma is of the form:

```lean
theorem summable_cauchyMajorant_weight
    (m : ℕ) {ρ r : ℝ}
    (hρ : 0 ≤ ρ) (hρr : ρ < r) (M : ℝ) :
    Summable (fun γ : Fin m → ℕ =>
      |M * (r⁻¹) ^ (∑ i, γ i)| * ρ ^ (∑ i, γ i))
```

Here `hρ` and `hρr` imply `0 < r`.

The current `analyticDatum` interface is deliberately scale \(1\). Do not force original normal variables through that interface by normalising to scale \(1\) and undoing the coefficient rescaling. That adds bookkeeping and obscures the intended coefficients.

In fact, holomorphicity is needed for reconstruction, not for the continuity-and-majorant construction itself. You may split those internally, but one ergonomic constructor with the full hypotheses is perfectly reasonable.

---

# 3. Geometry and compact neighbourhoods

## 3.1 Complex insertion

For each `I : NonemptyIdx d`, set `m := nI I + 1` and define a complex-linear insertion
\[
L_I:\mathbb C^m\longrightarrow\mathbb C^d.
\]

Prefer a reusable `ContinuousLinearMap ℂ` with the coordinate formula
\[
(L_Iz)_j=
\begin{cases}
z_{\sigma_I^{-1}(j)},&j\in I,\\
0,&j\notin I.
\end{cases}
\]

This formula is easier for norm estimates than a sum of standard basis vectors. Prove its equality with the sum formulation once if needed.

Required API:

1. selected-coordinate formula;
2. outside-coordinate formula;
3. `‖L_I z‖ ≤ ‖z‖`;
4. continuity and complex differentiability, supplied by the CLM;
5. compatibility with real insertion:
   \[
   \iota(\operatorname{originalNormalMap}(I,s,u))
   =\iota(s)+L_I(\iota(u)).
   \]

Only the inequality in item 3 is needed. An isometry theorem is optional.

**Important:** the default norm on `Fin d → ℂ` is the finite-product sup norm. Consequently, insertion has norm at most \(1\), with no factor of \(d\), \(\sqrt d\), or \(|I|\).

Do not accidentally move this construction into `EuclideanSpace`.

## 3.2 Compact faces

Prove:

```lean
isCompact_faceSet :
    IsCompact (faceSet a I)
```

by expressing the face as the compact box intersected with finitely many closed coordinate-zero conditions.

For
```lean
X := ↥(faceSet a I)
```
the topology is already the correct subtype topology. Its inclusion into the ambient real space is continuous. When a compact-space instance is useful, install it locally from `isCompact_faceSet`.

Do not require users to supply a global instance for every face, and do not replace the closed face by the relative open stratum.

## 3.3 Uniform ambient buffer

Let \(K=\iota(W)\), a compact subset of \(E_{\mathbb C}\). From \(K\subseteq\Omega\) and openness, obtain \(\varepsilon>0\) such that the open \(\varepsilon\)-thickening of \(K\) lies in \(\Omega\).

Then choose, for example,
\[
R=\varepsilon/2,\qquad r=\varepsilon/4,\qquad \rho=\varepsilon/8.
\]

This deliberately leaves three gaps:

- ambient buffer versus closed \(R\)-tube;
- holomorphic normal radius \(R\) versus Cauchy radius \(r\);
- Cauchy radius \(r\) versus summability radius \(\rho\).

These fixed fractions are not mathematically significant. They make strict inequalities mechanical.

A particularly useful local geometric lemma is:

```lean
theorem exists_uniform_complex_box_buffer
    (hΩ : IsOpen Ω)
    (hWΩ : ∀ w ∈ W, complexify w ∈ Ω) :
    ∃ R > 0,
      ∀ w ∈ W, ∀ z : Fin d → ℂ,
        ‖z‖ ≤ R → complexify w + z ∈ Ω
```

Prove it once using thickening and a radius shrink. All facewise neighbourhood statements then follow from the insertion norm bound.

## 3.4 Uniform bounds

Use the compact ambient tube
\[
T_R=\{\iota(w)+v:w\in W,\ \|v\|\le R\}.
\]
It is a continuous image of a product of compact sets and lies in \(\Omega\).

Holomorphicity on the open set gives continuity there; restricting to \(T_R\) gives boundedness. Obtain separate nonnegative bounds \(M_\varphi,M_\phi\), or take their maximum.

This route gives:

- one radius for all faces;
- optionally one bound for all faces;
- no finite minimisation over dependent face dimensions.

It also avoids proving compactness of a union of facewise polydiscs. That alternative works, but the ambient tube is cleaner.

---

# 4. The facewise family and exact proof sequence

For fixed `I`, define
```lean
G : ↥(faceSet a I.1) → (Fin (nI I + 1) → ℂ) → ℂ :=
  fun s z => H (complexify s.1 + complexInsert I z)
```

Yes: **this is exactly the right recentering**, and it lets you reuse `PolyCoeffParam` verbatim.

Prove the following in order.

### Lemma A: image containment

For `s ∈ faceSet a I.1` and `z ∈ closedPolydisc m R`,
\[
\iota(s)+L_Iz\in\Omega.
\]

Use:

- `s` lies in the box;
- coordinate bounds imply `‖z‖ ≤ R`;
- insertion is norm-nonincreasing;
- the uniform buffer.

Use the analogous containment for `openPolydisc m R` when proving holomorphicity.

### Lemma B: holomorphicity in the normal variable

```lean
∀ s, DifferentiableOn ℂ (G s) (openPolydisc m R)
```

The affine map `z ↦ complexify s.1 + complexInsert I z` is complex differentiable. Compose it with `H`.

Because \(\Omega\) is open, `DifferentiableOn ℂ H Ω` gives ordinary differentiability at each image point. Either use that pointwise route or the `DifferentiableOn.comp` route with the explicit `MapsTo` proof.

### Lemma C: joint continuity

```lean
ContinuousOn
  (fun p : X × (Fin m → ℂ) => G p.1 p.2)
  (univ ×ˢ closedPolydisc m r)
```

The inner map is globally continuous:

- subtype inclusion;
- coordinatewise complexification;
- complex insertion;
- addition.

Compose with `ContinuousOn H Ω`, using image containment. Recentering creates no new integral theorem.

### Lemma D: uniform bound

```lean
∀ s, ∀ z ∈ closedPolydisc m r, ‖G s z‖ ≤ M
```

The image lies in `T_R`, since `r < R`.

### Lemma E: uniform coefficient family

Apply `analyticUniformSeries` at \(\rho<r<R\). Its coefficients are exactly
```lean
polyRealCoeff m r (G s)
```
in the **original** normal coordinates.

### Lemma F: evaluation for the original real function

For real `u` with `‖u‖ < ρ`:

1. each complexified coordinate has norm less than `r`;
2. reconstruction gives
   \[
   \operatorname{evalF}(f_s,u)
   =\operatorname{Re}H(\iota(s)+L_I\iota(u));
   \]
3. real-insertion compatibility identifies the argument with
   \[
   \iota(\operatorname{originalNormalMap}(I,s,u));
   \]
4. image containment permits the real-slice identity;
5. reverse the equality to match `OriginalFaceSeries.hϕ_eq`.

Repeat for the observable, using the same radii, and package `OriginalFaceSeries` with `ρ := ρ`.

No differentiation in `s`, no tangential analyticity, and no compatibility of coefficients across different faces is required.

---

# 5. Mathlib inventory and boundaries

The following are the relevant routes. I would check exact signatures in the pinned Mathlib version rather than design the implementation around guessed argument order.

| Obligation | Route |
|---|---|
| Compact box | finite products of compact intervals |
| Compact embedded box | `IsCompact.image` and continuous complexification |
| Compact face | compact box intersected with closed coordinate conditions |
| Compact complex ball | properness of finite-dimensional complex normed spaces; compact closed balls |
| Uniform neighbourhood | `IsCompact.exists_thickening_subset_open`, or its available neighbourhood variant |
| Closed buffer from open thickening | choose a strictly smaller radius |
| Holomorphic implies continuous | `DifferentiableOn.continuousOn` |
| Composition | `DifferentiableOn.comp`, or differentiability at points of an open domain |
| Compact uniform bound | `IsCompact.exists_bound_of_continuousOn`, or boundedness of the compact image |
| Joint continuity | product projections, subtype inclusion, finite-coordinate continuity, CLM continuity |
| Sup-norm bounds | finite-product norm lemmas such as the `norm_le_pi_norm` / `pi_norm_le_iff` family |
| Small-\(\delta\) choice | positive-power limits at zero, finite intersections of eventual conditions |

Two implementation cautions:

1. **Check what the thickening theorem actually supplies.** An open thickening bound at radius \(\varepsilon\) does not immediately contain closed balls of radius \(\varepsilon\). Shrink before using closed Cauchy contours.
2. **The real-slice identity is an assumption**, not a consequence of holomorphicity. The theorem proves containment that makes this assumption applicable.

For multivariable Cauchy theory, your existing Grammar results carry the load. There is no reason to search for a replacement Mathlib polydisc coefficient API.

`norm_polyCoeff_le`, applied to the bound restricted to the torus, is sufficient. The new work is entirely:

- uniform geometric containment;
- parameter continuity through recentering;
- weighted summability at \(\rho<r\).

---

# 6. Small-\(\delta\) selection

Keep this separate from complex analysis.

The target statement should use the **literal exponent expressions in CCCXXV**, avoiding an additional coercion-and-exponent conversion at the consumer:

```lean
theorem exists_small_delta
    (hd : 0 < d) (ha : 0 < a)
    (hk : ∀ i, 0 < k i)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      (∀ i,
        2 * δ ^
          ((d : ℝ)⁻¹ * ((2 * k i : ℕ) : ℝ)⁻¹) < ρ)
```

I recommend the limit proof:

- every exponent is positive;
- each corresponding positive power tends to zero as \(\delta\to0^+\);
- every target bound is positive;
- there are finitely many coordinates;
- choose one positive \(\delta\) satisfying their intersection.

An explicit construction via \(\delta=t^d\) is valid, but generally incurs more `rpow`/natural-power algebra.

A stronger “all sufficiently small positive \(\delta\)” theorem is often more useful; derive existence from it.

For common-radius data, the facewise smallness condition follows simply by specialising the coordinate inequality to `(σI I i).1` and rewriting `radius_eq`.

---

# 7. Unit breakdown and gates

A realistic decomposition is:

| Unit | Content | Estimated lines | Gate |
|---|---|---:|---|
| 1. `AnalyticUniformSeries` | weighted geometric helper; arbitrary-radius constructor; reconstruction | 200–350 | Works for arbitrary `X`, `m`, and `0 < ρ < r < R`, without compactness |
| 2. `ComplexNormalInsertion` | complexification, insertion CLM, norm bound, real compatibility, face compactness | 200–400 | Exact cast identity with the existing `originalNormalMap` |
| 3. `HolomorphicBoxBuffer` | compact embedded box, uniform buffer, compact tube, uniform bounds | 200–350 | One ambient radius and bounds independent of `I` |
| 4. `HolomorphicOriginalFaceSeries` | recentered family; holomorphicity, continuity, bounds; common-radius producer | 300–500 | Produces the unchanged `OriginalFaceSeries` including exterior-point evaluation |
| 5. `AnalyticCoordinateBoxExpansion` | small-\(\delta\) lemma; composition with CCCXXV; box-local nonnegativity wrapper | 200–400 | Final expansion with the actual produced certificate and coefficient field |

Expected total: **roughly 1,100–2,000 lines**, with five reviewable units. The main uncertainty is API/coercion work in units 2–3, not new analysis. For someone fluent in the existing files, budget approximately **one to two focused weeks**, rather than treating the entire bridge as a single short adapter.

The optional box-only extension/congruence wrapper and any theorem constructing complexifications from real analyticity are outside that estimate.

## Final programme theorem

The primary theorem should retain the existing measure-theoretic hypotheses and say:

> Given holomorphic extensions on a complex neighbourhood of the embedded compact box, agreeing with the prior and observable on its real slice, and the existing measurability, integrability, and nonnegativity assumptions, the compact-box coordinate model admits the coordinate-free expansion for every sufficiently small positive collar parameter \(\delta\), with the stratum measure and coefficient field of the certificates constructed from these extensions.

Provide two versions:

1. global nonnegative prior: compose with `hasCoordFreeExpansion_collar_of_face`;
2. box-local nonnegative prior: first produce the original face series, then `toFaceSeries`, then use `hasCoordFreeExpansion_collar_of_nonneg_on`.

**Do not attempt to holomorphically extend `posPart ϕ`.** The existing positive-part adapter belongs *after* restriction to the collar series, exactly as CCCXXV currently arranges it.

Also, analyticity near the box does not imply global measurability of arbitrary values assigned outside that neighbourhood. Retaining CCCXXV’s global `Measurable` assumptions is the cheapest honest theorem. Removing them requires a separate local-measure or measurable-extension adapter.

No change to `OriginalFaceSeries.ρ` is needed.

---

# 8. Honesty audit

## CCCXXV

The supplied row is appropriately scoped. It expressly marks the analytic-neighbourhood bridge as separate.

One point to preserve in future summaries is:

> The positive-part theorem uses the certificate and coefficient field of the positive-part prior, while asserting the expansion for the original box integral.

Your row already says this. Do not later shorten it to “the positive part has the same original normal series.” That need not hold outside the box.

## CCCXXVI

The supplied row is also appropriately qualified:

- coordinate model, not general SNC;
- fixed straight tubular germ;
- frame scale \(\lambda_i\), not unit conormal pairing;
- no base or frame-scale differentiation in the normal-jet comparison.

I see no mathematical overclaim in the supplied wording. The essential qualification is the **chosen tubular germ**: higher “normal differentials” here must continue to mean derivatives of that fixed normal germ, not an unqualified intrinsic higher normal derivative independent of tubular choices.

## Paper-facing sentence after this phase

I would use:

> For priors and observables admitting holomorphic extensions to a complex neighbourhood of the closed coordinate box, agreeing with the real functions on a real neighbourhood of the box, compactness and Cauchy estimates produce uniform convergent normal series over every closed face at a common positive radius. After choosing the collar parameter sufficiently small, these series feed the compact-box producer and yield its coordinate-free expansion with stratum-integral coefficients; the chart jets are the normal differentials of the fixed straight tubular germs evaluated along the prescribed frames.

Add separately:

> The construction of a common holomorphic extension from purely real-analytic hypotheses is not included in this bridge.

That is the precise stopping gate: **complex neighbourhood → unchanged closed-face series interface → existing certificates and expansion**, with no new claim about general SNC geometry or complexification theory.
