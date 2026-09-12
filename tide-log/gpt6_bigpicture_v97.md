## Recommendation

**CCCXXIV is a genuine compact-box producer, conditional on uniform normal-series data. It is not yet the analytic-neighbourhood theorem.** The distinction is substantial but accurately acknowledged in your non-claims.

My recommended order is:

1. **Freeze CCCXXIV as the completed series-input producer.**
2. Add a small **closed-face/original-variable adapter**, so the public API also expresses the hypothesis envisaged in #96.
3. Do **one narrowly scoped coordinate compatibility slice**, with an actual constructor and a fixed-germ derivative consumer.
4. **Stop this phase there.** Put 5b in a separate analytic-input phase.

Do not introduce five general compatibility structures before proving a consumer. In particular, neither the collar nor its exact transport requires general SNC compatibility machinery.

I am auditing the declarations and descriptions supplied here, not a checkout of `768f406`; consequently, statements about proof internals, implicit hypotheses, and reducibility below are recommendations rather than independently checked build results.

---

# 1. Audit

## 1.1 What has actually been achieved

The essential construction is now present:

- an exact, parameter-dependent normal transport theorem;
- fixed-side normal cores with the correct density and phase;
- a finite, positive measure decomposition, up to null overlaps;
- a uniform positive phase gap on the complement;
- an embedding of the core bases into the actual coordinate strata;
- identification of the core parametrisations with the chosen tubular maps and frames;
- coefficient and expansion certificates.

This is appreciably more than “the abstract completion theorem applied to assumed cores”: **the cores, measures, frames, collar, and tail gap have been constructed.** The remaining substantial input is the normal analytic data.

The particularly important correctness features are:

- `map_Φ` uses fibrewise transport, so no derivative of `lamT` is being smuggled into a Jacobian.
- The thresholds are proved null for the **transported weighted measure**, not merely asserted to be ambient hypersurfaces.
- `measure_compl_inter_sublevel` is an **almost-everywhere gap**, which is exactly what the integration argument needs.
- The observable jets refer to the **unclamped observable fibre**. The clamping is only a bounded representative for the density.
- The density coefficient family is `J · fϕ`, whereas the observable jet family is `fφ`. Those roles have not been conflated.

These are the right gates.

## 1.2 Bases versus closed faces; normalised versus original variables

Your present `FaceSeries` is mathematically sufficient and a good **low-level producer interface**. It is not literally a family over the closed face, however.

Let
\[
X_I=\{s\in[0,a]^d:s_i=0\text{ for }i\in I\}.
\]
Then your base is a compact subset
\[
B_I^{\mathrm{str}}\subset S_I\cap X_I.
\]
There is no requirement that the producer carry analytic data over the unused portion of \(X_I\). Indeed, requiring only the base is strictly more economical.

Two qualifications:

1. The bases and normalised variables depend on \(\delta\). Thus this is a **collar-adapted series hypothesis**, not a radius hypothesis stated before choosing a collar.
2. The name `FaceSeries` may suggest data over all of \(X_I\). I would document it explicitly as “series over the compact collar base”, or use an alias such as `NormalisedBaseSeries`.

### Add an adapter, not a replacement

Keep the existing interface. Add a public input in the original normal coordinates.

For each nonempty \(I\), use the unscaled insertion
\[
\Psi_I(s,z)=s+\sum_{j\in I}z_{\sigma_I^{-1}j}e_j.
\]
An original-coordinate packet should contain:

```lean
-- Schematic: X I is the subtype of the closed face.
structure OriginalFaceSeries (I : NonemptyIdx d) where
  ρ : ℝ
  hρ : 0 < ρ
  Fϕ : UniformSeriesFamily (X I) (nI I + 1) ρ
  Fφ : UniformSeriesFamily (X I) (nI I + 1) ρ
  hϕ_eq : ∀ s z, ‖z‖ < ρ →
    ϕ (originalNormalMap I s z) = evalF (Fϕ.f s) z
  hφ_eq : ∀ s z, ‖z‖ < ρ →
    φ (originalNormalMap I s z) = evalF (Fφ.f s) z
```

This symmetric identity is convenient for the public adapter; it is stronger than the existing prior identity and need not replace it.

The adapter restricts the parameter to `KI`, then rescales by
```lean
fun s i => lamT k I.1 δ (eI k hk a δ I.1 s) (σI I i)
```
using
\[
L_i=\frac{\delta^{1/(2k_{\sigma_I(i)}d)}}{b_I}.
\]
Your geometry gives
\[
\lambda_i(s)\le L_i,\qquad
2b_I L_i=2\delta^{1/(2k_{\sigma_I(i)}d)}.
\]

Therefore the sufficient radius condition is exactly
\[
2\delta^{1/(2k_i d)}<\rho_I\qquad(i\in I).
\]

Use strict inequalities in this public theorem: they make evaluation inside the original open ball immediate. The summability adapter itself only needs the corresponding non-strict inequality.

A suitable endpoint is:

```lean
noncomputable def OriginalFaceSeries.toFaceSeries
    (A : ∀ I, OriginalFaceSeries ... I)
    (hsmall : ∀ I (i : Nrm I.1),
      2 * δ ^ (((2 * k i.1 * d : ℕ) : ℝ)⁻¹) < (A I).ρ) :
    ∀ I, WaterFilling.FaceSeries k hk a δ ϕ φ I
```

Expect a small parameter-pullback operation for `UniformSeriesFamily` if you do not already have one. This is an API adapter, not 5b.

**Verdict:** acceptable and sufficient now; add the original-variable adapter for the paper-facing public hypothesis.

## 1.3 The two-sided observable identity

The open-ball requirement is right **for the conclusion currently proved**:
```lean
jetFamily n (core.obsFibre s) = D.Fφ.f s
```
where the fibre is the actual ambient function
\[
v\longmapsto \phi(\Phi(s,v)).
\]

A full Fréchet jet at zero is a two-sided germ. Values only in the positive normal box do not establish that the given ambient function has that jet.

There are two legitimate interfaces:

### A. Fixed ambient observable — your current interface

The ambient `φ` must agree with the series on the indicated full normal neighbourhood. This is correct.

### B. Observable on the box, with a chosen analytic extension

Take an extension `φext` and assume
```lean
hφext : Set.EqOn φext φ W
```
or a suitable almost-everywhere equality for the final integral. Apply the producer to `φext`, then transfer the integral.

The coefficient interpretation then concerns the normal jets of `φext`, **not automatically the jets of the originally supplied ambient `φ`**.

Thus:

> The extension can be freely chosen subject to the required analytic/series condition and agreement on the integration domain. It cannot be arbitrary off the box while retaining a theorem about the original ambient jets.

If two analytic normal extensions agree on the positive normal box, their normal germs agree by uniqueness. That is a useful later extension-independence theorem, but it should not be silently built into the present claim.

There is also a deliberate asymmetry worth documenting:

- `hϕ_eq` only identifies a density representative on the integration box;
- `hφ_eq` identifies the actual observable germ on a neighbourhood.

Do not describe both as full ambient analytic-germ hypotheses.

## 1.4 Global nonnegativity of the prior

Global nonnegativity is unnecessarily strong for the integral over \(W\). The natural public assumption is
```lean
∀ w ∈ W, 0 ≤ ϕ w
```
or eventually almost-everywhere nonnegativity with respect to restricted volume.

I would **not refactor the completion theorem merely to improve this application’s signature**. First add a wrapper using
\[
\phi_{\mathrm{prior}}^+(w)=\max(\phi_{\mathrm{prior}}(w),0).
\]

Concretely:

- `ϕ⁺` is measurable and globally nonnegative;
- `ϕ⁺ = ϕ` on \(W\);
- the weighted measures restricted to \(W\) agree;
- `Fϕ` is unchanged, because every positive core box maps into \(W\);
- integrability transfers;
- the observable and its jets are unchanged.

Your weak prior identity makes this especially clean: there is no need for `max ϕ 0` to be analytic outside the box.

The final transfer should state precisely which certificate and coefficient field are used. Do not promise definitional equality with the certificate built under a global nonnegativity proof.

**Verdict:** too narrow as a public hypothesis, but not wrong. A wrapper is the inexpensive correction.

## 1.5 Spectrum and denominator

Keep the current theorem over
```lean
spectrumLe (commonQ cores.k) (commonD cores.n)
```
as the robust internal theorem.

For the companion statement:

- evaluate `commonD = d - 1`;
- either display the evaluated product denominator or explicitly call it “the finite common lattice supplied by the construction”.

Under your stated definition of `commonQ`, the evaluated denominator is
\[
Q=\prod_{\varnothing\ne I\subseteq\{1,\dots,d\}}
      \left(2\prod_{i\in I}k_i\right).
\]
Prove this as an indexing lemma; do not rely on unfolding the chosen enumeration in the final theorem.

The product denominator is valid but not optimal. There are two distinct improvements:

1. **LCM of the existing per-core denominators.**  
   This is the natural improvement to the generic common-lattice construction. It needs divisibility and spectrum-inclusion lemmas for each core.

2. **The coordinate monomial denominator**
   \[
   \operatorname{lcm}_{i}(2k_i).
   \]
   This is the natural denominator suggested by the actual monomial poles. It generally requires a sharper support statement than membership in the existing broad per-core lattices.

Do not confuse these improvements. An expansion on a fine lattice does **not** by itself yield an expansion on a coarser lattice: one must show that the unwanted coefficients vanish.

I would not make optimal denominators a gate for this phase. The log-degree bound \(d-1\) is worth exposing now; optimal rational support is a separate theorem.

## 1.6 Choices, hidden qualifications, and headline corrections

### Choices

`σI` and `coreIdx` are harmless choices for construction and existence. They are not harmless if you claim an already-proved independence theorem for the resulting coefficient field.

Distinguish:

- existence of a certificate using chosen enumerations;
- covariance under reindexing;
- equality of coefficient fields under different frames/collars;
- uniqueness of the resulting integrated asymptotic expansion.

Only the first follows from the supplied construction without further work.

Also, `certificate.stratumMeasure` is the **certificate’s induced stratum measure**, supported on the relevant compact bases. It should not be advertised as a pre-existing canonical measure on each entire coordinate stratum.

### Headline adjustments

I would make these edits:

- CCCXXIV: “general producer from **uniform collar-base normal series**”, followed by the original-face adapter when available.
- “over all nonempty coordinate strata” should read:
  > “a finite sum indexed by all nonempty coordinate strata, with the induced measures supported on their compact collar bases.”
- CCCXXI: generic `Data` contains a tangential embedding; the actual embedding as a subset of the geometric stratum is supplied in CCCXXIV. Say “a compact tangential base”, rather than suggesting the generic structure itself contains a stratum inclusion.
- CCCXXIII: separate the purely measure-theoretic fact from its packaging. Null overlaps and the gap concern any measurable nonnegative prior, but the object named `AnalyticCoreDecomposition` still takes the series input.
- “axiom-clean” is fine as your repository convention. It should not mean that ordinary Lean foundations such as choice have been eliminated.

Finally, audit the fully elaborated public signatures for the typeclass assumptions furnishing compactness, Borel measurability, and finite base measure. The supplied `Data` header alone does not show all assumptions used by `core`. Likewise, do not list `Measurable φ` as an independent explicit argument where it is merely available in the section or not used.

**No mathematical defect is apparent in the construction as described. The main corrections are scope and public-interface clarity.**

---

# 2. The compatibility first slice

## 2.1 What to build first

Build an **exact coordinate specialisation**, not a purported general SNC compatibility object.

I would call it something like:

```lean
CoordinateNormalCompatibility
```

Its job is to connect:

1. the ambient coordinate divisor labels and orders;
2. the normal space and conormals;
3. the chosen frame;
4. the fixed tubular map;
5. the diagonal box parametrisation.

Then derive phase and transport consequences. Do not initially make `MonomialPhaseCompatibility` and `ResolvedDensityCompatibility` into independent bags of hypotheses.

In particular:

- a conormal-frame identity is not an exact transport theorem;
- an infinitesimal conormal identity is not a tubular-map identity;
- phase normalisation is not implied by either;
- in curved geometry, pointwise frame information alone does not compute the tubular Jacobian.

The first slice should make these distinctions visible.

## 2.2 A concrete field list

Here is a self-contained shape, close to compilable Lean. It uses explicit ambient coordinates to avoid guessing your general geometry API.

```lean
open NormalisedBox

structure CoordinateNormalCompatibility
    {d n : ℕ} (k : Fin d → ℕ)
    (I : Finset (Fin d))
    (K : Type*) (N : Type*)
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (base : K → (Fin d → ℝ))
    (e : K → (Tan I → ℝ))
    (inc : N →L[ℝ] (Fin d → ℝ))
    (du : Nrm I → (N →L[ℝ] ℝ))
    (tube : K → N → (Fin d → ℝ))
    (lamT : (Tan I → ℝ) → (Nrm I → ℝ))
    (κ η : Fin (n + 1) → ℕ) where
  label : Fin (n + 1) ≃ Nrm I
  frame : K → ((Fin (n + 1) → ℝ) ≃L[ℝ] N)

  k_eq : ∀ i, κ i = k (label i).1
  h_eq : ∀ i, η i = 0

  base_normal : ∀ s (j : Nrm I), base s j.1 = 0
  base_tangent : ∀ s (j : Tan I), base s j.1 = e s j

  inc_tangent : ∀ ξ (j : Tan I), inc ξ j.1 = 0
  du_coordinate : ∀ ξ (j : Nrm I), du j ξ = inc ξ j.1

  tubular_eq : ∀ s ξ, tube s ξ = base s + inc ξ

  frame_conormal : ∀ s u (j : Nrm I),
    du j (frame s u) =
      lamT (e s) j * u (label.symm j)
```

The associated scale is a definition, not additional redundant data:

```lean
def frameScale (C : CoordinateNormalCompatibility ...) (s : K)
    (i : Fin (n + 1)) : ℝ :=
  lamT (e s) (C.label i)
```

Consequently,
```lean
du (C.label i) (C.frame s (Pi.single j 1))
  = if i = j then C.frameScale s i else 0
```
is a theorem. The diagonal entry is **\(\lambda_i(s)\), not \(1\)**.

If `κ` and `η` are not independently present in the consuming API, make them definitions instead of fields. A field should certify an existing chart’s labels/orders, not manufacture equality between two definitions.

Positivity, continuity, and normalisation belong in the box geometry packet below, not in this algebraic compatibility structure.

### Coordinate verification

For your concrete instance:

- `base s := s.1.1`;
- `N := normalSpace d I`;
- `inc` is the continuous linear subtype inclusion;
- `tube s ξ := normalData.Φ I s.1 ξ`;
- `label := σI I`;
- `frame := frameI ... I`.

Proof sources:

| Field/consequence | Existing source |
|---|---|
| `base_normal` | membership in the coordinate stratum |
| `base_tangent` | definition of `eI` |
| `inc_tangent` | membership in `span {e_i : i ∈ I}` |
| `du_coordinate` | coordinate definition of `du`, or linearity plus `du_apply_basisVec` |
| `tubular_eq` | coordinate `normalData.Φ` |
| `frame_conormal` | `coe_frameI_apply` and `du_coordinate` |
| `k_eq`, `h_eq` | coordinate chart orders and `zeroOrders` |

The basic consumer is then:

```lean
theorem tube_frame_eq_normalisedBox
    (C : CoordinateNormalCompatibility ...) (s : K)
    (u : Fin (n + 1) → ℝ) :
    tube s (C.frame s u) =
      NormalisedBox.Φ I C.label e lamT (s, u)
```

Prove it by ambient-coordinate extensionality and the normal/tangential split.

For the water-filling instance, it should agree with `Φ_eq_frame`. Do not maintain two substantially different proofs.

## 2.3 Phase compatibility should first be a theorem

Derive:

```lean
theorem phase_tube_frame
    (C : CoordinateNormalCompatibility ...) (s : K)
    (u : Fin (n + 1) → ℝ) :
    CoordModel.phase d k (tube s (C.frame s u)) =
      (NormalisedBox.tanUnit k I (e s) *
        ∏ j : Nrm I, lamT (e s) j ^ (2 * k j.1)) *
      ∏ i, u i ^ (2 * κ i)
```

Proof:

1. rewrite by `tube_frame_eq_normalisedBox`;
2. use `phase_Φ`;
3. rewrite `kι` through `k_eq`.

Then, with
```lean
hnorm : ∀ s,
  NormalisedBox.tanUnit k I (e s) *
    ∏ j : Nrm I, lamT (e s) j ^ (2 * k j.1) = β
```
obtain the normal-form identity with coefficient `β`.

For water filling, `tanUnit_mul_prod_lamT` gives `β = 1`.

A later `MonomialPhaseCompatibility` can package these conclusions for a genuinely broader producer. There is no reason to introduce it first here.

## 2.4 Density compatibility should first be derived transport

Similarly, derive the exact measure statement for
```lean
fun p => tube p.1 (C.frame p.1 p.2)
```
by rewriting `map_Φ`.

The density is
\[
J(s)=\prod_{j\in I}\lambda_j(e(s)).
\]

This is a **derived transport theorem**, not an assumed `ResolvedDensityCompatibility` field. In this coordinate instance, `h_eq = 0` explains the absence of an extra exceptional monomial density factor.

For nonzero density orders, the determinant alone would not be the whole transformed density. Do not imply that the present structure covers that case.

## 2.5 The first constructive consumer

Use a geometry packet containing the remaining fields of `NormalisedBox.Data`:

```lean
structure CoordinateBoxBounds ... where
  he : Continuous e
  he_inj : Function.Injective e
  hlamT : Measurable lamT
  hlam_cont : ContinuousOn lamT (Set.range e)
  hpos : ∀ t ∈ Set.range e, ∀ j, 0 < lamT t j

  β : ℝ
  hnorm : ∀ t ∈ Set.range e,
    NormalisedBox.tanUnit k I t *
      ∏ j : Nrm I, lamT t j ^ (2 * k j.1) = β

  b : ℝ
  b' : ℝ
  hb : 0 < b
  hbb' : b < b'
  hW : NormalisedBox.image I e lamT b ⊆ W
```

Take series whose identities are stated **in tubular-frame notation**:

```lean
structure TubularFrameSeries
    (C : CoordinateNormalCompatibility ...)
    (B : CoordinateBoxBounds ...) where
  Fϕ : UniformSeriesFamily K (n + 1) B.b'
  Fφ : UniformSeriesFamily K (n + 1) B.b'

  hϕ_eq : ∀ s, ∀ u ∈ NormalisedBox.box B.b,
    ϕ (tube s (C.frame s u)) = evalF (Fϕ.f s) u

  hφ_eq : ∀ s u, ‖u‖ < B.b' →
    φ (tube s (C.frame s u)) = evalF (Fφ.f s) u
```

The actual bridge is:

```lean
noncomputable def toNormalisedBoxData
    (C : CoordinateNormalCompatibility ...)
    (B : CoordinateBoxBounds ...)
    (A : TubularFrameSeries C B) :
    NormalisedBox.Data k I n K W ϕ φ
```

Its series fields are proved using `tube_frame_eq_normalisedBox`.

Then:

```lean
noncomputable def produceCore_of_coordinateCompat
    -- the existing ambient L/measure/phase/observable hypotheses
    (C : CoordinateNormalCompatibility ...)
    (B : CoordinateBoxBounds ...)
    (A : TubularFrameSeries C B) :
    CorePresentation L
      (L.μ.restrict (NormalisedBox.image I e lamT B.b))
      K n B.β :=
  NormalisedBox.core ... (toNormalisedBoxData C B A)
```

Also expose the resulting `CoreNormalMomentPresentation`.

This is admittedly a thin constructor over CCCXXI, but it is not circular: its inputs contain neither a core, nor a transport proof, nor a normal-form phase proof, nor a coefficient certificate.

**Acceptance test:** instantiate it on the coordinate model, and show that its observable fibre is `φ ∘ tube_s ∘ frame_s`. If the compatibility packet is only attached to an already-built core, this gate has not been met.

## 2.6 The fixed-germ jet consumer

The clean generic theorem is the pointwise multilinear statement:

```lean
theorem iteratedFDeriv_comp_continuousLinearEquiv
    {E N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (F : E ≃L[ℝ] N) (G : N → ℝ)
    (hG : AnalyticAt ℝ G 0)
    (r : ℕ) (v : Fin r → E) :
    iteratedFDeriv ℝ r (fun u => G (F u)) 0 v =
      iteratedFDeriv ℝ r G 0 (fun j => F (v j))
```

The exact proof can use the available iterated-derivative composition API or induction. If finite-order smoothness yields a simpler reusable theorem, use that and derive the analytic corollary. `AnalyticAt` is a convenient sufficient hypothesis, not the minimal one.

For a fixed \(s\), set
\[
G_s(\xi)=\phi(\operatorname{tube}(s,\xi)).
\]
Then obtain
\[
D^r(\operatorname{obsFibre}_s)(0)[v_1,\ldots,v_r]
=
D^rG_s(0)[F_s v_1,\ldots,F_s v_r].
\]

Two important details:

- No derivative in the base variable \(s\) occurs.
- No derivative of `frameScale` occurs: the frame is fixed while differentiating the fibre.

For the present producer, analyticity of `G_s` need not become a new user hypothesis. The series identity gives analyticity of `G_s ∘ frame_s` at zero; composing with `frame_s.symm` gives analyticity of `G_s`.

Finally connect this derivative statement to `jetFamily_obsFibre`. Respect your library’s factorial and multi-index conventions: do not identify coefficients with raw iterated derivatives without the appropriate normalisation.

### Effort

Indicative, not repository-tested:

- compatibility packet, coordinate instance, phase/transport corollaries: **250–500 lines**;
- constructive adapter and concrete consumer checks: **150–300 lines**;
- fixed-germ derivative theorem and coefficient interpretation: **150–350 lines**.

Target **550–1,150 lines**, with a hard scope boundary against general SNC geometry.

---

# 3. The analytic bridge, 5b

## 3.1 The theorem I would ultimately accept

The clean real-analytic theorem is:

> Let \(d>0\), \(a>0\), and \(k_i>0\). Suppose \(\varphi\) and \(\phi\) are real analytic on an open neighbourhood \(U\) of \([0,a]^d\). Then there exists \(\delta>0\), satisfying the collar smallness inequalities, and a `FaceSeries` packet for every nonempty coordinate index set.

Schematically:

```lean
theorem exists_faceSeries_of_analyticOnNhd
    (hd : 0 < d) (ha : 0 < a)
    (hk : ∀ i, 0 < k i)
    {U : Set (Fin d → ℝ)}
    (hU : IsOpen U)
    (hWU : piBox d (Icc 0 a) ⊆ U)
    (hϕ : AnalyticOnNhd ℝ ϕ U)
    (hφ : AnalyticOnNhd ℝ φ U) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, δ ^ ((d : ℝ)⁻¹) < a ^ (2 * k i)) ∧
      Nonempty (∀ I : NonemptyIdx d,
        WaterFilling.FaceSeries k hk a δ ϕ φ I)
```

The `Nonempty` matters because the series packet is data in `Type`, not a proposition.

This bridge itself needs no sign assumption. A theorem producing the expansion then adds nonnegativity on the box and whatever measurability hypotheses the current completion interface still needs. Analyticity near the box also gives continuity and boundedness there, hence the required restricted integrability; it does not control arbitrary values outside the neighbourhood.

## 3.2 Prefer an intermediate conclusion over the closed faces

The most reusable bridge is actually:

\[
\exists \rho>0,\quad
\forall I\ne\varnothing,\quad
\text{uniform original-normal series over }X_I
\text{ at radius }\rho.
\]

For each family require:

- continuous coefficient functions in the face parameter;
- a common nonnegative coefficientwise majorant;
- summability of that majorant at \(\rho\);
- evaluation identities on the open normal ball of radius \(\rho\).

Then choose \(\delta\) afterward so that
\[
\delta^{1/d}<a^{2k_i},
\qquad
2\delta^{1/(2k_i d)}<\rho
\]
for every \(i\). Finiteness and positivity of the exponents give such a \(\delta\).

This separates three facts that should remain separate:

1. analyticity supplies face series;
2. small \(\delta\) makes the collar fit those radii;
3. CCCXXIV supplies the certificate.

It also avoids proving coefficient continuity on moving \(\delta\)-dependent bases.

## 3.3 Cheapest route with your existing infrastructure

Given `AnalyticFamilyData` and `polyRealCoeff`, I would implement the **complex-neighbourhood bridge first**.

A sufficient hypothesis is:

- \(\Omega\subset\mathbb C^d\) open;
- the real box, embedded in \(\mathbb C^d\), lies in \(\Omega\);
- holomorphic extensions \(H_\varphi,H_\phi\) exist on \(\Omega\);
- on its real slice,
  \[
  \varphi(x)=\Re H_\varphi(x),\qquad
  \phi(x)=\Re H_\phi(x).
  \]

Equality on the real slice of the neighbourhood, rather than merely on \(W\), gives the current full-ball observable identity. Equality merely on \(W\) instead gives a theorem for chosen extensions, followed by the integral-transfer wrapper discussed above.

No global uniform bound needs to be assumed:

1. compactness of the embedded box gives a uniform complex neighbourhood inside \(\Omega\);
2. shrink to a compact thickening;
3. continuity gives bounds there.

For a closed face parameter \(s\), consider
\[
z\longmapsto H(s+\operatorname{insert}_I z).
\]
Choose two radii
\[
0<\rho<R
\]
with all the corresponding normal polydiscs of radius \(R\) inside the controlled complex neighbourhood. Uniform Cauchy estimates give
\[
|c_\gamma(s)|\le M R^{-|\gamma|}.
\]
The resulting majorant is summable at \(\rho\):
\[
\sum_{\gamma\in\mathbb N^m}
M(\rho/R)^{|\gamma|}
=
M(1-\rho/R)^{-m}.
\]

Coefficient continuity comes from your analytic-family coefficient construction, or from derivatives/Cauchy integrals varying continuously with the parameter.

**Do not use the Cauchy radius itself as the summability radius.** The strict radius shrink is a real proof obligation.

Apply the original-face adapter to finish.

## 3.4 Why “compactness plus local real expansions” is not a one-page proof

Compactness alone only supplies a finite cover by neighbourhoods with local expansions. The desired family is centred at **each varying face point**. One must additionally establish:

- recentering of local series;
- coefficient continuity in the moving centre;
- coefficientwise uniform majorants;
- summability at a common strictly smaller radius;
- compatibility of coefficients on overlaps.

These are all true. They are also exactly the work that a superficial “take a finite subcover” argument omits.

If the requisite real analytic-family API already exists, the real route can be competitive. From the infrastructure you describe, the complex route has the clearer implementation path.

### Scope and estimated size

- **Complex-neighbourhood to closed-face families**, reusing `AnalyticFamilyData`: roughly **700–1,500 lines**, potentially less if its parameter API already matches compact face subtypes.
- Small-\(\delta\) selection and final bridge wrapper: **100–250 lines**.
- A general **real-analytic-neighbourhood** theorem, including any missing uniformisation/complexification infrastructure: plausibly **1,500–3,500 additional lines**.

A theorem assuming a single enormous polydisc about the origin would be easier but unnecessarily narrow: it would miss the point of local face data. A uniform thin complex neighbourhood of the compact real box is the appropriate target.

---

# 4. Paper-facing paragraph

> **Compact-box expansion from uniform normal series.** Let \(d>0\), \(k_i>0\), \(a>0\), and \(K(w)=\prod_{i=1}^d w_i^{2k_i}\) on \(W=[0,a]^d\). Choose \(\delta>0\) with \(\delta^{1/d}<a^{2k_i}\) for every \(i\). For each nonempty coordinate index set \(I\), form the compact water-filling base in the exact coordinate stratum \(S_I\), with normalised side \(b_I=\delta^{1/(2\sum_{i\in I}k_i)}\) and positive diagonal normal frame determined by the water-filling widths. Suppose the prior and observable admit uniform normal-series families over these bases at radius \(2b_I\), identifying the prior on the positive normal box and the observable on the full open normal ball. For a measurable globally nonnegative prior and a measurable observable integrable against the prior-weighted measure on \(W\), the formalisation constructs a resolved certificate and its coefficient certificate, and proves the associated coordinate-free expansion of \(\int_W\phi(w)\varphi(w)e^{-NK(w)}\,dw\). The coefficient formula is a finite sum indexed by all nonempty coordinate strata, using the certificate’s induced measures supported on their compact collar bases; the complement has phase at least \(\delta\) almost everywhere. The expansion is stated on the construction’s common rational lattice, with logarithmic degree at most \(d-1\). Uniform normal-series families are hypotheses of this theorem; deriving them from analytic-neighbourhood assumptions, and proving general SNC compatibility or independence from certificate choices, are separate results.

After the nonnegativity wrapper, replace “globally nonnegative” by “nonnegative on \(W\)”.

---

# 5. Ranking and stopping point

| Next unit | Value | Indicative size | Recommendation |
|---|---:|---:|---|
| Original-face restriction/rescaling adapter | Very high API value | 150–350 lines | **Do next** |
| Box-local nonnegativity wrapper | High usability | 80–200 lines | Include as polish |
| Coordinate compatibility + constructive consumer + fixed-germ jets | High interpretive value | 550–1,150 lines | **Next substantive slice** |
| `commonD = d - 1`, evaluated product lattice | Moderate, inexpensive | 100–300 lines | Include if straightforward |
| Complex analytic-neighbourhood bridge | Very high user-facing value | 800–1,750 lines | Separate next phase |
| General real analytic bridge | High, infrastructure-heavy | 1,500–3,500+ lines | After complex bridge |
| Optimal spectral support / LCM refinements | Moderate | API-dependent | Defer |
| General SNC/tubular/density compatibility tower | Potentially high, currently diffuse | Several modules | Do not start here |

**Precise stopping gate for this phase:**

1. original-coordinate closed-face input can produce the existing `FaceSeries`;
2. coordinate conormals evaluate the actual diagonal frames with scale \(\lambda_i(s)\);
3. tubular-frame series construct a core without assuming transport or phase normal form;
4. observable derivatives are identified with derivatives of the fixed normal germ through the frame;
5. all four are instantiated on the existing water-filling certificate.

Then stop.

CCCXXIV already justifies a completed milestone. The compatibility slice gives it the missing local geometric interpretation at controlled cost. **5b should be the next named theorem programme, not an unadvertised obligation attached to the claim that the series-input producer has landed.**
