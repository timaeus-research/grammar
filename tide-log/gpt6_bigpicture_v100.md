## Recommendation

**G should end with a single `HasCoordFreeExpansion` on the signed box, obtained by transporting expansions—not certificates.** Keep the finite-sum expansion as an intermediate theorem.

There is one important correction to the proposed assembly:

> Reflected bases are disjoint for different signs **off** \(I\), but generally overlap for different signs **on** \(I\). Thus full-sign piecewise gluing does not work.

I recommend a finite **dominated-measure assembly** lemma: sum the pushed-forward measures and weight the transported moment fields by their Radon–Nikodym densities relative to that sum. This handles the overlap without changing the geometry or constructing a reflected certificate.

The main prerequisite to audit immediately is whether the coefficient certificates already expose:

1. a.e. summability of the normal-order series;
2. integrability of its pointwise sum.

Both are needed for this assembly; `HasCoordFreeExpansion` alone does not supply them.

---

## 1. The target API

### Signed analytic packet

Add the direct signed analogue of the existing packet:

```lean
structure HolomorphicSignedBoxExtension
    (a : ℝ) (ϕ φ : (Fin d → ℝ) → ℝ) where
  Ω : Set (Fin d → ℂ)
  isOpen_Ω : IsOpen Ω
  box_subset :
    ∀ w ∈ piBox d (Icc (-a) a), complexify w ∈ Ω
  Hϕ : (Fin d → ℂ) → ℂ
  Hφ : (Fin d → ℂ) → ℂ
  holϕ : DifferentiableOn ℂ Hϕ Ω
  holφ : DifferentiableOn ℂ Hφ Ω
  eqϕ :
    ∀ w, complexify w ∈ Ω →
      ϕ w = (Hϕ (complexify w)).re
  eqφ :
    ∀ w, complexify w ∈ Ω →
      φ w = (Hφ (complexify w)).re
```

A generic “holomorphic extension near a set” packet would also work, but **do not make refactoring the existing packet a prerequisite for G**.

### Main theorem

Normalize the coordinate spectrum first, with a named `coordCommonQ k`. Then the public existential theorem should have this shape:

```lean
theorem hasCoordFreeExpansion_of_holomorphicSignedBoxExtension_local
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (A : HolomorphicSignedBoxExtension a ϕ φ)
    (hd : 0 < d) (ha : 0 < a)
    (hϕ0W : ∀ w ∈ piBox d (Icc (-a) a), 0 ≤ ϕ w) :
    ∃ (ν : ∀ I : Finset (Fin d),
          Measure ((geometry d k (zeroOrders d) hk).Stratum I))
      (B : (normalData d k (zeroOrders d) hk).MomentCoefficientField),
      (normalData d k (zeroOrders d) hk).HasCoordFreeExpansion
        ν B
        (spectrumLe (coordCommonQ k) (d - 1))
        (piBox d (Icc (-a) a))
        (phase d k) ϕ φ
```

Also expose named outputs, for example:

```lean
signedStratumMeasure k hk A hd ha hϕ0W
signedMomentField    k hk A hd ha hϕ0W
```

and prove the main theorem directly for those outputs. The existential version is then a convenience corollary.

Accompany these outputs with:

* `IsFiniteMeasure (signedStratumMeasure ... I)`;
* a.e. support in the signed box;
* the defining finite-sum identity for the measures;
* the finite-sum identity for expansion coefficients.

The last identity is a central public specification:

\[
C_{\mathrm{signed}}(\phi,q)
  =\sum_{\varepsilon} C_{\varepsilon}(\phi\circ R_\varepsilon,q).
\]

Do **not** call the assembled object a `ResolvedCertificate`: no such structure has been constructed.

### Collar choices

There is no need to expose a single signed collar parameter. Choose one positive-box output for each reflection. A finite family of possibly different \(\delta_\varepsilon\) is sufficient.

Package these choices once, or use named choice definitions. Do not repeatedly reconstruct certificate terms with different proof arguments.

### The common spectrum

Your reading is correct **provided the produced cores use the same fixed chart indexing and exponent family for every packet**, as the construction description indicates.

However, `commonQ` is a product over the **indexed family of cores**, not merely an operation on the set of values \(\{k_i\}\). Repeating charts can change that product.

The right normalization lemma is therefore:

```lean
theorem producedCertificate_commonQ :
    commonQ (producedCertificate ...).cores.k = coordCommonQ k
```

Prove it from the actual fixed core exponent family, before assembling reflections. The supplied `commonQ` definition alone does not establish this equality.

Once normalized, use the existing spectrum unchanged. There is no need to enlarge it by taking a product of the denominators of the reflected copies.

---

## 2. The overlap issue—and its correct resolution

For a stratum \(S_I\), put

\[
O_{I,\eta}
 =\{s\in S_I:\operatorname{sign}(s_i)=\eta_i\text{ for }i\notin I\}.
\]

These are measurable, pairwise disjoint sign chambers of the stratum. Since positive-box bases have \(s_i>0\) for \(i\notin I\), reflected bases with distinct off-\(I\) sign patterns are indeed disjoint.

But for fixed \(\eta\), there are \(2^{|I|}\) full reflections extending it. Their actions on the base points coincide in the \(I\)-coordinates, because those coordinates are zero. Their actions on the **normal directions** do not coincide.

At the deepest stratum \(I=\mathrm{univ}\), all \(2^d\) reflected measures live at the same point.

Consequently:

* selecting a full reflection from the sign of \(s\) loses normal-side contributions;
* summing fields while also summing measures introduces unwanted cross-terms;
* ambient Lebesgue-nullness of the divisors is irrelevant to this problem—the coefficient measures deliberately live on those divisors.

### Recommended assembly

Write the transported data as

\[
\mu_{\varepsilon,I}=(R_{\varepsilon,I})_*\nu_{\varepsilon,I},
\qquad C_{\varepsilon,I,r,q}(s).
\]

Define

\[
\nu_I=\sum_\varepsilon\mu_{\varepsilon,I}.
\]

Every \(\mu_{\varepsilon,I}\le\nu_I\). Let

\[
w_{\varepsilon,I}
  =\frac{d\mu_{\varepsilon,I}}{d\nu_I},
\]

using real-valued representatives of these densities, and set

\[
B_{I,r,q}(s)
  =\sum_\varepsilon
      w_{\varepsilon,I}(s)\,
      C_{\varepsilon,I,r,q}(s).
\]

This is a finite sum in the **same moment-tensor fiber at \(s\)**. It is valid even for dependent normal bundles; no tensors at different points are added.

For finite measures, the RN route is standard. Here one also has \(0\le w_{\varepsilon,I}\le1\) a.e. and \(\sum_\varepsilon w_{\varepsilon,I}=1\) a.e. The construction is an averaged field relative to the summed measure—not an unweighted sum of fields.

### A possible optimization, but not a starting assumption

If an audit proves that, after choosing a common collar, all normal-sign variants have the same stratum measure within each off-\(I\) sign chamber, then ordinary finite averaging can replace RN derivatives there.

That could be cheaper. But it requires a real theorem about the measures, their dependence on the prior, and their dependence on the collar. The snippets supplied do not establish it. I would not design G around that unverified equality.

---

## 3. Assembly lemmas: separate the three layers

### A. Pure finite asymptotic assembly

First prove a lemma independent of moment fields:

* each \(L_\varepsilon\) has expansion coefficients \(c_\varepsilon\) on the same `spec`;
* eventually,
  \[
  L(n)=\sum_\varepsilon L_\varepsilon(n);
  \]
* define \(c(q)=\sum_\varepsilon c_\varepsilon(q)\).

Then \(L\) has the corresponding expansion.

The proof is just finite rearrangement and a finite sum of `IsLittleO`s.

This is useful on its own and isolates asymptotics from measure theory.

### B. Spatial gluing with a compatible field

A clean general disjoint-support lemma does exist. A slightly more general and simpler formulation uses an already-supplied field \(B\):

* finitely many measures \(\mu_e\);
* fields \(B_e\);
* for every \(e,I\), \(B=B_e\), in every degree and index, \(\mu_{e,I}\)-a.e.;
* the scalar coefficient-series functions are integrable.

Then

\[
C_{\sum_e\mu_e,B}(\phi,q)
   =\sum_e C_{\mu_e,B_e}(\phi,q).
\]

Measurable pairwise-disjoint support sets are one way to construct such a compatible \(B\). A finite sum of indicator-weighted fields is convenient; `Set.piecewise` is also fine.

This lemma needs **no interchange of a finite sum with `tsum`**, because field compatibility gives equality term by term under each component measure.

It is useful infrastructure, but **does not solve G’s normal-sign overlaps**.

### C. Dominated-field assembly

For RN-weighted assembly, additionally require, for each \(e,I,q\),

```lean
∀ᵐ s ∂μ e I,
  Summable (fun r =>
    (r.factorial : ℝ)⁻¹ *
      (B e I r q s).pair (D.normalDifferential φ I s r))
```

and integrability of the pointwise sum.

The intended calculation is

\[
\begin{aligned}
\sum_r \langle J_r,B_r\rangle/r!
 &=\sum_e w_e\sum_r\langle J_r,B_{e,r}\rangle/r!,\\
\int \sum_e w_e F_e\,d\nu
 &=\sum_e\int F_e\,d\mu_e.
\end{aligned}
\]

The a.e. summability assumption is essential: Lean’s `tsum` is totalized, and arbitrary nonsummable series cannot be distributed through finite sums.

When transferring component-a.e. facts to \(\nu\), use them on \(\{w_e\ne0\}\); where \(w_e=0\), the weighted series is identically zero. One must not claim a \(\mu_e\)-a.e. property holds \(\nu\)-a.e. without this qualification.

### Integral decomposition hypotheses

For the domain pieces \(W_e\), use:

* measurable pieces;
* coverage modulo ambient measure zero;
* pairwise ambient-null intersections;
* integrability of each Laplace integrand, at least eventually in the parameter.

`HasCoordFreeExpansion` alone does not imply these analytic integrability hypotheses. Totalized Bochner integrals make a bare “expansions on pieces imply expansion on union” lemma false without appropriate assumptions.

For G, compactness and the local analytic packet give the required integrability for every real parameter \(n\).

---

## 4. Reflection transport: expansions, not certificates

Use a finite sign type such as:

```lean
abbrev CoordSign (d : ℕ) := Fin d → Bool
```

with a fixed interpretation as \(\pm1\). Reuse `signReflect`; do not create a competing reflection implementation.

For each sign:

1. a continuous linear equivalence on `Fin d → ℝ`;
2. a measurable equivalence \(R_{\varepsilon,I}:S_I\simeq_m S_I\);
3. a linear isometric equivalence
   \[
   L_{\varepsilon,I}:N_I\simeq_{\mathrm{li}}N_I.
   \]

The constancy of `normalData.N I s` in \(s\) is a substantial advantage.

### Domain integral

Prove

\[
\int_{R_\varepsilon W} f(w)\,dw
  =\int_W f(R_\varepsilon u)\,du.
\]

Since the phase is coordinatewise even,

\[
K(R_\varepsilon u)=K(u),
\]

hence

\[
L_{R_\varepsilon W}(K,\phi\varphi)
 =L_W(K,(\phi\circ R_\varepsilon)(\varphi\circ R_\varepsilon)).
\]

### Tubular compatibility

The geometric identity underlying the jet proof is

\[
R_\varepsilon(\Phi_I(s,v))
 =\Phi_I(R_{\varepsilon,I}s,L_{\varepsilon,I}v).
\]

Prove this directly by coordinate extensionality.

### Jet pullback

Define the continuous linear operator on jet forms

\[
P_{\varepsilon,I,r}(J)
   =J\circ(L_{\varepsilon,I},\ldots,L_{\varepsilon,I}).
\]

For \(\psi=\phi\circ R_\varepsilon\),

\[
J^r_\perp\psi(s)
  =P_{\varepsilon,I,r}
       \bigl(J^r_\perp\phi(R_{\varepsilon,I}s)\bigr).
\]

Because the reflection is involutive, this is equivalent to the identity in your question.

For G, it suffices to prove this at points where \(\phi\) is smooth in a neighborhood of the reflected base point. The signed analytic packet supplies this a.e. on the measures. Do not begin by proving the most general naturality theorem for arbitrary totalized iterated derivatives under arbitrary continuous linear maps.

### Moment pushforward

For \(t=R_{\varepsilon,I}s\), define

\[
C_{\varepsilon,I,r,q}(t)
   =B_{\varepsilon,I,r,q}(s)\circ P_{\varepsilon,I,r}.
\]

Then

\[
C_{\varepsilon,I,r,q}(R_{\varepsilon,I}s)
       \bigl(J^r_\perp\phi(R_{\varepsilon,I}s)\bigr)
 =
B_{\varepsilon,I,r,q}(s)
       \bigl(J^r_\perp(\phi\circ R_\varepsilon)(s)\bigr).
\]

This pairing identity is the best rewrite theorem for downstream proofs.

### Stratum integral

Finally use

\[
\int g\,d((R_{\varepsilon,I})_*\nu_I)
 =\int g(R_{\varepsilon,I}s)\,d\nu_I.
\]

Prove transport first for the **whole scalar normal-order series**. There is no reason to exchange its `tsum` with the stratum integral.

Package transport of:

* the expansion;
* a.e. series summability;
* integrability of the summed series;
* support in the reflected box.

These are all lightweight facts about the produced data, not a reflected certificate.

---

## 5. Pulling back the analytic packet

For the complex-linear reflection \(R^\mathbb C_\varepsilon\), take

\[
\Omega_\varepsilon=(R^\mathbb C_\varepsilon)^{-1}\Omega,
\qquad
H_{\varphi,\varepsilon}=H_\varphi\circ R^\mathbb C_\varepsilon,
\qquad
H_{\phi,\varepsilon}=H_\phi\circ R^\mathbb C_\varepsilon.
\]

The proof uses:

* continuity of the complex reflection for openness;
* \(R_\varepsilon[0,a]^d\subseteq[-a,a]^d\);
* `complexify` commuting with reflection;
* holomorphic composition.

This is routine, but package it as a named definition and prove its field identities once.

**No new `posPart` argument is needed in G.** Nonnegativity pulls back from the signed box, and CCCXXXIV handles representatives and positive parts internally.

The commuting identity for `posPart` is a harmless one-line convenience lemma, not part of the signed theorem’s conceptual proof.

For coefficient regularity, transfer the positive producer’s summability and integrability from its observable representative to the original observable using the a.e. germ equality already established in the hygiene phase.

---

## 6. Mathlib routes

I would use the following routes; exact theorem names beyond those supplied should be checked against the pinned Mathlib version.

### Reflection and volume

**Reuse `map_signReflect_volume`.** The determinant/Haar work has already been done.

Add wrappers for:

* the measurable equivalence;
* measure preservation;
* restricted-measure transport;
* set-integral change of variables.

There is no reason to reopen `map_pi` or the general Haar determinant API for this phase.

Be careful about norms:

* `Fin d → ℝ` has its ordinary function-space norm;
* `Amb d` is `EuclideanSpace`, with the \(L^2\) norm.

Use separate diagonal reflections on these spaces, joined by coordinate identities. Do not accidentally assert that the ordinary coordinate identification is a linear isometry.

### Hyperplane-null overlaps

Two robust routes:

1. finite-product/Fubini reasoning using the singleton-null coordinate;
2. the proper-subspace-null theorem for finite-dimensional additive Haar measure.

If global coordinate-hyperplane nullness is awkward, prove nullness inside the bounded signed box using a rectangle with one singleton coordinate. That is enough for G.

Prove once:

```lean
∀ᵐ w ∂volume,
  ∀ i, w i ≠ 0
```

and use it to show unique orthant membership a.e.

The integral decomposition can then be proved through a.e. indicator identities and finite integral additivity. This is often simpler than iterated `setIntegral_union`.

### Finite sums

Use the finite-sum lemmas in `Asymptotics.IsLittleO`, or induction with `.add`. The asymptotic part should be small.

### Jets

Search the `iteratedFDeriv` composition API, especially the already-used `iteratedFDerivWithin_comp_right`. If necessary:

* establish local `ContDiff`;
* use the within theorem on an open neighborhood or `univ`;
* rewrite the reflection/translation compatibility.

Make `JetForm` pullback a named continuous linear operator. Its continuity is needed to compose it with a `MomentTensor`; a pointwise multilinear formula alone is insufficient.

### RN assembly

Use:

* absolute continuity from \(\mu_e\le\sum_e\mu_e\);
* `Measure.rnDeriv`;
* reconstruction by `withDensity`;
* the real-valued `withDensity` integral formula;
* finite measure-integral additivity.

Prove a scalar weighted-integral helper first. Keep ENNReal-to-real conversion details out of the moment-field proof.

Also, “the field is measurable” is not currently a field of `MomentCoefficientField`. State and prove the measurability actually used: the scalar paired series, or paired terms where needed. Piecewise construction does not establish regularity of the constituent fields.

---

## 7. Six-unit plan

These are logical units, not necessarily one file each.

| Unit | Deliverable | Dependencies | Size/risk |
|---|---|---|---|
| **G1 — Signs and signed packets** | Finite sign API, real/complex reflection wrappers, signed packet, positive pullbacks, spectrum normalization | Existing reflection and analytic packet modules | Small–medium |
| **G2 — Orthant integral decomposition** | Signed-box cover, null overlaps, Laplace integral finite-sum identity | G1 | Medium |
| **G3 — Normal reflection transport** | Stratum equivalences, normal isometries, jet pullback operator, pairing identity, measure/coefficient/expansion transport | G1; existing normal data | Medium–large |
| **G4 — Finite coefficient assembly** | Pure asymptotic lemma, scalar RN integration helper, dominated-field assembly | General measure/jet API | Largest risk |
| **G5 — Positive-output regularity interface** | A.e. summability and summed-series integrability for produced outputs and original observables; reflected versions | Hygiene, coefficient certificate API, G3 | Small if already exposed; otherwise medium–large |
| **G6 — Signed producer and examples** | Named choices and assembled data, signed theorem, support/finite-measure/coefficient-sum specs, polynomial corollary and tests | G1–G5 | Medium |

**Execution order:** do a short G5 audit first, then G1; prototype the scalar RN helper early. Those two checks determine the real cost. The finite asymptotics and complex packet pullback are not the schedule risks.

Do not spend time making the collar common unless the equal-measure optimization has first been verified.

### Kernel hygiene

Continue the landed convention:

* named proof constants in data-valued constructors;
* named chosen positive outputs;
* named normal reflection maps and jet pullback maps;
* theorem-level rewriting for spectrum normalization;
* no large certificate comparisons through proof-valued casts.

In particular, normalize the spectrum by a proposition-level rewrite, not by rebuilding a certificate with transported proof arguments.

---

## 8. Stopping gate

G is complete when all of the following are axiom-clean:

1. **Public signed local-input theorem:** only the signed holomorphic packet, `hd`, `ha`, and prior nonnegativity on the signed box.
2. **One measure family and one moment field** on the existing full coordinate strata.
3. **Exact measure specification**
   \[
   \nu_I=\sum_\varepsilon(R_{\varepsilon,I})_*\nu_{\varepsilon,I}.
   \]
4. **Exact coefficient-sum specification** on the common coordinate spectrum.
5. **Finite measures and signed-box a.e. support.**
6. **No hidden global measurability or global nonnegativity requirements.**
7. **Regression checks exercising the overlap**, not merely the integral cover:
   * \(d=1\), where both normal sides meet at the origin;
   * a crossing stratum in \(d=2\);
   * a reflection-sensitive jet or moment test, so omitting the normal sign action would fail.
8. A signed polynomial instance requiring nonnegativity only on the signed box.

A sum-of-expansions theorem alone is a useful milestone, but it does **not** meet this stopping gate.

---

## 9. What the paper may claim

I cannot determine the paper’s exact intended statement from these excerpts, but the mathematically justified endpoint is:

> The coordinate-free expansion is established for the two-sided coordinate normal-crossings model on a signed box, with analytic prior and observable, an even monomial phase, and a prior nonnegative on the box. Contributions from all normal sides are assembled into moment fields on the original coordinate strata, without enlarging the power–log spectrum.

That is genuinely the two-sided local coordinate model for a real divisor.

Keep the boundary explicit: this phase does not by itself establish arbitrary-chart gluing, absorption of a nonconstant phase unit, or general Jacobian factors such as \(\prod_i |w_i|^{h_i}\). The proposed theorem still uses `zeroOrders d`.

**Bottom line:** take option **(a)** as the endpoint and **(b)** as the intermediate. Do not use even/odd decomposition as the main architecture. The decisive design change is **RN-weighted assembly across overlapping normal-side measures**, rather than full-sign piecewise gluing.
