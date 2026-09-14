## A. Audit of level (1)

**Verdict:** the displayed statements deliver level (1) as designed: an intrinsic linear coefficient functional on the **fixed measured resolution**, with germ locality along the compact relevant zero fibre and compatibility with Theorem C on pull-backs. They do **not** yet deliver continuity as a distribution, invariance under changing the resolution, or stratum-kernel presentations.

This is a statement-level audit of the supplied signatures, not an independent checkout of the two revisions.

### A1. The domain is right

Keep
\[
\mathcal T^U_{\mu,q}:C^\infty(U)\longrightarrow\mathbb R.
\]

Let
\[
L:=\pi^{-1}(\operatorname{tsupport}\mathrm{prior}),\qquad
Z_0:=L\cap\{K\circ\pi=0\}.
\]
The landed results give compactness of \(L\), finiteness of \(\mu_U\), and concentration of \(\mu_U\) on \(L\). Thus requiring compact support of \(F\) would impose an unnecessary restriction: every smooth \(F\) is bounded on the part of \(U\) seen by the integral.

The eventual distribution-theoretic interpretation is a **compactly supported distribution acting on all smooth functions**, whose restriction to \(C_c^\infty(U)\) is a distribution in the usual test-function sense. The missing ingredient is continuity, not compact support of the input.

For the interface, it would be useful—but not necessary—to package smooth functions as a real vector space and bundle `coeff_add`, `coeff_smul`, and `coeff_zero` into a `LinearMap`. Choice of a transport can then be hidden behind `coeff_eq_of_transports`.

### A2. The support statement is exactly the appropriate current statement

`coeff_congr_of_eventuallyEq` says that the functional depends only on the smooth germ along \(Z_0\). This is the correct formal substitute for
\[
\operatorname{supp}\mathcal T^U_{\mu,q}\subseteq Z_0
\]
before a distribution structure has been installed.

In the paper, say either:

* “the coefficient functional is germ-local along \(Z_0\),” or
* “it has support contained in \(Z_0\), in the sense that it annihilates functions vanishing on a neighbourhood of \(Z_0\).”

Do **not** say it depends only on \(F|_{Z_0}\). Normal derivatives can contribute.

### A3. Distribution continuity: worth isolating, but not a prerequisite for D5–D6

The missing analytic estimate is indeed a finite chart-wise jet bound. For fixed \((\mu,q)\), the useful form is
\[
|\mathcal T^U_{\mu,q}[F]|
 \le C\max_{i,\ |\alpha|\le r}
       \sup_{u\in B_i}
       |\partial^\alpha(F\circ\phi_i^{-1})(u)|,
\]
with finitely many compact coordinate boxes \(B_i\) lying inside chart targets. The constants may depend on the fixed presentation and the coefficient index, but not on \(F\).

Two qualifications:

1. The boxes must lie where the inverse charts are genuinely smooth; the measurable totalisation `chartInv` is not the object on which to state derivative estimates.
2. Proving this estimate and building a manifold distribution API are separate tasks. The estimate already establishes the paper’s continuity claim under the standard topology.

**Recommendation:** make this an independent D3b unit, size **M–L**, after checking how directly `abs_observableCoeff_le` can be reused. Do not block D5 on it. Defer a general manifold-distribution infrastructure unless another result needs it.

### A4. Scope and cautions

The following aspects are correctly scoped:

* `eq_liftMeasure_of_map_gv` is genuinely unconditional **given its two hypotheses**. Those hypotheses themselves force the pushed measure to be concentrated on the regular locus.
* `coeff_eq_of_transports` compares transports over the **same** \(R\), prior, and lifted measure.
* `coeff_comp_gv` compares with the Euclidean input built from **that transport’s** `Y.T`; this is exactly the right bridge.
* Smooth functions on \(U\), rather than only pull-backs, are an essential gain.
* D4’s tangent-wall correspondence is sufficient for the numerical invariants below. No stronger wall-mapping theorem should be advertised as landed.

There is one important issue to address in the D5 adapter: **Jacobian exponents on phase-inactive coordinates**. See D5a below.

---

## B. Design of level (2)

### Recommended dependency structure

| Unit | Content | Size |
|---|---|---:|
| D5a | Atlas-transition adapter; inactive Jacobian exponents vanish | M–L |
| D5b | Intrinsic pairs, depth, resonance count | S–M |
| D5c | Local coordinate formula; closed filtrations | M |
| D6a | Engine resonance/support lemma | M–L, pending engine audit |
| D6b | Intrinsic resonant support | M with D6a; otherwise L–XL |
| D7 | Restriction/support consequences only | S |
| D8a | Conditional leading-functional positivity and bounds | M |
| D8b | Riesz representation on the compact zero fibre | M–L separately |

The signatures below are Lean-shaped interfaces, not claims about existing declaration names.

## D5a. Bridge the atlas to D4 before defining invariants

### 1. Name the divisor and centred charts

```lean
def divisor : Set R.U :=
  {P | K (R.gv P) = 0}

structure CenteredEvenChart (P : R.U) where
  E : EvenChartBox R
  mem_source : P ∈ E.φ.source
  coord_eq_zero : E.φ P = 0

def EvenChartBox.active (E : EvenChartBox R) : Finset (Fin d) :=
  Finset.univ.filter fun j => 0 < E.k j
```

Use `exists_evenChartBox` to prove nonemptiness for \(P\in D\).

### 2. Prove the inactive-exponent lemma

```lean
theorem EvenChartBox.h_eq_zero_of_k_eq_zero
    (E : EvenChartBox R) {j : Fin d} (hj : E.k j = 0) :
    E.h j = 0
```

**Why it matters.** D4’s Jacobian comparison uses monomials indexed by the active phase walls. At a translated point, an inactive coordinate that is zero cannot be absorbed into a nonvanishing Jacobian unit unless its Jacobian exponent is zero.

**Proof route.** Inside the open target near \(0\), choose a point with coordinate \(j=0\) and every other coordinate nonzero. Since \(k_j=0\), its phase is nonzero. The blow-down is a local analytic isomorphism there, so its coordinate Jacobian determinant is nonzero. The displayed Jacobian formula would make it zero if \(h_j>0\).

This uses `isoOff` and its derivative-invertibility consequence, not D4 alone. It is a small mathematical lemma but potentially **M** in the manifold API.

### 3. Prove one centred comparison theorem

```lean
def EvenChartBox.pairData (E : EvenChartBox R) :
    Multiset (ℕ × ℕ) :=
  E.active.val.map fun j => (E.k j, E.h j)

theorem centered_pairData_eq
    (E E' : CenteredEvenChart R P) :
    E.E.pairData = E'.E.pairData
```

The adapter supplies:

* analytic transition \(H=\phi'\circ\phi^{-1}\) near \(0\);
* analytic inverse \(G\);
* both inverse germ identities;
* \(H(0)=0\);
* phase equality;
* the signed determinant chain-rule identity.

Apply D4 with phase units \(1\), after removing inactive factors using the preceding lemma.

**Keep the adapter reusable for general unit-monomial charts.** D5c and comparison with engine charts will need more than the exact `EvenChartBox` structure.

---

## D5b. Define pairs first; derive depth and resonance

I recommend defining these on **all of \(U\)**, using the empty multiset off the divisor. This removes repeated subtype coercions and makes the closed-set statements cleaner.

```lean
noncomputable def pairs (P : R.U) : Multiset (ℕ × ℕ) :=
  if hP : P ∈ divisor R then
    (chosenCenteredEvenChart R hP).E.pairData
  else
    0

def depth (P : R.U) : ℕ :=
  (pairs R P).card

def Resonates (μ : ℝ) (p : ℕ × ℕ) : Prop :=
  ∃ m : ℕ,
    2 * (p.1 : ℝ) * μ = (p.2 : ℝ) + 1 + (m : ℝ)

noncomputable def resonanceCount (μ : ℝ) (P : R.U) : ℕ :=
  ((pairs R P).filter (Resonates μ)).card
```

Here classical decidability is harmless.

First prove:

```lean
theorem pairs_eq_centered ...
theorem depth_eq_card_active ...
theorem pairs_eq_zero_of_not_mem_divisor ...
theorem fst_pos_of_mem_pairs ...
theorem depth_le_dim : depth R P ≤ d
theorem resonanceCount_le_depth :
    resonanceCount R μ P ≤ depth R P
theorem depth_pos_iff :
    0 < depth R P ↔ P ∈ divisor R
```

Also useful:

```lean
theorem resonanceCount_eq_zero_of_nonpos
    (hμ : μ ≤ 0) :
    resonanceCount R μ P = 0
```

The resonance count is an **upper bound on possible logarithmic multiplicity**, not a nonvanishing invariant. Smooth-amplitude vanishing, orthant cancellation, and other cancellations may reduce the actual coefficient.

---

## D5c. Prove the local formula, then get both filtrations

The central theorem should be the multiset formula, not upper semicontinuity directly.

For an even chart \(E\), define
\[
J_E(Q)=\{j\in E.\mathrm{active}:(E.\phi Q)_j=0\}.
\]

Aim for:

```lean
theorem pairs_eq_chart_vanishing_pairs
    (E : EvenChartBox R)
    (hQ : Q ∈ E.φ.source) :
    pairs R Q =
      (E.active.filter fun j => E.φ Q j = 0).val.map
        (fun j => (E.k j, E.h j))
```

If an initial proof is easier on a smaller open neighbourhood of the centre, land that first. The mathematical formula holds throughout the source under the displayed `EvenChartBox` hypotheses.

### Proof route

At \(u_0=E.\phi Q\), translate coordinates by \(u_0\).

* Coordinates nonzero at \(u_0\) contribute analytic nonvanishing phase and Jacobian units.
* Active coordinates zero at \(u_0\) remain monomial factors.
* Inactive Jacobian factors disappear by D5a.
* Compare this translated unit-monomial form with a centred even chart at \(Q\), using D4.
* If \(Q\notin D\), the vanishing active set is empty, and no centred even chart is needed.

Thus **yes, use D4 with its general phase unit**. There is no need to normalise that unit away.

This yields locally
\[
\mathrm{pairs}(Q)\le \mathrm{pairs}(P)
\]
in the submultiset order whenever the chart is centred at \(P\). Consequently both depth and every fixed-\(\mu\) resonance count can only decrease nearby.

### Filtration definitions

```lean
def depthGE (c : ℕ) : Set R.U :=
  {P | c ≤ depth R P}

def resonanceGE (μ : ℝ) (c : ℕ) : Set R.U :=
  {P | c ≤ resonanceCount R μ P}

def shallowOpen (c : ℕ) : Set R.U :=
  (depthGE R (c + 1))ᶜ

def depthStratum (c : ℕ) : Set R.U :=
  {P | depth R P = c}
```

Prove:

```lean
theorem isClosed_depthGE (c) : IsClosed (depthGE R c)
theorem isClosed_resonanceGE (μ) (c) :
    IsClosed (resonanceGE R μ c)
theorem isOpen_shallowOpen (c) : IsOpen (shallowOpen R c)

theorem depthGE_one : depthGE R 1 = divisor R
theorem depthGE_succ_dim : depthGE R (d + 1) = ∅
```

Outside \(D\), use openness of the complement of the divisor. Inside \(D\), use the centred-chart submultiset formula. Directly proving openness of complements is likely easier than locating the right semicontinuity API.

### Coordinate description of the depth stratum

If \(E\) is centred at \(P\) and \(c=\mathrm{depth}(P)\), then, for \(Q\) in its source,
\[
Q\in D_{\ge c}
\iff
(\forall j\in E.\mathrm{active},\;(\phi Q)_j=0).
\]
Moreover, \(D_{\ge c+1}\) is absent from that chart source.

Land this as a set equality or membership equivalence. It supplies the desired local coordinate-subspace description.

**Do not build `S_c` as a bundled submanifold yet.** Locally closed sets plus these coordinate descriptions suffice for D6 and the proposed minimal D7. Nor should this stage claim Whitney conditions.

---

## D6. Resonant support: the target is clear, but an engine bridge is missing

Define the compact relevant resonance locus:

```lean
def resonantZeroFibre (μ : ℝ) (q : ℕ) : Set R.U :=
  Ξ.zeroFibre ∩ resonanceGE Ξ.R μ (q + 1)
```

D5c makes this compact. The desired theorem is:

```lean
theorem coeff_eq_zero_of_eventually_zero_on_resonantZeroFibre
    (hF :
      ∀ᶠ P in 𝓝ˢ (Ξ.resonantZeroFibre μ q), Ξ.F P = 0) :
    Ξ.coeff Y μ q = 0
```

Follow immediately with germ congruence and the weaker depth-support corollary:
\[
\operatorname{supp}\mathcal T^U_{\mu,q}
 \subseteq Z_0\cap\{r_\mu\ge q+1\}
 \subseteq Z_0\cap D_{\ge q+1}.
\]

### What can be concluded from the supplied engine signatures?

The bound `q ≤ d − 1` is **not sufficient**. Nor can I certify a finer `familyCoeff` lemma without its actual signatures.

There are two distinct statements to look for:

1. **Chart-wide multiplicity bound**
   \[
   q+1\le \#\{j\text{ active}:2k_j\mu=h_j+1+m_j\}.
   \]
2. **Local support on resonant wall intersections.**

The first alone does not prove D6 for a fixed chart: the amplitude may vanish near the deepest resonant intersections while remaining nonzero elsewhere in that chart.

### Cheapest recommended route: an engine-local support lemma

For a monomial model chart, let
\[
B_{\mu,q}
 =\left\{u:
 \#\{j:\ k_j>0,\ u_j=0,\ \exists m,\,
                 2k_j\mu=h_j+1+m\}\ge q+1\right\}.
\]

Prove that its coefficient vanishes when the smooth amplitude vanishes near \(B_{\mu,q}\), within the relevant model support.

This can often be extracted from the engine’s iterated Taylor/Mellin construction:

* a resonant coordinate supplies a possible simple pole at \(\mu\);
* its residue is supported on that coordinate wall;
* a logarithmic power \(q\) requires pole order at least \(q+1\);
* therefore the coefficient is supported on intersections of at least \(q+1\) resonant walls.

The implementation should use the engine’s existing coefficient construction, not introduce a new Mellin formalisation.

Apply this chart by chart to the **existing** resolved decomposition, identify the local wall counts by the D5 comparison adapter, and sum. This avoids constructing a new transport.

### Why the proposed partition-of-unity route is not free

The landed existence theorem does not say that a resolved transport can be chosen subordinate to an arbitrary prescribed cover. A proof through newly chosen centred charts therefore needs either:

* a subordinate-transport theorem; or
* a local coordinate density/change-of-variables theorem for \(\mu_U\), followed by a local monomial expansion theorem.

Those are additional interfaces. Thus I would not schedule D6 as “just partition of unity.”

**Decision gate:** inspect the engine for local wall-supported coefficient formulas first. If they exist, D6 is **M**. If only a coarse degree bound exists, isolate D6a explicitly and budget **M–L** or more.

---

## D7. Land restrictions, defer kernels

The minimal useful D7 is entirely algebraic and support-theoretic.

For \(U_c=U\setminus D_{\ge c+1}\):

1. If \(q\ge c\), the restriction of \(\mathcal T^U_{\mu,q}\) to \(U_c\) is zero.
2. For \(q=c-1\), its restriction to \(U_c\) is supported on
   \[
   Z_0\cap S_c\cap\{r_\mu=c\}.
   \]

Initially state these for global smooth functions whose topological support is contained in \(U_c\). This avoids introducing test functions on an open submanifold and extension-by-zero machinery.

**Defer actual kernels.** A smooth stratum-kernel presentation generally involves **normal jets**:
\[
F\longmapsto
 \sum_\alpha\int_{S_c}
       a_\alpha\,(\partial_\nu^\alpha F)|_{S_c},
\]
not necessarily just integration of \(F|_{S_c}\). Even in one dimension, higher coefficients of a Gaussian expansion involve derivatives at the divisor. D5–D6 do not establish such a presentation.

---

## D8. Leading positivity: define “leading” at the functional level

This is the principal correction to the proposed wording.

Being first nonzero for the particular observable stored in `Ξ.F` is **not** enough. “Globally first” must refer to the coefficient functionals, or be established using the constant observable \(1\) and domination.

Write \(C_{\mu,q}(G)\) for the coefficient with observable \(G\), and define
\[
(\nu,p)\prec(\mu,q)
\quad\Longleftrightarrow\quad
\nu<\mu\ \text{or}\ (\nu=\mu\ \text{and}\ p>q).
\]

### Safest initial interface

```lean
def IsLeadingFunctionalIndex (μ₀ : ℝ) (q₀ : ℕ) : Prop :=
  (∃ G hG, C μ₀ q₀ G hG ≠ 0) ∧
  ∀ ν p, Precedes (ν, p) (μ₀, q₀) →
    ∀ G hG, C ν p G hG = 0
```

The common lattice and logarithmic bound should be fixed from one transport and shown independent of the observable. Then prove a general expansion lemma giving
\[
N^{\mu_0}(\log N)^{-q_0}Z_N[G]
 \longrightarrow C_{\mu_0,q_0}(G).
\]
Only \(N>1\) matters, so the normalising factor is positive.

Consequently:
\[
G\ge0\text{ on }L
\quad\Longrightarrow\quad
C_{\mu_0,q_0}(G)\ge0.
\]

For any \(M\ge0\) bounding \(|G|\) on \(L\), apply positivity to \(M\pm G\):
\[
|C_{\mu_0,q_0}(G)|
 \le M\,C_{\mu_0,q_0}(1).
\]

Under `IsLeadingFunctionalIndex`, nonzeroness then implies
\[
C_{\mu_0,q_0}(1)>0.
\]

This is **M**, not automatically S: extracting the normalised limit from the expansion and managing the common support are the substantive steps.

### An alternative, convenient user-facing hypothesis

Assume \((\mu_0,q_0)\) is the leading nonzero index for \(Z_N[1]\). Since
\[
|Z_N[G]|\le \sup_L|G|\,Z_N[1],
\]
expansion comparison forces all preceding coefficients of every \(G\) to vanish. Thus this hypothesis implies the functional-level leading condition.

This is a useful second theorem, after a general “domination excludes earlier asymptotic terms” lemma.

### Existence remains conditional

Correct: no unconditional first nonzero coefficient should be claimed. A zero prior, support away from the divisor, or sufficiently flat amplitudes can leave every algebraic-logarithmic coefficient zero.

If some coefficient **functional** is nonzero, the common nonnegative lattice and finite log bound give a first index. A convenient Lean construction minimises the lattice numerator in \(\mathbb N\), then maximises the log degree in a finite set.

### Zero-fibre norm and Riesz

The first bound should use \(\sup_L|G|\). A sharper bound
\[
|C_{\mu_0,q_0}(G)|
 \le C_{\mu_0,q_0}(1)\sup_{Z_0}|G|
\]
can then be proved using concentration near \(Z_0\): outside any neighbourhood of \(Z_0\), the integral is exponentially small; inside a sufficiently small neighbourhood, continuity bounds \(|G|\) by \(\sup_{Z_0}|G|+\varepsilon\).

This yields dependence only on the **values** of \(G\) on \(Z_0\) for this leading functional—a stronger property than general germ locality.

Riesz representation is a separate unit. One must extend the bounded positive functional from smooth restrictions to \(C(Z_0)\), using density of smooth restrictions, and then invoke the relevant representation theorem. Do not label that formal step “automatic”; smooth separation/density and the compact-space measure API still need bridging.

---

## Regression: \(x^2y^2\) on the quadrant

Yes—valuable, but split it.

### D5 regression: inexpensive

For \(k=(1,1)\), \(h=(0,0)\):

* depth is two at the origin;
* depth is one on either punctured axis;
* depth is zero off the axes;
* at \(\mu=\tfrac12\), resonance count equals depth.

Thus D6 predicts:

* the \((\tfrac12,1)\) coefficient is supported at the origin;
* the \((\tfrac12,0)\) coefficient is supported on the axes.

This tests precisely the distinction between depth and resonance support.

### Coefficient regression: later

For quadrant Lebesgue measure and an amplitude equal to \(1\) near the origin, the leading coefficient is
\[
C_{1/2,1}(F)=\frac{\sqrt\pi}{4}F(0,0).
\]
Away from the origin, the \(q=0\) axis contribution has density proportional to \(1/x\) or \(1/y\). This is an excellent regression for why kernel statements concern **restrictions to strata away from deeper strata**, rather than globally smooth kernels on closed axes.

Land the combinatorial regression with D5; defer the evaluated Gaussian constants until D6/D8.

---

## C. Paper-facing paragraph — nine sentences

On the fixed measured resolution \((U,\pi,\mu_U)\), we define the resolved integral for every smooth real-valued observable on \(U\), without requiring the observable to descend through \(\pi\). The measure \(\mu_U\) is the divisor-null lift of the prior-density measure, characterised by `eq_liftMeasure_of_map_gv`, and `map_gv_resolvedMeasure` identifies its push-forward with that prior-density measure. It is finite and concentrated on the compact inverse image of the prior’s support, so compact support of the observable is unnecessary. For every resolved core transport, `hasSmoothCoordFreeExpansion` supplies the corresponding algebraic-logarithmic asymptotic expansion. The theorem `coeff_eq_of_transports` shows that its coefficients are independent of the chosen transport on this fixed resolution. The results `coeff_add`, `coeff_smul`, and `coeff_zero` make each coefficient a real-linear functional on smooth observables. By `coeff_congr_of_eventuallyEq`, this functional depends only on the smooth germ along the compact set \(\pi^{-1}(\operatorname{tsupport}\mathrm{prior})\cap\{K\circ\pi=0\}\), giving support there in the germ-local sense. For pull-back observables, `coeff_comp_gv` identifies these functionals with the coefficients of Theorem C through the Euclidean bridge associated with the transport. These results do not yet assert continuity in the smooth-function topology, invariance under changing the resolution, or smooth stratum-kernel presentations.
