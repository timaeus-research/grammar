## Recommendation

Build Theorem D, but separate three levels:

1. **An intrinsic coefficient functional on the fixed resolution** \((U,\pi)\), where \(\pi=R.gv\). This is the immediate, substantial theorem.
2. **An intrinsic normal-crossing depth/resonance filtration**, obtained from a chart-invariance lemma.
3. **Smooth stratum-kernel presentations of appropriate restrictions**, not a canonical decomposition of every coefficient into contributions from all strata.

The last distinction matters. Keeping the resolved manifold fixes the carrier problem, but it does **not** canonically split a distribution among incident strata. Finite-part extension across deeper strata still has an ambiguity supported on those deeper strata.

Two proposed statements need correction:

- The highest logarithmic coefficient **at an arbitrary exponent** need not be a measure.
- The candidate exponents of a normal-crossing product are given by **coordinate ratios and their coincidences**, not generally by sums of those ratios.

What follows is a design based on the exports you supplied, rather than an inspection of the current engine definitions.

---

# 1. Hironaka: define the resolved measure canonically, then lift the transport

Write
\[
D=\{P\in U:K(\pi P)=0\},\qquad
U^\times=U\setminus D,\qquad
W^\times=W\setminus K^{-1}(0).
\]

Here “regular locus” means the **off-divisor locus**, not the locus where \(dK\ne0\).

Assume throughout the existing bridge hypotheses, including nonnegative prior, compact support contained in \(W\), and the zero-set nullity established there.

## 1.1 Use the off-divisor isomorphism to define \(\mu_U\)

This is the cleanest definition for intrinsicness.

First package `isoOff` as a homeomorphism of subtypes
\[
e:U^\times \simeq_{\mathrm{homeo}} W^\times.
\]
An analytic equivalence is welcome but not needed for the measure construction.

Let \(\nu\) be the prior-weighted volume measure on \(W\), and let \(\nu^\times\) be its restriction, regarded as a measure on the subtype \(W^\times\). Define
\[
\mu_U
  :=(\operatorname{incl}_{U^\times})_*
       (e^{-1}_*\nu^\times).
\]

Use subtype maps; do **not** first choose a globally defined inverse \(W\to U\). That introduces unnecessary default values and measurability obligations.

Equip \(U\) with its Borel measurable structure. The inverse on the subtype is continuous, hence measurable. No continuity of any extension across \(D\) is required.

The foundational lemmas should be:

```lean
-- Schematic interfaces, not proposed exact Mathlib spellings.

offDivisorHomeomorph :
  {P : R.U // K (R.gv P) ≠ 0} ≃ₜ
  {x : W // K x ≠ 0}

resolvedMeasure_divisor :
  μU D = 0

resolvedMeasure_map_gv :
  Measure.map R.gv μU = priorMeasure

resolvedMeasure_concentrated :
  μU ((R.gv ⁻¹' tsupport prior)ᶜ) = 0

isCompact_resolvedPriorSupport :
  IsCompact (R.gv ⁻¹' tsupport prior)
```

The third identity is on the ambient Euclidean target if `priorMeasure` is defined there; otherwise first prove it on \(W\), then compose with inclusion.

### Which nullity is needed?

The needed target assertion is
\[
\nu(K^{-1}(0))=0.
\]
It is enough to prove volume-nullity of \(K^{-1}(0)\cap\operatorname{tsupport}(\text{prior})\), as the bridge already does.

Do not phrase this as “the divisor is null on \(W\).” The divisor lives on \(U\); its \(\mu_U\)-nullity follows from the definition. There is no need to choose a reference volume measure on \(U\).

## 1.2 Add a uniqueness theorem for lifts

This is the useful algebraic hinge:

> A measure on \(U\) that gives \(D\) zero mass is determined by its pushforward under \(\pi\).

More precisely, for the measures needed here:
```lean
eq_of_map_gv_eq_of_divisor_null
    (hη : η D = 0) (hξ : ξ D = 0)
    (hmap : η.map R.gv = ξ.map R.gv) :
    η = ξ
```

This follows by restricting to the subtype homeomorphism.

It turns the resolved transport identity into a short consequence of the existing target transport identity.

## 1.3 Lift the existing cores and tail

For each core, retain its map into \(U\):
\[
\eta_i(u)=\phi_i^{-1}(u)
\]
or the corresponding rescaled chart parametrization if normalization introduces a rescaling.

Then
\[
\pi\circ\eta_i=\psi_i
\]
on the core box, and
\[
\operatorname{coreU}_i=(\eta_i)_*(\operatorname{coreSource}_i).
\]

**Important implementation detail:** `OpenPartialHomeomorph.symm` is only controlled on its target. Do not demand that its arbitrary globally defined function be measurable everywhere. Either:

- define \(\eta_i\) on the subtype of the core box; or
- prove the needed a.e.-measurability relative to the core measure.

The subtype version is cleaner.

For the tail, the existing identity implies `tail ≤ priorMeasure`; in particular, it is concentrated on \(W\). The positive gap implies it is concentrated off the zero set. Thus define `tailU` by the same subtype inverse construction.

Prove:
\[
\begin{aligned}
\pi_*\operatorname{coreU}_i&=\operatorname{coreTarget}_i,\\
\operatorname{coreU}_i(D)&=0,\\
\pi_*\operatorname{tailU}&=\operatorname{tail},\\
\operatorname{tailU}(D)&=0,\\
\delta&\le K\circ\pi\quad\text{a.e. for }\operatorname{tailU}.
\end{aligned}
\]

Core nullity uses coordinate-wall nullity in the source box. Now push forward
\[
\sum_i\operatorname{coreU}_i+\operatorname{tailU}
\]
and use uniqueness of null-divisor lifts to obtain
\[
\boxed{\quad \sum_i\operatorname{coreU}_i+\operatorname{tailU}=\mu_U.\quad}
\]

This reuses the existing bridge rather than duplicating its measure assembly.

## 1.4 Recommended structures

I would use two layers.

### A. Canonical measure package

Parameterized by `R`, prior, and the relevant hypotheses:

```lean
ResolvedPriorMeasure R prior
```

Its primary content is the definition of `μU`, with the pushforward, concentration, finiteness, and null-divisor theorems.

### B. Lifted core transport

Schematic:

```lean
structure ResolvedCoreTransport (R ...) where
  toCore : NormalisedCoreTransport d K prior

  -- Maps defined on core-box subtypes.
  lift : ∀ i, CoreBox toCore i → R.U
  lift_continuous : ...
  lift_smooth : ...
  gv_lift : ∀ i u, R.gv (lift i u) = toCore.ψ i u

  tailU : Measure R.U
  map_tailU : tailU.map R.gv = toCore.tail
  tailU_gap : ∀ᵐ P ∂tailU, toCore.δ ≤ K (R.gv P)

  transportU :
    ∑ i, coreMeasureU lift i + tailU = resolvedPriorMeasure R prior
```

The finite `EvenChartBox` family, cutoffs, and relationships with `lift` belong in the concrete constructor/witness package. They are useful presentation data, but the grammar-facing interface need not duplicate every construction detail.

In particular, distinguish:

- the minimal transport interface consumed by grammar;
- the stronger atlas-derived witness constructed by hironaka.

## 1.5 The integral identity

For smooth \(F\), compactness of
\[
C=\pi^{-1}(\operatorname{tsupport}\text{ prior})
\]
makes \(F\) bounded on the measure’s support. Hence
\[
Z_t^U[F]=\int_U F(P)e^{-tK(\pi P)}\,d\mu_U(P)
\]
is well-defined under the existing phase hypotheses.

Pushforward gives
\[
\boxed{\quad
Z_t^U[f\circ\pi]
 =\int_{\mathbb R^d}f(x)e^{-tK(x)}\operatorname{prior}(x)\,dx.
\quad}
\]

This should be proved before any coefficient construction.

---

# 2. Grammar: the primary object should be a smooth functional with compact control

## 2.1 Do not start with overlap-compatible chart distributions

They are a correct eventual presentation, but they are not the shortest route:

- distributions must be localized to overlap domains;
- transition laws require test-function transport and continuity estimates;
- cutoff-weighted pieces are **not** themselves an overlap-compatible family.

Instead define the global functional first and derive its local distributions afterward.

## 2.2 Proposed formal object

Use a linear functional on the vector space of globally smooth real-valued functions on \(U\), accompanied by a compact finite-order estimate.

Conceptually:

```lean
structure CompactlyControlledSmoothFunctional (U ...) where
  toLinearMap : SmoothFunctions U →ₗ[ℝ] ℝ
  control : FiniteChartJetControl U
  bound : ∃ C, 0 ≤ C ∧
    ∀ F, |toLinearMap F| ≤ C * control.seminorm F
```

Here `FiniteChartJetControl` contains finitely many relatively compact chart domains, compact coordinate sets, and derivative orders. Its seminorm has the form
\[
p_r(F)=
 \max_{i,\ |\alpha|\le r}
 \sup_{u\in Q_i}
 \left|\partial^\alpha(F\circ\eta_i)(u)\right|.
\]

This is the compactly supported-distribution version of the object. It is legitimate to act on **all smooth functions**, because the functional has compact support.

For the first implementation, “smooth in every maximal-atlas chart” is acceptable if that is what the extension machinery consumes. Provide equivalence with the intended `ContMDiff` notion separately; avoid making two unrelated notions permanent.

## 2.3 Construction and intrinsicness

Run the existing box engine with chart observables
\[
F\circ\eta_i.
\]
Choose controlled smooth extensions exactly as for `obsExt`, and construct a certificate for the **same global function** \(t\mapsto Z_t^U[F]\).

Define
\[
\mathcal T_{\mu,q}^R(F)
\]
from one such certificate. Then use `SmoothExpansionCertificate.coeff_eq` to prove independence of:

- finite chart cover;
- partition cutoffs;
- normalized core presentation;
- extension choices;
- auxiliary truncation/certificate choices.

The required hypothesis is that both certificates expand the same \(Z^U[F]\), with the normal index conventions reconciled as in Theorem C.

Then prove:

1. linearity;
2. compact finite-order control;
3. support/locality;
4. pushforward compatibility;
5. uniform remainder.

The main compatibility is
\[
\boxed{\quad
\mathcal T_{\mu,q}^R(f\circ\pi)
   = \operatorname{coeffDistribution}(X,\mu,q)(f).
\quad}
\]

## 2.4 Support and uniformity

Set \(D_C=D\cap C\). Prove
\[
\operatorname{supp}\mathcal T_{\mu,q}^R\subseteq D_C.
\]

The useful first Lean statement is:

```lean
coeff_eq_zero_of_vanishes_near_divisorSupport
    (hF : ∃ O, IsOpen O ∧ D_C ⊆ O ∧ ∀ P ∈ O, F P = 0) :
    resolvedCoeff μ q F = 0
```

Its proof can use the phase gap on the remaining compact support and uniqueness, independently of face combinatorics.

For the uniform remainder, use a finite atlas seminorm of sufficiently high order and include a bound for \(F\) on \(C\) to control the tail. Transfer the existing explicit spectral gap machinery; no new exponent-gap argument should be necessary.

## 2.5 Dependence on the resolution

The functional is intrinsic **on the fixed measured resolution** \((U,\pi,\mu_U)\).

It is not meaningful to equate functionals on two unrelated spaces of smooth functions. What is meaningful is:

- equality on observables pulled back from the base;
- functoriality under a specified smooth comparison map \(h:U'\to U\) satisfying the phase and measure-pushforward identities.

A common-refinement theorem is not needed for Theorem D and should not be claimed from the supplied exports.

---

# 3. Stratification: do A, but isolate it from the first landing

I recommend:

- first land the resolved functional without any chart-invariance theorem;
- develop **A** as an independent normal-crossing geometry unit;
- use fixed-atlas descriptions only as an interim presentation, not as the final intrinsic definition;
- do not use C.

The iterated-singular-locus route adds infrastructure and does not remove the local invariance argument.

## 3.1 A is smaller than the proposed hypersurface-germ route suggests

You do not need irreducible analytic-set decomposition. Nor do you need a general theorem classifying smooth hypersurface germs contained in a crossing.

Use the **lowest nonzero homogeneous term** of the local phase.

At \(P\), translate both coordinate systems so that \(P\) is the origin. Coordinates nonzero at \(P\) become units. The two phase descriptions have the form
\[
a(x)\prod_{j\in J}x_j^{2k_j}
 =
a'(H(x))\prod_{\ell\in J'}H_\ell(x)^{2k'_\ell},
\]
where \(a(0),a'(0)\ne0\), \(H(0)=0\), and \(DH(0)\) is invertible.

Taking leading homogeneous terms gives a polynomial identity
\[
a(0)\prod_{j\in J}x_j^{2k_j}
 =
a'(0)\prod_{\ell\in J'}
       ((DH(0)x)_\ell)^{2k'_\ell}.
\]

Unique factorization into nonzero linear factors gives a bijection
\[
\sigma:J\simeq J'
\]
matching branch tangent hyperplanes and satisfying \(k_j=k'_{\sigma(j)}\).

Now apply the same leading-term argument to the Jacobian transformation law
\[
\det D\psi_i
 =(\det D\psi_j\circ H)\det DH.
\]
Since \(\det DH(0)\ne0\), it is a unit. Using the already identified branch correspondence gives
\[
h_j=h'_{\sigma(j)}.
\]

This establishes the paired multiset invariance, not merely separate invariance of the two multisets.

## 3.2 The precise local theorem to target

A suitable theorem is:

> For two smooth local coordinate systems at \(P\), with invertible transition derivative and nonvanishing-unit monomial descriptions of the same phase and the same blow-down determinant, their active wall sets through \(P\) admit a bijection preserving \((k,h)\).

Its conclusion should retain the branch correspondence:

```lean
∃ σ : WallAt chart₁ P ≃ WallAt chart₂ P,
  (∀ j, k₁ j = k₂ (σ j)) ∧
  (∀ j, h₁ j = h₂ (σ j)) ∧
  tangentHyperplanesMatch σ
```

The algebraic core is a finite-dimensional polynomial lemma. The analytic wrapper needs leading-jet calculations under a local diffeomorphism. I would budget this as a **large standalone unit**, not as a one-lemma application of existing manifold infrastructure. It is nevertheless much narrower than analytic germ factorization.

Avoid promising specific existing Mathlib theorem names for those leading-term bridges until they are checked.

## 3.3 Intrinsic strata

Define
\[
d_D(P)=|J(P)|,\qquad
D_{\ge c}=\{P:d_D(P)\ge c\},\qquad
S_c=D_{\ge c}\setminus D_{\ge c+1}.
\]

Locally:
\[
D_{\ge c}
 =\bigcup_{|J|=c}\{u_j=0\text{ for }j\in J\}.
\]

Consequently:

- \(D_{\ge c}\) is closed;
- \(S_c\) is a smooth, locally closed submanifold of codimension \(c\);
- \(U_c=U\setminus D_{\ge c+1}\) is open;
- \(S_c\) is closed **inside \(U_c\)**.

Thus the closure in the proposal is unnecessary once this geometry is proved.

The weighted multiset gives finer, locally closed smooth pieces. Call these the **normal-crossing depth/weight decomposition** initially. Connected-stratum conventions, local finiteness, and Whitney conditions should be separate statements if the paper needs them.

---

# 4. What stratified coefficient statements are actually true?

## 4.1 Support filtration: true, but distinguish restriction from splitting

For any coefficient, restriction to \(U_c\) is intrinsic and supported on
\[
D\cap U_c=S_1\cup\cdots\cup S_c.
\]

That is the corrected version of (i). It does not by itself assign independent objects to each of those strata.

There is a natural filtration
\[
\mathscr F_c
 =\{T:\operatorname{supp}T\subseteq D_{\ge c}\}.
\]
If \(T\in\mathscr F_c\), its restriction to \(U_c\) is an intrinsic distribution supported on \(S_c\). Two such distributions have the same restriction precisely when their difference is supported on \(D_{\ge c+1}\).

This gives the appropriate associated-graded interpretation. It does **not** give a canonical projection of an arbitrary \(T\in\mathscr F_1\) onto each graded level.

This limitation should be explicit in the paper.

## 4.2 Smooth kernels on open strata: true in the right support range

Statement (ii), as written, is too strong in two ways.

### First correction: \(F\) supported in \(U_c\) still sees shallower strata

It can meet every \(S_1,\ldots,S_c\). Therefore its coefficient cannot generally be expressed by an integral over \(S_c\) alone.

### Second correction: Taylor remainders do not simply disappear

Vanishing near deeper intersections eliminates terms localized there, but a coordinate Taylor remainder is not thereby identically zero. What becomes true is that the relevant singular weights are ordinary smooth functions away from their further walls; compactly supported tests there see ordinary integrals.

A good theorem is:

> If \(\mathcal T_{\mu,q}\) is supported on \(D_{\ge c}\), then locally on \(U_c\) it is a finite transverse differential operator applied to smooth densities on \(S_c\).

In adapted coordinates \((z,v)\), with \(S_c=\{z=0\}\),
\[
\mathcal T_{\mu,q}(F)
 =\sum_{|a|\le r}
   \int_{S_c}
      \partial_z^aF(0,v)\,B_{a,\mu,q}(v)\,|dv|
\]
for tests compactly supported in the coordinate neighborhood inside \(U_c\).

The \(B_a\) are smooth there and explicitly computable from the resolution density and engine coefficients. Thus they are integrable against such tests.

Do not infer global \(L^1\)-integrability up to the deleted deeper strata. The kernel \(1/x\) in the regression is the basic counterexample.

### What is intrinsic in this formula?

The restricted functional is intrinsic. The individual normal derivatives and \(B_a\) are coordinate-dependent and transform together.

Without a tubular structure or connection, there is no preferred splitting into individual normal derivative orders. The transverse-order filtration and its principal normal symbol are intrinsic.

A particularly useful automatic case is
\[
\boxed{\quad
\mathcal T_{\mu,q}|_{U_{q+1}}
\text{ is supported on }S_{q+1}
\text{ and has smooth transverse-jet kernels there.}
\quad}
\]
This follows from the logarithmic-depth bound below.

## 4.3 Highest log coefficient: false at a general exponent

Already in one dimension,
\[
\int_{\mathbb R}e^{-nx^2}F(x)\,dx
 \sim \sqrt\pi\,n^{-1/2}F(0)
 +\frac{\sqrt\pi}{4}n^{-3/2}F''(0)+\cdots.
\]
At exponent \(3/2\), the highest log power is \(0\), but its coefficient is a multiple of \(\delta''\), not a measure.

This is not merely a zero-log pathology. For a product phase \(x^2y^2\), higher coincident Mellin poles give logarithmic coefficients involving mixed normal derivatives.

In the displayed engine expression, setting \(j-q=0\) removes the logarithmic moment factor. It does **not** remove:

- normal Taylor derivatives;
- the `remList` operators;
- all possible finite-part behavior by itself.

So “`e = 0` implies order zero” is not a valid proof.

### Correct leading-coefficient theorem

For a positive measure \(\mu_U\), the coefficient of the **globally first nonzero asymptotic term**—smallest exponent, then highest log power at that exponent—is a positive order-zero functional.

Indeed, for nonnegative smooth \(F\),
\[
n^\lambda(\log n)^{-q_*}Z_n^U[F]
 \longrightarrow \mathcal T_{\lambda,q_*}(F)\ge0,
\]
provided all preceding coefficient functionals vanish.

Positivity gives, using a cutoff equal to one near the compact support,
\[
|\mathcal T_{\lambda,q_*}(F)|
 \le C\sup_C|F|.
\]
Hence this is a finite positive Radon measure.

That is a robust abstract route to order zero. A concrete density formula still needs the face analysis.

For the familiar leading-residue formula, prove a more explicit sufficient-condition theorem:

- the contributing normal Taylor index is zero;
- all remaining transverse weights after evaluation at \(\lambda\) have exponent \(>-1\);
- the maximal tied set has been taken.

Then the remaining integral is genuinely integrable, no finite-part extension is needed for that residue, and the paper’s leading formula follows.

“Deepest contributing” should mean **maximal resonant multiplicity at that exponent**, not simply largest geometric depth.

## 4.4 Exponents and logarithms: use resonant coordinate ratios

In local resolved coordinates, the measure density is
\[
\operatorname{prior}(\pi(u))\,|b(u)|
       \prod_j|u_j|^{h_j}\,du,
\]
and the phase is \(\prod_j u_j^{2k_j}\).

The candidate positive Mellin poles from branch \(j\) are
\[
L_j=\left\{\frac{h_j+1+m}{2k_j}:m\in\mathbb N\right\},
\qquad k_j>0.
\]

Thus candidate exponents lie in the **union** of these lattices. Multiple poles arise from **equalities** between such ratios.

For a face \(J\) contributing a simultaneous pole at \(\mu\), the relevant condition is
\[
2k_j\mu=h_j+1+m_j\qquad(j\in J),
\]
not a sum over \(j\).

Smooth two-sided charts can give parity improvements, and amplitude vanishing can remove candidates. Start with the safe over-approximation above.

Define the intrinsic resonant count
\[
r_\mu(P)=
 \#\left\{j\in J(P):
   \mu\in L_j\right\}.
\]
Paired-multiset invariance makes this well-defined.

The desired local theorem is:
\[
\boxed{\quad
\operatorname{supp}\mathcal T_{\mu,q}
 \subseteq C\cap\{P:r_\mu(P)\ge q+1\}.
\quad}
\]

In particular,
\[
\operatorname{supp}\mathcal T_{\mu,q}
 \subseteq C\cap D_{\ge q+1}.
\]

These are **necessary contribution conditions**, not nonvanishing assertions. Prior vanishing, symmetry, and cancellations remain possible.

To prove them intrinsically, localize the observable to a sufficiently small chart and use uniqueness to compare with a locally adapted expansion. Do not try to read local support directly from every term of one fixed global face presentation.

---

# 5. Regression: \(K=x^2y^2\) on the quadrant

For
\[
Z_n[u]=\int_0^1\int_0^1e^{-nx^2y^2}u(x,y)\,dx\,dy,
\]
with unit density:

- if \(u\) is supported near the horizontal open axis and away from the corner,
  \[
  T_{1/2,0}(u)
    =\frac{\sqrt\pi}{2}
       \int_0^1\frac{u(x,0)}x\,dx;
  \]
- similarly for the vertical axis;
- for a test supported away from the corner but meeting both axes, include both terms;
- the top leading logarithmic coefficient is
  \[
  T_{1/2,1}=\frac{\sqrt\pi}{4}\delta_{(0,0)}.
  \]

The extension of the two \(1/x\)-type kernels across the corner requires finite parts. Changing the finite-part normalization shifts a corner-supported term. This is the concrete reason that “intrinsic open-stratum restriction” does not mean “canonical global summand belonging to that stratum.”

The exact constants above are for the stated quadrant normalization; do not reuse them unchanged for the full plane.

---

# 6. Landing plan, sizes, and parallel work

Here `S/M/L` means relative implementation scope, not a repository-verified line estimate.

| Unit | Content | Size |
|---|---|---:|
| D0 | Off-divisor subtype homeomorphism; canonical \(\mu_U\); unique null-divisor lift; pushforward integral identity | M |
| D1 | Lift existing cores/tail and construct `ResolvedCoreTransport` | M |
| D2 | Smooth-observable adapter; resolved certificates; uniqueness and base compatibility | M–L |
| D3 | Compact smooth-functional object; jet estimates; support; uniform remainder | M–L |
| D4 | Local wall correspondence preserving \((k,h)\) | L |
| D5 | Intrinsic depth/weight/resonance loci and their local geometry | M after D4 |
| D6 | Resonant-support theorem and log-depth filtration | M–L |
| D7 | Smooth transverse-jet kernels on open strata; overlap transformation statements | L |
| D8 | Leading positive measure theorem and explicit leading-density corollaries | M, then M–L |

## First unit

**Land D0 first.**

Its acceptance criterion should be:

> There is a canonical finite measure on the fixed resolution, concentrated over the prior support, giving the divisor zero mass, with the correct pushforward and observable integral identity.

This already establishes the object whose expansions will be intrinsic. It contains no grammar-engine changes and no stratification theory.

## Parallelizable work

After agreeing on interfaces:

- hironaka can develop D0–D1;
- grammar can develop D2–D3 against an abstract lifted transport;
- the normal-crossing algebra team can develop D4 independently;
- the engine team can prove the local ratio/resonance bound and the open-stratum kernel theorem in Euclidean normal-crossing coordinates before D4 is available;
- the positivity argument for D8 can be developed from an abstract positive integral and coefficient certificate.

## Explicit non-claims

Theorem D should not initially claim:

1. a canonical decomposition into global summands indexed by every stratum;
2. coordinate-independent individual \(B_a\) or normal derivative operators;
3. order zero for the highest log coefficient at every exponent;
4. global integrability of open-stratum kernels up to deeper strata;
5. nonvanishing for every candidate exponent;
6. independence of the resolved functional from the resolution without specified comparison maps;
7. Whitney stratification or global irreducible divisor components.

---

## Suggested mirror paragraph

**Theorem D — resolved and stratified coefficient distributions.** For a fixed Watanabe modification, the prior-weighted measure lifts canonically to the resolved manifold through the off-divisor analytic isomorphism. Its Laplace integral against smooth resolved observables has intrinsic, compactly supported, finite-order coefficient functionals, independent of the chart cover, cutoffs, and extension choices. Their pushforwards recover Theorem C. The local normal-crossing multiplicities define intrinsic depth and resonance loci; the coefficient of \(n^{-\mu}(\log n)^q\) is supported where at least \(q+1\) branches are resonant at \(\mu\). Appropriate open-stratum restrictions admit explicit smooth transverse-jet kernel presentations, while extension across deeper strata retains finite-part phenomena. The globally leading highest-log coefficient is a positive measure. No canonical splitting among incident strata, or measure property at arbitrary higher exponents, is asserted.
