## Recommendation

Pursue **(B) as the proof engine, with a limited version of (C) as its geometric realization**. Work in grammar at v4.33.1, against a small interface for a **chosen normal family and tubular pullback**. Do not start by constructing quotient bundles, symmetric-power bundles, or manifold densities.

The target should be:

> For a chosen tubular pullback, fibrewise Taylor forms and fibre moment functionals have compatible frame-transformation laws; their contraction is frame-independent. Under explicit measure-transport and Taylor-summability hypotheses, integrating these contractions recovers the stratum integral. For transverse labelled divisors, the homogeneous Taylor forms have an intrinsic multi-index decomposition.

That is substantial mathematical content, not merely terminology. Most of its analytic and integration engine already exists in grammar.

There are, however, **several corrections to the paper that should precede the dots**—especially normalization, the density expansion, and the reduction to a box.

---

## 1. Why not simply choose (C)?

There are two important qualifications.

### An embedded normal bundle is not automatically the desired normal bundle

If \(S\subset M\subset\mathbb R^d\), StrucDual’s orthogonal normal to \(S\) **in \(\mathbb R^d\)** is not the normal of \(S\) **in \(M\)**. Its rank is generally wrong, and \(s+n\) need not lie in \(M\).

Thus StrucDual directly supplies the desired realization when the ambient manifold really is an open Euclidean ambient space. It does not, merely by embedding the resolved manifold, supply the paper’s tubular map into that manifold.

For the general application, keep \(\Phi\) as a hypothesis. An eventual adapter must identify the correct normal family and provide a map into the resolved space.

### “Canonical” must mean relative to the chosen geometry

For \(S\subset\mathbb R^d\), the derivative of
\[
n\longmapsto F(s+n),\qquad n\in N_s,
\]
is frame-independent, but depends on the ambient embedding and Euclidean normal choice. More generally, the full normal Taylor series depends on \(\Phi\).

This is consistent with the paper’s corrected discussion, but not with an unqualified claim that normal derivatives are canonical.

### Dependency decision

**Use an abstract interface now; connect StrucDual later.**

* Keep grammar on v4.33.1.
* Do not attempt to use the v4.29.0 dependency unchanged.
* Do not copy the approximately 17 Geometry files into grammar.
* Make the interface small enough that a future adapter consists mainly of definitions and applications of StrucDual theorems.
* If that adapter becomes necessary, first port/bump StrucDual to v4.33.1 and test it independently; then pin a compatible commit as a Lake dependency.

A Lake dependency does not provide an independent Mathlib universe with a different version. Combining these repositories means choosing and checking a common toolchain/dependency graph.

**Crucially:** an interface theorem may honestly be dotted as conditional on a tubular model. It must not be presented as a proof that the interface is inhabited in the paper’s general setting.

---

## 2. Fix the normalization before formalizing anything else

The paper currently uses two incompatible conventions.

Its definition
\[
D_\perp^rF=\sum_{|b|=r}\frac{\partial^bF}{b!}(du)^b
\]
is the **normalized homogeneous Taylor tensor**, corresponding to \(D^rF/r!\).

But `eq:per_stratum_expansion_coordfree` puts another \(1/r!\) in front of its pairing. The subsequent multi-index identity also omits multinomial coefficients.

Use two explicitly named objects in Lean:
\[
J_r(F)=D^r(F\circ\Phi_s)(0),\qquad
T_r(F)=\frac1{r!}J_r(F).
\]

I recommend keeping `defn:normal_diff` as the definition of \(T_r\), and changing the coordinate-free expansion to
\[
\mathcal Z_n
=\sum_{r\ge0}\int_S\langle T_r(F),M_r(n)\rangle\,d\nu.
\]
Alternatively redefine \(D_\perp^r\) to mean \(J_r\), retaining the external factorial. Either choice works; mixing them does not.

The exact component formula to formalize is
\[
\boxed{
\frac1{r!}\,M_r(J_r)
=
M_r(T_r)
=
\sum_{|b|=r}\frac{\partial^bF(0)}{b!}\,\widetilde M_b.
}
\]

This is one of the most valuable new bridge theorems.

---

## 3. Minimal mathematical interface

Use a finite-dimensional real normed space for the algebraic/analytic core. Require an inner product only for the embedded realization.

Conceptually:

```lean
-- Proposed interface, not claimed existing declaration names.
S : Type*
E : Type*
N : S → Submodule ℝ E
Phi : (s : S) → N s → M
F : M → ℝ
```

Only a germ of `Phi s` near zero matters for derivatives. A total map with hypotheses on an open fibre domain is adequate; locality lemmas should establish independence of extensions.

Define
```lean
rawNormalJet s r :=
  iteratedFDeriv ℝ r (fun n : N s => F (Phi s n)) 0

normalTaylorForm s r :=
  (r.factorial : ℝ)⁻¹ • rawNormalJet s r
```

Use symmetric continuous multilinear forms, implemented as a subspace of `ContinuousMultilinearMap`, or initially use unrestricted multilinear forms and prove symmetry separately under sufficient regularity.

A local frame is a family
```lean
frame s : V ≃L[ℝ] N s
```
on a base patch. A change of frame is a continuous linear equivalence of `V`, varying with the base.

Do **not** require a measurable structure on the entire dependent normal total space in the first implementation. Perform measure theory in fixed-fibre trivializations, push fibre measures through `frame s` pointwise, and prove measurability/integrability of the resulting scalar pairings in those presentations.

For smoothness, prove a separate local theorem: a jointly smooth pulled-back function has locally smooth fibre Taylor coefficients in a smooth frame. Pointwise compatibility alone does not prove the “smooth section” assertion.

---

## 4. What makes each label honestly dottable?

All theorem names below are proposed. The displayed identities describe the required statements, not guaranteed compiling signatures.

### `lem:normal_deriv`

Prove both:

1. **General linear-frame covariance**
   \[
   J_r(f\circ L)=L^*J_r(f).
   \]
   This largely reuses `normalJet_comp_linear` and its family version.

2. **Labelled diagonal component invariance.** If \(u'_i=g_i(s)u_i\), then
   \[
   a'_b(s)=\Big(\prod_i g_i(s)^{-b_i}\Big)a_b(s),
   \qquad
   P'_b(s)=\Big(\prod_i g_i(s)^{b_i}\Big)P_b(s),
   \]
   hence \(a'_bP'_b=a_bP_b\), where \(a_b=\partial^bf/b!\).

Also prove local smoothness under explicit joint smoothness hypotheses.

**Scope:** compatible local representatives of a smooth section; no Mathlib symmetric-power bundle object. General \(GL(k)\) changes preserve the entire degree-\(r\) form, not each labelled \(b\)-component.

**Mirror:** a local-representative convention suffices; an embedded convention is unnecessary for this theorem.

### `defn:normal_diff`

Define `normalTaylorForm` and prove:

* degree zero is restriction to the zero section;
* fibre-frame covariance;
* independence from the chosen extension outside a neighbourhood of zero;
* for the additive Euclidean realization, agreement with the ambient derivative restricted to \(N_s\).

**Scope:** a family of symmetric forms with local compatibility and regularity, not a constructed bundle section. Dependence on \(\Phi\) remains explicit.

**Mirror:** fix the factorial convention and state the local-representative implementation.

### `eq:decomp_nx`

At a point, take independent covectors \(\ell_i\in E^*\) and
\[
T=\bigcap_i\ker\ell_i,\qquad C=T^\circ,\qquad L_i=\operatorname{span}(\ell_i).
\]
Prove that the sum map
\[
\prod_i L_i\longrightarrow C
\]
is a linear equivalence. For finite indices this is the finite direct sum.

Prove invariance of each line under \(\ell'_i=g_i\ell_i\), \(g_i\ne0\). Connect to defining equations by a derivative lemma for \(u'_i=g_i u_i\) on \(u_i=0\).

In an inner-product realization, identify \(C\) with \((T^\perp)^*\). Optionally prove the pointwise exact sequence using inclusion and orthogonal projection:
\[
\ker(\operatorname{proj}_{T^\perp})=T,\qquad
\operatorname{proj}_{T^\perp}\text{ is surjective}.
\]

**Scope:** fibrewise conormal splitting and overlap compatibility, not a short exact sequence of vector bundles.

**Important:** compatibility of the *intersection’s* tangent space does not identify the individual divisor lines. You need labelled individual divisor data, not just an LCI atlas for their intersection.

### `eq:decomp_sym_nx`

Avoid constructing algebraic tensor-product bundles. Prove the equivalent **weight-space decomposition of symmetric multilinear forms**.

For a conormal basis \(\ell_i\), define \(P_b\) to be the symmetric form whose diagonal polynomial is
\[
P_b(n,\ldots,n)=\prod_i\ell_i(n)^{b_i}.
\]
For \(|b|=r\), prove:

* the \(P_b\) form a basis of symmetric \(r\)-forms;
* the lines \(W_b=\operatorname{span}(P_b)\) give a direct-sum decomposition;
* \(W_b\) is unchanged by rescaling the labelled \(\ell_i\);
* the Taylor tensor has components \((\partial^bf/b!)P_b\).

**Scope:** the symmetric-form realization of the displayed decomposition. It does not construct \(\bigotimes_i\operatorname{Sym}^{b_i}L_i\) as bundle objects.

**Mirror:** explicitly say this dot verifies the equivalent fibrewise symmetric-form decomposition. A multinomial identity alone is not enough to dot the asserted isomorphism.

### `eq:pushforward_char` and `eq:pushforward_local`

Use measures.

For a measurable projection \(p\) and measure \(\Omega\), prove the pushforward integral identity with the relevant integrability hypotheses:
\[
\int f\,d(p_*\Omega)=\int f\circ p\,d\Omega.
\]

For a presentation
\[
d\Omega(s,u)=c(s,u)\,d\lambda(u)\,d\nu(s),\qquad c\ge0,
\]
prove
\[
\int H\,d\Omega
=
\int_S\left(\int H(s,u)c(s,u)\,d\lambda(u)\right)d\nu(s).
\]

Use nonnegative `lintegral` statements first, and integrable real-valued statements second.

**Scope:** pushforward of measures and weighted Fubini, not construction or smoothness of manifold densities. Equality of measures can be characterized by measurable tests; uniqueness from compactly supported smooth tests is a separate theorem.

**Mirror:** a measure-realization sentence is required.

### `eq:dressed_moment`

Define the actual fibre measure, including the domain:
\[
d\eta_{s,n}(u)
=
1_{D_s}(u)|u|^h e^{-nK_s(u)}c(s,u)\,du.
\]
Define \(\widetilde M_b(s,n)=\int u^b\,d\eta_{s,n}\).

Prove the density Taylor identity
\[
\widetilde M_b
=
\sum_\delta a_\delta M_{b+\delta}
\]
only under hypotheses that justify Taylor equality and interchange with the integral—for example
\[
\sum_\delta\int
|a_\delta(s)u^{b+\delta}|\,d\eta_{\mathrm{bare},s,n}<\infty.
\]

The bare moments must use the **same domain and bare measure**. They may still depend on \(s\); independence requires another certificate.

**Scope:** exact convergent identity under summability, or finite Taylor identity with an explicit integrated remainder. Not an infinite Taylor theorem for arbitrary smooth \(c\).

### `eq:tubular_expansion`

First prove the exact finite identity
\[
\mathcal Z_n
=
\sum_{r=0}^{R}\int_S M_{s,n,r}(T_r(F)_s)\,d\nu(s)
+
\int_S\int R_R(s,u)\,d\eta_{s,n}(u)\,d\nu(s).
\]

Then prove an infinite equality under joint absolute summability:
\[
\sum_r\int_S\int |T_r(F)_s(u,\ldots,u)|\,d\eta_{s,n}\,d\nu<\infty.
\]

**Scope:** a Taylor–moment identity. To dot the literal asymptotic symbol, additionally connect it to an existing quantitative asymptotic theorem and state its ordering/remainder convention. Normal degree alone is not an asymptotic scale.

### `eq:moment_tensor_defn`

On each normal fibre, reuse `momentFunctional`:
\[
M_{\eta,r}(A)=\int A(n,\ldots,n)\,d\eta(n),
\qquad
\|M_{\eta,r}\|\le\int\|n\|^r\,d\eta.
\]

Restrict to symmetric forms. Prove the frame transport theorem for linear equivalences between possibly different fibre spaces:
\[
M_{L_*\eta,r}(A)=M_{\eta,r}(L^*A).
\]

**Scope:** a continuous functional on symmetric covariant forms, not an explicitly constructed element of an algebraic \(\operatorname{Sym}^r N_s\). In finite dimension this is the appropriate dual realization.

**Mirror:** say so. Do not claim smooth dependence on \(s\) from pointwise moment existence.

### `eq:per_stratum_expansion_coordfree`

Combine the previous pairing, scalar measurability/integrability, measure transport, and Taylor convergence. Prove invariance under a family of fibre-frame changes transporting **all** fibre measure data.

The key component theorem is the boxed factorial identity above, followed by its base-integrated version.

**Scope:** conditional on the chosen tubular pullback and certified fibre-measure presentation. No tubular-independence, nonlinear-coordinate tensoriality, or automatically monomial phase.

### `rem:reduce_to_box`

Prove a localization lemma:

If a fibre measure is supported in a fixed box and \(\kappa=1\) almost everywhere on its support, insertion of \(\kappa\) and restriction to that box do not change the pairing.

Then provide a **finite collection of trivialized presentations**, each satisfying the support and transport certificates, and sum their identities.

**Scope:** certified local reduction to boxes. Not “compact projected support implies one trivialization,” and not the subsequent smooth-Taylor-to-finitely-many-asymptotic-terms assertion without an additional remainder theorem.

---

## 5. Corrections and traps that are load-bearing

### Geometry

* **Individual divisor lines:** equality of the simultaneous zero set gives equality of total tangent/conormal spaces, not a labelled splitting.
* **Gradients are not the dual normal coordinate frame.** The gradients \(\nabla u_i\) generally are not orthonormal. Construct the frame dual to \(du_i|_{N_s}\); do not silently use the gradients themselves.
* **No regularity from `N : S → Submodule ℝ E`.** Smoothness and measurability need local frame hypotheses or separate certificates.
* **Nonlinear tubular changes:** generally change higher Taylor coefficients. Tangential mixing can change even first normal derivatives of arbitrary observables. An intrinsic leading-jet theorem needs genuine vanishing along the stratum, such as the appropriate \(I^r\) condition—not just a pointwise assertion at one base point.

### Analyticity and phase normal form

* Smoothness gives finite Taylor expansions with remainders, not convergent infinite Taylor series.
* An analytic tubular chart does not automatically provide the particular uniform holomorphic bounds consumed by grammar’s summability engine.
* Absorbing a positive unit in \(K=\varepsilon(v,u)u^{2k}\) is generally a **nonlinear** change in \(u\). It need not preserve an already chosen tubular parametrization or glue as a vector-bundle frame change.
* Treat monomial phase and analytic-amplitude bounds as `ChartPresentation`-style certificates. Do not derive them from an arbitrary orthogonal tube.

### Cutoffs and boxes

* A smooth compactly supported cutoff is not generally analytic in normal variables.
* Compact support may require finitely many trivializations; shrinking one patch cannot keep arbitrary compact support inside it.
* A function in \(C_c^\infty(\mathbb R^k)\) supported in a half-box cannot equal one at a boundary point such as \(u_i=0\). Boundary charts require a relative/corner formulation or restriction of a cutoff defined across the boundary.
* Positive and symmetric boxes must be separate cases. Under \(u_i\mapsto-u_i\), a positive box also changes its sign chamber.
* With the written weight \(|u_i|^{h_i}\), the **bare** symmetric moment vanishes when \(\gamma_i\) is odd—not when \(h_i+\gamma_i\) is odd. A non-even dressing can destroy that vanishing.

### The paper’s leading-density claim is false as stated

The conclusion
\[
\widetilde M_\gamma=c_0M_\gamma+\text{subleading}
\]
does not follow in general. A correction in a non-minimizing coordinate can change the leading coefficient.

Also, increasing one minimizing coordinate need not increase the minimum exponent when there is a tie; it may instead reduce logarithmic multiplicity.

Do not formalize these sentences as targets. Replace them by statements tracking exponents **and** multiplicities using the existing moment theory.

### Measures and densities

* Use nonnegative weights for `withDensity`; keep signed observables in the integrand.
* A compactly supported cutoff produces a nonnegative density, not an everywhere strictly positive one.
* Conditional probability measures are defined only almost everywhere, with choices on zero-mass fibres. A smooth, everywhere-defined conditional family is additional structure.
* “Fibrewise compact support” alone is insufficient for all claimed smooth pushforward properties; properness/local uniform control matters.
* Under a frame change, transport the complete measure, including Jacobians, domain, phase, and cutoff. The displayed bare monomial factor is not separately invariant.
* It is simpler initially to use an arbitrary base measure and **unnormalized** fibre measures. If reproducing the paper’s marginal/conditional convention, prove its cancellation separately, treating zero marginals explicitly.

### Lean engineering

* Make the core generic in finite-dimensional real normed spaces. Specialize to an inner-product space only for orthogonal complements.
* `Fin d → ℝ` and `EuclideanSpace ℝ (Fin d)` have different norm presentations. Connect them explicitly rather than expecting definitional equality.
* Use finite products for finite direct sums where convenient.
* Keep the base and fibre universes generic, but do not introduce a dependent measurable total space until it is actually needed.
* Handle \(r=0\), \(k=0\), and zero-mass fibres from the start; they expose normalization and empty-product errors early.

---

## 6. Ranked programme: eight units

Names below are intended deliverables, not claims about current Mathlib declarations.

### 1. Chosen-normal Taylor forms and frame independence — **first honest dot**

**Deliverables**

* `normalTaylorForm`
* `normalTaylorForm_comp_frame`
* `normalTaylorForm_zero`
* germ-locality
* local smoothness of coefficients under joint smoothness assumptions

**Inputs:** `iteratedFDeriv`, existing `normalJet_comp_linear`, `normalJet_comp_linear_family`, Mathlib’s linear-composition and iterated-derivative regularity results.

**Dots:** `defn:normal_diff`; the full-form portion of `lem:normal_deriv`. Add the diagonal component dot after Unit 3.

**Non-claim:** existence of a tubular neighbourhood or a constructed bundle of sections.

This is the first unit because it immediately formalizes an intrinsic object for a **chosen** normal model, rather than merely setting up infrastructure.

### 2. Fibrewise conormal exactness and labelled line splitting

**Deliverables**

* annihilator of \(\bigcap\ker\ell_i\) equals their span;
* sum of independent conormal lines is a linear equivalence;
* line invariance under changes of defining equations by units;
* orthogonal-normal/annihilator identification.

**Inputs:** finite-dimensional linear algebra, spans, kernels, duals, inner-product orthogonal decomposition; `HasFDerivAt` product rule.

**Dots:** scoped `eq:decomp_nx`; optionally the pointwise exact sequence.

**Non-claim:** quotient vector bundles or regularity of an arbitrary submodule field.

### 3. Symmetric weight decomposition and factorial bridge

**Deliverables**

* symmetric multilinear-form subspace;
* monomial basis indexed by \(\sum b_i=r\);
* canonical weight lines under diagonal changes;
* `normalTaylorForm_eq_sum_multiIndex`;
* diagonal component invariance.

**Inputs:** finite-dimensional multilinear algebra, permutation invariance, finite multinomial combinatorics. Reuse grammar’s jet forms.

**Dots:** `eq:decomp_sym_nx`, completion of `lem:normal_deriv`.

**Non-claim:** general symmetric-power bundle infrastructure.

**Local stop:** if this begins demanding that infrastructure, retain the explicit multinomial bridge and leave `eq:decomp_sym_nx` undotted.

### 4. Normal-fibre moments and invariant contraction

**Deliverables**

* moments on `N s`;
* norm bounds;
* covariance under frame equivalences;
* invariant Taylor–moment contraction.

**Inputs:** existing `momentFunctional`, moment–jet invariance, `moment_contraction`.

**Dots:** `eq:moment_tensor_defn`.

**Non-claim:** an algebraic tensor-power implementation or smooth moment sections.

### 5. Weighted fibre integration and dressed moments

**Deliverables**

* projection pushforward characterization;
* weighted Fubini;
* normalization/cancellation for conditional versus unnormalized fibres;
* dressed moment definition;
* density-series interchange under explicit absolute summability.

**Inputs:** `Measure.map`, `Measure.withDensity`, product integration/Tonelli/Fubini; existing CXXXVI and dressed-measure results.

**Dots:** measure versions of `eq:pushforward_char`, `eq:pushforward_local`, `eq:dressed_moment`.

**Non-claim:** smooth density pushforward or a general disintegration theorem.

### 6. Coordinate-free Taylor–moment expansion

**Deliverables**

* finite expansion with exact integrated remainder;
* infinite expansion under joint absolute summability;
* integrated multi-index/factorial bridge;
* invariance under transported fibre presentations.

**Inputs:** Units 1, 3–5; existing CXII Taylor–moment series and summability machinery.

**Dots:** corrected identity versions of `eq:tubular_expansion` and `eq:per_stratum_expansion_coordfree`.

**Non-claim:** normal-degree asymptotic ordering. Asymptotic dots require an explicit additional connection to the existing quantitative expansion.

### 7. Certified finite box reduction and grammar application

**Deliverables**

* support-restriction/cutoff insertion lemma;
* finite trivialized-cover summation;
* adapter from `ChartPresentation` to the coordinate-free pairing;
* corollary of `AdaptedStrataData.cutoffExpansion` stated through those pairings.

**Inputs:** existing chart transport, CXXXVI, CXII, CXIII.

**Dots:** corrected `rem:reduce_to_box`; asymptotic expansion dots to the extent the inherited theorem proves exactly their stated conclusion.

**Non-claim:** production of adapted charts, analytic cutoffs, or absorption of phase units.

### 8. Optional StrucDual realization

**Deliverables**

* a v4.33.1-compatible adapter from `NormalTubularChart`;
* additive realization `Phi s n = s + n` on the tube;
* inverse/domain certificates;
* agreement of interface jets with restricted ambient jets;
* analytic local-coefficient corollaries where available.

**Inputs:** upgraded StrucDual geometry.

**Non-claim:** a tubular theorem inside an arbitrary embedded manifold, or global monomialization.

This unit should not block Units 1–7.

---

## 7. Stop rule and mirror convention

Set the boundary now:

> No quotient-bundle library, symmetric-power bundle library, general manifold integration library, or new global tubular theorem in this programme.

Stop a unit if it requires one of those projects. Publish the conditional/local theorem already obtained, state its hypotheses in the mirror, and leave the stronger label undotted.

A suitable mirror convention is:

> **Formalization convention.** The formalized coordinate-free identities use a chosen normal-family presentation. Covariant symmetric tensors are represented by symmetric continuous multilinear forms, contravariant moment tensors by continuous functionals on these forms, and sections by compatible local representatives with the stated regularity. Integration is represented by measures and certified fibre presentations. Euclidean realizations use the chosen ambient orthogonal normal geometry. These results do not assert existence of a general manifold tubular neighbourhood or independence from the chosen tubular map.

That convention is honest only when accompanied by the concrete transformation, decomposition, and integration theorems above. With those in place, the output is a meaningful formalization of the subsections’ mathematical mechanism—not a simulation of their vocabulary.
