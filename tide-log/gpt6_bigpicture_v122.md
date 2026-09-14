## Recommendation

**Do not target (i), with ordinary integrable kernel fields, as the next unconditional theorem. In general that statement is false.** The smooth engine naturally produces **renormalized stratum functionals**, not necessarily integrals against ordinary moment-coefficient fields.

There are two separate issues:

1. At a crossing, a fixed asymptotic order need not involve only finitely many normal Taylor terms of the *deepest-stratum* moment expansion.
2. Reorganizing the contributions among all strata can give finite normal-jet dependence, but the resulting tangential coefficient functionals can be **finite-part distributions**, rather than integrable densities.

I recommend landing:

- first, **finite-jet determination**, a precise version of (iv);
- next, an explicit **finite, chart-local, renormalized strata formula**, stronger than merely restating the definition because it separates observable jets from density data;
- finally, if desired, a global **distribution-valued normal-jet pairing**.

The ordinary-kernel version of the paper’s formula should remain a conditional specialization, not the unconditional target.

---

## 1. Two tests that determine the correct statement

Work on the positive unit square with \(K=x^2y^2\).

### 1.1 Observation (A) is false at a crossing

For every integer \(M>0\),
\[
\int_0^1\int_0^1 x^M e^{-n x^2y^2}\,dy\,dx
\sim \frac{\sqrt\pi}{2M}n^{-1/2}.
\]

Thus arbitrarily high \(x\)-Taylor terms at the corner contribute at the **same** exponent \(\mu=1/2\).

The reason is that a monomial moment has candidate exponents
\[
\frac{m_i+h_i+1}{2k_i}
\]
from individual active coordinates. Fixing \(\mu\) bounds the Taylor degree in a coordinate responsible for that exponent, **not in every active coordinate**.

Consequently:

- a fixed coefficient of a full corner-moment expansion need not be a finite sum of corner normal derivatives;
- a finite-jet description **along the entire divisor** is nevertheless possible: \(x^M\) is visible in the value of the observable along \(y=0\).

This distinction is essential. For smooth observables, an infinite Taylor series at the corner is not an alternative: it need not reconstruct even the leading coefficient.

### 1.2 Ordinary finite-jet kernel fields generally do not exist

Choose a smooth cutoff \(\chi\), equal to \(1\) near \(0\), supported in \([0,1)\), and put
\[
f_\varepsilon(x,y)=\chi(x/\varepsilon)\chi(y/\varepsilon).
\]
Scaling gives
\[
I_n[f_\varepsilon]=\varepsilon^2 I_{n\varepsilon^4}[\chi\otimes\chi].
\]
Since the \(n^{-1/2}\log n\) coefficient is \(A=\sqrt\pi/4\),
\[
c_{1/2,0}(f_\varepsilon)
=
c_{1/2,0}(\chi\otimes\chi)+4A\log\varepsilon.
\]
This is unbounded as \(\varepsilon\downarrow0\).

But, using the ordinary coordinate normal directions:

- all positive-order normal derivatives of \(f_\varepsilon\) vanish along either open axis;
- its values along those axes are bounded by \(1\);
- its corner jet is the same constant jet for every \(\varepsilon\).

An ordinary finite-jet integral formula with fixed integrable coefficient fields on the axes and corner would therefore be uniformly bounded on this family. Contradiction.

The missing object is familiar:
\[
\int_0^1 \frac{f(x,0)-f(0,0)}{x}\,dx,
\]
or its higher-order analogue. This is a convergent **subtracted integral**, but it is not integration of \(f(x,0)\) against an integrable density. It is a finite-part functional with boundary counterterms.

This directly explains why `remList` cannot simply be removed.

---

## 2. The right unconditional theorems

### Theorem A: finite-jet determination along the resolved divisor

Fix the resolution, prior, chart decomposition and coefficient index. Let `Obs` be the existing vector space of admissible smooth observables, and write
\[
T_{\mu,q}(f)=c_{\mu,q}(f).
\]

A suitable first statement is:

```lean
theorem coeff_eq_of_equal_resolved_finiteJets
    (μ : ℝ) (q : ℕ) :
    ∃ R : ℕ, ∀ f g : Obs,
      EqualJetsOn R resolvedDivisor
        (pullbackObs f) (pullbackObs g) →
      intrinsicCoeff f μ q = intrinsicCoeff g μ q
```

Here `EqualJetsOn` should initially mean equality of **full chart jets through order `R`**, on the relevant closed divisor faces in the compact chart supports. This avoids prematurely introducing higher conormal derivatives as intrinsic tensors.

Then derive the requested original-space version:

```lean
theorem coeff_eq_of_equal_finiteJets
    (μ : ℝ) (q : ℕ) :
    ∃ R : ℕ, ∀ f g : Obs,
      EqualAmbientJetsOn R (D ∩ K ⁻¹' {0}) f g →
      intrinsicCoeff f μ q = intrinsicCoeff g μ q
```

The implication is by finite-order chain rules and multiplication by the fixed density.

**Important scope:** this concerns restrictions of ambient smooth observables. For domains with boundary, retain whatever ambient-extension convention the smooth producers already use.

An equivalent algebraic interface is factorization through the **range of the finite-jet restriction map**:

```lean
∃ R, ∃ L : LinearMap.range (resolvedJetRestriction R) →ₗ[ℝ] ℝ,
  ∀ f, intrinsicCoeff f μ q =
    L ⟨resolvedJetRestriction R f, by ...⟩
```

Using the range records compatibility of jets at intersecting faces automatically.

### Theorem B: explicit renormalized chart-strata formula

This is the appropriate next “strata integral” theorem.

Write the fixed density, including the chart weight, as \(D\), and the pulled-back observable as \(f\). For a face \(J\), let \(K=J^c\), and define
\[
d_{J,\ell}(s,w)
=
\partial_J^\ell D(s,0_J,w),\qquad
u_{J,a}(f)(s,w)
=
\partial_J^a f(s,0_J,w).
\]

Define a linear functional on compatible smooth face fields:
\[
\begin{aligned}
\mathcal B_{J,a,\mu,q}(u)
={}&
\int_s
\sum_{\substack{m<p_J\\a\le m}}
\frac{1}{(m-a)!}
\sum_{j=q}^{|J|-1}
C_{J,m,\mu,j}(s)\binom jq\\
&\qquad\qquad\cdot
\int_{(0,b]^K}
R_K^p\!\left[d_{J,m-a}\,u\right](s,w)\,
w^{h_K}(w^{2k_K})^{-\mu}
\bigl(\logSum_K(w)\bigr)^{j-q}\,dw\,d\nu(s).
\end{aligned}
\]
Here \(C\) is the existing `faceCoef`. Empty-face conventions should follow the engine, with any zero contribution proved explicitly.

Then:
\[
\boxed{
c_{\mu,q}(f)
=
\sum_{\text{chart pieces}}\sum_J\sum_{a<p_J}
\frac1{a!}\,
\mathcal B_{J,a,\mu,q}\bigl(u_{J,a}(f)\bigr).
}
\]

This has:

- finitely many observable normal jets;
- density-only linear functionals;
- explicit, convergent stratum integrals;
- all weight derivatives absorbed into the density data;
- the necessary tangential subtraction retained.

Call this a **renormalized strata-integral formula**, not an ordinary kernel-field formula. The face fields must have compatible extensions to deeper faces: `R_K^p` uses those boundary traces.

### Theorem C: global distributional form

After additional geometry, the conceptual global statement is
\[
c_{\mu,q}(f)
=
\sum_I\sum_{r\le R}
\frac1{r!}
\left\langle
\mathcal B_{I,r,\mu,q},
j_{\perp,I}^r(f\circ\pi)
\right\rangle_{\mathrm{ren}}.
\]

Here \(\mathcal B\) is distribution-valued, and the pairing includes the extension/subtraction data at deeper strata.

An even cleaner initial global statement is:

> \(T_{\mu,q}\) is a finite-order distribution supported on the resolved zero divisor.

A finite-order seminorm estimate should accompany that claim; algebraic finite-jet dependence alone does not establish continuity.

---

## 3. What is and is not the paper’s claim?

| Candidate | Assessment |
|---|---|
| **(i) Ordinary finite-jet kernel fields** | Stronger than what the smooth engine generally supports; false without extra hypotheses or a renormalized interpretation. |
| **(ii) Cutoff-independent kernels** | Not justified. Normal-constant cutoffs remove some derivative terms, but do not make per-stratum kernels canonical. The paper itself allows partition-dependent stratum contributions. |
| **(iii) Chart-local strata formula** | Achievable now. Upgrade it by separating observable jets from density-only renormalized functionals. |
| **(iv) Finite-jet determination** | Achievable and intrinsic. It is substantive coordinate-free content, but not itself a moment-kernel representation. |

The paper’s displayed formula is a **moment-level expansion**, with moments still depending on \(n\). Extracting a fixed coefficient from it requires a separate theorem about exchanging or reorganizing the normal expansion and the moment asymptotics.

At crossings, “replace the smooth normal series by finitely many terms at each \((\mu,q)\)” is not that theorem.

---

## 4. Proof strategy

### First theorem: use the engine directly

For fixed \(\mu\), choose the existing admissible depth \(p\).

Every term is built from:

1. a normal derivative on a nonempty divisor face;
2. finitely many complementary Taylor subtractions;
3. an integral of the resulting remainder.

Expanding `remList` as a finite combination of Taylor projections shows that its inputs use only finitely many ambient derivatives evaluated on divisor faces, possibly deeper ones.

Therefore sufficiently many equal jets on the divisor imply equality of every coefficient term.

A conservative chartwise bound of the form
\[
R_{\text{chart}}\le \sum_i p_i
\]
should be available; the exact bound should follow from a trace-dependency lemma for the implementation of `remList`. Take the maximum over the finitely many chart pieces.

This needs neither a second expansion nor coefficient uniqueness, except to identify the chosen producer’s coefficient with the intrinsic one.

### Renormalized formula: finite Leibniz reorganization

Use
\[
\frac1{m!}\partial_J^m(Df)
=
\sum_{a\le m}
\frac1{a!(m-a)!}
(\partial_J^{m-a}D)(\partial_J^a f).
\]

Then use linearity of `remList`, integration, and finite sums.

**Do not try to commute `remList` past the product.** Keep
\[
R_K^p[d\,u]
\]
inside the density-only functional acting on \(u\). Removing it is precisely the unjustified step that would turn a finite-part functional into an ordinary density.

### Where the weight derivatives go

They occur in
\[
\partial_J^{m-a}
\bigl(\omega\,|j|\,(\mathrm{prior}\circ\psi)\bigr).
\]
They are fixed data, independent of the observable, and belong in \(\mathcal B\).

There is no need to eliminate them. A normal-constant cutoff can eliminate derivatives of that cutoff in a specified normal region, but:

- the original chart weight may still have normal derivatives;
- finite-part behavior at deeper strata remains;
- per-stratum terms remain choice-dependent.

### Second expansion plus uniqueness

Observation (B) is correct **once the second expansion has been established**. It is an excellent comparison theorem, not a mechanism for manufacturing the missing kernel representation.

Use it later for:

- comparing two renormalization or localization choices;
- identifying a conditional ordinary-kernel construction with the intrinsic coefficient;
- connecting to the analytic route on their common domain.

For the immediate smooth theorem, direct finite algebra is substantially cheaper.

---

## 5. Chart-local adapted partitions and global geometry

Observation (C) is broadly right as a localization strategy, subject to stating the exact plateau/support properties rather than importing the paper’s global lemma verbatim.

A finite chart-local localization can separate coordinates bounded away from zero from coordinates allowed to approach zero. It needs no compatible global normal fibres.

But it does **not** turn product phases into uniformly coercive normal phases. A neighborhood of a crossing still contains regions approaching its shallower faces. Hence its full fibre moments retain sub-face contributions.

Thus:

- chart-local localization is enough for chart-local renormalized formulas;
- it does not prove ordinary finite-jet kernels;
- a global tubular construction is needed only if the theorem explicitly uses a chosen global normal-jet/tensor realization;
- even global tubes do not eliminate the finite-part obstruction.

Observation (D) should therefore be weakened: remainders are not inevitable in every normal-crossings coefficient—for example, the top log coefficient may be a simple deepest-stratum evaluation—but boundary subtraction or an equivalent distributional mechanism is unavoidable in general.

---

## 6. Kernel interfaces and overlap

### RN aggregation is not the missing step

The analytic construction works because its local coefficient objects are already integrable fields against positive base measures.

Here the local object can instead be
\[
u\longmapsto\int \frac{u(w)-u(0)}w\,dw.
\]
No Radon–Nikodym weighting turns that into an ordinary integrable field acting on \(u(w)\).

First decide which category the local objects inhabit.

### Recommended interface

Introduce something like:

```lean
structure SmoothRenormalizedMomentData ... where
  order : ℕ
  faceJetSpace : ...
  jetRestriction : Obs →ₗ[ℝ] faceJetSpace
  coefficientFunctional : faceJetSpace →ₗ[ℝ] ℝ
  coefficient_eq :
    ∀ f, intrinsicCoeff f μ q =
      coefficientFunctional (jetRestriction f)
  -- explicit face/remainder representation and bounds
```

Initially let `faceJetSpace` be the range of a concrete finite family of chart trace maps.

Later add:

- continuity bounds;
- pushforward under chart maps;
- compatibility under changes of normal-jet realization;
- a distribution-valued global pairing.

Overlap is handled by **summing weighted local functionals**, just as distributions are summed after localization. No a.e.-disjointness is needed.

Reuse the algebraic coefficient/observable interfaces of `MomentKernelData`, but do not force this into an interface whose defining theorem demands
\[
\int \sum_r \langle j^r f,B_r\rangle\,d\nu
\]
with ordinary integrable fields.

Finite families can of course be encoded in the existing analytic interface when an ordinary-field representation is separately available.

Also record that higher normal derivatives are not automatically canonical sections of `Sym^r N*`: a tubular/connection choice or a jet-bundle formulation is needed. The intrinsic total functional can be canonical while its tensor presentation is not.

---

## 7. Ordered implementation units

These are relative design estimates, not repository-verified line counts.

| Unit | Deliverable / inputs | Size | Main risk |
|---|---|---:|---|
| **1. Face trace dependency** | `remList`/`faceAmp` equality from finite jets on closed divisor faces; fixed depth | M | Mixed derivative bookkeeping and empty-face conventions |
| **2. Intrinsic finite-jet theorem** | Integrate Unit 1 over bases, sum charts, transfer to original observables | M–L | Uniform bounds and pullback jet API |
| **3. Finite-order bound** | Bound coefficient by a compact `C^R` seminorm using `faceAmp_bound` | M–L | Uniform domination over the base |
| **4. Leibniz-separated face formula** | Density-only renormalized functionals \(\mathcal B\), finite observable jet family | L | Multi-index factorial identities and integrability after finite rearrangement |
| **5. Choice comparison** | Equal totals for alternate admissible depths/localizations via uniqueness | S–M | Matching certificate hypotheses |
| **6. Global distributional packaging** | Pushforward and normal-jet/stratum presentation | XL | Distribution and stratified jet infrastructure |
| **7. Ordinary-kernel specialization** | Additional hypotheses guaranteeing integrable local fields; RN globalization | L after suitable hypotheses | Hypotheses must genuinely exclude finite-part obstruction |

**First unit to land:** Unit 1, immediately followed by Unit 2. Avoid adding a new atlas or partition producer before these.

### Regression suite

For \(K=x^2y^2\) on the positive unit square:

1. **Top log coefficient**
   \[
   c_{1/2,1}(P)=\frac{\sqrt\pi}{4}P(0,0).
   \]
   Here \(P\) denotes the full smooth amplitude; separating observable and density gives the corresponding product at the corner.

2. **Shallow-stratum detection**
   \[
   c_{1/2,0}(x^M)=\frac{\sqrt\pi}{2M},\qquad M>0.
   \]
   This prevents an incorrect finite-corner-jet theorem.

3. **Renormalized constant coefficient**
   Compare the engine coefficient to axis-subtraction terms involving
   \[
   \int_0^1\frac{P(x,0)-P(0,0)}x\,dx,
   \qquad
   \int_0^1\frac{P(0,y)-P(0,0)}y\,dy,
   \]
   together with the universal corner constant. Derive normalization from the engine.

4. **Weight Leibniz regression**
   Set \(P=Df\) with a non-normal-constant smooth \(D\); verify the separated formula without imposing `ω_indep`.

---

## 8. Non-claims to record

For finite-jet determination alone:

- no ordinary moment-kernel field has been constructed;
- no per-stratum canonical coefficient has been defined;
- no global adapted partition or tubular system has been produced;
- no claim is made that finitely many corner jets determine a coefficient;
- no smooth Taylor-series reconstruction is used.

For the renormalized strata formula:

- the kernels are **linear functionals on compatible face jets**, not generally integrable tensor fields;
- the subtractions and deeper-face counterterms are part of the formula;
- chart weights and their derivatives are allowed;
- individual face terms depend on charts, depths, and renormalization choices;
- only the total is identified intrinsically by coefficient uniqueness.

**Bottom line:** the unconditional smooth result can be upgraded to finite-jet dependence and an explicit renormalized strata pairing at moderate cost. Upgrading it to the literal ordinary-field version of (i) is not merely unfinished atlas engineering: the \(x^2y^2\) example shows that the proposed statement needs to change.
