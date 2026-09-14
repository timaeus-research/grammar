## Recommendation

Make the first statement of record:

> **For each \((\mu,q)\), the coefficient functional is an intrinsic, compactly supported distribution on the original Euclidean space, with an explicit finite-order bound. Its support lies in the images of the resolved coordinate walls and in the support of the prior. Theorem B gives a finite chart-face presentation of this distribution.**

This is **(a), supplemented by Theorem B**. Subsequently add:

- **(b)** as a chart-face, distribution-valued normal-jet presentation;
- **(d)** first in the weak, test-function sense, then with a separate uniform-remainder theorem if the requisite estimates are audited.

Do **not** construct (c) merely to obtain a nominal “resolved space.” A disjoint union of boxes supplies labels and a carrier, but neither gluing nor intrinsic strata. It does not improve the distribution theorem.

Three corrections to the draft are important:

1. The order certified directly by the estimates is the **maximum of the sums of the rectangular derivative depths**, not the maximum coordinate depth.
2. Compactness of the wall images eliminates the need for global continuity of \(K\) in the support theorem.
3. The chart-face coefficients are **presentation data**, not individually weight- or refinement-independent objects.

---

## 1. Statement of record and Lean-facing interface

Write `E := Fin d → ℝ` and take `Ω : Opens E := ⊤`. Define the coefficient with a variable observable:

```lean
noncomputable def observableCoeff
    (X : BridgeInputs d) (μ : ℝ) (q : ℕ)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) : ℝ :=
  (X.withObs f hf).decomp.coeff μ q
```

The signatures below are proposed interfaces; field projections, coercions, and the finite-order cast should be adjusted to the actual files.

First land proof-independence, additivity, and homogeneity:

```lean
theorem observableCoeff_add ...
theorem observableCoeff_smul ...
theorem observableCoeff_zero ...
```

These should use certificate operations and uniqueness, rather than unfolding the coefficient engine.

### A bound interface that avoids premature supremum infrastructure

Use an elementary predicate initially:

```lean
def JetBound (R : ℕ) (S : Set E) (f : E → ℝ) (M : ℝ) : Prop :=
  ∀ r ≤ R, ∀ x ∈ S,
    ‖iteratedFDeriv ℝ r f x‖ ≤ M
```

Let:

- `coreImage X` be the finite union of images of closed chart boxes;
- `wallImage X` be the finite union of `ψ i '' activeWalls i`;
- `engineOrder X μ` be the maximum, over pieces, of the sum of the engine’s rectangular depth.

The foundational estimate should be:

```lean
theorem observableCoeff_bound
    (X : BridgeInputs d) (μ : ℝ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (M : ℝ),
        0 ≤ M →
        JetBound (engineOrder X μ) (coreImage X) f M →
        |observableCoeff X μ q f hf| ≤ C * M
```

This is already a compact-local finite-order estimate. A sum-of-suprema formulation can be derived later; it need not block the distribution construction.

Then define:

```lean
noncomputable def coeffDistribution
    (X : BridgeInputs d) (μ : ℝ) (q : ℕ) :
    𝓓'(Ω, ℝ)
```

with the essential evaluation theorem:

```lean
theorem coeffDistribution_apply
    (f : 𝓓(Ω, ℝ)) :
    coeffDistribution X μ q f =
      observableCoeff X μ q f f.contDiff
```

Record a distribution-level bound:

```lean
theorem coeffDistribution_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : 𝓓(Ω, ℝ)) (M : ℝ), 0 ≤ M →
        JetBound (engineOrder X μ) (coreImage X) f M →
        |coeffDistribution X μ q f| ≤ C * M
```

Finally:

```lean
theorem dsupport_coeffDistribution_subset :
    dsupport (coeffDistribution X μ q) ⊆
      wallImage X ∩ tsupport X.prior
```

and its corollary:

```lean
theorem dsupport_coeffDistribution_subset_zero_prior :
    dsupport (coeffDistribution X μ q) ⊆
      {x | X.K x = 0} ∩ tsupport X.prior
```

Also record compactness of the distributional support.

### Intrinsicness

Give intrinsicness its own theorem, using equality of the underlying scalar integral functions or certificates. In particular, two bridge presentations of the same phase and prior yield equal distributions.

This equality should not depend on comparing their chart families, face indices, or derivative-order bounds. Those can differ.

---

## 2. Order: use the engine depth first

### The safe order

Define initially
\[
R_{\mathrm{eng}}(X,\mu)
  =\max_P\sum_{\ell\in\mathrm{Fin}(d_a(P))}p_{P,\ell},
\]
where \(p_P\) is **exactly** the depth used by `smoothCoeff`.

This follows directly from `RectBound`: mixed derivatives with \(\alpha\le p\) can have total order \(\sum_i p_i\).

The proposed
\[
\max_i\max_j\operatorname{chartJetOrder}_{i,\mu,j}
\]
is not justified by this argument. A rectangular bound can require, for example, \(\partial_1^p\partial_2^p f\), whose total order is \(2p\).

### Relation to Theorem A’s order

Prove a small arithmetic/interface lemma:

```lean
theorem engineOrder_le_chartJetTotal :
    engineOrder X μ ≤
      finiteMax (fun i => chartJetTotal X i μ)
```

or equality, if that is what the definitions give.

Then the public theorem may use
\[
R=\max_i\operatorname{chartJetTotal}_i(\mu).
\]

**Do not infer this numerical estimate solely from Theorem A.** Jet determination is an algebraic locality statement; the coefficient estimate needs a quantitative bound. Audit the correspondence between `depthOf`, `cutoffOf`, and `chartJetOrder` explicitly.

The resulting order is an upper bound, not a claim of minimal order. It may be independent of \(q\) even though some coefficients, especially top logarithmic coefficients, have much smaller actual order.

### Domain: smooth test functions

Use `𝓓(Ω, ℝ)` with the finite-order estimate. Do not make extension to `𝓓^{R}` a prerequisite.

I do not know a ready-made Mathlib theorem at the stated pin establishing the required compact-support-controlled \(C^R\) mollification density. The supplied convolution lemmas alone are not that theorem.

Moreover, density in a **fixed** `𝓓^R_K` needs care for arbitrary compact \(K\). The usual approximation argument permits a slightly enlarged compact support. An extension project would need to handle:

1. \(C^R\)-convergence of mollifications;
2. support enlargement inside the ambient open set;
3. independence of approximation;
4. compatibility across compact supports.

That is worthwhile infrastructure, but unnecessary for the standard assertion “a distribution of finite order.”

---

## 3. Infrastructure and the quantitative estimate

### 3.1 Coordinate derivatives versus Fréchet derivatives

The useful general lemma is for a coordinate word, followed by the `pdMulti` corollary.

For a list `l` without duplicates, the number of differentiations is
\[
N=\sum_{i\in l}m_i.
\]
Identify `pdMulti m l f x` with `iteratedFDeriv ℝ N f x` evaluated on the corresponding repeated coordinate vectors, in the appropriate order.

Then derive:

```lean
theorem norm_pdMulti_le_norm_iteratedFDeriv
    (hf : ContDiff ℝ ∞ f) (hl : l.Nodup) :
    |pdMulti m l f x| ≤
      ‖iteratedFDeriv ℝ (∑ i ∈ l.toFinset, m i) f x‖
```

The coordinate vectors have norm one for the usual norm on `Fin d → ℝ`. Handle the empty derivative word explicitly; it is useful throughout the bounds.

Prove the evaluation identity using `deriv`/`fderiv` compatibility and `iteratedFDeriv_succ_apply_left`. Choose the coordinate-word convention to match the recursion rather than introducing an unnecessary permutation theorem.

### 3.2 Scalar coefficient bound

Land a theorem of this shape before involving charts:

```lean
theorem abs_smoothCoeff_le_mul_rectBound
    (admissible : ...)
    (hM : 0 ≤ M)
    (hF : RectBound F p b M) :
    |smoothCoeff F h k β b μ q| ≤
      coeffBoundConstant h k β b μ q * M
```

Here `p` is the actual canonical depth, or an explicit depth in an `AtDepth` version.

Define the constant through finite sums of:

- absolute face coefficients and combinatorial factors;
- factorial factors from `faceAmp_bound`;
- integrals of the **absolute majorants** supplied by the integrability theorem.

This avoids trying to extract a numerical constant from the proposition `Integrable`. Its finiteness is certified by the existing integrability results.

### 3.3 Products and charts

The Leibniz estimate is:

\[
\operatorname{RectBound}(D f,p,b,\,
  2^{\sum_i p_i}M_D M_f),
\]
assuming nonnegative bounds. More precise constants are not needed.

For chart composition, obtain one \(D_i\ge1\) satisfying all required positive-order derivative bounds for \(\psi_i\) on its compact box. Then the supplied chain-rule estimate gives
\[
\|D^r(f\circ\psi_i)(u)\|
 \le r!\,M\,D_i^r
\]
from `JetBound R (coreImage X) f M`.

One technical issue deserves its own lemma: the chart is smooth **on a neighbourhood of the box**, not necessarily globally. Localize the supplied global-looking composition theorem, using local smooth extensions or locality of derivatives. Do not silently assume global `ContDiff ψ i`.

Transfer to orthant coordinates using the affine jet lemma. Multiply by the uniformly bounded density jets, apply the scalar bound, and integrate over the finite-measure compact bases.

### 3.4 Continuity on test functions

On each `𝓓_K`, let
\[
P_R(f)=\sum_{r=0}^{R}
 \operatorname{ContDiffMapSupportedIn.seminorm}(r)(f).
\]
Each derivative value on `coreImage X` is bounded by this sum. Consequently,
\[
|T(f)|\le C P_R(f)
\]
with the **same \(C,R\) for every support compact \(K\)**.

Use the seminorm continuity API to construct the restricted CLM, then `TestFunction.limitCLM` or `continuous_iff_continuous_comp` and `mkCLM`.

This does not require `K` to contain `coreImage X`.

---

## 4. Support: no global continuity of the phase is needed

Let
\[
W_X=\bigcup_i\psi_i(\mathrm{activeWalls}_i).
\]

### First prove geometric helper lemmas

1. `activeWalls i` is compact: it is a closed subset of the compact closed box.
2. `ψ i` is continuous on that box.
3. Therefore `W_X` is compact, hence closed.
4. The monomial identity gives
   \[
   W_X\subseteq\{x:K(x)=0\}.
   \]

These facts suffice even if the full zero set of \(K\) is not closed.

### Vanishing off the wall image

If `tsupport f ⊆ W_Xᶜ`, then at every point of \(W_X\), \(f\) vanishes on a neighbourhood. Local continuity of each chart makes \(f\circ\psi_i\) locally zero at the corresponding wall point. All required jets vanish.

Apply Theorem A against the zero observable, giving:

```lean
theorem isVanishingOn_coeffDistribution_wallImage_compl :
    Distribution.IsVanishingOn
      (coeffDistribution X μ q) (wallImage X)ᶜ
```

Because `wallImage X` is closed, its membership among the closed sets in the definition of `dsupport` yields the desired inclusion directly.

If a convenient general lemma is absent, add the small helper
“closed `S` + `IsVanishingOn T Sᶜ` implies `dsupport T ⊆ S`.”

### Support in the prior

Prove this separately and more cheaply. For a test function supported outside `tsupport prior`,
\[
\mathrm{prior}(x)f(x)=0
\]
everywhere. The scalar integral is identically zero, so uniqueness makes every coefficient zero.

Intersect the two support inclusions.

**Important distinction:** knowing only `W ⊆ {K = 0}` would not justify
`closure W ⊆ {K = 0}` for measurable \(K\). Here the repair is that \(W\) itself is compact and closed.

---

## 5. C5: the honest chart-face theorem

### What can be claimed

The strongest available global, coordinate-free object is \(T_{\mu,q}\) on the original space. There is currently no carrier or transition structure supporting intrinsic global fields
\(\mathcal B_{I,r,\mu,q}\) on resolved strata.

Theorem B already gives the correct algebraic precursor to a chart-face distribution presentation. Upgrade it without inventing a manifold.

For a piece \(P\) and face \(J\), use a Euclidean tangential space containing:

- the inactive/base coordinates;
- the active coordinates in \(K=J^c\).

Call it `FaceSpace P J`. Its compact integration rectangle is `faceBox P J`.

Define
```lean
chartFaceDistribution X P J a μ q :
  𝓓'(⊤ : Opens (FaceSpace P J), ℝ)
```
by integrating `renormFunctional` over the base, inserting a tangential test function using its extension constant in the normal \(J\)-coordinates.

This construction requires three lemmas:

1. **Face factorization:** the renormalized functional depends only on the restriction of `U` to the face, including the tangential differentiations implicit in the remainder.
2. **Tangential finite-order bound:** sufficient order is
   \[
   R_{P,J}\le\sum_{k\in K}p_k.
   \]
   No base derivatives are needed for this bound.
3. **Locality:** support is contained in `faceBox P J`.

The crucial point is that the \(K\)-remainder remains **inside** the face distribution. This is not a finite measure obtained by simply restricting the density.

### Closed box, not automatically open face box

Do not initially claim compact support in the open face box. Nothing stated guarantees that the relevant density vanishes near all box boundaries.

Use the whole tangential Euclidean space, with support in the closed rectangle, or an open neighbourhood containing that rectangle.

### Pairing with normal jets needs a cutoff

The normal jet of \(f\circ\psi_i\) need not be compactly supported on the face, even when \(f\) is compactly supported: the chart map need not be proper.

Thus define a compact-support pairing for these compactly supported face distributions:

- choose a smooth cutoff equal to one near `faceBox`;
- multiply the smooth face function by the cutoff;
- prove independence of the cutoff.

Likewise, use the existing smooth chart extension where needed and prove independence of its choice on the relevant box.

The presentation becomes
\[
T_{\mu,q}(f)=
 \sum_{P,J,a}\frac1{a!}
 \left\langle B_{P,J,a,\mu,q},
   \left.\partial_J^a(f\circ\psi_i\circ T_P)\right|_{v_J=0}
 \right\rangle_c,
\]
with the exact `faceW` normalization from Theorem B. Absorb any remaining fixed conventions into \(B\).

The total order is consistent with C1 because
\[
|a|+\sum_{k\in K}p_k\le\sum_i p_i.
\]

### Multi-indices before “moment tensors”

Use multi-index components as the formal statement. A theorem grouping terms with \(|a|=r\) is inexpensive finite-sum bookkeeping.

Do not add `Sym^r`, tensor sections, or a normal bundle merely to display \(1/r!\). In coordinate components, the \(1/a!\) factors and multinomial factors explain the relation to that notation. Without transition laws, these remain coordinate components of presentation data.

### Independence: what is true and false

**True:**

- the fully reconstructed distribution is independent of bridge presentation;
- consequently its sum of chart-face terms is independent of admissible weights and refinements;
- for an **identical parametrized piece with identical engine data**, splitting its density as \(D=\sum_\ell D_\ell\) gives the corresponding additive splitting of every face functional.

That last theorem is a useful, checkable density-splitting lemma, proved by linearity in the density.

**False in general:**

- individual chart-face distributions are independent of weights;
- arbitrary refinement identifies individual face distributions;
- distributions attached to charts “covering the same stratum” can be compared without transition data.

Two identical charts with weights \(\theta\) and \(1-\theta\) already show why individual terms vary. Do not advertise the density-splitting lemma as general geometric gluing.

---

## 6. The \(n\)-dependent packaging

### Land the weak version early

For nonnegative \(n\), define
\[
Z_n(f)=\int \mathrm{prior}(x)f(x)e^{-nK(x)}\,dx.
\]

First establish the integrability/boundedness facts from the actual bridge hypotheses. The transported monomial cores and phase-gap tail should supply the needed control; measurability of an arbitrary phase plus compact prior alone would not.

Construct `Z_n` as a distribution, then state:

> For every fixed smooth test function, evaluating \(Z_n\) has the scalar expansion whose coefficients are `coeffDistribution X μ q`.

This is the scalar theorem repackaged. Call it a **weak distributional expansion**, explicitly meaning test-function-wise convergence. Do not identify it with convergence in the compact-convergence topology of the distribution type without a uniform argument.

### Strong remainder: valuable, but a separate project

The appropriate target is
\[
|R_{n,A}(f)|
 \le \varepsilon_A(n)\,P_{R_A,Q_A}(f),
 \qquad \varepsilon_A(n)=o(n^{-A}),
\]
or a more explicit
\[
|R_{n,A}(f)|
 \le C_A n^{-B}(\log n)^L P_{R_A,Q_A}(f),
 \qquad B>A.
\]

The draft bound \(C_A n^{-A}P(f)\) is only an \(O(n^{-A})\) bound, not the displayed \(o(n^{-A})\) expansion.

“Constants are `RectBound`-linear” is an excellent starting point, but audit:

1. every constant and threshold is independent of the observable;
2. the common finite candidate exponent set is fixed by the bridge and cutoff;
3. depths used for the remainder, not just coefficients, are controlled;
4. critical logarithms are absorbed using a strict exponent margin;
5. all base integrals preserve the same linear seminorm control.

### Tail

From nonnegativity and exact transport,
\[
\mathrm{tail}\le \mathrm{prior}\cdot\mathrm{vol}.
\]
Therefore the tail is finite and concentrated on `tsupport prior`. One can prove this directly at the measure level; a separate topological-support theorem is unnecessary.

Thus the tail bound needs only the zeroth jet on `tsupport prior`. For the uniform theorem take
\[
Q_A=\mathrm{coreImage}(X)\cup\mathrm{tsupport}(\mathrm{prior}),
\]
which is compact.

A uniform finite-order remainder estimate gives uniform convergence on bounded test sets: the global finite-derivative seminorms are continuous by the same LF restriction argument used in C2. State this implication separately, after proving the estimate.

---

## 7. Ordered units and delegation

| Unit | Deliverable | Size | Main risk |
|---|---|---:|---|
| **C0a** | Observable coefficient linearity and proof-independence | S–M | Certificate/coercion plumbing |
| **C0b** | Compact core/wall images; wall image lies in zero set | S–M | Local chart continuity |
| **C0c** | Coordinate-word / `pdMulti` Fréchet derivative bridge | M–L | Derivative recursion and order conventions |
| **C1a** | `smoothCoeffAtDepth` quantitative bound | M–L | Absolute majorants and finite sums |
| **C1b** | Product, local composition, affine transfer bounds | L | Charts only locally smooth |
| **C1c** | Global coefficient `JetBound` estimate; order comparison | M–L | Matching engine depth to A’s order |
| **C2** | Distribution construction and finite-order theorem | M | Seminorm/LF API |
| **C3** | Wall/prior support and intrinsicness | S–M | Local-zero jet helpers |
| **C4w** | `Z_n` and weak expansion | M | Uniform integrability prerequisites |
| **C5a** | Face factorization and tangential bounds | L | Restriction through the Taylor remainder |
| **C5b** | Face distributions, cutoff pairing, presentation | L–XL | Boundary and extension bookkeeping |
| **C4s** | Seminorm-uniform remainder | L–XL | Quantitative audit of every remainder |
| **C6** | Finite-part regression and engine link | M, then M–L | Explicit cutoff family |

**First to land:** C0a, C0b, and C1a. C1a is the most useful first substantive theorem: it validates the quantitative route without waiting for the Fréchet infrastructure.

**Parallel delegation:**

- derivative specialist: C0c and local composition;
- engine specialist: C1a and remainder audit;
- bridge specialist: C0a, C0b, prior support, order arithmetic;
- distribution specialist: a generic LF construction from a `JetBound` estimate;
- regression specialist: the one-dimensional finite-part example.

**First release boundary:** C2 + C3 + intrinsicness, with Theorem B cited as the presentation. C5 and C4s should not block it.

---

## 8. Regression: isolate the finite part first

The cleanest new regression is the distribution
\[
F(u)=\int_0^1\frac{u(x)-u(0)}x\,dx
\]
on smooth compactly supported functions on \(\mathbb R\).

Prove:

1. the integral exists;
2. linearity;
3. the order-one estimate
   \[
   |F(u)|\le\sup_{x\in[0,1]}|u'(x)|;
   \]
4. support is contained in \([0,1]\);
5. there is **no order-zero bound on one fixed compact support**.

For (5), use uniformly bounded smooth \(u_\varepsilon\), all supported in a fixed compact interval, with \(u_\varepsilon(0)=0\) and \(u_\varepsilon=1\) on \([\varepsilon,1]\). Then
\[
F(u_\varepsilon)\ge\log(1/\varepsilon).
\]
This directly demonstrates “finite order, but not order zero,” without first building signed-measure representation infrastructure.

Next link to CDX using cutoff versions of \(u(x)=x^M\):
\[
F(x^M)=1/M,\qquad M\ge1.
\]
This matches the landed coefficient \(\sqrt\pi/(2M)\).

For the unweighted **quadrant-box** model,
\[
T_{1/2,1}=\frac{\sqrt\pi}{4}\delta_0,\qquad
T_{1/2,0}(u(x))
 =\frac{\sqrt\pi}{2}F(u)+c_{\mathrm{corner}}u(0).
\]
Use cutoffs to turn functions of \(x\) alone into genuine ambient test functions.

Keep this normalization separate from the whole-space smooth-prior model. A full neighbourhood with four orthants changes the leading constant; arbitrary smooth weights also affect the lower coefficient. Do not make the regression depend on a vaguely normalized “product of weights.”

---

## Non-claims

The initial theorem does not assert a minimal distributional order, extension to \(C^R\) test functions, a resolved manifold, intrinsic per-stratum tensors, positive or signed measure coefficients, chart-transition compatibility, or a strong distribution-topology expansion. Each would require additional statements beyond coefficient uniqueness and the present bridge data.

## Eight-sentence paper-facing mirror

For every exponent and logarithmic degree, the asymptotic coefficient defines an intrinsic distribution on the original parameter space.  
This distribution has compact support and admits a finite-order estimate controlled by finitely many derivatives of the observable on a fixed compact set.  
Its support is contained in the prior support and in the images of the resolved coordinate walls, hence in the zero set of the phase.  
No global continuity assumption on the phase is needed for this support conclusion because the wall images are compact.  
The resolved charts express the distribution as a finite sum of normal-jet pairings with tangential finite-part functionals.  
These chart-face functionals are presentation data and may depend on the partition of unity, while their reconstructed sum is intrinsic.  
The scalar asymptotic theorem gives a weak distributional expansion, and a separate uniform remainder estimate upgrades it to uniformity on bounded test sets.  
The normal-crossing example shows why the tangential coefficients must be allowed to be finite-order distributions rather than measures or finite corner-jet functionals.
