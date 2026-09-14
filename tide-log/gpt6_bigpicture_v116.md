## Recommendation

Your real-variable route works, and it fits the existing monomial engine well. I would implement it as:

1. **A finite tensor Taylor identity**, proved by induction over a coordinate list.
2. **One generic “flat complement + monomial face” integration theorem**, using the two-regime estimate.
3. A finite sum over faces and Taylor indices.
4. **Cutoff/depth independence by uniqueness of asymptotic expansions**, before exposing cutoff-free smooth coefficients.
5. A separate parameterized wrapper and then the radius-margin analytic-data map.

The main corrections are: carry the Taylor factorials; require nonempty inner faces when calling the monomial engine; track the common exponent lattice; and do not initially call the coefficients `smoothCoeff F μ q` without recording the Taylor depth.

---

## 1. Verification of the mathematical argument

Assume throughout
\[
d\ge1,\quad b>0,\quad \beta>0,\quad N\ge1,
\]
and the hypotheses on \(h,k\) required by the existing engine. Put \(a_i=2k_i\). Choose integers \(p_i\ge1\) satisfying
\[
p_i+h_i+1>a_iL.
\tag{A}
\]

### 1.1 Tensor Taylor expansion: correct, with factorial bookkeeping

For \(J\subseteq\{1,\ldots,d\}\), write \(K=J^c\), and define the **normalized** face remainder
\[
G_{J,m}(w)
=
\frac1{\prod_{i\in J}m_i!}
\left[
\left(\prod_{i\in K}R_i^{p_i}\right)
\partial_J^mF
\right](0_J,w),
\qquad m_i<p_i.
\]

Then
\[
F(v)=
\sum_J\sum_{m_J<p_J}v_J^mG_{J,m}(v_K).
\tag{1}
\]

This normalization lets you use the coefficient formula in your question unchanged. With your unnormalized definition of \(G\), a factor \(1/\prod_{i\in J}m_i!\) must appear outside each face term, including in the final coefficient formula.

The existing remainder bound gives
\[
|G_{J,m}(w)|
\le
M\,
\frac{\prod_{i\in K}w_i^{p_i}}
{\left(\prod_{i\in J}m_i!\right)
 \left(\prod_{i\in K}(p_i-1)!\right)},
\tag{2}
\]
provided \(M\) bounds the required mixed derivatives on the closed box.

The needed derivative orders fit inside the rectangle
\[
0\le\alpha_i\le p_i.
\]
In particular, the important derivative for this face is
\[
\alpha_i=m_i\quad(i\in J),\qquad
\alpha_i=p_i\quad(i\in K).
\]

**Additional algebra lemmas are needed beyond `pdPow_coordRem`:**

- restriction to one coordinate face commutes with Taylor/remainder in another coordinate;
- \(R_i\) pulls out a factor independent of coordinate \(i\);
- distinct-coordinate Taylor operators commute;
- the finite tensor expansion.

These are elementary but should be treated as explicit U2 deliverables.

### 1.2 Fubini: correct

For nonempty \(J\), the corresponding term becomes
\[
\int_{(0,b]^K}
G_{J,m}(w)w^{h_K}
Z^J_m\!\left(Nw^{a_K}\right)\,dw.
\tag{3}
\]

Prove absolute integrability before applying Bochner Fubini. Here it is easy: the original face amplitude is bounded on a finite box, with the admissible monomial weight, and the exponential is bounded by \(1\).

Empty complements are harmless mathematically: integration over the empty-coordinate space is evaluation at its unique point. It is worth supplying a dedicated simplification lemma for this case.

### 1.3 The two-regime estimate is sufficient

For \(r=|J|\ge1\), let \(D=r-1\). The engine and a finite-sum estimate give
\[
\left|
Z^J_m(t)-
\sum_{\mu<L}\sum_{j=0}^{D}
c^{J,m}_{\mu,j}t^{-\mu}(\log t)^j
\right|
\le C\,t^{-L}(1+|\log t|)^D,
\qquad t>0.
\tag{4}
\]

For \(0<t<1\):

- \(Z^J_m(t)\) is bounded by its unweighted-exponential monomial integral;
- \(t^{-\mu}\le t^{-L}\) for \(\mu<L\);
- \(|\log t|^j\le(1+|\log t|)^D\).

The precise trivial bound is
\[
Z^J_m(t)\le
\prod_{i\in J}\frac{b^{m_i+h_i+1}}{m_i+h_i+1},
\]
under the usual \(m_i+h_i>-1\) hypothesis. Your cruder bound is also available when those denominators are at least \(1\).

After substitution, put
\[
S_K(w)=\sum_{i\in K}a_i\log w_i.
\]
Since \(N\ge1\),
\[
1+|\log(Nw^{a_K})|
\le (1+\log N)(1+|S_K(w)|).
\tag{5}
\]
Thus the absolute outer remainder is bounded by
\[
CMN^{-L}(1+\log N)^D
\int_{(0,b]^K}
\prod_{i\in K}w_i^{p_i+h_i-a_iL}
(1+|S_K(w)|)^D\,dw.
\tag{6}
\]

Condition (A) makes this integral finite.

**So yes: the shrinking-region restriction is completely unnecessary.** Use the global estimate (4) and integrate over the whole outer box. This is cleaner both mathematically and in Lean.

A useful reusable integrability lemma is
\[
\operatorname{IntegrableOn}
\left(
w\mapsto \prod_i w_i^{c_i}
       (1+|\textstyle\sum_i a_i\log w_i|)^D
\right)
(0,b]^K
\]
when every \(c_i>-1\). Prove it by domination by a product of one-dimensional power-log weights and product integration.

### 1.4 Log degree is preserved

Exactly:
\[
(\log N+S)^j
=\sum_{q=0}^j\binom jq(\log N)^qS^{j-q}.
\]

No new \(\log N\) powers arise. Each nonempty face contributes degree at most
\[
|J|-1\le d-1.
\]

The normalized coefficient contribution is
\[
\sum_{j=q}^{|J|-1}
c^{J,m}_{\mu,j}\binom jq
\int_{(0,b]^K}
G_{J,m}(w)w^{h_K-a_K\mu}
S_K(w)^{j-q}\,dw.
\tag{7}
\]

### 1.5 Simplify the fully flat term

Your monomial-engine proof is valid. But an elementary bound is smaller and gives **no logarithmic loss**.

For \(L>0\), choose \(C_L\) with
\[
e^{-x}\le C_Lx^{-L}\qquad(x>0).
\]
Then a fully flat \(G\) satisfies
\[
\begin{aligned}
\left|\int G(v)v^he^{-N\beta v^a}\,dv\right|
&\le MC_L\beta^{-L}N^{-L}
\int_{(0,b]^d}v^{p+h-aL}\,dv\\
&\le C M N^{-L}.
\end{aligned}
\tag{8}
\]

This avoids a candidate-set argument entirely. Keep the monomial-engine proof as an alternative if it is already easier to invoke.

### 1.6 Use the box API

Use `boxCoeff`/`dataBoxCoeff` at the actual side \(b\), with effective parameter \(t=Nw^{a_K}\).

The small-\(t\) extension only needs:

- the box cutoff estimate for \(t\ge1\);
- a trivial box integral bound;
- finiteness of the spectral sum.

Rescaling again introduces
\[
\log(t b^{\sum_{i\in J}a_i})
\]
and another coefficient transformation. There is no benefit if the box theorem already provides the desired \(t\ge1\) bound.

### 1.7 Common lattice bookkeeping

The inner engine uses its face lattice \(Q_J=2\prod_{i\in J}k_i\), whereas the final theorem should use one ambient lattice.

For nonempty \(J\),
\[
Q_J\mid Q_{\mathrm{all}},
\qquad Q_{\mathrm{all}}=2\prod_i k_i.
\]
Hence its exponents embed in the ambient lattice. Prove once that the inner expansion can be padded by zero coefficients to an ambient `latticeBelow`.

Use the off-candidate vanishing theorem where needed to justify the padding. There is no empty-face lattice to manage if the fully flat term is separate.

---

## 2. The essential missing step: canonical coefficients

The formula (7) initially defines
\[
C^{p}_{\mu,q}(F),
\]
not yet a depth-free \(C_{\mu,q}(F)\).

Indeed, its integrals are guaranteed convergent only in the range permitted by \(p\), and its face decomposition explicitly depends on \(p\).

I recommend:

1. Define `smoothCoeffAtDepth p F μ q`.
2. Prove the expansion through every \(L\) satisfying (A).
3. Prove uniqueness of finite real power-log asymptotic expansions.
4. Deduce that two admissible depths give identical coefficients below their common valid cutoff.
5. Define public `smoothCoeff F μ q` using a deterministic depth valid beyond \(\mu\), and prove agreement with every admissible cutoff construction.

For uniqueness, if
\[
\sum_{\mu<L}N^{-\mu}P_\mu(\log N)
=O\!\left(N^{-L}(1+\log N)^{d-1}\right),
\]
take the least exponent with nonzero polynomial and multiply by its power of \(N\). Exponential decay in \(\log N\) forces that polynomial to vanish.

This also proves independence of coordinate enumeration or finite-type reindexing if those choices enter the implementation.

**Do this before wiring U4 to cutoff-free coefficients.** Otherwise depth choices will leak into the downstream interface.

---

## 3. Lean architecture

### 3.1 Index over an arbitrary finite coordinate type

Prefer
```lean
ι : Type*
[Fintype ι] [DecidableEq ι]
F : (ι → ℝ) → ℝ
```
rather than baking `Fin d` into the smooth theorem.

Then a water-filling core instantiates `ι := Nrm I` directly.

The existing monomial engine can be bridged to arbitrary **nonempty** finite types by reindexing to `Fin (n + 1)`. Hide this in one adapter. Do not repeatedly transport individual faces through `Fin` inside the main proof.

Treat the zero-coordinate integral separately if it is needed downstream.

### 3.2 Bundle regularity, not a chosen bounding constant

For the first theorem, inline hypotheses are perfectly reasonable:
```lean
hF    : ContDiff ℝ ∞ F
hderiv :
  ∀ α, (∀ i, α i ≤ p i) →
    ∀ v ∈ closedBox b, |mixedPD α F v| ≤ M
```
together with `0 ≤ M`.

For reuse, bundle \(F\) and its regularity; expose the bound as a proposition such as
```lean
MixedDerivBound p b F M
```
rather than making \(M\) part of the amplitude’s identity.

A rectangular derivative seminorm can come later. Pointwise bounds avoid early supremum/compactness bureaucracy and directly match `remList_bound`.

Global `ContDiff ℝ ∞ F` is a good first implementation target because it matches U1. Finite differentiability on a neighborhood of the closed box is mathematically sufficient but not the smallest Lean milestone.

### 3.3 Split API

Use a single wrapper around the measure-preserving coordinate split, exposing:

- split/unsplit coordinate evaluation;
- box membership iff membership in the two split boxes;
- product and monomial splitting;
- a set-integral Fubini theorem.

If the existing `Tan/Nrm/split` API already supplies these, reuse or generalize it. Otherwise implement the generic wrapper using `piEquivPiSubtypeProd`, then identify it with the existing split.

**Do not involve tubular `Φ` geometry in this theorem.** Compatibility should come from the coordinate types and split lemmas, not from carrying the atlas apparatus through the smooth proof.

### 3.4 Face and Taylor-index sums

A good representation is
```lean
J ∈ Finset.univ.powerset
```
and, schematically,
```lean
FaceMultiIndex p J :=
  (i : {i // i ∈ J}) → Fin (p i.val)
```

This gives a finite type of bounded multi-indices with no separate boundedness predicate in every summand.

Use a fixed enumeration of coordinates to define `remList`; prove the operator identities for that enumeration. Order-independence can be proved separately, and canonical coefficient independence can also follow from asymptotic uniqueness.

Define the coefficient as an actual finite sum of integrals. Its useful convergence and continuity theorems must carry the admissible-depth hypotheses—Lean’s total integral operation does not itself certify convergence.

### 3.5 Subset sum versus recursion

**Use the subset formula externally and list induction internally.**

A direct recursive asymptotic proof is not genuinely dimension-decreasing on the remainder branch: \(R_0F\) still depends on \(v_0\), and the phase still contains \(v_0^{a_0}\). A “declared flat set” formulation repairs this, but introduces exactly the state tracked by \((J,J^c)\).

The generic face-integration theorem isolates all analytic difficulty once. The subset sum is then finite algebra.

---

## 4. Base parameters and continuity

Keep the scalar/fibre theorem first. Add a parameterized wrapper rather than making all of U2 depend on parameter spaces.

Let \(s\in K\), and suppose:

- \(K\) is compact;
- for every \(\alpha_i\le p_i\),
  \[
  (s,v)\longmapsto\partial_v^\alpha F(s,v)
  \]
  is jointly continuous on \(K\times[0,b]^d\);
- the fibre regularity required by U1 holds.

Then compactness gives a uniform rectangular derivative bound. The normalized face remainders are jointly continuous and have the uniform flat majorant (2). Dominated convergence gives continuity of every valid coefficient (7).

Thus your proposed hypotheses on \(\chi\) suffice **provided the corresponding derivative continuity and bounds also hold for \(A\)**; Leibniz supplies them for \(F=\chi A\).

For integration over the base, additionally require \(\nu\) to be a finite measure, or otherwise supply integrability. **Compactness alone does not imply that an arbitrary measure on \(K\) is finite.**

With finite \(\nu\), the fibrewise estimate yields
\[
\left|
\int_K I_{F_s}(N)\,d\nu(s)
-
\sum_{\mu<L,q}N^{-\mu}(\log N)^q
\int_K C_{\mu,q}(F_s)\,d\nu(s)
\right|
\le C M\,\nu(K)\,N^{-L}(1+\log N)^{d-1}.
\]

If \(b,\beta,h,k\) are fixed on a presentation, this is immediate. If \(b\) or \(\beta\) varies with \(s\), uniform positive lower bounds and uniform monomial-engine constants are an additional task; continuity of the amplitude alone is not enough.

---

## 5. U4 and the analytic datum

Yes: **the radius-margin route is the fastest route**.

For an \(\ell^1\) coefficient norm at radius \(b'>b\), termwise real differentiation gives
\[
\sup_{v\in[0,b]^d}|\partial^\alpha A_c(v)|
\le C_{\alpha,b,b'}\|c\|_{\ell^1_{b'}}.
\]
The polynomial growth of falling factorials is absorbed by the geometric margin \(b/b'<1\). No complex-analytic Cauchy theorem is required.

Leibniz then gives
\[
\|\,\chi A_c\,\|_{\mathrm{mixed},p}
\le C_{\chi,p,b,b'}\|c\|_{\ell^1_{b'}}.
\]

For each valid coefficient,
\[
|C_{\mu,q}(F)|\le C_{\mu,q,p}\|F\|_{\mathrm{mixed},p}.
\]
The fixed-depth formula is linear, so after depth independence the public coefficient is linear as well. For fixed \(\chi\), this constructs the desired bounded linear coefficient functional in \(c\). The finite coefficient vector below a fixed \(L\) is likewise bounded linear.

For a base-dependent datum \(c_\gamma(s)\), specify a norm that controls the required fibre bounds—typically a weighted \(\ell^1\) norm with a supremum over \(s\), or an appropriate integrable bound.

### Downstream interface

A new `WeightedCorePresentation` should expose
\[
\mathrm{weightedTanCoeff}(\mu,q)
=
\int_K
\mathrm{smoothCoeff}\bigl(v\mapsto\chi(s,v)A_{x(s)}(v)\bigr)
\,\mu\,q\,d\nu(s).
\]

Keep the old `tanCoeff` intact. Supply the same **expansion interface** for the new presentation:

- its core integral;
- a cutoff-free coefficient function;
- the finite-cutoff remainder estimate;
- coefficient vanishing/support properties actually used downstream.

If `AnalyticCoreDecomposition.expansion` consumes only that interface, its proof can stay unchanged. If it unfolds `tanCoeff` or `dataBoxIntegral`, first factor out the abstract “presentation has an expansion” theorem; merely replacing the coefficient definition will not preserve such a proof verbatim.

---

## 6. Smallest milestones

### First: the one-dimensional smooth theorem

Choose \(p+h+1>aL\), write
\[
F(v)=\sum_{m<p}\frac{F^{(m)}(0)}{m!}v^m+R^pF(v),
\]
apply the existing monomial expansion to the finite polynomial part, and use (8) for the flat remainder.

Initially state the coefficients using the existing monomial coefficients:
\[
C_{\mu,0}(F)
=
\sum_{m<p}\frac{F^{(m)}(0)}{m!}\,c^{(m)}_{\mu,0}.
\]

**Do not make identification with Gamma values part of this milestone.** It is unnecessary for the smooth expansion and creates a separate normalization obligation.

This validates factorials, depth selection, linear bounds, and the smooth-to-monomial adapter.

### Second: a generic one-flat-complement face theorem

Before specializing all of \(d=2\), prove the theorem behind (3)–(7):

> An inner monomial integral with an all-positive-size cutoff estimate can be integrated against an outer amplitude satisfying a product-flat bound, producing explicit power-log coefficients and the same logarithmic remainder degree.

This is the reusable analytic heart of U3.

### Third: the two-dimensional tensor expansion

For \(d=2\), the four terms are:

- \(T_1T_2F\): corner jets, log degree at most \(1\);
- \(T_1R_2F\), \(R_1T_2F\): edge coefficient integrals, degree \(0\);
- \(R_1R_2F\): fully flat error.

This is the first useful U0 compatibility test. The degree-one logarithmic coefficient comes only from the corner term.

**Bottom line:** the argument is sound. The most valuable simplifications are the elementary fully-flat bound, a single generic face-integration lemma, and an early uniqueness theorem making the resulting coefficients genuinely depth- and cutoff-independent.
