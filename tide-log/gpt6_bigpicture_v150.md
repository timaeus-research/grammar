## Recommendation

**Do not start by generalizing the monomial-series differentiation theorem to arbitrary order.** For finite jets, the cheapest route is likely:

> Apply the existing compact **first-derivative representative theorem to every scalar coordinate derivative of the \(L^s\)-valued kernel**, synchronize these representatives on one conull set, and bootstrap the resulting finite \(C^1\) tower to \(C^R\).

This avoids both the missing monomial-to-power-series converse and global bounds for `contDiff_tsum`. It also lets you reuse the existing `CoeffExpansion` data rather than produce higher-order coefficient expansions from scratch.

There are two small but important qualifications:

1. You must establish that the first-derivative witness represents the corresponding \(L^s\) derivative. If the existing first-derivative theorem does not export that fact, add a difference-quotient lemma.
2. Apply compact gluing on a **larger compact set whose interior contains the box**. A within-derivative theorem on the box alone does not directly give the ambient derivatives you want.

I cannot inspect the repository here. In particular, the supplied information does **not** determine the fields of `CoeffExpansion`, and I will not invent them or claim unverified Mathlib theorem names. Below, code blocks defining new interfaces are proposed Lean signatures, not claims that those declarations already exist.

---

## 1. Ranked smoothness routes

### Rank 1: finite coordinate-jet \(C^1\) bootstrap

Write \(V=\mathrm{Fin}\ d\to\mathbb R\), and let
\[
e_j=\operatorname{Pi.single}(j,1).
\]
For a coordinate word \(b:\mathrm{Fin}\ k\to\mathrm{Fin}\ d\), define
\[
G_{k,b}(u)=D^k F(u)[e_{b_0},\ldots,e_{b_{k-1}}].
\]

These are exactly instances of your existing `derivKernel`, and hence are analytic on `Q.S α`.

For each \(k\le R\) and each \(b\):

* apply `exists_compact_representative_deriv` to \(G_{k,b}\);
* obtain a scalar representative \(h_{k,b}(x,u)\) and its continuous first-derivative witness;
* identify the \(j\)-th coordinate of that witness a.e. with \(G_{k+1,\operatorname{cons}(j,b)}(u)\);
* compare it with \(h_{k+1,\operatorname{cons}(j,b)}(x,u)\).

At first this comparison holds a.e. for each fixed \(u\). Take the intersection over a countable dense subset of the open neighbourhood and the finitely many coordinate words. Continuity extends the equality to every \(u\), on one conull set.

Thus, on that set,
\[
D h_{k,b}(x,u)[e_j]
   =h_{k+1,\operatorname{cons}(j,b)}(x,u)
\]
simultaneously. Finite-dimensional reconstruction of a linear map gives the full first derivative, and induction gives \(h_{0,\varnothing}(x,\cdot)\in C^R\).

**Declarations to consume:**

* your `isLpValuedAnalytic_derivKernel`;
* `exists_compact_representative_deriv`;
* Mathlib’s `HasFDerivWithinAt` → `HasFDerivAt` conversion at an interior point;
* local/recursive characterizations of `ContDiffOn`;
* finite-dimensional reconstruction of continuous linear and multilinear maps from their values on coordinate vectors.

The last reconstruction is small enough to make a bridge helper rather than search for a perfectly matched theorem.

**Bonus:** applying this to all orders and taking a countable intersection gives \(C^\infty\). It does **not**, by itself, give analyticity.

### Rank 2: higher-order monomial differentiation on nested balls

This is viable, but needs more infrastructure.

Use strictly nested positive radii
\[
0<r_0<r_1<r_2,
\]
where the available coefficient majorant is at \(r_2\), and the desired derivative bounds are on \(r_0\) or \(r_1\). For each fixed \(R\),
\[
\sup_{k\le R}\sup_{\|u-w_0\|\le r_1}
 \|D^k C_i(u)\|
 \le M_R\,r_2^{\deg i}.
\]

The radius slack absorbs the degree factors:
\[
\sup_n n^R(r_1/r_2)^n<\infty.
\]

There are two implementation choices:

* prove a local smooth-series wrapper using the local derivative/uniform-convergence machinery;
* multiply every term by **one fixed smooth bump**, equal to one near the target ball and supported strictly inside the majorant ball, then use the global smooth-series theorem.

The bump route is a reasonable fallback if the installed `SmoothSeries` API is global-only. Do not try to use an open-ball subtype as a normed vector space: it is not one.

**A genuine issue with the supplied interface:** `exists_pointwise_expansion` exports only `Continuous (C i)`, not that `C i` is a monomial. Its statement alone is insufficient for higher differentiation. You must strengthen its interface, or work inside its construction and retain the monomial identity.

### Rank 3: reconstruct a scalar `FormalMultilinearSeries`

Mathematically clean, but probably not the cheapest Lean work.

One must:

1. turn each degree-\(n\) multi-index coefficient into an \(n\)-linear coordinate monomial;
2. sum over the finitely many degree-\(n\) multi-indices;
3. control the operator norm of that finite sum;
4. justify regrouping the scalar series by degree;
5. prove the `HasFPowerSeriesOnBall` statement.

`ContinuousMultilinearMap.mkPiAlgebra` can help construct coordinate products, but is not a ready-made multivariate coefficient correspondence. `FormalMultilinearSeries.ofScalars` is not a turnkey converse for arbitrary multivariate monomial coefficients.

I would not implement this just for Stage B.

---

## 2. The important quantifier correction

The desirable assertion is

```lean
∀ u ∈ U, ∀ k ≤ R, ∀ v,
  (fun x => iteratedFDeriv ℝ k (f x) u v)
    =ᵐ[μ] (Q.derivKernel α k v u)
```

together with **one conull set on which the sample functions are smooth and their chosen jet representatives agree everywhere**.

Do **not** silently strengthen that to

```lean
∀ᵐ x ∂μ, ∀ u ∈ U, ...
    = (Q.derivKernel α k v u) x
```

using the pre-existing `Lp` coercions on the right. Countably many coefficient representatives do not make all the uncountably many independently chosen `Lp` representatives compatible.

The correct synchronized representative is
```lean
fun x => iteratedFDeriv ℝ k (f x) u v
```
itself. It represents the required \(L^s\) class for each \(u,k,v\), and its pathwise compatibility is literal.

This distinction is essential, not cosmetic.

---

## 3. Suggested Stage B output

I would make the main structure stronger and simpler: redefine the family to zero off a measurable conull set, so that **every** sample path is smooth. There is then no need to thread a good set through every deterministic calculus lemma.

Here is the core interface. Ambient atlas and measure parameters are suppressed; use the calculus-order coercions of your Mathlib checkout.

```lean
abbrev Param (d : ℕ) := Fin d → ℝ

structure ChartKernelRep
    (Q : AnalyticChartKernel A F) (α : ι) (R : ℕ) where
  U : Set (Param d)
  isOpen_U : IsOpen U
  box_subset_U : GreyBook.box d (A.b α) ⊆ U
  U_subset_S : U ⊆ Q.S α

  f : E → Param d → ℝ

  measurable_jet :
    ∀ k ≤ R, ∀ u ∈ U, ∀ v : Fin k → Param d,
      Measurable
        (fun x => iteratedFDeriv ℝ k (f x) u v)

  smooth :
    ∀ x, ContDiffOn ℝ R (f x) U

  represents :
    ∀ k ≤ R, ∀ u ∈ U, ∀ v : Fin k → Param d,
      (fun x => iteratedFDeriv ℝ k (f x) u v)
        =ᵐ[μ] (Q.derivKernel α k v u)

  B : E → ℝ
  measurable_B : Measurable B
  nonneg_B : ∀ x, 0 ≤ B x
  memLp_B : MemLp B s μ

  jet_bound :
    ∀ x, ∀ u ∈ GreyBook.box d (A.b α), ∀ k ≤ R,
      ‖iteratedFDeriv ℝ k (f x) u‖ ≤ B x
```

You may also want an explicit order-zero `represents₀` field for convenient rewriting. Mathematically it is redundant.

### Keep the probabilistic expansion separate

`CoeffExpansion` depends on `X`, `P`, and the centering function, whereas the structure above is a deterministic representative theorem. I would export a second theorem, at \(s=6\), producing coordinate-jet expansions for this same `f`.

That theorem should use only the finite coordinate-word index type, not all direction tuples.

### Assumptions

For the route based on `exists_pointwise_expansion`, state `s ≠ ∞`. Stage C at \(s=6\) satisfies it. Do not claim the supplied theorem handles \(s=\infty\).

For centering by integration and moving derivatives through integration, state the finite-measure/probability assumptions actually used. They are not implied by `Fact (1 ≤ s)`.

---

## 4. Three intermediate lemmas worth adding

### Lemma A: a samplewise first derivative represents the \(L^s\) derivative

This isolates the only potentially missing first-order identification.

```lean
theorem ae_fderiv_eq_of_representative
    {U : Set (Param d)}
    {G : Param d → Lp ℝ s μ}
    {g : E → Param d → ℝ}
    {dg : E → Param d → (Param d →L[ℝ] ℝ)}
    (hs_top : s ≠ ∞)
    (hU : IsOpen U)
    (hG : DifferentiableOn ℝ G U)
    (hg_meas : ∀ u ∈ U, Measurable (fun x => g x u))
    (hg_rep : ∀ u ∈ U, (fun x => g x u) =ᵐ[μ] G u)
    (hg_deriv :
      ∀ x, ∀ u ∈ U, HasFDerivAt (g x) (dg x u) u) :
    ∀ u ∈ U, ∀ v : Param d,
      (fun x => dg x u v) =ᵐ[μ] (fderiv ℝ G u v)
```

This assumes the usual ambient `Fact (1 ≤ s)`.

**Proof route:** fix \(u,v\), choose a deterministic nonzero sequence \(t_n\to0\) with \(u+t_nv\in U\). Then:

* the \(L^s\) difference quotients converge in \(L^s\) to `fderiv ℝ G u v`;
* the pointwise difference quotients converge to `dg x u v`;
* countably many uses of `hg_rep` identify the two sequences a.e.;
* uniqueness of the limit identifies the two limits a.e.

The measure-theoretic wrapper you need is:

> \(L^s\)-convergence of classes plus a.e. pointwise convergence of representatives implies that the pointwise limit represents the \(L^s\) limit.

This can be proved through convergence in measure and uniqueness, or through an a.e.-convergent subsequence. Check the installed `Lp`/convergence-in-measure API and the proof of `LpPointwise`: the latter necessarily resolves closely related representative-limit bookkeeping.

I would **not** name a purported `Lp.tendsto_ae...` theorem without checking the checkout. The precise wrapper above is more useful to the bridge than whichever low-level theorem implements it.

If `exists_coeffExpansion_deriv_of_hasFPowerSeriesOnBall` already proves this identification internally, export that result instead.

### Lemma B: a finite coordinate \(C^1\) tower is a \(C^R\) jet

A scalar, non-measure-theoretic lemma:

```lean
def coordVec (j : Fin d) : Param d :=
  Pi.single j 1

def coordLinear
    (c : Fin d → ℝ) : Param d →L[ℝ] ℝ :=
  ∑ j, c j • ContinuousLinearMap.proj j
```

Then use an interface of the following form:

```lean
theorem contDiffOn_and_iteratedFDeriv_of_coordTower
    {U : Set (Param d)}
    (hU : IsOpen U)
    (R : ℕ)
    (h : (k : ℕ) → (Fin k → Fin d) → Param d → ℝ)
    (hc :
      ∀ k ≤ R, ∀ b, ContinuousOn (h k b) U)
    (hd :
      ∀ k < R, ∀ b, ∀ u ∈ U,
        HasFDerivAt (h k b)
          (coordLinear
            (fun j => h (k + 1) (Fin.cons j b) u))
          u) :
    ContDiffOn ℝ R (h 0 Fin.elim0) U ∧
    ∀ k ≤ R, ∀ b, ∀ u ∈ U,
      iteratedFDeriv ℝ k (h 0 Fin.elim0) u
        (fun j => coordVec (b j))
        = h k b u
```

Check the argument-order convention in the recursive `iteratedFDeriv` API. If it prepends/appends differently, adjust the coordinate-word convention once. For analytic \(G\), symmetry also resolves the corresponding coordinate derivative identity.

The proof is induction using the recursive characterization of smoothness and the continuous-linear equivalence between a linear map on \(\mathbb R^d\) and its \(d\) coordinate values.

This is the main deterministic helper I would invest in.

### Lemma C: the coefficient majorant belongs to \(L^s\)

```lean
theorem memLp_tsum_abs_majorant
    (hs_top : s ≠ ∞)
    (A : ℕ → E → ℝ)
    (b : ℕ → ℝ)
    (hA_meas : ∀ i, Measurable (A i))
    (hA_lp : ∀ i, MemLp (A i) s μ)
    (hb : ∀ i, 0 ≤ b i)
    (hsum :
      Summable
        (fun i => b i * (eLpNorm (A i) s μ).toReal))
    (hpoint :
      ∀ x, Summable (fun i => b i * |A i x|)) :
    MemLp (fun x => ∑' i, b i * |A i x|) s μ
```

**Proof:** put \(b_i|A_i|\) into `Lp` using `MemLp.toLp`. Their norms are summable, so their `Lp` series converges by completeness and `Summable.of_norm`. Identify the pointwise tsum with that `Lp` sum using the representative-limit wrapper from Lemma A.

This avoids depending on whether your checkout happens to export the desired `eLpNorm_tsum_le` variant. If it does, use it and shorten the proof.

Crucially, `hA_lp` or an equivalent finiteness hypothesis is needed. A `.toReal` summability hypothesis alone is not enough: `ENNReal.toReal ∞ = 0`.

---

## 5. Gluing: reuse the compact theorem, but enlarge the compact set

Choose compact \(L\) and open \(V\) such that
\[
K_0\subset V\subset L\subset Q.S(\alpha),
\qquad V\subset \operatorname{interior} L.
\]
Such a choice is available because \(K_0\) is compact and the parameter space is finite-dimensional.

Apply `exists_compact_representative_deriv` on **\(L\)** separately to each \(G_{k,b}\). You now have:

* \(h_{k,b}(x,\cdot)\), continuous on \(L\);
* \(d h_{k,b}(x,\cdot)\), continuous on \(L\);
* within derivatives on \(L\), hence ambient derivatives on \(V\);
* the existing coefficient-expansion data.

For each \(k<R,b,j\), Lemma A gives, at each fixed \(u\in V\),
\[
d h_{k,b}(x,u)[e_j]
 = h_{k+1,\operatorname{cons}(j,b)}(x,u)
 \quad\text{a.e. }x.
\]

Take a countable dense subset of \(V\). The equality sets are measurable, and their countable intersection is a measurable conull set \(N\). Continuity gives equality on all of \(V\).

Set
\[
f(x,u)=
\begin{cases}
h_{0,\varnothing}(x,u),&x\in N,\\
0,&x\notin N.
\end{cases}
\]

Apply Lemma B on \(N\); use the zero function outside \(N\). This gives the all-\(x\) `smooth` field above.

**Thus: reuse the existing compact gluing.** No need to copy its σ-selection machinery into a higher-order gluing theorem.

For one good event across charts, you need finitely or countably many charts. An unrestricted uncountable `ι` cannot be handled merely by intersecting conull sets.

---

## 6. Envelopes without differentiating the original coefficient series

Obtain an \(L^s\) envelope \(B_{k,b}\) for each continuous representative \(h_{k,b}\), from its existing coefficient expansion and Lemma C.

On \(N\), coordinate-jet compatibility identifies these with the coordinate values of \(D^k f\). For the usual sup norm on `Fin d → ℝ`,
\[
\|D^k f(x,u)\|
 \le \sum_{b:\mathrm{Fin}\ k\to\mathrm{Fin}\ d}
       |h_{k,b}(x,u)|.
\]

Consequently, take
\[
B(x)=
 \sum_{k=0}^{R}\ \sum_b B_{k,b}(x),
\]
and set it to zero off \(N\) if convenient.

This is a finite sum of \(L^s\) functions. It bounds all orders through \(R\), with no higher-order monomial estimate needed. If you use another norm convention, insert the finite-dimensional comparison constant.

You do not need to formalize an actual supremum. The `jet_bound` field is both stronger operationally and much easier to use.

---

## 7. `CoeffExpansion` and the joint law

### What can be said exactly

The supplied statements do not reveal the fields of `CoeffExpansion`. In particular, they do not determine whether it records:

* literal series identities or a.e. identities;
* separate centered and uncentered expansions;
* sample-index conditions involving `X`;
* a specific envelope normalization.

So an exact constructor recipe requires its definition. The first task should be to inspect that definition and the constructor used in `LpCoeffExpansionDeriv.lean`.

### Cheapest route with the bootstrap

For each coordinate word \((k,b)\), you already applied the compact representative theorem to the analytic kernel \(G_{k,b}\). It therefore already supplies the relevant expansion for **its own** representative \(h_{k,b}\).

You have then proved
\[
D^k f(x,u)[e_b]=h_{k,b}(x,u)
\]
for every \(u\in K_0\), on one conull set.

There are two implementation choices.

1. **Keep the old `CoeffExpansion` inputs.**  
   Feed \(h_{k,b}\) directly to `chartProcessCM_law`. On the sample-good event, identify the resulting empirical field with the derivatives of the empirical field built from \(f\).

   This is likely cheapest: no `CoeffExpansion` transport theorem is needed.

2. **Transport the expansions to the synchronized jets.**  
   Add a congruence lemma under equality a.e. in \(x\), uniformly on the box. If literal series identities are required, replace every coefficient \(A_i\) by `N.indicator A_i`; the representative becomes zero off \(N\), and all \(L^6\) data remain unchanged.

Thus **no order-\(R\) generalization of the coefficient-expansion differentiation theorem is necessary** for the joint-law route.

For centering, under the probability/finite-measure assumptions making integration a continuous linear map on `Lp`, commute this map with derivatives:
\[
\int G_{k,b}(u)\,d\mu
 =D^k\!\left(\int F(u)\,d\mu\right)[e_b].
\]
For `Q.a α`, use `Q.mean` to identify this with the coordinate derivative of the monomial. This is a separate, short Banach-valued differentiation lemma.

Finally, countably many sample indices and finitely/countably many charts give a probability-one event where every sampled \(X_i\) lies in the synchronized good sets. On that event, finite-sum differentiation gives the empirical jet identity simultaneously for all \(u\).

---

## 8. Can Stage B be avoided?

Not by assigning unrelated continuous representatives to the derivative kernels and invoking closedness. One still has to prove compatibility.

There are alternatives:

* prove distributional derivative compatibility, then recover classical regularity;
* construct smooth polynomial/partition-of-unity approximations whose jets converge uniformly;
* prove support in the closed realizable-jet space directly from integral compatibility identities.

But each requires essentially the same compatibility work, often with more analytic infrastructure.

The \(C^1\)-tower bootstrap is already a cheap compatibility proof. It produces actual smooth representatives rather than merely membership in the closure of realizable jets.

## Bottom line

I would implement:

1. **`ae_fderiv_eq_of_representative`**, unless the existing first-order expansion theorem already exports it;
2. **`contDiffOn_and_iteratedFDeriv_of_coordTower`**;
3. **a coefficient-majorant `MemLp` helper**, if greybook does not already have one.

Then reuse `exists_compact_representative_deriv` on a larger compact neighbourhood for all finite coordinate derivatives. Keep its existing `CoeffExpansion` outputs for the law theorem, and identify those processes with the synchronized samplewise jets on one good event.

That delivers Stage B without a monomial converse, without global smooth-series bounds, and probably without touching greybook’s higher-order series machinery.