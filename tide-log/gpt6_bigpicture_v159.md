## Recommendation and ranking

The next useful milestone is **uniqueness-certified Mellin principal parts, followed by actual asymptotic division**. The quotient algebra and the sum–integral interchange are now infrastructure, not the remaining conclusions.

My implementation order would be:

1. **C: bounded principal-part uniqueness**, then identification of every \(c_{\mu,q}\).
2. **B(i): rational expansion at infinity**, then **B(ii): deterministic two-scale division**.
3. **A(b): annealed coefficient expansion**, with an explicit absolute-moment hypothesis.
4. **A(a): Gaussian polynomial-jet Wick evaluation**, composed with step 3.
5. **B(iii): continuous mapping for finite quotient/Laurent-coordinate vectors**.
6. **D: a downstairs finite-dimensional-law bridge**, only if it is nearly a re-export.

Do not start Hadamard finite parts, a global meromorphic API, or a Gaussian random-field descent construction now.

Two corrections are important:

* For a finite-dimensional Gaussian vector, \(\mathbb E e^{c\|Z\|}<\infty\) for **every finite \(c\)**. Smallness enters for **quadratic** exponential growth, not linear exponential growth.
* Positivity of the denominator’s **leading log coefficient** does not imply that its entire polynomial \(B_0(L)\) is positive for every \(L\). It gives eventual positivity, which is what deterministic division needs.

The statements below are Lean-shaped specifications, not claims about exact existing API names.

---

## A. Gaussian Wick: prove (b), then a genuinely jet-compatible version of (a)

### A1. The immediate new theorem: annealed coefficient expansion

Let \(Y_\omega\) denote the **actual multiplier in the population expansion**. In the existing chart theorem this may be \(u^kG_\omega\), rather than \(G_\omega\) alone. Write
\[
T_r(f):=C^{\mathrm{pop}}_{\mu+r/2,q}[f],
\qquad
g_r(\omega):=\frac1{r!}T_r(\eta Y_\omega^r).
\]

A convenient interface is:

```lean
theorem integral_empCoeff_eq_tsum_population
    (hseries : ∀ᵐ ω ∂P, HasSum (fun r => g r ω) (C ω))
    (hCmeas : AEStronglyMeasurable C P)
    (hg : ∀ r, Integrable (g r) P)
    (habs :
      Summable (fun r => ∫ ω, ‖g r ω‖ ∂P)) :
    Integrable C P ∧
      (∫ ω, C ω ∂P) = ∑' r, ∫ ω, g r ω ∂P
```

Here the application supplies `hseries` using `hasSum_empCoeffRect_population`.

**Route.** Derive integrability of \(\sum_r\|g_r\|\), and almost-everywhere absolute summability, by Tonelli; invoke DXXX. It is worth packaging that Tonelli step once.

Keep `hg` explicitly. A condition involving ordinary Bochner integrals of norms, without individual integrability, is unsafe because Lean’s integral is totalized.

This is new and worthwhile: it moves the existing pointwise population identity through expectation. It is not yet Wick, and its name should not suggest otherwise.

### A2. The clean evaluated Wick theorem

The useful final interface is:

```lean
theorem integral_empCoeff_gaussian_wick
    (hseries : ...)
    (hg : ∀ r, Integrable (g r) P)
    (habs : Summable (fun r => ∫ ω, ‖g r ω‖ ∂P))
    (hodd : ∀ j,
      (∫ ω, T (2*j+1) (η * Y ω ^ (2*j+1)) ∂P) = 0)
    (heven : ∀ j,
      (∫ ω, T (2*j) (η * Y ω ^ (2*j)) ∂P) =
        ((2*j)! / (2^j * j!)) * T (2*j) (η * W^j)) :
    (∫ ω, C ω ∂P) =
      ∑' j, (1 / (2^j * j!)) * T (2*j) (η * W^j)
```

All factorial arithmetic here should be cast to \(\mathbb R\). The displayed `T` notation suppresses its function-space arguments.

This composition theorem is short. The substantive Gaussian theorem should discharge `hodd` and `heven`, not leave them as the end product.

Absolute summability permits splitting into even and odd indices; factorial cancellation gives the stated weights. The result should also expose summability of the evaluated Wick series.

**Chart monomial warning.** If \(Y=u^kG\), then
\[
W=\operatorname{Var}(Y)=u^{2k}V.
\]
Thus the direct engine statement has \(\eta(u^{2k}V)^j\). Only remove that monomial if a separately proved shift/normalization lemma gives the paper’s notation
\(C^{\mathrm{pop}}_{\mu+j,q}[\phi V^j]\).

### A3. What the Gaussian-jet hypothesis actually needs

A jointly centered Gaussian jet vector guarantees that every polynomial in those jets is integrable. It does **not, by itself**, identify its covariance entries with derivatives of a specified function \(V\).

The clean algebraic route is a **truncated Taylor-jet algebra** at each evaluation point:

* `Jω` is the truncated jet of \(Y_\omega\), in normalized Taylor coordinates.
* Its finitely many real coordinates are jointly centered Gaussian.
* `JV` is the truncated jet of \(W\).
* Require the covariance compatibility
  \[
  \mathbb E[J_\omega^2]=J_V
  \]
  in that truncated algebra.

Then prove, coordinatewise,
\[
\mathbb E[J_\omega^{2j}]
 =\frac{(2j)!}{2^j j!}J_V^j,
\qquad
\mathbb E[J_\omega^{2j+1}]=0.
\]

This follows from finite-dimensional Wick: expand the jet-algebra products and group pairings. Every pairing contributes the same algebra product because the algebra is commutative. Multiplication by the deterministic jet of \(\eta\), followed by the finite linear coefficient functional, gives the coefficient-level identities.

In raw derivative coordinates, compatibility reads
\[
\partial^\alpha W(x)
 =
 \sum_{\beta\leq\alpha}
 {\alpha\choose\beta}\,
 \mathbb E[
   \partial^\beta Y(x)\,
   \partial^{\alpha-\beta}Y(x)].
\]

This is the missing bridge between “polynomial in Gaussian jets” and “derivatives of \(V^j\).”

**Implementation advice:** prove a finite polynomial/Wick lemma first; do not build a general theorem for differentiating arbitrary expectations. If deriving compatibility from a random smooth field, use an explicit \(L^2\)-differentiability or local domination hypothesis. Samplewise smoothness alone is not the desired interface.

Also check the scope of “fixed finite jet vector”: as \(r\) increases, the population depth is \(\mu+r/2\). A common finite-jet reduction must come from the engine’s weighted structure; it should not be inferred merely from each individual coefficient having finite depth. The annealed theorem can perfectly well use a separate finite Gaussian vector for each \(r\).

### A4. The envelope is not automatically the existing variance threshold

The jet-ball estimates do not establish a global envelope until their dependence on \(B\) is quantified.

* If one proves
  \[
  \sum_r |g_r(\omega)|
    \le C(1+\|J_\omega\|)^M e^{c\|J_\omega\|},
  \]
  every finite-dimensional Gaussian jet law satisfies the required integrability.
* For a bound involving \(e^{c\|J_\omega\|^2}\), covariance-dependent smallness is needed.
* The \(v<2\) threshold comes from the quadratic growth of the fluctuation kernel, approximately \(e^{a^2/4}\) times a polynomial factor. It is not a threshold for linear Gaussian exponentials.
* A sufficient condition obtained from a whole-jet norm need not equal the sharp pointwise threshold \(V<2\).

Therefore **retain the explicit absolute-moment hypothesis in the first Wick release**. Finite Gaussian moments prove each term integrable, not summability over all terms.

### A5. Option (c)

For a leading residue formula already expressed as a fluctuation-kernel integral, your existing Gaussian-marginal Fubini theorem supplies essentially the analytic content.

The only likely new wrapper is
\[
\mathbb E C_{\mu,c-1}[G,\phi]
 =
 \frac{\Gamma(\mu)}{(c-1)!}
 \int \phi(x)(1-V(x)/2)^{-\mu}\,d\mathrm{Res}(x),
\]
assuming \(\mu>0\), \(V<2\) almost everywhere, and the appropriate absolute-integrability condition. For signed \(\phi\), formulate that condition with \(|\phi|\).

If `integral_tupleLimit_gaussian_varying` already exposes this varying-variance conclusion, **do not count this as a new gap closure**. Add only the named coefficient-to-residue corollary if useful.

---

## B. Posterior quotient: deterministic division first

### B(i). Rational functions at infinity

Use `Polynomial ℝ`, but avoid introducing rational functions merely to evaluate \(P/Q\).

For nonzero \(P,Q\), put \(a=\deg P\), \(b=\deg Q\), and define their reversed coefficient sequences
\[
A_i=\begin{cases}P_{a-i}&i\le a\\0&\text{otherwise},\end{cases}
\qquad
B_i=\begin{cases}Q_{b-i}&i\le b\\0&\text{otherwise}.\end{cases}
\]
Set \(r_i=\texttt{quotientBlocks}\ A\ B\ i\).

```lean
theorem polynomial_eval_div_asymptotic
    (P Q : Polynomial ℝ)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (M : ℕ) :
    (fun L : ℝ =>
      P.eval L / Q.eval L -
        Real.rpow L ((P.natDegree : ℝ) - Q.natDegree) *
          ∑ i ∈ Finset.range M,
            r i * Real.rpow L (-(i : ℝ)))
      =O[atTop]
    (fun L =>
      Real.rpow L
        ((P.natDegree : ℝ) - Q.natDegree - M))
```

Treat \(P=0\) separately, or preferably also provide a **fixed-degree-bound version**: \(a\) may be an upper bound for \(\deg P\), while \(Q_b\ne0\) and \(\deg Q\le b\). That version is better for probabilistic transfer because random numerator degrees may drop.

**Route: no analytic Taylor machinery.**

1. Put \(t=1/L\).
2. For the reversed polynomials \(P^\#,Q^\#\), use `sum_mul_quotientBlocks` to show
   \[
   P^\#(t)-Q^\#(t)\sum_{i<M}r_it^i=t^M H_M(t)
   \]
   for a polynomial \(H_M\).
3. Since \(Q^\#(0)=Q.\mathrm{leadingCoeff}\ne0\), \(H_M/Q^\#\) is bounded near zero.
4. Transfer \(t\to0^+\) along \(L\to+\infty\).

This is exactly where DXXIX should now pay off.

### B(ii). Minimal two-scale division theorem

First normalize away the common leading power:
\[
A(n)=n^\lambda E_n[\phi],\qquad B(n)=n^\lambda E_n[1].
\]
Put \(x(n)=n^{-1/Q}\), with \(Q>0\). Assume, for a fixed \(J\ge1\),
\[
A(n)=\sum_{j<J}A_j(\log n)x(n)^j
       +O(x(n)^J(\log n)^D),
\]
and the corresponding statement for \(B\), with all retained polynomials of degree at most \(D\), and \(B_0\ne0\) as a polynomial.

Define directly over \(\mathbb R\), pointwise in \(L\),
```lean
R j L :=
  quotientBlocks
    (fun i => (Apoly i).eval L)
    (fun i => (Bpoly i).eval L)
    j
```

Then target:

```lean
theorem quotient_twoScale_isBigO
    (hQ : 0 < Q) (hJ : 1 ≤ J)
    (hA : A - retainedA =O[atTop] remainderScale)
    (hB : B - retainedB =O[atTop] remainderScale)
    (hdegA : ∀ j < J, (Apoly j).degree ≤ D)
    (hdegB : ∀ j < J, (Bpoly j).degree ≤ D)
    (hB0 : Bpoly 0 ≠ 0) :
    (fun n =>
      A n / B n -
        ∑ j ∈ Finset.range J,
          R j (Real.log n) *
            Real.rpow n (-(j : ℝ) / Q))
      =O[atTop]
    (fun n =>
      Real.rpow n (-(J : ℝ) / Q) *
        (Real.log n)^((J+1)*D))
```

The exponent \((J+1)D\) is deliberately coarse. It is sufficient under these degree hypotheses and avoids premature log-order optimization.

**Proof route.**

1. If \(b=\deg B_0\), obtain
   \[
   |B_0(L)|\ge cL^b
   \]
   eventually.
2. Power decay beats every fixed log power, so
   \[
   B(n)/B_0(\log n)\longrightarrow1.
   \]
   This gives eventual nonvanishing and a quantitative inverse bound.
3. Multiply the proposed truncated quotient by \(B(n)\).
4. Cancel all powers \(x^j\), \(j<J\), using DXXIX.
5. Bound the uncancelled finite terms and the two input remainders; divide by the denominator lower bound.

**Why not assume just eventual \(B_0(L)\ne0\)?** For an arbitrary function that is too weak. For a nonzero polynomial it comes with the required quantitative growth, but expose the polynomial hypothesis rather than hiding the argument.

Finally make a wrapper deriving these normalized expansions from `CutoffExpansion`. That wrapper must state the common leading exponent and vanishing below it explicitly; the lattice reindexing is not automatic.

**Do not initially expand every \(R_j\) into inverse logs.** First prove this theorem with exact rational blocks, then apply B(i) to whichever blocks the paper needs.

### B(iii). Probabilistic transfer: finite coordinates, not `RatFunc` laws

Use a finite coefficient vector \(\theta\). Define a finite vector of:

* quotient coordinates at specified admissible evaluations; or, preferably,
* coefficients in the inverse-log expansions of finitely many \(R_j\).

For the latter, work with fixed degree bounds and a fixed denominator degree \(b\). The coordinate map is continuous on
\[
\{\theta:B_{0,b}(\theta)\ne0\}.
\]

The target shape is:

```lean
(hθ : TendstoInDistribution θn atTop θ)
(hcont : ContinuousOn quotientCoordinateMap goodSet)
(hgood : ∀ᵐ ω ∂P, θ ω ∈ goodSet)
⊢ TendstoInDistribution
    (fun n ω => quotientCoordinateMap (θn n ω))
    atTop
    (fun ω => quotientCoordinateMap (θ ω))
```

Use the existing distributional-convergence vocabulary and its almost-sure-continuity mapping theorem.

Your positivity argument is the right one for the leading scalar:
\[
B_{0,b}(G)=\int \text{prior}\cdot S_\lambda(G)\,d\mathrm{Res}>0.
\]
But formally it needs:

* nonnegative prior;
* positive residue mass where the prior is positive;
* measurability and finiteness of the integral.

No non-atomicity theorem is needed. Nor is \(V<2\) needed merely for pathwise positivity; that threshold concerns annealed integrability.

Two cautions:

1. \(B_{0,b}>0\) does not imply \(B_0(L)>0\) at every fixed \(L\).
2. Evaluating at \(L=\log n\) is an \(n\)-dependent map. Ordinary fixed-map CMT alone does not handle it.

For the latter, finite-dimensional tightness plus uniform deterministic estimates on compact coefficient sets bounded away from \(B_{0,b}=0\) is the natural route. Transferring the **actual posterior**, rather than its coefficient vector, additionally requires stochastic control of the expansion remainders. Joint coefficient convergence alone is insufficient.

---

## C. Lower log orders: uniqueness now, finite parts later

### C1. Prove bounded principal-part uniqueness

Use coefficients in the standard \((s-\mu)^{-k}\) convention:

```lean
def polarPart (a : Fin (D+1) → ℂ) (μ s : ℂ) : ℂ :=
  ∑ q, a q / (s - μ)^(q.val + 1)

theorem polarPart_eq_of_sub_isBigO_one
    (hbounded :
      (fun s => polarPart a μ s - polarPart b μ s)
        =O[𝓝[≠] μ] (fun _ => (1 : ℂ))) :
    a = b
```

This is stronger and cheaper than requiring a holomorphic extension.

**Slick route:** descending induction on pole order.

For the top order \(D+1\), multiply the difference by \((s-\mu)^{D+1}\).

* Boundedness implies the product tends to zero.
* On the punctured neighborhood, finite algebra rewrites it as
  \[
  \sum_{q=0}^D(a_q-b_q)(s-\mu)^{D-q}.
  \]
* Continuity gives limit \(a_D-b_D\).

Thus \(a_D=b_D\). Remove that term and repeat.

I would not use `Polynomial.eq_of_infinite_eval_eq`: you have boundedness, not an infinite set of exact zeros. The pole-stripping limit argument matches the hypotheses directly.

### C2. What this adds to DXXVII

For a **positive** retained exponent \(\mu\), choose \(U>\mu\) and a small disk around \(\mu\) contained in \(0<\Re s<U\), excluding all other retained poles.

Then:

* the Mellin remainder is holomorphic on that disk;
* principal parts at other exponents are holomorphic there;
* the principal part at \(\mu\) is uniquely determined.

Consequently its standard polar coefficient is
\[
\ell_{\mu,-q-1}=(-1)^{q+1}q!\,c_{\mu,q},
\]
or
\[
c_{\mu,q}
 =\frac{(-1)^{q+1}}{q!}\ell_{\mu,-q-1}.
\]

Call this a **unique local principal-part representation** unless you actually instantiate a Laurent-series API. It gives the intended intrinsic characterization without doing so.

The qualification \(\mu>0\) matters: your coherent family presently lives in the right half-plane. A statement at \(\mu=0\) would require additional continuation across the small-\(N\) boundary.

Thus DXXVII contains the representation, but uniqueness is a real, small, valuable new theorem.

### C3. The two-dimensional anchor

Do not claim that the displayed finite-part formula is merely a Taylor-tree computation.

The Taylor tree can verify a finite combinatorial expression for \(c_{\mu,0}\). Identifying that expression with
\[
\frac{D_1\mathrm{FP}_2A_\mu}{2k_1}
+\frac{\mathrm{FP}_1D_2A_\mu}{2k_2}
-\frac{D_1D_2(\partial_sA_s|_\mu)}{4k_1k_2}
\]
requires definitions of \(\mathrm{FP}_i\), their subtraction/normalization conventions, and comparison with the chart integrals. Even “depth at most one” must be checked against the relevant resonance; it is not implied solely by dimension two.

**Recommendation:** prove the explicit \(d=2\) engine formula only if it is useful independently. Defer the Hadamard-finite-part identification.

---

## D. Downstairs Gaussian limit: one cheap bridge, otherwise skip

The best value/cost statement is the finite-dimensional limit already suggested:

For finite \(w_1,\dots,w_d\in W\), with centered square-integrable features,
\[
(H_n(w_1),\dots,H_n(w_d))
 \Rightarrow N(0,\Sigma),
\qquad
\Sigma_{ij}
 =\operatorname{Cov}(f(X,w_i),f(X,w_j)).
\]

Lean-shaped:

```lean
theorem empiricalProcess_evalVector_gaussian_limit
    (hfeature : ∀ i, MemLp (fun x => f x (w i)) 2 P)
    (hcenter : ∀ i, ∫ x, f x (w i) ∂P = 0)
    (hiid : ...)
    :
    TendstoInDistribution
      (fun n ω i => H n ω (w i))
      atTop
      gaussianVectorWithCovariance
```

Prove it by instantiating the grey book’s finite-dimensional CLT and identifying the covariance matrix. If those identifications already exist, make this a bridge corollary rather than a new engine development.

It proves **finite-dimensional distributions downstairs**, not a random continuous field, tightness in a function space, or descent of a chartwise Gaussian field.

Do not start continuous descent unless the quotient-map hypotheses and fibre constancy of the *joint* limiting object are already available. Matching separate chart laws is not enough.

---

## E. Paper-mirror paragraph — eight lines

> The fluctuation-zeta theorem identifies the Mellin transform of frozen evidence with an integral of the complex fluctuation kernel.  
> This identity assumes an \(S\)-finite parameter measure, almost-everywhere positivity of \(K\), and the stated absolute product-integrability hypothesis `hint`.  
> Separately, a cutoff expansion, local integrability on \((0,\infty)\) (`hE`), and boundedness near zero (`hE0`) define Mellin transforms of subtracted remainders.  
> For each positive cutoff \(U\), the remainder transform is holomorphic on \(0<\Re s<U\).  
> Adding the finite sum \(\sum_{\mu<U,q}c_{\mu,q}q!/(\mu-s)^{q+1}\) defines a continuation expression \(F_U\) away from its possible poles.  
> On the stated initial convergence strip, this expression agrees with the original Mellin transform.  
> Compatibility of the remainder transforms makes the expressions \(F_U\) agree on overlapping domains away from their possible poles.  
> The formalization does not yet package this family in a meromorphic API, prove principal-part uniqueness, or derive `hint` on the expected strip \(0<\Re s<\lambda\) from the model data.