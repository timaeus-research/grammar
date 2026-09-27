## 1. Fidelity check

**DCLVII–DCLX are mathematically consistent, with one important support distinction.** This is a check of the supplied statements, not an independent build of the pin.

**(a) Residual constant: correct.** Put \(R=\sqrt N\), \(s=\sqrt{2\pi}\). After factoring \(2/s\), use
\[
|e^{-v^2/(2N)}-1|\le \min\{v^2/(2N),1\}.
\]
The three regions give
\[
(0,1]:\quad \frac1{6N}\le\frac1{2N},
\]
\[
(1,R]:\quad \frac K{2N}\int_1^R(1+2\log v)\,dv
 \le \frac{K(1+\ell)}{2R},
\]
and
\[
(R,\infty):\quad K\int_R^\infty\frac{1+2\log v}{v^2}\,dv
=\frac{K(3+2\log R)}R.
\]
Thus the stated bound is valid, including \(N=1\).

**(b) Log-power bound: correct; split off \(j=0\).** For \(j>0\), the stated inequality follows from your logarithmic estimate. Equivalently, with \(t=-\log x\ge0\),
\[
t^j e^{-t/2}\le (2j/e)^j\le(2j)^j.
\]
For \(j=0\), it is \(1\le1/\sqrt x\); do not run the \(1/(2j)\) argument.

**(c) Positivity set versus support.** For \(0<z<M\),
\[
M/z>1,\qquad V/(Mz)\ge M/z>1,
\]
so `nbClosed M V z > 0`. Consequently,
\[
\boxed{\rho(\lambda,z)>0
\iff -M_-<z<M_+\ \text{and}\ z\ne0.}
\]
Your implementation explicitly sets \(\rho(\lambda,0)=0\). Therefore:

- the **pointwise positivity set** is the punctured interval;
- the **topological support**, and the support of the associated measure, is
  \(\boxed{[-M_-,M_+]}\);
- the open interval is the interior of that support, not literally the support or positivity set.

The `quadP_div_le` mechanism correctly supplies vanishing at and beyond the endpoints.

**(d) Primitive and mass: correct.** Writing \(A=c_1-\log z\), \(B=c_2-\log z\),
\[
\frac d{dz}\{2z[AB+A+B+2]\}=2AB.
\]
At \(z=M\), \(A=0\), \(B=\log(V/M^2)\), yielding
\[
2M[\log(V/M^2)+2].
\]
Also \(V\ge M_\pm^2\) gives the useful strengthening
\[
m(\lambda)\ge4(M_++M_-)>0.
\]

---

## 2. All-depth engine

### Interface corrections

**First: integrate the residual over the positive half-line, not all of \(\mathbb R\).** An unqualified `∫ v, polyResidual ... v` is not the intended \(Q\).

**Second: make `prim` explicitly zero-normalised.** Require
```lean
derivative (primZero P) = P
(primZero P).eval 0 = 0
```
Otherwise the flat term includes a subtraction at zero.

I would introduce these wrappers:

```lean
def polyResidual (L : ℕ) (P : Polynomial ℝ) (v : ℝ) : ℝ :=
  gaussLaplaceL L (v ^ 2) -
    (Ioi (1 : ℝ)).indicator
      (fun v => P.eval (2 * Real.log v) / v) v

noncomputable def residualMass (L : ℕ) (P : Polynomial ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), polyResidual L P v

def HasPolyRate (L : ℕ) (P : Polynomial ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℝ, 1 ≤ N →
    |Real.sqrt N * gaussLaplaceL L N - P.eval (Real.log N)| ≤
      K * (1 + Real.log N) / Real.sqrt N
```

Your hypothesis gives the residual tail **directly** at \(N=v^2\). No separate polynomial-growth estimate belongs in that argument. The small-\(v\) hypothesis comes from the existing \(0\le Z_L\le1\), not from `HasPolyRate`.

### Use Hasse derivatives for the Taylor step

Define a local polynomial-valued wrapper `taylorPiece P j`, representing
\[
H_jP=\frac{P^{(j)}}{j!}.
\]
Its central contract should be:

```lean
theorem eval_add_eq_sum_taylorPiece (P : Polynomial ℝ) (x y : ℝ) :
    P.eval (x + y) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (taylorPiece P j).eval x * y ^ j
```

Then define
\[
\boxed{
\operatorname{stepPoly}(P,Q)
=\frac1s\operatorname{primZero}(P)
+\frac2s\sum_{j=0}^{\operatorname{natDegree}P}
       2^jJ_j\,H_jP
+\frac{2Q}s.
}
\]

This avoids factorial division throughout the analytic proof. Prove the ordinary-derivative identification once, for presentation and coefficient calculations.

**API advice:** first inspect the pinned `Polynomial.taylor` and `Polynomial.hasseDeriv` declarations. I would not assume the proposed theorem names or argument orders without that inspection. The natural route is:

1. evaluate `P.taylor x` at \(y\);
2. expand that evaluation as a finite coefficient sum;
3. identify its \(j\)-th coefficient with \((H_jP)(x)\).

If the bridge is missing, prove it once using polynomial induction. Do **not** make the engine itself carry a double binomial sum and reindexing argument.

### Which steps are risky?

**(iii), the flat primitive, is comparatively routine.** Isolate:

```lean
theorem integral_poly_log_div
    (P : Polynomial ℝ) {N : ℝ} (hN : 1 ≤ N) :
    -- a = 1 / sqrt N, ℓ = log N
    (∫ x in a..1, P.eval (ℓ + 2 * Real.log x) / x) =
      (primZero P).eval ℓ / 2
```

Composition of polynomial differentiation with `Real.log`, endpoint identities, and FTC should suffice. The interval stays away from zero. Handle \(N=1\) naturally as a degenerate interval.

**(iv) is an API risk, not a mathematical risk.** Once the local Taylor lemma exists, the real work is likely:

- integrability of the finitely many moment terms;
- exact remainder bookkeeping;
- uniformly packaging the cutoff estimate for arbitrary degree.

For the cutoff, **do not initially optimise each derivative’s degree**. The coarser estimate
\[
|(H_jP)(\ell)|\le C_j(1+\ell)^d,\qquad d=P.\mathrm{natDegree},
\]
is enough. Sum finitely many constants, then invoke a standalone absorption lemma:

```lean
theorem exists_log_pow_cutoff_constant (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      (1 + Real.log N) ^ d * N ^ (-(3 / 4 : ℝ)) ≤
        C * (1 + Real.log N) / Real.sqrt N
```

Here the powers with real exponents are `Real.rpow`. Prove this independently by exponential domination, splitting \(d\le1\) from \(d>1\), or using an exponential-series bound.

The resulting theorem is your intended one:

```lean
theorem HasPolyRate.step
    (hL : 2 ≤ L) (h : HasPolyRate L P) :
    HasPolyRate (L + 1) (stepPoly P (residualMass L P))
```

No degree-exactness or leading-coefficient hypothesis is needed.

### Constants and acceptance tests

With zero-normalised primitive,
\[
(\operatorname{stepPoly}(P,Q))(0)
=\frac2s\left[\sum_j2^jJ_j(H_jP)(0)+Q\right].
\]
Yes: this is the next constant term.

Your acceptance tests are exactly right:

```lean
theorem hasPolyRate_three : HasPolyRate 3 P₃

theorem stepPoly_three :
    stepPoly P₃ (residualMass 3 P₃) = P₄

theorem stepPoly_four :
    stepPoly P₄ (residualMass 4 P₄) = P₅
```

If existing `Q₃`, `Q₄` have different definitions, add explicit residual-mass identification lemmas. Prove the polynomial identities coefficientwise, then recover the existing depth-four and depth-five rate statements by rewriting `.step`.

Also test the zero and constant polynomials in the purely algebraic `stepPoly` API; these catch `natDegree` and primitive-normalisation mistakes cheaply.

**Estimate:** 2–3 days is a plausible best case with the existing depth-five decomposition reusable. I would budget **3–5 focused days** for a clean reusable interface. Taylor alone should not dominate that budget.

---

## 3. Day-sized alternatives

### Ranking by short-term certainty

1. **Strict positivity and conditional normalisation**, bundled.
2. **Surrogate posterior as a ratio of finite closed-piece integrals**, using the note’s precise likelihood weight.
3. **Moment-to-\(G_r\) bridge**, without identifying \(G_r\) with Gamma derivatives.
4. **All-order Gamma differentiation under the integral.**
5. **Cone \(c_3\)**, unless a next-order remainder theorem is already available.

The engine remains the highest-value structural project; items 1–3 are cheaper deliverables, not substitutes.

### (a) Gamma bridge: separate the inexpensive and expensive stages

Under the convention
\[
h(x)=e^{-x^2/2}-\mathbf1_{(0,1]}(x),\qquad
J_k=\int_0^\infty h(x)\frac{\log^k x}{x}\,dx,
\]
put
\[
G_r=\int_0^\infty e^{-u}\log^r u\,du.
\]
Then
\[
I_k:=\int_0^\infty
 (e^{-u}-\mathbf1_{(0,1]}(u))\frac{\log^k u}{u}\,du
=\frac{G_{k+1}}{k+1},
\]
and the cutoff shift under \(u=x^2/2\) gives
\[
\boxed{
J_k=\frac1{2^{k+1}}\left[
\sum_{r=0}^k\binom kr(\log2)^{k-r}\frac{G_{r+1}}{r+1}
+\frac{(\log2)^{k+1}}{k+1}
\right].
}
\]

That is a useful standalone formal target.

I would **not promise stage 4 in one day**, and would not assume an existing all-order Gamma-integral derivative theorem on this pin. A robust construction is
\[
F_r(a)=\int_0^\infty e^{-u}u^{a-1}\log^r u\,du,
\qquad F_r'(a)=F_{r+1}(a).
\]
Prove the derivative relation locally for \(a>0\), using a compact parameter interval inside \((0,\infty)\), then induct. Near \(a=1\), domination splits into \(u^{-1/2}|\log u|^r\) near zero and an exponential envelope at infinity. The dominated-differentiation API is the right family, but envelope and induction bookkeeping are substantial.

### (b) Conditional density and posterior mean

The genuinely day-sized statement is:
\[
p_\lambda(z)=\rho(\lambda,z)/m(\lambda)
\quad\text{is a probability density for every interior }\lambda.
\]

A useful additional exact calculation is the **unweighted conditional mean**. Let
\[
A_\pm=\log(V/M_\pm^2).
\]
Since
\[
\int_0^M z\,\operatorname{nbClosed}(M,V,z)\,dz
=\frac{M^2}{2}\left(\log(V/M^2)+1\right),
\]
one gets
\[
\mathbb E[\mu\mid\lambda]
=\frac{M_+^2(A_++1)-M_-^2(A_-+1)}{2m(\lambda)}.
\]

Do not identify this with the note’s **surrogate posterior** mean: that also includes the surrogate likelihood weight. For a positive bounded weight \(w\), its mean is
\[
\frac{
 \int_0^{M_+}z\,w(z)C_+(z)\,dz
-\int_0^{M_-}z\,w(-z)C_-(z)\,dz
}{
 \int_0^{M_+}w(z)C_+(z)\,dz
+\int_0^{M_-}w(-z)C_-(z)\,dz
},
\]
where \(C_\pm=\operatorname{nbClosed}(M_\pm,V,\cdot)\).
This is a clean day-sized bridge to `nb_postmu`; substitute the note’s exact weight before claiming that identification.

### Top-choice Lean interface

Below, retain the existing interior hypotheses as section variables:

```lean
theorem nbClosed_pos
    (hz : 0 < z) (hzM : z < M) (hM2 : M ^ 2 ≤ V) :
    0 < nbClosed M V z

theorem nbFibreDensity_pos_iff (z : ℝ) :
    0 < nbFibreDensity l₁ l₂ z ↔
      -nbMminus l₁ l₂ < z ∧
      z < nbMplus l₁ l₂ ∧ z ≠ 0

theorem nbFibreMass_pos :
    0 < nbFibreMass l₁ l₂

noncomputable def nbConditionalDensity (l₁ l₂ z : ℝ) : ℝ≥0∞ :=
  nbFibreDensity l₁ l₂ z /
    ENNReal.ofReal (nbFibreMass l₁ l₂)

theorem lintegral_nbConditionalDensity :
    ∫⁻ z, nbConditionalDensity l₁ l₂ z = 1
```

Then define the measure by `volume.withDensity` and prove `IsProbabilityMeasure`. This completes the probabilistic interpretation of DCLX with very little new analysis—and records the crucial distinction between the joint-coordinate density \(\rho\) and its normalised conditional density.