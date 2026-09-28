## 1. Fidelity and the Mellin computation

**Yes: your coefficient and bracket coincidence are correct.** This is a mathematical consistency check of the supplied statements, not an independent source audit.

- The `ε²/8` Taylor bound has the right normalization: the factor \(2\) in `ampJ`, the exponential remainder, and
  \[
  \int_0^\infty u^3e^{-u^4/2}\,du=\tfrac12
  \]
  give precisely \(\varepsilon^2/8\).
- The moment correction has sign
  \[
  I(\varepsilon)=I(0)-\tfrac14\varepsilon\log(1/\varepsilon)+O(\varepsilon).
  \]
  Consequently, multiplication by \(-\varepsilon\) contributes **positive**
  \(\tfrac14\varepsilon^2\log(1/\varepsilon)\).
- Frozen and moving linear terms cancel. Their logarithmic coefficients combine as
  \[
  -\tfrac3{16}+\tfrac14=\tfrac1{16}.
  \]
- The displayed bounds `2ε`, `3ε²`, `2ε²` are mutually consistent; `5ε²` follows by the triangle inequality. The final change of variables gives `5 * sqrt (2*pi)` with the displayed normalization.

Your Laurent calculation gives
\[
\frac{\sqrt{2\pi}}{32}
  \bigl(\log N+5\log2-\gamma\bigr)N^{-3/2}.
\]
The cancellation involving \(\psi(3/2)-\psi(1/2)=2\) is exactly as you describe.

For HEADLINES, prefer:

> “The integral proof recovers the \(N^{-3/2}\log N\) coefficient predicted by the double pole of \(\zeta\) at \(-3/2\).”

“Is the double pole … read off from the integral” conflates the pole with its transferred coefficient, including the Gamma multiplier. It also risks suggesting that a Mellin-transfer theorem was used formally.

---

## 2. A substantially slicker route for candidate (x)

There is an **exact Bessel-type representation**, so do not begin by evaluating the separate frozen/moving finite parts.

Write
\[
J(\varepsilon)=\operatorname{ampJ}(a_\varepsilon,\varepsilon),
\qquad z=\varepsilon^2/16.
\]
With \(u=\sqrt{\varepsilon}\sinh(s/4)\),
\[
\boxed{
J(\varepsilon)=\frac12\int_0^\infty
  \exp\!\bigl(-z(\cosh s-1)\bigr)\,ds
=\frac12e^zK_0(z).
}
\]
Indeed,
\[
u^4+\varepsilon u^2
=\frac{\varepsilon^2}{8}(\cosh s-1),
\qquad
\frac{2\,du}{\sqrt{u^2+\varepsilon}}=\frac12\,ds.
\]

This explains the coefficient coincidence without separate finite-part computations. Put
\[
L(z)=\tfrac12(\log(2/z)-\gamma).
\]
The standard small-\(z\) expansion yields
\[
\tfrac12e^zK_0(z)
=(1+z)L(z)+O\!\left(z^2(1+\log(1/z))\right).
\]
Therefore
\[
\boxed{
J(\varepsilon)
=\log(4/\varepsilon)+R_\infty
+\frac{\varepsilon^2}{16}\log(1/\varepsilon)
+\frac{5\log2-\gamma}{32}\varepsilon^2
+O\!\left(\varepsilon^4(1+\log(1/\varepsilon))\right).
}
\]

**Important:** the requested \(O(\varepsilon^3\log(1/\varepsilon))\) is unnecessarily weak. Since \(\varepsilon=N^{-1/2}\), it would give only an \(O(N^{-2}\log N)\) evidence remainder, not the proposed \(O(N^{-5/2}\log N)\).

### Lean route without a Bessel library

Define the integral above as `blowBesselProfile z`. Prove, for \(z>0\),
\[
zH''+(1-2z)H'-H=0.
\]
Equivalently,
\[
(ze^{-2z}H')'=e^{-2z}H.
\]
A useful resulting integral identity is
\[
H'(z)=\frac{e^{2z}}z
 \left(-\frac12+\int_0^z e^{-2t}H(t)\,dt\right).
\]
Together with the already-established logarithmic asymptotic, this permits a quantitative bootstrap to \((1+z)L(z)\), without formalizing Gamma continuation or contour shifting.

The boundary constant \(-1/2\) needs proof; it must not be obtained merely by differentiating an asymptotic equivalence.

**Estimate:** about **2–4 units**: exact substitution; differentiation/integration-by-parts and boundary control; quantitative ODE bootstrap; final packaging. Less if suitable Bessel or singular-ODE infrastructure already exists.

`lintegral_blowK_gauss_closed` alone supplies neither Mellin inversion nor contour shifting. I cannot determine repository API availability from its name. A transfer route additionally needs strip continuation, vertical estimates and a justified contour displacement.

---

## 3. Ranking

For a bounded, independently useful **next unit**, I recommend:

1. **(v) Product-radial cone corner**, with an explicit quadratic error.
2. **(x) Exact constant**, through the exact representation above—not term-by-term finite parts.
3. **(vii) Localized NB exact-phase replacement.**

Reasons:

- **(v)** admits an elementary exact cancellation identity. It needs neither differentiation under an improper integral nor general Leray regularity.
- **(x)** is now much more attractive, but still introduces nontrivial differentiation and singular-boundary infrastructure.
- **(vii)** has a cheap pointwise inequality but a potentially expensive useful conclusion. Localization, uniform coercivity, phase-error order, and treatment of \(V<v_0\) remain necessary. The pointwise bound alone does not preserve the \(N^{-3/2}\log^2N\) coefficient.

If the next milestone must remain specifically about the blow-up example, select **(x)**. Otherwise, take the following cone unit.

---

## 4. Recommended unit: product-radial cone corner

### Contract

Use **Lipschitz profiles with an upper cutoff**, stronger quantitatively and easier analytically than starting with `ContDiff`.

Let \(R>0\), \(L_f,L_g\ge0\), \(M_f,M_g\ge0\), with

\[
|f(x)-f(y)|\le L_f|x-y|,\qquad
|g(x)-g(y)|\le L_g|x-y|,
\]
\[
|f(x)|\le M_f,\quad |g(x)|\le M_g\quad(x\ge0),
\]
\[
f(x)=g(x)=0\quad(x\ge R).
\]

Lean-facing assumptions:

```lean
{Lf Lg : ℝ≥0} {R Mf Mg : ℝ}
(hR : 0 < R)
(hfLip : LipschitzWith Lf f)
(hgLip : LipschitzWith Lg g)
(hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
(hfBound : ∀ x, 0 ≤ x → |f x| ≤ Mf)
(hgBound : ∀ x, 0 ≤ x → |g x| ≤ Mg)
(hfCut : ∀ x, R ≤ x → f x = 0)
(hgCut : ∀ x, R ≤ x → g x = 0)
```

Global Lipschitz assumptions are a convenience; only the nonnegative half-line is used. A later wrapper can extract these witnesses from \(C_c^1(\mathbb R)\).

### Definitions

```lean
noncomputable def coneProductPrior
    (f g : ℝ → ℝ) (u : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  f (u.1.1 ^ 2 + u.1.2 ^ 2) *
  g (u.2.1 ^ 2 + u.2.2 ^ 2)

noncomputable def coneProductDensity
    (f g : ℝ → ℝ) (v : ℝ) : ℝ :=
  2 * Real.pi ^ 2 *
    ∫ q in Ioi (0 : ℝ),
      f (q + 2 * max v 0) *
      g (q + 2 * max (-v) 0)
```

This fixed-domain definition avoids moving endpoints entirely.

### Core lemma list

#### A. Fixed finite support and integrability

For every \(v\), the density integrand vanishes for \(q\ge R\). Hence its `Ioi 0` integral equals its `Ioc 0 R` integral and is integrable.

Also prove:

\[
|L(v)|\le2\pi^2RM_fM_g,
\qquad
L(v)=0\quad\text{if }R/2\le |v|.
\]

A convenient continuity certificate is the explicit Lipschitz bound
\[
|L(v)-L(w)|
\le4\pi^2R(L_fM_g+M_fL_g)|v-w|.
\]

#### B. Positive/negative evaluation

For \(t\ge0\),
\[
L(t)=2\pi^2\int_0^\infty f(q+2t)g(q)\,dq,
\]
\[
L(-t)=2\pi^2\int_0^\infty f(q)g(q+2t)\,dq.
\]

#### C. Half-line shift identity

For the relevant compactly supported integrable \(h\), and \(a\ge0\),
\[
\int_0^\infty h(q+a)\,dq-\int_0^\infty h(q)\,dq
=-\int_0^a h(q)\,dq.
\]

Prove this as a reusable lemma with explicit integrability hypotheses, rather than specializing immediately to \(fg\).

#### D. Exact symmetric-corner identity

Define
\[
\Delta_a f(q)=f(q+a)-f(q).
\]
Then, for \(t\ge0\),
\[
\boxed{
L(t)+L(-t)-2L(0)
=-2\pi^2\int_0^{2t}f(q)g(q)\,dq
-2\pi^2\int_0^\infty\Delta_{2t}f(q)\Delta_{2t}g(q)\,dq.
}
\]

The algebraic identity behind it is simply
\[
f(q+a)g(q)+f(q)g(q+a)-2f(q)g(q)
=\Delta_a(fg)(q)-\Delta_af(q)\Delta_ag(q).
\]

This is the key simplification: **no derivative interchange**.

#### E. Explicit error bound

The two estimates are
\[
\left|\int_0^{2t}(f(q)g(q)-f(0)g(0))\,dq\right|
\le2(L_fM_g+M_fL_g)t^2,
\]
and
\[
\left|\int_0^\infty\Delta_{2t}f(q)\Delta_{2t}g(q)\,dq\right|
\le4RL_fL_gt^2.
\]

Thus define

```lean
noncomputable def coneCornerErrorConst
    (R Mf Mg : ℝ) (Lf Lg : ℝ≥0) : ℝ :=
  4 * Real.pi ^ 2 *
    ((Lf : ℝ) * Mg + Mf * (Lg : ℝ) +
      2 * R * (Lf : ℝ) * (Lg : ℝ))
```

and prove

```lean
theorem coneProductDensity_corner_bound
    -- assumptions above
    {t : ℝ} (ht : 0 ≤ t) :
    |coneProductDensity f g t +
       coneProductDensity f g (-t) -
       2 * coneProductDensity f g 0 +
       4 * Real.pi ^ 2 * f 0 * g 0 * t|
      ≤ coneCornerErrorConst R Mf Mg Lf Lg * t ^ 2
```

**Split points:** exactly \(0,2t\) for the boundary term and \(0,R\) for the increment product. No restriction \(t\le1\) is needed.

For \(t>0\), divide to obtain error at most `C * t`, and conclude

```lean
Tendsto
  (fun t : ℝ =>
    (coneProductDensity f g t +
      coneProductDensity f g (-t) -
      2 * coneProductDensity f g 0) / t)
  (𝓝[>] 0)
  (𝓝 (-4 * Real.pi ^ 2 * f 0 * g 0))
```

### Geometric identification: include it, or explicitly defer it

An analytic profile theorem alone is not yet a theorem about the pushforward of `coneQ`.

For nonnegative \(f,g\) on `Ici 0`, prove

```lean
Measure.map coneQ
    (volume.withDensity
      (fun u => ENNReal.ofReal (coneProductPrior f g u))) =
  volume.withDensity
    (fun v => ENNReal.ofReal (coneProductDensity f g v))
```

The clean infrastructure is:

1. Generalize the **two radial reductions** to arbitrary nonnegative measurable \(H(p,t)\).
2. Generalize the quadrant change of variables:
   \[
   (p,t)=
   \bigl(q+2\max(v,0),\,q+2\max(-v,0)\bigr),
   \]
   with Jacobian \(2\), on the two half-planes \(v>0\), \(v<0\).
3. Specialize \(H\) to the profile product and a test function of \((p-t)/2\).
4. Bridge the inner `lintegral` to `ofReal` of the integrable real integral.

The Gaussian-only pushforward theorem does **not** directly imply this weighted result. Reuse/generalize the proofs of `lintegral_cone_gauss` and `lintegral_quadrant`.

**Size:** one unit for the analytic identity/bound; another if the weighted quadrant generalization proves substantial. With easy proof reuse, both can fit one larger unit. Do not label the analytic-only result “general-prior Leray corner”.

### Mathlib touchpoints

Use existing repository coordinate-change helpers first. Relevant Mathlib APIs include:

- `LipschitzWith.continuous`;
- integrability of continuous functions on compact intervals;
- translation/change-of-variable lemmas for interval and set integrals;
- `intervalIntegral.integral_add_adjacent_intervals`;
- `integral_add`, `integral_sub`, and norm-of-integral inequalities;
- Tonelli/`lintegral_prod`;
- `lintegral_map` and `withDensity` integration;
- a squeeze argument for the final right-hand limit.

Check exact local lemma names before implementation, especially for affine substitutions and restricted integrals.

---

## 5. Convention hazards

1. **Do not require `support f ⊆ Icc 0 R`.** Continuity would force \(f(0)=0\), trivializing the corner coefficient. Require only an upper cutoff on the nonnegative half-line.
2. The density includes **\(2\pi^2\)**: \(\pi^2\) from the two squared-radius reductions, and \(2\) from \(q=(p-t)/2\).
3. The symmetric quotient tends to the derivative jump:
   \[
   -4\pi^2F(0).
   \]
   The coefficient of \(|v|\) is half of this:
   \[
   B_F(0)=-2\pi^2F(0).
   \]
4. The quotient limit is explicitly **from \(t>0\)**. A two-sided quotient has the opposite sign on the negative side.
5. The analytic bound allows signed profiles. A `withDensity (ofReal ...)` identification requires nonnegativity; otherwise `ofReal` truncates rather than represents a signed measure.
6. `Ioi`, `Ioc`, and interval-integral endpoint changes need explicit null-endpoint bridges.
7. This unit proves a quantitative product-radial corner theorem—not the full smooth decomposition \(A_F+B_F|v|\) for arbitrary priors.

**Recommendation:** take the cone product-radial identity next, and record the exact \(e^zK_0(z)/2\) representation as the design decision for the subsequent blow-up constant unit.