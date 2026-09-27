## 1. Fidelity check

**DCXVIII–DCXX meet the round-7 specifications, on the supplied statements.** I have not independently built the pinned checkout.

- **DCXVIII:** the factor `2π` correctly converts the probability-normalised Gaussian DLN integral to the crossing integral with unnormalised prior. Both the constant and the remainder scale correctly.
- **DCXIX:** `18` is a useful strengthening of the requested `∃ C`. The four allocations `1 + 2 + 14 + 1` support exactly
  \[
  O\!\left(\frac{1+\log N}{\sqrt N}\right),\qquad N\ge1.
  \]
  This proves the leading coefficient, **not** the second coefficient: the latter is precisely within the error allowance. Keeping `1 + log N` is important at `N = 1`.
- **DCXX:** yes—the integral in transported normal coordinates is the right coordinate-level formalisation. Pointwise transport is sufficient; no change-of-variables theorem is missing from this statement.

For the note, additionally give the invariant formulation, while distinguishing it from the already formal coordinate theorem. A small algebraic bridge would remove that distinction:

\[
P_{x,y}(B)=P_xB+BP_y-P_xBP_y,\qquad
P_x=\frac{xx^\top}{\|x\|^2},\quad P_y=\frac{yy^\top}{\|y\|^2}.
\]

For nonzero `x,y`, this is the Frobenius-orthogonal projection onto
\[
T_A=\operatorname{range}D_{x,y},\qquad A=xy^\top.
\]
At the displayed orbit point, prove
\[
\|P_{x,y}\Xi\|_F^2
 =\operatorname{crossNormSq}(U^\top\Xi V).
\]

**That bridge is day-sized and high-value.** It still does not prove the Morse–Bott passage from the full model to its normal integral.

---

## 2. Ranked round-8 targets

My ranking among the proposed analytic targets is **(e), (a), (b)**, with deliberately limited scope for (e) and (b).

### 1. Monomial renormalised constant — a reliable day-sized target

For an integer `k ≥ 1`, the proposed identity is correct:
\[
2\int_0^\infty
 \frac{e^{-u^{2k}/2}-\mathbf1_{(0,1]}(u)}u\,du
 =\frac{\log2-\gamma}{k}.
\]

Prefer a split-integral interface, avoiding an indicator inside the principal theorem:

```lean
-- Proposed interface; powers here are natural-number powers.
theorem monomial_renorm_constant {k : ℕ} (hk : 0 < k) :
    2 * ((∫ u in Ioc (0 : ℝ) 1,
            (Real.exp (-(u ^ (2 * k)) / 2) - 1) / u) +
         (∫ u in Ioi (1 : ℝ),
            Real.exp (-(u ^ (2 * k)) / 2) / u)) =
      (Real.log 2 - Real.eulerMascheroniConstant) / (k : ℝ)
```

Export integrability of both pieces separately.

**Route:** substitute `v = u^k` and reduce directly to the existing `k = 1` Gaussian renormalised constant. Both domains retain endpoint `1`; `du/u = dv/(k v)`. This is cleaner than substituting `u^(2k)/2`, which moves the splitting point.

**Scope warning:** this lemma alone does not establish every model’s two-term expansion. For
\[
K_k=\tfrac12x^2(x^{2k-2}+y^2),
\]
one still needs the scaling adapter and, if present, control of the rescaled Gaussian factor in `x`. Require **`k ≥ 2`** for that logarithmic expansion; `k = 1` is a different regime.

For the unnormalised standard Gaussian prior, the resulting target is
\[
Z_k(N)=\frac{\sqrt{2\pi}}{\sqrt N}
 \left[
 \frac{k-1}{k}\log N+2\log2+\frac{\log2-\gamma}{k}
 \right]+o(N^{-1/2}).
\]
At `k = 2`, this recovers the existing blow-up coefficients. Treat this family theorem as a follow-up, not part of the guaranteed one-day deliverable.

### 2. Depth-three second coefficient — realistically day-sized with the renormalised-constant API

Target:

```lean
theorem gaussLaplaceL_three_two_term :
    (fun N : ℝ =>
      gaussLaplaceL 3 N -
        ((Real.log N)^2 +
          4 * (2 * Real.log 2 - Real.eulerMascheroniConstant) *
            Real.log N) /
        (4 * Real.pi * Real.sqrt N))
      =O[atTop] (fun N => (Real.sqrt N)⁻¹)
```

An explicit-bound intermediate theorem is preferable:

```lean
∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
  |gaussLaplaceL 3 N - twoTermMain N| ≤ C / Real.sqrt N
```

Call this **two-term, with bounded residual**, rather than three-term: the constant coefficient remains unidentified.

**Two refinements are essential.**

1. **Do not replace `log(2*N*x²)` by `log(2*N)` in the depth-two remainder.** With `r = √N*x`,
   \[
   \int_{N^{-1/2}}^\infty
   \frac{\log(2Nx^2)+3}{N^{3/2}x^3}\,dx
   =
   \frac1{\sqrt N}\int_1^\infty
   \frac{\log(2r^2)+3}{r^3}\,dr
   =O(N^{-1/2}).
   \]
   This removes the artificial logarithmic loss.

2. **Keep the Gaussian on the whole outer region**, not merely the middle interval. Define
   \[
   h(x)=e^{-x^2/2}-\mathbf1_{(0,1]}(x).
   \]
   Use
   \[
   R_0=\int_0^\infty\frac{h(x)}x\,dx
      =\frac{\log2-\gamma}{2},
   \qquad
   \int_0^\infty\frac{|h(x)|(1+|\log x|)}x\,dx<\infty.
   \]
   The second integral only needs finiteness, not evaluation.

Writing `ℓ = log N`, `c = 3 log 2 − γ`, the assembled expression is
\[
Z_3(N)=\frac1{\pi\sqrt N}
 \left[\frac{\ell^2}{4}+\left(\frac c2+R_0\right)\ell+O(1)\right].
\]
Thus
\[
\frac1\pi\left(\frac c2+R_0\right)
=\frac{2\log2-\gamma}{\pi}.
\]

**Important:** the old crude tail estimate cannot remain in this proof; the tail contributes to the coefficient being identified.

### 3. Scalar leading-term propagation — scope one day to the reusable step

Use natural powers of `s = √(2π)`, not real powers of `2π`.

A clean all-depth statement, indexed to avoid truncated subtraction, is:

```lean
theorem gaussLaplaceL_leading_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |gaussLaplaceL (m + 2) t -
        (Real.log t)^(m + 1) /
          ((Nat.factorial (m + 1) : ℝ) *
            Real.sqrt (2 * Real.pi)^(m + 1) * Real.sqrt t)| ≤
        C * (1 + Real.log t)^m / Real.sqrt t
```

For the first day, prove an abstract propagation lemma. Define schematically:

```lean
GaussianStep f N := ∫ x : ℝ, gaussDensity x * f (N * x^2)
```

Assume:

- `Measurable f`;
- `0 ≤ f t ∧ f t ≤ 1` for `0 ≤ t`;
- for `t ≥ 1`,
  \[
  \left|f(t)-A\frac{(\log t)^{m+1}}{\sqrt t}\right|
  \le C\frac{(1+\log t)^m}{\sqrt t}.
  \]

Conclude the same bound for `GaussianStep f`, with leading coefficient
\[
A'=\frac{A}{(m+2)\sqrt{2\pi}}
\]
and error exponent `m+1`.

**Route:** the existing three-region split.

- Inner: boundedness by `1`.
- Middle: integrate the leading polynomial exactly; integrate the induction error rather than bounding its logarithm by `log N`.
- Gaussian replacement: use `1 − e^{-x²/2} ≤ x²/2`.
- Tail: use fixed-order Gaussian moments; avoid elaborate explicit constants.

The abstract step is a plausible but **stretch** day. The step **plus** the all-depth scalar recursion, boundedness API, induction, and limit theorem is not an honest guaranteed one-day package. Establish the general scalar recursion separately:

```lean
gaussLaplaceL (L + 1) N =
  ∫ x : ℝ, gaussDensity x * gaussLaplaceL L (N * x^2)
```

with the actual allowable depth range made explicit.

**Scheduling recommendation:** if three dependable one-day completions are required, replace target 3 by the invariant rank-one projection bridge above.

---

## Other candidates

### Naive Bayes envelope

The excerpt does **not** determine `M_±`, `ℓ_λ`, `c_λ`, `b_λ`, `L_λ`, or `φ_λ(0)` uniquely. In particular, a fibre support cutoff and a dominating envelope must not be identified merely because both use `M`. I would not invent these definitions from the displayed density.

Extract:

1. the exact `ρ(λ,z)` formula, including support;
2. the parameter domain and integration measure;
3. definitions of all six quantities and the proposed envelope;
4. the coefficient dependence on `λ`;
5. the local face chart and its Jacobian.

A **local face patch away from the other faces** is plausibly day-sized. The useful certificate is a bound of the form
\[
E(\lambda)\le C\,\lambda_1^{-a}
             (1+|\log\lambda_1|)^b,\qquad a<1,
\]
with remaining coordinates in a compact interior patch. This does not settle corners, joint measurability, or global envelope integrability.

### Cone averaged posterior

Supply the numerator and denominator integrands, observable, averaging measure, domain, and exact normalisation. In particular: is the target an average of posterior ratios or a ratio of averaged integrals? Those require different arguments.

### Blow-up observables

`x²` and `y²` are sensible first choices, but require distinct adapters:

- `x²` removes the logarithmic singularity in the reduced amplitude;
- integrating out `y` with observable `y²` changes the kernel from a square-root denominator to a three-halves power.

Start with **unnormalised numerators**, then divide by the established partition-function asymptotic. A leading numerator theorem can be day-sized; two-term posterior expansions should not be promised before checking the exact prior and amplitude interfaces.

---

## 3. Convention hazards

1. **`18` is not asymptotic data.** Keep it in the quantitative theorem; also export a Big-O wrapper so downstream proofs do not depend on that particular estimate.
2. **`depthThreeM` contains the depth-two constant.** Its integrated `log N` coefficient is not the final depth-three coefficient. The Gaussian correction, including the tail, supplies the difference.
3. **Transpose convention:**  
   `conjMat Uᵀ Vᵀ Ξ = Uᵀ * Ξ * V`. Export a matrix-form simp lemma to make this explicit.
4. **Argument order:** `gnDGen x ξ y η` is easy to misuse. A pair-based wrapper
   ```lean
   rankOneDifferential (x, y) (ξ, η)
   ```
   would improve theorem readability without changing the underlying definition.
5. **Projection requires nonzero factors.** The axis/orbit theorem has positive `α,β`; any invariant generalisation must retain the corresponding nondegeneracy assumptions.
6. **Coordinate integral versus full model:** DCXX integrates over a parametrised normal space. It does not yet assert orbit integration, its measure/Jacobian, or a Morse–Bott remainder.
7. **Prior normalisation remains visible:** crossing and blow-up constants must not be compared with probability-normalised DLN constants without the prior-mass factors.