## 1. Fidelity check

**On the supplied statements, all three round-14 targets are met.** This is a statement-level check, not a fresh repository build.

- **DCXLVI: indexing is exact.** Substituting \(L=m+4\) gives
  \[
  D_L=(m+5)\log2-(m+3)\gamma,\quad L+3=m+7,\quad
  (L-3)!=(m+1)!,\quad s^{L-1}=s^{m+3}.
  \]
  Together with `gaussLaplaceL_third_coeff`, `thirdCoeff_eq_closed` identifies the actual asymptotic coefficient, not merely a solution of the recurrence.

- **DCXLVII: no positivity assumption on \(a\) is needed.** Eventually \(a<z<1\). On \(0<v\le1\),
  \[
  |v^{z-1}q(v)|\le v^{a-1}|q(v)|,
  \]
  and on \(v>1\), it is bounded by \(|q(v)|\). Moreover, \(v^{a-1}\ge1\) near zero, so the hypotheses also imply integrability of \(q\) there. Negative \(a\) simply imposes stronger weighted integrability.

  **Scope caveat:** this proves a real, one-sided finite-part limit. It does not itself establish complex meromorphic continuation or a holomorphic residual.

- **DCXLVIII: the exponent bookkeeping is sound.**
  \[
  a-k\varepsilon+1
  =(a+1)\frac{k+2}{2(k+1)}>0.
  \]
  This includes \(k=0\). The corrected constant \((1+1/\varepsilon)^k\) is appropriate. The generic certificate does **not** settle the model-specific chart exponents, Jacobians, or fibre measurability; the note’s separation is correct.

## 2. Next targets: ranking and interfaces

My ranking is **(b), (a), then a bounded version of (e)**. Only the first two are confidently day-sized from the interfaces supplied. I would not promise a third model-specific theorem *with a rate* before inspecting the existing quantitative transfer bounds.

### 1. Polynomial-subtraction Mellin transfer — highest value/effort

This closes the abstraction already advertised in the note.

A convenient interface avoids requiring global measurability of an arbitrary representative of `Z`:

```lean
noncomputable def mellinLogTail {d : ℕ}
    (p : Fin (d + 1) → ℝ) (v : ℝ) : ℝ :=
  if 1 < v then (∑ k, p k * Real.log v ^ (k : ℕ)) / v else 0

theorem tendsto_mellin_sub_logPolynomial
    {d : ℕ} (p : Fin (d + 1) → ℝ)
    {q : ℝ → ℝ} {a : ℝ} (ha : a < 1)
    (hq : Measurable q)
    (hsmall : IntegrableOn
      (fun v => v ^ (a - 1) * q v) (Ioc 0 1))
    (hlarge : IntegrableOn q (Ioi 1)) :
    Tendsto
      (fun z : ℝ =>
        (∫ v in Ioi (0 : ℝ),
          v ^ (z - 1) * (q v + mellinLogTail p v)) -
        ∑ k : Fin (d + 1),
          p k * ((k : ℕ).factorial : ℝ) /
            (1 - z) ^ ((k : ℕ) + 1))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ v in Ioi (0 : ℝ), q v))
```

**Route:** establish integrability of the weighted residual for \(a<z<1\); use finite-sum integrability and the log-power transforms; prove exact cancellation on that interval; finish by eventual equality and `tendsto_mellin_residual`.

Do not use `integral_add` before supplying integrability: Lean’s totalised integral makes that a substantive requirement. An a.e.-decomposition adapter for a separately defined `Z` can follow.

### 2. Naive-Bayes Gaussian second log moment — honest day-sized

Yes: the Mellin derivative route at \(s=\tfrac12\) is the correct reuse. The domain condition \(0<\Re s\) gives ample room; this is not a boundary differentiation problem.

```lean
theorem integrable_gaussian_log_abs_sq :
    Integrable (fun z : ℝ =>
      Real.exp (-(z ^ 2) / 2) * (Real.log |z|) ^ 2)

theorem integral_gaussian_log_abs_sq :
    (∫ z : ℝ,
      Real.exp (-(z ^ 2) / 2) * (Real.log |z|) ^ 2) =
    Real.sqrt (2 * Real.pi) *
      (((Real.eulerMascheroniConstant + Real.log 2) ^ 2) / 4
        + Real.pi ^ 2 / 8)
```

**Route:**

1. Reuse the DCXXXVIII differentiation argument at \(s=\tfrac12\), obtaining
   \[
   \int_0^\infty t^{-1/2}e^{-t}\log^2t\,dt=\Gamma''(1/2).
   \]
2. Obtain the zeroth and first moments from \(\Gamma(1/2)\) and
   \[
   \Gamma'(1/2)=-\sqrt\pi(\gamma+2\log2).
   \]
   Check the existing first-derivative theorem name before starting.
3. Split the real integral by evenness and substitute \(z=\sqrt{2t}\):
   \[
   m_2=\frac{\sqrt2}{4}
   \left[\Gamma''(1/2)+2\log2\,\Gamma'(1/2)
                      +(\log2)^2\Gamma(1/2)\right].
   \]
4. Rewrite the Gamma values and finish algebraically.

The main effort is the change-of-variables and real/complex integral bridge, not new analysis. Package the half-Gamma log-moment identity separately: it is reusable.

### 3. Depth-four constant — first the moment and limit, not a promised rate

Avoid calling this `D₄`: that already denotes \(5\log2-3\gamma\) in the coefficient formulas. Use something like `depthFourConst`.

The final interface should be:

```lean
noncomputable def depthFourConst : ℝ := -- explicit residual/kernel integrals

theorem gaussLaplaceL_four_constant :
    Tendsto
      (fun N : ℝ =>
        Real.sqrt N * gaussLaplaceL 4 N -
          gaussCoeffA 0 * (Real.log N) ^ 3 -
          gaussCoeffB 0 * (Real.log N) ^ 2 -
          thirdCoeffClosed 0 * Real.log N)
      atTop (𝓝 depthFourConst)
```

**Route:** introduce the actual kernel’s second logarithmic moment, prove its absolute integrability at both endpoints, and run the existing transfer decomposition one order further. No evaluation in terms of \(H_3\) or \(\zeta(3)\) is required.

**Day-sized boundary:** the weighted-moment lemma and explicit constant definition are a credible day target. The limit is credible if DCXXXI/DCXXXIV already expose sufficiently strong remainder estimates. A rate does **not** follow from the displayed third-coefficient limit alone. Choose its explicit form only after auditing those estimates; do not guess an \(N^{-1/2}\)-type rate.

### Why not the other candidates?

- **(c) Cone \(c_3\):** worthwhile, but not safely one day. The exponential Taylor inequality is easy; integrable domination after the geometric rescaling and subsequent ratio algebra are the work. Also require \(x\ge0\) in the quoted inequality, and use \(G_2=\tfrac12\partial_\delta^2F\).

- **(d) Blow-up: correct the order before scheduling.** For the stated Gaussian model, \(\alpha_1=\sqrt{\pi/2}/16\) is the coefficient of
  \[
  N^{-3/2}\log N,
  \]
  not an ordinary \(N^{-1}\) term of \(Z_N\). Indeed, the unnormalised model has the Mellin identity
  \[
  \int_0^\infty N^{s-1}Z_N\,dN
  =2^{1-3s}\Gamma(s)\Gamma(1/2-s)^2,
  \qquad 0<s<\tfrac12.
  \]
  Its continuation has double poles at \(s=\tfrac12,\tfrac32,\ldots\), and no pole at \(s=1\). The double-pole coefficient at \(3/2\) is exactly \(\sqrt{\pi/2}/16\). Thus an \(O(N^{-3/2})\) remainder after only the leading two terms would omit a nonzero logarithm. The `AmplitudeJ` engine may help, but the proposed target needs reformulation first.

- **(f) Naive Bayes:** joint measurability is potentially a good day-sized target **if** the fibre family has an explicit fixed-domain measurable integral representation. The signatures here do not establish that. KL-versus-surrogate control is a larger geometric/uniformity task, not a safe one-day commitment.

## 3. Convention hazards

1. **Coefficient naming and offsets.** Keep `thirdCoeff` as the recursively defined asymptotic coefficient and `thirdCoeffClosed` as its formula. Add a user-facing corollary rewriting the existing limit directly to `thirdCoeffClosed m`. State “depth \(m+4\)” in both docstrings. Avoid globally marking the recursive definition for aggressive simplification.

2. **Product measure versus restricted cube.** The certificate uses
   ```lean
   Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1))
   ```
   not syntactically `volume.restrict cube`. Supply a named measure-identification or integrability adapter for
   ```lean
   {x : Fin d → ℝ | ∀ i, x i ∈ Ioo (0 : ℝ) 1}
   ```
   rather than expecting rewriting to happen automatically. Chart Jacobians remain additional factors.

   Also add an **a.e. domination adapter**: the current `hC : ∀ x, ...` unnecessarily demands control outside the cube.

3. **Measurability strength.** `Measurable q` is a sound, convenient first interface, but stronger than necessary. A later version can accept
   ```lean
   AEStronglyMeasurable q (volume.restrict (Ioi (0 : ℝ)))
   ```
   and use a measurable representative or the a.e. dominated-convergence interface. Keep the restricted measure explicit. This weakening is polish, not a correction to DCXLVII.