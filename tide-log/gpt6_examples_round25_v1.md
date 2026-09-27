## 1. Fidelity: yes, with two scope qualifications

**(a) Normalisations check out.** Writing \(s=\sqrt{2\pi}\),
\[
\frac{2^k k!a_k}{(2u)^{k+1}}
=\frac{k!a_k}{2u^{k+1}}
=\frac{s^Lk!a_k\,u^{L-k}}{2s^Lu^{L+1}}.
\]
Thus reindexing \(j=L-k\) gives exactly `depthPoles_sum_eq`.

Likewise, using \(\Gamma(u)=\Gamma(1+u)/u\),
\[
\frac{2^{L(u-1/2)}\Gamma(1/2-u)\Gamma(u)^{L+1}}
 {2\pi^{(L+1)/2}}
=\frac{H_{L+1}(u)}{2s^Lu^{L+1}}.
\]
The hypothesis `hu0 : 0 < u` supplies the recurrence and nonzero denominator conditions.

**(b)** Apply uniqueness with **`n := L + 1`**:
\[
c_j=s^L(L-j)!a_{L+1,L-j},\qquad q=2s^LQ_{L+1},
\]
cast into \(\mathbb C\). Only `j < L + 1` matters for `c`; truncated natural subtraction outside that range is harmless. `tendsto_depthJet_scaled` is precisely `hc`.

**(c)** Correct: in one dimension, evaluating the degree-\(j\) multilinear coefficient on \(j\) copies of `1` gives the scalar coefficient. `factorial_smul` identifies
\[
j!\,p_j(1,\ldots,1)=f^{(j)}(0).
\]
Division by the nonzero factorial gives your coefficient. At another evaluation vector, the additional factor is \(y^j\).

Scope qualifications:

- The engine identifications currently cover **depth \(D\ge2\)**.
- `depthJetCoeff_im` currently proves reality only for **`j ≤ D`**, not all Taylor coefficients. Both are exactly sufficient for the engine conclusions.

## 2. Ranking and recommended interfaces

**Priority:** **(i) all-orders duplication → (iii) logarithmic-derivative recurrence → (iv) depth-five instance → (v).** Fold **(ii)** into a small regression section/file alongside (i); it need not consume a separate day-sized target.

### (i) All-orders duplication: use α internally, expose β

I would make this **two bounded units**: generic jet multiplication, then Gamma duplication. Do not make discovering a multilinear-series multiplication API the critical path.

#### Generic Leibniz statement

This is the exact open-set interface I would expose:

```lean
theorem iteratedDeriv_mul_of_analyticOnNhd
    {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U)
    {z : ℂ} (hz : z ∈ U) (n : ℕ) :
    iteratedDeriv n (fun w => f w * g w) z =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) *
          iteratedDeriv k f z *
          iteratedDeriv (n - k) g z
```

Induct **generalising `z`**. For the successor step:

1. The induction hypothesis holds at every point of `U`.
2. Openness gives eventual equality near `z`.
3. Differentiate that equality.
4. Differentiate the finite sum and products, using analyticity of the iterated derivatives.
5. Finish with a separate finite-sum Pascal identity.

Keep the Pascal arithmetic separate from the analytic proof. In particular, resolve identities involving `n - k` under the relevant range bounds before rewriting.

Also expose the more convenient local wrapper:

```lean
theorem iteratedDeriv_mul_of_analyticAt
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (n : ℕ) :
    iteratedDeriv n (fun w => f w * g w) z =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) *
          iteratedDeriv k f z *
          iteratedDeriv (n - k) g z
```

The local wrapper follows by shrinking to a common open analytic neighbourhood.

#### Immediately package the normalized version

```lean
noncomputable def jetCoeff (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f z / (n.factorial : ℂ)

theorem jetCoeff_mul
    {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (n : ℕ) :
    jetCoeff (fun w => f w * g w) z n =
      ∑ k ∈ Finset.range (n + 1),
        jetCoeff f z k * jetCoeff g z (n - k)
```

This is the reusable **one-dimensional Cauchy product** you need. Prove factorial/binomial cancellation once.

I cannot certify an exact `FormalMultilinearSeries.mul`/`HasFPowerSeriesAt.mul` route at this pin from the supplied scout. Even if multiplication exists, extracting its scalar coefficient formula may cost more than α.

There is also a genuine β alternative using your new infrastructure: multiply finite Taylor polynomials, bound the discarded terms by \(O(u^{n+1})\), then invoke jet uniqueness. That avoids Leibniz but introduces convolution/remainder bookkeeping. **My default remains α → normalized β.**

#### Duplication’s public endpoint

Define
\[
g_n=\frac{\Gamma^{(n)}(1)}{n!},\qquad
e_n=\frac{\Gamma^{(n)}(1/2)}{\sqrt\pi\,n!},\qquad \ell=\log2.
\]
Use the **shifted identity near zero**
\[
\frac{\Gamma(1/2+z)\Gamma(1+z)}{\sqrt\pi}
=e^{-2\ell z}\Gamma(1+2z).
\]
This avoids carrying the unshifted affine factors through every theorem.

Expose `g_zero`, `e_zero`, the convolution identity, and especially:

```lean
theorem gammaHalfCoeff_succ (n : ℕ) :
    gammaHalfCoeff (n + 1) =
      (∑ k ∈ Finset.range (n + 2),
        (2 : ℂ) ^ k * gammaOneCoeff k *
          (-2 * (Real.log 2 : ℂ)) ^ (n + 1 - k) /
          ((n + 1 - k).factorial : ℂ)) -
      ∑ k ∈ Finset.range (n + 1),
        gammaHalfCoeff k * gammaOneCoeff (n + 1 - k)
```

Here `gammaHalfCoeff n` divides by
`(Real.sqrt Real.pi : ℂ) * (n.factorial : ℂ)`.

This successor form is the right **rewrite interface**: no self-reference on the right. Keep the raw binomial derivative identity as a companion theorem, not the main computational API.

For orders four and five: instantiate finitely, expand the finite sums, rewrite lower orders, then `ring`. Prefer explicit rewrites over a global `[simp]` attribute on the recursive theorem, to avoid expansion blow-up.

### (ii) Depth-three regression: fold it in

Worth keeping, but not a standalone conceptual unit.

First try to recover the equalities from the already proved engine coefficient and residual-mass identifications, plus `depthJetCoeff_im`. That avoids replaying `cubicH'`/`cubicH''` differentiation.

If connecting the functions directly, prove a neighbourhood equality with the correctly normalized cubic function, then transport iterated derivatives. Equality merely at zero is insufficient.

### (iii) Recurrence packaging: use \(H'/H\), not a global logarithm

For an analytic \(H\) with \(H(0)\ne0\), define
\[
h_n=[z^n]H,\qquad
q_n=[z^n]\frac{H'}H.
\]
The clean generic theorem is:

```lean
theorem jetCoeff_succ_mul
    {H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (h0 : H 0 ≠ 0) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * jetCoeff H 0 (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        jetCoeff (fun z => deriv H z / H z) 0 j *
          jetCoeff H 0 (n - j)
```

Proof: nonvanishing locally, analyticity of the quotient, local identity
`deriv H = (deriv H / H) * H`, then `jetCoeff_mul`.

Set \(b_{n+1}=q_n/(n+1)\), \(b_0=0\). This gives the requested recurrence without logarithmic branch obligations.

**Local principal logs would also work:** Gamma at \(1\) and \(1/2\) is positive real, so shrink until its values lie in the slit plane. But analyticity of `Complex.log ∘ Gamma` on the entire right half-plane does not follow merely from Gamma’s nonvanishing.

Also, your displayed \(B_D\) needs the constant **\(-\tfrac12\log\pi\)** to equal \(\log H_D\). Its omission does not affect derivatives.

Once the digamma bridge is proved or supplied explicitly, the expected coefficients are
\[
b_1=(D+1)\ell-(D-1)\gamma,\qquad
b_n=\frac{(2^n-1)+D(-1)^n}{n}\zeta(n)\quad(n\ge2).
\]
Keep these as a separate bridge, not hidden inside recurrence packaging. Your stated polygamma–zeta formulas require **derivative order at least one**; order zero uses the separate digamma values.

### (iv) Depth five

After duplication, this is a useful acceptance test rather than new infrastructure: eliminate half-point derivatives through order four, substitute DCLXXIII, and normalize by `ring`. Keep the exact meanings of `λ₃, λ₄` explicit—raw Gamma derivatives and logarithmic derivatives are different coordinates.

## 3. Convention hazards

- **`.re`:** do algebra in \(\mathbb C\), establish reality, then take real parts. Do not silently replace complex multiplication by multiplication of real parts.
- **Depth indexing:** use `D` in generic Gamma/jet APIs; substitute `D := L + 1` only at the engine boundary. Current engine theorems require `L ≥ 1`.
- **Reality scope:** duplication can additionally prove all-order reality of the half-point jet from the one-point jet, beyond the current `j ≤ D` result.
- **Iteration:** use `iteratedDeriv` consistently. Transport recursive derivative identities through the library’s defining lemmas; do not assume `iteratedDeriv n f` and `deriv^[n] f` unfold in the direction your induction wants.
- **Local identities:** Gamma duplication, quotient identities, and branch-sensitive rewrites need only hold eventually near the expansion point. Keep that locality explicit rather than proving unnecessarily global statements.