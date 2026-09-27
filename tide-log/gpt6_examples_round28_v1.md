## 1. Fidelity

**Mathematically sound, on the reported statements**—this is not an independent source audit.

- **Reality induction:** the recurrence
  \[
  \psi_n=(n+1)g_{n+1}-\sum_{j<n}\psi_jg_{n-j}
  \]
  proves reality by strong induction once every \(g_r\) is real. No additional analytic argument is needed. Identifying \(\psi_3=\lambda_4/6\) and \(\psi_4=\lambda_5/24\) is then the correct complex-valued conclusion, not merely a real-part identity.
- **Cone:** \(T'=-e^{-x^2/2}\) gives \(F'=xF-1\). Thus, writing \(A=\sqrt{\pi/2}\),
  \[
  F(x)=A-x+\frac A2x^2-\frac13x^3+\cdots.
  \]
  The vertex term is **negative**, \(-4\pi^2/N\).
- The reported scaled limit is exactly the third asymptotic coefficient:
  \[
  N^{3/2}\left(Z_N-4\pi^2A N^{-1/2}+4\pi^2N^{-1}\right)
  \longrightarrow 2\pi^2A.
  \]
  The next scaled correction is indeed \(-4\pi^2/(3\sqrt N)\).

## 2. Choose Route B

**Route B has less new analytic infrastructure at this pin.** Convexity replaces the singular Beta limit, its endpoint envelopes, and the subsequent Mellin/geometric-series integration.

I would make two simplifications:

1. Work on the fixed complex ball **`Metric.ball 0 (1/2)`**. Radius \(1\) is unnecessary for jets at zero.
2. Use **iterated termwise differentiation**, not a double-series-to-`HasFPowerSeriesAt` construction. The latter is mathematically elegant but introduces more Lean representation machinery unless the repository already has a scalar-power-series constructor and coefficient reader ready to use.

The following are **proposed interface signatures**, not claims that these declarations already exist or that their proofs have been compiled.

### Module 1: real digamma monotonicity and decay

Choose the real function to be the real part of complex digamma; then the real/complex bridge is isolated in one theorem.

```lean
noncomputable def realDigamma (x : ℝ) : ℝ :=
  (Complex.digamma (x : ℂ)).re

theorem deriv_log_Gamma_eq_realDigamma
    {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) x =
      realDigamma x

theorem monotoneOn_realDigamma :
    MonotoneOn realDigamma (Set.Ioi 0)

theorem realDigamma_add_one
    {x : ℝ} (hx : 0 < x) :
    realDigamma (x + 1) = realDigamma x + x⁻¹

theorem abs_realDigamma_nat_shift_sub_le
    (N : ℕ) (hN : 1 ≤ N)
    {x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    |realDigamma ((N : ℝ) + 1 + x) -
       realDigamma ((N : ℝ) + 1)| ≤
      1 / (N : ℝ)
```

The last proof uses the **two separate endpoint differences**, not the width of the entire interval:
\[
-\frac1N
\le \psi(N+1+x)-\psi(N+1)
\le \frac1{N+1}.
\]
Merely bounding by \(\psi(N+2)-\psi(N)\) would give the weaker sum of two reciprocals.

**Bridge hazards:**

- Prove differentiability of `log ∘ Real.Gamma` on `Ioi 0` using Gamma positivity and differentiability; convexity alone is insufficient for `monotoneOn_deriv`.
- For the derivative identification, restrict the **complex Gamma derivative** to the real axis, use `Complex.Gamma_ofReal`, and then divide by the positive real Gamma value. Do not rely on simplifying `deriv` across the embedding automatically.
- `digamma` and `logDeriv` are totalized definitions. Keep all mathematical derivative and recurrence arguments on positive real points or a pole-free complex neighborhood.
- Discharge the recurrence’s `∀ m, s ≠ -m` hypothesis from positivity of the real part.

**Day one:** this module is plausibly day-sized; the principal uncertainty is the derivative bridge.

**Acceptance test:** all four declarations above compile with no new analytic assumptions. A useful final corollary is:

```lean
theorem tendsto_realDigamma_nat_shift_sub
    {x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        realDigamma ((N : ℝ) + 1 + x) -
          realDigamma ((N : ℝ) + 1))
      Filter.atTop (nhds 0)
```

Do **not** make complex series machinery part of day-one acceptance.

### Module 2: telescope to a real `HasSum`

```lean
theorem hasSum_realDigamma_sub
    {x : ℝ} (hx₀ : -1 < x) (hx₁ : x ≤ 1) :
    HasSum
      (fun n : ℕ =>
        x / (((n : ℝ) + 1) * ((n : ℝ) + 1 + x)))
      (realDigamma (1 + x) - realDigamma 1)
```

Expose a finite-sum telescoping identity internally. Its clean orientation is
\[
\sum_{n<N}\frac{x}{(n+1)(n+1+x)}
=\psi(1+x)-\psi(1)
 -\bigl(\psi(N+1+x)-\psi(N+1)\bigr).
\]

Then use the decay theorem and the standard equivalence between `HasSum` and convergence of natural partial sums. **There is no need to prove summability separately first.**

### Module 3: the holomorphic series and identity theorem

```lean
noncomputable def digammaSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ,
    z / (((n : ℂ) + 1) * ((n : ℂ) + 1 + z))

theorem analyticOnNhd_digammaSeries :
    AnalyticOnNhd ℂ digammaSeries
      (Metric.ball (0 : ℂ) (1 / 2 : ℝ))

theorem digammaSeries_eq_digamma_sub
    {z : ℂ} (hz : ‖z‖ < (1 / 2 : ℝ)) :
    digammaSeries z =
      Complex.digamma (1 + z) - Complex.digamma 1
```

For \(\|z\|<1/2\), writing \(k=n+1\),
\[
|k+z|\ge k/2,\qquad
\left|\frac{z}{k(k+z)}\right|\le \frac1{k^2}.
\]
That is a single summable majorant on the entire chosen ball.

Two important details:

- Establish analyticity of digamma there from `Gamma' / Gamma`, Gamma analyticity, and Gamma nonvanishing. **Meromorphicity alone is not analyticity.**
- The real `HasSum` initially identifies real parts. To obtain equality in \(\mathbb C\) on the real segment, also use that digamma is real at positive real arguments—the same Gamma restriction argument used in Module 1.

For the identity theorem, use the preconnected ball and real points accumulating at zero, for example \(z_m=1/(m+3)\). The exact punctured-neighborhood formulation of “frequently equal” needs a small adapter; one equality at zero is not enough.

### Module 4: coefficients, then zeta

For \(j\ge1\),
\[
\left(\frac{d}{dz}\right)^j
 \frac{z}{k(k+z)}
 =
 \frac{(-1)^{j+1}j!}{(k+z)^{j+1}},
\]
with uniform bound
\[
\frac{j!\,2^{j+1}}{k^{j+1}}
\]
on the same ball. Every exponent here is at least \(2\).

**Keep order zero separate:** it has cancellation and a \(k^{-2}\) bound. Splitting the original series into \(\sum 1/k-\sum1/(k+z)\) would destroy convergence.

Inductively apply `hasSum_deriv_of_summable_norm`, retaining derivative identities throughout the ball. At zero divide by \(j!\), use the local digamma identity, and read `psiOneCoeff` with the existing Taylor toolkit.

The most useful exported coefficient theorem is directly:

```lean
theorem hasSum_psiOneCoeff
    (j : ℕ) (hj : 1 ≤ j) :
    HasSum
      (fun n : ℕ =>
        (-1 : ℂ) ^ (j + 1) /
          ((n : ℂ) + 1) ^ (j + 1))
      (psiOneCoeff j)
```

Then:

```lean
theorem psiOneCoeff_eq_zeta
    (j : ℕ) (hj : 1 ≤ j) :
    psiOneCoeff j =
      (-1 : ℂ) ^ (j + 1) *
        riemannZeta ((j : ℂ) + 1)

theorem hasSum_neg_psiOneCoeff_two :
    HasSum
      (fun n : ℕ => (((n : ℂ) + 1) ^ 3)⁻¹)
      (-psiOneCoeff 2)

theorem psiOneCoeff_two_eq :
    psiOneCoeff 2 = -riemannZeta (3 : ℂ)
```

The final adapter is `cpow` at a natural exponent versus ordinary `pow`, plus
\(1<\operatorname{re}(j+1)\). This is algebraic bookkeeping, not another analytic step.

**Scheduling:** Modules 1 and 2 are credible individual day-sized targets. Modules 3 and 4 should remain separate tasks; neither should be promised first-try. If only \(\psi_2\) is urgently needed, specialize Module 4 to two differentiations before generalizing.

## 3. After the bridge

**Yes: publish the depth-\(\le5\) zeta-valued forms as a short closure/regression module.** They are the reader-facing payoff; users should not need to unfold Gamma jets and recurrences.

In particular:

- state the displayed \(D_4\) formula in the repository’s exact convention for \(b\);
- state the existing depth-five \(E_5\) formula with \(\psi_2\) replaced by \(-\zeta(3)\), and even zeta values reduced to \(\pi^2,\pi^4\);
- derive these from the already-proved symbolic formulas, rather than re-proving their asymptotics;
- provide real-valued versions using `.re` of zeta if the existing coefficients are real, or package zeta reality once from its convergent series.

One qualification: **the normalized coefficient polynomials** lie in the indicated ring. Coefficients such as \(D_4\) still carry the external factor \((2\pi)^{-3/2}\); they are not literally polynomials in \(\pi^2\).

For arbitrary depth, eliminating *all* even zeta values also needs a general even-zeta evaluation theorem; the scouted `hasSum_zeta_two/four` suffice only for the relevant low depths.

**No new §2 analytic target is apparent from this brief** if the all-depth expansions and remainder assertions are already formalized. The remaining work would then be exact constants and presentation. I would not declare §2 completely closed without checking `examples_slop.tex` itself for any additional uniformity, remainder, or parameter-range claim.