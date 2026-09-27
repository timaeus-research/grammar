## 1. Fidelity

**All three checks pass**, at the mathematical/interface level; I have not independently compiled the supplied statements.

- **(a)** The shifted duplication identity gives exactly
  \[
  \sum_{k=0}^n e_k g_{n-k}
  =\sum_{k=0}^n\frac{(-2\ell)^k}{k!}\,2^{n-k}g_{n-k}.
  \]
  The sign, scaling, and division by \(\sqrt\pi\) are correct.
- **(b)** `gammaOneCoeff_three = gammaThirdOne / 6` is the correct bridge: `iteratedDeriv_eq_iterate` identifies the numerator, and \(3!=6\).
- **(c)** Write \(p=\gamma+2\ell\) and
  \(\lambda_3=\Gamma'''(1)+\gamma^3+\gamma\pi^2/2\). Your formula is
  \[
  e_3=\frac{7\lambda_3-p^3-\frac32p\pi^2}{6},
  \]
  exactly the third exponential coefficient of the normalized half-point jet.

**DCLXXVI closes the duplication target. No further Leibniz infrastructure is needed.**

## 2. Ranking: digamma jets first

Yes: **package the remaining closure in digamma jets**, not in unrelated `q` symbols. Keep `q` as the derived interface for each depth.

My next-day ranking:

1. **Digamma one-point recurrence + duplication:** (α), (γ).
2. **General depth logarithmic derivative + recurrence:** (β).
3. **Depth five regression**, using that recurrence.
4. **Scout/prove the ζ-bridge.**
5. Cone/NB/blow-up only with a sharply specified missing identity.

Splitting 1 and 2 provides useful stopping points if derivative bookkeeping consumes the day.

### Proposed Lean interfaces

These are proposed signatures, not claims about existing names. Use complex subtraction for `D − 1`. Until the actual `depthJet` definition is checked at `D = 0`, retain `hD : 1 ≤ D`.

```lean
noncomputable def gammaLogDeriv (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

noncomputable def psiOneCoeff (j : ℕ) : ℂ :=
  taylorCoeff gammaLogDeriv 1 j

noncomputable def psiHalfCoeff (j : ℕ) : ℂ :=
  taylorCoeff gammaLogDeriv (1 / 2) j
```

Your shift lemma identifies these with coefficients of the requested translated functions. Avoid creating another jet abstraction.

One reusable helper, unless already present:

```lean
theorem taylorCoeff_deriv (f : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    taylorCoeff (deriv f) z n =
      (n + 1 : ℂ) * taylorCoeff f z (n + 1)
```

This is factorial arithmetic plus iteration of `deriv`; it needs no analyticity hypothesis. Analyticity enters the **product** and local differential identities.

### (α) The one-point recurrence

```lean
theorem psiOneCoeff_zero :
    psiOneCoeff 0 = -(Real.eulerMascheroniConstant : ℂ)

theorem gammaOneCoeff_succ_mul (n : ℕ) :
    (n + 1 : ℂ) * gammaOneCoeff (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        psiOneCoeff j * gammaOneCoeff (n - j)
```

Proof: near \(1\), Gamma is analytic and nonzero, so
\[
\Gamma'=(\Gamma'/\Gamma)\Gamma.
\]
Apply local Taylor congruence, `taylorCoeff_mul`, and `taylorCoeff_deriv`.

Also expose the rewrite-oriented version with division by `(n + 1 : ℂ)` if downstream proofs prefer it.

### (γ) Digamma duplication

**Differentiate the product identity; do not introduce complex `log`.** The correct analytic statement is local:

```lean
theorem gammaLogDeriv_duplication_eventually :
    ∀ᶠ z : ℂ in nhds 0,
      gammaLogDeriv (1 / 2 + z) + gammaLogDeriv (1 + z) =
        2 * gammaLogDeriv (1 + 2 * z) -
          2 * (Real.log 2 : ℂ)
```

Then the all-orders interface is:

```lean
theorem psiHalfCoeff_eq (j : ℕ) :
    psiHalfCoeff j =
      ((2 : ℂ) ^ (j + 1) - 1) * psiOneCoeff j -
        (if j = 0 then 2 * (Real.log 2 : ℂ) else 0)
```

Your proposed formula is correct. The extra factor \(2\) comes from differentiating the doubled argument; scaling the resulting digamma jet contributes \(2^j\).

**Proof organization:**

1. Establish eventual analyticity/nonvanishing of the three Gamma factors.
2. Differentiate `duplication_shifted` locally using `HasDerivAt` rules.
3. Use the original identity to cancel the common product.
4. Transfer the eventual equality to Taylor coefficients.

Do not attempt a global digamma duplication theorem with no pole exclusions.

### (β) Depth recurrence

Define the coefficient of the logarithmic derivative directly:

```lean
noncomputable def depthLogDerivCoeff (D j : ℕ) : ℂ :=
  (if j = 0 then
      ((D : ℂ) - 1) * (Real.log 2 : ℂ)
    else 0) -
    (-1 : ℂ) ^ j * psiHalfCoeff j +
    (D : ℂ) * psiOneCoeff j
```

The requested logarithmic-derivative interface:

```lean
theorem depthJet_logDeriv_eventually
    (D : ℕ) (hD : 1 ≤ D) :
    ∀ᶠ z : ℂ in nhds 0,
      deriv (depthJet D) z / depthJet D z =
        ((D : ℂ) - 1) * (Real.log 2 : ℂ) -
          gammaLogDeriv (1 / 2 - z) +
          (D : ℂ) * gammaLogDeriv (1 + z)
```

But make the **multiplicative differential equation** the working theorem:

```lean
theorem depthJet_deriv_eventually
    (D : ℕ) (hD : 1 ≤ D) :
    ∀ᶠ z : ℂ in nhds 0,
      deriv (depthJet D) z =
        (((D : ℂ) - 1) * (Real.log 2 : ℂ) -
            gammaLogDeriv (1 / 2 - z) +
            (D : ℂ) * gammaLogDeriv (1 + z)) *
          depthJet D z
```

Then:

```lean
theorem depthJetCoeff_succ_mul
    (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    (n + 1 : ℂ) * depthJetCoeff D (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        depthLogDerivCoeff D j * depthJetCoeff D (n - j)
```

And the one-point reduction:

```lean
theorem depthLogDerivCoeff_eq_one (D j : ℕ) :
    depthLogDerivCoeff D j =
      ((D : ℂ) -
          (-1 : ℂ) ^ j * ((2 : ℂ) ^ (j + 1) - 1)) *
        psiOneCoeff j +
      (if j = 0 then
          ((D : ℂ) + 1) * (Real.log 2 : ℂ)
        else 0)
```

In particular,
\[
q_{D,0}=(D+1)\ell-(D-1)\gamma.
\]

**Implementation preference:** explicit local `HasDerivAt` product/power/chain rules, following `hasDerivAt_cubicH`. They expose the minus sign and the factor \(D\) cleanly. Derive the quotient theorem afterward. `AnalyticAt` remains useful for regularity and the Cauchy products; it need not carry the derivative calculation itself.

## 3. Depth five: one important qualification

Let \(a=6\ell-4\gamma\). The formal cumulant coefficients are
\[
\log H_5(z)
 =az+\frac{2\pi^2}{3}z^2-\frac{\lambda_3}{3}z^3
   +\frac{5\lambda_4}{6}z^4+O(z^5).
\]
This is a mathematical description; the Lean proof need not define a logarithm.

Therefore
\[
h_{5,3}=\frac{a^3}{6}+\frac{2\pi^2a}{3}-\frac{\lambda_3}{3},
\]
so **your \(D_5\) is correct**.

Before evaluating \(\lambda_4\), the fourth coefficient is
\[
\boxed{
h_{5,4}
=\frac{a^4}{24}+\frac{\pi^2a^2}{3}
-\frac{a\lambda_3}{3}
+\frac{5\lambda_4}{6}+\frac{2\pi^4}{9}.
}
\]

Using \(\lambda_4=\pi^4/15\), its last two terms become \(25\lambda_4/6\). Thus **your \(E_5\) is correct after that evaluation**, but it is not the appropriate pre-ζ-bridge regression. Do not silently absorb the \(\pi^4\) term into an unevaluated \(\lambda_4\).

For a stronger acceptance test, the same recurrence gives
\[
\begin{aligned}
h_{5,5}={}&\frac{a^5}{120}+\frac{\pi^2a^3}{9}
-\frac{a^2\lambda_3}{6}\\
&+a\left(\frac{5\lambda_4}{6}+\frac{2\pi^4}{9}\right)
-\frac{2\pi^2\lambda_3}{9}-\frac{13\lambda_5}{60}.
\end{aligned}
\]
Then \(Q_5=h_{5,5}/(2s^4)\). This genuinely introduces the next one-point datum.

**Use the general recurrence for the formal proof.** Direct Cauchy expansion is a useful independent check, but is now the less valuable implementation route.

## 4. Boundary and convention hazards

- **Lean division is total.** `gammaLogDeriv` is not undefined when Gamma vanishes; it has a totalized value. Analytic logarithmic-derivative reasoning still requires local nonvanishing.
- **Reflection sign:** the coefficient of \(-\psi(\tfrac12-z)\) is
  \(-(-1)^j\psiHalfCoeff\,j\), exactly as above.
- **Factorial indexing:**
  \[
  \psiOneCoeff(j)=\frac{\psi^{(j)}(1)}{j!}
  =\frac{\lambda_{j+1}}{j!}.
  \]
  In particular, \(\lambda_3=2\,\psiOneCoeff(2)\) and
  \(\lambda_4=6\,\psiOneCoeff(3)\).
- **ζ-boundary:** for \(j\ge1\),
  \[
  \psiOneCoeff(j)=(-1)^{j+1}\zeta(j+1),
  \qquad \psiOneCoeff(0)=-\gamma.
  \]
  No factorial remains in this normalized formula.
- Keep the jet algebra in `ℂ`; cast real evaluations once at the interface. Rewrite `Complex.log 2` to the real cast before coefficient normalization.
- Check `D = 0` separately: `(D - 1 : ℕ)` and `((D : ℂ) - 1)` are different conventions.

For NB ratios, a reusable **quotient-jet recurrence** is a plausible day-sized target:
\[
v_0w_{n+1}
=u_{n+1}-\sum_{k=0}^{n}w_kv_{n+1-k},
\qquad W=U/V,\quad v_0\ne0.
\]
It reuses the same Cauchy machinery. Without the actual cone/blow-up interfaces, I would not rank either above completing the digamma reduction and depth-five regression.