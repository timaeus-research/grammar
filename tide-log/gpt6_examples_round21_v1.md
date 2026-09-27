## 1. Fidelity

**Consistent with the supplied statements; this is not an independent audit of the pinned files.**

- **Canonicality:** the degree-zero case reduces to a constant polynomial, whose value is zero by uniqueness of limits. For positive degree, `Polynomial.abs_tendsto_atTop` contradicts `|P(x)| → 0`. Ensure the degree-zero branch includes the zero polynomial; `natDegree = 0` does not imply nonzero.
- **Coefficient recursion:** correct. Hasse differentiation gives
  \[
  [X^{k+1}]H_jP=\binom{k+1+j}{j}P_{k+1+j},
  \]
  and the multiplier is exactly \(2^jJ_j\), with **no additional \(j!\)**.
- **Subleading recursions:** both are correct:
  \[
  B_{L+1}=\frac{B_L}{s(L-1)}+\frac{2R_0A_L}{s},
  \]
  \[
  C_{L+1}=\frac{C_L}{s(L-2)}
    +\frac2s\bigl(R_0B_L+2(L-1)JA_L\bigr).
  \]
  Their ranges are respectively \(L\ge2\), \(L\ge3\). The second Hasse contribution uses \(\binom{L-1}{1}=L-1\). These agree with the displayed closed forms. I cannot independently check the DCXXXVI cross-reference.

The important qualification remains: **the coefficient recursion is complete, but the closed-form evaluation of its moment and residual-mass inputs is not.**

## 2. The all-\(k\) moment bridge

**Recommended next target. The proposed formula is correct.** Write \(a=\log2\). Substitution gives
\[
J_k=2^{-(k+1)}
 \int_0^\infty
 (e^{-u}-\mathbf1_{u\le1/2})\frac{(\log u+a)^k}{u}\,du.
\]
Changing the cutoff to \(1\) adds
\[
\int_{1/2}^1\frac{(\log u+a)^k}{u}\,du
=\frac{a^{k+1}}{k+1}.
\]
Thus precisely
\[
J_k=\frac1{2^{k+1}}\left[
 \sum_{r=0}^k\binom kr a^{k-r}\frac{G(r+1)}{r+1}
 +\frac{a^{k+1}}{k+1}\right].
\]

### (i) IBP versus Fubini

**Use split IBP as the primary route.** Set
\[
F_-(u)=\frac{(e^{-u}-1)(\log u)^{r+1}}{r+1},
\qquad
F_+(u)=\frac{e^{-u}(\log u)^{r+1}}{r+1}.
\]
On their respective intervals,
\[
F_\pm'(u)
=(e^{-u}-\mathbf1_{u\le1})\frac{(\log u)^r}{u}
-\frac{e^{-u}(\log u)^{r+1}}{r+1}.
\]
All endpoint terms vanish, including for \(r=0\).

The improper-integral FTC lemmas you propose are the right *shape*. I would isolate the endpoint and integrability certificates first, then adapt to their exact pinned signatures. A finite-interval proof followed by endpoint limits is a reasonable fallback.

**Correction to the proposed Fubini identity:** it must be anchored:
\[
\frac{(\log u)^{r+1}}{r+1}
=\int_1^u\frac{(\log v)^r}{v}\,dv
\]
as an oriented interval integral. An unanchored integral over \(0<v\le u\) diverges. The split Fubini proof is valid, but adds absolute-integrability bookkeeping and signs below \(1\).

### (ii) Integrability and Gamma derivatives

Your certificates are appropriate:

- Near zero, dominate \(|\log u|^m\) by the existing \((1+|\log u|)^m\) certificate.
- For the renormalised integrand, use \(|e^{-u}-1|\le u\).
- At infinity, absorb any fixed logarithmic power into an exponential envelope.
- Package \(u|\log u|^m\to0\) and \(e^{-u}|\log u|^m\to0\) once.

**Do not make `G r = iteratedDeriv r Real.Gamma 1` a dependency of this bridge.** First-derivative Gamma-integral APIs do not automatically supply arbitrary differentiated integral identities: one still needs uniform domination in a neighbourhood of the parameter.

I cannot establish from the supplied material whether DCXXXVIII exposes the integral identity for \(G2\). `deriv_deriv_Gamma_one` alone is only a derivative value. But there is a cheap workaround:

1. Prove the general IBP bridge.
2. Specialise it to \(r=1\).
3. Compare with the existing `integral_renormalised_exp_log`.

This yields \(G2=\Gamma''(1)\) without another differentiation-under-the-integral proof. Similarly, the \(k=0\) bridge and the existing value of \(J_0\) can recover \(G1=-\gamma\), though that makes the subsequent \(J_0\) check a consistency check rather than an independent derivation.

The checks are
\[
J_0=\frac{a-\gamma}{2}=R_0,\qquad
J_1=\frac{(a-\gamma)^2+\pi^2/6}{8}
=\frac{R_0^2}{2}+\frac{\pi^2}{48}.
\]

### (iii) Effort

Conditional planning estimates, not repository-audited commitments:

| Deliverable | Focused person-days |
|---|---:|
| General IBP identity and integrability API | 2–4 |
| Substitution, cutoff shift, finite-sum bridge | 1–3 |
| Only \(k=2,3\), reusing existing substitution machinery | 2–4 total |

**Prefer all \(k\):** most difficulty is analytic infrastructure, not induction on the exponent. These estimates exclude evaluating \(G3,G4\) in ζ-values and exclude arbitrary Gamma-derivative identification.

## 3. Alternatives and priority

My ranking is **bridge → \(Q_3/D_4\) → NB surrogate ratio → cone \(c_3\) → general Mellin asymptotics**. The middle two are provisional without their precise current interfaces.

### \(Q_3\) and \(D_4\): the next focused payoff

Your expression
\[
D_4=\frac2s(4A_3J_2+2B_3J+C_3R_0+Q_3)
\]
is correct. **The bridge alone does not close it.**

Finite-part extraction can close \(Q_3\) **without** proving a general contour-shift asymptotic. The clean model interface is: if
\[
q_L(v)=Z_L(v^2)-\mathbf1_{v\ge1}\frac{P_L(2\log v)}v,
\qquad
M_L(z)=\int_0^\infty Z_L(v^2)v^{z-1}\,dv,
\]
then, writing \(a_k=[X^k]P_L\),
\[
Q_L=\lim_{z\to1^-}
\left(M_L(z)-\sum_k\frac{2^k k!\,a_k}{(1-z)^{k+1}}\right).
\]

This formula requires verification against the **actual cutoff and residual normalisation**; a different definition introduces explicit correction terms. Also, if DCVI uses Mellin variable \(t\) for \(N\), then
\[
M_L(z)=\tfrac12\,\mathcal M_N[Z_L](z/2).
\]
Do not identify poles at \(t=\tfrac12\) and \(z=1\) without this conversion.

For this residual model, the limit follows by dominated convergence: the integrable residual controls the tail, while a small-\(v\) weighted certificate controls the origin. The Gamma product then computes the finite part.

At depth three, a third-order regularised Gamma jet is the expected ζ(3) input. **One day is plausible only if that jet and the residual-limit template already exist.** Otherwise budget roughly **3–7 days** after the bridge; more if Gamma-jet infrastructure must be built.

### General Mellin-jet asymptotics

This is **not a routine extension of canonicality**. It needs inversion, vertical-line estimates, contour shifting, horizontal-edge control and a remainder estimate at every depth. Canonicality makes the *last step* short, not the analytic argument.

Absent an existing contour-shift framework: **several weeks, plausibly 4–10+**, rather than days. A depth-recursive real-variable route exploiting the existing rate engine may be cheaper; investigate that before committing to contours.

### NB and cone

- **NB surrogate posterior ratio:** attractive if numerator and denominator expansions already exist. Package denominator eventual nonvanishing and quotient remainder control. Keep the surrogate/exact-posterior distinction explicit.
- **Cone \(c_3\):** a useful independent milestone, but lower leverage for completing the Gaussian coefficient story.

## Proposed Lean-facing interface

These are **proposed signatures, not checked code**:

```lean
noncomputable def gammaOneLogMoment (r : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * Real.log u ^ r

theorem integrableOn_gammaOneLogMoment (r : ℕ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-u) * Real.log u ^ r)
      (Set.Ioi 0)

theorem integral_renormalised_exp_log_pow (r : ℕ) :
    (∫ u in Set.Ioi (0 : ℝ),
      (Real.exp (-u) - (if u ≤ 1 then 1 else 0)) *
        Real.log u ^ r / u) =
      gammaOneLogMoment (r + 1) / (r + 1 : ℝ)

theorem gaussJlogPow_eq_gammaOneLogMoment (k : ℕ) :
    gaussJlogPow k =
      (1 / (2 : ℝ) ^ (k + 1)) *
        ((∑ r ∈ Finset.range (k + 1),
          (k.choose r : ℝ) * Real.log 2 ^ (k - r) *
            (gammaOneLogMoment (r + 1) / (r + 1 : ℝ))) +
          Real.log 2 ^ (k + 1) / (k + 1 : ℝ))
```

Also expose integrability of the renormalised integrand. **Round-21 acceptance criterion:** all-\(k\) bridge, \(G1/G2\), regression checks against the existing \(J_0/J_1\), and explicit \(J_2/J_3\) expressions in \(G3/G4\)—with ζ-evaluations and \(Q_3\) clearly separate.