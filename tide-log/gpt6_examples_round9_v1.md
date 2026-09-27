## 1. Fidelity check

**On the supplied statements, all four targets match their intended scope.** Two qualifications belong in the note: DCXXI evaluates the amplitude constant, not yet the whole monomial family partition function; DCXXII identifies the invariant tilt under the supplied orthogonal-frame hypotheses, not yet the Morse–Bott asymptotic.

- **DCXXIV:** the error
  \[
  C_m(1+\log N)^m/\sqrt N
  \]
  is correct at depth \(m+2\). The `1 +` is necessary for this **all-\(N\ge1\)** formulation: for \(m>0\), replacing it by \((\log N)^m\) would force zero error at \(N=1\). Eventually, say \(N\ge e\), it can be absorbed into \(2^m(\log N)^m\).
  
  The recursion for \(C'\) is sensible and deliberately generous: inner-region budget \(1\), twice the middle-region budget, and twice the tail budget. Its rapid growth is harmless for **fixed-depth** asymptotics; it provides no useful uniform-in-depth claim.

- **DCXXIII:** the coefficient identification is exact:
  \[
  c=3\log2-\gamma,\qquad R_0=(\log2-\gamma)/2,\qquad
  c/2+R_0=2\log2-\gamma.
  \]
  After the evenness factor and \(1/(2\pi\sqrt N)\), this gives the stated coefficient \((2\log2-\gamma)/\pi\). The constant \(12\) is safe; indeed the displayed final budgets add to \(6/\sqrt N\). I would not spend a target tightening it.

- **Interface:** keep `LeadingData` unchanged. It is a useful minimal propagation contract. Add a separate `TwoTermData`; requiring second-order information would unnecessarily restrict existing leading-order clients.

## 2. Recommended next three targets

My value-per-effort ranking is:

| Rank | Target | Scope |
|---|---|---|
| 1 | Monomial family, including Gaussian scaling | Strong day-sized target |
| 2 | Two-term propagation and all-depth second coefficient | Focused but ambitious day; split helper moments from propagation if needed |
| 3 | Integral-defined \(K_0\) and the depth-two identity | Credible day-sized fallback; lower asymptotic value |
| Stretch | Depth-three constant | Not confidently day-sized without second Gamma-derivative infrastructure |

The naive Bayes face and cone average cannot be responsibly estimated before seeing the promised density/integrand.

### Target 1: the monomial family, with a genuinely vanishing remainder

First fix normalization. The coefficient in the question corresponds to the **unnormalized Gaussian weight**
\[
Z_k(N)=\int_{\mathbb R^2}
 e^{-N(x^{2k}+x^2y^2)/2}e^{-(x^2+y^2)/2}\,dx\,dy.
\]
For normalized two-dimensional Gaussian prior, divide everything by \(2\pi\).

Set
\[
m=N^{1/(2k)},\qquad \delta=m^{-2},\qquad
\varepsilon=m^{2-2k}.
\]
Integrating out \(y\), then putting \(x=u/m\), gives
\[
Z_k(N)=\sqrt{2\pi}N^{-1/2}
 \int_{\mathbb R}
 \frac{e^{-u^{2k}/2}e^{-\delta u^2/2}}{\sqrt{u^2+\varepsilon}}\,du.
\]

**Recommended remainder:**
\[
\boxed{
Z_k(N)=\sqrt{2\pi}N^{-1/2}
 \left[\frac{k-1}{k}\log N+2\log2+\frac{\log2-\gamma}{k}\right]
 +O_k(N^{-1/2-1/k}).
}
\]

This stronger, log-free remainder has a short route for \(k\ge2\):

1. Removing the extra \(x\)-Gaussian costs \(O_k(\delta)\), uniformly in \(\varepsilon\):
   \[
   1-e^{-\delta u^2/2}\le\delta u^2/2,\qquad
   \frac{u^2}{\sqrt{u^2+\varepsilon}}\le u\quad(u>0).
   \]
2. For the fixed monomial amplitude, use
   \[
   \left|\frac1{\sqrt{u^2+\varepsilon}}-\frac1u\right|
   \le\frac{\varepsilon}{2u^3}.
   \]
   The required weighted renormalized integral is finite because
   \[
   e^{-u^{2k}/2}-1=O(u^{2k}),\qquad 2k-3\ge1.
   \]
   Together with the exact indicator-piece integral, this yields an \(O_k(\varepsilon)\) kernel error.
3. For \(m\ge1,\ k\ge2\), \(\varepsilon\le\delta\).

Thus one need not separately control \(R_{a_m}-R_\infty\), although the same \(O(m^{-2})\) estimate follows.

**Proposed Lean interface**—names below are new:
```lean
noncomputable def monomialFamilyZ (k : ℕ) (N : ℝ) : ℝ := ...

noncomputable def monomialFamilyMain (k : ℕ) (N : ℝ) : ℝ := ...

theorem monomialFamily_two_term_bound {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      |monomialFamilyZ k N - monomialFamilyMain k N| ≤
        C / (Real.sqrt N * N ^ (1 / (k : ℝ)))
```

Prove the bound first at `N = m ^ (2 * k)` with `1 ≤ m`; transport to arbitrary \(N\) afterward.

**Fallback:** if only the generic quadratic amplitude estimate is reused, an honest bound is
\[
O_k\!\left(N^{-1/2}
 [N^{-1/k}+N^{-(k-1)/k}(1+\log N)]\right).
\]
Do not mistake that generic-engine loss for an intrinsic logarithm.

### Target 2: two-term propagation

Write \(s=\sqrt{2\pi}\), and suppose \(n\ge2\):
\[
f(t)=\frac{A(\log t)^n+B(\log t)^{n-1}}{\sqrt t}
 +O\!\left(\frac{(1+\log t)^{n-2}}{\sqrt t}\right).
\]
Then the Gaussian step has
\[
\boxed{
A'=\frac{A}{(n+1)s},\qquad
B'=\frac1s\left(\frac Bn+2AR_0\right).
}
\]

The two contributions to \(B'\) are:

- integrating the \(B\)-term against the flat cutoff: \(B/(ns)\);
- restoring the Gaussian instead of the cutoff: \(2AR_0/s\).

**Crucial implementation point:** the existing tail estimate discards information of precisely the order needed for \(B'\). Replace “bound the tail” with “retain the \(h=\texttt{gaussH}\) contribution across the whole positive half-line.”

Suggested indexing avoids truncated natural subtraction:
```lean
-- Degree m+2, second degree m+1, error degree m.
structure TwoTermData (f : ℝ → ℝ) (A B C : ℝ) (m : ℕ) : Prop where
  A_nonneg : 0 ≤ A
  C_nonneg : 0 ≤ C
  f_nonneg : ∀ t, 0 ≤ t → 0 ≤ f t
  f_le_one : ∀ t, 0 ≤ t → f t ≤ 1
  bound : ∀ t, 1 ≤ t →
    |f t -
      (A * (Real.log t) ^ (m + 2) +
       B * (Real.log t) ^ (m + 1)) / Real.sqrt t| ≤
      C * (1 + Real.log t) ^ m / Real.sqrt t
```

Do **not** require \(B\ge0\). Use \(|B|\) in error budgets.

The propagation interface should return:
```lean
∃ C', 0 ≤ C' ∧
  TwoTermData gaussianStep
    (A / ((m + 3) * s))
    ((B / (m + 2) + 2 * A * R₀) / s)
    C' (m + 1)
```
with the recursion integrability hypothesis supplied explicitly.

The reusable helper is finiteness of
\[
\int_0^\infty |h(x)|\,|\log x|^j\,\frac{dx}{x}
\]
for every natural \(j\). Exact values beyond \(j=0\) are unnecessary for this target.

Starting from DCXXIII gives, for \(L\ge3\),
\[
A_L=\frac1{(L-1)!\,s^{L-1}},\qquad
\boxed{
B_L=\frac{(L+1)\log2-(L-1)\gamma}
 {(L-2)!\,s^{L-1}}.
}
\]
Equivalently,
\[
\frac{B_L}{A_L}
=(L-1)\big((L+1)\log2-(L-1)\gamma\big).
\]
This is the subleading coefficient predicted by the note’s polynomials, under the stated \(Z_L\) normalization. At \(L=3\), it reproduces DCXXIII.

Use depth three as the induction base. Applying this generic interface directly at depth two would introduce a spurious negative logarithmic error exponent.

### Target 3: a modest, self-contained Bessel identity

Define only the function actually needed:
```lean
noncomputable def besselK0Integral (z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-z * Real.cosh t)

theorem integrableOn_besselK0Integral {z : ℝ} (hz : 0 < z) : ...

theorem gaussLaplace2_eq_besselK0Integral {N : ℝ} (hN : 0 < N) :
    gaussLaplace2 N =
      Real.exp (1 / (4 * N)) *
        besselK0Integral (1 / (4 * N)) /
          Real.sqrt (2 * Real.pi * N)
```

Route: integrate out one Gaussian, use evenness, substitute
\(x=\sinh t/\sqrt N\), use
\(\sinh^2t=(\cosh(2t)-1)/2\), then rescale \(2t\).

This is worth a day as an exact note-to-Lean bridge. It is **not** worth starting a general Bessel API. State explicitly that this is the standard integral representation for positive argument; no ODE or analytic-continuation theory is being claimed.

## 3. Depth-three constant: the missing ingredients

Let \(d=\log2-\gamma\). The logarithmic moment is
\[
\boxed{
J=\int_0^\infty h(x)\frac{\log x}{x}\,dx
=\frac{d^2}{8}+\frac{\pi^2}{48}.
}
\]
Indeed, the renormalized Mellin transform is
\[
2^{z/2-1}\Gamma(z/2)-\frac1z,
\]
and \(J\) is its derivative at zero. This involves second-order Gamma data, not merely the existing Gamma values.

**But evaluating \(J\) is not sufficient.** The scaled inner region and the integrated depth-two remainder have nonzero limiting contributions.

A clean combined object is
\[
q(v)=Z_2(v^2)-
  1_{(1,\infty)}(v)\frac{2\log v+c}{s}.
\]
`gaussLaplace2_bounds` should readily prove \(q\in L^1(0,\infty)\). Dominated convergence then reduces the desired constant to
\[
\frac{cR_0+2J}{\pi}+\frac2s\int_0^\infty q(v)\,dv.
\]
The additional exact evaluation required is
\[
\boxed{
\int_0^\infty q(v)\,dv
=\frac{c^2+5\pi^2/6}{4s}.
}
\]
Together these give
\[
\frac{(4\log2-2\gamma)^2+\pi^2}{4\pi}.
\]

The cutoff term \((\log N+c)I_a\) tends to zero. The Gaussian tail contributes through \(R_0,J\); the inner piece and induction error are captured together by \(q\).

**Honest day-sized intermediate:** prove integrability of \(q\) and the residual limit expressed using \(J\) and \(\int q\). The explicit constant needs the two exact moment evaluations—potentially more than a day.

## 4. Convention checklist

- **`LeadingData`:** bounds on \(f\) apply for \(t\ge0\); asymptotic control starts at \(t\ge1\). It supplies no measurability or integrability—retain the separate `hint`.
- **Depth indexing:** current `m` means \(L=m+2\), leading degree \(m+1\), error degree \(m\). In the proposed `TwoTermData`, `m` means leading degree \(m+2\); document this explicitly.
- **`ampRenorm`:** its factor \(2/u\) already includes the evenness factor. Hence `ampRenorm (monoAmp 1) = 2 * R₀`, not \(R_0\).
- **Constants `12` and `18`:** distinguish a pointwise bound with `1 ≤ N` from an eventual Big-O statement. No `18` theorem appears in the supplied signatures, so I would not identify its scope from this packet.
- **`tanProj x y B`:** \(x\) determines the left/row-space projection; \(y\) the right/column-space projection. The norm is Frobenius, not operator norm. The tangent interpretation needs both vectors nonzero.
- **Frames:** DCXXII proves the invariant expression under supplied orthogonal frames. It does not itself construct frames for arbitrary nonzero vectors.
- **Family normalization:** record raw versus normalized Gaussian measure in the definition; otherwise the entire family expansion can silently acquire a factor \(2\pi\).