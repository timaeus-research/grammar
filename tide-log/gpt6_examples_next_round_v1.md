## 1. Fidelity check

**Yes, with three qualifications the note should state explicitly.**

- **Tie formula:** your convention is the principal part in powers of **\(s-\mu\)**:
  \[
  C_{\mu,2}=(\texttt{chartPolarCoeff}\;\cdots\;1),\qquad
  C_{\mu,1}=(\texttt{chartPolarCoeff}\;\cdots\;0).
  \]
  Thus \(C_{1/2,2}=c_{00}/8\), and the simple coefficients are **negative**. The factors \(1/2\) and \(1/4\) come from \(2k_1\) and \(2k_0\), respectively. Writing poles using \(\mu-s\) would reverse the simple-pole signs. Also, \(c_{00}\) means zero when the zero multi-index is absent from `S`.

- **Naive Bayes surrogate:** with \(V=v_1v_2\), the coefficient of \(N^{-3/2}\log^2N\) is indeed
  \[
  c_3=\pi\sqrt{2\pi}\,V.
  \]
  The theorem proves the **exact surrogate identity**, including cancellation of the odd \(u\,\mathrm{sign}\) term—not yet an asymptotic theorem for the actual KL.

- **Normal tilt:** `normalCoord` is an **orthonormal parametrisation of the normal space**, because its final coordinate direction is \((\beta,\alpha)/\rho\), orthogonal to \((\alpha,-\beta)\). Hence there is no additional coordinate-volume factor. The displayed denominator is the Gaussian determinant factor.  
  The tilt is independent of positive aligned orbit rescaling \((\alpha,\beta)\mapsto(t\alpha,\beta/t)\); the **whole prefactor is not**. Arbitrary-orientation invariance still needs the orthogonal-change-of-coordinates bridge. Your theorem proves the aligned version, not that bridge.

## 2. Next three targets, ranked

The following are proposed statements/API, not claims about existing declaration names.

### 1. (g) The two elementary state-density polar dictionaries

**Best value/effort:** these turn already-formal exact reductions into genuine distributional polar formulas.

For a smooth real test amplitude \(\varphi\) on a neighbourhood of \([-1,1]\), define
\[
R_\rho(\varphi,s)=
\int_{-1}^{1}\rho(t)(\varphi(t)-\varphi(0))|t|^{-2s}\,dt,
\]
using complex powers in Lean. Define the continuations
\[
\begin{aligned}
F_{\log}(\varphi,s)
 &=\frac{4\varphi(0)}{(1-2s)^2}
   +R_{\,2\log(1/|t|)}(\varphi,s),\\
F_{\rm uneq}(\varphi,s)
 &=\varphi(0)\left(\frac6{1-6s}-\frac2{1-2s}\right)
   +R_{\,|t|^{-2/3}-1}(\varphi,s).
\end{aligned}
\]

**Concrete Lean goals:**
```lean
(fun s => Flog φ s - (φ 0 : ℂ) / (s - 1/2)^2)
  =O[𝓝[≠] (1/2 : ℂ)] (fun _ => (1 : ℂ))

(fun s => Funeq φ s + (φ 0 : ℂ) / (s - 1/6))
  =O[𝓝[≠] (1/6 : ℂ)] (fun _ => (1 : ℂ))

(fun s => Funeq φ s - (φ 0 : ℂ) / (s - 1/2))
  =O[𝓝[≠] (1/2 : ℂ)] (fun _ => (1 : ℂ))
```

Also prove agreement with the original Mellin integrals on their convergence strips.

These identify the polar distributions:
- logarithmic density: \(C_{1/2,2}=\delta_0,\ C_{1/2,1}=0\);
- unequal density: \(C_{1/6,1}=-\delta_0,\ C_{1/2,1}=+\delta_0\).

**Route:** elementary Mellin integrals; \(\varphi(t)-\varphi(0)=O(|t|)\); dominated holomorphy. The remainder domains include \(\Re s<1\) and \(\Re s<2/3\), respectively. Then use principal-part uniqueness wherever the corresponding chart/global continuation has already been identified.

**Scope:** one day for the explicit continuations and polar data; do not include the naive Bayes density yet.

### 2. (b) Smooth tie formula with the decomposition supplied

Make the day-sized target the analytic formula, not a general-purpose smooth-division library.

Assume smooth `g₁ g₂ : ℝ → ℝ`, smooth `ρ : (Fin 2 → ℝ) → ℝ`, and set
```lean
η u := a + u 0 * g₁ (u 0) + u 1 * g₂ (u 1)
         + u 0 * u 1 * ρ u
```

Under the existing `hp0` and `FlatStrip` hypotheses, prove:
```lean
chartPolarCoeff p η tieH tieK (1/2) 1 = (a : ℂ) / 8

chartPolarCoeff p η tieH tieK (1/2) 0 =
  -((∫ x in (0:ℝ)..1, g₁ x : ℝ) : ℂ) / 2
  -((∫ y in (0:ℝ)..1, g₂ y : ℝ) : ℂ) / 4
```

**Route:** linearity; separate the wall variables; absorb factors of `u` and `v` into shifted chart exponents. The mixed term has shifted \(h=(2,1)\), whose convergence strip contains \(1/2\). For the two wall terms, subtract the value of their holomorphic numerator at \(1/2\), leaving a bounded divided difference. Finish with the same uniqueness route as the polynomial theorem.

**New content:** arbitrary smooth wall profiles, not just finite monomial sums.

### 3. (c) General-depth flat **one-dimensional reduction**, with unevaluated Gamma moments

Do not make trigamma a prerequisite.

Let
\[
H_j=\int_0^\infty e^{-x}x^{-1/2}(\log x)^j\,dx,\qquad
Q_m(X)=\frac1{\sqrt\pi}\sum_{j=0}^m
 {m\choose j}(-1)^jH_jX^{m-j},
\]
and
\[
D_m(N)=\int_{-1}^1e^{-Nt^2/2}
 \frac{2^m}{m!}\log^m(1/|t|)\,dt.
\]

**Concrete Lean goal:**
```lean
(fun N : ℝ =>
  D m N -
    Real.sqrt (2 * Real.pi) / (m.factorial : ℝ) /
      Real.sqrt N * Q m (Real.log N - Real.log 2))
  =O[atTop] (fun N => Real.exp (-N / 2))
```

**Route:** substitute \(x=Nt^2/2\), expand the finite power, and bound the tail. A useful uniform estimate for \(N\ge1,\ x\ge N/2\) is
\[
0\le \log(2x/N)\le 2(x-N/2)/N.
\]
This reduces the tail to exponential polynomial moments.

This proves the general-depth polynomial expansion **for the reduced integral**. Identifying \(D_{L-1}\) with the original unnormalised box integral is a separate product-density induction unless already available. Likewise, \(H_j=\Gamma^{(j)}(1/2)\) can follow later; the formula itself does not require formal higher Gamma derivatives.

### Leave as derivations for now

- **(a):** no averaging theorem based on integrability of the bare tilt. For bounded posterior observables, domination of the *normalised ratio* may work; that is a different argument.
- **(b):** geometric blow-up identification and two-crossing assembly.
- **(c):** Gaussian-prior general-depth formula and explicit higher Gamma constants.
- **(d):** the evaluated `gaussLogSq`.
- **(e):** actual-KL comparison and the cubic-phase coefficient.
- **(f):** noncompact Morse–Bott passage and Bessel constants.
- **(g):** naive Bayes polar distributions.

## 3. Is the unrestricted smooth tie formula worth doing now?

**Yes—but separate the formula from smooth-division infrastructure.**

The canonical decomposition is
\[
\begin{aligned}
a&=\eta(0,0),\\
g_1(u)&=\frac{\eta(u,0)-a}{u},&
g_2(v)&=\frac{\eta(0,v)-a}{v},\\
\rho(u,v)&=
 \frac{\eta(u,v)-\eta(u,0)-\eta(0,v)+a}{uv},
\end{aligned}
\]
with continuous extensions at zero. Equivalently,
\[
\rho(u,v)=\int_0^1\!\int_0^1
 \partial_{uv}\eta(tu,rv)\,dt\,dr.
\]

The clean final formula is
\[
\boxed{
C_{1/2,2}[\eta]=\frac{\eta(0,0)}8,\qquad
C_{1/2,1}[\eta]=
-\frac12\int_0^1\frac{\eta(u,0)-\eta(0,0)}u\,du
-\frac14\int_0^1\frac{\eta(0,v)-\eta(0,0)}v\,dv .
}
\]
These are the wall finite parts in the specified unit-box coordinates.

**Regularity:** bounded measurable \(g_1,g_2,\rho\) already suffices for the local parameter-integral holomorphy argument; continuity on the compact box is a convenient sufficient hypothesis. The respective holomorphy domains are
\[
\Re s<3/4,\qquad \Re s<1,\qquad \Re s<3/4.
\]
Thus \(C^2\) regularity of \(\eta\) suffices analytically. Keep `ContDiff ℝ ∞ η` in the public theorem to match the current polar-coefficient API.

**Size:** roughly one day for the supplied-decomposition theorem using shifted-chart holomorphy; another one–three days for canonical decomposition and the unrestricted smooth wrapper, depending on existing division/parameter-integral lemmas. I would do the analytic core now, but would not bundle it with blow-up geometry or crossing assembly.