## 1. Fidelity check

**DCXXV–DCXXVII match the stated formal scope, with one important correction to the advertised Bessel corollary.** I am checking the supplied statements, not independently checking the repository.

### DCXXVI: the second coefficient is correct

Put \(s=\sqrt{2\pi}\) and
\[
D_L=(L+1)\log2-(L-1)\gamma.
\]
The Mellin jet relevant to the leading pole includes the scaling factor:
\[
2^{(L-1)\varepsilon}\Gamma(\tfrac12-\varepsilon)\Gamma(1+\varepsilon)^L.
\]
Its logarithmic derivative at zero is
\[
(L-1)\log2-\psi(\tfrac12)-L\gamma=D_L.
\]
Consequently
\[
\boxed{\frac{B_L}{A_L}=(L-1)D_L}.
\]
This agrees exactly with the landed formula. The jet of the **Gamma product alone** gives \(2\log2-(L-1)\gamma\); omitting the power of \(2\) loses \((L-1)\log2\).

With leading degree \(m+2=L-1\), the recursion
\[
A'=\frac{A}{(m+3)s},\qquad
B'=\frac{B/(m+2)+2AR_0}{s}
\]
is correct.

### DCXXV: honest remainder, correct exclusion

The landed \(O(N^{-1/2-1/k}\log N)\) is exactly what its explicit bound says; do not relabel it log-free.

Excluding \(k=1\) is essential **for this asymptotic formula**, not for the definition or conditional reduction. At \(k=1\), the scaled regularisation parameter remains \(1\), rather than tending to zero, and the proposed constant is not the correct limiting constant.

There is, however, a substantially simpler route to the log-free bound than applying a sharper estimate uniformly to `famAmp`; see target 1 below.

### DCXXVII: normalisation correct; translated constant incorrect

The argument \(1/(4N)\), exponential factor, and denominator are the standard normalisation for
\[
K_0(z)=\int_0^\infty e^{-z\cosh t}\,dt.
\]

But the proposed corollary must be
\[
\boxed{e^zK_0(z)=\log(1/z)+\log2-\gamma
       +O\!\left(z\log(1/z)\right)}
\]
as \(z\downarrow0\), **not** with \(3\log2-\gamma\).

Indeed, DCXII has \(\log N+3\log2-\gamma\), and \(N=1/(4z)\) subtracts \(2\log2\). Export this corrected corollary using `𝓝[>] 0`. It is a useful, small follow-up, not a separate day-sized project.

---

## 2. Recommended next three targets

My value-per-effort ranking is:

1. **Log-free family remainder**, using comparison with the fixed monomial amplitude.
2. **Cone averaged posterior**, via a uniform domination lemma for the exact ratio.
3. **Depth-three residual limit**, with unevaluated but integrable constants.

These each close a clearly identified gap without requiring a general Mellin-transfer theorem.

### Target 1 — log-free family remainder

The key is to compare the **whole integrals**, rather than first comparing renormalised constants:
\[
|J_{\mathrm{famAmp}(k,m)}(\varepsilon)-J_{\mathrm{monoAmp}(k)}(\varepsilon)|
\le \frac1{m^2}\int_0^\infty u e^{-u^{2k}/2}\,du
\le \frac2{m^2}.
\]
Here use \(1-e^{-u^2/(2m^2)}\le u^2/(2m^2)\) and
\(\sqrt{u^2+\varepsilon}\ge u\). The last integral needs only an elementary split at \(1\), not a new Gamma evaluation.

For the **fixed** amplitude \(a(u)=e^{-u^{2k}/2}\), prove
\[
\left|J_a(\varepsilon)-\log(1/\varepsilon)-2\log2-R_a\right|
\le 2\varepsilon,\qquad 0<\varepsilon\le1,\quad k\ge2.
\]
Route:

* Isolate the flat integral over \((0,1)\); its exact logarithmic formula has error at most \(\varepsilon/2\).
* On \((0,1)\), use
  \[
  |a(u)-1|\le u^{2k}/2\le u^4/2.
  \]
* On both remaining pieces use
  \[
  0\le \frac1u-\frac1{\sqrt{u^2+\varepsilon}}
  \le \frac{\varepsilon}{2u^3}.
  \]
  The weighted integrals are now finite without a logarithm.

Since \(\varepsilon=m^{-(2k-2)}\le m^{-2}\), this gives the comfortable uniform constant \(4\).

**Proposed interfaces:**
```lean
theorem ampJ_famAmp_sub_monoAmp_le
    {k : ℕ} (hk : 2 ≤ k) {m ε : ℝ}
    (hm : 1 ≤ m) (hε : 0 < ε) :
    |ampJ (famAmp k m) ε - ampJ (monoAmp k) ε| ≤ 2 / m ^ 2

theorem ampJ_monoAmp_remainder_le
    {k : ℕ} (hk : 2 ≤ k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |ampJ (monoAmp k) ε -
      (Real.log (1 / ε) + 2 * Real.log 2 + ampRenorm (monoAmp k))|
      ≤ 2 * ε
```

Then target:
```lean
theorem monomialFamily_two_term_logFree_bound
    {k : ℕ} (hk : 2 ≤ k) {N : ℝ} (hN : 1 ≤ N) :
    |monomialFamilyZ k N - Real.sqrt (2 * Real.pi) / Real.sqrt N *
      (((k : ℝ) - 1) / k * Real.log N + 2 * Real.log 2 +
        (Real.log 2 - Real.eulerMascheroniConstant) / k)| ≤
      4 * Real.sqrt (2 * Real.pi) /
        (Real.sqrt N * N ^ (1 / (k : ℝ)))
```

**Status:** honest day-sized target. This route avoids the small quadratic defect of `famAmp` at zero, which makes a direct generic amplitude estimate unnecessarily logarithmic.

### Target 2 — cone: average of ratios, with domination

The note asks for
\[
\mathbb E_a\!\left[\frac{Z_N[u_1^2;a]}{Z_N[1;a]}\right],
\]
**not** the ratio of averaged evidences. In fact, the latter is the prior expectation \(1\), whereas the former tends to \(1/2\).

Set \(\delta=N^{-1/2}\), and let \(\mathbb E_{\delta,a}\) denote expectation under the density proportional to
\[
e^{-t^2/2+at-\delta|t|}.
\]
The supplied Leray formulas give the exact identity
\[
\sqrt N\left(\frac{Z_N[u_1^2;a]}{Z_N[1;a]}-\frac12\right)
=\mathbb E_{\delta,a}[t_+].
\]

Now exponentially tilting the distribution of \(|t|\) by \(e^{-\delta|t|}\) decreases its mean. Hence
\[
0\le \mathbb E_{\delta,a}[t_+]
\le \mathbb E_{\delta,a}|t|
\le \mathbb E_{0,a}|t|
\le |a|+\sqrt{2/\pi}.
\]
This is an integrable, \(N\)-independent envelope under the standard Gaussian law of \(a\).

**Lean-facing reduced interface:**
```lean
noncomputable def coneScaledCorrection (δ a : ℝ) : ℝ :=
  (∫ t : ℝ, max t 0 *
      Real.exp (-t ^ 2 / 2 + a * t - δ * |t|)) /
  (∫ t : ℝ, Real.exp (-t ^ 2 / 2 + a * t - δ * |t|))

theorem coneScaledCorrection_bound
    {δ : ℝ} (hδ : 0 ≤ δ) (a : ℝ) :
    0 ≤ coneScaledCorrection δ a ∧
    coneScaledCorrection δ a ≤ |a| + Real.sqrt (2 / Real.pi)
```

Prove the mean-decrease lemma by the double-integral sign
\[
(r-r')(e^{-\delta r}-e^{-\delta r'})\le0;
\]
this avoids differentiating a quotient of integrals.

Then DCT gives
\[
\boxed{\sqrt N\left(\mathbb E_a[\text{posterior }u_1^2]-\frac12\right)
\longrightarrow \frac1{\sqrt\pi}},
\]
since \(\mathbb E_{a,G}(a+G)_+=1/\sqrt\pi\).

**Scope:** domination and the resulting limit are day-sized using the existing Leray bridge. This proves an \(o(N^{-1/2})\) remainder after the first correction—not automatically the averaged \(O(N^{-1})\) remainder.

### Target 3 — depth-three constant as an integral-defined limit

There is a typo in the proposed \(q\): **the subtraction requires a factor \(1/v\)**. Without it, \(q\) is not integrable.

Use
\[
c=3\log2-\gamma,\qquad
q(v)=Z_2(v^2)-\mathbf1_{(1,\infty)}(v)\frac{2\log v+c}{sv},
\quad v>0.
\]

**Proposed interfaces:**
```lean
noncomputable def depthThreeQ (v : ℝ) : ℝ :=
  gaussLaplace2 (v ^ 2) -
    (Ioi (1 : ℝ)).indicator
      (fun v => (2 * Real.log v + depthTwoC) /
        (Real.sqrt (2 * Real.pi) * v)) v

theorem integrableOn_depthThreeQ :
    IntegrableOn depthThreeQ (Ioi 0)
```

Then define \(Q=\int_0^\infty q(v)\,dv\) and
\(J=\int_0^\infty h(x)\log x/x\,dx\), and prove
\[
\boxed{
\sqrt N\,Z_3(N)-A_3(\log N)^2-B_3\log N
\longrightarrow
\frac{cR_0+2J}{\pi}+\frac2sQ }.
\]

Precise route:

1. On \((0,1]\), `gaussLaplace2_bounds` gives \(0\le q\le1\).
2. On \((1,\infty)\), use the **explicit two-term remainder** from DCXII/the depth-three infrastructure:
   \[
   |q(v)|\le C(1+\log v)/v^3.
   \]
   Plain \(0\le Z_2\le1\) bounds are insufficient for this tail.
3. Rescale the scalar recursion:
   \[
   \sqrt N Z_3(N)=\frac2s\int_0^\infty
       e^{-v^2/(2N)}Z_2(v^2)\,dv.
   \]
4. The \(q\)-piece tends to \(2Q/s\) by DCT.
5. Reuse the DCXXIII flat-piece identity. Retain, rather than bound away, the \(h\)-piece:
   \[
   \int_a^\infty h(x)\frac{\log N+2\log x+c}{x}\,dx.
   \]
6. `gaussH_log_pow` integrability supplies convergence to \(R_0,J\); the omitted \((0,a)\) pieces vanish, including the factor \(\log N\), using \(h(x)=O(x^2)\).

**Status:** honest day-sized target. Keep exact evaluation of \(Q\) separate.

---

## 3. Other candidates

### Exact \(J\): worthwhile, but slightly less predictable

The clean identity is
\[
\int_0^\infty h(x)x^{z-1}\,dx
=\frac{2^{z/2}\Gamma(1+z/2)-1}{z}.
\]
Its derivative at zero gives
\[
J=\frac{(\log2-\gamma)^2}{8}+\frac{\pi^2}{48}.
\]

Thus the natural route needs
\[
\Gamma''(1)=\gamma^2+\pi^2/6.
\]
With the existing half-point second derivative, **duplication is cleaner than reflection**: twice differentiate its logarithm to obtain
\[
\psi_1(\tfrac12)+\psi_1(1)=4\psi_1(1),
\]
hence \(\psi_1(1)=\pi^2/6\). Local positivity lets this be expressed through ordinary Gamma derivatives without introducing a polygamma API.

The remaining work is a parameter-differentiation/removable-singularity lemma for the renormalised Mellin integral. Day-sized if that infrastructure is readily reusable; otherwise budget more than one day.

### Naive Bayes: a face lemma is day-sized; the full envelope is not yet specified

Take
\[
0<r=\lambda_1<\eta,\qquad
\delta\le\lambda_2\le1-\delta,\qquad
0<\eta\le\delta/2.
\]
On this patch,
\[
M_+=r(1-\lambda_2),\qquad M_-=r\lambda_2,\qquad
V\asymp_\delta r.
\]
Therefore
\[
M_\pm\asymp_\delta r,\qquad
M_\pm/\sqrt V\asymp_\delta\sqrt r,\qquad
|u_1|\le C_\delta+|\log r|.
\]

A concrete density-only result is
\[
|\rho(\lambda,\sqrt V\,z)|
\le C_\delta(1+|\log r|)^2(1+|\log|z||)^2,
\qquad z\ne0.
\]
Integrating this against a fixed Gaussian gives an envelope with **\(a=0,b=2\)**.

For the existing full certificate, the definitions of
\(\ell_\lambda,c_\lambda,b_\lambda,L_\lambda,\varphi_\lambda(0)\) are still needed: the density formula alone does not determine which inverse scales its envelope contains. In particular, an inverse power \(p\) of the standardised support radius costs \(r^{-p/2}\), and face integrability requires \(p<2\), absent compensating factors. Do not infer full facewise domination merely from logarithmic density coefficients.

### Blow-up observable numerators: good reserve target

For the \(k=2\) model with the raw Gaussian prior, define the inserted integrals \(X_N,Y_N\) using \(x^2,y^2\). Then
\[
\boxed{N X_N\to\pi,\qquad \sqrt N\,Y_N\to2\sqrt{2\pi}}.
\]
Conditional Gaussian integration followed by DCT is cleaner than forcing both through `ampJ`:

* \(x=N^{-1/4}u\) for \(X_N\);
* \(x=N^{-1/2}v\) for \(Y_N\), whose reduced denominator is \((1+Nx^2)^{3/2}\).

Both are honest day-sized leading-numerator theorems.

### `ThreeTermData`: third coefficients are not all constant terms

Propagating three leading coefficients needs the **exact values \(R_0,J\)** and only bounds for higher moments. If \(C_L\) denotes the coefficient of \((\log N)^{L-3}\), then
\[
C_{L+1}
=\frac{C_L/(L-2)+2B_LR_0+4(L-1)A_LJ}{s}.
\]

But this is the constant term only at depth three. Computing the actual constant at depth four already involves
\(\int h(x)\log^2x/x\,dx\), together with a renormalised residual contribution. Thus “constant terms at every depth by `ThreeTermData`” overstates what that interface supplies.

---

## 4. Convention hazards

* **Raw versus normalised Gaussian:** `monomialFamilyZ` has prior mass \(2\pi\), while `gaussLaplaceL` uses probability-normalised Gaussian factors. Keep this visible in observable theorem names/docstrings.
* **`famAmp` depends on the scaling parameter.** Its renormalised constant is not exactly the limiting monomial constant.
* **Natural subtraction versus real subtraction:** explicitly cast \(k\) before writing coefficient expressions such as `((k : ℝ) - 1) / k`; reserve natural subtraction for exponents with hypotheses.
* **`TwoTermData ... m`:** leading degree is `m + 2`, depth is `m + 3`; the landed all-depth interface starts at depth three.
* **`besselK0Integral`:** its integral representation has the claimed meaning for \(z>0\). Lean’s totalised integral at nonintegrable parameters is not a Bessel continuation.
* **The family’s `8`:** a sufficient bound constant for the landed proof, not an asymptotic coefficient or an optimal constant.
* The isolated `def / set / clear_value` fragments in the supplied signature dump are extraction debris, not public declarations. Remove them from any published API synopsis.