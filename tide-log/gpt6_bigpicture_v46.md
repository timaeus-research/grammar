**Prioritise assembly, then a genuinely nontrivial consequence of the explicit \(B\), then joint-limit identification.** The random-field theorem is worth doing, but only as a conditional transfer theorem—not as another external CLT project.

I recommend **six bounded units**. No PDF report now.

## 1. Finite-chart next-log assembly, including normalized observables

This is the highest-value immediate theorem. It is purely analytic assembly of supplied chart expansions, **not** the deferred geometric bridge.

### Exact target

Let \(I\) be finite. Suppose chart \(i\) has exponent \(\lambda_i\), multiplicity \(m_i\ge1\), and
\[
Z_i(N)
=N^{-\lambda_i}L^{m_i-1}
\left(F_i+\frac{B_i}{L}+o(L^{-1})\right).
\]
For secondary charts, only a leading asymptotic is actually needed; for negligible charts, an appropriate big-\(O\) bound suffices.

Set
\[
\lambda=\min_i\lambda_i,\qquad
m=\max_{\lambda_i=\lambda}m_i,
\]
and
\[
I_0=\{i:\lambda_i=\lambda,\ m_i=m\},\qquad
I_1=\{i:\lambda_i=\lambda,\ m_i=m-1\}.
\]
When \(m=1\), take \(I_1=\varnothing\). Absorb fixed chart weights into \(F_i,B_i\), or write them explicitly throughout.

Then
\[
\boxed{
\sum_i Z_i(N)
=N^{-\lambda}L^{m-1}
\left(A+\frac{D}{L}+o(L^{-1})\right),
}
\]
where
\[
\boxed{
A=\sum_{i\in I_0}F_i,\qquad
D=\sum_{i\in I_0}B_i+\sum_{i\in I_1}F_i.
}
\]

Thus **multiplicity-\((m-1)\) charts contribute their leading coefficients to the global next-log term**. Their own \(B_i\) do not contribute at this order.

### Assembled observable correction

Suppose denominator and numerator chart contributions have aligned expansions, with coefficients \(F_{i,q},B_{i,q}\), where \(q=0\) denotes the denominator. Define
\[
A_q=\sum_{I_0}F_{i,q},\qquad
D_q=\sum_{I_0}B_{i,q}+\sum_{I_1}F_{i,q}.
\]
If \(A_0>0\), then
\[
\boxed{
L\left(\frac{\sum_i Z_{i,q}(N)}{\sum_i Z_{i,0}(N)}
-\frac{A_q}{A_0}\right)
\longrightarrow
\frac{A_0D_q-A_qD_0}{A_0^2}.
}
\]
For \(q=1\), using the aligned energy numerator, this is the assembled \(c_2\).

Also take the inexpensive corollary
\[
-\log\sum_i Z_i(N)
=\lambda L-(m-1)\log L-\log A-\frac{D}{AL}+o(L^{-1}).
\]

**Inputs:** finite chartwise asymptotics and an exact finite-sum identity, both supplied as hypotheses.

**Traps / non-claims:**
- Do not claim construction of charts or partitions of unity.
- Require \(A_0>0\); cancellation can invalidate the chosen leading scale.
- Charts with larger \(\lambda_i\) are negligible even if their multiplicities are larger, but prove the power-versus-log estimate.
- No all-orders quotient machinery: one reusable two-term ratio lemma is enough.
- With your \(B_i=0\) convention for \(m_i=1\), the assembled \(1/L\) coefficient is zero when the dominant multiplicity is one.

---

## 2. Independent two-dimensional regression, followed by strict transverse sensitivity

This both checks the signs/constants and turns LXXX into a strict theorem.

### Constant-phase regression

For
\[
d=2,\quad h=(0,0),\quad k=(1,1),\quad \eta=1,
\]
one has \(\lambda=\tfrac12\), \(m=2\), and
\[
\boxed{
F(a,1)=\frac14J_{1/2}(a),\qquad
B(a,1)=\frac14\dot J_{1/2}(a).
}
\]

There is **no additional \(J_{1/2}(a)\) term**: there are no nonface coordinates, and all transverse finite parts vanish for constant \(H\).

An independent calculation is especially clean. For the local integral
\[
Z_N(a)=\int_0^1\int_0^1
e^{-\beta N x^2z^2+\beta a\sqrt N\,xz}\,dx\,dz,
\]
the substitutions \(r=xz\), \(y=Nr^2\) give
\[
\boxed{
Z_N(a)=\frac{N^{-1/2}}4
\int_0^N y^{-1/2}e^{-\beta y+\beta a\sqrt y}
(\log N-\log y)\,dy.
}
\]
The exponentially decaying tail then independently yields the two coefficients above.

At \(a=0\),
\[
B(0,1)=
\frac{\sqrt\pi}{4\sqrt\beta}
\bigl(\log\beta+\gamma_{\!E}+2\log2\bigr).
\]
The \(J,\dot J\) theorem should be the required regression; the Euler-constant specialization is optional if its special-function dependencies are expensive.

### Strict example

In the same model, take
\[
\xi(x,z)=c+ax,\qquad a>0.
\]
Then
\[
F(\xi,1)=\frac14J_{1/2}(c),
\]
but
\[
\boxed{
B(\xi,1)-B(c,1)
=\frac12\int_0^1
\frac{J_{1/2}(c+at)-J_{1/2}(c)}t\,dt>0.
}
\]

This is a concrete theorem saying: **identical leading joint limit, different next-log evidence coefficient**.

**Inputs:** your explicit \(B\), strict increase of \(J_\lambda\), and integrability of this finite part.

**Bound:** prove the integrability needed for this example first. A derivative bound on the compact interval \([c,c+a]\) suffices. Do not make general finite-part integrability infrastructure a prerequisite.

---

## 3. Product form, converse, and independence characterization

Let \(\nu^\xi\) denote the spatial marginal of the joint face law:
\[
\nu^\xi(dv)\ \propto\
\eta(v)J_\lambda(\xi(v))\,\mu_{\mathrm{face}}(dv).
\]
Your disintegration says the conditional energy kernel is \(\rho_{\xi(v)}\).

### Targets

For any \(a\in\mathbb R\),
\[
\boxed{
\widetilde Q^\xi=\rho_a\otimes\nu^\xi
\quad\Longleftrightarrow\quad
\xi(v)=a\quad \nu^\xi\text{-a.e.}
}
\]

Then strengthen to
\[
\boxed{
Y\ \text{and}\ V\ \text{are independent under }\widetilde Q^\xi
\quad\Longleftrightarrow\quad
\xi(V)\ \text{is a.s. constant}.
}
\]

The converse uses
\[
\mathbb E[Y\mid V]=\mu(\xi(V)),
\qquad
\mu(a)=\mathbb E_{\rho_a}[Y],
\]
and `phaseLawMean_strictMono`.

**Inputs:** disintegration, integrability of \(Y\), strict monotonicity.

**Traps:**
- Your disintegration interface is currently for bounded measurable functions. Pass to \(Y\) by truncation; do not silently apply it to an unbounded function.
- The conclusion is almost everywhere on the spatial marginal, not everywhere on the face. Pointwise constancy needs an additional support/continuity argument.
- General independence initially gives an unspecified common energy law; show it must be some \(\rho_a\).

This is a useful identification theorem, not merely packaging.

---

## 4. Conditional random-field transfer—yes, worth formalising

There is a clean theorem here. I would target **random posterior laws**, with finite observables as a corollary.

Use the compact closed cube \(K=[0,1]^d\), so face evaluation is defined, and put
\[
E=\mathbb R\times K,\qquad
\mathcal Q_N(\xi)=\text{joint posterior law of }(NK,u),\qquad
\mathcal Q(\xi)=\widetilde Q^\xi.
\]

### Deterministic core

Prove
\[
\xi_N\to\xi\text{ in }C(K)
\quad\Longrightarrow\quad
\mathcal Q_N(\xi_N)\Rightarrow\mathcal Q(\xi),
\]
together with continuity of \(\mathcal Q\) and measurability of \(\mathcal Q_N\).

This implies uniform-on-compact convergence in a compatible metric on \(\mathcal P(E)\).

### Random theorem

Conditional on the external hypothesis
\[
X_N\Rightarrow X\quad\text{in }C(K),
\]
prove
\[
\boxed{
(X_N,\mathcal Q_N(X_N))
\Rightarrow
(X,\mathcal Q(X))
\quad\text{in }C(K)\times\mathcal P(E).
}
\]

In particular, for bounded continuous \(g_1,\ldots,g_r\),
\[
\left(X_N,\left(\int g_j\,d\mathcal Q_N(X_N)\right)_{j=1}^r\right)
\Rightarrow
\left(X,\left(\int g_j\,d\mathcal Q(X)\right)_{j=1}^r\right).
\]

**Inputs:** external \(C(K)\)-valued weak convergence; fixed nonnegative weight with positive face mass.

**Main analytic trap:** phase perturbations introduce
\[
e^{\beta\|\xi_N-\xi\|_\infty\sqrt y},
\]
not a uniformly bounded likelihood ratio. Use uniform energy-tail/exponential-moment control for bounded phase sets. Pointwise convergence for each fixed phase is insufficient.

**Non-claims:** no field CLT, no geometric bridge, no stable convergence relative to an unspecified background sigma-algebra, and no random-field \(1/L\) correction without additional rate hypotheses.

**Bound:** if law-valued measurability becomes disproportionate, stop at the finite-observable theorem. That is still a substantive, publishable transfer result.

---

## 5. A bounded next-log observable dictionary

Do not pursue “arbitrary observables” at next order. Prove one reusable ratio theorem, then instantiate it for:

1. \((NK)^r g(u)\), with \(r\in\mathbb N\) and \(g\) in the existing coefficient-family class;
2. energy Laplace transforms;
3. evidence ratios between two admissible phases or weights.

For moments, define
\[
H_r(u)=\eta(u)g(u)J_{\lambda+r}(\xi(u)).
\]
The leading coefficient is the existing face formula with \(J_\lambda\) replaced by \(J_{\lambda+r}\); the second coefficient uses the same replacement, including
\[
\dot J_{\lambda+r}=-\partial_\nu J_\nu\big|_{\nu=\lambda+r}.
\]
The spatial weight \(w\) stays unchanged because shifting \(h\) by \(2kr\) and \(\lambda\) by \(r\) cancels in its exponent.

Then
\[
L\left(
\mathbb E_{Q_N^\xi}[(NK)^r g(u)]-\frac{F_{r,g}}{F_{0,1}}
\right)
\to
\frac{F_{0,1}B_{r,g}-F_{r,g}B_{0,1}}{F_{0,1}^2}.
\]

For \(e^{-sNK}\), \(s\ge0\), remember the parameter change is
\[
\beta'=\beta+s,\qquad
\xi'=\frac{\beta}{\beta+s}\xi.
\]
Changing \(\beta\) alone changes the phase coupling incorrectly.

**Non-claim:** joint weak convergence by itself does not supply moment convergence or next-log corrections for arbitrary bounded continuous energy observables.

---

## 6. One-page theorem map, not a report project

After units 1–4, add a short repository document containing:

- local \(F,B\);
- assembled \(A,D\);
- normalized-observable correction;
- joint disintegration and independence criterion;
- random-field transfer assumptions;
- an explicit list of the still-external geometric and probabilistic inputs.

No PDF and no retrospective narrative. This is a hand-off aid, not the next research milestone.

### Bottom line

The next four priorities are:

1. **Global next-log assembly.**
2. **The \(B=\dot J_{1/2}/4\) regression and strict transverse example.**
3. **Independence iff face phase is a.s. constant.**
4. **Conditional random-field transfer.**

Fold free energy into assembly; postpone broad observable generalization until those are done.
