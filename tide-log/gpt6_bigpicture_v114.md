## Recommendation

Build **D1 as a facewise Mellin expansion theorem**, with **D2 as its analytic-data adapter**. Do not replace a smooth amplitude by a Taylor polynomial at the deepest corner.

The key design decisions are:

1. Each full-box core needs its own face analysis. A.e.-disjoint assembly does not remove this requirement.
2. The natural coefficient object is a **finite-order distribution supported on the union of the normal coordinate faces**, described by transverse jets and compatible Mellin finite parts.
3. For fixed smooth \(\chi\), this gives a new coefficient map that is **linear and continuous in the existing analytic \(\ell^1\) datum**.
4. There are two coordinate-free output forms:
   - retain the existing **infinite analytic observable-jet representation**, with new smooth-weight moments;
   - or use a **finite facewise jet representation**, with enlarged face bases.

In general, one cannot replace the existing infinite sum over observable normal order by a finite sum at the original deepest-stratum base.

---

# 1. The smooth core theorem

Write
\[
d=n+1,\qquad a_i=2k_i,\qquad
I_F(N)=\int_K\int_{(0,b]^d}
 F(s,v)\prod_i v_i^{h_i}
 e^{-N\beta\prod_i v_i^{a_i}}\,dv\,d\nu(s).
\]

Assume \(\nu\) is finite, \(\beta,b>0\), \(a_i>0\), and \(h_i>-1\). Positivity of \(h_i\) is stronger than necessary.

For the initial D1 theorem, take \(F\) itself to have continuous, uniformly bounded mixed normal derivatives of sufficiently high finite order. Then extend to \(F=\chi A\) with the existing analytic datum using D2 below.

## 1.1 Face geometry: what the core actually sees

In a chart normal to \(S_I\), the locus
\[
v_J=0,\qquad v_{I\setminus J}>0
\]
is a \(J\)-type divisor-face region; it is not the deepest corner \(S_I\) unless \(J=I\). More precisely, it maps to the relevant open stratum or its closure according to the chart’s other divisor coordinates.

The fact that another core is indexed by \(J\) does **not** remove this region from the asymptotic analysis of the \(I\)-core:

- the faces themselves have zero volume;
- boundary layers approaching those faces from inside the \(I\)-box have positive volume;
- those boundary layers contribute algebraic asymptotic terms.

Disjointness concerns the actual integration regions, not a cancellation or reassignment of their asymptotic boundary layers.

**Therefore every full-box core must handle all its coordinate faces.** Water-filling changes the geometry and base measures, not this analytic fact.

## 1.2 Mellin definition of the coefficients

For each \(s\), initially define
\[
Z_F(s,z)=
 \int_{(0,b]^d}F(s,v)\prod_i v_i^{h_i-a_i z}\,dv,
\qquad
\Re z<\lambda_0:=\min_i\frac{h_i+1}{a_i}.
\]

Its possible positive poles are
\[
\mathcal P=\bigcup_{i=1}^d
 \left\{\frac{h_i+1+m}{a_i}:m\in\mathbb N\right\}.
\]
Their order is at most \(d\).

Put
\[
H_F(s,z)=\Gamma(z)\beta^{-z}Z_F(s,z).
\]
At a pole \(\mu\), use the convention
\[
H_F(s,z)=
 \sum_{\ell=1}^{d}\frac{d_{\mu,\ell}(s)}{(\mu-z)^\ell}
 +\text{holomorphic part}.
\]
Then
\[
\boxed{\quad
 C_{\mu,j}(F)=\frac1{j!}\int_K d_{\mu,j+1}(s)\,d\nu(s),
 \qquad 0\le j\le d-1.
 \quad}
\]

This convention incorporates the contour-shift sign. It gives
\[
I_F(N)\sim
 \sum_{\mu,j} C_{\mu,j}(F)N^{-\mu}(\log N)^j.
\]

There is **no remaining \(N\)-dependent exponential in these coefficients**. They are finite-part face integrals, together with derivatives of \(\Gamma(z)\beta^{-z}\).

## 1.3 An explicit, compatible face-subtraction formula

Choose a contour height \(T>L\), avoiding \(\mathcal P\), and integers \(p_i\ge0\) satisfying
\[
h_i+1+p_i>a_iT.
\]
Define coordinate Taylor and remainder operators
\[
T_iF=\sum_{m=0}^{p_i-1}
 \frac{v_i^m}{m!}\,
 \partial_i^mF\big|_{v_i=0},
\qquad R_i=1-T_i.
\]
The operators in different coordinates commute, and
\[
F=\prod_i(T_i+R_i)F.
\]

For \(J\subseteq\{1,\ldots,d\}\), set
\[
F_{J,m}(s,v_{J^c})
 =
 \left.
 \frac{\partial_J^mF(s,v)}{m!}
 \right|_{v_J=0},
 \qquad 0\le m_i<p_i.
\]
Then the meromorphic continuation is
\[
\boxed{
\begin{aligned}
Z_F(s,z)
={}&
\sum_{J\subseteq[d]}
\ \sum_{m_J<p_J}
\left[
 \prod_{i\in J}
 \frac{b^{h_i+m_i+1-a_i z}}
      {h_i+m_i+1-a_i z}
\right]\\
&\quad\cdot
\int_{(0,b]^{J^c}}
 \left(\prod_{i\in J^c}R_i\right)
 F_{J,m}(s,v_{J^c})
 \prod_{i\in J^c}v_i^{h_i-a_i z}\,dv_{J^c}.
\end{aligned}}
\]
Empty products and empty integrals have their usual meanings.

The remainder integrals are holomorphic through \(\Re z=T\). This formula supplies:

- facewise transverse jets;
- the subtraction terms required at intersections;
- an unambiguous finite-part convention using the actual box width \(b\);
- the complete Laurent coefficients, including coincident-pole logarithms.

Different sufficiently large truncation orders give the same continuation and coefficients.

### Deepest-corner contribution

The term \(J=[d]\) is explicitly
\[
\sum_{m_i<p_i}
 \frac{\partial^mF(s,0)}{m!}
 \prod_i
 \frac{b^{h_i+m_i+1-a_i z}}
      {h_i+m_i+1-a_i z}.
\]
For \(F=\chi A\), with \(A(s,v)=\sum_\gamma A_\gamma(s)v^\gamma\),
\[
\frac{\partial^mF(s,0)}{m!}
 =
 \sum_{\gamma\le m}
 A_\gamma(s)
 \frac{\partial^{m-\gamma}\chi(s,0)}{(m-\gamma)!}.
\]

That is the requested corner convolution. **It is only one part of the coefficient formula.** All proper nonempty \(J\) supply face terms. Their tangential variables \(v_{J^c}\) must be retained.

The pole order can be sharpened: at \(\mu\), it is at most the number of coordinates \(i\) for which \(a_i\mu-h_i-1\) is a nonnegative integer.

## 1.4 Finite regularity and remainder

A clean first regularity hypothesis is availability of all mixed derivatives
\[
0\le\alpha_i\le p_i.
\]
Ordinary \(C^M\) regularity with \(M\ge\sum_i p_i\) suffices. This is a convenient sufficient condition, not a claim of minimal isotropic regularity.

Prove first the stronger contour statement
\[
I_F(N)
-
\sum_{\mu<T}\sum_{j=0}^{d-1}
 C_{\mu,j}(F)N^{-\mu}(\log N)^j
=O(N^{-T}).
\]
Gamma decay makes the vertical-contour estimate particularly useful here.

It follows that, for every requested cutoff \(L\),
\[
\boxed{
\left|
 I_F(N)-
 \sum_{\mu<L}\sum_{j=0}^{d-1}
 C_{\mu,j}(F)N^{-\mu}(\log N)^j
\right|
\le
 C_L\|F\|_{\mathrm{mixed},p}
 N^{-L}(1+\log N)^{d-1}.
}
\]

For the coordinate-free \(o(N^{-A})\) theorem, include coefficients with \(\mu\le A\) and prove the remainder using some \(T>A\). Do not confuse this with truncation at \(\mu<A\): a pole at \(A\) matters.

---

# 2. D2: retaining the analytic datum

This is the preferred integration path into the current engine.

Let
\[
A(s,v)=\sum_\gamma c_\gamma(s)v^\gamma,\qquad
\sum_\gamma |c_\gamma(s)|b^{|\gamma|}<\infty,
\]
with the existing continuity in the weighted \(\ell^1\) norm. Then
\[
I_{\chi A}(N)
 =
 \int_K\sum_\gamma c_\gamma(s)M_{\gamma,\chi}(N,s)\,d\nu(s),
\]
where
\[
M_{\gamma,\chi}(N,s)
 =
 \int_{(0,b]^d}
 \chi(s,v)v^{\gamma+h}
 e^{-N\beta\prod v_i^{a_i}}\,dv.
\]

Define \(m_{\gamma,\mu,j}(\chi;s)\) using the preceding Laurent construction with \(h\) replaced by \(h+\gamma\).

## 2.1 The precise uniform theorem to prove

For fixed \(L\), prove both
\[
\sum_{\mu<L}\sum_{j=0}^{d-1}
 |m_{\gamma,\mu,j}(\chi;s)|
 \le C_L\|\chi\|_{\mathrm{mixed},P}\,b^{|\gamma|}
\]
and
\[
\boxed{
\left|
M_{\gamma,\chi}(N,s)
-
\sum_{\mu<L,j}
m_{\gamma,\mu,j}(\chi;s)N^{-\mu}(\log N)^j
\right|
\le
C_L\|\chi\|_{\mathrm{mixed},P}
b^{|\gamma|}
N^{-L}(1+\log N)^{d-1}.
}
\]
Constants are uniform in \(s,\gamma,N\ge2\). Use zero coefficients when the shifted monomial has no pole at \(\mu\).

A useful scaled seminorm is
\[
\|\chi\|_{\mathrm{mixed},P}
 =
 \max_{\alpha_i\le P_i}
 b^{|\alpha|}\sup_{s,v}|\partial^\alpha\chi(s,v)|.
\]

### How to obtain uniformity without differentiating \(v^\gamma\)

Use **index-dependent subtraction depths**
\[
p_i(\gamma)=
 \min\{p\ge0:\gamma_i+h_i+1+p>a_iT\}.
\]
Then \(p_i(\gamma)\le P_i:=p_i(0)\).

- When \(\gamma_i\) is large enough, no subtraction in that coordinate is needed.
- Otherwise only a bounded number of derivatives of \(\chi\) are used.
- The factors produced by all integrals and Taylor terms retain the common factor \(b^{|\gamma|}\).
- Choose \(T\) away from the pole set. The relevant denominators then have a uniform positive separation.

This avoids artificial polynomial growth in \(\gamma\). It should be the target D2 theorem.

### Role of the Cauchy margin

The packet margin \(b'>b\) supplies an easier fallback proof:

- differentiate \(\chi v^\gamma\);
- accept a factor \((1+|\gamma|)^M\);
- absorb it using
  \[
  \sup_\gamma (1+|\gamma|)^M(b/b')^{|\gamma|}<\infty.
  \]

That proves continuity on analytic data controlled at \(b'\), but **does not by itself prove continuity on the old \(\ell^1\) norm at \(b\)**.

Recommended order: obtain the margin-based result first if it substantially reduces implementation cost; then prove the index-aware uniform estimate to recover the exact old data topology.

## 2.2 The new coefficient map

Set
\[
\operatorname{smoothTanCoeff}_{\chi}(x;\mu,j)
 =
 \int_K\sum_\gamma
 c_\gamma(s)m_{\gamma,\mu,j}(\chi;s)\,d\nu(s).
\]
The uniform estimate proves:

- absolute summability;
- continuity in the base;
- linearity and boundedness in \(x\);
- cutoff remainder bounds proportional to \(\|x\|\);
- compatibility with the old `tanCoeff` when \(\chi=1\).

Thus, for fixed \(\chi\), the analytic-data continuity interface used by §4 can be retained.

**Qualification:** continuity alone does not establish every stochastic identity. Linear operations and probabilistic arguments using bounded coefficient maps transfer; insertion and ladder identities must be rechecked against the new moments. The coefficient map must remain observable-independent for the J-min interface.

---

# 3. Reuse and replacement

| Existing component | Status |
|---|---|
| Scalar monomial Mellin/Gamma formulas | Reuse as primitives and regression theorems |
| Existing multivariate monomial expansion | Reuse for \(\chi=1\), consistency and parts of D2 |
| Exponentially small phase-gap tail | Reuse, with the same integrability hypotheses |
| `commonD n` | Reuse: maximum log degree remains \(d-1=n\) |
| `commonQ`, `spectrumLe` | Reuse under the existing arithmetic hypotheses on \(h,k\) |
| Geometry, normal exponents, measures, transport | Reuse |
| Frames and `Φ_eq` | Reuse for deepest-corner tensors; extend to facewise output if chosen |
| Uniqueness of power-log expansions | Reuse |
| RLCT readout from the first nonzero term | Reuse, but nonvanishing must be established |
| `TangentialData` | Retain for \(A\) through D2; supplement by smooth-weight data |
| `amplitude_eq` | Replace by \(\chi\cdot\operatorname{evalF}(\cdots)=c\cdot\mathrm{obs}\circ\Phi\), or separate weighted transport |
| `CoreNormalMomentPresentation.analytic` | Retain for the analytic observable in D2; not an analyticity assertion about \(\chi A\) |
| `CoefficientCertificate.datum_eq` | Retain analytic convolution for analytic factors; add smooth face-jet Leibniz identities |
| `tsum_field_pair` | Retain in the analytic-observable representation; replace by finite sums only in an enlarged facewise representation |

An implementation detail: if \(\chi\ge0\) is absorbed into the measure, it generally depends on both \(s\) and \(v\). It is **not merely a modification of the base measure \(\nu\)**. The core integral and coefficient map must still know the full weight.

---

# 4. Certificates and coordinate-free output

## 4.1 Recommended certificate split

Use an order-indexed finite certificate as the foundational object:
```text
SmoothCoreExpansionAt T
  geometry / transport / phase_normal
  smoothWeight
  finite mixed derivative data and bounds
  analytic datum for A
  amplitude identity
  face-subtraction compatibility
  coefficient definition by Laurent principal parts
  remainder estimate beyond requested order
```

Then package
```text
SmoothResolvedCertificate
  fixed geometry and weights
  smoothness at all orders
  expansionAt : ∀ requestedOrder, ...
  compatibility between orders
```

For \(C^M\) weights, expose only the orders justified by \(M\). Do not ask a finite-regularity producer to fake an all-orders certificate.

`CoefficientCertificate'` should contain:

1. the analytic density/observable datum and its existing convolution identity;
2. smooth transverse face jets;
3. restriction/intersection compatibility;
4. finite-order Leibniz identities;
5. identification of the Laurent coefficient functional with the geometric pairing;
6. summability bounds if using the infinite analytic-jet representation.

The finite parts should be derived by a fixed subtraction operator, not supplied independently as unrelated face numbers.

## 4.2 A necessary correction: finite normal order at the old base is false

Consider the two-normal-coordinate example with analytic observable \(\psi(x)\). The leading functional can contain
\[
\int_0^b \chi(x,0)\psi(x)\,\frac{dx}{x}.
\]
Even when \(\chi\) is supported away from \(x=0\), this depends on arbitrarily high Taylor coefficients of analytic \(\psi\) at \(0\). Taking \(\psi(x)=x^m\) shows that no fixed finite corner jet suffices.

Consequently:

### Option A — maximal reuse

Keep
\[
\sum_{r=0}^{\infty}\frac1{r!}
 \langle D_\perp^r\phi(s),B^\chi_{I,r,\mu,j}(s)\rangle.
\]
Construct \(B^\chi\) using the new smooth-weight coefficient map. Use packet margins or the bounded D2 map to establish convergence.

Here the old base \(S_I\), frames and tensor architecture survive, but the sum over \(r\) is generally infinite even at a fixed asymptotic order.

### Option B — genuinely finite-order output

Enlarge the bases to the coordinate faces:
\[
(s,v_{J^c}),\qquad v_J=0.
\]
Use finitely many transverse derivatives in the \(J\) directions, leaving full tangential dependence along the face. Coefficients are compatible finite-part integrals of these jets.

The invariant object is most naturally a coefficient distribution
\[
\mathcal C_{\mu,j}(\phi),
\]
supported on the divisor faces, of finite differential order for each cutoff. A representation by ordinary smooth fields integrated against the old stratum measures is not automatic: finite parts may be distributional.

**Recommendation:** implement Option A first; make Option B the conceptual specification and a later coordinate-free refinement.

## 4.3 Canonicity

For certificates representing the same integral functional:

- total coefficients agree by uniqueness of the asymptotic scale;
- coefficient distributions agree if equality is established for a determining class of observables;
- order choices and subtraction depths do not affect the coefficients.

Stratumwise or corewise allocation is not canonical merely because the total integral is canonical. It is invariant when the comparison preserves the corresponding localized integral functionals, possibly after regrouping. Changing a partition generally redistributes coefficients.

An intrinsic decomposition into face-supported pieces additionally needs a specified extension/subtraction convention or another uniqueness condition preventing transfers onto intersections.

---

# 5. Ranked unit plan

## U0 — Lock the specification and first regression

**No dependency.**

Prove, for smooth \(f\) supported in a compact subset of \((0,b)\),
\[
\int_0^b\int_0^b
 f(x)e^{-Nx^2y^2}\,dy\,dx
 =
 \frac{\sqrt\pi}{2}N^{-1/2}
 \int_0^b\frac{f(x)}x\,dx
 +O(e^{-cN}).
\]

All deepest-corner jets vanish, while the leading coefficient need not vanish.

Also test \(\chi=1\), where a double pole produces the known logarithm. These two tests distinguish face contributions from coincident-pole contributions.

## U1 — One-coordinate subtraction as a parameterized operator

Build Taylor/remainder operators, weighted integral estimates, and continuity in compact parameters. Base parameters may already include unintegrated normal coordinates.

Deliverable: bounded parameterized meromorphic continuation with explicit simple denominators.

## U2 — Tensor subtraction and Laurent bookkeeping

**Depends on U1.**

Prove commuting subtractions, the subset formula, compatibility at intersections, and independence of truncation order.

Deliverable: `FaceMellinDatum` and finite Laurent principal parts.

## U3 — Smooth core expansion

**Depends on U2 and existing Gamma/inversion infrastructure.**

Prove the \(O(N^{-T})\) contour theorem, then the existing-style cutoff bound.

Deliverable: a smooth replacement for `cutoffExpansion_gInt`, independent of geometry.

## U4 — D2 adapter and analytic compatibility

**Depends on U3.**

Implement shifted moments and uniform-in-\(\gamma\) estimates. Prove:

- bounded linear coefficient maps;
- summable remainder estimates;
- equality with old coefficients for \(\chi=1\);
- agreement when \(\chi\) is analytic and is instead absorbed into the analytic convolution.

This is the main reuse milestone.

## U5 — Core/decomposition assembly

**Depends on U4.**

Introduce weighted core presentations; reuse transport, finite assembly and the phase-gap tail.

Deliverable: smooth-weight `AnalyticCoreDecomposition` analogue with essentially the old expansion proof after the core theorem call is changed.

## U6 — Coordinate-free D2 certificate

**Depends on U5.**

Retain analytic observable tensors and the convergent infinite \(r\)-sum. Prove coefficient identification, J-min independence and total canonicity.

Do not make finite corner order a requirement.

## U7 — Finite facewise coordinate-free presentation

**Depends on U6 or directly on U3 plus face geometry.**

Expose face-supported coefficient distributions and finite transverse order. This is valuable, but should not block the working smooth engine.

## U8 — Stochastic adapter

**Depends on U4 and whichever certificate interface §4 consumes.**

Port results based on bounded linear coefficient maps first. Check insertion/ladder identities separately rather than declaring the entire stochastic layer unchanged.

---

# 6. Interface with Q1-\(\alpha\), stopping rule, and non-claims

The parallel weighted-atlas producer need only supply to this engine:

- the existing exact monomial chart geometry and transport;
- a smooth weight on a neighbourhood of each closed normal box;
- finite mixed-derivative bounds at the requested order;
- analytic packets for the remaining factors;
- weighted measure assembly and a tail gap.

No partition construction belongs in this consult.

A stratum-adapted weight independent of the relevant normal variables is an immediate special case: it factors through the base integral and must give exactly the existing coefficients. More general overlap cases should be compared through equality of their localized integrals and asymptotic uniqueness.

### Stopping rule

The first usable engine is complete at **U6**, once:

1. the face regression passes;
2. analytic compatibility passes;
3. the smooth coefficient map is continuous in the advertised analytic-data norm;
4. weighted core assembly gives arbitrary-order expansions for \(C^\infty\) weights;
5. total coefficient canonicity is proved.

U7 is not required to run D1/D2 in parallel with Q1-\(\alpha\).

### Explicit non-claims and corrections

- A full-box core does not become face-free because cores are a.e.-disjoint.
- Corner Taylor remainder \(O(\|v\|^M)\) is insufficient.
- Finite transverse order **along every face** does not mean finite normal order at the deepest base.
- Smooth weights can cancel or remove candidate poles. Flatness along all relevant faces can produce decay faster than every algebraic order.
- The old geometric RLCT is preserved only with appropriate nonvanishing/positivity hypotheses.
- Positive real \(k_i,h_i\) alone do not imply a common rational lattice. Reuse `commonQ` under its actual arithmetic assumptions.
- Mellin transformation factorizes a monomial’s zeta integral. The original exponential \(e^{-N\beta\prod v_i^{2k_i}}\) does not itself factor into independent one-variable exponentials.
- A \(C^M\) certificate proves only its licensed range of orders.

The central deliverable is therefore **a bounded, face-aware Mellin coefficient operator parameterized by a smooth weight**, not a smooth Taylor-series replacement for the analytic engine.
