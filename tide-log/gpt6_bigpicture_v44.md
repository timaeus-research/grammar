## Recommendation

**Choose (A), but strengthen its endpoint to arbitrary continuous chart phases.** The joint constant-phase theorem is plausibly cheap; the substantive payoff is that it should unlock fixed nonconstant phases **without a new Taylor tree**.

Rank: **A strengthened > moving/random spatial fields > B**. Do not restart kernels merely to package the constant-phase Gaussian mixture. That mixture is useful as a corollary, but it does not capture the paper’s spatial fluctuation unless the limiting phase is constant on the dominant face.

Below is a six-unit programme. Units 1–3 are the core; stop after 3 if necessary.

## Setup and standing hypotheses

Write \(B\) for the compact normal-form box, \(F=P_JB\) for the dominant face, and \(Y_N=Nu^{2k}\). Let
\[
\nu_F(dv)=H^{-1}\eta(v)
 \prod_{i\notin J}v_i^{h_i-2k_i\lambda}\,dv
\]
denote the normalized face measure, using exactly the existing convention for \(H\). Regard it also as a measure on \(B\), supported on \(F\).

Assume the existing normal-form hypotheses, nonnegative amplitude, and **\(H>0\)**. Let \(Q_N^\xi\) be the chart posterior with phase \(\xi\).

The crucial internal input is the leading constant-phase asymptotic with continuous amplitude multipliers:
\[
\eta\longmapsto\eta g,\qquad
H\longmapsto H_g=H\int_F g(v)\,\nu_F(dv).
\]
If the current theorem has stronger multiplier regularity, proving this extension is part of Unit 1—not an external hypothesis to conceal.

---

## 1. Weighted energy-Laplace limits

**Target.** For \(g\in C(B,\mathbb R)\), \(t\ge0\), and constant \(a\),
\[
\mathbb E_{Q_N^a}\!\left[e^{-tY_N}g(u)\right]
\longrightarrow
L_a(t)\int_F g(v)\,\nu_F(dv),
\]
where
\[
L_a(t)=\int e^{-ty}\,\rho_a(dy).
\]

**Route.** Apply the leading asymptotic to the numerator with amplitude \(\eta g\), using the existing temperature-change identity, and divide by the denominator.

**Assessment of “cheap.”** Yes, at the scalar-asymptotic level. Moreover, use **\(g(u)\), not merely \(g(P_Ju)\)**. Its leading coefficient still depends only on its face restriction. This simultaneously detects concentration onto the face.

**Traps.**

- An asymptotic stated only for positive amplitudes cannot simply be instantiated with signed \(g\). Shift by a constant and subtract, or establish a signed-multiplier lemma.
- If only smooth multipliers are supported, approximate continuous \(g\) uniformly; posterior normalization gives the error bound immediately.
- Verify the face coefficient convention and integrability of its noncritical-coordinate weights.
- No conclusion here covers \(H=0\): that can change the dominant asymptotic.

**External inputs:** none beyond the already assumed normal-form setting.

## 2. Constant-phase joint energy–chart convergence

**Target.**
\[
(Y_N,u)_\#Q_N^a
\;\Rightarrow\;
\rho_a\otimes\nu_F
\qquad\text{on }[0,\infty)\times B.
\]

The requested energy–face theorem follows by projection.

**Proof architecture.** Combine energy tightness with compactness of \(B\), then use Unit 1 to identify the limit. Alternatively, approximate continuous observables on energy truncations by finite sums of products, using energy Laplace functions as a determining algebra.

**What is genuinely new:** asymptotic independence of energy and face position, plus posterior concentration onto the dominant face in chart coordinates.

**Trap:** the scalar Laplace continuity theorem does not automatically prove this product-space statement. This is the main extra probability/approximation lemma behind the apparently cheap argument. It need not require a general multivariate Laplace theorem.

**Non-claim:** this is not the deferred original-space posterior or geometric bridge.

## 3. Main headline: arbitrary continuous spatial phases

**Target.** For every fixed \(\xi\in C(B,\mathbb R)\),
\[
(Y_N,u)_\#Q_N^\xi\Rightarrow Q^\xi,
\]
where
\[
Q^\xi(dy,dv)=
\frac{y^{\lambda-1}e^{-\beta y+\beta\xi(v)\sqrt y}}
     {M_\xi}\,dy\,\nu_F(dv),
\qquad
M_\xi=\int_F J_\lambda(\xi(v))\,\nu_F(dv).
\]

Thus **only the restriction \(\xi|_F\) survives at leading order**.

Also prove the evidence ratio
\[
\frac{\mathcal Z_N[\eta;\xi]}
     {\mathcal Z_N[\eta;a]}
\longrightarrow
\frac{M_\xi}{J_\lambda(a)}.
\]

**Route.** Tilt the Unit 2 joint law by
\[
w_\xi(y,u)=e^{\beta(\xi(u)-a)\sqrt y}.
\]
This is continuous but unbounded. Supply the essential uniform-integrability bound:
\[
\mathbb E_{Q_N^a}[e^{c\sqrt{Y_N}}]
=
\frac{\mathcal Z_N[\eta;a+c/\beta]}
     {\mathcal Z_N[\eta;a]},
\]
whose limit is already known. A larger phase shift bounds a power of the tilt, yielding uniform integrability.

**Consequences, stated explicitly:**
\[
\operatorname{Law}_{Q^\xi}(v)
=\frac{J_\lambda(\xi(v))}{M_\xi}\nu_F(dv),
\]
and
\[
\operatorname{Law}_{Q^\xi}(Y)
=\frac{\int_F J_\lambda(\xi(v))\rho_{\xi(v)}\,\nu_F(dv)}
       {M_\xi}.
\]

This includes candidate (A), with \(\xi(v)=a+\varepsilon\zeta(v)\), but is substantially stronger.

**Traps.**

- Weak convergence alone does not justify the unbounded tilt.
- Merely bounded measurable \(\xi\) is not covered automatically.
- Spatial variation transverse to \(F\) disappears only under the continuity/concentration argument—not by replacing \(\xi(u)\) with \(\xi(P_Ju)\) pointwise.

## 4. Spatial-phase moments and face selection

**Target.** For \(r\ge0\) and continuous \(g\),
\[
\mathbb E_{Q_N^\xi}[Y_N^r g(u)]
\longrightarrow
\frac{\int_F g(v)J_{\lambda+r}(\xi(v))\,\nu_F(dv)}
     {M_\xi}.
\]

Derive the spatial-phase mean and variance, including
\[
\operatorname{Var}_{Q^\xi}(Y)
=
\mathbb E_{\widehat\nu_\xi}[v(\xi(V))]
+
\operatorname{Var}_{\widehat\nu_\xi}(\mu(\xi(V))),
\]
where
\[
\widehat\nu_\xi(dv)=J_\lambda(\xi(v))\,\nu_F(dv)/M_\xi.
\]

This exhibits a new **between-face contribution to energy variance** and makes the evidence-induced selection of face locations explicit.

**Inputs:** larger phase-shift bounds again control polynomial factors.

**Non-claim:** no next-log correction or convergence rate.

## 5. Moving continuous spatial phases

**Target.** If \(N_m\to\infty\) and
\[
\|\xi_m-\xi\|_\infty\to0,
\]
then
\[
(Y_{N_m},u)_\#Q_{N_m}^{\xi_m}\Rightarrow Q^\xi,
\]
with the evidence-ratio and mixed-moment limits above.

Also establish continuity of
\[
\xi\longmapsto Q^\xi
\]
from \(C(B)\) with the sup norm into probability measures with the weak topology.

**Why this is not merely skipped packaging:** it supplies the deterministic theorem needed for genuine random spatial fields, rather than scalar random phases.

**Trap:** compact-uniform convergence on compact subsets of \(C(B)\) may follow; uniformity over all sup-norm-bounded phases does not follow. Such a family need not be equicontinuous near the face.

## 6. Author-facing capstone: random spatial-field posterior limits

**External input, explicitly conditional:**
\[
\xi_N\Rightarrow\Xi
\quad\text{in }C(B).
\]
A scalar CLT for \(\xi_N(0)\) is insufficient.

**Target.** As random probability measures,
\[
(Y_N,u)_\#Q_N^{\xi_N}\Rightarrow Q^\Xi.
\]
With a posterior draw, obtain the joint phase–energy–location limit whose conditional law given \(\Xi\) is \(Q^\Xi\).

The constant Gaussian phase \(\Xi(v)\equiv X\) gives candidate (C):
\[
\operatorname{Law}(Y)=\int\rho_a\,\operatorname{Law}(X)(da).
\]

**Important distinction:** this averages normalized posteriors. Do **not** evidence-weight the outer law of \(X\) or \(\Xi\). Evidence weighting occurs *within the face mixture*; a different sampling model would be needed to reweight the external fluctuation law.

---

## Cuts and decision points

- **B: postpone.** Leading spatial limits are available by weak convergence and tilting; next-log spatial corrections require quantitative asymptotics and cannot be extracted from that argument.
- **C: retain only as a corollary of Unit 6**, unless a short author-facing theorem is urgently desired.
- **D: excluded by instruction. E: after theorems.**
- **First checkpoint:** inspect the continuous-amplitude leading theorem. If it supports Unit 1, the strongest near-term headline is not merely “joint energy–face law,” but **“the leading posterior for every continuous chart phase depends only on its dominant-face restriction.”**

That is a natural new programme, directly connected to §4, without reopening geometry or the inverse-log no-go.
