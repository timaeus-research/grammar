## Verdict

**The conjecture is correct for the graded coefficient you specify**, with three qualifications:

1. Work with a **fixed field** \(\psi\), not an uncontrolled \(N\)-dependent sequence \(\psi_N\).
2. Fix the normalization of \(S\) and \(\beta\): the ladder identity quoted in the inventory does not match the displayed integral definition.
3. The replacement
   \[
   A\longmapsto A\,\frac{S_\mu(\xi)}{\Gamma(\mu)}
   \]
   identifies the **top surviving log coefficient under the depth-vanishing hypothesis**. It is not a coefficient-by-coefficient substitution rule for the entire expansion.

The one-dimensional empirical smooth engine is the right first substantial unit. It already restores the normal derivatives of fluctuation functions, without waiting for the multidimensional machinery.

I am auditing the supplied account of #141 and the repository architecture; I cannot inspect the issue or Lean declarations directly here.

---

## (a) Audit of empirical Theorem E

### 1. Normalize the fluctuation function first

For this answer, set \(\beta=1\) and define
\[
S_\mu(a)=\int_0^\infty s^{\mu-1}e^{-s+a\sqrt s}\,ds,
\qquad \mu>0.
\]
Then
\[
S_\mu(0)=\Gamma(\mu),
\qquad
\partial_a^r S_\mu(a)=S_{\mu+r/2}(a).
\]

For the definition in the inventory,
\[
S_{\mu,\beta}(a)=
\int_0^\infty s^{\mu-1}e^{-\beta s+\beta a\sqrt s}\,ds,
\]
the identities are instead
\[
S_{\mu,\beta}(0)=\beta^{-\mu}\Gamma(\mu),
\qquad
\partial_a S_{\mu,\beta}(a)=\beta S_{\mu+1/2,\beta}(a).
\]
There is **no factor \(1/2\)** for that displayed definition.

Consequently, when comparing to the population engine with the same \(\beta\), the normalization-independent replacement is
\[
A\longmapsto
A\,\frac{S_{\mu,\beta}(\xi)}{S_{\mu,\beta}(0)}.
\]
Your \(S_\mu/\Gamma(\mu)\) is exactly right at \(\beta=1\). Resolve this API issue before building new modules.

### 2. The \(\tau^r\) factor does not shift the exponent

In one dimension, put
\[
\mu_\alpha=\frac{h+\alpha+1}{2k}.
\]
Then
\[
\begin{aligned}
&\int_0^b u^{h+\alpha}
   (\sqrt t\,u^k)^r
   e^{-tu^{2k}+a\sqrt t\,u^k}\,du\\
&\qquad =
\frac{t^{-\mu_\alpha}}{2k}
\int_0^{tb^{2k}}
s^{\mu_\alpha+r/2-1}e^{-s+a\sqrt s}\,ds.
\end{aligned}
\]
Thus \(r\) changes the fluctuation-function index, not the power of \(t\).

Equivalently, the shifted monomial exponent gives
\[
t^{r/2}t^{-(h+\alpha+rk+1)/(2k)}
=t^{-\mu_\alpha}.
\]

For a fully resonant \(c\)-face, the same cancellation occurs simultaneously in all its coordinates. The highest log coefficient is
\[
\frac{S_{\mu+r/2}(a)}
     {(c-1)!\prod_{j\in J}2k_j}.
\]

**Important proof detail:** Taylor expansion is performed at fixed \(\tau\). Only after taking that Taylor expansion do you substitute \(\tau=\sqrt t\,u_J^{k_J}\). Differentiating the substituted expression in \(u_J\) would be a different calculation.

### 3. The normal-jet formula is correct

For fixed \(\mu\),
\[
\partial_J^\alpha\!\left[A\,S_\mu(\xi)\right]
=
\int_0^\infty
s^{\mu-1}e^{-s}
\partial_J^\alpha\!\left[Ae^{\sqrt s\,\xi}\right]\,ds.
\]
On bounded field ranges, differentiation under the integral is justified by bounds of the form
\[
\left|\partial^\alpha(Ae^{\sqrt s\,\xi})\right|
\le C_\alpha(1+s^{|\alpha|/2})e^{M\sqrt s},
\]
and
\[
e^{-s+M\sqrt s}\le e^{M^2/2}e^{-s/2}.
\]

The chain rule therefore gives exactly the proposed normal jet. For example,
\[
\partial_u[A S_\mu(\xi)]
=A'S_\mu(\xi)+A\xi'S_{\mu+1/2}(\xi),
\]
and
\[
\partial_u^2[A S_\mu(\xi)]
=A''S_\mu
 +(2A'\xi'+A\xi'')S_{\mu+1/2}
 +A(\xi')^2S_{\mu+1}.
\]

This is precisely where the old draft’s derivatives of fluctuation functions return.

### 4. Why the same graded constants survive

There is a useful conceptual check through the Mellin transform. Write \(q(u)=u^k>0\). Then
\[
\int_0^\infty
N^{z-1}e^{-Nq(u)^2+\sqrt Nq(u)\xi(u)}\,dN
=q(u)^{-2z}S_z(\xi(u)).
\]
Thus, on its initial convergence strip,
\[
\mathcal M_N Z^{\rm emp}(z)
=
\int A(u)u^{h-2kz}S_z(\xi(u))\,du.
\]
The population version has \(S_z(\xi)\) replaced by \(\Gamma(z)\).

A fully resonant \(c\)-face produces a pole of order \(c\). Its highest Laurent coefficient depends on the relevant normal jet of
\[
A S_\mu(\xi),
\]
evaluated at \(z=\mu\). It does not differentiate \(S_z\) in \(z\).

Accordingly:

- the resonant orders remain
  \[
  \alpha_j=2k_j\mu-h_j-1;
  \]
- the Taylor factorials and face combinatorics are unchanged;
- the population factor \(\Gamma(\mu)\) is replaced by \(S_\mu\), inside the normal-jet operation;
- once the depth-\((c+1)\) contributions vanish, log degrees \(>c-1\) vanish.

This Mellin calculation is a diagnostic and a possible alternative architecture, not a claim that the required Mellin inversion infrastructure already exists.

**Boundary of the claim.** Lower log coefficients generally involve
\[
\partial_\mu^\ell S_\mu(a)
=\int_0^\infty s^{\mu-1}(\log s)^\ell e^{-s+a\sqrt s}\,ds.
\]
They cannot generally be recovered by replacing the amplitude by \(A S_\mu/\Gamma(\mu)\) in each population coefficient. Even a constant field on a two-wall resonant face exposes this distinction.

### 5. Outer-coordinate dependence creates no additional graded term

Correct: \(w\) is a parameter in the normal Taylor calculation. The face integral contains
\[
\partial_J^{\alpha_J}
   [A(u)S_\mu(\xi(u))](0_J,w)
\]
with the existing population face weight.

There are no additional \(w\)-derivatives.

What changes is the proof infrastructure: the inner expansion’s coefficients are now functions of \(w\), so the current constant-coefficient `face_expansion` is insufficient without a parameterized variant or an equivalent specialized lemma.

### 6. Regularity

A clean first theorem should assume:

- smoothness in the box coordinates up to every wall;
- bounded field values;
- sufficiently controlled normal derivatives, uniformly over any base parameter being integrated;
- the existing amplitude, base-measure, and support hypotheses.

For a single compact box, taking \(\eta,\xi\) to be restrictions of \(C^\infty\) functions on an open neighborhood is convenient and sufficient. A suitable smooth-up-to-corners/Whitney formulation is also sufficient, but formalizing its equivalence to extension-based smoothness should not be part of this unit.

For a cutoff \(L\), only finitely many derivatives are needed. In one dimension, \(C^M\) suffices when
\[
\frac{h+M+1}{2k}\ge L.
\]
In several dimensions, the required finite orders are those chosen by the existing Taylor-remainder and face-integrability inequalities.

Smoothness in the **base variables** is not intrinsically required. Measurability, suitable continuity of the normal jets, and integrable domination suffice. Merely saying “each slice is smooth” does not provide the uniform bounds needed for assembly.

### 7. Coefficient existence must come first

Yes. Until an empirical cutoff expansion is proved, the proposed right-hand side is a candidate coefficient, not yet an identified canonical coefficient.

The logical order should be:

1. establish expansion existence;
2. define canonical `empCoeff`;
3. prove the graded identification;
4. recover the existing leading formula as a compatibility theorem.

---

## (b) Recommended proof architecture

### Main route: option 1, beginning in dimension one

Use the existing smooth-engine architecture, but add two genuinely new analytic components:

1. constant-field fluctuation kernels with compact-parameter-uniform estimates;
2. spatial-field Taylor remainders controlled uniformly in the auxiliary variable \(\tau\).

Do not start by copying the entire population engine.

### First theorem: the one-dimensional empirical smooth engine

Let \(k\ge1\), \(h\ge0\), \(b>0\), and let \(\eta,\xi\) be smooth near \([0,b]\). Define
\[
Z_{\eta,\xi}(N)
=\int_0^b
\eta(u)u^h e^{-Nu^{2k}+\sqrt N\,u^k\xi(u)}\,du.
\]
Set
\[
\mu_j=\frac{h+j+1}{2k},
\qquad
C_j(\eta,\xi)
=\frac{1}{2k\,j!}
\left.\frac{d^j}{du^j}
       [\eta(u)S_{\mu_j}(\xi(u))]
\right|_{u=0}.
\]
Then, for every \(L>0\), there are \(K,N_0\) such that
\[
\left|
Z_{\eta,\xi}(N)
-\sum_{\mu_j<L}C_jN^{-\mu_j}
\right|
\le K N^{-L}
\qquad(N\ge N_0).
\]

This is a full no-log cutoff expansion, not merely the first correction.

A particularly clean proof uses
\[
u=N^{-1/(2k)}x.
\]
Taylor-expand
\[
v\longmapsto \eta(v)e^{x^k\xi(v)}
\]
at \(v=0\), keeping \(x\) fixed. Polynomial factors in \(x^k\) are dominated by the remaining \(e^{-x^{2k}}\). Extend the coefficient integrals to infinity and control the resulting tails.

That proof avoids needing the parameterized generic face theorem for the first unit.

### Why not option 2?

There is no evident direct call to `smooth_cutoffExpansion` that makes the empirical problem disappear. The amplitude depends on \(N\), and the correct replacement depends on \(\mu\).

The Mellin identity above offers a real alternative if a suitable Mellin asymptotics engine exists. Building such an engine solely for this theorem is unlikely to be the minimal route.

### Why not option 3 as the main route?

It is viable for **analytic amplitudes and analytic fields**, with the required analytic norms. Restricting only the field to be analytic does not make an arbitrary smooth test amplitude analytic.

Also, the existing analytic expansion does not automatically justify coefficientwise manipulation and resolved assembly without uniform summability estimates.

Use the analytic Taylor tree later as a compatibility theorem:
\[
\texttt{familySpectralCoeff}
=
\texttt{empCoeff}
\]
on their common domain, preferably by uniqueness. Extracting every combinatorial identity directly from the Cauchy product need not be the main proof.

---

## (c) Staged Lean plan

These are design-level statements, not proposed verbatim declaration signatures. Line estimates are incremental and include local helper lemmas; they need revision after inspecting the dependency graph.

| Stage | Deliverable | Estimated Lean lines |
|---|---|---:|
| 0 | Normalize \(S\); compact-parameter derivative and tail bounds | 200–450 |
| 1 | One-dimensional empirical smooth expansion and explicit jets | 900–1,600 |
| 2 | Parameterized generic face theorem | 350–750 |
| 3 | Constant-field empirical face-monomial expansion | 1,000–2,000 |
| 4 | Spatial-field Taylor/remainder calculus | 1,000–2,000 |
| 5 | Multidimensional empirical smooth engine; canonical coefficients | 1,200–2,400 |
| 6 | Local graded face formula and deep-face vanishing | 700–1,400 |
| 7 | Resolved assembly and headline empirical Theorem E | 600–1,200 |

Roughly **6,000–12,000 lines**, best split into modules of about 200–500 lines. This is a new smooth engine with substantial reuse, not just a bookkeeping extension.

### Stage 0: fluctuation-function API

For \(\mu>0\), compact \(K\subset\mathbb R\), and finite derivative orders, prove:

- \(S_\mu(0)=\Gamma(\mu)\);
- \(\partial_a^rS_\mu=S_{\mu+r/2}\);
- continuity/smoothness and boundedness on \(K\);
- differentiation under the integral;
- polynomial-log moment and tail estimates uniform in \(a\in K\).

Add \(\mu\)-derivative lemmas when Stage 3 needs them rather than building an unnecessarily broad special-function API first.

### Stage 1: explicit one-dimensional coefficients

Prove the theorem above, followed by:

- `emp1D_cutoffExpansion`;
- explicit coefficient identification;
- zero-field specialization to the population coefficients;
- first- and second-normal-jet formulas.

**This is the minimal meaningful release that answers the author’s original question.**

### Stage 2: parameterized `face_expansion`

Replace the inner hypothesis by
\[
\left|
Z'(t,w)-\sum_{\mu,j}c_{\mu j}(w)t^{-\mu}(\log t)^j
\right|
\le C t^{-L}(1+|\log t|)^D,
\]
uniformly in \(w\), with measurable coefficient functions and the needed integrability bounds.

The output coefficients are
\[
\sum_{j\ge q}\binom jq
\int G(w)w^{h-a\mu}
       c_{\mu j}(w)(\log w^a)^{j-q}\,dw.
\]

The remainder retains the existing `faceRemWeight` estimate. Bounded \(c_{\mu j}\) is a convenient sufficient condition, not the most general necessary one.

### Stage 3: constant-field face kernels

For
\[
Z_e(t;a)=\int_{(0,b]^J}
u^e e^{-tu^{2k}+\sqrt t\,u^k a}\,du,
\]
prove compact-\(a\)-uniform cutoff expansions, then globalize their remainder estimates to all \(t>0\) for use in Stage 2.

Provide an explicit highest-log theorem: if
\[
e_j=2k_j\mu-1\quad(j\in J),
\]
then
\[
[t^{-\mu}(\log t)^{|J|-1}]\,Z_e(t;a)
=
\frac{S_\mu(a)}
{(|J|-1)!\prod_{j\in J}2k_j}.
\]

Lower-log coefficients involve \(\mu\)-derivatives of \(S\).

### Stage 4: spatial-field jets

Develop the normal Taylor decomposition of
\[
B(u,\tau)=A(u)e^{\tau\xi(u)}
\]
at fixed \(\tau\).

The crucial remainder bound should have the shape
\[
|R(u,\tau)|
\le C\left(\prod_{i\in R}u_i^{p_i}\right)
(1+\tau)^M e^{M_0\tau},
\qquad \tau\ge0.
\]
After multiplying by \(e^{-\tau^2}\), this is controlled by a polynomial times a Gaussian with weaker decay.

This is the main new bridge from smooth fields to the existing product-flat remainder machinery. Avoid a full explicit Faà di Bruno implementation if differentiation under the \(S\)-integral gives the needed jet identity more economically.

### Stage 5: existence and canonical `empCoeff`

For admissible chart data \(D=(A,\xi,h,k,b)\), define `empIntegral D N`. Prove
```text
∃ coeff, CutoffExpansion (Qamb k) (d - 1) (empIntegral D) coeff
```
with the repository’s established conventions for lattice support.

Then define `empCoeff D` by choosing such a coefficient family. Prove
```text
emp_cutoffExpansion :
  CutoffExpansion ... (empIntegral D) (empCoeff D)

empCoeff_unique :
  CutoffExpansion ... (empIntegral D) c → c = empCoeff D
```
on the coefficient index type.

If coefficients are represented on a larger ambient domain, normalize them to zero outside the expansion lattice and log-degree range. Expansion uniqueness does not determine values at unused indices.

Reuse or extract the **generic uniqueness theorem for cutoff expansions**. No empirical-specific uniqueness argument is needed.

Also prove:

- zero-field compatibility;
- amplitude linearity;
- invariance under changes of data that leave the integral family unchanged.

### Stage 6: local graded formula

For a chart amplitude vanishing near the relevant depth-\((c+1)\) locus, prove:

- `empCoeff ... μ j = 0` for \(j\ge c\);
- at \(j=c-1\), the population face sum with
  \[
  \partial_J^{\alpha_J}A
  \quad\text{replaced by}\quad
  \frac{1}{\Gamma(\mu)}
  \partial_J^{\alpha_J}[A S_\mu(\xi)].
  \]

Only include faces for which all resonant orders are nonnegative integers. Nonresonant faces contribute zero in this graded formula.

### Stage 7: root-field structure and assembly

A useful initial structure is conceptually:
```text
SmoothRootField extends ExistingContinuousRootField
  -- existing compatible branch representatives
  -- smoothness in normal box variables up to the walls
  -- joint continuity/measurability of their normal jets
  -- uniform bounds, or specified integrable envelopes, on active pieces
```

Do not require a global smooth scalar representative on the singular space. Smoothness belongs to the resolved branch representatives.

For compact bases and closed boxes, jointly continuous normal jets supply the desired boundedness. Otherwise record envelopes explicitly.

Resolved assembly can reuse the population organization, but it still needs empirical versions of:

- base-integrated remainder domination;
- negligible tails;
- coefficient integration;
- representative/partition independence, where appropriate.

The existing leading theorem should then be recovered from the \(\alpha=0\) specialization.

### Paper-facing statement

> **Empirical Theorem E.** Fix a root field whose resolved branch representatives are smooth up to the chart walls and satisfy the bounds required for chartwise integration. The empirical partition function admits a canonical full power–log cutoff expansion on the population exponent lattice. If \(F\) vanishes near \(D_{c+1}\), its coefficients of log degree greater than \(c-1\) vanish, and its coefficient at \((\mu,c-1)\) is the population graded stratum formula with each resonant normal jet of the chart amplitude replaced by the corresponding normal jet of \(A\,S_\mu(\xi)/\Gamma(\mu)\), at \(\beta=1\). Thus the field enters through its normal jets and derivatives of the fluctuation function; at zero normal order the formula reduces to the previously established empirical leading stratum measure. This is a deterministic theorem for a fixed smooth field and does not assert convergence in distribution of subleading coefficients for varying random fields.

Random coefficient convergence would require uniform expansions on suitably controlled smooth-field families and continuity in a sufficiently strong jet topology. The current continuous-field leading theory does not provide that for free.

---

## (d) Where the Weber module belongs

Your proposed interpretation is essentially right, with one useful refinement.

For the **graded normal-jet theorem**, the special-function identity needed is
\[
\partial_a^rS_\mu=S_{\mu+r/2}.
\]
Together with differentiation under the integral, this explains the derivative structure completely.

For the **full expansion**, lower log powers also bring in \(\mu\)-derivatives of \(S_\mu\). That is separate from the field-derivative ladder.

The Weber equation and parabolic-cylinder closed form are then:

- evaluation and simplification tools;
- recurrence relations for presenting coefficients;
- tools for studying their dependence on the field value;
- independent compatibility checks.

They are not prerequisites for expansion existence or the graded stratum formula.

So the honest answer to “where has that gone?” is:

> It has not disappeared: the continuous-field leading theorem only sees the restriction of the field to the stratum. Empirical Theorem E restores its normal jets, and the chain rule turns those jets into the fluctuation-function ladder. The Weber module evaluates and organizes those functions; it is downstream of, rather than foundational to, the structure theorem.