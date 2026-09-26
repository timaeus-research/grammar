## A. Mathematical statements and proofs

Two conventions should be fixed before starting.

1. **The geometric polar functionals exclude the radial Gamma factor.** Write
   \[
   T_{h,k}(s)[G]=\int_{(0,1]^d}G(u)\prod_i u_i^{h_i-2k_i s}\,du,
   \qquad
   T_{h,k}(s)=\sum_{r=1}^{M_\mu}\frac{A_{\mu,r}}{(\mu-s)^r}+H_\mu(s).
   \]
2. The supplied definition confirms
   \[
   \boxed{\texttt{polarCoeff}\ c\ \mu\ q=(-1)^{q+1}q!\,c_{\mu,q},}
   \]
   not \((-1)^q q!c_{\mu,q}\). The paper’s equation `eq:laurent` is correct.

I use \(G\) for a chart amplitude, \(F\) for a resolved observable, and \(\zeta\) for a chart root field. All statements below are at unit temperature.

### A1. Chart meromorphic continuation

Let \(d\ge1\), \(h_i\in\mathbb N\), \(k_i\in\mathbb N_{>0}\), and \(C=[0,1]^d\). Amplitudes are smooth on a neighbourhood of \(C\), complex-valued when discussing continuation. Put
\[
\lambda_i=\frac{h_i+1}{2k_i},\quad
\lambda_0=\min_i\lambda_i,\quad
\mathcal P=\bigcup_i\left\{\frac{h_i+a+1}{2k_i}:a\in\mathbb N\right\},
\]
and
\[
J_\mu=\{i:\alpha_i:=2k_i\mu-h_i-1\in\mathbb N\},
\qquad M_\mu=|J_\mu|.
\]

Here \(M_\mu\) is a **candidate order bound**, not necessarily the pole order of a particular amplitude pairing.

**Theorem A1.**

1. For \(\Re s<\lambda_0\), the integral defining \(T_{h,k}(s)[G]\) is absolutely convergent and holomorphic in \(s\).
2. It has a unique meromorphic continuation to \(\mathbb C\), with possible poles only in \(\mathcal P\).
3. At \(\mu\in\mathcal P\), there are continuous complex-linear functionals \(A_{\mu,r}\), \(1\le r\le M_\mu\), such that
   \[
   T_{h,k}(s)[G]
   =\sum_{r=1}^{M_\mu}\frac{A_{\mu,r}[G]}{(\mu-s)^r}+H_\mu(s)[G].
   \]
   Locally in \(s\), both the polar functionals and the holomorphic remainder are controlled by one finite \(C^R(C)\) seminorm.
4. Writing
   \[
   R_{\mu,r}=\left\{u\in C:
      \#\{i\in J_\mu:u_i=0\}\ge r\right\},
   \]
   the distribution \(A_{\mu,r}\) is supported in \(R_{\mu,r}\).
5. For real \(G\), all \(A_{\mu,r}[G]\) are real.

The relevant distribution space can initially be described as continuous linear functionals on smooth functions near \(C\), with continuity established by finite-seminorm bounds. There is no need to build an abstract space of distributions before proving the theorem.

#### Constructive continuation

Choose integers \(p_i\ge0\), and expand in coordinate \(i\):
\[
L_i(s)g=
\sum_{a<p_i}\frac{\partial_i^a g|_{u_i=0}}
 {a!\,(h_i+a+1-2k_i s)}
+\int_0^1
 \left(g-\sum_{a<p_i}\frac{\partial_i^ag|_{u_i=0}}{a!}u_i^a\right)
 u_i^{h_i-2k_i s}\,du_i.
\tag{1}
\]
This is an operator in the remaining variables. The remainder is holomorphic when
\[
2k_i\Re s<h_i+p_i+1.
\tag{2}
\]

Compose these operators over the coordinates, or equivalently use the existing subset expansion with `faceAmp`. The resulting expression is
\[
\sum_{(J,a)}
 \frac{\texttt{faceW}(J,a)}
 {\prod_{j\in J}(h_j+a_j+1-2k_js)}
 \int_{(0,1]^{J^c}}
 \operatorname{faceAmp}_{p,J,a}(G)(w)\,
 w^{h_{J^c}-2k_{J^c}s}\,dw.
\tag{3}
\]

Every complementary integral is holomorphic under (2), by the rectangular remainder bound. Differentiating it \(\ell\) times in \(s\) adds
\[
(-\log w^{2k})^\ell.
\]
These factors are integrable after retaining a strict margin in (2).

For every compact set of \(s\)-values, one sufficiently large \(p\) works. Different choices of \(p\) agree on the initial half-plane, hence agree meromorphically. This constructs the continuation.

For formalisation, the important quantitative statement is:

> On a closed disk avoiding the other candidates, after multiplication by \((s-\mu)^{M_\mu}\), expression (3) is holomorphic and bounded by \(C\|G\|_{C^R(C)}\), for \(R=\sum_i p_i\) and a suitable \(C\).

Cauchy estimates then bound its Taylor coefficients, hence the \(A_{\mu,r}\).

#### An explicit local polar model

For \(i\in J_\mu\), set
\[
D_i g=\frac{\partial_i^{\alpha_i}g(0)}{2k_i\alpha_i!}.
\]
Then
\[
L_i(s)=\frac{D_i}{\mu-s}+B_i(s),
\]
with \(B_i\) holomorphic near \(\mu\). For \(i\notin J_\mu\), \(L_i(s)\) itself is holomorphic there. Thus
\[
T_{h,k}(s)=
\bigotimes_{i\in J_\mu}
 \left(\frac{D_i}{\mu-s}+B_i(s)\right)
\otimes
\bigotimes_{i\notin J_\mu}L_i(s).
\tag{4}
\]

Formula (4) proves the order and support assertions. Every term contributing to \(A_{\mu,r}\) contains residues in at least \(r\) coordinates.

It also gives the precise meaning of “finite transverse order”: a finite sum of normal delta derivatives with finite-part/logarithmic distributions in complementary coordinates. It does **not** generally mean a bounded-order jet at the deepest crossing alone.

### A2. Holomorphic amplitude families and all logarithmic orders

#### The amplitude-family lemma

Let \(V\subset\mathbb C\) be a neighbourhood of a positive \(\mu\), containing no other candidate pole. Let \(g:V\times C\to\mathbb C\) satisfy:

- each \(g(s,\cdot)\) extends smoothly near \(C\);
- for each required spatial derivative \(\partial_u^\alpha\), the function
  \(\partial_u^\alpha g(s,u)\) is jointly continuous;
- for each \(u\), it is holomorphic in \(s\);
- these derivatives are locally uniformly bounded on compact subsets of \(V\times C\).

For the local conclusion, only finitely many spatial derivatives are needed: choose \(R\) as in A1. Equivalently, use a holomorphic family in the finite-\(C^R\) topology.

Write
\[
g_\ell(u)=\frac1{\ell!}\partial_s^\ell g(\mu,u).
\]
Then
\[
T_{h,k}(s)[g(s)]
=\sum_{p=1}^{M_\mu}
 \frac{\displaystyle\sum_{r=p}^{M_\mu}
          (-1)^{r-p}A_{\mu,r}[g_{r-p}]}
      {(\mu-s)^p}
+\text{holomorphic}.
\tag{5}
\]

**Proof.** Taylor-expand in the finite-\(C^R\) topology:
\[
g(s)=\sum_{\ell<M_\mu}(s-\mu)^\ell g_\ell
 +(s-\mu)^{M_\mu}R(s),
\]
where \(R(s)\) is holomorphic in that topology. Apply the uniformly finite-order family of A1. The last term is holomorphic because the pole order is at most \(M_\mu\). In the finite sum use
\[
(s-\mu)^\ell=(-1)^\ell(\mu-s)^\ell.
\]

The uniform topology is essential. Pointwise holomorphy and pointwise smoothness without uniform control are not sufficient hypotheses for this argument.

#### The complex fluctuation amplitude

Define, for \(\Re s>0\),
\[
S(s,a)=\int_0^\infty t^{s-1}e^{-t+a\sqrt t}\,dt.
\]
This is a **new complex-index definition** relative to the supplied closure: `Grammar.fluctuation` has three real arguments.

For \(a\) in a bounded real interval and \(s\) in a compact subset of \(\Re s>0\),
\[
\partial_s^\ell\partial_a^j S(s,a)
=\int_0^\infty
 t^{s+j/2-1}(\log t)^\ell e^{-t+a\sqrt t}\,dt.
\tag{6}
\]
A common integrable majorant follows from:

- near zero: \(t^{\sigma_0-1}|\log t|^\ell\), \(\sigma_0>0\);
- near infinity: a polynomial-log factor times \(e^{-t/2}\), using
  \(a\sqrt t\le t/2+a^2/2\).

Consequently \(g(s,u)=G(u)S(s,\zeta(u))\) satisfies the amplitude-family lemma. Spatial derivatives introduce finite sums of the integrands in (6), with \(j\) bounded by the spatial derivative order.

On the real axis,
\[
S(\mu,a)=\texttt{fluctuation}\ 1\ \mu\ a,
\]
and
\[
\partial_s^\ell S(\mu,a)
=\operatorname{iteratedDeriv}_\nu^\ell
   (\texttt{fluctuation}\ 1\ \nu\ a)\big|_{\nu=\mu}.
\tag{7}
\]

#### Mellin identity

For \(0<\Re s<\lambda_0\),
\[
\operatorname{Mellin}_N
  \big(\texttt{empIntegral}\ G\ \zeta\ h\ k\big)(s)
=T_{h,k}(s)[G\,S(s,\zeta)].
\tag{8}
\]

Absolute Fubini is justified by boundedness of \(G,\zeta\) on \(C\), followed by \(t=Nu^{2k}\). In particular,
\[
\int_0^\infty N^{\sigma-1}
 \left|\texttt{empIntegral}\ G\ \zeta\ h\ k\ N\right|\,dN
\le C\int_Cu^{h-2k\sigma}\,du<\infty.
\]
The empirical integral is locally integrable in \(N>0\) and bounded as \(N\downarrow0\). Thus the hypotheses of `Grammar.polarCoeff_unique` are available.

Use `Grammar.SmoothEngine.emp_cutoffExpansion` for existence of the expansion. **Do not attempt to deduce an asymptotic expansion from meromorphic continuation alone:** that would require additional vertical-growth/inversion estimates, unnecessarily duplicating the existing engine.

#### Formula (*) in the exact library convention

For \(\ell\ge0\), put
\[
g^{[\ell]}_\mu(u)
=G(u)\left.\partial_s^\ell S(s,\zeta(u))\right|_{s=\mu}.
\]
Define the standard Laurent coefficient
\[
b_{\mu,q}
=\sum_{r=q+1}^{M_\mu}
 \frac{(-1)^r}{(r-q-1)!}
 A_{\mu,r}[g^{[r-q-1]}_\mu].
\tag{9}
\]
Then the continued Mellin transform minus
\[
\texttt{polarPart}\ (d-1)\ b_\mu\ \mu
\]
is holomorphic near \(\mu\), padding \(b_{\mu,q}=0\) for \(q\ge M_\mu\). Therefore
\[
\boxed{
b_{\mu,q}
=\texttt{polarCoeff}\,
  (\texttt{empCoeff}\ G\ \zeta\ h\ k)\,\mu\,q.
}
\tag{10}
\]
Solving (10) gives
\[
\boxed{
\texttt{empCoeff}\ G\ \zeta\ h\ k\ \mu\ q
=
\frac1{q!}
\sum_{r=q+1}^{M_\mu}
 \frac{(-1)^{r-q-1}}{(r-q-1)!}
 A_{\mu,r}\!\left[
 G\,\left.\partial_s^{r-q-1}S(s,\zeta)\right|_\mu
 \right].
}
\tag{*}
\]

The proof connecting (8) to `mellinContinuation` needs an identity theorem on the positive half-plane with the discrete candidate set removed. It is not enough merely to know equality on the initial strip and boundedness near an unrelated pole.

For implementation, replace the sum over \(r\) by \(j=r-1\):
\[
\frac1{q!}\sum_{j\in\mathrm{Ico}(q,M_\mu)}
 \frac{(-1)^{j-q}}{(j-q)!}
 A_{\mu,j+1}[g^{[j-q]}_\mu].
\tag{11}
\]
This avoids nested natural-number subtractions.

At zero field:
\[
\texttt{smoothCoeff}\ G\ h\ k\ 1\ 1\ \mu\ q
=
\frac1{q!}\sum_{r=q+1}^{M_\mu}
 \frac{(-1)^{r-q-1}\Gamma^{(r-q-1)}(\mu)}
 {(r-q-1)!}A_{\mu,r}[G].
\tag{12}
\]

The existing log-moment convention is consistent:
\[
\texttt{mellinMom}\ (\tau\mapsto e^{a\tau})\ \mu\ \ell
=(-1)^\ell\partial_s^\ell S(\mu,a).
\]
Meanwhile differentiating a complementary zeta integral gives
\[
\partial_s^\ell T(s)[G]\big|_\mu
=(-1)^\ell\,
 \texttt{faceCoeffInt}\ G\ h\ (2k)\ 1\ \mu\ \ell
\]
when the latter converges. These are separate sources of signs; neither should be silently absorbed.

### A3. Residues, measures and finite parts

#### Highest candidate polar coefficient in a chart

From (4),
\[
A_{\mu,M_\mu}[G]
=
\left(\prod_{j\in J_\mu}\frac1{2k_j\alpha_j!}\right)
\left(\bigotimes_{i\notin J_\mu}L_i(\mu)\right)
\left[\partial_{J_\mu}^{\alpha}G(0_{J_\mu},\cdot)\right].
\tag{13}
\]

The complementary operators are generally **finite parts**, not positive measures.

Thus the following unrestricted assertion would be false:

> “The highest polar coefficient under zero normal order is always the library’s residue measure.”

One also needs either:

- restriction to the shallow open set/admissible tests used by the library; or
- integrability across every complementary wall, as at the global leading pair.

For example, for \(h=0,\ k=(1,3)\), at \(\mu=1/2\) both coordinates resonate, but one resonance has positive normal order. At other nonminimal exponents, even zero-order residues in the resonant coordinates can have nonintegrable complementary weights.

#### Identification on the library’s shallow open set

On
\[
X_c=\texttt{stratumOpen}\ c
=U\setminus\texttt{deepZeroFibre}\ c,
\]
the pole order is at most \(c\). For smooth \(F\) vanishing near `deepZeroFibre c`,
\[
c^{\rm pop}_{\mu,c-1}(F)
=\frac{\Gamma(\mu)}{(c-1)!}A_{\mu,c}[F].
\]
Under `Ξ.ZeroOrder μ c`,
\[
\boxed{
A_{\mu,c}[F]
=\int_{X_c}F\,d(\texttt{Ξ.residueMeasure}\ Y\ hc\ hzero).
}
\tag{14}
\]
Equivalently,
\[
A_{\mu,c}[F]
=\frac{(c-1)!}{\Gamma(\mu)}
 \int_{X_c}F\,d(\texttt{Ξ.stratumMeasure}\ Y\ hc\ hzero).
\]

This follows directly from (*) at zero field and
`Grammar.SmoothEngine.ResolvedData.coeff_withF_eq_integral_stratumMeasure`.
The chart-density identification then uses
`Grammar.SmoothEngine.ResolvedData.chartResidueMeasure_eq_residueMeasure`.

There is **no sign** in (14), because \(A\) uses \((\mu-s)^{-r}\). In the standard Laurent convention the corresponding distribution is \((-1)^cA_{\mu,c}\).

#### A simple candidate pole

Assume exactly one coordinate \(i_0\) resonates with \(\mu\), with order \(\alpha\). Then
\[
\boxed{
A_{\mu,1}[G]
=\frac1{2k_{i_0}\alpha!}
 \operatorname{FP}\!\int_{(0,1]^{i_0^c}}
 \partial_{i_0}^{\alpha}G(0,w)\,
 w^{h-2k\mu}\,dw.
}
\tag{15}
\]

For one nonresonant complementary variable, with \(a=h_i-2k_i\mu\), choose \(p\) so \(a+p>-1\):
\[
\operatorname{FP}_a(g)
=\int_0^1
 \left(g(w)-\sum_{j<p}\frac{g^{(j)}(0)}{j!}w^j\right)w^a\,dw
+\sum_{j<p}\frac{g^{(j)}(0)}{j!(a+j+1)}.
\tag{16}
\]
Nonresonance ensures every displayed denominator is nonzero. Different sufficiently large \(p\) give the same value. Tensoring (16) defines the multivariable finite part, and the coordinate operators commute.

Equations (15), (*) give the paper’s population and empirical simple-pole formulas for **all** \(\alpha\), without a gap assumption. When all complementary exponents exceed \(-1\), (15) is an ordinary `faceCoeffInt ... 0`.

“Simple pole” here should mean **one local resonant coordinate**, or an independently proved distributional order bound one. A scalar pairing can have a simple pole through cancellation of a higher-order distributional pole; that alone does not imply (15).

#### Mandatory regression example

For \(h=0,\ k=(1,1),\ \mu=1/2\):
\[
A_{\mu,2}[G]=\frac14G(0,0),
\]
\[
A_{\mu,1}[G]
=\frac12\int_0^1\frac{G(x,0)-G(0,0)}x\,dx
+\frac12\int_0^1\frac{G(0,y)-G(0,0)}y\,dy.
\]
Hence
\[
c_{\mu,1}=A_{\mu,2}[GS_\mu(\zeta)],
\quad
c_{\mu,0}=A_{\mu,1}[GS_\mu(\zeta)]
-A_{\mu,2}[G\partial_sS(\mu,\zeta)].
\]
This tests all signs and factorials against `Grammar.SmoothEngine.tendsto_logExample`.

### A4. Global leading measure

#### Chart theorem

Assume `Grammar.BoxLeading h k lam m`, \(\lambda>0,\ m\ge1\). Let
\[
J=\{i:\lambda_i=\lambda\},\qquad j=|J|\le m.
\]
For a nonnegative smooth density amplitude \(a\), define
\[
\rho_{\lambda,m}^{a}=
\begin{cases}
\displaystyle
\left(\prod_{i\in J}\frac1{2k_i}\right)
(\iota_J)_*
 \left(a(0_J,w)\prod_{i\notin J}w_i^{h_i-2k_i\lambda}\,dw\right),
&j=m,\\
0,&j<m.
\end{cases}
\tag{17}
\]
This is a finite positive measure on the closed cube. Indeed, for \(i\notin J\),
\[
h_i-2k_i\lambda>-1.
\]
Its complementary coordinate boundary has measure zero.

For every continuous \(F,\zeta\) on the closed cube,
\[
\boxed{
N^\lambda(\log N)^{-(m-1)}
 \int_CaF\,u^h e^{-Nu^{2k}+\sqrt N u^k\zeta}\,du
\longrightarrow
\frac1{(m-1)!}\int_C F S_\lambda(\zeta)\,d\rho_{\lambda,m}^{a}.
}
\tag{18}
\]
For smooth tests, \(\rho_{\lambda,m}^{a}\) is exactly \(A_{\lambda,m}\) of the weighted zeta family.

Most of the asymptotic work in (18) already exists in `Grammar.tendsto_empBoxIntegral_div_boxFaceLimit`; the new work is its measure representation on the **closed face**, without deleting deeper corners.

#### Resolved theorem

Work first in the precise scope of `Grammar.SmoothEngine.ResolvedData`, not the paper’s general rectilinearised boundary domain. Let \(C_U=\pi^{-1}(\operatorname{tsupport}\varphi)\), which is compact. Assume
`Ξ.IsExtremalData lam m`, \(\lambda>0,\ m\ge1\).

There exists a finite positive measure \(\rho_{\lambda,m}\) on \(U\) such that:

1. It represents \(A_{\lambda,m}\) on all smooth resolved tests.
2. It is carried by the locus of \(m\) minimal walls, and
   \[
   \rho_{\lambda,m}(\texttt{Ξ.deepZeroFibre}\ m)=0.
   \tag{19}
   \]
   Its **topological support** can nevertheless meet that deeper set.
3. On `stratumOpen m`, it equals `residueMeasure` at \((\lambda,m)\).
4. If
   \[
   \nu_{\lambda,m}=\frac{\Gamma(\lambda)}{(m-1)!}\rho_{\lambda,m},
   \]
   then
   \[
   \boxed{
   \nu_{\lambda,m}
   =(\texttt{Subtype.val})_*
       (\texttt{Ξ.extremalStratumMeasure}\ Y\ h\ hm).
   }
   \tag{20}
   \]
5. For every smooth \(F:U\to\mathbb R\),
   \[
   N^\lambda(\log N)^{-(m-1)}
   \int_UF e^{-NK\circ\pi}\,d\mu_U
   \longrightarrow\int_UF\,d\nu_{\lambda,m}.
   \tag{21}
   \]
   In particular the old finite-mass inequality becomes equality, without a deep-empty hypothesis.

The “extension” in (20) is simply extension by zero as a measure. Since finiteness of `extremalStratumMeasure` is already proved, constructing that extension is easy. **The missing theorem is that no leading mass is lost on the deleted deeper set.** Finiteness alone does not establish this.

#### Assembly proof

Use an adapted finite normal-crossing cover near \(C_U\cap\{K\circ\pi=0\}\).

- At a point of the zero fibre, extremality bounds all wall ratios and the number of minimal walls.
- Shrink to a centred chart with exactly those local wall data.
- Apply (17) in each permitted orthant, including tangential variables.
- Sum the finite positive face measures with the nonnegative partition weights.
- A complementary wall is nonminimal; its exponent is greater than \(-1\), and its zero set is null for the face measure. This proves (19).
- Sum (18), and discard the phase-gap tail.
- Identify the restriction with `residueMeasure` by smooth-test uniqueness.
- Identify the full measure by (19), giving (20).
- Independence of the adapted cover follows from the leading coefficient functional on **all** smooth tests.

There is an implementation distinction:

> `Ξ.IsExtremalData lam m` is intrinsic and support-truncated.  
> `Ξ.ChartLeading Y lam m` constrains every box in the particular transport.

Do not claim that the former implies the latter for an arbitrary supplied `Y`. Some boxes can contain irrelevant walls outside the prior support. Either construct an adapted transport, or localise the existing amplitudes further. Under `ChartLeading`, the existing `hasLeadingTerm_empZ` supplies the global limit immediately; only measure identification remains.

#### Branchwise empirical version

On a branch presentation \(B\), let \(p:B\to U\), \(\rho_B\) be the one-sided residue measure, and \(\zeta_B\) the continuous branch field. Then
\[
N^\lambda(\log N)^{-(m-1)}Z_N[F;\psi]
\longrightarrow
\frac1{(m-1)!}\int_B(F\circ p)S_\lambda(\zeta_B)\,d\rho_B.
\tag{22}
\]
Its population pushforward satisfies \(p_*\rho_B=\rho_{\lambda,m}\).

In general (22) **cannot** be written as reweighting \(\rho_{\lambda,m}\) by a single trace of \(\psi\) on \(U\). The branch label is necessary.

### Resolved continuation and invariance

For arbitrary smooth resolved tests,
\[
\widetilde T(s)[F]=\int_UF(K\circ\pi)^{-s}\,d\mu_U
\]
continues by finite chart assembly. The phase-gap tail is entire: on its compact support, \(K\circ\pi\) is bounded above and bounded away from zero.

Its polar coefficients satisfy the corresponding resonance-support statement. Pushforward gives
\[
T(s)[f]=\widetilde T(s)[f\circ\pi],
\qquad
A^{\rm downstairs}_{\mu,r}[f]
=A^{U}_{\mu,r}[f\circ\pi].
\tag{23}
\]
These identities follow first on the convergence half-plane and then by uniqueness of continuation.

For orthantwise amplitudes, assemble on a branch presentation rather than pretending they are smooth functions on \(U\). Compatibility/invariance is asserted for representatives of the **same off-divisor field**. Arbitrary unrelated orthant fields define different tilted integrals.

---

## B. Formalisation route

All names below not already in the supplied closure are **proposed declarations**, not claims that they exist. The snippets are Lean-like interfaces; I have not compiled against the repository.

### Interface choice

Use scalar meromorphic pairings plus explicit finite-seminorm bounds first. Avoid starting with:

- a general distribution-valued meromorphic-function API;
- a Fréchet-space analytic-function library;
- a manifold-with-corners formalisation.

Those can be wrappers around the proved scalar/finite-order results.

Keep `polarCoeff`, `polarPart`, `principalParts`, `empCoeff`, `smoothCoeff` and their definitions unchanged.

### Ordered units

#### 1. `Grammar/PolarAmplitudeAlgebra.lean` — start here

**Purpose:** isolate every sign, factorial and finite-sum identity before analysis.

Import `Grammar.PrincipalPartUniqueness`. Define, for raw derivative pairings `a : ℕ → ℕ → ℂ`:
```lean
def polarAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico q (D + 1),
    (-1 : ℂ) ^ (j + 1) * a j (j - q) /
      ((j - q).factorial : ℂ)

def logAmplitudeCoeff (D : ℕ) (a : ℕ → ℕ → ℂ) (q : ℕ) : ℂ :=
  (1 / (q.factorial : ℂ)) *
    ∑ j ∈ Finset.Ico q (D + 1),
      (-1 : ℂ) ^ (j - q) * a j (j - q) /
        ((j - q).factorial : ℂ)
```
Here `a j ℓ` means \(A_{\mu,j+1}[\partial_s^\ell g(\mu)]\).

Prove:
```lean
theorem polarAmplitudeCoeff_eq :
  polarAmplitudeCoeff D a q =
    (-1 : ℂ) ^ (q + 1) * (q.factorial : ℂ) *
      logAmplitudeCoeff D a q
```

Define
\[
P_j(s)=\sum_{\ell=0}^{D}a_{j,\ell}(s-\mu)^\ell/\ell!.
\]
For \(s\ne\mu\), prove the exact identity
\[
\sum_{j=0}^D\frac{P_j(s)}{(\mu-s)^{j+1}}
-\texttt{polarPart}\ D\
    (\texttt{polarAmplitudeCoeff}\ D\ a)\ \mu\ s
=
\sum_{j=0}^D\sum_{\ell=j+1}^D
 \frac{(-1)^{j+1}a_{j,\ell}}{\ell!}
 (s-\mu)^{\ell-j-1}.
\tag{24}
\]
The right side is polynomial.

Add:

- zero-padding/order-bound lemmas;
- `q = D` and `D = 1` simplifications;
- a real-data coercion lemma relating the result directly to `polarCoeff`.

**Proof:** split pairs \((j,\ell)\) by \(\ell\le j\), reindex \(q=j-\ell\), use `pow_add`, factorial nonzero, and field simplification only under `s ≠ μ`.

**Estimate:** 300–450 lines. This unit has no new analytic infrastructure and is independently useful.

#### 2. `Grammar/ComplexCubeTaylor.lean`

**Statement:** complex-linear versions of the coordinate Taylor decomposition, `faceAmp`, rectangular remainder estimate, and face-split identity.

**Reuse:** `SmoothCoordTaylor`, `SmoothFaceOperators`, `SmoothFaceSplit`.

**New definitions:** complex counterparts implemented componentwise from real and imaginary parts, unless the existing derivative lemmas generalise cheaply.

**Proof:** real/imaginary decomposition; the same rectangular bounds with a harmless factor two.

**Estimate:** 350–550 lines.

**Generalisation policy:** generalise elementary derivative/linearity lemmas in place where they are genuinely codomain-polymorphic. Do not change the codomain of `smoothCoeff` or `empCoeff`, or force a broad refactor through all 897 modules.

#### 3. `Grammar/ChartZetaStrip.lean`

```lean
def chartZeta (G : (Fin d → ℝ) → ℂ)
    (h k : Fin d → ℕ) (s : ℂ) : ℂ := ...

theorem integrable_chartZeta ...
    (hs : ∀ i, 2 * k i * s.re < h i + 1) : ...

theorem differentiableOn_chartZeta ...
```

**Reuse:** `box`, monomial power integrability, product/Fubini machinery.

**New:** complex weight defined using `Complex.exp` and real logs on the positive box; avoid branch ambiguity from arbitrary complex bases.

**Proof:** product domination on compact substrips, differentiated integrand with log factors.

**Estimate:** 350–550 lines.

#### 4. `Grammar/ChartZetaRegularization.lean`

```lean
def chartZetaAtDepth (p : Fin d → ℕ) ... (s : ℂ) : ℂ := ...

theorem chartZetaAtDepth_eq_chartZeta ...
theorem chartZetaAtDepth_holomorphic_after_denominators ...
theorem chartZetaAtDepth_compatible ...
```

**Reuse:** units 2–3; `faceIndex`, `faceW`, Taylor-remainder bounds.

**New:** expression (3).

**Proof:** Fubini on the initial half-plane; dominated holomorphy of flat-complement integrals; compatibility by identity theorem.

**Estimate:** 450–600 lines.

#### 5. `Grammar/ChartZetaPolar.lean`

```lean
def chartPolarFunctional (h k : Fin d → ℕ)
    (μ : ℝ) (r : ℕ) : SmoothCubeAmplitude d ℂ →ₗ[ℂ] ℂ := ...

theorem chartZeta_sub_polar_holomorphic ...
theorem chartPolarFunctional_eq_zero_of_order_gt ...
theorem chartPolarFunctional_bound ...
```

**Reuse:** unit 4, local Laurent/Taylor extraction, `polarPart` uniqueness where convenient.

**New:** a smooth-amplitude submodule; explicit finite-jet seminorm; positive-\(\mu\) polar functionals, with zero outside \(1\le r\le M_\mu\).

**Proof:** multiply by the candidate pole power, Taylor-expand the resulting holomorphic function; Cauchy bounds and uniqueness.

**Estimate:** 450–600 lines.

The continuation can be exposed as compatible depth expressions rather than a globally selected function at poles. Its values *at* poles have no mathematical role.

#### 6. `Grammar/ChartZetaPolarSupport.lean`

```lean
theorem chartPolarFunctional_eq_zero_of_eventually_zero_resonant ...
theorem chartPolarFunctional_real ...
theorem chartPolarFunctional_congr_jets ...
```

**Reuse:** unit 5 and coordinate localisations; the ideas in `SmoothJetDetermination` and `SmoothResonantSupport`.

**New:** chart resonance locus; a safe rectangular jet-equality relation along resonant walls.

**Proof:** local pole-order bound away from the resonance superlevel set; compact partition/locality; conjugation; finite Taylor representation.

**Estimate:** 350–550 lines.

Do not state a lower-pole analogue of `coeff_eq_of_memIdealPow` on one `exactStratum`; that is generally false.

#### 7. `Grammar/HolomorphicCubeFamily.lean`

**Statement:** uniform spatial-jet holomorphy implies a Taylor expansion in \(s\), with a holomorphic remainder controlled in the required finite-jet seminorm.

**New:** `HolomorphicCubeFamily` with spatial derivatives jointly continuous and holomorphic in the complex parameter.

**Reuse:** unit 2, scalar Cauchy/Taylor theory, compactness.

**Proof:** Cauchy integral on one common circle, uniformity over the cube and finitely many derivatives.

**Estimate:** 400–600 lines.

This is a genuine infrastructure unit. Do not hide it inside the empirical theorem.

#### 8. `Grammar/ChartZetaHolomorphicAmplitude.lean`

```lean
theorem chartZeta_family_sub_polar_holomorphic
    (g : HolomorphicCubeFamily ...) : ...
```

**Reuse:** units 1, 5, 7.

**New:** the polar coefficient array of a family.

**Proof:** Taylor in the finite-jet topology; multiply the remainder by the pole-killing power; use (24).

**Estimate:** 250–400 lines.

#### 9. `Grammar/ComplexFluctuation.lean`

```lean
def complexFluctuation (s : ℂ) (a : ℝ) : ℂ := ...

theorem complexFluctuation_ofReal ...
theorem complexFluctuation_hasDerivAt ...
theorem complexFluctuation_indexDeriv_ofReal ...
```

**Reuse:** `fluctuation`, `mellinMom`,
`mellinMom_pow_mul_exp_eq_iteratedDeriv`.

**New:** complex-index radial integral.

**Proof:** the uniform majorants in (6); comparison with the existing real-index derivatives.

**Estimate:** 400–600 lines.

Do not generalise the existing real `fluctuation` definition in place.

#### 10. `Grammar/FluctuationAmplitudeFamily.lean`

```lean
theorem holomorphicCubeFamily_mul_complexFluctuation
    (hG : ContDiff ℝ ∞ G) (hζ : ContDiff ℝ ∞ ζ) : ...

theorem fluctuationIndexJet_locallyLipschitz ...
```

**Reuse:** unit 9, `JetCloseness`, `EmpiricalFieldJets`.

**New:** real index-derivative amplitudes and mixed spatial/index derivative formulas.

**Proof:** differentiated integral, finite spatial chain-rule expressions, uniform radial envelopes.

**Estimate:** 350–550 lines.

#### 11. `Grammar/EmpiricalChartMellin.lean`

```lean
theorem mellin_empIntegral_eq_chartZeta ...
theorem empIntegral_locallyIntegrable ...
theorem empIntegral_isBigO_one_at_zero ...
```

**Reuse:** `empIntegral`, units 3 and 9; bridge-style Mellin substitution, but no greybook dependency.

**New:** none beyond adapters.

**Proof:** absolute Fubini and radial substitution; compact amplitude/field bounds.

**Estimate:** 350–550 lines.

#### 12. `Grammar/EmpiricalPolarCoefficients.lean`

```lean
theorem polarCoeff_empCoeff_eq_polarAmplitudeCoeff ...
theorem empCoeff_eq_chartPolar_sum ...
theorem smoothCoeff_eq_chartPolar_gamma_sum ...
```

The central real statement should have the form:
```lean
empCoeff G ζ h k μ q =
  1 / (q.factorial : ℝ) *
    ∑ j ∈ Finset.Ico q d,
      (-1 : ℝ) ^ (j - q) / ((j - q).factorial : ℝ) *
        chartPolarReal h k μ (j + 1)
          (fun u => G u *
            iteratedDeriv (j - q)
              (fun ν => fluctuation 1 ν (ζ u)) μ)
```
with the relevant smoothness, positivity and lattice/range hypotheses.

**Reuse:** `emp_cutoffExpansion`, `CutoffExpansion`,
`mellinContinuation`, `principalParts`, `polarCoeff_unique`, units 8–11.

**Proof:** continuation equality by the identity theorem; bounded polar remainder; uniqueness; algebra from unit 1.

**Estimate:** 400–600 lines.

#### 13. `Grammar/ChartPolarFinitePart.lean`

```lean
def finitePartPower ...
theorem finitePartPower_independent_depth ...
theorem chartPolar_one_resonant ...
theorem chartPolar_top_eq_faceIntegral_of_gap ...
```

**Reuse:** units 4–5, `faceCoeffInt`, `resOrder`, `faceW`.

**New:** finite-part operator (16).

**Proof:** telescoping Taylor subtractions; coordinate commutation; take residues in (1).

**Estimate:** 400–600 lines.

#### 14. `Grammar/PolarTwoDimExamples.lean`

**Statement:** the explicit \(A_{1/2,2}\), \(A_{1/2,1}\), and variable-field two-dimensional coefficient formulas.

**Reuse:** units 12–13; `tendsto_logExample`.

**New:** only example data and readable integral wrappers.

**Proof:** two one-variable Laurent expansions; (*) and simplification.

**Estimate:** 250–400 lines.

This is a mathematical regression test, not merely exposition.

#### 15. `Grammar/ResolvedZetaFunctional.lean`

```lean
def ResolvedData.zetaPairing ...
def ResolvedData.polarFunctional ...
theorem ResolvedData.polarFunctional_eq_of_transports ...
theorem ResolvedData.polarFunctional_comp_gv ...
```

**Reuse:** `ResolvedData`, `ResolvedCoreTransport`, `withF`, `decomp`, units 4–6.

**New:** finite-base integrated zeta expressions and phase-gap tail.

**Proof:** parameter-uniform bounds, finite integration/assembly, identity on the initial half-plane.

**Estimate:** 450–600 lines.

Retain positive phase constants: a piece with phase \(c\,u^{2k}\) contributes \(c^{-s}\). Either use the transport’s established unit-normalisation theorem or carry this factor explicitly.

#### 16. `Grammar/ResolvedPolarStratum.lean`

```lean
theorem ResolvedData.polarFunctional_eq_integral_residueMeasure ...
theorem ResolvedData.polarFunctional_eq_zero_of_eventually_zero_resonant ...
```

**Reuse:** unit 15,
`coeff_withF_eq_integral_stratumMeasure`,
`chartResidueMeasure_eq_residueMeasure`,
`coeff_eq_zero_of_eventually_zero_resonant`.

**New:** no new measure definitions.

**Proof:** triangular population formula (12), descending induction if needed; graded top identity for admissible tests.

**Estimate:** 300–500 lines.

#### 17. `Grammar/EmpiricalResolvedPolar.lean`

```lean
theorem ResolvedData.SmoothRootField.resolvedCoeff_eq_polar_sum ...
```

**Reuse:** unit 12 piecewise, unit 15, `SmoothRootField`,
`resolvedCoeff`, `pieceCoeff`.

**New:** branchwise polar pairing with holomorphic amplitude families.

**Proof:** sum/integral interchange under uniform finite-order bounds; rectangle scaling; trace compatibility on open boxes.

**Estimate:** 350–550 lines.

This is not multiplication of an ordinary distribution on \(U\) by a discontinuous function.

#### 18. `Grammar/LeadingFaceMeasure.lean`

**Statement:** finite closed-face version of (17), its integral formula, boundary-null property, and identification with `boxFaceLimit`.

**Reuse:** `BoxLeading`, `resSet`, `faceFunctional`,
`tendsto_empBoxIntegral_div_boxFaceLimit`, `residueWeight`.

**New:** closed-face measure including a nonnegative amplitude.

**Proof:** product power integrability; pushforward; boundary nullity; rewrite the existing face functional.

**Estimate:** 350–550 lines.

This unit can proceed in parallel with units 2–17.

#### 19. `Grammar/ResolvedLeadingMeasureChart.lean`

```lean
def ResolvedData.leadingResidueMeasureU ...
theorem ..._finite ...
theorem ..._deepZeroFibre_eq_zero ...
theorem hasLeadingTerm_empZ_eq_integral_leading ...
```

Initially assume `Ξ.ChartLeading Y lam m`.

**Reuse:** unit 18, `faceMeasureU`, `faceDensity`,
`hasLeadingTerm_empZ`, `pieceFaceLimit`.

**New:** finite sum of **unrestricted** `faceMeasureU`, and its branch-weighted empirical analogue.

**Proof:** identify selected faces with the complete minimal-coordinate set; integrate base variables; use the existing global leading theorem.

**Estimate:** 400–600 lines.

#### 20. `Grammar/ResolvedExtremalLocalisation.lean`

**Statement:** intrinsic `IsExtremalData` suffices for the global measure representation, without assuming an arbitrary existing transport is `ChartLeading`.

**Reuse:** centred charts, compactness of `zeroFibre`, unit 19’s local argument, intrinsic coefficient uniqueness.

**New:** an adapted local leading-cover certificate, preferably weaker than a whole new `ResolvedCoreTransport`.

**Proof:** finite supported localisation near the zero fibre; wall-data comparison; discard the phase-gap complement; sum local measures.

**Estimate:** 450–600 lines **if** the existing chart-localisation API supplies the needed cover. Otherwise split into a separate cover-construction file and an assembly file. This is the main unresolved size dependency.

#### 21. `Grammar/SmoothGlobalLeadingMeasure.lean`

```lean
def ResolvedData.globalExtremalStratumMeasure ... :=
  (Ξ.extremalStratumMeasure Y h hm).map Subtype.val

theorem coeff_eq_integral_globalExtremalStratumMeasure ...
theorem tendsto_normalised_partitionObs_extremal_all ...
theorem extremalStratumMeasure_univ_eq ...
```

**Reuse:** units 19–20, `extremalStratumMeasure`,
`eq_stratumMeasure_of_tests`,
`tendsto_normalised_partitionObs_extremal`.

**Proof:** restriction identity plus no mass on `deepZeroFibre`; smooth leading coefficient limit; mass equality with \(F=1\).

**Estimate:** 250–450 lines.

**In-place change:** after this lands, strengthen
`Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal`
by removing `h0`, preserving the old result as a wrapper if API compatibility matters. Do not change the type of `extremalStratumMeasure`.

#### 22. `Grammar/CompactLeadingBranches.lean`

**Statement:** construct an atlas-dependent compact metric presentation sufficient for the compact-base Gaussian theory.

**New:**
```lean
def LeadingBranchSpace :=
  Σ p, Σ J : selectedLeadingFaces p,
    Base ... × closedComplementaryFace ...

def branchResidueMeasure : Measure LeadingBranchSpace
def branchProjection : LeadingBranchSpace → Ξ.R.U
def RootField.branchTrace : C(LeadingBranchSpace, ℝ)
```

**Reuse:** `faceRef`, `faceDensity`, `faceMap`, `RootField.loc_cont`, unit 18.

**Proof:** finite disjoint union of compact boxes; finite measure; continuity of traces and projection on the chart boxes; integral formula (22).

**Estimate:** 400–600 lines.

Retain partition weights in the measure. Duplicate chart points are intentional.

#### 23. `Grammar/LeadingBranchGibbs.lean`

```lean
theorem leadingPosterior_eq_compactAvg ...
theorem branchPresentation_independent ...
```

**Reuse:** unit 22, `compactD`, `compactAvg`, `gibbsJoint`, leading ratio theorem.

**New:** observable pullback to branch space.

**Proof:** cancel the common \((m-1)!\); compare presentations through the same frozen leading integrals.

**Estimate:** 200–350 lines.

A Gaussian-field instance still requires a jointly compatible process limit on this compact presentation. Compactness does not prove that statistical hypothesis.

#### 24. `Grammar/EmpiricalAllLogContinuity.lean`

**Statement:** every fixed \((\mu,q)\) coefficient is locally Lipschitz in sufficiently many cube/branch jets, without depth admissibility.

**Reuse:** (*), finite-seminorm bounds for \(A_{\mu,r}\), unit 10, `JetCloseness`, `BranchJetSpace`.

**New:** all-log coefficient maps on realizable/closed realizable jets.

**Proof:** finite sum of continuous finite-order functionals applied to locally Lipschitz composition maps.

**Estimate:** 350–550 lines; resolved probability packaging can be a further 250–400-line file.

**In-place policy:** add stronger general results, then make
`exists_resolvedCoeff_top_bound` and the existing top-coefficient convergence theorem corollaries. Do not merely delete their admissibility hypotheses before this proof exists.

### Scope and estimate

The full route is approximately **9–13 kLOC**, depending especially on complex Taylor infrastructure and adapted localisation. The algebraic centre is small; the analytic interfaces are not.

A practical sequence is:

1. unit 1;
2. units 2–12, with unit 14 as the first complete coefficient milestone;
3. units 18–23 in parallel;
4. resolved continuation/assembly;
5. all-log continuity;
6. optional intrinsic manifold-with-corners geometry.

---

## C. Risks and what to prove first

### 1. Two-variable continuation: standard, but the interface is substantive

There is no joint holomorphic continuation in the real spatial variable \(u\), nor is one needed. The required statement is:

> holomorphic in \(s\), smooth in \(u\), with locally uniform control of finitely many spatial derivatives.

The main danger is proving only scalar holomorphy for fixed amplitudes and then substituting \(g(s,\cdot)\) without proving finite-topology Taylor remainder control.

**De-risk:** prove units 7–8 in one dimension before general chart assembly. Test \(g(s,u)=g_0(u)+(s-\mu)g_1(u)\) at a double pole.

### 2. The library already has the general empirical leading limit

`Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ` has **no test-support restriction**. The restriction occurs in `hasLeadingTerm_empZ_eq_integral`.

Thus the missing leading theorem is largely a **global measure identification**, not a new asymptotic theorem.

**De-risk:** unit 18 followed by unit 19 under `ChartLeading`. This should deliver a useful all-observable theorem before solving intrinsic support-localisation.

### 3. Intrinsic extremality versus arbitrary transport

This is the largest geometric proof risk. `IsExtremalData` only inspects the support-truncated zero fibre. It need not constrain irrelevant box walls.

**De-risk:** inspect the exact support and chart-centre lemmas in `ResolvedCoreTransport` before committing to a three-file estimate for F5. Prefer a local cover certificate to reconstructing the entire transport.

### 4. Orthant signs

On a signed chart, with signed-root field \(\xi\), the positive-box absolute-root representative is
\[
\zeta_\sigma(v)=
\left(\prod_i\sigma_i^{k_i}\right)\xi(\sigma v).
\]
For normal derivatives,
\[
\partial_v^\alpha(G\circ R_\sigma)
=\left(\prod_i\sigma_i^{\alpha_i}\right)
 (\partial^\alpha G)\circ R_\sigma.
\]
The Jacobian density carries absolute values and no orientation sign.

**De-risk:** prove these adapters using `WaterFilling.sgn`, `WaterFilling.refl`, `signReflect`, and `pdMulti_comp_affineMap`. Test:

- \(K=x^2\), signed constant field \(a\), branches \(a,-a\);
- \(K=x^4\), signed constant field \(a\), both branches \(a\);
- \(K=x^2y^2\), four branches \(\sigma_x\sigma_y a\).

The second test prevents an incorrect universal “opposite signs on the two sides” rule.

### 5. Branch-space compactness

The real oriented blow-up of the ambient resolved manifold along a simple normal-crossing divisor is standard geometry. But:

- its restriction over an arbitrary smooth prior’s closed support need not itself be a manifold with corners;
- global wall labels can have transition permutations and normal-line twisting;
- a quotient of chart boxes requires Hausdorffness and compatibility proofs;
- the supplied Lean development does not provide that infrastructure.

**Recommendation:** first use the finite disjoint union of closed leading-face parameter spaces. It is compact, metrizable and sufficient for `compactAvg`, `gibbsJoint`, and `GaussianField`. It is an **atlas-dependent compact branch presentation**, not an intrinsic oriented blow-up.

An intrinsic cut-open resolution can be a later geometric theorem. It should not block the leading Gaussian application.

### 6. Lower-pole jet claims

The old exact-stratum ideal-power theorem cannot simply be generalised to every \(r\).

For \(x^2y^2\), \(A_{1/2,1}\) sees values along the axes. An amplitude \(G=x^2\) vanishes at the crossing but gives \(A_{1/2,1}[G]\ne0\). Crossing jets do not determine it.

**De-risk:** state and prove a conservative finite rectangular jet bound along the whole resonant divisor first. Keep exact-stratum descent as an associated-graded theorem.

### 7. Statistical variance two

The proposed variance-two lemma requires a quantitative likelihood-normalisation remainder. A sufficient hypothesis is a locally uniform exponential moment for \(a(X,u)\), strong enough that
\[
\mathbb E\!\left[
 e^{-v a}-1+v a-\frac{v^2a^2}{2}
\right]=o(v^2),\qquad v=u^k.
\]
Together with \(\mathbb Ea=v\), this yields \(\mathbb Ea^2\to2\). Continuity of the second moment then gives variance \(2\) on the divisor.

This belongs in the greybook bridge, with the moment hypotheses explicit. It is independent of the polar-distribution implementation.

---

## D. Corrections to the plan and the corrected paper

### Corrections to the draft plan

1. **Fix the recalled `polarCoeff` sign.** It is \((-1)^{q+1}q!\).
2. **`fluctuation` is not complex-index in the supplied closure.** Add `complexFluctuation`; reuse the real function through comparison lemmas.
3. **Do not identify every highest polar coefficient with a residue measure.** Formula (14) is restricted to the shallow open set; the unrestricted measure statement is protected by extremality or complementary integrability.
4. **Do not generalise `coeff_eq_of_memIdealPow` mechanically to all polar orders.** Lower orders require the whole stratified resonant locus, not one exact stratum.
5. **F5 is not “construct an extension”.** A finite zero-extension already exists. Prove equality with the full leading functional and zero mass on the deleted deeper fibre.
6. **Use `hasLeadingTerm_empZ` rather than reproving its limit.**
7. **Separate `IsExtremalData` from `ChartLeading`.** Add the adapted-localisation step explicitly.
8. **Move a compact branch presentation earlier; defer the intrinsic oriented blow-up.** The former completes the compact-base interface at much lower cost.
9. **Use `polarCoeff_unique` for the identification.** Avoid an independent proof that the complicated face construction equals the new Laurent formula.
10. **Do not change the lattice denominator during this project.** An lcm adapter is harmless later, but replacing `Qamb` adds migration work unrelated to the mathematics.

### Remaining paper issues

#### 1. “The highest polar coefficient is positive” needs extremality

The rewritten theorem must distinguish:

- the highest candidate polar coefficient at an arbitrary \(\mu\), possibly a differentiated finite-part distribution;
- the restricted zero-order residue measure on \(X_c\);
- the global leading positive measure.

These are different assertions.

#### 2. The leading measure remains carried by the exact stratum, but its support can meet deeper points

At the extremal pair the deeper nonminimal intersections have **zero measure**, although every neighbourhood can have positive mass. Say “carried by” or “concentrated on” the exact stratum, and reserve “support” for its closed topological support.

For \(x^2y^6\), the extended \(x^{-1/3}dx\) measure gives the origin mass zero but has the origin in its support.

#### 3. The claimed ideal quotient in the graded section is too strong

The sentence
> “The summed coefficient … descends to a functional on \(\mathcal I_{c+1}/\mathcal I_c\)”

is valid as a quotient by observables vanishing near depth \(c\), but it is not the same as the transverse-jet quotient later constructed. Make the distinction explicit; the quotient does not by itself encode the normal-order bound.

More generally, replace broad “one stratum” coefficient descriptions by the polar-distribution statement, retaining the exact-stratum formula only under its admissibility hypothesis.

#### 4. Smooth prior vanishing is not generally encoded by an integer divisor

The resolution section says that a prior vanishing along \(W_0\) changes \(h_i\). For an arbitrary smooth prior this is only true under an additional finite monomial-order factorisation. A smooth prior may be flat or vanish on a nonanalytic set.

Under the paper’s principal hypothesis that the prior is positive near \(W_0\), this issue does not arise. State the vanishing-prior observation conditionally.

#### 5. Individual normal vanishing orders do not always give a nonzero joint leading normal coefficient

The implication
\[
\text{“order }l_i\text{ along each }E_i”\quad\Rightarrow\quad
f=\prod_i u_i^{l_i}\widetilde f,\quad
\widetilde f|_{S_I}\not\equiv0
\]
is not automatic. For instance \(f=x^2+y^2\) has generic wall order zero along both coordinate axes, but its restriction to their crossing is zero.

The displayed factorisation with nonzero stratum trace is a stronger hypothesis and should be labelled as such. Vanishing orders provide candidate bounds; they do not classify arbitrary smooth amplitudes near a crossing.

#### 6. Boundary rectilinearisation needs consistent resolution scope

The appendix alternates between:

- an isomorphism off \(\{K=0\}\);
- simultaneous boundary resolution that may modify points outside \(\{K=0\}\).

Use the latter consistently when discussing general domains. Boundary-only exceptional components can carry Jacobian orders while having phase order zero. They are parameters for the chart asymptotics, but they cannot simply disappear from the full Jacobian normal form.

The existing assembled `ResolvedData` theorem remains the interior-support theorem stated in the coverage table.

#### 7. The empirical Mellin integral downstairs needs a descended field

In `eq:fluctuation_zeta`, \(\psi\) was defined on \(U\), while the integral is written over \(W\). Either:

- write the integral upstairs/branchwise; or
- explicitly define the off-zero descended field on \(W\setminus W_0\).

Its arbitrary values on \(W_0\) do not determine branch traces.

#### 8. A meromorphic continuation alone does not imply the expansion

Some explanatory sentences say the poles “determine the expansion” without specifying the analytic input. Here the clean proof is:

- expansion from the existing smooth engine;
- Mellin regularisation;
- equality of continuations;
- uniqueness of polar coefficients.

No Mellin inversion theorem is needed. The rewritten proof should say this.

#### 9. Replace the moving-right-hand-side arrow

The corrected prose explains the intended meanings, but the displayed
\[
\mathbb E[f\mid D_n]\longrightarrow\langle f\rangle_{\hat\psi_n}
\]
is still misleading. Replace it by the three separate frozen, diagonal-error, and Gaussian-law statements.

Also, the frozen leading posterior formula holds for **every** smooth observable, including those with zero leading numerator. “Not identically zero on the leading stratum” is neither necessary nor sufficient for a nonzero leading average of a signed observable.

#### 10. The formalisation limitations overstate the strip gap

The supplied bridge list already contains
`fluctuationZeta_eq_mellinContinuation_of_bounded_std`
and `isFrozenCoeff_polarCoeff_unique_of_bounded`, with strip hypotheses derived. The “What is not proved” bullet saying strip convergence is simply assumed needs to be reconciled with that coverage.

The proposed chart Mellin theorem removes any need for a Watanabe-specific strip-convergence assumption in the deterministic smooth theory.

#### 11. Some scalar pole statements should say “possible”

The Gamma factor has possible poles at nonpositive integers; individual amplitude pairings can cancel them. Likewise the continued \(S_s(a)\) has possible nonpositive half-integer poles, with cancellations for special \(a\), notably \(a=0\). Avoid asserting every listed point is an actual pole.

#### 12. The principal leading extension paragraph is now mathematically correct

The earlier review’s complaint about infinite leading mass has already been repaired in the supplied paper. Retain its integrability argument, but replace the “derivation, not pinned” qualification once units 18–21 land. The stronger conclusion is exact total-mass equality even when `deepZeroFibre m` is nonempty.

---

**Immediate action:** implement `Grammar/PolarAmplitudeAlgebra.lean` with (24), then run the double-pole regression. In parallel, implement the closed-face measure of unit 18. These two small deliverables test the two most consequential parts of the reorganisation—every coefficient’s normalisation, and the genuinely global leading measure—without committing first to a large distribution or manifold-with-corners abstraction.