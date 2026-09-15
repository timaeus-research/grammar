## Recommendation

Proceed with the graded project, with two important corrections:

1. **The single-Taylor-order assertion is valid for the top logarithm of a face, not for arbitrary coefficients of that face.**
2. **For higher normal orders, the intrinsic object is the coefficient functional restricted away from deeper strata—not a separately canonical scalar density multiplying a canonically defined normal derivative.**

With those corrections, E1–E3 give a clean, useful theorem without regularisation. Prove the explicit top-face constant: it is inexpensive relative to the assembly and makes the resulting statement substantially more informative.

## 1. First gate: correct the resonance assertion

The parenthetical assertion
> `faceCoef … μ j ≠ 0` forces every coordinate of `J` to resonate at `μ`

is too strong for ordinary monomial Mellin coefficients. Each coordinate supplies one possible pole; the poles form a **union**, and coincident poles determine logarithmic multiplicity.

For example,
\[
\int_0^1\!\int_0^1 y^2e^{-Nx^2y^2}\,dx\,dy
=\frac12\int_0^1(1-t^2)e^{-Nt^2}\,dt
\sim \frac{\sqrt\pi}{4}N^{-1/2}
-\frac{\sqrt\pi}{8}N^{-3/2}.
\]
The two coordinate ratios are \(1/2\) and \(3/2\), but both exponents contribute.

The assertion you need, and which follows from the supplied resonant-count theorem, is:
\[
\operatorname{faceCoef}(J,e;\mu,|J|-1)\ne0
\quad\Longrightarrow\quad
2k_j\mu=e_j+1\quad\text{for every }j\in J.
\]
Indeed, otherwise the resonant count is at most \(|J|-1\).

Consequently, **after** killing faces larger than \(c\) and selecting \(q=c-1\), a surviving size-\(c\) face has exactly one possible Taylor multi-order:
\[
\alpha_j=2k_j\mu-h_j-1\in\mathbb N.
\]
That is exactly the integer in `Resonates`.

This correction does not damage E1. It does affect how the full, lower-logarithmic expansion should be described.

## 2. The right intrinsic formulation

Write
\[
D_c:=Z_0\cap\{\operatorname{depth}\ge c\},\qquad
S^\mu_c:=Z_0\cap\{\operatorname{depth}=c,\ r_\mu=c\},
\]
and, within the existing admissible observable space, put
\[
\mathcal I_c
:=\{F:F=0\text{ on some neighbourhood of }D_c\}.
\]

The primary object should be
\[
\left.\mathcal T^U_{\mu,c-1}\right|_{\mathcal I_{c+1}}.
\]

Equivalently, work on the open manifold
\[
V_c:=U\setminus D_{c+1}.
\]
On compactly supported tests in \(V_c\), this coefficient is supported on \(S^\mu_c\) and admits the convergent face-integral formula below.

There is also a genuine graded formulation:
\[
\mathcal I_c\subseteq\mathcal I_{c+1},
\qquad
\mathcal T^U_{\mu,c-1}|_{\mathcal I_c}=0,
\]
so the functional descends to
\[
\mathcal I_{c+1}/\mathcal I_c.
\]
This is the precise, choice-free meaning of “canonical modulo deeper strata.”

### What is canonical?

- The restricted functional and its induced graded functional are canonical.
- Its **sum** of chart-piece normal-jet integrals is independent of the normal-crossings presentation.
- Individual higher-jet densities and individual coordinate normal derivatives need not be canonical separately.
- When all contributing normal orders are zero, the functional is represented by an intrinsic positive density/measure on the resonant stratum.

Thus I would call the project **“graded stratum formulas for resolved coefficient functionals.”** Avoid promising canonical higher-jet kernels before proving their transformation laws.

## 3. Exact hypotheses and engine theorem

### Engine hypotheses

Use the existing engine admissibility package, but make the following requirements visible:

1. \(c\ge1\), with \(c\le d\) for the nonvacuous formula.
2. The coordinates indexed by \(J\) and counted for depth are **active divisor coordinates**. Inactive/base coordinates are not counted.
3. \(k_i>0\), \(b_i>0\), \(\beta>0\), and the existing admissible Jacobian exponents—typically \(h_i\in\mathbb N\).
4. The amplitude \(A\) is smooth on a neighbourhood of the relevant closed box.
5. \(A\) vanishes near
   \[
   H_{c+1}:=\{v:\text{at least }c+1\text{ active coordinates vanish}\}.
   \]
   A finite-jet hypothesis could suffice, but smooth neighbourhood vanishing is the clean interface.
6. The Taylor depth \(p\) is certified for the target coefficient and includes every relevant resonant order:
   \[
   \alpha_i<p_i
   \]
   in the engine’s indexing convention.
7. For a family over a base, retain the existing parameter measurability, smoothness and integrability hypotheses. Pointwise face integrability alone is not a substitute for the family-integral obligations.

For a contributing face \(J\), define
\[
a_i:=2k_i,\qquad
\alpha_j:=a_j\mu-h_j-1.
\]
The theorem should give
\[
\begin{aligned}
\operatorname{smoothCoeff}(A,h,k,\beta,b;\mu,c-1)
={}&
\frac{\Gamma(\mu)\beta^{-\mu}}{(c-1)!}\\
&\times
\sum_{\substack{|J|=c\\
a_j\mu-h_j-1\in\mathbb N\ \forall j\in J}}
\left(\prod_{j\in J}\frac1{a_j\alpha_j!}\right)
\int_{(0,b]^{J^c}}
(\partial_J^\alpha A)(0_J,w)
\prod_{i\notin J}w_i^{h_i-a_i\mu}\,dw .
\end{aligned}
\]
For this explicit version take \(\mu>0\); every actual resonant contribution already has \(\mu>0\) under the stated exponent hypotheses.

Here \(A\) means the **entire engine amplitude**. In the resolved application,
\[
A=\omega\,|b|\,(\mathrm{prior}\circ\pi)\,F
\]
in chart coordinates. Unless \(\alpha=0\), the derivative falls on this entire product. Expanding by Leibniz gives a differential functional of the observable involving its normal derivatives of orders at most \(\alpha\), not merely one derivative of \(F\).

### Proof structure

Your collapse argument is correct after the resonance correction:

- \(|J|>c\): the face amplitude vanishes by neighbourhood vanishing on the corresponding deeper face.
- \(|J|<c\): the logarithmic index range is empty at \(q=c-1\), or the resonant-count bound kills it.
- \(|J|=c\): only \(j=c-1\) occurs.
- Nonresonant size-\(c\) faces vanish by the resonant-count bound.
- Resonant size-\(c\) faces have the unique multi-order \(\alpha\).
- The logarithmic weight has exponent \(j-q=0\).
- The complementary Taylor remainder reduces to the unremaindered face derivative.

### The `remList` lemma

The needed lemma is genuinely modest, but its hypothesis should concern the relevant **normal jets on each complementary coordinate hyperplane**, not just function values.

For
\[
G(w):=(\partial_J^\alpha A)(0_J,w),
\]
neighbourhood vanishing of \(A\) near depth \(c+1\) implies that \(G\) vanishes near every complementary active hyperplane. Hence each coordinate Taylor polynomial of \(G\) is zero, and each coordinate remainder operator fixes \(G\). Iterate through `remList`.

The proof can use all jets as a convenient interface even though only finitely many are required.

### Convergence is a theorem, not notation

Do explicitly prove `Integrable` for the unremaindered power-weighted integrand. The fact that Lean permits writing `∫` does not establish that it is an honest convergent integral.

On a compact closed face, neighbourhood vanishing gives a collar near every complementary active boundary on which \(G=0\). The remaining power weight is bounded on the support. For families, obtain the appropriate uniform or dominated statement from the compact chart-support/base hypotheses.

## 4. The top-face constant

Your constant is correct:
\[
\boxed{
\operatorname{faceMonoCoeff}_{\mathrm{top}}
=
\frac{\Gamma(\mu)\beta^{-\mu}}{(c-1)!}
\prod_{j\in J}\frac1{2k_j}.
}
\]

For rectangular upper limits, put \(a_j=2k_j\) and
\[
B=\prod_{j\in J}b_j^{a_j}.
\]
When \(e_j+1=a_j\mu\), substitution followed by the product-coordinate formula gives
\[
\int \prod_j u_j^{e_j}
e^{-N\beta\prod_j u_j^{a_j}}\,du
=
\frac{\prod_j a_j^{-1}}{(c-1)!}
\int_0^B t^{\mu-1}e^{-N\beta t}
\bigl(\log(B/t)\bigr)^{c-1}\,dt.
\]
Scaling \(t\) by \(N\beta\) gives the displayed coefficient. In particular it is independent of the upper box lengths.

For \(x^2y^2\), \(c=2\), \(\mu=1/2\), \(\beta=1\), this is indeed \(\sqrt\pi/4\).

**Prove the formula, not only positivity.** It supplies the density’s normalization and makes the “stratum integral” description concrete.

## 5. Resolved assembly and the density’s name

E2 should first define the finite chart-piece expression and prove
\[
F\in\mathcal I_{c+1}
\quad\Longrightarrow\quad
\mathcal T^U_{\mu,c-1}[F]=\Sigma_{\mu,c}[F].
\]

Then prove a short geometric interpretation lemma: a face point with precisely the \(J\)-coordinates zero and all complementary active coordinates positive lies in the exact depth-\(c\) stratum. Under resonance of its \(c\) walls, it lies in \(S^\mu_c\).

This identification is worth doing. Without it, the formal result is a face formula while the paper calls it a stratum formula. It should only require the existing wall/face-point bookkeeping, not a new global parametrization of every stratum. Artificial box boundaries and the localization support must be handled using the atlas conventions already in the resolved package.

### Local description

Write the phase in a presentation adapted to \(J\) as
\[
K\circ\pi
=\left(\prod_{j\in J}u_j^{a_j}\right)A_J(s,w),
\qquad
A_J(s,w)=\beta(s)\prod_{i\notin J}w_i^{a_i}>0
\]
on the open face. Then the tangential weight contains
\[
A_J(s,w)^{-\mu}\prod_{i\notin J}w_i^{h_i}.
\]

A good name is:

> **the local top Mellin-residue weight along the normal-crossings stratum.**

In the zero-normal-order case, “top Mellin-residue density” is appropriate intrinsically. This terminology describes the explicit local calculation; it does not assert that global meromorphic continuation has been constructed.

Avoid writing \((K\circ\pi|_{S})^{-\mu}\): the phase restricts to zero on the stratum. It is the **positive residual phase factor after removing the normal monomial** that is raised to \(-\mu\).

Inactive directions contribute the background tangential measure; their monomial factor is \(1\) in the stated convention.

## 6. Positivity and values-only dependence

E3 is correct with this exact condition:

> At every contributing point of \(S^\mu_c\), every incident wall satisfies
> \[
> 2k_j\mu=h_j+1.
> \]

Thus all selected normal orders are zero. Assuming the existing nonnegative partition of unity and nonnegative prior/density factors,
\[
F\ge0,\quad F\in\mathcal I_{c+1}
\quad\Longrightarrow\quad
\mathcal T^U_{\mu,c-1}[F]\ge0.
\]
Within \(\mathcal I_{c+1}\), the functional depends only on \(F|_{S^\mu_c}\).

This yields a positive stratum measure, locally finite away from deeper strata. Do **not** assert finite mass after adjoining the deeper boundary without an additional estimate.

The slogan “each stratum carries its own positive leading functional” needs qualification: it applies to strata whose incident wall ratios coincide. A stratum with unequal ratios need not have this zero-order positive top-log functional.

No Riesz machinery is necessary for E3 if the measure is given directly by the positive local densities.

## 7. Vanishing near versus flatness

Use **vanishing near** in the initial theorem.

Flatness is a natural extension, and mathematically it should work here:

- flatness gives the same Taylor-remainder cancellation;
- arbitrarily high boundary decay makes the power-weighted face integrals integrable.

But it should remain a non-claim until those estimates are formalized.

There is a standard compact-support cutoff approximation of flat functions by functions vanishing near a normal-crossings closed set, in the smooth topology. It is not a free shortcut in this development. To pass to the formula one still needs:

1. continuity of the coefficient functional in a specified topology;
2. continuity or dominated convergence for the weighted stratum integrals;
3. the cutoff construction and estimates, uniformly over the finite atlas.

Unless those interfaces already exist, direct flat-decay estimates may cost no more. Put this in an optional follow-up, not on Theorem E’s critical path.

## 8. Unit list and costs

| Unit | Deliverable | Cost |
|---|---|---:|
| **E0** | Audit resonance semantics; prove top-log nonvanishing forces full face resonance and uniqueness of \(\alpha\). Record the required depth certificate. | **S** |
| **E1a** | `remList_eq_self_of_jetsZero_on_hyperplanes`, plus application to face derivatives under deeper-face vanishing. | **M** |
| **E1b** | `faceMonoCoeff_top`: explicit gamma constant, upper-limit independence, positivity. | **M** |
| **E1c** | Integrability/collar lemma for unremaindered weighted face derivatives, including the family version needed downstream. | **M** |
| **E1d** | Engine face-sum collapse at \((\mu,c-1)\), first at certified depth, then for the stable coefficient. | **M** |
| **E2** | Resolved chart-piece definition and equality; transport neighbourhood vanishing; exact-stratum interpretation; intrinsic restricted/graded functional. | **L** |
| **E3** | Zero-order positivity, values-only dependence, and positive local density formulation. | **M** |
| **E4** | Euclidean pullback corollary and paper statement with non-claims. | **S** |

Dependency order:
\[
E0\to(E1a,E1b,E1c)\to E1d\to E2\to E3\to E4.
\]

E2 deserves **L** as a planning estimate. Reusing CDXXXV should control the point bookkeeping, but the theorem also needs unremaindered integrability, family assembly, and the geometric interpretation.

No global zeta continuation, chosen-kernel transformation calculus, flat-observable extension, or weak-convergence theorem belongs on this critical path.

## 9. What to say about the full expansion

Correct E4’s description of the lower logarithms.

For \(q<c-1\), contributions need not come only from shallower faces: size-\(c\) faces themselves can contribute lower logarithms. The established formula is a sum of **Taylor-subtracted face integrals**, with power-log weights and depth-dependent decomposition.

Call these:
> convergent Taylor-subtracted chart-face formulas.

They may be interpreted as a regularisation scheme, but the existing integrals should not be described as divergent, and no canonical regularised contribution should be assigned to each individual stratum.

For the original observable,
\[
C_{\mu,q}(f)=\mathcal T^U_{\mu,q}[f\circ\pi],
\]
retain the established support inclusion
\[
\operatorname{supp}C_{\mu,q}
\subseteq
\pi\!\left(Z_0\cap\{r_\mu\ge q+1\}\right).
\]
The graded stratum formula applies when \(f\circ\pi\in\mathcal I_{c+1}\).

That restriction can be substantial: different resolved strata may project to the same subset of \(W\). Hence the theorem is not a claim that arbitrary original observables have every coefficient represented by an unregularised integral over exact strata. Their complete coefficients remain covered by the existing chart-face formula.

## 10. Paper-facing statement

> **Theorem E (graded stratum formula).** Under the hypotheses of Theorem D, let \(D_c=Z_0\cap\{\mathrm{depth}\ge c\}\), and let \(F\) be an admissible smooth observable vanishing on a neighbourhood of \(D_{c+1}\), where \(c\ge1\). Then \(\mathcal T^U_{\mu,q}[F]=0\) for \(q\ge c\), while \(\mathcal T^U_{\mu,c-1}[F]\) is a finite sum of absolutely convergent stratum integrals over \(S^\mu_c=Z_0\cap\{\mathrm{depth}=c,\ r_\mu=c\}\). In normal-crossings coordinates, each contribution is obtained by differentiating the localized resolved amplitude in the \(c\) normal directions to the unique orders \(\alpha_j=2k_j\mu-h_j-1\in\mathbb N\), integrating against the complementary power weight, and multiplying by \(\Gamma(\mu)\beta^{-\mu}/((c-1)!\prod_j(2k_j)\alpha_j!)\). The total is intrinsic and defines a functional on \(\mathcal I_{c+1}/\mathcal I_c\), although individual higher-jet chart contributions need not be canonical. If all contributing orders are zero, this functional depends only on the values of \(F\) on \(S^\mu_c\) and is positive for nonnegative \(F\). The corresponding assertion for the original partition-function coefficients follows by taking \(F=f\circ\pi\); without the neighbourhood-vanishing hypothesis, all coefficients retain their Taylor-subtracted chart-face formulas, and no canonical individual regularised stratum contributions or flat-observable extension is asserted.