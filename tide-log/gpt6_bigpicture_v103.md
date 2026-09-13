## Verdict

**E4 meets the stated “assembled chart expansions of the original cube integral” specification. Intrinsic gluing is not needed for that claim or for citing this theorem in the paper.**

The supplied code establishes the important conjunction:

1. an **exact decomposition of the original integral**, not merely a replacement model;
2. certificates produced for the actual pulled-back amplitudes and phase;
3. identification of every piece with its certificate’s Laplace integral;
4. an all-order expansion obtained by finite-sum assembly, with coefficients given by the chart certificates’ strata integrals.

I would accept phase E, subject to the documentation corrections below. My next gate would be a small **E4 coefficient-fidelity phase**, not E5 or an atlas.

This is an audit of the supplied source and declarations, not an independent checkout/build of `d8853e3`.

---

## 1. Specification audit: what is, and is not, delivered

### The central specification is met

The decisive theorem is actually the pair
```lean
cube_integral_eq_sum_pieces
cube_hasExpansion
```
The first holds for every real `n`; the second sums the piecewise little-o remainders on a common finite cutoff spectrum. In the assembly proof, neither an asymptotic replacement of the original integral nor an unproved coefficient identification is smuggled in.

The pullback order is also correct:
\[
z\longmapsto R_\sigma z\longmapsto\phi_\beta(R_\sigma z).
\]
The phase, Jacobian weight, observable and prior are all transported in that order.

**The paper may say:**

> For the quadratic phase on the cube, we construct singleton chart certificates in the signed blow-up coordinates and assemble their strata-integral coefficients into an all-order expansion of the original integral.

It should immediately distinguish this from:

> We construct a global resolved geometry for the blow-up and an intrinsic coefficient field on its exceptional divisor.

The latter is not delivered.

### Three scope qualifications

**First:** the generalisation has two different levels:

- E1–E2 provide partial-active geometry and weighted/unit-normalised core infrastructure.
- E3–E4 provide a completed producer and assembly for the **singleton-active, quadratic-normal** case.

Do not describe this as a completed producer for arbitrary active sets and arbitrary monomial orders. That remains E5.

**Second:** the chart geometries have `π = id`. Their relationship to the original cube is supplied externally by the exact chart change-of-variables theorem. These are legitimate **chart-model certificates**, not certificates on one globally constructed blow-up space.

**Third:** the strata of `G β (d−1)` are ambient chart strata. The closed face in `[0,1]^d` is the certificate’s compact base/support, not the definition of the whole ambient stratum. Replace prose saying

> “the strata are `{yβ = 0}` and its complement in `[0,1]^d`”

with

> “the ambient chart strata are `{yβ = 0}` and its complement; the certificate is localised to `[0,1]^d`, with compact base its closed `β`-face.”

### Gluing is a separate project

There is no missing gluing obligation for finite-sum assembly. The exact integral identity already handles overlap multiplicities a.e.

Nor should the next project simply replace `π := id` by `π := φβ`: on the entire affine chart, the fibre over zero is noncompact for `d > 1`, so that map is not proper.

Also distinguish the intended global object:

- real projective blow-up: exceptional divisor \(\mathbb{RP}^{d-1}\);
- oriented/radial blow-up: exceptional boundary \(S^{d-1}\).

They are alternatives with different identifications, not interchangeable descriptions of an already formalised space.

---

## 2. Spectrum: prove the small fidelity gate, but correct the cancellation claim

The current spectrum is a perfectly valid **ambient indexing lattice**. An expansion need not be presented on its minimal support.

Nevertheless, identifying its actual support would substantially improve the paper-facing result.

### A necessary correction: odd orders do not vanish on individual pieces

The proposed explanation

> “odd normal orders vanish pointwise on each piece and the two orthant sides cancel”

is false in its first clause.

For example, take `d = 1`, `p = 1`, and `F(x) = 1 + x`. On the positive piece,
\[
\int_0^1(1+r)e^{-Nr^2}\,dr
\]
has a nonzero \(N^{-1}\) coefficient. The negative piece has the opposite coefficient.

The correct statement is:

> Odd **total amplitude Taylor orders** cancel after pairing the two normal-sign pieces, pointwise in the tangential base variable after the appropriate identifications.

“Total amplitude” matters: cancellation involves derivatives of the prior and observable together, not merely odd observable jets.

### The actual parity condition

Write the lattice exponent as \(\alpha=m/2\). The expected support is
\[
\alpha=d/2+j,\qquad j\in\mathbb N.
\]
Thus the surviving lattice numerators satisfy
\[
m\ge d,\qquad m\equiv d\pmod 2.
\]

It is **not** “odd `m` vanish” unless `d` is even. In odd dimension the leading exponent itself has odd numerator.

### Recommended statements

Initially state these on the declared spectrum. For example, use a hypothesis equivalent to
```lean
∃ B : ℝ, q ∈ spectrumLe 2 0 B
```
rather than claiming uniqueness determines coefficients at arbitrary `PowerLogIndex` values.

The targets are:

1. **Below-leading vanishing**
   \[
   q\text{ in the declared spectrum},\quad q.\mathrm{exponent}<d/2
   \Longrightarrow C(q)=0.
   \]

2. **Leading identification**
   \[
   C((d/2,0))=\pi^{d/2}F(0)p(0).
   \]

3. **Support**
   \[
   q\text{ in the declared spectrum},\quad
   \neg\exists j\in\mathbb N,\ q.\mathrm{exponent}=d/2+j
   \Longrightarrow C(q)=0.
   \]

Uniqueness on `spectrumLe 2 0` does not, by itself, determine values at indices never appearing there. If the coefficient implementation is globally zero off that lattice, that is a separate support lemma.

### Cheapest route for (a) and (b): leading asymptotics plus uniqueness

Obtain the unconditional leading remainder statement
\[
I(N)-c_0N^{-d/2}=o(N^{-d/2}),
\qquad
c_0=\pi^{d/2}F(0)p(0).
\]
Compare it with `cube_hasExpansion` at cutoff \(d/2\), using the candidate coefficient family that is zero below \(d/2\) and equal to \(c_0\) there.

That proves both (a) and (b) without opening the certificate fields.

**Two cautions:**

- A leading equivalence theorem requiring \(c_0\ne0\) does not cover all E4 inputs. Here `F(0)p(0)` can vanish. In particular, asymptotic equivalence to the identically zero function is not the general leading-remainder assertion you need. Use a scaled-limit or little-o formulation.
- The cited leading result has `d ≥ 2`, whereas E4 has `[NeZero d]`. Preserve E4’s hypothesis: add a one-dimensional leading lemma if necessary, rather than silently restricting the final theorem.

`leadingMeasure_eq` is the natural identification input, but an equality of measures still needs the corresponding convergence/leading-remainder theorem to connect it to this integral.

### Cheapest route for (c): structural support and normal-sign pairing

A leading theorem alone cannot eliminate the intervening higher exponents. Uniqueness helps only once a genuine alternative all-order expansion is available.

For this codebase, I would try the following route before constructing a second expansion.

**Step 1 — singleton support.** For normal weight \(h_0\), prove the piece coefficient can occur only at
\[
\alpha=\frac{h_0+1+\ell}{2},\qquad \ell\in\mathbb N.
\]
For E4 this becomes \((d+\ell)/2\). This already gives below-leading vanishing directly.

**Step 2 — flip only the chart normal sign.** Let \(\sigma^\ast\) agree with \(\sigma\) except at \(\beta\). Then
\[
\phi_\beta(R_{\sigma^\ast}z)
=-\phi_\beta(R_\sigma z).
\]
Moreover, varying the original chart normal variable through zero gives
\[
a_{\sigma^\ast}(t,r)=a_\sigma(t,-r),
\quad
a_\sigma=(Fp)\circ\phi_\beta\circ R_\sigma.
\]
The unit, weight and tangential base are unchanged. Consequently, the total Taylor coefficient of order \(\ell\) changes by \((-1)^\ell\).

**Step 3 — sum over the fixed-point-free sign involution.** Odd \(\ell\) cancels.

Use G7’s sign-sum mechanics, but do not assume `synthetic_cancellation` applies unchanged to these produced density/observable fields. The missing bridge is the transformation of the **convolution of prior coefficients and observable jets**.

If chosen packet radii or certificate cores differ between paired pieces, do not try to prove the certificates definitionally equal. Prove coefficient-level invariance under those choices, or use uniqueness to compare each piece with an explicit singleton Taylor expansion.

---

## 3. Fidelity of representatives and jets

### Observable representatives: yes, the germs are correct

Your reasoning is sound **because agreement holds on the open real domain**, not merely on the box.

Every base point belongs to that open domain. Therefore
\[
\operatorname{obsRep}_{\beta,\sigma}
=F\circ\phi_\beta\circ R_\sigma
\]
eventually in the neighbourhood filter of each base point. All ambient derivatives, and hence the normal differentials defined using the same chart normal data, agree.

This remains true at corners of the closed face. The face need not be open; the real domain containing it is open.

I would add explicit bridge lemmas:

- `obsRep_piece_eventuallyEq`;
- `normalDifferential_obsRep_piece`.

These are cheap and make the paper’s jet interpretation a theorem rather than an explanation buried in packet definitions.

**Keep the frame distinction explicit:** equality of the underlying normal differentials does not remove the \(\lambda\)-rescaling when those differentials are evaluated on the certificate frame.

### Positive-part priors: distinguish measure fidelity from derivative fidelity

The E3 design correctly separates:

- the measurable, nonnegative density representative `ϕ'`;
- the analytic series prior `ϕ`.

It requires agreement on the integration box. It does **not** need derivatives of `ϕ'` to be analytic or to agree with those of `ϕ` across the boundary.

This is important: in a generic positive-box example, \(p(y)=y_\beta\) is nonnegative on the box, while \(\max(p,0)\) is not differentiable across its zero face. So do not advertise the coefficient density family as “the derivatives of the positive-part prior”.

For the specific E4 pieces there is a stronger fact available. Every base point maps to the original origin, which is interior to the signed cube. Continuity of the chart map gives a neighbourhood mapping into that cube. Hence the pulled-back prior is nonnegative locally at every base point, and the positive-part operation is locally inactive there.

That stronger lemma is optional. The existing certificate construction does not need it.

**Bottom line:** nothing is lost in the integral or observable jets. The coefficient construction deliberately uses the analytic prior extension, not an unjustified differentiation of an arbitrary measurable density representative.

---

## 4. Unit normalisation: correct, with an important density clarification

Yes: this is exactly the intended fibrewise normalisation.

Write the original normal variable as \(y_\beta\), and the normalised one as \(r\):
\[
r=\sqrt{u(t)}\,y_\beta,\qquad
y_\beta=\lambda(t)r,\qquad
\lambda=u^{-1/2}.
\]
Then
\[
u(t)y_\beta^2=r^2.
\]

The weight transforms as
\[
|y_\beta|^{h_0}\,dy_\beta
=\lambda^{h_0+1}|r|^{h_0}\,dr.
\]
For the cube, \(h_0=d-1\), so the analytic density prefactor is
\[
\lambda^d=u^{-d/2}.
\]

Thus the safest paper statement is:

> In the normalised normal coordinate, the weighted density is  
> \[
> |r|^{d-1}u(t)^{-d/2}\,
> p\bigl(\phi_\beta(R_\sigma(t,\lambda(t)r))\bigr)\,dt\,dr.
> \]

Your expression “\(|y_\beta|^{d-1}p\,(\sqrt u)^{-1}\) per unit normal length” is correct only if “normal length” means \(dr\) and \(y_\beta=\lambda r\) is retained in that expression. Otherwise it can conceal the missing \(\lambda^{d-1}\) from the weight. State \(\lambda^{h_0+1}\) explicitly.

A Taylor term of total order \(\ell\) supplies another \(\lambda^\ell\), giving
\[
u^{-(d+\ell)/2}.
\]
The associated positive-normal moment is
\[
\int_0^\infty r^{d-1+\ell}e^{-Nr^2}\,dr
=\frac12\Gamma\!\left(\frac{d+\ell}{2}\right)
N^{-(d+\ell)/2}.
\]

This is the expected chart coefficient mechanism. The produced moment field is appropriately called a **chart coefficient tensor field** or **chart-local moment field**. Calling it a global exceptional-divisor tensor would overstate the result.

As a numerical/factorial sanity check, after pairing normal signs, the expected formula is indeed
\[
C_j=
\frac{\Gamma(d/2+j)}{(2j)!}
\sum_\beta\int_{[-1,1]^{d-1}}
u_\beta(t)^{-d/2-j}
D^{2j}(Fp)(0)[v_\beta(t),\ldots,v_\beta(t)]\,dt,
\]
with \(v_\beta(t)_\beta=1\) and the other coordinates \(t\). This is a target interpretation, not something E4 already identifies formally.

---

## 5. Next gate and ranking

### Recommended next phase: **E4F — coefficient fidelity**

Keep it sharply bounded.

| Gate | Deliverable | Priority |
|---|---|---|
| F0 | Correct scope/parity/density documentation; observable germ bridge | Required |
| F1 | Below-leading vanishing and leading coefficient identification | Required for the next paper-facing endpoint |
| F2 | Singleton support plus paired odd-total-order cancellation; sharpened spectrum corollary | Worth doing, time-boxed |
| F3 | Full directional-derivative/Gamma coefficient formula | Defer |

For F1, use uniqueness and the unconditional leading remainder. Do not unfold the tensor field just to recover a known leading constant.

For F2, first inspect how directly singleton moments expose their support. If proving the pairing turns into a new general tensor-naturality framework, stop after F1 and publish with the explicitly stated ambient spectrum. That is still a sound all-order result.

If F2 lands, add a corollary of the schematic form
\[
I(N)-
\sum_{\substack{j\in\mathbb N\\d/2+j\le A}}
C((d/2+j,0))N^{-d/2-j}
=o(N^{-A}).
\]
Retain `cube_hasExpansion` as the certificate-facing theorem; the sharp version is the paper-facing wrapper.

### Ranking the larger options

For the present paper:

1. **(i) E4 fidelity items.** Highest value, smallest scope.
2. **(iv) Programme J.** Next only if observable-independent functionals are a substantive paper claim. Scalar canonicity for each `F` does not alone construct a common functional.
3. **(ii) E5 partial-active collar.** Good library generalisation, but it proves substantially more than the cube application needs.
4. **(iii) Intrinsic blow-up gluing.** Geometrically valuable, unnecessary for assembled expansions, and requires a genuinely new global object.
5. **(v) SNC atlas.** A separate programme, not the next gate.

**Stopping point:** F1, preferably F2. Do not make E5, J, gluing or SNC prerequisites for the present assembled-chart theorem.

---

## 6. Exact changes I would make now

### No mathematical change to `cube_hasExpansion`

Its statement and `[NeZero d]` hypothesis are appropriate. Keep the name; optionally add a more explicit paper-facing alias, rather than renaming the existing API.

### Amend its docstring

Replace the spectrum interpretation by:

> The expansion is indexed by the ambient half-integer lattice `spectrumLe 2 0`. This statement does not identify its minimal support. Its coefficients are sums of strata integrals on independently constructed chart-model geometries with identity projection; no global blow-up geometry or intrinsic gluing is asserted.

After F1/F2, link the sharper theorems.

### Amend E3’s integral description

The theorem’s density is `ϕ'`, so write:

> The weighted integral with density `|yβ|^h₀ · ϕ'`, where `ϕ'` agrees on the box with the analytic series prior `ϕ`, has the produced chart-strata expansion.

This avoids suggesting that the measurable representative is globally analytic.

### Amend the cancellation target

Replace:

> “odd normal orders vanish pointwise on each piece”

by:

> “odd total prior–observable Taylor orders cancel between paired normal-sign pieces.”

Replace “odd `m`” by “`m` of parity different from `d`”.

### Amend the density interpretation

Replace an unqualified “factor \(u^{-1/2}\)” by:

> “Normal rescaling contributes \(u^{-(h_0+1)/2}\) to the weighted analytic amplitude; for the cube this is \(u^{-d/2}\).”

### Add a packet-independence lemma if it is cheap

Uniqueness should show that two analytic packets representing the same `p, F` give the same `cubeCoefficient` **on the declared spectrum**. This is a useful scalar fidelity statement and does not require programme J or intrinsic gluing.

---

**Overall assessment:** phase E has delivered the intended original-integral assembly, not merely another synthetic model. The remaining risks are chiefly overinterpretation: confusing ambient spectrum with support, piecewise jets with already-glued tensors, positive-part measure representatives with analytic density germs, and one-sided coefficients with parity-cancelled coefficients. Correct those claims, add the leading/support bridges within a bounded gate, and stop for the paper.
