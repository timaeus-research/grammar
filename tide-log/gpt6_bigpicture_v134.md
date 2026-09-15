## Verdict

The substantive conclusions look right: **local positivity, finiteness of the extremal measure, the monomial regression, and the corrected \(x^2y^2\) constant all have the advertised mathematical content.** I would make four wording corrections:

1. Distinguish **admissible extremal data** from **realised, positive leading data**.
2. Say the equal-exponent exact stratum is **contained in the origin**, unless the hypotheses ensuring membership are stated.
3. Separate the original-parameter orthant constant from the square-parameter constant; the current parenthesis risks counting the logarithmic factor twice.
4. Correct candidate (v): for unequal exponents, the leading coefficient involves a **weighted restriction of the prior to a coordinate subspace**, not generally \(\varphi(0)\) times a residual integral, and the leading measure is not generally a point mass.

One scope qualification: the excerpts suppress section parameters. Thus this is an audit of the displayed mathematical contracts, not a verification of their complete elaborated parameter lists. In particular, the equal-exponent positivity statements must carry the relevant \(0<\kappa\) and \(\varphi(0)>0\) assumptions.

## (a) Signature audit

### Positivity

These statements have the right hierarchy:

- Continuous observables suffice for integrability and the local positive orthant bound.
- Smoothness is used to enter the coefficient/asymptotic machinery.
- Global nonnegativity of \(f\), positivity of the prior and \(f\) at the realised point, and exact resonance count give a **strictly positive coefficient**.
- Identifying that coefficient with the stratum integral additionally requires vanishing near the deep zero fibre.

The distinction in the last item matters. A point with exactly \(m\) resonating walls can still have more than \(m\) walls in total. The coefficient-positivity theorem applies there; the measure-integral theorem has the additional vanishing hypothesis, which may be incompatible with positivity at that point.

Consequently, these signatures do **not**, by themselves, identify the full support of \(\nu\), or guarantee an admissible positive observable at every resonating point. Your mirror paragraph does not explicitly claim either, but preserve that distinction.

The absence of \(0<\varepsilon\) from `Z_ge_mul_monoBoxIntegral` is not a problem: positivity of the useful box size is supplied by `exists_orthant_bound_obs`.

### Finiteness

This closes the finiteness question cleanly:

\[
\nu(X)\leq \mathcal T[1]<\infty.
\]

The compact-cutoff argument is exactly the right mechanism. The comparison theorem needs only \(\chi\leq1\); nonnegativity of \(\chi\) is needed for its use as a cutoff, not for the general coefficient comparison.

Two wording changes:

- Replace “in general the unit insertion **fails** the neighbourhood-vanishing hypothesis” by “the unit insertion **need not satisfy** the neighbourhood-vanishing hypothesis.”
- Replace “the mass is not identified with the coefficient” by “**these results do not identify** the mass with the coefficient in general.”

Neither the inequality nor the conditional equality establishes a strict deficit when the deep fibre is nonempty.

### Monomial regression

Yes: the combination
\[
\mathrm{IsExtremalData}(\lambda_*,m_*),
\qquad
\text{realisation at }0,
\qquad
\varphi(0)>0
\]
is the right formal content for recovering the classical leading monomial asymptotic.

`isExtremalData_monomial` alone should not be described as proving that these are the actual nonzero leading data for an arbitrary prior and arbitrary \(W\). For example, \(W\) or the prior support might avoid the maximal intersection. Realisation and positivity remove that issue.

The construction is **not circular**:

- The identity map is constructed as an actual modification.
- Unit absorption supplies the local chart interface.
- The intrinsic pairs and resonance counts are then calculated.
- The general theorem produces the asymptotic and positivity.

Reusing unit absorption is legitimate infrastructure reuse. This is an **end-to-end regression**, not an independent verification of unit absorption itself. CDLXII adds an independently evaluated normalization check, which makes the regression substantially stronger.

### Equal exponents

The safe claims are:

- \(D_{d+1}=\varnothing\), from the depth bound.
- The exact stratum is contained in \(\{0\}\).
- The measure is \(c\delta_0\), provided the origin is available as a point of its domain.
- With positive prior at the origin, \(c>0\).

The point-mass theorem remains meaningful when \(c=0\). The sentence “the exact stratum is the origin” needs the origin-membership assumptions, not just `exactStratum_equal_subset`.

For the public API, I would explicitly inspect the fully elaborated signatures of:

- `isExtremalData_equal`;
- `tendsto_normalised_partitionObs_equal`.

The former should carry the intended positivity assumption on \(\kappa\); the latter’s existential **positive** \(c\), when applied to \(f=1\), requires an appropriate positivity hypothesis on the prior.

## (b) The constants

### Top stratum: confirmed

For the original parameter \(N\),
\[
\boxed{\nu^{(1/2)}_2=\sqrt{\pi}\,\varphi(0)\,\delta_0.}
\]

Each original-parameter orthant contributes
\[
\frac{\sqrt{\pi}}4\,\varphi(0)
\]
to the coefficient of \(N^{-1/2}\log N\).

For the square-parameter headline, each orthant instead contributes
\[
\frac{\sqrt{\pi}}2\,\varphi(0)
\]
to the coefficient of \(T^{-1}\log T\). Substituting \(T=\sqrt N\) gives the extra factor \(1/2\).

Thus use **either** of these explanations:

- four sectors, each \(\sqrt\pi\,\varphi(0)/4\), in the original parameter; or
- four sectors, each \(\sqrt\pi\,\varphi(0)/2\), followed by halving the logarithm.

The current mirror parenthesis mixes the two stages.

### Depth one: also confirmed

On the punctured axes,
\[
\boxed{
\nu^{(1/2)}_1
=
\sqrt{\pi}\left(
\frac{\varphi(x,0)}{|x|}\,dx
+
\frac{\varphi(0,y)}{|y|}\,dy
\right).
}
\]

Here \(dx\) and \(dy\) range over the respective **full punctured axes**. The coefficient \(\sqrt\pi\) comes from integrating over both normal sides:
\[
\int_{\mathbb R}e^{-Nx^2y^2}\,dy
=\frac{\sqrt\pi}{\sqrt N\,|x|}.
\]
The positive and negative tangential rays are already included in \(dx\); there is no additional doubling.

If \(\varphi(0)>0\), this measure has infinite total mass near the omitted origin. That gives the concrete example supporting “off the extremal index, stratum measures can have infinite mass.”

### Box support

The half-open box assumption is mathematically acceptable as a technical regression hypothesis, but I would remove it from the paper-facing theorem. It is arbitrary and visually distracting.

Scaling is straightforward. With \(x=tz\), define
\[
\varphi_t(z)=t^2\varphi(tz).
\]
Then
\[
Z_\varphi(N)=Z_{\varphi_t}(t^4N),
\]
and
\[
\frac{\sqrt N}{\log N}Z_\varphi(N)
=
t^{-2}\frac{\log(t^4N)}{\log N}
\left[
\frac{\sqrt{t^4N}}{\log(t^4N)}
Z_{\varphi_t}(t^4N)
\right].
\]
Since \(\varphi_t(0)=t^2\varphi(0)\), the factors cancel and the same constant results. Choose \(t\) large enough to put the rescaled compact support strictly inside the unit box. The observable version uses \(f_t(z)=f(tz)\).

## (c) Direction

### Recommended next substantive unit: corrected mixed-monomial constant, preferably for all smooth insertions

Given that `monomialSymReal_tendsto` and `monomialMixedConst` already exist, this looks like the best next S–M investment. It tests something the equal-exponent case cannot: a **positive-dimensional leading measure**.

Let
\[
J=\{i:k_i=k_{\max}\},\qquad m=|J|,\qquad
\lambda=\frac1{2k_{\max}},
\]
and let \(z\) denote the remaining coordinates. The expected leading coefficient is
\[
\boxed{
\mathcal T[f]
=
\frac{2^m\Gamma(\lambda)}
{(m-1)!\prod_{i\in J}(2k_i)}
\int_{\mathbb R^{J^c}}
\varphi(0_J,z)f(0_J,z)
\prod_{j\notin J}|z_j|^{-2k_j\lambda}\,dz.
}
\]

The residual powers are locally integrable because \(k_j<k_{\max}\).

This corrects candidate (v) in three ways:

- The prior is \(\varphi(0_J,z)\), not generally \(\varphi(0)\).
- With integration over the full residual space, the explicit sign factor is \(2^m\), not \(2^d\).
- The leading measure is supported on \(\{x_i=0:i\in J\}\), not generally at the origin.

An all-orthant formulation can have a different arrangement of sign factors, but must retain reflected residual amplitudes unless symmetry is assumed.

For equal exponents this reduces to
\[
c=
\frac{2^d\Gamma(1/(2\kappa))}
{(d-1)!(2\kappa)^d}\,\varphi(0),
\]
so the general equal-exponent explicit point mass comes along as a corollary.

### Then: general chart-pushforward measure \(=\nu\)

This remains the most valuable **general structural** follow-up. It turns the abstract representing measure into the explicit geometric object and resolves chart-weight bookkeeping once rather than example by example.

### Depth-one \(x^2y^2\): try a direct route before transport bookkeeping

You may not need to calculate `residueSum` for a specially chosen \(Y\).

For smooth tests vanishing near the origin, directly prove
\[
\sqrt N\int \varphi f\,e^{-Nx^2y^2}
\longrightarrow
\sqrt\pi\left(
\int\frac{\varphi(x,0)f(x,0)}{|x|}\,dx+
\int\frac{\varphi(0,y)f(0,y)}{|y|}\,dy
\right).
\]
Use the existing graded limit/representation theorem to identify the same limit with integration against \(\nu^{(1/2)}_1\), then invoke uniqueness on compactly supported smooth tests.

For the identity modification, compactly supported smooth tests on the relevant open domain can be extended by zero as needed. This route avoids explicitly resolving transport chart weights and supplies an independent normalization check. If it is short, it is an excellent intervening unit.

I would keep subtype-\(S\) packaging below these unless a downstream theorem needs it. Zeta continuation remains a separate, larger project; none of the present closure claims requires it.

## (d) Suggested replacement regression wording

> For a monomial phase \(K(x)=\prod_i x_i^{2k_i}\), with at least one \(k_i>0\), the identity on \(W\) is a Watanabe modification. At a zero \(P\), the intrinsic wall pairs are \((k_i,0)\) for those coordinates with \(P_i=0\) and \(k_i>0\). The values \(\lambda_*=1/(2k_{\max})\) and \(m_*=\#\{i:k_i=k_{\max}\}\) satisfy the extremal-data conditions; when the prior is positive at the origin, these data are realised and the general theorem yields the classical monomial asymptotic with a strictly positive leading constant.
>
> For equal positive exponents \(k_i=\kappa\) in positive dimension, the deep zero fibre \(D_{d+1}\) is empty and the exact stratum is contained in the origin. Assuming the origin lies in \(W\), the leading stratum measure is \(c\delta_0\), where \(c\) is the unit-insertion coefficient; it is positive when the prior is positive at the origin. Every smooth insertion has normalized limit \(cf(0)\).
>
> For \(K=x^2y^2\), direct evaluation of the symmetric-box headline gives \(c=\sqrt\pi\,\varphi(0)\). Equivalently, each of the four orthants contributes \(\sqrt\pi\,\varphi(0)/4\) in the original parameter. Hence the leading measure is \(\sqrt\pi\,\varphi(0)\delta_0\), and the normalized observable integral converges to \(\sqrt\pi\,\varphi(0)f(0)\).

Retain a box-support qualifier in the final paragraph until the scaling corollary lands. After that, state it for the usual smooth compactly supported nonnegative prior.