## 1. Mathematical fidelity

### A. The setting does not yet support all the theorems stated

**1. The empirical normal form needs additional statistical hypotheses.**

> “We assume \(K\) is real analytic …”

and

> “on the resolution of \(K\) [the process] extends to a smooth function … and this extended process converges in law to a Gaussian process.”

Analyticity of the *expected* log-likelihood ratio does not imply analytic or smooth divisibility of the individual log-likelihood ratios, nor a functional central limit theorem. The hypotheses on \(p,q\) in §2.1 are insufficient for these assertions.

Write instead:

> “For the empirical results we additionally assume the analytic likelihood-ratio factorisation and moment hypotheses of [precise version of Watanabe’s standard-form theorem]. The population results require only the geometric and smooth-amplitude hypotheses stated above. Convergence of derivatives of the empirical field is a separate hypothesis.”

List those statistical hypotheses rather than referring only to a theorem number.

**2. The standardised field defined using \(\sqrt K\) need not extend smoothly across interior walls.**

> “The process \(\psi_n\) … on the resolution of \(K\) … extends to a smooth function.”

In the usual standard form, the smooth field multiplies a **signed monomial** \(u^k\), not necessarily \(|u^k|=\sqrt{K\circ\pi}\). Dividing by the latter can introduce sign jumps. A regular normal-location model already exhibits this problem.

Write:

> “The standard form supplies a smooth signed-root representative \(\xi_n\) with \(K_n\circ\pi=u^{2k}-n^{-1/2}u^k\xi_n\). The field obtained by dividing by \(\sqrt{K\circ\pi}=|u^k|\) is generally only orthantwise smooth.”

Make §9.1 consistent with this formulation; its present assertion of smooth extension followed by potentially unequal one-sided limits is contradictory.

**3. The empirical centring is misstated.**

> “Since \(L_n(w)-L_n^{\min}\) is, up to the constant … the empirical divergence \(K_n(w)\), the factor \(e^{-nL_n^{\min}}\) cancels …”

The exact identity is
\[
K_n(w)=L_n(w)+\frac1n\sum_i\log q(x_i).
\]
There is no need to introduce \(L_n^{\min}\), which is a different centring.

Write:

> “Since \(K_n=L_n+n^{-1}\sum_i\log q(x_i)\), replacing \(L_n\) by \(K_n\) multiplies numerator and denominator by the same sample-dependent constant. From now on \(Z_n\) denotes this renormalised partition function.”

**4. Exclude degenerate zero sets and irrelevant components.**

> “the truth is realisable: \(W_0=\{K=0\}\) is nonempty.”

This does not ensure a positive RLCT asymptotic under the stated geometric assumptions. For example, \(K\equiv0\) is allowed. Also, a compact semianalytic \(W\) can contain isolated, zero-volume components on which \(K=0\), while its positive-volume part stays away from zero.

Add hypotheses ensuring that \(K\) is not identically zero on relevant ambient components and that the zero locus is approached within the support of the integration measure. Minimise wall exponents only over the resolved integration domain and prior support, not all components with real points.

**5. Boundary resolution is not supplied by resolving \(K\) alone.**

> “the local picture on the real resolution is …”

For general semianalytic \(W\), you must also rectify the integration domain. Boundary components can have \(k_i=0\), and they need not be components of the divisor of \(K\).

Write:

> “We use a simultaneous rectilinearisation of the phase and integration domain. In each integration chart the active phase coordinates have \(k_i>0\); remaining coordinates, including phase-inactive boundary coordinates, are treated as parameters.”

Appendix D cannot simultaneously promise arbitrary boundary resolution and an isomorphism everywhere off \(\{K_{\mathbb C}=0\}\) without further qualification.

---

### B. Several geometric assertions confuse candidate orders with actual nonzero coefficients

**6. Comparability preserves the leading RLCT data, not the complete realised expansion.**

> “Comparable functions have … the same exponents and multiplicities in the expansions below.”

The common resolution gives the same divisorial orders and candidate pole data. Actual higher coefficients can vanish for one phase and not another. For example, a locally quadratic phase with constant amplitude can have no algebraic corrections, whereas a comparable nonquadratic phase generally has corrections.

Write:

> “Comparable phases have the same divisorial orders on a common resolution and the same leading RLCT and multiplicity for positive amplitudes. They have the same candidate pole data, but their actual nonzero subleading terms can differ.”

The same correction is needed in Appendix D.

**7. Vanishing on the deepest stratum need not raise the exponent.**

> “an observable vanishing on the axis, such as \(f=x^2\), is seen at a higher exponent”

This contradicts the correct later calculation:
\[
\mathcal Z_n[x^2]\asymp n^{-1/2},\qquad
\mathcal Z_n[1]\asymp n^{-1/2}\log n.
\]

Write:

> “An observable vanishing on the axis can lose the leading logarithm without changing the exponent; \(f=x^2\) gives precisely this behaviour.”

**8. Nonvanishing of a signed observable does not guarantee a nonzero coefficient.**

> “If \(f\circ\pi\) does not vanish identically on some exact stratum … the exponents and logarithmic degrees of numerator and denominator agree”

A signed observable can integrate to zero against the leading measure. Odd observables can have identically zero partition functions. Smooth flat observables can have no first nonzero algebraic term.

Throughout §§4, 6, 7.2, 7.10 and 11.3, replace assertions about the *first actual term* inferred solely from vanishing orders by:

> “These orders give candidate first terms. The stated asymptotic equivalence holds when the corresponding coefficient is nonzero; nonnegative observables positive on the relevant support provide a sufficient condition.”

Use an equality with an \(o(\cdot)\) remainder instead of “\(\sim\)” when the displayed coefficient might be zero.

**9. The wall-factorisation convention is wrong for odd orders on interior walls.**

> “\(f\circ\pi=\prod |u_i|^{l_i}\tilde f\) …”

For smooth \(f\), odd-order divisibility is by \(u_i^{l_i}\), not by \(|u_i|^{l_i}\) with smooth quotient across the wall.

Write \(u^l\tilde f\) in signed coordinates, or explicitly restrict the statement to an orthant. Also allow infinite-order vanishing rather than assuming every smooth observable has finite divisorial orders.

**10. The prose about moment exponents is incorrect at ties.**

> “Increasing \(\gamma_i\) in a direction attaining the minimum raises the exponent”

Not if another direction still attains that minimum: the logarithmic multiplicity drops instead.

> “increasing it in another direction leaves the exponent alone until that direction catches up.”

Increasing an already larger ratio moves it farther from the minimum.

Write:

> “Increasing a uniquely minimising ratio raises the minimum until another ratio takes over; increasing one member of a tied minimum first reduces its multiplicity; increasing a nonminimising ratio leaves the leading pair unchanged.”

Also change “its logarithmic degree is the number of directions attaining the minimum” to “one less than that number.”

---

### C. The blow-up example

**11. This example does not need a blow-up.**

> “an example where a blow-up is genuinely needed”

For \(K=x^2(x-y)^2\), the linear coordinates \(u=x,\ v=x-y\) already give \(K=u^2v^2\). The divisor is already normal crossing.

Write:

> “We also examine an optional blow-up of an already normal-crossing example, to show how a further resolution redistributes the same asymptotic data.”

If an essential blow-up is wanted, use a different example.

**12. The numerical blow-up data are correct, but the incidence description needs precision.**

The data
\[
(k_0,h_0)=(2,1),\qquad (k,h)=(1,0)
\]
for each strict transform, and all three ratios \(1/2\), are correct.

> “The three components meet in two points”

Write:

> “The exceptional curve meets each strict transform once, at distinct points; the two strict transforms are disjoint.”

For the pulled-back **density**, write \(|u|\,|du\,dv|\), not \(u\,du\,dv\).

**13. The claimed selective vanishing is false.**

> “an observable vanishing only on the line \(\{x=0\}\) shifts only the one strict transform”

Such an observable vanishes at the origin and therefore also along the exceptional curve after pullback. For \(f=x\), both the exceptional component and the strict transform of \(x=0\) acquire vanishing order one.

Write:

> “An observable vanishing along \(x=0\) shifts that strict transform and the exceptional component; the resulting minimum and tie multiplicity must be recomputed at both marked points.”

Repeat this correction in §4.3.

---

### D. The normal-geometry and moment-tensor construction has substantive problems

**14. The claimed fibre-constant partition of unity is not justified and is generally unavailable in the stated form.**

> “Such partitions exist for the same reason tubular neighbourhoods do”

and Appendix D:

> “pull them back … constant on fibres … and normalise.”

Normalising functions constant along different fibre projections does not preserve constancy along each projection. A nonzero fibre-constant function also cannot generally be extended by zero smoothly across the normal boundary of its tubular neighbourhood.

Replace this construction by an ordinary smooth partition of unity subordinate to resolved charts:

> “The cutoffs may depend on all chart coordinates and are included in the differentiated amplitude.”

That is already what the valid chart coefficient formulas require.

**15. Boundary strata do not have the ordinary normal-bundle tubular picture asserted in Appendix D.**

> “Each \(E_I\) is a neat submanifold … \(E_I\) meets the boundary transversely.”

A divisor component that *is* a boundary face is not transverse to that boundary. Its admissible normal directions form an inward cone, not a full vector-bundle neighbourhood.

Write a separate orthant/cone-bundle formulation, or keep the geometric discussion on the ambient real resolution and impose the integration-domain restrictions chartwise.

**16. The per-stratum Taylor expansion is not an asymptotic expansion in general.**

> Proposition 6.2: “\(\displaystyle \int\chi F e^{-nK}\cdots\sim\sum_{r\ge0}\cdots\)”

A finite Taylor expansion at a crossing does not control contributions along the entire adjacent walls. For \(K=x^2y^2\), take a smooth amplitude flat at \((0,0)\) but nonzero on \(y=0,\ x>0\). Every normal Taylor coefficient at the crossing vanishes, yet the integral has a nonzero \(n^{-1/2}\) term.

Thus the stated proposition is not rescued by adding a standard Taylor remainder estimate.

Replace it by:

> “Finite fibrewise Taylor expansion gives an exact identity with a remainder. For product phases this is not, by itself, an asymptotic expansion: contributions away from the zero section must be retained by facewise Taylor subtraction.”

Then derive actual coefficient statements from the face/Laurent construction. No cited Lean declaration proves the proposition as written.

**17. There is a factorial inconsistency.**

The definition of \(D_b\) already includes \(1/b!\), and \(D_\perp^r\) is their sum. Consequently the additional \(1/r!\) in (6.3) double-normalises the Taylor coefficients under the stated convention.

Either remove that \(1/r!\), or redefine \(D_\perp^r\) as the unnormalised symmetric derivative and revise the component formula consistently.

**18. Smooth Taylor series are written as convergent equalities.**

> “\(\displaystyle c(v,u)=\sum_\delta c_\delta(v)u^\delta/\delta!\)”  
> “\(\displaystyle \widetilde M_\gamma=\sum_\delta g_\delta M_{\gamma+\delta}/\delta!\)”

These are not equalities for general smooth data.

Write finite Taylor formulas with explicit remainders. Do not describe the infinite sum as convergent.

**19. The proposed tensor is not intrinsically defined by the displayed formula.**

> “the singular monomial weight \(|u|^{h_I}\) is kept separate”

That scalar weight depends on the choice of defining functions. The corresponding smooth density factor must transform with it. An arbitrary tubular map also does not automatically preserve the monomial phase.

Define tensor-valued fibre integrals using the **full pulled-back density** and the actual pulled-back phase. If a monomial computation is then made, specify the compatible chart and its transformation law. Avoid disintegration into a positive marginal where the cutoff makes the marginal vanish.

**20. Several claims of canonicity are reversed or overstated.**

> “the leading nonvanishing one is intrinsic, and the lower ones are intrinsic modulo the higher ones.”

Higher transverse derivatives generally depend on lower-order jets under nonlinear coordinate changes. The intrinsic statement is the associated-graded identification
\[
\mathcal I_S^r/\mathcal I_S^{r+1}\cong \operatorname{Sym}^rN^*S.
\]

> “\(\rho_\alpha\) is … valued in … the conormal bundle”

The coefficient pairing with a conormal jet is valued in the corresponding **normal** tensor bundle, tensored with densities.

> “when \(S\) is a single point … every term … is … canonical”

Point support does not make individual derivative-of-delta coefficients invariant under nonlinear coordinate changes.

Replace these passages with the associated-graded statement and distinguish the invariant distribution/principal symbol from a chosen derivative presentation.

---

### E. Stratum measures and residue normalisations

**21. The positive-box constants in the principal formulas are correct.**

The factors in (7.2), (7.3), and the zero-order residue normalisation are consistent:
\[
\frac{\Gamma(\mu)}
{(c-1)!\prod_{j\in J}(2k_j)\alpha_j!}.
\]
The one-variable full-line check
\[
\mathcal R_1^{1/(2k)}=\frac1k\delta_0
\]
is also correct.

Do not change these constants.

**22. The displayed \(2^c\) formula is not valid for boundary walls.**

> “\(\displaystyle \mathcal R_c^\mu=\frac{2^c}{\prod 2k_j}\operatorname{res}(\cdots)\)”

The accompanying prose mentions interior walls, but the equation is presented generally. For \(c_{\mathrm{int}}\) interior walls and the remaining walls one-sided, the factor is \(2^{c_{\mathrm{int}}}\), assuming the side limits agree. More generally, sum the densities of the permitted branches.

Write:

> “For two-sided interior walls with matching smooth density, the side factor is \(2^c\); in general the residue measure is the sum over the permitted normal orthants, with \((2k_j)^{-1}\) per wall.”

Similarly, the collar definition with \(2\log(1/\varepsilon)\) must use \(\log(1/\varepsilon)\) for a one-sided wall.

**23. The asymptotic-limit definition of the residue is false at a general exponent.**

> “the defining property is [equation (7.8)] for \(F\) vanishing near \(D_{c+1}\)”

The zero-order condition at \((\mu,c)\) does not eliminate contributions at smaller exponents. For instance, in a positive-box model \(K=x^4y^6\), take \(\mu=1/4,c=1\) and a test supported near \(y=0\), away from the origin and \(x=0\). It is admissible, the \(\mu\)-residue on \(x=0\) sees nothing, but the normalised integral grows like \(n^{1/4-1/6}\).

The truncated negative-moment limit has the same defect.

Write:

> “At a general exponent, \(\mathcal R_c^\mu\) is defined by coefficient extraction. The displayed un-subtracted limits apply only when all more dominant terms vanish, in particular at an appropriate leading pair.”

Alternatively subtract the more dominant terms explicitly.

**24. Do not reuse \(\eta\) inconsistently in the residue formula.**

In the graded formula \(\eta=\rho c(f\circ\pi)\); subsequently the face density is integrated against \(f\circ\pi\) again. Read literally, this inserts \(f\) twice.

Use a separate symbol, say \(a=\rho c\), for the density amplitude without the observable, and write the face measure using \(a\).

**25. A coefficient is not generally a smooth-density distribution on one open stratum.**

> “each coefficient … is a distribution supported on a stratum”

The correct support statement is the closed resonant set \(\{r_\mu\ge q+1\}\). Finite-part terms along open strata can have singular behaviour at their boundaries. The smooth-density conormal presentation applies locally away from deeper strata or to the admissible graded coefficient, not automatically to the entire coefficient.

Write:

> “Each coefficient is a distribution supported on the resonant zero fibre; on the depth-graded admissible tests it is represented by finite transverse jets integrated over the exact stratum.”

Use this formulation in the abstract, introduction and conclusion.

**26. The leading-measure theorem is later used outside its stated range.**

Theorem 7.8 assumes vanishing near \(D_{m+1}\), but §§7.10, 11 and 12 apply its measure formula to the denominator \(f=1\) without ensuring \(D_{m+1}=\varnothing\) or proving the needed extension.

Either impose that condition in those applications, or prove a global leading-measure identification that includes mixed-depth boundary points. The cited inequality
\(\nu(X)\le c_{\lambda,m-1}(1)\) is not itself that identification.

Also, the theorem’s sentence saying the “general” case follows from Theorem 7.4 is circular: Theorem 7.4 has the same admissibility restriction.

**27. The statement about a quotient class in the planes example is false.**

> “the class of \(c_{1/2,0}\) on observables modulo those vanishing near the axis”

The functional does not vanish on observables vanishing near the axis; on them it is precisely the nonzero plane-measure integral. It therefore does not descend to that quotient.

Write:

> “The complete \(c_{1/2,0}\) is canonical. Its restriction to observables vanishing near the axis is the plane-measure integral; its decomposition into plane finite parts and an axis term depends on conventions.”

---

### F. The three tiers, finite parts and running examples

**28. The finite-part formula needs a complete definition, including the compensating Taylor integrals.**

> “FP is … namely the subtraction of the Taylor polynomial …”

Subtraction alone is not the finite part. In one tangential variable, with \(a=h-2k\mu\) not a negative integer and \(N\) large enough,
\[
\operatorname{FP}\int_0^1g(w)w^a\,dw
=
\int_0^1\left(g(w)-\sum_{j=0}^N\frac{g^{(j)}(0)}{j!}w^j\right)w^a\,dw
+\sum_{j=0}^N\frac{g^{(j)}(0)}{j!(a+j+1)}.
\]
Use this formula and its iterated version, with the chosen boundary defining functions/cutoffs specified.

The positive sign in the displayed coefficient formula is correct. But:

> “This is the pairing with \(\delta^{(\alpha)}(u)\otimes\mathrm{FP}\cdots\)”

needs the factor \((-1)^\alpha\), since
\(\langle\delta^{(\alpha)},g\rangle=(-1)^\alpha g^{(\alpha)}(0)\).

**29. Both \(x^2y^2\) tie computations have the correct signs and constants.**

Per positive quadrant,
\[
c_{1/2,1}=\frac{A_{1/2}(0,0)}4,
\]
\[
c_{1/2,0}
=-\frac{\partial_sA_s(0,0)|_{1/2}}4
+\frac12\int_0^1\frac{A_{1/2}(x,0)-A_{1/2}(0,0)}x\,dx
+\frac12\int_0^1\frac{A_{1/2}(0,y)-A_{1/2}(0,0)}y\,dy
\]
is correct, with \(A_s=\Gamma(s)\eta\) or \(A_s=\eta S_s(\zeta)\).

Two editorial corrections are necessary:

* each quadrant uses its own pulled-back amplitude and root-field representative;
* “Integrating over \(z\) **against the prior**” double-counts the prior already included in \(\eta=\varphi f\); write “integrating over \(z\) and summing the quadrants.”

**30. The mixed-example exponents and integrability tests are correct, but “first correction” must mean candidate correction.**

For \(x^2y^6\) on \([0,1]^2\),
\[
\lambda=\frac16,\qquad \mu_1=\frac13,\qquad \mu_2=\frac12,
\]
and \(x^{-1/3},x^{-2/3}\) are both integrable at zero. The displayed coefficient at \(1/3\) is correct.

However:

> “the second correction … a logarithm appears there”

requires a nonzero second normal derivative. More precisely,
\[
c_{1/2,1}=\frac{\Gamma(1/2)}{24}\,\partial_y^2\eta(0,0)
\]
on the positive square in the population case.

For constant amplitude,
\[
\mathcal Z_n[1]
=\frac{\Gamma(1/6)}4n^{-1/6}
-\frac{\Gamma(1/2)}4n^{-1/2}
+O(e^{-\varepsilon n}),
\]
so there is neither an \(n^{-1/3}\) term nor an \(n^{-1/2}\log n\) term.

Write:

> “The first possible correction is at \(1/3\); the next possible exponent is \(1/2\), where a logarithmic term is allowed and is present when the indicated second derivative is nonzero.”

**31. The population parity statement is correct in its proper scope; its empirical extension is not.**

> “on a symmetric domain … the odd normal moments cancel”

For the population monomial phase and the full smooth amplitude, yes: odd normal Taylor terms cancel between matching sides.

> “the first nonzero correction is the one with the logarithm”

No: the constant-amplitude calculation above remains a counterexample on the symmetric square, multiplied by four.

Also, arbitrary empirical root-field representatives on opposite sides need not give matching weights. An odd amplitude derivative can couple to the odd part of the empirical exponential and survive.

Write:

> “For the population integral, symmetric two-sided integration removes odd normal Taylor terms. Thus the \(1/3\) candidate vanishes in the symmetric mixed example; the next candidate is \(1/2\), with a logarithm only if its coefficient is nonzero. Empirical parity requires compatible reflection symmetry of the field as well.”

---

### G. Fluctuation function, Weber equation and empirical coefficients

**32. The Weber substitution and closed form are correct.**

The stated substitution gives
\[
f''+\left(\frac12-2\mu-\frac{z^2}4\right)f=0,
\]
and
\[
S_\mu(a)=2^{1-\mu}\Gamma(2\mu)e^{a^2/8}
D_{-2\mu}(-a/\sqrt2).
\]
The ladder, recurrence, incomplete-function equation and one-dimensional coefficient formula also have the stated normalisations.

Do not change these formulas.

**33. The Weyl-algebra discussion needs qualification.**

> “every fluctuation function is a derivative of \(e^{a^2/4}\operatorname{erf}(a/2)\)”

For the positive half-integer orbit, the seed is the **full**
\[
S_{1/2}(a)=\sqrt\pi e^{a^2/4}(1+\operatorname{erf}(a/2)),
\]
not the erf term alone.

The positive half-integer span is not closed under \(b\) unless constants/polynomials are adjoined, because \(bS_{1/2}=2\). At nonpositive half-integers the meromorphic continuation has poles, not ordinary functions to include indiscriminately in a span.

Write:

> “The space \(\mathbb C[a]+\operatorname{span}\{S_{(n+1)/2}:n\ge0\}\) is stable under the operators; modulo the polynomial submodule it has a lowest-weight vector represented by \(S_{1/2}\).”

The claim that Weber’s equation is “the source” of the statistical equations of state should be replaced by a precise derivation/reference or removed.

**34. The weighted-residue shorthand is used beyond its definition.**

> “the normal jet of order \(\alpha\) … integrated against … \(\mathcal R_c^\mu\)”

Your \(\mathcal R_c^\mu\) has only been defined under the zero-order condition, where \(\alpha=0\). For positive normal orders, write “against the chart residue data of the differentiated amplitude,” or define a separate tensor-valued/higher-pole object.

**35. Root-field reweighting must remain branchwise.**

> “\(S_\lambda(\hat\psi)\,d\mathcal R_m^\lambda\)”

If the representatives differ on the two sides, \(\hat\psi\) is not a single function on the underlying stratum. An unweighted side-summed measure cannot simply be multiplied by one chosen value.

Write the leading coefficient as a sum over side-labelled strata, or define the empirical measure by summing the branchwise weighted residues. Collapse to the displayed pointwise reweighting only when branch representatives agree.

**36. “Fixed sample” must be separated from the diagonal sample-size limit.**

> “Fix the sample … as \(n\to\infty\)”

The actual field \(\psi_n\) changes with \(n\). State the deterministic theorem for an independent parameter \(N\to\infty\) and a fixed field \(\zeta\), then evaluate its uniform expansion at \((N,\zeta)=(n,\psi_n)\).

Likewise:

> “the normalised remainders … converge accordingly”

does not follow merely from coefficient convergence. Tightness of the relevant jet norms gives \(O_P\) remainder bounds; convergence to zero requires an appropriate stronger normalisation or deeper cutoff. State the precise probabilistic conclusion.

---

### H. Gaussian averaging, posterior quotients and leading expectations

**37. The Gaussian average and threshold are correct.**

For \(\mu>0\) and \(v\ge0\),
\[
\mathbb E S_\mu(N(0,v))
=\Gamma(\mu)(1-v/2)^{-\mu}\quad(v<2),
\]
and the nonnegative expectation is infinite for \(v\ge2\), including equality.

**38. The conclusion about finite-sample expected evidence is false.**

> “the expected partition function is infinite, although every sample partition function is finite.”

The Gaussian limiting coefficient can have infinite mean; this does not imply infinite expectation of the finite-\(n\) evidence.

Indeed, for the renormalised \(K_n\) used in this paper, under the common-support realisable model,
\[
\mathbb E_{\mathcal D_n}e^{-nK_n(w)}
=\prod_{i=1}^n\mathbb E_q\frac{p(X_i\mid w)}{q(X_i)}=1,
\]
and hence
\[
\mathbb E Z_n[1]=\int_W\varphi(w)\,dw.
\]

Write:

> “The Gaussian limiting leading coefficient may fail to be integrable, demonstrating failure of uniform integrability and of exchanging the asymptotic limit with expectation.”

For an integrated Gaussian leading coefficient, a bad variance on a set of positive residue measure is sufficient for divergence; a bad value at a null set alone is not.

**39. The Wick condition is sufficient, not an equivalence with pointwise variance \(<2\).**

> “which is the condition \(W<2\) in jet form”

An exponential moment of the supremum norm of a jet is much stronger than pointwise variance inequalities. Also, in the cited Wick theorem \(W\) is the variance of \(u^k\zeta\), whereas the exponential moment controls jets of \(\zeta\).

Write:

> “This exponential jet-norm condition is a sufficient uniform integrability hypothesis; it is not equivalent to the pointwise scalar threshold.”

**40. The quotient exponent \((d-1)(J+1)\) is correct.**

It matches the supplied Lean statement with \(D=d-1\). The missing explicit algebraic hypotheses are \(Q>0\), a common base exponent, and vanishing of both coefficient systems below it. For a bounded posterior observable the latter follows from
\[
|Z_n[f]|\le\|f\|_\infty Z_n[1].
\]

Appendix C contains a literal contradiction:

> “\(|1/B_0|\le C(1+\ell)^0\) is not available, only \(|1/B_0|\le C\)”

These are identical. Replace the sentence by:

> “Since \(B_0\) is a nonzero polynomial, \(1/B_0(\ell)=O(1)\) as \(\ell\to\infty\); the displayed logarithmic growth is a coarse bound for the finite products in formal division.”

Also, rational-log quotient expansions are an enlargement of the scale defined in §2.3, not expansions in that original nonnegative-log-power scale.

**41. The empirical assertion for \(f=K\) is false.**

> “\(\mathbb E[K\mid\mathcal D_n]\sim\lambda/n\) with the fluctuation factors cancelling”

They do not cancel. Under the leading radial description,
\[
\mathbb E[K\mid\zeta]
\sim
\frac1n
\frac{\int S_{\lambda+1}(\zeta)\,d\rho}
{\int S_\lambda(\zeta)\,d\rho},
\]
with the branchwise interpretation above.

For the full-line regular integral \(e^{-nx^2+\sqrt n\,ax}\),
\[
\mathbb E[x^2]=\frac{1/2+a^2/4}{n}.
\]

Replace the claimed cancellation with the ratio formula. The population statement \(\mathbb E_\infty[K]\sim\lambda/n\) is correct.

**42. Sample independence at a single leading point is correct only as a leading-value statement.**

> “When the leading stratum is a single point, the reweighting cancels”

Yes, provided the leading measure description applies and its whole support projects to that point. More generally the same holds when the observable is constant on the support of the leading measure.

Write:

> “For a frozen field, the leading posterior expectation of a smooth observable is its value at the image of that point, independently of the field. The first nonzero correction can still depend on the sample.”

Do not infer convergence for arbitrary unbounded sequences of sample fields. For the actual sampling sequence, use the relevant tightness/probabilistic theorem.

**43. The two-site identity is correct, but its hypotheses need correction.**

The identity and interval bound are correct for \(0<p<1\), positive measurable weights, and an exchangeable joint law. Endpoint cases are trivial and should be treated separately.

> “exchangeable, which is the case when the two field values have the same variance”

Equal variance alone does not imply exchangeability. It does for a **jointly centred Gaussian pair**, since its covariance matrix is invariant under swapping coordinates.

Write that qualification explicitly.

**44. Wall-crossing with data cannot exclude coefficient cancellations.**

> “The exponents and logarithmic degrees … do not depend on the sample.”

The candidate exponents and maximum logarithmic degrees do not. Actual coefficients may vanish for particular fields or observables.

Write:

> “The resolution determines the candidate support of the expansion independently of the sample; sample-dependent cancellations can remove candidate terms.”

**45. Section 12 applies compact-base theorems to a generally noncompact stratum.**

> “\(g\mapsto\langle f\rangle_g\) … on \(C(S,\mathbb R)\) with the sup norm”

An exact stratum is generally noncompact, and not every continuous function on it is bounded. The cited Lean theorems use a compact base.

Add a standing hypothesis:

> “In this section the base is a compact space carrying a finite nonzero measure, the field is a Gaussian random element of \(C(S)\), the covariance kernel is continuous and PSD, and \(\mathbb E\|G\|_\infty^2<\infty\).”

Then either construct such a compact, possibly side-labelled base from the leading geometry or leave that identification explicitly conditional.

The displayed Fréchet, Stein and three-replica interpolation formulas agree with the supplied signatures at \(\beta=1\), including the sign after relabelling replicas and the numerical bound. They are not justified on the current unrestricted \(S\).

**46. Posterior variance is a susceptibility only for the matching source.**

> “The posterior variance is the susceptibility … response … to a perturbation of the data”

For a tilt by \(\varepsilon f\), the response of \(\mathbb E[f]\) is \(\operatorname{Var}(f)\). For a general data perturbation, it is a covariance with the perturbing score, not necessarily that variance.

State the specific perturbation before making the identification.

---

## 2. Formalisation table

### Scope of this audit

The supplied text consists of source-header excerpts, not complete elaborated `#check` output with all section variables. In particular, the two-site declarations display no hypotheses even though their conclusions cannot hold without them. Thus hidden ambient assumptions cannot be certified from these excerpts.

Two named declarations have **no supplied signature**:

* `ResolvedData.coeff`;
* `boundedInProbSeq_posteriorMean_allOrders`.

Mark those rows unverified until their complete signatures are supplied. The axiom-dependency claim also cannot be checked from theorem statements; provide the audit output and the commits of all bridge dependencies.

### Row-by-row corrections

| Table row | Comparison with supplied signatures; required edit |
|---|---|
| **Chart expansion — population** | Supported after specialising \(\beta=b=1\), with \(h_i\in\mathbb N\), \(k_i>0\), and ambient `ContDiff`. State these conventions. Uniqueness is asserted on the lattice and within the degree bound, not for arbitrary \((\mu,q)\). |
| **Resolved coefficients** | `coeff_eq_of_transports` requires two `NormalisedCoreTransport`s, measurable \(K\), smooth nonnegative compactly supported prior, and smooth observable. `coeff_comp_gv` is compatibility of pullback-observable coefficients, not independently a theorem about arbitrary resolution changes. Replace the row with those statements; supply `ResolvedData.coeff`. |
| **Support** | Matches neighbourhood-vanishing on the closed resonant zero fibre. Do not describe this as support on one open stratum. |
| **Graded stratum formula** | The three signatures support the top coefficient and its constant. They do **not explicitly state** vanishing of all degrees \(\ge c\); cite that theorem separately. The chart theorem uses `JetsZeroOn`, while the resolved theorem uses neighbourhood vanishing. Explain the implication. |
| **Jet dependence** | The signatures require both functions smooth and both vanishing near the deeper set, with \(c\ge1\). Add these hypotheses to the row. The quotient declaration supports descent once its domain/kernel definitions are supplied. |
| **Stratum measure** | **Wrong declaration name/namespace:** the supplied `stratumMeasure` from `MomentKernelData.lean` takes a component set \(I\) and returns a measure on `R.Stratum I`; it is not the zero-order coefficient measure used by the other two declarations. Cite the fully qualified declaration from `SmoothStratumMeasure.lean`. Representation and regular-measure uniqueness are supported; transport independence and the support/Radon assertions need their own declarations or explicit structure fields. |
| **Residue** | Chart-measure equality additionally assumes \(\mu>0\). Add this. These signatures identify measures constructed from charts; they do not formalise an independent manifold-level iterated density-residue operation. |
| **Leading term** | The normalised limit has the stated admissibility condition. Positivity separately requires a nonnegative observable and positive value at a realiser. The supplied mass theorem proves only the inequality; the equality when the deeper set is empty needs another citation or an explicitly stated deduction. |
| **RLCT** | Add nonempty zero fibre and the precise prior-positivity hypothesis on zeros in `tsupport prior`, together with the ambient resolved-data assumptions. |
| **Ladder, Weber** | The derivative and recurrence are supported for positive \(\beta,\mu\). `fluctuation_ode` itself is an algebraic recurrence in shifted fluctuation functions; the derivative interpretation requires the derivative theorem. No listed signature gives the erf closed form, the parabolic-cylinder closed form or the Weber substitution. Add declarations or label these as analytic derivations. |
| **One-dimensional expansion** | Add \(k>0,b>0\), integer \(q,L\), \(2kL\le q+1+h\), and the eventual lower bounds on \(N\). The explicit uniform theorem assumes bounds on `jetPoly`, not merely an unspecified smoothness norm. `empOneDimCoeff_one` gives only the first correction; cite the general coefficient-definition identity for the claimed all-\(j\) formula. |
| **Chart expansion — empirical** | Add \(k_i>0\). The uniform theorem is linear in a `FieldJetBound` constant, with field bound \(M'\) fixed; it is not linear in an arbitrary joint \(C^R\) norm without a further estimate. State the exact bounded quantity. |
| **Resolved expansion** | Matches a smooth root-field object plus a global bound. Zero-field equality is supplied only on the common lattice and within `commonD`; say so. |
| **Graded empirical formula** | Add \(\mu>0,c\ge1,k_i>0\), and distinguish chart `DeepVanishing` from resolved neighbourhood vanishing. Again, degrees \(\ge c\) vanishing are not explicitly in these displayed conclusions. |
| **Empirical leading term** | The integral theorem requires `IsTest m Ξ.F`, not merely membership in the broad class denoted \(\mathcal I_{m+1}\). State what `IsTest` includes and prove the required implication for your observables. Both theorems also require `ChartLeading`, \(m\ge1\), and bounded field; the integral version assumes \(\lambda>0\). |
| **Generic first correction** | Matches the formulas under the strict gap and \(k_i>0\). The assertion about all other coefficients is limited to lattice exponents and the specified logarithmic range. |
| **Two-dimensional tie** | Matches the constant-field, constant-amplitude positive-square example and its \(o(n^{-1/2})\) remainder. It does not cover the nonconstant-amplitude formulas in §§7.9 and 9.4. |
| **Generating identity** | Matches on lattice exponents and \(q\le d-1\), with \(k_i>0\) and smooth data. The signature uses the equivalent form with \(\eta\zeta^r\) and \(h\mapsto h+rk\). Include those range conditions. |
| **Mellin–Laurent characterisation** | “Any cutoff expansion” is too broad. Both declarations require local integrability on \((0,\infty)\) and boundedness near zero; the decomposition additionally assumes a lower support bound and a strip condition. `polarCoeff_unique` assumes a bounded remainder after subtracting the proposed pole. Put these hypotheses in the row. |
| **Coefficient continuity** | The citations concern the **top depth-graded coefficient**, with admissible observable, \(\mu>0,c\ge1\), and specified chart jet bounds. They do not establish the body’s unrestricted claim for every lower-log coefficient. Limit convergence is conditional on convergence in law of `RealizableJets`. Narrow the row and the body, or cite additional results. |
| **Gaussian average** | `integral_fluctuation_gaussianReal'` proves integrability and the finite formula only under \(1-\beta v/2>0\). It does **not** state divergence otherwise. Cite a nonintegrability/extended-integral theorem for that half of the row. The Wick theorem additionally needs Gaussian-process structure, smooth nonnegative variance profile, the scaled-field Gaussian laws, measurability conditions, and a sufficiently high jet order. “Under an exponential moment” omits substantial hypotheses. |
| **Quotient to all orders** | The remainder exponent matches. Add \(Q>0\), common base \(m_0/Q\), `VanishBelow` for both expansions, and \(J\ge1\). The in-probability declaration is missing from the supplied signatures and cannot be checked. |
| **Connected coefficients** | The algebraic second-source identity is supported. The variance theorem additionally assumes `BoxLeading`, a base exponent no larger than \(\lambda\), and a nonzero denominator block there. Its displayed remainder has logarithmic exponent \((d-1)(2J+2)\), not the mean quotient’s exponent. This row does not certify every higher cumulant assertion. |
| **Two-site balancing** | The conclusions match. The excerpts omit the assumptions entirely; provide elaborated signatures showing \(p\), positivity, measurability, probability measure and exchangeability assumptions. State \(0<p<1\) or explain endpoint conventions. |
| **Fréchet derivative, Stein** | Add positive \(\beta,\lambda\), finite nonzero base measure, continuous observables, and the precise `GaussianField` assumptions. The derivative theorem itself needs no Gaussian hypothesis. The body must be restricted to the compact-base setting. |
| **Interpolation** | The three displayed identities/bounds match at \(\beta=1\), after replica relabelling. The bound explicitly assumes \(\rho\ne0\) and a nonnegative diagonal bound; include these. |
| **Inverse evidence** | “All moments finite” omits the essential measurable \(C(K)\)-valued Gaussian random element, positive \(\beta,\lambda\), and nonzero base measure. The theorem proves nonnegative powers of the inverse; state that. |
| **Quenched source** | The stated bound and first two derivative identities are supported subject to the ambient assumptions and \(\rho\ne0\). The radius-of-convergence claim in §12 is not among these signatures; provide its elementary proof or another declaration. |

### Body statements requiring proof, restriction or removal

Do not classify every unformalised statement as an open mathematical problem. The finite-part evaluation, nonconstant \(x^2y^2\) computation, Weber reduction and Gaussian integration identities can be proved directly and belong to established analytic machinery.

The genuinely unsupported issues here are:

* the **false** per-stratum asymptotic Taylor proposition;
* the fibre-constant partition construction;
* unrestricted continuity and convergence claims for **all** coefficients when the citations cover admissible top coefficients;
* the passage from the potentially noncompact, branch-dependent geometric leading object to the compact-base Gaussian posterior;
* jet-level empirical-process convergence under the paper’s currently insufficient statistical assumptions.

For the last two, state conditional theorems and identify the missing bridge. Do not claim either a formal theorem or an established literature theorem under the present hypotheses.

---

## 3. Structure and exposition

### A. Put the actual invariant object before its presentations

> “every coefficient is a distribution on a stratum”

This opening promises a stronger and cleaner geometry than the paper establishes.

Replace the opening description by the hierarchy actually proved:

1. a canonical coefficient distribution supported on the resonant zero fibre;
2. its restriction to admissible depth-graded observables;
3. its finite transverse-jet representation;
4. a positive measure under zero-order hypotheses;
5. chart formulas computing these objects.

That makes the three actors precise: the observable is a test, the strata organise support and jets, and the field changes the coefficient functional.

### B. Introduce admissibility before promising per-stratum coefficients

> §6: “Collecting the terms … gives a functional … with \(\rho_\beta\) smooth densities on \(S\).”

The reader learns only in §7.3 that deeper crossings can make these integrals divergent and that admissibility is required.

Move the explanation of deeper-face divergence and admissible observables before this claim. The \(x^2y^2\) plane density \(dx/|x|\) is the shortest motivation: it explains both why a measure exists away from the axis and why a finite part is needed globally.

### C. Separate the two meanings of “exact”

> §4.2: “all normal directions share the same ratio … exact”

versus

> §7.3: “all … walls resonate”

These differ at higher normal orders. Use “zero-order exact” for equal unshifted ratios, and “\(\mu\)-resonant exact” for the shifted condition, or reserve “exact” for the later definition and introduce it only once.

### D. The moment-tensor detour currently obstructs the primer

Sections 5–6 introduce tubular neighbourhoods, disintegration and tensor moments before demonstrating a computation that requires them. They then fail to provide the general asymptotic reduction claimed.

Retain the conormal splitting and ideal-jet interpretation. Move the optional tensor-moment construction after the valid graded formula, with its choices and limitations explicit. The motivating question should be:

> “Why does the chart derivative formula define a coordinate-independent functional?”

That question is answered by jets and coefficient uniqueness; it does not require the invalid global Taylor summation.

### E. Consolidate wall-crossing

§4.3, §7.10 and §11.5 repeat the same narrative, sometimes with incompatible claims.

* In §4.3, give only the elementary shifted-ratio computation and the distinction between exponent increase and logarithm loss.
* In §7.10, compute the population quotient for the running examples.
* In §11.5, state only what changes with data: coefficients and possible cancellations, not candidate pole locations.

Remove repeated general claims about all observables having a definite shifted first term.

### F. Consolidate the three tiers

§7.9 and §9.4 substantially duplicate the finite-part and tie derivations.

Use a common notation \(A_s\), with
\[
A_s=\Gamma(s)\eta
\quad\text{or}\quad
A_s=\eta S_s(\zeta),
\]
and perform the Laurent calculation once. In §9.4, display only the resulting field-derivative terms and explain their statistical meaning.

Explicitly label the three levels:

1. zero-order residue measure;
2. one resonant wall, higher normal order, possibly finite part;
3. tied walls, with lower Laurent coefficients.

Currently “three tiers” is announced without a sufficiently stable three-part organisation.

### G. Make the examples carry the hypotheses, not just the pictures

For \(x^2y^6\), work with:

* constant amplitude, showing that candidate corrections can vanish;
* an amplitude with nonzero first \(y\)-derivative, producing the \(1/3\) term;
* an amplitude with nonzero second \(y\)-derivative, producing the \(1/2\) logarithm.

For \(x^2y^2\), use the same amplitude convention throughout and explicitly distinguish positive-quadrant formulas from their full-domain sum.

For the blow-up example, present it as invariance under an additional blow-up, not as an essential resolution.

### H. Move the special-function representation theory out of the main route

The ladder is needed for empirical coefficients; the Weyl-module discussion is not. Keep the ODE and one sentence giving the parabolic-cylinder closed form in §8. Move the orbit/module material to Appendix B, after correcting it.

### I. Separate the frozen-field theorem from statistics at the start of Part III

The current order repeatedly says “fixed sample” while using \(n\to\infty\), then qualifies the meaning later.

Introduce three distinct objects immediately:

* \(Z_N(\eta;\zeta)\), deterministic with frozen field;
* \(Z_n(\eta;\psi_n)\), the empirical diagonal;
* the limiting random functional evaluated at \(G\).

This removes ambiguity from §§9–12 and makes the role of uniform remainders visible.

### J. Part IV contains two different projects

The quotient and source-cumulant algebra directly answer the paper’s central question. Compact-base Gaussian interpolation studies a further limiting model whose identification is still conditional.

Keep §11 in the main development. Either move the detailed Stein/interpolation identities to an appendix or label §12 explicitly:

> “A conditional compact-base Gaussian limit model.”

The two-site calculation belongs naturally there, after the limiting weights are defined.

### K. Replace the blanket formalisation claim

> “The statements of this paper have been formalised …”

Write:

> “The chart expansion, specified resolved coefficient constructions, quotient algebra, and compact-base Gaussian identities have formal counterparts listed below. The geometric and statistical identifications not covered by those declarations are stated separately.”

Use fully qualified declaration names, repository commits and complete elaborated signatures.

### L. Acknowledge the subsumed paper explicitly

The related-work section does not identify Gerraty–Murfet’s earlier paper or distinguish inherited results from the present extension.

Add a short paragraph explaining which population/geometric results are subsumed, which empirical and averaging results are new, and that the present treatment uses smooth finite-order jets rather than the earlier Taylor-tree presentation. There is no reason to restore the dropped material.

---

## 4. Prioritised fix list

1. Replace the false per-stratum asymptotic Taylor proposition and fibre-constant partition construction with the valid chartwise face-subtraction argument.
2. State the additional statistical standard-form hypotheses and distinguish signed-root representatives, orthantwise fields, frozen asymptotics and the empirical diagonal.
3. Correct the empirical \(f=K\) expectation and the false inference from an infinite Gaussian limiting mean to infinite finite-sample expected evidence.
4. Restrict residue-limit formulas to leading situations or subtract all more dominant terms, and replace the universal \(2^c\) factor by the permitted-side sum.
5. Resolve the gap between admissible leading-stratum measures and their unrestricted use in posterior denominators and the compact-base Gaussian model.
6. Rewrite claims about exponents, wall-crossing and parity in terms of candidate terms, explicitly allowing signed cancellations, flatness and absent logarithms.
7. Correct the blow-up example’s “genuinely needed” claim and its erroneous assertion that vanishing along one original line leaves the exceptional component unshifted.
8. Repair Table 1 using fully qualified declarations, complete hypotheses and elaborated signatures, including the wrong `stratumMeasure` citation and the two missing signatures.
9. Consolidate the tier computations and wall-crossing discussions, and move the optional moment-tensor, Weyl-module and Gaussian-interpolation machinery out of the main explanatory route.
10. Reframe the abstract, introduction and conclusion around canonical resonant-support distributions and their admissible graded representations, while explicitly acknowledging the subsumed Gerraty–Murfet paper.