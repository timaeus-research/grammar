## Verdict

**Yes: `emp_cutoffExpansion` is the right deterministic empirical expansion theorem on a normal-crossing box.** The general-\(G\) state-density design is an improvement over the constant-field design: it preserves linearity and makes the face-flatness estimates compositional.

There are three qualifications worth recording:

1. This is the **box expansion**, not yet the empirical stratum identification or the resolved/random-field theorem.
2. With your definition of `mellinMom`, the identification with derivatives in the Mellin exponent has a **sign \((-1)^\ell\)**.
3. Mellin integration commutes with `faceAmp` **including its remainder operator**. Removing that remainder requires the deep-locus vanishing hypothesis; it is not an unconditional Mellin identity.

I am auditing the statements you supplied, rather than inspecting the repository implementation. In particular, below I distinguish the mathematical mechanism for removing \(R_K\) from any claim about the exact internal proof script of `smoothCoeff_eq_faceSum_top`.

---

## (a) Audit of the box theorem

### Hypotheses and chart applicability

Global `ContDiff ℝ ∞` is acceptable as an engine convention, particularly since the population engine uses it.

For the chart application, add an adapter:

> A function smooth on an open neighbourhood of the compact closed box has a globally smooth representative agreeing with it on a neighbourhood of that box.

Choose a smooth cutoff supported inside the neighbourhood and equal to one near the box, multiply, then extend by zero. Do this for both amplitude and field. Agreement on a neighbourhood preserves all relevant jets, not merely the integral.

This avoids weakening every engine theorem to `ContDiffOn`. It does assume that the chart representatives genuinely extend smoothly across the relevant boundary faces; smoothness only on the open positive box would not suffice.

### Spectrum and logarithmic degree

The lattice and degree are correct, with \(k_i>0\) and the nonnegative integral weight conventions in your development:

\[
\mu=\frac{h_i+m_i+1}{2k_i}
\quad\Longrightarrow\quad
\mu\in (2\prod_i k_i)^{-1}\mathbb N,
\qquad \deg_{\log N}\le d-1.
\]

The field does **not enlarge the ambient spectral lattice**. At fixed coupling parameter, its normal derivatives produce polynomial factors in \(\tau\); after Mellin integration these shift the order of \(S\), not the outside power \(N^{-\mu}\). It can change coefficients and cancellations, and hence the first nonzero term, but not introduce new permitted exponents or higher logarithmic degrees.

The ambient lattice is deliberately larger than the actually supported spectrum.

### Coefficient structure and lower logarithms

Your coefficient construction has exactly the expected two sources of logarithmic mixing:

1. **Inner Mellin mixing**, from
   \[
   (\log t-\log s)^j
   =\sum_{q=0}^j\binom jq(\log t)^q(-\log s)^{j-q}.
   \]
   This produces `mellinMom G μ (j-q)`.

2. **Outer face mixing**, from
   \[
   \log(Nw^{2k_K})=\log N+S(w).
   \]
   This produces the powers of \(S(w)\) in `faceCoeffInt`.

Thus lower coefficients contain both exponent derivatives of fluctuation functions and geometric logarithmic weights on the complementary face.

**Sign correction:** writing \(S_\nu(a)\) for \(\beta=1\),
\[
\boxed{
\operatorname{mellinMom}(\tau\mapsto\tau^r e^{a\tau})\,\mu\,\ell
=
(-1)^\ell
\left.\partial_\nu^\ell S_\nu(a)\right|_{\nu=\mu+r/2}.
}
\]
This requires \(\mu+r/2>0\). Your stated unsigned identity is not correct for the convention \((-\log s)^\ell\).

At the graded top power under the depth-support hypothesis, the proposed population comparison is correct:
\[
\partial_J^\alpha\eta
\quad\rightsquigarrow\quad
\frac{\partial_J^\alpha[\eta\,S_\mu(\zeta)]}{\Gamma(\mu)}.
\]
Here \(\mu\) is held fixed during spatial differentiation. This is a **graded-top comparison**, not a replacement rule for every coefficient.

### Scaling, normalization and \(\beta\)

There is no intrinsic unit-box obstruction. For \(v_i=b_i u_i\), put
\[
A_b=\prod_i b_i^{h_i+1},
\qquad B_b=\prod_i b_i^{2k_i}.
\]
Then
\[
Z_b(N;\eta,\zeta)
=A_b Z_1(B_bN;\eta\circ b,\zeta\circ b).
\]
The coupling transforms correctly because
\[
\sqrt N\,v^k=\sqrt{B_bN}\,u^k.
\]
**No additional scaling of \(\zeta\) is needed in this convention.** For a common side length \(b\), \(B_b=b^{2\sum_i k_i}\); a monomial is homogeneous even when the \(k_i\) differ.

For the convention
\[
e^{-\beta Nv^{2k}+\beta\sqrt N\,v^k\zeta(v)},
\]
use \(N'=\beta N\) and \(\zeta'=\sqrt\beta\,\zeta\), assuming \(\beta>0\).

What remains substantive is the chart identity matching the paper’s empirical contrast to
\[
Nv^{2k}-\sqrt N\,v^k\zeta_n(v).
\]
That identity must explicitly account for signs, analytic units, branch choices and normalization. The box theorem neither supplies nor assumes away that factorization.

---

## (b) Graded identification

### 1. The precise top state-density coefficient

Let \(J\ne\varnothing\), \(s=|J|\), and
\[
\lambda_i=\frac{e_i+1}{2k_i},\qquad
r=\#\{i\in J:\lambda_i=\mu\}>0.
\]

Separate the Jacobian factor from the density representation:
\[
\int_{(0,1]^J}u^e F(u^{2k})\,du
=
\left(\prod_{i\in J}\frac1{2k_i}\right)
\int_0^1 F(z)\rho(z)\,dz,
\]
where
\[
\rho(z)=\sum_{\nu,j}a_{\nu j}z^{\nu-1}(-\log z)^j.
\]

Then
\[
a_{\mu j}=0\quad(j\ge r),
\]
and
\[
\boxed{
a_{\mu,r-1}
=
\frac1{(r-1)!}
\prod_{\substack{i\in J\\\lambda_i\ne\mu}}
\frac1{\lambda_i-\mu}.
}
\]

This follows equally from the partial fractions of
\[
\prod_{i\in J}(s+\lambda_i)^{-1}.
\]
If your `coeffAt(rep)` uses the normalization above—as the displayed formula for `empInnerCoeff` indicates—this is its top-coefficient formula. The factor \(\prod(2k_i)^{-1}\) belongs outside `coeffAt`, not inside it.

For the graded proof, the important specialization is **all coordinates resonant**:
\[
r=s,\qquad
a_{\mu,s-1}=\frac1{(s-1)!}.
\]
Consequently,
\[
\boxed{
\operatorname{empFaceCoef}_{J,e,G}(\mu,s-1)
=
\frac{\prod_{i\in J}(2k_i)^{-1}}{(s-1)!}
\,\operatorname{mellinMom}(G,\mu,0)
}
\]
when every \(\lambda_i=\mu\), and it is zero at degree \(s-1\) otherwise.

The partial-resonance product formula is useful, but **not needed** to land the graded theorem.

### 2. The unconditional Mellin identity retains \(R_K\)

Define
\[
H_\mu(v)=\eta(v)S_\mu(\zeta(v)),\qquad \mu>0.
\]
The correct unconditional identity is
\[
\boxed{
\operatorname{mellinMom}
\bigl(\tau\mapsto
\operatorname{faceAmp}\,p\,J
(\operatorname{fieldFam}\eta\zeta\,\tau)\,\alpha\,w\bigr)
\,\mu\,0
=
\operatorname{faceAmp}\,p\,J\,H_\mu\,\alpha\,w.
}
\]
Equivalently, its right side is
\[
(R_K^p\partial_J^\alpha H_\mu)(0_J,w).
\]

Separately, for the plain derivative,
\[
\boxed{
\operatorname{mellinMom}
\bigl(\tau\mapsto
\partial_J^\alpha[\eta e^{\tau\zeta}](0_J,w)\bigr)
\,\mu\,0
=
\partial_J^\alpha H_\mu(0_J,w).
}
\]

Both follow by differentiation under the integral, using the field-jet bounds. The first additionally commutes the finite Taylor operations—and their evaluations—with the integral.

### 3. Why \(R_K\) disappears under deep-locus vanishing

The clean mechanism is **vanishing Taylor jets**, not cancellation of weighted integrals.

Assume \(\eta\) vanishes near the locus of depth at least \(c+1\). Then \(H_\mu\), and also \(\eta e^{\tau\zeta}\) for every fixed \(\tau\), vanish there.

For \(|J|=c\), set
\[
f(w)=\partial_J^\alpha H_\mu(0_J,w).
\]
For every \(i\in K\), the locus \(w_i=0\) inside this face has at least \(c+1\) zero coordinates. Therefore all Taylor jets of \(f\) in coordinate \(i\) at that coordinate hyperplane vanish:
\[
T_i^{p_i}f=0.
\]
Hence
\[
R_K^p f=\prod_{i\in K}(1-T_i^{p_i})f=f.
\]

This is the mechanism consistent with your reported `jetsZeroOn_amp_deep` and final population formula. There is no need for a coordinate Taylor polynomial to integrate to zero against a singular weight.

Indeed, you can apply this mechanism **before Mellin integration**, obtaining
\[
\operatorname{faceAmp}\,p\,J
(\operatorname{fieldFam}\eta\zeta\,\tau)\,\alpha\,w
=
\partial_J^\alpha[\eta e^{\tau\zeta}](0_J,w)
\]
for \(|J|=c\). That is likely the shortest graded proof.

### 4. Clean proof route

Work at one admissible depth whose cutoff exceeds \(\mu\), then use canonical coefficient compatibility.

* **Faces \(|J|>c\):** their face amplitudes vanish. Normal derivatives are evaluated on a face already contained in the deep locus.
* **Faces \(|J|<c\):** their log degree is at most \(|J|-1<c-1\).
* **Faces \(|J|=c\):** degree \(c-1\) forces all coordinates to resonate. Outer log mixing then has exponent zero.
* Remove \(R_K\) by the preceding vanishing-jets lemma.
* Apply the plain Mellin/derivative identity.

Thus, for \(1\le c\le d\) and \(\mu>0\),
\[
\boxed{
\operatorname{empCoeff}(\mu,c-1)
=
\sum_{\substack{|J|=c\\
\alpha_i=2k_i\mu-h_i-1\in\mathbb N\ (i\in J)}}
\frac{\prod_{i\in J}(2k_i)^{-1}}
{(c-1)!\prod_{i\in J}\alpha_i!}
\int_{(0,1]^K}
\partial_J^\alpha H_\mu(0_J,w)\,
w^{h_K}(w^{2k_K})^{-\mu}\,dw .
}
\]
Also \(\operatorname{empCoeff}(\mu,j)=0\) for \(c\le j\le d-1\).

Keep an **explicit resonance guard** if `resOrder` uses natural-number truncation. Defining an \(\alpha\) for a nonresonant \(\mu\) does not make that face contribute.

The population form follows because its exactly resonant top face coefficient is
\[
\frac{\prod_{i\in J}(2k_i)^{-1}}{(c-1)!}\Gamma(\mu).
\]

---

## (c) Uniformity and random fields

### Uniform theorem to prove

Fix \(h,k,p,L,M'\), with the existing admissibility assumptions. Put \(P=\sum_i p_i\).

Prove that there exists \(K_0\ge0\), depending only on those fixed data, such that for every smooth \(\eta,\zeta\) and \(C\ge0\), if
\[
|\partial^m_v[\eta(v)e^{\tau\zeta(v)}]|
\le C(1+\tau)^P e^{M'\tau}
\]
for all \(m\le p\), \(\tau\ge0\), and \(v\) in the closed box, then
\[
\boxed{
|Z_{\eta,\zeta}(N)-\operatorname{absSpectralSum}
(\operatorname{empCoeffAtDepth}\eta\zeta hkp,L,N)|
\le C K_0N^{-L}(1+\log N)^{d-1}
}
\]
for every \(N\ge1\).

This is the useful **linear-in-\(C\)** formulation. A corollary can replace the field-family bound by bounded rectangular derivative norms of \(\eta,\zeta\), together with a common bound on \(|\zeta|\).

Then transfer the estimate to canonical coefficients below the cutoff.

### Random-field conclusion

Two additional results are needed:

1. Uniform control of the remainder on bounded sets of field jets.
2. Continuity of the finite coefficient vector in the corresponding field topology.

For fixed \(\eta\), joint convergence of branch representatives in a topology controlling all required rectangular derivatives gives, by continuous mapping,
\[
(c_{\mu j}(\zeta_n))_{\mu<L,\ j\le d-1}
\Rightarrow
(c_{\mu j}(\zeta))_{\mu<L,\ j\le d-1}.
\]
Ordinary \(C^{|p|}\) convergence is sufficient; “\(C^p\)” should be defined carefully when \(p\) is a multi-index.

Tight field-jet bounds then give
\[
Z_n(N)-\operatorname{absSpectralSum}(c(\zeta_n),L,N)
=
O_{\mathbb P}\!\left(N^{-L}(1+\log N)^{d-1}\right).
\]

These are **conditional probabilistic consequences**, not currently consequences formalized by the deterministic box theorem alone. In particular, coefficient convergence is joint convergence of nonlinear functionals of the field; a Gaussian field need not produce Gaussian coefficients.

---

## (d) Recommended next five units

I would defer resolved assembly until these interfaces are stable.

### 1. Uniform engine

**Target:** `empirical_expansion_at_depth_uniform`, exactly as above, plus canonical-coefficient transfer.

The main task is auditing constant dependence through the existing assembly. Avoid simultaneously developing probability or general boxes.

### 2. Mellin–jet bridge

Prioritize:

* `mellinMom_pow_mul_exp_zero`:
  \[
  \operatorname{mellinMom}(\tau^r e^{a\tau})\,\mu\,0
  =S_{\mu+r/2}(a).
  \]
* `mellinMom_pdMulti_fieldFam_zero`.
* If inexpensive, `mellinMom_faceAmp_fieldFam_zero`.

The full \(\ell>0\) exponent-derivative ladder is valuable documentation and a later explicit-coefficient interface, but do not let developing smoothness in \(\mu\) block the graded theorem. Its correct sign is \((-1)^\ell\).

### 3. Top spectral coefficient and depth-flatness interfaces

Prove:

* `empFaceCoef_eq_zero_of_expMult_le`.
* `empFaceCoef_top_eq_zero_of_not_exact`.
* `empFaceCoef_top_of_exact`, with factor
  \[
  \frac{\prod(2k_i)^{-1}}{(|J|-1)!}.
  \]
* Deep-locus vanishing implies:
  * `faceAmp = 0` for \(|J|>c\);
  * `faceAmp = pdMulti` for \(|J|=c\).

Prefer a generic smooth-amplitude depth lemma reusable for both \(H_\mu\) and `fieldFam`.

### 4. Box graded identification

Prove:

* `empCoeff_eq_zero_of_depthSupport`;
* `empCoeff_eq_faceSum_top`;
* a population-normalized corollary using \(H_\mu/\Gamma(\mu)\);
* zero-field recovery at the coefficient level, restricted to the canonical lattice and permitted log degrees.

With Units 2–3 available, this should be coefficient bookkeeping rather than new analysis.

### 5. General-box scaling adapter

Do **not** build another inner-kernel engine merely for \(b\).

Prove the exact integral scaling and coefficient transformation:
\[
\boxed{
c^{\,b}_{\mu q}
=
A_b B_b^{-\mu}
\sum_{j=q}^{d-1}
\binom jq(\log B_b)^{j-q}c^{\,1}_{\mu j}.
}
\]
Derive general-box `CutoffExpansion`, and add the neighbourhood-to-global representative adapter if it fits.

Each is a reasonable approximately-500-line target given the reported infrastructure, though the generic depth-flatness and Mellin-interchange interfaces are the likely budget risks. `SmoothRootField` and resolved assembly should follow as a separate sequence.

### Paper-facing paragraph—what is proved now

> **Deterministic empirical expansion on a normal-crossing box.** Let \(d\ge1\), let \(k_i\) be positive integers and \(h_i\) nonnegative integers, and let \(\eta,\zeta\) be smooth real-valued functions on \(\mathbb R^d\). The integral
> \[
> Z(N)=\int_{(0,1]^d}\eta(v)v^h
> \exp\!\bigl(-Nv^{2k}+\sqrt N\,v^k\zeta(v)\bigr)\,dv
> \]
> admits a canonical power–logarithmic asymptotic expansion with exponents in \((2\prod_i k_i)^{-1}\mathbb N\) and logarithmic degree at most \(d-1\): for every \(L>0\), truncation to exponents \(\mu<L\) has remainder \(O(N^{-L}(1+\log N)^{d-1})\). The coefficients are constructed from finite coordinate jets, face integrals and log-weighted Mellin moments, and are unique on the stated lattice and degree range. Setting \(\zeta=0\) recovers the population integral. This result concerns deterministic smooth fields on a normal-crossing box; it does not yet assert the empirical stratum formula, assembly over a resolution, uniformity over field families, or convergence in distribution for random fields.

That is a substantial theorem in its own right, without borrowing claims from the subsequent graded or probabilistic stages.