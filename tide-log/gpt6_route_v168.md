## Recommendation

**Adopt route B for the next implementation milestone.** It is mathematically sound, uses the landed real-amplitude infrastructure directly, and avoids the most expensive part of route A.

I would make three corrections to the proposal:

1. The coupling integrals are holomorphic on the **positive flat strip**
   \[
   0<\Re s,\qquad \mathrm{FlatStrip}\ p\ h\ k\ s,
   \]
   not, in general, on the entire flat strip.
2. The identity-theorem argument needs an explicit **initial-strip comparison with `mellinContinuation`**. The appendix supplies the necessary theorem, but its `hlow` hypothesis must be discharged; it is not automatic merely from holomorphy.
3. B4 is a complete integrated all-log formula, but obtaining the original amplitude formula (*) still requires **log-weighted** moment/jet interchange. The supplied `mellinMom_pdMulti_fieldFam_zero` covers only log order zero.

The signs and factorials in B3 and B4 are correct.

For the paper, I would retain (*) as the main structural theorem, with B1 as the transform identity and B4 as an equivalent coupling-average formulation. For Lean, prove them in the opposite order: **B1 → B3 → B4 → (*)**.

The proposed Lean statements below are interface sketches using the supplied API, not claims of checked elaboration against the repository. In particular, ambient variables and the exact integrability lemma signatures need checking in source.

---

# 1. Correctness of B1–B4

## 1.1 B1: convergence and Fubini

Put
\[
K(v)=v^{2k},\qquad H(v)=v^k\zeta(v).
\]
On the open-sided box, \(K(v)>0\) and
\[
\sqrt{K(v)}=v^k,\qquad H(v)/\sqrt{K(v)}=\zeta(v).
\]

For \(\sigma=\Re s>0\), the norm relevant to the first Fubini interchange is
\[
N^{\sigma-1}|\eta(v)|v^h
 \exp(-NK(v)+\sqrt N\,H(v)).
\]

Choose bounds \(|\eta|\le C_\eta\), \(|\zeta|\le M\) on the closed unit box. Your AM–GM estimate gives
\[
\exp(-NK+\sqrt N\,H)
 \le e^{M^2/2}e^{-NK/2}.
\]
Consequently,
\[
\int_0^\infty
N^{\sigma-1}|\eta(v)|v^h
e^{-NK+\sqrt N H}\,dN
\le
C_\eta e^{M^2/2}2^\sigma\Gamma(\sigma)\,
v^{h-2k\sigma}.
\]
The right-hand side is integrable over the box precisely under the coordinate conditions
\[
2k_i\sigma<h_i+1.
\]

Thus the first Fubini step is justified on the stated initial strip. Applying `mellin_exp_tilt` pointwise gives
\[
\mathcal M E(s)
 =
\int_{\mathrm{box}}
\eta(v)\operatorname{cpowWeight}(h,k,s,v)
S(s,\zeta(v))\,dv.
\]
This expression does **not** require defining `chartZeta` for complex amplitudes: it is just an intermediate integral.

Unfolding `fluctuationCplx`, the second Fubini step follows from
\[
t^{\sigma-1}e^{-t+M\sqrt t}\,
C_\eta v^{h-2k\sigma}.
\]
This is an integrable product majorant. Therefore
\[
\boxed{
\mathcal M E(s)=
\int_0^\infty
t^{s-1}e^{-t}
\,\operatorname{chartZeta}(\operatorname{fieldFam}\eta\zeta\sqrt t)\,h\,k\,s\,dt.
}
\tag{B1}
\]

**Implementation recommendation:** use `mellin_exp_tilt` for the pointwise complex identity and `integral_rpow_mul_exp_tilt_scaled` or `exp_tilt_le` for absolute convergence. Do not reproach the scaling substitution through `mellin_comp_mul_left` unless the existing theorem creates an actual elaboration obstacle.

The theorem `mellin_exp_tilt` being stated for every `s` does not remove these convergence obligations: Lean’s totalized integral identities are not Fubini hypotheses.

---

## 1.2 B2: the correct analytic domain

For a face \(x=(J,m)\), write \(K=J^c\) and define
\[
\Phi_x(s)=
\int_0^\infty\int_{\mathrm{box}_K}
t^{s-1}e^{-t}\,
G_x(\sqrt t,w)\,
\operatorname{cpowWeight}(h_K,k_K,s,w)\,dw\,dt,
\]
where
\[
G_x(\tau,w)=\operatorname{faceAmp}\ p\ J\
(\operatorname{fieldFam}\eta\zeta\tau)\ m\ w.
\]

The supplied growth bound gives, after absorbing face-dependent factorials,
\[
|G_x(\sqrt t,w)|
\le C_x w^{p_K}(1+\sqrt t)^R e^{M\sqrt t},
\qquad R=\sum_i p_i.
\]

Hence \(\Phi_x\) is holomorphic on
\[
\boxed{\{s:0<\Re s\ \land\ \mathrm{FlatStrip}\ p\ h\ k\ s\}.}
\]

The lower bound is essential. Near \(t=0\), a generic face amplitude has a nonzero limit, so \(t^{s-1}\) need not be integrable when \(\Re s\le0\).

More precisely, an individual face only needs the complementary-coordinate flat inequalities. Using the full ambient `FlatStrip` is a convenient uniform sufficient hypothesis.

Define the global continued expression first without choosing a centre:
\[
Z_p(s)=\sum_x
\operatorname{faceW}_x\,
\operatorname{innerFactor}_x(s)\,
\Phi_x(s).
\]
It is holomorphic on the positive flat strip minus `PoleAt`.

On that domain, finite-sum interchange gives
\[
Z_p(s)=
\int_0^\infty t^{s-1}e^{-t}
\,\operatorname{chartZetaAtDepth}p
(\operatorname{fieldFam}\eta\zeta\sqrt t)hks\,dt.
\]
Factorizing `innerFactor` at a real \(\mu\) gives B2.

This ordering is useful in Lean:

- `Z_p` is independent of \(\mu\);
- the global identity-theorem proof uses `innerFactor`;
- only the local polar calculation uses `regularFactor` and `resConst`.

There is no need to formulate B2 as an integral identity at candidate poles, where totalized divisions and integrals obscure the intended meromorphic meaning.

---

## 1.3 The identity theorem: include the seed-strip argument

Let
\[
V=\min(U,\operatorname{flatEdge}(p,h,k)),
\]
and remove from \(\{0<\Re s<V\}\) the finite set
\[
P=\{\operatorname{PoleAt}\ p\ h\ k\}
 \cup \operatorname{ofReal}(\operatorname{latticeBelow}(Q,U)).
\]
Then `isPreconnected_strip_diff_finite` gives the required preconnectedness. The domain is open because the deleted set is finite and hence closed.

On this domain:

- `Z_p` is holomorphic by the coupling integral theorem;
- `mellinContinuation` is holomorphic by
  `differentiableAt_mellin_cutoffRemainderFun` plus the finite rational principal parts.

To show agreement somewhere, use B1 and
`mellin_eq_mellin_cutoffRemainderFun_add_principalParts`.

### Discharging `hlow`

Choose a small positive \(a\) satisfying
\[
a<U,\qquad a<\operatorname{flatEdge},\qquad
2k_i a<h_i+1,\qquad a\le 1/Q.
\]
For positive exponents on the \(Q^{-1}\mathbb N\) lattice, \(\mu\ge1/Q\), so `hlow` follows without proving the optimal first nonzero exponent.

If `latticeBelow` includes zero, additionally prove
\[
\operatorname{empCoeff}\eta\zeta hk\,0\,q=0.
\]
The appendix does not include the definition of `latticeBelow`, so this point should be checked rather than assumed.

Thus the two holomorphic functions agree on a nonempty initial open substrip avoiding \(P\), and therefore throughout the connected deleted strip.

### Choosing the cutoff

The simplest choice is
\[
L\ge L_0(h),\qquad \mu<L,\qquad p=\operatorname{depthOf}h k L,
\qquad U=L.
\]
Then `flatStrip_depthOf` supplies the needed flatness. In particular, the canonical choice
\[
L=\operatorname{cutoffOf}h\mu
\]
should suffice after proving its elementary inequalities.

You do not need to formalize the exact edge formula. For \(d>0\), it is indeed
\[
\operatorname{flatEdge}(p,h,k)
=L+\min_i\frac1{2k_i}
=L+\frac1{2\max_i k_i}.
\]
But `U = L` and `flatStrip_depthOf` avoid all max/min bookkeeping.

Finally, choose a disc around \(\mu\) contained in the positive strip and avoiding \(P\setminus\{\mu\}\). This gives the eventual equality on `𝓝[≠] (μ : ℂ)` needed to transfer the `IsBigO` statement.

---

## 1.4 B3 and the degree bound

Set
\[
c_x=\operatorname{poleOrder}_x(\mu),\quad
w_x=\operatorname{faceW}_x\operatorname{resConst}_x,\quad
f_x(s)=\operatorname{regularFactor}_x(s)\Phi_x(s).
\]
Then
\[
Z_p(s)=\sum_x w_x(\mu-s)^{-c_x}f_x(s).
\]

Since
\[
(\mu-s)^{-c_x}=(-1)^{c_x}(s-\mu)^{-c_x},
\]
the coefficient of \((s-\mu)^{-(q+1)}\) is exactly
\[
\boxed{
a_q^*=
\sum_{x:c_x\ge q+1}
w_x(-1)^{c_x}
\frac{f_x^{(c_x-1-q)}(\mu)}{(c_x-1-q)!}.
}
\tag{B3}
\]

Then `polarCoeff_unique` gives, in its stated direction,
\[
a_q^*=\operatorname{polarCoeff}(\operatorname{empCoeff})\,\mu\,q
\qquad(q\le d-1).
\]

### `D = d - 1`, including `d = 0`

There is no principal-part degree problem:

\[
c_x\le d\le(d-1)+1
\]
holds for all natural \(d\), including zero. In Lean the second inequality is an `omega` fact; do **not** rewrite `(d - 1) + 1 = d` without `0 < d`.

For \(d=0\):

- all \(c_x=0\);
- all chart polar coefficients vanish;
- `D = 0`, so `polarPart D` has one slot, but its coefficient is zero;
- the empirical integral is
  \[
  \eta(*)e^{-N+\sqrt N\,\zeta(*)},
  \]
  which is rapidly decreasing at infinity.

The actual zero-dimensional issue is **`flatEdge`**, not `polarPart`: its displayed `inf'` definition requires a nonempty coordinate type. There must be an omitted ambient nonemptiness assumption in that API. Either state the edge-based continuation theorem under `0 < d`, or use an arbitrary numerical upper strip bound and treat \(d=0\) separately.

---

## 1.5 B4: exact regrouping

Write
\[
H_x(t,s)=
\operatorname{regularFactor}_x(s)\,
\operatorname{chartZeta}(G_x(\sqrt t,\cdot))h_Kk_Ks.
\]
Then
\[
f_x(s)=\int_0^\infty t^{s-1}e^{-t}H_x(t,s)\,dt.
\]

For \(n=c_x-1-q\),
\[
\frac{f_x^{(n)}(\mu)}{n!}
=
\sum_{b+j=n}\frac1{b!\,j!}
\int_0^\infty
t^{\mu-1}(\log t)^j e^{-t}
\,\partial_s^bH_x(t,\mu)\,dt.
\]
Here
\[
\frac{\binom nb}{n!}=\frac1{b!(n-b)!}.
\]

Set \(r=c_x-b\). Then
\[
j=r-q-1,\qquad b=c_x-r.
\]
The face sum at fixed \(r\) is precisely the definition of
`chartPolarCoeff ... (r - 1)`.

Therefore
\[
\boxed{
a_q^*=
\sum_{r=q+1}^{d}\frac1{(r-q-1)!}
\int_0^\infty
t^{\mu-1}(\log t)^{r-q-1}e^{-t}
\operatorname{chartPolarCoeff}
p(\operatorname{fieldFam}\eta\zeta\sqrt t)hk\mu(r-1)\,dt.
}
\tag{B4}
\]

There is:

- no extra binomial coefficient;
- no extra sign;
- no missing derivative of `regularFactor`.

The derivatives of `regularFactor` are already inside the population `chartPolarCoeff`.

For Lean, avoid the positive index \(r\) and write
\[
\sum_{j\in\operatorname{Ico}(q,d)}
\frac1{(j-q)!}\int_0^\infty
t^{\mu-1}(\log t)^{j-q}e^{-t}
\operatorname{chartPolarCoeff}(\cdots)j\,dt.
\]
This also makes the zero-dimensional sum empty automatically.

---

# 2. What to print in the paper

Route B is not a conceptual detour. It is a **weak integral representation of the same meromorphic distribution**.

Let
\[
T(s)[F]=\int_{\mathrm{box}}F(v)v^{h-2ks}\,dv,
\]
meromorphically continued, and use the \((\mu-s)\)-convention
\[
T(s)=\sum_{r=1}^{d}\frac{A_{\mu,r}}{(\mu-s)^r}
+\text{holomorphic distribution}.
\]
Thus, in the library,
\[
\boxed{
A_{\mu,r}[F]
=(-1)^r\operatorname{chartPolarCoeff}pFhk\mu(r-1).
}
\]
For a real formulation use `chartPolarReal` on the right.

Define
\[
m_{\mu,\ell}(a)=
\int_0^\infty t^{\mu-1}(\log t)^\ell e^{-t+a\sqrt t}\,dt
=\left.\partial_s^\ell S(s,a)\right|_{s=\mu}.
\]

## Main theorem: empirical all-log formula

For \(\mu>0\) and \(0\le q\le d-1\),
\[
\boxed{
c_{\mu,q}
=
\frac1{q!}
\sum_{r=q+1}^{d}
\frac{(-1)^{r-q-1}}{(r-q-1)!}
A_{\mu,r}
\!\left[\eta\,m_{\mu,r-q-1}(\zeta)\right].
}
\tag{*}
\]

This matches `logAmplitudeCoeffReal` with
\[
b(j,\ell)=
A_{\mu,j+1}[\eta\,m_{\mu,\ell}(\zeta)].
\]

Equivalently, directly in the library’s Laurent convention,
\[
c_{\mu,q}
=
\frac{(-1)^{q+1}}{q!}
\sum_{j=q}^{d-1}\frac{
\operatorname{chartPolarReal}
p(\eta\,m_{\mu,j-q}(\zeta))hk\mu j
}{(j-q)!}.
\]

## Transform proposition

On the initial convergence strip,
\[
\mathcal M E(s)
=
\int_0^\infty t^{s-1}e^{-t}
T(s)[\eta e^{\sqrt t\zeta}]\,dt.
\]

## Equivalent coupling-average formula

Print B4, or its real coefficient version,
\[
c_{\mu,q}
=
\frac{(-1)^{q+1}}{q!}
\sum_{r=q+1}^{d}\frac1{(r-q-1)!}
\int_0^\infty t^{\mu-1}(\log t)^{r-q-1}e^{-t}
\,C_{\mu,r}[\eta e^{\sqrt t\zeta}]\,dt,
\]
where \(C_{\mu,r}=(-1)^rA_{\mu,r}\).

The structural theorem is (*), because it makes the distributional support and jet dependence immediately visible. B4 is particularly valuable as the **formal proof route and computational representation**.

For the Lean milestone, however, B4 deserves to be a named theorem in its own right; do not postpone declaring success until the optional moment-interchange layer lands.

---

# 3. Additive unit decomposition

I recommend the following files. The estimates are planning targets, not verified line counts; B4 and the uniform-envelope work are the largest uncertainties.

## B7 — `FiniteFacePolar.lean` — about 150–250 lines

Add a general finite-family theorem; leave unit 5 unchanged.

```lean
noncomputable def finiteFacePolarCoeff
    (X : Finset α) (w : α → ℂ) (c : α → ℕ)
    (f : α → ℂ → ℂ) (μ : ℂ) (q : ℕ) : ℂ :=
  ∑ x ∈ X.filter (fun x => q + 1 ≤ c x),
    w x * ((-1 : ℂ) ^ c x *
      iteratedDeriv (c x - 1 - q) (f x) μ /
        ((c x - 1 - q)! : ℂ))
```

```lean
theorem finiteFaceSum_sub_polarPart_isBigO_one
    (hU : U ∈ 𝓝 μ)
    (hf : ∀ x ∈ X, DifferentiableOn ℂ (f x) U)
    (hD : ∀ x ∈ X, c x ≤ D + 1) :
    (fun s =>
      (∑ x ∈ X, w x * ((μ - s)⁻¹ ^ c x * f x s)) -
      polarPart D (finiteFacePolarCoeff X w c f μ) μ s)
      =O[𝓝[≠] μ] fun _ => (1 : ℂ)
```

Reuse:

- `pole_taylor_isBigO_one`;
- finite sums of `IsBigO`;
- the finite-sum rearrangement pattern from
  `polarPart_chartPolarCoeff_eq`.

Include `c x = 0`; its contribution is holomorphic and its principal part is empty.

---

## B8 — `CoupledZetaBounds.lean` — about 250–400 lines

Develop one generic envelope theorem for a real coupling family
```lean
H : ℝ → (ι → ℝ) → ℝ
```
with joint continuity or suitable joint measurability and the hypothesis
```lean
∀ τ, 0 ≤ τ →
  FlatOn (H τ) p
    (C * (1 + τ) ^ R * Real.exp (M * τ))
```
where `0 ≤ C`.

On a small disc about \(s_0\), choose
\[
0<a<\Re s<b,\qquad p_i+h_i-2k_i b>-1.
\]
Use the product envelope
\[
C\bigl(t^{a-1}+t^{b-1}\bigr)
(1+\sqrt t)^R e^{-t+M\sqrt t}
w^{p+h-2kb}.
\]
For arbitrary finite log order \(n\), multiply by
\[
\bigl(|\log t|+2|\operatorname{logSum}k\,w|\bigr)^n.
\]

Prove integrability of these envelopes. At infinity use, for example,
\[
M\sqrt t\le t/2+M^2/2.
\]
At zero, use positive margins in the \(t\)-exponent and every \(w\)-exponent.

This unit should export bounds for **all finite log orders**, not merely the first derivative. Otherwise B4 forces a second analytic development.

---

## B9 — `CoupledChartZeta.lean` — about 250–400 lines

Define
```lean
noncomputable def coupledChartZeta
    (H : ℝ → (ι → ℝ) → ℝ)
    (h k : ι → ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ),
    (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ) *
      chartZeta (H (Real.sqrt t)) h k s
```

Prove equality with the product-measure integral.

The core analytic theorem should have the shape
```lean
theorem hasDerivAt_coupledChartZeta
    (hH : Continuous fun z : ℝ × (ι → ℝ) => H z.1 z.2)
    (hC : 0 ≤ C)
    (hflat : ∀ τ, 0 ≤ τ →
      FlatOn (H τ) p
        (C * (1 + τ) ^ R * Real.exp (M * τ)))
    (hs0 : 0 < s.re)
    (hs : FlatStrip p h k s) :
    HasDerivAt (coupledChartZeta H h k)
      (coupledChartZetaLogMoment H h k 1 s) s
```

Define the order-\(n\) log moment using the single multiplier
\[
\bigl(\log t-2\operatorname{logSum}k\,w\bigr)^n.
\]
Then prove
```lean
iteratedDeriv n (coupledChartZeta H h k) s =
  coupledChartZetaLogMoment H h k n s
```
by induction using the B8 envelopes.

### Product measure versus iterated differentiation

I recommend
```lean
(volume.restrict (Ioi 0)).prod
  (volume.restrict (SmoothEngine.box ι 1))
```
and `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, subject to checking its exact signature in the pinned Mathlib.

Reasons:

- one explicit exponential carries all `s`-dependence;
- one derivative multiplier handles every order;
- no separate parameter-measurability proof for `deriv` of the inner integral;
- B4 later reduces to finite algebra and Fubini.

Iterating the two differentiation arguments is viable, but it requires exporting uniform inner derivative bounds that unit 2 does not currently state.

`mellin_hasDerivAt_of_isBigO_rpow` is not the right primary abstraction here: the function whose Mellin transform you are taking also depends on \(s\). It does not directly account for the chart-zeta derivative.

---

## B10 — `EmpiricalChartMellin.lean` — about 250–400 lines

Export three facts:

```lean
theorem locallyIntegrableOn_empIntegral ...
    : LocallyIntegrableOn
        (fun N => (empIntegral η ζ h k N : ℂ)) (Ioi 0)
```

```lean
theorem empIntegral_isBigO_one_zero ...
    : (fun N => (empIntegral η ζ h k N : ℂ))
        =O[𝓝[>] 0] fun _ => (1 : ℂ)
```

```lean
theorem mellin_empIntegral_eq_coupledChartZeta
    (hη : ContDiff ℝ ∞ η) (hζ : ContDiff ℝ ∞ ζ)
    (hk : ∀ i, 0 < k i)
    (hs0 : 0 < s.re) (hs : ZetaStrip h k s) :
    mellin (fun N => (empIntegral η ζ h k N : ℂ)) s =
      coupledChartZeta (fieldFam η ζ) h k s
```

Reuse the tilt local-integrability and bounded-at-zero results mentioned in the question, plus the two supplied pointwise Mellin identities.

When applying the general tilt results, remember that the coefficient is \(\eta(v)v^h\), not merely \(\eta(v)\).

---

## B11 — `EmpiricalMellinContinuation.lean` — about 250–400 lines

Define
```lean
coupledFaceZeta p η ζ h k J m s
```
as `coupledChartZeta` of the real face-amplitude family.

Define
```lean
empZetaAtDepth p η ζ h k s :=
  ∑ x ∈ SmoothEngine.faceIndex p,
    (SmoothEngine.faceW x.1 x.2 : ℂ) *
      innerFactor h k x.1 x.2 s *
      coupledFaceZeta p η ζ h k x.1 x.2 s
```

Prove:

1. Holomorphy on the positive flat strip off `PoleAt`.
2. Equality with `mellin empIntegral` on the initial strip.
3. Equality with `mellinContinuation` on the common deleted strip.
4. The local corollary:
   ```lean
   empZetaAtDepth p η ζ h k
     =ᶠ[𝓝[≠] (μ : ℂ)]
   mellinContinuation (Qamb k) (d - 1)
     (empIntegral η ζ h k) (empCoeff η ζ h k) U
   ```
   under `0 < μ`, `μ < U`, and `FlatStrip p h k μ`.

For the local corollary, whether \(\mu\) itself is a lattice point is irrelevant. Lattice membership is needed later by `polarCoeff_unique`.

Reuse `growthLE_faceAmp_fieldFam`,
`continuous_faceAmp_fieldFam_joint`,
`finite_poleSet`, and `isPreconnected_strip_diff_finite`.

---

## B12 — `EmpiricalIntegratedPolar.lean` — about 150–300 lines

Define
```lean
empFaceHolo ... μ s :=
  regularFactor h k J m μ s *
    coupledFaceZeta p η ζ h k J m s
```
and define `empIntegratedPolarCoeff` by the B3 finite sum.

Use B7 to prove
```lean
(empZetaAtDepth p η ζ h k -
  polarPart (d - 1) (empIntegratedPolarCoeff ... μ) μ)
  =O[𝓝[≠] (μ : ℂ)] fun _ => (1 : ℂ)
```
with subtraction written pointwise if needed.

Then:
```lean
theorem empIntegratedPolarCoeff_eq_polarCoeff
    ...
    (hμlat : μ ∈ latticeBelow (Qamb k) U)
    (hμU : μ < U) (hμpos : 0 < μ)
    (hq : q ≤ d - 1) :
    empIntegratedPolarCoeff p η ζ h k μ q =
      polarCoeff (empCoeff η ζ h k) μ q
```

This is the first substantive completion milestone: it identifies the existing empirical coefficients by a new meromorphic calculation.

---

## B13a — `CoupledPolarInterchange.lean` — about 250–400 lines

Prove the analytic/algebraic interchange needed for B4.

Do **not** make the expanded binomial formula for `iteratedDeriv Φ` the public endpoint. The compact formula
\[
\Phi_x^{(n)}(\mu)
=\iint \text{base kernel}\,
(\log t-2\logSum k\,w)^n
\]
is the better analytic API.

Internally:

1. expand the power using the binomial theorem;
2. establish the corresponding log-moment formulas for the inner chart integral;
3. apply finite Leibniz to `regularFactor`;
4. normalize derivatives by factorials;
5. regroup using \(j=r-q-1\).

It is worth isolating the factorial/binomial normalization as a finite algebra lemma.

All integrals of chart polar coefficients used in B4 should have explicit integrability lemmas. Do not rely on linearity of totalized integrals.

---

## B13b — `EmpiricalCouplingAllLog.lean` — about 100–250 lines

Define, in zero-based indexing,
```lean
noncomputable def couplingPolarCoeff ... (q : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico q d,
    ((j - q)! : ℂ)⁻¹ *
      ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ ((μ : ℂ) - 1) *
        (Real.log t : ℂ) ^ (j - q) *
        (Real.exp (-t) : ℂ) *
        chartPolarCoeff p
          (fieldFam η ζ (Real.sqrt t)) h k μ j
```

Export
```lean
theorem couplingPolarCoeff_eq_polarCoeff ...
    (hq : q ≤ d - 1) :
    couplingPolarCoeff p η ζ h k μ q =
      polarCoeff (empCoeff η ζ h k) μ q
```
and a real-valued `empCoeff` corollary using `ofReal_chartPolarReal`.

This is B4 in the library’s exact Laurent convention.

### Size assessment

I would not commit to 800–1200 lines for all of B1–B4 before a prototype of B8/B9. The architecture is substantially cheaper than route A, but uniform log envelopes and finite derivative regrouping can be sizeable. Splitting B13 is prudent.

---

## Optional B15–B16 — from B4 to (*)

Define real log moments
\[
m_{\mu,\ell}(a)=(-1)^\ell
\operatorname{mellinMom}(\tau\mapsto e^{\tau a})\,\mu\,\ell.
\]

Then prove:

1. log-weighted analogues of `mellinMom_pdMulti_fieldFam_zero`;
2. smoothness of \(v\mapsto\eta(v)m_{\mu,\ell}(\zeta(v))\);
3. interchange through `remList` and hence `faceAmp`;
4. interchange through the finite-order chart polar functional.

The existing zero-log theorem and `contDiff_mul_fluctuation` are the base cases, not the full result.

For the identification with \(\partial_s^\ell S\), B9 specialized to a zero-dimensional complementary box—or a simpler scalar version of its kernel theorem—already supplies complex-index differentiation. No joint \((s,a)\)-smoothness theorem is needed.

---

# 4. Regression milestones

## First: one coordinate, constant amplitude, no fluctuation

Take \(d=1\), \(\eta=1\), \(\zeta=0\), \(k>0\), and
\[
\mu=\frac{h+1}{2k}.
\]
Then
\[
\operatorname{chartZeta}(1)hks=\frac1{h+1-2ks},
\]
so its Laurent coefficient at \(\mu\) is
\[
\operatorname{chartPolarCoeff}(\cdots)\,0=-\frac1{2k}.
\]
Therefore B4 gives
\[
a_0=-\frac{\Gamma(\mu)}{2k},
\qquad
\boxed{\operatorname{empCoeff}(\mu,0)=\frac{\Gamma(\mu)}{2k}.}
\]

Equivalently the meromorphic Mellin transform is
\[
\frac{\Gamma(s)}{h+1-2ks}.
\]

This catches the most likely sign error immediately. Other positive chart candidate points have zero polar data for this constant amplitude.

A useful extension with constant \(\zeta=a\) is
\[
\operatorname{empCoeff}(\mu,0)=\frac{S(\mu,a)}{2k}.
\]

## Then: the \(x^2y^2\) chart

For the positive unit square with \(\eta=1,\zeta=0,h=(0,0),k=(1,1)\),
\[
E(N)=\int_0^1\int_0^1e^{-Nx^2y^2}\,dx\,dy,
\]
and
\[
T(s)[1]=\frac1{(1-2s)^2}
=\frac1{4(s-\tfrac12)^2}.
\]
Thus at \(\mu=\tfrac12\),
\[
\operatorname{chartPolarCoeff}(\cdots)\,1=\frac14,
\qquad
\operatorname{chartPolarCoeff}(\cdots)\,0=0.
\]

B4 must produce
\[
a_1=\frac{\Gamma(\tfrac12)}4,\qquad
a_0=\frac{\Gamma'(\tfrac12)}4.
\]
Converting to empirical coefficients:
\[
\boxed{
c_{1/2,1}=\frac{\sqrt\pi}{4},
\qquad
c_{1/2,0}=-\frac{\Gamma'(\tfrac12)}4
=\frac{\sqrt\pi}{4}(\gamma+2\log2).
}
\]

Hence
\[
E(N)=N^{-1/2}
\left(
\frac{\sqrt\pi}{4}\log N
-\frac{\Gamma'(\tfrac12)}4
\right)+\text{rapidly decreasing remainder}.
\]

The leading regression is
\[
\frac{\sqrt N}{\log N}E(N)\longrightarrow\frac{\sqrt\pi}{4}.
\]
That is what should match `tendsto_logExample`, after checking its domain and normalization. Its statement was not supplied; a full square \([-1,1]^2\), for example, introduces a factor four.

The **constant logarithmic-order-zero coefficient** is the stronger B4 regression: it tests the derivative of the coupling kernel rather than only its value. Initially leave it as `-Γ'(1/2)/4` if the digamma special-value infrastructure is inconvenient.

---

# 5. Traps and safeguards

### 1. Positive real part is indispensable

Every coupling holomorphy theorem should visibly include `0 < s.re`. At a local pole, visibly include `0 < μ`.

### 2. The library uses negative-log moments

`mellinMom` contains `(-log t)^ℓ`, while B4 contains `(log t)^ℓ`. Thus
\[
\int t^{\mu-1}(\log t)^\ell G(\sqrt t)e^{-t}\,dt
=(-1)^\ell\operatorname{mellinMom}G\,\mu\,\ell.
\]
This is a likely source of a second, subtler sign error.

### 3. Measurability is straightforward but should be packaged

Use `continuous_faceAmp_fieldFam_joint` composed with
\[
(t,w)\mapsto(\sqrt t,w).
\]
`Real.sqrt` is continuous on all of \(\mathbb R\), so no differentiability at zero is needed.

If using `measurable_uncurry_faceAmp_fieldFam` in `(w,τ)` order, explicitly compose with the swap and square-root map. Restrict the measures afterward.

### 4. Candidate poles lie on the ambient lattice only under `hk`

With \(Q=2\prod_i k_i\) and \(k_i>0\),
\[
\frac{m_i+h_i+1}{2k_i}
=
\frac{(m_i+h_i+1)\prod_{j\ne i}k_j}{Q}.
\]
Thus they are positive lattice points.

For Lean, package the natural-number divisibility/factorization once. Avoid division in `ℕ` when constructing the lattice numerator; use the product over the erased index.

### 5. Lattice membership is not the same as being a chart pole

At a positive lattice point that is not a candidate pole:

- every `chartPolarCoeff` vanishes;
- B3/B4 vanish;
- `polarCoeff_unique` proves the corresponding empirical coefficients vanish.

At a point off the lattice, `polarCoeff_unique` does not identify the raw value of the function `empCoeff`. A separate support lemma for its definition is needed for an unrestricted “all real \(\mu\)” theorem. `CutoffExpansion` alone only controls the coefficients it actually samples.

### 6. Higher log degrees need a separate support statement

`polarCoeff_unique` gives only \(q\le d-1\). A theorem for every natural `q` needs an additional proof that `empCoeff ... μ q = 0` above that bound. The face definition should make this easy, but it is not a consequence of the displayed uniqueness theorem.

### 7. Pointwise bounded remainders cannot simply be integrated

Unit 5 applied separately at each \(t\) gives an \(O(1)\) constant that may depend on \(t\). Integrating those statements is unjustified without a uniform integrable majorant.

Your proposed B3 route avoids this correctly: first integrate the holomorphic factors, then apply the finite-family polar theorem.

### 8. Do not claim (*) follows from linearity alone

Besides linearity, passing a polar functional through the coupling integral needs continuity/dominated interchange in enough amplitude derivatives. Route B supplies the needed bounds economically, but the log-weighted jet step remains real work.

---

## Bottom line

Proceed with route B, additively:

1. a finite-face polar lemma;
2. a generic real-family coupling transform with all finite log moments;
3. B1 and empirical continuation;
4. B3 via `polarCoeff_unique`;
5. B4 by normalized Taylor-coefficient convolution;
6. optional log-moment amplitude interchange giving (*).

The decisive simplification is not merely “real rather than complex amplitudes.” It is that **all holomorphic parameter dependence is explicit in scalar exponential kernels**, while the existing smooth engine is used only on real, parameter-independent slices. That is a strong architectural fit for the library as it has actually landed.