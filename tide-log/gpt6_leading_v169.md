## Verdict

The product-with-density construction is the right assembly for unit 19. However, **the appendix exposes two substantive corrections to the plan**:

1. **`RootField.loc_eq` does not identify the field on a leading face with `ξ.ψ` there.** It only applies on the open box. Consequently, (M4) with the integrand `S_λ(ξ.ψ x)` is **false for the current `RootField` interface**, without an additional trace-compatibility assumption.
2. **The proposed raw residue measure and `extremalStratumMeasure` have different normalisations.** With unit 18’s convention,
   \[
   \nu^\lambda_m(0)=\frac{\Gamma(\lambda)}{(m-1)!}\,\rho_{\lambda,m}|_X,
   \qquad X=U\setminus D_{m+1}.
   \]
   Thus `globalExtremalStratumMeasure := (extremalStratumMeasure).map val` is the **population coefficient measure**, not the raw measure appearing after the factor \(1/(m-1)!\) in (M4).

There is also a genuine unresolved geometric dependency: the supplied statements do not establish `IsExtremalData ⇒ ChartLeading` for an arbitrary existing transport.

Below, proposed new Lean names/signatures are interface recommendations, not claims that those declarations already exist.

---

## 1. Construct the raw measure using the unit observable

Put
\[
\Xi_1=\Xi.\mathrm{withF}(1),\qquad
a_p(s,v)=(\Xi_1.\mathrm{amp}\ Y\ p).\mathrm{amp}(s,v).
\]

**Yes: this is the correct amplitude.** The original amplitude already contains the observable. In particular, `piecePresentation.amplitude_eq` identifies it, on the transported box, with
\[
\rho_f(T_p(s,v))\,\Xi.F(\operatorname{divPt}_p(s,v)).
\]

The useful new lemma is the **closed-box** identity
\[
(\Xi.\mathrm{amp}\ Y\ p).\mathrm{amp}(s,v)
 =
a_p(s,v)\,\Xi.F(\Xi.\mathrm{divPt}\ Y\ p\ s\ v).
\tag{1}
\]

Do not obtain (1) merely by using `piecePresentation.amplitude_eq`: that field is an a.e. statement for the volume presentation, and an a.e. identity in the ambient box says nothing about values on a leading face. Prove (1) directly from the definitions and the closed-box versions of `G_eq`, `ρf_eq`, and the chart-map identity. The proof of `amplitude_eq` in the appendix strongly suggests that these ingredients are available.

Also prove \(a_p\geq0\) on the relevant closed box. Global nonnegativity of the extended amplitude on all of \(\mathbb R^{d_p}\) is not established by the appendix.

### Definition

For an attaining piece, write
\[
J_p=\operatorname{resSet}(h_p,k_p,\lambda),\quad
W_p=(0,b_p]^{J_p^c},\quad
Q_p=\nu_p\otimes(\mathrm{vol}|_{W_p}),
\]
and define
\[
\begin{aligned}
d_p(s,w)&=
 \operatorname{leadingFaceDensity}(h_p,k_p,\lambda,a_p(s,\cdot))(w),\\
H_p(s,w)&=\Xi.\operatorname{divPt}\ Y\ p\ s
                 (\operatorname{glue}(J_p,0,w)),\\
\rho_p&=(H_p)_*\bigl(Q_p.\operatorname{withDensity}(\operatorname{ofReal}\circ d_p)\bigr).
\end{aligned}
\]

Then define
\[
\rho_{\lambda,m}
 =
\sum_p
 \begin{cases}
 \rho_p,&\operatorname{multCount}(h_p,k_p,\lambda)=m,\\
 0,&\text{otherwise}.
 \end{cases}
\tag{2}
\]

Recommended name:

```lean
noncomputable def leadingResidueMeasureU
    (lam : ℝ) (m : ℕ) : Measure Ξ.R.U := ...
```

Defining it using an `if` inside the finite sum is usually easier than introducing an attaining-piece subtype.

### Why this construction is preferable

It avoids a measurable family of measures and `Measure.bind`. Its integral formula is precisely a pushforward integral followed by a density integral and Fubini.

The ingredients `ν_p`, `hA`, `kA`, and the geometric map should be independent of `Ξ.F`; establish the corresponding `withF` simp lemmas if they are not definitional. **A piece measure is nevertheless chart-dependent.** Independence under reparametrisation or replacement of the transport is a theorem, not a consequence of using a product measure.

I would not introduce fibrewise `leadingFaceMeasure` as the foundational definition. Instead, prove afterwards that integration against (2) is the iterated integral against unit 18’s fibre measures.

---

## 2. Identification: attaining pieces only, with one missing signed-observable bridge

Under `ChartLeading`, every piece has multiplicity at most \(m\). Therefore:

- multiplicity \(<m\): `pieceFaceLimit = 0`;
- multiplicity \(=m\): use the full resonant face;
- there is no multiplicity \(>m\) case.

For an attaining piece the desired identity is
\[
\begin{split}
\int_s \operatorname{pieceFaceLimit}_p(s)\,d\nu_p
={}&\frac1{(m-1)!}
 \int_s\int_u
 F(\operatorname{divPt}_p(s,u))\\
&\qquad\qquad{}\cdot S_\lambda(\xi.\operatorname{loc}_p(s,u))
 \,d\operatorname{leadingFaceMeasure}(a_p(s,\cdot))(u)\,d\nu_p.
\end{split}
\tag{3}
\]

### The exact unit 18 theorem does not directly prove (3)

`faceFunctional_eq_integral_leadingFaceMeasure` assumes its entire amplitude `η` is nonnegative. Here the original amplitude contains an arbitrary signed `F`.

You need the factored version
\[
\operatorname{faceFunctional}(\xi,aF)
 =
\frac1{(m-1)!}\int F\,S_\lambda(\xi)\,d\operatorname{leadingFaceMeasure}(a).
\tag{4}
\]

This follows directly by unfolding `faceFunctional` and using `integral_leadingFaceMeasure`. Alternatively, under its continuity hypotheses, it follows by uniqueness of limits from the two box-limit theorems. **The direct integral proof is preferable**, because `F ∘ divPt` may only be continuous on the chart box, not on the totalised chart map’s entire domain.

Thus unit 18 supplies essentially all the analysis, but the stated nonnegative-amplitude theorem still needs this small factorisation bridge.

### Joint obligations

The principal obligations are:

| Obligation | Source or required addition |
|---|---|
| Joint measurability of \(a_p(s,\operatorname{glue}(0,w))\) | Joint amplitude continuity; glue continuity/measurability |
| Joint measurability of the residue weight | `measurable_residueWeight`, composed with `Prod.snd` |
| Measurability of \(H_p\) | Measurable chart map and `Tm`; or a supported/a.e. identification with the presentation map |
| Integrability of \(d_p\) over \(Q_p\) | Finite base measure, a **uniform** amplitude bound, `integrableOn_residueWeight_compl` |
| Integrability with \(F(H_p)\) and the field weight | Bounds on the relevant compact chart images and closed parameter boxes |
| Fubini | Integrability of the joint signed integrand, not merely fibrewise integrability |
| Removing `ENNReal.ofReal` | Nonnegativity of \(d_p\), a.e. on the reference measure |

`continuous_amp_uncurry`, if available in the stated form, handles joint continuity. It does **not by itself** supply a uniform bound on a noncompact base. Use compactness of the parameter domain or continuous extension to its compact closure.

Likewise, finiteness of every fibre measure does not imply finiteness of its base integral. Prove the uniform domination
\[
|d_p(s,w)|\le C_p\,\operatorname{residueWeight}(w)
\]
and use \(\nu_p(\mathrm{univ})<\infty\).

### Deeper-corner nullity needs a geometric bridge

`leadingFaceMeasure_deep` proves coordinate-corner nullity. To conclude
```lean
leadingResidueMeasureU ... (Ξ.deepZeroFibre m) = 0
```
you still need to show that, almost everywhere on an attaining face, intrinsic depth is at most \(m\).

That means identifying intrinsic walls with the coordinate walls, and accounting for any exceptional base-coordinate loci. This is not supplied by `leadingFaceMeasure_deep` alone. It is a small but essential geometric obligation, separate from Fubini.

---

## 3. The current `RootField` does **not** descend to `ξ.ψ` on the face

This is the most important correction.

The hypothesis is

```lean
z.2 ∈ SmoothEngine.box ... →
  ξ.loc p z = ξ.ψ (Ξ.divPt Y p z.1 z.2)
```

and `SmoothEngine.box` is the positive box. An attaining face has resonant coordinates equal to zero, so `loc_eq` does not apply.

Continuity of `loc` determines its trace from interior values. It does **not** constrain the value of a merely measurable `ψ` on the divisor.

### Counterexample

Take a one-dimensional resolved model \(K(x)=x^2\), with positive prior at zero. Set
\[
\psi(x)=0\quad(x\ne0),\qquad \psi(0)=1,
\]
and take every branch representative to be identically zero.

This is bounded and satisfies the supplied `RootField` conditions. The empirical partition function is the population partition function: changing `ψ` only on \(K=0\) does not change it. But the proposed right side of (M4) evaluates \(S_\lambda(1)\), whereas the actual leading coefficient uses \(S_\lambda(0)\).

More generally, different sectors can have different continuous traces at the same divisor point. No single field on \(U\) need represent those traces.

### Two valid interfaces

**A. Add face-trace compatibility.**

Introduce a proposition, for example

```lean
def LeadingFaceTraceCompatible
    (ξ : Ξ.RootField Y) (lam : ℝ) (m : ℕ) : Prop := ...
```

meaning, for every attaining piece and every relevant face parameter,
\[
\xi.\operatorname{loc}_p(s,\operatorname{glue}(0,w))
 =\xi.\psi(H_p(s,w)).
\tag{5}
\]

An a.e. version with respect to the density-weighted reference measure is sufficient; pointwise compatibility is easier to use.

Global continuity of `ξ.ψ`, together with continuity of the chart maps on the closed boxes, implies (5) by density of the positive box. No admissibility hypothesis on `F` is involved.

**B. Retain the present `RootField` and assemble the tilted measure directly.**

Define
\[
\widehat\nu^\lambda_m(\xi)
 =
\frac1{(m-1)!}
 \sum_{p\text{ attaining}}
 (H_p)_*\left(
   \operatorname{ofReal}\bigl[d_p(s,w)
          S_\lambda(\xi.\operatorname{loc}_p(s,\operatorname{glue}(0,w)))\bigr]
   \,Q_p
 \right).
\tag{6}
\]

Then the unconditional statement for the existing interface is
\[
\operatorname{HasLeadingTerm}
 \left(\operatorname{empZ}[F;\xi],
       \int_U F\,d\widehat\nu^\lambda_m(\xi),
       \lambda,m-1\right).
\tag{7}
\]

Under (5), (6) becomes
\[
\widehat\nu^\lambda_m(\xi)
 =
\rho_{\lambda,m}.\operatorname{withDensity}
 \left(x\mapsto
  \operatorname{ofReal}\frac{S_\lambda(\xi.\psi(x))}{(m-1)!}\right).
\tag{8}
\]

**Recommendation:** provide both (7) and the trace-compatible version of (M4).

---

## 4. Unit 20: what is actually needed

### `IsExtremalData ⇒ ChartLeading` is not justified for arbitrary `Y`

`IsExtremalData` constrains walls through points of `zeroFibre`, which includes the prior-support condition. The excerpt does not say that every existing chart’s entire active wall list is realised through such a point.

A chart can contain walls irrelevant to the supported zero fibre. Their amplitudes may vanish where necessary, while their ratios still prevent the box data from satisfying `ChartLeading`.

Thus:

> Do not make `chartLeading_of_extremalData` a theorem for arbitrary `Y` until the construction of `ResolvedCoreTransport` supplies the necessary centred-wall certificate.

The definition of that transport, and the definition of `IsExtremalData`, are not included, so the appendix cannot settle this point.

### Minimal useful certificate

At piece level, it suffices to know that its active wall multiset embeds, preserving multiplicities, into the intrinsic wall multiset at some supported zero-fibre point:
\[
\forall p,\ \exists P\in Z_0,\quad
 \{\!\{(k_{p,i},h_{p,i}):i\}\!\}
 \le \operatorname{pairs}(P).
\tag{9}
\]

Multiset inclusion matters: ordinary set inclusion does not control resonance multiplicity.

A proposed structure can package (9):

```lean
structure ExtremalLocalisationCertificate
    (Y : ResolvedCoreTransport Ξ.R Ξ.hKc Ξ.prior) : Prop where
  wallData :
    ∀ p : (Ξ.X Y).PIdx,
      ∃ P ∈ Ξ.zeroFibre,
        pieceWallMultiset Ξ Y p ≤ pairs Ξ.R Ξ.hK0 P
```

Here `pieceWallMultiset` is a proposed helper containing `(kA p i, hA p i)` with multiplicity.

Then

```lean
theorem chartLeading_of_extremalData_of_certificate
    (h : Ξ.IsExtremalData lam m)
    (hY : Ξ.ExtremalLocalisationCertificate Y) :
    Ξ.ChartLeading Y lam m
```

is the inexpensive part. Constructing a certified cover is the size risk.

A chart-centred certificate, with centres in `zeroFibre` and an active-wall/pairs equality, is stronger but likely closer to the existing geometry. Put the geometric certificate with the transport/localisation infrastructure, not in the empirical integral layer.

For empirical use, changing transports also requires transporting or rebuilding `RootField` representatives. This is automatic for a globally continuous field; it is **not automatically available for an arbitrary current `RootField`**.

### Can population Riesz avoid unit 20?

It can avoid some box assembly, but not the central no-deep-mass argument.

The unconditional population limit and positivity make a global Riesz construction plausible. On a common compact carrier \(C\), positivity yields a bound of the form
\[
|L(G)|\le L(1)\sup_C|G|.
\]
With the usual smooth approximation and localisation machinery, one can construct a finite measure on \(U\) representing \(L\).

But test uniqueness on \(X\) only identifies its restriction to \(X\). It cannot exclude an additional positive measure on \(D_{m+1}\):
\[
\widehat\nu+\tau,\qquad \operatorname{supp}\tau\subset D_{m+1},
\]
has exactly the same integrals against all `IsTest m` functions.

Therefore `eq_stratumMeasure_of_tests` does **not** remove the need to prove that the global measure gives the deep fibre zero mass. Local integrable-exponent estimates, or an equivalent cutoff estimate, remain necessary.

**Recommendation:** use explicit local measures for the no-deep-mass theorem, then uniqueness to identify the canonical population measure. Do not run a second global Riesz development merely to postpone the same geometric obligation.

---

## 5. Recommended theorem interfaces and dependencies

### A. Unit 19: raw and empirical measures

For the raw measure:

```lean
theorem isFiniteMeasure_leadingResidueMeasureU
    (hlam : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    IsFiniteMeasure (Ξ.leadingResidueMeasureU Y lam m)

theorem leadingResidueMeasureU_deepZeroFibre
    (hlam : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    Ξ.leadingResidueMeasureU Y lam m (Ξ.deepZeroFibre m) = 0
```

Also prove that it is carried by a common compact subset of the lifted prior support. This is important: **a finite measure alone does not integrate every unbounded smooth function**.

The requested empirical theorem must include trace compatibility:

```lean
theorem hasLeadingTerm_empZ_eq_integral_leading
    (ξ : Ξ.RootField Y)
    (hlam : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m)
    (htrace : Ξ.LeadingFaceTraceCompatible Y ξ lam m)
    {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      ((1 / ((m - 1).factorial : ℝ)) *
        ∫ P, Ξ.F P * fluctuation 1 lam (ξ.ψ P)
          ∂(Ξ.leadingResidueMeasureU Y lam m))
      lam (m - 1)
```

For the current unrestricted field interface:

```lean
theorem hasLeadingTerm_empZ_eq_integral_leadingEmpirical
    (ξ : Ξ.RootField Y)
    (hlam : 0 < lam) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m)
    {M : ℝ} (hM : ∀ P, |ξ.ψ P| ≤ M) :
    HasLeadingTerm (Ξ.empZ Y ξ)
      (∫ P, Ξ.F P ∂(Ξ.leadingEmpiricalMeasureU Y ξ lam m))
      lam (m - 1)
```

The latter measure uses the coefficient normalisation in (6).

### B. Unit 20: certified localisation and identification

Prove, in order:

1. intrinsic wall data versus local coordinate wall data;
2. existence of an adapted transport, if not already available;
3. its `ChartLeading` property;
4. population coefficient representation using the zero field;
5. identification on `stratumOpen` using `eq_stratumMeasure_of_tests`;
6. transport independence of the resulting global population measure.

The uniqueness invocation needs a `Regular` instance for the candidate measure on the open subtype. Account for it explicitly.

### C. Unit 21: use the population-normalised measure

The proposed definition is good:

```lean
noncomputable def globalExtremalStratumMeasure
    {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    Measure Ξ.R.U :=
  (Ξ.extremalStratumMeasure Y h hm).map Subtype.val
```

The comparison with a chart-leading raw measure is

```lean
theorem globalExtremalStratumMeasure_eq_smul_leadingResidueMeasureU
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    (hlead : Ξ.ChartLeading Y lam m) :
    Ξ.globalExtremalStratumMeasure Y h hm =
      ENNReal.ofReal (residueConst lam m) •
        Ξ.leadingResidueMeasureU Y lam m
```

This—not equality with the raw measure—is the normalisation bridge.

Then:

```lean
theorem isFiniteMeasure_globalExtremalStratumMeasure
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    IsFiniteMeasure (Ξ.globalExtremalStratumMeasure Y h hm)

theorem globalExtremalStratumMeasure_deepZeroFibre
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm (Ξ.deepZeroFibre m) = 0

theorem globalExtremalStratumMeasure_restrict_stratumOpen
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    (Ξ.globalExtremalStratumMeasure Y h hm).restrict (Ξ.stratumOpen m) =
      (Ξ.extremalStratumMeasure Y h hm).map Subtype.val
```

The last two are essentially pushforward facts once the definition and measurability are established. The substantive theorem is:

```lean
theorem coeff_withF_eq_integral_globalExtremalStratumMeasure
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m)
    {G : Ξ.R.U → ℝ}
    (hG : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ G) :
    (Ξ.withF G hG).coeff Y lam (m - 1) =
      ∫ P, G P ∂(Ξ.globalExtremalStratumMeasure Y h hm)
```

Also expose integrability of every such `G`, using the common compact carrier.

The all-observable theorem should then be:

```lean
theorem tendsto_normalised_partitionObs_extremal_all
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    {lam : ℝ} {m : ℕ}
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    Tendsto
      (normalised lam (m - 1) (partitionObs Ξ.K Ξ.prior f))
      atTop
      (𝓝 (∫ P, f (Ξ.R.gv P)
        ∂(Ξ.globalExtremalStratumMeasure Y h hm)))
```

For the in-place strengthening, preserve the old open-subtype right side and simply remove `h0`; derive it using `integral_map`. Do the same for `tendsto_normalised_Z_extremal`. The equivalence theorem can also drop `h0`, retaining `hne`.

### Mass statements

Distinguish three equalities:

\[
\begin{aligned}
\widehat\nu(U)&=\nu(X),\\
\widehat\nu(U)&=L(1),\\
\rho(U)&=\frac{(m-1)!}{\Gamma(\lambda)}L(1).
\end{aligned}
\]

For example:

```lean
theorem globalExtremalStratumMeasure_univ
    (h : Ξ.IsExtremalData lam m) (hm : 1 ≤ m) :
    Ξ.globalExtremalStratumMeasure Y h hm Set.univ =
      ENNReal.ofReal
        ((Ξ.withF (fun _ => (1 : ℝ)) contMDiff_const).coeff
          Y lam (m - 1))
```

### Rough implementation sizes

These are planning estimates, conditional on existing compactness and local-wall lemmas:

| Block | Estimated proof/code size |
|---|---:|
| Unit 19: amplitude factorisation, product measure, integrability, coefficient identity, nullity | 600–1,100 lines |
| Trace interface and unrestricted tilted-measure variant | 150–350 lines |
| Unit 20 with an existing adapted-cover constructor | 300–700 lines |
| Unit 20 requiring new transport construction/refinement | 1,000–2,000+ lines |
| Unit 21 after representation and normalisation bridge | 200–400 lines |

The risk remains unit 20, followed by the intrinsic-depth bridge in unit 19—not the finite sum of pushforwards.

---

## 6. Paper statement

Print one of these two equivalent conventions, and keep them distinct.

### Raw residue convention

For a bounded field with compatible continuous face traces,
\[
N^\lambda(\log N)^{-(m-1)}Z_N[F;\xi]
\longrightarrow
\frac1{(m-1)!}\int_U F(x)S_\lambda(\xi(x))\,d\rho_{\lambda,m}(x).
\]

Here \(\rho_{\lambda,m}\) is finite, nonnegative, independent of \(F\) and \(\xi\), and gives \(D_{m+1}\) zero mass.

### Population coefficient convention

Set
\[
\widehat\nu_{\lambda,m}
 =\frac{\Gamma(\lambda)}{(m-1)!}\rho_{\lambda,m}.
\]
Then
\[
N^\lambda(\log N)^{-(m-1)}Z_N[F;\xi]
\longrightarrow
\int_U F(x)\frac{S_\lambda(\xi(x))}{\Gamma(\lambda)}
 \,d\widehat\nu_{\lambda,m}(x).
\]

This convention matches `globalExtremalStratumMeasure`.

The open-stratum relationship is:
\[
\widehat\nu_{\lambda,m}=\iota_*\nu^\lambda_m(0),
\]
and, for compatible fields,
\[
\iota_*\nu^\lambda_m(\xi)
 =
\rho_{\lambda,m}.\operatorname{withDensity}
 \left(\operatorname{ofReal}\frac{S_\lambda(\xi)}{(m-1)!}\right).
\]

Say **“the unique extension assigning zero mass to the removed deep fibre.”** Restriction alone does not give uniqueness. For the raw measure, the restriction agrees with the open population measure only after the factor \(\Gamma(\lambda)/(m-1)!\).

“All smooth observables” is correct once the common compact carrier and representation are proved. “Finite positive measure” should mean nonnegative; strict positivity of its mass needs a separate nonvanishing hypothesis.

Finally, one additional audit item: `piecePresentation` displays `βf = phaseConst`, whereas the empirical kernel and unit 18 use unit phase. The excerpt does not show where that constant is absorbed. If it is genuinely a phase factor \(b_pu^{2k}\), the raw residue includes \(b_p^{-\lambda}\). The existing empirical transport theorem presumably resolves this, but verify that normalisation before freezing the measure definition.

**Recommended route:** keep the explicit product-density assembly, separate raw from population normalisation, add a face-trace interface, and make the adapted-wall certificate an explicit unit-20 deliverable. Without those corrections, the requested (M4) is not a theorem of the supplied interfaces.