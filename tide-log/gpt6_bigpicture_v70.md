## Decision

**Do (C) next. Add a small conditional global-exponent theorem as (D). Do not spend the next ten units trying to manufacture fibre-saturated ownership.**

My ranking is:

| Rank | Route | Assessment |
|---|---|---|
| 1 | **C: identify the local leading term** | High-value, bounded mathematical engineering. Requires new coefficient-identification and positivity theorems, not new resolution geometry. |
| 2 | **D: transfer the exponent through bounded overlap** | Cheap and paper-relevant **conditional on an actual finite local-box cover near the zero set**. Does not give the global coefficient or expansion. |
| 3 | **A: resolve intersections/ownership regions** | Classical in principle, but a substantial new rectilinearisation/subanalytic-integration layer. Not a “several strip charts” lemma. |
| 4 | **B: find simultaneous fibre-saturated ownership** | The unsupported geometric gate. No reason the proposed Jacobian/Voronoi rules satisfy it. Potentially the wrong intermediate statement altogether. |

The distinction is important: **the global asymptotic theorem is classical; your proposed special box-compatible partition is not thereby supplied by a classical theorem in precisely that form.**

---

## 1. Claims I would correct immediately

### 1.1 Nonzero Jacobian does not imply injectivity

This wording in CCII is wrong:

> Jacobian monomial is nonzero off the normal hyperplanes ⇒ `φ` injective there.

Nonzero determinant gives a **local** diffeomorphism. Global injectivity must come from the injectivity field of `IsMonomialChart`, together with a proof that your off-normal box lies in the locus covered by that field.

You probably used the correct field in Lean. Correct the prose, and audit that exact locus.

### 1.2 CCIV does not supply the finite cover assumed in (A)

You correctly disclaim that `Ω` is a neighbourhood. Consequently:

> Cover the compact region by finitely many local `Ω_i` from CCIV …

is an additional geometric step, not compactness applied to CCIV.

Even covering the zero set by these compact images and extracting a finite subcover is unavailable without an open-cover or lifted-compactness argument. And covering the zero set alone does not automatically cover an ambient neighbourhood of it.

You need, for example, a suitable compact lifted set covered by interiors of source boxes, plus a coverage/properness statement connecting it to the target. Your description of `Q_all` does not provide that.

### 1.3 Analytic images of boxes need not be semianalytic

In (A), the assertion

> the pulled-back overlaps are semianalytic

is generally false.

With the compact boxes and analytic neighbourhood extensions you describe, the natural conclusion is **subanalytic**, not semianalytic. Intersecting an analytic image with another chart, or taking its analytic preimage locally, does not repair this distinction.

Nor do you automatically get a finite union of analytically parametrised boxes **preserving the already exact-monomial phase**.

### 1.4 “Unconditional” needs its scope retained

CCIV is unconditional **relative to its displayed chart hypotheses**, including

```lean
∀ j, 0 < h j → 0 < e j
```

That hypothesis is not a consequence of nonnegativity of `K` alone. If the intended global application requires it for the resolution readout, that is still an audit item.

### 1.5 The displayed CCIV interface forgets useful strength

It records only `φ y₀ ∈ Ω`, not positive volume, the strip-box witness, or any coverage property. As an existential statement, a singleton would also admit a vacuous zero-integral expansion.

That does not invalidate your construction. It means the next theorem should **retain the constructed geometry**, rather than consume only the displayed existential conclusion.

Also, if `Q` is an asymptotic cutoff threshold, `∃ Q > 0` alone does not establish arbitrary-order expansion, nor identification of a leading exponent above `Q`. Check this against the actual definition of `CutoffExpansion`; the displayed signature alone does not settle it.

---

## 2. The local leading term I would stand behind

State this first in **exact-monomial coordinates**. That removes all ambiguity about strip-normalisation factors.

Let:

- \(a_j=2k_j>0\), \(h_j\in\mathbb N\), \(j=1,\dots,s\);
- \(\beta>0\);
- \(A\) be your compact tangential box;
- \(b>0\);
- \(H(t,u)\) be analytic on a neighbourhood of \(A\times[0,b]^s\).

Consider
\[
I(N)=
\int_A\int_{[0,b]^s}
H(t,u)\prod_{j=1}^s u_j^{h_j}
\exp\!\left(-N\beta\prod_{j=1}^s u_j^{a_j}\right)\,du\,dt.
\]

Define
\[
\lambda=\min_j\frac{h_j+1}{a_j},\qquad
M=\left\{j:\frac{h_j+1}{a_j}=\lambda\right\},\qquad
m=|M|,
\]
and \(L=\{1,\dots,s\}\setminus M\). Write \(\iota_L(v)\) for the vector with coordinates \(v_j\) on \(L\) and zero on \(M\).

Then the coefficient is
\[
\boxed{
C=
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(m-1)!}
\left(\prod_{j\in M}\frac1{a_j}\right)
\int_A\int_{[0,b]^L}
H(t,\iota_L(v))
\prod_{j\in L}v_j^{h_j-a_j\lambda}\,dv\,dt .
}
\]

The precise asymptotic statement is
\[
\boxed{
\lim_{N\to+\infty}
\frac{N^\lambda}{(\log N)^{m-1}}I(N)=C.
}
\]

All the face weights are integrable because
\[
h_j-a_j\lambda>-1\qquad(j\in L).
\]

### Crucial qualifications

1. **For signed analytic \(F\), \(C\) can vanish.**  
   Then \((\lambda,m)\) is a candidate geometric pair, not necessarily the actual leading pair.

2. **Positivity must be proved.**  
   A convenient sufficient condition is \(H\ge0\) on the box and strict positivity at a point of the critical face with a relatively positive-measure neighbourhood. For the centred construction, shrinking until \(F>0\) throughout the chart image when \(F(\phi y_0)>0\) is especially clean.

3. **The face integral includes the nonminimising normal coordinates.**  
   It is not generally just an integral over the tangential base. That simplification holds when every normal coordinate minimises, or after those other coordinates have explicitly been integrated out.

4. **The amplitude is the fully transformed amplitude.**  
   For CCIII it includes the strip-Jacobian and monomial-rescaling factors. Do not silently replace it by `jac₀ · F ∘ φ`.

### Two-sided normalisation

For
\[
I_{\pm}(N)=
\int_A\int_{[-b,b]^s}
H(t,u)\prod_j|u_j|^{h_j}
e^{-N\beta\prod_j u_j^{a_j}}\,du\,dt
\]
with even \(a_j\), the coefficient is
\[
\boxed{
C_{\pm}=
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(m-1)!}
\left(\prod_{j\in M}\frac{2}{a_j}\right)
\int_A\int_{[-b,b]^L}
H(t,\iota_L(v))
\prod_{j\in L}|v_j|^{h_j-a_j\lambda}\,dv\,dt .
}
\]

This is exactly what summing the reflected orthants should produce. In particular, **do not insert an extra \(2^s\)**: the nonminimising signs are already inside the two-sided face integral.

### Multiplicity

For this nonvanishing leading face contribution:

- pole multiplicity: \(m\);
- highest logarithmic degree: \(m-1\);
- \(m\) is the **number of minimising normal coordinates**.

“Maximal face dimension” is unsafe without specifying the polyhedron and convention. The relevant minimizing simplex has dimension \(m-1\); the coordinate face on which you integrate has normal dimension \(s-m\). Those are different objects.

---

## 3. First three units for (C)

These are proposed interfaces, not claims that the names already exist in your repository. I would use real \(N\to+\infty\), then restrict to natural \(N\) if required.

### Unit 1 — `CriticalLattice`

**Purpose:** identify the pole at \(\lambda\) across *every amplitude monomial*, and establish a uniform gap above it.

Inputs:

```lean
s : ℕ
hs : 0 < s
a h : Fin s → ℕ
ha : ∀ j, 0 < a j
```

Define
```lean
ratio j := ((h j : ℝ) + 1) / (a j : ℝ)
λ := min_j ratio j
M := Finset.univ.filter (fun j => ratio j = λ)
m := M.card
```

Export:

```lean
theorem latticeMin_pos : 0 < λ

theorem critical_nonempty : M.Nonempty

theorem noncritical_weight_gt_neg_one
    {j : Fin s} (hj : j ∉ M) :
    -1 < (h j : ℝ) - (a j : ℝ) * λ
```

The important series-facing theorem is:

```lean
theorem shifted_ratio_eq_min_iff
    (q : Fin s → ℕ) (j : Fin s) :
    (((h j : ℝ) + (q j : ℝ) + 1) / (a j : ℝ) = λ) ↔
      j ∈ M ∧ q j = 0
```

And a uniform spectral gap:

```lean
theorem exists_uniform_pole_gap :
    ∃ η : ℝ, 0 < η ∧
      ∀ (q : Fin s → ℕ) (j : Fin s),
        let r := ((h j : ℝ) + (q j : ℝ) + 1) / (a j : ℝ)
        r = λ ∨ λ + η ≤ r
```

A possible gap is the minimum of
\[
\begin{cases}
1/a_j,&j\in M,\\
(h_j+1)/a_j-\lambda,&j\notin M.
\end{cases}
\]

**Why this unit matters:** Taylor monomials attain the top log degree at \(\lambda\) exactly when they have zero degree on **all** critical coordinates. Their unrestricted noncritical Taylor degrees must then resum to the face integral.

**Mathlib support:** finite minima (`Finset.min'_mem`, `Finset.min'_le`, `Finset.le_min'`), finite products, cast arithmetic, `div_le_div_iff₀`, `linarith`, `positivity`. Reuse CLXXXV where it already proves the same finite combinatorics.

**Hazard:** proving only the \(q=0\) case does not identify the analytic-amplitude coefficient.

---

### Unit 2 — `MonomialLeadingFace`

Define:

- `X := (Fin t → ℝ) × (Fin s → ℝ)`;
- `Box A b := A ×ˢ {u | ∀ j, u j ∈ Set.Icc 0 b}`;
- `LaplaceBox ... H N` by the integral above;
- `leadingFaceCoeff ... H` by the boxed formula, using the subtype of noncritical indices for the residual normal space.

For a first bounded interface, take \(A=[-B,B]^t\), \(B>0\). General measurable tangential bases can wait.

Main theorem:

```lean
theorem monomial_leadingFace
    (hB : 0 < B) (hb : 0 < b) (hβ : 0 < β)
    (hH : AnalyticOnNhd ℝ H (Box (tangentBox B) b)) :
    Tendsto
      (fun N : ℝ =>
        Real.rpow N λ / (Real.log N) ^ (m - 1) *
          LaplaceBox a h β (tangentBox B) b H N)
      atTop
      (𝓝 (leadingFaceCoeff a h β (tangentBox B) b H))
```

Also export integrability of the face integrand and a positivity lemma, for example:

```lean
theorem leadingFaceCoeff_pos
    (hH : AnalyticOnNhd ℝ H (Box (tangentBox B) b))
    (hHnonneg : ∀ z ∈ Box (tangentBox B) b, 0 ≤ H z)
    (hH0 : 0 < H (0, 0))
    ... :
    0 < leadingFaceCoeff a h β (tangentBox B) b H
```

The two-sided theorem should follow by reflection and summation.

**Proof route:** use the existing ℓ¹ amplitude machinery and identify its top coefficient. Do not start another Laplace proof unless inspection shows that the existing coefficient interface is unusable.

**Mathlib support:**

- `AnalyticOnNhd.continuousOn`;
- compact-set integrability and boundedness;
- `MeasureTheory.integral_prod`;
- `MeasureTheory.integral_congr_ae`;
- `MeasureTheory.integral_finset_sum`;
- `Real.rpow_pos_of_pos`, rpow algebra;
- the real-rpow interval-integral and Gamma-integral declarations.

For exchanging an infinite series and an integral, reuse your already-proved series bounds. Dominated-convergence machinery is available, but the necessary domination is your theorem, not something Mathlib will infer.

**Hazards:**

- dimensions zero: \(t=0\) and \(L=\varnothing\) must use the volume of the zero-dimensional space correctly;
- negative residual exponents at coordinate zero are harmless a.e., but pointwise simplification is treacherous;
- the \(m=1\) case has \(0!=1\) and log power zero;
- fixed box endpoints affect lower log coefficients, not the displayed highest-log factor for critical coordinates;
- an abstract expansion with unnamed coefficients does not itself establish this formula.

---

### Unit 3 — `CentredChartLeadingTerm`

Strengthen the CCIV output to retain the actual normalized-box data. Prefer a structure containing:

- `Ω`, compactness and containment;
- the source box and normalized map;
- \(a,h,\beta\);
- the fully transformed analytic amplitude;
- the integral change-of-variables identity;
- the leading coefficient.

Then prove, schematically:

```lean
theorem IsMonomialChart.local_identified_asymptotic
    -- all the CCIV hypotheses
    ... :
    ∃ D : LocalLeadingPresentation hc y₀ F,
      Tendsto
        (fun N : ℝ =>
          Real.rpow N D.λ / (Real.log N) ^ (D.m - 1) *
            ∫ x in D.Ω, F x * Real.exp (-N * K x))
        atTop
        (𝓝 D.leadingCoeff)
```

The structure should identify
\[
D.\lambda=\min_j\frac{h_{n_j}+1}{2k_j},
\qquad
D.m=\#\operatorname{argmin}_j\frac{h_{n_j}+1}{2k_j}.
\]

Add the stronger positive-observable theorem:

```lean
theorem IsMonomialChart.local_positive_leading_term
    -- all the geometric hypotheses
    (hF : AnalyticOnNhd ℝ F U)
    (hFy₀ : 0 < F (φ y₀)) :
    ∃ D : LocalLeadingPresentation hc y₀ F,
      0 < D.leadingCoeff ∧
      Tendsto ... (𝓝 D.leadingCoeff)
```

Here the construction shrinks the box using continuity so that \(F>0\) on its image.

**Mathlib support:** your change-of-variables and reflection units should do nearly all the work; continuity supplies the positive neighbourhood; finite-sum limits assemble orthants.

**Hazard:** for an already-fixed large CCIV box, positivity merely at `φ y₀` does not rule out cancellation elsewhere. The positivity theorem above chooses a smaller box.

After these three units, identify the corresponding **canonical cutoff coefficient**, using an asymptotic-uniqueness theorem and a cutoff extending beyond \(\lambda\). That is a separate interface obligation, not automatic from the existence of an expansion.

---

## 4. What (A) actually requires

There is a classical route here, but it is substantially larger than the proposed intermediate statement.

For compact analytic box images:

1. establish subanalyticity of images, intersections and ownership regions;
2. rectilinearise those regions;
3. do so compatibly with the phase and the Jacobian data;
4. integrate on the resulting quadrant/box-type pieces;
5. control multiplicities or use a decomposition with an appropriate integration identity.

The relevant literature is **Hironaka’s rectilinearisation of subanalytic sets**, together with resolution/monomialisation methods for integration. Semianalytic stratification alone is not enough: a smooth stratum or analytic boundary need not be a product region compatible with your monomial phase.

There is also an off-divisor analytic transition map wherever both charts are invertible. But it need not extend analytically across the divisor. That is precisely where the asymptotic geometry lives.

So:

> Is the bounded version accessible?

Mathematically yes. **Not plausibly as a ten-unit corollary of the listed interfaces.** You would be building a new geometric subsystem. “Several analytic images of boxes” disguises rather than removes that work.

---

## 5. Why (B) is not a promising shortcut

Your doubt is correct.

A largest-Jacobian rule compares functions depending on normal coordinates. A Voronoi rule usually does the same. Neither produces walls saturated along the normal fibres of the owning chart.

Moreover, the fibre structures need not agree across charts. Requiring compatibility with both is much stronger than measurable disjointisation.

Thus:

- measurable ownership: engineering;
- proving its pullbacks admit your required core tilings: the geometric gate;
- finding a magic ownership rule that avoids that gate: currently unsupported.

I would not make simultaneous fibre saturation a conjectured necessary feature of the final proof. Rectilinearisation may solve the integration problem by **changing charts again**, rather than respecting the original fibres.

---

## 6. A useful fourth route: global exponent without global expansion

For a nonnegative observable, overlap is much less problematic for the exponent.

Suppose you separately obtain finitely many local regions \(\Omega_i\subseteq R\) such that:

- they cover \(R\cap\{K<\delta_0\}\) a.e.;
- the omitted part has \(K\ge\delta_0>0\) a.e.;
- its amplitude is integrable;
- every local integral has a positive identified leading term.

If there are \(r>0\) pieces, then
\[
\frac1r\sum_i I_i(N)
\le
\int_{\bigcup_i\Omega_i}F e^{-NK}
\le
\sum_i I_i(N).
\]

A better multiplicity bound replaces \(r\). Therefore the actual target integral has order
\[
\Theta\!\left(N^{-\lambda_*}(\log N)^{m_*-1}\right),
\]
where
\[
\lambda_*=\min_i\lambda_i,\qquad
m_*=\max\{m_i:\lambda_i=\lambda_*\}.
\]

Equivalently,
\[
\log Z_N
=
-\lambda_*\log N+(m_*-1)\log\log N+O(1).
\]

**No ownership and no intersection expansions are needed.** But the finite local-box coverage hypothesis remains real; CCIV does not discharge it.

This would turn your summed-chart exponent theorem into a conditional theorem about the actual target measure. It is a good small addition after (C), clearly labelled conditional.

---

## Bottom line

The paper’s global expansion is the stronger eventual payoff. **The best next payoff is the local identified leading term**, because it is now within reach and exposes exactly the positivity, normalization and coefficient issues that any global theorem will also need.

Your current obstruction is not another reflection, strip, or summability lemma. It is a **geometric integration identity across charts**, with a separate **finite local-box coverage problem** before it.

Finish the spectral content of the theorem you genuinely have. Keep the global gate explicit.
