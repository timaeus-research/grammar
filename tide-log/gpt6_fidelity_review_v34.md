## Verdict

**u295 PASS; u296 PASS; u297 PASS; u298 PASS.** No blocking fixes in these four units.

This is a fidelity review of the supplied files against the frozen interfaces and stated scope; I have not independently rerun the reported build. The remaining canonical-coefficient bridge is a **P3 proof obligation**, not a defect in these units.

## 1. u295 — monomial shift: PASS

The exact identity is correct:
\[
(u^s\psi)\,u^h=\psi\,u^{h+s}.
\]
It preserves the phase, domain, and all other parameters. Its algebraic proof needs no integrability or regularity assumptions: it establishes equality of the integrands before integration.

`population_shift_leadingCoeff` correctly applies the population theorem to the **shifted presentation**:

- weight \(h+s\);
- amplitude \(\psi\);
- coefficient family `taylorFamily … Fψ`;
- candidate support \(\Lambda(h+s,k)\);
- minimum \(\lambda_s\) and multiplicity \(m_s\) computed from \(h+s\);
- leading coefficient `amplitudeCoeff (h+s) k ls β ψ`.

There is no double counting of the monomial factor.

The regularity of \(\psi\) is explicitly assumed, not inferred from divisorial vanishing or regularity of \(u^s\psi\). The docstring accurately records this boundary of the formalisation.

The distinction between shifted and unshifted systems is also adequate. Equality of their represented integrals does **not by itself identify their coefficient systems**; your documentation expressly avoids that inference.

`shift_min_le` supplies the promised monotonicity separately. It need not be included in the existential package.

**Scope note:** the shift identity allows any phase, whereas the population coefficient theorem specialises to zero phase. The statements make this distinction correctly.

## 2. u296 — positivity: PASS

This is the honest sufficient criterion. Since `faceProj` maps the closed cube onto the relevant closed face,
```lean
∀ u ∈ closedCube _, 0 ≤ η (faceProj … u)
```
expresses nonnegativity on that face, and the witness expresses positivity at a point **of that face**, not merely at an unrelated ambient point.

The proof addresses the relevant analytic issues correctly:

1. `η ∘ faceProj` is continuous.
2. Its restriction to the compact closed cube is bounded.
3. Multiplication by the integrable residual weight therefore gives an integrable weighted integrand.
4. Nonnegativity holds on the integration box.
5. `exists_interior_pos` is applied to the **continuous projected amplitude**, not to the potentially boundary-singular weighted integrand.
6. There is an open ball inside the open box on which the projected amplitude and residual weight are both positive.
7. That ball has positive ambient Lebesgue measure and lies in the support intersected with the integration domain.
8. The support criterion yields a positive integral, and `faceLeadConst_pos` supplies the positive prefactor.

In particular, there is no mistaken attempt to use the ambient measure of the lower-dimensional face.

`population_leadingCoeff_pos` correctly gives **chart-level denominator leading-coefficient positivity**, provided the residual prior/Jacobian amplitude satisfies the stated face hypotheses. It does not yet prove positivity or asymptotics of an assembled denominator.

A useful qualification for later prose: “positive prior × Jacobian” must mean the remaining amplitude after the relevant monomial Jacobian factors have been placed in \(u^h\). Positivity merely in the open chart, with vanishing everywhere on the projected face, would not suffice.

## 3. u297 — first candidate and equivalence: PASS

The implication is correct:
\[
f/g\to A,\qquad A\ne0
\quad\Longrightarrow\quad
f/(Ag)\to1
\quad\Longrightarrow\quad
f\sim Ag.
\]

The division rearrangement in the proof is valid, and there is no unnecessary sign restriction on \(A\). It is also appropriate that `population_isEquivalent` requires only continuity: the holomorphic-extension hypothesis is needed for the Taylor-tree package, not for the underlying first-scale limit.

`population_firstCandidate` faithfully packages:

- a Taylor-tree system representing the population integral;
- vanishing below \(\lambda\);
- vanishing at \(\lambda\) above log degree \(m-1\), **within the expansion’s degree range** `Finset.range (n + 1)`;
- identification of the top first-candidate coefficient with the face functional;
- asymptotic equivalence conditional on that functional being nonzero.

The treatment of \(A=0\) is correct. In particular, it does not conclude that the next surviving term has a larger exponent; a lower log degree at the same exponent may survive.

**Nonblocking documentation improvement:** qualify “none above log degree \(m-1\)” with “among the expansion’s log degrees \(0,\ldots,n\).” The formal statement already has the correct range.

## 4. u298 — regressions: PASS

Both requested regressions are established in one chart.

### Face dependence

The amplitudes agree at the corner, but
\[
A(1)=\frac{\sqrt\pi}{4},
\qquad
A(1+u_1)=\frac{5\sqrt\pi}{12},
\]
and the proof establishes their inequality using \(\sqrt\pi>0\).

This directly rules out determination of the general leading coefficient by the corner value alone.

### Signed cancellation

For \(\psi=1-\frac32u_1\),
\[
\psi(0)=1,\qquad
A(\psi)=\frac{\sqrt\pi}{4}
-\frac32\frac{\sqrt\pi}{6}=0.
\]
The moment calculation explicitly establishes the integrability needed for splitting the integral.

Because this example has \(m=1\), the normalised limit theorem gives
\[
\mathcal Z_\psi(N)/N^{-1/2}\longrightarrow0,
\]
which is precisely the claimed little‑\(o\) behaviour. No smaller nonnegative log degree remains at this first candidate.

**Nonblocking wording improvement:** the theorem `signed_cancellation` formally states a nonzero **corner value** and a zero face functional. That is enough here to show that the zeroth normal restriction is not identically zero, but “nonzero deepest normal jet” is an interpretation rather than an explicitly formalised jet predicate. Say so, or use the concrete wording in the theorem docstring.

## 5. P3 guidance

### A. Zero noise: use a generic condition and provide a constructor

Both proposed encodings are legitimate, but they serve different purposes.

**Generic integration theorem:** accept data with an explicit zero-noise condition, schematically
```lean
hzero : ∀ I v, xiCoord (x I v) = 0
```
with the quantification adapted to the actual chart domains.

**Population-facing construction:** construct the data from zero-phase families,
```lean
ofFamilies 0 (ψ_I v)
```
and prove the zero-noise condition once for that embedding.

This gives both reuse and a safe population API. A named predicate such as `IsPopulationData`/`HasZeroNoise` is worthwhile if the condition recurs.

The essential check is that the condition actually implies that the **phase family used by `dataBoxCoeff` and the represented integral is zero**. If `xiCoord` already is that family, this should be immediate; otherwise provide the bridge. Do not infer zero noise merely because `x : JointData` is fixed or deterministic.

Also, distinguish the coefficient family `ψ_I v : CoeffFamily` from its realised real amplitude \(\eta_{I,v}\) in notation and hypotheses.

### B. The tangential leading-coefficient target is right

For fixed chart data \(h,k,\lambda,m\), the natural target is
\[
\mathcal C_{\lambda,m-1}(x)
=
\int_K
\operatorname{amplitudeCoeff}(h,k,\lambda,\beta,\eta_v)\,d\nu(v).
\]

This assumes that \(\nu\) and \(\eta_v\), between them, include the intended tangential density, cutoff, and chart factors **exactly once**.

The clean route is:

1. identify `dataBoxCoeff … (x v) λ (m-1)` pointwise with the face functional;
2. use the definition of the tangential coefficient as the integral of `dataBoxCoeff`;
3. apply integral congruence.

No interchange of the normal and tangential integrals is needed for that coefficient identity. An explicit iterated-face-integral formula may need additional Fubini hypotheses.

However, **pointwise asymptotics alone do not justify integrating the asymptotic expansion**. The tangential expansion theorem must retain the uniform or integrably dominated remainder control supplied by the relevant `TangentialData`/`gInt` machinery. Continuity of a coefficient-family map alone should not silently replace those hypotheses.

### C. Canonical-coefficient bridge: sufficient in principle, check the exact arguments

Yes: the proposed `coeff_eq` together with the definition of `dataBoxCoeff` through `boxCoeff` is the right route. It avoids needing a separate general uniqueness theorem.

The chain should explicitly establish:
\[
C(\mu,j)
=
\operatorname{familySpectralCoeff}(\ldots,\operatorname{scale}c_\xi 1,
                                      \operatorname{scale}c_\eta 1,\mu,j)
=
\operatorname{dataBoxCoeff}(\ldots,x,\mu,j).
\]

Before treating this as automatic, check:

- the box families of the embedded data are exactly the families used in u294;
- `scale c 1 = c`;
- zero phase stays zero through every box conversion;
- the dimension, \(h,k,\beta\), and coefficient/log conventions agree;
- any box-change prefactor becomes \(1\) at \(b=1\);
- `boxCoeff` introduces no additional normalisation absent from `coeff_eq`.

At the unit box there should be no surviving box-rescaling factor, but that conclusion should be an explicit Lean bridge lemma, not a prose assumption. The quoted interfaces do not by themselves expose enough definitions to certify the final equality.

### D. Finite assembly and ordered extraction

For P3–P5:

- **Sum coefficients first, then select the leading pair.**
- Order by increasing exponent and, at equal exponent, decreasing log degree.
- Require the selected **assembled** coefficient to be nonzero.
- Permit both tangential and cross-chart signed cancellation.
- Ensure the extraction argument has the necessary support/local-finiteness control; do not assume every arbitrary nonempty subset of \(\mathbb R\) has a minimum.
- Prove the exponentially small residual is negligible relative to the selected power-log scale.
- For a ratio corollary, separately establish denominator nonvanishing, preferably positive assembled leading coefficient.

## Fix summary

**Blocking fixes for u295–298:** none.

**Nonblocking should-fixes:** clarify the finite log-degree range; make the regression’s jet terminology explicitly interpretive; qualify prior/Jacobian positivity as positivity of the residual face amplitude.

**Required before claiming P3 complete:** explicit zero-noise-to-zero-phase bridge, canonical `dataBoxCoeff` identification at \(b=1\), justified tangential remainder integration, and nonzero assembled-coefficient ordered extraction.
