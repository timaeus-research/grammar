# A. The migration map

## A.0. Editorial decisions to make before moving text

The new paper should distinguish three levels throughout:

1. **Formal chart statements:** meromorphic continuation, polar coefficients, support/jet congruence, B1, B4, and the constant-field \(x^2y^2\) regression.
2. **Formal resolved leading statements:** the measures on \(U\), the all-observable limits, and the extremal identification **under a certificate on the transport**.
3. **Analytic packaging or derivations not yet formalised:** distribution-valued continuity, the log-weighted jet interchange needed for (*), general closed finite-part evaluations, and the intrinsic branch-space construction.

Two limitations of the supplied formal evidence matter:

- `ChartZetaPolarSupport.lean` explicitly does **not** establish linearity and continuity of `chartPolarCoeff` as a distribution-valued map; that is deferred to unit 24. The paper may use the classical distribution language, but must distinguish this analytic packaging from the formal scalar-pairing theorems.
- No supplied declaration proves the general finite-part identification, B15–B16, or the **variance-2 lemma on the statistical bridge**. Do not infer their formalisation from the programme’s original unit numbering. In the supplied completed route, `EmpiricalCouplingAllLog.lean` supplies B4, not the missing log-weighted jet interchange.

Use the following compiled architecture:

```latex
\input{sections/01_expectations}
\input{sections/02_polar_distributions}
\input{sections/03_polar_coefficients}
\input{sections/04_radial_tilting}
\input{sections/05_posterior_limits}
\input{sections/06_averaging}

\appendix
\input{sections/A_chart_proofs}
\input{sections/B_finite_parts}
\input{sections/C_expansion_algebra}
\input{sections/D_special_functions}
\input{sections/E_gaussian_gibbs}
\input{sections/F_formalisation}
```

Remove the four `\part` divisions. Put the bibliography after the appendices, or leave it before them if that is house style.

**Label policy.** Retain theorem/equation labels when replacing a statement by its successor. Give the six new sections new architectural labels where needed; retain old section labels as unique landing anchors on the relevant subsections. Never duplicate a label between the condensed main-text version and its appendix expansion.

In the inventory below, **“unlabelled under `sec:...`” means exactly that the present subsection has no `\label`**. Do not manufacture a purported current label.

---

## A.1. New §1 — What a posterior expectation sees

Suggested section label: retain `sec:introduction`.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `sec:introduction`, **Introduction**, opening question and ratio \(Z_n[f]/Z_n[1]\) | **Rewrite/condense** into the opening two paragraphs. Retain the motivating observables, but replace the stratum-first thesis by the polar-distribution thesis. |
| `sec:setting`, **Partition functions with insertion** — unlabelled subsection | **Split.** Move only the definitions of \(\Zcal_n[f]\), \(Z_n[f]\), and the cancellation of the empirical-loss normalising constant here. Full hypotheses go to §2. |
| `sec:examples`, **The running examples**, especially `ex:planes` | **Split/rewrite.** Introduce the positive unit-square \(x^2y^2\) calculation here; explain separately that four signed quadrants recover the interior-wall example. Keep `ex:planes` for the three-dimensional geometric example in §2/§3. |
| `sec:fluctuation`, **Index derivatives and logarithms** — unlabelled subsection | Move the constant-amplitude, constant-field \(x^2y^2\) calculation here, **rewritten** as the complete regression theorem through the constant log term. The general index-derivative discussion moves to §4. |
| `sec:tiers`, **The Laurent data and the three tiers**, constant \(x^2y^2\) specialisation | **Merge** into that calculation; delete the duplicate presentation. |
| `sec:conclusion`, paragraph **Related work** | **Condense/rewrite** into “Classical ingredients and the contribution of this paper.” |
| `sec:conclusion`, paragraph **Relation to the earlier paper** | **Condense** to one attribution paragraph or footnote here. |
| `sec:introduction`, paragraphs **Plan** and **Notation** | **Replace.** Print the new six-section plan; use only notation needed immediately. Detailed conventions belong to §2. |

### New material

1. **Accessible main theorem:** coefficients are polar data; leading coefficients are integrals against a finite positive measure; posterior expectations are formal normalisations.
   - Chart polar data: `chartZetaAtDepth_sub_polarPart_isBigO_one`, `chartPolarCoeff`.
   - Empirical coefficients: `ofReal_empCoeff_eq_couplingPolarCoeff`.
   - Leading measure: `hasLeadingTerm_empZ_eq_integral_leadingU`.
   - Extremal identification: `globalExtremalStratumMeasure_eq`.
   - Quotient: retain `cutoff_div_isBigO'`.

2. **Complete constant-field \(x^2y^2\) calculation**, as in B.5 below.
   - `empCoeff_xy_sq_one`
   - `empCoeff_xy_sq_zero`
   - `tendsto_logExample`
   - `tendsto_logExample_empCoeff`

3. A short status paragraph:
   > The chart polar identities, the coupling-average formula, and the global leading-measure theorem are formalised. The amplitude form (*) is stated under an explicit interchange hypothesis. Distribution-valued terminology packages the scalar pairing identities; its full topological formalisation is not claimed.

### Delete or replace

- Delete the claim that the paper is organised around three actors as its actual architecture: **superseded**.
- Delete “every coefficient is a measure or a normal derivative integrated over one stratum” as an unrestricted description: **misleading** without finite parts and depth restrictions.
- Delete the blanket final sentence of the abstract saying that “the statements have been formalised”: **too broad**.
- Rewrite the abstract only after §§2–5 are stable.

---

## A.2. New §2 — Meromorphic distributions and normal-crossing computation

Suggested section label: `sec:polar_distributions`.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `sec:setting`, **Partition functions with insertion** — unlabelled | **Rewrite** the full geometric hypotheses here. State the formal resolved scope—open ambient domain, compactly supported smooth prior—here, not only in coverage. Distinguish positive-box boundary examples from assembled boundary-domain theorems. Retain `sec:setting` as the landing anchor. |
| `sec:scale`, **Asymptotic expansions in the scale…** | **Condense** to cutoff expansions, uniqueness, and the lattice. Move quotient discussion to §5 and technical algebra to Appendix C. |
| `sec:resolution`, **The theorem** — unlabelled | **Condense** to the real normal-crossing presentation actually used. Retain `eq:real_normal_form`. Move the complexification and real-structure discussion to Appendix A’s resolution supplement. |
| `sec:resolution`, **The two divisors** — unlabelled | **Condense/rewrite** as phase orders \(2k_i\), density orders \(h_i\), and amplitude. Retain `eq:one_variable`. |
| `sec:resolution`, **Irreducible components as primes** — unlabelled | **Move to Appendix A**, condensed as geometric background. |
| `ex:blowup`, **An example with a blow-up** | **Condense**, retaining the two charts, the pair \((2,1),(1,0)\), and the tie. Move the observable computations to §3’s cancellation discussion. |
| `sec:stratification`, **Depth and strata** — unlabelled | **Condense/rewrite**. Introduce geometric depth and resonance count separately. Explicitly define the support-truncated deep zero fibre used by formal resolved statements. |
| `sec:stratification`, **Exponents and multiplicities of a stratum** — unlabelled | **Rewrite** around candidate poles versus actual poles. Keep the explanatory two-wall mechanism. Move leading-measure conclusions to §3. |
| `sec:normal_geometry`, **Normal and tangential coordinates** — unlabelled | **Condense** to normal-crossing coordinate changes and the conormal splitting. |
| `sec:normal_geometry`, **The fibre integral and the bare moments** — unlabelled | **Split.** Keep one paragraph explaining local amplitudes. Move bare-moment calculations to Appendix A. |
| `rem:flat`, **Why the crossing does not see everything** | **Keep, lightly rewrite**, immediately before the face-sum formula. This is essential motivation, not an appendix aside. |
| `rem:cutoff`, **Cutoffs** | **Keep, condensed**, after the localised chart presentation. |
| `sec:conormal`, **What is intrinsic** | **Split/rewrite.** Keep the distinction between a functional and a coordinate presentation here. Move ideal-power descent and principal-symbol discussion to §3 after admissibility. |
| `sec:population`, **The per-stratum decomposition** — unlabelled | **Rewrite** as “Localisation and chart assembly.” It is a chart decomposition, not a canonical decomposition by strata. Retain `eq:strata_decomposition` with corrected wording. |
| `sec:population`, **The zeta function of a stratum and the shape of the expansion** — unlabelled | **Split.** Move the bare monomial product here, using the positive-pole \(s\)-convention. Move `eq:zeta_leading` to Appendix B or a short §3 example. Move `thm:population_expansion` to §3. |
| `sec:tiers`, opening through `eq:laurent` | **Rewrite/split.** Define the Gamma-free \(T(s)\) here. Put the Mellin transform \(\Gamma(s)T(s)\) and coefficient conversion in §§3–4. Preserve `eq:laurent` at that conversion. |

### New material

In this order:

1. \(T(s)\) downstairs, \(\widetilde T(s)\) upstairs, \(\pi_*\widetilde T=T\).
2. Gamma-free chart functional \(T_{h,k}(s)[G]\).
3. Candidate resonance set, \(M_\mu\), and the distinction between an order bound and an actual pole.
4. Taylor-subtracted face decomposition and continuation:
   - `chartZeta_eq_sum_faces`
   - `chartZetaAtDepth_eq_chartZeta`
   - `differentiableOn_chartZetaAtDepth`
   - `chartZetaAtDepth_eq_of_depths`
5. Polar coefficient theorem and explicit chart formula:
   - `chartPolarCoeff`
   - `chartZetaAtDepth_sub_polarPart_isBigO_one`
6. Reality, resonant support, rectangular jet congruence:
   - `ofReal_chartPolarReal`
   - `chartPolarCoeff_eq_zero_of_jetsZeroOn`
   - `chartPolarCoeff_eq_zero_of_eqOn_zero`
   - `chartPolarCoeff_congr`
7. A subsection **Tests upstairs and observables downstairs**: \(G\) is arbitrary upstairs; the statistical observable is \(G=f\circ\pi\). Resolution independence belongs to the pushed-down functional, not to an identification of arbitrary tests on different resolutions.

### Delete or correct

- Eliminate the use of \(z\) and \(s\) for opposite zeta conventions in the main argument. Keep \(z=-s\) only in a historical notation remark.
- Delete “a stratum contributes precisely when…” where it asserts actual nonvanishing: replace by **“can contribute only when…”**.
- Delete claims that candidate sets are resolution-independent.
- Do not describe formal jet congruence as an already formalised continuous map into distributions.
- Do not call \(\Gamma(s)\int fK^{-s}\varphi\) simply “Watanabe’s zeta function” without distinguishing it from the zeta pairing itself.

---

## A.3. New §3 — Polar coefficients, residues and finite parts

Retain `sec:population` as this section’s main label, or use `sec:polar_coefficients` and retain `sec:population` as an alias.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `thm:population_expansion` from the unlabelled population zeta subsection | **Rewrite** as a clean existence/uniqueness/support theorem. Remove the bundled informal assertion about the “first contribution of a stratum”; place that in the cancellation discussion with its qualifications. |
| `sec:leading`, **The leading term with insertion** | **Replace** by the global leading-measure theorem and extremal identification in B.4. This comes **before** restricted stratum formulas. |
| `ex:population_examples`, **The running examples** | **Split/rewrite.** Put the global axis and mixed-exponent leading measures immediately after the global theorem. Put the depth-one divergent plane measure after admissibility and residues. |
| `sec:exact_strata`, **Depth, exact strata and admissible observables** | **Retain/rewrite**, after the global theorem and before every restricted depth-graded claim. Say these restrictions remain necessary for the general associated-graded theory, not for the global leading term. |
| `sec:graded`, **The graded stratum formula** | **Retain, condensed**; explain it as the restricted top-pole evaluation. |
| `sec:jets`, **Jet dependence, without coordinates** | **Retain**, with the exact top-degree/admissibility hypotheses. |
| Remaining part of `sec:conormal`, **What is intrinsic** | **Merge here**: ideal powers, associated graded, principal symbol, and noncanonical splitting. |
| `sec:stratum_measure`, **The stratum measure** | **Retain/rewrite** as the general zero-order measure on the open stratum. Separate formal test representation from any broader integrability assertion not explicitly supplied. |
| `sec:residue`, **The weighted logarithmic residue** | **Condense** to `eq:face_density`, `eq:residue_measure`, `thm:residue`, and the chart identity. Move density-residue calculus and truncated negative moments to Appendix B. |
| `sec:tiers`, **One resonant coordinate** | **Condense** to the FP formula for \(A_{\mu,1}\), with its analytic status stated. Full Taylor-subtracted evaluation goes to Appendix B. |
| `sec:tiers`, **Ties** | **Rewrite** in terms of \(A_{\mu,r}\) and Gamma derivatives. Keep one nonconstant \(x^2y^2\) formula; move detailed evaluation to Appendix B. |
| `sec:wallcrossing`, **Wall-crossing** | **Move/rewrite** as “Observable vanishing and cancellation.” State vanishing of the relevant functional first; monomial divisibility is a useful sufficient condition, not the universal mechanism. |
| `rem:parity`, **Parity** | **Retain**, after cancellation, with the signed-root adapter cross-reference to §4. |
| `sec:setting`, **Comparability** — unlabelled | **Move, condensed**, after cancellation. |
| Observable computations from `ex:blowup` | **Move here**, condensed. |
| `sec:population_posterior`, **Population posterior expectations** | **Move to §5**; retain only a one-sentence forward reference here. |

### New material

1. Population coefficients as the Laurent data of \(\Gamma(s)\widetilde T(s)\), including
   \[
   c^{\rm pop}_{\mu,q}(F)
   =\frac1{q!}\sum_{r=q+1}^{M_\mu}
     \frac{(-1)^{r-q-1}\Gamma^{(r-q-1)}(\mu)}
          {(r-q-1)!}\,A_{\mu,r}[F].
   \]
   Backing: B4 at zero field, `polarAmplitudeCoeff_eq`, and the Gamma log moments. Do not conflate this with \(A_{\mu,q+1}[F]\).

2. Closed-face/raw leading measure and finiteness:
   - `leadingFaceMeasure`
   - `leadingFaceMeasure_univ_lt_top`
   - `leadingFaceMeasure_deep`
   - `leadingResidueMeasureU`
   - `isFiniteMeasure_leadingResidueMeasureU`

3. Certificate and intrinsic bridge:
   - `ExtremalCertificate`
   - `extremalCertificate_of_divPt_zero`
   - `chartLeading_of_extremalData`

4. Global identification and all-observable population coefficient:
   - `leadingResidueMeasureU_deepZeroFibre`
   - `globalExtremalStratumMeasure_eq`
   - `coeff_withF_eq_integral_globalExtremalStratumMeasure`
   - `tendsto_normalised_partitionObs_extremal_all`

5. One boxed normalisation convention, used thereafter:
   \[
   \boxed{\rho^\lambda_m\text{ is raw},\qquad
   \nu^\lambda_m=\frac{\Gamma(\lambda)}{(m-1)!}\rho^\lambda_m
   \text{ is population-normalised}.}
   \]
   At the extremal pair, the latter is the global extension of the existing stratum measure.

### Delete or replace

- Replace all of old `thm:leading`; do not retain the mass inequality as the principal result.
- Delete “This extension is a derivation and is not among the pinned declarations.”
- Delete the denominator convention “either \(D_{m+1}=\varnothing\) or the extended measure is understood.”
- Delete any unconditional `IsExtremalData ⇒ ChartLeading` claim.
- Keep the general stratum measure’s possible infinite mass. The global leading theorem does **not** make every \(\nu^\mu_c\) finite.
- Keep general finite-part formulas marked as analytic evaluations: no supplied declaration closes that gap.

---

## A.4. New §4 — Universal radial tilting

Suggested label: `sec:radial_tilting`; retain `sec:fluctuation` and `sec:empirical` on their landing subsections.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `sec:setting`, **The standard form of the empirical divergence** — unlabelled | **Move/rewrite** as the statistical source of a root field. State exactly which assumptions are statistical and which are not used by B1/B4. |
| `sec:empirical`, **Root fields** — unlabelled | **Rewrite** immediately after standard form. Add the explicit orthant adapter. |
| `sec:fluctuation`, **The one-variable computation** — unlabelled | **Retain, condensed**, with `def:fluctuation` and complex \(S_s\). |
| `sec:fluctuation`, **The ladder** — unlabelled | **Split.** Keep ladder, recurrence, and the one-dimensional coefficient pattern. Move proof, Weber form, Weyl algebra, and regular-orbit discussion to Appendix D. |
| `sec:fluctuation`, **Index derivatives and logarithms** — unlabelled | **Retain, condensed**; remove the duplicate constant \(x^2y^2\) calculation, now in §1. |
| `sec:empirical`, **The coefficients** — unlabelled | **Rebuild completely**: B1 → B4 → conditional (*) → graded specialisation → generating identity. Preserve `eq:empirical_graded`, `eq:fluctuation_zeta`, and `eq:generating` at their new homes. |
| `sec:empirical`, **The expansion** — unlabelled | **Retain/rewrite**, after B4 and (*), as the uniform expansion theorem. Call it “frozen,” not “fixed sample,” in the theorem title. |
| `sec:first_orders`, **What enters at the first orders** | **Retain/rewrite** as two calculations: one resonant coordinate under the gap hypothesis; nonconstant \(x^2y^2\) tie, with the latter explicitly a derivation under interchange/FP evaluation. |
| `sec:empirical`, **How much of the field is seen** — unlabelled | **Retain, corrected**: distinguish formal support/jet dependence from formal continuity, which remains pinned only for the depth-graded coefficients. |
| `sec:fluctuation`, **The field in the exponent, and the incomplete function** — unlabelled | **Move to Appendix D**, leaving one sentence about uniform tail estimates in the expansion subsection. |
| Leading part of old **The coefficients**, `eq:empirical_leading` | **Replace** by the all-observable tilted measure theorem, after the uniform theorem or as the closing subsection. |

### New material

- B1: `mellin_empIntegral_eq_coupledChartZeta`.
- Coupled continuation:
  `empZetaAtDepth_eq_mellinContinuation`.
- B4:
  `empIntegratedPolarCoeff_eq_couplingPolarCoeff`,
  `ofReal_empCoeff_eq_couplingPolarCoeff`.
- Conditional (*), with the explicit interchange hypothesis in B.3.
- Tilted leading measure:
  `empiricalLeadingMeasureU`,
  `hasLeadingTerm_empZ_eq_integral_leadingU`,
  `isFiniteMeasure_empiricalLeadingMeasureU`,
  `empiricalLeadingMeasureU_zero`.
- Orthant rule
  \[
  \zeta_\sigma(v)=\Big(\prod_i\sigma_i^{k_i}\Big)\xi(\sigma v).
  \]
  The supplied excerpts establish the positive-box theory; do not attach an invented adapter declaration.

### Delete or replace

- Delete “a chart-level Mellin identity … is not yet in the library.”
- Replace the bridge-only justification of `eq:fluctuation_zeta` by the grammar chart theorem plus assembly; retain the bridge reference for its genuinely statistical statement.
- Delete “the lower logarithmic orders have no closed geometric formula” if intended to exclude polar-distribution formula (*). Say instead that they do not have the **single-stratum ordinary-integral form** of the graded formula.
- Do not upgrade (*) to an unconditional formally backed theorem.
- Do not identify the tilt with \(S_\lambda(\xi.\psi)\) on \(U\) when branch traces differ.

---

## A.5. New §5 — Posterior normalisation and the sample limit

Retain `sec:posterior`.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `sec:posterior`, **Blocks and the quotient** — unlabelled | **Rewrite** to begin with observable-valued coefficient blocks, followed by scalar evaluation and formal normalisation. Retain `eq:quotient_blocks`, `thm:posterior_quotient`. |
| `sec:population_posterior`, **Population posterior expectations** | **Condense/merge** into a population specialisation of the leading posterior theorem. Retain the three cancellation regimes, but formulate them in terms of first nonzero coefficients. |
| `sec:posterior`, **The leading term** — unlabelled | **Replace** by the all-observable quotient using \(\widehat\nu(\xi)\). Remove \(D_{m+1}=\varnothing\) and branch-agreement assumptions. Give the single-density formula only as a compatible-trace specialisation. |
| `sec:limit`, **Convergence in law of the coefficients** — unlabelled | **Rewrite** into separate frozen, empirical-diagonal, and Gaussian-limit statements. Retain `sec:limit` as its landing anchor. |
| `sec:limit`, **What is a hypothesis** — unlabelled | **Merge immediately after those statements**, not at the end of a distant section. |
| `sec:posterior`, **The source and the connected coefficients** — unlabelled | **Condense** as a corollary of formal normalisation; move recursion details to Appendix C. |
| `sec:posterior`, **Wall-crossing with data** — unlabelled | **Condense/merge** with the three coefficient-cancellation regimes. |
| `sec:posterior`, **Tied strata and the two-site phenomenon** — unlabelled | **Move to §6**. |

### New material

1. Distribution/functional-valued blocks:
   \[
   B_j^\psi(\ell)[F]=\sum_q c_{\lambda+j/Q,q}(F;\psi)\ell^q.
   \]
   Their posterior normalisation is evaluated at \(1\) in the denominator. Do not assert a new formal topological distribution-valued construction.

2. Frozen leading probability:
   \[
   \Pi_\xi=\pi_*\!\left(\frac{\widehat\nu^\lambda_m(\xi)}
                                  {\widehat\nu^\lambda_m(\xi)(U)}\right),
   \]
   assuming positive total mass.

3. State diagonal convergence only under the uniform-remainder/tightness and denominator hypotheses; state Gaussian convergence only under the relevant process convergence.

4. If a compact branch parameter space is used, define it as the finite disjoint union of the closed leading-face parameter spaces of the transport. This is atlas-dependent. The intrinsic oriented blow-up is future work, not an object already supplied by these formal files.

### Delete or replace

- Delete all denominator admissibility restrictions.
- Delete unqualified random asymptotic notation \(\sim D_n\cdots\). Specify a frozen statement, or a diagonal error statement in probability.
- Do not claim all lower-log coefficients now have formal continuity/convergence-in-law theorems merely because B4 identifies them.

---

## A.6. New §6 — What averaging does and does not preserve

Retain `sec:averaging`.

### Existing material, in reading order

| Current source | Action and destination |
|---|---|
| `sec:averaging`, **Where the theory stops** — unlabelled | **Split/rewrite.** Begin with bounded posterior convergence once convergence in law is established; end the section with remaining statistical and branch-space identifications. |
| `sec:limit`, **Averaging over the sample: the fluctuation function of a Gaussian** — unlabelled | **Move/rewrite** immediately after bounded posterior convergence. Emphasise the critical value \(v=2\), not just \(v>2\). Move Wick-series details to Appendix E. |
| `sec:posterior`, **Tied strata and the two-site phenomenon** — unlabelled | **Move nearly verbatim**, including `eq:two_site`; adjust references. |
| `sec:averaging`, **The limit posterior** — unlabelled | **Condense** to the compact-base Gibbs model and radial lift `eq:gibbs`. Keep its geometric identification conditional. |
| `sec:averaging`, **Three exact identities** — unlabelled | **Move to Appendix E**. Leave a short summary and perhaps the Fréchet derivative as the sole displayed identity. |
| `sec:conclusion`, paragraph **Conclusion** | **Rewrite** as the closing two or three paragraphs of §6. No seventh main section. |

### New material

1. A proposition: convergence in law of bounded posterior expectations implies convergence of their expectations. This is standard bounded-continuous-test reasoning; do not invent a new grammar declaration.
2. A critical-variance statement conditional on the variance-2 bridge lemma:
   - The scalar threshold is backed by `lintegral_gaussMomentJ_lt_top_iff`.
   - The assertion that the model’s limiting root field has variance exactly \(2\) on the relevant zero fibre needs the **actual bridge declaration and bridge pin**, neither supplied here.
3. An explicit distinction:
   - finite-sample \(\E Z_n[1]=\int\varphi\);
   - normalised evidence and its Gaussian leading limit;
   - bounded posterior ratios.
4. State that a nonintegrable limiting normalised evidence rules out uniform integrability of that normalised sequence. Finite-sample integrability is not contradicted.

### Delete or replace

- Delete “None of this affects the posterior” as too absolute. Replace by:
  > The evidence threshold does not obstruct bounded-posterior averaging once posterior convergence has been established.
- Delete any assertion that units 18–21 themselves identify the geometric branch object with the compact-base Gaussian model.
- Do not label the variance-2 identification formal at grammar commit `1a04563`.

---

## A.7. Appendices: complete disposition

### Appendix A — Chart proofs and resolution/transport details

Retain `app:chart_proofs`.

**Existing chart subsections, all currently unlabelled:**

1. **One variable** — retain, lightly edit.
2. **Fubini along a resonant coordinate** — retain.
3. **Dominated convergence and the generic first correction** — retain.
4. **Reading off the coefficients** — retain.
5. **The general chart expansion** — rewrite around the explicit face operators; do not suggest that a crossing Taylor expansion alone proves the result.

Add, in this order before or after those proofs:

- Taylor-subtracted chart zeta continuation.
- Polar extraction and support/jet congruence.
- B1 and coupled continuation.
- B4 Taylor-coefficient convolution.
- Closed-face integrability, extremal certificate, and deep-fibre nullity.

Backing declarations are those listed in A.2–A.4 and the coverage table below.

**Absorb all of old `app:resolution_facts`, Resolution facts used**, retaining its label on a subsection or subappendix:

- **The resolution theorem** — retain/condense, with domain-rectilinearisation qualifications.
- **Where the analyticity of \(K\) is used** — retain, corrected for the separate statistical analyticity assumptions.
- **Change of variables** — retain.
- **Tubular neighbourhoods and boundary walls** — rewrite; remove reliance on unused tubes.
- **The partition of unity** — retain.
- **Comparability** — retain.

Absorb the detailed complexification discussion and **Irreducible components as primes** from old §3 here.

### Appendix B — Finite-part computations

New label: `app:finite_parts`.

Move here:

- Full **One resonant coordinate** computation from `sec:tiers`.
- Full nonconstant **Ties** computation from `sec:tiers`.
- The finite-part portion of `sec:first_orders`.
- From `sec:residue`:
  - **Through the asymptotics**, including the truncated negative-moment formula;
  - **As an iterated density residue**;
  - the density-calculus interpretation of `thm:identity`.
- The mixed-ratio bare-moment product `eq:zeta_leading` and its calculation.

Add the explicit tensor-product Taylor-subtracted FP definition and its relation to the chart face sum.

**Status:** analytic evaluations unless and until exact Lean names for these identifications are supplied. The formal face-sum coefficient theorem is not itself a named closed-FP evaluation.

### Appendix C — Expansion algebra

Retain `app:expansion_algebra`.

Keep all four existing paragraphs:

- **Blocks**
- **Multiplication**
- **Division**
- **The logarithm with a source**

Move the detailed connected-coefficient recursion from old §11 here. Add `polarAmplitudeCoeff_eq`, `polarAmplitudeCoeff_ofReal`, and `polarAmplitudeSum_sub_polarPart` as the sign/factorial algebra behind (*).

Correct “form an algebra with bounded logarithmic degree” to allow the degree bound to increase under multiplication.

### Appendix D — Special functions

Retain `app:fluctuation_facts` on the renamed appendix.

Keep all six current paragraphs:

- **Ladder and recurrence**
- **Weber’s equation**
- **The Weyl algebra**
- **Index derivatives**
- **The incomplete function**
- **Gaussian average**

Move here the corresponding extended discussion and proof from old §8. Avoid duplicating proofs already present. The Gaussian average may be a short cross-reference to §6, with its proof retained here.

### Appendix E — Gaussian Gibbs identities

New label: `app:gaussian_gibbs`.

Move:

- Old §12 **Three exact identities**, all three items.
- The following inverse-evidence and quenched-source paragraphs.
- Wick-series/exponential-jet-moment discussion from old §10.
- Replica definitions from old §12, expanded only as needed.

Retain their existing formal pins, after checking them at the new grammar revision. Keep bridge pins separate.

### Appendix F — Formalisation coverage

Retain `sec:formalisation` and `tab:lean`.

Move old §13 here, **rewrite throughout**:

- pin grammar to `1a04563`;
- state 915 modules and no `sorry` or additional axioms, while retaining the ordinary Lean foundational axioms;
- replace the single oversized table by several tables grouped by topic;
- remove “the reader should take the table as the precise version”: hypotheses must already appear in the main statements;
- retain a concise formal scope paragraph and an explicit non-claims list.

### Old Appendix E — Moment tensors and tubular neighbourhoods

**Remove from the compiled paper; archive in the repository.**

This accounts for all three existing subsections:

1. **Normal derivatives as global sections**, including `lem:normal_deriv` and `eq:normal_differential`;
2. **Tubular neighbourhoods and integration along fibres**, including `eq:pushforward`;
3. **Moment tensors**, including `def:moment_tensor`, `eq:moment_tensor`, `eq:dressed_moment`, the commented-out proposition, and **What the moment tensors know**.

Reason: **superseded as an organising language and unused in every proof**. The canonical conormal splitting and associated-graded statement survive in §§2–3. Keeping this appendix would recreate the competing architecture the reorganisation is intended to remove.

Remove all references to `app:moment_tensors` from the compiled paper.

### Figures

- `resolution_schematic`, `stratification`: §2, retaining only what fits the compressed exposition.
- `planes`, `mixed`: §3 examples.
- `depth`: §3 admissibility subsection.
- `x2y2`: §1 if compatible with the positive-square calculation; otherwise §3.
- `wall_crossing`: §3 or §5, not both.

---

# B. The statements to print

The following statements use the existing theorem environments and macros. New notation is defined locally rather than requiring new macros.

## B.1. Meromorphic distributions and polar coefficients

### Distribution notation and its status

Print the definition, followed by the chart theorem. In the surrounding prose say:

> We use “meromorphic distribution” in the usual weak sense, with the standard continuity in the test-function topology supplied by the finite Taylor-subtraction construction. The formal results cited here establish the scalar chart continuations, their polar coefficients, and their support and jet congruences. They do not yet package these maps as continuous distribution-valued maps in Lean.

```latex
\begin{defn}[The zeta distribution and its resolved presentation]
\label{def:zeta_distribution}
For a smooth test function $f$ downstairs, define on the initial
convergence half-plane
\[
 \langle T(s),f\rangle
   =\int_W f(w)K(w)^{-s}\varphi(w)\,dw .
\]
Its resolved presentation is the weak meromorphic family
\[
 \widetilde T(s)=(K\circ\pi)^{-s}\pi^*(\varphi\,dw),
 \qquad
 \langle\widetilde T(s),F\rangle
   =\int_U F(K\circ\pi)^{-s}\pi^*(\varphi\,dw).
\]
Thus $\pi_*\widetilde T(s)=T(s)$, meaning that
$\langle T(s),f\rangle=\langle\widetilde T(s),f\circ\pi\rangle$.
Neither $T$ nor $\widetilde T$ includes a Gamma factor.

For a positive candidate exponent $\mu$, write
\[
 \widetilde T(s)
   =\sum_{r=1}^{M_\mu}\frac{A_{\mu,r}}{(\mu-s)^r}
       +H_\mu(s),
\]
where $H_\mu$ is holomorphic near $\mu$ and $M_\mu$ is a
candidate order bound. The actual pole order of a pairing may be
smaller, and all its polar coefficients may vanish.
\end{defn}
```

Here the initial half-plane is \(\Re s<\lambda\) under the stated leading integrability assumptions. For a finite resolved cover, take \(M_\mu\) to be the maximum local resonance count, not the number of all resonant components in the entire resolution.

### Exact chart formula

The notation preceding the theorem should be:

- \(h_i\in\N\), \(k_i\ge1\), \(G\) smooth on a neighbourhood of \([0,1]^d\);
- positive Taylor depths \(p_i\);
- \(P_i^{p_i}\) is Taylor truncation in coordinate \(i\), retaining orders \(0,\ldots,p_i-1\);
- \(R_i^{p_i}=1-P_i^{p_i}\);
- for a face \(J\) and \(0\le a_i<p_i\), \(i\in J\),
  \[
  G_{J,a}^{p}(w)
  =\left.\partial_J^a\Big(\prod_{i\notin J}R_i^{p_i}G\Big)
    \right|_{u_J=0}.
  \]
  This is the paper notation for `faceAmp`.
- \(w_{J,a}=\prod_{i\in J}(a_i!)^{-1}\).

```latex
% Lean @ 1a04563: Grammar/ChartZetaFace.lean:
% Grammar.chartZeta_eq_sum_faces
% Lean @ 1a04563: Grammar/ChartZetaRegularization.lean:
% Grammar.chartZetaAtDepth_eq_chartZeta,
% Grammar.differentiableOn_chartZetaAtDepth,
% Grammar.chartZetaAtDepth_eq_of_depths
% Lean @ 1a04563: Grammar/ChartZetaPolar.lean:
% Grammar.chartPolarCoeff,
% Grammar.chartZetaAtDepth_sub_polarPart_isBigO_one
\begin{thm}[Chart continuation and polar coefficients]
\label{thm:chart_polar}
Let $G$ be smooth on a neighbourhood of $[0,1]^d$,
$h_i\in\N$ and $k_i\ge1$. On the initial strip
$2k_i\operatorname{Re}s<h_i+1$ for every $i$, put
\[
 T_{h,k}(s)[G]
   =\int_{(0,1]^d}G(u)\prod_i u_i^{h_i-2k_i s}\,du .
\]
For positive integers $p_i$, its Taylor-subtracted presentation is
\[
 T^p_{h,k}(s)[G]
  =\sum_{J,a} w_{J,a}
      \prod_{i\in J}(a_i+h_i+1-2k_i s)^{-1}
      T_{h_{J^c},k_{J^c}}(s)[G^p_{J,a}],
\]
where the sum runs over all faces $J$ and the Taylor orders
$0\le a_i<p_i$, $i\in J$.
It agrees with $T_{h,k}(s)[G]$ on the initial strip and is
holomorphic on
\[
 2k_i\operatorname{Re}s<p_i+h_i+1\quad\hbox{for every }i
\]
away from its candidate poles. Positive depths give compatible
continuations on their common domains.

Fix $\mu>0$ with $2k_i\mu<p_i+h_i+1$ for every $i$. Set
\[
 I_\mu=\{i:2k_i\mu-h_i-1\in\N\},\qquad M_\mu=|I_\mu|.
\]
For a face term $x=(J,a)$ define
\[
 R_x=\{i\in J:a_i+h_i+1=2k_i\mu\},\qquad c_x=|R_x|,
 \qquad b_x=\prod_{i\in R_x}(2k_i)^{-1},
\]
and the holomorphic factor
\[
 H_x(s)=
 \prod_{i\in J\setminus R_x}(a_i+h_i+1-2k_i s)^{-1}
 T_{h_{J^c},k_{J^c}}(s)[G^p_{J,a}].
\]
Then near $\mu$,
\[
 T^p_{h,k}(s)[G]
   =\sum_{r=1}^{M_\mu}\frac{A_{\mu,r}[G]}{(\mu-s)^r}
      +H_\mu[G](s),
\]
with $H_\mu[G]$ holomorphic, and
\begin{equation}\label{eq:chart_polar}
 A_{\mu,r}[G]
   =\sum_{x:\,c_x\ge r}
       w_x b_x\,\frac{(-1)^{c_x-r}}{(c_x-r)!}
       H_x^{(c_x-r)}(\mu).
\end{equation}
These coefficients do not depend on the sufficiently large depth
used to compute them. They are real for real $G$ and vanish for
$r>M_\mu$.
\end{thm}
```

The formal theorem supplies a bounded holomorphic punctured remainder; the printed holomorphic remainder is its removable-singularity formulation. Depth independence of polar data follows from depth compatibility and principal-part uniqueness.

Print the convention box immediately afterward:

```latex
\begin{equation}\label{eq:polar_conventions}
 C_{\mu,r}[G]
 :=[(s-\mu)^{-r}]T_{h,k}(s)[G]
 =(-1)^rA_{\mu,r}[G]
 =\operatorname{chartPolarCoeff}(p,G,h,k,\mu,r-1).
\end{equation}
```

The last term is mathematical documentation of the Lean name; it need not be used elsewhere in the exposition.

### Support and finite jet order

```latex
% Lean @ 1a04563: Grammar/ChartZetaPolarSupport.lean:
% Grammar.chartPolarCoeff_eq_zero_of_jetsZeroOn,
% Grammar.chartPolarCoeff_eq_zero_of_eqOn_zero,
% Grammar.chartPolarCoeff_congr,
% Grammar.ofReal_chartPolarReal
\begin{prop}[Resonant support and finite jet dependence]
\label{prop:polar_support_jets}
Under the hypotheses of \cref{thm:chart_polar}, let
\[
 \Sigma_{\mu,r}
  =\{u\in[0,1]^d:
        \#\{i\in I_\mu:u_i=0\}\ge r\}.
\]
The functional $A_{\mu,r}$ vanishes on every amplitude that
vanishes on a neighbourhood of $\Sigma_{\mu,r}$.
More generally, equality of the rectangular $p$-jets of two
amplitudes on $\Sigma_{\mu,r}$ implies equality of their
$A_{\mu,r}$-values; vanishing of those jets implies a zero value.
In particular the polar functional is supported on
$\Sigma_{\mu,r}$ and depends on only finitely many jets there.
The depth $p$ gives a sufficient finite-order bound, not an
assertion of the optimal transverse order.
\end{prop}
```

Define “rectangular \(p\)-jets” using the exact `EqJetsOn` convention when transcribing that file. The supplied summary does not show its derivative-index definition; do not silently replace it by the intrinsic ideal-power condition of old `thm:jet`.

---

## B.2. B1 and B4

### B1

```latex
% Lean @ 1a04563: Grammar/EmpiricalChartMellin.lean:
% Grammar.mellin_empIntegral_eq_coupledChartZeta,
% Grammar.integrable_mellinEmpIntegrand
\begin{prop}[Mellin transform as a coupling average]
\label{prop:empirical_mellin}
Let $\eta,\zeta$ be smooth on a neighbourhood of $[0,1]^d$,
and let $h_i,k_i\in\N$. Define
\[
 Z_N(\eta;\zeta)
   =\int_{(0,1]^d}\eta(u)u^h
       e^{-Nu^{2k}+\sqrt N\,u^k\zeta(u)}\,du .
\]
For
\[
 0<\operatorname{Re}s,\qquad
 2k_i\operatorname{Re}s<h_i+1\quad\hbox{for every }i,
\]
the Mellin integral is absolutely convergent and
\begin{align}
 \int_0^\infty N^{s-1}Z_N(\eta;\zeta)\,dN
 &=\int_0^\infty t^{s-1}e^{-t}
       T_{h,k}(s)[\eta e^{\sqrt t\,\zeta}]\,dt
       \label{eq:coupled_mellin}\\
 &=T_{h,k}(s)[\eta S_s(\zeta)],
 \qquad
 S_s(a)=\int_0^\infty t^{s-1}e^{-t+a\sqrt t}\,dt .
 \label{eq:fluctuation_zeta}
\end{align}
At zero field this becomes
$\Gamma(s)T_{h,k}(s)[\eta]$.
\end{prop}
```

**Hypothesis audit.** The attached B1 declaration assumes global smooth functions; smoothness on a neighbourhood of the closed box is the usual equivalent local presentation after extension. It does not require separate supplied bounds \(C,M\): boundedness on the closed box is derived. It also does not require \(k_i>0\); using that stronger standing assumption in the paper is harmless.

### Flat growth statement used by the coupled analysis

Include this short lemma or explicit hypothesis paragraph, rather than hiding it in coverage:

```latex
\begin{lem}[The positive flat strip]
\label{lem:coupled_flat_strip}
Suppose $H(\tau,u)$ is jointly continuous and, for $\tau\ge0$,
\[
 |H(\tau,u)|
   \le C(1+\tau)^R e^{M\tau}\prod_i u_i^{p_i},
 \qquad C\ge0.
\]
Then its coupled chart zeta integral is absolutely convergent
and holomorphic where
\[
 0<\operatorname{Re}s,\qquad
 2k_i\operatorname{Re}s<p_i+h_i+1\quad\hbox{for every }i.
\]
Its index derivatives are the corresponding product integrals
with powers of
$\log t-2\sum_i k_i\log u_i$.
For $H(\tau,u)=\eta(u)e^{\tau\zeta(u)}$, boundedness of
$\eta,\zeta$ gives this bound with $p=0$.
The Taylor-subtracted face amplitudes satisfy the analogous
positive-depth bounds with polynomial growth in $\tau$.
\end{lem}
```

Backing:
`integrable_coupIntegrand`,
`iteratedDeriv_coupledChartZeta`,
`differentiableOn_coupledChartZeta`,
`flatOn_fieldFam`,
`flatOn_faceAmp_fieldFam`.

### B4

Define the cutoff convention before the theorem: \(Q=Q_{\rm amb}(k)\), \(L\in\N\), \(L\ge L_0(h)\), and \(p=\operatorname{depthOf}(h,k,L)\). The paper may use the existing common multiple \(Q=2\prod_i k_i\), but the formal correspondence should identify it with the library’s `Qamb`.

```latex
% Lean @ 1a04563: Grammar/EmpiricalCouplingAllLog.lean:
% Grammar.empIntegratedPolarCoeff_eq_couplingPolarCoeff,
% Grammar.ofReal_empCoeff_eq_couplingPolarCoeff,
% Grammar.couplingPolarCoeff_eq_polarCoeff
\begin{thm}[Empirical coefficients as coupling-averaged polar data]
\label{thm:coupling_all_log}
Let $\eta,\zeta$ be smooth on a neighbourhood of $[0,1]^d$,
$h_i\in\N$ and $k_i\ge1$. Choose an integer cutoff
$L\ge L_0(h)$ and the canonical Taylor depth
$p=\operatorname{depthOf}(h,k,L)$.
Let
\[
 \mu\in Q^{-1}\N,\qquad 0<\mu<L,\qquad 0\le q\le d-1,
 \qquad Q=Q_{\rm amb}(k).
\]
Writing $C_{\mu,r}=(-1)^rA_{\mu,r}$ as in
\eqref{eq:polar_conventions}, the coefficient of
$N^{-\mu}(\log N)^q$ in the frozen expansion is
\begin{equation}\label{eq:coupling_all_log}
 c_{\mu,q}(\eta;\zeta)
 =\frac{(-1)^{q+1}}{q!}
   \sum_{r=q+1}^{d}\frac1{(r-q-1)!}
   \int_0^\infty
       t^{\mu-1}(\log t)^{r-q-1}e^{-t}
       C_{\mu,r}[\eta e^{\sqrt t\,\zeta}]\,dt .
\end{equation}
All displayed integrals are absolutely convergent.
Terms with $r>M_\mu$ vanish.
\end{thm}
```

The exact library normalisation, worth printing in a remark, is

\[
\boxed{
\operatorname{empCoeff}
=\frac{(-1)^{q+1}}{q!}\operatorname{couplingPolarCoeff},
\qquad
\operatorname{couplingPolarCoeff}
=(-1)^{q+1}q!\operatorname{empCoeff}.
}
\]

For the intermediate equality
`empIntegratedPolarCoeff_eq_couplingPolarCoeff`, the hypotheses are more general: any positive depth, \(0<\mu\), \(\mu\) in its flat strip, and any \(q\). The **identification with `empCoeff`** is the theorem requiring the canonical cutoff, lattice membership, \(0<\mu<L\), and \(q\le d-1\). Keep these two levels distinct.

---

## B.3. How to print (*)

**Recommendation: print a corollary under an explicit interchange hypothesis.** This is more precise than a theorem whose proof is merely labelled “derivation,” because the missing analytic step is visible in the statement.

Define
\[
m_{\mu,\ell}(a)
=\int_0^\infty t^{\mu-1}(\log t)^\ell e^{-t+a\sqrt t}\,dt
=\left.\partial_s^\ell S_s(a)\right|_{s=\mu}.
\]

```latex
% Lean @ 1a04563: B4 is formalised in
% Grammar/EmpiricalCouplingAllLog.lean.
% The log-weighted jet interchange below (B15--B16) is not formalised.
% The sign/factorial algebra is formalised in
% Grammar/PolarAmplitudeAlgebra.lean.
\begin{cor}[Amplitude form of the all-log formula]
\label{cor:polar_amplitude}
Assume the hypotheses of \cref{thm:coupling_all_log}.
Assume also the log-weighted polar interchange: for every
$r=q+1,\ldots,M_\mu$, with $\ell=r-q-1$,
\begin{equation}\label{eq:polar_interchange}
 A_{\mu,r}[\eta\,m_{\mu,\ell}(\zeta)]
  =\int_0^\infty t^{\mu-1}(\log t)^\ell e^{-t}
       A_{\mu,r}[\eta e^{\sqrt t\,\zeta}]\,dt .
\end{equation}
Then
\begin{equation}\label{eq:structural_all_log}
 c_{\mu,q}(\eta;\zeta)
 =\frac1{q!}
   \sum_{r=q+1}^{M_\mu}
     \frac{(-1)^{r-q-1}}{(r-q-1)!}
     A_{\mu,r}\!
       \left[\eta\,
       \left.\partial_s^{\,r-q-1}S_s(\zeta)\right|_{s=\mu}
       \right].
\end{equation}
In particular, at the top candidate logarithmic degree,
\[
 c_{\mu,M_\mu-1}(\eta;\zeta)
   =\frac{A_{\mu,M_\mu}[\eta S_\mu(\zeta)]}
          {(M_\mu-1)!}.
\]
\end{cor}
```

Follow with:

> **Derivation and formal status.** The corollary follows from B4 and the stated interchange. The latter is justified analytically by passing the log-weighted coupling integral through the finitely many amplitude jets and Taylor-subtracted face integrals defining the polar functional. This is the B15–B16 interchange layer and is not among the formal results cited here. The finite-sum sign and factorial algebra is formalised in `PolarAmplitudeAlgebra.lean`.

The existing formal top graded formula remains an **independent unconditional theorem under its own admissibility hypotheses**. Do not make that established result appear dependent on this new interchange assumption.

The zero-field specialisation can be printed separately without invoking the general amplitude interchange:

```latex
\begin{cor}[Population coefficients]
\label{cor:population_polar}
Under the corresponding population hypotheses,
\[
 c^{\mathrm{pop}}_{\mu,q}(\eta)
 =\frac1{q!}\sum_{r=q+1}^{M_\mu}
   \frac{(-1)^{r-q-1}}{(r-q-1)!}
   \Gamma^{(r-q-1)}(\mu)\,A_{\mu,r}[\eta].
\]
\end{cor}
```

This is the zero-field evaluation of B4: the polar coefficient inside each integral is constant in the coupling variable.

---

## B.4. The global leading measure

### Fix the set and measure conventions first

Use the following main-text convention:

- \(Z_0\) is the **support-truncated resolved zero fibre** used by the resolved data.
- \(D_{m+1}\) denotes geometric depth at least \(m+1\).
- The formal deep set is
  \[
  D_{m+1}\cap Z_0.
  \]
- Set
  \[
  X_m=U\setminus(D_{m+1}\cap Z_0).
  \]

This matches the attached code’s `stratumOpen = compl deepZeroFibre`. Its comments sometimes abbreviate this as \(U\setminus D_{m+1}\); do not reproduce that abbreviation without defining \(D_{m+1}\) to be support-truncated.

For each transport piece \(p\) and simple face \(J\), denote by \(\rho_{p,J}^\lambda\) the raw face measure on its parameter space and by \(b_{p,J}\) its map to \(U\). Its density is the existing `faceDensity`, including transport density, reference measure, and the factors \((2k_j)^{-1}\).

```latex
\begin{defn}[Raw, population and tilted leading measures]
\label{def:global_leading_measures}
For a resolved core transport $Y$, define
\[
 \rho^\lambda_m
   =\sum_p\sum_{J\in\mathcal F_p(\lambda,m)}
       (b_{p,J})_*\rho^\lambda_{p,J},
\]
where $\mathcal F_p(\lambda,m)$ is the set of simple
$\lambda$-resonant faces of size $m$ in piece $p$.
This is the raw leading residue measure.

For $\lambda>0$ set
\[
 \nu^\lambda_m
   =\frac{\Gamma(\lambda)}{(m-1)!}\rho^\lambda_m .
\]
Thus $\nu^\lambda_m$ has the population coefficient normalisation.

For a root field $\xi$, let $\xi_{p,J}$ be its branch trace on
the face parameter space and define
\[
 \widehat\nu^\lambda_m(\xi)
   =\frac1{(m-1)!}
      \sum_p\sum_{J\in\mathcal F_p(\lambda,m)}
       (b_{p,J})_*
       \big(S_\lambda(\xi_{p,J})\,\rho^\lambda_{p,J}\big).
\]
In particular $\widehat\nu^\lambda_m(0)=\nu^\lambda_m$.
\end{defn}
```

Backed by:
`leadingResidueMeasureU`,
`empiricalLeadingMeasureU`,
`empiricalLeadingMeasureU_zero`,
`integral_empiricalLeadingMeasureU`.

The library’s `empFaceMeasureU` already includes
\[
\operatorname{fluctDensity}(\lambda,a)
=\frac{S_\lambda(a)}{\Gamma(\lambda)}.
\]
This explains why its assembly multiplies by \(\Gamma(\lambda)/(m-1)!\), whereas the raw-face display above multiplies by \(1/(m-1)!\).

### Chart-leading theorem

State `ChartLeading` explicitly: every piece has all wall ratios at least \(\lambda\), and at most \(m\) walls whose ratio equals \(\lambda\). Attainment is not required.

```latex
% Lean @ 1a04563: Grammar/ResolvedLeadingMeasure.lean:
% Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_empZ_eq_integral_leadingU,
% Grammar.SmoothEngine.ResolvedData.hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU,
% Grammar.SmoothEngine.ResolvedData.isFiniteMeasure_empiricalLeadingMeasureU,
% Grammar.SmoothEngine.ResolvedData.isFiniteMeasure_leadingResidueMeasureU
\begin{thm}[Global leading measures and every smooth observable]
\label{thm:global_leading}
Let $\lambda>0$, $m\ge1$, and suppose the transport is
chart-leading at $(\lambda,m)$.
Then $\rho^\lambda_m$ and
$\widehat\nu^\lambda_m(\xi)$ are finite positive measures.
For every smooth observable $F$ on $U$ and every root field
$\xi$ whose underlying measurable field is bounded,
\[
 N^\lambda(\log N)^{-(m-1)}Z_N[F;\xi]
   \longrightarrow
   \int_U F\,d\widehat\nu^\lambda_m(\xi).
\]
At zero field,
\[
 N^\lambda(\log N)^{-(m-1)}\Zcal_N[F]
   \longrightarrow
   \frac{\Gamma(\lambda)}{(m-1)!}
       \int_U F\,d\rho^\lambda_m
   =\int_U F\,d\nu^\lambda_m.
\]
No admissibility or test-support condition is imposed on $F$.
The limits are allowed to be zero.
\end{thm}
```

Do not write \(\sim cN^{-\lambda}(\log N)^{m-1}\) in this theorem unless \(c\ne0\) is added.

### Deep-fibre nullity

```latex
% Lean @ 1a04563: Grammar/SmoothGlobalLeadingMeasure.lean:
% Grammar.SmoothEngine.ResolvedData.leadingResidueMeasureU_deepZeroFibre,
% Grammar.SmoothEngine.ResolvedData.leadingResidueMeasureU_restrict_stratumOpen
\begin{prop}[Deep-fibre nullity]
\label{prop:leading_deep_null}
For every real $\lambda$ and every $m\in\N$,
\[
 \rho^\lambda_m(D_{m+1}\cap Z_0)=0,
 \qquad
 \rho^\lambda_m|_{X_m}=\rho^\lambda_m .
\]
This assertion does not require extremality or the
chart-leading hypothesis. It is a nullity assertion, not a
general finiteness assertion.
\end{prop}
```

The closed support may meet the deep set. Nullity does not imply disjoint closed support.

### Certificate

```latex
% Lean @ 1a04563: Grammar/ResolvedExtremalLocalisation.lean:
% Grammar.SmoothEngine.ResolvedData.ExtremalCertificate,
% Grammar.SmoothEngine.ResolvedData.extremalCertificate_of_divPt_zero,
% Grammar.SmoothEngine.ResolvedData.chartLeading_of_extremalData
\begin{defn}[Extremal certificate for a transport]
\label{def:extremal_certificate}
A resolved core transport $Y$ has an extremal certificate if,
for every piece $p$, there is a point $P\in Z_0$ such that
the multiset of wall data $(k_i,h_i)$ of $p$ is a submultiset
of the intrinsic wall data through $P$.
\end{defn}

\begin{prop}[From intrinsic extremality to chart-leading data]
\label{prop:extremal_certificate}
Suppose $(\lambda,m)$ satisfies the intrinsic extremal-data
bounds on $Z_0$ and $Y$ has an extremal certificate.
Then $Y$ is chart-leading at $(\lambda,m)$.

A sufficient condition for the certificate is that every piece
has a box origin in $Z_0$: for every piece $p$ there exists a
base parameter $s$ for which the resolved point represented by
$(s,0)$ belongs to $Z_0$.
\end{prop}
```

This is a **hypothesis on the chosen transport**, not a new consequence of resolution existence. The sufficient condition is existential in the base parameter, exactly as in the attached declaration.

### Global identification and coefficient functional

Use \(\nu_{\mathrm{str},m}^{\lambda}\) temporarily for the old measure on \(X_m\), and then state that its pushforward is the globally defined population measure. This avoids defining the same notation twice by different constructions.

```latex
% Lean @ 1a04563: Grammar/SmoothGlobalLeadingMeasure.lean:
% Grammar.SmoothEngine.ResolvedData.globalExtremalStratumMeasure_eq,
% Grammar.SmoothEngine.ResolvedData.coeff_withF_eq_integral_globalExtremalStratumMeasure,
% Grammar.SmoothEngine.ResolvedData.extremalStratumMeasure_univ,
% Grammar.SmoothEngine.ResolvedData.isFiniteMeasure_extremalStratumMeasure
\begin{thm}[Global identification with the extremal stratum measure]
\label{thm:global_stratum_identification}
Let $\lambda_*>0$, $m_*\ge1$, suppose
$(\lambda_*,m_*)$ satisfies the intrinsic extremal-data bounds,
and assume an extremal certificate for $Y$.
Let $\nu_{\mathrm{str},m_*}^{\lambda_*}$ be the stratum measure
on $X_{m_*}$ characterised by its smooth test integrals, and
let $\iota:X_{m_*}\hookrightarrow U$.
Then
\[
 \iota_*\nu_{\mathrm{str},m_*}^{\lambda_*}
   =\nu_{m_*}^{\lambda_*}
   =\frac{\Gamma(\lambda_*)}{(m_*-1)!}
       \rho_{m_*}^{\lambda_*}
 \quad\hbox{on all of }U.
\]
For every smooth $F$ on $U$,
\[
 c_{\lambda_*,m_*-1}(F)
   =\int_U F\,d\nu_{m_*}^{\lambda_*}.
\]
In particular,
\[
 \nu_{\mathrm{str},m_*}^{\lambda_*}(X_{m_*})
   =\nu_{m_*}^{\lambda_*}(U)
   =c_{\lambda_*,m_*-1}(1)
   =\frac{\Gamma(\lambda_*)}{(m_*-1)!}
        \rho_{m_*}^{\lambda_*}(U)<\infty.
\]
\end{thm}
```

```latex
% Lean @ 1a04563: Grammar/ResolvedExtremalLocalisation.lean:
% Grammar.SmoothEngine.ResolvedData.tendsto_normalised_partitionObs_extremal_all,
% Grammar.SmoothEngine.ResolvedData.partitionObs_isEquivalent_extremal_all
\begin{cor}[Leading asymptotic downstairs]
\label{thm:leading}
Under the hypotheses of
\cref{thm:global_stratum_identification}, every smooth
observable $f$ downstairs satisfies
\[
 N^{\lambda_*}(\log N)^{-(m_*-1)}\Zcal_N[f]
   \longrightarrow
   \int_U(f\circ\pi)\,d\nu_{m_*}^{\lambda_*}.
\]
If this integral is nonzero, then
\[
 \Zcal_N[f]\sim
 \left(\int_U(f\circ\pi)\,d\nu_{m_*}^{\lambda_*}\right)
 N^{-\lambda_*}(\log N)^{m_*-1}.
\]
\end{cor}
```

### Relation to \(A_{\lambda,m}\)

Print the conceptual identification
\[
A_{\lambda,m}[F]=\int_U F\,d\rho^\lambda_m
\]
at the leading pair, but label its formal provenance carefully:

- The supplied files formally identify the **asymptotic coefficient functional** with the raw measure times \(\Gamma(\lambda)/(m-1)!\).
- The chart polar theory and zero-field B4 identify the same leading coefficient with \(\Gamma(\lambda)A_{\lambda,m}[F]/(m-1)!\).
- Their comparison gives the displayed weak identification after chart assembly.

There is no supplied standalone declaration named “resolved polar distribution equals leading measure.” Do not cite `globalExtremalStratumMeasure_eq` as though it directly contains that statement.

---

## B.5. The \(x^2y^2\) calculation for new §1

This is the complete display to use.

```latex
% Lean @ 1a04563: Grammar/PolarTwoDimExamples.lean:
% Grammar.chartPolarCoeff_const_xy_sq,
% Grammar.empCoeff_xy_sq_one,
% Grammar.empCoeff_xy_sq_zero,
% Grammar.tendsto_logExample_empCoeff
% Lean: Grammar/LogExampleTwoDim.lean:
% Grammar.SmoothEngine.tendsto_logExample
\begin{prop}[A crossing, including the constant log term]
\label{prop:xy_sq_polar_example}
For $a\in\R$, let
\[
 Z_N(a)=\int_0^1\!\!\int_0^1
       e^{-Nx^2y^2+a\sqrt N\,xy}\,dx\,dy.
\]
The population chart zeta function of the constant amplitude is
\[
 T(s)[1]=\frac1{(1-2s)^2}
        =\frac{1/4}{(\frac12-s)^2}.
\]
Thus $M_{1/2}=2$, $A_{1/2,2}[1]=1/4$, and
$A_{1/2,1}[1]=0$.
The empirical coefficients are
\[
 c_{1/2,1}(1;a)=\frac14S_{1/2}(a),\qquad
 c_{1/2,0}(1;a)
   =-\frac14\left.\partial_\nu S_\nu(a)\right|_{\nu=1/2}.
\]
Consequently,
\begin{equation}\label{eq:xy_sq_complete}
 Z_N(a)=\frac{N^{-1/2}}4
 \left[
   S_{1/2}(a)\log N
   -\left.\partial_\nu S_\nu(a)\right|_{\nu=1/2}
 \right]+o(N^{-1/2}).
\end{equation}
At zero field,
\[
 Z_N(0)=\frac{N^{-1/2}}4
       \left[\sqrt\pi\log N-\Gamma'(1/2)\right]
       +o(N^{-1/2}).
\]
\end{prop}
```

Immediately after it, give the direct one-line radial calculation:

\[
Z_N(a)=\frac1{4\sqrt N}\int_0^N
 t^{-1/2}e^{-t+a\sqrt t}(\log N-\log t)\,dt.
\]

Then explain the point:

> The double pole fixes the logarithm, but its constant companion is not another residue measure: it also sees the derivative of the radial kernel in its index.

Do not include the digamma special value as formal. Do not say the regression file proves the functional identity between `empIntegral` and `logExample`; it proves agreement of coefficients with the separately established direct asymptotic.

---

# C. Claims in the current draft that must change

## C.1. Claims now formally established, or with a new formal route

| Current location/claim | Required change |
|---|---|
| §13 non-claims: no chart-level Mellin identity | Delete. B1 is `mellin_empIntegral_eq_coupledChartZeta`, with no statistical input. |
| `sec:tiers`: chart meromorphic continuation used informally | Cite `chartZetaAtDepth_eq_chartZeta`, `differentiableOn_chartZetaAtDepth`, `chartZetaAtDepth_eq_of_depths`. |
| `sec:tiers`: coefficients described only through abstract Mellin uniqueness | Add the explicit population chart polar theorem, `chartPolarCoeff` and `chartZetaAtDepth_sub_polarPart_isBigO_one`. |
| `sec:conormal`: support/finite chart jet dependence discussed through asymptotic coefficients | Add the direct polar-functional support and congruence theorems. Do not replace the distinct intrinsic ideal-power theorem. |
| `sec:empirical`, analytic coefficient paragraph | B4 is now a named formal theorem, not merely a derivation from a formal Mellin characterisation. |
| Constant-field \(x^2y^2\) coefficient identification | Upgrade to explicit `empCoeff_xy_sq_one`, `empCoeff_xy_sq_zero`, in addition to the already formal direct limit. |
| `sec:leading`: extension of the leading residue across nonminimal walls | Upgrade to finite global measure theorem. |
| Same paragraph: “gives \(D_{m+1}\) measure zero” | Upgrade to `leadingResidueMeasureU_deepZeroFibre`, with the exact support-truncated deep set. |
| Same paragraph: equality with the extended stratum measure | Upgrade to `globalExtremalStratumMeasure_eq`, under certificate. |
| General-prior leading examples | They are now applications of the formal global measure framework; the exact displayed coordinate simplifications are still paper computations unless separately named. |
| Mixed-ratio leading integrability | Backed by `integrableOn_residueWeight_compl` and the closed-face leading theorem; the elementary evaluation of the complementary integral may remain a displayed calculation. |

## C.2. Restrictions superseded by stronger formal statements

1. **Old `thm:leading`:** remove \(f\circ\pi\in\Ical_{m+1}\). Replace with the certificate hypothesis and all-observable conclusion.
2. **Old mass statement:** replace
   \[
   \nu(X)\le c_{\lambda,m-1}(1),
   \quad\text{equality if }D_{m+1}=\varnothing
   \]
   by equality under the certificate, with no deep-empty assumption.
3. **`eq:empirical_leading`:** remove admissibility at depth \(m\) for the global leading formula.
4. **Old §11 leading posterior:** remove \(D_{m+1}=\varnothing\). Use the global tilted measure.
5. **Old §11 branch agreement:** remove it from the general theorem; retain it only for simplifying the branchwise measure to multiplication by a single field on \(U\).
6. **§13 empirical-leading row:** replace the `IsTest`-restricted measure identification by `hasLeadingTerm_empZ_eq_integral_leadingU`.
7. **Old “extended measure is understood” clauses:** delete throughout; the measure is now defined explicitly.

These upgrades **do not** remove admissibility from:

- general depth-graded formulas;
- the intrinsic ideal-power statement at a nonleading pair;
- general zero-order stratum measures;
- the existing coefficient-continuity and jet-law theorems.

## C.3. Wrong or misleading claims/conventions

### 1. Gamma-free versus Gamma-weighted objects

Current `eq:zeta_global` defines the Mellin transform, not the Gamma-free zeta distribution. Replace the notation by
\[
\mathcal M\Zcal_F(s)=\Gamma(s)\langle\widetilde T(s),F\rangle.
\]

A lower-log coefficient is generally a sum involving several \(A_{\mu,r}\) and Gamma derivatives. It is not simply one Laurent coefficient of the Gamma-free distribution.

### 2. Signs

Keep `eq:laurent`; its sign is correct:
\[
c_{\mu,q}=\frac{(-1)^{q+1}}{q!}
[(s-\mu)^{-(q+1)}]\mathcal MZ(s).
\]

But introduce the explicit bridge:
\[
C_{\mu,r}=(-1)^rA_{\mu,r}.
\]

The simple-pole FP formula for \(A_{\mu,1}\) has **no leading minus sign**. A sign only appears if it is rewritten as a standard-Laurent coefficient or as a derivative-of-delta pairing.

### 3. Raw/population normalisation

The old definition
\[
\Rres^\mu_c=\frac{(c-1)!}{\Gamma(\mu)}\nu^\mu_c
\]
is correct.

The direction must remain:
\[
\nu=\frac{\Gamma(\mu)}{(c-1)!}\Rres,
\qquad
\Rres=\frac{(c-1)!}{\Gamma(\mu)}\nu.
\]

At the global leading pair, \(\rho\) is raw. Never use \((m-1)!/\Gamma(\lambda)\) as the factor multiplying \(\rho\) to obtain the population measure.

### 4. “Every coefficient is represented over one stratum”

False without qualification. Lower polar orders can involve finite parts along larger resonant loci and contributions from deeper intersections. Use the polar distributions globally; single exact-stratum integrals are associated-graded/restricted evaluations.

### 5. “When \(c\) walls resonate, the pole has order \(c\)”

Replace “has” by “has order at most \(c\)” unless nonvanishing has been established. Candidate order is not actual pairing order.

### 6. Intrinsic versus transport leading data

`IsExtremalData` alone does not imply `ChartLeading` for an arbitrary transport. Add `ExtremalCertificate`.

The code does not prove existence of a certified adapted transport. Do not state that the certificate is automatic.

### 7. The exact deep set

The attached implementation uses the complement of `deepZeroFibre`, not the complement of every geometric deep point in the ambient manifold. Fix this in the main notation and in every measure-restriction formula.

### 8. Nullity versus support

The measure gives the deep set zero mass, but its closed support may meet that set. The mixed-exponent origin is the simplest example.

The new equality of total masses is stronger than the old mass bound; the old phrase “as the bound … records” should disappear.

### 9. Root-field values on the divisor

A measurable field \(\xi.\psi\) can be assigned values on walls unrelated to its branch traces. The coefficients see `ξ.loc` through `faceTrace`, not arbitrary on-wall values of `ξ.ψ`.

### 10. Main-text scope versus formal scope

The old §13 admits hypotheses more restrictive than the body and asks the reader to treat the table as precise. Reverse this arrangement:

- main resolved statements must say which support, prior, transport and certificate hypotheses are used;
- positive-box boundary examples must not be advertised as a formal general boundary-domain assembly;
- the stronger positivity hypotheses of `exists_rlct_asymptotic` remain separate from the new leading-measure representation.

### 11. Smoothness and analyticity

“This is the only place analyticity is used” is true only for the deterministic smooth expansion after resolution. The statistical standard-form theorem has its own analyticity/moment hypotheses.

### 12. Gaussian threshold

The divergence threshold is \(v\ge2\), including \(v=2\). Do not discuss only \(v>2\), particularly if the intended statistical application is the variance-2 case.

### 13. Frozen versus diagonal asymptotics

“Fixed sample” should mean a field frozen while \(N\to\infty\). An actual sample sequence has changing fields. Uniform estimates and probabilistic hypotheses are required to pass to \(N=n\).

### 14. Asymptotic equivalence with a zero coefficient

`HasLeadingTerm` permits a zero normalised limit. The corresponding \(\sim\) statement requires a nonzero coefficient, as the attached `partitionObs_isEquivalent_extremal_all` explicitly assumes.

### 15. Blanket formalisation/novelty claims

Rewrite the abstract, introduction, conclusion, and §13:

- the entire distribution-valued topological package is not yet formalised;
- (*) is not yet unconditional in Lean;
- general finite-part evaluations are not supplied;
- the bridge’s statistical results have a separate pin;
- classical distribution/zeta machinery should not be claimed as mathematically new merely because its formal proof is new.

## C.4. Claims that must remain marked

1. **B15–B16 log-weighted jet interchange** and hence unconditional general (*).
2. **Linearity/continuity as a formal distribution-valued map**, deferred to unit 24 in the supplied summary.
3. **General one-resonance FP evaluation for all \(\alpha\)** as a named formal identity. The formula is valid without a gap hypothesis, but that does not make its identification formally supplied.
4. **Nonconstant \(x^2y^2\) finite-part formulas**, unless additional declaration names are furnished.
5. **General empirical finite-part formula** `eq:empirical_tier2` beyond the independently formal generic/gap cases.
6. **Truncated negative-moment/sublevel formula** in `eq:defA`’s discussion.
7. **Manifold density-residue calculus** independent of the chart measure identity.
8. **Weber substitution, parabolic-cylinder form, erf normalisation, Weyl-module structure**, and the other currently marked special-function derivations.
9. **Intrinsic oriented blow-up/branch-space identification**, and identification with the compact-base Gaussian model.
10. **Existence of a certified adapted transport.**
11. **Joint convergence of normal derivatives of the empirical process.**
12. **Formal continuity and convergence in law of arbitrary lower-log coefficients.**
13. **Variance-2 statistical bridge lemma**, until its exact declaration and bridge commit are supplied.
14. **Averaged subleading corrections**, including the needed rates/Edgeworth input.
15. The explanatory \(K\)-insertion formulas in old §11 remain derivations unless separately pinned.

---

# D. Coverage table at `1a04563`

Use separate tables. The following rows cover the supplied units 1–14 and 18–21; the numbering follows the completed files in the summary, not an earlier planned allocation.

Abbreviate namespaces in the caption:

- `G = Grammar`
- `SE = Grammar.SmoothEngine`
- `RD = Grammar.SmoothEngine.ResolvedData`

Do not abbreviate them ambiguously in source comments.

## D.1. New polar and coupling rows

| Unit | Statement and hypotheses | Lean declarations |
|---|---|---|
| 1 | Polar-amplitude finite-sum algebra; arbitrary polar array, truncation degree; no analytic claim | `polarAmplitudeCoeff_eq`, `polarAmplitudeCoeff_ofReal`, `polarAmplitudeSum_sub_polarPart` |
| 2 | Chart zeta integrability and holomorphy: continuous amplitude with `FlatOn`, nonnegative bound constant, `FlatStrip`; bounded case uses depth zero | `integrableOn_chartZeta_integrand_flat`, `hasDerivAt_chartZeta_flat`, `differentiableOn_chartZeta_flat`, `hasDerivAt_chartZeta` |
| 3 | Face decomposition on the initial zeta strip; smooth amplitude; Taylor face construction | `zeta_faceTerm_integral`, `chartZeta_eq_sum_faces`, `integral_box_cpowWeight` |
| 4 | Positive-depth regularised chart zeta; holomorphic on flat strip off candidate poles; compatibility on common domains, with the formal overlap restriction \(\Re s>-1\) | `chartZetaAtDepth_eq_chartZeta`, `differentiableOn_chartZetaAtDepth`, `chartZetaAtDepth_eq_of_depths`, `finite_poleSet` |
| 5 | Polar extraction: smooth amplitude, positive depth, \(\mu\) in flat strip, \(D+1\) at least every face pole order; bounded punctured remainder | `chartPolarCoeff`, `innerFactor_eq_res`, `chartZetaAtDepth_sub_polarPart_isBigO_one`, `chartZetaAtDepth_depthOf_sub_polarPart_isBigO_one` |
| 6 | Reality and support/rectangular-jet congruence of chart polar coefficients; vanishing jets or equality of jets on the relevant resonant stratum | `ofReal_chartPolarReal`, `chartPolarCoeff_eq_zero_of_jetsZeroOn`, `chartPolarCoeff_eq_zero_of_eqOn_zero`, `chartPolarCoeff_congr` |
| 7 / B7 | Finite face polar extraction; finite family, bounded pole orders, holomorphic face factors | `finiteFaceSum_sub_polarPart_isBigO_one`, `chartPolarCoeff_eq_finiteFacePolarCoeff` |
| 8 / B8–B9 | Coupled zeta holomorphy and derivatives: jointly continuous coupling family, polynomial-exponential flat growth, positive flat strip | `integrable_coupIntegrand`, `coupledChartZeta_eq_logMoment_zero`, `iteratedDeriv_coupledChartZeta`, `differentiableOn_coupledChartZeta` |
| 9 / B10 | B1: smooth \(\eta,\zeta\), \(0<\Re s\), `ZetaStrip`; absolute Fubini; local integrability and boundedness at \(N=0^+\) | `mellin_empIntegral_eq_coupledChartZeta`, `integrable_mellinEmpIntegrand`, `locallyIntegrableOn_empIntegral`, `empIntegral_isBigO_one_zero` |
| 10 / B11 | Coupled face continuation; smooth data, positive \(k_i\), canonical depth \(L\ge L_0(h)\); equality with Mellin continuation on \(0<\Re s<L\) off lattice/candidates | `differentiableOn_empZetaAtDepth`, `empZetaAtDepth_eq_mellin`, `empZetaAtDepth_eq_mellinContinuation`, `empZetaAtDepth_eventuallyEq_mellinContinuation` |
| 11 / B12 | Integrated polar coefficients equal asymptotic polar data: lattice \(0<\mu<L\), \(q\le d-1\), smooth data, positive \(k_i\), canonical cutoff | `empZetaAtDepth_sub_polarPart_isBigO_one`, `empIntegratedPolarCoeff_eq_polarCoeff`, `ofReal_empCoeff_eq_empIntegratedPolarCoeff` |
| 12 / B13a | Log-moment derivatives and coupling split: flat amplitudes/coupling growth on the positive flat strip | `iteratedDeriv_chartZeta_flat`, `iteratedDeriv_chartZeta_eq_logMoment`, `coupledLogMoment_eq_sum`, `taylorCoeff_mul` |
| 13 / B13b | B4: integrated-to-coupling equality for positive depth and positive \(\mu\) in flat strip; `empCoeff` identification additionally requires canonical depth, lattice \(0<\mu<L\), \(q\le d-1\) | `taylorCoeff_empFaceHolo_eq`, `empIntegratedPolarCoeff_eq_couplingPolarCoeff`, `ofReal_empCoeff_eq_couplingPolarCoeff`, `couplingPolarCoeff_eq_polarCoeff` |
| 14 | Constant-amplitude/constant-field \(x^2y^2\) regression on the positive unit square; both log coefficients and consistency with direct limit | `chartPolarCoeff_const_xy_sq`, `couplingPolarCoeff_xy_sq`, `empCoeff_xy_sq_one`, `empCoeff_xy_sq_zero`, `tendsto_logExample_empCoeff` |

Add a short **non-formal packaging row or note**, not a theorem row:

> Distribution-valued continuity and general log-weighted amplitude interchange are not asserted by units 1–14. Formula (*) is printed under the explicit interchange hypothesis. General finite-part evaluations are analytic computations.

## D.2. New leading-measure rows

| Unit | Statement and hypotheses | Lean declarations |
|---|---|---|
| 18 | Closed leading-face measure; nonnegative continuous amplitude, positive box size as required, \(\lambda\le(h_i+1)/(2k_i)\); complementary weight integrable, finite measure, complementary deep corners null | `integrableOn_residueWeight_compl`, `leadingFaceMeasure_univ_lt_top`, `isFiniteMeasure_leadingFaceMeasure`, `leadingFaceMeasure_face`, `leadingFaceMeasure_deep` |
| 18 | Box leading limit against the closed-face measure; `BoxLeading`, attaining multiplicity, continuous observable and field, nonnegative amplitude | `faceFunctional_eq_integral_leadingFaceMeasure`, `tendsto_empBoxIntegral_leadingFaceMeasure` |
| 19 | Raw and tilted measures on \(U\); \(\lambda>0\), chart-leading transport; finite measures; zero field gives population normalisation | `leadingResidueMeasureU`, `empiricalLeadingMeasureU`, `empiricalLeadingMeasureU_zero`, `isFiniteMeasure_leadingResidueMeasureU`, `isFiniteMeasure_empiricalLeadingMeasureU` |
| 19 | Every-observable empirical leading measure theorem; \(\lambda>0\), \(m\ge1\), `ChartLeading`, root field and global bound on its underlying measurable field; smooth observable; no `IsTest` | `hasLeadingTerm_empZ_eq_integral_leadingU` |
| 19 | Every-observable population leading measure theorem; \(\lambda>0\), \(m\ge1\), `ChartLeading` | `hasLeadingTerm_Z_eq_integral_leadingResidueMeasureU` |
| 20 | Transport certificate; piece wall multiset embeds in intrinsic pairs at a zero-fibre point; sufficient condition: a box origin in zero fibre for each piece | `ExtremalCertificate`, `pairs_divPt_zero`, `extremalCertificate_of_divPt_zero` |
| 20 | Intrinsic extremal data plus certificate imply chart-leading data | `chartLeading_of_extremalData` |
| 20 | Extremal coefficient equals \(\Gamma(\lambda)/(m-1)!\) times raw measure integral; \(\lambda>0\), \(m\ge1\), extremal data, certificate, every smooth observable | `coeff_withF_eq_integral_leadingResidueMeasureU`, `coeff_one_eq_mass_leadingResidueMeasureU` |
| 20 | Downstairs normalised limit for every smooth \(f\); same hypotheses; asymptotic equivalence additionally requires nonzero integral | `tendsto_normalised_partitionObs_extremal_all`, `partitionObs_isEquivalent_extremal_all` |
| 21 | Deep-fibre nullity for every \((\lambda,m)\), without extremality or chart-leading assumptions | `faceMeasureU_deepZeroFibre`, `leadingResidueMeasureU_deepZeroFibre`, `leadingResidueMeasureU_restrict_stratumOpen` |
| 21 | Global stratum-measure identification; extremal data, certificate, \(\lambda>0\), \(m\ge1\); equality on all \(U\), every smooth observable, finite mass equal to the leading coefficient of \(1\) | `globalExtremalStratumMeasure_eq`, `coeff_withF_eq_integral_globalExtremalStratumMeasure`, `extremalStratumMeasure_univ`, `isFiniteMeasure_extremalStratumMeasure` |

The intermediate restriction equality and iff criterion may be listed in a technical subrow:
`extremalStratumMeasure_eq_leadingResidue`,
`globalExtremalStratumMeasure_eq_restrict`,
`globalExtremalStratumMeasure_eq_iff`.
They should no longer be presented as the endpoint.

## D.3. Existing rows to modify or remove

### Replace

- **Leading term (`thm:leading`)**: replace the test/admissibility and mass-inequality content by the unit 20–21 rows above.
- **Empirical leading term (`eq:empirical_leading`)**: replace the test-only measure identification by unit 19.
- **Two-dimensional tie**: add the `empCoeff` identities; retain `tendsto_logExample`.
- **Mellin–Laurent characterisation**: retain the abstract theorem but add the explicit chart B1/B4 rows. It is no longer the sole formal coefficient identification.
- **Support**: retain resolved asymptotic support and add direct chart polar support. These are related, not duplicates.
- **Residue**: retain the general open-stratum result; add the global extremal identification separately.

### Delete as obsolete coverage endpoints

- `extremalStratumMeasure_univ_le` and `extremalStratumMeasure_univ_eq_of_deep_empty` from the main leading-measure row. The library declarations remain; the paper no longer needs them as its coverage endpoint.
- The claim that empirical measure representation requires `IsTest`.
- The non-claim that the deterministic chart Mellin identity is missing.
- The non-claim that deep-fibre nullity or global leading extension is missing.
- Any row implying that the bridge is needed to prove the deterministic chart B1/B4 formulas.

### Retain unchanged in substance

- General graded formula and ideal-power descent.
- General open-stratum measure and chart residue identity.
- RLCT existence/positivity with its actual stronger hypotheses.
- Uniform expansion and generating identity.
- Generic first correction with the gap hypothesis.
- Top-coefficient continuity and law convergence with their restrictions.
- Quotient/source/Gaussian Gibbs results.

Do not update the bridge commit merely because grammar’s commit changes.

---

# E. Order of execution and risks

## E.1. Recommended execution order

### Step 1 — Create a notation and hypothesis sheet

Before editing prose, settle these conventions in one source file or editorial note:

1. \(T(s)\) and \(\widetilde T(s)\) exclude Gamma.
2. \(A_{\mu,r}\) uses \((\mu-s)^{-r}\); \(C_{\mu,r}=(-1)^rA_{\mu,r}\).
3. \(M_\mu\) is a candidate order bound.
4. \(\rho\) is raw; \(\nu=\Gamma(\lambda)\rho/(m-1)!\) is population-normalised.
5. \(\widehat\nu\) is branchwise tilted and coefficient-normalised.
6. \(D_{m+1}\cap Z_0\), \(X_m\), support truncation, and certificate are explicit.
7. \(N\) is the frozen asymptotic parameter; \(n\) is the sample size.
8. Distinguish global dimension, active chart dimension, and the common logarithmic-degree bound.

This prevents later sections from independently recreating incompatible conventions.

### Step 2 — Rewrite §2

Write definitions and the chart polar theorem first. This fixes the object whose evaluations everything else uses.

Preserve `rem:flat` prominently. It prevents the reader—and future edits—from reverting to a crossing-jet-only account.

### Step 3 — Rewrite the global part of §3

Introduce raw/population measures, certificate, deep-fibre nullity, and the all-observable theorem. Only then restore the restricted graded/residue material.

This order makes clear that admissibility is a restriction of a useful secondary description, not a limitation of the leading theorem.

### Step 4 — Rewrite §4 around B1 and B4

Transcribe the B4 hypotheses directly from the attached statement. Add (*) only after its interchange hypothesis is written.

Then restore ladder, graded formula, uniform expansion, generating identity, and the worked calculations.

### Step 5 — Rewrite §5

Use \(\widehat\nu\) in the general leading posterior formula. Separate frozen, diagonal, and Gaussian statements typographically, preferably as three propositions or a theorem with three explicitly different hypothesis blocks.

### Step 6 — Rewrite §1 and the abstract

Now the accessible theorem can accurately summarise the actual paper. Put the constant-field \(x^2y^2\) regression here and remove all duplicate calculations elsewhere.

### Step 7 — Rewrite §6

Keep the statistical variance-2 identification visibly conditional until the bridge declaration is available. Move the Gaussian identity machinery to Appendix E.

### Step 8 — Assemble appendices and coverage

Archive old moment tensors. Move rather than duplicate the remaining proofs. Update all grammar pins, but preserve bridge provenance.

### Step 9 — Perform a claim-and-reference audit

Search at least for:

```text
admissible
IsTest
D_{m+1}
extended measure
derivation
not formalised
Gamma
(m-1)!
(s-\mu)
(\mu-s)
fixed sample
converges in law
all coefficients
intrinsic
```

Check every occurrence against the new status.

---

## E.2. What to preserve as appendix material

Preserve:

- the smooth one-dimensional and generic-correction proofs;
- the face-first general expansion construction;
- detailed resolution/domain and partition-of-unity discussion;
- full FP calculations and the density-residue interpretation;
- quotient/source algebra;
- Weber/Weyl/incomplete-function material;
- Gaussian Stein/replica/interpolation/inverse-evidence/quenched-source identities.

Do **not** preserve a second competing narrative in the appendices. In particular, archive rather than compile the moment-tensor appendix, and remove duplicated constant-field \(x^2y^2\) derivations.

---

## E.3. Four high-risk places

### Risk 1 — Three different “polar coefficient” conventions

There are three conversions:

\[
\widetilde T(s)=\sum_r\frac{A_{\mu,r}}{(\mu-s)^r}+\cdots,
\qquad
C_{\mu,r}=(-1)^rA_{\mu,r},
\]
\[
\operatorname{polarCoeff}(c,\mu,q)
=(-1)^{q+1}q!\,c_{\mu,q}.
\]

A useful regression is always
\[
T(s)[1]=\frac1{4(\frac12-s)^2},
\quad
c_{1/2,1}=\frac14S_{1/2},
\quad
c_{1/2,0}=-\frac14\partial_\mu S_\mu|_{1/2}.
\]

If the constant term acquires a plus sign, the convention bridge is wrong.

### Risk 2 — Gamma and factorial counted twice

The raw measure contains the face factors \((2k_j)^{-1}\), but no radial Gamma factor and no \((m-1)!^{-1}\).

\[
c^{\rm pop}_{\lambda,m-1}(F)
=\frac{\Gamma(\lambda)}{(m-1)!}\int F\,d\rho,
\]
\[
c^{\rm emp}_{\lambda,m-1}(F;\xi)
=\frac1{(m-1)!}\sum_{\rm branches}\int F S_\lambda(\xi)\,d\rho_{\rm branch}.
\]

If using the library’s `empFaceMeasureU`, remember that its tilt is already divided by \(\Gamma(\lambda)\).

### Risk 3 — Silently strengthening a formal statement

The principal traps are:

- arbitrary transport versus certified transport;
- all smooth observables at the leading pair versus admissible observables at general graded pairs;
- formal B4 versus unformalised B15–B16;
- scalar pairing/jet congruence versus formal continuous distribution-valued maps;
- grammar’s leading measure versus a completed statistical compact-branch identification.

These distinctions must be in theorem statements, not repaired in Appendix F.

### Risk 4 — Losing branch information or confusing nullity with geometry

The empirical tilt uses one-sided traces. A single \(S_\lambda(\psi)\rho\) formula on \(U\) is only justified when the traces are compatible.

Also:
\[
\rho(D_{m+1}\cap Z_0)=0
\]
does not mean its closed support avoids deeper crossings, and it does not by itself prove finiteness at arbitrary \((\lambda,m)\).

---

The resulting paper has a clear hierarchy: **the meromorphic distribution is the object; polar data are its coefficients; residues and finite parts are evaluations; radial tilting supplies the empirical amplitudes; the global leading measure supplies the posterior limit; formal normalisation supplies the corrections.** The old stratum theory remains valuable, but as a precise associated-graded description within that hierarchy rather than as the framework into which every coefficient must be forced.