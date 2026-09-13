# Consult #106 — claim-and-dependency survey

## Executive assessment

**The note is substantially formalised, but its remaining gap is not “Gaussian averaging.”** The central Gaussian identities, raw-moment thresholds, compact-base transfer, and conditional annealed evidence chain already have substantial support. The principal unfinished statistical claim is:

> Transfer the **actual scaled, normalised statistical observables** to the Gaussian quartet, with enough integrability to pass expectations, and control the predictive logarithm’s remainder.

Three distinctions should govern the next work:

1. **Raw evidence moments are not quartet moment bounds.** The restriction \(\beta\kappa<2\) belongs to the sufficient raw-evidence moment argument. It should not be imported into the finite-resolution self-normalised Gaussian theorem, which holds for every \(\beta>0\).
2. **Fixed-phase posterior limits are not empirical posterior limits.** Substituting a sample from \(G\) into a deterministic spatial theorem produces a random limiting posterior; it does not establish transfer from the \(n\)-dependent empirical phase.
3. **The CLT/tail gap needs a signature audit before new mathematics.** The supplied endpoint declarations suggest that, under the coordinate certificate, a substantial part of that chain is already closed. The interface table may be stale or may describe a lower-level interface. These possibilities must be distinguished.

### Audit limitation

I have the complete TeX and declaration inventory, but not the complete Lean statements or their surrounding section variables. Consequently, this is a **documentary claim-and-dependency ledger**, not a fresh signature-level audit of `32cdbf6`.

In particular, I cannot honestly certify “zero mismatches” from declaration names and truncated signatures. Below:

- **(a)** means the supplied material identifies a declaration directly supporting the claim;
- **(b)** means support is expressly conditional or restricted as stated;
- **(c)** means the prose exceeds that support, omits a necessary condition, or conflates interfaces;
- **(d)** means no supporting formal statement is identified.

All proposed **(a)/(b)** entries require a **G0 signature gate** before being advertised as a new formal audit. This qualification is especially important for the CLT construction and the exponent-comparison paragraph.

No implementation, commit, or publication authorisation is implied.

---

# 1. Ledger conventions and hypothesis packs

To keep the ledger readable, the following hypotheses are inherited wherever indicated.

- **F:** \(\beta,\lambda>0\), or \(\beta,\mu>0\) where the index is \(\mu\).
- **G:** finite-dimensional centred Gaussian represented as \(AZ\), \(Z\) standard Gaussian; covariance \(AA^{\mathsf T}\). Degeneracy is allowed unless a scalar theorem expressly requires positive variance.
- **Q:** F, a nonempty finite index set, fixed positive weights \(\rho_i\), fixed covariance \(b=AA^{\mathsf T}\). Constant diagonal \(b_{ii}=c\) only where specified.
- **K:** nonempty compact metric base, finite nonzero Borel measure, continuous symmetric PSD kernel; continuous deterministic phase.
- **GF:** K plus the supplied `GaussianField` certificate: measurable evaluations, specified centred finite-dimensional Gaussian laws, integrable squared supremum norm.
- **S:** measurable i.i.d. observations in the certified data space, coefficient measurability and the weighted summable-coordinate-\(L^2\) certificate, fixed zero-phase amplitude datum.
- **B:** certified positive-radius monomial box chart, admissible exponent data, bounded amplitude, and the exact core/data identities required by the cited declaration. The displayed supplied signatures use \(k_i>0\).
- **MGF:** a uniform **full-box**, finite-sample phase MGF bound with proxy \(\kappa\), obtained either directly or from `UniformSubgaussianPhase`.
- **E:** scaled external remainder is integrable and
  \[
  \mathbb E|A_n\mathrm{Rem}_n|\longrightarrow0.
  \]

Notation `Module:declaration` identifies a file and declaration, **not an asserted Lean namespace**.

“Keep” below means keep in the main text, subject to G0 and the listed qualifications.

---

# 2. Claim ledger

## §2 — sampling, covariance, and jets

| ID | Exact claim | Exact substantive hypotheses | Existing declaration(s) | Missing bridge / status / unit |
|---|---|---|---|---|
| 2.1 | Resolution supplies \(f=\phi a\), \(\mathbb Ea=\phi\), hence \(K=\phi^2\). | Actual model-to-chart representation; integrability of \(a\); mean identity; normal-crossing presentation where used. | Sampling declarations **consume**, rather than construct, these identities. | **(b)** as an external geometric/model hypothesis, not a formalised construction. Keep; **MODEL gate**. |
| 2.2 | \(n^{-1}\sum f=\phi^2+\phi\zeta_n/\sqrt n\), and the sampling exponent has phase \(-\zeta_n\). | \(n>0\); \(f_i=\phi a_i\); definitions of centred sums. No probabilistic independence needed. | `SamplingIdentity:sum_mul_eq`, `sampling_exponent_eq`. | **(a)**. Add \(n\ge1\) explicitly to proposition. |
| 2.3 | Sample datum has centred coefficient phase, unchanged amplitude, and evaluation commutes with the mean. | Integrable phase observations; zero-phase amplitude datum; valid bounded evaluation map. | `SampleDatum:xiCoord_sampleDatum`; `AnalyticCertificate:dataPhase_sampleDatum`; `SamplingCompatibility:phaseEvalCLM_integral`, `phaseEval_sampleDatum_of_integrable`, `etaCoord_sampleDatum_of_integrable`. | **(a)**. Keep. |
| 2.4 | Taking coefficients of \(-a\) makes sample phase \(-\zeta_n\), and the core equals the sampling integral with \(N=n\). | B; Taylor representation of \(-a\) at the scaled box point; \(\mathbb Ea=\phi\); monomial identity for \(\phi\). | `SamplingCompatibility:evalF_xiCoord_sampleDatum_eq_neg_zetaEmp`, `sampling_exponent_eq_sampleDatum_phase`, `exp_sampling_exponent_eq_core_factor`, `dataBoxIntegral_sampleDatum_eq_sampling`. | **(b)**. Model/coefficient identification remains an input, correctly stated. |
| 2.5 | Global negation leaves a centred Gaussian law unchanged. | Centred jointly Gaussian law; global, not coordinatewise arbitrary, negation. | No specific symmetry declaration in inventory. | **(d)** locally, standard fact. Cite a declaration or leave as unmarked explanation. |
| 2.6 | Normal-location example has phase \(\sqrt2\,n^{-1/2}\sum X_i\) and variance \(2\). | \(n>0\); independent standard normal observations; specified normal form. | `EffectiveTemperature:sum_normalLocation`, `normalLocation_standard_form`, `neg_zetaEmp_normalLocation`, `variance_phase_normalLocation`. | **(a)** for calculation; **(b)** regarding geometry/remainder, as already stated. |
| 2.7 | \(a\) and \(\xi_n\) are defined on the divisor, unlike the naive quotient. | An already extended resolved coefficient \(a\) on the entire chart. | No construction declaration identified. | **(b)** as a consequence of the supplied standard form; not a theorem constructing the extension. |
| 2.8 | “By the CLT, \(\xi_n\Rightarrow G\)” with the displayed covariance. | S; a bounded continuous evaluation map from the data space to the selected function space; appropriate law/tail certificates or their construction; second moments. | `L1SeqCLT:clt_l1`; functional and closure declarations below. | **(c)** as presently unconditional introductory prose. Replace by “Under the coordinate CLT certificate and the evaluation-map compatibility…”. **CLT gate**. |
| 2.9 | \(C(u,u')=\mathbb E[a(u)a(u')]-\phi(u)\phi(u')\). | Square-integrable evaluations; the mean identity; limiting Gaussian evaluation covariance matches the observation covariance. | `L1GaussianFunctional…`; `GaussianLinearCombination…` support routes, but no direct resolved-model covariance declaration identified. | **(b)** conditional identification; add a precise adapter reference rather than attributing everything to `clt_l1`. |
| 2.10 | Likelihood normalisation \(\mathbb E_qe^{-f}=1\). | No model mass outside \(\{q>0\}\); positivity \(p>0\), \(q\)-a.s., for a finite real log ratio; measurability. | `AnnealedIdentity` consumes normalisation. | **(b)**. Existing support qualification is important and correct. |
| 2.11 | Exponential Taylor bound and \(|\mathbb Ea^2-2h|\le2|\phi|\,\mathbb E[|a|^3e^{|\phi a|}]\). | Probability law; \(\phi\ne0\); the two mean identities; the four stated integrability assumptions. | `DivisorVariance:abs_exp_neg_sub_le`, `abs_integral_sq_sub_le`. | **(a)**. Keep. |
| 2.12 | Constant improves from \(2\) to \(1/3\). | Same assumptions, using the sharper third-order exponential remainder. | None identified. | **(d)**. Optional unmarked mathematical aside; not a central bridge. |
| 2.13 | \(\mathbb Ea_t^2\to2h_0\), then \(\mathbb Ea_0^2=2h_0\). | Pointwise variance-lemma assumptions eventually; \(\phi_t\to0\), eventually nonzero; \(h_t\to h_0\); uniform cubic envelope; for the second claim, second-moment convergence. | `DivisorVariance:tendsto_integral_sq`, `integral_sq_eq_of_tendsto`. | **(a)**. |
| 2.14 | Divisor covariance diagonal is \(2\). | Previous row with \(h=1\), second-moment continuity, and centred divisor evaluation. | Same declarations plus covariance identification. | **(b)**, correctly conditional. Do not replace the envelope by pointwise analyticity. |
| 2.15 | Normalisation alone does not imply variance \(2\); the shifted Gaussian example disproves it. | Given Gaussian family and arbitrary \(\sigma\). | None identified for the counterexample. | **(d)** formal status, mathematically sound explanatory material. Keep without a certification implication. |
| 2.16 | Fisher-score calculation recovers variance \(2\). | Regular correctly specified model; differentiability and interchange assumptions; positive Fisher information; the local coordinate expansion. | None identified. | **(d)**. Label “informal regular-model check” or move to an examples appendix. |
| 2.17 | Leaf jet covariances equal differentiated kernel covariances, and jets are jointly Gaussian. | Bounded jet maps on the chosen data space, or mean-square differentiability plus interchange domination. **Plain \(\ell^1\) summability at the boundary does not automatically make derivative evaluation bounded.** | `L1Seq:coordCLM`; Gaussian functional declarations cover bounded linear functionals, not arbitrary jets. | **(c)** if read as discharged. State as a conditional jet interface; use a smaller radius/weighted certificate when needed. **JET gate**, deferred. |
| 2.18 | No spatial covariance decay is asserted. | None. | Not a theorem requiring certification. | **(a)** as a scope limitation. Keep. |

### Important notation correction

Material D’s shorthand
\[
K_n=K+\xi_n/\sqrt n
\]
does **not** use the note’s resolved phase convention. In the note,
\[
K_n(u)=\phi(u)^2-\frac{\phi(u)}{\sqrt n}\xi_n(u).
\]
Use a different symbol for the fluctuation of \(K_n\) itself. Otherwise the sign audit is undone at the notation layer.

---

## §3 — raw Gaussian averages

| ID | Exact claim | Hypotheses | Existing declaration(s) | Missing bridge / status / unit |
|---|---|---|---|---|
| 3.1 | One-point mean equals \(\Gamma(\mu)(\beta\delta)^{-\mu}\) below threshold, and extended mean is infinite at/above threshold. | F; centred scalar Gaussian variance \(c\ge0\); \(\delta=1-\beta c/2\). | `GaussianThreshold:lintegral_gaussMomentJ_eq_of_lt`, `…eq_top_of_ge`; `GaussianDichotomy:lintegral_gaussMomentJ_eq`; `HeadlineGaussian:headline_gaussian_dichotomy`; `FluctuationSelfNormalised:fluctuation_eq_two_mul_gaussMomentJ`. | **(a)**. ENNReal divergence and Bochner finiteness must remain distinguished. |
| 3.2 | At divisor variance \(2\), the Gaussian raw threshold is \(\beta<1\). | Row 2.14’s divisor hypotheses, then row 3.1. | Same. | **(b)**. “Every sample coefficient is finite” refers to finite phase values, not finite dataset expectation. |
| 3.3 | Tilted first and second Gaussian moments have the displayed covariance formulas. | G; real tilt parameter. | `GaussianTilted:integral_mul_exp_gaussianVector`, `integral_mul_mul_exp_gaussianVector`. | **(a)**. |
| 3.4 | \(Q=1,2\) insertion formulas and their integrability. | F, G; \(\delta>0\). | `GaussianInsertion:integral_coord_mul_fluctuation`, `integral_coord_mul_coord_mul_fluctuation`, `integral_fluctuation_gaussianVector`. | **(a)** in the represented-vector formulation. |
| 3.5 | Fubini and the radial Gamma integral justify the insertion formulas. | The integrability assumptions in the generic Fubini lemma; discharged by the Gaussian tilted bounds in the specialised theorems. | `GaussianInsertion:integral_mul_fluctuation_eq`, `integral_radialKernel_mul_tilt`. | **(a)**. Do not cite the generic Fubini lemma alone for unconditional interchange. |
| 3.6 | Every centred finite Gaussian vector can be represented as \(AZ\). | Finite covariance PSD; equality in law sufficient. | `GaussianLinearCombination:gramFactor_mul_transpose`, `isGaussian_ext_of_moments`, `map_evalVec_eq_gaussianVector`. | **(b)**: a small representation adapter/reference, not a new Gaussian integration programme. |
| 3.7 | Bilocal extended-integral identity. | F; represented jointly Gaussian pair. | `BilocalGaussian:lintegral_fluctuation_mul_fluctuation`. | **(a)**. |
| 3.8 | Bilocal finiteness for \(A,B>0,\ H<2\sqrt{AB}\). | F and those inequalities. | `BilocalGaussian:lintegral_bilocalIntegrand_lt_top`, `integrable_fluctuation_mul_fluctuation`. | **(a)**. Negative covariance needs no absolute-value restriction here. |
| 3.9 | Critical-line finiteness iff \(\lambda<1/4\). | \(A,B>0,\ H=2\sqrt{AB}\), \(\lambda>0\). | `BilocalCriticalBoundary:bilocal_lintegral_lt_top_iff_of_critical`, `lintegral_fluctuation_mul_fluctuation_lt_top_iff_of_critical`. | **(a)**. |
| 3.10 | Critical substitution yields the stated one-dimensional profile and its integrability test. | Same critical hypotheses. | `BilocalCriticalBoundary:lintegral_bilocalIntegrand_critical_eq`, `lintegral_criticalProfile_lt_top_iff`. | **(a)**. |
| 3.11 | Bilocal divergence for \(A,B>0,\ H>2\sqrt{AB}\). | Those strict inequalities. | `BilocalDivergence:lintegral_bilocalIntegrand_eq_top`. | **(a)**. Replace “in particular” after the critical-line discussion by “Above the critical line”. |
| 3.12 | Absolutely convergent cross-pairing series. | \(A,B>0,\ |H|<2\sqrt{AB}\), F. | `BilocalSeries:summable_bilocalCoeff`, `integral_fluctuation_mul_fluctuation_eq_tsum`. | **(a)**. |
| 3.13 | Divergence whenever \(A\le0\) or \(B\le0\). | F; the stated bilocal integrand. | None; the note expressly acknowledges this. | **(d)**, not wrong or heuristic merely because unformalised. Keep as a separately labelled analytical proof, or move out of the dotted proposition’s proof to avoid scope confusion. |
| 3.14 | Equal-diagonal threshold simplifications and \(b=2,\beta=1/2\) endpoint. | \(c=c'=2\), admissible Gaussian covariance \(|b|\le2\), previous threshold hypotheses. | Algebraic specialisations of rows 3.8–3.12. | **(b)**; small corollary packaging only. |
| 3.15 | Connected covariance integral; series starts at \(r=1\). | Product and individual means integrable; series additionally needs \(|H|<2\sqrt{AB}\). | `BilocalSeries:cov_fluctuation_eq_connected`, `cov_fluctuation_eq_tsum`. | **(a)** with the two different regimes kept explicit. |
| 3.16 | Scalar real-\(p\) moment strict thresholds. | \(\lambda,\beta,c,p>0\). | `GaussianPMoment:integrable_fluctuation_rpow_gaussianReal`, `lintegral_fluctuation_rpow_gaussianReal_eq_top`. | **(a)**. |
| 3.17 | Scalar critical moment iff \(p(2\lambda-1)<-1\). | Same, with \(\beta cp=2\). | `GaussianCriticalMoment:integrable_fluctuation_rpow_gaussianReal_iff_of_critical`. | **(a)**. |
| 3.18 | Finite-mixture strict moment criterion is governed by the largest diagonal variance. | Q; \(p\ge1\); positivity of tested coordinate variances as required by cited finite-moment statement. | `GaussianPMoment:integrable_quartetD_rpow`, `lintegral_quartetD_rpow_eq_top`, `quartetD_rpow_le`, `gaussianVector_map_eval`. | **(b)**. Say **strict-regime threshold**; mixture endpoint classification is not supplied by these two dots. Zero-variance coordinates can be handled separately. |
| 3.19 | Sharp upper/lower fluctuation bounds prove the moment tests. | F; stated \(\eta\)-range or \(a\ge2\). | `FluctuationSharpBounds:fluctuation_le_eta`, `le_fluctuation_of_two_le`; `FluctuationSharpUpper:fluctuation_eq_exp_mul_integral`, `fluctuation_le_polynomial_mul_gaussian`; `GaussianCriticalMoment:fluctuation_mono`. | **(a)**. The displayed asymptotic is explanatory, not needed for certification. |
| 3.20 | Compact-base \(p\)-moment sufficiency, but not necessity from pointwise divergence. | GF; \(p\ge1\); \(C(x,x)\le c\); \(p\beta c<2\). | `CompactBaseFirstMoment:GaussianField.integrable_compactD_rpow`. | **(b)**, correctly qualified. |
| 3.21 | A finite moment of the Gaussian limit does not give uniform empirical moments. | None beyond the distinction between limit and approximants. | Logical limitation, not a transfer theorem. | Keep. No reverse implication should be introduced. |
| 3.22 | Floor-rises averaged leaf formula and bilocal \(r=1\) coefficient. | The stated leaf geometry; Gaussian evaluations with diagonal \(2\); measurability; Tonelli for nonnegative amplitude or absolute integrability; stated temperature ranges. | One-point/bilocal results; no dedicated worked-example declaration identified. | **(d)** as a packaged example, mathematically supported by **(b)** specialisation. Keep; low-priority arithmetic corollary gate. |

---

## §4 — finite self-normalised quartet

| ID | Exact claim | Hypotheses | Existing declaration(s) | Missing bridge / status / unit |
|---|---|---|---|---|
| 4.1 | Definitions of \(D,W,M_2,H,V\). | Q; constant diagonal for displayed \(V=cM_2-Q\). | `GaussianQuartetDet:quartetD`, `quartetW`, `quartetM2`, `quartetH`, `quartetV`. | **(a)** definitions. Define the bilocal quantity \(Q(g)\) explicitly before using the letter in prose. |
| 4.2 | Marked posterior interpretation and Hilbert-space variance representation of \(V\). | Positive finite weights; radial integrability; Gram representation \(b_{ij}=\langle h_i,h_j\rangle\). | Algebraic quartet declarations; no marked-probability-space identity in inventory. | **(d)** as a formal posterior representation, although the finite algebra is sound. Optional adapter, not prerequisite for the existing theorem. |
| 4.3 | \(S_\mu(a)>0\), hence \(D(g)>0\). | Positive indices/temperature; nonempty positive-weight mixture. | Used throughout listed quartet declarations; standalone positivity declaration not identified in inventory. | **(b)** pending G0 identification of the exact positivity lemmas. |
| 4.4 | Schwinger–Dyson \(M_2=\lambda/\beta+H/2\). | Q; deterministic \(g\). | `GaussianQuartetDet:quartetM2_eq`. | **(a)**. |
| 4.5 | \(R_1^2\le R_2\), \(R_2\le2\lambda/\beta+a_+^2/4\), corresponding \(R_1\) bound. | F; real \(a\). | `FluctuationSelfNormalised:fluctuation_half_sq_le`, `fluctuation_succ_le`, `fluctuation_half_le`. | **(a)**. |
| 4.6 | \(W_i\ge0\), linear bound; quadratic bounds for \(M_2,H,Q,V\). | Q; fixed finite covariance. | `GaussianQuartetDet:quartetW_nonneg`, `quartetW_le`, `polyBoundedPi_quartetW`; `GaussianQuartetGeneral:polyBoundedPi_quartetDiag`, `polyBoundedPi_quartetVgen`. | **(b)**: the single \(W\)-growth dot should not purport to certify the entire list. Add direct references or state the elementary derived bounds. **UI unit**. |
| 4.7 | Polynomial lower bound for \(S\), quadratic bound for \(|\log S|\), then \(|\log D|\). | F; positive fixed weights. | `FluctuationSelfNormalised:fluctuation_ge_lower`, `abs_log_fluctuation_le`; `CovarianceInterpolation:abs_log_quartetD_le`. | **(a)**. |
| 4.8 | Derivative formula for \(W_i\). | Q, deterministic phase. | `GaussianQuartetDet:hasFDerivAt_quartetW`. | **(a)**. |
| 4.9 | \(0\le V\le cM_2\). | Q with constant diagonal; Gram covariance. | `GaussianQuartetDet:quartetV_nonneg`; general-diagonal positivity declarations. | **(a)** for the stated PSD setting, not arbitrary matrices. |
| 4.10 | Scalar Stein identity. | Positive scalar Gaussian variance; differentiability and polynomial growth of function and derivative. | `GaussianStein:gaussianReal_stein`. | **(a)**. In prose write \(v>0\), rather than a bare real \(v\ne0\). |
| 4.11 | Product and correlated-vector Stein identities. | G; differentiability and stated polynomial growth. | `GaussianSteinVector:stdGaussianPi_stein`, `gaussianVector_stein`. | **(a)**. Degenerate \(AA^{\mathsf T}\) is allowed. |
| 4.12 | All quartet observables integrable for every \(\beta>0\), and \(\mathbb EH=\beta\mathbb EV\). | Q, constant diagonal for the displayed \(V\). | `GaussianQuartet:integral_quartetH_eq`, `quartet_identities`; supporting polynomial bounds. | **(a)**. No raw-evidence threshold. |
| 4.13 | \(\nu\ge0\), \(\mathbb EV=2\nu/\beta\), \(\mathbb EM_2=\lambda/\beta+\nu\). | Same; \(\nu=\mathbb EH/2\). | `GaussianQuartet:quartet_identities`. | **(a)**. |
| 4.14 | Four algebraic combinations give the familiar quartet coefficients. | Same identities; definitions of the four combinations. | `GaussianQuartet:bayes_quartet`. | **(a)** as algebra. |
| 4.15 | These combinations are coefficients of the actual model’s expected errors. | Joint empirical observable transfer; statistical observable/normal-form identification; UI or suitable moments; predictive remainder; appropriate covariance normalisation. | No theorem identified closing this chain. | **(b)** as explicitly conditional interpretation; **(d)** as an unconditional statistical theorem. **TRANSFER + UI + PRED units**. |
| 4.16 | \(\nu\) equals a model’s singular fluctuation. | A model-level identification theorem and its hypotheses. | None supplied. | **(d)**, correctly disclaimed. Keep disclaimer. |

---

## §5 — interpolation and compact base

| ID | Exact claim | Hypotheses | Existing declaration(s) | Missing bridge / status / unit |
|---|---|---|---|---|
| 5.1 | \(L(s)\) continuous on \([0,1]\), differentiable inside, \(L'=\beta^2\mathbb EV_s/2\). | Q; covariance in \(V_s\) is the original fixed covariance; \(s>0\) for derivative. | `CovarianceInterpolation:continuousOn_interpL`, `hasDerivAt_interpL`, `interpV_nonneg`. | **(a)**. |
| 5.2 | Integrated interpolation identity and \(\mathbb E\log D\ge\log D_0\). | Q. | `CovarianceInterpolation:integral_log_quartetD_eq`, `log_quartetD_zero_le_integral`. | **(a)**. |
| 5.3 | Scaled Stein identity \(\mathbb EH(\sqrt sG)=\beta s\,\mathbb EV_s\). | Q; \(s\ge0\). | `CovarianceInterpolation:integral_quartetH_scaled`. | **(a)**. No pathwise derivative at zero. |
| 5.4 | General diagonal \(V_{\rm gen}\ge0\), IBP and interpolation. | Q without constant-diagonal assumption. | `GaussianQuartetGeneral:quartetVgen`, `quartetVgen_nonneg`, `integral_quartetH_eq_gen`, `integral_log_quartetD_eq_gen`, `log_quartetD_zero_le_integral_gen`. | **(a)**. |
| 5.5 | Continuous PSD kernel and compact \(D,H,V\) definitions. | K. | `CompactBaseKernel:PSDKernel`, `compactV`; `CompactBaseQuantise:compactD`, `compactH`. | **(a)** definitions, not field existence. |
| 5.6 | `GaussianField` packages continuous paths, evaluation laws and squared-supremum integrability. | Exactly the supplied record fields. | `CompactBaseFinite:GaussianField`. | **(a)** as adapter definition. |
| 5.7 | Compact \(D>0\), log bound, \(M_2,H,V\) bounds independent of partition. | K; \(\|g\|_\infty\le R\); diagonal upper bound \(c\) for \(V\). | `CompactBaseQuantise:compactD_pos`, `abs_log_compactD_le`; `CompactBaseKernel:compactM2_le`, `abs_compactH_le`, `compactV_nonneg`, `compactV_le`. | **(a)**. |
| 5.8 | Measurable finite-range approximations exist and preserve mass under pushforward. | Compact metric base; positive mesh; finite measure. | `CompactBaseQuantise:exists_measurable_finiteRange_approx`; `CompactBaseGaussian:map_quantise_real_univ`, `map_quantise_ne_zero`. | **(a)**. |
| 5.9 | \(D,\log D,H,V\) converge for each fixed continuous phase under mesh refinement. | K; mesh tends to zero; nonzero mass for ratios/logarithms. | `CompactBaseQuantise:tendsto_compactD_map`, `tendsto_log_compactD_map`, `tendsto_compactH_map`; `CompactBaseKernel:tendsto_compactV_map`. | **(a)**. Not uniform over an entire sup-norm ball of \(C(K)\). |
| 5.10 | Atomic quantities equal finite-quartet quantities; positivity survives. | Finite-range quantisation; positive-mass atoms; PSD kernel. | `CompactBaseFinite:compactV_map_eq`; `CompactBaseKernel:compactQ_nonneg`, `compactQnum_le`, `compactV_nonneg`. | **(a)**. |
| 5.11 | Compact IBP and integrated interpolation follow by dominated convergence. | GF. | `CompactBaseFinite:integral_compactH_map_eq`, `integral_log_compactD_map_eq`; `CompactBaseGaussian:tendsto_integral_compactH_map`, `tendsto_integral_compactV_map`, `tendsto_integral_log_compactD_map`, `integral_compactH_eq`, `integral_log_compactD_eq`, `log_compactD_zero_le_integral`. | **(a)**. |
| 5.12 | Every continuous PSD kernel has a `GaussianField` of the stipulated kind. | Continuity and PSD alone are **insufficient**. | No such theorem; explicitly not claimed by the adapter. | **(d)** and false at this level of generality. Do not make this a target. **FIELD unit**, narrower only. |

---

## §6 — stochastic interfaces and conditional assembly

| ID | Exact claim | Hypotheses | Existing declaration(s) | Missing bridge / status / unit |
|---|---|---|---|---|
| 6.1 | Fixed continuous phase gives leading evidence coefficient. | B; fixed continuous phase/amplitude and the spatial theorem’s hypotheses. | `SpatialPhaseLeading:spatialPhase_tendsto`. | **(a)** as deterministic/fixed-phase asymptotics. |
| 6.2 | Fixed-phase energy and location posterior limits are evidence-weighted face mixtures. | Continuous nonnegative amplitude, positive face functional, \(N_m\to\infty\), stated observable hypotheses. | `SpatialEnergyLaw:spatialEnergyLaw_tendsto`; `SpatialLocationLaw:phasePosterior_tendsto_faceLocation`. | **(a)** in that regime. |
| 6.3 | Taking \(\xi=G\) describes a random Gaussian posterior ratio. | A field with admissible paths and positive denominator. | Previous deterministic results applied pathwise. | **(b)**. This describes the candidate limit, **not** empirical transfer. |
| 6.4 | Leading spatial posterior weights are random in general; expectation of ratio is not ratio of expectations. | Nontrivial spatial phase and observable; ratios well-defined. | `GibbsJointRatio:expectation_eq_div` is algebra, not a universal nonconstancy theorem. | **(b)** explanatory statement. Say “can be random at order one”; spatially constant or otherwise cancelling cases exist. |
| 6.5 | Exact annealed product identity. | Measurability, independence, identical one-observation laws where the power is used, nonnegative Tonelli integrands. | `AnnealedIdentity:lintegral_annealedZ`. | **(a)**. |
| 6.6 | \(\mathbb EZ_n(1)=\pi(W)\). | Row 6.5; likelihood normalisation; **finite prior mass** for the real/Bochner expectation formulation. | `AnnealedIdentity:lintegral_annealedZ_one`. | **(b)**. The dot is an extended-integral theorem. Add finite prior mass or retain \(\mathbb E_+\). |
| 6.7 | Finite Gaussian denominator mean and divergence. | Q; constant diagonal; respective threshold conditions. | `GaussianDenominator:lintegral_fluctuation_gaussianVector`, `integral_quartetD`, `lintegral_quartetD_eq_top`, `not_integrable_quartetD`. | **(a)**. |
| 6.8 | Compact first moment is the diagonal-variance face integral. | GF; strict subcriticality everywhere; compactness and kernel continuity supply a uniform margin. | `CompactBaseFirstMoment:GaussianField.lintegral_exp_eval`, `GaussianField.integral_compactD_eq`. | **(a)**. |
| 6.9 | Constant-diagonal compact inflation factor; divergence on a positive-mass overcritical set. | GF; stated constant diagonal/subcriticality or positive-measure divergence condition. | `CompactBaseFirstMoment:GaussianField.integral_compactD_eq_of_const_diag`, `…eq_compactD_zero_mul`, `GaussianField.lintegral_compactD_eq_top`. | **(a)**. |
| 6.10 | Jensen compares \(\mathbb E\log D\) and \(\log\mathbb ED\), not identifies them. | Integrable positive \(D\), integrable \(\log D\). | No specific Jensen declaration dotted here; existing moment/log results supply its inputs. | **(b)** elementary consequence. |
| 6.11 | Weak convergence plus a uniform \(p>1\) moment gives convergence of means. | Real measurable random variables on probability spaces; distributional convergence; genuine integrability/moment bounds. | `ExpectationBridge:tendsto_integral_of_tendstoInDistribution_of_moment`, `abs_sub_clipR_le`. | **(a)**. A bound on totalised Bochner integrals alone must not replace integrability hypotheses. |
| 6.12 | Nonnegative weak limit with infinite extended mean forces approximating extended means to infinity. | Nonnegative variables and limit; distributional convergence; infinite limiting extended mean. | `ExpectationBridge:tendsto_lintegral_top_of_tendstoInDistribution`. | **(a)**. |
| 6.13 | Application of expectation/divergence bridge to the Gaussian denominator. | Rows 6.7, 6.11/12; empirical scaled denominator convergence supplied. | `ExpectationBridge:tendsto_integral_quartetD_of_tendstoInDistribution`, `tendsto_lintegral_top_of_tendstoInDistribution_quartetD`. | **(b)**, not an expected-error result. |
| 6.14 | Pointwise one-sided MGF gives the displayed raw compact-\(D\) \(p\)-moment bound. | Finite measure, joint measurability, F, \(p\ge1\), proxy \(c\ge0\), \(p\beta c<2\). | `UniformMomentSubgaussian:lintegral_compactD_rpow_le_of_subgaussian`, `ofReal_fluctuation_eq_lintegral_gammaWeight`. | **(a)**. In the proof, the MGF bound makes the expectation **at most** \(1\), not “exactly \(1\)”. |
| 6.15 | Bounded independent pointwise observations give uniform empirical raw-\(D\) moments. | Uniform bounds \([l,h]\), independence for each fixed base point, measurability; stated temperature/moment condition. | `UniformMomentSubgaussian:empiricalField`, `lintegral_compactD_rpow_empirical_le`. | **(a)**. No independence across base points needed. |
| 6.16 | Evaluation measurability, Bochner integrability and domination transfer. | Continuous paths/measurable evaluations where used; moment and domination hypotheses. | `UniformMomentSubgaussian:measurable_uncurry_eval`, `integrable_compactD_rpow_of_subgaussian`, `moment_bound_of_dominated`. | **(a)**. |
| 6.17 | Deterministic finite-weight exponential integral has \(p\)-moment at most mass\(^p\). | Finite measure; joint measurability; **\(p\ge1\)**; \(\mathbb Ee^{pH}\le1\) a.e. | `FiniteWeightMoment:lintegral_rpow_lintegral_exp_le_mass_rpow`. | **(c)**: proposition does not locally state \(p\ge1\). Add it. |
| 6.18 | Scaled chart integral moment bounded by reduced-temperature population mass. | \(p\ge1\), nonnegative weight/radial function and scale, bounded amplitude, integrability of deterministic mass, MGF; \(\alpha>0\) for the subsequent population theorem. | `FiniteWeightMoment:moment_scaled_integral_le_population_mass`. | **(b)** after explicitly restoring these assumptions. |
| 6.19 | Certified box-core moment bound and uniformity. | B, MGF, admissible \(p\); deterministic population bound. | `BoxMomentBound:moment_scaled_dataBoxIntegral_le`, `uniform_moment_scaled_dataBoxIntegral`, `measurable_uncurry_xiField`. | **(b)**. Verify whether the theorem needs bounded **amplitude** or bounded full data; do not claim bounded sample-data norm uniformly in \(n\). |
| 6.20 | Population mass is the zero-phase monomial integral; domination of exponent pairs gives its scaled bound. | B; \(\alpha>0\); scale-pair domination and eventual positive \(n\). | `PopulationBoundDischarge:popBoxMass_eq_monomialBoxReal`, `exists_population_bound_scaleA`, `uniform_moment_scaled_dataBoxIntegral_of_dominated`. | **(a)** as population asymptotics. |
| 6.21 | Sample phase is a bounded linear evaluation of the centred empirical data. | S; evaluation point in the closed unit cube. | `SampleDatumMGF:phaseEvalCLM`, `phaseEval_sampleDatum`. | **(a)**. |
| 6.22 | Bounded \(\ell^1\) observations give proxy \(M_0^2\) uniformly over the box and sample size. | Measurable i.i.d. observations; a.s. norm bound; zero-phase amplitude. | `SampleDatumMGF:lintegral_exp_phase_sampleDatum_le`. | **(a)**. |
| 6.23 | Uniform single-observation sub-Gaussian proxy is inherited by the empirical phase. | S’s integrability/independence parts; `UniformSubgaussianPhase`; \(n>0\). | `SubgaussianPhase:UniformSubgaussianPhase`, `hasSubgaussianMGF_empiricalPhase`, `lintegral_exp_phase_sampleDatum_le_of_subgaussian`. | **(a)**. |
| 6.24 | Evaluation variance \(\le\kappa\); bounded observations supply the proxy. | Centred two-sided sub-Gaussian MGF; or bounded observations. | `SubgaussianPhase:variance_le_of_hasSubgaussianMGF`, `phaseVar_le_of_uniformSubgaussian`, `uniformSubgaussianPhase_of_bounded`. | **(a)**. |
| 6.25 | Fernique discharges squared-supremum integrability for a Gaussian Borel law on \(C(K)\). | Borel Gaussian Banach law; separable Banach setting; probability measure. | `GaussianFieldFernique:integrable_sq_norm_of_isGaussian`, `GaussianField.ofIsGaussian`. | **(a)**. Not existence from the kernel. |
| 6.26 | Centring/covariance certificates determine finite evaluation laws and construct the adapter. | Existing Gaussian Borel law; specified first/second moments; K. | `GaussianLinearCombination:map_evalCombination_eq_gaussianReal_of_certificates`, `isGaussian_ext_of_moments`, `PSDKernel.kernelMatrix_posSemidef`, `gramFactor_mul_transpose`, `map_evalVec_eq_gaussianVector`, `GaussianField.ofIsGaussianCertificates`. | **(a)**. |
| 6.27 | Scaled core weak limit plus scaled remainder \(o_P(1)\) gives total weak limit. | Measurability; \(A_nZ_n^{core}\Rightarrow L\); \(A_n\mathrm{Rem}_n\to0\) in probability. | `ScaledAssembly:tendstoInDistribution_scaled_assembly`. | **(a)**. |
| 6.28 | Scaled \(L^1\) negligibility implies \(o_P(1)\); exponential annealed bounds imply scaled negligibility. | E; or an actual bound \(\mathbb E|\mathrm{Rem}_n|\le Ce^{-cn}\), \(c>0\). | `ScaledAssembly:tendstoInMeasure_zero_of_tendsto_integral_abs`, `tendsto_scaleA_mul_exp_neg`. | **(b)**. A pathwise good-event gap bound is not this hypothesis. Replace “automatic” by “under the paper’s annealed-gap hypotheses for this remainder”. |
| 6.29 | Uniform core moments give convergence of the total expectation. | Weak core limit, uniform \(p>1\) core moments, **E**, not merely an \(o_P(1)\) external remainder. | `ScaledAssembly:tendsto_integral_scaled_assembly`. | **(c)**: item (2)’s “If moreover” can inherit only the weaker condition of item (1). State E explicitly. |
| 6.30 | Positive limiting mean gives asymptotic equivalence for \(\mathbb EZ_n\). | Row 6.29; \(\mathbb EL>0\); specified scale. | `ScaledAssembly:isEquivalent_integral_scaled`. | **(a)** once 6.29 is repaired. |
| 6.31 | Positive scaled weak limit gives \(\log Z_n/\log n\to-\lambda\) in probability. | \(Z_n>0\), \(L>0\) a.s.; scaled weak convergence; scale asymptotics. | `ScaledAssembly:tendsto_measure_log_of_tendstoInDistribution`, `tendstoInMeasure_log_div_log`. | **(a)**. Neither a CLT nor an expected-log expansion. |
| 6.32 | Finite sums of cores inherit uniform moments and expectation assembly. | B per chart, finite chart set, MGF, common admissible \(p>1\), population bounds, core weak limit, E. | `CertifiedCoreAssembly:abs_sum_rpow_le`, `uniform_moment_coreSum`, `tendsto_integral_scaled_assembly_of_certified_subgaussian_cores`. | **(a)**. No chart independence needed. |
| 6.33 | Population bounds and sample MGFs discharge the corresponding assembly inputs. | Pair domination; S; bounded-observation or sub-Gaussian hypothesis; E and core weak limit. | `PopulationBoundDischarge:tendsto_integral_scaled_assembly_of_dominated_cores`; `SampleDatumMGF:tendsto_integral_scaled_assembly_sampleDatum`; `SubgaussianAssembly:tendsto_integral_scaled_assembly_sampleDatum_subgaussian`. | **(b)**. Keep bounded-amplitude versus bounded-phase-observation assumptions separate. |
| 6.34 | Leading predecessors vanish; ordered remainder is the scaled core. | B at its leading pair; scale convention/eventual \(n\). | `SampleDatumLimit:predSum_leading`, `scaleA_mul_dataBoxIntegral_eq_orderedRemainder`. | **(a)**. |
| 6.35 | Single-chart empirical scaled-core limit follows from stochastic expansion/tightness. | B, S, and whatever CLT/law certificates the complete signature actually consumes. | `SampleDatumLimit:tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum`; `SampleExpansion:sample_stochastic_expansion`. | **(b), CLT gate**. No claim of an a.s. empirical expansion. |
| 6.36 | Single-chart expectations converge under bounded or sub-Gaussian observations. | Row 6.35; amplitude bound; \(p>1,\ p\beta\kappa<2\); E. | `SampleDatumLimit:tendsto_integral_scaled_sampleDatum_single`; `SubgaussianAssembly:tendsto_integral_scaled_sampleDatum_single_subgaussian`. | **(b)**. |
| 6.37 | Same-sample finite charts converge jointly; only leading charts survive. | Finite stacked S certificate; B per chart; common scale dominated by every chart pair; joint, not separate scalar, law. | `JointSampleLimit:jointSampleDatum_apply_eq_sampleDatum`, `continuous_jointLeadingCoeff`, `tendstoInDistribution_scaled_coreSum_sampleDatum`. | **(b)**. Verify stacked certificate construction; no independent-chart substitution. |
| 6.38 | Finite-chart expectation assembly. | Row 6.37; uniform moment hypotheses per chart/common proxy; E. | `JointSampleLimit:tendsto_integral_scaled_coreSum_sampleDatum`; `SubgaussianAssembly:tendsto_integral_scaled_coreSum_sampleDatum_subgaussian`. | **(b)**. |
| 6.39 | Coordinate Gaussian marginals plus tail bound make all bounded linear functionals Gaussian with observation variance. | Probability law with those certificates; summable coordinate controls; bounded observations or Banach \(L^2\) as in the corresponding theorem. | `L1GaussianFunctional:map_eq_gaussianReal_of_marginals`, `map_phaseEvalCLM_eq_gaussianReal`; `L1GaussianFunctionalL2:map_eq_gaussianReal_of_marginals_of_memLp`. | **(a)** conditional on certificates. Does not itself construct the law. |
| 6.40 | Phase moment is \(S/2\); Gaussian evaluation mean gives the modified-temperature factor. | F; identified Gaussian evaluation variance; \(\beta\sigma^2<2\). | `LeadingCoeffGaussianMoment:phaseMoment_eq_half_fluctuation`, `integral_fluctuation_gaussianReal`, `integral_phaseMoment_evalF`; `SubgaussianAssembly:integral_phaseMoment_evalF_subgaussian`. | **(a)**. |
| 6.41 | Gaussian amplitude coordinates vanish; leading coefficient equals represented face functional. | Phase-only observations; zero covariance/mean amplitude coordinates; B. | `LeadingCoeffGaussianMoment:ae_etaCoord_eq_zero`, `dataBoxCoeff_leading_eq_spatialFace`. | **(a)** under those certificates. |
| 6.42 | Fubini identifies the limiting coefficient’s expectation with the displayed covariance-modified face integral. | B; deterministic bounded amplitude; identified evaluation laws; uniform strict subcritical bound; coefficient integrability. | `LeadingCoeffGaussianMoment:integral_dataBoxCoeff_leading_eq`; `SubgaussianAssembly:integral_dataBoxCoeff_leading_eq_subgaussian`. | **(a)** conditional theorem. Define the geometric \(c\) in \(c^{-\lambda}\); it must not be confused with variance/proxy \(c\). |
| 6.43 | Constant face variance gives population coefficient at \(\beta_{\rm eff}\). | Row 6.42; a.e. constant face variance; \(\beta v_0<2\); same geometry/amplitude. | `EffectiveTemperature:dataBoxCoeff_leading_zero_phase`, `integral_dataBoxCoeff_leading_eq_population_of_const_faceVariance`. | **(a)**. Chart-specific variances give chart-specific temperatures. |
| 6.44 | Limiting empirical mean is generally not the population coefficient at \(\beta\). | Nonzero contributing variance and nontrivial amplitude for strict inflation examples. | Gaussian denominator/effective-temperature results. | **(b)**. In the remark, replace unconditional \(\beta_{\rm eff}<\beta\) by “\(\le\beta\), strictly if \(v_0>0\)”. |
| 6.45 | Summable coordinate \(L^2\) implies Banach \(L^2\). | Countable coordinates, `SummableCoordL2`, measurability. | `ClosureEndpoint:eLpNorm_le_tsum_coordL2`, `memLp_two_of_summableCoordL2`, `memLp_two_sampleObs_of_certificate`. | **(a)**. |
| 6.46 | The sample-limit law also carries the tail certificate. | Exact hypotheses of the endpoint declaration. | `ClosureEndpoint:tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail`. | **(b), CLT gate**. This is the key signature to compare with §6.10. |
| 6.47 | One law supplies both expectation convergence and identified limiting expectation. | B, S, MGF, admissible \(p>1\), E, and any remaining law-existence inputs in the full signature. | `ClosureEndpoint:annealed_sampleDatum_single_identified`, `annealed_sampleDatum_single_effectiveTemperature`. | **(b)**; likely endpoint packaging already exists, not a new bridge to commission blindly. |
| 6.48 | \(\beta\kappa<2\) permits some \(p>1\) with \(p\beta\kappa<2\). | \(\beta>0,\kappa\ge0\). | `ClosureEndpoint:exists_p_gt_one_of_lt_two`, `annealed_sampleDatum_single_identified_of_lt_two`. | **(a)**. |
| 6.49 | Power–log orders are unique; same-population comparison identifies \((\lambda,m)\). | Same positive population integral; nonzero positive leading coefficient; both order descriptions; \(m\ge1\). | `ExponentComparison:powerLogRate_pair_eq_of_isTheta_nat`, `exponentPair_eq_of_population_comparison`. | **(a)**. |
| 6.50 | Hironaka now gives unconditional local population order existence. | Precise analytic/nonnegative/nontrivial phase and small-cube hypotheses of the cited theorem. | `ExponentComparison:exists_exponentPair_of_Q`; `HironakaUnconditional:exists_exponentPair`. | **(b)** for existence. |
| 6.51 | “This holds unconditionally…” identifies the certified pair and then the empirical exponent. | Still needs same-integral compatibility, positive core coefficient, empirical weak limit and positive limit. | `ExponentComparison:tendstoInMeasure_log_div_log_of_population_comparison`. | **(c)** if “this” includes identification/empirical transfer. Separate unconditional population **existence** from conditional **comparison and transport**. |
| 6.52 | Stochastic expansion supplies distributional coefficient/remainder limits. | S and certified expansion hypotheses. | `SampleExpansion:sample_stochastic_expansion`. | **(a)** at its stated distributional level. |
| 6.53 | Existing posterior laws already establish empirical convergence of all quartet observables. | Would require joint empirical numerator/denominator/variance transfer, including unbounded scaled observables. | Fixed-phase spatial laws and stochastic scalar expansions do not alone establish this. | **(c)** in §6.9’s compressed wording. Explicitly retain the observable-transfer hypothesis. **TRANSFER unit**. |
| 6.54 | UI and predictive remainder then determine expected-error coefficients. | Actual scaled observable transfer; UI or suitable moments; model identities; predictive remainder; Gaussian quartet. | `ExpectationBridge…`, `GaussianQuartet:bayes_quartet` are downstream ingredients. | **(b)** as a conditional programme; **(d)** as a completed theorem. |

### §6.10 interface table

The individual rows mostly describe legitimate interfaces, but four changes are needed:

| Interface | Required correction |
|---|---|
| Pathwise / annealed gap | No supporting declarations are supplied in this inventory. Retain the split; require direct declaration references. A good-event pathwise estimate is not an annealed estimate. |
| Distributional assembly | Distinguish a **lower-level theorem consuming a Gaussian law with marginal/tail certificates** from a **higher-level theorem constructing those certificates from the coordinate hypothesis**. The current “Not supplied” column may contradict `ClosureEndpoint`. |
| Annealed assembly | Include \(\mathbb EL>0\) for the advertised asymptotic equivalence. Expectation convergence alone does not provide a nonzero equivalent. |
| Expected errors | Add a row: “joint scaled normalised-observable transfer + UI + predictive remainder → expected quartet coefficients; none of these is supplied merely by a raw-core limit.” |

---

# 3. Smallest missing bridges feeding central claims

## Rank 0 — G0: signature-and-composition audit

This is the first unit, not an implementation programme.

### Target

Produce a checked dependency sheet for:

1. `L1SeqCLT.clt_l1`;
2. `SampleDatumLimit.tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum`;
3. `JointSampleLimit.tendstoInDistribution_scaled_coreSum_sampleDatum`;
4. `ClosureEndpoint.tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail`;
5. the three single-chart identified endpoint declarations;
6. `ScaledAssembly.tendsto_integral_scaled_assembly`;
7. the population/exponent-comparison declarations;
8. the sample-amplitude bound used in `BoxMomentBound`.

### Success gate

For each, record complete binders and section hypotheses, and mark every certificate **constructed** or **consumed**. Then reconcile §6.10.

### Stopping rule

Do not infer law existence, remainder integrability, or bounded sample-data norm from a theorem name. If a certificate is consumed, keep the endpoint conditional until a narrowly specified constructor is found.

---

## Rank 1 — finite-resolution quartet expectation transfer

This is the smallest useful new mathematical unit.

### Proposed theorem: `tendsto_integral_finite_quartet_of_subgaussian`

Fix Q. Let \(g_n\) be measurable finite-dimensional empirical phase vectors and \(G=AZ\). Assume

\[
g_n\Rightarrow G,\qquad
\mathbb E e^{t g_{n,i}}\le e^{\kappa_i t^2/2}
\quad\text{for all }n,i,t\in\mathbb R.
\]

Then, for
\[
F\in\{W_i,M_2,H,V,\log D\},
\qquad
\mathbb EF(g_n)\longrightarrow\mathbb EF(G).
\]

A reusable moment version replaces the MGF hypothesis by
\[
\sup_n\mathbb E\|g_n\|^{2p}<\infty
\quad\text{for some }p>1.
\]

**There is no condition \(\beta\kappa<2\).** Polynomial growth of the normalised quantities is the controlling fact.

### Dependencies

- `GaussianQuartetDet:quartetW_le`, `quartetM2_eq`, `hasFDerivAt_quartetW`;
- `GaussianQuartetGeneral:continuous_quartetVgen`, `polyBoundedPi_quartetVgen`;
- `CovarianceInterpolation:abs_log_quartetD_le`;
- `SubgaussianPhase:hasSubgaussianMGF_empiricalPhase`;
- `ExpectationBridge:tendsto_integral_of_tendstoInDistribution_of_moment`;
- `GaussianQuartet:quartet_identities`, `bayes_quartet`.

### Success gate

One finite-dimensional theorem yielding expectation convergence for the quartet combinations, with:

- fixed weights and covariance;
- arbitrary fixed \(\beta>0\);
- explicit continuity and polynomial bounds;
- no inverse-denominator moment assumption;
- no raw-evidence exponential-moment threshold.

### Stopping rule

Stop before continuum sup-norm moment bounds or empirical-process tightness. Also stop before calling \(F(g_n)\) the actual model error coefficient: that identification belongs to the next unit.

### Assessment of §6.9’s UI gap

For **finite-resolution Gaussian-form empirical approximants**, this gap is small under the note’s sub-Gaussian assumptions.

For **actual finite-sample statistical observables**, it remains substantial: one must transfer to those approximants in a mode strong enough for expectations. Gaussian-limit integrability alone does not do this.

---

## Rank 2 — actual normalised-observable transfer, not numerator transfer

### Proposed theorem: `expected_quartet_of_L1_observable_transfer`

Define
\[
\mathcal Q(g)=
\left(
M_2,\;
M_2-H,\;
M_2-\tfrac12V,\;
M_2-H-\tfrac12V
\right)(g).
\]

For actual scaled model observables \(B_{n,j}\), assume
\[
\mathbb E|B_{n,j}-\mathcal Q_j(g_n)|\longrightarrow0
\qquad(j=1,\ldots,4),
\]
and the hypotheses of Rank 1. Then
\[
\mathbb EB_{n,j}\longrightarrow
\left(
\frac{\lambda}{\beta}+\nu,\;
\frac{\lambda}{\beta}-\nu,\;
\frac{\lambda-\nu}{\beta}+\nu,\;
\frac{\lambda-\nu}{\beta}-\nu
\right)_j.
\]

This is an explicit endpoint theorem with an honest statistical interface.

### Dependencies

- Rank 1;
- `GaussianQuartet:bayes_quartet`;
- `GibbsJointRatio:expectation_eq_div`, `tendstoInDistribution_expectation`;
- `PosteriorTransfer:HasLeadingTerm.tendsto_div_same_pair`;
- the stochastic coefficient expansion, only where its joint form applies.

### Success gate

A model-facing statement identifies exactly what \(B_{n,j}\) are and exactly which residual is \(o_{L^1}(1)\). For an \(o_P(1)\)-based variant, require a separate UI certificate for the actual \(B_{n,j}\).

### Stopping rule

Do not replace \(o_{L^1}(1)\) by \(o_P(1)\) without UI. Do not use deterministic `HasLeadingTerm` results as if they were uniform empirical posterior transfer.

### Numerator versus ratio

`GibbsJointRatio` already supplies an important **leading ratio law** interface. It does not establish:

- a joint numerator/denominator limit from two marginal limits;
- a rate for ratio fluctuations;
- Gaussianity of the resulting random ratio;
- moment control for \(nK\)-type unbounded scaled observables.

For a bounded location observable, `GibbsJointRatio:abs_expectation_le` and `tendsto_integral_expectation` are particularly useful. They do **not** cover the scaled energy quartet merely by renaming the observable.

---

## Rank 3 — predictive Taylor remainder, narrowly stated

This is the principal analytical obstruction to a model-level Bayes theorem.

Let \(\Pi_n\) be the posterior and
\[
\ell_n(x,t)=\log\int e^{-t f(x,w)}\,\Pi_n(dw).
\]
Then
\[
-\ell_n(x,1)
=
\langle f(x,\cdot)\rangle_n
-\frac12\operatorname{Var}_{\Pi_n}(f(x,\cdot))
+R_n(x).
\]

### Proposed theorem: `predictive_remainder_L1_of_tilted_third_moment`

Assume:

1. measurable posterior kernels and positive finite tilted normalisers for \(0\le t\le1\);
2. domination sufficient for three differentiations under the posterior integral;
3. with \(\Pi_{n,x,t}\propto e^{-tf(x,\cdot)}\Pi_n\),
   \[
   n\,\mathbb E_{\text{data},x}
   \sup_{0\le t\le1}
   \left\langle |f(x,\cdot)|^3\right\rangle_{n,x,t}
   \longrightarrow0.
   \]

Then
\[
n\,\mathbb E_{\text{data},x}|R_n(x)|\longrightarrow0.
\]

For training error, require the corresponding **empirical average over the observed \(X_i\)**. It is not interchangeable with the fresh-test-point expectation.

The proof uses the third derivative of the log normaliser, i.e. a tilted centred third moment, and Taylor’s integral remainder. A universal bound by a constant times the tilted absolute third moment suffices.

### Dependencies

- fluctuation derivative/recurrence and self-normalised radial bounds;
- model likelihood and posterior definitions;
- ordinary dominated differentiation and Taylor remainder infrastructure;
- Rank 2 for the final expected-error assembly.

No listed declaration currently supplies this predictive logarithmic estimate.

### Success gate

First prove the explicit remainder implication. Then discharge its hypothesis in **one narrowly specified finite-resolution model**, with stated coefficient-envelope assumptions.

### Stopping rule

If discharge requires general posterior empirical-process estimates, stop. Keep §6.9 conditional. A theorem assuming the tilted-third-moment certificate is useful, but must not be described as having proved that certificate for the statistical model.

---

## Rank 4 — CLT and tail certificate closure

### Assessment

This may be primarily an audit/packaging issue rather than missing mathematics.

The note already lists:

- summable coordinate \(L^2\);
- single-chart empirical limits;
- finite stacked-chart limits;
- a theorem named `…sampleDatum_tail`;
- identified single-chart endpoints.

One should not commission another \(\ell^1\) CLT before inspecting those signatures.

### Proposed target, only if absent

`exists_joint_l1_limit_with_tail_of_coordinate_certificate`:

For a finite family of chart observations read from the same i.i.d. sample, each with measurable weighted summable coordinate \(L^2\), construct one stacked law \(\nu\) such that:

1. the centred normalised stacked sample data converge in distribution to \(\nu\);
2. every finite coordinate vector has the centred Gaussian law with the observation covariance;
3. the truncation tail satisfies the stated summable bound;
4. unpacking gives the chart laws used by both distributional and expectation assembly.

### Dependencies

- `L1Seq:SummableCoordL2`, `finiteCoords`, `truncate`, `norm_sub_truncate_le_tsum`, `tendsto_truncate`;
- `L1SeqCLT:clt_l1`;
- `JointSampleLimit:jointSampleDatum_apply_eq_sampleDatum`;
- `ClosureEndpoint:memLp_two_of_summableCoordL2`, `tendstoInDistribution_scaled_dataBoxIntegral_sampleDatum_tail`;
- `L1GaussianFunctionalL2:map_eq_gaussianReal_of_marginals_of_memLp`.

### Success gate

One and the same constructed law feeds the stacked core limit and the Gaussian expectation identification, with no hidden external existence certificate.

### Stopping rule

If the existing CLT consumes a functional limit theorem not supplied by the coordinate certificate, expose it in the note. Do not silently broaden the project to a generic Banach-space or empirical-process CLT.

A finite-dimensional truncation theorem is an acceptable narrower endpoint.

---

## Rank 5 — construct the compact field from the existing Taylor-data law

### Do not target existence from an arbitrary continuous PSD kernel

That statement is false for the required continuous-path adapter.

For example, take \(K=\{0\}\cup\{1/n:n\ge1\}\), let \(C(0,\cdot)=0\), and set
\[
C(1/n,1/m)=
\begin{cases}
1/\log(n+1),&n=m,\\
0,&n\ne m.
\end{cases}
\]
This is continuous and PSD. Its coordinate Gaussian variables are independent, with variances tending to zero too slowly to converge to zero almost surely. It therefore cannot have the stipulated continuous paths.

### Proposed theorem: `GaussianField.ofL1TaylorLimit`

Assume:

- an existing centred Gaussian law \(\nu\) on the Taylor-data \(\ell^1\) space;
- a **specified bounded linear map**
  \[
  E:\ell^1\longrightarrow C(K);
  \]
- covariance certificate
  \[
  C(x,y)=\int E(z)(x)E(z)(y)\,d\nu(z).
  \]

Then the pushforward \(E_*\nu\) supplies a `GaussianField` with kernel \(C\).

### Dependencies

- `L1GaussianFunctionalL2:map_eq_gaussianReal_of_marginals_of_memLp`;
- `SampleDatumMGF:phaseEvalCLM`;
- `GaussianFieldFernique:integrable_sq_norm_of_isGaussian`;
- `GaussianLinearCombination:GaussianField.ofIsGaussianCertificates`.

The missing piece may simply be packaging the existing evaluation family into a continuous linear map to \(C(K)\).

### Success gate

Construct a field tied to the **same Taylor-data law** already used in the empirical limit. No independent abstract process construction, no KL basis, no entropy theorem.

### Stopping rule

If continuity of the evaluation map requires stronger coefficient control, state it. Do not infer it for jet evaluations from plain boundary \(\ell^1\) summability.

A finite-rank field \(G(x)=\sum_{j=1}^r Z_jh_j(x)\), \(h_j\in C(K)\), is an even smaller fallback.

---

## Rank 6 — ratio correction algebra, only if a fluctuation claim is wanted

There is currently no reason to add a general ratio CLT to the central programme.

A useful bounded unit would be:

### Proposed theorem: `ratio_first_correction_of_joint_limit`

Let \(r_n\to\infty\). Suppose
\[
\left(
N_{0,n},D_{0,n},
r_n(N_n-N_{0,n}),
r_n(D_n-D_{0,n})
\right)
\Rightarrow(N_0,D_0,U,V),
\qquad D_0>0\ \text{a.s.}
\]
with the finite-\(n\) ratios well-defined. Then
\[
r_n\left(\frac{N_n}{D_n}-\frac{N_{0,n}}{D_{0,n}}\right)
\Rightarrow
\frac{U}{D_0}-\frac{N_0V}{D_0^2}.
\]

### Dependencies

`GibbsJointRatio:expectation_eq_div`, the existing joint-ratio continuity interface, elementary ratio algebra, and continuous mapping/Slutsky infrastructure.

### Success gate

A conditional algebraic transport theorem only. It must explicitly retain the denominator fluctuation term.

### Stopping rule

Do not undertake the joint second-order CLT needed to instantiate it. Even when \((U,V)\) is Gaussian, random \(N_0,D_0\) generally make the displayed correction non-Gaussian.

---

# 4. Fixed versus dataset-dependent structure

The note’s formal Gaussian computations use:

- fixed prior and chart geometry;
- fixed weights;
- fixed covariance kernel or Gram matrix;
- random Gaussian evaluations.

The Gram factorisation in `GaussianLinearCombination` is **not** a theorem about empirical eigenvectors, empirical covariance operators, or dataset-dependent spectral truncations.

If a future observable uses \(C_n\), random weights, or a data-selected basis, then:

- a leading ratio limit needs joint convergence of those objects with the phase;
- moment transfer needs bounds uniform in them;
- a fluctuation theorem needs their rates and cross-covariances.

No general spectral programme is needed here. Put this restriction in the ledger and keep all proposed first units fixed-structure.

Likewise:

- `EmpiricalConcentration:tendsto_gibbsMass_ge`,
  `ae_tendsto_gibbsMass_ge`, and
  `tendsto_measure_gibbsMass_ge`
  are concentration statements;
- they do not establish Gaussian limits of scaled observables;
- concentration near a zero set may identify bounded observables constant there, but not the energy fluctuation quartet.

---

# 5. TeX changes now

## Mandatory wording repairs

1. **Conditionalise the field-CLT assertion in the introduction and §2.**
   > Under the stated coordinate CLT certificate and the evaluation-map compatibility, the empirical phase has the centred Gaussian limit used below.

2. **Repair scaled assembly item (2).**
   > If, in addition, the scaled core has a uniform \(p>1\) moment bound and \(\mathbb E|A_n\mathrm{Rem}_n|\to0\), then …

3. **Separate Hironaka existence from comparison and empirical transport.**
   > The unconditional analytic theorem supplies the local population order. Identification with the certified core pair still requires comparison for the same integral; empirical transport additionally requires the stated positive distributional limit.

4. **Repair §6.9’s transfer sentence.**
   > The fixed-phase posterior theorems identify candidate limiting posterior functionals. Expected finite-sample errors additionally require convergence of the relevant scaled empirical normalised observables, uniform integrability, and the predictive remainder estimate.

5. **Restore \(p\ge1\)** in the deterministic-weight proposition and clarify nonnegative scales.

6. **Change “exactly \(1\)” to “at most \(1\)”** in the sub-Gaussian moment proof.

7. **Distinguish bounded amplitude from bounded full sample datum.** The latter generally is not a uniform deterministic hypothesis.

8. **Resolve the CLT/tail interface-table discrepancy after G0.**

9. **Use finite prior mass or \(\mathbb E_+\)** for the annealed identity.

10. **Repair minor notation:** define quartet \(Q\); distinguish geometric \(c\) from variance/proxy; use \(\beta_{\rm eff}\le\beta\), with strictness conditional on positive variance.

## Material to move?

**No central Gaussian theorem should move to an appendix.** Nor should the conditional annealed endpoint move merely because it has substantial hypotheses.

Recommended handling:

- **Fisher-information paragraph:** label as an informal regular-model check, or move to a worked-examples appendix.
- **Jets paragraph:** keep a short conditional interface in §2; move any unconditional differentiation/Gaussian-jet derivation to an appendix until its weighted-map hypotheses are stated.
- **Undotted bilocal \(A\le0\) or \(B\le0\) proof:** it is mathematical, not heuristic. It may remain in the main text as explicitly unformalised analysis. Separate it from the dotted scope if necessary.
- **Any assertion that only UI and predictive remainder remain for actual empirical posteriors:** reword, rather than move. The missing observable-transfer hypothesis must be visible.

Wrong statements should be corrected, **not merely relocated to an appendix**. The existing diagrammatic appendices already have the right restraint.

---

# 6. Are the three “levels” the right scaffold?

They are useful, but insufficient as a ledger classification.

In particular, “Gaussian-limit theorem” risks suggesting that the empirical convergence to that Gaussian object has already been established. I recommend:

1. **Exact deterministic / finite-sample identities.**
2. **Exact Gaussian-model identities**, whether or not a statistical model has yet been connected to that Gaussian law.
3. **Conditional empirical asymptotic consequences.**

Then attach independent tags to each row:

| Axis | Tags |
|---|---|
| Object | population / empirical / Gaussian model |
| Observable | numerator / denominator / normalised ratio / log evidence |
| Limit mode | fixed-path / a.s. / in probability / in distribution / \(L^1\) / expectation |
| Jointness | scalar / finite joint / function-space |
| Structure | fixed / dataset-dependent |
| Certification | (a) / (b) / (c) / (d), plus signature-audit state |

Population Laplace asymptotics deserve an explicit object tag: they do not fit naturally into “exact finite-sample” or “Gaussian-limit” alone.

---

# 7. Recommended next authorisation boundary

Authorise only the following after G0:

1. **Finite-resolution self-normalised moment and expectation transfer**, with fixed covariance and weights.
2. **An explicit expected-quartet endpoint consuming actual-observable \(L^1\) transfer certificates.**
3. **A narrowly stated predictive Taylor-remainder lemma**, followed by one controlled model test.
4. **Only if missing:** package the existing coordinate CLT/tail closure and the Taylor-law-to-compact-field adapter.

Do **not** authorise:

- a general empirical-process theorem;
- a generic functional CLT;
- continuous Gaussian-process existence from arbitrary continuous kernels;
- empirical spectral asymptotics;
- a second-order ratio CLT;
- a general higher-order Bayes-error expansion.

**Bottom line:** the note can remain a strong, largely certified account of exact Gaussian averaging and conditional annealed evidence asymptotics. The next central theorem should concern **normalised finite-resolution expectation transfer**, not another raw numerator theorem. The statistical expected-error programme must continue to advertise three separate obligations: **observable transfer, integrability transfer, and predictive remainder control**.
